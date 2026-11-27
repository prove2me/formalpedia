-- Prove2me | solution 1 for DirectedHamiltonicity.Main.read_cycle_graph_ram
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-27T02:33:37.107853+00:00
-- url     : https://prove2.me/submissions/92f9d665-e554-4a65-aefb-ebdcc49191be

import Definitions.Def_DirectedHamiltonicity_CycleSearch
import Definitions.Def_LogCostRAM_StructuredExecution
import Definitions.Def_DirectedHamiltonicity_Main_Algorithms

namespace TargetedSamplers.Structured

theorem Exec.post {τ inv c s t k} (e : Exec τ inv c s t k) (hs : inv s) : inv t := by
  induction e <;> solve_by_elim

theorem Store.write_fits {s : Store} {width v : ℕ} (h : s.Fits width) (d : ℕ) (hv : v.size ≤ width) :
    (s.write d v).Fits width := by
  intro a
  by_cases he : a = d
  · simpa [Store.write, he] using hv
  · simpa [Store.write, he] using h a

@[simp] theorem Store.write_overwrite (s : Store) (a x y : ℕ) : (s.write a x).write a y = s.write a y := by
  simp [Store.write]

def Op.written (τ : Tapes) (s : Store) : Op → ℕ
  | .const _ c => c
  | .add _ a b => s.mem a + s.mem b
  | .sub _ a b => s.mem a - s.mem b
  | .load _ a => s.mem (s.mem a)
  | .store _ b => s.mem b
  | .input _ a => bitVal τ.input[s.mem a]?
  | .coin _ a => bitVal τ.coins[s.mem a]?
  | .output _ => 0

theorem Op.eval_fits (p : Op) (τ : Tapes) {s : Store} {b : ℕ}
    (hi : s.Fits b) (hw : (p.written τ s).size ≤ b) : (p.eval τ s).Fits b := by
  cases p <;> first | exact Store.write_fits hi _ hw | exact hi

structure Result where
  last : Store
  steps : ℕ
  writeWidth : ℕ

/-- Evaluation charges the actual control transfers and records the largest value written. -/
def Fragment.run (τ : Tapes) (s : Store) : Fragment → Result
  | .skip => ⟨s,0,0⟩
  | .op o => ⟨o.eval τ s,1,(o.written τ s).size⟩
  | .seq x y =>
    let p := x.run τ s
    let q := y.run τ p.last
    ⟨q.last,p.steps+q.steps,max p.writeWidth q.writeWidth⟩
  | .branch a b yes no =>
    if s.mem a ≤ s.mem b then
      let p := yes.run τ s
      ⟨p.last,1+p.steps,p.writeWidth⟩
    else
      let p := no.run τ s
      ⟨p.last,1+p.steps+1,p.writeWidth⟩

theorem Fragment.exec (f : Fragment) (τ : Tapes) (s : Store) (b : ℕ)
    (hs : s.Fits b) (hw : (f.run τ s).writeWidth ≤ b) :
    Exec τ (fun st => st.Fits b) f.cmd s (f.run τ s).last (f.run τ s).steps := by
  induction f generalizing s with
  | skip => exact .skip s
  | op o => exact .op s o (o.eval_fits τ hs hw)
  | seq x y ix iy =>
    obtain ⟨hx,hy⟩ := max_le_iff.mp hw
    have first := ix s hs hx
    exact .seq first (iy _ (first.post hs) hy)
  | branch a b y n iy ino =>
    by_cases h : s.mem a ≤ s.mem b
    · simp only [run,h,if_true] at hw ⊢
      exact .yes h (iy s hs hw)
    · simp only [run,h,if_false] at hw ⊢
      exact .no h (ino s hs hw)


end TargetedSamplers.Structured

namespace BoundedBinaryInput
theorem fold_bits (x : ℕ) : x.bits.foldr Nat.bit 0 = x := by
  induction x using Nat.binaryRec' with
  | zero => rfl
  | bit b x h ih => simp [Nat.bits_append_bit x b h, ih]
end BoundedBinaryInput

namespace TargetedSamplers.Structured.BinaryRead

structure Reading (r : Fin 7 ↪ ℕ) (s : Store) (p a w m : ℕ) : Prop where
  pos : s.mem (r 0) = p
  acc : s.mem (r 1) = a
  place : s.mem (r 2) = w
  mark : s.mem (r 3) = m
  zero : s.mem (r 5) = 0
  one : s.mem (r 6) = 1

private theorem bit_width (v : Option Bool) : (bitVal v).size ≤ 2 := by
  cases v with
  | none => decide
  | some x => cases x <;> decide

set_option maxHeartbeats 700000 in
theorem oneDigit_exec (r : Fin 7 ↪ ℕ) {τ : Tapes} {b : ℕ} {s : Store} {p a w : ℕ} (x : Bool)
    (h : Reading r s p a w 1) (input : τ.input[p+1]? = some x) (fit : s.Fits b) (hb : 2 ≤ b)
    (hp : (p+2).size ≤ b) (ha : (a+w).size ≤ b) (hw : (w+w).size ≤ b) :
    let u := ((oneDigit r).run τ s).last
    ∃ j ≤ 8, Exec τ (fun st => st.Fits b) (oneDigit r).cmd s u j ∧
      Reading r u (p+2) (if x then a+w else a) (w+w) (bitVal τ.input[p+2]?) ∧
      u.out = s.out ∧ ∀ addr, (∀ i, addr ≠ r i) → u.mem addr = s.mem addr := by
  let u := ((oneDigit r).run τ s).last
  have heq (i j : Fin 7) : r i = r j ↔ i = j := r.injective.eq_iff
  have hp' := (Nat.size_le_size (by omega : p+1 ≤ p+2)).trans hp
  have hm := (bit_width τ.input[p+2]?).trans hb
  have val (y : Bool) : bitVal (some y) = y.toNat := rfl
  have two : p+1+1 = p+2 := rfl
  have width : ((oneDigit r).run τ s).writeWidth ≤ b := by
    cases x <;> simp [oneDigit,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,
      Function.update_apply,heq,h.pos,h.zero,h.one,h.acc,h.place,input,val,two,hp,hp',ha,hw,hm] <;> omega
  have ex := (oneDigit r).exec τ s b fit width
  refine ⟨_,?_,ex,?_,?_,?_⟩
  · cases x <;> simp [oneDigit,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Store.write,
      Function.update_apply,heq,h.pos,h.zero,h.one,input,val]
  · cases x <;> constructor <;> simp [oneDigit,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Store.write,
      Function.update_apply,heq,h.pos,h.zero,h.one,h.acc,h.place,input,val,two]
  · cases x <;> simp [oneDigit,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Store.write,
      Function.update_apply,heq,h.pos,h.zero,h.one,input,val]
  · intro addr hfree
    cases x <;> simp [oneDigit,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Store.write,
      Function.update_apply,heq,h.pos,h.zero,h.one,h.acc,h.place,input,val,hfree]

def pairs (xs : List Bool) := xs.flatMap fun x => [true,x]

theorem bitVal_marker (xs rest : List Bool) : bitVal (pairs xs ++ false::rest)[0]? = marker xs := by
  cases xs <;> rfl

theorem scan_exec (r : Fin 7 ↪ ℕ) {τ : Tapes} {b : ℕ} (xs rest : List Bool) (p a w : ℕ) (s : Store)
    (h : Reading r s p a w (marker xs)) (fit : s.Fits b) (hb : 2 ≤ b)
    (input : τ.input.drop p = pairs xs ++ false::rest) (hp : (p+2*xs.length).size ≤ b)
    (hplace : (w*2^xs.length).size ≤ b) (hdata : (a+w*(2^xs.length-1)).size ≤ b) :
    ∃ t j, Exec τ (fun st => st.Fits b) (scan r) s t j ∧ j ≤ 10*xs.length+1 ∧
      Reading r t (p+2*xs.length) (a+w*xs.foldr Nat.bit 0) (w*2^xs.length) 0 ∧
      t.out = s.out ∧ ∀ addr, (∀ i, addr ≠ r i) → t.mem addr = s.mem addr := by
  induction xs generalizing p a w s with
  | nil =>
    refine ⟨s,1,.done (by rw [h.mark,h.zero]; decide),by simp,?_,rfl,fun _ _ => rfl⟩
    simpa [marker] using h
  | cons x xs ih =>
    have hi : τ.input[p+1]? = some x := by rw [← List.getElem?_drop,input]; rfl
    have remaining : τ.input.drop (p+2) = pairs xs ++ false::rest := by rw [← List.drop_drop,input]; rfl
    have mark : bitVal τ.input[p+2]? = marker xs := by
      have eq : τ.input[p+2]? = (τ.input.drop (p+2))[0]? := by simp
      rw [eq,remaining,bitVal_marker]
    have sp : p+2+2*xs.length = p+2*(x::xs).length := by simp; omega
    have hx : 1 ≤ 2^xs.length := Nat.one_le_two_pow
    have hplaces : (w+w)*2^xs.length = w*2^(x::xs).length := by simp [pow_succ]; ring
    have rem : 2^(x::xs).length-1 = 1+2*(2^xs.length-1) := by simp only [List.length_cons,pow_succ]; omega
    have ha : (a+w).size ≤ b := (Nat.size_le_size (by
      rw [rem]; simp only [Nat.mul_add,Nat.mul_one]; omega)).trans hdata
    have hw : (w+w).size ≤ b := (Nat.size_le_size (by
      rw [← hplaces]; simpa using Nat.mul_le_mul_left (w+w) hx)).trans hplace
    have hp' := (Nat.size_le_size (show p+2 ≤ p+2*(x::xs).length by simp)).trans hp
    obtain ⟨l,hl,ex,hr,log,frame⟩ := oneDigit_exec r x h hi fit hb hp' ha hw
    rw [mark] at hr
    let next := if x then a+w else a
    have hd : (next+(w+w)*(2^xs.length-1)).size ≤ b := by
      apply (Nat.size_le_size ?_).trans hdata
      rw [rem]
      cases x <;> dsimp [next] <;> nlinarith only [Nat.zero_le w]
    obtain ⟨t,j,loop,hj,out,hlog,save⟩ := ih (p+2) next (w+w) _ hr (ex.post fit) remaining
      (by rwa [sp]) (by rwa [hplaces]) hd
    refine ⟨t,_,.again (by rw [h.mark,h.zero]; change ¬(1:ℕ) ≤ 0; decide) ex loop,by simp; omega,?_,hlog.trans log,
      fun addr ha => (save addr ha).trans (frame addr ha)⟩
    have value : next+(w+w)*xs.foldr Nat.bit 0 = a+w*(x::xs).foldr Nat.bit 0 := by
      cases x <;> simp [next,Nat.bit] <;> ring
    simpa only [sp,value,hplaces] using out

theorem begin_exec (r : Fin 7 ↪ ℕ) {τ : Tapes} {b : ℕ} {s : Store} {p : ℕ}
    (ptr : s.mem (r 0) = p) (xs rest : List Bool) (bits : τ.input.drop p = pairs xs ++ false::rest)
    (fit : s.Fits b) (hb : 2 ≤ b) :
    let t := ((beginField r).run τ s).last
    Exec τ (fun st => st.Fits b) (beginField r).cmd s t 5 ∧ Reading r t p 0 1 (marker xs) ∧
      t.out = s.out ∧ ∀ a, (∀ i, a ≠ r i) → t.mem a = s.mem a := by
  have ne (i j : Fin 7) : r i = r j ↔ i = j := r.injective.eq_iff
  have hm : bitVal τ.input[p]? = marker xs := by
    have eq : (τ.input.drop p)[0]? = τ.input[p]? := by simp
    rw [← eq,bits,bitVal_marker]
  have width : ((beginField r).run τ s).writeWidth ≤ b := by
    have hv := (bit_width τ.input[p]?).trans hb
    simp [beginField,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,
      Function.update_apply,ne,ptr,hv] <;> omega
  refine ⟨(beginField r).exec τ s b fit width,?_,rfl,?_⟩
  · constructor <;> simp [beginField,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Store.write,
      Function.update_apply,ne,ptr,hm]
  · intro a ha
    simp [beginField,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Store.write,Function.update_apply,ha]

theorem readField_exec (r : Fin 7 ↪ ℕ) {τ : Tapes} {b : ℕ} (p x : ℕ) (rest : List Bool) (s : Store)
    (ptr : s.mem (r 0) = p) (input : τ.input.drop p = pairs x.bits ++ false::rest) (fit : s.Fits b)
    (hb : 2 ≤ b) (hp : (p+2*x.size+1).size ≤ b) (hw : x.size+1 ≤ b) :
    ∃ t j, Exec τ (fun st => st.Fits b) (readField r) s t j ∧ j ≤ 10*x.size+7 ∧
      t.mem (r 0) = p+2*x.size+1 ∧ t.mem (r 1) = x ∧ t.mem (r 5) = 0 ∧ t.mem (r 6) = 1 ∧ t.out = s.out ∧
      ∀ a, (∀ i, a ≠ r i) → t.mem a = s.mem a := by
  obtain ⟨init,hr,oi,fi⟩ := begin_exec (τ := τ) r ptr x.bits rest input fit hb
  have place : ((1:ℕ)*2^x.bits.length).size ≤ b := by simpa [Nat.size_eq_bits_len,Nat.size_pow] using hw
  have data : (0+1*(2^x.bits.length-1)).size ≤ b := by
    simp only [Nat.zero_add,Nat.one_mul] at place ⊢
    exact (Nat.size_le_size (Nat.sub_le ..)).trans place
  have range : (p+2*x.bits.length).size ≤ b := by
    rw [Nat.size_eq_bits_len]; exact (Nat.size_le_size (by omega)).trans hp
  obtain ⟨u,l,loop,hl,post,ou,fu⟩ := scan_exec (τ := τ) r x.bits rest p 0 1 _ hr (init.post fit) hb input range place data
  let t := u.write (r 0) (p+2*x.size+1)
  have eq : (Op.add (r 0) (r 0) (r 6)).eval τ u = t := by
    simp [Op.eval,t,post.pos,post.one,Nat.size_eq_bits_len]
  have last : Exec τ (fun v => v.Fits b) (.op (.add (r 0) (r 0) (r 6))) u t 1 := by
    simpa only [eq] using (Exec.op (τ := τ) (inv := fun v => v.Fits b) u (.add (r 0) (r 0) (r 6))
      (by rw [eq]; exact Store.write_fits (loop.post (init.post fit)) _ hp))
  rw [Nat.size_eq_bits_len] at hl
  refine ⟨t,_,init.seq (loop.seq last),by omega,by simp [t,Store.write],?_,?_,?_,ou.trans oi,?_⟩
  · simpa [t,Store.write,r.injective.ne (by decide : (1:Fin 7) ≠ 0),BoundedBinaryInput.fold_bits] using post.acc
  · simpa [t,Store.write,r.injective.ne (by decide : (5:Fin 7) ≠ 0)] using post.zero
  · simpa [t,Store.write,r.injective.ne (by decide : (6:Fin 7) ≠ 0)] using post.one
  · intro a ha
    simpa [t,Store.write,ha] using (fu a ha).trans (fi a ha)

end TargetedSamplers.Structured.BinaryRead

namespace DirectedHamiltonicity.Main.CycleReduction.TapeReader

open TargetedSamplers TargetedSamplers.Structured FiniteSampling
open scoped BigOperators

inductive Port | input | coin

def Port.read (port : Port) (dst addr : ℕ) : Op :=
  match port with | .input => .input dst addr | .coin => .coin dst addr

def Port.tape (port : Port) (τ : Tapes) : List Bool :=
  match port with | .input => τ.input | .coin => τ.coins

@[simp] theorem read_eval (p : Port) (d a : ℕ) (τ : Tapes) (s : Store) :
    (p.read d a).eval τ s = s.write d (bitVal (p.tape τ)[s.mem a]?) := by cases p <;> rfl
@[simp] theorem read_written (p : Port) (d a : ℕ) (τ : Tapes) (s : Store) :
    (p.read d a).written τ s = bitVal (p.tape τ)[s.mem a]? := by cases p <;> rfl

/-- Read little-endian bits. Missing cells of a short tape have value zero. -/
def value (coins : List Bool) (base : ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => value coins base k + (coins[base+k]?.getD false).toNat * 2^k

/-- Registers hold a descending cursor, its lower endpoint, one, the read symbol and the accumulator. -/
def digit (port : Port) (r : Fin 5 ↪ ℕ) : Fragment := Structured.sequence [
  .op (.sub (r 0) (r 0) (r 2)),.op (port.read (r 3) (r 0)),.op (.add (r 4) (r 4) (r 4)),
  .branch (r 3) (r 2) (.branch (r 2) (r 3) (.op (.add (r 4) (r 4) (r 2))) .skip) .skip]

def loop (port : Port) (r : Fin 5 ↪ ℕ) : Cmd := .whileGt (r 0) (r 1) (digit port r).cmd

private theorem digit_exec (port : Port) {τ : Tapes} {width : ℕ} (r : Fin 5 ↪ ℕ) (s : Store) (p v : ℕ)
    (pos : s.mem (r 0) = p+1) (one : s.mem (r 2) = 1) (acc : s.mem (r 4) = v)
    (fit : s.Fits width) (hb : 2 ≤ width) (w : (v+v+1).size ≤ width) :
    let t := ((digit port r).run τ s).last
    ∃ j ≤ 7, Exec τ (fun u => u.Fits width) (digit port r).cmd s t j ∧
      t.mem (r 0) = p ∧ t.mem (r 4) = v+v+((port.tape τ)[p]?.getD false).toNat ∧ t.out = s.out ∧
      ∀ a, a ≠ r 0 → a ≠ r 3 → a ≠ r 4 → t.mem a = s.mem a := by
  cases port with
  | input =>
    have eq (i j : Fin 5) : r i = r j ↔ i=j := r.injective.eq_iff
    have wp := (Nat.size_le_size (Nat.le_succ p)).trans (pos ▸ fit (r 0))
    have wv := (Nat.size_le_size (Nat.le_succ (v+v))).trans w
    have two : (2:ℕ).size ≤ width := hb
    have unit : 1 ≤ width := by omega
    have ww : ((digit .input r).run τ s).writeWidth ≤ width := by
      cases h : τ.input[p]? with
      | none => simp [Port.read,Port.tape,digit,Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,eq,pos,one,acc,h,bitVal,two,unit,wp,wv]
      | some x => cases x <;> simp [Port.read,Port.tape,digit,Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,eq,pos,one,acc,h,bitVal,two,unit,wp,wv,w]
    refine ⟨_,?_,(digit .input r).exec τ s width fit ww,?_,?_,?_,?_⟩
    all_goals first
      | (intro a h₀ h₃ h₄
         cases h : τ.input[p]? with
         | none => simp [Port.read,Port.tape,digit,Structured.sequence,Fragment.run,Op.eval,Store.write,eq,pos,one,acc,h,bitVal,h₀,h₃,h₄]
         | some x => cases x <;> simp [Port.read,Port.tape,digit,Structured.sequence,Fragment.run,Op.eval,Store.write,eq,pos,one,acc,h,bitVal,h₀,h₃,h₄])
      | (cases h : τ.input[p]? with
         | none => simp [Port.read,Port.tape,digit,Structured.sequence,Fragment.run,Op.eval,Store.write,eq,pos,one,acc,h,bitVal]
         | some x => cases x <;> simp [Port.read,Port.tape,digit,Structured.sequence,Fragment.run,Op.eval,Store.write,eq,pos,one,acc,h,bitVal])
  | coin =>
    have eq (i j : Fin 5) : r i = r j ↔ i=j := r.injective.eq_iff
    have wp := (Nat.size_le_size (Nat.le_succ p)).trans (pos ▸ fit (r 0))
    have wv := (Nat.size_le_size (Nat.le_succ (v+v))).trans w
    have two : (2:ℕ).size ≤ width := hb
    have unit : 1 ≤ width := by omega
    have ww : ((digit .coin r).run τ s).writeWidth ≤ width := by
      cases h : τ.coins[p]? with
      | none => simp [Port.read,Port.tape,digit,Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,eq,pos,one,acc,h,bitVal,two,unit,wp,wv]
      | some x => cases x <;> simp [Port.read,Port.tape,digit,Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,eq,pos,one,acc,h,bitVal,two,unit,wp,wv,w]
    refine ⟨_,?_,(digit .coin r).exec τ s width fit ww,?_,?_,?_,?_⟩
    all_goals first
      | (intro a h₀ h₃ h₄
         cases h : τ.coins[p]? with
         | none => simp [Port.read,Port.tape,digit,Structured.sequence,Fragment.run,Op.eval,Store.write,eq,pos,one,acc,h,bitVal,h₀,h₃,h₄]
         | some x => cases x <;> simp [Port.read,Port.tape,digit,Structured.sequence,Fragment.run,Op.eval,Store.write,eq,pos,one,acc,h,bitVal,h₀,h₃,h₄])
      | (cases h : τ.coins[p]? with
         | none => simp [Port.read,Port.tape,digit,Structured.sequence,Fragment.run,Op.eval,Store.write,eq,pos,one,acc,h,bitVal]
         | some x => cases x <;> simp [Port.read,Port.tape,digit,Structured.sequence,Fragment.run,Op.eval,Store.write,eq,pos,one,acc,h,bitVal])

/-- A fixed bounded loop port reads a coin block at an arbitrary address. No length query is used. -/
theorem loop_exec (port : Port) {τ : Tapes} {width : ℕ} (r : Fin 5 ↪ ℕ) (s : Store) (base k v : ℕ)
    (pos : s.mem (r 0) = base+k) (stop : s.mem (r 1) = base) (one : s.mem (r 2) = 1)
    (acc : s.mem (r 4) = v) (fit : s.Fits width) (hb : 2 ≤ width) (room : ((v+1)*2^k).size ≤ width) :
    ∃ t j, Exec τ (fun u => u.Fits width) (loop port r) s t j ∧ j ≤ 9*k+1 ∧
      t.mem (r 0) = base ∧ t.mem (r 4) = v*2^k+value (port.tape τ) base k ∧ t.out = s.out ∧
      ∀ a, a ≠ r 0 → a ≠ r 3 → a ≠ r 4 → t.mem a = s.mem a := by
  induction k generalizing s v with
  | zero =>
    exact ⟨s,1,.done (by simp [pos,stop]),by simp,by simpa using pos,by simpa [value] using acc,rfl,fun _ _ _ _ => rfl⟩
  | succ k ih =>
    have ne {i j : Fin 5} (h : i ≠ j) := r.injective.ne h
    let x := ((port.tape τ)[base+k]?.getD false).toNat
    have bit : x ≤ 1 := Bool.toNat_le _
    have lower : v+v+1 ≤ (v+1)*2^(k+1) := by
      rw [pow_succ]
      have m := Nat.mul_le_mul_left (v+1) (Nat.one_le_two_pow (n := k))
      nlinarith only [m]
    obtain ⟨j,hj,first,pp,vv,out,frame⟩ := digit_exec port (τ := τ) r s (base+k) v (by simpa [Nat.add_assoc] using pos)
      one acc fit hb ((Nat.size_le_size lower).trans room)
    let u := ((digit port r).run τ s).last
    have bound : (v+v+x+1)*2^k ≤ (v+1)*2^(k+1) := by
      rw [pow_succ,show (v+1)*(2^k*2) = ((v+1)*2)*2^k by ring]
      exact Nat.mul_le_mul_right _ (by omega)
    obtain ⟨t,i,rest,hi,done',number,ofinal,last⟩ := ih u (v+v+x) pp
      ((frame _ (ne (by decide)) (ne (by decide)) (ne (by decide))).trans stop)
      ((frame _ (ne (by decide)) (ne (by decide)) (ne (by decide))).trans one) vv (first.post fit)
      ((Nat.size_le_size bound).trans room)
    refine ⟨t,_,.again (by rw [pos,stop]; omega) first rest,by omega,done',?_,ofinal.trans out,
      fun a h₀ h₃ h₄ => (last a h₀ h₃ h₄).trans (frame a h₀ h₃ h₄)⟩
    rw [number,value,pow_succ]
    dsimp [x]
    ring

private theorem binaryRank_val (k : ℕ) (bits : Fin k → Bool) :
    (binaryRank k bits).val = ∑ i, (bits i).toNat*2^i.val := by
  change (finFunctionFinEquiv (fun i => finTwoEquiv.symm (bits i))).val = _
  rw [finFunctionFinEquiv_apply]
  apply Finset.sum_congr rfl
  intro i _
  have h (x : Bool) : (finTwoEquiv.symm x).val = x.toNat := by cases x <;> rfl
  rw [h]

theorem coinValue_eq_binaryRank (coins : List Bool) (base k : ℕ) :
    value coins base k = (binaryRank k fun i => coins[base+i.val]?.getD false).val := by
  rw [binaryRank_val]
  induction k with
  | zero => simp [value]
  | succ k ih => simp only [value,Fin.sum_univ_castSucc,Fin.val_castSucc,Fin.val_last,ih]

def readRank (port : Port) (r : Fin 5 ↪ ℕ) : Cmd := .seq (.op (.const (r 4) 0)) (loop port r)

/-- The RAM returns the rank used by the sampling proof, for every finite tape. -/
theorem readRank_exec (port : Port) {τ : Tapes} {width : ℕ} (r : Fin 5 ↪ ℕ) (s : Store) (base k : ℕ)
    (pos : s.mem (r 0) = base+k) (stop : s.mem (r 1) = base) (one : s.mem (r 2) = 1)
    (fit : s.Fits width) (hw : 2 ≤ width) (room : k+1 ≤ width) :
    ∃ t j, Exec τ (fun u => u.Fits width) (readRank port r) s t j ∧ j ≤ 9*k+2 ∧
      t.mem (r 0) = base ∧ t.mem (r 4) = (binaryRank k fun i => (port.tape τ)[base+i.val]?.getD false).val ∧
      t.out = s.out ∧ ∀ a, a ≠ r 0 → a ≠ r 3 → a ≠ r 4 → t.mem a = s.mem a := by
  let u := s.write (r 4) 0
  have f : u.Fits width := Store.write_fits fit _ (by simp)
  have init : Exec τ (fun v => v.Fits width) (.op (.const (r 4) 0)) s u 1 := .op _ _ f
  have kept (i : Fin 5) (hi : i ≠ 4) : u.mem (r i) = s.mem (r i) := by simp [u,Store.write,r.injective.ne hi]
  obtain ⟨t,j,run,work,cursor,val,out,frame⟩ := loop_exec port (τ := τ) r u base k 0
    ((kept 0 (by decide)).trans pos) ((kept 1 (by decide)).trans stop) ((kept 2 (by decide)).trans one)
    (by simp [u,Store.write]) f hw (by simpa only [Nat.zero_add,Nat.one_mul,Nat.size_pow] using room)
  exact ⟨t,_,init.seq run,by omega,cursor,by simpa [coinValue_eq_binaryRank] using val,out,
    fun a h₀ h₃ h₄ => (frame a h₀ h₃ h₄).trans (by simp [u,Store.write,h₄])⟩


end DirectedHamiltonicity.Main.CycleReduction.TapeReader

namespace DirectedHamiltonicity.Main.CycleReduction.GraphInput

open TargetedSamplers TargetedSamplers.Structured FiniteSampling

def headerRegs : Fin 7 ↪ ℕ := Fin.valEmbedding
def blockRegs : Fin 5 ↪ ℕ where
  toFun i := ![0,2,6,3,4] i
  inj' := by decide

def beginRows : Fragment := Structured.sequence [.op (.add 2 0 5), .op (.add 7 1 5)]
def addRow : Fragment := Structured.sequence [.op (.add 0 0 1), .op (.sub 7 7 6)]
def skipRows : Cmd := .whileGt 7 5 addRow.cmd

/-- Parse n, compute the end of the matrix, and read the n-squared row-major bits into one word. -/
def readGraph : Cmd := .seq (BinaryRead.readField headerRegs)
  (.seq beginRows.cmd (.seq skipRows (TapeReader.readRank .input blockRegs)))

def rowBits {n : ℕ} (adj : Fin n → Fin n → Bool) (i : Fin (n*n)) : Bool :=
  adj (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2

theorem tape_eq {n : ℕ} (adj : Fin n → Fin n → Bool) :
    encodeDigraph n adj = encNat n ++ List.ofFn (rowBits adj) := by
  unfold encodeDigraph
  apply congrArg (List.append (encNat n))
  rw [List.ofFn_mul]
  simp only [List.ofFn_eq_map,← List.flatMap_def]
  apply congrArg (fun f => (List.finRange n).flatMap f)
  funext i
  apply congrArg (fun f => (List.finRange n).map f)
  funext j
  have idx (h : i.val*n+j.val < n*n) : (⟨i.val*n+j.val,h⟩ : Fin (n*n)) = finProdFinEquiv (i,j) := by
    apply Fin.ext
    change _ = j.val+n*i.val
    ring
  unfold rowBits
  rw [idx _,Equiv.symm_apply_apply]

private theorem rows_exec (τ : Tapes) (b n p k : ℕ) (s : Store)
    (fit : s.Fits b) (cursor : s.mem 0=p) (dim : s.mem 1=n) (zero : s.mem 5=0)
    (one : s.mem 6=1) (count : s.mem 7=k) (width : (p+k*n).size ≤ b) :
    ∃ t j, Exec τ (fun u => u.Fits b) skipRows s t j ∧ j ≤ 4*k+1 ∧
      t.mem 0=p+k*n ∧ t.out=s.out ∧ ∀ a, a≠0 → a≠7 → t.mem a=s.mem a := by
  induction k generalizing p s with
  | zero =>
    exact ⟨s,1,.done (by rw [count,zero]),by simp,by simpa using cursor,rfl,fun _ _ _ => rfl⟩
  | succ k ih =>
    let u := (addRow.run τ s).last
    have bound := (Nat.size_le_size (show p+n ≤ p+(k+1)*n by rw [Nat.succ_mul];omega)).trans width
    have short := (Nat.size_le_size (Nat.le_succ k)).trans (count ▸ fit 7)
    have wrote : (addRow.run τ s).writeWidth ≤ b := by
      simp [addRow,Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,cursor,dim,count,one,bound,short]
    have ex : Exec τ (fun v => v.Fits b) addRow.cmd s u 2 := (addRow.exec τ s b fit wrote)
    have mem : u.mem = Function.update (Function.update s.mem 0 (p+n)) 7 k := by
      simp [u,addRow,Structured.sequence,Fragment.run,Op.eval,Store.write,cursor,dim,count,one]
    have out : u.out=s.out := rfl
    have last : p+n+k*n = p+(k+1)*n := by ring
    obtain ⟨t,j,run,le,ptr,done',frame⟩ := ih (p+n) u (ex.post fit)
      (by simp [mem]) (by simp [mem,dim]) (by simp [mem,zero]) (by simp [mem,one]) (by simp [mem]) (last ▸ width)
    exact ⟨t,_,.again (by rw [count,zero];omega) ex run,by omega,ptr.trans last,done'.trans out,
      fun a a0 a7 => (frame a a0 a7).trans (by simp [mem,a0,a7])⟩

private theorem rank_bit {k : ℕ} (f : Fin k → Bool) (j : Fin k) :
    (binaryRank k f).val.testBit j.val = f j := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have eq : (finTwoEquiv.symm (f j)).val=((binaryRank k f).val/2^j.val)%2 := by
    change _=((finFunctionFinEquiv.symm (finFunctionFinEquiv (fun i => finTwoEquiv.symm (f i)))) j).val
    rw [Equiv.symm_apply_apply]
  rw [←eq];cases f j <;> rfl

theorem read_graph_exec (n : ℕ) (adj : Fin n → Fin n → Bool) (coins : List Bool) (b : ℕ) (s : Store)
    (start : s.mem 0=0) (fit : s.Fits b) (room : 8*(n+1)^2 ≤ b) :
    ∃ t k, Exec (runTapes (encodeDigraph n adj) coins) (fun u => u.Fits b) readGraph s t k ∧
      k ≤ 10*n.size+4*n+9*(n*n)+12 ∧ t.mem 1=n ∧
      (∀ u v : Fin n, (t.mem 4).testBit (v.val+n*u.val)=adj u v) ∧ t.out=s.out ∧
      ∀ a ≥ 8, t.mem a=s.mem a := by
  let τ := runTapes (encodeDigraph n adj) coins
  let H := 2*n.size+1
  have ns : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  have wide : (H+n*n).size ≤ b := by
    exact (show (H+n*n).size ≤ H+n*n from Nat.size_le.mpr Nat.lt_two_pow_self).trans
      (by dsimp [H];nlinarith)
  have hlen : (encNat n).length = H := by
    unfold encNat H
    simp [List.length_flatMap,Nat.size_eq_bits_len,Nat.mul_comm]
  let rest := List.ofFn (rowBits adj)
  have tape : τ.input = encNat n ++ rest := tape_eq adj
  obtain ⟨h,j,header,steps,pos,dim,z,o,out,frame⟩ := BinaryRead.readField_exec (τ := τ) headerRegs 0 n rest s
    start (by rw [List.drop_zero,tape];simp [encNat,BinaryRead.pairs,List.append_assoc]) fit (by nlinarith)
    ((Nat.size_le_size (show 0+2*n.size+1 ≤ H+n*n by dsimp [H];omega)).trans wide) (by nlinarith)
  change h.mem 0=0+2*n.size+1 at pos
  change h.mem 1=n at dim
  change h.mem 5=0 at z
  change h.mem 6=1 at o
  have pos' : h.mem 0=H := by simpa [H] using pos
  let init := (beginRows.run τ h).last
  have wrote : (beginRows.run τ h).writeWidth ≤ b := by
    simp [beginRows,Structured.sequence,Fragment.run,Op.written,Op.eval,Store.write,z]
    exact ⟨header.post fit _,header.post fit _⟩
  have ex : Exec τ (fun v => v.Fits b) beginRows.cmd h init 2 := beginRows.exec τ h b (header.post fit) wrote
  have initMem : init.mem = Function.update (Function.update h.mem 2 H) 7 n := by
    simp [init,beginRows,Structured.sequence,Fragment.run,Op.eval,Store.write,z,pos',dim]
  obtain ⟨u,q,skip,qsteps,ptr,uout,uframe⟩ := rows_exec τ b n H n init (ex.post (header.post fit))
    (by simp [initMem,pos']) (by simp [initMem,dim]) (by simp [initMem,z]) (by simp [initMem,o]) (by simp [initMem]) wide
  obtain ⟨t,l,read,lsteps,_,rank,tout,tframe⟩ := TapeReader.readRank_exec .input (τ:=τ) blockRegs u H (n*n)
    ptr ((uframe 2 (by decide) (by decide)).trans (by simp [initMem]))
    ((uframe 6 (by decide) (by decide)).trans (by simp [initMem,o]))
    (skip.post (ex.post (header.post fit))) (by nlinarith) (by nlinarith)
  have stored : t.mem 4=(binaryRank (n*n) (rowBits adj)).val := by
    change t.mem 4 = _ at rank
    rw [rank]
    apply congrArg (fun f => (binaryRank (n*n) f).val)
    funext i
    change _ = rowBits adj i
    change τ.input[H+i.val]?.getD false = _
    rw [tape,List.getElem?_append_right (by omega),hlen]
    simp [rest]
  refine ⟨t,_,header.seq (ex.seq (skip.seq read)),by omega,?_,?_,tout.trans (uout.trans out),?_⟩
  · exact (tframe 1 (by decide) (by decide) (by decide)).trans ((uframe 1 (by decide) (by decide)).trans (by simp [initMem,dim]))
  · intro u v
    rw [stored,show v.val+n*u.val = (finProdFinEquiv (u,v)).val by rfl,rank_bit]
    simp [rowBits]
  · intro a ha
    change t.mem a=s.mem a
    refine (tframe a (by change a ≠ 0;omega) (by change a ≠ 3;omega) (by change a ≠ 4;omega)).trans ?_
    rw [uframe a (by omega) (by omega),initMem]
    simp only [Function.update_of_ne (show a≠7 by omega),Function.update_of_ne (show a≠2 by omega)]
    exact frame a (by intro i;change a ≠ i.val;have := i.isLt;omega)

end DirectedHamiltonicity.Main.CycleReduction.GraphInput

open TargetedSamplers TargetedSamplers.Structured DirectedHamiltonicity.Main

theorem solution :
    ∃ code : Cmd, ∀ (n : ℕ) (adj : Fin n → Fin n → Bool) (coins : List Bool) (b : ℕ) (s : Store),
      s.mem 0 = 0 → s.Fits b → 8*(n+1)^2 ≤ b →
      ∃ t k, Exec (runTapes (encodeDigraph n adj) coins) (fun u => u.Fits b) code s t k ∧
        k ≤ 10*n.size+4*n+9*(n*n)+12 ∧ t.mem 1 = n ∧
        (∀ u v : Fin n, (t.mem 4).testBit (v.val+n*u.val) = adj u v) ∧ t.out = s.out ∧
        ∀ a ≥ 8, t.mem a = s.mem a := by
  exact ⟨_,CycleReduction.GraphInput.read_graph_exec⟩
