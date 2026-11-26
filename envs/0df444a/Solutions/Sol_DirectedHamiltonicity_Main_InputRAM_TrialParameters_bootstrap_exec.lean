-- Prove2me | solution 1 for DirectedHamiltonicity.Main.InputRAM.TrialParameters.bootstrap_exec
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-26T17:27:24.885972+00:00
-- url     : https://prove2.me/submissions/6d6d9b70-2e82-488d-af08-480e0446bbe2

import Definitions.Def_DirectedHamiltonicity_ParityRAMInterfaces

set_option autoImplicit false

section StructuredLogCostRAM

/-! Structured, relocatable programs for the Prove2Me log-cost machine. All costs count
the primitive steps of the published instruction list, including jumps. -/

namespace TargetedSamplers.Structured

theorem Exec.post {τ inv c s t k} (e : Exec τ inv c s t k) (hs : inv s) : inv t := by
  induction e <;> solve_by_elim

/-- A live, ordinary machine state at the specified instruction, memory and output. -/
structure Located (st : State) (pc : ℕ) (s : Store) : Prop where
  counter : st.pc = pc
  live : st.halted = false
  normal : st.bot = false
  memory : st.mem = s.mem
  output : st.out = s.out

private theorem step_op {P : Program} (τ : Tapes) {st pc s} (h : Located st pc s)
    (p : Op) (hp : P[pc]? = some p.instruction) : Located (P.step τ st) (pc+1) (p.eval τ s) := by
  obtain ⟨hc,hh,hb,hm,ho⟩ := h
  cases p <;> constructor <;> simp_all [Op.instruction, Op.eval, Program.step, State.write, Store.write]

end TargetedSamplers.Structured

end StructuredLogCostRAM

section StructuredLogCostFragments

namespace TargetedSamplers.Structured

theorem Store.write_fits {s : Store} {width v : ℕ} (h : s.Fits width) (d : ℕ) (hv : v.size ≤ width) :
    (s.write d v).Fits width := by
  intro a
  by_cases he : a = d
  · simpa [Store.write, he] using hv
  · simpa [Store.write, he] using h a

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

end StructuredLogCostFragments

section LogCostRAMDivisionStep

namespace TargetedSamplers.Structured.Word

private theorem doublePair_exec (r : Fin 9 ↪ ℕ) {τ : Tapes} {b z a : ℕ} {s : Store}
    (scale : s.mem (r 3) = z) (factor : s.mem (r 4) = a) (fit : s.Fits b)
    (hz : (2*z).size ≤ b) (hz' : (2*(2*z)).size ≤ b) (ha : (2*a).size ≤ b) :
    let t := ((doublePair r).run τ s).last
    Exec τ (fun u => u.Fits b) (doublePair r).cmd s t 3 ∧
      t.mem (r 3) = 2*z ∧ t.mem (r 4) = 2*a ∧ t.mem (r 5) = 2*(2*z) ∧ t.out = s.out ∧
      ∀ k, k ≠ r 3 → k ≠ r 4 → k ≠ r 5 → t.mem k = s.mem k := by
  have eq (i j : Fin 9) : r i = r j ↔ i=j := r.injective.eq_iff
  simp only [two_mul] at hz hz' ha
  have width : ((doublePair r).run τ s).writeWidth ≤ b := by
    simp [doublePair,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,
      Function.update_apply,eq,scale,factor,hz,hz',ha]
  refine ⟨(doublePair r).exec τ s b fit width,?_,?_,?_,rfl,?_⟩
  all_goals first
    | (intro k h3 h4 h5
       simp [doublePair,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Store.write,
         Function.update_apply,h3,h4,h5])
    | simp [doublePair,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Store.write,
        Function.update_apply,eq,scale,factor,two_mul]

/-- Select the largest shifted multiple fitting in the remainder. Only addition and a
comparison are used; doubling until the next multiple is too large takes 5j+1 primitive
instructions, where j is the selected shift. -/
theorem growPair_exec (r : Fin 9 ↪ ℕ) {τ : Tapes} {b : ℕ} (j rem z a : ℕ) (s : Store)
    (scale : s.mem (r 3) = z) (factor : s.mem (r 4) = a) (dbl : s.mem (r 5) = 2*z)
    (upper : s.mem (r 6) = rem+1) (fit : s.Fits b) (width : (2*rem).size ≤ b)
    (amountWidth : (a*2^j).size ≤ b) (low : z*2^j ≤ rem) (high : rem < 2*(z*2^j)) :
    ∃ t, Exec τ (fun u => u.Fits b) (grow r) s t (5*j+1) ∧
      t.mem (r 3) = z*2^j ∧ t.mem (r 4) = a*2^j ∧ t.mem (r 5) = 2*(z*2^j) ∧ t.out = s.out ∧
      ∀ k, k ≠ r 3 → k ≠ r 4 → k ≠ r 5 → t.mem k = s.mem k := by
  induction j generalizing s z a with
  | zero =>
    simp only [pow_zero,Nat.mul_one] at high ⊢
    exact ⟨s,.done (by rw [upper,dbl]; omega),scale,factor,dbl,rfl,fun _ _ _ _ => rfl⟩
  | succ j ih =>
    have zs : 2*z*2^j = z*2^(j+1) := by rw [pow_succ]; ring
    have zs' : 2*z ≤ rem := (by
      have h := Nat.mul_le_mul_left (2*z) (Nat.one_le_two_pow (n := j))
      rw [Nat.mul_one,zs] at h
      exact h.trans low)
    have pw (v : ℕ) (hv : v ≤ 2*rem) : v.size ≤ b := (Nat.size_le_size hv).trans width
    have az : 2*a*2^j = a*2^(j+1) := by rw [pow_succ]; ring
    have amt : 2*a ≤ a*2^(j+1) := by
      simpa only [Nat.mul_one,az] using Nat.mul_le_mul_left (2*a) (Nat.one_le_two_pow (n := j))
    obtain ⟨ex,sz,sz',db,out,save⟩ := doublePair_exec (τ := τ) r scale factor fit
      (pw _ (by omega)) (pw _ (by omega)) ((Nat.size_le_size amt).trans amountWidth)
    let u := ((doublePair r).run τ s).last
    have ne {i k : Fin 9} (h : i ≠ k) := r.injective.ne h
    have up := (save (r 6) (ne (by decide)) (ne (by decide)) (ne (by decide))).trans upper
    obtain ⟨t,loop,finalZ,finalA,finalD,log,frame⟩ := ih (2*z) (2*a) u sz sz' db up
      (ex.post fit) (by rwa [az]) (by rwa [zs]) (by rwa [zs])
    have go : ¬s.mem (r 6) ≤ s.mem (r 5) := by rw [upper,dbl]; omega
    have count : 5*(j+1)+1 = 1+3+1+(5*j+1) := by omega
    refine ⟨t,?_,?_,?_,?_,log.trans out,?_⟩
    · rw [count]; exact .again go ex loop
    · simpa only [zs] using finalZ
    · simpa only [show 2*a*2^j = a*2^(j+1) by rw [pow_succ]; ring] using finalA
    · simpa only [zs] using finalD
    · intro k h3 h4 h5; exact (frame k h3 h4 h5).trans (save k h3 h4 h5)

/-- Specialization for division, where the quotient-place register never exceeds the
shifted divisor. -/
theorem grow_exec (r : Fin 9 ↪ ℕ) {τ : Tapes} {b : ℕ} (j rem z a : ℕ) (s : Store)
    (scale : s.mem (r 3) = z) (factor : s.mem (r 4) = a) (dbl : s.mem (r 5) = 2*z)
    (upper : s.mem (r 6) = rem+1) (ha : a ≤ z) (fit : s.Fits b) (width : (2*rem).size ≤ b)
    (low : z*2^j ≤ rem) (high : rem < 2*(z*2^j)) :
    ∃ t, Exec τ (fun u => u.Fits b) (grow r) s t (5*j+1) ∧
      t.mem (r 3) = z*2^j ∧ t.mem (r 4) = a*2^j ∧ t.mem (r 5) = 2*(z*2^j) ∧ t.out = s.out ∧
      ∀ k, k ≠ r 3 → k ≠ r 4 → k ≠ r 5 → t.mem k = s.mem k := by
  have small := (Nat.mul_le_mul_right (2^j) ha).trans low
  exact growPair_exec r j rem z a s scale factor dbl upper fit width
    ((Nat.size_le_size (show a*2^j ≤ 2*rem by omega)).trans width) low high

/-- The binary shift is bounded by the number of bits of the dividend, independent of
the numerical quotient. -/
theorem shift_exists {d x : ℕ} (hd : 0 < d) (hx : d ≤ x) :
    ∃ j ≤ x.size, d*2^j ≤ x ∧ x < 2*(d*2^j) := by
  let q := x/d
  have hp : 0 < q := Nat.div_pos hx hd
  have pos := Nat.size_pos.mpr hp
  let j := q.size-1
  have hj : j+1 = q.size := by dsimp [j]; omega
  have hlo : 2^j ≤ q := Nat.lt_size.mp (by omega)
  have hhi : q < 2^(j+1) := by rw [hj]; exact Nat.lt_size_self q
  have small := (Nat.le_div_iff_mul_le hd).mp hlo
  have large := (Nat.div_lt_iff_lt_mul hd).mp hhi
  refine ⟨j,le_trans (by omega : j ≤ q.size) (Nat.size_le_size (Nat.div_le_self x d)),?_,?_⟩
  · simpa [Nat.mul_comm] using small
  · have e : 2^(j+1)*d = 2*(d*2^j) := by rw [pow_succ]; ring
    rwa [← e]

end TargetedSamplers.Structured.Word

end LogCostRAMDivisionStep

section LogCostRAMDivision

namespace TargetedSamplers.Structured.Word

structure DivRegs (r : Fin 9 ↪ ℕ) (s : Store) (rem d q : ℕ) : Prop where
  remReg : s.mem (r 0) = rem
  divisor : s.mem (r 1) = d
  quotient : s.mem (r 2) = q
  upper : s.mem (r 6) = rem+1
  zero : s.mem (r 7) = 0
  one : s.mem (r 8) = 1

theorem DivRegs.scratch {r : Fin 9 ↪ ℕ} {s t : Store} {rem d q : ℕ} (h : DivRegs r s rem d q)
    (frame : ∀ a, a ≠ r 3 → a ≠ r 4 → a ≠ r 5 → t.mem a = s.mem a) : DivRegs r t rem d q := by
  have get (i : Fin 9) (a : i ≠ 3) (b : i ≠ 4) (c : i ≠ 5) := frame (r i) (r.injective.ne a) (r.injective.ne b) (r.injective.ne c)
  exact ⟨(get 0 (by decide) (by decide) (by decide)).trans h.remReg,
    (get 1 (by decide) (by decide) (by decide)).trans h.divisor,(get 2 (by decide) (by decide) (by decide)).trans h.quotient,
    (get 6 (by decide) (by decide) (by decide)).trans h.upper,(get 7 (by decide) (by decide) (by decide)).trans h.zero,
    (get 8 (by decide) (by decide) (by decide)).trans h.one⟩

private theorem start_exec {r : Fin 9 ↪ ℕ} {τ : Tapes} {b rem d q : ℕ} {s : Store}
    (hr : DivRegs r s rem d q) (fit : s.Fits b) (hb : 1 ≤ b) (wd : (2*d).size ≤ b) :
    let t := ((startRound r).run τ s).last
    Exec τ (fun u => u.Fits b) (startRound r).cmd s t 3 ∧ t.mem (r 3) = d ∧ t.mem (r 4) = 1 ∧
      t.mem (r 5) = 2*d ∧ t.out = s.out ∧ ∀ a, a ≠ r 3 → a ≠ r 4 → a ≠ r 5 → t.mem a = s.mem a := by
  have eq (i j : Fin 9) : r i = r j ↔ i=j := r.injective.eq_iff
  have h := hr.divisor ▸ fit (r 1)
  have ww : ((startRound r).run τ s).writeWidth ≤ b := by
    simp only [two_mul] at wd
    simp [startRound,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,
      Function.update_apply,eq,hr.divisor,hr.zero,wd,h,hb]
  refine ⟨(startRound r).exec τ s b fit ww,?_,?_,?_,rfl,?_⟩
  all_goals first
    | (intro a n3 n4 n5; simp [startRound,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Store.write,
        Function.update_apply,n3,n4,n5])
    | simp [startRound,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Store.write,
        Function.update_apply,eq,hr.divisor,hr.zero,two_mul]

theorem finishRound_exec {r : Fin 9 ↪ ℕ} {τ : Tapes} {b rem d q z a : ℕ} {s : Store}
    (hr : DivRegs r s rem d q) (scale : s.mem (r 3) = z) (amount : s.mem (r 4) = a) (fit : s.Fits b)
    (wrem : (rem-z+1).size ≤ b) (wq : (q+a).size ≤ b) :
    let t := ((finishRound r).run τ s).last
    Exec τ (fun u => u.Fits b) (finishRound r).cmd s t 3 ∧ DivRegs r t (rem-z) d (q+a) ∧
      t.out = s.out ∧ ∀ k, (∀ i, k ≠ r i) → t.mem k = s.mem k := by
  have eq (i j : Fin 9) : r i = r j ↔ i=j := r.injective.eq_iff
  have ww' := (Nat.size_le_size (show rem-z ≤ rem-z+1 by omega)).trans wrem
  have ww : ((finishRound r).run τ s).writeWidth ≤ b := by
    simp [finishRound,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,
      Function.update_apply,eq,hr.remReg,hr.quotient,hr.one,scale,amount,ww',wrem,wq]
  refine ⟨(finishRound r).exec τ s b fit ww,?_,rfl,?_⟩
  · constructor <;> simp [finishRound,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Store.write,
      Function.update_apply,eq,hr.remReg,hr.divisor,hr.quotient,hr.zero,hr.one,scale,amount]
  · intro k hk
    simp [finishRound,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Store.write,Function.update_apply,hk]

theorem size_lt_of_double_lt {old new : ℕ} (h : 2*new < old) : new.size < old.size := by
  have ho := Nat.size_pos.mpr (show 0 < old by omega)
  have e : 2^old.size = 2^(old.size-1)*2 := by
    conv_lhs => rw [show old.size = old.size-1+1 by omega,pow_succ]
  have lim := Nat.lt_size_self old
  rw [e] at lim
  have hn := Nat.size_le.mpr (show new < 2^(old.size-1) by omega)
  omega

/-- Quotient selection by maximal doubling removes at least half of the remainder at
each round. Thus division is polynomial in bit *length* on the addition-only RAM. -/
theorem quotientLoop_exec (r : Fin 9 ↪ ℕ) {τ : Tapes} {b : ℕ} (x d : ℕ) (hd : 0 < d)
    (hb : 1 ≤ b) (width : (2*x+2).size ≤ b) (fuel rem q : ℕ) (s : Store)
    (hr : DivRegs r s rem d q) (law : d*q+rem = x) (bound : rem.size ≤ fuel) (fit : s.Fits b) :
    ∃ t j, Exec τ (fun u => u.Fits b) (quotientLoop r) s t j ∧ j ≤ fuel*(5*x.size+9)+1 ∧
      DivRegs r t (x%d) d (x/d) ∧ t.out = s.out ∧ ∀ a, (∀ i, a ≠ r i) → t.mem a = s.mem a := by
  have done {rem q fuel : ℕ} {s : Store} (hr : DivRegs r s rem d q) (law : d*q+rem = x) (lt : rem < d) :
      ∃ t j, Exec τ (fun u => u.Fits b) (quotientLoop r) s t j ∧ j ≤ fuel*(5*x.size+9)+1 ∧
        DivRegs r t (x%d) d (x/d) ∧ t.out = s.out ∧ ∀ a, (∀ i, a ≠ r i) → t.mem a = s.mem a := by
    have eq : x = rem+d*q := by omega
    refine ⟨s,1,.done (by rw [hr.upper,hr.divisor]; omega),by omega,?_,rfl,fun _ _ => rfl⟩
    simpa only [eq,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt lt,Nat.add_mul_div_left _ _ hd,
      Nat.div_eq_of_lt lt,Nat.zero_add] using hr
  induction fuel generalizing s rem q with
  | zero =>
    have h := Nat.size_eq_zero.mp (by omega : rem.size = 0)
    exact done hr law (by omega)
  | succ fuel ih =>
    by_cases stop : rem < d
    · exact done hr law stop
    have le : d ≤ rem := by omega
    obtain ⟨k,hk,low,high⟩ := shift_exists hd le
    have wr (v : ℕ) (hv : v ≤ 2*x+2) := (Nat.size_le_size hv).trans width
    obtain ⟨init,z,a,z₂,oi,fi⟩ := start_exec (τ := τ) hr fit hb (wr _ (by omega))
    obtain ⟨v,loop,scale,amount,_,og,fg⟩ := grow_exec (τ := τ) r k rem d 1 _ z a z₂
      (hr.scratch fi).upper hd (init.post fit) (wr _ (by omega)) low high
    let pow := 2^k
    let rem' := rem-d*pow
    have next : d*(q+pow)+rem' = x := by
      dsimp [rem',pow]; rw [Nat.mul_add]; omega
    have qx : q+pow ≤ x := by
      have h := Nat.mul_le_mul_right (q+pow) hd
      simp only [Nat.one_mul] at h; omega
    have red : 2*rem' < rem := by dsimp [rem',pow]; omega
    have shrink := size_lt_of_double_lt red
    obtain ⟨finish,hr',ofin,ff⟩ := finishRound_exec (τ := τ) ((hr.scratch fi).scratch fg) scale
      (show v.mem (r 4) = pow by simpa [pow] using amount) (loop.post (init.post fit))
      (wr _ (by change rem-d*pow+1 ≤ _; omega)) (wr _ (by omega))
    obtain ⟨t,j,rest,hj,reg,out,fre⟩ := ih rem' (q+pow) _ hr' next (by omega) (finish.post (loop.post (init.post fit)))
    have go : ¬s.mem (r 6) ≤ s.mem (r 1) := by rw [hr.upper,hr.divisor]; omega
    have hx := hk.trans (Nat.size_le_size (by omega : rem ≤ x))
    refine ⟨t,_,.again go (init.seq (loop.seq finish)) rest,?_,reg,out.trans (ofin.trans (og.trans oi)),?_⟩
    · rw [Nat.succ_mul fuel (5*x.size+9)]; omega
    · intro addr f
      exact (fre addr f).trans ((ff addr f).trans ((fg addr (f 3) (f 4) (f 5)).trans (fi addr (f 3) (f 4) (f 5))))

/-- Shared zero accumulator, constant registers, and upper bound for shifted arithmetic. -/
theorem initDiv_exec (r : Fin 9 ↪ ℕ) {τ : Tapes} {width : ℕ} (x d : ℕ) (s : Store)
    (input : s.mem (r 0) = x) (divisor : s.mem (r 1) = d) (fit : s.Fits width) (hb : 1 ≤ width)
    (upper : (x+1).size ≤ width) :
    let u := ((initDiv r).run τ s).last
    Exec τ (fun v => v.Fits width) (initDiv r).cmd s u 4 ∧ DivRegs r u x d 0 ∧ u.out = s.out ∧
      ∀ a, (∀ i, a ≠ r i) → u.mem a = s.mem a := by
  have eq (i j : Fin 9) : r i = r j ↔ i=j := r.injective.eq_iff
  let u := ((initDiv r).run τ s).last
  have good : ((initDiv r).run τ s).writeWidth ≤ width := by
    simp [initDiv,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,
      Function.update_apply,eq,input,hb,upper]
  have init : Exec τ (fun v => v.Fits width) (initDiv r).cmd s u 4 := (initDiv r).exec τ s width fit good
  have hr : DivRegs r u x d 0 := by
    constructor <;> simp [u,initDiv,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Store.write,
      Function.update_apply,eq,input,divisor]
  have fr (a : ℕ) (f : ∀ i, a ≠ r i) : u.mem a = s.mem a := by
    simp [u,initDiv,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Store.write,Function.update_apply,f]
  exact ⟨init,hr,rfl,fr⟩

/-- Compute both natural division and remainder on the posted RAM, including divisor
zero. A b-bit dividend uses at most 5b²+9b+7 primitive instructions; the largest new
word is at most 2x+2. Caller memory is framed. -/
theorem divMod_exec (r : Fin 9 ↪ ℕ) {τ : Tapes} {width : ℕ} (x d : ℕ) (s : Store)
    (input : s.mem (r 0) = x) (divisor : s.mem (r 1) = d) (fit : s.Fits width)
    (hb : 1 ≤ width) (hw : (2*x+2).size ≤ width) :
    ∃ t j, Exec τ (fun u => u.Fits width) (divMod r) s t j ∧ j ≤ x.size*(5*x.size+9)+7 ∧
      t.mem (r 0) = x%d ∧ t.mem (r 2) = x/d ∧ t.out = s.out ∧ ∀ a, (∀ i, a ≠ r i) → t.mem a = s.mem a := by
  let u := ((initDiv r).run τ s).last
  obtain ⟨init,hr,_,fr⟩ := initDiv_exec (τ := τ) r x d s input divisor fit hb
    ((Nat.size_le_size (by omega : x+1 ≤ 2*x+2)).trans hw)
  by_cases hd : d = 0
  · refine ⟨u,_,init.seq (.yes (by rw [hr.divisor,hr.zero,hd]) (.skip u)),by omega,
      by simpa [hd] using hr.remReg,by simpa [hd] using hr.quotient,rfl,fr⟩
  · obtain ⟨t,j,loop,hj,out,ot,ft⟩ := quotientLoop_exec (τ := τ) r x d (by omega) hb hw x.size x 0 u hr
      (by simp) le_rfl (init.post fit)
    refine ⟨t,_,init.seq (.no (by rw [hr.divisor,hr.zero]; omega) loop),by omega,
      out.remReg,out.quotient,ot,fun a f => (ft a f).trans (fr a f)⟩

end TargetedSamplers.Structured.Word

end LogCostRAMDivision

section LogCostRAMMultiply

namespace TargetedSamplers.Structured.Word

private theorem startMultiple_exec {τ : TargetedSamplers.Tapes} (r : Fin 9 ↪ ℕ) {b rem y q : ℕ} {s : Store}
    (h : DivRegs r s rem y q) (fit : s.Fits b) (hb : 2 ≤ b) :
    let u := ((startMultiple r).run τ s).last
    Exec τ (fun t => t.Fits b) (startMultiple r).cmd s u 3 ∧ u.mem (r 3) = 1 ∧
      u.mem (r 4) = y ∧ u.mem (r 5) = 2 ∧ u.out = s.out ∧
      ∀ a, a ≠ r 3 → a ≠ r 4 → a ≠ r 5 → u.mem a = s.mem a := by
  have eq (i j : Fin 9) : r i = r j ↔ i=j := r.injective.eq_iff
  have hy := h.divisor ▸ fit (r 1)
  have two : (2:ℕ).size ≤ b := (by decide : (2:ℕ).size ≤ 2).trans hb
  have safe : ((startMultiple r).run τ s).writeWidth ≤ b := by
    simp [startMultiple,Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,eq,h.divisor,h.zero,hy,two]; omega
  refine ⟨(startMultiple r).exec τ s b fit safe,?_,?_,?_,rfl,?_⟩
  all_goals first
    | (intro a h₃ h₄ h₅; simp [startMultiple,Structured.sequence,Fragment.run,Op.eval,Store.write,h₃,h₄,h₅])
    | simp [startMultiple,Structured.sequence,Fragment.run,Op.eval,Store.write,eq,h.divisor,h.zero]

private theorem multiplyLoop_exec {τ : TargetedSamplers.Tapes} (r : Fin 9 ↪ ℕ) {b : ℕ} (x y : ℕ)
    (hb : 2 ≤ b) (wx : (2*x+2).size ≤ b) (wp : (x*y).size ≤ b) (fuel rem q : ℕ) (s : Store)
    (hr : DivRegs r s rem y q) (hx : rem ≤ x) (law : q+rem*y = x*y)
    (bound : rem.size ≤ fuel) (fit : s.Fits b) :
    ∃ t j, Exec τ (fun v => v.Fits b) (multiplyLoop r) s t j ∧ j ≤ fuel*(5*x.size+9)+1 ∧
      t.mem (r 2) = x*y ∧ t.out = s.out ∧ ∀ a, (∀ i, a ≠ r i) → t.mem a = s.mem a := by
  have done {n q : ℕ} {s : Store} (hr : DivRegs r s 0 y q) (h : q+0*y = x*y) :
      ∃ t j, Exec τ (fun v => v.Fits b) (multiplyLoop r) s t j ∧ j ≤ n*(5*x.size+9)+1 ∧
        t.mem (r 2) = x*y ∧ t.out = s.out ∧ ∀ a, (∀ i, a ≠ r i) → t.mem a = s.mem a :=
    ⟨s,1,.done (by rw [hr.remReg,hr.zero]),by omega,hr.quotient.trans (by simpa using h),rfl,fun _ _ => rfl⟩
  induction fuel generalizing rem q s with
  | zero =>
    have zero : rem = 0 := Nat.size_eq_zero.mp (by omega)
    subst rem; exact done hr law
  | succ fuel ih =>
    by_cases hzero : rem=0
    · subst rem; exact done hr law
    obtain ⟨k,hk,lo,hi⟩ := shift_exists (by decide : 0 < 1) (show 1 ≤ rem by omega)
    simp only [Nat.one_mul] at lo hi
    let z := 2^k
    have amount : y*z ≤ x*y := by
      simpa only [Nat.mul_comm y z] using Nat.mul_le_mul_right y (lo.trans hx)
    obtain ⟨init,start,coeff,dbl,oi,fi⟩ := startMultiple_exec (τ := τ) r hr fit hb
    obtain ⟨u,loop,pow,term,_,og,fg⟩ := growPair_exec (τ := τ) r k rem 1 y _ start coeff dbl (hr.scratch fi).upper
      (init.post fit) ((Nat.size_le_size (by omega : 2*rem ≤ 2*x+2)).trans wx)
      ((Nat.size_le_size amount).trans wp) (by simpa using lo) (by simpa using hi)
    have split : z+(rem-z) = rem := Nat.add_sub_of_le lo
    have product := congrArg (fun v : ℕ => v*y) split
    simp only [Nat.add_mul] at product
    have law' : (q+y*z)+(rem-z)*y = x*y := by rw [Nat.mul_comm y z]; omega
    have sumWidth := (Nat.size_le_size (show q+y*z ≤ x*y by omega)).trans wp
    obtain ⟨finish,hnext,ofin,ff⟩ := finishRound_exec (τ := τ) ((hr.scratch fi).scratch fg)
      (show u.mem (r 3) = z by simpa only [Nat.one_mul] using pow) term (loop.post (init.post fit))
      ((Nat.size_le_size (by omega : rem-z+1 ≤ 2*x+2)).trans wx) sumWidth
    have shrink := size_lt_of_double_lt (show 2*(rem-z) < rem by change 2*(rem-2^k) < rem; omega)
    obtain ⟨t,j,tail,hj,answer,out,frame⟩ := ih (rem-z) (q+y*z) _ hnext (by omega) law' (by omega)
      (finish.post (loop.post (init.post fit)))
    have go : ¬s.mem (r 0) ≤ s.mem (r 7) := by rw [hr.remReg,hr.zero]; omega
    have cost := hk.trans (Nat.size_le_size hx)
    refine ⟨t,_,.again go (init.seq (loop.seq finish)) tail,?_,answer,out.trans (ofin.trans (og.trans oi)),?_⟩
    · rw [Nat.succ_mul fuel (5*x.size+9)]; omega
    · intro a free
      exact (frame a free).trans ((ff a free).trans ((fg a (free 3) (free 4) (free 5)).trans (fi a (free 3) (free 4) (free 5))))

/-- Multiply two arbitrary words on the addition-only logarithmic-cost RAM. Register 2
receives the exact product; the step count is quadratic in the bit length of the first
operand, including zero. No loop runs once per unit of an exponential operand. -/
theorem multiply_exec {τ : TargetedSamplers.Tapes} (r : Fin 9 ↪ ℕ) {b : ℕ} (x y : ℕ) (s : Store)
    (inX : s.mem (r 0) = x) (inY : s.mem (r 1) = y) (fit : s.Fits b) (hb : 2 ≤ b)
    (wx : (2*x+2).size ≤ b) (wp : (x*y).size ≤ b) :
    ∃ t j, Exec τ (fun v => v.Fits b) (multiply r) s t j ∧ j ≤ x.size*(5*x.size+9)+5 ∧
      t.mem (r 2) = x*y ∧ t.out = s.out ∧ ∀ a, (∀ i, a ≠ r i) → t.mem a = s.mem a := by
  obtain ⟨init,regs,out,save⟩ := initDiv_exec (τ := τ) r x y s inX inY fit (by omega)
    ((Nat.size_le_size (by omega : x+1 ≤ 2*x+2)).trans wx)
  obtain ⟨t,j,loop,cost,correct,ret,frame⟩ := multiplyLoop_exec r x y hb wx wp x.size x 0 _ regs le_rfl
    (by simp) le_rfl (init.post fit)
  exact ⟨t,_,init.seq loop,by omega,correct,ret.trans out,fun a free => (frame a free).trans (save a free)⟩

end TargetedSamplers.Structured.Word

end LogCostRAMMultiply

section LogCostRAMPower

namespace TargetedSamplers.Structured.Word

private structure PowerState (r : Fin 13 ↪ ℕ) (s : Store) (x e a : ℕ) : Prop where
  base : s.mem (r 9) = x
  count : s.mem (r 10) = e
  result : s.mem (r 2) = a
  zero : s.mem (r 11) = 0
  one : s.mem (r 12) = 1

private theorem powerLoop_exec {τ : TargetedSamplers.Tapes} (r : Fin 13 ↪ ℕ) {b : ℕ} (x e a : ℕ)
    (s : Store) (h : PowerState r s x e a) (fit : s.Fits b) (hb : 2 ≤ b) (wx : (2*x+2).size ≤ b)
    (finalWidth : (a*x^e).size ≤ b) :
    ∃ t j, Exec τ (fun v => v.Fits b) (powerLoop r) s t j ∧ j ≤ e*(x.size*(5*x.size+9)+10)+1 ∧
      t.mem (r 2) = a*x^e ∧ t.out = s.out ∧ ∀ v, (∀ i, v ≠ r i) → t.mem v = s.mem v := by
  have eq (i j : Fin 13) : r i = r j ↔ i=j := r.injective.eq_iff
  have ne {i j : Fin 13} (hne : i ≠ j) := r.injective.ne hne
  induction e generalizing s a with
  | zero =>
    exact ⟨s,1,.done (by rw [h.count,h.zero]),by simp,by simpa using h.result,rfl,fun _ _ => rfl⟩
  | succ e ih =>
    let u := ((powerOperands r).run τ s).last
    have xw := h.base ▸ fit (r 9)
    have aw := h.result ▸ fit (r 2)
    have safe : ((powerOperands r).run τ s).writeWidth ≤ b := by
      simp [powerOperands,Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,eq,h.base,h.result,h.zero,xw,aw]
    have setup := (powerOperands r).exec τ s b fit safe
    have xarg : u.mem (r 0) = x := by simp [u,powerOperands,Structured.sequence,Fragment.run,Op.eval,Store.write,eq,h.base,h.zero]
    have aarg : u.mem (r 1) = a := by simp [u,powerOperands,Structured.sequence,Fragment.run,Op.eval,Store.write,eq,h.result,h.zero]
    have old (v : ℕ) (h₀ : v ≠ r 0) (h₁ : v ≠ r 1) : u.mem v = s.mem v := by
      simp [u,powerOperands,Structured.sequence,Fragment.run,Op.eval,Store.write,h₀,h₁]
    have step : x ≤ x^(e+1) := by
      by_cases z : x=0
      · simp [z]
      · simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < x) (by omega : 1 ≤ e+1)
    have part : x*a ≤ a*x^(e+1) := by simpa only [Nat.mul_comm x a] using Nat.mul_le_mul_left a step
    obtain ⟨v,k,mul,hk,product,out,fr⟩ := multiply_exec (τ := τ) (powerMulRegs r) x a u xarg aarg
      (setup.post fit) hb wx ((Nat.size_le_size part).trans finalWidth)
    have keep (i : Fin 13) (large : 9 ≤ i.val) : v.mem (r i) = s.mem (r i) := by
      have diff (j : Fin 13) (hj : j.val < 9) : i ≠ j := by intro he; subst j; omega
      have outside (j : Fin 9) : r i ≠ powerMulRegs r j := by
        intro he
        have same := congrArg (fun u : Fin 13 => u.val) (r.injective he)
        change i.val = j.val at same; have := j.isLt; omega
      exact (fr _ outside).trans (old _ (ne (diff 0 (by decide))) (ne (diff 1 (by decide))))
    let w := v.write (r 10) e
    have update : (Op.sub (r 10) (r 10) (r 12)).eval τ v = w := by
      simp [Op.eval,w,(keep 10 (by decide)).trans h.count,(keep 12 (by decide)).trans h.one]
    have countWidth : (e+1).size ≤ b := by rw [← h.count]; exact fit (r 10)
    have fw := Store.write_fits (mul.post (setup.post fit)) (r 10)
      ((Nat.size_le_size (Nat.le_succ e)).trans countWidth)
    have dec : Exec τ (fun v => v.Fits b) (.op (.sub (r 10) (r 10) (r 12))) v w 1 := by
      simpa only [update] using (Exec.op (τ := τ) (inv := fun v => v.Fits b) v (.sub (r 10) (r 10) (r 12)) (by rwa [update]))
    change v.mem (r 2) = x*a at product
    have next : PowerState r w x e (x*a) := by
      constructor <;> simp [w,Store.write,eq,keep 9 (by decide),keep 11 (by decide),keep 12 (by decide),
        h.base,h.zero,h.one,product]
    have total : x*a*x^e = a*x^(e+1) := by rw [pow_succ]; ring
    obtain ⟨t,j,loop,hj,last,ret,save⟩ := ih (x*a) w next fw (by rwa [total])
    have go : ¬s.mem (r 10) ≤ s.mem (r 11) := by rw [h.count,h.zero]; omega
    have setupSteps : ((powerOperands r).run τ s).steps = 2 := rfl
    refine ⟨t,_,.again go (setup.seq (mul.seq dec)) loop,?_,last.trans total,ret.trans out,?_⟩
    · rw [Nat.succ_mul e (x.size*(5*x.size+9)+10)]; omega
    · intro v' free
      have outside (j : Fin 9) : v' ≠ powerMulRegs r j := free ⟨j.val,by have := j.isLt; omega⟩
      exact (save _ free).trans ((show w.mem v' = v.mem v' by simp [w,Store.write,free]).trans
        ((fr v' outside).trans (old _ (free 0) (free 1))))

/-- Raise a word to an input exponent by counted multiplication. The loop count is the
exponent itself, and each iteration costs a polynomial in the base's bit length. -/
theorem power_exec {τ : TargetedSamplers.Tapes} (r : Fin 13 ↪ ℕ) {b : ℕ} (x e : ℕ) (s : Store)
    (base : s.mem (r 9) = x) (exponent : s.mem (r 10) = e) (fit : s.Fits b) (hb : 2 ≤ b)
    (wx : (2*x+2).size ≤ b) (wp : (x^e).size ≤ b) :
    ∃ t j, Exec τ (fun v => v.Fits b) (power r) s t j ∧ j ≤ e*(x.size*(5*x.size+9)+10)+4 ∧
      t.mem (r 2) = x^e ∧ t.out = s.out ∧ ∀ v, (∀ i, v ≠ r i) → t.mem v = s.mem v := by
  have eq (i j : Fin 13) : r i = r j ↔ i=j := r.injective.eq_iff
  let u := ((initPower r).run τ s).last
  have safe : ((initPower r).run τ s).writeWidth ≤ b := by
    simp [initPower,Structured.sequence,Fragment.run,Op.written]; omega
  have init := (initPower r).exec τ s b fit safe
  have regs : PowerState r u x e 1 := by
    constructor <;> simp [u,initPower,Structured.sequence,Fragment.run,Op.eval,Store.write,eq,base,exponent]
  obtain ⟨t,j,loop,hj,last,ret,fr⟩ := powerLoop_exec (τ := τ) r x e 1 u regs (init.post fit) hb wx (by simpa using wp)
  have count : ((initPower r).run τ s).steps = 3 := rfl
  refine ⟨t,_,init.seq loop,by omega,by simpa using last,ret,?_⟩
  intro v free
  simpa [u,initPower,Structured.sequence,Fragment.run,Op.eval,Store.write,free] using fr v free

end TargetedSamplers.Structured.Word

end LogCostRAMPower

section LogCostRAMArithmetic

namespace TargetedSamplers.Structured.Word

def Arithmetic.steps : Arithmetic → ℕ → ℕ → ℕ
  | .mul, x, _ => x.size*(5*x.size+9)+5
  | .div, x, _ | .mod, x, _ => x.size*(5*x.size+9)+7
  | .pow, x, y => y*(x.size*(5*x.size+9)+10)+4

private theorem Arithmetic.native_exec {τ : TargetedSamplers.Tapes} (op : Arithmetic) {b : ℕ}
    (x y : ℕ) (s : Store) (left : s.mem op.leftReg = x) (right : s.mem op.rightReg = y)
    (fit : s.Fits b) (hb : 2 ≤ b) (wx : (2*x+2).size ≤ b) (wy : (op.value x y).size ≤ b) :
    ∃ t j, Exec τ (fun u => u.Fits b) op.native s t j ∧ j ≤ op.steps x y ∧
      t.mem op.outReg = op.value x y ∧ t.out = s.out ∧ ∀ a, 13 ≤ a → t.mem a = s.mem a := by
  have outside (n : ℕ) (hn : n ≤ 13) (a : ℕ) (ha : 13 ≤ a) (i : Fin n) : a ≠ Fin.valEmbedding i := by
    change a ≠ i.val; have := i.isLt; omega
  cases op with
  | mul =>
    obtain ⟨t,j,ex,hj,ans,out,fr⟩ := multiply_exec (τ := τ) Fin.valEmbedding x y s left right fit hb wx wy
    exact ⟨t,j,ex,hj,ans,out,fun a ha => fr a (outside 9 (by decide) a ha)⟩
  | div =>
    obtain ⟨t,j,ex,hj,_,ans,out,fr⟩ := divMod_exec (τ := τ) Fin.valEmbedding x y s left right fit (by omega) wx
    exact ⟨t,j,ex,hj,ans,out,fun a ha => fr a (outside 9 (by decide) a ha)⟩
  | mod =>
    obtain ⟨t,j,ex,hj,ans,_,out,fr⟩ := divMod_exec (τ := τ) Fin.valEmbedding x y s left right fit (by omega) wx
    exact ⟨t,j,ex,hj,ans,out,fun a ha => fr a (outside 9 (by decide) a ha)⟩
  | pow =>
    obtain ⟨t,j,ex,hj,ans,out,fr⟩ := power_exec (τ := τ) Fin.valEmbedding x y s left right fit hb wx wy
    exact ⟨t,j,ex,hj,ans,out,fun a ha => fr a (outside 13 le_rfl a ha)⟩

private theorem loadArgs_exec {τ : TargetedSamplers.Tapes} {b : ℕ} (p q l r : ℕ) (s : Store)
    (hp : p < 13) (hq : q < 13) (ne : p ≠ q) (fit : s.Fits b) :
    let t := ((loadArgs p q l r).run τ s).last
    Exec τ (fun u => u.Fits b) (loadArgs p q l r).cmd s t 3 ∧ t.mem p = s.mem (cell l) ∧
      t.mem q = s.mem (cell r) ∧ t.mem 13 = 0 ∧ t.out = s.out ∧ ∀ i, t.mem (cell i) = s.mem (cell i) := by
  have far (i v : ℕ) (h : v ≤ 13) : cell i ≠ v := by dsimp [cell]; omega
  have z : 13 ≠ p := by omega
  have safe : ((loadArgs p q l r).run τ s).writeWidth ≤ b := by
    simp [loadArgs,Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,far l 13 le_rfl,far r 13 le_rfl,
      far r p hp.le,z,fit (cell l),fit (cell r)]
  refine ⟨(loadArgs p q l r).exec τ s b fit safe,?_,?_,?_,rfl,?_⟩
  all_goals first
    | (intro i; simp [loadArgs,Structured.sequence,Fragment.run,Op.eval,Store.write,far i p hp.le,far i q hq.le,far i 13 le_rfl])
    | simp [loadArgs,Structured.sequence,Fragment.run,Op.eval,Store.write,ne,far l 13 le_rfl,far r 13 le_rfl,
        far r p hp.le,z,show 13 ≠ q by omega]

theorem Arithmetic.call_exec {τ : TargetedSamplers.Tapes} {b : ℕ} (op : Arithmetic) (d l r : ℕ) (s : Store)
    (fit : s.Fits b) (hb : 2 ≤ b) :
    let x := s.mem (cell l)
    let y := s.mem (cell r)
    (2*x+2).size ≤ b → (op.value x y).size ≤ b →
    ∃ t j, Exec τ (fun u => u.Fits b) (op.call d l r) s t j ∧ j ≤ op.steps x y+4 ∧ t.out = s.out ∧
      ∀ i, t.mem (cell i) = if i=d then op.value x y else s.mem (cell i) := by
  intro x y wx wy
  obtain ⟨load,left,right,zero,out₀,fr₀⟩ := loadArgs_exec (τ := τ) op.leftReg op.rightReg l r s
    (by cases op <;> decide) (by cases op <;> decide) (by cases op <;> decide) fit
  obtain ⟨v,j,run,hj,value,out,fr⟩ := op.native_exec (τ := τ) x y _ left right (load.post fit) hb wx wy
  let t := v.write (cell d) (op.value x y)
  have put : (Op.add (cell d) op.outReg 13).eval τ v = t := by simp [Op.eval,t,value,(fr 13 le_rfl).trans zero]
  have write : Exec τ (fun u => u.Fits b) (.op (.add (cell d) op.outReg 13)) v t 1 := by
    simpa only [put] using (Exec.op (τ := τ) (inv := fun u => u.Fits b) v (.add (cell d) op.outReg 13)
      (by rw [put]; exact Store.write_fits (run.post (load.post fit)) _ wy))
  refine ⟨t,_,load.seq (run.seq write),by omega,out.trans out₀,?_⟩
  intro i
  by_cases eq : i=d
  · subst i; simp [t,Store.write]
  · have ne : cell i ≠ cell d := by simpa [cell] using eq
    simp [t,Store.write,ne,eq,(fr (cell i) (by dsimp [cell]; omega)).trans (fr₀ i)]

end TargetedSamplers.Structured.Word

end LogCostRAMArithmetic

section LogCostRAMArithmeticCircuit

namespace TargetedSamplers.Structured.Word

def Expression.steps (v : ℕ → ℕ) : Expression → ℕ
  | .arithmetic op l r => op.steps (v l) (v r)+4
  | _ => 1

def Expression.width (v : ℕ → ℕ) (e : Expression) : ℕ :=
  match e with
  | .arithmetic _ l _ => max (2*v l+2).size (e.eval v).size
  | _ => (e.eval v).size

/-- The only arithmetic loop counted in the numerical value of an operand is a power's
exponent. The other primitives have cost polynomial in word width. -/
def Expression.multiplicity (v : ℕ → ℕ) : Expression → ℕ
  | .arithmetic .pow _ r => v r+1
  | _ => 1

theorem Expression.steps_le (e : Expression) (v : ℕ → ℕ) (b : ℕ) (h : e.width v ≤ b) :
    e.steps v ≤ e.multiplicity v*(b*(5*b+9)+15) := by
  cases e with
  | literal | add | sub => simp [steps,multiplicity]
  | arithmetic op l r =>
    have wl := (max_le_iff.mp h).1
    have le := (Nat.size_le_size (show v l ≤ 2*v l+2 by omega)).trans wl
    have quad := Nat.mul_le_mul le (show 5*(v l).size+9 ≤ 5*b+9 by omega)
    cases op with
    | mul | div | mod => simp [steps,multiplicity,Arithmetic.steps]; omega
    | pow =>
      simp only [steps,multiplicity,Arithmetic.steps,Nat.succ_mul (v r) (b*(5*b+9)+15)]
      have := Nat.mul_le_mul_left (v r) (show (v l).size*(5*(v l).size+9)+10 ≤ b*(5*b+9)+15 by omega)
      omega

def Assignment.update (a : Assignment) (v : ℕ → ℕ) := Function.update v a.dst (a.rhs.eval v)

def Represents (s : Store) (v : ℕ → ℕ) : Prop := ∀ i, s.mem (cell i) = v i

theorem Assignment.exec {τ : TargetedSamplers.Tapes} {b : ℕ} (a : Assignment) (v : ℕ → ℕ) (s : Store)
    (h : Represents s v) (fit : s.Fits b) (hb : 2 ≤ b) (width : a.rhs.width v ≤ b) :
    ∃ t j, Exec τ (fun u => u.Fits b) a.cmd s t j ∧ j ≤ a.rhs.steps v ∧ Represents t (a.update v) ∧ t.out = s.out := by
  obtain ⟨d,e⟩ := a
  have simple (op : Op) (z : ℕ) (ev : op.eval τ s = s.write (cell d) z) (wz : z.size ≤ b) :
      let t := s.write (cell d) z
      Exec τ (fun u => u.Fits b) (.op op) s t 1 ∧ Represents t (Function.update v d z) ∧ t.out = s.out := by
    refine ⟨?_,?_,rfl⟩
    · simpa only [ev] using (Exec.op (τ := τ) (inv := fun u => u.Fits b) s op (by rw [ev]; exact Store.write_fits fit _ wz))
    · intro i
      by_cases eq : i=d
      · subst i; simp [Store.write]
      · have dif : cell i ≠ cell d := by simpa [cell] using eq
        simpa [Store.write,Function.update_of_ne eq,Function.update_of_ne dif] using h i
  cases e with
  | literal x =>
    obtain ⟨ex,post,out⟩ := simple (.const (cell d) x) x rfl width
    exact ⟨_,1,ex,le_rfl,post,out⟩
  | add l r =>
    obtain ⟨ex,post,out⟩ := simple (.add (cell d) (cell l) (cell r)) (v l+v r) (by simp [Op.eval,h l,h r]) width
    exact ⟨_,1,ex,le_rfl,post,out⟩
  | sub l r =>
    obtain ⟨ex,post,out⟩ := simple (.sub (cell d) (cell l) (cell r)) (v l-v r) (by simp [Op.eval,h l,h r]) width
    exact ⟨_,1,ex,le_rfl,post,out⟩
  | arithmetic op l r =>
    change max (2*v l+2).size (op.value (v l) (v r)).size ≤ b at width
    obtain ⟨wl,wr⟩ := max_le_iff.mp width
    obtain ⟨t,j,ex,work,out,regs⟩ := op.call_exec (τ := τ) d l r s fit hb (by rwa [h l]) (by rwa [h l,h r])
    refine ⟨t,j,ex,by simpa only [Expression.steps,h l,h r] using work,?_,out⟩
    intro i
    by_cases eq : i=d
    · subst i; simpa [Assignment.update,Expression.eval,h l,h r] using regs d
    · simpa [Assignment.update,Expression.eval,Function.update_of_ne eq,eq,h i] using regs i

namespace Circuit

def result (v : ℕ → ℕ) : List Assignment → (ℕ → ℕ)
  | [] => v
  | a::as => result (a.update v) as

def steps (v : ℕ → ℕ) : List Assignment → ℕ
  | [] => 0
  | a::as => a.rhs.steps v + steps (a.update v) as

def width (v : ℕ → ℕ) : List Assignment → ℕ
  | [] => 0
  | a::as => max (a.rhs.width v) (width (a.update v) as)

def multiplicity (v : ℕ → ℕ) : List Assignment → ℕ
  | [] => 0
  | a::as => a.rhs.multiplicity v + multiplicity (a.update v) as

theorem steps_le (as : List Assignment) (v : ℕ → ℕ) (b : ℕ) (h : width v as ≤ b) :
    steps v as ≤ multiplicity v as*(b*(5*b+9)+15) := by
  induction as generalizing v with
  | nil => simp [steps,multiplicity]
  | cons a as ih =>
    obtain ⟨first,rest⟩ := max_le_iff.mp h
    simpa only [steps,multiplicity,Nat.add_mul] using Nat.add_le_add (a.rhs.steps_le v b first) (ih (a.update v) rest)

theorem result_untouched (as : List Assignment) (v : ℕ → ℕ) (i : ℕ) (free : ∀ a ∈ as, i ≠ a.dst) :
    result v as i = v i := by
  induction as generalizing v with
  | nil => rfl
  | cons a as ih =>
    rw [result,ih (a.update v) (fun x hx => free x (List.mem_cons_of_mem _ hx))]
    exact Function.update_of_ne (free a (by simp)) _ _

/-- A finite arithmetic circuit is a fixed program on the public RAM. Its bound is a
sum of the individual operation costs, and its width accounts for their intermediates. -/
theorem exec {τ : TargetedSamplers.Tapes} {b : ℕ} (as : List Assignment) (v : ℕ → ℕ) (s : Store)
    (repr : Represents s v) (fit : s.Fits b) (hb : 2 ≤ b) (bound : width v as ≤ b) :
    ∃ t j, Exec τ (fun u => u.Fits b) (cmd as) s t j ∧ j ≤ steps v as ∧ Represents t (result v as) ∧ t.out = s.out := by
  induction as generalizing v s with
  | nil => exact ⟨s,0,.skip s,le_rfl,repr,rfl⟩
  | cons a as ih =>
    obtain ⟨first,later⟩ := max_le_iff.mp bound
    obtain ⟨u,i,run,hi,rep,out⟩ := a.exec (τ := τ) v s repr fit hb first
    obtain ⟨t,j,tail,hj,final,ret⟩ := ih (a.update v) u rep (run.post fit) later
    exact ⟨t,_,run.seq tail,Nat.add_le_add hi hj,final,ret.trans out⟩

end Circuit

end TargetedSamplers.Structured.Word

end LogCostRAMArithmeticCircuit

section LogCostRAMBankCircuit

namespace TargetedSamplers.Structured.Word.Circuit

def atBank (bank : ℕ) (v : ℕ → ℕ) := fun i => v (bank+i)

private theorem eval_move (bank : ℕ) (v : ℕ → ℕ) (e : Expression) :
    (moveExpr bank e).eval v=e.eval (atBank bank v) := by cases e <;> rfl

private theorem width_move (bank : ℕ) (v : ℕ → ℕ) (e : Expression) :
    (moveExpr bank e).width v=e.width (atBank bank v) := by cases e <;> rfl

private theorem update_move (bank : ℕ) (v : ℕ → ℕ) (a : Assignment) :
    atBank bank ((moveAssignment bank a).update v)=a.update (atBank bank v) := by
  funext i
  by_cases eq : i=a.dst
  · subst i;simp [atBank,Assignment.update,moveAssignment,eval_move]
  · simp [atBank,Assignment.update,moveAssignment,eq,show bank+i ≠ bank+a.dst by omega]

private theorem circuit_move (bank : ℕ) (v : ℕ → ℕ) (as : List Assignment) :
    atBank bank (result v (as.map (moveAssignment bank)))=result (atBank bank v) as ∧
    width v (as.map (moveAssignment bank))=width (atBank bank v) as ∧
    multiplicity v (as.map (moveAssignment bank))=multiplicity (atBank bank v) as := by
  induction as generalizing v with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons a as ih =>
    have more := ih ((moveAssignment bank a).update v)
    rw [update_move] at more
    have weights : (moveExpr bank a.rhs).multiplicity v=a.rhs.multiplicity (atBank bank v) := by
      cases a.rhs with
      | arithmetic op l r => cases op <;> rfl
      | _ => rfl
    simp only [List.map_cons,result,width,multiplicity,moveAssignment,width_move,weights] at *
    exact ⟨more.1,congrArg (max _) more.2.1,congrArg (_+·) more.2.2⟩

/-- Place all user registers of a verified arithmetic circuit into a protected
caller bank. The machine and cost bounds stay identical under this relocation. -/
theorem bank_exec {τ : Tapes} {b : ℕ} (bank : ℕ) (as : List Assignment) (s : Store)
    (fit : s.Fits b) (hb : 2 ≤ b) :
    let v := fun i => s.mem (cell (bank+i))
    width v as ≤ b →
    ∃ t j, Exec τ (fun u => u.Fits b) (bankCmd bank as) s t j ∧ j ≤ multiplicity v as*(b*(5*b+9)+15) ∧
      (∀ i, t.mem (cell (bank+i))=result v as i) ∧ t.out=s.out ∧
      ∀ a, 14 ≤ a → (∀ h∈as, a ≠ cell (bank+h.dst)) → t.mem a=s.mem a := by
  intro v enough
  let regs := fun i => s.mem (cell i)
  let code := as.map (moveAssignment bank)
  have map := circuit_move bank regs as
  have room : width regs code ≤ b := map.2.1.trans_le enough
  obtain ⟨t,j,run,used,rep,out⟩ := exec (τ := τ) code regs s (fun _ => rfl) fit hb room
  have work := used.trans (steps_le code regs b room)
  rw [map.2.2] at work
  refine ⟨t,j,run,work,fun i => (rep _).trans (congrFun map.1 i),out,?_⟩
  intro a ha free
  have ix : cell (a-14)=a := by dsimp [cell];omega
  rw [← ix,rep]
  apply result_untouched
  intro h hh
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hh
  have apart := free x hx
  dsimp [moveAssignment,cell] at *
  omega

end TargetedSamplers.Structured.Word.Circuit

end LogCostRAMBankCircuit

section HamiltonianRequestRegisters

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers.Structured

theorem RequestHeader.transport {base n h source sink graph width : ℕ} {u v : Store}
    (o : RequestHeader base n h source sink graph width u)
    (save : ∀ a, base ≤ a ∧ a < base+5 ∨ a=base+9 → v.mem a=u.mem a) :
    RequestHeader base n h source sink graph width v :=
  ⟨(save _ (by omega)).trans o.vertices,(save _ (by omega)).trans o.weights,(save _ (by omega)).trans o.src,
    (save _ (by omega)).trans o.dst,(save _ (by omega)).trans o.adjacency,(save _ (by omega)).trans o.radix⟩

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRequestRegisters

section LogCostRAMCoinBlock

namespace TargetedSamplers.Structured.CoinRead

/-- Read little-endian bits. Missing cells of a short tape have value zero. -/
def value (coins : List Bool) (base : ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => value coins base k + (coins[base+k]?.getD false).toNat * 2^k

private theorem digit_exec {τ : Tapes} {width : ℕ} (r : Fin 5 ↪ ℕ) (s : Store) (p v : ℕ)
    (pos : s.mem (r 0) = p+1) (one : s.mem (r 2) = 1) (acc : s.mem (r 4) = v)
    (fit : s.Fits width) (hb : 2 ≤ width) (w : (v+v+1).size ≤ width) :
    let t := ((digit r).run τ s).last
    ∃ j ≤ 7, Exec τ (fun u => u.Fits width) (digit r).cmd s t j ∧
      t.mem (r 0) = p ∧ t.mem (r 4) = v+v+(τ.coins[p]?.getD false).toNat ∧ t.out = s.out ∧
      ∀ a, a ≠ r 0 → a ≠ r 3 → a ≠ r 4 → t.mem a = s.mem a := by
  have eq (i j : Fin 5) : r i = r j ↔ i=j := r.injective.eq_iff
  have wp := (Nat.size_le_size (Nat.le_succ p)).trans (pos ▸ fit (r 0))
  have wv := (Nat.size_le_size (Nat.le_succ (v+v))).trans w
  have two : (2:ℕ).size ≤ width := hb
  have unit : 1 ≤ width := by omega
  have ww : ((digit r).run τ s).writeWidth ≤ width := by
    cases h : τ.coins[p]? with
    | none => simp [digit,sequence,Fragment.run,Op.eval,Op.written,Store.write,eq,pos,one,acc,h,bitVal,two,unit,wp,wv]
    | some x => cases x <;> simp [digit,sequence,Fragment.run,Op.eval,Op.written,Store.write,eq,pos,one,acc,h,bitVal,two,unit,wp,wv,w]
  refine ⟨_,?_,(digit r).exec τ s width fit ww,?_,?_,?_,?_⟩
  all_goals first
    | (intro a h₀ h₃ h₄
       cases h : τ.coins[p]? with
       | none => simp [digit,sequence,Fragment.run,Op.eval,Store.write,eq,pos,one,acc,h,bitVal,h₀,h₃,h₄]
       | some x => cases x <;> simp [digit,sequence,Fragment.run,Op.eval,Store.write,eq,pos,one,acc,h,bitVal,h₀,h₃,h₄])
    | (cases h : τ.coins[p]? with
       | none => simp [digit,sequence,Fragment.run,Op.eval,Store.write,eq,pos,one,acc,h,bitVal]
       | some x => cases x <;> simp [digit,sequence,Fragment.run,Op.eval,Store.write,eq,pos,one,acc,h,bitVal])

/-- A fixed bounded loop reads a coin block at an arbitrary address. No length query is used. -/
theorem loop_exec {τ : Tapes} {width : ℕ} (r : Fin 5 ↪ ℕ) (s : Store) (base k v : ℕ)
    (pos : s.mem (r 0) = base+k) (stop : s.mem (r 1) = base) (one : s.mem (r 2) = 1)
    (acc : s.mem (r 4) = v) (fit : s.Fits width) (hb : 2 ≤ width) (room : ((v+1)*2^k).size ≤ width) :
    ∃ t j, Exec τ (fun u => u.Fits width) (loop r) s t j ∧ j ≤ 9*k+1 ∧
      t.mem (r 0) = base ∧ t.mem (r 4) = v*2^k+value τ.coins base k ∧ t.out = s.out ∧
      ∀ a, a ≠ r 0 → a ≠ r 3 → a ≠ r 4 → t.mem a = s.mem a := by
  induction k generalizing s v with
  | zero =>
    exact ⟨s,1,.done (by simp [pos,stop]),by simp,by simpa using pos,by simpa [value] using acc,rfl,fun _ _ _ _ => rfl⟩
  | succ k ih =>
    have ne {i j : Fin 5} (h : i ≠ j) := r.injective.ne h
    let x := (τ.coins[base+k]?.getD false).toNat
    have bit : x ≤ 1 := Bool.toNat_le _
    have lower : v+v+1 ≤ (v+1)*2^(k+1) := by
      rw [pow_succ]
      have m := Nat.mul_le_mul_left (v+1) (Nat.one_le_two_pow (n := k))
      nlinarith only [m]
    obtain ⟨j,hj,first,pp,vv,out,frame⟩ := digit_exec (τ := τ) r s (base+k) v (by simpa [Nat.add_assoc] using pos)
      one acc fit hb ((Nat.size_le_size lower).trans room)
    let u := ((digit r).run τ s).last
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

end TargetedSamplers.Structured.CoinRead

end LogCostRAMCoinBlock

section RAMRankedCoins

namespace FiniteSampling

open TargetedSamplers TargetedSamplers.Structured

open scoped BigOperators

private theorem binaryRank_val (k : ℕ) (bits : Fin k → Bool) :
    (binaryRank k bits).val = ∑ i, (bits i).toNat*2^i.val := by
  change (finFunctionFinEquiv (fun i => finTwoEquiv.symm (bits i))).val = _
  rw [finFunctionFinEquiv_apply]
  apply Finset.sum_congr rfl
  intro i _
  have h (x : Bool) : (finTwoEquiv.symm x).val = x.toNat := by cases x <;> rfl
  rw [h]

theorem coinValue_eq_binaryRank (coins : List Bool) (base k : ℕ) :
    CoinRead.value coins base k = (binaryRank k fun i => coins[base+i.val]?.getD false).val := by
  rw [binaryRank_val]
  induction k with
  | zero => simp [CoinRead.value]
  | succ k ih => simp only [CoinRead.value,Fin.sum_univ_castSucc,Fin.val_castSucc,Fin.val_last,ih]

/-- The RAM returns the rank used by the sampling proof, for every finite tape. -/
theorem readRank_exec {τ : Tapes} {width : ℕ} (r : Fin 5 ↪ ℕ) (s : Store) (base k : ℕ)
    (pos : s.mem (r 0) = base+k) (stop : s.mem (r 1) = base) (one : s.mem (r 2) = 1)
    (fit : s.Fits width) (hw : 2 ≤ width) (room : k+1 ≤ width) :
    ∃ t j, Exec τ (fun u => u.Fits width) (readRank r) s t j ∧ j ≤ 9*k+2 ∧
      t.mem (r 0) = base ∧ t.mem (r 4) = (binaryRank k fun i => τ.coins[base+i.val]?.getD false).val ∧
      t.out = s.out ∧ ∀ a, a ≠ r 0 → a ≠ r 3 → a ≠ r 4 → t.mem a = s.mem a := by
  let u := s.write (r 4) 0
  have f : u.Fits width := Store.write_fits fit _ (by simp)
  have init : Exec τ (fun v => v.Fits width) (.op (.const (r 4) 0)) s u 1 := .op _ _ f
  have kept (i : Fin 5) (hi : i ≠ 4) : u.mem (r i) = s.mem (r i) := by simp [u,Store.write,r.injective.ne hi]
  obtain ⟨t,j,run,work,cursor,val,out,frame⟩ := CoinRead.loop_exec (τ := τ) r u base k 0
    ((kept 0 (by decide)).trans pos) ((kept 1 (by decide)).trans stop) ((kept 2 (by decide)).trans one)
    (by simp [u,Store.write]) f hw (by simpa only [Nat.zero_add,Nat.one_mul,Nat.size_pow] using room)
  exact ⟨t,_,init.seq run,by omega,cursor,by simpa [coinValue_eq_binaryRank] using val,out,
    fun a h₀ h₃ h₄ => (frame a h₀ h₃ h₄).trans (by simp [u,Store.write,h₄])⟩

end FiniteSampling

end RAMRankedCoins

section HamiltonianRAMTrialRead

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word FiniteSampling

theorem cell_add (bank i : ℕ) : cell (bank+i)=cell bank+i := by simp only [cell,Nat.add_assoc]

theorem saveWord_exec {τ : Tapes} {b : ℕ} (base dst src : ℕ) (u : Store)
    (zero : u.mem (base+23)=0) (fit : u.Fits b) :
    Exec τ (fun v => v.Fits b) (saveWord base dst src) u (u.write (base+dst) (u.mem src)) 1 := by
  have val : (Op.add (base+dst) src (base+23)).eval τ u=u.write (base+dst) (u.mem src) := by
    simp [Op.eval,zero]
  simpa only [saveWord,val] using Exec.op (τ := τ) (inv := fun v => v.Fits b) u (.add (base+dst) src (base+23))
    (val ▸ Store.write_fits fit (base+dst) (fit src))

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMTrialRead

section LogCostRAMCeilLog

namespace TargetedSamplers.Structured

private theorem ceilLogLoop_exec {τ : Tapes} {b : ℕ} (r : Fin 4 ↪ ℕ) (x i left : ℕ) (s : Store)
    (atEnd : i+left = Nat.clog 2 x) (input : s.mem (r 0) = x) (place : s.mem (r 1) = 2^i)
    (expo : s.mem (r 2) = i) (one : s.mem (r 3) = 1) (fit : s.Fits b) (room : Nat.clog 2 x + 1 ≤ b) :
    ∃ t, Exec τ (fun st => st.Fits b) (ceilLogLoop r) s t (4*left+1) ∧
      t.mem (r 1) = 2^(Nat.clog 2 x) ∧ t.mem (r 2) = Nat.clog 2 x ∧ t.out = s.out ∧
      ∀ a, a ≠ r 1 → a ≠ r 2 → t.mem a = s.mem a := by
  have ne {j l : Fin 4} (h : j ≠ l) := r.injective.ne h
  induction left generalizing i s with
  | zero =>
    have eq : i = Nat.clog 2 x := by omega
    exact ⟨s,.done (by rw [input,place,eq]; exact Nat.le_pow_clog (by decide) _),eq ▸ place,expo.trans eq,rfl,fun _ _ _ => rfl⟩
  | succ left ih =>
    have lt : i < Nat.clog 2 x := by omega
    have hval : 2^i+2^i = 2^(i+1) := by rw [pow_succ]; omega
    let v := s.write (r 1) (2^(i+1))
    let z := v.write (r 2) (i+1)
    have e₁ : (Op.add (r 1) (r 1) (r 1)).eval τ s = v := by simp [Op.eval,v,place,hval]
    have w₁ : (2^(i+1)).size ≤ b := by rw [Nat.size_pow]; omega
    have f₁ : v.Fits b := Store.write_fits fit _ w₁
    have op₁ : Exec τ (fun st => st.Fits b) (.op (.add (r 1) (r 1) (r 1))) s v 1 := by
      simpa only [e₁] using (Exec.op (τ := τ) (inv := fun st => st.Fits b) s (.add (r 1) (r 1) (r 1)) (by rw [e₁]; exact f₁))
    have e₂ : (Op.add (r 2) (r 2) (r 3)).eval τ v = z := by
      simp [v,z,Op.eval,Store.write,ne (by decide : (2:Fin 4) ≠ 1),ne (by decide : (3:Fin 4) ≠ 1),expo,one]
    have w₂ : (i+1).size ≤ b := (Nat.size_le.mpr (i+1).lt_two_pow_self).trans (by omega)
    have f₂ : z.Fits b := Store.write_fits f₁ _ w₂
    have op₂ : Exec τ (fun st => st.Fits b) (.op (.add (r 2) (r 2) (r 3))) v z 1 := by
      simpa only [e₂] using (Exec.op (τ := τ) (inv := fun st => st.Fits b) v (.add (r 2) (r 2) (r 3)) (by rw [e₂]; exact f₂))
    have frame (a : ℕ) (h₁ : a ≠ r 1) (h₂ : a ≠ r 2) : z.mem a = s.mem a := by simp [z,v,Store.write,h₁,h₂]
    obtain ⟨t,run,pow',log',out,kept⟩ := ih (i+1) z (by omega)
      ((frame _ (ne (by decide)) (ne (by decide))).trans input)
      (by simp [z,v,Store.write,ne (by decide : (1:Fin 4) ≠ 2)]) (by simp [z,Store.write])
      ((frame _ (ne (by decide)) (ne (by decide))).trans one) f₂
    have step := Exec.again (a := r 0) (b := r 1)
      (by rw [input,place]; exact Nat.not_le_of_gt (Nat.pow_lt_of_lt_clog lt)) (op₁.seq op₂) run
    refine ⟨t,?_,pow',log',out,fun a h₁ h₂ => (kept a h₁ h₂).trans (frame a h₁ h₂)⟩
    rw [show 4*(left+1)+1 = 1+(1+1)+1+(4*left+1) by omega]
    exact step

/-- Compute the exact width of a fair-bit block, even for cardinality zero or one. -/
theorem ceilLog_exec {τ : Tapes} {b : ℕ} (r : Fin 4 ↪ ℕ) (x : ℕ) (s : Store)
    (input : s.mem (r 0) = x) (fit : s.Fits b) (room : Nat.clog 2 x+1 ≤ b) :
    ∃ t, Exec τ (fun st => st.Fits b) (ceilLog r) s t (4*Nat.clog 2 x+4) ∧
      t.mem (r 1) = 2^(Nat.clog 2 x) ∧ t.mem (r 2) = Nat.clog 2 x ∧ t.out = s.out ∧
      ∀ a, a ≠ r 1 → a ≠ r 2 → a ≠ r 3 → t.mem a = s.mem a := by
  let f := Structured.sequence [.op (.const (r 1) 1),.op (.const (r 2) 0),.op (.const (r 3) 1)]
  let t := (f.run τ s).last
  have eq (j l : Fin 4) : r j = r l ↔ j=l := r.injective.eq_iff
  have w : (f.run τ s).writeWidth ≤ b := by
    have hb : 1 ≤ b := by omega
    simp [f,Structured.sequence,Fragment.run,Op.written,hb]
  obtain ⟨z,run,pow',log',out,frame⟩ := ceilLogLoop_exec (τ := τ) r x 0 (Nat.clog 2 x) t (by omega)
    (by simp [t,f,Structured.sequence,Fragment.run,Op.eval,Store.write,eq,input])
    (by simp [t,f,Structured.sequence,Fragment.run,Op.eval,Store.write,eq])
    (by simp [t,f,Structured.sequence,Fragment.run,Op.eval,Store.write,eq])
    (by simp [t,f,Structured.sequence,Fragment.run,Op.eval,Store.write,eq]) ((f.exec τ s b fit w).post fit) room
  have init : Exec τ (fun st => st.Fits b) f.cmd s t 3 := f.exec τ s b fit w
  have seq := init.seq run
  refine ⟨z,?_,pow',log',out,?_⟩
  · rw [show 4*Nat.clog 2 x+4 = 3+(4*Nat.clog 2 x+1) by omega]
    exact seq
  intro a h₁ h₂ h₃
  exact (frame a h₁ h₂).trans (by simp [t,f,Structured.sequence,Fragment.run,Op.eval,Store.write,h₁,h₂,h₃])

end TargetedSamplers.Structured

end LogCostRAMCeilLog

section HamiltonianRAMSharedRead

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word FiniteSampling

theorem sharedRead_exec {τ : Tapes} {b : ℕ} (a maskLen card : ℕ) (u : Store)
    (maskAt : u.mem (a+13)=maskLen) (cardAt : u.mem (a+14)=card) (zero : u.mem (a+23)=0)
    (one : u.mem (a+24)=1) (fit : u.Fits b) (hb : 2 ≤ b) (maskW : maskLen+1 ≤ b) (trialW : Nat.clog 2 card+1 ≤ b) :
    ∃ z j, Exec τ (fun v => v.Fits b) (sharedRead a) u z j ∧ j ≤ 4*Nat.clog 2 card+9*maskLen+7 ∧
      z.mem (a+5)=(binaryRank maskLen (fun i => τ.coins[i.val]?.getD false)).val ∧
      z.mem (a+15)=Nat.clog 2 card ∧ z.out=u.out ∧
      ∀ x, x ≠ a+5 → x ≠ a+15 → x ≠ a+30 → x ≠ a+31 → x ≠ a+33 → z.mem x=u.mem x := by
  obtain ⟨v,lg,_,logarithm,ret,frame⟩ := ceilLog_exec (τ := τ) (logRegisters a) card u cardAt fit trialW
  change v.mem (a+15)=Nat.clog 2 card at logarithm
  change ∀ x, x ≠ a+31 → x ≠ a+15 → x ≠ a+33 → v.mem x=u.mem x at frame
  have vz := (frame (a+23) (by omega) (by omega) (by omega)).trans zero
  have len := (frame (a+13) (by omega) (by omega) (by omega)).trans maskAt
  let y := v.write (a+30) (v.mem (a+13))
  have copy := saveWord_exec (τ := τ) a 30 (a+13) v vz (lg.post fit)
  have fixed (x : ℕ) (hx : x ≠ a+30) : y.mem x=v.mem x := by simp [y,Store.write,hx]
  have head : y.mem (a+30)=0+maskLen := by simp [y,Store.write,len]
  have base : y.mem (a+23)=0 := (fixed _ (by omega)).trans vz
  have unit : y.mem (a+24)=1 := (fixed _ (by omega)).trans ((frame _ (by omega) (by omega) (by omega)).trans one)
  obtain ⟨z,j,scan,cost,_,rank,out,keep⟩ := readRank_exec (τ := τ) (maskRegisters a) y 0 maskLen
    head base unit (copy.post (lg.post fit)) hb maskW
  change ∀ x, x ≠ a+30 → x ≠ a+33 → x ≠ a+5 → z.mem x=y.mem x at keep
  change z.mem (a+5)=(binaryRank maskLen fun i => τ.coins[0+i.val]?.getD false).val at rank
  refine ⟨z,_,lg.seq (copy.seq scan),by omega,by simpa only [Nat.zero_add] using rank,
    (keep _ (by omega) (by omega) (by omega)).trans ((fixed _ (by omega)).trans logarithm),out.trans ret,?_⟩
  intro x h5 h15 h30 h31 h33
  exact (keep _ h30 h33 h5).trans ((fixed _ h30).trans (frame _ h31 h15 h33))

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMSharedRead

section HamiltonianRAMSharedPrefix

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word FiniteSampling

/-- The mask length and the nonzero tuple cardinality are both queried from the packed graph.
The resulting shared mask and bit-block width are retained in the caller's bank. -/
theorem sharedPrefix_exec {τ : Tapes} {b : ℕ} (bank floor maskLen card cost : ℕ) (kernel : Cmd)
    (n h src dst graph width : ℕ) (u : Store) (high : floor ≤ cell bank)
    (header : RequestHeader (cell bank) n h src dst graph width u) (args : RequestArgs (cell bank) 0 0 0 0 u)
    (zero : u.mem (cell bank+23)=0) (one : u.mem (cell bank+24)=1) (fit : u.Fits b) (hb : 2 ≤ b)
    (mw : maskLen+1 ≤ b) (cw : Nat.clog 2 card+1 ≤ b)
    (call : ∀ (mode : Fin 2) (v : Store), RequestHeader (cell bank) n h src dst graph width v →
      RequestArgs (cell bank) 0 0 0 mode.val v → v.Fits b →
      ∃ y j, Exec τ (fun s => s.Fits b) kernel v y j ∧ j ≤ cost ∧ y.mem 0=(if mode.val=0 then maskLen else card) ∧
        y.out=v.out ∧ ∀ x ≥ floor,y.mem x=v.mem x) :
    let a := cell bank
    ∃ z j, Exec τ (fun s => s.Fits b) (sharedPrefix bank kernel) u z j ∧
      j ≤ 2*cost+4*Nat.clog 2 card+9*maskLen+10 ∧
      z.mem (a+5)=(binaryRank maskLen (fun i => τ.coins[i.val]?.getD false)).val ∧ z.mem (a+13)=maskLen ∧
      z.mem (a+14)=card ∧ z.mem (a+15)=Nat.clog 2 card ∧ z.out=u.out ∧
      ∀ x, floor ≤ x → x ≠ a+5 → x ≠ a+8 → x ≠ a+13 → x ≠ a+14 → x ≠ a+15 → x ≠ a+30 → x ≠ a+31 → x ≠ a+33 → z.mem x=u.mem x := by
  intro a
  obtain ⟨v,j₀,first,w₀,answer₀,ret₀,frame₀⟩ := call 0 u header args fit
  have ans₀ : v.mem 0=maskLen := answer₀
  have vzero := (frame₀ (a+23) (by omega)).trans zero
  let y := v.write (a+13) (v.mem 0)
  have save₀ := saveWord_exec (τ := τ) a 13 0 v vzero (first.post fit)
  let z := y.write (a+8) 1
  have fz : z.Fits b := Store.write_fits (save₀.post (first.post fit)) _ ((by decide : (1:ℕ).size ≤ 2).trans hb)
  have mode : Exec τ (fun s => s.Fits b) (.op (.const (a+8) 1)) y z 1 := .op _ _ fz
  have hold (x : ℕ) (hx : floor ≤ x) (h₈ : x ≠ a+8) (h₁₃ : x ≠ a+13) : z.mem x=u.mem x := by
    simpa [z,y,Store.write,h₈,h₁₃] using frame₀ x hx
  have hz := header.transport (v := z) (fun x hx => hold x (by omega) (by omega) (by omega))
  have ar : RequestArgs a 0 0 0 1 z := ⟨(hold _ (by omega) (by omega) (by omega)).trans args.maskWord,
    (hold _ (by omega) (by omega) (by omega)).trans args.keyWord,
    (hold _ (by omega) (by omega) (by omega)).trans args.indexWord,by simp [z,Store.write]⟩
  obtain ⟨t,j₁,second,w₁,answer₁,ret₁,frame₁⟩ := call 1 z hz ar fz
  have ans₁ : t.mem 0=card := answer₁
  have holdT (x : ℕ) (hx : floor ≤ x) (h₈ : x ≠ a+8) (h₁₃ : x ≠ a+13) :=
    (frame₁ x hx).trans (hold x hx h₈ h₁₃)
  have zt := (holdT (a+23) (by omega) (by omega) (by omega)).trans zero
  have save₁ := saveWord_exec (τ := τ) a 14 0 t zt (second.post fz)
  let y₁ := t.write (a+14) (t.mem 0)
  have hold₁ (x : ℕ) (h₁₄ : x ≠ a+14) : y₁.mem x=t.mem x := by simp [y₁,Store.write,h₁₄]
  have mask₁ : y₁.mem (a+13)=maskLen := by
    rw [hold₁ _ (by omega),frame₁ _ (by omega)]
    simp [z,y,Store.write,ans₀]
  have card₁ : y₁.mem (a+14)=card := by simp [y₁,Store.write,ans₁]
  obtain ⟨z₁,j,scan,w,mask,logarithm,ret,keep⟩ := sharedRead_exec (τ := τ) a maskLen card y₁ mask₁ card₁
    ((hold₁ _ (by omega)).trans zt) ((hold₁ _ (by omega)).trans ((holdT _ (by omega) (by omega) (by omega)).trans one))
    (save₁.post (second.post fz)) hb mw cw
  refine ⟨z₁,_,first.seq (save₀.seq (mode.seq (second.seq (save₁.seq scan)))),by omega,mask,
    (keep _ (by omega) (by omega) (by omega) (by omega) (by omega)).trans mask₁,
    (keep _ (by omega) (by omega) (by omega) (by omega) (by omega)).trans card₁,
    logarithm,ret.trans (ret₁.trans ret₀),?_⟩
  intro x low h₅ h₈ h₁₃ h₁₄ h₁₅ h₃₀ h₃₁ h₃₃
  exact (keep x h₅ h₁₅ h₃₀ h₃₁ h₃₃).trans ((hold₁ x h₁₄).trans (holdT x low h₈ h₁₃))

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMSharedPrefix

section HamiltonianRAMSolverLayout

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers.Structured TargetedSamplers.Structured.Word

abbrev solverRegister (i : ℕ) : Prop := i=16 ∨ i=30 ∨ i=31 ∨ i=40 ∨ i=41 ∨ 50 ≤ i ∧ i ≤ 56

theorem solverLayout_writes (bank c d : ℕ) (h : Assignment) (hh : h∈initSolverLayout bank c d) :
    solverRegister h.dst := by
  have writes : (initSolverLayout bank c d).all (fun v => decide (solverRegister v.dst))=true := rfl
  exact of_decide_eq_true (List.all_eq_true.mp writes h hh)

theorem initSolverLayout_values (bank c d : ℕ) (v : ℕ → ℕ) (z : v 23=0) (one : v 24=1) (two : v 25=2) :
    let t := Circuit.result v (initSolverLayout bank c d)
    let q := v 12
    t 40=solverArea bank q ∧ t 41=q ∧ t 50=solverArea bank q ∧ t 51=q ∧
      t 52=rowArea bank ∧ t 53=pinArea bank q ∧ t 54=0 ∧ t 55=1 ∧ t 56=2 ∧
      t 16=seenArea bank q c d (v 26) := by
  simp [initSolverLayout,Circuit.result,Assignment.update,Expression.eval,Arithmetic.value,Function.update_apply,
    z,one,two,solverArea,pinArea,seenArea]

theorem initSolverLayout_work (bank c d : ℕ) (v : ℕ → ℕ) :
    Circuit.multiplicity v (initSolverLayout bank c d)=d+(initSolverLayout bank c d).length := by
  simp [initSolverLayout,Circuit.multiplicity,Expression.multiplicity,Assignment.update,Expression.eval,
    Arithmetic.value,Function.update_apply,Nat.add_assoc] <;> omega

set_option maxHeartbeats 1600000 in
theorem initSolverLayout_width (bank c d : ℕ) (v : ℕ → ℕ) (z : v 23=0) (one : v 24=1) (two : v 25=2) :
    Circuit.width v (initSolverLayout bank c d) ≤ solverRoom bank (v 12) c d (v 26) := by
  let R := solverRoom bank (v 12) c d (v 26)
  have small (x : ℕ) (hx : x ≤ R) : x.size ≤ R := (Nat.size_le.mpr x.lt_two_pow_self).trans hx
  change _ ≤ R
  simp [initSolverLayout,Circuit.width,Assignment.update,Expression.eval,Expression.width,Arithmetic.value,
    Function.update_apply,z,one,two,max_le_iff]
  dsimp [R,solverRoom,seenArea,solverArea,pinArea] at small ⊢
  repeat' apply And.intro
  all_goals first | apply small <;> omega | omega

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMSolverLayout

section LogCostRAMMarkWord

namespace TargetedSamplers.Structured.BinaryStack

theorem tracksWords_empty (q base : ℕ) (s : Store) (zero : ∀ a ≥ base, s.mem a=0) :
    tracksWords q base ∅ s := by
  intro xs len
  simpa using zero (base+packed xs) (by omega)

end TargetedSamplers.Structured.BinaryStack

end LogCostRAMMarkWord

section HamiltonianRAMVisitWord

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.BinaryStack

open scoped BigOperators

@[simp] theorem parityWord_empty (f : List Bool → ZMod 2) : parityWord f ∅=0 := by simp [parityWord]

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMVisitWord

section HamiltonianRAMTrialProblem

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word

open TargetedSamplers.Structured.BinaryStack AffinePrefixEnumeration EditGV897.Main FiniteSampling Multidigraph

namespace TrialParameters

abbrev layout (P : TrialParameters) := TrialState P.bank P.vertices P.weights P.source P.sink P.graph P.fieldWidth
  P.mask P.maskLength P.card P.dim P.trials P.target P.seenBase

end TrialParameters

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMTrialProblem

section
open DirectedHamiltonicity DirectedHamiltonicity.Main DirectedHamiltonicity.Main.InputRAM
open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word
open TargetedSamplers.Structured.BinaryStack FiniteSampling
open DirectedHamiltonicity DirectedHamiltonicity.Main DirectedHamiltonicity.Main.InputRAM DirectedHamiltonicity.Main.InputRAM.TrialParameters

theorem solution {τ : Tapes} {b floor cost : ℕ} (P : TrialParameters) (c d gridEnd : ℕ)
    (kernel : Cmd) (f : List Bool → ZMod 2) (u : Store)
    (beginAt : PreparedRequest P.a P.vertices P.weights P.source P.sink P.graph P.trials P.target gridEnd u)
    (width : P.fieldWidth=argumentWidth P.vertices P.weights) (dimension : P.dim=P.vertices-2)
    (baseEq : P.seenBase=seenArea P.bank P.dim c d gridEnd)
    (prefixEq : P.mask=(binaryRank P.maskLength fun i => τ.coins[i.val]?.getD false).val)
    (empty : ∀ x, P.a+68 < x → gridEnd ≤ x → u.mem x=0) (floorLow : floor ≤ P.a)
    (room : solverRoom P.bank P.dim c d gridEnd ≤ b) (hb : 2 ≤ b)
    (mw : P.maskLength+1 ≤ b) (cw : Nat.clog 2 P.card+1 ≤ b) (fit : u.Fits b)
    (query : ∀ (mode : Fin 2) (v : Store), P.header v → RequestArgs P.a 0 0 0 mode.val v → v.Fits b →
      ∃ t k, Exec τ (fun s => s.Fits b) kernel v t k ∧ k ≤ cost ∧ t.mem 0=(if mode.val=0 then P.maskLength else P.card) ∧
        t.out=v.out ∧ ∀ x ≥ floor,t.mem x=v.mem x) :
    ∃ z j, Exec τ (fun s => s.Fits b) (bootstrap P.bank c d kernel) u z j ∧
      j ≤ (d+(initSolverLayout P.bank c d).length)*(b*(5*b+9)+15)+2*cost+4*Nat.clog 2 P.card+9*P.maskLength+10 ∧
      P.invariant f ∅ z ∧ z.mem (P.a+65)=0 ∧ z.mem (P.a+68)=0 ∧ z.out=u.out := by
  let v := fun i => u.mem (cell (P.bank+i))
  have old (i : ℕ) : v i=u.mem (P.a+i) := by simp [v,a,cell,Nat.add_assoc]
  have zero := (old 23).trans beginAt.zero
  have one := (old 24).trans beginAt.one
  have two := (old 25).trans beginAt.two
  have dim := (old 12).trans (beginAt.dim.trans dimension.symm)
  have last := (old 26).trans beginAt.grid
  have space := initSolverLayout_width P.bank c d v zero one two
  rw [dim,last] at space
  obtain ⟨y,j,setup,wj,regs,out₀,unmodified⟩ := Circuit.bank_exec (τ := τ) P.bank (initSolverLayout P.bank c d) u fit hb (space.trans room)
  let t := Circuit.result v (initSolverLayout P.bank c d)
  have reg (i : ℕ) : y.mem (P.a+i)=t i := by rw [show P.a+i=cell (P.bank+i) from (cell_add ..).symm];exact regs i
  have kept (i : ℕ) (apart : ¬solverRegister i) : y.mem (P.a+i)=u.mem (P.a+i) := by
    rw [reg]
    exact (Circuit.result_untouched (initSolverLayout P.bank c d) v i (fun h hh e => apart (e.symm ▸ solverLayout_writes P.bank c d h hh))).trans (old i)
  have hv := initSolverLayout_values P.bank c d v zero one two
  change t 40=_ ∧ t 41=_ ∧ t 50=_ ∧ t 51=_ ∧ t 52=_ ∧ t 53=_ ∧ t 54=_ ∧ t 55=_ ∧ t 56=_ ∧ t 16=_ at hv
  simp only [← reg,dim,last,← baseEq] at hv
  obtain ⟨base₀,dim₀,pin₀,rows₀,row₀,after₀,pause₀,unit₀,two₀,seen₀⟩ := hv
  have header₀ : P.header u := by rw [TrialParameters.header,width];exact beginAt.header
  have headerY : P.header y := header₀.transport (fun x hx => by
    have eq : P.a+(x-P.a)=x := by omega
    simpa only [eq] using kept (x-P.a) (by unfold solverRegister;omega))
  have argsY : RequestArgs P.a 0 0 0 0 y := ⟨(kept 5 (by decide)).trans beginAt.args.maskWord,
    (kept 6 (by decide)).trans beginAt.args.keyWord,(kept 7 (by decide)).trans beginAt.args.indexWord,
    (kept 8 (by decide)).trans beginAt.args.kindWord⟩
  obtain ⟨z,k,shared,wk,mask,len,card,logarithm,out,frame⟩ := sharedPrefix_exec (τ := τ) P.bank floor P.maskLength P.card cost
    kernel P.vertices P.weights P.source P.sink P.graph P.fieldWidth y floorLow headerY argsY
    ((kept 23 (by decide)).trans beginAt.zero) ((kept 24 (by decide)).trans beginAt.one) (setup.post fit) hb mw cw query
  change ∀ x, floor ≤ x → x ≠ P.a+5 → x ≠ P.a+8 → x ≠ P.a+13 → x ≠ P.a+14 → x ≠ P.a+15 →
    x ≠ P.a+30 → x ≠ P.a+31 → x ≠ P.a+33 → z.mem x=y.mem x at frame
  let scratch (i : ℕ) : Prop := i=5 ∨ i=8 ∨ i=13 ∨ i=14 ∨ i=15 ∨ i=30 ∨ i=31 ∨ i=33
  have stable (i : ℕ) (h : ¬scratch i) : z.mem (P.a+i)=y.mem (P.a+i) := by
    dsimp [scratch] at h;apply frame <;> omega
  have both (i : ℕ) (h : ¬scratch i) (h' : ¬solverRegister i) := (stable i h).trans (kept i h')
  have headZ := headerY.transport (v := z) (fun x hx => by
    have eq : P.a+(x-P.a)=x := by omega
    simpa only [eq] using stable (x-P.a) (by dsimp [scratch];omega))
  have lay : P.layout z :=
    ⟨headZ,mask.trans prefixEq.symm,(both 11 (by decide) (by decide)).trans beginAt.degree,
      (both 12 (by decide) (by decide)).trans (beginAt.dim.trans dimension.symm),len,card,logarithm,
      (stable 16 (by decide)).trans seen₀,(both 19 (by decide) (by decide)).trans beginAt.cap,
      (both 23 (by decide) (by decide)).trans beginAt.zero,(both 24 (by decide) (by decide)).trans beginAt.one,
      (stable 40 (by decide)).trans base₀,(stable 41 (by decide)).trans dim₀,(stable 50 (by decide)).trans pin₀,
      (stable 51 (by decide)).trans rows₀,(stable 52 (by decide)).trans row₀,(stable 53 (by decide)).trans after₀,
      (stable 54 (by decide)).trans pause₀,(stable 55 (by decide)).trans unit₀,(stable 56 (by decide)).trans two₀,
      (both 66 (by decide) (by decide)).trans beginAt.limit,(both 67 (by decide) (by decide)).trans beginAt.stride⟩
  have above : P.a+69 < P.seenBase ∧ gridEnd ≤ P.seenBase := by
    rw [baseEq];dsimp [a,seenArea,solverArea,pinArea,rowArea,cell];omega
  have flags := tracksWords_empty P.dim P.seenBase z (fun x hx => by
    have away := unmodified x (by dsimp [a,cell] at above;omega) (fun h hh e => by
      have hreg := solverLayout_writes P.bank c d h hh
      rw [cell_add] at e
      unfold solverRegister at hreg
      change x=P.a+h.dst at e;omega)
    rw [frame x (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),away]
    exact empty x (by omega) (by omega))
  have bound : j ≤ (d+(initSolverLayout P.bank c d).length)*(b*(5*b+9)+15) := by
    change j ≤ Circuit.multiplicity v (initSolverLayout P.bank c d)*_ at wj
    rwa [initSolverLayout_work] at wj
  exact ⟨z,_,setup.seq shared,by omega,⟨lay,flags,by simpa using (both 22 (by decide) (by decide)).trans beginAt.parity⟩,
    (both 65 (by decide) (by decide)).trans beginAt.cursor,(both 68 (by decide) (by decide)).trans beginAt.total,out.trans out₀⟩
end
