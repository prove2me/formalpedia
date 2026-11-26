-- Prove2me | solution 1 for DirectedHamiltonicity.Main.InputRAM.TrialParameters.runTrials_exec
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-26T17:42:02.665926+00:00
-- url     : https://prove2.me/submissions/8b1efb8d-5d8c-4ab4-b655-0980ab095fdb

import Definitions.Def_DirectedHamiltonicity_ParityRAMInterfaces
import Theorems.Thm_EditGV897_Main_affine_count_correct

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

section LogCostRAMRanges

namespace TargetedSamplers.Structured

/-- An ascending loop can charge each iteration separately. A cumulative cost
bound permits output-sensitive enumeration even when one trial returns many words. -/
theorem forRange_exec_budget {τ : Tapes} {b : ℕ} (ptr stop one lo count : ℕ) (budget : ℕ → ℕ) (body : Cmd)
    (state : ℕ → Store → Prop)
    (control : ∀ i ≤ count, ∀ s, state i s → s.mem ptr = lo+i ∧ s.mem stop = lo+count)
    (bodyRun : ∀ i < count, ∀ s, state i s → s.Fits b →
      ∃ u k, Exec τ (fun st => st.Fits b) body s u k ∧ budget i+k+3 ≤ budget (i+1) ∧ u.mem ptr = lo+i ∧ u.mem one = 1 ∧
        state (i+1) (u.write ptr (lo+i+1)))
    (width : (lo+count).size ≤ b) (s : Store) (start : state 0 s) (fit : s.Fits b) :
    ∃ t j, Exec τ (fun st => st.Fits b) (forRange ptr stop one body) s t j ∧
      budget 0+j ≤ budget count+1 ∧ state count t := by
  have run (left i : ℕ) (he : i+left = count) (u : Store) (hi : state i u) (hf : u.Fits b) :
      ∃ t j, Exec τ (fun st => st.Fits b) (forRange ptr stop one body) u t j ∧
        budget i+j ≤ budget count+1 ∧ state count t := by
    induction left generalizing i u with
    | zero =>
      have eq : i = count := by omega
      obtain ⟨hp,hs⟩ := control i (by omega) u hi
      exact ⟨u,1,.done (by rw [hs,hp,eq]),by rw [eq],eq ▸ hi⟩
    | succ left ih =>
      obtain ⟨hp,hs⟩ := control i (by omega) u hi
      obtain ⟨v,k,ex,hk,hp',h1,hn⟩ := bodyRun i (by omega) u hi hf
      have hnext : (Op.add ptr ptr one).eval τ v = v.write ptr (lo+i+1) := by simp [Op.eval,hp',h1]
      have hiw := (Nat.size_le_size (show lo+i+1 ≤ lo+count by omega)).trans width
      have inc : Exec τ (fun st => st.Fits b) (.op (.add ptr ptr one)) v (v.write ptr (lo+i+1)) 1 := by
        simpa only [hnext] using (Exec.op (τ := τ) (inv := fun st => st.Fits b) v (.add ptr ptr one)
          (by rw [hnext]; exact Store.write_fits (ex.post hf) ptr hiw))
      obtain ⟨t,j,loop,hj,ret⟩ := ih (i+1) (by omega) _ hn (inc.post (ex.post hf))
      refine ⟨t,_,.again (by rw [hs,hp]; omega) (ex.seq inc) loop,?_,ret⟩
      omega
  exact run count 0 (by simp) s start fit

/-- A constant bound on the loop body gives three further primitive instructions
per iteration for the comparison, increment and back edge. -/
theorem forRange_exec {τ : Tapes} {b : ℕ} (ptr stop one lo count bound : ℕ) (body : Cmd)
    (state : ℕ → Store → Prop)
    (control : ∀ i ≤ count, ∀ s, state i s → s.mem ptr = lo+i ∧ s.mem stop = lo+count)
    (bodyRun : ∀ i < count, ∀ s, state i s → s.Fits b →
      ∃ u k, Exec τ (fun st => st.Fits b) body s u k ∧ k ≤ bound ∧ u.mem ptr = lo+i ∧ u.mem one = 1 ∧
        state (i+1) (u.write ptr (lo+i+1)))
    (width : (lo+count).size ≤ b) (s : Store) (start : state 0 s) (fit : s.Fits b) :
    ∃ t j, Exec τ (fun st => st.Fits b) (forRange ptr stop one body) s t j ∧
      j ≤ count*(bound+3)+1 ∧ state count t := by
  obtain ⟨t,j,run,cost,final⟩ := forRange_exec_budget (τ := τ) ptr stop one lo count
    (fun i => i*(bound+3)) body state control (fun i hi u hu fu => by
      obtain ⟨v,k,ex,work,ptr,unit,next⟩ := bodyRun i hi u hu fu
      exact ⟨v,k,ex,by rw [Nat.succ_mul]; omega,ptr,unit,next⟩) width s start fit
  exact ⟨t,j,run,by simpa using cost,final⟩

/-- The outer loop pays once per trial and once per returned word. The result keeps
both counts separate so that a cap on their total gives a linear trial budget. -/
theorem forRange_exec_reported {τ : Tapes} {b : ℕ} (ptr stop one count setup perWord : ℕ)
    (reports : ℕ → ℕ) (body : Cmd) (state : ℕ → Store → Prop)
    (control : ∀ i ≤ count, ∀ s, state i s → s.mem ptr=i ∧ s.mem stop=count)
    (bodyRun : ∀ i < count, ∀ s, state i s → s.Fits b →
      ∃ u k, Exec τ (fun st => st.Fits b) body s u k ∧ k ≤ setup+reports i*perWord ∧
        u.mem ptr=i ∧ u.mem one=1 ∧ state (i+1) (u.write ptr (i+1)))
    (width : count.size ≤ b) (s : Store) (start : state 0 s) (fit : s.Fits b) :
    ∃ t j, Exec τ (fun st => st.Fits b) (forRange ptr stop one body) s t j ∧
      j ≤ count*(setup+3)+prefixReports reports count*perWord+1 ∧ state count t := by
  let budget := fun i => i*(setup+3)+prefixReports reports i*perWord
  obtain ⟨t,j,ex,cost,post⟩ := forRange_exec_budget (τ := τ) ptr stop one 0 count budget body state
    (by simpa only [Nat.zero_add] using control) (fun i hi u hu fu => by
      obtain ⟨v,k,run,work,ptr,unit,next⟩ := bodyRun i hi u hu fu
      refine ⟨v,k,run,?_,by simpa using ptr,unit,by simpa using next⟩
      simp only [budget,prefixReports,Nat.succ_mul,Nat.add_mul]
      omega) (by simpa using width) s start fit
  exact ⟨t,j,ex,by simpa [budget,prefixReports] using cost,post⟩

end TargetedSamplers.Structured

end LogCostRAMRanges

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

theorem size_mul_le_add (x y : ℕ) : (x*y).size ≤ x.size+y.size := by
  apply Nat.size_le.mpr
  rw [pow_add]
  exact (Nat.mul_le_mul_left x (Nat.lt_size_self y).le).trans_lt
    (Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self x) (pow_pos (by decide) _))

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

section LogCostRAMTabulate

namespace TargetedSamplers.Structured

theorem tabulate_exec {τ : Tapes} {b : ℕ} (ptr stop one value lo count cost : ℕ) (entry : Cmd)
    (f : ℕ → ℕ) (K : Store → Prop) (limit : ∀ u, K u → u.mem stop=lo+count ∧ u.mem one=1)
    (stable : ∀ u, K u → ∀ a v, a=ptr ∨ lo ≤ a ∧ a < lo+count → K (u.write a v))
    (separate : ptr < lo ∧ stop < lo ∧ one < lo ∧ value < lo)
    (compute : ∀ i < count, ∀ u, K u → u.mem ptr=lo+i → u.Fits b →
      ∃ v j, Exec τ (fun st => st.Fits b) entry u v j ∧ j ≤ cost ∧ K v ∧ v.mem ptr=lo+i ∧
        v.mem value=f i ∧ v.out=u.out ∧ ∀ a ≥ lo, v.mem a=u.mem a)
    (space : (lo+count).size ≤ b) (s : Store) (inv : K s) (pos : s.mem ptr=lo) (fit : s.Fits b) :
    ∃ t j, Exec τ (fun st => st.Fits b) (tabulate ptr stop one value entry) s t j ∧ j ≤ count*(cost+4)+1 ∧
      K t ∧ t.mem ptr=lo+count ∧ t.out=s.out ∧ ∀ a ≥ lo,
        t.mem a = if a < lo+count then f (a-lo) else s.mem a := by
  let state (i : ℕ) (u : Store) := K u ∧ u.mem ptr=lo+i ∧ u.out=s.out ∧
    ∀ a ≥ lo, u.mem a = if a < lo+i then f (a-lo) else s.mem a
  have control (i : ℕ) (_ : i ≤ count) (u : Store) (h : state i u) :
      u.mem ptr=lo+i ∧ u.mem stop=lo+count := ⟨h.2.1,(limit u h.1).1⟩
  have initial : state 0 s := ⟨inv,by simpa using pos,rfl,fun a ha => by simp [Nat.not_lt.mpr ha]⟩
  have step (i : ℕ) (hi : i < count) (u : Store) (h : state i u) (fu : u.Fits b) :
      ∃ z j, Exec τ (fun st => st.Fits b) (.seq entry (.op (.store ptr value))) u z j ∧ j ≤ cost+1 ∧
        z.mem ptr=lo+i ∧ z.mem one=1 ∧ state (i+1) (z.write ptr (lo+i+1)) := by
    obtain ⟨v,j,ex,bound,kv,pp,val,out,keep⟩ := compute i hi u h.1 h.2.1 fu
    let z := v.write (lo+i) (f i)
    have ev : (Op.store ptr value).eval τ v = z := by simp [Op.eval,z,pp,val]
    have zw : z.Fits b := Store.write_fits (ex.post fu) _ (val ▸ (ex.post fu) value)
    have store : Exec τ (fun st => st.Fits b) (.op (.store ptr value)) v z 1 := by
      simpa only [ev] using (Exec.op (τ := τ) (inv := fun st => st.Fits b) v (.store ptr value) (ev ▸ zw))
    have kz : K z := stable v kv _ _ (Or.inr ⟨by omega,by omega⟩)
    have next := stable z kz ptr (lo+i+1) (Or.inl rfl)
    refine ⟨z,_,ex.seq store,by omega,by simp [z,Store.write,show ptr ≠ lo+i by omega,pp],(limit z kz).2,
      next,by simp [Store.write,Nat.add_assoc],out.trans h.2.2.1,?_⟩
    intro a ha
    have dif : a ≠ ptr := by omega
    by_cases eq : a=lo+i
    · subst a; simp [z,Store.write,dif]
    · rw [show (z.write ptr (lo+i+1)).mem a = v.mem a by simp [z,Store.write,dif,eq],keep _ ha,h.2.2.2 a ha]
      split <;> split <;> first | omega | rfl
  obtain ⟨t,j,run,w,post⟩ := forRange_exec (τ := τ) ptr stop one lo count (cost+1) _ state control step space s initial fit
  exact ⟨t,j,run,by simpa [Nat.add_assoc] using w,post⟩

end TargetedSamplers.Structured

end LogCostRAMTabulate

section PackedBinaryStacks

namespace TargetedSamplers.Structured.BinaryStack

open Word

@[simp] theorem packed_nil : packed [] = 1 := rfl

theorem packed_cons (b : Bool) (xs : List Bool) : packed (b::xs) = packed xs+packed xs+b.toNat := by
  cases b <;> simp [packed,Nat.bit,two_mul]

theorem packed_pos (xs : List Bool) : 0 < packed xs := by
  induction xs with
  | nil => decide
  | cons b xs ih => rw [packed_cons]; omega

@[simp] theorem packed_size (xs : List Bool) : (packed xs).size = xs.length+1 := by
  induction xs with
  | nil => decide
  | cons b xs ih =>
    change (Nat.bit b (packed xs)).size = _
    rw [Nat.size_bit (Nat.ne_of_gt (packed_pos (b::xs))),ih,List.length_cons]

/-- Bits below the high sentinel are the numbered coordinates of the subset. -/
theorem packed_testBit (xs : List Bool) (i : ℕ) (hi : i < xs.length) : (packed xs).testBit i = xs[i] := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons b bs ih =>
    cases i with
    | zero => exact Nat.testBit_bit_zero b (packed bs)
    | succ i => simpa only [packed,Nat.testBit_bit_succ,List.getElem_cons_succ] using ih i (by simpa using hi)

/-- The packed word is a unique sparse-table key, including for lists with leading
or trailing zero bits. The lookup cost depends only on its bit length. -/
theorem packed_injective : Function.Injective packed := by
  intro xs ys h
  have sizes := congrArg Nat.size h
  have len : xs.length=ys.length := by simpa using sizes
  apply List.ext_getElem len
  intro i left right
  rw [← packed_testBit xs i left,← packed_testBit ys i right,h]

end TargetedSamplers.Structured.BinaryStack

end PackedBinaryStacks

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

theorem readTrial_exec {τ : Tapes} {b : ℕ} (bank offset k i : ℕ) (s : Store)
    (offsetAt : s.mem (cell bank+13)=offset) (widthAt : s.mem (cell bank+15)=k)
    (trialAt : s.mem (cell bank+65)=i) (zero : s.mem (cell bank+23)=0) (fit : s.Fits b)
    (hb : 2 ≤ b) (width : k+1 ≤ b) (addr : (offset+k*i+k+2*k+2).size ≤ b) :
    let a := cell bank
    ∃ u j, Exec τ (fun t => t.Fits b) (readTrial bank) s u j ∧ j ≤ 4*(b*(5*b+9)+15)+9*k+3 ∧
      u.mem (a+6)=(binaryRank k (fun j => τ.coins[offset+k*i+j.val]?.getD false)).val ∧ u.out=s.out ∧
      ∀ x, 14 ≤ x → x ≠ a+6 → (x < a+30 ∨ a+34 < x) → u.mem x=s.mem x := by
  intro a
  let v := fun j => s.mem (cell (bank+j))
  have at₁ : v 13=offset := by simpa [v,cell_add] using offsetAt
  have at₂ : v 15=k := by simpa [v,cell_add] using widthAt
  have at₃ : v 65=i := by simpa [v,cell_add] using trialAt
  have space (x : ℕ) (hx : x ≤ offset+k*i+k+2*k+2) : x.size ≤ b := (Nat.size_le_size hx).trans addr
  have room : Circuit.width v trialAddress ≤ b := by
    simp [Circuit.width,trialAddress,Assignment.update,Expression.eval,Expression.width,Arithmetic.value,at₁,at₂,at₃]
    repeat' apply And.intro
    all_goals first | apply space <;> omega | omega
  obtain ⟨t,j,setup,wj,regs,ret,frame⟩ := Circuit.bank_exec (τ := τ) bank trialAddress s fit hb room
  have work : j ≤ 4*(b*(5*b+9)+15) := wj
  have vals : t.mem (a+30)=offset+k*i+k ∧ t.mem (a+31)=offset+k*i ∧ t.mem (a+32)=1 := by
    have h (l : ℕ) : t.mem (a+l)=Circuit.result v trialAddress l := by
      rw [← cell_add bank l]
      exact regs l
    simp [h,Circuit.result,trialAddress,Assignment.update,Expression.eval,Arithmetic.value,at₁,at₂,at₃]
  let r := window (a+30) 5
  obtain ⟨y,l,read,wl,_,rank,ry,keep⟩ := readRank_exec (τ := τ) r t (offset+k*i) k
    (by exact vals.1) (by exact vals.2.1) (by exact vals.2.2) (setup.post fit) hb width
  have preserve (x : ℕ) (above : 14 ≤ x) (other : x < a+30 ∨ a+34 < x) : y.mem x=s.mem x := by
    have outside (j : Fin 5) : x ≠ r j := by change x ≠ a+30+j.val;omega
    rw [keep x (outside _) (outside _) (outside _)]
    apply frame x above
    intro h hh
    simp [trialAddress] at hh
    rcases hh with rfl | rfl | rfl | rfl <;> simp only [cell_add] <;> change x ≠ a+_ <;> omega
  have zy := (preserve (a+23) (by dsimp [a,cell];omega) (by omega)).trans zero
  have copy := saveWord_exec (τ := τ) a 6 (a+34) y zy (read.post (setup.post fit))
  refine ⟨_,_,setup.seq (read.seq copy),by omega,?_,ry.trans ret,?_⟩
  · change y.mem (a+34)=_ at rank
    simpa [Store.write] using rank
  · intro x hx apart other
    simpa [Store.write,apart] using preserve x hx other

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMTrialRead

section HamiltonianRAMSolverLayout

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers.Structured TargetedSamplers.Structured.Word

theorem initSolverLayout_values (bank c d : ℕ) (v : ℕ → ℕ) (z : v 23=0) (one : v 24=1) (two : v 25=2) :
    let t := Circuit.result v (initSolverLayout bank c d)
    let q := v 12
    t 40=solverArea bank q ∧ t 41=q ∧ t 50=solverArea bank q ∧ t 51=q ∧
      t 52=rowArea bank ∧ t 53=pinArea bank q ∧ t 54=0 ∧ t 55=1 ∧ t 56=2 ∧
      t 16=seenArea bank q c d (v 26) := by
  simp [initSolverLayout,Circuit.result,Assignment.update,Expression.eval,Arithmetic.value,Function.update_apply,
    z,one,two,solverArea,pinArea,seenArea]

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMSolverLayout

section LogCostRAMMarkWord

namespace TargetedSamplers.Structured.BinaryStack

theorem markWord_exec {τ : TargetedSamplers.Tapes} {b q base : ℕ} (r : Fin 5 ↪ ℕ)
    (seen : Finset (List Bool)) (xs : List Bool) (s : Store) (len : xs.length=q)
    (table : tracksWords q base seen s) (area : s.mem (r 0)=base) (key : s.mem (r 1)=packed xs)
    (one : s.mem (r 2)=1) (sep : ∀ i, r i < base) (fit : s.Fits b) (width : (base+packed xs).size ≤ b) :
    let t := ((markWord r).run τ s).last
    Exec τ (fun u => u.Fits b) (markWord r).cmd s t 3 ∧ t.mem (r 4)=(if xs ∈ seen then 1 else 0) ∧
      tracksWords q base (insert xs seen) t ∧ t.out=s.out ∧
      ∀ a, a ≠ r 3 → a ≠ r 4 → a ≠ base+packed xs → t.mem a=s.mem a := by
  intro t
  let adr := base+packed xs
  have dist {i j : Fin 5} (h : i ≠ j) : r i ≠ r j := r.injective.ne h
  have above (i : Fin 5) : adr ≠ r i := by have := sep i; dsimp [adr]; omega
  have away (i : Fin 5) : r i ≠ adr := (above i).symm
  have wone : (1:ℕ).size ≤ b := one ▸ fit (r 2)
  have ww : ((markWord r).run τ s).writeWidth ≤ b := by
    simp (disch := decide) [markWord,Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,
      Function.update_apply,dist,area,key,one,← show adr=base+packed xs from rfl,above,fit adr]
    exact ⟨width,wone⟩
  have exec := (markWord r).exec τ s b fit ww
  have old : t.mem (r 4)=s.mem adr := by
    simp (disch := decide) [t,markWord,Structured.sequence,Fragment.run,Op.eval,Store.write,Function.update_apply,
      dist,area,key,← show adr=base+packed xs from rfl,above,away]
  have flag : t.mem adr=1 := by
    simp (disch := decide) [t,markWord,Structured.sequence,Fragment.run,Op.eval,Store.write,Function.update_apply,
      dist,area,key,one,← show adr=base+packed xs from rfl]
  have frame (a : ℕ) (h₃ : a ≠ r 3) (h₄ : a ≠ r 4) (ha : a ≠ adr) : t.mem a=s.mem a := by
    simp (disch := decide) [t,markWord,Structured.sequence,Fragment.run,Op.eval,Store.write,Function.update_apply,
      dist,h₃,h₄,ha,area,key,← show adr=base+packed xs from rfl]
  refine ⟨exec,old.trans (table xs len),?_,rfl,frame⟩
  intro ys length
  by_cases eq : ys=xs
  · subst ys
    simpa using flag
  · have diff : packed ys ≠ packed xs := packed_injective.ne eq
    have low₃ := sep 3
    have low₄ := sep 4
    rw [frame _ (by omega) (by omega) (by dsimp [adr];omega),table ys length]
    simp [eq]

end TargetedSamplers.Structured.BinaryStack

end LogCostRAMMarkWord

section HamiltonianRAMVisitWord

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.BinaryStack

open scoped BigOperators

theorem parityWord_insert (f : List Bool → ZMod 2) (seen : Finset (List Bool)) (x : List Bool) :
    parityWord f (insert x seen)=
      if x∈seen then parityWord f seen else if f x ≠ 0 then 1-parityWord f seen else parityWord f seen := by
  by_cases present : x∈seen
  · simp [present]
  · simp only [if_neg present,parityWord,Finset.sum_insert present]
    exact (by decide : ∀ a b : ZMod 2, (decide (a+b ≠ 0)).toNat =
      if a ≠ 0 then 1-(decide (b ≠ 0)).toNat else (decide (b ≠ 0)).toNat) _ _

private theorem leafArgs_exec {τ : Tapes} {b : ℕ} (a : ℕ) (u : Store) (zero : u.mem (a+23)=0)
    (fit : u.Fits b) (hb : 2 ≤ b) :
    let v := ((leafArgs a).run τ u).last
    Exec τ (fun z => z.Fits b) (leafArgs a).cmd u v 3 ∧ v.out=u.out ∧ v.mem (a+6)=u.mem (a+58) ∧
      v.mem (a+7)=u.mem (a+11) ∧ v.mem (a+8)=3 ∧ ∀ x, x ≠ a+6 → x ≠ a+7 → x ≠ a+8 → v.mem x=u.mem x := by
  intro v
  have sep (i j : ℕ) (h : i ≠ j) : a+i ≠ a+j := by omega
  have room : ((leafArgs a).run τ u).writeWidth ≤ b := by
    simp (disch := decide) [leafArgs,Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,
      Function.update_apply,sep,zero,fit (a+11),fit (a+58),show (3:ℕ).size ≤ b from (by decide : (3:ℕ).size ≤ 2).trans hb]
  refine ⟨(leafArgs a).exec τ u b fit room,rfl,?_,?_,?_,?_⟩
  all_goals first
    | intro x h₆ h₇ h₈;simp [v,leafArgs,Structured.sequence,Fragment.run,Op.eval,Store.write,h₆,h₇,h₈]
    | simp (disch := decide) [v,leafArgs,Structured.sequence,Fragment.run,Op.eval,Store.write,Function.update_apply,sep,zero]

/-- Test and insert the sparse key before querying its determinant bit. Repetitions
make no call, and zero and nonzero determinant coefficients update parity correctly. -/
theorem visitWord_exec {τ : Tapes} {b q : ℕ} (a floor seenBase B cost : ℕ) (kernel : Cmd)
    (f : List Bool → ZMod 2) (seen : Finset (List Bool)) (xs : List Bool) (u : Store)
    (len : xs.length=q) (fit : u.Fits b) (hb : 2 ≤ b) (lo : floor ≤ a) (tableHigh : a+58 < seenBase)
    (baseAt : u.mem (a+16)=seenBase) (current : u.mem (a+58)=packed xs) (deg : u.mem (a+11)=B)
    (zero : u.mem (a+23)=0) (one : u.mem (a+24)=1) (sum : u.mem (a+22)=parityWord f seen)
    (table : tracksWords q seenBase seen u) (room : (seenBase+packed xs).size ≤ b)
    (call : ∀ v : Store, v.mem (a+6)=packed xs → v.mem (a+7)=B → v.mem (a+8)=3 →
      (∀ x, floor ≤ x → x ≠ a+6 → x ≠ a+7 → x ≠ a+8 → x ≠ a+33 → x ≠ a+34 → x ≠ seenBase+packed xs → v.mem x=u.mem x) →
      v.Fits b → ∃ t j, Exec τ (fun y => y.Fits b) kernel v t j ∧ j ≤ cost ∧
        t.mem 0=(decide (f xs ≠ 0)).toNat ∧ t.out=v.out ∧ ∀ x ≥ floor,t.mem x=v.mem x) :
    ∃ z j, Exec τ (fun v => v.Fits b) (visitWord a kernel) u z j ∧ j ≤ cost+12 ∧
      tracksWords q seenBase (insert xs seen) z ∧ z.mem (a+22)=parityWord f (insert xs seen) ∧ z.out=u.out ∧
      ∀ x, floor ≤ x → x ≠ a+6 → x ≠ a+7 → x ≠ a+8 → x ≠ a+22 → x ≠ a+33 → x ≠ a+34 →
        x ≠ seenBase+packed xs → z.mem x=u.mem x := by
  let r := markRegisters a
  let y := ((markWord r).run τ u).last
  have sep : ∀ i, r i < seenBase := by
    intro i
    fin_cases i
    · change a+16 < seenBase;omega
    · exact tableHigh
    · change a+24 < seenBase;omega
    · change a+33 < seenBase;omega
    · change a+34 < seenBase;omega
  obtain ⟨mark,old,updated,ry,frame⟩ := markWord_exec (τ := τ) r seen xs u len table baseAt current one sep fit room
  change y.mem (a+34)=_ at old
  change ∀ x, x ≠ a+33 → x ≠ a+34 → x ≠ seenBase+packed xs → y.mem x=u.mem x at frame
  have lowY (i : ℕ) (hi : i ≤ 58) (h₃ : i ≠ 33) (h₄ : i ≠ 34) := frame (a+i) (by omega) (by omega) (by omega)
  have zy := (lowY 23 (by decide) (by decide) (by decide)).trans zero
  by_cases present : xs∈seen
  · have cmp : ¬y.mem (a+34) ≤ y.mem (a+23) := by simp [old,present,zy]
    refine ⟨y,_,mark.seq (.no cmp (.skip y)),by omega,updated,?_,ry,fun x _ _ _ _ _ h₃ h₄ e => frame x h₃ h₄ e⟩
    simpa [parityWord_insert,present] using (lowY 22 (by decide) (by decide) (by decide)).trans sum
  · have cmp : y.mem (a+34) ≤ y.mem (a+23) := by simp [old,present,zy]
    let v := ((leafArgs a).run τ y).last
    obtain ⟨prep,rp,arg₆,arg₇,arg₈,keep⟩ := leafArgs_exec (τ := τ) a y zy (mark.post fit) hb
    have clean (x : ℕ) (_ : floor ≤ x) (h₆ : x ≠ a+6) (h₇ : x ≠ a+7) (h₈ : x ≠ a+8)
        (h₃ : x ≠ a+33) (h₄ : x ≠ a+34) (away : x ≠ seenBase+packed xs) :=
      (keep x h₆ h₇ h₈).trans (frame x h₃ h₄ away)
    obtain ⟨t,k,eval,wk,ans,ret,stable⟩ := call v
      (arg₆.trans ((lowY 58 (by decide) (by decide) (by decide)).trans current))
      (arg₇.trans ((lowY 11 (by decide) (by decide) (by decide)).trans deg)) arg₈ clean (prep.post (mark.post fit))
    have high (x : ℕ) (hx : floor ≤ x) (h₆ : x ≠ a+6) (h₇ : x ≠ a+7) (h₈ : x ≠ a+8) :
        t.mem x=y.mem x := (stable x hx).trans (keep x h₆ h₇ h₈)
    have lowT (i : ℕ) (hi : i ≤ 58) (other : i ≠ 6 ∧ i ≠ 7 ∧ i ≠ 8 ∧ i ≠ 33 ∧ i ≠ 34) :
        t.mem (a+i)=u.mem (a+i) := (high _ (by omega) (by omega) (by omega) (by omega)).trans
      (lowY i hi (by omega) (by omega))
    have zt := (lowT 23 (by decide) (by decide)).trans zero
    have ot := (lowT 24 (by decide) (by decide)).trans one
    have st := (lowT 22 (by decide) (by decide)).trans sum
    have tracked : tracksWords q seenBase (insert xs seen) t := fun ys hy =>
      (high _ (by omega) (by omega) (by omega) (by omega)).trans (updated ys hy)
    have frozen (x : ℕ) (hx : floor ≤ x) (h₆ : x ≠ a+6) (h₇ : x ≠ a+7) (h₈ : x ≠ a+8)
        (h₃ : x ≠ a+33) (h₄ : x ≠ a+34) (away : x ≠ seenBase+packed xs) :=
      (stable x hx).trans (clean x hx h₆ h₇ h₈ h₃ h₄ away)
    by_cases nonzero : f xs ≠ 0
    · have toggle : ¬t.mem 0 ≤ t.mem (a+23) := by simp [ans,nonzero,zt]
      let z := t.write (a+22) (1-parityWord f seen)
      have op : (Op.sub (a+22) (a+24) (a+22)).eval τ t=z := by simp [Op.eval,z,ot,st]
      have sz : (1-parityWord f seen).size ≤ b := (Nat.size_le_size (Nat.sub_le _ _)).trans
        (show (1:ℕ).size ≤ b from (by decide : (1:ℕ).size ≤ 2).trans hb)
      have run : Exec τ (fun u => u.Fits b) (.op (.sub (a+22) (a+24) (a+22))) t z 1 := by
        simpa only [op] using Exec.op (τ := τ) (inv := fun u => u.Fits b) t (.sub (a+22) (a+24) (a+22))
          (op ▸ Store.write_fits (eval.post (prep.post (mark.post fit))) _ sz)
      refine ⟨z,_,mark.seq (.yes cmp (prep.seq (eval.seq (.no toggle run)))),by omega,?_,?_,ret.trans (rp.trans ry),?_⟩
      · intro ys hy;simpa [z,Store.write,show seenBase+packed ys ≠ a+22 by omega] using tracked ys hy
      · simp [z,Store.write,parityWord_insert,present,nonzero]
      · intro x hx h₆ h₇ h₈ h₂ h₃ h₄ away;simpa [z,Store.write,h₂] using frozen x hx h₆ h₇ h₈ h₃ h₄ away
    · have skip : t.mem 0 ≤ t.mem (a+23) := by simp [ans,nonzero,zt]
      exact ⟨t,_,mark.seq (.yes cmp (prep.seq (eval.seq (.yes skip (.skip t))))),by omega,tracked,
        by simpa [parityWord_insert,present,nonzero] using st,ret.trans (rp.trans ry),
        fun x hx h₆ h₇ h₈ _ h₃ h₄ away => frozen x hx h₆ h₇ h₈ h₃ h₄ away⟩

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMVisitWord

section HamiltonianRAMTrialState

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers.Structured TargetedSamplers.Structured.Word TargetedSamplers.Structured.BinaryStack

abbrev trialRegister (i : ℕ) : Prop :=
  i ≤ 5 ∨ i=9 ∨ 11 ≤ i ∧ i ≤ 16 ∨ i=19 ∨ i=23 ∨ i=24 ∨ i=40 ∨ i=41 ∨
    50 ≤ i ∧ i ≤ 56 ∨ i=66 ∨ i=67

theorem TrialState.transport {bank n h src dst graph wbits mask maskLen card q M B seenBase : ℕ} {u v : Store}
    (s : TrialState bank n h src dst graph wbits mask maskLen card q M B seenBase u)
    (keep : ∀ i, trialRegister i → v.mem (cell bank+i)=u.mem (cell bank+i)) :
    TrialState bank n h src dst graph wbits mask maskLen card q M B seenBase v := by
  have head := s.header.transport (v := v) (fun x hx => by
    have lo : cell bank ≤ x := by omega
    have eq : cell bank+(x-cell bank)=x := by omega
    simpa only [eq] using keep (x-cell bank) (by unfold trialRegister;omega))
  exact ⟨head,(keep 5 (by decide)).trans s.maskAt,(keep 11 (by decide)).trans s.target,(keep 12 (by decide)).trans s.dim,
    (keep 13 (by decide)).trans s.masks,(keep 14 (by decide)).trans s.choices,(keep 15 (by decide)).trans s.coinWidth,
    (keep 16 (by decide)).trans s.seenAt,(keep 19 (by decide)).trans s.cap,(keep 23 (by decide)).trans s.zero,
    (keep 24 (by decide)).trans s.one,(keep 40 (by decide)).trans s.baseAt,(keep 41 (by decide)).trans s.columns,
    (keep 50 (by decide)).trans s.pinEnd,(keep 51 (by decide)).trans s.rows,(keep 52 (by decide)).trans s.first,
    (keep 53 (by decide)).trans s.after,(keep 54 (by decide)).trans s.pause,(keep 55 (by decide)).trans s.unit,
    (keep 56 (by decide)).trans s.two,(keep 66 (by decide)).trans s.limit,(keep 67 (by decide)).trans s.stride⟩

theorem TrialInvariant.preserve {bank n h src dst graph wbits mask maskLen card q M B seenBase : ℕ}
    {f : List Bool → ZMod 2} {seen : Finset (List Bool)} {u v : Store}
    (s : TrialInvariant bank n h src dst graph wbits mask maskLen card q M B seenBase f seen u)
    (regs : ∀ i, trialRegister i ∨ i=22 → v.mem (cell bank+i)=u.mem (cell bank+i))
    (high : ∀ x ≥ seenBase, v.mem x=u.mem x) :
    TrialInvariant bank n h src dst graph wbits mask maskLen card q M B seenBase f seen v :=
  ⟨s.layout.transport (fun i hi => regs i (.inl hi)),fun x hx => (high _ (by omega)).trans (s.flags x hx),
    (regs 22 (.inr rfl)).trans s.parity⟩

theorem TrialInvariant.writeCursor {bank n h src dst graph wbits mask maskLen card q M B seenBase : ℕ}
    {f : List Bool → ZMod 2} {seen : Finset (List Bool)} {u : Store}
    (s : TrialInvariant bank n h src dst graph wbits mask maskLen card q M B seenBase f seen u)
    (top : cell bank+69 < seenBase) (a v : ℕ) (cursor : a=cell bank+65 ∨ a=cell bank+68) :
    TrialInvariant bank n h src dst graph wbits mask maskLen card q M B seenBase f seen (u.write a v) :=
  s.preserve (fun i hi => by
    have neq : cell bank+i ≠ a := by unfold trialRegister at hi;omega
    simp [Store.write,neq]) (fun x hx => by simp [Store.write,show x ≠ a by omega])

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMTrialState

section LogCostRAMIndexedQuery

namespace TargetedSamplers.Structured

/-- Only the input index and cursor vary inside a dense polynomial query.
The result can be read directly from the kernel's output register by the store instruction. -/
theorem indexedQueries_exec {τ : Tapes} {b : ℕ} (floor ptr stop one value src index lo len cost : ℕ)
    (kernel : Cmd) (entries : ℕ → ℕ) (s : Store)
    (bank : floor ≤ ptr ∧ floor ≤ stop ∧ floor ≤ one ∧ floor ≤ src)
    (separate : ptr < lo ∧ stop < lo ∧ one < lo ∧ value < lo ∧ src < lo ∧ index < lo)
    (fixed : stop ≠ ptr ∧ one ≠ ptr ∧ src ≠ ptr ∧ stop ≠ index ∧ one ≠ index ∧ src ≠ index ∧ ptr ≠ index)
    (base : s.mem src=lo) (start : s.mem ptr=lo) (limit : s.mem stop=lo+len) (unit : s.mem one=1)
    (call : ∀ i < len, ∀ u, u.mem index=i →
      (∀ a, floor ≤ a → a < lo → a ≠ ptr → a ≠ index → u.mem a=s.mem a) → u.Fits b →
      ∃ t j, Exec τ (fun v => v.Fits b) kernel u t j ∧ j ≤ cost ∧ t.mem value=entries i ∧
        t.out=u.out ∧ ∀ a ≥ floor,t.mem a=u.mem a)
    (width : (lo+len).size ≤ b) (fit : s.Fits b) :
    ∃ t j, Exec τ (fun v => v.Fits b) (indexedQueries ptr stop one value src index kernel) s t j ∧
      j ≤ len*(cost+5)+1 ∧ t.mem ptr=lo+len ∧ t.out=s.out ∧
      (∀ a, floor ≤ a → a < lo → a ≠ ptr → a ≠ index → t.mem a=s.mem a) ∧
      ∀ a ≥ lo,t.mem a=if a < lo+len then entries (a-lo) else s.mem a := by
  let K (u : Store) := ∀ a, floor ≤ a → a < lo → a ≠ ptr → a ≠ index → u.mem a=s.mem a
  obtain ⟨p0,s0,o0,b0⟩ := bank
  obtain ⟨pp,sp,op,vp,bp,ip⟩ := separate
  obtain ⟨s1,o1,b1,si,oi,bi,pi⟩ := fixed
  have ctrl (u : Store) (h : K u) := And.intro ((h _ s0 sp s1 si).trans limit) ((h _ o0 op o1 oi).trans unit)
  have stable (u : Store) (h : K u) (d x : ℕ) (hx : d=ptr ∨ lo ≤ d ∧ d < lo+len) : K (u.write d x) := by
    intro a above below d1 d2
    simpa [Store.write,show a ≠ d by omega] using h a above below d1 d2
  have step (i : ℕ) (hi : i < len) (u : Store) (h : K u) (pos : u.mem ptr=lo+i) (fu : u.Fits b) :
      ∃ t j, Exec τ (fun v => v.Fits b) (.seq (.op (.sub index ptr src)) kernel) u t j ∧ j ≤ cost+1 ∧ K t ∧
        t.mem ptr=lo+i ∧ t.mem value=entries i ∧ t.out=u.out ∧ ∀ a ≥ lo,t.mem a=u.mem a := by
    let v := u.write index i
    have off := (h _ b0 bp b1 bi).trans base
    have sub : (Op.sub index ptr src).eval τ u=v := by simp [Op.eval,v,pos,off]
    have fv : v.Fits b := Store.write_fits fu _ ((Nat.size_le_size (by omega : i ≤ lo+len)).trans width)
    have ex : Exec τ (fun a => a.Fits b) (.op (.sub index ptr src)) u v 1 := by
      simpa only [sub] using Exec.op (τ := τ) (inv := fun a => a.Fits b) u (.sub index ptr src) (sub ▸ fv)
    have kv : K v := fun a above below dp di => by simpa [v,Store.write,di] using h a above below dp di
    obtain ⟨z,j,run,work,answer,out,frame⟩ := call i hi v (by simp [v,Store.write]) kv fv
    refine ⟨z,_,ex.seq run,by omega,fun a above below dp di => (frame a above).trans (kv a above below dp di),?_,
      answer,out,?_⟩
    · rw [frame _ p0];simp [v,Store.write,pi,pos]
    · intro a above
      rw [frame _ (by omega)];simp [v,Store.write,show a ≠ index by omega]
  obtain ⟨t,j,run,work,keep,atEnd,out,data⟩ := tabulate_exec (τ := τ) ptr stop one value lo len (cost+1)
    _ entries K ctrl stable ⟨pp,sp,op,vp⟩ step width s (fun _ _ _ _ _ => rfl) start fit
  exact ⟨t,j,run,by simpa only [Nat.add_assoc] using work,atEnd,out,keep,data⟩

end TargetedSamplers.Structured

end LogCostRAMIndexedQuery

section BoundedEnumeration

/-! Output-sensitive enumeration from a binary prefix-feasibility test. -/

namespace BoundedEnumeration

/-- A specification of all accepted completions. The prefix is stored in reverse order. -/
def completions (accept : List Bool → Bool) : ℕ → List Bool → List (List Bool)
  | 0, pref => if accept pref then [pref] else []
  | k + 1, pref => completions accept k (false :: pref) ++ completions accept k (true :: pref)

end BoundedEnumeration

end BoundedEnumeration

section CountedUnranking

namespace BoundedEnumeration

theorem unrank_eq_get (accept : List Bool → Bool) (count : ℕ → List Bool → ℕ) (n : ℕ)
    (counts : ∀ k p, k+p.length=n → count k p = (completions accept k p).length)
    (k : ℕ) (p : List Bool) (hp : k+p.length=n) (i : ℕ) (hi : i < (completions accept k p).length) :
    unrank count k p i = (completions accept k p)[i] := by
  induction k generalizing p i with
  | zero =>
    cases h : accept p
    · simp [completions,h] at hi
    · have eq : i=0 := by simp [completions,h] at hi; omega
      subst i
      simp [unrank,completions,h]
  | succ k ih =>
    have length (b : Bool) : k+(b::p).length=n := by simp; omega
    have left := counts k (false::p) (length false)
    simp only [unrank,left,completions]
    by_cases inLeft : i < (completions accept k (false::p)).length
    · rw [if_pos inLeft,List.getElem_append_left inLeft]
      exact ih _ (length false) i inLeft
    · rw [if_neg inLeft,List.getElem_append_right (by omega)]
      apply ih _ (length true)

end BoundedEnumeration

end CountedUnranking

section AffineRAMCountPort

namespace AffinePrefixEnumeration

open EditGV897.Main

open TargetedSamplers TargetedSamplers.Structured

theorem Port.transport {n : ℕ} {E : List (Equation n)} {base row pin bank : ℕ} {s t : Store}
    (h : Port E base row pin bank s) (keep : ∀ a, a=bank ∨ a=bank+1 ∨ a=bank+10 ∨ a=bank+11 ∨
      a=bank+12 ∨ a=bank+13 ∨ row ≤ a ∧ a < row+(denseWords E).length → t.mem a=s.mem a) :
    Port E base row pin bank t :=
  ⟨(keep _ (by omega)).trans h.target,(keep _ (by omega)).trans h.dimension,(keep _ (by omega)).trans h.pinEnd,
    (keep _ (by omega)).trans h.rows,(keep _ (by omega)).trans h.firstRow,(keep _ (by omega)).trans h.afterRows,
    fun i hi => (keep _ (by omega)).trans (h.rowData i hi)⟩

end AffinePrefixEnumeration

end AffineRAMCountPort

section HamiltonianRAMRowQueries

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word

open AffinePrefixEnumeration EditGV897.Main

/-- The Gaussian kernel receives the entire dense augmented matrix, including
the constant term in each row and also rows whose coefficients are all zero. -/
theorem rowQueries_exec {τ : Tapes} {b q : ℕ} (E : List (Equation q))
    (bank n h src dst graph width mask key floor cost : ℕ) (kernel : Cmd) (u : Store)
    (head : RequestHeader (cell bank) n h src dst graph width u)
    (maskAt : u.mem (cell bank+5)=mask) (keyAt : u.mem (cell bank+6)=key) (modeAt : u.mem (cell bank+8)=2)
    (high : floor ≤ cell bank) (shape : (denseWords E).length=q*(q+1)) (rows : E.length=q)
    (baseAt : u.mem (cell bank+40)=solverArea bank q) (dim : u.mem (cell bank+41)=q)
    (pinEnd : u.mem (cell bank+50)=pinArea bank q+q) (rowsAt : u.mem (cell bank+51)=q)
    (first : u.mem (cell bank+52)=rowArea bank) (after : u.mem (cell bank+53)=pinArea bank q)
    (cursor : u.mem (cell bank+34)=rowArea bank) (inc : u.mem (cell bank+24)=1)
    (call : ∀ (i : ℕ) (hi : i < (denseWords E).length) (v : Store), RequestHeader (cell bank) n h src dst graph width v →
      RequestArgs (cell bank) mask key i 2 v → v.Fits b →
      ∃ t j, Exec τ (fun y => y.Fits b) kernel v t j ∧ j ≤ cost ∧ t.mem 0=(denseWords E)[i] ∧
        t.out=v.out ∧ ∀ x ≥ floor,t.mem x=v.mem x)
    (room : (pinArea bank q).size ≤ b) (fit : u.Fits b) :
    let a := cell bank
    let lo := rowArea bank
    let pin := pinArea bank q
    ∃ v j, Exec τ (fun t => t.Fits b) (rowQueries bank kernel) u v j ∧ j ≤ q*(q+1)*(cost+5)+1 ∧
      Port E (solverArea bank q) lo pin (a+40) v ∧ v.out=u.out ∧
      ∀ x, floor ≤ x → x ≠ a+7 → x ≠ a+34 → (x < lo ∨ pin ≤ x) → v.mem x=u.mem x := by
  intro a lo pin
  let len := (denseWords E).length
  let entry := fun (i : ℕ) => (denseWords E)[i]?.getD 0
  have span : lo+len=pin := by simp [pin,pinArea,lo,len,shape]
  have rowHigh : lo=a+104 := rfl
  have ask (i : ℕ) (hi : i < len) (v : Store) (idx : v.mem (a+7)=i)
      (keep : ∀ x, floor ≤ x → x < lo → x ≠ a+34 → x ≠ a+7 → v.mem x=u.mem x) (fv : v.Fits b) :
      ∃ t j, Exec τ (fun y => y.Fits b) kernel v t j ∧ j ≤ cost ∧ t.mem 0=entry i ∧ t.out=v.out ∧ ∀ x ≥ floor,t.mem x=v.mem x := by
    have hold (x : ℕ) (hx : a ≤ x ∧ x ≤ a+9) (other : x ≠ a+7) := keep x (by omega) (by omega) (by omega) other
    have newHead := head.transport (v := v) (fun x hx => hold x (by omega) (by omega))
    have args : RequestArgs a mask key i 2 v := ⟨(hold _ (by omega) (by omega)).trans maskAt,
      (hold _ (by omega) (by omega)).trans keyAt,idx,(hold _ (by omega) (by omega)).trans modeAt⟩
    simpa only [entry,List.getElem?_eq_getElem hi,Option.getD_some] using call i hi v newHead args fv
  obtain ⟨v,j,run,budget,_,out,keep,data⟩ := indexedQueries_exec (τ := τ) floor (a+34) (a+53) (a+24) 0
    (a+52) (a+7) lo len cost kernel entry u (by omega) (by omega) (by omega) first cursor
    (after.trans span.symm) inc ask (by rwa [span]) fit
  have retained (i : ℕ) (hi : 40 ≤ i ∧ i ≤ 53) : v.mem (a+i)=u.mem (a+i) := keep _ (by omega) (by omega) (by omega) (by omega)
  have info : Port E (solverArea bank q) lo pin (a+40) v :=
    ⟨(retained 40 (by decide)).trans baseAt,(retained 41 (by decide)).trans dim,
      (retained 50 (by decide)).trans pinEnd,(retained 51 (by decide)).trans (rowsAt.trans rows.symm),
      (retained 52 (by decide)).trans first,(retained 53 (by decide)).trans (after.trans span.symm),by
        intro i hi
        rw [data (lo+i) (by omega),if_pos (Nat.add_lt_add_left hi lo),Nat.add_sub_cancel_left]
        simp [entry,List.getElem?_eq_getElem hi]⟩
  refine ⟨v,j,run,by simpa only [len,shape] using budget,info,out,?_⟩
  intro x low d₁ d₂ region
  rcases region with below | above
  · exact keep x low below d₂ d₁
  · rw [data x (by omega),if_neg (by omega)]

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMRowQueries

section LogCostRAMRankCursor

namespace TargetedSamplers.Structured.RankedPrefix

open BinaryStack

/-- The suffix stores Gaussian tape symbols 1 and 2. Its packed copy is the key
used for sparse deduplication and for reading coordinates of the candidate. -/
structure Cursor (bank pin n k rank : ℕ) (p : List Bool) (s : Store) : Prop where
  length : k+p.length=n
  column : s.mem (bank+6)=k
  pointer : s.mem (bank+9)=pin+k
  zero : s.mem (bank+14)=0
  one : s.mem (bank+15)=1
  two : s.mem (bank+16)=2
  residual : s.mem (bank+17)=rank
  mask : s.mem (bank+18)=packed p
  bits : ∀ i (hi : i < p.length), s.mem (pin+k+i)=1+p[i].toNat

theorem Cursor.transport {bank pin n k rank : ℕ} {p : List Bool} {s t : Store} (c : Cursor bank pin n k rank p s)
    (keep : ∀ a, (bank ≤ a ∧ a ≤ bank+18) ∨ (pin+k ≤ a ∧ a < pin+n) → t.mem a=s.mem a) :
    Cursor bank pin n k rank p t := by
  have len := c.length
  exact ⟨len,(keep _ (by omega)).trans c.column,(keep _ (by omega)).trans c.pointer,(keep _ (by omega)).trans c.zero,
    (keep _ (by omega)).trans c.one,(keep _ (by omega)).trans c.two,(keep _ (by omega)).trans c.residual,
    (keep _ (by omega)).trans c.mask,fun i hi => (keep _ (by omega)).trans (c.bits i hi)⟩

def outside (bank pin n a : ℕ) : Prop :=
  a ≠ bank+6 ∧ a ≠ bank+9 ∧ a ≠ bank+17 ∧ a ≠ bank+18 ∧ (a < pin ∨ pin+n ≤ a)

theorem enterFalse_exec {τ : Tapes} {bank pin n k rank b : ℕ} (p : List Bool) (u : Store)
    (c : Cursor bank pin n (k+1) rank p u) (sep : bank+20 ≤ pin) (fit : u.Fits b) (room : n+2 ≤ b) :
    let t := ((enterFalse bank).run τ u).last
    Exec τ (fun v => v.Fits b) (enterFalse bank).cmd u t 4 ∧ Cursor bank pin n k rank (false::p) t ∧
      t.out=u.out ∧ ∀ a, outside bank pin n a → t.mem a=u.mem a := by
  intro t
  let addr := pin+k
  have coord : (k+1)-1=k := by omega
  have ptr : (pin+(k+1))-1=addr := by dsimp [addr] <;> omega
  have low (i : ℕ) (hi : i < 20) : bank+i ≠ addr := by dsimp [addr]; omega
  have eq (i j : ℕ) : (bank+i=bank+j) ↔ i=j := by omega
  have data : packed p+packed p=packed (false::p) := by simp [packed_cons]
  have maskW : (packed (false::p)).size ≤ b := by simp [packed_size]; have := c.length; omega
  have ptrW : addr.size ≤ b := (Nat.size_le_size (by dsimp [addr]; omega : addr ≤ pin+(k+1))).trans
    (c.pointer ▸ fit (bank+9))
  have colW : k.size ≤ b := (Nat.size_le_size (Nat.le_succ k)).trans (by simpa only [c.column] using fit (bank+6))
  have oneW : (1:ℕ).size ≤ b := c.one ▸ fit (bank+15)
  have ww : ((enterFalse bank).run τ u).writeWidth ≤ b := by
    simp (disch := decide) [enterFalse,Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,
      Function.update_apply,eq,c.column,c.one,c.pointer,c.mask,coord,ptr,data,ptrW,colW]
    have := c.length
    omega
  have ev := (enterFalse bank).exec τ u b fit ww
  have memory : t = (((u.write (bank+6) k).write (bank+9) addr).write (bank+18) (packed (false::p))).write addr 1 := by
    simp (disch := decide) [t,enterFalse,Structured.sequence,Fragment.run,Op.eval,Store.write,
      Function.update_apply,eq,c.column,c.one,c.pointer,c.mask,coord,ptr,data]
  have frozen (a : ℕ) (ha : a ≠ bank+6 ∧ a ≠ bank+9 ∧ a ≠ bank+18 ∧ a ≠ addr) : t.mem a=u.mem a := by
    simp [memory,Store.write,ha.1,ha.2.1,ha.2.2.1,ha.2.2.2]
  have len := c.length
  refine ⟨ev,⟨by simp; omega,?_,?_,(frozen _ (by dsimp [addr];omega)).trans c.zero,
    (frozen _ (by dsimp [addr];omega)).trans c.one,(frozen _ (by dsimp [addr];omega)).trans c.two,
    (frozen _ (by dsimp [addr];omega)).trans c.residual,?_,?_⟩,by rw [memory];rfl,?_⟩
  · simp (disch := omega) [memory,Store.write,Function.update_apply,eq,low]
  · simp (disch := omega) [memory,Store.write,Function.update_apply,eq,low,addr]
  · simp (disch := omega) [memory,Store.write,Function.update_apply,eq,low]
  · intro i hi
    cases i with
    | zero => simp [memory,Store.write,addr]
    | succ i =>
      have shift : pin+k+(i+1)=pin+(k+1)+i := by omega
      rw [frozen _ (by dsimp [addr];omega),shift]
      exact c.bits i (by simpa using hi)
  · intro a h
    unfold outside at h
    exact frozen a (by dsimp [addr];omega)

theorem useTrue_exec {τ : Tapes} {bank pin n k rank b left : ℕ} (p : List Bool) (u : Store)
    (c : Cursor bank pin n k rank (false::p) u) (count : u.mem 4=left)
    (high : 4 < bank) (sep : bank+20 ≤ pin) (fit : u.Fits b) (room : n+2 ≤ b) :
    let t := ((useTrue bank).run τ u).last
    Exec τ (fun v => v.Fits b) (useTrue bank).cmd u t 3 ∧ Cursor bank pin n k (rank-left) (true::p) t ∧
      t.out=u.out ∧ ∀ a, outside bank pin n a → t.mem a=u.mem a := by
  intro t
  let addr := pin+k
  have low (i : ℕ) (hi : i < 20) : bank+i ≠ addr := by dsimp [addr]; omega
  have eq (i j : ℕ) : (bank+i=bank+j) ↔ i=j := by omega
  have stk : packed (false::p)+1=packed (true::p) := by simp [packed_cons]
  have len := c.length
  simp only [List.length_cons] at len
  have maskW : (packed (true::p)).size ≤ b := by simp;omega
  have rankW : (rank-left).size ≤ b := (Nat.size_le_size (Nat.sub_le rank left)).trans (c.residual ▸ fit (bank+17))
  have twoW : (2:ℕ).size ≤ b := c.two ▸ fit (bank+16)
  have ww : ((useTrue bank).run τ u).writeWidth ≤ b := by
    simp (disch := omega) [useTrue,Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,Function.update_apply,
      eq,c.residual,c.one,c.pointer,c.mask,c.two,count,stk,rankW,twoW]
    omega
  have ev := (useTrue bank).exec τ u b fit ww
  have memory : t=((u.write (bank+17) (rank-left)).write (bank+18) (packed (true::p))).write addr 2 := by
    simp (disch := omega) [t,useTrue,Structured.sequence,Fragment.run,Op.eval,Store.write,Function.update_apply,
      eq,c.residual,c.one,c.pointer,c.mask,c.two,count,stk,addr]
  have frozen (a : ℕ) (ha : a ≠ bank+17 ∧ a ≠ bank+18 ∧ a ≠ addr) : t.mem a=u.mem a := by
    simp [memory,Store.write,ha.1,ha.2.1,ha.2.2]
  refine ⟨ev,⟨by simpa using c.length,(frozen _ (by dsimp [addr];omega)).trans c.column,
    (frozen _ (by dsimp [addr];omega)).trans c.pointer,(frozen _ (by dsimp [addr];omega)).trans c.zero,
    (frozen _ (by dsimp [addr];omega)).trans c.one,(frozen _ (by dsimp [addr];omega)).trans c.two,?_,?_,?_⟩,
    by rw [memory];rfl,?_⟩
  · simp (disch := omega) [memory,Store.write,Function.update_apply,eq,low]
  · simp (disch := omega) [memory,Store.write,Function.update_apply,eq,low]
  · intro i hi
    cases i with
    | zero => simp [memory,Store.write,addr]
    | succ i =>
      rw [frozen _ (by dsimp [addr];omega)]
      exact c.bits (i+1) (by simpa using hi)
  · intro a h
    unfold outside at h
    exact frozen a (by dsimp [addr];omega)

end TargetedSamplers.Structured.RankedPrefix

end LogCostRAMRankCursor

section AffineRAMUnrank

namespace AffinePrefixEnumeration

open EditGV897.Main TargetedSamplers.Structured TargetedSamplers.Structured.RankedPrefix

open BoundedEnumeration

/-- Reconstruct a ranked solution in the public RAM. The count is recomputed for
the zero child. Choosing the other child subtracts that count from the residual
rank, and simultaneously appends its bit to the sparse-table key. -/
theorem walkRank_exec {τ : TargetedSamplers.Tapes} {n : ℕ} (E : List (Equation n))
    (base row pin bank floor b steps span : ℕ) (counter : Cmd)
    (floorLow : 4 < bank) (bankLow : floor ≤ bank) (rowLow : bank+20 ≤ row)
    (endRow : row+(denseWords E).length ≤ pin) (endPin : pin+n ≤ base) (room : n+2 ≤ b)
    (call : ∀ k (p : List Bool) (r : ℕ) (u : Store), Port E base row pin bank u → Cursor bank pin n k r p u →
      u.Fits b → ∃ z j, Exec τ (fun v => v.Fits b) (countPort bank counter) u z j ∧ j ≤ steps ∧
        z.mem 4=affineCount (E++pins n k p) ∧ z.out=u.out ∧
        ∀ a, floor ≤ a → (a < base ∨ base+span ≤ a) → z.mem a=u.mem a)
    (k : ℕ) (p : List Bool) (r : ℕ) (u : Store) (port : Port E base row pin bank u)
    (cur : Cursor bank pin n k r p u) (fit : u.Fits b) :
    ∃ z j rem, Exec τ (fun v => v.Fits b) (walkRank bank counter) u z j ∧ j ≤ k*(steps+10)+1 ∧
      Port E base row pin bank z ∧ Cursor bank pin n 0 rem
        (unrank (fun col pref => affineCount (E++pins n col pref)) k p r) z ∧ z.out=u.out ∧
      ∀ a, floor ≤ a → (a < base ∨ base+span ≤ a) → outside bank pin n a → z.mem a=u.mem a := by
  have ptrSep : bank+20 ≤ pin := by omega
  induction k generalizing p r u with
  | zero =>
    exact ⟨u,1,r,.done (by rw [cur.column,cur.zero]),by simp,port,cur,rfl,fun _ _ _ _ => rfl⟩
  | succ k ih =>
    let v := ((enterFalse bank).run τ u).last
    obtain ⟨desc,atFalse,outV,saveV⟩ := enterFalse_exec (τ := τ) p u cur ptrSep fit room
    have vport : Port E base row pin bank v := port.transport (fun a h => saveV a (by unfold outside;omega))
    obtain ⟨w,j,solve,wj,answer,outW,saveW⟩ := call k (false::p) r v vport atFalse (desc.post fit)
    have wf := solve.post (desc.post fit)
    have wport : Port E base row pin bank w := vport.transport (fun a h => saveW a (by omega) (.inl (by omega)))
    have wc : Cursor bank pin n k r (false::p) w :=
      atFalse.transport (fun a h => saveW a (by omega) (.inl (by omega)))
    let left := affineCount (E++pins n k (false::p))
    let bit := decide (left ≤ r)
    let nextRank := if r < left then r else r-left
    have chosen : ∃ t m, Exec τ (fun s => s.Fits b) (chooseRank bank) w t m ∧ m ≤ 4 ∧
        Port E base row pin bank t ∧ Cursor bank pin n k nextRank (bit::p) t ∧ t.out=w.out ∧
        ∀ a, outside bank pin n a → t.mem a=w.mem a := by
      by_cases inLeft : r < left
      · have no : ¬ (w.mem 4 ≤ w.mem (bank+17)) := by rw [answer,wc.residual];exact Nat.not_le_of_lt inLeft
        exact ⟨w,2,.no no (.skip w),by decide,wport,by simpa [nextRank,bit,inLeft,Nat.not_le_of_lt inLeft] using wc,
          rfl,fun _ _ => rfl⟩
      · have ge : left ≤ r := by omega
        obtain ⟨right,cursor,ret,keep⟩ := useTrue_exec (τ := τ) p w wc answer floorLow ptrSep wf room
        have yes : w.mem 4 ≤ w.mem (bank+17) := by rw [answer,wc.residual];exact ge
        exact ⟨_,4,.yes yes right,by decide,wport.transport (fun a h => keep a (by unfold outside;omega)),
          by simpa [nextRank,bit,inLeft,ge,left] using cursor,ret,keep⟩
    obtain ⟨t,m,pick,wm,pt,ct,outT,saveT⟩ := chosen
    obtain ⟨z,l,rem,walk,wl,pz,cz,ret,keep⟩ := ih (bit::p) nextRank t pt ct (pick.post wf)
    have eq : unrank (fun col pref => affineCount (E++pins n col pref)) (k+1) p r =
        unrank (fun col pref => affineCount (E++pins n col pref)) k (bit::p) nextRank := by
      change (if r < left then _ else _) = _
      by_cases h : r < left
      · rw [if_pos h]
        simp [bit,nextRank,h,Nat.not_le_of_lt h]
      · rw [if_neg h]
        simp [bit,nextRank,h,Nat.le_of_not_gt h] <;> rfl
    refine ⟨z,_,rem,.again (by rw [cur.column,cur.zero];omega) (desc.seq (solve.seq pick)) walk,
      by rw [Nat.succ_mul];omega,pz,by rwa [eq],ret.trans (outT.trans (outW.trans outV)),?_⟩
    intro a low zone free
    exact (keep a low zone free).trans ((saveT a free).trans ((saveW a low zone).trans (saveV a free)))

end AffinePrefixEnumeration

end AffineRAMUnrank

section AffineRAMSolver

namespace AffinePrefixEnumeration

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.RankedPrefix EditGV897.Main

open TargetedSamplers.Structured.BinaryStack

structure Solver.Fits {n : ℕ} (S : Solver) (E : List (Equation n)) (base row pin bank b : ℕ) : Prop where
  bankHigh : S.floor ≤ bank
  afterBank : bank+20 ≤ row
  afterRows : row+(denseWords E).length ≤ pin
  afterPins : pin+n ≤ base
  floorWidth : S.floor.size ≤ b
  wordWidth : n+2 ≤ b
  spaceWidth : (base+S.space (n+(E.length+n))).size ≤ b

theorem Solver.countAll {n : ℕ} (S : Solver) (E : List (Equation n)) {base row pin bank b : ℕ}
    (u : Store) (τ : Tapes) (area : S.Fits E base row pin bank b) (port : Port E base row pin bank u)
    (col : u.mem (bank+6)=n) (ptr : u.mem (bank+9)=pin+n) (fit : u.Fits b) :
    let N := n+(E.length+n)
    ∃ v j, Exec τ (fun t => t.Fits b) (countPort bank S.command) u v j ∧ j ≤ S.work N ∧
      v.mem 4=affineCount E ∧ v.out=u.out ∧ ∀ a, S.floor ≤ a → (a < base ∨ base+S.space N ≤ a) → v.mem a=u.mem a := by
  intro N
  simpa only [pins,List.length_nil,List.ofFn_zero,List.append_nil] using
    S.count n E n [] (by simp) base row pin bank b u τ area.bankHigh area.afterBank area.afterRows
      area.afterPins area.floorWidth area.wordWidth area.spaceWidth port col ptr (by intro i hi;simp at hi) fit

theorem Solver.select {n : ℕ} (S : Solver) (E : List (Equation n)) {base row pin bank b : ℕ} (rank : ℕ)
    (u : Store) (τ : Tapes) (high : 4 < bank) (area : S.Fits E base row pin bank b)
    (port : Port E base row pin bank u) (cur : Cursor bank pin n n rank [] u) (fit : u.Fits b) :
    let N := n+(E.length+n)
    ∃ v j, Exec τ (fun t => t.Fits b) (walkRank bank S.command) u v j ∧ j ≤ n*(S.work N+10)+1 ∧
      v.mem (bank+18)=packed (rankedSolution E rank) ∧ Port E base row pin bank v ∧ v.out=u.out ∧
      ∀ a, S.floor ≤ a → (a < base ∨ base+S.space N ≤ a) → outside bank pin n a → v.mem a=u.mem a := by
  intro N
  have call (k : ℕ) (p : List Bool) (r : ℕ) (v : Store) (pt : Port E base row pin bank v)
      (h : Cursor bank pin n k r p v) (fv : v.Fits b) := S.count n E k p h.length base row pin bank b v τ
    area.bankHigh area.afterBank area.afterRows area.afterPins area.floorWidth area.wordWidth area.spaceWidth
    pt h.column h.pointer (fun i hi => by
      have eq (x : Bool) : 1+x.toNat=bitWord x := by cases x <;> rfl
      exact (h.bits i hi).trans (eq _)) fv
  obtain ⟨v,j,rem,path,bound,preserved,found,out,keep⟩ := walkRank_exec (τ := τ) E base row pin bank
    S.floor b (S.work N) (S.space N) S.command high area.bankHigh area.afterBank area.afterRows area.afterPins
    area.wordWidth call n [] rank u port cur fit
  exact ⟨v,j,path,bound,found.mask,preserved,out,keep⟩

end AffinePrefixEnumeration

end AffineRAMSolver

section HamiltonianRAMAffineCall

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word

open TargetedSamplers.Structured.BinaryStack TargetedSamplers.Structured.RankedPrefix

open AffinePrefixEnumeration EditGV897.Main

private theorem restoreCursor_exec {τ : Tapes} {b : ℕ} (a : ℕ) (u : Store) (zero : u.mem (a+23)=0) (fit : u.Fits b) :
    let v := ((restoreCursor a).run τ u).last
    Exec τ (fun s => s.Fits b) (restoreCursor a).cmd u v 2 ∧ v.mem (a+46)=u.mem (a+12) ∧
      v.mem (a+49)=u.mem (a+50) ∧ v.out=u.out ∧ ∀ x, x ≠ a+46 → x ≠ a+49 → v.mem x=u.mem x := by
  intro v
  have ne (i j : ℕ) (h : i ≠ j) : a+i ≠ a+j := by omega
  have width : ((restoreCursor a).run τ u).writeWidth ≤ b := by
    simp (disch := decide) [restoreCursor,Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,
      Function.update_apply,ne,zero,fit (a+12),fit (a+50)]
  refine ⟨(restoreCursor a).exec τ u b fit width,?_,?_,rfl,?_⟩
  all_goals first
    | intro x p q;simp [v,restoreCursor,Structured.sequence,Fragment.run,Op.eval,Store.write,p,q]
    | simp (disch := decide) [v,restoreCursor,Structured.sequence,Fragment.run,Op.eval,Store.write,Function.update_apply,ne,zero]

private theorem startRank_exec {τ : Tapes} {b : ℕ} (a : ℕ) (u : Store) (zero : u.mem (a+23)=0)
    (fit : u.Fits b) (one : 1 ≤ b) :
    let v := ((startRank a).run τ u).last
    Exec τ (fun s => s.Fits b) (startRank a).cmd u v 2 ∧ v.mem (a+57)=u.mem (a+68) ∧
      v.mem (a+58)=1 ∧ v.out=u.out ∧ ∀ x, x ≠ a+57 → x ≠ a+58 → v.mem x=u.mem x := by
  intro v
  have width : ((startRank a).run τ u).writeWidth ≤ b := by
    simp [startRank,Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,zero,fit (a+68),one]
  refine ⟨(startRank a).exec τ u b fit width,?_,?_,rfl,?_⟩
  all_goals first
    | intro x p q;simp [v,startRank,Structured.sequence,Fragment.run,Op.eval,Store.write,p,q]
    | simp [v,startRank,Structured.sequence,Fragment.run,Op.eval,Store.write,zero]

theorem countPrepared_exec {τ : Tapes} {q b : ℕ} (S : Solver) (E : List (Equation q))
    (bank base row pin : ℕ) (u : Store)
    (area : S.Fits E base row pin (cell bank+40) b) (floor : S.floor ≤ cell bank)
    (port : Port E base row pin (cell bank+40) u) (dim : u.mem (cell bank+12)=q)
    (zero : u.mem (cell bank+23)=0) (fit : u.Fits b) :
    let a := cell bank
    let N := q+(E.length+q)
    a+69 < row →
    ∃ z j, Exec τ (fun v => v.Fits b) (countPrepared bank S.command) u z j ∧ j ≤ S.work N+3 ∧
      z.mem (a+69)=affineCount E ∧ Port E base row pin (a+40) z ∧ z.out=u.out ∧
      ∀ x, S.floor ≤ x → (x < base ∨ base+S.space N ≤ x) → x ≠ a+46 → x ≠ a+49 → x ≠ a+69 → z.mem x=u.mem x := by
  intro a N below
  let y := ((restoreCursor a).run τ u).last
  obtain ⟨restore,col,ptr,ret,frame⟩ := restoreCursor_exec (τ := τ) a u zero fit
  have pr : Port E base row pin (a+40) y := port.transport (fun x hx => frame x (by omega) (by omega))
  obtain ⟨t,k,solve,work,answer,rk,stable⟩ := S.countAll E y τ area pr (col.trans dim) (ptr.trans port.pinEnd) (restore.post fit)
  have afterRows := area.afterRows
  have afterPins := area.afterPins
  have stay (x : ℕ) (hx : S.floor ≤ x) (region : x < base ∨ base+S.space N ≤ x) (h₆ : x ≠ a+46) (h₉ : x ≠ a+49) :=
    (stable x hx region).trans (frame x h₆ h₉)
  have zeroT := (stay (a+23) (by omega) (.inl (by omega)) (by omega) (by omega)).trans zero
  have copy := saveWord_exec (τ := τ) a 69 4 t zeroT (solve.post (restore.post fit))
  let z := t.write (a+69) (t.mem 4)
  have keep (x : ℕ) (hx : S.floor ≤ x) (region : x < base ∨ base+S.space N ≤ x)
      (h₆ : x ≠ a+46) (h₉ : x ≠ a+49) (h : x ≠ a+69) : z.mem x=u.mem x := by
    simpa [z,Store.write,h] using stay x hx region h₆ h₉
  exact ⟨z,_,restore.seq (solve.seq copy),by dsimp [N];omega,by simp [z,Store.write,answer],
    port.transport (fun x hx => keep x (by omega) (.inl (by omega)) (by omega) (by omega) (by omega)),rk.trans ret,keep⟩

theorem rankPrepared_exec {τ : Tapes} {q b : ℕ} (S : Solver) (E : List (Equation q))
    (bank base row pin rank : ℕ) (u : Store) (area : S.Fits E base row pin (cell bank+40) b)
    (floor : S.floor ≤ cell bank) (port : Port E base row pin (cell bank+40) u) (dim : u.mem (cell bank+12)=q)
    (zero : u.mem (cell bank+23)=0) (rankAt : u.mem (cell bank+68)=rank)
    (pause : u.mem (cell bank+54)=0) (unit : u.mem (cell bank+55)=1) (two : u.mem (cell bank+56)=2) (fit : u.Fits b) :
    let a := cell bank
    let N := q+(E.length+q)
    a+69 < row →
    ∃ z j, Exec τ (fun v => v.Fits b) (rankPrepared bank S.command) u z j ∧ j ≤ q*(S.work N+10)+5 ∧
      z.mem (a+58)=packed (rankedSolution E rank) ∧ Port E base row pin (a+40) z ∧ z.out=u.out ∧
      ∀ x, S.floor ≤ x → (x < base ∨ base+S.space N ≤ x) → outside (a+40) pin q x → z.mem x=u.mem x := by
  intro a N below
  let y := ((restoreCursor a).run τ u).last
  obtain ⟨restore,col,ptr,ret,frame⟩ := restoreCursor_exec (τ := τ) a u zero fit
  let v := ((startRank a).run τ y).last
  obtain ⟨load,res,mask,retV,kept⟩ := startRank_exec (τ := τ) a y ((frame _ (by omega) (by omega)).trans zero)
    (restore.post fit) (by have := area.wordWidth;omega)
  have saved (x : ℕ) (h₁ : x ≠ a+46) (h₂ : x ≠ a+49) (h₃ : x ≠ a+57) (h₄ : x ≠ a+58) : v.mem x=u.mem x :=
    (kept x h₃ h₄).trans (frame x h₁ h₂)
  have vp : Port E base row pin (a+40) v :=
    port.transport (fun x hx => saved x (by omega) (by omega) (by omega) (by omega))
  have cur : Cursor (a+40) pin q q rank [] v :=
    ⟨by simp,(kept _ (by omega) (by omega)).trans (col.trans dim),(kept _ (by omega) (by omega)).trans (ptr.trans port.pinEnd),
      (saved _ (by omega) (by omega) (by omega) (by omega)).trans pause,
      (saved _ (by omega) (by omega) (by omega) (by omega)).trans unit,
      (saved _ (by omega) (by omega) (by omega) (by omega)).trans two,res.trans ((frame _ (by omega) (by omega)).trans rankAt),
      mask,by intro i hi;simp at hi⟩
  obtain ⟨z,j,run,work,word,portZ,out,keep⟩ := S.select E rank v τ (by omega) area vp cur (load.post (restore.post fit))
  refine ⟨z,_,restore.seq (load.seq run),by dsimp [N];omega,word,portZ,out.trans (retV.trans ret),?_⟩
  intro x high region free
  exact (keep x high region free).trans (saved x (by unfold outside at free;omega) (by unfold outside at free;omega)
    (by unfold outside at free;omega) (by unfold outside at free;omega))

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMAffineCall

section HamiltonianRankedTrials

namespace DirectedHamiltonicity.Main.Multidigraph

open Classical BoundedEnumeration EditGV897.Main AffinePrefixEnumeration FiniteSampling

open scoped BigOperators

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] {q N : ℕ}

variable (H : Multidigraph V E) (w : E → ℕ) (s t : V) (order : Fin q ≃ Internal s t)

variable (rank : H.NonzeroCoeffs w s t ≃ Fin N) (r : H.RandomMasks w s t)

def trialSize (eqs : Option (List (Equation q))) : ℕ := eqs.elim 0 affineCount

@[simp] theorem wordsByRank_length (eqs : Option (List (Equation q))) : (wordsByRank eqs).length=trialSize eqs := by
  cases eqs <;> simp [wordsByRank,trialSize]

end DirectedHamiltonicity.Main.Multidigraph

end HamiltonianRankedTrials

section HamiltonianRAMTrialProblem

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word

open TargetedSamplers.Structured.BinaryStack AffinePrefixEnumeration EditGV897.Main FiniteSampling Multidigraph

namespace TrialParameters

abbrev row (P : TrialParameters) := rowArea P.bank

abbrev gaussian (P : TrialParameters) := P.a+40

structure Ready (P : TrialParameters) (eqs : Option (List (Equation P.dim))) (u : Store) : Prop where
  count : u.mem (P.a+69)=trialSize eqs
  port : ∀ E, eqs=some E → Port E P.base P.row P.pin P.gaussian u

theorem Ready.writeRank {P : TrialParameters} {eqs : Option (List (Equation P.dim))} {u : Store}
    (s : P.Ready eqs u) (rank : ℕ) : P.Ready eqs (u.write (P.a+68) rank) := by
  have low : P.a+69 < P.row := by simp [row,rowArea,a]
  refine ⟨by simpa [Store.write] using s.count,?_⟩
  intro E e
  exact (s.port E e).transport (fun x hx => by
    have apart : x ≠ P.a+68 := by dsimp only [gaussian] at hx;omega
    simp [Store.write,apart])

theorem denseWords_shape {q : ℕ} (E : List (Equation q)) :
    (denseWords E).length=E.length*(q+1) := by
  have rowLen (r : Equation q) : (rowPayload r).length=q+1 := by simp [rowPayload]
  induction E with
  | nil => simp [denseWords]
  | cons r E ih =>
    change ((r::E).flatMap rowPayload |>.map bitWord).length=_
    rw [List.flatMap_cons,List.map_append,List.length_append,List.length_map,rowLen]
    change (q+1)+(denseWords E).length=_
    rw [ih,List.length_cons,Nat.succ_mul,Nat.add_comm]

theorem Space.area {P : TrialParameters} {S : Solver} {floor b : ℕ}
    (s : P.Space S floor b) (E : List (Equation P.dim)) (len : E.length=P.dim) :
    S.Fits E P.base P.row P.pin P.gaussian b := by
  refine ⟨by have := s.floorSolve;dsimp [gaussian];omega,by simp [gaussian,row,rowArea,a],?_,?_,
    s.floorWidth,s.kernelWidth,by simpa only [len] using s.solverWidth⟩
  · rw [denseWords_shape,len];rfl
  · rfl

theorem seen_above {P : TrialParameters} {S : Solver} {floor b : ℕ}
    (s : P.Space S floor b) : P.a+69 < P.seenBase := by
  have region := s.table
  dsimp [base,solverArea,pinArea,rowArea,a] at region ⊢
  omega

end TrialParameters

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMTrialProblem

section HamiltonianRAMTrialCount

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word AffinePrefixEnumeration

open EditGV897.Main Multidigraph

private theorem startRows_exec {τ : Tapes} {b : ℕ} (a : ℕ) (u : Store) (zero : u.mem (a+23)=0)
    (fit : u.Fits b) (hb : 2 ≤ b) :
    let v := ((startRows a).run τ u).last
    Exec τ (fun s => s.Fits b) (startRows a).cmd u v 2 ∧ v.mem (a+8)=2 ∧ v.mem (a+34)=u.mem (a+52) ∧ v.out=u.out ∧
      ∀ x, x ≠ a+8 → x ≠ a+34 → v.mem x=u.mem x := by
  intro v
  have width : ((startRows a).run τ u).writeWidth ≤ b := by
    simp [startRows,Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,zero,fit (a+52),
      show (2:ℕ).size ≤ b from (by decide : (2:ℕ).size ≤ 2).trans hb]
  refine ⟨(startRows a).exec τ u b fit width,?_,?_,rfl,?_⟩
  all_goals first
    | intro x p q;simp [v,startRows,Structured.sequence,Fragment.run,Op.eval,Store.write,p,q]
    | simp [v,startRows,Structured.sequence,Fragment.run,Op.eval,Store.write,zero]

namespace TrialParameters

abbrev countRegister (i : ℕ) : Prop := trialRegister i ∨ i=22 ∨ i=65 ∨ i=68

private structure CountFrame (P : TrialParameters) (u v : Store) : Prop where
  fixed : ∀ i, countRegister i → v.mem (P.a+i)=u.mem (P.a+i)
  heap : ∀ x ≥ P.seenBase, v.mem x=u.mem x

private theorem CountFrame.trans {P : TrialParameters} {u v y : Store} (a : CountFrame P u v) (b : CountFrame P v y) :
    CountFrame P u y := ⟨fun i hi => (b.fixed i hi).trans (a.fixed i hi),fun x hx => (b.heap x hx).trans (a.heap x hx)⟩

private theorem CountFrame.keeps {P : TrialParameters} {u v : Store} {f : List Bool → ZMod 2} {seen : Finset (List Bool)}
    (h : CountFrame P u v) (start : P.invariant f seen u) : P.invariant f seen v :=
  start.preserve (fun i hi => h.fixed i (hi.elim Or.inl (fun e => Or.inr (.inl e)))) h.heap

theorem prepare_trial {τ : Tapes} {b floor cost : ℕ} (P : TrialParameters) (S : Solver) (kernel : Cmd)
    (eqs : ℕ → Option (List (Equation P.dim))) (f : List Bool → ZMod 2)
    (space : P.Space S floor b) (oracle : P.Queries τ b floor cost kernel eqs f)
    (i : ℕ) (within : i < P.trials) (seen : Finset (List Bool)) (u : Store)
    (start : P.invariant f seen u) (cursor : u.mem (P.a+65)=i) (fit : u.Fits b) :
    ∃ z j, Exec τ (fun y => y.Fits b) (countTrial P.bank kernel S.command) u z j ∧ j ≤ P.countCost S b cost ∧
      P.invariant f seen z ∧ P.Ready (eqs i) z ∧ z.mem (P.a+65)=i ∧ z.mem (P.a+68)=u.mem (P.a+68) ∧ z.out=u.out := by
  have low : 14 ≤ P.a := by simp [a,cell]
  have upper := seen_above space
  have rowLow : P.a+69 < P.row := by dsimp [a,row,rowArea];omega
  have pinRow : P.row ≤ P.pin := by dsimp [row,pin,pinArea];omega
  have basePin : P.pin ≤ P.base := by dsimp [pin,base,solverArea];omega
  have high := space.table
  have floorQ := space.floorQuery
  have floorS := space.floorSolve
  obtain ⟨v,j,read,runtime,keyAt,outV,frame⟩ := readTrial_exec (τ := τ) P.bank P.maskLength (Nat.clog 2 P.card) i u
    start.layout.masks start.layout.coinWidth cursor start.layout.zero fit space.two space.trialWidth (space.seekWidth i within)
  change v.mem (P.a+6)=P.key τ i at keyAt
  change ∀ x, 14 ≤ x → x ≠ P.a+6 → (x < P.a+30 ∨ P.a+34 < x) → v.mem x=u.mem x at frame
  have f₀ : CountFrame P u v := by
    constructor
    · intro r hr
      dsimp only [countRegister,trialRegister] at hr
      exact frame (P.a+r) (by omega) (by omega) (by omega)
    · intro x hx
      exact frame x (by omega) (by omega) (by omega)
  have readyV := f₀.keeps start
  have cardAt := readyV.layout.choices
  have work₀ : j ≤ 4*(b*(5*b+9)+15)+9*Nat.clog 2 P.card+3 := runtime
  by_cases pad : P.card ≤ P.key τ i
  · let z := v.write (P.a+69) 0
    have set : Exec τ (fun y => y.Fits b) (.op (.const (P.a+69) 0)) v z 1 :=
      .op _ _ (Store.write_fits (read.post fit) _ (by simp))
    have cmp : v.mem (P.a+14) ≤ v.mem (P.a+6) := by rwa [cardAt,keyAt]
    have after : CountFrame P v z := ⟨fun k hk => by
        have other : P.a+k ≠ P.a+69 := by unfold countRegister trialRegister at hk;omega
        exact Function.update_of_ne other _ _,fun x hx => by
        exact Function.update_of_ne (by omega : x ≠ P.a+69) _ _⟩
    have endFrame := f₀.trans after
    have no := oracle.padding i within pad
    have done : P.Ready (eqs i) z := ⟨by simp [no,trialSize,z,Store.write],by intro E e;rw [no] at e;contradiction⟩
    exact ⟨z,_,read.seq (.yes cmp set),by unfold countCost;omega,endFrame.keeps start,done,
      (endFrame.fixed 65 (by decide)).trans cursor,endFrame.fixed 68 (by decide),outV⟩
  · obtain ⟨E,eq,shape,ask⟩ := oracle.valid i within (Nat.lt_of_not_ge pad)
    have len := (denseWords_shape E).trans (congrArg (·*(P.dim+1)) shape)
    have cmp : ¬v.mem (P.a+14) ≤ v.mem (P.a+6) := by rwa [cardAt,keyAt]
    let y := ((startRows P.a).run τ v).last
    obtain ⟨prep,mode,ptr,outY,keep⟩ := startRows_exec (τ := τ) P.a v readyV.layout.zero (read.post fit) space.two
    have f₁ : CountFrame P v y := by
      constructor
      · intro r hr
        dsimp only [countRegister,trialRegister] at hr
        exact keep (P.a+r) (by omega) (by omega)
      · intro x hx
        exact keep x (by omega) (by omega)
    have readyY := f₁.keeps readyV
    have lay := readyY.layout
    obtain ⟨t,l,fill,wl,port,ret,retain⟩ := rowQueries_exec (τ := τ) E P.bank P.vertices P.weights P.source P.sink P.graph
      P.fieldWidth P.mask (P.key τ i) floor cost kernel y lay.header lay.maskAt ((keep (P.a+6) (by omega) (by omega)).trans keyAt)
      mode floorQ len shape lay.baseAt lay.columns lay.pinEnd lay.rows lay.first lay.after (ptr.trans readyV.layout.first)
      lay.one ask space.rowWidth (prep.post (read.post fit))
    change ∀ x, floor ≤ x → x ≠ P.a+7 → x ≠ P.a+34 → (x < P.row ∨ P.pin ≤ x) → t.mem x=y.mem x at retain
    have f₂ : CountFrame P y t := by
      constructor
      · intro r hr
        dsimp only [countRegister,trialRegister] at hr
        exact retain (P.a+r) (by omega) (by omega) (by omega) (.inl (by omega))
      · intro x hx
        exact retain x (by omega) (by omega) (by omega) (.inr (by omega))
    have readyT := f₂.keeps readyY
    obtain ⟨z,r,solve,wr,answer,pt,outZ,stable⟩ := countPrepared_exec (τ := τ) S E P.bank P.base P.row P.pin t
      (space.area E shape) floorS port readyT.layout.dim readyT.layout.zero (fill.post (prep.post (read.post fit))) rowLow
    simp only [shape] at wr stable
    change ∀ x, S.floor ≤ x → (x < P.base ∨ P.base+S.space P.N ≤ x) → x ≠ P.a+46 → x ≠ P.a+49 →
      x ≠ P.a+69 → z.mem x=t.mem x at stable
    have f₃ : CountFrame P t z := by
      constructor
      · intro r hr
        dsimp only [countRegister,trialRegister] at hr
        exact stable (P.a+r) (by omega) (.inl (by omega)) (by omega) (by omega) (by omega)
      · intro x hx
        exact stable x (by omega) (.inr (high.trans hx)) (by omega) (by omega) (by omega)
    have all := ((f₀.trans f₁).trans f₂).trans f₃
    have done : P.Ready (eqs i) z := ⟨by simpa only [eq,trialSize,Option.elim] using answer,by
      intro F h;have same := Option.some.inj (eq.symm.trans h);subst F;exact pt⟩
    refine ⟨z,_,read.seq (.no cmp (prep.seq (fill.seq solve))),?_,all.keeps start,done,
      (all.fixed 65 (by decide)).trans cursor,all.fixed 68 (by decide),outZ.trans (ret.trans (outY.trans outV))⟩
    dsimp only [countCost,N]
    omega

end TrialParameters

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMTrialCount

section LogCostRAMReportedCounts

namespace TargetedSamplers.Structured

theorem prefixReports_mono (reports : ℕ → ℕ) : Monotone (prefixReports reports) := by
  apply monotone_nat_of_le_succ
  intro j;change _ ≤ prefixReports reports j+reports j;omega

theorem scanCounts_exec {τ : TargetedSamplers.Tapes} {b : ℕ} (r : Fin 5 ↪ ℕ) (query : Cmd) (M qcost : ℕ)
    (reports : ℕ → ℕ) (K : Store → Prop)
    (stable : ∀ u, K u → ∀ a v, a=r 0 ∨ a=r 3 → K (u.write a v))
    (control : ∀ u, K u → u.mem (r 1)=M ∧ u.mem (r 2)=1)
    (step : ∀ i < M, ∀ u, K u → u.mem (r 0)=i → u.Fits b →
      ∃ t j, Exec τ (fun v => v.Fits b) query u t j ∧ j ≤ qcost ∧ K t ∧ t.mem (r 0)=i ∧
        t.mem (r 4)=reports i ∧ t.mem (r 3)=u.mem (r 3) ∧ t.out=u.out)
    (bounds : M.size ≤ b ∧ (prefixReports reports M).size ≤ b) (s : Store) (inv : K s)
    (cursor : s.mem (r 0)=0) (total : s.mem (r 3)=0) (fit : s.Fits b) :
    ∃ t j, Exec τ (fun v => v.Fits b) (scanCounts r query) s t j ∧ j ≤ M*(qcost+4)+1 ∧
      K t ∧ t.mem (r 0)=M ∧ t.mem (r 3)=prefixReports reports M ∧ t.out=s.out := by
  let state (i : ℕ) (u : Store) := K u ∧ u.mem (r 0)=i ∧ u.mem (r 3)=prefixReports reports i ∧ u.out=s.out
  have limit (i : ℕ) (_ : i ≤ M) (u : Store) (h : state i u) :
      u.mem (r 0)=0+i ∧ u.mem (r 1)=0+M := by simpa only [Nat.zero_add] using And.intro h.2.1 (control u h.1).1
  have neq {i j : Fin 5} (h : i ≠ j) : r i ≠ r j := r.injective.ne h
  have body (i : ℕ) (hi : i < M) (u : Store) (h : state i u) (fu : u.Fits b) :
      ∃ v j, Exec τ (fun st => st.Fits b) (.seq query (.op (.add (r 3) (r 3) (r 4)))) u v j ∧ j ≤ qcost+1 ∧
        v.mem (r 0)=0+i ∧ v.mem (r 2)=1 ∧ state (i+1) (v.write (r 0) (0+i+1)) := by
    obtain ⟨t,j,call,work,kt,atI,value,old,out⟩ := step i hi u h.1 h.2.1 fu
    let p := prefixReports reports (i+1)
    have width : p.size ≤ b := (Nat.size_le_size (prefixReports_mono reports (Nat.succ_le_of_lt hi))).trans bounds.2
    let v := t.write (r 3) p
    have ev : (Op.add (r 3) (r 3) (r 4)).eval τ t=v := by
      simp [Op.eval,p,v,prefixReports,old,h.2.2.1,value]
    have fv : v.Fits b := Store.write_fits (call.post fu) _ width
    have add : Exec τ (fun st => st.Fits b) (.op (.add (r 3) (r 3) (r 4))) t v 1 := by
      simpa only [ev] using Exec.op (τ := τ) (inv := fun st => st.Fits b) t (.add (r 3) (r 3) (r 4)) (ev ▸ fv)
    have kv : K v := stable t kt _ _ (.inr rfl)
    refine ⟨v,_,call.seq add,by omega,?_,(control v kv).2,stable v kv _ _ (.inl rfl),?_,?_,out.trans h.2.2.2⟩
    · simp [v,Store.write,neq (by decide : (0:Fin 5) ≠ 3),atI]
    · simp [Store.write]
    · simp [Store.write,v,neq (by decide : (3:Fin 5) ≠ 0),p]
  obtain ⟨t,j,run,work,post⟩ := forRange_exec (τ := τ) (r 0) (r 1) (r 2) 0 M (qcost+1) _ state limit body
    (by simpa using bounds.1) s ⟨inv,cursor,total,rfl⟩ fit
  exact ⟨t,j,run,by simpa only [Nat.add_assoc] using work,post⟩

end TargetedSamplers.Structured

end LogCostRAMReportedCounts

section LogCostRAMReportedWords

namespace TargetedSamplers.Structured

theorem scanReportedWords_exec {X : Type*} {τ : TargetedSamplers.Tapes} {b : ℕ}
    (r : Fin 5 ↪ ℕ) (query visit : Cmd) (M queryCost visitCost : ℕ)
    (reports : ℕ → ℕ) (advance : ℕ → ℕ → X → X) (K : X → Store → Prop) (Ready : ℕ → Store → Prop)
    (stable : ∀ x u, K x u → ∀ a v, a=r 0 ∨ a=r 3 → K x (u.write a v))
    (readyRank : ∀ i u, Ready i u → ∀ v, Ready i (u.write (r 3) v))
    (control : ∀ x u, K x u → u.mem (r 1)=M ∧ u.mem (r 2)=1)
    (count : ∀ i u, Ready i u → u.mem (r 4)=reports i)
    (prepare : ∀ i < M, ∀ x u, K x u → u.mem (r 0)=i → u.Fits b →
      ∃ v k, Exec τ (fun t => t.Fits b) query u v k ∧ k ≤ queryCost ∧ K x v ∧ Ready i v ∧ v.mem (r 0)=i ∧ v.out=u.out)
    (emit : ∀ i < M, ∀ j < reports i, ∀ x u, K x u → Ready i u → u.mem (r 0)=i → u.mem (r 3)=j → u.Fits b →
      ∃ v k, Exec τ (fun t => t.Fits b) visit u v k ∧ k ≤ visitCost ∧ K (advance i j x) v ∧
        Ready i v ∧ v.mem (r 0)=i ∧ v.mem (r 3)=j ∧ v.out=u.out)
    (width : M.size ≤ b) (start : X) (s : Store) (initial : K start s) (cursor : s.mem (r 0)=0) (fit : s.Fits b) :
    let acc := fun i => applyPrefix (fun j => applyPrefix (advance j) (reports j)) i start
    ∃ t k, Exec τ (fun v => v.Fits b) (scanReportedWords r query visit) s t k ∧
      k ≤ M*(queryCost+5)+prefixReports reports M*(visitCost+3)+1 ∧ K (acc M) t ∧ t.mem (r 0)=M ∧ t.out=s.out := by
  intro acc
  let state (i : ℕ) (v : Store) := K (acc i) v ∧ v.mem (r 0)=i ∧ v.out=s.out
  have dif {i j : Fin 5} (h : i ≠ j) : r i ≠ r j := r.injective.ne h
  have body (i : ℕ) (hi : i < M) (u : Store) (h : state i u) (fu : u.Fits b) :
      ∃ v k, Exec τ (fun t => t.Fits b) (.seq query (.seq (.op (.const (r 3) 0)) (forRange (r 3) (r 4) (r 2) visit))) u v k ∧
        k ≤ (queryCost+2)+reports i*(visitCost+3) ∧ v.mem (r 0)=i ∧ v.mem (r 2)=1 ∧ state (i+1) (v.write (r 0) (i+1)) := by
    obtain ⟨v,j,call,used,kv,ready,ptr,out⟩ := prepare i hi (acc i) u h.1 h.2.1 fu
    let v' := v.write (r 3) 0
    have fv' : v'.Fits b := Store.write_fits (call.post fu) _ (by simp)
    have init : Exec τ (fun t => t.Fits b) (.op (.const (r 3) 0)) v v' 1 := Exec.op _ _ fv'
    let inner (j : ℕ) (z : Store) := K (applyPrefix (advance i) j (acc i)) z ∧ Ready i z ∧
      z.mem (r 0)=i ∧ z.mem (r 3)=j ∧ z.out=u.out
    have bounds (j : ℕ) (_ : j ≤ reports i) (z : Store) (q : inner j z) :
        z.mem (r 3)=0+j ∧ z.mem (r 4)=0+reports i := by simpa only [Nat.zero_add] using And.intro q.2.2.2.1 (count i z q.2.1)
    have oneStep (j : ℕ) (hj : j < reports i) (z : Store) (q : inner j z) (fz : z.Fits b) :
        ∃ y k, Exec τ (fun t => t.Fits b) visit z y k ∧ k ≤ visitCost ∧ y.mem (r 3)=0+j ∧ y.mem (r 2)=1 ∧
          inner (j+1) (y.write (r 3) (0+j+1)) := by
      obtain ⟨y,k,ex,cost,ky,ry,atI,atJ,ret⟩ := emit i hi j hj _ z q.1 q.2.1 q.2.2.1 q.2.2.2.1 fz
      refine ⟨y,k,ex,cost,by simpa using atJ,(control _ y ky).2,stable _ y ky _ _ (.inr rfl),
        readyRank i y ry _,?_,?_,ret.trans q.2.2.2.2⟩
      · simp [Store.write,dif (by decide : (0:Fin 5) ≠ 3),atI]
      · simp [Store.write]
    have first : inner 0 v' := ⟨stable _ v kv _ _ (.inr rfl),readyRank i v ready _,
      by simp [v',Store.write,dif (by decide : (0:Fin 5) ≠ 3),ptr],by simp [v',Store.write],out⟩
    have size : (reports i).size ≤ b := count i v ready ▸ (call.post fu) (r 4)
    obtain ⟨y,k,walk,work,endAt⟩ := forRange_exec (τ := τ) (r 3) (r 4) (r 2) 0 (reports i) visitCost visit
      inner bounds oneStep (by simpa using size) v' first fv'
    refine ⟨y,_,call.seq (init.seq walk),by omega,endAt.2.2.1,(control _ y endAt.1).2,
      stable _ y endAt.1 _ _ (.inl rfl),by simp [Store.write],endAt.2.2.2.2.trans h.2.2⟩
  obtain ⟨z,k,run,work,post⟩ := forRange_exec_reported (τ := τ) (r 0) (r 1) (r 2) M (queryCost+2) (visitCost+3)
    reports _ state (fun i _ u h => ⟨h.2.1,(control _ u h.1).1⟩) body width s ⟨initial,cursor,rfl⟩ fit
  exact ⟨z,k,run,by simpa only [Nat.add_assoc] using work,post⟩

end TargetedSamplers.Structured

end LogCostRAMReportedWords

section LogCostRAMCappedReports

namespace TargetedSamplers.Structured

theorem cappedReports_exec {X : Type*} {τ : TargetedSamplers.Tapes} {b : ℕ}
    (r : Fin 5 ↪ ℕ) (cap zero result : ℕ) (query visit : Cmd) (M queryCost visitCost : ℕ)
    (reports : ℕ → ℕ) (advance : ℕ → ℕ → X → X) (bit : X → Bool) (K : X → Store → Prop) (Ready : ℕ → Store → Prop)
    (stable : ∀ x u, K x u → ∀ a v, a=r 0 ∨ a=r 3 → K x (u.write a v))
    (readyRank : ∀ i u, Ready i u → ∀ v, Ready i (u.write (r 3) v))
    (control : ∀ x u, K x u → u.mem (r 1)=M ∧ u.mem (r 2)=1 ∧ u.mem cap=12*M ∧ u.mem zero=0 ∧
      (u.mem result != 0)=bit x)
    (count : ∀ i u, Ready i u → u.mem (r 4)=reports i)
    (prepare : ∀ i < M, ∀ x u, K x u → u.mem (r 0)=i → u.Fits b →
      ∃ v k, Exec τ (fun t => t.Fits b) query u v k ∧ k ≤ queryCost ∧ K x v ∧ Ready i v ∧ v.mem (r 0)=i ∧
        v.mem (r 3)=u.mem (r 3) ∧ v.out=u.out)
    (emit : ∀ i < M, ∀ j < reports i, ∀ x u, K x u → Ready i u → u.mem (r 0)=i → u.mem (r 3)=j → u.Fits b →
      ∃ v k, Exec τ (fun t => t.Fits b) visit u v k ∧ k ≤ visitCost ∧ K (advance i j x) v ∧
        Ready i v ∧ v.mem (r 0)=i ∧ v.mem (r 3)=j ∧ v.out=u.out)
    (width : M.size ≤ b ∧ (prefixReports reports M).size ≤ b) (start : X) (s : Store) (initial : K start s)
    (cursor : s.mem (r 0)=0) (total : s.mem (r 3)=0) (fit : s.Fits b) :
    let finish := applyPrefix (fun i => applyPrefix (advance i) (reports i)) M start
    ∃ t k, Exec τ (fun v => v.Fits b) (cappedReports r cap zero result query visit) s t k ∧
      k ≤ M*((queryCost+4)+(queryCost+5)+12*(visitCost+3))+5 ∧
      t.out=s.out++[if prefixReports reports M ≤ 12*M then bit finish else false] := by
  intro finish
  have ctrl (x u) (h : K x u) := And.intro (control x u h).1 (control x u h).2.1
  obtain ⟨u,j,first,wj,ku,atEnd,sum,out⟩ := scanCounts_exec (τ := τ) r query M queryCost reports (K start)
    (stable start) (ctrl start) (fun i hi v h pos f => by
      obtain ⟨z,k,run,work,kz,ready,ptr,keep,ret⟩ := prepare i hi start v h pos f
      exact ⟨z,k,run,work,kz,ptr,count i z ready,keep,ret⟩) width s initial cursor total fit
  have fu := first.post fit
  have limits := control start u ku
  have budget : M*((queryCost+4)+(queryCost+5)+12*(visitCost+3))=
      M*(queryCost+4)+M*(queryCost+5)+(12*M)*(visitCost+3) := by ring
  by_cases safe : prefixReports reports M ≤ 12*M
  · let v := u.write (r 0) 0
    have fv : v.Fits b := Store.write_fits fu _ (by simp)
    have reset : Exec τ (fun t => t.Fits b) (.op (.const (r 0) 0)) u v 1 := Exec.op _ _ fv
    obtain ⟨y,k,second,wk,ky,_,ret⟩ := scanReportedWords_exec (τ := τ) r query visit M queryCost visitCost
      reports advance K Ready stable readyRank ctrl count (fun i hi x u h pos f => by
        obtain ⟨z,k,run,work,kz,ready,ptr,_,ret⟩ := prepare i hi x u h pos f
        exact ⟨z,k,run,work,kz,ready,ptr,ret⟩) emit width.1 start v (stable start u ku _ _ (.inl rfl))
      (by simp [v,Store.write]) fv
    have last := Exec.op (τ := τ) (inv := fun t => t.Fits b) y (.output result) (second.post fv)
    have cmp : u.mem (r 3) ≤ u.mem cap := by rwa [sum,limits.2.2.1]
    refine ⟨_,_,first.seq (.yes cmp (reset.seq (second.seq last))),?_,?_⟩
    · have bound := Nat.mul_le_mul_right (visitCost+3) safe
      rw [budget];omega
    · simp only [if_pos safe,Op.eval,(control finish y ky).2.2.2.2,ret]
      exact congrArg (·++[bit finish]) out
  · have last := Exec.op (τ := τ) (inv := fun t => t.Fits b) u (.output zero) fu
    have cmp : ¬u.mem (r 3) ≤ u.mem cap := by rwa [sum,limits.2.2.1]
    exact ⟨_,_,first.seq (.no cmp last),by rw [budget];omega,by simp [Op.eval,limits.2.2.2.1,safe,out]⟩

end TargetedSamplers.Structured

end LogCostRAMCappedReports

section HamiltonianRAMTrialVisit

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word TargetedSamplers.Structured.BinaryStack

open TargetedSamplers.Structured.RankedPrefix AffinePrefixEnumeration EditGV897.Main Multidigraph BoundedEnumeration

private theorem unrank_length (count : ℕ → List Bool → ℕ) (n : ℕ) (p : List Bool) (i : ℕ) :
    (unrank count n p i).length=n+p.length := by
  induction n generalizing p i with
  | zero => simp [unrank]
  | succ n ih =>
    rw [unrank];split <;> rw [ih,List.length_cons] <;> omega

namespace TrialParameters

theorem emit_trial {τ : Tapes} {b floor cost : ℕ} (P : TrialParameters) (S : Solver) (kernel : Cmd)
    (eqs : ℕ → Option (List (Equation P.dim))) (f : List Bool → ZMod 2)
    (space : P.Space S floor b) (oracle : P.Queries τ b floor cost kernel eqs f)
    (i j : ℕ) (within : i < P.trials) (has : j < trialSize (eqs i)) (seen : Finset (List Bool)) (u : Store)
    (start : P.invariant f seen u) (ready : P.Ready (eqs i) u) (trial : u.mem (P.a+65)=i)
    (rank : u.mem (P.a+68)=j) (fit : u.Fits b) :
    ∃ z k, Exec τ (fun y => y.Fits b) (visitRank P.bank kernel S.command) u z k ∧ k ≤ P.visitCost S cost ∧
      P.invariant f (insertAt (wordsByRank (eqs i)) j seen) z ∧ P.Ready (eqs i) z ∧
      z.mem (P.a+65)=i ∧ z.mem (P.a+68)=j ∧ z.out=u.out := by
  have valid : P.key τ i < P.card := by
    by_contra bad
    have no := oracle.padding i within (Nat.le_of_not_gt bad)
    simp [no,trialSize] at has
  obtain ⟨E,eq,shape,_⟩ := oracle.valid i within valid
  have pos : j < affineCount E := by simpa only [eq,trialSize,Option.elim] using has
  let xs := rankedSolution E j
  have len : xs.length=P.dim := by
    simpa only [xs,rankedSolution,List.length_nil,Nat.add_zero] using
      (unrank_length (fun k p => affineCount (E++pins P.dim k p)) P.dim [] j)
  have leafSet : insertAt (wordsByRank (eqs i)) j seen=insert xs seen := by
    rw [eq];simp [insertAt,wordsByRank,List.getElem?_eq_getElem, pos,xs]
  have rowLow : P.a+69 < P.row := by dsimp [a,row,rowArea];omega
  have rowPin : P.row ≤ P.pin := by dsimp [row,pin,pinArea];omega
  have endPin : P.pin+P.dim=P.base := rfl
  have baseSeen := space.table
  let L := start.layout
  obtain ⟨v,k,walk,w,found,port,ret,frame⟩ := rankPrepared_exec (τ := τ) S E P.bank P.base P.row P.pin j u
    (space.area E shape) space.floorSolve (ready.port E eq) L.dim L.zero rank L.pause L.unit L.two fit rowLow
  simp only [shape] at frame w
  change ∀ x, S.floor ≤ x → (x < P.base ∨ P.base+S.space P.N ≤ x) → outside (P.a+40) P.pin P.dim x →
    v.mem x=u.mem x at frame
  have solverFloor := space.floorSolve
  have queryFloor := space.floorQuery
  have far := seen_above space
  have fixed (r : ℕ) (h : trialRegister r ∨ r=22 ∨ r=65 ∨ r=68 ∨ r=69) : v.mem (P.a+r)=u.mem (P.a+r) := by
    unfold trialRegister at h
    exact frame _ (by omega) (.inl (by omega)) (by unfold outside;omega)
  have heap (x : ℕ) (hx : P.seenBase ≤ x) : v.mem x=u.mem x :=
    frame x (by omega) (.inr (baseSeen.trans hx)) (by unfold outside;omega)
  have sv : P.invariant f seen v := start.preserve
    (fun r h => fixed r (h.elim Or.inl (fun e => Or.inr (.inl e)))) heap
  have callback (y : Store) (key : y.mem (P.a+6)=packed xs) (tgt : y.mem (P.a+7)=P.target) (mode : y.mem (P.a+8)=3)
      (kept : ∀ x, floor ≤ x → x ≠ P.a+6 → x ≠ P.a+7 → x ≠ P.a+8 → x ≠ P.a+33 → x ≠ P.a+34 → x ≠ P.seenBase+packed xs → y.mem x=v.mem x)
      (fy : y.Fits b) := oracle.leaf xs len y (sv.layout.header.transport (fun x hx => by
        change (P.a ≤ x ∧ x < P.a+5) ∨ x=P.a+9 at hx
        exact kept x (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)))
        ⟨(kept (P.a+5) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans sv.layout.maskAt,
          key,tgt,mode⟩ fy
  obtain ⟨z,l,visit,wl,marked,parity,out,keep⟩ := visitWord_exec (τ := τ) P.a floor P.seenBase P.target cost kernel f
    seen xs v len (walk.post fit) space.two queryFloor (by omega) sv.layout.seenAt found sv.layout.target
      sv.layout.zero sv.layout.one sv.parity sv.flags (space.seenWidth xs len) callback
  have keepReg (r : ℕ) (hr : trialRegister r ∨ r=65 ∨ r=68 ∨ r=69) : z.mem (P.a+r)=v.mem (P.a+r) := by
    unfold trialRegister at hr
    apply keep <;> omega
  have sz : P.invariant f (insert xs seen) z :=
    ⟨sv.layout.transport (fun r h => keepReg r (.inl h)),marked,parity⟩
  have dataEnd : P.row+(denseWords E).length=P.pin := by rw [denseWords_shape,shape];rfl
  have pz : Port E P.base P.row P.pin P.gaussian z := port.transport (fun x hx => by
    simp only [a,row,pin,base,gaussian] at *
    apply keep <;> omega)
  have rz : P.Ready (eqs i) z := ⟨(keepReg 69 (by decide)).trans ((fixed 69 (by decide)).trans ready.count),by
    intro F h;have same := Option.some.inj (eq.symm.trans h);subst F;exact pz⟩
  rw [leafSet]
  exact ⟨z,_,walk.seq visit,by dsimp only [visitCost,N];omega,sz,rz,
    (keepReg 65 (by decide)).trans ((fixed 65 (by decide)).trans trial),
    (keepReg 68 (by decide)).trans ((fixed 68 (by decide)).trans rank),out.trans ret⟩

end TrialParameters

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMTrialVisit

section HamiltonianRAMReportWidth

namespace DirectedHamiltonicity.Main.Multidigraph

open EditGV897.Main AffinePrefixEnumeration TargetedSamplers.Structured TargetedSamplers.Structured.Word

theorem totalReportWidth {q : ℕ} (reports : ℕ → Option (List (Equation q))) (M : ℕ) :
    (prefixReports (fun i => trialSize (reports i)) M).size ≤ M.size+q+1 := by
  have each (i : ℕ) : trialSize (reports i) ≤ 2^q := by
    cases e : reports i with
    | none => simp [trialSize]
    | some E =>
      change affineCount E ≤ 2^q
      rw [affine_count_correct]
      simpa [EditGV897.Main.Word] using Finset.card_le_univ (affineSet E)
  have total (j : ℕ) : prefixReports (fun i => trialSize (reports i)) j ≤ j*2^q := by
    induction j with
    | zero => simp [prefixReports]
    | succ j ih => rw [prefixReports,Nat.succ_mul];exact Nat.add_le_add ih (each j)
  have bound := (Nat.size_le_size (total M)).trans (size_mul_le_add M (2^q))
  simpa only [Nat.size_pow,Nat.add_assoc] using bound

end DirectedHamiltonicity.Main.Multidigraph

end HamiltonianRAMReportWidth

section
open DirectedHamiltonicity DirectedHamiltonicity.Main DirectedHamiltonicity.Main.InputRAM
open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word
open AffinePrefixEnumeration EditGV897.Main Multidigraph
open scoped BigOperators
open DirectedHamiltonicity DirectedHamiltonicity.Main DirectedHamiltonicity.Main.InputRAM DirectedHamiltonicity.Main.InputRAM.TrialParameters

theorem solution {τ : Tapes} {b floor cost : ℕ} (P : TrialParameters) (S : Solver) (kernel : Cmd)
    (eqs : ℕ → Option (List (Equation P.dim))) (f : List Bool → ZMod 2)
    (space : P.Space S floor b) (oracle : P.Queries τ b floor cost kernel eqs f) (u : Store)
    (initial : P.invariant f ∅ u) (trial : u.mem (P.a+65)=0) (total : u.mem (P.a+68)=0) (fit : u.Fits b) :
    let p := P.countCost S b cost
    let v := P.visitCost S cost
    ∃ z k, Exec τ (fun y => y.Fits b) (runTrials P.bank kernel S.command) u z k ∧
      k ≤ P.trials*((p+4)+(p+5)+12*(v+3))+5 ∧ z.out=u.out++[P.estimate eqs f] := by
  intro p v
  let r := window (P.a+65) 5
  let count := fun i => trialSize (eqs i)
  let advance := fun i => insertAt (wordsByRank (eqs i))
  have rb (s : Store) (x : Finset (List Bool)) (k : P.invariant f x s) :
      s.mem (r 1)=P.trials ∧ s.mem (r 2)=1 ∧ s.mem (P.a+19)=12*P.trials ∧ s.mem (P.a+23)=0 ∧
        (s.mem (P.a+22) != 0)=emits f x := by
    refine ⟨k.layout.limit,k.layout.stride,k.layout.cap,k.layout.zero,?_⟩
    rw [k.parity];change ((emits f x).toNat != 0)=emits f x;cases emits f x <;> rfl
  have size : P.trials.size ≤ b ∧ (prefixReports count P.trials).size ≤ b := by
    have room := space.countWidth
    exact ⟨by omega,(totalReportWidth eqs P.trials).trans room⟩
  obtain ⟨z,k,run,work,out⟩ := cappedReports_exec r (P.a+19) (P.a+23) (P.a+22)
    (countTrial P.bank kernel S.command) (visitRank P.bank kernel S.command) P.trials p v
    count advance (emits f) (P.invariant f) (fun i => P.Ready (eqs i))
    (fun _ _ k a w h => k.writeCursor (seen_above space) a w h)
    (fun _ _ ready rank => ready.writeRank rank)
    (fun x u h => rb u x h) (fun _ _ ready => ready.count)
    (fun i hi x u h ptr fu => P.prepare_trial S kernel eqs f space oracle i hi x u h ptr fu)
    (fun i hi j hj x u h ready ptr rank fu => P.emit_trial S kernel eqs f space oracle i j hi hj x u h ready ptr rank fu)
    size ∅ u initial trial total fit
  refine ⟨z,k,run,work,?_⟩
  simpa only [estimate,wordsByRank_length,count,advance] using out
end
