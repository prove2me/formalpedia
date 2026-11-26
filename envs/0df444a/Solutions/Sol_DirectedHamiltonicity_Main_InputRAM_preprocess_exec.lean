-- Prove2me | solution 1 for DirectedHamiltonicity.Main.InputRAM.preprocess_exec
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-26T17:20:45.982293+00:00
-- url     : https://prove2.me/submissions/fa93d2f6-3710-4822-9277-13205c6c9b66

import Definitions.Def_DirectedHamiltonicity_ParityRAMInterfaces

set_option autoImplicit false

section LogCostWordBounds

/-! Bit-cost bounds for bounded-width executions on the published log-cost RAM. -/

namespace TargetedSamplers

theorem size_add_le_succ {u v b : ℕ} (hu : u.size ≤ b) (hv : v.size ≤ b) :
    (u + v).size ≤ b + 1 := by
  rw [Nat.size_le] at *
  rw [pow_succ]
  omega

end TargetedSamplers

end LogCostWordBounds

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

section HamiltonianInputFields

namespace DirectedHamiltonicity.Main

open TargetedSamplers.Structured.BinaryRead

theorem arcFields_length {n m : ℕ} (tail head : Fin m → Fin n) (weight : Fin m → ℕ) (s t : Fin n) :
    (arcFields tail head weight s t).length = 3*m+2 := by
  have h (es : List (Fin m)) : (es.flatMap fun e => [(tail e).val,(head e).val,weight e]).length = 3*es.length := by
    induction es with
    | nil => rfl
    | cons e es ih =>
      simp only [List.flatMap_cons,List.length_append,List.length_cons,List.length_nil,ih]
      omega
  simp [arcFields,h]

theorem arcFields_terminals {n m : ℕ} (tail head : Fin m → Fin n) (weight : Fin m → ℕ) (s t : Fin n) :
    (arcFields tail head weight s t)[3*m]? = some s.val ∧ (arcFields tail head weight s t)[3*m+1]? = some t.val := by
  let es := (List.finRange m).flatMap fun e => [(tail e).val,(head e).val,weight e]
  have h := arcFields_length tail head weight s t
  change (es++[s.val,t.val]).length = 3*m+2 at h
  simp only [List.length_append,List.length_cons,List.length_nil] at h
  have len : es.length = 3*m := by omega
  change (es++[s.val,t.val])[3*m]? = _ ∧ (es++[s.val,t.val])[3*m+1]? = _
  rw [List.getElem?_append_right (by omega),List.getElem?_append_right (by omega),len]
  simp

end DirectedHamiltonicity.Main

end HamiltonianInputFields

section LogCostRAMStridedMax

namespace TargetedSamplers.Structured

/-- Maximum of a finite prefix, using zero as the maximum of the empty prefix. -/
def prefixMax (v : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | i+1 => max (prefixMax v i) (v i)

private theorem maxBody_exec {τ : Tapes} (r : Fin 8 ↪ ℕ) {s : Store} {b addr stride old val : ℕ}
    (ptr : s.mem (r 3) = addr) (step : s.mem (r 4) = stride) (acc : s.mem (r 6) = old)
    (hz : s.mem (r 7) = 0) (v : s.mem addr = val) (hw : (addr+stride).size ≤ b) (fit : s.Fits b) :
    let u := ((maxBody r).run τ s).last
    ∃ k ≤ 4, Exec τ (fun t => t.Fits b) (maxBody r).cmd s u k ∧
      u.mem (r 3) = addr+stride ∧ u.mem (r 6) = max old val ∧ u.out = s.out ∧
      ∀ a, a ≠ r 3 → a ≠ r 5 → a ≠ r 6 → u.mem a = s.mem a := by
  have eq (i j : Fin 8) : r i = r j ↔ i=j := r.injective.eq_iff
  have vw := v ▸ fit addr
  have ww : ((maxBody r).run τ s).writeWidth ≤ b := by
    by_cases h : old ≤ val <;>
      simp [maxBody,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,
        Function.update_apply,eq,ptr,step,acc,hz,v,h,hw,vw]
  refine ⟨_,?_,(maxBody r).exec τ s b fit ww,?_,?_,?_,?_⟩
  all_goals first
    | (intro a h3 h5 h6
       by_cases ht : old ≤ val <;> simp [maxBody,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Store.write,
         Function.update_apply,eq,ptr,acc,v,ht,h3,h5,h6])
    | (by_cases ht : old ≤ val <;>
       simp [maxBody,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Store.write,Function.update_apply,
         eq,ptr,step,acc,hz,v,ht,max_def])

/-- Scan one field of fixed-size records. The output depends only on the values at the
requested offsets and all memory outside the four mutable registers is preserved. -/
theorem stridedMax_exec {τ : Tapes} (r : Fin 8 ↪ ℕ) {b : ℕ} (s : Store) (base stride count : ℕ)
    (val : ℕ → ℕ) (data : ∀ i < count, s.mem (base+i*stride) = val i) (sep : ∀ i, r i < base)
    (start : s.mem (r 0) = 0) (stop : s.mem (r 1) = count) (unit : s.mem (r 2) = 1)
    (ptr : s.mem (r 3) = base) (step : s.mem (r 4) = stride) (acc : s.mem (r 6) = 0) (hz : s.mem (r 7) = 0)
    (fit : s.Fits b) (hw : (base+count*stride).size ≤ b) :
    ∃ t j, Exec τ (fun u => u.Fits b) (stridedMax r) s t j ∧ j ≤ 7*count+1 ∧
      t.mem (r 6) = prefixMax val count ∧ t.out = s.out ∧
      ∀ a, a ≠ r 0 → a ≠ r 3 → a ≠ r 5 → a ≠ r 6 → t.mem a = s.mem a := by
  let state (i : ℕ) (u : Store) : Prop :=
    u.mem (r 0) = i ∧ u.mem (r 3) = base+i*stride ∧ u.mem (r 6) = prefixMax val i ∧ u.out = s.out ∧
      ∀ a, a ≠ r 0 → a ≠ r 3 → a ≠ r 5 → a ≠ r 6 → u.mem a = s.mem a
  have ne {i j : Fin 8} (h : i ≠ j) := r.injective.ne h
  have kept {i : ℕ} {u : Store} (h : state i u) (a : Fin 8) (h0 : a ≠ 0) (h3 : a ≠ 3) (h5 : a ≠ 5) (h6 : a ≠ 6) :=
    h.2.2.2.2 (r a) (ne h0) (ne h3) (ne h5) (ne h6)
  have control (i : ℕ) (_ : i ≤ count) (u : Store) (h : state i u) :
      u.mem (r 0) = 0+i ∧ u.mem (r 1) = 0+count := by
    simpa using And.intro h.1 ((kept h 1 (by decide) (by decide) (by decide) (by decide)).trans stop)
  have work (i : ℕ) (hi : i < count) (u : Store) (h : state i u) (fu : u.Fits b) :
      ∃ z k, Exec τ (fun st => st.Fits b) (maxBody r).cmd u z k ∧ k ≤ 4 ∧ z.mem (r 0) = 0+i ∧ z.mem (r 2) = 1 ∧
        state (i+1) (z.write (r 0) (0+i+1)) := by
    have outside (j : Fin 8) : base+i*stride ≠ r j := by have := sep j; omega
    have src := (h.2.2.2.2 _ (outside 0) (outside 3) (outside 5) (outside 6)).trans (data i hi)
    have addr : base+i*stride+stride = base+(i+1)*stride := by rw [Nat.succ_mul,Nat.add_assoc]
    have hbnd : base+i*stride+stride ≤ base+count*stride := addr ▸ Nat.add_le_add_left (Nat.mul_le_mul_right _ hi) _
    obtain ⟨k,hk,ex,pos,mx,out,fr⟩ := maxBody_exec (τ := τ) r h.2.1
      ((kept h 4 (by decide) (by decide) (by decide) (by decide)).trans step) h.2.2.1
      ((kept h 7 (by decide) (by decide) (by decide) (by decide)).trans hz) src ((Nat.size_le_size hbnd).trans hw) fu
    let z := ((maxBody r).run τ u).last
    refine ⟨z,k,ex,hk,by simpa using (fr _ (ne (by decide)) (ne (by decide)) (ne (by decide))).trans h.1,
      (fr _ (ne (by decide)) (ne (by decide)) (ne (by decide))).trans
        ((kept h 2 (by decide) (by decide) (by decide) (by decide)).trans unit),?_,?_,?_,out.trans h.2.2.2.1,?_⟩
    · simp [Store.write]
    · simpa only [Store.write,Function.update_of_ne (ne (by decide : (3:Fin 8) ≠ 0)),addr] using pos
    · simpa only [Store.write,Function.update_of_ne (ne (by decide : (6:Fin 8) ≠ 0)),prefixMax] using mx
    · intro a h0 h3 h5 h6
      simpa [Store.write,h0] using (fr a h3 h5 h6).trans (h.2.2.2.2 a h0 h3 h5 h6)
  have initial : state 0 s := ⟨start,by simpa using ptr,acc,rfl,fun _ _ _ _ _ => rfl⟩
  obtain ⟨t,j,ex,hj,last⟩ := forRange_exec (τ := τ) (r 0) (r 1) (r 2) 0 count 4 (maxBody r).cmd state control work
    (by simpa using (stop ▸ fit (r 1))) s initial fit
  exact ⟨t,j,ex,by omega,last.2.2.1,last.2.2.2⟩

end TargetedSamplers.Structured

end LogCostRAMStridedMax

section HamiltonianInputBound

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.BinaryRead

def weightAt {m : ℕ} (w : Fin m → ℕ) (i : ℕ) : ℕ := if h : i < m then w ⟨i,h⟩ else 0

private theorem prefixMax_le_iff (w : ℕ → ℕ) (j a : ℕ) :
    prefixMax w j ≤ a ↔ ∀ i < j, w i ≤ a := by
  induction j with
  | zero => simp [prefixMax]
  | succ j ih =>
    rw [prefixMax,max_le_iff,ih]
    constructor
    · rintro ⟨p,q⟩ i hi
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with v|rfl
      · exact p i v
      · exact q
    · exact fun h => ⟨fun i hi => h i (Nat.lt_succ_of_lt hi),h j (Nat.lt_succ_self j)⟩

theorem prefixMax_fin {m : ℕ} (w : Fin m → ℕ) :
    prefixMax (weightAt w) m = Finset.univ.sup w := by
  apply le_antisymm
  · apply (prefixMax_le_iff ..).2
    intro i hi
    simpa [weightAt,hi] using (Finset.le_sup (f := w) (Finset.mem_univ (⟨i,hi⟩ : Fin m)))
  · apply Finset.sup_le
    intro i _
    simpa [weightAt,i.isLt] using (prefixMax_le_iff (weightAt w) m _).1 le_rfl i.val i.isLt

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianInputBound

section LogCostRAMCompare

namespace TargetedSamplers.Structured

/-- Compare words using the native non-strict comparison. Equal words take two jumps;
unequal words take at most three before and after executing the selected arm. -/
theorem ifEqual_exec {τ : TargetedSamplers.Tapes} {I : Store → Prop} (l r : ℕ)
    {yes no : Cmd} {s t : Store} {k : ℕ} (h : Exec τ I (if s.mem l=s.mem r then yes else no) s t k) :
    ∃ j ≤ k+3, Exec τ I (ifEqual l r yes no) s t j := by
  by_cases eq : s.mem l = s.mem r
  · rw [if_pos eq] at h
    exact ⟨_,by omega,.yes eq.le (.yes eq.ge h)⟩
  · rw [if_neg eq] at h
    by_cases le : s.mem l ≤ s.mem r
    · exact ⟨_,by omega,.yes le (.no (by omega) h)⟩
    · exact ⟨_,by omega,.no le h⟩

def allEqual (s : Store) (xs : List (ℕ × ℕ)) := xs.all fun p => decide (s.mem p.1 = s.mem p.2)

theorem whenEqual_exec {τ : TargetedSamplers.Tapes} {I : Store → Prop} (tests : List (ℕ × ℕ)) (body : Cmd)
    {s t : Store} {k : ℕ} (h : Exec τ I (if allEqual s tests then body else .skip) s t k) :
    ∃ j ≤ k+3*tests.length, Exec τ I (whenEqual tests body) s t j := by
  induction tests with
  | nil => exact ⟨k,by simp,by simpa [whenEqual,allEqual] using h⟩
  | cons test rest ih =>
    obtain ⟨a,b⟩ := test
    have head : allEqual s ((a,b)::rest) = (decide (s.mem a = s.mem b) && allEqual s rest) := rfl
    rw [head] at h
    by_cases eq : s.mem a = s.mem b
    · rw [decide_eq_true eq, Bool.true_and] at h
      obtain ⟨j,hj,run⟩ := ih h
      obtain ⟨i,hi,exec⟩ := ifEqual_exec (τ := τ) (I := I) a b (yes := whenEqual rest body) (no := .skip)
        (s := s) (t := t) (k := j) (by simpa only [if_pos eq] using run)
      exact ⟨i,by simp only [List.length_cons]; omega,exec⟩
    · have skip : Exec τ I .skip s t k := by simpa only [decide_eq_false eq, Bool.false_and, Bool.false_eq_true, if_false] using h
      obtain ⟨j,hj,exec⟩ := ifEqual_exec (τ := τ) (I := I) a b (yes := whenEqual rest body) (no := .skip)
        (s := s) (t := t) (k := k) (by simpa only [if_neg eq] using skip)
      exact ⟨j,by simp only [List.length_cons]; omega,exec⟩

end TargetedSamplers.Structured

end LogCostRAMCompare

section LogCostRAMTripleParity

namespace TargetedSamplers.Structured.TripleScan

theorem RecordsAt.congr {s t : Store} {base : ℕ} {xs : List Record}
    (h : RecordsAt s base xs) (same : ∀ a ≥ base, t.mem a = s.mem a) : RecordsAt t base xs := by
  induction xs generalizing base with
  | nil => trivial
  | cons x xs ih =>
    exact ⟨(same _ le_rfl).trans h.1,(same _ (by omega)).trans h.2.1,
      (same _ (by omega)).trans h.2.2.1,ih h.2.2.2 (fun a ha => same a (by omega))⟩

def wanted (r : Fin 10 ↪ ℕ) (s : Store) : Record := (s.mem (r 3),s.mem (r 4),s.mem (r 5))

private theorem readFields_exec {τ : Tapes} {b : ℕ} (r : Fin 10 ↪ ℕ) (s : Store) (p : ℕ)
    (ptr : s.mem (r 0) = p) (one : s.mem (r 2) = 1) (sep : ∀ i, r i < p)
    (fit : s.Fits b) (width : (p+3).size ≤ b) :
    let t := ((readFields r).run τ s).last
    Exec τ (fun u => u.Fits b) (readFields r).cmd s t 6 ∧ t.mem (r 0) = p+3 ∧
      t.mem (r 7) = s.mem p ∧ t.mem (r 8) = s.mem (p+1) ∧ t.mem (r 9) = s.mem (p+2) ∧
      t.out = s.out ∧ ∀ a, a ≠ r 0 → a ≠ r 7 → a ≠ r 8 → a ≠ r 9 → t.mem a = s.mem a := by
  have eq (i j : Fin 10) : r i = r j ↔ i=j := r.injective.eq_iff
  have past (k : ℕ) (i : Fin 10) : p+k ≠ r i := by have := sep i; omega
  have w₁ := (Nat.size_le_size (show p+1 ≤ p+3 by omega)).trans width
  have w₂ := (Nat.size_le_size (show p+2 ≤ p+3 by omega)).trans width
  have ww : ((readFields r).run τ s).writeWidth ≤ b := by
    simp [readFields,sequence,Fragment.run,Op.eval,Op.written,Store.write,Function.update_apply,
      eq,ptr,one,Nat.add_assoc,past,w₁,w₂,width,fit p,fit (p+1),fit (p+2)]
  refine ⟨(readFields r).exec τ s b fit ww,?_,?_,?_,?_,rfl,?_⟩
  all_goals first
    | (intro a h₀ h₇ h₈ h₉
       simp [readFields,sequence,Fragment.run,Op.eval,Store.write,Function.update_apply,h₀,h₇,h₈,h₉])
    | simp [readFields,sequence,Fragment.run,Op.eval,Store.write,Function.update_apply,eq,ptr,one,Nat.add_assoc,past]

private theorem toggle_exec {τ : Tapes} {b : ℕ} (r : Fin 10 ↪ ℕ) (s : Store)
    (unit : s.mem (r 2) = 1) (fit : s.Fits b) :
    Exec τ (fun u => u.Fits b) (toggle r) s (s.write (r 6) (1-s.mem (r 6))) 1 := by
  have wh := (Nat.size_le_size (Nat.sub_le 1 (s.mem (r 6)))).trans (unit ▸ fit (r 2))
  simpa only [toggle,Op.eval,unit] using (Exec.op (τ := τ) (inv := fun u => u.Fits b)
    s (.sub (r 6) (r 2) (r 6)) (by simp only [Op.eval,unit]; exact Store.write_fits fit _ wh))

private theorem guardedToggle_exec {τ : Tapes} {b : ℕ} (r : Fin 10 ↪ ℕ) (s : Store)
    (hit : Bool) (matchBit : allEqual s (tests r) = hit) (one : s.mem (r 2) = 1) (fit : s.Fits b) :
    ∃ t j, Exec τ (fun u => u.Fits b) (whenEqual (tests r) (toggle r)) s t j ∧ j ≤ 10 ∧
      t.mem (r 6) = (if hit then 1-s.mem (r 6) else s.mem (r 6)) ∧
      t.out = s.out ∧ ∀ a, a ≠ r 6 → t.mem a = s.mem a := by
  cases hit with
  | false =>
    obtain ⟨j,hj,ex⟩ := whenEqual_exec (tests r) (toggle r)
      (τ := τ) (I := fun u => u.Fits b) (s := s) (t := s) (k := 0)
      (by simp only [matchBit,Bool.false_eq_true,if_false]; exact .skip _)
    exact ⟨s,j,ex,by simp [tests] at hj; omega,rfl,rfl,fun _ _ => rfl⟩
  | true =>
    obtain ⟨j,hj,ex⟩ := whenEqual_exec (tests r) (toggle r)
      (τ := τ) (I := fun u => u.Fits b) (s := s) (t := s.write (r 6) (1-s.mem (r 6))) (k := 1)
      (by simp only [matchBit,if_true]; exact toggle_exec r s one fit)
    exact ⟨_,j,ex,by simpa [tests] using hj,by simp [Store.write],rfl,fun _ h => by simp [Store.write,h]⟩

/-- Read a triple, compare it with the query, and toggle a bit once for each match. -/
theorem loop_exec {τ : Tapes} {b : ℕ} (r : Fin 10 ↪ ℕ) (xs : List Record) (s : Store)
    (p v : ℕ) (q : Record) (data : RecordsAt s p xs) (ptr : s.mem (r 0) = p)
    (stop : s.mem (r 1) = p+3*xs.length) (unit : s.mem (r 2) = 1) (key : wanted r s = q)
    (acc : s.mem (r 6) = v) (bit : v ≤ 1) (sep : ∀ i, r i < p) (fit : s.Fits b) :
    ∃ t j, Exec τ (fun u => u.Fits b) (loop r) s t j ∧ j ≤ 18*xs.length+1 ∧
      t.mem (r 0) = p+3*xs.length ∧ t.mem (r 6) = (v+xs.count q)%2 ∧ t.out = s.out ∧
      ∀ a, untouched r a → t.mem a = s.mem a := by
  induction xs generalizing s p v with
  | nil =>
    exact ⟨s,1,.done (by simpa [stop,ptr]),by simp,by simpa using ptr,
      by simpa [Nat.mod_eq_of_lt (show v < 2 by omega)] using acc,rfl,fun _ _ => rfl⟩
  | cons x xs ih =>
    have eq (i j : Fin 10) : r i = r j ↔ i=j := r.injective.eq_iff
    have endAt : s.mem (r 1) = p+3+3*xs.length := by rw [stop,List.length_cons]; omega
    let u := ((readFields r).run τ s).last
    obtain ⟨read,pos,h₇,h₈,h₉,out₁,fr₁⟩ := readFields_exec (τ := τ) r s p ptr unit sep fit
      ((Nat.size_le_size (show p+3 ≤ s.mem (r 1) by omega)).trans (fit _))
    have keep (i : Fin 10) (h : i ≠ 0 ∧ i ≠ 7 ∧ i ≠ 8 ∧ i ≠ 9) : u.mem (r i) = s.mem (r i) :=
      fr₁ _ (r.injective.ne h.1) (r.injective.ne h.2.1) (r.injective.ne h.2.2.1) (r.injective.ne h.2.2.2)
    have one : u.mem (r 2) = 1 := (keep 2 (by decide)).trans unit
    have matchBit : allEqual u (tests r) = decide (x = q) := by
      subst q
      rcases x with ⟨a,c,d⟩
      simp only [allEqual,tests,List.all_cons,List.all_nil, Bool.and_true, wanted,
        Prod.mk.injEq,Bool.decide_and]
      rw [h₇,h₈,h₉,data.1,data.2.1,data.2.2.1,keep 3 (by decide),keep 4 (by decide),keep 5 (by decide)]
    obtain ⟨z,k,guard,hk,val,out₂,fr₂⟩ := guardedToggle_exec (τ := τ) r u _ matchBit one (read.post fit)
    let next := if x=q then 1-v else v
    have vz : z.mem (r 6) = next := by simpa [next,keep 6 (by decide),acc] using val
    have frame (a : ℕ) (hp : untouched r a) : z.mem a = s.mem a :=
      (fr₂ a hp.2.1).trans (fr₁ a hp.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2)
    have regular (i : Fin 10) (hi : i ≠ 0 ∧ i ≠ 6 ∧ i ≠ 7 ∧ i ≠ 8 ∧ i ≠ 9) : untouched r (r i) := by
      simpa only [untouched,ne_eq,eq] using hi
    have off (a : ℕ) (ha : p ≤ a) : untouched r a := by
      have outside (i : Fin 10) : a ≠ r i := by have := sep i; omega
      exact ⟨outside _,outside _,outside _,outside _,outside _⟩
    have kz : wanted r z = q := by
      simpa only [wanted,frame _ (regular 3 (by decide)),frame _ (regular 4 (by decide)),frame _ (regular 5 (by decide))] using key
    have posz := (fr₂ _ (r.injective.ne (by decide : (0:Fin 10) ≠ 6))).trans pos
    obtain ⟨t,j,rest,hj,last,result,out₃,fr₃⟩ := ih z (p+3) next
      (data.2.2.2.congr (fun a ha => frame a (off a (by omega)))) posz
      ((frame _ (regular 1 (by decide))).trans endAt) ((frame _ (regular 2 (by decide))).trans unit) kz vz
      (by dsimp [next]; split <;> omega) (fun i => by have := sep i; omega) (guard.post (read.post fit))
    refine ⟨t,_,.again (by rw [ptr,endAt]; omega) (read.seq guard) rest,
      by simp only [List.length_cons]; omega,by rw [last,List.length_cons]; omega,?_,
      out₃.trans (out₂.trans out₁),fun a ha => (fr₃ a ha).trans (frame a ha)⟩
    rw [result]
    by_cases eqx : x=q
    · subst x
      simp only [next,if_true,List.count_cons_self]
      omega
    · simp only [next,if_neg eqx,List.count_cons_of_ne eqx]

end TargetedSamplers.Structured.TripleScan

end LogCostRAMTripleParity

section LogCostRAMFilter

namespace TargetedSamplers.Structured

def anyEqual (s : Store) (xs : List (ℕ × ℕ)) := xs.any fun p => decide (s.mem p.1 = s.mem p.2)

theorem clearEqual_exec {τ : Tapes} {b : ℕ} (dst : ℕ) (xs : List (ℕ × ℕ)) (s : Store)
    (apart : ∀ p ∈ xs, p.1 ≠ dst ∧ p.2 ≠ dst) (fit : s.Fits b) :
    ∃ t j, Exec τ (fun u => u.Fits b) (clearEqual dst xs) s t j ∧ j ≤ 4*xs.length ∧
      t.mem dst = (if anyEqual s xs then 0 else s.mem dst) ∧ t.out = s.out ∧
      ∀ a, a ≠ dst → t.mem a = s.mem a := by
  induction xs generalizing s with
  | nil => exact ⟨s,0,.skip _,by simp,rfl,rfl,fun _ _ => rfl⟩
  | cons p xs ih =>
    obtain ⟨a,c⟩ := p
    let u := if s.mem a = s.mem c then s.write dst 0 else s
    have run : ∃ j ≤ 4, Exec τ (fun u => u.Fits b) (ifEqual a c (.op (.const dst 0)) .skip) s u j := by
      by_cases eq : s.mem a = s.mem c
      · exact ifEqual_exec a c (s := s) (t := u) (k := 1)
          (by rw [if_pos eq]; dsimp [u]; rw [if_pos eq]; exact .op _ _ (Store.write_fits fit _ (by simp)))
      · obtain ⟨j,hj,ex⟩ := ifEqual_exec (τ := τ) (I := fun u => u.Fits b) a c
          (yes := .op (.const dst 0)) (no := .skip) (s := s) (t := u) (k := 0)
          (by rw [if_neg eq]; dsimp [u]; rw [if_neg eq]; exact .skip _)
        exact ⟨j,by omega,ex⟩
    obtain ⟨i,wi,first⟩ := run
    have keep (z : ℕ) (h : z ≠ dst) : u.mem z = s.mem z := by
      dsimp [u]; split <;> simp [Store.write,h]
    have tailApart (p : ℕ × ℕ) (hp : p ∈ xs) := apart p (List.mem_cons_of_mem _ hp)
    have same : anyEqual u xs = anyEqual s xs := by
      apply Bool.eq_iff_iff.mpr
      simp only [anyEqual,List.any_eq_true,decide_eq_true_eq]
      constructor <;> rintro ⟨p,hp,eq⟩ <;> refine ⟨p,hp,?_⟩ <;>
        simpa only [keep _ (tailApart p hp).1,keep _ (tailApart p hp).2] using eq
    obtain ⟨t,j,rest,wj,result,out,frame⟩ := ih u tailApart (first.post fit)
    refine ⟨t,_,first.seq rest,by simp only [List.length_cons]; omega,?_,?_,fun z hz => (frame z hz).trans (keep z hz)⟩
    · rw [result,same]
      change _ = (if (decide (s.mem a = s.mem c) || anyEqual s xs) then 0 else s.mem dst)
      by_cases eq : s.mem a = s.mem c <;> simp [u,eq,Store.write]
    · rw [out]; dsimp [u]; split <;> rfl

end TargetedSamplers.Structured

end LogCostRAMFilter

section HamiltonianRAMArcs

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.TripleScan

open Multidigraph

private def words (xs : List Record) : List ℕ :=
  xs.flatMap fun x => [x.1,x.2.1,x.2.2]

private theorem recordsAt_of_words (s : Store) (base : ℕ) (xs : List Record) (suffix : List ℕ)
    (table : ∀ i (hi : i < (words xs ++ suffix).length), s.mem (base+i) = (words xs ++ suffix)[i]) :
    RecordsAt s base xs := by
  induction xs generalizing base with
  | nil => trivial
  | cons x xs ih =>
    let rest := words xs ++ suffix
    have data (i : ℕ) (hi : i < (x.1::x.2.1::x.2.2::rest).length) :
        s.mem (base+i) = (x.1::x.2.1::x.2.2::rest)[i] := table i hi
    have first := data 0 (by simp)
    change s.mem (base+0) = x.1 at first
    refine ⟨first,data 1 (by simp),data 2 (by simp),ih (base+3) ?_⟩
    intro i hi
    have loc := data (i+3) (by simp only [List.length_cons]; dsimp [rest]; omega)
    simpa only [List.getElem_cons_succ,show base+(i+3) = base+3+i by omega] using loc

/-- Link the store returned by the tape parser to the triple-scan interface. -/
theorem Parsed.records {n m : ℕ} {tail head : Fin m → Fin n} {w : Fin m → ℕ} {s t : Fin n}
    {B : ℤ} {u : Store} (h : Parsed tail head w s t B u) : RecordsAt u graphBase (edgeRecords tail head w) := by
  apply recordsAt_of_words u graphBase _ [s.val,t.val]
  simpa [edgeRecords,arcFields,words,List.flatMap_map,Function.comp_def] using h.table

/-- Count queried triples in precisely the edge enumeration used by the external encoding. -/
theorem count_edgeRecords {n m W : ℕ} (tail head : Fin m → Fin n) (w : Fin m → ℕ)
    (hw : ∀ e, w e ≤ W) (q : ArcType (Fin n) W) :
    (edgeRecords tail head w).count (q.1.val,q.2.1.val,q.2.2.val) =
      Nat.card {e : Fin m // Multidigraph.arcType (⟨tail,head⟩ : Multidigraph (Fin n) (Fin m)) w hw e = q} := by
  classical
  let f (e : Fin m) : Record := ((tail e).val,(head e).val,w e)
  let test (e : Fin m) := Multidigraph.arcType (⟨tail,head⟩ : Multidigraph (Fin n) (Fin m)) w hw e = q
  let key : Record := (q.1.val,q.2.1.val,q.2.2.val)
  have he (e : Fin m) : f e = key ↔ test e := by
    rcases q with ⟨a,b,c⟩
    simp [f,key,test,arcType,Prod.ext_iff,Fin.ext_iff]
  have counts (es : List (Fin m)) : (es.map f).count key = es.countP fun e => decide (test e) := by
    induction es with
    | nil => rfl
    | cons e es ih =>
      by_cases h : f e = key
      · simp [h,(he e).mp h,ih]
      · have hn : ¬test e := fun eq => h ((he e).mpr eq)
        simp [List.countP_cons,h,hn,ih]
  change ((List.finRange m).map f).count key = Nat.card {e : Fin m // test e}
  rw [counts,Nat.card_eq_fintype_card,Fintype.card_subtype,← (List.nodup_finRange m).card_eq_countP]
  simp

theorem retainedQuery_exec {τ : Tapes} {width : ℕ} {n m W : ℕ} (tail head : Fin m → Fin n)
    (w : Fin m → ℕ) (hw : ∀ e, w e ≤ W) (s t : Fin n) (q : ArcType (Fin n) W)
    (r : Fin 10 ↪ ℕ) (src dst base : ℕ) (u : Store) (records : RecordsAt u base (edgeRecords tail head w))
    (sep : ∀ i, r i < base) (ptr : u.mem (r 0) = base) (stop : u.mem (r 1) = base+3*m)
    (one : u.mem (r 2) = 1) (key : wanted r u = (q.1.val,q.2.1.val,q.2.2.val))
    (source : u.mem src = s.val) (sink : u.mem dst = t.val) (hs : untouched r src) (ht : untouched r dst)
    (fit : u.Fits width) :
    ∃ z j, Exec τ (fun v => v.Fits width) (retainedQuery r src dst) u z j ∧ j ≤ 18*m+14 ∧
      z.mem (r 6) ≤ 1 ∧ (z.mem (r 6) = 1 ↔ Multidigraph.retainArc (⟨tail,head⟩ : Multidigraph (Fin n) (Fin m)) w s t hw q) ∧
      z.mem (r 0) = base+3*m ∧ z.out = u.out ∧ ∀ a, untouched r a → z.mem a = u.mem a := by
  let v := u.write (r 6) 0
  have f : v.Fits width := Store.write_fits fit _ (by simp)
  have init : Exec τ (fun st => st.Fits width) (.op (.const (r 6) 0)) u v 1 := .op _ _ f
  have ne {i j : Fin 10} (h : i ≠ j) := r.injective.ne h
  have eq (i j : Fin 10) : r i = r j ↔ i=j := r.injective.eq_iff
  have atReg (i : Fin 10) (hi : i ≠ 6) : v.mem (r i) = u.mem (r i) := by simp [v,Store.write,ne hi]
  have keep (a : ℕ) (ha : untouched r a) : v.mem a = u.mem a := by simp [v,Store.write,ha.2.1]
  have len : (edgeRecords tail head w).length = m := by simp [edgeRecords]
  have records' : RecordsAt v base (edgeRecords tail head w) := records.congr (fun a ha => by
    have := sep 6; simp [v,Store.write,show a ≠ r 6 by omega])
  obtain ⟨a,i,scan,wi,pos,bit,out,frame⟩ := loop_exec (τ := τ) r (edgeRecords tail head w) v base 0
    (q.1.val,q.2.1.val,q.2.2.val) records' ((atReg 0 (by decide)).trans ptr) (by rw [len,atReg _ (by decide),stop])
    ((atReg 2 (by decide)).trans one) (by simpa only [wanted,atReg 3 (by decide),atReg 4 (by decide),atReg 5 (by decide)] using key)
    (by simp [v,Store.write]) (by decide) sep f
  rw [len] at wi pos
  rw [Nat.zero_add,count_edgeRecords tail head w hw q] at bit
  have fixes (p : ℕ × ℕ) (hp : p ∈ forbidden r src dst) : p.1 ≠ r 6 ∧ p.2 ≠ r 6 := by
    simp only [forbidden,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl
    · exact ⟨ne (by decide),ne (by decide)⟩
    · exact ⟨ne (by decide),hs.2.1⟩
    · exact ⟨ne (by decide),ht.2.1⟩
  obtain ⟨z,k,filter,wk,ret,out',fr⟩ := clearEqual_exec (τ := τ) (r 6) _ a fixes (scan.post f)
  have saved (ad : ℕ) (h : untouched r ad) := (frame ad h).trans (keep ad h)
  have reg (i : Fin 10) (h : i ≠ 0 ∧ i ≠ 6 ∧ i ≠ 7 ∧ i ≠ 8 ∧ i ≠ 9) : untouched r (r i) := by
    simpa only [untouched,ne_eq,eq] using h
  have keys := Prod.mk.inj key
  have heads := Prod.mk.inj keys.2
  have bad : anyEqual a (forbidden r src dst) = decide (q.1 = q.2.1 ∨ q.2.1 = s ∨ q.1 = t) := by
    simp only [anyEqual,forbidden,List.any_cons,List.any_nil,Bool.or_false,
      saved _ (reg 3 (by decide)),saved _ (reg 4 (by decide)),saved _ hs,saved _ ht,
      keys.1,heads.1,source,sink,Bool.decide_or,Fin.ext_iff]
  simp only [bad,decide_eq_true_eq] at ret
  refine ⟨z,_,init.seq (scan.seq filter),by simp [forbidden] at wk; omega,?_,?_,
    (fr _ (ne (by decide))).trans pos,out'.trans out,fun ad ha => (fr ad ha.2.1).trans (saved ad ha)⟩
  · rw [ret]; split <;> omega
  · rw [ret,bit]
    by_cases h : q.1 = q.2.1 ∨ q.2.1 = s ∨ q.1 = t
    · rw [if_pos h]
      simp only [retainArc,Nat.odd_iff,Nat.zero_ne_one]
      tauto
    · rw [if_neg h]
      simp only [retainArc,Nat.odd_iff,Nat.zero_ne_one]
      tauto

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMArcs

section LogCostRAMFold

namespace TargetedSamplers.Structured

def Reduction.join : Reduction → ℕ → ℕ → ℕ
  | .sum,x,y => x+y
  | .maximum,x,y => max x y

def Reduction.prefix (op : Reduction) (x : ℕ) (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => x
  | i+1 => op.join (op.prefix x f i) (f i)

private theorem write_own (s : Store) (a : ℕ) : s.write a (s.mem a) = s := by cases s; simp [Store.write]

private theorem Reduction.combine_exec {τ : Tapes} {b : ℕ} (op : Reduction) (r : Fin 6 ↪ ℕ) (s : Store)
    (x y : ℕ) (acc : s.mem (r 3) = x) (v : s.mem (r 4) = y) (zero : s.mem (r 5) = 0)
    (fit : s.Fits b) (w : (op.join x y).size ≤ b) :
    ∃ k ≤ 2, Exec τ (fun u => u.Fits b) (op.combine r) s (s.write (r 3) (op.join x y)) k := by
  cases op with
  | sum =>
    have ev : (Op.add (r 3) (r 3) (r 4)).eval τ s = s.write (r 3) (x+y) := by simp [Op.eval,acc,v]
    exact ⟨1,by decide,by simpa only [combine,join,ev] using
      (Exec.op (τ := τ) (inv := fun u => u.Fits b) s (.add (r 3) (r 3) (r 4))
        (by rw [ev]; exact Store.write_fits fit _ w))⟩
  | maximum =>
    by_cases h : x ≤ y
    · have ev : (Op.add (r 3) (r 4) (r 5)).eval τ s = s.write (r 3) y := by simp [Op.eval,v,zero]
      have cp := Exec.op (τ := τ) (inv := fun u => u.Fits b) s (.add (r 3) (r 4) (r 5))
        (by rw [ev]; exact Store.write_fits fit _ (v ▸ fit _))
      have e : Exec τ (fun u => u.Fits b) _ s (s.write (r 3) y) 2 :=
        Exec.yes (a := r 3) (b := r 4) (n := .skip) (by rwa [acc,v]) (ev ▸ cp)
      exact ⟨2,le_rfl,by simpa only [combine,join,max_eq_right h] using e⟩
    · have e := Exec.no (τ := τ) (inv := fun u => u.Fits b) (a := r 3) (b := r 4)
        (y := .op (.add (r 3) (r 4) (r 5))) (by rwa [acc,v]) (Exec.skip s)
      have own : s.write (r 3) x = s := by rw [← acc,write_own]
      exact ⟨2,le_rfl,by simpa only [combine,join,max_eq_left (by omega : y ≤ x),own] using e⟩

/-- Reduce a sequence of kernel results. The invariant describes the caller's live data and
may leave the body's private workspace unspecified. This permits nested reductions. -/
theorem Reduction.reduce_exec {τ : Tapes} {b : ℕ} (op : Reduction) (r : Fin 6 ↪ ℕ)
    (initial count bound : ℕ) (body : Cmd) (f : ℕ → ℕ) (K : Store → Prop)
    (stable : ∀ s, K s → ∀ a, a = r 0 ∨ a = r 3 → ∀ x, K (s.write a x))
    (ctrl : ∀ s, K s → s.mem (r 1) = count ∧ s.mem (r 2) = 1 ∧ s.mem (r 5) = 0)
    (kernel : ∀ i < count, ∀ s, K s → s.mem (r 0) = i → s.Fits b →
      ∃ t j, Exec τ (fun u => u.Fits b) body s t j ∧ j ≤ bound ∧ K t ∧
        t.mem (r 0) = i ∧ t.mem (r 3) = s.mem (r 3) ∧ t.mem (r 4) = f i)
    (room : ∀ i ≤ count, (op.prefix initial f i).size ≤ b) (s : Store) (h : K s) (fit : s.Fits b) :
    ∃ t j, Exec τ (fun u => u.Fits b) (op.reduce r initial body) s t j ∧ j ≤ count*(bound+5)+3 ∧
      K t ∧ t.mem (r 0) = count ∧ t.mem (r 3) = op.prefix initial f count := by
  let state (i : ℕ) (u : Store) := K u ∧ u.mem (r 0) = i ∧ u.mem (r 3) = op.prefix initial f i
  let z := s.write (r 0) 0
  let start := z.write (r 3) initial
  have hz := stable s h _ (Or.inl rfl) 0
  have hs := stable z hz _ (Or.inr rfl) initial
  have fz : z.Fits b := Store.write_fits fit _ (by simp)
  have fs : start.Fits b := Store.write_fits fz _ (room 0 (by omega))
  have first : Exec τ (fun u => u.Fits b) (.op (.const (r 0) 0)) s z 1 := .op _ _ fz
  have second : Exec τ (fun u => u.Fits b) (.op (.const (r 3) initial)) z start 1 := .op _ _ fs
  have ne {i j : Fin 6} (hi : i ≠ j) := r.injective.ne hi
  have st : state 0 start := ⟨hs,by simp [start,z,Store.write,ne (by decide : (0:Fin 6) ≠ 3)],
    by simp [start,Store.write,Reduction.prefix]⟩
  have work (i : ℕ) (hi : i < count) (u : Store) (inv : state i u) (fu : u.Fits b) :
      ∃ v j, Exec τ (fun a => a.Fits b) (.seq body (op.combine r)) u v j ∧ j ≤ bound+2 ∧
        v.mem (r 0) = 0+i ∧ v.mem (r 2) = 1 ∧ state (i+1) (v.write (r 0) (0+i+1)) := by
    obtain ⟨t,j,ex,hj,kt,pos,acc,val⟩ := kernel i hi u inv.1 inv.2.1 fu
    obtain ⟨k,hk,joinStep⟩ := op.combine_exec (τ := τ) r t _ _ (acc.trans inv.2.2) val (ctrl t kt).2.2 (ex.post fu)
      (room (i+1) hi)
    let v := t.write (r 3) (op.prefix initial f (i+1))
    have kv := stable t kt _ (Or.inr rfl) (op.prefix initial f (i+1))
    refine ⟨v,_,ex.seq joinStep,by omega,?_,(ctrl v kv).2.1,stable v kv _ (Or.inl rfl) _,?_,?_⟩
    · simp [v,Store.write,ne (by decide : (0:Fin 6) ≠ 3),pos]
    · simp [Store.write]
    · simp [v,Store.write,ne (by decide : (3:Fin 6) ≠ 0)]
  obtain ⟨t,j,run,hj,done'⟩ := forRange_exec (τ := τ) (r 0) (r 1) (r 2) 0 count (bound+2)
    (.seq body (op.combine r)) state (fun i _ u inv => by simpa using And.intro inv.2.1 (ctrl u inv.1).1)
    work (by simpa using ((ctrl s h).1 ▸ fit (r 1))) start st fs
  change j ≤ count*(bound+5)+1 at hj
  exact ⟨t,_,first.seq (second.seq run),by omega,done'⟩

theorem Reduction.max_prefix_le {f : ℕ → ℕ} {x B : ℕ} (hx : x ≤ B) (h : ∀ i, f i ≤ B) (k : ℕ) :
    Reduction.maximum.prefix x f k ≤ B := by
  induction k with
  | zero => exact hx
  | succ i ih => exact max_le ih (h i)

theorem Reduction.max_prefix_one {f : ℕ → ℕ} (h : ∀ i, f i ≤ 1) (k : ℕ) :
    Reduction.maximum.prefix 0 f k = 1 ↔ ∃ i < k, f i = 1 := by
  induction k with
  | zero => simp [Reduction.prefix]
  | succ i ih =>
    change max (Reduction.maximum.prefix 0 f i) (f i) = 1 ↔ _
    have h₁ := Reduction.max_prefix_le (by decide : 0 ≤ 1) h i
    have h₂ := h i
    have mx : max (Reduction.maximum.prefix 0 f i) (f i) = 1 ↔
        Reduction.maximum.prefix 0 f i = 1 ∨ f i = 1 := by omega
    rw [mx,ih]
    constructor
    · rintro (⟨v,hv,p⟩|p)
      · exact ⟨v,by omega,p⟩
      · exact ⟨i,by omega,p⟩
    · rintro ⟨v,hv,p⟩
      by_cases eq : v=i
      · exact Or.inr (eq ▸ p)
      · exact Or.inl ⟨v,by omega,p⟩

theorem Reduction.sum_prefix (f : ℕ → ℕ) (k : ℕ) :
    Reduction.sum.prefix 0 f k = (Finset.range k).sum f := by
  induction k with
  | zero => simp [Reduction.prefix]
  | succ i ih => rw [Reduction.prefix,Finset.sum_range_succ,ih]; rfl

/-- The output tape and every address outside a finite register set are preserved. -/
structure Frame (dirty : Finset ℕ) (s t : Store) : Prop where
  output : t.out = s.out
  read : ∀ a ∉ dirty, t.mem a = s.mem a

theorem Frame.refl (dirty : Finset ℕ) (s : Store) : Frame dirty s s := ⟨rfl,fun _ _ => rfl⟩

theorem Frame.trans {dirty : Finset ℕ} {s t u : Store} (h : Frame dirty s t) (k : Frame dirty t u) :
    Frame dirty s u := ⟨k.output.trans h.output,fun a ha => (k.read a ha).trans (h.read a ha)⟩

theorem Frame.mono {small big : Finset ℕ} {s t : Store} (h : Frame small s t) (sub : small ⊆ big) :
    Frame big s t := ⟨h.output,fun a ha => h.read a (fun z => ha (sub z))⟩

theorem Frame.write {dirty : Finset ℕ} {s t : Store} (h : Frame dirty s t) (a : ℕ)
    (ha : a ∈ dirty) (x : ℕ) : Frame dirty s (t.write a x) := by
  refine ⟨h.output,fun z hz => ?_⟩
  have dif : z ≠ a := fun eq => hz (eq ▸ ha)
  simpa only [Store.write,Function.update_of_ne dif] using h.read z hz

end TargetedSamplers.Structured

end LogCostRAMFold

section HamiltonianRAMNeighborhood

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.TripleScan

open Multidigraph Classical

def arcScratch : Finset ℕ := {40,46,47,48,49}

def tailScratch := insert 43 (insert 50 arcScratch)

def weightScratch := insert 45 (insert 51 tailScratch)

def vertexScratch := insert 44 (insert 52 weightScratch)

theorem GraphView.frame {n m W base : ℕ} {tail head : Fin m → Fin n} {w : Fin m → ℕ}
    {s t : Fin n} {u v : Store} {regs : Finset ℕ} (g : GraphView (W := W) tail head w s t base u)
    (fr : Frame regs u v) (sub : regs ⊆ vertexScratch) : GraphView (W := W) tail head w s t base v := by
  have keep := fr.mono sub
  refine ⟨g.low,g.records.congr ?_,(keep.read 30 (by decide)).trans g.source,
    (keep.read 31 (by decide)).trans g.sink,(keep.read 32 (by decide)).trans g.zero,
    (keep.read 33 (by decide)).trans g.vertices,(keep.read 34 (by decide)).trans g.weights,
    (keep.read 35 (by decide)).trans g.table,(keep.read 41 (by decide)).trans g.stop,(keep.read 42 (by decide)).trans g.unit⟩
  intro a ha
  apply keep.read
  have := g.low
  simp only [vertexScratch,weightScratch,tailScratch,arcScratch,Finset.mem_insert,Finset.mem_singleton]
  omega

theorem inspectArc_exec {τ : Tapes} {b n m W base : ℕ} {tail head : Fin m → Fin n} {w : Fin m → ℕ}
    (hw : ∀ e, w e ≤ W) {s t : Fin n} (q : ArcType (Fin n) W) (u : Store)
    (g : GraphView (W := W) tail head w s t base u) (tailWord : u.mem 43 = q.1.val)
    (headWord : u.mem 44 = q.2.1.val) (weightWord : u.mem 45 = q.2.2.val) (fit : u.Fits b) :
    ∃ z j, Exec τ (fun v => v.Fits b) inspectArc u z j ∧ j ≤ 18*m+15 ∧ Frame arcScratch u z ∧
      z.mem 46 = (if Multidigraph.retainArc (⟨tail,head⟩ : Multidigraph (Fin n) (Fin m)) w s t hw q then 1 else 0) := by
  let v := u.write 40 base
  have e : (Op.add 40 35 32).eval τ u = v := by simp [Op.eval,v,g.table,g.zero]
  have f : v.Fits b := Store.write_fits fit _ (g.table ▸ fit 35)
  have reset : Exec τ (fun st => st.Fits b) (.op (.add 40 35 32)) u v 1 := by
    simpa only [e] using (Exec.op (τ := τ) (inv := fun st => st.Fits b) u (.add 40 35 32) (e ▸ f))
  have fr := (Frame.refl arcScratch u).write 40 (by decide) base
  have view := g.frame fr (by decide)
  have key : wanted arcRegs v = (q.1.val,q.2.1.val,q.2.2.val) :=
    Prod.ext ((fr.read 43 (by decide)).trans tailWord)
      (Prod.ext ((fr.read 44 (by decide)).trans headWord) ((fr.read 45 (by decide)).trans weightWord))
  obtain ⟨z,j,run,hj,bit,result,_,out,frame⟩ := retainedQuery_exec (τ := τ) tail head w hw s t q
    arcRegs 30 31 base v view.records (fun i => by change 40+i.val < base; have := i.isLt; have := g.low; omega)
    (by change v.mem 40 = base; simp [v,Store.write]) view.stop view.unit key view.source view.sink
    (by unfold untouched; decide) (by unfold untouched; decide) f
  change z.mem 46 ≤ 1 at bit
  change z.mem 46 = 1 ↔ _ at result
  refine ⟨z,_,reset.seq run,by omega,fr.trans ⟨out,?_⟩,?_⟩
  · intro a ha
    apply frame
    change a ≠ 40 ∧ a ≠ 46 ∧ a ≠ 47 ∧ a ≠ 48 ∧ a ≠ 49
    simpa [arcScratch] using ha
  · split
    · exact result.mpr (by assumption)
    · have hnot : z.mem 46 ≠ 1 := fun h => (by assumption : ¬Multidigraph.retainArc _ w s t hw q) (result.mp h)
      omega

/-- Membership of a weight in the normalized incoming list is witnessed by a retained tail. -/
theorem normalized_incoming_iff {n m W : ℕ} (H : Multidigraph (Fin n) (Fin m)) (w : Fin m → ℕ)
    (hw : ∀ e, w e ≤ W) (s t v : Fin n) (b : Fin (W+1)) :
    b.val ∈ Multidigraph.incomingWeights (Multidigraph.normalizedGraph H w s t hw)
      (Multidigraph.normalizedWeight H w s t hw) v ↔ ∃ a : Fin n, Multidigraph.retainArc H w s t hw (a,v,b) := by
  simp only [Multidigraph.incomingWeights,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨e,he,eq⟩
    have hh : e.val.2.1 = v := he
    have hb : e.val.2.2 = b := Fin.ext eq
    have heq : e.val = (e.val.1,v,b) := Prod.ext rfl (Prod.ext hh hb)
    exact ⟨e.val.1,heq ▸ e.property⟩
  · rintro ⟨a,ha⟩
    let e : RetainedArc H w s t hw := ⟨(a,v,b),ha⟩
    exact ⟨e,rfl,rfl⟩

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMNeighborhood

section HamiltonianRAMView

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured

private theorem Parsed.terminals {n m : ℕ} {tail head : Fin m → Fin n} {w : Fin m → ℕ} {s t : Fin n}
    {B : ℤ} {u : Store} (h : Parsed tail head w s t B u) :
    u.mem (graphBase+3*m) = s.val ∧ u.mem (graphBase+3*m+1) = t.val := by
  let xs := arcFields tail head w s t
  have len : xs.length = 3*m+2 := arcFields_length ..
  have hs : 3*m < xs.length := by omega
  have ht : 3*m+1 < xs.length := by omega
  obtain ⟨a,b⟩ := arcFields_terminals tail head w s t
  change xs[3*m]? = some s.val at a
  change xs[3*m+1]? = some t.val at b
  rw [List.getElem?_eq_getElem hs] at a
  rw [List.getElem?_eq_getElem ht] at b
  exact ⟨(h.table _ hs).trans (Option.some.inj a),by simpa [Nat.add_assoc] using (h.table _ ht).trans (Option.some.inj b)⟩

set_option maxHeartbeats 900000 in
theorem prepareView_exec {τ : Tapes} {b n m : ℕ} {tail head : Fin m → Fin n} {w : Fin m → ℕ} {s t : Fin n}
    {B : ℤ} (u : Store) (h : Parsed tail head w s t B u) (fit : u.Fits b) (hw : (Finset.univ.sup w+1).size ≤ b) :
    let z := (prepareView.run τ u).last
    Exec τ (fun v => v.Fits b) prepareView.cmd u z 10 ∧
      GraphView (W := Finset.univ.sup w) tail head w s t graphBase z ∧ z.mem 53 = u.mem 1 ∧ z.out = u.out ∧
      ∀ a ≥ graphBase, z.mem a=u.mem a := by
  intro z
  have low : 60 ≤ graphBase := by decide
  have a : graphBase+(3*m+2)-1 = graphBase+3*m+1 := by omega
  have c : graphBase+3*m+1-1 = graphBase+3*m := by omega
  have outsideS (j : ℕ) (hj : j < 60) : graphBase+3*m ≠ j := by omega
  have outsideT (j : ℕ) (hj : j < 60) : graphBase+3*m+1 ≠ j := by omega
  have endRoom := h.tableEnd ▸ fit 10
  have vbase := (Nat.size_le_size (show graphBase ≤ graphBase+(3*m+2) by omega)).trans endRoom
  have vs := (Nat.size_le_size (show graphBase+3*m ≤ graphBase+(3*m+2) by omega)).trans endRoom
  have vt := (Nat.size_le_size (show graphBase+3*m+1 ≤ graphBase+(3*m+2) by omega)).trans endRoom
  have unit : (1:ℕ).size ≤ b := (Nat.size_le_size (show 1 ≤ graphBase+(3*m+2) by omega)).trans endRoom
  have one : 1 ≤ b := unit
  obtain ⟨src,dst⟩ := h.terminals
  have ww : (prepareView.run τ u).writeWidth ≤ b := by
    simp (disch := decide) [prepareView,Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,Function.update_apply,
      h.tableEnd,h.maxWeight,a,c,outsideS,outsideT,one,unit,vbase,vs,vt,hw,fit 7,fit 1,fit (graphBase+3*m),fit (graphBase+3*m+1)]
  have fields (ad : ℕ) (ha : graphBase ≤ ad) : z.mem ad = u.mem ad := by
    have far (j : ℕ) (hj : j < 60) : ad ≠ j := by omega
    simp (disch := decide) [z,prepareView,Structured.sequence,Fragment.run,Op.eval,Store.write,Function.update_apply,far]
  refine ⟨prepareView.exec τ u b fit ww,⟨low,h.records.congr fields,?_,?_,?_,?_,?_,?_,?_,?_⟩,?_,rfl,fields⟩
  all_goals simp (disch := decide) [z,prepareView,Structured.sequence,Fragment.run,Op.eval,Store.write,Function.update_apply,
    h.tableEnd,h.maxWeight,h.vertices,a,c,outsideS,outsideT,src,dst]

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMView

section HamiltonianRAMDegree

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured

open Multidigraph Classical

/-- Search all tails of one fixed head and weight. The workspace frame allows this loop
to serve directly as the body of the enclosing loop over weights. -/
theorem incomingTest_exec {τ : Tapes} {b n m W base : ℕ} {tail head : Fin m → Fin n} {w : Fin m → ℕ}
    (hw : ∀ e, w e ≤ W) {s t : Fin n} (v : Fin n) (j : Fin (W+1)) (u : Store)
    (g : GraphView (W := W) tail head w s t base u) (headWord : u.mem 44 = v.val)
    (weightWord : u.mem 45 = j.val) (fit : u.Fits b) :
    let H : Multidigraph (Fin n) (Fin m) := ⟨tail,head⟩
    let weights := Multidigraph.incomingWeights (Multidigraph.normalizedGraph H w s t hw)
      (Multidigraph.normalizedWeight H w s t hw) v
    ∃ z k, Exec τ (fun st => st.Fits b) incomingTest u z k ∧ k ≤ n*(18*m+20)+3 ∧ Frame tailScratch u z ∧
      z.mem 50 = (if j.val ∈ weights then 1 else 0) := by
  intro H weights
  let f (i : ℕ) := if hi : i < n then
    if Multidigraph.retainArc H w s t hw (⟨i,hi⟩,v,j) then 1 else 0 else 0
  have bits (i : ℕ) : f i ≤ 1 := by dsimp [f]; split <;> first | split <;> omega | omega
  have room (i : ℕ) (_ : i ≤ n) : (Reduction.maximum.prefix 0 f i).size ≤ b :=
    (Nat.size_le_size (Reduction.max_prefix_le (by decide) bits i)).trans (g.unit ▸ fit 42)
  let K := Frame tailScratch u
  have stable (z : Store) (h : K z) (a : ℕ) (ha : a = tailRegs 0 ∨ a = tailRegs 3) (x : ℕ) : K (z.write a x) := by
    apply h.write; rcases ha with rfl|rfl <;> decide
  have ctrl (z : Store) (h : K z) : z.mem (tailRegs 1) = n ∧ z.mem (tailRegs 2) = 1 ∧ z.mem (tailRegs 5) = 0 := by
    have view := g.frame h (by decide)
    exact ⟨view.vertices,view.unit,view.zero⟩
  have kernel (i : ℕ) (hi : i < n) (z : Store) (h : K z) (pos : z.mem (tailRegs 0) = i) (fz : z.Fits b) :
      ∃ a k, Exec τ (fun st => st.Fits b) inspectArc z a k ∧ k ≤ 18*m+15 ∧ K a ∧
        a.mem (tailRegs 0) = i ∧ a.mem (tailRegs 3) = z.mem (tailRegs 3) ∧ a.mem (tailRegs 4) = f i := by
    have view := g.frame h (by decide)
    obtain ⟨a,k,run,cost,frame,result⟩ := inspectArc_exec (τ := τ) hw (⟨i,hi⟩,v,j) z view pos
      ((h.read 44 (by decide)).trans headWord) ((h.read 45 (by decide)).trans weightWord) fz
    exact ⟨a,k,run,cost,h.trans (frame.mono (by decide)),(frame.read 43 (by decide)).trans pos,
      frame.read 50 (by decide),by
        change a.mem 46 = f i
        dsimp only [f,H]; rw [dif_pos hi]
        exact result⟩
  obtain ⟨z,k,run,cost,frame,_,val⟩ := Reduction.maximum.reduce_exec (τ := τ) tailRegs 0 n (18*m+15)
    inspectArc f K stable ctrl kernel room u (.refl _ _) fit
  have has : Reduction.maximum.prefix 0 f n = 1 ↔ j.val ∈ weights := by
    rw [Reduction.max_prefix_one bits,normalized_incoming_iff H w hw s t v j]
    constructor
    · rintro ⟨i,hi,hit⟩
      refine ⟨⟨i,hi⟩,?_⟩
      simpa [f,hi] using hit
    · rintro ⟨i,hit⟩
      exact ⟨i.val,i.isLt,by simp [f,i.isLt,hit]⟩
  have bound := Reduction.max_prefix_le (by decide : 0 ≤ 1) bits n
  change z.mem 50 = _ at val
  refine ⟨z,k,run,cost,frame,?_⟩
  rw [val]
  split
  · exact has.mpr (by assumption)
  · have noHit : Reduction.maximum.prefix 0 f n ≠ 1 := fun hit => (by assumption : j.val ∉ weights) (has.mp hit)
    omega

private theorem incoming_weight_lt {n m W : ℕ} (H : Multidigraph (Fin n) (Fin m)) (w : Fin m → ℕ)
    (hw : ∀ e, w e ≤ W) (s t v : Fin n) {i : ℕ} (h : i ∈ Multidigraph.incomingWeights
      (Multidigraph.normalizedGraph H w s t hw) (Multidigraph.normalizedWeight H w s t hw) v) : i < W+1 := by
  obtain ⟨a,_,ha⟩ := Finset.mem_image.mp h
  exact ha ▸ a.1.2.2.isLt

theorem countIncoming_exec {τ : Tapes} {b n m W base : ℕ} {tail head : Fin m → Fin n} {w : Fin m → ℕ}
    (hw : ∀ e, w e ≤ W) {s t : Fin n} (v : Fin n) (u : Store)
    (g : GraphView (W := W) tail head w s t base u) (headWord : u.mem 44 = v.val) (fit : u.Fits b) :
    let H : Multidigraph (Fin n) (Fin m) := ⟨tail,head⟩
    let weights := Multidigraph.incomingWeights (Multidigraph.normalizedGraph H w s t hw)
      (Multidigraph.normalizedWeight H w s t hw) v
    ∃ z k, Exec τ (fun st => st.Fits b) countIncoming u z k ∧ k ≤ (W+1)*(n*(18*m+20)+8)+3 ∧
      Frame weightScratch u z ∧ z.mem 51 = weights.card := by
  intro H weights
  let f (i : ℕ) := if i ∈ weights then 1 else 0
  have bits (i : ℕ) : f i ≤ 1 := by dsimp [f]; split <;> omega
  have bound (i : ℕ) : Reduction.sum.prefix 0 f i ≤ i := by
    induction i with
    | zero => rfl
    | succ i ih =>
      change Reduction.sum.prefix 0 f i + f i ≤ i+1
      exact Nat.add_le_add ih (bits i)
  have room (i : ℕ) (hi : i ≤ W+1) := (Nat.size_le_size ((bound i).trans hi)).trans (g.weights ▸ fit 34)
  let K := Frame weightScratch u
  have stable (z : Store) (h : K z) (a : ℕ) (ha : a = weightRegs 0 ∨ a = weightRegs 3) (x : ℕ) : K (z.write a x) := by
    apply h.write; rcases ha with rfl|rfl <;> decide
  have ctrl (z : Store) (h : K z) : z.mem (weightRegs 1) = W+1 ∧ z.mem (weightRegs 2) = 1 ∧ z.mem (weightRegs 5) = 0 := by
    have view := g.frame h (by decide)
    exact ⟨view.weights,view.unit,view.zero⟩
  have kernel (i : ℕ) (hi : i < W+1) (z : Store) (h : K z) (pos : z.mem (weightRegs 0) = i) (fz : z.Fits b) :
      ∃ a k, Exec τ (fun st => st.Fits b) incomingTest z a k ∧ k ≤ n*(18*m+20)+3 ∧ K a ∧
        a.mem (weightRegs 0) = i ∧ a.mem (weightRegs 3) = z.mem (weightRegs 3) ∧ a.mem (weightRegs 4) = f i := by
    obtain ⟨a,k,run,cost,frame,result⟩ := incomingTest_exec (τ := τ) hw v ⟨i,hi⟩ z (g.frame h (by decide))
      ((h.read 44 (by decide)).trans headWord) pos fz
    exact ⟨a,k,run,cost,h.trans (frame.mono (by decide)),(frame.read 45 (by decide)).trans pos,frame.read 51 (by decide),result⟩
  obtain ⟨z,k,run,cost,frame,_,val⟩ := Reduction.sum.reduce_exec (τ := τ) weightRegs 0 (W+1) (n*(18*m+20)+3)
    incomingTest f K stable ctrl kernel room u (.refl _ _) fit
  have bounded (i : ℕ) (hi : i ∈ weights) : i < W+1 := incoming_weight_lt H w hw s t v hi
  have eq : ((Finset.range (W+1)).filter (· ∈ weights)) = weights := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_range]
    exact ⟨And.right,fun h => ⟨bounded i h,h⟩⟩
  refine ⟨z,k,run,cost,frame,?_⟩
  change z.mem 51 = _ at val
  rw [val,Reduction.sum_prefix]
  change (∑ i ∈ Finset.range (W+1), if i ∈ weights then 1 else 0) = weights.card
  rw [Finset.sum_boole,eq,Nat.cast_id]

private theorem max_from_one (f : ℕ → ℕ) (i : ℕ) :
    Reduction.maximum.prefix 1 f i = max 1 (prefixMax f i) := by
  induction i with
  | zero => rfl
  | succ i ih => simp only [Reduction.prefix,Reduction.join,prefixMax,ih,max_assoc]

/-- Compute the exact parameter used by the trial schedule from a graph view alone. -/
theorem findSamplingDegree_exec {τ : Tapes} {b n m W base : ℕ} {tail head : Fin m → Fin n} {w : Fin m → ℕ}
    (hw : ∀ e, w e ≤ W) {s t : Fin n} (u : Store)
    (g : GraphView (W := W) tail head w s t base u) (fit : u.Fits b) :
    let H : Multidigraph (Fin n) (Fin m) := ⟨tail,head⟩
    let G := Multidigraph.normalizedGraph H w s t hw
    let p := Multidigraph.normalizedWeight H w s t hw
    ∃ z k, Exec τ (fun st => st.Fits b) findSamplingDegree u z k ∧ k ≤ n*((W+1)*(n*(18*m+20)+8)+8)+3 ∧
      Frame vertexScratch u z ∧ z.mem 52 = Multidigraph.samplingDegree G p := by
  intro H G p
  let deg (v : Fin n) := (Multidigraph.incomingWeights G p v).card
  have small (v : Fin n) : deg v ≤ W+1 := by
    have sub : Multidigraph.incomingWeights G p v ⊆ Finset.range (W+1) :=
      fun _ h => Finset.mem_range.mpr (incoming_weight_lt H w hw s t v h)
    simpa using Finset.card_le_card sub
  have bounds (i : ℕ) : weightAt deg i ≤ W+1 := by
    unfold weightAt; split <;> first | exact small _ | omega
  have room (i : ℕ) (_ : i ≤ n) := (Nat.size_le_size
    (Reduction.max_prefix_le (by omega : 1 ≤ W+1) bounds i)).trans (g.weights ▸ fit 34)
  let K := Frame vertexScratch u
  have stable (z : Store) (h : K z) (a : ℕ) (ha : a = vertexRegs 0 ∨ a = vertexRegs 3) (x : ℕ) : K (z.write a x) := by
    apply h.write; rcases ha with rfl|rfl <;> decide
  have ctrl (z : Store) (h : K z) : z.mem (vertexRegs 1) = n ∧ z.mem (vertexRegs 2) = 1 ∧ z.mem (vertexRegs 5) = 0 := by
    have view := g.frame h (by decide)
    exact ⟨view.vertices,view.unit,view.zero⟩
  let budget := (W+1)*(n*(18*m+20)+8)+3
  have kernel (i : ℕ) (hi : i < n) (z : Store) (h : K z) (pos : z.mem (vertexRegs 0) = i) (fz : z.Fits b) :
      ∃ a k, Exec τ (fun st => st.Fits b) countIncoming z a k ∧ k ≤ budget ∧ K a ∧
        a.mem (vertexRegs 0) = i ∧ a.mem (vertexRegs 3) = z.mem (vertexRegs 3) ∧ a.mem (vertexRegs 4) = weightAt deg i := by
    obtain ⟨a,k,run,cost,frame,result⟩ := countIncoming_exec (τ := τ) hw ⟨i,hi⟩ z (g.frame h (by decide)) pos fz
    exact ⟨a,k,run,cost,h.trans (frame.mono (by decide)),(frame.read 44 (by decide)).trans pos,frame.read 52 (by decide),
      by
        change a.mem 51 = weightAt deg i
        rw [weightAt,dif_pos hi]
        exact result⟩
  obtain ⟨z,k,run,cost,frame,_,val⟩ := Reduction.maximum.reduce_exec (τ := τ) vertexRegs 1 n budget
    countIncoming (weightAt deg) K stable ctrl kernel room u (.refl _ _) fit
  rw [max_from_one,prefixMax_fin] at val
  exact ⟨z,k,run,cost,frame,val⟩

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMDegree

section HamiltonianIntegerSchedule

namespace DirectedHamiltonicity.Main.Multidigraph

def trialNumerator (n d : ℕ) := (2^(d+1)-1)^(n-2)

def trialDenominator (n d : ℕ) := (2^d)^(n-2)

/-- The exact sample count uses only natural arithmetic and a positive integer divisor. -/
def integerBlockSize (n d : ℕ) :=
  2*((trialNumerator n d+trialDenominator n d-1)/trialDenominator n d)

private theorem ceil_ratio (a b : ℕ) (hb : 0 < b) : ⌈(a:ℚ)/(b:ℚ)⌉₊ = (a+b-1)/b := by
  rw [← Nat.ceilDiv_eq_add_pred_div]
  have test (c : ℕ) : ⌈(a:ℚ)/(b:ℚ)⌉₊ ≤ c ↔ a ⌈/⌉ b ≤ c := by
    rw [Nat.ceil_le,div_le_iff₀ (by exact_mod_cast hb : 0 < (b:ℚ)),ceilDiv_le_iff_le_mul hb,mul_comm b c]
    exact_mod_cast (Iff.rfl : a ≤ c*b ↔ a ≤ c*b)
  exact le_antisymm ((test _).2 le_rfl) ((test _).1 le_rfl)

theorem integerBlockSize_eq (n d : ℕ) : integerBlockSize n d = samplingBlockSize n d := by
  have den : 0 < trialDenominator n d := by dsimp [trialDenominator]; positivity
  have power : 2-(1/2:ℚ)^d = ((2^(d+1)-1 : ℕ):ℚ)/(2^d : ℕ) := by
    rw [Nat.cast_sub (Nat.one_le_two_pow (n := d+1))]
    push_cast
    rw [div_pow,one_pow,pow_succ]
    field_simp
  have ratio : (2-(1/2:ℚ)^d)^(n-2) = (trialNumerator n d:ℚ)/(trialDenominator n d:ℚ) := by
    rw [power,div_pow]
    simp only [trialNumerator,trialDenominator,Nat.cast_pow]
  rw [samplingBlockSize,ratio,ceil_ratio _ _ den]
  rfl

/-- Even the doubled dividend used by binary division has polynomially many bits.
This includes the zero exponent and does not rely on the value of the target weight. -/
theorem schedule_word_sizes (n d : ℕ) :
    let e := (d+1)*(n-2)
    let a := trialNumerator n d
    let b := trialDenominator n d
    a.size ≤ e+1 ∧ b.size ≤ e+1 ∧ (2*(a+b-1)+2).size ≤ e+3 := by
  intro e a b
  have ha : a ≤ 2^e := by
    rw [show 2^e = (2^(d+1))^(n-2) by rw [← pow_mul]]
    exact Nat.pow_le_pow_left (Nat.sub_le _ _) _
  have hb : b ≤ 2^e := by
    change (2^d)^(n-2) ≤ 2^((d+1)*(n-2))
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (Nat.le_succ d))
  have pos : 0 < 2^e := pow_pos (by decide) _
  have p₁ : 2^(e+1) = 2*2^e := by rw [pow_succ,Nat.mul_comm]
  have p₃ : 2^(e+3) = 8*2^e := by rw [pow_add]; ring
  refine ⟨Nat.size_le.mpr (by rw [p₁]; omega),Nat.size_le.mpr (by rw [p₁]; omega),
    Nat.size_le.mpr (by rw [p₃]; omega)⟩

end DirectedHamiltonicity.Main.Multidigraph

end HamiltonianIntegerSchedule

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

theorem size_twice_add_two (x : ℕ) : (2*x+2).size ≤ x.size+2 := by
  apply Nat.size_le.mpr
  have scale : 2^(x.size+2) = 4*2^x.size := by rw [pow_add]; ring
  rw [scale]
  have := Nat.lt_size_self x; omega

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

section HamiltonianRAMSchedule

namespace DirectedHamiltonicity.Main.Multidigraph

open TargetedSamplers.Structured TargetedSamplers.Structured.Word

private theorem twicePower (d : ℕ) : 2^d+2^d = 2^(d+1) := by rw [pow_succ]; omega

private theorem schedule_result (v : ℕ → ℕ) (n d : ℕ) (vn : v 0 = n) (vd : v 1 = d) :
    Circuit.result v trialSchedule 11 = samplingBlockSize n d ∧
      Circuit.result v trialSchedule 13 = samplingBlockSize n d*(n+4) := by
  rw [← integerBlockSize_eq]
  simp [Circuit.result,trialSchedule,Assignment.update,Expression.eval,Arithmetic.value,vn,vd,
    integerBlockSize,trialNumerator,trialDenominator,twicePower,two_mul,Nat.mul_comm (n+4)]

private theorem schedule_work (v : ℕ → ℕ) (n d : ℕ) (vn : v 0 = n) (vd : v 1 = d) :
    Circuit.multiplicity v trialSchedule = d+2*(n-2)+15 := by
  simp [Circuit.multiplicity,trialSchedule,Assignment.update,Expression.eval,Expression.multiplicity,vn,vd]; omega

set_option maxHeartbeats 800000 in
private theorem schedule_width (v : ℕ → ℕ) (n d : ℕ) (vn : v 0 = n) (vd : v 1 = d) :
    Circuit.width v trialSchedule ≤ scheduleWidth n d := by
  let e := (d+1)*(n-2)
  let D := 2^d
  let F := 2^(d+1)-1
  let a := trialNumerator n d
  let b := trialDenominator n d
  let x := a+b-1
  let c := x/b
  let w := scheduleWidth n d
  have bound : w = e+n+d+16 := rfl
  have Dsize : D.size = d+1 := Nat.size_pow
  have Fsize : F.size ≤ d+2 := (Nat.size_le_size (Nat.sub_le (2^(d+1)) 1)).trans_eq Nat.size_pow
  have da : (2^(d+1)).size ≤ w := by rw [Nat.size_pow]; omega
  have qsize : (n-2).size ≤ n := (Nat.size_le_size (Nat.sub_le _ _)).trans (Nat.size_le.mpr n.lt_two_pow_self)
  obtain ⟨ha,hb,_⟩ := schedule_word_sizes n d
  change a.size ≤ e+1 at ha
  change b.size ≤ e+1 at hb
  have sum := TargetedSamplers.size_add_le_succ ha hb
  have smallX : x.size ≤ e+2 := (Nat.size_le_size (Nat.sub_le (a+b) 1)).trans sum
  have smallC : c.size ≤ e+2 := (Nat.size_le_size (Nat.div_le_self x b)).trans smallX
  have dbl := TargetedSamplers.size_add_le_succ smallC smallC
  have poly : (n+4).size ≤ n+4 := Nat.size_le.mpr (n+4).lt_two_pow_self
  have prod := size_mul_le_add (n+4) (c+c)
  have Doperand := size_twice_add_two D
  have Foperand := size_twice_add_two F
  have Xoperand := size_twice_add_two x
  have Noperand := size_twice_add_two (n+4)
  have consts : (2:ℕ).size ≤ w ∧ (1:ℕ).size ≤ w ∧ (4:ℕ).size ≤ w ∧ (2*2+2:ℕ).size ≤ w := by
    have H : 4 ≤ w := by omega
    exact ⟨(by decide : (2:ℕ).size ≤ 4).trans H,(by decide : (1:ℕ).size ≤ 4).trans H,
      (by decide : (4:ℕ).size ≤ 4).trans H,(by decide : (2*2+2:ℕ).size ≤ 4).trans H⟩
  have six : (6:ℕ).size ≤ w := (by decide : (6:ℕ).size ≤ 4).trans (by omega)
  have nums : (2^(d+1)-1)^(n-2) = a := rfl
  have dens : (2^d)^(n-2) = b := rfl
  have operands : (2*D+2).size ≤ w ∧ (2*F+2).size ≤ w ∧ (2*x+2).size ≤ w ∧ (2*(n+4)+2).size ≤ w := by omega
  have values : D.size ≤ w ∧ F.size ≤ w ∧ a.size ≤ w ∧ b.size ≤ w ∧ (a+b).size ≤ w ∧ x.size ≤ w ∧ c.size ≤ w ∧
      (c+c).size ≤ w ∧ (n+4).size ≤ w ∧ ((n+4)*(c+c)).size ≤ w ∧ (n-2).size ≤ w := by omega
  change Circuit.width v trialSchedule ≤ w
  dsimp only [D,F,c,x] at operands values
  simp [Circuit.width,trialSchedule,Assignment.update,Expression.width,Expression.eval,Arithmetic.value,
    vn,vd,twicePower,nums,dens] <;> omega

/-- One fixed RAM command computes the integer schedule for all input dimensions. -/
theorem trialSchedule_exec {τ : TargetedSamplers.Tapes} {width : ℕ} (n d : ℕ) (s : Store)
    (vn : s.mem (cell 0) = n) (vd : s.mem (cell 1) = d) (fit : s.Fits width)
    (enough : scheduleWidth n d ≤ width) :
    ∃ t j, Exec τ (fun u => u.Fits width) (Circuit.cmd trialSchedule) s t j ∧ j ≤ scheduleSteps n d ∧
      t.mem (cell 11) = samplingBlockSize n d ∧ t.mem (cell 13) = samplingBlockSize n d*(n+4) ∧
      t.out = s.out ∧ ∀ i, (∀ a ∈ trialSchedule, i ≠ a.dst) → t.mem (cell i) = s.mem (cell i) := by
  let v := fun i => s.mem (cell i)
  have small := schedule_width v n d vn vd
  have hb : 2 ≤ width := by dsimp [scheduleWidth] at enough; omega
  obtain ⟨t,j,ex,hj,reg,out⟩ := Circuit.exec (τ := τ) trialSchedule v s (fun _ => rfl) fit hb (small.trans enough)
  have runtime := Circuit.steps_le trialSchedule v (scheduleWidth n d) small
  rw [schedule_work v n d vn vd] at runtime
  obtain ⟨block,trials⟩ := schedule_result v n d vn vd
  exact ⟨t,j,ex,hj.trans runtime,(reg 11).trans block,(reg 13).trans trials,out,fun i free =>
    (reg i).trans (Circuit.result_untouched trialSchedule v i free)⟩

end DirectedHamiltonicity.Main.Multidigraph

end HamiltonianRAMSchedule

section HamiltonianRAMPreprocess

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word

open Multidigraph Classical

private theorem scheduleFromView_exec {τ : Tapes} {b : ℕ} (u : Store) (n d : ℕ)
    (nv : u.mem 33 = n) (degree : u.mem 52 = d) (zero : u.mem 32 = 0)
    (fit : u.Fits b) (wh : scheduleWidth n d ≤ b) :
    ∃ z j, Exec τ (fun v => v.Fits b) scheduleFromView u z j ∧ j ≤ scheduleSteps n d+3 ∧
      z.mem 54 = samplingBlockSize n d*(n+4) ∧ z.out = u.out ∧ ∀ a ≥ 28, a ≠ 54 → z.mem a = u.mem a := by
  let v := (scheduleArgs.run τ u).last
  have ww : (scheduleArgs.run τ u).writeWidth ≤ b := by
    simp [scheduleArgs,Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,cell,zero,fit 33,fit 52]
  have args : Exec τ (fun st => st.Fits b) scheduleArgs.cmd u v 2 := scheduleArgs.exec τ u b fit ww
  have g₁ : v.mem (cell 0) = n := by simp [v,scheduleArgs,Structured.sequence,Fragment.run,Op.eval,Store.write,cell,zero,nv]
  have g₂ : v.mem (cell 1) = d := by simp [v,scheduleArgs,Structured.sequence,Fragment.run,Op.eval,Store.write,cell,zero,degree]
  obtain ⟨t,j,run,bound,_,trials,out,fr⟩ := trialSchedule_exec (τ := τ) n d v g₁ g₂ (args.post fit) wh
  have high (a : ℕ) (ha : 28 ≤ a) : t.mem a = u.mem a := by
    have lower : cell (a-14) = a := by dsimp [cell]; omega
    have dsts : trialSchedule.all (fun x => decide (x.dst < 14)) = true := by decide
    have keep := fr (a-14) (fun x hx => by
      have hd : x.dst < 14 := of_decide_eq_true (List.all_eq_true.mp dsts x hx)
      omega)
    rw [lower] at keep
    simpa [v,scheduleArgs,Structured.sequence,Fragment.run,Op.eval,Store.write,cell,
      show a ≠ 14 by omega,show a ≠ 15 by omega] using keep
  let M := samplingBlockSize n d*(n+4)
  have eq : (Op.add 54 (cell 13) 32).eval τ t = t.write 54 M := by simp [Op.eval,high 32 (by decide),zero,trials,M]
  have put : Exec τ (fun st => st.Fits b) (.op (.add 54 (cell 13) 32)) t (t.write 54 M) 1 := by
    simpa only [eq] using (Exec.op (τ := τ) (inv := fun st => st.Fits b) t (.add 54 (cell 13) 32)
      (by rw [eq]; apply Store.write_fits (run.post (args.post fit))
          change (samplingBlockSize n d*(n+4)).size ≤ b
          rw [← trials]
          exact (run.post (args.post fit)) (cell 13)))
  exact ⟨_,_,args.seq (run.seq put),by omega,by simp [Store.write,M],out,
    fun a ha hn => by simpa [Store.write,hn] using high a ha⟩

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMPreprocess

section
open DirectedHamiltonicity DirectedHamiltonicity.Main DirectedHamiltonicity.Main.InputRAM
open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word
open Multidigraph Classical

theorem solution {τ : Tapes} {b n m : ℕ} {tail head : Fin m → Fin n} {w : Fin m → ℕ}
    {s t : Fin n} {B : ℤ} (u : Store) (h : Parsed tail head w s t B u) (fit : u.Fits b) :
    let W := Finset.univ.sup w
    let hw : ∀ e, w e ≤ W := fun e => Finset.le_sup (Finset.mem_univ e)
    let H : Multidigraph (Fin n) (Fin m) := ⟨tail,head⟩
    let G := Multidigraph.normalizedGraph H w s t hw
    let p := Multidigraph.normalizedWeight H w s t hw
    let d := Multidigraph.samplingDegree G p
    (W+1).size ≤ b → scheduleWidth n d ≤ b →
    ∃ z j, Exec τ (fun v => v.Fits b) preprocess u z j ∧ j ≤ preprocessWork n m W d ∧
      GraphView (W := W) tail head w s t graphBase z ∧ z.mem 52 = d ∧ z.mem 53 = u.mem 1 ∧
      z.mem 54 = samplingBlockSize n d*(n+4) ∧ z.out = u.out ∧
      ∀ a ≥ graphBase+(3*m+2), z.mem a=0 := by
  intro W hw H G p d room wh
  let v := (prepareView.run τ u).last
  obtain ⟨setup,view,save,out₀,heap⟩ := prepareView_exec (τ := τ) u h fit room
  obtain ⟨a,k,findD,wk,frame,found⟩ := findSamplingDegree_exec (τ := τ) hw v view (setup.post fit)
  have ga := view.frame frame (by decide)
  obtain ⟨z,j,plan,wj,result,out,keep⟩ := scheduleFromView_exec (τ := τ) a n d ga.vertices found ga.zero
    (findD.post (setup.post fit)) wh
  have gz : GraphView (W := W) tail head w s t graphBase z :=
    ⟨ga.low,ga.records.congr (fun ad had => keep ad (by dsimp [graphBase] at had; omega) (by dsimp [graphBase] at had; omega)),
      (keep 30 (by decide) (by decide)).trans ga.source,(keep 31 (by decide) (by decide)).trans ga.sink,
      (keep 32 (by decide) (by decide)).trans ga.zero,(keep 33 (by decide) (by decide)).trans ga.vertices,
      (keep 34 (by decide) (by decide)).trans ga.weights,(keep 35 (by decide) (by decide)).trans ga.table,
      (keep 41 (by decide) (by decide)).trans ga.stop,(keep 42 (by decide) (by decide)).trans ga.unit⟩
  refine ⟨z,_,setup.seq (findD.seq plan),by dsimp [preprocessWork]; omega,gz,
    (keep 52 (by decide) (by decide)).trans found,
    (keep 53 (by decide) (by decide)).trans ((frame.read 53 (by decide)).trans save),
    result,out.trans (frame.output.trans out₀),?_⟩
  intro addr ha
  have baseLow : 60 ≤ graphBase := by decide
  have noReg : addr ∉ vertexScratch := by
    simp only [vertexScratch,weightScratch,tailScratch,arcScratch,Finset.mem_insert,Finset.mem_singleton]
    omega
  exact (keep addr (by omega) (by omega)).trans ((frame.read addr noReg).trans
    ((heap addr (by omega)).trans (h.free addr (by omega) (.inr ha))))
end
