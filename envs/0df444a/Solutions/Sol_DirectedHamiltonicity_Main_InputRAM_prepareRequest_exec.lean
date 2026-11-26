-- Prove2me | solution 1 for DirectedHamiltonicity.Main.InputRAM.prepareRequest_exec
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-26T17:40:39.668087+00:00
-- url     : https://prove2.me/submissions/30140f2b-0e5f-48cc-9186-ac466771b40f

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

theorem dispatch_select {τ : Tapes} {inv : Store → Prop} (key scratch : ℕ) (hne : key ≠ scratch)
    (cs : List Cmd) (base : ℕ) (s t : Store) (j : Fin cs.length) (steps : ℕ)
    (tag : s.mem key = base+j.val) (safe : ∀ v ≤ base+j.val, inv (s.write scratch v))
    (branch : Exec τ inv cs[j.val] (s.write scratch (base+j.val)) t steps) :
    Exec τ inv (dispatch key scratch base cs) s t (3*j.val+2+steps) := by
  induction cs generalizing base s with
  | nil => exact Fin.elim0 j
  | cons c cs ih =>
    cases j using Fin.cases with
    | zero =>
      have h := safe base (by simp)
      have ht : (s.write scratch base).mem key ≤ (s.write scratch base).mem scratch := by
        simp [Store.write, hne, tag]
      have he : Exec τ inv c (s.write scratch base) t steps := by simpa using branch
      simpa [dispatch, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Exec.seq (Exec.op s (.const scratch base) h) (Exec.yes (n := dispatch key scratch (base+1) cs) ht he)
    | succ i =>
      let m := s.write scratch base
      have hm : inv m := safe _ (by simp)
      have hg : ¬m.mem key ≤ m.mem scratch := by
        simp [m, Store.write, hne, tag]
      have htag : m.mem key = base+1+i.val := by
        simpa [m, Store.write, Function.update_apply, hne, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using tag
      have he := ih (base+1) m i htag (fun v hv => by
        simpa [m] using safe v (by simp at hv ⊢; omega)) (by
        simpa [m, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using branch)
      have run := Exec.seq (Exec.op s (.const scratch base) hm) (Exec.no (y := c) hg he)
      convert run using 1 <;> simp [dispatch] <;> omega

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

end TargetedSamplers.Structured

end LogCostRAMRanges

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

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMNeighborhood

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

section HamiltonianRAMGrid

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word

theorem gridCoordinates_exec {τ : Tapes} {b n width base i : ℕ} (s : Store)
    (cur : s.mem (cell 41) = base+i) (start : s.mem (cell 44) = base)
    (rows : s.mem (cell 19)=n) (cols : s.mem (cell 20)=width) (stride : s.mem (cell 43)=n*width)
    (fit : s.Fits b) (hb : 2 ≤ b) (room : (2*i+2).size ≤ b) :
    ∃ t j, Exec τ (fun u => u.Fits b) (Circuit.cmd gridCoordinates) s t j ∧
      j ≤ 5*(b*(5*b+9)+15) ∧
      t.mem 43=i/(n*width) ∧ t.mem 44=(i/width)%n ∧ t.mem 45=i%width ∧ t.out=s.out ∧
      ∀ a, 30 ≤ a → a ≠ 43 → a ≠ 44 → a ≠ 45 → t.mem a=s.mem a := by
  let v := fun j => s.mem (cell j)
  have relative : v 41-v 44=i := by simp [v,cur,start]
  have ns : v 19=n := rows
  have ws : v 20=width := cols
  have rs : v 43=n*width := stride
  have bounded (q : ℕ) (h : q ≤ 2*i+2) : q.size ≤ b := (Nat.size_le_size h).trans room
  have dh : i/width ≤ i := Nat.div_le_self ..
  have rh : i/(n*width) ≤ i := Nat.div_le_self ..
  have mh : (i/width)%n ≤ i/width := Nat.mod_le ..
  have nh : i%width ≤ i := Nat.mod_le ..
  have wmax : Circuit.width v gridCoordinates ≤ b := by
    simp (disch := decide) [gridCoordinates,Circuit.width,Expression.width,Assignment.update,Expression.eval,
      Function.update_apply,relative,ns,ws,rs,Arithmetic.value,max_le_iff]
    exact ⟨bounded _ (by omega),room,bounded _ (by omega),room,bounded _ (by omega),
      bounded _ (by omega),bounded _ (by omega),room,bounded _ (by omega)⟩
  obtain ⟨t,j,ex,w,rep,out⟩ := Circuit.exec (τ := τ) gridCoordinates v s (fun _ => rfl) fit hb wmax
  have mult : Circuit.multiplicity v gridCoordinates=5 := rfl
  have bound := (Circuit.steps_le gridCoordinates v b wmax)
  rw [mult] at bound
  refine ⟨t,j,ex,w.trans bound,?_,?_,?_,out,?_⟩
  · change t.mem (cell 29)=_
    rw [rep]; simp [gridCoordinates,Circuit.result,Assignment.update,Expression.eval,Function.update_apply,relative,rs,Arithmetic.value]
  · change t.mem (cell 30)=_
    rw [rep]; simp [gridCoordinates,Circuit.result,Assignment.update,Expression.eval,Function.update_apply,relative,ws,ns,Arithmetic.value]
  · change t.mem (cell 31)=_
    rw [rep]; simp [gridCoordinates,Circuit.result,Assignment.update,Expression.eval,Function.update_apply,relative,ws,Arithmetic.value]
  · intro a high h₁ h₂ h₃
    have hx : cell (a-14)=a := by dsimp [cell]; omega
    rw [← hx,rep]
    apply Circuit.result_untouched
    intro item mem
    simp only [gridCoordinates,List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl <;> dsimp <;> omega

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMGrid

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

section HamiltonianRAMDenseEntry

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word

open TargetedSamplers.Structured.TripleScan Multidigraph Classical

private theorem records_transport {s t : Store} {xs : List Record} {base : ℕ} (h : RecordsAt s base xs)
    (keep : ∀ a, base ≤ a → a < base+3*xs.length → t.mem a=s.mem a) : RecordsAt t base xs := by
  induction xs generalizing base with
  | nil => trivial
  | cons a xs ih =>
    obtain ⟨u,v,w,rest⟩ := h
    have range (i : ℕ) (hm : i < 3) : t.mem (base+i) = s.mem (base+i) :=
      keep _ (by omega) (by simp only [List.length_cons]; omega)
    refine ⟨by simpa using (range 0 (by decide)).trans u,(range 1 (by decide)).trans v,(range 2 (by decide)).trans w,
      ih rest (fun a lo hi => keep a (by omega) (by simp only [List.length_cons]; omega))⟩

def inView (raw m a : ℕ) : Prop := (30 ≤ a ∧ a ≤ 35) ∨ a=41 ∨ a=42 ∨ raw ≤ a ∧ a < raw+3*m

theorem transport {n m W raw : ℕ} {tail head : Fin m → Fin n} {w : Fin m → ℕ} {s t : Fin n} {u v : Store}
    (g : GraphView (W := W) tail head w s t raw u) (keep : ∀ a, inView raw m a → v.mem a = u.mem a) :
    GraphView (W := W) tail head w s t raw v := by
  refine ⟨g.low,records_transport g.records (fun a lo hi => keep a (Or.inr (Or.inr (Or.inr ⟨lo,?_⟩)))),
    (keep 30 (by unfold inView; omega)).trans g.source,(keep 31 (by unfold inView; omega)).trans g.sink,
    (keep 32 (by unfold inView; omega)).trans g.zero,(keep 33 (by unfold inView; omega)).trans g.vertices,
    (keep 34 (by unfold inView; omega)).trans g.weights,(keep 35 (by unfold inView; omega)).trans g.table,
    (keep 41 (by unfold inView; omega)).trans g.stop,(keep 42 (by unfold inView; omega)).trans g.unit⟩
  simpa [edgeRecords] using hi

def entryScratch (a : ℕ) : Prop := a=40 ∨ 43 ≤ a ∧ a ≤ 49

noncomputable def normalizedAt {n m W : ℕ} (tail head : Fin m → Fin n) (w : Fin m → ℕ)
    (hw : ∀ e, w e ≤ W) (s t : Fin n) (i : ℕ) : ℕ :=
  if h : i < n*(n*(W+1)) then
    if retainArc (⟨tail,head⟩ : Multidigraph (Fin n) (Fin m)) w s t hw (linearArc (by have := s.isLt; omega) i h)
      then 1 else 0
  else 0

theorem normalizedEntry_exec {τ : Tapes} {b n m W raw dst i : ℕ} {tail head : Fin m → Fin n} {w : Fin m → ℕ}
    (hw : ∀ e, w e ≤ W) {s t : Fin n} (u : Store) (g : GraphView (W := W) tail head w s t raw u)
    (hi : i < n*(n*(W+1))) (ptr : u.mem 55=dst+i) (base : u.mem 58=dst) (stride : u.mem 57=n*(W+1))
    (fit : u.Fits b) (hb : 2 ≤ b) (room : (2*i+2).size ≤ b) :
    ∃ z j, Exec τ (fun v => v.Fits b) normalizedEntry u z j ∧ j ≤ 5*(b*(5*b+9)+15)+18*m+15 ∧
      z.mem 46 = normalizedAt tail head w hw s t i ∧ z.out=u.out ∧
      ∀ a, 30 ≤ a → ¬entryScratch a → z.mem a=u.mem a := by
  obtain ⟨v,k,decode,wk,tails,heads,weights,ov,fr⟩ := gridCoordinates_exec (τ := τ) u ptr base g.vertices g.weights stride fit hb room
  have same (a : ℕ) (h : inView raw m a) : v.mem a=u.mem a := by
    have low := g.low
    unfold inView at h
    exact fr a (by omega) (by omega) (by omega) (by omega)
  let q := linearArc (W := W) (by have := s.isLt; omega : 0 < n) i hi
  obtain ⟨z,l,check,wl,frame,val⟩ := inspectArc_exec (τ := τ) hw q v (transport g same) tails heads weights (decode.post fit)
  refine ⟨z,_,decode.seq check,by omega,by simpa [normalizedAt,hi,q] using val,frame.output.trans ov,?_⟩
  intro a ha free
  unfold entryScratch at free
  exact (frame.read a (by simp only [arcScratch,Finset.mem_insert,Finset.mem_singleton]; omega)).trans
    (fr a ha (by omega) (by omega) (by omega))

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMDenseEntry

section HamiltonianRAMDenseTable

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured Multidigraph

theorem normalizedTable_exec {τ : Tapes} {b n m W raw dst : ℕ} {tail head : Fin m → Fin n} {w : Fin m → ℕ}
    (hw : ∀ e, w e ≤ W) {s t : Fin n} (u : Store) (g : GraphView (W := W) tail head w s t raw u)
    (separate : raw+3*m ≤ dst) (ptr : u.mem 55=dst) (endAt : u.mem 56=dst+n*(n*(W+1)))
    (stride : u.mem 57=n*(W+1)) (base : u.mem 58=dst) (fit : u.Fits b) (hb : 2 ≤ b)
    (space : (dst+n*(n*(W+1))).size ≤ b) (room : (2*(n*(n*(W+1)))+2).size ≤ b) :
    let count := n*(n*(W+1))
    ∃ z j, Exec τ (fun v => v.Fits b) normalizedTable u z j ∧
      j ≤ count*(5*(b*(5*b+9)+15)+18*m+19)+1 ∧ GraphView (W := W) tail head w s t raw z ∧
      z.mem 55=dst+count ∧ z.out=u.out ∧
      (∀ a ≥ dst, z.mem a = if a < dst+count then normalizedAt tail head w hw s t (a-dst) else u.mem a) ∧
      ∀ a, 30 ≤ a → ¬entryScratch a → a ≠ 55 → a < dst → z.mem a=u.mem a := by
  intro count
  have low := g.low
  let K (v : Store) := GraphView (W := W) tail head w s t raw v ∧ v.mem 56=dst+count ∧
    v.mem 57=n*(W+1) ∧ v.mem 58=dst ∧
      ∀ a, 30 ≤ a → ¬entryScratch a → a ≠ 55 → a < dst → v.mem a=u.mem a
  have initial : K u := ⟨g,endAt,stride,base,fun _ _ _ _ _ => rfl⟩
  have bounds (a : ℕ) (ha : inView raw m a) : a < dst ∧ a ≠ 55 ∧ 30 ≤ a ∧ ¬entryScratch a := by
    unfold inView at ha
    unfold entryScratch
    omega
  have stable (v : Store) (h : K v) (a val : ℕ) (pos : a=55 ∨ dst ≤ a ∧ a < dst+count) : K (v.write a val) := by
    have same (i : ℕ) (hl : i < dst) (hd : i ≠ 55) : (v.write a val).mem i=v.mem i := by
      simp [Store.write,show i ≠ a by omega]
    exact ⟨transport h.1 (fun i hi => same i (bounds i hi).1 (bounds i hi).2.1),
      (same 56 (by omega) (by decide)).trans h.2.1,(same 57 (by omega) (by decide)).trans h.2.2.1,
      (same 58 (by omega) (by decide)).trans h.2.2.2.1,
      fun i hi free ptr top => (same i top ptr).trans (h.2.2.2.2 i hi free ptr top)⟩
  have body (i : ℕ) (hi : i < count) (v : Store) (h : K v) (cur : v.mem 55=dst+i) (fv : v.Fits b) :
      ∃ z j, Exec τ (fun r => r.Fits b) normalizedEntry v z j ∧ j ≤ 5*(b*(5*b+9)+15)+18*m+15 ∧
        K z ∧ z.mem 55=dst+i ∧ z.mem 46=normalizedAt tail head w hw s t i ∧ z.out=v.out ∧ ∀ a ≥ dst, z.mem a=v.mem a := by
    obtain ⟨z,j,ex,work,val,out,keep⟩ := normalizedEntry_exec (τ := τ) hw v h.1 hi cur h.2.2.2.1 h.2.2.1 fv hb
      ((Nat.size_le_size (by change 2*i+2 ≤ 2*count+2; omega)).trans room)
    have kz : K z := ⟨transport h.1 (fun i hi => keep i (bounds i hi).2.2.1 (bounds i hi).2.2.2),
      (keep 56 (by decide) (by unfold entryScratch; omega)).trans h.2.1,(keep 57 (by decide) (by unfold entryScratch; omega)).trans h.2.2.1,
      (keep 58 (by decide) (by unfold entryScratch; omega)).trans h.2.2.2.1,
      fun i hl free ptr top => (keep i hl free).trans (h.2.2.2.2 i hl free ptr top)⟩
    exact ⟨z,j,ex,work,kz,(keep 55 (by decide) (by unfold entryScratch; omega)).trans cur,val,out,
      fun a ha => keep a (by omega) (by unfold entryScratch; omega)⟩
  obtain ⟨z,j,ex,work,kz,done,out,cells⟩ := tabulate_exec (τ := τ) 55 56 42 46 dst count
    (5*(b*(5*b+9)+15)+18*m+15) normalizedEntry _ K (fun v h => ⟨h.2.1,h.1.unit⟩) stable (by omega)
    body space u initial ptr fit
  exact ⟨z,j,ex,by exact work,kz.1,done,out,cells,kz.2.2.2.2⟩

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMDenseTable

section HamiltonianRAMBuildGrid

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word

theorem buildNormalizedGrid_exec {τ : Tapes} {b n m W raw : ℕ} {tail head : Fin m → Fin n} {w : Fin m → ℕ}
    (hw : ∀ e, w e ≤ W) {s t : Fin n} (reserve : ℕ) (u : Store) (g : GraphView (W := W) tail head w s t raw u)
    (fit : u.Fits b) (hb : 2 ≤ b) :
    let dst := raw+3*m+(reserve+2)
    let count := n*(n*(W+1))
    (dst+2*count+2*n+2).size ≤ b →
    ∃ z j, Exec τ (fun v => v.Fits b) (buildNormalizedGrid reserve) u z j ∧
      j ≤ 6*(b*(5*b+9)+15)+count*(5*(b*(5*b+9)+15)+18*m+19)+1 ∧
      GraphView (W := W) tail head w s t raw z ∧ z.out=u.out ∧
      (∀ a ≥ dst, z.mem a = if a < dst+count then normalizedAt tail head w hw s t (a-dst) else u.mem a) ∧
      (∀ a, 50 ≤ a → a < 55 → z.mem a=u.mem a) ∧ z.mem 55=dst+count ∧ z.mem 58=dst := by
  intro dst count room
  let v := fun i => u.mem (cell i)
  have nval : v 19=n := g.vertices
  have wval : v 20=W+1 := g.weights
  have zero : v 18=0 := g.zero
  have stop : v 27=raw+3*m := g.stop
  have one : 1 ≤ n := by have := s.isLt; omega
  have row : n*(W+1) ≤ count := by
    dsimp [count]
    simpa using Nat.mul_le_mul_right (n*(W+1)) one
  have upper (v : ℕ) (h : v ≤ dst+2*count+2*n+2) : v.size ≤ b := (Nat.size_le_size h).trans room
  have wfit : Circuit.width v (gridSetup reserve) ≤ b := by
    simp [gridSetup,Circuit.width,Assignment.update,Expression.width,Expression.eval,Function.update_apply,
      nval,wval,zero,stop,Arithmetic.value,max_le_iff]
    dsimp [dst,count] at *
    repeat' apply And.intro
    all_goals first | exact room | apply upper <;> omega
  obtain ⟨a,i,init,wi,rep,ret⟩ := Circuit.exec (τ := τ) (gridSetup reserve) v u (fun _ => rfl) fit hb wfit
  have mul : Circuit.multiplicity v (gridSetup reserve)=6 := rfl
  have wi' := wi.trans (Circuit.steps_le _ _ _ wfit)
  rw [mul] at wi'
  have vals : a.mem 55=dst ∧ a.mem 56=dst+count ∧ a.mem 57=n*(W+1) ∧ a.mem 58=dst := by
    change a.mem (cell 41)=dst ∧ a.mem (cell 42)=dst+count ∧ a.mem (cell 43)=n*(W+1) ∧ a.mem (cell 44)=dst
    rw [rep 41,rep 42,rep 43,rep 44]
    simp [gridSetup,Circuit.result,Assignment.update,Expression.eval,Function.update_apply,nval,wval,zero,stop,
      Arithmetic.value,dst,count,Nat.add_comm]
  have fixed (x : ℕ) (h : 30 ≤ x ∧ (x < 55 ∨ 59 < x)) : a.mem x=u.mem x := by
    have addr : cell (x-14)=x := by dsimp [cell]; omega
    rw [← addr,rep]
    apply Circuit.result_untouched
    intro item mem
    simp only [gridSetup,List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl <;> dsimp <;> omega
  have low := g.low
  have ga := transport g (fun x hx => fixed x (by unfold inView at hx; omega))
  have dstge : raw+3*m ≤ dst := by dsimp [dst]; omega
  obtain ⟨z,j,make,wj,gz,finish,out,data,keep⟩ := normalizedTable_exec (τ := τ) hw a ga dstge vals.1 vals.2.1 vals.2.2.1 vals.2.2.2
    (init.post fit) hb (upper _ (by omega)) (upper _ (by omega))
  change j ≤ count*(5*(b*(5*b+9)+15)+18*m+19)+1 at wj
  refine ⟨z,_,init.seq make,by omega,gz,out.trans ret,?_,?_,finish,?_⟩
  · intro x hx
    rw [data x hx,fixed x (by omega)]
  · intro x xl xh
    exact (keep x (by omega) (by unfold entryScratch; omega) (by omega) (by omega)).trans (fixed x (by omega))
  · exact (keep 58 (by decide) (by unfold entryScratch; omega) (by decide) (by omega)).trans vals.2.2.2

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMBuildGrid

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

/-- The three fixed constants used by the stack and finite-control instructions. -/
structure Constants (s : Store) : Prop where
  one : s.mem (cell 1) = 1
  two : s.mem (cell 2) = 2
  zero : s.mem (cell 5) = 0

theorem push_exec {τ : TargetedSamplers.Tapes} {b : ℕ} (k : ℕ) (hk : 8 ≤ k) (bit : Bool)
    (xs : List Bool) (s : Store) (c : Constants s) (v : s.mem (cell k) = packed xs) (fit : s.Fits b)
    (room : xs.length+2 ≤ b) :
    ∃ t j, Exec τ (fun u => u.Fits b) (push k bit) s t j ∧ j ≤ 2 ∧
      t.mem (cell k) = packed (bit::xs) ∧ t.out = s.out ∧ ∀ a, a ≠ cell k → t.mem a = s.mem a := by
  let x := packed xs
  let u := s.write (cell k) (x+x)
  have ev : (Op.add (cell k) (cell k) (cell k)).eval τ s = u := by simp [Op.eval,u,x,v]
  have size : (x+x).size ≤ b := by
    have e : x+x = packed (false::xs) := by simp [packed_cons,x]
    rw [e,packed_size,List.length_cons]; omega
  have fu := Store.write_fits fit (cell k) size
  have first : Exec τ (fun st => st.Fits b) (.op (.add (cell k) (cell k) (cell k))) s u 1 := by
    simpa only [ev] using (Exec.op (τ := τ) (inv := fun st => st.Fits b) s (.add (cell k) (cell k) (cell k)) (by rw [ev]; exact fu))
  cases bit with
  | false => exact ⟨u,1,first,by decide,by simp [u,Store.write,packed_cons,x],rfl,fun a h => by simp [u,Store.write,h]⟩
  | true =>
    have diff : cell 1 ≠ cell k := by simp [cell]; omega
    have e : (Op.add (cell k) (cell k) (cell 1)).eval τ u = u.write (cell k) (packed (true::xs)) := by
      simp [Op.eval,u,Store.write,diff,c.one,packed_cons,x]
    have second := Exec.op (τ := τ) (inv := fun st => st.Fits b) u (.add (cell k) (cell k) (cell 1))
      (by rw [e]; exact Store.write_fits fu _ (by rw [packed_size,List.length_cons]; omega))
    exact ⟨_,2,first.seq second,le_rfl,by rw [e]; simp [Store.write],rfl,
      fun a h => by rw [e]; simp [u,Store.write,h]⟩

end TargetedSamplers.Structured.BinaryStack

end PackedBinaryStacks

section HamiltonianAdjacencyBits

namespace DirectedHamiltonicity.Main.NativeGraph

open Multidigraph InputRAM Classical TargetedSamplers.Structured.BinaryStack

variable {n m W : ℕ} (H : Multidigraph (Fin n) (Fin m)) (w : Fin m → ℕ) (hw : ∀ e, w e ≤ W) (s t : Fin n)

@[simp] theorem adjacencyBits_length : (adjacencyBits H w hw s t).length=n*(n*(W+1)) := by simp [adjacencyBits]

theorem adjacencyBits_cell (i : ℕ) (hi : i < n*(n*(W+1))) :
    ((adjacencyBits H w hw s t)[i]'(by simpa using hi)).toNat =
      normalizedAt H.tail H.head w hw s t i := by
  simp only [adjacencyBits,List.getElem_ofFn,normalizedAt,dif_pos hi]
  split <;> simp_all

end DirectedHamiltonicity.Main.NativeGraph

end HamiltonianAdjacencyBits

section PackedBitWriter

namespace TargetedSamplers.Structured.BinaryStack

open Word

theorem prepend_exec {τ : Tapes} {b : ℕ} (dst : ℕ) (hdst : 8 ≤ dst) (tail : List Bool) (s : Store)
    (c : Constants s) (value : s.mem (cell dst) = packed tail) (fit : s.Fits b)
    (bits : List Bool) (room : bits.length+tail.length+1 ≤ b) :
    ∃ t j, Exec τ (fun u => u.Fits b) (prepend dst bits) s t j ∧ j ≤ 2*bits.length ∧
      t.mem (cell dst) = packed (bits++tail) ∧ t.out=s.out ∧ ∀ a, a ≠ cell dst → t.mem a = s.mem a := by
  induction bits with
  | nil => exact ⟨s,0,.skip s,by simp,by simpa using value,rfl,fun _ _ => rfl⟩
  | cons bit bs ih =>
    have space : bs.length+tail.length+1 ≤ b := by simp only [List.length_cons] at room; omega
    obtain ⟨u,i,run,w,acc,out,fr⟩ := ih space
    have uc : Constants u := ⟨(fr _ (by simp [cell]; omega)).trans c.one,
      (fr _ (by simp [cell]; omega)).trans c.two,(fr _ (by simp [cell]; omega)).trans c.zero⟩
    obtain ⟨t,j,p,wp,val,done,keep⟩ := push_exec (τ := τ) dst hdst bit (bs++tail) u uc acc (run.post fit)
      (by simp only [List.length_cons,List.length_append] at *; omega)
    exact ⟨t,_,run.seq p,by simp only [List.length_cons]; omega,val,done.trans out,fun a h => (keep a h).trans (fr a h)⟩

end TargetedSamplers.Structured.BinaryStack

end PackedBitWriter

section SerializedTokenRAM

namespace TargetedSamplers.Structured.BinaryStack

open Word

structure TokenState (base ptr : ℕ) (suffix : List Bool) (s : Store) : Prop where
  constants : Constants s
  value : s.mem (cell 8) = packed suffix
  cursor : s.mem (cell 9) = ptr
  start : s.mem (cell 10) = base

structure TokenFrame (s t : Store) : Prop where
  out : t.out = s.out
  high : ∀ a, cell 12 < a → t.mem a = s.mem a

theorem tokenStep_exec {τ : Tapes} {b base i : ℕ} (words : List (List Bool)) (token : Fin words.length)
    (tail : List Bool) (s : Store) (st : TokenState base (base+i+1) tail s)
    (tape : s.mem (base+i) = token.val) (disjoint : cell 12 < base) (fit : s.Fits b)
    (room : words[token.val].length+tail.length+1 ≤ b) :
    ∃ t j, Exec τ (fun u => u.Fits b) (tokenStep words) s t j ∧
      j ≤ 3*token.val+4+2*words[token.val].length ∧
      TokenState base (base+i) (words[token.val]++tail) t ∧ TokenFrame s t := by
  let p := base+i
  let u := s.write (cell 9) p
  let v := u.write (cell 11) token.val
  let z := v.write (cell 12) token.val
  have cn (a d : ℕ) : cell a = cell d ↔ a=d := by simp [cell]
  have away (j : ℕ) (hj : j ≤ 12) : p ≠ cell j := by dsimp [p,cell] at *; omega
  have move : (Op.sub (cell 9) (cell 9) (cell 1)).eval τ s = u := by simp [Op.eval,u,p,st.cursor,st.constants.one]
  have fu : u.Fits b := Store.write_fits fit _ ((Nat.size_le_size (show p ≤ base+i+1 by dsimp [p]; omega)).trans (st.cursor ▸ fit (cell 9)))
  have rd : (Op.load (cell 11) (cell 9)).eval τ u = v := by
    simp [v,u,Op.eval,Store.write,away _ (by decide : 9 ≤ 12),p,tape]
  have ft : token.val.size ≤ b := tape ▸ fit (base+i)
  have fv : v.Fits b := Store.write_fits fu _ ft
  have fz : z.Fits b := Store.write_fits fv _ ft
  have ex1 : Exec τ (fun u => u.Fits b) (.op (.sub (cell 9) (cell 9) (cell 1))) s u 1 := by
    simpa only [move] using (Exec.op (τ := τ) (inv := fun u => u.Fits b) s (.sub (cell 9) (cell 9) (cell 1)) (move ▸ fu))
  have ex2 : Exec τ (fun u => u.Fits b) (.op (.load (cell 11) (cell 9))) u v 1 := by
    simpa only [rd] using (Exec.op (τ := τ) (inv := fun u => u.Fits b) u (.load (cell 11) (cell 9)) (rd ▸ fv))
  have zz : Constants z := by
    constructor <;> simp [z,v,u,Store.write,cn,st.constants.one,st.constants.two,st.constants.zero]
  obtain ⟨t,j,arm,w,result,out,frame⟩ := prepend_exec (τ := τ) 8 le_rfl tail z zz
    (by simp [z,v,u,Store.write,cn,st.value]) fz words[token.val] room
  let codes := words.map (prepend 8)
  let k := token.cast (List.length_map (f := prepend 8)).symm
  have selected : codes[k.val] = prepend 8 words[token.val] := by simp [codes,k]
  have kk : k.val = token.val := by simp [k]
  have sel := dispatch_select (τ := τ) (inv := fun u => u.Fits b) (cell 11) (cell 12) (by decide)
    codes 0 v t k j (by simp [k,v,Store.write]) (fun x hx => Store.write_fits fv _ ((Nat.size_le_size (by simpa [k] using hx)).trans ft))
    (by rw [selected]; simpa only [Nat.zero_add,kk,z] using arm)
  have fixed (a : ℕ) (ha : a ≠ 8) : t.mem (cell a) = z.mem (cell a) := frame _ (cn _ _ |>.not.mpr ha)
  refine ⟨t,_,ex1.seq (ex2.seq sel),?_,⟨⟨(fixed 1 (by decide)).trans zz.one,
    (fixed 2 (by decide)).trans zz.two,(fixed 5 (by decide)).trans zz.zero⟩,result,?_,?_⟩,⟨out,?_⟩⟩
  · dsimp [k]; omega
  · rw [fixed 9 (by decide)]; simp [z,v,u,Store.write,cn,p]
  · rw [fixed 10 (by decide)]; simp [z,v,u,Store.write,cn,st.start]
  · intro a ha
    have far (x : ℕ) (hx : x ≤ 12) : a ≠ cell x := by dsimp [cell] at *; omega
    rw [frame _ (far 8 (by decide))]
    simp [z,v,u,Store.write,far]

/-- Serialize an entire RAM table of finite tags. The work is linear in the number
of tags for each fixed codebook. No previously stored workspace value is consulted. -/
theorem encodeTokens_exec {τ : Tapes} {b base maxLen : ℕ} (words : List (List Bool))
    (bounded : ∀ i : Fin words.length, words[i.val].length ≤ maxLen) (xs : List (Fin words.length))
    (tail : List Bool) (s : Store) (st : TokenState base (base+xs.length) tail s)
    (tape : ∀ k (h : k < xs.length), s.mem (base+k) = (xs[k]).val)
    (disjoint : cell 12 < base) (fit : s.Fits b)
    (room : (xs.flatMap (fun k => words[k.val])).length+tail.length+1 ≤ b) :
    ∃ t j, Exec τ (fun u => u.Fits b) (encodeTokens words) s t j ∧
      j ≤ xs.length*(3*words.length+2*maxLen+6)+1 ∧
      TokenState base base ((xs.flatMap (fun k => words[k.val]))++tail) t ∧ TokenFrame s t := by
  induction xs using List.reverseRecOn generalizing tail s with
  | nil =>
    refine ⟨s,1,.done (by simpa [st.cursor,st.start]),by simp,?_,rfl,fun _ _ => rfl⟩
    simpa using st
  | append_singleton xs a ih =>
    let chunk := words[a.val]
    have pos : TokenState base (base+xs.length+1) tail s := by simpa [Nat.add_assoc] using st
    have data : s.mem (base+xs.length) = a.val := by simpa using tape xs.length (by simp)
    have space : (xs.flatMap (fun k => words[k.val])).length+chunk.length+tail.length+1 ≤ b := by
      simpa [chunk,List.flatMap_append] using room
    obtain ⟨u,i,first,wi,mid,fr⟩ := tokenStep_exec (τ := τ) words a tail s pos data disjoint fit (by dsimp [chunk] at space; omega)
    have sub (k : ℕ) (hk : k < xs.length) : u.mem (base+k) = (xs[k]).val := by
      rw [fr.high _ (by omega)]
      exact (tape k (by simp; omega)).trans (by simp [List.getElem_append_left,hk])
    obtain ⟨t,j,rest,wj,post,done⟩ := ih (chunk++tail) u mid sub (first.post fit) (by rw [List.length_append]; omega)
    have keep : TokenFrame s t := ⟨done.out.trans fr.out,fun a h => (done.high a h).trans (fr.high a h)⟩
    refine ⟨t,_,.again (by rw [pos.cursor,pos.start]; omega) first rest,?_,?_,keep⟩
    · have := bounded a
      have := a.isLt
      rw [List.length_append,List.length_singleton,Nat.succ_mul xs.length (3*words.length+2*maxLen+6)]
      omega
    · simpa [List.flatMap_append,List.append_assoc,chunk] using post

end TargetedSamplers.Structured.BinaryStack

end SerializedTokenRAM

section PackedMemoryBits

namespace TargetedSamplers.Structured.BinaryStack

open Word

private def token (b : Bool) : Fin binaryCode.length := ⟨b.toNat,by cases b <;> decide⟩

/-- Read a contiguous ordinary bit table, packing its true length in the high
sentinel. Zero bits at either end are retained, as is every other heap cell. -/
theorem packMemory_exec {τ : Tapes} {b base : ℕ} (xs : List Bool) (s : Store)
    (high : cell 12 < base) (endAt : s.mem (cell 9)=base+xs.length) (beginAt : s.mem (cell 10)=base)
    (data : ∀ i (hi : i < xs.length), s.mem (base+i)=xs[i].toNat) (fit : s.Fits b) (hb : 2 ≤ b)
    (space : xs.length+1 ≤ b) :
    ∃ t j, Exec τ (fun u => u.Fits b) packMemory s t j ∧ j ≤ 14*xs.length+5 ∧
      t.mem (cell 8)=packed xs ∧ t.out=s.out ∧ ∀ a, cell 12 < a → t.mem a=s.mem a := by
  let u := (emptyWord.run τ s).last
  have two : (2:ℕ).size=2 := by decide
  have ww : (emptyWord.run τ s).writeWidth ≤ b := by
    simp [emptyWord,Structured.sequence,Fragment.run,Op.written,Op.eval,two]; omega
  have start : Exec τ (fun v => v.Fits b) emptyWord.cmd s u 4 := emptyWord.exec τ s b fit ww
  have diff (i j : ℕ) : (cell i=cell j) ↔ i=j := by simp [cell]
  have highFrame (a : ℕ) (ha : cell 8 < a) : u.mem a=s.mem a := by
    have off (i : ℕ) (h : i ≤ 8) : a ≠ cell i := by dsimp [cell] at *;omega
    simp (disch := omega) [u,emptyWord,Structured.sequence,Fragment.run,Op.eval,Store.write,Function.update_apply,off]
  let tokens : List (Fin binaryCode.length) := xs.map token
  have init : TokenState base (base+tokens.length) [] u := by
    refine ⟨⟨?_,?_,?_⟩,?_,?_,?_⟩
    · simp [u,emptyWord,Structured.sequence,Fragment.run,Op.eval,Store.write,diff]
    · simp [u,emptyWord,Structured.sequence,Fragment.run,Op.eval,Store.write,diff]
    · simp [u,emptyWord,Structured.sequence,Fragment.run,Op.eval,Store.write,diff]
    · simp [u,emptyWord,Structured.sequence,Fragment.run,Op.eval,Store.write,diff]
    · simpa [tokens] using (highFrame (cell 9) (by decide)).trans endAt
    · exact (highFrame (cell 10) (by decide)).trans beginAt
  have bits : tokens.flatMap (fun i => binaryCode[i.val])=xs := by
    have digit (b : Bool) : binaryCode[(token b).val]=[b] := by cases b <;> rfl
    simp [tokens,List.flatMap_map,Function.comp_def,digit]
  have tab (i : ℕ) (hi : i < tokens.length) : u.mem (base+i)=tokens[i].val := by
    rw [highFrame _ (by dsimp [cell] at high ⊢;omega)]
    simpa [tokens,token] using data i (by simpa [tokens] using hi)
  have bound (i : Fin binaryCode.length) : binaryCode[i.val].length ≤ 1 := by
    have hi : i.val < 2 := i.isLt
    rcases (show i.val=0 ∨ i.val=1 by omega) with h|h <;> simp [h,binaryCode]
  obtain ⟨t,j,walk,cost,result,frame⟩ := encodeTokens_exec (τ := τ) binaryCode bound tokens [] u init tab high
    (start.post fit) (by simpa [bits] using space)
  refine ⟨t,_,start.seq walk,?_,by simpa only [bits,List.append_nil] using result.value,frame.out,?_⟩
  · change j ≤ tokens.length*14+1 at cost
    simp only [tokens,List.length_map] at cost
    omega
  · intro a ha
    exact (frame.high a ha).trans (highFrame a (by dsimp [cell] at *;omega))

end TargetedSamplers.Structured.BinaryStack

end PackedMemoryBits

section HamiltonianRAMGraphArgument

namespace DirectedHamiltonicity.Main.InputRAM

open Multidigraph NativeGraph TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word

open TargetedSamplers.Structured.BinaryStack

/-- The fixed graph preparation program produces a packed adjacency argument
directly from the parsed multigraph. Source, sink, target, trial count and the
untouched heap above the workspace are available to the caller. -/
theorem packNormalizedGrid_exec {τ : Tapes} {b n m W raw : ℕ} {tail head : Fin m → Fin n} {w : Fin m → ℕ}
    (hw : ∀ e, w e ≤ W) {s t : Fin n} (reserve : ℕ) (u : Store) (g : GraphView (W := W) tail head w s t raw u)
    (fit : u.Fits b) (hb : 2 ≤ b) :
    let H : Multidigraph (Fin n) (Fin m) := ⟨tail,head⟩
    let dst := raw+3*m+(reserve+2)
    let N := n*(n*(W+1))
    (dst+2*N+2*n+2).size ≤ b → N+1 ≤ b →
    ∃ z j, Exec τ (fun v => v.Fits b) (packNormalizedGrid reserve) u z j ∧
      j ≤ 6*(b*(5*b+9)+15)+N*(5*(b*(5*b+9)+15)+18*m+19)+14*N+8 ∧
      z.mem (cell 8)=packed (adjacencyBits H w hw s t) ∧ z.out=u.out ∧
      GraphView (W := W) tail head w s t raw z ∧ z.mem 55=dst+N ∧
      (∀ a, 50 ≤ a → a < 55 → z.mem a=u.mem a) ∧ ∀ a ≥ dst+N,z.mem a=u.mem a := by
  intro H dst N room width
  obtain ⟨v,j,grid,work,gv,out,table,saved,finish,beginAt⟩ := buildNormalizedGrid_exec (τ := τ) hw reserve u g fit hb room
  let a := (copyBounds.run τ v).last
  have low := gv.low
  have fv := grid.post fit
  have fitsBounds : (copyBounds.run τ v).writeWidth ≤ b := by
    simp [copyBounds,Structured.sequence,Fragment.run,Op.written,Op.eval,Store.write,cell,gv.zero]
    exact ⟨fv 55,fv 58⟩
  have copy : Exec τ (fun v => v.Fits b) copyBounds.cmd v a 2 := copyBounds.exec τ v b fv fitsBounds
  have keep (i : ℕ) (hi : cell 10 < i) : a.mem i=v.mem i := by
    have n9 : i ≠ cell 9 := by dsimp [cell] at *;omega
    have n10 : i ≠ cell 10 := by omega
    simp [a,copyBounds,Structured.sequence,Fragment.run,Op.eval,Store.write,n9,n10]
  let xs := adjacencyBits H w hw s t
  have size : xs.length=N := adjacencyBits_length H w hw s t
  have last : a.mem (cell 9)=dst+xs.length := by
    simp [a,copyBounds,Structured.sequence,Fragment.run,Op.eval,Store.write,cell,gv.zero,finish,size,N,dst]
  have first : a.mem (cell 10)=dst := by
    simp [a,copyBounds,Structured.sequence,Fragment.run,Op.eval,Store.write,cell,gv.zero,beginAt,dst]
  have data (i : ℕ) (hi : i < xs.length) : a.mem (dst+i)=xs[i].toNat := by
    have ix : i < N := hi.trans_le size.le
    rw [keep _ (by dsimp [cell,dst];omega),table _ (by omega),if_pos (Nat.add_lt_add_left ix dst),Nat.add_sub_cancel_left]
    exact (adjacencyBits_cell H w hw s t i ix).symm
  obtain ⟨z,k,pack,cost,val,ret,fr⟩ := packMemory_exec (τ := τ) xs a (by dsimp [cell,dst];omega)
    last first data (copy.post fv) hb (by rwa [size])
  have stable (i : ℕ) (hi : 30 ≤ i) : z.mem i=v.mem i :=
    (fr i (by dsimp [cell];omega)).trans (keep i (by dsimp [cell];omega))
  change j ≤ 6*(b*(5*b+9)+15)+N*(5*(b*(5*b+9)+15)+18*m+19)+1 at work
  rw [size] at cost
  refine ⟨z,_,grid.seq (copy.seq pack),by omega,val,ret.trans out,transport gv (fun i h => stable i
    (by unfold inView at h;omega)),(stable 55 (by decide)).trans finish,
    fun i lo hi => (stable i (by omega)).trans (saved i lo hi),?_⟩
  intro i hi
  rw [stable i (by dsimp [dst] at hi;omega),table i (by omega),if_neg (by omega)]

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMGraphArgument

section HamiltonianRAMCapture

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured

theorem captureGraph_exec {τ : TargetedSamplers.Tapes} {b : ℕ} (base : ℕ) (u : Store)
    (above : 60 ≤ base) (zero : u.mem 32=0) (fit : u.Fits b) :
    let v := ((captureGraph base).run τ u).last
    Exec τ (fun s => s.Fits b) (captureGraph base).cmd u v 8 ∧ v.out=u.out ∧
      v.mem (base+0)=u.mem 33 ∧ v.mem (base+1)=u.mem 34 ∧ v.mem (base+2)=u.mem 30 ∧ v.mem (base+3)=u.mem 31 ∧
      v.mem (base+4)=u.mem 22 ∧ v.mem (base+10)=u.mem 54 ∧ v.mem (base+11)=u.mem 53 ∧ v.mem (base+26)=u.mem 55 ∧
      ∀ a, base+26 < a → v.mem a=u.mem a := by
  intro v
  have low (a j : ℕ) (ha : a < 60) : a ≠ base+j := by omega
  have away (a : ℕ) (ha : a < 60) : a ≠ base := by omega
  have width : ((captureGraph base).run τ u).writeWidth ≤ b := by
    simp (disch := omega) [captureGraph,Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,
      Function.update_apply,low,away,zero]
    exact ⟨fit _,fit _,fit _,fit _,fit _,fit _,fit _,fit _⟩
  refine ⟨(captureGraph base).exec τ u b fit width,rfl,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals first
    | intro a ha
      simp (disch := omega) [v,captureGraph,Structured.sequence,Fragment.run,Op.eval,Store.write,Function.update_apply]
    | simp (disch := omega) [v,captureGraph,Structured.sequence,Fragment.run,Op.eval,Store.write,Function.update_apply,
        low,away,zero]

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMCapture

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

section HamiltonianRequestWidth

namespace DirectedHamiltonicity.Main.InputRAM

theorem argumentWidth_room (n h : ℕ) :
    let N := n*(n*h)
    N+1 ≤ argumentWidth n h ∧ n*(N+1)+1 ≤ argumentWidth n h ∧ n+h+8 ≤ argumentWidth n h := by
  intro N
  simp only [argumentWidth,Nat.succ_mul]
  dsimp [N]
  omega

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRequestWidth

section HamiltonianRAMFieldSetup

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word

private theorem width_append (v : ℕ → ℕ) (xs ys : List Assignment) :
    Circuit.width v (xs++ys)=max (Circuit.width v xs) (Circuit.width (Circuit.result v xs) ys) := by
  induction xs generalizing v with
  | nil => simp [Circuit.width,Circuit.result]
  | cons a xs ih => simp only [List.cons_append,Circuit.width,Circuit.result,ih,max_assoc]

theorem initFields_values (v : ℕ → ℕ) :
    let u := Circuit.result v initFields
    let w := argumentWidth (v 0) (v 1)
    u 9=2^w ∧ u 12=v 0-2 ∧ u 19=12*v 10 ∧ u 27=w ∧ u 23=0 ∧ u 24=1 ∧ u 25=2 ∧
      u 5=0 ∧ u 6=0 ∧ u 7=0 ∧ u 8=0 ∧ u 22=0 ∧ u 65=0 ∧ u 66=v 10 ∧ u 67=1 ∧ u 68=0 := by
  simp [initFields,initDimensions,initLimits,initCursors,Circuit.result,Assignment.update,Expression.eval,Arithmetic.value,Function.update_apply,argumentWidth]

theorem initFields_destinations (a : Assignment) (ha : a∈initFields) :
    5 ≤ a.dst ∧ a.dst ≠ 10 ∧ a.dst ≠ 11 ∧ a.dst ≠ 26 ∧ a.dst ≤ 68 := by
  have check : initFields.all (fun h => decide (5 ≤ h.dst ∧ h.dst ≠ 10 ∧ h.dst ≠ 11 ∧ h.dst ≠ 26 ∧ h.dst ≤ 68))=true := by decide
  exact of_decide_eq_true (List.all_eq_true.mp check a ha)

theorem initFields_work (v : ℕ → ℕ) :
    Circuit.multiplicity v initFields=argumentWidth (v 0) (v 1)+initFields.length := by
  simp [initFields,initDimensions,initLimits,initCursors,Circuit.multiplicity,Expression.multiplicity,Assignment.update,Expression.eval,Arithmetic.value,
    Function.update_apply,argumentWidth,Nat.add_assoc] <;> omega

set_option maxHeartbeats 800000 in
theorem initFields_width (v : ℕ → ℕ) (b : ℕ) (hn : 1 ≤ v 0)
    (room : argumentWidth (v 0) (v 1)+2 ≤ b) (total : (12*v 10).size ≤ b) :
    Circuit.width v initFields ≤ b := by
  let n := v 0
  let h := v 1
  let N := n*(n*h)
  let top := argumentWidth n h
  have base : n+1 ≤ (n+1)*(N+1) := by
    simpa using Nat.mul_le_mul_left (n+1) (Nat.succ_le_succ (Nat.zero_le N))
  have grid : N+1 ≤ (n+1)*(N+1) := by
    simpa using Nat.mul_le_mul_right (N+1) (Nat.succ_le_succ (Nat.zero_le n))
  have slice : n*h ≤ N := by simpa [N] using Nat.mul_le_mul_right (n*h) hn
  have wh : top+2 ≤ b := room
  have small (z : ℕ) (hz : z ≤ top+2) : z.size ≤ b := (Nat.size_le.mpr z.lt_two_pow_self).trans (hz.trans wh)
  have pw : (2^top).size ≤ b := by rw [Nat.size_pow];omega
  have sizeM : (v 10).size ≤ b := (Nat.size_le_size (show v 10 ≤ 12*v 10 by omega)).trans total
  let u := Circuit.result v initDimensions
  let y := Circuit.result u initLimits
  have dims : u 27=top ∧ u 10=v 10 ∧ u 25=2 ∧ u 23=0 := by
    simp [u,initDimensions,Circuit.result,Assignment.update,Expression.eval,Arithmetic.value,top,argumentWidth,N,n,h]
  have rest : y 10=v 10 ∧ y 23=0 := by
    simp [y,initLimits,Circuit.result,Assignment.update,dims.2.1,dims.2.2.2]
  rw [initFields,List.append_assoc,width_append]
  apply max_le
  · simp [initDimensions,Circuit.width,Assignment.update,Expression.eval,Expression.width,Arithmetic.value]
    dsimp [top,argumentWidth,N,n,h] at base grid slice small
    repeat' apply And.intro
    all_goals first | apply small <;> omega | omega
  · change Circuit.width u (initLimits++initCursors) ≤ b
    rw [width_append]
    apply max_le
    · have bmin : 16 ≤ b := by dsimp [argumentWidth] at room;omega
      have six : (6:ℕ).size ≤ b := (by decide : (6:ℕ).size ≤ 16).trans bmin
      have twelve : (12:ℕ).size ≤ b := (by decide : (12:ℕ).size ≤ 16).trans bmin
      have operand : (26:ℕ).size ≤ b := (by decide : (26:ℕ).size ≤ 16).trans bmin
      simp [initLimits,Circuit.width,Assignment.update,Expression.eval,Expression.width,Arithmetic.value,
        dims.1,dims.2.1,dims.2.2.1,pw,total,six,twelve,operand] <;> omega
    · change Circuit.width y initCursors ≤ b
      simp [initCursors,Circuit.width,Assignment.update,Expression.eval,Expression.width,rest.1,rest.2,sizeM] <;> omega

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMFieldSetup

section
open DirectedHamiltonicity DirectedHamiltonicity.Main DirectedHamiltonicity.Main.InputRAM
open Multidigraph NativeGraph TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word
open TargetedSamplers.Structured.BinaryStack

theorem solution {τ : Tapes} {b n m W raw : ℕ} {tail head : Fin m → Fin n} {w : Fin m → ℕ}
    (hw : ∀ e, w e ≤ W) {s t : Fin n} (bank M D : ℕ) (u : Store)
    (view : GraphView (W := W) tail head w s t raw u) (trials : u.mem 54=M) (target : u.mem 53=D)
    (high : 60 ≤ cell bank) (fit : u.Fits b) (hb : 2 ≤ b) :
    let H : Multidigraph (Fin n) (Fin m) := ⟨tail,head⟩
    let wbits := argumentWidth n (W+1)
    let N := n*(n*(W+1))
    let dst := raw+3*m+2
    let L := b*(5*b+9)+15
    (dst+2*N+2*n+2).size ≤ b → wbits+2 ≤ b → (12*M).size ≤ b →
    ∃ z j, Exec τ (fun v => v.Fits b) (prepareRequest bank) u z j ∧
      j ≤ 6*L+N*(5*L+18*m+19)+14*N+16+(wbits+initFields.length)*L ∧
      PreparedRequest (cell bank) n (W+1) s.val t.val (packed (adjacencyBits H w hw s t)) M D (dst+N) z ∧
      z.out=u.out ∧ ∀ i, cell bank+68 < i → dst+N ≤ i → z.mem i=u.mem i := by
  intro H wbits N dst L gridRoom wordRoom capRoom
  have Nroom : N+1 ≤ b := (argumentWidth_room n (W+1)).1.trans (by omega)
  obtain ⟨v,j,grid,wj,key,ret,gv,endAt,frozen,above⟩ :=
    packNormalizedGrid_exec (τ := τ) hw 0 u view fit hb gridRoom Nroom
  let a := cell bank
  let y := ((captureGraph a).run τ v).last
  obtain ⟨copy,retY,nv,wh,src,sink,graph,tr,goal,stopAt,frame⟩ :=
    captureGraph_exec (τ := τ) a v high gv.zero (grid.post fit)
  let args := fun i => y.mem (cell (bank+i))
  have reg (i : ℕ) : args i=y.mem (a+i) := by simp [args,a,cell,Nat.add_assoc]
  have rn : args 0=n := (reg 0).trans (nv.trans gv.vertices)
  have rh : args 1=W+1 := (reg 1).trans (wh.trans gv.weights)
  have rs : args 2=s.val := (reg 2).trans (src.trans gv.source)
  have rt : args 3=t.val := (reg 3).trans (sink.trans gv.sink)
  have rg : args 4=packed (adjacencyBits H w hw s t) := (reg 4).trans (graph.trans key)
  have rm : args 10=M := (reg 10).trans (tr.trans ((frozen _ (by decide) (by decide)).trans trials))
  have rd : args 11=D := (reg 11).trans (goal.trans ((frozen _ (by decide) (by decide)).trans target))
  have re : args 26=dst+N := (reg 26).trans (stopAt.trans endAt)
  have right : Circuit.width args initFields ≤ b := initFields_width args b (by rw [rn];have := s.isLt;omega)
    (by rwa [rn,rh]) (by rwa [rm])
  obtain ⟨z,k,setup,wk,res,retZ,keep⟩ := Circuit.bank_exec (τ := τ) bank initFields y (copy.post (grid.post fit)) hb right
  have result (i : ℕ) : z.mem (a+i)=Circuit.result args initFields i := by
    change z.mem (cell bank+i)=_
    rw [show cell bank+i=cell (bank+i) by simp [cell,Nat.add_assoc]]
    exact res i
  have saved (i : ℕ) (hi : i ≤ 4 ∨ i=10 ∨ i=11 ∨ i=26) : z.mem (a+i)=args i := by
    rw [result];apply Circuit.result_untouched
    intro h hh;have := initFields_destinations h hh;omega
  have vals := initFields_values args
  simp only [← result,rn,rh,rm] at vals
  obtain ⟨rad,dim,cap,width,zero,one,two,q5,q6,q7,q8,par,cur,limit,stride,total⟩ := vals
  have state : PreparedRequest a n (W+1) s.val t.val (packed (adjacencyBits H w hw s t)) M D (dst+N) z :=
    ⟨⟨(saved 0 (by decide)).trans rn,(saved 1 (by decide)).trans rh,(saved 2 (by decide)).trans rs,
      (saved 3 (by decide)).trans rt,(saved 4 (by decide)).trans rg,rad⟩,⟨q5,q6,q7,q8⟩,
      (saved 10 (by decide)).trans rm,(saved 11 (by decide)).trans rd,dim,cap,par,zero,one,two,
      (saved 26 (by decide)).trans re,width,cur,limit,stride,total⟩
  change k ≤ Circuit.multiplicity args initFields*L at wk
  rw [initFields_work,rn,rh] at wk
  change j ≤ 6*L+N*(5*L+18*m+19)+14*N+8 at wj
  refine ⟨z,_,grid.seq (copy.seq setup),by dsimp [wbits] at *;omega,state,retZ.trans (retY.trans ret),?_⟩
  intro i hi ge
  have hold := keep i (by omega) (fun h hh => by
    have := (initFields_destinations h hh).2.2.2.2
    dsimp [a,cell] at *;omega)
  exact hold.trans ((frame i (by omega)).trans (above i ge))
end
