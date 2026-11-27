-- Prove2me | solution 1 for DirectedHamiltonicity.Main.CycleHost.readGraph_exec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T04:02:49.706267+00:00
-- url     : https://prove2.me/submissions/c89d9ac5-7cc6-4b25-a6e6-f4f56f12d6d0

import Definitions.Def_LogCostRAM_StructuredExecution
import Definitions.Def_DirectedHamiltonicity_CycleSearchHost

-- ===== Solutions/Dev/Lib.lean =====

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
namespace BoundedBinaryInput
theorem fold_bits (x : ℕ) : x.bits.foldr Nat.bit 0 = x := by
  induction x using Nat.binaryRec' with
  | zero => rfl
  | bit b x h ih => simp [Nat.bits_append_bit x b h, ih]

end BoundedBinaryInput
section LogCostRAMBinaryRead

namespace TargetedSamplers.Structured.BinaryRead

/-- Registers in order: input cursor, accumulator, binary place value, continuation
marker, digit, zero and one. The input and following fields may be arbitrarily long. -/
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
/-- One continuation marker causes a digit read, one accumulation at its place value, and
a lookahead to the following marker. No length instruction is used. -/
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

/-- A field's payload followed by its terminator is scanned in at most ten steps per
digit and one final guard. The proof frames the next field on the input tape. -/
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

/-- Decode a canonical little-endian field, advancing to its successor. The contents and
length of the suffix never enter the instruction, time or word-width bound. -/
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

end LogCostRAMBinaryRead

section LogCostRAMFieldArray

namespace TargetedSamplers.Structured.BinaryRead

def field (x : ℕ) := pairs x.bits ++ [false]

def fields (xs : List ℕ) := xs.flatMap field

theorem field_length (x : ℕ) : (field x).length = 2*x.size+1 := by
  have h (bs : List Bool) : (pairs bs).length = 2*bs.length := by
    induction bs with
    | nil => rfl
    | cons y ys ih =>
      change (pairs ys).length+1+1 = 2*(ys.length+1)
      rw [ih]; omega
  simp [field,h,Nat.size_eq_bits_len]

def fieldWork (xs : List ℕ) := (xs.map (fun x => 10*x.size+12)).sum

/-- Decode a stream of self-delimiting natural numbers directly into consecutive memory
words. The following input suffix is never read, even to find its length. -/
theorem readFields_exec (r : Fin 7 ↪ ℕ) (count dest : ℕ) (cd : count ≠ dest)
    (cr : ∀ i, count ≠ r i) (dr : ∀ i, dest ≠ r i) {τ : Tapes} {width : ℕ}
    (xs : List ℕ) (rest : List Bool) (p dst : ℕ) (s : Store)
    (ptr : s.mem (r 0) = p) (hc : s.mem count = xs.length) (hd : s.mem dest = dst)
    (hz : s.mem (r 5) = 0) (fit : s.Fits width) (hb : 2 ≤ width)
    (data : ∀ x ∈ xs, x.size+1 ≤ width) (hw : (p+(fields xs).length).size ≤ width)
    (dw : (dst+xs.length).size ≤ width) (low : count < dst ∧ dest < dst ∧ ∀ i, r i < dst)
    (input : τ.input.drop p = fields xs ++ rest) :
    ∃ t j, Exec τ (fun st => st.Fits width) (readFields r count dest) s t j ∧ j ≤ fieldWork xs+1 ∧
      t.mem (r 0) = p+(fields xs).length ∧ t.mem count = 0 ∧ t.mem dest = dst+xs.length ∧
      (∀ i (hi : i < xs.length), t.mem (dst+i) = xs[i]) ∧ t.out = s.out ∧
      ∀ a, a ≠ count → a ≠ dest → (∀ i, a ≠ r i) → (a < dst ∨ dst+xs.length ≤ a) → t.mem a = s.mem a := by
  induction xs generalizing s p dst with
  | nil =>
    exact ⟨s,1,.done (by rw [hc,hz]; rfl),by simp [fieldWork],by simpa [fields] using ptr,hc,
      by simpa using hd,by simp,rfl,fun _ _ _ _ _ => rfl⟩
  | cons x xs ih =>
    let next := p+(field x).length
    have parts : fields (x::xs) = field x ++ fields xs := rfl
    have sum : p+(fields (x::xs)).length = next+(fields xs).length := by simp [parts,next,Nat.add_assoc]
    have hinput : τ.input.drop p = pairs x.bits ++ false :: (fields xs++rest) := by
      simpa [parts,field,List.append_assoc] using input
    have midSize : (p+2*x.size+1).size ≤ width := by
      apply (Nat.size_le_size ?_).trans hw
      simp [parts,field_length]; omega
    obtain ⟨u,k,read,hk,pu,au,zu,ou,outu,frame⟩ := readField_exec (τ := τ) r p x (fields xs++rest) s ptr
      hinput fit hb midSize (data x (by simp))
    have fu := read.post fit
    have uc := (frame count cr).trans hc
    have ud := (frame dest dr).trans hd
    let u₁ := u.write dst x
    let u₂ := u₁.write dest (dst+1)
    let v := u₂.write count xs.length
    have ed : (Op.store dest (r 1)).eval τ u = u₁ := by simp [Op.eval,u₁,au,ud]
    have f₁ : u₁.Fits width := Store.write_fits fu dst (au ▸ fu (r 1))
    have st : Exec τ (fun z => z.Fits width) (.op (.store dest (r 1))) u u₁ 1 := by
      simpa only [ed] using (Exec.op (τ := τ) (inv := fun z => z.Fits width) u (.store dest (r 1)) (by rwa [ed]))
    have saved (a : ℕ) (ha : a < dst) : u₁.mem a = u.mem a := by simp [u₁,Store.write,ha.ne]
    have einc : (Op.add dest dest (r 6)).eval τ u₁ = u₂ := by
      simp [Op.eval,u₂,saved dest low.2.1,saved (r 6) (low.2.2 6),ud,ou]
    have f₂ : u₂.Fits width := Store.write_fits f₁ _ ((Nat.size_le_size (by simp : dst+1 ≤ dst+(x::xs).length)).trans dw)
    have inc : Exec τ (fun z => z.Fits width) (.op (.add dest dest (r 6))) u₁ u₂ 1 := by
      simpa only [einc] using (Exec.op (τ := τ) (inv := fun z => z.Fits width) u₁ (.add dest dest (r 6)) (by rwa [einc]))
    have saved' (a : ℕ) (ha : a < dst) (hne : a ≠ dest) : u₂.mem a = u.mem a := by
      simpa [u₂,Store.write,hne] using saved a ha
    have edec : (Op.sub count count (r 6)).eval τ u₂ = v := by
      simp [Op.eval,v,saved' count low.1 cd,saved' (r 6) (low.2.2 6) (dr 6).symm,uc,ou]
    have cw : xs.length.size ≤ width :=
      (Nat.size_le_size (show xs.length ≤ (x::xs).length by simp)).trans (uc ▸ fu count)
    have fv : v.Fits width := Store.write_fits f₂ count cw
    have dec : Exec τ (fun z => z.Fits width) (.op (.sub count count (r 6))) u₂ v 1 := by
      simpa only [edec] using (Exec.op (τ := τ) (inv := fun z => z.Fits width) u₂ (.sub count count (r 6)) (by rwa [edec]))
    have reg (i : Fin 7) : v.mem (r i) = u.mem (r i) := by
      simpa [v,Store.write,(cr i).symm] using saved' (r i) (low.2.2 i) (dr i).symm
    have unaffected (a : ℕ) (hc' : a ≠ count) (hd' : a ≠ dest) (ha : ∀ i, a ≠ r i) (n : a ≠ dst) :
        v.mem a = s.mem a := by simpa [v,u₂,u₁,Store.write,hc',hd',n] using frame a ha
    have pnext : v.mem (r 0) = next := by simpa [next,field_length,Nat.add_assoc] using (reg 0).trans pu
    have nextInput : τ.input.drop next = fields xs++rest := by
      rw [show next = p+(field x).length from rfl, ← List.drop_drop,input,parts,List.append_assoc,List.drop_left]
    obtain ⟨t,j,loop,hj,pt,ct,dt,words,ot,fr⟩ := ih next (dst+1) v pnext (by simp [v,Store.write])
      (by simp [v,u₂,Store.write,cd.symm]) ((reg 5).trans zu) fv (fun y hy => data y (by simp [hy]))
      (sum ▸ hw) (by simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using dw)
      ⟨by have := low.1; omega,by have := low.2.1; omega,fun i => by have := low.2.2 i; omega⟩ nextInput
    have body := read.seq (st.seq (inc.seq dec))
    have go : ¬s.mem count ≤ s.mem (r 5) := by simp [hc,hz]
    refine ⟨t,_,.again go body loop,?_,sum ▸ pt,ct,?_,?_,ot.trans outu,?_⟩
    · simp only [fieldWork,List.map_cons,List.sum_cons] at hj ⊢
      omega
    · simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using dt
    · intro i hi
      cases i with
      | zero =>
        have old := fr dst low.1.ne.symm low.2.1.ne.symm (fun i => (low.2.2 i).ne.symm) (.inl (by omega))
        simpa [v,u₂,u₁,Store.write,low.1.ne.symm,low.2.1.ne.symm] using old
      | succ i => simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using words i (by simpa using hi)
    · intro a nc nd nr out
      have sh : a < dst+1 ∨ dst+1+xs.length ≤ a := by simp only [List.length_cons] at out; omega
      exact (fr a nc nd nr sh).trans (unaffected a nc nd nr (by simp only [List.length_cons] at out; omega))

end TargetedSamplers.Structured.BinaryRead

end LogCostRAMFieldArray
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


-- ===== Solutions/Dev/HostSpecs.lean =====


-- ===== Solutions/Dev/ReadGraph.lean =====

set_option autoImplicit false

namespace DirectedHamiltonicity.Main.CycleHost

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word
open TargetedSamplers.Structured.Interp DirectedHamiltonicity.Main.CycleReduction

namespace RGC

theorem mem_write (s : Store) (d v a : ℕ) : (s.write d v).mem a = if a = d then v else s.mem a := by
  simp [Store.write, Function.update_apply]

@[simp] theorem out_write (s : Store) (d v : ℕ) : (s.write d v).out = s.out := rfl

theorem size_le_of_lt {x b : ℕ} (h : x < 2 ^ b) : x.size ≤ b := Nat.size_le.mpr h

theorem asg_lit {τ : Tapes} {b : ℕ} (s : Store) (d x : ℕ) (fit : s.Fits b) (w : x.size ≤ b) :
    Exec τ (fun w => w.Fits b) (asg d (.literal x)).cmd s (s.write (cell d) x) 1 :=
  Exec.op s (.const (cell d) x) (Store.write_fits fit _ w)

theorem asg_add {τ : Tapes} {b : ℕ} (s : Store) (d l r : ℕ) (fit : s.Fits b)
    (w : (s.mem (cell l) + s.mem (cell r)).size ≤ b) :
    Exec τ (fun w => w.Fits b) (asg d (.add l r)).cmd s
      (s.write (cell d) (s.mem (cell l) + s.mem (cell r))) 1 :=
  Exec.op s (.add (cell d) (cell l) (cell r)) (Store.write_fits fit _ w)

theorem circ_cons {τ : Tapes} {I : Store → Prop} {a : Assignment} {as : List Assignment}
    {s m t : Store} {k1 k2 : ℕ} (h1 : Exec τ I a.cmd s m k1) (h2 : Exec τ I (circ as) m t k2) :
    Exec τ I (circ (a :: as)) s t (k1 + k2) := Exec.seq h1 h2

theorem circ_nil {τ : Tapes} {I : Store → Prop} (s : Store) : Exec τ I (circ []) s s 0 := Exec.skip s

theorem circ_one {τ : Tapes} {I : Store → Prop} {a : Assignment} {s t : Store} {k : ℕ}
    (h : Exec τ I a.cmd s t k) : Exec τ I (circ [a]) s t k := by
  simpa using circ_cons h (circ_nil t)

/-- Accumulated binary number from a bit function. -/
def bitsAcc (f : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | e + 1 => bitsAcc f e + if f e then 2 ^ e else 0

theorem bitsAcc_lt (f : ℕ → Bool) (e : ℕ) : bitsAcc f e < 2 ^ e := by
  induction e with
  | zero => simp [bitsAcc]
  | succ e ih =>
    simp only [bitsAcc, pow_succ]
    split <;> omega

theorem bitsAcc_testBit (f : ℕ → Bool) (e k : ℕ) (hk : k < e) : (bitsAcc f e).testBit k = f k := by
  induction e with
  | zero => omega
  | succ e ih =>
    simp only [bitsAcc]
    have hl := bitsAcc_lt f e
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
    · split
      · rw [Nat.add_comm, Nat.testBit_two_pow_add_gt hk, ih hk]
      · rw [Nat.add_zero, ih hk]
    · subst hk
      split
      · rename_i h
        rw [Nat.add_comm, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hl, h]; rfl
      · rename_i h
        rw [Nat.add_zero, Nat.testBit_lt_two_pow hl]; simpa using h

theorem flatMap_get {α β : Type} (g : α → List β) (m : ℕ) (hg : ∀ a, (g a).length = m)
    (l : List α) (k y : ℕ) (hy : y < m) :
    (l.flatMap g)[k * m + y]? = (l[k]?).bind (fun a => (g a)[y]?) := by
  induction l generalizing k with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons]
    cases k with
    | zero =>
      rw [Nat.zero_mul, Nat.zero_add, List.getElem?_append_left (by rw [hg]; exact hy)]
      simp
    | succ k =>
      rw [List.getElem?_append_right (by rw [hg]; nlinarith)]
      rw [hg, show (k + 1) * m + y - m = k * m + y by rw [Nat.succ_mul]; omega, ih]
      simp

theorem input_bit {n : ℕ} (adj : Fin n → Fin n → Bool) (x y : Fin n) :
    (encodeDigraph n adj)[2 * n.size + 1 + (x.val * n + y.val)]? = some (adj x y) := by
  unfold encodeDigraph
  have hl : (encNat n).length = 2 * n.size + 1 := BinaryRead.field_length n
  rw [List.getElem?_append_right (by omega), hl, Nat.add_sub_cancel_left,
    flatMap_get _ n (by simp) _ _ _ y.isLt]
  simp

theorem size_bitVal (o : Option Bool) : (bitVal o).size ≤ 2 := by
  apply Nat.size_le.mpr
  cases o with
  | none => simp [bitVal]
  | some x => cases x <;> simp [bitVal]

/-- One iteration of the `readGraph` loop. -/
theorem rg_body {τ : Tapes} {b : ℕ} (s : Store) (fit : s.Fits b) (hb : 2 ≤ b) (cur e g p : ℕ)
    (hcur : s.mem (cell rCur) = cur) (he : s.mem (cell rE) = e) (hg : s.mem (cell rG) = g)
    (hp : s.mem (cell rPow) = p) (hz : s.mem (cell rZero) = 0)
    (w1 : (cur + e).size ≤ b) (w2 : (g + p).size ≤ b) (w3 : (p + p).size ≤ b) :
    ∃ t k, Exec τ (fun w => w.Fits b) (.seq (circ [asg rAddr (.add rCur rE)])
      (.seq (.op (.input (cell rCoin) (cell rAddr)))
        (.seq (ifLe rCoin rZero .skip (circ [asg rG (.add rG rPow)]))
          (circ [asg rPow (.add rPow rPow)])))) s t k ∧ k ≤ 6 ∧ t.out = s.out ∧
      t.mem (cell rG) = g + (if 0 < bitVal τ.input[cur + e]? then p else 0) ∧
      t.mem (cell rPow) = p + p ∧
      ∀ a, a ≠ cell rG → a ≠ cell rPow → a ≠ cell rAddr → a ≠ cell rCoin → t.mem a = s.mem a := by
  have e1 := circ_one (asg_add (τ := τ) s rAddr rCur rE fit (by rw [hcur, he]; exact w1))
  set s1 := s.write (cell rAddr) (s.mem (cell rCur) + s.mem (cell rE)) with hs1
  have f1 := e1.post fit
  have hv : s1.mem (cell rAddr) = cur + e := by simp [s1, mem_write, hcur, he]
  have e2 := Exec.op (τ := τ) (inv := fun w => w.Fits b) s1 (.input (cell rCoin) (cell rAddr))
    (Store.write_fits f1 _ ((size_bitVal _).trans hb))
  set c := bitVal τ.input[cur + e]? with hc
  have hs2 : (Op.input (cell rCoin) (cell rAddr)).eval τ s1 = s1.write (cell rCoin) c := by
    simp [Op.eval, hv, c]
  rw [hs2] at e2
  set s2 := s1.write (cell rCoin) c with hs2'
  have f2 := e2.post f1
  have m2 : ∀ a, a ≠ cell rAddr → a ≠ cell rCoin → s2.mem a = s.mem a := by
    intro a h1 h2; simp [s2, s1, mem_write, h1, h2]
  have c2 : s2.mem (cell rCoin) = c := by simp [s2, mem_write]
  have z2 : s2.mem (cell rZero) = 0 := by rw [m2 _ (by simp [cell, rZero, rAddr]) (by simp [cell, rZero, rCoin]), hz]
  have g2 : s2.mem (cell rG) = g := by rw [m2 _ (by simp [cell, rG, rAddr]) (by simp [cell, rG, rCoin]), hg]
  have p2 : s2.mem (cell rPow) = p := by rw [m2 _ (by simp [cell, rPow, rAddr]) (by simp [cell, rPow, rCoin]), hp]
  -- the branch
  obtain ⟨s3, k3, e3, hk3, g3, p3, o3, m3⟩ : ∃ s3 k3, Exec τ (fun w => w.Fits b)
      (ifLe rCoin rZero .skip (circ [asg rG (.add rG rPow)])) s2 s3 k3 ∧ k3 ≤ 3 ∧
      s3.mem (cell rG) = g + (if 0 < c then p else 0) ∧ s3.mem (cell rPow) = p ∧
      s3.out = s2.out ∧ ∀ a, a ≠ cell rG → s3.mem a = s2.mem a := by
    by_cases h : c ≤ 0
    · refine ⟨s2, _, Exec.yes (by rw [c2, z2]; exact h) (Exec.skip _), by omega, ?_, p2, rfl,
        fun _ _ => rfl⟩
      rw [g2, if_neg (by omega)]; rfl
    · have e := circ_one (asg_add (τ := τ) s2 rG rG rPow f2 (by rw [g2, p2]; exact w2))
      refine ⟨_, _, Exec.no (by rw [c2, z2]; exact h) e, by omega, ?_, ?_, rfl, ?_⟩
      · simp [mem_write, g2, p2]; omega
      · rw [mem_write, if_neg (by simp [cell, rPow, rG]), p2]
      · intro a ha; rw [mem_write, if_neg ha]
  have f3 := e3.post f2
  have e4 := circ_one (asg_add (τ := τ) s3 rPow rPow rPow f3 (by rw [p3]; exact w3))
  refine ⟨_, _, Exec.seq e1 (Exec.seq e2 (Exec.seq e3 e4)), by omega, ?_, ?_, ?_, ?_⟩
  · simp only [out_write]; rw [o3]; rfl
  · rw [mem_write, if_neg (by simp [cell, rPow, rG]), g3]
  · rw [mem_write, if_pos rfl, p3]
  · intro a h1 h2 h3 h4
    rw [mem_write, if_neg h2, m3 a h1, m2 a h3 h4]

theorem bitsAcc_sum (f : ℕ → Bool) (e : ℕ) :
    bitsAcc f e = ∑ j : Fin e, (f j.val).toNat * 2 ^ j.val := by
  induction e with
  | zero => simp [bitsAcc]
  | succ e ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, ← ih, bitsAcc]
    cases f e <;> simp

/-- One iteration of the `readSeed` loop. -/
theorem rs_body {τ : Tapes} {b : ℕ} (s : Store) (fit : s.Fits b) (hb : 2 ≤ b) (pos e g p : ℕ)
    (hpos : s.mem (cell rSeedPos) = pos) (he : s.mem (cell rJ) = e) (hg : s.mem (cell rDv) = g)
    (hp : s.mem (cell rPow) = p) (hz : s.mem (cell rZero) = 0) (h1 : s.mem (cell rOne) = 1)
    (w1 : (pos + e).size ≤ b) (w2 : (g + p).size ≤ b) (w3 : (p + p).size ≤ b) :
    ∃ t k, Exec τ (fun w => w.Fits b) (.seq (circ [asg rAddr (.add rSeedPos rJ)])
      (.seq (.op (.coin (cell rCoin) (cell rAddr)))
        (.seq (ifLe rCoin rZero .skip (ifLe rCoin rOne (circ [asg rDv (.add rDv rPow)]) .skip))
          (circ [asg rPow (.add rPow rPow)])))) s t k ∧ k ≤ 7 ∧ t.out = s.out ∧
      t.mem (cell rDv) = g + (if (τ.coins[pos + e]?.getD false) then p else 0) ∧
      t.mem (cell rPow) = p + p ∧
      ∀ a, a ≠ cell rDv → a ≠ cell rPow → a ≠ cell rAddr → a ≠ cell rCoin → t.mem a = s.mem a := by
  have e1 := circ_one (asg_add (τ := τ) s rAddr rSeedPos rJ fit (by rw [hpos, he]; exact w1))
  set s1 := s.write (cell rAddr) (s.mem (cell rSeedPos) + s.mem (cell rJ)) with hs1
  have f1 := e1.post fit
  have hv : s1.mem (cell rAddr) = pos + e := by simp [s1, mem_write, hpos, he]
  have e2 := Exec.op (τ := τ) (inv := fun w => w.Fits b) s1 (.coin (cell rCoin) (cell rAddr))
    (Store.write_fits f1 _ ((size_bitVal _).trans hb))
  set c := bitVal τ.coins[pos + e]? with hc
  have hs2 : (Op.coin (cell rCoin) (cell rAddr)).eval τ s1 = s1.write (cell rCoin) c := by
    simp [Op.eval, hv, c]
  rw [hs2] at e2
  set s2 := s1.write (cell rCoin) c with hs2'
  have f2 := e2.post f1
  have m2 : ∀ a, a ≠ cell rAddr → a ≠ cell rCoin → s2.mem a = s.mem a := by
    intro a h1 h2; simp [s2, s1, mem_write, h1, h2]
  have c2 : s2.mem (cell rCoin) = c := by simp [s2, mem_write]
  have z2 : s2.mem (cell rZero) = 0 := by rw [m2 _ (by simp [cell, rZero, rAddr]) (by simp [cell, rZero, rCoin]), hz]
  have o2 : s2.mem (cell rOne) = 1 := by rw [m2 _ (by simp [cell, rOne, rAddr]) (by simp [cell, rOne, rCoin]), h1]
  have g2 : s2.mem (cell rDv) = g := by rw [m2 _ (by simp [cell, rDv, rAddr]) (by simp [cell, rDv, rCoin]), hg]
  have p2 : s2.mem (cell rPow) = p := by rw [m2 _ (by simp [cell, rPow, rAddr]) (by simp [cell, rPow, rCoin]), hp]
  have hcond : (c = 1) ↔ (τ.coins[pos + e]?.getD false) = true := by
    simp only [c]
    cases τ.coins[pos + e]? with
    | none => simp [bitVal]
    | some x => cases x <;> simp [bitVal]
  -- the branch
  obtain ⟨s3, k3, e3, hk3, g3, p3, o3, m3⟩ : ∃ s3 k3, Exec τ (fun w => w.Fits b)
      (ifLe rCoin rZero .skip (ifLe rCoin rOne (circ [asg rDv (.add rDv rPow)]) .skip)) s2 s3 k3 ∧
      k3 ≤ 4 ∧ s3.mem (cell rDv) = g + (if c = 1 then p else 0) ∧ s3.mem (cell rPow) = p ∧
      s3.out = s2.out ∧ ∀ a, a ≠ cell rDv → s3.mem a = s2.mem a := by
    by_cases h : c ≤ 0
    · refine ⟨s2, _, Exec.yes (by rw [c2, z2]; exact h) (Exec.skip _), by omega, ?_, p2, rfl,
        fun _ _ => rfl⟩
      rw [g2, if_neg (by omega)]; rfl
    · by_cases h' : c ≤ 1
      · have e := circ_one (asg_add (τ := τ) s2 rDv rDv rPow f2 (by rw [g2, p2]; exact w2))
        refine ⟨_, _, Exec.no (by rw [c2, z2]; exact h) (Exec.yes (by rw [c2, o2]; exact h') e),
          by omega, ?_, ?_, rfl, ?_⟩
        · simp [mem_write, g2, p2]; omega
        · rw [mem_write, if_neg (by simp [cell, rPow, rDv]), p2]
        · intro a ha; rw [mem_write, if_neg ha]
      · refine ⟨s2, _, Exec.no (by rw [c2, z2]; exact h) (Exec.no (by rw [c2, o2]; exact h')
          (Exec.skip _)), by omega, ?_, p2, rfl, fun _ _ => rfl⟩
        rw [g2, if_neg (by omega)]; rfl
  have f3 := e3.post f2
  have e4 := circ_one (asg_add (τ := τ) s3 rPow rPow rPow f3 (by rw [p3]; exact w3))
  refine ⟨_, _, Exec.seq e1 (Exec.seq e2 (Exec.seq e3 e4)), by omega, ?_, ?_, ?_, ?_⟩
  · simp only [out_write]; rw [o3]; rfl
  · rw [mem_write, if_neg (by simp [cell, rPow, rDv]), g3]
    by_cases hh : c = 1
    · rw [if_pos hh, if_pos (hcond.mp hh)]
    · rw [if_neg hh, if_neg (fun h => hh (hcond.mpr (by simpa using h)))]
  · rw [mem_write, if_pos rfl, p3]
  · intro a h1 h2 h3 h4
    rw [mem_write, if_neg h2, m3 a h1, m2 a h3 h4]

end RGC

end DirectedHamiltonicity.Main.CycleHost

namespace DirectedHamiltonicity.Main.CycleHost

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word
open TargetedSamplers.Structured.Interp DirectedHamiltonicity.Main.CycleReduction RGC

theorem readGraph_exec' {τ : Tapes} {b : ℕ} (u : Store) {n : ℕ} (adj : Fin n → Fin n → Bool)
    (hin : τ.input = encodeDigraph n adj)
    (c : Consts u) (rn : u.mem (cell rN) = n) (rn2 : u.mem (cell rN2) = n * n)
    (rcur : u.mem (cell rCur) = 2 * n.size + 1)
    (fit : u.Fits b) (hb : 64 * (n + 1) ^ 3 ≤ b) :
    ∃ v j, Exec τ (fun w => w.Fits b) readGraph u v j ∧ j ≤ 100 * (n + 1) ^ 2 ∧
      v.mem (cell rG) < 2 ^ (n * n) ∧
      (∀ x y : Fin n, (v.mem (cell rG)).testBit (x.val * n + y.val) = adj x y) ∧
      Kept readGraphDirty u v (fun _ => True) := by
  set cur := 2 * n.size + 1 with hcur
  let F : ℕ → Bool := fun e => decide (0 < bitVal τ.input[cur + e]?)
  have hns : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  have hb1 : 2 * n + 1 + n * n + 2 ≤ b := by nlinarith
  have small : ∀ x, x ≤ b → x.size ≤ b := fun x hx =>
    size_le_of_lt (lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) hx))
  have smallp : ∀ x k, x < 2 ^ k → k ≤ b → x.size ≤ b := fun x k hx hk =>
    size_le_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hk))
  -- initialisation
  have e0 := circ_cons (asg_lit (τ := τ) u rG 0 fit (by simp))
    (circ_cons (asg_lit (τ := τ) _ rPow 1 (Store.write_fits fit _ (by simp)) (small 1 (by omega)))
      (circ_one (asg_lit (τ := τ) _ rE 0
        (Store.write_fits (Store.write_fits fit _ (by simp)) _ (small 1 (by omega))) (by simp))))
  have f0 := e0.post fit
  set s0 := ((u.write (cell rG) 0).write (cell rPow) 1).write (cell rE) 0 with hs0
  let state : ℕ → Store → Prop := fun e s =>
    s.mem (cell rE) = e ∧ s.mem (cell rN2) = n * n ∧ s.mem (cell rG) = bitsAcc F e ∧
    s.mem (cell rPow) = 2 ^ e ∧ s.out = u.out ∧
    ∀ a, 14 ≤ a → (∀ d ∈ readGraphDirty, a ≠ cell d) → s.mem a = u.mem a
  have keep : ∀ s e, state e s → ∀ i, i ∉ readGraphDirty → s.mem (cell i) = u.mem (cell i) := by
    intro s e hs i hi
    exact hs.2.2.2.2.2 _ (by simp [cell]) (fun d hd h => hi (by
      simp only [cell] at h; rwa [show i = d by omega]))
  have start : state 0 s0 := by
    refine ⟨by simp [s0, mem_write], ?_, by simp [s0, mem_write, bitsAcc, cell, rG, rE, rPow],
      by simp [s0, mem_write, cell, rPow, rE], rfl, ?_⟩
    · simp [s0, mem_write, cell, rN2, rE, rPow, rG]; simpa [cell, rN2] using rn2
    · intro a _ ha
      simp only [readGraphDirty, List.mem_cons, List.not_mem_nil, forall_eq_or_imp] at ha
      simp [s0, mem_write, ha.1, ha.2.1, ha.2.2.1]
  obtain ⟨t, j, ex, hj, st⟩ := forRange_exec (τ := τ) (b := b) (cell rE) (cell rN2) (cell rOne) 0
    (n * n) 6 _ state
    (fun i _ s hs => ⟨by rw [hs.1]; simp, by rw [hs.2.1]; simp⟩)
    (by
      intro i hi s hs fs
      have hcur' : s.mem (cell rCur) = cur := by rw [keep s i hs rCur (by decide), rcur]
      have hz : s.mem (cell rZero) = 0 := by rw [keep s i hs rZero (by decide), c.zero]
      have ho : s.mem (cell rOne) = 1 := by rw [keep s i hs rOne (by decide), c.one]
      have hlt := bitsAcc_lt F i
      obtain ⟨t, k, ex, hk, ot, gt, pt, mt⟩ := rg_body (τ := τ) s fs (by omega) cur i _ _ hcur' hs.1
        hs.2.2.1 hs.2.2.2.1 hz (small _ (by omega))
        (smallp _ (i + 1) (by rw [pow_succ]; omega) (by omega))
        (smallp _ (i + 2) (by rw [pow_succ, pow_succ]; have := Nat.one_le_two_pow (n := i); omega)
          (by omega))
      have ne : ∀ d ∈ readGraphDirty, cell rE ≠ cell d ∨ d = rE := by
        intro d _; by_cases h : d = rE
        · exact Or.inr h
        · left; simp only [cell]; intro h'; exact h (by omega)
      refine ⟨t, k, ex, hk, ?_, ?_, ?_⟩
      · rw [mt _ (by simp [cell, rE, rG]) (by simp [cell, rE, rPow]) (by simp [cell, rE, rAddr])
          (by simp [cell, rE, rCoin]), hs.1]; simp
      · rw [mt _ (by simp [cell, rOne, rG]) (by simp [cell, rOne, rPow]) (by simp [cell, rOne, rAddr])
          (by simp [cell, rOne, rCoin]), ho]
      · refine ⟨by simp [mem_write], ?_, ?_, ?_, by simp [ot, hs.2.2.2.2.1], ?_⟩
        · rw [mem_write, if_neg (by simp [cell, rE, rN2]),
            mt _ (by simp [cell, rN2, rG]) (by simp [cell, rN2, rPow]) (by simp [cell, rN2, rAddr])
            (by simp [cell, rN2, rCoin]), hs.2.1]
        · rw [mem_write, if_neg (by simp [cell, rE, rG]), gt]
          simp only [bitsAcc, F, decide_eq_true_eq]
        · rw [mem_write, if_neg (by simp [cell, rE, rPow]), pt, pow_succ]; ring
        · intro a ha hd
          simp only [readGraphDirty, List.mem_cons, List.not_mem_nil, forall_eq_or_imp] at hd
          rw [mem_write, if_neg hd.2.2.1, mt a hd.1 hd.2.1 hd.2.2.2.1 hd.2.2.2.2.1]
          exact hs.2.2.2.2.2 a ha (by
            simp only [readGraphDirty, List.mem_cons, List.not_mem_nil, forall_eq_or_imp]
            exact hd))
    (by simpa using small _ (by nlinarith)) s0 start f0
  refine ⟨t, 3 + j, Exec.seq e0 ex, by nlinarith, ?_, ?_, st.2.2.2.2.1, fun a ha hd _ => ?_⟩
  · rw [st.2.2.1]; exact bitsAcc_lt F _
  · intro x y
    have hxy : x.val * n + y.val < n * n := by
      have := x.isLt; have := y.isLt; nlinarith
    rw [st.2.2.1, bitsAcc_testBit F _ _ hxy]
    simp [F, hin, input_bit, cur, bitVal]
    cases adj x y <;> rfl
  · exact st.2.2.2.2.2 a ha hd

end DirectedHamiltonicity.Main.CycleHost

namespace DirectedHamiltonicity.Main.CycleHost

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word
open TargetedSamplers.Structured.Interp DirectedHamiltonicity.Main.CycleReduction RGC

/-- Corrected spec of `readSeed`.  The original `readSeed_exec` is false: the multiplication
`rI * rSw` costs `Θ(i.size^2)` steps (not `O(sw)`), and for `sw = 0` its scratch value `i + 1`
can overflow the width `b`.  This version adds `(2 * i + 2).size ≤ b` and the step term
`10 * (b + 1) ^ 2`. -/
theorem readSeed_exec_fixed {τ : Tapes} {b : ℕ} (u : Store) (i sw : ℕ)
    (c : Consts u) (ri : u.mem (cell rI) = i) (rsw : u.mem (cell rSw) = sw)
    (fit : u.Fits b) (hb : (i * sw + sw).size + sw + 4 ≤ b) (hi : (2 * i + 2).size ≤ b) :
    ∃ v j, Exec τ (fun w => w.Fits b) readSeed u v j ∧ j ≤ 100 * (sw + 1) + 10 * (b + 1) ^ 2 ∧
      v.mem (cell rDv) = ∑ j : Fin sw, (τ.coins[i * sw + j.val]?.getD false).toNat * 2 ^ j.val ∧
      Kept readSeedDirty u v (fun _ => True) := by
  let F : ℕ → Bool := fun e => τ.coins[i * sw + e]?.getD false
  have smallp : ∀ x k, x < 2 ^ k → k ≤ b → x.size ≤ b := fun x k hx hk =>
    size_le_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hk))
  have hsb : (i * sw + sw).size ≤ b := by omega
  have hb2 : 2 ≤ b := by omega
  have hone : (1 : ℕ).size ≤ b := by simp; omega
  -- initialisation
  have e0 := asg_lit (τ := τ) u rDv 0 fit (by simp)
  have f0 := e0.post fit
  have e1 := asg_lit (τ := τ) _ rPow 1 f0 hone
  have f1 := e1.post f0
  set s1 := (u.write (cell rDv) 0).write (cell rPow) 1 with hs1
  have i1 : s1.mem (cell rI) = i := by simp [s1, mem_write, cell, rI, rDv, rPow]; simpa [cell, rI] using ri
  have sw1 : s1.mem (cell rSw) = sw := by simp [s1, mem_write, cell, rSw, rDv, rPow]; simpa [cell, rSw] using rsw
  obtain ⟨t2, k2, e2, hk2, o2, m2⟩ := Arithmetic.call_exec (τ := τ) .mul rSeedPos rI rSw s1 f1 hb2
    (by rw [i1]; exact hi)
    (by rw [i1, sw1]; exact (Nat.size_le_size (by simp [Arithmetic.value])).trans hsb)
  have f2 := e2.post f1
  have e3 := asg_lit (τ := τ) t2 rJ 0 f2 (by simp)
  have f3 := e3.post f2
  have einit : Exec τ (fun w => w.Fits b) (circ [asg rDv (.literal 0), asg rPow (.literal 1),
      asg rSeedPos (.arithmetic .mul rI rSw), asg rJ (.literal 0)]) u (t2.write (cell rJ) 0)
      (1 + (1 + (k2 + 1))) :=
    circ_cons e0 (circ_cons e1 (circ_cons e2 (circ_one e3)))
  set s3 := t2.write (cell rJ) 0 with hs3
  have m3 : ∀ x, s3.mem (cell x) = if x = rJ then 0 else if x = rSeedPos then i * sw else
      if x = rPow then 1 else if x = rDv then 0 else u.mem (cell x) := by
    intro x
    rw [hs3, mem_write]
    by_cases hx : x = rJ
    · simp [hx]
    · rw [if_neg (by simp [cell]; exact hx), if_neg hx, m2 x]
      by_cases hy : x = rSeedPos
      · simp [hy, i1, sw1, Arithmetic.value]
      · rw [if_neg hy, if_neg hy]
        simp only [s1, mem_write, cell]
        by_cases hz : x = rPow
        · simp [hz]
        · rw [if_neg (by omega), if_neg hz]
          by_cases hw : x = rDv
          · simp [hw]
          · rw [if_neg (by omega), if_neg hw]
  let state : ℕ → Store → Prop := fun e s =>
    s.mem (cell rJ) = e ∧ s.mem (cell rSw) = sw ∧ s.mem (cell rDv) = bitsAcc F e ∧
    s.mem (cell rPow) = 2 ^ e ∧ s.mem (cell rSeedPos) = i * sw ∧ s.out = u.out ∧
    ∀ a, 14 ≤ a → (∀ d ∈ readSeedDirty, a ≠ cell d) → s.mem a = u.mem a
  have keep : ∀ s e, state e s → ∀ x, x ∉ readSeedDirty → s.mem (cell x) = u.mem (cell x) := by
    intro s e hs x hx
    exact hs.2.2.2.2.2.2 _ (by simp [cell]) (fun d hd h => hx (by
      simp only [cell] at h; rwa [show x = d by omega]))
  have start : state 0 s3 := by
    refine ⟨by rw [m3]; simp, by rw [m3]; simpa [rSw, rJ, rSeedPos, rPow, rDv] using rsw,
      by rw [m3]; simp [rDv, rJ, rSeedPos, rPow, bitsAcc],
      by rw [m3]; simp [rPow, rJ, rSeedPos], by rw [m3]; simp [rSeedPos, rJ], ?_, ?_⟩
    · simp [s3, o2, s1]
    · intro a ha hd
      have := m3 (a - 14)
      rw [show cell (a - 14) = a by simp [cell]; omega] at this
      rw [this]
      simp only [readSeedDirty, List.mem_cons, List.not_mem_nil, forall_eq_or_imp] at hd
      have h1 : a - 14 ≠ rJ := fun h => hd.2.2.2.1 (by simp [cell]; omega)
      have h2 : a - 14 ≠ rSeedPos := fun h => hd.2.2.1 (by simp [cell]; omega)
      have h3 : a - 14 ≠ rPow := fun h => hd.2.1 (by simp [cell]; omega)
      have h4 : a - 14 ≠ rDv := fun h => hd.1 (by simp [cell]; omega)
      rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4]
  obtain ⟨t, j, ex, hj, st⟩ := forRange_exec (τ := τ) (b := b) (cell rJ) (cell rSw) (cell rOne) 0
    sw 7 _ state
    (fun e _ s hs => ⟨by rw [hs.1]; simp, by rw [hs.2.1]; simp⟩)
    (by
      intro e he s hs fs
      have hz : s.mem (cell rZero) = 0 := by rw [keep s e hs rZero (by decide), c.zero]
      have ho : s.mem (cell rOne) = 1 := by rw [keep s e hs rOne (by decide), c.one]
      have hlt := bitsAcc_lt F e
      obtain ⟨t, k, ex, hk, ot, gt, pt, mt⟩ := rs_body (τ := τ) s fs hb2 (i * sw) e _ _
        hs.2.2.2.2.1 hs.1 hs.2.2.1 hs.2.2.2.1 hz ho
        ((Nat.size_le_size (by omega)).trans hsb)
        (smallp _ (e + 1) (by rw [pow_succ]; omega) (by omega))
        (smallp _ (e + 2) (by rw [pow_succ, pow_succ]; have := Nat.one_le_two_pow (n := e); omega)
          (by omega))
      refine ⟨t, k, ex, hk, ?_, ?_, ?_⟩
      · rw [mt _ (by simp [cell, rJ, rDv]) (by simp [cell, rJ, rPow]) (by simp [cell, rJ, rAddr])
          (by simp [cell, rJ, rCoin]), hs.1]; simp
      · rw [mt _ (by simp [cell, rOne, rDv]) (by simp [cell, rOne, rPow]) (by simp [cell, rOne, rAddr])
          (by simp [cell, rOne, rCoin]), ho]
      · refine ⟨by simp [mem_write], ?_, ?_, ?_, ?_, by simp [ot, hs.2.2.2.2.2.1], ?_⟩
        · rw [mem_write, if_neg (by simp [cell, rJ, rSw]),
            mt _ (by simp [cell, rSw, rDv]) (by simp [cell, rSw, rPow]) (by simp [cell, rSw, rAddr])
            (by simp [cell, rSw, rCoin]), hs.2.1]
        · rw [mem_write, if_neg (by simp [cell, rJ, rDv]), gt]
          simp only [bitsAcc, F]
        · rw [mem_write, if_neg (by simp [cell, rJ, rPow]), pt, pow_succ]; ring
        · rw [mem_write, if_neg (by simp [cell, rJ, rSeedPos]),
            mt _ (by simp [cell, rSeedPos, rDv]) (by simp [cell, rSeedPos, rPow])
            (by simp [cell, rSeedPos, rAddr]) (by simp [cell, rSeedPos, rCoin]), hs.2.2.2.2.1]
        · intro a ha hd
          simp only [readSeedDirty, List.mem_cons, List.not_mem_nil, forall_eq_or_imp] at hd
          rw [mem_write, if_neg hd.2.2.2.1, mt a hd.1 hd.2.1 hd.2.2.2.2.1 hd.2.2.2.2.2.1]
          exact hs.2.2.2.2.2.2 a ha (by
            simp only [readSeedDirty, List.mem_cons, List.not_mem_nil, forall_eq_or_imp]
            exact hd))
    (by simpa using smallp sw sw Nat.lt_two_pow_self (by omega)) s3 start f3
  have isz : i.size ≤ b := by rw [← ri]; exact fit _
  have hmul : Arithmetic.steps .mul (s1.mem (cell rI)) (s1.mem (cell rSw)) ≤ 5 * b * b + 9 * b + 5 := by
    rw [i1]; simp only [Arithmetic.steps]; nlinarith
  refine ⟨t, _, Exec.seq einit ex, by nlinarith, ?_, st.2.2.2.2.2.1, fun a ha hd _ => ?_⟩
  · rw [st.2.2.1, bitsAcc_sum]
  · exact st.2.2.2.2.2.2 a ha hd

theorem readSeed_exec_fixed_pos {τ : Tapes} {b : ℕ} (u : Store) (i sw : ℕ)
    (c : Consts u) (ri : u.mem (cell rI) = i) (rsw : u.mem (cell rSw) = sw)
    (fit : u.Fits b) (hb : (i * sw + sw).size + sw + 4 ≤ b) (hsw : 0 < sw) :
    ∃ v j, Exec τ (fun w => w.Fits b) readSeed u v j ∧ j ≤ 100 * (sw + 1) + 10 * (b + 1) ^ 2 ∧
      v.mem (cell rDv) = ∑ j : Fin sw, (τ.coins[i * sw + j.val]?.getD false).toNat * 2 ^ j.val ∧
      Kept readSeedDirty u v (fun _ => True) := by
  refine readSeed_exec_fixed u i sw c ri rsw fit hb ?_
  have h1 : 2 * i + 2 ≤ 2 * (i * sw + sw) := by nlinarith
  have h2 := Nat.size_le_size h1
  have h3 : (2 * (i * sw + sw)).size ≤ (i * sw + sw).size + 1 := by
    apply Nat.size_le.mpr
    rw [pow_succ]; have := Nat.lt_size_self (i * sw + sw); omega
  omega

end DirectedHamiltonicity.Main.CycleHost


section SolutionBlock
open DirectedHamiltonicity.Main
open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word
open TargetedSamplers.Structured.Interp DirectedHamiltonicity.Main.CycleReduction
open DirectedHamiltonicity.Main.CycleHost
theorem solution {τ : Tapes} {b : ℕ} (u : Store) {n : ℕ} (adj : Fin n → Fin n → Bool)
    (hin : τ.input = encodeDigraph n adj)
    (c : Consts u) (rn : u.mem (cell rN) = n) (rn2 : u.mem (cell rN2) = n * n)
    (rcur : u.mem (cell rCur) = 2 * n.size + 1)
    (fit : u.Fits b) (hb : 64 * (n + 1) ^ 3 ≤ b) :
    ∃ v j, Exec τ (fun w => w.Fits b) readGraph u v j ∧ j ≤ 100 * (n + 1) ^ 2 ∧
      v.mem (cell rG) < 2 ^ (n * n) ∧
      (∀ x y : Fin n, (v.mem (cell rG)).testBit (x.val * n + y.val) = adj x y) ∧
      Kept readGraphDirty u v (fun _ => True) := by
  apply DirectedHamiltonicity.Main.CycleHost.readGraph_exec' <;> assumption
end SolutionBlock
