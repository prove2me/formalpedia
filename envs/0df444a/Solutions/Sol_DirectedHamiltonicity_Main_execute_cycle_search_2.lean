-- Prove2me | solution 2 for DirectedHamiltonicity.Main.execute_cycle_search
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T04:21:07.246241+00:00
-- url     : https://prove2.me/submissions/d598b63a-c237-42b5-8fc1-e2966ac678e9

import Definitions.Def_LogCostRAM_StructuredExecution
import Definitions.Def_DirectedHamiltonicity_CycleSearchHost
import Theorems.Thm_TargetedSamplers_Structured_Work_framework
import Definitions.Def_DirectedHamiltonicity_CycleSearch
import Definitions.Def_LogCostRAM_Interpreter
import Theorems.Thm_TargetedSamplers_Structured_Interp_call_exec
import Theorems.Thm_DirectedHamiltonicity_Main_CycleHost_buildX_exec
import Theorems.Thm_DirectedHamiltonicity_Main_CycleHost_certify_exec
import Theorems.Thm_DirectedHamiltonicity_Main_CycleHost_readGraph_exec
import Theorems.Thm_DirectedHamiltonicity_Main_CycleHost_readSeed_exec
import Theorems.Thm_DirectedHamiltonicity_Main_CycleHost_decodeDraw_exec
import Theorems.Thm_DirectedHamiltonicity_Main_CycleHost_params_exec

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


-- ===== Solutions/Dev/WLoop.lean =====

set_option autoImplicit false

namespace TargetedSamplers.Structured.Work

open TargetedSamplers TargetedSamplers.Structured

variable {τ : Tapes} {J : ℕ}

theorem toW {b : ℕ} {c : Cmd} {s t : Store} {k : ℕ}
    (ev : Exec τ (fun v => v.Fits b) c s t k) (hs : s.Fits b) (hf : Cmd.FieldsFit J c) (h2 : 2 ≤ b) :
    WExec τ J c s t (k * (4 * b + 4 * J + 4)) :=
  framework.2.1 ev hs hf h2

theorem WExec.mono' {c : Cmd} {s t : Store} {k k' : ℕ} (h : WExec τ J c s t k) (hk : k ≤ k') :
    WExec τ J c s t k' := WExec.mono h hk

theorem op_add_cost_le {s : Store} {d a c b : ℕ} (hd : d.size ≤ J) (ha : a.size ≤ J) (hc : c.size ≤ J)
    (ma : (s.mem a).size ≤ b) (mc : (s.mem c).size ≤ b) (mr : (s.mem a + s.mem c).size ≤ b) :
    Op.cost τ s (.add d a c) ≤ 3 * J + 3 * b + 1 := by
  simp only [Op.cost]; omega

theorem jumpCost_le {s : Store} {a c b : ℕ} (ha : a.size ≤ J) (hc : c.size ≤ J)
    (ma : (s.mem a).size ≤ b) (mc : (s.mem c).size ≤ b) : jumpCost J s a c ≤ 3 * J + 2 * b + 1 := by
  simp only [jumpCost]; omega

theorem jumpCost_zero_le {s : Store} {b : ℕ} (m : (s.mem 0).size ≤ b) : jumpCost J s 0 0 ≤ J + 2 * b + 1 := by
  simp only [jumpCost]; simp; omega

/-- An ascending loop in exact-cost semantics. -/
theorem wforRange {b : ℕ} (ptr stop one lo count bound : ℕ) (body : Cmd) (state : ℕ → Store → Prop)
    (hf : Cmd.FieldsFit J (forRange ptr stop one body))
    (control : ∀ i ≤ count, ∀ s, state i s → s.mem ptr = lo + i ∧ s.mem stop = lo + count)
    (width : (lo + count + 1).size ≤ b)
    (bodyRun : ∀ i < count, ∀ s, state i s →
      ∃ u k, WExec τ J body s u k ∧ k ≤ bound ∧ u.mem ptr = lo + i ∧ u.mem one = 1 ∧
        (u.mem 0).size ≤ b ∧ state (i + 1) (u.write ptr (lo + i + 1)))
    (s : Store) (start : state 0 s) :
    ∃ t k, WExec τ J (forRange ptr stop one body) s t k ∧
      k ≤ count * (bound + 7 * J + 7 * b + 3) + 3 * J + 2 * b + 1 ∧ state count t := by
  simp only [forRange, Cmd.FieldsFit] at hf
  obtain ⟨hs, hp, hfb, hfo⟩ := hf
  simp only [Op.fields, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hfo
  have sz (x : ℕ) (hx : x ≤ lo + count) : x.size ≤ b :=
    (Nat.size_le_size (by omega : x ≤ lo + count + 1)).trans width
  have run (left i : ℕ) (he : i + left = count) (u : Store) (hi : state i u) :
      ∃ t k, WExec τ J (forRange ptr stop one body) u t k ∧
        k ≤ left * (bound + 7 * J + 7 * b + 3) + 3 * J + 2 * b + 1 ∧ state count t := by
    induction left generalizing i u with
    | zero =>
      have eq : i = count := by omega
      obtain ⟨hpv, hsv⟩ := control i (by omega) u hi
      refine ⟨u, _, WExec.done (by rw [hsv, hpv, eq]), ?_, eq ▸ hi⟩
      have := jumpCost_le (J := J) (s := u) (b := b) hs hp (by rw [hsv]; exact sz _ le_rfl)
        (by rw [hpv]; exact sz _ (by omega))
      simpa using this
    | succ left ih =>
      obtain ⟨hpv, hsv⟩ := control i (by omega) u hi
      obtain ⟨v, k, ex, hk, hp', h1, h0, hn⟩ := bodyRun i (by omega) u hi
      have hnext : (Op.add ptr ptr one).eval τ v = v.write ptr (lo + i + 1) := by
        simp [Op.eval, hp', h1]
      have inc : WExec τ J (.op (.add ptr ptr one)) v (v.write ptr (lo + i + 1))
          (Op.cost τ v (.add ptr ptr one)) := by
        rw [← hnext]; exact WExec.op v _
      have cinc : Op.cost τ v (.add ptr ptr one) ≤ 3 * J + 3 * b + 1 :=
        op_add_cost_le hp hp hfo.2.2 (by rw [hp']; exact sz _ (by omega)) (by rw [h1]; exact (Nat.size_le_size (by omega : 1 ≤ lo + count + 1)).trans width)
          (by rw [hp', h1]; exact sz _ (by omega))
      obtain ⟨t, j, loop, hj, ret⟩ := ih (i + 1) (by omega) _ hn
      have c1 := jumpCost_le (J := J) (s := u) (b := b) hs hp (by rw [hsv]; exact sz _ le_rfl)
        (by rw [hpv]; exact sz _ (by omega))
      have m0 : ((v.write ptr (lo + i + 1)).mem 0).size ≤ b := by
        by_cases h : (0 : ℕ) = ptr
        · subst h; simp [Store.write]; exact sz _ (by omega)
        · simp [Store.write, Function.update_of_ne h]; exact h0
      have c2 := jumpCost_zero_le (J := J) m0
      refine ⟨t, _, WExec.again (by rw [hsv, hpv]; omega) (ex.seq inc) loop, ?_, ret⟩
      have : left * (bound + 7 * J + 7 * b + 3) + (bound + 7 * J + 7 * b + 3) =
          (left + 1) * (bound + 7 * J + 7 * b + 3) := by ring
      omega
  obtain ⟨t, k, h1, h2, h3⟩ := run count 0 (by simp) s start
  exact ⟨t, k, h1, h2, h3⟩

end TargetedSamplers.Structured.Work


-- ===== Solutions/Dev/Panel.lean =====

set_option autoImplicit false

namespace DirectedHamiltonicity.Main.CycleHost

open DirectedHamiltonicity.Main.CycleReduction FiniteSampling

theorem panel_seed (n L : ℕ) (coins : List Bool) (i : Fin (trials n)) (j : Fin (seedWidth n)) :
    (panelFromTape n L coins).1 i j = coins[i.val * seedWidth n + j.val]?.getD false := by
  show coins[((finSumFinEquiv (Sum.inl (finProdFinEquiv (i, j)) :
    Fin (trials n * seedWidth n) ⊕ Fin (2 * majorityHalf n * L)))).val]?.getD false = _
  simp [finProdFinEquiv_apply_val]
  ring_nf

theorem panel_tape (n L : ℕ) (coins : List Bool) (j : Fin (2 * majorityHalf n)) (u : Fin L) :
    (panelFromTape n L coins).2 j u =
      coins[trials n * seedWidth n + j.val * L + u.val]?.getD false := by
  show coins[((finSumFinEquiv (Sum.inr (finProdFinEquiv (j, u)) :
    Fin (trials n * seedWidth n) ⊕ Fin (2 * majorityHalf n * L)))).val]?.getD false = _
  simp [finProdFinEquiv_apply_val]
  ring_nf

theorem binaryRank_val (k : ℕ) (bits : Fin k → Bool) :
    (binaryRank k bits).val = ∑ j : Fin k, (bits j).toNat * 2 ^ j.val := by
  simp [binaryRank, finFunctionFinEquiv_apply]
  congr 1; ext j; cases bits j <;> rfl

end DirectedHamiltonicity.Main.CycleHost


-- ===== Solutions/Dev/PruneMath.lean =====

set_option autoImplicit false

namespace DirectedHamiltonicity.Main.CycleHost

open DirectedHamiltonicity.Main.CycleReduction

theorem prune_append {E : Type} [DecidableEq E] (ask : E → Finset E → Bool) (G : Finset E) (l1 l2 : List E) :
    CycleReduction.prune ask G (l1 ++ l2) = CycleReduction.prune ask (CycleReduction.prune ask G l1) l2 := by
  induction l1 generalizing G with
  | nil => rfl
  | cons e es ih => simp [CycleReduction.prune, ih]

theorem prune_single {E : Type} [DecidableEq E] (ask : E → Finset E → Bool) (G : Finset E) (e : E) :
    CycleReduction.prune ask G [e] = if ask e (G.erase e) then G.erase e else G := rfl

theorem edgeOrder_length (n : ℕ) : (edgeOrder n).length = n * n := by
  simp [edgeOrder, List.length_flatMap]

theorem rows (m n : ℕ) (hn : 0 < n) :
    (List.range m).flatMap (fun i => (List.range n).map (fun j => (i, j))) =
      (List.range (m * n)).map (fun e => (e / n, e % n)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append, ih, Nat.succ_mul, List.range_add, List.map_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_map]
    congr 1
    apply List.map_congr_left
    intro j hj
    simp at hj
    simp only [Function.comp]
    rw [Prod.mk.injEq]
    constructor
    · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hj]; simp
    · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]

theorem edgeOrder_vals (n : ℕ) (hn : 0 < n) :
    (edgeOrder n).map (fun p => (p.1.val, p.2.val)) = (List.range (n * n)).map (fun e => (e / n, e % n)) := by
  rw [← rows n n hn, edgeOrder, List.map_flatMap]
  simp only [List.map_map]
  have h1 : (List.finRange n).flatMap (fun a => List.map ((fun p : Fin n × Fin n => (p.1.val, p.2.val)) ∘
      fun j => (a, j)) (List.finRange n)) =
      (List.finRange n).flatMap (fun a => (List.range n).map (fun j => (a.val, j))) := by
    congr 1; funext a
    rw [← List.map_coe_finRange_eq_range, List.map_map]; rfl
  rw [h1]
  have h2 : (List.finRange n).flatMap (fun a => (List.range n).map (fun j => (a.val, j))) =
      ((List.finRange n).map Fin.val).flatMap (fun i => (List.range n).map (fun j => (i, j))) := by
    rw [List.flatMap_map]
  rw [h2, List.map_coe_finRange_eq_range]

theorem edgeOrder_get (n e : ℕ) (he : e < (edgeOrder n).length) :
    ((edgeOrder n)[e]'he).1.val = e / n ∧ ((edgeOrder n)[e]'he).2.val = e % n := by
  have hn : 0 < n := by
    rw [edgeOrder_length] at he; rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp at he
    · exact h
  have hv := edgeOrder_vals n hn
  have h1 : e < ((edgeOrder n).map (fun p => (p.1.val, p.2.val))).length := by simpa using he
  have := congrArg (fun l => l[e]?) hv
  rw [List.getElem?_map, List.getElem?_map, List.getElem?_eq_getElem he,
    List.getElem?_range (by rw [edgeOrder_length] at he; exact he)] at this
  simp at this
  exact this

theorem testBit_sub_two_pow (m e j : ℕ) (h : m.testBit e = true) :
    (m - 2 ^ e).testBit j = (decide (j ≠ e) && m.testBit j) := by
  have hge : 2 ^ e ≤ m := Nat.ge_two_pow_of_testBit h
  obtain ⟨x, rfl⟩ : ∃ x, m = 2 ^ e + x := ⟨m - 2 ^ e, by omega⟩
  rw [Nat.add_sub_cancel_left]
  have hx : x.testBit e = false := by
    have := Nat.testBit_two_pow_add_eq x e; rw [h] at this; simpa using this.symm
  rcases lt_trichotomy j e with hj | rfl | hj
  · rw [Nat.testBit_two_pow_add_gt hj]; simp [Nat.ne_of_lt hj]
  · simp [hx]
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 + e := ⟨j - e - 1, by omega⟩
    have hy : (x / 2 ^ e) % 2 = 0 := by
      have := Nat.testBit_div_two_pow (n := e) x 0
      rw [zero_add, hx, Nat.testBit_zero] at this
      simp at this; omega
    have d1 : (2 ^ e + x) / 2 ^ e = 1 + x / 2 ^ e := by
      rw [Nat.add_comm, Nat.add_div_right _ (Nat.two_pow_pos e)]; ring
    have L : x.testBit (i + 1 + e) = (x / 2 ^ e).testBit (i + 1) := (Nat.testBit_div_two_pow x (i + 1)).symm
    have R : (2 ^ e + x).testBit (i + 1 + e) = ((2 ^ e + x) / 2 ^ e).testBit (i + 1) :=
      (Nat.testBit_div_two_pow _ (i + 1)).symm
    have : (1 + x / 2 ^ e) / 2 = x / 2 ^ e / 2 := by omega
    rw [R, L, d1, Nat.testBit_succ, Nat.testBit_succ, this]
    simp

end DirectedHamiltonicity.Main.CycleHost


-- ===== Solutions/Dev/Asm1.lean =====

set_option autoImplicit false

namespace DirectedHamiltonicity.Main.CycleHost

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word
open TargetedSamplers.Structured.Work
open TargetedSamplers.Structured.Interp DirectedHamiltonicity.Main.CycleReduction

variable {τ : Tapes} {J : ℕ}

/-- Exact-cost run of an arithmetic circuit. -/
theorem wcirc {b : ℕ} (as : List Assignment) (s : Store) (fit : s.Fits b) (hb : 2 ≤ b)
    (hw : Circuit.width (fun i => s.mem (cell i)) as ≤ b) (hf : Cmd.FieldsFit J (circ as)) :
    ∃ t, WExec τ J (circ as) s t
        (Circuit.multiplicity (fun i => s.mem (cell i)) as * (b * (5 * b + 9) + 15) * (4 * b + 4 * J + 4)) ∧
      (∀ i, t.mem (cell i) = Circuit.result (fun i => s.mem (cell i)) as i) ∧ t.out = s.out ∧ t.Fits b := by
  obtain ⟨t, j, ex, hj, rep, out⟩ := Circuit.exec (τ := τ) as (fun i => s.mem (cell i)) s (fun _ => rfl) fit hb hw
  have hs := Circuit.steps_le as (fun i => s.mem (cell i)) b hw
  refine ⟨t, WExec.mono (toW ex fit hf hb) ?_, rep, out, ex.post fit⟩
  exact Nat.mul_le_mul_right _ (hj.trans hs)

def VBv (n : ℕ) : ℕ := xBase + 128 * (n + 1) ^ 3
def LOGv (n : ℕ) : ℕ := VBv n + n
def BIGv (n A k : ℕ) : ℕ := LOGv n + coinSpan A k n + 1

/-- Registers and memory regions that stay fixed after the parameters are computed. -/
structure HostInv (n A k b : ℕ) (s : Store) : Prop where
  consts : Consts s
  rn : s.mem (cell rN) = n
  rn2 : s.mem (cell rN2) = n * n
  rm : s.mem (cell rM) = 3 * (n * n)
  rw : s.mem (cell rW) = Wmax n
  rbm : s.mem (cell rBm1) = Bmax n + 1
  rpw : s.mem (cell rPW) = Wmax n ^ (n * 3)
  rin : s.mem (cell rIn) = 50 ^ (n * n) * Wmax n ^ (n * 3) * (Bmax n + 1)
  rdc : s.mem (cell rDc) = drawCount n
  rtr : s.mem (cell rTrials) = trials n
  rsw : s.mem (cell rSw) = seedWidth n
  rl : s.mem (cell rL) = coinSpan A k n
  rr : s.mem (cell rR) = majorityHalf n
  rr2 : s.mem (cell rR2) = 2 * majorityHalf n
  rtb : s.mem (cell rTapeBase) = trials n * seedWidth n
  rvb : s.mem (cell rVB) = VBv n
  rlog : s.mem (cell 103) = LOGv n
  rbig : s.mem (cell 102) = BIGv n A k
  rxb : s.mem (cell 105) = xBase
  rone' : s.mem (cell 110) = 1
  rzero' : s.mem (cell 111) = 0
  rds : s.mem (cell 112) = 0
  t1 : s.mem (cell 113) = 0
  t2 : s.mem (cell 114) = 0
  t3 : s.mem (cell 115) = 0
  t4 : s.mem (cell 116) = 0
  t5 : s.mem (cell 117) = 0
  t6 : s.mem (cell 118) = 0
  high : ∀ a, LOGv n ≤ a → s.mem a = 0
  vis : ∀ i < n, s.mem (VBv n + i) = 0
  fits : s.Fits b

/-- The logical registers mentioned by `HostInv`. -/
def invRegs : List ℕ :=
  [rOne, rZero, rTwo, rThree, rSix, rSeven, rFifty, rC49, rN, rN2, rM, rW, rBm1, rPW, rIn, rDc,
   rTrials, rSw, rL, rR, rR2, rTapeBase, rVB, 103, 102, 105, 110, 111, 112, 113, 114, 115, 116, 117, 118]

theorem HostInv.congr {n A k b : ℕ} {s t : Store} (h : HostInv n A k b s)
    (regs : ∀ d ∈ invRegs, t.mem (cell d) = s.mem (cell d))
    (high : ∀ a, VBv n ≤ a → t.mem a = s.mem a) (fit : t.Fits b) : HostInv n A k b t where
  consts := {
    one := by rw [regs rOne (by simp [invRegs])]; exact h.consts.one,
    zero := by rw [regs rZero (by simp [invRegs])]; exact h.consts.zero,
    two := by rw [regs rTwo (by simp [invRegs])]; exact h.consts.two,
    three := by rw [regs rThree (by simp [invRegs])]; exact h.consts.three,
    six := by rw [regs rSix (by simp [invRegs])]; exact h.consts.six,
    seven := by rw [regs rSeven (by simp [invRegs])]; exact h.consts.seven,
    fifty := by rw [regs rFifty (by simp [invRegs])]; exact h.consts.fifty,
    c49 := by rw [regs rC49 (by simp [invRegs])]; exact h.consts.c49 }
  rn := by rw [regs rN (by simp [invRegs])]; exact h.rn
  rn2 := by rw [regs rN2 (by simp [invRegs])]; exact h.rn2
  rm := by rw [regs rM (by simp [invRegs])]; exact h.rm
  rw := by rw [regs rW (by simp [invRegs])]; exact h.rw
  rbm := by rw [regs rBm1 (by simp [invRegs])]; exact h.rbm
  rpw := by rw [regs rPW (by simp [invRegs])]; exact h.rpw
  rin := by rw [regs rIn (by simp [invRegs])]; exact h.rin
  rdc := by rw [regs rDc (by simp [invRegs])]; exact h.rdc
  rtr := by rw [regs rTrials (by simp [invRegs])]; exact h.rtr
  rsw := by rw [regs rSw (by simp [invRegs])]; exact h.rsw
  rl := by rw [regs rL (by simp [invRegs])]; exact h.rl
  rr := by rw [regs rR (by simp [invRegs])]; exact h.rr
  rr2 := by rw [regs rR2 (by simp [invRegs])]; exact h.rr2
  rtb := by rw [regs rTapeBase (by simp [invRegs])]; exact h.rtb
  rvb := by rw [regs rVB (by simp [invRegs])]; exact h.rvb
  rlog := by rw [regs 103 (by simp [invRegs])]; exact h.rlog
  rbig := by rw [regs 102 (by simp [invRegs])]; exact h.rbig
  rxb := by rw [regs 105 (by simp [invRegs])]; exact h.rxb
  rone' := by rw [regs 110 (by simp [invRegs])]; exact h.rone'
  rzero' := by rw [regs 111 (by simp [invRegs])]; exact h.rzero'
  rds := by rw [regs 112 (by simp [invRegs])]; exact h.rds
  t1 := by rw [regs 113 (by simp [invRegs])]; exact h.t1
  t2 := by rw [regs 114 (by simp [invRegs])]; exact h.t2
  t3 := by rw [regs 115 (by simp [invRegs])]; exact h.t3
  t4 := by rw [regs 116 (by simp [invRegs])]; exact h.t4
  t5 := by rw [regs 117 (by simp [invRegs])]; exact h.t5
  t6 := by rw [regs 118 (by simp [invRegs])]; exact h.t6
  high a ha := by rw [high a (by simp only [LOGv] at ha; omega)]; exact h.high a ha
  vis i hi := by rw [high _ (by omega)]; exact h.vis i hi
  fits := fit

end DirectedHamiltonicity.Main.CycleHost


-- ===== Solutions/Dev/Asm2.lean =====

set_option autoImplicit false

namespace DirectedHamiltonicity.Main.CycleHost

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word
open TargetedSamplers.Structured.Work
open TargetedSamplers.Structured.Interp DirectedHamiltonicity.Main.CycleReduction

/-- The interpreter contract with constant `C` (statement of `Interp.call_exec`). -/
def ICall (Q : Program) (r : IRegs) (C : ℕ) : Prop :=
  ∀ (τ : Tapes) (J : ℕ) (x : List Bool) (co cl T BIG LOG XB : ℕ) (st : State) (S : Store),
      Q.final ⟨x, windowCoins τ.coins co cl, [], noOracle⟩ = some st → st.work ≤ T →
      Cmd.FieldsFit J (call r Q) →
      S.mem r.pc = 0 → S.mem r.run = 1 → S.mem r.cnt = 0 → S.mem r.cap = 2 → S.mem r.one = 1 →
      S.mem r.zero = 0 → S.mem r.ds = 0 → S.mem r.t1 = 0 → S.mem r.t2 = 0 → S.mem r.t3 = 0 →
      S.mem r.t4 = 0 → S.mem r.t5 = 0 → S.mem r.t6 = 0 → S.mem 0 = 0 →
      S.mem r.big = BIG → S.mem r.logb = LOG → S.mem r.xb = XB → S.mem r.xlen = x.length →
      S.mem r.co = co → S.mem r.cl = cl →
      (∀ y ∈ r.all, y < XB) → XB + x.length ≤ LOG → LOG + T + 1 ≤ BIG →
      (∀ i (hi : i < x.length), S.mem (XB + i) = (x[i]'hi).toNat) →
      (∀ u, S.mem (BIG + u) = 0) → (∀ j, j ≤ T → S.mem (LOG + j) = 0) →
      ∃ S' k, WExec τ J (call r Q) S S' k ∧ k ≤ C * (T + 1) * ((BIG + co + cl).size + J + 1) ∧
        S'.mem r.cap = capValue st.out ∧ S'.mem r.run = 0 ∧
        S'.out = S.out ∧ ∀ y, y ≠ r.cap → y ≠ r.run → S'.mem y = S.mem y

theorem icall_exists (Q : Program) : ∃ C, ICall Q iregs C := by
  have hr : iregs.all.Nodup := by decide
  have h0 : ∀ y ∈ iregs.all, y ≠ 0 := by decide
  obtain ⟨C, hC⟩ := Interp.call_exec Q iregs hr h0
  exact ⟨C, hC⟩

/-- The width needed by the host. -/
def hostWidth (n A k : ℕ) : ℕ :=
  (BIGv n A k + trials n * seedWidth n + (2 * majorityHalf n + 2) * (coinSpan A k n + 2)).size +
    1000 * (n + 1) ^ 3 * (k + 1) + 2 * A.size + 4 * seedWidth n + 64 + (2 * trials n + 2).size

def runTapeDirty : List ℕ := [107, 108, 100, 101, 104, 109, rVotes]

/-- One parity run on tape `j`: add the run's output bit to the vote count. -/
theorem runTape_w {τ : Tapes} {J : ℕ} (Q : Program) (C : ℕ) (hC : ICall Q iregs C)
    {n A k b : ℕ} (S : Store) (hinv : HostInv n A k b S) (hb : hostWidth n A k ≤ b)
    (hf : Cmd.FieldsFit J (runTape Q))
    (j vt : ℕ) (hj : j < 2 * majorityHalf n) (rj : S.mem (cell rJ) = j)
    (rv : S.mem (cell rVotes) = vt) (hvt : vt ≤ j)
    (x : List Bool) (rxl : S.mem (cell 106) = x.length) (hxl : x.length ≤ 128 * (n + 1) ^ 3)
    (xbits : ∀ i (hi : i < x.length), S.mem (xBase + i) = (x[i]'hi).toNat)
    (st : State)
    (hfin : Q.final ⟨x, windowCoins τ.coins (trials n * seedWidth n + j * coinSpan A k n)
      (coinSpan A k n), [], noOracle⟩ = some st) (hwork : st.work ≤ coinSpan A k n) :
    ∃ S' w, WExec τ J (runTape Q) S S' w ∧
      w ≤ 8 * (b * (5 * b + 9) + 15) * (4 * b + 4 * J + 4) + (J + 4) +
        C * (coinSpan A k n + 1) * (b + J + 1) ∧
      HostInv n A k b S' ∧ S'.mem (cell rVotes) = vt + capValue st.out ∧
      S'.out = S.out ∧ ∀ a, 14 ≤ a → (∀ d ∈ runTapeDirty, a ≠ cell d) → S'.mem a = S.mem a := by
  classical
  unfold hostWidth at hb
  set L := coinSpan A k n with hL
  set co := trials n * seedWidth n + j * L with hco
  have hfit := hinv.fits
  have hb2 : 2 ≤ b := by
    generalize 1000 * (n + 1) ^ 3 * (k + 1) = P at hb; omega
  have hbig : (BIGv n A k + trials n * seedWidth n + (2 * majorityHalf n + 2) * (L + 2)).size ≤ b := by
    generalize 1000 * (n + 1) ^ 3 * (k + 1) = P at hb; omega
  have sz (x : ℕ) (hx : x ≤ BIGv n A k + trials n * seedWidth n + (2 * majorityHalf n + 2) * (L + 2)) :
      x.size ≤ b := (Nat.size_le_size hx).trans hbig
  have jL : j * L ≤ (2 * majorityHalf n + 2) * (L + 2) := by
    exact Nat.mul_le_mul (by omega : j ≤ 2 * majorityHalf n + 2) (by omega : L ≤ L + 2)
  unfold runTape at hf
  simp only [Cmd.FieldsFit] at hf
  obtain ⟨hf1, hf2, hf3, hf4⟩ := hf
  -- first circuit
  set C1 := [asg 107 (.arithmetic .mul rJ rL), asg 107 (.add 107 rTapeBase),
      asg 108 (.add rL rZero), asg 100 (.literal 0), asg 101 (.literal 1),
      asg 104 (.literal 0), asg 109 (.literal 2)] with hC1
  have rl := hinv.rl
  have rtb := hinv.rtb
  have r0 := hinv.consts.zero
  have w1 : Circuit.width (fun i => S.mem (cell i)) C1 ≤ b := by
    have rj' : S.mem (cell 18) = j := rj
    have rl' : S.mem (cell 10) = L := rl
    have rtb' : S.mem (cell 34) = trials n * seedWidth n := rtb
    have r0' : S.mem (cell 15) = 0 := r0
    simp only [hC1, Circuit.width, asg, Expression.width, Expression.eval, Arithmetic.value,
      Assignment.update, Function.update, rJ, rL, rTapeBase, rZero]
    simp only [rj', rl', rtb', r0']
    simp
    try simp only [← hL]
    have hc : (2 * j + 2) ≤ (2 * majorityHalf n + 2) * (L + 2) :=
      le_trans (by omega : 2 * j + 2 ≤ (2 * majorityHalf n + 2) * 2)
        (Nat.mul_le_mul_left _ (by omega))
    have hL2 : L ≤ (2 * majorityHalf n + 2) * (L + 2) :=
      le_trans (by omega : L ≤ L + 2) (Nat.le_mul_of_pos_left _ (by omega))
    refine ⟨sz _ (by omega), sz _ (by omega), sz _ (by omega), sz _ (by omega), by omega,
      Nat.size_le.mpr (lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hb2))⟩
  obtain ⟨T1, e1, v1, o1, f1⟩ := wcirc (τ := τ) (J := J) C1 S hfit hb2 w1 hf1
  have res1 (i : ℕ) : T1.mem (cell i) = Circuit.result (fun i => S.mem (cell i)) C1 i := v1 i
  have keep1 (a : ℕ) (ha : 14 ≤ a) (h1 : a ≠ cell 107) (h2 : a ≠ cell 108) (h3 : a ≠ cell 100)
      (h4 : a ≠ cell 101) (h5 : a ≠ cell 104) (h6 : a ≠ cell 109) : T1.mem a = S.mem a := by
    have e : a = cell (a - 14) := by simp [cell]; omega
    rw [e, res1, Circuit.result_untouched]
    simp only [hC1, asg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp only [cell] at h1 h2 h3 h4 h5 h6
    omega
  have t107 : T1.mem (cell 107) = co := by
    rw [res1]; simp [hC1, Circuit.result, asg, Assignment.update, Expression.eval, Arithmetic.value,
      Function.update, rJ, rL, rTapeBase, rZero]
    have rj' : S.mem (cell 18) = j := rj
    have rl' : S.mem (cell 10) = L := rl
    have rtb' : S.mem (cell 34) = trials n * seedWidth n := rtb
    rw [rj', rl', rtb', hco]; ring
  have t108 : T1.mem (cell 108) = L := by
    rw [res1]; simp [hC1, Circuit.result, asg, Assignment.update, Expression.eval,
      Function.update, rL, rZero]
    have rl' : S.mem (cell 10) = L := rl
    have r0' : S.mem (cell 15) = 0 := r0
    rw [rl', r0']; simp
  have tlit (d c : ℕ) (hd : d = 100 ∧ c = 0 ∨ d = 101 ∧ c = 1 ∨ d = 104 ∧ c = 0 ∨ d = 109 ∧ c = 2) :
      T1.mem (cell d) = c := by
    rw [res1]
    rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [hC1, Circuit.result, asg, Assignment.update, Expression.eval, Function.update]
  -- clear cell 0
  set T2 := T1.write 0 0 with hT2
  have e2 : WExec τ J (.op (.const 0 0)) T1 T2 (Op.cost τ T1 (.const 0 0)) := WExec.op T1 _
  have m2 (a : ℕ) (ha : 14 ≤ a) : T2.mem a = T1.mem a := by
    simp [hT2, Store.write, Function.update_of_ne (show a ≠ 0 by omega)]
  have m2c (i : ℕ) : T2.mem (cell i) = T1.mem (cell i) := m2 _ (by simp [cell])
  have m20 : T2.mem 0 = 0 := by simp [hT2, Store.write]
  -- the interpreter call
  have hbase (a : ℕ) (ha : LOGv n ≤ a) : T2.mem a = 0 := by
    have h14 : 14 ≤ a := by simp only [LOGv, VBv, xBase] at ha; omega
    rw [m2 a h14, keep1 a h14 (by simp [cell, LOGv, VBv, xBase] at ha ⊢; omega)
      (by simp [cell, LOGv, VBv, xBase] at ha ⊢; omega) (by simp [cell, LOGv, VBv, xBase] at ha ⊢; omega)
      (by simp [cell, LOGv, VBv, xBase] at ha ⊢; omega) (by simp [cell, LOGv, VBv, xBase] at ha ⊢; omega)
      (by simp [cell, LOGv, VBv, xBase] at ha ⊢; omega)]
    exact hinv.high a ha
  have regT2 (d : ℕ) (hd : d ∈ invRegs) : T2.mem (cell d) = S.mem (cell d) := by
    have hn : d ≠ 107 ∧ d ≠ 108 ∧ d ≠ 100 ∧ d ≠ 101 ∧ d ≠ 104 ∧ d ≠ 109 := by
      revert d; decide
    rw [m2c, keep1 _ (by simp [cell])] <;> simp only [cell] <;> omega
  obtain ⟨S3, k3, e3, hk3, cap3, run3, out3, frame3⟩ := hC τ J x co L L (BIGv n A k) (LOGv n) xBase st T2
    hfin hwork hf3
    (by change T2.mem (cell 100) = _; rw [m2c]; exact tlit 100 0 (by simp)) (by change T2.mem (cell 101) = _; rw [m2c]; exact tlit 101 1 (by simp))
    (by change T2.mem (cell 104) = _; rw [m2c]; exact tlit 104 0 (by simp)) (by change T2.mem (cell 109) = _; rw [m2c]; exact tlit 109 2 (by simp))
    (by change T2.mem (cell 110) = _; rw [regT2 110 (by simp [invRegs])]; exact hinv.rone')
    (by change T2.mem (cell 111) = _; rw [regT2 111 (by simp [invRegs])]; exact hinv.rzero')
    (by change T2.mem (cell 112) = _; rw [regT2 112 (by simp [invRegs])]; exact hinv.rds)
    (by change T2.mem (cell 113) = _; rw [regT2 113 (by simp [invRegs])]; exact hinv.t1)
    (by change T2.mem (cell 114) = _; rw [regT2 114 (by simp [invRegs])]; exact hinv.t2)
    (by change T2.mem (cell 115) = _; rw [regT2 115 (by simp [invRegs])]; exact hinv.t3)
    (by change T2.mem (cell 116) = _; rw [regT2 116 (by simp [invRegs])]; exact hinv.t4)
    (by change T2.mem (cell 117) = _; rw [regT2 117 (by simp [invRegs])]; exact hinv.t5)
    (by change T2.mem (cell 118) = _; rw [regT2 118 (by simp [invRegs])]; exact hinv.t6)
    m20
    (by change T2.mem (cell 102) = _; rw [regT2 102 (by simp [invRegs])]; exact hinv.rbig)
    (by change T2.mem (cell 103) = _; rw [regT2 103 (by simp [invRegs])]; exact hinv.rlog)
    (by change T2.mem (cell 105) = _; rw [regT2 105 (by simp [invRegs])]; exact hinv.rxb)
    (by change T2.mem (cell 106) = _; rw [m2c, keep1 _ (by simp [cell]) (by simp [cell]) (by simp [cell]) (by simp [cell])
      (by simp [cell]) (by simp [cell]) (by simp [cell])]; exact rxl)
    (by change T2.mem (cell 107) = _; rw [m2c]; exact t107)
    (by change T2.mem (cell 108) = _; rw [m2c]; exact t108)
    (by decide)
    (by simp only [LOGv, VBv]; omega) (by simp only [BIGv]; omega)
    (by
      intro i hi
      have h14 : 14 ≤ xBase + i := by simp [xBase]; omega
      rw [m2 _ h14, keep1 _ h14 (by simp [cell, xBase]; omega) (by simp [cell, xBase]; omega)
        (by simp [cell, xBase]; omega) (by simp [cell, xBase]; omega) (by simp [cell, xBase]; omega)
        (by simp [cell, xBase]; omega)]
      exact xbits i hi)
    (fun u => hbase _ (by simp only [BIGv]; omega))
    (fun i _ => hbase _ (by omega))
  have fT2 : T2.Fits b := by
    intro a; by_cases h : a = 0
    · subst h; rw [m20]; simp
    · simp [hT2, Store.write, Function.update_of_ne h]; exact f1 a
  have capv : capValue st.out ≤ 2 := by
    unfold capValue; split <;> [omega; (rename_i bb _; cases bb <;> simp)]
  have fS3 : S3.Fits b := by
    intro a
    by_cases hc : a = iregs.cap
    · rw [hc, cap3]; exact (Nat.size_le_size capv).trans (by simpa using (show Nat.size 2 ≤ b from
        Nat.size_le.mpr (lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hb2))))
    by_cases hr : a = iregs.run
    · rw [hr, run3]; simp
    rw [frame3 a hc hr]; exact fT2 a
  have s3c (i : ℕ) (h1 : cell i ≠ iregs.cap) (h2 : cell i ≠ iregs.run) : S3.mem (cell i) = T2.mem (cell i) :=
    frame3 _ h1 h2
  have s3v : S3.mem (cell rVotes) = vt := by
    rw [s3c _ (by simp [cell, iregs, rVotes]) (by simp [cell, iregs, rVotes]), m2c,
      keep1 _ (by simp [cell]) (by simp [cell, rVotes]) (by simp [cell, rVotes]) (by simp [cell, rVotes])
      (by simp [cell, rVotes]) (by simp [cell, rVotes]) (by simp [cell, rVotes])]
    exact rv
  have s3cap : S3.mem (cell 109) = capValue st.out := cap3
  set C2 := [asg rVotes (.add rVotes 109)] with hC2
  have w2 : Circuit.width (fun i => S3.mem (cell i)) C2 ≤ b := by
    have a1 : S3.mem (cell 35) = vt := s3v
    simp only [hC2, Circuit.width, asg, Expression.width, Expression.eval, rVotes, a1, s3cap]
    simp
    have hX : 2 * majorityHalf n + 2 ≤ (2 * majorityHalf n + 2) * (L + 2) :=
      Nat.le_mul_of_pos_right _ (by omega)
    exact sz _ (by omega)
  obtain ⟨S4, e4, v4, o4, f4⟩ := wcirc (τ := τ) (J := J) C2 S3 fS3 hb2 w2 hf4
  have keep4 (a : ℕ) (ha : 14 ≤ a) (h1 : a ≠ cell rVotes) : S4.mem a = S3.mem a := by
    have e : a = cell (a - 14) := by simp [cell]; omega
    rw [e, v4, Circuit.result_untouched]
    simp only [hC2, asg, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
    simp only [cell, rVotes] at h1 ⊢; omega
  have frameAll (a : ℕ) (ha : 14 ≤ a) (hd : ∀ d ∈ runTapeDirty, a ≠ cell d) : S4.mem a = S.mem a := by
    simp only [runTapeDirty, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hd
    obtain ⟨d1, d2, d3, d4, d5, d6, d7⟩ := hd
    rw [keep4 a ha d7, frame3 a d6 d4, m2 a ha, keep1 a ha d1 d2 d3 d4 d5 d6]
  have m1 : Circuit.multiplicity (fun i => S.mem (cell i)) C1 = 7 := by
    simp [hC1, Circuit.multiplicity, asg, Expression.multiplicity]
  have m4 : Circuit.multiplicity (fun i => S3.mem (cell i)) C2 = 1 := by
    simp [hC2, Circuit.multiplicity, asg, Expression.multiplicity]
  have c2 : Op.cost τ T1 (.const 0 0) = 1 := by simp [Op.cost]
  have hsz : (BIGv n A k + co + L).size ≤ b := by
    apply sz
    have : (j + 1) * L ≤ (2 * majorityHalf n + 2) * (L + 2) :=
      Nat.mul_le_mul (by omega) (by omega)
    have e : co + L = trials n * seedWidth n + (j + 1) * L := by rw [hco]; ring
    omega
  have hk3' : k3 ≤ C * (L + 1) * (b + J + 1) := by
    refine hk3.trans (Nat.mul_le_mul_left _ ?_); omega
  have ex : WExec τ J (runTape Q) S S4 _ := e1.seq (e2.seq (e3.seq e4))
  refine ⟨S4, _, ex, ?_, ?_, ?_, ?_, frameAll⟩
  · rw [m1, m4, c2]
    have : 7 * (b * (5 * b + 9) + 15) * (4 * b + 4 * J + 4) + (1 * (b * (5 * b + 9) + 15) *
      (4 * b + 4 * J + 4)) = 8 * (b * (5 * b + 9) + 15) * (4 * b + 4 * J + 4) := by ring
    omega
  · refine hinv.congr (fun d hd => frameAll _ (by simp [cell]) ?_) (fun a ha => frameAll a ?_ ?_) f4
    · have hn : d ≠ 107 ∧ d ≠ 108 ∧ d ≠ 100 ∧ d ≠ 101 ∧ d ≠ 104 ∧ d ≠ 109 ∧ d ≠ rVotes := by
        revert d; decide
      simp only [runTapeDirty, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
        cell]; omega
    · simp only [VBv, xBase] at ha; omega
    · simp only [VBv, xBase] at ha
      simp only [runTapeDirty, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
        cell, rVotes]; omega
  · rw [v4]; simp [hC2, Circuit.result, asg, Assignment.update, Expression.eval, Function.update, rVotes]
    have a1 : S3.mem (cell 35) = vt := s3v
    rw [a1, s3cap]
  · rw [o4, out3]; simp [hT2, Store.write, o1]

end DirectedHamiltonicity.Main.CycleHost


-- ===== Solutions/Dev/Asm3.lean =====

set_option autoImplicit false

namespace DirectedHamiltonicity.Main.CycleHost

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word
open TargetedSamplers.Structured.Work
open TargetedSamplers.Structured.Interp DirectedHamiltonicity.Main.CycleReduction

theorem final_of_runsIn {P : Program} {τ : Tapes} {c : ℕ} {bb : Bool} (h : P.RunsIn τ c (some [bb])) :
    ∃ st, P.final τ = some st ∧ st.work ≤ c ∧ st.out = [bb] := by
  obtain ⟨st, h1, h2, h3⟩ := h
  refine ⟨st, h1, h2, ?_⟩
  unfold State.result at h3
  split at h3 <;> simp_all

theorem capValue_single (bb : Bool) : capValue [bb] = bb.toNat := by simp [capValue]

theorem cost_a (X R r J b w2 jc : ℕ) (hw2 : w2 ≤ 2 * r * (R + 7 * J + 7 * b + 3) + 3 * J + 2 * b + 1)
    (hjc : jc ≤ 3 * J + 2 * b + 1) :
    2 * X + (w2 + (jc + 0)) ≤ (2 * r + 1) * (R + 7 * J + 7 * b + 3) + 3 * X + 3 * J + 2 * b + 1 := by
  have : (2 * r + 1) * (R + 7 * J + 7 * b + 3) = 2 * r * (R + 7 * J + 7 * b + 3) + (R + 7 * J + 7 * b + 3) := by
    ring
  rw [this]; generalize 2 * r * (R + 7 * J + 7 * b + 3) = Y at *; omega

theorem cost_b (X R r J b w2 jc jc0 : ℕ) (hw2 : w2 ≤ 2 * r * (R + 7 * J + 7 * b + 3) + 3 * J + 2 * b + 1)
    (hjc : jc ≤ 3 * J + 2 * b + 1) (hjc0 : jc0 ≤ J + 2 * b + 1) :
    2 * X + (w2 + (jc + X + jc0)) ≤ (2 * r + 1) * (R + 7 * J + 7 * b + 3) + 3 * X + 3 * J + 2 * b + 1 := by
  have : (2 * r + 1) * (R + 7 * J + 7 * b + 3) = 2 * r * (R + 7 * J + 7 * b + 3) + (R + 7 * J + 7 * b + 3) := by
    ring
  rw [this]; generalize 2 * r * (R + 7 * J + 7 * b + 3) = Y at *; omega

def runCost (n A k b J C : ℕ) : ℕ :=
  8 * (b * (5 * b + 9) + 15) * (4 * b + 4 * J + 4) + (J + 4) +
    C * (coinSpan A k n + 1) * (b + J + 1) + 7 * J + 7 * b + 3

/-- The vote loop over the `2r` parity strings. -/
def votesCmd (Q : Program) : Cmd :=
  .seq (circ [asg rVotes (.literal 0), asg rJ (.literal 0)])
    (.seq (loop rJ rR2 (runTape Q)) (ifLe rVotes rR .skip (circ [asg rFlag (.literal 1)])))

def votesDirty : List ℕ := [rJ, rFlag] ++ runTapeDirty

theorem votes_w {τ : Tapes} {J : ℕ} (Q : Program) (C : ℕ) (hC : ICall Q iregs C)
    {n A k b : ℕ} (S : Store) (hinv : HostInv n A k b S) (hb : hostWidth n A k ≤ b)
    (hf : Cmd.FieldsFit J (votesCmd Q))
    (x : List Bool) (rxl : S.mem (cell 106) = x.length) (hxl : x.length ≤ 128 * (n + 1) ^ 3)
    (xbits : ∀ i (hi : i < x.length), S.mem (xBase + i) = (x[i]'hi).toNat)
    (hQ : ∀ coins : List Bool, ∃ cost, Q.RunsIn (runTapes x coins) cost (some [outputBit Q x coins]) ∧
      cost ≤ coinSpan A k n)
    (f : ℕ) (rf : S.mem (cell rFlag) = f) :
    ∃ S' w, WExec τ J (votesCmd Q) S S' w ∧
      w ≤ (2 * majorityHalf n + 1) * (runCost n A k b J C + 7 * J + 7 * b + 3) +
        3 * (b * (5 * b + 9) + 15) * (4 * b + 4 * J + 4) + 3 * J + 2 * b + 1 ∧
      HostInv n A k b S' ∧
      S'.mem (cell rFlag) = (if majority (fun tape => outputBit Q x (List.ofFn tape)) (majorityHalf n)
        (panelFromTape n (coinSpan A k n) τ.coins).2 then 1 else f) ∧
      S'.out = S.out ∧ ∀ a, 14 ≤ a → (∀ d ∈ votesDirty, a ≠ cell d) → S'.mem a = S.mem a := by
  classical
  have hb0 := hb
  unfold hostWidth at hb0
  set L := coinSpan A k n with hL
  set r := majorityHalf n with hr
  have hfit := hinv.fits
  have c14 : ∀ i, 14 ≤ cell i := fun i => by unfold cell; omega
  have hb2 : 2 ≤ b := by generalize 1000 * (n + 1) ^ 3 * (k + 1) = P at hb0; omega
  have hbig : (BIGv n A k + trials n * seedWidth n + (2 * r + 2) * (L + 2)).size ≤ b := by
    generalize 1000 * (n + 1) ^ 3 * (k + 1) = P at hb0; omega
  have sz (y : ℕ) (hy : y ≤ BIGv n A k + trials n * seedWidth n + (2 * r + 2) * (L + 2)) :
      y.size ≤ b := (Nat.size_le_size hy).trans hbig
  have hX : 2 * r + 2 ≤ (2 * r + 2) * (L + 2) := Nat.le_mul_of_pos_right _ (by omega)
  unfold votesCmd at hf
  simp only [Cmd.FieldsFit] at hf
  obtain ⟨hf1, hf2, hf3⟩ := hf
  -- outputs of the individual runs
  let ob (j : ℕ) : Bool := outputBit Q x (windowCoins τ.coins (trials n * seedWidth n + j * L) L)
  -- initial circuit
  set C0 := [asg rVotes (.literal 0), asg rJ (.literal 0)] with hC0
  have w0 : Circuit.width (fun i => S.mem (cell i)) C0 ≤ b := by
    simp [hC0, Circuit.width, asg, Expression.width, Expression.eval]
  obtain ⟨S1, e1, v1, o1, f1⟩ := wcirc (τ := τ) (J := J) C0 S hfit hb2 w0 hf1
  have keep1 (a : ℕ) (ha : 14 ≤ a) (h1 : a ≠ cell rVotes) (h2 : a ≠ cell rJ) : S1.mem a = S.mem a := by
    have e : a = cell (a - 14) := by simp [cell]; omega
    rw [e, v1, Circuit.result_untouched]
    simp only [hC0, asg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp only [cell, rVotes, rJ] at h1 h2 ⊢; omega
  have s1v : S1.mem (cell rVotes) = 0 := by
    rw [v1]; simp [hC0, Circuit.result, asg, Assignment.update, Expression.eval, Function.update, rVotes, rJ]
  have s1j : S1.mem (cell rJ) = 0 := by
    rw [v1]; simp [hC0, Circuit.result, asg, Assignment.update, Expression.eval, Function.update, rVotes, rJ]
  have hinv1 : HostInv n A k b S1 := by
    refine hinv.congr (fun d hd => keep1 _ (c14 _) ?_ ?_) (fun a ha => keep1 a ?_ ?_ ?_) f1
    · have : d ≠ rVotes := by revert d; decide
      simp only [cell]; omega
    · have : d ≠ rJ := by revert d; decide
      simp only [cell]; omega
    · simp only [VBv, xBase] at ha; omega
    · simp only [VBv, xBase, cell, rVotes] at ha ⊢; omega
    · simp only [VBv, xBase, cell, rJ] at ha ⊢; omega
  have hfb : Cmd.FieldsFit J (runTape Q) := by
    have h := hf2; simp only [loop, forRange, Cmd.FieldsFit] at h; exact h.2.2.1
  let state (j : ℕ) (U : Store) : Prop :=
    HostInv n A k b U ∧ U.mem (cell rJ) = j ∧
      U.mem (cell rVotes) = ∑ j' ∈ Finset.range j, (ob j').toNat ∧ U.out = S.out ∧
      ∀ a, 14 ≤ a → (∀ d ∈ rJ :: runTapeDirty, a ≠ cell d) → U.mem a = S.mem a
  have start : state 0 S1 := by
    refine ⟨hinv1, s1j, by simp [s1v], o1, fun a ha hd => keep1 a ha ?_ ?_⟩
    · exact hd rVotes (by simp [runTapeDirty])
    · exact hd rJ (by simp)
  have sumle (j : ℕ) : ∑ j' ∈ Finset.range j, (ob j').toNat ≤ j := by
    calc _ ≤ ∑ j' ∈ Finset.range j, 1 := Finset.sum_le_sum (fun i _ => Bool.toNat_le _)
      _ = j := by simp
  have body (j : ℕ) (hj : j < 2 * r) (U : Store) (hU : state j U) :
      ∃ U' w, WExec τ J (runTape Q) U U' w ∧ w ≤ runCost n A k b J C ∧ U'.mem (cell rJ) = 0 + j ∧
        U'.mem (cell rOne) = 1 ∧ (U'.mem 0).size ≤ b ∧ state (j + 1) (U'.write (cell rJ) (0 + j + 1)) := by
    obtain ⟨hiU, rjU, rvU, oU, frU⟩ := hU
    have keepS (a : ℕ) (ha : 14 ≤ a) (hd : ∀ d ∈ votesDirty, a ≠ cell d) : U.mem a = S.mem a :=
      frU a ha (fun d hd' => hd d (by simp [votesDirty] at hd' ⊢; tauto))
    obtain ⟨cost, hrun, hcost⟩ := hQ (windowCoins τ.coins (trials n * seedWidth n + j * L) L)
    obtain ⟨st, hfin, hwork, hout⟩ := final_of_runsIn hrun
    have c106 : U.mem (cell 106) = x.length := by
      rw [keepS _ (c14 _) (by simp [votesDirty, runTapeDirty, cell, rJ, rFlag, rVotes])]; exact rxl
    have xb' (i : ℕ) (hi : i < x.length) : U.mem (xBase + i) = (x[i]'hi).toNat := by
      have h1 : 14 ≤ xBase + i := by simp [xBase]; omega
      have h2 : ∀ d ∈ votesDirty, xBase + i ≠ cell d := by
        simp [votesDirty, runTapeDirty, cell, xBase, rJ, rFlag, rVotes]; omega
      rw [keepS _ h1 h2]; exact xbits i hi
    obtain ⟨U', w, ex, hw, hiU', vU', oU', frU'⟩ := runTape_w (τ := τ) (J := J) Q C hC U hiU hb hfb j
      (∑ j' ∈ Finset.range j, (ob j').toNat) hj rjU rvU (sumle j) x c106 hxl xb'
      st hfin (hwork.trans hcost)
    have rjU' : U'.mem (cell rJ) = j := by
      rw [frU' _ (c14 _) (by simp [runTapeDirty, cell, rJ, rVotes])]; exact rjU
    refine ⟨U', w, ex, ?_, by rw [rjU']; simp, hiU'.consts.one, hiU'.fits 0, ?_⟩
    · unfold runCost; omega
    · have fitW : (U'.write (cell rJ) (0 + j + 1)).Fits b :=
        Store.write_fits hiU'.fits _ (sz _ (by omega))
      refine ⟨hiU'.congr (fun d hd => ?_) (fun a ha => ?_) fitW, ?_, ?_, ?_, ?_⟩
      · have : d ≠ rJ := by revert d; decide
        simp [Store.write, cell, Function.update_of_ne (show 14 + d ≠ 14 + rJ by omega)]
      · simp only [VBv, xBase] at ha
        simp [Store.write, cell, Function.update_of_ne (show a ≠ 14 + rJ by simp [rJ]; omega)]
      · simp [Store.write]
      · rw [show (U'.write (cell rJ) (0 + j + 1)).mem (cell rVotes) = U'.mem (cell rVotes) by
          simp [Store.write, cell, rJ, rVotes]]
        rw [vU', Finset.sum_range_succ, hout, capValue_single]
      · simp [Store.write, oU', oU]
      · intro a ha hd
        have h1 : a ≠ cell rJ := hd rJ (by simp)
        rw [show (U'.write (cell rJ) (0 + j + 1)).mem a = U'.mem a by
          simp [Store.write, Function.update_of_ne h1]]
        rw [frU' a ha (fun d hd' => hd d (List.mem_cons_of_mem _ hd'))]
        exact frU a ha hd
  have ctrl : ∀ i ≤ 2 * r, ∀ U, state i U → U.mem (cell rJ) = 0 + i ∧ U.mem (cell rR2) = 0 + 2 * r := by
    intro i _ U hU; exact ⟨by rw [hU.2.1]; simp, by rw [hU.1.rr2]; simp [hr]⟩
  obtain ⟨S2, w2, e2, hw2, hS2⟩ := wforRange (τ := τ) (J := J) (b := b) (cell rJ) (cell rR2) (cell rOne)
    0 (2 * r) (runCost n A k b J C) (runTape Q) state hf2 ctrl (sz _ (by omega)) body S1 start
  obtain ⟨hi2, rj2, rv2, o2, fr2⟩ := hS2
  -- the majority value
  have hcard : (Finset.univ.filter (fun i : Fin (2 * r) =>
      (fun tape => outputBit Q x (List.ofFn tape)) ((panelFromTape n L τ.coins).2 i) = true)).card =
      ∑ j' ∈ Finset.range (2 * r), (ob j').toNat := by
    rw [Finset.card_filter, ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    have : List.ofFn ((panelFromTape n L τ.coins).2 i) =
        windowCoins τ.coins (trials n * seedWidth n + i.val * L) L := by
      unfold windowCoins; congr 1; funext u; rw [panel_tape]
    simp only [this, ob]
    cases outputBit Q x (windowCoins τ.coins (trials n * seedWidth n + i.val * L) L) <;> rfl
  have hmaj : majority (fun tape => outputBit Q x (List.ofFn tape)) r (panelFromTape n L τ.coins).2 =
      decide (r < S2.mem (cell rVotes)) := by
    unfold majority; rw [rv2, ← hcard]
  have rf2 : S2.mem (cell rFlag) = f := by
    rw [fr2 _ (c14 _) (by simp [runTapeDirty, cell, rFlag, rJ, rVotes])]; exact rf
  have rr2' : S2.mem (cell rR) = r := hi2.rr
  have szv : (S2.mem (cell rVotes)).size ≤ b := hi2.fits _
  have szr : (S2.mem (cell rR)).size ≤ b := hi2.fits _
  have hfin3 := hf3
  simp only [ifLe, Cmd.FieldsFit] at hfin3
  obtain ⟨hv1, hv2, _, hv4⟩ := hfin3
  have jc := jumpCost_le (J := J) (s := S2) (b := b) hv1 hv2 szv szr
  have Xc : 0 ≤ (b * (5 * b + 9) + 15) * (4 * b + 4 * J + 4) := Nat.zero_le _
  have sub : ∀ d ∈ rJ :: runTapeDirty, d ∈ votesDirty := by
    intro d hd
    simp only [runTapeDirty, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with h | h | h | h | h | h | h | h <;> subst h <;> decide
  by_cases hvr : S2.mem (cell rVotes) ≤ S2.mem (cell rR)
  · -- no majority: flag unchanged
    have ex3 : WExec τ J (ifLe rVotes rR .skip (circ [asg rFlag (.literal 1)])) S2 S2
        (jumpCost J S2 (cell rVotes) (cell rR) + 0) := WExec.yes hvr (WExec.skip S2)
    have exAll : WExec τ J (votesCmd Q) S S2
        (Circuit.multiplicity (fun i => S.mem (cell i)) C0 * (b * (5 * b + 9) + 15) * (4 * b + 4 * J + 4) +
          (w2 + (jumpCost J S2 (cell rVotes) (cell rR) + 0))) := by
      unfold votesCmd; exact e1.seq (e2.seq ex3)
    have frA : ∀ a, 14 ≤ a → (∀ d ∈ votesDirty, a ≠ cell d) → S2.mem a = S.mem a := by
      intro a ha hd
      exact fr2 a ha (fun d hd' => hd d (sub d hd'))
    refine ⟨S2, _, exAll, ?_, hi2, ?_, o2, frA⟩
    · have m0 : Circuit.multiplicity (fun i => S.mem (cell i)) C0 = 2 := by
        simp [hC0, Circuit.multiplicity, asg, Expression.multiplicity]
      rw [m0]
      have h := cost_a ((b * (5 * b + 9) + 15) * (4 * b + 4 * J + 4)) _ r J b w2 _ hw2 jc
      calc _ = 2 * ((b * (5 * b + 9) + 15) * (4 * b + 4 * J + 4)) +
            (w2 + (jumpCost J S2 (cell rVotes) (cell rR) + 0)) := by ring
        _ ≤ _ := h
        _ = _ := by ring
    · rw [hmaj, rf2]; rw [rr2'] at hvr; simp [show ¬ r < S2.mem (cell rVotes) by omega]
  · -- majority: set the flag
    set C3 := [asg rFlag (.literal 1)] with hC3
    have w3 : Circuit.width (fun i => S2.mem (cell i)) C3 ≤ b := by
      simp [hC3, Circuit.width, asg, Expression.width, Expression.eval]; omega
    obtain ⟨S3, e3, v3, o3, f3⟩ := wcirc (τ := τ) (J := J) C3 S2 hi2.fits hb2 w3 hv4
    have keep3 (a : ℕ) (ha : 14 ≤ a) (h1 : a ≠ cell rFlag) : S3.mem a = S2.mem a := by
      have e : a = cell (a - 14) := by simp [cell]; omega
      rw [e, v3, Circuit.result_untouched]
      simp only [hC3, asg, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
      simp only [cell, rFlag] at h1 ⊢; omega
    have ex3 : WExec τ J (ifLe rVotes rR .skip (circ [asg rFlag (.literal 1)])) S2 S3
        (jumpCost J S2 (cell rVotes) (cell rR) +
          Circuit.multiplicity (fun i => S2.mem (cell i)) C3 * (b * (5 * b + 9) + 15) * (4 * b + 4 * J + 4) +
          jumpCost J S3 0 0) := WExec.no hvr e3
    have exAll : WExec τ J (votesCmd Q) S S3
        (Circuit.multiplicity (fun i => S.mem (cell i)) C0 * (b * (5 * b + 9) + 15) * (4 * b + 4 * J + 4) +
          (w2 + (jumpCost J S2 (cell rVotes) (cell rR) +
          Circuit.multiplicity (fun i => S2.mem (cell i)) C3 * (b * (5 * b + 9) + 15) * (4 * b + 4 * J + 4) +
          jumpCost J S3 0 0))) := by
      unfold votesCmd; exact e1.seq (e2.seq ex3)
    have jc0 := jumpCost_zero_le (J := J) (f3 0)
    refine ⟨S3, _, exAll, ?_, ?_, ?_, by rw [o3, o2], ?_⟩
    · have m0 : Circuit.multiplicity (fun i => S.mem (cell i)) C0 = 2 := by
        simp [hC0, Circuit.multiplicity, asg, Expression.multiplicity]
      have m3 : Circuit.multiplicity (fun i => S2.mem (cell i)) C3 = 1 := by
        simp [hC3, Circuit.multiplicity, asg, Expression.multiplicity]
      rw [m0, m3]
      have h := cost_b ((b * (5 * b + 9) + 15) * (4 * b + 4 * J + 4)) (runCost n A k b J C) r J b w2 _ _ hw2 jc jc0
      calc _ = 2 * ((b * (5 * b + 9) + 15) * (4 * b + 4 * J + 4)) +
            (w2 + (jumpCost J S2 (cell rVotes) (cell rR) + ((b * (5 * b + 9) + 15) * (4 * b + 4 * J + 4)) +
              jumpCost J S3 0 0)) := by ring
        _ ≤ _ := h
        _ = _ := by ring
    · refine hi2.congr (fun d hd => keep3 _ (c14 _) ?_) (fun a ha => keep3 a ?_ ?_) f3
      · have : d ≠ rFlag := by revert d; decide
        simp only [cell]; omega
      · simp only [VBv, xBase] at ha; omega
      · simp only [VBv, xBase, cell, rFlag] at ha ⊢; omega
    · have h1 : S3.mem (cell rFlag) = 1 := by
        rw [v3]; simp [hC3, Circuit.result, asg, Assignment.update, Expression.eval, Function.update]
      rw [h1, hmaj]
      rw [rr2'] at hvr
      simp [show r < S2.mem (cell rVotes) by omega]
    · intro a ha hd
      rw [keep3 a ha (hd rFlag (by simp [votesDirty]))]
      exact fr2 a ha (fun d hd' => hd d (sub d hd'))

end DirectedHamiltonicity.Main.CycleHost


-- ===== Solutions/Dev/Asm4.lean =====

set_option autoImplicit false

namespace DirectedHamiltonicity.Main.CycleHost

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word
open TargetedSamplers.Structured.Work
open TargetedSamplers.Structured.Interp DirectedHamiltonicity.Main.CycleReduction

def candCmd (Q : Program) : Cmd :=
  .seq (circ ([asg rIdx (.arithmetic .mul rT rN), asg rIdx (.add rIdx rS)] ++ bitOf rGp rIdx))
    (ifLe rTmp rZero .skip (.seq buildX (votesCmd Q)))

def candDirty : List ℕ := [rIdx, rTmp] ++ buildXDirty ++ votesDirty

def Xc (b J : ℕ) : ℕ := (b * (5 * b + 9) + 15) * (4 * b + 4 * J + 4)

def votesBound (n A k b J C : ℕ) : ℕ :=
  (2 * majorityHalf n + 1) * (runCost n A k b J C + 7 * J + 7 * b + 3) +
        3 * (b * (5 * b + 9) + 15) * (4 * b + 4 * J + 4) + 3 * J + 2 * b + 1

theorem div_pow_mod_two (x i : ℕ) : x / 2 ^ i % 2 = (x.testBit i).toNat := by
  rw [Nat.testBit, Nat.shiftRight_eq_div_pow]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ i) with h | h <;> simp [h]

theorem cost_c0 (A MX V wb wv jc jc0 X : ℕ) (hA : A ≤ 75 * MX) (hwb : wb ≤ 10 ^ 6 * MX) (hwv : wv ≤ V)
    (hj : jc + jc0 ≤ X) (hX : X ≤ MX) : A + (jc + (wb + wv) + jc0) ≤ V + 10 ^ 8 * MX := by omega

theorem cost_c (n b J idx V wb wv jc jc0 : ℕ) (hidx : idx < n * n)
    (hwb : wb ≤ 10 ^ 6 * (n + 1) ^ 6 * (b + 1) ^ 2 * (4 * b + 4 * J + 4)) (hwv : wv ≤ V)
    (hjc : jc ≤ 3 * J + 2 * b + 1) (hjc0 : jc0 ≤ J + 2 * b + 1) :
    (idx + 5) * (b * (5 * b + 9) + 15) * (4 * b + 4 * J + 4) + (jc + (wb + wv) + jc0) ≤
      V + 10 ^ 8 * (n + 1) ^ 6 * (b + 1) ^ 2 * (4 * b + 4 * J + 4) := by
  have h1 : idx + 5 ≤ 5 * (n + 1) ^ 6 := by
    have : n * n ≤ (n + 1) ^ 6 := by
      calc n * n ≤ (n + 1) * (n + 1) := Nat.mul_le_mul (by omega) (by omega)
        _ = (n + 1) ^ 2 := by ring
        _ ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
    have : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
    omega
  have h2 : b * (5 * b + 9) + 15 ≤ 15 * (b + 1) ^ 2 := by nlinarith
  have h4 : 1 ≤ (n + 1) ^ 6 * (b + 1) ^ 2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hA : (idx + 5) * (b * (5 * b + 9) + 15) * (4 * b + 4 * J + 4) ≤
      75 * ((n + 1) ^ 6 * (b + 1) ^ 2 * (4 * b + 4 * J + 4)) := by
    calc (idx + 5) * (b * (5 * b + 9) + 15) * (4 * b + 4 * J + 4)
        ≤ (5 * (n + 1) ^ 6) * (15 * (b + 1) ^ 2) * (4 * b + 4 * J + 4) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul h1 h2)
      _ = 75 * ((n + 1) ^ 6 * (b + 1) ^ 2 * (4 * b + 4 * J + 4)) := by ring
  have eB : 10 ^ 6 * (n + 1) ^ 6 * (b + 1) ^ 2 * (4 * b + 4 * J + 4) =
      10 ^ 6 * ((n + 1) ^ 6 * (b + 1) ^ 2 * (4 * b + 4 * J + 4)) := by ring
  have eC : 10 ^ 8 * (n + 1) ^ 6 * (b + 1) ^ 2 * (4 * b + 4 * J + 4) =
      10 ^ 8 * ((n + 1) ^ 6 * (b + 1) ^ 2 * (4 * b + 4 * J + 4)) := by ring
  rw [eB] at hwb; rw [eC]
  have hX : 4 * b + 4 * J + 4 ≤ (n + 1) ^ 6 * (b + 1) ^ 2 * (4 * b + 4 * J + 4) :=
    Nat.le_mul_of_pos_left _ h4
  exact cost_c0 _ _ _ _ _ _ _ (4 * b + 4 * J + 4) hA hwb hwv (by omega) hX

theorem cand_w {τ : Tapes} {J : ℕ} (Q : Program) (C : ℕ) (hC : ICall Q iregs C)
    {n A k b : ℕ} (hn : 2 ≤ n) (S : Store) (hinv : HostInv n A k b S) (hb : hostWidth n A k ≤ b)
    (hf : Cmd.FieldsFit J (candCmd Q))
    (Gs : Finset (Fin n × Fin n)) (Gp : ℕ) (hGp : Gp < 2 ^ (n * n))
    (bits : ∀ x y : Fin n, Gp.testBit (x.val * n + y.val) = adjacency Gs x y)
    (s t : Fin n) (z : MatrixSeed n) (B : ℕ) (hB : B ≤ Bmax n) (sym wt : ℕ)
    (hsym : sym < 50 ^ (n * n)) (hwt : wt < Wmax n ^ (n * 3))
    (symd : ∀ x y : Fin n, sym / 50 ^ (x.val * n + y.val) % 50 = (z.1 (x, y)).val)
    (wtd : ∀ (y : Fin n) (l : Fin 3), wt / Wmax n ^ (y.val * 3 + l.val) % Wmax n = (z.2 (y, l)).val)
    (rg : S.mem (cell rGp) = Gp) (rs : S.mem (cell rS) = s.val) (rt : S.mem (cell rT) = t.val)
    (rb : S.mem (cell rB) = B) (rsym : S.mem (cell rSym) = sym) (rwt : S.mem (cell rWt) = wt)
    (hQ : adjacency Gs t s = true → ∀ coins : List Bool, ∃ cost,
      Q.RunsIn (runTapes (candX (adjacency Gs) s t z B) coins) cost
        (some [outputBit Q (candX (adjacency Gs) s t z B) coins]) ∧ cost ≤ coinSpan A k n)
    (f : ℕ) (rf : S.mem (cell rFlag) = f) :
    ∃ S' w, WExec τ J (candCmd Q) S S' w ∧
      w ≤ votesBound n A k b J C + 10 ^ 8 * (n + 1) ^ 6 * (b + 1) ^ 2 * (4 * b + 4 * J + 4) ∧
      HostInv n A k b S' ∧
      S'.mem (cell rFlag) = (if adjacency Gs t s = true then
        (if majority (fun tape => outputBit Q (candX (adjacency Gs) s t z B) (List.ofFn tape))
          (majorityHalf n) (panelFromTape n (coinSpan A k n) τ.coins).2 then 1 else f) else f) ∧
      S'.out = S.out ∧ ∀ a, 14 ≤ a → (∀ d ∈ candDirty, a ≠ cell d) → (a < xBase ∨ VBv n ≤ a) →
        S'.mem a = S.mem a := by
  classical
  have hb0 := hb
  unfold hostWidth at hb0
  have hfit := hinv.fits
  have c14 : ∀ i, 14 ≤ cell i := fun i => by unfold cell; omega
  have hb2 : 2 ≤ b := by generalize 1000 * (n + 1) ^ 3 * (k + 1) = P at hb0; omega
  have hb3 : 64 * (n + 1) ^ 3 ≤ b := by
    have : 64 * (n + 1) ^ 3 ≤ 1000 * (n + 1) ^ 3 * (k + 1) := by nlinarith [Nat.zero_le ((n+1)^3)]
    generalize 1000 * (n + 1) ^ 3 * (k + 1) = P at hb0 this; omega
  have nn : n * n ≤ (n + 1) ^ 3 := by nlinarith
  have hsz (y : ℕ) (hy : y < 2 ^ (n * n + 2)) : y.size ≤ b := by
    have : y.size ≤ n * n + 2 := Nat.size_le.mpr hy
    omega
  unfold candCmd at hf
  simp only [Cmd.FieldsFit] at hf
  obtain ⟨hf1, hv1, hv2, _, hf3⟩ := hf
  -- adjacency bit
  have rn := hinv.rn
  have r0 := hinv.consts.zero
  have r2 := hinv.consts.two
  set idx := t.val * n + s.val with hidx
  have hidx' : idx < n * n := by
    have := t.isLt; have := s.isLt
    calc idx = t.val * n + s.val := rfl
      _ < t.val * n + n := by omega
      _ = (t.val + 1) * n := by ring
      _ ≤ n * n := Nat.mul_le_mul_right _ (by omega)
  set C1 := [asg rIdx (.arithmetic .mul rT rN), asg rIdx (.add rIdx rS)] ++ bitOf rGp rIdx with hC1
  have pw : 2 ^ idx < 2 ^ (n * n + 2) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have gp2 : 2 * Gp + 2 < 2 ^ (n * n + 2) := by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show n * n ≤ n * n + 1 by omega)
    rw [pow_succ, pow_succ] at *; omega
  have w1 : Circuit.width (fun i => S.mem (cell i)) C1 ≤ b := by
    have rt' : S.mem (cell 24) = t.val := rt
    have rs' : S.mem (cell 23) = s.val := rs
    have rn' : S.mem (cell 0) = n := rn
    have rg' : S.mem (cell 6) = Gp := rg
    have r2' : S.mem (cell 16) = 2 := r2
    simp only [hC1, bitOf, List.cons_append, List.nil_append, Circuit.width, asg, Expression.width,
      Expression.eval, Arithmetic.value, Assignment.update, Function.update, rIdx, rT, rN, rS, rTmp, rGp,
      rTwo]
    simp [rt', rs', rn', rg', r2']
    have ht := t.isLt
    have hP : n * n < 2 ^ (n * n) := Nat.lt_two_pow_self
    have h4 : 2 ^ (n * n + 2) = 4 * 2 ^ (n * n) := by rw [pow_add]; ring
    have h16 : 16 ≤ 2 ^ (n * n) := by
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ (n * n) := Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul hn hn)
    have nle : n ≤ n * n := Nat.le_mul_of_pos_left n (by omega)
    have tn : t.val * n < n * n := lt_of_le_of_lt (Nat.le_add_right _ _) hidx'
    have dle : Gp / 2 ^ idx ≤ Gp := Nat.div_le_self _ _
    have m2 : Gp / 2 ^ idx % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have pw' : 2 ^ idx < 4 * 2 ^ (n * n) := h4 ▸ pw
    have gp2' : 2 * Gp + 2 < 4 * 2 ^ (n * n) := h4 ▸ gp2
    have g (y : ℕ) (hy : y < 4 * 2 ^ (n * n)) : y.size ≤ b := hsz y (h4 ▸ hy)
    have nP : n < 2 ^ (n * n) := lt_of_le_of_lt nle hP
    have a1 : 2 * t.val + 2 < 4 * 2 ^ (n * n) := by omega
    have a2 : t.val * n < 4 * 2 ^ (n * n) := by omega
    have hs' := s.isLt
    have a3 : t.val * n + s.val < 4 * 2 ^ (n * n) := by omega
    have a4 : 6 < 4 * 2 ^ (n * n) := by omega
    have d1 : Gp / 2 ^ (t.val * n + s.val) ≤ Gp := Nat.div_le_self _ _
    have d2 : Gp / 2 ^ (t.val * n + s.val) % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have a5 : Gp / 2 ^ (t.val * n + s.val) < 4 * 2 ^ (n * n) := by omega
    have a6 : 2 * (Gp / 2 ^ (t.val * n + s.val)) + 2 < 4 * 2 ^ (n * n) := by omega
    have a7 : Gp / 2 ^ (t.val * n + s.val) % 2 < 4 * 2 ^ (n * n) := by omega
    exact ⟨g _ a1, g _ a2, g _ a3, g _ a4, g _ pw', g _ gp2', g _ a5, g _ a6, g _ a7⟩
  obtain ⟨S1, e1, v1, o1, f1⟩ := wcirc (τ := τ) (J := J) C1 S hfit hb2 w1 hf1
  have keep1 (a : ℕ) (ha : 14 ≤ a) (h1 : a ≠ cell rIdx) (h2 : a ≠ cell rTmp) : S1.mem a = S.mem a := by
    have e : a = cell (a - 14) := by simp [cell]; omega
    rw [e, v1, Circuit.result_untouched]
    simp only [hC1, bitOf, asg, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq]
    simp only [cell, rIdx, rTmp] at h1 h2 ⊢; omega
  have tmp1 : S1.mem (cell rTmp) = (adjacency Gs t s).toNat := by
    have rt' : S.mem (cell 24) = t.val := rt
    have rs' : S.mem (cell 23) = s.val := rs
    have rn' : S.mem (cell 0) = n := rn
    have rg' : S.mem (cell 6) = Gp := rg
    have r2' : S.mem (cell 16) = 2 := r2
    rw [v1]
    simp only [hC1, bitOf, List.cons_append, List.nil_append, Circuit.result, asg, Assignment.update,
      Expression.eval, Arithmetic.value, Function.update, rIdx, rT, rN, rS, rTmp, rGp, rTwo]
    simp [rt', rs', rn', rg', r2']
    rw [div_pow_mod_two, ← bits t s]
  have hinv1 : HostInv n A k b S1 := by
    refine hinv.congr (fun d hd => keep1 _ (c14 _) ?_ ?_) (fun a ha => keep1 a ?_ ?_ ?_) f1
    · have : d ≠ rIdx := by revert d; decide
      simp only [cell]; omega
    · have : d ≠ rTmp := by revert d; decide
      simp only [cell]; omega
    · simp only [VBv, xBase] at ha; omega
    · simp only [VBv, xBase, cell, rIdx] at ha ⊢; omega
    · simp only [VBv, xBase, cell, rTmp] at ha ⊢; omega
  have r0' : S1.mem (cell rZero) = 0 := hinv1.consts.zero
  have jc := jumpCost_le (J := J) (s := S1) (b := b) hv1 hv2 (f1 _) (f1 _)
  have m1 : Circuit.multiplicity (fun i => S.mem (cell i)) C1 = idx + 5 := by
    have rt' : S.mem (cell 24) = t.val := rt
    have rs' : S.mem (cell 23) = s.val := rs
    have rn' : S.mem (cell 0) = n := rn
    simp only [hC1, bitOf, List.cons_append, List.nil_append, Circuit.multiplicity, asg, Assignment.update,
      Expression.eval, Arithmetic.value, Expression.multiplicity, Function.update, rIdx, rT, rN, rS, rTmp,
      rGp, rTwo]
    simp [rt', rs', rn', hidx]; ring
  by_cases hadj : adjacency Gs t s = true
  · -- candidate present: build the instance and vote
    have hnot : ¬ S1.mem (cell rTmp) ≤ S1.mem (cell rZero) := by rw [tmp1, r0', hadj]; simp
    have hfbx := hf3
    simp only [Cmd.FieldsFit] at hfbx
    obtain ⟨hfb, hfv⟩ := hfbx
    have hc1 : Consts S1 := hinv1.consts
    obtain ⟨S2, j2, ex2, hj2, hxl, r106, xbits, ⟨o2, fr2⟩⟩ := buildX_exec (τ := τ) (b := b) S1 hn
      (adjacency Gs) s t z B hB Gp sym wt hGp hsym hwt bits symd wtd hc1 hinv1.rn hinv1.rm
      (by rw [keep1 _ (c14 _) (by simp [cell, rIdx, rGp]) (by simp [cell, rTmp, rGp])]; exact rg)
      (by rw [keep1 _ (c14 _) (by simp [cell, rIdx, rS]) (by simp [cell, rTmp, rS])]; exact rs)
      (by rw [keep1 _ (c14 _) (by simp [cell, rIdx, rT]) (by simp [cell, rTmp, rT])]; exact rt)
      (by rw [keep1 _ (c14 _) (by simp [cell, rIdx, rB]) (by simp [cell, rTmp, rB])]; exact rb)
      (by rw [keep1 _ (c14 _) (by simp [cell, rIdx, rSym]) (by simp [cell, rTmp, rSym])]; exact rsym)
      (by rw [keep1 _ (c14 _) (by simp [cell, rIdx, rWt]) (by simp [cell, rTmp, rWt])]; exact rwt)
      hinv1.rw hinv1.fits hb3
    have w2 := toW ex2 hinv1.fits hfb hb2
    have fr2' (a : ℕ) (ha : 14 ≤ a) (hd : ∀ d ∈ buildXDirty, a ≠ cell d)
        (hout : a < xBase ∨ xBase + 128 * (n + 1) ^ 3 ≤ a) : S2.mem a = S1.mem a := fr2 a ha hd hout
    have hinv2 : HostInv n A k b S2 := by
      refine hinv1.congr (fun d hd => fr2' _ (c14 _) ?_ ?_) (fun a ha => fr2' a ?_ ?_ ?_) (ex2.post hinv1.fits)
      · intro d' hd'
        have : d ∈ invRegs → d' ∈ buildXDirty → d ≠ d' := by revert d d'; decide
        simp only [cell]; have := this hd hd'; omega
      · left; simp only [cell, xBase]
        have : d < 200 := by revert d; decide
        omega
      · simp only [VBv, xBase] at ha; omega
      · intro d' hd'
        have : d' < 200 := by revert d'; decide
        simp only [VBv, xBase, cell] at ha ⊢; omega
      · right; simp only [VBv] at ha; omega
    have rf2 : S2.mem (cell rFlag) = f := by
      rw [fr2' _ (c14 _) (by simp [buildXDirty, cell, rFlag, rXc, rK, rTmp, rSlot, rQ, rLl, rU, rV, rIdx,
        rCand, rTmp2, rWv, rTv, rHv, rMm, rAddr])
        (Or.inl (by simp [cell, rFlag, xBase])),
        keep1 _ (c14 _) (by simp [cell, rIdx, rFlag]) (by simp [cell, rTmp, rFlag])]
      exact rf
    obtain ⟨S3, w3, ex3, hw3, hinv3, rf3, o3, fr3⟩ := votes_w (τ := τ) (J := J) Q C hC S2 hinv2 hb hfv
      (candX (adjacency Gs) s t z B) r106 hxl xbits (hQ hadj) f rf2
    have exAll : WExec τ J (candCmd Q) S S3
        (Circuit.multiplicity (fun i => S.mem (cell i)) C1 * (b * (5 * b + 9) + 15) * (4 * b + 4 * J + 4) +
          (jumpCost J S1 (cell rTmp) (cell rZero) + (j2 * (4 * b + 4 * J + 4) + w3) + jumpCost J S3 0 0)) := by
      unfold candCmd; exact e1.seq (WExec.no hnot (w2.seq ex3))
    refine ⟨S3, _, exAll, ?_, hinv3, ?_, ?_, ?_⟩
    · rw [m1]
      exact cost_c n b J idx _ _ _ _ _ hidx' (Nat.mul_le_mul_right _ hj2) hw3 jc
        (jumpCost_zero_le (J := J) (hinv3.fits 0))
    · rw [rf3, if_pos hadj]
    · rw [o3, o2, o1]
    · intro a ha hd hout
      have hout' : a < xBase ∨ xBase + 128 * (n + 1) ^ 3 ≤ a := by
        rcases hout with h | h
        · exact Or.inl h
        · right; simp only [VBv] at h; omega
      rw [fr3 a ha (fun d hd' => hd d (List.mem_append_right _ hd')),
        fr2' a ha (fun d hd' => hd d (List.mem_append_left _ (List.mem_append_right _ hd'))) hout',
        keep1 a ha (hd rIdx (by simp [candDirty])) (hd rTmp (by simp [candDirty]))]
  · -- no candidate
    have hle : S1.mem (cell rTmp) ≤ S1.mem (cell rZero) := by
      rw [tmp1, r0']; simp at hadj; simp [hadj]
    have exAll : WExec τ J (candCmd Q) S S1
        (Circuit.multiplicity (fun i => S.mem (cell i)) C1 * (b * (5 * b + 9) + 15) * (4 * b + 4 * J + 4) +
          (jumpCost J S1 (cell rTmp) (cell rZero) + 0)) := by
      unfold candCmd; exact e1.seq (WExec.yes hle (WExec.skip S1))
    refine ⟨S1, _, exAll, ?_, hinv1, ?_, o1, ?_⟩
    · rw [m1]
      have := cost_c n b J idx (votesBound n A k b J C) 0 0 _ 0 hidx' (by positivity) (Nat.zero_le _) jc
        (Nat.zero_le _)
      simpa using this
    · rw [if_neg hadj, keep1 _ (c14 _) (by simp [cell, rIdx, rFlag]) (by simp [cell, rTmp, rFlag])]; exact rf
    · intro a ha hd _
      exact keep1 a ha (hd rIdx (by simp [candDirty])) (hd rTmp (by simp [candDirty]))

end DirectedHamiltonicity.Main.CycleHost


-- ===== Solutions/Dev/Asm5.lean =====


set_option autoImplicit false

namespace DirectedHamiltonicity.Main.CycleHost

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word
open TargetedSamplers.Structured.Work
open TargetedSamplers.Structured.Interp DirectedHamiltonicity.Main.CycleReduction FiniteSampling

def trialDirty : List ℕ := readSeedDirty ++ decodeDirty ++ candDirty

def trialBound (n A k b J C : ℕ) : ℕ :=
  votesBound n A k b J C + 10 ^ 9 * (n + 1) ^ 6 * (b + 1) ^ 2 * (seedWidth n + 1) * (4 * b + 4 * J + 4)

theorem trial_arith (n b J sw j1 : ℕ) (hj1 : j1 ≤ 100 * (sw + 1) + 10 * (b + 1) ^ 2) :
    (4 * b + 4 * J + 4) ≤ (n + 1) ^ 6 * (b + 1) ^ 2 * (sw + 1) * (4 * b + 4 * J + 4) ∧
    j1 * (4 * b + 4 * J + 4) ≤ 110 * ((n + 1) ^ 6 * (b + 1) ^ 2 * (sw + 1) * (4 * b + 4 * J + 4)) ∧
    (∀ j2, j2 ≤ 100 * (b + 1) ^ 2 →
      j2 * (4 * b + 4 * J + 4) ≤ 100 * ((n + 1) ^ 6 * (b + 1) ^ 2 * (sw + 1) * (4 * b + 4 * J + 4))) ∧
    (∀ V w3, w3 ≤ V + 10 ^ 8 * (n + 1) ^ 6 * (b + 1) ^ 2 * (4 * b + 4 * J + 4) →
      w3 ≤ V + 10 ^ 8 * ((n + 1) ^ 6 * (b + 1) ^ 2 * (sw + 1) * (4 * b + 4 * J + 4))) := by
  have M1 : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have B1 : 1 ≤ (b + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have MB : 1 ≤ (n + 1) ^ 6 * (b + 1) ^ 2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have K1 : sw + 1 ≤ (n + 1) ^ 6 * (b + 1) ^ 2 * (sw + 1) := by
    calc sw + 1 = 1 * (sw + 1) := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ MB
  have K2 : (b + 1) ^ 2 ≤ (n + 1) ^ 6 * (b + 1) ^ 2 * (sw + 1) := by
    calc (b + 1) ^ 2 = 1 * (b + 1) ^ 2 * 1 := by ring
      _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_right _ M1) (by omega)
  have K3 : (n + 1) ^ 6 * (b + 1) ^ 2 ≤ (n + 1) ^ 6 * (b + 1) ^ 2 * (sw + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have K0 : 1 ≤ (n + 1) ^ 6 * (b + 1) ^ 2 * (sw + 1) := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc 4 * b + 4 * J + 4 = 1 * (4 * b + 4 * J + 4) := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ K0
  · calc j1 * (4 * b + 4 * J + 4) ≤ (110 * ((n + 1) ^ 6 * (b + 1) ^ 2 * (sw + 1))) * (4 * b + 4 * J + 4) :=
          Nat.mul_le_mul_right _ (by omega)
      _ = _ := by ring
  · intro j2 hj2
    calc j2 * (4 * b + 4 * J + 4) ≤ (100 * ((n + 1) ^ 6 * (b + 1) ^ 2 * (sw + 1))) * (4 * b + 4 * J + 4) :=
          Nat.mul_le_mul_right _ (by omega)
      _ = _ := by ring
  · intro V w3 hw3
    have : 10 ^ 8 * (n + 1) ^ 6 * (b + 1) ^ 2 * (4 * b + 4 * J + 4) ≤
        10 ^ 8 * ((n + 1) ^ 6 * (b + 1) ^ 2 * (sw + 1) * (4 * b + 4 * J + 4)) := by
      calc 10 ^ 8 * (n + 1) ^ 6 * (b + 1) ^ 2 * (4 * b + 4 * J + 4) =
          10 ^ 8 * ((n + 1) ^ 6 * (b + 1) ^ 2) * (4 * b + 4 * J + 4) := by ring
        _ ≤ 10 ^ 8 * ((n + 1) ^ 6 * (b + 1) ^ 2 * (sw + 1)) * (4 * b + 4 * J + 4) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ K3)
        _ = _ := by ring
    omega

theorem trialBound_eq (n A k b J C : ℕ) : trialBound n A k b J C = votesBound n A k b J C +
    10 ^ 9 * ((n + 1) ^ 6 * (b + 1) ^ 2 * (seedWidth n + 1) * (4 * b + 4 * J + 4)) := by
  unfold trialBound; ring

theorem pathA (V P X j1X a1 : ℕ) (h1 : j1X ≤ 110 * P) (ha1 : a1 ≤ X) (hX : X ≤ P) :
    j1X + (a1 + 0) ≤ V + 10 ^ 9 * P := by omega
theorem pathB (V P X j1X j2X a1 a2 a3 a4 : ℕ) (h1 : j1X ≤ 110 * P) (h2 : j2X ≤ 100 * P)
    (ha1 : a1 ≤ X) (ha2 : a2 ≤ X) (ha3 : a3 ≤ X) (ha4 : a4 ≤ X) (hX : X ≤ P) :
    j1X + (a1 + (j2X + (a2 + (a3 + 0))) + a4) ≤ V + 10 ^ 9 * P := by omega
theorem pathC (V P X j1X j2X w3 a1 a2 a3 a4 a5 : ℕ) (h1 : j1X ≤ 110 * P) (h2 : j2X ≤ 100 * P)
    (h3 : w3 ≤ V + 10 ^ 8 * P)
    (ha1 : a1 ≤ X) (ha2 : a2 ≤ X) (ha3 : a3 ≤ X) (ha4 : a4 ≤ X) (ha5 : a5 ≤ X) (hX : X ≤ P) :
    j1X + (a1 + (j2X + (a2 + (a3 + w3 + a4))) + a5) ≤ V + 10 ^ 9 * P := by omega
theorem pathD (V P X j1X j2X w3 a1 a2 a4 a5 : ℕ) (h1 : j1X ≤ 110 * P) (h2 : j2X ≤ 100 * P)
    (h3 : w3 ≤ V + 10 ^ 8 * P)
    (ha1 : a1 ≤ X) (ha2 : a2 ≤ X) (ha4 : a4 ≤ X) (ha5 : a5 ≤ X) (hX : X ≤ P) :
    j1X + (a1 + (j2X + (a2 + w3 + a4)) + a5) ≤ V + 10 ^ 9 * P := by omega

theorem jle_X {J b x : ℕ} (h : x ≤ 3 * J + 2 * b + 1) : x ≤ 4 * b + 4 * J + 4 := by omega
theorem jle0_X {J b x : ℕ} (h : x ≤ J + 2 * b + 1) : x ≤ 4 * b + 4 * J + 4 := by omega

theorem trial_eq (Q : Program) : trial Q =
    .seq readSeed (ifLe rDc rDv .skip (.seq decodeDraw (ifEqual (cell rS) (cell rT) .skip (candCmd Q)))) := rfl

theorem trial_w {τ : Tapes} {J : ℕ} (Q : Program) (C : ℕ) (hC : ICall Q iregs C)
    {n A k b : ℕ} (QT : QueryTime Q A k) (hn : 2 ≤ n) (S : Store) (hinv : HostInv n A k b S)
    (hb : hostWidth n A k ≤ b) (hf : Cmd.FieldsFit J (trial Q))
    (Gs : Finset (Fin n × Fin n)) (Gp : ℕ) (hGp : Gp < 2 ^ (n * n))
    (bits : ∀ x y : Fin n, Gp.testBit (x.val * n + y.val) = adjacency Gs x y)
    (i : ℕ) (hi : i < trials n) (ri : S.mem (cell rI) = i) (rg : S.mem (cell rGp) = Gp)
    (f : ℕ) (rf : S.mem (cell rFlag) = f) :
    ∃ S' w, WExec τ J (trial Q) S S' w ∧ w ≤ trialBound n A k b J C ∧ HostInv n A k b S' ∧
      S'.mem (cell rFlag) = (if verifiedQuery Q (adjacency Gs) (majorityHalf n) (coinSpan A k n)
        ((panelFromTape n (coinSpan A k n) τ.coins).1 ⟨i, hi⟩)
        (panelFromTape n (coinSpan A k n) τ.coins).2 then 1 else f) ∧
      S'.out = S.out ∧ ∀ a, 14 ≤ a → (∀ d ∈ trialDirty, a ≠ cell d) → (a < xBase ∨ VBv n ≤ a) →
        S'.mem a = S.mem a := by
  classical
  have hb0 := hb
  unfold hostWidth at hb0
  have hfit := hinv.fits
  have c14 : ∀ i, 14 ≤ cell i := fun i => by unfold cell; omega
  have hb2 : 2 ≤ b := by generalize 1000 * (n + 1) ^ 3 * (k + 1) = P at hb0; omega
  have hb3 : 64 * (n + 1) ^ 3 ≤ b := by
    have : 64 * (n + 1) ^ 3 ≤ 1000 * (n + 1) ^ 3 * (k + 1) := by
      calc 64 * (n + 1) ^ 3 ≤ 1000 * (n + 1) ^ 3 := by omega
        _ ≤ 1000 * (n + 1) ^ 3 * (k + 1) := Nat.le_mul_of_pos_right _ (by omega)
    generalize 1000 * (n + 1) ^ 3 * (k + 1) = P at hb0 this; omega
  set sw := seedWidth n with hsw
  set L := coinSpan A k n with hL
  have isw : i * sw + sw ≤ trials n * sw := by
    calc i * sw + sw = (i + 1) * sw := by ring
      _ ≤ trials n * sw := Nat.mul_le_mul_right _ hi
  have hbs : (i * sw + sw).size + sw + 4 ≤ b := by
    have : (i * sw + sw).size ≤ (BIGv n A k + trials n * sw +
        (2 * majorityHalf n + 2) * (L + 2)).size := Nat.size_le_size (by omega)
    generalize 1000 * (n + 1) ^ 3 * (k + 1) = P at hb0; omega
  have hbi : (2 * i + 2).size ≤ b := by
    have : (2 * i + 2).size ≤ (2 * trials n + 2).size := Nat.size_le_size (by omega)
    generalize 1000 * (n + 1) ^ 3 * (k + 1) = P at hb0; omega
  rw [trial_eq] at hf ⊢
  simp only [ifLe, ifEqual, Cmd.FieldsFit] at hf
  obtain ⟨hfr, hd1, hd2, _, hfd, he1, he2, _, hfc1, hfc2⟩ := hf
  have hfc : Cmd.FieldsFit J (candCmd Q) := by
    unfold candCmd; simp only [ifLe, Cmd.FieldsFit]; exact ⟨hfc1, hfc2⟩
  -- read the seed block
  obtain ⟨S1, j1, ex1, hj1, rdv, o1, fr1⟩ := readSeed_exec (τ := τ) S i sw hinv.consts ri hinv.rsw
    hfit hbs hbi
  have w1 := toW ex1 hfit hfr hb2
  have fS1 := ex1.post hfit
  set D := S1.mem (cell rDv) with hDdef
  have hD : D = (binaryRank sw ((panelFromTape n L τ.coins).1 ⟨i, hi⟩)).val := by
    rw [binaryRank_val, rdv]
    apply Finset.sum_congr rfl; intro j _
    rw [panel_seed]
  have keep1 (a : ℕ) (ha : 14 ≤ a) (hd : ∀ d ∈ readSeedDirty, a ≠ cell d) : S1.mem a = S.mem a :=
    fr1 a ha hd trivial
  have hinv1 : HostInv n A k b S1 := by
    refine hinv.congr (fun d hd => keep1 _ (c14 _) ?_) (fun a ha => keep1 a ?_ ?_) fS1
    · intro d' hd'
      have : d ∈ invRegs → d' ∈ readSeedDirty → d ≠ d' := by revert d d'; decide
      simp only [cell]; have := this hd hd'; omega
    · simp only [VBv, xBase] at ha; omega
    · intro d' hd'
      have : d' < 200 := by revert d'; decide
      simp only [VBv, xBase, cell] at ha ⊢; omega
  have rdc : S1.mem (cell rDc) = drawCount n := hinv1.rdc
  have jc1 := jumpCost_le (J := J) (s := S1) (b := b) hd1 hd2 (fS1 _) (fS1 _)
  have hvq : verifiedQuery Q (adjacency Gs) (majorityHalf n) L ((panelFromTape n L τ.coins).1 ⟨i, hi⟩)
      (panelFromTape n L τ.coins).2 = (if h : D < drawCount n then
        ((candidateInput (adjacency Gs) ((rankDraw n).symm ⟨D, h⟩)).elim false
          (fun x => majority (fun tape => outputBit Q x (List.ofFn tape)) (majorityHalf n)
            (panelFromTape n L τ.coins).2)) else false) := by
    unfold verifiedQuery decodeRank
    by_cases h : D < drawCount n
    · have h' : (binaryRank sw ((panelFromTape n L τ.coins).1 ⟨i, hi⟩)).val < drawCount n := hD ▸ h
      rw [dif_pos h', dif_pos h]
      have e : ((⟨(binaryRank sw ((panelFromTape n L τ.coins).1 ⟨i, hi⟩)).val, h'⟩ : Fin (drawCount n)) =
          ⟨D, h⟩) := Fin.ext hD.symm
      rw [e]; rfl
    · rw [dif_neg (fun h' => h (hD ▸ h')), dif_neg h]; rfl
  have Xpos : 0 < 4 * b + 4 * J + 4 := by omega
  obtain ⟨FX, F1, F2, F3⟩ := trial_arith n b J sw j1 hj1
  by_cases hDc : drawCount n ≤ D
  · -- rejected draw
    have hle : S1.mem (cell rDc) ≤ S1.mem (cell rDv) := by rw [rdc]; exact hDc
    have exAll : WExec τ J (.seq readSeed (ifLe rDc rDv .skip (.seq decodeDraw (ifEqual (cell rS) (cell rT)
        .skip (candCmd Q))))) S S1 (j1 * (4 * b + 4 * J + 4) + (jumpCost J S1 (cell rDc) (cell rDv) + 0)) :=
      w1.seq (WExec.yes hle (WExec.skip S1))
    refine ⟨S1, _, exAll, ?_, hinv1, ?_, o1, ?_⟩
    · rw [trialBound_eq]; exact pathA _ _ _ _ _ F1 (jle_X jc1) FX
    · rw [hvq, dif_neg (by omega)]; simp
      rw [keep1 _ (c14 _) (by simp [readSeedDirty, cell, rFlag, rDv, rPow, rSeedPos, rJ, rAddr, rCoin])]
      exact rf
    · intro a ha hd _
      exact keep1 a ha (fun d hd' => hd d (List.mem_append_left _ (List.mem_append_left _ hd')))
  · -- accepted draw
    have hDlt : D < drawCount n := by omega
    have hnle : ¬ S1.mem (cell rDc) ≤ S1.mem (cell rDv) := by rw [rdc]; exact hDc
    set d := (rankDraw n).symm ⟨D, hDlt⟩ with hd
    obtain ⟨S2, j2, ex2, hj2, rs2, rt2, rb2, hsym, hwt, symd, wtd, o2, fr2⟩ :=
      decodeDraw_exec (τ := τ) (b := b) S1 hn D hDlt hinv1.consts hinv1.rn rfl hinv1.rin hinv1.rbm hinv1.rpw
        fS1 hb3
    have w2 := toW ex2 fS1 hfd hb2
    have fS2 := ex2.post fS1
    have keep2 (a : ℕ) (ha : 14 ≤ a) (hd' : ∀ d ∈ decodeDirty, a ≠ cell d) : S2.mem a = S1.mem a :=
      fr2 a ha hd' trivial
    have hinv2 : HostInv n A k b S2 := by
      refine hinv1.congr (fun d hd => keep2 _ (c14 _) ?_) (fun a ha => keep2 a ?_ ?_) fS2
      · intro d' hd'
        have : d ∈ invRegs → d' ∈ decodeDirty → d ≠ d' := by revert d d'; decide
        simp only [cell]; have := this hd hd'; omega
      · simp only [VBv, xBase] at ha; omega
      · intro d' hd'
        have : d' < 200 := by revert d'; decide
        simp only [VBv, xBase, cell] at ha ⊢; omega
    have jc2 := jumpCost_le (J := J) (s := S2) (b := b) he1 he2 (fS2 _) (fS2 _)
    have jc2' := jumpCost_le (J := J) (s := S2) (b := b) he2 he1 (fS2 _) (fS2 _)
    have cand_ok : candidateInput (adjacency Gs) d =
        if d.1.1 ≠ d.1.2 ∧ adjacency Gs d.1.2 d.1.1 = true then
          some (candX (adjacency Gs) d.1.1 d.1.2 d.2.1 d.2.2.val) else none := by
      by_cases hc : d.1.1 ≠ d.1.2 ∧ adjacency Gs d.1.2 d.1.1 = true
      · rw [if_pos hc]; unfold candidateInput; rw [if_pos hc]; rfl
      · rw [if_neg hc]; unfold candidateInput; rw [if_neg hc]
    have rg2 : S2.mem (cell rGp) = Gp := by
      rw [keep2 _ (c14 _) (by simp [decodeDirty, cell, rGp, rHi, rInner, rS, rT, rB, rTab, rSym, rWt]),
        keep1 _ (c14 _) (by simp [readSeedDirty, cell, rGp, rDv, rPow, rSeedPos, rJ, rAddr, rCoin])]
      exact rg
    have rf2 : S2.mem (cell rFlag) = f := by
      rw [keep2 _ (c14 _) (by simp [decodeDirty, cell, rFlag, rHi, rInner, rS, rT, rB, rTab, rSym, rWt]),
        keep1 _ (c14 _) (by simp [readSeedDirty, cell, rFlag, rDv, rPow, rSeedPos, rJ, rAddr, rCoin])]
      exact rf
    by_cases hst : d.1.1 = d.1.2
    · -- equal endpoints: skip
      have h1 : S2.mem (cell rS) ≤ S2.mem (cell rT) := by rw [rs2, rt2, hst]
      have h2 : S2.mem (cell rT) ≤ S2.mem (cell rS) := by rw [rs2, rt2, hst]
      have ex3 : WExec τ J (ifEqual (cell rS) (cell rT) .skip (candCmd Q)) S2 S2
          (jumpCost J S2 (cell rS) (cell rT) + (jumpCost J S2 (cell rT) (cell rS) + 0)) :=
        WExec.yes h1 (WExec.yes h2 (WExec.skip S2))
      have exAll : WExec τ J (.seq readSeed (ifLe rDc rDv .skip (.seq decodeDraw (ifEqual (cell rS) (cell rT)
          .skip (candCmd Q))))) S S2 (j1 * (4 * b + 4 * J + 4) + (jumpCost J S1 (cell rDc) (cell rDv) +
            (j2 * (4 * b + 4 * J + 4) + (jumpCost J S2 (cell rS) (cell rT) +
              (jumpCost J S2 (cell rT) (cell rS) + 0))) + jumpCost J S2 0 0)) :=
        w1.seq (WExec.no hnle (w2.seq ex3))
      refine ⟨S2, _, exAll, ?_, hinv2, ?_, by rw [o2, o1], ?_⟩
      · rw [trialBound_eq]
        exact pathB _ _ _ _ _ _ _ _ _ F1 (F2 _ hj2) (jle_X jc1) (jle_X jc2) (jle_X jc2')
          (jle0_X (jumpCost_zero_le (J := J) (fS2 0))) FX
      · rw [hvq, dif_pos hDlt, cand_ok, if_neg (show ¬(d.1.1 ≠ d.1.2 ∧ adjacency Gs d.1.2 d.1.1 = true) from fun h => h.1 hst)]; simp [rf2]
      · intro a ha hdd _
        rw [keep2 a ha (fun d hd' => hdd d (List.mem_append_left _ (List.mem_append_right _ hd'))),
          keep1 a ha (fun d hd' => hdd d (List.mem_append_left _ (List.mem_append_left _ hd')))]
    · -- distinct endpoints: run the candidate routine
      have hQ : adjacency Gs d.1.2 d.1.1 = true → ∀ coins : List Bool, ∃ cost,
          Q.RunsIn (runTapes (candX (adjacency Gs) d.1.1 d.1.2 d.2.1 d.2.2.val) coins) cost
            (some [outputBit Q (candX (adjacency Gs) d.1.1 d.1.2 d.2.1 d.2.2.val) coins]) ∧
            cost ≤ coinSpan A k n := fun hadj coins =>
        QT (adjacency Gs) d _ (by rw [cand_ok, if_pos ⟨hst, hadj⟩]) coins
      obtain ⟨S3, w3, ex3, hw3, hinv3, rf3, o3, fr3⟩ := cand_w (τ := τ) (J := J) Q C hC hn S2 hinv2 hb hfc
        Gs Gp hGp bits d.1.1 d.1.2 d.2.1 d.2.2.val (Nat.le_of_lt_succ d.2.2.isLt) _ _ hsym hwt symd wtd
        rg2 rs2 rt2 rb2 rfl rfl hQ f rf2
      have hflag : S3.mem (cell rFlag) = (if verifiedQuery Q (adjacency Gs) (majorityHalf n) L
          ((panelFromTape n L τ.coins).1 ⟨i, hi⟩) (panelFromTape n L τ.coins).2 then 1 else f) := by
        rw [rf3, hvq, dif_pos hDlt, cand_ok]
        by_cases hadj : adjacency Gs d.1.2 d.1.1 = true
        · rw [if_pos (show d.1.1 ≠ d.1.2 ∧ adjacency Gs d.1.2 d.1.1 = true from ⟨hst, hadj⟩), if_pos hadj]; rfl
        · rw [if_neg (show ¬(d.1.1 ≠ d.1.2 ∧ adjacency Gs d.1.2 d.1.1 = true) from fun h => hadj h.2),
            if_neg hadj]; simp
      have frA (a : ℕ) (ha : 14 ≤ a) (hdd : ∀ d ∈ trialDirty, a ≠ cell d) (hout : a < xBase ∨ VBv n ≤ a) :
          S3.mem a = S.mem a := by
        rw [fr3 a ha (fun d hd' => hdd d (List.mem_append_right _ hd')) hout,
          keep2 a ha (fun d hd' => hdd d (List.mem_append_left _ (List.mem_append_right _ hd'))),
          keep1 a ha (fun d hd' => hdd d (List.mem_append_left _ (List.mem_append_left _ hd')))]
      have hne : S2.mem (cell rS) ≠ S2.mem (cell rT) := by
        rw [rs2, rt2]; exact fun h => hst (Fin.ext h)
      by_cases hle : S2.mem (cell rS) ≤ S2.mem (cell rT)
      · have h2 : ¬ S2.mem (cell rT) ≤ S2.mem (cell rS) := by omega
        have ex4 : WExec τ J (ifEqual (cell rS) (cell rT) .skip (candCmd Q)) S2 S3
            (jumpCost J S2 (cell rS) (cell rT) + (jumpCost J S2 (cell rT) (cell rS) + w3 + jumpCost J S3 0 0)) :=
          WExec.yes hle (WExec.no h2 ex3)
        have exAll : WExec τ J (.seq readSeed (ifLe rDc rDv .skip (.seq decodeDraw (ifEqual (cell rS) (cell rT)
            .skip (candCmd Q))))) S S3 (j1 * (4 * b + 4 * J + 4) + (jumpCost J S1 (cell rDc) (cell rDv) +
              (j2 * (4 * b + 4 * J + 4) + (jumpCost J S2 (cell rS) (cell rT) +
                (jumpCost J S2 (cell rT) (cell rS) + w3 + jumpCost J S3 0 0))) + jumpCost J S3 0 0)) :=
          w1.seq (WExec.no hnle (w2.seq ex4))
        refine ⟨S3, _, exAll, ?_, hinv3, hflag, by rw [o3, o2, o1], frA⟩
        rw [trialBound_eq]
        exact pathC _ _ _ _ _ _ _ _ _ _ _ F1 (F2 _ hj2) (F3 _ _ hw3) (jle_X jc1) (jle_X jc2) (jle_X jc2')
          (jle0_X (jumpCost_zero_le (J := J) (hinv3.fits 0))) (jle0_X (jumpCost_zero_le (J := J) (hinv3.fits 0))) FX
      · have ex4 : WExec τ J (ifEqual (cell rS) (cell rT) .skip (candCmd Q)) S2 S3
            (jumpCost J S2 (cell rS) (cell rT) + w3 + jumpCost J S3 0 0) :=
          WExec.no hle ex3
        have exAll : WExec τ J (.seq readSeed (ifLe rDc rDv .skip (.seq decodeDraw (ifEqual (cell rS) (cell rT)
            .skip (candCmd Q))))) S S3 (j1 * (4 * b + 4 * J + 4) + (jumpCost J S1 (cell rDc) (cell rDv) +
              (j2 * (4 * b + 4 * J + 4) + (jumpCost J S2 (cell rS) (cell rT) + w3 + jumpCost J S3 0 0)) +
                jumpCost J S3 0 0)) :=
          w1.seq (WExec.no hnle (w2.seq ex4))
        refine ⟨S3, _, exAll, ?_, hinv3, hflag, by rw [o3, o2, o1], frA⟩
        rw [trialBound_eq]
        exact pathD _ _ _ _ _ _ _ _ _ _ F1 (F2 _ hj2) (F3 _ _ hw3) (jle_X jc1) (jle_X jc2)
          (jle0_X (jumpCost_zero_le (J := J) (hinv3.fits 0))) (jle0_X (jumpCost_zero_le (J := J) (hinv3.fits 0))) FX

end DirectedHamiltonicity.Main.CycleHost


-- ===== Solutions/Dev/Asm6.lean =====

set_option autoImplicit false

namespace DirectedHamiltonicity.Main.CycleHost

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word
open TargetedSamplers.Structured.Work
open TargetedSamplers.Structured.Interp DirectedHamiltonicity.Main.CycleReduction FiniteSampling

def decideDirty : List ℕ := rI :: trialDirty

def decideBound (n A k b J C : ℕ) : ℕ :=
  (trials n + 1) * (trialBound n A k b J C + 7 * J + 7 * b + 3) +
    2 * (b * (5 * b + 9) + 15) * (4 * b + 4 * J + 4)

theorem decide_cost (T R X w : ℕ) (hw : w ≤ T * (R + X) + X) :
    w ≤ (T + 1) * (R + X) := by
  have : (T + 1) * (R + X) = T * (R + X) + (R + X) := by ring
  omega

theorem decide_w {τ : Tapes} {J : ℕ} (Q : Program) (C : ℕ) (hC : ICall Q iregs C)
    {n A k b : ℕ} (QT : QueryTime Q A k) (hn : 2 ≤ n) (S : Store) (hinv : HostInv n A k b S)
    (hb : hostWidth n A k ≤ b) (hf : Cmd.FieldsFit J (decideCmd Q))
    (Gs : Finset (Fin n × Fin n)) (Gp : ℕ) (hGp : Gp < 2 ^ (n * n))
    (bits : ∀ x y : Fin n, Gp.testBit (x.val * n + y.val) = adjacency Gs x y)
    (rg : S.mem (cell rGp) = Gp) :
    ∃ S' w, WExec τ J (decideCmd Q) S S' w ∧ w ≤ decideBound n A k b J C ∧ HostInv n A k b S' ∧
      S'.mem (cell rFlag) = (twoSided Q (adjacency Gs)
        (panelFromTape n (coinSpan A k n) τ.coins)).toNat ∧
      S'.out = S.out ∧ ∀ a, 14 ≤ a → (∀ d ∈ decideDirty, a ≠ cell d) → (a < xBase ∨ VBv n ≤ a) →
        S'.mem a = S.mem a := by
  classical
  have hb0 := hb
  unfold hostWidth at hb0
  have hfit := hinv.fits
  have c14 : ∀ i, 14 ≤ cell i := fun i => by unfold cell; omega
  have hb2 : 2 ≤ b := by generalize 1000 * (n + 1) ^ 3 * (k + 1) = P at hb0; omega
  have htr : (trials n + 1).size ≤ b := by
    have : (trials n + 1).size ≤ (2 * trials n + 2).size := Nat.size_le_size (by omega)
    generalize 1000 * (n + 1) ^ 3 * (k + 1) = P at hb0; omega
  unfold decideCmd at hf
  simp only [Cmd.FieldsFit] at hf
  obtain ⟨hf1, hf2⟩ := hf
  set panel := panelFromTape n (coinSpan A k n) τ.coins with hpanel
  let vq (i : Fin (trials n)) : Bool := verifiedQuery Q (adjacency Gs) (majorityHalf n) (coinSpan A k n)
    (panel.1 i) panel.2
  set C0 := [asg rFlag (.literal 0), asg rI (.literal 0)] with hC0
  have w0 : Circuit.width (fun i => S.mem (cell i)) C0 ≤ b := by
    simp [hC0, Circuit.width, asg, Expression.width, Expression.eval]
  obtain ⟨S1, e1, v1, o1, f1⟩ := wcirc (τ := τ) (J := J) C0 S hfit hb2 w0 hf1
  have keep1 (a : ℕ) (ha : 14 ≤ a) (h1 : a ≠ cell rFlag) (h2 : a ≠ cell rI) : S1.mem a = S.mem a := by
    have e : a = cell (a - 14) := by simp [cell]; omega
    rw [e, v1, Circuit.result_untouched]
    simp only [hC0, asg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp only [cell, rFlag, rI] at h1 h2 ⊢; omega
  have hinv1 : HostInv n A k b S1 := by
    refine hinv.congr (fun d hd => keep1 _ (c14 _) ?_ ?_) (fun a ha => keep1 a ?_ ?_ ?_) f1
    · have : d ≠ rFlag := by revert d; decide
      simp only [cell]; omega
    · have : d ≠ rI := by revert d; decide
      simp only [cell]; omega
    · simp only [VBv, xBase] at ha; omega
    · simp only [VBv, xBase, cell, rFlag] at ha ⊢; omega
    · simp only [VBv, xBase, cell, rI] at ha ⊢; omega
  have hfb : Cmd.FieldsFit J (trial Q) := by
    have h := hf2; simp only [loop, forRange, Cmd.FieldsFit] at h; exact h.2.2.1
  let state (i : ℕ) (U : Store) : Prop :=
    HostInv n A k b U ∧ U.mem (cell rI) = i ∧ U.mem (cell rGp) = Gp ∧
      U.mem (cell rFlag) = (if ∃ i' : Fin (trials n), i'.val < i ∧ vq i' = true then 1 else 0) ∧
      U.out = S.out ∧ ∀ a, 14 ≤ a → (∀ d ∈ decideDirty, a ≠ cell d) → (a < xBase ∨ VBv n ≤ a) →
        U.mem a = S.mem a
  have start : state 0 S1 := by
    refine ⟨hinv1, ?_, ?_, ?_, o1, fun a ha hd _ => keep1 a ha (hd rFlag ?_) (hd rI (by simp [decideDirty]))⟩
    · rw [v1]; simp [hC0, Circuit.result, asg, Assignment.update, Expression.eval, Function.update, rFlag, rI]
    · rw [keep1 _ (c14 _) (by simp [cell, rGp, rFlag]) (by simp [cell, rGp, rI])]; exact rg
    · rw [v1]; simp [hC0, Circuit.result, asg, Assignment.update, Expression.eval, Function.update, rFlag, rI]
    · simp [decideDirty, trialDirty, candDirty, votesDirty]
  have body (i : ℕ) (hi : i < trials n) (U : Store) (hU : state i U) :
      ∃ U' w, WExec τ J (trial Q) U U' w ∧ w ≤ trialBound n A k b J C ∧ U'.mem (cell rI) = 0 + i ∧
        U'.mem (cell rOne) = 1 ∧ (U'.mem 0).size ≤ b ∧ state (i + 1) (U'.write (cell rI) (0 + i + 1)) := by
    obtain ⟨hiU, riU, rgU, rfU, oU, frU⟩ := hU
    obtain ⟨U', w, ex, hw, hiU', rfU', oU', frU'⟩ := trial_w (τ := τ) (J := J) Q C hC QT hn U hiU hb hfb
      Gs Gp hGp bits i hi riU rgU _ rfU
    have riU' : U'.mem (cell rI) = i := by
      rw [frU' _ (c14 _) (by simp [trialDirty, readSeedDirty, decodeDirty, candDirty, buildXDirty, votesDirty,
        runTapeDirty, cell, rI, rDv, rPow, rSeedPos, rJ, rAddr, rCoin, rHi, rInner, rS, rT, rB, rTab, rSym,
        rWt, rIdx, rTmp, rXc, rK, rSlot, rQ, rLl, rU, rV, rCand, rTmp2, rWv, rTv, rHv, rMm, rFlag, rVotes])
        (Or.inl (by simp [cell, rI, xBase]))]
      exact riU
    have rgU' : U'.mem (cell rGp) = Gp := by
      rw [frU' _ (c14 _) (by simp [trialDirty, readSeedDirty, decodeDirty, candDirty, buildXDirty, votesDirty,
        runTapeDirty, cell, rGp, rDv, rPow, rSeedPos, rJ, rAddr, rCoin, rHi, rInner, rS, rT, rB, rTab, rSym,
        rWt, rIdx, rTmp, rXc, rK, rSlot, rQ, rLl, rU, rV, rCand, rTmp2, rWv, rTv, rHv, rMm, rFlag, rVotes])
        (Or.inl (by simp [cell, rGp, xBase]))]
      exact rgU
    refine ⟨U', w, ex, hw, by rw [riU']; simp, hiU'.consts.one, hiU'.fits 0, ?_⟩
    have fitW : (U'.write (cell rI) (0 + i + 1)).Fits b :=
      Store.write_fits hiU'.fits _ ((Nat.size_le_size (by omega)).trans htr)
    have wr (a : ℕ) (ha : a ≠ cell rI) : (U'.write (cell rI) (0 + i + 1)).mem a = U'.mem a := by
      simp [Store.write, Function.update_of_ne ha]
    refine ⟨hiU'.congr (fun d hd => wr _ ?_) (fun a ha => wr a ?_) fitW, by simp [Store.write], ?_, ?_,
      by simp [Store.write, oU', oU], ?_⟩
    · have : d ≠ rI := by revert d; decide
      simp only [cell]; omega
    · simp only [VBv, xBase, cell, rI] at ha ⊢; omega
    · rw [wr _ (by simp [cell, rGp, rI])]; exact rgU'
    · rw [wr _ (by simp [cell, rFlag, rI]), rfU']
      by_cases hv : vq ⟨i, hi⟩ = true
      · have : ∃ i' : Fin (trials n), i'.val < i + 1 ∧ vq i' = true := ⟨⟨i, hi⟩, by simp, hv⟩
        simp only [vq] at hv this ⊢
        rw [if_pos hv, if_pos this]
      · simp only [vq] at hv ⊢
        rw [if_neg hv]
        have e : (∃ i' : Fin (trials n), i'.val < i + 1 ∧ vq i' = true) ↔
            (∃ i' : Fin (trials n), i'.val < i ∧ vq i' = true) := by
          constructor
          · rintro ⟨i', h1, h2⟩
            refine ⟨i', ?_, h2⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with h | h
            · exact h
            · exact absurd (show vq ⟨i, hi⟩ = true by rw [← h2]; congr 1; exact Fin.ext h.symm) hv
          · rintro ⟨i', h1, h2⟩; exact ⟨i', by omega, h2⟩
        simp only [vq] at e
        congr 1; exact propext e.symm
    · intro a ha hd hout
      rw [wr a (hd rI (by simp [decideDirty])), frU' a ha (fun d hd' => hd d (List.mem_cons_of_mem _ hd')) hout]
      exact frU a ha hd hout
  have ctrl : ∀ i ≤ trials n, ∀ U, state i U → U.mem (cell rI) = 0 + i ∧ U.mem (cell rTrials) = 0 + trials n := by
    intro i _ U hU; exact ⟨by rw [hU.2.1]; simp, by rw [hU.1.rtr]; simp⟩
  obtain ⟨S2, w2, e2, hw2, hS2⟩ := wforRange (τ := τ) (J := J) (b := b) (cell rI) (cell rTrials) (cell rOne)
    0 (trials n) (trialBound n A k b J C) (trial Q) state hf2 ctrl (by simpa using htr) body S1 start
  obtain ⟨hi2, _, _, rf2, o2, fr2⟩ := hS2
  have m0 : Circuit.multiplicity (fun i => S.mem (cell i)) C0 = 2 := by
    simp [hC0, Circuit.multiplicity, asg, Expression.multiplicity]
  refine ⟨S2, _, e1.seq e2, ?_, hi2, ?_, o2, fr2⟩
  · rw [m0]; unfold decideBound
    have e : 2 * (b * (5 * b + 9) + 15) * (4 * b + 4 * J + 4) = 2 * ((b * (5 * b + 9) + 15) * (4 * b + 4 * J + 4)) := by ring
    rw [e]
    have := decide_cost (trials n) (trialBound n A k b J C) (7 * J + 7 * b + 3) w2
      (by have : trials n * (trialBound n A k b J C + 7 * J + 7 * b + 3) =
            trials n * (trialBound n A k b J C + (7 * J + 7 * b + 3)) := by ring
          omega)
    have e2 : (trials n + 1) * (trialBound n A k b J C + (7 * J + 7 * b + 3)) =
      (trials n + 1) * (trialBound n A k b J C + 7 * J + 7 * b + 3) := by ring
    omega
  · rw [rf2]
    unfold twoSided
    by_cases hx : ∃ i' : Fin (trials n), i'.val < trials n ∧ vq i' = true
    · rw [if_pos hx]
      obtain ⟨i', _, h⟩ := hx
      rw [show (decide (∃ i, verifiedQuery Q (adjacency Gs) (majorityHalf n) (coinSpan A k n) (panel.1 i)
        panel.2 = true)) = true from decide_eq_true ⟨i', h⟩]; rfl
    · rw [if_neg hx]
      rw [show (decide (∃ i, verifiedQuery Q (adjacency Gs) (majorityHalf n) (coinSpan A k n) (panel.1 i)
        panel.2 = true)) = false from decide_eq_false (fun ⟨i', h⟩ => hx ⟨i', i'.isLt, h⟩)]; rfl

end DirectedHamiltonicity.Main.CycleHost


-- ===== Solutions/Dev/Asm7.lean =====

set_option autoImplicit false

namespace DirectedHamiltonicity.Main.CycleHost

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word
open TargetedSamplers.Structured.Work
open TargetedSamplers.Structured.Interp DirectedHamiltonicity.Main.CycleReduction FiniteSampling

def pruneDirty : List ℕ := rG :: rGp :: rTmp :: rTmp2 :: rFlag :: decideDirty

def iterBound (n A k b J C : ℕ) : ℕ :=
  decideBound n A k b J C + 100 * (n + 1) ^ 2 * (b * (5 * b + 9) + 15) * (4 * b + 4 * J + 4)

def pruneBound (n A k b J C : ℕ) : ℕ :=
  (n * n + 1) * (iterBound n A k b J C + 7 * J + 7 * b + 3) + (b * (5 * b + 9) + 15) * (4 * b + 4 * J + 4)

/-- The body of the deletion loop. -/
def pruneBody (Q : Program) : Cmd :=
  .seq (circ (bitOf rG rE))
    (ifLe rTmp rZero .skip
      (.seq (circ [asg rTmp2 (.arithmetic .pow rTwo rE), asg rGp (.sub rG rTmp2)])
        (.seq (decideCmd Q) (ifLe rFlag rZero .skip (circ [asg rG (.add rGp rZero)])))))

theorem prune_eq (Q : Program) : CycleHost.prune Q = .seq (circ [asg rE (.literal 0)]) (loop rE rN2 (pruneBody Q)) := rfl

theorem iter_cost (D Xc X e N a1 a2 a3 c1 c2 c3 w : ℕ) (he : e < N) (hX : X ≤ Xc)
    (h1 : c1 ≤ (e + 3) * Xc) (h2 : c2 ≤ (e + 2) * Xc) (h3 : c3 ≤ Xc) (hw : w ≤ D)
    (ha1 : a1 ≤ X) (ha2 : a2 ≤ X) (ha3 : a3 ≤ X) :
    c1 + (a1 + (c2 + (w + (a2 + c3 + a3))) + a3) ≤ D + 100 * (N + 1) * Xc := by
  have : (e + 3) * Xc + (e + 2) * Xc ≤ (2 * N + 5) * Xc := by
    rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ (by omega)
  have : (2 * N + 5) * Xc + 5 * Xc ≤ 100 * (N + 1) * Xc := by
    rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ (by omega)
  omega

theorem iter_cost' (D Xc X e N a1 a2 a3 c1 c2 w : ℕ) (he : e < N) (hX : X ≤ Xc)
    (h1 : c1 ≤ (e + 3) * Xc) (h2 : c2 ≤ (e + 2) * Xc) (hw : w ≤ D)
    (ha1 : a1 ≤ X) (ha2 : a2 ≤ X) (ha3 : a3 ≤ X) :
    c1 + (a1 + (c2 + (w + (a2 + 0))) + a3) ≤ D + 100 * (N + 1) * Xc := by
  have : (e + 3) * Xc + (e + 2) * Xc ≤ (2 * N + 5) * Xc := by
    rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ (by omega)
  have : (2 * N + 5) * Xc + 5 * Xc ≤ 100 * (N + 1) * Xc := by
    rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ (by omega)
  omega

theorem iter_cost0 (D Xc X e N a1 c1 : ℕ) (he : e < N) (hX : X ≤ Xc)
    (h1 : c1 ≤ (e + 3) * Xc) (ha1 : a1 ≤ X) :
    c1 + (a1 + 0) ≤ D + 100 * (N + 1) * Xc := by
  have : (e + 3) * Xc + Xc ≤ 100 * (N + 1) * Xc := by
    rw [← Nat.add_one_mul]; exact Nat.mul_le_mul_right _ (by omega)
  omega

theorem iterBound_eq (n A k b J C : ℕ) : iterBound n A k b J C = decideBound n A k b J C +
    100 * ((n + 1) ^ 2 - 1 + 1) * ((b * (5 * b + 9) + 15) * (4 * b + 4 * J + 4)) := by
  unfold iterBound
  have : (n + 1) ^ 2 - 1 + 1 = (n + 1) ^ 2 := by have := Nat.one_le_pow 2 (n + 1) (by omega); omega
  rw [this]; ring

theorem pruneBody_w {τ : Tapes} {J : ℕ} (Q : Program) (C : ℕ) (hC : ICall Q iregs C)
    {n A k b : ℕ} (QT : QueryTime Q A k) (hn : 2 ≤ n) (S : Store) (hinv : HostInv n A k b S)
    (hb : hostWidth n A k ≤ b) (hf : Cmd.FieldsFit J (pruneBody Q))
    (R : Finset (Fin n × Fin n)) (G : ℕ) (hG : G < 2 ^ (n * n))
    (bits : ∀ x y : Fin n, G.testBit (x.val * n + y.val) = decide ((x, y) ∈ R))
    (e : ℕ) (he : e < n * n) (re : S.mem (cell rE) = e) (rg : S.mem (cell rG) = G) :
    let p := (edgeOrder n)[e]'(by rw [edgeOrder_length]; exact he)
    let R' := CycleReduction.prune (fun _ G => twoSided Q (adjacency G) (panelFromTape n (coinSpan A k n) τ.coins)) R [p]
    ∃ S' w, WExec τ J (pruneBody Q) S S' w ∧ w ≤ iterBound n A k b J C ∧ HostInv n A k b S' ∧
      S'.mem (cell rG) < 2 ^ (n * n) ∧
      (∀ x y : Fin n, (S'.mem (cell rG)).testBit (x.val * n + y.val) = decide ((x, y) ∈ R')) ∧
      S'.out = S.out ∧ ∀ a, 14 ≤ a → (∀ d ∈ pruneDirty, a ≠ cell d) → (a < xBase ∨ VBv n ≤ a) →
        S'.mem a = S.mem a := by
  intro p R'
  classical
  have hb0 := hb
  unfold hostWidth at hb0
  have hfit := hinv.fits
  have c14 : ∀ i, 14 ≤ cell i := fun i => by unfold cell; omega
  have hb2 : 2 ≤ b := by generalize 1000 * (n + 1) ^ 3 * (k + 1) = P at hb0; omega
  have nn3 : n * n + 2 ≤ 1000 * (n + 1) ^ 3 * (k + 1) := by
    have h1 : n * n + 2 ≤ (n + 1) ^ 3 := by nlinarith
    have h2 : (n + 1) ^ 3 ≤ 1000 * (n + 1) ^ 3 * (k + 1) := by
      calc (n + 1) ^ 3 ≤ 1000 * (n + 1) ^ 3 := by omega
        _ ≤ _ := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hsz (y : ℕ) (hy : y < 4 * 2 ^ (n * n)) : y.size ≤ b := by
    have h4 : 4 * 2 ^ (n * n) = 2 ^ (n * n + 2) := by rw [pow_add]; ring
    have : y.size ≤ n * n + 2 := Nat.size_le.mpr (h4 ▸ hy)
    generalize 1000 * (n + 1) ^ 3 * (k + 1) = P at hb0 nn3; omega
  have hP : 16 ≤ 2 ^ (n * n) := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (n * n) := Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul hn hn)
  have heP : e < 2 ^ (n * n) := lt_trans he Nat.lt_two_pow_self
  have pv := edgeOrder_get n e (by rw [edgeOrder_length]; exact he)
  have hpe : p.1.val * n + p.2.val = e := by
    rw [pv.1, pv.2]; exact Nat.div_add_mod' e n
  have hpidx (x y : Fin n) : x.val * n + y.val = e ↔ (x, y) = p := by
    constructor
    · intro h
      have hy := y.isLt; have hx := x.isLt
      have h1 : (x.val * n + y.val) / n = x.val := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hy]; simp
      have h2 : (x.val * n + y.val) % n = y.val := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hy]
      rw [h] at h1 h2
      exact Prod.ext (Fin.ext (h1.symm.trans pv.1.symm)) (Fin.ext (h2.symm.trans pv.2.symm))
    · intro h; rw [show x = p.1 from congrArg Prod.fst h, show y = p.2 from congrArg Prod.snd h]; exact hpe
  unfold pruneBody at hf
  simp only [ifLe, Cmd.FieldsFit] at hf
  obtain ⟨hf1, hj1, hj2, _, hf2, hfd, hk1, hk2, _, hf4⟩ := hf
  -- bit test
  set C1 := bitOf rG rE with hC1
  have re' : S.mem (cell 4) = e := re
  have rg' : S.mem (cell 3) = G := rg
  have r2' : S.mem (cell 16) = 2 := hinv.consts.two
  have w1 : Circuit.width (fun i => S.mem (cell i)) C1 ≤ b := by
    simp only [hC1, bitOf, Circuit.width, asg, Expression.width, Expression.eval, Arithmetic.value,
      Assignment.update, Function.update, rTmp, rTwo, rE, rG]
    simp [re', rg', r2']
    have d1 : G / 2 ^ e ≤ G := Nat.div_le_self _ _
    have d2 : G / 2 ^ e % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have pw : 2 ^ e < 4 * 2 ^ (n * n) := by
      have := Nat.pow_lt_pow_right (show 1 < 2 by norm_num) he; omega
    exact ⟨hsz _ (by omega), hsz _ pw, hsz _ (by omega), hsz _ (by omega), hsz _ (by omega),
      hsz _ (by omega)⟩
  obtain ⟨S1, e1, v1, o1, f1⟩ := wcirc (τ := τ) (J := J) C1 S hfit hb2 w1 hf1
  have keep1 (a : ℕ) (ha : 14 ≤ a) (h1 : a ≠ cell rTmp) : S1.mem a = S.mem a := by
    have ee : a = cell (a - 14) := by simp [cell]; omega
    rw [ee, v1, Circuit.result_untouched]
    simp only [hC1, bitOf, asg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp only [cell, rTmp] at h1 ⊢; omega
  have tmp1 : S1.mem (cell rTmp) = (decide (p ∈ R)).toNat := by
    rw [v1]
    simp only [hC1, bitOf, Circuit.result, asg, Assignment.update, Expression.eval, Arithmetic.value,
      Function.update, rTmp, rTwo, rE, rG]
    simp [re', rg', r2']
    rw [div_pow_mod_two, ← hpe, bits]
  have hinv1 : HostInv n A k b S1 := by
    refine hinv.congr (fun d hd => keep1 _ (c14 _) ?_) (fun a ha => keep1 a ?_ ?_) f1
    · have : d ≠ rTmp := by revert d; decide
      simp only [cell]; omega
    · simp only [VBv, xBase] at ha; omega
    · simp only [VBv, xBase, cell, rTmp] at ha ⊢; omega
  have jc1 := jumpCost_le (J := J) (s := S1) (b := b) hj1 hj2 (f1 _) (f1 _)
  have m1 : Circuit.multiplicity (fun i => S.mem (cell i)) C1 = e + 3 := by
    simp only [hC1, bitOf, Circuit.multiplicity, asg, Assignment.update, Expression.eval, Arithmetic.value,
      Expression.multiplicity, Function.update, rTmp, rTwo, rE, rG]
    simp [re']
  have m1' : Circuit.multiplicity (fun i => S.mem (cell i)) C1 * (b * (5 * b + 9) + 15) *
      (4 * b + 4 * J + 4) ≤ (e + 3) * ((b * (5 * b + 9) + 15) * (4 * b + 4 * J + 4)) := by
    rw [m1]; ring_nf; exact le_refl _
  have Xc_ge : 4 * b + 4 * J + 4 ≤ (b * (5 * b + 9) + 15) * (4 * b + 4 * J + 4) :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hnn : e < (n + 1) ^ 2 - 1 := by
    have : n * n + 2 * n = (n + 1) ^ 2 - 1 := by
      have := Nat.one_le_pow 2 (n + 1) (by omega)
      have e2 : (n + 1) ^ 2 = n * n + 2 * n + 1 := by ring
      omega
    omega
  by_cases hpR : p ∈ R
  · -- the arc is present: try deleting it
    have hnot : ¬ S1.mem (cell rTmp) ≤ S1.mem (cell rZero) := by
      rw [tmp1, hinv1.consts.zero]; simp [hpR]
    set C2 := [asg rTmp2 (.arithmetic .pow rTwo rE), asg rGp (.sub rG rTmp2)] with hC2
    have re1 : S1.mem (cell 4) = e := by rw [keep1 _ (c14 _) (by simp [cell, rTmp])]; exact re'
    have rg1 : S1.mem (cell 3) = G := by rw [keep1 _ (c14 _) (by simp [cell, rTmp])]; exact rg'
    have r21 : S1.mem (cell 16) = 2 := hinv1.consts.two
    have w2 : Circuit.width (fun i => S1.mem (cell i)) C2 ≤ b := by
      simp only [hC2, Circuit.width, asg, Expression.width, Expression.eval, Arithmetic.value,
        Assignment.update, Function.update, rTmp2, rTwo, rE, rG, rGp]
      simp [re1, rg1, r21]
      have pw : 2 ^ e < 4 * 2 ^ (n * n) := by
        have := Nat.pow_lt_pow_right (show 1 < 2 by norm_num) he; omega
      have gs : G - 2 ^ e ≤ G := Nat.sub_le _ _
      exact ⟨hsz _ (by omega), hsz _ pw, hsz _ (by omega)⟩
    obtain ⟨S2, e2, v2, o2, f2⟩ := wcirc (τ := τ) (J := J) C2 S1 hinv1.fits hb2 w2 hf2
    have keep2 (a : ℕ) (ha : 14 ≤ a) (h1 : a ≠ cell rTmp2) (h2 : a ≠ cell rGp) : S2.mem a = S1.mem a := by
      have ee : a = cell (a - 14) := by simp [cell]; omega
      rw [ee, v2, Circuit.result_untouched]
      simp only [hC2, asg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      simp only [cell, rTmp2, rGp] at h1 h2 ⊢; omega
    have gp2 : S2.mem (cell rGp) = G - 2 ^ e := by
      rw [v2]
      simp only [hC2, Circuit.result, asg, Assignment.update, Expression.eval, Arithmetic.value,
        Function.update, rTmp2, rTwo, rE, rG, rGp]
      simp [re1, rg1, r21]
    have hinv2 : HostInv n A k b S2 := by
      refine hinv1.congr (fun d hd => keep2 _ (c14 _) ?_ ?_) (fun a ha => keep2 a ?_ ?_ ?_) f2
      · have : d ≠ rTmp2 := by revert d; decide
        simp only [cell]; omega
      · have : d ≠ rGp := by revert d; decide
        simp only [cell]; omega
      · simp only [VBv, xBase] at ha; omega
      · simp only [VBv, xBase, cell, rTmp2] at ha ⊢; omega
      · simp only [VBv, xBase, cell, rGp] at ha ⊢; omega
    have hbitG : G.testBit e = true := by rw [← hpe, bits]; simp [hpR]
    have bits2 : ∀ x y : Fin n, (G - 2 ^ e).testBit (x.val * n + y.val) = adjacency (R.erase p) x y := by
      intro x y
      rw [testBit_sub_two_pow G e _ hbitG, bits]
      simp only [adjacency, Finset.mem_erase]
      by_cases h : (x, y) = p
      · simp [h, (hpidx x y).mpr h]
      · have : x.val * n + y.val ≠ e := fun h' => h ((hpidx x y).mp h')
        simp [h, this]
    have hGp2 : G - 2 ^ e < 2 ^ (n * n) := lt_of_le_of_lt (Nat.sub_le _ _) hG
    obtain ⟨S3, w3, e3, hw3, hinv3, rf3, o3, fr3⟩ := decide_w (τ := τ) (J := J) Q C hC QT hn S2 hinv2 hb hfd
      (R.erase p) (G - 2 ^ e) hGp2 bits2 gp2
    have rg3 : S3.mem (cell rG) = G := by
      rw [fr3 _ (c14 _) (by simp [decideDirty, trialDirty, readSeedDirty, decodeDirty, candDirty,
        buildXDirty, votesDirty, runTapeDirty, cell, rG, rI, rDv, rPow, rSeedPos, rJ, rAddr, rCoin, rHi,
        rInner, rS, rT, rB, rTab, rSym, rWt, rIdx, rTmp, rXc, rK, rSlot, rQ, rLl, rU, rV, rCand, rTmp2, rWv,
        rTv, rHv, rMm, rFlag, rVotes]) (Or.inl (by simp [cell, rG, xBase])),
        keep2 _ (c14 _) (by simp [cell, rG, rTmp2]) (by simp [cell, rG, rGp]),
        keep1 _ (c14 _) (by simp [cell, rG, rTmp])]
      exact rg
    have rgp3 : S3.mem (cell rGp) = G - 2 ^ e := by
      rw [fr3 _ (c14 _) (by simp [decideDirty, trialDirty, readSeedDirty, decodeDirty, candDirty,
        buildXDirty, votesDirty, runTapeDirty, cell, rGp, rI, rDv, rPow, rSeedPos, rJ, rAddr, rCoin, rHi,
        rInner, rS, rT, rB, rTab, rSym, rWt, rIdx, rTmp, rXc, rK, rSlot, rQ, rLl, rU, rV, rCand, rTmp2, rWv,
        rTv, rHv, rMm, rFlag, rVotes]) (Or.inl (by simp [cell, rGp, xBase]))]
      exact gp2
    have jc3 := jumpCost_le (J := J) (s := S3) (b := b) hk1 hk2 (hinv3.fits _) (hinv3.fits _)
    have m2 : Circuit.multiplicity (fun i => S1.mem (cell i)) C2 = e + 2 := by
      simp only [hC2, Circuit.multiplicity, asg, Assignment.update, Expression.eval, Arithmetic.value,
        Expression.multiplicity, Function.update, rTmp2, rTwo, rE, rG, rGp]
      simp [re1]
    have m2' : Circuit.multiplicity (fun i => S1.mem (cell i)) C2 * (b * (5 * b + 9) + 15) *
        (4 * b + 4 * J + 4) ≤ (e + 2) * ((b * (5 * b + 9) + 15) * (4 * b + 4 * J + 4)) := by
      rw [m2]; ring_nf; exact le_refl _
    have hR' : R' = if twoSided Q (adjacency (R.erase p)) (panelFromTape n (coinSpan A k n) τ.coins)
        then R.erase p else R := prune_single _ _ _
    have frA (U : Store) (hU : ∀ a, 14 ≤ a → (∀ d ∈ decideDirty, a ≠ cell d) → (a < xBase ∨ VBv n ≤ a) →
        U.mem a = S2.mem a) (a : ℕ) (ha : 14 ≤ a) (hd : ∀ d ∈ pruneDirty, a ≠ cell d)
        (hout : a < xBase ∨ VBv n ≤ a) : U.mem a = S.mem a := by
      rw [hU a ha (fun d hd' => hd d (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hd')))))) hout,
        keep2 a ha (hd rTmp2 (by simp [pruneDirty])) (hd rGp (by simp [pruneDirty])),
        keep1 a ha (hd rTmp (by simp [pruneDirty]))]
    by_cases hts : twoSided Q (adjacency (R.erase p)) (panelFromTape n (coinSpan A k n) τ.coins) = true
    · -- deletion accepted
      have hn3 : ¬ S3.mem (cell rFlag) ≤ S3.mem (cell rZero) := by
        rw [rf3, hinv3.consts.zero, hts]; simp
      set C3 := [asg rG (.add rGp rZero)] with hC3
      have w3c : Circuit.width (fun i => S3.mem (cell i)) C3 ≤ b := by
        have a1 : S3.mem (cell 6) = G - 2 ^ e := rgp3
        have a2 : S3.mem (cell 15) = 0 := hinv3.consts.zero
        simp only [hC3, Circuit.width, asg, Expression.width, Expression.eval, rG, rGp, rZero, a1, a2]
        simp
        exact hsz _ (by omega)
      obtain ⟨S4, e4, v4, o4, f4⟩ := wcirc (τ := τ) (J := J) C3 S3 hinv3.fits hb2 w3c hf4
      have keep4 (a : ℕ) (ha : 14 ≤ a) (h1 : a ≠ cell rG) : S4.mem a = S3.mem a := by
        have ee : a = cell (a - 14) := by simp [cell]; omega
        rw [ee, v4, Circuit.result_untouched]
        simp only [hC3, asg, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
        simp only [cell, rG] at h1 ⊢; omega
      have rg4 : S4.mem (cell rG) = G - 2 ^ e := by
        have a1 : S3.mem (cell 6) = G - 2 ^ e := rgp3
        have a2 : S3.mem (cell 15) = 0 := hinv3.consts.zero
        rw [v4]; simp [hC3, Circuit.result, asg, Assignment.update, Expression.eval, Function.update, rG, rGp,
          rZero, a1, a2]
      have exAll : WExec τ J (pruneBody Q) S S4
          (Circuit.multiplicity (fun i => S.mem (cell i)) C1 * (b * (5 * b + 9) + 15) * (4 * b + 4 * J + 4) +
            (jumpCost J S1 (cell rTmp) (cell rZero) +
              (Circuit.multiplicity (fun i => S1.mem (cell i)) C2 * (b * (5 * b + 9) + 15) * (4 * b + 4 * J + 4) +
                (w3 + (jumpCost J S3 (cell rFlag) (cell rZero) +
                  Circuit.multiplicity (fun i => S3.mem (cell i)) C3 * (b * (5 * b + 9) + 15) * (4 * b + 4 * J + 4) +
                  jumpCost J S4 0 0))) + jumpCost J S4 0 0)) := by
        unfold pruneBody; exact e1.seq (WExec.no hnot (e2.seq (e3.seq (WExec.no hn3 e4))))
      have m3 : Circuit.multiplicity (fun i => S3.mem (cell i)) C3 = 1 := by
        simp [hC3, Circuit.multiplicity, asg, Expression.multiplicity]
      refine ⟨S4, _, exAll, ?_, ?_, ?_, ?_, by rw [o4, o3, o2, o1], ?_⟩
      · rw [iterBound_eq]
        refine iter_cost _ _ (4 * b + 4 * J + 4) e _ _ _ _ _ _ _ _ hnn Xc_ge m1' m2' ?_ hw3 (jle_X jc1) (jle_X jc3)
          (jle0_X (jumpCost_zero_le (J := J) (f4 0)))
        rw [m3]; simp
      · refine hinv3.congr (fun d hd => keep4 _ (c14 _) ?_) (fun a ha => keep4 a ?_ ?_) f4
        · have : d ≠ rG := by revert d; decide
          simp only [cell]; omega
        · simp only [VBv, xBase] at ha; omega
        · simp only [VBv, xBase, cell, rG] at ha ⊢; omega
      · rw [rg4]; exact hGp2
      · intro x y; rw [rg4, bits2, hR', if_pos hts]; rfl
      · intro a ha hd hout
        rw [keep4 a ha (hd rG (by simp [pruneDirty]))]
        exact frA S3 fr3 a ha hd hout
    · -- deletion rejected
      have hts' : twoSided Q (adjacency (R.erase p)) (panelFromTape n (coinSpan A k n) τ.coins) = false := by
        simpa using hts
      have hl3 : S3.mem (cell rFlag) ≤ S3.mem (cell rZero) := by rw [rf3, hinv3.consts.zero, hts']; simp
      have exAll : WExec τ J (pruneBody Q) S S3
          (Circuit.multiplicity (fun i => S.mem (cell i)) C1 * (b * (5 * b + 9) + 15) * (4 * b + 4 * J + 4) +
            (jumpCost J S1 (cell rTmp) (cell rZero) +
              (Circuit.multiplicity (fun i => S1.mem (cell i)) C2 * (b * (5 * b + 9) + 15) * (4 * b + 4 * J + 4) +
                (w3 + (jumpCost J S3 (cell rFlag) (cell rZero) + 0))) + jumpCost J S3 0 0)) := by
        unfold pruneBody; exact e1.seq (WExec.no hnot (e2.seq (e3.seq (WExec.yes hl3 (WExec.skip S3)))))
      refine ⟨S3, _, exAll, ?_, hinv3, ?_, ?_, by rw [o3, o2, o1], frA S3 fr3⟩
      · rw [iterBound_eq]
        exact iter_cost' _ _ (4 * b + 4 * J + 4) e _ _ _ _ _ _ _ hnn Xc_ge m1' m2' hw3 (jle_X jc1) (jle_X jc3)
          (jle0_X (jumpCost_zero_le (J := J) (hinv3.fits 0)))
      · rw [rg3]; exact hG
      · intro x y; rw [rg3, bits, hR', if_neg (by simpa using hts)]
  · -- the arc is absent: nothing to do
    have hle : S1.mem (cell rTmp) ≤ S1.mem (cell rZero) := by
      rw [tmp1, hinv1.consts.zero]; simp [hpR]
    have exAll : WExec τ J (pruneBody Q) S S1
        (Circuit.multiplicity (fun i => S.mem (cell i)) C1 * (b * (5 * b + 9) + 15) * (4 * b + 4 * J + 4) +
          (jumpCost J S1 (cell rTmp) (cell rZero) + 0)) := by
      unfold pruneBody; exact e1.seq (WExec.yes hle (WExec.skip S1))
    have hR' : R' = R := by
      show CycleReduction.prune _ R [p] = R
      rw [prune_single, Finset.erase_eq_of_notMem hpR]; simp
    have rg1' : S1.mem (cell rG) = G := by rw [keep1 _ (c14 _) (by simp [cell, rG, rTmp])]; exact rg
    refine ⟨S1, _, exAll, ?_, hinv1, by rw [rg1']; exact hG, ?_, o1, ?_⟩
    · rw [iterBound_eq]; exact iter_cost0 _ _ _ e _ _ _ hnn Xc_ge m1' (jle_X jc1)
    · intro x y; rw [rg1', bits, hR']
    · intro a ha hd _
      exact keep1 a ha (hd rTmp (by simp [pruneDirty]))

end DirectedHamiltonicity.Main.CycleHost


-- ===== Solutions/Dev/Asm8.lean =====

set_option autoImplicit false

namespace DirectedHamiltonicity.Main.CycleHost

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word
open TargetedSamplers.Structured.Work
open TargetedSamplers.Structured.Interp DirectedHamiltonicity.Main.CycleReduction FiniteSampling

theorem prune_w {τ : Tapes} {J : ℕ} (Q : Program) (C : ℕ) (hC : ICall Q iregs C)
    {n A k b : ℕ} (QT : QueryTime Q A k) (hn : 2 ≤ n) (S : Store) (hinv : HostInv n A k b S)
    (hb : hostWidth n A k ≤ b) (hf : Cmd.FieldsFit J (CycleHost.prune Q))
    (adj : Fin n → Fin n → Bool) (rg : S.mem (cell rG) < 2 ^ (n * n))
    (bits : ∀ x y : Fin n, (S.mem (cell rG)).testBit (x.val * n + y.val) = adj x y) :
    ∃ S' w, WExec τ J (CycleHost.prune Q) S S' w ∧ w ≤ pruneBound n A k b J C ∧ HostInv n A k b S' ∧
      S'.mem (cell rG) < 2 ^ (n * n) ∧
      (∀ x y : Fin n, (S'.mem (cell rG)).testBit (x.val * n + y.val) =
        decide ((x, y) ∈ remaining Q adj (panelFromTape n (coinSpan A k n) τ.coins))) ∧
      S'.out = S.out := by
  classical
  have hb0 := hb
  unfold hostWidth at hb0
  have hfit := hinv.fits
  have c14 : ∀ i, 14 ≤ cell i := fun i => by unfold cell; omega
  have hb2 : 2 ≤ b := by generalize 1000 * (n + 1) ^ 3 * (k + 1) = P at hb0; omega
  have nn3 : n * n + 1 ≤ 1000 * (n + 1) ^ 3 * (k + 1) := by
    have h1 : n * n + 1 ≤ (n + 1) ^ 3 := by nlinarith
    have h2 : (n + 1) ^ 3 ≤ 1000 * (n + 1) ^ 3 * (k + 1) := by
      calc (n + 1) ^ 3 ≤ 1000 * (n + 1) ^ 3 := by omega
        _ ≤ _ := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hwid : (n * n + 1).size ≤ b := by
    have : (n * n + 1).size ≤ n * n + 1 := Nat.size_le.mpr Nat.lt_two_pow_self
    generalize 1000 * (n + 1) ^ 3 * (k + 1) = P at hb0 nn3; omega
  rw [prune_eq] at hf ⊢
  simp only [Cmd.FieldsFit] at hf
  obtain ⟨hf1, hf2⟩ := hf
  set panel := panelFromTape n (coinSpan A k n) τ.coins with hpanel
  set ask : Fin n × Fin n → Finset (Fin n × Fin n) → Bool := fun _ G => twoSided Q (adjacency G) panel
    with hask
  set C0 := [asg rE (.literal 0)] with hC0
  have w0 : Circuit.width (fun i => S.mem (cell i)) C0 ≤ b := by
    simp [hC0, Circuit.width, asg, Expression.width, Expression.eval]
  obtain ⟨S1, e1, v1, o1, f1⟩ := wcirc (τ := τ) (J := J) C0 S hfit hb2 w0 hf1
  have keep1 (a : ℕ) (ha : 14 ≤ a) (h1 : a ≠ cell rE) : S1.mem a = S.mem a := by
    have e : a = cell (a - 14) := by simp [cell]; omega
    rw [e, v1, Circuit.result_untouched]
    simp only [hC0, asg, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
    simp only [cell, rE] at h1 ⊢; omega
  have hinv1 : HostInv n A k b S1 := by
    refine hinv.congr (fun d hd => keep1 _ (c14 _) ?_) (fun a ha => keep1 a ?_ ?_) f1
    · have : d ≠ rE := by revert d; decide
      simp only [cell]; omega
    · simp only [VBv, xBase] at ha; omega
    · simp only [VBv, xBase, cell, rE] at ha ⊢; omega
  have hfb : Cmd.FieldsFit J (pruneBody Q) := by
    have h := hf2; simp only [loop, forRange, Cmd.FieldsFit] at h; exact h.2.2.1
  let state (e : ℕ) (U : Store) : Prop :=
    HostInv n A k b U ∧ U.mem (cell rE) = e ∧ U.mem (cell rG) < 2 ^ (n * n) ∧
      (∀ x y : Fin n, (U.mem (cell rG)).testBit (x.val * n + y.val) =
        decide ((x, y) ∈ CycleReduction.prune ask (edges adj) ((edgeOrder n).take e))) ∧ U.out = S.out
  have start : state 0 S1 := by
    refine ⟨hinv1, ?_, ?_, ?_, o1⟩
    · rw [v1]; simp [hC0, Circuit.result, asg, Assignment.update, Expression.eval, Function.update, rE]
    · rw [keep1 _ (c14 _) (by simp [cell, rG, rE])]; exact rg
    · intro x y
      rw [keep1 _ (c14 _) (by simp [cell, rG, rE]), bits]
      simp [CycleReduction.prune, edges]
  have body (e : ℕ) (he : e < n * n) (U : Store) (hU : state e U) :
      ∃ U' w, WExec τ J (pruneBody Q) U U' w ∧ w ≤ iterBound n A k b J C ∧ U'.mem (cell rE) = 0 + e ∧
        U'.mem (cell rOne) = 1 ∧ (U'.mem 0).size ≤ b ∧ state (e + 1) (U'.write (cell rE) (0 + e + 1)) := by
    obtain ⟨hiU, reU, rgU, bitsU, oU⟩ := hU
    obtain ⟨U', w, ex, hw, hiU', rgU', bitsU', oU', frU'⟩ := pruneBody_w (τ := τ) (J := J) Q C hC QT hn U hiU
      hb hfb _ _ rgU bitsU e he reU rfl
    have reU' : U'.mem (cell rE) = e := by
      have hd : ∀ d ∈ pruneDirty, cell rE ≠ cell d := by
        intro d hd'
        have : d ≠ rE := by revert d; decide
        simp only [cell]; omega
      rw [frU' _ (c14 _) hd (Or.inl (by simp [cell, rE, xBase]))]
      exact reU
    refine ⟨U', w, ex, hw, by rw [reU']; simp, hiU'.consts.one, hiU'.fits 0, ?_⟩
    have fitW : (U'.write (cell rE) (0 + e + 1)).Fits b :=
      Store.write_fits hiU'.fits _ ((Nat.size_le_size (by omega)).trans hwid)
    have wr (a : ℕ) (ha : a ≠ cell rE) : (U'.write (cell rE) (0 + e + 1)).mem a = U'.mem a := by
      simp [Store.write, Function.update_of_ne ha]
    have hgE : cell rG ≠ cell rE := by simp [cell, rG, rE]
    refine ⟨hiU'.congr (fun d hd => wr _ ?_) (fun a ha => wr a ?_) fitW, by simp [Store.write], ?_, ?_,
      by simp [Store.write, oU', oU]⟩
    · have : d ≠ rE := by revert d; decide
      simp only [cell]; omega
    · simp only [VBv, xBase, cell, rE] at ha ⊢; omega
    · rw [wr _ hgE]; exact rgU'
    · intro x y
      rw [wr _ hgE, bitsU']
      have ht : (edgeOrder n).take (e + 1) = (edgeOrder n).take e ++ [(edgeOrder n)[e]'(by
          rw [edgeOrder_length]; exact he)] := by
        rw [List.take_succ, List.getElem?_eq_getElem]; rfl
      rw [ht, prune_append]
  have ctrl : ∀ e ≤ n * n, ∀ U, state e U → U.mem (cell rE) = 0 + e ∧ U.mem (cell rN2) = 0 + n * n := by
    intro e _ U hU; exact ⟨by rw [hU.2.1]; simp, by rw [hU.1.rn2]; simp⟩
  obtain ⟨S2, w2, e2, hw2, hS2⟩ := wforRange (τ := τ) (J := J) (b := b) (cell rE) (cell rN2) (cell rOne)
    0 (n * n) (iterBound n A k b J C) (pruneBody Q) state hf2 ctrl (by simpa using hwid) body S1 start
  obtain ⟨hi2, _, rg2, bits2, o2⟩ := hS2
  have m0 : Circuit.multiplicity (fun i => S.mem (cell i)) C0 = 1 := by
    simp [hC0, Circuit.multiplicity, asg, Expression.multiplicity]
  refine ⟨S2, _, e1.seq e2, ?_, hi2, rg2, ?_, o2⟩
  · rw [m0]; unfold pruneBound
    have e3 : (n * n + 1) * (iterBound n A k b J C + 7 * J + 7 * b + 3) =
      n * n * (iterBound n A k b J C + 7 * J + 7 * b + 3) + (iterBound n A k b J C + 7 * J + 7 * b + 3) := by ring
    rw [e3, one_mul]
    generalize n * n * (iterBound n A k b J C + 7 * J + 7 * b + 3) = Y at hw2 ⊢
    omega
  · intro x y
    rw [bits2]
    have : (edgeOrder n).take (n * n) = edgeOrder n := by
      rw [List.take_of_length_le (by rw [edgeOrder_length])]
    rw [this]; rfl

end DirectedHamiltonicity.Main.CycleHost


-- ===== Solutions/Dev/Asm9.lean =====

set_option autoImplicit false

namespace DirectedHamiltonicity.Main.CycleHost

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word
open TargetedSamplers.Structured.Work TargetedSamplers.Structured.BinaryRead
open TargetedSamplers.Structured.Interp DirectedHamiltonicity.Main.CycleReduction FiniteSampling

def mainBound (n A k J C : ℕ) : ℕ :=
  let b := hostWidth n A k
  pruneBound n A k b J C + (20 * (b * (5 * b + 9) + 15) + 10 * (b + 1) +
    10 ^ 4 * (n + 1) ^ 2 * (k + 1) * (b + 1) ^ 2 + 100 * (n + 1) ^ 2 +
    10 ^ 6 * (n + 1) ^ 4 * (b + 1) ^ 2 + 10) * (4 * b + 4 * J + 4)

def C0main (A k : ℕ) : List Assignment :=
  [asg rOne (.literal 1), asg rZero (.literal 0), asg rTwo (.literal 2),
      asg rThree (.literal 3), asg rSix (.literal 6), asg rSeven (.literal 7),
      asg rFifty (.literal 50), asg rC49 (.literal 49), asg rA (.literal A), asg rKk (.literal k),
      asg 50 (.literal 0)]

def C1main : List Assignment := [asg rN (.add 51 rZero), asg rCur (.add 50 rZero)]

def smallCmd : Cmd := ifLe rN rZero (.op (.output (cell rZero)))
      (.seq (.op (.input (cell rCoin) (cell rCur))) (.op (.output (cell rCoin))))

def bigCmd (Q : Program) : Cmd := .seq params (.seq readGraph (.seq (CycleHost.prune Q) certify))

theorem main_eq (Q : Program) (A k : ℕ) : main Q A k =
    .seq (circ (C0main A k)) (.seq (readField readRegs) (.seq (circ C1main) (ifLe rN rOne smallCmd (bigCmd Q)))) :=
  rfl

theorem logv_ge (n a : ℕ) (h : LOGv n ≤ a) : cell 120 ≤ a := by
  simp only [LOGv, VBv, xBase, cell] at h ⊢; omega

theorem vbv_ge (n i : ℕ) : cell 120 ≤ VBv n + i := by
  simp only [VBv, xBase, cell]; omega

theorem inv_rg_disj : ∀ d ∈ invRegs, ∀ d' ∈ readGraphDirty, d ≠ d' := by decide
theorem rg_small : ∀ d ∈ readGraphDirty, d < 200 := by decide
theorem vbv_le (n a : ℕ) (h : VBv n ≤ a) : cell 0 ≤ a := by simp only [VBv, xBase, cell] at h ⊢; omega
theorem vbv_ne (n a : ℕ) (h : VBv n ≤ a) (d : ℕ) (hd : d < 200) : a ≠ cell d := by
  simp only [VBv, xBase, cell] at h ⊢; omega

theorem params_ne (a : ℕ) (ha : cell 112 ≤ a) : ∀ d ∈ paramsDirty, a ≠ cell d := by
  intro d hd
  have : d < 112 := by revert d; decide
  simp only [cell] at ha ⊢; omega

theorem logv_ge' (n a : ℕ) (h : LOGv n ≤ a) : cell 112 ≤ a := by
  simp only [LOGv, VBv, xBase, cell] at h ⊢; omega

theorem vbv_ge' (n i : ℕ) : cell 112 ≤ VBv n + i := by
  simp only [VBv, xBase, cell]; omega

theorem vb_size (n A k : ℕ) : (VBv n + n).size + 2 ≤ hostWidth n A k := by
  unfold hostWidth
  have h1 : (VBv n + n).size ≤ VBv n + n := Nat.size_le.mpr Nat.lt_two_pow_self
  have h2 : VBv n + n + 2 ≤ 1000 * (n + 1) ^ 3 * (k + 1) := by
    have : 1 ≤ (n + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
    have : n + 1 ≤ (n + 1) ^ 3 := by
      calc n + 1 = (n + 1) ^ 1 := by ring
        _ ≤ (n + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    have h3 : 1000 * (n + 1) ^ 3 ≤ 1000 * (n + 1) ^ 3 * (k + 1) := Nat.le_mul_of_pos_right _ (by omega)
    simp only [VBv, xBase]; omega
  generalize 1000 * (n + 1) ^ 3 * (k + 1) = P at h2 ⊢
  omega

def bigBound (n A k J C : ℕ) : ℕ :=
  let b := hostWidth n A k
  pruneBound n A k b J C + (10 ^ 4 * (n + 1) ^ 2 * (k + 1) * (b + 1) ^ 2 + 100 * (n + 1) ^ 2 +
    10 ^ 6 * (n + 1) ^ 4 * (b + 1) ^ 2) * (4 * b + 4 * J + 4)

theorem big_cost (P X a1 a2 a3 c4 c5 w6 c7 : ℕ) (_hX : True) (h4 : c4 ≤ a1 * X) (h5 : c5 ≤ a2 * X) (h6 : w6 ≤ P)
    (h7 : c7 ≤ a3 * X) : c4 + (c5 + (w6 + c7)) ≤ P + (a1 + a2 + a3) * X := by
  have : (a1 + a2 + a3) * X = a1 * X + a2 * X + a3 * X := by ring
  omega

theorem big_w (Q : Program) (C : ℕ) (hC : ICall Q iregs C) (A k : ℕ) (QT : QueryTime Q A k)
    (n : ℕ) (hn2 : 2 ≤ n) (adj : Fin n → Fin n → Bool) (coins : List Bool) (J : ℕ)
    (hfb : Cmd.FieldsFit J (bigCmd Q)) (S3 : Store) (c3 : Consts S3) (s3n : S3.mem (cell rN) = n)
    (s3A : S3.mem (cell rA) = A) (s3k : S3.mem (cell rKk) = k) (s3cur : S3.mem (cell rCur) = 2 * n.size + 1)
    (f3 : S3.Fits (hostWidth n A k)) (o3 : S3.out = []) (hz : ∀ a, cell 112 ≤ a → S3.mem a = 0) :
    ∃ t K, WExec (runTapes (encodeDigraph n adj) coins) J (bigCmd Q) S3 t K ∧
      t.out = [CycleReduction.certify n (remaining Q adj (panelFromTape n (coinSpan A k n) coins))] ∧
      K ≤ bigBound n A k J C ∧ t.Fits (hostWidth n A k) := by
  classical
  set τ := runTapes (encodeDigraph n adj) coins with hτ
  set b := hostWidth n A k with hbdef
  have hb0 : (BIGv n A k + trials n * seedWidth n + (2 * majorityHalf n + 2) * (coinSpan A k n + 2)).size +
      1000 * (n + 1) ^ 3 * (k + 1) + 2 * A.size + 4 * seedWidth n + 64 + (2 * trials n + 2).size ≤ b := le_rfl
  have c14 : ∀ i, 14 ≤ cell i := fun i => by unfold cell; omega
  have h64 : 64 * (n + 1) ^ 3 ≤ 1000 * (n + 1) ^ 3 * (k + 1) := by
    calc 64 * (n + 1) ^ 3 ≤ 1000 * (n + 1) ^ 3 := by omega
      _ ≤ _ := Nat.le_mul_of_pos_right _ (by omega)
  have hb2 : 2 ≤ b := by generalize 1000 * (n + 1) ^ 3 * (k + 1) = P at hb0; omega
  have hb3 : 64 * (n + 1) ^ 3 ≤ b := by generalize 1000 * (n + 1) ^ 3 * (k + 1) = P at hb0 h64; omega
  have hbp : 1000 * (n + 1) ^ 3 * (k + 1) + 2 * A.size ≤ b := by
    generalize 1000 * (n + 1) ^ 3 * (k + 1) = P at hb0 ⊢; omega
  simp only [bigCmd, Cmd.FieldsFit] at hfb
  obtain ⟨hp, hrg, hpr, hce⟩ := hfb
  obtain ⟨S4, j4, ex4, hj4, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17,
    p18, p19, ⟨o4, fr4⟩⟩ := params_exec (τ := τ) (b := b) S3 hn2 A k c3 s3n s3A s3k f3 hbp
  have w4 := toW ex4 f3 hp hb2
  have fS4 := ex4.post f3
  have zbig (a : ℕ) (ha : cell 112 ≤ a) : S4.mem a = 0 := by
    rw [fr4 a (le_trans (c14 _) ha) (fun d hd => params_ne a ha d hd) trivial]; exact hz a ha
  have c4 : Consts S4 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      first
      | (rw [fr4 _ (c14 _) (by simp [paramsDirty, cell, rOne, rZero, rTwo, rThree, rSix, rSeven, rFifty, rC49,
          rN2, rM, rTmp, rW, rBm1, rTmp2, rPW, rP50, rIn, rDc, rP49, rCeil50, rTb, rOb, rTrials, rP15, rP8,
          rCeil15, rBase, rL, rSw, rR, rR2, rTapeBase, rXmax, rVB]) trivial])
    · exact c3.one
    · exact c3.zero
    · exact c3.two
    · exact c3.three
    · exact c3.six
    · exact c3.seven
    · exact c3.fifty
    · exact c3.c49
  have rn4 : S4.mem (cell rN) = n := by
    rw [fr4 _ (c14 _) (by simp [paramsDirty, cell, rN, rTmp, rW, rBm1, rTmp2, rPW, rP50, rIn, rDc, rP49,
      rCeil50, rTb, rOb, rTrials, rP15, rP8, rCeil15, rBase, rL, rSw, rR, rR2, rTapeBase, rXmax, rVB, rN2, rM])
      trivial]; exact s3n
  have rcur4 : S4.mem (cell rCur) = 2 * n.size + 1 := by
    rw [fr4 _ (c14 _) (by simp [paramsDirty, cell, rCur, rTmp, rW, rBm1, rTmp2, rPW, rP50, rIn, rDc, rP49,
      rCeil50, rTb, rOb, rTrials, rP15, rP8, rCeil15, rBase, rL, rSw, rR, rR2, rTapeBase, rXmax, rVB, rN2, rM])
      trivial]; exact s3cur
  have hinv4 : HostInv n A k b S4 := {
    consts := c4, rn := rn4, rn2 := p1, rm := p2, rw := p3, rbm := p4, rpw := p5, rin := p6, rdc := p7,
    rtr := p8, rsw := p9, rl := p10, rr := p11, rr2 := p12, rtb := p13, rvb := p14, rlog := p15, rbig := p16,
    rxb := p17, rone' := p18, rzero' := p19,
    rds := zbig _ (by simp [cell]), t1 := zbig _ (by simp [cell]), t2 := zbig _ (by simp [cell]),
    t3 := zbig _ (by simp [cell]), t4 := zbig _ (by simp [cell]), t5 := zbig _ (by simp [cell]),
    t6 := zbig _ (by simp [cell]),
    high := fun a ha => zbig a (logv_ge' n a ha),
    vis := fun i _ => zbig _ (vbv_ge' n i),
    fits := fS4 }
  obtain ⟨S5, j5, ex5, hj5, rg5, bits5, ⟨o5, fr5⟩⟩ := readGraph_exec (τ := τ) (b := b) S4 adj rfl c4 rn4 p1
    rcur4 fS4 hb3
  have w5 := toW ex5 fS4 hrg hb2
  have hinv5 : HostInv n A k b S5 :=
    hinv4.congr (fun d hd => fr5 _ (c14 _) (fun d' hd' => by have := inv_rg_disj d hd d' hd'; simp only [cell]; omega)
      trivial) (fun a ha => fr5 a (le_trans (by simp [cell]) (vbv_le n a ha))
        (fun d' hd' => vbv_ne n a ha d' (rg_small d' hd')) trivial) (ex5.post fS4)
  obtain ⟨S6, w6, ex6, hw6, hinv6, rg6, bits6, o6⟩ := prune_w (τ := τ) (J := J) Q C hC QT hn2 S5 hinv5 le_rfl
    hpr adj rg5 bits5
  obtain ⟨S7, j7, ex7, hj7, o7, _⟩ := certify_exec (τ := τ) (b := b) S6 hn2 _ _ (VBv n) rg6 bits6
    hinv6.consts hinv6.rn rfl hinv6.rvb (by simp [cell, VBv, xBase]; omega) hinv6.vis hinv6.fits hb3 (vb_size n A k)
  have w7 := toW ex7 hinv6.fits hce hb2
  refine ⟨S7, _, w4.seq (w5.seq (ex6.seq w7)), ?_, ?_, ex7.post hinv6.fits⟩
  · rw [o7, o6, o5, o4, o3]; rfl
  · unfold bigBound
    exact big_cost _ _ _ _ _ _ _ _ _ trivial (Nat.mul_le_mul_right _ hj4) (Nat.mul_le_mul_right _ hj5) hw6
      (Nat.mul_le_mul_right _ hj7)


theorem c0_ne (a : ℕ) (ha : cell 112 ≤ a) :
    ∀ d ∈ [rOne, rZero, rTwo, rThree, rSix, rSeven, rFifty, rC49, rA, rKk, 50], a ≠ cell d := by
  intro d hd
  have : d < 112 := by revert d; decide
  simp only [cell] at ha ⊢; omega

theorem jle_X' {J b x : ℕ} (_h : 2 ≤ b) (h : x ≤ 3 * J + 2 * b + 1) : x ≤ 4 * b + 4 * J + 4 := by omega

theorem main_cost_big (P Xb X b j2X jc K jc0 m4 m5 m6 : ℕ)
    (hK : K ≤ P + (m4 + m5 + m6) * X) (hj2 : j2X ≤ 10 * (b + 1) * X) (hjc : jc ≤ X) (hjc0 : jc0 ≤ X)
    (hX : X ≤ Xb * X) :
    11 * Xb * X + (j2X + (2 * Xb * X + (jc + K + jc0))) ≤
      P + (20 * Xb + 10 * (b + 1) + m4 + m5 + m6 + 10) * X := by
  have e : (20 * Xb + 10 * (b + 1) + m4 + m5 + m6 + 10) * X =
    20 * (Xb * X) + 10 * (b + 1) * X + (m4 + m5 + m6) * X + 10 * X := by ring
  have e1 : 11 * Xb * X = 11 * (Xb * X) := by ring
  have e2 : 2 * Xb * X = 2 * (Xb * X) := by ring
  rw [e, e1, e2]; omega

theorem main_cost_small0 (P Xb X b j2X jc jz co m4 m5 m6 : ℕ)
    (hj2 : j2X ≤ 10 * (b + 1) * X) (hjc : jc ≤ X) (hjz : jz ≤ X) (hco : co ≤ X) :
    11 * Xb * X + (j2X + (2 * Xb * X + (jc + (jz + co)))) ≤
      P + (20 * Xb + 10 * (b + 1) + m4 + m5 + m6 + 10) * X := by
  have e : (20 * Xb + 10 * (b + 1) + m4 + m5 + m6 + 10) * X =
    20 * (Xb * X) + 10 * (b + 1) * X + (m4 + m5 + m6) * X + 10 * X := by ring
  have e1 : 11 * Xb * X = 11 * (Xb * X) := by ring
  have e2 : 2 * Xb * X = 2 * (Xb * X) := by ring
  rw [e, e1, e2]; omega

theorem main_cost_small1 (P Xb X b j2X jc jz ci co jz0 m4 m5 m6 : ℕ)
    (hj2 : j2X ≤ 10 * (b + 1) * X) (hjc : jc ≤ X) (hjz : jz ≤ X) (hci : ci ≤ X) (hco : co ≤ X)
    (hjz0 : jz0 ≤ X) :
    11 * Xb * X + (j2X + (2 * Xb * X + (jc + (jz + (ci + co) + jz0)))) ≤
      P + (20 * Xb + 10 * (b + 1) + m4 + m5 + m6 + 10) * X := by
  have e : (20 * Xb + 10 * (b + 1) + m4 + m5 + m6 + 10) * X =
    20 * (Xb * X) + 10 * (b + 1) * X + (m4 + m5 + m6) * X + 10 * X := by ring
  have e1 : 11 * Xb * X = 11 * (Xb * X) := by ring
  have e2 : 2 * Xb * X = 2 * (Xb * X) := by ring
  rw [e, e1, e2]; omega

theorem main_w (Q : Program) (C : ℕ) (hC : ICall Q iregs C) (A k : ℕ) (QT : QueryTime Q A k)
    (n : ℕ) (adj : Fin n → Fin n → Bool) (coins : List Bool) (J : ℕ) (hJ : Cmd.FieldsFit J (main Q A k)) :
    ∃ t K, WExec (runTapes (encodeDigraph n adj) coins) J (main Q A k) ⟨fun _ => 0, []⟩ t K ∧
      t.out = [answer Q A k adj coins] ∧ K ≤ mainBound n A k J C := by
  classical
  set τ := runTapes (encodeDigraph n adj) coins with hτ
  set b := hostWidth n A k with hbdef
  have hb0 : (BIGv n A k + trials n * seedWidth n + (2 * majorityHalf n + 2) * (coinSpan A k n + 2)).size +
      1000 * (n + 1) ^ 3 * (k + 1) + 2 * A.size + 4 * seedWidth n + 64 + (2 * trials n + 2).size ≤ b := le_rfl
  have c14 : ∀ i, 14 ≤ cell i := fun i => by unfold cell; omega
  have kk : k + 1 ≤ 1000 * (n + 1) ^ 3 * (k + 1) := by
    have : 1 ≤ 1000 * (n + 1) ^ 3 := by have := Nat.one_le_pow 3 (n + 1) (by omega); omega
    calc k + 1 = 1 * (k + 1) := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ this
  have nn : n + 1 ≤ 1000 * (n + 1) ^ 3 * (k + 1) := by
    have : n + 1 ≤ (n + 1) ^ 3 := by
      calc n + 1 = (n + 1) ^ 1 := by ring
        _ ≤ (n + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : (n + 1) ^ 3 ≤ 1000 * (n + 1) ^ 3 * (k + 1) := by
      calc (n + 1) ^ 3 ≤ 1000 * (n + 1) ^ 3 := by omega
        _ ≤ _ := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have h64 : 64 * (n + 1) ^ 3 ≤ 1000 * (n + 1) ^ 3 * (k + 1) := by
    calc 64 * (n + 1) ^ 3 ≤ 1000 * (n + 1) ^ 3 := by omega
      _ ≤ _ := Nat.le_mul_of_pos_right _ (by omega)
  have hb2 : 2 ≤ b := by generalize 1000 * (n + 1) ^ 3 * (k + 1) = P at hb0; omega
  have hb3 : 64 * (n + 1) ^ 3 ≤ b := by generalize 1000 * (n + 1) ^ 3 * (k + 1) = P at hb0 h64; omega
  have hbp : 1000 * (n + 1) ^ 3 * (k + 1) + 2 * A.size ≤ b := by
    generalize 1000 * (n + 1) ^ 3 * (k + 1) = P at hb0 ⊢; omega
  have hbn : n.size + 2 ≤ b := by
    have : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
    generalize 1000 * (n + 1) ^ 3 * (k + 1) = P at hb0 nn; omega
  have hbk : k.size ≤ b := by
    have : k.size ≤ k := Nat.size_le.mpr Nat.lt_two_pow_self
    generalize 1000 * (n + 1) ^ 3 * (k + 1) = P at hb0 kk; omega
  have hbA : A.size ≤ b := by generalize 1000 * (n + 1) ^ 3 * (k + 1) = P at hb0; omega
  have b64 : 64 ≤ b := by
    have : 1 ≤ (n + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
    omega
  have small : ∀ c, c < 64 → c.size ≤ b := fun c hc =>
    Nat.size_le.mpr (lt_of_lt_of_le hc (le_trans (by norm_num : 64 ≤ 2 ^ 6)
      (Nat.pow_le_pow_right (by norm_num) (by omega))))
  rw [main_eq] at hJ ⊢
  simp only [ifLe, Cmd.FieldsFit] at hJ
  obtain ⟨hf0, hfr, hf1, hn1, hn2, hfs, hfb⟩ := hJ
  set S0 : Store := ⟨fun _ => 0, []⟩ with hS0
  have fS0 : S0.Fits b := by intro a; simp [hS0]
  -- constants
  have w0 : Circuit.width (fun i => S0.mem (cell i)) (C0main A k) ≤ b := by
    simp only [C0main, Circuit.width, asg, Expression.width, Expression.eval]
    simp
    exact ⟨by omega, small 2 (by norm_num), small 3 (by norm_num), small 6 (by norm_num),
      small 7 (by norm_num), small 50 (by norm_num), small 49 (by norm_num), hbA, hbk⟩
  obtain ⟨S1, e1, v1, o1, f1⟩ := wcirc (τ := τ) (J := J) (C0main A k) S0 fS0 hb2 w0 hf0
  have r1 (i : ℕ) : S1.mem (cell i) = Circuit.result (fun i => S0.mem (cell i)) (C0main A k) i := v1 i
  have s1zero (a : ℕ) (ha : 14 ≤ a) (hd : ∀ d ∈ [rOne, rZero, rTwo, rThree, rSix, rSeven, rFifty, rC49, rA, rKk, 50],
      a ≠ cell d) : S1.mem a = 0 := by
    have e : a = cell (a - 14) := by simp [cell]; omega
    have hu : ∀ x ∈ C0main A k, a - 14 ≠ x.dst := by
      simp only [C0main, asg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, cell, rOne, rZero,
        rTwo, rThree, rSix, rSeven, rFifty, rC49, rA, rKk] at hd ⊢
      omega
    rw [e, r1, Circuit.result_untouched _ _ _ hu]
  have c1 : Consts S1 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      (rw [r1]; simp [C0main, Circuit.result, asg, Assignment.update, Expression.eval, Function.update,
        rOne, rZero, rTwo, rThree, rSix, rSeven, rFifty, rC49, rA, rKk])
  have s1A : S1.mem (cell rA) = A := by
    rw [r1]; simp [C0main, Circuit.result, asg, Assignment.update, Expression.eval, Function.update,
      rOne, rZero, rTwo, rThree, rSix, rSeven, rFifty, rC49, rA, rKk]
  have s1k : S1.mem (cell rKk) = k := by
    rw [r1]; simp [C0main, Circuit.result, asg, Assignment.update, Expression.eval, Function.update,
      rOne, rZero, rTwo, rThree, rSix, rSeven, rFifty, rC49, rA, rKk]
  have s150 : S1.mem (cell 50) = 0 := by
    rw [r1]; simp [C0main, Circuit.result, asg, Assignment.update, Expression.eval, Function.update,
      rOne, rZero, rTwo, rThree, rSix, rSeven, rFifty, rC49, rA, rKk]
  -- read n
  have hin : τ.input.drop 0 = pairs n.bits ++ false :: (List.finRange n).flatMap fun i =>
      (List.finRange n).map fun j => adj i j := by
    simp [hτ, runTapes, encodeDigraph, encNat, pairs]
  obtain ⟨S2, j2, ex2, hj2, p2, x2, _, _, o2, fr2⟩ := readField_exec (τ := τ) (b := b) readRegs 0 n _ S1 s150 hin
    f1 hb2 (by
      have : (0 + 2 * n.size + 1).size ≤ 0 + 2 * n.size + 1 := Nat.size_le.mpr Nat.lt_two_pow_self
      have : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
      have nn2 : 2 * n + 1 ≤ 64 * (n + 1) ^ 3 := by
        have : n + 1 ≤ (n + 1) ^ 3 := by
          calc n + 1 = (n + 1) ^ 1 := by ring
            _ ≤ (n + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
        omega
      omega) (by omega)
  have w2 := toW ex2 f1 hfr hb2
  have fS2 := ex2.post f1
  have keep2 (a : ℕ) (ha : 14 ≤ a) (hd : a < cell 50 ∨ cell 57 ≤ a) : S2.mem a = S1.mem a := by
    apply fr2; intro i; simp only [readRegs, Function.Embedding.coeFn_mk, cell] at hd ⊢
    have := i.isLt; omega
  have s2_51 : S2.mem (cell 51) = n := x2
  have s2_50 : S2.mem (cell 50) = 2 * n.size + 1 := by rw [show cell 50 = readRegs 0 from rfl, p2]; simp
  have s2z : S2.mem (cell rZero) = 0 := by rw [keep2 _ (c14 _) (Or.inl (by simp [cell, rZero]))]; exact c1.zero
  have s2z' : S2.mem (cell 15) = 0 := s2z
  have w3 : Circuit.width (fun i => S2.mem (cell i)) C1main ≤ b := by
    simp only [C1main, Circuit.width, asg, Expression.width, Expression.eval, Assignment.update,
      Function.update, rN, rCur, rZero]
    simp [s2_51, s2_50, s2z']
    have : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
    have h1 : n.size ≤ b := by omega
    have h2 : (2 * n.size + 1).size ≤ 2 * n.size + 1 := Nat.size_le.mpr Nat.lt_two_pow_self
    exact ⟨h1, by
      have nn2 : 2 * n + 1 ≤ 64 * (n + 1) ^ 3 := by
        have : n + 1 ≤ (n + 1) ^ 3 := by
          calc n + 1 = (n + 1) ^ 1 := by ring
            _ ≤ (n + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
        omega
      omega⟩
  obtain ⟨S3, e3, v3, o3, f3⟩ := wcirc (τ := τ) (J := J) C1main S2 fS2 hb2 w3 hf1
  have keep3 (a : ℕ) (ha : 14 ≤ a) (h1 : a ≠ cell rN) (h2 : a ≠ cell rCur) : S3.mem a = S2.mem a := by
    have ee : a = cell (a - 14) := by simp [cell]; omega
    rw [ee, v3, Circuit.result_untouched]
    simp only [C1main, asg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp only [cell, rN, rCur] at h1 h2 ⊢; omega
  have s3n : S3.mem (cell rN) = n := by
    rw [v3]; simp [C1main, Circuit.result, asg, Assignment.update, Expression.eval, Function.update, rN, rCur,
      rZero, s2_51, s2z']
  have s3cur : S3.mem (cell rCur) = 2 * n.size + 1 := by
    rw [v3]; simp [C1main, Circuit.result, asg, Assignment.update, Expression.eval, Function.update, rN, rCur,
      rZero, s2_50, s2z']
  -- memory facts carried from the zero store
  have keep321 (a : ℕ) (ha : 14 ≤ a) (h : a ≠ cell rN ∧ a ≠ cell rCur ∧ (a < cell 50 ∨ cell 57 ≤ a)) :
      S3.mem a = S1.mem a := by
    rw [keep3 a ha h.1 h.2.1, keep2 a ha h.2.2]
  have c3 : Consts S3 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      first
      | (rw [keep321 _ (c14 _) (by simp [cell, rN, rCur, rOne, rZero, rTwo, rThree, rSix, rSeven, rFifty, rC49])])
    · exact c1.one
    · exact c1.zero
    · exact c1.two
    · exact c1.three
    · exact c1.six
    · exact c1.seven
    · exact c1.fifty
    · exact c1.c49
  have o3' : S3.out = [] := by rw [o3, o2, o1]
  have Xc_ge : 4 * b + 4 * J + 4 ≤ (b * (5 * b + 9) + 15) * (4 * b + 4 * J + 4) :=
    Nat.le_mul_of_pos_left _ (by omega)
  have jc := jumpCost_le (J := J) (s := S3) (b := b) hn1 hn2 (f3 _) (f3 _)
  have m0 : Circuit.multiplicity (fun i => S0.mem (cell i)) (C0main A k) = 11 := by
    simp [C0main, Circuit.multiplicity, asg, Expression.multiplicity]
  have m3 : Circuit.multiplicity (fun i => S2.mem (cell i)) C1main = 2 := by
    simp [C1main, Circuit.multiplicity, asg, Expression.multiplicity]
  have hfsmall := hfs
  simp only [smallCmd, ifLe, Cmd.FieldsFit] at hfsmall
  obtain ⟨hz1, hz2, hz3, hz4⟩ := hfsmall
  by_cases hn : n ≤ 1
  · have hle : S3.mem (cell rN) ≤ S3.mem (cell rOne) := by rw [s3n, c3.one]; exact hn
    have ans : answer Q A k adj coins = smallCycleAnswer n adj := by unfold answer; rw [if_pos hn]
    have jz := jumpCost_le (J := J) (s := S3) (b := b) hz1 hz2 (f3 _) (f3 _)
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn with h0 | h1
    · -- n = 0
      have hz : S3.mem (cell rN) ≤ S3.mem (cell rZero) := by rw [s3n, c3.zero, h0]
      have eo : WExec τ J (.op (.output (cell rZero))) S3 _ (Op.cost τ S3 (.output (cell rZero))) := WExec.op S3 _
      refine ⟨_, _, e1.seq (w2.seq (e3.seq (WExec.yes hle (WExec.yes hz eo)))), ?_, ?_⟩
      · simp only [Op.eval, o3', c3.zero, ans, smallCycleAnswer]
        subst h0; simp
      · rw [m0, m3]; unfold mainBound
        have co : Op.cost τ S3 (.output (cell rZero)) ≤ 4 * b + 4 * J + 4 := by
          simp only [Op.cost]
          have := hz3 (cell rZero) (by simp [Op.fields])
          have := f3 (cell rZero); omega
        exact main_cost_small0 _ _ _ _ _ _ _ _ _ _ _ (Nat.mul_le_mul_right _ (show j2 ≤ 10 * (b + 1) by omega))
          (jle_X' hb2 jc) (jle_X' hb2 jz) co
    · -- n = 1
      have hz : ¬ S3.mem (cell rN) ≤ S3.mem (cell rZero) := by rw [s3n, c3.zero, h1]; omega
      have ei : WExec τ J (.op (.input (cell rCoin) (cell rCur))) S3 _ (Op.cost τ S3 (.input (cell rCoin) (cell rCur))) :=
        WExec.op S3 _
      set S4 := Op.eval τ S3 (.input (cell rCoin) (cell rCur)) with hS4
      have eo : WExec τ J (.op (.output (cell rCoin))) S4 _ (Op.cost τ S4 (.output (cell rCoin))) := WExec.op S4 _
      refine ⟨_, _, e1.seq (w2.seq (e3.seq (WExec.yes hle (WExec.no hz (ei.seq eo))))), ?_, ?_⟩
      · simp only [hS4, Op.eval, Store.write, o3', ans, smallCycleAnswer]
        subst h1
        simp [s3cur, hτ, runTapes, encodeDigraph, encNat, bitVal]
        simp [List.finRange_succ]
      · rw [m0, m3]; unfold mainBound
        have ci : Op.cost τ S3 (.input (cell rCoin) (cell rCur)) ≤ 4 * b + 4 * J + 4 := by
          simp only [Op.cost]
          have h1 := hz4.1 (cell rCoin) (by simp [Op.fields])
          have h2 := hz4.1 (cell rCur) (by simp [Op.fields])
          have h3 := f3 (cell rCur)
          have h4 : (bitVal τ.input[S3.mem (cell rCur)]?).size ≤ 2 := by
            rcases τ.input[S3.mem (cell rCur)]? with _ | ⟨_ | _⟩ <;> decide
          omega
        have co : Op.cost τ S4 (.output (cell rCoin)) ≤ 4 * b + 4 * J + 4 := by
          simp only [Op.cost]
          have h1 := hz4.2 (cell rCoin) (by simp [Op.fields])
          have h4 : (S4.mem (cell rCoin)).size ≤ 2 := by
            simp only [hS4, Op.eval, Store.write, Function.update_self]
            rcases τ.input[S3.mem (cell rCur)]? with _ | ⟨_ | _⟩ <;> decide
          omega
        have jz0 := jle0_X (jumpCost_zero_le (J := J) (show (((Op.eval τ S4 (.output (cell rCoin)))).mem 0).size ≤ b by
          simp only [Op.eval]
          simp only [hS4, Op.eval, Store.write]
          by_cases h : (0 : ℕ) = cell rCoin
          · simp [cell, rCoin] at h
          · rw [Function.update_of_ne h]; exact f3 0))
        exact main_cost_small1 _ _ _ _ _ _ _ _ _ _ _ _ _ (Nat.mul_le_mul_right _ (show j2 ≤ 10 * (b + 1) by omega))
          (jle_X' hb2 jc) (jle_X' hb2 jz) ci co jz0
  · have hn2 : 2 ≤ n := by omega
    have hgt : ¬ S3.mem (cell rN) ≤ S3.mem (cell rOne) := by rw [s3n, c3.one]; omega
    have s3A : S3.mem (cell rA) = A := by
      rw [keep321 _ (c14 _) (by simp [cell, rN, rCur, rA])]; exact s1A
    have s3k : S3.mem (cell rKk) = k := by
      rw [keep321 _ (c14 _) (by simp [cell, rN, rCur, rKk])]; exact s1k
    have hz : ∀ a, cell 112 ≤ a → S3.mem a = 0 := by
      intro a ha
      have h14 : 14 ≤ a := le_trans (c14 _) ha
      rw [keep321 a h14 ⟨by simp [cell, rN] at ha ⊢; omega, by simp [cell, rCur] at ha ⊢; omega,
        Or.inr (by simp [cell] at ha ⊢; omega)⟩]
      exact s1zero a h14 (fun d hd => c0_ne a ha d hd)
    obtain ⟨t, K, ex, ho, hK, ft⟩ := big_w Q C hC A k QT n hn2 adj coins J hfb S3 c3 s3n s3A s3k s3cur f3 o3' hz
    refine ⟨t, _, e1.seq (w2.seq (e3.seq (WExec.no hgt ex))), ?_, ?_⟩
    · rw [ho]; unfold answer; rw [if_neg hn]
    · rw [m0, m3]; unfold mainBound
      exact main_cost_big _ _ _ _ _ _ _ _ _ _ _ (by unfold bigBound at hK; exact hK)
        (Nat.mul_le_mul_right _ (show j2 ≤ 10 * (b + 1) by omega)) (jle_X' hb2 jc)
        (jle0_X (jumpCost_zero_le (J := J) (ft 0))) Xc_ge

end DirectedHamiltonicity.Main.CycleHost


-- ===== Solutions/Dev/Final.lean =====

set_option autoImplicit false

namespace DirectedHamiltonicity.Main.CycleHost

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word
open TargetedSamplers.Structured.Work
open TargetedSamplers.Structured.Interp DirectedHamiltonicity.Main.CycleReduction FiniteSampling

/-- The final polynomial-overhead bound (proved separately). -/
def FinalBound (A k J C : ℕ) : Prop :=
  ∃ (D : ℝ) (j : ℕ), 0 < D ∧ ∀ n : ℕ,
    ((mainBound n A k J C + 1 : ℕ) : ℝ) ≤ D * (searchWork A k n : ℝ) * ((n : ℝ) + 1) ^ j

theorem execute_of_bound (Q : Program) (A k : ℕ) (QT : QueryTime Q A k)
    (hB : ∀ J C, FinalBound A k J C) : ExecutesSearch Q A k := by
  obtain ⟨C, hC⟩ := icall_exists Q
  let c := main Q A k
  let J := max (staticWidth c.program) ((c.compile 0).length.size)
  have hJ : Cmd.FieldsFit J c :=
    framework.2.2.2 c (le_max_left _ _) (framework.2.2.1 c)
  obtain ⟨D, j, hD, hb⟩ := hB J C
  refine ⟨c.program, D, j, hD, fun n adj coins => ?_⟩
  obtain ⟨t, K, ex, hout, hK⟩ := main_w Q C hC A k QT n adj coins J hJ
  have run := framework.1 ex (le_max_right _ _)
  rw [hout] at run
  refine ⟨K + 1, run, ?_⟩
  have h1 : ((K + 1 : ℕ) : ℝ) ≤ ((mainBound n A k J C + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
  exact h1.trans (hb n)

end DirectedHamiltonicity.Main.CycleHost


-- ===== Solutions/Dev/ParamsA.lean =====

set_option autoImplicit false

namespace DirectedHamiltonicity.Main.CycleHost

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word
open TargetedSamplers.Structured.Interp DirectedHamiltonicity.Main.CycleReduction

theorem rankDraw_symm_vals (n D : ℕ) (hD : D < drawCount n) :
    let d := (rankDraw n).symm ⟨D, hD⟩
    let I := 50 ^ (n * n) * Wmax n ^ (n * 3) * (Bmax n + 1)
    let PW := Wmax n ^ (n * 3)
    d.1.1.val = D / I / n ∧ d.1.2.val = D / I % n ∧ d.2.2.val = D % I % (Bmax n + 1) ∧
    (∀ x y : Fin n, (D % I / (Bmax n + 1) / PW) / 50 ^ (x.val * n + y.val) % 50 =
      (d.2.1.1 (x, y)).val) ∧
    (∀ (y : Fin n) (l : Fin 3), (D % I / (Bmax n + 1) % PW) / Wmax n ^ (y.val * 3 + l.val) % Wmax n =
      (d.2.1.2 (y, l)).val) := by
  intro d I PW
  simp only [d, rankDraw, tableRank, Equiv.symm_trans_apply, Equiv.prodCongr_symm,
    Equiv.prodCongr_apply, finProdFinEquiv_symm_apply, Prod.map, Fin.coe_divNat, Fin.coe_modNat]
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · intro x y
    simp [Equiv.arrowCongr_symm, finFunctionFinEquiv_symm_apply_val, finProdFinEquiv_apply_val,
      Fin.coe_divNat, Fin.coe_modNat, I, PW]
    rw [show x.val * n + y.val = y.val + n * x.val by ring]
  · intro y l
    simp [Equiv.arrowCongr_symm, finFunctionFinEquiv_symm_apply_val, finProdFinEquiv_apply_val,
      Fin.coe_divNat, Fin.coe_modNat, I, PW]
    rw [show y.val * 3 + l.val = l.val + 3 * y.val by ring]

/-- Run a straight-line circuit, starting from the store's own register view. -/
theorem circ_run {τ : Tapes} {b : ℕ} (as : List Assignment) (s : Store) (fit : s.Fits b)
    (hb : 2 ≤ b) (bound : Circuit.width (fun i => s.mem (cell i)) as ≤ b) :
    ∃ t j, Exec τ (fun w => w.Fits b) (circ as) s t j ∧
      j ≤ Circuit.multiplicity (fun i => s.mem (cell i)) as * (b * (5 * b + 9) + 15) ∧
      (∀ i, t.mem (cell i) = Circuit.result (fun i => s.mem (cell i)) as i) ∧ t.out = s.out ∧
      (∀ a, 14 ≤ a → (∀ x ∈ as, a ≠ cell x.dst) → t.mem a = s.mem a) := by
  obtain ⟨t, j, ex, hj, rep, out⟩ := Circuit.exec (τ := τ) as _ s (fun _ => rfl) fit hb bound
  refine ⟨t, j, ex, hj.trans (Circuit.steps_le as _ b bound), rep, out, ?_⟩
  intro a ha hne
  obtain ⟨i, rfl⟩ : ∃ i, a = cell i := ⟨a - 14, by simp only [cell]; omega⟩
  rw [rep i, Circuit.result_untouched]
  intro x hx h
  exact hne x hx (h ▸ rfl)

theorem size_le_of_lt_pow {x E b : ℕ} (h : x < 2 ^ E) (hE : E ≤ b) : x.size ≤ b :=
  (Nat.size_le.mpr h).trans hE

theorem size_twice_le {x E b : ℕ} (h : x < 2 ^ E) (hE : E + 2 ≤ b) : (2 * x + 2).size ≤ b :=
  (size_twice_add_two x).trans (by have := Nat.size_le.mpr h; omega)

theorem wmax_le (n : ℕ) : Wmax n ≤ 2 ^ (n + 3) := by
  have := (Nat.lt_two_pow_self (n := n)).le
  rw [pow_add]
  show 6 * (n - 1) ≤ 2 ^ n * 2 ^ 3
  rw [show (2:ℕ) ^ 3 = 8 by norm_num]; omega

theorem nn_le (n : ℕ) : n * n ≤ 2 ^ (2 * n) := by
  have := (Nat.lt_two_pow_self (n := n)).le
  rw [two_mul, pow_add]; exact Nat.mul_le_mul this this

theorem bmax_le (n : ℕ) : Bmax n + 1 ≤ 2 ^ (2 * n + 4) := by
  have h := nn_le n
  have h1 := Nat.one_le_two_pow (n := 2 * n)
  have : Bmax n + 1 ≤ 8 * (n * n) + 1 := by
    show (n - 1) * (6 * (n - 1)) + 1 ≤ 8 * (n * n) + 1
    rcases n with _ | m
    · simp
    · simp only [Nat.add_sub_cancel]; nlinarith
  rw [pow_add, show (2:ℕ) ^ 4 = 16 by norm_num]; omega

theorem drawCount_le (n : ℕ) : drawCount n ≤ 2 ^ (9 * (n * n) + 13 * n + 4) := by
  have a := nn_le n
  have b : 50 ^ (n * n) ≤ 2 ^ (6 * (n * n)) := by
    rw [pow_mul (2:ℕ) 6]; exact Nat.pow_le_pow_left (by norm_num) _
  have c : Wmax n ^ (n * 3) ≤ 2 ^ ((n + 3) * (n * 3)) := by
    rw [pow_mul (2:ℕ) (n + 3)]; exact Nat.pow_le_pow_left (wmax_le n) _
  have d := bmax_le n
  have : 2 ^ (9 * (n * n) + 13 * n + 4) =
      2 ^ (2 * n) * ((2 ^ (6 * (n * n)) * 2 ^ ((n + 3) * (n * 3))) * 2 ^ (2 * n + 4)) := by
    rw [← pow_add, ← pow_add, ← pow_add]; congr 1; ring
  rw [this]
  exact Nat.mul_le_mul a (Nat.mul_le_mul (Nat.mul_le_mul b c) d)

theorem drawCount_lt (n : ℕ) : drawCount n < 2 ^ (16 * (n + 1) ^ 2) :=
  (drawCount_le n).trans_lt (Nat.pow_lt_pow_right (by norm_num) (by nlinarith))

theorem kept_of {as : List Assignment} {dirty : List ℕ} {u v : Store}
    (h : ∀ x ∈ as, x.dst ∈ dirty) (out : v.out = u.out)
    (fr : ∀ a, 14 ≤ a → (∀ x ∈ as, a ≠ cell x.dst) → v.mem a = u.mem a) :
    Kept dirty u v (fun _ => True) :=
  ⟨out, fun a ha hd _ => fr a ha fun x hx => hd x.dst (h x hx)⟩

/-! ### Power-of-two upper bounds, composed syntactically. -/

theorem pb_mul {x y a c : ℕ} (hx : x ≤ 2 ^ a) (hy : y ≤ 2 ^ c) : x * y ≤ 2 ^ (a + c) := by
  rw [pow_add]; exact Nat.mul_le_mul hx hy

theorem pb_add {x y a c : ℕ} (hx : x ≤ 2 ^ a) (hy : y ≤ 2 ^ c) : x + y ≤ 2 ^ (a + c + 1) := by
  have h1 : 2 ^ a ≤ 2 ^ (a + c) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ c ≤ 2 ^ (a + c) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [pow_succ]; omega

theorem pb_sub {x y a : ℕ} (hx : x ≤ 2 ^ a) : x - y ≤ 2 ^ a := (Nat.sub_le _ _).trans hx

theorem pb_div {x y a : ℕ} (hx : x ≤ 2 ^ a) : x / y ≤ 2 ^ a := (Nat.div_le_self _ _).trans hx

theorem pb_mod {x y a : ℕ} (hx : x ≤ 2 ^ a) : x % y ≤ 2 ^ a := (Nat.mod_le _ _).trans hx

theorem pb_pow {x e a : ℕ} (hx : x ≤ 2 ^ a) : x ^ e ≤ 2 ^ (a * e) := by
  rw [pow_mul]; exact Nat.pow_le_pow_left hx _

theorem clog_le_self' (x : ℕ) : Nat.clog 2 x ≤ x :=
  Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le

theorem pb_clog {x a : ℕ} (hx : x ≤ 2 ^ a) : Nat.clog 2 x ≤ 2 ^ a := (clog_le_self' x).trans hx

theorem pb_atom (x : ℕ) : x ≤ 2 ^ x := Nat.lt_two_pow_self.le

theorem pb_size (x : ℕ) : x ≤ 2 ^ x.size := (Nat.lt_size_self x).le


theorem size_le_pb {x E b : ℕ} (h : x ≤ 2 ^ E) (hE : E + 1 ≤ b) : x.size ≤ b :=
  size_le_of_lt_pow (h.trans_lt (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self E))) hE

theorem twice_le_pb {x E b : ℕ} (h : x ≤ 2 ^ E) (hE : E + 3 ≤ b) : (2 * x + 2).size ≤ b :=
  size_twice_le (h.trans_lt (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self E))) hE

/-! ### Arithmetic identities for the parameters. -/

theorem nat_ceil_div (a c : ℕ) (hc : 0 < c) : ⌈(a : ℚ) / c⌉₊ = (a + c - 1) / c := by
  apply eq_of_forall_ge_iff
  intro z
  rw [Nat.ceil_le, div_le_iff₀ (by exact_mod_cast hc), ← Nat.lt_succ_iff,
    Nat.div_lt_iff_lt_mul hc]
  have : ((a : ℚ) ≤ (z : ℚ) * c) ↔ a ≤ z * c := by exact_mod_cast Iff.rfl
  rw [this, Nat.succ_mul]
  omega

theorem ceil_pow_div (p q n : ℕ) (hq : 0 < q) :
    ⌈((p : ℚ) / q) ^ n⌉₊ = (p ^ n + q ^ n - 1) / q ^ n := by
  rw [div_pow, ← nat_ceil_div _ _ (pow_pos hq n)]
  push_cast; rfl

theorem outerCeil_eq (n : ℕ) : outerCeil n = (50 ^ n + 49 ^ n - 1) / 49 ^ n := by
  have := ceil_pow_div 50 49 n (by norm_num)
  simpa [outerCeil] using this

theorem ceil15_eq (n : ℕ) : ⌈(15 / 8 : ℚ) ^ n⌉₊ = (15 ^ n + 8 ^ n - 1) / 8 ^ n := by
  have := ceil_pow_div 15 8 n (by norm_num)
  simpa using this

theorem size_eq_clog (x : ℕ) : x.size = Nat.clog 2 (x + 1) := by
  apply eq_of_forall_ge_iff
  intro c
  rw [Nat.size_le, Nat.clog_le_iff_le_pow (by norm_num)]
  omega

theorem card_draw (n : ℕ) : Fintype.card (Draw n) = drawCount n := by
  rw [Fintype.card_congr (rankDraw n), Fintype.card_fin]

/-! ### The pieces of `params`. -/

def paramsC1 : List Assignment := [
    asg rN2 (.arithmetic .mul rN rN), asg rM (.arithmetic .mul rThree rN2),
    asg rTmp (.sub rN rOne), asg rW (.arithmetic .mul rSix rTmp),
    asg rBm1 (.arithmetic .mul rTmp rW), asg rBm1 (.add rBm1 rOne),
    asg rTmp2 (.arithmetic .mul rN rThree), asg rPW (.arithmetic .pow rW rTmp2),
    asg rP50 (.arithmetic .pow rFifty rN2), asg rIn (.arithmetic .mul rP50 rPW),
    asg rIn (.arithmetic .mul rIn rBm1), asg rDc (.arithmetic .mul rN2 rIn),
    asg rP50 (.arithmetic .pow rFifty rN), asg rP49 (.arithmetic .pow rC49 rN),
    asg rCeil50 (.add rP50 rP49), asg rCeil50 (.sub rCeil50 rOne),
    asg rCeil50 (.arithmetic .div rCeil50 rP49),
    asg rTb (.arithmetic .mul rN2 rBm1), asg rTmp (.literal 4), asg rTb (.arithmetic .mul rTmp rTb),
    asg rTb (.arithmetic .mul rTb rCeil50),
    asg rOb (.arithmetic .mul rSix rN2), asg rOb (.add rOb rSix),
    asg rTrials (.arithmetic .mul rTb rOb),
    asg rTmp (.literal 15), asg rP15 (.arithmetic .pow rTmp rN),
    asg rTmp (.literal 8), asg rP8 (.arithmetic .pow rTmp rN),
    asg rCeil15 (.add rP15 rP8), asg rCeil15 (.sub rCeil15 rOne),
    asg rCeil15 (.arithmetic .div rCeil15 rP8),
    asg rBase (.add rN rM), asg rBase (.add rBase rW), asg rBase (.add rBase rOne),
    asg rBase (.arithmetic .pow rBase rKk),
    asg rL (.arithmetic .mul rA rCeil15), asg rL (.arithmetic .mul rL rBase),
    asg rTmp (.add rTrials rOne)]

def paramsC2 : List Assignment := [
    asg rR (.add rTmp2 rOb), asg rR (.add rR rR), asg rR2 (.add rR rR),
    asg rTapeBase (.arithmetic .mul rTrials rSw),
    asg rXmax (.add rN rOne), asg rTmp (.arithmetic .mul rXmax rXmax),
    asg rXmax (.arithmetic .mul rTmp rXmax), asg rTmp (.literal 128),
    asg rXmax (.arithmetic .mul rTmp rXmax),
    asg rVB (.literal xBase), asg rVB (.add rVB rXmax),
    asg 103 (.add rVB rN), asg 102 (.add 103 rL), asg 102 (.add 102 rOne),
    asg 105 (.literal xBase), asg 110 (.literal 1), asg 111 (.literal 0)]

theorem params_eq : params =
    .seq (circ paramsC1) (.seq (clogInto rTmp2 rTmp) (.seq (clogInto rSw rDc) (circ paramsC2))) :=
  rfl

theorem clogInto_exec {τ : Tapes} {b : ℕ} (dst src : ℕ) (s : Store) (x : ℕ)
    (hx : s.mem (cell src) = x) (z : s.mem (cell rZero) = 0) (fit : s.Fits b) (hb2 : 2 ≤ b)
    (room : Nat.clog 2 x + 1 ≤ b) (hxb : x.size ≤ b) :
    ∃ t j, Exec τ (fun w => w.Fits b) (clogInto dst src) s t j ∧
      j ≤ 4 * Nat.clog 2 x + 4 + 2 * (b * (5 * b + 9) + 15) ∧
      t.mem (cell dst) = Nat.clog 2 x ∧ t.out = s.out ∧
      ∀ a, 14 ≤ a → a ≠ cell dst → (a < cell 90 ∨ cell 93 < a) → t.mem a = s.mem a := by
  simp only [rZero] at z
  obtain ⟨s1, j1, e1, hj1, v1, o1, f1⟩ := circ_run (τ := τ) [asg 90 (.add src rZero)] s fit hb2
    (by simpa [Circuit.width, Expression.width, Expression.eval, asg, hx, z, rZero] using hxb)
  simp only [Circuit.multiplicity, Expression.multiplicity, asg] at hj1
  have in1 : s1.mem (logRegs 0) = x := by
    rw [show logRegs 0 = cell 90 from rfl, v1]
    simp [Circuit.result, Assignment.update, Expression.eval, asg, hx, z, rZero]
  obtain ⟨s2, e2, p2, l2, o2, f2⟩ := ceilLog_exec (τ := τ) logRegs x s1 in1 (e1.post fit) room
  have z2 : s2.mem (cell 15) = 0 := by
    rw [f2 _ (by decide) (by decide) (by decide), f1 _ (by decide) (by simp [asg, cell, rZero]), z]
  have fit2 := e2.post (e1.post fit)
  obtain ⟨s3, j3, e3, hj3, v3, o3, f3⟩ := circ_run (τ := τ) [asg dst (.add 92 rZero)] s2 fit2 hb2
    (by
      simp only [Circuit.width, Expression.width, Expression.eval, asg, z2, rZero, max_le_iff]
      refine ⟨?_, Nat.zero_le _⟩
      rw [show cell 92 = logRegs 2 from rfl, l2, add_zero]
      exact (Nat.size_le.mpr (Nat.lt_two_pow_self)).trans (by omega))
  simp only [Circuit.multiplicity, Expression.multiplicity, asg] at hj3
  refine ⟨s3, j1 + ((4 * Nat.clog 2 x + 4) + j3), e1.seq (e2.seq e3), by omega, ?_, ?_, ?_⟩
  · rw [v3]
    simp [Circuit.result, Assignment.update, Expression.eval, asg, z2, rZero]
    rw [show cell 92 = logRegs 2 from rfl, l2]
  · rw [o3, o2, o1]
  · intro a ha hd hr
    have n1 : a ≠ logRegs 1 := by simp only [logRegs, cell] at hr ⊢; change a ≠ 14 + (90 + 1); omega
    have n2 : a ≠ logRegs 2 := by simp only [logRegs, cell] at hr ⊢; change a ≠ 14 + (90 + 2); omega
    have n3 : a ≠ logRegs 3 := by simp only [logRegs, cell] at hr ⊢; change a ≠ 14 + (90 + 3); omega
    rw [f3 a ha (by simpa [asg] using hd), f2 a n1 n2 n3,
      f1 a ha (by simp only [List.mem_singleton, forall_eq, asg, cell] at hr ⊢; omega)]

theorem budget_facts {n k b : ℕ} (A : ℕ) (hb : 1000 * (n + 1) ^ 3 * (k + 1) + 2 * A.size ≤ b) :
    2 ≤ b ∧ 1000 * ((n + 1) ^ 2 * (k + 1)) + 2 * A.size ≤ b := by
  have hb' : 1000 * ((n + 1) ^ 3 * (k + 1)) + 2 * A.size ≤ b := by rw [← mul_assoc]; exact hb
  have h3 : (n + 1) ^ 2 * (k + 1) ≤ (n + 1) ^ 3 * (k + 1) :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by norm_num))
  have h1 : 1 ≤ (n + 1) ^ 2 * (k + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  constructor <;> omega

set_option maxHeartbeats 4000000 in
theorem paramsC1_run {τ : Tapes} {b : ℕ} (u : Store) {n : ℕ} (hn : 2 ≤ n) (A k : ℕ)
    (c : Consts u) (rn : u.mem (cell rN) = n) (ra : u.mem (cell rA) = A) (rk : u.mem (cell rKk) = k)
    (fit : u.Fits b) (hb : 1000 * (n + 1) ^ 3 * (k + 1) + 2 * A.size ≤ b) :
    ∃ v j, Exec τ (fun w => w.Fits b) (circ paramsC1) u v j ∧
      j ≤ (n * n + 7 * n + k + 40) * (b * (5 * b + 9) + 15) ∧
      v.mem (cell rN2) = n * n ∧ v.mem (cell rM) = 3 * (n * n) ∧ v.mem (cell rW) = Wmax n ∧
      v.mem (cell rBm1) = Bmax n + 1 ∧ v.mem (cell rPW) = Wmax n ^ (n * 3) ∧
      v.mem (cell rIn) = 50 ^ (n * n) * Wmax n ^ (n * 3) * (Bmax n + 1) ∧
      v.mem (cell rDc) = drawCount n ∧ v.mem (cell rTrials) = trials n ∧
      v.mem (cell rL) = coinSpan A k n ∧ v.mem (cell rOb) = outerBlocks n ∧
      v.mem (cell rTmp) = trials n + 1 ∧ v.out = u.out ∧
      (∀ a, 14 ≤ a → (∀ x ∈ paramsC1, a ≠ cell x.dst) → v.mem a = u.mem a) := by
  have c1 := c.one
  have c0 := c.zero
  have c3 := c.three
  have c6 := c.six
  have c50 := c.fifty
  have c49 := c.c49
  simp only [rN, rA, rKk, rOne, rZero, rThree, rSix, rFifty, rC49] at rn ra rk c1 c0 c3 c6 c50 c49
  have hA : A ≤ 2 ^ A.size := pb_size A
  obtain ⟨le2, key⟩ := budget_facts A hb
  ring_nf at key
  obtain ⟨v1, j1, e1, hj1, vals1, o1, f1⟩ := circ_run (τ := τ) paramsC1 u fit le2 (by
    simp only [paramsC1, Circuit.width, Expression.width, Assignment.update, Expression.eval,
      Arithmetic.value, asg, Function.update_apply, rN, rN2, rM, rTmp, rW, rBm1, rTmp2, rPW, rP50,
      rIn, rDc, rP49, rCeil50, rTb, rOb, rTrials, rP15, rP8, rCeil15, rBase, rL, rA, rKk, rOne,
      rThree, rSix, rFifty, rC49, rn, ra, rk, c1, c3, c6, c50, c49,
      Nat.reduceEqDiff, ↓reduceIte, max_le_iff]
    repeat' apply And.intro
    all_goals first
      | exact Nat.zero_le _
      | (apply twice_le_pb; (· (repeat' (first | apply pb_mul | apply pb_add | apply pb_sub | apply pb_div | apply pb_mod | apply pb_pow | apply pb_clog | assumption | apply pb_atom))); (ring_nf; omega))
      | (apply size_le_pb; (· (repeat' (first | apply pb_mul | apply pb_add | apply pb_sub | apply pb_div | apply pb_mod | apply pb_pow | apply pb_clog | assumption | apply pb_atom))); (ring_nf; omega)))
  simp only [paramsC1, Circuit.multiplicity, Expression.multiplicity, Assignment.update,
    Expression.eval, Arithmetic.value, asg, Function.update_apply, rN, rN2, rM, rTmp, rW, rBm1,
    rTmp2, rPW, rP50, rIn, rDc, rP49, rCeil50, rTb, rOb, rTrials, rP15, rP8, rCeil15, rBase, rL, rA,
    rKk, rOne, rThree, rSix, rFifty, rC49, rn, rk, c1, c3, c6, c50, c49,
    Nat.reduceEqDiff, ↓reduceIte] at hj1
  replace hj1 : j1 ≤ (n * n + 7 * n + k + 40) * (b * (5 * b + 9) + 15) := by
    refine le_trans hj1 (Nat.mul_le_mul_right _ ?_)
    clear * -
    omega
  have g := fun i => vals1 i
  have gN2 := g rN2
  have gM := g rM
  have gW := g rW
  have gB := g rBm1
  have gPW := g rPW
  have gIn := g rIn
  have gDc := g rDc
  have gTr := g rTrials
  have gL := g rL
  have gOb := g rOb
  have gTmp := g rTmp
  simp only [paramsC1, Circuit.result, Assignment.update,
    Expression.eval, Arithmetic.value, asg, Function.update_apply, rN, rN2, rM, rTmp, rW, rBm1,
    rTmp2, rPW, rP50, rIn, rDc, rP49, rCeil50, rTb, rOb, rTrials, rP15, rP8, rCeil15, rBase, rL, rA,
    rKk, rOne, rThree, rSix, rFifty, rC49, rn, ra, rk, c1, c3, c6, c50, c49,
    Nat.reduceEqDiff, ↓reduceIte] at gN2 gM gW gB gPW gIn gDc gTr gL gOb gTmp
  have eT : trials n = 4 * (n * n * ((n - 1) * (6 * (n - 1)) + 1)) *
      ((50 ^ n + 49 ^ n - 1) / 49 ^ n) * (6 * (n * n) + 6) := by
    simp only [trials, trialBlock, outerBlocks, outerCeil_eq, Bmax, Wmax]; ring
  refine ⟨v1, j1, e1, hj1, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, o1, f1⟩
  · simpa only [rN2] using gN2
  · simpa only [rM] using gM
  · simpa only [rW] using gW
  · simpa only [rBm1] using gB
  · simpa only [rPW] using gPW
  · simpa only [rIn] using gIn
  · simp only [rDc] at gDc ⊢; rw [gDc]
  · simp only [rTrials] at gTr ⊢; rw [gTr, eT]
  · simp only [rL] at gL ⊢; rw [gL, coinSpan, ceil15_eq]; ring
  · simp only [rOb] at gOb ⊢; rw [gOb, outerBlocks]; ring
  · simp only [rTmp] at gTmp ⊢; rw [gTmp, eT]

theorem pb_mono {x E F : ℕ} (h : x ≤ 2 ^ E) (hEF : E ≤ F) : x ≤ 2 ^ F :=
  h.trans (Nat.pow_le_pow_right (by norm_num) hEF)

theorem size_le_self' (x : ℕ) : x.size ≤ x := Nat.size_le.mpr Nat.lt_two_pow_self

theorem trials_le (n : ℕ) : trials n ≤ 2 ^ (100 * (n + 1) ^ 2) := by
  have eT : trials n = 4 * (n * n * ((n - 1) * (6 * (n - 1)) + 1)) *
      ((50 ^ n + 49 ^ n - 1) / 49 ^ n) * (6 * (n * n) + 6) := by
    simp only [trials, trialBlock, outerBlocks, outerCeil_eq, Bmax, Wmax]; ring
  rw [eT]
  apply pb_mono
  · (repeat' (first | apply pb_mul | apply pb_add | apply pb_sub | apply pb_div | apply pb_mod | apply pb_pow | apply pb_clog | assumption | apply pb_atom))
  · ring_nf; omega

theorem outerBlocks_le (n : ℕ) : outerBlocks n ≤ 2 ^ (100 * (n + 1) ^ 2) := by
  rw [outerBlocks]
  apply pb_mono
  · (repeat' (first | apply pb_mul | apply pb_add | apply pb_sub | apply pb_div | apply pb_mod | apply pb_pow | apply pb_clog | assumption | apply pb_atom))
  · ring_nf; omega

theorem coinSpan_le (A k n : ℕ) : coinSpan A k n ≤ 2 ^ (A.size + 200 * (n + 1) ^ 2 * (k + 1)) := by
  have hA : A ≤ 2 ^ A.size := pb_size A
  rw [coinSpan, ceil15_eq]
  apply pb_mono
  · (repeat' (first | apply pb_mul | apply pb_add | apply pb_sub | apply pb_div | apply pb_mod | apply pb_pow | apply pb_clog | assumption | apply pb_atom))
  · ring_nf; omega

theorem seedWidth_eq (n : ℕ) : seedWidth n = Nat.clog 2 (drawCount n) := by
  rw [seedWidth, card_draw]

theorem seedWidth_le (n : ℕ) : seedWidth n ≤ 2 ^ (100 * (n + 1) ^ 2) := by
  rw [seedWidth_eq]
  refine (clog_le_self' _).trans ((drawCount_lt n).le.trans (Nat.pow_le_pow_right (by norm_num) ?_))
  nlinarith

set_option maxHeartbeats 4000000 in
theorem paramsC2_run {τ : Tapes} {b : ℕ} (s : Store) {n Z O T S L : ℕ} (A k : ℕ)
    (rn : s.mem (cell rN) = n) (one : s.mem (cell rOne) = 1) (rz : s.mem (cell rTmp2) = Z)
    (ro : s.mem (cell rOb) = O) (rt : s.mem (cell rTrials) = T) (rs : s.mem (cell rSw) = S)
    (rl : s.mem (cell rL) = L)
    (hZ : Z ≤ 2 ^ (100 * (n + 1) ^ 2)) (hO : O ≤ 2 ^ (100 * (n + 1) ^ 2))
    (hT : T ≤ 2 ^ (100 * (n + 1) ^ 2)) (hS : S ≤ 2 ^ (100 * (n + 1) ^ 2))
    (hL : L ≤ 2 ^ (A.size + 200 * (n + 1) ^ 2 * (k + 1)))
    (fit : s.Fits b) (hb : 1000 * (n + 1) ^ 3 * (k + 1) + 2 * A.size ≤ b) :
    ∃ v j, Exec τ (fun w => w.Fits b) (circ paramsC2) s v j ∧
      j ≤ 17 * (b * (5 * b + 9) + 15) ∧
      v.mem (cell rR) = 2 * (Z + O) ∧ v.mem (cell rR2) = 2 * (2 * (Z + O)) ∧
      v.mem (cell rTapeBase) = T * S ∧ v.mem (cell rVB) = xBase + 128 * (n + 1) ^ 3 ∧
      v.mem (cell 103) = xBase + 128 * (n + 1) ^ 3 + n ∧
      v.mem (cell 102) = xBase + 128 * (n + 1) ^ 3 + n + L + 1 ∧
      v.mem (cell 105) = xBase ∧ v.mem (cell 110) = 1 ∧ v.mem (cell 111) = 0 ∧ v.out = s.out ∧
      (∀ a, 14 ≤ a → (∀ x ∈ paramsC2, a ≠ cell x.dst) → v.mem a = s.mem a) := by
  simp only [rN, rOne, rTmp2, rOb, rTrials, rSw, rL] at rn one rz ro rt rs rl
  obtain ⟨le2, key⟩ := budget_facts A hb
  ring_nf at key
  obtain ⟨v, j, e, hj, vals, o, f⟩ := circ_run (τ := τ) paramsC2 s fit le2 (by
    simp only [paramsC2, Circuit.width, Expression.width, Assignment.update, Expression.eval,
      Arithmetic.value, asg, Function.update_apply, rN, rTmp, rTmp2, rOb, rTrials, rSw, rL, rOne,
      rR, rR2, rTapeBase, rXmax, rVB, xBase, rn, one, rz, ro, rt, rs, rl,
      Nat.reduceEqDiff, ↓reduceIte, max_le_iff]
    repeat' apply And.intro
    all_goals first
      | exact Nat.zero_le _
      | (apply twice_le_pb; (· (repeat' (first | apply pb_mul | apply pb_add | apply pb_sub | apply pb_div | apply pb_mod | apply pb_pow | apply pb_clog | assumption | apply pb_atom))); (ring_nf; omega))
      | (apply size_le_pb; (· (repeat' (first | apply pb_mul | apply pb_add | apply pb_sub | apply pb_div | apply pb_mod | apply pb_pow | apply pb_clog | assumption | apply pb_atom))); (ring_nf; omega)))
  simp only [paramsC2, Circuit.multiplicity, Expression.multiplicity, asg] at hj
  have g := fun i => vals i
  have gR := g rR
  have gR2 := g rR2
  have gTB := g rTapeBase
  have gVB := g rVB
  have g103 := g 103
  have g102 := g 102
  have g105 := g 105
  have g110 := g 110
  have g111 := g 111
  simp only [paramsC2, Circuit.result, Assignment.update, Expression.eval,
    Arithmetic.value, asg, Function.update_apply, rN, rTmp, rTmp2, rOb, rTrials, rSw, rL, rOne,
    rR, rR2, rTapeBase, rXmax, rVB, rn, one, rz, ro, rt, rs, rl,
    Nat.reduceEqDiff, ↓reduceIte] at gR gR2 gTB gVB g103 g102 g105 g110 g111
  refine ⟨v, j, e, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, o, f⟩
  · simp only [rR] at gR ⊢; rw [gR]; ring
  · simp only [rR2] at gR2 ⊢; rw [gR2]; ring
  · simpa only [rTapeBase] using gTB
  · simp only [rVB] at gVB ⊢; rw [gVB]; ring
  · rw [g103]; ring
  · rw [g102]; ring
  · exact g105
  · exact g110
  · exact g111

theorem steps_total (n k b j1 j2 j3 j4 c1 c2 : ℕ)
    (hj1 : j1 ≤ (n * n + 7 * n + k + 40) * (b * (5 * b + 9) + 15))
    (hj2 : j2 ≤ 4 * c1 + 4 + 2 * (b * (5 * b + 9) + 15))
    (hj3 : j3 ≤ 4 * c2 + 4 + 2 * (b * (5 * b + 9) + 15))
    (hj4 : j4 ≤ 17 * (b * (5 * b + 9) + 15)) (hc1 : c1 ≤ b) (hc2 : c2 ≤ b) :
    j1 + (j2 + (j3 + j4)) ≤ 10 ^ 4 * (n + 1) ^ 2 * (k + 1) * (b + 1) ^ 2 := by
  have hQ : b * (5 * b + 9) + 15 ≤ 15 * (b + 1) ^ 2 := by nlinarith
  have hM : (n * n + 7 * n + k + 61) * 15 + 8 ≤ 10 ^ 4 * (n + 1) ^ 2 * (k + 1) := by
    nlinarith [Nat.zero_le (n * k), Nat.zero_le (n * n * k)]
  have hb1 : 8 * b + 8 ≤ 8 * (b + 1) ^ 2 := by nlinarith
  have split : (n * n + 7 * n + k + 61) * (b * (5 * b + 9) + 15) =
      (n * n + 7 * n + k + 40) * (b * (5 * b + 9) + 15) + 21 * (b * (5 * b + 9) + 15) := by ring
  calc j1 + (j2 + (j3 + j4))
      ≤ (n * n + 7 * n + k + 61) * (b * (5 * b + 9) + 15) + (8 * b + 8) := by omega
    _ ≤ (n * n + 7 * n + k + 61) * (15 * (b + 1) ^ 2) + 8 * (b + 1) ^ 2 :=
        Nat.add_le_add (Nat.mul_le_mul_left _ hQ) hb1
    _ = ((n * n + 7 * n + k + 61) * 15 + 8) * (b + 1) ^ 2 := by ring
    _ ≤ 10 ^ 4 * (n + 1) ^ 2 * (k + 1) * (b + 1) ^ 2 := Nat.mul_le_mul_right _ hM

end DirectedHamiltonicity.Main.CycleHost


-- ===== Solutions/Dev/FinalArithA.lean =====

set_option autoImplicit false

namespace DirectedHamiltonicity.Main.CycleHost

open DirectedHamiltonicity.Main.CycleReduction

theorem fa_sw_le (n : ℕ) : seedWidth n ≤ 16 * (n + 1) ^ 2 := by
  rw [seedWidth_eq]
  exact Nat.clog_le_of_le_pow (drawCount_lt n).le

theorem fa_tsize_le (n : ℕ) : (trials n).size ≤ 100 * (n + 1) ^ 2 + 1 :=
  Nat.size_le.mpr ((trials_le n).trans_lt (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self _)))

theorem fa_r_le (n : ℕ) : majorityHalf n ≤ 212 * (n + 1) ^ 2 + 2 := by
  have h1 := fa_tsize_le n
  have h2 : outerBlocks n ≤ 6 * (n + 1) ^ 2 := by
    rw [outerBlocks]; nlinarith
  rw [majorityHalf]; omega

theorem fa_t2_le (n : ℕ) : (2 * trials n + 2).size ≤ 100 * (n + 1) ^ 2 + 3 :=
  twice_le_pb (trials_le n) le_rfl

theorem fa_big_eq (n A k : ℕ) : BIGv n A k = (300 + 128 * (n + 1) ^ 3 + n + 1) + coinSpan A k n := by
  unfold BIGv LOGv VBv xBase; omega

theorem fa_width (n A k : ℕ) :
    hostWidth n A k ≤ (4 * A.size + 2000 * (k + 1) + 2000) * (n + 1) ^ 3 := by
  have hsw := fa_sw_le n
  have hr := fa_r_le n
  have ht2 := fa_t2_le n
  have hT := trials_le n
  have hL := coinSpan_le A k n
  have hqc : (n + 1) ^ 2 ≤ (n + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hnc : n + 1 ≤ (n + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  have hswp : seedWidth n ≤ 2 ^ (16 * (n + 1) ^ 2) := hsw.trans (pb_atom _)
  have hrp : 2 * majorityHalf n + 2 ≤ 2 ^ (2 * majorityHalf n + 2) := pb_atom _
  have hap : 300 + 128 * (n + 1) ^ 3 + n + 1 ≤ 2 ^ (300 + 128 * (n + 1) ^ 3 + n + 1) := pb_atom _
  have h2 : (2 : ℕ) ≤ 2 ^ 2 := by norm_num
  have hBig := pb_add (pb_add (pb_add hap hL) (pb_mul hT hswp)) (pb_mul hrp (pb_add hL h2))
  rw [← fa_big_eq] at hBig
  have hs := size_le_pb hBig le_rfl
  have hAc : A.size ≤ A.size * (n + 1) ^ 3 := Nat.le_mul_of_pos_right _ (pow_pos (Nat.succ_pos n) 3)
  have hqk : (n + 1) ^ 2 * (k + 1) ≤ (n + 1) ^ 3 * (k + 1) := Nat.mul_le_mul_right _ hqc
  have hk1 : (n + 1) ^ 3 ≤ (n + 1) ^ 3 * (k + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have e2 : (4 * A.size + 2000 * (k + 1) + 2000) * (n + 1) ^ 3 =
      4 * (A.size * (n + 1) ^ 3) + 2000 * ((n + 1) ^ 3 * (k + 1)) + 2000 * (n + 1) ^ 3 := by ring
  have e3 : 1000 * (n + 1) ^ 3 * (k + 1) = 1000 * ((n + 1) ^ 3 * (k + 1)) := by ring
  have e4 : 200 * (n + 1) ^ 2 * (k + 1) = 200 * ((n + 1) ^ 2 * (k + 1)) := by ring
  rw [e4] at hs
  unfold hostWidth
  rw [e2, e3]
  generalize (BIGv n A k + trials n * seedWidth n + (2 * majorityHalf n + 2) * (coinSpan A k n + 2)).size = sz at hs ⊢
  generalize (2 * trials n + 2).size = t2 at ht2 ⊢
  generalize seedWidth n = sw at hsw ⊢
  generalize majorityHalf n = rr at hr hs
  generalize A.size * (n + 1) ^ 3 = Q1 at hAc ⊢
  generalize (n + 1) ^ 3 * (k + 1) = Q2 at hqk hk1 ⊢
  generalize (n + 1) ^ 2 * (k + 1) = Q3 at hqk hs
  generalize (n + 1) ^ 3 = c at *
  generalize (n + 1) ^ 2 = q at *
  generalize A.size = As at *
  omega


theorem fa_basic (b J C k B : ℕ) (hB : b + J + C + k + 1 ≤ B) :
    (b * (5 * b + 9) + 15) * (4 * b + 4 * J + 4) ≤ 60 * B ^ 3 := by
  have hb : b + 1 ≤ B := by omega
  have hX : 4 * b + 4 * J + 4 ≤ 4 * B := by omega
  have hP : b * (5 * b + 9) + 15 ≤ 15 * B ^ 2 := by
    have : (b + 1) ^ 2 ≤ B ^ 2 := Nat.pow_le_pow_left hb 2
    nlinarith
  calc _ ≤ (15 * B ^ 2) * (4 * B) := Nat.mul_le_mul hP hX
    _ = 60 * B ^ 3 := by ring

theorem fa_s1 (n A k b J C B : ℕ) (hB : b + J + C + k + 1 ≤ B) :
    runCost n A k b J C + 7 * J + 7 * b + 3 ≤ 1000 * B ^ 3 * (coinSpan A k n + 1) := by
  unfold runCost
  generalize coinSpan A k n = L
  have hPX := fa_basic b J C k B hB
  have h1 : C * (L + 1) * (b + J + 1) ≤ B * (L + 1) * B :=
    Nat.mul_le_mul (Nat.mul_le_mul_right _ (by omega)) (by omega)
  have hB1 : 1 ≤ B := by omega
  have h2 : B ^ 3 ≤ B ^ 3 * (L + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have h3 : B * (L + 1) * B ≤ B ^ 3 * (L + 1) := by
    have : B ^ 2 ≤ B ^ 3 := Nat.pow_le_pow_right hB1 (by norm_num)
    calc B * (L + 1) * B = B ^ 2 * (L + 1) := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ this
  have h4 : B ≤ B ^ 3 := Nat.le_self_pow (by norm_num) _
  have h5 : 15 * J + 15 * b + 10 ≤ 25 * B := by omega
  linarith

theorem fa_s2 (n A k b J C B : ℕ) (hB : b + J + C + k + 1 ≤ B) :
    votesBound n A k b J C ≤
      2000 * B ^ 3 * ((2 * majorityHalf n + 1) * (seedWidth n + coinSpan A k n + 1)) := by
  have s1 := fa_s1 n A k b J C B hB
  unfold votesBound
  generalize runCost n A k b J C = R at s1 ⊢
  generalize coinSpan A k n = L at s1 ⊢
  generalize seedWidth n = sw
  generalize majorityHalf n = r
  have hPX := fa_basic b J C k B hB
  have h1 := Nat.mul_le_mul_left (2 * r + 1) s1
  have h2 : (2 * r + 1) * (1000 * B ^ 3 * (L + 1)) ≤ 1000 * (B ^ 3 * ((2 * r + 1) * (sw + L + 1))) := by
    calc (2 * r + 1) * (1000 * B ^ 3 * (L + 1)) = 1000 * (B ^ 3 * ((2 * r + 1) * (L + 1))) := by ring
      _ ≤ _ := by gcongr; omega
  have h3 : B ^ 3 ≤ B ^ 3 * ((2 * r + 1) * (sw + L + 1)) :=
    Nat.le_mul_of_pos_right _ (by positivity)
  have h4 : B ≤ B ^ 3 := Nat.le_self_pow (by norm_num) _
  have h5 : 3 * J + 2 * b + 1 ≤ 3 * B := by omega
  have e : 2000 * B ^ 3 * ((2 * r + 1) * (sw + L + 1)) = 2000 * (B ^ 3 * ((2 * r + 1) * (sw + L + 1))) := by ring
  rw [e]
  generalize B ^ 3 * ((2 * r + 1) * (sw + L + 1)) = G at h2 h3 ⊢
  generalize (2 * r + 1) * (R + 7 * J + 7 * b + 3) = V at h1 ⊢
  linarith

theorem fa_s3 (n A k b J C B : ℕ) (hB : b + J + C + k + 1 ≤ B) :
    trialBound n A k b J C + 7 * J + 7 * b + 3 ≤
      10 ^ 10 * (B ^ 4 * (n + 1) ^ 6 * ((2 * majorityHalf n + 1) * (seedWidth n + coinSpan A k n + 1))) := by
  have s2 := fa_s2 n A k b J C B hB
  unfold trialBound
  generalize votesBound n A k b J C = V at s2 ⊢
  generalize coinSpan A k n = L at s2 ⊢
  generalize seedWidth n = sw at s2 ⊢
  generalize majorityHalf n = r at s2 ⊢
  have hB1 : 1 ≤ B := by omega
  have hb : b + 1 ≤ B := by omega
  have hX : 4 * b + 4 * J + 4 ≤ 4 * B := by omega
  have hG1 : 1 ≤ (2 * r + 1) * (sw + L + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hB34 : B ^ 3 ≤ B ^ 4 := Nat.pow_le_pow_right hB1 (by norm_num)
  have hZ : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have hBM : B ^ 3 ≤ B ^ 4 * (n + 1) ^ 6 := hB34.trans (Nat.le_mul_of_pos_right _ hZ)
  have h1 : 10 ^ 9 * (n + 1) ^ 6 * (b + 1) ^ 2 * (sw + 1) * (4 * b + 4 * J + 4) ≤
      4 * 10 ^ 9 * (B ^ 4 * (n + 1) ^ 6 * ((2 * r + 1) * (sw + L + 1))) := by
    calc 10 ^ 9 * (n + 1) ^ 6 * (b + 1) ^ 2 * (sw + 1) * (4 * b + 4 * J + 4)
        ≤ 10 ^ 9 * (n + 1) ^ 6 * B ^ 2 * ((2 * r + 1) * (sw + L + 1)) * (4 * B) := by
          gcongr
          calc sw + 1 ≤ sw + L + 1 := by omega
            _ ≤ _ := Nat.le_mul_of_pos_left _ (by omega)
      _ = 4 * 10 ^ 9 * (B ^ 3 * (n + 1) ^ 6 * ((2 * r + 1) * (sw + L + 1))) := by ring
      _ ≤ _ := by gcongr
  have h2 : 2000 * B ^ 3 * ((2 * r + 1) * (sw + L + 1)) ≤
      2000 * (B ^ 4 * (n + 1) ^ 6 * ((2 * r + 1) * (sw + L + 1))) := by
    rw [mul_assoc]; gcongr
  have h3 : B ≤ B ^ 4 * (n + 1) ^ 6 * ((2 * r + 1) * (sw + L + 1)) :=
    (Nat.le_self_pow (by norm_num) B).trans (hBM.trans (Nat.le_mul_of_pos_right _ hG1))
  have h5 : 7 * J + 7 * b + 3 ≤ 10 * B := by omega
  generalize B ^ 4 * (n + 1) ^ 6 * ((2 * r + 1) * (sw + L + 1)) = G at h1 h2 h3 ⊢
  generalize 10 ^ 9 * (n + 1) ^ 6 * (b + 1) ^ 2 * (sw + 1) * (4 * b + 4 * J + 4) = E at h1 ⊢
  generalize 2000 * B ^ 3 * ((2 * r + 1) * (sw + L + 1)) = E2 at h2 s2
  omega

theorem fa_s4 (n A k b J C B : ℕ) (hB : b + J + C + k + 1 ≤ B) :
    decideBound n A k b J C ≤
      2 * 10 ^ 10 * (B ^ 4 * (n + 1) ^ 6 * ((trials n + 1) * (2 * majorityHalf n + 1) *
        (seedWidth n + coinSpan A k n + 1))) := by
  have s3 := fa_s3 n A k b J C B hB
  unfold decideBound
  generalize trialBound n A k b J C = V at s3 ⊢
  generalize coinSpan A k n = L at s3 ⊢
  generalize seedWidth n = sw at s3 ⊢
  generalize majorityHalf n = r at s3 ⊢
  generalize trials n = T
  have hPX := fa_basic b J C k B hB
  have hB1 : 1 ≤ B := by omega
  have hB34 : B ^ 3 ≤ B ^ 4 := Nat.pow_le_pow_right hB1 (by norm_num)
  have hZ : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have hR1 : 1 ≤ (T + 1) * (2 * r + 1) * (sw + L + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have h3 : B ^ 3 ≤ B ^ 4 * (n + 1) ^ 6 * ((T + 1) * (2 * r + 1) * (sw + L + 1)) :=
    (hB34.trans (Nat.le_mul_of_pos_right _ hZ)).trans (Nat.le_mul_of_pos_right _ hR1)
  have h1 := Nat.mul_le_mul_left (T + 1) s3
  have e : (T + 1) * (10 ^ 10 * (B ^ 4 * (n + 1) ^ 6 * ((2 * r + 1) * (sw + L + 1)))) =
      10 ^ 10 * (B ^ 4 * (n + 1) ^ 6 * ((T + 1) * (2 * r + 1) * (sw + L + 1))) := by ring
  rw [e] at h1
  have e2 : 2 * (b * (5 * b + 9) + 15) * (4 * b + 4 * J + 4) =
      2 * ((b * (5 * b + 9) + 15) * (4 * b + 4 * J + 4)) := by ring
  rw [e2]
  generalize B ^ 4 * (n + 1) ^ 6 * ((T + 1) * (2 * r + 1) * (sw + L + 1)) = G at h1 h3 ⊢
  generalize (b * (5 * b + 9) + 15) * (4 * b + 4 * J + 4) = P at hPX ⊢
  generalize (T + 1) * (V + 7 * J + 7 * b + 3) = W at h1 ⊢
  generalize B ^ 3 = B3 at hPX h3
  omega

theorem fa_s5 (n A k b J C B : ℕ) (hB : b + J + C + k + 1 ≤ B) :
    iterBound n A k b J C + 7 * J + 7 * b + 3 ≤
      3 * 10 ^ 10 * (B ^ 4 * (n + 1) ^ 6 * ((trials n + 1) * (2 * majorityHalf n + 1) *
        (seedWidth n + coinSpan A k n + 1))) := by
  have s4 := fa_s4 n A k b J C B hB
  unfold iterBound
  have hR1 : 1 ≤ (trials n + 1) * (2 * majorityHalf n + 1) * (seedWidth n + coinSpan A k n + 1) :=
    Nat.one_le_iff_ne_zero.mpr (by positivity)
  generalize decideBound n A k b J C = V at s4 ⊢
  generalize (trials n + 1) * (2 * majorityHalf n + 1) * (seedWidth n + coinSpan A k n + 1) = R at s4 hR1 ⊢
  have hPX := fa_basic b J C k B hB
  have hB1 : 1 ≤ B := by omega
  have hB34 : B ^ 3 ≤ B ^ 4 := Nat.pow_le_pow_right hB1 (by norm_num)
  have hZ : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h1 : (n + 1) ^ 2 * ((b * (5 * b + 9) + 15) * (4 * b + 4 * J + 4)) ≤
      60 * (B ^ 4 * (n + 1) ^ 6 * R) := by
    calc (n + 1) ^ 2 * ((b * (5 * b + 9) + 15) * (4 * b + 4 * J + 4)) ≤ (n + 1) ^ 6 * (60 * B ^ 4) :=
          Nat.mul_le_mul hZ (hPX.trans (Nat.mul_le_mul_left 60 hB34))
      _ = 60 * (B ^ 4 * (n + 1) ^ 6 * 1) := by ring
      _ ≤ _ := Nat.mul_le_mul_left 60 (Nat.mul_le_mul_left _ hR1)
  have h2 : B ≤ B ^ 4 * (n + 1) ^ 6 * R := by
    calc B ≤ B ^ 4 := Nat.le_self_pow (by norm_num) B
      _ = B ^ 4 * 1 * 1 := by ring
      _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.one_le_pow _ _ (by omega))) hR1
  have e : 100 * (n + 1) ^ 2 * (b * (5 * b + 9) + 15) * (4 * b + 4 * J + 4) =
      100 * ((n + 1) ^ 2 * ((b * (5 * b + 9) + 15) * (4 * b + 4 * J + 4))) := by ring
  rw [e]
  generalize B ^ 4 * (n + 1) ^ 6 * R = G at h1 h2 s4 ⊢
  generalize (n + 1) ^ 2 * ((b * (5 * b + 9) + 15) * (4 * b + 4 * J + 4)) = E at h1 ⊢
  omega

theorem fa_s6 (n A k b J C B : ℕ) (hB : b + J + C + k + 1 ≤ B) :
    pruneBound n A k b J C ≤ 4 * 10 ^ 10 * (B ^ 4 * (n + 1) ^ 6 * searchWork A k n) := by
  have s5 := fa_s5 n A k b J C B hB
  have eS : searchWork A k n = (n * n + 1) * ((trials n + 1) * (2 * majorityHalf n + 1) *
      (seedWidth n + coinSpan A k n + 1)) := by unfold searchWork; ring
  rw [eS]
  unfold pruneBound
  have hR1 : 1 ≤ (trials n + 1) * (2 * majorityHalf n + 1) * (seedWidth n + coinSpan A k n + 1) :=
    Nat.one_le_iff_ne_zero.mpr (by positivity)
  generalize iterBound n A k b J C = V at s5 ⊢
  generalize (trials n + 1) * (2 * majorityHalf n + 1) * (seedWidth n + coinSpan A k n + 1) = R at s5 hR1 ⊢
  have hPX := fa_basic b J C k B hB
  have hB1 : 1 ≤ B := by omega
  have h1 := Nat.mul_le_mul_left (n * n + 1) s5
  have e : (n * n + 1) * (3 * 10 ^ 10 * (B ^ 4 * (n + 1) ^ 6 * R)) =
      3 * 10 ^ 10 * (B ^ 4 * (n + 1) ^ 6 * ((n * n + 1) * R)) := by ring
  rw [e] at h1
  have h2 : 60 * B ^ 3 ≤ 60 * (B ^ 4 * (n + 1) ^ 6 * ((n * n + 1) * R)) := by
    calc 60 * B ^ 3 ≤ 60 * (B ^ 4 * 1 * (1 * 1)) := by
          rw [mul_one, mul_one, mul_one]
          exact Nat.mul_le_mul_left 60 (Nat.pow_le_pow_right hB1 (by norm_num))
      _ ≤ _ := Nat.mul_le_mul_left 60 (Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.one_le_pow _ _ (by omega)))
          (Nat.mul_le_mul (by omega) hR1))
  generalize B ^ 4 * (n + 1) ^ 6 * ((n * n + 1) * R) = G at h1 h2 ⊢
  generalize (b * (5 * b + 9) + 15) * (4 * b + 4 * J + 4) = P at hPX ⊢
  generalize (n * n + 1) * (V + 7 * J + 7 * b + 3) = W at h1 ⊢
  omega

theorem fa_s7 (n A k J C B : ℕ) (hB : hostWidth n A k + J + C + k + 1 ≤ B) :
    mainBound n A k J C + 1 ≤ 10 ^ 11 * (B ^ 4 * (n + 1) ^ 6 * searchWork A k n) := by
  simp only [mainBound]
  have s6 := fa_s6 n A k (hostWidth n A k) J C B hB
  have hS : 1 ≤ searchWork A k n := Nat.one_le_iff_ne_zero.mpr (by unfold searchWork; positivity)
  generalize hostWidth n A k = b at hB s6 ⊢
  generalize pruneBound n A k b J C = V at s6 ⊢
  generalize searchWork A k n = S at s6 hS ⊢
  have hB1 : 1 ≤ B := by omega
  have hb : b + 1 ≤ B := by omega
  have hk : k + 1 ≤ B := by omega
  have hX : 4 * b + 4 * J + 4 ≤ 4 * B := by omega
  have hZ1 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hP : b * (5 * b + 9) + 15 ≤ 15 * B ^ 2 := by
    have : (b + 1) ^ 2 ≤ B ^ 2 := Nat.pow_le_pow_left hb 2
    nlinarith
  have hb2 : (b + 1) ^ 2 ≤ B ^ 2 := Nat.pow_le_pow_left hb 2
  have hZ24 : (n + 1) ^ 2 ≤ (n + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hZ1' : 1 ≤ (n + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
  have hB23 : B ^ 2 ≤ B ^ 3 := Nat.pow_le_pow_right hB1 (by norm_num)
  have hB13 : B ≤ B ^ 3 := Nat.le_self_pow (by norm_num) B
  have hB03 : 1 ≤ B ^ 3 := Nat.one_le_pow _ _ hB1
  -- the inner sum is at most 2 * 10 ^ 6 * (B ^ 3 * (n + 1) ^ 4)
  have i1 : 20 * (b * (5 * b + 9) + 15) ≤ 300 * (B ^ 3 * (n + 1) ^ 4) := by
    calc 20 * (b * (5 * b + 9) + 15) ≤ 300 * (B ^ 3 * 1) := by rw [mul_one]; omega
      _ ≤ _ := by gcongr
  have i2 : 10 * (b + 1) ≤ 10 * (B ^ 3 * (n + 1) ^ 4) := by
    calc 10 * (b + 1) ≤ 10 * (B ^ 3 * 1) := by rw [mul_one]; omega
      _ ≤ _ := by gcongr
  have i3 : 10 ^ 4 * (n + 1) ^ 2 * (k + 1) * (b + 1) ^ 2 ≤ 10 ^ 4 * (B ^ 3 * (n + 1) ^ 4) := by
    calc 10 ^ 4 * (n + 1) ^ 2 * (k + 1) * (b + 1) ^ 2 ≤ 10 ^ 4 * (n + 1) ^ 4 * B * B ^ 2 := by
          gcongr
      _ = 10 ^ 4 * (B ^ 3 * (n + 1) ^ 4) := by ring
  have i4 : 100 * (n + 1) ^ 2 ≤ 100 * (B ^ 3 * (n + 1) ^ 4) := by
    calc 100 * (n + 1) ^ 2 ≤ 100 * (1 * (n + 1) ^ 4) := by rw [one_mul]; omega
      _ ≤ _ := by gcongr
  have i5 : 10 ^ 6 * (n + 1) ^ 4 * (b + 1) ^ 2 ≤ 10 ^ 6 * (B ^ 3 * (n + 1) ^ 4) := by
    calc 10 ^ 6 * (n + 1) ^ 4 * (b + 1) ^ 2 ≤ 10 ^ 6 * (n + 1) ^ 4 * B ^ 3 := by gcongr; omega
      _ = _ := by ring
  have i6 : 10 ≤ 10 * (B ^ 3 * (n + 1) ^ 4) := by
    have : 1 ≤ B ^ 3 * (n + 1) ^ 4 := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  have hin : 20 * (b * (5 * b + 9) + 15) + 10 * (b + 1) + 10 ^ 4 * (n + 1) ^ 2 * (k + 1) * (b + 1) ^ 2 +
      100 * (n + 1) ^ 2 + 10 ^ 6 * (n + 1) ^ 4 * (b + 1) ^ 2 + 10 ≤ 2 * 10 ^ 6 * (B ^ 3 * (n + 1) ^ 4) := by
    generalize B ^ 3 * (n + 1) ^ 4 = G at i1 i2 i3 i4 i5 i6 ⊢
    omega
  have hmul : (20 * (b * (5 * b + 9) + 15) + 10 * (b + 1) + 10 ^ 4 * (n + 1) ^ 2 * (k + 1) * (b + 1) ^ 2 +
      100 * (n + 1) ^ 2 + 10 ^ 6 * (n + 1) ^ 4 * (b + 1) ^ 2 + 10) * (4 * b + 4 * J + 4) ≤
      8 * 10 ^ 6 * (B ^ 4 * (n + 1) ^ 6 * S) := by
    calc _ ≤ (2 * 10 ^ 6 * (B ^ 3 * (n + 1) ^ 4)) * (4 * B) := Nat.mul_le_mul hin hX
      _ = 8 * 10 ^ 6 * (B ^ 4 * (n + 1) ^ 4 * 1) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.mul_le_mul_left _
          (Nat.pow_le_pow_right (Nat.succ_pos n) (by norm_num))) hS)
  have h1 : 1 ≤ B ^ 4 * (n + 1) ^ 6 * S := Nat.one_le_iff_ne_zero.mpr (by positivity)
  generalize B ^ 4 * (n + 1) ^ 6 * S = G at hmul h1 s6 ⊢
  generalize (20 * (b * (5 * b + 9) + 15) + 10 * (b + 1) + 10 ^ 4 * (n + 1) ^ 2 * (k + 1) * (b + 1) ^ 2 +
      100 * (n + 1) ^ 2 + 10 ^ 6 * (n + 1) ^ 4 * (b + 1) ^ 2 + 10) * (4 * b + 4 * J + 4) = E at hmul ⊢
  omega

end DirectedHamiltonicity.Main.CycleHost


-- ===== Solutions/Dev/FinalArith.lean =====

set_option autoImplicit false

namespace DirectedHamiltonicity.Main.CycleHost

open DirectedHamiltonicity.Main.CycleReduction

theorem finalBound_nat (A k J C n : ℕ) :
    mainBound n A k J C + 1 ≤
      10 ^ 11 * (4 * A.size + 2000 * (k + 1) + 2000 + J + C + k + 1) ^ 4 * searchWork A k n *
        (n + 1) ^ 18 := by
  have hw := fa_width n A k
  have h1 : 1 ≤ (n + 1) ^ 3 := Nat.one_le_pow _ _ (Nat.succ_pos n)
  have hJ : J + C + k + 1 ≤ (J + C + k + 1) * (n + 1) ^ 3 := Nat.le_mul_of_pos_right _ h1
  have hB : hostWidth n A k + J + C + k + 1 ≤
      (4 * A.size + 2000 * (k + 1) + 2000 + J + C + k + 1) * (n + 1) ^ 3 := by
    have e : (4 * A.size + 2000 * (k + 1) + 2000 + J + C + k + 1) * (n + 1) ^ 3 =
        (4 * A.size + 2000 * (k + 1) + 2000) * (n + 1) ^ 3 + (J + C + k + 1) * (n + 1) ^ 3 := by ring
    rw [e]; omega
  have h := fa_s7 n A k J C _ hB
  refine h.trans (le_of_eq ?_)
  ring

theorem finalBound_holds (A k J C : ℕ) : FinalBound A k J C := by
  refine ⟨((10 ^ 11 * (4 * A.size + 2000 * (k + 1) + 2000 + J + C + k + 1) ^ 4 : ℕ) : ℝ), 18,
    by positivity, fun n => ?_⟩
  have h := finalBound_nat A k J C n
  exact_mod_cast h

end DirectedHamiltonicity.Main.CycleHost


section SolutionBlock
open TargetedSamplers DirectedHamiltonicity.Main.CycleReduction

theorem solution (Q : Program) (A k : ℕ)
    (bounded : QueryTime Q A k) : ExecutesSearch Q A k :=
  DirectedHamiltonicity.Main.CycleHost.execute_of_bound Q A k bounded
    (fun J C => DirectedHamiltonicity.Main.CycleHost.finalBound_holds A k J C)

end SolutionBlock
