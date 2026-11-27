-- Prove2me | solution 1 for DirectedHamiltonicity.Main.CycleHost.buildX_exec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T04:33:18.253509+00:00
-- url     : https://prove2.me/submissions/b1271728-3f72-4f46-a701-8080e49eaeb0

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


-- ===== Solutions/Dev/BuildXA.lean =====

set_option autoImplicit false

namespace DirectedHamiltonicity.Main.CycleHost

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word
open TargetedSamplers.Structured.Interp DirectedHamiltonicity.Main.CycleReduction

theorem bits_pos (k : ℕ) (hk : 0 < k) : k.bits = decide (k % 2 = 1) :: (k / 2).bits := by
  have hk2 : k = 2 * (k / 2) + k % 2 := (Nat.div_add_mod k 2).symm
  rcases Nat.mod_two_eq_zero_or_one k with h | h
  · have : k / 2 ≠ 0 := by omega
    rw [h] at hk2
    conv_lhs => rw [hk2]
    simp [h, this]
  · rw [h] at hk2
    conv_lhs => rw [hk2]
    simp [h]

/-- Appending `pre` at the cursor, dirtying registers `D`. -/
def Step (pre : List Bool) (D : List ℕ) (s t : Store) : Prop :=
  t.out = s.out ∧ t.mem (cell rXc) = s.mem (cell rXc) + pre.length ∧
  (∀ i (hi : i < pre.length), t.mem (xBase + s.mem (cell rXc) + i) = (pre[i]'hi).toNat) ∧
  ∀ a, 14 ≤ a → (∀ d ∈ D, a ≠ cell d) →
    (a < xBase + s.mem (cell rXc) ∨ xBase + s.mem (cell rXc) + pre.length ≤ a) → t.mem a = s.mem a

theorem Step.refl (D : List ℕ) (s : Store) : Step [] D s s :=
  ⟨rfl, by simp, fun i hi => by simp at hi, fun _ _ _ _ => rfl⟩

theorem Step.trans {p q : List Bool} {D : List ℕ} {s m t : Store} (hD : ∀ d ∈ D, cell d < xBase)
    (h1 : Step p D s m) (h2 : Step q D m t) : Step (p ++ q) D s t := by
  obtain ⟨o1, c1, b1, f1⟩ := h1
  obtain ⟨o2, c2, b2, f2⟩ := h2
  refine ⟨o2.trans o1, by rw [c2, c1, List.length_append]; omega, ?_, ?_⟩
  · intro i hi
    by_cases hp : i < p.length
    · rw [List.getElem_append_left hp, ← b1 i hp]
      apply f2 _ (by unfold xBase; omega)
      · intro d hd; have := hD d hd; omega
      · left; rw [c1]; omega
    · have := b2 (i - p.length) (by simp at hi; omega)
      rw [List.getElem_append_right (by omega), ← this, c1]
      congr 1; omega
  · intro a ha hd hout
    rw [f2 a ha hd (by rw [c1]; simp at hout; omega), f1 a ha hd (by simp at hout; omega)]

theorem Step.mono {p : List Bool} {D E : List ℕ} {s t : Store} (h : Step p D s t) (sub : ∀ d ∈ D, d ∈ E) :
    Step p E s t :=
  ⟨h.1, h.2.1, h.2.2.1, fun a ha hd hout => h.2.2.2 a ha (fun d hdD => hd d (sub d hdD)) hout⟩

theorem Step.write {p : List Bool} {D : List ℕ} {s t : Store} (h : Step p D s t) (d v : ℕ)
    (hd : d ∈ D) (hx : d ≠ rXc) (hlow : cell d < xBase) : Step p D s (t.write (cell d) v) := by
  obtain ⟨o, c, bt, f⟩ := h
  have ne : cell rXc ≠ cell d := by simp [cell]; omega
  refine ⟨o, by simp [Store.write, Function.update_of_ne ne, c], ?_, ?_⟩
  · intro i hi
    have : xBase + s.mem (cell rXc) + i ≠ cell d := by omega
    simp [Store.write, Function.update_of_ne this, bt i hi]
  · intro a ha hdd hout
    have : a ≠ cell d := hdd d hd
    simp [Store.write, Function.update_of_ne this, f a ha hdd hout]

/-- Cost unit of an arithmetic call. -/
def Qc (b : ℕ) : ℕ := b * (5 * b + 9) + 15

/-- Generic circuit run with frame. -/
theorem circ_run {τ : Tapes} {b : ℕ} (as : List Assignment) (D : List ℕ)
    (hD : ∀ x ∈ as, x.dst ∈ D) (hX : ∀ x ∈ as, x.dst ≠ rXc) (s : Store) (fit : s.Fits b) (hb : 2 ≤ b)
    (w : Circuit.width (fun i => s.mem (cell i)) as ≤ b) :
    ∃ t j, Exec τ (fun w => w.Fits b) (circ as) s t j ∧
      j ≤ Circuit.multiplicity (fun i => s.mem (cell i)) as * Qc b ∧
      (∀ i, t.mem (cell i) = Circuit.result (fun i => s.mem (cell i)) as i) ∧ Step [] D s t := by
  obtain ⟨t, j, ex, hj, rep, out⟩ := Circuit.exec (τ := τ) as _ s (fun i => rfl) fit hb w
  refine ⟨t, j, ex, hj.trans (Circuit.steps_le as _ b w), rep, out, ?_, fun i hi => by simp at hi, ?_⟩
  · rw [rep, Circuit.result_untouched as _ _ (fun x hx => (hX x hx).symm)]; simp
  · intro a ha hd _
    have e : a = cell (a - 14) := by simp [cell]; omega
    rw [e, rep, Circuit.result_untouched]
    intro x hx h
    exact hd x.dst (hD x hx) (by rw [e, h])

theorem putBit_step {τ : Tapes} {b : ℕ} (val : ℕ) (bv : Bool) (D : List ℕ)
    (hA : rAddr ∈ D) (hXD : rXc ∈ D) (hvA : val ≠ rAddr) (s : Store) (fit : s.Fits b)
    (hval : s.mem (cell val) = bv.toNat) (hone : s.mem (cell rOne) = 1)
    (hw : (xBase + s.mem (cell rXc) + 1).size ≤ b) :
    ∃ t, Exec τ (fun w => w.Fits b) (putBit val) s t 4 ∧ Step [bv] D s t := by
  obtain ⟨c, hc⟩ : ∃ c, s.mem (cell rXc) = c := ⟨_, rfl⟩
  rw [hc] at hw
  have sz1 : (xBase).size ≤ b := (Nat.size_le_size (by omega)).trans hw
  have sz2 : (xBase + c).size ≤ b := (Nat.size_le_size (by omega)).trans hw
  have sz3 : (c + 1).size ≤ b := (Nat.size_le_size (by omega)).trans hw
  have szv : (bv.toNat).size ≤ b := (Nat.size_le_size (by cases bv <;> simp)).trans hw
  have nAX : cell rAddr ≠ cell rXc := by decide
  have nAv : cell val ≠ cell rAddr := by simp [cell]; exact hvA
  have nXA : xBase + c ≠ cell rXc := by simp [xBase, cell, rXc]; omega
  have nXo : xBase + c ≠ cell rOne := by simp [xBase, cell, rOne]; omega
  let s1 := s.write (cell rAddr) xBase
  let s2 := s1.write (cell rAddr) (xBase + c)
  let s3 := s2.write (xBase + c) bv.toNat
  let s4 := s3.write (cell rXc) (c + 1)
  have f1 : s1.Fits b := Store.write_fits fit _ sz1
  have f2 : s2.Fits b := Store.write_fits f1 _ sz2
  have f3 : s3.Fits b := Store.write_fits f2 _ szv
  have f4 : s4.Fits b := Store.write_fits f3 _ sz3
  have e1 : (Op.const (cell rAddr) xBase).eval τ s = s1 := rfl
  have e2 : (Op.add (cell rAddr) (cell rAddr) (cell rXc)).eval τ s1 = s2 := by
    simp [Op.eval, s2, s1, Store.write, Function.update_of_ne nAX.symm, hc]
  have e3 : (Op.store (cell rAddr) (cell val)).eval τ s2 = s3 := by
    simp [Op.eval, s3, s2, s1, Store.write, Function.update_of_ne nAv, hval]
  have e4 : (Op.add (cell rXc) (cell rXc) (cell rOne)).eval τ s3 = s4 := by
    simp [Op.eval, s4, s3, s2, s1, Store.write, Function.update_of_ne nAX.symm,
      Function.update_of_ne nXA.symm, Function.update_of_ne nXo.symm, hone, hc, (show cell rOne ≠ cell rAddr by decide)]
  refine ⟨s4, ?_, ?_⟩
  · have x1 := Exec.op (τ := τ) (inv := fun w : Store => w.Fits b) s (Op.const (cell rAddr) xBase) (by rw [e1]; exact f1)
    have x2 := Exec.op (τ := τ) (inv := fun w : Store => w.Fits b) s1 (Op.add (cell rAddr) (cell rAddr) (cell rXc)) (by rw [e2]; exact f2)
    have x3 := Exec.op (τ := τ) (inv := fun w : Store => w.Fits b) s2 (Op.store (cell rAddr) (cell val)) (by rw [e3]; exact f3)
    have x4 := Exec.op (τ := τ) (inv := fun w : Store => w.Fits b) s3 (Op.add (cell rXc) (cell rXc) (cell rOne)) (by rw [e4]; exact f4)
    rw [e1] at x1; rw [e2] at x2; rw [e3] at x3; rw [e4] at x4
    exact Exec.seq (Exec.seq x1 (Exec.seq x2 (Exec.skip _))) (Exec.seq x3 (Exec.seq x4 (Exec.skip _)))
  · refine ⟨rfl, ?_, ?_, ?_⟩
    · simp [s4, Store.write, hc]
    · intro i hi
      simp at hi; subst hi
      simp [s4, s3, Store.write, Function.update_of_ne nXA, hc]
    · intro a ha hd hout
      have h1 : a ≠ cell rXc := hd _ hXD
      have h2 : a ≠ cell rAddr := hd _ hA
      have h3 : a ≠ xBase + c := by simp at hout; omega
      simp [s4, s3, s2, s1, Store.write, Function.update_of_ne h1, Function.update_of_ne h2,
        Function.update_of_ne h3]

theorem modTwo_run {τ : Tapes} {b : ℕ} (d : ℕ) (s : Store) (fit : s.Fits b) (hb : 2 ≤ b) (k : ℕ)
    (hk : s.mem (cell rK) = k) (htwo : s.mem (cell rTwo) = 2) (hks : k.size + 2 ≤ b) (hd : d ≠ rXc)
    (a : Arithmetic) (ha : a = .mod ∨ a = .div) :
    ∃ t j, Exec τ (fun w => w.Fits b) (circ [asg d (.arithmetic a rK rTwo)]) s t j ∧ j ≤ Qc b ∧
      t.mem (cell d) = a.value k 2 ∧ Step [] [d] s t := by
  obtain ⟨t, j, ex, hj, res, st⟩ := circ_run (τ := τ) [asg d (.arithmetic a rK rTwo)] [d]
    (by simp [asg]) (by simp [asg, hd]) s fit hb (by
      have h1 := Word.size_twice_add_two k
      have h2 : (a.value k 2).size ≤ k.size := Nat.size_le_size (by
        rcases ha with rfl | rfl
        · exact Nat.mod_le _ _
        · exact Nat.div_le_self _ _)
      simp [Circuit.width, asg, Expression.width, Expression.eval, hk, htwo]
      omega)
  refine ⟨t, j, ex, ?_, ?_, st⟩
  · have : Circuit.multiplicity (fun i => s.mem (cell i)) [asg d (.arithmetic a rK rTwo)] ≤ 1 := by
      rcases ha with rfl | rfl <;> simp [Circuit.multiplicity, asg, Expression.multiplicity]
    calc j ≤ _ := hj
      _ ≤ 1 * Qc b := Nat.mul_le_mul_right _ this
      _ = Qc b := by simp
  · rw [res]; simp [Circuit.result, asg, Assignment.update, Expression.eval, hk, htwo]

theorem Step.reg {p : List Bool} {D : List ℕ} {s t : Store} (h : Step p D s t) (r : ℕ)
    (hr : r ∉ D) (hlow : cell r < xBase) : t.mem (cell r) = s.mem (cell r) :=
  h.2.2.2 _ (by simp [cell]) (fun d hd e => hr (by simp [cell] at e; exact e ▸ hd)) (Or.inl (by omega))

def emitD : List ℕ := [rK, rTmp, rAddr, rXc]

theorem emitD_low : ∀ d ∈ emitD, cell d < xBase := by decide

def emitBody : Cmd := .seq (putBit rOne) (.seq (circ [asg rTmp (.arithmetic .mod rK rTwo)])
  (.seq (putBit rTmp) (circ [asg rK (.arithmetic .div rK rTwo)])))

theorem emitK_eq : emitK = .seq (.whileGt (cell rK) (cell rZero) emitBody) (putBit rZero) := rfl

theorem emitBody_run {τ : Tapes} {b : ℕ} (s : Store) (fit : s.Fits b) (hb : 2 ≤ b) (k : ℕ)
    (hk : s.mem (cell rK) = k) (hone : s.mem (cell rOne) = 1) (htwo : s.mem (cell rTwo) = 2)
    (hks : k.size + 2 ≤ b) (hw : (xBase + s.mem (cell rXc) + 2).size ≤ b) :
    ∃ t j, Exec τ (fun w => w.Fits b) emitBody s t j ∧ j ≤ 2 * Qc b + 8 ∧
      Step [true, decide (k % 2 = 1)] emitD s t ∧ t.mem (cell rK) = k / 2 := by
  have sub1 : ∀ d ∈ [rAddr, rXc], d ∈ emitD := by decide
  have sub2 : ∀ d ∈ [rTmp], d ∈ emitD := by decide
  have sub3 : ∀ d ∈ [rK], d ∈ emitD := by decide
  obtain ⟨s1, x1, st1⟩ := putBit_step (τ := τ) rOne true [rAddr, rXc] (by decide) (by decide) (by decide)
    s fit (by simpa using hone) hone ((Nat.size_le_size (by omega)).trans hw)
  have f1 := x1.post fit
  have k1 : s1.mem (cell rK) = k := (st1.reg rK (by decide) (by decide)).trans hk
  have t1 : s1.mem (cell rTwo) = 2 := (st1.reg rTwo (by decide) (by decide)).trans htwo
  have o1 : s1.mem (cell rOne) = 1 := (st1.reg rOne (by decide) (by decide)).trans hone
  obtain ⟨s2, j2, x2, hj2, v2, st2⟩ := modTwo_run (τ := τ) rTmp s1 f1 hb k k1 t1 hks (by decide) .mod (Or.inl rfl)
  have f2 := x2.post f1
  have k2 : s2.mem (cell rK) = k := (st2.reg rK (by decide) (by decide)).trans k1
  have t2 : s2.mem (cell rTwo) = 2 := (st2.reg rTwo (by decide) (by decide)).trans t1
  have o2 : s2.mem (cell rOne) = 1 := (st2.reg rOne (by decide) (by decide)).trans o1
  have c2 : s2.mem (cell rXc) = s.mem (cell rXc) + 1 := by rw [st2.2.1, st1.2.1]; simp
  obtain ⟨s3, x3, st3⟩ := putBit_step (τ := τ) rTmp (decide (k % 2 = 1)) [rAddr, rXc] (by decide) (by decide)
    (by decide) s2 f2 (by rw [v2]; simp [Arithmetic.value]; rcases Nat.mod_two_eq_zero_or_one k with h | h <;> simp [h])
    o2 (by rw [c2]; exact (Nat.size_le_size (by omega)).trans hw)
  have f3 := x3.post f2
  have k3 : s3.mem (cell rK) = k := (st3.reg rK (by decide) (by decide)).trans k2
  have t3 : s3.mem (cell rTwo) = 2 := (st3.reg rTwo (by decide) (by decide)).trans t2
  obtain ⟨s4, j4, x4, hj4, v4, st4⟩ := modTwo_run (τ := τ) rK s3 f3 hb k k3 t3 hks (by decide) .div (Or.inr rfl)
  refine ⟨s4, 4 + (j2 + (4 + j4)), Exec.seq x1 (Exec.seq x2 (Exec.seq x3 x4)), by omega, ?_, by
    rw [v4]; rfl⟩
  have := Step.trans emitD_low (st1.mono sub1) (Step.trans emitD_low (st2.mono sub2)
    (Step.trans emitD_low (st3.mono sub1) (st4.mono sub3)))
  simpa using this

theorem emitLoop_run {τ : Tapes} {b : ℕ} (hb : 2 ≤ b) (k : ℕ) : ∀ (s : Store), s.Fits b →
    s.mem (cell rK) = k → s.mem (cell rOne) = 1 → s.mem (cell rTwo) = 2 → s.mem (cell rZero) = 0 →
    k.size + 2 ≤ b → (xBase + s.mem (cell rXc) + 2 * k.size).size ≤ b →
    ∃ t j, Exec τ (fun w => w.Fits b) (.whileGt (cell rK) (cell rZero) emitBody) s t j ∧
      j ≤ k.size * (2 * Qc b + 12) + 1 ∧ Step (k.bits.flatMap fun x => [true, x]) emitD s t := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro s fit hk hone htwo hzero hks hw
  rcases Nat.eq_zero_or_pos k with rfl | kpos
  · exact ⟨s, 1, Exec.done (by rw [hk, hzero]), by simp, by simpa using Step.refl emitD s⟩
  have hbits := bits_pos k kpos
  have hsz : k.size = (k / 2).size + 1 := by
    rw [← Nat.size_eq_bits_len, ← Nat.size_eq_bits_len, hbits]; simp
  obtain ⟨s1, j1, x1, hj1, st1, k1⟩ := emitBody_run (τ := τ) s fit hb k hk hone htwo hks
    ((Nat.size_le_size (by omega)).trans hw)
  have f1 := x1.post fit
  obtain ⟨s2, j2, x2, hj2, st2⟩ := ih (k / 2) (by omega) s1 f1 k1
    ((st1.reg rOne (by decide) (by decide)).trans hone) ((st1.reg rTwo (by decide) (by decide)).trans htwo)
    ((st1.reg rZero (by decide) (by decide)).trans hzero) (by omega)
    (by rw [st1.2.1]; simp; exact (Nat.size_le_size (by omega)).trans hw)
  refine ⟨s2, 1 + j1 + 1 + j2, Exec.again (by rw [hk, hzero]; omega) x1 x2, ?_, ?_⟩
  · rw [hsz, Nat.add_mul]; omega
  · rw [hbits]
    simpa using Step.trans emitD_low st1 st2

theorem emitK_run {τ : Tapes} {b : ℕ} (hb : 2 ≤ b) (k : ℕ) (s : Store) (fit : s.Fits b)
    (hk : s.mem (cell rK) = k) (hone : s.mem (cell rOne) = 1) (htwo : s.mem (cell rTwo) = 2)
    (hzero : s.mem (cell rZero) = 0)
    (hks : k.size + 2 ≤ b) (hw : (xBase + s.mem (cell rXc) + (encNat k).length).size ≤ b) :
    ∃ t j, Exec τ (fun w => w.Fits b) emitK s t j ∧
      j ≤ (k.size + 1) * (2 * Qc b + 12) ∧ Step (encNat k) emitD s t := by
  have hlen : (encNat k).length = 2 * k.size + 1 := by
    have := BinaryRead.field_length k
    simpa [BinaryRead.field, BinaryRead.pairs, encNat] using this
  rw [hlen] at hw
  obtain ⟨s1, j1, x1, hj1, st1⟩ := emitLoop_run (τ := τ) hb k s fit hk hone htwo hzero hks
    ((Nat.size_le_size (by omega)).trans hw)
  have f1 := x1.post fit
  obtain ⟨s2, x2, st2⟩ := putBit_step (τ := τ) rZero false [rAddr, rXc] (by decide) (by decide) (by decide)
    s1 f1 (by rw [st1.reg rZero (by decide) (by decide), hzero]; rfl)
    ((st1.reg rOne (by decide) (by decide)).trans hone)
    (by rw [st1.2.1]; simp [Nat.size_eq_bits_len]; exact (Nat.size_le_size (by omega)).trans hw)
  refine ⟨s2, j1 + 4, by rw [emitK_eq]; exact Exec.seq x1 x2, ?_, ?_⟩
  · rw [Nat.add_mul]; omega
  · exact Step.trans emitD_low st1 (st2.mono (by decide))


theorem emit_run {τ : Tapes} {b : ℕ} (hb : 2 ≤ b) (src k : ℕ) (s : Store) (fit : s.Fits b)
    (hk : s.mem (cell src) = k) (hone : s.mem (cell rOne) = 1) (htwo : s.mem (cell rTwo) = 2)
    (hzero : s.mem (cell rZero) = 0)
    (hks : k.size + 2 ≤ b) (hw : (xBase + s.mem (cell rXc) + (encNat k).length).size ≤ b) :
    ∃ t j, Exec τ (fun w => w.Fits b) (emit src) s t j ∧
      j ≤ (k.size + 1) * (2 * Qc b + 12) + Qc b ∧ Step (encNat k) emitD s t := by
  obtain ⟨s1, j1, x1, hj1, res, st1⟩ := circ_run (τ := τ) [asg rK (.add src rZero)] [rK]
    (by simp [asg]) (by simp [asg]; decide) s fit hb
    (by simp [Circuit.width, asg, Expression.width, Expression.eval, hk, hzero]; omega)
  have f1 := x1.post fit
  have k1 : s1.mem (cell rK) = k := by
    rw [res]; simp [Circuit.result, asg, Assignment.update, Expression.eval, hk, hzero]
  obtain ⟨s2, j2, x2, hj2, st2⟩ := emitK_run (τ := τ) hb k s1 f1 k1
    ((st1.reg rOne (by decide) (by decide)).trans hone) ((st1.reg rTwo (by decide) (by decide)).trans htwo)
    ((st1.reg rZero (by decide) (by decide)).trans hzero) hks (by rw [st1.2.1]; simpa using hw)
  refine ⟨s2, j1 + j2, Exec.seq x1 x2, ?_, by simpa using Step.trans emitD_low (st1.mono (by decide)) st2⟩
  have : j1 ≤ Qc b := by
    simpa [Circuit.multiplicity, asg, Expression.multiplicity] using hj1
  omega

end DirectedHamiltonicity.Main.CycleHost


-- ===== Solutions/Dev/BuildXB.lean =====

set_option autoImplicit false

namespace DirectedHamiltonicity.Main.CycleHost

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word
open TargetedSamplers.Structured.Interp DirectedHamiltonicity.Main.CycleReduction

def arcList : List Assignment :=
  [asg rQ (.arithmetic .div rSlot rThree), asg rLl (.arithmetic .mod rSlot rThree),
      asg rU (.arithmetic .div rQ rN), asg rV (.arithmetic .mod rQ rN),
      asg rIdx (.arithmetic .mul rU rN), asg rIdx (.add rIdx rV)] ++ bitOf rGp rIdx ++
      [asg rCand (.add rTmp rZero),
       asg rTmp2 (.arithmetic .pow rFifty rIdx), asg rTmp2 (.arithmetic .div rSym rTmp2),
       asg rTmp2 (.arithmetic .mod rTmp2 rFifty),
       asg rIdx (.arithmetic .mul rV rThree), asg rIdx (.add rIdx rLl),
       asg rWv (.arithmetic .pow rW rIdx), asg rWv (.arithmetic .div rWt rWv),
       asg rWv (.arithmetic .mod rWv rW), asg rWv (.add rWv rOne),
       asg rTv (.add rS rZero), asg rHv (.add rS rZero)]

def maskCmd : Cmd := ifLe rTmp2 rZero (circ [asg rMm (.literal 0)])
      (circ [asg rMm (.sub rTmp2 rOne), asg rMm (.arithmetic .div rMm rSeven),
        asg rMm (.add rMm rOne)])

def filterCmd : Cmd :=
  ifLe rCand rZero (circ [asg rWv (.literal 0)])
        (ifLe rTmp rZero (circ [asg rWv (.literal 0)])
          (ifEqual (cell rU) (cell rV) (circ [asg rWv (.literal 0)])
            (ifEqual (cell rV) (cell rS) (circ [asg rWv (.literal 0)])
              (ifEqual (cell rU) (cell rT) (circ [asg rWv (.literal 0)])
                (circ [asg rTv (.add rU rZero), asg rHv (.add rV rZero)])))))

theorem slotArc_eq : slotArc = .seq (circ arcList) (.seq maskCmd (.seq (circ (bitOf rMm rLl)) filterCmd)) :=
  rfl

def slotD : List ℕ := [rQ, rLl, rU, rV, rIdx, rTmp, rCand, rTmp2, rWv, rTv, rHv, rMm]

theorem lt_div' {x y M : ℕ} (h : x < M) : x / y < M := lt_of_le_of_lt (Nat.div_le_self _ _) h
theorem lt_mod' {x y M : ℕ} (h : x < M) : x % y < M := lt_of_le_of_lt (Nat.mod_le _ _) h
theorem lt_divmul' {x y M : ℕ} (h : x < M) : x / y * y < M := lt_of_le_of_lt (Nat.div_mul_le_self _ _) h
theorem lt_add0' {x M : ℕ} (h : x < M) : x + 0 < M := by simpa using h
theorem lt_modsucc' {x y M : ℕ} (h : y < M) (hy : 0 < y) : x % y + 1 < M :=
  lt_of_le_of_lt (Nat.mod_lt _ hy) h


theorem szK1 {x K b : ℕ} (h : x < 2 ^ K) (hK : K + 2 ≤ b) : x.size ≤ b :=
  (Nat.size_le.mpr h).trans (by omega)

theorem szK2 {x K b : ℕ} (h : x < 2 ^ K) (hK : K + 2 ≤ b) : (2 * x + 2).size ≤ b := by
  apply Nat.size_le.mpr
  calc 2 * x + 2 < 2 ^ (K + 2) := by rw [pow_add]; omega
    _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hK

theorem arcList_run {τ : Tapes} {b : ℕ} (s : Store) (fit : s.Fits b) (K n i G sym W wt sv : ℕ)
    (hKb : K + 2 ≤ b) (hWpos : 0 < W)
    (hi : s.mem (cell rSlot) = i) (hn : s.mem (cell rN) = n) (hG : s.mem (cell rGp) = G)
    (hsym : s.mem (cell rSym) = sym) (hW : s.mem (cell rW) = W) (hwt : s.mem (cell rWt) = wt)
    (hs : s.mem (cell rS) = sv) (c : Consts s)
    (b1 : i < 2 ^ K) (b2 : G < 2 ^ K) (b3 : 2 ^ (i / 3) < 2 ^ K) (b4 : 50 ^ (i / 3) < 2 ^ K)
    (b5 : sym < 2 ^ K) (b6 : W < 2 ^ K) (b7 : W ^ (i / 3 % n * 3 + i % 3) < 2 ^ K)
    (b8 : wt < 2 ^ K) (b9 : sv < 2 ^ K) (b10 : i / 3 % n * 3 + i % 3 < 2 ^ K)
    (b11 : i / 3 % n * 3 < 2 ^ K) (b12 : 2 < 2 ^ K) (b13 : 50 < 2 ^ K) :
    ∃ t j, Exec τ (fun w => w.Fits b) (circ arcList) s t j ∧
      j ≤ (2 * (i / 3) + (i / 3 % n * 3 + i % 3) + 21) * Qc b ∧ Step [] slotD s t ∧
      t.mem (cell rLl) = i % 3 ∧ t.mem (cell rU) = i / 3 / n ∧ t.mem (cell rV) = i / 3 % n ∧
      t.mem (cell rCand) = G / 2 ^ (i / 3) % 2 ∧ t.mem (cell rTmp2) = sym / 50 ^ (i / 3) % 50 ∧
      t.mem (cell rWv) = wt / W ^ (i / 3 % n * 3 + i % 3) % W + 1 ∧
      t.mem (cell rTv) = sv ∧ t.mem (cell rHv) = sv := by
  obtain ⟨one, zero, two, three, -, -, fifty, -⟩ := c
  simp only [rSlot, rN, rGp, rSym, rW, rWt, rS, rOne, rZero, rTwo, rThree, rFifty] at *
  obtain ⟨t, j, ex, hj, res, st⟩ := circ_run (τ := τ) arcList slotD
    (by simp [arcList, bitOf, asg, slotD, rQ, rLl, rU, rV, rIdx, rTmp, rCand, rTmp2, rWv, rTv, rHv, rMm])
    (by simp [arcList, bitOf, asg, rXc, rQ, rLl, rU, rV, rIdx, rTmp, rCand, rTmp2, rWv, rTv, rHv]) s fit
    (by omega) (by
      simp only [arcList, bitOf, List.cons_append, List.nil_append, Circuit.width, asg, Expression.width,
        Expression.eval, Arithmetic.value, Assignment.update, Function.update_apply, rQ, rSlot, rThree, rLl,
        rU, rN, rV, rIdx, rGp, rTmp, rTwo, rCand, rZero, rTmp2, rFifty, rSym, rWv, rW, rWt, rOne, rTv, rS, rHv,
        reduceIte, Nat.reduceEqDiff, max_le_iff, hi, hn, hG, hsym, hW, hwt, hs, one, zero, two, three, fifty,
        Nat.div_add_mod', Nat.add_zero]
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_,
        ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
      all_goals first
        | exact Nat.zero_le _
        | (apply szK2 _ hKb; (repeat' (first | assumption | apply lt_divmul' | apply lt_div' | apply lt_mod' | (apply lt_modsucc' <;> assumption))))
        | (apply szK1 _ hKb; (repeat' (first | assumption | apply lt_divmul' | apply lt_div' | apply lt_mod' | (apply lt_modsucc' <;> assumption)))))
  have mult : Circuit.multiplicity (fun i => s.mem (cell i)) arcList ≤ 2 * (i / 3) + (i / 3 % n * 3 + i % 3) + 21 := by
    simp only [arcList, bitOf, List.cons_append, List.nil_append, Circuit.multiplicity, Expression.multiplicity,
      asg, Expression.eval, Arithmetic.value, Assignment.update, Function.update_apply, rQ, rSlot, rThree, rLl,
      rU, rN, rV, rIdx, rGp, rTmp, rTwo, rCand, rZero, rTmp2, rFifty, rSym, rWv, rW, rWt, rOne, rTv, rS, rHv,
      reduceIte, Nat.reduceEqDiff, hi, hn, hG, hsym, hW, hwt, hs, one, zero, two, three, fifty,
      Nat.div_add_mod', Nat.add_zero]
    exact le_of_eq (by ring)
  refine ⟨t, j, ex, hj.trans (Nat.mul_le_mul_right _ mult), st, ?_⟩
  simp only [res]
  simp only [arcList, bitOf, List.cons_append, List.nil_append, Circuit.result, Expression.multiplicity,
      asg, Expression.eval, Arithmetic.value, Assignment.update, Function.update_apply, rQ, rSlot, rThree, rLl,
      rU, rN, rV, rIdx, rGp, rTmp, rTwo, rCand, rZero, rTmp2, rFifty, rSym, rWv, rW, rWt, rOne, rTv, rS, rHv,
      reduceIte, Nat.reduceEqDiff, hi, hn, hG, hsym, hW, hwt, hs, one, zero, two, three, fifty,
      Nat.div_add_mod', Nat.add_zero, and_self]


def mmOf (sy : ℕ) : ℕ := if sy ≤ 0 then 0 else (sy - 1) / 7 + 1

theorem mmOf_lt (sy : ℕ) (h : sy < 50) : mmOf sy < 8 := by
  unfold mmOf; split_ifs <;> omega

theorem maskCmd_run {τ : Tapes} {b : ℕ} (s : Store) (fit : s.Fits b) (hb : 9 ≤ b) (sy : ℕ)
    (hsy : s.mem (cell rTmp2) = sy) (hsy50 : sy < 50) (c : Consts s) :
    ∃ t j, Exec τ (fun w => w.Fits b) maskCmd s t j ∧ j ≤ 3 * Qc b + 2 ∧ Step [] [rMm] s t ∧
      t.mem (cell rMm) = mmOf sy := by
  obtain ⟨one, zero, -, -, -, seven, -, -⟩ := c
  simp only [rTmp2, rZero, rOne, rSeven] at *
  by_cases h : sy ≤ 0
  · obtain ⟨t, j, ex, hj, res, st⟩ := circ_run (τ := τ) [asg rMm (.literal 0)] [rMm]
      (by simp [asg]) (by simp [asg, rXc, rMm]) s fit (by omega)
      (by simp [Circuit.width, asg, Expression.width, Expression.eval])
    refine ⟨t, 1 + j, Exec.yes (by simp only [rTmp2, rZero]; rw [hsy, zero]; exact h) ex, ?_, st, ?_⟩
    · have : j ≤ Qc b := by simpa [Circuit.multiplicity, asg, Expression.multiplicity] using hj
      omega
    · rw [res]; simp [Circuit.result, asg, Assignment.update, Expression.eval, mmOf, h]
  · obtain ⟨t, j, ex, hj, res, st⟩ := circ_run (τ := τ) [asg rMm (.sub rTmp2 rOne),
      asg rMm (.arithmetic .div rMm rSeven), asg rMm (.add rMm rOne)] [rMm]
      (by simp [asg]) (by simp [asg, rXc, rMm]) s fit (by omega) (by
        simp only [Circuit.width, asg, Expression.width, Expression.eval, Arithmetic.value,
          Assignment.update, Function.update_apply, rMm, rTmp2, rOne, rSeven, reduceIte, Nat.reduceEqDiff,
          max_le_iff, hsy, one, seven]
        refine ⟨?_, ⟨?_, ?_⟩, ?_, ?_⟩
        all_goals first
          | exact Nat.zero_le _
          | (apply szK2 (K := 7) _ (by omega); first | omega | (norm_num; done) | (norm_num; omega))
          | (apply szK1 (K := 7) _ (by omega); first | omega | (norm_num; done) | (norm_num; omega)))
    refine ⟨t, 1 + j + 1, Exec.no (by simp only [rTmp2, rZero]; rw [hsy, zero]; exact h) ex, ?_, st, ?_⟩
    · have : j ≤ 3 * Qc b := by simpa [Circuit.multiplicity, asg, Expression.multiplicity] using hj
      omega
    · rw [res]
      simp [Circuit.result, asg, Assignment.update, Expression.eval, mmOf, h, hsy, one, seven, Arithmetic.value,
        rMm, rTmp2, rOne, rSeven]

theorem bitMm_run {τ : Tapes} {b : ℕ} (s : Store) (fit : s.Fits b) (hb : 9 ≤ b) (mm l : ℕ)
    (hmm : s.mem (cell rMm) = mm) (hl : s.mem (cell rLl) = l) (hmm8 : mm < 8) (hl3 : l < 3) (c : Consts s) :
    ∃ t j, Exec τ (fun w => w.Fits b) (circ (bitOf rMm rLl)) s t j ∧ j ≤ 6 * Qc b ∧ Step [] [rTmp] s t ∧
      t.mem (cell rTmp) = mm / 2 ^ l % 2 := by
  obtain ⟨-, -, two, -, -, -, -, -⟩ := c
  simp only [rMm, rLl, rTwo] at *
  have hp : 2 ^ l < 8 := by
    calc 2 ^ l < 2 ^ 3 := Nat.pow_lt_pow_right (by norm_num) hl3
      _ = 8 := by norm_num
  obtain ⟨t, j, ex, hj, res, st⟩ := circ_run (τ := τ) (bitOf rMm rLl) [rTmp]
      (by simp [asg, bitOf]) (by simp [asg, bitOf, rXc, rTmp]) s fit (by omega) (by
        simp only [bitOf, Circuit.width, asg, Expression.width, Expression.eval, Arithmetic.value,
          Assignment.update, Function.update_apply, rMm, rLl, rTwo, rTmp, reduceIte, Nat.reduceEqDiff,
          max_le_iff, hmm, hl, two]
        have h1 : mm / 2 ^ l < 8 := lt_of_le_of_lt (Nat.div_le_self _ _) hmm8
        have h2 : mm / 2 ^ l % 2 < 8 := lt_of_le_of_lt (Nat.mod_le _ _) h1
        refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
        all_goals first
          | exact Nat.zero_le _
          | (apply szK2 (K := 7) _ (by omega); first | omega | (norm_num; done) | (norm_num; omega))
          | (apply szK1 (K := 7) _ (by omega); first | omega | (norm_num; done) | (norm_num; omega)))
  refine ⟨t, j, ex, ?_, st, ?_⟩
  · have : Circuit.multiplicity (fun i => s.mem (cell i)) (bitOf rMm rLl) ≤ 6 := by
      simp only [bitOf, Circuit.multiplicity, asg, Expression.multiplicity, Assignment.update,
        Function.update_apply, rMm, rLl, rTwo, rTmp, reduceIte, Nat.reduceEqDiff, hl, Expression.eval,
        Arithmetic.value, hmm, two]
      all_goals omega
    exact hj.trans (Nat.mul_le_mul_right _ this)
  · rw [res]
    simp [bitOf, Circuit.result, asg, Assignment.update, Expression.eval, Arithmetic.value, hmm, hl, two,
      rMm, rLl, rTwo, rTmp]


theorem ifEqual_yes' {τ : Tapes} {inv : Store → Prop} {l r : ℕ} {yes no : Cmd} {s t : Store} {k : ℕ}
    (h : s.mem l = s.mem r) (e : Exec τ inv yes s t k) :
    Exec τ inv (ifEqual l r yes no) s t (1 + (1 + k)) :=
  Exec.yes (le_of_eq h) (Exec.yes (le_of_eq h.symm) e)

theorem ifEqual_no' {τ : Tapes} {inv : Store → Prop} {l r : ℕ} {yes no : Cmd} {s t : Store} {k : ℕ}
    (h : s.mem l ≠ s.mem r) (e : Exec τ inv no s t k) :
    ∃ k', k' ≤ k + 3 ∧ Exec τ inv (ifEqual l r yes no) s t k' := by
  by_cases h1 : s.mem l ≤ s.mem r
  · exact ⟨_, le_refl _ |>.trans (by omega), Exec.yes h1 (Exec.no (by omega) e)⟩
  · exact ⟨_, by omega, Exec.no h1 e⟩

def arcOut (cand bit u v sv tv w : ℕ) : ℕ × ℕ × ℕ :=
  if cand ≤ 0 ∨ bit ≤ 0 ∨ u = v ∨ v = sv ∨ u = tv then (sv, sv, 0) else (u, v, w)

theorem filterCmd_run {τ : Tapes} {b : ℕ} (s : Store) (fit : s.Fits b) (hb : 2 ≤ b)
    (cand bit u v sv tv w : ℕ) (hu : u.size ≤ b) (hv : v.size ≤ b)
    (hc : s.mem (cell rCand) = cand) (hbit : s.mem (cell rTmp) = bit) (hU : s.mem (cell rU) = u)
    (hV : s.mem (cell rV) = v) (hS : s.mem (cell rS) = sv) (hT : s.mem (cell rT) = tv)
    (hW : s.mem (cell rWv) = w) (hTv : s.mem (cell rTv) = sv) (hHv : s.mem (cell rHv) = sv)
    (hzero : s.mem (cell rZero) = 0) :
    ∃ t j, Exec τ (fun w => w.Fits b) filterCmd s t j ∧ j ≤ 2 * Qc b + 20 ∧
      Step [] [rWv, rTv, rHv] s t ∧ t.mem (cell rTv) = (arcOut cand bit u v sv tv w).1 ∧
      t.mem (cell rHv) = (arcOut cand bit u v sv tv w).2.1 ∧
      t.mem (cell rWv) = (arcOut cand bit u v sv tv w).2.2 := by
  obtain ⟨t0, j0, x0, hj0, res0, st0⟩ := circ_run (τ := τ) [asg rWv (.literal 0)] [rWv]
      (by simp [asg]) (by simp [asg, rXc, rWv]) s fit hb
      (by simp [Circuit.width, asg, Expression.width, Expression.eval])
  have j0le : j0 ≤ Qc b := by simpa [Circuit.multiplicity, asg, Expression.multiplicity] using hj0
  have w0 : t0.mem (cell rWv) = 0 := by rw [res0]; simp [Circuit.result, asg, Assignment.update, Expression.eval]
  have tv0 : t0.mem (cell rTv) = sv := (st0.reg rTv (by decide) (by decide)).trans hTv
  have hv0 : t0.mem (cell rHv) = sv := (st0.reg rHv (by decide) (by decide)).trans hHv
  have st0' : Step [] [rWv, rTv, rHv] s t0 := st0.mono (by decide)
  by_cases h1 : cand ≤ 0
  · refine ⟨t0, 1 + j0, Exec.yes (by rw [hc, hzero]; exact h1) x0, by omega, st0', ?_⟩
    simp [arcOut, h1, tv0, hv0, w0]
  have n1 : ¬ s.mem (cell rCand) ≤ s.mem (cell rZero) := by rw [hc, hzero]; exact h1
  by_cases h2 : bit ≤ 0
  · refine ⟨t0, 1 + (1 + j0) + 1, Exec.no n1 (Exec.yes (by rw [hbit, hzero]; exact h2) x0), by omega, st0', ?_⟩
    simp [arcOut, h2, tv0, hv0, w0]
  have n2 : ¬ s.mem (cell rTmp) ≤ s.mem (cell rZero) := by rw [hbit, hzero]; exact h2
  by_cases h3 : u = v
  · refine ⟨t0, 1 + (1 + (1 + (1 + j0)) + 1) + 1, Exec.no n1 (Exec.no n2 (ifEqual_yes' (l := cell rU) (r := cell rV) (by rw [hU, hV]; exact h3) x0)),
      by omega, st0', ?_⟩
    simp [arcOut, h3, tv0, hv0, w0]
  have n3 : s.mem (cell rU) ≠ s.mem (cell rV) := by rw [hU, hV]; exact h3
  by_cases h4 : v = sv
  · obtain ⟨k4, hk4, e4⟩ := ifEqual_no' (yes := circ [asg rWv (.literal 0)]) n3
      (ifEqual_yes' (l := cell rV) (r := cell rS) (no := ifEqual (cell rU) (cell rT) (circ [asg rWv (.literal 0)])
                (circ [asg rTv (.add rU rZero), asg rHv (.add rV rZero)])) (by rw [hV, hS]; exact h4) x0)
    refine ⟨t0, 1 + (1 + k4 + 1) + 1, Exec.no n1 (Exec.no n2 e4), by omega, st0', ?_⟩
    simp [arcOut, h4, tv0, hv0, w0]
  have n4 : s.mem (cell rV) ≠ s.mem (cell rS) := by rw [hV, hS]; exact h4
  by_cases h5 : u = tv
  · obtain ⟨k5, hk5, e5⟩ := ifEqual_no' (yes := circ [asg rWv (.literal 0)]) n4
      (ifEqual_yes' (l := cell rU) (r := cell rT) (no := circ [asg rTv (.add rU rZero), asg rHv (.add rV rZero)])
        (by rw [hU, hT]; exact h5) x0)
    obtain ⟨k4, hk4, e4⟩ := ifEqual_no' (yes := circ [asg rWv (.literal 0)]) n3 e5
    refine ⟨t0, 1 + (1 + k4 + 1) + 1, Exec.no n1 (Exec.no n2 e4), by omega, st0', ?_⟩
    simp [arcOut, h5, tv0, hv0, w0]
  have n5 : s.mem (cell rU) ≠ s.mem (cell rT) := by rw [hU, hT]; exact h5
  obtain ⟨t1, j1, x1, hj1, res1, st1⟩ := circ_run (τ := τ)
      [asg rTv (.add rU rZero), asg rHv (.add rV rZero)] [rWv, rTv, rHv]
      (by simp [asg]) (by simp [asg, rXc, rTv, rHv]) s fit hb
      (by
        simp only [Circuit.width, asg, Expression.width, Expression.eval, Assignment.update,
          Function.update_apply, rTv, rHv, rU, rV, rZero, reduceIte, Nat.reduceEqDiff, max_le_iff]
        simp only [rU, rV, rZero] at hU hV hzero
        simp [hU, hV, hzero, hu, hv])
  have j1le : j1 ≤ 2 * Qc b := by
    have : Circuit.multiplicity (fun i => s.mem (cell i))
        [asg rTv (.add rU rZero), asg rHv (.add rV rZero)] = 2 := by
      simp [Circuit.multiplicity, asg, Expression.multiplicity]
    rw [this] at hj1; exact hj1
  obtain ⟨k5, hk5, e5⟩ := ifEqual_no' (yes := circ [asg rWv (.literal 0)]) n5 x1
  obtain ⟨k4', hk4', e4'⟩ := ifEqual_no' (yes := circ [asg rWv (.literal 0)]) n4 e5
  obtain ⟨k4, hk4, e4⟩ := ifEqual_no' (yes := circ [asg rWv (.literal 0)]) n3 e4'
  refine ⟨t1, 1 + (1 + k4 + 1) + 1, Exec.no n1 (Exec.no n2 e4), by omega, st1, ?_⟩
  have e1 : t1.mem (cell rTv) = u := by
    rw [res1]; simp only [rU, rV, rZero] at hU hV hzero
    simp [Circuit.result, asg, Assignment.update, Expression.eval, rTv, rHv, rU, rV, rZero, hU, hzero]
  have e2 : t1.mem (cell rHv) = v := by
    rw [res1]; simp only [rU, rV, rZero] at hU hV hzero
    simp [Circuit.result, asg, Assignment.update, Expression.eval, rTv, rHv, rU, rV, rZero, hV, hzero]
  have e3 : t1.mem (cell rWv) = w := by
    rw [res1]; simp only [rWv] at hW
    simp [Circuit.result, asg, Assignment.update, Expression.eval, rTv, rHv, rWv, hW]
  simp [arcOut, h1, h2, h3, h4, h5, e1, e2, e3]


/-- The arc computed for slot `i` by `slotArc`. -/
def slotOut (n G sym W wt sv tv i : ℕ) : ℕ × ℕ × ℕ :=
  arcOut (G / 2 ^ (i / 3) % 2) (mmOf (sym / 50 ^ (i / 3) % 50) / 2 ^ (i % 3) % 2) (i / 3 / n) (i / 3 % n)
    sv tv (wt / W ^ (i / 3 % n * 3 + i % 3) % W + 1)

theorem Qc_ge (b : ℕ) : 15 ≤ Qc b := by unfold Qc; omega

theorem cost_aux (X Q j1 j2 j3 j4 : ℕ) (hQ : 15 ≤ Q) (h1 : j1 ≤ (X + 21) * Q) (h2 : j2 ≤ 3 * Q + 2)
    (h3 : j3 ≤ 6 * Q) (h4 : j4 ≤ 2 * Q + 20) : j1 + (j2 + (j3 + j4)) ≤ (X + 40) * Q := by
  rw [Nat.add_mul] at h1 ⊢; omega

theorem slotArc_run {τ : Tapes} {b : ℕ} (s : Store) (fit : s.Fits b) (K n i G sym W wt sv tv : ℕ)
    (hKb : K + 2 ≤ b) (hb : 9 ≤ b) (hWpos : 0 < W)
    (hi : s.mem (cell rSlot) = i) (hn : s.mem (cell rN) = n) (hG : s.mem (cell rGp) = G)
    (hsym : s.mem (cell rSym) = sym) (hW : s.mem (cell rW) = W) (hwt : s.mem (cell rWt) = wt)
    (hs : s.mem (cell rS) = sv) (ht : s.mem (cell rT) = tv) (c : Consts s)
    (b1 : i < 2 ^ K) (b2 : G < 2 ^ K) (b3 : 2 ^ (i / 3) < 2 ^ K) (b4 : 50 ^ (i / 3) < 2 ^ K)
    (b5 : sym < 2 ^ K) (b6 : W < 2 ^ K) (b7 : W ^ (i / 3 % n * 3 + i % 3) < 2 ^ K)
    (b8 : wt < 2 ^ K) (b9 : sv < 2 ^ K) (b10 : i / 3 % n * 3 + i % 3 < 2 ^ K)
    (b11 : i / 3 % n * 3 < 2 ^ K) (b12 : 2 < 2 ^ K) (b13 : 50 < 2 ^ K) :
    ∃ t j, Exec τ (fun w => w.Fits b) slotArc s t j ∧
      j ≤ (2 * (i / 3) + (i / 3 % n * 3 + i % 3) + 40) * Qc b ∧ Step [] slotD s t ∧
      t.mem (cell rTv) = (slotOut n G sym W wt sv tv i).1 ∧
      t.mem (cell rHv) = (slotOut n G sym W wt sv tv i).2.1 ∧
      t.mem (cell rWv) = (slotOut n G sym W wt sv tv i).2.2 := by
  have c0 := c
  obtain ⟨one, zero, two, three, six, seven, fifty, c49⟩ := c
  obtain ⟨s1, j1, x1, hj1, st1, l1, u1, v1, cand1, sy1, w1, tv1, hv1⟩ :=
    arcList_run (τ := τ) s fit K n i G sym W wt sv hKb hWpos hi hn hG hsym hW hwt hs c0
      b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13
  have f1 := x1.post fit
  have keep1 : ∀ r, r ∉ slotD → cell r < xBase → s1.mem (cell r) = s.mem (cell r) :=
    fun r h1 h2 => st1.reg r h1 h2
  have c1 : Consts s1 := ⟨(keep1 rOne (by decide) (by decide)).trans one,
    (keep1 rZero (by decide) (by decide)).trans zero, (keep1 rTwo (by decide) (by decide)).trans two,
    (keep1 rThree (by decide) (by decide)).trans three, (keep1 rSix (by decide) (by decide)).trans six,
    (keep1 rSeven (by decide) (by decide)).trans seven, (keep1 rFifty (by decide) (by decide)).trans fifty,
    (keep1 rC49 (by decide) (by decide)).trans c49⟩
  obtain ⟨s2, j2, x2, hj2, st2, mm2⟩ := maskCmd_run (τ := τ) s1 f1 hb _ sy1 (Nat.mod_lt _ (by norm_num)) c1
  have f2 := x2.post f1
  have keep2 : ∀ r, r ∉ [rMm] → cell r < xBase → s2.mem (cell r) = s1.mem (cell r) :=
    fun r h1 h2 => st2.reg r h1 h2
  have c2 : Consts s2 := ⟨(keep2 rOne (by decide) (by decide)).trans c1.one,
    (keep2 rZero (by decide) (by decide)).trans c1.zero, (keep2 rTwo (by decide) (by decide)).trans c1.two,
    (keep2 rThree (by decide) (by decide)).trans c1.three, (keep2 rSix (by decide) (by decide)).trans c1.six,
    (keep2 rSeven (by decide) (by decide)).trans c1.seven,
    (keep2 rFifty (by decide) (by decide)).trans c1.fifty, (keep2 rC49 (by decide) (by decide)).trans c1.c49⟩
  obtain ⟨s3, j3, x3, hj3, st3, bit3⟩ := bitMm_run (τ := τ) s2 f2 hb _ _ mm2
    ((keep2 rLl (by decide) (by decide)).trans l1) (mmOf_lt _ (Nat.mod_lt _ (by norm_num)))
    (Nat.mod_lt _ (by norm_num)) c2
  have f3 := x3.post f2
  have keep3 : ∀ r, r ∉ [rTmp] → cell r < xBase → s3.mem (cell r) = s2.mem (cell r) :=
    fun r h1 h2 => st3.reg r h1 h2
  have k23 : ∀ r, r ∉ [rTmp] → r ∉ [rMm] → cell r < xBase → s3.mem (cell r) = s1.mem (cell r) :=
    fun r h1 h2 h3 => (keep3 r h1 h3).trans (keep2 r h2 h3)
  have hu : (i / 3 / n).size ≤ b := szK1 (lt_div' (lt_div' b1)) hKb
  have hv : (i / 3 % n).size ≤ b := szK1 (lt_mod' (lt_div' b1)) hKb
  obtain ⟨s4, j4, x4, hj4, st4, o1, o2, o3⟩ := filterCmd_run (τ := τ) s3 f3 (by omega) _ _ _ _ sv tv _ hu hv
    ((k23 rCand (by decide) (by decide) (by decide)).trans cand1) bit3
    ((k23 rU (by decide) (by decide) (by decide)).trans u1)
    ((k23 rV (by decide) (by decide) (by decide)).trans v1)
    ((k23 rS (by decide) (by decide) (by decide)).trans ((keep1 rS (by decide) (by decide)).trans hs))
    ((k23 rT (by decide) (by decide) (by decide)).trans ((keep1 rT (by decide) (by decide)).trans ht))
    ((k23 rWv (by decide) (by decide) (by decide)).trans w1)
    ((k23 rTv (by decide) (by decide) (by decide)).trans tv1)
    ((k23 rHv (by decide) (by decide) (by decide)).trans hv1)
    ((k23 rZero (by decide) (by decide) (by decide)).trans c1.zero)
  refine ⟨s4, j1 + (j2 + (j3 + j4)), by rw [slotArc_eq]; exact x1.seq (x2.seq (x3.seq x4)), ?_, ?_,
    o1, o2, o3⟩
  · exact cost_aux _ _ _ _ _ _ (Qc_ge b) hj1 hj2 hj3 hj4
  · have low : ∀ d ∈ slotD, cell d < xBase := by decide
    simpa using Step.trans low st1 (Step.trans low (st2.mono (by decide))
      (Step.trans low (st3.mono (by decide)) (st4.mono (by decide))))

end DirectedHamiltonicity.Main.CycleHost


-- ===== Solutions/Dev/BuildXC.lean =====

set_option autoImplicit false

namespace DirectedHamiltonicity.Main.CycleHost

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word
open TargetedSamplers.Structured.Interp DirectedHamiltonicity.Main.CycleReduction

theorem mmOf_testBit (x : Fin 50) (l : Fin 3) :
    mmOf x.val / 2 ^ l.val % 2 = (decide (l ∈ copyMask x)).toNat := by
  have h : mmOf x.val = (if x.val = 0 then 0 else 1 + (x.val - 1) / 7) := by
    unfold mmOf; split_ifs <;> omega
  simp only [copyMask, Finset.mem_filter, Finset.mem_univ, true_and, h, Nat.testBit_eq_decide_div_mod_eq]
  generalize (if x.val = 0 then 0 else 1 + (x.val - 1) / 7) / 2 ^ l.val = N
  rcases Nat.mod_two_eq_zero_or_one N with e | e <;> simp [e]

theorem slot_spec {n : ℕ} (hn : 2 ≤ n) (adj : Fin n → Fin n → Bool) (s t : Fin n) (z : MatrixSeed n)
    (G sym wt : ℕ)
    (bits : ∀ x y : Fin n, G.testBit (x.val * n + y.val) = adj x y)
    (symd : ∀ x y : Fin n, sym / 50 ^ (x.val * n + y.val) % 50 = (z.1 (x, y)).val)
    (wtd : ∀ (y : Fin n) (l : Fin 3), wt / Wmax n ^ (y.val * 3 + l.val) % Wmax n = (z.2 (y, l)).val)
    (i : ℕ) (hi : i < n * n * 3) :
    let a := pathAdj adj s t
    let r := restrictedSeed a s z
    let S : SArc a → Finset (Fin 3) := fun e => copyMask (r.1 e)
    let H := inputGraph a S s
    ((H.tail ⟨i, hi⟩ : ℕ) = (slotOut n G sym (Wmax n) wt s t i).1) ∧
    ((H.head ⟨i, hi⟩ : ℕ) = (slotOut n G sym (Wmax n) wt s t i).2.1) ∧
    inputWeight a S s (clean_no_in adj s t) (labelWeight s r.2) ⟨i, hi⟩ =
      (slotOut n G sym (Wmax n) wt s t i).2.2 := by
  intro a r S H
  have npos : 0 < n := by omega
  have hq : i / 3 < n * n := by omega
  have hu : i / 3 / n < n := Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hq)
  have hv : i / 3 % n < n := Nat.mod_lt _ npos
  have hl : i % 3 < 3 := Nat.mod_lt _ (by norm_num)
  set u : Fin n := ⟨i / 3 / n, hu⟩ with hu'
  set v : Fin n := ⟨i / 3 % n, hv⟩ with hv'
  set l : Fin 3 := ⟨i % 3, hl⟩ with hl'
  have heq : (slotEquiv n).symm ⟨i, hi⟩ = ((u, v), l) := by
    simp [slotEquiv, finProdFinEquiv, Fin.divNat, Fin.modNat, u, v, l]
  have hidx : u.val * n + v.val = i / 3 := by simp [u, v]; exact Nat.div_add_mod' _ _
  have hcand : G / 2 ^ (i / 3) % 2 = (adj u v).toNat := by
    have := bits u v
    rw [hidx, Nat.testBit_eq_decide_div_mod_eq] at this
    rcases Nat.mod_two_eq_zero_or_one (G / 2 ^ (i / 3)) with e | e <;> rw [e] <;> rw [e] at this <;>
      cases h : adj u v <;> simp_all
  have hsy : sym / 50 ^ (i / 3) % 50 = (z.1 (u, v)).val := by rw [← hidx]; exact symd u v
  have hw : wt / Wmax n ^ (i / 3 % n * 3 + i % 3) % Wmax n = (z.2 (v, l)).val := wtd v l
  have hbit : mmOf (sym / 50 ^ (i / 3) % 50) / 2 ^ (i % 3) % 2 = (decide (l ∈ copyMask (z.1 (u, v)))).toNat := by
    rw [hsy]; exact mmOf_testBit _ l
  have hdec : decodeSlot a S ⟨i, hi⟩ = decodePair a S ((u, v), l) := by
    simp only [decodeSlot]; rw [heq]
  have hout : slotOut n G sym (Wmax n) wt s t i =
      arcOut (adj u v).toNat (decide (l ∈ copyMask (z.1 (u, v)))).toNat u v s t ((z.2 (v, l)).val + 1) := by
    simp only [slotOut]; rw [hcand, hbit, hw]
  rw [hout]
  simp only [H, inputGraph, paddedGraph, paddedTail, paddedHead, inputWeight, paddedWeight, hdec, decodePair]
  by_cases hA : a u v
  · by_cases hL : l ∈ copyMask (z.1 (u, v))
    · have hL' : l ∈ S ⟨(u, v), hA⟩ := hL
      have hA0 := hA
      obtain ⟨h1, h2, h3, h4⟩ := hA0
      have n2 : u.val ≠ v.val := fun e => h2 (Fin.ext e)
      have n3 : v.val ≠ s.val := fun e => h3 (Fin.ext e)
      have n4 : u.val ≠ t.val := fun e => h4 (Fin.ext e)
      simp [hA, hL', arcOut, h1, hL, n2, n3, n4, copyGraph, GroupIsolation.weight, labelWeight, r,
        restrictedSeed, GroupIsolation.dest]
    · have hL' : l ∉ S ⟨(u, v), hA⟩ := hL
      simp [hA, hL', arcOut, hL]
  · have : ¬ ((adj u v).toNat ≤ 0 → False) ∨ u.val = v.val ∨ v.val = s.val ∨ u.val = t.val := by
      simp only [a, pathAdj, not_and_or, not_not] at hA
      rcases hA with h | h | h | h
      · left; cases e : adj u v <;> simp_all
      · right; left; exact congrArg Fin.val h
      · right; right; left; exact congrArg Fin.val h
      · right; right; right; exact congrArg Fin.val h
    have hc : ((adj u v).toNat ≤ 0 ∨ (decide (l ∈ copyMask (z.1 (u, v)))).toNat ≤ 0 ∨ u.val = v.val ∨
        v.val = s.val ∨ u.val = t.val) := by
      rcases this with h | h
      · left; by_contra h'; exact h (fun _ => h' (by omega))
      · right; right; exact h
    have ho : arcOut (adj u v).toNat (decide (l ∈ copyMask (z.1 (u, v)))).toNat u v s t ((z.2 (v, l)).val + 1)
        = ((s : ℕ), (s : ℕ), 0) := if_pos hc
    rw [ho]
    simp [hA]


theorem flatMap_finRange_eq {m : ℕ} (f : Fin m → List Bool) (g : ℕ → List Bool)
    (h : ∀ i (hi : i < m), f ⟨i, hi⟩ = g i) :
    (List.finRange m).flatMap f = (List.range m).flatMap g := by
  rw [← List.map_coe_finRange_eq_range, List.flatMap_map]
  congr 1
  funext e
  exact h e.val e.isLt

def slotEnc (n G sym wt sv tv i : ℕ) : List Bool :=
  encNat (slotOut n G sym (Wmax n) wt sv tv i).1 ++ encNat (slotOut n G sym (Wmax n) wt sv tv i).2.1 ++
    encNat (slotOut n G sym (Wmax n) wt sv tv i).2.2

theorem candX_eq {n : ℕ} (hn : 2 ≤ n) (adj : Fin n → Fin n → Bool) (s t : Fin n) (z : MatrixSeed n)
    (B : ℕ) (G sym wt : ℕ)
    (bits : ∀ x y : Fin n, G.testBit (x.val * n + y.val) = adj x y)
    (symd : ∀ x y : Fin n, sym / 50 ^ (x.val * n + y.val) % 50 = (z.1 (x, y)).val)
    (wtd : ∀ (y : Fin n) (l : Fin 3), wt / Wmax n ^ (y.val * 3 + l.val) % Wmax n = (z.2 (y, l)).val) :
    candX adj s t z B = encNat n ++ encNat (3 * (n * n)) ++
      (List.range (3 * (n * n))).flatMap (slotEnc n G sym wt s t) ++ encNat s ++ encNat t ++
      [false] ++ encNat B := by
  simp only [candX, parityInput, encodeParityInstance]
  rw [flatMap_finRange_eq _ (slotEnc n G sym wt s t) (fun i hi => by
    obtain ⟨h1, h2, h3⟩ := slot_spec hn adj s t z G sym wt bits symd wtd i hi
    simp only [slotEnc]; rw [h1, h2, h3])]
  rw [show n * n * 3 = 3 * (n * n) by ring]
  simp [encInt]

end DirectedHamiltonicity.Main.CycleHost


-- ===== Solutions/Dev/BuildXD.lean =====

set_option autoImplicit false

namespace DirectedHamiltonicity.Main.CycleHost

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word
open TargetedSamplers.Structured.Interp DirectedHamiltonicity.Main.CycleReduction

theorem pow_two_mono {x y : ℕ} (h : x ≤ y) : 2 ^ x ≤ 2 ^ y := Nat.pow_le_pow_right (by norm_num) h

theorem lt_two_pow_of_lt {x K : ℕ} (h : x ≤ K) : x < 2 ^ K :=
  lt_of_le_of_lt h (Nat.lt_two_pow_self)

theorem fifty_pow_le (q : ℕ) : 50 ^ q ≤ 2 ^ (6 * q) := by
  rw [pow_mul]; exact Nat.pow_le_pow_left (by norm_num) q

theorem wmax_lt {n : ℕ} (hn : 2 ≤ n) : Wmax n < 2 ^ (3 * n) := by
  have h1 : n < 2 ^ n := Nat.lt_two_pow_self
  have h2 : 2 ^ (n + 3) ≤ 2 ^ (3 * n) := pow_two_mono (by omega)
  have h3 : 2 ^ (n + 3) = 8 * 2 ^ n := by rw [pow_add]; ring
  simp only [Wmax]; omega

theorem wpow_le {n e : ℕ} (hn : 2 ≤ n) : Wmax n ^ e ≤ 2 ^ (3 * n * e) := by
  rw [pow_mul]; exact Nat.pow_le_pow_left (wmax_lt hn).le e

/-- All the width facts used by `slotArc_run`. -/
theorem kbounds {n : ℕ} (hn : 2 ≤ n) (i G sym wt sv : ℕ) (hi : i < 3 * (n * n)) (hG : G < 2 ^ (n * n))
    (hsym : sym < 50 ^ (n * n)) (hwt : wt < Wmax n ^ (n * 3)) (hsv : sv < n) :
    let K := 10 * (n + 1) ^ 2
    i < 2 ^ K ∧ G < 2 ^ K ∧ 2 ^ (i / 3) < 2 ^ K ∧ 50 ^ (i / 3) < 2 ^ K ∧ sym < 2 ^ K ∧
    Wmax n < 2 ^ K ∧ Wmax n ^ (i / 3 % n * 3 + i % 3) < 2 ^ K ∧ wt < 2 ^ K ∧ sv < 2 ^ K ∧
    i / 3 % n * 3 + i % 3 < 2 ^ K ∧ i / 3 % n * 3 < 2 ^ K ∧ 2 < 2 ^ K ∧ 50 < 2 ^ K := by
  intro K
  have hK : 10 * (n * n) + 20 * n + 10 = K := by simp only [K]; ring
  have hq : i / 3 < n * n := by omega
  have hv : i / 3 % n < n := Nat.mod_lt _ (by omega)
  have he : i / 3 % n * 3 + i % 3 < 3 * n := by omega
  have nn : n ≤ n * n := Nat.le_mul_self n
  have he2 : 3 * n * (i / 3 % n * 3 + i % 3) < 3 * n * (3 * n) :=
    Nat.mul_lt_mul_of_pos_left he (by omega)
  have he3 : 3 * n * (n * 3) = 9 * (n * n) := by ring
  have he4 : 3 * n * (3 * n) = 9 * (n * n) := by ring
  refine ⟨lt_two_pow_of_lt (by omega), lt_of_lt_of_le hG (pow_two_mono (by omega)),
    Nat.pow_lt_pow_right (by norm_num) (by omega),
    lt_of_le_of_lt (fifty_pow_le _) (Nat.pow_lt_pow_right (by norm_num) (by omega)),
    lt_of_lt_of_le hsym ((fifty_pow_le _).trans (pow_two_mono (by omega))),
    lt_two_pow_of_lt (by simp only [Wmax]; omega),
    lt_of_le_of_lt (wpow_le hn) (Nat.pow_lt_pow_right (by norm_num) (by omega)),
    lt_of_lt_of_le hwt ((wpow_le hn).trans (pow_two_mono (by omega))),
    lt_two_pow_of_lt (by omega), lt_two_pow_of_lt (by omega), lt_two_pow_of_lt (by omega),
    lt_two_pow_of_lt (by omega), lt_two_pow_of_lt (by omega)⟩

theorem size_le_big {N b y : ℕ} (hN : 1 ≤ N) (hb : 64 * N ≤ b) (hy : y ≤ 429 * N) : y.size + 2 ≤ b := by
  have h1 : N < 2 ^ N := Nat.lt_two_pow_self
  have h2 : y < 2 ^ (N + 9) := by rw [pow_add]; norm_num; omega
  have h3 : y.size ≤ N + 9 := Nat.size_le.mpr h2
  omega

theorem size_le_big' {N b y : ℕ} (hN : 1 ≤ N) (hb : 64 * N ≤ b) (hy : y ≤ 429 * N) : y.size ≤ b := by
  have := size_le_big hN hb hy; omega

theorem size_le_self' (k : ℕ) : k.size ≤ k := Nat.size_le.mpr Nat.lt_two_pow_self

theorem encNat_length (k : ℕ) : (encNat k).length = 2 * k.size + 1 := by
  have := BinaryRead.field_length k
  simpa [BinaryRead.field, BinaryRead.pairs, encNat] using this

theorem encNat_length_le (k : ℕ) : (encNat k).length ≤ 2 * k + 1 := by
  rw [encNat_length]; have := size_le_self' k; omega

theorem slotOut_bounds {n : ℕ} (hn : 2 ≤ n) (G sym wt sv tv i : ℕ) (hsv : sv < n) (hi : i < 3 * (n * n)) :
    (slotOut n G sym (Wmax n) wt sv tv i).1 < n ∧ (slotOut n G sym (Wmax n) wt sv tv i).2.1 < n ∧
      (slotOut n G sym (Wmax n) wt sv tv i).2.2 ≤ Wmax n := by
  have hu : i / 3 / n < n := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)
  have hv : i / 3 % n < n := Nat.mod_lt _ (by omega)
  have hw : wt / Wmax n ^ (i / 3 % n * 3 + i % 3) % Wmax n + 1 ≤ Wmax n :=
    Nat.mod_lt _ (by simp only [Wmax]; omega)
  simp only [slotOut, arcOut]
  split_ifs <;> simp_all

theorem slotEnc_length {n : ℕ} (hn : 2 ≤ n) (G sym wt sv tv i : ℕ) (hsv : sv < n) (hi : i < 3 * (n * n)) :
    (slotEnc n G sym wt sv tv i).length ≤ 16 * n := by
  obtain ⟨h1, h2, h3⟩ := slotOut_bounds hn G sym wt sv tv i hsv hi
  simp only [slotEnc, List.length_append]
  have := encNat_length_le (slotOut n G sym (Wmax n) wt sv tv i).1
  have := encNat_length_le (slotOut n G sym (Wmax n) wt sv tv i).2.1
  have := encNat_length_le (slotOut n G sym (Wmax n) wt sv tv i).2.2
  have : Wmax n ≤ 6 * n := by simp only [Wmax]; omega
  omega

theorem flatMap_range_length (g : ℕ → List Bool) (C : ℕ) (m : ℕ) (h : ∀ i < m, (g i).length ≤ C) :
    ((List.range m).flatMap g).length ≤ m * C := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, Nat.succ_mul]
    have := ih (fun i hi => h i (by omega))
    have := h m (by omega)
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    omega


def bodyD : List ℕ := [rQ, rLl, rU, rV, rIdx, rTmp, rCand, rTmp2, rWv, rTv, rHv, rMm, rK, rAddr, rXc]

theorem bodyD_low : ∀ d ∈ bodyD, cell d < xBase := by decide

theorem emit_cost (n Q k j : ℕ) (hQ : 15 ≤ Q) (hk : k ≤ 6 * n) (h : j ≤ (k + 1) * (2 * Q + 12) + Q) :
    j ≤ (18 * n + 4) * Q := by
  have : (k + 1) * (2 * Q + 12) ≤ (6 * n + 1) * (3 * Q) :=
    Nat.mul_le_mul (by omega) (by omega)
  nlinarith

theorem body_cost (n Q j1 j2 j3 j4 X : ℕ) (hQ : 15 ≤ Q) (hX : X ≤ 2 * (n * n) + 3 * n)
    (h1 : j1 ≤ (X + 40) * Q) (h2 : j2 ≤ (18 * n + 4) * Q) (h3 : j3 ≤ (18 * n + 4) * Q)
    (h4 : j4 ≤ (18 * n + 4) * Q) : j1 + (j2 + (j3 + j4)) ≤ 60 * (n + 1) ^ 2 * Q := by
  have : (X + 40) * Q ≤ (2 * (n * n) + 3 * n + 40) * Q := Nat.mul_le_mul_right _ (by omega)
  nlinarith

theorem gEmit_run {τ : Tapes} {b : ℕ} {n : ℕ} (m : ℕ) (hm : m ≤ (n + 1) ^ 3) (hb : 64 * (n + 1) ^ 3 ≤ b)
    (src k : ℕ)
    (s : Store) (fit : s.Fits b) (hk : s.mem (cell src) = k) (hkn : k ≤ 6 * m) (c : Consts s)
    (hw : (xBase + s.mem (cell rXc) + (encNat k).length).size ≤ b) :
    ∃ t j, Exec τ (fun w => w.Fits b) (emit src) s t j ∧ j ≤ (18 * m + 4) * Qc b ∧
      Step (encNat k) emitD s t ∧ Consts t := by
  have hN : 1 ≤ (n + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  obtain ⟨t, j, ex, hj, st⟩ := emit_run (τ := τ) (by nlinarith) src k s fit hk c.one c.two c.zero
    (size_le_big hN hb (by omega)) hw
  refine ⟨t, j, ex, emit_cost m (Qc b) k.size j (Qc_ge b) ((size_le_self' k).trans hkn) hj, st, ?_⟩
  have keep : ∀ r, r ∉ emitD → cell r < xBase → t.mem (cell r) = s.mem (cell r) :=
    fun r h1 h2 => st.reg r h1 h2
  exact ⟨(keep rOne (by decide) (by decide)).trans c.one,
    (keep rZero (by decide) (by decide)).trans c.zero, (keep rTwo (by decide) (by decide)).trans c.two,
    (keep rThree (by decide) (by decide)).trans c.three, (keep rSix (by decide) (by decide)).trans c.six,
    (keep rSeven (by decide) (by decide)).trans c.seven, (keep rFifty (by decide) (by decide)).trans c.fifty,
    (keep rC49 (by decide) (by decide)).trans c.c49⟩

def slotBody : Cmd := .seq slotArc (.seq (emit rTv) (.seq (emit rHv) (emit rWv)))

theorem body_run {τ : Tapes} {b : ℕ} {n : ℕ} (hn : 2 ≤ n) (hb : 64 * (n + 1) ^ 3 ≤ b)
    (s : Store) (fit : s.Fits b) (i G sym wt sv tv : ℕ) (hi : i < 3 * (n * n)) (hG : G < 2 ^ (n * n))
    (hsym : sym < 50 ^ (n * n)) (hwt : wt < Wmax n ^ (n * 3)) (hsv : sv < n)
    (ri : s.mem (cell rSlot) = i) (rn : s.mem (cell rN) = n) (rg : s.mem (cell rGp) = G)
    (rsym : s.mem (cell rSym) = sym) (rw : s.mem (cell rW) = Wmax n) (rwt : s.mem (cell rWt) = wt)
    (rs : s.mem (cell rS) = sv) (rt : s.mem (cell rT) = tv) (c : Consts s)
    (hw : (xBase + s.mem (cell rXc) + (slotEnc n G sym wt sv tv i).length).size ≤ b) :
    ∃ t j, Exec τ (fun w => w.Fits b) slotBody s t j ∧ j ≤ 60 * (n + 1) ^ 2 * Qc b ∧
      Step (slotEnc n G sym wt sv tv i) bodyD s t := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13⟩ := kbounds hn i G sym wt sv hi hG hsym hwt hsv
  have hKb : 10 * (n + 1) ^ 2 + 2 ≤ b := by nlinarith
  obtain ⟨s1, j1, x1, hj1, st1, tv1, hv1, wv1⟩ := slotArc_run (τ := τ) s fit _ n i G sym (Wmax n) wt sv tv hKb
    (by nlinarith) (by simp only [Wmax]; omega) ri rn rg rsym rw rwt rs rt c
    b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13
  have f1 := x1.post fit
  have keep1 : ∀ r, r ∉ slotD → cell r < xBase → s1.mem (cell r) = s.mem (cell r) :=
    fun r h1 h2 => st1.reg r h1 h2
  have c1 : Consts s1 := ⟨(keep1 rOne (by decide) (by decide)).trans c.one,
    (keep1 rZero (by decide) (by decide)).trans c.zero, (keep1 rTwo (by decide) (by decide)).trans c.two,
    (keep1 rThree (by decide) (by decide)).trans c.three, (keep1 rSix (by decide) (by decide)).trans c.six,
    (keep1 rSeven (by decide) (by decide)).trans c.seven, (keep1 rFifty (by decide) (by decide)).trans c.fifty,
    (keep1 rC49 (by decide) (by decide)).trans c.c49⟩
  obtain ⟨o1, o2, o3⟩ := slotOut_bounds hn G sym wt sv tv i hsv hi
  have hW6 : Wmax n ≤ 6 * n := by simp only [Wmax]; omega
  have hn3 : n ≤ (n + 1) ^ 3 := le_trans (by omega) (Nat.le_self_pow (by norm_num) (n + 1))
  set out := slotOut n G sym (Wmax n) wt sv tv i with hout
  have hlen : (slotEnc n G sym wt sv tv i).length =
      (encNat out.1).length + (encNat out.2.1).length + (encNat out.2.2).length := by
    simp [slotEnc, out, Nat.add_assoc]
  rw [hlen] at hw
  obtain ⟨s2, j2, x2, hj2, st2, c2⟩ := gEmit_run (τ := τ) n hn3 hb rTv out.1 s1 f1 tv1 (by omega) c1
    (by rw [st1.2.1]; simp only [List.length_nil, Nat.add_zero]; exact (Nat.size_le_size (by omega)).trans hw)
  have f2 := x2.post f1
  obtain ⟨s3, j3, x3, hj3, st3, c3⟩ := gEmit_run (τ := τ) n hn3 hb rHv out.2.1 s2 f2
    ((st2.reg rHv (by decide) (by decide)).trans hv1) (by omega) c2
    (by rw [st2.2.1, st1.2.1]; simp only [List.length_nil, Nat.add_zero]; exact (Nat.size_le_size (by omega)).trans hw)
  have f3 := x3.post f2
  obtain ⟨s4, j4, x4, hj4, st4, c4⟩ := gEmit_run (τ := τ) n hn3 hb rWv out.2.2 s3 f3
    ((st3.reg rWv (by decide) (by decide)).trans ((st2.reg rWv (by decide) (by decide)).trans wv1))
    (by omega) c3
    (by rw [st3.2.1, st2.2.1, st1.2.1]; simp only [List.length_nil, Nat.add_zero]; exact (Nat.size_le_size (by omega)).trans hw)
  have hq : 2 * (i / 3) + (i / 3 % n * 3 + i % 3) ≤ 2 * (n * n) + 3 * n := by
    have : i / 3 % n < n := Nat.mod_lt _ (by omega)
    omega
  refine ⟨s4, j1 + (j2 + (j3 + j4)), x1.seq (x2.seq (x3.seq x4)),
    body_cost n (Qc b) j1 j2 j3 j4 _ (Qc_ge b) hq hj1 hj2 hj3 hj4, ?_⟩
  have e : slotEnc n G sym wt sv tv i = [] ++ (encNat out.1 ++ (encNat out.2.1 ++ encNat out.2.2)) := by
    simp [slotEnc, out]
  rw [e]
  exact Step.trans bodyD_low (st1.mono (by decide)) (Step.trans bodyD_low (st2.mono (by decide))
    (Step.trans bodyD_low (st3.mono (by decide)) (st4.mono (by decide))))

end DirectedHamiltonicity.Main.CycleHost


-- ===== Solutions/Dev/BuildXE.lean =====

set_option autoImplicit false

namespace DirectedHamiltonicity.Main.CycleHost

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word
open TargetedSamplers.Structured.Interp DirectedHamiltonicity.Main.CycleReduction

theorem buildXDirty_low : ∀ d ∈ buildXDirty, cell d < xBase := by decide

/-- Registers outside `buildXDirty` keep the values of `u`. -/
def Agree (u s : Store) : Prop := ∀ r, r ∉ buildXDirty → cell r < xBase → s.mem (cell r) = u.mem (cell r)

theorem Agree.consts {u s : Store} (h : Agree u s) (c : Consts u) : Consts s :=
  ⟨(h rOne (by decide) (by decide)).trans c.one, (h rZero (by decide) (by decide)).trans c.zero,
    (h rTwo (by decide) (by decide)).trans c.two, (h rThree (by decide) (by decide)).trans c.three,
    (h rSix (by decide) (by decide)).trans c.six, (h rSeven (by decide) (by decide)).trans c.seven,
    (h rFifty (by decide) (by decide)).trans c.fifty, (h rC49 (by decide) (by decide)).trans c.c49⟩

theorem Agree.step {u s0 s : Store} {pre : List Bool} (h : Agree u s0) (st : Step pre buildXDirty s0 s) :
    Agree u s := fun r h1 h2 => (st.reg r h1 h2).trans (h r h1 h2)

theorem flatMap_range_mono (g : ℕ → List Bool) {a c : ℕ} (h : a ≤ c) :
    ((List.range a).flatMap g).length ≤ ((List.range c).flatMap g).length := by
  induction c with
  | zero => simp at h; subst h; rfl
  | succ c ih =>
    rcases Nat.eq_or_lt_of_le h with e | e
    · rw [e]
    · refine (ih (by omega)).trans ?_
      rw [List.range_succ, List.flatMap_append, List.length_append]; omega

theorem flatMap_range_succ (g : ℕ → List Bool) (i : ℕ) :
    (List.range (i + 1)).flatMap g = (List.range i).flatMap g ++ g i := by
  rw [List.range_succ, List.flatMap_append]; simp

theorem total_len {n : ℕ} (hn : 2 ≤ n) (lP lF ls lt lB B : ℕ) (hP : lP ≤ (2 * n + 1) + (2 * (3 * (n * n)) + 1))
    (hF : lF ≤ 3 * (n * n) * (16 * n)) (hs : ls ≤ 2 * n + 1) (ht : lt ≤ 2 * n + 1)
    (hB : lB ≤ 2 * B + 1) (hBm : B ≤ (n - 1) * (6 * (n - 1))) :
    lP + lF + ls + lt + 1 + lB ≤ 128 * (n + 1) ^ 3 := by
  have h1 : (n - 1) * (6 * (n - 1)) ≤ 6 * (n * n) := by
    have : n - 1 ≤ n := Nat.sub_le n 1
    calc (n - 1) * (6 * (n - 1)) ≤ n * (6 * n) := Nat.mul_le_mul this (by omega)
      _ = 6 * (n * n) := by ring
  have h2 : 3 * (n * n) * (16 * n) = 48 * (n * n * n) := by ring
  have h3 : 128 * (n + 1) ^ 3 = 128 * (n * n * n) + 384 * (n * n) + 384 * n + 128 := by ring
  omega

theorem total_cost (n b Q j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 : ℕ) (hn : 2 ≤ n) (hQ : Q ≤ 15 * (b + 1) ^ 2)
    (hQ15 : 15 ≤ Q)
    (h0 : j0 ≤ 1) (h1 : j1 ≤ (18 * (n + 1) ^ 2 + 4) * Q) (h2 : j2 ≤ (18 * (n + 1) ^ 2 + 4) * Q)
    (h3 : j3 ≤ Q) (h4 : j4 ≤ 3 * (n * n) * (60 * (n + 1) ^ 2 * Q + 3) + 1)
    (h5 : j5 ≤ (18 * (n + 1) ^ 2 + 4) * Q) (h6 : j6 ≤ (18 * (n + 1) ^ 2 + 4) * Q) (h7 : j7 ≤ 4)
    (h8 : j8 ≤ (18 * (n + 1) ^ 2 + 4) * Q) (h9 : j9 ≤ Q) :
    j0 + (j1 + (j2 + ((j3 + j4) + (j5 + (j6 + (j7 + (j8 + j9))))))) ≤
      10 ^ 6 * (n + 1) ^ 6 * (b + 1) ^ 2 := by
  set A := (n + 1) ^ 2 with hA
  have hA1 : 9 ≤ A := by rw [hA]; nlinarith
  have hnn : n * n ≤ A := by rw [hA]; nlinarith
  have e6 : (n + 1) ^ 6 = A * A * A := by rw [hA]; ring
  rw [e6]
  have k1 : 3 * (n * n) * (60 * A * Q + 3) + 1 ≤ 3 * A * (60 * A * Q + 3) + 1 :=
    by gcongr
  have k2 : j0 + (j1 + (j2 + ((j3 + j4) + (j5 + (j6 + (j7 + (j8 + j9))))))) ≤ 400 * (A * A) * Q := by
    nlinarith
  have k3 : 400 * (A * A) * Q ≤ 400 * (A * A) * (15 * (b + 1) ^ 2) := Nat.mul_le_mul_left _ hQ
  have k4 : 400 * (A * A) * (15 * (b + 1) ^ 2) ≤ 10 ^ 6 * (A * A * A) * (b + 1) ^ 2 := by
    have : 6000 * (A * A) ≤ 10 ^ 6 * (A * A * A) := by nlinarith
    nlinarith
  omega

theorem Qc_le (b : ℕ) : Qc b ≤ 15 * (b + 1) ^ 2 := by unfold Qc; nlinarith

end DirectedHamiltonicity.Main.CycleHost


-- ===== Solutions/Dev/BuildX.lean =====

set_option autoImplicit false

namespace DirectedHamiltonicity.Main.CycleHost

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word
open TargetedSamplers.Structured.Interp DirectedHamiltonicity.Main.CycleReduction

theorem sq_facts (n : ℕ) : n * n ≤ (n + 1) ^ 2 ∧ n ≤ (n + 1) ^ 2 := by
  constructor <;> nlinarith

set_option maxHeartbeats 1000000 in
/-- Spec of `buildX`. -/
theorem buildX_exec' {τ : Tapes} {b : ℕ} (u : Store) {n : ℕ} (hn : 2 ≤ n)
    (adj : Fin n → Fin n → Bool) (s t : Fin n) (z : MatrixSeed n) (B : ℕ) (hB : B ≤ Bmax n)
    (G sym wt : ℕ) (hG : G < 2 ^ (n * n)) (hsym : sym < 50 ^ (n * n)) (hwt : wt < Wmax n ^ (n * 3))
    (bits : ∀ x y : Fin n, G.testBit (x.val * n + y.val) = adj x y)
    (symd : ∀ x y : Fin n, sym / 50 ^ (x.val * n + y.val) % 50 = (z.1 (x, y)).val)
    (wtd : ∀ (y : Fin n) (l : Fin 3), wt / Wmax n ^ (y.val * 3 + l.val) % Wmax n = (z.2 (y, l)).val)
    (c : Consts u) (rn : u.mem (cell rN) = n) (rm : u.mem (cell rM) = 3 * (n * n))
    (rg : u.mem (cell rGp) = G) (rs : u.mem (cell rS) = s.val) (rt : u.mem (cell rT) = t.val)
    (rb : u.mem (cell rB) = B) (rsym : u.mem (cell rSym) = sym) (rwt : u.mem (cell rWt) = wt)
    (rw : u.mem (cell rW) = Wmax n) (fit : u.Fits b) (hb : 64 * (n + 1) ^ 3 ≤ b) :
    let x := candX adj s t z B
    ∃ v j, Exec τ (fun w => w.Fits b) buildX u v j ∧ j ≤ 10 ^ 6 * (n + 1) ^ 6 * (b + 1) ^ 2 ∧
      x.length ≤ 128 * (n + 1) ^ 3 ∧ v.mem (cell 106) = x.length ∧
      (∀ i (hi : i < x.length), v.mem (xBase + i) = (x[i]'hi).toNat) ∧
      Kept buildXDirty u v (fun a => a < xBase ∨ xBase + 128 * (n + 1) ^ 3 ≤ a) := by
  intro x
  have hx := candX_eq hn adj s t z B G sym wt bits symd wtd
  set m := 3 * (n * n) with hm
  set g := slotEnc n G sym wt s t with hg
  set P := encNat n ++ encNat m with hP
  set F := (List.range m).flatMap g with hF
  have hN : 1 ≤ (n + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hb2 : 2 ≤ b := by omega
  have hA3 : (n + 1) ^ 2 ≤ (n + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hA : n * n ≤ (n + 1) ^ 2 := (sq_facts n).1
  have hn1 : n ≤ (n + 1) ^ 2 := (sq_facts n).2
  have hs : s.val < n := s.isLt
  have ht : t.val < n := t.isLt
  have hBn : B ≤ 6 * (n * n) := by
    have : (n - 1) * (6 * (n - 1)) ≤ 6 * (n * n) := by
      calc (n - 1) * (6 * (n - 1)) ≤ n * (6 * n) := Nat.mul_le_mul (Nat.sub_le n 1) (by omega)
        _ = 6 * (n * n) := by ring
    simp only [Bmax, Wmax] at hB
    omega
  -- lengths
  have lP : P.length ≤ (2 * n + 1) + (2 * (3 * (n * n)) + 1) := by
    simp only [hP, List.length_append]
    have := encNat_length_le n; have := encNat_length_le m; omega
  have lF : F.length ≤ 3 * (n * n) * (16 * n) :=
    flatMap_range_length g _ m (fun i hi => slotEnc_length hn G sym wt s t i hs hi)
  have hxe : x = P ++ F ++ encNat s ++ encNat t ++ [false] ++ encNat B := hx
  have hxl : x.length = P.length + F.length + (encNat s).length + (encNat t).length + 1 +
      (encNat B).length := by
    rw [hxe]; simp only [List.length_append, List.length_singleton]
  have hxlen : x.length ≤ 128 * (n + 1) ^ 3 := by
    rw [hxl]
    exact total_len hn _ _ _ _ _ B lP lF ((encNat_length_le _).trans (by omega))
      ((encNat_length_le _).trans (by omega)) (encNat_length_le B) hB
  have wsz : ∀ y, y ≤ xBase + x.length → y.size ≤ b := fun y hy =>
    size_le_big' hN hb (by unfold xBase at hy; omega)
  have D_low := buildXDirty_low
  -- step 0: cursor := 0
  let s0 := u.write (cell rXc) 0
  have f0 : s0.Fits b := Store.write_fits fit _ (by simp)
  have x0 : Exec τ (fun w => w.Fits b) (circ [asg rXc (.literal 0)]) u s0 (1 + 0) :=
    Exec.seq (Exec.op u (.const (cell rXc) 0) f0) (Exec.skip _)
  have s0x : s0.mem (cell rXc) = 0 := by simp [s0, Store.write]
  have s0o : ∀ a, a ≠ cell rXc → s0.mem a = u.mem a := fun a ha => by
    simp [s0, Store.write, Function.update_of_ne ha]
  have ag0 : Agree u s0 := fun r h1 _ => s0o _ (by
    intro e; apply h1; simp only [cell] at e; have : r = rXc := by omega
    rw [this]; decide)
  -- emit n
  obtain ⟨s1, j1, x1, hj1, st1, c1⟩ := gEmit_run (τ := τ) ((n + 1) ^ 2) hA3 hb rN n s0 f0
    ((ag0 rN (by decide) (by decide)).trans rn) (by omega) (ag0.consts c)
    (wsz _ (by rw [s0x, hxl, hP, List.length_append]; omega))
  have f1 := x1.post f0
  have T1 : Step (encNat n) buildXDirty s0 s1 := st1.mono (by decide)
  -- emit m
  obtain ⟨s2, j2, x2, hj2, st2, c2⟩ := gEmit_run (τ := τ) ((n + 1) ^ 2) hA3 hb rM m s1 f1
    (((ag0.step T1) rM (by decide) (by decide)).trans rm) (by omega) c1
    (wsz _ (by rw [T1.2.1, s0x, hxl, hP, List.length_append]; omega))
  have f2 := x2.post f1
  have T2 : Step P buildXDirty s0 s2 := Step.trans D_low T1 (st2.mono (by decide))
  -- slot := 0
  obtain ⟨s3, j3, x3, hj3, res3, st3⟩ := circ_run (τ := τ) [asg rSlot (.literal 0)] [rSlot]
    (by simp [asg]) (by simp [asg, rXc, rSlot]) s2 f2 hb2
    (by simp [Circuit.width, asg, Expression.width, Expression.eval])
  have f3 := x3.post f2
  have hj3' : j3 ≤ Qc b := by simpa [Circuit.multiplicity, asg, Expression.multiplicity] using hj3
  have T3 : Step P buildXDirty s0 s3 := by
    simpa using Step.trans D_low T2 (st3.mono (by decide))
  have slot3 : s3.mem (cell rSlot) = 0 := by
    rw [res3]; simp [Circuit.result, asg, Assignment.update, Expression.eval]
  -- the slot loop
  have hFm : ∀ i, i ≤ m → ((List.range i).flatMap g).length ≤ F.length :=
    fun i hi => flatMap_range_mono g hi
  obtain ⟨s4, j4, x4, hj4, T4, -⟩ := forRange_exec (τ := τ) (b := b) (cell rSlot) (cell rM) (cell rOne) 0 m
    (60 * (n + 1) ^ 2 * Qc b) slotBody
    (fun i w => Step (P ++ (List.range i).flatMap g) buildXDirty s0 w ∧ w.mem (cell rSlot) = i)
    (fun i _ w hw => ⟨by rw [hw.2]; simp, by
      rw [((ag0.step hw.1) rM (by decide) (by decide)).trans rm]; simp [m]⟩)
    (fun i hi w hw fw => by
      obtain ⟨stw, slw⟩ := hw
      have agw := ag0.step stw
      obtain ⟨t', j', ex', hj', st'⟩ := body_run (τ := τ) hn hb w fw i G sym wt s t hi hG hsym hwt hs
        slw ((agw rN (by decide) (by decide)).trans rn) ((agw rGp (by decide) (by decide)).trans rg)
        ((agw rSym (by decide) (by decide)).trans rsym) ((agw rW (by decide) (by decide)).trans rw)
        ((agw rWt (by decide) (by decide)).trans rwt) ((agw rS (by decide) (by decide)).trans rs)
        ((agw rT (by decide) (by decide)).trans rt) (agw.consts c)
        (wsz _ (by
          have h1 := hFm (i + 1) (by omega)
          rw [flatMap_range_succ, List.length_append] at h1
          rw [stw.2.1, s0x, List.length_append, hxl]
          change _ + (g i).length ≤ _
          omega))
      refine ⟨t', j', ex', hj', by rw [st'.reg rSlot (by decide) (by decide), slw]; simp,
        (st'.reg rOne (by decide) (by decide)).trans (agw.consts c).one, ?_, by simp [Store.write]⟩
      have := (Step.trans D_low stw (st'.mono (by decide))).write rSlot (0 + i + 1) (by decide)
        (by decide) (by decide)
      rw [flatMap_range_succ, ← List.append_assoc]
      exact this)
    (size_le_big' hN hb (by omega)) s3 ⟨by simpa using T3, slot3⟩ f3
  have f4 := x4.post f3
  have T4' : Step (P ++ F) buildXDirty s0 s4 := T4
  have ag4 := ag0.step T4'
  -- emit s, t
  obtain ⟨s5, j5, x5, hj5, st5, c5⟩ := gEmit_run (τ := τ) ((n + 1) ^ 2) hA3 hb rS s.val s4 f4
    ((ag4 rS (by decide) (by decide)).trans rs) (by omega) (ag4.consts c)
    (wsz _ (by rw [T4'.2.1, s0x, hxl, List.length_append]; omega))
  have f5 := x5.post f4
  have T5 : Step (P ++ F ++ encNat s) buildXDirty s0 s5 := Step.trans D_low T4' (st5.mono (by decide))
  have ag5 := ag0.step T5
  obtain ⟨s6, j6, x6, hj6, st6, c6⟩ := gEmit_run (τ := τ) ((n + 1) ^ 2) hA3 hb rT t.val s5 f5
    ((ag5 rT (by decide) (by decide)).trans rt) (by omega) c5
    (wsz _ (by rw [T5.2.1, s0x, hxl]; simp only [List.length_append]; omega))
  have f6 := x6.post f5
  have T6 : Step (P ++ F ++ encNat s ++ encNat t) buildXDirty s0 s6 :=
    Step.trans D_low T5 (st6.mono (by decide))
  -- sign bit
  obtain ⟨s7, x7, st7⟩ := putBit_step (τ := τ) rZero false [rAddr, rXc] (by decide) (by decide) (by decide)
    s6 f6 (by rw [c6.zero]; rfl) c6.one
    (wsz _ (by rw [T6.2.1, s0x, hxl]; simp only [List.length_append]; omega))
  have f7 := x7.post f6
  have T7 : Step (P ++ F ++ encNat s ++ encNat t ++ [false]) buildXDirty s0 s7 :=
    Step.trans D_low T6 (st7.mono (by decide))
  have ag7 := ag0.step T7
  -- emit B
  obtain ⟨s8, j8, x8, hj8, st8, c8⟩ := gEmit_run (τ := τ) ((n + 1) ^ 2) hA3 hb rB B s7 f7
    ((ag7 rB (by decide) (by decide)).trans rb) (by omega) (ag7.consts c)
    (wsz _ (by rw [T7.2.1, s0x, hxl]; simp only [List.length_append, List.length_singleton]; omega))
  have f8 := x8.post f7
  have T8 : Step x buildXDirty s0 s8 := by
    rw [hxe]; exact Step.trans D_low T7 (st8.mono (by decide))
  -- xlen
  obtain ⟨v, j9, x9, hj9, res9, st9⟩ := circ_run (τ := τ) [asg 106 (.add rXc rZero)] [106]
    (by simp [asg]) (by simp [asg, rXc]) s8 f8 hb2
    (by
      simp only [Circuit.width, asg, Expression.width, Expression.eval, max_le_iff]
      rw [T8.2.1, s0x, c8.zero]
      exact ⟨wsz _ (by omega), Nat.zero_le _⟩)
  have hj9' : j9 ≤ Qc b := by simpa [Circuit.multiplicity, asg, Expression.multiplicity] using hj9
  have T9 : Step x buildXDirty s0 v := by simpa using Step.trans D_low T8 (st9.mono (by decide))
  refine ⟨v, 1 + 0 + (j1 + (j2 + ((j3 + j4) + (j5 + (j6 + (4 + (j8 + j9))))))),
    x0.seq (x1.seq (x2.seq ((x3.seq x4).seq (x5.seq (x6.seq (x7.seq (x8.seq x9))))))), ?_, hxlen, ?_, ?_, ?_⟩
  · exact total_cost n b (Qc b) (1 + 0) j1 j2 j3 j4 j5 j6 4 j8 j9 hn (Qc_le b) (Qc_ge b) (by omega)
      hj1 hj2 hj3' hj4 hj5 hj6 le_rfl hj8 hj9'
  · rw [res9]
    simp only [Circuit.result, asg, Assignment.update, Expression.eval, Function.update_self]
    rw [T8.2.1, s0x, c8.zero]; simp
  · intro i hi
    have := T9.2.2.1 i hi
    rw [s0x] at this; simpa using this
  · refine ⟨T9.1.trans rfl, fun a ha hd hout => ?_⟩
    rw [T9.2.2.2 a ha hd (by rw [s0x]; omega)]
    exact s0o a (hd rXc (by decide))

end DirectedHamiltonicity.Main.CycleHost


section SolutionBlock
open DirectedHamiltonicity.Main
open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word
open TargetedSamplers.Structured.Interp DirectedHamiltonicity.Main.CycleReduction
open DirectedHamiltonicity.Main.CycleHost
theorem solution {τ : Tapes} {b : ℕ} (u : Store) {n : ℕ} (hn : 2 ≤ n)
    (adj : Fin n → Fin n → Bool) (s t : Fin n) (z : MatrixSeed n) (B : ℕ) (hB : B ≤ Bmax n)
    (G sym wt : ℕ) (hG : G < 2 ^ (n * n)) (hsym : sym < 50 ^ (n * n)) (hwt : wt < Wmax n ^ (n * 3))
    (bits : ∀ x y : Fin n, G.testBit (x.val * n + y.val) = adj x y)
    (symd : ∀ x y : Fin n, sym / 50 ^ (x.val * n + y.val) % 50 = (z.1 (x, y)).val)
    (wtd : ∀ (y : Fin n) (l : Fin 3), wt / Wmax n ^ (y.val * 3 + l.val) % Wmax n = (z.2 (y, l)).val)
    (c : Consts u) (rn : u.mem (cell rN) = n) (rm : u.mem (cell rM) = 3 * (n * n))
    (rg : u.mem (cell rGp) = G) (rs : u.mem (cell rS) = s.val) (rt : u.mem (cell rT) = t.val)
    (rb : u.mem (cell rB) = B) (rsym : u.mem (cell rSym) = sym) (rwt : u.mem (cell rWt) = wt)
    (rw : u.mem (cell rW) = Wmax n) (fit : u.Fits b) (hb : 64 * (n + 1) ^ 3 ≤ b) :
    let x := candX adj s t z B
    ∃ v j, Exec τ (fun w => w.Fits b) buildX u v j ∧ j ≤ 10 ^ 6 * (n + 1) ^ 6 * (b + 1) ^ 2 ∧
      x.length ≤ 128 * (n + 1) ^ 3 ∧ v.mem (cell 106) = x.length ∧
      (∀ i (hi : i < x.length), v.mem (xBase + i) = (x[i]'hi).toNat) ∧
      Kept buildXDirty u v (fun a => a < xBase ∨ xBase + 128 * (n + 1) ^ 3 ≤ a) := by
  apply DirectedHamiltonicity.Main.CycleHost.buildX_exec' <;> assumption
end SolutionBlock
