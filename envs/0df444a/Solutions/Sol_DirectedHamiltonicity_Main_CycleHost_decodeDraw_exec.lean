-- Prove2me | solution 1 for DirectedHamiltonicity.Main.CycleHost.decodeDraw_exec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T04:20:44.590062+00:00
-- url     : https://prove2.me/submissions/228d769f-bf48-455d-a587-dc209790e21e

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


-- ===== Solutions/Dev/Params.lean =====

set_option autoImplicit false

namespace DirectedHamiltonicity.Main.CycleHost

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word
open TargetedSamplers.Structured.Interp DirectedHamiltonicity.Main.CycleReduction


/-- Spec of `decodeDraw`: the registers hold the components of `(rankDraw n).symm`. -/
theorem decodeDraw_exec' {τ : Tapes} {b : ℕ} (u : Store) {n : ℕ} (hn : 2 ≤ n) (D : ℕ)
    (hD : D < drawCount n)
    (c : Consts u) (rn : u.mem (cell rN) = n) (rdv : u.mem (cell rDv) = D)
    (rin : u.mem (cell rIn) = 50 ^ (n * n) * Wmax n ^ (n * 3) * (Bmax n + 1))
    (rbm : u.mem (cell rBm1) = Bmax n + 1) (rpw : u.mem (cell rPW) = Wmax n ^ (n * 3))
    (fit : u.Fits b) (hb : 64 * (n + 1) ^ 3 ≤ b) :
    let d := (rankDraw n).symm ⟨D, hD⟩
    ∃ v j, Exec τ (fun w => w.Fits b) decodeDraw u v j ∧ j ≤ 100 * (b + 1) ^ 2 ∧
      v.mem (cell rS) = d.1.1.val ∧ v.mem (cell rT) = d.1.2.val ∧ v.mem (cell rB) = d.2.2.val ∧
      v.mem (cell rSym) < 50 ^ (n * n) ∧ v.mem (cell rWt) < Wmax n ^ (n * 3) ∧
      (∀ x y : Fin n, v.mem (cell rSym) / 50 ^ (x.val * n + y.val) % 50 = (d.2.1.1 (x, y)).val) ∧
      (∀ (y : Fin n) (l : Fin 3),
        v.mem (cell rWt) / Wmax n ^ (y.val * 3 + l.val) % Wmax n = (d.2.1.2 (y, l)).val) ∧
      Kept decodeDirty u v (fun _ => True) := by
  intro d
  obtain ⟨h1, h2, h3, h4, h5⟩ := rankDraw_symm_vals n D hD
  simp only [rN, rDv, rIn, rBm1, rPW] at rn rdv rin rbm rpw
  have hDb : D < 2 ^ (b - 2) := by
    refine hD.trans ((drawCount_lt n).trans_le (Nat.pow_le_pow_right (by norm_num) ?_))
    have : (n + 1) ^ 2 ≤ (n + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  have le2 : 2 ≤ b := by nlinarith
  obtain ⟨v, j, ex, hj, vals, out, fr⟩ := circ_run (τ := τ) [asg rHi (.arithmetic .div rDv rIn), asg rInner (.arithmetic .mod rDv rIn),
    asg rS (.arithmetic .div rHi rN), asg rT (.arithmetic .mod rHi rN),
    asg rB (.arithmetic .mod rInner rBm1), asg rTab (.arithmetic .div rInner rBm1),
    asg rSym (.arithmetic .div rTab rPW), asg rWt (.arithmetic .mod rTab rPW)] u fit le2 (by
      simp only [Circuit.width, Expression.width, Assignment.update, Expression.eval,
        Arithmetic.value, asg, Function.update_apply, rHi, rDv, rIn, rInner, rS, rN, rT, rB, rBm1,
        rTab, rSym, rPW, rWt, rn, rdv, rin, rbm, rpw, Nat.reduceEqDiff, ↓reduceIte, max_le_iff]
      repeat' apply And.intro
      all_goals first
        | exact Nat.zero_le _
        | exact size_twice_le (lt_of_le_of_lt (by (repeat (first | exact le_rfl | refine (Nat.div_le_self _ _).trans ?_ | refine (Nat.mod_le _ _).trans ?_))) hDb) (by omega)
        | exact size_le_of_lt_pow (lt_of_le_of_lt (by (repeat (first | exact le_rfl | refine (Nat.div_le_self _ _).trans ?_ | refine (Nat.mod_le _ _).trans ?_))) hDb) (by omega))
  have gS := vals rS
  have gT := vals rT
  have gB := vals rB
  have gSym := vals rSym
  have gWt := vals rWt
  simp only [Circuit.result, Assignment.update, Expression.eval,
    Arithmetic.value, asg, Function.update_apply, rHi, rDv, rIn, rInner, rS, rN, rT, rB, rBm1,
    rTab, rSym, rPW, rWt, rn, rdv, rin, rbm, rpw, Nat.reduceEqDiff, ↓reduceIte] at gS gT gB gSym gWt
  simp only [Circuit.multiplicity, Expression.multiplicity, asg] at hj
  have hW : 0 < Wmax n := by show 0 < 6 * (n - 1); omega
  have hPW : 0 < Wmax n ^ (n * 3) := pow_pos hW _
  have hI : 0 < 50 ^ (n * n) * Wmax n ^ (n * 3) * (Bmax n + 1) := by positivity
  simp only [rS, rT, rB, rSym, rWt]
  refine ⟨v, j, ex, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, kept_of (by decide) out fr⟩
  · nlinarith
  · exact gS.trans h1.symm
  · exact gT.trans h2.symm
  · exact gB.trans h3.symm
  · rw [gSym, Nat.div_lt_iff_lt_mul hPW, Nat.div_lt_iff_lt_mul (by omega)]
    exact Nat.mod_lt _ hI
  · rw [gWt]; exact Nat.mod_lt _ hPW
  · intro x y; rw [gSym]; exact h4 x y
  · intro y l; rw [gWt]; exact h5 y l

set_option maxHeartbeats 2000000 in
/-- Spec of `params`. -/
theorem params_exec' {τ : Tapes} {b : ℕ} (u : Store) {n : ℕ} (hn : 2 ≤ n) (A k : ℕ)
    (c : Consts u) (rn : u.mem (cell rN) = n) (ra : u.mem (cell rA) = A) (rk : u.mem (cell rKk) = k)
    (fit : u.Fits b) (hb : 1000 * (n + 1) ^ 3 * (k + 1) + 2 * A.size ≤ b) :
    ∃ v j, Exec τ (fun w => w.Fits b) params u v j ∧ j ≤ 10 ^ 4 * (n + 1) ^ 2 * (k + 1) * (b + 1) ^ 2 ∧
      v.mem (cell rN2) = n * n ∧ v.mem (cell rM) = 3 * (n * n) ∧ v.mem (cell rW) = Wmax n ∧
      v.mem (cell rBm1) = Bmax n + 1 ∧ v.mem (cell rPW) = Wmax n ^ (n * 3) ∧
      v.mem (cell rIn) = 50 ^ (n * n) * Wmax n ^ (n * 3) * (Bmax n + 1) ∧
      v.mem (cell rDc) = drawCount n ∧ v.mem (cell rTrials) = trials n ∧
      v.mem (cell rSw) = seedWidth n ∧ v.mem (cell rL) = coinSpan A k n ∧
      v.mem (cell rR) = majorityHalf n ∧ v.mem (cell rR2) = 2 * majorityHalf n ∧
      v.mem (cell rTapeBase) = trials n * seedWidth n ∧
      v.mem (cell rVB) = xBase + 128 * (n + 1) ^ 3 ∧
      v.mem (cell 103) = xBase + 128 * (n + 1) ^ 3 + n ∧
      v.mem (cell 102) = xBase + 128 * (n + 1) ^ 3 + n + coinSpan A k n + 1 ∧
      v.mem (cell 105) = xBase ∧ v.mem (cell 110) = 1 ∧ v.mem (cell 111) = 0 ∧
      Kept paramsDirty u v (fun _ => True) := by
  rw [params_eq]
  obtain ⟨le2, key⟩ := budget_facts A hb
  have hP1 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hPk : (n + 1) ^ 2 ≤ (n + 1) ^ 2 * (k + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hP : 100 * (n + 1) ^ 2 + 3 ≤ b := by omega
  obtain ⟨v1, j1, e1, hj1, gN2, gM, gW, gB, gPW, gIn, gDc, gTr, gL, gOb, gTmp, o1, f1⟩ :=
    paramsC1_run (τ := τ) u hn A k c rn ra rk fit hb
  have fit1 := e1.post fit
  have z1 : v1.mem (cell rZero) = 0 := by rw [f1 _ (by decide) (by decide), c.zero]
  -- first ceiling logarithm: (trials n).size
  have hT1 : trials n + 1 ≤ 2 ^ (100 * (n + 1) ^ 2 + 1) := by
    have := trials_le n
    have : 1 ≤ 2 ^ (100 * (n + 1) ^ 2) := Nat.one_le_two_pow
    rw [pow_succ]; omega
  have cT : Nat.clog 2 (trials n + 1) ≤ 100 * (n + 1) ^ 2 + 1 := Nat.clog_le_of_le_pow hT1
  obtain ⟨v2, j2, e2, hj2, l2, o2, f2⟩ := clogInto_exec (τ := τ) rTmp2 rTmp v1 (trials n + 1)
    gTmp z1 fit1 le2 (by omega) (size_le_pb hT1 (by omega))
  have fit2 := e2.post fit1
  have z2 : v2.mem (cell rZero) = 0 := by
    rw [f2 _ (by decide) (by decide) (by decide), z1]
  have d2 : v2.mem (cell rDc) = drawCount n := by
    rw [f2 _ (by decide) (by decide) (by decide), gDc]
  -- second ceiling logarithm: seedWidth n
  have hD := (drawCount_lt n).le
  have cD : Nat.clog 2 (drawCount n) ≤ 16 * (n + 1) ^ 2 := Nat.clog_le_of_le_pow hD
  obtain ⟨v3, j3, e3, hj3, l3, o3, f3⟩ := clogInto_exec (τ := τ) rSw rDc v2 (drawCount n)
    d2 z2 fit2 le2 (by omega) (size_le_pb hD (by omega))
  have fit3 := e3.post fit2
  have t31 : ∀ a, 14 ≤ a → a ≠ cell rSw → a ≠ cell rTmp2 → (a < cell 90 ∨ cell 93 < a) →
      v3.mem a = v1.mem a := fun a h1 h2 h3 h4 => (f3 a h1 h2 h4).trans (f2 a h1 h3 h4)
  obtain ⟨v4, j4, e4, hj4, gR, gR2, gTB, gVB, g103, g102, g105, g110, g111, o4, f4⟩ :=
    paramsC2_run (τ := τ) v3 (n := n) (Z := Nat.clog 2 (trials n + 1)) (O := outerBlocks n)
      (T := trials n) (S := Nat.clog 2 (drawCount n)) (L := coinSpan A k n) A k
      (by rw [t31 _ (by decide) (by decide) (by decide) (by decide),
        f1 _ (by decide) (by decide), rn])
      (by rw [t31 _ (by decide) (by decide) (by decide) (by decide),
        f1 _ (by decide) (by decide), c.one])
      (by rw [f3 _ (by decide) (by decide) (by decide), l2])
      (by rw [t31 _ (by decide) (by decide) (by decide) (by decide), gOb])
      (by rw [t31 _ (by decide) (by decide) (by decide) (by decide), gTr])
      l3
      (by rw [t31 _ (by decide) (by decide) (by decide) (by decide), gL])
      (by rw [← size_eq_clog]; exact (size_le_self' _).trans (trials_le n))
      (outerBlocks_le n) (trials_le n) (by rw [← seedWidth_eq]; exact seedWidth_le n)
      (coinSpan_le A k n) fit3 hb
  have t41 : ∀ a, 14 ≤ a → (∀ x ∈ paramsC2, a ≠ cell x.dst) → a ≠ cell rSw → a ≠ cell rTmp2 →
      (a < cell 90 ∨ cell 93 < a) → v4.mem a = v1.mem a :=
    fun a h1 h2 h3 h4 h5 => (f4 a h1 h2).trans (t31 a h1 h3 h4 h5)
  refine ⟨v4, j1 + (j2 + (j3 + j4)), e1.seq (e2.seq (e3.seq e4)), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, g105, g110, g111, ?_⟩
  · exact steps_total n k b j1 j2 j3 j4 _ _ hj1 hj2 hj3 hj4 (by omega) (by omega)
  · rw [t41 _ (by decide) (by decide) (by decide) (by decide) (by decide), gN2]
  · rw [t41 _ (by decide) (by decide) (by decide) (by decide) (by decide), gM]
  · rw [t41 _ (by decide) (by decide) (by decide) (by decide) (by decide), gW]
  · rw [t41 _ (by decide) (by decide) (by decide) (by decide) (by decide), gB]
  · rw [t41 _ (by decide) (by decide) (by decide) (by decide) (by decide), gPW]
  · rw [t41 _ (by decide) (by decide) (by decide) (by decide) (by decide), gIn]
  · rw [t41 _ (by decide) (by decide) (by decide) (by decide) (by decide), gDc]
  · rw [t41 _ (by decide) (by decide) (by decide) (by decide) (by decide), gTr]
  · rw [f4 _ (by decide) (by decide), l3, seedWidth_eq]
  · rw [t41 _ (by decide) (by decide) (by decide) (by decide) (by decide), gL]
  · rw [gR, majorityHalf, size_eq_clog]
  · rw [gR2, majorityHalf, size_eq_clog]
  · rw [gTB, seedWidth_eq]
  · exact gVB
  · exact g103
  · exact g102
  · refine ⟨by rw [o4, o3, o2, o1], fun a ha hd _ => ?_⟩
    have m : ∀ r ∈ paramsDirty, a ≠ cell r := hd
    simp only [paramsDirty, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at m
    rw [t41 a ha ?_ ?_ ?_ ?_, f1 a ha ?_]
    · intro x hx
      exact hd x.dst (by revert x; decide)
    · intro x hx
      exact hd x.dst (by revert x; decide)
    · exact hd rSw (by decide)
    · exact hd rTmp2 (by decide)
    · simp only [cell] at m ⊢; omega

end DirectedHamiltonicity.Main.CycleHost


section SolutionBlock
open DirectedHamiltonicity.Main
open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word
open TargetedSamplers.Structured.Interp DirectedHamiltonicity.Main.CycleReduction
open DirectedHamiltonicity.Main.CycleHost
theorem solution {τ : Tapes} {b : ℕ} (u : Store) {n : ℕ} (hn : 2 ≤ n) (D : ℕ)
    (hD : D < drawCount n)
    (c : Consts u) (rn : u.mem (cell rN) = n) (rdv : u.mem (cell rDv) = D)
    (rin : u.mem (cell rIn) = 50 ^ (n * n) * Wmax n ^ (n * 3) * (Bmax n + 1))
    (rbm : u.mem (cell rBm1) = Bmax n + 1) (rpw : u.mem (cell rPW) = Wmax n ^ (n * 3))
    (fit : u.Fits b) (hb : 64 * (n + 1) ^ 3 ≤ b) :
    let d := (rankDraw n).symm ⟨D, hD⟩
    ∃ v j, Exec τ (fun w => w.Fits b) decodeDraw u v j ∧ j ≤ 100 * (b + 1) ^ 2 ∧
      v.mem (cell rS) = d.1.1.val ∧ v.mem (cell rT) = d.1.2.val ∧ v.mem (cell rB) = d.2.2.val ∧
      v.mem (cell rSym) < 50 ^ (n * n) ∧ v.mem (cell rWt) < Wmax n ^ (n * 3) ∧
      (∀ x y : Fin n, v.mem (cell rSym) / 50 ^ (x.val * n + y.val) % 50 = (d.2.1.1 (x, y)).val) ∧
      (∀ (y : Fin n) (l : Fin 3),
        v.mem (cell rWt) / Wmax n ^ (y.val * 3 + l.val) % Wmax n = (d.2.1.2 (y, l)).val) ∧
      Kept decodeDirty u v (fun _ => True) := by
  apply DirectedHamiltonicity.Main.CycleHost.decodeDraw_exec' <;> assumption
end SolutionBlock
