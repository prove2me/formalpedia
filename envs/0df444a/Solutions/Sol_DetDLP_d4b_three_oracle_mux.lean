-- Prove2me | solution 1 for DetDLP.d4b_three_oracle_mux
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T07:45:58.100247+00:00
-- url     : https://prove2.me/submissions/3db33a73-6b09-47a5-9b4b-b069ffbf1ca9

import Definitions.Def_DetDLP_W1_Pipeline
import Theorems.Thm_DetDLP_m89_resettable_machine

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace DetDLP DetDLP.MachineComposition

namespace DetDLP.D4BTaggedMux
noncomputable section

def sim (A : PrimitiveMachine) (o : Fin A.tapeCount) (R : PrimitiveMachine) (K : ℕ) :=
  ∀ (x y : List Bool) (t s : ℝ), RunsWithin A o x y t s →
    RunsWithin R R.inputTape x y (K*(t+x.length+1)) (K*(s+x.length+1))

theorem normalize (A : PrimitiveMachine) (o : Fin A.tapeCount) : ∃ R K, sim A o R K := by
  obtain ⟨R,c,hc,H⟩ := m89_resettable_machine A o
  refine ⟨R,c*(2*A.tapeCount+3)+R.tapeCount*(2*c+1),?_⟩
  intro x y t s h
  obtain ⟨m,z,hm,hz,hy,mt,zs⟩ := (runsWithin_iff_final_space ..).mp h
  have ht := (Nat.cast_nonneg m).trans mt
  have hs := (Nat.cast_nonneg (visitedSpace z)).trans zs
  have hactual := (runsWithin_iff_final_space ..).mpr ⟨m,z,hm,hz,hy,mt,(le_refl (visitedSpace z : ℝ))⟩
  obtain ⟨n,B,d,hn,hh,ho,_,_,hnt,hB,hbox⟩ := H x y t (visitedSpace z) ht (Nat.cast_nonneg _) hactual
  have htime : (visitedSpace z : ℝ) ≤ (A.tapeCount : ℝ)*(x.length+2*(m:ℝ)+1) := by exact_mod_cast locatedTrace_space_le_of_length hm
  have hspace : visitedSpace d ≤ R.tapeCount*(2*B+1) := by
    unfold visitedSpace
    calc
      _ ≤ ∑ _ : Fin R.tapeCount, (2*B+1) := by
        apply Finset.sum_le_sum; intro i _; have := hbox i; omega
      _ = _ := by simp
  apply (runsWithin_iff_final_space ..).mpr
  refine ⟨n,d,hn,hh,ho,hnt.trans ?_,?_⟩
  · push_cast
    calc
      _ ≤ c*((2*(A.tapeCount:ℝ)+3)*(t+x.length+1)) := by
        gcongr
        have h' : (visitedSpace z : ℝ) ≤ (A.tapeCount:ℝ)*(x.length+2*t+1) := htime.trans (by gcongr)
        nlinarith only [h', ht, (Nat.cast_nonneg A.tapeCount (α:=ℝ)), (Nat.cast_nonneg x.length (α:=ℝ)),
          mul_nonneg (Nat.cast_nonneg A.tapeCount (α:=ℝ)) (Nat.cast_nonneg x.length (α:=ℝ))]
      _ ≤ _ := by rw [← mul_assoc]; apply mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) (by positivity)
  · have hh' : (visitedSpace d : ℝ) ≤ (R.tapeCount : ℝ)*(2*(B:ℝ)+1) := by exact_mod_cast hspace
    push_cast
    apply hh'.trans
    calc
      _ ≤ R.tapeCount*((2*(c:ℝ)+1)*(s+x.length+1)) := by
        gcongr
        have h' : (B:ℝ) ≤ (c:ℝ)*(s+1) := hB.trans (by gcongr)
        nlinarith only [h', hs, (Nat.cast_nonneg x.length (α:=ℝ)), mul_nonneg (Nat.cast_nonneg c (α:=ℝ)) (Nat.cast_nonneg x.length (α:=ℝ))]
      _ ≤ _ := by rw [← mul_assoc]; apply mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity)) (by positivity)

open DetDLP_W1_Pipeline

def positionProgram (A : PrimitiveMachine) {N : ℕ} (i : Fin N) (h : A.tapeCount ≤ N) : Program N :=
  let B := addTapes A (N-A.tapeCount)
  let e : Fin B.tapeCount ≃ Fin N := finCongr (Nat.add_sub_of_le h)
  PermutedTapes.program (.ofMachine B) (e.trans (Equiv.swap (e B.inputTape) i))

theorem position_run (A : PrimitiveMachine) {N : ℕ} (i : Fin N) (h : A.tapeCount ≤ N)
    {x y : List Bool} {t s : ℝ} (ha : RunsWithin A A.inputTape x y t s) :
    RunsWithin ((positionProgram A i h).machine i) i x y t (s+(N-A.tapeCount : ℕ)) := by
  let B := addTapes A (N-A.tapeCount)
  let P := Program.ofMachine B
  let e₀ : Fin B.tapeCount ≃ Fin N := finCongr (Nat.add_sub_of_le h)
  let e := e₀.trans (Equiv.swap (e₀ B.inputTape) i)
  have he : e B.inputTape = i := by simp [e]
  have hiff (j : Fin N) : e.symm j = B.inputTape ↔ j = i := by rw [← he]; exact e.symm_apply_eq
  obtain ⟨n,z,seg,hh,ho,ht⟩ := (runsWithin_iff_segment ..).mp (runsWithin_addTapes (N-A.tapeCount) ha)
  let mv := PermutedTapes.positioned P e B.inputTape i
  have init : mv (locatedInit B x) = locatedInit ((positionProgram A i h).machine i) x := by
    unfold mv PermutedTapes.positioned PermutedTapes.positionedCfg locatedInit PrimitiveMachine.init
    simp only [Function.comp_def, hiff]; rfl
  have seg' := PermutedTapes.positioned_segment P e B.inputTape i seg
  change Segment _ (mv _) (mv _) _ _ at seg'
  rw [init] at seg'
  apply (runsWithin_iff_segment ..).mpr
  refine ⟨n,mv z,seg',hh,?_,ht⟩
  exact (congrArg (fun j : Fin N => (mv z).config.tapes j) he.symm).trans
    ((PermutedTapes.positioned_tapes P e B.inputTape i z B.inputTape).trans ho)

section Tag
variable {N : ℕ} (P : Bool → Program N) (i : Fin N)
abbrev Ctrl := Unit ⊕ (Bool ⊕ ((b : Bool) × Fin (P b).stateCount))
abbrev addr (q : Ctrl P) := Fintype.equivFin (Ctrl P) q
abbrev sub (b : Bool) (q : Fin (P b).stateCount) : Fin (Fintype.card (Ctrl P)) := addr P (.inr (.inr ⟨b,q⟩))
abbrev nextState (b : Bool) (r : Bool ⊕ (Fin (P b).stateCount × Turing.TM0.Stmt (Option Bool))) :=
  r.map id (Prod.map (sub P b) id)

def tagged : PrimitiveMachine where
  tapeCount := N
  stateCount := Fintype.card (Ctrl P)
  inputTape := i
  start := addr P (.inl ())
  scan j := match (Fintype.equivFin (Ctrl P)).symm j with
    | .inr (.inr ⟨b,q⟩) => (P b).scan q
    | _ => i
  transition j s := match (Fintype.equivFin (Ctrl P)).symm j with
    | .inl () => .inr (addr P (.inr (.inl (s.getD false))), .write none)
    | .inr (.inl b) => .inr (sub P b (P b).start,.move .right)
    | .inr (.inr ⟨b,q⟩) => nextState P b ((P b).transition q s)

def emb (b : Bool) (c : LocatedCfg ((P b).machine i)) : LocatedCfg (tagged P i) :=
  ⟨⟨c.config.state.map id (sub P b),c.config.tapes⟩,c.position,c.lower,c.upper⟩

theorem emb_step (b : Bool) {c d : LocatedCfg ((P b).machine i)} (hs : locatedStep _ c = some d) :
    locatedStep _ (emb P i b c) = some (emb P i b d) := by
  rcases c with ⟨⟨s,tapes⟩,pos,lo,hi⟩
  cases s with
  | inl z => simp [locatedStep,PrimitiveMachine.step] at hs
  | inr q =>
    cases ht : (P b).transition q (tapes ((P b).scan q)).head with
    | inl z =>
      simp [locatedStep,PrimitiveMachine.step,LocatedCfg.monitor,Program.machine,ht] at hs
      subst d; simp [locatedStep,PrimitiveMachine.step,LocatedCfg.monitor,emb,tagged,sub,addr,ht,nextState]
    | inr qa =>
      obtain ⟨q',act⟩ := qa
      cases act <;> simp [locatedStep,PrimitiveMachine.step,LocatedCfg.monitor,Program.machine,ht] at hs <;>
        subst d <;> simp [locatedStep,PrimitiveMachine.step,LocatedCfg.monitor,emb,tagged,sub,addr,ht,nextState]

private theorem erase_move (b : Bool) (x : List Bool) :
    (((Turing.Tape.mk₁ ((b :: x).map some)).write none).move .right) =
      Turing.Tape.mk₁ (x.map some) := by
  change Turing.Tape.mk _ ((Turing.ListBlank.mk ([] : List (Option Bool))).cons none) _ = _
  have h : (Turing.ListBlank.mk ([] : List (Option Bool))).cons none = Turing.ListBlank.mk [] := by
    exact Quotient.sound' (Or.inr ⟨1,rfl⟩)
  rw [h]; rfl

private theorem enter (b : Bool) (x : List Bool) :
    ∃ entry, Computation.Trace (locatedStep (tagged P i)) 2 (locatedInit _ (b::x)) entry ∧
      entry.config = (emb P i b (locatedInit _ x)).config := by
  let M := tagged P i
  let start := locatedInit M (b :: x)
  let t := start.config.tapes
  let wr := Function.update t i ((t i).write none)
  let c₁ : M.Cfg := ⟨.inr (addr P (.inr (.inl b))), wr⟩
  let d₁ := start.monitor c₁
  let c₂ : M.Cfg := ⟨.inr (sub P b (P b).start), Function.update wr i ((wr i).move .right)⟩
  let d₂ := d₁.monitor c₂
  have hhead : (t i).head = some b := by simp [t,start,locatedInit,PrimitiveMachine.init,M,tagged]; rfl
  have h₁ : M.step start.config = some c₁ := by
    change (tagged P i).step ⟨.inr (addr P (.inl ())),t⟩ = some c₁
    simp [PrimitiveMachine.step,tagged,addr,hhead,c₁,wr]
  have hcfg₁ : d₁.config = c₁ := by
    change ((⟨⟨.inr (addr P (.inl ())),t⟩,_,_,_⟩ : LocatedCfg (tagged P i)).monitor c₁).config = c₁
    simp [LocatedCfg.monitor,tagged,addr]
  have h₂ : M.step d₁.config = some c₂ := by
    rw [hcfg₁]; simp [PrimitiveMachine.step,c₁,M,tagged,addr,c₂]
  refine ⟨d₂,.cons (show (M.step start.config).map start.monitor = _ by rw [h₁]; rfl)
    (.cons (show (M.step d₁.config).map d₁.monitor = _ by rw [h₂]; rfl) (.refl _)),?_⟩
  have hcfg₂ : d₂.config = c₂ := by
    simp only [d₂,LocatedCfg.monitor,hcfg₁,c₁,M,tagged,addr,Equiv.symm_apply_apply,Sum.elim_inr]
  rw [hcfg₂]; change (⟨_,_⟩ : M.Cfg) = ⟨_,_⟩
  congr 1; funext j
  by_cases h : j = i
  · subst j; simpa [c₂,wr,t,start,locatedInit,PrimitiveMachine.init,M,emb,tagged,Program.machine]
      using erase_move b x
  · simp [wr,t,start,locatedInit,PrimitiveMachine.init,M,tagged,Program.machine,h]

theorem tagged_run (b : Bool) {x y : List Bool} {t s : ℝ}
    (hr : RunsWithin ((P b).machine i) i x y t s) :
    RunsWithin (tagged P i) i (b :: x) y (t+2) (N*(x.length+6)+s) := by
  obtain ⟨n,z,sg,⟨v,hv⟩,ho,ht⟩ := (runsWithin_iff_segment ..).mp hr
  obtain ⟨d,tr,hd⟩ := enter P i b x
  let f := emb P i b
  have sg' : Segment (tagged P i) (f (locatedInit _ x)) (f z) n s :=
    segment_iff_final_space.mpr ⟨MachineComposition.Trace.map f (fun _ _ => emb_step P i b) sg.1,
      (segment_iff_final_space.mp sg).2⟩
  obtain ⟨w,hw,rest⟩ := DetDLP_W1_SavedCall.RelativeMonitor.call
    (locatedWellFormed_reachable tr) hd (fun _ => rfl) (originCovered_init ((P b).machine i) x) sg'
  apply (runsWithin_iff_final_space ..).mpr
  refine ⟨2+n,w,MachineComposition.Trace.append tr rest.1,⟨v,?_⟩,?_,by push_cast; linarith,?_⟩
  · rw [hw]; change z.config.state.map id (sub P b) = _; rw [hv]; rfl
  · rw [hw]; exact ho
  · apply (segment_iff_final_space.mp rest).2.trans
    gcongr; exact_mod_cast locatedTrace_space_le_of_length tr

end Tag
end
end DetDLP.D4BTaggedMux

open DetDLP.D4BTaggedMux in
open DetDLP_W1_Pipeline in
theorem solution (A : Fin 3 → PrimitiveMachine) (o : ∀ j, Fin (A j).tapeCount) :
    ∃ (M : PrimitiveMachine) (K : ℕ), ∀ (j : Fin 3) (x y : List Bool) (t s : ℝ),
      RunsWithin (A j) (o j) x y t s →
      RunsWithin M M.inputTape (if j = 0 then false :: x else true :: decide (j = 2) :: x) y
        (K * (t + x.length + 1)) (K * (s + x.length + 1)) := by
  classical
  choose R k H using (fun j => normalize (A j) (o j))
  let N := (∑ j, (R j).tapeCount) + 1
  let k₀ := ∑ j, k j
  let i : Fin N := ⟨0, Nat.zero_lt_succ _⟩
  have hsum : ∀ j : Fin 3, (R j).tapeCount ≤ ∑ a, (R a).tapeCount := fun j => Finset.single_le_sum
    (f := fun a => (R a).tapeCount) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have hN (j : Fin 3) : (R j).tapeCount ≤ N := Nat.le_succ_of_le (hsum j)
  have hk (j : Fin 3) : k j ≤ k₀ := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  let P (j : Fin 3) := positionProgram (R j) i (hN j)
  let Q (b : Bool) := if b then P 2 else P 1
  let L (b : Bool) : Program N := if b then Program.ofMachine (tagged Q i) else P 0
  have htagN : (tagged Q i).tapeCount = N := by rfl
  have hNN : (N : ℝ) ≤ ((tagged Q i).tapeCount : ℝ) := by rw [htagN]
  refine ⟨tagged L i,k₀+20*N+4,?_⟩
  intro j x y t s h
  obtain ⟨n,z,_,_,_,hnt,hsz⟩ := (runsWithin_iff_final_space ..).mp h
  have ht : 0 ≤ t := (Nat.cast_nonneg n).trans hnt
  have hs : 0 ≤ s := (Nat.cast_nonneg (visitedSpace z)).trans hsz
  let τ := (k₀:ℝ)*(t+x.length+1)
  let σ := (k₀:ℝ)*(s+x.length+1)
  have ha : RunsWithin ((P j).machine i) i x y τ (σ+N) := by
    apply runsWithin_mono (position_run (R j) i (hN j) (H j x y t s h))
    · unfold τ; gcongr; exact_mod_cast hk j
    · unfold σ; gcongr
      · exact_mod_cast hk j
      · exact_mod_cast Nat.sub_le N (R j).tapeCount
  have hb : RunsWithin (tagged L i) i (if j = 0 then false :: x else true :: decide (j = 2) :: x) y
      (τ+4) (N*((x.length:ℝ)+7)+(N*((x.length:ℝ)+6)+(σ+N))) := by
    fin_cases j
    · exact runsWithin_mono (tagged_run L i false ha) (by linarith) (by push_cast; linarith [show 0 ≤ (N:ℝ)*(x.length+7) by positivity])
    · exact runsWithin_mono (tagged_run L i true (tagged_run Q i false ha)) (by linarith)
        (by simp; ring_nf; nlinarith [Nat.cast_nonneg (α:=ℝ) N, Nat.cast_nonneg (α:=ℝ) x.length])
    · exact runsWithin_mono (tagged_run L i true (tagged_run Q i true ha)) (by linarith)
        (by simp; ring_nf; nlinarith [Nat.cast_nonneg (α:=ℝ) N, Nat.cast_nonneg (α:=ℝ) x.length])
  apply runsWithin_mono hb <;> push_cast <;> dsimp only [τ,σ]
  · nlinarith only [ht,Nat.cast_nonneg (α:=ℝ) x.length,Nat.cast_nonneg (α:=ℝ) N,
      mul_nonneg (Nat.cast_nonneg (α:=ℝ) N) (by positivity : 0 ≤ t+x.length)]
  · nlinarith only [hs,Nat.cast_nonneg (α:=ℝ) x.length,Nat.cast_nonneg (α:=ℝ) N,
      mul_nonneg (Nat.cast_nonneg (α:=ℝ) N) hs,
      mul_nonneg (Nat.cast_nonneg (α:=ℝ) N) (Nat.cast_nonneg (α:=ℝ) x.length)]
