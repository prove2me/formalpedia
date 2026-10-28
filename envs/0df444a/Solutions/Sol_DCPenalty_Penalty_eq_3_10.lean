-- Prove2me | solution 1 for DCPenalty.Penalty.eq_3_10
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T16:22:23.38168+00:00
-- url     : https://prove2.me/submissions/ecab2df9-e4a2-4213-a0ac-efb2639844ec

import Mathlib
import Definitions.Def_ClarkeGradients_MaxFunctions_HasOneSidedDirDeriv
import Definitions.Def_DCPenalty_Penalty_Problem
import Definitions.Def_DCPenalty_Penalty_Stationarity
import Definitions.Def_DCPenalty_Penalty_Algorithm

open Filter Topology

open DCPenalty.Penalty in
theorem AuxEq310_remark {n m : ℕ} (P : DCProblem n m) (hP : P.Standing) {ε : ℝ} (hε : 0 < ε)
    {xbar : EuclideanSpace ℝ (Fin n)} (hxbar : xbar ∈ P.X) :
    ∀ᶠ x in 𝓝[P.X] xbar, P.Jact 0 xbar ⊆ P.J0eps ε x ∧ P.Jtup xbar ⊆ P.Jeps ε x := by
  have hS : xbar ∈ P.S := hP.X_subset_S hxbar
  have hψc : ∀ i j, ContinuousAt (P.ψ i j) xbar := fun i j =>
    ((hP.ψ_C1 i j).continuousOn).continuousAt (hP.isOpen_S.mem_nhds hS)
  have hpsic : ∀ i, ContinuousAt (P.psi i) xbar := by
    intro i
    unfold DCProblem.psi
    exact ContinuousAt.finset_sup'_apply _ (fun j _ => hψc i j)
  have key : ∀ i (j : Fin (P.J i)), ∀ᶠ x in 𝓝 xbar,
      P.psi i xbar = P.ψ i j xbar → P.psi i x ≤ P.ψ i j x + ε := by
    intro i j
    have hc : ContinuousAt (fun x => P.psi i x - P.ψ i j x) xbar := (hpsic i).sub (hψc i j)
    by_cases h : P.psi i xbar = P.ψ i j xbar
    · have hlt : P.psi i xbar - P.ψ i j xbar < ε := by rw [h, sub_self]; exact hε
      filter_upwards [hc.eventually (gt_mem_nhds hlt)] with x hx _
      linarith
    · exact Eventually.of_forall fun x h' => absurd h' h
  have hall : ∀ᶠ x in 𝓝 xbar, ∀ i (j : Fin (P.J i)),
      P.psi i xbar = P.ψ i j xbar → P.psi i x ≤ P.ψ i j x + ε :=
    eventually_all.mpr fun i => eventually_all.mpr fun j => key i j
  filter_upwards [nhdsWithin_le_nhds hall] with x hx
  refine ⟨fun j hj => hx 0 j hj, fun jj hjj i => hx i.succ (jj i) (hjj i)⟩

open DCPenalty.Penalty in
theorem solution {n m : ℕ} (P : DCProblem n m) (hP : P.Standing)
    {p ε ρ0 σ : ℝ} {η : ℕ → ℝ} {x : ℕ → EuclideanSpace ℝ (Fin n)}
    (hrun : P.IsPenaltyRun p ε ρ0 σ η x)
    {K : ℕ → ℕ} (hK : StrictMono K) {xinf : EuclideanSpace ℝ (Fin n)}
    (hlim : Tendsto (x ∘ K) atTop (𝓝 xinf)) :
    ∀ᶠ k in atTop, ∀ j0 ∈ P.Jact 0 xinf, ∀ jj ∈ P.Jtup xinf, ∀ y ∈ P.X,
      P.Frho p (ρ0 * σ ^ (K k)) (x (K k)) - η (K k) ≤
        P.Qrho p (ρ0 * σ ^ (K k)) (x (K k)) j0 jj y := by
  have hε : 0 < ε := hrun.1
  have hxX : ∀ k, x k ∈ P.X := hrun.2.2.2.2.2.2.1
  have hmain := hrun.2.2.2.2.2.2.2
  have hxinf : xinf ∈ P.X :=
    hP.isClosed_X.mem_of_tendsto hlim (Eventually.of_forall fun k => hxX (K k))
  have hlim' : Tendsto (x ∘ K) atTop (𝓝[P.X] xinf) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall fun k => hxX (K k)⟩
  have hev := hlim'.eventually (AuxEq310_remark P hP hε hxinf)
  filter_upwards [hev] with k hk
  intro j0 hj0 jj hjj y hy
  have := hmain (K k) j0 (hk.1 hj0) jj (hk.2 hjj) y hy
  linarith
