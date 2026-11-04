-- Prove2me | solution 1 for DoubleMoralHazard.Baseline.theorem_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T21:43:45.449391+00:00
-- url     : https://prove2.me/submissions/79a77768-4514-40cd-9df9-7bce1b26a365
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DoubleMoralHazard_Baseline_Params
import Definitions.Def_DoubleMoralHazard_Baseline_HJB
import Definitions.Def_DoubleMoralHazard_Baseline_Arrivals
import Definitions.Def_DoubleMoralHazard_Baseline_Contracts
import Definitions.Def_DoubleMoralHazard_Baseline_TenureContracts
import Theorems.Thm_DoubleMoralHazard_Baseline_proposition_1
import Theorems.Thm_DoubleMoralHazard_Baseline_proposition_2
import Theorems.Thm_DoubleMoralHazard_Baseline_gamma_mem_GammaIC

open DoubleMoralHazard.Baseline Set

/-- A maximizer of a function that is extended with slope `-1` beyond `wbar` lies in `[0, wbar]`. -/
private lemma max_le_wbar (F : ℝ → ℝ) (wbar w0 : ℝ) (hw0 : 0 ≤ w0) (hwbar : 0 ≤ wbar)
    (hext : ∀ w, wbar ≤ w → F w = F wbar - (w - wbar))
    (hmax : ∀ w : ℝ, 0 ≤ w → F w ≤ F w0) : w0 ∈ Icc 0 wbar := by
  refine ⟨hw0, ?_⟩
  by_contra h
  rw [not_le] at h
  have h1 := hext w0 h.le
  have h2 := hmax wbar hwbar
  linarith

/-- The comparison step (2.15): any `γ ∈ Γ^IC` is dominated by `F w0` via Proposition 2. -/
private lemma compare (P : Params) (F : ℝ → ℝ) (w0 : ℝ) (γ : Contract) (hγ : γ ∈ GammaIC P)
    (hmax : ∀ w : ℝ, 0 ≤ w → F w ≤ F w0)
    (hP2 : ∀ γ ∈ GammaIC P, ∀ w : ℝ, 0 ≤ w → u P γ sbar = ENNReal.ofReal w → U P γ ≤ F w) :
    U P γ ≤ F w0 := by
  have hfin : u P γ sbar < ⊤ := hγ.2.2
  have hw : u P γ sbar = ENNReal.ofReal (u P γ sbar).toReal :=
    (ENNReal.ofReal_toReal hfin.ne).symm
  exact (hP2 γ hγ _ ENNReal.toReal_nonneg hw).trans (hmax _ ENNReal.toReal_nonneg)

theorem solution (P : Params) :
    (P.c ≤ P.mu * P.p * P.Ru → ∀ F : ℝ → ℝ, IsSol1 P F →
      ∀ w1 : ℝ, 0 ≤ w1 → (∀ w : ℝ, 0 ≤ w → F w ≤ F w1) →
        gamma1 P w1 ∈ GammaIC P ∧ ∀ γ ∈ GammaIC P, U P γ ≤ U P (gamma1 P w1)) ∧
    (P.mu * P.p * P.Ru < P.c ∧ P.c < P.mu * P.Ru → ∀ F : ℝ → ℝ, IsSol2 P F →
      ∀ w2 : ℝ, 0 ≤ w2 → (∀ w : ℝ, 0 ≤ w → F w ≤ F w2) →
        gamma2 P w2 ∈ GammaIC P ∧ ∀ γ ∈ GammaIC P, U P γ ≤ U P (gamma2 P w2)) ∧
    (P.mu * P.Ru ≤ P.c → ∀ F : ℝ → ℝ, IsSol3 P F →
      ∀ w3 : ℝ, 0 ≤ w3 → (∀ w : ℝ, 0 ≤ w → F w ≤ F w3) →
        gamma3 P w3 ∈ GammaIC P ∧ ∀ γ ∈ GammaIC P, U P γ ≤ U P (gamma3 P w3)) := by
  obtain ⟨A1, A2, A3⟩ := proposition_1 P
  obtain ⟨B1, B2, B3⟩ := proposition_2 P
  obtain ⟨C1, C2, C3⟩ := gamma_mem_GammaIC P
  have hr := P.r_pos
  have hmu := P.mu_pos
  have hp := P.p_pos
  have hR := P.Ru_pos
  have hc := P.c_pos
  have hw1 : 0 ≤ P.wbar1 := by unfold Params.wbar1; positivity
  have hw2 : 0 ≤ P.wbar2 := by unfold Params.wbar2; positivity
  have hw3 : 0 ≤ P.wbar3 := by unfold Params.wbar3 Params.wbar2; positivity
  refine ⟨?_, ?_, ?_⟩
  · intro hcase F hF w0 hw0 hmax
    have hmem := max_le_wbar F _ w0 hw0 hw1 hF.2.1 hmax
    refine ⟨C1 hcase w0 hmem, fun γ hγ => ?_⟩
    rw [(A1 hcase F hF w0 hmem).1]
    exact compare P F w0 γ hγ hmax (B1 hcase F hF)
  · intro hcase F hF w0 hw0 hmax
    have hmem := max_le_wbar F _ w0 hw0 hw2 hF.2.1 hmax
    refine ⟨C2 hcase w0 hmem, fun γ hγ => ?_⟩
    rw [(A2 hcase F hF w0 hmem).1]
    exact compare P F w0 γ hγ hmax (B2 hcase F hF)
  · intro hcase F hF w0 hw0 hmax
    have hmem := max_le_wbar F _ w0 hw0 hw3 hF.2.1 hmax
    refine ⟨C3 hcase w0 hmem, fun γ hγ => ?_⟩
    rw [(A3 hcase F hF w0 hmem).1]
    exact compare P F w0 γ hγ hmax (B3 hcase F hF)
