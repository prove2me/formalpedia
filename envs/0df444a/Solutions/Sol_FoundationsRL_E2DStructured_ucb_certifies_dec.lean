-- Prove2me | solution 1 for FoundationsRL.E2DStructured.ucb_certifies_dec
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T02:46:15.800766+00:00
-- url     : https://prove2.me/submissions/bb3a446e-d6d8-4e13-a8e3-2625b399f8e6

import Mathlib
import Definitions.Def_FoundationsRL_E2DStructured_IsRewardClass
import Definitions.Def_FoundationsRL_E2DStructured_dec
import Definitions.Def_FoundationsRL_E2DStructured_upperConf
import Definitions.Def_FoundationsRL_E2DStructured_pointMass

open MeasureTheory
open scoped ENNReal

open FoundationsRL.E2DStructured in
theorem solution {D : Type*} [MeasurableSpace D] (G : Set (D → ℝ))
    (hG : IsRewardClass G)
    (hbddAbove : ∀ π, BddAbove ((fun f : D → ℝ => f π) '' G))
    (γ : ℝ) (hγ : 0 < γ) (fhat : D → ℝ) (hfhat : Measurable fhat)
    (πt : D) (hπt : ∀ π, upperConf G π ≤ upperConf G πt) :
    decGame γ G fhat (pointMass πt) ≤ ((upperConf G πt - fhat πt + 1 / (4 * γ) : ℝ) : EReal) ∧
      dec γ G fhat ≤ ((upperConf G πt - fhat πt + 1 / (4 * γ) : ℝ) : EReal) := by
  haveI : Nonempty D := ⟨πt⟩
  have key : decGame γ G fhat (pointMass πt) ≤
      ((upperConf G πt - fhat πt + 1 / (4 * γ) : ℝ) : EReal) := by
    unfold decGame
    refine iSup₂_le fun f hf => ?_
    obtain ⟨hfm, π₀, hπ₀⟩ := hG f hf
    have hM : maxValue f = f π₀ := by
      unfold maxValue
      exact le_antisymm (ciSup_le hπ₀) (le_ciSup ⟨f π₀, by rintro _ ⟨π, rfl⟩; exact hπ₀ π⟩ π₀)
    have hU0 : f π₀ ≤ upperConf G π₀ :=
      le_csSup (hbddAbove π₀) ⟨f, hf, rfl⟩
    have hU := hπt π₀
    have hge : f πt ≤ f π₀ := hπ₀ πt
    have m1 : Measurable fun π => ENNReal.ofReal (maxValue f - f π) :=
      ENNReal.measurable_ofReal.comp (measurable_const.sub hfm)
    have m2 : Measurable fun π => ENNReal.ofReal ((f π - fhat π) ^ 2) :=
      ENNReal.measurable_ofReal.comp ((hfm.sub hfhat).pow_const 2)
    unfold decObjective expectedGap sqError pointMass
    simp only [ProbabilityMeasure.coe_mk]
    rw [lintegral_dirac' πt m1, lintegral_dirac' πt m2, EReal.coe_ennreal_ofReal,
      EReal.coe_ennreal_ofReal, hM]
    rw [max_eq_left (by linarith), max_eq_left (sq_nonneg _)]
    rw [← EReal.coe_mul, ← EReal.coe_sub, EReal.coe_le_coe_iff]
    have h4 : 0 ≤ (2 * γ * (fhat πt - f πt) - 1) ^ 2 / (4 * γ) := by positivity
    have h5 : (fhat πt - f πt) - γ * (f πt - fhat πt) ^ 2 ≤ 1 / (4 * γ) := by
      have : 1 / (4 * γ) - ((fhat πt - f πt) - γ * (f πt - fhat πt) ^ 2)
          = (2 * γ * (fhat πt - f πt) - 1) ^ 2 / (4 * γ) := by
        field_simp <;> ring
      linarith
    linarith
  exact ⟨key, (iInf_le _ _).trans key⟩
