-- Prove2me | solution 1 for FoundationsRL.E2DStructured.ucb_certifies_dec_zero
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T04:10:31.494225+00:00
-- url     : https://prove2.me/submissions/bd016c6a-8d1f-41e2-bdde-5106f9743d4d

import Mathlib
import Definitions.Def_FoundationsRL_E2DStructured_IsRewardClass
import Definitions.Def_FoundationsRL_E2DStructured_decHull
import Definitions.Def_FoundationsRL_E2DStructured_decGame
import Definitions.Def_FoundationsRL_E2DStructured_upperConf
import Definitions.Def_FoundationsRL_E2DStructured_lowerConf
import Definitions.Def_FoundationsRL_E2DStructured_pointMass

open MeasureTheory
open scoped ENNReal

open FoundationsRL.E2DStructured in
theorem solution {D : Type*} [MeasurableSpace D] (G : Set (D → ℝ))
    (hG : IsRewardClass G)
    (hbddAbove : ∀ π, BddAbove ((fun f : D → ℝ => f π) '' G))
    (hbddBelow : ∀ π, BddBelow ((fun f : D → ℝ => f π) '' G))
    (πt : D) (hπt : ∀ π, upperConf G π ≤ upperConf G πt) :
    (∀ fhat : D → ℝ, decGame 0 G fhat (pointMass πt) ≤
        ((upperConf G πt - lowerConf G πt : ℝ) : EReal)) ∧
      decHull 0 G ≤ ((upperConf G πt - lowerConf G πt : ℝ) : EReal) := by
  haveI : Nonempty D := ⟨πt⟩
  have key : ∀ fhat : D → ℝ, decGame 0 G fhat (pointMass πt) ≤
      ((upperConf G πt - lowerConf G πt : ℝ) : EReal) := by
    intro fhat
    unfold decGame
    refine iSup₂_le fun f hf => ?_
    obtain ⟨hfm, π₀, hπ₀⟩ := hG f hf
    have hM : maxValue f = f π₀ := by
      unfold maxValue
      exact le_antisymm (ciSup_le hπ₀) (le_ciSup ⟨f π₀, by rintro _ ⟨π, rfl⟩; exact hπ₀ π⟩ π₀)
    have hU0 : f π₀ ≤ upperConf G π₀ :=
      le_csSup (hbddAbove π₀) ⟨f, hf, rfl⟩
    have hL : lowerConf G πt ≤ f πt :=
      csInf_le (hbddBelow πt) ⟨f, hf, rfl⟩
    have hU := hπt π₀
    have hge : f πt ≤ f π₀ := hπ₀ πt
    have m1 : Measurable fun π => ENNReal.ofReal (maxValue f - f π) :=
      ENNReal.measurable_ofReal.comp (measurable_const.sub hfm)
    unfold decObjective expectedGap
    rw [EReal.coe_zero, zero_mul, sub_zero]
    unfold pointMass
    simp only [ProbabilityMeasure.coe_mk]
    rw [lintegral_dirac' πt m1, EReal.coe_ennreal_ofReal, hM, max_eq_left (by linarith),
      EReal.coe_le_coe_iff]
    linarith
  refine ⟨key, ?_⟩
  unfold decHull
  refine iSup₂_le fun fhat _ => ?_
  unfold dec
  exact (iInf_le _ _).trans (key fhat)
