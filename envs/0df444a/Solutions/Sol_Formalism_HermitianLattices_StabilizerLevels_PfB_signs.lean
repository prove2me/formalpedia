-- Prove2me | solution 1 for Formalism.HermitianLattices.StabilizerLevels.PfB.signs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:18:48.961802+00:00
-- url     : https://prove2.me/submissions/d815e194-fcfd-4da2-ad94-0d2db3823a68

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_CongruenceTorsion
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferenceStableUnderAction
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferentIdealConditions
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_CongruenceSubgroupTorsionFree
import Theorems.Thm_Formalism_FrobeniusOrbits_Final_cmType
import Theorems.Thm_Formalism_FrobeniusOrbits_HostHyp_toHypOdd
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_FrobeniusOrbits_hostGalSpec
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_HypQD_toHypOdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.StabilizerLevels
open Formalism.HermitianLattices.StabilizerLevels.PfB
open NumberField IntermediateField Ideal IsDedekindDomain nonZeroDivisors
open scoped Pointwise
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition Formalism.HermitianLattices.FiltrationBoundaryCriterion
namespace Formalism.HermitianLattices.StabilizerLevels.PfB
theorem _root_.solution (e q d : ℕ) (hH : HostHyp q d)
    (L : Type) [Field L] [NumberField L] (ζ a b : L) (h : IsLayer (e + 2) q d ζ a b)
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (hσ : galE e ζ a b σ = cc e) (N : ℕ)
    (ξ : hostE ζ a b) (hξ : ξ * ((N : hostE ζ a b) * bE ζ a b) = -1) :
    σ ξ = -ξ ∧ (∀ φ ∈ cmType ζ a b d, 0 < (φ ξ).im) := by
  constructor
  · have hb : σ (bE ζ a b) = - bE ζ a b := by
      have := (hostGalSpec e q d hH.toHypOdd L ζ a b h σ).2.1
      rw [hσ] at this
      apply Subtype.ext
      rw [this]
      simp [cc, c0, bE]
    have h1 := congrArg σ hξ
    simp only [map_mul, map_natCast, hb, map_neg, map_one] at h1
    have hne : ((N : hostE ζ a b) * bE ζ a b) ≠ 0 := by
      intro h0; rw [h0] at hξ; simp at hξ
    have : (σ ξ + ξ) * ((N : hostE ζ a b) * bE ζ a b) = 0 := by linear_combination hξ - h1
    rcases mul_eq_zero.1 this with h2 | h2
    · linear_combination h2
    · exact absurd h2 hne
  · intro φ hφ
    have hb : φ (bE ζ a b) = Complex.I * (Real.sqrt d : ℂ) := hφ
    have h1 := congrArg φ hξ
    simp only [map_mul, map_natCast, hb, map_neg, map_one] at h1
    have h2 := congrArg Complex.re h1
    simp at h2
    have hr : 0 ≤ (N : ℝ) * Real.sqrt d := by positivity
    by_contra hneg
    have hneg' : (φ ξ).im ≤ 0 := not_lt.1 hneg
    have := mul_nonpos_of_nonpos_of_nonneg hneg' hr
    linarith
end Formalism.HermitianLattices.StabilizerLevels.PfB
