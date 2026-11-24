-- Prove2me | solution 1 for CompanionTheory.D.DSIC.qminor_intertwine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:14:31.204263+00:00
-- url     : https://prove2.me/submissions/d6492e2e-d739-4b95-a0e1-ae230847a57b

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QnCovDet
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QnCovLin
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_Spread
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
open Matrix Finset
open scoped InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.DSIC
open Formalism.REAL Formalism.FourierDecayAlt.Q
namespace CompanionTheory.D.DSIC
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] {n t : ℕ} (τ : Module.End ℂ V)
    (E E' : Fin n → Fin n → Module.End ℂ V) (h : ∀ a b, τ * E a b = E' a b * τ) (a b : Fin t → Fin n) (u : ℂ) :
    τ * qminor E a b u = qminor E' a b u * τ := by
  simp only [qminor, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← mul_assoc, ← (Int.cast_commute _ τ).eq, mul_assoc, mul_assoc]
  congr 1
  rw [List.ofFn_eq_map, List.ofFn_eq_map]
  induction List.finRange t with
  | nil => simp
  | cons k l ih =>
    have hk : τ * Tm E (u - k) (a (σ k)) (b k) = Tm E' (u - k) (a (σ k)) (b k) * τ := by
      simp only [Tm, mul_add, add_mul, h]
      split_ifs
      · rw [Algebra.commutes]
      · simp
    simp only [List.map_cons, List.prod_cons]
    rw [← mul_assoc, hk, mul_assoc, ih, mul_assoc]
end CompanionTheory.D.DSIC
