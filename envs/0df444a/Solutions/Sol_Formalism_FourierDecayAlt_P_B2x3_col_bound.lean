-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x3.col_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:42:29.372485+00:00
-- url     : https://prove2.me/submissions/d40892b6-d6eb-4e5c-915f-16fc8649b100

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_hb_form
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_real_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_hb_self_re

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x3
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x3
theorem _root_.solution (z : Fin (k + 1) → ℂ) (hT : (star z ⬝ᵥ (Hb k *ᵥ z)).re < 0) :
    ∃ R : ℝ, ∀ μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, μᴴ * Hb k * μ = Hb k → μ *ᵥ z = z → ∀ i j, ‖μ i j‖ ≤ R := by
  rw [hb_self_re] at hT
  refine ⟨1 + ((∑ j, ‖z j‖) + √(∑ i : Fin k, ‖z i.castSucc‖ ^ 2)) /
    (‖z (Fin.last k)‖ - √(∑ i : Fin k, ‖z i.castSucc‖ ^ 2)), fun μ hμ hz i j => ?_⟩
  have hu : ∀ l, (μ *ᵥ Pi.single j 1) l = μ l j := fun l => by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hHb : ∀ l, (Hb k *ᵥ Pi.single j 1) l = Hb k l j := fun l => by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have key : ∀ w : Fin (k + 1) → ℂ, star (μ *ᵥ w) ⬝ᵥ (Hb k *ᵥ (μ *ᵥ Pi.single j 1)) = star w ⬝ᵥ (Hb k *ᵥ Pi.single j 1) := by
    intro w
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hμ]
  have hHbn : ∀ l, ‖Hb k l j‖ ≤ 1 := by
    intro l
    unfold Hb
    rw [Matrix.diagonal_apply]
    split_ifs <;> simp
  have a1 := key (Pi.single j 1)
  have a2 := key z
  rw [hz] at a2
  have b1 : (star (μ *ᵥ Pi.single j 1) ⬝ᵥ (Hb k *ᵥ (μ *ᵥ Pi.single j 1))).re ≤ 1 := by
    rw [a1]
    have : star (Pi.single j 1 : Fin (k + 1) → ℂ) ⬝ᵥ (Hb k *ᵥ Pi.single j 1) = Hb k j j := by
      rw [← hHb j]
      simp [dotProduct, Pi.single_apply]
    rw [this]
    exact (Complex.re_le_norm _).trans (hHbn j)
  rw [hb_self_re] at b1
  have b2 : ‖star z ⬝ᵥ (Hb k *ᵥ (μ *ᵥ Pi.single j 1))‖ ≤ ∑ j, ‖z j‖ := by
    rw [a2, dotProduct]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
    rw [hHb, norm_mul, Pi.star_apply, norm_star]
    exact mul_le_of_le_one_right (norm_nonneg _) (hHbn l)
  rw [hb_form] at b2
  have := real_bound (μ *ᵥ Pi.single j 1) z _ b1 b2 (by linarith) i
  rwa [hu] at this
end Formalism.FourierDecayAlt.P.B2x3
