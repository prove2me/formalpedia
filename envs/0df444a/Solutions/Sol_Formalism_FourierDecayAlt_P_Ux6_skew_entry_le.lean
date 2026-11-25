-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux6.skew_entry_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:47:53.098383+00:00
-- url     : https://prove2.me/submissions/1da7a06b-0ae2-4494-8d31-2be3b2912922

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_hpk_conjTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_skewOf_conjTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_entry_le_gN
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Ux6_wMat_mul_apply__b0bdc8c54c6d
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_Rn_13

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux6
variable {k j ρ : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux6
theorem _root_.solution (x : RC k j ρ) (a b : Fin j) : ‖skewOf x.2 a b‖ ≤ B.gN (Rn k j ρ x) := by
  set X := (Matrix.of x.1)ᴴ * Hpk k ρ * Matrix.of x.1 with hXdef
  set W := (-(1 / 2 : ℂ)) • X + skewOf x.2 with hWdef
  have hX : Xᴴ = X := by
    simp only [hXdef, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hpk_conjTranspose, Matrix.mul_assoc]
  have hWh : Wᴴ = (-(1 / 2 : ℂ)) • X - skewOf x.2 := by
    simp only [hWdef, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hX, skewOf_conjTranspose]
    have : star (-(1 / 2 : ℂ)) = -(1 / 2 : ℂ) := by simp
    rw [this]; abel
  have hS : skewOf x.2 = (1 / 2 : ℂ) • (W - Wᴴ) := by
    rw [hWh, hWdef]; module
  have hWe : ∀ a b : Fin j, ‖W a b‖ ≤ B.gN (Rn k j ρ x) := by
    intro a b
    have h1 : W a b = (G.wMat j * W) a.rev b := by rw [wMat_mul_apply', Fin.rev_rev]
    rw [h1, ← Rn_13]
    exact entry_le_gN _ _ _
  have he : skewOf x.2 a b = (1 / 2 : ℂ) * (W a b - star (W b a)) := by
    rw [hS]; simp [Matrix.conjTranspose_apply]
  rw [he, norm_mul]
  have h2 : ‖W a b - star (W b a)‖ ≤ ‖W a b‖ + ‖W b a‖ := by
    calc ‖W a b - star (W b a)‖ ≤ ‖W a b‖ + ‖star (W b a)‖ := norm_sub_le _ _
      _ = ‖W a b‖ + ‖W b a‖ := by rw [norm_star]
  have h3 := hWe a b
  have h4 := hWe b a
  have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  rw [this]
  linarith
end Formalism.FourierDecayAlt.P.Ux6
