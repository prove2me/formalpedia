-- Prove2me | solution 1 for Formalism.L2.Th1.B.E2.det_rows
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:04:09.6791+00:00
-- url     : https://prove2.me/submissions/64974bba-a1f7-4af5-92ef-1c1c10504f36

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffLawWithInverseThree
import Theorems.Thm_Formalism_G_LogP_hs2
import Theorems.Thm_Formalism_G_LogP_hs3
import Theorems.Thm_Formalism_G_LogP_psubst_subst
import Theorems.Thm_Formalism_G_LogP_subst2_subst
import Theorems.Thm_Formalism_G_LogP_subst_XX
import Theorems.Thm_P2M_Formalism_G_LogP_subst_zero__b4a287294211


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.E2
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob in3)
open Formalism.G.LogP (hs2 hs3 subst2_subst psubst_subst subst_XX subst_zero')
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Th1.B.E2
theorem _root_.solution {R : Type} [CommRing R] (x L A B e : Fin 3 → R) (c0 a1 a3 : R)
    (h2 : ∀ j, x j ^ 2 * A j = L j ^ 2 * (e j + c0 * x j ^ 2))
    (h3 : ∀ j, x j ^ 3 * B j = L j ^ 3 * (-2 * e j + a1 * x j * e j + a3 * x j ^ 3)) :
    (x 0 * x 1 * x 2) ^ 3 * Matrix.det (Matrix.of fun j => ![L j ^ 3, L j * A j, B j]) =
      2 * (L 0 * L 1 * L 2) ^ 3 *
        Matrix.det (Matrix.of fun j => ![x j ^ 3, x j * e j, -e j]) := by
  have hA : ∀ j, x j ^ 3 * (L j * A j) = L j ^ 3 * (x j * e j + c0 * x j ^ 3) := fun j => by
    linear_combination (x j * L j) * h2 j
  have d1 : Matrix.det (Matrix.of fun j => ![L j ^ 3, L j * A j, B j]) =
      L 0 ^ 3 * (L 1 * A 1) * B 2 - L 0 ^ 3 * B 1 * (L 2 * A 2) - L 0 * A 0 * L 1 ^ 3 * B 2 +
        L 0 * A 0 * B 1 * L 2 ^ 3 + B 0 * L 1 ^ 3 * (L 2 * A 2) - B 0 * (L 1 * A 1) * L 2 ^ 3 := by
    rw [Matrix.det_fin_three]; rfl
  have d2 : Matrix.det (Matrix.of fun j => ![x j ^ 3, x j * e j, -e j]) =
      x 0 ^ 3 * (x 1 * e 1) * -e 2 - x 0 ^ 3 * -e 1 * (x 2 * e 2) - x 0 * e 0 * x 1 ^ 3 * -e 2 +
        x 0 * e 0 * -e 1 * x 2 ^ 3 + -e 0 * x 1 ^ 3 * (x 2 * e 2) - -e 0 * (x 1 * e 1) * x 2 ^ 3 := by
    rw [Matrix.det_fin_three]; rfl
  rw [d1, d2]
  calc _ = (x 0 ^ 3 * L 0 ^ 3) * (x 1 ^ 3 * (L 1 * A 1)) * (x 2 ^ 3 * B 2) -
        (x 0 ^ 3 * L 0 ^ 3) * (x 1 ^ 3 * B 1) * (x 2 ^ 3 * (L 2 * A 2)) -
        (x 0 ^ 3 * (L 0 * A 0)) * (x 1 ^ 3 * L 1 ^ 3) * (x 2 ^ 3 * B 2) +
        (x 0 ^ 3 * (L 0 * A 0)) * (x 1 ^ 3 * B 1) * (x 2 ^ 3 * L 2 ^ 3) +
        (x 0 ^ 3 * B 0) * (x 1 ^ 3 * L 1 ^ 3) * (x 2 ^ 3 * (L 2 * A 2)) -
        (x 0 ^ 3 * B 0) * (x 1 ^ 3 * (L 1 * A 1)) * (x 2 ^ 3 * L 2 ^ 3) := by ring
    _ = _ := by rw [hA 0, hA 1, hA 2, h3 0, h3 1, h3 2]; ring
end Formalism.L2.Th1.B.E2
