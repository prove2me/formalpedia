-- Prove2me | solution 1 for Formalism.L2.Col.sub_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:51:43.945706+00:00
-- url     : https://prove2.me/submissions/47e4bbfd-8ccb-46fb-9aa8-4401de0009d9

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Columns_GenericUnipotentCharacter
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DimensionMassJointBound
import Definitions.Def_Formalism_LocalToGlobal_Columns_LevGCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset IsDedekindDomain NumberField
open Formalism Formalism.L2 Formalism.L2.Col
variable {n : ℕ} {κ : Type} [CommRing κ] {K : Type} [Field K]
namespace Formalism.L2.Col
theorem _root_.solution {s : ℕ} (A B : Matrix (Fin (s + 1)) (Fin (s + 1)) κ) (hA : ∀ i : Fin s, A i.castSucc (Fin.last s) = 0) :
    (A * B).submatrix Fin.castSucc Fin.castSucc = A.submatrix Fin.castSucc Fin.castSucc * B.submatrix Fin.castSucc Fin.castSucc := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  rw [Fin.sum_univ_castSucc, hA i, zero_mul, add_zero]
end Formalism.L2.Col
