-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.cofactor_line_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:14:02.056816+00:00
-- url     : https://prove2.me/submissions/55f0115c-5fcc-49c4-94f6-3a9cd882f562

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_LatticeDeterminantIndexSq
import Definitions.Def_Formalism_FlagUnipotentLattices_SignaturePreservingEntryNorms
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegerGroupLocalParametrization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField nonZeroDivisors Finset
noncomputable section
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.LocalIntegralStructure Formalism.HermitianLatticeCounting.P.IntegralityLocalGlobal
set_option linter.all false
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : CofactorLine := by
  intro K _ r Z c hdet hc
  refine ⟨(∑ b, c b * Z b (Fin.last r)) * Z.det⁻¹, fun b => ?_⟩
  have hu : IsUnit Z.det := isUnit_iff_ne_zero.mpr hdet
  have h1 : Matrix.vecMul c Z = Pi.single (Fin.last r) (∑ b, c b * Z b (Fin.last r)) := by
    ext a
    by_cases ha : a = Fin.last r
    · subst ha; simp [Matrix.vecMul, dotProduct]
    · simp [Matrix.vecMul, dotProduct, ha, hc a ha]
  have h2 : c = Matrix.vecMul (Matrix.vecMul c Z) Z⁻¹ := by
    rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hu, Matrix.vecMul_one]
  calc c b = (Matrix.vecMul (Matrix.vecMul c Z) Z⁻¹) b := congrFun h2 b
    _ = _ := by
      rw [h1, Matrix.single_vecMul]
      simp [Matrix.inv_def, Ring.inverse_eq_inv']; ring
end Formalism.HermitianLatticeCounting.P
