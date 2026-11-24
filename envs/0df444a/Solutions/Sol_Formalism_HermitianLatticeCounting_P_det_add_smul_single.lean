-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.det_add_smul_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:47:53.099939+00:00
-- url     : https://prove2.me/submissions/fe88ec52-22e1-49ce-8702-45aa91d4d369

import Definitions.Def_Formalism_FlagUnipotentLattices_DetIndexProductHyperbolicInequality
import Definitions.Def_Formalism_FlagUnipotentLattices_DetIndexProductPlacesInequalitySq
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_HyperbolicPlaceProducts_ArithmeticCountRevised
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LocalIntegralStructure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Formalism.HermitianLatticeCounting.LocalIntegralStructure nonZeroDivisors
set_option linter.all false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Matrix Polynomial
variable {R : Type} [CommRing R]
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n R) (i j : n) (c : R) :
    (M + c • Matrix.single i j (1 : R)).det = M.det + c * M.adjugate j i := by
  have hM : M + c • Matrix.single i j (1 : R) = M.updateRow i (M i + c • Pi.single j 1) := by
    ext a b
    by_cases ha : a = i
    · subst ha
      by_cases hb : b = j
      · subst hb
        simp
      · simp [Matrix.single_apply, Pi.single_apply, hb, Ne.symm hb]
    · simp [Matrix.single_apply, Matrix.updateRow_ne ha, ha, Ne.symm ha]
  rw [hM, Matrix.det_updateRow_add, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self,
    Matrix.adjugate_apply]
end Formalism.HermitianLatticeCounting.P
