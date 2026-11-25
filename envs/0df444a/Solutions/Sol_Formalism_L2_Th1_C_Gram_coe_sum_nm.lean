-- Prove2me | solution 1 for Formalism.L2.Th1.C.Gram.coe_sum_nm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:52:40.877166+00:00
-- url     : https://prove2.me/submissions/5a437afd-0307-4c7a-bfb9-78061c1ce7ff

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_GramFormula
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_UnitaryInverseIdentity
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SquareEqDiagOfQuadraticEven
import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_CharacterExistsAllEmbeddings
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_TraceDiagonalBis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open Formalism.L2.Th1.C.Gram
open Pts Calc Formalism.HermitianLattices.IntegralLatticeDensity
namespace Formalism.L2.Th1.C.Gram
theorem _root_.solution {O : Type} [CommRing O] [StarRing O] {n : Type} [Fintype n] (a : n → O) :
    ((∑ i, nm (a i) : saRing O) : O) = ∑ i, star (a i) * a i := by
  rw [AddSubmonoidClass.coe_finsetSum]
  rfl
end Formalism.L2.Th1.C.Gram
