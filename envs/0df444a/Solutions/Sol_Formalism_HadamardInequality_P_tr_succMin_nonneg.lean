-- Prove2me | solution 1 for Formalism.HadamardInequality.P.tr_succMin_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:17:29.295134+00:00
-- url     : https://prove2.me/submissions/c4c4a70a-c845-4c55-9e1c-ad947eb405c8

import Definitions.Def_Formalism_GelfandTransference_EnergyIdentity
import Definitions.Def_Formalism_NormUnitaryBounds_NormUnitary
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_ShortIndependentVectorsOfDualMinimum
import Definitions.Def_Formalism_LatticeTheta_ThetaShiftInversion
import Definitions.Def_Formalism_GelfandTransference_HadamardGelfand_Transference

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HadamardInequality Formalism.HadamardInequality.P
namespace Formalism.HadamardInequality.P
theorem _root_.solution {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L : Submodule ℤ E) (i : ℕ) : 0 ≤ Formalism.HadamardInequality.succMin L i :=
  Real.sInf_nonneg fun _ hx => hx.1
end Formalism.HadamardInequality.P
