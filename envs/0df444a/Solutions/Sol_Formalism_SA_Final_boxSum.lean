-- Prove2me | solution 1 for Formalism.SA.Final.boxSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:32:20.561494+00:00
-- url     : https://prove2.me/submissions/becd78f4-9408-4cd3-b372-78cec40c950a

import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_PackingCountGeometricMean
import Definitions.Def_Formalism_LatticeRigidity_HeightMin
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_PowFinrankEqZeroOfTracePow
import Definitions.Def_Formalism_GelfandTransference_HadamardGelfand_Transference
import Mathlib
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_BlockEquationHolds
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_ChebyshevLeadingCoeffHolds
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_SqrtAbsNormLeProd
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_OneLeProdOfInt
import Definitions.Def_Formalism_LatticeRigidity_RecursionUnrestrictedFalse
import Theorems.Thm_Formalism_SA_P_smoothedSumBound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.SA Formalism.SA.Final
namespace Formalism.SA.Final
theorem _root_.solution : Formalism.SA.C.BoxSum := Formalism.SA.P.smoothedSumBound
end Formalism.SA.Final
