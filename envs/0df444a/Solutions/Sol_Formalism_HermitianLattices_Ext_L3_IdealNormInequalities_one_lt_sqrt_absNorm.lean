-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.IdealNormInequalities.one_lt_sqrt_absNorm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:09.973703+00:00
-- url     : https://prove2.me/submissions/c25fa8bb-7691-4e9d-aa74-3010c1590a73

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFilterResCharLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_EulerFacMulConjInvSplit
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_IdealNormInequalities_one_lt_absNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K : Type} [Field K] [NumberField K] [StarRing K]
open Formalism.HermitianLattices.Ext.L3.IdealNormInequalities
namespace Formalism.HermitianLattices.Ext.L3.IdealNormInequalities
theorem _root_.solution {P : Ideal (𝓞 K)} (hP : P.IsMaximal) :
    (1 : ℝ) < Real.sqrt (Ideal.absNorm P : ℝ) := by
  rw [Real.lt_sqrt (by norm_num)]
  simpa using one_lt_absNorm hP
end Formalism.HermitianLattices.Ext.L3.IdealNormInequalities
