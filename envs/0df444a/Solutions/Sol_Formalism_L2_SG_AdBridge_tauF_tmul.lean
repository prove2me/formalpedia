-- Prove2me | solution 1 for Formalism.L2.SG.AdBridge.tauF_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:43:52.598548+00:00
-- url     : https://prove2.me/submissions/0bf9e0d3-c916-4fa7-aa72-493e8d3927d0

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_LevelIntersectParabolic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_AdBridge
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.AdBridge
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst uMat)
variable (I : AutInst)
namespace Formalism.L2.SG.AdBridge
theorem _root_.solution (a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) (x : I.E) :
    tauF I (a ⊗ₜ[I.F] x) = x ⊗ₜ[I.F] a.2 := by
  first
    | (simp [tauF, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA, Algebra.TensorProduct.tmul_mul_tmul]; done)
    | (show (1 : I.E) ⊗ₜ[I.F] a.2 * x ⊗ₜ[I.F] (1 : Formalism.MainNotions.S.Af I.F) = _
       rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one])
end Formalism.L2.SG.AdBridge
