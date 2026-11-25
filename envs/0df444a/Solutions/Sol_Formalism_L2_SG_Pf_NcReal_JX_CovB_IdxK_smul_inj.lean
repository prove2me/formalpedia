-- Prove2me | solution 1 for Formalism.L2.SG.Pf.NcReal.JX.CovB.IdxK.smul_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:18:16.315743+00:00
-- url     : https://prove2.me/submissions/912c21ff-7207-4f64-8afe-b86c35b228f9

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_CovolIdxK

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open scoped nonZeroDivisors
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.NcReal Formalism.L2.SG.Pf.NcReal.JX Formalism.L2.SG.Pf.NcReal.JX.CovB Formalism.L2.SG.Pf.NcReal.JX.CovB.IdxK
variable {K : Type} [Field K] [NumberField K]
open scoped Pointwise
variable {M : Type} [AddCommGroup M] [Module (𝓞 K) M] [NoZeroSMulDivisors (𝓞 K) M]
namespace Formalism.L2.SG.Pf.NcReal.JX.CovB.IdxK
theorem _root_.solution (π : 𝓞 K) (hπ : π ≠ 0) : Function.Injective (DistribSMul.toAddMonoidHom M π) := by
  intro x y h
  exact smul_right_injective M hπ (by simpa using h)
end Formalism.L2.SG.Pf.NcReal.JX.CovB.IdxK
