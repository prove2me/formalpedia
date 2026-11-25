-- Prove2me | solution 1 for Formalism.L2.SG.Pf.NcReal.JX.CovB.IdxK.smul_toAddSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:17:22.864801+00:00
-- url     : https://prove2.me/submissions/17be0c20-965b-47cd-8772-2f8a32c4f16d

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
theorem _root_.solution (π : 𝓞 K) (N : Submodule (𝓞 K) M) :
    (Ideal.span {π} • N).toAddSubgroup = N.toAddSubgroup.map (DistribSMul.toAddMonoidHom M π) := by
  ext x
  rw [Submodule.mem_toAddSubgroup, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists, AddSubgroup.mem_map]
  first
  | simp
  | exact Iff.rfl
end Formalism.L2.SG.Pf.NcReal.JX.CovB.IdxK
