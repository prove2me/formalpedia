-- Prove2me | solution 1 for Formalism.L2.SG.Pf.Lem3Mass.coe_algebraMap_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:42:02.483536+00:00
-- url     : https://prove2.me/submissions/0924b959-6513-41d8-ad98-583af692a043

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_IsUnitDetOfIsometry
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExistsSubDivMemSP
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExistsDenOfLeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Lem3Mass
open scoped TensorProduct Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.UnitaryGroupLocal
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Topology Filter
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (v : HeightOneSpectrum (𝓞 F))
variable (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) (hfix : ∀ y : E, σ y = y → y ∈ (algebraMap F E).range)
namespace Formalism.L2.SG.Pf.Lem3Mass
theorem _root_.solution (t : 𝓞 F) :
    algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) t) = algebraMap F E (t : F) := by
  rw [← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E, IsScalarTower.algebraMap_apply (𝓞 F) F E]
end Formalism.L2.SG.Pf.Lem3Mass
