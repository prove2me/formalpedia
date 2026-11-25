-- Prove2me | solution 1 for Formalism.L2.SG.Pf.G7.locF_le_of_zsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:38:58.222592+00:00
-- url     : https://prove2.me/submissions/330e954c-23ea-4226-95f5-b2dce633034a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_GlueExistsOfOf
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_TraceReal
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_GlueExistsOfLocal
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_mem_locF_iff


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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.G7
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt
variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.L2.SG.Pf.G7
theorem _root_.solution {A B : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) (n : ℤ)
    (hn : (n : 𝓞 F) ∉ 𝔭) (hAB : ∀ x ∈ A, n • x ∈ B) : locF 𝔭 A ≤ locF 𝔭 B := by
  intro x hx
  obtain ⟨t, ht, htx⟩ := (LocF.mem_locF_iff hp A x).1 hx
  refine (LocF.mem_locF_iff hp B x).2 ⟨(n : 𝓞 F) * t, fun hm => (hp.mem_or_mem hm).elim hn ht, ?_⟩
  rw [map_mul, map_intCast, mul_smul, Int.cast_smul_eq_zsmul]
  exact hAB _ htx
end Formalism.L2.SG.Pf.G7
