-- Prove2me | solution 1 for Formalism.L2.SG.Pf.G3.mem_span_iff_spanS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:34:43.472609+00:00
-- url     : https://prove2.me/submissions/517748f9-392e-4951-ab8a-c683e0c632a2

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_SplitAtOf
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_MemSpanIffSpanS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.G3
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}
namespace Formalism.L2.SG.Pf.G3
theorem _root_.solution {ι : Type} [Fintype ι] (b : ι → V) (v : V) :
    v ∈ Submodule.span K (Set.range b) ↔ v ∈ spanS (⊤ : Subring K) b := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩
    exact Exists.intro c ⟨fun _ => Subring.mem_top _, rfl⟩
  · rintro ⟨c, _, rfl⟩
    exact ⟨c, rfl⟩
end Formalism.L2.SG.Pf.G3
