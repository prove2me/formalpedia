-- Prove2me | solution 1 for Formalism.L2.SG.Pf.G3.sd_basis_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:46:08.089312+00:00
-- url     : https://prove2.me/submissions/36577ae3-ab06-46b9-9b74-531e0ac855b7

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_MemSpanSSelf
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_SdBasisBot
import Theorems.Thm_Formalism_L2_SG_Pf_G3_spanS_empty


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
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}
namespace Formalism.L2.SG.Pf.G3
theorem _root_.solution {W : Submodule K V} {M : AddSubgroup V} (hM : IsSD S h W M) (hW : W = ⊥) :
    ∃ (k : ℕ) (f : Fin k → V), (∀ i j, i ≠ j → h (f i) (f j) = 0) ∧
      (∀ i, IsUnitIn S (h (f i) (f i))) ∧ (∀ v, v ∈ spanS S f ↔ v ∈ M) ∧
      Submodule.span K (Set.range f) = W := by
  refine ⟨0, Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun v => ?_, ?_⟩
  · rw [spanS_empty]
    constructor
    · rintro rfl
      exact M.zero_mem
    · intro hv
      have := hM.le v hv
      rwa [hW, Submodule.mem_bot] at this
  · rw [hW, Set.range_eq_empty, Submodule.span_empty]
end Formalism.L2.SG.Pf.G3
