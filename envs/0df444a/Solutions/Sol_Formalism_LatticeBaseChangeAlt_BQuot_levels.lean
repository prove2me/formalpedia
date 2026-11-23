-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.BQuot.levels
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:00.955873+00:00
-- url     : https://prove2.me/submissions/daa3fa88-eacf-448f-97a9-e286a6535713

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_ReductionQuotient
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxDet
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_MemSpanBasisFun
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_BQuot_ql_le_of_map
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_BQuot_ql_anti_right
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_BQuot_ql_le_of_le_sup
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_BQuot_ql_triangle

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeBaseChangeAlt
open Module
open Formalism.LatticeBaseChangeAlt.BQuot
variable {O V W : Type*} [CommRing O] [AddCommGroup V] [Module O V] [AddCommGroup W] [Module O W]
namespace Formalism.LatticeBaseChangeAlt.BQuot
theorem _root_.solution (N' M₁ N₁ Z Zm : Submodule O V) (AA AA' N₁' : Submodule O W) (ρ : ↥N' →ₗ[O] W)
    (hM : M₁ ≤ N') (hρ : ∀ x, ρ x ∈ AA')
    (hker : LinearMap.ker ρ = Zm.comap N'.subtype) (himg : (N₁.comap N'.subtype).map ρ = N₁') :
    ql M₁ (N₁ ⊔ Z) ≤ ql AA' AA + ql AA N₁' + ql Zm Z := by
  set Y : Submodule O V := (AA.comap ρ).map N'.subtype with hYdef
  set Y' : Submodule O V := (N₁'.comap ρ).map N'.subtype with hY'def
  have hYN : Y ≤ N' := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have s1 : ql M₁ Y ≤ ql AA' AA :=
    ql_le_of_map (ρ ∘ₗ Submodule.inclusion hM) (fun x => hρ _)
      (fun x hx => ⟨Submodule.inclusion hM x, hx, rfl⟩)
  have s2 : ql Y Y' ≤ ql AA N₁' := by
    refine ql_le_of_map (ρ ∘ₗ Submodule.inclusion hYN) (fun x => ?_)
      (fun x hx => ⟨Submodule.inclusion hYN x, hx, rfl⟩)
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.1 x.2
    have hxy : Submodule.inclusion hYN x = y := Subtype.ext hyx.symm
    rw [LinearMap.comp_apply, hxy]
    exact hy
  have s3 : ql Y' (N₁ ⊔ Z) ≤ ql Zm Z := by
    have hsub : Y' ≤ Zm ⊔ (N₁ ⊔ Z) := by
      rintro _ ⟨y, hy, rfl⟩
      have hy' : ρ y ∈ (N₁.comap N'.subtype).map ρ := by
        rw [himg]
        exact hy
      obtain ⟨z, hz, hzy⟩ := Submodule.mem_map.1 hy'
      have hk : y - z ∈ LinearMap.ker ρ := by
        rw [LinearMap.mem_ker, map_sub, hzy, sub_self]
      rw [hker] at hk
      have hsplit : N'.subtype y = ((y - z : ↥N') : V) + (z : V) := by
        simp
      rw [hsplit]
      exact Submodule.add_mem_sup hk (Submodule.mem_sup_left hz)
    exact (ql_le_of_le_sup hsub).trans (ql_anti_right le_sup_right)
  calc ql M₁ (N₁ ⊔ Z) ≤ ql M₁ Y + ql Y (N₁ ⊔ Z) := ql_triangle _ _ _
    _ ≤ ql M₁ Y + (ql Y Y' + ql Y' (N₁ ⊔ Z)) := by
      gcongr
      exact ql_triangle _ _ _
    _ ≤ ql AA' AA + (ql AA N₁' + ql Zm Z) := by gcongr
    _ = ql AA' AA + ql AA N₁' + ql Zm Z := by rw [add_assoc]
end Formalism.LatticeBaseChangeAlt.BQuot
