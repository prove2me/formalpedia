-- Prove2me | solution 1 for Formalism.LatticeIndexTer.goodIndex_of_latFinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:52:46.205186+00:00
-- url     : https://prove2.me/submissions/9afaed6d-b533-4184-b6eb-ec0bec6a52e4

import Definitions.Def_Formalism_LogFactorialIndices_StatementIdx
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ChainLength
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsPowSmulMem
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SubspaceLatticeIndex
import Theorems.Thm_Formalism_LatticeIndexTer_subgroupData_length_le_of_le
import Theorems.Thm_Formalism_LatticeIndexTer_subgroupData_length_le_of_ge
import Theorems.Thm_Formalism_LatticeIndexTer_subgroupData_qlen_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Pointwise
noncomputable section
open Formalism Formalism.LatticeIndexTer
open Formalism.LatticeIndexTer.subgroupData
namespace Formalism.LatticeIndexTer
theorem _root_.solution (h1 : LatFinite) : GoodIndex := by
  intro O K X _ _ _ _ _ _ _ _ _ _ _ e he A Θ hA hΘ hΘA V₀
  have hfin : qlen O X A Θ ≠ ⊤ := h1 O K X A Θ hA hΘ
  have hQ'P : Θ ⊓ V₀ ≤ A ⊓ V₀ := inf_le_inf_right _ hΘA
  have hPQ' : qlen O X (A ⊓ V₀) (Θ ⊓ V₀) ≤ qlen O X A Θ :=
    length_le_of_le inf_le_left inf_le_left (fun x hx =>
      Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp hx).2,
        (Submodule.mem_inf.mp (Submodule.mem_inf.mp hx).1).2⟩)
  have hfin' : qlen O X (A ⊓ V₀) (Θ ⊓ V₀) ≠ ⊤ := ne_top_of_le_ne_top hfin hPQ'
  have hidx1 : idx O X A Θ = ((qlen O X A Θ).toNat : ℤ) := by
    simp [idx, qlen_eq_zero hΘA]
  have hidx2 : idx O X (A ⊓ V₀) (Θ ⊓ V₀) = ((qlen O X (A ⊓ V₀) (Θ ⊓ V₀)).toNat : ℤ) := by
    simp [idx, qlen_eq_zero hQ'P]
  refine ⟨?_, ?_⟩
  · rw [hidx1, hidx2]
    exact_mod_cast ENat.toNat_le_toNat hPQ' hfin
  · rw [hidx2]
    have hQ'Q : Θ ⊓ V₀ ≤ Θ.map (e.restrictScalars O) := by
      intro x hx
      have hxΘ : x ∈ Θ := (Submodule.mem_inf.mp hx).1
      have hxV : x ∈ LinearMap.range e := (Submodule.mem_inf.mp hx).2
      obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hxV
      refine Submodule.mem_map.mpr ⟨e y, hxΘ, ?_⟩
      have := LinearMap.congr_fun he y
      simpa using this
    have hle : qlen O X (A ⊓ V₀) (Θ.map (e.restrictScalars O)) ≤ qlen O X (A ⊓ V₀) (Θ ⊓ V₀) :=
      length_le_of_ge hQ'Q
    have := ENat.toNat_le_toNat hle hfin'
    unfold idx
    omega
end Formalism.LatticeIndexTer
