-- Prove2me | solution 1 for Formalism.F.mem_of_starProjection_mem_span_orthQuotient
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:43:46.675821+00:00
-- url     : https://prove2.me/submissions/40a6f40a-d0e0-4d75-93ee-3661b39dad93

import Definitions.Def_Formalism_LatticeSlopes_Statement
import Definitions.Def_Formalism_LatticeSlopes_CovolAntiSameRank
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolPos
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DegQuot
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_SaturationProperties
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_MuMaxAttained
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_FiniteSaturated
import Theorems.Thm_Formalism_F_sub_mem_of_starProjection_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.F
universe u
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
namespace Formalism.F
theorem _root_.solution {L M N₁ : Submodule ℤ E} (hM : IsSaturated L M) (h1 : N₁ ≤ M)
    {x : E} (hx : x ∈ L)
    (hπ : (span ℝ (N₁ : Set E))ᗮ.starProjection x ∈ span ℝ (quot M N₁ : Set E)) : x ∈ M := by
  unfold quot at hπ
  rw [Submodule.map_coe] at hπ
  have hfun : ⇑(LinearMap.restrictScalars ℤ
      (((span ℝ (N₁ : Set E))ᗮ.starProjection : E →L[ℝ] E) : E →ₗ[ℝ] E)) =
      ⇑(((span ℝ (N₁ : Set E))ᗮ.starProjection : E →L[ℝ] E) : E →ₗ[ℝ] E) := rfl
  rw [hfun, Submodule.span_image, Submodule.mem_map] at hπ
  obtain ⟨y, hy, hyx⟩ := hπ
  have hxy : x - y ∈ span ℝ (N₁ : Set E) := sub_mem_of_starProjection_eq _ hyx.symm
  have hle : span ℝ (N₁ : Set E) ≤ span ℝ (M : Set E) := span_mono h1
  refine hM.2 x hx ?_
  have := add_mem (hle hxy) hy
  rwa [sub_add_cancel] at this
end Formalism.F
