-- Prove2me | solution 1 for Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.rk_map_cut
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:54:26.887082+00:00
-- url     : https://prove2.me/submissions/1d0319fb-4aa9-4754-975e-778869219a71

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_MuMaxMinkowski
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_GoodBadCut
import Theorems.Thm_Formalism_ExtensionFiltration_HermitianIdempotentFrameLemmas_map_cut_le
import Theorems.Thm_Formalism_ExtensionFiltration_HermitianIdempotentFrameLemmas_smul_mem_map_cut

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.ExtensionFiltration
open Formalism.HN
open Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
variable [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas
theorem _root_.solution (e : V →ₗ[K] V) (g : ℕ) (N : Submodule (𝓞 K) V) (hg : 1 ≤ g)
    (hee : e ∘ₗ e = e) (hint : ∀ x ∈ N, (g : K) • e x ∈ N) :
    rkK (N ⊓ (LinearMap.ker e).restrictScalars (𝓞 K)) =
      rkK (N.map (((g : K) • (LinearMap.id - e) : V →ₗ[K] V).restrictScalars (𝓞 K))) := by
  have hg0 : (g : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hspan : Submodule.span K ((N ⊓ (LinearMap.ker e).restrictScalars (𝓞 K) : Submodule (𝓞 K) V) : Set V) =
      Submodule.span K ((N.map (((g : K) • (LinearMap.id - e) : V →ₗ[K] V).restrictScalars (𝓞 K)) :
        Submodule (𝓞 K) V) : Set V) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro y hy
      have h1 := smul_mem_map_cut e g N hy
      have h2 : (g : K) • y ∈ Submodule.span K ((N.map (((g : K) • (LinearMap.id - e) : V →ₗ[K] V).restrictScalars (𝓞 K)) :
          Submodule (𝓞 K) V) : Set V) := Submodule.subset_span h1
      have h3 := Submodule.smul_mem _ ((g : K)⁻¹) h2
      rwa [smul_smul, inv_mul_cancel₀ hg0, one_smul] at h3
    · exact Submodule.span_mono (SetLike.coe_subset_coe.mpr (map_cut_le e g N hee hint))
  unfold rkK
  rw [hspan]
end Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas
