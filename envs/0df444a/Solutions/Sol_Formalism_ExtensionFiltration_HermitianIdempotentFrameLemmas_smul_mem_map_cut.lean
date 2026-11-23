-- Prove2me | solution 1 for Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.smul_mem_map_cut
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:22:34.62139+00:00
-- url     : https://prove2.me/submissions/d0e78e84-69a9-4994-bdfa-180afd4b5329

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_MuMaxMinkowski
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_GoodBadCut

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
theorem _root_.solution (e : V →ₗ[K] V) (g : ℕ) (N : Submodule (𝓞 K) V) {y : V}
    (hy : y ∈ N ⊓ (LinearMap.ker e).restrictScalars (𝓞 K)) :
    (g : K) • y ∈ N.map (((g : K) • (LinearMap.id - e) : V →ₗ[K] V).restrictScalars (𝓞 K)) := by
  obtain ⟨hyN, hyk⟩ := hy
  refine ⟨y, hyN, ?_⟩
  have hy0 : e y = 0 := hyk
  show (g : K) • (y - e y) = (g : K) • y
  rw [hy0, sub_zero]
end Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas
