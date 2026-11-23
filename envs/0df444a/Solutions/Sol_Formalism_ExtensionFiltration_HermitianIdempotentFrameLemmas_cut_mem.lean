-- Prove2me | solution 1 for Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.cut_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:43:45.952292+00:00
-- url     : https://prove2.me/submissions/dca23a74-e1b1-4698-80f8-696ab532552e

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_MuMaxMinkowski
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_GoodBadCut
import Theorems.Thm_Formalism_ExtensionFiltration_HermitianIdempotentFrameLemmas_natCast_smul_mem
import Theorems.Thm_Formalism_ExtensionFiltration_HermitianIdempotentFrameLemmas_idem_apply

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
theorem _root_.solution (e : V →ₗ[K] V) (g : ℕ) (N : Submodule (𝓞 K) V) (hee : e ∘ₗ e = e)
    (hint : ∀ x ∈ N, (g : K) • e x ∈ N) {x : V} (hx : x ∈ N) :
    (g : K) • (x - e x) ∈ N ⊓ (LinearMap.ker e).restrictScalars (𝓞 K) := by
  refine ⟨?_, ?_⟩
  · rw [smul_sub]
    exact N.sub_mem (natCast_smul_mem N g hx) (hint x hx)
  · show e ((g : K) • (x - e x)) = 0
    rw [map_smul, map_sub, idem_apply e hee x, sub_self, smul_zero]
end Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas
