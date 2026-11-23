-- Prove2me | solution 1 for Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.map_cut_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:51:24.055922+00:00
-- url     : https://prove2.me/submissions/0c89df7f-fb98-4baa-a3d6-bd911d913907

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_MuMaxMinkowski
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_GoodBadCut
import Theorems.Thm_Formalism_ExtensionFiltration_HermitianIdempotentFrameLemmas_cut_mem

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
    (hint : ∀ x ∈ N, (g : K) • e x ∈ N) :
    N.map (((g : K) • (LinearMap.id - e) : V →ₗ[K] V).restrictScalars (𝓞 K)) ≤
      N ⊓ (LinearMap.ker e).restrictScalars (𝓞 K) := by
  rintro _ ⟨x, hx, rfl⟩
  exact cut_mem e g N hee hint hx
end Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas
