-- Prove2me | solution 1 for Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.ker_cut
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:35:03.751781+00:00
-- url     : https://prove2.me/submissions/71024307-e7fc-49f5-bb26-46514d68d45d

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_MuMaxMinkowski
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_GoodBadCut
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
theorem _root_.solution (e : V →ₗ[K] V) (g : ℕ) (hg : 1 ≤ g) (hee : e ∘ₗ e = e) :
    LinearMap.ker ((g : K) • (LinearMap.id - e)) = LinearMap.range e := by
  ext x
  have hg0 : (g : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  constructor
  · intro h
    have h' : (g : K) • (x - e x) = 0 := h
    have h'' : x - e x = 0 := (smul_eq_zero.mp h').resolve_left hg0
    exact ⟨x, (sub_eq_zero.mp h'').symm⟩
  · rintro ⟨y, rfl⟩
    show (g : K) • (e y - e (e y)) = 0
    rw [idem_apply e hee y, sub_self, smul_zero]
end Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas
