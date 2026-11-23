-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.repr_aniso
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:32:23.446997+00:00
-- url     : https://prove2.me/submissions/8f1839f7-696a-49bd-85a6-20a9513ad13a

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_GoodMap_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ}
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution [FiniteDimensional K V] (H : HermSpace K V) (W : Submodule K V)
    (hW : ∀ w ∈ W, H.B w w = 0 → w = 0) (l : V →ₗ[K] K) : ∃ v ∈ W, ∀ w ∈ W, H.B w v = l w := by
  let b := Module.finBasis K W
  let Ψ : W →ₗ[K] (Fin (Module.finrank K W) → K) := LinearMap.pi fun i => (H.B.flip (b i : V)).comp W.subtype
  have hΨ : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    have hb : ∀ i, H.B (w : V) (b i : V) = 0 := fun i => by simpa [Ψ] using congrFun hw i
    have h0 : (H.B (w : V)).comp W.subtype = 0 := b.ext fun i => by
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.zero_apply]
      exact hb i
    have h5 := LinearMap.congr_fun h0 w
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.zero_apply] at h5
    exact Subtype.ext (hW w w.2 h5)
  have hsurj : Function.Surjective Ψ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).1 hΨ
  obtain ⟨w, hw⟩ := hsurj (fun i => star (l (b i : V)))
  have key : ∀ i, H.B (b i : V) (w : V) = l (b i : V) := by
    intro i
    have h1 := congrFun hw i
    simp only [Ψ, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.flip_apply] at h1
    rw [← H.herm, h1, star_star]
  refine ⟨w, w.2, fun u hu => ?_⟩
  have h2 : (H.B.flip (w : V)).comp W.subtype = l.comp W.subtype := b.ext fun i => by
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.flip_apply]
    exact key i
  have h3 := LinearMap.congr_fun h2 ⟨u, hu⟩
  simpa using h3
end Formalism.HermitianLatticeCounting.P
