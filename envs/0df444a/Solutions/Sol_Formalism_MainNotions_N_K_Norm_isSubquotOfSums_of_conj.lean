-- Prove2me | solution 1 for Formalism.MainNotions.N.K.Norm.isSubquotOfSums_of_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:33:02.048326+00:00
-- url     : https://prove2.me/submissions/3d0bb2c4-bdf1-4fa7-a098-65ad40e30d80

import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_QuotientHomNonvanishingBound
import Definitions.Def_Formalism_AdmissibleDesigns_InvariantsEqBotIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Formalism.WeaklyAdmissibleFiltrations TensorProduct
open Formalism Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K Formalism.MainNotions.N.K.Norm
variable {G : Type} [Group G] {LL : Type} [Field LL] {V : Type} [AddCommGroup V] [Module LL V]
  (ρ : Representation LL G V) {ι : Type} {k : ℕ}
namespace Formalism.MainNotions.N.K.Norm
theorem _root_.solution (Ms Ms' : ι → G → Matrix (Fin k) (Fin k) LL) (hc : ∀ x, IsConjM (Ms x) (Ms' x))
    (h : IsSubquotOfSums ρ Ms') : IsSubquotOfSums ρ Ms := by
  choose P Q h1 h2 h3 using fun x => (hc x).symm
  obtain ⟨m, xs, U, q, hU, hq, hqg⟩ := h
  let Φ : (Fin m → Fin k → LL) →ₗ[LL] (Fin m → Fin k → LL) :=
    LinearMap.pi fun a => Matrix.toLin' (P (xs a)) ∘ₗ LinearMap.proj a
  let Ψ : (Fin m → Fin k → LL) →ₗ[LL] (Fin m → Fin k → LL) :=
    LinearMap.pi fun a => Matrix.toLin' (Q (xs a)) ∘ₗ LinearMap.proj a
  have hΦ : ∀ u a, Φ u a = (P (xs a)).mulVec (u a) := fun _ _ => rfl
  have hΨ : ∀ u a, Ψ u a = (Q (xs a)).mulVec (u a) := fun _ _ => rfl
  have hΨΦ : ∀ u, Ψ (Φ u) = u := by
    intro u
    funext a
    rw [hΨ, hΦ, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
  have hcomm : ∀ g u, (fun a => (Ms (xs a) g).mulVec (Φ u a)) = Φ (fun a => (Ms' (xs a) g).mulVec (u a)) := by
    intro g u
    funext a
    rw [hΦ, hΦ, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h3]
  refine ⟨m, xs, U.map Φ, q ∘ₗ Ψ, ?_, ?_, ?_⟩
  · rintro g _ ⟨u, hu, rfl⟩
    exact ⟨_, hU g u hu, (hcomm g u).symm⟩
  · intro v
    obtain ⟨u, hu, rfl⟩ := hq v
    exact ⟨Φ u, ⟨u, hu, rfl⟩, by rw [LinearMap.comp_apply, hΨΦ]⟩
  · rintro g _ ⟨u, hu, rfl⟩
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hcomm, hΨΦ, hΨΦ]
    exact hqg g u hu
end Formalism.MainNotions.N.K.Norm
