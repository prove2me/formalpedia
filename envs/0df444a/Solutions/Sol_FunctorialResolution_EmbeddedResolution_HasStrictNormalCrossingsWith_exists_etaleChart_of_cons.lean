-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.HasStrictNormalCrossingsWith.exists_etaleChart_of_cons
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:23:31.566612+00:00
-- url     : https://prove2.me/submissions/df005d68-767c-4f77-8177-855a714aa791

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
namespace HasStrictNormalCrossingsWith
theorem _root_.solution {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {Z : X.IdealSheafData}
    {H : X.IdealSheafData} {E : List X.IdealSheafData}
    (h : HasStrictNormalCrossingsWith p Z (H :: E)) {x : X} (hx : x ∈ Z.support) :
    ∃ (U : X.Opens) (_ : x ∈ U) (m : ℕ) (c : EtaleChart p U m) (S : Finset (Fin m))
      (aH : Option (Fin m)) (a : ℕ → Option (Fin m)),
      restrictIdeal Z U = c.coordIdeal S ∧
      (aH = none → restrictIdeal H U = ⊤) ∧
      (∀ t : Fin m, aH = some t → restrictIdeal H U = c.coordIdeal {t}) ∧
      (∀ i, ∀ h : i < E.length, a i = none → restrictIdeal (E[i]'h) U = ⊤) ∧
      (∀ i, ∀ h : i < E.length, ∀ t : Fin m, a i = some t →
        restrictIdeal (E[i]'h) U = c.coordIdeal {t}) ∧
      (∀ i < E.length, ∀ t : Fin m, a i = some t → aH ≠ some t) ∧
      (∀ i < E.length, ∀ j < E.length, ∀ t : Fin m, a i = some t → a j = some t → i = j) := by
  obtain ⟨U, hU, m, c, a, S, h1, h2, h3, h4⟩ := h x hx
  have hzero : 0 < (H :: E).length := by simp
  refine ⟨U, hU, m, c, S, a 0, fun i => a (i + 1), h4, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h0
    have hres := h2 0 hzero h0
    simpa using hres
  · intro t ht
    have hres := h3 0 hzero t ht
    simpa using hres
  · intro i hi hni
    have hi' : i + 1 < (H :: E).length := by
      simp only [List.length_cons]; omega
    have hres := h2 (i + 1) hi' hni
    simpa using hres
  · intro i hi t ht
    have hi' : i + 1 < (H :: E).length := by
      simp only [List.length_cons]; omega
    have hres := h3 (i + 1) hi' t ht
    simpa using hres
  · intro i hi t ht hc
    have hi' : i + 1 < (H :: E).length := by
      simp only [List.length_cons]; omega
    have := h1 (i + 1) hi' 0 hzero t ht hc
    omega
  · intro i hi j hj t hti htj
    have hi' : i + 1 < (H :: E).length := by
      simp only [List.length_cons]; omega
    have hj' : j + 1 < (H :: E).length := by
      simp only [List.length_cons]; omega
    have := h1 (i + 1) hi' (j + 1) hj' t hti htj
    omega
end HasStrictNormalCrossingsWith
end FunctorialResolution.EmbeddedResolution
