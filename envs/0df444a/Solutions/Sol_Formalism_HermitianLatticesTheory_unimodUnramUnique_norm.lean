-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.unimodUnramUnique_norm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:09.121871+00:00
-- url     : https://prove2.me/submissions/eb9d2652-1767-496b-bf6e-8bda3fbd417e

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementJac
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique
import Theorems.Thm_Formalism_HermitianLatticesTheory_unimodUnramUnique_quad

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
open Polynomial IsLocalRing Matrix
variable {R : Type} [CommRing R] [StarRing R] {R₀ : Subring R}
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution [HenselianLocalRing R₀] [Finite (ResidueField R₀)]
    (hR₀ : ∀ x, x ∈ R₀ ↔ star x = x) {θ : R} (hθ : IsUnit (θ - star θ)) {d : R}
    (hd : star d = d) (hdu : IsUnit d) : ∃ w : R, star w * w = d := by
  have hT : star (θ + star θ) = θ + star θ := unimodUnramUnique_trFix θ
  have hN : star (star θ * θ) = star θ * θ := by rw [star_mul, star_star]
  have hD : star ((θ - star θ) ^ 2) = (θ - star θ) ^ 2 := by
    rw [star_pow, star_sub, star_star]; ring
  set T : R₀ := ⟨θ + star θ, (hR₀ _).2 hT⟩ with hTdef
  set N : R₀ := ⟨star θ * θ, (hR₀ _).2 hN⟩ with hNdef
  set d₀ : R₀ := ⟨d, (hR₀ _).2 hd⟩ with hd₀def
  have hDu : IsUnit (T ^ 2 - 4 * N) := by
    have := unimodUnramUnique_fixUnit hR₀ hD (hθ.pow 2)
    convert this using 1
    apply Subtype.ext
    simp only [hTdef, hNdef]
    push_cast
    rw [show ((4 : R₀) : R) = 4 from map_ofNat R₀.subtype 4]
    ring
  obtain ⟨s, t, hst⟩ :=
    unimodUnramUnique_quad T N d₀ hDu (unimodUnramUnique_fixUnit hR₀ hd hdu)
  refine ⟨(s : R) + (t : R) * θ, ?_⟩
  have hs : star (s : R) = s := (hR₀ _).1 s.2
  have ht : star (t : R) = t := (hR₀ _).1 t.2
  have := congrArg Subtype.val hst
  simp only [hTdef, hNdef, hd₀def] at this
  push_cast at this
  rw [star_add, star_mul, hs, ht]
  linear_combination this
end Formalism.HermitianLatticesTheory
