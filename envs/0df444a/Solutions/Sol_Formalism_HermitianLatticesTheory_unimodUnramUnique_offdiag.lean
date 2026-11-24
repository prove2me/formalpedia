-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.unimodUnramUnique_offdiag
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:21.980245+00:00
-- url     : https://prove2.me/submissions/2bfbb7ba-78e2-44f4-99ae-6bd21e6819cf

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementJac
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique
import Theorems.Thm_Formalism_HermitianLatticesTheory_unimodUnramUnique_mem_J
import Theorems.Thm_Formalism_HermitianLatticesTheory_unimodUnramUnique_hermFix

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
theorem _root_.solution [IsLocalRing R₀] (hR₀ : ∀ x, x ∈ R₀ ↔ star x = x)
    {θ : R} (hθ : IsUnit (θ - star θ)) {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : Matrix ι ι R) (hA : Aᴴ = A) (hdet : IsUnit A.det) (hdiag : ∀ i, ¬ IsUnit (A i i)) :
    ∃ i j c, i ≠ j ∧ IsUnit (c * A i j + star (c * A i j)) := by
  by_contra hcon
  push Not at hcon
  have hmem : ∀ i j, A i j ∈ unimodUnramUnique_J hR₀ := by
    intro i j
    rw [unimodUnramUnique_mem_J]
    intro c
    by_cases hij : i = j
    · subst hij
      have hfix := unimodUnramUnique_hermFix A hA i i
      have e : c * A i i + star (c * A i i) = (c + star c) * A i i := by
        rw [star_mul, hfix]; ring
      rw [e]; exact fun h => hdiag i (isUnit_of_mul_isUnit_right h)
    · exact hcon i j c hij
  have hdetJ : A.det ∈ unimodUnramUnique_J hR₀ := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, RingHom.map_det]
    have : (Ideal.Quotient.mk (unimodUnramUnique_J hR₀)).mapMatrix A = 0 := by
      ext i j
      simpa [Ideal.Quotient.eq_zero_iff_mem] using hmem i j
    rw [this, det_zero]
  have htop := Ideal.eq_top_of_isUnit_mem _ hdetJ hdet
  have h1 : (1 : R) ∈ unimodUnramUnique_J hR₀ := htop ▸ Submodule.mem_top
  rw [unimodUnramUnique_mem_J] at h1
  obtain ⟨v, hv⟩ := hθ.exists_right_inv
  apply h1 (θ * v)
  have h2 : star v * (θ - star θ) = -1 := by
    have := congrArg star hv
    rw [star_mul, star_sub, star_star, star_one] at this
    linear_combination -this
  have hsv : star v = -v := by
    calc star v = star v * ((θ - star θ) * v) := by rw [hv, mul_one]
      _ = (star v * (θ - star θ)) * v := by ring
      _ = -v := by rw [h2]; ring
  have : θ * v * 1 + star (θ * v * 1) = 1 := by
    rw [mul_one, star_mul, hsv]; linear_combination hv
  rw [this]; exact isUnit_one
end Formalism.HermitianLatticesTheory
