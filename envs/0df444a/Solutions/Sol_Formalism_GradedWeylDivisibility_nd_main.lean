-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.nd_main
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:05:18.980037+00:00
-- url     : https://prove2.me/submissions/79fbb643-bdd1-4030-b87c-bcde6b7b6300

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LNondomLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylNonDom
import Theorems.Thm_Formalism_GradedWeylDivisibility_ndE_eq_zero
import Theorems.Thm_Formalism_GradedWeylDivisibility_nd_iter_Eul_l
import Theorems.Thm_Formalism_GradedWeylDivisibility_nd_iter_E
import Theorems.Thm_Formalism_GradedWeylDivisibility_ndEul_homog
import Theorems.Thm_Formalism_GradedWeylDivisibility_ndEul_neg_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
variable {R : Type*} [CommRing R] {r n : ℕ}
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution [IsDomain R] [CharZero R] (ν : Fin n → ℕ) {l j : Fin n} (hlj : l < j)
    (hν : ν l < ν j) (f : MvPolynomial (Fin r × Fin n) R)
    (hhom : IsWeightedHomogeneous (colW r n) f ν) (hinv : colAddGen R l j f = rename some f) :
    f = 0 := by
  have hne : l ≠ j := ne_of_lt hlj
  have hl := ndEul_homog (R := R) hhom l
  have hj := ndEul_homog (R := R) hhom j
  have hE := ndE_eq_zero hinv
  set G : ℕ → MvPolynomial (Fin r × Fin n) R := fun k => (ndF R r n l j)^[k] f with hG

  have hN : G (ν l + 1) = 0 := by
    apply ndEul_neg_eq_zero l
    rw [hG]; dsimp only
    rw [nd_iter_Eul_l hne hl, Nat.cast_succ, show (ν l : R) - ((ν l : R) + 1) = -1 by ring,
      neg_one_smul]

  have hstep : ∀ k, G (k + 1) = 0 → G k = 0 := by
    intro k hk
    have h1 := nd_iter_E hne hl hj hE k
    rw [show (ndF R r n l j)^[k + 1] f = G (k + 1) from rfl, hk, map_zero] at h1
    have hc : (((k : R) + 1) * ((ν l : R) - (ν j : R) - k)) ≠ 0 := by
      refine mul_ne_zero (Nat.cast_add_one_ne_zero k) ?_
      have : (ν l : R) - (ν j : R) - k = (((ν l : ℤ) - ν j - k : ℤ) : R) := by push_cast; ring
      rw [this, Int.cast_ne_zero]
      omega
    exact (smul_eq_zero.1 h1.symm).resolve_left hc
  have hdown : ∀ d k, G (k + d) = 0 → G k = 0 := by
    intro d
    induction d with
    | zero => intro k hk; simpa using hk
    | succ d ih =>
      intro k hk
      exact hstep k (ih (k + 1) (by rw [show k + 1 + d = k + (d + 1) by omega]; exact hk))
  have := hdown (ν l + 1) 0 (by simpa using hN)
  simpa [hG] using this
end Formalism.GradedWeylDivisibility
