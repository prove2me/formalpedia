-- Prove2me | solution 1 for CharPSComp.eq_10
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T16:19:18.969411+00:00
-- url     : https://prove2.me/submissions/24bd94b8-bf3e-47ee-95e5-cf61e12dcf47

import Mathlib
import Definitions.Def_CharPSComp_schonhageSum

namespace Aux_CharPSComp_eq10
open MvPolynomial CharPSComp

lemma aux_V (q : ℕ) (i : Fin q) : ∑ j : Fin q, Vhat q i j = 0 := by
  rcases q with _ | n
  · exact i.elim0
  rw [Fin.sum_univ_castSucc]
  by_cases hi : i.val < n
  · simp [Vhat, hi]
  · simp [Vhat, hi]

lemma aux_U (q : ℕ) (j : Fin q) : ∑ i : Fin q, Uhat q i j = 0 := by
  rcases q with _ | n
  · exact j.elim0
  rw [Fin.sum_univ_castSucc]
  by_cases hj : j.val < n
  · simp [Uhat, hj]
  · simp [Uhat, hj]

lemma aux_UV (q : ℕ) : ∑ i : Fin q, ∑ j : Fin q, Uhat q i j * Vhat q i j
    = ∑ i : Fin (q - 1), ∑ j : Fin (q - 1), X (SVar.u i j) * X (SVar.v i j) := by
  rcases q with _ | n
  · simp
  simp [Fin.sum_univ_castSucc, Uhat, Vhat]

end Aux_CharPSComp_eq10

open CharPSComp MvPolynomial Aux_CharPSComp_eq10 in
theorem solution (q : ℕ) : schonhageSum q = schonhageG q + schonhageGerr q := by
  have key : ∑ i : Fin q, ∑ j : Fin q, (X (SVar.x i) + Uhat q i j) * (X (SVar.y j) + Vhat q i j)
      = (∑ i : Fin q, X (SVar.x i)) * (∑ j : Fin q, X (SVar.y j))
        + ∑ i : Fin (q - 1), ∑ j : Fin (q - 1), X (SVar.u i j) * X (SVar.v i j) := by
    have e : ∀ i j, (X (SVar.x i) + Uhat q i j) * (X (SVar.y j) + Vhat q i j)
        = X (SVar.x i) * X (SVar.y j) + X (SVar.x i) * Vhat q i j
          + X (SVar.y j) * Uhat q i j + Uhat q i j * Vhat q i j := by
      intro i j; ring
    simp only [e, Finset.sum_add_distrib]
    rw [aux_UV]
    have h1 : ∑ i : Fin q, ∑ j : Fin q, X (SVar.x i) * Vhat q i j = 0 := by
      simp only [← Finset.mul_sum, aux_V, mul_zero, Finset.sum_const_zero]
    have h2 : ∑ i : Fin q, ∑ j : Fin q, X (SVar.y j) * Uhat q i j = 0 := by
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum, aux_U, mul_zero, Finset.sum_const_zero]
    rw [h1, h2, Finset.sum_mul_sum]
    ring
  unfold schonhageSum schonhageG schonhageGerr
  have e2 : ∀ i j, (X (SVar.x i) + Uhat q i j) * (X (SVar.y j) + Vhat q i j)
      * (X (SVar.z i j) + X SVar.z0)
      = X (SVar.x i) * X (SVar.y j) * X (SVar.z i j)
        + (X (SVar.x i) * Vhat q i j + Uhat q i j * X (SVar.y j) + Uhat q i j * Vhat q i j)
          * X (SVar.z i j)
        + (X (SVar.x i) + Uhat q i j) * (X (SVar.y j) + Vhat q i j) * X SVar.z0 := by
    intro i j; ring
  simp only [e2, Finset.sum_add_distrib, ← Finset.sum_mul]
  rw [key]
  ring
