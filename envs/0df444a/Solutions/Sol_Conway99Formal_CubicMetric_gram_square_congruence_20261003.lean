-- Prove2me | solution 1 for Conway99Formal.CubicMetric.gram_square_congruence_20261003
-- status  : ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-04T03:22:04.470981+00:00
-- url     : https://prove2.me/submissions/b1cad746-fc06-4824-8354-4fc2f1f94a75

import Mathlib
set_option autoImplicit false

namespace Conway99Formal.CubicMetric

private theorem symmetric_sum_dvd_four {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ι → ℤ)
    (hsym : ∀ i j, f i j = f j i)
    (hdiag : ∀ i, 4 ∣ f i i)
    (hoff : ∀ i j, i ≠ j → 2 ∣ f i j) :
    4 ∣ ∑ i ∈ s, ∑ j ∈ s, f i j := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hcross : 2 ∣ ∑ j ∈ s, f i j := by
        apply Finset.dvd_sum
        intro j hj
        apply hoff i j
        intro hij
        exact hi (hij.symm ▸ hj)
      have hswap : (∑ j ∈ s, f j i) = ∑ j ∈ s, f i j := by
        apply Finset.sum_congr rfl
        intro j _
        exact hsym j i
      simp only [Finset.sum_insert hi, Finset.sum_add_distrib]
      rw [hswap]
      obtain ⟨d, hd⟩ := hdiag i
      obtain ⟨c, hc⟩ := hcross
      obtain ⟨q, hq⟩ := ih
      refine ⟨d + c + q, ?_⟩
      rw [hd, hc, hq]
      ring

private theorem even_square_sub_self (g : ℤ) : 2 ∣ g ^ 2 - g := by
  simpa [pow_two, mul_sub] using (Int.even_mul_pred_self g).two_dvd

theorem gram_square_congruence_proof {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (G : ι → ι → ℤ) (a : ι → ℤ)
    (hsym : ∀ i j, G i j = G j i)
    (hdiag : ∀ i, G i i = 4) :
    4 ∣ ∑ i ∈ s, ∑ j ∈ s,
      a i * ((G i j) ^ 2 - G i j) * a j := by
  apply symmetric_sum_dvd_four s
    (fun i j => a i * ((G i j) ^ 2 - G i j) * a j)
  · intro i j
    rw [hsym i j]
    ring
  · intro i
    refine ⟨3 * a i ^ 2, ?_⟩
    rw [hdiag i]
    ring
  · intro i j _
    obtain ⟨k, hk⟩ := even_square_sub_self (G i j)
    refine ⟨a i * k * a j, ?_⟩
    rw [hk]
    ring

end Conway99Formal.CubicMetric

theorem solution {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (G : ι → ι → ℤ) (a : ι → ℤ)
    (hsym : ∀ i j, G i j = G j i)
    (hdiag : ∀ i, G i i = 4) :
    4 ∣ ∑ i ∈ s, ∑ j ∈ s, a i * ((G i j) ^ 2 - G i j) * a j := by
  exact Conway99Formal.CubicMetric.gram_square_congruence_proof s G a hsym hdiag

#print axioms Conway99Formal.CubicMetric.gram_square_congruence_proof
#print axioms solution
