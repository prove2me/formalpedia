-- Prove2me | solution 1 for FracRiccati.Radius.prop_B_1_a
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T04:02:44.552353+00:00
-- url     : https://prove2.me/submissions/f90a3131-53d4-46e7-9816-cb132d3ebbf5

import Mathlib
import Definitions.Def_FracRiccati_Radius_Coeff

namespace Aux_FRR_B1a

lemma odd_sum (c : ℕ → ℂ) (n : ℕ) (hn : n % 2 = 1)
    (hev : ∀ k, 1 ≤ k → 2 * k ≤ n → c (2 * k) = 0) :
    ∑ ℓ ∈ Finset.Ico 1 n, c ℓ * c (n - ℓ) = 0 := by
  apply Finset.sum_eq_zero
  intro ℓ hℓ
  rw [Finset.mem_Ico] at hℓ
  rcases Nat.even_or_odd ℓ with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [show ℓ = 2 * m by omega, hev m (by omega) (by omega), zero_mul]
  · obtain ⟨m', hm'⟩ : ∃ m', n - ℓ = 2 * m' := ⟨(n - ℓ) / 2, by omega⟩
    rw [hm', hev m' (by omega) (by omega), mul_zero]

end Aux_FRR_B1a

open FracRiccati.Radius Aux_FRR_B1a in
theorem solution (α : ℝ) (hα0 : 0 < α) (lam nu : ℂ) (hlam : lam ≠ 0) (hnu : nu ≠ 0) :
    (∀ k : ℕ, 1 ≤ k → coeff α lam 0 nu (2 * k) = 0) ∧
    (∀ k : ℕ, 1 ≤ k →
      ∑ ℓ ∈ Finset.Ico 1 (2 * k - 1), coeff α lam 0 nu ℓ * coeff α lam 0 nu (2 * k - 1 - ℓ) = 0) ∧
    coeff α lam 0 nu (2 * 1 - 1) = nu / (Real.Gamma (α + 1) : ℂ) ∧
    (∀ k : ℕ, 1 ≤ k →
      coeff α lam 0 nu (2 * (k + 1) - 1) =
        lam * ((Real.Gamma (2 * α * k + 1) / Real.Gamma ((2 * k + 1) * α + 1) : ℝ) : ℂ) *
          ∑ ℓ ∈ Finset.Ico 1 (k + 1),
            coeff α lam 0 nu (2 * ℓ - 1) * coeff α lam 0 nu (2 * (k + 1 - ℓ) - 1)) := by
  set c := coeff α lam 0 nu with hc
  have hrec : ∀ j, c (j + 2) =
      lam * (∑ ℓ ∈ Finset.Ico 1 (j + 1), c ℓ * c (j + 1 - ℓ)) *
        ((Real.Gamma (α * ((j + 1 : ℕ) : ℝ) + 1) /
          Real.Gamma (α * ((j + 1 : ℕ) : ℝ) + α + 1) : ℝ) : ℂ) := by
    intro j
    rw [hc, coeff,
      Finset.sum_attach (Finset.Ico 1 (j + 1)) (fun ℓ => coeff α lam 0 nu ℓ * coeff α lam 0 nu (j + 1 - ℓ))]
    simp only [zero_mul, add_zero]
  have hev : ∀ k, 1 ≤ k → c (2 * k) = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      rw [show 2 * k = (2 * k - 2) + 2 by omega, hrec, show 2 * k - 2 + 1 = 2 * k - 1 by omega,
        odd_sum c (2 * k - 1) (by omega) (fun k' hk' hk'2 => ih k' (by omega) hk'),
        mul_zero, zero_mul]
  refine ⟨hev, fun k hk => odd_sum c (2 * k - 1) (by omega) (fun k' hk' _ => hev k' hk'), ?_, ?_⟩
  · show c 1 = _
    rw [hc, coeff]
  · intro k hk
    rw [show 2 * (k + 1) - 1 = (2 * k - 1) + 2 by omega, hrec, show 2 * k - 1 + 1 = 2 * k by omega]
    have hg1 : α * ((2 * k : ℕ) : ℝ) + 1 = 2 * α * k + 1 := by push_cast; ring
    have hg2 : α * ((2 * k : ℕ) : ℝ) + α + 1 = (2 * k + 1) * α + 1 := by push_cast; ring
    rw [hg1, hg2]
    have hsum : ∑ ℓ ∈ Finset.Ico 1 (2 * k), c ℓ * c (2 * k - ℓ) =
        ∑ ℓ ∈ Finset.Ico 1 (k + 1), c (2 * ℓ - 1) * c (2 * (k + 1 - ℓ) - 1) := by
      rw [← Finset.sum_filter_add_sum_filter_not _ (fun ℓ => ℓ % 2 = 1)]
      have hzero : ∑ ℓ ∈ (Finset.Ico 1 (2 * k)).filter (fun ℓ => ¬ ℓ % 2 = 1),
          c ℓ * c (2 * k - ℓ) = 0 := by
        apply Finset.sum_eq_zero
        intro ℓ hℓ
        rw [Finset.mem_filter, Finset.mem_Ico] at hℓ
        rw [show ℓ = 2 * (ℓ / 2) by omega, hev (ℓ / 2) (by omega), zero_mul]
      rw [hzero, add_zero]
      refine Finset.sum_nbij' (fun ℓ => (ℓ + 1) / 2) (fun m => 2 * m - 1) ?_ ?_ ?_ ?_ ?_
      · intro ℓ hℓ
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ico] at hℓ ⊢
        omega
      · intro m hm
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ico] at hm ⊢
        omega
      · intro ℓ hℓ
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ico] at hℓ
        omega
      · intro m hm
        simp only [Finset.mem_coe, Finset.mem_Ico] at hm
        omega
      · intro ℓ hℓ
        rw [Finset.mem_filter, Finset.mem_Ico] at hℓ
        congr 2 <;> omega
    rw [hsum]
    ring
