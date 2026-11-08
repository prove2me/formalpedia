-- Prove2me | solution 1 for BaconThesis.Multilevel.eq_12_3_to_12_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T22:48:53.498733+00:00
-- url     : https://prove2.me/submissions/ea316426-f4b9-40ce-9d9f-a165e32dc1eb

import Mathlib
import Definitions.Def_BaconThesis_Multilevel_sumSigma
import Definitions.Def_BaconThesis_Multilevel_Gmat

open scoped Matrix

namespace Aux_BTM1234

open BaconThesis.Multilevel

theorem dsum {N : ℕ} (F : Fin N → Fin N → ℂ) (p q : Fin N)
    (h : ∀ i j, (i ≠ p ∨ j ≠ q) → F i j = 0) : ∑ i, ∑ j, F i j = F p q := by
  rw [Finset.sum_eq_single p (fun i _ hi => Finset.sum_eq_zero (fun j _ => h i j (Or.inl hi)))
    (by simp), Finset.sum_eq_single q (fun j _ hj => h p j (Or.inr hj)) (by simp)]

theorem sumSigma_eq {N : ℕ} (g : Fin N → Fin N → ℂ) : sumSigma g = Gmat g := by
  ext p q
  have hterm : ∀ i j : Fin N,
      ((if j < i then g i j • (Matrix.single i j (1 : ℂ) + Matrix.single j i 1) else 0 :
        Matrix (Fin N) (Fin N) ℂ)) p q =
        (if i = p ∧ j = q ∧ j < i then g i j else 0) +
          (if j = p ∧ i = q ∧ j < i then g i j else 0) := by
    intro i j
    by_cases hji : j < i
    · rw [if_pos hji]
      simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.single_apply, smul_eq_mul, hji,
        and_true]
      split_ifs <;> ring
    · rw [if_neg hji]
      simp [hji]
  simp only [sumSigma, Matrix.sum_apply]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hterm i j))]
  simp only [Finset.sum_add_distrib]
  rw [dsum (fun i j => if i = p ∧ j = q ∧ j < i then g i j else 0) p q
      (fun i j hij => by
        rw [if_neg]
        rintro ⟨h1, h2, -⟩
        rcases hij with h | h <;> contradiction),
    dsum (fun i j => if j = p ∧ i = q ∧ j < i then g i j else 0) q p
      (fun i j hij => by
        rw [if_neg]
        rintro ⟨h1, h2, -⟩
        rcases hij with h | h <;> contradiction)]
  simp only [Gmat, Matrix.of_apply, true_and]
  rcases lt_trichotomy p q with h | rfl | h
  · simp [h, not_lt_of_gt h]
  · simp
  · simp [h, not_lt_of_gt h]

theorem Gmat_conj {N : ℕ} (g : Fin N → Fin N → ℂ) :
    (Gmat g)ᴴ = Gmat (fun i j => star (g i j)) := by
  ext p q
  simp only [Matrix.conjTranspose_apply, Gmat, Matrix.of_apply]
  rcases lt_trichotomy p q with h | rfl | h
  · rw [if_pos h, if_neg (not_lt_of_gt h), if_pos h]
  · simp
  · rw [if_neg (not_lt_of_gt h), if_pos h, if_pos h]

end Aux_BTM1234

open BaconThesis.Multilevel Aux_BTM1234 in
theorem solution {N : ℕ} (g : Fin N → Fin N → ℂ) :
    sumSigma g = Gmat g ∧
      ∀ (ψ : Fin N → ℂ) (α₁ α₂ : ℂ), ψ ≠ 0 →
        sumSigma g *ᵥ ψ = α₁ • ψ →
        sumSigma (fun i j => star (g i j)) *ᵥ ψ = α₂ • ψ →
        α₁ = star α₂ ∧ Gmat g *ᵥ ψ = α₁ • ψ := by
  refine ⟨sumSigma_eq g, fun ψ α₁ α₂ hψ h1 h2 => ?_⟩
  rw [sumSigma_eq] at h1 h2
  refine ⟨?_, h1⟩
  have hD : star ψ ⬝ᵥ ψ ≠ 0 := by
    open ComplexOrder in exact fun h => hψ (dotProduct_star_self_eq_zero.mp h)
  have e1 : star ψ ⬝ᵥ (Gmat g *ᵥ ψ) = α₁ * (star ψ ⬝ᵥ ψ) := by
    rw [h1, dotProduct_smul, smul_eq_mul]
  have hv : star ψ ᵥ* Gmat g = star (Gmat (fun i j => star (g i j)) *ᵥ ψ) := by
    rw [Matrix.star_mulVec, ← Gmat_conj, Matrix.conjTranspose_conjTranspose]
  have e2 : star ψ ⬝ᵥ (Gmat g *ᵥ ψ) = star α₂ * (star ψ ⬝ᵥ ψ) := by
    rw [Matrix.dotProduct_mulVec, hv, h2, star_smul, smul_dotProduct, smul_eq_mul]
  exact mul_right_cancel₀ hD (e1.symm.trans e2)
