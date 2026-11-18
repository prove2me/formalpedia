-- Prove2me | solution 1 for BBPSSW.Distill.random_parity_agree
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T09:43:08.75707+00:00
-- url     : https://prove2.me/submissions/56e6feff-febc-4571-9b94-e7ec5db5a2d8

import Mathlib
namespace BBPSSW.Distill

theorem random_parity_agree (n r : ℕ) (x y : Fin n → ZMod 2) (hxy : x ≠ y) :
    ((Finset.univ.filter fun S : Fin r → Finset (Fin n) =>
          ∀ j, ∑ i ∈ S j, x i = ∑ i ∈ S j, y i).card : ℝ) /
        (Fintype.card (Fin r → Finset (Fin n)) : ℝ) ≤ (1 / 2 : ℝ) ^ r := by
  classical
  set A := Finset.univ.filter (fun T : Finset (Fin n) => ∑ i ∈ T, x i = ∑ i ∈ T, y i) with hA
  obtain ⟨i0, hi0⟩ : ∃ i0, x i0 ≠ y i0 := by
    by_contra h; push_neg at h; exact hxy (funext h)
  let g : Finset (Fin n) → Finset (Fin n) := fun T => if i0 ∈ T then T.erase i0 else insert i0 T
  have hg_inv : ∀ T, g (g T) = T := by
    intro T
    by_cases h : i0 ∈ T
    · simp [g, h, Finset.insert_erase h]
    · simp [g, h, Finset.erase_insert h]
  have hgA : ∀ T ∈ A, g T ∈ Aᶜ := by
    intro T hT
    simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and] at hT
    simp only [hA, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases h : i0 ∈ T
    · simp only [g, h, if_true]
      rw [Finset.sum_erase_eq_sub h, Finset.sum_erase_eq_sub h, hT]
      intro h2; exact hi0 (by linear_combination -h2)
    · simp only [g, h, if_false]
      rw [Finset.sum_insert h, Finset.sum_insert h, hT]
      intro h2; exact hi0 (by linear_combination h2)
  have hcardA : 2 * A.card ≤ 2 ^ n := by
    have h1 : A.card ≤ Aᶜ.card :=
      Finset.card_le_card_of_injOn g (fun T hT => hgA T hT)
        (fun a _ b _ hab => by rw [← hg_inv a, hab, hg_inv b])
    have h2 : A.card + Aᶜ.card = 2 ^ n := by
      rw [Finset.card_add_card_compl, Fintype.card_finset, Fintype.card_fin]
    omega
  have hfilter : (Finset.univ.filter fun S : Fin r → Finset (Fin n) =>
          ∀ j, ∑ i ∈ S j, x i = ∑ i ∈ S j, y i) = Fintype.piFinset (fun _ => A) := by
    ext S; simp [hA]
  rw [hfilter, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Fintype.card_fun, Fintype.card_finset, Fintype.card_fin, Fintype.card_fin]
  push_cast
  rw [← div_pow]
  apply pow_le_pow_left₀ (by positivity)
  rw [div_le_iff₀ (by positivity)]
  have : (2 : ℝ) * A.card ≤ 2 ^ n := by exact_mod_cast hcardA
  linarith

end BBPSSW.Distill

theorem solution (n r : ℕ) (x y : Fin n → ZMod 2) (hxy : x ≠ y) :
    ((Finset.univ.filter fun S : Fin r → Finset (Fin n) =>
          ∀ j, ∑ i ∈ S j, x i = ∑ i ∈ S j, y i).card : ℝ) /
        (Fintype.card (Fin r → Finset (Fin n)) : ℝ) ≤ (1 / 2 : ℝ) ^ r :=
  BBPSSW.Distill.random_parity_agree n r x y hxy
