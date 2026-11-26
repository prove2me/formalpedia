-- Prove2me | solution 1 for Erdos287.dispersion_frequency_determinant_energy
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T18:51:29.002679+00:00
-- url     : https://prove2.me/submissions/8698dd93-4198-44bb-8440-d1a91425005e

import Mathlib

open Finset

set_option autoImplicit false

private theorem determinant_step (a b : ℕ) (hb : 0 < b) (hab : a.Coprime b)
    (u v : ℤ × ℤ) (h : u.1 * (b : ℤ) - u.2 * (a : ℤ) = v.1 * (b : ℤ) - v.2 * (a : ℤ)) :
    ∃ t : ℤ, u.1 - v.1 = (a : ℤ) * t ∧ u.2 - v.2 = (b : ℤ) * t := by
  have hb0 : (b : ℤ) ≠ 0 := by exact_mod_cast hb.ne'
  have he : (u.2 - v.2) * (a : ℤ) = (b : ℤ) * (u.1 - v.1) := by
    linear_combination -h
  have hc : IsCoprime (b : ℤ) (a : ℤ) := Nat.isCoprime_iff_coprime.mpr hab.symm
  have hdiv : (b : ℤ) ∣ (u.2 - v.2) * (a : ℤ) := ⟨u.1 - v.1, he⟩
  obtain ⟨t, ht⟩ := hc.dvd_of_dvd_mul_right hdiv
  refine ⟨t, mul_left_cancel₀ hb0 ?_, ht⟩
  calc
    (b : ℤ) * (u.1 - v.1) = (u.2 - v.2) * (a : ℤ) := he.symm
    _ = (b : ℤ) * ((a : ℤ) * t) := by rw [ht]; ring

private theorem scaled_interval (B H : ℕ) (hB : 0 < B) (t : ℤ)
    (hl : -(H : ℤ) ≤ (B : ℤ) * t) (hu : (B : ℤ) * t ≤ H) :
    t ∈ Icc (-(↑(H / B) : ℤ)) (↑(H / B) : ℤ) := by
  have hB' : (0 : ℤ) < B := by exact_mod_cast hB
  have hp := Int.ediv_le_ediv hB' hu
  have hn : (B : ℤ) * (-t) ≤ H := by rw [mul_neg]; omega
  have hq := Int.ediv_le_ediv hB' hn
  rw [Int.mul_ediv_cancel_left _ hB'.ne', ← Int.natCast_div] at hp hq
  exact mem_Icc.mpr ⟨by omega, hp⟩

/-- Count pairs of frequency pairs with equal determinant and nonzero
frequency pairs on the zero determinant. The larger primitive slope can be
placed in the second coordinate. -/
theorem solution (a b H : ℕ) (hb : 0 < b) (hab : a.Coprime b) :
    let T := Finset.Icc (-(H : ℤ)) (H : ℤ)
    let P := T ×ˢ T
    let det := fun u : ℤ × ℤ => u.1 * (b : ℤ) - u.2 * (a : ℤ)
    (((P ×ˢ P).filter (fun p => det p.1 = det p.2)).card ≤
      (2 * H + 1) ^ 2 * (2 * (2 * H / b) + 1)) ∧
    ((P.filter (fun u => det u = 0 ∧ u.2 ≠ 0)).card ≤ 2 * (H / b)) := by
  classical
  dsimp only
  let T := Icc (-(H : ℤ)) (H : ℤ)
  let P := T ×ˢ T
  let det := fun u : ℤ × ℤ => u.1 * (b : ℤ) - u.2 * (a : ℤ)
  change (((P ×ˢ P).filter (fun p => det p.1 = det p.2)).card ≤ _) ∧
    ((P.filter (fun u => det u = 0 ∧ u.2 ≠ 0)).card ≤ _)
  have hb0 : (b : ℤ) ≠ 0 := by exact_mod_cast hb.ne'
  have hcard (D : ℕ) : (Icc (-(D : ℤ)) (D : ℤ)).card = 2 * D + 1 := by
    rw [Int.card_Icc]
    omega
  constructor
  · let U := Icc (-(↑(2 * H / b) : ℤ)) (↑(2 * H / b) : ℤ)
    let F := (P ×ˢ P).filter (fun p => det p.1 = det p.2)
    let encode (p : (ℤ × ℤ) × (ℤ × ℤ)) := (p.1, (p.1.2 - p.2.2) / (b : ℤ))
    have hparameter (p : (ℤ × ℤ) × (ℤ × ℤ)) (hp : p ∈ F) :
        p.1.1 - p.2.1 = (a : ℤ) * (encode p).2 ∧ p.1.2 - p.2.2 = (b : ℤ) * (encode p).2 := by
      obtain ⟨t, h₁, h₂⟩ := determinant_step a b hb hab p.1 p.2 (mem_filter.mp hp).2
      have ht : (encode p).2 = t := by
        dsimp only [encode]
        rw [h₂, Int.mul_ediv_cancel_left _ hb0]
      simpa only [ht] using And.intro h₁ h₂
    have hbound : F.card ≤ (P ×ˢ U).card := by
      apply card_le_card_of_injOn encode
      · intro p hp
        have hpF : p ∈ F := hp
        have hmem := mem_product.mp (mem_filter.mp hpF).1
        have h₁ := mem_Icc.mp (mem_product.mp hmem.1).2
        have h₂ := mem_Icc.mp (mem_product.mp hmem.2).2
        change (p.1, (encode p).2) ∈ P ×ˢ U
        refine mem_product.mpr ⟨hmem.1, ?_⟩
        apply scaled_interval b (2 * H) hb
        all_goals rw [← (hparameter p hpF).2]; push_cast; omega
      · intro p hp q hq he
        have hf := congrArg Prod.fst he
        have hs := congrArg Prod.snd he
        change p.1 = q.1 at hf
        change (encode p).2 = (encode q).2 at hs
        have h₁ := hparameter p hp
        have h₂ := hparameter q hq
        have hf₁ : p.1.1 = q.1.1 := congrArg Prod.fst hf
        have hf₂ : p.1.2 = q.1.2 := congrArg Prod.snd hf
        rw [hf₁, hf₂, hs] at h₁
        exact Prod.ext hf (Prod.ext (sub_right_inj.mp (h₁.1.trans h₂.1.symm))
          (sub_right_inj.mp (h₁.2.trans h₂.2.symm)))
    calc
      F.card ≤ (P ×ˢ U).card := hbound
      _ = (2 * H + 1) ^ 2 * (2 * (2 * H / b) + 1) := by
        simp only [P, T, U, card_product, hcard, pow_two]
  · let U := Icc (-(↑(H / b) : ℤ)) (↑(H / b) : ℤ)
    let F := P.filter (fun u => det u = 0 ∧ u.2 ≠ 0)
    let encode (u : ℤ × ℤ) := u.2 / (b : ℤ)
    have hparameter (u : ℤ × ℤ) (hu : u ∈ F) :
        u.1 = (a : ℤ) * encode u ∧ u.2 = (b : ℤ) * encode u := by
      have h : det u = det (0, 0) := by simpa [det] using (mem_filter.mp hu).2.1
      obtain ⟨t, h₁, h₂⟩ := determinant_step a b hb hab u (0, 0) h
      simp only [sub_zero] at h₁ h₂
      have ht : encode u = t := by
        dsimp only [encode]
        rw [h₂, Int.mul_ediv_cancel_left _ hb0]
      simpa only [ht] using And.intro h₁ h₂
    have hbound : F.card ≤ (U.erase 0).card := by
      apply card_le_card_of_injOn encode
      · intro u hu
        have huF : u ∈ F := hu
        have hcond := mem_filter.mp huF
        have hmem := mem_Icc.mp (mem_product.mp hcond.1).2
        refine mem_erase.mpr ⟨?_, scaled_interval b H hb _ ?_ ?_⟩
        · intro he
          exact hcond.2.2 (by rw [(hparameter u huF).2, he, mul_zero])
        · rw [← (hparameter u huF).2]
          exact hmem.1
        · rw [← (hparameter u huF).2]
          exact hmem.2
      · intro u hu v hv he
        rw [Prod.ext_iff]
        simpa only [he] using And.intro
          ((hparameter u hu).1.trans (by rw [he, ← (hparameter v hv).1]))
          ((hparameter u hu).2.trans (by rw [he, ← (hparameter v hv).2]))
    have hnonneg : (0 : ℤ) ≤ ↑(H / b) := Int.natCast_nonneg _
    have hzero : (0 : ℤ) ∈ U := mem_Icc.mpr ⟨neg_nonpos.mpr hnonneg, hnonneg⟩
    have hU : U.card = 2 * (H / b) + 1 := hcard (H / b)
    calc
      F.card ≤ (U.erase 0).card := hbound
      _ = 2 * (H / b) := by rw [card_erase_of_mem hzero, hU, Nat.add_sub_cancel]

