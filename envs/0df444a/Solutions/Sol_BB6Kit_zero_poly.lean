-- Prove2me | solution 1 for BB6Kit.zero_poly
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @alon yuval
-- created : 2026-11-24T08:13:52.617957+00:00
-- url     : https://prove2.me/submissions/09891225-b582-42e5-8b8f-71026e0fef80
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BB6Delta
import Definitions.Def_BB6Kit
import Theorems.Thm_BB6Kit_gouillon_311
import Theorems.Thm_BB6Kit_lemma317
import Theorems.Thm_BB6Kit_lemma321

open Finset

lemma ZPmem_rowSet {K L : ℕ} (p : ℕ × ℕ × ℕ) :
    p ∈ BB6Kit.rowSet K L ↔ p.1 < K ∧ p.2.1 < K ∧ p.2.2 < L ∧ p.1 + p.2.1 ≤ K - 1 := by
  unfold BB6Kit.rowSet
  simp only [mem_filter, mem_product, mem_range]
  tauto

theorem solution (K L R S T N b1 b2 b3 α1 α2 α3 R1 S1 T1 R2 S2 T2 R3 S3 T3 : ℕ) (χ : ℝ)
    (hK : 3 ≤ K) (hL : 5 ≤ L) (hN : N = K * (K + 1) * L / 2) (hRST : N ≤ R * S * T)
    (hα1 : 1 < α1) (hα2 : 1 < α2) (hα3 : 1 < α3) (hind : BB6Kit.MultIndep α1 α2 α3)
    (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3) (hgcd : Nat.gcd (Nat.gcd b1 b2) b3 = 1)
    (hΛ : ((b1 : ℝ) * Real.log (α1 : ℝ) + (b2 : ℝ) * Real.log (α2 : ℝ) - (b3 : ℝ) * Real.log (α3 : ℝ)) ≠ 0)
    (hpos : 0 < R1 ∧ 0 < S1 ∧ 0 < T1 ∧ 0 < R2 ∧ 0 < S2 ∧ 0 < T2 ∧ 0 < R3 ∧ 0 < S3 ∧ 0 < T3)
    (h27 : R1 + R2 + R3 < R ∧ S1 + S2 + S3 < S ∧ T1 + T2 + T3 < T) (hχ : 0 < χ)
    (h29 : (K : ℝ) * (max (max ((R1 : ℝ) + S1 + 1) ((S1 : ℝ) + T1 + 1)) (max ((R1 : ℝ) + T1 + 1) (χ * Real.sqrt (((R1 : ℝ) + 1) * ((S1 : ℝ) + 1) * ((T1 : ℝ) + 1))))) < (((R1 : ℝ) + 1) * ((S1 : ℝ) + 1) * ((T1 : ℝ) + 1)))
    (h210 : L < ((Finset.range (R1 + 1) ×ˢ Finset.range (S1 + 1) ×ˢ Finset.range (T1 + 1)).image (fun x => α1 ^ x.1 * α2 ^ x.2.1 * α3 ^ x.2.2)).card)
    (h211 : 2 * K * L < ((Finset.range (R2 + 1) ×ˢ Finset.range (S2 + 1) ×ˢ Finset.range (T2 + 1)).image (fun x => α1 ^ x.1 * α2 ^ x.2.1 * α3 ^ x.2.2)).card)
    (h212 : K ^ 2 < (R2 + 1) * (S2 + 1) * (T2 + 1))
    (h213 : 3 * K ^ 2 * L < (R3 + 1) * (S3 + 1) * (T3 + 1))
    (h214 : ¬ (b1 ≤ max R1 R2 ∧ b2 ≤ max S1 S2 ∧ b3 ≤ max T1 T2))
    (h215 : ¬ (∃ u1 u2 u3 : ℤ, u1 * (b1 : ℤ) + u2 * (b2 : ℤ) + u3 * (b3 : ℤ) = 0 ∧ Int.gcd (Int.gcd u1 u2 : ℤ) u3 = 1 ∧
        (|u1| : ℝ) ≤ ((S1 : ℝ) + 1) * ((T1 : ℝ) + 1) / ((max (max ((R1 : ℝ) + S1 + 1) ((S1 : ℝ) + T1 + 1)) (max ((R1 : ℝ) + T1 + 1) (χ * Real.sqrt (((R1 : ℝ) + 1) * ((S1 : ℝ) + 1) * ((T1 : ℝ) + 1))))) - max (S1 : ℝ) T1) ∧
        (|u2| : ℝ) ≤ ((R1 : ℝ) + 1) * ((T1 : ℝ) + 1) / ((max (max ((R1 : ℝ) + S1 + 1) ((S1 : ℝ) + T1 + 1)) (max ((R1 : ℝ) + T1 + 1) (χ * Real.sqrt (((R1 : ℝ) + 1) * ((S1 : ℝ) + 1) * ((T1 : ℝ) + 1))))) - max (R1 : ℝ) T1) ∧
        (|u3| : ℝ) ≤ ((R1 : ℝ) + 1) * ((S1 : ℝ) + 1) / ((max (max ((R1 : ℝ) + S1 + 1) ((S1 : ℝ) + T1 + 1)) (max ((R1 : ℝ) + T1 + 1) (χ * Real.sqrt (((R1 : ℝ) + 1) * ((S1 : ℝ) + 1) * ((T1 : ℝ) + 1))))) - max (R1 : ℝ) S1))) :
    ∀ c : ℕ × ℕ × ℕ → ℝ,
      (∀ r < R, ∀ s < S, ∀ t < T,
        ∑ q ∈ BB6Kit.rowSet K L, c q * ((r : ℝ) + t * (((b1 / Nat.gcd b1 b3 : ℕ) : ℝ) / ((b3 / Nat.gcd b1 b3 : ℕ) : ℝ))) ^ q.1 * ((s : ℝ) + t * (((b2 / Nat.gcd b2 b3 : ℕ) : ℝ) / ((b3 / Nat.gcd b2 b3 : ℕ) : ℝ))) ^ q.2.1 *
          ((α1 : ℝ) ^ r * (α2 : ℝ) ^ s * (α3 : ℝ) ^ t) ^ q.2.2 = 0) →
      ∀ q ∈ BB6Kit.rowSet K L, c q = 0 := by
  intro c hc
  have hg13 : 0 < Nat.gcd b1 b3 := Nat.gcd_pos_of_pos_right _ hb3
  have hg23 : 0 < Nat.gcd b2 b3 := Nat.gcd_pos_of_pos_right _ hb3
  have hb3r : (0 : ℝ) < b3 := by exact_mod_cast hb3
  have hb3ne : (b3 : ℝ) ≠ 0 := hb3r.ne'
  have hβ1 : ((b1 / Nat.gcd b1 b3 : ℕ) : ℝ) / ((b3 / Nat.gcd b1 b3 : ℕ) : ℝ) = (b1 : ℝ) / b3 := by
    have hg : ((Nat.gcd b1 b3 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hg13.ne'
    rw [Nat.cast_div (Nat.gcd_dvd_left b1 b3) hg, Nat.cast_div (Nat.gcd_dvd_right b1 b3) hg]
    first
    | (field_simp; ring)
    | field_simp
  have hβ2 : ((b2 / Nat.gcd b2 b3 : ℕ) : ℝ) / ((b3 / Nat.gcd b2 b3 : ℕ) : ℝ) = (b2 : ℝ) / b3 := by
    have hg : ((Nat.gcd b2 b3 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hg23.ne'
    rw [Nat.cast_div (Nat.gcd_dvd_left b2 b3) hg, Nat.cast_div (Nat.gcd_dvd_right b2 b3) hg]
    first
    | (field_simp; ring)
    | field_simp
  rw [hβ1, hβ2] at hc
  have hα1r : (0 : ℝ) < α1 := by exact_mod_cast (show 0 < α1 by omega)
  have hα2r : (0 : ℝ) < α2 := by exact_mod_cast (show 0 < α2 by omega)
  have hα3r : (0 : ℝ) < α3 := by exact_mod_cast (show 0 < α3 by omega)
  obtain ⟨hR1, hS1, hT1, hR2, hS2, hT2, hR3, hS3, hT3⟩ := hpos
  obtain ⟨hRR, hSS, hTT⟩ := h27
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℕ × ℕ × ℕ → ℝ × ℝ × ℝ, ψ = fun x =>
      ((x.1 : ℝ) + x.2.2 * ((b1 : ℝ) / b3), (x.2.1 : ℝ) + x.2.2 * ((b2 : ℝ) / b3),
        (α1 : ℝ) ^ x.1 * (α2 : ℝ) ^ x.2.1 * (α3 : ℝ) ^ x.2.2) := ⟨_, rfl⟩
  have hthird : ∀ (X Y Z : ℕ), ((range (X + 1) ×ˢ range (Y + 1) ×ˢ range (Z + 1)).image ψ).image (fun p => p.2.2) =
      ((range (X + 1) ×ˢ range (Y + 1) ×ˢ range (Z + 1)).image
        (fun x => α1 ^ x.1 * α2 ^ x.2.1 * α3 ^ x.2.2)).image (fun n : ℕ => (n : ℝ)) := by
    intro X Y Z
    rw [image_image, image_image]
    apply image_congr
    intro x _
    simp only [Function.comp, hψ]
    push_cast
    ring
  have hfirst2 : ∀ (X Y Z : ℕ), ((range (X + 1) ×ˢ range (Y + 1) ×ˢ range (Z + 1)).image ψ).image (fun p => (p.1, p.2.1)) =
      (range (X + 1) ×ˢ range (Y + 1) ×ˢ range (Z + 1)).image
        (fun x => ((x.1 : ℝ) + x.2.2 * ((b1 : ℝ) / b3), (x.2.1 : ℝ) + x.2.2 * ((b2 : ℝ) / b3))) := by
    intro X Y Z
    rw [image_image]
    apply image_congr
    intro x _
    simp only [Function.comp, hψ]
  refine BB6Kit.gouillon_311 K L (by omega) (by omega)
    ((range (R1 + 1) ×ˢ range (S1 + 1) ×ˢ range (T1 + 1)).image ψ)
    ((range (R2 + 1) ×ˢ range (S2 + 1) ×ˢ range (T2 + 1)).image ψ)
    ((range (R3 + 1) ×ˢ range (S3 + 1) ×ˢ range (T3 + 1)).image ψ)
    ?_ ?_ ?_ ?_ ?_ ?_ (BB6Kit.rowSet K L) ?_ c ?_
  · -- third coordinates are nonzero
    intro p hp
    simp only [mem_union, mem_image] at hp
    rcases hp with ((⟨x, _, rfl⟩ | ⟨x, _, rfl⟩) | ⟨x, _, rfl⟩) <;>
    · rw [hψ]
      exact (mul_pos (mul_pos (pow_pos hα1r _) (pow_pos hα2r _)) (pow_pos hα3r _)).ne'
  · -- (3.17)(a) via Lemmas 3.17 and 3.21 and (2.9)
    intro l m hlm
    have h317 := BB6Kit.lemma317 b1 b2 b3 R1 S1 T1 hb1 hb2 hb3 hgcd (by
      rintro ⟨h1, h2, h3⟩
      exact h214 ⟨le_trans h1 (le_max_left _ _), le_trans h2 (le_max_left _ _), le_trans h3 (le_max_left _ _)⟩)
    have h321 := BB6Kit.lemma321 R1 S1 T1 b1 b2 b3 χ hR1 hS1 hT1 hb1 hb2 hb3 hgcd hχ h317 h215 l m hlm
    have himg : ((range (R1 + 1) ×ˢ range (S1 + 1) ×ˢ range (T1 + 1)).image ψ).image (fun p => l * p.1 + m * p.2.1) =
        (range (R1 + 1) ×ˢ range (S1 + 1) ×ˢ range (T1 + 1)).image
          (fun x => l * ((x.1 : ℝ) + x.2.2 * ((b1 : ℝ) / b3)) + m * ((x.2.1 : ℝ) + x.2.2 * ((b2 : ℝ) / b3))) := by
      rw [image_image]
      apply image_congr
      intro x _
      simp only [Function.comp, hψ]
    rw [himg]
    have hMpos : (0 : ℝ) < max (max ((R1 : ℝ) + S1 + 1) ((S1 : ℝ) + T1 + 1))
        (max ((R1 : ℝ) + T1 + 1) (χ * Real.sqrt (((R1 : ℝ) + 1) * ((S1 : ℝ) + 1) * ((T1 : ℝ) + 1)))) := by
      have : (0 : ℝ) < (R1 : ℝ) + S1 + 1 := by positivity
      exact lt_of_lt_of_le this (le_trans (le_max_left _ _) (le_max_left _ _))
    push_cast at h321
    have hlt : (K : ℝ) < ((range (R1 + 1) ×ˢ range (S1 + 1) ×ˢ range (T1 + 1)).image
          (fun x => l * ((x.1 : ℝ) + x.2.2 * ((b1 : ℝ) / b3)) + m * ((x.2.1 : ℝ) + x.2.2 * ((b2 : ℝ) / b3)))).card := by
      by_contra hcon
      push_neg at hcon
      have := mul_le_mul_of_nonneg_left hcon hMpos.le
      nlinarith [h29, h321, this]
    exact_mod_cast hlt
  · -- (3.17)(b) is (2.10)
    rw [hthird, card_image_of_injective _ Nat.cast_injective]
    exact h210
  · -- (3.18)(a) from (2.11)
    intro l m _
    have h1 : ((range (R2 + 1) ×ˢ range (S2 + 1) ×ˢ range (T2 + 1)).image ψ).image (fun p => p.2.2) =
        (((range (R2 + 1) ×ˢ range (S2 + 1) ×ˢ range (T2 + 1)).image ψ).image
          (fun p => (l * p.1 + m * p.2.1, p.2.2))).image Prod.snd := by
      rw [image_image, image_image, image_image]
      rfl
    have h2 := card_image_le (s := ((range (R2 + 1) ×ˢ range (S2 + 1) ×ˢ range (T2 + 1)).image ψ).image
      (fun p => (l * p.1 + m * p.2.1, p.2.2))) (f := Prod.snd)
    rw [← h1, hthird, card_image_of_injective _ Nat.cast_injective] at h2
    omega
  · -- (3.18)(b) via Lemma 3.17 and (2.12)
    rw [hfirst2, BB6Kit.lemma317 b1 b2 b3 R2 S2 T2 hb1 hb2 hb3 hgcd (by
      rintro ⟨h1, h2, h3⟩
      exact h214 ⟨le_trans h1 (le_max_right _ _), le_trans h2 (le_max_right _ _), le_trans h3 (le_max_right _ _)⟩)]
    exact h212
  · -- (3.19): ψ is injective because Λ ≠ 0
    rw [card_image_of_injOn, card_product, card_product, card_range, card_range, card_range]
    · rw [← mul_assoc]
      exact h213
    intro x _ y _ hxy
    simp only [hψ, Prod.mk.injEq] at hxy
    obtain ⟨h1, h2, h3⟩ := hxy
    have hinv : (b3 : ℝ) * (b3 : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hb3ne
    rw [div_eq_mul_inv] at h1 h2
    have e1 : ((x.1 : ℝ) - y.1) * b3 = -(((x.2.2 : ℝ) - y.2.2) * b1) := by
      linear_combination (b3 : ℝ) * h1 - ((x.2.2 : ℝ) - y.2.2) * b1 * hinv
    have e2 : ((x.2.1 : ℝ) - y.2.1) * b3 = -(((x.2.2 : ℝ) - y.2.2) * b2) := by
      linear_combination (b3 : ℝ) * h2 - ((x.2.2 : ℝ) - y.2.2) * b2 * hinv
    have hl := congrArg Real.log h3
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_pow, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow] at hl
    have key : ((x.2.2 : ℝ) - y.2.2) * ((b1 : ℝ) * Real.log (α1 : ℝ) + (b2 : ℝ) * Real.log (α2 : ℝ) -
        (b3 : ℝ) * Real.log (α3 : ℝ)) = 0 := by
      linear_combination (-(b3 : ℝ)) * hl + Real.log (α1 : ℝ) * e1 + Real.log (α2 : ℝ) * e2
    have ht : (x.2.2 : ℝ) = y.2.2 := by
      rcases mul_eq_zero.mp key with h | h
      · linarith
      · exact absurd h hΛ
    rw [ht, sub_self, zero_mul, neg_zero] at e1 e2
    have hr : (x.1 : ℝ) = y.1 := by
      have := (mul_eq_zero.mp e1).resolve_right hb3ne
      linarith
    have hs : (x.2.1 : ℝ) = y.2.1 := by
      have := (mul_eq_zero.mp e2).resolve_right hb3ne
      linarith
    exact Prod.ext (by exact_mod_cast hr) (Prod.ext (by exact_mod_cast hs) (by exact_mod_cast ht))
  · -- degrees
    intro q hq
    have := (ZPmem_rowSet q).mp hq
    omega
  · -- vanishing on the sumset, by (2.7)
    intro p1 hp1 p2 hp2 p3 hp3
    rw [mem_image] at hp1 hp2 hp3
    obtain ⟨x1, hx1, rfl⟩ := hp1
    obtain ⟨x2, hx2, rfl⟩ := hp2
    obtain ⟨x3, hx3, rfl⟩ := hp3
    simp only [mem_product, mem_range] at hx1 hx2 hx3
    have hv := hc (x1.1 + x2.1 + x3.1) (by omega) (x1.2.1 + x2.2.1 + x3.2.1) (by omega)
      (x1.2.2 + x2.2.2 + x3.2.2) (by omega)
    refine Eq.trans (sum_congr rfl (fun q _ => ?_)) hv
    simp only [hψ]
    push_cast
    ring
