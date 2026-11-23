-- Prove2me | solution 1 for BLTCounting.AccuracySpace.lemma_4_6
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:22:59.312819+00:00
-- url     : https://prove2.me/submissions/efc282dd-a389-4942-a9d1-13d60ac08366
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BLTCounting_AccuracySpace_MatrixNorms
import Definitions.Def_BLTCounting_AccuracySpace_FourierKernel
import Definitions.Def_BLTCounting_AccuracySpace_Sequences
import Definitions.Def_BLTCounting_AccuracySpace_GeometricBlocks
import Theorems.Thm_BLTCounting_AccuracySpace_claim_4_5
import Theorems.Thm_BLTCounting_AccuracySpace_claim_6_1

open Matrix BLTCounting.AccuracySpace

namespace AuxLemma46

lemma c0_even (x : ℝ) : c0 (-x) = c0 x := by
  unfold c0
  have hneg : (-x) / 2 = -(x / 2) := by ring
  rw [hneg, Real.cosh_neg]

lemma c0_nonneg (x : ℝ) : 0 ≤ c0 x := by
  unfold c0
  positivity

lemma c0_le_exp (x : ℝ) : c0 x ≤ Real.exp (-|x| / 4) := by
  unfold c0
  have hcosh : (1 / 2 : ℝ) * Real.exp (|x| / 2) ≤ Real.cosh (x / 2) := by
    rw [Real.cosh_eq]
    rcases le_or_gt 0 x with hx | hx
    · rw [abs_of_nonneg hx]
      have hpos : 0 < Real.exp (-(x / 2)) := Real.exp_pos _
      linarith
    · rw [abs_of_neg hx]
      have hpos : 0 < Real.exp (x / 2) := Real.exp_pos _
      have heq : -x / 2 = -(x / 2) := by ring
      rw [heq]
      linarith
  have hpos_lhs : 0 < (1 / 2 : ℝ) * Real.exp (|x| / 2) := by positivity
  have hinv : 1 / Real.cosh (x / 2) ≤ 2 * Real.exp (-|x| / 2) := by
    have h1 := one_div_le_one_div_of_le hpos_lhs hcosh
    refine le_trans h1 (le_of_eq ?_)
    rw [one_div, mul_inv, show ((1 / 2 : ℝ))⁻¹ = 2 by norm_num, ← Real.exp_neg]
    congr 2
    ring
  have hsqrt : Real.sqrt (1 / Real.cosh (x / 2)) ≤ Real.sqrt 2 * Real.exp (-|x| / 4) := by
    calc
      Real.sqrt (1 / Real.cosh (x / 2))
          ≤ Real.sqrt (2 * Real.exp (-|x| / 2)) := Real.sqrt_le_sqrt hinv
      _ = Real.sqrt 2 * Real.sqrt (Real.exp (-|x| / 2)) :=
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) _
      _ = Real.sqrt 2 * Real.exp (-|x| / 4) := by
        congr 1
        have hsq : Real.exp (-|x| / 2) = Real.exp (-|x| / 4) ^ 2 := by
          rw [sq, ← Real.exp_add]
          congr 1
          ring
        rw [hsq, Real.sqrt_sq (Real.exp_pos _).le]
  calc
    (Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (1 / Real.cosh (x / 2))
        ≤ (Real.sqrt (2 * Real.pi))⁻¹ * (Real.sqrt 2 * Real.exp (-|x| / 4)) :=
      mul_le_mul_of_nonneg_left hsqrt (by positivity)
    _ = (Real.sqrt Real.pi)⁻¹ * Real.exp (-|x| / 4) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), mul_inv]
      have hs2 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
      field_simp [hs2]
    _ ≤ 1 * Real.exp (-|x| / 4) := by
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      have hpi1 : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
      have hs1 : (1 : ℝ) ≤ Real.sqrt Real.pi := by
        simpa using Real.sqrt_le_sqrt hpi1
      exact inv_le_one_of_one_le₀ hs1
    _ = Real.exp (-|x| / 4) := one_mul _

lemma sum_h_exp_le_eight (K : ℕ) {h : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1) :
    ∑ t ∈ Finset.range K, h * Real.exp (-(t : ℝ) * h / 4) ≤ 8 := by
  let r : ℝ := Real.exp (-h / 4)
  have hr_lt : r < 1 := by
    dsimp [r]
    rw [Real.exp_lt_one_iff]
    linarith
  have h1_sub : h / 8 ≤ 1 - r := by
    have hadd : 1 + h / 4 ≤ Real.exp (h / 4) := by linarith [Real.add_one_le_exp (h / 4)]
    have hprod : Real.exp (-h / 4) * Real.exp (h / 4) = 1 := by
      rw [← Real.exp_add]
      have hz : -h / 4 + h / 4 = 0 := by ring
      rw [hz, Real.exp_zero]
    have hr_pos : 0 < r := Real.exp_pos _
    have hle : r * (1 + h / 4) ≤ 1 := by
      dsimp [r]
      nlinarith
    have h2 : h / 4 ≤ 1 := by linarith
    nlinarith
  have hrew : (∑ t ∈ Finset.range K, h * Real.exp (-(t : ℝ) * h / 4)) =
      h * ∑ t ∈ Finset.range K, r ^ t := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    congr 1
    dsimp [r]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hrew, geom_sum_eq (ne_of_lt hr_lt)]
  have hden_pos : 0 < 1 - r := by linarith
  have hr_pow_nn : 0 ≤ r ^ K := pow_nonneg (Real.exp_pos _).le K
  have hgeom : (r ^ K - 1) / (r - 1) = (1 - r ^ K) / (1 - r) := by
    have hne1 : r - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_lt hr_lt)
    have hne2 : 1 - r ≠ 0 := ne_of_gt hden_pos
    field_simp [hne1, hne2]
    ring
  rw [hgeom]
  calc
    h * ((1 - r ^ K) / (1 - r)) ≤ h * (1 / (1 - r)) := by
      refine mul_le_mul_of_nonneg_left ?_ hh0.le
      exact div_le_div_of_nonneg_right (by linarith) hden_pos.le
    _ ≤ h * (1 / (h / 8)) := by
      refine mul_le_mul_of_nonneg_left ?_ hh0.le
      exact one_div_le_one_div_of_le (by positivity) h1_sub
    _ = 8 := by field_simp [ne_of_gt hh0]

lemma row_kernel_sum_le (K : ℕ) {h : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1) (i : Fin K) :
    ∑ j : Fin K, h * c0 ((((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) * h) ≤ 16 := by
  let S_le := Finset.univ.filter (fun j : Fin K => (j : ℕ) ≤ (i : ℕ))
  let S_gt := Finset.univ.filter (fun j : Fin K => ¬ ((j : ℕ) ≤ (i : ℕ)))
  have hsplit : (∑ j : Fin K, h * c0 ((((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) * h)) =
      (∑ j ∈ S_le, h * c0 ((((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) * h)) +
      (∑ j ∈ S_gt, h * c0 ((((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) * h)) := by
    simpa [S_le, S_gt] using
      (Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin K => (j : ℕ) ≤ (i : ℕ))
        (fun j => h * c0 ((((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) * h))).symm
  have h_le : (∑ j ∈ S_le, h * c0 ((((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) * h)) ≤ 8 := by
    calc
      (∑ j ∈ S_le, h * c0 ((((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) * h))
          ≤ ∑ j ∈ S_le, h * Real.exp (-((((i : ℕ) - (j : ℕ) : ℕ) : ℝ)) * h / 4) := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hjle : (j : ℕ) ≤ (i : ℕ) := (Finset.mem_filter.mp hj).2
        have habs : |(((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) * h| =
            (((i : ℕ) - (j : ℕ) : ℕ) : ℝ) * h := by
          rw [Nat.cast_sub hjle, abs_of_nonneg]
          exact mul_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr hjle)) hh0.le
        have hc := c0_le_exp ((((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) * h)
        rw [habs] at hc
        have heq : -((((i : ℕ) - (j : ℕ) : ℕ) : ℝ) * h) / 4 =
            -((((i : ℕ) - (j : ℕ) : ℕ) : ℝ)) * h / 4 := by ring
        rw [heq] at hc
        exact mul_le_mul_of_nonneg_left hc hh0.le
      _ = ∑ t ∈ S_le.image (fun j : Fin K => (i : ℕ) - (j : ℕ)),
          h * Real.exp (-(t : ℝ) * h / 4) := by
        rw [Finset.sum_image]
        intro j₁ hj₁ j₂ hj₂ heq
        have h₁ : (j₁ : ℕ) ≤ (i : ℕ) := (Finset.mem_filter.mp (Finset.mem_coe.mp hj₁)).2
        have h₂ : (j₂ : ℕ) ≤ (i : ℕ) := (Finset.mem_filter.mp (Finset.mem_coe.mp hj₂)).2
        dsimp at heq
        exact Fin.ext (by omega)
      _ ≤ ∑ t ∈ Finset.range K, h * Real.exp (-(t : ℝ) * h / 4) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
        intro t ht
        rcases Finset.mem_image.mp ht with ⟨j, _, rfl⟩
        rw [Finset.mem_range]
        exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.isLt
      _ ≤ 8 := sum_h_exp_le_eight K hh0 hh1
  have h_gt : (∑ j ∈ S_gt, h * c0 ((((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) * h)) ≤ 8 := by
    calc
      (∑ j ∈ S_gt, h * c0 ((((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) * h))
          ≤ ∑ j ∈ S_gt, h * Real.exp (-((((j : ℕ) - (i : ℕ) : ℕ) : ℝ)) * h / 4) := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hjgt : (i : ℕ) < (j : ℕ) := not_le.mp (Finset.mem_filter.mp hj).2
        have habs : |(((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) * h| =
            (((j : ℕ) - (i : ℕ) : ℕ) : ℝ) * h := by
          rw [Nat.cast_sub hjgt.le, abs_mul, abs_of_pos hh0]
          have hsub_neg : ((i : ℕ) : ℝ) - ((j : ℕ) : ℝ) = -(((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) := by
            ring
          rw [hsub_neg, abs_neg, abs_of_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr hjgt.le))]
        have hc := c0_le_exp ((((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) * h)
        rw [habs] at hc
        have heq : -((((j : ℕ) - (i : ℕ) : ℕ) : ℝ) * h) / 4 =
            -((((j : ℕ) - (i : ℕ) : ℕ) : ℝ)) * h / 4 := by ring
        rw [heq] at hc
        exact mul_le_mul_of_nonneg_left hc hh0.le
      _ = ∑ t ∈ S_gt.image (fun j : Fin K => (j : ℕ) - (i : ℕ)),
          h * Real.exp (-(t : ℝ) * h / 4) := by
        rw [Finset.sum_image]
        intro j₁ hj₁ j₂ hj₂ heq
        have h₁ : (i : ℕ) < (j₁ : ℕ) := not_le.mp (Finset.mem_filter.mp (Finset.mem_coe.mp hj₁)).2
        have h₂ : (i : ℕ) < (j₂ : ℕ) := not_le.mp (Finset.mem_filter.mp (Finset.mem_coe.mp hj₂)).2
        dsimp at heq
        exact Fin.ext (by omega)
      _ ≤ ∑ t ∈ Finset.range K, h * Real.exp (-(t : ℝ) * h / 4) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
        intro t ht
        rcases Finset.mem_image.mp ht with ⟨j, _, rfl⟩
        rw [Finset.mem_range]
        exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) j.isLt
      _ ≤ 8 := sum_h_exp_le_eight K hh0 hh1
  linarith

end AuxLemma46

theorem solution (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2) (δ : ℝ) (hδ : 0 < δ) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ η : ℝ, 0 < η → 0 < Real.log (1 / η) →
      Real.log (1 / η) ≤ (1 / 2 - ε) * Real.log m →
      specNorm (blockCompression (sectionR m η) (sectionH m η) (sectionK m η) sqrtSeq -
          rescaledToeplitz (sectionK m η) (sectionH m η)) ≤ δ * η := by
  have _ := hε0
  have _ := hε1
  rcases claim_4_5 with ⟨c, hc_pos, hc45⟩
  let L₀ : ℝ := max 2 (48 * c / δ)
  refine ⟨⌈Real.exp L₀⌉₊ + 1, fun m hm η hη hlog_pos _ => ?_⟩
  have hm_pos : (0 : ℝ) < (m : ℝ) := by
    have hm1 : 1 ≤ m := by omega
    exact Nat.cast_pos.mpr (by omega)
  have hexp_le : Real.exp L₀ ≤ (m : ℝ) := by
    have h1 : (⌈Real.exp L₀⌉₊ : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : ⌈Real.exp L₀⌉₊ ≤ m)
    exact le_trans (Nat.le_ceil _) h1
  have hL_ge : L₀ ≤ Real.log (m : ℝ) := by
    rw [← Real.log_exp L₀]
    exact Real.log_le_log (Real.exp_pos _) hexp_le
  have hL_ge2 : 2 ≤ Real.log (m : ℝ) := le_trans (le_max_left _ _) hL_ge
  have hL_pos : 0 < Real.log (m : ℝ) := by linarith
  have hL_large : 48 * c / δ ≤ Real.log (m : ℝ) := le_trans (le_max_right _ _) hL_ge
  have hη_lt1 : η < 1 := by
    have h1 : 1 < 1 / η := (Real.log_pos_iff (by positivity)).mp hlog_pos
    have h2 := (lt_div_iff₀ hη).mp h1
    linarith
  let R := sectionR m η
  let h := sectionH m η
  let K := sectionK m η
  have hh0 : 0 < h := div_pos hη hL_pos
  have hh1 : h ≤ 1 := by
    dsimp [h, sectionH]
    rw [div_le_one hL_pos]
    linarith
  have hR_real_ge : Real.log (m : ℝ) ^ 4 / η ^ 2 ≤ (R : ℝ) := Nat.le_ceil _
  have hL4_ge16 : (16 : ℝ) ≤ Real.log (m : ℝ) ^ 4 := by
    calc
      (16 : ℝ) = 2 ^ 4 := by norm_num
      _ ≤ Real.log (m : ℝ) ^ 4 := pow_le_pow_left₀ (by norm_num) hL_ge2 4
  have hη2_lt1 : η ^ 2 < 1 := by nlinarith
  have hquot_gt1 : 1 < Real.log (m : ℝ) ^ 4 / η ^ 2 := by
    rw [one_lt_div (by positivity)]
    linarith
  have hR1 : 1 ≤ R := by
    have hR_gt1 : (1 : ℝ) < (R : ℝ) := lt_of_lt_of_le hquot_gt1 hR_real_ge
    by_contra hlt
    have hR0 : R = 0 := by omega
    rw [hR0] at hR_gt1
    norm_num at hR_gt1
  have hRh_ge : Real.log (m : ℝ) ^ 3 / η ≤ (R : ℝ) * h := by
    calc
      Real.log (m : ℝ) ^ 3 / η
          = (Real.log (m : ℝ) ^ 4 / η ^ 2) * (η / Real.log (m : ℝ)) := by
            field_simp [ne_of_gt hη, ne_of_gt hL_pos]
      _ ≤ (R : ℝ) * h := mul_le_mul_of_nonneg_right hR_real_ge hh0.le
  have hRh_gt1 : 1 < (R : ℝ) * h := by
    have hL3 : (8 : ℝ) ≤ Real.log (m : ℝ) ^ 3 := by
      calc
        (8 : ℝ) = 2 ^ 3 := by norm_num
        _ ≤ Real.log (m : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) hL_ge2 3
    have hgt : 1 < Real.log (m : ℝ) ^ 3 / η := by
      rw [one_lt_div hη]
      linarith
    exact lt_of_lt_of_le hgt hRh_ge
  have hparam_le : h + 1 / ((R : ℝ) * h) + 1 / (R : ℝ) ≤ 3 * η / Real.log (m : ℝ) := by
    have h1 : h = η / Real.log (m : ℝ) := rfl
    have h2 : 1 / ((R : ℝ) * h) ≤ η / Real.log (m : ℝ) := by
      calc
        1 / ((R : ℝ) * h) ≤ 1 / (Real.log (m : ℝ) ^ 3 / η) :=
          one_div_le_one_div_of_le (by positivity) hRh_ge
        _ = η / Real.log (m : ℝ) ^ 3 := by field_simp [ne_of_gt hη, ne_of_gt hL_pos]
        _ ≤ η / Real.log (m : ℝ) := by
          refine div_le_div_of_nonneg_left hη.le hL_pos ?_
          calc
            Real.log (m : ℝ) = Real.log (m : ℝ) ^ 1 := (pow_one _).symm
            _ ≤ Real.log (m : ℝ) ^ 3 := pow_le_pow_right₀ (by linarith) (by omega)
    have h3 : 1 / (R : ℝ) ≤ η / Real.log (m : ℝ) := by
      calc
        1 / (R : ℝ) ≤ 1 / (Real.log (m : ℝ) ^ 4 / η ^ 2) :=
          one_div_le_one_div_of_le (by positivity) hR_real_ge
        _ = η ^ 2 / Real.log (m : ℝ) ^ 4 := by field_simp [ne_of_gt hη, ne_of_gt hL_pos]
        _ ≤ η / Real.log (m : ℝ) := by
          rw [div_le_div_iff₀ (by positivity) hL_pos]
          have hη2 : η ^ 2 ≤ η := by nlinarith
          have hL4 : Real.log (m : ℝ) ≤ Real.log (m : ℝ) ^ 4 := by
            calc
              Real.log (m : ℝ) = Real.log (m : ℝ) ^ 1 := (pow_one _).symm
              _ ≤ Real.log (m : ℝ) ^ 4 := pow_le_pow_right₀ (by linarith) (by omega)
          exact mul_le_mul hη2 hL4 hL_pos.le hη.le
    have h3sum : η / Real.log (m : ℝ) + η / Real.log (m : ℝ) + η / Real.log (m : ℝ) =
        3 * η / Real.log (m : ℝ) := by ring
    linarith
  let E := blockCompression R h K sqrtSeq - rescaledToeplitz K h
  by_cases hK0 : K = 0
  · have hzero : E = 0 := Matrix.ext fun i => Fin.elim0 (hK0 ▸ i)
    change specNorm E ≤ δ * η
    rw [hzero]
    unfold specNorm
    simp [le_of_lt (mul_pos hδ hη)]
  · have hKne : Nonempty (Fin K) := ⟨⟨0, Nat.pos_of_ne_zero hK0⟩⟩
    have hentry : ∀ i j : Fin K,
        ‖E i j‖ ≤ (3 * c * η / Real.log (m : ℝ)) *
          (h * c0 ((((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) * h)) := by
      intro i j
      have h45 := hc45 R h K hR1 hh0 hh1 hRh_gt1 i j
      have hdef : E i j = blockCompression R h K sqrtSeq i j -
          ((h * c0 ((((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) * h) : ℝ) : ℂ) := by
        simp [E, rescaledToeplitz]
      rw [hdef]
      refine le_trans h45 ?_
      have hker_nn : 0 ≤ h * c0 ((((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) * h) :=
        mul_nonneg hh0.le (AuxLemma46.c0_nonneg _)
      refine mul_le_mul_of_nonneg_right ?_ hker_nn
      calc
        c * (h + 1 / ((R : ℝ) * h) + 1 / (R : ℝ))
            ≤ c * (3 * η / Real.log (m : ℝ)) :=
          mul_le_mul_of_nonneg_left hparam_le hc_pos.le
        _ = 3 * c * η / Real.log (m : ℝ) := by ring
    have hcoeff_le : (3 * c * η / Real.log (m : ℝ)) * 16 ≤ δ * η := by
      have h1 := (div_le_iff₀ hδ).mp hL_large
      rw [div_mul_eq_mul_div, div_le_iff₀ hL_pos]
      nlinarith
    have hrow : maxRowSum E ≤ δ * η := by
      unfold maxRowSum
      refine ciSup_le fun i => ?_
      calc
        ∑ j : Fin K, ‖E i j‖
            ≤ ∑ j : Fin K, (3 * c * η / Real.log (m : ℝ)) *
              (h * c0 ((((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) * h)) :=
          Finset.sum_le_sum fun j _ => hentry i j
        _ = (3 * c * η / Real.log (m : ℝ)) *
            ∑ j : Fin K, h * c0 ((((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) * h) := by
          rw [← Finset.mul_sum]
        _ ≤ (3 * c * η / Real.log (m : ℝ)) * 16 := by
          refine mul_le_mul_of_nonneg_left (AuxLemma46.row_kernel_sum_le K hh0 hh1 i) (by positivity)
        _ ≤ δ * η := hcoeff_le
    have hcol : maxColSum E ≤ δ * η := by
      unfold maxColSum
      refine ciSup_le fun j => ?_
      calc
        ∑ i : Fin K, ‖E i j‖
            ≤ ∑ i : Fin K, (3 * c * η / Real.log (m : ℝ)) *
              (h * c0 ((((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) * h)) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have hsym : c0 ((((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) * h) =
              c0 ((((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) * h) := by
            have hneg : (((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) * h =
                -((((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) * h) := by ring
            rw [hneg, AuxLemma46.c0_even]
          simpa [hsym] using hentry i j
        _ = (3 * c * η / Real.log (m : ℝ)) *
            ∑ i : Fin K, h * c0 ((((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) * h) := by
          rw [← Finset.mul_sum]
        _ ≤ (3 * c * η / Real.log (m : ℝ)) * 16 := by
          refine mul_le_mul_of_nonneg_left (AuxLemma46.row_kernel_sum_le K hh0 hh1 j) (by positivity)
        _ ≤ δ * η := hcoeff_le
    have h61 := claim_6_1 E
    have hcol_nn : 0 ≤ maxColSum E :=
      le_trans (Finset.sum_nonneg fun _ _ => norm_nonneg _)
        (le_ciSup (f := fun j : Fin K => ∑ i : Fin K, ‖E i j‖) (Finite.bddAbove_range _)
          (Classical.arbitrary (Fin K)))
    have hsq : specNorm E ^ 2 ≤ (δ * η) ^ 2 := by
      calc
        specNorm E ^ 2 ≤ maxColSum E * maxRowSum E := h61
        _ ≤ (δ * η) * (δ * η) := mul_le_mul hcol hrow (by
            exact le_trans (Finset.sum_nonneg fun _ _ => norm_nonneg _)
              (le_ciSup (f := fun i : Fin K => ∑ j : Fin K, ‖E i j‖) (Finite.bddAbove_range _)
                (Classical.arbitrary (Fin K))))
          (by positivity)
        _ = (δ * η) ^ 2 := (sq _).symm
    exact le_of_sq_le_sq hsq (by positivity)
