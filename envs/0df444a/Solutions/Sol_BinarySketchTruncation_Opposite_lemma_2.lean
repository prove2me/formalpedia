-- Prove2me | solution 1 for BinarySketchTruncation.Opposite.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:50:30.812548+00:00
-- url     : https://prove2.me/submissions/ec7e0368-4a64-458f-b18e-231c3e5e4361

import Mathlib
import Definitions.Def_BinarySketchTruncation_Opposite_ExplicitKernel

section
namespace BinarySketchTruncation.Dev.Lemma2

open BinarySketchTruncation.Opposite

lemma univ_bit : (Finset.univ : Finset Bit) = {0, 1} := by decide

lemma bit_cases (u : Bit) : u = 0 ∨ u = 1 := by revert u; decide

lemma sum_bit (f : Bit → ℝ) : ∑ s, f s = f 0 + f 1 := by
  rw [univ_bit, Finset.sum_pair (by decide)]

lemma bitLaw_zero (p : Bias) : (bitLaw p 0).toReal = 1 - (p : ℝ) := by
  have h := p.property
  unfold bitLaw
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_bool]
  simp
  have h2 := @PMF.bernoulli_apply ⟨p.val, h.1⟩ h.2 false
  rw [h2]
  have hq : (⟨p.val, h.1⟩ : NNReal) ≤ 1 := h.2
  show (((1 - ⟨p.val, h.1⟩ : NNReal) : NNReal) : ENNReal).toReal = _
  rw [ENNReal.coe_toReal]
  exact NNReal.coe_sub hq

lemma bitLaw_one (p : Bias) : (bitLaw p 1).toReal = (p : ℝ) := by
  have h := p.property
  unfold bitLaw
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_bool]
  simp
  have h2 := @PMF.bernoulli_apply ⟨p.val, h.1⟩ h.2 true
  rw [h2]
  exact ENNReal.coe_toReal (⟨p.val, h.1⟩ : NNReal)


/-! ### General facts about experiments on finite additive groups -/

lemma map_add_apply {S : Type} [Fintype S] [AddCommGroup S] [DecidableEq S]
    (P : PMF S) (c t : S) : (P.map (fun u => u + c)) t = P (t - c) := by
  rw [PMF.map_apply, tsum_fintype]
  have : ∀ a : S, (t = a + c) ↔ (a = t - c) := by
    intro a; constructor <;> intro h <;> [rw [h]; rw [h]] <;> abel
  simp_rw [this]
  simp

lemma shift_apply {S : Type} [Fintype S] [AddCommGroup S] [DecidableEq S]
    (P : Experiment S) (v : S) (h : Bool) (t : S) :
    (shiftUnderOne P v h t) = P h (t - if h then v else 0) :=
  map_add_apply _ _ _

/-- Bhattacharyya coefficient of an experiment. -/
noncomputable def BC {S : Type} [Fintype S] (P : Experiment S) : ℝ :=
  ∑ s, Real.sqrt ((P false s).toReal * (P true s).toReal)

lemma BC_mono {S T : Type} [Fintype S] [Fintype T] {P : Experiment S} {Q : Experiment T}
    {K : S → T → ℝ} (hK : Simulates P Q K) : BC P ≤ BC Q := by
  obtain ⟨⟨hK0, hK1⟩, hQ⟩ := hK
  have key : ∀ t, ∑ s, Real.sqrt ((P false s).toReal * (P true s).toReal) * K s t ≤
      Real.sqrt ((Q false t).toReal * (Q true t).toReal) := by
    intro t
    have hcs := Real.sum_sqrt_mul_sqrt_le (Finset.univ : Finset S)
      (f := fun s => (P false s).toReal * K s t) (g := fun s => (P true s).toReal * K s t)
      (fun s => mul_nonneg ENNReal.toReal_nonneg (hK0 s t))
      (fun s => mul_nonneg ENNReal.toReal_nonneg (hK0 s t))
    rw [hQ false t, hQ true t, ← Real.sqrt_mul
      (Finset.sum_nonneg (fun s _ => mul_nonneg ENNReal.toReal_nonneg (hK0 s t)))] at *
    refine le_trans (le_of_eq ?_) (hcs.trans_eq ?_)
    · refine Finset.sum_congr rfl (fun s _ => ?_)
      rw [← Real.sqrt_mul (mul_nonneg ENNReal.toReal_nonneg (hK0 s t))]
      have : (P false s).toReal * K s t * ((P true s).toReal * K s t)
          = ((P false s).toReal * (P true s).toReal) * K s t ^ 2 := by ring
      rw [this, Real.sqrt_mul (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg),
        Real.sqrt_sq (hK0 s t)]
    · rw [Real.sqrt_mul (Finset.sum_nonneg (fun s _ => mul_nonneg ENNReal.toReal_nonneg (hK0 s t)))]
  unfold BC
  calc ∑ s, Real.sqrt ((P false s).toReal * (P true s).toReal)
      = ∑ s, Real.sqrt ((P false s).toReal * (P true s).toReal) * ∑ t, K s t := by
        simp [hK1]
    _ = ∑ t, ∑ s, Real.sqrt ((P false s).toReal * (P true s).toReal) * K s t := by
        simp_rw [Finset.mul_sum]; exact Finset.sum_comm
    _ ≤ _ := Finset.sum_le_sum (fun t _ => key t)


/-! ### The single-bit kernel -/

lemma flip_vals (p₀ p₁ : Bias) (hne : p₀ ≠ p₁) :
    flipKernel p₀ p₁ 0 0 = (p₁ : ℝ) * (1 - 2 * (p₀ : ℝ)) / ((p₁ : ℝ) - (p₀ : ℝ)) ∧
    flipKernel p₀ p₁ 0 1 = 1 - (p₁ : ℝ) * (1 - 2 * (p₀ : ℝ)) / ((p₁ : ℝ) - (p₀ : ℝ)) ∧
    flipKernel p₀ p₁ 1 0 = (1 - (p₀ : ℝ)) * (2 * (p₁ : ℝ) - 1) / ((p₁ : ℝ) - (p₀ : ℝ)) ∧
    flipKernel p₀ p₁ 1 1 = 1 - (1 - (p₀ : ℝ)) * (2 * (p₁ : ℝ) - 1) / ((p₁ : ℝ) - (p₀ : ℝ)) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [flipKernel, hne]

lemma flip_ab_mem (p₀ p₁ : Bias) (hne : p₀ ≠ p₁) (hopp : OppositeSides p₀ p₁) :
    (0 ≤ (p₁ : ℝ) * (1 - 2 * (p₀ : ℝ)) / ((p₁ : ℝ) - (p₀ : ℝ)) ∧
      (p₁ : ℝ) * (1 - 2 * (p₀ : ℝ)) / ((p₁ : ℝ) - (p₀ : ℝ)) ≤ 1) ∧
    (0 ≤ (1 - (p₀ : ℝ)) * (2 * (p₁ : ℝ) - 1) / ((p₁ : ℝ) - (p₀ : ℝ)) ∧
      (1 - (p₀ : ℝ)) * (2 * (p₁ : ℝ) - 1) / ((p₁ : ℝ) - (p₀ : ℝ)) ≤ 1) := by
  obtain ⟨⟨x0, x1⟩, ⟨y0, y1⟩⟩ := And.intro p₀.property p₁.property
  have hne' : (p₀ : ℝ) ≠ p₁ := fun h => hne (Subtype.ext h)
  rcases lt_or_gt_of_ne hne' with hlt | hgt
  · have hD : 0 < (p₁ : ℝ) - p₀ := by linarith
    have hx : (p₀ : ℝ) ≤ 1 / 2 ∧ 1 / 2 ≤ (p₁ : ℝ) := by
      rcases hopp with h | h
      · exact h
      · exfalso; linarith [h.1, h.2]
    obtain ⟨hx1, hx2⟩ := hx
    refine ⟨⟨div_nonneg ?_ hD.le, (div_le_one hD).2 ?_⟩, ⟨div_nonneg ?_ hD.le,
      (div_le_one hD).2 ?_⟩⟩ <;> nlinarith
  · have hD : (p₁ : ℝ) - p₀ < 0 := by linarith
    have hx : (p₁ : ℝ) ≤ 1 / 2 ∧ 1 / 2 ≤ (p₀ : ℝ) := by
      rcases hopp with h | h
      · exfalso; linarith [h.1, h.2]
      · exact h
    obtain ⟨hx1, hx2⟩ := hx
    refine ⟨⟨div_nonneg_of_nonpos ?_ hD.le, (div_le_one_of_neg hD).2 ?_⟩,
      ⟨div_nonneg_of_nonpos ?_ hD.le, (div_le_one_of_neg hD).2 ?_⟩⟩ <;> nlinarith

lemma flip_simulates (p₀ p₁ : Bias) (hne : p₀ ≠ p₁) (hopp : OppositeSides p₀ p₁) :
    Simulates (bitExperiment p₀ p₁) (shiftUnderOne (bitExperiment p₀ p₁) (1 : Bit))
      (flipKernel p₀ p₁) := by
  obtain ⟨v00, v01, v10, v11⟩ := flip_vals p₀ p₁ hne
  obtain ⟨⟨a0, a1⟩, ⟨b0, b1⟩⟩ := flip_ab_mem p₀ p₁ hne hopp
  have hne' : (p₀ : ℝ) ≠ p₁ := fun h => hne (Subtype.ext h)
  have hD : (p₁ : ℝ) - p₀ ≠ 0 := sub_ne_zero.2 (Ne.symm hne')
  generalize ha : (p₁ : ℝ) * (1 - 2 * (p₀ : ℝ)) / ((p₁ : ℝ) - (p₀ : ℝ)) = a at *
  generalize hb : (1 - (p₀ : ℝ)) * (2 * (p₁ : ℝ) - 1) / ((p₁ : ℝ) - (p₀ : ℝ)) = b at *
  have ea : a * ((p₁ : ℝ) - p₀) = p₁ * (1 - 2 * p₀) := by rw [← ha]; field_simp
  have eb : b * ((p₁ : ℝ) - p₀) = (1 - p₀) * (2 * p₁ - 1) := by rw [← hb]; field_simp
  have q1 : (1 - (p₀ : ℝ)) * a + p₀ * b = 1 - p₀ := by
    apply mul_right_cancel₀ hD; linear_combination (1 - (p₀ : ℝ)) * ea + (p₀ : ℝ) * eb
  have q2 : (1 - (p₁ : ℝ)) * a + p₁ * b = p₁ := by
    apply mul_right_cancel₀ hD; linear_combination (1 - (p₁ : ℝ)) * ea + (p₁ : ℝ) * eb
  have e1 : (0 : Bit) - 1 = 1 := by decide
  have e2 : (1 : Bit) - 1 = 0 := by decide
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro u s
    rcases bit_cases u with rfl | rfl <;> rcases bit_cases s with rfl | rfl <;>
      simp [v00, v01, v10, v11] <;> linarith
  · intro u
    rw [sum_bit]
    rcases bit_cases u with rfl | rfl <;> simp [v00, v01, v10, v11]
  · intro h t
    rw [sum_bit, shift_apply]
    cases h <;> rcases bit_cases t with rfl | rfl <;>
      simp [bitExperiment, biasAt, bitLaw_zero, bitLaw_one, v00, v01, v10, v11, e1, e2] <;>
      linarith

lemma opp_iff_prod (p₀ p₁ : Bias) :
    OppositeSides p₀ p₁ ↔ (1 - 2 * (p₀ : ℝ)) * (1 - 2 * (p₁ : ℝ)) ≤ 0 := by
  unfold OppositeSides
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> nlinarith
  · intro h
    rcases mul_nonpos_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; constructor <;> linarith
    · right; constructor <;> linarith

/-- The squared Bhattacharyya identity for one bit. -/
lemma bc_sq_diff (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    (Real.sqrt ((1 - x) * (1 - y)) + Real.sqrt (x * y)) ^ 2 -
      (Real.sqrt ((1 - x) * y) + Real.sqrt (x * (1 - y))) ^ 2 = (1 - 2 * x) * (1 - 2 * y) := by
  have a1 : 0 ≤ 1 - x := by linarith
  have a2 : 0 ≤ 1 - y := by linarith
  have hAB : Real.sqrt ((1 - x) * (1 - y)) * Real.sqrt (x * y) =
      Real.sqrt ((1 - x) * y) * Real.sqrt (x * (1 - y)) := by
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
    congr 1; ring
  have hA := Real.sq_sqrt (show 0 ≤ (1 - x) * (1 - y) by positivity)
  have hB := Real.sq_sqrt (show 0 ≤ x * y by positivity)
  have hC := Real.sq_sqrt (show 0 ≤ (1 - x) * y by positivity)
  have hD := Real.sq_sqrt (show 0 ≤ x * (1 - y) by positivity)
  nlinarith

end BinarySketchTruncation.Dev.Lemma2

namespace BinarySketchTruncation.Opposite

open BinarySketchTruncation.Dev.Lemma2

theorem chk_lemma_2 (p₀ p₁ : Bias) (hne : p₀ ≠ p₁) :
    Dominates (bitExperiment p₀ p₁)
      (shiftUnderOne (bitExperiment p₀ p₁) (1 : Bit)) ↔ OppositeSides p₀ p₁ := by
  constructor
  · rintro ⟨K, hK⟩
    have hm := BC_mono hK
    unfold BC at hm
    rw [sum_bit, sum_bit] at hm
    have e1 : (0 : Bit) - 1 = 1 := by decide
    have e2 : (1 : Bit) - 1 = 0 := by decide
    simp only [shift_apply, bitExperiment, biasAt, bitLaw_zero, bitLaw_one, e1, e2, Bool.false_eq_true, ↓reduceIte, sub_zero] at hm
    obtain ⟨⟨x0, x1⟩, ⟨y0, y1⟩⟩ := And.intro p₀.property p₁.property
    have hsq := bc_sq_diff p₀ p₁ x0 x1 y0 y1
    rw [opp_iff_prod, ← hsq]
    have hpos : 0 ≤ Real.sqrt ((1 - (p₀:ℝ)) * (1 - p₁)) + Real.sqrt (p₀ * p₁) := by positivity
    linarith [pow_le_pow_left₀ hpos hm 2]
  · exact fun hopp => ⟨_, flip_simulates p₀ p₁ hne hopp⟩

end BinarySketchTruncation.Opposite
end

theorem solution : type_of% @BinarySketchTruncation.Opposite.chk_lemma_2 := @BinarySketchTruncation.Opposite.chk_lemma_2
