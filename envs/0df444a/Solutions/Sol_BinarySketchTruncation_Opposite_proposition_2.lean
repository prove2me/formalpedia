-- Prove2me | solution 1 for BinarySketchTruncation.Opposite.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:50:30.61453+00:00
-- url     : https://prove2.me/submissions/8ba96ca0-9006-4bd3-ab16-bc5207d27d00

import Mathlib
import Definitions.Def_BinarySketchTruncation_Opposite_ExplicitKernel
import Definitions.Def_BinarySketchTruncation_Opposite_Model

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

lemma independentSum_pure {S : Type} [AddCommGroup S] (P : Experiment S) (v : S) :
    independentSum P (fun h => PMF.pure (if h then v else 0)) = shiftUnderOne P v := by
  funext h
  simp only [independentSum, shiftUnderOne, PMF.pure_map]
  rfl

lemma independentSum_toReal {S : Type} [Fintype S] [AddCommGroup S] [DecidableEq S]
    (P Q : Experiment S) (h : Bool) (t : S) :
    (independentSum P Q h t).toReal =
      ∑ u, (P h u).toReal * ∑ v, if t = u + v then (Q h v).toReal else 0 := by
  unfold independentSum
  rw [PMF.bind_apply, tsum_fintype, ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [ENNReal.toReal_mul]
    congr 1
    rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum]
    · refine Finset.sum_congr rfl (fun v _ => ?_)
      split_ifs <;> simp
    · intro v _
      split_ifs
      · exact PMF.apply_ne_top _ _
      · simp
  · intro u _
    refine ENNReal.mul_ne_top (PMF.apply_ne_top _ _) ?_
    rw [PMF.map_apply, tsum_fintype]
    refine ENNReal.sum_ne_top.2 (fun v _ => ?_)
    split_ifs
    · exact PMF.apply_ne_top _ _
    · simp

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

end BinarySketchTruncation.Opposite
end

section
namespace BinarySketchTruncation.Dev.Lemma1

open BinarySketchTruncation.Opposite BinarySketchTruncation.Dev.Lemma2

section general

variable {G : Type} [Fintype G] [AddCommGroup G] [DecidableEq G]

lemma pmf_toReal_sum_one (P : PMF G) : ∑ v, (P v).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun v _ => PMF.apply_ne_top _ _)]
  have := P.tsum_coe
  rw [tsum_fintype] at this
  rw [this]; simp

lemma indep_formula (h2 : ∀ x : G, x + x = 0) (P Q : Experiment G) (h : Bool) (t : G) :
    (independentSum P Q h t).toReal = ∑ v, (Q h v).toReal * (P h (t + v)).toReal := by
  rw [independentSum_toReal]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [Finset.sum_eq_single (t + v)]
  · have : t = t + v + v := by rw [add_assoc, h2, add_zero]
    simp only [← this, if_true]; ring
  · intro u _ hu
    have : ¬ t = u + v := by
      intro h'; apply hu; rw [h', add_assoc, h2, add_zero]
    simp [this]
  · simp

/-- Averaging the deterministic-shift kernels over independent `v₀ ~ ν₀`, `v₁ ~ ν₁`. -/
noncomputable def avgKernel (Kf : G → G → G → ℝ) (ν : Experiment G) (u s : G) : ℝ :=
  ∑ v₀, ∑ v₁, (ν false v₀).toReal * (ν true v₁).toReal * Kf (v₀ + v₁) u (s + v₀)

lemma avgKernel_simulates (h2 : ∀ x : G, x + x = 0) (U : Experiment G) (Kf : G → G → G → ℝ)
    (hKf : ∀ w, Simulates U (shiftUnderOne U w) (Kf w)) (ν : Experiment G) :
    Simulates U (independentSum U ν) (avgKernel Kf ν) := by
  have hneg : ∀ x y : G, x - y = x + y := by
    intro x y
    have : -y = y := neg_eq_of_add_eq_zero_right (h2 y)
    rw [sub_eq_add_neg, this]
  have n0 := pmf_toReal_sum_one (ν false)
  have n1 := pmf_toReal_sum_one (ν true)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro u s
    refine Finset.sum_nonneg (fun v₀ _ => Finset.sum_nonneg (fun v₁ _ => ?_))
    exact mul_nonneg (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
      ((hKf _).1.1 _ _)
  · intro u
    unfold avgKernel
    rw [Finset.sum_comm]
    have : ∀ v₀ : G, ∑ s, ∑ v₁, (ν false v₀).toReal * (ν true v₁).toReal *
        Kf (v₀ + v₁) u (s + v₀) = ∑ v₁, (ν false v₀).toReal * (ν true v₁).toReal := by
      intro v₀
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun v₁ _ => ?_)
      rw [← Finset.mul_sum]
      have e : ∑ s, Kf (v₀ + v₁) u (s + v₀) = 1 := by
        have e := Equiv.sum_comp (Equiv.addRight v₀) (fun s => Kf (v₀ + v₁) u s)
        simp only [Equiv.coe_addRight] at e
        rw [e]
        exact (hKf _).1.2 u
      rw [e, mul_one]
    simp_rw [this]
    rw [← Finset.sum_mul_sum, n0, n1, mul_one]
  · intro h t
    rw [indep_formula h2]
    have step : ∑ u, (U h u).toReal * avgKernel Kf ν u t =
        ∑ v₀, ∑ v₁, (ν false v₀).toReal * (ν true v₁).toReal *
          (U h (t + v₀ - if h then v₀ + v₁ else 0)).toReal := by
      unfold avgKernel
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun v₀ _ => ?_)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun v₁ _ => ?_)
      have := (hKf (v₀ + v₁)).2 h (t + v₀)
      rw [shift_apply] at this
      rw [this, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun x _ => by ring)
    rw [step]
    cases h
    · simp only [Bool.false_eq_true, ↓reduceIte, sub_zero]
      refine Finset.sum_congr rfl (fun v₀ _ => ?_)
      have : ∑ v₁, (ν false v₀).toReal * (ν true v₁).toReal * (U false (t + v₀)).toReal =
          (ν false v₀).toReal * (U false (t + v₀)).toReal * ∑ v₁, (ν true v₁).toReal := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring)
      rw [this, n1, mul_one]
    · simp only [↓reduceIte]
      have key : ∀ v₀ v₁ : G, t + v₀ - (v₀ + v₁) = t + v₁ := by
        intro v₀ v₁
        rw [hneg]
        calc t + v₀ + (v₀ + v₁) = t + (v₀ + v₀) + v₁ := by abel
          _ = t + v₁ := by rw [h2, add_zero]
      simp_rw [key]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun v₁ _ => ?_)
      have : ∑ v₀, (ν false v₀).toReal * (ν true v₁).toReal * (U true (t + v₁)).toReal =
          (ν true v₁).toReal * (U true (t + v₁)).toReal * ∑ v₀, (ν false v₀).toReal := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring)
      rw [this, n0, mul_one]

end general

lemma vec_add_self (k : ℕ) (x : Vec k) : x + x = 0 := by
  funext i
  have : ∀ a : Bit, a + a = 0 := by decide
  exact this (x i)

end BinarySketchTruncation.Dev.Lemma1

namespace BinarySketchTruncation.Opposite

open BinarySketchTruncation.Dev.Lemma1

end BinarySketchTruncation.Opposite
end

section
namespace BinarySketchTruncation.Dev.Prop2

open BinarySketchTruncation.Opposite BinarySketchTruncation.Dev.Lemma2
  BinarySketchTruncation.Dev.Lemma1

lemma cube_toReal (k : ℕ) (p₀ p₁ : Bias) (h : Bool) (x : Vec k) :
    (cubeExperiment k p₀ p₁ h x).toReal = ∏ i, (bitExperiment p₀ p₁ h (x i)).toReal := by
  unfold cubeExperiment cubeLaw bitExperiment
  rw [PMF.ofFintype_apply, ENNReal.toReal_prod]

lemma cube_shift_toReal (k : ℕ) (p₀ p₁ : Bias) (w : Vec k) (h : Bool) (t : Vec k) :
    (shiftUnderOne (cubeExperiment k p₀ p₁) w h t).toReal =
      ∏ i, (shiftUnderOne (bitExperiment p₀ p₁) (w i) h (t i)).toReal := by
  rw [shift_apply, cube_toReal]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [shift_apply]
  cases h <;> simp

lemma coord_simulates (p₀ p₁ : Bias) (hne : p₀ ≠ p₁) (hopp : OppositeSides p₀ p₁) (d : Bit) :
    Simulates (bitExperiment p₀ p₁) (shiftUnderOne (bitExperiment p₀ p₁) d)
      (coordinateKernel p₀ p₁ d) := by
  rcases bit_cases d with rfl | rfl
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro u s; simp only [coordinateKernel]; split_ifs <;> norm_num
    · intro u; simp [coordinateKernel]
    · intro h t
      rw [shift_apply]
      simp [coordinateKernel]
  · have := flip_simulates p₀ p₁ hne hopp
    have e : coordinateKernel p₀ p₁ 1 = flipKernel p₀ p₁ := by
      funext u s; simp [coordinateKernel]
    rw [e]; exact this

lemma prod_sum_ident {k : ℕ} (a : Fin k → Bit → ℝ) (K : Fin k → Bit → Bit → ℝ) (t : Vec k) :
    ∑ s : Vec k, (∏ i, a i (s i)) * ∏ i, K i (s i) (t i) = ∏ i, ∑ b, a i b * K i b (t i) := by
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [← Finset.prod_mul_distrib]

lemma cube_simulates (k : ℕ) (p₀ p₁ : Bias) (hne : p₀ ≠ p₁) (hopp : OppositeSides p₀ p₁)
    (w : Vec k) :
    Simulates (cubeExperiment k p₀ p₁) (shiftUnderOne (cubeExperiment k p₀ p₁) w)
      (fun u s => ∏ i, coordinateKernel p₀ p₁ (w i) (u i) (s i)) := by
  have hc := fun i => coord_simulates p₀ p₁ hne hopp (w i)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro u s
    exact Finset.prod_nonneg (fun i _ => (hc i).1.1 _ _)
  · intro u
    have := prod_sum_ident (k := k) (fun _ _ => 1) (fun i b t => coordinateKernel p₀ p₁ (w i) b t)
    rw [← Fintype.prod_sum]
    simp_rw [(hc _).1.2]
    simp
  · intro h t
    rw [cube_shift_toReal]
    simp_rw [cube_toReal]
    rw [prod_sum_ident (fun i b => (bitExperiment p₀ p₁ h b).toReal)
      (fun i b t => coordinateKernel p₀ p₁ (w i) b t) t]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    exact (hc i).2 h (t i)


lemma identity_simulates {S : Type} [Fintype S] [DecidableEq S] (P Q : Experiment S)
    (h : ∀ h t, (Q h t).toReal = (P h t).toReal) :
    Simulates P Q (fun u s => if s = u then 1 else 0) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro u s; dsimp only; split_ifs <;> norm_num
  · intro u; simp
  · intro hh t
    simp [h hh t]

lemma simulates_zero (p₀ p₁ : Bias) (ν : Experiment (Vec 0)) :
    Simulates (cubeExperiment 0 p₀ p₁) (independentSum (cubeExperiment 0 p₀ p₁) ν)
      (fun u s => if s = u then 1 else 0) := by
  refine identity_simulates _ _ (fun h t => ?_)
  have key : ∀ P : PMF (Vec 0), (P t).toReal = 1 := by
    intro P
    have := pmf_toReal_sum_one P
    rwa [Finset.sum_eq_single t (fun b _ hb => absurd (Subsingleton.elim b t) hb)
      (fun h => absurd (Finset.mem_univ t) h)] at this
  rw [key, key]

lemma opp_eq_half (p₀ p₁ : Bias) (hopp : OppositeSides p₀ p₁) (he : p₀ = p₁) :
    (p₀ : ℝ) = 1 / 2 := by
  subst he
  rcases hopp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith

lemma simulates_half (k : ℕ) (p₀ p₁ : Bias) (hopp : OppositeSides p₀ p₁) (he : p₀ = p₁)
    (ν : Experiment (Vec k)) :
    Simulates (cubeExperiment k p₀ p₁) (independentSum (cubeExperiment k p₀ p₁) ν)
      (fun u s => if s = u then 1 else 0) := by
  have hp := opp_eq_half p₀ p₁ hopp he
  have hp' : (p₁ : ℝ) = 1 / 2 := by rw [← he]; exact hp
  have hc : ∀ h x, (cubeExperiment k p₀ p₁ h x).toReal = (1 / 2 : ℝ) ^ k := by
    intro h x
    rw [cube_toReal]
    have : ∀ b : Bit, (bitExperiment p₀ p₁ h b).toReal = 1 / 2 := by
      intro b
      rcases bit_cases b with rfl | rfl <;> cases h <;>
        simp [bitExperiment, biasAt, bitLaw_zero, bitLaw_one, hp, hp'] <;> norm_num
    simp [this]
  refine identity_simulates _ _ (fun h t => ?_)
  rw [indep_formula (vec_add_self k)]
  simp_rw [hc]
  rw [← Finset.sum_mul, pmf_toReal_sum_one, one_mul]

lemma explicit_eq_avg (k : ℕ) (p₀ p₁ : Bias) (hk : k ≠ 0) (hne : p₀ ≠ p₁)
    (ν : Experiment (Vec k)) :
    explicitKernel k p₀ p₁ ν =
      avgKernel (fun w u s => ∏ i, coordinateKernel p₀ p₁ (w i) (u i) (s i)) ν := by
  funext u s
  simp [explicitKernel, avgKernel, hk, hne]

theorem second_conjunct (k : ℕ) (p₀ p₁ : Bias) (h : k = 0 ∨ OppositeSides p₀ p₁)
    (ν : Experiment (Vec k)) :
    Simulates (cubeExperiment k p₀ p₁) (independentSum (cubeExperiment k p₀ p₁) ν)
      (explicitKernel k p₀ p₁ ν) := by
  by_cases hk : k = 0
  · subst hk
    have : explicitKernel 0 p₀ p₁ ν = fun u s => if s = u then 1 else 0 := by
      funext u s; simp [explicitKernel]
    rw [this]; exact simulates_zero p₀ p₁ ν
  · have hopp : OppositeSides p₀ p₁ := h.resolve_left hk
    by_cases he : p₀ = p₁
    · have : explicitKernel k p₀ p₁ ν = fun u s => if s = u then 1 else 0 := by
        funext u s; simp [explicitKernel, hk, he]
      rw [this]; exact simulates_half k p₀ p₁ hopp he ν
    · rw [explicit_eq_avg k p₀ p₁ hk he]
      exact avgKernel_simulates (vec_add_self k) _ _
        (fun w => cube_simulates k p₀ p₁ he hopp w) ν


lemma sum_sqrt_prod (k : ℕ) (a b : Bit → ℝ) (ha : ∀ x, 0 ≤ a x) (hb : ∀ x, 0 ≤ b x) :
    ∑ t : Vec k, Real.sqrt ((∏ i, a (t i)) * ∏ i, b (t i)) =
      (Real.sqrt (a 0 * b 0) + Real.sqrt (a 1 * b 1)) ^ k := by
  have h1 : ∀ t : Vec k, Real.sqrt ((∏ i, a (t i)) * ∏ i, b (t i)) =
      ∏ i, Real.sqrt (a (t i) * b (t i)) := by
    intro t
    rw [← Finset.prod_mul_distrib, Real.sqrt_prod _ (fun i _ => mul_nonneg (ha _) (hb _))]
  simp_rw [h1]
  have := Fintype.prod_sum (κ := fun _ : Fin k => Bit) (fun _ x => Real.sqrt (a x * b x))
  rw [← this]
  simp [sum_bit]

lemma BC_cube (k : ℕ) (p₀ p₁ : Bias) :
    BC (cubeExperiment k p₀ p₁) =
      (Real.sqrt ((1 - (p₀ : ℝ)) * (1 - (p₁ : ℝ))) + Real.sqrt ((p₀ : ℝ) * (p₁ : ℝ))) ^ k := by
  unfold BC
  simp_rw [cube_toReal]
  rw [sum_sqrt_prod k (fun x => (bitExperiment p₀ p₁ false x).toReal)
    (fun x => (bitExperiment p₀ p₁ true x).toReal) (fun _ => ENNReal.toReal_nonneg)
    (fun _ => ENNReal.toReal_nonneg)]
  simp [bitExperiment, biasAt, bitLaw_zero, bitLaw_one]

lemma BC_cube_shift (k : ℕ) (p₀ p₁ : Bias) :
    BC (shiftUnderOne (cubeExperiment k p₀ p₁) (fun _ => (1 : Bit))) =
      (Real.sqrt ((1 - (p₀ : ℝ)) * (p₁ : ℝ)) + Real.sqrt ((p₀ : ℝ) * (1 - (p₁ : ℝ)))) ^ k := by
  unfold BC
  simp_rw [shift_apply, cube_toReal]
  have e : ∀ t : Vec k, (t - fun _ => (1 : Bit)) = fun i => t i - 1 := fun t => rfl
  simp only [e, Bool.false_eq_true, ↓reduceIte, sub_zero, if_true]
  have e1 : (0 : Bit) - 1 = 1 := by decide
  have e2 : (1 : Bit) - 1 = 0 := by decide
  rw [sum_sqrt_prod k (fun x => (bitExperiment p₀ p₁ false x).toReal)
    (fun x => (bitExperiment p₀ p₁ true (x - 1)).toReal) (fun _ => ENNReal.toReal_nonneg)
    (fun _ => ENNReal.toReal_nonneg)]
  simp [bitExperiment, biasAt, bitLaw_zero, bitLaw_one, e1, e2]

theorem first_reverse (k : ℕ) (p₀ p₁ : Bias)
    (H : ∀ ν : Experiment (Vec k), Dominates (cubeExperiment k p₀ p₁)
        (independentSum (cubeExperiment k p₀ p₁) ν)) : k = 0 ∨ OppositeSides p₀ p₁ := by
  by_cases hk : k = 0
  · exact Or.inl hk
  right
  by_contra hopp
  obtain ⟨K, hK⟩ := H (fun h => PMF.pure (if h then (fun _ => (1 : Bit)) else 0))
  have hm := BC_mono hK
  have e : independentSum (cubeExperiment k p₀ p₁)
      (fun h => PMF.pure (if h then (fun _ => (1 : Bit)) else 0)) =
      shiftUnderOne (cubeExperiment k p₀ p₁) (fun _ => (1 : Bit)) :=
    independentSum_pure _ _
  rw [e, BC_cube, BC_cube_shift] at hm
  rw [opp_iff_prod] at hopp
  push_neg at hopp
  obtain ⟨⟨x0, x1⟩, ⟨y0, y1⟩⟩ := And.intro p₀.property p₁.property
  have hsq := bc_sq_diff p₀ p₁ x0 x1 y0 y1
  have hpos : 0 ≤ Real.sqrt ((1 - (p₀:ℝ)) * p₁) + Real.sqrt (p₀ * (1 - (p₁:ℝ))) := by positivity
  have hlt : Real.sqrt ((1 - (p₀:ℝ)) * p₁) + Real.sqrt (p₀ * (1 - (p₁:ℝ))) <
      Real.sqrt ((1 - (p₀:ℝ)) * (1 - p₁)) + Real.sqrt (p₀ * p₁) := by
    apply lt_of_pow_lt_pow_left₀ 2 (by positivity)
    linarith
  exact absurd hm (not_le.2 (pow_lt_pow_left₀ hlt hpos hk))

end BinarySketchTruncation.Dev.Prop2

namespace BinarySketchTruncation.Opposite

open BinarySketchTruncation.Dev.Prop2

theorem chk_proposition_2 (k : ℕ) (p₀ p₁ : Bias) :
    ((∀ ν : Experiment (Vec k), Dominates (cubeExperiment k p₀ p₁)
        (independentSum (cubeExperiment k p₀ p₁) ν)) ↔
      k = 0 ∨ OppositeSides p₀ p₁) ∧
    ((k = 0 ∨ OppositeSides p₀ p₁) → ∀ ν : Experiment (Vec k),
      Simulates (cubeExperiment k p₀ p₁)
        (independentSum (cubeExperiment k p₀ p₁) ν)
        (explicitKernel k p₀ p₁ ν)) := by
  refine ⟨⟨first_reverse k p₀ p₁, fun h ν => ⟨_, second_conjunct k p₀ p₁ h ν⟩⟩,
    fun h ν => second_conjunct k p₀ p₁ h ν⟩

end BinarySketchTruncation.Opposite
end

theorem solution : type_of% @BinarySketchTruncation.Opposite.chk_proposition_2 := @BinarySketchTruncation.Opposite.chk_proposition_2
