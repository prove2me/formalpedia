-- Prove2me | solution 1 for DetANN.mgg_cosine_inequality
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-14T21:29:55.610862+00:00
-- url     : https://prove2.me/submissions/5458c7f1-cc17-4596-b900-0221533457e3

import Mathlib
import Definitions.Def_DetANN_MGGOrder
import Theorems.Thm_DetANN_mgg_pointwise_weight_bound

open DetANN

namespace MGGCred

variable {m : ℕ}

lemma farther_asymm (z w : ZMod m × ZMod m) (h : mggFarther z w) : ¬ mggFarther w z := by
  unfold mggFarther at *
  rintro ⟨h1, h2, h3 | h3⟩ <;> omega

lemma weight_mul {α : ℝ} (hα : α ≠ 0) (z w : ZMod m × ZMod m) :
    mggWeight α z w * mggWeight α w z = 1 := by
  unfold mggWeight
  by_cases h1 : mggFarther z w
  · have h2 := farther_asymm z w h1
    simp [h1, h2, hα]
  · by_cases h2 : mggFarther w z
    · simp [h1, h2, hα]
    · simp [h1, h2]

lemma weight_pos (z w : ZMod m × ZMod m) : 0 < mggWeight (Real.sqrt 2) z w := by
  unfold mggWeight
  split_ifs <;> positivity

lemma amgm (g a b : ℝ) (hg : 0 < g) : 2 * a * b ≤ g * a ^ 2 + g⁻¹ * b ^ 2 := by
  have h : g * a ^ 2 + g⁻¹ * b ^ 2 - 2 * a * b = g⁻¹ * (g * a - b) ^ 2 := by
    field_simp
    ring
  nlinarith [mul_nonneg (inv_nonneg.2 hg.le) (sq_nonneg (g * a - b))]

/-- One edge: `2 G(z) G(w) c ≤ c (γ(z,w) G(z)² + γ(w,z) G(w)²)`. -/
lemma edge_bound (G : ZMod m × ZMod m → ℝ) (c : ℝ) (hc : 0 ≤ c) (z w : ZMod m × ZMod m) :
    2 * G z * (G w * c) ≤
      c * (mggWeight (Real.sqrt 2) z w * G z ^ 2 + mggWeight (Real.sqrt 2) w z * G w ^ 2) := by
  have hg := weight_pos z w
  have hinv : mggWeight (Real.sqrt 2) w z = (mggWeight (Real.sqrt 2) z w)⁻¹ :=
    eq_inv_of_mul_eq_one_right (weight_mul (by positivity) z w)
  rw [hinv]
  have := amgm _ (G z) (G w) hg
  nlinarith [mul_le_mul_of_nonneg_left this hc]

/-- The shear `T₂ : (x, y) ↦ (x, y + 2x)` as a bijection. -/
def T2e : (ZMod m × ZMod m) ≃ (ZMod m × ZMod m) where
  toFun w := (w.1, w.2 + 2 * w.1)
  invFun z := (z.1, z.2 - 2 * z.1)
  left_inv w := by simp
  right_inv z := by simp

/-- The shear `T₁ : (x, y) ↦ (x + 2y, y)` as a bijection. -/
def T1e : (ZMod m × ZMod m) ≃ (ZMod m × ZMod m) where
  toFun w := (w.1 + 2 * w.2, w.2)
  invFun z := (z.1 - 2 * z.2, z.2)
  left_inv w := by simp
  right_inv z := by simp

end MGGCred

open MGGCred in
theorem solution (m : ℕ) [NeZero m] (G : ZMod m × ZMod m → ℝ)
    (_hG : ∀ z, 0 ≤ G z) (hG0 : G 0 = 0) :
    ∑ z, 2 * G z * (G (z.1, z.2 - 2 * z.1) * |Real.cos (Real.pi * (z.1.valMinAbs : ℝ) / m)| +
        G (z.1 - 2 * z.2, z.2) * |Real.cos (Real.pi * (z.2.valMinAbs : ℝ) / m)|)
      ≤ 5 * Real.sqrt 2 / 2 * ∑ z, G z ^ 2 := by
  set γ := mggWeight (m := m) (Real.sqrt 2) with hγ
  set c1 : ZMod m × ZMod m → ℝ := fun z => |Real.cos (Real.pi * (z.1.valMinAbs : ℝ) / m)| with hc1
  set c2 : ZMod m × ZMod m → ℝ := fun z => |Real.cos (Real.pi * (z.2.valMinAbs : ℝ) / m)| with hc2
  -- Step 1: AM–GM on every edge
  have step1 : ∑ z, 2 * G z * (G (z.1, z.2 - 2 * z.1) * c1 z + G (z.1 - 2 * z.2, z.2) * c2 z) ≤
      ∑ z, ((c1 z * γ z (z.1, z.2 - 2 * z.1) * G z ^ 2 + c2 z * γ z (z.1 - 2 * z.2, z.2) * G z ^ 2) +
        c1 z * (γ (z.1, z.2 - 2 * z.1) z * G (z.1, z.2 - 2 * z.1) ^ 2) +
        c2 z * (γ (z.1 - 2 * z.2, z.2) z * G (z.1 - 2 * z.2, z.2) ^ 2)) := by
    refine Finset.sum_le_sum (fun z _ => ?_)
    have e1 := edge_bound G (c1 z) (abs_nonneg _) z (z.1, z.2 - 2 * z.1)
    have e2 := edge_bound G (c2 z) (abs_nonneg _) z (z.1 - 2 * z.2, z.2)
    rw [mul_add]
    linarith
  -- Step 2: reindex the returning halves through the shears
  have re2 : ∑ z, c1 z * (γ (z.1, z.2 - 2 * z.1) z * G (z.1, z.2 - 2 * z.1) ^ 2) =
      ∑ w, c1 w * (γ w (w.1, w.2 + 2 * w.1) * G w ^ 2) := by
    rw [← (T2e (m := m)).sum_comp]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    simp [T2e, hc1]
  have re1 : ∑ z, c2 z * (γ (z.1 - 2 * z.2, z.2) z * G (z.1 - 2 * z.2, z.2) ^ 2) =
      ∑ w, c2 w * (γ w (w.1 + 2 * w.2, w.2) * G w ^ 2) := by
    rw [← (T1e (m := m)).sum_comp]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    simp [T1e, hc2]
  -- Step 3: collect as ∑ G(z)² Q(z) and apply child D pointwise
  have collect : ∑ z, ((c1 z * γ z (z.1, z.2 - 2 * z.1) * G z ^ 2 +
        c2 z * γ z (z.1 - 2 * z.2, z.2) * G z ^ 2) +
        c1 z * (γ (z.1, z.2 - 2 * z.1) z * G (z.1, z.2 - 2 * z.1) ^ 2) +
        c2 z * (γ (z.1 - 2 * z.2, z.2) z * G (z.1 - 2 * z.2, z.2) ^ 2)) =
      ∑ z, G z ^ 2 * (c1 z * (γ z (z.1, z.2 + 2 * z.1) + γ z (z.1, z.2 - 2 * z.1)) +
        c2 z * (γ z (z.1 + 2 * z.2, z.2) + γ z (z.1 - 2 * z.2, z.2))) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, re2, re1, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    ring
  have pointwise : ∑ z, G z ^ 2 * (c1 z * (γ z (z.1, z.2 + 2 * z.1) + γ z (z.1, z.2 - 2 * z.1)) +
        c2 z * (γ z (z.1 + 2 * z.2, z.2) + γ z (z.1 - 2 * z.2, z.2))) ≤
      ∑ z, G z ^ 2 * (5 * Real.sqrt 2 / 2) := by
    refine Finset.sum_le_sum (fun z _ => ?_)
    by_cases hz : z = 0
    · subst hz; simp [hG0]
    · exact mul_le_mul_of_nonneg_left (mgg_pointwise_weight_bound m z hz) (sq_nonneg _)
  calc _ = ∑ z, 2 * G z * (G (z.1, z.2 - 2 * z.1) * c1 z + G (z.1 - 2 * z.2, z.2) * c2 z) := rfl
    _ ≤ _ := step1
    _ = _ := collect
    _ ≤ _ := pointwise
    _ = 5 * Real.sqrt 2 / 2 * ∑ z, G z ^ 2 := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun z _ => by ring)
