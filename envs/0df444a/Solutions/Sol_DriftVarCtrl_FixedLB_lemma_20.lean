-- Prove2me | solution 1 for DriftVarCtrl.FixedLB.lemma_20
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T14:30:56.989161+00:00
-- url     : https://prove2.me/submissions/5a3a7c2a-775c-4443-9eb7-fef0fc366ee2

import Mathlib
set_option autoImplicit false

theorem dvc20_mono (f f' : ℝ → ℝ) (hf : ∀ x, HasDerivAt f (f' x) x)
    (h : ∀ x, 0 ≤ x → 0 ≤ f' x) : MonotoneOn f (Set.Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
  · exact (continuous_iff_continuousAt.2 fun x => (hf x).continuousAt).continuousOn
  · exact fun x _ => (hf x).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    rw [(hf x).deriv]
    exact h x (le_of_lt hx)

theorem dvc20_a (x : ℝ) : Real.exp x ≤ x * Real.exp x + 1 := by
  have h1 := Real.add_one_le_exp (-x)
  have h2 : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  have h3 := Real.exp_pos x
  nlinarith [mul_le_mul_of_nonneg_left h1 h3.le]

theorem dvc20_c (x : ℝ) (hx : 0 ≤ x) : 2 * Real.exp x ≤ x ^ 2 * Real.exp x + 2 * x + 2 := by
  -- g' (x) = (x^2+2x-2) e^x + 2 is nonneg on [0,∞)
  have hg' : ∀ y : ℝ, 0 ≤ y → 0 ≤ (y ^ 2 + 2 * y - 2) * Real.exp y + 2 := by
    have hd : ∀ y : ℝ, HasDerivAt (fun y => (y ^ 2 + 2 * y - 2) * Real.exp y + 2)
        ((y ^ 2 + 4 * y) * Real.exp y) y := by
      intro y
      have h1 : HasDerivAt (fun y : ℝ => y ^ 2 + 2 * y - 2) (2 * y + 2) y := by
        have := ((hasDerivAt_pow 2 y).add ((hasDerivAt_id y).const_mul 2)).sub_const 2
        exact this.congr_deriv (by norm_num <;> ring)
      have := (h1.mul (Real.hasDerivAt_exp y)).add_const 2
      exact this.congr_deriv (by ring)
    intro y hy
    have hm := dvc20_mono _ _ hd (fun z hz => by positivity) (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hy) hy
    norm_num at hm
    linarith
  have hd : ∀ y : ℝ, HasDerivAt (fun y => y ^ 2 * Real.exp y + 2 * y + 2 - 2 * Real.exp y)
      ((y ^ 2 + 2 * y - 2) * Real.exp y + 2) y := by
    intro y
    have h1 := (((hasDerivAt_pow 2 y).mul (Real.hasDerivAt_exp y)).add
      ((hasDerivAt_id y).const_mul 2)).add_const 2 |>.sub ((Real.hasDerivAt_exp y).const_mul 2)
    exact h1.congr_deriv (by norm_num <;> ring)
  have hm := dvc20_mono _ _ hd hg' (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hx) hx
  norm_num at hm
  linarith

theorem dvc20_b (x : ℝ) (hx : 0 ≤ x) : 2 * Real.exp x ≤ x * Real.exp x + x + 2 := by
  have hd : ∀ y : ℝ, HasDerivAt (fun y => y * Real.exp y + y + 2 - 2 * Real.exp y)
      ((y - 1) * Real.exp y + 1) y := by
    intro y
    have h1 := (((hasDerivAt_id y).mul (Real.hasDerivAt_exp y)).add
      (hasDerivAt_id y)).add_const 2 |>.sub ((Real.hasDerivAt_exp y).const_mul 2)
    exact h1.congr_deriv (by norm_num <;> ring)
  have hm := dvc20_mono _ _ hd (fun z _ => by have := dvc20_a z; linarith) (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hx) hx
  norm_num at hm
  linarith

theorem solution (x : ℝ) (hx : 0 ≤ x) :
    Real.exp x ≤ x * Real.exp x + 1 ∧
    2 * Real.exp x ≤ x * Real.exp x + x + 2 ∧
    2 * Real.exp x ≤ x ^ 2 * Real.exp x + 2 * x + 2 :=
  ⟨dvc20_a x, dvc20_b x hx, dvc20_c x hx⟩
