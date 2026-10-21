-- Prove2me | solution 1 for DriftVarCtrl.FixedLB.lemma_21
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T14:30:30.041724+00:00
-- url     : https://prove2.me/submissions/3afd9dd2-2079-4f6d-b666-8188a6c730f0

import Mathlib
set_option autoImplicit false

theorem solution (k : ℝ) (hk : 0 < k) :
    (∀ x : ℝ, 0 < x → 1 / k < x / (1 - Real.exp (-k * x))) ∧
    (∀ x : ℝ, x < 0 → 0 < x / (1 - Real.exp (-k * x)) ∧ x / (1 - Real.exp (-k * x)) < 1 / k) ∧
    (∀ x : ℝ, 0 < x → 0 < x * Real.exp (-k * x) / (1 - Real.exp (-k * x)) ∧
      x * Real.exp (-k * x) / (1 - Real.exp (-k * x)) < 1 / k) ∧
    (∀ x : ℝ, x < 0 → 1 / k < x * Real.exp (-k * x) / (1 - Real.exp (-k * x))) := by
  -- key facts for any x ≠ 0
  have key : ∀ x : ℝ, x ≠ 0 → 1 - k * x < Real.exp (-k * x) ∧
      Real.exp (-k * x) * (k * x + 1) < 1 := by
    intro x hx
    have hkx : k * x ≠ 0 := mul_ne_zero hk.ne' hx
    have h1 := Real.add_one_lt_exp (show -k * x ≠ 0 by simpa using hkx)
    have h2 := Real.add_one_lt_exp hkx
    have he : Real.exp (-k * x) * Real.exp (k * x) = 1 := by
      rw [← Real.exp_add]; simp
    have hpos := Real.exp_pos (-k * x)
    refine ⟨by linarith, ?_⟩
    calc Real.exp (-k * x) * (k * x + 1) < Real.exp (-k * x) * Real.exp (k * x) :=
          mul_lt_mul_of_pos_left h2 hpos
      _ = 1 := he
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨h1, _⟩ := key x hx.ne'
    have he : Real.exp (-k * x) < 1 := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by nlinarith)
    rw [div_lt_div_iff₀ hk (by linarith)]
    nlinarith
  · intro x hx
    obtain ⟨h1, _⟩ := key x hx.ne
    have he : 1 < Real.exp (-k * x) := Real.one_lt_exp_iff.mpr (by nlinarith)
    have hd : 1 - Real.exp (-k * x) < 0 := by linarith
    refine ⟨div_pos_of_neg_of_neg hx hd, ?_⟩
    rw [div_lt_iff_of_neg hd, div_mul_eq_mul_div, div_lt_iff₀ hk]
    nlinarith
  · intro x hx
    obtain ⟨_, h2⟩ := key x hx.ne'
    have he : Real.exp (-k * x) < 1 := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by nlinarith)
    have hep := Real.exp_pos (-k * x)
    have hd : 0 < 1 - Real.exp (-k * x) := by linarith
    refine ⟨div_pos (mul_pos hx hep) hd, ?_⟩
    rw [div_lt_div_iff₀ hd hk]
    nlinarith
  · intro x hx
    obtain ⟨_, h2⟩ := key x hx.ne
    have he : 1 < Real.exp (-k * x) := Real.one_lt_exp_iff.mpr (by nlinarith)
    have hd : 1 - Real.exp (-k * x) < 0 := by linarith
    rw [lt_div_iff_of_neg hd, one_div, inv_mul_eq_div, lt_div_iff₀ hk]
    nlinarith
