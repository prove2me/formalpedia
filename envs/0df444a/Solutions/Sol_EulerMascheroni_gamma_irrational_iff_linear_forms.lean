-- Prove2me | solution 1 for EulerMascheroni.gamma_irrational_iff_linear_forms
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-10T20:21:46.605015+00:00
-- url     : https://prove2.me/submissions/22d179a4-a80a-4728-a00f-015797bd74c2

import Mathlib

open Real Filter Topology

/-- Irrationality of Euler's constant is *equivalent* to the existence of integer linear
forms in it that never vanish and tend to zero. -/
theorem solution :
    Irrational Real.eulerMascheroniConstant ↔
      ∃ p q : ℕ → ℤ,
        (∀ n, (q n : ℝ) * Real.eulerMascheroniConstant - (p n : ℝ) ≠ 0) ∧
        Filter.Tendsto (fun n => (q n : ℝ) * Real.eulerMascheroniConstant - (p n : ℝ))
          Filter.atTop (nhds 0) := by
  constructor
  · -- (⇒) Dirichlet's approximation theorem supplies the forms.
    intro hirr
    choose k hk0 _hkle hkbd using fun n : ℕ =>
      Real.exists_nat_abs_mul_sub_round_le Real.eulerMascheroniConstant
        (n := n + 1) (Nat.succ_pos n)
    refine ⟨fun n => round ((k n : ℝ) * Real.eulerMascheroniConstant),
            fun n => (k n : ℤ), ?_, ?_⟩
    · intro n h
      apply hirr
      have hkpos : (0 : ℝ) < (k n : ℝ) := by exact_mod_cast hk0 n
      refine ⟨(round ((k n : ℝ) * Real.eulerMascheroniConstant) : ℚ) / (k n : ℚ), ?_⟩
      push_cast
      field_simp
      push_cast at h
      linarith
    · refine squeeze_zero_norm (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
      have := hkbd n
      push_cast at this ⊢
      calc ‖((k n : ℝ) * Real.eulerMascheroniConstant
              - (round ((k n : ℝ) * Real.eulerMascheroniConstant) : ℝ))‖
          = |(k n : ℝ) * Real.eulerMascheroniConstant
              - (round ((k n : ℝ) * Real.eulerMascheroniConstant) : ℝ)| := rfl
        _ ≤ 1 / ((n : ℝ) + 1 + 1) := this
        _ ≤ 1 / ((n : ℝ) + 1) := by
            apply one_div_le_one_div_of_le
            · positivity
            · linarith
  · -- (⇐) a vanishing sequence of non-zero forms forces irrationality.
    rintro ⟨p, q, hne, hlim⟩
    rintro ⟨r, hr⟩
    have hden : (0 : ℝ) < (r.den : ℝ) := by exact_mod_cast r.pos
    have hrr : Real.eulerMascheroniConstant = (r.num : ℝ) / (r.den : ℝ) := by
      rw [← hr]; exact_mod_cast (Rat.num_div_den r).symm
    have hLN : ∀ n, (q n : ℝ) * Real.eulerMascheroniConstant - (p n : ℝ)
        = ((q n * r.num - p n * (r.den : ℤ) : ℤ) : ℝ) / (r.den : ℝ) := by
      intro n; rw [hrr]; push_cast; field_simp
    have hkey : ∀ n, 1 / (r.den : ℝ)
        ≤ |(q n : ℝ) * Real.eulerMascheroniConstant - (p n : ℝ)| := by
      intro n
      have h0 : q n * r.num - p n * (r.den : ℤ) ≠ 0 := by
        intro h; exact hne n (by rw [hLN n, h]; simp)
      have h1 : (1 : ℝ) ≤ |((q n * r.num - p n * (r.den : ℤ) : ℤ) : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs h0
      rw [hLN n, abs_div, abs_of_pos hden]
      gcongr
    have habs : Filter.Tendsto
        (fun n => |(q n : ℝ) * Real.eulerMascheroniConstant - (p n : ℝ)|)
        Filter.atTop (nhds 0) := by simpa using hlim.abs
    obtain ⟨n, hn⟩ :=
      (habs.eventually (gt_mem_nhds (show (0:ℝ) < 1 / (r.den : ℝ) by positivity))).exists
    exact absurd hn (not_lt.mpr (hkey n))
