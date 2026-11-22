-- Prove2me | solution 1 for GRH.riemannZeta_zero_nontrivial_in_critical_strip
-- status  : ACCEPTED   (prove)
-- author  : @LG
-- created : 2026-11-21T16:22:22.632699+00:00
-- url     : https://prove2.me/submissions/e3c9f5e2-c9ce-4ee0-b25b-05b655421324

import Mathlib

open Complex

theorem solution {s : ℂ} (hz : riemannZeta s = 0)
    (htriv : ¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) :
    0 < s.re ∧ s.re < 1 := by
  have hs0 : s ≠ 0 := fun e => by
    rw [e, riemannZeta_zero] at hz
    norm_num at hz
  rcases lt_or_ge 0 s.re with hpos | hnpos
  · rcases lt_or_ge s.re 1 with hlt1 | hge1
    · exact ⟨hpos, hlt1⟩
    · exact absurd hz (riemannZeta_ne_zero_of_one_le_re hge1)
  · exfalso
    have hG : Gammaℝ s ≠ 0 := by
      intro hg
      obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp hg
      rcases n with _ | n
      · exact hs0 (by simpa using hn)
      · exact htriv ⟨n, by rw [hn]; push_cast; ring⟩
    have hc : completedRiemannZeta s = 0 := by
      rw [riemannZeta_def_of_ne_zero hs0, div_eq_zero_iff] at hz
      exact hz.resolve_right hG
    have h1s : 1 - s ≠ 0 := fun e => by
      have := congrArg Complex.re e
      rw [Complex.sub_re, Complex.one_re, Complex.zero_re] at this
      linarith
    have hz' : riemannZeta (1 - s) = 0 := by
      rw [riemannZeta_def_of_ne_zero h1s, completedRiemannZeta_one_sub, hc, zero_div]
    exact riemannZeta_ne_zero_of_one_le_re (by rw [Complex.sub_re, Complex.one_re]; linarith) hz'
