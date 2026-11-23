-- Prove2me | solution 1 for BroughanRH.xiZerosReal
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-23T18:38:25.392591+00:00
-- url     : https://prove2.me/submissions/117b21ff-6378-454f-ae1f-94852a3701d8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_riemann_hypothesis

/-- `Λ(s) ≠ 0` for `Re s ≥ 1`, `s ≠ 1`. -/
lemma completed_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) (hs1 : s ≠ 1) :
    completedRiemannZeta s ≠ 0 := by
  have hpos : 0 < s.re := by linarith
  have hs0 : s ≠ 0 := by rintro rfl; simp at hpos
  have hG := Complex.Gammaℝ_ne_zero_of_re_pos hpos
  have hζ := riemannZeta_ne_zero_of_one_le_re hs
  rw [riemannZeta_def_of_ne_zero hs0] at hζ
  intro h
  rw [h, zero_div] at hζ
  exact hζ rfl

theorem solution :
    let xi (s : ℂ) : ℂ := (1 + s * (s-1) * completedRiemannZeta₀ s) / 2
    ∀ z : ℂ, xi (1/2 + Complex.I * z) = 0 → z.im = 0 := by
  intro xi z hz
  set s : ℂ := 1/2 + Complex.I * z with hsdef
  have hx : 1 + s * (s-1) * completedRiemannZeta₀ s = 0 := by
    have : xi s = 0 := hz
    simp only [xi] at this
    linear_combination 2 * this
  have hs0 : s ≠ 0 := by rintro h; rw [h] at hx; simp at hx
  have hs1 : s ≠ 1 := by rintro h; rw [h] at hx; simp at hx
  have h1s : (1 - s) ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have hΛ : completedRiemannZeta s = 0 := by
    rw [completedRiemannZeta_eq]
    have hss : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    field_simp
    linear_combination (-1 : ℂ) * hx
  have hre : s.re = 1/2 := by
    rcases le_or_gt 1 s.re with h | h
    · exact absurd hΛ (completed_ne_zero_of_one_le_re h hs1)
    rcases le_or_gt s.re 0 with h' | h'
    · have : 1 ≤ (1 - s).re := by simp; linarith
      refine absurd ?_ (completed_ne_zero_of_one_le_re this ?_)
      · rw [completedRiemannZeta_one_sub]; exact hΛ
      · intro h2; apply hs0; linear_combination -h2
    have hζ : riemannZeta s = 0 := by
      rw [riemannZeta_def_of_ne_zero hs0, hΛ, zero_div]
    apply riemann_hypothesis s hζ
    · rintro ⟨n, hn⟩
      rw [hn] at h'
      simp at h'
      have : (0:ℝ) ≤ n := n.cast_nonneg
      linarith
    · exact hs1
  have := hre
  rw [hsdef] at this
  simp at this
  linarith
