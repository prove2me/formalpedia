-- Prove2me | solution 1 for FourBlockIP350.Main.Supplement.two_point_majorization
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T09:02:11.578785+00:00
-- url     : https://prove2.me/submissions/12c26e6a-668f-4eed-81cf-29918a7cd895

import Mathlib

namespace FourBlockIP350.Main.Supplement

theorem two_point_majorization (ϕ : ℝ → ℝ) (hϕ : ConvexOn ℝ Set.univ ϕ)
    (a b c d : ℝ) (hsum : a + b = c + d)
    (hc : min a b ≤ c ∧ c ≤ max a b) (hd : min a b ≤ d ∧ d ≤ max a b) :
    ϕ c + ϕ d ≤ ϕ a + ϕ b := by
  have key : ∀ x y z : ℝ, x < y → x ≤ z → z ≤ y →
      ϕ z ≤ ((y - z) / (y - x)) * ϕ x + ((z - x) / (y - x)) * ϕ y := by
    intro x y z hxy hxz hzy
    have hpos : 0 < y - x := by linarith
    have h1 : 0 ≤ (y - z) / (y - x) := div_nonneg (by linarith) hpos.le
    have h2 : 0 ≤ (z - x) / (y - x) := div_nonneg (by linarith) hpos.le
    have h3 : (y - z) / (y - x) + (z - x) / (y - x) = 1 := by
      field_simp; ring
    have := hϕ.2 (Set.mem_univ x) (Set.mem_univ y) h1 h2 h3
    have hz : ((y - z) / (y - x)) • x + ((z - x) / (y - x)) • y = z := by
      simp only [smul_eq_mul]; field_simp; ring
    rw [hz] at this
    simpa [smul_eq_mul] using this
  have main : ∀ x y : ℝ, x ≤ y → x + y = c + d → x ≤ c → c ≤ y → x ≤ d → d ≤ y →
      ϕ c + ϕ d ≤ ϕ x + ϕ y := by
    intro x y hxy hs hxc hcy hxd hdy
    rcases eq_or_lt_of_le hxy with h | h
    · subst h
      have : c = x := le_antisymm hcy hxc
      have : d = x := le_antisymm hdy hxd
      subst_vars; rfl
    · have k1 := key x y c h hxc hcy
      have k2 := key x y d h hxd hdy
      have hpos : 0 < y - x := by linarith
      have e : ((y - c) / (y - x)) * ϕ x + ((c - x) / (y - x)) * ϕ y
          + (((y - d) / (y - x)) * ϕ x + ((d - x) / (y - x)) * ϕ y) = ϕ x + ϕ y := by
        have hd' : d = x + y - c := by linarith
        subst hd'
        field_simp; ring
      linarith
  rcases le_total a b with hab | hab
  · rw [min_eq_left hab, max_eq_right hab] at hc hd
    exact main a b hab hsum hc.1 hc.2 hd.1 hd.2
  · rw [min_eq_right hab, max_eq_left hab] at hc hd
    have := main b a hab (by linarith) hc.1 hc.2 hd.1 hd.2
    linarith

end FourBlockIP350.Main.Supplement

theorem solution (ϕ : ℝ → ℝ) (hϕ : ConvexOn ℝ Set.univ ϕ)
    (a b c d : ℝ) (hsum : a + b = c + d)
    (hc : min a b ≤ c ∧ c ≤ max a b) (hd : min a b ≤ d ∧ d ≤ max a b) :
    ϕ c + ϕ d ≤ ϕ a + ϕ b :=
  FourBlockIP350.Main.Supplement.two_point_majorization ϕ hϕ a b c d hsum hc hd
