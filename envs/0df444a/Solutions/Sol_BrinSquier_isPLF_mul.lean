-- Prove2me | solution 1 for BrinSquier.isPLF_mul
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-12T22:11:18.575111+00:00
-- url     : https://prove2.me/submissions/e127b7c1-b1b3-449a-94b2-694f93758fb8

import Definitions.Def_BrinSquier
import Mathlib

open BrinSquier

theorem solution {f g : ℝ ≃o ℝ} (hf : IsPLF f) (hg : IsPLF g) : IsPLF (f * g) := by
  classical
  obtain ⟨Bf, hBf⟩ := hf
  obtain ⟨Bg, hBg⟩ := hg
  refine ⟨Bg ∪ Bf.image (fun z => g⁻¹ z), ?_⟩
  intro x hx
  simp only [Finset.coe_union, Set.mem_union, Finset.coe_image, Set.mem_image,
    Finset.mem_coe, not_or, not_exists, not_and] at hx
  obtain ⟨hxg, hxf⟩ := hx
  -- `g` is affine near `x`
  obtain ⟨e1, he1, a1, b1, h1⟩ := hBg x hxg
  -- `g x` is not a breakpoint of `f`
  have hgx : (g x) ∉ (Bf : Set ℝ) := by
    intro hmem
    exact absurd (RelIso.inv_apply_self g x) (hxf _ (Finset.mem_coe.1 hmem))
  obtain ⟨e2, he2, a2, b2, h2⟩ := hBf (g x) hgx
  have habs : (0:ℝ) ≤ |a1| := abs_nonneg a1
  set d : ℝ := min e1 (e2 / (|a1| + 1)) with hd
  have hpos : 0 < d := lt_min he1 (div_pos he2 (by linarith))
  refine ⟨d, hpos, a2 * a1, a2 * b1 + b2, ?_⟩
  intro y hy
  have hyd : |y - x| < d := by
    rw [abs_sub_lt_iff]; constructor <;> [linarith [hy.2]; linarith [hy.1]]
  have hy1 : y ∈ Set.Ioo (x - e1) (x + e1) := by
    have : d ≤ e1 := min_le_left _ _
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hgxv : g x = a1 * x + b1 := h1 x ⟨by linarith, by linarith⟩
  have hgyv : g y = a1 * y + b1 := h1 y hy1
  -- `g y` stays inside the interval where `f` is affine
  have hclose : |g y - g x| < e2 := by
    have hrw : g y - g x = a1 * (y - x) := by rw [hgyv, hgxv]; ring
    have hle : |a1 * (y - x)| ≤ |a1| * d := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (le_of_lt hyd) habs
    have hdle : d ≤ e2 / (|a1| + 1) := min_le_right _ _
    have : |a1| * d ≤ |a1| * (e2 / (|a1| + 1)) := mul_le_mul_of_nonneg_left hdle habs
    have hden : (0:ℝ) < |a1| + 1 := by linarith
    have hc : (e2 / (|a1| + 1)) * (|a1| + 1) = e2 := by field_simp
    have hcpos : 0 < e2 / (|a1| + 1) := div_pos he2 hden
    have hfin : |a1| * (e2 / (|a1| + 1)) < e2 := by nlinarith [hc, hcpos]
    rw [hrw]; linarith
  have hgy2 : g y ∈ Set.Ioo (g x - e2) (g x + e2) := by
    rw [abs_sub_lt_iff] at hclose
    exact ⟨by linarith [hclose.2], by linarith [hclose.1]⟩
  show f (g y) = a2 * a1 * y + (a2 * b1 + b2)
  rw [h2 (g y) hgy2, hgyv]; ring
