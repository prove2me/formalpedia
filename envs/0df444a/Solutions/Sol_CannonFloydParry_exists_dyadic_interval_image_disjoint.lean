-- Prove2me | solution 1 for CannonFloydParry.exists_dyadic_interval_image_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T22:16:56.467788+00:00
-- url     : https://prove2.me/submissions/356c8bcd-4010-4330-9fd0-52ce7f70ec44

import Definitions.Def_CannonFloydParry
import Mathlib

open CannonFloydParry

/-- Between any two distinct reals there is a dyadic rational.

`⌊u * 2 ^ k⌋ + 1` over `2 ^ k` lands in `(u, u + 2 ^ (-k)]`, and `2 ^ (-k) < v - u`
once `2 ^ k` exceeds `1 / (v - u)`. -/
private lemma exists_dyadic_btwn {u v : ℝ} (h : u < v) :
    ∃ q : ℝ, IsDyadic q ∧ u < q ∧ q < v := by
  have hvu : (0:ℝ) < v - u := sub_pos.mpr h
  obtain ⟨k, hk⟩ :=
    pow_unbounded_of_one_lt (1 / (v - u)) (by norm_num : (1:ℝ) < 2)
  have hpos : (0:ℝ) < (2:ℝ) ^ k := by positivity
  have hwide : (1:ℝ) < 2 ^ k * (v - u) := (div_lt_iff₀ hvu).mp hk
  have hfl : ((⌊u * (2:ℝ) ^ k⌋ : ℤ) : ℝ) ≤ u * (2:ℝ) ^ k := Int.floor_le _
  have hfl2 : u * (2:ℝ) ^ k < ((⌊u * (2:ℝ) ^ k⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  refine ⟨((⌊u * (2:ℝ) ^ k⌋ + 1 : ℤ) : ℝ) / (2:ℝ) ^ k,
    ⟨⌊u * (2:ℝ) ^ k⌋ + 1, k, rfl⟩, ?_, ?_⟩
  · rw [lt_div_iff₀ hpos]
    push_cast
    linarith
  · rw [div_lt_iff₀ hpos]
    push_cast
    linarith

theorem solution {f : UI ≃o UI} (hf : f ∈ F) (hf1 : f ≠ 1) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < 1 ∧ IsDyadic a ∧ IsDyadic b ∧
      ∀ z : UI, (z : ℝ) ∈ Set.Icc a b → (f z : ℝ) ∉ Set.Icc a b := by
  -- `f ≠ 1` gives a moved point `t`.
  obtain ⟨t, ht⟩ : ∃ t : UI, ((f t : UI) : ℝ) ≠ ((t : UI) : ℝ) := by
    by_contra hc
    push_neg at hc
    exact hf1 (RelIso.ext fun z => Subtype.ext (hc z))
  have ht0 : (0:ℝ) ≤ ((t : UI) : ℝ) := t.2.1
  have ht1 : ((t : UI) : ℝ) ≤ 1 := t.2.2
  have hft0 : (0:ℝ) ≤ ((f t : UI) : ℝ) := (f t).2.1
  have hft1 : ((f t : UI) : ℝ) ≤ 1 := (f t).2.2
  rcases lt_or_gt_of_ne ht with hlt | hgt
  · -- `f t < t`: take dyadics `f t < a < b < t`.
    obtain ⟨a, hda, ha1, ha2⟩ := exists_dyadic_btwn hlt
    obtain ⟨b, hdb, hb1, hb2⟩ := exists_dyadic_btwn ha2
    refine ⟨a, b, by linarith, hb1, by linarith, hda, hdb, ?_⟩
    intro z hz hfz
    have hzt : ((z : UI) : ℝ) ≤ ((t : UI) : ℝ) := le_trans hz.2 (le_of_lt hb2)
    have hmono : ((f z : UI) : ℝ) ≤ ((f t : UI) : ℝ) := (OrderIso.le_iff_le f).mpr hzt
    linarith [hfz.1]
  · -- `t < f t`: take dyadics `t < a < b < f t`.
    obtain ⟨a, hda, ha1, ha2⟩ := exists_dyadic_btwn hgt
    obtain ⟨b, hdb, hb1, hb2⟩ := exists_dyadic_btwn ha2
    refine ⟨a, b, by linarith, hb1, by linarith, hda, hdb, ?_⟩
    intro z hz hfz
    have hzt : ((t : UI) : ℝ) ≤ ((z : UI) : ℝ) := le_trans (le_of_lt ha1) hz.1
    have hmono : ((f t : UI) : ℝ) ≤ ((f z : UI) : ℝ) := (OrderIso.le_iff_le f).mpr hzt
    linarith [hfz.2]
