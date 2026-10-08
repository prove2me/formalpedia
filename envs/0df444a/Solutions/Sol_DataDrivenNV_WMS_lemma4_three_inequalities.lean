-- Prove2me | solution 1 for DataDrivenNV.WMS.lemma4_three_inequalities
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T01:53:18.349049+00:00
-- url     : https://prove2.me/submissions/2f13b1e3-1670-4d48-baad-cc8eda315e9b

import Mathlib
import Definitions.Def_LogConcaveOn
import Definitions.Def_DataDrivenNV_WMS_Setting

open MeasureTheory

private lemma log_bound (b : ℝ) (hb : 0 < b) (hb1 : b < 1) :
    0 ≤ b / (1 - b) * Real.log (1 / b) - b := by
  have hl := Real.log_le_sub_one_of_pos hb
  rw [Real.log_div (by norm_num) hb.ne', Real.log_one]
  have hd : 0 < 1 - b := by linarith
  have hc : b / (1 - b) * (1 - b) = b := by field_simp
  have hm := mul_le_mul_of_nonneg_left (show 1 - b ≤ -Real.log b by linarith)
    (show 0 ≤ b / (1 - b) by positivity)
  nlinarith

theorem solution (β η : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hη0 : -(1 / (1 - β)) < η) (hη1 : η < 1 / β) :
    0 ≤ (1 / (1 - β) + η) * Real.log (1 + η * (1 - β)) + (1 / β - η) * Real.log (1 - η * β)
        - min β (1 - β) * η ^ 2 ∧
    0 ≤ β / (1 - β) * Real.log (1 / β) - β ∧
    0 ≤ (1 - β) / β * Real.log (1 / (1 - β)) - (1 - β) := by
  have ha : 0 < 1 - β := by linarith
  have hbn := hβ0.ne'
  have han := ha.ne'
  let D := Set.Ioo (-(1 / (1 - β))) (1 / β)
  let m := min β (1 - β)
  let g := fun x : ℝ => (1 / (1 - β) + x) * Real.log (1 + x * (1 - β)) +
    (1 / β - x) * Real.log (1 - x * β) - m * x ^ 2
  let g' := fun x : ℝ => Real.log (1 + x * (1 - β)) - Real.log (1 - x * β) - 2 * m * x
  let g'' := fun x : ℝ => (1 - β) / (1 + x * (1 - β)) + β / (1 - x * β) - 2 * m
  have pos (x : ℝ) (hx : x ∈ D) : 0 < 1 + x * (1 - β) ∧ 0 < 1 - x * β := by
    have h1 := (div_lt_iff₀ ha).mp (show -1 / (1 - β) < x by simpa only [neg_div] using hx.1)
    have h2 := (lt_div_iff₀ hβ0).mp hx.2
    constructor <;> nlinarith
  have hg (x : ℝ) (hx : x ∈ D) : HasDerivAt g (g' x) x := by
    obtain ⟨hu,hv⟩ := pos x hx
    have hu' := ((hasDerivAt_id x).mul_const (1 - β)).const_add 1
    have hv' := ((hasDerivAt_id x).mul_const β).const_sub 1
    have hd := (((hasDerivAt_id x).const_add (1 / (1 - β))).mul (hu'.log hu.ne')).add
      (((hasDerivAt_id x).const_sub (1 / β)).mul (hv'.log hv.ne'))
    have hs := hd.sub (((hasDerivAt_id x).pow 2).const_mul m)
    convert hs using 1 <;> first | rfl | (dsimp [g, g']; field_simp [hu.ne', hv.ne', han, hbn]; ring)
  have hg' (x : ℝ) (hx : x ∈ D) : HasDerivAt g' (g'' x) x := by
    obtain ⟨hu,hv⟩ := pos x hx
    convert ((((hasDerivAt_id x).mul_const (1 - β)).const_add 1).log hu.ne').sub
      ((((hasDerivAt_id x).mul_const β).const_sub 1).log hv.ne') |>.sub
      ((hasDerivAt_id x).const_mul (2 * m)) using 1 <;>
      first | rfl | (dsimp [g',g'']; ring)
  have hg'' (x : ℝ) (hx : x ∈ D) : 0 ≤ g'' x := by
    obtain ⟨hu,hv⟩ := pos x hx
    have huv : 0 < (1 + x * (1 - β)) * (1 - x * β) := mul_pos hu hv
    have hc : 2 * m ≤ 4 * β * (1 - β) := by
      dsimp [m]
      rcases le_total β (1 - β) with h | h
      · rw [min_eq_left h]; nlinarith
      · rw [min_eq_right h]; nlinarith
    have hs : 4 * β * (1 - β) * ((1 + x * (1 - β)) * (1 - x * β)) ≤ 1 := by
      nlinarith [sq_nonneg (β * (1 + x * (1 - β)) - (1 - β) * (1 - x * β))]
    have hm := mul_le_mul_of_nonneg_right hc huv.le
    have he : g'' x * ((1 + x * (1 - β)) * (1 - x * β)) =
        1 - 2 * m * ((1 + x * (1 - β)) * (1 - x * β)) := by
      calc
        g'' x * ((1 + x * (1 - β)) * (1 - x * β)) =
          (((1 - β) / (1 + x * (1 - β))) * (1 + x * (1 - β))) * (1 - x * β) +
          ((β / (1 - x * β)) * (1 - x * β)) * (1 + x * (1 - β)) -
          2 * m * ((1 + x * (1 - β)) * (1 - x * β)) := by dsimp [g'']; ring
        _ = (1 - β) * (1 - x * β) + β * (1 + x * (1 - β)) -
          2 * m * ((1 + x * (1 - β)) * (1 - x * β)) := by
            rw [div_mul_cancel₀ _ hu.ne', div_mul_cancel₀ _ hv.ne']
        _ = _ := by ring
    have : 0 ≤ g'' x * ((1 + x * (1 - β)) * (1 - x * β)) := by linarith
    exact nonneg_of_mul_nonneg_left this huv
  have hc : ConvexOn ℝ D g := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioo _ _)
      (fun x hx => (hg x hx).continuousAt.continuousWithinAt)
      (f' := g') (f'' := g'')
    · intro x hx; exact (hg x (interior_subset hx)).hasDerivWithinAt
    · intro x hx; exact (hg' x (interior_subset hx)).hasDerivWithinAt
    · intro x hx; exact hg'' x (interior_subset hx)
  have h0 : (0 : ℝ) ∈ D := by
    dsimp [D]
    have h1 : 0 < 1 / (1 - β) := by positivity
    have h2 : 0 < 1 / β := by positivity
    constructor <;> linarith
  have hz : HasDerivAt g 0 0 := by simpa [g',g] using hg 0 h0
  have hη : η ∈ D := ⟨hη0,hη1⟩
  have hg0 : g 0 = 0 := by simp [g]
  have hmain : 0 ≤ g η := by
    rcases lt_trichotomy η 0 with h | h | h
    · have hs := hc.slope_le_of_hasDerivAt hη h0 h hz
      rw [slope_def_field, hg0] at hs
      have := (div_nonpos_iff).mp hs
      rcases this with h' | h' <;> nlinarith
    · subst η; rw [hg0]
    · have hs := hc.le_slope_of_hasDerivAt h0 hη h hz
      rw [slope_def_field, hg0] at hs
      have := (div_nonneg_iff).mp hs
      rcases this with h' | h' <;> linarith
  refine ⟨hmain, log_bound β hβ0 hβ1, ?_⟩
  simpa using log_bound (1 - β) ha (by linarith)

#print axioms solution
