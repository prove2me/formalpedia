-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_deriv_ge_one_of_regular_minimal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T06:43:48.861036+00:00
-- url     : https://prove2.me/submissions/a55320e0-a638-4347-8bcf-fbff7883672d

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution (W : ℝ → ℝ)
    (hreg : ContDiffOn ℝ 1 W (Ioi 0))
    (hpos : ∀ x : ℝ, 0 < x → 0 < deriv W x)
    (hmin : (cstar W).toReal = 0 ∨
      (0 < (cstar W).toReal ∧
        ∀ x : ℝ, 0 < x → deriv W (cstar W).toReal ≤ deriv W x)) :
    ∀ x : ℝ, 0 < x → DifferentiableAt ℝ (vcstar W) x ∧
      1 ≤ deriv (vcstar W) x := by
  intro x hx
  rcases hmin with hc0 | ⟨hc, hmin⟩
  · have hlocal : vcstar W =ᶠ[𝓝 x]
        (fun y : ℝ => y + divE (W 0) (scaleDeriv W 0)) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      change 0 < y at hy
      simp [vcstar, barrierValue, hc0, not_lt.mpr hy.le, not_le.mpr hy]
    have hd : HasDerivAt (vcstar W) 1 x :=
      ((hasDerivAt_id x).add_const _).congr_of_eventuallyEq hlocal
    exact ⟨hd.differentiableAt, by simpa [hd.deriv]⟩
  · let c := (cstar W).toReal
    have hc' : 0 < c := hc
    have hcne : c ≠ 0 := hc'.ne'
    have hdc : 0 < deriv W c := hpos c hc'
    have hscale : scaleDeriv W c = ((deriv W c : ℝ) : EReal) := by
      simp [scaleDeriv, hcne]
    have hdiv (y : ℝ) : divE (W y) (scaleDeriv W c) = W y / deriv W c := by
      simp [hscale, divE]
    have hWdiff (y : ℝ) (hy : 0 < y) : DifferentiableAt ℝ W y :=
      (hreg.differentiableOn_one y hy).differentiableAt (Ioi_mem_nhds hy)
    by_cases hxc : x = c
    · subst x
      have hL0 : HasDerivWithinAt (fun y : ℝ => W y / deriv W c) 1
          (Icc 0 c) c := by
        simpa [hdc.ne'] using
          ((hWdiff c hc').hasDerivAt.div_const (deriv W c)).hasDerivWithinAt
      have hL : HasDerivWithinAt (vcstar W) 1 (Icc 0 c) c :=
        hL0.congr_of_mem (fun y hy => by
          change 0 ≤ y ∧ y ≤ c at hy
          simp [vcstar, barrierValue, c, not_lt.mpr hy.1, hy.2, hdiv]) ⟨hc'.le, le_rfl⟩
      have hR0 : HasDerivWithinAt
          (fun y : ℝ => y - c + W c / deriv W c) 1 (Ici c) c := by
        simpa using (((hasDerivAt_id c).sub_const c).add_const
          (W c / deriv W c)).hasDerivWithinAt
      have hR : HasDerivWithinAt (vcstar W) 1 (Ici c) c :=
        hR0.congr_of_mem (fun y hy => by
          change c ≤ y at hy
          rcases eq_or_lt_of_le hy with rfl | hy'
          · simp [vcstar, barrierValue, c, hc'.le, hdiv]
          · have hy0 : 0 < y := hc'.trans hy'
            simp [vcstar, barrierValue, c, not_lt.mpr hy0.le,
              not_le.mpr hy', hdiv]) (by simp)
      have hu := hL.union hR
      rw [Icc_union_Ici_eq_Ici hc'.le] at hu
      have hd : HasDerivAt (vcstar W) 1 c := hu.hasDerivAt (Ici_mem_nhds hc')
      exact ⟨hd.differentiableAt, by simpa [hd.deriv]⟩
    · rcases lt_or_gt_of_ne hxc with hlt | hgt
      · have hlocal : vcstar W =ᶠ[𝓝 x] (fun y : ℝ => W y / deriv W c) := by
          filter_upwards [Ioo_mem_nhds hx hlt] with y hy
          change 0 < y ∧ y < c at hy
          simp [vcstar, barrierValue, c, not_lt.mpr hy.1.le, hy.2.le, hdiv]
        have hd : HasDerivAt (vcstar W) (deriv W x / deriv W c) x :=
          ((hWdiff x hx).hasDerivAt.div_const _).congr_of_eventuallyEq hlocal
        refine ⟨hd.differentiableAt, ?_⟩
        rw [hd.deriv, one_le_div₀ hdc]
        exact hmin x hx
      · have hlocal : vcstar W =ᶠ[𝓝 x]
            (fun y : ℝ => y - c + divE (W c) (scaleDeriv W c)) := by
          filter_upwards [Ioi_mem_nhds hgt] with y hy
          change c < y at hy
          have hy0 : 0 < y := hc'.trans hy
          simp [vcstar, barrierValue, c, not_lt.mpr hy0.le, not_le.mpr hy]
        have hd : HasDerivAt (vcstar W) 1 x :=
          (((hasDerivAt_id x).sub_const c).add_const
            (divE (W c) (scaleDeriv W c))).congr_of_eventuallyEq hlocal
        exact ⟨hd.differentiableAt, by simpa [hd.deriv]⟩
