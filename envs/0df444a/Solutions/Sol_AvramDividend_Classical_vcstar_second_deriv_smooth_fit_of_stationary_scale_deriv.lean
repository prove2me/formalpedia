-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_second_deriv_smooth_fit_of_stationary_scale_deriv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T17:05:57.953005+00:00
-- url     : https://prove2.me/submissions/813ade71-caaf-491f-9878-29b1b0a6fce6

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_eq_one_above_cstar

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    (W : ℝ → ℝ)
    (hc : 0 < (cstar W).toReal)
    (hWdiff : ∀ y : ℝ, 0 < y → DifferentiableAt ℝ W y)
    (hdne : deriv W (cstar W).toReal ≠ 0)
    (hWstat : HasDerivAt (deriv W) 0 (cstar W).toReal)
    (hvderiv : deriv (vcstar W) (cstar W).toReal = 1) :
    deriv (deriv (vcstar W)) (cstar W).toReal =
      deriv (deriv (fun z : ℝ =>
        divE (W z) (scaleDeriv W (cstar W).toReal))) (cstar W).toReal := by
  let c := (cstar W).toReal
  have hc' : 0 < c := hc
  have hcne : c ≠ 0 := hc'.ne'
  have hdne' : deriv W c ≠ 0 := hdne
  have hv : deriv (vcstar W) c = 1 := hvderiv
  have hscale : scaleDeriv W c = ((deriv W c : ℝ) : EReal) := by
    simp [scaleDeriv, hcne]
  have hdiv (y : ℝ) :
      divE (W y) (scaleDeriv W c) = W y / deriv W c := by
    simp [hscale, divE]
  have hderivLeft (y : ℝ) (hy : 0 < y) (hyc : y < c) :
      deriv (vcstar W) y = deriv W y / deriv W c := by
    have hlocal : vcstar W =ᶠ[𝓝 y]
        (fun z : ℝ => W z / deriv W c) := by
      filter_upwards [Ioo_mem_nhds hy hyc] with z hz
      change 0 < z ∧ z < c at hz
      simp [vcstar, barrierValue, c, not_lt.mpr hz.1.le, hz.2.le, hdiv]
    have hd : HasDerivAt (vcstar W) (deriv W y / deriv W c) y :=
      ((hWdiff y hy).hasDerivAt.div_const _).congr_of_eventuallyEq hlocal
    exact hd.deriv
  have hL0 : HasDerivWithinAt
      (fun y : ℝ => deriv W y / deriv W c) 0 (Ioc 0 c) c := by
    simpa using (hWstat.div_const (deriv W c)).hasDerivWithinAt
  have hL : HasDerivWithinAt
      (deriv (vcstar W)) 0 (Ioc 0 c) c :=
    hL0.congr_of_mem (fun y hy => by
      change 0 < y ∧ y ≤ c at hy
      rcases eq_or_lt_of_le hy.2 with rfl | hylt
      · simpa [hv, hdne']
      · exact hderivLeft y hy.1 hylt) ⟨hc', le_rfl⟩
  have hR0 : HasDerivWithinAt
      (fun _ : ℝ => (1 : ℝ)) 0 (Ici c) c := by
    simpa using (hasDerivAt_const c (1 : ℝ)).hasDerivWithinAt
  have hR : HasDerivWithinAt
      (deriv (vcstar W)) 0 (Ici c) c :=
    hR0.congr_of_mem (fun y hy => by
      change c ≤ y at hy
      rcases eq_or_lt_of_le hy with rfl | hygt
      · exact hv
      · exact AvramDividend.Classical.vcstar_deriv_eq_one_above_cstar
          W y hygt) (by simp)
  have hcover : Ioc (0 : ℝ) c ∪ Ici c = Ioi 0 := by
    ext y
    simp only [mem_union, mem_Ioc, mem_Ici, mem_Ioi]
    constructor
    · intro hy
      rcases hy with ⟨hy, _⟩ | hy
      · exact hy
      · exact lt_of_lt_of_le hc' hy
    · intro hy
      rcases le_total y c with hyc | hcy
      · exact Or.inl ⟨hy, hyc⟩
      · exact Or.inr hcy
  have hu := hL.union hR
  rw [hcover] at hu
  have hvcsecond : HasDerivAt (deriv (vcstar W)) 0 c :=
    hu.hasDerivAt (Ioi_mem_nhds hc')
  have hDerivScaleLocal :
      (fun y : ℝ => deriv (fun z : ℝ => W z / deriv W c) y)
        =ᶠ[𝓝 c] (fun y : ℝ => deriv W y / deriv W c) := by
    filter_upwards [Ioi_mem_nhds hc'] with y hy
    change 0 < y at hy
    exact ((hWdiff y hy).hasDerivAt.div_const _).deriv
  have hScaledSecond0 :
      HasDerivAt (fun y : ℝ => deriv W y / deriv W c) 0 c := by
    simpa using hWstat.div_const (deriv W c)
  have hScaledSecond1 :
      HasDerivAt (deriv (fun z : ℝ => W z / deriv W c)) 0 c :=
    hScaledSecond0.congr_of_eventuallyEq hDerivScaleLocal
  have hFunEq :
      (fun z : ℝ => divE (W z) (scaleDeriv W c)) =
        (fun z : ℝ => W z / deriv W c) := funext hdiv
  have hScaledSecond : HasDerivAt
      (deriv (fun z : ℝ => divE (W z) (scaleDeriv W c))) 0 c := by
    simpa only [hFunEq] using hScaledSecond1
  exact hvcsecond.deriv.trans hScaledSecond.deriv.symm
