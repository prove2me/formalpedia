-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_all_beta_wh_analytic_continuation_with_removable_root
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T10:35:06.148389+00:00
-- url     : https://prove2.me/submissions/8d3dba42-735e-432b-8c6b-4522e319018f

import Mathlib
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.FDeriv.Analytic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped Topology

theorem solution
    (p lam m : ℝ) (hp : 0 < p) (hlam : 0 < lam) (hm : 0 < m)
    (L g : ℝ → ℝ)
    (hLAnalytic : AnalyticOnNhd ℝ L (Set.Ioi (0 : ℝ)))
    (hgAnalytic : AnalyticOnNhd ℝ g (Set.Ioi (0 : ℝ)))
    (hgRoot : g lam = p) (hgDeriv : HasDerivAt g m lam)
    (hgUnique : ∀ β : ℝ, 0 < β → β ≠ lam → g β ≠ p)
    (hStrip : ∀ β : ℝ, 0 < β → β < lam →
      L β * (p - g β) = (p / lam) * (lam - β)) :
    ∀ β : ℝ, 0 < β →
      L β = if β = lam then p / (lam * m)
        else (p / lam) * ((lam - β) / (p - g β)) := by
  have hConstP :
      AnalyticOnNhd ℝ (fun _ : ℝ => p) (Set.Ioi (0 : ℝ)) :=
    analyticOnNhd_const
  have hConstlam :
      AnalyticOnNhd ℝ (fun _ : ℝ => lam) (Set.Ioi (0 : ℝ)) :=
    analyticOnNhd_const
  have hConstRatio :
      AnalyticOnNhd ℝ (fun _ : ℝ => p / lam) (Set.Ioi (0 : ℝ)) :=
    analyticOnNhd_const
  have hId : AnalyticOnNhd ℝ (fun x : ℝ => x) (Set.Ioi (0 : ℝ)) :=
    analyticOnNhd_id
  have hLeft :
      AnalyticOnNhd ℝ (fun β : ℝ => L β * (p - g β)) (Set.Ioi (0 : ℝ)) :=
    hLAnalytic.mul (hConstP.sub hgAnalytic)
  have hRight :
      AnalyticOnNhd ℝ (fun β : ℝ => (p / lam) * (lam - β)) (Set.Ioi (0 : ℝ)) :=
    hConstRatio.mul (hConstlam.sub hId)
  have hMid : lam / 2 ∈ Set.Ioo (0 : ℝ) lam := by
    change 0 < lam / 2 ∧ lam / 2 < lam
    constructor <;> linarith
  have hLocal :
      (fun β : ℝ => L β * (p - g β)) =ᶠ[𝓝 (lam / 2)]
        (fun β : ℝ => (p / lam) * (lam - β)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hMid] with β hβ
    exact hStrip β hβ.1 hβ.2
  have hEqOn :
      Set.EqOn (fun β : ℝ => L β * (p - g β))
        (fun β : ℝ => (p / lam) * (lam - β)) (Set.Ioi (0 : ℝ)) :=
    hLeft.eqOn_of_preconnected_of_eventuallyEq hRight
      isPreconnected_Ioi (by change 0 < lam / 2; linarith) hLocal
  have hRootMem : lam ∈ Set.Ioi (0 : ℝ) := hlam
  have hRootLocal :
      (fun β : ℝ => L β * (p - g β)) =ᶠ[𝓝 lam]
        (fun β : ℝ => (p / lam) * (lam - β)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hRootMem] with β hβ
    exact hEqOn hβ
  have hLDeriv : HasDerivAt L (deriv L lam) lam :=
    ((hLAnalytic.differentiableOn lam hRootMem).differentiableAt
      (isOpen_Ioi.mem_nhds hRootMem)).hasDerivAt
  have hLeftDeriv :
      HasDerivAt (fun β : ℝ => L β * (p - g β))
        ((deriv L lam) * (p - g lam) + L lam * (0 - m)) lam := by
    convert (hLDeriv.mul ((hasDerivAt_const lam p).sub hgDeriv)) using 1 <;>
      first | rfl | ring
  have hRightDeriv :
      HasDerivAt (fun β : ℝ => (p / lam) * (lam - β))
        ((p / lam) * (0 - 1)) lam := by
    convert (((hasDerivAt_const lam lam).sub (hasDerivAt_id lam)).const_mul (p / lam)) using 1 <;>
      first | rfl | ring
  have hSlope :
      (deriv L lam) * (p - g lam) + L lam * (0 - m) =
        (p / lam) * (0 - 1) :=
    hLeftDeriv.unique (hRightDeriv.congr_of_eventuallyEq hRootLocal)
  have hLm : L lam * m = p / lam := by
    have hNeg : -(L lam * m) = -(p / lam) := by
      simpa [hgRoot] using hSlope
    linarith
  have hlamne : lam ≠ 0 := ne_of_gt hlam
  have hmne : m ≠ 0 := ne_of_gt hm
  have hAtRoot : L lam = p / (lam * m) := by
    apply (eq_div_iff (mul_ne_zero hlamne hmne)).2
    calc
      L lam * (lam * m) = lam * (L lam * m) := by ring
      _ = lam * (p / lam) := by rw [hLm]
      _ = p := by field_simp [hlamne]
  intro β hβ
  by_cases hβlam : β = lam
  · subst β
    simp only [if_pos rfl]
    exact hAtRoot
  · have hDen : p - g β ≠ 0 :=
      sub_ne_zero.mpr (Ne.symm (hgUnique β hβ hβlam))
    simp only [if_neg hβlam]
    calc
      L β = (L β * (p - g β)) / (p - g β) := by
        field_simp [hDen]
      _ = ((p / lam) * (lam - β)) / (p - g β) := by
        exact congrArg (fun x : ℝ => x / (p - g β)) (hEqOn hβ)
      _ = (p / lam) * ((lam - β) / (p - g β)) := by ring
