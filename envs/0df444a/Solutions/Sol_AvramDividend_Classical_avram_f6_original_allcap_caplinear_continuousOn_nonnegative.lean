-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_allcap_caplinear_continuousOn_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T17:24:24.517192+00:00
-- url     : https://prove2.me/submissions/362933d1-7b28-40ef-8f59-c9beafec7413

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0))
    (C : ℝ≥0∞) :
    ContinuousOn
      (fun z : ℝ => if ENNReal.ofReal z ≤ C then w z
         else w C.toReal + (z - C.toReal)) (Ici 0) := by
  by_cases htop : C = ⊤
  · simpa [htop] using hw
  · have hboundary : ∀ z ∈ (Ici (0 : ℝ)) ∩
        frontier {a : ℝ | a ≤ C.toReal},
        w z = w C.toReal + (z - C.toReal) := by
      intro z hz
      have hzC : z = C.toReal := by
        have hmem : z ∈ frontier (Iic C.toReal) := hz.2
        simpa only [frontier_Iic, mem_singleton_iff] using hmem
      subst z
      ring
    have hleft : ContinuousOn w
        ((Ici (0 : ℝ)) ∩ closure {a : ℝ | a ≤ C.toReal}) :=
      hw.mono inter_subset_left
    have hright : ContinuousOn
        (fun z : ℝ => w C.toReal + (z - C.toReal))
        ((Ici (0 : ℝ)) ∩ closure {a : ℝ | ¬ a ≤ C.toReal}) := by
      fun_prop
    have hpiece := ContinuousOn.if hboundary hleft hright
    have heq (z : ℝ) : (ENNReal.ofReal z ≤ C) ↔ z ≤ C.toReal :=
      ENNReal.ofReal_le_iff_le_toReal htop
    simpa only [heq] using hpiece
