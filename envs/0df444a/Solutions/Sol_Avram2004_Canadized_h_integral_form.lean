-- Prove2me | solution 1 for Avram2004.Canadized.h_integral_form
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T21:40:04.338993+00:00
-- url     : https://prove2.me/submissions/2389529b-440d-43b2-a834-49df16f1dd30

import Mathlib
import Definitions.Def_Avram2004_Shared_IsSNLevy
import Definitions.Def_Avram2004_Shared_Standing
import Definitions.Def_Avram2004_Shared_scaleFun
import Definitions.Def_Avram2004_Shared_tiltedScale
import Definitions.Def_Avram2004_Shared_reflected
import Definitions.Def_Avram2004_Shared_esscher
import Definitions.Def_Avram2004_Canadized_canadizedProblem

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Avram2004.H48e

lemma scaleFun_props (φ : ℝ → ℝ) (q : ℝ) :
    (∀ x, 0 ≤ Avram2004.Shared.scaleFun φ q x) ∧
      (∀ x ≤ 0, Avram2004.Shared.scaleFun φ q x = 0) := by
  unfold Avram2004.Shared.scaleFun
  split_ifs with h
  · exact ⟨h.choose_spec.1, h.choose_spec.2.1⟩
  · exact ⟨fun _ => by simp, fun _ _ => by simp⟩

lemma Iic_eq_interval (Wf : ℝ → ℝ) (hWz : ∀ x ≤ 0, Wf x = 0) (x : ℝ) :
    ∫ y in Set.Iic x, Wf y = ∫ y in Set.Ioc 0 x, Wf y := by
  calc ∫ y in Set.Iic x, Wf y = ∫ y in Set.Iic x, (Set.Ioi (0:ℝ)).indicator Wf y := by
        congr 1; funext y
        by_cases hy : (0:ℝ) < y
        · simp [Set.indicator_of_mem (Set.mem_Ioi.2 hy)]
        · rw [Set.indicator_of_notMem (by simpa using hy), hWz y (not_lt.1 hy)]
    _ = ∫ y in Set.Iic x ∩ Set.Ioi 0, Wf y := setIntegral_indicator measurableSet_Ioi
    _ = _ := by
        rw [Set.inter_comm, Set.Ioi_inter_Iic]

lemma interval_eq_Ioc (Wf : ℝ → ℝ) (hWz : ∀ x ≤ 0, Wf x = 0) (x : ℝ) :
    ∫ y in (0:ℝ)..x, Wf y = ∫ y in Set.Ioc 0 x, Wf y := by
  rw [intervalIntegral]
  have : ∫ y in Set.Ioc x 0, Wf y = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero (fun y hy => hWz y hy.2)
  rw [this, sub_zero]

end Avram2004.H48e

open MeasureTheory ProbabilityTheory Filter Topology NNReal ENNReal Avram2004 Avram2004.Canadized in
theorem solution {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (X : ℝ≥0 → Ω → ℝ)
    (hX : Shared.IsSNLevyWrt 𝓕 P X) (hS : Shared.Standing P X) (r : ℝ) (hr : 0 ≤ r) (hψ : Shared.psi P X 1 = r)
    (hQ : Shared.IsEsscher 𝓕 P Q X r) (α : ℝ) (hα : 0 < α) (η : Ω → ℝ) (lam : ℝ)
    (hη : IsExpClock 𝓕 Q η lam) (p : ℝ) (hp : p = α + lam + r)
    (z : ℝ) (hz : 0 ≤ z) :
    hCR P X p lam z =
        Real.exp z + (p - lam) * Real.exp z * ∫ y in (0 : ℝ)..(kappaLow P X p lam - z), Shared.W P X 0 p y ∧
      Real.exp z ≤ hCR P X p lam z := by
  have hlam : 0 < lam := hη.1
  have hp0 : 0 < p := by rw [hp]; linarith
  have hpl : 0 ≤ p - lam := by rw [hp]; linarith
  set Wf := Shared.scaleFun (Shared.tilt P X 0) p with hWfdef
  have hWeq : Shared.W P X 0 p = Wf := by
    funext x; simp [Shared.W, Shared.scaleFunExt, hp0.le, hWfdef]
  obtain ⟨hW0, hWz⟩ := Avram2004.H48e.scaleFun_props (Shared.tilt P X 0) p
  set x := kappaLow P X p lam - z with hx
  have hI : ∫ y in (0 : ℝ)..x, Shared.W P X 0 p y = ∫ y in Set.Ioc 0 x, Wf y := by
    rw [hWeq]; exact Avram2004.H48e.interval_eq_Ioc Wf hWz x
  have hZ : Shared.Z P X 0 p x = 1 + p * ∫ y in Set.Ioc 0 x, Wf y := by
    have : Shared.Z P X 0 p x = 1 + p * ∫ y in Set.Iic x, Shared.W P X 0 p y := rfl
    rw [this, hWeq, Avram2004.H48e.Iic_eq_interval Wf hWz x]
  have hnn : 0 ≤ ∫ y in Set.Ioc 0 x, Wf y := setIntegral_nonneg measurableSet_Ioc (fun y _ => hW0 y)
  have hh : hCR P X p lam z = Real.exp z + (p - lam) * Real.exp z * ∫ y in Set.Ioc 0 x, Wf y := by
    unfold hCR
    rw [← hx, hZ]
    field_simp
    ring
  refine ⟨by rw [hh, hI], ?_⟩
  rw [hh]
  have : 0 ≤ (p - lam) * Real.exp z * ∫ y in Set.Ioc 0 x, Wf y :=
    mul_nonneg (mul_nonneg hpl (Real.exp_pos z).le) hnn
  linarith
