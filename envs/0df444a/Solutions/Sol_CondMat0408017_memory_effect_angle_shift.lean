-- Prove2me | solution 1 for CondMat0408017.memory_effect_angle_shift
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-26T17:35:45.908805+00:00
-- url     : https://prove2.me/submissions/71c1f447-5839-4208-ad12-c4f7b50fa399

import Mathlib
import Definitions.Def_CondMat0408017_Basic

open MeasureTheory Filter Topology Complex CondMat0408017

theorem solution (θ0 θs : ℝ) (hθs : |θs| < Real.pi / 2) :
    memoryShiftAngle θ0 θs θ0 = θs ∧
    (∀ᶠ θ in 𝓝 θ0,
      Real.sin (memoryShiftAngle θ0 θs θ) - Real.sin θ = Real.sin θs - Real.sin θ0) ∧
    HasDerivAt (memoryShiftAngle θ0 θs) (Real.cos θ0 / Real.cos θs) θ0 := by
  have hθs_lo : -(Real.pi / 2) < θs := (abs_lt.mp hθs).1
  have hθs_hi : θs < Real.pi / 2 := (abs_lt.mp hθs).2
  have hsin_lo : -1 < Real.sin θs := by
    have hneg : Real.sin (-(Real.pi / 2)) = -1 := by rw [Real.sin_neg, Real.sin_pi_div_two]
    rw [← hneg]
    exact Real.strictMonoOn_sin (by constructor <;> linarith [Real.pi_pos])
      ⟨hθs_lo.le, hθs_hi.le⟩ hθs_lo
  have hsin_hi : Real.sin θs < 1 := by
    rw [← Real.sin_pi_div_two]
    exact Real.strictMonoOn_sin ⟨hθs_lo.le, hθs_hi.le⟩
      (by constructor <;> linarith [Real.pi_pos]) hθs_hi
  have hcos_pos : 0 < Real.cos θs := Real.cos_pos_of_mem_Ioo ⟨hθs_lo, hθs_hi⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [memoryShiftAngle, add_sub_cancel]
    exact Real.arcsin_sin hθs_lo.le hθs_hi.le
  · have hcont : Continuous (fun θ : ℝ => Real.sin θ + (Real.sin θs - Real.sin θ0)) := by fun_prop
    have hmem : Set.Ioo (-1 : ℝ) 1 ∈ 𝓝 (Real.sin θ0 + (Real.sin θs - Real.sin θ0)) := by
      rw [add_sub_cancel]
      exact Ioo_mem_nhds hsin_lo hsin_hi
    filter_upwards [hcont.continuousAt.preimage_mem_nhds hmem] with θ hθ
    simp only [Set.mem_preimage, Set.mem_Ioo] at hθ
    simp only [memoryShiftAngle]
    rw [Real.sin_arcsin hθ.1.le hθ.2.le]
    ring
  · have hinner : HasDerivAt (fun θ : ℝ => Real.sin θ + (Real.sin θs - Real.sin θ0)) (Real.cos θ0) θ0 :=
      (Real.hasDerivAt_sin θ0).add_const _
    have harcsin : HasDerivAt Real.arcsin (1 / Real.sqrt (1 - Real.sin θs ^ 2)) (Real.sin θs) :=
      Real.hasDerivAt_arcsin hsin_lo.ne' hsin_hi.ne
    have hcomp : HasDerivAt (fun θ => Real.arcsin (Real.sin θ + (Real.sin θs - Real.sin θ0)))
        ((1 / Real.sqrt (1 - Real.sin θs ^ 2)) * Real.cos θ0) θ0 := by
      have harcsin' : HasDerivAt Real.arcsin (1 / Real.sqrt (1 - Real.sin θs ^ 2))
          (Real.sin θ0 + (Real.sin θs - Real.sin θ0)) := by
        simpa [add_sub_cancel] using harcsin
      exact harcsin'.comp θ0 hinner
    have hsqrt : Real.sqrt (1 - Real.sin θs ^ 2) = Real.cos θs := by
      rw [← Real.cos_sq', Real.sqrt_sq hcos_pos.le]
    rw [hsqrt] at hcomp
    have hmul : 1 / Real.cos θs * Real.cos θ0 = Real.cos θ0 / Real.cos θs := by ring
    rw [hmul] at hcomp
    exact hcomp
