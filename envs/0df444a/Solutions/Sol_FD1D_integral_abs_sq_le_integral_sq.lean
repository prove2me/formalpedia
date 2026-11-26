-- Prove2me | solution 1 for FD1D.integral_abs_sq_le_integral_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:32:22.832703+00:00
-- url     : https://prove2.me/submissions/38cddd34-5888-487d-99f5-8b298d8ecd9a

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const



set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]
namespace FD1D
theorem _root_.solution {f : ℝ → ℝ}
    (hf : IntegrableOn f (Icc 0 1))
    (hfsq : IntegrableOn (fun z => f z ^ 2) (Icc 0 1)) :
    cdfTransportArea f ^ 2 ≤ ∫ z in Icc (0 : ℝ) 1, f z ^ 2 := by
  let ν : Measure ℝ := volume.restrict (Icc 0 1)
  letI : IsProbabilityMeasure ν := ⟨by
    simp [ν, Real.volume_Icc]⟩
  have habs : Integrable (fun z => |f z|) ν := hf.norm
  have habssq : Integrable (fun z => |f z| ^ 2) ν := by
    simpa [ν, IntegrableOn, sq_abs] using hfsq
  have hj := (Even.convexOn_pow (even_iff_two_dvd.mpr (by norm_num : 2 ∣ 2)) :
      ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2)).map_integral_le
      (continuous_pow 2).continuousOn isClosed_univ
      (Filter.Eventually.of_forall fun _ => Set.mem_univ _)
      habs habssq
  simpa [ν, cdfTransportArea, Function.comp_def] using hj
end FD1D
