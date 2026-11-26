-- Prove2me | solution 1 for FD1D.expected_area_le_sqrt_l2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:38:47.729994+00:00
-- url     : https://prove2.me/submissions/6e8ece5a-3af8-4c3f-9a7c-16b1788b93f8

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
import Theorems.Thm_FD1D_cdfTransportArea_nonneg
import Theorems.Thm_FD1D_cdfTransportArea_sq_le_haarL2
import Theorems.Thm_FD1D_FiniteLaw_expect_le_sqrt_expect_sq

set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]
namespace FD1D
theorem _root_.solution (μ : FiniteLaw Ω) (l p : ι → ℝ)
    (b : Ω → ι → ℝ) (hp : ∀ i, 0 < p i) :
    μ.expect (fun ω => cdfTransportArea (haarCombination l p (b ω))) ≤
      Real.sqrt (μ.expect (fun ω => haarL2 l p (b ω))) := by
  apply μ.expect_le_sqrt_expect_sq
  · exact fun _ => cdfTransportArea_nonneg _
  · exact fun _ => integral_nonneg fun _ => sq_nonneg _
  · exact fun ω => cdfTransportArea_sq_le_haarL2 l p (b ω) hp
end FD1D
