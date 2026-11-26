-- Prove2me | solution 1 for FD1D.haarCombination_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:32:04.597828+00:00
-- url     : https://prove2.me/submissions/bb9054ef-1644-4339-a3a8-d59fcf626d13

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
import Theorems.Thm_FD1D_dyadicTent_integrable

set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]
namespace FD1D
theorem _root_.solution (l p b : ι → ℝ) :
    Integrable (haarCombination l p b) := by
  unfold haarCombination
  exact integrable_finsetSum _ fun i _ =>
    (dyadicTent_integrable (l i) (p i)).const_mul _
end FD1D
