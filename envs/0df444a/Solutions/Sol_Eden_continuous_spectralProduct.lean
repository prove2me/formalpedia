-- Prove2me | solution 1 for Eden.continuous_spectralProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:49:34.785395+00:00
-- url     : https://prove2.me/submissions/a89f11ef-daf0-480a-8759-7a2950ca3905

import Definitions.Def_Eden_SingularValues
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.Compact
import Definitions.Def_Eden_SingularValueFunction
import Theorems.Thm_Eden_continuous_singularWeight

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {n : ℕ} {a : ℕ → ℝ}
    (ha : ∀ i < n, a i ≠ 0) : Continuous (spectralProduct n a) := by
  unfold spectralProduct
  apply continuous_finsetProd
  intro i hi
  exact (Real.continuous_const_rpow (ha i (Finset.mem_range.mp hi))).comp
    (continuous_singularWeight i)
end Eden
