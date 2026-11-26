-- Prove2me | solution 1 for Eden.singularValueFunction_interpolate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:01:33.877558+00:00
-- url     : https://prove2.me/submissions/758b9a05-6ca1-4c25-843d-5c0cd4c96de9

import Definitions.Def_Eden_SingularValues
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.Compact
import Definitions.Def_Eden_SingularValueFunction
import Theorems.Thm_Eden_spectralProduct_interpolate

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution (A : PhaseSpace →ₗ[ℝ] PhaseSpace)
    {k : ℕ} (hk : k < 5) {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    singularValueFunction A ((k : ℝ) + α) =
      (∏ i ∈ Finset.range k, A.singularValues i) * A.singularValues k ^ α :=
  spectralProduct_interpolate _ hk hα₀ hα₁
end Eden
