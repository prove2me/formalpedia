-- Prove2me | solution 1 for EdenVerified.D08_singular_value_function
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:01:55.916251+00:00
-- url     : https://prove2.me/submissions/5f6647df-a9cb-4b49-9891-5a5ea3745a07

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_continuous_singularValueFunction
import Theorems.Thm_Eden_singularValueFunction_five
import Theorems.Thm_Eden_singularValueFunction_interpolate
import Theorems.Thm_Eden_singularValueFunction_zero
attribute [local simp] Eden.singularValueFunction_zero



set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution (M : PhaseSpace →ₗ[ℝ] PhaseSpace)
    (hM : Function.Injective M) :
    singularValueFunction M 0 = 1 ∧
    (∀ k : ℕ, k < 5 → ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
      singularValueFunction M ((k : ℝ) + α) =
        (∏ i ∈ Finset.range k, M.singularValues i) * M.singularValues k ^ α) ∧
    singularValueFunction M 5 = |M.det| ∧
    ContinuousOn (singularValueFunction M) (Icc 0 5) :=
  ⟨singularValueFunction_zero M,
    fun _k hk _α hα₀ hα₁ => singularValueFunction_interpolate M hk hα₀ hα₁,
    singularValueFunction_five M, (continuous_singularValueFunction hM).continuousOn⟩
end EdenVerified
