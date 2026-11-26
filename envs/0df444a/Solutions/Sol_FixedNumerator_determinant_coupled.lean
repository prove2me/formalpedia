-- Prove2me | solution 1 for FixedNumerator.determinant_coupled
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:49:41.734105+00:00
-- url     : https://prove2.me/submissions/894d51bd-47c2-4b4c-bb2a-33ad8b2c7295

module
public import Definitions.Def_FixedNumerator
public import Definitions.Def_FixedNumerator_Solution
public import Theorems.Thm_FixedNumerator_delta_coupled_lower


set_option autoImplicit true
@[expose] public section
public section
open Complex Finset Filter Asymptotics Topology
open scoped ContDiff
noncomputable section
open FixedNumerator
namespace FixedNumerator
theorem _root_.solution (N σ : ℝ) (hN : 1 < N) (a₁ a₃ w : ℂ)
    (ha₁ : ‖a₁‖ ≤ N ^ ((1 : ℝ) / 2)) (ha₃ : ‖a₃‖ ≤ N ^ ((5 : ℝ) / 2)) (hw : ‖w‖ = N ^ (-σ))
    (hσ : 1 ≤ σ) :
    0 < 1 - N ^ (-1 : ℝ) ∧ 1 - N ^ (-1 : ℝ) ≤ ‖1 - a₁ * a₃ * w ^ 4‖ :=
  delta_coupled_lower hN ha₁ ha₃ hw hσ
end FixedNumerator
