-- Prove2me | solution 1 for Eden.real_subadditive_mul_add_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:47:21.252356+00:00
-- url     : https://prove2.me/submissions/e5a9f4aa-ca6f-40d4-ae67-189314b9e49c

import Definitions.Def_Eden_GlobalGrowth
import Mathlib.Analysis.Subadditive
import Mathlib.Algebra.Order.Floor.Semiring
import Definitions.Def_Eden_RealSubadditive
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_diagonalLinear_apply
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_planarX_origin
import Theorems.Thm_Eden_planarX_zero_time
import Theorems.Thm_Eden_planarY_origin
import Theorems.Thm_Eden_planarY_zero_time
import Theorems.Thm_Eden_radialAmplitude_zero_time
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_radialDiscriminant_at_zero
import Theorems.Thm_Eden_radialDiscriminant_zero_time
import Theorems.Thm_Eden_singularValueFunction_zero
import Theorems.Thm_Eden_spectralProduct_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_at_one
import Theorems.Thm_Eden_squaredRadiusEvolution_at_two
import Theorems.Thm_Eden_squaredRadiusEvolution_at_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
attribute [local simp] Eden.amplitudeSq_at_zero
attribute [local simp] Eden.amplitudeSq_zero_time
attribute [local simp] Eden.blockRotation_apply
attribute [local simp] Eden.diagonalLinear_apply
attribute [local simp] Eden.evolution_zero_time
attribute [local simp] Eden.planarAmplitude_zero_time
attribute [local simp] Eden.planarX_origin
attribute [local simp] Eden.planarX_zero_time
attribute [local simp] Eden.planarY_origin
attribute [local simp] Eden.planarY_zero_time
attribute [local simp] Eden.radialAmplitude_zero_time
attribute [local simp] Eden.radialDiscriminant_at_two
attribute [local simp] Eden.radialDiscriminant_at_zero
attribute [local simp] Eden.radialDiscriminant_zero_time
attribute [local simp] Eden.singularValueFunction_zero
attribute [local simp] Eden.spectralProduct_zero
attribute [local simp] Eden.squaredRadiusEvolution_at_one
attribute [local simp] Eden.squaredRadiusEvolution_at_two
attribute [local simp] Eden.squaredRadiusEvolution_at_zero
attribute [local simp] Eden.squaredRadiusEvolution_zero_time



set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden
namespace Eden
theorem _root_.solution {f : ℝ → ℝ}
    (hsub : ∀ s t, 0 ≤ s → 0 ≤ t → f (s + t) ≤ f s + f t)
    {T r : ℝ} (hT : 0 ≤ T) (hr : 0 ≤ r) (m : ℕ) :
    f ((m : ℝ) * T + r) ≤ (m : ℝ) * f T + f r := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc
      f (((m + 1 : ℕ) : ℝ) * T + r) = f (T + ((m : ℝ) * T + r)) := by
        congr 1
        push_cast
        ring
      _ ≤ f T + f ((m : ℝ) * T + r) :=
        hsub _ _ hT (add_nonneg (mul_nonneg (Nat.cast_nonneg _) hT) hr)
      _ ≤ f T + ((m : ℝ) * f T + f r) := by linarith
      _ = _ := by push_cast; ring
end Eden
