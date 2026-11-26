-- Prove2me | solution 1 for Eden.real_subadditive_div_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:49:09.300343+00:00
-- url     : https://prove2.me/submissions/3fc16a16-7533-4bb9-8c4d-e53c716d9c25

import Definitions.Def_Eden_GlobalGrowth
import Mathlib.Analysis.Subadditive
import Mathlib.Algebra.Order.Floor.Semiring
import Definitions.Def_Eden_RealSubadditive
import Theorems.Thm_Eden_real_subadditive_mul_add_le
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
theorem _root_.solution {f : ℝ → ℝ} {C : ℝ}
    (hsub : ∀ s t, 0 ≤ s → 0 ≤ t → f (s + t) ≤ f s + f t)
    (hC : 0 ≤ C) (hbound : ∀ t, 0 ≤ t → |f t| ≤ C * t)
    {T t : ℝ} (hT : 0 < T) (ht : 0 < t) :
    f t / t ≤ f T / T + (C + |f T / T|) * T / t := by
  let m : ℕ := ⌊t / T⌋₊
  let r : ℝ := t - (m : ℝ) * T
  have hm : (m : ℝ) * T ≤ t :=
    (le_div_iff₀ hT).mp (Nat.floor_le (div_nonneg ht.le hT.le))
  have hmt : t < ((m : ℝ) + 1) * T :=
    (div_lt_iff₀ hT).mp (Nat.lt_floor_add_one (t / T))
  have hr : 0 ≤ r := sub_nonneg.mpr hm
  have hrT : r ≤ T := by dsimp [r]; linarith
  have heq : (m : ℝ) * T + r = t := by dsimp [r]; ring
  have hs := real_subadditive_mul_add_le hsub hT.le hr m
  rw [heq] at hs
  have hb : f r ≤ C * r := (le_abs_self _).trans (hbound r hr)
  have ha : T * (f T / T) = f T := mul_div_cancel₀ _ hT.ne'
  have he : r * (C - f T / T) ≤ T * (C + |f T / T|) := by
    calc
      _ ≤ r * (C + |f T / T|) :=
        mul_le_mul_of_nonneg_left (by linarith [neg_le_abs (f T / T)]) hr
      _ ≤ _ := mul_le_mul_of_nonneg_right hrT (add_nonneg hC (abs_nonneg _))
  apply (div_le_iff₀ ht).2
  have hcancel : ((C + |f T / T|) * T / t) * t =
      (C + |f T / T|) * T := div_mul_cancel₀ _ ht.ne'
  have hmul := congrArg (fun x : ℝ => (m : ℝ) * x) ha
  dsimp only [r] at hs hb he
  nlinarith
end Eden
