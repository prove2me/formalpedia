-- Prove2me | solution 1 for Eden.planar_surjective_on_disc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:30:23.779022+00:00
-- url     : https://prove2.me/submissions/de3dc438-dcf3-4312-a582-4d6bd0a2e2f0

import Definitions.Def_Eden_InvariantSets
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_Eden_StrictInvariance
import Theorems.Thm_Eden_squaredRadiusEvolution_surjOn
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_mul_amplitudeSq
import Theorems.Thm_Eden_planarAmplitude_pos
import Theorems.Thm_Eden_planarAmplitude_sq
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_planarX_origin
import Theorems.Thm_Eden_planarX_zero_time
import Theorems.Thm_Eden_planarY_origin
import Theorems.Thm_Eden_planarY_zero_time
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_radialDiscriminant_at_zero
import Theorems.Thm_Eden_radialDiscriminant_zero_time
import Theorems.Thm_Eden_squaredRadiusEvolution_at_one
import Theorems.Thm_Eden_squaredRadiusEvolution_at_two
import Theorems.Thm_Eden_squaredRadiusEvolution_at_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
attribute [local simp] Eden.amplitudeSq_at_zero
attribute [local simp] Eden.amplitudeSq_zero_time
attribute [local simp] Eden.evolution_zero_time
attribute [local simp] Eden.planarAmplitude_zero_time
attribute [local simp] Eden.planarX_origin
attribute [local simp] Eden.planarX_zero_time
attribute [local simp] Eden.planarY_origin
attribute [local simp] Eden.planarY_zero_time
attribute [local simp] Eden.radialDiscriminant_at_two
attribute [local simp] Eden.radialDiscriminant_at_zero
attribute [local simp] Eden.radialDiscriminant_zero_time
attribute [local simp] Eden.squaredRadiusEvolution_at_one
attribute [local simp] Eden.squaredRadiusEvolution_at_two
attribute [local simp] Eden.squaredRadiusEvolution_at_zero
attribute [local simp] Eden.squaredRadiusEvolution_zero_time



set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution (Ω : ℝ) {t x y : ℝ} (ht : 0 ≤ t)
    (hxy : x ^ 2 + y ^ 2 ≤ 2) :
    ∃ u v : ℝ, u ^ 2 + v ^ 2 ≤ 2 ∧ planarX Ω t u v = x ∧ planarY Ω t u v = y := by
  obtain ⟨s, hs, heq⟩ := squaredRadiusEvolution_surjOn ht
    ⟨add_nonneg (sq_nonneg x) (sq_nonneg y), hxy⟩
  let g := planarAmplitude t s
  let a := Real.cos (Ω * t)
  let b := Real.sin (Ω * t)
  have hg : g ≠ 0 := ne_of_gt (planarAmplitude_pos ht hs.1)
  have hab : a ^ 2 + b ^ 2 = 1 := by
    dsimp [a, b]
    nlinarith [Real.sin_sq_add_cos_sq (Ω * t)]
  have hsg : s * g ^ 2 = x ^ 2 + y ^ 2 := by
    dsimp [g]
    rw [planarAmplitude_sq ht hs.1, mul_amplitudeSq ht, heq]
  let u := (x * a + y * b) / g
  let v := (-x * b + y * a) / g
  have huv : u ^ 2 + v ^ 2 = s := by
    dsimp [u, v]
    field_simp
    nlinarith [congrArg (fun z : ℝ => (x ^ 2 + y ^ 2) * z) hab]
  refine ⟨u, v, huv ▸ hs.2, ?_, ?_⟩
  · unfold planarX
    rw [huv]
    change g * (u * a - v * b) = x
    dsimp [u, v]
    field_simp
    nlinarith [congrArg (fun z : ℝ => x * z) hab]
  · unfold planarY
    rw [huv]
    change g * (u * b + v * a) = y
    dsimp [u, v]
    field_simp
    nlinarith [congrArg (fun z : ℝ => y * z) hab]
end Eden
