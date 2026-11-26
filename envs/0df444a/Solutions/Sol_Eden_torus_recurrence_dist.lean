-- Prove2me | solution 1 for Eden.torus_recurrence_dist
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:55:45.110185+00:00
-- url     : https://prove2.me/submissions/fec8eae9-6b5a-40a8-b2fe-a3dd5ecd6f2d

import Definitions.Def_Eden_TorusAngles
import Definitions.Def_Eden_DerivativeFrames
import Definitions.Def_Eden_Uniqueness
import Mathlib.Topology.MetricSpace.Cauchy
import Definitions.Def_Eden_TorusRecurrence
import Theorems.Thm_Eden_dist_evolution_torus
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_diagonalLinear_apply
import Theorems.Thm_Eden_evolution_add
import Theorems.Thm_Eden_evolution_origin
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_isCompact_torus
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_planarX_origin
import Theorems.Thm_Eden_planarX_zero_time
import Theorems.Thm_Eden_planarY_origin
import Theorems.Thm_Eden_planarY_zero_time
import Theorems.Thm_Eden_radialAmplitude_zero_time
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_radialDiscriminant_at_zero
import Theorems.Thm_Eden_radialDiscriminant_zero_time
import Theorems.Thm_Eden_squaredRadiusEvolution_at_one
import Theorems.Thm_Eden_squaredRadiusEvolution_at_two
import Theorems.Thm_Eden_squaredRadiusEvolution_at_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
import Theorems.Thm_Eden_torus_invariant_all_real
attribute [local simp] Eden.amplitudeSq_at_zero
attribute [local simp] Eden.amplitudeSq_zero_time
attribute [local simp] Eden.blockRotation_apply
attribute [local simp] Eden.diagonalLinear_apply
attribute [local simp] Eden.evolution_origin
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
attribute [local simp] Eden.squaredRadiusEvolution_at_one
attribute [local simp] Eden.squaredRadiusEvolution_at_two
attribute [local simp] Eden.squaredRadiusEvolution_at_zero
attribute [local simp] Eden.squaredRadiusEvolution_zero_time



set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) {p : PhaseSpace} (hp : p ∈ torus)
    {ε : ℝ} (hε : 0 < ε) (R : ℝ) :
    ∃ t : ℝ, R < t ∧ 0 ≤ t ∧ dist (evolution c t p) p < ε := by
  obtain ⟨a, ha, φ, hφ, hlim⟩ := isCompact_torus.tendsto_subseq
    (fun n : ℕ => torus_invariant_all_real c (n : ℝ) hp)
  have hC := hlim.cauchySeq
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hC ε hε
  obtain ⟨K, hK⟩ := exists_nat_gt (max R 0 + (φ N : ℝ))
  let M : ℕ := N + K
  have hNM : N ≤ M := Nat.le_add_right N K
  have hKM : K ≤ M := Nat.le_add_left K N
  have hKφ : (K : ℝ) ≤ (φ M : ℝ) := by exact_mod_cast hKM.trans (hφ.id_le M)
  have hφNM : (φ N : ℝ) ≤ (φ M : ℝ) := by exact_mod_cast hφ.monotone hNM
  let t : ℝ := (φ M : ℝ) - (φ N : ℝ)
  have ht : 0 ≤ t := sub_nonneg.mpr hφNM
  have htR : R < t := by dsimp [t]; linarith [le_max_left R 0]
  refine ⟨t, htR, ht, ?_⟩
  have hadd : evolution c (φ M : ℝ) p =
      evolution c (φ N : ℝ) (evolution c t p) := by
    have he : (φ M : ℝ) = t + (φ N : ℝ) := by dsimp [t]; ring
    conv_lhs => rw [he]
    exact evolution_add c ht (Nat.cast_nonneg _) p
  have hd := dist_evolution_torus c (φ N : ℝ) (torus_invariant_all_real c t hp) hp
  rw [← hadd] at hd
  rw [← hd]
  exact hN M hNM N le_rfl
end Eden
