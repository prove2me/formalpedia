-- Prove2me | solution 1 for Formalism.F.discreteTopology_span_range_of_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:22:34.787452+00:00
-- url     : https://prove2.me/submissions/10225f13-356d-495d-b92b-2f0f19c5fc5d

import Definitions.Def_Formalism_LatticeSlopes_Statement
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolEqGram
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DegQuot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.F
namespace Formalism.F
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι] (c : ι → E) (hc : LinearIndependent ℝ c) :
    DiscreteTopology (span ℤ (Set.range c)) := by
  classical
  let φ : (ι → ℝ) →ₗ[ℝ] E := Fintype.linearCombination ℝ c
  have hker : LinearMap.ker φ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro r hr
    funext i
    exact Fintype.linearIndependent_iff.1 hc r
      (by rw [← Fintype.linearCombination_apply]; exact hr) i
  obtain ⟨K, hK, hφ⟩ := LinearMap.exists_antilipschitzWith φ hker
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have key : ∀ x ∈ Submodule.span ℤ (Set.range c), x ≠ 0 → (K : ℝ)⁻¹ ≤ ‖x‖ := by
    intro x hx hx0
    obtain ⟨n, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hx
    have hφn : φ (fun i => (n i : ℝ)) = ∑ i, n i • c i := by
      simp only [φ, Fintype.linearCombination_apply]
      exact Finset.sum_congr rfl fun i _ => Int.cast_smul_eq_zsmul ℝ (n i) (c i)
    obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      apply hx0
      simp [hcon]
    have h1 : (1 : ℝ) ≤ ‖(fun i => (n i : ℝ))‖ := by
      calc (1 : ℝ) ≤ |(n i : ℝ)| := by exact_mod_cast Int.one_le_abs hi
        _ = ‖(n i : ℝ)‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖(fun i => (n i : ℝ))‖ := norm_le_pi_norm (fun i => (n i : ℝ)) i
    have h2 := hφ.le_mul_dist (fun i => (n i : ℝ)) 0
    rw [dist_zero_right, map_zero, dist_zero_right, hφn] at h2
    rw [inv_eq_one_div, div_le_iff₀ hKpos]
    nlinarith
  have hε : (0 : ℝ) < (K : ℝ)⁻¹ := inv_pos.mpr hKpos
  apply discreteTopology_of_isOpen_singleton_zero
  refine isOpen_induced_iff.mpr ⟨Metric.ball 0 (K : ℝ)⁻¹, Metric.isOpen_ball, ?_⟩
  ext y
  rw [Set.mem_preimage, Metric.mem_ball, dist_zero_right, Set.mem_singleton_iff]
  constructor
  · intro h
    by_contra hne
    have hy : (y : E) ≠ 0 := fun h0 => hne (Subtype.ext h0)
    exact absurd (key y y.2 hy) (not_le.mpr h)
  · intro h
    rw [h]
    simpa using hε
end Formalism.F
