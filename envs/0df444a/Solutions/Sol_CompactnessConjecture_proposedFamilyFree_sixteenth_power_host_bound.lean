-- Prove2me | solution 1 for CompactnessConjecture.proposedFamilyFree_sixteenth_power_host_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:02.568649+00:00
-- url     : https://prove2.me/submissions/2559d929-ba66-4c4a-aa56-a1e790343e89

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_exists_bipartite_min_degree_subgraph
import Theorems.Thm_CompactnessConjecture_familyFree_of_embedded_subgraph
import Theorems.Thm_CompactnessConjecture_proposedFamilyFree_minDegree_ambient_sixteenth_power_le

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Filter Finset SimpleGraph
open scoped Classical Topology
namespace CompactnessConjecture
theorem _root_.solution
    (n : ℕ) (host : SimpleGraph (Fin n))
    (hfree : FamilyFree proposedFamily host) :
    (host.edgeFinset.card : ℝ) ^ 16 ≤
      compactnessHostPowerConstant * (n : ℝ) ^ 21 := by
  classical
  by_cases hzero : host.edgeFinset.card = 0
  · simp only [hzero, Nat.cast_zero, zero_pow (by norm_num : 16 ≠ 0)]
    unfold compactnessHostPowerConstant compactnessDegreePowerConstant
    positivity
  · have hpositive : 0 < host.edgeFinset.card :=
      Nat.pos_of_ne_zero hzero
    obtain ⟨N, B, f, hN, hNn, hBbip, hmap, hminimum,
      _hminimum_pointwise⟩ :=
      exists_bipartite_min_degree_subgraph host hpositive
    have hn : 0 < n := by
      omega
    have hBfree : FamilyFree proposedFamily B :=
      familyFree_of_embedded_subgraph host B f hmap hfree
    let d : ℕ := B.minDegree
    have hdegree : ∀ v : Fin N, d ≤ B.degree v := by
      intro v
      exact B.minDegree_le_degree v
    have hminimumNat :
        host.edgeFinset.card ≤ 2 * n * d := by
      simpa only [d] using hminimum
    have hminimumReal :
        (host.edgeFinset.card : ℝ) ≤
          2 * (n : ℝ) * (d : ℝ) := by
      exact_mod_cast hminimumNat
    have hdPower := proposedFamilyFree_minDegree_ambient_sixteenth_power_le
      B hN hn hNn hBfree hBbip d hdegree
    calc
      (host.edgeFinset.card : ℝ) ^ 16 ≤
          (2 * (n : ℝ) * (d : ℝ)) ^ 16 := by
        gcongr
      _ = (2 : ℝ) ^ 16 * (n : ℝ) ^ 16 * (d : ℝ) ^ 16 := by
        ring
      _ ≤ (2 : ℝ) ^ 16 * (n : ℝ) ^ 16 *
          (compactnessDegreePowerConstant * (n : ℝ) ^ 5) := by
        gcongr
      _ = compactnessHostPowerConstant * (n : ℝ) ^ 21 := by
        unfold compactnessHostPowerConstant
        ring
end CompactnessConjecture
