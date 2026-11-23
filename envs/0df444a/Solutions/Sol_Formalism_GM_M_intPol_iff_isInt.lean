-- Prove2me | solution 1 for Formalism.GM.M.intPol_iff_isInt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:47:25.620295+00:00
-- url     : https://prove2.me/submissions/2643470f-cbde-42f0-b16d-e69ed07013cf

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SSDirect

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.M
open MvPolynomial Finset SSD
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
variable {σ : Type}
namespace Formalism.GM.M
theorem _root_.solution (f : MvPolynomial σ ℚ_[p]) : f ∈ IntPol p σ ↔ IsInt f := by
  have e1 : f ∈ IntPol p σ ↔ (f.coeffs : Set ℚ_[p]) ⊆ Set.range (algebraMap ℤ_[p] ℚ_[p]) := by
    rw [← mem_range_map_iff_coeffs_subset]
    simp only [IntPol, LinearMap.mem_range, AlgHom.toLinearMap_apply, mapAlgHom_apply, Set.mem_range]
    rfl
  rw [e1]
  constructor
  · intro h m
    by_cases hm : m ∈ f.support
    · exact h (by rw [Finset.mem_coe]; exact coeff_mem_coeffs m (mem_support_iff.mp hm))
    · rw [notMem_support_iff.mp hm]; exact ⟨0, map_zero _⟩
  · intro h c hc
    rw [Finset.mem_coe, mem_coeffs_iff] at hc
    obtain ⟨m, _, rfl⟩ := hc
    exact h m
end Formalism.GM.M
