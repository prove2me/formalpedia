-- Prove2me | solution 1 for Formalism.CountingSumsFrames.change_lattice_good_rank
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:44:18.917795+00:00
-- url     : https://prove2.me/submissions/25f8080a-14ae-4337-8cd1-11b72fda7fff

import Definitions.Def_Formalism_PolynomialDimension_DigitSumValuationBound
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentBoundThreeHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution : ChangeLatticeGoodRank := by
  intro O _ _ _ π _ L L' _ _ _ _ _ _ _ _ f f' φ c y n D hc hφ hgood
  obtain ⟨u, v, huv⟩ := hgood
  obtain ⟨k₀, hk₀⟩ := hc
  refine ⟨φ ∘ₗ u, (k₀ * k₀) • (v ∘ₗ φ.dualMap), ?_⟩
  have hdual : ∀ x, φ.dualMap (f' (φ (u x))) = (c * c) • f (u x) := by
    intro x
    refine LinearMap.ext fun z => ?_
    simp [LinearMap.dualMap_apply, hφ]
  apply LinearMap.ext
  intro x
  have h1 := LinearMap.congr_fun huv x
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply] at h1 ⊢
  rw [hdual, map_smul, h1, smul_smul, smul_smul]
  congr 1
  have e : π ^ (D + 2 * y) = π ^ D * π ^ y * π ^ y := by ring
  rw [e, hk₀]
  ring
end Formalism.CountingSumsFrames
