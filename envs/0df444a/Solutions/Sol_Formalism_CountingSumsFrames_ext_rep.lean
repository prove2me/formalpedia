-- Prove2me | solution 1 for Formalism.CountingSumsFrames.ext_rep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:50:47.130816+00:00
-- url     : https://prove2.me/submissions/696a95a0-1e1a-43ea-b02a-d9f8b766d1ab

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
import Theorems.Thm_Formalism_CountingSumsFrames_ext_mul
import Theorems.Thm_Formalism_CountingSumsFrames_isF_of_polLz
import Theorems.Thm_Formalism_CountingSumsFrames_isL_monomial_of
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_rep_span


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames
theorem _root_.solution (L : Letters N) (j0 : ℕ) (U : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
    (hU : U ≤ Pol p r (Lz L j0)) {x : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hx : x ∈ Submodule.span ℚ_[p] {x | ∃ g ∈ U,
      ∃ q ∈ MvPolynomial.supported ℚ_[p] {v : Fin N × Fin r | j0 ≤ (v.1 : ℕ)}, x = g * q}) :
    ∃ s : Finset (Fin N × Fin r →₀ ℕ), ∃ a : (Fin N × Fin r →₀ ℕ) → MvPolynomial (Fin N × Fin r) ℚ_[p],
      (∀ b, a b ∈ U) ∧ x = ∑ b ∈ s, a b * monomial b 1 ∧
      ∀ a' : (Fin N × Fin r →₀ ℕ) → MvPolynomial (Fin N × Fin r) ℚ_[p], (∀ b, a' b ∈ Pol p r (Lz L j0)) →
        ∀ φ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p],
        ext (fsj N r j0) φ (∑ b ∈ s, a' b * monomial b 1) = ∑ b ∈ s, φ (a' b) * monomial b 1 := by
  obtain ⟨s, a, hs, ha, hxs⟩ := rep_span U j0 hx
  refine ⟨s, a, ha, hxs, fun a' ha' φ => ?_⟩
  rw [map_sum]
  exact Finset.sum_congr rfl fun b hb => ext_mul _ φ (isF_of_polLz L j0 (ha' b)) (isL_monomial_of j0 b (hs b hb) 1)
end Formalism.CountingSumsFrames
