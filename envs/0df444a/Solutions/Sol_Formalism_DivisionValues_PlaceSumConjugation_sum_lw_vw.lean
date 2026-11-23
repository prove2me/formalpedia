-- Prove2me | solution 1 for Formalism.DivisionValues.PlaceSumConjugation.sum_lw_vw
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:32:04.712795+00:00
-- url     : https://prove2.me/submissions/50571b4a-b2fb-4d3f-b258-06871777a6c5

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_Complement2Normaliser
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondComplementParameterBounds
import Theorems.Thm_P2M_Formalism_DivisionValues_PlaceSumConjugation_natCast_ne_zero__72e1bc708076
import Theorems.Thm_Formalism_DivisionValues_PlaceSumConjugation_vw_nat_nonneg
import Theorems.Thm_P2M_Formalism_DivisionValues_prod_formula__ad6919c95c2d


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Finset
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.PlaceSumConjugation
namespace Formalism.DivisionValues.PlaceSumConjugation
theorem _root_.solution (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] {g : ℕ}
    (hg : 0 < g) (hS : {w : HeightOneSpectrum (𝓞 K) | PlOver g w}.Finite) :
    ∑ w ∈ hS.toFinset, lw w * (vw w (g : K) : ℝ) = Real.log g := by
  obtain ⟨_, h⟩ := prod_formula' K (g : K) (natCast_ne_zero' hg)
  have h1 : ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * (vw w (g : K) : ℝ) =
      ∑ w ∈ hS.toFinset, lw w * (vw w (g : K) : ℝ) := by
    apply finsum_eq_sum_of_support_subset
    intro w hw
    simp only [Set.Finite.coe_toFinset, Set.mem_ofPred_eq]
    rw [Function.mem_support] at hw
    have h0 : vw w (g : K) ≠ 0 := by
      intro h0
      apply hw
      rw [h0]
      simp
    have := vw_nat_nonneg (K := K) g w
    unfold PlOver
    omega
  rw [← h1, ← h]
  have hn : (finrank ℚ K : ℝ) = 2 * (Fintype.card (InfinitePlace K) : ℝ) := by
    have h2 := IsTotallyComplex.finrank (K := K)
    have h3 : InfinitePlace.nrComplexPlaces K = Fintype.card (InfinitePlace K) := by
      have := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K
      rw [nrRealPlaces_eq_zero_iff.mpr inferInstance] at this
      omega
    rw [h2, h3]
    push_cast
    ring
  have hc : (0 : ℝ) < Fintype.card (InfinitePlace K) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (InfinitePlace K))
  have hnorm : ∀ v : InfinitePlace K, ‖v.embedding (g : K)‖ = (g : ℝ) := by
    intro v
    rw [map_natCast]
    simp
  simp only [hnorm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hn]
  field_simp
end Formalism.DivisionValues.PlaceSumConjugation
