-- Prove2me | solution 1 for Formalism.DivisionValues.PlaceSumConjugation.sum_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:57:03.212805+00:00
-- url     : https://prove2.me/submissions/10bdf776-e13d-4847-90b0-0a3826b0b6f9

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_Complement2Normaliser
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondComplementParameterBounds
import Theorems.Thm_Formalism_DivisionValues_PlaceSumConjugation_plOver_conj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module NumberField IsDedekindDomain Finset
noncomputable section
namespace Formalism.DivisionValues
namespace PlaceSumConjugation
section Places
variable {K : Type} [Field K] [NumberField K]
end Places
section Star
variable {K : Type} [Field K] [NumberField K] [StarRing K]
private theorem conjPl_conjPl_lemma {K : Type} [Field K] [NumberField K] [StarRing K]
    (w : HeightOneSpectrum (𝓞 K)) : conjPl (conjPl w) = w := by
  have hinv : ∀ x : 𝓞 K, cO K (cO K x) = x := by
    intro x
    apply RingOfIntegers.ext
    first
      | (simp [cO]; done)
      | (change star (star (x : K)) = (x : K); exact star_star _)
      | (simp [cO, RingOfIntegers.mapRingEquiv]; done)
  have key : (w.asIdeal.map (cO K)).map (cO K) = w.asIdeal := by
    ext x
    simp only [Ideal.mem_map_of_equiv]
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      rw [hinv]; exact hz
    · intro hx
      exact ⟨cO K x, ⟨x, hx, rfl⟩, hinv x⟩
  exact HeightOneSpectrum.ext key
end Star
end PlaceSumConjugation
open PlaceSumConjugation
end Formalism.DivisionValues
end
end

set_option autoImplicit false
open Module NumberField IsDedekindDomain Finset
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.PlaceSumConjugation
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.DivisionValues.PlaceSumConjugation
theorem _root_.solution {g : ℕ} (hS : {w : HeightOneSpectrum (𝓞 K) | PlOver g w}.Finite)
    (f : HeightOneSpectrum (𝓞 K) → ℝ) :
    ∑ w ∈ hS.toFinset, f (conjPl w) = ∑ w ∈ hS.toFinset, f w := by
  apply Finset.sum_nbij' conjPl conjPl
  · intro w hw
    simp only [Set.Finite.coe_toFinset, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hw ⊢
    exact (plOver_conj g w).2 hw
  · intro w hw
    simp only [Set.Finite.coe_toFinset, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hw ⊢
    exact (plOver_conj g w).2 hw
  · intro w _; exact conjPl_conjPl_lemma w
  · intro w _; exact conjPl_conjPl_lemma w
  · intro w _; rfl
end Formalism.DivisionValues.PlaceSumConjugation
