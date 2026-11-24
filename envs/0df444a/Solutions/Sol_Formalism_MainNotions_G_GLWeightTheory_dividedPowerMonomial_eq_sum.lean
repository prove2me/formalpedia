-- Prove2me | solution 1 for Formalism.MainNotions.G.GLWeightTheory.dividedPowerMonomial_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:40:11.569158+00:00
-- url     : https://prove2.me/submissions/bd1b9d89-ec6c-4e01-93ce-e50cb71dee11

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RootWeights_MatrixSubstTransvectionMonomialOfFixed
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RootWeights_SumFinsuppAntidiagEqSumPiFinset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory
open Formalism.MainNotions.G
variable {B : Type*} [CommRing B] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
  (a b : Fin n) (t : B) (m : ι × Fin n →₀ ℕ)
open Classical
namespace Formalism.MainNotions.G.GLWeightTheory
theorem _root_.solution (k : ℕ) :
    divPowMono B LL S a b k m = ∑ f ∈ Finset.finsuppAntidiag (Finset.univ.filter (· ∈ S)) k,
      monomial (shiftedExponent LL a b m (⇑f)) (rootShiftCoefficient B LL a b m (⇑f)) := by
  have sum_support_single_eq_lemma {σ ι : Type _} [Fintype ι] (f : ι →₀ ℕ) (g : ι → σ) :
      ∑ l ∈ f.support, Finsupp.single (g l) (f l) = ∑ l, Finsupp.single (g l) (f l) :=
    Finset.sum_subset (Finset.subset_univ _) fun l _ hl => by
      have h0 : f l = 0 := by simpa using hl
      rw [h0, Finsupp.single_zero]
  simp only [Formalism.MainNotions.G.divPowMono, shiftedExponent, rootShiftCoefficient, sourceVar, targetVar]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [sum_support_single_eq_lemma f, sum_support_single_eq_lemma f, Finset.prod_subset (Finset.subset_univ f.support)]
  intro l _ hl
  have h0 : f l = 0 := by simpa using hl
  simp [h0]
end Formalism.MainNotions.G.GLWeightTheory
