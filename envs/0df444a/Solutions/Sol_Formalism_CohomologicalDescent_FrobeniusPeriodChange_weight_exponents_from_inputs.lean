-- Prove2me | solution 1 for Formalism.CohomologicalDescent.FrobeniusPeriodChange.weight_exponents_from_inputs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:45:32.120809+00:00
-- url     : https://prove2.me/submissions/6b24fd73-d7c0-4e06-92fa-7e786668fba3

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaWFromLattice
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_alpha_bounds_hold
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_weight_properties_of_inputs
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_sum_tail_le_sum_of_antitone
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_card_filter_le_val_eq_sub
import Theorems.Thm_Formalism_CohomologicalDescent_weightExchangeFull_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.FrobeniusPeriodChange
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
variable {ι : Type} {t n : ℕ} {O F : Type} [CommRing O] [Field F]
namespace Formalism.CohomologicalDescent.FrobeniusPeriodChange
theorem _root_.solution : WEFromInputs := by
  intro ι _ σ k j t q l h _ O F _ _ _ _ _ W u c U U' bot cst kap τ hl2 hsmall hW hU hU' hblock hlink
    hU0 hsum hrows
  classical
  have hα := alpha_bounds_hold ι σ l h t _ O F W u c U' _ kap hl2 hW
  have hH1 := hW.1.2.1
  have hwt := hW.1.2.2.1
  have hT0 : 0 ≤ ∑ a ∈ Finset.univ.filter (fun a : Fin (k + j + t + q) => k + j + q ≤ (a : ℕ)),
      U' τ a := Finset.sum_nonneg fun a _ => (hH1 τ a).1
  have hcard := card_filter_le_val_eq_sub (k + j + t + q) (k + j + q) (by omega)
  refine weightExchangeFull_holds ι σ k j t q l h F (W.toWData l c σ) U U' bot cst kap
    (fun i => if i = τ then (∑ a ∈ Finset.univ.filter
      (fun a : Fin (k + j + t + q) => k + j + q ≤ (a : ℕ)), U' τ a).toNat else 0) τ Fact.out hsmall
    (weight_properties_of_inputs ι σ l h t _ O F W u c U' bot kap _ hl2 hW ?_) hwt hα hU hU' hblock hlink
    hU0 (hH1 τ) hsum hrows ?_
  · intro i J hJ
    by_cases hi : i = τ
    · subst hi
      simp only [if_true]
      rw [Int.toNat_of_nonneg hT0]
      exact sum_tail_le_sum_of_antitone (U' i) (hU' i).antitone _ J (by rw [hJ, hcard]; omega)
    · simpa [hi] using Finset.sum_nonneg fun a _ => (hH1 i a).1
  · simp only [if_true]
    rw [Int.toNat_of_nonneg hT0]
end Formalism.CohomologicalDescent.FrobeniusPeriodChange
