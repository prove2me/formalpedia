-- Prove2me | solution 1 for Formalism.CountingSumsFrames.harmonicDecomposition_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:23:07.432639+00:00
-- url     : https://prove2.me/submissions/f3dc982b-1009-48ef-9e13-5d350b0af6fb

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_har_indep
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_decomp_exists

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
open Finset MvPolynomial
open Formalism Formalism.CountingSumsFrames
open Har2
namespace Formalism.CountingSumsFrames
theorem _root_.solution : HarDecomp := by
  unfold HarDecomp
  intro K _ _ k A B hk f hf
  obtain ⟨w, hw, hfw⟩ := decomp_exists hk A B f hf
  have e2 := Fin.sum_univ_eq_sum_range (fun j => hXY K k ^ j * w j) (min A B + 1)
  refine ⟨fun j => w j, ⟨fun j => hw j, hfw.trans e2.symm⟩, ?_⟩
  rintro v ⟨hv, hfv⟩
  funext j
  have key := har_indep hk (min A B + 1) (fun j => A - j) (fun j => B - j)
    (fun j => if h : j < min A B + 1 then v ⟨j, h⟩ - w j else 0)
    (fun j => by
      by_cases h : j < min A B + 1
      · simp only [h, ↓reduceDIte]
        exact Submodule.sub_mem _ (hv ⟨j, h⟩) (hw j)
      · simp only [h, ↓reduceDIte]
        exact Submodule.zero_mem _)
    (by
      have e1 := Fin.sum_univ_eq_sum_range
        (fun j => hXY K k ^ j * (if h : j < min A B + 1 then v ⟨j, h⟩ - w j else 0)) (min A B + 1)
      refine e1.symm.trans ?_
      simp only [Fin.is_lt, ↓reduceDIte, Fin.eta, mul_sub, Finset.sum_sub_distrib]
      rw [← hfv, e2, ← hfw, sub_self])
  have := key j j.isLt
  simp only [j.isLt, ↓reduceDIte, Fin.eta, sub_eq_zero] at this
  exact this
end Formalism.CountingSumsFrames
