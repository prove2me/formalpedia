-- Prove2me | solution 1 for Formalism.CohomologicalDescent.FrobeniusPeriodChange.weight_lemma_from_inputs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:20:26.766132+00:00
-- url     : https://prove2.me/submissions/a1e14296-7ef8-4a43-9aef-868238754d5a

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaWFromLattice
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_alpha_bounds_hold
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_weight_properties_of_inputs
import Theorems.Thm_Formalism_CohomologicalDescent_twisted_block_bounds


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
theorem _root_.solution : LemmaWFromInputs := by
  intro ι _ σ l h t n _ O F _ _ _ _ _ W u c U' bot kap hl2 hW
  classical
  have hα := alpha_bounds_hold ι σ l h t n O F W u c U' _ kap hl2 hW
  have hU := hW.1.2.1
  have hwt := hW.1.2.2.1
  have hmain : ∀ cc : ι → ℕ,
      (∀ i (J : Finset (Fin n)), J.card = t → (cc i : ℤ) ≤ ∑ j ∈ J, U' i j) → _ :=
    fun cc hcc => twisted_block_bounds ι σ l h t n F (W.toWData l c σ) U' bot kap cc Fact.out
      (weight_properties_of_inputs ι σ l h t n O F W u c U' bot kap cc hl2 hW hcc) hwt hα
  have h0 := hmain (fun _ => 0) (fun i J _ => by
    simpa using Finset.sum_nonneg fun j _ => (hU i j).1)
  refine ⟨h0.1, h0.2.1, ?_⟩
  intro i
  by_contra hcon
  push Not at hcon
  have hA0 : 0 ≤ ∑ s : Fin t, (bot i + ((s : ℕ) : ℤ) + (l : ℤ) * kap (σ i) s - kap i s) :=
    Finset.sum_nonneg fun s _ => by have := (hα i s).1; linarith
  generalize hA : ∑ s : Fin t, (bot i + ((s : ℕ) : ℤ) + (l : ℤ) * kap (σ i) s - kap i s) = A at *
  have h1 := (hmain (fun i' => if i' = i then A.toNat + 1 else 0) (by
    intro i' J hJ
    by_cases hi : i' = i
    · subst hi
      have := hcon J hJ
      simp only [if_true]
      push_cast
      rw [Int.toNat_of_nonneg hA0]
      omega
    · simpa [hi] using Finset.sum_nonneg fun j _ => (hU i' j).1)).2.2 i
  rw [hA] at h1
  simp only [if_true] at h1
  push_cast at h1
  rw [Int.toNat_of_nonneg hA0] at h1
  omega
end Formalism.CohomologicalDescent.FrobeniusPeriodChange
