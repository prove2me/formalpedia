-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas.mono_eq_of_counts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:11:41.8504+00:00
-- url     : https://prove2.me/submissions/62a0dbfe-43f1-42ac-960d-779848d6b366

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Lemmata_GeneralBFactRightFurther_Imports
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LinearIndependentOfLead
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_leadingTermLemmas_mono_le_iff

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
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas
variable {n C : ℕ}
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas
theorem _root_.solution (f g : Fin C → ℕ) (hf : Monotone f) (hg : Monotone g) (hfn : ∀ c, f c ≤ n)
    (hgn : ∀ c, g c ≤ n)
    (h : ∀ v < n, (univ.filter fun c => f c = v).card = (univ.filter fun c => g c = v).card) : f = g := by
  have hiff : ∀ v < n, ∀ c, f c ≤ v ↔ g c ≤ v := by
    intro v hv c
    rw [mono_le_iff f hf, mono_le_iff g hg]
    rw [Finset.sum_congr rfl fun w hw => h w (by have := Finset.mem_range.1 hw; omega)]
  funext c
  have h1 := hfn c
  have h2 := hgn c
  by_cases hfc : f c < n
  · have h3 := (hiff (f c) hfc c).1 le_rfl
    have h4 := (hiff (g c) (by omega) c).2 le_rfl
    omega
  · by_cases hgc : g c < n
    · have h4 := (hiff (g c) hgc c).2 le_rfl
      omega
    · omega
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas
