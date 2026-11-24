-- Prove2me | solution 1 for Formalism.CohomologicalDescent.WorkedExample.append_strictAnti
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:03:22.412863+00:00
-- url     : https://prove2.me/submissions/b8c386af-3fbc-4be3-b369-1684752612ab

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_MultiplicityZeroThickEmbedding
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WorkedExample

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.WorkedExample
open Formalism.CohomologicalDescent
namespace Formalism.CohomologicalDescent.WorkedExample
theorem _root_.solution {m n : ℕ} (f : Fin m → ℝ) (g : Fin n → ℝ) (hf : StrictAnti f)
    (hg : StrictAnti g) (hfg : ∀ i j, g j < f i) : StrictAnti (Fin.append f g) := by
  intro i j hij
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j =>
      simp only [Fin.append_left]
      rw [Fin.lt_def] at hij
      exact hf (by rw [Fin.lt_def]; simpa only [Fin.coe_castAdd] using hij)
    | right j =>
      simp only [Fin.append_left, Fin.append_right]
      exact hfg i j
  | right i =>
    induction j using Fin.addCases with
    | left j =>
      exfalso
      rw [Fin.lt_def] at hij
      simp only [Fin.coe_castAdd, Fin.coe_natAdd] at hij
      have := j.isLt
      omega
    | right j =>
      simp only [Fin.append_right]
      rw [Fin.lt_def] at hij
      exact hg (by rw [Fin.lt_def]; simpa only [Fin.coe_natAdd, Nat.add_lt_add_iff_left] using hij)
end Formalism.CohomologicalDescent.WorkedExample
