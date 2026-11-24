-- Prove2me | solution 1 for Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates.nCard
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:38.515104+00:00
-- url     : https://prove2.me/submissions/21e9a80b-f269-4a61-815e-0bcdbb868232

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_QuadraticFormLowerBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HilbertSchmidtHalfBound
import Theorems.Thm_Formalism_HermitianLattices_CumulantEstimateDefs_CumulantEstimates_cardUni
import Theorems.Thm_Formalism_HermitianLattices_CumulantEstimateDefs_CumulantEstimates_countFree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.CumulantEstimateDefs Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates
open Finset
namespace Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates
theorem _root_.solution : Formalism.HermitianLattices.CumulantEstimateDefs.UnipotentRadicalCard := by
  unfold Formalism.HermitianLattices.CumulantEstimateDefs.UnipotentRadicalCard
  intro F _ _ _ k m hm hev
  obtain ⟨s, rfl⟩ := hev
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  dsimp only
  have e1 : (t + 1 + (t + 1)) / 2 - 1 = t := by omega
  have e2 : k + (t + 1 + (t + 1)) - 1 = t + (k + 1) + t := by omega
  rw [e1, e2]
  refine ⟨rfl, ?_⟩
  have key := cardUni F (t + (k + 1) + t) (fun i => bb k t i.val)
  have cf := countFree k t (t + (k + 1) + t) rfl
  simp only [bb] at key cf
  rw [key, cf]
  congr 1
  have h : (t + (k + 1) + t) ^ 2 = (k + 1) ^ 2 + 2 * (t * (2 * k + 1 + 2 * t)) + 2 * t := by ring
  rw [h]
  generalize (k + 1) ^ 2 = A
  generalize t * (2 * k + 1 + 2 * t) = B
  omega
end Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates
