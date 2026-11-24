-- Prove2me | solution 1 for Formalism.CohomologicalDescent.WorkedExample.linked_all_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:20:05.908857+00:00
-- url     : https://prove2.me/submissions/33ef48dc-8083-4d0c-8804-d1b082b59fb7

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_MultiplicityZeroThickEmbedding
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WorkedExample
import Theorems.Thm_Formalism_CohomologicalDescent_WorkedExample_linkage_reflection_holds
import Theorems.Thm_Formalism_CohomologicalDescent_WorkedExample_prod_X_add_C_shift_eq

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
theorem _root_.solution : LinkedAll := by
  intro ι N D σ h t F _ cst hR hL
  obtain ⟨hinv, _, hΦ, hU, hU', hbot⟩ := hR
  have hc : ∀ i ∈ D.Φ, StrictAnti (D.U (D.cc i)) ∧ StrictAnti (D.U' (D.cc i)) ∧
      (∀ s : Fin t, ∃ a, D.U (D.cc i) a = D.bot (D.cc i) + ((s : ℕ) : ℤ)) ∧
      (∏ a, (Polynomial.X + Polynomial.C (((D.U (D.cc i) a + 0 : ℤ)) : F))) =
        ∏ a, (Polynomial.X + Polynomial.C (((D.U' (D.cc i) a + 0 : ℤ)) : F)) := by
    intro i hi
    obtain ⟨h1, h2, h3, h4⟩ := hL i hi
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b hab
      rw [hU, hU]
      have := h1 (Fin.rev_lt_rev.mpr hab)
      omega
    · intro a b hab
      rw [hU', hU']
      have := h2 (Fin.rev_lt_rev.mpr hab)
      omega
    · intro s
      obtain ⟨a, ha⟩ := h3 (Fin.rev s)
      refine ⟨Fin.rev a, ?_⟩
      rw [hU, Fin.rev_rev, ha, hbot]
      have e1 : ((Fin.rev s : Fin t) : ℕ) = t - (s + 1) := Fin.val_rev s
      have e2 := s.isLt
      omega
    · have e := linkage_reflection_holds F N (D.U i) (D.U' i) (cst i) 0 h h4
      have r1 := Equiv.prod_comp Fin.revPerm
        (fun a => (Polynomial.X + Polynomial.C ((((h : ℤ) - D.U i a + 0 : ℤ)) : F)))
      have r2 := Equiv.prod_comp Fin.revPerm
        (fun a => (Polynomial.X + Polynomial.C ((((h : ℤ) - D.U' i a + 0 : ℤ)) : F)))
      simp only [Fin.revPerm_apply] at r1 r2
      simp only [hU, hU']
      rw [r1, r2, e]
  intro i
  rcases hΦ i with hi | hi
  · obtain ⟨h1, h2, h3, h4⟩ := hL i hi
    exact ⟨h1, h2, h3, prod_X_add_C_shift_eq _ _ _ _ h4⟩
  · have := hc (D.cc i) hi
    rwa [hinv i] at this
end Formalism.CohomologicalDescent.WorkedExample
