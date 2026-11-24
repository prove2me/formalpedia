-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.ld_sym_mu
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:53:04.204304+00:00
-- url     : https://prove2.me/submissions/f290b138-c575-4add-af0f-27a5f3c5d681

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Theorems.Thm_Formalism_CohomologicalDescent_LD_ld_sym_shape
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution (q w i : ℕ) (hq : 0 < q) (hi : i ≤ w) (c : ℤ) (h0 : 0 ≤ c) (h1 : c < (i : ℤ)) :
    mu 1 w i (fun _ : Fin q => 0) c ≠ 0 := by
  have hmem := (ld_sym_shape q w i hi).resolve_right (by omega)
  intro h0'
  have hle := Finset.le_sup (f := fun tau => boxesOfContent (fun _ : Fin q => 0) tau c) hmem
  unfold mu at h0'
  rw [h0'] at hle
  have hpos : 0 < boxesOfContent (fun _ : Fin q => 0) (fun a : Fin q => if a.val = 0 then i else 0) c := by
    unfold boxesOfContent
    apply Finset.card_pos.mpr
    refine ⟨⟨0, hq⟩, ?_⟩
    simp
    omega
  exact absurd (lt_of_lt_of_le hpos hle) (lt_irrefl 0)
end Formalism.CohomologicalDescent.LD
