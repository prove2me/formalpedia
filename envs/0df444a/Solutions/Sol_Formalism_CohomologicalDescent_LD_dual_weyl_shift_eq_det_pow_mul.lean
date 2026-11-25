-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.dual_weyl_shift_eq_det_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:47:34.549601+00:00
-- url     : https://prove2.me/submissions/c338836c-cee1-49ba-80c8-a7f3b7793668

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Theorems.Thm_Formalism_CohomologicalDescent_LA_det_dvd_of_mem_dual_weyl_shift
import Theorems.Thm_Formalism_CohomologicalDescent_LA_mem_dual_weyl_of_det_mul
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
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LA
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution {r : ℕ} (ν : Fin r → ℕ) (hν : Antitone ν) (c : ℕ)
    {f : MvPolynomial (Fin r × Fin r) ℤ} (hf : f ∈ dualWeyl ℤ r r (fun a => ν a + c)) :
    ∃ g ∈ dualWeyl ℤ r r ν, f = genericDet ℤ r ^ c * g := by
  induction c generalizing f with
  | zero => exact ⟨f, by simpa using hf, by simp⟩
  | succ c ih =>
    have hν' : Antitone (fun a => ν a + c) := fun a b hab => Nat.add_le_add_right (hν hab) c
    obtain ⟨y, rfl⟩ := det_dvd_of_mem_dual_weyl_shift (fun a => ν a + c) hν' hf
    obtain ⟨g, hg, rfl⟩ := ih (mem_dual_weyl_of_det_mul (fun a => ν a + c) hf)
    exact ⟨g, hg, by rw [pow_succ', mul_assoc]⟩
end Formalism.CohomologicalDescent.LD
