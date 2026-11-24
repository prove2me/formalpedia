-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.dominance_of_nabla_weight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:30:41.831247+00:00
-- url     : https://prove2.me/submissions/f9a407fa-fde7-4a7b-b3a1-7fb8335450d6

import Definitions.Def_Formalism_PieriBlockIdeals_BranchingBoundLastGradedOneRow
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeylDominanceZ
import Theorems.Thm_Formalism_GradedWeylDivisibility_ldrow_weight_rowW
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
theorem _root_.solution (r : ℕ) (ν μ : Fin r → ℕ) (hν : Antitone ν) (x : MvPolynomial (Fin r × Fin r) ℤ)
    (hx : x ∈ nablaWt r ν μ) (hne : x ≠ 0) :
    (∀ k : ℕ, (∑ a : Fin r with a.val < k, μ a) ≤ ∑ a : Fin r with a.val < k, ν a) ∧ ∑ a, μ a = ∑ a, ν a := by
  obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hne
  have hdom := dualWeylDominanceZ r r ν le_rfl hν x hx.1 d hd
  have hwt : Finsupp.weight (rowW r r) d = μ := hx.2 (MvPolynomial.mem_support_iff.mp hd)
  have h1 : ∀ a, rowDeg d a = μ a := fun a => by rw [← ldrow_weight_rowW, hwt]
  have h2 : ∀ a : Fin r, rowNu (r := r) ν a = ν a := fun a => by
    unfold rowNu
    rw [dif_pos a.isLt]
  simp only [h1, h2] at hdom
  exact hdom
end Formalism.CohomologicalDescent.LD
