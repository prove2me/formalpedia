-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bs_hwspace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:44:27.725681+00:00
-- url     : https://prove2.me/submissions/fdaf0b97-8fc1-4ccf-a390-77ef494dfb9b

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchScale
import Theorems.Thm_Formalism_BranchingDeterminantCap_bs_dom
import Theorems.Thm_Formalism_BranchingDeterminantCap_bs_height_le
import Theorems.Thm_Formalism_GradedWeylDivisibility_hwLine
import Theorems.Thm_Formalism_GradedWeylDivisibility_ldrow_weight_rowW
import Theorems.Thm_Formalism_GradedWeylDivisibility_lhwin_rowDiv_shift
import Theorems.Thm_Formalism_GradedWeylDivisibility_lhwin_weight_ht
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivStable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
open Formalism.REAL
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution {n : ℕ} (sg : Fin n → ℕ) (hsg : Antitone sg) (q : MvPolynomial (Fin n × Fin n) ℂ)
    (hq : q ∈ dualWeyl ℂ n n sg) (hqw : IsWeightedHomogeneous (rowW n n) q sg) :
    ∃ c : ℂ, q = c • hw ℂ le_rfl sg := by
  apply hwLine ℂ n n le_rfl sg hsg q hq
  intro a b hab k hk
  by_contra hne
  have hmem := rowDivStable ℂ n n sg a b k q hq
  have hht : IsWeightedHomogeneous (lhwinHt n n) q (∑ a : Fin n, (a.val : ℤ) * (sg a : ℤ)) := by
    intro d hd
    rw [lhwin_weight_ht, hqw hd]
  have hsh := lhwin_rowDiv_shift ℂ _ a b k q hht
  obtain ⟨d, hd⟩ := ne_zero_iff.mp hne
  have e := hsh hd
  rw [lhwin_weight_ht] at e
  simp only [ldrow_weight_rowW] at e
  have dom := bs_dom sg _ hmem d (mem_support_iff.mpr hd)
  have hle := bs_height_le n (rowDeg d) sg dom.1 dom.2
  have hab' : (a.val : ℤ) - b.val ≤ -1 := by
    have : a.val < b.val := hab
    omega
  have hk' : (1 : ℤ) ≤ k := by exact_mod_cast hk
  nlinarith
end Formalism.BranchingDeterminantCap
