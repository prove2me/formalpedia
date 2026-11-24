-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lehw_kill
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:39:21.15635+00:00
-- url     : https://prove2.me/submissions/de8581c8-251d-4985-8375-d2fafc69beef

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_lehw_dom
import Theorems.Thm_Formalism_GradedWeylDivisibility_lehw_rowDiv_shift
import Theorems.Thm_Formalism_GradedWeylDivisibility_highestWeightCount_self_eq_succ_of_lt
import Theorems.Thm_Formalism_GradedWeylDivisibility_lehw_weight_P
import Theorems.Thm_Formalism_GradedWeylDivisibility_lehw_weight_rowW
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivStable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν)
    (G : MvPolynomial (Fin r × Fin n) ℚ) (hG : G ∈ dualWeyl ℚ r n ν)
    (hGh : IsWeightedHomogeneous (rowW r n) G (rowNu (r := r) ν))
    (a b : Fin r) (hab : a < b) (k : ℕ) (hk : 1 ≤ k) : rowDiv ℚ a b k G = 0 := by
  have hH := rowDivStable ℚ r n ν a b k G hG
  by_contra hne
  obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.mp hne
  have hGP : IsWeightedHomogeneous (lehwP (n := n) a) G
      ((∑ a' : Fin r with a'.val < a.val + 1, rowNu (r := r) ν a' : ℕ) : ℤ) := by
    intro d hd
    rw [lehw_weight_P]
    congr 1
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [← lehw_weight_rowW, hGh hd]
  have hshift := lehw_rowDiv_shift ℚ (lehwP a) 1 a b (highestWeightCount_self_eq_succ_of_lt hab) _ k G hGP
  have hmw := hshift hm
  rw [lehw_weight_P] at hmw
  have hdom := lehw_dom ν hn hν _ hH m (mem_support_iff.mpr hm) (a.val + 1)
  omega
end Formalism.GradedWeylDivisibility
