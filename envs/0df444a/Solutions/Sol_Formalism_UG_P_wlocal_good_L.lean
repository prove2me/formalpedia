-- Prove2me | solution 1 for Formalism.UG.P.wlocal_good_L
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:55:31.494405+00:00
-- url     : https://prove2.me/submissions/71c89f7a-7296-481f-8fa8-8b0bf47ee198

import Definitions.Def_Formalism_SatakeDualWeyl_StatementW
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal
import Theorems.Thm_Formalism_UG_P_wlocal_good_one
import Theorems.Thm_Formalism_UG_P_wlocal_good_mul
import Theorems.Thm_Formalism_UG_P_wlocal_good_E
import Theorems.Thm_Formalism_UG_P_wlocal_L_one
import Theorems.Thm_Formalism_UG_P_wlocal_L_congr
import Theorems.Thm_Formalism_UG_P_wlocal_L_insert
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
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
open Formalism.GradedWeylDivisibility
variable {R : Type} [CommRing R]
namespace Formalism.UG.P
theorem _root_.solution {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (k : Fin r) (c : Fin r → R) :
    wlocal_Good hn ν (wlocal_L k c) := by
  have key : ∀ s : Finset (Fin r), wlocal_Good hn ν (wlocal_L k (fun i => if i ∈ s then c i else 0)) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · rw [show (fun i : Fin r => if i ∈ (∅ : Finset (Fin r)) then c i else 0) = 0 from
        funext fun i => by simp, wlocal_L_one]
      exact wlocal_good_one hn ν
    · intro a s ha ih
      by_cases hak : a = k
      · rw [wlocal_L_congr k (fun i => if i ∈ insert a s then c i else 0) (fun i => if i ∈ s then c i else 0)
          (by
            intro i hi
            have hia : i ≠ a := fun h => hi (h.trans hak)
            simp [Finset.mem_insert, hia])]
        exact ih
      · rw [wlocal_L_insert k a c s ha hak]
        exact wlocal_good_mul (wlocal_good_E hn ν a k (c a)) ih
  have h := key Finset.univ
  rwa [show (fun i : Fin r => if i ∈ (Finset.univ : Finset (Fin r)) then c i else 0) = c from
    funext fun i => by simp] at h
end Formalism.UG.P
