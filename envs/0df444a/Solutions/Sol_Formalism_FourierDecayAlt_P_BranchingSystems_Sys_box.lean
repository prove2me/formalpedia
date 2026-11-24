-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BranchingSystems.Sys.box
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:17:18.105877+00:00
-- url     : https://prove2.me/submissions/936cc2a8-fd5f-4ef3-82a1-663edff387bb

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BranchingSystems
import Theorems.Thm_Formalism_FourierDecayAlt_P_BranchingSystems_between
import Theorems.Thm_Formalism_FourierDecayAlt_P_BranchingSystems_runDown

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BranchingSystems
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
variable {n : ℕ} {L : Fin (n + 1) → ℤ} {P : (Fin n → ℤ) → Prop}
namespace Formalism.FourierDecayAlt.P.BranchingSystems
namespace Sys
theorem _root_.solution (h : Sys L P) (M : Fin n → ℤ) (hM : Box L M) : P M := by
  have key : ∀ s : Finset (Fin n), P (fun j => if j ∈ s then M j else L j.castSucc) := by
    intro s
    refine Finset.induction_on s (by simpa using h.top) ?_
    intro a s ha ih
    have e : (fun j => if j ∈ insert a s then M j else L j.castSucc) =
        Function.update (fun j => if j ∈ s then M j else L j.castSucc) a (M a) := by
      funext j
      by_cases hj : j = a
      · subst hj
        simp
      · simp [hj, Function.update_of_ne hj]
    rw [e]
    have h0 : P (Function.update (fun j => if j ∈ s then M j else L j.castSucc) a (L a.castSucc)) := by
      have e2 : Function.update (fun j => if j ∈ s then M j else L j.castSucc) a (L a.castSucc) =
          (fun j => if j ∈ s then M j else L j.castSucc) := by
        rw [Function.update_eq_self_iff]
        simp [ha]
      rw [e2]
      exact ih
    have hMa := hM a
    exact runDown h.down _ a (L a.castSucc) h0 (M a) hMa.2
      (fun t' h1 h2 j => between h.anti a (by omega) h2 j)
  simpa using key Finset.univ
end Sys
end Formalism.FourierDecayAlt.P.BranchingSystems
