-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BranchingSystems.runUp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:57:54.879197+00:00
-- url     : https://prove2.me/submissions/3f8ad612-b209-4969-aeaa-2607aaea87a8

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BranchingSystems
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ


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
theorem _root_.solution (hR : ∀ M, P M → ∀ i, (∀ j, M i ≠ L j) → P (Function.update M i (M i + 1)))
    (M : Fin n → ℤ) (i : Fin n) (t0 : ℤ) (h0 : P (Function.update M i t0)) (t : ℤ) (ht : t0 ≤ t) :
    (∀ t', t0 ≤ t' → t' < t → ∀ j, t' ≠ L j) → P (Function.update M i t) := by
  induction t, ht using Int.le_induction with
  | base => intro _; exact h0
  | succ t ht ih =>
    intro hv
    have hP := ih (fun t' h1 h2 => hv t' h1 (by omega))
    have h2 := hR _ hP i (by simpa using hv t ht (by omega))
    simpa using h2
end Formalism.FourierDecayAlt.P.BranchingSystems
