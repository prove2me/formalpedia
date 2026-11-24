-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BranchingSystems.runDown
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:56:36.903891+00:00
-- url     : https://prove2.me/submissions/b0f1a1a6-d022-44c2-b3d8-21225a4c58f8

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BranchingSystems

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
theorem _root_.solution (hD : ∀ M, P M → ∀ i, (∀ j, M i - 1 ≠ L j) → P (Function.update M i (M i - 1)))
    (M : Fin n → ℤ) (i : Fin n) (t0 : ℤ) (h0 : P (Function.update M i t0)) (t : ℤ) (ht : t ≤ t0) :
    (∀ t', t ≤ t' → t' < t0 → ∀ j, t' ≠ L j) → P (Function.update M i t) := by
  induction t, ht using Int.le_induction_down with
  | base => intro _; exact h0
  | pred t ht ih =>
    intro hv
    have hP := ih (fun t' h1 h2 => hv t' (by omega) h2)
    have h2 := hD _ hP i (by simpa using hv (t - 1) le_rfl (by omega))
    simpa using h2
end Formalism.FourierDecayAlt.P.BranchingSystems
