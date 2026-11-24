-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx2.exists_skip_one_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:24:55.050897+00:00
-- url     : https://prove2.me/submissions/b2626ae3-0f95-41b4-9aa9-594f54c449ea

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.Qx2
variable {k r : ℕ} {i : Fin (r + 1)}
namespace Formalism.FourierDecayAlt.P.Qx2
theorem _root_.solution {t : ℕ} {a b : Fin t} (h : a ≠ b) : ∃ l, skip1 b l = a := by
  rcases Nat.lt_or_gt_of_ne (fun e => h (Fin.ext e)) with hab | hab
  · refine ⟨⟨a.val, by have := b.isLt; omega⟩, ?_⟩
    apply Fin.ext
    unfold skip1
    split_ifs with h' <;> simp only [Fin.val_mk] at * <;> omega
  · refine ⟨⟨a.val - 1, by have := a.isLt; omega⟩, ?_⟩
    apply Fin.ext
    unfold skip1
    split_ifs with h' <;> simp only [Fin.val_mk] at * <;> omega
end Formalism.FourierDecayAlt.P.Qx2
