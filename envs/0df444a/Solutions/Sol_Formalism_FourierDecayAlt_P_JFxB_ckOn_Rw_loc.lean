-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxB.ckOn_Rw_loc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:06:57.541971+00:00
-- url     : https://prove2.me/submissions/2a92be6f-7d23-43c0-b7e2-da5abeaf1da2

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfCVUnderIntOfParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CkOn_Dw
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_sCkOn_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxB
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.JFxB
theorem _root_.solution {UU : Set (Mat k r)} {w : List (Mat k r)} (hw : ∀ X ∈ w, inLie k r X) {j : ℕ}
    (hj : w.length + 1 ≤ j + 1) {f : Mat k r → E} (hf : CkOn ((j + 1 : ℕ) : ℕ∞) UU f) :
    CkOn 1 UU (Rw w f) := by
  rw [← Dw_wR]
  apply CkOn_Dw
  · intro x hx
    simp only [wR, List.mem_map] at hx
    obtain ⟨X, hX, rfl⟩ := hx
    exact hw X hX
  · apply sCkOn_mono _ hf
    have h1 : (wR w).length = w.length := by simp [wR]
    rw [h1]
    exact_mod_cast (by omega : 1 + w.length ≤ j + 1)
end Formalism.FourierDecayAlt.P.JFxB
