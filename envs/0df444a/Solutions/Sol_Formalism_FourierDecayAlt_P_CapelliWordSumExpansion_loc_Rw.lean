-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.loc_Rw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:42:19.085107+00:00
-- url     : https://prove2.me/submissions/cde572df-2360-4063-8289-e63110a6d35c

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliWordSumExpansion
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliWordSumExpansion_loc_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliWordSumExpansion_loc_RdV
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
theorem _root_.solution {N : ℕ} {f : Mat k r → E} {g : Mat k r} (h : Loc (N : ℕ∞) f g) (w : List (Mat k r))
    (hw : ∀ X ∈ w, inLie k r X) (m : ℕ) (hle : m + w.length ≤ N) : Loc (m : ℕ∞) (Rw w f) g := by
  induction w generalizing m with
  | nil =>
    simp only [List.length_nil, add_zero] at hle
    exact loc_mono (by exact_mod_cast hle) h
  | cons X w ih =>
    have h1 : Loc ((m + 1 : ℕ) : ℕ∞) (Rw w f) g :=
      ih (fun Y hY => hw Y (List.mem_cons_of_mem X hY)) (m + 1) (by simp at hle; omega)
    have h2 : Loc ((m : ℕ∞) + 1) (Rw w f) g := by simpa using h1
    exact loc_RdV (hw X (by simp)) h2
end Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
