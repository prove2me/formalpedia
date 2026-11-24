-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FourTermExpansion.fold_loc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:25:10.508871+00:00
-- url     : https://prove2.me/submissions/f7da3fa5-21f1-450f-81bd-c25bbbac5e16

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourTermExpansion
import Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_fold_nil
import Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_fold_cons
import Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_top_loc

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FourTermExpansion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (M : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Mat k r)
namespace Formalism.FourierDecayAlt.P.FourTermExpansion
theorem _root_.solution (ts : List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) :
    ∀ (m : ℕ) (Φ : Mat k r → E) (g : Mat k r), Loc ((m + ts.length : ℕ) : ℕ∞) Φ g →
      Loc (m : ℕ∞) (fold M ts Φ) g := by
  induction ts with
  | nil =>
    intro m Φ g h
    rw [fold_nil]
    simpa using h
  | cons t ts ih =>
    intro m Φ g h
    rw [fold_cons]
    have e : m + 1 + ts.length = m + (t :: ts).length := by simp only [List.length_cons]; omega
    have h' : Loc ((m + 1 + ts.length : ℕ) : ℕ∞) Φ g := by rw [e]; exact h
    have := ih (m + 1) Φ g h'
    exact top_loc M (by exact_mod_cast this) t.1 t.2.1 t.2.2
end Formalism.FourierDecayAlt.P.FourTermExpansion
