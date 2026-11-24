-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FourTermExpansion.split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:37:48.373875+00:00
-- url     : https://prove2.me/submissions/a79dc36d-50b9-4e23-b739-6df382980cc6

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourTermExpansion
import Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_fold_cons
import Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_fold_append

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
namespace Formalism.FourierDecayAlt.P.FourTermExpansion
theorem _root_.solution (M : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Mat k r) {t : ℕ}
    (f : Fin t → ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) (i : ℕ) (hi : i + 1 < t) (Φ : Mat k r → E) :
    fold M (List.ofFn f) Φ = fold M ((List.ofFn f).take i)
      (Top (LT M) (f ⟨i, by omega⟩).1 (f ⟨i, by omega⟩).2.1 (f ⟨i, by omega⟩).2.2
        (Top (LT M) (f ⟨i + 1, hi⟩).1 (f ⟨i + 1, hi⟩).2.1 (f ⟨i + 1, hi⟩).2.2
          (fold M ((List.ofFn f).drop (i + 2)) Φ))) := by
  conv_lhs =>
    rw [← List.take_append_drop i (List.ofFn f),
      List.drop_eq_getElem_cons (l := List.ofFn f) (i := i) (by simp; omega),
      List.drop_eq_getElem_cons (l := List.ofFn f) (i := i + 1) (by simp; omega)]
  rw [fold_append, fold_cons, fold_cons, List.getElem_ofFn, List.getElem_ofFn]
  all_goals rfl
end Formalism.FourierDecayAlt.P.FourTermExpansion
