-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.glue_coordinate_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:34:07.908181+00:00
-- url     : https://prove2.me/submissions/c125cc9c-8cd8-4347-bc11-2b458390bb5f

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaOfDensities
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HsInnerAddSmulRight
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelIntegrandAestronglyMeasurable
import Theorems.Thm_Formalism_FourierDecayAlt_P5_coordinate_split_fst
import Theorems.Thm_Formalism_FourierDecayAlt_P5_coordinate_split_snd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd
variable {r : ℕ}
namespace Formalism.FourierDecayAlt.P5
theorem _root_.solution (l : Fin r) (c : Fin r → ℂ) (a : Cf r l.castSucc) :
    glue l.castSucc c a = glue l.succ (Function.update c l (coordinateSplit l a).1) (coordinateSplit l a).2 := by
  funext j
  rw [coordinate_split_fst]
  unfold glue
  rcases lt_trichotomy j.val l.val with h | h | h
  · have h1 : ¬ (l.castSucc.val ≤ j.val) := by simp only [Fin.val_castSucc]; omega
    have h2 : ¬ (l.succ.val ≤ j.val) := by simp only [Fin.val_succ]; omega
    have h3 : j ≠ l := fun e => by rw [e] at h; omega
    rw [dif_neg h1, dif_neg h2, Function.update_of_ne h3]
  · have hj : j = l := Fin.ext h
    subst hj
    have h2 : ¬ (j.succ.val ≤ j.val) := by simp
    rw [dif_pos (by simp), dif_neg h2, Function.update_self]
  · have h1 : l.castSucc.val ≤ j.val := by simp only [Fin.val_castSucc]; omega
    have h2 : l.succ.val ≤ j.val := by simp only [Fin.val_succ]; omega
    rw [dif_pos h1, dif_pos h2, coordinate_split_snd]
end Formalism.FourierDecayAlt.P5
