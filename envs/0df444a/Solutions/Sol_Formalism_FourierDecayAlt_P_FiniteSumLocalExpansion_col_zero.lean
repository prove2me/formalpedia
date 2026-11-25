-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion.col_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:28:51.640993+00:00
-- url     : https://prove2.me/submissions/17ff984f-df04-49b2-adcd-eaededaa1926

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourTermExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfCVUnderIntOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellOrbitSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FiniteSumLocalExpansion
import Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_half
import Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_skewCol
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal
  Formalism.FourierDecayAlt.P.FourTermExpansion
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion
theorem _root_.solution {t : ℕ} (a d : Fin t → Fin (2 * r + k + 1)) (u : ℂ) (Φ : Mat k r → E) (g : Mat k r)
    (hg : g ∈ GV k r) (hloc : Loc (t : ℕ∞) Φ g) (hd : ¬ Function.Injective d) :
    qminorOp (Q.EH k r) a d u Φ g = 0 := by
  unfold Function.Injective at hd
  push_neg at hd
  obtain ⟨i, j, hij, hne⟩ := hd
  have hdτ : d ∘ Equiv.swap i j = d := by
    funext x
    simp only [Function.comp_apply]
    rcases eq_or_ne x i with rfl | hxi
    · simp [hij]
    rcases eq_or_ne x j with rfl | hxj
    · simp [hij]
    · rw [Equiv.swap_apply_of_ne_of_ne hxi hxj]
  have := FourTermExpansion.skewCol a u Φ g hg hloc d (Equiv.swap i j)
  rw [hdτ, Equiv.Perm.sign_swap hne] at this
  simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_smul] at this
  have h2 := sub_eq_zero.mpr this
  rw [sub_neg_eq_add] at h2
  exact FourTermExpansion.half _ h2
end Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion
