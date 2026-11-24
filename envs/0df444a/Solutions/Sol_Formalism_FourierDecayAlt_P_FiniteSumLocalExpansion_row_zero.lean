-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion.row_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:08:40.636337+00:00
-- url     : https://prove2.me/submissions/b36fad89-61f0-4440-bd42-895a08f59da4

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourTermExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfCVUnderIntOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellOrbitSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FiniteSumLocalExpansion
import Theorems.Thm_Formalism_FourierDecayAlt_P_FiniteSumLocalExpansion_skewRow
import Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_half
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
theorem _root_.solution {t : ℕ} (c b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) (Φ : Mat k r → E) (g : Mat k r)
    (hc : ¬ Function.Injective c) : qminorOp (Q.EH k r) c b u Φ g = 0 := by
  unfold Function.Injective at hc
  push_neg at hc
  obtain ⟨i, j, hij, hne⟩ := hc
  have hcτ : c ∘ Equiv.swap i j = c := by
    funext x
    simp only [Function.comp_apply]
    rcases eq_or_ne x i with rfl | hxi
    · simp [hij]
    rcases eq_or_ne x j with rfl | hxj
    · simp [hij]
    · rw [Equiv.swap_apply_of_ne_of_ne hxi hxj]
  have := skewRow c b u Φ g (Equiv.swap i j)
  rw [hcτ, Equiv.Perm.sign_swap hne] at this
  simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_smul] at this
  have h2 := sub_eq_zero.mpr this
  rw [sub_neg_eq_add] at h2
  exact FourTermExpansion.half _ h2
end Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion
