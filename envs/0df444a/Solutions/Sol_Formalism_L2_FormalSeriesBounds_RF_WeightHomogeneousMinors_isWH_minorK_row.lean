-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors.isWH_minorK_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:16:33.887589+00:00
-- url     : https://prove2.me/submissions/d8886de8-3cd4-4a21-9f50-eb23953cf15e

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipNormOne
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NormOneRowDegrees
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_WeightHomogeneousMinors_isWH_deg
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_WeightHomogeneousMinors_isWH_minorK_gen
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_WeightHomogeneousMinors_sum_fin_ite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial
open Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors
variable {R : Type} [CommRing R]
namespace Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors
theorem _root_.solution {N N' k : ℕ} {w : Fin N × Fin N' → ℕ} (P : Prop) [Decidable P] (c0 : ℕ)
    (hw : ∀ x, w x = if P ∧ (x.2 : ℕ) = c0 then 1 else 0) :
    IsWeightedHomogeneous w (minorK R N N' k) (if k ≤ N ∧ k ≤ N' ∧ P ∧ c0 < k then 1 else 0) := by
  by_cases h : k ≤ N ∧ k ≤ N'
  · have hg := isWH_minorK_gen (R := R) (fun c : Fin N' => if P ∧ (c : ℕ) = c0 then 1 else 0) hw h
    refine isWH_deg hg ?_
    by_cases hP : P
    · simp only [hP, true_and, Fin.coe_castLE]
      rw [sum_fin_ite]
      simp [h.1, h.2, hP]
    · simp [hP]
  · unfold minorK
    rw [dif_neg h, if_neg (fun hc => h ⟨hc.1, hc.2.1⟩)]
    exact isWeightedHomogeneous_one R w
end Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors
