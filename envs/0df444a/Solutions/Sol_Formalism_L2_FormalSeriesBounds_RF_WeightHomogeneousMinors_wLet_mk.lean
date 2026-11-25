-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors.wLet_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:16:28.482547+00:00
-- url     : https://prove2.me/submissions/1cf31aaf-432c-4a26-9ffb-67ade680b203

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipNormOne
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NormOneRowDegrees
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_WeightHomogeneousMinors_letEq

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
variable {T : Type} (r : T → ℕ) (n : ℕ)
variable {r n}
namespace Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors
theorem _root_.solution (σ : T) (c0 : Fin (r σ)) (τ : T) (c : Fin (r τ)) (ρ : Fin n) :
    wLet r n σ c0 ⟨τ, (c, ρ)⟩ = if (⟨τ, c⟩ : Σ σ, Fin (r σ)) = ⟨σ, c0⟩ then 1 else 0 := by
  unfold wLet
  simp only [letEq]
  by_cases h : (⟨τ, c⟩ : Σ σ, Fin (r σ)) = ⟨σ, c0⟩
  · simp only [h, true_and, if_true]
    rw [Finset.sum_ite_eq]
    simp
  · simp [h]
end Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors
