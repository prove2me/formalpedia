-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors.isWH_minorK_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:58:27.392949+00:00
-- url     : https://prove2.me/submissions/eedbef53-07dc-4cf6-b2d9-85feeb864b64

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipNormOne
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NormOneRowDegrees
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_prod
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sum


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
theorem _root_.solution {N N' k : ℕ} {w : Fin N × Fin N' → ℕ} (v : Fin N' → ℕ) (hw : ∀ x, w x = v x.2)
    (h : k ≤ N ∧ k ≤ N') :
    IsWeightedHomogeneous w (minorK R N N' k) (∑ c : Fin k, v (Fin.castLE h.2 c)) := by
  unfold minorK
  rw [dif_pos h, Matrix.det_apply]
  refine IsWeightedHomogeneous.sum _ _ _ fun σ _ => ?_
  have hprod : IsWeightedHomogeneous w (∏ i : Fin k, (Matrix.of fun b c : Fin k =>
      (X (Fin.castLE h.1 b, Fin.castLE h.2 c) : MvPolynomial (Fin N × Fin N') R)) (σ i) i)
      (∑ c : Fin k, v (Fin.castLE h.2 c)) :=
    IsWeightedHomogeneous.prod _ _ _ fun i _ => by
      simp only [Matrix.of_apply]
      have hx := isWeightedHomogeneous_X R w (Fin.castLE h.1 (σ i), Fin.castLE h.2 i)
      rwa [hw] at hx
  intro dd hdd
  apply hprod
  intro h0
  apply hdd
  rw [MvPolynomial.coeff_smul, h0, smul_zero]
end Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors
