-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.jacobian_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:43:20.240896+00:00
-- url     : https://prove2.me/submissions/db454b8c-7012-4158-8f87-5ae21de48852

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_map_smul_muPi
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_two_card_UT
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_mp_shear

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
set_option linter.unusedSimpArgs false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G5
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.G.Jacobian := by
  intro n β t ht
  have hcomp : coordMap n t = (Prod.map (fun v : Fin n → ℂ => t • v)
      (Prod.map (fun v : UT n → ℂ => t • v) (fun v : Fin n → ℂ => t • v))) ∘
      (fun p : BlockCoord n => ((p.1 ᵥ* (wMat n * upper p.2.1), p.2.1, p.2.2) : BlockCoord n)) := by
    funext p
    rfl
  have hm1 : ∀ ι : Type, Measurable (fun v : ι → ℂ => t • v) := fun ι => measurable_const_smul t
  rw [hcomp, ← Measure.map_map ((hm1 _).prodMap ((hm1 _).prodMap (hm1 _))) (mp_shear n β).measurable,
    (mp_shear n β).map_eq]
  unfold muBlock
  rw [← Measure.map_prod_map _ _ (hm1 _) ((hm1 _).prodMap (hm1 _)), ← Measure.map_prod_map _ _ (hm1 _) (hm1 _),
    map_smul_muPi β t _ ht, map_smul_muPi β t _ ht, Measure.prod_smul_left, Measure.prod_smul_left,
    Measure.prod_smul_right, Measure.prod_smul_right, Measure.prod_smul_right, smul_smul, smul_smul]
  congr 1
  rw [← Real.toNNReal_mul (by positivity), ← Real.toNNReal_mul (by positivity), ← mul_inv, ← mul_inv,
    ← pow_add, ← pow_add, two_card_UT, Fintype.card_fin]
  congr 3
  cases n with
  | zero => rfl
  | succ k => simp only [Nat.add_sub_cancel]; ring
end Formalism.FourierDecayAlt.P
