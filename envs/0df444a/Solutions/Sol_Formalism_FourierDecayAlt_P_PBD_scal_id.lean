-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBD.scal_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:55:05.911613+00:00
-- url     : https://prove2.me/submissions/74459638-37b9-4d71-873b-fd184af1dbab

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ComponentFamilySettingOfSettingBis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBD
open Formalism.FourierDecayAlt NumberField MeasureTheory Formalism.QuantumDeterminants
open scoped Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
namespace Formalism.FourierDecayAlt.P.PBD
theorem _root_.solution (A B : ℝ) (hA : 0 < A) (hB : 0 < B) (ν e : ℤ) :
    (B ^ (-ν) / ((A * B)⁻¹ ^ ν)) ^ (2 * e) / ((A * B)⁻¹ ^ ν) ^ 2 = B ^ (2 * ν) * A ^ (2 * ν * (e + 1)) := by
  have h1 : B ^ (-ν) / ((A * B)⁻¹ ^ ν) = A ^ ν := by
    rw [inv_zpow, div_inv_eq_mul, mul_zpow, zpow_neg]
    field_simp
  have h2 : ((A * B)⁻¹ ^ ν) ^ 2 = A ^ (-(2 * ν)) * B ^ (-(2 * ν)) := by
    rw [← zpow_natCast, ← zpow_mul, mul_inv, mul_zpow, ← zpow_neg_one, ← zpow_neg_one B, ← zpow_mul, ← zpow_mul]
    congr 2 <;> push_cast <;> ring
  rw [h1, h2, ← zpow_mul]
  rw [div_eq_mul_inv, mul_inv, ← zpow_neg, ← zpow_neg]
  simp only [neg_neg]
  rw [show 2 * ν * (e + 1) = ν * (2 * e) + 2 * ν by ring, zpow_add₀ hA.ne']
  ring
end Formalism.FourierDecayAlt.P.PBD
