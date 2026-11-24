-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.WModel.exists_pow_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:11:48.778803+00:00
-- url     : https://prove2.me/submissions/e34ab965-2de7-4984-bd2c-8fa7ee97973e

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementW
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_WittTeichmullerRoot
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_WModel
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_WModel_p_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped NNReal
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.InvariantFactorPaths.G7.WModel
variable (p : ℕ) [hp : Fact p.Prime]
namespace Formalism.InvariantFactorPaths.G7.WModel
theorem _root_.solution (x : KK p) (hx : x ≠ 0) :
    ∃ (n : ℤ) (u : (WW p)ˣ), x = (p : KK p) ^ n * algebraMap (WW p) (KK p) (u : WW p) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := WW p) x
  have ha : a ≠ 0 := by
    rintro rfl
    simp at hx
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨m, a', rfl⟩ := WittVector.exists_eq_pow_p_mul' a ha
  obtain ⟨n, b', rfl⟩ := WittVector.exists_eq_pow_p_mul' b hb0
  refine ⟨(m : ℤ) - n, a' * b'⁻¹, ?_⟩
  have hp0 := p_ne_zero p
  have h1 : algebraMap (WW p) (KK p) (b' : WW p) * algebraMap (WW p) (KK p) ((b'⁻¹ : (WW p)ˣ) : WW p)
      = 1 := by
    rw [← map_mul]
    simp
  have hB : algebraMap (WW p) (KK p) (b' : WW p) ≠ 0 := left_ne_zero_of_mul_eq_one h1
  have h2 : algebraMap (WW p) (KK p) ((b'⁻¹ : (WW p)ˣ) : WW p)
      = (algebraMap (WW p) (KK p) (b' : WW p))⁻¹ := eq_inv_of_mul_eq_one_right h1
  rw [zpow_sub₀ hp0, Units.val_mul, map_mul, map_mul, map_mul, h2, map_pow, map_pow, map_natCast,
    zpow_natCast, zpow_natCast]
  field_simp
end Formalism.InvariantFactorPaths.G7.WModel
