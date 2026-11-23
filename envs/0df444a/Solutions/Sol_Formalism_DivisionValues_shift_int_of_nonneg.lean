-- Prove2me | solution 1 for Formalism.DivisionValues.shift_int_of_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:58:28.078252+00:00
-- url     : https://prove2.me/submissions/48ddd478-0748-4999-9999-7cf2fd7027d9

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_DivIntoDualShift
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LcvBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DivIntoDual
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TwistedLatticeNaturality
import Theorems.Thm_Formalism_DivisionValues_shift_coe_ne_zero
import Theorems.Thm_Formalism_DivisionValues_shift_decomp
import Theorems.Thm_Formalism_DivisionValues_ReductionFirst_vw_int_nonneg
import Theorems.Thm_Formalism_DivisionValues_ReductionFirst_vw_mul
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_int_nonneg
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix nonZeroDivisors
noncomputable section
open Formalism Formalism.DivisionValues
variable {K : Type} [Field K] [NumberField K] [StarRing K] {d : ℕ}
namespace Formalism.DivisionValues
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) (b : K) (hb : b ≠ 0) (hv : 0 ≤ vw w b) :
    ∃ t y : 𝓞 K, t ∉ w.asIdeal ∧ (t : K) * b = (y : K) := by
  obtain ⟨ϖ, hϖ0, _, hdec⟩ := shift_decomp w
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := 𝓞 K) b
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hyK : (y : K) ≠ 0 := shift_coe_ne_zero hy0
  change (x : K) / (y : K) = b at hxy
  have hx0 : x ≠ 0 := by
    intro h
    rw [h] at hxy
    apply hb
    rw [← hxy]
    simp
  have hxK : (x : K) ≠ 0 := shift_coe_ne_zero hx0
  have hvx : vw w (x : K) = vw w b + vw w (y : K) := by
    rw [← ValuationRepresentative.vw_mul w _ _ hb hyK, ← hxy, div_mul_cancel₀ _ hyK]
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (ValuationRepresentative.vw_int_nonneg w y)
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le hv
  have hvx' : vw w (x : K) = ((k + m : ℕ) : ℤ) := by
    rw [hvx, hm, hk]
    push_cast
    ring
  obtain ⟨t1, s1, ht1, hs1, h1⟩ := hdec (k + m) x hx0 hvx'
  obtain ⟨t2, s2, ht2, hs2, h2⟩ := hdec m y hy0 hm
  refine ⟨t1 * s2, ϖ ^ k * s1 * t2, w.isPrime.mul_notMem ht1 hs2, ?_⟩
  rw [← hxy, mul_div_assoc', div_eq_iff hyK]
  have : t1 * s2 * x = ϖ ^ k * s1 * t2 * y := by
    calc t1 * s2 * x = s2 * (t1 * x) := by ring
      _ = s2 * (ϖ ^ (k + m) * s1) := by rw [h1]
      _ = ϖ ^ k * s1 * (ϖ ^ m * s2) := by ring
      _ = ϖ ^ k * s1 * (t2 * y) := by rw [h2]
      _ = ϖ ^ k * s1 * t2 * y := by ring
  exact_mod_cast congrArg (fun z : 𝓞 K => (z : K)) this
end Formalism.DivisionValues
