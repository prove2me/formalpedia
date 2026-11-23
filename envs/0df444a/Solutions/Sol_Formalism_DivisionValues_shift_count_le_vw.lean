-- Prove2me | solution 1 for Formalism.DivisionValues.shift_count_le_vw
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:11:45.596811+00:00
-- url     : https://prove2.me/submissions/6d8d29cf-5220-47cb-b380-d11d89336b15

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
theorem _root_.solution (I : FractionalIdeal (𝓞 K)⁰ K) (w : HeightOneSpectrum (𝓞 K)) {b : K}
    (hb0 : b ≠ 0) (hb : b ∈ I) : FractionalIdeal.count K w I ≤ vw w b := by
  have hI : I ≠ 0 := by
    intro h
    rw [h, FractionalIdeal.mem_zero_iff] at hb
    exact hb0 hb
  have hle : FractionalIdeal.spanSingleton (𝓞 K)⁰ b ≤ I :=
    (FractionalIdeal.spanSingleton_le_iff_mem).mpr hb
  have hJ : I⁻¹ * FractionalIdeal.spanSingleton (𝓞 K)⁰ b ≤ 1 := by
    calc I⁻¹ * FractionalIdeal.spanSingleton (𝓞 K)⁰ b ≤ I⁻¹ * I := by gcongr
      _ = 1 := inv_mul_cancel₀ hI
  obtain ⟨J, hJe⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hJ
  have hsp0 : FractionalIdeal.spanSingleton (𝓞 K)⁰ b ≠ 0 := by
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact hb0
  have hJ0 : (J : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
    rw [hJe]; exact mul_ne_zero (inv_ne_zero hI) hsp0
  have e : FractionalIdeal.spanSingleton (𝓞 K)⁰ b = I * (J : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [hJe, ← mul_assoc, mul_inv_cancel₀ hI, one_mul]
  have hv : vw w b = FractionalIdeal.count K w I + FractionalIdeal.count K w (J : FractionalIdeal (𝓞 K)⁰ K) := by
    show FractionalIdeal.count K w (FractionalIdeal.spanSingleton (𝓞 K)⁰ b) = _
    rw [e, FractionalIdeal.count_mul K w hI hJ0]
  have hnn := FractionalIdeal.count_coe_nonneg K w J
  omega
end Formalism.DivisionValues
