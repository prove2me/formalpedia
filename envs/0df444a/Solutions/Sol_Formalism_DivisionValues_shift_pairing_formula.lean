-- Prove2me | solution 1 for Formalism.DivisionValues.shift_pairing_formula
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:50:21.888551+00:00
-- url     : https://prove2.me/submissions/b406a0b0-73a0-4c7d-a041-bf0f0a0e8251

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
import Theorems.Thm_Formalism_DivisionValues_shift_mem_smulLat
import Theorems.Thm_Formalism_DivisionValues_shift_coe_ne_zero
import Theorems.Thm_Formalism_DivisionValues_imageLcv_mem_locP
import Theorems.Thm_Formalism_DivisionValues_valuation_basic_properties

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module NumberField IsDedekindDomain
open scoped Matrix nonZeroDivisors
noncomputable section
namespace Formalism.DivisionValues
section Smul
variable {K : Type} [Field K] [NumberField K] [StarRing K] {d : ℕ}
end Smul
section Prime
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable [IsTotallyComplex K]
end Prime
section Unit
variable {K : Type} [Field K] [NumberField K] [StarRing K] {d : ℕ}
end Unit
section Ideal
variable {K : Type} [Field K] [NumberField K] [StarRing K] {d : ℕ}
end Ideal
private theorem vw_eq_zero_of_not_mem_asIdeal {K : Type} [Field K] [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K))
    {t : 𝓞 K} (ht : t ∉ w.asIdeal) : vw w (t : K) = 0 := by
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact ht w.asIdeal.zero_mem
  have hI : Ideal.span {t} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact ht0
  have hv : vw w (t : K) =
      ((Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {t})).factors : ℤ) := by
    rw [← FractionalIdeal.count_coe K w hI, FractionalIdeal.coeIdeal_span_singleton]
    simp [vw]
  have hnd : ¬ (w.asIdeal ∣ Ideal.span {t}) := by
    rw [Ideal.dvd_span_singleton]
    exact ht
  rw [← Associates.count_ne_zero_iff_dvd hI w.irreducible] at hnd
  push_neg at hnd
  rw [hv, hnd]
  rfl
end Formalism.DivisionValues
end
end

set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix nonZeroDivisors
noncomputable section
open Formalism Formalism.DivisionValues
namespace Formalism.DivisionValues
theorem _root_.solution : ShiftPairing := by
  intro K _ _ _ d w N N' s hsh f hf φ hφ
  obtain ⟨a, ha, hva, hloc⟩ := hsh
  have hVB := valuation_basic_properties K w
  have hφl : φ ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal N' :=
    (imageLcv_mem_locP _ _ _).2 ⟨1, w.asIdeal.primeCompl.one_mem, by rw [one_smul]; exact hφ⟩
  rw [hloc, imageLcv_mem_locP] at hφl
  obtain ⟨t, ht, htφ⟩ := hφl
  rw [shift_mem_smulLat] at htφ
  obtain ⟨ψ, hψ, hψe⟩ := htφ
  have ht' : t ∉ w.asIdeal := ht
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact ht' w.asIdeal.zero_mem
  have htK : (t : K) ≠ 0 := shift_coe_ne_zero ht0
  have hft : a * f ψ = (t : K) * f φ := by
    have h1 := congrArg f hψe
    rw [map_smul, smul_eq_mul, LinearMap.map_smul_of_tower, Algebra.smul_def] at h1
    exact h1
  have hvt : vw w (t : K) = 0 := vw_eq_zero_of_not_mem_asIdeal w ht'
  rcases hf ψ hψ with h0 | hle
  · left
    rw [h0, mul_zero] at hft
    exact (mul_eq_zero.mp hft.symm).resolve_left htK
  · by_cases hfφ : f φ = 0
    · exact Or.inl hfφ
    · right
      have hfψ : f ψ ≠ 0 := by
        intro h
        rw [h, mul_zero] at hft
        exact hfφ ((mul_eq_zero.mp hft.symm).resolve_left htK)
      have e1 := hVB.1 a (f ψ) ha hfψ
      have e2 := hVB.1 (t : K) (f φ) htK hfφ
      rw [hft, e2, hvt] at e1
      omega
end Formalism.DivisionValues
