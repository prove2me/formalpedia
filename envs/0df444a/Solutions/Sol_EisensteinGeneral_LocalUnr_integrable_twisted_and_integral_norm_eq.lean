-- Prove2me | solution 1 for EisensteinGeneral.LocalUnr.integrable_twisted_and_integral_norm_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/47477a41-09bf-5579-adce-67ff8d10ce42

import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Theorems.Thm_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_EisensteinGeneral_LocalUnr_integrable_twisted_and_integral_norm_eq
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option Elab.async false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

namespace TwistedUnramifiedLocal

open LanglandsTunnell.TateLocal NumberField.AdelicLevel Filter Topology

section Auxiliary

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

private theorem valued_uniformizer_zpow (ϖ : (v.adicCompletion F)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) (k : ℤ) :
    Valued.v ((ϖ ^ k : (v.adicCompletion F)ˣ) : v.adicCompletion F) = WithZero.exp (-k) := by
  have hϖ' : Valued.v (ϖ : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := hϖ
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ', ← WithZero.exp_zsmul]
  congr 1
  simp

private theorem isOpen_ball (ϖ : (v.adicCompletion F)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) (k : ℤ) :
    IsOpen {x : v.adicCompletion F | Valued.v x ≤ WithZero.exp k} := by
  have ht : ((ϖ ^ (-k) : (v.adicCompletion F)ˣ) : v.adicCompletion F) ≠ 0 := Units.ne_zero _
  have h := isOpen_setOf_valued_le v _ ht
  rw [valued_uniformizer_zpow ϖ hϖ, neg_neg] at h
  exact h

private theorem isCompact_integers :
    IsCompact (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
  isCompact_iff_compactSpace.mpr
    (NumberField.AdelicHaar.compactSpace_adicCompletionIntegers (𝓞 F) F v)

private theorem measureReal_integers_pos [MeasurableSpace (v.adicCompletion F)]
    [BorelSpace (v.adicCompletion F)] (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure] :
    0 < μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  rw [measureReal_def, ENNReal.toReal_pos_iff]
  exact ⟨(Valued.isOpen_valuationSubring _).measure_pos μ
      ⟨0, (v.adicCompletionIntegers F).zero_mem⟩,
    (isCompact_integers (F := F) (v := v)).measure_lt_top⟩

private theorem continuous_addChar_of_level (ϖ : (v.adicCompletion F)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (ψ : AddChar (v.adicCompletion F) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp n → ψ x = 1) : Continuous ψ := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  have hmem : (fun y => y - x) ⁻¹' {y : v.adicCompletion F | Valued.v y ≤ WithZero.exp n} ∈ 𝓝 x := by
    apply ((isOpen_ball ϖ hϖ n).preimage (continuous_id.sub continuous_const)).mem_nhds
    simp
  have hev : (fun _ : v.adicCompletion F => ψ x) =ᶠ[𝓝 x] ψ := by
    filter_upwards [hmem] with y hy
    have hy' : ψ (y - x) = 1 := hψn _ hy
    calc ψ x = ψ (y - x) * ψ x := by rw [hy', one_mul]
      _ = ψ (y - x + x) := (AddChar.map_add_eq_mul ψ _ _).symm
      _ = ψ y := by rw [sub_add_cancel]
  exact (continuousAt_congr hev).mp continuousAt_const

private theorem norm_addChar_of_level (ψ : AddChar (v.adicCompletion F) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (x : v.adicCompletion F) : ‖ψ x‖ = 1 := by
  have hq1 : 1 < Ideal.absNorm v.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hvq : Valued.v ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F) < 1 := by
    have h := (HeightOneSpectrum.intValuation_lt_one_iff_mem v (Ideal.absNorm v.asIdeal : 𝓞 F)).mpr
      (by exact_mod_cast Ideal.absNorm_mem v.asIdeal)
    rw [← valued_algebraMap (K := F) v (Ideal.absNorm v.asIdeal : 𝓞 F)] at h
    simpa only [map_natCast] using h
  obtain ⟨j, hj⟩ : ∃ j : ℕ,
      Valued.v (((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F) ^ j * x) ≤ WithZero.exp n := by
    by_cases hx : Valued.v x = 0
    · exact ⟨0, by rw [map_mul, hx, mul_zero]; exact zero_le'⟩
    · by_cases hq0 : Valued.v ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F) = 0
      · exact ⟨1, by rw [map_mul, map_pow, hq0, pow_one, zero_mul]; exact zero_le'⟩
      · have hql : Valued.v ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F)
            = WithZero.exp (WithZero.log (Valued.v ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F))) :=
          (WithZero.exp_log hq0).symm
        have hxm : Valued.v x = WithZero.exp (WithZero.log (Valued.v x)) := (WithZero.exp_log hx).symm
        set l := WithZero.log (Valued.v ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F)) with hl
        set m := WithZero.log (Valued.v x) with hm
        have hl0 : l < 0 := by
          rw [hql, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hvq
          exact hvq
        refine ⟨(m - n).toNat, ?_⟩
        rw [map_mul, map_pow, hql, hxm, ← WithZero.exp_nsmul, ← WithZero.exp_add, WithZero.exp_le_exp,
          nsmul_eq_mul]
        have h1 : (m - n : ℤ) ≤ ((m - n).toNat : ℤ) := Int.self_le_toNat (m - n)
        have h2 : (0 : ℤ) ≤ ((m - n).toNat : ℤ) := by omega
        have h3 : ((m - n).toNat : ℤ) * l ≤ ((m - n).toNat : ℤ) * (-1) :=
          mul_le_mul_of_nonneg_left (by omega) h2
        linarith
  have h1 : ψ (((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F) ^ j * x) = 1 := hψn _ hj
  have h2 : ψ (((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F) ^ j * x)
      = ψ x ^ (Ideal.absNorm v.asIdeal ^ j) := by
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, Nat.cast_pow]
  have h3 : ‖ψ x‖ ^ (Ideal.absNorm v.asIdeal ^ j) = 1 := by rw [← norm_pow, ← h2, h1, norm_one]
  have hqj : Ideal.absNorm v.asIdeal ^ j ≠ 0 := pow_ne_zero _ (by omega)
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hqj).mp h3

private noncomputable def untwisted (χ : (v.adicCompletion F)ˣ →* ℂˣ) (s : ℂ)
    (x : v.adicCompletion F) : ℂ :=
  (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (1 : ℂ)) x
    + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
        (fun y => charExt χ⁻¹ y * ((modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) x

private theorem untwisted_of_le (χ : (v.adicCompletion F)ˣ →* ℂˣ) (s : ℂ) {x : v.adicCompletion F}
    (hx : Valued.v x ≤ 1) : untwisted χ s x = 1 := by
  have hmem : x ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := hx
  have hnot : x ∉ (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ := fun h => h hmem
  rw [untwisted, Set.indicator_of_mem hmem, Set.indicator_of_notMem hnot, add_zero]

private theorem untwisted_of_lt (χ : (v.adicCompletion F)ˣ →* ℂˣ) (s : ℂ) {x : v.adicCompletion F}
    (hx : 1 < Valued.v x) :
    untwisted χ s x = charExt χ⁻¹ x * ((modulus x : ℝ) : ℂ) ^ (-(2 * s + 1)) := by
  have hnot : x ∉ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := fun h => not_le.mpr hx h
  have hmem : x ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ := hnot
  rw [untwisted, Set.indicator_of_notMem hnot, Set.indicator_of_mem hmem, zero_add]

private theorem norm_mul_natCast_cpow (c w : ℂ) :
    ‖c * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ w‖ = ‖c‖ * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ w.re := by
  have hN : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (lt_trans zero_lt_one (NumberField.HeightOneSpectrum.one_lt_absNorm v))
  rw [norm_mul, ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hN]

private theorem re_neg_two_mul_add_one (s : ℂ) : (-(2 * s + 1)).re = -(2 * s.re + 1) := by
  simp

private theorem integrable_untwisted [MeasurableSpace (v.adicCompletion F)]
    [BorelSpace (v.adicCompletion F)] (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (ϖ : (v.adicCompletion F)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (v.adicCompletion F)ˣ →* ℂˣ)
    (hχ : ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χ u = 1)
    (s : ℂ) (hs : ‖((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))‖ < 1) :
    Integrable (untwisted χ s) μ := by
  have hN1 : (1 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
    exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm v).le
  have hN : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := lt_of_lt_of_le zero_lt_one hN1
  have hval :
      ∫ x, untwisted χ s x ∂μ
        = (μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ)
          * (1 - ((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))
          * (1 - ((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s)))⁻¹ :=
    AutomorphicForm.LocalIntertwining.integral_unramifiedWeylIntegrand_adicCompletion F v μ ϖ hϖ χ hχ s hs
  have hre2 : (-(2 * s)).re = -(2 * s.re) := by simp
  have hre3 : (-(2 * s + 1)).re = -(2 * s.re) + (-1) := by
    rw [re_neg_two_mul_add_one]
    ring
  have ha : ‖((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))‖
      = ‖((χ ϖ : ℂˣ) : ℂ)‖ * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re)) := by
    rw [norm_mul_natCast_cpow, hre2]
  have hb : ‖((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1))‖
      ≤ ‖((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))‖ := by
    rw [norm_mul_natCast_cpow, hre3, ha, Real.rpow_add hN, Real.rpow_neg_one]
    have h1 : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hN1
    have h2 : 0 ≤ ‖((χ ϖ : ℂˣ) : ℂ)‖ * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re)) :=
      mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hN.le _)
    calc ‖((χ ϖ : ℂˣ) : ℂ)‖ * (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re))
            * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹)
          = ‖((χ ϖ : ℂˣ) : ℂ)‖ * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re))
            * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ := by ring
      _ ≤ ‖((χ ϖ : ℂˣ) : ℂ)‖ * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re)) * 1 :=
          mul_le_mul_of_nonneg_left h1 h2
      _ = _ := mul_one _
  have hne1 : (1 : ℂ) - ((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)) ≠ 0 := by
    refine sub_ne_zero.mpr fun h => ?_
    have h' := congrArg (fun z : ℂ => ‖z‖) h
    simp only [norm_one] at h'
    linarith [hb.trans_lt hs]
  have hne2 : ((1 : ℂ) - ((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s)))⁻¹ ≠ 0 := by
    refine inv_ne_zero (sub_ne_zero.mpr fun h => ?_)
    have h' := congrArg (fun z : ℂ => ‖z‖) h
    simp only [norm_one] at h'
    linarith
  have hne0 : ((μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (measureReal_integers_pos μ).ne'
  by_contra hni
  exact mul_ne_zero (mul_ne_zero hne0 hne1) hne2 (hval.symm.trans (integral_undef hni))

private noncomputable def normChar (χ : (v.adicCompletion F)ˣ →* ℂˣ) : (v.adicCompletion F)ˣ →* ℂˣ where
  toFun u := Units.mk0 ((‖((χ u : ℂˣ) : ℂ)‖ : ℝ) : ℂ)
    (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (χ u).ne_zero))
  map_one' := by
    ext
    simp
  map_mul' a b := by
    ext
    simp

private theorem normChar_apply (χ : (v.adicCompletion F)ˣ →* ℂˣ) (u : (v.adicCompletion F)ˣ) :
    ((normChar χ u : ℂˣ) : ℂ) = ((‖((χ u : ℂˣ) : ℂ)‖ : ℝ) : ℂ) := rfl

private theorem ofReal_norm_untwisted_mul (χ : (v.adicCompletion F)ˣ →* ℂˣ) (s : ℂ)
    (ψ : AddChar (v.adicCompletion F) ℂ) (hψ1 : ∀ y, ‖ψ y‖ = 1) (ξ x : v.adicCompletion F) :
    ((‖untwisted χ s x * ψ (-(ξ * x))‖ : ℝ) : ℂ) = untwisted (normChar χ) (s.re : ℂ) x := by
  rw [norm_mul, hψ1, mul_one]
  by_cases hx : Valued.v x ≤ 1
  · rw [untwisted_of_le χ s hx, untwisted_of_le (normChar χ) _ hx, norm_one, Complex.ofReal_one]
  · rw [not_le] at hx
    have hx0 : x ≠ 0 := by
      intro h
      rw [h, map_zero] at hx
      exact WithZero.not_lt_zero _ hx
    have hm : (0 : ℝ) < ((modulus x : NNReal) : ℝ) := NNReal.coe_pos.mpr (modulus_pos hx0)
    rw [untwisted_of_lt χ s hx, untwisted_of_lt (normChar χ) _ hx, charExt_of_ne_zero _ hx0,
      charExt_of_ne_zero _ hx0, MonoidHom.inv_apply, MonoidHom.inv_apply, Units.val_inv_eq_inv_val,
      Units.val_inv_eq_inv_val, normChar_apply, norm_mul, norm_inv,
      Complex.norm_cpow_eq_rpow_re_of_pos hm, re_neg_two_mul_add_one,
      show (-(2 * (s.re : ℂ) + 1) : ℂ) = ((-(2 * s.re + 1) : ℝ) : ℂ) from (by push_cast; ring),
      ← Complex.ofReal_cpow hm.le]
    push_cast
    ring

end Auxiliary

end TwistedUnramifiedLocal

open TwistedUnramifiedLocal LanglandsTunnell.TateLocal NumberField.AdelicLevel Filter Topology in

theorem solution
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (ϖ : (v.adicCompletion F)ˣ) (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (v.adicCompletion F)ˣ →* ℂˣ)
    (hχ : ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χ u = 1)
    (s : ℂ) (hs : ‖((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))‖ < 1)
    (ψ : AddChar (v.adicCompletion F) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (ξ : v.adicCompletion F) :
    Integrable (fun x => (((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (1 : ℂ)) x
            + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
                (fun y => LanglandsTunnell.TateLocal.charExt χ⁻¹ y
                  * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) x)
            * ψ (-(ξ * x)))) μ ∧
      ∫ x, ‖(((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (1 : ℂ)) x
            + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
                (fun y => LanglandsTunnell.TateLocal.charExt χ⁻¹ y
                  * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) x)
            * ψ (-(ξ * x)))‖ ∂μ
        = μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F))
            * (1 - ‖((χ ϖ : ℂˣ) : ℂ)‖ * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re + 1)))
            * (1 - ‖((χ ϖ : ℂˣ) : ℂ)‖ * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re)))⁻¹ := by
  have hN : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (lt_trans zero_lt_one (NumberField.HeightOneSpectrum.one_lt_absNorm v))
  have hψc : Continuous ψ := continuous_addChar_of_level ϖ hϖ ψ n hψn
  have hψ1 : ∀ y, ‖ψ y‖ = 1 := norm_addChar_of_level ψ n hψn
  have hint : Integrable (untwisted χ s) μ := integrable_untwisted μ ϖ hϖ χ hχ s hs
  have hmeas : AEStronglyMeasurable (fun x : v.adicCompletion F => ψ (-(ξ * x))) μ :=
    (hψc.comp (continuous_const.mul continuous_id).neg).aestronglyMeasurable
  have hintψ : Integrable (fun x => untwisted χ s x * ψ (-(ξ * x))) μ :=
    hint.mul_bdd hmeas (Eventually.of_forall fun x => (hψ1 _).le)
  refine ⟨hintψ, ?_⟩
  have hχ' : ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → normChar χ u = 1 := by
    intro u hu
    ext
    rw [normChar_apply, hχ u hu, Units.val_one, norm_one, Complex.ofReal_one]
  have hre1 : (-(2 * (s.re : ℂ))).re = -(2 * s.re) := by simp
  have hre2 : (-(2 * s)).re = -(2 * s.re) := by simp
  have hs' : ‖((normChar χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * (s.re : ℂ)))‖ < 1 := by
    rw [norm_mul_natCast_cpow, normChar_apply, Complex.norm_real, norm_norm, hre1]
    rw [norm_mul_natCast_cpow, hre2] at hs
    exact hs
  have hval :
      ∫ x, untwisted (normChar χ) (s.re : ℂ) x ∂μ
        = (μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ)
          * (1 - ((normChar χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * (s.re : ℂ) + 1)))
          * (1 - ((normChar χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * (s.re : ℂ))))⁻¹ :=
    AutomorphicForm.LocalIntertwining.integral_unramifiedWeylIntegrand_adicCompletion F v μ ϖ hϖ
      (normChar χ) hχ' (s.re : ℂ) hs'
  have e1 : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * (s.re : ℂ) + 1))
      = (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re + 1)) : ℝ) := by
    rw [Complex.ofReal_cpow hN.le, Complex.ofReal_natCast]
    congr 1
    push_cast
    ring
  have e2 : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * (s.re : ℂ)))
      = (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re)) : ℝ) := by
    rw [Complex.ofReal_cpow hN.le, Complex.ofReal_natCast]
    congr 1
    push_cast
    ring
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  show ∫ x, ((‖untwisted χ s x * ψ (-(ξ * x))‖ : ℝ) : ℂ) ∂μ = _
  simp_rw [ofReal_norm_untwisted_mul χ s ψ hψ1 ξ]
  rw [hval, normChar_apply, e1, e2]
  push_cast
  ring

end S_EisensteinGeneral_LocalUnr_integrable_twisted_and_integral_norm_eq
end P2MW
export P2MW.S_EisensteinGeneral_LocalUnr_integrable_twisted_and_integral_norm_eq (solution)
