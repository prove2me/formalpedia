-- Prove2me | solution 1 for EisensteinGeneral.LocalRam.integral_twisted_smooth_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/64eab497-93bc-5759-8964-b2f141f82b0f

import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_EisensteinGeneral_LocalRam_integral_twisted_smooth_eq
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.CarrierPins.mk.injEq AutomorphicForm.CarrierPins.mk.sizeOf_spec AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false

noncomputable section

open MeasureTheory IsDedekindDomain NumberField

namespace TwistedSmoothLocal

section Prep

open IsDedekindDomain.HeightOneSpectrum Filter Topology
open LanglandsTunnell.TateLocal NumberField.AdelicLevel

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

private theorem setOf_valued_sub_le_mem_nhds (x z : v.adicCompletion F) (hz : Valued.v z ≠ 0) :
    {y : v.adicCompletion F | Valued.v (y - x) ≤ Valued.v z} ∈ 𝓝 x := by
  have hr : Valued.v.restrict z ≠ 0 := by
    rwa [Ne, Valuation.restrict_eq_zero_iff]
  have hopen : IsOpen {w : v.adicCompletion F | Valued.v.restrict w ≤ Valued.v.restrict z} :=
    Valued.isOpen_closedBall (R := v.adicCompletion F) hr
  have hopen' : IsOpen {y : v.adicCompletion F | Valued.v.restrict (y - x) ≤ Valued.v.restrict z} :=
    hopen.preimage (continuous_id.sub continuous_const)
  have hx : x ∈ {y : v.adicCompletion F | Valued.v.restrict (y - x) ≤ Valued.v.restrict z} := by
    simp
  refine Filter.mem_of_superset (hopen'.mem_nhds hx) fun y hy => ?_
  rw [Set.mem_setOf_eq, Valuation.restrict_le_iff] at hy
  exact hy

private theorem setOf_valued_sub_lt_mem_nhds (x z : v.adicCompletion F) (hz : Valued.v z ≠ 0) :
    {y : v.adicCompletion F | Valued.v (y - x) < Valued.v z} ∈ 𝓝 x := by
  have hr : Valued.v.restrict z ≠ 0 := by
    rwa [Ne, Valuation.restrict_eq_zero_iff]
  have hopen : IsOpen {w : v.adicCompletion F | Valued.v.restrict w < Valued.v.restrict z} :=
    Valued.isOpen_ball (R := v.adicCompletion F) _
  have hopen' : IsOpen {y : v.adicCompletion F | Valued.v.restrict (y - x) < Valued.v.restrict z} :=
    hopen.preimage (continuous_id.sub continuous_const)
  have hx : x ∈ {y : v.adicCompletion F | Valued.v.restrict (y - x) < Valued.v.restrict z} := by
    simp only [Set.mem_setOf_eq, sub_self, map_zero]
    exact pos_iff_ne_zero.mpr hr
  refine Filter.mem_of_superset (hopen'.mem_nhds hx) fun y hy => ?_
  rw [Set.mem_setOf_eq, Valuation.restrict_lt_iff] at hy
  exact hy

private theorem valued_uniformizer_exp (ϖ : (v.adicCompletion F)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) :
    Valued.v (ϖ : v.adicCompletion F) = WithZero.exp (-1 : ℤ) :=
  hϖ

private theorem valued_uniformizer_pow (ϖ : (v.adicCompletion F)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) (k : ℕ) :
    Valued.v ((ϖ : v.adicCompletion F) ^ k) = WithZero.exp (-(k : ℤ)) := by
  rw [map_pow, valued_uniformizer_exp ϖ hϖ, ← WithZero.exp_nsmul]
  congr 1
  simp

private theorem continuous_of_depth (ϖ : (v.adicCompletion F)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) (m : ℕ)
    (B : v.adicCompletion F → ℂ)
    (hB : ∀ x y : v.adicCompletion F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B y = B x) :
    Continuous B := by
  have hz : Valued.v ((ϖ : v.adicCompletion F) ^ m)
      = (Multiplicative.ofAdd (-(m : ℤ)) : Multiplicative ℤ) :=
    valued_uniformizer_pow ϖ hϖ m
  have hz0 : Valued.v ((ϖ : v.adicCompletion F) ^ m) ≠ 0 := by
    rw [hz]
    exact WithZero.coe_ne_zero
  refine continuous_iff_continuousAt.mpr fun x => ?_
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [setOf_valued_sub_le_mem_nhds x _ hz0] with y hy
  rw [hz] at hy
  exact (hB x y hy).symm

private theorem charExt_inv_eq_of_sub_le (χ : (v.adicCompletion F)ˣ →* ℂˣ) (c : ℕ)
    (hχ : ∀ u ∈ higherUnitsAt F v c, χ u = 1) {x y : v.adicCompletion F} (hx : x ≠ 0)
    (hlt : Valued.v (y - x) < Valued.v x)
    (hle : Valued.v (y - x) ≤ Valued.v x * WithZero.exp (-(c : ℤ))) :
    charExt χ⁻¹ y = charExt χ⁻¹ x := by
  have hvx : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  have hvy : Valued.v y = Valued.v x := Valuation.map_eq_of_sub_lt _ hlt
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, map_zero] at hvy
    exact hvx hvy.symm
  set u : (v.adicCompletion F)ˣ := (Units.mk0 x hx)⁻¹ * Units.mk0 y hy0 with hu
  have huval : (u : v.adicCompletion F) = x⁻¹ * y := by simp [hu]
  have hu1 : Valued.v (u : v.adicCompletion F) = 1 := by
    rw [huval, map_mul, map_inv₀, hvy, inv_mul_cancel₀ hvx]
  have hu2 : Valued.v ((u : v.adicCompletion F) - 1) ≤ WithZero.exp (-(c : ℤ)) := by
    have h1 : (u : v.adicCompletion F) - 1 = x⁻¹ * (y - x) := by
      rw [huval, mul_sub, inv_mul_cancel₀ hx]
    rw [h1, map_mul, map_inv₀]
    calc (Valued.v x)⁻¹ * Valued.v (y - x)
        ≤ (Valued.v x)⁻¹ * (Valued.v x * WithZero.exp (-(c : ℤ))) := by gcongr
      _ = WithZero.exp (-(c : ℤ)) := by rw [← mul_assoc, inv_mul_cancel₀ hvx, one_mul]
  have hmem : u ∈ higherUnitsAt F v c := ⟨hu1, Or.inr hu2⟩
  have hχu : χ u = 1 := hχ u hmem
  have hy' : Units.mk0 y hy0 = Units.mk0 x hx * u := by
    rw [hu, ← mul_assoc, mul_inv_cancel, one_mul]
  rw [charExt_of_ne_zero _ hx, charExt_of_ne_zero _ hy0, hy', map_mul]
  simp [hχu]

private theorem continuousOn_charExt_inv (ϖ : (v.adicCompletion F)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (v.adicCompletion F)ˣ →* ℂˣ) (c : ℕ) (hχ : ∀ u ∈ higherUnitsAt F v c, χ u = 1) :
    ContinuousOn (charExt χ⁻¹) {(0 : v.adicCompletion F)}ᶜ := by
  intro x hx
  rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hx
  have hvx : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  apply ContinuousAt.continuousWithinAt
  have hzv : Valued.v (x * (ϖ : v.adicCompletion F) ^ c) = Valued.v x * WithZero.exp (-(c : ℤ)) := by
    rw [map_mul, valued_uniformizer_pow ϖ hϖ c]
  have hz0 : Valued.v (x * (ϖ : v.adicCompletion F) ^ c) ≠ 0 := by
    rw [hzv]
    exact mul_ne_zero hvx WithZero.coe_ne_zero
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [setOf_valued_sub_lt_mem_nhds x _ hz0] with y hy
  rw [hzv] at hy
  have hle1 : WithZero.exp (-(c : ℤ)) ≤ 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  have hlt : Valued.v (y - x) < Valued.v x :=
    lt_of_lt_of_le hy (mul_le_of_le_one_right' hle1)
  exact (charExt_inv_eq_of_sub_le χ c hχ hx hlt hy.le).symm

private theorem continuous_addChar_neg_mul (ψ : AddChar (v.adicCompletion F) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (ξ : v.adicCompletion F) :
    Continuous fun x : v.adicCompletion F => ψ (-(ξ * x)) := by
  by_cases hξ : ξ = 0
  · subst hξ
    simp only [zero_mul, neg_zero, AddChar.map_zero_eq_one]
    exact continuous_const
  have hvξ : Valued.v ξ ≠ 0 := (Valuation.ne_zero_iff _).mpr hξ
  obtain ⟨z, hz⟩ := valuedAdicCompletion_surjective (K := F) (v := v)
    (WithZero.exp n * (Valued.v ξ)⁻¹)
  have hz0 : Valued.v z ≠ 0 := by
    rw [hz]
    exact mul_ne_zero WithZero.coe_ne_zero (inv_ne_zero hvξ)
  refine continuous_iff_continuousAt.mpr fun x => ?_
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [setOf_valued_sub_le_mem_nhds x z hz0] with y hy
  rw [hz] at hy
  have hsmall : Valued.v (ξ * (y - x)) ≤ WithZero.exp n := by
    rw [map_mul]
    calc Valued.v ξ * Valued.v (y - x)
        ≤ Valued.v ξ * (WithZero.exp n * (Valued.v ξ)⁻¹) := by gcongr
      _ = WithZero.exp n := by rw [mul_comm, mul_assoc, inv_mul_cancel₀ hvξ, mul_one]
  have h1 : ψ (ξ * (y - x)) = 1 := hψn _ hsmall
  have hsplit : -(ξ * y) = -(ξ * x) + -(ξ * (y - x)) := by ring
  show ψ (-(ξ * x)) = ψ (-(ξ * y))
  rw [hsplit, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv (ψ := ψ) (ξ * (y - x)), h1, inv_one,
    mul_one]

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

private def untwisted (χ : (v.adicCompletion F)ˣ →* ℂˣ) (s : ℂ) (A B : v.adicCompletion F → ℂ)
    (x : v.adicCompletion F) : ℂ :=
  (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator A x
    + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
        (fun y => charExt χ⁻¹ y * ((modulus y : ℝ) : ℂ) ^ (-(2 * s + 1)) * B y⁻¹) x

private theorem modulus_eq_of_valued_eq {x y : v.adicCompletion F} (h : Valued.v x = Valued.v y) :
    modulus x = modulus y := by
  rw [modulus_adicCompletion_eq_nnnorm F v x, modulus_adicCompletion_eq_nnnorm F v y]
  apply NNReal.coe_injective
  simp only [coe_nnnorm]
  exact le_antisymm (Valued.toNormedField.norm_le_iff.mpr h.le) (Valued.toNormedField.norm_le_iff.mpr h.ge)

private theorem isOpen_integers : IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  have hr : Valued.v.restrict (1 : v.adicCompletion F) ≠ 0 := by
    rw [Ne, Valuation.restrict_eq_zero_iff, map_one]
    exact one_ne_zero
  have h := Valued.isOpen_closedBall (R := v.adicCompletion F) hr
  convert h using 1
  ext y
  simp only [SetLike.mem_coe, mem_adicCompletionIntegers, Set.mem_setOf_eq]
  rw [Valuation.restrict_le_iff, map_one]

private theorem isCompact_integers : IsCompact (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
  isCompact_iff_compactSpace.mpr
    (NumberField.AdelicHaar.compactSpace_adicCompletionIntegers (𝓞 F) F v)

private theorem continuousOn_of_valued_eq {E : Type} [TopologicalSpace E] (g : v.adicCompletion F → E)
    (hg : ∀ x y : v.adicCompletion F, Valued.v x = Valued.v y → g x = g y) :
    ContinuousOn g {(0 : v.adicCompletion F)}ᶜ := by
  intro x hx
  rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hx
  have hvx : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  apply ContinuousAt.continuousWithinAt
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [setOf_valued_sub_lt_mem_nhds x x hvx] with y hy
  exact hg x y (Valuation.map_eq_of_sub_lt _ hy).symm

private theorem continuousOn_modulus_cpow (w : ℂ) :
    ContinuousOn (fun y : v.adicCompletion F => ((modulus y : ℝ) : ℂ) ^ w) {(0 : v.adicCompletion F)}ᶜ :=
  continuousOn_of_valued_eq _ fun x y h => by rw [modulus_eq_of_valued_eq h]

private theorem compl_integers_subset :
    (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ ⊆ {(0 : v.adicCompletion F)}ᶜ := by
  intro x hx h0
  apply hx
  rw [Set.mem_singleton_iff] at h0
  subst h0
  exact (v.adicCompletionIntegers F).zero_mem

section Measurability

variable [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
variable (μ : Measure (v.adicCompletion F))

private theorem aestronglyMeasurable_untwisted (ϖ : (v.adicCompletion F)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (v.adicCompletion F)ˣ →* ℂˣ) (c : ℕ) (hχ : ∀ u ∈ higherUnitsAt F v c, χ u = 1) (m : ℕ)
    (A : v.adicCompletion F → ℂ)
    (hA : IntegrableOn A (v.adicCompletionIntegers F : Set (v.adicCompletion F)) μ)
    (B : v.adicCompletion F → ℂ)
    (hB : ∀ x y : v.adicCompletion F, Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B y = B x)
    (s : ℂ) : AEStronglyMeasurable (untwisted χ s A B) μ := by
  have hO : MeasurableSet (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    isOpen_integers.measurableSet
  have h1 : AEStronglyMeasurable
      ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator A) μ :=
    (aestronglyMeasurable_indicator_iff hO).mpr hA.aestronglyMeasurable
  have hcont : ContinuousOn (fun y : v.adicCompletion F =>
      charExt χ⁻¹ y * ((modulus y : ℝ) : ℂ) ^ (-(2 * s + 1)) * B y⁻¹)
      (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ := by
    have h0 := compl_integers_subset (F := F) (v := v)
    have hB' : ContinuousOn (fun y : v.adicCompletion F => B y⁻¹)
        (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ :=
      (continuous_of_depth ϖ hϖ m B hB).comp_continuousOn (continuousOn_inv₀.mono h0)
    exact (((continuousOn_charExt_inv ϖ hϖ χ c hχ).mono h0).mul
      ((continuousOn_modulus_cpow _).mono h0)).mul hB'
  have h2 : AEStronglyMeasurable
      ((v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
        (fun y => charExt χ⁻¹ y * ((modulus y : ℝ) : ℂ) ^ (-(2 * s + 1)) * B y⁻¹)) μ :=
    (aestronglyMeasurable_indicator_iff hO.compl).mpr (hcont.aestronglyMeasurable hO.compl)
  exact h1.add h2

end Measurability

private def absChar (χ : (v.adicCompletion F)ˣ →* ℂˣ) : (v.adicCompletion F)ˣ →* ℂˣ where
  toFun u := Units.mk0 ((‖((χ u : ℂˣ) : ℂ)‖ : ℝ) : ℂ)
    (by exact_mod_cast (norm_ne_zero_iff.mpr (χ u).ne_zero))
  map_one' := by
    ext
    simp
  map_mul' u w := by
    ext
    simp

private theorem absChar_apply (χ : (v.adicCompletion F)ˣ →* ℂˣ) (u : (v.adicCompletion F)ˣ) :
    ((absChar χ u : ℂˣ) : ℂ) = ((‖((χ u : ℂˣ) : ℂ)‖ : ℝ) : ℂ) :=
  rfl

private theorem absChar_higherUnits (χ : (v.adicCompletion F)ˣ →* ℂˣ) (c : ℕ)
    (hχ : ∀ u ∈ higherUnitsAt F v c, χ u = 1) :
    ∃ c : ℕ, ∀ u ∈ higherUnitsAt F v c, absChar χ u = 1 := by
  refine ⟨c, fun u hu => ?_⟩
  ext
  rw [absChar_apply, hχ u hu]
  simp

private theorem norm_charExt_inv_absChar (χ : (v.adicCompletion F)ˣ →* ℂˣ) (y : v.adicCompletion F) :
    ‖charExt χ⁻¹ y‖ = ‖charExt (absChar χ)⁻¹ y‖ := by
  by_cases hy : y = 0
  · subst hy
    simp
  rw [charExt_of_ne_zero _ hy, charExt_of_ne_zero _ hy]
  simp only [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, absChar_apply]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_norm]

private theorem depth_norm_add_one (m : ℕ) (B : v.adicCompletion F → ℂ)
    (hB : ∀ x y : v.adicCompletion F, Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B y = B x) :
    ∀ x y : v.adicCompletion F, Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) →
      (fun z => ((‖B z‖ + 1 : ℝ) : ℂ)) y = (fun z => ((‖B z‖ + 1 : ℝ) : ℂ)) x := by
  intro x y hxy
  simp only [hB x y hxy]

private theorem absNorm_pos : 0 < Ideal.absNorm v.asIdeal := by
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  exact Nat.pos_of_ne_zero ((Ideal.absNorm_ne_zero_iff v.asIdeal).mpr inferInstance)

private theorem hs_absChar (ϖ : (v.adicCompletion F)ˣ) (χ : (v.adicCompletion F)ˣ →* ℂˣ) (s : ℂ)
    (hs : ‖((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))‖ < 1) :
    ‖((absChar χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * (s.re : ℂ)))‖ < 1 := by
  have hN : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by exact_mod_cast absNorm_pos (F := F) (v := v)
  have hcast : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) = (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [norm_mul, hcast, Complex.norm_cpow_eq_rpow_re_of_pos hN] at hs ⊢
  rw [absChar_apply, Complex.norm_real, Real.norm_eq_abs, abs_norm]
  convert hs using 3
  simp

private theorem norm_untwisted_le (χ : (v.adicCompletion F)ˣ →* ℂˣ) (s : ℂ) (A B : v.adicCompletion F → ℂ)
    (x : v.adicCompletion F) :
    ‖untwisted χ s A B x‖
      ≤ ‖untwisted (absChar χ) (s.re : ℂ) (fun z => ((‖A z‖ + 1 : ℝ) : ℂ)) (fun z => ((‖B z‖ + 1 : ℝ) : ℂ)) x‖ := by
  by_cases hx : x ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  · simp only [untwisted, Set.indicator_of_mem hx, Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hx),
      add_zero, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity)]
    linarith
  · have hx0 : x ≠ 0 := fun h => hx (h ▸ (v.adicCompletionIntegers F).zero_mem)
    have hmod : (0 : ℝ) < (modulus x : ℝ) := by
      rw [modulus_adicCompletion_eq_nnnorm F v x]
      exact_mod_cast norm_pos_iff.mpr hx0
    simp only [untwisted, Set.indicator_of_notMem hx, Set.indicator_of_mem (Set.mem_compl hx), zero_add,
      norm_mul]
    rw [norm_charExt_inv_absChar, Complex.norm_cpow_eq_rpow_re_of_pos hmod,
      Complex.norm_cpow_eq_rpow_re_of_pos hmod]
    have hre : (-(2 * s + 1)).re = (-(2 * (s.re : ℂ) + 1)).re := by simp
    rw [hre]
    gcongr
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    linarith

section NormAddOne

variable [MeasurableSpace (v.adicCompletion F)]
variable (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]

private theorem integrableOn_norm_add_one (A : v.adicCompletion F → ℂ)
    (hA : IntegrableOn A (v.adicCompletionIntegers F : Set (v.adicCompletion F)) μ) :
    IntegrableOn (fun z => ((‖A z‖ + 1 : ℝ) : ℂ)) (v.adicCompletionIntegers F : Set (v.adicCompletion F)) μ := by
  have hfin : μ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) ≠ ⊤ :=
    (isCompact_integers.measure_lt_top).ne
  exact (hA.norm.add (integrableOn_const hfin)).ofReal

end NormAddOne

private theorem charExt_absChar_inv_eq (χ : (v.adicCompletion F)ˣ →* ℂˣ) (x : v.adicCompletion F) :
    charExt (absChar χ)⁻¹ x = ((‖charExt χ⁻¹ x‖ : ℝ) : ℂ) := by
  by_cases hx : x = 0
  · subst hx
    simp
  rw [charExt_of_ne_zero _ hx, charExt_of_ne_zero _ hx]
  simp only [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, absChar_apply, norm_inv]
  push_cast
  rfl

section Domination

variable [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
variable (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]

private theorem integrable_dominator (ϖ : (v.adicCompletion F)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (v.adicCompletion F)ˣ →* ℂˣ) (c : ℕ) (hχ : ∀ u ∈ higherUnitsAt F v c, χ u = 1)
    (m : ℕ) (hm : 1 ≤ m) (A : v.adicCompletion F → ℂ)
    (hA : IntegrableOn A (v.adicCompletionIntegers F : Set (v.adicCompletion F)) μ)
    (B : v.adicCompletion F → ℂ)
    (hB : ∀ x y : v.adicCompletion F, Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B y = B x)
    (s : ℂ) (hs : ‖((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))‖ < 1) :
    Integrable (untwisted (absChar χ) (s.re : ℂ) (fun z => ((‖A z‖ + 1 : ℝ) : ℂ))
      (fun z => ((‖B z‖ + 1 : ℝ) : ℂ))) μ := by
  set A' : v.adicCompletion F → ℂ := fun z => ((‖A z‖ + 1 : ℝ) : ℂ) with hA'def
  set B' : v.adicCompletion F → ℂ := fun z => ((‖B z‖ + 1 : ℝ) : ℂ) with hB'def
  have hval := AutomorphicForm.LocalIntertwining.integral_smoothWeylIntegrand_adicCompletion F v μ ϖ hϖ
    (absChar χ) (absChar_higherUnits χ c hχ) m hm A' (integrableOn_norm_add_one μ A hA) B'
    (depth_norm_add_one m B hB) (s.re : ℂ) (hs_absChar ϖ χ s hs)
  change ∫ x, untwisted (absChar χ) (s.re : ℂ) A' B' x ∂μ = _ at hval
  by_contra hnot
  rw [integral_undef hnot] at hval

  have hfin : μ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) ≠ ⊤ :=
    isCompact_integers.measure_lt_top.ne
  have hpos : 0 < μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    ENNReal.toReal_pos (isOpen_integers.measure_pos μ ⟨0, (v.adicCompletionIntegers F).zero_mem⟩).ne' hfin
  have hN : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by exact_mod_cast absNorm_pos (F := F) (v := v)

  have hshell : ∀ S : Set (v.adicCompletion F),
      ∃ r : ℝ, 0 ≤ r ∧ ∫ x in S, charExt (absChar χ)⁻¹ x * B' x⁻¹ ∂μ = (r : ℂ) := by
    intro S
    refine ⟨∫ x in S, ‖charExt χ⁻¹ x‖ * (‖B x⁻¹‖ + 1) ∂μ, integral_nonneg fun x => by positivity, ?_⟩
    have heq : (fun x => charExt (absChar χ)⁻¹ x * B' x⁻¹)
        = fun x => ((‖charExt χ⁻¹ x‖ * (‖B x⁻¹‖ + 1) : ℝ) : ℂ) := by
      funext x
      rw [charExt_absChar_inv_eq, hB'def]
      push_cast
      ring
    rw [heq, integral_complex_ofReal]
  have hunit : ∃ r : ℝ, 0 ≤ r ∧
      ∫ u in {u : v.adicCompletion F | Valued.v u = 1}, charExt (absChar χ)⁻¹ u ∂μ = (r : ℂ) := by
    refine ⟨∫ u in {u : v.adicCompletion F | Valued.v u = 1}, ‖charExt χ⁻¹ u‖ ∂μ,
      integral_nonneg fun x => by positivity, ?_⟩
    have heq : (fun u => charExt (absChar χ)⁻¹ u) = fun u => ((‖charExt χ⁻¹ u‖ : ℝ) : ℂ) := by
      funext u
      rw [charExt_absChar_inv_eq]
    rw [heq, integral_complex_ofReal]

  set ra : ℝ := ‖((χ ϖ : ℂˣ) : ℂ)‖ * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re)) with hra_def
  have hra0 : 0 ≤ ra := by positivity
  have hra1 : ra < 1 := by
    rw [norm_mul, ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hN] at hs
    convert hs using 3
    simp
  have hratio : ((absChar χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * (s.re : ℂ))) = (ra : ℂ) := by
    rw [absChar_apply, hra_def, Complex.ofReal_mul, Complex.ofReal_cpow hN.le]
    push_cast
    ring_nf
  have hcpow : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * (s.re : ℂ) + 1))
      = ((((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re + 1)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hN.le]
    push_cast
    ring_nf
  have key : ∀ t₁ t₂ t₃ : ℂ,
      μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) ≤ t₁.re → 0 ≤ t₂.re → 0 ≤ t₃.re →
      (0 : ℂ) = t₁ + t₂ + t₃ → False := by
    intro t₁ t₂ t₃ h₁ h₂ h₃ h
    have := congrArg Complex.re h
    simp only [Complex.zero_re, Complex.add_re] at this
    linarith
  refine key _ _ _ ?_ ?_ ?_ hval
  ·
    have heq : ∫ x in (v.adicCompletionIntegers F : Set (v.adicCompletion F)), A' x ∂μ
        = ((∫ x in (v.adicCompletionIntegers F : Set (v.adicCompletion F)), (‖A x‖ + 1) ∂μ : ℝ) : ℂ) := by
      rw [hA'def]
      exact integral_complex_ofReal
    rw [heq, Complex.ofReal_re]
    have hmono : ∫ _ in (v.adicCompletionIntegers F : Set (v.adicCompletion F)), (1 : ℝ) ∂μ
        ≤ ∫ x in (v.adicCompletionIntegers F : Set (v.adicCompletion F)), (‖A x‖ + 1) ∂μ :=
      integral_mono (integrableOn_const hfin) (hA.norm.add (integrableOn_const hfin))
        fun x => by simp
    rw [setIntegral_const, smul_eq_mul, mul_one] at hmono
    exact hmono
  ·
    rw [Complex.re_sum]
    refine Finset.sum_nonneg fun k _ => ?_
    obtain ⟨r, hr0, hr⟩ := hshell {x : v.adicCompletion F | Valued.v x = Multiplicative.ofAdd (k : ℤ)}
    rw [hr, hcpow, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
    exact mul_nonneg (pow_nonneg (Real.rpow_nonneg hN.le _) k) hr0
  ·
    obtain ⟨r, hr0, hr⟩ := hunit
    rw [hr, hratio, hB'def]
    simp only
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_inv, ← Complex.ofReal_pow,
      ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re]
    have h1 : 0 < 1 - ra := by linarith
    positivity

private theorem integrable_twisted_aux (ϖ : (v.adicCompletion F)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (v.adicCompletion F)ˣ →* ℂˣ) (c : ℕ) (hχ : ∀ u ∈ higherUnitsAt F v c, χ u = 1)
    (m : ℕ) (hm : 1 ≤ m) (A : v.adicCompletion F → ℂ)
    (hA : IntegrableOn A (v.adicCompletionIntegers F : Set (v.adicCompletion F)) μ)
    (B : v.adicCompletion F → ℂ)
    (hB : ∀ x y : v.adicCompletion F, Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B y = B x)
    (s : ℂ) (hs : ‖((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))‖ < 1)
    (ψ : AddChar (v.adicCompletion F) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp n → ψ x = 1) (ξ : v.adicCompletion F) :
    Integrable (fun x => untwisted χ s A B x * ψ (-(ξ * x))) μ := by
  have hD := (integrable_dominator μ ϖ hϖ χ c hχ m hm A hA B hB s hs).norm
  refine hD.mono' ?_ (ae_of_all _ fun x => ?_)
  · exact (aestronglyMeasurable_untwisted μ ϖ hϖ χ c hχ m A hA B hB s).mul
      (continuous_addChar_neg_mul ψ n hψn ξ).aestronglyMeasurable
  · rw [norm_mul, norm_addChar_of_level ψ n hψn, mul_one]
    exact norm_untwisted_le χ s A B x

end Domination

private theorem isOpen_setOf_valued_le (z : v.adicCompletion F) (hz : Valued.v z ≠ 0) :
    IsOpen {x : v.adicCompletion F | Valued.v x ≤ Valued.v z} := by
  have hr : Valued.v.restrict z ≠ 0 := by
    rwa [Ne, Valuation.restrict_eq_zero_iff]
  have h := Valued.isOpen_closedBall (R := v.adicCompletion F) hr
  convert h using 1
  ext y
  simp only [Set.mem_setOf_eq]
  rw [Valuation.restrict_le_iff]

private theorem isOpen_setOf_valued_lt (z : v.adicCompletion F) (hz : Valued.v z ≠ 0) :
    IsOpen {x : v.adicCompletion F | Valued.v x < Valued.v z} := by
  have hr : Valued.v.restrict z ≠ 0 := by
    rwa [Ne, Valuation.restrict_eq_zero_iff]
  have h := Valued.isOpen_ball (R := v.adicCompletion F) (Valued.v.restrict z)
  convert h using 1
  ext y
  simp only [Set.mem_setOf_eq]
  rw [Valuation.restrict_lt_iff]

section ShellSets

variable [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]

private theorem measurableSet_setOf_valued_eq (k : ℤ) :
    MeasurableSet {x : v.adicCompletion F | Valued.v x = WithZero.exp k} := by
  obtain ⟨z, hz⟩ := valuedAdicCompletion_surjective (K := F) (v := v) (WithZero.exp k)
  have hz0 : Valued.v z ≠ 0 := by
    rw [hz]
    exact WithZero.coe_ne_zero
  have hset : {x : v.adicCompletion F | Valued.v x = WithZero.exp k}
      = {x : v.adicCompletion F | Valued.v x ≤ Valued.v z}
          ∩ {x : v.adicCompletion F | Valued.v x < Valued.v z}ᶜ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_compl_iff, not_lt, ← hz]
    exact le_antisymm_iff
  rw [hset]
  exact (isOpen_setOf_valued_le z hz0).measurableSet.inter (isOpen_setOf_valued_lt z hz0).measurableSet.compl

private theorem measurableSet_setOf_exp_lt (k : ℤ) :
    MeasurableSet {x : v.adicCompletion F | WithZero.exp k < Valued.v x} := by
  obtain ⟨z, hz⟩ := valuedAdicCompletion_surjective (K := F) (v := v) (WithZero.exp k)
  have hz0 : Valued.v z ≠ 0 := by
    rw [hz]
    exact WithZero.coe_ne_zero
  have hset : {x : v.adicCompletion F | WithZero.exp k < Valued.v x}
      = {x : v.adicCompletion F | Valued.v x ≤ Valued.v z}ᶜ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le, hz]
  rw [hset]
  exact (isOpen_setOf_valued_le z hz0).measurableSet.compl

end ShellSets

private theorem toAdd_unzero_exp (j : ℤ) (h : WithZero.exp j ≠ 0) :
    (WithZero.unzero h).toAdd = j :=
  congrArg Multiplicative.toAdd (WithZero.unzero_coe (x := Multiplicative.ofAdd j) h)

private theorem coe_modulus_of_valued_eq {x : v.adicCompletion F} {j : ℤ}
    (hx : Valued.v x = WithZero.exp j) :
    ((modulus x : NNReal) : ℝ) = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ j := by
  rw [modulus_adicCompletion_eq_nnnorm F v x, coe_nnnorm, NumberField.FinitePlace.norm_def, hx,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero, toAdd_unzero_exp, NNReal.coe_zpow]
  norm_cast

private theorem ofReal_pow_cpow {a : ℝ} (ha : 0 ≤ a) (s : ℂ) (k : ℕ) :
    (((a ^ k : ℝ)) : ℂ) ^ s = (((a : ℝ) : ℂ) ^ s) ^ k := by
  induction k with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (pow_nonneg ha n) ha, ih,
        pow_succ]

private theorem untwisted_add_eq_of_sphere (χ : (v.adicCompletion F)ˣ →* ℂˣ) (c : ℕ) (hc : 1 ≤ c)
    (hχ : ∀ u ∈ higherUnitsAt F v c, χ u = 1) (m : ℕ) (hm : 1 ≤ m) (s : ℂ)
    (A B : v.adicCompletion F → ℂ)
    (hB : ∀ x y : v.adicCompletion F, Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B y = B x)
    {t x : v.adicCompletion F} {j : ℤ} (hmj : (m : ℤ) ≤ j) (hx : Valued.v x = WithZero.exp j)
    (ht : Valued.v t ≤ WithZero.exp (j - c)) :
    untwisted χ s A B (t + x) = untwisted χ s A B x := by
  have hvx1 : (1 : WithZero (Multiplicative ℤ)) < Valued.v x := by
    rw [hx, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hvx1
    exact (not_lt_of_ge zero_le') hvx1
  have htlt : Valued.v t < Valued.v x := by
    rw [hx]
    exact lt_of_le_of_lt ht (WithZero.exp_lt_exp.mpr (by omega))
  have hvtx : Valued.v (t + x) = Valued.v x := Valued.v.map_add_eq_of_lt_right htlt
  have hxO : x ∉ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
    show x ∉ v.adicCompletionIntegers F
    rw [mem_adicCompletionIntegers]
    exact not_le_of_gt hvx1
  have htxO : t + x ∉ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
    show t + x ∉ v.adicCompletionIntegers F
    rw [mem_adicCompletionIntegers, hvtx]
    exact not_le_of_gt hvx1
  have hB0 : ∀ y : v.adicCompletion F, Valued.v y = WithZero.exp j → B y⁻¹ = B 0 := by
    intro y hy
    refine hB 0 y⁻¹ ?_
    rw [sub_zero, map_inv₀, hy, ← WithZero.exp_neg]
    show WithZero.exp (-j) ≤ WithZero.exp (-(m : ℤ))
    exact WithZero.exp_le_exp.mpr (by omega)
  have hsub : (t + x) - x = t := add_sub_cancel_right t x
  simp only [untwisted, Set.indicator_of_notMem hxO, Set.indicator_of_notMem htxO,
    Set.indicator_of_mem (Set.mem_compl hxO), Set.indicator_of_mem (Set.mem_compl htxO), zero_add]
  have hchar : charExt χ⁻¹ (t + x) = charExt χ⁻¹ x := by
    refine charExt_inv_eq_of_sub_le χ c hχ hx0 (by rw [hsub]; exact htlt) ?_
    rw [hsub, hx, ← WithZero.exp_add]
    exact ht.trans (WithZero.exp_le_exp.mpr (by omega))
  rw [hchar, modulus_eq_of_valued_eq hvtx, hB0 _ (hvtx.trans hx), hB0 _ hx]

end Prep

private theorem integral_twisted_smooth_eq
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (ϖ : (v.adicCompletion F)ˣ) (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (v.adicCompletion F)ˣ →* ℂˣ)
    (c : ℕ) (hc : 1 ≤ c) (hχ : ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt F v c, χ u = 1)
    (m : ℕ) (hm : 1 ≤ m)
    (A : v.adicCompletion F → ℂ)
    (hA : IntegrableOn A (v.adicCompletionIntegers F : Set (v.adicCompletion F)) μ)
    (B : v.adicCompletion F → ℂ)
    (hB : ∀ x y : v.adicCompletion F, Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B y = B x)
    (s : ℂ) (hs : ‖((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))‖ < 1)
    (ψ : AddChar (v.adicCompletion F) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (hψn' : ∃ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1)
    (ξ : v.adicCompletion F) (e : ℤ) (hξ : Valued.v ξ = WithZero.exp e) :
    ∫ x, (((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator A x
          + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
              (fun y => LanglandsTunnell.TateLocal.charExt χ⁻¹ y
                * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1)) * B y⁻¹) x)
          * ψ (-(ξ * x))) ∂μ
      = (∫ x in (v.adicCompletionIntegers F : Set (v.adicCompletion F)), A x * ψ (-(ξ * x)) ∂μ)
        + ∑ k ∈ Finset.Icc 1 (max ((m : ℤ) - 1) (n + (c : ℤ) - e)).toNat,
            (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1))) ^ k
              * ∫ x in {x : v.adicCompletion F | Valued.v x = WithZero.exp (k : ℤ)},
                  LanglandsTunnell.TateLocal.charExt χ⁻¹ x * B x⁻¹ * ψ (-(ξ * x)) ∂μ := by
  set K : ℕ := (max ((m : ℤ) - 1) (n + (c : ℤ) - e)).toNat with hK
  have hKm : (m : ℤ) - 1 ≤ K := (le_max_left _ _).trans (Int.self_le_toNat _)
  have hKn : n + (c : ℤ) - e ≤ K := (le_max_right _ _).trans (Int.self_le_toNat _)
  change ∫ x, untwisted χ s A B x * ψ (-(ξ * x)) ∂μ = _
  set g : v.adicCompletion F → ℂ := fun x => untwisted χ s A B x * ψ (-(ξ * x)) with hg_def
  have hgi : Integrable g μ := integrable_twisted_aux μ ϖ hϖ χ c hχ m hm A hA B hB s hs ψ n hψn ξ
  have hO : MeasurableSet (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    isOpen_integers.measurableSet
  set tail : Set (v.adicCompletion F) := {x | WithZero.exp (K : ℤ) < Valued.v x} with htail_def
  have hmeasT : MeasurableSet tail := measurableSet_setOf_exp_lt (K : ℤ)
  have hmeasS : ∀ k ∈ Finset.Icc 1 K,
      MeasurableSet {x : v.adicCompletion F | Valued.v x = WithZero.exp (k : ℤ)} :=
    fun k _ => measurableSet_setOf_valued_eq (k : ℤ)

  have hsplit1 : ∫ x, g x ∂μ
      = (∫ x in (v.adicCompletionIntegers F : Set (v.adicCompletion F)), g x ∂μ)
        + ∫ x in (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ, g x ∂μ :=
    (integral_add_compl hO hgi).symm
  have hOterm : ∫ x in (v.adicCompletionIntegers F : Set (v.adicCompletion F)), g x ∂μ
      = ∫ x in (v.adicCompletionIntegers F : Set (v.adicCompletion F)), A x * ψ (-(ξ * x)) ∂μ := by
    refine setIntegral_congr_fun hO fun x hx => ?_
    simp only [hg_def, untwisted, Set.indicator_of_mem hx,
      Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hx), add_zero]

  have hcover : (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ
      = (⋃ k ∈ Finset.Icc 1 K, {x : v.adicCompletion F | Valued.v x = WithZero.exp (k : ℤ)}) ∪ tail := by
    ext x
    simp only [Set.mem_compl_iff, SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, not_le, Set.mem_union,
      Set.mem_iUnion, Finset.mem_Icc, exists_prop, htail_def, Set.mem_setOf_eq]
    constructor
    · intro h1
      have hx0 : Valued.v x ≠ 0 := (lt_trans zero_lt_one h1).ne'
      obtain ⟨j, hj⟩ : ∃ j : ℤ, Valued.v x = WithZero.exp j := ⟨_, (WithZero.exp_log hx0).symm⟩
      have hj0 : 0 < j := by
        rw [hj, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
        exact h1
      by_cases hjK : j ≤ K
      · left
        refine ⟨j.toNat, ⟨by omega, by omega⟩, ?_⟩
        rw [hj]
        congr 1
        omega
      · right
        rw [hj, WithZero.exp_lt_exp]
        omega
    · rintro (⟨k, ⟨hk1, -⟩, hxk⟩ | hxt)
      · rw [hxk, ← WithZero.exp_zero, WithZero.exp_lt_exp]
        omega
      · refine lt_of_le_of_lt ?_ hxt
        rw [← WithZero.exp_zero, WithZero.exp_le_exp]
        omega
  have hpair : Set.Pairwise (↑(Finset.Icc 1 K) : Set ℕ)
      (Function.onFun Disjoint
        fun k : ℕ => {x : v.adicCompletion F | Valued.v x = WithZero.exp (k : ℤ)}) := by
    intro i _ j _ hij
    show Disjoint {x : v.adicCompletion F | Valued.v x = WithZero.exp (i : ℤ)}
      {x : v.adicCompletion F | Valued.v x = WithZero.exp (j : ℤ)}
    rw [Set.disjoint_left]
    intro x hxi hxj
    change Valued.v x = WithZero.exp (i : ℤ) at hxi
    change Valued.v x = WithZero.exp (j : ℤ) at hxj
    apply hij
    have h := WithZero.exp_inj.mp (hxi.symm.trans hxj)
    exact_mod_cast h
  have hdisjUT : Disjoint
      (⋃ k ∈ Finset.Icc 1 K, {x : v.adicCompletion F | Valued.v x = WithZero.exp (k : ℤ)}) tail := by
    rw [Set.disjoint_left]
    intro x hx hxt
    simp only [Set.mem_iUnion, exists_prop, Finset.mem_Icc] at hx
    obtain ⟨k, ⟨-, hkK⟩, hxk⟩ := hx
    change Valued.v x = WithZero.exp (k : ℤ) at hxk
    change WithZero.exp (K : ℤ) < Valued.v x at hxt
    rw [hxk, WithZero.exp_lt_exp] at hxt
    omega
  have hsplit2 : ∫ x in (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ, g x ∂μ
      = (∑ k ∈ Finset.Icc 1 K,
          ∫ x in {x : v.adicCompletion F | Valued.v x = WithZero.exp (k : ℤ)}, g x ∂μ)
        + ∫ x in tail, g x ∂μ := by
    rw [hcover, setIntegral_union hdisjUT hmeasT hgi.integrableOn hgi.integrableOn,
      integral_biUnion_finset _ hmeasS hpair fun k _ => hgi.integrableOn]

  have htail0 : ∫ x in tail, g x ∂μ = 0 := by
    obtain ⟨x₀, hx₀v, hx₀⟩ := hψn'
    have hvξ : Valued.v ξ ≠ 0 := by
      rw [hξ]
      exact WithZero.coe_ne_zero
    have hξ0 : ξ ≠ 0 := (Valuation.ne_zero_iff _).mp hvξ
    set t : v.adicCompletion F := -(ξ⁻¹ * x₀) with ht_def
    have hvt : Valued.v t ≤ WithZero.exp (n + 1 - e) := by
      rw [ht_def, Valuation.map_neg, map_mul, map_inv₀, hξ, ← WithZero.exp_neg]
      calc WithZero.exp (-e) * Valued.v x₀
          ≤ WithZero.exp (-e) * WithZero.exp (n + 1) := by gcongr
        _ = WithZero.exp (n + 1 - e) := by
          rw [← WithZero.exp_add]
          congr 1
          ring
    have hψt : ∀ x : v.adicCompletion F, ψ (-(ξ * (t + x))) = ψ (-(ξ * x)) * ψ x₀ := by
      intro x
      have h : -(ξ * (t + x)) = -(ξ * x) + x₀ := by
        rw [ht_def]
        field_simp
        ring
      rw [h, AddChar.map_add_eq_mul]
    have hinv : ∀ x : v.adicCompletion F, tail.indicator g (t + x) = tail.indicator g x * ψ x₀ := by
      intro x
      by_cases hx : x ∈ tail
      · have hx' : WithZero.exp (K : ℤ) < Valued.v x := hx
        have hx0 : Valued.v x ≠ 0 := (lt_of_le_of_lt zero_le' hx').ne'
        obtain ⟨j, hj⟩ : ∃ j : ℤ, Valued.v x = WithZero.exp j := ⟨_, (WithZero.exp_log hx0).symm⟩
        have hjK : (K : ℤ) < j := by
          rw [hj, WithZero.exp_lt_exp] at hx'
          exact hx'
        have htj : Valued.v t ≤ WithZero.exp (j - c) :=
          hvt.trans (WithZero.exp_le_exp.mpr (by omega))
        have htlt : Valued.v t < Valued.v x := by
          rw [hj]
          exact lt_of_le_of_lt htj (WithZero.exp_lt_exp.mpr (by omega))
        have hvtx : Valued.v (t + x) = Valued.v x := Valued.v.map_add_eq_of_lt_right htlt
        have htx : t + x ∈ tail := by
          show WithZero.exp (K : ℤ) < Valued.v (t + x)
          rw [hvtx]
          exact hx'
        rw [Set.indicator_of_mem htx, Set.indicator_of_mem hx, hg_def]
        simp only
        rw [untwisted_add_eq_of_sphere χ c hc hχ m hm s A B hB (by omega) hj htj, hψt x, mul_assoc]
      · have htx : t + x ∉ tail := by
          intro htx
          apply hx
          have htx' : WithZero.exp (K : ℤ) < Valued.v (t + x) := htx
          have h0 : Valued.v (t + x) ≠ 0 := (lt_of_le_of_lt zero_le' htx').ne'
          obtain ⟨j, hj⟩ : ∃ j : ℤ, Valued.v (t + x) = WithZero.exp j := ⟨_, (WithZero.exp_log h0).symm⟩
          have hjK : (K : ℤ) < j := by
            rw [hj, WithZero.exp_lt_exp] at htx'
            exact htx'
          have htlt : Valued.v (-t) < Valued.v (t + x) := by
            rw [Valuation.map_neg, hj]
            exact lt_of_le_of_lt hvt (WithZero.exp_lt_exp.mpr (by omega))
          have hxeq : Valued.v x = Valued.v (t + x) := by
            have hx' : x = (t + x) + -t := by ring
            conv_lhs => rw [hx']
            exact Valued.v.map_add_eq_of_lt_left htlt
          show WithZero.exp (K : ℤ) < Valued.v x
          rw [hxeq]
          exact htx'
        rw [Set.indicator_of_notMem htx, Set.indicator_of_notMem hx, zero_mul]
    rw [← integral_indicator hmeasT]
    have h2 : ∫ x, tail.indicator g x ∂μ = (∫ x, tail.indicator g x ∂μ) * ψ x₀ := by
      calc ∫ x, tail.indicator g x ∂μ
          = ∫ x, tail.indicator g (t + x) ∂μ := (integral_add_left_eq_self (tail.indicator g) t).symm
        _ = ∫ x, tail.indicator g x * ψ x₀ ∂μ := by
            congr 1
            funext x
            exact hinv x
        _ = (∫ x, tail.indicator g x ∂μ) * ψ x₀ := by rw [integral_mul_const]
    have h3 : (∫ x, tail.indicator g x ∂μ) * (ψ x₀ - 1) = 0 := by
      rw [mul_sub, mul_one, ← h2, sub_self]
    exact (mul_eq_zero.mp h3).resolve_right (sub_ne_zero.mpr hx₀)

  have hsphere : ∀ k ∈ Finset.Icc 1 K,
      ∫ x in {x : v.adicCompletion F | Valued.v x = WithZero.exp (k : ℤ)}, g x ∂μ
        = (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1))) ^ k
            * ∫ x in {x : v.adicCompletion F | Valued.v x = WithZero.exp (k : ℤ)},
                LanglandsTunnell.TateLocal.charExt χ⁻¹ x * B x⁻¹ * ψ (-(ξ * x)) ∂μ := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    rw [← integral_const_mul]
    refine setIntegral_congr_fun (measurableSet_setOf_valued_eq (k : ℤ)) fun x hx => ?_
    change Valued.v x = WithZero.exp (k : ℤ) at hx
    have hxO : x ∉ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
      show x ∉ v.adicCompletionIntegers F
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, hx, ← WithZero.exp_zero, not_le, WithZero.exp_lt_exp]
      omega
    simp only [hg_def, untwisted, Set.indicator_of_notMem hxO, Set.indicator_of_mem (Set.mem_compl hxO),
      zero_add]
    rw [coe_modulus_of_valued_eq hx, zpow_natCast, ofReal_pow_cpow (Nat.cast_nonneg _)]
    push_cast
    ring

  rw [hsplit1, hsplit2, htail0, add_zero, hOterm]
  congr 1
  exact Finset.sum_congr rfl hsphere

end TwistedSmoothLocal

theorem solution
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (ϖ : (v.adicCompletion F)ˣ) (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (v.adicCompletion F)ˣ →* ℂˣ)
    (c : ℕ) (hc : 1 ≤ c) (hχ : ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt F v c, χ u = 1)
    (m : ℕ) (hm : 1 ≤ m)
    (A : v.adicCompletion F → ℂ)
    (hA : IntegrableOn A (v.adicCompletionIntegers F : Set (v.adicCompletion F)) μ)
    (B : v.adicCompletion F → ℂ)
    (hB : ∀ x y : v.adicCompletion F, Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B y = B x)
    (s : ℂ) (hs : ‖((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))‖ < 1)
    (ψ : AddChar (v.adicCompletion F) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (hψn' : ∃ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1)
    (ξ : v.adicCompletion F) (e : ℤ) (hξ : Valued.v ξ = WithZero.exp e) :
    ∫ x, (((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator A x
          + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
              (fun y => LanglandsTunnell.TateLocal.charExt χ⁻¹ y
                * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1)) * B y⁻¹) x)
          * ψ (-(ξ * x))) ∂μ
      = (∫ x in (v.adicCompletionIntegers F : Set (v.adicCompletion F)), A x * ψ (-(ξ * x)) ∂μ)
        + ∑ k ∈ Finset.Icc 1 (max ((m : ℤ) - 1) (n + (c : ℤ) - e)).toNat,
            (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1))) ^ k
              * ∫ x in {x : v.adicCompletion F | Valued.v x = WithZero.exp (k : ℤ)},
                  LanglandsTunnell.TateLocal.charExt χ⁻¹ x * B x⁻¹ * ψ (-(ξ * x)) ∂μ :=
  TwistedSmoothLocal.integral_twisted_smooth_eq F v μ ϖ hϖ χ c hc hχ m hm A hA B hB s hs ψ n hψn hψn' ξ e hξ

end
end S_EisensteinGeneral_LocalRam_integral_twisted_smooth_eq
end P2MW
export P2MW.S_EisensteinGeneral_LocalRam_integral_twisted_smooth_eq (solution)
