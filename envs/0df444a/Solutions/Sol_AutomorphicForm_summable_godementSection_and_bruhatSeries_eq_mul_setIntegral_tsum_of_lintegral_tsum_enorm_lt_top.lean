-- Prove2me | solution 1 for AutomorphicForm.summable_godementSection_and_bruhatSeries_eq_mul_setIntegral_tsum_of_lintegral_tsum_enorm_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/de8c4760-58a9-5e24-9693-480af841fcfa

import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_summable_godementSection_and_bruhatSeries_eq_mul_setIntegral_tsum_of_lintegral_tsum_enorm_lt_top
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.TateGlobal AutomorphicForm Matrix Filter Topology
open scoped ENNReal NNReal

namespace GodementUnfold

variable {F : Type} [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F

abbrev prin (a : Fˣ) : (𝔸)ˣ := Units.map (algebraMap F 𝔸 : F →* 𝔸) a

variable (F) in

abbrev Γ : Subgroup (𝔸)ˣ := (Units.map (algebraMap F 𝔸 : F →* 𝔸)).range

theorem prin_injective : Function.Injective (prin (F := F)) := by
  intro a b h
  apply Units.ext
  have h' := congrArg (fun u : (𝔸)ˣ => (u : 𝔸)) h
  exact NumberField.AdeleRing.algebraMap_injective (𝓞 F) F h'

theorem coe_prin (a : Fˣ) : ((prin a : (𝔸)ˣ) : 𝔸) = algebraMap F 𝔸 (a : F) := rfl

def prinEquiv : Fˣ ≃ ↥(Γ F) :=
  (MonoidHom.ofInjective (f := (Units.map (algebraMap F 𝔸 : F →* 𝔸))) prin_injective).toEquiv

theorem coe_prinEquiv (a : Fˣ) : ((prinEquiv a : ↥(Γ F)) : (𝔸)ˣ) = prin a := rfl

theorem ideleNorm_prin (a : Fˣ) : ideleNorm F (prin a) = 1 := by
  unfold ideleNorm
  letI : MeasurableSpace 𝔸 := borel _
  haveI : BorelSpace 𝔸 := ⟨rfl⟩
  have h := NumberField.AdeleRing.distribHaarChar_algebraMap F a
  exact_mod_cast h

theorem chi_prin {μ ν : (𝔸)ˣ →* ℂˣ} (hμ : IsIdeleClassChar (𝓞 F) F μ) (hν : IsIdeleClassChar (𝓞 F) F ν) (a : Fˣ) :
    (μ * ν⁻¹) (prin a) = 1 := by
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hμ a, hν a, inv_one, one_mul]

theorem map_neg_one_of_isIdeleClassChar {χ : (𝔸)ˣ →* ℂˣ} (hχ : IsIdeleClassChar (𝓞 F) F χ) : χ (-1) = 1 := by
  have h := hχ (-1)
  have e : Units.map (algebraMap F 𝔸 : F →* 𝔸) (-1) = -1 := by
    apply Units.ext; simp
  rwa [e] at h

theorem map_neg_one_eq_one_of_pos (α : (𝔸)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) : α (-1) = 1 := by
  have h2 : ((α (-1) : ℝˣ) : ℝ) * ((α (-1) : ℝˣ) : ℝ) = 1 := by
    rw [← Units.val_mul, ← map_mul, neg_mul_neg, one_mul, map_one, Units.val_one]
  have hpos := hα (-1)
  apply Units.ext
  rw [Units.val_one]
  nlinarith [hpos, h2]

theorem countable_numberField : Countable F :=
  (Module.Free.chooseBasis ℚ F).equivFun.toEquiv.countable_iff.2 inferInstance

scoped instance countable_units_numberField : Countable Fˣ := by
  haveI := countable_numberField (F := F)
  exact Function.Injective.countable (f := (Units.val : Fˣ → F)) Units.val_injective

scoped instance countable_Gamma : Countable ↥(Γ F) :=
  (MonoidHom.rangeRestrict_surjective (Units.map (algebraMap F 𝔸 : F →* 𝔸))).countable

scoped instance countable_nonzeroVec : Countable {ξ : Fin 2 → F // ξ ≠ 0} := by
  haveI := countable_numberField (F := F)
  infer_instance

variable (F) in

def iota (v : Fin 2 → F) : Fin 2 → 𝔸 := fun i => algebraMap F 𝔸 (v i)

theorem iota_smul (a : F) (v : Fin 2 → F) : iota F (a • v) = algebraMap F 𝔸 a • iota F v := by
  funext i; simp [iota]

def rho (g : AdelicGL2 (𝓞 F) F) (v : Fin 2 → F) (t : (𝔸)ˣ) : Fin 2 → 𝔸 :=
  (t : 𝔸) • Matrix.vecMul (iota F v) (g : Matrix (Fin 2) (Fin 2) 𝔸)

theorem rho_prin_mul (g : AdelicGL2 (𝓞 F) F) (v : Fin 2 → F) (a : Fˣ) (t : (𝔸)ˣ) :
    rho g v (prin a * t) = rho g ((a : F) • v) t := by
  unfold rho
  rw [iota_smul, Matrix.smul_vecMul, smul_smul, Units.val_mul, coe_prin, mul_comm]

def G (Φ : (Fin 2 → 𝔸) → ℂ) (χ : (𝔸)ˣ →* ℂˣ) (s' : ℂ) (g : AdelicGL2 (𝓞 F) F) (v : Fin 2 → F) (t : (𝔸)ˣ) : ℂ :=
  Φ (rho g v t) * ((χ t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ s'

theorem G_prin_mul (Φ : (Fin 2 → 𝔸) → ℂ) {μ ν : (𝔸)ˣ →* ℂˣ} (hμ : IsIdeleClassChar (𝓞 F) F μ)
    (hν : IsIdeleClassChar (𝓞 F) F ν) (s' : ℂ) (g : AdelicGL2 (𝓞 F) F) (v : Fin 2 → F) (a : Fˣ) (t : (𝔸)ˣ) :
    G Φ (μ * ν⁻¹) s' g v (prin a * t) = G Φ (μ * ν⁻¹) s' g ((a : F) • v) t := by
  unfold G
  rw [rho_prin_mul, map_mul, chi_prin hμ hν, one_mul, ideleNorm_mul, ideleNorm_prin, one_mul]

def vrep : Unit ⊕ F → (Fin 2 → F)
  | Sum.inl _ => ![0, 1]
  | Sum.inr ξ => ![1, ξ]

theorem smul_vrep_ne_zero (o : Unit ⊕ F) (a : Fˣ) : (a : F) • vrep o ≠ 0 := by
  intro h
  rcases o with _ | ξ
  · have := congrFun h 1
    simp [vrep] at this
  · have := congrFun h 0
    simp [vrep] at this

def orb (p : (Unit ⊕ F) × Fˣ) : {ξ : Fin 2 → F // ξ ≠ 0} := ⟨(p.2 : F) • vrep p.1, smul_vrep_ne_zero p.1 p.2⟩

theorem snd_ne_zero_of_fst_eq_zero {ξ : Fin 2 → F} (hξ : ξ ≠ 0) (h0 : ξ 0 = 0) : ξ 1 ≠ 0 := by
  intro h1
  apply hξ
  funext i
  fin_cases i
  · exact h0
  · exact h1

open scoped Classical in

def orbInv (ξ : {ξ : Fin 2 → F // ξ ≠ 0}) : (Unit ⊕ F) × Fˣ :=
  if h : ξ.1 0 = 0 then (Sum.inl (), Units.mk0 (ξ.1 1) (snd_ne_zero_of_fst_eq_zero ξ.2 h))
  else (Sum.inr (ξ.1 1 / ξ.1 0), Units.mk0 (ξ.1 0) h)

def orbEquiv : (Unit ⊕ F) × Fˣ ≃ {ξ : Fin 2 → F // ξ ≠ 0} where
  toFun := orb
  invFun := orbInv
  left_inv := by
    classical
    rintro ⟨o, a⟩
    rcases o with u | ξ
    · have h0 : ((a : F) • vrep (F := F) (Sum.inl u)) 0 = 0 := by simp [vrep]
      simp only [orb, orbInv, h0, dif_pos]
      refine Prod.ext rfl (Units.ext ?_)
      simp [vrep]
    · have h0 : ((a : F) • vrep (Sum.inr ξ)) 0 ≠ 0 := by simp [vrep]
      simp only [orb, orbInv, h0, dif_neg, not_false_eq_true]
      refine Prod.ext ?_ (Units.ext ?_)
      · simp [vrep]
      · simp [vrep]
  right_inv := by
    classical
    rintro ⟨ξ, hξ⟩
    by_cases h0 : ξ 0 = 0
    · simp only [orbInv, h0, dif_pos, orb]
      apply Subtype.ext
      funext i
      fin_cases i
      · simp [vrep, h0]
      · simp [vrep]
    · simp only [orbInv, h0, dif_neg, not_false_eq_true, orb]
      apply Subtype.ext
      funext i
      fin_cases i
      · simp [vrep]
      · simp [vrep]
        field_simp

theorem orbEquiv_apply_val (o : Unit ⊕ F) (a : Fˣ) : ((orbEquiv (o, a) : {ξ : Fin 2 → F // ξ ≠ 0}) : Fin 2 → F)
    = (a : F) • vrep o := rfl

theorem orb_injective_snd (o : Unit ⊕ F) : Function.Injective fun a : Fˣ => orbEquiv (F := F) (o, a) := by
  intro a b h
  have := orbEquiv.injective h
  exact (Prod.mk.inj this).2

section Measure

variable [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]

theorem continuous_rho (g : AdelicGL2 (𝓞 F) F) (v : Fin 2 → F) : Continuous (rho g v) := by
  unfold rho
  exact Units.continuous_val.smul continuous_const

theorem continuous_chi {μ ν : (𝔸)ˣ →* ℂˣ} (hμc : Continuous fun x : (𝔸)ˣ => ((μ x : ℂˣ) : ℂ))
    (hνc : Continuous fun x : (𝔸)ˣ => ((ν x : ℂˣ) : ℂ)) :
    Continuous fun x : (𝔸)ˣ => (((μ * ν⁻¹) x : ℂˣ) : ℂ) := by
  have e : (fun x : (𝔸)ˣ => (((μ * ν⁻¹) x : ℂˣ) : ℂ)) = fun x => ((μ x : ℂˣ) : ℂ) * ((ν x : ℂˣ) : ℂ)⁻¹ := by
    funext x
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val]
  rw [e]
  exact hμc.mul (hνc.inv₀ fun x => Units.ne_zero _)

theorem continuous_ideleNorm_cpow (s' : ℂ) : Continuous fun t : (𝔸)ˣ => ((ideleNorm F t : ℝ) : ℂ) ^ s' := by
  have hc : Continuous fun t : (𝔸)ˣ => ((ideleNorm F t : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (NumberField.TateGlobal.continuous_ideleNorm F)
  refine continuous_iff_continuousAt.2 fun t => ?_
  exact hc.continuousAt.cpow continuousAt_const (Complex.ofReal_mem_slitPlane.2 (ideleNorm_pos t))

theorem continuous_G {Φ : (Fin 2 → 𝔸) → ℂ} (hΦ : Continuous Φ) {μ ν : (𝔸)ˣ →* ℂˣ}
    (hμc : Continuous fun x : (𝔸)ˣ => ((μ x : ℂˣ) : ℂ)) (hνc : Continuous fun x : (𝔸)ˣ => ((ν x : ℂˣ) : ℂ))
    (s' : ℂ) (g : AdelicGL2 (𝓞 F) F) (v : Fin 2 → F) : Continuous (G Φ (μ * ν⁻¹) s' g v) := by
  unfold G
  exact ((hΦ.comp (continuous_rho g v)).mul (continuous_chi hμc hνc)).mul (continuous_ideleNorm_cpow s')

variable (ν₀ : Measure (AdeleRing (𝓞 F) F)ˣ) [ν₀.IsMulLeftInvariant] (Ω : Set (AdeleRing (𝓞 F) F)ˣ)

theorem lintegral_eq_tsum_units (hΩ : IsFundamentalDomain (↥(Γ F)) Ω ν₀) (f : (𝔸)ˣ → ℝ≥0∞) :
    ∫⁻ x, f x ∂ν₀ = ∑' a : Fˣ, ∫⁻ x in Ω, f (prin a * x) ∂ν₀ := by
  rw [hΩ.lintegral_eq_tsum'' f]
  rw [← Equiv.tsum_eq prinEquiv]
  rfl

theorem integral_eq_tsum_units (hΩ : IsFundamentalDomain (↥(Γ F)) Ω ν₀) (f : (𝔸)ˣ → ℂ) (hf : Integrable f ν₀) :
    ∫ x, f x ∂ν₀ = ∑' a : Fˣ, ∫ x in Ω, f (prin a * x) ∂ν₀ := by
  rw [hΩ.integral_eq_tsum'' f hf]
  rw [← Equiv.tsum_eq prinEquiv]
  rfl

variable {ν₀ Ω}
variable (hΩ : IsFundamentalDomain (↥(Γ F)) Ω ν₀)
  {Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Continuous Φ) {μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}
  (hμ : IsIdeleClassChar (𝓞 F) F μ) (hν : IsIdeleClassChar (𝓞 F) F ν)
  (hμc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
  (hνc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
  (s' : ℂ) (g : AdelicGL2 (𝓞 F) F)
  (habs : ∫⁻ t in Ω, ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0}, ‖G Φ (μ * ν⁻¹) s' g ξ.1 t‖ₑ ∂ν₀ < ⊤)

include hΩ hΦ hμ hν hμc hνc habs

theorem lintegral_enorm_G_vrep_lt_top (o : Unit ⊕ F) :
    ∫⁻ t, ‖G Φ (μ * ν⁻¹) s' g (vrep o) t‖ₑ ∂ν₀ < ⊤ := by
  rw [lintegral_eq_tsum_units ν₀ Ω hΩ]
  have h1 : ∀ a : Fˣ, (fun t => ‖G Φ (μ * ν⁻¹) s' g (vrep o) (prin a * t)‖ₑ)
      = fun t => ‖G Φ (μ * ν⁻¹) s' g ((a : F) • vrep o) t‖ₑ := by
    intro a; funext t; rw [G_prin_mul Φ hμ hν]
  simp_rw [h1]
  rw [← lintegral_tsum fun a => ((continuous_G hΦ hμc hνc s' g _).aestronglyMeasurable.enorm).restrict]
  refine lt_of_le_of_lt (lintegral_mono fun t => ?_) habs
  exact ENNReal.tsum_comp_le_tsum_of_injective (orb_injective_snd o)
    (fun ξ : {ξ : Fin 2 → F // ξ ≠ 0} => ‖G Φ (μ * ν⁻¹) s' g ξ.1 t‖ₑ)

theorem integrable_G_vrep (o : Unit ⊕ F) : Integrable (G Φ (μ * ν⁻¹) s' g (vrep o)) ν₀ :=
  ⟨(continuous_G hΦ hμc hνc s' g _).aestronglyMeasurable,
    lintegral_enorm_G_vrep_lt_top hΩ hΦ hμ hν hμc hνc s' g habs o⟩

theorem integral_G_vrep_eq_tsum (o : Unit ⊕ F) :
    ∫ t, G Φ (μ * ν⁻¹) s' g (vrep o) t ∂ν₀
      = ∑' a : Fˣ, ∫ t in Ω, G Φ (μ * ν⁻¹) s' g ((orbEquiv (o, a) : {ξ : Fin 2 → F // ξ ≠ 0}) : Fin 2 → F) t ∂ν₀ := by
  rw [integral_eq_tsum_units ν₀ Ω hΩ _ (integrable_G_vrep hΩ hΦ hμ hν hμc hνc s' g habs o)]
  refine tsum_congr fun a => ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  show G Φ (μ * ν⁻¹) s' g (vrep o) (prin a * t) = _
  rw [G_prin_mul Φ hμ hν, orbEquiv_apply_val]

theorem summable_setIntegral_G :
    Summable fun ξ : {ξ : Fin 2 → F // ξ ≠ 0} => ∫ t in Ω, G Φ (μ * ν⁻¹) s' g ξ.1 t ∂ν₀ := by
  have hmeas : ∀ ξ : {ξ : Fin 2 → F // ξ ≠ 0},
      AEMeasurable (fun t => ‖G Φ (μ * ν⁻¹) s' g ξ.1 t‖ₑ) (ν₀.restrict Ω) :=
    fun ξ => ((continuous_G hΦ hμc hνc s' g _).aestronglyMeasurable.enorm).restrict
  have hsum : ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0}, ∫⁻ t in Ω, ‖G Φ (μ * ν⁻¹) s' g ξ.1 t‖ₑ ∂ν₀ ≠ ⊤ := by
    rw [← lintegral_tsum hmeas]; exact habs.ne
  refine Summable.of_norm_bounded (ENNReal.summable_toReal hsum) fun ξ => ?_
  simpa only [ofReal_norm_eq_enorm] using norm_integral_le_lintegral_norm (μ := ν₀.restrict Ω)
    (fun t => G Φ (μ * ν⁻¹) s' g ξ.1 t)

theorem tsum_setIntegral_G_eq :
    ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0}, ∫ t in Ω, G Φ (μ * ν⁻¹) s' g ξ.1 t ∂ν₀
      = ∫ t in Ω, ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0}, G Φ (μ * ν⁻¹) s' g ξ.1 t ∂ν₀ := by
  have hmeas : ∀ ξ : {ξ : Fin 2 → F // ξ ≠ 0},
      AEStronglyMeasurable (fun t => G Φ (μ * ν⁻¹) s' g ξ.1 t) (ν₀.restrict Ω) :=
    fun ξ => (continuous_G hΦ hμc hνc s' g _).aestronglyMeasurable.restrict
  have hsum : ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0}, ∫⁻ t in Ω, ‖G Φ (μ * ν⁻¹) s' g ξ.1 t‖ₑ ∂ν₀ ≠ ⊤ := by
    rw [← lintegral_tsum fun ξ => (hmeas ξ).enorm]; exact habs.ne
  exact (integral_tsum hmeas hsum).symm

theorem integrableOn_tsum_G :
    IntegrableOn (fun t => ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0}, G Φ (μ * ν⁻¹) s' g ξ.1 t) Ω ν₀ := by
  have hmeas : ∀ ξ : {ξ : Fin 2 → F // ξ ≠ 0},
      AEStronglyMeasurable (fun t => G Φ (μ * ν⁻¹) s' g ξ.1 t) (ν₀.restrict Ω) :=
    fun ξ => (continuous_G hΦ hμc hνc s' g _).aestronglyMeasurable.restrict
  refine ⟨?_, ?_⟩
  · exact (AEMeasurable.tsum (L := SummationFilter.unconditional _) fun ξ => (hmeas ξ).aemeasurable).aestronglyMeasurable
  · unfold HasFiniteIntegral
    calc ∫⁻ t in Ω, ‖∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0}, G Φ (μ * ν⁻¹) s' g ξ.1 t‖ₑ ∂ν₀
        ≤ ∫⁻ t in Ω, ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0}, ‖G Φ (μ * ν⁻¹) s' g ξ.1 t‖ₑ ∂ν₀ :=
          lintegral_mono fun t => enorm_tsum_le_tsum_enorm
      _ < ⊤ := habs

omit [ν₀.IsMulLeftInvariant] hΩ hΦ hμ hν hμc hνc habs in

theorem fibre_eq (o : Unit ⊕ F) (a : Fˣ) :
    ((fun ξ : {ξ : Fin 2 → F // ξ ≠ 0} => ∫ t in Ω, G Φ (μ * ν⁻¹) s' g ξ.1 t ∂ν₀) ∘ (orbEquiv (F := F))) (o, a)
      = ∫ t in Ω, G Φ (μ * ν⁻¹) s' g ((orbEquiv (o, a) : {ξ : Fin 2 → F // ξ ≠ 0}) : Fin 2 → F) t ∂ν₀ := rfl

theorem hasSum_integral_G_vrep :
    HasSum (fun o : Unit ⊕ F => ∫ t, G Φ (μ * ν⁻¹) s' g (vrep o) t ∂ν₀)
      (∫ t in Ω, ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0}, G Φ (μ * ν⁻¹) s' g ξ.1 t ∂ν₀) := by
  have hIsum : Summable fun ξ : {ξ : Fin 2 → F // ξ ≠ 0} => ∫ t in Ω, G Φ (μ * ν⁻¹) s' g ξ.1 t ∂ν₀ :=
    summable_setIntegral_G hΩ hΦ hμ hν hμc hνc s' g habs
  have hIhas : HasSum (fun ξ : {ξ : Fin 2 → F // ξ ≠ 0} => ∫ t in Ω, G Φ (μ * ν⁻¹) s' g ξ.1 t ∂ν₀)
      (∫ t in Ω, ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0}, G Φ (μ * ν⁻¹) s' g ξ.1 t ∂ν₀) := by
    rw [← tsum_setIntegral_G_eq hΩ hΦ hμ hν hμc hνc s' g habs]
    exact hIsum.hasSum
  have hE : HasSum ((fun ξ : {ξ : Fin 2 → F // ξ ≠ 0} => ∫ t in Ω, G Φ (μ * ν⁻¹) s' g ξ.1 t ∂ν₀) ∘ (orbEquiv (F := F)))
      (∫ t in Ω, ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0}, G Φ (μ * ν⁻¹) s' g ξ.1 t ∂ν₀) :=
    (Equiv.hasSum_iff orbEquiv).2 hIhas
  refine HasSum.prod_fiberwise hE fun o => ?_
  have hfib : Summable fun a : Fˣ =>
      ((fun ξ : {ξ : Fin 2 → F // ξ ≠ 0} => ∫ t in Ω, G Φ (μ * ν⁻¹) s' g ξ.1 t ∂ν₀) ∘ (orbEquiv (F := F))) (o, a) :=
    hE.summable.prod_factor o
  rw [hfib.hasSum_iff, integral_G_vrep_eq_tsum hΩ hΦ hμ hν hμc hνc s' g habs o]
  exact tsum_congr fun a => fibre_eq s' g o a

theorem summable_and_tsum_eq :
    Summable (fun ξ : F => ∫ t, G Φ (μ * ν⁻¹) s' g (vrep (Sum.inr ξ)) t ∂ν₀) ∧
    (∫ t, G Φ (μ * ν⁻¹) s' g (vrep (Sum.inl ())) t ∂ν₀)
        + ∑' ξ : F, ∫ t, G Φ (μ * ν⁻¹) s' g (vrep (Sum.inr ξ)) t ∂ν₀
      = ∫ t in Ω, ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0}, G Φ (μ * ν⁻¹) s' g ξ.1 t ∂ν₀ := by
  have h := hasSum_integral_G_vrep hΩ hΦ hμ hν hμc hνc s' g habs
  have hs : Summable fun o : Unit ⊕ F => ∫ t, G Φ (μ * ν⁻¹) s' g (vrep o) t ∂ν₀ := h.summable
  have h1 : Summable ((fun o : Unit ⊕ F => ∫ t, G Φ (μ * ν⁻¹) s' g (vrep o) t ∂ν₀) ∘ Sum.inl) :=
    hs.comp_injective Sum.inl_injective
  have h2 : Summable ((fun o : Unit ⊕ F => ∫ t, G Φ (μ * ν⁻¹) s' g (vrep o) t ∂ν₀) ∘ Sum.inr) :=
    hs.comp_injective Sum.inr_injective
  refine ⟨h2, ?_⟩
  have e : ∑' o, (fun o : Unit ⊕ F => ∫ t, G Φ (μ * ν⁻¹) s' g (vrep o) t ∂ν₀) o
      = ∑' u : Unit, (fun o : Unit ⊕ F => ∫ t, G Φ (μ * ν⁻¹) s' g (vrep o) t ∂ν₀) (Sum.inl u)
        + ∑' ξ : F, (fun o : Unit ⊕ F => ∫ t, G Φ (μ * ν⁻¹) s' g (vrep o) t ∂ν₀) (Sum.inr ξ) :=
    Summable.tsum_sum h1 h2
  have e2 : ∑' u : Unit, (fun o : Unit ⊕ F => ∫ t, G Φ (μ * ν⁻¹) s' g (vrep o) t ∂ν₀) (Sum.inl u)
      = ∫ t, G Φ (μ * ν⁻¹) s' g (vrep (Sum.inl ())) t ∂ν₀ := by
    rw [tsum_fintype]
    simp
  rw [← h.tsum_eq, e, e2]

end Measure

theorem adelicWeyl_coe :
    ((adelicWeyl (𝓞 F) F : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) 𝔸) = !![0, 1; 1, 0] := by
  ext i j
  change algebraMap F 𝔸 ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F) i j) = _
  fin_cases i <;> fin_cases j <;> simp

theorem adelicWeyl_mul_unipotentGL2_coe (x : 𝔸) :
    ((adelicWeyl (𝓞 F) F * unipotentGL2 x : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) 𝔸) = !![0, 1; 1, x] := by
  rw [Matrix.GeneralLinearGroup.coe_mul, adelicWeyl_coe, unipotentGL2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem bottomRowVec_bigCell (ξ : F) (g : AdelicGL2 (𝓞 F) F) (t : (𝔸)ˣ) :
    bottomRowVec F (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F 𝔸 ξ) * g) t = rho g (vrep (Sum.inr ξ)) t := by
  funext j
  simp only [bottomRowVec, Matrix.GeneralLinearGroup.coe_mul, rho, vrep, Pi.smul_apply, smul_eq_mul]
  rw [show ((adelicWeyl (𝓞 F) F : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) 𝔸)
      * ((unipotentGL2 (algebraMap F 𝔸 ξ) : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) 𝔸) = !![0, 1; 1, algebraMap F 𝔸 ξ]
    from by rw [← Matrix.GeneralLinearGroup.coe_mul, adelicWeyl_mul_unipotentGL2_coe]]
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, iota]

theorem bottomRowVec_idCell (g : AdelicGL2 (𝓞 F) F) (t : (𝔸)ˣ) :
    bottomRowVec F g t = rho g (vrep (Sum.inl ())) t := by
  funext j
  simp [bottomRowVec, rho, vrep, iota, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem det_bigCell (x : 𝔸) (g : AdelicGL2 (𝓞 F) F) :
    Matrix.GeneralLinearGroup.det (adelicWeyl (𝓞 F) F * unipotentGL2 x * g) = -Matrix.GeneralLinearGroup.det g := by
  apply Units.ext
  rw [map_mul, Units.val_mul, Units.val_neg, Matrix.GeneralLinearGroup.val_det_apply,
    Matrix.GeneralLinearGroup.val_det_apply, adelicWeyl_mul_unipotentGL2_coe, Matrix.det_fin_two_of]
  ring

theorem godementSection_idCell {mI : MeasurableSpace (𝔸)ˣ} (ν₀ : Measure (𝔸)ˣ) (μ ν : (𝔸)ˣ →* ℂˣ)
    (α : (𝔸)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (Φ : (Fin 2 → 𝔸) → ℂ) (s : ℂ) (g : AdelicGL2 (𝓞 F) F) :
    godementSection F ν₀ μ ν α hα Φ s g
      = ((μ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)
        * ((cpowChar α hα (s + 1 / 2) (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)
        * ∫ t, G Φ (μ * ν⁻¹) (2 * s + 1) g (vrep (Sum.inl ())) t ∂ν₀ := by
  unfold godementSection zetaIntegral G
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only
  rw [bottomRowVec_idCell]

theorem godementSection_bigCell {mI : MeasurableSpace (𝔸)ˣ} (ν₀ : Measure (𝔸)ˣ) {μ : (𝔸)ˣ →* ℂˣ}
    (hμ : IsIdeleClassChar (𝓞 F) F μ) (ν : (𝔸)ˣ →* ℂˣ) (α : (𝔸)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (Φ : (Fin 2 → 𝔸) → ℂ) (s : ℂ) (ξ : F) (g : AdelicGL2 (𝓞 F) F) :
    godementSection F ν₀ μ ν α hα Φ s (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F 𝔸 ξ) * g)
      = ((μ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)
        * ((cpowChar α hα (s + 1 / 2) (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)
        * ∫ t, G Φ (μ * ν⁻¹) (2 * s + 1) g (vrep (Sum.inr ξ)) t ∂ν₀ := by
  unfold godementSection zetaIntegral G
  rw [det_bigCell, ← neg_one_mul, map_mul, map_mul, map_neg_one_of_isIdeleClassChar hμ, one_mul]
  have hc : cpowChar α hα (s + 1 / 2) (-1 : (𝔸)ˣ) = 1 := by
    apply Units.ext
    rw [cpowChar_apply_val, map_neg_one_eq_one_of_pos α hα, Units.val_one, Complex.ofReal_one, Complex.one_cpow,
      Units.val_one]
  rw [hc, one_mul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only
  rw [bottomRowVec_bigCell]

theorem main
    [MeasurableSpace (𝔸)ˣ] [BorelSpace (𝔸)ˣ]
    (ν₀ : Measure (𝔸)ˣ) [ν₀.IsMulLeftInvariant]
    (Ω : Set (𝔸)ˣ)
    (hΩ : IsFundamentalDomain (Units.map (algebraMap F 𝔸 : F →* 𝔸)).range Ω ν₀)
    (μ ν : (𝔸)ˣ →* ℂˣ)
    (hμ : IsIdeleClassChar (𝓞 F) F μ) (hν : IsIdeleClassChar (𝓞 F) F ν)
    (hμc : Continuous fun x : (𝔸)ˣ => ((μ x : ℂˣ) : ℂ))
    (hνc : Continuous fun x : (𝔸)ˣ => ((ν x : ℂˣ) : ℂ))
    (α : (𝔸)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (Φ : (Fin 2 → 𝔸) → ℂ) (hΦ : Continuous Φ)
    (s : ℂ) (g : AdelicGL2 (𝓞 F) F)
    (habs : ∫⁻ t in Ω, ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0},
        ‖Φ ((t : 𝔸) • Matrix.vecMul (fun i => algebraMap F 𝔸 (ξ.1 i)) (g : Matrix (Fin 2) (Fin 2) 𝔸))
          * (((μ * ν⁻¹) t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ (2 * s + 1)‖ₑ ∂ν₀ < ⊤) :
    Summable (fun ξ : F => godementSection F ν₀ μ ν α hα Φ s
        (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F 𝔸 ξ) * g)) ∧
    IntegrableOn (fun t : (𝔸)ˣ => ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0},
        Φ ((t : 𝔸) • Matrix.vecMul (fun i => algebraMap F 𝔸 (ξ.1 i)) (g : Matrix (Fin 2) (Fin 2) 𝔸))
          * (((μ * ν⁻¹) t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ (2 * s + 1)) Ω ν₀ ∧
    godementSection F ν₀ μ ν α hα Φ s g
        + ∑' ξ : F, godementSection F ν₀ μ ν α hα Φ s
            (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F 𝔸 ξ) * g)
      = ((μ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)
        * ((cpowChar α hα (s + 1 / 2) (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)
        * ∫ t in Ω, ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0},
            Φ ((t : 𝔸) • Matrix.vecMul (fun i => algebraMap F 𝔸 (ξ.1 i)) (g : Matrix (Fin 2) (Fin 2) 𝔸))
              * (((μ * ν⁻¹) t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ (2 * s + 1) ∂ν₀ := by

  have habs' : ∫⁻ t in Ω, ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0}, ‖G Φ (μ * ν⁻¹) (2 * s + 1) g ξ.1 t‖ₑ ∂ν₀ < ⊤ := habs
  obtain ⟨hsum, heq⟩ := summable_and_tsum_eq hΩ hΦ hμ hν hμc hνc (2 * s + 1) g habs'
  have hint := integrableOn_tsum_G hΩ hΦ hμ hν hμc hνc (2 * s + 1) g habs'
  refine ⟨?_, hint, ?_⟩
  · simp_rw [godementSection_bigCell ν₀ hμ ν α hα Φ s]
    exact hsum.mul_left _
  · simp_rw [godementSection_bigCell ν₀ hμ ν α hα Φ s, godementSection_idCell ν₀ μ ν α hα Φ s g]
    rw [tsum_mul_left, ← mul_add, heq]
    rfl

end GodementUnfold
p2m_reactivate "P2MW.S_AutomorphicForm_summable_godementSection_and_bruhatSeries_eq_mul_setIntegral_tsum_of_lintegral_tsum_enorm_lt_top.GodementUnfold"

open MeasureTheory NumberField NumberField.TateGlobal AutomorphicForm in
theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν₀ : Measure (AdeleRing (𝓞 F) F)ˣ) [ν₀.IsMulLeftInvariant]
    (Ω : Set (AdeleRing (𝓞 F) F)ˣ)
    (hΩ : IsFundamentalDomain
      (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range Ω ν₀)
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hμ : IsIdeleClassChar (𝓞 F) F μ) (hν : IsIdeleClassChar (𝓞 F) F ν)
    (hμc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
    (hνc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
    (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (hΦ : Continuous Φ)
    (s : ℂ) (g : AdelicGL2 (𝓞 F) F)
    (habs : ∫⁻ t in Ω, ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0},
        ‖Φ ((t : AdeleRing (𝓞 F) F) •
              Matrix.vecMul (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ.1 i))
                (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))
          * (((μ * ν⁻¹) t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ (2 * s + 1)‖ₑ ∂ν₀ < ⊤) :
    Summable (fun ξ : F => godementSection F ν₀ μ ν α hα Φ s
        (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) ∧
    IntegrableOn (fun t : (AdeleRing (𝓞 F) F)ˣ => ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0},
        Φ ((t : AdeleRing (𝓞 F) F) •
              Matrix.vecMul (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ.1 i))
                (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))
          * (((μ * ν⁻¹) t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ (2 * s + 1)) Ω ν₀ ∧
    godementSection F ν₀ μ ν α hα Φ s g
        + ∑' ξ : F, godementSection F ν₀ μ ν α hα Φ s
            (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)
      = ((μ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)
        * ((cpowChar α hα (s + 1 / 2) (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)
        * ∫ t in Ω, ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0},
            Φ ((t : AdeleRing (𝓞 F) F) •
                  Matrix.vecMul (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ.1 i))
                    (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))
              * (((μ * ν⁻¹) t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ (2 * s + 1) ∂ν₀ :=
  GodementUnfold.main ν₀ Ω hΩ μ ν hμ hν hμc hνc α hα Φ hΦ s g habs

end
p2m_reactivate "P2MW.S_AutomorphicForm_summable_godementSection_and_bruhatSeries_eq_mul_setIntegral_tsum_of_lintegral_tsum_enorm_lt_top.GodementUnfold"

end S_AutomorphicForm_summable_godementSection_and_bruhatSeries_eq_mul_setIntegral_tsum_of_lintegral_tsum_enorm_lt_top
end P2MW
export P2MW.S_AutomorphicForm_summable_godementSection_and_bruhatSeries_eq_mul_setIntegral_tsum_of_lintegral_tsum_enorm_lt_top (solution)
