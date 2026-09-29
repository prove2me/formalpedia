-- Prove2me | solution 1 for AutomorphicForm.summable_norm_godementSection_bruhat_and_norm_add_tsum_norm_le_mul_setIntegral_tsum_norm_of_lintegral_tsum_enorm_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/028c6bec-d09d-53b7-9f4a-3af634275408

import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_summable_norm_godementSection_bruhat_and_norm_add_tsum_norm_le_mul_setIntegral_tsum_norm_of_lintegral_tsum_enorm_lt_top
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

theorem continuous_rho (g : AdelicGL2 (𝓞 F) F) (v : Fin 2 → F) : Continuous (rho g v) := by
  unfold rho
  exact Units.continuous_val.smul continuous_const

def Gabs (Φ : (Fin 2 → 𝔸) → ℂ) (σ' : ℝ) (g : AdelicGL2 (𝓞 F) F) (v : Fin 2 → F) (t : (𝔸)ˣ) : ℝ≥0∞ :=
  ‖Φ (rho g v t)‖ₑ * ENNReal.ofReal (ideleNorm F t ^ σ')

theorem Gabs_prin_mul (Φ : (Fin 2 → 𝔸) → ℂ) (σ' : ℝ) (g : AdelicGL2 (𝓞 F) F) (v : Fin 2 → F) (a : Fˣ) (t : (𝔸)ˣ) :
    Gabs Φ σ' g v (prin a * t) = Gabs Φ σ' g ((a : F) • v) t := by
  unfold Gabs
  rw [rho_prin_mul, ideleNorm_mul, ideleNorm_prin, one_mul]

section Measure

variable [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]

theorem measurable_Gabs {Φ : (Fin 2 → 𝔸) → ℂ} (hΦ : Continuous Φ) (σ' : ℝ) (g : AdelicGL2 (𝓞 F) F) (v : Fin 2 → F) :
    Measurable (Gabs Φ σ' g v) := by
  unfold Gabs
  refine Measurable.fun_mul ?_ ?_
  · exact (hΦ.comp (continuous_rho g v)).measurable.enorm
  · refine ENNReal.measurable_ofReal.comp ?_
    exact ((NumberField.TateGlobal.continuous_ideleNorm F).measurable.pow_const σ')

variable (ν₀ : Measure (AdeleRing (𝓞 F) F)ˣ) [ν₀.IsMulLeftInvariant] (Ω : Set (AdeleRing (𝓞 F) F)ˣ)

theorem lintegral_eq_tsum_units (hΩ : IsFundamentalDomain (↥(Γ F)) Ω ν₀) (f : (𝔸)ˣ → ℝ≥0∞) :
    ∫⁻ x, f x ∂ν₀ = ∑' a : Fˣ, ∫⁻ x in Ω, f (prin a * x) ∂ν₀ := by
  rw [hΩ.lintegral_eq_tsum'' f]
  rw [← Equiv.tsum_eq prinEquiv]
  rfl

theorem tsum_lintegral_Gabs_vrep (hΩ : IsFundamentalDomain (↥(Γ F)) Ω ν₀)
    {Φ : (Fin 2 → 𝔸) → ℂ} (hΦ : Continuous Φ) (σ' : ℝ) (g : AdelicGL2 (𝓞 F) F) :
    ∑' o : Unit ⊕ F, ∫⁻ t, Gabs Φ σ' g (vrep o) t ∂ν₀
      = ∫⁻ t in Ω, ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0}, Gabs Φ σ' g ξ.1 t ∂ν₀ := by
  have h1 : ∀ o : Unit ⊕ F, ∫⁻ t, Gabs Φ σ' g (vrep o) t ∂ν₀
      = ∑' a : Fˣ, ∫⁻ t in Ω, Gabs Φ σ' g ((orbEquiv (o, a) : {ξ : Fin 2 → F // ξ ≠ 0}) : Fin 2 → F) t ∂ν₀ := by
    intro o
    rw [lintegral_eq_tsum_units ν₀ Ω hΩ]
    refine tsum_congr fun a => lintegral_congr fun t => ?_
    rw [Gabs_prin_mul, orbEquiv_apply_val]
  simp_rw [h1]
  rw [← ENNReal.tsum_prod (f := fun (o : Unit ⊕ F) (a : Fˣ) =>
      ∫⁻ t in Ω, Gabs Φ σ' g ((orbEquiv (o, a) : {ξ : Fin 2 → F // ξ ≠ 0}) : Fin 2 → F) t ∂ν₀)]
  rw [lintegral_tsum fun ξ : {ξ : Fin 2 → F // ξ ≠ 0} => ((measurable_Gabs hΦ σ' g ξ.1).aemeasurable).restrict]
  exact Equiv.tsum_eq orbEquiv (fun ξ : {ξ : Fin 2 → F // ξ ≠ 0} => ∫⁻ t in Ω, Gabs Φ σ' g ξ.1 t ∂ν₀)

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

section Main

variable [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]

theorem enorm_integrand {μ ν : (𝔸)ˣ →* ℂˣ} (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
    (Φ : (Fin 2 → 𝔸) → ℂ) (s' : ℂ) (x : Fin 2 → 𝔸) (t : (𝔸)ˣ) :
    ‖Φ x * (((μ * ν⁻¹) t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ s'‖ₑ = ‖Φ x‖ₑ * ENNReal.ofReal (ideleNorm F t ^ s'.re) := by
  have hχ : ‖(((μ * ν⁻¹) t : ℂˣ) : ℂ)‖ = 1 := by
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val, norm_mul, norm_inv, hμ t, hν t,
      inv_one, mul_one]
  have hN : ‖((ideleNorm F t : ℝ) : ℂ) ^ s'‖ = ideleNorm F t ^ s'.re := Complex.norm_cpow_eq_rpow_re_of_pos (ideleNorm_pos t) s'
  rw [enorm_mul, enorm_mul, ← ofReal_norm (((μ * ν⁻¹) t : ℂˣ) : ℂ), hχ, ENNReal.ofReal_one, mul_one,
    ← ofReal_norm (((ideleNorm F t : ℝ) : ℂ) ^ s'), hN]

theorem norm_godementSection_cell_le {μ ν : (𝔸)ˣ →* ℂˣ} (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
    (ν₀ : Measure (𝔸)ˣ) (α : (𝔸)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) {Φ : (Fin 2 → 𝔸) → ℂ}
    (s : ℂ) (g h : AdelicGL2 (𝓞 F) F) (v : Fin 2 → F)
    (hdet : Matrix.GeneralLinearGroup.det h = Matrix.GeneralLinearGroup.det g ∨
      Matrix.GeneralLinearGroup.det h = -Matrix.GeneralLinearGroup.det g)
    (hrow : ∀ t : (𝔸)ˣ, bottomRowVec F h t = rho g v t) :
    ‖godementSection F ν₀ μ ν α hα Φ s h‖
      ≤ ((α (Matrix.GeneralLinearGroup.det g) : ℝˣ) : ℝ) ^ (s.re + 1 / 2) * (∫⁻ t, Gabs Φ (2 * s.re + 1) g v t ∂ν₀).toReal := by
  unfold godementSection zetaIntegral
  have hα' : ((α (Matrix.GeneralLinearGroup.det h) : ℝˣ) : ℝ) = ((α (Matrix.GeneralLinearGroup.det g) : ℝˣ) : ℝ) := by
    rcases hdet with hd | hd
    · rw [hd]
    · rw [hd, ← neg_one_mul, map_mul, map_neg_one_eq_one_of_pos α hα, one_mul]
  rw [norm_mul, norm_mul, hμ, one_mul, cpowChar_apply_val, hα', Complex.norm_cpow_eq_rpow_re_of_pos (hα _), re_add_half]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (hα _).le _)
  refine (norm_integral_le_lintegral_norm _).trans (le_of_eq ?_)
  congr 1
  refine lintegral_congr fun t => ?_
  simp only [ofReal_norm]
  rw [enorm_integrand hμ hν, hrow]
  unfold Gabs
  congr 2
  simp [Complex.add_re, Complex.mul_re]

theorem main
    (ν₀ : Measure (𝔸)ˣ) [ν₀.IsMulLeftInvariant]
    (Ω : Set (𝔸)ˣ)
    (hΩ : IsFundamentalDomain (Units.map (algebraMap F 𝔸 : F →* 𝔸)).range Ω ν₀)
    (μ ν : (𝔸)ˣ →* ℂˣ)
    (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
    (α : (𝔸)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (Φ : (Fin 2 → 𝔸) → ℂ) (hΦ : Continuous Φ)
    (s : ℂ) (g : AdelicGL2 (𝓞 F) F)
    (habs : ∫⁻ t in Ω, ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0},
        ‖Φ ((t : 𝔸) • Matrix.vecMul (fun i => algebraMap F 𝔸 (ξ.1 i)) (g : Matrix (Fin 2) (Fin 2) 𝔸))
          * (((μ * ν⁻¹) t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ (2 * s + 1)‖ₑ ∂ν₀ < ⊤) :
    Summable (fun ξ : F => ‖godementSection F ν₀ μ ν α hα Φ s
        (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F 𝔸 ξ) * g)‖) ∧
    ‖godementSection F ν₀ μ ν α hα Φ s g‖
        + ∑' ξ : F, ‖godementSection F ν₀ μ ν α hα Φ s
            (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F 𝔸 ξ) * g)‖
      ≤ ((α (Matrix.GeneralLinearGroup.det g) : ℝˣ) : ℝ) ^ (s.re + 1 / 2)
        * ∫ t in Ω, (∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0},
            ‖Φ ((t : 𝔸) • Matrix.vecMul (fun i => algebraMap F 𝔸 (ξ.1 i)) (g : Matrix (Fin 2) (Fin 2) 𝔸))‖)
              * (ideleNorm F t) ^ (2 * s.re + 1) ∂ν₀ := by
  set σ' : ℝ := 2 * s.re + 1 with hσ'
  have hre : (2 * s + 1).re = σ' := by rw [hσ']; simp [Complex.add_re, Complex.mul_re]

  have habs' : ∫⁻ t in Ω, ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0}, Gabs Φ σ' g ξ.1 t ∂ν₀ < ⊤ := by
    refine lt_of_le_of_lt (le_of_eq ?_) habs
    refine lintegral_congr fun t => tsum_congr fun ξ => ?_
    rw [enorm_integrand hμ hν, hre]; rfl

  set L : Unit ⊕ F → ℝ≥0∞ := fun o => ∫⁻ t, Gabs Φ σ' g (vrep o) t ∂ν₀ with hL
  have hLsum : ∑' o, L o = ∫⁻ t in Ω, ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0}, Gabs Φ σ' g ξ.1 t ∂ν₀ :=
    tsum_lintegral_Gabs_vrep ν₀ Ω hΩ hΦ σ' g
  have hLtop : ∑' o, L o ≠ ⊤ := by rw [hLsum]; exact habs'.ne
  have hLo : ∀ o, L o ≠ ⊤ := fun o => ne_top_of_le_ne_top hLtop (ENNReal.le_tsum o)
  set C : ℝ := ((α (Matrix.GeneralLinearGroup.det g) : ℝˣ) : ℝ) ^ (s.re + 1 / 2) with hC
  have hC0 : 0 ≤ C := Real.rpow_nonneg (hα _).le _

  have hid : ‖godementSection F ν₀ μ ν α hα Φ s g‖ ≤ C * (L (Sum.inl ())).toReal :=
    norm_godementSection_cell_le hμ hν ν₀ α hα s g g _ (Or.inl rfl) (bottomRowVec_idCell g)
  have hbig : ∀ ξ : F, ‖godementSection F ν₀ μ ν α hα Φ s (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F 𝔸 ξ) * g)‖
      ≤ C * (L (Sum.inr ξ)).toReal := fun ξ =>
    norm_godementSection_cell_le hμ hν ν₀ α hα s g _ _ (Or.inr (det_bigCell _ g)) (bottomRowVec_bigCell ξ g)

  have hsumR : Summable fun o : Unit ⊕ F => (L o).toReal := ENNReal.summable_toReal hLtop
  have hsumBig : Summable fun ξ : F => (L (Sum.inr ξ)).toReal := hsumR.comp_injective Sum.inr_injective
  have hS : Summable (fun ξ : F => ‖godementSection F ν₀ μ ν α hα Φ s
      (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F 𝔸 ξ) * g)‖) :=
    Summable.of_nonneg_of_le (fun ξ => norm_nonneg _) hbig (hsumBig.mul_left C)
  refine ⟨hS, ?_⟩

  have h1 : ‖godementSection F ν₀ μ ν α hα Φ s g‖
        + ∑' ξ : F, ‖godementSection F ν₀ μ ν α hα Φ s (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F 𝔸 ξ) * g)‖
      ≤ C * (L (Sum.inl ())).toReal + ∑' ξ : F, C * (L (Sum.inr ξ)).toReal :=
    add_le_add hid (hS.tsum_le_tsum hbig (hsumBig.mul_left C))
  have h2 : C * (L (Sum.inl ())).toReal + ∑' ξ : F, C * (L (Sum.inr ξ)).toReal = C * (∑' o, L o).toReal := by
    have hU : ∑' u : Unit, (L (Sum.inl u)).toReal = (L (Sum.inl ())).toReal := by simp
    rw [tsum_mul_left, ← mul_add, ENNReal.tsum_toReal_eq hLo,
      Summable.tsum_sum (hsumR.comp_injective Sum.inl_injective) hsumBig]
    show C * ((L (Sum.inl ())).toReal + ∑' ξ : F, (L (Sum.inr ξ)).toReal) =
      C * (∑' u : Unit, (L (Sum.inl u)).toReal + ∑' ξ : F, (L (Sum.inr ξ)).toReal)
    rw [hU]

  have h3 : (∑' o, L o).toReal = ∫ t in Ω, (∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0},
            ‖Φ ((t : 𝔸) • Matrix.vecMul (fun i => algebraMap F 𝔸 (ξ.1 i)) (g : Matrix (Fin 2) (Fin 2) 𝔸))‖)
              * (ideleNorm F t) ^ σ' ∂ν₀ := by
    rw [hLsum]

    have hmeas : Measurable fun t : (𝔸)ˣ => ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0}, Gabs Φ σ' g ξ.1 t :=
      Measurable.ennreal_tsum fun ξ => measurable_Gabs hΦ σ' g _

    have hfin : ∀ᵐ t ∂(ν₀.restrict Ω), ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0}, Gabs Φ σ' g ξ.1 t < ⊤ :=
      ae_lt_top hmeas habs'.ne

    have hptw : ∀ t : (𝔸)ˣ, ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0}, Gabs Φ σ' g ξ.1 t < ⊤ →
        ENNReal.ofReal ((∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0},
            ‖Φ ((t : 𝔸) • Matrix.vecMul (fun i => algebraMap F 𝔸 (ξ.1 i)) (g : Matrix (Fin 2) (Fin 2) 𝔸))‖)
              * (ideleNorm F t) ^ σ') = ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0}, Gabs Φ σ' g ξ.1 t := by
      intro t ht
      have hpow : 0 ≤ ideleNorm F t ^ σ' := Real.rpow_nonneg (ideleNorm_pos t).le _
      have hG : ∀ ξ : {ξ : Fin 2 → F // ξ ≠ 0}, Gabs Φ σ' g ξ.1 t =
          ENNReal.ofReal (‖Φ ((t : 𝔸) • Matrix.vecMul (fun i => algebraMap F 𝔸 (ξ.1 i)) (g : Matrix (Fin 2) (Fin 2) 𝔸))‖
            * ideleNorm F t ^ σ') := fun ξ => by
        unfold Gabs rho iota
        rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm]
      simp_rw [hG] at ht ⊢
      have hsum : Summable fun ξ : {ξ : Fin 2 → F // ξ ≠ 0} =>
          ‖Φ ((t : 𝔸) • Matrix.vecMul (fun i => algebraMap F 𝔸 (ξ.1 i)) (g : Matrix (Fin 2) (Fin 2) 𝔸))‖ * ideleNorm F t ^ σ' := by
        exact (ENNReal.summable_toReal ht.ne).congr fun ξ => ENNReal.toReal_ofReal (mul_nonneg (norm_nonneg _) hpow)
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun ξ => mul_nonneg (norm_nonneg _) hpow) hsum, tsum_mul_right]

    set fR : (𝔸)ˣ → ℝ := fun t => (∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0},
        ‖Φ ((t : 𝔸) • Matrix.vecMul (fun i => algebraMap F 𝔸 (ξ.1 i)) (g : Matrix (Fin 2) (Fin 2) 𝔸))‖) * (ideleNorm F t) ^ σ' with hfR
    have hfR0 : ∀ t, 0 ≤ fR t := fun t =>
      mul_nonneg (tsum_nonneg fun ξ => norm_nonneg _) (Real.rpow_nonneg (ideleNorm_pos t).le _)
    have hae : ∀ᵐ t ∂(ν₀.restrict Ω), fR t = (∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0}, Gabs Φ σ' g ξ.1 t).toReal := by
      filter_upwards [hfin] with t ht
      rw [← hptw t ht, ENNReal.toReal_ofReal (hfR0 t)]
    have hfRm : AEStronglyMeasurable fR (ν₀.restrict Ω) :=
      (hmeas.ennreal_toReal.aestronglyMeasurable).congr (Filter.EventuallyEq.symm hae)
    show _ = ∫ t in Ω, fR t ∂ν₀
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hfR0) hfRm]
    congr 1
    exact lintegral_congr_ae (hfin.mono fun t ht => (hptw t ht).symm)
  rw [hσ'] at h3
  calc _ ≤ C * (L (Sum.inl ())).toReal + ∑' ξ : F, C * (L (Sum.inr ξ)).toReal := h1
    _ = C * (∑' o, L o).toReal := h2
    _ = _ := by rw [h3]

end Main

end GodementUnfold
p2m_reactivate "P2MW.S_AutomorphicForm_summable_norm_godementSection_bruhat_and_norm_add_tsum_norm_le_mul_setIntegral_tsum_norm_of_lintegral_tsum_enorm_lt_top.GodementUnfold"

theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν₀ : Measure (AdeleRing (𝓞 F) F)ˣ) [ν₀.IsMulLeftInvariant]
    (Ω : Set (AdeleRing (𝓞 F) F)ˣ)
    (hΩ : IsFundamentalDomain
      (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range Ω ν₀)
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
    (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (hΦ : Continuous Φ)
    (s : ℂ) (g : AdelicGL2 (𝓞 F) F)
    (habs : ∫⁻ t in Ω, ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0},
        ‖Φ ((t : AdeleRing (𝓞 F) F) •
              Matrix.vecMul (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ.1 i))
                (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))
          * (((μ * ν⁻¹) t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ (2 * s + 1)‖ₑ ∂ν₀ < ⊤) :
    Summable (fun ξ : F => ‖godementSection F ν₀ μ ν α hα Φ s
        (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)‖) ∧
    ‖godementSection F ν₀ μ ν α hα Φ s g‖
        + ∑' ξ : F, ‖godementSection F ν₀ μ ν α hα Φ s
            (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)‖
      ≤ ((α (Matrix.GeneralLinearGroup.det g) : ℝˣ) : ℝ) ^ (s.re + 1 / 2)
        * ∫ t in Ω, (∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0},
            ‖Φ ((t : AdeleRing (𝓞 F) F) •
                  Matrix.vecMul (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ.1 i))
                    (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))‖)
              * (ideleNorm F t) ^ (2 * s.re + 1) ∂ν₀ :=
  GodementUnfold.main ν₀ Ω hΩ μ ν hμ hν α hα Φ hΦ s g habs

end
end S_AutomorphicForm_summable_norm_godementSection_bruhat_and_norm_add_tsum_norm_le_mul_setIntegral_tsum_norm_of_lintegral_tsum_enorm_lt_top
end P2MW
export P2MW.S_AutomorphicForm_summable_norm_godementSection_bruhat_and_norm_add_tsum_norm_le_mul_setIntegral_tsum_norm_of_lintegral_tsum_enorm_lt_top (solution)
