-- Prove2me | solution 1 for AutomorphicForm.tendsto_sub_one_mul_lintegral_mul_ideleNorm_det_rpow_twistedCentralizer_nhdsGT_one_of_isFundamentalDomain_of_forall_ne_scalar_of_finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/7a3094b5-0f9a-5d08-914b-690aa020cb12

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_AutomorphicForm_setLIntegral_mul_ideleNorm_det_rpow_add_eq_setLIntegral_reflectPair_add_lintegral_mul_rate_of_isFundamentalDomain_twistedCentralizer_of_forall_ne_scalar_of_finrank_eq_two
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_AdelicFourier_continuous_integrable_comp_vecMul_mem_and_bottomRowVec_mem_schwartzBruhat_of_mem_schwartzBruhat2
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_tendsto_sub_one_mul_lintegral_mul_ideleNorm_det_rpow_twistedCentralizer_nhdsGT_one_of_isFundamentalDomain_of_forall_ne_scalar_of_finrank_eq_two
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply ContinuousAddEquiv.preimage_mulLeft_smul"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory Set Filter NumberField
open scoped ENNReal Topology

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "baseChangeGLEquiv isTopologicalRing_tensor centralizerBorel twistedCentralizer twistedCentralizerBorel sigmaCentralizer IsGlobalAddChar setLIntegral_mul_ideleNorm_det_rpow_add_eq_setLIntegral_reflectPair_add_lintegral_mul_rate_of_isFundamentalDomain_twistedCentralizer_of_forall_ne_scalar_of_finrank_eq_two"
namespace QuatZetaRes
p2m_open "AutomorphicForm"

theorem tendsto_of_identity (A P M Zb : ℝ → ℝ≥0∞) (φ0 I R B : ℝ≥0∞)
    (hφ0 : φ0 ≠ ⊤) (hI : I ≠ ⊤) (hR : R ≠ ⊤) (hB : B ≠ ⊤)
    (s₁ : ℝ) (hs₁ : 1 < s₁)
    (hP : ∀ s : ℝ, 1 < s → P s ≤ B) (hM : ∀ s : ℝ, 1 < s → M s ≤ B)
    (hZb : ∀ s : ℝ, 1 < s → s ≤ s₁ → Zb s ≤ B)
    (hE : ∀ s : ℝ, 1 < s →
      A s + φ0 * R * ENNReal.ofReal (1 / s) + M s = P s + I * R * ENNReal.ofReal (1 / (s - 1))) :
    Tendsto (fun s : ℝ => ENNReal.ofReal (s - 1) * (A s + Zb s)) (𝓝[>] (1 : ℝ)) (𝓝 (I * R)) := by

  set b : ℝ := B.toReal with hb
  set r : ℝ := R.toReal with hr
  set i : ℝ := I.toReal with hi
  set f : ℝ := φ0.toReal with hf
  have hb0 : 0 ≤ b := ENNReal.toReal_nonneg
  have hr0 : 0 ≤ r := ENNReal.toReal_nonneg
  have hf0 : 0 ≤ f := ENNReal.toReal_nonneg

  have hPt : ∀ s, 1 < s → P s ≠ ⊤ := fun s hs => ne_top_of_le_ne_top hB (hP s hs)
  have hMt : ∀ s, 1 < s → M s ≠ ⊤ := fun s hs => ne_top_of_le_ne_top hB (hM s hs)
  have hZbt : ∀ s, 1 < s → s ≤ s₁ → Zb s ≠ ⊤ := fun s hs hs' => ne_top_of_le_ne_top hB (hZb s hs hs')
  have hIRt : ∀ s, 1 < s → I * R * ENNReal.ofReal (1 / (s - 1)) ≠ ⊤ := fun s hs =>
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hI hR) ENNReal.ofReal_ne_top
  have hfRt : ∀ s, 1 < s → φ0 * R * ENNReal.ofReal (1 / s) ≠ ⊤ := fun s hs =>
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hφ0 hR) ENNReal.ofReal_ne_top
  have hAt : ∀ s, 1 < s → A s ≠ ⊤ := by
    intro s hs
    have h := hE s hs
    have hle : A s ≤ P s + I * R * ENNReal.ofReal (1 / (s - 1)) := by
      calc A s ≤ A s + φ0 * R * ENNReal.ofReal (1 / s) + M s := by
            rw [add_assoc]; exact le_self_add
        _ = _ := h
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hPt s hs, hIRt s hs⟩) hle

  have hEr : ∀ s, 1 < s →
      (A s).toReal + f * r * (1 / s) + (M s).toReal = (P s).toReal + i * r * (1 / (s - 1)) := by
    intro s hs
    have h := congrArg ENNReal.toReal (hE s hs)
    have hs0 : (0 : ℝ) ≤ 1 / s := by positivity
    have hs1 : (0 : ℝ) ≤ 1 / (s - 1) := div_nonneg zero_le_one (by linarith)
    rw [ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨hAt s hs, hfRt s hs⟩) (hMt s hs),
      ENNReal.toReal_add (hAt s hs) (hfRt s hs), ENNReal.toReal_add (hPt s hs) (hIRt s hs),
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hs0, ENNReal.toReal_ofReal hs1] at h
    exact h

  have hPr : ∀ s, 1 < s → (P s).toReal ≤ b := fun s hs => ENNReal.toReal_mono hB (hP s hs)
  have hMr : ∀ s, 1 < s → (M s).toReal ≤ b := fun s hs => ENNReal.toReal_mono hB (hM s hs)
  have hZbr : ∀ s, 1 < s → s ≤ s₁ → (Zb s).toReal ≤ b := fun s hs hs' => ENNReal.toReal_mono hB (hZb s hs hs')

  set g : ℝ → ℝ := fun s => (s - 1) * ((A s).toReal + (Zb s).toReal) with hg
  have hdist : ∀ s, 1 < s → s ≤ s₁ → |g s - i * r| ≤ (s - 1) * (3 * b + f * r) := by
    intro s hs hs'
    have hs' : 0 < s - 1 := by linarith
    have hE' := hEr s hs
    have hkey : g s - i * r = (s - 1) * (P s).toReal - (s - 1) * (f * r * (1 / s)) - (s - 1) * (M s).toReal +
        (s - 1) * (Zb s).toReal := by
      have h1 : (s - 1) * (i * r * (1 / (s - 1))) = i * r := by field_simp
      rw [hg]; dsimp only
      linear_combination (s - 1) * hE' + h1
    rw [hkey]
    have hP0 : 0 ≤ (P s).toReal := ENNReal.toReal_nonneg
    have hM0 : 0 ≤ (M s).toReal := ENNReal.toReal_nonneg
    have hZ0 : 0 ≤ (Zb s).toReal := ENNReal.toReal_nonneg
    have hq : 0 ≤ f * r * (1 / s) := by positivity
    have hq' : f * r * (1 / s) ≤ f * r := by
      have : (1 : ℝ) / s ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      calc f * r * (1 / s) ≤ f * r * 1 := by gcongr
        _ = f * r := mul_one _
    rw [abs_le]
    constructor
    · nlinarith [hPr s hs, hMr s hs, hZbr s hs (by linarith), mul_nonneg hs'.le hP0, mul_nonneg hs'.le hZ0,
        mul_nonneg hs'.le hM0, mul_nonneg hs'.le hq, mul_le_mul_of_nonneg_left (hMr s hs) hs'.le,
        mul_le_mul_of_nonneg_left hq' hs'.le]
    · nlinarith [hPr s hs, hMr s hs, hZbr s hs (by linarith), mul_nonneg hs'.le hP0, mul_nonneg hs'.le hZ0,
        mul_nonneg hs'.le hM0, mul_nonneg hs'.le hq, mul_le_mul_of_nonneg_left (hPr s hs) hs'.le,
        mul_le_mul_of_nonneg_left (hZbr s hs (by linarith)) hs'.le]

  have hgt : Tendsto g (𝓝[>] (1 : ℝ)) (𝓝 (i * r)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hbound : Tendsto (fun s : ℝ => (s - 1) * (3 * b + f * r)) (𝓝[>] (1 : ℝ)) (𝓝 0) := by
      have : Tendsto (fun s : ℝ => (s - 1) * (3 * b + f * r)) (𝓝 (1 : ℝ)) (𝓝 ((1 - 1) * (3 * b + f * r))) :=
        ((continuous_id.sub continuous_const).mul continuous_const).tendsto 1
      rw [sub_self, zero_mul] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine squeeze_zero' (Eventually.of_forall fun s => norm_nonneg _) ?_ hbound
    filter_upwards [Ioo_mem_nhdsGT hs₁] with s hs
    rw [Real.norm_eq_abs]
    exact hdist s hs.1 hs.2.le

  have hlim : ENNReal.ofReal (i * r) = I * R := by
    rw [hi, hr, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hI, ENNReal.ofReal_toReal hR]
  rw [← hlim]
  refine ((ENNReal.tendsto_ofReal hgt).congr' ?_)
  filter_upwards [Ioo_mem_nhdsGT hs₁] with s hs
  rw [hg]; dsimp only
  rw [ENNReal.ofReal_mul (by linarith [hs.1]), ← ENNReal.toReal_add (hAt s hs.1) (hZbt s hs.1 hs.2.le),
    ENNReal.ofReal_toReal (ENNReal.add_ne_top.2 ⟨hAt s hs.1, hZbt s hs.1 hs.2.le⟩)]

section Setting

p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_tendsto_sub_one_mul_lintegral_mul_ideleNorm_det_rpow_twistedCentralizer_nhdsGT_one_of_isFundamentalDomain_of_forall_ne_scalar_of_finrank_eq_two.AutomorphicForm NumberField.AdelicFourier NumberField.AdelicBox NumberField.TateGlobal"
open scoped TensorProduct TensorProduct.RightActions

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.twistedCentralizerBorel

abbrev Emap : L ⊗[K] AdeleRing (𝓞 K) K →+* AdeleRing (𝓞 L) L :=
  ((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
    (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom

abbrev Tw (σ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) :
    Subgroup (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :=
  AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ
    (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
      Matrix.GeneralLinearGroup.scalar (Fin 2) c)

variable (σ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)

def normDet (t : Tw K L σ δ₀ c) : ℝ :=
  NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (Emap K L)
    (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))))

theorem normDet_pos (t : Tw K L σ δ₀ c) : 0 < normDet K L σ δ₀ c t := NumberField.TateGlobal.ideleNorm_pos _

theorem continuous_normDet : Continuous (normDet K L σ δ₀ c) := by
  haveI := isTopologicalRing_tensor K L (AdeleRing (𝓞 K) K)
  have hE : Continuous fun g : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) =>
      Matrix.GeneralLinearGroup.map (n := Fin 2) (Emap K L) g :=
    (baseChangeGLEquiv K L).continuous.congr fun g => rfl
  exact (NumberField.TateGlobal.continuous_ideleNorm L).comp
    (Matrix.GeneralLinearGroup.continuous_det.comp (hE.comp continuous_subtype_val))

theorem measurable_normDet : Measurable (normDet K L σ δ₀ c) := by
  haveI : BorelSpace (Tw K L σ δ₀ c) := ⟨rfl⟩
  exact (continuous_normDet K L σ δ₀ c).measurable

def colv (v : Fin 2 → L) (t : Tw K L σ δ₀ c) : Fin 2 → AdeleRing (𝓞 L) L :=
  ((Matrix.GeneralLinearGroup.map (Emap K L) (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :
      GL (Fin 2) (AdeleRing (𝓞 L) L)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec
    fun i => algebraMap L (AdeleRing (𝓞 L) L) (v i)

theorem continuous_colv (v : Fin 2 → L) : Continuous (colv K L σ δ₀ c v) := by
  haveI := isTopologicalRing_tensor K L (AdeleRing (𝓞 K) K)
  have hE : Continuous fun g : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) =>
      Matrix.GeneralLinearGroup.map (n := Fin 2) (Emap K L) g :=
    (baseChangeGLEquiv K L).continuous.congr fun g => rfl
  exact (Units.continuous_val.comp (hE.comp continuous_subtype_val)).matrix_mulVec continuous_const

end Setting

section Main

p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_tendsto_sub_one_mul_lintegral_mul_ideleNorm_det_rpow_twistedCentralizer_nhdsGT_one_of_isFundamentalDomain_of_forall_ne_scalar_of_finrank_eq_two.AutomorphicForm NumberField.AdelicFourier NumberField.AdelicBox NumberField.TateGlobal"
open scoped TensorProduct TensorProduct.RightActions

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.twistedCentralizerBorel

theorem main
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)
    (hN₀ : ∃ z : Lˣ, δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) δ₀ =
      Matrix.GeneralLinearGroup.scalar (Fin 2) z)
    (hns : ∀ (x : GL (Fin 2) L) (z : Lˣ),
      x⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) x ≠
        Matrix.GeneralLinearGroup.scalar (Fin 2) z)
    (v : Fin 2 → L) (hv : v ≠ 0)
    [MeasurableSpace (AdeleRing (𝓞 L) L)] [BorelSpace (AdeleRing (𝓞 L) L)]
    (μ₁ : Measure (AdeleRing (𝓞 L) L)) [μ₁.IsAddHaarMeasure] (hμ₁ : μ₁ (adelicBox L) = 1)
    {ψ : AddChar (AdeleRing (𝓞 L) L) ℂ} (hψ : IsGlobalAddChar L ψ)
    {Φ : (Fin 2 → AdeleRing (𝓞 L) L) → ℂ} (hΦ : Φ ∈ schwartzBruhat2 L)
    (hΦnn : ∀ x, 0 ≤ (Φ x).re)
    (τ' : Measure (Tw K L σ δ₀ c)) (hτ' : τ'.IsHaarMeasure) (hτ'r : τ'.IsMulRightInvariant)
    (R' : ENNReal) (hR' : R' ≠ ⊤)
    (hD' : ∀ D' : Set (Tw K L σ δ₀ c),
      IsFundamentalDomain
        (((AutomorphicForm.sigmaCentralizer
            (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀).map
            (Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K))).subgroupOf
          (Tw K L σ δ₀ c)).op D' τ' →
      ∀ a b : ℝ, 0 < a → a ≤ b →
        τ' (D' ∩ {t | normDet K L σ δ₀ c t ∈ Set.Icc a b}) = R' * ENNReal.ofReal (Real.log (b / a)))
    (D₀ : Set (Tw K L σ δ₀ c)) (hD₀m : MeasurableSet D₀)
    (hD₀ : IsFundamentalDomain
        (((AutomorphicForm.sigmaCentralizer
            (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀).map
            (Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K))).subgroupOf
          (Tw K L σ δ₀ c)).op D₀ τ')
    (s₁ : ℝ) (hs₁ : 1 < s₁)
    (hZ : ∫⁻ t in {t | 1 ≤ normDet K L σ δ₀ c t},
        ENNReal.ofReal (Φ (colv K L σ δ₀ c v t)).re * ENNReal.ofReal (normDet K L σ δ₀ c t ^ s₁) ∂τ' < ⊤)
    (hZ' : ∫⁻ t in {t | 1 ≤ normDet K L σ δ₀ c t}, ‖reflectPair ψ μ₁ Φ (colv K L σ δ₀ c v t)‖ₑ ∂τ' < ⊤) :
    Tendsto (fun s : ℝ => ENNReal.ofReal (s - 1) *
      ∫⁻ t, ENNReal.ofReal (Φ (colv K L σ δ₀ c v t)).re * ENNReal.ofReal (normDet K L σ δ₀ c t ^ s) ∂τ')
      (𝓝[>] (1 : ℝ)) (𝓝 ((∫⁻ x, ENNReal.ofReal (Φ x).re ∂(pairHaar μ₁)) * R')) := by

  set N := normDet K L σ δ₀ c with hNdef
  set col := colv K L σ δ₀ c v with hcoldef
  set Φ' := reflectPair ψ μ₁ Φ with hΦ'def
  have hNm : Measurable N := measurable_normDet K L σ δ₀ c
  have hS0 : MeasurableSet ({t | N t ≤ 1} : Set (Tw K L σ δ₀ c)) := hNm measurableSet_Iic

  set A : ℝ → ℝ≥0∞ := fun s => ∫⁻ t in {t | N t ≤ 1}, ENNReal.ofReal (Φ (col t)).re * ENNReal.ofReal (N t ^ s) ∂τ'
    with hA
  set Zb : ℝ → ℝ≥0∞ := fun s => ∫⁻ t in {t | N t ≤ 1}ᶜ, ENNReal.ofReal (Φ (col t)).re * ENNReal.ofReal (N t ^ s) ∂τ'
    with hZb
  set P : ℝ → ℝ≥0∞ := fun s => ∫⁻ t in {t | 1 ≤ N t}, ENNReal.ofReal (Φ' (col t)).re * ENNReal.ofReal (N t ^ (1 - s)) ∂τ'
    with hP
  set M : ℝ → ℝ≥0∞ := fun s => ∫⁻ t in {t | 1 ≤ N t}, ENNReal.ofReal (-(Φ' (col t)).re) * ENNReal.ofReal (N t ^ (1 - s)) ∂τ'
    with hM
  set I : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (Φ x).re ∂(pairHaar μ₁) with hI
  set B₁ : ℝ≥0∞ := ∫⁻ t in {t | 1 ≤ N t}, ENNReal.ofReal (Φ (col t)).re * ENNReal.ofReal (N t ^ s₁) ∂τ' with hB₁
  set B₂ : ℝ≥0∞ := ∫⁻ t in {t | 1 ≤ N t}, ‖Φ' (col t)‖ₑ ∂τ' with hB₂

  have hsplit : ∀ s : ℝ, A s + Zb s =
      ∫⁻ t, ENNReal.ofReal (Φ (col t)).re * ENNReal.ofReal (N t ^ s) ∂τ' := fun s =>
    lintegral_add_compl _ hS0

  have hE : ∀ s : ℝ, 1 < s →
      A s + ENNReal.ofReal (Φ 0).re * R' * ENNReal.ofReal (1 / s) + M s = P s + I * R' * ENNReal.ofReal (1 / (s - 1)) :=
    fun s hs =>
      AutomorphicForm.setLIntegral_mul_ideleNorm_det_rpow_add_eq_setLIntegral_reflectPair_add_lintegral_mul_rate_of_isFundamentalDomain_twistedCentralizer_of_forall_ne_scalar_of_finrank_eq_two
        K L h2 σ hgen δ₀ c hN₀ hns v hv μ₁ hμ₁ hψ hΦ hΦnn τ' hτ' hτ'r R' hR' hD' D₀ hD₀m hD₀ s hs

  have hIt : I ≠ ⊤ := by
    have hint : Integrable Φ (pairHaar μ₁) :=
      (NumberField.AdelicFourier.continuous_integrable_comp_vecMul_mem_and_bottomRowVec_mem_schwartzBruhat_of_mem_schwartzBruhat2
        L Φ hΦ).2.2.2.1 μ₁
    refine ne_of_lt (lt_of_le_of_lt (lintegral_mono fun x => ?_) hint.hasFiniteIntegral)
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (Complex.abs_re_le_norm _))

  have hpw : ∀ (s : ℝ) (t : Tw K L σ δ₀ c), 1 ≤ N t → 1 ≤ s → ENNReal.ofReal (N t ^ (1 - s)) ≤ 1 := by
    intro s t ht hs
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_one_of_one_le_of_nonpos ht (by linarith))
  have hPB : ∀ s : ℝ, 1 < s → P s ≤ B₁ + B₂ := by
    intro s hs
    refine le_add_left ?_
    refine setLIntegral_mono' (hNm measurableSet_Ici) fun t ht => ?_
    calc ENNReal.ofReal (Φ' (col t)).re * ENNReal.ofReal (N t ^ (1 - s))
        ≤ ‖Φ' (col t)‖ₑ * 1 := by
          refine mul_le_mul' ?_ (hpw s t ht hs.le)
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (Complex.abs_re_le_norm _))
      _ = ‖Φ' (col t)‖ₑ := mul_one _
  have hMB : ∀ s : ℝ, 1 < s → M s ≤ B₁ + B₂ := by
    intro s hs
    refine le_add_left ?_
    refine setLIntegral_mono' (hNm measurableSet_Ici) fun t ht => ?_
    calc ENNReal.ofReal (-(Φ' (col t)).re) * ENNReal.ofReal (N t ^ (1 - s))
        ≤ ‖Φ' (col t)‖ₑ * 1 := by
          refine mul_le_mul' ?_ (hpw s t ht hs.le)
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal ((neg_le_abs _).trans (Complex.abs_re_le_norm _))
      _ = ‖Φ' (col t)‖ₑ := mul_one _
  have hZbB : ∀ s : ℝ, 1 < s → s ≤ s₁ → Zb s ≤ B₁ + B₂ := by
    intro s hs hs'
    refine le_add_right ?_
    have hsub : ({t | N t ≤ 1}ᶜ : Set (Tw K L σ δ₀ c)) ⊆ {t | 1 ≤ N t} := fun t ht => by
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at ht
      exact ht.le
    calc Zb s ≤ ∫⁻ t in {t | 1 ≤ N t}, ENNReal.ofReal (Φ (col t)).re * ENNReal.ofReal (N t ^ s) ∂τ' :=
          lintegral_mono_set hsub
      _ ≤ B₁ := by
          refine setLIntegral_mono' (hNm measurableSet_Ici) fun t ht => ?_
          refine mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_)
          exact Real.rpow_le_rpow_of_exponent_le ht hs'
  have hBt : B₁ + B₂ ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hZ.ne, hZ'.ne⟩

  have h := tendsto_of_identity A P M Zb (ENNReal.ofReal (Φ 0).re) I R' (B₁ + B₂) ENNReal.ofReal_ne_top hIt hR' hBt
    s₁ hs₁ hPB hMB hZbB hE
  simp_rw [hsplit] at h
  exact h

end Main

end AutomorphicForm.QuatZetaRes

end

p2m_open "MeasureTheory Filter NumberField NumberField.AdelicHaar NumberField.AdelicFourier NumberField.AdelicBox NumberField.TateGlobal IsDedekindDomain AutomorphicForm P2MW.S_AutomorphicForm_tendsto_sub_one_mul_lintegral_mul_ideleNorm_det_rpow_twistedCentralizer_nhdsGT_one_of_isFundamentalDomain_of_forall_ne_scalar_of_finrank_eq_two.AutomorphicForm"

open scoped TensorProduct TensorProduct.RightActions Topology ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)
    (hN₀ : ∃ z : Lˣ, δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) δ₀ =
      Matrix.GeneralLinearGroup.scalar (Fin 2) z)
    (hns : ∀ (x : GL (Fin 2) L) (z : Lˣ),
      x⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) x ≠
        Matrix.GeneralLinearGroup.scalar (Fin 2) z)
    (v : Fin 2 → L) (hv : v ≠ 0)

    [MeasurableSpace (AdeleRing (𝓞 L) L)] [BorelSpace (AdeleRing (𝓞 L) L)]
    (μ₁ : Measure (AdeleRing (𝓞 L) L)) [μ₁.IsAddHaarMeasure] (hμ₁ : μ₁ (adelicBox L) = 1)
    {ψ : AddChar (AdeleRing (𝓞 L) L) ℂ} (hψ : IsGlobalAddChar L ψ)
    {Φ : (Fin 2 → AdeleRing (𝓞 L) L) → ℂ} (hΦ : Φ ∈ schwartzBruhat2 L)
    (hΦnn : ∀ x, 0 ≤ (Φ x).re)

    (τ' : Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
    (hτ' : τ'.IsHaarMeasure) (hτ'r : τ'.IsMulRightInvariant)
    (R' : ENNReal) (hR' : R' ≠ ⊤)
    (hD' : ∀ D' : Set (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)),
      IsFundamentalDomain
        (((AutomorphicForm.sigmaCentralizer
            (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀).map
            (Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K))).subgroupOf
          (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))).op D' τ' →
      ∀ a b : ℝ, 0 < a → a ≤ b →
        τ' (D' ∩ {t | NumberField.TateGlobal.ideleNorm L
          (Matrix.GeneralLinearGroup.det
            (Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))) ∈ Set.Icc a b}) =
          R' * ENNReal.ofReal (Real.log (b / a)))

    (D₀ : Set (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
    (hD₀m : MeasurableSet D₀)
    (hD₀ : IsFundamentalDomain
        (((AutomorphicForm.sigmaCentralizer
            (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀).map
            (Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K))).subgroupOf
          (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))).op D₀ τ')

    (s₁ : ℝ) (hs₁ : 1 < s₁)
    (hZ : ∫⁻ t in {t | 1 ≤ NumberField.TateGlobal.ideleNorm L
          (Matrix.GeneralLinearGroup.det
            (Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))))},
        ENNReal.ofReal (Φ ((Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec
            fun i => algebraMap L (AdeleRing (𝓞 L) L) (v i))).re *
          ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L
          (Matrix.GeneralLinearGroup.det
            (Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))) ^ s₁) ∂τ' < ⊤)
    (hZ' : ∫⁻ t in {t | 1 ≤ NumberField.TateGlobal.ideleNorm L
          (Matrix.GeneralLinearGroup.det
            (Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))))},
        ‖reflectPair ψ μ₁ Φ ((Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec
            fun i => algebraMap L (AdeleRing (𝓞 L) L) (v i))‖ₑ ∂τ' < ⊤) :
    Tendsto (fun s : ℝ => ENNReal.ofReal (s - 1) *
      ∫⁻ t, ENNReal.ofReal (Φ ((Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec
            fun i => algebraMap L (AdeleRing (𝓞 L) L) (v i))).re *
          ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L
          (Matrix.GeneralLinearGroup.det
            (Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))) ^ s) ∂τ')
      (𝓝[>] (1 : ℝ)) (𝓝 ((∫⁻ x, ENNReal.ofReal (Φ x).re ∂(pairHaar μ₁)) * R')) :=
  AutomorphicForm.QuatZetaRes.main K L h2 σ hgen δ₀ c hN₀ hns v hv μ₁ hμ₁ hψ hΦ hΦnn τ' hτ' hτ'r R' hR' hD' D₀ hD₀m hD₀
    s₁ hs₁ hZ hZ'

end S_AutomorphicForm_tendsto_sub_one_mul_lintegral_mul_ideleNorm_det_rpow_twistedCentralizer_nhdsGT_one_of_isFundamentalDomain_of_forall_ne_scalar_of_finrank_eq_two
end P2MW
export P2MW.S_AutomorphicForm_tendsto_sub_one_mul_lintegral_mul_ideleNorm_det_rpow_twistedCentralizer_nhdsGT_one_of_isFundamentalDomain_of_forall_ne_scalar_of_finrank_eq_two (solution)
