-- Prove2me | solution 1 for AutomorphicForm.twisted_window_values_inv_mul_unitsMap_eq_of_ne_one_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/ba6a899d-1014-5d81-9ca0-06154cb30f69

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_AutomorphicForm_WindingDatum
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_UnramifiedWhittaker_ZetaIntegrand
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_AutomorphicForm_map_subtypeVal_centralizer_eq_and_map_conj_adelicWeyl_eq_of_forall_integral_eq_mul_integral_prod
import Theorems.Thm_AutomorphicForm_eq_inv_mul_of_isTwistedWeightedOrbitalIntegralOn_of_normString_eq_toTensorGL_diagonal_of_coupled_one_smul_infiniteAdeleRing
import Theorems.Thm_AutomorphicForm_eq_of_isTwistedWeightedOrbitalIntegral_of_isTwistedWeightedOrbitalIntegral_of_normString_eq_toTensorGL_diagonal
import Theorems.Thm_AutomorphicForm_archWeight_archIdentGL_diagonal_mul_and_continuous
import Theorems.Thm_AutomorphicForm_exists_isNormOf_glArch_centralScalar_mul_diagUnits2_iff_inv_and_finComponent_iff_inv
import Theorems.Thm_AutomorphicForm_isRegularSemisimple_finComponent_glFin_centralScalar_mul_diagUnits2_of_ne_one
import Theorems.Thm_AutomorphicForm_coe_finComponent_glFin_centralScalar_mul_diagUnits2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_twisted_window_values_inv_mul_unitsMap_eq_of_ne_one_of_prime
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open scoped NNReal ENNReal TensorProduct TensorProduct.RightActions

noncomputable section

namespace TwA

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] (σ : L ≃ₐ[K] L)

local notation "G₂" => GL (Fin 2) (L ⊗[K] A)

theorem mem_twistedCentralizer_conj_iff (x δ g : G₂) (hx : sigmaGL K L A σ x = x) :
    x * g * x⁻¹ ∈ twistedCentralizer K L A σ (x * δ * x⁻¹) ↔ g ∈ twistedCentralizer K L A σ δ := by
  show x * g * x⁻¹ ∈ sigmaCentralizer (sigmaGL K L A σ) (x * δ * x⁻¹) ↔ g ∈ sigmaCentralizer (sigmaGL K L A σ) δ
  rw [mem_sigmaCentralizer_iff, mem_sigmaCentralizer_iff]
  have hxi : sigmaGL K L A σ x⁻¹ = x⁻¹ := by rw [map_inv, hx]
  rw [map_mul, map_mul, hx, hxi]
  constructor
  · intro h
    calc g * δ * (sigmaGL K L A σ g)⁻¹ = x⁻¹ * (x * g * x⁻¹ * (x * δ * x⁻¹) * (x * sigmaGL K L A σ g * x⁻¹)⁻¹) * x := by group
      _ = x⁻¹ * (x * δ * x⁻¹) * x := by rw [h]
      _ = δ := by group
  · intro h
    calc x * g * x⁻¹ * (x * δ * x⁻¹) * (x * sigmaGL K L A σ g * x⁻¹)⁻¹ = x * (g * δ * (sigmaGL K L A σ g)⁻¹) * x⁻¹ := by group
      _ = x * δ * x⁻¹ := by rw [h]

noncomputable def conjEquiv (x δ : G₂) (hx : sigmaGL K L A σ x = x) :
    twistedCentralizer K L A σ δ ≃ₜ* twistedCentralizer K L A σ (x * δ * x⁻¹) :=
  haveI := isTopologicalGroup_tensorGL K L A
  { toFun := fun t => ⟨x * t * x⁻¹, (mem_twistedCentralizer_conj_iff K L A σ x δ t hx).2 t.2⟩
    invFun := fun t' => ⟨x⁻¹ * t' * x, by
      have h := (mem_twistedCentralizer_conj_iff K L A σ x δ (x⁻¹ * t' * x) hx).1
      refine h ?_
      have : x * (x⁻¹ * (t' : G₂) * x) * x⁻¹ = t' := by group
      rw [this]; exact t'.2⟩
    left_inv := fun t => by ext; simp [mul_assoc]
    right_inv := fun t' => by ext; simp [mul_assoc]
    map_mul' := fun s t => by ext; simp [mul_assoc]
    continuous_toFun := by
      apply Continuous.subtype_mk
      exact (continuous_const.mul continuous_subtype_val).mul continuous_const
    continuous_invFun := by
      apply Continuous.subtype_mk
      exact (continuous_const.mul continuous_subtype_val).mul continuous_const }

@[scoped simp] theorem coe_conjEquiv (x δ : G₂) (hx : sigmaGL K L A σ x = x) (t : twistedCentralizer K L A σ δ) :
    ((conjEquiv K L A σ x δ hx t : twistedCentralizer K L A σ (x * δ * x⁻¹)) : G₂) = x * t * x⁻¹ := rfl

noncomputable def conjMeasure (x δ : G₂) (hx : sigmaGL K L A σ x = x)
    (τ : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ)) :
    @Measure (twistedCentralizer K L A σ (x * δ * x⁻¹)) (twistedCentralizerBorel K L A σ (x * δ * x⁻¹)) :=
  @Measure.map _ _ (twistedCentralizerBorel K L A σ δ) (twistedCentralizerBorel K L A σ (x * δ * x⁻¹))
    (conjEquiv K L A σ x δ hx) τ

theorem isHaarMeasure_conjMeasure (x δ : G₂) (hx : sigmaGL K L A σ x = x)
    (τ : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L A σ δ) τ) :
    @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L A σ (x * δ * x⁻¹)) (conjMeasure K L A σ x δ hx τ) := by
  letI := twistedCentralizerBorel K L A σ δ
  letI := twistedCentralizerBorel K L A σ (x * δ * x⁻¹)
  haveI := isTopologicalGroup_tensorGL K L A
  haveI : BorelSpace (twistedCentralizer K L A σ δ) := ⟨rfl⟩
  haveI : BorelSpace (twistedCentralizer K L A σ (x * δ * x⁻¹)) := ⟨rfl⟩
  haveI := hτ
  exact (conjEquiv K L A σ x δ hx).isHaarMeasure_map τ

theorem integral_conjMeasure (x δ : G₂) (hx : sigmaGL K L A σ x = x)
    (τ : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ)) (F : G₂ → ℝ) :
    (letI := twistedCentralizerBorel K L A σ (x * δ * x⁻¹);
      ∫ t', F (t' : G₂) ∂(conjMeasure K L A σ x δ hx τ)) =
    (letI := twistedCentralizerBorel K L A σ δ; ∫ t, F (x * (t : G₂) * x⁻¹) ∂τ) := by
  letI : MeasurableSpace G₂ := glBorelOf (L ⊗[K] A)
  haveI : BorelSpace G₂ := borelSpace_glBorelOf (L ⊗[K] A)
  haveI := isTopologicalGroup_tensorGL K L A
  letI := twistedCentralizerBorel K L A σ δ
  letI := twistedCentralizerBorel K L A σ (x * δ * x⁻¹)
  haveI : BorelSpace (twistedCentralizer K L A σ δ) := ⟨rfl⟩
  haveI : BorelSpace (twistedCentralizer K L A σ (x * δ * x⁻¹)) := ⟨rfl⟩
  have hemb : MeasurableEmbedding (conjEquiv K L A σ x δ hx : twistedCentralizer K L A σ δ → _) :=
    (conjEquiv K L A σ x δ hx).toHomeomorph.measurableEmbedding
  show ∫ t', F (t' : G₂) ∂(Measure.map (conjEquiv K L A σ x δ hx) τ) = _
  rw [hemb.integral_map]
  rfl

theorem map_subtypeVal_conjMeasure (x δ : G₂) (hx : sigmaGL K L A σ x = x)
    (τ : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ)) :
    @Measure.map _ _ (twistedCentralizerBorel K L A σ (x * δ * x⁻¹)) (glBorelOf (L ⊗[K] A)) Subtype.val
        (conjMeasure K L A σ x δ hx τ) =
      @Measure.map _ _ (twistedCentralizerBorel K L A σ δ) (glBorelOf (L ⊗[K] A))
        (fun t : twistedCentralizer K L A σ δ => x * (t : G₂) * x⁻¹) τ := by
  letI : MeasurableSpace G₂ := glBorelOf (L ⊗[K] A)
  haveI : BorelSpace G₂ := borelSpace_glBorelOf (L ⊗[K] A)
  haveI := isTopologicalGroup_tensorGL K L A
  letI := twistedCentralizerBorel K L A σ δ
  letI := twistedCentralizerBorel K L A σ (x * δ * x⁻¹)
  haveI : BorelSpace (twistedCentralizer K L A σ δ) := ⟨rfl⟩
  haveI : BorelSpace (twistedCentralizer K L A σ (x * δ * x⁻¹)) := ⟨rfl⟩
  have hmeas : Measurable (conjEquiv K L A σ x δ hx : twistedCentralizer K L A σ δ → twistedCentralizer K L A σ (x * δ * x⁻¹)) :=
    (conjEquiv K L A σ x δ hx).continuous.measurable
  show Measure.map Subtype.val (Measure.map (conjEquiv K L A σ x δ hx) τ) = _
  rw [Measure.map_map continuous_subtype_val.measurable hmeas]
  rfl

theorem isTwistedSectionFnOn_conj (x δ : G₂) (hx : sigmaGL K L A σ x = x)
    (τ : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ))
    (φ : G₂ → ℂ) (w : G₂ → ℝ) (hw : IsTwistedSectionFnOn K L A σ δ τ φ w) :
    IsTwistedSectionFnOn K L A σ (x * δ * x⁻¹) (conjMeasure K L A σ x δ hx τ) φ (fun y => w (x⁻¹ * y)) := by
  letI : MeasurableSpace G₂ := glBorelOf (L ⊗[K] A)
  haveI : BorelSpace G₂ := borelSpace_glBorelOf (L ⊗[K] A)
  haveI := isTopologicalGroup_tensorGL K L A
  obtain ⟨hw0, hwm, hwc, hws⟩ := hw
  refine ⟨fun y => hw0 _, hwm.comp (measurable_const_mul x⁻¹), hwc.comp_homeomorph (Homeomorph.mulLeft x⁻¹), ?_⟩
  intro y hy
  have hxi : sigmaGL K L A σ x⁻¹ = x⁻¹ := by rw [map_inv, hx]
  have hy' : φ ((x⁻¹ * y)⁻¹ * δ * sigmaGL K L A σ (x⁻¹ * y)) ≠ 0 := by
    have : (x⁻¹ * y)⁻¹ * δ * sigmaGL K L A σ (x⁻¹ * y) = y⁻¹ * (x * δ * x⁻¹) * sigmaGL K L A σ y := by
      rw [map_mul, hxi]; group
    rwa [this]
  have := integral_conjMeasure K L A σ x δ hx τ (fun g => w (x⁻¹ * (g * y)))
  rw [this]
  have hpt : ∀ t : twistedCentralizer K L A σ δ,
      w (x⁻¹ * (x * (t : G₂) * x⁻¹ * y)) = w ((t : G₂) * (x⁻¹ * y)) := fun t => by congr 1; group
  simp_rw [hpt]
  exact hws (x⁻¹ * y) hy'

theorem isTwistedWeightedOrbitalIntegralOn_conj
    (μ : @Measure G₂ (glBorelOf (L ⊗[K] A)))
    (hμ : @Measure.IsMulLeftInvariant G₂ (glBorelOf (L ⊗[K] A)) _ μ)
    (W : G₂ → ℝ) (x δ : G₂) (hx : sigmaGL K L A σ x = x) (hW : ∀ y, W (x * y) = W y)
    (τ : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ))
    (φ : G₂ → ℂ) (J : ℂ) (h : IsTwistedWeightedOrbitalIntegralOn K L A σ μ W δ τ φ J) :
    IsTwistedWeightedOrbitalIntegralOn K L A σ μ W (x * δ * x⁻¹) (conjMeasure K L A σ x δ hx τ) φ J := by
  letI : MeasurableSpace G₂ := glBorelOf (L ⊗[K] A)
  haveI : BorelSpace G₂ := borelSpace_glBorelOf (L ⊗[K] A)
  haveI := isTopologicalGroup_tensorGL K L A
  obtain ⟨w, hw, hJ⟩ := h
  refine ⟨fun y => w (x⁻¹ * y), isTwistedSectionFnOn_conj K L A σ x δ hx τ φ w hw, ?_⟩
  rw [hJ]
  haveI := hμ
  have hL := integral_mul_left_eq_self (μ := μ)
    (fun z : G₂ => φ (z⁻¹ * (x * δ * x⁻¹) * sigmaGL K L A σ z) * (W z : ℂ) * ((w (x⁻¹ * z) : ℝ) : ℂ)) x
  rw [← hL]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only
  have h1 : (x * z)⁻¹ * (x * δ * x⁻¹) * sigmaGL K L A σ (x * z) = z⁻¹ * δ * sigmaGL K L A σ z := by
    rw [map_mul, hx]; group
  rw [h1, inv_mul_cancel_left, hW]

end TwA
p2m_reactivate "P2MW.S_AutomorphicForm_twisted_window_values_inv_mul_unitsMap_eq_of_ne_one_of_prime.TwA"

namespace PccArch

open LanglandsTunnell.CubicInduction (diagUnits2)

variable (K : Type) [Field K] [NumberField K]

private theorem _root_.PccArch.glArch_apply (g : GL (Fin 2) (AdeleRing (𝓞 K) K)) (i j : Fin 2) :
    ((AdelicLevel.glArch (𝓞 K) K g : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j =
      AdelicLevel.adeleArch (𝓞 K) K (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))) i j) := rfl

p2m_export "PccArch" "glArch_apply"
theorem val_centralScalar_mul_diagUnits2 (z a b : (AdeleRing (𝓞 K) K)ˣ) :
    ((AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 a b : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
      !![(z : AdeleRing (𝓞 K) K) * a, 0; 0, (z : AdeleRing (𝓞 K) K) * b] := by
  rw [Units.val_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AutomorphicForm.centralScalar, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply]

theorem gamma_entries (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) :
    ((AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 0 = 0 ∧
    ((AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 1 = 0 ∧
    ((AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 0 -
      ((AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 1 =
      AdelicLevel.adeleArch (𝓞 K) K (z : AdeleRing (𝓞 K) K) *
        AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K) - 1) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [glArch_apply, val_centralScalar_mul_diagUnits2, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, map_zero]
  rw [← map_mul, ← map_sub, mul_sub, mul_one, Units.val_one, mul_one, Units.coe_map, MonoidHom.coe_coe]

theorem isUnit_gamma_sub (u : Kˣ) (hu1 : (u : K) ≠ 1) (z : (AdeleRing (𝓞 K) K)ˣ) :
    IsUnit (((AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 0 -
      ((AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 1) := by
  rw [(gamma_entries K u z).2.2]
  refine (z.isUnit.map _).mul ?_
  rw [← map_one (algebraMap K (AdeleRing (𝓞 K) K)), ← map_sub]
  exact ((isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hu1)).map _).map _

end PccArch
p2m_reactivate "P2MW.S_AutomorphicForm_twisted_window_values_inv_mul_unitsMap_eq_of_ne_one_of_prime.TwA"
namespace E8A
namespace TW

section T1

variable (K : Type) [Field K] [NumberField K]

theorem adelicWeyl_val_apply (i j : Fin 2) :
    ((AutomorphicForm.adelicWeyl (𝓞 K) K : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j =
      if i = j then 0 else 1 := by
  have : ((AutomorphicForm.adelicWeyl (𝓞 K) K : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j =
      algebraMap K (AdeleRing (𝓞 K) K) ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K) i j) := rfl
  rw [this]
  fin_cases i <;> fin_cases j <;> simp

theorem adelicWeyl_inv :
    (AutomorphicForm.adelicWeyl (𝓞 K) K)⁻¹ = AutomorphicForm.adelicWeyl (𝓞 K) K := by
  show (AutomorphicForm.globalPoints (𝓞 K) K AutomorphicForm.gl2Weyl)⁻¹ = AutomorphicForm.globalPoints (𝓞 K) K AutomorphicForm.gl2Weyl
  rw [← map_inv, AutomorphicForm.gl2Weyl_inv]

theorem val_centralScalar_mul_diagUnits2 (z a b : (AdeleRing (𝓞 K) K)ˣ) :
    ((AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 a b : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
      !![(z : AdeleRing (𝓞 K) K) * a, 0; 0, (z : AdeleRing (𝓞 K) K) * b] := by
  rw [Units.val_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AutomorphicForm.centralScalar, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply]

theorem gamma_inv_eq_conj (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) :
    AutomorphicForm.centralScalar (𝓞 K) K (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) *
        diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u⁻¹) 1 =
      AutomorphicForm.adelicWeyl (𝓞 K) K *
        (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) *
        (AutomorphicForm.adelicWeyl (𝓞 K) K)⁻¹ := by
  rw [adelicWeyl_inv]
  have hu1 : (algebraMap K (AdeleRing (𝓞 K) K) (u : K)) * (algebraMap K (AdeleRing (𝓞 K) K) ((u : K)⁻¹)) = 1 := by
    rw [← map_mul, mul_inv_cancel₀ u.ne_zero, map_one]
  apply Units.ext
  simp only [Units.val_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AutomorphicForm.centralScalar, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply,
      adelicWeyl_val_apply, Units.coe_map, MonoidHom.coe_coe, mul_assoc, hu1]

theorem glArch_gamma_apply (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) (i j : Fin 2) :
    ((AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2
        (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) : GL (Fin 2) (InfiniteAdeleRing K)) :
        Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j =
      ((!![(z : AdeleRing (𝓞 K) K) * algebraMap K (AdeleRing (𝓞 K) K) (u : K), 0; 0, (z : AdeleRing (𝓞 K) K)] :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).1 := by
  rw [AdelicLevel.glArch_apply, val_centralScalar_mul_diagUnits2]
  simp [Units.coe_map, MonoidHom.coe_coe]

theorem isRegularSemisimple_glArch_gamma (u : Kˣ) (hu : (u : K) ≠ 1) (z : (AdeleRing (𝓞 K) K)ˣ) :
    AutomorphicForm.IsRegularSemisimple (AdelicLevel.glArch (𝓞 K) K
      (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) := by
  unfold AutomorphicForm.IsRegularSemisimple
  rw [Matrix.trace_fin_two, Matrix.det_fin_two]
  simp only [glArch_gamma_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  have h0 : ((0 : AdeleRing (𝓞 K) K).1) = 0 := rfl
  rw [h0, mul_zero, sub_zero]
  have key : IsUnit (((z : AdeleRing (𝓞 K) K) * algebraMap K (AdeleRing (𝓞 K) K) (u : K)).1 - ((z : AdeleRing (𝓞 K) K)).1) := by
    have h1 : ((z : AdeleRing (𝓞 K) K) * algebraMap K (AdeleRing (𝓞 K) K) (u : K)).1 - ((z : AdeleRing (𝓞 K) K)).1 =
        AdelicLevel.adeleArch (𝓞 K) K ((z : AdeleRing (𝓞 K) K) * (algebraMap K (AdeleRing (𝓞 K) K) ((u : K) - 1))) := by
      rw [map_sub, map_one, mul_sub, mul_one]; rfl
    rw [h1]
    exact (z.isUnit.mul (((isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hu)).map _))).map _
  have : (((z : AdeleRing (𝓞 K) K) * algebraMap K (AdeleRing (𝓞 K) K) (u : K)).1 + ((z : AdeleRing (𝓞 K) K)).1) ^ 2 -
      4 * (((z : AdeleRing (𝓞 K) K) * algebraMap K (AdeleRing (𝓞 K) K) (u : K)).1 * ((z : AdeleRing (𝓞 K) K)).1) =
      (((z : AdeleRing (𝓞 K) K) * algebraMap K (AdeleRing (𝓞 K) K) (u : K)).1 - ((z : AdeleRing (𝓞 K) K)).1) ^ 2 := by ring
  rw [this]
  exact key.pow 2

theorem finComponent_gamma_apply (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) (i j : Fin 2) :
    ((AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K
      (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) :
        GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j =
      ((!![(z : AdeleRing (𝓞 K) K) * algebraMap K (AdeleRing (𝓞 K) K) (u : K), 0; 0, (z : AdeleRing (𝓞 K) K)] :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 v := by
  rw [AdelicLevel.finComponent_apply, AdelicLevel.glFin_apply, val_centralScalar_mul_diagUnits2]
  simp [Units.coe_map, MonoidHom.coe_coe]

theorem isRegularSemisimple_finComponent_gamma (u : Kˣ) (hu : (u : K) ≠ 1)
    (z : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    AutomorphicForm.IsRegularSemisimple (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K
      (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) ∧
    ((AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K
      (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) :
        GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 ∧
    ((AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K
      (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) :
        GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold AutomorphicForm.IsRegularSemisimple
    rw [Matrix.trace_fin_two, Matrix.det_fin_two]
    simp only [finComponent_gamma_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    have h0 : ((0 : AdeleRing (𝓞 K) K).2) v = 0 := rfl
    rw [h0, mul_zero, sub_zero]
    have key : IsUnit ((((z : AdeleRing (𝓞 K) K) * algebraMap K (AdeleRing (𝓞 K) K) (u : K)).2) v - (((z : AdeleRing (𝓞 K) K)).2) v) := by
      have h1 : (((z : AdeleRing (𝓞 K) K) * algebraMap K (AdeleRing (𝓞 K) K) (u : K)).2) v - (((z : AdeleRing (𝓞 K) K)).2) v =
          AdelicLevel.finAdeleEval (𝓞 K) K v (AdelicLevel.adeleFin (𝓞 K) K
            ((z : AdeleRing (𝓞 K) K) * (algebraMap K (AdeleRing (𝓞 K) K) ((u : K) - 1)))) := by
        rw [map_sub, map_one, mul_sub, mul_one, map_sub, map_sub]; rfl
      rw [h1]
      exact ((z.isUnit.mul (((isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hu)).map _))).map _).map _
    have : ((((z : AdeleRing (𝓞 K) K) * algebraMap K (AdeleRing (𝓞 K) K) (u : K)).2) v + (((z : AdeleRing (𝓞 K) K)).2) v) ^ 2 -
        4 * ((((z : AdeleRing (𝓞 K) K) * algebraMap K (AdeleRing (𝓞 K) K) (u : K)).2) v * (((z : AdeleRing (𝓞 K) K)).2) v) =
        ((((z : AdeleRing (𝓞 K) K) * algebraMap K (AdeleRing (𝓞 K) K) (u : K)).2) v - (((z : AdeleRing (𝓞 K) K)).2) v) ^ 2 := by ring
    rw [this]
    exact key.pow 2
  · rw [finComponent_gamma_apply]; rfl
  · rw [finComponent_gamma_apply]; rfl

end T1
p2m_reactivate "P2MW.S_AutomorphicForm_twisted_window_values_inv_mul_unitsMap_eq_of_ne_one_of_prime.TwA"

section Generic

variable {A : Type*} [CommRing A]

theorem weyl_mul_self (w : GL (Fin 2) A) (hw : (w : Matrix (Fin 2) (Fin 2) A) = !![0, 1; 1, 0]) : w * w = 1 := by
  apply Units.ext
  simp only [Units.val_mul, hw, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem weyl_inv_eq (w : GL (Fin 2) A) (hw : (w : Matrix (Fin 2) (Fin 2) A) = !![0, 1; 1, 0]) : w⁻¹ = w :=
  inv_eq_of_mul_eq_one_left (weyl_mul_self w hw)

theorem map_weyl {B : Type*} [CommRing B] (φ : A →+* B) (w : GL (Fin 2) A)
    (hw : (w : Matrix (Fin 2) (Fin 2) A) = !![0, 1; 1, 0]) :
    ((Matrix.GeneralLinearGroup.map φ w : GL (Fin 2) B) : Matrix (Fin 2) (Fin 2) B) = !![0, 1; 1, 0] := by
  ext i j
  change φ ((w : Matrix (Fin 2) (Fin 2) A) i j) = _
  rw [hw]
  fin_cases i <;> fin_cases j <;> simp

theorem weight_weyl_mul {F : Type*} [NormedField F] (w : GL (Fin 2) F)
    (hw : (w : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0]) (y : GL (Fin 2) F) :
    AutomorphicForm.LocalWeight.weight (w * y) = AutomorphicForm.LocalWeight.weight y := by
  unfold AutomorphicForm.LocalWeight.weight AdelicHeight.rowMaxNorm
  have h00 : ((w * y : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 = (y : Matrix (Fin 2) (Fin 2) F) 1 0 := by
    simp [Units.val_mul, hw, Matrix.mul_apply, Fin.sum_univ_two]
  have h01 : ((w * y : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 1 = (y : Matrix (Fin 2) (Fin 2) F) 1 1 := by
    simp [Units.val_mul, hw, Matrix.mul_apply, Fin.sum_univ_two]
  have h10 : ((w * y : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = (y : Matrix (Fin 2) (Fin 2) F) 0 0 := by
    simp [Units.val_mul, hw, Matrix.mul_apply, Fin.sum_univ_two]
  have h11 : ((w * y : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 1 = (y : Matrix (Fin 2) (Fin 2) F) 0 1 := by
    simp [Units.val_mul, hw, Matrix.mul_apply, Fin.sum_univ_two]
  have hdet : ‖((w * y : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det‖ = ‖(y : Matrix (Fin 2) (Fin 2) F).det‖ := by
    rw [Units.val_mul, Matrix.det_mul, norm_mul, hw]
    simp [Matrix.det_fin_two]
  rw [h00, h01, h10, h11, hdet, mul_comm (max _ _) (max _ _)]

theorem conj_mem_integralUnitsSet_iff (U : Set A) (w g : GL (Fin 2) A)
    (hw : (w : Matrix (Fin 2) (Fin 2) A) = !![0, 1; 1, 0]) :
    w * g * w⁻¹ ∈ AutomorphicForm.integralUnitsSet U ↔ g ∈ AutomorphicForm.integralUnitsSet U := by
  have hwi : ((w⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = !![0, 1; 1, 0] := by
    rw [weyl_inv_eq _ hw, hw]
  have perm : ∀ (M : Matrix (Fin 2) (Fin 2) A),
      (!![0, 1; 1, 0] * M * !![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) A) = !![M 1 1, M 1 0; M 0 1, M 0 0] := fun M => by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, Matrix.vecHead, Matrix.vecTail]
  have hval : ((w * g * w⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) =
      !![((g : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 1, ((g : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 0;
        ((g : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 1, ((g : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 0] := by
    rw [Units.val_mul, Units.val_mul, hw, hwi]; exact perm _
  have hinv : (((w * g * w⁻¹)⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) =
      !![((g⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 1, ((g⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 0;
        ((g⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 1, ((g⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 0] := by
    rw [show (w * g * w⁻¹)⁻¹ = w * g⁻¹ * w⁻¹ by rw [mul_inv_rev, mul_inv_rev, inv_inv, mul_assoc], Units.val_mul,
      Units.val_mul, hw, hwi]
    exact perm _
  simp only [AutomorphicForm.mem_integralUnitsSet, hval, hinv]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · fin_cases i <;> fin_cases j
      · simpa using h1 1 1
      · simpa using h1 1 0
      · simpa using h1 0 1
      · simpa using h1 0 0
    · fin_cases i <;> fin_cases j
      · simpa using h2 1 1
      · simpa using h2 1 0
      · simpa using h2 0 1
      · simpa using h2 0 0
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · fin_cases i <;> fin_cases j
      · simpa using h1 1 1
      · simpa using h1 1 0
      · simpa using h1 0 1
      · simpa using h1 0 0
    · fin_cases i <;> fin_cases j
      · simpa using h2 1 1
      · simpa using h2 1 0
      · simpa using h2 0 1
      · simpa using h2 0 0

end Generic
p2m_reactivate "P2MW.S_AutomorphicForm_twisted_window_values_inv_mul_unitsMap_eq_of_ne_one_of_prime.TwA"

section T2

theorem sigmaGL_toTensorGL (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]
    (σ : L ≃ₐ[K] L) (g : GL (Fin 2) A) :
    AutomorphicForm.sigmaGL K L A σ (AutomorphicForm.toTensorGL K L A g) = AutomorphicForm.toTensorGL K L A g := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change AutomorphicForm.sigmaTensor K L A σ
      ((Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom ((g : Matrix (Fin 2) (Fin 2) A) i j)) =
    (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom ((g : Matrix (Fin 2) (Fin 2) A) i j)
  simp [AutomorphicForm.sigmaTensor, Algebra.TensorProduct.includeRight_apply]

theorem normString_conj_of_sigmaGL_eq (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]
    (σ : L ≃ₐ[K] L) (G δ : GL (Fin 2) (L ⊗[K] A)) (hG : AutomorphicForm.sigmaGL K L A σ G = G) :
    AutomorphicForm.normString K L A σ (G * δ * G⁻¹) = G * AutomorphicForm.normString K L A σ δ * G⁻¹ := by
  unfold AutomorphicForm.normString
  have hiter : ∀ i : ℕ, (⇑(AutomorphicForm.sigmaGL K L A σ))^[i] (G * δ * G⁻¹) =
      G * ((⇑(AutomorphicForm.sigmaGL K L A σ))^[i] δ) * G⁻¹ := by
    intro i
    induction i with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', ih, map_mul, map_mul, map_inv, hG, Function.iterate_succ_apply']
  have hmap : (List.range (Module.finrank K L)).map (fun i => (⇑(AutomorphicForm.sigmaGL K L A σ))^[i] (G * δ * G⁻¹)) =
      ((List.range (Module.finrank K L)).map (fun i => (⇑(AutomorphicForm.sigmaGL K L A σ))^[i] δ)).map (MulAut.conj G) := by
    rw [List.map_map]
    congr 1
    funext i
    rw [Function.comp_apply, MulAut.conj_apply, hiter]
  rw [hmap, ← map_list_prod, MulAut.conj_apply]

end T2
p2m_reactivate "P2MW.S_AutomorphicForm_twisted_window_values_inv_mul_unitsMap_eq_of_ne_one_of_prime.TwA"

section Weyl

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

omit L in
theorem adelicWeyl_val :
    ((AutomorphicForm.adelicWeyl (𝓞 K) K : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
      !![0, 1; 1, 0] :=
  map_weyl (algebraMap K (AdeleRing (𝓞 K) K)) AutomorphicForm.gl2Weyl AutomorphicForm.gl2Weyl_val

omit L in
theorem glArch_adelicWeyl_val :
    ((AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K) : GL (Fin 2) (InfiniteAdeleRing K)) :
      Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) = !![0, 1; 1, 0] :=
  map_weyl _ _ (adelicWeyl_val K)

omit L in
theorem finComponent_adelicWeyl_val (v : HeightOneSpectrum (𝓞 K)) :
    ((AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K)) :
      GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = !![0, 1; 1, 0] := by
  have h1 := map_weyl (AdelicLevel.adeleFin (𝓞 K) K) _ (adelicWeyl_val K)
  exact map_weyl _ _ h1

theorem toTensorGL_glArch_adelicWeyl_val :
    ((AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K)
        (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K)) : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :
      Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) = !![0, 1; 1, 0] :=
  map_weyl _ _ (glArch_adelicWeyl_val K)

theorem toTensorGL_finComponent_adelicWeyl_val (v : HeightOneSpectrum (𝓞 K)) :
    ((AutomorphicForm.toTensorGL K L (v.adicCompletion K)
        (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K))) :
        GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) = !![0, 1; 1, 0] :=
  map_weyl _ _ (finComponent_adelicWeyl_val K v)

theorem archIdentGL_toTensorGL_glArch_adelicWeyl :
    AutomorphicForm.archIdentGL K L (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K)
        (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K))) =
      AdelicLevel.glArch (𝓞 L) L (AutomorphicForm.adelicWeyl (𝓞 L) L) := by
  apply Units.ext
  have h1 : ((AutomorphicForm.archIdentGL K L (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K)
        (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K))) : GL (Fin 2) (InfiniteAdeleRing L)) :
        Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) = !![0, 1; 1, 0] :=
    map_weyl (AutomorphicForm.archIdent K L) _ (toTensorGL_glArch_adelicWeyl_val K L)
  rw [h1, glArch_adelicWeyl_val L]

theorem archWeight_toTensorGL_adelicWeyl_mul (y : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :
    (-Real.log (AutomorphicForm.WindowedSiegel.archHeight L (AutomorphicForm.archIdentGL K L
          (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K)) * y)))
        - Real.log (AutomorphicForm.WindowedSiegel.archHeight L
            (AdelicLevel.glArch (𝓞 L) L (AutomorphicForm.adelicWeyl (𝓞 L) L) *
              AutomorphicForm.archIdentGL K L
                (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K)) * y)))) =
      (-Real.log (AutomorphicForm.WindowedSiegel.archHeight L (AutomorphicForm.archIdentGL K L y))
        - Real.log (AutomorphicForm.WindowedSiegel.archHeight L
            (AdelicLevel.glArch (𝓞 L) L (AutomorphicForm.adelicWeyl (𝓞 L) L) * AutomorphicForm.archIdentGL K L y))) := by
  rw [map_mul, archIdentGL_toTensorGL_glArch_adelicWeyl, ← mul_assoc,
    weyl_mul_self _ (glArch_adelicWeyl_val L), one_mul]
  ring

theorem semiLocalWeight_toTensorGL_weyl_mul (v : HeightOneSpectrum (𝓞 K)) (x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    AutomorphicForm.semiLocalWeight K L v
        (AutomorphicForm.toTensorGL K L (v.adicCompletion K)
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K))) * x) =
      AutomorphicForm.semiLocalWeight K L v x := by
  unfold AutomorphicForm.semiLocalWeight
  congr 1
  funext w
  rw [map_mul]
  exact weight_weyl_mul _ (map_weyl _ _ (toTensorGL_finComponent_adelicWeyl_val K L v)) _

theorem conj_mem_semiLocalIntegralSet_iff (v : HeightOneSpectrum (𝓞 K)) (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    AutomorphicForm.toTensorGL K L (v.adicCompletion K)
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K))) * t *
        (AutomorphicForm.toTensorGL K L (v.adicCompletion K)
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K))))⁻¹ ∈
        AutomorphicForm.semiLocalIntegralSet K L v ↔
      t ∈ AutomorphicForm.semiLocalIntegralSet K L v :=
  conj_mem_integralUnitsSet_iff _ _ _ (toTensorGL_finComponent_adelicWeyl_val K L v)

end Weyl
p2m_reactivate "P2MW.S_AutomorphicForm_twisted_window_values_inv_mul_unitsMap_eq_of_ne_one_of_prime.TwA"

section T3

theorem isNormOf_conj (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]
    (σ : L ≃ₐ[K] L) (g γ : GL (Fin 2) A) (δ : GL (Fin 2) (L ⊗[K] A))
    (h : AutomorphicForm.IsNormOf K L A σ γ δ) : AutomorphicForm.IsNormOf K L A σ (g * γ * g⁻¹) δ := by
  obtain ⟨y, hy⟩ := h
  refine ⟨y * (AutomorphicForm.toTensorGL K L A g)⁻¹, ?_⟩
  unfold AutomorphicForm.IsNormConjugator at hy ⊢
  rw [map_mul, map_mul, map_inv, hy, mul_inv_rev, inv_inv]
  group

theorem exists_isNormOf_conj_iff (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]
    (σ : L ≃ₐ[K] L) (g γ : GL (Fin 2) A) :
    (∃ δ, AutomorphicForm.IsNormOf K L A σ (g * γ * g⁻¹) δ) ↔ (∃ δ, AutomorphicForm.IsNormOf K L A σ γ δ) := by
  constructor
  · rintro ⟨δ, h⟩
    refine ⟨δ, ?_⟩
    have := isNormOf_conj K L A σ g⁻¹ _ δ h
    simpa [mul_assoc] using this
  · rintro ⟨δ, h⟩
    exact ⟨δ, isNormOf_conj K L A σ g γ δ h⟩

end T3
p2m_reactivate "P2MW.S_AutomorphicForm_twisted_window_values_inv_mul_unitsMap_eq_of_ne_one_of_prime.TwA"

end E8A.TW
p2m_reactivate "P2MW.S_AutomorphicForm_twisted_window_values_inv_mul_unitsMap_eq_of_ne_one_of_prime.TwA"
p2m_reactivate "P2MW.S_AutomorphicForm_twisted_window_values_inv_mul_unitsMap_eq_of_ne_one_of_prime.TwA"

namespace TwB

open AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

variable (K : Type) [Field K] [NumberField K]

theorem units_inv_ne_one (u : Kˣ) (hu : (u : K) ≠ 1) : ((u⁻¹ : Kˣ) : K) ≠ 1 := by
  intro h
  apply hu
  have : (u⁻¹ : Kˣ) = 1 := Units.ext h
  rw [inv_eq_one] at this
  rw [this, Units.val_one]

theorem isRegularSemisimple_of_diag {A : Type} [CommRing A] (g : GL (Fin 2) A)
    (h10 : (g : Matrix (Fin 2) (Fin 2) A) 1 0 = 0) (h01 : (g : Matrix (Fin 2) (Fin 2) A) 0 1 = 0)
    (hreg : IsUnit ((g : Matrix (Fin 2) (Fin 2) A) 0 0 - (g : Matrix (Fin 2) (Fin 2) A) 1 1)) :
    AutomorphicForm.IsRegularSemisimple g := by
  unfold AutomorphicForm.IsRegularSemisimple
  have : Matrix.trace (g : Matrix (Fin 2) (Fin 2) A) ^ 2 - 4 * Matrix.det (g : Matrix (Fin 2) (Fin 2) A) =
      ((g : Matrix (Fin 2) (Fin 2) A) 0 0 - (g : Matrix (Fin 2) (Fin 2) A) 1 1) ^ 2 := by
    rw [Matrix.trace_fin_two, Matrix.det_fin_two, h10, h01]; ring
  rw [this]
  exact hreg.pow 2

theorem continuous_toTensorGL (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous (AutomorphicForm.toTensorGL K L A) := by
  have h : (⇑(Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A)) = fun a : A => a • (1 : L ⊗[K] A) := by
    funext a
    rw [AutomorphicForm.rightActions_smul_eq, mul_one]
    rfl
  have hc : Continuous (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) := by
    rw [h]
    exact (IsModuleTopology.continuous_of_linearMap (LinearMap.toSpanSingleton A (L ⊗[K] A) 1) : _)
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  unfold AutomorphicForm.toTensorGL Matrix.GeneralLinearGroup.map
  exact Units.continuous_map (continuous_id.matrix_map hc)

end TwB
p2m_reactivate "P2MW.S_AutomorphicForm_twisted_window_values_inv_mul_unitsMap_eq_of_ne_one_of_prime.TwA"

end
p2m_reactivate "P2MW.S_AutomorphicForm_twisted_window_values_inv_mul_unitsMap_eq_of_ne_one_of_prime.TwA"

open scoped TensorProduct TensorProduct.RightActions in
open scoped Classical in

open AutomorphicForm in
open scoped TensorProduct.RightActions in
set_option maxHeartbeats 1600000 in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (hprime : (Module.finrank K L).Prime)
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure]
    (SK T : Finset (HeightOneSpectrum (𝓞 K))) (hTS : Disjoint T SK)

    (faK : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (hfaK : AutomorphicForm.IsArchTestFactor K faK)
    (fSK : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hfSK : ∀ v ∈ SK, AutomorphicForm.IsLocalTestFn K v (fSK v))
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (hφa : AutomorphicForm.IsArchTestFactor L φa)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (hφS : ∀ v ∈ SK, AutomorphicForm.IsSemiLocalTestFn K L v (φS v))
    (hmatchA : AutomorphicForm.AreMatchingArch K L σ φa faK)
    (hmatchS : ∀ v ∈ SK, AutomorphicForm.AreMatchingLocal K L v σ (φS v) (fSK v))

    (fT : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hfT : ∀ v ∈ T, AutomorphicForm.IsLocalTestFn K v (fT v))
    (hmatchT : ∀ v ∈ T, ∃ φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ,
      AutomorphicForm.IsSemiLocalTestFn K L v φv ∧ AutomorphicForm.AreMatchingLocal K L v σ φv (fT v))
    (hunit : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK → v ∉ T →
      AutomorphicForm.AreMatchingLocal K L v σ
        ((AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ))
        ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ)))

    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
    (hf : AutomorphicForm.IsUnitFactorization K (SK ∪ T) f faK ff (fun v => if v ∈ T then fT v else fSK v))

    (νA : @Measure (GL (Fin 2) (InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)))
    (cG : ℝ)
    (hG : ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
        (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.glBorelOf (InfiniteAdeleRing K)] fa νA →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.localGLBorel K v] (fS v)
          (AutomorphicForm.localHaar K v)) →
        (∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
          (∀ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g) ∈
              AutomorphicForm.localIntegralSet K v) →
            f g = fa (AdelicLevel.glArch (𝓞 K) K g) *
              ∏ v ∈ S, fS v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g))) →
        (∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
          (∃ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g) ∉
              AutomorphicForm.localIntegralSet K v) → f g = 0) →
          ∫ g, f g ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
            cG * (∫ x, fa x ∂νA) * ∏ v ∈ S, ∫ y, fS v y ∂(AutomorphicForm.localHaar K v))

    (cτK : ℝ) (hcτK : 0 < cτK)
    (τG : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ),
      Measure (Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K)))))
    (hτG : ∀ u z, ((u : Kˣ) : K) ≠ 1 → (τG u z).IsHaarMeasure)
    (hτGc : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ,
      ∫ t : Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          g (t : GL (Fin 2) (AdeleRing (𝓞 K) K)) ∂(τG u z) =
        cτK * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ, g (diagUnits2 p.1 p.2) ∂(νZK.prod νZK))
    (τA : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ),
      @Measure (Subgroup.centralizer
          ({AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (InfiniteAdeleRing K))))
        (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))))
    (hτA : ∀ u z, ((u : Kˣ) : K) ≠ 1 → @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τA u z))
    (τF : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)),
      @Measure (AutomorphicForm.localCentralizer K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))))
        (AutomorphicForm.localCentralizerBorel K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))))
    (hτF : ∀ u z v, ((u : Kˣ) : K) ≠ 1 → @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.localCentralizerBorel K v
        (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))) (τF u z v))
    (hτF1 : ∀ u z v, ((u : Kˣ) : K) ≠ 1 → τF u z v (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1)
    (cT : ℝ) (hcT : 0 < cT)
    (hT : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) (S : Finset (HeightOneSpectrum (𝓞 K)))
        (W : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (Wa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
        (u : K) ≠ 1 →
        AEStronglyMeasurable[AutomorphicForm.centralizerBorel (InfiniteAdeleRing K)
          (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))] (fun t => Wa t) (τA u z) →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.localCentralizerBorel K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))]
            (fun t => WS v t) (τF u z v)) →
        (∀ t : Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          (∀ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t) ∈
              AutomorphicForm.localIntegralSet K v) →
            W t = Wa (AdelicLevel.glArch (𝓞 K) K t) *
              ∏ v ∈ S, WS v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t))) →
        (∀ t : Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          (∃ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t) ∉
              AutomorphicForm.localIntegralSet K v) → W t = 0) →
          ∫ t, W t ∂(τG u z) = cT * (∫ t, Wa t ∂(τA u z)) * ∏ v ∈ S, ∫ t, WS v t ∂(τF u z v))

    (IA : Kˣ → (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hIA : ∀ u z, ((u : Kˣ) : K) ≠ 1 → AutomorphicForm.IsOrbitalIntegralOn (InfiniteAdeleRing K) νA
      (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) (τA u z) faK (IA u z))
    (IF : Kˣ → (AdeleRing (𝓞 K) K)ˣ → HeightOneSpectrum (𝓞 K) → ℂ)
    (hIF : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ v ∈ SK, AutomorphicForm.IsOrbitalIntegral K v
      (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τF u z v) (fSK v) (IF u z v))
    (JA : Kˣ → (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hJA : ∀ u z, ((u : Kˣ) : K) ≠ 1 → AutomorphicForm.IsWeightedOrbitalIntegralOn (InfiniteAdeleRing K) νA
      (fun y : GL (Fin 2) (InfiniteAdeleRing K) =>
        -Real.log (AutomorphicForm.WindowedSiegel.archHeight K y)
          - Real.log (AutomorphicForm.WindowedSiegel.archHeight K
              (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K) * y)))
      (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) (τA u z) faK (JA u z))
    (JF : Kˣ → (AdeleRing (𝓞 K) K)ˣ → HeightOneSpectrum (𝓞 K) → ℂ)
    (hJF : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ v ∈ SK, AutomorphicForm.IsWeightedOrbitalIntegral K v
      (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τF u z v) (fSK v) (JF u z v))

    (νA' : @Measure (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)))
    (hνA : νA = AutomorphicForm.archHaarK K) (hνA' : νA' = AutomorphicForm.archHaarL K L)
    (δA : Kˣ → (AdeleRing (𝓞 K) K)ˣ → GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
    (hδA : ∀ u z, ((u : Kˣ) : K) ≠ 1 → (∃ δ, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) δ) →
      AutomorphicForm.normString K L (InfiniteAdeleRing K) σ (δA u z) =
        AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))
    (τA' : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ),
      Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ (δA u z)))
    (hτA' : ∀ u z, ((u : Kˣ) : K) ≠ 1 → (τA' u z).IsHaarMeasure)
    (hτA'c : ∀ u z, ((u : Kˣ) : K) ≠ 1 → (∃ δ, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) δ) →
      AutomorphicForm.Coupled K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) (δA u z) 1 (τA u z) (τA' u z))
    (δF : Kˣ → (AdeleRing (𝓞 K) K)ˣ → ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδF : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ v ∈ SK, (∃ δ, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) δ) →
      AutomorphicForm.normString K L (v.adicCompletion K) σ (δF u z v) =
        AutomorphicForm.toTensorGL K L (v.adicCompletion K) (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))))
    (τF' : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)),
      Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (δF u z v)))
    (hτF' : ∀ u z v, ((u : Kˣ) : K) ≠ 1 → (τF' u z v).IsHaarMeasure)
    (hτF'1 : ∀ u z v, ((u : Kˣ) : K) ≠ 1 → τF' u z v (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v) = 1)
    (JA' : Kˣ → (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hJA' : ∀ u z, ((u : Kˣ) : K) ≠ 1 → (∃ δ, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) δ) →
      AutomorphicForm.IsTwistedWeightedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ νA'
        (fun y : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
          -Real.log (AutomorphicForm.WindowedSiegel.archHeight L (AutomorphicForm.archIdentGL K L y))
            - Real.log (AutomorphicForm.WindowedSiegel.archHeight L
                (AdelicLevel.glArch (𝓞 L) L (AutomorphicForm.adelicWeyl (𝓞 L) L) *
                  AutomorphicForm.archIdentGL K L y)))
        (δA u z) (τA' u z) (φa ∘ AutomorphicForm.archIdentGL K L) (JA' u z))
    (hJA'0 : ∀ u z, ((u : Kˣ) : K) ≠ 1 → (¬ ∃ δ, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) δ) → JA' u z = 0)
    (JF' : Kˣ → (AdeleRing (𝓞 K) K)ˣ → HeightOneSpectrum (𝓞 K) → ℂ)
    (hJF' : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ v ∈ SK, (∃ δ, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) δ) →
      AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ (δF u z v) (τF' u z v) (φS v) (JF' u z v))
    (hJF'0 : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ v ∈ SK, (¬ ∃ δ, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) δ) →
      JF' u z v = 0)

    (IT : Kˣ → (AdeleRing (𝓞 K) K)ˣ → HeightOneSpectrum (𝓞 K) → ℂ)
    (hIT : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ v ∈ T, AutomorphicForm.IsOrbitalIntegral K v
      (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τF u z v) (fT v) (IT u z v))
    (IU : Kˣ → (AdeleRing (𝓞 K) K)ˣ → HeightOneSpectrum (𝓞 K) → ℂ)
    (hIU : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ v ∉ SK ∪ T, AutomorphicForm.IsOrbitalIntegral K v
      (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τF u z v)
        ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ)) (IU u z v))
    :
    ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ), (u : K) ≠ 1 →
      ((∃ δ, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) δ) →
        JA' u⁻¹ (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) = JA' u z) ∧
      (∀ v ∈ SK,
        (∃ δ, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ
            (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) δ) →
          JF' u⁻¹ (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) v = JF' u z v) := by
  intro u z hu
  classical

  have hu' : ((u⁻¹ : Kˣ) : K) ≠ 1 := TwB.units_inv_ne_one K u hu
  set ιu : (AdeleRing (𝓞 K) K)ˣ := Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u with hιu
  set z' : (AdeleRing (𝓞 K) K)ˣ := z * ιu with hz'
  set γ₁ : GL (Fin 2) (AdeleRing (𝓞 K) K) := AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 ιu 1 with hγ₁
  set γ₂ : GL (Fin 2) (AdeleRing (𝓞 K) K) :=
    AutomorphicForm.centralScalar (𝓞 K) K z' * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u⁻¹) 1 with hγ₂
  set wA : GL (Fin 2) (AdeleRing (𝓞 K) K) := AutomorphicForm.adelicWeyl (𝓞 K) K with hwA
  have hcls : γ₂ = wA * γ₁ * wA⁻¹ := E8A.TW.gamma_inv_eq_conj K u z

  have hN := AutomorphicForm.exists_isNormOf_glArch_centralScalar_mul_diagUnits2_iff_inv_and_finComponent_iff_inv K L σ u z
  refine ⟨fun hnorm => ?_, fun v hv hnormv => ?_⟩
  ·
    have hnorm' := hN.1.1 hnorm
    have hJ1 := hJA' u z hu hnorm
    have hδ1 := hδA u z hu hnorm
    have hc1 := hτA'c u z hu hnorm
    have hJ2 := hJA' u⁻¹ (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) hu' hnorm'
    have hδ2 := hδA u⁻¹ (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) hu' hnorm'
    have hc2 := hτA'c u⁻¹ (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) hu' hnorm'

    letI mGL : MeasurableSpace (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)
    haveI : BorelSpace (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := AutomorphicForm.borelSpace_glBorelOf _
    haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L (InfiniteAdeleRing K)
    letI mGK : MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing K)) := AutomorphicForm.glBorelOf (InfiniteAdeleRing K)
    haveI : BorelSpace (GL (Fin 2) (InfiniteAdeleRing K)) := AutomorphicForm.borelSpace_glBorelOf _

    have hWfix : AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K))) = (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K))) :=
      E8A.TW.sigmaGL_toTensorGL K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K))
    have hWwt : ∀ y : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K), (fun y : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
          -Real.log (AutomorphicForm.WindowedSiegel.archHeight L (AutomorphicForm.archIdentGL K L y))
            - Real.log (AutomorphicForm.WindowedSiegel.archHeight L
                (AdelicLevel.glArch (𝓞 L) L (AutomorphicForm.adelicWeyl (𝓞 L) L) *
                  AutomorphicForm.archIdentGL K L y))) ((AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K))) * y) = (fun y : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
          -Real.log (AutomorphicForm.WindowedSiegel.archHeight L (AutomorphicForm.archIdentGL K L y))
            - Real.log (AutomorphicForm.WindowedSiegel.archHeight L
                (AdelicLevel.glArch (𝓞 L) L (AutomorphicForm.adelicWeyl (𝓞 L) L) *
                  AutomorphicForm.archIdentGL K L y))) y :=
      fun y => E8A.TW.archWeight_toTensorGL_adelicWeyl_mul K L y
    obtain ⟨hwt, hwtc⟩ := AutomorphicForm.archWeight_archIdentGL_diagonal_mul_and_continuous K L

    have hclsA : (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u⁻¹) 1)) = (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K)) * (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) * (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K))⁻¹ := by
      rw [show (AutomorphicForm.centralScalar (𝓞 K) K (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u⁻¹) 1) = (AutomorphicForm.adelicWeyl (𝓞 K) K) * (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) * (AutomorphicForm.adelicWeyl (𝓞 K) K)⁻¹ from hcls, map_mul, map_mul, map_inv]
    have hent := PccArch.gamma_entries K u⁻¹ (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)
    have hreg : AutomorphicForm.IsRegularSemisimple (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u⁻¹) 1)) :=
      TwB.isRegularSemisimple_of_diag _ hent.1 hent.2.1 (PccArch.isUnit_gamma_sub K u⁻¹ hu' (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u))

    have hνhaar : @Measure.IsHaarMeasure (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) _ _
        (AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)) νA' := by
      rw [hνA']
      haveI := AutomorphicForm.locallyCompactSpace_tensorGL K L (InfiniteAdeleRing K)
      delta AutomorphicForm.archHaarL
      exact Measure.isHaarMeasure_haarMeasure _
    haveI := hνhaar
    have hμinv : @Measure.IsMulLeftInvariant (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf _) _ νA' :=
      inferInstance

    have hJ1' := TwA.isTwistedWeightedOrbitalIntegralOn_conj K L (InfiniteAdeleRing K) σ νA' hμinv (fun y : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
          -Real.log (AutomorphicForm.WindowedSiegel.archHeight L (AutomorphicForm.archIdentGL K L y))
            - Real.log (AutomorphicForm.WindowedSiegel.archHeight L
                (AdelicLevel.glArch (𝓞 L) L (AutomorphicForm.adelicWeyl (𝓞 L) L) *
                  AutomorphicForm.archIdentGL K L y))) (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K))) (δA u z)
      hWfix hWwt (τA' u z) (φa ∘ AutomorphicForm.archIdentGL K L) (JA' u z) hJ1
    have hτ1' := TwA.isHaarMeasure_conjMeasure K L (InfiniteAdeleRing K) σ (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K))) (δA u z) hWfix (τA' u z) (hτA' u z hu)

    obtain ⟨hI, hII, -⟩ :=
      AutomorphicForm.map_subtypeVal_centralizer_eq_and_map_conj_adelicWeyl_eq_of_forall_integral_eq_mul_integral_prod
        K νZK cτK hcτK τG hτG hτGc τA hτA τF hτF hτF1 cT hcT hT
    have hpin := (hII u z hu).trans (hI u u⁻¹ z (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) hu hu')

    have hcoup1 : AutomorphicForm.Coupled K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u⁻¹) 1)) ((AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K))) * δA u z * (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K)))⁻¹) 1
        (τA u⁻¹ (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)) (TwA.conjMeasure K L (InfiniteAdeleRing K) σ (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K))) (δA u z) hWfix (τA' u z)) := by
      letI mT1 : MeasurableSpace (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ (δA u z)) :=
        AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ (δA u z)
      letI mT1' : MeasurableSpace (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ ((AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K))) * δA u z * (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K)))⁻¹)) :=
        AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ ((AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K))) * δA u z * (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K)))⁻¹)
      letI mC1 : MeasurableSpace (Subgroup.centralizer ({(AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))} : Set (GL (Fin 2) (InfiniteAdeleRing K)))) :=
        AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))
      letI mC2 : MeasurableSpace (Subgroup.centralizer ({(AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u⁻¹) 1))} : Set (GL (Fin 2) (InfiniteAdeleRing K)))) :=
        AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u⁻¹) 1))
      haveI : BorelSpace (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ (δA u z)) := ⟨rfl⟩
      haveI : BorelSpace (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ ((AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K))) * δA u z * (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K)))⁻¹)) := ⟨rfl⟩
      haveI : BorelSpace (Subgroup.centralizer ({(AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))} : Set (GL (Fin 2) (InfiniteAdeleRing K)))) := ⟨rfl⟩
      haveI : BorelSpace (Subgroup.centralizer ({(AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u⁻¹) 1))} : Set (GL (Fin 2) (InfiniteAdeleRing K)))) := ⟨rfl⟩
      have htT : Continuous (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K)) :=
        TwB.continuous_toTensorGL K L (InfiniteAdeleRing K)
      have hcW : Measurable (fun x : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) => (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K))) * x * (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K)))⁻¹) :=
        ((continuous_const.mul continuous_id).mul continuous_const).measurable
      have hv1 : Measurable (fun t : AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ (δA u z) =>
          (1 : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))⁻¹ * (t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) * 1) :=
        ((continuous_const.mul continuous_subtype_val).mul continuous_const).measurable
      have htv : Measurable (fun t : Subgroup.centralizer ({(AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))} : Set (GL (Fin 2) (InfiniteAdeleRing K))) =>
          AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (t : GL (Fin 2) (InfiniteAdeleRing K))) :=
        (htT.comp continuous_subtype_val).measurable
      have hcw : Measurable (fun t : Subgroup.centralizer ({(AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))} : Set (GL (Fin 2) (InfiniteAdeleRing K))) =>
          (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K)) * (t : GL (Fin 2) (InfiniteAdeleRing K)) * (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K))⁻¹) :=
        ((continuous_const.mul continuous_subtype_val).mul continuous_const).measurable
      have hv2 : Measurable (Subtype.val : Subgroup.centralizer ({(AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u⁻¹) 1))} : Set (GL (Fin 2) (InfiniteAdeleRing K))) →
          GL (Fin 2) (InfiniteAdeleRing K)) := continuous_subtype_val.measurable
      unfold AutomorphicForm.Coupled
      have e1 : (fun s : AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ ((AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K))) * δA u z * (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K)))⁻¹) =>
          (1 : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))⁻¹ * (s : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) * 1) = Subtype.val := by
        funext s; simp
      rw [e1, TwA.map_subtypeVal_conjMeasure]
      have e2 : (fun t : AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ (δA u z) =>
          (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K))) * (t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) * (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K)))⁻¹) =
          (fun x : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) => (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K))) * x * (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K)))⁻¹) ∘
            (fun t : AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ (δA u z) =>
              (1 : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))⁻¹ * (t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) * 1) := by
        funext t; simp [mul_assoc]
      rw [e2, ← Measure.map_map hcW hv1]
      have hc1' := hc1
      unfold AutomorphicForm.Coupled at hc1'
      rw [hc1', Measure.map_map hcW htv]
      have e3 : (fun x : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) => (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K))) * x * (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K)))⁻¹) ∘
          (fun t : Subgroup.centralizer ({(AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))} : Set (GL (Fin 2) (InfiniteAdeleRing K))) =>
            AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (t : GL (Fin 2) (InfiniteAdeleRing K))) =
          AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) ∘
            (fun t : Subgroup.centralizer ({(AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))} : Set (GL (Fin 2) (InfiniteAdeleRing K))) =>
              (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K)) * (t : GL (Fin 2) (InfiniteAdeleRing K)) * (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K))⁻¹) := by
        funext t; simp [map_mul, map_inv]
      rw [e3, ← Measure.map_map htT.measurable hcw]
      erw [hpin]
      rw [Measure.map_map htT.measurable hv2]
      rfl
    have hcoup2 : AutomorphicForm.Coupled K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u⁻¹) 1)) (δA u⁻¹ (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)) 1
        (ENNReal.ofReal 1 • τA u⁻¹ (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)) (τA' u⁻¹ (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)) := by
      rw [ENNReal.ofReal_one, one_smul]; exact hc2

    have hδ1' : AutomorphicForm.normString K L (InfiniteAdeleRing K) σ ((AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K))) * δA u z * (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K)))⁻¹) =
        AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u⁻¹) 1)) := by
      have hconjT : ∀ g : GL (Fin 2) (InfiniteAdeleRing K),
          AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) ((AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K)) * g * (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K))⁻¹) =
            (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K))) * AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) g * (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K)))⁻¹ := fun g => by
        rw [map_mul, map_mul, map_inv]
      calc AutomorphicForm.normString K L (InfiniteAdeleRing K) σ ((AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K))) * δA u z * (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K)))⁻¹)
          = (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K))) * AutomorphicForm.normString K L (InfiniteAdeleRing K) σ (δA u z) * (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K)))⁻¹ :=
            E8A.TW.normString_conj_of_sigmaGL_eq K L (InfiniteAdeleRing K) σ (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K))) (δA u z) hWfix
        _ = (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K))) * AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) * (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K)))⁻¹ := by rw [hδ1]
        _ = AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) ((AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K)) * (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) * (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K))⁻¹) := (hconjT _).symm
        _ = AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u⁻¹) 1)) := congrArg _ hclsA.symm
    haveI := hτA u⁻¹ (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) hu'
    have key := AutomorphicForm.eq_inv_mul_of_isTwistedWeightedOrbitalIntegralOn_of_normString_eq_toTensorGL_diagonal_of_coupled_one_smul_infiniteAdeleRing
      K L σ hgen (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u⁻¹) 1)) hreg hent.2.1 hent.1 νA' hνhaar (fun y : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
          -Real.log (AutomorphicForm.WindowedSiegel.archHeight L (AutomorphicForm.archIdentGL K L y))
            - Real.log (AutomorphicForm.WindowedSiegel.archHeight L
                (AdelicLevel.glArch (𝓞 L) L (AutomorphicForm.adelicWeyl (𝓞 L) L) *
                  AutomorphicForm.archIdentGL K L y))) hwtc hwt (τA u⁻¹ (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)) 1 one_pos
      ((AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K))) * δA u z * (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K)))⁻¹) (δA u⁻¹ (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)) hδ1' hδ2
      (TwA.conjMeasure K L (InfiniteAdeleRing K) σ (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K))) (δA u z) hWfix (τA' u z)) hτ1' hcoup1
      (τA' u⁻¹ (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)) (hτA' u⁻¹ (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) hu') hcoup2 φa hφa (JA' u z) (JA' u⁻¹ (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)) hJ1' hJ2
    rw [key]; simp
  ·
    have hnormv' := (hN.2 v).1 hnormv
    have hJ1 := hJF' u z hu v hv hnormv
    have hδ1 := hδF u z hu v hv hnormv
    have hJ2 := hJF' u⁻¹ (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) hu' v hv hnormv'
    have hδ2 := hδF u⁻¹ (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) hu' v hv hnormv'
    obtain ⟨hreg, h01, h10⟩ := E8A.TW.isRegularSemisimple_finComponent_gamma K u⁻¹ hu' (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) v
    letI mGL : MeasurableSpace (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
    haveI : BorelSpace (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := AutomorphicForm.borelSpace_glBorelOf _
    haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L (v.adicCompletion K)
    have hWfix : AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ (AutomorphicForm.toTensorGL K L (v.adicCompletion K) (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K)))) = (AutomorphicForm.toTensorGL K L (v.adicCompletion K) (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K)))) :=
      E8A.TW.sigmaGL_toTensorGL K L (v.adicCompletion K) σ (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K)))
    have hWwt : ∀ x : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
        AutomorphicForm.semiLocalWeight K L v ((AutomorphicForm.toTensorGL K L (v.adicCompletion K) (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K)))) * x) = AutomorphicForm.semiLocalWeight K L v x :=
      fun x => E8A.TW.semiLocalWeight_toTensorGL_weyl_mul K L v x
    have hclsv : (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u⁻¹) 1))) = (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K))) * (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) * (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K)))⁻¹ := by
      rw [show (AutomorphicForm.centralScalar (𝓞 K) K (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u⁻¹) 1) = (AutomorphicForm.adelicWeyl (𝓞 K) K) * (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) * (AutomorphicForm.adelicWeyl (𝓞 K) K)⁻¹ from hcls]
      simp only [map_mul, map_inv]
    have hμv := AutomorphicForm.isHaarMeasure_semiLocalHaar K L v
    haveI := hμv
    have hμinv : @Measure.IsMulLeftInvariant (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (AutomorphicForm.glBorelOf _) _
        (AutomorphicForm.semiLocalHaar K L v) := inferInstance
    have hJ1' := TwA.isTwistedWeightedOrbitalIntegralOn_conj K L (v.adicCompletion K) σ (AutomorphicForm.semiLocalHaar K L v) hμinv
      (AutomorphicForm.semiLocalWeight K L v) (AutomorphicForm.toTensorGL K L (v.adicCompletion K) (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K)))) (δF u z v) hWfix hWwt (τF' u z v) (φS v) (JF' u z v) hJ1
    have hτ1' := TwA.isHaarMeasure_conjMeasure K L (v.adicCompletion K) σ (AutomorphicForm.toTensorGL K L (v.adicCompletion K) (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K)))) (δF u z v) hWfix (τF' u z v) (hτF' u z v hu)

    have hmass : (TwA.conjMeasure K L (v.adicCompletion K) σ (AutomorphicForm.toTensorGL K L (v.adicCompletion K) (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K)))) (δF u z v) hWfix (τF' u z v))
        (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v) = 1 := by
      letI mT1 : MeasurableSpace (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (δF u z v)) :=
        AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (δF u z v)
      letI mT1' : MeasurableSpace (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ ((AutomorphicForm.toTensorGL K L (v.adicCompletion K) (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K)))) * δF u z v * (AutomorphicForm.toTensorGL K L (v.adicCompletion K) (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K))))⁻¹)) :=
        AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ ((AutomorphicForm.toTensorGL K L (v.adicCompletion K) (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K)))) * δF u z v * (AutomorphicForm.toTensorGL K L (v.adicCompletion K) (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K))))⁻¹)
      haveI : BorelSpace (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (δF u z v)) := ⟨rfl⟩
      haveI : BorelSpace (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ ((AutomorphicForm.toTensorGL K L (v.adicCompletion K) (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K)))) * δF u z v * (AutomorphicForm.toTensorGL K L (v.adicCompletion K) (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K))))⁻¹)) := ⟨rfl⟩
      haveI := AutomorphicForm.t2Space_tensorGL K L (v.adicCompletion K)
      have hSm : MeasurableSet (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v :
          Set (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ ((AutomorphicForm.toTensorGL K L (v.adicCompletion K) (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K)))) * δF u z v * (AutomorphicForm.toTensorGL K L (v.adicCompletion K) (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K))))⁻¹))) :=
        ((AutomorphicForm.isCompact_semiLocalIntegralSet K L v).isClosed.preimage continuous_subtype_val).measurableSet
      have hme : Measurable (TwA.conjEquiv K L (v.adicCompletion K) σ (AutomorphicForm.toTensorGL K L (v.adicCompletion K) (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K)))) (δF u z v) hWfix :
          AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (δF u z v) →
            AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ ((AutomorphicForm.toTensorGL K L (v.adicCompletion K) (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K)))) * δF u z v * (AutomorphicForm.toTensorGL K L (v.adicCompletion K) (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K))))⁻¹)) :=
        (TwA.conjEquiv K L (v.adicCompletion K) σ (AutomorphicForm.toTensorGL K L (v.adicCompletion K) (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K)))) (δF u z v) hWfix).continuous.measurable
      unfold TwA.conjMeasure
      rw [Measure.map_apply hme hSm]
      have hset : (TwA.conjEquiv K L (v.adicCompletion K) σ (AutomorphicForm.toTensorGL K L (v.adicCompletion K) (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K)))) (δF u z v) hWfix) ⁻¹'
          (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v) =
          Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v := by
        ext t
        simp only [Set.mem_preimage, TwA.coe_conjEquiv]
        exact E8A.TW.conj_mem_semiLocalIntegralSet_iff K L v (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
      rw [hset]
      exact hτF'1 u z v hu
    have hδ1' : AutomorphicForm.normString K L (v.adicCompletion K) σ ((AutomorphicForm.toTensorGL K L (v.adicCompletion K) (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K)))) * δF u z v * (AutomorphicForm.toTensorGL K L (v.adicCompletion K) (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K))))⁻¹) =
        AutomorphicForm.toTensorGL K L (v.adicCompletion K) (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u⁻¹) 1))) := by
      have hconjT : ∀ g : GL (Fin 2) (v.adicCompletion K),
          AutomorphicForm.toTensorGL K L (v.adicCompletion K) ((AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K))) * g * (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K)))⁻¹) =
            (AutomorphicForm.toTensorGL K L (v.adicCompletion K) (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K)))) * AutomorphicForm.toTensorGL K L (v.adicCompletion K) g * (AutomorphicForm.toTensorGL K L (v.adicCompletion K) (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K))))⁻¹ := fun g => by
        rw [map_mul, map_mul, map_inv]
      calc AutomorphicForm.normString K L (v.adicCompletion K) σ ((AutomorphicForm.toTensorGL K L (v.adicCompletion K) (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K)))) * δF u z v * (AutomorphicForm.toTensorGL K L (v.adicCompletion K) (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K))))⁻¹)
          = (AutomorphicForm.toTensorGL K L (v.adicCompletion K) (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K)))) * AutomorphicForm.normString K L (v.adicCompletion K) σ (δF u z v) * (AutomorphicForm.toTensorGL K L (v.adicCompletion K) (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K))))⁻¹ :=
            E8A.TW.normString_conj_of_sigmaGL_eq K L (v.adicCompletion K) σ (AutomorphicForm.toTensorGL K L (v.adicCompletion K) (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K)))) (δF u z v) hWfix
        _ = (AutomorphicForm.toTensorGL K L (v.adicCompletion K) (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K)))) * AutomorphicForm.toTensorGL K L (v.adicCompletion K) (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) * (AutomorphicForm.toTensorGL K L (v.adicCompletion K) (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K))))⁻¹ := by rw [hδ1]
        _ = AutomorphicForm.toTensorGL K L (v.adicCompletion K) ((AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K))) * (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) * (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K)))⁻¹) := (hconjT _).symm
        _ = AutomorphicForm.toTensorGL K L (v.adicCompletion K) (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u⁻¹) 1))) := congrArg _ hclsv.symm
    have key := AutomorphicForm.eq_of_isTwistedWeightedOrbitalIntegral_of_isTwistedWeightedOrbitalIntegral_of_normString_eq_toTensorGL_diagonal
      K L σ hgen v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u⁻¹) 1))) hreg h01 h10 ((AutomorphicForm.toTensorGL K L (v.adicCompletion K) (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K)))) * δF u z v * (AutomorphicForm.toTensorGL K L (v.adicCompletion K) (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K))))⁻¹) (δF u⁻¹ (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) v) hδ1' hδ2
      (TwA.conjMeasure K L (v.adicCompletion K) σ (AutomorphicForm.toTensorGL K L (v.adicCompletion K) (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K)))) (δF u z v) hWfix (τF' u z v)) hτ1' hmass
      (τF' u⁻¹ (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) v) (hτF' u⁻¹ (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) v hu') (hτF'1 u⁻¹ (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) v hu') (φS v) (hφS v hv)
      (JF' u z v) (JF' u⁻¹ (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) v) hJ1' hJ2
    exact key.symm

end S_AutomorphicForm_twisted_window_values_inv_mul_unitsMap_eq_of_ne_one_of_prime
end P2MW
export P2MW.S_AutomorphicForm_twisted_window_values_inv_mul_unitsMap_eq_of_ne_one_of_prime (solution)
