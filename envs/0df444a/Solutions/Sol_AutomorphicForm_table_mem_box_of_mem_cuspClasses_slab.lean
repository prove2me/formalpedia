-- Prove2me | solution 1 for AutomorphicForm.table_mem_box_of_mem_cuspClasses_slab
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/37ccf14a-9de9-59d8-9206-d98f60725835

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ProductionPins
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_HeckeEigensystem
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_SiegelCovering
import Theorems.Thm_NumberField_TateGlobal_measurableSet_setOf_ideleNorm_det_mem_Icc
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_NumberField_TateGlobal_exists_norm_apply_eq_ideleNorm_rpow
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_det_eq_one_of_isCompact_of_mem
import Theorems.Thm_AutomorphicForm_isCompact_levelOne_inf_finiteAdelicGL2Subgroup
import Theorems.Thm_AutomorphicForm_cosetSum_adjoint_weightedPairing_of_isLsXiFunction
import Theorems.Thm_AutomorphicForm_rightTranslate_adjoint_weightedPairing_of_isLsXiFunction
import Theorems.Thm_AutomorphicForm_setIntegral_mul_conj_mul_ideleNorm_det_rpow_ne_zero_of_isLsXiFunction_of_isFundamentalDomain
import Theorems.Thm_NumberField_AdelicLevel_exists_heckeGen_inv_eq_centralScalar_mul_mul_heckeGen_mul_levelOne_and_mul_det_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_table_mem_box_of_mem_cuspClasses_slab
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_table_mem_box_of_mem_cuspClasses_slab.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering"
p2m_open "IsDedekindDomain MeasureTheory NumberField.AdelicHaar"
open scoped ComplexConjugate BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsIsotypicCuspFormAt isotypicCuspSubmodule isotypicCuspSubmodule_ne_bot_iff cuspClasses productionPinsOf productionPinsOf_gen AdelicGL2 globalPoints centralScalar IsIdeleClassChar IsLsXiFunction finiteAdelicGL2Subgroup lsXiMemberAt_iff HeckeEigensystem.cNorm HeckeEigensystem.cNorm_ne_zero HeckeEigensystem isCompact_levelOne_inf_finiteAdelicGL2Subgroup cosetSum_adjoint_weightedPairing_of_isLsXiFunction rightTranslate_adjoint_weightedPairing_of_isLsXiFunction setIntegral_mul_conj_mul_ideleNorm_det_rpow_ne_zero_of_isLsXiFunction_of_isFundamentalDomain"
namespace SatakeBox
p2m_open "AutomorphicForm"

variable {L : Type} [Field L] [NumberField L]

private theorem b_eq_cNorm_mul_of_isIsotypicCuspFormAt
    (D : Set (AdelicGL2 (𝓞 L) L)) (U : Ideal (𝓞 L) → Subgroup (AdelicGL2 (𝓞 L) L))
    (gen : HeightOneSpectrum (𝓞 L) → AdelicGL2 (𝓞 L) L) (B : Set (AdeleRing (𝓞 L) L))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (N : Ideal (𝓞 L)) (S : Finset (HeightOneSpectrum (𝓞 L))) (Ψ : HeckeEigensystem L ℂ)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : IsIsotypicCuspFormAt L (productionPinsOf L D U gen B) ξ N S Ψ φ) (hφ0 : φ ≠ 0)
    (w : HeightOneSpectrum (𝓞 L)) (hw : w ∉ S) :
    Ψ.b w = HeckeEigensystem.cNorm w *
      ((ξ ⟨Matrix.GeneralLinearGroup.det (gen w), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) := by
  obtain ⟨g, hg⟩ : ∃ g, φ g ≠ 0 := by
    by_contra h; push Not at h; exact hφ0 (funext h)

  have hls : IsLsXiFunction (𝓞 L) L (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) ξ φ := by
    have h1 := hφ.smoothCusp.1.1
    exact ((lsXiMemberAt_iff (𝓞 L) L _ _ ξ _ φ).mp h1).1
  have hz := hls.central_transform ⟨Matrix.GeneralLinearGroup.det (gen w), Subgroup.mem_top _⟩ g

  have hc := hφ.central_eigen w hw g
  rw [productionPinsOf_gen] at hc
  change φ (centralScalar (𝓞 L) L (Matrix.GeneralLinearGroup.det (gen w)) * g) = _ at hz
  rw [hz] at hc
  have hb : ((ξ ⟨Matrix.GeneralLinearGroup.det (gen w), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) =
      Ψ.toRawCentral.b w := mul_right_cancel₀ hg hc
  show Ψ.b w = _
  rw [hb]
  show Ψ.b w = HeckeEigensystem.cNorm w * ((HeckeEigensystem.cNorm w)⁻¹ * Ψ.b w)
  rw [← mul_assoc, mul_inv_cancel₀ (HeckeEigensystem.cNorm_ne_zero w), one_mul]

private theorem exists_sigma (ξ : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξ ⟨z, Subgroup.mem_top z⟩ = 1) :
    ∃ σ : ℝ, ∀ z : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ),
      ‖((ξ z : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm L (z : (AdeleRing (𝓞 L) L)ˣ) ^ σ := by
  let μ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ := ξ.comp (Subgroup.topEquiv : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) ≃* _).symm.toMonoidHom
  have hμ : ∀ z, μ z = ξ ⟨z, Subgroup.mem_top z⟩ := fun _ => rfl
  have hcl : IsIdeleClassChar (𝓞 L) L μ := fun u => by
    rw [hμ]; exact hξt _ ⟨u, rfl⟩
  have hc : Continuous μ := by
    rw [Units.continuous_iff]
    refine ⟨?_, ?_⟩
    · exact hξc
    · have : (fun x => ((μ x)⁻¹ : ℂˣ).val) = (fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) ∘
        fun x => x⁻¹ := by
        funext x
        simp only [Function.comp_apply, hμ]
        rw [← map_inv]
        rfl
      rw [this]
      exact hξc.comp continuous_inv
  obtain ⟨σ, hσ⟩ := NumberField.TateGlobal.exists_norm_apply_eq_ideleNorm_rpow L μ hcl hc
  refine ⟨σ, fun z => ?_⟩
  rw [← hσ z, hμ]

private theorem ideleNorm_det_eq_one_of_mem (N : Ideal (𝓞 L)) (u : AdelicGL2 (𝓞 L) L)
    (hu : u ∈ levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) :
    NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det u) = 1 :=
  NumberField.TateGlobal.ideleNorm_det_eq_one_of_isCompact_of_mem L _
    (AutomorphicForm.isCompact_levelOne_inf_finiteAdelicGL2Subgroup L N) u hu

section Pairing

open NumberField.TateGlobal

variable (K : Type) [Field K] [NumberField K]

private abbrev μH : Measure (AdelicGL2 (𝓞 K) K) := adelicGLHaar (Fin 2) (𝓞 K) K

private def wtR (σ : ℝ) (x : AdelicGL2 (𝓞 K) K) : ℝ := ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ)

private def wt (σ : ℝ) (x : AdelicGL2 (𝓞 K) K) : ℂ := ((ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ)

variable {K}

private def slab (α β : ℝ) : Set (AdelicGL2 (𝓞 K) K) := {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}

private scoped instance instBorelGL : BorelSpace (AdelicGL2 (𝓞 K) K) := borelSpace_glBorel (Fin 2) (𝓞 K) K

private theorem slab_measurableSet (α β : ℝ) : MeasurableSet (slab (K := K) α β) :=
  measurableSet_setOf_ideleNorm_det_mem_Icc K α β

private theorem ae_mem_slab (α β : ℝ) (Φ₀ : Set (AdelicGL2 (𝓞 K) K)) (hΦ₀ : Φ₀ ⊆ slab α β) :
    ∀ᵐ x ∂((μH K).restrict Φ₀), x ∈ slab (K := K) α β :=
  ae_mono (Measure.restrict_mono hΦ₀ le_rfl) (ae_restrict_mem (slab_measurableSet α β))

private theorem wtR_continuous (σ : ℝ) : Continuous (wtR K σ) :=
  (continuous_ideleNorm_det K).rpow_const fun _ => Or.inl (ideleNorm_pos _).ne'

private theorem wt_continuous (σ : ℝ) : Continuous (wt K σ) :=
  Complex.continuous_ofReal.comp (wtR_continuous σ)

private theorem wtR_pos (σ : ℝ) (x : AdelicGL2 (𝓞 K) K) : 0 < wtR K σ x := Real.rpow_pos_of_pos (ideleNorm_pos _) _

private theorem wt_eq (σ : ℝ) (x : AdelicGL2 (𝓞 K) K) : wt K σ x = ((wtR K σ x : ℝ) : ℂ) := rfl

private theorem wtR_bounds (α β σ : ℝ) (hα : 0 < α) (x : AdelicGL2 (𝓞 K) K)
    (hx : ideleNorm K (Matrix.GeneralLinearGroup.det x) ∈ Set.Icc α β) :
    wtR K σ x ≤ max (α ^ (-σ)) (β ^ (-σ)) := by
  obtain ⟨h1, h2⟩ := hx
  unfold wtR
  rcases le_or_gt 0 (-σ) with hs | hs
  · exact (Real.rpow_le_rpow (ideleNorm_pos _).le h2 hs).trans (le_max_right _ _)
  · exact (Real.rpow_le_rpow_of_nonpos hα h1 hs.le).trans (le_max_left _ _)

private theorem wt_ae_bound (α β σ : ℝ) (hα : 0 < α) (Φ₀ : Set (AdelicGL2 (𝓞 K) K)) (hΦ₀ : Φ₀ ⊆ slab α β) :
    ∀ᵐ x ∂((μH K).restrict Φ₀), ‖wt K σ x‖ ≤ max (α ^ (-σ)) (β ^ (-σ)) :=
  (ae_mem_slab α β Φ₀ hΦ₀).mono fun x hx => by
    rw [wt_eq, Complex.norm_real, Real.norm_of_nonneg (wtR_pos σ x).le]
    exact wtR_bounds α β σ hα x hx

private theorem sqrt_wtR_ae_bound (α β σ : ℝ) (hα : 0 < α) (Φ₀ : Set (AdelicGL2 (𝓞 K) K)) (hΦ₀ : Φ₀ ⊆ slab α β) :
    ∀ᵐ x ∂((μH K).restrict Φ₀), Real.sqrt (wtR K σ x) ≤ Real.sqrt (max (α ^ (-σ)) (β ^ (-σ))) :=
  (ae_mem_slab α β Φ₀ hΦ₀).mono fun x hx => Real.sqrt_le_sqrt (wtR_bounds α β σ hα x hx)

private theorem integrable_mul_of_memLp_two {ρ : Measure (AdelicGL2 (𝓞 K) K)} (a b : AdelicGL2 (𝓞 K) K → ℂ)
    (ha : AEStronglyMeasurable a ρ) (hb : AEStronglyMeasurable b ρ) (ha₂ : MemLp a 2 ρ) (hb₂ : MemLp b 2 ρ) :
    Integrable (fun x => a x * b x) ρ := by
  have ha' := (memLp_two_iff_integrable_sq_norm ha).1 ha₂
  have hb' := (memLp_two_iff_integrable_sq_norm hb).1 hb₂
  have hpt : ∀ x, ‖a x * b x‖ ≤ (‖a x‖ ^ 2 + ‖b x‖ ^ 2) / 2 := fun x => by
    rw [norm_mul]
    nlinarith [sq_nonneg (‖a x‖ - ‖b x‖)]
  exact Integrable.mono' ((ha'.add hb').div_const 2) (ha.mul hb) (Filter.Eventually.of_forall fun x => hpt x)

private theorem integrable_pairing (α β σ : ℝ) (hα : 0 < α) (Φ₀ : Set (AdelicGL2 (𝓞 K) K)) (hΦ₀ : Φ₀ ⊆ slab α β)
    (a b : AdelicGL2 (𝓞 K) K → ℂ) (hac : Continuous a) (hbc : Continuous b)
    (ha₂ : MemLp a 2 ((μH K).restrict Φ₀)) (hb₂ : MemLp b 2 ((μH K).restrict Φ₀)) :
    Integrable (fun x => a x * conj (b x) * wt K σ x) ((μH K).restrict Φ₀) := by
  have hb₂' : MemLp (fun x => conj (b x)) 2 ((μH K).restrict Φ₀) := by
    have hm : AEStronglyMeasurable (fun x => conj (b x)) ((μH K).restrict Φ₀) :=
      (Complex.continuous_conj.comp hbc).aestronglyMeasurable
    refine (memLp_two_iff_integrable_sq_norm hm).2 ?_
    simpa only [Complex.norm_conj] using (memLp_two_iff_integrable_sq_norm hbc.aestronglyMeasurable).1 hb₂
  have hab := integrable_mul_of_memLp_two a (fun x => conj (b x)) hac.aestronglyMeasurable
    (Complex.continuous_conj.comp hbc).aestronglyMeasurable ha₂ hb₂'
  have h := hab.bdd_mul (wt_continuous σ).aestronglyMeasurable (wt_ae_bound α β σ hα Φ₀ hΦ₀)
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only
  ring

private theorem pairing_self_eq (σ : ℝ) (Φ₀ : Set (AdelicGL2 (𝓞 K) K)) (a : AdelicGL2 (𝓞 K) K → ℂ) :
    ∫ x in Φ₀, a x * conj (a x) * wt K σ x ∂(μH K) = ((∫ x in Φ₀, ‖a x‖ ^ 2 * wtR K σ x ∂(μH K) : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  congr 1
  funext x
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, wt_eq]
  push_cast
  ring

private theorem sqnorm_integral_nonneg (σ : ℝ) (Φ₀ : Set (AdelicGL2 (𝓞 K) K)) (a : AdelicGL2 (𝓞 K) K → ℂ) :
    0 ≤ ∫ x in Φ₀, ‖a x‖ ^ 2 * wtR K σ x ∂(μH K) :=
  integral_nonneg fun x => mul_nonneg (sq_nonneg _) (wtR_pos σ x).le

private theorem memLp_norm_mul_sqrt (α β σ : ℝ) (hα : 0 < α) (Φ₀ : Set (AdelicGL2 (𝓞 K) K)) (hΦ₀ : Φ₀ ⊆ slab α β)
    (a : AdelicGL2 (𝓞 K) K → ℂ) (hac : Continuous a) (ha₂ : MemLp a 2 ((μH K).restrict Φ₀)) :
    MemLp (fun x => ‖a x‖ * Real.sqrt (wtR K σ x)) 2 ((μH K).restrict Φ₀) := by
  refine MemLp.of_le_mul (c := Real.sqrt (max (α ^ (-σ)) (β ^ (-σ)))) ha₂.norm ?_ ?_
  · exact (hac.norm.mul ((wtR_continuous σ).sqrt)).aestronglyMeasurable
  · refine (sqrt_wtR_ae_bound α β σ hα Φ₀ hΦ₀).mono fun x hx => ?_
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)), Real.norm_of_nonneg (norm_nonneg _),
      mul_comm]
    exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

private theorem norm_pairing_le (α β σ : ℝ) (hα : 0 < α) (Φ₀ : Set (AdelicGL2 (𝓞 K) K)) (hΦ₀ : Φ₀ ⊆ slab α β)
    (a b : AdelicGL2 (𝓞 K) K → ℂ) (hac : Continuous a) (hbc : Continuous b)
    (ha₂ : MemLp a 2 ((μH K).restrict Φ₀)) (hb₂ : MemLp b 2 ((μH K).restrict Φ₀)) :
    ‖∫ x in Φ₀, a x * conj (b x) * wt K σ x ∂(μH K)‖ ≤
      Real.sqrt (∫ x in Φ₀, ‖a x‖ ^ 2 * wtR K σ x ∂(μH K)) * Real.sqrt (∫ x in Φ₀, ‖b x‖ ^ 2 * wtR K σ x ∂(μH K)) := by
  have hF := memLp_norm_mul_sqrt α β σ hα Φ₀ hΦ₀ a hac ha₂
  have hG := memLp_norm_mul_sqrt α β σ hα Φ₀ hΦ₀ b hbc hb₂
  have h22 : Real.HolderConjugate 2 2 := by rw [Real.holderConjugate_iff]; norm_num
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg h22
    (Filter.Eventually.of_forall fun x => mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
    (Filter.Eventually.of_forall fun x => mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
    (by simpa using hF) (by simpa using hG)

  have hsq : ∀ (c : AdelicGL2 (𝓞 K) K → ℂ) (x : AdelicGL2 (𝓞 K) K),
      (‖c x‖ * Real.sqrt (wtR K σ x)) ^ (2 : ℝ) = ‖c x‖ ^ 2 * wtR K σ x := by
    intro c x
    rw [Real.rpow_two, mul_pow, Real.sq_sqrt (wtR_pos σ x).le]
  have hprod : ∀ x : AdelicGL2 (𝓞 K) K, ‖a x‖ * Real.sqrt (wtR K σ x) * (‖b x‖ * Real.sqrt (wtR K σ x)) =
      ‖a x * conj (b x) * wt K σ x‖ := by
    intro x
    rw [norm_mul, norm_mul, Complex.norm_conj, wt_eq, Complex.norm_real, Real.norm_of_nonneg (wtR_pos σ x).le]
    have := Real.mul_self_sqrt (wtR_pos σ x).le
    linear_combination (‖a x‖ * ‖b x‖) * this
  simp only [hsq, hprod] at hH
  refine (norm_integral_le_integral_norm _).trans (hH.trans (le_of_eq ?_))
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  try norm_num

private theorem isLsXi_translate (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (u : AdelicGL2 (𝓞 K) K → ℂ)
    (hu : IsLsXiFunction (𝓞 K) K ⊤ ξ u) (y : AdelicGL2 (𝓞 K) K) :
    IsLsXiFunction (𝓞 K) K ⊤ ξ (fun x => u (x * y)) where
  left_invariant γ x := by simp only [mul_assoc, hu.left_invariant]
  central_transform z x := by simp only [mul_assoc, hu.central_transform]

private theorem memLp_translate_of (α β : ℝ) (hα : 0 < α) (Φ₀ : Set (AdelicGL2 (𝓞 K) K)) (hΦ₀ : Φ₀ ⊆ slab α β)
    (hFD : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀ ((μH K).restrict (slab α β)))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (σ : ℝ)
    (hσ : ∀ z : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ), ‖((ξ z : ℂˣ) : ℂ)‖ = ideleNorm K (z : (AdeleRing (𝓞 K) K)ˣ) ^ σ)
    (u : AdelicGL2 (𝓞 K) K → ℂ) (hu : IsLsXiFunction (𝓞 K) K ⊤ ξ u) (huc : Continuous u)
    (hu₂ : MemLp u 2 ((μH K).restrict Φ₀)) (y : AdelicGL2 (𝓞 K) K) :
    MemLp (fun x => u (x * y)) 2 ((μH K).restrict Φ₀) :=
  (rightTranslate_adjoint_weightedPairing_of_isLsXiFunction K α β hα Φ₀ hΦ₀ hFD ξ σ hσ u u hu hu huc huc
    hu₂ hu₂ y).1

end Pairing

section Algebra

private theorem conj_eq_of_adjoint (a t : ℂ) (N : ℕ) (hN : N ≠ 0) (ht : t ≠ 0)
    (h : a = ((‖t‖ : ℝ) : ℂ) * conj (t⁻¹) * conj a) :
    conj a = conj ((N : ℂ) * t) / ((‖(N : ℂ) * t‖ : ℝ) : ℂ) * a := by
  have hnt : ((‖t‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr ht)
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  have hct : conj t = ((‖t‖ : ℝ) : ℂ) ^ 2 * t⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ ht, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    try ring
  have h1 : conj a = ((‖t‖ : ℝ) : ℂ) * t⁻¹ * a := by
    have := congrArg conj h
    rw [map_mul, map_mul, Complex.conj_conj, Complex.conj_conj, Complex.conj_ofReal] at this
    exact this
  rw [h1, norm_mul, Complex.norm_natCast, map_mul, Complex.conj_natCast, hct]
  push_cast
  field_simp

private theorem sqrt_mul_self_mul (r S : ℝ) (hr : 0 ≤ r) (hS : 0 ≤ S) :
    Real.sqrt (r * S) * Real.sqrt S = Real.sqrt r * S := by
  rw [Real.sqrt_mul hr, mul_assoc, Real.mul_self_sqrt hS]

end Algebra

section Analytic

open NumberField.TateGlobal AutomorphicForm.SmoothCusp

set_option maxHeartbeats 1600000 in

private theorem clauses34 (L : Type) [Field L] [NumberField L]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    (hΦs : ΦL ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range ΦL
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (N : Ideal (𝓞 L)) (hN : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ N → w ∈ SL)
    (Ψ : HeckeEigensystem L ℂ) (φ : AdelicGL2 (𝓞 L) L → ℂ)
    (hφ : IsIsotypicCuspFormAt L (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL Ψ φ) (hφ0 : φ ≠ 0)
    (w : HeightOneSpectrum (𝓞 L)) (hw : w ∉ SL) :
    ‖Ψ.a w‖ ≤ ((Ideal.absNorm w.asIdeal : ℝ) + 1) *
        Real.sqrt ‖((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ : ℂˣ) : ℂ)‖ ∧
      conj (Ψ.a w) = conj (Ψ.b w) / ((‖Ψ.b w‖ : ℝ) : ℂ) * Ψ.a w := by
  classical

  have hmem := (lsXiMemberAt_iff (𝓞 L) L _ _ ξL _ φ).mp hφ.smoothCusp.1.1
  have hls : IsLsXiFunction (𝓞 L) L ⊤ ξL φ := hmem.1
  have hφ2 : MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict ΦL) := hmem.2
  have hφc : Continuous φ := hφ.continuous
  set U : Subgroup (AdelicGL2 (𝓞 L) L) := levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L with hUdef
  have hφU : ∀ g : AdelicGL2 (𝓞 L) L, ∀ u ∈ U, φ (g * u) = φ g := fun g u hu => hφ.level_invariant g u hu
  obtain ⟨reps, hsys, hsum⟩ := hφ.hecke_eigen w hw
  obtain ⟨σ, hσ⟩ := exists_sigma ξL hξc hξt
  have hUσ : ∀ u ∈ U, ideleNorm L (Matrix.GeneralLinearGroup.det u) ^ σ = 1 := fun u hu => by
    rw [ideleNorm_det_eq_one_of_mem N u hu, Real.one_rpow]
  set gv : AdelicGL2 (𝓞 L) L := heckeGen (𝓞 L) L w with hgv
  obtain ⟨z, u₁, u₂, hu₁, hu₂, hinv, hzdet⟩ :=
    NumberField.AdelicLevel.exists_heckeGen_inv_eq_centralScalar_mul_mul_heckeGen_mul_levelOne_and_mul_det_eq_one
      L N SL hN w hw
  have hreps : ∀ i, ∃ u ∈ U, ∃ u' ∈ U, reps i = u * gv * u' := fun i => by
    obtain ⟨u, hu, v, hv, h⟩ := HeckePair.mem_doubleCoset_iff.mp (hsys.mem_doubleCoset i)
    exact ⟨u, hu, v, hv, h.symm⟩
  let c : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) := ⟨z, Subgroup.mem_top z⟩
  let d : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) := ⟨Matrix.GeneralLinearGroup.det gv, Subgroup.mem_top _⟩
  have hc : ∃ u ∈ U, ∃ u' ∈ U, gv⁻¹ = centralScalar (𝓞 L) L (c : (AdeleRing (𝓞 L) L)ˣ) * (u * gv * u') :=
    ⟨u₁, hu₁, u₂, hu₂, by rw [hinv]; simp only [mul_assoc]; rfl⟩

  have hs : ∀ x : AdelicGL2 (𝓞 L) L, (∑ i, φ (x * reps i)) = Ψ.a w * φ x := fun x => hsum x

  set a : ℂ := Ψ.a w with ha
  set t : ℂ := ((ξL d : ℂˣ) : ℂ) with ht
  have ht0 : t ≠ 0 := Units.ne_zero _
  set r : ℝ := ideleNorm L (Matrix.GeneralLinearGroup.det gv) ^ σ with hr
  have hrt : ‖t‖ = r := hσ d
  have hr0 : 0 ≤ r := by rw [← hrt]; exact norm_nonneg _
  have hcd : c * d = 1 := Subtype.ext hzdet
  have hξc_eq : ((ξL c : ℂˣ) : ℂ) = t⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← Units.val_mul, ← map_mul, hcd, map_one, Units.val_one]

  set Pc : ℂ := ∫ x in ΦL, φ x * conj (φ x) * wt L σ x ∂(adelicGLHaar (Fin 2) (𝓞 L) L) with hPc
  have hPc0 : Pc ≠ 0 :=
    AutomorphicForm.setIntegral_mul_conj_mul_ideleNorm_det_rpow_ne_zero_of_isLsXiFunction_of_isFundamentalDomain
      L α β hα hαβ ΦL hΦs hΦ ξL σ φ hls hφc hφ2 hφ0
  set Sφ : ℝ := ∫ x in ΦL, ‖φ x‖ ^ 2 * wtR L σ x ∂(adelicGLHaar (Fin 2) (𝓞 L) L) with hSφ
  have hPS : Pc = ((Sφ : ℝ) : ℂ) := pairing_self_eq σ ΦL φ
  have hS0 : 0 < Sφ := by
    rcases (sqnorm_integral_nonneg σ ΦL φ).lt_or_eq with h | h
    · exact h
    · exfalso
      apply hPc0
      have h' : Sφ = 0 := by rw [hSφ]; exact h.symm
      rw [hPS, h']
      simp

  obtain ⟨-, -, hadj⟩ := AutomorphicForm.cosetSum_adjoint_weightedPairing_of_isLsXiFunction L α β hα ΦL hΦs hΦ ξL σ hσ
    U hUσ φ φ hls hls hφc hφc hφ2 hφ2 hφU hφU gv _ reps hreps c hc
  have e1 : (fun x : AdelicGL2 (𝓞 L) L => (∑ i, φ (x * reps i)) * conj (φ x) *
      ((ideleNorm L (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ)) =
      fun x => a * (φ x * conj (φ x) * wt L σ x) := by
    funext x; rw [hs]; simp only [wt]; ring
  have e2 : (fun x : AdelicGL2 (𝓞 L) L => φ x * conj (∑ i, φ (x * reps i)) *
      ((ideleNorm L (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ)) =
      fun x => conj a * (φ x * conj (φ x) * wt L σ x) := by
    funext x; rw [hs, map_mul]; simp only [wt]; ring
  rw [e1, e2, integral_const_mul, integral_const_mul] at hadj

  rw [← hPc] at hadj
  have hE1 : a = ((r : ℝ) : ℂ) * conj ((ξL c : ℂˣ) : ℂ) * conj a := by
    apply mul_right_cancel₀ hPc0
    rw [hadj, hr]
    ring
  rw [hξc_eq, ← hrt] at hE1
  refine ⟨?_, ?_⟩
  swap
  ·
    have hb : Ψ.b w = HeckeEigensystem.cNorm w * t :=
      b_eq_cNorm_mul_of_isIsotypicCuspFormAt ΦL _ _ _ ξL N SL Ψ φ hφ hφ0 w hw
    rw [hb, HeckeEigensystem.cNorm]
    exact conj_eq_of_adjoint a t _ (Ideal.absNorm_eq_zero_iff.not.mpr w.ne_bot) ht0 hE1
  ·
    have hint : ∀ i, Integrable (fun x => φ (x * reps i) * conj (φ x) * wt L σ x)
        ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict ΦL) := fun i =>
      integrable_pairing α β σ hα ΦL hΦs _ _ (hφc.comp (continuous_mul_const _)) hφc
        (memLp_translate_of α β hα ΦL hΦs hΦ ξL σ hσ φ hls hφc hφ2 (reps i)) hφ2
    have hsum2 : a * Pc = ∑ i, ∫ x in ΦL, φ (x * reps i) * conj (φ x) * wt L σ x ∂(adelicGLHaar (Fin 2) (𝓞 L) L) := by
      rw [← integral_finsetSum _ (fun i _ => hint i), hPc, ← integral_const_mul]
      congr 1; funext x
      rw [← Finset.sum_mul, ← Finset.sum_mul, hs]
      ring

    have hterm : ∀ i, ‖∫ x in ΦL, φ (x * reps i) * conj (φ x) * wt L σ x ∂(adelicGLHaar (Fin 2) (𝓞 L) L)‖ ≤
        Real.sqrt r * Sφ := by
      intro i
      have hRi2 := memLp_translate_of α β hα ΦL hΦs hΦ ξL σ hσ φ hls hφc hφ2 (reps i)
      have hcs := norm_pairing_le α β σ hα ΦL hΦs (fun x => φ (x * reps i)) φ
        (hφc.comp (continuous_mul_const _)) hφc hRi2 hφ2

      obtain ⟨-, -, hcov⟩ := AutomorphicForm.rightTranslate_adjoint_weightedPairing_of_isLsXiFunction L α β hα ΦL hΦs hΦ
        ξL σ hσ φ (fun x => φ (x * reps i)) hls (isLsXi_translate ξL φ hls (reps i)) hφc
        (hφc.comp (continuous_mul_const _)) hφ2 hRi2 (reps i)
      have e3 : (fun x : AdelicGL2 (𝓞 L) L => φ x * conj ((fun x => φ (x * reps i)) (x * (reps i)⁻¹)) *
          ((ideleNorm L (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ)) =
          fun x => φ x * conj (φ x) * wt L σ x := by
        funext x; simp only [inv_mul_cancel_right, wt]
      have hri : ideleNorm L (Matrix.GeneralLinearGroup.det (reps i)) ^ σ = r := by
        obtain ⟨u, hu, u', hu', hi⟩ := hreps i
        rw [hi, map_mul, map_mul, ideleNorm_mul, ideleNorm_mul, Real.mul_rpow (mul_pos (ideleNorm_pos _) (ideleNorm_pos _)).le
          (ideleNorm_pos _).le, Real.mul_rpow (ideleNorm_pos _).le (ideleNorm_pos _).le, hUσ u hu, hUσ u' hu',
          one_mul, mul_one]
      rw [e3, hri] at hcov
      have hself : ∫ x in ΦL, ‖φ (x * reps i)‖ ^ 2 * wtR L σ x ∂(adelicGLHaar (Fin 2) (𝓞 L) L) = r * Sφ := by
        have h1 := pairing_self_eq σ ΦL (fun x => φ (x * reps i))
        have h2 : ∫ x in ΦL, (fun x => φ (x * reps i)) x * conj ((fun x => φ (x * reps i)) x) * wt L σ x
            ∂(adelicGLHaar (Fin 2) (𝓞 L) L) = ((r : ℝ) : ℂ) * Pc := by
          rw [hPc]; exact hcov
        rw [h2, hPS] at h1
        exact_mod_cast h1.symm
      rw [hself, sqrt_mul_self_mul r Sφ hr0 hS0.le] at hcs
      exact hcs
    have hfin : ‖a‖ * Sφ ≤ ((Ideal.absNorm w.asIdeal : ℝ) + 1) * (Real.sqrt r * Sφ) := by
      have h1 : ‖a * Pc‖ ≤ ∑ i : Fin (Ideal.absNorm w.asIdeal + 1), Real.sqrt r * Sφ := by
        rw [hsum2]; exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hterm i)
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, norm_mul, hPS, Complex.norm_real,
        Real.norm_of_nonneg hS0.le] at h1
      exact_mod_cast h1
    rw [hrt]
    have h2 : ‖a‖ * Sφ ≤ ((Ideal.absNorm w.asIdeal : ℝ) + 1) * Real.sqrt r * Sφ := by
      rw [mul_assoc]; exact hfin
    exact le_of_mul_le_mul_right h2 hS0

end Analytic

end AutomorphicForm.SatakeBox
p2m_reactivate "P2MW.S_AutomorphicForm_table_mem_box_of_mem_cuspClasses_slab.AutomorphicForm P2MW.S_AutomorphicForm_table_mem_box_of_mem_cuspClasses_slab.AutomorphicForm.SatakeBox"
p2m_reactivate "P2MW.S_AutomorphicForm_table_mem_box_of_mem_cuspClasses_slab.AutomorphicForm"

end
p2m_reactivate "P2MW.S_AutomorphicForm_table_mem_box_of_mem_cuspClasses_slab.AutomorphicForm P2MW.S_AutomorphicForm_table_mem_box_of_mem_cuspClasses_slab.AutomorphicForm.SatakeBox"

theorem solution
    (L : Type) [Field L] [NumberField L]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    (hΦs : ΦL ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range ΦL
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (N : Ideal (𝓞 L)) (hN : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ N → w ∈ SL)
    (Ψ : HeckeEigensystem L ℂ)
    (hΨ : Ψ ∈ cuspClasses L
      (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL) :
    (fun w : HeightOneSpectrum (𝓞 L) => (Ψ.a w, Ψ.b w)) ∈
      {x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ |
        (∀ w ∈ SL, x w = 0) ∧
        ∀ w ∉ SL,
          (x w).2 = HeckeEigensystem.cNorm w *
              ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ∧
          ‖(x w).1‖ ≤ ((Ideal.absNorm w.asIdeal : ℝ) + 1) *
              Real.sqrt ‖((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ :
                ℂˣ) : ℂ)‖ ∧
          conj (x w).1 = conj (x w).2 / ((‖(x w).2‖ : ℝ) : ℂ) * (x w).1} := by
  classical

  have h3 : Ψ.level = N ∧ (∀ v ∈ SL, Ψ.a v = 0 ∧ Ψ.b v = 0) ∧
      isotypicCuspSubmodule L (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL Ψ ≠ ⊥ := hΨ
  obtain ⟨-, hS, hne⟩ := h3
  obtain ⟨φ, hφ, hφ0⟩ := (isotypicCuspSubmodule_ne_bot_iff L (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL Ψ).mp hne
  refine ⟨fun w hw => ?_, fun w hw => ⟨?_, ?_, ?_⟩⟩
  · obtain ⟨ha, hb⟩ := hS w hw
    exact Prod.ext ha hb
  · exact AutomorphicForm.SatakeBox.b_eq_cNorm_mul_of_isIsotypicCuspFormAt ΦL _ _ _ ξL N SL Ψ φ hφ hφ0 w hw
  ·
    exact (AutomorphicForm.SatakeBox.clauses34 L α β hα hαβ ΦL hΦs hΦ ξL hξc hξt SL N hN Ψ φ hφ hφ0 w hw).1
  · exact (AutomorphicForm.SatakeBox.clauses34 L α β hα hαβ ΦL hΦs hΦ ξL hξc hξt SL N hN Ψ φ hφ hφ0 w hw).2

end S_AutomorphicForm_table_mem_box_of_mem_cuspClasses_slab
end P2MW
export P2MW.S_AutomorphicForm_table_mem_box_of_mem_cuspClasses_slab (solution)
