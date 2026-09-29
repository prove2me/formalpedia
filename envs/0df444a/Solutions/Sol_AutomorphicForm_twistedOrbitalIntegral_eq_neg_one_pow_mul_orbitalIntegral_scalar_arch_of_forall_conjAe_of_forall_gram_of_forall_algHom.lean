-- Prove2me | solution 1 for AutomorphicForm.twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/c7827142-7568-5f6e-96a6-a6151a19800a

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_SplitFibreIntegral
import Theorems.Thm_AutomorphicForm_semilocal_central_transfer_of_forall_oneplace_of_isInvInvariant
import Theorems.Thm_AutomorphicForm_exists_mulEquiv_generalLinearGroup_tensorProduct_infiniteAdeleRing_pi
import Theorems.Thm_AutomorphicForm_exists_ringEquiv_tensorProduct_infiniteAdeleRing_pi_forall_tmul
import Theorems.Thm_Matrix_GeneralLinearGroup_isMulRightInvariant_and_isInvInvariant_of_isHaarMeasure_fin_two
import Theorems.Thm_AutomorphicForm_archIdent_tmul_apply
import Theorems.Thm_MeasureTheory_Measure_exists_ne_zero_map_mulEquiv_eq_smul_pi
import Theorems.Thm_AutomorphicForm_isInvInvariant_of_coupled_of_isInvInvariant
import Theorems.Thm_AutomorphicForm_exists_continuous_isSectionFnOn_and_isOrbitalIntegralOn_iff_completion_of_isRegularSemisimple
import Theorems.Thm_AutomorphicForm_exists_isTwistedSectionFnOn_and_continuous_completion_of_isRegularSemisimple_normString
import Theorems.Thm_AutomorphicForm_exists_isTwistedSectionFnOn_and_continuous_completion_of_isSigmaConjugate_scalar_of_prime
import Definitions.Def_M4aHerbrand_ArchSemilocal
import Mathlib.Topology.Algebra.Group.Units
import Theorems.Thm_AutomorphicForm_semilocal_central_transfer_of_forall_oneplace_of_referenceMeasures
import Theorems.Thm_MeasureTheory_Measure_map_withDensity_gramMeasure_eq_of_linearEquiv_of_bilinForm_eq
import Theorems.Thm_MeasureTheory_Measure_map_withDensity_gram_trace_matrix_pi_eq_pi_of_span_eq
import Theorems.Thm_AutomorphicForm_exists_isNormConjugator_and_coupled_of_gram_of_algHom_real
import Theorems.Thm_AutomorphicForm_exists_isNormConjugator_and_coupled_of_gram_of_algHom_complex
import Theorems.Thm_AutomorphicForm_exists_isNormConjugator_and_coupled_of_gram_conjAe_of_pos
import Theorems.Thm_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar
import Theorems.Thm_AutomorphicForm_map_centralizer_map_ringEquiv_pi_eq_smul_gram_of_infiniteAdeleRing
import Theorems.Thm_AutomorphicForm_map_twistedCentralizer_map_ringEquiv_pi_eq_smul_gram_of_infiniteAdeleRing
import Theorems.Thm_AutomorphicForm_mem_span_map_ringEquiv_pi_iff_of_span_eq_range_includeRight
import Theorems.Thm_AutomorphicForm_mem_span_map_ringEquiv_pi_iff_of_span_eq_setOf_mul_eq_mul_map_sigmaTensor
import Theorems.Thm_AutomorphicForm_exists_gram_map_of_ringEquiv_of_exists_gram
import Theorems.Thm_MeasureTheory_volume_setOf_mvPolynomial_eval_eq_zero
import Theorems.Thm_Algebra_exists_mvPolynomial_forall_eval_eq_norm_det_sum_smul
import Theorems.Thm_AutomorphicForm_exists_ringEquiv_tensor_completion_complex_of_isRamified
import Theorems.Thm_AutomorphicForm_isTwistedOrbitalIntegralOn_map_of_ringEquiv_and_isHaarMeasure_map
import Theorems.Thm_AutomorphicForm_isNormConjugator_map_iff_and_coupled_map_iff_of_ringEquiv
import Theorems.Thm_AutomorphicForm_isOrbitalIntegralOn_map_generalLinearGroup_map_of_ringEquiv
import Theorems.Thm_AutomorphicForm_isHaarMeasure_map_and_exists_isHaarMeasure_centralizer_of_ringEquiv
import Theorems.Thm_AutomorphicForm_pos_and_exists_coupled_toTensorGL_scalar_one_iff_of_coupled_scalar_conjAe
import Theorems.Thm_AutomorphicForm_exists_ringEquiv_tensor_baseChange_of_ringEquiv
import Theorems.Thm_NumberField_InfinitePlace_nonempty_algHom_completion_of_isUnramified
import Theorems.Thm_MeasureTheory_Measure_isInvInvariant_of_isMulRightInvariant
import Theorems.Thm_AutomorphicForm_isOrbitalIntegralOn_scalar_neg_of_isTwistedOrbitalIntegralOn_conjAe_of_gram_of_nhds_forall_isNormConjugator_of_neg
import Theorems.Thm_AutomorphicForm_exists_isSigmaConjugate_scalar_of_isNormConjugator_scalar_of_algHom_of_prime
import Theorems.Thm_AutomorphicForm_exists_isSigmaConjugate_scalar_of_coupled
import Theorems.Thm_AutomorphicForm_exists_isTwistedSectionFnOn_and_continuous_completion_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
import Theorems.Thm_AutomorphicForm_exists_isSigmaConjugate_scalar_conjAe_iff_pos_of_isNormConjugator_scalar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom
p2m_attr_erase "simp" "LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11"

set_option autoImplicit false

set_option autoImplicit false

namespace AutomorphicForm
p2m_export "AutomorphicForm" "isTopologicalRing_tensor t2Space_tensor locallyCompactSpace_tensor isTopologicalGroup_tensorGL t2Space_tensorGL locallyCompactSpace_tensorGL glBorelOf borelSpace_glBorelOf centralizerBorel toTensorGL sigmaTensor sigmaGL normString IsSigmaConjugate IsNormConjugator IsNormOf twistedCentralizer twistedCentralizerBorel IsSectionFnOn IsOrbitalIntegralOn IsTwistedSectionFnOn IsTwistedOrbitalIntegralOn Coupled AreMatchingOn archHaarK archHaarL archIdent archIdentGL AreMatchingArch IsRegularSemisimple archEntries_apply IsArchTestFactor sigmaCentralizer mem_sigmaCentralizer_iff SplitPlace.psi SplitPlace.psiEquiv SplitPlace.psiEquiv_apply SplitPlace.psiEquiv_symm_const SplitPlace.psiGL exists_mulEquiv_generalLinearGroup_tensorProduct_infiniteAdeleRing_pi exists_ringEquiv_tensorProduct_infiniteAdeleRing_pi_forall_tmul archIdent_tmul_apply exists_continuous_isSectionFnOn_and_isOrbitalIntegralOn_iff_completion_of_isRegularSemisimple exists_isTwistedSectionFnOn_and_continuous_completion_of_isRegularSemisimple_normString exists_isTwistedSectionFnOn_and_continuous_completion_of_isSigmaConjugate_scalar_of_prime semilocal_central_transfer_of_forall_oneplace_of_referenceMeasures exists_isNormConjugator_and_coupled_of_gram_of_algHom_real exists_isNormConjugator_and_coupled_of_gram_of_algHom_complex exists_isNormConjugator_and_coupled_of_gram_conjAe_of_pos isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar map_centralizer_map_ringEquiv_pi_eq_smul_gram_of_infiniteAdeleRing map_twistedCentralizer_map_ringEquiv_pi_eq_smul_gram_of_infiniteAdeleRing mem_span_map_ringEquiv_pi_iff_of_span_eq_range_includeRight mem_span_map_ringEquiv_pi_iff_of_span_eq_setOf_mul_eq_mul_map_sigmaTensor exists_gram_map_of_ringEquiv_of_exists_gram exists_ringEquiv_tensor_completion_complex_of_isRamified isTwistedOrbitalIntegralOn_map_of_ringEquiv_and_isHaarMeasure_map isNormConjugator_map_iff_and_coupled_map_iff_of_ringEquiv isOrbitalIntegralOn_map_generalLinearGroup_map_of_ringEquiv isHaarMeasure_map_and_exists_isHaarMeasure_centralizer_of_ringEquiv pos_and_exists_coupled_toTensorGL_scalar_one_iff_of_coupled_scalar_conjAe exists_ringEquiv_tensor_baseChange_of_ringEquiv isOrbitalIntegralOn_scalar_neg_of_isTwistedOrbitalIntegralOn_conjAe_of_gram_of_nhds_forall_isNormConjugator_of_neg exists_isSigmaConjugate_scalar_of_isNormConjugator_scalar_of_algHom_of_prime exists_isTwistedSectionFnOn_and_continuous_completion_of_not_isSigmaConjugate_scalar_of_finrank_eq_two exists_isSigmaConjugate_scalar_conjAe_iff_pos_of_isNormConjugator_scalar"
namespace CentAsmLocal
p2m_open "AutomorphicForm"

open MeasureTheory NumberField NumberField.InfinitePlace
open scoped TensorProduct TensorProduct.RightActions NumberField.LiesOver

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

noncomputable scoped instance instFintypeExtension (v : InfinitePlace K) : Fintype (v.Extension L) := Fintype.ofFinite _

noncomputable def epsK (v : InfinitePlace K) (g : GL (Fin 2) v.Completion) : Fin 2 → Fin 2 → ℂ :=
  fun i j => Completion.extensionEmbedding v ((g : Matrix (Fin 2) (Fin 2) v.Completion) i j)

noncomputable def epsL (v : InfinitePlace K) (g : GL (Fin 2) (L ⊗[K] v.Completion)) :
    Fin 2 → Fin 2 → v.Extension L → ℂ :=
  fun i j w =>
    letI : w.1.1.LiesOver v.1 := M4aHerbrand.ArchSemilocal.liesOver_of_comap_eq w.2
    Completion.extensionEmbedding w.1
      (M4aHerbrand.ArchSemilocal.psiFactor v w.1
        (_root_.Algebra.TensorProduct.comm K L v.Completion ((g : Matrix (Fin 2) (Fin 2) _) i j)))

end AutomorphicForm.CentAsmLocal
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal"
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm"

set_option autoImplicit false

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "isTopologicalRing_tensor t2Space_tensor locallyCompactSpace_tensor isTopologicalGroup_tensorGL t2Space_tensorGL locallyCompactSpace_tensorGL glBorelOf borelSpace_glBorelOf centralizerBorel toTensorGL sigmaTensor sigmaGL normString IsSigmaConjugate IsNormConjugator IsNormOf twistedCentralizer twistedCentralizerBorel IsSectionFnOn IsOrbitalIntegralOn IsTwistedSectionFnOn IsTwistedOrbitalIntegralOn Coupled AreMatchingOn archHaarK archHaarL archIdent archIdentGL AreMatchingArch IsRegularSemisimple archEntries_apply IsArchTestFactor sigmaCentralizer mem_sigmaCentralizer_iff SplitPlace.psi SplitPlace.psiEquiv SplitPlace.psiEquiv_apply SplitPlace.psiEquiv_symm_const SplitPlace.psiGL exists_mulEquiv_generalLinearGroup_tensorProduct_infiniteAdeleRing_pi exists_ringEquiv_tensorProduct_infiniteAdeleRing_pi_forall_tmul archIdent_tmul_apply exists_continuous_isSectionFnOn_and_isOrbitalIntegralOn_iff_completion_of_isRegularSemisimple exists_isTwistedSectionFnOn_and_continuous_completion_of_isRegularSemisimple_normString exists_isTwistedSectionFnOn_and_continuous_completion_of_isSigmaConjugate_scalar_of_prime semilocal_central_transfer_of_forall_oneplace_of_referenceMeasures exists_isNormConjugator_and_coupled_of_gram_of_algHom_real exists_isNormConjugator_and_coupled_of_gram_of_algHom_complex exists_isNormConjugator_and_coupled_of_gram_conjAe_of_pos isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar map_centralizer_map_ringEquiv_pi_eq_smul_gram_of_infiniteAdeleRing map_twistedCentralizer_map_ringEquiv_pi_eq_smul_gram_of_infiniteAdeleRing mem_span_map_ringEquiv_pi_iff_of_span_eq_range_includeRight mem_span_map_ringEquiv_pi_iff_of_span_eq_setOf_mul_eq_mul_map_sigmaTensor exists_gram_map_of_ringEquiv_of_exists_gram exists_ringEquiv_tensor_completion_complex_of_isRamified isTwistedOrbitalIntegralOn_map_of_ringEquiv_and_isHaarMeasure_map isNormConjugator_map_iff_and_coupled_map_iff_of_ringEquiv isOrbitalIntegralOn_map_generalLinearGroup_map_of_ringEquiv isHaarMeasure_map_and_exists_isHaarMeasure_centralizer_of_ringEquiv pos_and_exists_coupled_toTensorGL_scalar_one_iff_of_coupled_scalar_conjAe exists_ringEquiv_tensor_baseChange_of_ringEquiv isOrbitalIntegralOn_scalar_neg_of_isTwistedOrbitalIntegralOn_conjAe_of_gram_of_nhds_forall_isNormConjugator_of_neg exists_isSigmaConjugate_scalar_of_isNormConjugator_scalar_of_algHom_of_prime exists_isTwistedSectionFnOn_and_continuous_completion_of_not_isSigmaConjugate_scalar_of_finrank_eq_two exists_isSigmaConjugate_scalar_conjAe_iff_pos_of_isNormConjugator_scalar"
namespace CentAsmLocal
p2m_open "AutomorphicForm"

open MeasureTheory

section Generic

variable {G H : Type*} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]

theorem map_mem_centralizer (e : G ≃ₜ* H) (γ : G) (t : Subgroup.centralizer ({γ} : Set G)) :
    e (t : G) ∈ Subgroup.centralizer ({e γ} : Set H) := by
  have ht : (t : G) * γ = γ * t := Subgroup.mem_centralizer_singleton_iff.1 t.2
  have h : e ((t : G) * γ) = e (γ * t) := congrArg e ht
  rw [map_mul, map_mul] at h
  exact Subgroup.mem_centralizer_singleton_iff.2 h

theorem symm_map_mem_centralizer (e : G ≃ₜ* H) (γ : G) (t' : Subgroup.centralizer ({e γ} : Set H)) :
    e.symm (t' : H) ∈ Subgroup.centralizer ({γ} : Set G) := by
  have ht : (t' : H) * e γ = e γ * t' := Subgroup.mem_centralizer_singleton_iff.1 t'.2
  have h : e.symm ((t' : H) * e γ) = e.symm (e γ * t') := congrArg e.symm ht
  rw [map_mul, map_mul, e.symm_apply_apply] at h
  exact Subgroup.mem_centralizer_singleton_iff.2 h

def centralizerCongr (e : G ≃ₜ* H) (γ : G) :
    Subgroup.centralizer ({γ} : Set G) ≃ₜ* Subgroup.centralizer ({e γ} : Set H) where
  toFun t := ⟨e t, map_mem_centralizer e γ t⟩
  invFun t' := ⟨e.symm t', symm_map_mem_centralizer e γ t'⟩
  left_inv _ := Subtype.ext (e.symm_apply_apply _)
  right_inv _ := Subtype.ext (e.apply_symm_apply _)
  map_mul' _ _ := Subtype.ext (map_mul e _ _)
  continuous_toFun := (e.continuous.comp continuous_subtype_val).subtype_mk (map_mem_centralizer e γ)
  continuous_invFun :=
    (e.symm.continuous.comp continuous_subtype_val).subtype_mk (symm_map_mem_centralizer e γ)

@[scoped simp] theorem coe_centralizerCongr_apply (e : G ≃ₜ* H) (γ : G)
    (t : Subgroup.centralizer ({γ} : Set G)) : ((centralizerCongr e γ t : _) : H) = e t := rfl

@[scoped simp] theorem coe_centralizerCongr_symm_apply (e : G ≃ₜ* H) (γ : G)
    (t' : Subgroup.centralizer ({e γ} : Set H)) :
    (((centralizerCongr e γ).symm t' : _) : G) = e.symm t' := rfl

theorem map_mem_sigmaCentralizer (e : G ≃ₜ* H) (θ : G →* G) (θ' : H →* H)
    (hθ : ∀ g, e (θ g) = θ' (e g)) (δ : G) (t : sigmaCentralizer θ δ) :
    e (t : G) ∈ sigmaCentralizer θ' (e δ) := by
  have ht : (t : G) * δ * (θ t)⁻¹ = δ := mem_sigmaCentralizer_iff.1 t.2
  have h : e ((t : G) * δ * (θ t)⁻¹) = e δ := congrArg e ht
  rw [map_mul, map_mul, map_inv, hθ] at h
  exact mem_sigmaCentralizer_iff.2 h

theorem symm_map_mem_sigmaCentralizer (e : G ≃ₜ* H) (θ : G →* G) (θ' : H →* H)
    (hθ : ∀ g, e (θ g) = θ' (e g)) (δ : G) (t' : sigmaCentralizer θ' (e δ)) :
    e.symm (t' : H) ∈ sigmaCentralizer θ δ := by
  have hθ' : ∀ h, e.symm (θ' h) = θ (e.symm h) := fun h => by
    apply e.injective
    rw [e.apply_symm_apply, hθ, e.apply_symm_apply]
  have ht : (t' : H) * e δ * (θ' t')⁻¹ = e δ := mem_sigmaCentralizer_iff.1 t'.2
  have h : e.symm ((t' : H) * e δ * (θ' t')⁻¹) = e.symm (e δ) := congrArg e.symm ht
  rw [map_mul, map_mul, map_inv, hθ', e.symm_apply_apply] at h
  exact mem_sigmaCentralizer_iff.2 h

def sigmaCentralizerCongr (e : G ≃ₜ* H) (θ : G →* G) (θ' : H →* H)
    (hθ : ∀ g, e (θ g) = θ' (e g)) (δ : G) :
    sigmaCentralizer θ δ ≃ₜ* sigmaCentralizer θ' (e δ) where
  toFun t := ⟨e t, map_mem_sigmaCentralizer e θ θ' hθ δ t⟩
  invFun t' := ⟨e.symm t', symm_map_mem_sigmaCentralizer e θ θ' hθ δ t'⟩
  left_inv _ := Subtype.ext (e.symm_apply_apply _)
  right_inv _ := Subtype.ext (e.apply_symm_apply _)
  map_mul' _ _ := Subtype.ext (map_mul e _ _)
  continuous_toFun :=
    (e.continuous.comp continuous_subtype_val).subtype_mk (map_mem_sigmaCentralizer e θ θ' hθ δ)
  continuous_invFun :=
    (e.symm.continuous.comp continuous_subtype_val).subtype_mk (symm_map_mem_sigmaCentralizer e θ θ' hθ δ)

@[scoped simp] theorem coe_sigmaCentralizerCongr_apply (e : G ≃ₜ* H) (θ : G →* G) (θ' : H →* H)
    (hθ : ∀ g, e (θ g) = θ' (e g)) (δ : G) (t : sigmaCentralizer θ δ) :
    ((sigmaCentralizerCongr e θ θ' hθ δ t : _) : H) = e t := rfl

@[scoped simp] theorem coe_sigmaCentralizerCongr_symm_apply (e : G ≃ₜ* H) (θ : G →* G) (θ' : H →* H)
    (hθ : ∀ g, e (θ g) = θ' (e g)) (δ : G) (t' : sigmaCentralizer θ' (e δ)) :
    (((sigmaCentralizerCongr e θ θ' hθ δ).symm t' : _) : G) = e.symm t' := rfl

variable [IsTopologicalGroup G] [IsTopologicalGroup H]
  [MeasurableSpace G] [BorelSpace G] [MeasurableSpace H] [BorelSpace H]

theorem exists_isHaarMeasure_centralizer_forward (e : G ≃ₜ* H) (γ : G)
    [MeasurableSpace (Subgroup.centralizer ({γ} : Set G))]
    [BorelSpace (Subgroup.centralizer ({γ} : Set G))]
    [MeasurableSpace (Subgroup.centralizer ({e γ} : Set H))]
    [BorelSpace (Subgroup.centralizer ({e γ} : Set H))]
    (τ : Measure (Subgroup.centralizer ({γ} : Set G))) [τ.IsHaarMeasure] :
    ∃ τ' : Measure (Subgroup.centralizer ({e γ} : Set H)), τ'.IsHaarMeasure ∧
      Measure.map (fun t' : Subgroup.centralizer ({e γ} : Set H) => (t' : H)) τ' =
        Measure.map (fun t : Subgroup.centralizer ({γ} : Set G) => e (t : G)) τ ∧
      (τ.IsInvInvariant → τ'.IsInvInvariant) := by
  have hmc : Measurable ((centralizerCongr e γ) : Subgroup.centralizer ({γ} : Set G) → Subgroup.centralizer ({e γ} : Set H)) :=
    (centralizerCongr e γ).continuous.measurable
  refine ⟨Measure.map (centralizerCongr e γ) τ, (centralizerCongr e γ).isHaarMeasure_map τ, ?_, ?_⟩
  · rw [Measure.map_map continuous_subtype_val.measurable hmc]
    rfl
  · intro hinv
    constructor
    show Measure.map Inv.inv (Measure.map (centralizerCongr e γ) τ) = Measure.map (centralizerCongr e γ) τ
    rw [Measure.map_map measurable_inv hmc,
      show (Inv.inv ∘ (centralizerCongr e γ)) = ((centralizerCongr e γ) ∘ Inv.inv) from
        funext fun t => (map_inv (centralizerCongr e γ) t).symm,
      ← Measure.map_map hmc measurable_inv, Measure.map_inv_eq_self]

theorem exists_isHaarMeasure_centralizer_backward (e : G ≃ₜ* H) (γ : G)
    [MeasurableSpace (Subgroup.centralizer ({γ} : Set G))]
    [BorelSpace (Subgroup.centralizer ({γ} : Set G))]
    [MeasurableSpace (Subgroup.centralizer ({e γ} : Set H))]
    [BorelSpace (Subgroup.centralizer ({e γ} : Set H))]
    (τ' : Measure (Subgroup.centralizer ({e γ} : Set H))) [τ'.IsHaarMeasure] :
    ∃ τ : Measure (Subgroup.centralizer ({γ} : Set G)), τ.IsHaarMeasure ∧
      Measure.map (fun t' : Subgroup.centralizer ({e γ} : Set H) => (t' : H)) τ' =
        Measure.map (fun t : Subgroup.centralizer ({γ} : Set G) => e (t : G)) τ ∧
      (τ'.IsInvInvariant → τ.IsInvInvariant) := by
  have hmc : Measurable ((centralizerCongr e γ).symm : Subgroup.centralizer ({e γ} : Set H) → Subgroup.centralizer ({γ} : Set G)) :=
    (centralizerCongr e γ).symm.continuous.measurable
  refine ⟨Measure.map (centralizerCongr e γ).symm τ', (centralizerCongr e γ).symm.isHaarMeasure_map τ', ?_, ?_⟩
  · have hm1 : Measurable (fun t : Subgroup.centralizer ({γ} : Set G) => e (t : G)) :=
      (e.continuous.comp continuous_subtype_val).measurable
    rw [Measure.map_map hm1 hmc]
    congr 1
    funext t'
    simp
  · intro hinv
    constructor
    show Measure.map Inv.inv (Measure.map (centralizerCongr e γ).symm τ') =
      Measure.map (centralizerCongr e γ).symm τ'
    rw [Measure.map_map measurable_inv hmc,
      show (Inv.inv ∘ (centralizerCongr e γ).symm) = ((centralizerCongr e γ).symm ∘ Inv.inv) from
        funext fun t => (map_inv (centralizerCongr e γ).symm t).symm,
      ← Measure.map_map hmc measurable_inv, Measure.map_inv_eq_self]

theorem exists_isHaarMeasure_sigmaCentralizer_forward (e : G ≃ₜ* H) (θ : G →* G) (θ' : H →* H)
    (hθ : ∀ g, e (θ g) = θ' (e g)) (δ : G)
    [MeasurableSpace (sigmaCentralizer θ δ)] [BorelSpace (sigmaCentralizer θ δ)]
    [MeasurableSpace (sigmaCentralizer θ' (e δ))] [BorelSpace (sigmaCentralizer θ' (e δ))]
    (τ : Measure (sigmaCentralizer θ δ)) [τ.IsHaarMeasure] :
    ∃ τ' : Measure (sigmaCentralizer θ' (e δ)), τ'.IsHaarMeasure ∧
      Measure.map (fun t' : sigmaCentralizer θ' (e δ) => (t' : H)) τ' =
        Measure.map (fun t : sigmaCentralizer θ δ => e (t : G)) τ ∧
      (τ.IsInvInvariant → τ'.IsInvInvariant) := by
  have hmc : Measurable ((sigmaCentralizerCongr e θ θ' hθ δ) : sigmaCentralizer θ δ → sigmaCentralizer θ' (e δ)) :=
    (sigmaCentralizerCongr e θ θ' hθ δ).continuous.measurable
  refine ⟨Measure.map (sigmaCentralizerCongr e θ θ' hθ δ) τ,
    (sigmaCentralizerCongr e θ θ' hθ δ).isHaarMeasure_map τ, ?_, ?_⟩
  · rw [Measure.map_map continuous_subtype_val.measurable hmc]
    rfl
  · intro hinv
    constructor
    show Measure.map Inv.inv (Measure.map (sigmaCentralizerCongr e θ θ' hθ δ) τ) =
      Measure.map (sigmaCentralizerCongr e θ θ' hθ δ) τ
    rw [Measure.map_map measurable_inv hmc,
      show (Inv.inv ∘ (sigmaCentralizerCongr e θ θ' hθ δ)) = ((sigmaCentralizerCongr e θ θ' hθ δ) ∘ Inv.inv) from
        funext fun t => (map_inv (sigmaCentralizerCongr e θ θ' hθ δ) t).symm,
      ← Measure.map_map hmc measurable_inv, Measure.map_inv_eq_self]

theorem exists_isHaarMeasure_sigmaCentralizer_backward (e : G ≃ₜ* H) (θ : G →* G) (θ' : H →* H)
    (hθ : ∀ g, e (θ g) = θ' (e g)) (δ : G)
    [MeasurableSpace (sigmaCentralizer θ δ)] [BorelSpace (sigmaCentralizer θ δ)]
    [MeasurableSpace (sigmaCentralizer θ' (e δ))] [BorelSpace (sigmaCentralizer θ' (e δ))]
    (τ' : Measure (sigmaCentralizer θ' (e δ))) [τ'.IsHaarMeasure] :
    ∃ τ : Measure (sigmaCentralizer θ δ), τ.IsHaarMeasure ∧
      Measure.map (fun t' : sigmaCentralizer θ' (e δ) => (t' : H)) τ' =
        Measure.map (fun t : sigmaCentralizer θ δ => e (t : G)) τ ∧
      (τ'.IsInvInvariant → τ.IsInvInvariant) := by
  have hmc : Measurable ((sigmaCentralizerCongr e θ θ' hθ δ).symm : sigmaCentralizer θ' (e δ) → sigmaCentralizer θ δ) :=
    (sigmaCentralizerCongr e θ θ' hθ δ).symm.continuous.measurable
  refine ⟨Measure.map (sigmaCentralizerCongr e θ θ' hθ δ).symm τ',
    (sigmaCentralizerCongr e θ θ' hθ δ).symm.isHaarMeasure_map τ', ?_, ?_⟩
  · have hm1 : Measurable (fun t : sigmaCentralizer θ δ => e (t : G)) :=
      (e.continuous.comp continuous_subtype_val).measurable
    rw [Measure.map_map hm1 hmc]
    congr 1
    funext t'
    simp
  · intro hinv
    constructor
    show Measure.map Inv.inv (Measure.map (sigmaCentralizerCongr e θ θ' hθ δ).symm τ') =
      Measure.map (sigmaCentralizerCongr e θ θ' hθ δ).symm τ'
    rw [Measure.map_map measurable_inv hmc,
      show (Inv.inv ∘ (sigmaCentralizerCongr e θ θ' hθ δ).symm) =
          ((sigmaCentralizerCongr e θ θ' hθ δ).symm ∘ Inv.inv) from
        funext fun t => (map_inv (sigmaCentralizerCongr e θ θ' hθ δ).symm t).symm,
      ← Measure.map_map hmc measurable_inv, Measure.map_inv_eq_self]

end Generic
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal"

section GLTwo

variable {R S : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]

def matEquiv (e : R ≃+* S) (he : Continuous e) (he' : Continuous e.symm) :
    Matrix (Fin 2) (Fin 2) R ≃ₜ* Matrix (Fin 2) (Fin 2) S :=
  { e.mapMatrix.toMulEquiv with
    continuous_toFun :=
      (continuous_id.matrix_map he : Continuous fun m : Matrix (Fin 2) (Fin 2) R => m.map e)
    continuous_invFun :=
      (continuous_id.matrix_map he' : Continuous fun m : Matrix (Fin 2) (Fin 2) S => m.map e.symm) }

def glEquiv (e : R ≃+* S) (he : Continuous e) (he' : Continuous e.symm) : GL (Fin 2) R ≃ₜ* GL (Fin 2) S :=
  Units.mapContinuousMulEquiv (matEquiv e he he')

omit [IsTopologicalRing R] [IsTopologicalRing S] in
theorem glEquiv_apply (e : R ≃+* S) (he : Continuous e) (he' : Continuous e.symm) (g : GL (Fin 2) R) :
    glEquiv e he he' g = Matrix.GeneralLinearGroup.map e.toRingHom g := by
  ext i j
  rfl

omit [IsTopologicalRing R] [IsTopologicalRing S] in
theorem coe_glEquiv (e : R ≃+* S) (he : Continuous e) (he' : Continuous e.symm) :
    (⇑(glEquiv e he he') : GL (Fin 2) R → GL (Fin 2) S) = Matrix.GeneralLinearGroup.map e.toRingHom :=
  funext (glEquiv_apply e he he')

omit [TopologicalSpace R] [IsTopologicalRing R] [TopologicalSpace S] [IsTopologicalRing S] in
theorem map_symm_map (e : R ≃+* S) (g : GL (Fin 2) R) :
    Matrix.GeneralLinearGroup.map e.symm.toRingHom (Matrix.GeneralLinearGroup.map e.toRingHom g) = g := by
  ext i j
  simp

omit [TopologicalSpace R] [IsTopologicalRing R] [TopologicalSpace S] [IsTopologicalRing S] in
theorem map_map_symm (e : R ≃+* S) (g' : GL (Fin 2) S) :
    Matrix.GeneralLinearGroup.map e.toRingHom (Matrix.GeneralLinearGroup.map e.symm.toRingHom g') = g' := by
  ext i j
  simp

omit [IsTopologicalRing R] [IsTopologicalRing S] in
theorem glEquiv_symm_apply (e : R ≃+* S) (he : Continuous e) (he' : Continuous e.symm) (g' : GL (Fin 2) S) :
    (glEquiv e he he').symm g' = Matrix.GeneralLinearGroup.map e.symm.toRingHom g' := by
  apply (glEquiv e he he').injective
  rw [ContinuousMulEquiv.apply_symm_apply, glEquiv_apply, map_map_symm]

omit [TopologicalSpace R] [IsTopologicalRing R] [TopologicalSpace S] [IsTopologicalRing S] in

theorem map_scalar (e : R ≃+* S) (c : Rˣ) :
    Matrix.GeneralLinearGroup.map e.toRingHom (Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (e : R →* S) c) := by
  ext i j
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.GeneralLinearGroup.map_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

omit [TopologicalSpace R] [IsTopologicalRing R] [TopologicalSpace S] [IsTopologicalRing S] in

theorem isRegularSemisimple_map (e : R ≃+* S) (g : GL (Fin 2) R) (hg : IsRegularSemisimple g) :
    IsRegularSemisimple (Matrix.GeneralLinearGroup.map e.toRingHom g) := by
  unfold IsRegularSemisimple at hg ⊢
  have h : Matrix.trace ((Matrix.GeneralLinearGroup.map e.toRingHom g : GL (Fin 2) S) : Matrix (Fin 2) (Fin 2) S) ^ 2 -
      4 * Matrix.det ((Matrix.GeneralLinearGroup.map e.toRingHom g : GL (Fin 2) S) : Matrix (Fin 2) (Fin 2) S) =
      e (Matrix.trace (g : Matrix (Fin 2) (Fin 2) R) ^ 2 - 4 * Matrix.det (g : Matrix (Fin 2) (Fin 2) R)) := by
    simp [Matrix.trace_fin_two, Matrix.det_fin_two, map_sub, map_mul, map_pow, map_add, map_ofNat]
  rw [h]
  exact hg.map e

end GLTwo
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal"

end AutomorphicForm.CentAsmLocal
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal"
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal"

end
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal"

set_option autoImplicit false

namespace AutomorphicForm
p2m_export "AutomorphicForm" "isTopologicalRing_tensor t2Space_tensor locallyCompactSpace_tensor isTopologicalGroup_tensorGL t2Space_tensorGL locallyCompactSpace_tensorGL glBorelOf borelSpace_glBorelOf centralizerBorel toTensorGL sigmaTensor sigmaGL normString IsSigmaConjugate IsNormConjugator IsNormOf twistedCentralizer twistedCentralizerBorel IsSectionFnOn IsOrbitalIntegralOn IsTwistedSectionFnOn IsTwistedOrbitalIntegralOn Coupled AreMatchingOn archHaarK archHaarL archIdent archIdentGL AreMatchingArch IsRegularSemisimple archEntries_apply IsArchTestFactor sigmaCentralizer mem_sigmaCentralizer_iff SplitPlace.psi SplitPlace.psiEquiv SplitPlace.psiEquiv_apply SplitPlace.psiEquiv_symm_const SplitPlace.psiGL exists_mulEquiv_generalLinearGroup_tensorProduct_infiniteAdeleRing_pi exists_ringEquiv_tensorProduct_infiniteAdeleRing_pi_forall_tmul archIdent_tmul_apply exists_continuous_isSectionFnOn_and_isOrbitalIntegralOn_iff_completion_of_isRegularSemisimple exists_isTwistedSectionFnOn_and_continuous_completion_of_isRegularSemisimple_normString exists_isTwistedSectionFnOn_and_continuous_completion_of_isSigmaConjugate_scalar_of_prime semilocal_central_transfer_of_forall_oneplace_of_referenceMeasures exists_isNormConjugator_and_coupled_of_gram_of_algHom_real exists_isNormConjugator_and_coupled_of_gram_of_algHom_complex exists_isNormConjugator_and_coupled_of_gram_conjAe_of_pos isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar map_centralizer_map_ringEquiv_pi_eq_smul_gram_of_infiniteAdeleRing map_twistedCentralizer_map_ringEquiv_pi_eq_smul_gram_of_infiniteAdeleRing mem_span_map_ringEquiv_pi_iff_of_span_eq_range_includeRight mem_span_map_ringEquiv_pi_iff_of_span_eq_setOf_mul_eq_mul_map_sigmaTensor exists_gram_map_of_ringEquiv_of_exists_gram exists_ringEquiv_tensor_completion_complex_of_isRamified isTwistedOrbitalIntegralOn_map_of_ringEquiv_and_isHaarMeasure_map isNormConjugator_map_iff_and_coupled_map_iff_of_ringEquiv isOrbitalIntegralOn_map_generalLinearGroup_map_of_ringEquiv isHaarMeasure_map_and_exists_isHaarMeasure_centralizer_of_ringEquiv pos_and_exists_coupled_toTensorGL_scalar_one_iff_of_coupled_scalar_conjAe exists_ringEquiv_tensor_baseChange_of_ringEquiv isOrbitalIntegralOn_scalar_neg_of_isTwistedOrbitalIntegralOn_conjAe_of_gram_of_nhds_forall_isNormConjugator_of_neg exists_isSigmaConjugate_scalar_of_isNormConjugator_scalar_of_algHom_of_prime exists_isTwistedSectionFnOn_and_continuous_completion_of_not_isSigmaConjugate_scalar_of_finrank_eq_two exists_isSigmaConjugate_scalar_conjAe_iff_pos_of_isNormConjugator_scalar"
namespace CentAsmLocal
p2m_open "AutomorphicForm"

open MeasureTheory NumberField
open scoped TensorProduct TensorProduct.RightActions

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

attribute [local instance 10000] AutomorphicForm.glBorelOf

private theorem _root_.AutomorphicForm.CentAsmLocal.borelSpace_gl (R : Type) [CommRing R] [TopologicalSpace R] : BorelSpace (GL (Fin 2) R) := ⟨rfl⟩

p2m_export "AutomorphicForm.CentAsmLocal" "borelSpace_gl"
attribute [local instance] borelSpace_gl

theorem hsecK (v : InfinitePlace K) (γ : GL (Fin 2) v.Completion) (hγ : IsRegularSemisimple γ)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) v.Completion))) (centralizerBorel v.Completion γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel v.Completion γ) τ)
    (f : GL (Fin 2) v.Completion → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    ∃ w : GL (Fin 2) v.Completion → ℝ, IsSectionFnOn v.Completion γ τ f w ∧ Continuous w := by
  haveI : LocallyCompactSpace (GL (Fin 2) v.Completion) := by
    haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) v.Completion) :=
      inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → v.Completion))
    exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  obtain ⟨C, hC⟩ := (hf.norm.bddAbove_range_of_hasCompactSupport hfc.norm)
  exact (AutomorphicForm.exists_continuous_isSectionFnOn_and_isOrbitalIntegralOn_iff_completion_of_isRegularSemisimple
    K v Measure.haar inferInstance γ hγ τ hτ f hf.measurable hfc ⟨C, fun g => hC ⟨g, rfl⟩⟩).1

theorem hsecL [IsGalois K L] (hprime : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : InfinitePlace K) (δ : GL (Fin 2) (L ⊗[K] v.Completion))
    (hδ : IsRegularSemisimple (normString K L v.Completion σ δ) ∨
      ∃ d : (L ⊗[K] v.Completion)ˣ,
        IsSigmaConjugate K L v.Completion σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) d))
    (τ' : @Measure (twistedCentralizer K L v.Completion σ δ) (twistedCentralizerBorel K L v.Completion σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L v.Completion σ δ) τ')
    (hτ'i : @Measure.IsInvInvariant _ (twistedCentralizerBorel K L v.Completion σ δ) _ τ')
    (φ : GL (Fin 2) (L ⊗[K] v.Completion) → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    ∃ W : GL (Fin 2) (L ⊗[K] v.Completion) → ℝ,
      IsTwistedSectionFnOn K L v.Completion σ δ τ' φ W ∧ Continuous W := by
  rcases hδ with hreg | hcent
  · exact AutomorphicForm.exists_isTwistedSectionFnOn_and_continuous_completion_of_isRegularSemisimple_normString
      K L σ hgen v δ hreg τ' hτ' φ hφc
  · exact AutomorphicForm.exists_isTwistedSectionFnOn_and_continuous_completion_of_isSigmaConjugate_scalar_of_prime
      K L hprime σ hgen v δ hcent τ' hτ' hτ'i φ hφc

end AutomorphicForm.CentAsmLocal
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal"
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal"

set_option autoImplicit false

p2m_open "MeasureTheory NumberField AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm"
open scoped TensorProduct
open scoped TensorProduct.RightActions

namespace FDTEF

p2m_open "NumberField AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm"
open scoped TensorProduct TensorProduct.RightActions

variable (K : Type) [Field K] [NumberField K]

noncomputable def XiK : InfiniteAdeleRing K ≃+* ((v : InfinitePlace K) → v.Completion) := RingEquiv.refl _

theorem XiK_apply (a : InfiniteAdeleRing K) (v : InfinitePlace K) : XiK K a v = a v := rfl

theorem continuous_XiK : Continuous (XiK K) := continuous_id
theorem continuous_XiK_symm : Continuous (XiK K).symm := continuous_id

noncomputable def thetaK :
    GL (Fin 2) (InfiniteAdeleRing K) ≃* ((v : InfinitePlace K) → GL (Fin 2) v.Completion) :=
  ((Units.mapEquiv (RingEquiv.mapMatrix (m := Fin 2) (XiK K)).toMulEquiv).trans
    (Units.mapEquiv (Matrix.piRingEquiv :
      Matrix (Fin 2) (Fin 2) ((v : InfinitePlace K) → v.Completion) ≃+*
        ((v : InfinitePlace K) → Matrix (Fin 2) (Fin 2) v.Completion)).toMulEquiv)).trans MulEquiv.piUnits

theorem thetaK_val (g : GL (Fin 2) (InfiniteAdeleRing K)) (v : InfinitePlace K) (i j : Fin 2) :
    ((thetaK K g v : GL (Fin 2) v.Completion) : Matrix (Fin 2) (Fin 2) v.Completion) i j =
      (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j v := rfl

theorem thetaK_apply (g : GL (Fin 2) (InfiniteAdeleRing K)) (v : InfinitePlace K) :
    thetaK K g v = Matrix.GeneralLinearGroup.map (Pi.evalRingHom (fun v : InfinitePlace K => v.Completion) v) g :=
  Units.ext (Matrix.ext fun i j => by rw [thetaK_val]; rfl)

theorem thetaK_symm_apply (F : (v : InfinitePlace K) → GL (Fin 2) v.Completion) :
    (thetaK K).symm F = (Units.mapEquiv (RingEquiv.mapMatrix (m := Fin 2) (XiK K)).toMulEquiv).symm
      ((Units.mapEquiv (Matrix.piRingEquiv :
        Matrix (Fin 2) (Fin 2) ((v : InfinitePlace K) → v.Completion) ≃+*
          ((v : InfinitePlace K) → Matrix (Fin 2) (Fin 2) v.Completion)).toMulEquiv).symm (MulEquiv.piUnits.symm F)) :=
  rfl

theorem continuous_thetaK : Continuous (thetaK K) := by
  refine continuous_pi fun v => ?_
  have hfun : (fun g => thetaK K g v) =
      Matrix.GeneralLinearGroup.map (Pi.evalRingHom (fun v : InfinitePlace K => v.Completion) v) :=
    funext fun g => thetaK_apply K g v
  rw [hfun]
  exact Continuous.units_map _ (continuous_id.matrix_map (continuous_apply v))

theorem continuous_thetaK_symm : Continuous (thetaK K).symm := by
  have h1 : Continuous (MulEquiv.piUnits (M := fun v : InfinitePlace K => Matrix (Fin 2) (Fin 2) v.Completion)).symm := by
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · exact continuous_pi fun v => Units.continuous_val.comp (continuous_apply v)
    · exact continuous_pi fun v => Units.continuous_coe_inv.comp (continuous_apply v)
  have h2 : Continuous (Units.mapEquiv (Matrix.piRingEquiv :
        Matrix (Fin 2) (Fin 2) ((v : InfinitePlace K) → v.Completion) ≃+*
          ((v : InfinitePlace K) → Matrix (Fin 2) (Fin 2) v.Completion)).toMulEquiv).symm := by
    refine Continuous.units_map _ ?_
    refine continuous_matrix fun i j => continuous_pi fun v => ?_
    exact ((continuous_apply j).comp ((continuous_apply i).comp (continuous_apply v)))
  have h3 : Continuous (Units.mapEquiv (RingEquiv.mapMatrix (m := Fin 2) (XiK K)).toMulEquiv).symm :=
    Continuous.units_map _ (continuous_id.matrix_map (continuous_XiK_symm K))
  have hfun := funext (thetaK_symm_apply K)
  rw [show ⇑(thetaK K).symm = _ from hfun]
  exact h3.comp (h2.comp h1)

variable (L : Type) [Field L] [NumberField L] [Algebra K L]

theorem exists_thetaL :
    ∃ (Ξ : L ⊗[K] InfiniteAdeleRing K ≃+* ((v : InfinitePlace K) → L ⊗[K] v.Completion))
      (Θ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) ≃* ((v : InfinitePlace K) → GL (Fin 2) (L ⊗[K] v.Completion))),
      Continuous Ξ ∧ Continuous Ξ.symm ∧ (∀ (x : L) (a : InfiniteAdeleRing K) (v : InfinitePlace K), Ξ (x ⊗ₜ a) v = x ⊗ₜ (a v)) ∧
      Continuous Θ ∧ Continuous Θ.symm ∧
      (∀ (g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (v : InfinitePlace K),
        Θ g v = Matrix.GeneralLinearGroup.map
          ((Pi.evalRingHom (fun v : InfinitePlace K => L ⊗[K] v.Completion) v).comp Ξ.toRingHom) g) ∧
      (∀ (σ : L ≃ₐ[K] L) (g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (v : InfinitePlace K),
        Θ (sigmaGL K L (InfiniteAdeleRing K) σ g) v = sigmaGL K L v.Completion σ (Θ g v)) ∧
      (∀ (g : GL (Fin 2) (InfiniteAdeleRing K)) (v : InfinitePlace K),
        Θ (toTensorGL K L (InfiniteAdeleRing K) g) v = toTensorGL K L v.Completion (thetaK K g v)) := by
  obtain ⟨Ξ, hΞ, hΞ', hΞt⟩ := AutomorphicForm.exists_ringEquiv_tensorProduct_infiniteAdeleRing_pi_forall_tmul K L
  obtain ⟨Θ, hΘ, hΘ', hΘapp, hΘσ, hΘι⟩ :=
    AutomorphicForm.exists_mulEquiv_generalLinearGroup_tensorProduct_infiniteAdeleRing_pi K L Ξ hΞ hΞ' hΞt
  refine ⟨Ξ, Θ, hΞ, hΞ', hΞt, hΘ, hΘ', hΘapp, hΘσ, fun g v => ?_⟩
  rw [hΘι, thetaK_apply]

section Instances

variable (v : InfinitePlace K)

theorem secondCountableTopology_completion : SecondCountableTopology v.Completion := by
  letI : NontriviallyNormedField v.Completion := M4aHerbrand.ArchSemilocal.nontriviallyNormedCompletion v
  haveI : ProperSpace v.Completion := ProperSpace.of_locallyCompactSpace v.Completion
  infer_instance

attribute [local instance 10000] AutomorphicForm.glBorelOf

theorem borelSpace_gl (R : Type) [CommRing R] [TopologicalSpace R] : BorelSpace (GL (Fin 2) R) := ⟨rfl⟩

attribute [local instance] borelSpace_gl

theorem locallyCompactSpace_gl (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [T2Space R] [LocallyCompactSpace R] : LocallyCompactSpace (GL (Fin 2) R) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) R) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → R))
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) R) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → R))
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

theorem secondCountableTopology_gl (R : Type) [CommRing R] [TopologicalSpace R]
    [SecondCountableTopology R] : SecondCountableTopology (GL (Fin 2) R) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) R) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → R))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) R)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem t2Space_gl (R : Type) [CommRing R] [TopologicalSpace R] [T2Space R] : T2Space (GL (Fin 2) R) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) R) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → R))
  exact Units.isEmbedding_embedProduct.t2Space

attribute [local instance] secondCountableTopology_completion locallyCompactSpace_gl
  secondCountableTopology_gl t2Space_gl

theorem isMulRightInvariant_haar_completion :
    (Measure.haar : Measure (GL (Fin 2) v.Completion)).IsMulRightInvariant := by
  exact (Matrix.GeneralLinearGroup.isMulRightInvariant_and_isInvInvariant_of_isHaarMeasure_fin_two
    (Measure.haar : Measure (GL (Fin 2) v.Completion))).1

end Instances
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal"

end FDTEF
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal"

namespace FDTEF

section GenericTransport

variable {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] [MeasurableSpace G'] [BorelSpace G']

omit [IsTopologicalGroup G] [IsTopologicalGroup G'] in
theorem measurable_cme (e : G ≃ₜ* G') : Measurable (e : G → G') := e.continuous.measurable

omit [IsTopologicalGroup G] [IsTopologicalGroup G'] in

theorem corr_symm (e : G ≃ₜ* G') {T T' : Type} [MeasurableSpace T] [MeasurableSpace T']
    (ι : T → G) (ι' : T' → G') (hι : Measurable ι) (hι' : Measurable ι')
    (τ : Measure T) (τ₀ : Measure T')
    (h : Measure.map ι' τ₀ = Measure.map (fun t => e (ι t)) τ) :
    Measure.map ι τ = Measure.map (fun t' => e.symm (ι' t')) τ₀ := by
  have hme : Measurable (e.symm : G' → G) := measurable_cme e.symm
  have h1 : Measure.map (fun t' => e.symm (ι' t')) τ₀ = Measure.map (e.symm : G' → G) (Measure.map ι' τ₀) :=
    (Measure.map_map hme hι').symm
  have h2 : Measure.map (e.symm : G' → G) (Measure.map (fun t => e (ι t)) τ) =
      Measure.map ((e.symm : G' → G) ∘ fun t => e (ι t)) τ :=
    Measure.map_map hme ((measurable_cme e).comp hι)
  rw [h1, h, h2]
  congr 1
  funext t
  simp

omit [IsTopologicalGroup G] [IsTopologicalGroup G'] in

theorem integral_torus_corr (e : G ≃ₜ* G') {T T' : Type} [MeasurableSpace T] [MeasurableSpace T']
    (ι : T → G) (ι' : T' → G') (hι : Measurable ι) (hι' : Measurable ι')
    (τ : Measure T) (τ₀ : Measure T')
    (h : Measure.map ι' τ₀ = Measure.map (fun t => e (ι t)) τ)
    (g : G' → ℝ) (hg : Measurable g) :
    ∫ t' : T', g (ι' t') ∂τ₀ = ∫ t : T, g (e (ι t)) ∂τ := by
  have h1 : ∫ t' : T', g (ι' t') ∂τ₀ = ∫ x, g x ∂(Measure.map ι' τ₀) :=
    (integral_map hι'.aemeasurable hg.stronglyMeasurable.aestronglyMeasurable).symm
  rw [h1, h]
  exact integral_map ((measurable_cme e).comp hι).aemeasurable hg.stronglyMeasurable.aestronglyMeasurable

omit [IsTopologicalGroup G] [IsTopologicalGroup G'] in
theorem integral_map_equiv' (e : G ≃ₜ* G') (μ : Measure G) (F : G' → ℂ) :
    ∫ x', F x' ∂(Measure.map e μ) = ∫ x, F (e x) ∂μ := by
  have := integral_map_equiv (μ := μ) e.toHomeomorph.toMeasurableEquiv F
  exact this

omit [IsTopologicalGroup G] in

theorem value_transport_iff (e : G ≃ₜ* G') (T : Subgroup G) (T' : Subgroup G')
    [MeasurableSpace T] [BorelSpace T] [MeasurableSpace T'] [BorelSpace T']
    (τ : Measure T) (τ₀ : Measure T')
    (hcorr : Measure.map (fun t' : T' => (t' : G')) τ₀ = Measure.map (fun t : T => e (t : G)) τ)
    (μ : Measure G) (o : G → G) (o' : G' → G') (ho : ∀ x, e (o x) = o' (e x))
    (f : G → ℂ) (f' : G' → ℂ) (hff' : ∀ x', f' x' = f (e.symm x')) (I : ℂ) :
    (∃ w : G → ℝ, (∀ x, 0 ≤ w x) ∧ Measurable w ∧ HasCompactSupport w ∧
        (∀ x, f (o x) ≠ 0 → ∫ t : T, w ((t : G) * x) ∂τ = 1) ∧
        I = ∫ x, f (o x) * (w x : ℂ) ∂μ) ↔
    (∃ w' : G' → ℝ, (∀ x, 0 ≤ w' x) ∧ Measurable w' ∧ HasCompactSupport w' ∧
        (∀ x, f' (o' x) ≠ 0 → ∫ t' : T', w' ((t' : G') * x) ∂τ₀ = 1) ∧
        I = ∫ x, f' (o' x) * (w' x : ℂ) ∂(Measure.map e μ)) := by
  have hfo : ∀ x, f' (o' (e x)) = f (o x) := fun x => by rw [hff', ← ho, e.symm_apply_apply]
  have hme : Measurable (e : G → G') := measurable_cme e
  have hme' : Measurable (e.symm : G' → G) := measurable_cme e.symm
  constructor
  · rintro ⟨w, hw0, hwm, hwc, hsec, hI⟩
    refine ⟨w ∘ e.symm, fun x => hw0 _, hwm.comp hme', hwc.comp_homeomorph e.symm.toHomeomorph,
      fun x' hx' => ?_, ?_⟩
    · have hx : f (o (e.symm x')) ≠ 0 := by
        rw [← hfo, e.apply_symm_apply]; exact hx'
      rw [← hsec _ hx]
      rw [integral_torus_corr e (fun t : T => (t : G)) (fun t' : T' => (t' : G')) continuous_subtype_val.measurable
        continuous_subtype_val.measurable τ τ₀ hcorr (fun h => (w ∘ e.symm) (h * x'))
        ((hwm.comp hme').comp (continuous_id.mul continuous_const).measurable)]
      congr 1
      funext t
      simp [Function.comp, map_mul]
    · rw [integral_map_equiv' e μ, hI]
      congr 1
      funext x
      simp [Function.comp, hfo]
  · rintro ⟨w', hw0, hwm, hwc, hsec, hI⟩
    refine ⟨w' ∘ e, fun x => hw0 _, hwm.comp hme, hwc.comp_homeomorph e.toHomeomorph,
      fun x hx => ?_, ?_⟩
    · have hx' : f' (o' (e x)) ≠ 0 := by rwa [hfo]
      rw [← hsec _ hx']
      rw [integral_torus_corr e (fun t : T => (t : G)) (fun t' : T' => (t' : G')) continuous_subtype_val.measurable
        continuous_subtype_val.measurable τ τ₀ hcorr (fun h => w' (h * e x))
        (hwm.comp (continuous_id.mul continuous_const).measurable)]
      congr 1
      funext t
      simp [Function.comp, map_mul]
    · rw [hI, integral_map_equiv' e μ]
      congr 1
      funext x
      simp [Function.comp, hfo]

variable {H H' : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H]
  [Group H'] [TopologicalSpace H'] [IsTopologicalGroup H'] [MeasurableSpace H'] [BorelSpace H']

omit [IsTopologicalGroup G] [IsTopologicalGroup G'] in

theorem coupling_transport (eG : G ≃ₜ* G') (eH : H ≃ₜ* H') (φ : G →* H) (φ' : G' →* H')
    (hφ : Continuous φ) (hφ' : Continuous φ') (hcomm : ∀ g, eH (φ g) = φ' (eG g))
    (S : Subgroup G) (S' : Subgroup G') [MeasurableSpace S] [BorelSpace S] [MeasurableSpace S'] [BorelSpace S']
    (τ : Measure S) (τ₀ : Measure S')
    (hcorrS : Measure.map (fun s' : S' => (s' : G')) τ₀ = Measure.map (fun s : S => eG (s : G)) τ)
    (T : Subgroup H) (T' : Subgroup H') [MeasurableSpace T] [BorelSpace T] [MeasurableSpace T'] [BorelSpace T']
    (τ' : Measure T) (τ₀' : Measure T')
    (hcorrT : Measure.map (fun t' : T' => (t' : H')) τ₀' = Measure.map (fun t : T => eH (t : H)) τ')
    (y : H)
    (h : Measure.map (fun t : T => y⁻¹ * (t : H) * y) τ' = Measure.map (fun s : S => φ (s : G)) τ) :
    Measure.map (fun t' : T' => (eH y)⁻¹ * (t' : H') * eH y) τ₀' =
      Measure.map (fun s' : S' => φ' (s' : G')) τ₀ := by
  have hmeG : Measurable (eG : G → G') := measurable_cme eG
  have hmeH : Measurable (eH : H → H') := measurable_cme eH
  have hc1 : Measurable (fun h : H' => (eH y)⁻¹ * h * eH y) :=
    ((continuous_const.mul continuous_id).mul continuous_const).measurable
  have hc2 : Measurable (fun t : T => y⁻¹ * (t : H) * y) :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).measurable
  have e1 : Measure.map (fun t' : T' => (eH y)⁻¹ * (t' : H') * eH y) τ₀' =
      Measure.map (fun h : H' => (eH y)⁻¹ * h * eH y) (Measure.map (fun t' : T' => (t' : H')) τ₀') :=
    (Measure.map_map hc1 continuous_subtype_val.measurable).symm
  have e2 : Measure.map (fun s' : S' => φ' (s' : G')) τ₀ =
      Measure.map (φ' : G' → H') (Measure.map (fun s' : S' => (s' : G')) τ₀) :=
    (Measure.map_map hφ'.measurable continuous_subtype_val.measurable).symm
  have e3 : Measure.map (fun h : H' => (eH y)⁻¹ * h * eH y) (Measure.map (fun t : T => eH (t : H)) τ') =
      Measure.map ((fun h : H' => (eH y)⁻¹ * h * eH y) ∘ fun t : T => eH (t : H)) τ' :=
    Measure.map_map hc1 (hmeH.comp continuous_subtype_val.measurable)
  have e4 : Measure.map (φ' : G' → H') (Measure.map (fun s : S => eG (s : G)) τ) =
      Measure.map ((φ' : G' → H') ∘ fun s : S => eG (s : G)) τ :=
    Measure.map_map hφ'.measurable (hmeG.comp continuous_subtype_val.measurable)
  have e5 : ((fun h : H' => (eH y)⁻¹ * h * eH y) ∘ fun t : T => eH (t : H)) =
      ((eH : H → H') ∘ fun t : T => y⁻¹ * (t : H) * y) := by
    funext t
    simp [map_mul, map_inv]
  have e6 : ((φ' : G' → H') ∘ fun s : S => eG (s : G)) = ((eH : H → H') ∘ fun s : S => φ (s : G)) := by
    funext s
    simp [hcomm]
  have e7 : Measure.map ((eH : H → H') ∘ fun t : T => y⁻¹ * (t : H) * y) τ' =
      Measure.map (eH : H → H') (Measure.map (fun t : T => y⁻¹ * (t : H) * y) τ') :=
    (Measure.map_map hmeH hc2).symm
  have e8 : Measure.map ((eH : H → H') ∘ fun s : S => φ (s : G)) τ =
      Measure.map (eH : H → H') (Measure.map (fun s : S => φ (s : G)) τ) :=
    (Measure.map_map hmeH (hφ.measurable.comp continuous_subtype_val.measurable)).symm
  rw [e1, e2, hcorrT, hcorrS, e3, e4, e5, e6, e7, e8, h]

end GenericTransport
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal"

section ProductData

variable (K : Type) [Field K] [NumberField K] (L : Type) [Field L] [NumberField L] [Algebra K L]

noncomputable def thetaKC :
    GL (Fin 2) (InfiniteAdeleRing K) ≃ₜ* ((v : InfinitePlace K) → GL (Fin 2) v.Completion) :=
  { thetaK K with
    continuous_toFun := continuous_thetaK K
    continuous_invFun := continuous_thetaK_symm K }

@[scoped simp] theorem thetaKC_apply (g : GL (Fin 2) (InfiniteAdeleRing K)) : thetaKC K g = thetaK K g := rfl

@[scoped simp] theorem thetaKC_symm_apply (g : (v : InfinitePlace K) → GL (Fin 2) v.Completion) :
    (thetaKC K).symm g = (thetaK K).symm g := rfl

omit [NumberField K] in
theorem disc_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (g : GL (Fin 2) R) :
    Matrix.trace ((Matrix.GeneralLinearGroup.map f g : GL (Fin 2) S) : Matrix (Fin 2) (Fin 2) S) ^ 2 -
      4 * Matrix.det ((Matrix.GeneralLinearGroup.map f g : GL (Fin 2) S) : Matrix (Fin 2) (Fin 2) S) =
    f (Matrix.trace (g : Matrix (Fin 2) (Fin 2) R) ^ 2 - 4 * Matrix.det (g : Matrix (Fin 2) (Fin 2) R)) := by
  simp [Matrix.trace_fin_two, Matrix.det_fin_two, map_sub, map_mul, map_pow, map_add, map_ofNat]

omit [NumberField K] in
theorem isRegularSemisimple_map_iff_of_injective_isUnit {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : ∀ x : R, IsUnit (f x) → IsUnit x) (g : GL (Fin 2) R) :
    IsRegularSemisimple (Matrix.GeneralLinearGroup.map f g) ↔ IsRegularSemisimple g := by
  unfold IsRegularSemisimple
  rw [disc_map]
  exact ⟨hf _, fun h => h.map f⟩

omit [NumberField K] in
theorem map_scalar' {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (c : Rˣ) :
    Matrix.GeneralLinearGroup.map f (Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (f : R →* S) c) := by
  ext i j
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.GeneralLinearGroup.map_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem isUnit_infiniteAdeleRing_iff (x : InfiniteAdeleRing K) : IsUnit x ↔ ∀ v : InfinitePlace K, IsUnit (x v) :=
  Pi.isUnit_iff

theorem isRegularSemisimple_iff_forall_thetaK (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    IsRegularSemisimple g ↔ ∀ v, IsRegularSemisimple (thetaK K g v) := by
  unfold IsRegularSemisimple
  rw [isUnit_infiniteAdeleRing_iff]
  refine forall_congr' fun v => ?_
  rw [thetaK_apply, disc_map]
  rfl

noncomputable def unitAt (c : (InfiniteAdeleRing K)ˣ) (v : InfinitePlace K) : (v.Completion)ˣ :=
  Units.map (Pi.evalMonoidHom (fun v : InfinitePlace K => v.Completion) v) c

@[scoped simp] theorem val_unitAt (c : (InfiniteAdeleRing K)ˣ) (v : InfinitePlace K) :
    ((unitAt K c v : (v.Completion)ˣ) : v.Completion) = (c : InfiniteAdeleRing K) v := rfl

theorem thetaK_scalar (c : (InfiniteAdeleRing K)ˣ) :
    thetaK K (Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      fun v => Matrix.GeneralLinearGroup.scalar (Fin 2) (unitAt K c v) := by
  funext v
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [thetaK_val]
  simp only [Matrix.GeneralLinearGroup.scalar, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe,
    Matrix.scalar_apply, Matrix.diagonal_apply, val_unitAt]
  split_ifs <;> rfl

variable {K L} in
omit [NumberField K] [NumberField L] in

theorem map_normString {A B : Type} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B] (σ : L ≃ₐ[K] L)
    (h : GL (Fin 2) (L ⊗[K] A) →* GL (Fin 2) (L ⊗[K] B))
    (hσ : ∀ g, h (sigmaGL K L A σ g) = sigmaGL K L B σ (h g)) (δ : GL (Fin 2) (L ⊗[K] A)) :
    h (normString K L A σ δ) = normString K L B σ (h δ) := by
  unfold normString
  rw [map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  have hs : Function.Semiconj (⇑h) (⇑(sigmaGL K L A σ)) (⇑(sigmaGL K L B σ)) := hσ
  exact (hs.iterate_right i) δ

variable (σ : L ≃ₐ[K] L)
  (Ξ : L ⊗[K] InfiniteAdeleRing K ≃+* ((v : InfinitePlace K) → L ⊗[K] v.Completion))
  (Θ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) ≃* ((v : InfinitePlace K) → GL (Fin 2) (L ⊗[K] v.Completion)))
  (hΘapp : ∀ (g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (v : InfinitePlace K),
    Θ g v = Matrix.GeneralLinearGroup.map
      ((Pi.evalRingHom (fun v : InfinitePlace K => L ⊗[K] v.Completion) v).comp Ξ.toRingHom) g)
  (hΘσ : ∀ (g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (v : InfinitePlace K),
    Θ (sigmaGL K L (InfiniteAdeleRing K) σ g) v = sigmaGL K L v.Completion σ (Θ g v))
  (hΘι : ∀ (g : GL (Fin 2) (InfiniteAdeleRing K)) (v : InfinitePlace K),
    Θ (toTensorGL K L (InfiniteAdeleRing K) g) v = toTensorGL K L v.Completion (thetaK K g v))

noncomputable def thetaAt (v : InfinitePlace K) :
    GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) →* GL (Fin 2) (L ⊗[K] v.Completion) :=
  (Pi.evalMonoidHom (fun v : InfinitePlace K => GL (Fin 2) (L ⊗[K] v.Completion)) v).comp Θ.toMonoidHom

omit [NumberField L] in
@[scoped simp] theorem thetaAt_apply (v : InfinitePlace K) (g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :
    thetaAt K L Θ v g = Θ g v := rfl

include hΘσ in
omit [NumberField L] in
theorem theta_normString (δ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (v : InfinitePlace K) :
    Θ (normString K L (InfiniteAdeleRing K) σ δ) v = normString K L v.Completion σ (Θ δ v) := by
  have := map_normString σ (thetaAt K L Θ v) (fun g => hΘσ g v) δ
  simpa only [thetaAt_apply] using this

include hΘapp in
omit [NumberField L] in

theorem isRegularSemisimple_iff_forall_theta (g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :
    IsRegularSemisimple g ↔ ∀ v, IsRegularSemisimple (Θ g v) := by
  have key : ∀ v, IsRegularSemisimple (Θ g v) ↔
      IsUnit (Ξ (Matrix.trace (g : Matrix (Fin 2) (Fin 2) _) ^ 2 - 4 * Matrix.det (g : Matrix (Fin 2) (Fin 2) _)) v) := by
    intro v
    unfold IsRegularSemisimple
    rw [hΘapp, disc_map]
    rfl
  simp_rw [key]
  rw [← Pi.isUnit_iff]
  unfold IsRegularSemisimple
  exact (MulEquiv.isUnit_map Ξ.toMulEquiv).symm

include hΘσ hΘι in
omit [NumberField L] in

theorem isNormConjugator_iff_forall (γ : GL (Fin 2) (InfiniteAdeleRing K))
    (δ y : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :
    IsNormConjugator K L (InfiniteAdeleRing K) σ γ δ y ↔
      ∀ v, IsNormConjugator K L v.Completion σ (thetaK K γ v) (Θ δ v) (Θ y v) := by
  unfold IsNormConjugator
  rw [← Θ.injective.eq_iff, funext_iff]
  refine forall_congr' fun v => ?_
  rw [hΘι, map_mul, map_mul, map_inv, Pi.mul_apply, Pi.mul_apply, Pi.inv_apply, theta_normString K L σ Θ hΘσ]

end ProductData
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal"

section Readings

variable (K : Type) [Field K] [NumberField K] (L : Type) [Field L] [NumberField L] [Algebra K L]

open NumberField.InfinitePlace
open scoped NumberField.LiesOver Classical

theorem continuous_epsK (v : InfinitePlace K) : Continuous (CentAsmLocal.epsK K v) := by
  unfold CentAsmLocal.epsK
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact (Completion.isometry_extensionEmbedding v).continuous.comp (Units.continuous_val.matrix_elem i j)

theorem continuous_psiFactor_comm (v : InfinitePlace K) (w : InfinitePlace L) [w.1.LiesOver v.1] :
    Continuous fun z : L ⊗[K] v.Completion =>
      M4aHerbrand.ArchSemilocal.psiFactor v w (_root_.Algebra.TensorProduct.comm K L v.Completion z) := by
  set φ : L ⊗[K] v.Completion →+* w.Completion :=
    (M4aHerbrand.ArchSemilocal.psiFactor v w).toRingHom.comp
      (_root_.Algebra.TensorProduct.comm K L v.Completion).toRingEquiv.toRingHom with hφdef
  have hcoe : (fun z : L ⊗[K] v.Completion =>
      M4aHerbrand.ArchSemilocal.psiFactor v w (_root_.Algebra.TensorProduct.comm K L v.Completion z)) = ⇑φ := by
    funext z
    simp [hφdef]
  have hφ : Continuous (φ.comp (algebraMap v.Completion (L ⊗[K] v.Completion))) := by
    have heq : (φ.comp (algebraMap v.Completion (L ⊗[K] v.Completion)) : v.Completion → w.Completion) =
        algebraMap v.Completion w.Completion := by
      funext a
      have ha : algebraMap v.Completion (L ⊗[K] v.Completion) a = (1 : L) ⊗ₜ a := rfl
      show φ (algebraMap v.Completion (L ⊗[K] v.Completion) a) = _
      rw [ha, ← congrFun hcoe ((1 : L) ⊗ₜ a)]
      show M4aHerbrand.ArchSemilocal.psiFactor v w (_root_.Algebra.TensorProduct.comm K L v.Completion ((1 : L) ⊗ₜ a)) = _
      rw [_root_.Algebra.TensorProduct.comm_tmul, M4aHerbrand.ArchSemilocal.psiFactor_tmul, map_one, mul_one]
    rw [heq]
    exact M4aHerbrand.ArchSemilocal.continuous_algebraMap_completion v w
  rw [hcoe]
  exact IsModuleTopology.continuous_of_ringHom φ hφ

theorem continuous_epsL (v : InfinitePlace K) : Continuous (CentAsmLocal.epsL K L v) := by
  unfold CentAsmLocal.epsL
  refine continuous_pi fun i => continuous_pi fun j => continuous_pi fun w => ?_
  letI : w.1.1.LiesOver v.1 := M4aHerbrand.ArchSemilocal.liesOver_of_comap_eq w.2
  exact (Completion.isometry_extensionEmbedding w.1).continuous.comp
    ((continuous_psiFactor_comm K L v w.1).comp (Units.continuous_val.matrix_elem i j))

noncomputable def toMixedK :
    ((v : InfinitePlace K) → Fin 2 → Fin 2 → ℂ) →ₗ[ℝ] (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) where
  toFun z := fun i j =>
    (fun w : {w : InfinitePlace K // w.IsReal} => (z w.1 i j).re,
     fun w : {w : InfinitePlace K // w.IsComplex} => z w.1 i j)
  map_add' z z' := by
    funext i j
    ext w <;> simp
  map_smul' r z := by
    funext i j
    ext w <;> simp

theorem thetaK_symm_entry (g : (v : InfinitePlace K) → GL (Fin 2) v.Completion) (v : InfinitePlace K) (i j : Fin 2) :
    ((((thetaK K).symm g : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j) v =
      ((g v : GL (Fin 2) v.Completion) : Matrix (Fin 2) (Fin 2) v.Completion) i j := by
  rw [← thetaK_val K ((thetaK K).symm g) v i j, MulEquiv.apply_symm_apply]

theorem hF_reading (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (hfa : IsArchTestFactor K fa) :
    (∃ F₁ : ((v : InfinitePlace K) → Fin 2 → Fin 2 → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F₁ ∧
        ∀ g, (fa ∘ ⇑(thetaKC K).symm) g = F₁ (fun v => CentAsmLocal.epsK K v (g v))) ∧
      HasCompactSupport (fa ∘ ⇑(thetaKC K).symm) := by
  obtain ⟨⟨Φ, hΦ, hfaΦ⟩, hc⟩ := hfa
  refine ⟨⟨fun z => Φ (toMixedK K z), ?_, fun g => ?_⟩, hc.comp_homeomorph (thetaKC K).symm.toHomeomorph⟩
  · have hP : ContDiff ℝ (⊤ : ℕ∞) (fun z => toMixedK K z) := (toMixedK K).toContinuousLinearMap.contDiff
    exact hΦ.comp hP
  · show fa ((thetaK K).symm g) = Φ (toMixedK K fun v => CentAsmLocal.epsK K v (g v))
    rw [hfaΦ]
    congr 1
    funext i j
    rw [archEntries_apply, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
    · show Completion.extensionEmbeddingOfIsReal w.2 _ = (CentAsmLocal.epsK K w.1 (g w.1) i j).re
      rw [thetaK_symm_entry, CentAsmLocal.epsK, ← Completion.extensionEmbeddingOfIsReal_apply w.2, Complex.ofReal_re]
    · show Completion.extensionEmbedding w.1 _ = CentAsmLocal.epsK K w.1 (g w.1) i j
      rw [thetaK_symm_entry, CentAsmLocal.epsK]

end Readings
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal"

section ReadingsL

variable (K : Type) [Field K] [NumberField K] (L : Type) [Field L] [NumberField L] [Algebra K L]

open NumberField.InfinitePlace
open scoped NumberField.LiesOver Classical

variable (Ξ : L ⊗[K] InfiniteAdeleRing K ≃+* ((v : InfinitePlace K) → L ⊗[K] v.Completion))
  (hΞt : ∀ (x : L) (a : InfiniteAdeleRing K) (v : InfinitePlace K), Ξ (x ⊗ₜ a) v = x ⊗ₜ (a v))

include hΞt in

theorem archIdent_apply_eq_psiFactor (z : L ⊗[K] InfiniteAdeleRing K) (w : InfinitePlace L) :
    letI : w.1.LiesOver (w.comap (algebraMap K L)).1 := ⟨rfl⟩
    archIdent K L z w =
      M4aHerbrand.ArchSemilocal.psiFactor (w.comap (algebraMap K L)) w
        (_root_.Algebra.TensorProduct.comm K L (w.comap (algebraMap K L)).Completion (Ξ z (w.comap (algebraMap K L)))) := by
  letI : w.1.LiesOver (w.comap (algebraMap K L)).1 := ⟨rfl⟩
  induction z using TensorProduct.induction_on with
  | zero =>
      simp only [map_zero, Pi.zero_apply]
      rfl
  | tmul x a =>
      rw [archIdent_tmul_apply, hΞt, _root_.Algebra.TensorProduct.comm_tmul, M4aHerbrand.ArchSemilocal.psiFactor_tmul]
  | add z₁ z₂ h₁ h₂ =>
      rw [(archIdent K L).map_add z₁ z₂]
      show archIdent K L z₁ w + archIdent K L z₂ w = _
      rw [h₁, h₂, RingEquiv.map_add Ξ z₁ z₂, Pi.add_apply,
        map_add (_root_.Algebra.TensorProduct.comm K L (w.comap (algebraMap K L)).Completion),
        map_add (M4aHerbrand.ArchSemilocal.psiFactor (w.comap (algebraMap K L)) w)]

noncomputable def toMixedL :
    ((v : InfinitePlace K) → Fin 2 → Fin 2 → v.Extension L → ℂ) →ₗ[ℝ] (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace L) where
  toFun z := fun i j =>
    (fun w : {w : InfinitePlace L // w.IsReal} => (z (w.1.comap (algebraMap K L)) i j ⟨w.1, rfl⟩).re,
     fun w : {w : InfinitePlace L // w.IsComplex} => z (w.1.comap (algebraMap K L)) i j ⟨w.1, rfl⟩)
  map_add' z z' := by
    funext i j
    ext w <;> simp
  map_smul' r z := by
    funext i j
    ext w <;> simp

variable (Θ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) ≃ₜ* ((v : InfinitePlace K) → GL (Fin 2) (L ⊗[K] v.Completion)))
  (hΘapp : ∀ (g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (v : InfinitePlace K),
    Θ g v = Matrix.GeneralLinearGroup.map
      ((Pi.evalRingHom (fun v : InfinitePlace K => L ⊗[K] v.Completion) v).comp Ξ.toRingHom) g)

include hΘapp in
theorem theta_symm_entry (g : (v : InfinitePlace K) → GL (Fin 2) (L ⊗[K] v.Completion))
    (v : InfinitePlace K) (i j : Fin 2) :
    Ξ (((Θ.symm g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) _) i j) v =
      ((g v : GL (Fin 2) (L ⊗[K] v.Completion)) : Matrix (Fin 2) (Fin 2) _) i j := by
  conv_rhs => rw [← Θ.apply_symm_apply g, hΘapp]
  rfl

include hΞt hΘapp in

theorem hPhi_smooth (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (hφa : IsArchTestFactor L φa) :
    ∃ Φ₁ : ((v : InfinitePlace K) → Fin 2 → Fin 2 → v.Extension L → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ₁ ∧
        ∀ g, ((φa ∘ ⇑(archIdentGL K L)) ∘ ⇑Θ.symm) g = Φ₁ (fun v => CentAsmLocal.epsL K L v (g v)) := by
  obtain ⟨⟨Φ, hΦ, hφaΦ⟩, -⟩ := hφa
  refine ⟨fun z => Φ (toMixedL K L z), ?_, fun g => ?_⟩
  · have hP : ContDiff ℝ (⊤ : ℕ∞) (fun z => toMixedL K L z) := (toMixedL K L).toContinuousLinearMap.contDiff
    exact hΦ.comp hP
  · show φa (archIdentGL K L (Θ.symm g)) = Φ (toMixedL K L fun v => CentAsmLocal.epsL K L v (g v))
    rw [hφaΦ]
    congr 1
    funext i j
    rw [archEntries_apply, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    have hent : ∀ w : InfinitePlace L,
        ((archIdentGL K L (Θ.symm g) : GL (Fin 2) (InfiniteAdeleRing L)) :
            Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) i j w =
          (letI : w.1.LiesOver (w.comap (algebraMap K L)).1 := ⟨rfl⟩
           M4aHerbrand.ArchSemilocal.psiFactor (w.comap (algebraMap K L)) w
            (_root_.Algebra.TensorProduct.comm K L (w.comap (algebraMap K L)).Completion
              (((g (w.comap (algebraMap K L)) : GL (Fin 2) (L ⊗[K] (w.comap (algebraMap K L)).Completion)) :
                Matrix (Fin 2) (Fin 2) _) i j))) := by
      intro w
      show archIdent K L (((Θ.symm g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) _) i j) w = _
      rw [archIdent_apply_eq_psiFactor K L Ξ hΞt, theta_symm_entry K L Ξ Θ hΘapp]
    refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
    · show Completion.extensionEmbeddingOfIsReal w.2 _ = (CentAsmLocal.epsL K L _ _ i j _).re
      rw [hent, CentAsmLocal.epsL, ← Completion.extensionEmbeddingOfIsReal_apply w.2, Complex.ofReal_re]
    · show Completion.extensionEmbedding w.1 _ = CentAsmLocal.epsL K L _ _ i j _
      rw [hent, CentAsmLocal.epsL]

end ReadingsL
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal"

section ArchIdentHomeo

variable (K : Type) [Field K] [NumberField K] (L : Type) [Field L] [NumberField L] [Algebra K L]

open NumberField.InfinitePlace
open scoped NumberField.LiesOver Classical

noncomputable def archIdentEquiv : L ⊗[K] InfiniteAdeleRing K ≃+* InfiniteAdeleRing L :=
  (_root_.Algebra.TensorProduct.comm K L (InfiniteAdeleRing K)).toRingEquiv.trans
    (M4aHerbrand.ArchSemilocal.genuineInfinitePlaceData (K := K) (L := L)).baseChangeRingEquiv

theorem archIdentEquiv_apply (z : L ⊗[K] InfiniteAdeleRing K) : archIdentEquiv K L z = archIdent K L z := rfl

theorem coe_archIdentEquiv : (⇑(archIdentEquiv K L) : L ⊗[K] InfiniteAdeleRing K → InfiniteAdeleRing L) = ⇑(archIdent K L) :=
  funext (archIdentEquiv_apply K L)

theorem archIdentEquiv_toRingHom : (archIdentEquiv K L).toRingHom = archIdent K L :=
  RingHom.ext (archIdentEquiv_apply K L)

variable (Ξ : L ⊗[K] InfiniteAdeleRing K ≃+* ((v : InfinitePlace K) → L ⊗[K] v.Completion))
  (hΞ : Continuous Ξ)
  (hΞt : ∀ (x : L) (a : InfiniteAdeleRing K) (v : InfinitePlace K), Ξ (x ⊗ₜ a) v = x ⊗ₜ (a v))

include Ξ hΞ hΞt in
theorem continuous_archIdent : Continuous (archIdent K L) := by
  have h : ∀ w : InfinitePlace L, Continuous fun z => archIdent K L z w := by
    intro w
    letI : w.1.LiesOver (w.comap (algebraMap K L)).1 := ⟨rfl⟩
    have heq : (fun z => archIdent K L z w) = fun z =>
        M4aHerbrand.ArchSemilocal.psiFactor (w.comap (algebraMap K L)) w
          (_root_.Algebra.TensorProduct.comm K L (w.comap (algebraMap K L)).Completion
            (Ξ z (w.comap (algebraMap K L)))) :=
      funext fun z => archIdent_apply_eq_psiFactor K L Ξ hΞt z w
    rw [heq]
    exact (continuous_psiFactor_comm K L _ w).comp ((continuous_apply _).comp hΞ)
  exact continuous_pi h

attribute [local instance] secondCountableTopology_completion

include Ξ hΞ hΞt in
theorem continuous_archIdentEquiv_symm : Continuous (archIdentEquiv K L).symm := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (InfiniteAdeleRing K)
  haveI := AutomorphicForm.locallyCompactSpace_tensor K L (InfiniteAdeleRing K)
  haveI : SecondCountableTopology (InfiniteAdeleRing K) :=
    inferInstanceAs (SecondCountableTopology ((v : InfinitePlace K) → v.Completion))
  haveI : SecondCountableTopology (L ⊗[K] InfiniteAdeleRing K) :=
    Module.Finite.secondCountabletopology (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K)
  haveI : T2Space (InfiniteAdeleRing L) := inferInstance
  have hc : Continuous (archIdentEquiv K L) := by
    rw [coe_archIdentEquiv]; exact continuous_archIdent K L Ξ hΞ hΞt
  have hopen : IsOpenMap (archIdentEquiv K L) :=
    AddMonoidHom.isOpenMap_of_sigmaCompact (archIdentEquiv K L).toAddMonoidHom (archIdentEquiv K L).surjective hc
  exact ((archIdentEquiv K L).toEquiv.toHomeomorphOfContinuousOpen hc hopen).symm.continuous

include Ξ hΞ hΞt in

theorem exists_archIdentGLC :
    ∃ e : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) ≃ₜ* GL (Fin 2) (InfiniteAdeleRing L),
      (⇑e : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → GL (Fin 2) (InfiniteAdeleRing L)) = ⇑(archIdentGL K L) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (InfiniteAdeleRing K)
  have hc : Continuous (archIdentEquiv K L) := by
    rw [coe_archIdentEquiv]; exact continuous_archIdent K L Ξ hΞ hΞt
  refine ⟨CentAsmLocal.glEquiv (archIdentEquiv K L) hc (continuous_archIdentEquiv_symm K L Ξ hΞ hΞt), ?_⟩
  rw [CentAsmLocal.coe_glEquiv, archIdentEquiv_toRingHom]
  rfl

include Ξ hΞ hΞt in

theorem hasCompactSupport_comp_archIdentGL (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (hφa : HasCompactSupport φa) :
    HasCompactSupport (φa ∘ ⇑(archIdentGL K L)) := by
  obtain ⟨e, he⟩ := exists_archIdentGLC K L Ξ hΞ hΞt
  rw [← he]
  exact hφa.comp_homeomorph e.toHomeomorph

end ArchIdentHomeo
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal"

section Haar

variable (K : Type) [Field K] [NumberField K] (L : Type) [Field L] [NumberField L] [Algebra K L]

attribute [local instance 10000] AutomorphicForm.glBorelOf
attribute [local instance] borelSpace_gl locallyCompactSpace_gl secondCountableTopology_gl t2Space_gl
  secondCountableTopology_completion

theorem isHaarMeasure_archHaarK : (archHaarK K).IsHaarMeasure := by
  unfold archHaarK
  infer_instance

theorem isHaarMeasure_archHaarL :
    @Measure.IsHaarMeasure _ _ _ (glBorelOf _) (archHaarL K L) := by
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L (InfiniteAdeleRing K)
  haveI := AutomorphicForm.locallyCompactSpace_tensorGL K L (InfiniteAdeleRing K)
  unfold archHaarL
  infer_instance

theorem isHaarMeasure_map_thetaKC :
    @Measure.IsHaarMeasure ((v : InfinitePlace K) → GL (Fin 2) v.Completion) _ _ (borel _)
      (@Measure.map _ _ (glBorelOf _) (borel _) (thetaKC K) (archHaarK K)) := by
  letI : MeasurableSpace ((v : InfinitePlace K) → GL (Fin 2) v.Completion) := borel _
  haveI : BorelSpace ((v : InfinitePlace K) → GL (Fin 2) v.Completion) := ⟨rfl⟩
  haveI := isHaarMeasure_archHaarK K
  exact (thetaKC K).isHaarMeasure_map (archHaarK K)

theorem isHaarMeasure_map_thetaL
    (Θ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) ≃ₜ* ((v : InfinitePlace K) → GL (Fin 2) (L ⊗[K] v.Completion))) :
    @Measure.IsHaarMeasure ((v : InfinitePlace K) → GL (Fin 2) (L ⊗[K] v.Completion)) _ _ (borel _)
      (@Measure.map _ _ (glBorelOf _) (borel _) Θ (archHaarL K L)) := by
  letI : MeasurableSpace ((v : InfinitePlace K) → GL (Fin 2) (L ⊗[K] v.Completion)) := borel _
  haveI : BorelSpace ((v : InfinitePlace K) → GL (Fin 2) (L ⊗[K] v.Completion)) := ⟨rfl⟩
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L (InfiniteAdeleRing K)
  haveI : ∀ v : InfinitePlace K, IsTopologicalGroup (GL (Fin 2) (L ⊗[K] v.Completion)) := fun v =>
    AutomorphicForm.isTopologicalGroup_tensorGL K L _
  haveI := isHaarMeasure_archHaarL K L
  exact Θ.isHaarMeasure_map (archHaarL K L)

omit [NumberField K] in

theorem isInvInvariant_of_map {A B : Type} [Group A] [Group B] [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableInv A] [MeasurableInv B] (e : A ≃* B) (he : Measurable e) (he' : Measurable e.symm)
    (μ : Measure A) (h : (Measure.map e μ).IsInvInvariant) : μ.IsInvInvariant := by
  have hμ : μ = Measure.map e.symm (Measure.map e μ) := by
    rw [Measure.map_map he' he]
    simp [Function.comp_def]
  constructor
  show Measure.map Inv.inv μ = μ
  conv_lhs => rw [hμ]
  rw [Measure.map_map measurable_inv he',
    show (Inv.inv ∘ ⇑e.symm) = (⇑e.symm ∘ Inv.inv) from funext fun b => (map_inv e.symm b).symm,
    ← Measure.map_map he' measurable_inv]
  have : Measure.map Inv.inv (Measure.map (⇑e) μ) = Measure.map (⇑e) μ := h.inv_eq_self
  rw [this, ← hμ]

theorem isInvInvariant_of_isHaarMeasure_pi
    (μ : Measure ((v : InfinitePlace K) → GL (Fin 2) v.Completion)) [μ.IsHaarMeasure] : μ.IsInvInvariant := by
  obtain ⟨c, -, h⟩ := MeasureTheory.Measure.exists_ne_zero_map_mulEquiv_eq_smul_pi μ
    (fun v => (Measure.haar : Measure (GL (Fin 2) v.Completion))) (MulEquiv.refl _) continuous_id continuous_id
  haveI hinv : ∀ v : InfinitePlace K, (Measure.haar : Measure (GL (Fin 2) v.Completion)).IsInvInvariant := fun v =>
    (Matrix.GeneralLinearGroup.isMulRightInvariant_and_isInvInvariant_of_isHaarMeasure_fin_two _).2
  have hμ : μ = c • Measure.pi fun v : InfinitePlace K => (Measure.haar : Measure (GL (Fin 2) v.Completion)) := by
    rw [← h]
    exact (Measure.map_id).symm
  rw [hμ]
  constructor
  show Measure.map Inv.inv (c • Measure.pi fun v : InfinitePlace K => (Measure.haar : Measure (GL (Fin 2) v.Completion))) = _
  rw [Measure.map_smul, Measure.map_inv_eq_self]

omit [NumberField K] in

theorem centralizer_scalar_eq_top (c : (InfiniteAdeleRing K)ˣ) :
    Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) (InfiniteAdeleRing K))) = ⊤ := by
  refine (Subgroup.eq_top_iff' _).2 fun g => Subgroup.mem_centralizer_singleton_iff.2 ?_
  refine Units.ext ?_
  simp only [Units.val_mul]
  exact ((Matrix.scalar_commute (c : InfiniteAdeleRing K) (fun r' => Commute.all _ _)
    (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))).symm).eq

theorem isInvInvariant_centralizer_scalar (c : (InfiniteAdeleRing K)ˣ)
    (τ : @Measure (Subgroup.centralizer
        ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) (InfiniteAdeleRing K))))
      (centralizerBorel (InfiniteAdeleRing K) (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
    (hτ : @Measure.IsHaarMeasure _ _ _
      (centralizerBorel (InfiniteAdeleRing K) (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) τ) :
    @Measure.IsInvInvariant _
      (centralizerBorel (InfiniteAdeleRing K) (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) _ τ := by
  letI instS : MeasurableSpace (Subgroup.centralizer
      ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) (InfiniteAdeleRing K)))) :=
    centralizerBorel (InfiniteAdeleRing K) (Matrix.GeneralLinearGroup.scalar (Fin 2) c)
  haveI : BorelSpace (Subgroup.centralizer
      ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) (InfiniteAdeleRing K)))) := ⟨rfl⟩
  have hS := centralizer_scalar_eq_top K c
  let e1 : Subgroup.centralizer
      ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) (InfiniteAdeleRing K))) ≃*
        GL (Fin 2) (InfiniteAdeleRing K) :=
    (MulEquiv.subgroupCongr hS).trans Subgroup.topEquiv
  have he1 : Continuous e1 := continuous_subtype_val
  have he1' : Continuous e1.symm := continuous_id.subtype_mk _
  let e : Subgroup.centralizer
      ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) (InfiniteAdeleRing K))) ≃ₜ*
        ((v : InfinitePlace K) → GL (Fin 2) v.Completion) :=
    { e1.trans (thetaK K) with
      continuous_toFun := (continuous_thetaK K).comp he1
      continuous_invFun := he1'.comp (continuous_thetaK_symm K) }
  haveI : (Measure.map e τ).IsHaarMeasure := e.isHaarMeasure_map τ
  have hinv := isInvInvariant_of_isHaarMeasure_pi K (Measure.map e τ)
  exact isInvInvariant_of_map e.toMulEquiv e.continuous.measurable e.symm.continuous.measurable τ hinv

end Haar
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal"

section HReg

variable (K : Type) [Field K] [NumberField K] (L : Type) [Field L] [NumberField L] [Algebra K L]

attribute [local instance 10000] AutomorphicForm.glBorelOf
attribute [local instance] borelSpace_gl locallyCompactSpace_gl secondCountableTopology_gl t2Space_gl
  secondCountableTopology_completion

variable (σ : L ≃ₐ[K] L)
  (Ξ : L ⊗[K] InfiniteAdeleRing K ≃+* ((v : InfinitePlace K) → L ⊗[K] v.Completion))
  (Θ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) ≃ₜ* ((v : InfinitePlace K) → GL (Fin 2) (L ⊗[K] v.Completion)))
  (hΘapp : ∀ (g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (v : InfinitePlace K),
    Θ g v = Matrix.GeneralLinearGroup.map
      ((Pi.evalRingHom (fun v : InfinitePlace K => L ⊗[K] v.Completion) v).comp Ξ.toRingHom) g)
  (hΘσ : ∀ (g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (v : InfinitePlace K),
    Θ (sigmaGL K L (InfiniteAdeleRing K) σ g) v = sigmaGL K L v.Completion σ (Θ g v))
  (hΘι : ∀ (g : GL (Fin 2) (InfiniteAdeleRing K)) (v : InfinitePlace K),
    Θ (toTensorGL K L (InfiniteAdeleRing K) g) v = toTensorGL K L v.Completion (thetaK K g v))
  (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)

noncomputable abbrev piTwist : ((v : InfinitePlace K) → GL (Fin 2) (L ⊗[K] v.Completion)) →*
    ((v : InfinitePlace K) → GL (Fin 2) (L ⊗[K] v.Completion)) :=
  MonoidHom.pi fun i : InfinitePlace K =>
    (sigmaGL K L i.Completion σ).comp (Pi.evalMonoidHom (fun i : InfinitePlace K => GL (Fin 2) (L ⊗[K] i.Completion)) i)

noncomputable abbrev piEmb : ((v : InfinitePlace K) → GL (Fin 2) v.Completion) →*
    ((v : InfinitePlace K) → GL (Fin 2) (L ⊗[K] v.Completion)) :=
  MonoidHom.pi fun i : InfinitePlace K =>
    (toTensorGL K L i.Completion).comp (Pi.evalMonoidHom (fun i : InfinitePlace K => GL (Fin 2) i.Completion) i)

include hΘσ in
theorem theta_twist (g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :
    Θ (sigmaGL K L (InfiniteAdeleRing K) σ g) = piTwist K L σ (Θ g) := by
  funext v
  exact hΘσ g v

include hΘσ in
theorem theta_symm_twist (g : (v : InfinitePlace K) → GL (Fin 2) (L ⊗[K] v.Completion)) :
    Θ.symm (piTwist K L σ g) = sigmaGL K L (InfiniteAdeleRing K) σ (Θ.symm g) := by
  apply Θ.injective
  rw [Θ.apply_symm_apply, theta_twist K L σ Θ hΘσ, Θ.apply_symm_apply]

include hΘι in
theorem theta_emb (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    Θ (toTensorGL K L (InfiniteAdeleRing K) g) = piEmb K L (thetaKC K g) := by
  funext v
  exact hΘι g v

include hΘι in
theorem theta_symm_emb (g : (v : InfinitePlace K) → GL (Fin 2) v.Completion) :
    Θ.symm (piEmb K L g) = toTensorGL K L (InfiniteAdeleRing K) ((thetaKC K).symm g) := by
  apply Θ.injective
  rw [Θ.apply_symm_apply, theta_emb K L Θ hΘι, ContinuousMulEquiv.apply_symm_apply]

variable {K L} in
theorem continuous_toTensorGL (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous (toTensorGL K L A) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  have h : Continuous (algebraMap A (L ⊗[K] A)) := by
    have heq : (algebraMap A (L ⊗[K] A) : A → L ⊗[K] A) = fun a => a • (1 : L ⊗[K] A) :=
      funext fun a => Algebra.algebraMap_eq_smul_one a
    rw [heq]
    exact continuous_id.fun_smul continuous_const
  have h' : Continuous (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) := by
    convert h using 1 <;> first | rfl | (funext a; rfl)
  exact Continuous.units_map _ (continuous_id.matrix_map h')

theorem continuous_piEmb : Continuous (piEmb K L) :=
  continuous_pi fun v => (continuous_toTensorGL v.Completion).comp (continuous_apply v)

end HReg
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal"

end FDTEF
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.FDTEF"

set_option autoImplicit false

p2m_open "MeasureTheory NumberField AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm"
open scoped TensorProduct
open scoped TensorProduct.RightActions

namespace FDTEF

section HRegMain

variable (K : Type) [Field K] [NumberField K] (L : Type) [Field L] [NumberField L] [Algebra K L]

attribute [local instance 10000] AutomorphicForm.glBorelOf
attribute [local instance] borelSpace_gl locallyCompactSpace_gl secondCountableTopology_gl t2Space_gl
  secondCountableTopology_completion

variable (σ : L ≃ₐ[K] L)
  (Ξ : L ⊗[K] InfiniteAdeleRing K ≃+* ((v : InfinitePlace K) → L ⊗[K] v.Completion))
  (Θ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) ≃ₜ* ((v : InfinitePlace K) → GL (Fin 2) (L ⊗[K] v.Completion)))
  (hΘapp : ∀ (g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (v : InfinitePlace K),
    Θ g v = Matrix.GeneralLinearGroup.map
      ((Pi.evalRingHom (fun v : InfinitePlace K => L ⊗[K] v.Completion) v).comp Ξ.toRingHom) g)
  (hΘσ : ∀ (g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (v : InfinitePlace K),
    Θ (sigmaGL K L (InfiniteAdeleRing K) σ g) v = sigmaGL K L v.Completion σ (Θ g v))
  (hΘι : ∀ (g : GL (Fin 2) (InfiniteAdeleRing K)) (v : InfinitePlace K),
    Θ (toTensorGL K L (InfiniteAdeleRing K) g) v = toTensorGL K L v.Completion (thetaK K g v))
  (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)

include hΘapp hΘσ hΘι in
set_option maxHeartbeats 16000000 in

theorem hreg_of_areMatchingArch (hm : AreMatchingArch K L σ φa fa) :
    ∀ (γ : ((i : InfinitePlace K) → GL (Fin 2) (InfinitePlace.Completion i))) (δ y : ((i : InfinitePlace K) → GL (Fin 2) (L ⊗[K] InfinitePlace.Completion i))),
      (∀ i : InfinitePlace K, IsRegularSemisimple (γ i)) → (∀ i : InfinitePlace K, IsRegularSemisimple (normString K L (InfinitePlace.Completion i) σ (δ i))) →
      (∀ i : InfinitePlace K, IsNormConjugator K L (InfinitePlace.Completion i) σ (γ i) (δ i) (y i)) →
      ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set ((i : InfinitePlace K) → GL (Fin 2) (InfinitePlace.Completion i)))) (borel _))
        (τ' : @Measure (sigmaCentralizer (MonoidHom.pi fun i : InfinitePlace K => (sigmaGL K L (InfinitePlace.Completion i) σ).comp (Pi.evalMonoidHom (fun i : InfinitePlace K => GL (Fin 2) (L ⊗[K] InfinitePlace.Completion i)) i)) δ) (borel _)),
        @Measure.IsHaarMeasure _ _ _ (borel _) τ → @Measure.IsHaarMeasure _ _ _ (borel _) τ' →
        @Measure.IsInvInvariant _ (borel _) _ τ' →
        @Measure.map _ _ (borel _) (borel ((i : InfinitePlace K) → GL (Fin 2) (L ⊗[K] InfinitePlace.Completion i)))
            (fun t : sigmaCentralizer (MonoidHom.pi fun i : InfinitePlace K => (sigmaGL K L (InfinitePlace.Completion i) σ).comp (Pi.evalMonoidHom (fun i : InfinitePlace K => GL (Fin 2) (L ⊗[K] InfinitePlace.Completion i)) i)) δ => y⁻¹ * (t : ((i : InfinitePlace K) → GL (Fin 2) (L ⊗[K] InfinitePlace.Completion i))) * y) τ' =
          @Measure.map _ _ (borel _) (borel ((i : InfinitePlace K) → GL (Fin 2) (L ⊗[K] InfinitePlace.Completion i)))
            (fun s : Subgroup.centralizer ({γ} : Set ((i : InfinitePlace K) → GL (Fin 2) (InfinitePlace.Completion i))) => fun i => toTensorGL K L (InfinitePlace.Completion i) ((s : ((i : InfinitePlace K) → GL (Fin 2) (InfinitePlace.Completion i))) i)) τ →
        ∀ I I' : ℂ,
          (∃ W : ((i : InfinitePlace K) → GL (Fin 2) (L ⊗[K] InfinitePlace.Completion i)) → ℝ, (∀ x, 0 ≤ W x) ∧ Measurable[borel ((i : InfinitePlace K) → GL (Fin 2) (L ⊗[K] InfinitePlace.Completion i))] W ∧ HasCompactSupport W ∧
            (∀ x : ((i : InfinitePlace K) → GL (Fin 2) (L ⊗[K] InfinitePlace.Completion i)), ((φa ∘ ⇑(archIdentGL K L)) ∘ ⇑Θ.symm) (x⁻¹ * δ * (MonoidHom.pi fun i : InfinitePlace K => (sigmaGL K L (InfinitePlace.Completion i) σ).comp (Pi.evalMonoidHom (fun i : InfinitePlace K => GL (Fin 2) (L ⊗[K] InfinitePlace.Completion i)) i)) x) ≠ 0 →
              @integral _ ℝ _ _ (borel _) τ' (fun t => W ((t : ((i : InfinitePlace K) → GL (Fin 2) (L ⊗[K] InfinitePlace.Completion i))) * x)) = 1) ∧
            I' = @integral _ ℂ _ _ (borel ((i : InfinitePlace K) → GL (Fin 2) (L ⊗[K] InfinitePlace.Completion i))) (@Measure.map _ _ (glBorelOf _) (borel _) Θ (archHaarL K L)) (fun x => ((φa ∘ ⇑(archIdentGL K L)) ∘ ⇑Θ.symm) (x⁻¹ * δ * (MonoidHom.pi fun i : InfinitePlace K => (sigmaGL K L (InfinitePlace.Completion i) σ).comp (Pi.evalMonoidHom (fun i : InfinitePlace K => GL (Fin 2) (L ⊗[K] InfinitePlace.Completion i)) i)) x) * (W x : ℂ))) →
          (∃ w : ((i : InfinitePlace K) → GL (Fin 2) (InfinitePlace.Completion i)) → ℝ, (∀ x, 0 ≤ w x) ∧ Measurable[borel ((i : InfinitePlace K) → GL (Fin 2) (InfinitePlace.Completion i))] w ∧ HasCompactSupport w ∧
            (∀ x : ((i : InfinitePlace K) → GL (Fin 2) (InfinitePlace.Completion i)), (fa ∘ ⇑(thetaKC K).symm) (x⁻¹ * γ * x) ≠ 0 →
              @integral _ ℝ _ _ (borel _) τ (fun s => w ((s : ((i : InfinitePlace K) → GL (Fin 2) (InfinitePlace.Completion i))) * x)) = 1) ∧
            I = @integral _ ℂ _ _ (borel ((i : InfinitePlace K) → GL (Fin 2) (InfinitePlace.Completion i))) (@Measure.map _ _ (glBorelOf _) (borel _) (thetaKC K) (archHaarK K)) (fun x => (fa ∘ ⇑(thetaKC K).symm) (x⁻¹ * γ * x) * (w x : ℂ))) →
          I' = I := by
  intro γ' δ' y' hγ' hδ' hN' τ₀ τ₀' hτ₀ hτ₀' _hinv hcoup I I' hI' hI

  letI mP : MeasurableSpace ((v : InfinitePlace K) → GL (Fin 2) v.Completion) := borel _
  haveI : BorelSpace ((v : InfinitePlace K) → GL (Fin 2) v.Completion) := ⟨rfl⟩
  letI mP' : MeasurableSpace ((v : InfinitePlace K) → GL (Fin 2) (L ⊗[K] v.Completion)) := borel _
  haveI : BorelSpace ((v : InfinitePlace K) → GL (Fin 2) (L ⊗[K] v.Completion)) := ⟨rfl⟩
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L (InfiniteAdeleRing K)
  haveI : ∀ v : InfinitePlace K, IsTopologicalGroup (GL (Fin 2) (L ⊗[K] v.Completion)) := fun v =>
    AutomorphicForm.isTopologicalGroup_tensorGL K L _

  set γ := (thetaKC K).symm γ' with hγdef
  set δ := Θ.symm δ' with hδdef
  set y := Θ.symm y' with hydef
  have hγ'eq : thetaKC K γ = γ' := (thetaKC K).apply_symm_apply γ'
  have hδ'eq : Θ δ = δ' := Θ.apply_symm_apply δ'
  have hy'eq : Θ y = y' := Θ.apply_symm_apply y'
  have hγreg : IsRegularSemisimple γ := by
    rw [isRegularSemisimple_iff_forall_thetaK]
    intro v
    have : thetaK K γ v = γ' v := congrFun hγ'eq v
    rw [this]; exact hγ' v
  have hδreg : IsRegularSemisimple (normString K L (InfiniteAdeleRing K) σ δ) := by
    rw [isRegularSemisimple_iff_forall_theta K L Ξ Θ.toMulEquiv hΘapp]
    intro v
    have h1 : (Θ.toMulEquiv) (normString K L (InfiniteAdeleRing K) σ δ) v = normString K L v.Completion σ (δ' v) := by
      rw [← congrFun hδ'eq v]
      exact theta_normString K L σ Θ.toMulEquiv hΘσ δ v
    rw [h1]; exact hδ' v
  have hN : IsNormConjugator K L (InfiniteAdeleRing K) σ γ δ y := by
    rw [isNormConjugator_iff_forall K L σ Θ.toMulEquiv hΘσ hΘι]
    intro v
    have e1 : thetaK K γ v = γ' v := congrFun hγ'eq v
    have e2 : (Θ.toMulEquiv) δ v = δ' v := congrFun hδ'eq v
    have e3 : (Θ.toMulEquiv) y v = y' v := congrFun hy'eq v
    rw [e1, e2, e3]; exact hN' v

  letI mS' : MeasurableSpace (Subgroup.centralizer ({γ'} : Set ((v : InfinitePlace K) → GL (Fin 2) v.Completion))) := borel _
  haveI : BorelSpace (Subgroup.centralizer ({γ'} : Set ((v : InfinitePlace K) → GL (Fin 2) v.Completion))) := ⟨rfl⟩
  letI mS : MeasurableSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K)))) :=
    centralizerBorel _ _
  haveI : BorelSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K)))) := ⟨rfl⟩
  letI mT' : MeasurableSpace (sigmaCentralizer (piTwist K L σ) δ') := borel _
  haveI : BorelSpace (sigmaCentralizer (piTwist K L σ) δ') := ⟨rfl⟩
  letI mT : MeasurableSpace (twistedCentralizer K L (InfiniteAdeleRing K) σ δ) := twistedCentralizerBorel _ _ _ _ _
  haveI : BorelSpace (twistedCentralizer K L (InfiniteAdeleRing K) σ δ) := ⟨rfl⟩
  haveI : τ₀.IsHaarMeasure := hτ₀
  haveI : τ₀'.IsHaarMeasure := hτ₀'

  obtain ⟨τ, hτ, hcorrS, -⟩ := CentAsmLocal.exists_isHaarMeasure_centralizer_forward (thetaKC K).symm γ' τ₀
  obtain ⟨τ', hτ', hcorrT, -⟩ := CentAsmLocal.exists_isHaarMeasure_sigmaCentralizer_forward Θ.symm
    (piTwist K L σ) (sigmaGL K L (InfiniteAdeleRing K) σ) (theta_symm_twist K L σ Θ hΘσ) δ' τ₀'

  have hC : Coupled K L (InfiniteAdeleRing K) σ γ δ y τ τ' := by
    have := coupling_transport (thetaKC K).symm Θ.symm (piEmb K L) (toTensorGL K L (InfiniteAdeleRing K))
      (continuous_piEmb K L) (continuous_toTensorGL (InfiniteAdeleRing K)) (theta_symm_emb K L Θ hΘι)
      (Subgroup.centralizer ({γ'} : Set ((v : InfinitePlace K) → GL (Fin 2) v.Completion)))
      (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K)))) τ₀ τ hcorrS
      (sigmaCentralizer (piTwist K L σ) δ') (twistedCentralizer K L (InfiniteAdeleRing K) σ δ) τ₀' τ' hcorrT
      y' hcoup
    exact this

  have hcorrT' := corr_symm Θ.symm (fun t : sigmaCentralizer (piTwist K L σ) δ' => (t : (v : InfinitePlace K) → GL (Fin 2) (L ⊗[K] v.Completion)))
    (fun t : twistedCentralizer K L (InfiniteAdeleRing K) σ δ => (t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))
    continuous_subtype_val.measurable continuous_subtype_val.measurable τ₀' τ' hcorrT
  have hcorrS' := corr_symm (thetaKC K).symm
    (fun t : Subgroup.centralizer ({γ'} : Set ((v : InfinitePlace K) → GL (Fin 2) v.Completion)) => (t : (v : InfinitePlace K) → GL (Fin 2) v.Completion))
    (fun t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))) => (t : GL (Fin 2) (InfiniteAdeleRing K)))
    continuous_subtype_val.measurable continuous_subtype_val.measurable τ₀ τ hcorrS
  have hI'K : IsTwistedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ (archHaarL K L) δ τ'
      (φa ∘ ⇑(archIdentGL K L)) I' := by
    have key := (value_transport_iff Θ (twistedCentralizer K L (InfiniteAdeleRing K) σ δ)
      (sigmaCentralizer (piTwist K L σ) δ') τ' τ₀' hcorrT' (archHaarL K L)
      (fun x => x⁻¹ * δ * sigmaGL K L (InfiniteAdeleRing K) σ x) (fun x => x⁻¹ * δ' * piTwist K L σ x)
      (fun x => by rw [map_mul, map_mul, map_inv, hδ'eq, theta_twist K L σ Θ hΘσ])
      (φa ∘ ⇑(archIdentGL K L)) ((φa ∘ ⇑(archIdentGL K L)) ∘ ⇑Θ.symm) (fun _ => rfl) I').2 hI'
    obtain ⟨w, h0, hm', hc, hn, hIw⟩ := key
    exact ⟨w, ⟨h0, hm', hc, hn⟩, hIw⟩
  have hIK : IsOrbitalIntegralOn (InfiniteAdeleRing K) (archHaarK K) γ τ fa I := by
    have key := (value_transport_iff (thetaKC K) (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))))
      (Subgroup.centralizer ({γ'} : Set ((v : InfinitePlace K) → GL (Fin 2) v.Completion))) τ τ₀ hcorrS' (archHaarK K)
      (fun x => x⁻¹ * γ * x) (fun x => x⁻¹ * γ' * x)
      (fun x => by rw [map_mul, map_mul, map_inv, hγ'eq])
      fa (fa ∘ ⇑(thetaKC K).symm) (fun _ => rfl) I).2 hI
    obtain ⟨w, h0, hm', hc, hn, hIw⟩ := key
    exact ⟨w, ⟨h0, hm', hc, hn⟩, hIw⟩
  have hm' : AreMatchingOn K L (InfiniteAdeleRing K) σ (archHaarL K L) (archHaarK K) (φa ∘ ⇑(archIdentGL K L)) fa := hm
  exact hm'.1 δ hδreg γ hγreg y hN τ τ' hτ hτ' hC I I' hI'K hIK

end HRegMain
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.FDTEF"

end FDTEF
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.FDTEF"

set_option autoImplicit false

p2m_open "MeasureTheory NumberField AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm"
open scoped TensorProduct NNReal
open scoped TensorProduct.RightActions

namespace FDTEF

section Gram

variable (K : Type) [Field K] [NumberField K] (L : Type) [Field L] [NumberField L] [Algebra K L]

attribute [local instance 10000] AutomorphicForm.glBorelOf
attribute [local instance] borelSpace_gl locallyCompactSpace_gl secondCountableTopology_gl t2Space_gl
  secondCountableTopology_completion

theorem locallyCompactSpace_tensorGL_completion' (v : InfinitePlace K) :
    LocallyCompactSpace (GL (Fin 2) (L ⊗[K] v.Completion)) :=
  AutomorphicForm.locallyCompactSpace_tensorGL K L _

theorem isTopologicalGroup_tensorGL_completion' (v : InfinitePlace K) :
    IsTopologicalGroup (GL (Fin 2) (L ⊗[K] v.Completion)) :=
  AutomorphicForm.isTopologicalGroup_tensorGL K L _

attribute [local instance] locallyCompactSpace_tensorGL_completion' isTopologicalGroup_tensorGL_completion'

set_option maxHeartbeats 16000000 in

theorem rel_central_transfer_of_heng (σ : L ≃ₐ[K] L)
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (hφa : AutomorphicForm.IsArchTestFactor L φa)
    (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (hfa : AutomorphicForm.IsArchTestFactor K fa)
    (hm : AutomorphicForm.AreMatchingArch K L σ φa fa)
    (c : (InfiniteAdeleRing K)ˣ)

    (V : InfinitePlace K → Type) [∀ i, MeasurableSpace (V i)]
    (κ : ∀ i : InfinitePlace K, GL (Fin 2) (InfinitePlace.Completion i) → V i)
    (hκ : ∀ i : InfinitePlace K, Measurable[glBorelOf (InfinitePlace.Completion i)] (κ i))
    (hκi : ∀ i : InfinitePlace K, Function.Injective (κ i))
    (κ' : ∀ i : InfinitePlace K, GL (Fin 2) (L ⊗[K] InfinitePlace.Completion i) → V i)
    (hκ' : ∀ i : InfinitePlace K, Measurable[glBorelOf (L ⊗[K] InfinitePlace.Completion i)] (κ' i))
    (hκ'i : ∀ i : InfinitePlace K, Function.Injective (κ' i))
    (m : ∀ i : InfinitePlace K, Measure (V i)) (hmσ : ∀ i : InfinitePlace K, SigmaFinite (m i))
    (m' : ∀ i : InfinitePlace K, GL (Fin 2) (L ⊗[K] InfinitePlace.Completion i) → Measure (V i))
    (hm'σ : ∀ (i : InfinitePlace K) δ, SigmaFinite (m' i δ))
    (lam : InfinitePlace K → ℂ)
    (hsecL : ∀ (i : InfinitePlace K) (δ : GL (Fin 2) (L ⊗[K] InfinitePlace.Completion i)),
      ∀ τ' : @Measure (twistedCentralizer K L (InfinitePlace.Completion i) σ δ) (twistedCentralizerBorel K L (InfinitePlace.Completion i) σ δ),
        @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (InfinitePlace.Completion i) σ δ) τ' →
        @Measure.IsInvInvariant _ (twistedCentralizerBorel K L (InfinitePlace.Completion i) σ δ) _ τ' →
      (IsRegularSemisimple (normString K L (InfinitePlace.Completion i) σ δ) ∨
        ∃ (τ : @Measure (Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) (unitAt K c i)} : Set (GL (Fin 2) (InfinitePlace.Completion i))))
              (centralizerBorel (InfinitePlace.Completion i) (Matrix.GeneralLinearGroup.scalar (Fin 2) (unitAt K c i)))),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel (InfinitePlace.Completion i) (Matrix.GeneralLinearGroup.scalar (Fin 2) (unitAt K c i))) τ ∧
          (∃ s : ℝ≥0, s ≠ 0 ∧
            @Measure.map _ _ (centralizerBorel (InfinitePlace.Completion i) (Matrix.GeneralLinearGroup.scalar (Fin 2) (unitAt K c i))) _
                (fun t : Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) (unitAt K c i)} : Set (GL (Fin 2) (InfinitePlace.Completion i))) => κ i (t : GL (Fin 2) (InfinitePlace.Completion i))) τ =
              s • m i ∧
            @Measure.map _ _ (twistedCentralizerBorel K L (InfinitePlace.Completion i) σ δ) _
                (fun t : twistedCentralizer K L (InfinitePlace.Completion i) σ δ => κ' i (t : GL (Fin 2) (L ⊗[K] InfinitePlace.Completion i))) τ' =
              s • m' i δ)) →
      ∀ φ : GL (Fin 2) (L ⊗[K] InfinitePlace.Completion i) → ℂ, Continuous φ → HasCompactSupport φ →
        ∃ W : GL (Fin 2) (L ⊗[K] InfinitePlace.Completion i) → ℝ, IsTwistedSectionFnOn K L (InfinitePlace.Completion i) σ δ τ' φ W ∧ Continuous W)
    (heng : ∀ (i : InfinitePlace K) (φ : GL (Fin 2) (L ⊗[K] InfinitePlace.Completion i) → ℂ),
      ((∃ Φ₁ : (Fin 2 → Fin 2 → InfinitePlace.Extension L i → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ₁ ∧ ∀ g, φ g = Φ₁ (CentAsmLocal.epsL K L i g)) ∧ HasCompactSupport φ) →
      ∀ (f : GL (Fin 2) (InfinitePlace.Completion i) → ℂ),
      ((∃ F₁ : (Fin 2 → Fin 2 → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F₁ ∧ ∀ g, f g = F₁ (CentAsmLocal.epsK K i g)) ∧ HasCompactSupport f) →
      (∃ V ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) (unitAt K c i)),
        ∀ δ : GL (Fin 2) (L ⊗[K] InfinitePlace.Completion i), IsRegularSemisimple (normString K L (InfinitePlace.Completion i) σ δ) →
        ∀ γ ∈ V, IsRegularSemisimple γ →
        ∀ y : GL (Fin 2) (L ⊗[K] InfinitePlace.Completion i), IsNormConjugator K L (InfinitePlace.Completion i) σ γ δ y →
        ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfinitePlace.Completion i)))) (centralizerBorel (InfinitePlace.Completion i) γ))
          (τ' : @Measure (twistedCentralizer K L (InfinitePlace.Completion i) σ δ) (twistedCentralizerBorel K L (InfinitePlace.Completion i) σ δ)),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel (InfinitePlace.Completion i) γ) τ →
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (InfinitePlace.Completion i) σ δ) τ' →
          Coupled K L (InfinitePlace.Completion i) σ γ δ y τ τ' →
          ∀ I I' : ℂ, IsTwistedOrbitalIntegralOn K L (InfinitePlace.Completion i) σ (Measure.haar : Measure (GL (Fin 2) (L ⊗[K] InfinitePlace.Completion i))) δ τ' φ I' →
            IsOrbitalIntegralOn (InfinitePlace.Completion i) (Measure.haar : Measure (GL (Fin 2) (InfinitePlace.Completion i))) γ τ f I → I' = I) →
      ∀ δ y : GL (Fin 2) (L ⊗[K] InfinitePlace.Completion i),
        IsNormConjugator K L (InfinitePlace.Completion i) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) (unitAt K c i)) δ y →
        ∀ (τ : @Measure (Subgroup.centralizer
              ({Matrix.GeneralLinearGroup.scalar (Fin 2) (unitAt K c i)} : Set (GL (Fin 2) (InfinitePlace.Completion i))))
              (centralizerBorel (InfinitePlace.Completion i) (Matrix.GeneralLinearGroup.scalar (Fin 2) (unitAt K c i))))
          (τ' : @Measure (twistedCentralizer K L (InfinitePlace.Completion i) σ δ) (twistedCentralizerBorel K L (InfinitePlace.Completion i) σ δ)),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel (InfinitePlace.Completion i) (Matrix.GeneralLinearGroup.scalar (Fin 2) (unitAt K c i))) τ →
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (InfinitePlace.Completion i) σ δ) τ' →
          @Measure.IsInvInvariant _ (twistedCentralizerBorel K L (InfinitePlace.Completion i) σ δ) _ τ' →
          (∃ s : ℝ≥0, s ≠ 0 ∧
            @Measure.map _ _ (centralizerBorel (InfinitePlace.Completion i) (Matrix.GeneralLinearGroup.scalar (Fin 2) (unitAt K c i))) _
                (fun t : Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) (unitAt K c i)} : Set (GL (Fin 2) (InfinitePlace.Completion i))) => κ i (t : GL (Fin 2) (InfinitePlace.Completion i))) τ =
              s • m i ∧
            @Measure.map _ _ (twistedCentralizerBorel K L (InfinitePlace.Completion i) σ δ) _
                (fun t : twistedCentralizer K L (InfinitePlace.Completion i) σ δ => κ' i (t : GL (Fin 2) (L ⊗[K] InfinitePlace.Completion i))) τ' =
              s • m' i δ) →
          ∀ I I' : ℂ, IsTwistedOrbitalIntegralOn K L (InfinitePlace.Completion i) σ (Measure.haar : Measure (GL (Fin 2) (L ⊗[K] InfinitePlace.Completion i))) δ τ' φ I' →
            IsOrbitalIntegralOn (InfinitePlace.Completion i) (Measure.haar : Measure (GL (Fin 2) (InfinitePlace.Completion i))) (Matrix.GeneralLinearGroup.scalar (Fin 2) (unitAt K c i)) τ f I → I' = lam i * I)

    (δ y : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
    (hN : AutomorphicForm.IsNormConjugator K L (InfiniteAdeleRing K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y)
    (τ : @Measure (Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) (InfiniteAdeleRing K))))
        (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ)
        (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) τ)
    (hτ' : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ) τ')
    (hτ'i : @Measure.IsInvInvariant _ (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ) _ τ')

    (hrel : ∀ (Ξ : L ⊗[K] InfiniteAdeleRing K ≃+* ((v : InfinitePlace K) → L ⊗[K] v.Completion))
        (Θ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) ≃ₜ* ((v : InfinitePlace K) → GL (Fin 2) (L ⊗[K] v.Completion))),
        Continuous Ξ → Continuous Ξ.symm →
        (∀ (x : L) (a : InfiniteAdeleRing K) (v : InfinitePlace K), Ξ (x ⊗ₜ a) v = x ⊗ₜ (a v)) →
        (∀ (g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (v : InfinitePlace K),
          Θ g v = Matrix.GeneralLinearGroup.map
            ((Pi.evalRingHom (fun v : InfinitePlace K => L ⊗[K] v.Completion) v).comp Ξ.toRingHom) g) →
        (∀ (g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (v : InfinitePlace K),
          Θ (sigmaGL K L (InfiniteAdeleRing K) σ g) v = sigmaGL K L v.Completion σ (Θ g v)) →
        (∀ (g : GL (Fin 2) (InfiniteAdeleRing K)) (v : InfinitePlace K),
          Θ (toTensorGL K L (InfiniteAdeleRing K) g) v = toTensorGL K L v.Completion (thetaK K g v)) →
        ∃ s : ℝ≥0, s ≠ 0 ∧
          @Measure.map _ _ (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (Matrix.GeneralLinearGroup.scalar (Fin 2) c))
              MeasurableSpace.pi
              (fun t : Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) (InfiniteAdeleRing K))) =>
                fun i : InfinitePlace K => κ i (thetaK K (t : GL (Fin 2) (InfiniteAdeleRing K)) i)) τ =
            s • Measure.pi m ∧
          @Measure.map _ _ (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ) MeasurableSpace.pi
              (fun t : AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ =>
                fun i : InfinitePlace K => κ' i (Θ (t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) i)) τ' =
            s • Measure.pi (fun i : InfinitePlace K => m' i (Θ δ i))) :
    ∀ I I' : ℂ,
      AutomorphicForm.IsTwistedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ (AutomorphicForm.archHaarL K L) δ τ'
        (φa ∘ AutomorphicForm.archIdentGL K L) I' →
      AutomorphicForm.IsOrbitalIntegralOn (InfiniteAdeleRing K) (AutomorphicForm.archHaarK K)
        (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ fa I →
      I' = (∏ i : InfinitePlace K, lam i) * I := by
  classical
  intro I I' hI' hI
  obtain ⟨Ξ, Θ0, hΞ, hΞ', hΞt, hΘ, hΘ', hΘapp, hΘσ, hΘι⟩ := exists_thetaL K L
  let Θ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) ≃ₜ* ((v : InfinitePlace K) → GL (Fin 2) (L ⊗[K] v.Completion)) :=
    { Θ0 with continuous_toFun := hΘ, continuous_invFun := hΘ' }
  have hΘapp' : ∀ (g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (v : InfinitePlace K),
      Θ g v = Matrix.GeneralLinearGroup.map
        ((Pi.evalRingHom (fun v : InfinitePlace K => L ⊗[K] v.Completion) v).comp Ξ.toRingHom) g := hΘapp
  have hΘσ' : ∀ (g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (v : InfinitePlace K),
      Θ (sigmaGL K L (InfiniteAdeleRing K) σ g) v = sigmaGL K L v.Completion σ (Θ g v) := hΘσ σ
  have hΘι' : ∀ (g : GL (Fin 2) (InfiniteAdeleRing K)) (v : InfinitePlace K),
      Θ (toTensorGL K L (InfiniteAdeleRing K) g) v = toTensorGL K L v.Completion (thetaK K g v) := hΘι

  letI mP : MeasurableSpace ((v : InfinitePlace K) → GL (Fin 2) v.Completion) := borel _
  haveI : BorelSpace ((v : InfinitePlace K) → GL (Fin 2) v.Completion) := ⟨rfl⟩
  letI mP' : MeasurableSpace ((v : InfinitePlace K) → GL (Fin 2) (L ⊗[K] v.Completion)) := borel _
  haveI : BorelSpace ((v : InfinitePlace K) → GL (Fin 2) (L ⊗[K] v.Completion)) := ⟨rfl⟩
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L (InfiniteAdeleRing K)
  haveI := AutomorphicForm.t2Space_tensorGL K L (InfiniteAdeleRing K)

  set γ' : (v : InfinitePlace K) → GL (Fin 2) v.Completion := thetaKC K (Matrix.GeneralLinearGroup.scalar (Fin 2) c)
    with hγ'def
  have hN' : ∀ v, IsNormConjugator K L v.Completion σ (Matrix.GeneralLinearGroup.scalar (Fin 2) (unitAt K c v))
      (Θ δ v) (Θ y v) := by
    have h := (isNormConjugator_iff_forall K L σ Θ.toMulEquiv hΘσ' hΘι' _ δ y).1 hN
    intro v
    have hv := h v
    rwa [show thetaK K (Matrix.GeneralLinearGroup.scalar (Fin 2) c) v =
        Matrix.GeneralLinearGroup.scalar (Fin 2) (unitAt K c v) from congrFun (thetaK_scalar K c) v] at hv

  letI mS : MeasurableSpace (Subgroup.centralizer
      ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) (InfiniteAdeleRing K)))) := centralizerBorel _ _
  haveI : BorelSpace (Subgroup.centralizer
      ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) (InfiniteAdeleRing K)))) := ⟨rfl⟩
  letI mS' : MeasurableSpace (Subgroup.centralizer ({γ'} : Set ((v : InfinitePlace K) → GL (Fin 2) v.Completion))) :=
    borel _
  haveI : BorelSpace (Subgroup.centralizer ({γ'} : Set ((v : InfinitePlace K) → GL (Fin 2) v.Completion))) := ⟨rfl⟩
  letI mT : MeasurableSpace (twistedCentralizer K L (InfiniteAdeleRing K) σ δ) := twistedCentralizerBorel _ _ _ _ _
  haveI : BorelSpace (twistedCentralizer K L (InfiniteAdeleRing K) σ δ) := ⟨rfl⟩
  letI mT' : MeasurableSpace (sigmaCentralizer (piTwist K L σ) (Θ δ)) := borel _
  haveI : BorelSpace (sigmaCentralizer (piTwist K L σ) (Θ δ)) := ⟨rfl⟩
  haveI : τ.IsHaarMeasure := hτ
  haveI : τ'.IsHaarMeasure := hτ'

  let eC := CentAsmLocal.centralizerCongr (thetaKC K) (Matrix.GeneralLinearGroup.scalar (Fin 2) c)
  let eT := CentAsmLocal.sigmaCentralizerCongr Θ (sigmaGL K L (InfiniteAdeleRing K) σ) (piTwist K L σ)
    (theta_twist K L σ Θ hΘσ') δ
  set τ₀ : Measure (Subgroup.centralizer ({γ'} : Set ((v : InfinitePlace K) → GL (Fin 2) v.Completion))) :=
    Measure.map eC τ with hτ₀def
  set τ₀' : Measure (sigmaCentralizer (piTwist K L σ) (Θ δ)) := Measure.map eT τ' with hτ₀'def
  have heCm : Measurable eC := eC.continuous.measurable
  have heTm : Measurable eT := eT.continuous.measurable
  have hτ₀ : τ₀.IsHaarMeasure := by rw [hτ₀def]; exact eC.isHaarMeasure_map τ
  have hτ₀' : τ₀'.IsHaarMeasure := by rw [hτ₀'def]; exact eT.isHaarMeasure_map τ'
  have hcorrS : Measure.map (fun t' : Subgroup.centralizer ({γ'} : Set ((v : InfinitePlace K) → GL (Fin 2) v.Completion)) =>
        (t' : (v : InfinitePlace K) → GL (Fin 2) v.Completion)) τ₀ =
      Measure.map (fun t : Subgroup.centralizer
        ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) (InfiniteAdeleRing K))) =>
          thetaKC K (t : GL (Fin 2) (InfiniteAdeleRing K))) τ := by
    rw [hτ₀def, Measure.map_map continuous_subtype_val.measurable heCm]
    rfl
  have hcorrT : Measure.map (fun t' : sigmaCentralizer (piTwist K L σ) (Θ δ) =>
        (t' : (v : InfinitePlace K) → GL (Fin 2) (L ⊗[K] v.Completion))) τ₀' =
      Measure.map (fun t : twistedCentralizer K L (InfiniteAdeleRing K) σ δ => Θ (t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) τ' := by
    rw [hτ₀'def, Measure.map_map continuous_subtype_val.measurable heTm]
    rfl
  have hτ₀'inv : τ₀'.IsInvInvariant := by
    haveI := hτ'i
    rw [hτ₀'def]
    constructor
    show Measure.map Inv.inv (Measure.map eT τ') = Measure.map eT τ'
    rw [Measure.map_map measurable_inv heTm,
      show (Inv.inv ∘ ⇑eT) = (⇑eT ∘ Inv.inv) from funext fun t => (map_inv eT t).symm,
      ← Measure.map_map heTm measurable_inv, Measure.map_inv_eq_self]

  have hrelP : ∃ s : ℝ≥0, s ≠ 0 ∧
      @Measure.map _ _ mS' MeasurableSpace.pi
          (fun t : Subgroup.centralizer ({γ'} : Set ((v : InfinitePlace K) → GL (Fin 2) v.Completion)) =>
            fun i : InfinitePlace K => κ i ((t : (v : InfinitePlace K) → GL (Fin 2) v.Completion) i)) τ₀ =
        s • Measure.pi m ∧
      @Measure.map _ _ mT' MeasurableSpace.pi
          (fun t : sigmaCentralizer (piTwist K L σ) (Θ δ) =>
            fun i : InfinitePlace K => κ' i ((t : (v : InfinitePlace K) → GL (Fin 2) (L ⊗[K] v.Completion)) i)) τ₀' =
        s • Measure.pi (fun i : InfinitePlace K => m' i (Θ δ i)) := by
    obtain ⟨s, hs, h1, h2⟩ := hrel Ξ Θ hΞ hΞ' hΞt hΘapp' hΘσ' hΘι'
    refine ⟨s, hs, ?_, ?_⟩
    · have hg : Measurable[mS', MeasurableSpace.pi]
          (fun t : Subgroup.centralizer ({γ'} : Set ((v : InfinitePlace K) → GL (Fin 2) v.Completion)) =>
            fun i : InfinitePlace K => κ i ((t : (v : InfinitePlace K) → GL (Fin 2) v.Completion) i)) :=
        measurable_pi_lambda _ fun i => (hκ i).comp ((continuous_apply i).comp continuous_subtype_val).measurable
      rw [← h1, hτ₀def, Measure.map_map hg heCm]
      rfl
    · have hg : Measurable[mT', MeasurableSpace.pi]
          (fun t : sigmaCentralizer (piTwist K L σ) (Θ δ) =>
            fun i : InfinitePlace K => κ' i ((t : (v : InfinitePlace K) → GL (Fin 2) (L ⊗[K] v.Completion)) i)) :=
        measurable_pi_lambda _ fun i => (hκ' i).comp ((continuous_apply i).comp continuous_subtype_val).measurable
      rw [← h2, hτ₀'def, Measure.map_map hg heTm]
      rfl

  have hI'P := (value_transport_iff Θ (twistedCentralizer K L (InfiniteAdeleRing K) σ δ)
      (sigmaCentralizer (piTwist K L σ) (Θ δ)) τ' τ₀' hcorrT (archHaarL K L)
      (fun x => x⁻¹ * δ * sigmaGL K L (InfiniteAdeleRing K) σ x) (fun x => x⁻¹ * Θ δ * piTwist K L σ x)
      (fun x => by rw [map_mul, map_mul, map_inv, theta_twist K L σ Θ hΘσ'])
      (φa ∘ ⇑(archIdentGL K L)) ((φa ∘ ⇑(archIdentGL K L)) ∘ ⇑Θ.symm) (fun _ => rfl) I').1
      (by obtain ⟨w, ⟨h0, hm', hc, hn⟩, hIw⟩ := hI'; exact ⟨w, h0, hm', hc, hn, hIw⟩)
  have hIP := (value_transport_iff (thetaKC K)
      (Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) (InfiniteAdeleRing K))))
      (Subgroup.centralizer ({γ'} : Set ((v : InfinitePlace K) → GL (Fin 2) v.Completion))) τ τ₀ hcorrS (archHaarK K)
      (fun x => x⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) c * x) (fun x => x⁻¹ * γ' * x)
      (fun x => by rw [map_mul, map_mul, map_inv])
      fa (fa ∘ ⇑(thetaKC K).symm) (fun _ => rfl) I).1
      (by obtain ⟨w, ⟨h0, hm', hc, hn⟩, hIw⟩ := hI; exact ⟨w, h0, hm', hc, hn, hIw⟩)

  have H := AutomorphicForm.semilocal_central_transfer_of_forall_oneplace_of_referenceMeasures K L σ
      (fun v : InfinitePlace K => v.Completion) (fun _ => Fin 2 → Fin 2 → ℂ)
      (fun v : InfinitePlace K => Fin 2 → Fin 2 → v.Extension L → ℂ)
      (CentAsmLocal.epsK K) (continuous_epsK K) (CentAsmLocal.epsL K L) (continuous_epsL K L) (unitAt K c)
      V κ hκ hκi κ' hκ' hκ'i m hmσ m' hm'σ lam
      (fun v => Measure.haar) (fun v => inferInstance) (fun v => isMulRightInvariant_haar_completion K v)
      (fun v => Measure.haar) (fun v => inferInstance)
      (CentAsmLocal.hsecK K) hsecL heng
      (Measure.map (thetaKC K) (archHaarK K)) (isHaarMeasure_map_thetaKC K)
      (Measure.map Θ (archHaarL K L)) (isHaarMeasure_map_thetaL K L Θ)
      (fa ∘ ⇑(thetaKC K).symm) (hF_reading K fa hfa)
      ((φa ∘ ⇑(archIdentGL K L)) ∘ ⇑Θ.symm)
      ⟨hPhi_smooth K L Ξ hΞt Θ hΘapp' φa hφa,
        (hasCompactSupport_comp_archIdentGL K L Ξ hΞ hΞt φa hφa.2).comp_homeomorph Θ.symm.toHomeomorph⟩
      (hreg_of_areMatchingArch K L σ Ξ Θ hΘapp' hΘσ' hΘι' φa fa hm)
  have hsc : (fun i : InfinitePlace K => Matrix.GeneralLinearGroup.scalar (Fin 2) (unitAt K c i)) = γ' := by
    rw [hγ'def]; exact (thetaK_scalar K c).symm
  rw [hsc] at H
  exact H (Θ δ) (Θ y) hN' τ₀ τ₀' hτ₀ hτ₀' hτ₀'inv hrelP I I' hI'P hIP

end Gram
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.FDTEF"

end FDTEF
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.FDTEF"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000

p2m_open "MeasureTheory NumberField AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm"
open scoped TensorProduct
open scoped TensorProduct.RightActions

namespace Ws46
namespace CASM

theorem prod_sign_eq_neg_one_pow_card {ι : Type*} [Fintype ι] (P : ι → Prop) [DecidablePred P]
    (lam : ι → ℂ) (hneg : ∀ w, P w → lam w = -1) (hpos : ∀ w, ¬ P w → lam w = 1) :
    ∏ w, lam w = (-1 : ℂ) ^ Nat.card {w // P w} := by
  classical
  have : ∀ w, lam w = if P w then (-1 : ℂ) else 1 := fun w => by
    by_cases h : P w
    · rw [if_pos h, hneg w h]
    · rw [if_neg h, hpos w h]
  simp_rw [this]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one, Nat.card_eq_fintype_card,
    Fintype.card_subtype]

end Ws46.CASM
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.FDTEF"
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.FDTEF"

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "isTopologicalRing_tensor t2Space_tensor locallyCompactSpace_tensor isTopologicalGroup_tensorGL t2Space_tensorGL locallyCompactSpace_tensorGL glBorelOf borelSpace_glBorelOf centralizerBorel toTensorGL sigmaTensor sigmaGL normString IsSigmaConjugate IsNormConjugator IsNormOf twistedCentralizer twistedCentralizerBorel IsSectionFnOn IsOrbitalIntegralOn IsTwistedSectionFnOn IsTwistedOrbitalIntegralOn Coupled AreMatchingOn archHaarK archHaarL archIdent archIdentGL AreMatchingArch IsRegularSemisimple archEntries_apply IsArchTestFactor sigmaCentralizer mem_sigmaCentralizer_iff SplitPlace.psi SplitPlace.psiEquiv SplitPlace.psiEquiv_apply SplitPlace.psiEquiv_symm_const SplitPlace.psiGL exists_mulEquiv_generalLinearGroup_tensorProduct_infiniteAdeleRing_pi exists_ringEquiv_tensorProduct_infiniteAdeleRing_pi_forall_tmul archIdent_tmul_apply exists_continuous_isSectionFnOn_and_isOrbitalIntegralOn_iff_completion_of_isRegularSemisimple exists_isTwistedSectionFnOn_and_continuous_completion_of_isRegularSemisimple_normString exists_isTwistedSectionFnOn_and_continuous_completion_of_isSigmaConjugate_scalar_of_prime semilocal_central_transfer_of_forall_oneplace_of_referenceMeasures exists_isNormConjugator_and_coupled_of_gram_of_algHom_real exists_isNormConjugator_and_coupled_of_gram_of_algHom_complex exists_isNormConjugator_and_coupled_of_gram_conjAe_of_pos isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar map_centralizer_map_ringEquiv_pi_eq_smul_gram_of_infiniteAdeleRing map_twistedCentralizer_map_ringEquiv_pi_eq_smul_gram_of_infiniteAdeleRing mem_span_map_ringEquiv_pi_iff_of_span_eq_range_includeRight mem_span_map_ringEquiv_pi_iff_of_span_eq_setOf_mul_eq_mul_map_sigmaTensor exists_gram_map_of_ringEquiv_of_exists_gram exists_ringEquiv_tensor_completion_complex_of_isRamified isTwistedOrbitalIntegralOn_map_of_ringEquiv_and_isHaarMeasure_map isNormConjugator_map_iff_and_coupled_map_iff_of_ringEquiv isOrbitalIntegralOn_map_generalLinearGroup_map_of_ringEquiv isHaarMeasure_map_and_exists_isHaarMeasure_centralizer_of_ringEquiv pos_and_exists_coupled_toTensorGL_scalar_one_iff_of_coupled_scalar_conjAe exists_ringEquiv_tensor_baseChange_of_ringEquiv isOrbitalIntegralOn_scalar_neg_of_isTwistedOrbitalIntegralOn_conjAe_of_gram_of_nhds_forall_isNormConjugator_of_neg exists_isSigmaConjugate_scalar_of_isNormConjugator_scalar_of_algHom_of_prime exists_isTwistedSectionFnOn_and_continuous_completion_of_not_isSigmaConjugate_scalar_of_finrank_eq_two exists_isSigmaConjugate_scalar_conjAe_iff_pos_of_isNormConjugator_scalar"
namespace CasmGram
p2m_open "AutomorphicForm"

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

@[reducible] def algR : Algebra ℝ (InfiniteAdeleRing K) :=
  ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
    (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra

@[reducible] def algKw (w : InfinitePlace K) : Algebra ℝ w.Completion :=
  ((Pi.evalRingHom (fun v : InfinitePlace K => v.Completion) w).comp
    (@algebraMap ℝ (InfiniteAdeleRing K) _ _ (algR K))).toAlgebra

@[reducible] def algE (w : InfinitePlace K) : Algebra ℝ (L ⊗[K] w.Completion) :=
  ((Algebra.TensorProduct.includeRight : w.Completion →ₐ[K] L ⊗[K] w.Completion).toRingHom.comp
    (@algebraMap ℝ w.Completion _ _ (algKw K w))).toAlgebra

attribute [local instance] algR algE

abbrev V (w : InfinitePlace K) : Type := Matrix (Fin 2) (Fin 2) (L ⊗[K] w.Completion)

scoped instance (w : InfinitePlace K) : MeasurableSpace (V K L w) := borel _
scoped instance (w : InfinitePlace K) : BorelSpace (V K L w) := ⟨rfl⟩

def κ (w : InfinitePlace K) (g : GL (Fin 2) w.Completion) : V K L w :=
  ((g : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).map (fun x : w.Completion => (1 : L) ⊗ₜ[K] x)

def κ' (w : InfinitePlace K) (h : GL (Fin 2) (L ⊗[K] w.Completion)) : V K L w :=
  ((h : GL (Fin 2) (L ⊗[K] w.Completion)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] w.Completion))

def WK (w : InfinitePlace K) : Submodule ℝ (V K L w) :=
  Submodule.span ℝ (Set.range (fun Y : Matrix (Fin 2) (Fin 2) w.Completion =>
    Y.map (fun x : w.Completion => (1 : L) ⊗ₜ[K] x)))

def WL (σ : L ≃ₐ[K] L) (w : InfinitePlace K) (δ' : Matrix (Fin 2) (Fin 2) (L ⊗[K] w.Completion)) :
    Submodule ℝ (V K L w) :=
  Submodule.span ℝ {Y : Matrix (Fin 2) (Fin 2) (L ⊗[K] w.Completion) |
    Y * δ' = δ' * Y.map (AutomorphicForm.sigmaTensor K L w.Completion σ)}

def gramWD (w : InfinitePlace K) (n : ℕ) (f : Fin n → V K L w) : Measure (V K L w) :=
  ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun a b : Fin n =>
      Algebra.trace ℝ (L ⊗[K] w.Completion) (Matrix.trace (f a * f b))).det|)) •
    Measure.map (fun c : Fin n → ℝ => ∑ a, c a • f a) volume).withDensity
    (fun X : V K L w => (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹)

open scoped Classical in

def m (w : InfinitePlace K) : Measure (V K L w) :=
  if h : ∃ (n : ℕ) (b : Fin n → V K L w), LinearIndependent ℝ b ∧ Submodule.span ℝ (Set.range b) = WK K L w
  then gramWD K L w h.choose h.choose_spec.choose else 0

open scoped Classical in

def m' (σ : L ≃ₐ[K] L) (c : (InfiniteAdeleRing K)ˣ) (w : InfinitePlace K)
    (δ' : GL (Fin 2) (L ⊗[K] w.Completion)) : Measure (V K L w) :=
  if ∃ y : GL (Fin 2) (L ⊗[K] w.Completion), AutomorphicForm.IsNormConjugator K L w.Completion σ
      (Matrix.GeneralLinearGroup.scalar (Fin 2) (FDTEF.unitAt K c w)) δ' y then
    (if h : ∃ (n : ℕ) (b : Fin n → V K L w), LinearIndependent ℝ b ∧
        Submodule.span ℝ (Set.range b) = WL K L σ w (δ' : Matrix (Fin 2) (Fin 2) (L ⊗[K] w.Completion))
    then gramWD K L w h.choose h.choose_spec.choose else 0)
  else 0

open scoped Classical in

def lam (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (w : InfinitePlace K) : ℂ :=
  if ∃ z : (L ⊗[K] w.Completion)ˣ,
      AutomorphicForm.IsSigmaConjugate K L w.Completion σ
        (Matrix.GeneralLinearGroup.map
          (Algebra.TensorProduct.map (AlgHom.id K L)
            (Pi.evalAlgHom K (fun w : InfinitePlace K => w.Completion) w)).toRingHom δ)
        (Matrix.GeneralLinearGroup.scalar (Fin 2) z)
  then 1 else -1

theorem measurable_κ (w : InfinitePlace K) : Measurable[glBorelOf w.Completion] (κ K L w) := by
  letI := glBorelOf w.Completion
  haveI : BorelSpace (GL (Fin 2) w.Completion) := borelSpace_glBorelOf _
  haveI := isTopologicalRing_tensor K L w.Completion
  have hc : Continuous (fun x : w.Completion => (1 : L) ⊗ₜ[K] x) :=
    (IsModuleTopology.continuous_of_linearMap (Algebra.linearMap w.Completion (L ⊗[K] w.Completion))).congr
      (fun x => rfl)
  exact (Units.continuous_val.matrix_map hc).measurable

theorem injective_κ (w : InfinitePlace K) : Function.Injective (κ K L w) := by
  intro a b h
  apply Units.ext
  ext i j : 1
  have hij := congrFun (congrFun h i) j
  simp only [κ, Matrix.map_apply] at hij
  haveI : Module.Free K w.Completion := Module.Free.of_divisionRing K _
  haveI : Module.Flat K w.Completion := Module.Flat.of_free
  exact Algebra.TensorProduct.includeRight_injective (A := L) (algebraMap K L).injective hij

theorem measurable_κ' (w : InfinitePlace K) : Measurable[glBorelOf (L ⊗[K] w.Completion)] (κ' K L w) := by
  letI := glBorelOf (L ⊗[K] w.Completion)
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] w.Completion)) := borelSpace_glBorelOf _
  exact Units.continuous_val.measurable

theorem injective_κ' (w : InfinitePlace K) : Function.Injective (κ' K L w) := by
  intro a b h
  exact Units.ext h

end AutomorphicForm.CasmGram
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.FDTEF P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CasmGram"
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.FDTEF"

end
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.FDTEF P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CasmGram"

noncomputable section

namespace P2mGramSide

open scoped ENNReal NNReal

section Generic

variable (E : Type) [CommRing E] [Algebra ℝ E] [Module.Free ℝ E] [Module.Finite ℝ E]
  [TopologicalSpace E] [IsTopologicalRing E] [ContinuousSMul ℝ E] [T2Space E]
  [MeasurableSpace (Matrix (Fin 2) (Fin 2) E)] [BorelSpace (Matrix (Fin 2) (Fin 2) E)]

theorem continuous_algebraNorm : Continuous (Algebra.norm ℝ : E → ℝ) := by
  classical
  let b := Module.finBasis ℝ E
  have h : (Algebra.norm ℝ : E → ℝ) = fun x => (Algebra.leftMulMatrix b x).det := by
    funext x; exact Algebra.norm_eq_matrix_det b x
  rw [h]
  exact ((Algebra.leftMulMatrix b).toLinearMap.continuous_of_finiteDimensional).matrix_det

theorem measurable_density :
    Measurable fun X : Matrix (Fin 2) (Fin 2) E => (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹ := by
  have hc : Continuous fun X : Matrix (Fin 2) (Fin 2) E => |Algebra.norm ℝ (Matrix.det X)| :=
    continuous_abs.comp ((continuous_algebraNorm E).comp (continuous_id.matrix_det))
  exact (ENNReal.continuous_ofReal.comp hc).measurable.inv

theorem sigmaFinite_gramWD {k : ℕ} (v : Fin k → Matrix (Fin 2) (Fin 2) E) (hli : LinearIndependent ℝ v)
    (hW : ∃ X ∈ Submodule.span ℝ (Set.range v), Algebra.norm ℝ (Matrix.det X) ≠ 0) :
    SigmaFinite ((((ENNReal.ofReal (Real.sqrt |(Matrix.of fun a b : Fin k =>
        Algebra.trace ℝ E (Matrix.trace (v a * v b))).det|)) •
      Measure.map (fun c : Fin k → ℝ => ∑ a, c a • v a) volume).withDensity
        (fun X : Matrix (Fin 2) (Fin 2) E => (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹))) := by
  classical
  have hLapply : ∀ c : Fin k → ℝ, Fintype.linearCombination ℝ v c = ∑ a, c a • v a := fun c => by
    simp [Fintype.linearCombination_apply]
  have hinj : Function.Injective (Fintype.linearCombination ℝ v) :=
    linearIndependent_iff_injective_fintypeLinearCombination.mp hli
  have hce : Topology.IsClosedEmbedding (Fintype.linearCombination ℝ v) :=
    LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hinj)
  have hemb : MeasurableEmbedding (fun c : Fin k → ℝ => ∑ a, c a • v a) := by
    have : (fun c : Fin k → ℝ => ∑ a, c a • v a) = Fintype.linearCombination ℝ v := funext fun c => (hLapply c).symm
    rw [this]; exact hce.measurableEmbedding
  haveI : SigmaFinite (Measure.map (fun c : Fin k → ℝ => ∑ a, c a • v a) volume) := hemb.sigmaFinite_map
  haveI : SigmaFinite ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun a b : Fin k =>
        Algebra.trace ℝ E (Matrix.trace (v a * v b))).det|)) •
      Measure.map (fun c : Fin k → ℝ => ∑ a, c a • v a) volume) :=
    (inferInstance : SigmaFinite ((Real.toNNReal _) • Measure.map (fun c : Fin k → ℝ => ∑ a, c a • v a) volume))
  refine SigmaFinite.withDensity_of_ne_top ?_
  refine Measure.ae_smul_measure ?_ _
  rw [ae_map_iff (p := fun X => (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹ ≠ ∞) hemb.measurable.aemeasurable
    ((measurable_density E) (MeasurableSet.compl (measurableSet_singleton _)))]
  obtain ⟨P, hP⟩ := Algebra.exists_mvPolynomial_forall_eval_eq_norm_det_sum_smul E (Fin 2) k v
  have hP0 : P ≠ 0 := by
    obtain ⟨X, hX, hN⟩ := hW
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hX
    intro h
    apply hN
    rw [← hP c, h, map_zero]
  have hnull := MeasureTheory.volume_setOf_mvPolynomial_eval_eq_zero P hP0
  rw [ae_iff]
  refine measure_mono_null (fun c hc => ?_) hnull
  simp only [Set.mem_setOf_eq, ne_eq, ENNReal.inv_eq_top, ENNReal.ofReal_eq_zero, not_le, abs_pos, not_not] at hc
  show MvPolynomial.eval c P = 0
  rw [hP c]; exact hc

end Generic
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.FDTEF P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CasmGram"

section Place

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

attribute [local instance] AutomorphicForm.CasmGram.algR AutomorphicForm.CasmGram.algE

theorem continuous_ringEquiv_mixedSpace_symm :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm := by
  apply continuous_pi
  intro v
  by_cases hv : InfinitePlace.IsReal v
  · have key : (fun y : mixedEmbedding.mixedSpace K => (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm y v)
        = fun y => (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm (y.1 ⟨v, hv⟩) := by
      funext y
      apply (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).injective
      rw [IsometryEquiv.apply_symm_apply]
      exact congrArg (fun z : mixedEmbedding.mixedSpace K => z.1 ⟨v, hv⟩)
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply y)
    rw [key]
    exact (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.continuous.comp
      ((continuous_apply _).comp continuous_fst)
  · have hc : InfinitePlace.IsComplex v := InfinitePlace.not_isReal_iff_isComplex.1 hv
    have key : (fun y : mixedEmbedding.mixedSpace K => (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm y v)
        = fun y => (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc).symm (y.2 ⟨v, hc⟩) := by
      funext y
      apply (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc).injective
      rw [IsometryEquiv.apply_symm_apply]
      exact congrArg (fun z : mixedEmbedding.mixedSpace K => z.2 ⟨v, hc⟩)
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply y)
    rw [key]
    exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc).symm.continuous.comp
      ((continuous_apply _).comp continuous_snd)

theorem continuous_algebraMap_R : Continuous (algebraMap ℝ (InfiniteAdeleRing K)) :=
  (continuous_ringEquiv_mixedSpace_symm K).comp (continuous_algebraMap ℝ (mixedEmbedding.mixedSpace K))

theorem continuous_algebraMap_E (w : InfinitePlace K) : Continuous (algebraMap ℝ (L ⊗[K] w.Completion)) := by
  haveI := isTopologicalRing_tensor K L w.Completion
  have : (algebraMap ℝ (L ⊗[K] w.Completion) : ℝ → L ⊗[K] w.Completion) =
      fun r => algebraMap w.Completion (L ⊗[K] w.Completion) (algebraMap ℝ (InfiniteAdeleRing K) r w) := rfl
  rw [this]
  exact (IsModuleTopology.continuous_of_linearMap (Algebra.linearMap w.Completion (L ⊗[K] w.Completion))).comp
    ((continuous_apply w).comp (continuous_algebraMap_R K))

scoped instance instTopRingE (w : InfinitePlace K) : IsTopologicalRing (L ⊗[K] w.Completion) :=
  isTopologicalRing_tensor K L w.Completion

scoped instance instT2E (w : InfinitePlace K) : T2Space (L ⊗[K] w.Completion) := t2Space_tensor K L w.Completion

scoped instance continuousSMul_E (w : InfinitePlace K) : ContinuousSMul ℝ (L ⊗[K] w.Completion) := by
  refine ⟨?_⟩
  have : (fun p : ℝ × (L ⊗[K] w.Completion) => p.1 • p.2) =
      fun p => algebraMap ℝ (L ⊗[K] w.Completion) p.1 * p.2 := by
    funext p; exact Algebra.smul_def p.1 p.2
  rw [this]
  exact ((continuous_algebraMap_E K L w).comp continuous_fst).mul continuous_snd

theorem moduleFinite_E (w : InfinitePlace K) : Module.Finite ℝ (L ⊗[K] w.Completion) := by
  classical
  letI : Algebra ℝ w.Completion := AutomorphicForm.CasmGram.algKw K w

  let eM : InfiniteAdeleRing K ≃ₐ[ℝ] mixedEmbedding.mixedSpace K :=
    AlgEquiv.ofRingEquiv (f := InfiniteAdeleRing.ringEquiv_mixedSpace K) fun r => by
      show InfiniteAdeleRing.ringEquiv_mixedSpace K
          ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (algebraMap ℝ (mixedEmbedding.mixedSpace K) r)) = _
      exact RingEquiv.apply_symm_apply _ _
  haveI : Module.Finite ℝ (InfiniteAdeleRing K) := Module.Finite.equiv eM.symm.toLinearEquiv

  let ev : InfiniteAdeleRing K →ₗ[ℝ] w.Completion :=
    { toFun := fun a => a w
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  haveI : Module.Finite ℝ w.Completion := by
    refine Module.Finite.of_surjective ev fun y => ?_
    refine ⟨@id (InfiniteAdeleRing K) (Pi.single w y), ?_⟩
    exact Pi.single_eq_same w y
  haveI : IsScalarTower ℝ w.Completion (L ⊗[K] w.Completion) :=
    IsScalarTower.of_algebraMap_eq (R := ℝ) (S := w.Completion) (A := L ⊗[K] w.Completion) fun _ => rfl
  exact Module.Finite.trans w.Completion (L ⊗[K] w.Completion)

end Place
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.FDTEF P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CasmGram"

end P2mGramSide
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.FDTEF P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CasmGram P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.P2mGramSide"

end
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.FDTEF P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CasmGram P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.P2mGramSide"

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "isTopologicalRing_tensor t2Space_tensor locallyCompactSpace_tensor isTopologicalGroup_tensorGL t2Space_tensorGL locallyCompactSpace_tensorGL glBorelOf borelSpace_glBorelOf centralizerBorel toTensorGL sigmaTensor sigmaGL normString IsSigmaConjugate IsNormConjugator IsNormOf twistedCentralizer twistedCentralizerBorel IsSectionFnOn IsOrbitalIntegralOn IsTwistedSectionFnOn IsTwistedOrbitalIntegralOn Coupled AreMatchingOn archHaarK archHaarL archIdent archIdentGL AreMatchingArch IsRegularSemisimple archEntries_apply IsArchTestFactor sigmaCentralizer mem_sigmaCentralizer_iff SplitPlace.psi SplitPlace.psiEquiv SplitPlace.psiEquiv_apply SplitPlace.psiEquiv_symm_const SplitPlace.psiGL exists_mulEquiv_generalLinearGroup_tensorProduct_infiniteAdeleRing_pi exists_ringEquiv_tensorProduct_infiniteAdeleRing_pi_forall_tmul archIdent_tmul_apply exists_continuous_isSectionFnOn_and_isOrbitalIntegralOn_iff_completion_of_isRegularSemisimple exists_isTwistedSectionFnOn_and_continuous_completion_of_isRegularSemisimple_normString exists_isTwistedSectionFnOn_and_continuous_completion_of_isSigmaConjugate_scalar_of_prime semilocal_central_transfer_of_forall_oneplace_of_referenceMeasures exists_isNormConjugator_and_coupled_of_gram_of_algHom_real exists_isNormConjugator_and_coupled_of_gram_of_algHom_complex exists_isNormConjugator_and_coupled_of_gram_conjAe_of_pos isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar map_centralizer_map_ringEquiv_pi_eq_smul_gram_of_infiniteAdeleRing map_twistedCentralizer_map_ringEquiv_pi_eq_smul_gram_of_infiniteAdeleRing mem_span_map_ringEquiv_pi_iff_of_span_eq_range_includeRight mem_span_map_ringEquiv_pi_iff_of_span_eq_setOf_mul_eq_mul_map_sigmaTensor exists_gram_map_of_ringEquiv_of_exists_gram exists_ringEquiv_tensor_completion_complex_of_isRamified isTwistedOrbitalIntegralOn_map_of_ringEquiv_and_isHaarMeasure_map isNormConjugator_map_iff_and_coupled_map_iff_of_ringEquiv isOrbitalIntegralOn_map_generalLinearGroup_map_of_ringEquiv isHaarMeasure_map_and_exists_isHaarMeasure_centralizer_of_ringEquiv pos_and_exists_coupled_toTensorGL_scalar_one_iff_of_coupled_scalar_conjAe exists_ringEquiv_tensor_baseChange_of_ringEquiv isOrbitalIntegralOn_scalar_neg_of_isTwistedOrbitalIntegralOn_conjAe_of_gram_of_nhds_forall_isNormConjugator_of_neg exists_isSigmaConjugate_scalar_of_isNormConjugator_scalar_of_algHom_of_prime exists_isTwistedSectionFnOn_and_continuous_completion_of_not_isSigmaConjugate_scalar_of_finrank_eq_two exists_isSigmaConjugate_scalar_conjAe_iff_pos_of_isNormConjugator_scalar"
namespace CasmGram
p2m_open "AutomorphicForm"

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

attribute [local instance] algR algE

theorem moduleFinite_tensor_completion (w : InfinitePlace K) : Module.Finite ℝ (L ⊗[K] w.Completion) :=
  P2mGramSide.moduleFinite_E K L w

theorem sigmaFinite_m (w : InfinitePlace K) : SigmaFinite (m K L w) := by
  classical
  haveI := moduleFinite_tensor_completion K L w
  unfold m
  split_ifs with h
  · obtain ⟨hli, hspan⟩ := h.choose_spec.choose_spec
    have hW : ∃ X ∈ Submodule.span ℝ (Set.range h.choose_spec.choose), Algebra.norm ℝ (Matrix.det X) ≠ 0 := by
      refine ⟨1, ?_, ?_⟩
      · rw [hspan, WK]
        apply Submodule.subset_span
        exact ⟨1, by ext i j; by_cases hij : i = j <;> simp [Matrix.one_apply, hij, Algebra.TensorProduct.one_def]⟩
      · rw [Matrix.det_one, map_one]; exact one_ne_zero
    exact P2mGramSide.sigmaFinite_gramWD (L ⊗[K] w.Completion) _ hli hW
  · infer_instance

theorem sigmaFinite_m' (σ : L ≃ₐ[K] L) (c : (InfiniteAdeleRing K)ˣ) (w : InfinitePlace K)
    (δ' : GL (Fin 2) (L ⊗[K] w.Completion)) : SigmaFinite (m' K L σ c w δ') := by
  classical
  haveI := moduleFinite_tensor_completion K L w
  unfold m'
  split_ifs with h1 h
  · obtain ⟨hli, hspan⟩ := h.choose_spec.choose_spec
    have hW : ∃ X ∈ Submodule.span ℝ (Set.range h.choose_spec.choose), Algebra.norm ℝ (Matrix.det X) ≠ 0 := by
      refine ⟨1, ?_, ?_⟩
      · rw [hspan, WL]
        apply Submodule.subset_span
        show (1 : Matrix (Fin 2) (Fin 2) (L ⊗[K] w.Completion)) * _ = _ * (1 : Matrix _ _ _).map _
        rw [Matrix.map_one (sigmaTensor K L w.Completion σ) (map_zero _) (map_one _), one_mul, mul_one]
      · rw [Matrix.det_one, map_one]; exact one_ne_zero
    exact P2mGramSide.sigmaFinite_gramWD (L ⊗[K] w.Completion) _ hli hW
  · infer_instance
  · infer_instance

end AutomorphicForm.CasmGram
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.FDTEF P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CasmGram P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.P2mGramSide"
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.FDTEF P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CasmGram P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.P2mGramSide"

end
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.FDTEF P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CasmGram P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.P2mGramSide"

namespace AutomorphicForm
p2m_export "AutomorphicForm" "isTopologicalRing_tensor t2Space_tensor locallyCompactSpace_tensor isTopologicalGroup_tensorGL t2Space_tensorGL locallyCompactSpace_tensorGL glBorelOf borelSpace_glBorelOf centralizerBorel toTensorGL sigmaTensor sigmaGL normString IsSigmaConjugate IsNormConjugator IsNormOf twistedCentralizer twistedCentralizerBorel IsSectionFnOn IsOrbitalIntegralOn IsTwistedSectionFnOn IsTwistedOrbitalIntegralOn Coupled AreMatchingOn archHaarK archHaarL archIdent archIdentGL AreMatchingArch IsRegularSemisimple archEntries_apply IsArchTestFactor sigmaCentralizer mem_sigmaCentralizer_iff SplitPlace.psi SplitPlace.psiEquiv SplitPlace.psiEquiv_apply SplitPlace.psiEquiv_symm_const SplitPlace.psiGL exists_mulEquiv_generalLinearGroup_tensorProduct_infiniteAdeleRing_pi exists_ringEquiv_tensorProduct_infiniteAdeleRing_pi_forall_tmul archIdent_tmul_apply exists_continuous_isSectionFnOn_and_isOrbitalIntegralOn_iff_completion_of_isRegularSemisimple exists_isTwistedSectionFnOn_and_continuous_completion_of_isRegularSemisimple_normString exists_isTwistedSectionFnOn_and_continuous_completion_of_isSigmaConjugate_scalar_of_prime semilocal_central_transfer_of_forall_oneplace_of_referenceMeasures exists_isNormConjugator_and_coupled_of_gram_of_algHom_real exists_isNormConjugator_and_coupled_of_gram_of_algHom_complex exists_isNormConjugator_and_coupled_of_gram_conjAe_of_pos isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar map_centralizer_map_ringEquiv_pi_eq_smul_gram_of_infiniteAdeleRing map_twistedCentralizer_map_ringEquiv_pi_eq_smul_gram_of_infiniteAdeleRing mem_span_map_ringEquiv_pi_iff_of_span_eq_range_includeRight mem_span_map_ringEquiv_pi_iff_of_span_eq_setOf_mul_eq_mul_map_sigmaTensor exists_gram_map_of_ringEquiv_of_exists_gram exists_ringEquiv_tensor_completion_complex_of_isRamified isTwistedOrbitalIntegralOn_map_of_ringEquiv_and_isHaarMeasure_map isNormConjugator_map_iff_and_coupled_map_iff_of_ringEquiv isOrbitalIntegralOn_map_generalLinearGroup_map_of_ringEquiv isHaarMeasure_map_and_exists_isHaarMeasure_centralizer_of_ringEquiv pos_and_exists_coupled_toTensorGL_scalar_one_iff_of_coupled_scalar_conjAe exists_ringEquiv_tensor_baseChange_of_ringEquiv isOrbitalIntegralOn_scalar_neg_of_isTwistedOrbitalIntegralOn_conjAe_of_gram_of_nhds_forall_isNormConjugator_of_neg exists_isSigmaConjugate_scalar_of_isNormConjugator_scalar_of_algHom_of_prime exists_isTwistedSectionFnOn_and_continuous_completion_of_not_isSigmaConjugate_scalar_of_finrank_eq_two exists_isSigmaConjugate_scalar_conjAe_iff_pos_of_isNormConjugator_scalar"
namespace CasmGram
p2m_open "AutomorphicForm"

open FDTEF
open scoped NNReal

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

attribute [local instance] algR algE

theorem continuous_ringEquiv_mixedSpace_symm :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm := by
  apply continuous_pi
  intro v
  by_cases hv : InfinitePlace.IsReal v
  · have key : (fun y : mixedEmbedding.mixedSpace K => (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm y v)
        = fun y => (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm (y.1 ⟨v, hv⟩) := by
      funext y
      apply (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).injective
      rw [IsometryEquiv.apply_symm_apply]
      exact congrArg (fun z : mixedEmbedding.mixedSpace K => z.1 ⟨v, hv⟩)
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply y)
    rw [key]
    exact (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.continuous.comp
      ((continuous_apply _).comp continuous_fst)
  · have hc : InfinitePlace.IsComplex v := InfinitePlace.not_isReal_iff_isComplex.1 hv
    have key : (fun y : mixedEmbedding.mixedSpace K => (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm y v)
        = fun y => (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc).symm (y.2 ⟨v, hc⟩) := by
      funext y
      apply (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc).injective
      rw [IsometryEquiv.apply_symm_apply]
      exact congrArg (fun z : mixedEmbedding.mixedSpace K => z.2 ⟨v, hc⟩)
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply y)
    rw [key]
    exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc).symm.continuous.comp
      ((continuous_apply _).comp continuous_snd)

theorem continuous_algebraMap_R : Continuous (algebraMap ℝ (InfiniteAdeleRing K)) :=
  (continuous_ringEquiv_mixedSpace_symm K).comp (continuous_algebraMap ℝ (mixedEmbedding.mixedSpace K))

theorem continuous_algebraMap_Kw (w : InfinitePlace K) :
    Continuous (@algebraMap ℝ w.Completion _ _ (algKw K w)) := by
  have : (@algebraMap ℝ w.Completion _ _ (algKw K w) : ℝ → w.Completion) =
      fun r => algebraMap ℝ (InfiniteAdeleRing K) r w := rfl
  rw [this]
  exact (continuous_apply w).comp (continuous_algebraMap_R K)

theorem continuous_algebraMap_right_w (w : InfinitePlace K) :
    Continuous (algebraMap w.Completion (L ⊗[K] w.Completion)) := by
  haveI := isTopologicalRing_tensor K L w.Completion
  exact IsModuleTopology.continuous_of_linearMap (Algebra.linearMap w.Completion (L ⊗[K] w.Completion))

theorem continuous_algebraMap_E (w : InfinitePlace K) : Continuous (algebraMap ℝ (L ⊗[K] w.Completion)) := by
  have : (algebraMap ℝ (L ⊗[K] w.Completion) : ℝ → L ⊗[K] w.Completion) =
      fun r => algebraMap w.Completion (L ⊗[K] w.Completion) (@algebraMap ℝ w.Completion _ _ (algKw K w) r) := rfl
  rw [this]
  exact (continuous_algebraMap_right_w K L w).comp (continuous_algebraMap_Kw K w)

theorem continuousSMul_E (w : InfinitePlace K) : ContinuousSMul ℝ (L ⊗[K] w.Completion) := by
  haveI := isTopologicalRing_tensor K L w.Completion
  refine ⟨?_⟩
  have : (fun p : ℝ × (L ⊗[K] w.Completion) => p.1 • p.2) =
      fun p => algebraMap ℝ (L ⊗[K] w.Completion) p.1 * p.2 := by
    funext p; exact Algebra.smul_def p.1 p.2
  rw [this]
  exact ((continuous_algebraMap_E K L w).comp continuous_fst).mul continuous_snd

theorem exists_basis_of_submodule (w : InfinitePlace K) [Module.Finite ℝ (L ⊗[K] w.Completion)]
    (W : Submodule ℝ (V K L w)) :
    ∃ (n : ℕ) (b : Fin n → V K L w), LinearIndependent ℝ b ∧ Submodule.span ℝ (Set.range b) = W := by
  haveI h1 : Module.Finite ℝ (Fin 2 → L ⊗[K] w.Completion) := Module.Finite.pi
  haveI h2 : Module.Finite ℝ (Fin 2 → Fin 2 → L ⊗[K] w.Completion) := Module.Finite.pi
  haveI : Module.Finite ℝ (V K L w) := h2
  haveI : Module.Finite ℝ W := FiniteDimensional.finiteDimensional_submodule W
  let b := Module.finBasis ℝ W
  refine ⟨_, fun a => (b a : V K L w), ?_, ?_⟩
  · exact b.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  · show Submodule.span ℝ (Set.range (W.subtype ∘ b)) = W
    rw [Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]

set_option maxHeartbeats 16000000 in
theorem hrel_of_hnorm (σ : L ≃ₐ[K] L) (c : (InfiniteAdeleRing K)ˣ)
    (δ y : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
    (hδ : AutomorphicForm.IsNormConjugator K L (InfiniteAdeleRing K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y)
    (τ : @Measure (Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) (InfiniteAdeleRing K))))
      (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ))
    (hnorm :
      letI : Algebra ℝ (InfiniteAdeleRing K) :=
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
          (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
      letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
        ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
          (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
      letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := borel _
      letI := AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (Matrix.GeneralLinearGroup.scalar (Fin 2) c)
      letI := AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ
      ∃ (n₁ n₂ : ℕ) (e₁ : Fin n₁ → Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
        (e₂ : Fin n₂ → Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (s : ENNReal),
        s ≠ 0 ∧ s ≠ ⊤ ∧
        LinearIndependent ℝ e₁ ∧
          (Submodule.span ℝ (Set.range e₁) : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) =
            Set.range (fun Y : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K) =>
              Y.map (Algebra.TensorProduct.includeRight :
                InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K)) ∧
        LinearIndependent ℝ e₂ ∧
          (Submodule.span ℝ (Set.range e₂) : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) =
            {X | X * (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) =
              (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) *
                X.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ)} ∧
        Measure.map (fun t : ↥(Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) (InfiniteAdeleRing K)))) =>
            ((t : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)).map
              (Algebra.TensorProduct.includeRight :
                InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K)) τ =
          s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₁ =>
                  Algebra.trace ℝ (L ⊗[K] InfiniteAdeleRing K) (Matrix.trace (e₁ i * e₁ j))).det|)) •
                Measure.map (fun c : Fin n₁ → ℝ => ∑ i, c i • e₁ i) volume).withDensity
              (fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
                (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹) ∧
        Measure.map (fun t : ↥(AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ) =>
            ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) τ' =
          s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
                  Algebra.trace ℝ (L ⊗[K] InfiniteAdeleRing K) (Matrix.trace (e₂ i * e₂ j))).det|)) •
                Measure.map (fun c : Fin n₂ → ℝ => ∑ i, c i • e₂ i) volume).withDensity
              (fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
                (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹)) :
    ∀ (Ξ : L ⊗[K] InfiniteAdeleRing K ≃+* ((v : InfinitePlace K) → L ⊗[K] v.Completion))
        (Θ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) ≃ₜ* ((v : InfinitePlace K) → GL (Fin 2) (L ⊗[K] v.Completion))),
        Continuous Ξ → Continuous Ξ.symm →
        (∀ (x : L) (a : InfiniteAdeleRing K) (v : InfinitePlace K), Ξ (x ⊗ₜ a) v = x ⊗ₜ (a v)) →
        (∀ (g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (v : InfinitePlace K),
          Θ g v = Matrix.GeneralLinearGroup.map
            ((Pi.evalRingHom (fun v : InfinitePlace K => L ⊗[K] v.Completion) v).comp Ξ.toRingHom) g) →
        (∀ (g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (v : InfinitePlace K),
          Θ (sigmaGL K L (InfiniteAdeleRing K) σ g) v = sigmaGL K L v.Completion σ (Θ g v)) →
        (∀ (g : GL (Fin 2) (InfiniteAdeleRing K)) (v : InfinitePlace K),
          Θ (toTensorGL K L (InfiniteAdeleRing K) g) v = toTensorGL K L v.Completion (FDTEF.thetaK K g v)) →
        ∃ s : ℝ≥0, s ≠ 0 ∧
          @Measure.map _ _ (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (Matrix.GeneralLinearGroup.scalar (Fin 2) c))
              MeasurableSpace.pi
              (fun t : Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) (InfiniteAdeleRing K))) =>
                fun i : InfinitePlace K => AutomorphicForm.CasmGram.κ K L i (FDTEF.thetaK K (t : GL (Fin 2) (InfiniteAdeleRing K)) i)) τ =
            s • Measure.pi (AutomorphicForm.CasmGram.m K L) ∧
          @Measure.map _ _ (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ) MeasurableSpace.pi
              (fun t : AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ =>
                fun i : InfinitePlace K => AutomorphicForm.CasmGram.κ' K L i (Θ (t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) i)) τ' =
            s • Measure.pi (fun i : InfinitePlace K => AutomorphicForm.CasmGram.m' K L σ c i (Θ δ i)) := by
  classical
  intro Ξ Θ hΞ hΞ' hΞt hΘapp hΘσ hΘι
  obtain ⟨n₁, n₂, e₁, e₂, s, hs0, hstop, hli₁, hsp₁, hli₂, hsp₂, hμ₁, hμ₂⟩ := hnorm

  let E : InfinitePlace K → Type := fun w => L ⊗[K] w.Completion
  haveI hTR : ∀ w : InfinitePlace K, IsTopologicalRing (E w) := fun w => isTopologicalRing_tensor K L _
  haveI hT2 : ∀ w : InfinitePlace K, T2Space (E w) := fun w => t2Space_tensor K L _

  have hΞr : ∀ (r : ℝ) (z : L ⊗[K] InfiniteAdeleRing K),
      (letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
        ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
          (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
       Ξ (r • z) = r • Ξ z) := by
    intro r z
    letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
      ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
        (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
    rw [Algebra.smul_def, map_mul]
    funext w
    rw [Pi.mul_apply, Pi.smul_apply, Algebra.smul_def]
    congr 1
    change Ξ ((1 : L) ⊗ₜ[K] (algebraMap ℝ (InfiniteAdeleRing K) r)) w = (1 : L) ⊗ₜ[K] (algebraMap ℝ (InfiniteAdeleRing K) r w)
    rw [hΞt]

  have hK := AutomorphicForm.map_centralizer_map_ringEquiv_pi_eq_smul_gram_of_infiniteAdeleRing K L Ξ hΞ hΞ' hΞr
    (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ n₁ e₁ s hμ₁
  have hKs := AutomorphicForm.mem_span_map_ringEquiv_pi_iff_of_span_eq_range_includeRight K L Ξ hΞt hΞr
    n₁ e₁ ⟨hli₁, hsp₁⟩
  have hL := AutomorphicForm.map_twistedCentralizer_map_ringEquiv_pi_eq_smul_gram_of_infiniteAdeleRing K L σ Ξ hΞ hΞ'
    hΞr δ τ' n₂ e₂ s hμ₂
  have hδw : ∀ (w : InfinitePlace K) (i j : Fin 2),
      Ξ ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) i j) w =
        ((Θ δ w : GL (Fin 2) (L ⊗[K] w.Completion)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] w.Completion)) i j := by
    intro w i j
    rw [hΘapp]
    rfl
  have hLs := AutomorphicForm.mem_span_map_ringEquiv_pi_iff_of_span_eq_setOf_mul_eq_mul_map_sigmaTensor K L σ Ξ
    hΞt hΞr (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
    (fun w => ((Θ δ w : GL (Fin 2) (L ⊗[K] w.Completion)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] w.Completion))) hδw
    n₂ e₂ ⟨hli₂, hsp₂⟩

  haveI hMF : ∀ w : InfinitePlace K, Module.Finite ℝ (L ⊗[K] w.Completion) := fun w => moduleFinite_tensor_completion K L w
  haveI hFree : ∀ w : InfinitePlace K, Module.Free ℝ (L ⊗[K] w.Completion) := fun w => Module.Free.of_divisionRing ℝ _
  haveI hCS : ∀ w : InfinitePlace K, ContinuousSMul ℝ (L ⊗[K] w.Completion) := fun w => continuousSMul_E K L w
  letI mPi : MeasurableSpace (Matrix (Fin 2) (Fin 2) ((w : InfinitePlace K) → L ⊗[K] w.Completion)) := borel _
  haveI bPi : BorelSpace (Matrix (Fin 2) (Fin 2) ((w : InfinitePlace K) → L ⊗[K] w.Completion)) := ⟨rfl⟩

  have hΛm : Measurable (fun (X : Matrix (Fin 2) (Fin 2) ((w : InfinitePlace K) → L ⊗[K] w.Completion))
      (i : InfinitePlace K) => X.map (Pi.evalRingHom (fun w : InfinitePlace K => L ⊗[K] w.Completion) i)) := by
    refine measurable_pi_lambda _ fun i => ?_
    exact (continuous_id.matrix_map (continuous_apply i)).measurable

  have hexK : ∀ i : InfinitePlace K, ∃ (n : ℕ) (b : Fin n → V K L i),
      LinearIndependent ℝ b ∧ Submodule.span ℝ (Set.range b) = WK K L i :=
    fun i => exists_basis_of_submodule K L i (WK K L i)
  have hexL : ∀ i : InfinitePlace K, ∃ (n : ℕ) (b : Fin n → V K L i),
      LinearIndependent ℝ b ∧ Submodule.span ℝ (Set.range b) =
        WL K L σ i ((Θ δ i : GL (Fin 2) (L ⊗[K] i.Completion)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] i.Completion)) :=
    fun i => exists_basis_of_submodule K L i _

  have hWK : ∀ i : InfinitePlace K, ∃ X ∈ WK K L i, Algebra.norm ℝ (Matrix.det X) ≠ 0 := by
    intro i
    refine ⟨1, Submodule.subset_span ⟨1, ?_⟩, by rw [Matrix.det_one, map_one]; exact one_ne_zero⟩
    ext j k
    by_cases hjk : j = k
    · subst hjk; simp [Algebra.TensorProduct.one_def]
    · simp [hjk]
  have hWL : ∀ i : InfinitePlace K, ∃ X ∈ WL K L σ i ((Θ δ i : GL (Fin 2) (L ⊗[K] i.Completion)) :
      Matrix (Fin 2) (Fin 2) (L ⊗[K] i.Completion)), Algebra.norm ℝ (Matrix.det X) ≠ 0 := by
    intro i
    refine ⟨1, Submodule.subset_span ?_, by rw [Matrix.det_one, map_one]; exact one_ne_zero⟩
    show (1 : Matrix (Fin 2) (Fin 2) (L ⊗[K] i.Completion)) * _ = _ * (1 : Matrix (Fin 2) (Fin 2) (L ⊗[K] i.Completion)).map _
    rw [Matrix.map_one _ (map_zero _) (map_one _), one_mul, mul_one]

  have hαK := MeasureTheory.Measure.map_withDensity_gram_trace_matrix_pi_eq_pi_of_span_eq
    (E := fun w : InfinitePlace K => L ⊗[K] w.Completion) (W := fun i => WK K L i)
    (n := fun i => (hexK i).choose) (e := fun i => (hexK i).choose_spec.choose)
    (he := fun i => (hexK i).choose_spec.choose_spec) (hW := hWK)
    (W' := Submodule.span ℝ (Set.range fun a => (e₁ a).map Ξ)) (hW' := hKs.2) (N := n₁)
    (f := fun a => (e₁ a).map Ξ) (hf := ⟨hKs.1, rfl⟩)
  have hαL := MeasureTheory.Measure.map_withDensity_gram_trace_matrix_pi_eq_pi_of_span_eq
    (E := fun w : InfinitePlace K => L ⊗[K] w.Completion)
    (W := fun i => WL K L σ i ((Θ δ i : GL (Fin 2) (L ⊗[K] i.Completion)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] i.Completion)))
    (n := fun i => (hexL i).choose) (e := fun i => (hexL i).choose_spec.choose)
    (he := fun i => (hexL i).choose_spec.choose_spec) (hW := hWL)
    (W' := Submodule.span ℝ (Set.range fun a => (e₂ a).map Ξ)) (hW' := hLs.2) (N := n₂)
    (f := fun a => (e₂ a).map Ξ) (hf := ⟨hLs.1, rfl⟩)

  have hmK : (fun i : InfinitePlace K => gramWD K L i (hexK i).choose (hexK i).choose_spec.choose) = m K L := by
    funext i; rw [m, dif_pos (hexK i)]
  have hcent : ∀ i : InfinitePlace K, ∃ y' : GL (Fin 2) (L ⊗[K] i.Completion),
      AutomorphicForm.IsNormConjugator K L i.Completion σ
        (Matrix.GeneralLinearGroup.scalar (Fin 2) (FDTEF.unitAt K c i)) (Θ δ i) y' := by
    intro i
    refine ⟨Θ y i, ?_⟩
    have h := (FDTEF.isNormConjugator_iff_forall K L σ Θ.toMulEquiv hΘσ hΘι
      (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y).1 hδ i
    rwa [FDTEF.thetaK_scalar] at h
  have hmL : (fun i : InfinitePlace K => gramWD K L i (hexL i).choose (hexL i).choose_spec.choose) =
      fun i => m' K L σ c i (Θ δ i) := by
    funext i; rw [m', if_pos (hcent i), dif_pos (hexL i)]

  have hfunK : (fun t : Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) (InfiniteAdeleRing K))) =>
        fun i : InfinitePlace K => κ K L i (FDTEF.thetaK K (t : GL (Fin 2) (InfiniteAdeleRing K)) i)) =
      (fun (X : Matrix (Fin 2) (Fin 2) ((w : InfinitePlace K) → L ⊗[K] w.Completion)) (i : InfinitePlace K) =>
        X.map (Pi.evalRingHom (fun w : InfinitePlace K => L ⊗[K] w.Completion) i)) ∘
      (fun t : Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) (InfiniteAdeleRing K))) =>
        ((t : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)).map
          (fun x : InfiniteAdeleRing K => Ξ ((1 : L) ⊗ₜ[K] x))) := by
    funext t; funext i; ext j k
    simp only [Function.comp_apply, κ, Matrix.map_apply, Pi.evalRingHom_apply]
    rw [hΞt]
    rfl
  have hfunL : (fun t : AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ =>
        fun i : InfinitePlace K => κ' K L i (Θ (t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) i)) =
      (fun (X : Matrix (Fin 2) (Fin 2) ((w : InfinitePlace K) → L ⊗[K] w.Completion)) (i : InfinitePlace K) =>
        X.map (Pi.evalRingHom (fun w : InfinitePlace K => L ⊗[K] w.Completion) i)) ∘
      (fun t : AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ =>
        (((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))).map Ξ) := by
    funext t; funext i; ext j k
    simp only [Function.comp_apply, κ', Matrix.map_apply, Pi.evalRingHom_apply]
    rw [hΘapp]
    rfl

  have hcontK : Continuous (fun t : Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) (InfiniteAdeleRing K))) =>
        ((t : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)).map
          (fun x : InfiniteAdeleRing K => Ξ ((1 : L) ⊗ₜ[K] x))) := by
    have h1 : Continuous (fun x : InfiniteAdeleRing K => Ξ ((1 : L) ⊗ₜ[K] x)) := by
      have h0 : Continuous (algebraMap (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K)) :=
        IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K))
      exact hΞ.comp h0
    exact (Units.continuous_val.comp continuous_subtype_val).matrix_map h1
  have hcontL : Continuous (fun t : AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ =>
        (((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))).map Ξ) :=
    (Units.continuous_val.comp continuous_subtype_val).matrix_map hΞ
  have hsNN : ((s.toNNReal : ℝ≥0) : ENNReal) = s := ENNReal.coe_toNNReal hstop
  refine ⟨s.toNNReal, ?_, ?_, ?_⟩
  · intro h0
    rcases (ENNReal.toNNReal_eq_zero_iff s).1 h0 with h | h
    · exact hs0 h
    · exact hstop h
  ·
    letI := AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (Matrix.GeneralLinearGroup.scalar (Fin 2) c)
    haveI : BorelSpace (Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) (InfiniteAdeleRing K)))) := ⟨rfl⟩
    have goalK : s • Measure.pi (fun i : InfinitePlace K => gramWD K L i (hexK i).choose (hexK i).choose_spec.choose) =
        s.toNNReal • Measure.pi (m K L) := by
      rw [hmK, ENNReal.smul_def, hsNN]
    rw [hfunK, ← Measure.map_map hΛm hcontK.measurable, hK, Measure.map_smul, hαK]
    exact goalK
  ·
    letI := AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ
    haveI : BorelSpace (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ) := ⟨rfl⟩
    have goalL : s • Measure.pi (fun i : InfinitePlace K => gramWD K L i (hexL i).choose (hexL i).choose_spec.choose) =
        s.toNNReal • Measure.pi (fun i : InfinitePlace K => m' K L σ c i (Θ δ i)) := by
      rw [hmL, ENNReal.smul_def, hsNN]
    rw [hfunL, ← Measure.map_map hΛm hcontL.measurable, hL, Measure.map_smul, hαL]
    exact goalL

end AutomorphicForm.CasmGram
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.FDTEF P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CasmGram P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.P2mGramSide"
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.FDTEF P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CasmGram P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.P2mGramSide"

set_option autoImplicit false

set_option autoImplicit false

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "isTopologicalRing_tensor t2Space_tensor locallyCompactSpace_tensor isTopologicalGroup_tensorGL t2Space_tensorGL locallyCompactSpace_tensorGL glBorelOf borelSpace_glBorelOf centralizerBorel toTensorGL sigmaTensor sigmaGL normString IsSigmaConjugate IsNormConjugator IsNormOf twistedCentralizer twistedCentralizerBorel IsSectionFnOn IsOrbitalIntegralOn IsTwistedSectionFnOn IsTwistedOrbitalIntegralOn Coupled AreMatchingOn archHaarK archHaarL archIdent archIdentGL AreMatchingArch IsRegularSemisimple archEntries_apply IsArchTestFactor sigmaCentralizer mem_sigmaCentralizer_iff SplitPlace.psi SplitPlace.psiEquiv SplitPlace.psiEquiv_apply SplitPlace.psiEquiv_symm_const SplitPlace.psiGL exists_mulEquiv_generalLinearGroup_tensorProduct_infiniteAdeleRing_pi exists_ringEquiv_tensorProduct_infiniteAdeleRing_pi_forall_tmul archIdent_tmul_apply exists_continuous_isSectionFnOn_and_isOrbitalIntegralOn_iff_completion_of_isRegularSemisimple exists_isTwistedSectionFnOn_and_continuous_completion_of_isRegularSemisimple_normString exists_isTwistedSectionFnOn_and_continuous_completion_of_isSigmaConjugate_scalar_of_prime semilocal_central_transfer_of_forall_oneplace_of_referenceMeasures exists_isNormConjugator_and_coupled_of_gram_of_algHom_real exists_isNormConjugator_and_coupled_of_gram_of_algHom_complex exists_isNormConjugator_and_coupled_of_gram_conjAe_of_pos isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar map_centralizer_map_ringEquiv_pi_eq_smul_gram_of_infiniteAdeleRing map_twistedCentralizer_map_ringEquiv_pi_eq_smul_gram_of_infiniteAdeleRing mem_span_map_ringEquiv_pi_iff_of_span_eq_range_includeRight mem_span_map_ringEquiv_pi_iff_of_span_eq_setOf_mul_eq_mul_map_sigmaTensor exists_gram_map_of_ringEquiv_of_exists_gram exists_ringEquiv_tensor_completion_complex_of_isRamified isTwistedOrbitalIntegralOn_map_of_ringEquiv_and_isHaarMeasure_map isNormConjugator_map_iff_and_coupled_map_iff_of_ringEquiv isOrbitalIntegralOn_map_generalLinearGroup_map_of_ringEquiv isHaarMeasure_map_and_exists_isHaarMeasure_centralizer_of_ringEquiv pos_and_exists_coupled_toTensorGL_scalar_one_iff_of_coupled_scalar_conjAe exists_ringEquiv_tensor_baseChange_of_ringEquiv isOrbitalIntegralOn_scalar_neg_of_isTwistedOrbitalIntegralOn_conjAe_of_gram_of_nhds_forall_isNormConjugator_of_neg exists_isSigmaConjugate_scalar_of_isNormConjugator_scalar_of_algHom_of_prime exists_isTwistedSectionFnOn_and_continuous_completion_of_not_isSigmaConjugate_scalar_of_finrank_eq_two exists_isSigmaConjugate_scalar_conjAe_iff_pos_of_isNormConjugator_scalar"
namespace CentAsmLocal
p2m_open "AutomorphicForm"

open MeasureTheory

section GLTransport

variable {R S : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]

attribute [local instance 10000] AutomorphicForm.glBorelOf AutomorphicForm.centralizerBorel

theorem borelSpace_centralizer (T : Type) [CommRing T] [TopologicalSpace T] (γ : GL (Fin 2) T) :
    BorelSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) T))) := ⟨rfl⟩

attribute [local instance] borelSpace_gl borelSpace_centralizer

theorem centralizer_forward_gl (e : R ≃+* S) (he : Continuous e) (he' : Continuous e.symm)
    (γ : GL (Fin 2) R) (τ : Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) R)))) (hτ : τ.IsHaarMeasure) :
    ∃ τ' : Measure (Subgroup.centralizer ({Matrix.GeneralLinearGroup.map e.toRingHom γ} : Set (GL (Fin 2) S))),
      τ'.IsHaarMeasure ∧
      Measure.map (fun t' : Subgroup.centralizer
          ({Matrix.GeneralLinearGroup.map e.toRingHom γ} : Set (GL (Fin 2) S)) => (t' : GL (Fin 2) S)) τ' =
        Measure.map (fun t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) R)) =>
          Matrix.GeneralLinearGroup.map e.toRingHom (t : GL (Fin 2) R)) τ ∧
      (τ.IsInvInvariant → τ'.IsInvInvariant) := by
  haveI := hτ
  have h := exists_isHaarMeasure_centralizer_forward (glEquiv e he he') γ τ
  simp only [glEquiv_apply] at h
  exact h

theorem centralizer_backward_gl (e : R ≃+* S) (he : Continuous e) (he' : Continuous e.symm)
    (γ : GL (Fin 2) R)
    (τ' : Measure (Subgroup.centralizer ({Matrix.GeneralLinearGroup.map e.toRingHom γ} : Set (GL (Fin 2) S))))
    (hτ' : τ'.IsHaarMeasure) :
    ∃ τ : Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) R))), τ.IsHaarMeasure ∧
      Measure.map (fun t' : Subgroup.centralizer
          ({Matrix.GeneralLinearGroup.map e.toRingHom γ} : Set (GL (Fin 2) S)) => (t' : GL (Fin 2) S)) τ' =
        Measure.map (fun t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) R)) =>
          Matrix.GeneralLinearGroup.map e.toRingHom (t : GL (Fin 2) R)) τ ∧
      (τ'.IsInvInvariant → τ.IsInvInvariant) := by
  have h := fun (τ'' : Measure (Subgroup.centralizer ({glEquiv e he he' γ} : Set (GL (Fin 2) S))))
    (h'' : τ''.IsHaarMeasure) => by
      haveI := h''
      exact exists_isHaarMeasure_centralizer_backward (glEquiv e he he') γ τ''
  simp only [glEquiv_apply] at h
  exact h τ' hτ'

end GLTransport
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.FDTEF P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CasmGram P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.P2mGramSide"

section TensorTransport

open scoped TensorProduct TensorProduct.RightActions

variable {K L A : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] (σ : L ≃ₐ[K] L)
  {K' L' A' : Type} [Field K'] [Field L'] [Algebra K' L'] [FiniteDimensional K' L']
  [CommRing A'] [Algebra K' A'] [TopologicalSpace A'] [IsTopologicalRing A'] (σ' : L' ≃ₐ[K'] L')
  (E : L ⊗[K] A ≃+* L' ⊗[K'] A') (hE : Continuous E) (hE' : Continuous E.symm)
  (hEσ : ∀ z, E (sigmaTensor K L A σ z) = sigmaTensor K' L' A' σ' (E z))

attribute [local instance 10000] AutomorphicForm.glBorelOf AutomorphicForm.twistedCentralizerBorel

theorem borelSpace_gl₂ (T : Type) [CommRing T] [TopologicalSpace T] : BorelSpace (GL (Fin 2) T) := ⟨rfl⟩

omit [TopologicalSpace A] [IsTopologicalRing A] in
theorem borelSpace_twistedCentralizer [TopologicalSpace A] (δ : GL (Fin 2) (L ⊗[K] A)) :
    BorelSpace (twistedCentralizer K L A σ δ) := ⟨rfl⟩

attribute [local instance] borelSpace_gl₂ borelSpace_twistedCentralizer

include hEσ in
omit [FiniteDimensional K L] [FiniteDimensional K' L'] [TopologicalSpace A] [IsTopologicalRing A]
  [TopologicalSpace A'] [IsTopologicalRing A'] in
theorem map_sigmaGL (x : GL (Fin 2) (L ⊗[K] A)) :
    Matrix.GeneralLinearGroup.map E.toRingHom (sigmaGL K L A σ x) =
      sigmaGL K' L' A' σ' (Matrix.GeneralLinearGroup.map E.toRingHom x) := by
  ext i j
  simp [sigmaGL, hEσ]

include hEσ in
omit [FiniteDimensional K L] [FiniteDimensional K' L'] [TopologicalSpace A] [IsTopologicalRing A]
  [TopologicalSpace A'] [IsTopologicalRing A'] in

theorem symm_sigmaTensor (z : L' ⊗[K'] A') :
    E.symm (sigmaTensor K' L' A' σ' z) = sigmaTensor K L A σ (E.symm z) := by
  apply E.injective
  rw [E.apply_symm_apply, hEσ, E.apply_symm_apply]

omit [FiniteDimensional K L] [FiniteDimensional K' L'] [TopologicalSpace A] [IsTopologicalRing A]
  [TopologicalSpace A'] [IsTopologicalRing A'] in

theorem symm_toTensorGL (e : A ≃+* A')
    (hEe : ∀ g : GL (Fin 2) A, Matrix.GeneralLinearGroup.map E.toRingHom (toTensorGL K L A g) =
      toTensorGL K' L' A' (Matrix.GeneralLinearGroup.map e.toRingHom g))
    (g' : GL (Fin 2) A') :
    Matrix.GeneralLinearGroup.map E.symm.toRingHom (toTensorGL K' L' A' g') =
      toTensorGL K L A (Matrix.GeneralLinearGroup.map e.symm.toRingHom g') := by
  have h := hEe (Matrix.GeneralLinearGroup.map e.symm.toRingHom g')
  rw [map_map_symm] at h
  rw [← h, map_symm_map]

include hEσ in
omit [FiniteDimensional K L] [FiniteDimensional K' L'] [TopologicalSpace A] [IsTopologicalRing A]
  [TopologicalSpace A'] [IsTopologicalRing A'] in

private theorem _root_.AutomorphicForm.CentAsmLocal.map_normString (hrank : Module.finrank K L = Module.finrank K' L') (δ : GL (Fin 2) (L ⊗[K] A)) :
    Matrix.GeneralLinearGroup.map E.toRingHom (normString K L A σ δ) =
      normString K' L' A' σ' (Matrix.GeneralLinearGroup.map E.toRingHom δ) := by
  unfold normString
  rw [map_list_prod, List.map_map, ← hrank]
  congr 1
  apply List.map_congr_left
  intro i _
  show Matrix.GeneralLinearGroup.map E.toRingHom ((⇑(sigmaGL K L A σ))^[i] δ) =
    (⇑(sigmaGL K' L' A' σ'))^[i] (Matrix.GeneralLinearGroup.map E.toRingHom δ)
  have hsc : Function.Semiconj (Matrix.GeneralLinearGroup.map E.toRingHom)
      (⇑(sigmaGL K L A σ)) (⇑(sigmaGL K' L' A' σ')) := fun x => map_sigmaGL σ σ' E hEσ x
  exact (hsc.iterate_right i).eq δ

p2m_export "AutomorphicForm.CentAsmLocal" "map_normString"

noncomputable def glE : GL (Fin 2) (L ⊗[K] A) ≃ₜ* GL (Fin 2) (L' ⊗[K'] A') :=
  haveI := isTopologicalRing_tensor K L A
  haveI := isTopologicalRing_tensor K' L' A'
  glEquiv E hE hE'

theorem glE_apply (g : GL (Fin 2) (L ⊗[K] A)) :
    glE E hE hE' g = Matrix.GeneralLinearGroup.map E.toRingHom g := by
  ext i j
  rfl

include hE hE' hEσ in

theorem twistedCentralizer_forward_gl (δ : GL (Fin 2) (L ⊗[K] A))
    (τ : Measure (twistedCentralizer K L A σ δ)) (hτ : τ.IsHaarMeasure) :
    ∃ τ' : Measure (twistedCentralizer K' L' A' σ' (Matrix.GeneralLinearGroup.map E.toRingHom δ)),
      τ'.IsHaarMeasure ∧
      Measure.map (fun t' : twistedCentralizer K' L' A' σ' (Matrix.GeneralLinearGroup.map E.toRingHom δ) =>
          (t' : GL (Fin 2) (L' ⊗[K'] A'))) τ' =
        Measure.map (fun t : twistedCentralizer K L A σ δ =>
          Matrix.GeneralLinearGroup.map E.toRingHom (t : GL (Fin 2) (L ⊗[K] A))) τ ∧
      (τ.IsInvInvariant → τ'.IsInvInvariant) := by
  haveI := hτ
  haveI := isTopologicalGroup_tensorGL K L A
  haveI := isTopologicalGroup_tensorGL K' L' A'
  have hθ : ∀ g, glE E hE hE' (sigmaGL K L A σ g) = sigmaGL K' L' A' σ' (glE E hE hE' g) := fun g => by
    rw [glE_apply, glE_apply, map_sigmaGL σ σ' E hEσ]
  have h := exists_isHaarMeasure_sigmaCentralizer_forward (glE E hE hE') (sigmaGL K L A σ)
    (sigmaGL K' L' A' σ') hθ δ τ
  simp only [glE_apply] at h
  exact h

include hE hE' hEσ in

theorem twistedCentralizer_backward_gl (δ : GL (Fin 2) (L ⊗[K] A))
    (τ' : Measure (twistedCentralizer K' L' A' σ' (Matrix.GeneralLinearGroup.map E.toRingHom δ)))
    (hτ' : τ'.IsHaarMeasure) :
    ∃ τ : Measure (twistedCentralizer K L A σ δ), τ.IsHaarMeasure ∧
      Measure.map (fun t' : twistedCentralizer K' L' A' σ' (Matrix.GeneralLinearGroup.map E.toRingHom δ) =>
          (t' : GL (Fin 2) (L' ⊗[K'] A'))) τ' =
        Measure.map (fun t : twistedCentralizer K L A σ δ =>
          Matrix.GeneralLinearGroup.map E.toRingHom (t : GL (Fin 2) (L ⊗[K] A))) τ ∧
      (τ'.IsInvInvariant → τ.IsInvInvariant) := by
  haveI := isTopologicalGroup_tensorGL K L A
  haveI := isTopologicalGroup_tensorGL K' L' A'
  have hθ : ∀ g, glE E hE hE' (sigmaGL K L A σ g) = sigmaGL K' L' A' σ' (glE E hE hE' g) := fun g => by
    rw [glE_apply, glE_apply, map_sigmaGL σ σ' E hEσ]
  have h := fun (τ'' : Measure (sigmaCentralizer (sigmaGL K' L' A' σ') (glE E hE hE' δ)))
    (h'' : τ''.IsHaarMeasure) => by
      haveI := h''
      exact exists_isHaarMeasure_sigmaCentralizer_backward (glE E hE hE') (sigmaGL K L A σ)
        (sigmaGL K' L' A' σ') hθ δ τ''
  simp only [glE_apply] at h
  exact h τ' hτ'

end TensorTransport
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.FDTEF P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CasmGram P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.P2mGramSide"

end AutomorphicForm.CentAsmLocal
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.FDTEF P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CasmGram P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.P2mGramSide"
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.FDTEF P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CasmGram P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.P2mGramSide"

end
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.FDTEF P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CasmGram P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.P2mGramSide"

namespace AutomorphicForm
p2m_export "AutomorphicForm" "isTopologicalRing_tensor t2Space_tensor locallyCompactSpace_tensor isTopologicalGroup_tensorGL t2Space_tensorGL locallyCompactSpace_tensorGL glBorelOf borelSpace_glBorelOf centralizerBorel toTensorGL sigmaTensor sigmaGL normString IsSigmaConjugate IsNormConjugator IsNormOf twistedCentralizer twistedCentralizerBorel IsSectionFnOn IsOrbitalIntegralOn IsTwistedSectionFnOn IsTwistedOrbitalIntegralOn Coupled AreMatchingOn archHaarK archHaarL archIdent archIdentGL AreMatchingArch IsRegularSemisimple archEntries_apply IsArchTestFactor sigmaCentralizer mem_sigmaCentralizer_iff SplitPlace.psi SplitPlace.psiEquiv SplitPlace.psiEquiv_apply SplitPlace.psiEquiv_symm_const SplitPlace.psiGL exists_mulEquiv_generalLinearGroup_tensorProduct_infiniteAdeleRing_pi exists_ringEquiv_tensorProduct_infiniteAdeleRing_pi_forall_tmul archIdent_tmul_apply exists_continuous_isSectionFnOn_and_isOrbitalIntegralOn_iff_completion_of_isRegularSemisimple exists_isTwistedSectionFnOn_and_continuous_completion_of_isRegularSemisimple_normString exists_isTwistedSectionFnOn_and_continuous_completion_of_isSigmaConjugate_scalar_of_prime semilocal_central_transfer_of_forall_oneplace_of_referenceMeasures exists_isNormConjugator_and_coupled_of_gram_of_algHom_real exists_isNormConjugator_and_coupled_of_gram_of_algHom_complex exists_isNormConjugator_and_coupled_of_gram_conjAe_of_pos isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar map_centralizer_map_ringEquiv_pi_eq_smul_gram_of_infiniteAdeleRing map_twistedCentralizer_map_ringEquiv_pi_eq_smul_gram_of_infiniteAdeleRing mem_span_map_ringEquiv_pi_iff_of_span_eq_range_includeRight mem_span_map_ringEquiv_pi_iff_of_span_eq_setOf_mul_eq_mul_map_sigmaTensor exists_gram_map_of_ringEquiv_of_exists_gram exists_ringEquiv_tensor_completion_complex_of_isRamified isTwistedOrbitalIntegralOn_map_of_ringEquiv_and_isHaarMeasure_map isNormConjugator_map_iff_and_coupled_map_iff_of_ringEquiv isOrbitalIntegralOn_map_generalLinearGroup_map_of_ringEquiv isHaarMeasure_map_and_exists_isHaarMeasure_centralizer_of_ringEquiv pos_and_exists_coupled_toTensorGL_scalar_one_iff_of_coupled_scalar_conjAe exists_ringEquiv_tensor_baseChange_of_ringEquiv isOrbitalIntegralOn_scalar_neg_of_isTwistedOrbitalIntegralOn_conjAe_of_gram_of_nhds_forall_isNormConjugator_of_neg exists_isSigmaConjugate_scalar_of_isNormConjugator_scalar_of_algHom_of_prime exists_isTwistedSectionFnOn_and_continuous_completion_of_not_isSigmaConjugate_scalar_of_finrank_eq_two exists_isSigmaConjugate_scalar_conjAe_iff_pos_of_isNormConjugator_scalar"
namespace CentAsmLocal
p2m_open "AutomorphicForm"

open NumberField NumberField.InfinitePlace
open scoped TensorProduct TensorProduct.RightActions NumberField.LiesOver

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

omit [NumberField K] [NumberField L] in
theorem comap_eq_mk (w : InfinitePlace L) :
    w.comap (algebraMap K L) = InfinitePlace.mk (w.embedding.comp (algebraMap K L)) := by
  conv_lhs => rw [← mk_embedding w]
  exact comap_mk _ _

omit [NumberField K] [NumberField L] in

theorem embedding_comap_eq (w : InfinitePlace L) (hv : (w.comap (algebraMap K L)).IsReal) :
    (w.comap (algebraMap K L)).embedding = w.embedding.comp (algebraMap K L) := by
  have h := comap_eq_mk (K := K) w
  have h' : InfinitePlace.mk (w.comap (algebraMap K L)).embedding =
      InfinitePlace.mk (w.embedding.comp (algebraMap K L)) := by rw [mk_embedding]; exact h
  rcases mk_eq_iff.1 h' with h1 | h1
  · exact h1
  · have hreal : ComplexEmbedding.IsReal (w.comap (algebraMap K L)).embedding := isReal_iff.1 hv
    rw [ComplexEmbedding.isReal_iff.1 hreal] at h1
    exact h1

omit [NumberField L] in
omit [NumberField K] [NumberField L] in

theorem eq_extensionEmbedding (v : InfinitePlace K) (f : v.Completion →+* ℂ) (hf : Continuous f)
    (h : ∀ k : K, f (algebraMap K v.Completion k) = v.embedding k) (a : v.Completion) :
    f a = Completion.extensionEmbedding v a := by
  induction a using NumberField.InfinitePlace.Completion.induction_on with
  | hp => exact isClosed_eq hf (Completion.isometry_extensionEmbedding v).continuous
  | ih x =>
      rw [Completion.extensionEmbedding_coe]
      have hx : ((x : WithAbs v.1) : v.Completion) = algebraMap K v.Completion (WithAbs.equiv v.1 x) := by
        rw [IsScalarTower.algebraMap_apply K (WithAbs v.1) v.Completion]; rfl
      rw [hx, h]

omit [NumberField K] [NumberField L] in

theorem ofReal_ramModel_eq_extensionEmbedding (w : InfinitePlace L) (hw : w.IsRamified K)
    (e : (w.comap (algebraMap K L)).Completion ≃+* ℝ) (he : Continuous e)
    (h8 : ∀ k : K, (e (algebraMap K (w.comap (algebraMap K L)).Completion k) : ℂ) = w.embedding (algebraMap K L k))
    (a : (w.comap (algebraMap K L)).Completion) :
    (e a : ℂ) = Completion.extensionEmbedding (w.comap (algebraMap K L)) a := by
  obtain ⟨-, hv⟩ := isRamified_iff.1 hw
  refine eq_extensionEmbedding (w.comap (algebraMap K L)) (Complex.ofRealHom.comp e.toRingHom)
    (Complex.continuous_ofReal.comp he) (fun k => ?_) a
  show (e (algebraMap K _ k) : ℂ) = _
  rw [h8, embedding_comap_eq w hv]
  rfl

theorem extensionEmbedding_psiFactor_comm_eq_rid_ramModel (w : InfinitePlace L) (hw : w.IsRamified K)
    (e : (w.comap (algebraMap K L)).Completion ≃+* ℝ) (he : Continuous e)
    (E : L ⊗[K] (w.comap (algebraMap K L)).Completion ≃+* ℂ ⊗[ℝ] ℝ)
    (h7 : ∀ (x : L) (a : (w.comap (algebraMap K L)).Completion),
      (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
        (Algebra.TensorProduct.rid ℝ ℝ ℂ)) (E (x ⊗ₜ a)) = w.embedding x * (e a : ℂ))
    (h8 : ∀ k : K, (e (algebraMap K (w.comap (algebraMap K L)).Completion k) : ℂ) = w.embedding (algebraMap K L k))
    (z : L ⊗[K] (w.comap (algebraMap K L)).Completion) :
    letI : w.1.LiesOver (w.comap (algebraMap K L)).1 := ⟨rfl⟩
    Completion.extensionEmbedding w
        (M4aHerbrand.ArchSemilocal.psiFactor (w.comap (algebraMap K L)) w
          (_root_.Algebra.TensorProduct.comm K L (w.comap (algebraMap K L)).Completion z)) =
      (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
        (Algebra.TensorProduct.rid ℝ ℝ ℂ)) (E z) := by
  letI : w.1.LiesOver (w.comap (algebraMap K L)).1 := ⟨rfl⟩
  obtain ⟨-, hv⟩ := isRamified_iff.1 hw
  haveI : ComplexEmbedding.LiesOver w.embedding (w.comap (algebraMap K L)).embedding :=
    ⟨by rw [embedding_comap_eq w hv]⟩
  haveI := Completion.liesOver_extensionEmbedding w (w.comap (algebraMap K L))
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x a =>
      rw [h7, _root_.Algebra.TensorProduct.comm_tmul, M4aHerbrand.ArchSemilocal.psiFactor_tmul, map_mul,
        Completion.liesOver_extensionEmbedding_apply, ← ofReal_ramModel_eq_extensionEmbedding w hw e he h8 a,
        mul_comm]
      congr 1
      have hx : (algebraMap L w.Completion x) = (((WithAbs.equiv w.1).symm x : WithAbs w.1) : w.Completion) := by
        rw [IsScalarTower.algebraMap_apply L (WithAbs w.1) w.Completion]; rfl
      rw [hx, Completion.extensionEmbedding_coe]
      simp
  | add z₁ z₂ h₁ h₂ =>
      rw [map_add (_root_.Algebra.TensorProduct.comm K L (w.comap (algebraMap K L)).Completion),
        map_add (M4aHerbrand.ArchSemilocal.psiFactor (w.comap (algebraMap K L)) w),
        map_add (Completion.extensionEmbedding w), h₁, h₂, E.map_add,
        map_add ((@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
          (Algebra.TensorProduct.rid ℝ ℝ ℂ)))]

end AutomorphicForm.CentAsmLocal
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.FDTEF P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CasmGram P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.P2mGramSide"
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.FDTEF P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CasmGram P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.P2mGramSide"

namespace AutomorphicForm
p2m_export "AutomorphicForm" "isTopologicalRing_tensor t2Space_tensor locallyCompactSpace_tensor isTopologicalGroup_tensorGL t2Space_tensorGL locallyCompactSpace_tensorGL glBorelOf borelSpace_glBorelOf centralizerBorel toTensorGL sigmaTensor sigmaGL normString IsSigmaConjugate IsNormConjugator IsNormOf twistedCentralizer twistedCentralizerBorel IsSectionFnOn IsOrbitalIntegralOn IsTwistedSectionFnOn IsTwistedOrbitalIntegralOn Coupled AreMatchingOn archHaarK archHaarL archIdent archIdentGL AreMatchingArch IsRegularSemisimple archEntries_apply IsArchTestFactor sigmaCentralizer mem_sigmaCentralizer_iff SplitPlace.psi SplitPlace.psiEquiv SplitPlace.psiEquiv_apply SplitPlace.psiEquiv_symm_const SplitPlace.psiGL exists_mulEquiv_generalLinearGroup_tensorProduct_infiniteAdeleRing_pi exists_ringEquiv_tensorProduct_infiniteAdeleRing_pi_forall_tmul archIdent_tmul_apply exists_continuous_isSectionFnOn_and_isOrbitalIntegralOn_iff_completion_of_isRegularSemisimple exists_isTwistedSectionFnOn_and_continuous_completion_of_isRegularSemisimple_normString exists_isTwistedSectionFnOn_and_continuous_completion_of_isSigmaConjugate_scalar_of_prime semilocal_central_transfer_of_forall_oneplace_of_referenceMeasures exists_isNormConjugator_and_coupled_of_gram_of_algHom_real exists_isNormConjugator_and_coupled_of_gram_of_algHom_complex exists_isNormConjugator_and_coupled_of_gram_conjAe_of_pos isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar map_centralizer_map_ringEquiv_pi_eq_smul_gram_of_infiniteAdeleRing map_twistedCentralizer_map_ringEquiv_pi_eq_smul_gram_of_infiniteAdeleRing mem_span_map_ringEquiv_pi_iff_of_span_eq_range_includeRight mem_span_map_ringEquiv_pi_iff_of_span_eq_setOf_mul_eq_mul_map_sigmaTensor exists_gram_map_of_ringEquiv_of_exists_gram exists_ringEquiv_tensor_completion_complex_of_isRamified isTwistedOrbitalIntegralOn_map_of_ringEquiv_and_isHaarMeasure_map isNormConjugator_map_iff_and_coupled_map_iff_of_ringEquiv isOrbitalIntegralOn_map_generalLinearGroup_map_of_ringEquiv isHaarMeasure_map_and_exists_isHaarMeasure_centralizer_of_ringEquiv pos_and_exists_coupled_toTensorGL_scalar_one_iff_of_coupled_scalar_conjAe exists_ringEquiv_tensor_baseChange_of_ringEquiv isOrbitalIntegralOn_scalar_neg_of_isTwistedOrbitalIntegralOn_conjAe_of_gram_of_nhds_forall_isNormConjugator_of_neg exists_isSigmaConjugate_scalar_of_isNormConjugator_scalar_of_algHom_of_prime exists_isTwistedSectionFnOn_and_continuous_completion_of_not_isSigmaConjugate_scalar_of_finrank_eq_two exists_isSigmaConjugate_scalar_conjAe_iff_pos_of_isNormConjugator_scalar"
namespace CentAsmLocal
p2m_open "AutomorphicForm"

open MeasureTheory

variable (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

attribute [local instance 10000] AutomorphicForm.glBorelOf AutomorphicForm.centralizerBorel

theorem borelSpace_gl' : BorelSpace (GL (Fin 2) A) := ⟨rfl⟩
theorem borelSpace_centralizer' (γ : GL (Fin 2) A) :
    BorelSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) := ⟨rfl⟩

attribute [local instance] borelSpace_gl' borelSpace_centralizer'

omit [TopologicalSpace A] [IsTopologicalRing A] in
theorem scalar_mul_comm (c : Aˣ) (x : GL (Fin 2) A) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) c * x = x * Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
  apply Units.ext
  simp only [Units.val_mul]
  have h : ((Matrix.GeneralLinearGroup.scalar (Fin 2) c : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) =
      Matrix.diagonal (fun _ => (c : A)) := rfl
  rw [h]
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]

omit [TopologicalSpace A] [IsTopologicalRing A] in
theorem conj_scalar (c : Aˣ) (x : GL (Fin 2) A) :
    x⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) c * x = Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
  rw [mul_assoc, scalar_mul_comm, ← mul_assoc, inv_mul_cancel, one_mul]

theorem isOrbitalIntegralOn_scalar_unique [SecondCountableTopology (GL (Fin 2) A)]
    (c : Aˣ) (μ : Measure (GL (Fin 2) A)) [μ.IsMulLeftInvariant] [SFinite μ]
    (τ : Measure (Subgroup.centralizer
      ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) A))))
    [τ.IsInvInvariant] [SFinite τ]
    (f : GL (Fin 2) A → ℂ) (I I' : ℂ)
    (h : IsOrbitalIntegralOn A μ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ f I)
    (h' : IsOrbitalIntegralOn A μ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ f I') : I = I' := by
  have hsf := (rfl : Matrix.GeneralLinearGroup.scalar (Fin 2) c = Matrix.GeneralLinearGroup.scalar (Fin 2) c)
  obtain ⟨w, ⟨hw0, hwm, -, hw1⟩, hI⟩ := h
  obtain ⟨w', ⟨hw0', hwm', -, hw1'⟩, hI'⟩ := h'
  have hcen : ∀ x : GL (Fin 2) A, x⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) c * x =
      Matrix.GeneralLinearGroup.scalar (Fin 2) c := conj_scalar A c
  simp only [hcen] at hI hI' hw1 hw1'
  by_cases hf : f (Matrix.GeneralLinearGroup.scalar (Fin 2) c) = 0
  · rw [hI, hI', hf]; simp

  set W : GL (Fin 2) A → ENNReal := fun x => ENNReal.ofReal (w x) with hW
  set W' : GL (Fin 2) A → ENNReal := fun x => ENNReal.ofReal (w' x) with hW'
  have hWm : Measurable W := ENNReal.measurable_ofReal.comp hwm
  have hWm' : Measurable W' := ENNReal.measurable_ofReal.comp hwm'
  have hT : ∀ x, ∫⁻ t, W ((t : GL (Fin 2) A) * x) ∂τ = 1 := by
    intro x
    have h1 := hw1 x hf
    have hint : Integrable (fun t : Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) A)) =>
        w ((t : GL (Fin 2) A) * x)) τ := Integrable.of_integral_ne_zero (by rw [h1]; exact one_ne_zero)
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun t => hw0 _), h1, ENNReal.ofReal_one]
  have hT' : ∀ x, ∫⁻ t, W' ((t : GL (Fin 2) A) * x) ∂τ = 1 := by
    intro x
    have h1 := hw1' x hf
    have hint : Integrable (fun t : Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) A)) =>
        w' ((t : GL (Fin 2) A) * x)) τ := Integrable.of_integral_ne_zero (by rw [h1]; exact one_ne_zero)
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun t => hw0' _), h1, ENNReal.ofReal_one]

  have hmulm : Measurable (fun p : GL (Fin 2) A × Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) A)) =>
      (p.2 : GL (Fin 2) A) * p.1) :=
    ((continuous_subtype_val.comp continuous_snd).mul continuous_fst).measurable
  have key : ∫⁻ x, W' x ∂μ = ∫⁻ x, W x ∂μ := by
    calc ∫⁻ x, W' x ∂μ = ∫⁻ x, (∫⁻ t, W ((t : GL (Fin 2) A) * x) ∂τ) * W' x ∂μ := by simp [hT]
      _ = ∫⁻ x, ∫⁻ t, W ((t : GL (Fin 2) A) * x) * W' x ∂τ ∂μ := by
          congr 1; funext x
          have hm1 : Measurable (fun t : Subgroup.centralizer
              ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) A)) => W ((t : GL (Fin 2) A) * x)) :=
            hWm.comp ((continuous_subtype_val.mul continuous_const).measurable)
          rw [lintegral_mul_const _ hm1]
      _ = ∫⁻ t, ∫⁻ x, W ((t : GL (Fin 2) A) * x) * W' x ∂μ ∂τ :=
          lintegral_lintegral_swap ((hWm.comp hmulm).mul (hWm'.comp measurable_fst)).aemeasurable
      _ = ∫⁻ t, ∫⁻ x, W x * W' ((t : GL (Fin 2) A)⁻¹ * x) ∂μ ∂τ := by
          congr 1; funext t
          have := lintegral_mul_left_eq_self (μ := μ)
            (fun x => W x * W' ((t : GL (Fin 2) A)⁻¹ * x)) (t : GL (Fin 2) A)
          rw [← this]
          congr 1; funext x
          rw [← mul_assoc, inv_mul_cancel, one_mul]
      _ = ∫⁻ x, ∫⁻ t, W x * W' ((t : GL (Fin 2) A)⁻¹ * x) ∂τ ∂μ := by
          refine (lintegral_lintegral_swap ?_).symm
          exact ((hWm.comp measurable_fst).mul (hWm'.comp
            (((continuous_subtype_val.comp continuous_snd).inv.mul continuous_fst).measurable))).aemeasurable
      _ = ∫⁻ x, W x * ∫⁻ t, W' ((t : GL (Fin 2) A)⁻¹ * x) ∂τ ∂μ := by
          congr 1; funext x
          have hm2 : Measurable (fun t : Subgroup.centralizer
              ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) A)) =>
              W' ((t : GL (Fin 2) A)⁻¹ * x)) :=
            hWm'.comp ((continuous_subtype_val.inv.mul continuous_const).measurable)
          rw [lintegral_const_mul _ hm2]
      _ = ∫⁻ x, W x * ∫⁻ t, W' ((t : GL (Fin 2) A) * x) ∂τ ∂μ := by
          congr 1; funext x; congr 1
          have := lintegral_inv_eq_self (μ := τ) (fun t => W' ((t : GL (Fin 2) A) * x))
          rw [← this]
          rfl
      _ = ∫⁻ x, W x ∂μ := by simp [hT']

  have hre : ∀ u : GL (Fin 2) A → ℝ, (∀ x, 0 ≤ u x) → Measurable u →
      ∫ x, f (Matrix.GeneralLinearGroup.scalar (Fin 2) c) * (u x : ℂ) ∂μ = f (Matrix.GeneralLinearGroup.scalar (Fin 2) c) * ((∫⁻ x, ENNReal.ofReal (u x) ∂μ).toReal : ℝ) := by
    intro u hu0 hum
    rw [integral_const_mul, integral_complex_ofReal, integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hu0)
      hum.aestronglyMeasurable]
  rw [hI, hI', hre w hw0 hwm, hre w' hw0' hwm']
  show f (Matrix.GeneralLinearGroup.scalar (Fin 2) c) * (((∫⁻ x, W x ∂μ).toReal : ℝ) : ℂ) = f (Matrix.GeneralLinearGroup.scalar (Fin 2) c) * (((∫⁻ x, W' x ∂μ).toReal : ℝ) : ℂ)
  rw [key]

section ScalarTorus

variable (F : Type) [Field F] [TopologicalSpace F] [IsTopologicalRing F]

attribute [local instance 10000] AutomorphicForm.glBorelOf AutomorphicForm.centralizerBorel
attribute [local instance] borelSpace_gl' borelSpace_centralizer'

omit [TopologicalSpace F] [IsTopologicalRing F] in
theorem mem_centralizer_scalar (c : Fˣ) (g : GL (Fin 2) F) :
    g ∈ Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) F)) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (scalar_mul_comm F c g).symm

def centralizerScalarEquiv (c : Fˣ) :
    Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) F)) ≃ₜ* GL (Fin 2) F where
  toFun t := (t : GL (Fin 2) F)
  invFun g := ⟨g, mem_centralizer_scalar F c g⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := continuous_subtype_val
  continuous_invFun := continuous_id.subtype_mk _

theorem isInvInvariant_and_sFinite_of_isHaarMeasure_centralizer_scalar
    [LocallyCompactSpace (GL (Fin 2) F)] [SecondCountableTopology (GL (Fin 2) F)]
    (c : Fˣ)
    (τ : Measure (Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) F))))
    [τ.IsHaarMeasure] : τ.IsInvInvariant ∧ SFinite τ := by
  set φ := centralizerScalarEquiv F c with hφ
  have hmφ : Measurable (φ : _ → GL (Fin 2) F) := φ.continuous.measurable
  have hmφ' : Measurable (φ.symm : GL (Fin 2) F → _) := φ.symm.continuous.measurable
  haveI : (Measure.map φ τ).IsHaarMeasure := φ.isHaarMeasure_map τ
  obtain ⟨-, hinv⟩ :=
    Matrix.GeneralLinearGroup.isMulRightInvariant_and_isInvInvariant_of_isHaarMeasure_fin_two (Measure.map φ τ)
  have hback : Measure.map φ.symm (Measure.map φ τ) = τ := by
    rw [Measure.map_map hmφ' hmφ, show ((φ.symm : GL (Fin 2) F → _) ∘ (φ : _ → GL (Fin 2) F)) = id from
      funext fun t => φ.symm_apply_apply t, Measure.map_id]
  refine ⟨?_, ?_⟩
  · rw [← hback]
    constructor
    show Measure.map Inv.inv (Measure.map φ.symm (Measure.map φ τ)) = Measure.map φ.symm (Measure.map φ τ)
    rw [Measure.map_map measurable_inv hmφ',
      show (Inv.inv ∘ (φ.symm : GL (Fin 2) F → _)) = ((φ.symm : GL (Fin 2) F → _) ∘ Inv.inv) from
        funext fun t => (map_inv φ.symm t).symm,
      ← Measure.map_map hmφ' measurable_inv, Measure.map_inv_eq_self]
  · rw [← hback]
    infer_instance

end ScalarTorus
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.FDTEF P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CasmGram P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.P2mGramSide"

end AutomorphicForm.CentAsmLocal
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.FDTEF P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CasmGram P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.P2mGramSide"
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.FDTEF P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CasmGram P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.P2mGramSide"

namespace AutomorphicForm
p2m_export "AutomorphicForm" "isTopologicalRing_tensor t2Space_tensor locallyCompactSpace_tensor isTopologicalGroup_tensorGL t2Space_tensorGL locallyCompactSpace_tensorGL glBorelOf borelSpace_glBorelOf centralizerBorel toTensorGL sigmaTensor sigmaGL normString IsSigmaConjugate IsNormConjugator IsNormOf twistedCentralizer twistedCentralizerBorel IsSectionFnOn IsOrbitalIntegralOn IsTwistedSectionFnOn IsTwistedOrbitalIntegralOn Coupled AreMatchingOn archHaarK archHaarL archIdent archIdentGL AreMatchingArch IsRegularSemisimple archEntries_apply IsArchTestFactor sigmaCentralizer mem_sigmaCentralizer_iff SplitPlace.psi SplitPlace.psiEquiv SplitPlace.psiEquiv_apply SplitPlace.psiEquiv_symm_const SplitPlace.psiGL exists_mulEquiv_generalLinearGroup_tensorProduct_infiniteAdeleRing_pi exists_ringEquiv_tensorProduct_infiniteAdeleRing_pi_forall_tmul archIdent_tmul_apply exists_continuous_isSectionFnOn_and_isOrbitalIntegralOn_iff_completion_of_isRegularSemisimple exists_isTwistedSectionFnOn_and_continuous_completion_of_isRegularSemisimple_normString exists_isTwistedSectionFnOn_and_continuous_completion_of_isSigmaConjugate_scalar_of_prime semilocal_central_transfer_of_forall_oneplace_of_referenceMeasures exists_isNormConjugator_and_coupled_of_gram_of_algHom_real exists_isNormConjugator_and_coupled_of_gram_of_algHom_complex exists_isNormConjugator_and_coupled_of_gram_conjAe_of_pos isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar map_centralizer_map_ringEquiv_pi_eq_smul_gram_of_infiniteAdeleRing map_twistedCentralizer_map_ringEquiv_pi_eq_smul_gram_of_infiniteAdeleRing mem_span_map_ringEquiv_pi_iff_of_span_eq_range_includeRight mem_span_map_ringEquiv_pi_iff_of_span_eq_setOf_mul_eq_mul_map_sigmaTensor exists_gram_map_of_ringEquiv_of_exists_gram exists_ringEquiv_tensor_completion_complex_of_isRamified isTwistedOrbitalIntegralOn_map_of_ringEquiv_and_isHaarMeasure_map isNormConjugator_map_iff_and_coupled_map_iff_of_ringEquiv isOrbitalIntegralOn_map_generalLinearGroup_map_of_ringEquiv isHaarMeasure_map_and_exists_isHaarMeasure_centralizer_of_ringEquiv pos_and_exists_coupled_toTensorGL_scalar_one_iff_of_coupled_scalar_conjAe exists_ringEquiv_tensor_baseChange_of_ringEquiv isOrbitalIntegralOn_scalar_neg_of_isTwistedOrbitalIntegralOn_conjAe_of_gram_of_nhds_forall_isNormConjugator_of_neg exists_isSigmaConjugate_scalar_of_isNormConjugator_scalar_of_algHom_of_prime exists_isTwistedSectionFnOn_and_continuous_completion_of_not_isSigmaConjugate_scalar_of_finrank_eq_two exists_isSigmaConjugate_scalar_conjAe_iff_pos_of_isNormConjugator_scalar"
namespace CentAsmLocal
p2m_open "AutomorphicForm"

open MeasureTheory NumberField NumberField.InfinitePlace
open scoped TensorProduct TensorProduct.RightActions NumberField.LiesOver

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

attribute [local instance 10000] AutomorphicForm.glBorelOf AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel
attribute [local instance] borelSpace_gl borelSpace_centralizer

set_option maxHeartbeats 4000000 in
theorem heng_ram
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (w : InfinitePlace L) (hw : w.IsRamified K)
    (hram : ∀
      (μA : @Measure (GL (Fin 2) ℝ) (glBorelOf ℝ))
      (μL : @Measure (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) (glBorelOf (ℂ ⊗[ℝ] ℝ)))
      (hμA : @Measure.IsHaarMeasure _ _ _ (glBorelOf ℝ) μA)
      (hμL : @Measure.IsHaarMeasure _ _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) μL)
      (φ : GL (Fin 2) ℂ → ℂ)
      (hφ : (∃ Φ : (Fin 2 → Fin 2 → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
        ∀ g, φ g = Φ (fun i j => (g : Matrix (Fin 2) (Fin 2) ℂ) i j)) ∧ HasCompactSupport φ)
      (f : GL (Fin 2) ℝ → ℂ)
      (hf : (∃ F : (Fin 2 → Fin 2 → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F ∧
        ∀ g, f g = F (fun i j => (g : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧ HasCompactSupport f)
      (c : ℝˣ) (hc : 0 < (c : ℝ))
      (hmatch : ∃ V ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
        ∀ δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ), IsRegularSemisimple (normString ℝ ℂ ℝ Complex.conjAe δ) →
        ∀ γ ∈ V, IsRegularSemisimple γ →
        ∀ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ), IsNormConjugator ℝ ℂ ℝ Complex.conjAe γ δ y →
        ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℝ))) (centralizerBorel ℝ γ))
          (τ' : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ)
            (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ)),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ γ) τ →
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) τ' →
          Coupled ℝ ℂ ℝ Complex.conjAe γ δ y τ τ' →
          ∀ I I' : ℂ,
            IsTwistedOrbitalIntegralOn ℝ ℂ ℝ Complex.conjAe μL δ τ'
              (fun z => φ (Matrix.GeneralLinearGroup.map
                (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                  (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom z : GL (Fin 2) ℂ)) I' →
            IsOrbitalIntegralOn ℝ μA γ τ f I → I' = I),
      ∀ δ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ),
        IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y →
        ∀ (τ : @Measure (Subgroup.centralizer
              ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ)))
              (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
          (τ' : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ)
            (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ)),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) τ →
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) τ' →
          Coupled ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y τ τ' →
          ∀ I' : ℂ,
            IsTwistedOrbitalIntegralOn ℝ ℂ ℝ Complex.conjAe μL δ τ'
              (fun z => φ (Matrix.GeneralLinearGroup.map
                (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                  (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom z : GL (Fin 2) ℂ)) I' →
            IsOrbitalIntegralOn ℝ μA (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ f I')
    (μ : @Measure (GL (Fin 2) (w.comap (algebraMap K L)).Completion) (glBorelOf (w.comap (algebraMap K L)).Completion))
    (hμ : @Measure.IsHaarMeasure _ _ _ (glBorelOf (w.comap (algebraMap K L)).Completion) μ)
    (μ' : @Measure (GL (Fin 2) (L ⊗[K] (w.comap (algebraMap K L)).Completion)) (glBorelOf (L ⊗[K] (w.comap (algebraMap K L)).Completion)))
    (hμ' : @Measure.IsHaarMeasure _ _ _ (glBorelOf (L ⊗[K] (w.comap (algebraMap K L)).Completion)) μ')
    (c : ((w.comap (algebraMap K L)).Completion)ˣ)
    (φ : GL (Fin 2) (L ⊗[K] (w.comap (algebraMap K L)).Completion) → ℂ)
    (hφ : (∃ Φ₁ : (Fin 2 → Fin 2 → ((w.comap (algebraMap K L)).Extension L) → ℂ) → ℂ,
        ContDiff ℝ (⊤ : ℕ∞) Φ₁ ∧ ∀ g, φ g = Φ₁ (epsL K L (w.comap (algebraMap K L)) g)) ∧ HasCompactSupport φ)
    (f : GL (Fin 2) (w.comap (algebraMap K L)).Completion → ℂ)
    (hf : (∃ F₁ : (Fin 2 → Fin 2 → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F₁ ∧
        ∀ g, f g = F₁ (epsK K (w.comap (algebraMap K L)) g)) ∧ HasCompactSupport f)
    (hmatch : ∃ V ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
        ∀ δ : GL (Fin 2) (L ⊗[K] (w.comap (algebraMap K L)).Completion), IsRegularSemisimple (normString K L (w.comap (algebraMap K L)).Completion σ δ) →
        ∀ γ ∈ V, IsRegularSemisimple γ →
        ∀ y : GL (Fin 2) (L ⊗[K] (w.comap (algebraMap K L)).Completion), IsNormConjugator K L (w.comap (algebraMap K L)).Completion σ γ δ y →
        ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (w.comap (algebraMap K L)).Completion))) (centralizerBorel (w.comap (algebraMap K L)).Completion γ))
          (τ' : @Measure (twistedCentralizer K L (w.comap (algebraMap K L)).Completion σ δ) (twistedCentralizerBorel K L (w.comap (algebraMap K L)).Completion σ δ)),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel (w.comap (algebraMap K L)).Completion γ) τ →
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (w.comap (algebraMap K L)).Completion σ δ) τ' →
          Coupled K L (w.comap (algebraMap K L)).Completion σ γ δ y τ τ' →
          ∀ I I' : ℂ, IsTwistedOrbitalIntegralOn K L (w.comap (algebraMap K L)).Completion σ μ' δ τ' φ I' →
            IsOrbitalIntegralOn (w.comap (algebraMap K L)).Completion μ γ τ f I → I' = I)
    (δ y : GL (Fin 2) (L ⊗[K] (w.comap (algebraMap K L)).Completion))
    (hN : IsNormConjugator K L (w.comap (algebraMap K L)).Completion σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y)
    (τ : @Measure (Subgroup.centralizer
          ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) (w.comap (algebraMap K L)).Completion)))
          (centralizerBorel (w.comap (algebraMap K L)).Completion (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
    (τ' : @Measure (twistedCentralizer K L (w.comap (algebraMap K L)).Completion σ δ) (twistedCentralizerBorel K L (w.comap (algebraMap K L)).Completion σ δ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel (w.comap (algebraMap K L)).Completion (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) τ)
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (w.comap (algebraMap K L)).Completion σ δ) τ')
    (hτ'i : @Measure.IsInvInvariant _ (twistedCentralizerBorel K L (w.comap (algebraMap K L)).Completion σ δ) _ τ')
    (hC : Coupled K L (w.comap (algebraMap K L)).Completion σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y τ τ')
    (I I' : ℂ) (hI' : IsTwistedOrbitalIntegralOn K L (w.comap (algebraMap K L)).Completion σ μ' δ τ' φ I')
    (hI : IsOrbitalIntegralOn (w.comap (algebraMap K L)).Completion μ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ f I) :
    I' = I := by
  classical

  obtain ⟨hwc, hv⟩ := isRamified_iff.1 hw
  haveI := isTopologicalRing_tensor K L (w.comap (algebraMap K L)).Completion
  haveI := isTopologicalRing_tensor ℝ ℂ ℝ
  haveI := isTopologicalGroup_tensorGL K L (w.comap (algebraMap K L)).Completion
  haveI := isTopologicalGroup_tensorGL ℝ ℂ ℝ

  obtain ⟨e, E, he, he', hE, hE', hEσ, hEι, h7, h8⟩ :=
    AutomorphicForm.exists_ringEquiv_tensor_completion_complex_of_isRamified K L h2 σ hσ w hw
  have hrank : Module.finrank K L = Module.finrank ℝ ℂ := by rw [h2, Complex.finrank_real_complex]

  obtain ⟨τ₀, hτ₀, hτ₀c, -⟩ := centralizer_forward_gl e he he' (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ hτ
  obtain ⟨τ₀', hτ₀', hτ₀'c, -⟩ := twistedCentralizer_forward_gl σ Complex.conjAe E hE hE' hEσ δ τ' hτ'
  have hTTC := AutomorphicForm.isNormConjugator_map_iff_and_coupled_map_iff_of_ringEquiv σ Complex.conjAe hrank
    e he he' E hE hE' hEσ hEι (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y
  have hN' := hTTC.1.mp hN
  have hC' := (hTTC.2 τ τ₀ τ' τ₀' hτ₀c hτ₀'c).mp hC
  have hTTV := AutomorphicForm.isTwistedOrbitalIntegralOn_map_of_ringEquiv_and_isHaarMeasure_map σ Complex.conjAe
    E hE hE' hEσ μ' δ
  have hI'm := hTTV.1 τ' τ₀' hτ₀'c φ I' hI'
  have hμL : @Measure.IsHaarMeasure _ _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ))
      (@Measure.map _ _ (glBorelOf (L ⊗[K] (w.comap (algebraMap K L)).Completion)) (glBorelOf (ℂ ⊗[ℝ] ℝ))
        (Matrix.GeneralLinearGroup.map E.toRingHom) μ') := hTTV.2.1 hμ'
  have hIm := AutomorphicForm.isOrbitalIntegralOn_map_generalLinearGroup_map_of_ringEquiv e he he' μ
    (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ τ₀ hτ₀c f I hI
  have hμA : @Measure.IsHaarMeasure _ _ _ (glBorelOf ℝ)
      (@Measure.map _ _ (glBorelOf (w.comap (algebraMap K L)).Completion) (glBorelOf ℝ) (Matrix.GeneralLinearGroup.map e.toRingHom) μ) :=
    (AutomorphicForm.isHaarMeasure_map_and_exists_isHaarMeasure_centralizer_of_ringEquiv e he he' μ hμ
      (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ₀ hτ₀).1

  obtain ⟨φm, hφm⟩ : ∃ φm : GL (Fin 2) ℂ → ℂ, ∀ g, φm g = φ (Matrix.GeneralLinearGroup.map E.symm.toRingHom
      (Matrix.GeneralLinearGroup.map (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _ (Algebra.TensorProduct.rid ℝ ℝ ℂ)).symm.toRingHom g)) := ⟨_, fun _ => rfl⟩
  obtain ⟨fm, hfm⟩ : ∃ fm : GL (Fin 2) ℝ → ℂ, ∀ g, fm g = f (Matrix.GeneralLinearGroup.map e.symm.toRingHom g) :=
    ⟨_, fun _ => rfl⟩
  have hφeq : (fun z : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) => φm (Matrix.GeneralLinearGroup.map (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _ (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom z : GL (Fin 2) ℂ)) =
      φ ∘ Matrix.GeneralLinearGroup.map E.symm.toRingHom := by
    funext z
    rw [hφm, map_symm_map]
    rfl
  have hfeq : (f ∘ Matrix.GeneralLinearGroup.map e.symm.toRingHom) = fm := funext fun g => (hfm g).symm
  have hφm_smooth : (∃ Φ : (Fin 2 → Fin 2 → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
      ∀ g, φm g = Φ (fun i j => (g : Matrix (Fin 2) (Fin 2) ℂ) i j)) ∧ HasCompactSupport φm := by
    obtain ⟨⟨Φ₁, hΦ₁, hφΦ⟩, hφc⟩ := hφ

    have hT : ∀ w' : (w.comap (algebraMap K L)).Extension L, ∃ T : ℂ →L[ℝ] ℂ, ∀ z : ℂ,
        T z = (letI : w'.1.1.LiesOver (w.comap (algebraMap K L)).1 :=
            M4aHerbrand.ArchSemilocal.liesOver_of_comap_eq w'.2
          Completion.extensionEmbedding w'.1
            (M4aHerbrand.ArchSemilocal.psiFactor (w.comap (algebraMap K L)) w'.1
              (_root_.Algebra.TensorProduct.comm K L (w.comap (algebraMap K L)).Completion (E.symm ((@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _ (Algebra.TensorProduct.rid ℝ ℝ ℂ)).symm z))))) := by
      intro w'
      letI iLO : w'.1.1.LiesOver (w.comap (algebraMap K L)).1 := M4aHerbrand.ArchSemilocal.liesOver_of_comap_eq w'.2
      have hv' : (w'.1.comap (algebraMap K L)).IsReal := by rw [w'.2]; exact hv
      haveI : ComplexEmbedding.LiesOver w'.1.embedding (w.comap (algebraMap K L)).embedding := by
        have h := embedding_comap_eq (K := K) w'.1 hv'
        rw [w'.2] at h
        exact ⟨by rw [h]⟩
      haveI := Completion.liesOver_extensionEmbedding w'.1 (w.comap (algebraMap K L))
      let Tr : ℂ →+* ℂ := (Completion.extensionEmbedding w'.1).comp
        ((M4aHerbrand.ArchSemilocal.psiFactor (w.comap (algebraMap K L)) w'.1).toRingHom.comp
          ((_root_.Algebra.TensorProduct.comm K L (w.comap (algebraMap K L)).Completion).toRingEquiv.toRingHom.comp
            (E.symm.toRingHom.comp (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _ (Algebra.TensorProduct.rid ℝ ℝ ℂ)).symm.toRingHom)))
      have hTr : ∀ z, Tr z = Completion.extensionEmbedding w'.1
          (M4aHerbrand.ArchSemilocal.psiFactor (w.comap (algebraMap K L)) w'.1
            (_root_.Algebra.TensorProduct.comm K L (w.comap (algebraMap K L)).Completion (E.symm ((@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _ (Algebra.TensorProduct.rid ℝ ℝ ℂ)).symm z)))) := fun z => rfl
      have hfix : ∀ r : ℝ, Tr (r : ℂ) = r := by
        intro r
        rw [hTr]
        have h1 : E.symm ((@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _ (Algebra.TensorProduct.rid ℝ ℝ ℂ)).symm (r : ℂ)) = (1 : L) ⊗ₜ e.symm r := by
          apply E.injective
          rw [E.apply_symm_apply]
          apply (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _ (Algebra.TensorProduct.rid ℝ ℝ ℂ)).injective
          rw [RingEquiv.apply_symm_apply, h7, map_one, one_mul, RingEquiv.apply_symm_apply]
        rw [h1, _root_.Algebra.TensorProduct.comm_tmul, M4aHerbrand.ArchSemilocal.psiFactor_tmul, map_one, mul_one,
          Completion.liesOver_extensionEmbedding_apply, ← ofReal_ramModel_eq_extensionEmbedding w hw e he h8,
          RingEquiv.apply_symm_apply]
      refine ⟨LinearMap.toContinuousLinearMap
        { toFun := Tr, map_add' := map_add Tr, map_smul' := fun r z => ?_ }, fun z => rfl⟩
      show Tr (r • z) = r • Tr z
      rw [Complex.real_smul, Complex.real_smul, map_mul, hfix]
    choose T hT using hT
    refine ⟨⟨fun M => Φ₁ (fun i j w' => T w' (M i j)), ?_, ?_⟩, ?_⟩
    · refine hΦ₁.comp ?_
      exact contDiff_pi.2 fun i => contDiff_pi.2 fun j => contDiff_pi.2 fun w' =>
        (T w').contDiff.comp (contDiff_apply_apply ℝ ℂ i j)
    · intro g
      rw [hφm, hφΦ]
      congr 1
      funext i j w'
      rw [hT]
      rfl
    ·
      have hRIDlin : ∃ l : (ℂ ⊗[ℝ] ℝ) →ₗ[ℝ] ℂ, ∀ x, l x = (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _ (Algebra.TensorProduct.rid ℝ ℝ ℂ)) x := by
        refine ⟨{ toFun := (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _ (Algebra.TensorProduct.rid ℝ ℝ ℂ)), map_add' := map_add _, map_smul' := ?_ }, fun _ => rfl⟩
        intro r x
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul z s =>
            rw [TensorProduct.RightActions.smul_def, TensorProduct.comm_tmul, TensorProduct.smul_tmul',
              TensorProduct.comm_symm_tmul, smul_eq_mul]
            show (Algebra.TensorProduct.rid ℝ ℝ ℂ) (z ⊗ₜ (r * s)) = r • (Algebra.TensorProduct.rid ℝ ℝ ℂ) (z ⊗ₜ s)
            rw [Algebra.TensorProduct.rid_tmul, Algebra.TensorProduct.rid_tmul, smul_smul]
        | add x y hx hy =>
            simp only [RingHom.id_apply] at hx hy ⊢
            rw [TensorProduct.RightActions.smul_def, map_add, smul_add, map_add, map_add,
              ← TensorProduct.RightActions.smul_def, ← TensorProduct.RightActions.smul_def, hx, hy]
            rw [map_add, smul_add]
      obtain ⟨l, hl⟩ := hRIDlin
      have hRIDc : Continuous (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _ (Algebra.TensorProduct.rid ℝ ℝ ℂ)) := by
        have hlc : Continuous l := IsModuleTopology.continuous_of_linearMap l
        exact hlc.congr hl
      have hmapRID : Continuous (Matrix.GeneralLinearGroup.map (n := Fin 2) (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _ (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom) :=
        Continuous.units_map _ (continuous_id.matrix_map hRIDc)
      have hmapE : Continuous (Matrix.GeneralLinearGroup.map (n := Fin 2) E.toRingHom) :=
        (glE E hE hE').continuous.congr (glE_apply E hE hE')
      refine HasCompactSupport.intro ((hφc.isCompact.image hmapE).image hmapRID) ?_
      intro g hg
      rw [hφm]
      by_contra hne
      apply hg
      refine ⟨Matrix.GeneralLinearGroup.map E.toRingHom (Matrix.GeneralLinearGroup.map E.symm.toRingHom
        (Matrix.GeneralLinearGroup.map (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _ (Algebra.TensorProduct.rid ℝ ℝ ℂ)).symm.toRingHom g)), ⟨_, subset_tsupport _ hne, rfl⟩, ?_⟩
      rw [map_map_symm, map_map_symm]
  have hfm_smooth : (∃ F : (Fin 2 → Fin 2 → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F ∧
      ∀ g, fm g = F (fun i j => (g : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧ HasCompactSupport fm := by
    obtain ⟨⟨F₁, hF₁, hfF⟩, hfc⟩ := hf
    refine ⟨⟨fun M => F₁ (fun i j => ((M i j : ℝ) : ℂ)), ?_, ?_⟩, ?_⟩
    · refine hF₁.comp ?_
      refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
      exact Complex.ofRealCLM.contDiff.comp (contDiff_apply_apply ℝ ℝ i j)
    · intro g
      rw [hfm, hfF]
      congr 1
      funext i j
      simp only [epsK, Matrix.GeneralLinearGroup.map_apply, Matrix.map_apply, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom]
      rw [← ofReal_ramModel_eq_extensionEmbedding w hw e he h8, RingEquiv.apply_symm_apply]
    · have he'' : Continuous e.symm.symm := by simpa using he
      have h1 := hfc.comp_homeomorph (glEquiv e.symm he' he'').toHomeomorph
      have h2 : (f ∘ ⇑(glEquiv e.symm he' he'').toHomeomorph) = fm := by
        funext g
        show f (glEquiv e.symm he' he'' g) = fm g
        rw [glEquiv_apply, hfm]
      rwa [h2] at h1

  have key := fun (c' : ℝˣ) (hc' : 0 < (c' : ℝ)) =>
    hram (@Measure.map _ _ (glBorelOf (w.comap (algebraMap K L)).Completion) (glBorelOf ℝ) (Matrix.GeneralLinearGroup.map e.toRingHom) μ)
      (@Measure.map _ _ (glBorelOf (L ⊗[K] (w.comap (algebraMap K L)).Completion)) (glBorelOf (ℂ ⊗[ℝ] ℝ))
        (Matrix.GeneralLinearGroup.map E.toRingHom) μ')
      hμA hμL φm hφm_smooth fm hfm_smooth c' hc'
  rw [← hφeq] at hI'm
  rw [hfeq] at hIm
  generalize hg : Matrix.GeneralLinearGroup.map e.toRingHom (Matrix.GeneralLinearGroup.scalar (Fin 2) c) = γ'
    at hN' τ₀ hτ₀ hτ₀c hC' hIm
  have hγ' : γ' = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (e : (w.comap (algebraMap K L)).Completion →* ℝ) c) := by
    rw [← hg, map_scalar]
  subst hγ'
  have hleft : ∀ g : GL (Fin 2) (ℂ ⊗[ℝ] ℝ),
      @Measure.map _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) (glBorelOf (ℂ ⊗[ℝ] ℝ)) (fun z => g * z)
        (0 : @Measure (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) (glBorelOf (ℂ ⊗[ℝ] ℝ))) = 0 := fun g =>
    @Measure.map_zero _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) (glBorelOf (ℂ ⊗[ℝ] ℝ)) _
  obtain ⟨hpos, -⟩ := AutomorphicForm.pos_and_exists_coupled_toTensorGL_scalar_one_iff_of_coupled_scalar_conjAe
    _ hleft (Units.map (e : (w.comap (algebraMap K L)).Completion →* ℝ) c) (Matrix.GeneralLinearGroup.map E.toRingHom δ)
    (Matrix.GeneralLinearGroup.map E.toRingHom y) hN' τ₀ hτ₀ τ₀' hτ₀' hC'

  have hmm : ∃ V ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (e : (w.comap (algebraMap K L)).Completion →* ℝ) c)),
      ∀ δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ), IsRegularSemisimple (normString ℝ ℂ ℝ Complex.conjAe δ) →
      ∀ γ ∈ V, IsRegularSemisimple γ →
      ∀ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ), IsNormConjugator ℝ ℂ ℝ Complex.conjAe γ δ y →
      ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℝ))) (centralizerBorel ℝ γ))
        (τ' : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ)),
        @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ γ) τ →
        @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) τ' →
        Coupled ℝ ℂ ℝ Complex.conjAe γ δ y τ τ' →
        ∀ I I' : ℂ, IsTwistedOrbitalIntegralOn ℝ ℂ ℝ Complex.conjAe
            (@Measure.map _ _ (glBorelOf (L ⊗[K] (w.comap (algebraMap K L)).Completion)) (glBorelOf (ℂ ⊗[ℝ] ℝ))
              (Matrix.GeneralLinearGroup.map E.toRingHom) μ') δ τ'
            (fun z => φm (Matrix.GeneralLinearGroup.map (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _ (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom z : GL (Fin 2) ℂ)) I' →
          IsOrbitalIntegralOn ℝ
            (@Measure.map _ _ (glBorelOf (w.comap (algebraMap K L)).Completion) (glBorelOf ℝ) (Matrix.GeneralLinearGroup.map e.toRingHom) μ)
            γ τ fm I → I' = I := by
    obtain ⟨V, hV, hVm⟩ := hmatch
    have he'' : Continuous e.symm.symm := by simpa using he
    have hE'' : Continuous E.symm.symm := by simpa using hE
    have hEσ' : ∀ z, E.symm (sigmaTensor ℝ ℂ ℝ Complex.conjAe z) =
        sigmaTensor K L (w.comap (algebraMap K L)).Completion σ (E.symm z) := symm_sigmaTensor σ Complex.conjAe E hEσ
    have hEι' : ∀ g' : GL (Fin 2) ℝ, Matrix.GeneralLinearGroup.map E.symm.toRingHom (toTensorGL ℝ ℂ ℝ g') =
        toTensorGL K L (w.comap (algebraMap K L)).Completion (Matrix.GeneralLinearGroup.map e.symm.toRingHom g') :=
      symm_toTensorGL E e hEι
    have hcont : Continuous (Matrix.GeneralLinearGroup.map (n := Fin 2) e.symm.toRingHom) := by
      rw [← coe_glEquiv e.symm he' he'']; exact (glEquiv e.symm he' he'').continuous
    refine ⟨(Matrix.GeneralLinearGroup.map e.symm.toRingHom) ⁻¹' V, ?_, ?_⟩
    · apply hcont.continuousAt.preimage_mem_nhds
      have hsc : Matrix.GeneralLinearGroup.map e.symm.toRingHom
          (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (e : (w.comap (algebraMap K L)).Completion →* ℝ) c)) =
          Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
        rw [← map_scalar e c, map_symm_map]
      rw [hsc]
      exact hV
    · intro δₘ hδₘ γₘ hγₘ hγreg yₘ hyₘ τₘ τₘ' hτₘ hτₘ' hCₘ J J' hJ' hJ
      have hδ₂ : IsRegularSemisimple (normString K L (w.comap (algebraMap K L)).Completion σ (Matrix.GeneralLinearGroup.map E.symm.toRingHom δₘ)) := by
        rw [← map_normString Complex.conjAe σ E.symm hEσ' hrank.symm δₘ]
        exact isRegularSemisimple_map E.symm _ hδₘ
      have hγ₂ : IsRegularSemisimple (Matrix.GeneralLinearGroup.map e.symm.toRingHom γₘ) :=
        isRegularSemisimple_map e.symm γₘ hγreg
      have hγ₂V : Matrix.GeneralLinearGroup.map e.symm.toRingHom γₘ ∈ V := hγₘ
      have hTTC₂ := AutomorphicForm.isNormConjugator_map_iff_and_coupled_map_iff_of_ringEquiv Complex.conjAe σ
        hrank.symm e.symm he' he'' E.symm hE' hE'' hEσ' hEι' γₘ δₘ yₘ
      have hN₂ := hTTC₂.1.mp hyₘ
      obtain ⟨τ₂, hτ₂, hτ₂c, -⟩ := centralizer_forward_gl e.symm he' he'' γₘ τₘ hτₘ
      obtain ⟨τ₂', hτ₂', hτ₂'c, -⟩ := twistedCentralizer_forward_gl Complex.conjAe σ E.symm hE' hE'' hEσ' δₘ τₘ' hτₘ'
      have hC₂ := (hTTC₂.2 τₘ τ₂ τₘ' τ₂' hτ₂c hτ₂'c).mp hCₘ
      have hTTV₂ := AutomorphicForm.isTwistedOrbitalIntegralOn_map_of_ringEquiv_and_isHaarMeasure_map Complex.conjAe σ
        E.symm hE' hE'' hEσ'
        (@Measure.map _ _ (glBorelOf (L ⊗[K] (w.comap (algebraMap K L)).Completion)) (glBorelOf (ℂ ⊗[ℝ] ℝ))
          (Matrix.GeneralLinearGroup.map E.toRingHom) μ') δₘ
      have hJ'₂ := hTTV₂.1 τₘ' τ₂' hτ₂'c _ J' hJ'
      have h84 := AutomorphicForm.isOrbitalIntegralOn_map_generalLinearGroup_map_of_ringEquiv e.symm he' he''
        (@Measure.map _ _ (glBorelOf (w.comap (algebraMap K L)).Completion) (glBorelOf ℝ) (Matrix.GeneralLinearGroup.map e.toRingHom) μ)
        γₘ τₘ τ₂ hτ₂c fm J hJ

      have hmE : Measurable (⇑(Matrix.GeneralLinearGroup.map (n := Fin 2) E.toRingHom)) :=
        ((glE E hE hE').continuous.congr (fun g => glE_apply E hE hE' g)).measurable
      have hmE' : Measurable (⇑(Matrix.GeneralLinearGroup.map (n := Fin 2) E.symm.toRingHom)) :=
        ((glE E.symm hE' hE'').continuous.congr (fun g => glE_apply E.symm hE' hE'' g)).measurable
      have hme : Measurable (⇑(Matrix.GeneralLinearGroup.map (n := Fin 2) e.toRingHom)) := by
        rw [← coe_glEquiv e he he']; exact (glEquiv e he he').continuous.measurable
      have hme' : Measurable (⇑(Matrix.GeneralLinearGroup.map (n := Fin 2) e.symm.toRingHom)) := by
        rw [← coe_glEquiv e.symm he' he'']; exact (glEquiv e.symm he' he'').continuous.measurable
      have hμ'back : Measure.map (⇑(Matrix.GeneralLinearGroup.map E.symm.toRingHom))
          (Measure.map (⇑(Matrix.GeneralLinearGroup.map E.toRingHom)) μ') = μ' := by
        rw [Measure.map_map hmE' hmE,
          show (⇑(Matrix.GeneralLinearGroup.map E.symm.toRingHom) ∘ ⇑(Matrix.GeneralLinearGroup.map (n := Fin 2) E.toRingHom)) = id
            from funext (map_symm_map E), Measure.map_id]
      have hμback : Measure.map (⇑(Matrix.GeneralLinearGroup.map e.symm.toRingHom))
          (Measure.map (⇑(Matrix.GeneralLinearGroup.map e.toRingHom)) μ) = μ := by
        rw [Measure.map_map hme' hme,
          show (⇑(Matrix.GeneralLinearGroup.map e.symm.toRingHom) ∘ ⇑(Matrix.GeneralLinearGroup.map (n := Fin 2) e.toRingHom)) = id
            from funext (map_symm_map e), Measure.map_id]
      have hψ : ((fun z : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) => φm (Matrix.GeneralLinearGroup.map (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _ (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom z : GL (Fin 2) ℂ)) ∘
          ⇑(Matrix.GeneralLinearGroup.map E.symm.symm.toRingHom)) = φ := by
        funext z
        simp only [Function.comp_apply, RingEquiv.symm_symm]
        rw [hφm, map_symm_map, map_symm_map]
      have hf' : (fm ∘ ⇑(Matrix.GeneralLinearGroup.map e.symm.symm.toRingHom)) = f := by
        funext g
        simp only [Function.comp_apply, RingEquiv.symm_symm]
        rw [hfm, map_symm_map]
      rw [hμ'back, hψ] at hJ'₂
      rw [hμback, hf'] at h84
      exact hVm _ hδ₂ _ hγ₂V hγ₂ _ hN₂ τ₂ τ₂' hτ₂ hτ₂' hC₂ J J' hJ'₂ h84
  have hJ := key (Units.map (e : (w.comap (algebraMap K L)).Completion →* ℝ) c) hpos hmm _ _ hN' τ₀ τ₀' hτ₀ hτ₀' hC' I' hI'm

  haveI : LocallyCompactSpace (GL (Fin 2) ℝ) := by
    haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) ℝ) :=
      inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → ℝ))
    exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SecondCountableTopology (GL (Fin 2) ℝ) := by
    haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℝ) :=
      inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℝ))
    haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℝ)ᵐᵒᵖ :=
      MulOpposite.opHomeomorph.symm.secondCountableTopology
    exact Units.isEmbedding_embedProduct.secondCountableTopology
  haveI := hμA
  haveI := hτ₀
  obtain ⟨hτ₀inv, hτ₀sf⟩ :=
    isInvInvariant_and_sFinite_of_isHaarMeasure_centralizer_scalar ℝ (Units.map (e : (w.comap (algebraMap K L)).Completion →* ℝ) c) τ₀
  haveI := hτ₀inv
  haveI := hτ₀sf
  exact isOrbitalIntegralOn_scalar_unique ℝ (Units.map (e : (w.comap (algebraMap K L)).Completion →* ℝ) c) _ τ₀ fm I' I hJ hIm

end AutomorphicForm.CentAsmLocal
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.FDTEF P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CasmGram P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.P2mGramSide"
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.FDTEF P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CasmGram P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.P2mGramSide"

set_option autoImplicit false

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "isTopologicalRing_tensor t2Space_tensor locallyCompactSpace_tensor isTopologicalGroup_tensorGL t2Space_tensorGL locallyCompactSpace_tensorGL glBorelOf borelSpace_glBorelOf centralizerBorel toTensorGL sigmaTensor sigmaGL normString IsSigmaConjugate IsNormConjugator IsNormOf twistedCentralizer twistedCentralizerBorel IsSectionFnOn IsOrbitalIntegralOn IsTwistedSectionFnOn IsTwistedOrbitalIntegralOn Coupled AreMatchingOn archHaarK archHaarL archIdent archIdentGL AreMatchingArch IsRegularSemisimple archEntries_apply IsArchTestFactor sigmaCentralizer mem_sigmaCentralizer_iff SplitPlace.psi SplitPlace.psiEquiv SplitPlace.psiEquiv_apply SplitPlace.psiEquiv_symm_const SplitPlace.psiGL exists_mulEquiv_generalLinearGroup_tensorProduct_infiniteAdeleRing_pi exists_ringEquiv_tensorProduct_infiniteAdeleRing_pi_forall_tmul archIdent_tmul_apply exists_continuous_isSectionFnOn_and_isOrbitalIntegralOn_iff_completion_of_isRegularSemisimple exists_isTwistedSectionFnOn_and_continuous_completion_of_isRegularSemisimple_normString exists_isTwistedSectionFnOn_and_continuous_completion_of_isSigmaConjugate_scalar_of_prime semilocal_central_transfer_of_forall_oneplace_of_referenceMeasures exists_isNormConjugator_and_coupled_of_gram_of_algHom_real exists_isNormConjugator_and_coupled_of_gram_of_algHom_complex exists_isNormConjugator_and_coupled_of_gram_conjAe_of_pos isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar map_centralizer_map_ringEquiv_pi_eq_smul_gram_of_infiniteAdeleRing map_twistedCentralizer_map_ringEquiv_pi_eq_smul_gram_of_infiniteAdeleRing mem_span_map_ringEquiv_pi_iff_of_span_eq_range_includeRight mem_span_map_ringEquiv_pi_iff_of_span_eq_setOf_mul_eq_mul_map_sigmaTensor exists_gram_map_of_ringEquiv_of_exists_gram exists_ringEquiv_tensor_completion_complex_of_isRamified isTwistedOrbitalIntegralOn_map_of_ringEquiv_and_isHaarMeasure_map isNormConjugator_map_iff_and_coupled_map_iff_of_ringEquiv isOrbitalIntegralOn_map_generalLinearGroup_map_of_ringEquiv isHaarMeasure_map_and_exists_isHaarMeasure_centralizer_of_ringEquiv pos_and_exists_coupled_toTensorGL_scalar_one_iff_of_coupled_scalar_conjAe exists_ringEquiv_tensor_baseChange_of_ringEquiv isOrbitalIntegralOn_scalar_neg_of_isTwistedOrbitalIntegralOn_conjAe_of_gram_of_nhds_forall_isNormConjugator_of_neg exists_isSigmaConjugate_scalar_of_isNormConjugator_scalar_of_algHom_of_prime exists_isTwistedSectionFnOn_and_continuous_completion_of_not_isSigmaConjugate_scalar_of_finrank_eq_two exists_isSigmaConjugate_scalar_conjAe_iff_pos_of_isNormConjugator_scalar"
namespace O6Split
p2m_open "AutomorphicForm"

p2m_open "MeasureTheory AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm"
open scoped TensorProduct TensorProduct.RightActions

section Pair
variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] (σ : L ≃ₐ[K] L)
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]
  (A' : Type) [CommRing A'] [Algebra K A'] [TopologicalSpace A'] [IsTopologicalRing A']
  (e : A ≃+* A') (E : L ⊗[K] A ≃+* L ⊗[K] A')

private theorem _root_.AutomorphicForm.O6Split.map_sigmaGL (hEσ : ∀ z, E (sigmaTensor K L A σ z) = sigmaTensor K L A' σ (E z)) (g : GL (Fin 2) (L ⊗[K] A)) :
    Matrix.GeneralLinearGroup.map E.toRingHom (sigmaGL K L A σ g) =
      sigmaGL K L A' σ (Matrix.GeneralLinearGroup.map E.toRingHom g) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  simp only [sigmaGL, Matrix.GeneralLinearGroup.map_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
    RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  exact hEσ _

p2m_export "AutomorphicForm.O6Split" "map_sigmaGL"

private theorem _root_.AutomorphicForm.O6Split.symm_sigmaTensor (hEσ : ∀ z, E (sigmaTensor K L A σ z) = sigmaTensor K L A' σ (E z)) (z : L ⊗[K] A') : E.symm (sigmaTensor K L A' σ z) = sigmaTensor K L A σ (E.symm z) := by
  apply E.injective
  rw [E.apply_symm_apply, hEσ, E.apply_symm_apply]

p2m_export "AutomorphicForm.O6Split" "symm_sigmaTensor"

private theorem _root_.AutomorphicForm.O6Split.map_normString (hEσ : ∀ z, E (sigmaTensor K L A σ z) = sigmaTensor K L A' σ (E z)) (δ : GL (Fin 2) (L ⊗[K] A)) :
    Matrix.GeneralLinearGroup.map E.toRingHom (normString K L A σ δ) =
      normString K L A' σ (Matrix.GeneralLinearGroup.map E.toRingHom δ) := by
  have hiter : ∀ (i : ℕ) (g : GL (Fin 2) (L ⊗[K] A)),
      Matrix.GeneralLinearGroup.map E.toRingHom ((⇑(sigmaGL K L A σ))^[i] g) =
        (⇑(sigmaGL K L A' σ))^[i] (Matrix.GeneralLinearGroup.map E.toRingHom g) := by
    intro i; induction i with
    | zero => intro g; rfl
    | succ i ih => intro g; rw [Function.iterate_succ_apply', Function.iterate_succ_apply', map_sigmaGL K L σ A A' E hEσ, ih]
  simp only [normString, map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  exact hiter i δ

p2m_export "AutomorphicForm.O6Split" "map_normString"
theorem isRegularSemisimple_map_of_ringHom {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (g : GL (Fin 2) R)
    (hg : IsRegularSemisimple g) : IsRegularSemisimple (Matrix.GeneralLinearGroup.map φ g) := by
  unfold IsRegularSemisimple at hg ⊢
  have h : Matrix.trace ((Matrix.GeneralLinearGroup.map φ g : GL (Fin 2) S) : Matrix (Fin 2) (Fin 2) S) ^ 2 -
      4 * Matrix.det ((Matrix.GeneralLinearGroup.map φ g : GL (Fin 2) S) : Matrix (Fin 2) (Fin 2) S) =
      φ (Matrix.trace (g : Matrix (Fin 2) (Fin 2) R) ^ 2 - 4 * Matrix.det (g : Matrix (Fin 2) (Fin 2) R)) := by
    simp [Matrix.trace_fin_two, Matrix.det_fin_two, map_sub, map_mul, map_pow, map_add, map_ofNat]
  rw [h]; exact hg.map φ

theorem isRegularSemisimple_map_iff (g : GL (Fin 2) A) :
    IsRegularSemisimple (Matrix.GeneralLinearGroup.map e.toRingHom g) ↔ IsRegularSemisimple g := by
  refine ⟨fun h => ?_, isRegularSemisimple_map_of_ringHom e.toRingHom g⟩
  have h2 := isRegularSemisimple_map_of_ringHom e.symm.toRingHom _ h
  have : Matrix.GeneralLinearGroup.map e.symm.toRingHom (Matrix.GeneralLinearGroup.map e.toRingHom g) = g := by
    ext i j; simp
  rwa [this] at h2

end Pair
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.FDTEF P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CasmGram P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.P2mGramSide"

section Measures
variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] (σ : L ≃ₐ[K] L)
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]
  (A' : Type) [CommRing A'] [Algebra K A'] [TopologicalSpace A'] [IsTopologicalRing A']
  (e : A ≃+* A') (E : L ⊗[K] A ≃+* L ⊗[K] A')

theorem exists_isHaarMeasure_centralizer_scalar_forward (he : Continuous e) (he' : Continuous e.symm) (c : Aˣ)
    (τ : @Measure (Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) A)))
      (centralizerBorel A (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel A (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) τ) :
    ∃ τ₀ : @Measure (Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (e : A →* A') c)} : Set (GL (Fin 2) A')))
        (centralizerBorel A' (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (e : A →* A') c))),
      @Measure.IsHaarMeasure _ _ _ (centralizerBorel A' _) τ₀ ∧
      (letI := glBorelOf A'; letI := centralizerBorel A (Matrix.GeneralLinearGroup.scalar (Fin 2) c);
        letI := centralizerBorel A' (Matrix.GeneralLinearGroup.map e.toRingHom (Matrix.GeneralLinearGroup.scalar (Fin 2) c));
        letI := centralizerBorel A' (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (e : A →* A') c));
        Measure.map (fun t : Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (e : A →* A') c)} : Set (GL (Fin 2) A')) => (t : GL (Fin 2) A')) τ₀ =
          Measure.map (fun t : Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) A)) =>
            Matrix.GeneralLinearGroup.map e.toRingHom (t : GL (Fin 2) A)) τ) ∧
      (@Measure.IsInvInvariant _ (centralizerBorel A _) _ τ → @Measure.IsInvInvariant _ (centralizerBorel A' _) _ τ₀) := by
  letI : MeasurableSpace (GL (Fin 2) A) := glBorelOf A
  letI : MeasurableSpace (GL (Fin 2) A') := glBorelOf A'
  haveI : BorelSpace (GL (Fin 2) A) := borelSpace_glBorelOf A
  haveI : BorelSpace (GL (Fin 2) A') := borelSpace_glBorelOf A'
  letI : MeasurableSpace (Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) A))) :=
    centralizerBorel A _
  haveI : BorelSpace (Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) A))) := ⟨rfl⟩
  haveI : τ.IsHaarMeasure := hτ
  let ê := AutomorphicForm.CentAsmLocal.glEquiv e he he'
  have hco : (⇑ê : GL (Fin 2) A → GL (Fin 2) A') = Matrix.GeneralLinearGroup.map e.toRingHom :=
    AutomorphicForm.CentAsmLocal.coe_glEquiv e he he'
  have hx : ê (Matrix.GeneralLinearGroup.scalar (Fin 2) c) = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (e : A →* A') c) := by
    rw [AutomorphicForm.CentAsmLocal.glEquiv_apply, AutomorphicForm.CentAsmLocal.map_scalar]
  have aux : ∀ (x : GL (Fin 2) A'), ê (Matrix.GeneralLinearGroup.scalar (Fin 2) c) = x →
      ∃ τ₀ : @Measure (Subgroup.centralizer ({x} : Set (GL (Fin 2) A'))) (centralizerBorel A' x),
        @Measure.IsHaarMeasure _ _ _ (centralizerBorel A' x) τ₀ ∧
        @Measure.map _ _ (centralizerBorel A' x) (glBorelOf A') (fun t : Subgroup.centralizer ({x} : Set (GL (Fin 2) A')) => (t : GL (Fin 2) A')) τ₀ =
          Measure.map (fun t : Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) A)) => ê (t : GL (Fin 2) A)) τ ∧
        (τ.IsInvInvariant → @Measure.IsInvInvariant _ (centralizerBorel A' x) _ τ₀) := by
    intro x hx'
    letI : MeasurableSpace (Subgroup.centralizer ({x} : Set (GL (Fin 2) A'))) := centralizerBorel A' x
    haveI : BorelSpace (Subgroup.centralizer ({x} : Set (GL (Fin 2) A'))) := ⟨rfl⟩
    subst hx'
    exact AutomorphicForm.CentAsmLocal.exists_isHaarMeasure_centralizer_forward ê _ τ
  obtain ⟨τ₀, h1, h2, h3⟩ := aux _ hx
  refine ⟨τ₀, h1, ?_, h3⟩
  rw [h2, hco]

theorem exists_isHaarMeasure_twistedCentralizer_forward (hE : Continuous E) (hE' : Continuous E.symm)
    (hEσ : ∀ z, E (sigmaTensor K L A σ z) = sigmaTensor K L A' σ (E z)) (δ : GL (Fin 2) (L ⊗[K] A))
    (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L A σ δ) τ') :
    ∃ τ₀' : @Measure (twistedCentralizer K L A' σ (Matrix.GeneralLinearGroup.map E.toRingHom δ))
        (twistedCentralizerBorel K L A' σ (Matrix.GeneralLinearGroup.map E.toRingHom δ)),
      @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L A' σ _) τ₀' ∧
      (letI := glBorelOf (L ⊗[K] A'); letI := twistedCentralizerBorel K L A σ δ;
        letI := twistedCentralizerBorel K L A' σ (Matrix.GeneralLinearGroup.map E.toRingHom δ);
        Measure.map (fun t : twistedCentralizer K L A' σ (Matrix.GeneralLinearGroup.map E.toRingHom δ) =>
            (t : GL (Fin 2) (L ⊗[K] A'))) τ₀' =
          Measure.map (fun t : twistedCentralizer K L A σ δ =>
            Matrix.GeneralLinearGroup.map E.toRingHom (t : GL (Fin 2) (L ⊗[K] A))) τ') ∧
      (@Measure.IsInvInvariant _ (twistedCentralizerBorel K L A σ δ) _ τ' →
        @Measure.IsInvInvariant _ (twistedCentralizerBorel K L A' σ _) _ τ₀') := by
  letI : MeasurableSpace (GL (Fin 2) (L ⊗[K] A)) := glBorelOf (L ⊗[K] A)
  letI : MeasurableSpace (GL (Fin 2) (L ⊗[K] A')) := glBorelOf (L ⊗[K] A')
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] A)) := borelSpace_glBorelOf _
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] A')) := borelSpace_glBorelOf _
  haveI : IsTopologicalRing (L ⊗[K] A) := isTopologicalRing_tensor K L A
  haveI : IsTopologicalRing (L ⊗[K] A') := isTopologicalRing_tensor K L A'
  haveI : IsTopologicalGroup (GL (Fin 2) (L ⊗[K] A)) := isTopologicalGroup_tensorGL K L A
  haveI : IsTopologicalGroup (GL (Fin 2) (L ⊗[K] A')) := isTopologicalGroup_tensorGL K L A'
  letI : MeasurableSpace (twistedCentralizer K L A σ δ) := twistedCentralizerBorel K L A σ δ
  haveI : BorelSpace (twistedCentralizer K L A σ δ) := ⟨rfl⟩
  haveI : τ'.IsHaarMeasure := hτ'
  let Ê := AutomorphicForm.CentAsmLocal.glEquiv E hE hE'
  have hco : (⇑Ê : GL (Fin 2) (L ⊗[K] A) → GL (Fin 2) (L ⊗[K] A')) = Matrix.GeneralLinearGroup.map E.toRingHom :=
    AutomorphicForm.CentAsmLocal.coe_glEquiv E hE hE'
  have hθ : ∀ g, Ê (sigmaGL K L A σ g) = sigmaGL K L A' σ (Ê g) := by
    intro g; rw [AutomorphicForm.CentAsmLocal.glEquiv_apply, AutomorphicForm.CentAsmLocal.glEquiv_apply]
    exact map_sigmaGL K L σ A A' E hEσ g
  have hx : Ê δ = Matrix.GeneralLinearGroup.map E.toRingHom δ := AutomorphicForm.CentAsmLocal.glEquiv_apply E hE hE' δ
  have aux : ∀ (x : GL (Fin 2) (L ⊗[K] A')), Ê δ = x →
      ∃ τ₀' : @Measure (twistedCentralizer K L A' σ x) (twistedCentralizerBorel K L A' σ x),
        @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L A' σ x) τ₀' ∧
        @Measure.map _ _ (twistedCentralizerBorel K L A' σ x) (glBorelOf (L ⊗[K] A'))
            (fun t : twistedCentralizer K L A' σ x => (t : GL (Fin 2) (L ⊗[K] A'))) τ₀' =
          Measure.map (fun t : twistedCentralizer K L A σ δ => Ê (t : GL (Fin 2) (L ⊗[K] A))) τ' ∧
        (τ'.IsInvInvariant → @Measure.IsInvInvariant _ (twistedCentralizerBorel K L A' σ x) _ τ₀') := by
    intro x hx'
    letI : MeasurableSpace (twistedCentralizer K L A' σ x) := twistedCentralizerBorel K L A' σ x
    haveI : BorelSpace (twistedCentralizer K L A' σ x) := ⟨rfl⟩
    subst hx'
    exact AutomorphicForm.CentAsmLocal.exists_isHaarMeasure_sigmaCentralizer_forward Ê
      (sigmaGL K L A σ) (sigmaGL K L A' σ) hθ δ τ'
  obtain ⟨τ₀', h1, h2, h3⟩ := aux _ hx
  refine ⟨τ₀', h1, ?_, h3⟩
  rw [h2, hco]

theorem isOrbitalIntegralOn_map_iff (he : Continuous e) (he' : Continuous e.symm) (γ : GL (Fin 2) A)
    (μ : @Measure (GL (Fin 2) A) (glBorelOf A))
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ))
    (τ₀ : @Measure (Subgroup.centralizer ({Matrix.GeneralLinearGroup.map e.toRingHom γ} : Set (GL (Fin 2) A')))
      (centralizerBorel A' (Matrix.GeneralLinearGroup.map e.toRingHom γ)))
    (hrel : letI := glBorelOf A'; letI := centralizerBorel A γ;
      letI := centralizerBorel A' (Matrix.GeneralLinearGroup.map e.toRingHom γ);
      Measure.map (fun t : Subgroup.centralizer ({Matrix.GeneralLinearGroup.map e.toRingHom γ} : Set (GL (Fin 2) A')) => (t : GL (Fin 2) A')) τ₀ =
        Measure.map (fun t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) => Matrix.GeneralLinearGroup.map e.toRingHom (t : GL (Fin 2) A)) τ)
    (f : GL (Fin 2) A → ℂ) (I : ℂ) :
    IsOrbitalIntegralOn A μ γ τ f I ↔
      IsOrbitalIntegralOn A' (@Measure.map _ _ (glBorelOf A) (glBorelOf A') (Matrix.GeneralLinearGroup.map e.toRingHom) μ)
        (Matrix.GeneralLinearGroup.map e.toRingHom γ) τ₀ (f ∘ Matrix.GeneralLinearGroup.map e.symm.toRingHom) I := by
  letI mA : MeasurableSpace (GL (Fin 2) A) := glBorelOf A
  letI mA' : MeasurableSpace (GL (Fin 2) A') := glBorelOf A'
  haveI : BorelSpace (GL (Fin 2) A) := borelSpace_glBorelOf A
  haveI : BorelSpace (GL (Fin 2) A') := borelSpace_glBorelOf A'
  letI mT : MeasurableSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) := centralizerBorel A γ
  letI mT' : MeasurableSpace (Subgroup.centralizer ({Matrix.GeneralLinearGroup.map e.toRingHom γ} : Set (GL (Fin 2) A'))) :=
    centralizerBorel A' _
  haveI : BorelSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) := ⟨rfl⟩
  haveI : BorelSpace (Subgroup.centralizer ({Matrix.GeneralLinearGroup.map e.toRingHom γ} : Set (GL (Fin 2) A'))) := ⟨rfl⟩
  let ê := AutomorphicForm.CentAsmLocal.glEquiv e he he'
  have hê : ∀ g, ê g = Matrix.GeneralLinearGroup.map e.toRingHom g := AutomorphicForm.CentAsmLocal.glEquiv_apply e he he'
  have hês : ∀ g, ê.symm g = Matrix.GeneralLinearGroup.map e.symm.toRingHom g := AutomorphicForm.CentAsmLocal.glEquiv_symm_apply e he he'
  let êm : GL (Fin 2) A ≃ᵐ GL (Fin 2) A' := ê.toHomeomorph.toMeasurableEquiv
  have hêm : ∀ g, êm g = Matrix.GeneralLinearGroup.map e.toRingHom g := hê
  have hmapμ : Measure.map (Matrix.GeneralLinearGroup.map e.toRingHom) μ = Measure.map êm μ := by
    rw [show (Matrix.GeneralLinearGroup.map e.toRingHom : GL (Fin 2) A → GL (Fin 2) A') = ⇑êm from (funext hêm).symm]
  have hcont : Continuous (Matrix.GeneralLinearGroup.map e.toRingHom : GL (Fin 2) A → GL (Fin 2) A') := by
    rw [← AutomorphicForm.CentAsmLocal.coe_glEquiv e he he']; exact ê.continuous
  have hcont' : Continuous (Matrix.GeneralLinearGroup.map e.symm.toRingHom : GL (Fin 2) A' → GL (Fin 2) A) := by
    rw [← AutomorphicForm.CentAsmLocal.coe_glEquiv e.symm he' (by simpa using he)]
    exact (AutomorphicForm.CentAsmLocal.glEquiv e.symm he' (by simpa using he)).continuous

  have htorus : ∀ F : GL (Fin 2) A' → ℝ, Measurable F →
      ∫ t, F (t : GL (Fin 2) A') ∂τ₀ = ∫ t, F (Matrix.GeneralLinearGroup.map e.toRingHom (t : GL (Fin 2) A)) ∂τ := by
    intro F hF
    have h1 : ∫ t, F (t : GL (Fin 2) A') ∂τ₀ = ∫ g, F g ∂(Measure.map (fun t : Subgroup.centralizer ({Matrix.GeneralLinearGroup.map e.toRingHom γ} : Set (GL (Fin 2) A')) => (t : GL (Fin 2) A')) τ₀) := by
      rw [integral_map continuous_subtype_val.measurable.aemeasurable hF.aestronglyMeasurable]
    have h2 : ∫ t, F (Matrix.GeneralLinearGroup.map e.toRingHom (t : GL (Fin 2) A)) ∂τ =
        ∫ g, F g ∂(Measure.map (fun t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) => Matrix.GeneralLinearGroup.map e.toRingHom (t : GL (Fin 2) A)) τ) := by
      rw [integral_map (show Measurable (fun t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) => Matrix.GeneralLinearGroup.map e.toRingHom (t : GL (Fin 2) A)) from (hcont.comp continuous_subtype_val).measurable).aemeasurable hF.aestronglyMeasurable]
    rw [h1, h2, hrel]
  have hconjA : ∀ x' : GL (Fin 2) A',
      Matrix.GeneralLinearGroup.map e.symm.toRingHom (x'⁻¹ * Matrix.GeneralLinearGroup.map e.toRingHom γ * x') =
        (Matrix.GeneralLinearGroup.map e.symm.toRingHom x')⁻¹ * γ * Matrix.GeneralLinearGroup.map e.symm.toRingHom x' := by
    intro x'; rw [map_mul, map_mul, map_inv, AutomorphicForm.CentAsmLocal.map_symm_map]
  have hconjA' : ∀ x : GL (Fin 2) A,
      Matrix.GeneralLinearGroup.map e.toRingHom (x⁻¹ * γ * x) =
        (Matrix.GeneralLinearGroup.map e.toRingHom x)⁻¹ * Matrix.GeneralLinearGroup.map e.toRingHom γ * Matrix.GeneralLinearGroup.map e.toRingHom x := by
    intro x; rw [map_mul, map_mul, map_inv]

  have hval : ∀ G : GL (Fin 2) A' → ℂ,
      ∫ x', G x' ∂(Measure.map (Matrix.GeneralLinearGroup.map e.toRingHom) μ) = ∫ x, G (Matrix.GeneralLinearGroup.map e.toRingHom x) ∂μ := by
    intro G; rw [hmapμ, MeasureTheory.integral_map_equiv]
    simp_rw [hêm]
  constructor
  · rintro ⟨w, ⟨hw0, hwm, hwcs, hw1⟩, hI⟩
    refine ⟨w ∘ Matrix.GeneralLinearGroup.map e.symm.toRingHom, ⟨fun x => hw0 _, hwm.comp hcont'.measurable, ?_, ?_⟩, ?_⟩
    · have : (w ∘ Matrix.GeneralLinearGroup.map e.symm.toRingHom) = w ∘ ê.symm.toHomeomorph := by
        funext g; exact congrArg w (hês g).symm
      rw [this]; exact hwcs.comp_homeomorph _
    · intro x' hx'
      have hx : f ((Matrix.GeneralLinearGroup.map e.symm.toRingHom x')⁻¹ * γ * Matrix.GeneralLinearGroup.map e.symm.toRingHom x') ≠ 0 := by
        rwa [Function.comp_apply, hconjA] at hx'
      have h := hw1 _ hx
      show ∫ t, w (Matrix.GeneralLinearGroup.map e.symm.toRingHom ((t : GL (Fin 2) A') * x')) ∂τ₀ = 1
      rw [htorus (fun g' => w (Matrix.GeneralLinearGroup.map e.symm.toRingHom (g' * x'))) (hwm.comp (hcont'.comp (continuous_id.mul continuous_const)).measurable)]
      simp_rw [map_mul, AutomorphicForm.CentAsmLocal.map_symm_map]
      exact h
    · rw [hI, hval]
      simp only [Function.comp_apply, hconjA, AutomorphicForm.CentAsmLocal.map_symm_map]
  · rintro ⟨w', ⟨hw0, hwm, hwcs, hw1⟩, hI⟩
    refine ⟨w' ∘ Matrix.GeneralLinearGroup.map e.toRingHom, ⟨fun x => hw0 _, hwm.comp hcont.measurable, ?_, ?_⟩, ?_⟩
    · have : (w' ∘ Matrix.GeneralLinearGroup.map e.toRingHom) = w' ∘ ê.toHomeomorph := by
        funext g; exact congrArg w' (hê g).symm
      rw [this]; exact hwcs.comp_homeomorph _
    · intro x hx
      have hx' : (f ∘ Matrix.GeneralLinearGroup.map e.symm.toRingHom)
          ((Matrix.GeneralLinearGroup.map e.toRingHom x)⁻¹ * Matrix.GeneralLinearGroup.map e.toRingHom γ * Matrix.GeneralLinearGroup.map e.toRingHom x) ≠ 0 := by
        rw [Function.comp_apply, ← hconjA', AutomorphicForm.CentAsmLocal.map_symm_map]; exact hx
      have h := hw1 _ hx'
      rw [htorus (fun g' => w' (g' * Matrix.GeneralLinearGroup.map e.toRingHom x)) (hwm.comp (continuous_id.mul continuous_const).measurable)] at h
      simp_rw [← map_mul] at h
      exact h
    · rw [hI, hval]
      simp only [Function.comp_apply, hconjA, AutomorphicForm.CentAsmLocal.map_symm_map]

theorem isTwistedOrbitalIntegralOn_map_iff (hE : Continuous E) (hE' : Continuous E.symm)
    (hEσ : ∀ z, E (sigmaTensor K L A σ z) = sigmaTensor K L A' σ (E z)) (δ : GL (Fin 2) (L ⊗[K] A))
    (μ : @Measure (GL (Fin 2) (L ⊗[K] A)) (glBorelOf (L ⊗[K] A)))
    (τ : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ))
    (τ₀ : @Measure (twistedCentralizer K L A' σ (Matrix.GeneralLinearGroup.map E.toRingHom δ))
      (twistedCentralizerBorel K L A' σ (Matrix.GeneralLinearGroup.map E.toRingHom δ)))
    (hrel : letI := glBorelOf (L ⊗[K] A'); letI := twistedCentralizerBorel K L A σ δ;
      letI := twistedCentralizerBorel K L A' σ (Matrix.GeneralLinearGroup.map E.toRingHom δ);
      Measure.map (fun t : twistedCentralizer K L A' σ (Matrix.GeneralLinearGroup.map E.toRingHom δ) => (t : GL (Fin 2) (L ⊗[K] A'))) τ₀ =
        Measure.map (fun t : twistedCentralizer K L A σ δ => Matrix.GeneralLinearGroup.map E.toRingHom (t : GL (Fin 2) (L ⊗[K] A))) τ)
    (f : GL (Fin 2) (L ⊗[K] A) → ℂ) (I : ℂ) :
    IsTwistedOrbitalIntegralOn K L A σ μ δ τ f I ↔
      IsTwistedOrbitalIntegralOn K L A' σ (@Measure.map _ _ (glBorelOf (L ⊗[K] A)) (glBorelOf (L ⊗[K] A')) (Matrix.GeneralLinearGroup.map E.toRingHom) μ)
        (Matrix.GeneralLinearGroup.map E.toRingHom δ) τ₀ (f ∘ Matrix.GeneralLinearGroup.map E.symm.toRingHom) I := by
  letI mA : MeasurableSpace (GL (Fin 2) (L ⊗[K] A)) := glBorelOf (L ⊗[K] A)
  haveI : IsTopologicalRing (L ⊗[K] A) := isTopologicalRing_tensor K L A
  haveI : IsTopologicalRing (L ⊗[K] A') := isTopologicalRing_tensor K L A'
  haveI : IsTopologicalGroup (GL (Fin 2) (L ⊗[K] A)) := isTopologicalGroup_tensorGL K L A
  haveI : IsTopologicalGroup (GL (Fin 2) (L ⊗[K] A')) := isTopologicalGroup_tensorGL K L A'
  letI mA' : MeasurableSpace (GL (Fin 2) (L ⊗[K] A')) := glBorelOf (L ⊗[K] A')
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] A)) := borelSpace_glBorelOf (L ⊗[K] A)
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] A')) := borelSpace_glBorelOf (L ⊗[K] A')
  letI mT : MeasurableSpace (twistedCentralizer K L A σ δ) := twistedCentralizerBorel K L A σ δ
  letI mT' : MeasurableSpace (twistedCentralizer K L A' σ (Matrix.GeneralLinearGroup.map E.toRingHom δ)) :=
    twistedCentralizerBorel K L A' σ _
  haveI : BorelSpace (twistedCentralizer K L A σ δ) := ⟨rfl⟩
  haveI : BorelSpace (twistedCentralizer K L A' σ (Matrix.GeneralLinearGroup.map E.toRingHom δ)) := ⟨rfl⟩
  let ê := AutomorphicForm.CentAsmLocal.glEquiv E hE hE'
  have hê : ∀ g, ê g = Matrix.GeneralLinearGroup.map E.toRingHom g := AutomorphicForm.CentAsmLocal.glEquiv_apply E hE hE'
  have hês : ∀ g, ê.symm g = Matrix.GeneralLinearGroup.map E.symm.toRingHom g := AutomorphicForm.CentAsmLocal.glEquiv_symm_apply E hE hE'
  let êm : GL (Fin 2) (L ⊗[K] A) ≃ᵐ GL (Fin 2) (L ⊗[K] A') := ê.toHomeomorph.toMeasurableEquiv
  have hêm : ∀ g, êm g = Matrix.GeneralLinearGroup.map E.toRingHom g := hê
  have hmapμ : Measure.map (Matrix.GeneralLinearGroup.map E.toRingHom) μ = Measure.map êm μ := by
    rw [show (Matrix.GeneralLinearGroup.map E.toRingHom : GL (Fin 2) (L ⊗[K] A) → GL (Fin 2) (L ⊗[K] A')) = ⇑êm from (funext hêm).symm]
  have hcont : Continuous (Matrix.GeneralLinearGroup.map E.toRingHom : GL (Fin 2) (L ⊗[K] A) → GL (Fin 2) (L ⊗[K] A')) := by
    rw [← AutomorphicForm.CentAsmLocal.coe_glEquiv E hE hE']; exact ê.continuous
  have hcont' : Continuous (Matrix.GeneralLinearGroup.map E.symm.toRingHom : GL (Fin 2) (L ⊗[K] A') → GL (Fin 2) (L ⊗[K] A)) := by
    rw [← AutomorphicForm.CentAsmLocal.coe_glEquiv E.symm hE' (by simpa using hE)]
    exact (AutomorphicForm.CentAsmLocal.glEquiv E.symm hE' (by simpa using hE)).continuous

  have htorus : ∀ F : GL (Fin 2) (L ⊗[K] A') → ℝ, Measurable F →
      ∫ t, F (t : GL (Fin 2) (L ⊗[K] A')) ∂τ₀ = ∫ t, F (Matrix.GeneralLinearGroup.map E.toRingHom (t : GL (Fin 2) (L ⊗[K] A))) ∂τ := by
    intro F hF
    have h1 : ∫ t, F (t : GL (Fin 2) (L ⊗[K] A')) ∂τ₀ = ∫ g, F g ∂(Measure.map (fun t : twistedCentralizer K L A' σ (Matrix.GeneralLinearGroup.map E.toRingHom δ) => (t : GL (Fin 2) (L ⊗[K] A'))) τ₀) := by
      rw [integral_map continuous_subtype_val.measurable.aemeasurable hF.aestronglyMeasurable]
    have h2 : ∫ t, F (Matrix.GeneralLinearGroup.map E.toRingHom (t : GL (Fin 2) (L ⊗[K] A))) ∂τ =
        ∫ g, F g ∂(Measure.map (fun t : twistedCentralizer K L A σ δ => Matrix.GeneralLinearGroup.map E.toRingHom (t : GL (Fin 2) (L ⊗[K] A))) τ) := by
      rw [integral_map (show Measurable (fun t : twistedCentralizer K L A σ δ => Matrix.GeneralLinearGroup.map E.toRingHom (t : GL (Fin 2) (L ⊗[K] A))) from (hcont.comp continuous_subtype_val).measurable).aemeasurable hF.aestronglyMeasurable]
    rw [h1, h2, hrel]
  have hσ' : ∀ x' : GL (Fin 2) (L ⊗[K] A'), Matrix.GeneralLinearGroup.map E.symm.toRingHom (sigmaGL K L A' σ x') =
      sigmaGL K L A σ (Matrix.GeneralLinearGroup.map E.symm.toRingHom x') :=
    fun x' => map_sigmaGL K L σ A' A E.symm (symm_sigmaTensor K L σ A A' E hEσ) x'
  have hconjA : ∀ x' : GL (Fin 2) (L ⊗[K] A'),
      Matrix.GeneralLinearGroup.map E.symm.toRingHom (x'⁻¹ * Matrix.GeneralLinearGroup.map E.toRingHom δ * sigmaGL K L A' σ x') =
        (Matrix.GeneralLinearGroup.map E.symm.toRingHom x')⁻¹ * δ * sigmaGL K L A σ (Matrix.GeneralLinearGroup.map E.symm.toRingHom x') := by
    intro x'; rw [map_mul, map_mul, map_inv, AutomorphicForm.CentAsmLocal.map_symm_map, hσ']
  have hconjA' : ∀ x : GL (Fin 2) (L ⊗[K] A),
      Matrix.GeneralLinearGroup.map E.toRingHom (x⁻¹ * δ * sigmaGL K L A σ x) =
        (Matrix.GeneralLinearGroup.map E.toRingHom x)⁻¹ * Matrix.GeneralLinearGroup.map E.toRingHom δ * sigmaGL K L A' σ (Matrix.GeneralLinearGroup.map E.toRingHom x) := by
    intro x; rw [map_mul, map_mul, map_inv, map_sigmaGL K L σ A A' E hEσ]

  have hval : ∀ G : GL (Fin 2) (L ⊗[K] A') → ℂ,
      ∫ x', G x' ∂(Measure.map (Matrix.GeneralLinearGroup.map E.toRingHom) μ) = ∫ x, G (Matrix.GeneralLinearGroup.map E.toRingHom x) ∂μ := by
    intro G; rw [hmapμ, MeasureTheory.integral_map_equiv]
    simp_rw [hêm]
  constructor
  · rintro ⟨w, ⟨hw0, hwm, hwcs, hw1⟩, hI⟩
    refine ⟨w ∘ Matrix.GeneralLinearGroup.map E.symm.toRingHom, ⟨fun x => hw0 _, hwm.comp hcont'.measurable, ?_, ?_⟩, ?_⟩
    · have : (w ∘ Matrix.GeneralLinearGroup.map E.symm.toRingHom) = w ∘ ê.symm.toHomeomorph := by
        funext g; exact congrArg w (hês g).symm
      rw [this]; exact hwcs.comp_homeomorph _
    · intro x' hx'
      have hx : f ((Matrix.GeneralLinearGroup.map E.symm.toRingHom x')⁻¹ * δ * sigmaGL K L A σ (Matrix.GeneralLinearGroup.map E.symm.toRingHom x')) ≠ 0 := by
        rwa [Function.comp_apply, hconjA] at hx'
      have h := hw1 _ hx
      show ∫ t, w (Matrix.GeneralLinearGroup.map E.symm.toRingHom ((t : GL (Fin 2) (L ⊗[K] A')) * x')) ∂τ₀ = 1
      rw [htorus (fun g' => w (Matrix.GeneralLinearGroup.map E.symm.toRingHom (g' * x'))) (hwm.comp (hcont'.comp (continuous_id.mul continuous_const)).measurable)]
      simp_rw [map_mul, AutomorphicForm.CentAsmLocal.map_symm_map]
      exact h
    · rw [hI, hval]
      simp only [Function.comp_apply, hconjA, AutomorphicForm.CentAsmLocal.map_symm_map]
  · rintro ⟨w', ⟨hw0, hwm, hwcs, hw1⟩, hI⟩
    refine ⟨w' ∘ Matrix.GeneralLinearGroup.map E.toRingHom, ⟨fun x => hw0 _, hwm.comp hcont.measurable, ?_, ?_⟩, ?_⟩
    · have : (w' ∘ Matrix.GeneralLinearGroup.map E.toRingHom) = w' ∘ ê.toHomeomorph := by
        funext g; exact congrArg w' (hê g).symm
      rw [this]; exact hwcs.comp_homeomorph _
    · intro x hx
      have hx' : (f ∘ Matrix.GeneralLinearGroup.map E.symm.toRingHom)
          ((Matrix.GeneralLinearGroup.map E.toRingHom x)⁻¹ * Matrix.GeneralLinearGroup.map E.toRingHom δ * sigmaGL K L A' σ (Matrix.GeneralLinearGroup.map E.toRingHom x)) ≠ 0 := by
        rw [Function.comp_apply, ← hconjA', AutomorphicForm.CentAsmLocal.map_symm_map]; exact hx
      have h := hw1 _ hx'
      rw [htorus (fun g' => w' (g' * Matrix.GeneralLinearGroup.map E.toRingHom x)) (hwm.comp (continuous_id.mul continuous_const).measurable)] at h
      simp_rw [← map_mul] at h
      exact h
    · rw [hI, hval]
      simp only [Function.comp_apply, hconjA, AutomorphicForm.CentAsmLocal.map_symm_map]

theorem image_mem_nhds_scalar (he : Continuous e) (he' : Continuous e.symm) (c : Aˣ) (V : Set (GL (Fin 2) A))
    (hV : V ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) :
    Matrix.GeneralLinearGroup.map e.toRingHom '' V ∈
      nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (e : A →* A') c)) := by
  let ê := AutomorphicForm.CentAsmLocal.glEquiv e he he'
  have hco : (⇑ê : GL (Fin 2) A → GL (Fin 2) A') = Matrix.GeneralLinearGroup.map e.toRingHom :=
    AutomorphicForm.CentAsmLocal.coe_glEquiv e he he'
  rw [← hco, ← AutomorphicForm.CentAsmLocal.map_scalar e c, ← AutomorphicForm.CentAsmLocal.glEquiv_apply e he he']
  exact ê.toHomeomorph.isOpenMap.image_mem_nhds hV

end Measures
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.FDTEF P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CasmGram P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.P2mGramSide"

section Field
variable (A : Type) [Field A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
  [LocallyCompactSpace A] [SecondCountableTopology A]

theorem isOrbitalIntegralOn_scalar_unique_field (c : Aˣ)
    (μ : @Measure (GL (Fin 2) A) (glBorelOf A)) (hμ : @Measure.IsHaarMeasure _ _ _ (glBorelOf A) μ)
    (τ : @Measure (Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) A)))
      (centralizerBorel A (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel A _) τ)
    (f : GL (Fin 2) A → ℂ) (I I' : ℂ)
    (h : IsOrbitalIntegralOn A μ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ f I)
    (h' : IsOrbitalIntegralOn A μ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ f I') : I = I' := by
  letI : MeasurableSpace (GL (Fin 2) A) := glBorelOf A
  letI : MeasurableSpace (Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) A))) :=
    centralizerBorel A _
  haveI : BorelSpace (GL (Fin 2) A) := borelSpace_glBorelOf A
  haveI : BorelSpace (Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) A))) := ⟨rfl⟩
  haveI : SecondCountableTopology (GL (Fin 2) A) := by
    haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) A) :=
      inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → A))
    haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) A)ᵐᵒᵖ :=
      MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
    exact Units.isInducing_embedProduct.secondCountableTopology
  haveI : LocallyCompactSpace (GL (Fin 2) A) := by
    haveI : T2Space (Matrix (Fin 2) (Fin 2) A) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → A))
    haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) A) :=
      inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → A))
    exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : μ.IsHaarMeasure := hμ
  haveI : τ.IsHaarMeasure := hτ

  have htop : Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) A)) = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro x; rw [Subgroup.mem_centralizer_iff]
    rintro m hm; rw [Set.mem_singleton_iff] at hm; rw [hm]
    exact AutomorphicForm.CentAsmLocal.scalar_mul_comm A c x
  let e1 : Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) A)) ≃* GL (Fin 2) A :=
    (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
  have he1 : ∀ s, e1 s = (s : GL (Fin 2) A) := fun s => rfl
  let e0 : Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) A)) ≃ₜ* GL (Fin 2) A :=
    { e1 with
      continuous_toFun := by
        show Continuous fun s => e1 s
        simp only [he1]; exact continuous_subtype_val
      continuous_invFun := by
        have : ∀ g, e1.symm g = ⟨g, htop.symm ▸ Subgroup.mem_top g⟩ := fun g => by
          apply e1.injective; rw [MulEquiv.apply_symm_apply]; rfl
        show Continuous fun g => e1.symm g
        simp only [this]; exact continuous_id.subtype_mk _ }
  have hm0 : Measurable (e0 : _ → GL (Fin 2) A) := e0.continuous.measurable
  have hm0' : Measurable (e0.symm : GL (Fin 2) A → _) := e0.symm.continuous.measurable

  haveI hν : (Measure.map e0 τ).IsHaarMeasure := e0.isHaarMeasure_map τ
  haveI : (Measure.map e0 τ).IsMulRightInvariant :=
    (Matrix.GeneralLinearGroup.isMulRightInvariant_and_isInvInvariant_of_isHaarMeasure_fin_two (Measure.map e0 τ)).1
  haveI hνinv : (Measure.map e0 τ).IsInvInvariant := MeasureTheory.Measure.isInvInvariant_of_isMulRightInvariant _
  have hback : τ = Measure.map e0.symm (Measure.map e0 τ) := by
    rw [Measure.map_map hm0' hm0]
    have : (e0.symm ∘ e0 : _ → _) = id := funext fun t => e0.symm_apply_apply t
    rw [this, Measure.map_id]
  haveI : τ.IsInvInvariant := by
    constructor
    show Measure.map Inv.inv τ = τ
    conv_lhs => rw [hback]
    rw [Measure.map_map measurable_inv hm0',
      show (Inv.inv ∘ e0.symm : GL (Fin 2) A → _) = (e0.symm ∘ Inv.inv) from funext fun t => (map_inv e0.symm t).symm,
      ← Measure.map_map hm0' measurable_inv, Measure.map_inv_eq_self, ← hback]
  haveI : SFinite τ := by rw [hback]; infer_instance
  exact AutomorphicForm.CentAsmLocal.isOrbitalIntegralOn_scalar_unique A c μ τ f I I' h h'

end Field
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.FDTEF P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CasmGram P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.P2mGramSide"

section MatchTransport
variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] (σ : L ≃ₐ[K] L)
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]
  (A' : Type) [CommRing A'] [Algebra K A'] [TopologicalSpace A'] [IsTopologicalRing A']
  (e : A ≃+* A') (E : L ⊗[K] A ≃+* L ⊗[K] A')

private theorem _root_.AutomorphicForm.O6Split.exists_isHaarMeasure_centralizer_backward (he : Continuous e) (he' : Continuous e.symm) (γ : GL (Fin 2) A)
    (τ₀ : @Measure (Subgroup.centralizer ({Matrix.GeneralLinearGroup.map e.toRingHom γ} : Set (GL (Fin 2) A')))
      (centralizerBorel A' (Matrix.GeneralLinearGroup.map e.toRingHom γ)))
    (hτ₀ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel A' _) τ₀) :
    ∃ τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ),
      @Measure.IsHaarMeasure _ _ _ (centralizerBorel A γ) τ ∧
      (letI := glBorelOf A'; letI := centralizerBorel A γ;
        letI := centralizerBorel A' (Matrix.GeneralLinearGroup.map e.toRingHom γ);
        Measure.map (fun t : Subgroup.centralizer ({Matrix.GeneralLinearGroup.map e.toRingHom γ} : Set (GL (Fin 2) A')) => (t : GL (Fin 2) A')) τ₀ =
          Measure.map (fun t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) => Matrix.GeneralLinearGroup.map e.toRingHom (t : GL (Fin 2) A)) τ) := by
  letI : MeasurableSpace (GL (Fin 2) A) := glBorelOf A
  letI : MeasurableSpace (GL (Fin 2) A') := glBorelOf A'
  haveI : BorelSpace (GL (Fin 2) A) := borelSpace_glBorelOf A
  haveI : BorelSpace (GL (Fin 2) A') := borelSpace_glBorelOf A'
  letI : MeasurableSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) := centralizerBorel A γ
  haveI : BorelSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) := ⟨rfl⟩
  let ê := AutomorphicForm.CentAsmLocal.glEquiv e he he'
  have hco : (⇑ê : GL (Fin 2) A → GL (Fin 2) A') = Matrix.GeneralLinearGroup.map e.toRingHom :=
    AutomorphicForm.CentAsmLocal.coe_glEquiv e he he'
  have hx : ê γ = Matrix.GeneralLinearGroup.map e.toRingHom γ := AutomorphicForm.CentAsmLocal.glEquiv_apply e he he' γ
  have aux : ∀ (x : GL (Fin 2) A') (hx : ê γ = x)
      [MeasurableSpace (Subgroup.centralizer ({x} : Set (GL (Fin 2) A')))] [BorelSpace (Subgroup.centralizer ({x} : Set (GL (Fin 2) A')))]
      (τ₀ : Measure (Subgroup.centralizer ({x} : Set (GL (Fin 2) A')))), τ₀.IsHaarMeasure →
      ∃ τ : Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))), τ.IsHaarMeasure ∧
        Measure.map (fun t : Subgroup.centralizer ({x} : Set (GL (Fin 2) A')) => (t : GL (Fin 2) A')) τ₀ =
          Measure.map (fun t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) => ê (t : GL (Fin 2) A)) τ := by
    intro x hx _ _ τ₀ hτ₀; subst hx
    obtain ⟨τ, h1, h2, -⟩ := AutomorphicForm.CentAsmLocal.exists_isHaarMeasure_centralizer_backward ê γ τ₀
    exact ⟨τ, h1, h2⟩
  letI : MeasurableSpace (Subgroup.centralizer ({Matrix.GeneralLinearGroup.map e.toRingHom γ} : Set (GL (Fin 2) A'))) :=
    centralizerBorel A' _
  haveI : BorelSpace (Subgroup.centralizer ({Matrix.GeneralLinearGroup.map e.toRingHom γ} : Set (GL (Fin 2) A'))) := ⟨rfl⟩
  haveI : τ₀.IsHaarMeasure := hτ₀
  obtain ⟨τ, h1, h2⟩ := aux _ hx τ₀ hτ₀
  refine ⟨τ, h1, ?_⟩
  rw [h2, hco]

p2m_export "AutomorphicForm.O6Split" "exists_isHaarMeasure_centralizer_backward"

theorem hmatch_transport (he : Continuous e) (he' : Continuous e.symm) (hE : Continuous E) (hE' : Continuous E.symm)
    (hEσ : ∀ z, E (sigmaTensor K L A σ z) = sigmaTensor K L A' σ (E z))
    (hEe : ∀ g : GL (Fin 2) A, Matrix.GeneralLinearGroup.map E.toRingHom (toTensorGL K L A g) =
      toTensorGL K L A' (Matrix.GeneralLinearGroup.map e.toRingHom g))
    (μ : @Measure (GL (Fin 2) A) (glBorelOf A))
    (μ' : @Measure (GL (Fin 2) (L ⊗[K] A)) (glBorelOf (L ⊗[K] A)))
    (φ : GL (Fin 2) (L ⊗[K] A) → ℂ) (f : GL (Fin 2) A → ℂ) (c : Aˣ)
    (hmatch : ∃ V ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
        ∀ δ : GL (Fin 2) (L ⊗[K] A), IsRegularSemisimple (normString K L A σ δ) →
        ∀ γ ∈ V, IsRegularSemisimple γ →
        ∀ y : GL (Fin 2) (L ⊗[K] A), IsNormConjugator K L A σ γ δ y →
        ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ))
          (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ)),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel A γ) τ →
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L A σ δ) τ' →
          Coupled K L A σ γ δ y τ τ' →
          ∀ I I' : ℂ, IsTwistedOrbitalIntegralOn K L A σ μ' δ τ' φ I' →
            IsOrbitalIntegralOn A μ γ τ f I → I' = I) :
    ∃ V' ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (e : A →* A') c)),
        ∀ δ' : GL (Fin 2) (L ⊗[K] A'), IsRegularSemisimple (normString K L A' σ δ') →
        ∀ γ' ∈ V', IsRegularSemisimple γ' →
        ∀ y' : GL (Fin 2) (L ⊗[K] A'), IsNormConjugator K L A' σ γ' δ' y' →
        ∀ (τ₁ : @Measure (Subgroup.centralizer ({γ'} : Set (GL (Fin 2) A'))) (centralizerBorel A' γ'))
          (τ₁' : @Measure (twistedCentralizer K L A' σ δ') (twistedCentralizerBorel K L A' σ δ')),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel A' γ') τ₁ →
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L A' σ δ') τ₁' →
          Coupled K L A' σ γ' δ' y' τ₁ τ₁' →
          ∀ I I' : ℂ,
            IsTwistedOrbitalIntegralOn K L A' σ
              (@Measure.map _ _ (glBorelOf (L ⊗[K] A)) (glBorelOf (L ⊗[K] A')) (Matrix.GeneralLinearGroup.map E.toRingHom) μ')
              δ' τ₁' (φ ∘ Matrix.GeneralLinearGroup.map E.symm.toRingHom) I' →
            IsOrbitalIntegralOn A' (@Measure.map _ _ (glBorelOf A) (glBorelOf A') (Matrix.GeneralLinearGroup.map e.toRingHom) μ)
              γ' τ₁ (f ∘ Matrix.GeneralLinearGroup.map e.symm.toRingHom) I → I' = I := by
  obtain ⟨V, hV, hm⟩ := hmatch
  refine ⟨Matrix.GeneralLinearGroup.map e.toRingHom '' V, image_mem_nhds_scalar A A' e he he' c V hV, ?_⟩
  intro δ' hδ'reg γ' hγ'V hγ'reg y' hN' τ₁ τ₁' hτ₁ hτ₁' hC' I I' hI' hI

  obtain ⟨γ, hγV, rfl⟩ := hγ'V
  obtain ⟨δ, rfl⟩ : ∃ δ, δ' = Matrix.GeneralLinearGroup.map E.toRingHom δ :=
    ⟨_, (AutomorphicForm.CentAsmLocal.map_map_symm E δ').symm⟩
  obtain ⟨y, rfl⟩ : ∃ y, y' = Matrix.GeneralLinearGroup.map E.toRingHom y :=
    ⟨_, (AutomorphicForm.CentAsmLocal.map_map_symm E y').symm⟩
  have hγreg : IsRegularSemisimple γ := (isRegularSemisimple_map_iff A A' e γ).1 hγ'reg
  have hδreg : IsRegularSemisimple (normString K L A σ δ) := by
    rw [← map_normString K L σ A A' E hEσ] at hδ'reg
    have h2 := isRegularSemisimple_map_of_ringHom E.symm.toRingHom _ hδ'reg
    rwa [AutomorphicForm.CentAsmLocal.map_symm_map] at h2
  obtain ⟨hNiff, hCiff⟩ :=
    AutomorphicForm.isNormConjugator_map_iff_and_coupled_map_iff_of_ringEquiv (σ := σ) (σ' := σ) rfl
      e he he' E hE hE' hEσ hEe γ δ y
  have hN : IsNormConjugator K L A σ γ δ y := hNiff.2 hN'

  obtain ⟨τ, hτ, hτrel⟩ := exists_isHaarMeasure_centralizer_backward A A' e he he' γ τ₁ hτ₁
  obtain ⟨-, -, hTTback⟩ :=
    AutomorphicForm.isTwistedOrbitalIntegralOn_map_of_ringEquiv_and_isHaarMeasure_map (σ := σ) (σ' := σ) E hE hE' hEσ μ' δ
  obtain ⟨τ', hτ', hτ'rel⟩ := hTTback τ₁' hτ₁'
  have hC : Coupled K L A σ γ δ y τ τ' := (hCiff τ τ₁ τ' τ₁' hτrel hτ'rel).2 hC'

  have hIA : IsOrbitalIntegralOn A μ γ τ f I :=
    (isOrbitalIntegralOn_map_iff A A' e he he' γ μ τ τ₁ hτrel f I).2 hI
  have hI'A : IsTwistedOrbitalIntegralOn K L A σ μ' δ τ' φ I' :=
    (isTwistedOrbitalIntegralOn_map_iff K L σ A A' E hE hE' hEσ δ μ' τ' τ₁' hτ'rel φ I').2 hI'
  exact hm δ hδreg γ hγV hγreg y hN τ τ' hτ hτ' hC I I' hI'A hIA

end MatchTransport
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.FDTEF P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CasmGram P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.P2mGramSide"

end AutomorphicForm.O6Split
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.FDTEF P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CasmGram P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.P2mGramSide"
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.FDTEF P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CasmGram P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.P2mGramSide"

namespace AutomorphicForm
p2m_export "AutomorphicForm" "isTopologicalRing_tensor t2Space_tensor locallyCompactSpace_tensor isTopologicalGroup_tensorGL t2Space_tensorGL locallyCompactSpace_tensorGL glBorelOf borelSpace_glBorelOf centralizerBorel toTensorGL sigmaTensor sigmaGL normString IsSigmaConjugate IsNormConjugator IsNormOf twistedCentralizer twistedCentralizerBorel IsSectionFnOn IsOrbitalIntegralOn IsTwistedSectionFnOn IsTwistedOrbitalIntegralOn Coupled AreMatchingOn archHaarK archHaarL archIdent archIdentGL AreMatchingArch IsRegularSemisimple archEntries_apply IsArchTestFactor sigmaCentralizer mem_sigmaCentralizer_iff SplitPlace.psi SplitPlace.psiEquiv SplitPlace.psiEquiv_apply SplitPlace.psiEquiv_symm_const SplitPlace.psiGL exists_mulEquiv_generalLinearGroup_tensorProduct_infiniteAdeleRing_pi exists_ringEquiv_tensorProduct_infiniteAdeleRing_pi_forall_tmul archIdent_tmul_apply exists_continuous_isSectionFnOn_and_isOrbitalIntegralOn_iff_completion_of_isRegularSemisimple exists_isTwistedSectionFnOn_and_continuous_completion_of_isRegularSemisimple_normString exists_isTwistedSectionFnOn_and_continuous_completion_of_isSigmaConjugate_scalar_of_prime semilocal_central_transfer_of_forall_oneplace_of_referenceMeasures exists_isNormConjugator_and_coupled_of_gram_of_algHom_real exists_isNormConjugator_and_coupled_of_gram_of_algHom_complex exists_isNormConjugator_and_coupled_of_gram_conjAe_of_pos isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar map_centralizer_map_ringEquiv_pi_eq_smul_gram_of_infiniteAdeleRing map_twistedCentralizer_map_ringEquiv_pi_eq_smul_gram_of_infiniteAdeleRing mem_span_map_ringEquiv_pi_iff_of_span_eq_range_includeRight mem_span_map_ringEquiv_pi_iff_of_span_eq_setOf_mul_eq_mul_map_sigmaTensor exists_gram_map_of_ringEquiv_of_exists_gram exists_ringEquiv_tensor_completion_complex_of_isRamified isTwistedOrbitalIntegralOn_map_of_ringEquiv_and_isHaarMeasure_map isNormConjugator_map_iff_and_coupled_map_iff_of_ringEquiv isOrbitalIntegralOn_map_generalLinearGroup_map_of_ringEquiv isHaarMeasure_map_and_exists_isHaarMeasure_centralizer_of_ringEquiv pos_and_exists_coupled_toTensorGL_scalar_one_iff_of_coupled_scalar_conjAe exists_ringEquiv_tensor_baseChange_of_ringEquiv isOrbitalIntegralOn_scalar_neg_of_isTwistedOrbitalIntegralOn_conjAe_of_gram_of_nhds_forall_isNormConjugator_of_neg exists_isSigmaConjugate_scalar_of_isNormConjugator_scalar_of_algHom_of_prime exists_isTwistedSectionFnOn_and_continuous_completion_of_not_isSigmaConjugate_scalar_of_finrank_eq_two exists_isSigmaConjugate_scalar_conjAe_iff_pos_of_isNormConjugator_scalar"
namespace CentAsmLocal
p2m_open "AutomorphicForm"

open MeasureTheory NumberField NumberField.InfinitePlace
open scoped TensorProduct TensorProduct.RightActions NumberField.LiesOver

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

section Tools

variable {R S : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]

omit [IsTopologicalRing R] [IsTopologicalRing S] in
theorem continuous_generalLinearGroup_map (e : R →+* S) (he : Continuous e) :
    Continuous (Matrix.GeneralLinearGroup.map e : GL (Fin 2) R → GL (Fin 2) S) := by
  refine Continuous.units_map _ ?_
  change Continuous fun M : Matrix (Fin 2) (Fin 2) R => M.map e
  exact continuous_id.matrix_map he

omit [TopologicalSpace R] [IsTopologicalRing R] [TopologicalSpace S] [IsTopologicalRing S] in
theorem map_symm_map' (e : R ≃+* S) (g : GL (Fin 2) R) :
    Matrix.GeneralLinearGroup.map e.symm.toRingHom (Matrix.GeneralLinearGroup.map e.toRingHom g) = g := by
  ext i j; simp

omit [TopologicalSpace R] [IsTopologicalRing R] [TopologicalSpace S] [IsTopologicalRing S] in
theorem map_map_symm' (e : R ≃+* S) (g' : GL (Fin 2) S) :
    Matrix.GeneralLinearGroup.map e.toRingHom (Matrix.GeneralLinearGroup.map e.symm.toRingHom g') = g' := by
  ext i j; simp

omit [IsTopologicalRing R] [IsTopologicalRing S] in

def mapSymmHomeo (e : R ≃+* S) (he : Continuous e) (he' : Continuous e.symm) : GL (Fin 2) S ≃ₜ GL (Fin 2) R where
  toFun := Matrix.GeneralLinearGroup.map e.symm.toRingHom
  invFun := Matrix.GeneralLinearGroup.map e.toRingHom
  left_inv := map_map_symm' e
  right_inv := map_symm_map' e
  continuous_toFun := continuous_generalLinearGroup_map e.symm.toRingHom he'
  continuous_invFun := continuous_generalLinearGroup_map e.toRingHom he

omit [IsTopologicalRing R] [IsTopologicalRing S] in
theorem hasCompactSupport_comp_map_symm {β : Type} [Zero β] (e : R ≃+* S) (he : Continuous e)
    (he' : Continuous e.symm) (f : GL (Fin 2) R → β) (hf : HasCompactSupport f) :
    HasCompactSupport (f ∘ Matrix.GeneralLinearGroup.map e.symm.toRingHom) :=
  hf.comp_homeomorph (mapSymmHomeo e he he')

theorem contDiff_ofReal_entries :
    ContDiff ℝ (⊤ : ℕ∞) (fun m : Fin 2 → Fin 2 → ℝ => fun i j => ((m i j : ℝ) : ℂ)) :=
  contDiff_pi.2 fun i => contDiff_pi.2 fun j =>
    Complex.ofRealCLM.contDiff.comp (contDiff_apply_apply ℝ ℝ i j)

end Tools
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.FDTEF P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CasmGram P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.P2mGramSide"

theorem f_model_real (v : InfinitePlace K) (hv : v.IsReal)
    (he : Continuous (Completion.ringEquivRealOfIsReal hv))
    (he' : Continuous (Completion.ringEquivRealOfIsReal hv).symm)
    (f : GL (Fin 2) v.Completion → ℂ)
    (hf : (∃ F₁ : (Fin 2 → Fin 2 → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F₁ ∧
        ∀ g, f g = F₁ (epsK K v g)) ∧ HasCompactSupport f) :
    (∃ F : (Fin 2 → Fin 2 → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F ∧
      ∀ g, (f ∘ Matrix.GeneralLinearGroup.map (Completion.ringEquivRealOfIsReal hv).symm.toRingHom) g =
        F (fun i j => (g : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧
      HasCompactSupport (f ∘ Matrix.GeneralLinearGroup.map (Completion.ringEquivRealOfIsReal hv).symm.toRingHom) := by
  obtain ⟨⟨F₁, hF₁, hfF⟩, hfc⟩ := hf
  refine ⟨⟨fun m => F₁ (fun i j => ((m i j : ℝ) : ℂ)), hF₁.comp contDiff_ofReal_entries, fun g => ?_⟩,
    hasCompactSupport_comp_map_symm _ he he' f hfc⟩
  rw [Function.comp_apply, hfF]
  congr 1
  funext i j
  show Completion.extensionEmbedding v ((Completion.ringEquivRealOfIsReal hv).symm ((g : Matrix (Fin 2) (Fin 2) ℝ) i j)) = _
  set a := (Completion.ringEquivRealOfIsReal hv).symm ((g : Matrix (Fin 2) (Fin 2) ℝ) i j) with ha
  have h1 : (g : Matrix (Fin 2) (Fin 2) ℝ) i j = Completion.ringEquivRealOfIsReal hv a := by
    rw [ha, RingEquiv.apply_symm_apply]
  show Completion.extensionEmbedding v a = (((g : Matrix (Fin 2) (Fin 2) ℝ) i j : ℝ) : ℂ)
  rw [h1, Completion.ringEquivRealOfIsReal_apply, Completion.extensionEmbeddingOfIsReal_apply]

theorem f_model_complex (v : InfinitePlace K) (hv : v.IsComplex)
    (he : Continuous (Completion.ringEquivComplexOfIsComplex hv))
    (he' : Continuous (Completion.ringEquivComplexOfIsComplex hv).symm)
    (f : GL (Fin 2) v.Completion → ℂ)
    (hf : (∃ F₁ : (Fin 2 → Fin 2 → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F₁ ∧
        ∀ g, f g = F₁ (epsK K v g)) ∧ HasCompactSupport f) :
    (∃ F : (Fin 2 → Fin 2 → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F ∧
      ∀ g, (f ∘ Matrix.GeneralLinearGroup.map (Completion.ringEquivComplexOfIsComplex hv).symm.toRingHom) g =
        F (fun i j => (g : Matrix (Fin 2) (Fin 2) ℂ) i j)) ∧
      HasCompactSupport (f ∘ Matrix.GeneralLinearGroup.map (Completion.ringEquivComplexOfIsComplex hv).symm.toRingHom) := by
  obtain ⟨⟨F₁, hF₁, hfF⟩, hfc⟩ := hf
  refine ⟨⟨F₁, hF₁, fun g => ?_⟩, hasCompactSupport_comp_map_symm _ he he' f hfc⟩
  rw [Function.comp_apply, hfF]
  congr 1
  funext i j
  show Completion.extensionEmbedding v ((Completion.ringEquivComplexOfIsComplex hv).symm ((g : Matrix (Fin 2) (Fin 2) ℂ) i j)) = _
  set a := (Completion.ringEquivComplexOfIsComplex hv).symm ((g : Matrix (Fin 2) (Fin 2) ℂ) i j) with ha
  have h1 : (g : Matrix (Fin 2) (Fin 2) ℂ) i j = Completion.ringEquivComplexOfIsComplex hv a := by
    rw [ha, RingEquiv.apply_symm_apply]
  show Completion.extensionEmbedding v a = (g : Matrix (Fin 2) (Fin 2) ℂ) i j
  rw [h1, Completion.ringEquivComplexOfIsComplex_apply]

theorem contDiff_coord {A' : Type} [NormedAddCommGroup A'] [NormedSpace ℝ A'] (n : ℕ) (i j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun m : Fin n → Fin 2 → Fin 2 → A' => fun k => m k i j) :=
  contDiff_pi.2 fun k => (contDiff_apply_apply ℝ A' i j).comp (contDiff_apply ℝ (Fin 2 → Fin 2 → A') k)

theorem phi_model_real (hprime : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : InfinitePlace K) (hv : v.IsReal)
    (he' : Continuous (Completion.ringEquivRealOfIsReal hv).symm)
    [Algebra K ℝ] (ι : L →ₐ[K] ℝ)
    (E : L ⊗[K] v.Completion ≃+* L ⊗[K] ℝ) (hE : Continuous E) (hE' : Continuous E.symm)
    (hEt : ∀ (x : L) (a : v.Completion), E (x ⊗ₜ a) = x ⊗ₜ (Completion.ringEquivRealOfIsReal hv a))
    (φ : GL (Fin 2) (L ⊗[K] v.Completion) → ℂ)
    (hφ : (∃ Φ₁ : (Fin 2 → Fin 2 → (v.Extension L) → ℂ) → ℂ,
        ContDiff ℝ (⊤ : ℕ∞) Φ₁ ∧ ∀ g, φ g = Φ₁ (epsL K L v g)) ∧ HasCompactSupport φ) :
    (∃ Φ : (Fin (Module.finrank K L) → Fin 2 → Fin 2 → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
      ∀ g, (φ ∘ Matrix.GeneralLinearGroup.map E.symm.toRingHom) g = Φ (fun k i j =>
        ((SplitPlace.psiGL ℝ σ ι hprime hσ g k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧
      HasCompactSupport (φ ∘ Matrix.GeneralLinearGroup.map E.symm.toRingHom) := by
  haveI : IsTopologicalRing (L ⊗[K] v.Completion) := isTopologicalRing_tensor K L v.Completion
  haveI : IsTopologicalRing (L ⊗[K] ℝ) := isTopologicalRing_tensor K L ℝ
  obtain ⟨⟨Φ₁, hΦ₁, hφΦ⟩, hφc⟩ := hφ
  have hS : ∀ w : v.Extension L, ∃ S : (Fin (Module.finrank K L) → ℝ) →L[ℝ] ℂ, ∀ z : L ⊗[K] ℝ,
      S (SplitPlace.psi K L ℝ σ ι z) =
        (letI : w.1.1.LiesOver v.1 := M4aHerbrand.ArchSemilocal.liesOver_of_comap_eq w.2
         Completion.extensionEmbedding w.1 (M4aHerbrand.ArchSemilocal.psiFactor v w.1
           (_root_.Algebra.TensorProduct.comm K L v.Completion (E.symm z)))) := by
    intro w
    letI iLO : w.1.1.LiesOver v.1 := M4aHerbrand.ArchSemilocal.liesOver_of_comap_eq w.2
    let Read : L ⊗[K] ℝ →+* ℂ := (Completion.extensionEmbedding w.1).comp
      ((M4aHerbrand.ArchSemilocal.psiFactor v w.1).toRingHom.comp
        ((_root_.Algebra.TensorProduct.comm K L v.Completion).toRingEquiv.toRingHom.comp E.symm.toRingHom))
    have hRead : ∀ z, Read z = Completion.extensionEmbedding w.1 (M4aHerbrand.ArchSemilocal.psiFactor v w.1
        (_root_.Algebra.TensorProduct.comm K L v.Completion (E.symm z))) := fun z => rfl
    let Sr : (Fin (Module.finrank K L) → ℝ) →+* ℂ :=
      Read.comp (SplitPlace.psiEquiv ℝ σ ι hprime hσ).symm.toRingEquiv.toRingHom
    have hSr : ∀ t, Sr t = Read ((SplitPlace.psiEquiv ℝ σ ι hprime hσ).symm t) := fun t => rfl

    let T : ℝ →+* ℂ := (Completion.extensionEmbedding w.1).comp
      ((algebraMap v.Completion w.1.Completion).comp (Completion.ringEquivRealOfIsReal hv).symm.toRingHom)
    have hTc : Continuous T :=
      (Completion.isometry_extensionEmbedding w.1).continuous.comp
        ((continuous_algebraMap v.Completion w.1.Completion).comp he')
    have hT : T = Complex.ofRealHom := Complex.ringHom_eq_ofReal_of_continuous hTc
    have hfix : ∀ r : ℝ, Sr (fun _ => r) = (r : ℂ) := by
      intro r
      rw [hSr, SplitPlace.psiEquiv_symm_const, hRead]
      have h1 : E.symm ((1 : L) ⊗ₜ[K] r) = (1 : L) ⊗ₜ[K] ((Completion.ringEquivRealOfIsReal hv).symm r) := by
        apply E.injective; rw [E.apply_symm_apply, hEt, RingEquiv.apply_symm_apply]
      rw [h1, _root_.Algebra.TensorProduct.comm_tmul, M4aHerbrand.ArchSemilocal.psiFactor_tmul, map_one, mul_one]
      exact congrArg (fun f : ℝ →+* ℂ => f r) hT
    have hsmul : ∀ (r : ℝ) (x : Fin (Module.finrank K L) → ℝ), Sr (r • x) = (r : ℂ) * Sr x := by
      intro r x
      have : r • x = (fun _ => r) * x := by funext k; simp [smul_eq_mul]
      rw [this, map_mul, hfix]
    let Sl : (Fin (Module.finrank K L) → ℝ) →ₗ[ℝ] ℂ :=
      { toFun := Sr, map_add' := map_add Sr
        map_smul' := fun r x => by rw [RingHom.id_apply, Complex.real_smul]; exact hsmul r x }
    refine ⟨LinearMap.toContinuousLinearMap Sl, fun z => ?_⟩
    show Sr (SplitPlace.psi K L ℝ σ ι z) = Read z
    rw [hSr, ← SplitPlace.psiEquiv_apply ℝ σ ι hprime hσ z, AlgEquiv.symm_apply_apply]
  choose S hS' using hS
  refine ⟨⟨fun m => Φ₁ (fun i j w => S w (fun k => m k i j)), ?_, fun g => ?_⟩,
    hasCompactSupport_comp_map_symm E hE hE' φ hφc⟩
  · exact hΦ₁.comp (contDiff_pi.2 fun i => contDiff_pi.2 fun j => contDiff_pi.2 fun w =>
      (S w).contDiff.comp (contDiff_coord (Module.finrank K L) i j))
  · rw [Function.comp_apply, hφΦ]
    congr 1
    funext i j w
    exact (hS' w ((g : Matrix (Fin 2) (Fin 2) (L ⊗[K] ℝ)) i j)).symm

theorem phi_model_complex (hprime : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : InfinitePlace K) (hv : v.IsComplex)
    (he' : Continuous (Completion.ringEquivComplexOfIsComplex hv).symm)
    [Algebra K ℂ] (ι : L →ₐ[K] ℂ)
    (E : L ⊗[K] v.Completion ≃+* L ⊗[K] ℂ) (hE : Continuous E) (hE' : Continuous E.symm)
    (hEt : ∀ (x : L) (a : v.Completion), E (x ⊗ₜ a) = x ⊗ₜ (Completion.ringEquivComplexOfIsComplex hv a))
    (φ : GL (Fin 2) (L ⊗[K] v.Completion) → ℂ)
    (hφ : (∃ Φ₁ : (Fin 2 → Fin 2 → (v.Extension L) → ℂ) → ℂ,
        ContDiff ℝ (⊤ : ℕ∞) Φ₁ ∧ ∀ g, φ g = Φ₁ (epsL K L v g)) ∧ HasCompactSupport φ) :
    (∃ Φ : (Fin (Module.finrank K L) → Fin 2 → Fin 2 → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
      ∀ g, (φ ∘ Matrix.GeneralLinearGroup.map E.symm.toRingHom) g = Φ (fun k i j =>
        ((SplitPlace.psiGL ℂ σ ι hprime hσ g k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) i j)) ∧
      HasCompactSupport (φ ∘ Matrix.GeneralLinearGroup.map E.symm.toRingHom) := by
  haveI : IsTopologicalRing (L ⊗[K] v.Completion) := isTopologicalRing_tensor K L v.Completion
  haveI : IsTopologicalRing (L ⊗[K] ℂ) := isTopologicalRing_tensor K L ℂ
  obtain ⟨⟨Φ₁, hΦ₁, hφΦ⟩, hφc⟩ := hφ
  have hS : ∀ w : v.Extension L, ∃ S : (Fin (Module.finrank K L) → ℂ) →L[ℝ] ℂ, ∀ z : L ⊗[K] ℂ,
      S (SplitPlace.psi K L ℂ σ ι z) =
        (letI : w.1.1.LiesOver v.1 := M4aHerbrand.ArchSemilocal.liesOver_of_comap_eq w.2
         Completion.extensionEmbedding w.1 (M4aHerbrand.ArchSemilocal.psiFactor v w.1
           (_root_.Algebra.TensorProduct.comm K L v.Completion (E.symm z)))) := by
    intro w
    letI iLO : w.1.1.LiesOver v.1 := M4aHerbrand.ArchSemilocal.liesOver_of_comap_eq w.2
    let Read : L ⊗[K] ℂ →+* ℂ := (Completion.extensionEmbedding w.1).comp
      ((M4aHerbrand.ArchSemilocal.psiFactor v w.1).toRingHom.comp
        ((_root_.Algebra.TensorProduct.comm K L v.Completion).toRingEquiv.toRingHom.comp E.symm.toRingHom))
    have hRead : ∀ z, Read z = Completion.extensionEmbedding w.1 (M4aHerbrand.ArchSemilocal.psiFactor v w.1
        (_root_.Algebra.TensorProduct.comm K L v.Completion (E.symm z))) := fun z => rfl
    let Sr : (Fin (Module.finrank K L) → ℂ) →+* ℂ :=
      Read.comp (SplitPlace.psiEquiv ℂ σ ι hprime hσ).symm.toRingEquiv.toRingHom
    have hSr : ∀ t, Sr t = Read ((SplitPlace.psiEquiv ℂ σ ι hprime hσ).symm t) := fun t => rfl

    let T : ℂ →+* ℂ := (Completion.extensionEmbedding w.1).comp
      ((algebraMap v.Completion w.1.Completion).comp (Completion.ringEquivComplexOfIsComplex hv).symm.toRingHom)
    have hTc : Continuous T :=
      (Completion.isometry_extensionEmbedding w.1).continuous.comp
        ((continuous_algebraMap v.Completion w.1.Completion).comp he')
    have hTr : ∀ r : ℝ, T (r : ℂ) = (r : ℂ) := by
      intro r
      rcases Complex.ringHom_eq_id_or_conj_of_continuous hTc with h | h
      · rw [h]; rfl
      · rw [h]; exact Complex.conj_ofReal r
    have hfix : ∀ r : ℝ, Sr (fun _ => (r : ℂ)) = (r : ℂ) := by
      intro r
      rw [hSr, SplitPlace.psiEquiv_symm_const, hRead]
      have h1 : E.symm ((1 : L) ⊗ₜ[K] (r : ℂ)) = (1 : L) ⊗ₜ[K] ((Completion.ringEquivComplexOfIsComplex hv).symm r) := by
        apply E.injective; rw [E.apply_symm_apply, hEt, RingEquiv.apply_symm_apply]
      rw [h1, _root_.Algebra.TensorProduct.comm_tmul, M4aHerbrand.ArchSemilocal.psiFactor_tmul, map_one, mul_one]
      exact hTr r
    have hsmul : ∀ (r : ℝ) (x : Fin (Module.finrank K L) → ℂ), Sr (r • x) = (r : ℂ) * Sr x := by
      intro r x
      have : r • x = (fun _ => (r : ℂ)) * x := by funext k; simp [Complex.real_smul]
      rw [this, map_mul, hfix]
    let Sl : (Fin (Module.finrank K L) → ℂ) →ₗ[ℝ] ℂ :=
      { toFun := Sr, map_add' := map_add Sr
        map_smul' := fun r x => by rw [RingHom.id_apply, Complex.real_smul]; exact hsmul r x }
    refine ⟨LinearMap.toContinuousLinearMap Sl, fun z => ?_⟩
    show Sr (SplitPlace.psi K L ℂ σ ι z) = Read z
    rw [hSr, ← SplitPlace.psiEquiv_apply ℂ σ ι hprime hσ z, AlgEquiv.symm_apply_apply]
  choose S hS' using hS
  refine ⟨⟨fun m => Φ₁ (fun i j w => S w (fun k => m k i j)), ?_, fun g => ?_⟩,
    hasCompactSupport_comp_map_symm E hE hE' φ hφc⟩
  · exact hΦ₁.comp (contDiff_pi.2 fun i => contDiff_pi.2 fun j => contDiff_pi.2 fun w =>
      (S w).contDiff.comp (contDiff_coord (Module.finrank K L) i j))
  · rw [Function.comp_apply, hφΦ]
    congr 1
    funext i j w
    exact (hS' w ((g : Matrix (Fin 2) (Fin 2) (L ⊗[K] ℂ)) i j)).symm

set_option maxHeartbeats 3200000 in
theorem heng_split_real
    (hprime : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : InfinitePlace K) (hv : v.IsReal) (hsplit : ∀ w : InfinitePlace L, w.comap (algebraMap K L) = v → ¬ w.IsRamified K)
    (hsplitR : ∀
      (hσ : σ ≠ 1) [Algebra K ℝ] (ι : L →ₐ[K] ℝ)
      (μA : @Measure (GL (Fin 2) ℝ) (glBorelOf ℝ))
      (hμA : @Measure.IsHaarMeasure _ _ _ (glBorelOf ℝ) μA)
      (μL : @Measure (GL (Fin 2) (L ⊗[K] ℝ)) (glBorelOf (L ⊗[K] ℝ)))
      (hμL : @Measure.IsHaarMeasure _ _ _ (glBorelOf (L ⊗[K] ℝ)) μL)
      (φ : GL (Fin 2) (L ⊗[K] ℝ) → ℂ)
      (hφ : (∃ Φ : (Fin (Module.finrank K L) → Fin 2 → Fin 2 → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
        ∀ g, φ g = Φ (fun k i j =>
          ((SplitPlace.psiGL ℝ σ ι hprime hσ g k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧
        HasCompactSupport φ)
      (f : GL (Fin 2) ℝ → ℂ)
      (hf : (∃ F : (Fin 2 → Fin 2 → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F ∧
        ∀ g, f g = F (fun i j => (g : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧ HasCompactSupport f)
      (c : ℝˣ)
      (hmatch : ∃ V ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
        ∀ δ : GL (Fin 2) (L ⊗[K] ℝ), IsRegularSemisimple (normString K L ℝ σ δ) →
        ∀ γ ∈ V, IsRegularSemisimple γ →
        ∀ y : GL (Fin 2) (L ⊗[K] ℝ), IsNormConjugator K L ℝ σ γ δ y →
        ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℝ))) (centralizerBorel ℝ γ))
          (τ' : @Measure (twistedCentralizer K L ℝ σ δ) (twistedCentralizerBorel K L ℝ σ δ)),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ γ) τ →
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L ℝ σ δ) τ' →
          Coupled K L ℝ σ γ δ y τ τ' →
          ∀ I I' : ℂ, IsTwistedOrbitalIntegralOn K L ℝ σ μL δ τ' φ I' →
            IsOrbitalIntegralOn ℝ μA γ τ f I → I' = I),
      ∀ δ y : GL (Fin 2) (L ⊗[K] ℝ),
        IsNormConjugator K L ℝ σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y →
        ∀ (τ : @Measure (Subgroup.centralizer
              ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ)))
              (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
          (τ' : @Measure (twistedCentralizer K L ℝ σ δ) (twistedCentralizerBorel K L ℝ σ δ)),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) τ →
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L ℝ σ δ) τ' →
          Coupled K L ℝ σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y τ τ' →
          ∀ I' : ℂ, IsTwistedOrbitalIntegralOn K L ℝ σ μL δ τ' φ I' →
            IsOrbitalIntegralOn ℝ μA (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ f I')
    (μ : @Measure (GL (Fin 2) v.Completion) (glBorelOf v.Completion))
    (hμ : @Measure.IsHaarMeasure _ _ _ (glBorelOf v.Completion) μ)
    (μ' : @Measure (GL (Fin 2) (L ⊗[K] v.Completion)) (glBorelOf (L ⊗[K] v.Completion)))
    (hμ' : @Measure.IsHaarMeasure _ _ _ (glBorelOf (L ⊗[K] v.Completion)) μ')
    (c : (v.Completion)ˣ)
    (φ : GL (Fin 2) (L ⊗[K] v.Completion) → ℂ)
    (hφ : (∃ Φ₁ : (Fin 2 → Fin 2 → (v.Extension L) → ℂ) → ℂ,
        ContDiff ℝ (⊤ : ℕ∞) Φ₁ ∧ ∀ g, φ g = Φ₁ (epsL K L v g)) ∧ HasCompactSupport φ)
    (f : GL (Fin 2) v.Completion → ℂ)
    (hf : (∃ F₁ : (Fin 2 → Fin 2 → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F₁ ∧
        ∀ g, f g = F₁ (epsK K v g)) ∧ HasCompactSupport f)
    (hmatch : ∃ V ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
        ∀ δ : GL (Fin 2) (L ⊗[K] v.Completion), IsRegularSemisimple (normString K L v.Completion σ δ) →
        ∀ γ ∈ V, IsRegularSemisimple γ →
        ∀ y : GL (Fin 2) (L ⊗[K] v.Completion), IsNormConjugator K L v.Completion σ γ δ y →
        ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) v.Completion))) (centralizerBorel v.Completion γ))
          (τ' : @Measure (twistedCentralizer K L v.Completion σ δ) (twistedCentralizerBorel K L v.Completion σ δ)),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel v.Completion γ) τ →
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L v.Completion σ δ) τ' →
          Coupled K L v.Completion σ γ δ y τ τ' →
          ∀ I I' : ℂ, IsTwistedOrbitalIntegralOn K L v.Completion σ μ' δ τ' φ I' →
            IsOrbitalIntegralOn v.Completion μ γ τ f I → I' = I)
    (δ y : GL (Fin 2) (L ⊗[K] v.Completion))
    (hN : IsNormConjugator K L v.Completion σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y)
    (τ : @Measure (Subgroup.centralizer
          ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) v.Completion)))
          (centralizerBorel v.Completion (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
    (τ' : @Measure (twistedCentralizer K L v.Completion σ δ) (twistedCentralizerBorel K L v.Completion σ δ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel v.Completion (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) τ)
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L v.Completion σ δ) τ')
    (hτ'i : @Measure.IsInvInvariant _ (twistedCentralizerBorel K L v.Completion σ δ) _ τ')
    (hC : Coupled K L v.Completion σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y τ τ')
    (I I' : ℂ) (hI' : IsTwistedOrbitalIntegralOn K L v.Completion σ μ' δ τ' φ I')
    (hI : IsOrbitalIntegralOn v.Completion μ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ f I) :
    I' = I := by
  classical
  let e : v.Completion ≃+* ℝ := Completion.ringEquivRealOfIsReal hv
  have he : Continuous e := (Completion.isometryEquivRealOfIsReal hv).continuous
  have he' : Continuous e.symm := (Completion.isometryEquivRealOfIsReal hv).symm.continuous
  letI instKR : Algebra K ℝ := (e.toRingHom.comp (algebraMap K v.Completion)).toAlgebra
  obtain ⟨E, hE, hE', hEt, hEσ, hEe⟩ :=
    AutomorphicForm.exists_ringEquiv_tensor_baseChange_of_ringEquiv K L σ v.Completion ℝ e he he'
  obtain ⟨w, hw⟩ : ∃ w : InfinitePlace L, w.comap (algebraMap K L) = v := NumberField.InfinitePlace.comap_surjective v
  have hun : w.IsUnramified K := by simpa [NumberField.InfinitePlace.IsRamified] using hsplit w hw
  obtain ⟨ι₀⟩ := NumberField.InfinitePlace.nonempty_algHom_completion_of_isUnramified K L v w hw hun
  let ι : L →ₐ[K] ℝ :=
    { toRingHom := e.toRingHom.comp ι₀.toRingHom
      commutes' := fun k => by
        show e (ι₀ (algebraMap K L k)) = e (algebraMap K v.Completion k)
        rw [ι₀.commutes] }

  haveI : IsTopologicalRing (L ⊗[K] v.Completion) := isTopologicalRing_tensor K L v.Completion
  haveI : IsTopologicalRing (L ⊗[K] ℝ) := isTopologicalRing_tensor K L ℝ
  letI mA : MeasurableSpace (GL (Fin 2) v.Completion) := glBorelOf v.Completion
  letI mR : MeasurableSpace (GL (Fin 2) ℝ) := glBorelOf ℝ
  letI mLA : MeasurableSpace (GL (Fin 2) (L ⊗[K] v.Completion)) := glBorelOf (L ⊗[K] v.Completion)
  letI mLR : MeasurableSpace (GL (Fin 2) (L ⊗[K] ℝ)) := glBorelOf (L ⊗[K] ℝ)
  haveI : BorelSpace (GL (Fin 2) v.Completion) := borelSpace_glBorelOf _
  haveI : BorelSpace (GL (Fin 2) ℝ) := borelSpace_glBorelOf _
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] v.Completion)) := borelSpace_glBorelOf _
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] ℝ)) := borelSpace_glBorelOf _
  haveI : IsTopologicalGroup (GL (Fin 2) (L ⊗[K] v.Completion)) := isTopologicalGroup_tensorGL K L v.Completion
  haveI : IsTopologicalGroup (GL (Fin 2) (L ⊗[K] ℝ)) := isTopologicalGroup_tensorGL K L ℝ
  haveI : μ.IsHaarMeasure := hμ
  haveI : SecondCountableTopology v.Completion := (Completion.isometryEquivRealOfIsReal hv).toHomeomorph.secondCountableTopology
  letI mT : MeasurableSpace (Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) v.Completion))) :=
    centralizerBorel v.Completion (Matrix.GeneralLinearGroup.scalar (Fin 2) c)
  letI mW : MeasurableSpace (twistedCentralizer K L v.Completion σ δ) := twistedCentralizerBorel K L v.Completion σ δ
  let ê : GL (Fin 2) v.Completion ≃ₜ* GL (Fin 2) ℝ := AutomorphicForm.CentAsmLocal.glEquiv e he he'
  have hê : (⇑ê : GL (Fin 2) v.Completion → GL (Fin 2) ℝ) = Matrix.GeneralLinearGroup.map e.toRingHom :=
    AutomorphicForm.CentAsmLocal.coe_glEquiv e he he'
  set c' : ℝˣ := Units.map (e : v.Completion →* ℝ) c with hc'
  have hsc : Matrix.GeneralLinearGroup.map e.toRingHom (Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) c' := AutomorphicForm.CentAsmLocal.map_scalar e c

  let μA' : Measure (GL (Fin 2) ℝ) := Measure.map (Matrix.GeneralLinearGroup.map e.toRingHom) μ
  have hμA' : μA'.IsHaarMeasure := by
    show (Measure.map (Matrix.GeneralLinearGroup.map e.toRingHom) μ).IsHaarMeasure
    rw [← hê]; exact ê.isHaarMeasure_map μ
  obtain ⟨-, hTThaar, -⟩ :=
    AutomorphicForm.isTwistedOrbitalIntegralOn_map_of_ringEquiv_and_isHaarMeasure_map (σ := σ) (σ' := σ) E hE hE' hEσ μ' δ
  let μL' : Measure (GL (Fin 2) (L ⊗[K] ℝ)) := Measure.map (Matrix.GeneralLinearGroup.map E.toRingHom) μ'
  have hμL' : @Measure.IsHaarMeasure _ _ _ (glBorelOf (L ⊗[K] ℝ)) μL' := hTThaar hμ'

  obtain ⟨τ₀, hτ₀, hτ₀rel, -⟩ :=
    AutomorphicForm.O6Split.exists_isHaarMeasure_centralizer_scalar_forward v.Completion ℝ e he he' c τ hτ
  obtain ⟨τ₀', hτ₀', hτ₀'rel, hτ₀'inv⟩ :=
    AutomorphicForm.O6Split.exists_isHaarMeasure_twistedCentralizer_forward K L σ v.Completion ℝ E hE hE' hEσ δ τ' hτ'
  have hτ₀'i := hτ₀'inv hτ'i

  obtain ⟨hNiff, hCiff⟩ :=
    AutomorphicForm.isNormConjugator_map_iff_and_coupled_map_iff_of_ringEquiv (σ := σ) (σ' := σ) rfl
      e he he' E hE hE' hEσ hEe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y
  rw [hsc] at hNiff hCiff
  have hN' := hNiff.1 hN
  have hC' := (hCiff τ τ₀ τ' τ₀' hτ₀rel hτ₀'rel).1 hC
  have hI'' : IsTwistedOrbitalIntegralOn K L ℝ σ μL' (Matrix.GeneralLinearGroup.map E.toRingHom δ) τ₀'
      (φ ∘ Matrix.GeneralLinearGroup.map E.symm.toRingHom) I' :=
    (AutomorphicForm.O6Split.isTwistedOrbitalIntegralOn_map_iff K L σ v.Completion ℝ E hE hE' hEσ δ μ' τ' τ₀' hτ₀'rel φ I').1 hI'
  have hmatch' := AutomorphicForm.O6Split.hmatch_transport K L σ v.Completion ℝ e E he he' hE hE' hEσ hEe μ μ' φ f c hmatch

  have hf' : (∃ F : (Fin 2 → Fin 2 → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F ∧
      ∀ g, (f ∘ Matrix.GeneralLinearGroup.map e.symm.toRingHom) g = F (fun i j => (g : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧
      HasCompactSupport (f ∘ Matrix.GeneralLinearGroup.map e.symm.toRingHom) := by
    obtain ⟨⟨F₁, hF₁, hfF⟩, hfc⟩ := hf
    refine ⟨⟨fun M => F₁ (fun i j => ((M i j : ℝ) : ℂ)), ?_, ?_⟩, ?_⟩
    · refine hF₁.comp ?_
      refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
      exact Complex.ofRealCLM.contDiff.comp (contDiff_apply_apply ℝ ℝ i j)
    · intro g
      rw [Function.comp_apply, hfF]
      congr 1
      funext i j
      simp only [epsK, Matrix.GeneralLinearGroup.map_apply, Matrix.map_apply, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom]
      rw [← Completion.extensionEmbeddingOfIsReal_apply hv, ← Completion.ringEquivRealOfIsReal_apply hv]
      show ((e (e.symm _) : ℝ) : ℂ) = _
      rw [RingEquiv.apply_symm_apply]
    · have he'' : Continuous e.symm.symm := by simpa using he
      have h1 := hfc.comp_homeomorph (AutomorphicForm.CentAsmLocal.glEquiv e.symm he' he'').toHomeomorph
      have h2 : (f ∘ ⇑(AutomorphicForm.CentAsmLocal.glEquiv e.symm he' he'').toHomeomorph) = f ∘ Matrix.GeneralLinearGroup.map e.symm.toRingHom := by
        funext g
        show f (AutomorphicForm.CentAsmLocal.glEquiv e.symm he' he'' g) = _
        rw [AutomorphicForm.CentAsmLocal.glEquiv_apply]; rfl
      rwa [h2] at h1
  have hφ'cs : HasCompactSupport (φ ∘ Matrix.GeneralLinearGroup.map E.symm.toRingHom) := by
    have hE'' : Continuous E.symm.symm := by simpa using hE
    have h1 := hφ.2.comp_homeomorph (AutomorphicForm.CentAsmLocal.glEquiv E.symm hE' hE'').toHomeomorph
    have h2 : (φ ∘ ⇑(AutomorphicForm.CentAsmLocal.glEquiv E.symm hE' hE'').toHomeomorph) = φ ∘ Matrix.GeneralLinearGroup.map E.symm.toRingHom := by
      funext g
      show φ (AutomorphicForm.CentAsmLocal.glEquiv E.symm hE' hE'' g) = _
      rw [AutomorphicForm.CentAsmLocal.glEquiv_apply]; rfl
    rwa [h2] at h1

  have hφ'sm : ∃ Φ : (Fin (Module.finrank K L) → Fin 2 → Fin 2 → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
      ∀ g, (φ ∘ Matrix.GeneralLinearGroup.map E.symm.toRingHom) g = Φ (fun k i j =>
        ((SplitPlace.psiGL ℝ σ ι hprime hσ g k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j) :=
    (phi_model_real K L hprime σ hσ v hv he' ι E hE hE' hEt φ hφ).1
  have hφ' := And.intro hφ'sm hφ'cs

  have key := hsplitR hσ ι μA' hμA' μL' hμL' _ hφ' _ hf' c' hmatch' _ _ hN' τ₀ τ₀' hτ₀ hτ₀' hC' I' hI''

  have back : ∀ (x : GL (Fin 2) ℝ) (hx : Matrix.GeneralLinearGroup.map e.toRingHom (Matrix.GeneralLinearGroup.scalar (Fin 2) c) = x)
      (τ₁ : @Measure (Subgroup.centralizer ({x} : Set (GL (Fin 2) ℝ))) (centralizerBorel ℝ x)),
      (letI := centralizerBorel ℝ x;
        Measure.map (fun t : Subgroup.centralizer ({x} : Set (GL (Fin 2) ℝ)) => (t : GL (Fin 2) ℝ)) τ₁ =
          Measure.map (fun t : Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) v.Completion)) =>
            Matrix.GeneralLinearGroup.map e.toRingHom (t : GL (Fin 2) v.Completion)) τ) →
      IsOrbitalIntegralOn ℝ μA' x τ₁ (f ∘ Matrix.GeneralLinearGroup.map e.symm.toRingHom) I' →
      IsOrbitalIntegralOn v.Completion μ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ f I' := by
    intro x hx τ₁ hrel h
    subst hx
    exact (AutomorphicForm.O6Split.isOrbitalIntegralOn_map_iff v.Completion ℝ e he he' _ μ τ τ₁ hrel f I').2 h
  have hI'A := back _ hsc τ₀ hτ₀rel key
  exact (AutomorphicForm.O6Split.isOrbitalIntegralOn_scalar_unique_field v.Completion c μ hμ τ hτ f I I' hI hI'A).symm

set_option maxHeartbeats 3200000 in
theorem heng_split_complex
    (hprime : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : InfinitePlace K) (hv : v.IsComplex) (hsplit : ∀ w : InfinitePlace L, w.comap (algebraMap K L) = v → ¬ w.IsRamified K)
    (hsplitC : ∀
      (hσ : σ ≠ 1) [Algebra K ℂ] (ι : L →ₐ[K] ℂ)
      (μA : @Measure (GL (Fin 2) ℂ) (glBorelOf ℂ))
      (hμA : @Measure.IsHaarMeasure _ _ _ (glBorelOf ℂ) μA)
      (μL : @Measure (GL (Fin 2) (L ⊗[K] ℂ)) (glBorelOf (L ⊗[K] ℂ)))
      (hμL : @Measure.IsHaarMeasure _ _ _ (glBorelOf (L ⊗[K] ℂ)) μL)
      (φ : GL (Fin 2) (L ⊗[K] ℂ) → ℂ)
      (hφ : (∃ Φ : (Fin (Module.finrank K L) → Fin 2 → Fin 2 → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
        ∀ g, φ g = Φ (fun k i j =>
          ((SplitPlace.psiGL ℂ σ ι hprime hσ g k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) i j)) ∧
        HasCompactSupport φ)
      (f : GL (Fin 2) ℂ → ℂ)
      (hf : (∃ F : (Fin 2 → Fin 2 → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F ∧
        ∀ g, f g = F (fun i j => (g : Matrix (Fin 2) (Fin 2) ℂ) i j)) ∧ HasCompactSupport f)
      (c : ℂˣ)
      (hmatch : ∃ V ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
        ∀ δ : GL (Fin 2) (L ⊗[K] ℂ), IsRegularSemisimple (normString K L ℂ σ δ) →
        ∀ γ ∈ V, IsRegularSemisimple γ →
        ∀ y : GL (Fin 2) (L ⊗[K] ℂ), IsNormConjugator K L ℂ σ γ δ y →
        ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℂ))) (centralizerBorel ℂ γ))
          (τ' : @Measure (twistedCentralizer K L ℂ σ δ) (twistedCentralizerBorel K L ℂ σ δ)),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℂ γ) τ →
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L ℂ σ δ) τ' →
          Coupled K L ℂ σ γ δ y τ τ' →
          ∀ I I' : ℂ, IsTwistedOrbitalIntegralOn K L ℂ σ μL δ τ' φ I' →
            IsOrbitalIntegralOn ℂ μA γ τ f I → I' = I),
      ∀ δ y : GL (Fin 2) (L ⊗[K] ℂ),
        IsNormConjugator K L ℂ σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y →
        ∀ (τ : @Measure (Subgroup.centralizer
              ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℂ)))
              (centralizerBorel ℂ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
          (τ' : @Measure (twistedCentralizer K L ℂ σ δ) (twistedCentralizerBorel K L ℂ σ δ)),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℂ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) τ →
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L ℂ σ δ) τ' →
          Coupled K L ℂ σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y τ τ' →
          ∀ I' : ℂ, IsTwistedOrbitalIntegralOn K L ℂ σ μL δ τ' φ I' →
            IsOrbitalIntegralOn ℂ μA (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ f I')
    (μ : @Measure (GL (Fin 2) v.Completion) (glBorelOf v.Completion))
    (hμ : @Measure.IsHaarMeasure _ _ _ (glBorelOf v.Completion) μ)
    (μ' : @Measure (GL (Fin 2) (L ⊗[K] v.Completion)) (glBorelOf (L ⊗[K] v.Completion)))
    (hμ' : @Measure.IsHaarMeasure _ _ _ (glBorelOf (L ⊗[K] v.Completion)) μ')
    (c : (v.Completion)ˣ)
    (φ : GL (Fin 2) (L ⊗[K] v.Completion) → ℂ)
    (hφ : (∃ Φ₁ : (Fin 2 → Fin 2 → (v.Extension L) → ℂ) → ℂ,
        ContDiff ℝ (⊤ : ℕ∞) Φ₁ ∧ ∀ g, φ g = Φ₁ (epsL K L v g)) ∧ HasCompactSupport φ)
    (f : GL (Fin 2) v.Completion → ℂ)
    (hf : (∃ F₁ : (Fin 2 → Fin 2 → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F₁ ∧
        ∀ g, f g = F₁ (epsK K v g)) ∧ HasCompactSupport f)
    (hmatch : ∃ V ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
        ∀ δ : GL (Fin 2) (L ⊗[K] v.Completion), IsRegularSemisimple (normString K L v.Completion σ δ) →
        ∀ γ ∈ V, IsRegularSemisimple γ →
        ∀ y : GL (Fin 2) (L ⊗[K] v.Completion), IsNormConjugator K L v.Completion σ γ δ y →
        ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) v.Completion))) (centralizerBorel v.Completion γ))
          (τ' : @Measure (twistedCentralizer K L v.Completion σ δ) (twistedCentralizerBorel K L v.Completion σ δ)),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel v.Completion γ) τ →
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L v.Completion σ δ) τ' →
          Coupled K L v.Completion σ γ δ y τ τ' →
          ∀ I I' : ℂ, IsTwistedOrbitalIntegralOn K L v.Completion σ μ' δ τ' φ I' →
            IsOrbitalIntegralOn v.Completion μ γ τ f I → I' = I)
    (δ y : GL (Fin 2) (L ⊗[K] v.Completion))
    (hN : IsNormConjugator K L v.Completion σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y)
    (τ : @Measure (Subgroup.centralizer
          ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) v.Completion)))
          (centralizerBorel v.Completion (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
    (τ' : @Measure (twistedCentralizer K L v.Completion σ δ) (twistedCentralizerBorel K L v.Completion σ δ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel v.Completion (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) τ)
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L v.Completion σ δ) τ')
    (hτ'i : @Measure.IsInvInvariant _ (twistedCentralizerBorel K L v.Completion σ δ) _ τ')
    (hC : Coupled K L v.Completion σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y τ τ')
    (I I' : ℂ) (hI' : IsTwistedOrbitalIntegralOn K L v.Completion σ μ' δ τ' φ I')
    (hI : IsOrbitalIntegralOn v.Completion μ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ f I) :
    I' = I := by
  classical
  let e : v.Completion ≃+* ℂ := Completion.ringEquivComplexOfIsComplex hv
  have he : Continuous e := (Completion.isometryEquivComplexOfIsComplex hv).continuous
  have he' : Continuous e.symm := (Completion.isometryEquivComplexOfIsComplex hv).symm.continuous
  letI instKC : Algebra K ℂ := (e.toRingHom.comp (algebraMap K v.Completion)).toAlgebra
  obtain ⟨E, hE, hE', hEt, hEσ, hEe⟩ :=
    AutomorphicForm.exists_ringEquiv_tensor_baseChange_of_ringEquiv K L σ v.Completion ℂ e he he'
  obtain ⟨w, hw⟩ : ∃ w : InfinitePlace L, w.comap (algebraMap K L) = v := NumberField.InfinitePlace.comap_surjective v
  have hun : w.IsUnramified K := by simpa [NumberField.InfinitePlace.IsRamified] using hsplit w hw
  obtain ⟨ι₀⟩ := NumberField.InfinitePlace.nonempty_algHom_completion_of_isUnramified K L v w hw hun
  let ι : L →ₐ[K] ℂ :=
    { toRingHom := e.toRingHom.comp ι₀.toRingHom
      commutes' := fun k => by
        show e (ι₀ (algebraMap K L k)) = e (algebraMap K v.Completion k)
        rw [ι₀.commutes] }

  haveI : IsTopologicalRing (L ⊗[K] v.Completion) := isTopologicalRing_tensor K L v.Completion
  haveI : IsTopologicalRing (L ⊗[K] ℂ) := isTopologicalRing_tensor K L ℂ
  letI mA : MeasurableSpace (GL (Fin 2) v.Completion) := glBorelOf v.Completion
  letI mR : MeasurableSpace (GL (Fin 2) ℂ) := glBorelOf ℂ
  letI mLA : MeasurableSpace (GL (Fin 2) (L ⊗[K] v.Completion)) := glBorelOf (L ⊗[K] v.Completion)
  letI mLR : MeasurableSpace (GL (Fin 2) (L ⊗[K] ℂ)) := glBorelOf (L ⊗[K] ℂ)
  haveI : BorelSpace (GL (Fin 2) v.Completion) := borelSpace_glBorelOf _
  haveI : BorelSpace (GL (Fin 2) ℂ) := borelSpace_glBorelOf _
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] v.Completion)) := borelSpace_glBorelOf _
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] ℂ)) := borelSpace_glBorelOf _
  haveI : IsTopologicalGroup (GL (Fin 2) (L ⊗[K] v.Completion)) := isTopologicalGroup_tensorGL K L v.Completion
  haveI : IsTopologicalGroup (GL (Fin 2) (L ⊗[K] ℂ)) := isTopologicalGroup_tensorGL K L ℂ
  haveI : μ.IsHaarMeasure := hμ
  haveI : SecondCountableTopology v.Completion := (Completion.isometryEquivComplexOfIsComplex hv).toHomeomorph.secondCountableTopology
  letI mT : MeasurableSpace (Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) v.Completion))) :=
    centralizerBorel v.Completion (Matrix.GeneralLinearGroup.scalar (Fin 2) c)
  letI mW : MeasurableSpace (twistedCentralizer K L v.Completion σ δ) := twistedCentralizerBorel K L v.Completion σ δ
  let ê : GL (Fin 2) v.Completion ≃ₜ* GL (Fin 2) ℂ := AutomorphicForm.CentAsmLocal.glEquiv e he he'
  have hê : (⇑ê : GL (Fin 2) v.Completion → GL (Fin 2) ℂ) = Matrix.GeneralLinearGroup.map e.toRingHom :=
    AutomorphicForm.CentAsmLocal.coe_glEquiv e he he'
  set c' : ℂˣ := Units.map (e : v.Completion →* ℂ) c with hc'
  have hsc : Matrix.GeneralLinearGroup.map e.toRingHom (Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) c' := AutomorphicForm.CentAsmLocal.map_scalar e c

  let μA' : Measure (GL (Fin 2) ℂ) := Measure.map (Matrix.GeneralLinearGroup.map e.toRingHom) μ
  have hμA' : μA'.IsHaarMeasure := by
    show (Measure.map (Matrix.GeneralLinearGroup.map e.toRingHom) μ).IsHaarMeasure
    rw [← hê]; exact ê.isHaarMeasure_map μ
  obtain ⟨-, hTThaar, -⟩ :=
    AutomorphicForm.isTwistedOrbitalIntegralOn_map_of_ringEquiv_and_isHaarMeasure_map (σ := σ) (σ' := σ) E hE hE' hEσ μ' δ
  let μL' : Measure (GL (Fin 2) (L ⊗[K] ℂ)) := Measure.map (Matrix.GeneralLinearGroup.map E.toRingHom) μ'
  have hμL' : @Measure.IsHaarMeasure _ _ _ (glBorelOf (L ⊗[K] ℂ)) μL' := hTThaar hμ'

  obtain ⟨τ₀, hτ₀, hτ₀rel, -⟩ :=
    AutomorphicForm.O6Split.exists_isHaarMeasure_centralizer_scalar_forward v.Completion ℂ e he he' c τ hτ
  obtain ⟨τ₀', hτ₀', hτ₀'rel, hτ₀'inv⟩ :=
    AutomorphicForm.O6Split.exists_isHaarMeasure_twistedCentralizer_forward K L σ v.Completion ℂ E hE hE' hEσ δ τ' hτ'
  have hτ₀'i := hτ₀'inv hτ'i

  obtain ⟨hNiff, hCiff⟩ :=
    AutomorphicForm.isNormConjugator_map_iff_and_coupled_map_iff_of_ringEquiv (σ := σ) (σ' := σ) rfl
      e he he' E hE hE' hEσ hEe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y
  rw [hsc] at hNiff hCiff
  have hN' := hNiff.1 hN
  have hC' := (hCiff τ τ₀ τ' τ₀' hτ₀rel hτ₀'rel).1 hC
  have hI'' : IsTwistedOrbitalIntegralOn K L ℂ σ μL' (Matrix.GeneralLinearGroup.map E.toRingHom δ) τ₀'
      (φ ∘ Matrix.GeneralLinearGroup.map E.symm.toRingHom) I' :=
    (AutomorphicForm.O6Split.isTwistedOrbitalIntegralOn_map_iff K L σ v.Completion ℂ E hE hE' hEσ δ μ' τ' τ₀' hτ₀'rel φ I').1 hI'
  have hmatch' := AutomorphicForm.O6Split.hmatch_transport K L σ v.Completion ℂ e E he he' hE hE' hEσ hEe μ μ' φ f c hmatch

  have hf' : (∃ F : (Fin 2 → Fin 2 → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F ∧
      ∀ g, (f ∘ Matrix.GeneralLinearGroup.map e.symm.toRingHom) g = F (fun i j => (g : Matrix (Fin 2) (Fin 2) ℂ) i j)) ∧
      HasCompactSupport (f ∘ Matrix.GeneralLinearGroup.map e.symm.toRingHom) := by
    obtain ⟨⟨F₁, hF₁, hfF⟩, hfc⟩ := hf
    refine ⟨⟨F₁, hF₁, ?_⟩, ?_⟩
    · intro g
      rw [Function.comp_apply, hfF]
      congr 1
      funext i j
      simp only [epsK, Matrix.GeneralLinearGroup.map_apply, Matrix.map_apply, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom]
      show Completion.ringEquivComplexOfIsComplex hv (e.symm _) = _
      exact RingEquiv.apply_symm_apply e _
    · have he'' : Continuous e.symm.symm := by simpa using he
      have h1 := hfc.comp_homeomorph (AutomorphicForm.CentAsmLocal.glEquiv e.symm he' he'').toHomeomorph
      have h2 : (f ∘ ⇑(AutomorphicForm.CentAsmLocal.glEquiv e.symm he' he'').toHomeomorph) = f ∘ Matrix.GeneralLinearGroup.map e.symm.toRingHom := by
        funext g
        show f (AutomorphicForm.CentAsmLocal.glEquiv e.symm he' he'' g) = _
        rw [AutomorphicForm.CentAsmLocal.glEquiv_apply]; rfl
      rwa [h2] at h1
  have hφ'cs : HasCompactSupport (φ ∘ Matrix.GeneralLinearGroup.map E.symm.toRingHom) := by
    have hE'' : Continuous E.symm.symm := by simpa using hE
    have h1 := hφ.2.comp_homeomorph (AutomorphicForm.CentAsmLocal.glEquiv E.symm hE' hE'').toHomeomorph
    have h2 : (φ ∘ ⇑(AutomorphicForm.CentAsmLocal.glEquiv E.symm hE' hE'').toHomeomorph) = φ ∘ Matrix.GeneralLinearGroup.map E.symm.toRingHom := by
      funext g
      show φ (AutomorphicForm.CentAsmLocal.glEquiv E.symm hE' hE'' g) = _
      rw [AutomorphicForm.CentAsmLocal.glEquiv_apply]; rfl
    rwa [h2] at h1

  have hφ'sm : ∃ Φ : (Fin (Module.finrank K L) → Fin 2 → Fin 2 → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
      ∀ g, (φ ∘ Matrix.GeneralLinearGroup.map E.symm.toRingHom) g = Φ (fun k i j =>
        ((SplitPlace.psiGL ℂ σ ι hprime hσ g k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) i j) :=
    (phi_model_complex K L hprime σ hσ v hv he' ι E hE hE' hEt φ hφ).1
  have hφ' := And.intro hφ'sm hφ'cs

  have key := hsplitC hσ ι μA' hμA' μL' hμL' _ hφ' _ hf' c' hmatch' _ _ hN' τ₀ τ₀' hτ₀ hτ₀' hC' I' hI''

  have back : ∀ (x : GL (Fin 2) ℂ) (hx : Matrix.GeneralLinearGroup.map e.toRingHom (Matrix.GeneralLinearGroup.scalar (Fin 2) c) = x)
      (τ₁ : @Measure (Subgroup.centralizer ({x} : Set (GL (Fin 2) ℂ))) (centralizerBorel ℂ x)),
      (letI := centralizerBorel ℂ x;
        Measure.map (fun t : Subgroup.centralizer ({x} : Set (GL (Fin 2) ℂ)) => (t : GL (Fin 2) ℂ)) τ₁ =
          Measure.map (fun t : Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) v.Completion)) =>
            Matrix.GeneralLinearGroup.map e.toRingHom (t : GL (Fin 2) v.Completion)) τ) →
      IsOrbitalIntegralOn ℂ μA' x τ₁ (f ∘ Matrix.GeneralLinearGroup.map e.symm.toRingHom) I' →
      IsOrbitalIntegralOn v.Completion μ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ f I' := by
    intro x hx τ₁ hrel h
    subst hx
    exact (AutomorphicForm.O6Split.isOrbitalIntegralOn_map_iff v.Completion ℂ e he he' _ μ τ τ₁ hrel f I').2 h
  have hI'A := back _ hsc τ₀ hτ₀rel key
  exact (AutomorphicForm.O6Split.isOrbitalIntegralOn_scalar_unique_field v.Completion c μ hμ τ hτ f I I' hI hI'A).symm

set_option maxHeartbeats 3200000 in
theorem heng_split
    (hprime : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : InfinitePlace K) (hsplit : ∀ w : InfinitePlace L, w.comap (algebraMap K L) = v → ¬ w.IsRamified K)
    (hsplitR : ∀
      (hσ : σ ≠ 1) [Algebra K ℝ] (ι : L →ₐ[K] ℝ)
      (μA : @Measure (GL (Fin 2) ℝ) (glBorelOf ℝ))
      (hμA : @Measure.IsHaarMeasure _ _ _ (glBorelOf ℝ) μA)
      (μL : @Measure (GL (Fin 2) (L ⊗[K] ℝ)) (glBorelOf (L ⊗[K] ℝ)))
      (hμL : @Measure.IsHaarMeasure _ _ _ (glBorelOf (L ⊗[K] ℝ)) μL)
      (φ : GL (Fin 2) (L ⊗[K] ℝ) → ℂ)
      (hφ : (∃ Φ : (Fin (Module.finrank K L) → Fin 2 → Fin 2 → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
        ∀ g, φ g = Φ (fun k i j =>
          ((SplitPlace.psiGL ℝ σ ι hprime hσ g k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧
        HasCompactSupport φ)
      (f : GL (Fin 2) ℝ → ℂ)
      (hf : (∃ F : (Fin 2 → Fin 2 → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F ∧
        ∀ g, f g = F (fun i j => (g : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧ HasCompactSupport f)
      (c : ℝˣ)
      (hmatch : ∃ V ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
        ∀ δ : GL (Fin 2) (L ⊗[K] ℝ), IsRegularSemisimple (normString K L ℝ σ δ) →
        ∀ γ ∈ V, IsRegularSemisimple γ →
        ∀ y : GL (Fin 2) (L ⊗[K] ℝ), IsNormConjugator K L ℝ σ γ δ y →
        ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℝ))) (centralizerBorel ℝ γ))
          (τ' : @Measure (twistedCentralizer K L ℝ σ δ) (twistedCentralizerBorel K L ℝ σ δ)),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ γ) τ →
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L ℝ σ δ) τ' →
          Coupled K L ℝ σ γ δ y τ τ' →
          ∀ I I' : ℂ, IsTwistedOrbitalIntegralOn K L ℝ σ μL δ τ' φ I' →
            IsOrbitalIntegralOn ℝ μA γ τ f I → I' = I),
      ∀ δ y : GL (Fin 2) (L ⊗[K] ℝ),
        IsNormConjugator K L ℝ σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y →
        ∀ (τ : @Measure (Subgroup.centralizer
              ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ)))
              (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
          (τ' : @Measure (twistedCentralizer K L ℝ σ δ) (twistedCentralizerBorel K L ℝ σ δ)),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) τ →
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L ℝ σ δ) τ' →
          Coupled K L ℝ σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y τ τ' →
          ∀ I' : ℂ, IsTwistedOrbitalIntegralOn K L ℝ σ μL δ τ' φ I' →
            IsOrbitalIntegralOn ℝ μA (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ f I')
    (hsplitC : ∀
      (hσ : σ ≠ 1) [Algebra K ℂ] (ι : L →ₐ[K] ℂ)
      (μA : @Measure (GL (Fin 2) ℂ) (glBorelOf ℂ))
      (hμA : @Measure.IsHaarMeasure _ _ _ (glBorelOf ℂ) μA)
      (μL : @Measure (GL (Fin 2) (L ⊗[K] ℂ)) (glBorelOf (L ⊗[K] ℂ)))
      (hμL : @Measure.IsHaarMeasure _ _ _ (glBorelOf (L ⊗[K] ℂ)) μL)
      (φ : GL (Fin 2) (L ⊗[K] ℂ) → ℂ)
      (hφ : (∃ Φ : (Fin (Module.finrank K L) → Fin 2 → Fin 2 → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
        ∀ g, φ g = Φ (fun k i j =>
          ((SplitPlace.psiGL ℂ σ ι hprime hσ g k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) i j)) ∧
        HasCompactSupport φ)
      (f : GL (Fin 2) ℂ → ℂ)
      (hf : (∃ F : (Fin 2 → Fin 2 → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F ∧
        ∀ g, f g = F (fun i j => (g : Matrix (Fin 2) (Fin 2) ℂ) i j)) ∧ HasCompactSupport f)
      (c : ℂˣ)
      (hmatch : ∃ V ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
        ∀ δ : GL (Fin 2) (L ⊗[K] ℂ), IsRegularSemisimple (normString K L ℂ σ δ) →
        ∀ γ ∈ V, IsRegularSemisimple γ →
        ∀ y : GL (Fin 2) (L ⊗[K] ℂ), IsNormConjugator K L ℂ σ γ δ y →
        ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℂ))) (centralizerBorel ℂ γ))
          (τ' : @Measure (twistedCentralizer K L ℂ σ δ) (twistedCentralizerBorel K L ℂ σ δ)),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℂ γ) τ →
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L ℂ σ δ) τ' →
          Coupled K L ℂ σ γ δ y τ τ' →
          ∀ I I' : ℂ, IsTwistedOrbitalIntegralOn K L ℂ σ μL δ τ' φ I' →
            IsOrbitalIntegralOn ℂ μA γ τ f I → I' = I),
      ∀ δ y : GL (Fin 2) (L ⊗[K] ℂ),
        IsNormConjugator K L ℂ σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y →
        ∀ (τ : @Measure (Subgroup.centralizer
              ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℂ)))
              (centralizerBorel ℂ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
          (τ' : @Measure (twistedCentralizer K L ℂ σ δ) (twistedCentralizerBorel K L ℂ σ δ)),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℂ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) τ →
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L ℂ σ δ) τ' →
          Coupled K L ℂ σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y τ τ' →
          ∀ I' : ℂ, IsTwistedOrbitalIntegralOn K L ℂ σ μL δ τ' φ I' →
            IsOrbitalIntegralOn ℂ μA (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ f I')
    (μ : @Measure (GL (Fin 2) v.Completion) (glBorelOf v.Completion))
    (hμ : @Measure.IsHaarMeasure _ _ _ (glBorelOf v.Completion) μ)
    (μ' : @Measure (GL (Fin 2) (L ⊗[K] v.Completion)) (glBorelOf (L ⊗[K] v.Completion)))
    (hμ' : @Measure.IsHaarMeasure _ _ _ (glBorelOf (L ⊗[K] v.Completion)) μ')
    (c : (v.Completion)ˣ)
    (φ : GL (Fin 2) (L ⊗[K] v.Completion) → ℂ)
    (hφ : (∃ Φ₁ : (Fin 2 → Fin 2 → (v.Extension L) → ℂ) → ℂ,
        ContDiff ℝ (⊤ : ℕ∞) Φ₁ ∧ ∀ g, φ g = Φ₁ (epsL K L v g)) ∧ HasCompactSupport φ)
    (f : GL (Fin 2) v.Completion → ℂ)
    (hf : (∃ F₁ : (Fin 2 → Fin 2 → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F₁ ∧
        ∀ g, f g = F₁ (epsK K v g)) ∧ HasCompactSupport f)
    (hmatch : ∃ V ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
        ∀ δ : GL (Fin 2) (L ⊗[K] v.Completion), IsRegularSemisimple (normString K L v.Completion σ δ) →
        ∀ γ ∈ V, IsRegularSemisimple γ →
        ∀ y : GL (Fin 2) (L ⊗[K] v.Completion), IsNormConjugator K L v.Completion σ γ δ y →
        ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) v.Completion))) (centralizerBorel v.Completion γ))
          (τ' : @Measure (twistedCentralizer K L v.Completion σ δ) (twistedCentralizerBorel K L v.Completion σ δ)),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel v.Completion γ) τ →
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L v.Completion σ δ) τ' →
          Coupled K L v.Completion σ γ δ y τ τ' →
          ∀ I I' : ℂ, IsTwistedOrbitalIntegralOn K L v.Completion σ μ' δ τ' φ I' →
            IsOrbitalIntegralOn v.Completion μ γ τ f I → I' = I)
    (δ y : GL (Fin 2) (L ⊗[K] v.Completion))
    (hN : IsNormConjugator K L v.Completion σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y)
    (τ : @Measure (Subgroup.centralizer
          ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) v.Completion)))
          (centralizerBorel v.Completion (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
    (τ' : @Measure (twistedCentralizer K L v.Completion σ δ) (twistedCentralizerBorel K L v.Completion σ δ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel v.Completion (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) τ)
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L v.Completion σ δ) τ')
    (hτ'i : @Measure.IsInvInvariant _ (twistedCentralizerBorel K L v.Completion σ δ) _ τ')
    (hC : Coupled K L v.Completion σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y τ τ')
    (I I' : ℂ) (hI' : IsTwistedOrbitalIntegralOn K L v.Completion σ μ' δ τ' φ I')
    (hI : IsOrbitalIntegralOn v.Completion μ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ f I) :
    I' = I := by
  rcases v.isReal_or_isComplex with hv | hv
  · exact heng_split_real K L hprime σ hσ v hv hsplit hsplitR μ hμ μ' hμ' c φ hφ f hf hmatch δ y hN τ τ' hτ hτ' hτ'i hC I I' hI' hI
  · exact heng_split_complex K L hprime σ hσ v hv hsplit hsplitC μ hμ μ' hμ' c φ hφ f hf hmatch δ y hN τ τ' hτ hτ' hτ'i hC I I' hI' hI

end AutomorphicForm.CentAsmLocal
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.FDTEF P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CasmGram P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.P2mGramSide"
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.FDTEF P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CasmGram P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.P2mGramSide"

end
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.FDTEF P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CasmGram P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.P2mGramSide"

set_option autoImplicit false

p2m_open "MeasureTheory NumberField NumberField.InfinitePlace AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm"
open scoped TensorProduct TensorProduct.RightActions NumberField.LiesOver

namespace AutomorphicForm
p2m_export "AutomorphicForm" "isTopologicalRing_tensor t2Space_tensor locallyCompactSpace_tensor isTopologicalGroup_tensorGL t2Space_tensorGL locallyCompactSpace_tensorGL glBorelOf borelSpace_glBorelOf centralizerBorel toTensorGL sigmaTensor sigmaGL normString IsSigmaConjugate IsNormConjugator IsNormOf twistedCentralizer twistedCentralizerBorel IsSectionFnOn IsOrbitalIntegralOn IsTwistedSectionFnOn IsTwistedOrbitalIntegralOn Coupled AreMatchingOn archHaarK archHaarL archIdent archIdentGL AreMatchingArch IsRegularSemisimple archEntries_apply IsArchTestFactor sigmaCentralizer mem_sigmaCentralizer_iff SplitPlace.psi SplitPlace.psiEquiv SplitPlace.psiEquiv_apply SplitPlace.psiEquiv_symm_const SplitPlace.psiGL exists_mulEquiv_generalLinearGroup_tensorProduct_infiniteAdeleRing_pi exists_ringEquiv_tensorProduct_infiniteAdeleRing_pi_forall_tmul archIdent_tmul_apply exists_continuous_isSectionFnOn_and_isOrbitalIntegralOn_iff_completion_of_isRegularSemisimple exists_isTwistedSectionFnOn_and_continuous_completion_of_isRegularSemisimple_normString exists_isTwistedSectionFnOn_and_continuous_completion_of_isSigmaConjugate_scalar_of_prime semilocal_central_transfer_of_forall_oneplace_of_referenceMeasures exists_isNormConjugator_and_coupled_of_gram_of_algHom_real exists_isNormConjugator_and_coupled_of_gram_of_algHom_complex exists_isNormConjugator_and_coupled_of_gram_conjAe_of_pos isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar map_centralizer_map_ringEquiv_pi_eq_smul_gram_of_infiniteAdeleRing map_twistedCentralizer_map_ringEquiv_pi_eq_smul_gram_of_infiniteAdeleRing mem_span_map_ringEquiv_pi_iff_of_span_eq_range_includeRight mem_span_map_ringEquiv_pi_iff_of_span_eq_setOf_mul_eq_mul_map_sigmaTensor exists_gram_map_of_ringEquiv_of_exists_gram exists_ringEquiv_tensor_completion_complex_of_isRamified isTwistedOrbitalIntegralOn_map_of_ringEquiv_and_isHaarMeasure_map isNormConjugator_map_iff_and_coupled_map_iff_of_ringEquiv isOrbitalIntegralOn_map_generalLinearGroup_map_of_ringEquiv isHaarMeasure_map_and_exists_isHaarMeasure_centralizer_of_ringEquiv pos_and_exists_coupled_toTensorGL_scalar_one_iff_of_coupled_scalar_conjAe exists_ringEquiv_tensor_baseChange_of_ringEquiv isOrbitalIntegralOn_scalar_neg_of_isTwistedOrbitalIntegralOn_conjAe_of_gram_of_nhds_forall_isNormConjugator_of_neg exists_isSigmaConjugate_scalar_of_isNormConjugator_scalar_of_algHom_of_prime exists_isTwistedSectionFnOn_and_continuous_completion_of_not_isSigmaConjugate_scalar_of_finrank_eq_two exists_isSigmaConjugate_scalar_conjAe_iff_pos_of_isNormConjugator_scalar"
namespace CentAsmLocal
p2m_open "AutomorphicForm"

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

attribute [local instance 10000] AutomorphicForm.glBorelOf AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel
attribute [local instance] borelSpace_gl borelSpace_centralizer

set_option maxHeartbeats 6400000 in
theorem dram
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (w : InfinitePlace L) (hw : w.IsRamified K)

    (e : (w.comap (algebraMap K L)).Completion ≃+* ℝ) (E : L ⊗[K] (w.comap (algebraMap K L)).Completion ≃+* ℂ ⊗[ℝ] ℝ)
    (he : Continuous e) (he' : Continuous e.symm) (hE : Continuous E) (hE' : Continuous E.symm)
    (hEσ : ∀ z, E (sigmaTensor K L (w.comap (algebraMap K L)).Completion σ z) = sigmaTensor ℝ ℂ ℝ Complex.conjAe (E z))
    (hEι : ∀ g : GL (Fin 2) (w.comap (algebraMap K L)).Completion,
      Matrix.GeneralLinearGroup.map E.toRingHom (toTensorGL K L (w.comap (algebraMap K L)).Completion g) =
        toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.map e.toRingHom g))
    (h7 : ∀ (x : L) (a : (w.comap (algebraMap K L)).Completion),
      (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
        (Algebra.TensorProduct.rid ℝ ℝ ℂ)) (E (x ⊗ₜ a)) = w.embedding x * (e a : ℂ))
    (h8 : ∀ k : K, (e (algebraMap K (w.comap (algebraMap K L)).Completion k) : ℂ) = w.embedding (algebraMap K L k))

    [instℝ : Algebra ℝ (L ⊗[K] (w.comap (algebraMap K L)).Completion)]
    (hEr : ∀ (r : ℝ) (z : L ⊗[K] (w.comap (algebraMap K L)).Completion), E (r • z) = r • E z)

    (hkind : ∀ (c : ℝˣ) (δ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)),
      IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y →
      ((∃ z : (ℂ ⊗[ℝ] ℝ)ˣ, IsSigmaConjugate ℝ ℂ ℝ Complex.conjAe δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z)) ↔
        0 < (c : ℝ)))
    (hram : ∀
      (μA : @Measure (GL (Fin 2) ℝ) (glBorelOf ℝ))
      (μL : @Measure (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) (glBorelOf (ℂ ⊗[ℝ] ℝ)))
      (hμA : @Measure.IsHaarMeasure _ _ _ (glBorelOf ℝ) μA)
      (hμL : @Measure.IsHaarMeasure _ _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) μL)
      (φ : GL (Fin 2) ℂ → ℂ)
      (hφ : (∃ Φ : (Fin 2 → Fin 2 → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
        ∀ g, φ g = Φ (fun i j => (g : Matrix (Fin 2) (Fin 2) ℂ) i j)) ∧ HasCompactSupport φ)
      (f : GL (Fin 2) ℝ → ℂ)
      (hf : (∃ F : (Fin 2 → Fin 2 → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F ∧
        ∀ g, f g = F (fun i j => (g : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧ HasCompactSupport f)
      (c : ℝˣ) (hc : 0 < (c : ℝ))
      (hmatch : ∃ V ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
        ∀ δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ), IsRegularSemisimple (normString ℝ ℂ ℝ Complex.conjAe δ) →
        ∀ γ ∈ V, IsRegularSemisimple γ →
        ∀ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ), IsNormConjugator ℝ ℂ ℝ Complex.conjAe γ δ y →
        ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℝ))) (centralizerBorel ℝ γ))
          (τ' : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ)
            (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ)),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ γ) τ →
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) τ' →
          Coupled ℝ ℂ ℝ Complex.conjAe γ δ y τ τ' →
          ∀ I I' : ℂ,
            IsTwistedOrbitalIntegralOn ℝ ℂ ℝ Complex.conjAe μL δ τ'
              (fun z => φ (Matrix.GeneralLinearGroup.map
                (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                  (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom z : GL (Fin 2) ℂ)) I' →
            IsOrbitalIntegralOn ℝ μA γ τ f I → I' = I),
      ∀ δ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ),
        IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y →
        ∀ (τ : @Measure (Subgroup.centralizer
              ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ)))
              (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
          (τ' : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ)
            (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ)),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) τ →
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) τ' →
          Coupled ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y τ τ' →
          ∀ I' : ℂ,
            IsTwistedOrbitalIntegralOn ℝ ℂ ℝ Complex.conjAe μL δ τ'
              (fun z => φ (Matrix.GeneralLinearGroup.map
                (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                  (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom z : GL (Fin 2) ℂ)) I' →
            IsOrbitalIntegralOn ℝ μA (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ f I')
    (μ : @Measure (GL (Fin 2) (w.comap (algebraMap K L)).Completion) (glBorelOf (w.comap (algebraMap K L)).Completion))
    (hμ : @Measure.IsHaarMeasure _ _ _ (glBorelOf (w.comap (algebraMap K L)).Completion) μ)
    (μ' : @Measure (GL (Fin 2) (L ⊗[K] (w.comap (algebraMap K L)).Completion)) (glBorelOf (L ⊗[K] (w.comap (algebraMap K L)).Completion)))
    (hμ' : @Measure.IsHaarMeasure _ _ _ (glBorelOf (L ⊗[K] (w.comap (algebraMap K L)).Completion)) μ')
    (c : ((w.comap (algebraMap K L)).Completion)ˣ)
    (φ : GL (Fin 2) (L ⊗[K] (w.comap (algebraMap K L)).Completion) → ℂ)
    (hφ : (∃ Φ₁ : (Fin 2 → Fin 2 → ((w.comap (algebraMap K L)).Extension L) → ℂ) → ℂ,
        ContDiff ℝ (⊤ : ℕ∞) Φ₁ ∧ ∀ g, φ g = Φ₁ (epsL K L (w.comap (algebraMap K L)) g)) ∧ HasCompactSupport φ)
    (f : GL (Fin 2) (w.comap (algebraMap K L)).Completion → ℂ)
    (hf : (∃ F₁ : (Fin 2 → Fin 2 → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F₁ ∧
        ∀ g, f g = F₁ (epsK K (w.comap (algebraMap K L)) g)) ∧ HasCompactSupport f)
    (hmatch : ∃ V ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
        ∀ δ : GL (Fin 2) (L ⊗[K] (w.comap (algebraMap K L)).Completion), IsRegularSemisimple (normString K L (w.comap (algebraMap K L)).Completion σ δ) →
        ∀ γ ∈ V, IsRegularSemisimple γ →
        ∀ y : GL (Fin 2) (L ⊗[K] (w.comap (algebraMap K L)).Completion), IsNormConjugator K L (w.comap (algebraMap K L)).Completion σ γ δ y →
        ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (w.comap (algebraMap K L)).Completion))) (centralizerBorel (w.comap (algebraMap K L)).Completion γ))
          (τ' : @Measure (twistedCentralizer K L (w.comap (algebraMap K L)).Completion σ δ) (twistedCentralizerBorel K L (w.comap (algebraMap K L)).Completion σ δ)),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel (w.comap (algebraMap K L)).Completion γ) τ →
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (w.comap (algebraMap K L)).Completion σ δ) τ' →
          Coupled K L (w.comap (algebraMap K L)).Completion σ γ δ y τ τ' →
          ∀ I I' : ℂ, IsTwistedOrbitalIntegralOn K L (w.comap (algebraMap K L)).Completion σ μ' δ τ' φ I' →
            IsOrbitalIntegralOn (w.comap (algebraMap K L)).Completion μ γ τ f I → I' = I)
    (δ y : GL (Fin 2) (L ⊗[K] (w.comap (algebraMap K L)).Completion))
    (hN : IsNormConjugator K L (w.comap (algebraMap K L)).Completion σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y)
    (τ : @Measure (Subgroup.centralizer
          ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) (w.comap (algebraMap K L)).Completion)))
          (centralizerBorel (w.comap (algebraMap K L)).Completion (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
    (τ' : @Measure (twistedCentralizer K L (w.comap (algebraMap K L)).Completion σ δ) (twistedCentralizerBorel K L (w.comap (algebraMap K L)).Completion σ δ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel (w.comap (algebraMap K L)).Completion (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) τ)
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (w.comap (algebraMap K L)).Completion σ δ) τ')
    (hτ'i : @Measure.IsInvInvariant _ (twistedCentralizerBorel K L (w.comap (algebraMap K L)).Completion σ δ) _ τ')
    (hgram : (letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] (w.comap (algebraMap K L)).Completion)) := borel _
       letI := centralizerBorel (w.comap (algebraMap K L)).Completion (Matrix.GeneralLinearGroup.scalar (Fin 2) c)
       letI := twistedCentralizerBorel K L (w.comap (algebraMap K L)).Completion σ δ
       ∃ (n₁ n₂ : ℕ) (e₁ : Fin n₁ → Matrix (Fin 2) (Fin 2) (L ⊗[K] (w.comap (algebraMap K L)).Completion))
         (e₂ : Fin n₂ → Matrix (Fin 2) (Fin 2) (L ⊗[K] (w.comap (algebraMap K L)).Completion)) (s : ENNReal),
         s ≠ 0 ∧ s ≠ ⊤ ∧
         LinearIndependent ℝ e₁ ∧
           (Submodule.span ℝ (Set.range e₁) : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] (w.comap (algebraMap K L)).Completion))) =
             Set.range (fun Y : Matrix (Fin 2) (Fin 2) (w.comap (algebraMap K L)).Completion =>
               Y.map (fun x : (w.comap (algebraMap K L)).Completion => ((1 : L) ⊗ₜ[K] x : L ⊗[K] (w.comap (algebraMap K L)).Completion))) ∧
         LinearIndependent ℝ e₂ ∧
           (Submodule.span ℝ (Set.range e₂) : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] (w.comap (algebraMap K L)).Completion))) =
             {X | X * (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] (w.comap (algebraMap K L)).Completion)) =
               (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] (w.comap (algebraMap K L)).Completion)) * X.map (sigmaTensor K L (w.comap (algebraMap K L)).Completion σ)} ∧
         Measure.map (fun t : ↥(Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) (w.comap (algebraMap K L)).Completion))) =>
             ((t : GL (Fin 2) (w.comap (algebraMap K L)).Completion) : Matrix (Fin 2) (Fin 2) (w.comap (algebraMap K L)).Completion).map
               (fun x : (w.comap (algebraMap K L)).Completion => ((1 : L) ⊗ₜ[K] x : L ⊗[K] (w.comap (algebraMap K L)).Completion))) τ =
           s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₁ =>
                   Algebra.trace ℝ (L ⊗[K] (w.comap (algebraMap K L)).Completion) (Matrix.trace (e₁ i * e₁ j))).det|)) •
                 Measure.map (fun a : Fin n₁ → ℝ => ∑ i, a i • e₁ i) volume).withDensity
               (fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] (w.comap (algebraMap K L)).Completion) =>
                 (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹) ∧
         Measure.map (fun t : ↥(twistedCentralizer K L (w.comap (algebraMap K L)).Completion σ δ) =>
             ((t : GL (Fin 2) (L ⊗[K] (w.comap (algebraMap K L)).Completion)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] (w.comap (algebraMap K L)).Completion))) τ' =
           s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
                   Algebra.trace ℝ (L ⊗[K] (w.comap (algebraMap K L)).Completion) (Matrix.trace (e₂ i * e₂ j))).det|)) •
                 Measure.map (fun a : Fin n₂ → ℝ => ∑ i, a i • e₂ i) volume).withDensity
               (fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] (w.comap (algebraMap K L)).Completion) =>
                 (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹)))
    (I I' : ℂ) (hI' : IsTwistedOrbitalIntegralOn K L (w.comap (algebraMap K L)).Completion σ μ' δ τ' φ I')
    (hI : IsOrbitalIntegralOn (w.comap (algebraMap K L)).Completion μ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ f I) :
    ((∃ z : (L ⊗[K] (w.comap (algebraMap K L)).Completion)ˣ,
        IsSigmaConjugate K L (w.comap (algebraMap K L)).Completion σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z)) → I' = I) ∧
    ((¬ ∃ z : (L ⊗[K] (w.comap (algebraMap K L)).Completion)ˣ,
        IsSigmaConjugate K L (w.comap (algebraMap K L)).Completion σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z)) → I' = -I) := by
  classical

  obtain ⟨hwc, hv⟩ := isRamified_iff.1 hw
  haveI := isTopologicalRing_tensor K L (w.comap (algebraMap K L)).Completion
  haveI := isTopologicalRing_tensor ℝ ℂ ℝ
  haveI := isTopologicalGroup_tensorGL K L (w.comap (algebraMap K L)).Completion
  haveI := isTopologicalGroup_tensorGL ℝ ℂ ℝ

  have hrank : Module.finrank K L = Module.finrank ℝ ℂ := by rw [h2, Complex.finrank_real_complex]

  obtain ⟨τ₀, hτ₀, hτ₀c, -⟩ := centralizer_forward_gl e he he' (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ hτ
  obtain ⟨τ₀', hτ₀', hτ₀'c, -⟩ := twistedCentralizer_forward_gl σ Complex.conjAe E hE hE' hEσ δ τ' hτ'
  have hTTC := AutomorphicForm.isNormConjugator_map_iff_and_coupled_map_iff_of_ringEquiv σ Complex.conjAe hrank
    e he he' E hE hE' hEσ hEι (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y
  have hN' := hTTC.1.mp hN
  have hTTV := AutomorphicForm.isTwistedOrbitalIntegralOn_map_of_ringEquiv_and_isHaarMeasure_map σ Complex.conjAe
    E hE hE' hEσ μ' δ
  have hI'm := hTTV.1 τ' τ₀' hτ₀'c φ I' hI'
  have hμL : @Measure.IsHaarMeasure _ _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ))
      (@Measure.map _ _ (glBorelOf (L ⊗[K] (w.comap (algebraMap K L)).Completion)) (glBorelOf (ℂ ⊗[ℝ] ℝ))
        (Matrix.GeneralLinearGroup.map E.toRingHom) μ') := hTTV.2.1 hμ'
  have hIm := AutomorphicForm.isOrbitalIntegralOn_map_generalLinearGroup_map_of_ringEquiv e he he' μ
    (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ τ₀ hτ₀c f I hI
  have hμA : @Measure.IsHaarMeasure _ _ _ (glBorelOf ℝ)
      (@Measure.map _ _ (glBorelOf (w.comap (algebraMap K L)).Completion) (glBorelOf ℝ) (Matrix.GeneralLinearGroup.map e.toRingHom) μ) :=
    (AutomorphicForm.isHaarMeasure_map_and_exists_isHaarMeasure_centralizer_of_ringEquiv e he he' μ hμ
      (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ₀ hτ₀).1

  obtain ⟨φm, hφm⟩ : ∃ φm : GL (Fin 2) ℂ → ℂ, ∀ g, φm g = φ (Matrix.GeneralLinearGroup.map E.symm.toRingHom
      (Matrix.GeneralLinearGroup.map (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _ (Algebra.TensorProduct.rid ℝ ℝ ℂ)).symm.toRingHom g)) := ⟨_, fun _ => rfl⟩
  obtain ⟨fm, hfm⟩ : ∃ fm : GL (Fin 2) ℝ → ℂ, ∀ g, fm g = f (Matrix.GeneralLinearGroup.map e.symm.toRingHom g) :=
    ⟨_, fun _ => rfl⟩
  have hφeq : (fun z : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) => φm (Matrix.GeneralLinearGroup.map (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _ (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom z : GL (Fin 2) ℂ)) =
      φ ∘ Matrix.GeneralLinearGroup.map E.symm.toRingHom := by
    funext z
    rw [hφm, map_symm_map]
    rfl
  have hfeq : (f ∘ Matrix.GeneralLinearGroup.map e.symm.toRingHom) = fm := funext fun g => (hfm g).symm
  have hφm_smooth : (∃ Φ : (Fin 2 → Fin 2 → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
      ∀ g, φm g = Φ (fun i j => (g : Matrix (Fin 2) (Fin 2) ℂ) i j)) ∧ HasCompactSupport φm := by
    obtain ⟨⟨Φ₁, hΦ₁, hφΦ⟩, hφc⟩ := hφ

    have hT : ∀ w' : (w.comap (algebraMap K L)).Extension L, ∃ T : ℂ →L[ℝ] ℂ, ∀ z : ℂ,
        T z = (letI : w'.1.1.LiesOver (w.comap (algebraMap K L)).1 :=
            M4aHerbrand.ArchSemilocal.liesOver_of_comap_eq w'.2
          Completion.extensionEmbedding w'.1
            (M4aHerbrand.ArchSemilocal.psiFactor (w.comap (algebraMap K L)) w'.1
              (_root_.Algebra.TensorProduct.comm K L (w.comap (algebraMap K L)).Completion (E.symm ((@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _ (Algebra.TensorProduct.rid ℝ ℝ ℂ)).symm z))))) := by
      intro w'
      letI iLO : w'.1.1.LiesOver (w.comap (algebraMap K L)).1 := M4aHerbrand.ArchSemilocal.liesOver_of_comap_eq w'.2
      have hv' : (w'.1.comap (algebraMap K L)).IsReal := by rw [w'.2]; exact hv
      haveI : ComplexEmbedding.LiesOver w'.1.embedding (w.comap (algebraMap K L)).embedding := by
        have h := embedding_comap_eq (K := K) w'.1 hv'
        rw [w'.2] at h
        exact ⟨by rw [h]⟩
      haveI := Completion.liesOver_extensionEmbedding w'.1 (w.comap (algebraMap K L))
      let Tr : ℂ →+* ℂ := (Completion.extensionEmbedding w'.1).comp
        ((M4aHerbrand.ArchSemilocal.psiFactor (w.comap (algebraMap K L)) w'.1).toRingHom.comp
          ((_root_.Algebra.TensorProduct.comm K L (w.comap (algebraMap K L)).Completion).toRingEquiv.toRingHom.comp
            (E.symm.toRingHom.comp (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _ (Algebra.TensorProduct.rid ℝ ℝ ℂ)).symm.toRingHom)))
      have hTr : ∀ z, Tr z = Completion.extensionEmbedding w'.1
          (M4aHerbrand.ArchSemilocal.psiFactor (w.comap (algebraMap K L)) w'.1
            (_root_.Algebra.TensorProduct.comm K L (w.comap (algebraMap K L)).Completion (E.symm ((@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _ (Algebra.TensorProduct.rid ℝ ℝ ℂ)).symm z)))) := fun z => rfl
      have hfix : ∀ r : ℝ, Tr (r : ℂ) = r := by
        intro r
        rw [hTr]
        have h1 : E.symm ((@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _ (Algebra.TensorProduct.rid ℝ ℝ ℂ)).symm (r : ℂ)) = (1 : L) ⊗ₜ e.symm r := by
          apply E.injective
          rw [E.apply_symm_apply]
          apply (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _ (Algebra.TensorProduct.rid ℝ ℝ ℂ)).injective
          rw [RingEquiv.apply_symm_apply, h7, map_one, one_mul, RingEquiv.apply_symm_apply]
        rw [h1, _root_.Algebra.TensorProduct.comm_tmul, M4aHerbrand.ArchSemilocal.psiFactor_tmul, map_one, mul_one,
          Completion.liesOver_extensionEmbedding_apply, ← ofReal_ramModel_eq_extensionEmbedding w hw e he h8,
          RingEquiv.apply_symm_apply]
      refine ⟨LinearMap.toContinuousLinearMap
        { toFun := Tr, map_add' := map_add Tr, map_smul' := fun r z => ?_ }, fun z => rfl⟩
      show Tr (r • z) = r • Tr z
      rw [Complex.real_smul, Complex.real_smul, map_mul, hfix]
    choose T hT using hT
    refine ⟨⟨fun M => Φ₁ (fun i j w' => T w' (M i j)), ?_, ?_⟩, ?_⟩
    · refine hΦ₁.comp ?_
      exact contDiff_pi.2 fun i => contDiff_pi.2 fun j => contDiff_pi.2 fun w' =>
        (T w').contDiff.comp (contDiff_apply_apply ℝ ℂ i j)
    · intro g
      rw [hφm, hφΦ]
      congr 1
      funext i j w'
      rw [hT]
      rfl
    ·
      have hRIDlin : ∃ l : (ℂ ⊗[ℝ] ℝ) →ₗ[ℝ] ℂ, ∀ x, l x = (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _ (Algebra.TensorProduct.rid ℝ ℝ ℂ)) x := by
        refine ⟨{ toFun := (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _ (Algebra.TensorProduct.rid ℝ ℝ ℂ)), map_add' := map_add _, map_smul' := ?_ }, fun _ => rfl⟩
        intro r x
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul z s =>
            rw [TensorProduct.RightActions.smul_def, TensorProduct.comm_tmul, TensorProduct.smul_tmul',
              TensorProduct.comm_symm_tmul, smul_eq_mul]
            show (Algebra.TensorProduct.rid ℝ ℝ ℂ) (z ⊗ₜ (r * s)) = r • (Algebra.TensorProduct.rid ℝ ℝ ℂ) (z ⊗ₜ s)
            rw [Algebra.TensorProduct.rid_tmul, Algebra.TensorProduct.rid_tmul, smul_smul]
        | add x y hx hy =>
            simp only [RingHom.id_apply] at hx hy ⊢
            rw [TensorProduct.RightActions.smul_def, map_add, smul_add, map_add, map_add,
              ← TensorProduct.RightActions.smul_def, ← TensorProduct.RightActions.smul_def, hx, hy]
            rw [map_add, smul_add]
      obtain ⟨l, hl⟩ := hRIDlin
      have hRIDc : Continuous (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _ (Algebra.TensorProduct.rid ℝ ℝ ℂ)) := by
        have hlc : Continuous l := IsModuleTopology.continuous_of_linearMap l
        exact hlc.congr hl
      have hmapRID : Continuous (Matrix.GeneralLinearGroup.map (n := Fin 2) (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _ (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom) :=
        Continuous.units_map _ (continuous_id.matrix_map hRIDc)
      have hmapE : Continuous (Matrix.GeneralLinearGroup.map (n := Fin 2) E.toRingHom) :=
        (glE E hE hE').continuous.congr (glE_apply E hE hE')
      refine HasCompactSupport.intro ((hφc.isCompact.image hmapE).image hmapRID) ?_
      intro g hg
      rw [hφm]
      by_contra hne
      apply hg
      refine ⟨Matrix.GeneralLinearGroup.map E.toRingHom (Matrix.GeneralLinearGroup.map E.symm.toRingHom
        (Matrix.GeneralLinearGroup.map (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _ (Algebra.TensorProduct.rid ℝ ℝ ℂ)).symm.toRingHom g)), ⟨_, subset_tsupport _ hne, rfl⟩, ?_⟩
      rw [map_map_symm, map_map_symm]
  have hfm_smooth : (∃ F : (Fin 2 → Fin 2 → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F ∧
      ∀ g, fm g = F (fun i j => (g : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧ HasCompactSupport fm := by
    obtain ⟨⟨F₁, hF₁, hfF⟩, hfc⟩ := hf
    refine ⟨⟨fun M => F₁ (fun i j => ((M i j : ℝ) : ℂ)), ?_, ?_⟩, ?_⟩
    · refine hF₁.comp ?_
      refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
      exact Complex.ofRealCLM.contDiff.comp (contDiff_apply_apply ℝ ℝ i j)
    · intro g
      rw [hfm, hfF]
      congr 1
      funext i j
      simp only [epsK, Matrix.GeneralLinearGroup.map_apply, Matrix.map_apply, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom]
      rw [← ofReal_ramModel_eq_extensionEmbedding w hw e he h8, RingEquiv.apply_symm_apply]
    · have he'' : Continuous e.symm.symm := by simpa using he
      have h1 := hfc.comp_homeomorph (glEquiv e.symm he' he'').toHomeomorph
      have h2 : (f ∘ ⇑(glEquiv e.symm he' he'').toHomeomorph) = fm := by
        funext g
        show f (glEquiv e.symm he' he'' g) = fm g
        rw [glEquiv_apply, hfm]
      rwa [h2] at h1

  have key := fun (c' : ℝˣ) (hc' : 0 < (c' : ℝ)) =>
    hram (@Measure.map _ _ (glBorelOf (w.comap (algebraMap K L)).Completion) (glBorelOf ℝ) (Matrix.GeneralLinearGroup.map e.toRingHom) μ)
      (@Measure.map _ _ (glBorelOf (L ⊗[K] (w.comap (algebraMap K L)).Completion)) (glBorelOf (ℂ ⊗[ℝ] ℝ))
        (Matrix.GeneralLinearGroup.map E.toRingHom) μ')
      hμA hμL φm hφm_smooth fm hfm_smooth c' hc'
  rw [← hφeq] at hI'm
  rw [hfeq] at hIm

  have hEι1 : ∀ x : (w.comap (algebraMap K L)).Completion, E ((1 : L) ⊗ₜ[K] x) = (1 : ℂ) ⊗ₜ[ℝ] e x := by
    intro x
    apply (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _ (Algebra.TensorProduct.rid ℝ ℝ ℂ)).injective
    rw [h7, map_one, one_mul]
    symm
    show (Algebra.TensorProduct.rid ℝ ℝ ℂ) ((1 : ℂ) ⊗ₜ[ℝ] e x) = ((e x : ℝ) : ℂ)
    rw [Algebra.TensorProduct.rid_tmul, Complex.real_smul, mul_one]
  have hgramM := AutomorphicForm.exists_gram_map_of_ringEquiv_of_exists_gram σ Complex.conjAe e he he' E hE hE' hEσ hEι1 hEr
    (Matrix.GeneralLinearGroup.scalar (Fin 2) c) _ rfl δ _ rfl τ τ₀ τ' τ₀' hτ₀c hτ₀'c hgram
  generalize hg : Matrix.GeneralLinearGroup.map e.toRingHom (Matrix.GeneralLinearGroup.scalar (Fin 2) c) = γ'
    at hN' τ₀ hτ₀ hτ₀c hgramM hIm
  have hγ' : γ' = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (e : (w.comap (algebraMap K L)).Completion →* ℝ) c) := by
    rw [← hg, map_scalar]
  subst hγ'

  have hmm : ∃ V ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (e : (w.comap (algebraMap K L)).Completion →* ℝ) c)),
      ∀ δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ), IsRegularSemisimple (normString ℝ ℂ ℝ Complex.conjAe δ) →
      ∀ γ ∈ V, IsRegularSemisimple γ →
      ∀ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ), IsNormConjugator ℝ ℂ ℝ Complex.conjAe γ δ y →
      ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℝ))) (centralizerBorel ℝ γ))
        (τ' : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ)),
        @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ γ) τ →
        @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) τ' →
        Coupled ℝ ℂ ℝ Complex.conjAe γ δ y τ τ' →
        ∀ I I' : ℂ, IsTwistedOrbitalIntegralOn ℝ ℂ ℝ Complex.conjAe
            (@Measure.map _ _ (glBorelOf (L ⊗[K] (w.comap (algebraMap K L)).Completion)) (glBorelOf (ℂ ⊗[ℝ] ℝ))
              (Matrix.GeneralLinearGroup.map E.toRingHom) μ') δ τ'
            (fun z => φm (Matrix.GeneralLinearGroup.map (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _ (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom z : GL (Fin 2) ℂ)) I' →
          IsOrbitalIntegralOn ℝ
            (@Measure.map _ _ (glBorelOf (w.comap (algebraMap K L)).Completion) (glBorelOf ℝ) (Matrix.GeneralLinearGroup.map e.toRingHom) μ)
            γ τ fm I → I' = I := by
    obtain ⟨V, hV, hVm⟩ := hmatch
    have he'' : Continuous e.symm.symm := by simpa using he
    have hE'' : Continuous E.symm.symm := by simpa using hE
    have hEσ' : ∀ z, E.symm (sigmaTensor ℝ ℂ ℝ Complex.conjAe z) =
        sigmaTensor K L (w.comap (algebraMap K L)).Completion σ (E.symm z) := symm_sigmaTensor σ Complex.conjAe E hEσ
    have hEι' : ∀ g' : GL (Fin 2) ℝ, Matrix.GeneralLinearGroup.map E.symm.toRingHom (toTensorGL ℝ ℂ ℝ g') =
        toTensorGL K L (w.comap (algebraMap K L)).Completion (Matrix.GeneralLinearGroup.map e.symm.toRingHom g') :=
      symm_toTensorGL E e hEι
    have hcont : Continuous (Matrix.GeneralLinearGroup.map (n := Fin 2) e.symm.toRingHom) := by
      rw [← coe_glEquiv e.symm he' he'']; exact (glEquiv e.symm he' he'').continuous
    refine ⟨(Matrix.GeneralLinearGroup.map e.symm.toRingHom) ⁻¹' V, ?_, ?_⟩
    · apply hcont.continuousAt.preimage_mem_nhds
      have hsc : Matrix.GeneralLinearGroup.map e.symm.toRingHom
          (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (e : (w.comap (algebraMap K L)).Completion →* ℝ) c)) =
          Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
        rw [← map_scalar e c, map_symm_map]
      rw [hsc]
      exact hV
    · intro δₘ hδₘ γₘ hγₘ hγreg yₘ hyₘ τₘ τₘ' hτₘ hτₘ' hCₘ J J' hJ' hJ
      have hδ₂ : IsRegularSemisimple (normString K L (w.comap (algebraMap K L)).Completion σ (Matrix.GeneralLinearGroup.map E.symm.toRingHom δₘ)) := by
        rw [← map_normString Complex.conjAe σ E.symm hEσ' hrank.symm δₘ]
        exact isRegularSemisimple_map E.symm _ hδₘ
      have hγ₂ : IsRegularSemisimple (Matrix.GeneralLinearGroup.map e.symm.toRingHom γₘ) :=
        isRegularSemisimple_map e.symm γₘ hγreg
      have hγ₂V : Matrix.GeneralLinearGroup.map e.symm.toRingHom γₘ ∈ V := hγₘ
      have hTTC₂ := AutomorphicForm.isNormConjugator_map_iff_and_coupled_map_iff_of_ringEquiv Complex.conjAe σ
        hrank.symm e.symm he' he'' E.symm hE' hE'' hEσ' hEι' γₘ δₘ yₘ
      have hN₂ := hTTC₂.1.mp hyₘ
      obtain ⟨τ₂, hτ₂, hτ₂c, -⟩ := centralizer_forward_gl e.symm he' he'' γₘ τₘ hτₘ
      obtain ⟨τ₂', hτ₂', hτ₂'c, -⟩ := twistedCentralizer_forward_gl Complex.conjAe σ E.symm hE' hE'' hEσ' δₘ τₘ' hτₘ'
      have hC₂ := (hTTC₂.2 τₘ τ₂ τₘ' τ₂' hτ₂c hτ₂'c).mp hCₘ
      have hTTV₂ := AutomorphicForm.isTwistedOrbitalIntegralOn_map_of_ringEquiv_and_isHaarMeasure_map Complex.conjAe σ
        E.symm hE' hE'' hEσ'
        (@Measure.map _ _ (glBorelOf (L ⊗[K] (w.comap (algebraMap K L)).Completion)) (glBorelOf (ℂ ⊗[ℝ] ℝ))
          (Matrix.GeneralLinearGroup.map E.toRingHom) μ') δₘ
      have hJ'₂ := hTTV₂.1 τₘ' τ₂' hτ₂'c _ J' hJ'
      have h84 := AutomorphicForm.isOrbitalIntegralOn_map_generalLinearGroup_map_of_ringEquiv e.symm he' he''
        (@Measure.map _ _ (glBorelOf (w.comap (algebraMap K L)).Completion) (glBorelOf ℝ) (Matrix.GeneralLinearGroup.map e.toRingHom) μ)
        γₘ τₘ τ₂ hτ₂c fm J hJ

      have hmE : Measurable (⇑(Matrix.GeneralLinearGroup.map (n := Fin 2) E.toRingHom)) :=
        ((glE E hE hE').continuous.congr (fun g => glE_apply E hE hE' g)).measurable
      have hmE' : Measurable (⇑(Matrix.GeneralLinearGroup.map (n := Fin 2) E.symm.toRingHom)) :=
        ((glE E.symm hE' hE'').continuous.congr (fun g => glE_apply E.symm hE' hE'' g)).measurable
      have hme : Measurable (⇑(Matrix.GeneralLinearGroup.map (n := Fin 2) e.toRingHom)) := by
        rw [← coe_glEquiv e he he']; exact (glEquiv e he he').continuous.measurable
      have hme' : Measurable (⇑(Matrix.GeneralLinearGroup.map (n := Fin 2) e.symm.toRingHom)) := by
        rw [← coe_glEquiv e.symm he' he'']; exact (glEquiv e.symm he' he'').continuous.measurable
      have hμ'back : Measure.map (⇑(Matrix.GeneralLinearGroup.map E.symm.toRingHom))
          (Measure.map (⇑(Matrix.GeneralLinearGroup.map E.toRingHom)) μ') = μ' := by
        rw [Measure.map_map hmE' hmE,
          show (⇑(Matrix.GeneralLinearGroup.map E.symm.toRingHom) ∘ ⇑(Matrix.GeneralLinearGroup.map (n := Fin 2) E.toRingHom)) = id
            from funext (map_symm_map E), Measure.map_id]
      have hμback : Measure.map (⇑(Matrix.GeneralLinearGroup.map e.symm.toRingHom))
          (Measure.map (⇑(Matrix.GeneralLinearGroup.map e.toRingHom)) μ) = μ := by
        rw [Measure.map_map hme' hme,
          show (⇑(Matrix.GeneralLinearGroup.map e.symm.toRingHom) ∘ ⇑(Matrix.GeneralLinearGroup.map (n := Fin 2) e.toRingHom)) = id
            from funext (map_symm_map e), Measure.map_id]
      have hψ : ((fun z : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) => φm (Matrix.GeneralLinearGroup.map (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _ (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom z : GL (Fin 2) ℂ)) ∘
          ⇑(Matrix.GeneralLinearGroup.map E.symm.symm.toRingHom)) = φ := by
        funext z
        simp only [Function.comp_apply, RingEquiv.symm_symm]
        rw [hφm, map_symm_map, map_symm_map]
      have hf' : (fm ∘ ⇑(Matrix.GeneralLinearGroup.map e.symm.symm.toRingHom)) = f := by
        funext g
        simp only [Function.comp_apply, RingEquiv.symm_symm]
        rw [hfm, map_symm_map]
      rw [hμ'back, hψ] at hJ'₂
      rw [hμback, hf'] at h84
      exact hVm _ hδ₂ _ hγ₂V hγ₂ _ hN₂ τ₂ τ₂' hτ₂ hτ₂' hC₂ J J' hJ'₂ h84

  haveI : LocallyCompactSpace (GL (Fin 2) ℝ) := by
    haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) ℝ) :=
      inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → ℝ))
    exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SecondCountableTopology (GL (Fin 2) ℝ) := by
    haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℝ) :=
      inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℝ))
    haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℝ)ᵐᵒᵖ :=
      MulOpposite.opHomeomorph.symm.secondCountableTopology
    exact Units.isEmbedding_embedProduct.secondCountableTopology
  haveI := hμA
  haveI := hτ₀
  obtain ⟨hτ₀inv, hτ₀sf⟩ :=
    isInvInvariant_and_sFinite_of_isHaarMeasure_centralizer_scalar ℝ (Units.map (e : (w.comap (algebraMap K L)).Completion →* ℝ) c) τ₀
  haveI := hτ₀inv
  haveI := hτ₀sf

  have hEσ' : ∀ z, E.symm (sigmaTensor ℝ ℂ ℝ Complex.conjAe z) =
      sigmaTensor K L (w.comap (algebraMap K L)).Completion σ (E.symm z) := symm_sigmaTensor σ Complex.conjAe E hEσ
  have hkindT : (∃ z : (L ⊗[K] (w.comap (algebraMap K L)).Completion)ˣ,
        IsSigmaConjugate K L (w.comap (algebraMap K L)).Completion σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z)) ↔
      (∃ z' : (ℂ ⊗[ℝ] ℝ)ˣ, IsSigmaConjugate ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.map E.toRingHom δ)
        (Matrix.GeneralLinearGroup.scalar (Fin 2) z')) := by
    constructor
    · rintro ⟨z, x, hx⟩
      refine ⟨Units.map (E : L ⊗[K] (w.comap (algebraMap K L)).Completion →* ℂ ⊗[ℝ] ℝ) z, Matrix.GeneralLinearGroup.map E.toRingHom x, ?_⟩
      rw [← map_scalar E z, hx, map_mul, map_mul, map_inv, map_sigmaGL σ Complex.conjAe E hEσ]
    · rintro ⟨z', x', hx'⟩
      refine ⟨Units.map (E.symm : ℂ ⊗[ℝ] ℝ →* L ⊗[K] (w.comap (algebraMap K L)).Completion) z', Matrix.GeneralLinearGroup.map E.symm.toRingHom x', ?_⟩
      have h := congrArg (Matrix.GeneralLinearGroup.map E.symm.toRingHom) hx'
      rw [map_mul, map_mul, map_inv, map_symm_map, map_sigmaGL Complex.conjAe σ E.symm hEσ', map_scalar] at h
      exact h
  have hkm := hkind (Units.map (e : (w.comap (algebraMap K L)).Completion →* ℝ) c) _ _ hN'
  refine ⟨fun hk => ?_, fun hk => ?_⟩
  ·
    have hc' : 0 < ((Units.map (e : (w.comap (algebraMap K L)).Completion →* ℝ) c) : ℝ) := hkm.1 (hkindT.1 hk)
    obtain ⟨y'', hN'', hC''⟩ := AutomorphicForm.exists_isNormConjugator_and_coupled_of_gram_conjAe_of_pos (Units.map (e : (w.comap (algebraMap K L)).Completion →* ℝ) c) hc'
      _ _ hN' τ₀ τ₀' hτ₀ hτ₀' hgramM
    have hJ := key (Units.map (e : (w.comap (algebraMap K L)).Completion →* ℝ) c) hc' hmm _ _ hN'' τ₀ τ₀' hτ₀ hτ₀' hC'' I' hI'm
    exact isOrbitalIntegralOn_scalar_unique ℝ (Units.map (e : (w.comap (algebraMap K L)).Completion →* ℝ) c) _ τ₀ fm I' I hJ hIm
  ·
    have hc' : ((Units.map (e : (w.comap (algebraMap K L)).Completion →* ℝ) c) : ℝ) < 0 := by
      rcases lt_or_gt_of_ne (Units.ne_zero (Units.map (e : (w.comap (algebraMap K L)).Completion →* ℝ) c)) with h | h
      · exact h
      · exact absurd (hkindT.2 (hkm.2 h)) hk
    have hJ := AutomorphicForm.isOrbitalIntegralOn_scalar_neg_of_isTwistedOrbitalIntegralOn_conjAe_of_gram_of_nhds_forall_isNormConjugator_of_neg
      _ _ hμA hμL φm hφm_smooth fm hfm_smooth (Units.map (e : (w.comap (algebraMap K L)).Completion →* ℝ) c) hc' hmm _ _ hN' τ₀ τ₀' hτ₀ hτ₀' hgramM I' hI'm
    have h := isOrbitalIntegralOn_scalar_unique ℝ (Units.map (e : (w.comap (algebraMap K L)).Completion →* ℝ) c) _ τ₀ fm (-I') I hJ hIm
    exact neg_eq_iff_eq_neg.mp h

end AutomorphicForm.CentAsmLocal
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.FDTEF P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CasmGram P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.P2mGramSide"
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.FDTEF P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CasmGram P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.P2mGramSide"

set_option autoImplicit false

p2m_open "MeasureTheory NumberField NumberField.InfinitePlace.NumberField AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm"
open scoped TensorProduct
open scoped TensorProduct.RightActions

namespace AutomorphicForm
p2m_export "AutomorphicForm" "isTopologicalRing_tensor t2Space_tensor locallyCompactSpace_tensor isTopologicalGroup_tensorGL t2Space_tensorGL locallyCompactSpace_tensorGL glBorelOf borelSpace_glBorelOf centralizerBorel toTensorGL sigmaTensor sigmaGL normString IsSigmaConjugate IsNormConjugator IsNormOf twistedCentralizer twistedCentralizerBorel IsSectionFnOn IsOrbitalIntegralOn IsTwistedSectionFnOn IsTwistedOrbitalIntegralOn Coupled AreMatchingOn archHaarK archHaarL archIdent archIdentGL AreMatchingArch IsRegularSemisimple archEntries_apply IsArchTestFactor sigmaCentralizer mem_sigmaCentralizer_iff SplitPlace.psi SplitPlace.psiEquiv SplitPlace.psiEquiv_apply SplitPlace.psiEquiv_symm_const SplitPlace.psiGL exists_mulEquiv_generalLinearGroup_tensorProduct_infiniteAdeleRing_pi exists_ringEquiv_tensorProduct_infiniteAdeleRing_pi_forall_tmul archIdent_tmul_apply exists_continuous_isSectionFnOn_and_isOrbitalIntegralOn_iff_completion_of_isRegularSemisimple exists_isTwistedSectionFnOn_and_continuous_completion_of_isRegularSemisimple_normString exists_isTwistedSectionFnOn_and_continuous_completion_of_isSigmaConjugate_scalar_of_prime semilocal_central_transfer_of_forall_oneplace_of_referenceMeasures exists_isNormConjugator_and_coupled_of_gram_of_algHom_real exists_isNormConjugator_and_coupled_of_gram_of_algHom_complex exists_isNormConjugator_and_coupled_of_gram_conjAe_of_pos isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar map_centralizer_map_ringEquiv_pi_eq_smul_gram_of_infiniteAdeleRing map_twistedCentralizer_map_ringEquiv_pi_eq_smul_gram_of_infiniteAdeleRing mem_span_map_ringEquiv_pi_iff_of_span_eq_range_includeRight mem_span_map_ringEquiv_pi_iff_of_span_eq_setOf_mul_eq_mul_map_sigmaTensor exists_gram_map_of_ringEquiv_of_exists_gram exists_ringEquiv_tensor_completion_complex_of_isRamified isTwistedOrbitalIntegralOn_map_of_ringEquiv_and_isHaarMeasure_map isNormConjugator_map_iff_and_coupled_map_iff_of_ringEquiv isOrbitalIntegralOn_map_generalLinearGroup_map_of_ringEquiv isHaarMeasure_map_and_exists_isHaarMeasure_centralizer_of_ringEquiv pos_and_exists_coupled_toTensorGL_scalar_one_iff_of_coupled_scalar_conjAe exists_ringEquiv_tensor_baseChange_of_ringEquiv isOrbitalIntegralOn_scalar_neg_of_isTwistedOrbitalIntegralOn_conjAe_of_gram_of_nhds_forall_isNormConjugator_of_neg exists_isSigmaConjugate_scalar_of_isNormConjugator_scalar_of_algHom_of_prime exists_isTwistedSectionFnOn_and_continuous_completion_of_not_isSigmaConjugate_scalar_of_finrank_eq_two exists_isSigmaConjugate_scalar_conjAe_iff_pos_of_isNormConjugator_scalar"
namespace CasmGram
p2m_open "AutomorphicForm"

p2m_open "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.FDTEF NumberField.InfinitePlace NumberField.InfinitePlace.NumberField.InfinitePlace"
open scoped NNReal

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

attribute [local instance] algR algE

theorem locallyCompactSpace_tensorGL_completion' (v : InfinitePlace K) :
    LocallyCompactSpace (GL (Fin 2) (L ⊗[K] v.Completion)) :=
  AutomorphicForm.locallyCompactSpace_tensorGL K L _

theorem isTopologicalGroup_tensorGL_completion' (v : InfinitePlace K) :
    IsTopologicalGroup (GL (Fin 2) (L ⊗[K] v.Completion)) :=
  AutomorphicForm.isTopologicalGroup_tensorGL K L _

attribute [local instance 10000] AutomorphicForm.glBorelOf
attribute [local instance] FDTEF.borelSpace_gl FDTEF.locallyCompactSpace_gl FDTEF.secondCountableTopology_gl
  FDTEF.t2Space_gl FDTEF.secondCountableTopology_completion
  locallyCompactSpace_tensorGL_completion' isTopologicalGroup_tensorGL_completion'

theorem coe_WK_eq_range (i : InfinitePlace K) :
    (WK K L i : Set (V K L i)) =
      Set.range (fun Y : Matrix (Fin 2) (Fin 2) i.Completion => Y.map (fun x : i.Completion => (1 : L) ⊗ₜ[K] x)) := by
  let W' : Submodule ℝ (V K L i) :=
    { carrier := Set.range (fun Y : Matrix (Fin 2) (Fin 2) i.Completion =>
        Y.map (fun x : i.Completion => (1 : L) ⊗ₜ[K] x))
      add_mem' := by
        rintro _ _ ⟨Y₁, rfl⟩ ⟨Y₂, rfl⟩
        refine ⟨Y₁ + Y₂, ?_⟩
        ext a b
        simp [Matrix.map_apply, TensorProduct.tmul_add]
      zero_mem' := ⟨0, by ext a b; simp [Matrix.map_apply]⟩
      smul_mem' := by
        rintro r _ ⟨Y, rfl⟩
        refine ⟨(algebraMap ℝ (InfiniteAdeleRing K) r i) • Y, ?_⟩
        ext a b
        simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
        rw [Algebra.smul_def]
        change ((1 : L) ⊗ₜ[K] (algebraMap ℝ (InfiniteAdeleRing K) r i * Y a b)) =
          ((1 : L) ⊗ₜ[K] (algebraMap ℝ (InfiniteAdeleRing K) r i)) * ((1 : L) ⊗ₜ[K] Y a b)
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul] }
  have hW' : (W' : Set (V K L i)) = Set.range (fun Y : Matrix (Fin 2) (Fin 2) i.Completion =>
      Y.map (fun x : i.Completion => (1 : L) ⊗ₜ[K] x)) := rfl
  rw [WK, ← hW', Submodule.span_eq]

theorem coe_WL_eq_setOf (σ : L ≃ₐ[K] L) (i : InfinitePlace K) (δ' : Matrix (Fin 2) (Fin 2) (L ⊗[K] i.Completion)) :
    (WL K L σ i δ' : Set (V K L i)) =
      {Y : Matrix (Fin 2) (Fin 2) (L ⊗[K] i.Completion) |
        Y * δ' = δ' * Y.map (AutomorphicForm.sigmaTensor K L i.Completion σ)} := by
  have hσ1 : ∀ a : i.Completion, AutomorphicForm.sigmaTensor K L i.Completion σ ((1 : L) ⊗ₜ[K] a) = (1 : L) ⊗ₜ[K] a := by
    intro a
    simp [AutomorphicForm.sigmaTensor]
  let W' : Submodule ℝ (V K L i) :=
    { carrier := {Y : Matrix (Fin 2) (Fin 2) (L ⊗[K] i.Completion) |
        Y * δ' = δ' * Y.map (AutomorphicForm.sigmaTensor K L i.Completion σ)}
      add_mem' := by
        intro Y₁ Y₂ h₁ h₂
        simp only [Set.mem_setOf_eq] at h₁ h₂ ⊢
        rw [Matrix.map_add _ (map_add (AutomorphicForm.sigmaTensor K L i.Completion σ)), add_mul, mul_add, h₁, h₂]
      zero_mem' := by
        simp only [Set.mem_setOf_eq]
        rw [Matrix.map_zero _ (map_zero _), zero_mul, mul_zero]
      smul_mem' := by
        intro r Y h
        simp only [Set.mem_setOf_eq] at h ⊢
        have hmap : (r • Y).map (AutomorphicForm.sigmaTensor K L i.Completion σ) =
            r • Y.map (AutomorphicForm.sigmaTensor K L i.Completion σ) := by
          ext a b
          simp only [Matrix.smul_apply, Matrix.map_apply]
          rw [Algebra.smul_def, Algebra.smul_def, map_mul]
          congr 1
          exact hσ1 _
        rw [hmap, Matrix.smul_mul, h]
        exact (Matrix.mul_smul δ' r _).symm }
  have hW' : (W' : Set (V K L i)) = {Y : Matrix (Fin 2) (Fin 2) (L ⊗[K] i.Completion) |
      Y * δ' = δ' * Y.map (AutomorphicForm.sigmaTensor K L i.Completion σ)} := rfl
  rw [WL, ← hW', Submodule.span_eq]

set_option maxHeartbeats 4000000 in

theorem gram_of_rel (σ : L ≃ₐ[K] L) (c : (InfiniteAdeleRing K)ˣ) (w : InfinitePlace K)
    (δ y : GL (Fin 2) (L ⊗[K] w.Completion))
    (hN : IsNormConjugator K L w.Completion σ (Matrix.GeneralLinearGroup.scalar (Fin 2) (unitAt K c w)) δ y)
    (τ : @Measure (Subgroup.centralizer
        ({Matrix.GeneralLinearGroup.scalar (Fin 2) (unitAt K c w)} : Set (GL (Fin 2) w.Completion)))
        (centralizerBorel w.Completion (Matrix.GeneralLinearGroup.scalar (Fin 2) (unitAt K c w))))
    (τ' : @Measure (twistedCentralizer K L w.Completion σ δ) (twistedCentralizerBorel K L w.Completion σ δ))
    (s : ℝ≥0) (hs0 : s ≠ 0)
    (hRK : @Measure.map _ _ (centralizerBorel w.Completion (Matrix.GeneralLinearGroup.scalar (Fin 2) (unitAt K c w))) _
        (fun t : Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) (unitAt K c w)} :
          Set (GL (Fin 2) w.Completion)) => κ K L w (t : GL (Fin 2) w.Completion)) τ = s • m K L w)
    (hRL : @Measure.map _ _ (twistedCentralizerBorel K L w.Completion σ δ) _
        (fun t : twistedCentralizer K L w.Completion σ δ => κ' K L w (t : GL (Fin 2) (L ⊗[K] w.Completion))) τ' =
          s • m' K L σ c w δ) :
    (letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] w.Completion)) := borel _;
       letI := centralizerBorel w.Completion (Matrix.GeneralLinearGroup.scalar (Fin 2) (unitAt K c w));
       letI := twistedCentralizerBorel K L w.Completion σ δ;
       ∃ (n₁ n₂ : ℕ) (e₁ : Fin n₁ → Matrix (Fin 2) (Fin 2) (L ⊗[K] w.Completion))
         (e₂ : Fin n₂ → Matrix (Fin 2) (Fin 2) (L ⊗[K] w.Completion)) (s : ENNReal),
         s ≠ 0 ∧ s ≠ ⊤ ∧
         LinearIndependent ℝ e₁ ∧
           (Submodule.span ℝ (Set.range e₁) : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] w.Completion))) =
             Set.range (fun Y : Matrix (Fin 2) (Fin 2) w.Completion =>
               Y.map (fun x : w.Completion => ((1 : L) ⊗ₜ[K] x : L ⊗[K] w.Completion))) ∧
         LinearIndependent ℝ e₂ ∧
           (Submodule.span ℝ (Set.range e₂) : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] w.Completion))) =
             {X | X * (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] w.Completion)) =
               (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] w.Completion)) * X.map (sigmaTensor K L w.Completion σ)} ∧
         Measure.map (fun t : ↥(Subgroup.centralizer ({(Matrix.GeneralLinearGroup.scalar (Fin 2) (unitAt K c w))} : Set (GL (Fin 2) w.Completion))) =>
             ((t : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).map
               (fun x : w.Completion => ((1 : L) ⊗ₜ[K] x : L ⊗[K] w.Completion))) τ =
           s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₁ =>
                   Algebra.trace ℝ (L ⊗[K] w.Completion) (Matrix.trace (e₁ i * e₁ j))).det|)) •
                 Measure.map (fun a : Fin n₁ → ℝ => ∑ i, a i • e₁ i) volume).withDensity
               (fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] w.Completion) =>
                 (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹) ∧
         Measure.map (fun t : ↥(twistedCentralizer K L w.Completion σ δ) =>
             ((t : GL (Fin 2) (L ⊗[K] w.Completion)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] w.Completion))) τ' =
           s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
                   Algebra.trace ℝ (L ⊗[K] w.Completion) (Matrix.trace (e₂ i * e₂ j))).det|)) •
                 Measure.map (fun a : Fin n₂ → ℝ => ∑ i, a i • e₂ i) volume).withDensity
               (fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] w.Completion) =>
                 (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹)) := by
  classical
  haveI := moduleFinite_tensor_completion K L w
  have hexK := exists_basis_of_submodule K L w (WK K L w)
  have hexL := exists_basis_of_submodule K L w
    (WL K L σ w ((δ : GL (Fin 2) (L ⊗[K] w.Completion)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] w.Completion)))
  rw [m, dif_pos hexK, ENNReal.smul_def] at hRK
  rw [m', if_pos ⟨y, hN⟩, dif_pos hexL, ENNReal.smul_def] at hRL
  refine ⟨_, _, hexK.choose_spec.choose, hexL.choose_spec.choose, (s : ENNReal), ?_, ENNReal.coe_ne_top,
    hexK.choose_spec.choose_spec.1, ?_, hexL.choose_spec.choose_spec.1, ?_, hRK, hRL⟩
  · exact_mod_cast hs0
  · rw [hexK.choose_spec.choose_spec.2]; exact coe_WK_eq_range K L w
  · rw [hexL.choose_spec.choose_spec.2]; exact coe_WL_eq_setOf K L σ w _

set_option maxHeartbeats 6400000 in

theorem coupled_of_gram_real
    (hprime : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : InfinitePlace K) (hv : v.IsReal)
    (hsplit : ∀ w : InfinitePlace L, w.comap (algebraMap K L) = v → ¬ w.IsRamified K)
    (c : (v.Completion)ˣ) (δ y : GL (Fin 2) (L ⊗[K] v.Completion))
    (hN : IsNormConjugator K L v.Completion σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y)
    (τ : @Measure (Subgroup.centralizer
          ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) v.Completion)))
          (centralizerBorel v.Completion (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
    (τ' : @Measure (twistedCentralizer K L v.Completion σ δ) (twistedCentralizerBorel K L v.Completion σ δ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel v.Completion (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) τ)
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L v.Completion σ δ) τ')
    (hG : (letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] v.Completion)) := borel _
       letI := centralizerBorel v.Completion (Matrix.GeneralLinearGroup.scalar (Fin 2) c)
       letI := twistedCentralizerBorel K L v.Completion σ δ
       ∃ (n₁ n₂ : ℕ) (e₁ : Fin n₁ → Matrix (Fin 2) (Fin 2) (L ⊗[K] v.Completion))
         (e₂ : Fin n₂ → Matrix (Fin 2) (Fin 2) (L ⊗[K] v.Completion)) (s : ENNReal),
         s ≠ 0 ∧ s ≠ ⊤ ∧
         LinearIndependent ℝ e₁ ∧
           (Submodule.span ℝ (Set.range e₁) : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] v.Completion))) =
             Set.range (fun Y : Matrix (Fin 2) (Fin 2) v.Completion =>
               Y.map (fun x : v.Completion => ((1 : L) ⊗ₜ[K] x : L ⊗[K] v.Completion))) ∧
         LinearIndependent ℝ e₂ ∧
           (Submodule.span ℝ (Set.range e₂) : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] v.Completion))) =
             {X | X * (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.Completion)) =
               (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.Completion)) * X.map (sigmaTensor K L v.Completion σ)} ∧
         Measure.map (fun t : ↥(Subgroup.centralizer ({(Matrix.GeneralLinearGroup.scalar (Fin 2) c)} : Set (GL (Fin 2) v.Completion))) =>
             ((t : GL (Fin 2) v.Completion) : Matrix (Fin 2) (Fin 2) v.Completion).map
               (fun x : v.Completion => ((1 : L) ⊗ₜ[K] x : L ⊗[K] v.Completion))) τ =
           s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₁ =>
                   Algebra.trace ℝ (L ⊗[K] v.Completion) (Matrix.trace (e₁ i * e₁ j))).det|)) •
                 Measure.map (fun a : Fin n₁ → ℝ => ∑ i, a i • e₁ i) volume).withDensity
               (fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.Completion) =>
                 (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹) ∧
         Measure.map (fun t : ↥(twistedCentralizer K L v.Completion σ δ) =>
             ((t : GL (Fin 2) (L ⊗[K] v.Completion)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.Completion))) τ' =
           s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
                   Algebra.trace ℝ (L ⊗[K] v.Completion) (Matrix.trace (e₂ i * e₂ j))).det|)) •
                 Measure.map (fun a : Fin n₂ → ℝ => ∑ i, a i • e₂ i) volume).withDensity
               (fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.Completion) =>
                 (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹))) :
    ∃ y' : GL (Fin 2) (L ⊗[K] v.Completion),
      IsNormConjugator K L v.Completion σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y' ∧
      Coupled K L v.Completion σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y' τ τ' := by
  classical
  let e : v.Completion ≃+* ℝ := Completion.ringEquivRealOfIsReal hv
  have he : Continuous e := (Completion.isometryEquivRealOfIsReal hv).continuous
  have he' : Continuous e.symm := (Completion.isometryEquivRealOfIsReal hv).symm.continuous
  letI instKR : Algebra K ℝ := (e.toRingHom.comp (algebraMap K v.Completion)).toAlgebra
  obtain ⟨E, hE, hE', hEt, hEσ, hEe⟩ :=
    AutomorphicForm.exists_ringEquiv_tensor_baseChange_of_ringEquiv K L σ v.Completion ℝ e he he'
  obtain ⟨w, hw⟩ : ∃ w : InfinitePlace L, w.comap (algebraMap K L) = v := NumberField.InfinitePlace.comap_surjective v
  have hun : w.IsUnramified K := by simpa [NumberField.InfinitePlace.IsRamified] using hsplit w hw
  obtain ⟨ι₀⟩ := NumberField.InfinitePlace.nonempty_algHom_completion_of_isUnramified K L v w hw hun
  let ι : L →ₐ[K] ℝ :=
    { toRingHom := e.toRingHom.comp ι₀.toRingHom
      commutes' := fun k => by
        show e (ι₀ (algebraMap K L k)) = e (algebraMap K v.Completion k)
        rw [ι₀.commutes] }
  haveI : IsTopologicalRing (L ⊗[K] v.Completion) := isTopologicalRing_tensor K L v.Completion
  haveI : IsTopologicalRing (L ⊗[K] ℝ) := isTopologicalRing_tensor K L ℝ
  set c' : ℝˣ := Units.map (e : v.Completion →* ℝ) c with hc'
  have hsc : Matrix.GeneralLinearGroup.map e.toRingHom (Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) c' := AutomorphicForm.CentAsmLocal.map_scalar e c

  obtain ⟨τ₀, hτ₀, hτ₀rel, -⟩ :=
    AutomorphicForm.O6Split.exists_isHaarMeasure_centralizer_scalar_forward v.Completion ℝ e he he' c τ hτ
  obtain ⟨τ₀', hτ₀', hτ₀'rel, -⟩ :=
    AutomorphicForm.O6Split.exists_isHaarMeasure_twistedCentralizer_forward K L σ v.Completion ℝ E hE hE' hEσ δ τ' hτ'

  have hEι : ∀ x : v.Completion, E ((1 : L) ⊗ₜ[K] x) = (1 : L) ⊗ₜ[K] e x := fun x => hEt 1 x
  have hea : ∀ r : ℝ, e (algebraMap ℝ (InfiniteAdeleRing K) r v) = r := by
    intro r
    have h1 := congrArg (fun z : mixedEmbedding.mixedSpace K => z.1 ⟨v, hv⟩)
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply (algebraMap ℝ (mixedEmbedding.mixedSpace K) r))
    simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply, Prod.algebraMap_apply, Pi.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply] at h1
    exact h1
  have hEr : ∀ (r : ℝ) (z : L ⊗[K] v.Completion), E (r • z) = r • E z := by
    intro r z
    have h2 : r • E z = algebraMap ℝ (L ⊗[K] ℝ) r * E z := Algebra.smul_def r (E z)
    rw [Algebra.smul_def, map_mul, h2]
    congr 1
    change E ((1 : L) ⊗ₜ[K] (algebraMap ℝ (InfiniteAdeleRing K) r v)) = (1 : L) ⊗ₜ[K] r
    rw [hEt, hea]

  have hGm := AutomorphicForm.exists_gram_map_of_ringEquiv_of_exists_gram (σ := σ) (σ' := σ) e he he' E hE hE' hEσ hEι hEr
    (Matrix.GeneralLinearGroup.scalar (Fin 2) c) (Matrix.GeneralLinearGroup.scalar (Fin 2) c') hsc
    δ (Matrix.GeneralLinearGroup.map E.toRingHom δ) rfl τ τ₀ τ' τ₀' hτ₀rel hτ₀'rel hG

  obtain ⟨hNiff, hCiff⟩ :=
    AutomorphicForm.isNormConjugator_map_iff_and_coupled_map_iff_of_ringEquiv (σ := σ) (σ' := σ) rfl
      e he he' E hE hE' hEσ hEe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y
  rw [hsc] at hNiff
  have hN' := hNiff.1 hN

  obtain ⟨ym, hNm, hCm⟩ := AutomorphicForm.exists_isNormConjugator_and_coupled_of_gram_of_algHom_real K L hprime σ hσ ι c'
    (Matrix.GeneralLinearGroup.map E.toRingHom δ) (Matrix.GeneralLinearGroup.map E.toRingHom y) hN' τ₀ τ₀' hτ₀ hτ₀' hGm

  refine ⟨Matrix.GeneralLinearGroup.map E.symm.toRingHom ym, ?_, ?_⟩
  · obtain ⟨hNiff', -⟩ :=
      AutomorphicForm.isNormConjugator_map_iff_and_coupled_map_iff_of_ringEquiv (σ := σ) (σ' := σ) rfl
        e he he' E hE hE' hEσ hEe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ
        (Matrix.GeneralLinearGroup.map E.symm.toRingHom ym)
    rw [hsc, AutomorphicForm.CentAsmLocal.map_map_symm] at hNiff'
    exact hNiff'.2 hNm
  · obtain ⟨-, hCiff'⟩ :=
      AutomorphicForm.isNormConjugator_map_iff_and_coupled_map_iff_of_ringEquiv (σ := σ) (σ' := σ) rfl
        e he he' E hE hE' hEσ hEe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ
        (Matrix.GeneralLinearGroup.map E.symm.toRingHom ym)
    rw [hsc, AutomorphicForm.CentAsmLocal.map_map_symm] at hCiff'
    exact (hCiff' τ τ₀ τ' τ₀' hτ₀rel hτ₀'rel).2 hCm

set_option maxHeartbeats 6400000 in

theorem coupled_of_gram_complex
    (hprime : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : InfinitePlace K) (hv : v.IsComplex)
    (hsplit : ∀ w : InfinitePlace L, w.comap (algebraMap K L) = v → ¬ w.IsRamified K)
    (c : (v.Completion)ˣ) (δ y : GL (Fin 2) (L ⊗[K] v.Completion))
    (hN : IsNormConjugator K L v.Completion σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y)
    (τ : @Measure (Subgroup.centralizer
          ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) v.Completion)))
          (centralizerBorel v.Completion (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
    (τ' : @Measure (twistedCentralizer K L v.Completion σ δ) (twistedCentralizerBorel K L v.Completion σ δ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel v.Completion (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) τ)
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L v.Completion σ δ) τ')
    (hG : (letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] v.Completion)) := borel _
       letI := centralizerBorel v.Completion (Matrix.GeneralLinearGroup.scalar (Fin 2) c)
       letI := twistedCentralizerBorel K L v.Completion σ δ
       ∃ (n₁ n₂ : ℕ) (e₁ : Fin n₁ → Matrix (Fin 2) (Fin 2) (L ⊗[K] v.Completion))
         (e₂ : Fin n₂ → Matrix (Fin 2) (Fin 2) (L ⊗[K] v.Completion)) (s : ENNReal),
         s ≠ 0 ∧ s ≠ ⊤ ∧
         LinearIndependent ℝ e₁ ∧
           (Submodule.span ℝ (Set.range e₁) : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] v.Completion))) =
             Set.range (fun Y : Matrix (Fin 2) (Fin 2) v.Completion =>
               Y.map (fun x : v.Completion => ((1 : L) ⊗ₜ[K] x : L ⊗[K] v.Completion))) ∧
         LinearIndependent ℝ e₂ ∧
           (Submodule.span ℝ (Set.range e₂) : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] v.Completion))) =
             {X | X * (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.Completion)) =
               (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.Completion)) * X.map (sigmaTensor K L v.Completion σ)} ∧
         Measure.map (fun t : ↥(Subgroup.centralizer ({(Matrix.GeneralLinearGroup.scalar (Fin 2) c)} : Set (GL (Fin 2) v.Completion))) =>
             ((t : GL (Fin 2) v.Completion) : Matrix (Fin 2) (Fin 2) v.Completion).map
               (fun x : v.Completion => ((1 : L) ⊗ₜ[K] x : L ⊗[K] v.Completion))) τ =
           s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₁ =>
                   Algebra.trace ℝ (L ⊗[K] v.Completion) (Matrix.trace (e₁ i * e₁ j))).det|)) •
                 Measure.map (fun a : Fin n₁ → ℝ => ∑ i, a i • e₁ i) volume).withDensity
               (fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.Completion) =>
                 (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹) ∧
         Measure.map (fun t : ↥(twistedCentralizer K L v.Completion σ δ) =>
             ((t : GL (Fin 2) (L ⊗[K] v.Completion)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.Completion))) τ' =
           s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
                   Algebra.trace ℝ (L ⊗[K] v.Completion) (Matrix.trace (e₂ i * e₂ j))).det|)) •
                 Measure.map (fun a : Fin n₂ → ℝ => ∑ i, a i • e₂ i) volume).withDensity
               (fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.Completion) =>
                 (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹))) :
    ∃ y' : GL (Fin 2) (L ⊗[K] v.Completion),
      IsNormConjugator K L v.Completion σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y' ∧
      Coupled K L v.Completion σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y' τ τ' := by
  classical
  let e : v.Completion ≃+* ℂ := Completion.ringEquivComplexOfIsComplex hv
  have he : Continuous e := (Completion.isometryEquivComplexOfIsComplex hv).continuous
  have he' : Continuous e.symm := (Completion.isometryEquivComplexOfIsComplex hv).symm.continuous
  letI instKR : Algebra K ℂ := (e.toRingHom.comp (algebraMap K v.Completion)).toAlgebra
  obtain ⟨E, hE, hE', hEt, hEσ, hEe⟩ :=
    AutomorphicForm.exists_ringEquiv_tensor_baseChange_of_ringEquiv K L σ v.Completion ℂ e he he'
  obtain ⟨w, hw⟩ : ∃ w : InfinitePlace L, w.comap (algebraMap K L) = v := NumberField.InfinitePlace.comap_surjective v
  have hun : w.IsUnramified K := by simpa [NumberField.InfinitePlace.IsRamified] using hsplit w hw
  obtain ⟨ι₀⟩ := NumberField.InfinitePlace.nonempty_algHom_completion_of_isUnramified K L v w hw hun
  let ι : L →ₐ[K] ℂ :=
    { toRingHom := e.toRingHom.comp ι₀.toRingHom
      commutes' := fun k => by
        show e (ι₀ (algebraMap K L k)) = e (algebraMap K v.Completion k)
        rw [ι₀.commutes] }
  haveI : IsTopologicalRing (L ⊗[K] v.Completion) := isTopologicalRing_tensor K L v.Completion
  haveI : IsTopologicalRing (L ⊗[K] ℂ) := isTopologicalRing_tensor K L ℂ
  set c' : ℂˣ := Units.map (e : v.Completion →* ℂ) c with hc'
  have hsc : Matrix.GeneralLinearGroup.map e.toRingHom (Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) c' := AutomorphicForm.CentAsmLocal.map_scalar e c

  obtain ⟨τ₀, hτ₀, hτ₀rel, -⟩ :=
    AutomorphicForm.O6Split.exists_isHaarMeasure_centralizer_scalar_forward v.Completion ℂ e he he' c τ hτ
  obtain ⟨τ₀', hτ₀', hτ₀'rel, -⟩ :=
    AutomorphicForm.O6Split.exists_isHaarMeasure_twistedCentralizer_forward K L σ v.Completion ℂ E hE hE' hEσ δ τ' hτ'

  have hEι : ∀ x : v.Completion, E ((1 : L) ⊗ₜ[K] x) = (1 : L) ⊗ₜ[K] e x := fun x => hEt 1 x
  have hea : ∀ r : ℝ, e (algebraMap ℝ (InfiniteAdeleRing K) r v) = (r : ℂ) := by
    intro r
    have h1 := congrArg (fun z : mixedEmbedding.mixedSpace K => z.2 ⟨v, hv⟩)
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply (algebraMap ℝ (mixedEmbedding.mixedSpace K) r))
    simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply, Prod.algebraMap_apply, Pi.algebraMap_apply,
      Complex.coe_algebraMap] at h1
    exact h1
  have hEr : ∀ (r : ℝ) (z : L ⊗[K] v.Completion), E (r • z) = r • E z := by
    intro r z
    have h2 : r • E z = algebraMap ℝ (L ⊗[K] ℂ) r * E z := Algebra.smul_def r (E z)
    rw [Algebra.smul_def, map_mul, h2]
    congr 1
    change E ((1 : L) ⊗ₜ[K] (algebraMap ℝ (InfiniteAdeleRing K) r v)) = (1 : L) ⊗ₜ[K] (algebraMap ℝ ℂ r)
    rw [hEt, hea]
    rfl

  have hGm := AutomorphicForm.exists_gram_map_of_ringEquiv_of_exists_gram (σ := σ) (σ' := σ) e he he' E hE hE' hEσ hEι hEr
    (Matrix.GeneralLinearGroup.scalar (Fin 2) c) (Matrix.GeneralLinearGroup.scalar (Fin 2) c') hsc
    δ (Matrix.GeneralLinearGroup.map E.toRingHom δ) rfl τ τ₀ τ' τ₀' hτ₀rel hτ₀'rel hG

  obtain ⟨hNiff, hCiff⟩ :=
    AutomorphicForm.isNormConjugator_map_iff_and_coupled_map_iff_of_ringEquiv (σ := σ) (σ' := σ) rfl
      e he he' E hE hE' hEσ hEe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y
  rw [hsc] at hNiff
  have hN' := hNiff.1 hN

  obtain ⟨ym, hNm, hCm⟩ := AutomorphicForm.exists_isNormConjugator_and_coupled_of_gram_of_algHom_complex K L hprime σ hσ ι c'
    (Matrix.GeneralLinearGroup.map E.toRingHom δ) (Matrix.GeneralLinearGroup.map E.toRingHom y) hN' τ₀ τ₀' hτ₀ hτ₀' hGm

  refine ⟨Matrix.GeneralLinearGroup.map E.symm.toRingHom ym, ?_, ?_⟩
  · obtain ⟨hNiff', -⟩ :=
      AutomorphicForm.isNormConjugator_map_iff_and_coupled_map_iff_of_ringEquiv (σ := σ) (σ' := σ) rfl
        e he he' E hE hE' hEσ hEe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ
        (Matrix.GeneralLinearGroup.map E.symm.toRingHom ym)
    rw [hsc, AutomorphicForm.CentAsmLocal.map_map_symm] at hNiff'
    exact hNiff'.2 hNm
  · obtain ⟨-, hCiff'⟩ :=
      AutomorphicForm.isNormConjugator_map_iff_and_coupled_map_iff_of_ringEquiv (σ := σ) (σ' := σ) rfl
        e he he' E hE hE' hEσ hEe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ
        (Matrix.GeneralLinearGroup.map E.symm.toRingHom ym)
    rw [hsc, AutomorphicForm.CentAsmLocal.map_map_symm] at hCiff'
    exact (hCiff' τ τ₀ τ' τ₀' hτ₀rel hτ₀'rel).2 hCm

omit [NumberField K] [NumberField L] in
theorem lam_eq_one_of_exists (σ : L ≃ₐ[K] L) (δg : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (i : InfinitePlace K)
    (h : ∃ z : (L ⊗[K] i.Completion)ˣ,
      AutomorphicForm.IsSigmaConjugate K L i.Completion σ
        (Matrix.GeneralLinearGroup.map
          (Algebra.TensorProduct.map (AlgHom.id K L)
            (Pi.evalAlgHom K (fun w : InfinitePlace K => w.Completion) i)).toRingHom δg)
        (Matrix.GeneralLinearGroup.scalar (Fin 2) z)) :
    lam K L σ δg i = 1 := by
  simp only [lam]; rw [if_pos h]

omit [NumberField K] [NumberField L] in
theorem lam_eq_neg_one_of_forall (σ : L ≃ₐ[K] L) (δg : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (i : InfinitePlace K)
    (h : ∀ z : (L ⊗[K] i.Completion)ˣ,
      ¬ AutomorphicForm.IsSigmaConjugate K L i.Completion σ
        (Matrix.GeneralLinearGroup.map
          (Algebra.TensorProduct.map (AlgHom.id K L)
            (Pi.evalAlgHom K (fun w : InfinitePlace K => w.Completion) i)).toRingHom δg)
        (Matrix.GeneralLinearGroup.scalar (Fin 2) z)) :
    lam K L σ δg i = -1 := by
  simp only [lam]; rw [if_neg (not_exists.mpr h)]

set_option maxHeartbeats 16000000 in

theorem isNormConjugator_eval (σ : L ≃ₐ[K] L) (c : (InfiniteAdeleRing K)ˣ)
    (δg yg : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
    (hδg : AutomorphicForm.IsNormConjugator K L (InfiniteAdeleRing K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δg yg)
    (i : InfinitePlace K) :
    AutomorphicForm.IsNormConjugator K L i.Completion σ (Matrix.GeneralLinearGroup.scalar (Fin 2) (unitAt K c i))
      (Matrix.GeneralLinearGroup.map
        (Algebra.TensorProduct.map (AlgHom.id K L) (Pi.evalAlgHom K (fun w : InfinitePlace K => w.Completion) i)).toRingHom δg)
      (Matrix.GeneralLinearGroup.map
        (Algebra.TensorProduct.map (AlgHom.id K L) (Pi.evalAlgHom K (fun w : InfinitePlace K => w.Completion) i)).toRingHom yg) := by
  set pr : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) →* GL (Fin 2) (L ⊗[K] i.Completion) :=
    Matrix.GeneralLinearGroup.map
      (Algebra.TensorProduct.map (AlgHom.id K L) (Pi.evalAlgHom K (fun w : InfinitePlace K => w.Completion) i)).toRingHom
    with hpr
  have hστ : ∀ z : L ⊗[K] ((w : InfinitePlace K) → w.Completion),
      (Algebra.TensorProduct.map (AlgHom.id K L) (Pi.evalAlgHom K (fun w : InfinitePlace K => w.Completion) i))
        (sigmaTensor K L ((w : InfinitePlace K) → w.Completion) σ z) =
      sigmaTensor K L i.Completion σ ((Algebra.TensorProduct.map (AlgHom.id K L)
        (Pi.evalAlgHom K (fun w : InfinitePlace K => w.Completion) i)) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | tmul x y =>
        simp only [sigmaTensor, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
          AlgHom.coe_id, id_eq, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe]
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add]
  have hσc : ∀ g, pr (sigmaGL K L (InfiniteAdeleRing K) σ g) = sigmaGL K L i.Completion σ (pr g) := by
    intro g
    refine Units.ext (Matrix.ext fun a b => ?_)
    exact hστ (((g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) a b)
  have hι : ∀ g : GL (Fin 2) (InfiniteAdeleRing K),
      pr (toTensorGL K L (InfiniteAdeleRing K) g) = toTensorGL K L i.Completion (FDTEF.thetaK K g i) := by
    intro g
    refine Units.ext (Matrix.ext fun a b => ?_)
    change (Algebra.TensorProduct.map (AlgHom.id K L) (Pi.evalAlgHom K (fun w : InfinitePlace K => w.Completion) i))
        ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K)
          ((g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) a b)) =
      (Algebra.TensorProduct.includeRight : i.Completion →ₐ[K] L ⊗[K] i.Completion)
        (((FDTEF.thetaK K g i : GL (Fin 2) i.Completion) : Matrix (Fin 2) (Fin 2) i.Completion) a b)
    rw [FDTEF.thetaK_val, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.includeRight_apply]
    exact Algebra.TensorProduct.map_tmul (AlgHom.id K L)
      (Pi.evalAlgHom K (fun w : InfinitePlace K => w.Completion) i) (1 : L) _
  unfold AutomorphicForm.IsNormConjugator at hδg ⊢
  have h := congrArg pr hδg
  rw [map_mul, map_mul, map_inv, FDTEF.map_normString σ pr hσc, hι] at h
  first
    | simpa only [FDTEF.thetaK_scalar, pr] using h
    | (simp only [FDTEF.thetaK_scalar, pr] at h; exact h)
    | (simp only [FDTEF.thetaK_scalar, pr] at h ⊢; exact h)

theorem sigma_ne_one' [IsGalois K L] (hprime : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) : σ ≠ 1 := by
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  rintro rfl
  have h1 : ∀ τ : L ≃ₐ[K] L, τ = 1 := fun τ => by
    have := hgen τ
    rwa [Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at this
  have hcard : Nat.card (L ≃ₐ[K] L) = 1 :=
    Nat.card_eq_one_iff_unique.2 ⟨⟨fun a b => by rw [h1 a, h1 b]⟩, ⟨1⟩⟩
  rw [IsGalois.card_aut_eq_finrank] at hcard
  exact hprime.ne_one hcard

set_option maxHeartbeats 16000000 in

theorem heng_rel
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (c : (InfiniteAdeleRing K)ˣ)
    (δg yg : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
    (hδg : AutomorphicForm.IsNormConjugator K L (InfiniteAdeleRing K) σ
      (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δg yg)
    (hprime : (Module.finrank K L).Prime)
    (hram : ∀
      (μA : @Measure (GL (Fin 2) ℝ) (glBorelOf ℝ))
      (μL : @Measure (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) (glBorelOf (ℂ ⊗[ℝ] ℝ)))
      (hμA : @Measure.IsHaarMeasure _ _ _ (glBorelOf ℝ) μA)
      (hμL : @Measure.IsHaarMeasure _ _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) μL)
      (φ : GL (Fin 2) ℂ → ℂ)
      (hφ : (∃ Φ : (Fin 2 → Fin 2 → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
        ∀ g, φ g = Φ (fun i j => (g : Matrix (Fin 2) (Fin 2) ℂ) i j)) ∧ HasCompactSupport φ)
      (f : GL (Fin 2) ℝ → ℂ)
      (hf : (∃ F : (Fin 2 → Fin 2 → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F ∧
        ∀ g, f g = F (fun i j => (g : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧ HasCompactSupport f)
      (c : ℝˣ) (hc : 0 < (c : ℝ))
      (hmatch : ∃ V ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
        ∀ δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ), IsRegularSemisimple (normString ℝ ℂ ℝ Complex.conjAe δ) →
        ∀ γ ∈ V, IsRegularSemisimple γ →
        ∀ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ), IsNormConjugator ℝ ℂ ℝ Complex.conjAe γ δ y →
        ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℝ))) (centralizerBorel ℝ γ))
          (τ' : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ)
            (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ)),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ γ) τ →
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) τ' →
          Coupled ℝ ℂ ℝ Complex.conjAe γ δ y τ τ' →
          ∀ I I' : ℂ,
            IsTwistedOrbitalIntegralOn ℝ ℂ ℝ Complex.conjAe μL δ τ'
              (fun z => φ (Matrix.GeneralLinearGroup.map
                (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                  (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom z : GL (Fin 2) ℂ)) I' →
            IsOrbitalIntegralOn ℝ μA γ τ f I → I' = I),
      ∀ δ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ),
        IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y →
        ∀ (τ : @Measure (Subgroup.centralizer
              ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ)))
              (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
          (τ' : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ)
            (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ)),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) τ →
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) τ' →
          Coupled ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y τ τ' →
          ∀ I' : ℂ,
            IsTwistedOrbitalIntegralOn ℝ ℂ ℝ Complex.conjAe μL δ τ'
              (fun z => φ (Matrix.GeneralLinearGroup.map
                (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                  (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom z : GL (Fin 2) ℂ)) I' →
            IsOrbitalIntegralOn ℝ μA (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ f I')
    (hsplitR : ∀
      (hσ : σ ≠ 1) [Algebra K ℝ] (ι : L →ₐ[K] ℝ)
      (μA : @Measure (GL (Fin 2) ℝ) (glBorelOf ℝ))
      (hμA : @Measure.IsHaarMeasure _ _ _ (glBorelOf ℝ) μA)
      (μL : @Measure (GL (Fin 2) (L ⊗[K] ℝ)) (glBorelOf (L ⊗[K] ℝ)))
      (hμL : @Measure.IsHaarMeasure _ _ _ (glBorelOf (L ⊗[K] ℝ)) μL)
      (φ : GL (Fin 2) (L ⊗[K] ℝ) → ℂ)
      (hφ : (∃ Φ : (Fin (Module.finrank K L) → Fin 2 → Fin 2 → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
        ∀ g, φ g = Φ (fun k i j =>
          ((SplitPlace.psiGL ℝ σ ι hprime hσ g k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧
        HasCompactSupport φ)
      (f : GL (Fin 2) ℝ → ℂ)
      (hf : (∃ F : (Fin 2 → Fin 2 → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F ∧
        ∀ g, f g = F (fun i j => (g : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧ HasCompactSupport f)
      (c : ℝˣ)
      (hmatch : ∃ V ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
        ∀ δ : GL (Fin 2) (L ⊗[K] ℝ), IsRegularSemisimple (normString K L ℝ σ δ) →
        ∀ γ ∈ V, IsRegularSemisimple γ →
        ∀ y : GL (Fin 2) (L ⊗[K] ℝ), IsNormConjugator K L ℝ σ γ δ y →
        ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℝ))) (centralizerBorel ℝ γ))
          (τ' : @Measure (twistedCentralizer K L ℝ σ δ) (twistedCentralizerBorel K L ℝ σ δ)),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ γ) τ →
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L ℝ σ δ) τ' →
          Coupled K L ℝ σ γ δ y τ τ' →
          ∀ I I' : ℂ, IsTwistedOrbitalIntegralOn K L ℝ σ μL δ τ' φ I' →
            IsOrbitalIntegralOn ℝ μA γ τ f I → I' = I),
      ∀ δ y : GL (Fin 2) (L ⊗[K] ℝ),
        IsNormConjugator K L ℝ σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y →
        ∀ (τ : @Measure (Subgroup.centralizer
              ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ)))
              (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
          (τ' : @Measure (twistedCentralizer K L ℝ σ δ) (twistedCentralizerBorel K L ℝ σ δ)),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) τ →
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L ℝ σ δ) τ' →
          Coupled K L ℝ σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y τ τ' →
          ∀ I' : ℂ, IsTwistedOrbitalIntegralOn K L ℝ σ μL δ τ' φ I' →
            IsOrbitalIntegralOn ℝ μA (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ f I')
    (hsplitC : ∀
      (hσ : σ ≠ 1) [Algebra K ℂ] (ι : L →ₐ[K] ℂ)
      (μA : @Measure (GL (Fin 2) ℂ) (glBorelOf ℂ))
      (hμA : @Measure.IsHaarMeasure _ _ _ (glBorelOf ℂ) μA)
      (μL : @Measure (GL (Fin 2) (L ⊗[K] ℂ)) (glBorelOf (L ⊗[K] ℂ)))
      (hμL : @Measure.IsHaarMeasure _ _ _ (glBorelOf (L ⊗[K] ℂ)) μL)
      (φ : GL (Fin 2) (L ⊗[K] ℂ) → ℂ)
      (hφ : (∃ Φ : (Fin (Module.finrank K L) → Fin 2 → Fin 2 → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
        ∀ g, φ g = Φ (fun k i j =>
          ((SplitPlace.psiGL ℂ σ ι hprime hσ g k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) i j)) ∧
        HasCompactSupport φ)
      (f : GL (Fin 2) ℂ → ℂ)
      (hf : (∃ F : (Fin 2 → Fin 2 → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F ∧
        ∀ g, f g = F (fun i j => (g : Matrix (Fin 2) (Fin 2) ℂ) i j)) ∧ HasCompactSupport f)
      (c : ℂˣ)
      (hmatch : ∃ V ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
        ∀ δ : GL (Fin 2) (L ⊗[K] ℂ), IsRegularSemisimple (normString K L ℂ σ δ) →
        ∀ γ ∈ V, IsRegularSemisimple γ →
        ∀ y : GL (Fin 2) (L ⊗[K] ℂ), IsNormConjugator K L ℂ σ γ δ y →
        ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℂ))) (centralizerBorel ℂ γ))
          (τ' : @Measure (twistedCentralizer K L ℂ σ δ) (twistedCentralizerBorel K L ℂ σ δ)),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℂ γ) τ →
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L ℂ σ δ) τ' →
          Coupled K L ℂ σ γ δ y τ τ' →
          ∀ I I' : ℂ, IsTwistedOrbitalIntegralOn K L ℂ σ μL δ τ' φ I' →
            IsOrbitalIntegralOn ℂ μA γ τ f I → I' = I),
      ∀ δ y : GL (Fin 2) (L ⊗[K] ℂ),
        IsNormConjugator K L ℂ σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y →
        ∀ (τ : @Measure (Subgroup.centralizer
              ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℂ)))
              (centralizerBorel ℂ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
          (τ' : @Measure (twistedCentralizer K L ℂ σ δ) (twistedCentralizerBorel K L ℂ σ δ)),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℂ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) τ →
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L ℂ σ δ) τ' →
          Coupled K L ℂ σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y τ τ' →
          ∀ I' : ℂ, IsTwistedOrbitalIntegralOn K L ℂ σ μL δ τ' φ I' →
            IsOrbitalIntegralOn ℂ μA (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ f I')
    (hgc : ∀ (c : ℝˣ) (hc : 0 < (c : ℝ))
      (δ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
      (hδ : IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y)
      (τ : @Measure (Subgroup.centralizer
          ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ)))
          (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
      (τ' : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ)
        (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ))
      (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) τ)
      (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) τ')
      (hgram : (letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) := borel _
         letI := centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)
         letI := twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ
         ∃ (n₁ n₂ : ℕ) (e₁ : Fin n₁ → Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ))
           (e₂ : Fin n₂ → Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) (s : ENNReal),
           s ≠ 0 ∧ s ≠ ⊤ ∧
           LinearIndependent ℝ e₁ ∧
             (Submodule.span ℝ (Set.range e₁) : Set (Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ))) =
               Set.range (fun Y : Matrix (Fin 2) (Fin 2) ℝ =>
                 Y.map (fun x : ℝ => ((1 : ℂ) ⊗ₜ[ℝ] x : ℂ ⊗[ℝ] ℝ))) ∧
           LinearIndependent ℝ e₂ ∧
             (Submodule.span ℝ (Set.range e₂) : Set (Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ))) =
               {X | X * (δ : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) =
                 (δ : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) * X.map (sigmaTensor ℝ ℂ ℝ Complex.conjAe)} ∧
           Measure.map (fun t : ↥(Subgroup.centralizer
                 ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ))) =>
               ((t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).map
                 (fun x : ℝ => ((1 : ℂ) ⊗ₜ[ℝ] x : ℂ ⊗[ℝ] ℝ))) τ =
             s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₁ =>
                     Algebra.trace ℝ (ℂ ⊗[ℝ] ℝ) (Matrix.trace (e₁ i * e₁ j))).det|)) •
                   Measure.map (fun a : Fin n₁ → ℝ => ∑ i, a i • e₁ i) volume).withDensity
                 (fun X : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ) =>
                   (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹) ∧
           Measure.map (fun t : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) =>
               ((t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ))) τ' =
             s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
                     Algebra.trace ℝ (ℂ ⊗[ℝ] ℝ) (Matrix.trace (e₂ i * e₂ j))).det|)) •
                   Measure.map (fun a : Fin n₂ → ℝ => ∑ i, a i • e₂ i) volume).withDensity
                 (fun X : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ) =>
                   (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹))),
      ∃ y' : GL (Fin 2) (ℂ ⊗[ℝ] ℝ),
        IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y' ∧
        Coupled ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y' τ τ') :
    ∀ (i : InfinitePlace K) (φ : GL (Fin 2) (L ⊗[K] InfinitePlace.Completion i) → ℂ),
      ((∃ Φ₁ : (Fin 2 → Fin 2 → InfinitePlace.Extension L i → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ₁ ∧ ∀ g, φ g = Φ₁ (CentAsmLocal.epsL K L i g)) ∧ HasCompactSupport φ) →
      ∀ (f : GL (Fin 2) (InfinitePlace.Completion i) → ℂ),
      ((∃ F₁ : (Fin 2 → Fin 2 → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F₁ ∧ ∀ g, f g = F₁ (CentAsmLocal.epsK K i g)) ∧ HasCompactSupport f) →
      (∃ V ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) (unitAt K c i)),
        ∀ δ : GL (Fin 2) (L ⊗[K] InfinitePlace.Completion i), IsRegularSemisimple (normString K L (InfinitePlace.Completion i) σ δ) →
        ∀ γ ∈ V, IsRegularSemisimple γ →
        ∀ y : GL (Fin 2) (L ⊗[K] InfinitePlace.Completion i), IsNormConjugator K L (InfinitePlace.Completion i) σ γ δ y →
        ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfinitePlace.Completion i)))) (centralizerBorel (InfinitePlace.Completion i) γ))
          (τ' : @Measure (twistedCentralizer K L (InfinitePlace.Completion i) σ δ) (twistedCentralizerBorel K L (InfinitePlace.Completion i) σ δ)),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel (InfinitePlace.Completion i) γ) τ →
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (InfinitePlace.Completion i) σ δ) τ' →
          Coupled K L (InfinitePlace.Completion i) σ γ δ y τ τ' →
          ∀ I I' : ℂ, IsTwistedOrbitalIntegralOn K L (InfinitePlace.Completion i) σ (Measure.haar : Measure (GL (Fin 2) (L ⊗[K] InfinitePlace.Completion i))) δ τ' φ I' →
            IsOrbitalIntegralOn (InfinitePlace.Completion i) (Measure.haar : Measure (GL (Fin 2) (InfinitePlace.Completion i))) γ τ f I → I' = I) →
      ∀ δ y : GL (Fin 2) (L ⊗[K] InfinitePlace.Completion i),
        IsNormConjugator K L (InfinitePlace.Completion i) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) (unitAt K c i)) δ y →
        ∀ (τ : @Measure (Subgroup.centralizer
              ({Matrix.GeneralLinearGroup.scalar (Fin 2) (unitAt K c i)} : Set (GL (Fin 2) (InfinitePlace.Completion i))))
              (centralizerBorel (InfinitePlace.Completion i) (Matrix.GeneralLinearGroup.scalar (Fin 2) (unitAt K c i))))
          (τ' : @Measure (twistedCentralizer K L (InfinitePlace.Completion i) σ δ) (twistedCentralizerBorel K L (InfinitePlace.Completion i) σ δ)),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel (InfinitePlace.Completion i) (Matrix.GeneralLinearGroup.scalar (Fin 2) (unitAt K c i))) τ →
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (InfinitePlace.Completion i) σ δ) τ' →
          @Measure.IsInvInvariant _ (twistedCentralizerBorel K L (InfinitePlace.Completion i) σ δ) _ τ' →
          (∃ s : ℝ≥0, s ≠ 0 ∧
            @Measure.map _ _ (centralizerBorel (InfinitePlace.Completion i) (Matrix.GeneralLinearGroup.scalar (Fin 2) (unitAt K c i))) _
                (fun t : Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) (unitAt K c i)} : Set (GL (Fin 2) (InfinitePlace.Completion i))) => AutomorphicForm.CasmGram.κ K L i (t : GL (Fin 2) (InfinitePlace.Completion i))) τ =
              s • AutomorphicForm.CasmGram.m K L i ∧
            @Measure.map _ _ (twistedCentralizerBorel K L (InfinitePlace.Completion i) σ δ) _
                (fun t : twistedCentralizer K L (InfinitePlace.Completion i) σ δ => AutomorphicForm.CasmGram.κ' K L i (t : GL (Fin 2) (L ⊗[K] InfinitePlace.Completion i))) τ' =
              s • AutomorphicForm.CasmGram.m' K L σ c i δ) →
          ∀ I I' : ℂ, IsTwistedOrbitalIntegralOn K L (InfinitePlace.Completion i) σ (Measure.haar : Measure (GL (Fin 2) (L ⊗[K] InfinitePlace.Completion i))) δ τ' φ I' →
            IsOrbitalIntegralOn (InfinitePlace.Completion i) (Measure.haar : Measure (GL (Fin 2) (InfinitePlace.Completion i))) (Matrix.GeneralLinearGroup.scalar (Fin 2) (unitAt K c i)) τ f I → I' = AutomorphicForm.CasmGram.lam K L σ δg i * I := by
  intro i φ hφ f hf hmatch δ y hN τ τ' hτ hτ' hτ'i hREL I I' hI' hI
  classical
  obtain ⟨s, hs0, hRK, hRL⟩ := hREL
  have hG := gram_of_rel K L σ c i δ y hN τ τ' s hs0 hRK hRL
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  haveI : Algebra.IsSeparable K L := Algebra.IsSeparable.of_integral K L
  haveI : Algebra.IsQuadraticExtension K L := { finrank_eq_two' := h2 }
  haveI : IsGalois K L := Algebra.IsQuadraticExtension.isGalois K L
  have hσ : σ ≠ 1 := sigma_ne_one' K L hprime σ hgen
  by_cases hr : ∃ w : InfinitePlace L, w.comap (algebraMap K L) = i ∧ w.IsRamified K
  · obtain ⟨w, hwi, hw⟩ := hr
    subst hwi
    obtain ⟨e, E, he, he', hE, hE', hEσ, hEι, h7, h8⟩ :=
      AutomorphicForm.exists_ringEquiv_tensor_completion_complex_of_isRamified K L h2 σ hσ w hw
    have hrank : Module.finrank K L = Module.finrank ℝ ℂ := by rw [h2, Complex.finrank_real_complex]

    have hEr : ∀ (r : ℝ) (z : L ⊗[K] (w.comap (algebraMap K L)).Completion), E (r • z) = r • E z := by
      obtain ⟨hwc, hv⟩ := isRamified_iff.1 hw

      have hea : ∀ r : ℝ, e (algebraMap ℝ (InfiniteAdeleRing K) r (w.comap (algebraMap K L))) = r := by
        intro r
        have h1 := congrArg (fun z : mixedEmbedding.mixedSpace K => z.1 ⟨w.comap (algebraMap K L), hv⟩)
          ((InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply (algebraMap ℝ (mixedEmbedding.mixedSpace K) r))
        simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply, Prod.algebraMap_apply, Pi.algebraMap_apply,
          Algebra.algebraMap_self, RingHom.id_apply] at h1

        have h2 : (Completion.ringEquivRealOfIsReal hv) (algebraMap ℝ (InfiniteAdeleRing K) r (w.comap (algebraMap K L))) = r := h1
        have huniq : e.toRingHom.comp (Completion.ringEquivRealOfIsReal hv).symm.toRingHom = RingHom.id ℝ :=
          Subsingleton.elim _ _
        have h3 := congrArg (fun f : ℝ →+* ℝ =>
          f ((Completion.ringEquivRealOfIsReal hv) (algebraMap ℝ (InfiniteAdeleRing K) r (w.comap (algebraMap K L))))) huniq
        simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply, RingEquiv.toRingHom_eq_coe,
          RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply] at h3
        exact h3.trans h2
      have hE1 : ∀ a : (w.comap (algebraMap K L)).Completion, E ((1 : L) ⊗ₜ[K] a) = ((e a : ℝ) : ℂ) ⊗ₜ[ℝ] (1 : ℝ) := by
        intro a
        have h := h7 1 a
        rw [map_one, one_mul] at h
        apply (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
          (Algebra.TensorProduct.rid ℝ ℝ ℂ)).injective
        rw [h]
        erw [Algebra.TensorProduct.rid_tmul]
        rw [one_smul]
      intro r z
      have h2 : r • E z = algebraMap ℝ (ℂ ⊗[ℝ] ℝ) r * E z := Algebra.smul_def r (E z)
      rw [Algebra.smul_def, map_mul, h2]
      congr 1
      change E ((1 : L) ⊗ₜ[K] (algebraMap ℝ (InfiniteAdeleRing K) r (w.comap (algebraMap K L)))) = _
      rw [hE1, hea]
      change ((r : ℝ) : ℂ) ⊗ₜ[ℝ] (1 : ℝ) = (1 : ℂ) ⊗ₜ[ℝ] r
      have hr1 : ((r : ℝ) : ℂ) = r • (1 : ℂ) := by rw [Complex.real_smul, mul_one]
      rw [hr1, TensorProduct.smul_tmul, smul_eq_mul, mul_one]
    have hkind : ∀ (c₀ : ℝˣ) (δ₀ y₀ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)),
        IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c₀) δ₀ y₀ →
        ((∃ z : (ℂ ⊗[ℝ] ℝ)ˣ, IsSigmaConjugate ℝ ℂ ℝ Complex.conjAe δ₀ (Matrix.GeneralLinearGroup.scalar (Fin 2) z)) ↔
          0 < (c₀ : ℝ)) :=
      fun c₀ δ₀ y₀ h₀ => AutomorphicForm.exists_isSigmaConjugate_scalar_conjAe_iff_pos_of_isNormConjugator_scalar c₀ δ₀ y₀ h₀
    have hD := CentAsmLocal.dram K L h2 σ hσ w hw e E he he' hE hE' hEσ hEι h7 h8 hEr hkind hram
      Measure.haar inferInstance Measure.haar inferInstance (unitAt K c (w.comap (algebraMap K L))) φ hφ f hf hmatch
      δ y hN τ τ' hτ hτ' hτ'i hG I I' hI' hI

    have hkT : ∀ (δ₁ y₁ : GL (Fin 2) (L ⊗[K] (w.comap (algebraMap K L)).Completion)),
        IsNormConjugator K L (w.comap (algebraMap K L)).Completion σ
          (Matrix.GeneralLinearGroup.scalar (Fin 2) (unitAt K c (w.comap (algebraMap K L)))) δ₁ y₁ →
        ((∃ z : (L ⊗[K] (w.comap (algebraMap K L)).Completion)ˣ,
            IsSigmaConjugate K L (w.comap (algebraMap K L)).Completion σ δ₁ (Matrix.GeneralLinearGroup.scalar (Fin 2) z)) ↔
          0 < ((Units.map (e : (w.comap (algebraMap K L)).Completion →* ℝ) (unitAt K c (w.comap (algebraMap K L))) : ℝˣ) : ℝ)) := by
      intro δ₁ y₁ h₁
      have hEσ' : ∀ z, E.symm (sigmaTensor ℝ ℂ ℝ Complex.conjAe z) =
          sigmaTensor K L (w.comap (algebraMap K L)).Completion σ (E.symm z) := CentAsmLocal.symm_sigmaTensor σ Complex.conjAe E hEσ
      have hT : (∃ z : (L ⊗[K] (w.comap (algebraMap K L)).Completion)ˣ,
            IsSigmaConjugate K L (w.comap (algebraMap K L)).Completion σ δ₁ (Matrix.GeneralLinearGroup.scalar (Fin 2) z)) ↔
          (∃ z' : (ℂ ⊗[ℝ] ℝ)ˣ, IsSigmaConjugate ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.map E.toRingHom δ₁)
            (Matrix.GeneralLinearGroup.scalar (Fin 2) z')) := by
        constructor
        · rintro ⟨z, x, hx⟩
          refine ⟨Units.map (E : L ⊗[K] (w.comap (algebraMap K L)).Completion →* ℂ ⊗[ℝ] ℝ) z,
            Matrix.GeneralLinearGroup.map E.toRingHom x, ?_⟩
          rw [← CentAsmLocal.map_scalar E z, hx, map_mul, map_mul, map_inv, CentAsmLocal.map_sigmaGL σ Complex.conjAe E hEσ]
        · rintro ⟨z', x', hx'⟩
          refine ⟨Units.map (E.symm : ℂ ⊗[ℝ] ℝ →* L ⊗[K] (w.comap (algebraMap K L)).Completion) z',
            Matrix.GeneralLinearGroup.map E.symm.toRingHom x', ?_⟩
          have h := congrArg (Matrix.GeneralLinearGroup.map E.symm.toRingHom) hx'
          rw [map_mul, map_mul, map_inv, CentAsmLocal.map_symm_map, CentAsmLocal.map_sigmaGL Complex.conjAe σ E.symm hEσ',
            CentAsmLocal.map_scalar] at h
          exact h
      obtain ⟨hNiff, -⟩ :=
        AutomorphicForm.isNormConjugator_map_iff_and_coupled_map_iff_of_ringEquiv (σ := σ) (σ' := Complex.conjAe) hrank
          e he he' E hE hE' hEσ hEι (Matrix.GeneralLinearGroup.scalar (Fin 2) (unitAt K c (w.comap (algebraMap K L)))) δ₁ y₁
      rw [CentAsmLocal.map_scalar] at hNiff
      exact hT.trans (hkind _ _ _ (hNiff.1 h₁))
    have hNg := isNormConjugator_eval K L σ c δg yg hδg (w.comap (algebraMap K L))
    by_cases hq : ∃ z : (L ⊗[K] (w.comap (algebraMap K L)).Completion)ˣ,
        IsSigmaConjugate K L (w.comap (algebraMap K L)).Completion σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z)
    · have hlam : lam K L σ δg (w.comap (algebraMap K L)) = 1 :=
        lam_eq_one_of_exists K L σ δg _ ((hkT _ _ hNg).2 ((hkT δ y hN).1 hq))
      rw [hlam, one_mul]
      exact hD.1 hq
    · have hlam : lam K L σ δg (w.comap (algebraMap K L)) = -1 :=
        lam_eq_neg_one_of_forall K L σ δg _
          (not_exists.mp fun h => hq ((hkT δ y hN).2 ((hkT _ _ hNg).1 h)))
      rw [hlam, neg_one_mul]
      exact hD.2 hq
  · have hsplit : ∀ w : InfinitePlace L, w.comap (algebraMap K L) = i → ¬ w.IsRamified K :=
      fun w hw hr' => hr ⟨w, hw, hr'⟩
    obtain ⟨y'', hN'', hC''⟩ : ∃ y'' : GL (Fin 2) (L ⊗[K] i.Completion),
        IsNormConjugator K L i.Completion σ (Matrix.GeneralLinearGroup.scalar (Fin 2) (unitAt K c i)) δ y'' ∧
        Coupled K L i.Completion σ (Matrix.GeneralLinearGroup.scalar (Fin 2) (unitAt K c i)) δ y'' τ τ' := by
      rcases i.isReal_or_isComplex with hv | hv
      · exact coupled_of_gram_real K L hprime σ hσ i hv hsplit (unitAt K c i) δ y hN τ τ' hτ hτ' hG
      · exact coupled_of_gram_complex K L hprime σ hσ i hv hsplit (unitAt K c i) δ y hN τ τ' hτ hτ' hG
    have h1 := CentAsmLocal.heng_split K L hprime σ hσ i hsplit hsplitR hsplitC
      Measure.haar inferInstance Measure.haar inferInstance (unitAt K c i) φ hφ f hf hmatch δ y'' hN'' τ τ' hτ hτ' hτ'i hC''
      I I' hI' hI
    have hlam : lam K L σ δg i = 1 := by
      apply lam_eq_one_of_exists
      obtain ⟨w, hw⟩ : ∃ w : InfinitePlace L, w.comap (algebraMap K L) = i := NumberField.InfinitePlace.comap_surjective i
      have hun : w.IsUnramified K := by simpa [NumberField.InfinitePlace.IsRamified] using hsplit w hw
      obtain ⟨ι₀⟩ := NumberField.InfinitePlace.nonempty_algHom_completion_of_isUnramified K L i w hw hun
      exact AutomorphicForm.exists_isSigmaConjugate_scalar_of_isNormConjugator_scalar_of_algHom_of_prime K L hprime σ hσ
        i.Completion ι₀ (unitAt K c i) _ _ (isNormConjugator_eval K L σ c δg yg hδg i)
    rw [hlam, one_mul]
    exact h1

set_option maxHeartbeats 16000000 in

theorem hsecL_rel
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (c : (InfiniteAdeleRing K)ˣ) :
    ∀ (i : InfinitePlace K) (δ : GL (Fin 2) (L ⊗[K] InfinitePlace.Completion i)),
      ∀ τ' : @Measure (twistedCentralizer K L (InfinitePlace.Completion i) σ δ) (twistedCentralizerBorel K L (InfinitePlace.Completion i) σ δ),
        @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (InfinitePlace.Completion i) σ δ) τ' →
        @Measure.IsInvInvariant _ (twistedCentralizerBorel K L (InfinitePlace.Completion i) σ δ) _ τ' →
      (IsRegularSemisimple (normString K L (InfinitePlace.Completion i) σ δ) ∨
        ∃ (τ : @Measure (Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) (unitAt K c i)} : Set (GL (Fin 2) (InfinitePlace.Completion i))))
              (centralizerBorel (InfinitePlace.Completion i) (Matrix.GeneralLinearGroup.scalar (Fin 2) (unitAt K c i)))),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel (InfinitePlace.Completion i) (Matrix.GeneralLinearGroup.scalar (Fin 2) (unitAt K c i))) τ ∧
          (∃ s : ℝ≥0, s ≠ 0 ∧
            @Measure.map _ _ (centralizerBorel (InfinitePlace.Completion i) (Matrix.GeneralLinearGroup.scalar (Fin 2) (unitAt K c i))) _
                (fun t : Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) (unitAt K c i)} : Set (GL (Fin 2) (InfinitePlace.Completion i))) => AutomorphicForm.CasmGram.κ K L i (t : GL (Fin 2) (InfinitePlace.Completion i))) τ =
              s • AutomorphicForm.CasmGram.m K L i ∧
            @Measure.map _ _ (twistedCentralizerBorel K L (InfinitePlace.Completion i) σ δ) _
                (fun t : twistedCentralizer K L (InfinitePlace.Completion i) σ δ => AutomorphicForm.CasmGram.κ' K L i (t : GL (Fin 2) (L ⊗[K] InfinitePlace.Completion i))) τ' =
              s • AutomorphicForm.CasmGram.m' K L σ c i δ)) →
      ∀ φ : GL (Fin 2) (L ⊗[K] InfinitePlace.Completion i) → ℂ, Continuous φ → HasCompactSupport φ →
        ∃ W : GL (Fin 2) (L ⊗[K] InfinitePlace.Completion i) → ℝ, IsTwistedSectionFnOn K L (InfinitePlace.Completion i) σ δ τ' φ W ∧ Continuous W := by
  intro i δ τ' hτ' hτ'i hcase φ hφ hφc
  classical
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  haveI : Algebra.IsSeparable K L := Algebra.IsSeparable.of_integral K L
  haveI : Algebra.IsQuadraticExtension K L := { finrank_eq_two' := h2 }
  haveI : IsGalois K L := Algebra.IsQuadraticExtension.isGalois K L
  have hprime : (Module.finrank K L).Prime := by rw [h2]; exact Nat.prime_two
  rcases hcase with hreg | ⟨τ, hτ, s, hs0, hRK, hRL⟩
  · exact CentAsmLocal.hsecL K L hprime σ hgen i δ (Or.inl hreg) τ' hτ' hτ'i φ hφ hφc
  · by_cases hc : ∃ y : GL (Fin 2) (L ⊗[K] i.Completion),
        IsNormConjugator K L i.Completion σ (Matrix.GeneralLinearGroup.scalar (Fin 2) (unitAt K c i)) δ y
    · obtain ⟨y, hN⟩ := hc
      by_cases hq : ∃ d : (L ⊗[K] i.Completion)ˣ,
          IsSigmaConjugate K L i.Completion σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) d)
      · exact CentAsmLocal.hsecL K L hprime σ hgen i δ (Or.inr hq) τ' hτ' hτ'i φ hφ hφc
      · exact AutomorphicForm.exists_isTwistedSectionFnOn_and_continuous_completion_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
          K L h2 σ hgen i (unitAt K c i) δ y hN (not_exists.mp hq) τ' hτ' φ hφ hφc
    · exfalso
      rw [m', if_neg hc, smul_zero] at hRL
      letI := twistedCentralizerBorel K L i.Completion σ δ
      haveI : BorelSpace (twistedCentralizer K L i.Completion σ δ) := ⟨rfl⟩
      haveI := isTopologicalRing_tensor K L i.Completion
      haveI := isTopologicalGroup_tensorGL K L i.Completion
      have hmeas : Measurable (fun t : twistedCentralizer K L i.Completion σ δ =>
          AutomorphicForm.CasmGram.κ' K L i (t : GL (Fin 2) (L ⊗[K] i.Completion))) :=
        (Units.continuous_val.comp continuous_subtype_val).measurable
      have hzero : τ' = 0 := (Measure.map_eq_zero_iff hmeas.aemeasurable).1 hRL
      haveI := hτ'
      have hpos := (hτ'.toIsOpenPosMeasure).open_pos Set.univ isOpen_univ Set.univ_nonempty
      rw [hzero] at hpos
      exact hpos (by simp only [Measure.coe_zero, Pi.zero_apply])

end AutomorphicForm.CasmGram
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.FDTEF P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CasmGram P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.P2mGramSide"
p2m_reactivate "P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CentAsmLocal P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.FDTEF P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.AutomorphicForm.CasmGram P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.P2mGramSide"

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (γ : GL (Fin 2) (InfiniteAdeleRing K))
    (hγ : ∃ c : (InfiniteAdeleRing K)ˣ, γ = Matrix.GeneralLinearGroup.scalar (Fin 2) c)
    (δ y : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
    (hδ : AutomorphicForm.IsNormConjugator K L (InfiniteAdeleRing K) σ γ δ y)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))))
      (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) γ) τ)
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ) τ')
    (hnorm :
      letI : Algebra ℝ (InfiniteAdeleRing K) :=
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
          (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
      letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
        ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
          (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
      letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := borel _
      letI := AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) γ
      letI := AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ
      ∃ (n₁ n₂ : ℕ) (e₁ : Fin n₁ → Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
        (e₂ : Fin n₂ → Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (s : ENNReal),
        s ≠ 0 ∧ s ≠ ⊤ ∧
        LinearIndependent ℝ e₁ ∧
          (Submodule.span ℝ (Set.range e₁) : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) =
            Set.range (fun Y : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K) =>
              Y.map (Algebra.TensorProduct.includeRight :
                InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K)) ∧
        LinearIndependent ℝ e₂ ∧
          (Submodule.span ℝ (Set.range e₂) : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) =
            {X | X * (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) =
              (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) *
                X.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ)} ∧
        Measure.map (fun t : ↥(Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K)))) =>
            ((t : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)).map
              (Algebra.TensorProduct.includeRight :
                InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K)) τ =
          s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₁ =>
                  Algebra.trace ℝ (L ⊗[K] InfiniteAdeleRing K) (Matrix.trace (e₁ i * e₁ j))).det|)) •
                Measure.map (fun c : Fin n₁ → ℝ => ∑ i, c i • e₁ i) volume).withDensity
              (fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
                (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹) ∧
        Measure.map (fun t : ↥(AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ) =>
            ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) τ' =
          s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
                  Algebra.trace ℝ (L ⊗[K] InfiniteAdeleRing K) (Matrix.trace (e₂ i * e₂ j))).det|)) •
                Measure.map (fun c : Fin n₂ → ℝ => ∑ i, c i • e₂ i) volume).withDensity
              (fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
                (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹))
    (hprime : (Module.finrank K L).Prime)
    (hram : ∀
      (μA : @Measure (GL (Fin 2) ℝ) (glBorelOf ℝ))
      (μL : @Measure (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) (glBorelOf (ℂ ⊗[ℝ] ℝ)))
      (hμA : @Measure.IsHaarMeasure _ _ _ (glBorelOf ℝ) μA)
      (hμL : @Measure.IsHaarMeasure _ _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) μL)
      (φ : GL (Fin 2) ℂ → ℂ)
      (hφ : (∃ Φ : (Fin 2 → Fin 2 → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
        ∀ g, φ g = Φ (fun i j => (g : Matrix (Fin 2) (Fin 2) ℂ) i j)) ∧ HasCompactSupport φ)
      (f : GL (Fin 2) ℝ → ℂ)
      (hf : (∃ F : (Fin 2 → Fin 2 → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F ∧
        ∀ g, f g = F (fun i j => (g : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧ HasCompactSupport f)
      (c : ℝˣ) (hc : 0 < (c : ℝ))
      (hmatch : ∃ V ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
        ∀ δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ), IsRegularSemisimple (normString ℝ ℂ ℝ Complex.conjAe δ) →
        ∀ γ ∈ V, IsRegularSemisimple γ →
        ∀ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ), IsNormConjugator ℝ ℂ ℝ Complex.conjAe γ δ y →
        ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℝ))) (centralizerBorel ℝ γ))
          (τ' : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ)
            (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ)),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ γ) τ →
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) τ' →
          Coupled ℝ ℂ ℝ Complex.conjAe γ δ y τ τ' →
          ∀ I I' : ℂ,
            IsTwistedOrbitalIntegralOn ℝ ℂ ℝ Complex.conjAe μL δ τ'
              (fun z => φ (Matrix.GeneralLinearGroup.map
                (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                  (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom z : GL (Fin 2) ℂ)) I' →
            IsOrbitalIntegralOn ℝ μA γ τ f I → I' = I),
      ∀ δ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ),
        IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y →
        ∀ (τ : @Measure (Subgroup.centralizer
              ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ)))
              (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
          (τ' : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ)
            (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ)),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) τ →
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) τ' →
          Coupled ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y τ τ' →
          ∀ I' : ℂ,
            IsTwistedOrbitalIntegralOn ℝ ℂ ℝ Complex.conjAe μL δ τ'
              (fun z => φ (Matrix.GeneralLinearGroup.map
                (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                  (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom z : GL (Fin 2) ℂ)) I' →
            IsOrbitalIntegralOn ℝ μA (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ f I')
    (hramNeg : ∀ (μA : @Measure (GL (Fin 2) ℝ) (glBorelOf ℝ))
      (μL : @Measure (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) (glBorelOf (ℂ ⊗[ℝ] ℝ)))
      (hμA : @Measure.IsHaarMeasure _ _ _ (glBorelOf ℝ) μA)
      (hμL : @Measure.IsHaarMeasure _ _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) μL)
      (φ : GL (Fin 2) ℂ → ℂ)
      (hφ : (∃ Φ : (Fin 2 → Fin 2 → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
        ∀ g, φ g = Φ (fun i j => (g : Matrix (Fin 2) (Fin 2) ℂ) i j)) ∧ HasCompactSupport φ)
      (f : GL (Fin 2) ℝ → ℂ)
      (hf : (∃ F : (Fin 2 → Fin 2 → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F ∧
        ∀ g, f g = F (fun i j => (g : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧ HasCompactSupport f)
      (c : ℝˣ) (hc : (c : ℝ) < 0)
      (hmatch : ∃ V ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
        (∀ δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ), IsRegularSemisimple (normString ℝ ℂ ℝ Complex.conjAe δ) →
        ∀ γ ∈ V, IsRegularSemisimple γ →
        ∀ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ), IsNormConjugator ℝ ℂ ℝ Complex.conjAe γ δ y →
        ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℝ))) (centralizerBorel ℝ γ))
          (τ' : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ)
            (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ)),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ γ) τ →
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) τ' →
          Coupled ℝ ℂ ℝ Complex.conjAe γ δ y τ τ' →
          ∀ I I' : ℂ,
            IsTwistedOrbitalIntegralOn ℝ ℂ ℝ Complex.conjAe μL δ τ'
              (fun z => φ (Matrix.GeneralLinearGroup.map
                (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                  (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom z : GL (Fin 2) ℂ)) I' →
            IsOrbitalIntegralOn ℝ μA γ τ f I → I' = I) ∧
        (∀ γ ∈ V, IsRegularSemisimple γ →
          (¬ ∃ δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ), IsNormOf ℝ ℂ ℝ Complex.conjAe γ δ) →
          ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℝ))) (centralizerBorel ℝ γ)),
            @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ γ) τ →
            ∀ I : ℂ, IsOrbitalIntegralOn ℝ μA γ τ f I → I = 0)),
      ∀ δ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ),
        IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y →
        ∀ (τ : @Measure (Subgroup.centralizer
              ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ)))
              (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
          (τ' : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ)
            (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ)),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) τ →
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) τ' →
          (letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) := borel _
           letI := centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)
           letI := twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ
           ∃ (n₁ n₂ : ℕ) (e₁ : Fin n₁ → Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ))
             (e₂ : Fin n₂ → Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) (s : ENNReal),
             s ≠ 0 ∧ s ≠ ⊤ ∧
             LinearIndependent ℝ e₁ ∧
               (Submodule.span ℝ (Set.range e₁) : Set (Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ))) =
                 Set.range (fun Y : Matrix (Fin 2) (Fin 2) ℝ =>
                   Y.map (fun x : ℝ => ((1 : ℂ) ⊗ₜ[ℝ] x : ℂ ⊗[ℝ] ℝ))) ∧
             LinearIndependent ℝ e₂ ∧
               (Submodule.span ℝ (Set.range e₂) : Set (Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ))) =
                 {X | X * (δ : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) =
                   (δ : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) * X.map (sigmaTensor ℝ ℂ ℝ Complex.conjAe)} ∧
             Measure.map (fun t : ↥(Subgroup.centralizer
                   ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ))) =>
                 ((t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).map
                   (fun x : ℝ => ((1 : ℂ) ⊗ₜ[ℝ] x : ℂ ⊗[ℝ] ℝ))) τ =
               s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₁ =>
                       Algebra.trace ℝ (ℂ ⊗[ℝ] ℝ) (Matrix.trace (e₁ i * e₁ j))).det|)) •
                     Measure.map (fun a : Fin n₁ → ℝ => ∑ i, a i • e₁ i) volume).withDensity
                   (fun X : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ) =>
                     (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹) ∧
             Measure.map (fun t : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) =>
                 ((t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ))) τ' =
               s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
                       Algebra.trace ℝ (ℂ ⊗[ℝ] ℝ) (Matrix.trace (e₂ i * e₂ j))).det|)) •
                     Measure.map (fun a : Fin n₂ → ℝ => ∑ i, a i • e₂ i) volume).withDensity
                   (fun X : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ) =>
                     (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹)) →
          ∀ I' : ℂ,
            IsTwistedOrbitalIntegralOn ℝ ℂ ℝ Complex.conjAe μL δ τ'
              (fun z => φ (Matrix.GeneralLinearGroup.map
                (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                  (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom z : GL (Fin 2) ℂ)) I' →
            IsOrbitalIntegralOn ℝ μA (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ f (-I'))
    (hsplitR : ∀
      (hσ : σ ≠ 1) [Algebra K ℝ] (ι : L →ₐ[K] ℝ)
      (μA : @Measure (GL (Fin 2) ℝ) (glBorelOf ℝ))
      (hμA : @Measure.IsHaarMeasure _ _ _ (glBorelOf ℝ) μA)
      (μL : @Measure (GL (Fin 2) (L ⊗[K] ℝ)) (glBorelOf (L ⊗[K] ℝ)))
      (hμL : @Measure.IsHaarMeasure _ _ _ (glBorelOf (L ⊗[K] ℝ)) μL)
      (φ : GL (Fin 2) (L ⊗[K] ℝ) → ℂ)
      (hφ : (∃ Φ : (Fin (Module.finrank K L) → Fin 2 → Fin 2 → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
        ∀ g, φ g = Φ (fun k i j =>
          ((SplitPlace.psiGL ℝ σ ι hprime hσ g k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧
        HasCompactSupport φ)
      (f : GL (Fin 2) ℝ → ℂ)
      (hf : (∃ F : (Fin 2 → Fin 2 → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F ∧
        ∀ g, f g = F (fun i j => (g : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧ HasCompactSupport f)
      (c : ℝˣ)
      (hmatch : ∃ V ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
        ∀ δ : GL (Fin 2) (L ⊗[K] ℝ), IsRegularSemisimple (normString K L ℝ σ δ) →
        ∀ γ ∈ V, IsRegularSemisimple γ →
        ∀ y : GL (Fin 2) (L ⊗[K] ℝ), IsNormConjugator K L ℝ σ γ δ y →
        ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℝ))) (centralizerBorel ℝ γ))
          (τ' : @Measure (twistedCentralizer K L ℝ σ δ) (twistedCentralizerBorel K L ℝ σ δ)),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ γ) τ →
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L ℝ σ δ) τ' →
          Coupled K L ℝ σ γ δ y τ τ' →
          ∀ I I' : ℂ, IsTwistedOrbitalIntegralOn K L ℝ σ μL δ τ' φ I' →
            IsOrbitalIntegralOn ℝ μA γ τ f I → I' = I),
      ∀ δ y : GL (Fin 2) (L ⊗[K] ℝ),
        IsNormConjugator K L ℝ σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y →
        ∀ (τ : @Measure (Subgroup.centralizer
              ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ)))
              (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
          (τ' : @Measure (twistedCentralizer K L ℝ σ δ) (twistedCentralizerBorel K L ℝ σ δ)),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) τ →
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L ℝ σ δ) τ' →
          Coupled K L ℝ σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y τ τ' →
          ∀ I' : ℂ, IsTwistedOrbitalIntegralOn K L ℝ σ μL δ τ' φ I' →
            IsOrbitalIntegralOn ℝ μA (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ f I')
    (hsplitC : ∀
      (hσ : σ ≠ 1) [Algebra K ℂ] (ι : L →ₐ[K] ℂ)
      (μA : @Measure (GL (Fin 2) ℂ) (glBorelOf ℂ))
      (hμA : @Measure.IsHaarMeasure _ _ _ (glBorelOf ℂ) μA)
      (μL : @Measure (GL (Fin 2) (L ⊗[K] ℂ)) (glBorelOf (L ⊗[K] ℂ)))
      (hμL : @Measure.IsHaarMeasure _ _ _ (glBorelOf (L ⊗[K] ℂ)) μL)
      (φ : GL (Fin 2) (L ⊗[K] ℂ) → ℂ)
      (hφ : (∃ Φ : (Fin (Module.finrank K L) → Fin 2 → Fin 2 → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
        ∀ g, φ g = Φ (fun k i j =>
          ((SplitPlace.psiGL ℂ σ ι hprime hσ g k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) i j)) ∧
        HasCompactSupport φ)
      (f : GL (Fin 2) ℂ → ℂ)
      (hf : (∃ F : (Fin 2 → Fin 2 → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F ∧
        ∀ g, f g = F (fun i j => (g : Matrix (Fin 2) (Fin 2) ℂ) i j)) ∧ HasCompactSupport f)
      (c : ℂˣ)
      (hmatch : ∃ V ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
        ∀ δ : GL (Fin 2) (L ⊗[K] ℂ), IsRegularSemisimple (normString K L ℂ σ δ) →
        ∀ γ ∈ V, IsRegularSemisimple γ →
        ∀ y : GL (Fin 2) (L ⊗[K] ℂ), IsNormConjugator K L ℂ σ γ δ y →
        ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℂ))) (centralizerBorel ℂ γ))
          (τ' : @Measure (twistedCentralizer K L ℂ σ δ) (twistedCentralizerBorel K L ℂ σ δ)),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℂ γ) τ →
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L ℂ σ δ) τ' →
          Coupled K L ℂ σ γ δ y τ τ' →
          ∀ I I' : ℂ, IsTwistedOrbitalIntegralOn K L ℂ σ μL δ τ' φ I' →
            IsOrbitalIntegralOn ℂ μA γ τ f I → I' = I),
      ∀ δ y : GL (Fin 2) (L ⊗[K] ℂ),
        IsNormConjugator K L ℂ σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y →
        ∀ (τ : @Measure (Subgroup.centralizer
              ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℂ)))
              (centralizerBorel ℂ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
          (τ' : @Measure (twistedCentralizer K L ℂ σ δ) (twistedCentralizerBorel K L ℂ σ δ)),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℂ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) τ →
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L ℂ σ δ) τ' →
          Coupled K L ℂ σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y τ τ' →
          ∀ I' : ℂ, IsTwistedOrbitalIntegralOn K L ℂ σ μL δ τ' φ I' →
            IsOrbitalIntegralOn ℂ μA (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ f I')
    (hgc : ∀ (c : ℝˣ) (hc : 0 < (c : ℝ))
      (δ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
      (hδ : IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y)
      (τ : @Measure (Subgroup.centralizer
          ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ)))
          (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
      (τ' : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ)
        (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ))
      (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) τ)
      (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) τ')
      (hgram : (letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) := borel _
         letI := centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)
         letI := twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ
         ∃ (n₁ n₂ : ℕ) (e₁ : Fin n₁ → Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ))
           (e₂ : Fin n₂ → Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) (s : ENNReal),
           s ≠ 0 ∧ s ≠ ⊤ ∧
           LinearIndependent ℝ e₁ ∧
             (Submodule.span ℝ (Set.range e₁) : Set (Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ))) =
               Set.range (fun Y : Matrix (Fin 2) (Fin 2) ℝ =>
                 Y.map (fun x : ℝ => ((1 : ℂ) ⊗ₜ[ℝ] x : ℂ ⊗[ℝ] ℝ))) ∧
           LinearIndependent ℝ e₂ ∧
             (Submodule.span ℝ (Set.range e₂) : Set (Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ))) =
               {X | X * (δ : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) =
                 (δ : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) * X.map (sigmaTensor ℝ ℂ ℝ Complex.conjAe)} ∧
           Measure.map (fun t : ↥(Subgroup.centralizer
                 ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ))) =>
               ((t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).map
                 (fun x : ℝ => ((1 : ℂ) ⊗ₜ[ℝ] x : ℂ ⊗[ℝ] ℝ))) τ =
             s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₁ =>
                     Algebra.trace ℝ (ℂ ⊗[ℝ] ℝ) (Matrix.trace (e₁ i * e₁ j))).det|)) •
                   Measure.map (fun a : Fin n₁ → ℝ => ∑ i, a i • e₁ i) volume).withDensity
                 (fun X : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ) =>
                   (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹) ∧
           Measure.map (fun t : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) =>
               ((t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ))) τ' =
             s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
                     Algebra.trace ℝ (ℂ ⊗[ℝ] ℝ) (Matrix.trace (e₂ i * e₂ j))).det|)) •
                   Measure.map (fun a : Fin n₂ → ℝ => ∑ i, a i • e₂ i) volume).withDensity
                 (fun X : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ) =>
                   (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹))),
      ∃ y' : GL (Fin 2) (ℂ ⊗[ℝ] ℝ),
        IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y' ∧
        Coupled ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y' τ τ') :
    ∀ (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ), AutomorphicForm.IsArchTestFactor L φa →
      ∀ (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ), AutomorphicForm.IsArchTestFactor K fa →
        AutomorphicForm.AreMatchingArch K L σ φa fa →
        ∀ I I' : ℂ,
          AutomorphicForm.IsTwistedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ (AutomorphicForm.archHaarL K L) δ τ'
            (φa ∘ AutomorphicForm.archIdentGL K L) I' →
          AutomorphicForm.IsOrbitalIntegralOn (InfiniteAdeleRing K) (AutomorphicForm.archHaarK K) γ τ fa I →
          I' = (-1 : ℂ) ^ (Nat.card {w : NumberField.InfinitePlace K //
            ∀ z : (L ⊗[K] w.Completion)ˣ,
              ¬ AutomorphicForm.IsSigmaConjugate K L w.Completion σ
                  (Matrix.GeneralLinearGroup.map
                    (Algebra.TensorProduct.map (AlgHom.id K L)
                      (Pi.evalAlgHom K (fun w : NumberField.InfinitePlace K => w.Completion) w)).toRingHom δ)
                  (Matrix.GeneralLinearGroup.scalar (Fin 2) z)}) * I := by
  intro φa hφa fa hfa hmatch I I' hI' hI
  obtain ⟨c, rfl⟩ := hγ

  have dock := FDTEF.rel_central_transfer_of_heng K L σ φa hφa fa hfa hmatch c

  have dock2 := dock (AutomorphicForm.CasmGram.V K L) (AutomorphicForm.CasmGram.κ K L)
    (AutomorphicForm.CasmGram.measurable_κ K L) (AutomorphicForm.CasmGram.injective_κ K L)
    (AutomorphicForm.CasmGram.κ' K L) (AutomorphicForm.CasmGram.measurable_κ' K L) (AutomorphicForm.CasmGram.injective_κ' K L)
    (AutomorphicForm.CasmGram.m K L) (AutomorphicForm.CasmGram.sigmaFinite_m K L)
    (AutomorphicForm.CasmGram.m' K L σ c) (AutomorphicForm.CasmGram.sigmaFinite_m' K L σ c)
    (AutomorphicForm.CasmGram.lam K L σ δ)

  have key : I' = (∏ i, AutomorphicForm.CasmGram.lam K L σ δ i) * I :=
    dock2 (AutomorphicForm.CasmGram.hsecL_rel K L h2 σ hgen c) (AutomorphicForm.CasmGram.heng_rel K L h2 σ hgen c δ y hδ hprime hram hsplitR hsplitC hgc) δ y hδ τ τ' hτ hτ' (AutomorphicForm.isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar K L hprime σ hgen c δ y hδ τ' hτ') (AutomorphicForm.CasmGram.hrel_of_hnorm K L σ c δ y hδ τ τ' hnorm) I I' hI' hI

  classical
  rw [Ws46.CASM.prod_sign_eq_neg_one_pow_card
    (P := fun w : NumberField.InfinitePlace K => ∀ z : (L ⊗[K] w.Completion)ˣ,
      ¬ AutomorphicForm.IsSigmaConjugate K L w.Completion σ
          (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.map (AlgHom.id K L)
              (Pi.evalAlgHom K (fun w : NumberField.InfinitePlace K => w.Completion) w)).toRingHom δ)
          (Matrix.GeneralLinearGroup.scalar (Fin 2) z))
    (AutomorphicForm.CasmGram.lam K L σ δ)
    (fun w hw => by simp only [AutomorphicForm.CasmGram.lam]; rw [if_neg (not_exists.mpr hw)])
    (fun w hw => by simp only [AutomorphicForm.CasmGram.lam]; rw [if_pos (not_forall_not.mp hw)])] at key
  exact key

end S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom
end P2MW
export P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom (solution)
