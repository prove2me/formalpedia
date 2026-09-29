-- Prove2me | solution 1 for AutomorphicForm.twistedWeighted_eq_finrank_mul_weighted_heckeWord_of_inertiaDeg_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/48f377cf-2430-5692-859e-c4749ee2917a

import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_LocalWeightedOrbital
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_SplitFibreIntegral
import Definitions.Def_DedekindDomain_IntegralClosure
import Theorems.Thm_AutomorphicForm_eq_of_isWeightedOrbitalIntegral_of_isWeightedOrbitalIntegral_diagonal_of_measure_preimage_localIntegralSet_eq_one
import Theorems.Thm_AutomorphicForm_exists_continuousMulEquiv_centralizer_twistedCentralizer_of_isNormConjugator
import Theorems.Thm_AutomorphicForm_exists_isWeightedOrbitalIntegral_and_integral_pi_mul_prod_indicator_cyclicString_eq_mul_of_forall_mul_eq
import Theorems.Thm_AutomorphicForm_isLocalTestFn_sum_indicator_localIntegralSet_prod_mul_zpow_inv_mul
import Theorems.Thm_AutomorphicForm_SatakeCombination_sum_slotCoeff_mul_sum_indicator_heckeWord_eq_sum_indicator_map_heckeWord_of_inertiaDeg_eq_one
import Theorems.Thm_AutomorphicForm_SplitPlace_continuous_coords_and_coords_sigmaGL_and_coords_normString_and_exists_pos_map_coords_eq_smul_pi
import Theorems.Thm_AutomorphicForm_SplitPlace_exists_ringEquiv_coords_semiLocalComponent_localEmbed_eq_mulSingle
import Theorems.Thm_AutomorphicForm_SplitPlace_mem_semiLocalIntegralSet_iff_coords_and_semiLocalWeight_eq_sum_and_map_coords_semiLocalHaar
import Theorems.Thm_NumberField_nonempty_algHom_adicCompletion_of_nontrivial_extension_of_prime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_twistedWeighted_eq_finrank_mul_weighted_heckeWord_of_inertiaDeg_eq_one
p2m_attr_erase "instance" "IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing"
p2m_attr_erase "simp" "AutomorphicForm.adeleArchAlgHom_apply AutomorphicForm.tensorPlaceHom_tmul AutomorphicForm.tensorArchHom_tmul AutomorphicForm.adelePlaceAlgHom_apply M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.Bridge.finiteConorm_apply M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply"
p2m_attr_erase "simp" "Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply AutomorphicForm.gl2Weyl_val LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11"

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions
open LanglandsTunnell.CubicInduction (diagUnits2)

namespace WSplitGlue

theorem secondCountableTopology_units (M : Type*) [Monoid M] [TopologicalSpace M]
    [SecondCountableTopology M] : SecondCountableTopology Mˣ := by
  haveI : SecondCountableTopology Mᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := M)).symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem indicator_forall_eq_prod {ι X : Type*} [Fintype ι] (S : Set X) (c : ι → X) (P : Prop) [Decidable P]
    (hP : P ↔ ∀ j, c j ∈ S) :
    (if P then (1 : ℂ) else 0) = ∏ j, S.indicator (fun _ => (1 : ℂ)) (c j) := by
  classical
  by_cases h : P
  · rw [if_pos h]
    exact (Finset.prod_eq_one fun j _ => by rw [Set.indicator_of_mem ((hP.1 h) j)]).symm
  · rw [if_neg h]
    obtain ⟨j, hj⟩ := not_forall.1 (mt hP.2 h)
    exact (Finset.prod_eq_zero (Finset.mem_univ j) (by rw [Set.indicator_of_notMem hj])).symm

theorem isRegularSemisimple_diagUnits2 {F : Type*} [Field F] (a b : Fˣ) (hab : a ≠ b) :
    AutomorphicForm.IsRegularSemisimple (diagUnits2 a b) := by
  unfold AutomorphicForm.IsRegularSemisimple
  have htr : ((diagUnits2 a b : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).trace = a + b := by
    simp [diagUnits2, Matrix.trace, Fin.sum_univ_two]
  have hdet : ((diagUnits2 a b : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = a * b := by
    simp [diagUnits2, Matrix.det_fin_two]
  rw [htr, hdet, isUnit_iff_ne_zero]
  have : ((a : F) + b) ^ 2 - 4 * (a * b) = ((a : F) - b) ^ 2 := by ring
  rw [this]
  exact pow_ne_zero _ (sub_ne_zero.2 fun h => hab (Units.ext h))

theorem indicator_inv_mul_eq_mul_prod {G H ι : Type*} [Group G] [Group H] [Fintype ι] [DecidableEq ι]
    (Ψ : G ≃* (ι → H)) (S : Set G) (T : Set H) (hmem : ∀ x, x ∈ S ↔ ∀ j, Ψ x j ∈ T)
    (i₀ : ι) (A : G) (B : H) (hA : Ψ A = Pi.mulSingle i₀ B) (g : G) :
    S.indicator (fun _ => (1 : ℂ)) (A⁻¹ * g) =
      T.indicator (fun _ => (1 : ℂ)) (B⁻¹ * Ψ g i₀) *
        ∏ j ∈ Finset.univ.erase i₀, T.indicator (fun _ => (1 : ℂ)) (Ψ g j) := by
  classical
  have h1 : Ψ (A⁻¹ * g) = (Ψ A)⁻¹ * Ψ g := by rw [map_mul, map_inv]
  have hc_same : Ψ (A⁻¹ * g) i₀ = B⁻¹ * Ψ g i₀ := by
    rw [h1, Pi.mul_apply, Pi.inv_apply, hA, Pi.mulSingle_eq_same]
  have hc_ne : ∀ j, j ≠ i₀ → Ψ (A⁻¹ * g) j = Ψ g j := by
    intro j hj
    rw [h1, Pi.mul_apply, Pi.inv_apply, hA, Pi.mulSingle_eq_of_ne hj, inv_one, one_mul]
  have hP : A⁻¹ * g ∈ S ↔ (B⁻¹ * Ψ g i₀ ∈ T ∧ ∀ j ∈ Finset.univ.erase i₀, Ψ g j ∈ T) := by
    rw [hmem]
    constructor
    · intro h
      refine ⟨?_, fun j hj => ?_⟩
      · rw [← hc_same]; exact h i₀
      · rw [← hc_ne j (Finset.mem_erase.1 hj).1]; exact h j
    · rintro ⟨h0, h1'⟩ j
      by_cases hj : j = i₀
      · subst hj; rw [hc_same]; exact h0
      · rw [hc_ne j hj]; exact h1' j (Finset.mem_erase.2 ⟨hj, Finset.mem_univ _⟩)
  by_cases hA' : B⁻¹ * Ψ g i₀ ∈ T
  · by_cases hB : ∀ j ∈ Finset.univ.erase i₀, Ψ g j ∈ T
    · rw [Set.indicator_of_mem (hP.2 ⟨hA', hB⟩), Set.indicator_of_mem hA', one_mul]
      exact (Finset.prod_eq_one fun j hj => by rw [Set.indicator_of_mem (hB j hj)]).symm
    · rw [Set.indicator_of_notMem (fun h => hB (hP.1 h).2)]
      push Not at hB
      obtain ⟨j, hj, hnot⟩ := hB
      rw [Finset.prod_eq_zero hj (Set.indicator_of_notMem hnot _), mul_zero]
  · rw [Set.indicator_of_notMem (fun h => hA' (hP.1 h).1), Set.indicator_of_notMem hA', zero_mul]

section NormKit

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

open AutomorphicForm

theorem mem_integers_iff_norm (y : v.adicCompletion K) :
    y ∈ v.adicCompletionIntegers K ↔ ‖y‖ ≤ 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, Valued.toNormedField.norm_le_one_iff]

theorem coe_integers_eq_closedBall :
    (v.adicCompletionIntegers K : Set (v.adicCompletion K)) = Metric.closedBall (0 : v.adicCompletion K) 1 := by
  ext y
  rw [SetLike.mem_coe, mem_integers_iff_norm, Metric.mem_closedBall, dist_zero_right]

theorem norm_entry_le_one_of_mem {g : GL (Fin 2) (v.adicCompletion K)} (hg : g ∈ localIntegralSet K v)
    (i j : Fin 2) : ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j‖ ≤ 1 :=
  (mem_integers_iff_norm K v _).1 (((mem_localIntegralSet K v).1 hg).1 i j)

theorem norm_inv_entry_le_one_of_mem {g : GL (Fin 2) (v.adicCompletion K)} (hg : g ∈ localIntegralSet K v)
    (i j : Fin 2) : ‖((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j‖ ≤ 1 :=
  (mem_integers_iff_norm K v _).1 (((mem_localIntegralSet K v).1 hg).2 i j)

theorem norm_det_le_one {M : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)} (hM : ∀ i j, ‖M i j‖ ≤ 1) :
    ‖M.det‖ ≤ 1 := by
  rw [Matrix.det_fin_two, sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]; exact mul_le_one₀ (hM 0 0) (norm_nonneg _) (hM 1 1)
  · rw [norm_neg, norm_mul]; exact mul_le_one₀ (hM 0 1) (norm_nonneg _) (hM 1 0)

theorem norm_det_eq_one_of_mem {g : GL (Fin 2) (v.adicCompletion K)} (hg : g ∈ localIntegralSet K v) :
    ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det‖ = 1 := by
  have h1 : ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det‖ ≤ 1 :=
    norm_det_le_one K v (norm_entry_le_one_of_mem K v hg)
  have h2 : ‖((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det‖ ≤ 1 :=
    norm_det_le_one K v (norm_inv_entry_le_one_of_mem K v hg)
  have hprod : (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det *
      ((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have hn : ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det‖ *
      ‖((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det‖ = 1 := by
    rw [← norm_mul, hprod, norm_one]
  by_contra hne
  have hlt : ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det‖ < 1 := lt_of_le_of_ne h1 hne
  have : ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det‖ *
      ‖((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det‖ < 1 :=
    mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hlt h2
  exact this.ne hn

theorem mem_localIntegralSet_of_norm {g : GL (Fin 2) (v.adicCompletion K)}
    (h1 : ∀ i j, ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j‖ ≤ 1)
    (h2 : ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det‖ = 1) : g ∈ localIntegralSet K v := by
  refine (mem_localIntegralSet K v).2 ⟨fun i j => (mem_integers_iff_norm K v _).2 (h1 i j), fun i j => ?_⟩
  rw [mem_integers_iff_norm, Matrix.coe_units_inv, Matrix.inv_def, Matrix.adjugate_fin_two, Ring.inverse_eq_inv',
    Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv, h2, inv_one, one_mul]
  fin_cases i <;> fin_cases j
  · exact h1 1 1
  · simpa using h1 0 1
  · simpa using h1 1 0
  · exact h1 0 0

theorem mem_localIntegralSet_iff_norm (g : GL (Fin 2) (v.adicCompletion K)) :
    g ∈ localIntegralSet K v ↔ (∀ i j, ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j‖ ≤ 1) ∧
      ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det‖ = 1 :=
  ⟨fun hg => ⟨norm_entry_le_one_of_mem K v hg, norm_det_eq_one_of_mem K v hg⟩,
    fun h => mem_localIntegralSet_of_norm K v h.1 h.2⟩

theorem norm_mul_entry_le_one {M N : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)} (hM : ∀ i j, ‖M i j‖ ≤ 1)
    (hN : ∀ i j, ‖N i j‖ ≤ 1) (i j : Fin 2) : ‖(M * N) i j‖ ≤ 1 := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]; exact mul_le_one₀ (hM i 0) (norm_nonneg _) (hN 0 j)
  · rw [norm_mul]; exact mul_le_one₀ (hM i 1) (norm_nonneg _) (hN 1 j)

theorem mul_mem_localIntegralSet {g h : GL (Fin 2) (v.adicCompletion K)} (hg : g ∈ localIntegralSet K v)
    (hh : h ∈ localIntegralSet K v) : g * h ∈ localIntegralSet K v := by
  rw [mem_localIntegralSet_iff_norm] at hg hh ⊢
  refine ⟨fun i j => ?_, ?_⟩
  · rw [Units.val_mul]; exact norm_mul_entry_le_one K v hg.1 hh.1 i j
  · rw [Units.val_mul, Matrix.det_mul, norm_mul, hg.2, hh.2, one_mul]

theorem inv_mem_localIntegralSet {g : GL (Fin 2) (v.adicCompletion K)} (hg : g ∈ localIntegralSet K v) :
    g⁻¹ ∈ localIntegralSet K v := by
  rw [mem_localIntegralSet] at hg ⊢
  rw [inv_inv]
  exact ⟨hg.2, hg.1⟩

theorem mul_mem_localIntegralSet_iff_left {g h : GL (Fin 2) (v.adicCompletion K)} (hh : h ∈ localIntegralSet K v) :
    g * h ∈ localIntegralSet K v ↔ g ∈ localIntegralSet K v := by
  refine ⟨fun hgh => ?_, fun hg => mul_mem_localIntegralSet K v hg hh⟩
  have := mul_mem_localIntegralSet K v hgh (inv_mem_localIntegralSet K v hh)
  rwa [mul_inv_cancel_right] at this

end NormKit

section SplitCount

theorem nontrivial_extension_of_inertiaDeg_eq_one
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hprime : (Module.finrank K L).Prime) (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (w₀ : v.Extension (𝓞 L)) (hsplit : v.asIdeal.inertiaDeg' w₀.1.asIdeal = 1) :
    Nontrivial (v.Extension (𝓞 L)) := by
  letI := HeightOneSpectrum.Extension.fintype (𝓞 K) K L (𝓞 L) v
  have hsum := Ideal.sum_ramification_inertia_extensions (𝓞 K) K L (𝓞 L) v
  by_contra hnt
  haveI : Subsingleton (v.Extension (𝓞 L)) := not_nontrivial_iff_subsingleton.1 hnt
  have hone : ∀ w : v.Extension (𝓞 L), Ideal.ramificationIdx' v.asIdeal w.val.asIdeal *
      (v.asIdeal).inertiaDeg' (w.val.asIdeal) = 1 := by
    intro w
    rw [Subsingleton.elim w w₀]
    have he := hv w₀.1 w₀.2
    rw [w₀.2] at he
    rw [he, hsplit, one_mul]
  rw [Fintype.sum_subsingleton _ w₀, hone] at hsum
  exact hprime.ne_one hsum.symm

end SplitCount

section WordKernel

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
  {G : Type*} [Group G] (φ : G →* GL (Fin 2) (v.adicCompletion K))
  (n : ℕ) (rL : Fin n → G) (z : G) (k j : ℕ)

open AutomorphicForm

theorem isLocalTestFn_sum_indicator_map_word :
    IsLocalTestFn K v (fun u : GL (Fin 2) (v.adicCompletion K) =>
      ∑ ι' : Fin k → Fin n, (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
        ((φ ((List.ofFn fun m => rL (ι' m)).prod * z ^ j))⁻¹ * u)) := by
  have h := AutomorphicForm.isLocalTestFn_sum_indicator_localIntegralSet_prod_mul_zpow_inv_mul K v n
    (fun i => φ (rL i)) (φ z) k j
  have hfun : (fun u : GL (Fin 2) (v.adicCompletion K) =>
      ∑ ι' : Fin k → Fin n, (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
        ((φ ((List.ofFn fun m => rL (ι' m)).prod * z ^ j))⁻¹ * u)) =
      fun x : GL (Fin 2) (v.adicCompletion K) =>
        ∑ ι' : Fin k → Fin n, (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
          (((List.ofFn fun i => φ (rL (ι' i))).prod * (φ z) ^ j)⁻¹ * x) := by
    funext x
    refine Finset.sum_congr rfl fun ι' _ => ?_
    rw [map_mul, map_pow, map_list_prod, List.map_ofFn]
    rfl
  rw [hfun]; exact h

theorem sum_indicator_map_word_mul_right (y k' : GL (Fin 2) (v.adicCompletion K))
    (hk' : k' ∈ localIntegralSet K v) :
    (∑ ι' : Fin k → Fin n, (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
        ((φ ((List.ofFn fun m => rL (ι' m)).prod * z ^ j))⁻¹ * (y * k'))) =
      ∑ ι' : Fin k → Fin n, (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
        ((φ ((List.ofFn fun m => rL (ι' m)).prod * z ^ j))⁻¹ * y) := by
  refine Finset.sum_congr rfl fun ι' _ => ?_
  rw [← mul_assoc]
  by_cases h : (φ ((List.ofFn fun m => rL (ι' m)).prod * z ^ j))⁻¹ * y ∈ localIntegralSet K v
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (mul_mem_localIntegralSet K v h hk')]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem]
    intro h'
    exact h ((mul_mem_localIntegralSet_iff_left K v hk').1 h')

end WordKernel

end WSplitGlue

open WSplitGlue AutomorphicForm in
set_option maxHeartbeats 1600000 in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hprime : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)

    (ws : ∀ u : HeightOneSpectrum (𝓞 K), u.Extension (𝓞 L))
    (hsplit : v.asIdeal.inertiaDeg' (ws v).1.asIdeal = 1)
    (ϖ : (ws v).1.adicCompletionIntegers L) (hϖ : Irreducible ϖ)
    (hϖ0 : algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) ϖ ≠ 0)
    (n : ℕ) (rL : Fin n → GL (Fin 2) ((ws v).1.adicCompletion L))
    (hrL : HeckeIntegralSeam.IsHeckeCosetSystem
      (LocalGL2.integralSubgroup ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L))
      (LocalGL2.diagPi ϖ hϖ0) rL)
    (z : GL (Fin 2) ((ws v).1.adicCompletion L))
    (hz : (z : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L)) =
      algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) ϖ •
        (1 : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L)))

    (ϖK : v.adicCompletionIntegers K) (hϖK : Irreducible ϖK)
    (hϖK0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖK ≠ 0)
    (nK : ℕ) (rK : Fin nK → GL (Fin 2) (v.adicCompletion K))
    (hrK : HeckeIntegralSeam.IsHeckeCosetSystem
      (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
      (LocalGL2.diagPi ϖK hϖK0) rK)
    (zK : GL (Fin 2) (v.adicCompletion K))
    (hzK : (zK : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖK •
        (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))
    (k j : ℕ)

    (a b : (v.adicCompletion K)ˣ) (hab : a ≠ b)
    (α β : (L ⊗[K] v.adicCompletion K)ˣ)
    (hN : AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
      AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a b))
    (τ : @Measure (AutomorphicForm.localCentralizer K v (diagUnits2 a b))
      (AutomorphicForm.localCentralizerBorel K v (diagUnits2 a b)))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v (diagUnits2 a b)) τ)
    (hτ1 : τ {t | (t : GL (Fin 2) (v.adicCompletion K)) ∈ AutomorphicForm.localIntegralSet K v} = 1)
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α β))
      (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)))
    (hτ' : @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)) τ')
    (hτ'1 : τ' {t | (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈
      AutomorphicForm.semiLocalIntegralSet K L v} = 1)
    (J J' : ℂ)
    (hJ : AutomorphicForm.IsWeightedOrbitalIntegral K v (diagUnits2 a b) τ
      (fun x : GL (Fin 2) (v.adicCompletion K) =>
        ∑ e ∈ (SatakeCombination.slotWord K L ws v k j).support,
          SatakeCombination.slotCoeff K L ws v k j e *
            ∑ ι : Fin (e 0) → Fin nK,
              (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                (((List.ofFn fun m => rK (ι m)).prod * zK ^ (e 1))⁻¹ * x))
      J)
    (hJ' : AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ (diagUnits2 α β) τ'
      (fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
        ∑ ι : Fin k → Fin n,
          (AutomorphicForm.semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
            ((AutomorphicForm.semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
              ((List.ofFn fun m => rL (ι m)).prod * z ^ j)))⁻¹ * x))
      J') :
    J' = (Module.finrank K L : ℂ) * J := by
  classical
  haveI hfd : FiniteDimensional K L := Module.finite_of_finrank_pos hprime.pos
  letI mG : MeasurableSpace (GL (Fin 2) (v.adicCompletion K)) := AutomorphicForm.localGLBorel K v
  haveI : BorelSpace (GL (Fin 2) (v.adicCompletion K)) := AutomorphicForm.borelSpace_localGLBorel K v
  letI mGL : MeasurableSpace (GL (Fin 2) (L ⊗[K] (v.adicCompletion K))) := AutomorphicForm.glBorelOf (L ⊗[K] (v.adicCompletion K))
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] (v.adicCompletion K))) := AutomorphicForm.borelSpace_glBorelOf (L ⊗[K] (v.adicCompletion K))
  haveI : IsTopologicalGroup (GL (Fin 2) (L ⊗[K] (v.adicCompletion K))) := AutomorphicForm.isTopologicalGroup_tensorGL K L (v.adicCompletion K)
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → (v.adicCompletion K)))
  haveI : SecondCountableTopology (GL (Fin 2) (v.adicCompletion K)) := secondCountableTopology_units _

  have hsplitN : Nontrivial (v.Extension (𝓞 L)) :=
    nontrivial_extension_of_inertiaDeg_eq_one K L hprime v hv (ws v) hsplit

  obtain ⟨ι⟩ := NumberField.nonempty_algHom_adicCompletion_of_nontrivial_extension_of_prime K L hprime σ hσ v hv hsplitN
  obtain ⟨hc1, hc2, hshift, hconst, hnormS, -, -⟩ :=
    AutomorphicForm.SplitPlace.continuous_coords_and_coords_sigmaGL_and_coords_normString_and_exists_pos_map_coords_eq_smul_pi
      K L hprime σ hσ (v.adicCompletion K) ι (AutomorphicForm.semiLocalHaar K L v) (AutomorphicForm.isHaarMeasure_semiLocalHaar K L v)
      (AutomorphicForm.localHaar K v) (AutomorphicForm.isHaarMeasure_localHaar K v)
  obtain ⟨hmem, hwt, hmap⟩ := AutomorphicForm.SplitPlace.mem_semiLocalIntegralSet_iff_coords_and_semiLocalWeight_eq_sum_and_map_coords_semiLocalHaar K L hprime σ hσ v hv ι

  obtain ⟨i₀, e, he, hcoordW⟩ :=
    AutomorphicForm.SplitPlace.exists_ringEquiv_coords_semiLocalComponent_localEmbed_eq_mulSingle
      K L hprime σ hσ v hv (ws v) hsplit ι
  set Ψ := AutomorphicForm.SplitPlace.coords (v.adicCompletion K) σ ι hprime hσ with hΨ

  obtain ⟨F, hF⟩ : ∃ F : GL (Fin 2) (v.adicCompletion K) → ℂ, F = fun u =>
    ∑ ι' : Fin k → Fin n,
      (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
        ((Matrix.GeneralLinearGroup.map e.toRingHom ((List.ofFn fun m => rL (ι' m)).prod * z ^ j))⁻¹ * u) := ⟨_, rfl⟩
  have hFtest : AutomorphicForm.IsLocalTestFn K v F := by
    rw [hF]
    exact isLocalTestFn_sum_indicator_map_word K v (Matrix.GeneralLinearGroup.map e.toRingHom) n rL z k j
  have hFK : ∀ (y k' : GL (Fin 2) (v.adicCompletion K)), k' ∈ AutomorphicForm.localIntegralSet K v → F (y * k') = F y := by
    intro y k' hk'
    rw [hF]
    exact sum_indicator_map_word_mul_right K v (Matrix.GeneralLinearGroup.map e.toRingHom) n rL z k j y k' hk'

  set δs : Fin (Module.finrank K L - 1 + 1) → GL (Fin 2) (v.adicCompletion K) := fun j' => Ψ (diagUnits2 α β) j' with hδs
  have hδdiag : ∀ j', ((δs j' : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 ∧
      ((δs j' : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0 := by
    intro j'
    simp only [hδs, hΨ, AutomorphicForm.SplitPlace.coords_apply_val, LanglandsTunnell.CubicInduction.diagUnits2,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Matrix.empty_val', map_zero, Pi.zero_apply, and_self]
  have hγs : ∀ j' : Fin (Module.finrank K L - 1 + 1),
      (List.ofFn fun k' : Fin (Module.finrank K L - 1 + 1) => δs (j' + k')).prod = diagUnits2 a b := by
    intro j'
    have h := hnormS (diagUnits2 α β) j'
    rw [hN, hconst] at h
    exact h.symm

  have hreg : AutomorphicForm.IsRegularSemisimple (diagUnits2 a b) := isRegularSemisimple_diagUnits2 a b hab
  have hcardAut : Nat.card (L ≃ₐ[K] L) = Module.finrank K L := by
    rw [Nat.card_eq_fintype_card]
    apply Nat.dvd_antisymm (AutomorphicForm.SplitPlace.card_aut_dvd_finrank K L)
    rw [← AutomorphicForm.SplitPlace.orderOf_eq_finrank hprime σ hσ]
    exact orderOf_dvd_card
  haveI : IsGalois K L := IsGalois.of_card_aut_eq_finrank K L hcardAut
  have hgen : ∀ θ : L ≃ₐ[K] L, θ ∈ Subgroup.zpowers σ := by
    have htop : Subgroup.zpowers σ = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [Nat.card_zpowers, AutomorphicForm.SplitPlace.orderOf_eq_finrank hprime σ hσ, hcardAut]
    intro θ
    rw [htop]
    exact Subgroup.mem_top θ
  obtain ⟨eC, heC⟩ :=
    AutomorphicForm.exists_continuousMulEquiv_centralizer_twistedCentralizer_of_isNormConjugator
      K L σ hgen (v.adicCompletion K) (diagUnits2 a b) hreg (diagUnits2 α β) 1
      (by simp [AutomorphicForm.IsNormConjugator, hN])
  letI mT : MeasurableSpace (AutomorphicForm.localCentralizer K v (diagUnits2 a b)) :=
    AutomorphicForm.localCentralizerBorel K v (diagUnits2 a b)
  letI mT' : MeasurableSpace (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α β)) :=
    AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)
  haveI : BorelSpace (AutomorphicForm.localCentralizer K v (diagUnits2 a b)) := ⟨rfl⟩
  haveI : BorelSpace (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α β)) := ⟨rfl⟩
  haveI := hτ'
  let eM : AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α β) ≃ᵐ
      AutomorphicForm.localCentralizer K v (diagUnits2 a b) := eC.symm.toHomeomorph.toMeasurableEquiv
  have heM : ∀ t', (eM t' : GL (Fin 2) (v.adicCompletion K)) = (eC.symm t' : GL (Fin 2) (v.adicCompletion K)) := fun _ => rfl
  have hecoe : ∀ t' : AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α β),
      (t' : GL (Fin 2) (L ⊗[K] (v.adicCompletion K))) = AutomorphicForm.toTensorGL K L (v.adicCompletion K) (eC.symm t' : GL (Fin 2) (v.adicCompletion K)) := by
    intro t'
    have h := heC (eC.symm t')
    rw [ContinuousMulEquiv.apply_symm_apply] at h
    rw [h]
    simp
  have hconstmem : ∀ g0 : GL (Fin 2) (v.adicCompletion K), AutomorphicForm.toTensorGL K L (v.adicCompletion K) g0 ∈ AutomorphicForm.semiLocalIntegralSet K L v ↔
      g0 ∈ AutomorphicForm.localIntegralSet K v := by
    intro g0
    rw [hmem]
    have hΨc : Ψ (AutomorphicForm.toTensorGL K L (v.adicCompletion K) g0) = fun _ => g0 := hconst g0
    simp only [hΨc]
    exact ⟨fun h => h 0, fun h _ => h⟩
  obtain ⟨τt, hτtdef⟩ : ∃ τt : Measure (AutomorphicForm.localCentralizer K v (diagUnits2 a b)), τt = Measure.map eM τ' :=
    ⟨_, rfl⟩
  have hτt : τt.IsHaarMeasure := by
    have := ContinuousMulEquiv.isHaarMeasure_map τ' eC.symm
    rw [hτtdef]
    exact this
  have hτt1 : τt {t | (t : GL (Fin 2) (v.adicCompletion K)) ∈ AutomorphicForm.localIntegralSet K v} = 1 := by
    rw [hτtdef, MeasurableEquiv.map_apply]
    convert hτ'1 using 2
    ext t'
    simp only [Set.mem_preimage, Set.mem_setOf_eq, heM]
    rw [hecoe t', hconstmem]

  obtain ⟨s, hs, hJ'eq⟩ := hJ'
  obtain ⟨hs0, hsm, hsc, hs1⟩ := hs
  let s' : (Fin (Module.finrank K L - 1 + 1) → GL (Fin 2) (v.adicCompletion K)) → ℝ := fun y => s (Ψ.symm y)
  have hs0' : ∀ y, 0 ≤ s' y := fun y => hs0 _
  let ΨH : GL (Fin 2) (L ⊗[K] (v.adicCompletion K)) ≃ₜ (Fin (Module.finrank K L - 1 + 1) → GL (Fin 2) (v.adicCompletion K)) :=
    { toEquiv := Ψ.toEquiv, continuous_toFun := hc1, continuous_invFun := hc2 }
  have hΨH : ∀ y, ΨH.symm y = Ψ.symm y := fun _ => rfl
  have hsm' : Measurable s' := hsm.comp hc2.measurable
  have hsc' : HasCompactSupport s' := by
    have := hsc.comp_homeomorph ΨH.symm
    exact this
  have hΨconj : ∀ (y : Fin (Module.finrank K L - 1 + 1) → GL (Fin 2) (v.adicCompletion K)) (j' : Fin (Module.finrank K L - 1 + 1)),
      Ψ ((Ψ.symm y)⁻¹ * diagUnits2 α β * AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ (Ψ.symm y)) j' =
        (y j')⁻¹ * δs j' * y (j' + 1) := by
    intro y j'
    rw [map_mul, map_mul, map_inv]
    simp only [Pi.mul_apply, Pi.inv_apply, hshift, MulEquiv.apply_symm_apply, hδs]
  have hΨconst : ∀ (g0 : GL (Fin 2) (v.adicCompletion K)) (y : Fin (Module.finrank K L - 1 + 1) → GL (Fin 2) (v.adicCompletion K)),
      Ψ.symm (fun j' => g0 * y j') = AutomorphicForm.toTensorGL K L (v.adicCompletion K) g0 * Ψ.symm y := by
    intro g0 y
    apply Ψ.injective
    rw [MulEquiv.apply_symm_apply, map_mul, hconst, MulEquiv.apply_symm_apply]
    rfl

  have hφΨ : ∀ g : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
      (∑ ι' : Fin k → Fin n,
          (AutomorphicForm.semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
            ((AutomorphicForm.semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
              ((List.ofFn fun m => rL (ι' m)).prod * z ^ j)))⁻¹ * g)) =
        F (Ψ g i₀) * ∏ j' ∈ Finset.univ.erase i₀,
          (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ)) (Ψ g j') := by
    intro g
    simp only [hF]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun ι' _ => ?_
    exact indicator_inv_mul_eq_mul_prod Ψ _ _ hmem i₀ _ _ (hcoordW _) g

  have hs1' : ∀ y : Fin (Module.finrank K L - 1 + 1) → GL (Fin 2) (v.adicCompletion K),
      F ((y i₀)⁻¹ * δs i₀ * y (i₀ + 1)) *
          (∏ j' ∈ Finset.univ.erase i₀,
            (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ)) ((y j')⁻¹ * δs j' * y (j' + 1))) ≠ 0 →
      ∫ t : AutomorphicForm.localCentralizer K v (diagUnits2 a b), s' (fun j' => (t.1 : GL (Fin 2) (v.adicCompletion K)) * y j') ∂τt = 1 := by
    intro y hy
    rw [hτtdef, MeasureTheory.integral_map_equiv]
    have h1 := hs1 (Ψ.symm y) (by
      beta_reduce
      rw [hφΨ]
      simp only [hΨconj]
      exact hy)
    refine (integral_congr_ae (Filter.Eventually.of_forall fun t' => ?_)).trans h1
    show s (Ψ.symm (fun j' => ((eM t').1 : GL (Fin 2) (v.adicCompletion K)) * y j')) = s ((t'.1 : GL (Fin 2) (L ⊗[K] (v.adicCompletion K))) * Ψ.symm y)
    rw [hΨconst, heM, ← hecoe]

  obtain ⟨J₁, hJ₁w, hJ₁eq⟩ :=
    AutomorphicForm.exists_isWeightedOrbitalIntegral_and_integral_pi_mul_prod_indicator_cyclicString_eq_mul_of_forall_mul_eq
      K v (Module.finrank K L - 1) i₀ δs hδdiag a b hab hγs τt hτt hτt1 F hFtest hFK s' hs0' hsm' hsc' hs1'

  have hJ'Ψ : J' = ∫ y : Fin (Module.finrank K L - 1 + 1) → GL (Fin 2) (v.adicCompletion K),
      F ((y i₀)⁻¹ * δs i₀ * y (i₀ + 1)) *
        (∏ j' ∈ Finset.univ.erase i₀,
          (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ)) ((y j')⁻¹ * δs j' * y (j' + 1))) *
        ((∑ j', AutomorphicForm.LocalWeight.weight (y j') : ℝ) : ℂ) * (s' y : ℂ)
      ∂(Measure.pi fun _ => AutomorphicForm.localHaar K v) := by
    let ΨM : GL (Fin 2) (L ⊗[K] (v.adicCompletion K)) ≃ᵐ (Fin (Module.finrank K L - 1 + 1) → GL (Fin 2) (v.adicCompletion K)) := ΨH.toMeasurableEquiv
    have hΨM : (⇑ΨM : GL (Fin 2) (L ⊗[K] (v.adicCompletion K)) → _) = ⇑Ψ := rfl
    rw [hJ'eq, ← hmap, ← hΨM, MeasureTheory.integral_map_equiv]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    beta_reduce
    rw [show ΨM x = Ψ x from rfl]
    have hsx : s' (Ψ x) = s x := by
      show s (Ψ.symm (Ψ x)) = s x
      rw [MulEquiv.symm_apply_apply]
    have hix := hφΨ (x⁻¹ * diagUnits2 α β * AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ x)
    have hconjx : ∀ j', Ψ (x⁻¹ * diagUnits2 α β * AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ x) j' =
        (Ψ x j')⁻¹ * δs j' * Ψ x (j' + 1) := by
      intro j'
      have := hΨconj (Ψ x) j'
      rw [MulEquiv.symm_apply_apply] at this
      exact this
    simp only [hconjx] at hix
    rw [hsx, hwt x, hix]

  have hN3 := AutomorphicForm.SatakeCombination.sum_slotCoeff_mul_sum_indicator_heckeWord_eq_sum_indicator_map_heckeWord_of_inertiaDeg_eq_one
    K L v ws hsplit ϖ hϖ hϖ0 n rL hrL z hz ϖK hϖK hϖK0 nK rK hrK zK hzK k j e he
  rw [hN3] at hJ
  have hJF : AutomorphicForm.IsWeightedOrbitalIntegral K v (diagUnits2 a b) τ F J := by rw [hF]; exact hJ
  have hdiag : ((diagUnits2 a b : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 ∧
      ((diagUnits2 a b : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0 := by
    constructor <;> simp [LanglandsTunnell.CubicInduction.coe_diagUnits2]
  have hJJ : J₁ = J :=
    AutomorphicForm.eq_of_isWeightedOrbitalIntegral_of_isWeightedOrbitalIntegral_diagonal_of_measure_preimage_localIntegralSet_eq_one
      K v (diagUnits2 a b) hreg hdiag.1 hdiag.2 τt τ hτt hτ hτt1 hτ1 F hFtest J₁ J hJ₁w hJF
  rw [hJ'Ψ, hJ₁eq, hJJ, ← AutomorphicForm.SplitPlace.finrank_eq_succ K L]

end S_AutomorphicForm_twistedWeighted_eq_finrank_mul_weighted_heckeWord_of_inertiaDeg_eq_one
end P2MW
export P2MW.S_AutomorphicForm_twistedWeighted_eq_finrank_mul_weighted_heckeWord_of_inertiaDeg_eq_one (solution)
