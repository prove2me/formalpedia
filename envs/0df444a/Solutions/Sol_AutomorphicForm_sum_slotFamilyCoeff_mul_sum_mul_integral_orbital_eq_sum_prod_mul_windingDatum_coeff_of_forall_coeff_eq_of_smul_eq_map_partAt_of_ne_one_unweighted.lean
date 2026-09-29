-- Prove2me | solution 1 for AutomorphicForm.sum_slotFamilyCoeff_mul_sum_mul_integral_orbital_eq_sum_prod_mul_windingDatum_coeff_of_forall_coeff_eq_of_smul_eq_map_partAt_of_ne_one_unweighted
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/28b00eb1-0e01-57af-96d7-04bd4676edcf

import Mathlib.Algebra.Polynomial.Laurent
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

import Theorems.Thm_AutomorphicForm_integral_mul_orbital_centralScalar_eq_mul_ideleNorm_mul_prod_tsum_mul_integral_of_isUnitFactorization_of_integrable
import Theorems.Thm_AutomorphicForm_sum_slotCoeff_mul_tsum_pow_mul_eq_inv_norm_sub_one_mul_ite_of_isOrbitalIntegral_heckeWord_diagonal_zpow
import Theorems.Thm_AutomorphicForm_exists_isOrbitalIntegral_of_isRegularSemisimple_of_isLocalTestFn
import Theorems.Thm_AutomorphicForm_isHaarMeasure_and_pos_of_forall_integral_adelicGLHaar_eq_mul_integral_mul_prod
import Theorems.Thm_AutomorphicForm_integrable_mul_orbital_mul_prod_orbital_sPart_of_isArchTestFactor_of_isLocalTestFn
import Theorems.Thm_AutomorphicForm_isLocalTestFn_sum_indicator_localIntegralSet_prod_mul_zpow_inv_mul
import Theorems.Thm_AutomorphicForm_sum_indicator_localIntegralSet_prod_mul_zpow_inv_mul_centralUnit_mul
import Theorems.Thm_NumberField_Idele_norm_algebraMap_adicCompletion_eq_norm_uniformizer_zpow_ord
import Theorems.Thm_AutomorphicForm_coe_finComponent_glFin_centralScalar_localUnit_mul_diagUnits2
import Theorems.Thm_AutomorphicForm_mul_prod_orbital_eq_zero_of_forall_apply_conj_centralScalar_mul_diagUnits2_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_sum_slotFamilyCoeff_mul_sum_mul_integral_orbital_eq_sum_prod_mul_windingDatum_coeff_of_forall_coeff_eq_of_smul_eq_map_partAt_of_ne_one_unweighted
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val"
p2m_attr_erase "simp" "AutomorphicForm.borelDiagSnd_apply_val"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

namespace AutomorphicForm p2m_export "AutomorphicForm" "glBorelOf centralizerBorel IsOrbitalIntegralOn IsUnitFactorization IsLocalTestFn localIntegralSet localGLBorel localHaar localCentralizer localCentralizerBorel IsOrbitalIntegral IsRegularSemisimple isRegularSemisimple_iff_ne_zero IsArchTestFactor IsFinTestFactor globalPoints centralScalar SatakeCombination.slotDeg SatakeCombination.slotWord SatakeCombination.slotCoeff SatakeCombination.slotIndex SatakeCombination.slotFamilyCoeff WindingDatum integral_mul_orbital_centralScalar_eq_mul_ideleNorm_mul_prod_tsum_mul_integral_of_isUnitFactorization_of_integrable sum_slotCoeff_mul_tsum_pow_mul_eq_inv_norm_sub_one_mul_ite_of_isOrbitalIntegral_heckeWord_diagonal_zpow exists_isOrbitalIntegral_of_isRegularSemisimple_of_isLocalTestFn isHaarMeasure_and_pos_of_forall_integral_adelicGLHaar_eq_mul_integral_mul_prod integrable_mul_orbital_mul_prod_orbital_sPart_of_isArchTestFactor_of_isLocalTestFn isLocalTestFn_sum_indicator_localIntegralSet_prod_mul_zpow_inv_mul sum_indicator_localIntegralSet_prod_mul_zpow_inv_mul_centralUnit_mul coe_finComponent_glFin_centralScalar_localUnit_mul_diagUnits2 mul_prod_orbital_eq_zero_of_forall_apply_conj_centralScalar_mul_diagUnits2_eq_zero" namespace WindPack end AutomorphicForm.WindPack
p2m_open_scoped "AutomorphicForm" in
open scoped Classical in

theorem AutomorphicForm.WindPack.sum_mul_elim_eq_sum_mul_finsum_mem
    {U : Type*} {d : ℕ} (Δ : Finset U) (box : Finset (Fin d → ℤ))
    (A : U → ℂ) (g : (Fin d → ℤ) → ℂ) (c : (Fin d → ℤ) → ℂ)
    (P : U → Prop) (lat : U → Option (Fin d → ℤ))
    (hΔP : ∀ u ∈ Δ, P u)
    (hout : ∀ u, P u → ∀ n, lat u = some n → u ∉ Δ → g n * A u = 0)
    (hbox : ∀ n, n ∉ box → g n = 0) :
    ∑ u ∈ Δ, A u * ((lat u).elim 0 fun n => g n * c n) =
      ∑ n ∈ box, g n * ∑ᶠ u ∈ {u | P u ∧ lat u = some n}, A u * c n := by
  classical

  have hpt : ∀ u ∈ Δ, A u * ((lat u).elim 0 fun n => g n * c n) =
      ∑ n ∈ box, (if lat u = some n then A u * (g n * c n) else 0) := by
    intro u _
    cases hlu : lat u with
    | none => simp
    | some n₀ =>
      simp only [Option.elim_some]
      by_cases hn : n₀ ∈ box
      · rw [Finset.sum_eq_single_of_mem n₀ hn]
        · simp
        · intro n _ hne
          rw [if_neg]
          intro h
          exact hne (Option.some_injective _ h).symm
      · rw [hbox n₀ hn]
        rw [Finset.sum_eq_zero]
        · simp
        · intro n hnb
          rw [if_neg]
          intro h
          have : n₀ = n := Option.some_injective _ h
          exact hn (this ▸ hnb)
  rw [Finset.sum_congr rfl hpt, Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_

  rw [← Finset.sum_filter]
  by_cases hg : g n = 0
  · simp [hg]
  ·
    have hsub : ({u | P u ∧ lat u = some n} ∩ Function.support fun u => A u * c n) ⊆
        ↑(Δ.filter fun u => lat u = some n) := by
      intro u hu
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Function.mem_support] at hu
      obtain ⟨⟨hP, hl⟩, hne⟩ := hu
      simp only [Finset.coe_filter, Set.mem_setOf_eq]
      refine ⟨?_, hl⟩
      by_contra hΔ
      have h0 := hout u hP n hl hΔ
      rcases mul_eq_zero.mp h0 with h | h
      · exact hg h
      · exact hne (by rw [h, zero_mul])
    have hsup : ↑(Δ.filter fun u => lat u = some n) ⊆ {u | P u ∧ lat u = some n} ∪
        (↑(Δ.filter fun u => lat u = some n) : Set U) := Set.subset_union_right
    rw [finsum_mem_eq_sum_of_subset (fun u => A u * c n) hsub ?_, Finset.mul_sum]
    · refine Finset.sum_congr rfl fun u _ => ?_
      ring
    · intro u hu
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hu
      exact ⟨hΔP u hu.1, hu.2⟩

p2m_open_scoped "AutomorphicForm" in

theorem AutomorphicForm.WindPack.T_add_T_inv_pow_apply_eq_zero (k : ℕ) (m : ℤ) (hm : (k : ℤ) < |m|) :
    ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ k : LaurentPolynomial ℂ).coeff m = 0 := by
  induction k generalizing m with
  | zero =>
    rw [pow_zero, ← LaurentPolynomial.T_zero, LaurentPolynomial.T_apply, if_neg]
    intro h; subst h; simp at hm
  | succ k ih =>
    have h1 : ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ k : LaurentPolynomial ℂ).coeff (m - 1) = 0 := by
      apply ih; push_cast at hm
      rcases abs_cases m with ⟨h, _⟩ | ⟨h, _⟩ <;> rcases abs_cases (m - 1) with ⟨h', _⟩ | ⟨h', _⟩ <;> omega
    have h2 : ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ k : LaurentPolynomial ℂ).coeff (m - -1) = 0 := by
      apply ih; push_cast at hm
      rcases abs_cases m with ⟨h, _⟩ | ⟨h, _⟩ <;> rcases abs_cases (m - -1) with ⟨h', _⟩ | ⟨h', _⟩ <;> omega
    rw [pow_succ, mul_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    unfold LaurentPolynomial.T at h1 h2 ⊢
    erw [AddMonoidAlgebra.coeff_mul_single_apply, AddMonoidAlgebra.coeff_mul_single_apply, h1, h2]
    simp

open scoped Classical in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure]

    (Ξ : Finset ((⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ))
    (hΞc : ∀ ξ ∈ Ξ, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hΞt : ∀ ξ ∈ Ξ, ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξ ⟨z, Subgroup.mem_top z⟩ = 1)
    (SK T : Finset (HeightOneSpectrum (𝓞 K))) (hTS : Disjoint T SK)

    (hur : ∀ ξ ∈ Ξ, ∀ v ∉ SK, ∀ t : (v.adicCompletion K)ˣ, Valued.v (t : v.adicCompletion K) = 1 →
      ξ ⟨Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t), Subgroup.mem_top _⟩ = 1)

    (ϖKs : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K)
    (hϖKi : ∀ v ∈ T, Irreducible (ϖKs v))
    (hϖKs0 : ∀ v ∈ T, algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖKs v) ≠ 0)
    (nKs : HeightOneSpectrum (𝓞 K) → ℕ)
    (rKs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (nKs v) → GL (Fin 2) (v.adicCompletion K))
    (hrKs : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
      HeckeIntegralSeam.IsHeckeCosetSystem
        (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
        (LocalGL2.diagPi (ϖKs v) (hϖKs0 v hv)) (rKs v))
    (zKs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K))
    (hzKs : ∀ v ∈ T, (zKs v : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖKs v) •
        (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))
    (ks js : HeightOneSpectrum (𝓞 K) → ℕ)

    (Nw : HeightOneSpectrum (𝓞 K) → ℕ) (hNw : ∀ v ∈ T, Ideal.absNorm (ws v).1.asIdeal = Nw v)
    (hNwf : ∀ v ∈ T, Nw v = Ideal.absNorm v.asIdeal ^ AutomorphicForm.SatakeCombination.slotDeg K L ws v)
    (ζ s : HeightOneSpectrum (𝓞 K) → ℂ) (hζ : ∀ v ∈ T, ζ v ≠ 0) (hs : ∀ v ∈ T, s v ^ 2 = ζ v)
    (hx : ∀ ξ ∈ Ξ, ∀ v ∈ T,
      ((ξ ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^
          AutomorphicForm.SatakeCombination.slotDeg K L ws v = ζ v)

    (faK : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (hfaK : AutomorphicForm.IsArchTestFactor K faK)
    (fSK : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hfSK : ∀ v ∈ SK, AutomorphicForm.IsLocalTestFn K v (fSK v))
    (fam : ((u : HeightOneSpectrum (𝓞 K)) → u ∈ T → (Fin 2 →₀ ℕ)) → GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ)
    (hfam : ∀ m ∈ AutomorphicForm.SatakeCombination.slotIndex K L ws ks js T,
      ∃ ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ,
        AutomorphicForm.IsFinTestFactor K ff ∧
        (∀ h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K),
          (∀ v ∉ SK ∪ T, AdelicLevel.finComponent (𝓞 K) K v h ∈ AutomorphicForm.localIntegralSet K v) →
            ff h = ∏ v ∈ SK ∪ T,
              (if hv : v ∈ T then fun x : GL (Fin 2) (v.adicCompletion K) =>
                  ∑ ι : Fin ((m v hv) 0) → Fin (nKs v),
                    (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                      (((List.ofFn fun m => rKs v (ι m)).prod * zKs v ^ (m v hv) 1)⁻¹ * x)
                else fSK v) (AdelicLevel.finComponent (𝓞 K) K v h)) ∧
        (∀ h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K),
          (∃ v ∉ SK ∪ T, AdelicLevel.finComponent (𝓞 K) K v h ∉ AutomorphicForm.localIntegralSet K v) →
            ff h = 0) ∧
        ∀ g, fam m g = faK (AdelicLevel.glArch (𝓞 K) K g) * ff (AdelicLevel.glFin (𝓞 K) K g))

    (ΔK : Finset (GL (Fin 2) K))
    (hΔK : ∀ γ ∈ ΔK, (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 ∧
      (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 1)
    (hΔKinj : ∀ γ ∈ ΔK, ∀ γ' ∈ ΔK,
      (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 =
        (γ' : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ' : Matrix (Fin 2) (Fin 2) K) 1 1 → γ = γ')
    (cτK : ℝ) (hcτK : 0 < cτK)
    (τK : ∀ γ : GL (Fin 2) K,
      Measure (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K)))))
    (hτK : ∀ γ : GL (Fin 2) K, (τK γ).IsHaarMeasure)
    (hτKc : ∀ γ ∈ ΔK, ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ,
      ∫ t : Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          g (t : GL (Fin 2) (AdeleRing (𝓞 K) K)) ∂(τK γ) =
        cτK * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ, g (diagUnits2 p.1 p.2) ∂(νZK.prod νZK))
    (IK : (((u : HeightOneSpectrum (𝓞 K)) → u ∈ T → (Fin 2 →₀ ℕ))) → GL (Fin 2) K → (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hIK : ∀ m ∈ AutomorphicForm.SatakeCombination.slotIndex K L ws ks js T, ∀ γ ∈ ΔK,
      ∀ z : (AdeleRing (𝓞 K) K)ˣ,
        AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) (adelicGLHaar (Fin 2) (𝓞 K) K)
          (AutomorphicForm.globalPoints (𝓞 K) K γ) (τK γ)
          (fun g : GL (Fin 2) (AdeleRing (𝓞 K) K) => fam m (AutomorphicForm.centralScalar (𝓞 K) K z * g))
          (IK m γ z))

    (hΔKc : ∀ m ∈ AutomorphicForm.SatakeCombination.slotIndex K L ws ks js T, ∀ u : Kˣ, (u : K) ≠ 1 →
      (∀ γ ∈ ΔK, (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ (u : K)) →
        ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (x : GL (Fin 2) (AdeleRing (𝓞 K) K)),
          fam m (x⁻¹ * (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) * x) = 0)
    (κ₀K κK : ℝ)

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
    (hT : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ), (u : K) ≠ 1 → ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (W : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (Wa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
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

    (PZ : UnramifiedWhittaker.ProductMeasureData SK νZK)
    (hPo : PZ.ord = NumberField.Idele.ord K) (hPp : PZ.projS = NumberField.Idele.partAt K SK)
    (hPν : ENNReal.ofReal PZ.c • PZ.νS =
      Measure.map (NumberField.Idele.partAt K SK)
        (νZK.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑SK) : Set (AdeleRing (𝓞 K) K)ˣ)))

    (IA : Kˣ → (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hIA : ∀ u z, ((u : Kˣ) : K) ≠ 1 → AutomorphicForm.IsOrbitalIntegralOn (InfiniteAdeleRing K) νA
      (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) (τA u z) faK (IA u z))
    (IF : Kˣ → (AdeleRing (𝓞 K) K)ˣ → HeightOneSpectrum (𝓞 K) → ℂ)
    (hIF : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ v ∈ SK, AutomorphicForm.IsOrbitalIntegral K v
      (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τF u z v) (fSK v) (IF u z v))

    (r c : ℕ) (𝒜 : AutomorphicForm.WindingDatum r T.card c)
    (h𝒜 : ∀ n : Fin T.card → ℤ, 𝒜.coeff n =
      ((κ₀K : ℂ) * ((κK : ℝ) : ℂ) * ((cG * cT⁻¹ * PZ.c : ℝ) : ℂ)) *
        ∑ᶠ u ∈ {u : Kˣ | (u : K) ≠ 1 ∧
            (∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK → v ∉ T → NumberField.Idele.ord K v (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) = 0) ∧
            ∀ i : Fin T.card, NumberField.Idele.ord K (T.equivFin.symm i).1 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) =
              (AutomorphicForm.SatakeCombination.slotDeg K L ws (T.equivFin.symm i).1 : ℤ) * n i},
          (∏ i : Fin T.card, (((Real.sqrt (Nw (T.equivFin.symm i).1 : ℝ) : ℂ) * s (T.equivFin.symm i).1) ^ (-(n i)))) *
          (if h1 : (u : K) - 1 ≠ 0 then
              ((NumberField.TateGlobal.ideleNorm K
                  (NumberField.Idele.partAt K SK (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (Units.mk0 ((u : K) - 1) h1))) : ℝ) : ℂ)
            else 0) *
          ∑ ξ ∈ Ξ, ∫ zS : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
              (IA u zS * ∏ v ∈ SK, IF u zS v) ∂PZ.νS) :
    ∑ ξ ∈ Ξ, ∑ m ∈ AutomorphicForm.SatakeCombination.slotIndex K L ws ks js T,
        AutomorphicForm.SatakeCombination.slotFamilyCoeff K L ws ks js T m *
          ∑ γ ∈ ΔK, (κ₀K : ℂ) *
            (((κK : ℝ) : ℂ) *
              ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * IK m γ z ∂νZK) =
      ∑ n ∈ Fintype.piFinset (fun i : Fin T.card => Finset.Icc (-(ks (T.equivFin.symm i).1 : ℤ)) (ks (T.equivFin.symm i).1)),
        (∏ i : Fin T.card,
            ((Real.sqrt (Nw (T.equivFin.symm i).1 : ℝ) : ℂ) * s (T.equivFin.symm i).1) ^ ks (T.equivFin.symm i).1 * ζ (T.equivFin.symm i).1 ^ js (T.equivFin.symm i).1 *
              ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ ks (T.equivFin.symm i).1 : LaurentPolynomial ℂ).coeff (n i)) *
          𝒜.coeff n := by
  classical

  let ι : Kˣ →* (AdeleRing (𝓞 K) K)ˣ := (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K))
  let vI : Fin T.card → HeightOneSpectrum (𝓞 K) := fun i => (T.equivFin.symm i).1
  let fd : Fin T.card → ℕ := fun i => AutomorphicForm.SatakeCombination.slotDeg K L ws (vI i)
  let ordi : Kˣ → Fin T.card → ℤ := fun u i => NumberField.Idele.ord K (vI i) (ι u)
  let ind : Kˣ → Prop := fun u =>
    ∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK → v ∉ T → NumberField.Idele.ord K v (ι u) = 0
  let lat : Kˣ → Option (Fin T.card → ℤ) := fun u =>
    if ∀ i, (fd i : ℤ) ∣ ordi u i then some (fun i => ordi u i / (fd i : ℤ)) else none
  let g : (Fin T.card → ℤ) → ℂ := fun n => ∏ i : Fin T.card,
    ((Real.sqrt (Nw (vI i) : ℝ) : ℂ) * s (vI i)) ^ ks (vI i) * ζ (vI i) ^ js (vI i) *
      ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ ks (vI i) : LaurentPolynomial ℂ).coeff (n i)
  let tw : (Fin T.card → ℤ) → ℂ := fun n =>
    ∏ i : Fin T.card, (((Real.sqrt (Nw (vI i) : ℝ) : ℂ) * s (vI i)) ^ (-(n i)))
  let W : Kˣ → ℂ := fun u => ∑ ξ ∈ Ξ, ∫ zS : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
    (IA u zS * ∏ v ∈ SK, IF u zS v) ∂PZ.νS
  let disc : Kˣ → ℂ := fun u => if h1 : (u : K) - 1 ≠ 0 then
      ((NumberField.TateGlobal.ideleNorm K (NumberField.Idele.partAt K SK (ι (Units.mk0 ((u : K) - 1) h1))) : ℝ) : ℂ)
    else 0
  let Cst : ℂ := (κ₀K : ℂ) * ((κK : ℝ) : ℂ) * ((cG * cT⁻¹ * PZ.c : ℝ) : ℂ)
  let A : Kˣ → ℂ := fun u => Cst * (disc u * W u)
  let P : Kˣ → Prop := fun u => (u : K) ≠ 1 ∧ ind u
  let box : Finset (Fin T.card → ℤ) :=
    Fintype.piFinset (fun i : Fin T.card => Finset.Icc (-(ks (vI i) : ℤ)) (ks (vI i)))
  let ratio : GL (Fin 2) K → Kˣ := fun γ =>
    if h : (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 0 then
      Units.mk0 _ h else 1
  let Δ : Finset Kˣ := (ΔK.image ratio).filter fun u => ind u

  have hnz : ∀ γ ∈ ΔK, (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 0 := by
    intro γ hγ
    obtain ⟨h10, -, -⟩ := hΔK γ hγ
    have hdet : (γ : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := γ.isUnit.map Matrix.detMonoidHom |>.ne_zero
    rw [Matrix.det_fin_two, h10, mul_zero, sub_zero] at hdet
    exact div_ne_zero (left_ne_zero_of_mul hdet) (right_ne_zero_of_mul hdet)
  have hratio : ∀ γ ∈ ΔK, ((ratio γ : Kˣ) : K) =
      (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 := by
    intro γ hγ
    simp only [ratio, dif_pos (hnz γ hγ), Units.val_mk0]
  have hinj : ∀ γ ∈ ΔK, ∀ γ' ∈ ΔK, ratio γ = ratio γ' → γ = γ' := by
    intro γ hγ γ' hγ' h
    apply hΔKinj γ hγ γ' hγ'
    rw [← hratio γ hγ, ← hratio γ' hγ', h]

  have hνA := (AutomorphicForm.isHaarMeasure_and_pos_of_forall_integral_adelicGLHaar_eq_mul_integral_mul_prod K νA cG hG).1

  have hfdv : ∀ v ∈ T, 0 < AutomorphicForm.SatakeCombination.slotDeg K L ws v := by
    intro v hv
    rcases Nat.eq_zero_or_pos (AutomorphicForm.SatakeCombination.slotDeg K L ws v) with h0 | hpos
    · exfalso
      have h1 : Nw v = 1 := by rw [hNwf _ hv, h0, pow_zero]
      have h2 : Ideal.absNorm (ws v).1.asIdeal = 1 := by rw [hNw _ hv, h1]
      rw [Ideal.absNorm_eq_one_iff] at h2
      exact (ws v).1.isPrime.ne_top h2
    · exact hpos
  have hu0v : ∀ (u : Kˣ) (v : HeightOneSpectrum (𝓞 K)), algebraMap K (v.adicCompletion K) (u : K) ≠ 0 := fun u v =>
    (map_ne_zero_iff _ (algebraMap K (v.adicCompletion K)).injective).mpr (Units.ne_zero u)
  have hu1v : ∀ (u : Kˣ), (u : K) ≠ 1 → ∀ v : HeightOneSpectrum (𝓞 K), algebraMap K (v.adicCompletion K) (u : K) ≠ 1 := fun u hu1 v h =>
    hu1 ((algebraMap K (v.adicCompletion K)).injective (by rw [h, map_one]))
  have hnrm : ∀ (u : Kˣ), (u : K) ≠ 1 → ∀ v : HeightOneSpectrum (𝓞 K), ((‖algebraMap K (v.adicCompletion K) (u : K) - 1‖ : ℝ) : ℂ) ≠ 0 := fun u hu1 v => by
    rw [Complex.ofReal_ne_zero, norm_ne_zero_iff]; exact sub_ne_zero.mpr (hu1v u hu1 v)

  let word : ∀ v : HeightOneSpectrum (𝓞 K), v ∈ T → (Fin 2 →₀ ℕ) → GL (Fin 2) (v.adicCompletion K) → ℂ :=
    fun v _ r x => ∑ ι : Fin (r 0) → Fin (nKs v),
      (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
        (((List.ofFn fun m => rKs v (ι m)).prod * zKs v ^ (r 1))⁻¹ * x)
  have hwordtest : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T) (r : Fin 2 →₀ ℕ),
      AutomorphicForm.IsLocalTestFn K v (word v hv r) := by
    intro v hv r
    exact AutomorphicForm.isLocalTestFn_sum_indicator_localIntegralSet_prod_mul_zpow_inv_mul K v (nKs v) (rKs v) (zKs v) (r 0) (r 1)
  have hwordcen : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T) (r : Fin 2 →₀ ℕ)
      (c : GL (Fin 2) (v.adicCompletion K)),
      (∃ ε : v.adicCompletion K, Valued.v ε = 1 ∧
        (c : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = ε • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) →
      ∀ y, word v hv r (c * y) = word v hv r y := by
    intro v hv r c hc y
    exact AutomorphicForm.sum_indicator_localIntegralSet_prod_mul_zpow_inv_mul_centralUnit_mul K v (nKs v) (rKs v) (zKs v) (r 0) (r 1) c hc y

  let zhat : HeightOneSpectrum (𝓞 K) → ℤ → (AdeleRing (𝓞 K) K)ˣ := fun v e =>
    if hv : v ∈ T then
      Units.map (finIncl (𝓞 K) K : FiniteAdeleRing (𝓞 K) K →* AdeleRing (𝓞 K) K)
        (localUnit (𝓞 K) K v ((Units.mk0 (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖKs v))
          (hϖKs0 v hv)) ^ e))
    else 1
  let tT : Kˣ → ∀ v : HeightOneSpectrum (𝓞 K), ℤ → GL (Fin 2) (v.adicCompletion K) := fun u v e =>
    AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K (zhat v e) * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))
  have htT : ∀ (u : Kˣ), ∀ v ∈ T, ∀ e : ℤ, (tT u v e : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      Matrix.diagonal ![(ϖKs v : v.adicCompletion K) ^ e * algebraMap K (v.adicCompletion K) (u : K),
        (ϖKs v : v.adicCompletion K) ^ e] := by
    intro u v hv e
    simp only [tT, zhat, dif_pos hv]
    rw [AutomorphicForm.coe_finComponent_glFin_centralScalar_localUnit_mul_diagUnits2]
    rw [Units.val_zpow_eq_zpow_val, Units.val_mk0]
    rfl
  have hreg : ∀ (u : Kˣ), (u : K) ≠ 1 → ∀ v ∈ T, ∀ e : ℤ, AutomorphicForm.IsRegularSemisimple (tT u v e) := by
    intro u hu1 v hv e
    rw [AutomorphicForm.isRegularSemisimple_iff_ne_zero, htT u v hv e, Matrix.trace_fin_two, Matrix.det_fin_two]
    simp only [Matrix.diagonal_apply_eq, ne_eq, Matrix.diagonal_apply_ne _ (show (0 : Fin 2) ≠ 1 by decide),
      Matrix.diagonal_apply_ne _ (show (1 : Fin 2) ≠ 0 by decide), Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]
    have hϖ : (ϖKs v : v.adicCompletion K) ≠ 0 := hϖKs0 v hv
    rw [show ((ϖKs v : v.adicCompletion K) ^ e * algebraMap K (v.adicCompletion K) (u : K) +
        (ϖKs v : v.adicCompletion K) ^ e) ^ 2 -
        4 * ((ϖKs v : v.adicCompletion K) ^ e * algebraMap K (v.adicCompletion K) (u : K) *
          (ϖKs v : v.adicCompletion K) ^ e - 0 * 0) =
        ((ϖKs v : v.adicCompletion K) ^ e * (algebraMap K (v.adicCompletion K) (u : K) - 1)) ^ 2 by ring]
    exact pow_ne_zero 2 (mul_ne_zero (zpow_ne_zero e hϖ) (sub_ne_zero.mpr (hu1v u hu1 v)))
  let τT : ∀ (u : Kˣ) (v : HeightOneSpectrum (𝓞 K)) (e : ℤ),
      @Measure (AutomorphicForm.localCentralizer K v (tT u v e)) (AutomorphicForm.localCentralizerBorel K v (tT u v e)) :=
    fun u v e => τF u (zhat v e) v
  have hτT : ∀ (u : Kˣ), (u : K) ≠ 1 → ∀ v e, @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v (tT u v e)) (τT u v e) :=
    fun u hu1 v e => hτF u (zhat v e) v hu1
  have hτT1 : ∀ (u : Kˣ), (u : K) ≠ 1 → ∀ v e, τT u v e (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1 :=
    fun u hu1 v e => hτF1 u (zhat v e) v hu1

  have hITex : ∀ (u : Kˣ) (hu1 : (u : K) ≠ 1) (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T) (r : Fin 2 →₀ ℕ) (e : ℤ),
      ∃ I : ℂ, AutomorphicForm.IsOrbitalIntegral K v (tT u v e) (τT u v e) (word v hv r) I :=
    fun u hu1 v hv r e => @AutomorphicForm.exists_isOrbitalIntegral_of_isRegularSemisimple_of_isLocalTestFn K _ _ v
      (tT u v e) (hreg u hu1 v hv e) (τT u v e) (hτT u hu1 v e) (word v hv r) (hwordtest v hv r)
  choose ITr hITr using hITex

  have hord : ∀ (u : Kˣ), ∀ v ∈ T, ‖algebraMap K (v.adicCompletion K) (u : K)‖ = ‖(ϖKs v : v.adicCompletion K)‖ ^ NumberField.Idele.ord K v (ι u) := by
    intro u v hv
    exact NumberField.Idele.norm_algebraMap_adicCompletion_eq_norm_uniformizer_zpow_ord K v (ϖKs v) (hϖKi v hv) u

  have hK2 : ∀ (u : Kˣ) (hu1 : (u : K) ≠ 1), ∀ ξ ∈ Ξ, ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
      ∑ r ∈ (AutomorphicForm.SatakeCombination.slotWord K L ws v (ks v) (js v)).support,
        AutomorphicForm.SatakeCombination.slotCoeff K L ws v (ks v) (js v) r *
          ∑' e : ℤ, ((ξ ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ e * ITr u hu1 v hv r e = ((‖algebraMap K (v.adicCompletion K) (u : K) - 1‖ : ℝ) : ℂ)⁻¹ * (if (AutomorphicForm.SatakeCombination.slotDeg K L ws v : ℤ) ∣ NumberField.Idele.ord K v (ι u) then
          ((Real.sqrt (Nw v : ℝ) : ℂ) * s v) ^ ks v * ζ v ^ js v *
              ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ ks v : LaurentPolynomial ℂ).coeff
                (NumberField.Idele.ord K v (ι u) / (AutomorphicForm.SatakeCombination.slotDeg K L ws v : ℤ)) *
            (((Real.sqrt (Nw v : ℝ) : ℂ) * s v) ^
              (-(NumberField.Idele.ord K v (ι u) / (AutomorphicForm.SatakeCombination.slotDeg K L ws v : ℤ))))
        else 0) := by
    intro u hu1 ξ hξ v hv
    exact (AutomorphicForm.sum_slotCoeff_mul_tsum_pow_mul_eq_inv_norm_sub_one_mul_ite_of_isOrbitalIntegral_heckeWord_diagonal_zpow
      K L ws v (ks v) (js v) (hfdv v hv) (Nw v) (hNw v hv) (hNwf v hv) (ζ v) (s v) ((ξ ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) (hζ v hv) (hs v hv)
      (hx ξ hξ v hv) (ϖKs v) (hϖKi v hv) (hϖKs0 v hv) (nKs v) (rKs v) (hrKs v hv) (zKs v) (hzKs v hv)
      (algebraMap K (v.adicCompletion K) (u : K)) (hu0v u v) (hu1v u hu1 v) (NumberField.Idele.ord K v (ι u)) (hord u v hv) (tT u v) (htT u v hv) (τT u v) (hτT u hu1 v)
      (hτT1 u hu1 v) (ITr u hu1 v hv) (fun r _ e => hITr u hu1 v hv r e)).2
  have hK2s : ∀ (u : Kˣ) (hu1 : (u : K) ≠ 1), ∀ ξ ∈ Ξ, ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
      ∀ r ∈ (AutomorphicForm.SatakeCombination.slotWord K L ws v (ks v) (js v)).support,
        Summable fun e : ℤ => ‖((ξ ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ e * ITr u hu1 v hv r e‖ := by
    intro u hu1 ξ hξ v hv
    exact (AutomorphicForm.sum_slotCoeff_mul_tsum_pow_mul_eq_inv_norm_sub_one_mul_ite_of_isOrbitalIntegral_heckeWord_diagonal_zpow
      K L ws v (ks v) (js v) (hfdv v hv) (Nw v) (hNw v hv) (hNwf v hv) (ζ v) (s v) ((ξ ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) (hζ v hv) (hs v hv)
      (hx ξ hξ v hv) (ϖKs v) (hϖKi v hv) (hϖKs0 v hv) (nKs v) (rKs v) (hrKs v hv) (zKs v) (hzKs v hv)
      (algebraMap K (v.adicCompletion K) (u : K)) (hu0v u v) (hu1v u hu1 v) (NumberField.Idele.ord K v (ι u)) (hord u v hv) (tT u v) (htT u v hv) (τT u v) (hτT u hu1 v)
      (hτT1 u hu1 v) (ITr u hu1 v hv) (fun r _ e => hITr u hu1 v hv r e)).1
  let fSm : (((u : HeightOneSpectrum (𝓞 K)) → u ∈ T → (Fin 2 →₀ ℕ))) →
      ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ :=
    fun m v => if hv : v ∈ T then fun x : GL (Fin 2) (v.adicCompletion K) =>
                ∑ ι : Fin ((m v hv) 0) → Fin (nKs v),
                  (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                    (((List.ofFn fun m => rKs v (ι m)).prod * zKs v ^ (m v hv) 1)⁻¹ * x)
      else fSK v
  have hcen : ∀ m, ∀ v ∈ T, ∀ c : GL (Fin 2) (v.adicCompletion K),
      (∃ ε : v.adicCompletion K, Valued.v ε = 1 ∧
        (c : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = ε • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) →
      ∀ y : GL (Fin 2) (v.adicCompletion K), fSm m v (c * y) = fSm m v y := by
    intro m v hv c hc y
    simp only [fSm, dif_pos hv]
    exact hwordcen v hv (m v hv) c hc y
  have hfU : ∀ m ∈ AutomorphicForm.SatakeCombination.slotIndex K L ws ks js T,
      ∃ ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ,
        AutomorphicForm.IsUnitFactorization K (SK ∪ T) (fam m) faK ff (fSm m) := by
    intro m hm
    obtain ⟨ff, hff, hprod, hzero, hfg⟩ := hfam m hm
    refine ⟨ff, hfaK, hff, ?_, hprod, hzero, hfg⟩
    intro v hv
    by_cases hvT : v ∈ T
    · simp only [fSm, dif_pos hvT]; exact hwordtest v hvT (m v hvT)
    · simp only [fSm, dif_neg hvT]
      rcases Finset.mem_union.mp hv with h | h
      · exact hfSK v h
      · exact absurd h hvT

  have hclass : ∀ γ ∈ ΔK,
      (∑ ξ ∈ Ξ, ∑ m ∈ AutomorphicForm.SatakeCombination.slotIndex K L ws ks js T,
        AutomorphicForm.SatakeCombination.slotFamilyCoeff K L ws ks js T m *
          ((κ₀K : ℂ) *
            (((κK : ℝ) : ℂ) *
              ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * IK m γ z ∂νZK))) =
      if ind (ratio γ) then A (ratio γ) * ((lat (ratio γ)).elim 0 fun n => g n * tw n) else 0 := by
    intro γ hγ
    obtain ⟨h10, h01, hne1⟩ := hΔK γ hγ
    have huval := hratio γ hγ

    generalize hudef : ratio γ = u at huval ⊢
    have hu1 : (u : K) ≠ 1 := by rw [huval]; exact hne1
    have hγ' : (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 ∧
        (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 = (u : K) := ⟨h10, h01, huval.symm⟩
    haveI hτKγ : (τK γ).IsHaarMeasure := hτK γ
    let IT : (((u : HeightOneSpectrum (𝓞 K)) → u ∈ T → (Fin 2 →₀ ℕ))) → HeightOneSpectrum (𝓞 K) → ℤ → ℂ :=
      fun m v e => if hv : v ∈ T then ITr u hu1 v hv (m v hv) e else 0
    have hIT : ∀ m, ∀ v ∈ T, ∀ e : ℤ, AutomorphicForm.IsOrbitalIntegral K v (tT u v e) (τT u v e) (fSm m v) (IT m v e) := by
      intro m v hv e
      simp only [fSm, IT, dif_pos hv]
      exact hITr u hu1 v hv (m v hv) e

    have hK1 : ∀ ξ ∈ Ξ, ∀ m ∈ AutomorphicForm.SatakeCombination.slotIndex K L ws ks js T,
        ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * IK m γ z ∂νZK =
        ((cG * cT⁻¹ * PZ.c : ℝ) : ℂ) *
          (if ∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK → v ∉ T → NumberField.Idele.ord K v (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) = 0
            then (1 : ℂ) else 0) *
          (if h1 : (u : K) - 1 ≠ 0 then
              ((NumberField.TateGlobal.ideleNorm K
                  (NumberField.Idele.partAt K SK (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (Units.mk0 ((u : K) - 1) h1))) : ℝ) : ℂ)
            else 0) *
          (∏ v ∈ T, ((‖algebraMap K (v.adicCompletion K) (u : K) - 1‖ : ℝ) : ℂ) *
              ∑' e : ℤ, ((ξ ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ e *
                IT m v e) *
          ∫ zS : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
              (IA u zS * ∏ v ∈ SK, IF u zS v) ∂PZ.νS := by
      intro ξ hξ m hm
      obtain ⟨ff, hf⟩ := hfU m hm
      exact AutomorphicForm.integral_mul_orbital_centralScalar_eq_mul_ideleNorm_mul_prod_tsum_mul_integral_of_isUnitFactorization_of_integrable
        K νZK ξ (hΞc ξ hξ) (hΞt ξ hξ) SK T hTS (hur ξ hξ) (fam m) faK ff (fSm m) hf (hcen m) γ u hu1 hγ' cτK hcτK
        (τK γ) (hτKc γ hγ) (IK m γ) (hIK m hm γ hγ) νA hνA cG hG (τG u) (fun z => hτG u z hu1) (fun z => hτGc u z hu1)
        (τA u) (fun z => hτA u z hu1) (τF u) (fun z v => hτF u z v hu1) (fun z v => hτF1 u z v hu1) cT hcT
        (fun z => hT u z hu1) PZ hPo hPp hPν (IA u) (fun z => hIA u z hu1) (IF u)
        (fun z v hv => by
          have hvT : v ∉ T := Finset.disjoint_right.mp hTS hv
          simp only [fSm, dif_neg hvT]
          exact hIF u z hu1 v hv)
        (AutomorphicForm.integrable_mul_orbital_mul_prod_orbital_sPart_of_isArchTestFactor_of_isLocalTestFn K νZK ξ
          (hΞc ξ hξ) SK u hu1 faK hfaK fSK hfSK cτK hcτK νA hνA (τG u) (fun z => hτG u z hu1) (fun z => hτGc u z hu1)
          (τA u) (fun z => hτA u z hu1) (τF u) (fun z v => hτF u z v hu1) (fun z v => hτF1 u z v hu1) cT hcT
          (fun z => hT u z hu1) PZ hPo hPp hPν (IA u) (fun z => hIA u z hu1) (IF u) (fun z v hv => hIF u z hu1 v hv))
        ϖKs hϖKi (tT u) (htT u) (τT u) (hτT u hu1) (hτT1 u hu1) (IT m) (hIT m)
        (fun v hv => by
          simp only [IT, dif_pos hv]
          exact hK2s u hu1 ξ hξ v hv (m v hv) (Finset.mem_pi.mp hm v hv))

    have hTfac : ∀ ξ ∈ Ξ, ∀ ITx : (((u : HeightOneSpectrum (𝓞 K)) → u ∈ T → (Fin 2 →₀ ℕ))) →
          HeightOneSpectrum (𝓞 K) → ℤ → ℂ, ITx = IT →
        ∑ m ∈ AutomorphicForm.SatakeCombination.slotIndex K L ws ks js T,
          AutomorphicForm.SatakeCombination.slotFamilyCoeff K L ws ks js T m *
            (∏ v ∈ T, ((‖algebraMap K (v.adicCompletion K) (u : K) - 1‖ : ℝ) : ℂ) * ∑' e : ℤ, ((ξ ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ e * ITx m v e) =
        (lat u).elim 0 fun n => g n * tw n := by
      intro ξ hξ ITx hITx
      subst hITx

      let Fr : HeightOneSpectrum (𝓞 K) → (Fin 2 →₀ ℕ) → ℂ := fun v r =>
        ((‖algebraMap K (v.adicCompletion K) (u : K) - 1‖ : ℝ) : ℂ) * ∑' e : ℤ, ((ξ ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ e * (if hv : v ∈ T then ITr u hu1 v hv r e else 0)
      have e1 : ∀ m ∈ AutomorphicForm.SatakeCombination.slotIndex K L ws ks js T,
          AutomorphicForm.SatakeCombination.slotFamilyCoeff K L ws ks js T m *
            (∏ v ∈ T, ((‖algebraMap K (v.adicCompletion K) (u : K) - 1‖ : ℝ) : ℂ) * ∑' e : ℤ, ((ξ ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ e * IT m v e) =
          ∏ a ∈ T.attach, (AutomorphicForm.SatakeCombination.slotCoeff K L ws a.1 (ks a.1) (js a.1) (m a.1 a.2) *
            Fr a.1 (m a.1 a.2)) := by
        intro m _
        have hc : AutomorphicForm.SatakeCombination.slotFamilyCoeff K L ws ks js T m =
            ∏ a ∈ T.attach, AutomorphicForm.SatakeCombination.slotCoeff K L ws a.1 (ks a.1) (js a.1) (m a.1 a.2) := rfl
        rw [hc, Finset.prod_mul_distrib (s := T.attach)]
        refine congrArg₂ (· * ·) rfl ?_
        rw [← Finset.prod_attach T (fun v => ((‖algebraMap K (v.adicCompletion K) (u : K) - 1‖ : ℝ) : ℂ) * ∑' e : ℤ, ((ξ ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ e * IT m v e)]
        try (refine Finset.prod_congr rfl fun a _ => ?_; first | rfl | simp only [Fr, IT, dif_pos a.2])
      rw [Finset.sum_congr rfl e1]
      rw [show AutomorphicForm.SatakeCombination.slotIndex K L ws ks js T =
          T.pi (fun v => (AutomorphicForm.SatakeCombination.slotWord K L ws v (ks v) (js v)).support) from rfl]
      rw [← Finset.prod_sum T (fun v => (AutomorphicForm.SatakeCombination.slotWord K L ws v (ks v) (js v)).support)
        (fun a r => AutomorphicForm.SatakeCombination.slotCoeff K L ws a (ks a) (js a) r * Fr a r)]

      have e2 : ∀ v ∈ T, ∑ r ∈ (AutomorphicForm.SatakeCombination.slotWord K L ws v (ks v) (js v)).support,
          AutomorphicForm.SatakeCombination.slotCoeff K L ws v (ks v) (js v) r * Fr v r = (if (AutomorphicForm.SatakeCombination.slotDeg K L ws v : ℤ) ∣ NumberField.Idele.ord K v (ι u) then
            ((Real.sqrt (Nw v : ℝ) : ℂ) * s v) ^ ks v * ζ v ^ js v *
                ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ ks v : LaurentPolynomial ℂ).coeff
                  (NumberField.Idele.ord K v (ι u) / (AutomorphicForm.SatakeCombination.slotDeg K L ws v : ℤ)) *
              (((Real.sqrt (Nw v : ℝ) : ℂ) * s v) ^
                (-(NumberField.Idele.ord K v (ι u) / (AutomorphicForm.SatakeCombination.slotDeg K L ws v : ℤ))))
          else 0) := by
        intro v hv
        have h2 := hK2 u hu1 ξ hξ v hv
        have h3 : ∑ r ∈ (AutomorphicForm.SatakeCombination.slotWord K L ws v (ks v) (js v)).support,
            AutomorphicForm.SatakeCombination.slotCoeff K L ws v (ks v) (js v) r * Fr v r =
            ((‖algebraMap K (v.adicCompletion K) (u : K) - 1‖ : ℝ) : ℂ) * ∑ r ∈ (AutomorphicForm.SatakeCombination.slotWord K L ws v (ks v) (js v)).support,
              AutomorphicForm.SatakeCombination.slotCoeff K L ws v (ks v) (js v) r *
                ∑' e : ℤ, ((ξ ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ e * ITr u hu1 v hv r e := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun r _ => ?_
          simp only [Fr, dif_pos hv]
          ring
        rw [h3, h2, ← mul_assoc, mul_inv_cancel₀ (hnrm u hu1 v), one_mul]
      rw [Finset.prod_congr rfl e2]

      rw [← Finset.prod_coe_sort T, Fintype.prod_equiv T.equivFin (fun x : ↥T => (if (AutomorphicForm.SatakeCombination.slotDeg K L ws (x : HeightOneSpectrum (𝓞 K)) : ℤ) ∣ NumberField.Idele.ord K (x : HeightOneSpectrum (𝓞 K)) (ι u) then
            ((Real.sqrt (Nw (x : HeightOneSpectrum (𝓞 K)) : ℝ) : ℂ) * s (x : HeightOneSpectrum (𝓞 K))) ^ ks (x : HeightOneSpectrum (𝓞 K)) * ζ (x : HeightOneSpectrum (𝓞 K)) ^ js (x : HeightOneSpectrum (𝓞 K)) *
                ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ ks (x : HeightOneSpectrum (𝓞 K)) : LaurentPolynomial ℂ).coeff
                  (NumberField.Idele.ord K (x : HeightOneSpectrum (𝓞 K)) (ι u) / (AutomorphicForm.SatakeCombination.slotDeg K L ws (x : HeightOneSpectrum (𝓞 K)) : ℤ)) *
              (((Real.sqrt (Nw (x : HeightOneSpectrum (𝓞 K)) : ℝ) : ℂ) * s (x : HeightOneSpectrum (𝓞 K))) ^
                (-(NumberField.Idele.ord K (x : HeightOneSpectrum (𝓞 K)) (ι u) / (AutomorphicForm.SatakeCombination.slotDeg K L ws (x : HeightOneSpectrum (𝓞 K)) : ℤ))))
          else 0)) (fun i => (if (AutomorphicForm.SatakeCombination.slotDeg K L ws (vI i) : ℤ) ∣ NumberField.Idele.ord K (vI i) (ι u) then
            ((Real.sqrt (Nw (vI i) : ℝ) : ℂ) * s (vI i)) ^ ks (vI i) * ζ (vI i) ^ js (vI i) *
                ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ ks (vI i) : LaurentPolynomial ℂ).coeff
                  (NumberField.Idele.ord K (vI i) (ι u) / (AutomorphicForm.SatakeCombination.slotDeg K L ws (vI i) : ℤ)) *
              (((Real.sqrt (Nw (vI i) : ℝ) : ℂ) * s (vI i)) ^
                (-(NumberField.Idele.ord K (vI i) (ι u) / (AutomorphicForm.SatakeCombination.slotDeg K L ws (vI i) : ℤ))))
          else 0))
        (fun x => by simp only [vI, Equiv.symm_apply_apply])]
      by_cases hall : ∀ i : Fin T.card, (fd i : ℤ) ∣ ordi u i
      · have hl : lat u = some (fun i => ordi u i / (fd i : ℤ)) := by simp only [lat, if_pos hall]
        rw [hl, Option.elim_some]
        simp only [g, tw, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        have hi := hall i
        simp only [fd, ordi, vI] at hi
        rw [if_pos hi]
      · have hl : lat u = none := by simp only [lat, if_neg hall]
        rw [hl, Option.elim_none]
        push Not at hall
        obtain ⟨i, hi⟩ := hall
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp only [fd, ordi, vI] at hi
        rw [if_neg hi]

    have hind_iff : (∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK → v ∉ T → NumberField.Idele.ord K v (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) = 0) ↔ ind u := Iff.rfl
    by_cases hind : ind u
    · rw [if_pos hind]
      have e3 : ∀ ξ ∈ Ξ, ∑ m ∈ AutomorphicForm.SatakeCombination.slotIndex K L ws ks js T,
          AutomorphicForm.SatakeCombination.slotFamilyCoeff K L ws ks js T m *
            ((κ₀K : ℂ) *
              (((κK : ℝ) : ℂ) *
                ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * IK m γ z ∂νZK)) =
          ((κ₀K : ℂ) * (((κK : ℝ) : ℂ) * (((cG * cT⁻¹ * PZ.c : ℝ) : ℂ) * (if h1 : (u : K) - 1 ≠ 0 then
              ((NumberField.TateGlobal.ideleNorm K
                  (NumberField.Idele.partAt K SK (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (Units.mk0 ((u : K) - 1) h1))) : ℝ) : ℂ)
            else 0) * (∫ zS : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
              (IA u zS * ∏ v ∈ SK, IF u zS v) ∂PZ.νS)))) *
            ((lat u).elim 0 fun n => g n * tw n) := by
        intro ξ hξ
        rw [← hTfac ξ hξ IT rfl, Finset.mul_sum]
        refine Finset.sum_congr rfl fun m hm => ?_
        rw [hK1 ξ hξ m hm, if_pos (hind_iff.mpr hind)]
        ring
      rw [Finset.sum_congr rfl e3, ← Finset.sum_mul]
      congr 1
      simp only [A, Cst, W, disc, ι, Finset.mul_sum]
      refine Finset.sum_congr rfl fun ξ _ => ?_
      ring
    · rw [if_neg hind]
      apply Finset.sum_eq_zero
      intro ξ hξ
      apply Finset.sum_eq_zero
      intro m hm
      rw [hK1 ξ hξ m hm, if_neg (fun h => hind (hind_iff.mp h))]
      simp

  have hout : ∀ u, P u → ∀ n, lat u = some n → u ∉ Δ → g n * A u = 0 := by
    intro u hPu n hlat hnot
    obtain ⟨hu1, hind⟩ := hPu

    have hnotratio : ∀ γ ∈ ΔK,
        (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ (u : K) := by
      intro γ hγ h
      apply hnot
      simp only [Δ, Finset.mem_filter, Finset.mem_image]
      refine ⟨⟨γ, hγ, Units.ext ?_⟩, hind⟩
      rw [hratio γ hγ, h]
    by_cases hg : g n = 0
    · rw [hg, zero_mul]
    ·
      suffices hW : W u = 0 by
        simp only [A, hW, mul_zero]

      by_cases hΞ : Ξ = ∅
      · simp only [W, hΞ, Finset.sum_empty]
      ·

        obtain ⟨ξ, hξ⟩ := Finset.nonempty_of_ne_empty hΞ

        have hlat' : (∀ i, (fd i : ℤ) ∣ ordi u i) ∧ (fun i => ordi u i / (fd i : ℤ)) = n := by
          simp only [lat] at hlat
          split_ifs at hlat with h
          exact ⟨h, Option.some_injective _ hlat⟩

        have hloc : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
            ∃ r ∈ (AutomorphicForm.SatakeCombination.slotWord K L ws v (ks v) (js v)).support, ∃ e : ℤ,
              ITr u hu1 v hv r e ≠ 0 := by
          intro v hv
          have h2 := hK2 u hu1 ξ hξ v hv
          set i : Fin T.card := T.equivFin ⟨v, hv⟩ with hi
          have hvi : vI i = v := by simp [vI, hi]
          have hdiv : (AutomorphicForm.SatakeCombination.slotDeg K L ws v : ℤ) ∣ NumberField.Idele.ord K v (ι u) := by
            have := hlat'.1 i
            simp only [fd, ordi] at this
            rwa [hvi] at this
          have hni : NumberField.Idele.ord K v (ι u) / (AutomorphicForm.SatakeCombination.slotDeg K L ws v : ℤ) = n i := by
            have := congr_fun hlat'.2 i
            simp only [fd, ordi] at this
            rwa [hvi] at this
          have hgi := (Finset.prod_ne_zero_iff.mp hg) i (Finset.mem_univ i)
          rw [hvi, ← hni] at hgi
          have hsv : s v ≠ 0 := fun h0 => hζ v hv (by rw [← hs v hv, h0]; ring)
          have hNw : (Real.sqrt (Nw v : ℝ) : ℂ) ≠ 0 := by
            rw [Complex.ofReal_ne_zero, Real.sqrt_ne_zero']
            have : 0 < Nw v := by
              rw [hNwf v hv]
              exact pow_pos (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)) _
            exact_mod_cast this
          have hR : ((‖algebraMap K (v.adicCompletion K) (u : K) - 1‖ : ℝ) : ℂ)⁻¹ * (if (AutomorphicForm.SatakeCombination.slotDeg K L ws v : ℤ) ∣ NumberField.Idele.ord K v (ι u) then
            ((Real.sqrt (Nw v : ℝ) : ℂ) * s v) ^ ks v * ζ v ^ js v *
                ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ ks v : LaurentPolynomial ℂ).coeff
                  (NumberField.Idele.ord K v (ι u) / (AutomorphicForm.SatakeCombination.slotDeg K L ws v : ℤ)) *
              (((Real.sqrt (Nw v : ℝ) : ℂ) * s v) ^
                (-(NumberField.Idele.ord K v (ι u) / (AutomorphicForm.SatakeCombination.slotDeg K L ws v : ℤ))))
          else 0) ≠ 0 := by
            refine mul_ne_zero (inv_ne_zero (hnrm u hu1 v)) ?_
            rw [if_pos hdiv]
            exact mul_ne_zero hgi (zpow_ne_zero _ (mul_ne_zero hNw hsv))
          rw [← h2] at hR
          obtain ⟨r, hr, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hR
          refine ⟨r, hr, ?_⟩
          by_contra hall
          push Not at hall
          apply hne
          have hz : (fun e : ℤ => ((ξ ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ e * ITr u hu1 v hv r e) = fun _ => 0 := by
            funext e; rw [hall e, mul_zero]
          rw [hz, tsum_zero, mul_zero]

        choose rsel hrsel esel hesel using hloc
        have hm : (fun v hv => rsel v hv) ∈ AutomorphicForm.SatakeCombination.slotIndex K L ws ks js T :=
          Finset.mem_pi.mpr hrsel

        have hwin : ∀ zS : (AdeleRing (𝓞 K) K)ˣ, IA u zS * ∏ v ∈ SK, IF u zS v = 0 := by
          intro zS
          obtain ⟨ff, hf⟩ := hfU _ hm
          let eT : HeightOneSpectrum (𝓞 K) → ℤ := fun v => if hv : v ∈ T then esel v hv else 0
          have heT : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T), eT v = esel v hv := fun v hv => dif_pos hv
          exact AutomorphicForm.mul_prod_orbital_eq_zero_of_forall_apply_conj_centralScalar_mul_diagUnits2_eq_zero
            K νZK SK T hTS u hu1 hind (fam fun v hv => rsel v hv) faK ff (fSm fun v hv => rsel v hv) hf
            (hcen fun v hv => rsel v hv) (hΔKc _ hm u hu1 hnotratio) cτK hcτK νA hνA cG hG
            (τG u) (fun z => hτG u z hu1) (fun z => hτGc u z hu1) (τA u) (fun z => hτA u z hu1) (τF u)
            (fun z v => hτF u z v hu1) (fun z v => hτF1 u z v hu1) cT hcT (fun z => hT u z hu1)
            (IA u) (fun z => hIA u z hu1) (IF u)
            (fun z v hv => by
              have hvT : v ∉ T := Finset.disjoint_right.mp hTS hv
              simp only [fSm, dif_neg hvT]
              exact hIF u z hu1 v hv)
            ϖKs hϖKi eT (fun v => tT u v (eT v)) (fun v hv => htT u v hv (eT v))
            (fun v hv => ⟨τT u v (eT v), ITr u hu1 v hv (rsel v hv) (eT v), hτT u hu1 v (eT v), hτT1 u hu1 v (eT v),
              by simpa only [fSm, dif_pos hv] using hITr u hu1 v hv (rsel v hv) (eT v),
              by rw [heT v hv]; exact hesel v hv⟩)
            zS

        simp only [W]
        refine Finset.sum_eq_zero fun ξ _ => ?_
        refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun zS => ?_)
        simp only [hwin zS, mul_zero, Pi.zero_apply]

  have hbox : ∀ n, n ∉ box → g n = 0 := by
    intro n hn
    simp only [box, Fintype.mem_piFinset, not_forall] at hn
    obtain ⟨i, hi⟩ := hn
    simp only [g]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [AutomorphicForm.WindPack.T_add_T_inv_pow_apply_eq_zero _ _ ?_, mul_zero]
    rw [Finset.mem_Icc] at hi
    rcases abs_cases (n i) with ⟨h, _⟩ | ⟨h, _⟩ <;> omega

  have hΔP : ∀ u ∈ Δ, P u := by
    intro u hu
    simp only [Δ, Finset.mem_filter, Finset.mem_image] at hu
    obtain ⟨⟨γ, hγ, rfl⟩, hind⟩ := hu
    refine ⟨?_, hind⟩
    rw [hratio γ hγ]
    exact (hΔK γ hγ).2.2

  have hL : (∑ ξ ∈ Ξ, ∑ m ∈ AutomorphicForm.SatakeCombination.slotIndex K L ws ks js T,
        AutomorphicForm.SatakeCombination.slotFamilyCoeff K L ws ks js T m *
          ∑ γ ∈ ΔK, (κ₀K : ℂ) *
            (((κK : ℝ) : ℂ) *
              ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * IK m γ z ∂νZK)) =
      ∑ u ∈ Δ, A u * ((lat u).elim 0 fun n => g n * tw n) := by

    simp_rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl fun ξ _ => Finset.sum_comm, Finset.sum_comm]
    rw [Finset.sum_congr rfl hclass]

    simp only [Δ]
    rw [Finset.sum_filter, Finset.sum_image hinj]

  have hfd : ∀ i, (fd i : ℤ) ≠ 0 := by
    intro i h0
    have h0' : fd i = 0 := by exact_mod_cast h0
    have hv : vI i ∈ T := (T.equivFin.symm i).2
    have h1 : Nw (vI i) = 1 := by rw [hNwf _ hv]; simp only [fd] at h0'; rw [h0', pow_zero]
    have h2 : Ideal.absNorm (ws (vI i)).1.asIdeal = 1 := by rw [hNw _ hv, h1]
    rw [Ideal.absNorm_eq_one_iff] at h2
    exact (ws (vI i)).1.isPrime.ne_top h2
  have hR : (∑ n ∈ box, g n * 𝒜.coeff n) = ∑ n ∈ box, g n * ∑ᶠ u ∈ {u | P u ∧ lat u = some n}, A u * tw n := by
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [h𝒜 n]
    congr 1
    rw [mul_finsum_mem]
    refine finsum_mem_congr ?_ fun u _ => ?_
    · ext u
      simp only [Set.mem_setOf_eq, P, lat, ind, ordi, fd, vI, ι]
      constructor
      · rintro ⟨h1, h2, h3⟩
        refine ⟨⟨h1, h2⟩, ?_⟩
        rw [if_pos (fun i => ⟨n i, h3 i⟩)]
        congr 1
        funext i
        rw [h3 i, Int.mul_ediv_cancel_left _ (hfd i)]
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨h1, h2, fun i => ?_⟩
        split_ifs at h3 with h4
        have h5 := congr_fun (Option.some_injective _ h3) i
        obtain ⟨q, hq⟩ := h4 i
        rw [hq] at h5 ⊢
        rw [Int.mul_ediv_cancel_left _ (hfd i)] at h5
        rw [h5]
    · simp only [A, Cst, tw, disc, W, ι, vI]
      ring
  have hmid := AutomorphicForm.WindPack.sum_mul_elim_eq_sum_mul_finsum_mem Δ box A g tw P lat hΔP hout hbox
  show _ = ∑ n ∈ box, g n * 𝒜.coeff n
  rw [hL, hmid, hR]

end S_AutomorphicForm_sum_slotFamilyCoeff_mul_sum_mul_integral_orbital_eq_sum_prod_mul_windingDatum_coeff_of_forall_coeff_eq_of_smul_eq_map_partAt_of_ne_one_unweighted
end P2MW
export P2MW.S_AutomorphicForm_sum_slotFamilyCoeff_mul_sum_mul_integral_orbital_eq_sum_prod_mul_windingDatum_coeff_of_forall_coeff_eq_of_smul_eq_map_partAt_of_ne_one_unweighted (solution)
