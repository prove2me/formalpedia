-- Prove2me | solution 1 for AutomorphicForm.table_mem_box_of_mem_cuspClasses_siegel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/5af78526-3a37-55dc-a920-befb938de791

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_LocalLanglands_IntegralSubgroupOpen
import Definitions.Def_LocalLanglands_HeckePair
import Definitions.Def_DedekindDomain_IntegralClosure
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_FnTwist
import Definitions.Def_Mathlib_LinearAlgebra_Countable
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TwistedGeometricRemainder
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_AutomorphicForm_PeterssonIntegral
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Theorems.Thm_AutomorphicForm_exists_mem_cuspClasses_levelOne_of_mem_cuspClasses_principalLevel
import Theorems.Thm_NumberField_TateGlobal_exists_norm_apply_eq_ideleNorm_rpow
import Theorems.Thm_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc
import Theorems.Thm_AutomorphicForm_exists_sesqForm_eq_peterssonIntegral_of_isGenuineCuspRealizationAt_of_isFundamentalDomain
import Theorems.Thm_AutomorphicForm_a_mul_conj_b_eq_and_norm_b_eq_of_sesqForm_covariant_of_ne_zero
import Theorems.Thm_AutomorphicForm_HeckeEigensystem_conj_eq_mul_div_and_conj_eq_sq_mul_inv_of_mul_conj_eq_of_norm_eq
import Theorems.Thm_AutomorphicForm_isIdeleClassChar_and_continuous_of_isLsXiFunction_of_continuous
import Theorems.Thm_LanglandsTunnell_satake_norm_lt_sqrt_absNorm_of_norm_b_eq_one
import Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_exists_twist_rpow_absNorm_exceptionalSet_eq_toFun_eq_ideleNorm_det_rpow_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_table_mem_box_of_mem_cuspClasses_siegel
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instSeparableSpaceAdicCompletionOfCountable_definitions LanglandsTunnell.isScalarTower_fixFldDetKer_fixFldQuatH_L LanglandsTunnell.isScalarTower_rat_fixFldSylowH_fixFldQuatH LanglandsTunnell.detKer_normal LanglandsTunnell.isScalarTower_rat_fixFldDetKer_fixFldQuatH LanglandsTunnell.algebra_fixFldDetKer_fixFldQuatH LanglandsTunnell.isScalarTower_fixFldSylowH_fixFldQuatH_L LanglandsTunnell.algebra_fixFldSylowH_fixFldQuatH LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain MeasureTheory NumberField.AdelicHaar AutomorphicForm NumberField.TateGlobal AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering LocalGL2
open scoped TensorProduct Pointwise TensorProduct.RightActions ComplexConjugate BigOperators NumberField NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace BoxK

theorem b_eq (K : Type) [Field K] [NumberField K]
    (cK uK d₁K d₂K : ℝ) (TK : Finset (AdelicGL2 (𝓞 K) K))
    (hcK : 0 < cK) (hd₁K : 0 < d₁K) (hdK : d₁K < d₂K)
    (hcovK : CoversModCentre K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (N'' : Ideal (𝓞 K)) (hN'' : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N'' → v ∈ SK)
    (π'' : HeckeEigensystem K ℂ)
    (hπ'' : π'' ∈ cuspClasses K
      (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
          (fun M => levelOne (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξK N'' SK)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ SK) :
    π''.b v = HeckeEigensystem.cNorm v *
      ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) := by
  classical
  obtain ⟨φ, hφ, h0⟩ := AutomorphicForm.exists_isIsotypicCuspFormAt_ne_zero_of_mem_cuspClasses hπ''
  obtain ⟨g₀, hg₀⟩ := Function.ne_iff.mp h0
  have hls : IsLsXiFunction (𝓞 K) K ⊤ ξK φ :=
    ((lsXiMemberAt_iff (𝓞 K) K _ _ _ _ φ).mp hφ.smoothCusp.1.1).1
  have h1 := hφ.central_eigen v hv g₀
  have h2 := hls.central_transform ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ g₀
  have h3 : π''.toRawCentral.b v * φ g₀ =
      ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) * φ g₀ :=
    h1.symm.trans h2
  rw [HeckeEigensystem.toRawCentral_b] at h3
  have h4 := mul_right_cancel₀ hg₀ h3
  rw [← h4, ← mul_assoc, mul_inv_cancel₀ (HeckeEigensystem.cNorm_ne_zero v), one_mul]

theorem conj_a_eq (K : Type) [Field K] [NumberField K]
    (cK uK d₁K d₂K : ℝ) (TK : Finset (AdelicGL2 (𝓞 K) K))
    (hcK : 0 < cK) (hd₁K : 0 < d₁K) (hdK : d₁K < d₂K)
    (hcovK : CoversModCentre K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (N'' : Ideal (𝓞 K)) (hN'' : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N'' → v ∈ SK)
    (π'' : HeckeEigensystem K ℂ)
    (hπ'' : π'' ∈ cuspClasses K
      (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
          (fun M => levelOne (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξK N'' SK)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ SK) :
    conj (π''.a v) = conj (π''.b v) / ((‖π''.b v‖ : ℝ) : ℂ) * π''.a v := by
  classical
  have hlev : π''.level = N'' := hπ''.1
  subst hlev
  obtain ⟨φ, hφ, h0⟩ := AutomorphicForm.exists_isIsotypicCuspFormAt_ne_zero_of_mem_cuspClasses hπ''
  have hne' : ∃ g, φ g ≠ 0 := Function.ne_iff.mp h0
  have hls : IsLsXiFunction (𝓞 K) K ⊤ ξK φ :=
    ((lsXiMemberAt_iff (𝓞 K) K _ _ _ _ φ).mp hφ.smoothCusp.1.1).1
  set R' := hφ.toRealization h0 with hR'def
  have hR'gen : IsGenuineCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
      (fun M => levelOne (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
      π''.toRawCentral R' := by
    show Continuous R'.toFun
    exact hφ.continuous

  obtain ⟨hcls, hcont⟩ :=
    AutomorphicForm.isIdeleClassChar_and_continuous_of_isLsXiFunction_of_continuous K ξK φ hls hφ.continuous hne'
  set μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ :=
    ξK.comp (Subgroup.topEquiv : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) ≃* (AdeleRing (𝓞 K) K)ˣ).symm.toMonoidHom with hμdef
  have hμ : ∀ x, μ x = ξK ⟨x, Subgroup.mem_top x⟩ := fun x => rfl
  obtain ⟨s, hs⟩ := NumberField.TateGlobal.exists_norm_apply_eq_ideleNorm_rpow K μ (fun u => hcls u) hcont

  obtain ⟨S, hSs, hS⟩ := AutomorphicForm.exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc K 1 2
  obtain ⟨-, hself, himp⟩ :=
    AutomorphicForm.exists_sesqForm_eq_peterssonIntegral_of_isGenuineCuspRealizationAt_of_isFundamentalDomain K cK uK d₁K d₂K
      TK hdK hcovK π'' π'' R' R' hR'gen s (fun x => hs x) 1 2 one_pos one_lt_two S hSs hS
  obtain ⟨-, P, hP, -, hPeq⟩ := himp rfl
  have hmem : R'.toFun ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 K) K => fun z => R'.toFun (z * h)) :=
    Submodule.subset_span ⟨1, funext fun z => congrArg R'.toFun (mul_one z)⟩
  have hself' : P R'.toFun R'.toFun ≠ 0 := by
    rw [hPeq _ _ (Submodule.mem_sup_right hmem) hmem]; exact hself
  obtain ⟨h1, h2⟩ :=
    AutomorphicForm.a_mul_conj_b_eq_and_norm_b_eq_of_sesqForm_covariant_of_ne_zero K _ π'' R' P s
      (fun g x y hx hy => hP g x y (Submodule.mem_sup_right hx) hy) hself' v hv (fun hdvd => hv (hN'' v hdvd))

  have hN0 : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot))
  have hc : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (1 - s) := Real.rpow_pos_of_pos hN0 _
  obtain ⟨hca, hcb⟩ :=
    AutomorphicForm.HeckeEigensystem.conj_eq_mul_div_and_conj_eq_sq_mul_inv_of_mul_conj_eq_of_norm_eq (π''.a v) (π''.b v)
      _ hc h1 h2
  have hb0 : π''.b v ≠ 0 := by
    intro h
    rw [h, norm_zero] at h2
    exact hc.ne' h2.symm
  have hc0 : ((((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (1 - s) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  rw [h2, hcb, hca]
  field_simp

end BoxK

namespace BoxK

theorem add_inv_le_add_inv {x s : ℝ} (hx : 0 < x) (hxs : x < s) (hsx : x⁻¹ < s) : x + x⁻¹ ≤ s + s⁻¹ := by
  have hs : 0 < s := hx.trans hxs
  have h1 : 1 < s * x := by
    have := (inv_lt_iff_one_lt_mul₀ hx).mp hsx
    linarith [this]
  rw [← sub_nonneg]
  have e : s + s⁻¹ - (x + x⁻¹) = (s - x) * (s * x - 1) / (s * x) := by
    field_simp
    ring
  rw [e]
  exact div_nonneg (mul_nonneg (sub_nonneg.mpr hxs.le) (sub_nonneg.mpr h1.le)) (mul_pos hs hx).le

theorem norm_a_le
    (K : Type) [Field K] [NumberField K] (cK uK d₁K d₂K : ℝ) (TK : Finset (AdelicGL2 (𝓞 K) K))
    (hcK : 0 < cK) (hd₁K : 0 < d₁K) (hdK : d₁K < d₂K)
    (hcovK : CoversModCentre K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (SK : Finset (HeightOneSpectrum (𝓞 K))) (N'' : Ideal (𝓞 K))
    (hN'' : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N'' → v ∈ SK)
    (π'' : HeckeEigensystem K ℂ)
    (hπ'' : π'' ∈ cuspClasses K
      (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
          (fun M => levelOne (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξK N'' SK)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ SK)
    (hb : π''.b v = HeckeEigensystem.cNorm v *
      ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ)) :
    ‖π''.a v‖ ≤ ((Ideal.absNorm v.asIdeal : ℝ) + 1) *
      Real.sqrt ‖((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ)‖ := by
  classical

  have hlev : π''.level = N'' := hπ''.1
  subst hlev

  obtain ⟨φ, hφ, h0⟩ := AutomorphicForm.exists_isIsotypicCuspFormAt_ne_zero_of_mem_cuspClasses hπ''
  set R := hφ.toRealization h0 with hRdef
  have hRgen : IsGenuineCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
        (fun M => levelOne (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
      π''.toRawCentral R := by
    show Continuous R.toFun
    exact hφ.continuous

  set Nr : ℝ := (Ideal.absNorm v.asIdeal : ℝ) with hNr
  set ξv : ℂ := ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) with hξv
  set r : ℝ := ‖π''.b v‖ with hr
  have hN2 : 2 ≤ Ideal.absNorm v.asIdeal := by
    have h0' : Ideal.absNorm v.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot
    have h1' : Ideal.absNorm v.asIdeal ≠ 1 := Ideal.absNorm_eq_one_iff.not.mpr v.isPrime.ne_top
    omega
  have hN1 : (1 : ℝ) < Nr := by rw [hNr]; exact_mod_cast hN2
  have hN0 : (0 : ℝ) < Nr := one_pos.trans hN1
  have hξ0 : 0 < ‖ξv‖ := norm_pos_iff.mpr (Units.ne_zero _)
  have hrNξ : r = Nr * ‖ξv‖ := by
    rw [hr, hb, norm_mul, hξv]
    congr 1
    rw [HeckeEigensystem.cNorm, Complex.norm_natCast]
  have hr0 : 0 < r := by rw [hrNξ]; exact mul_pos hN0 hξ0

  set t : ℝ := Real.logb Nr r / 2 with ht
  set c : ℝ := Nr ^ (-t) with hc
  have hc0 : 0 < c := Real.rpow_pos_of_pos hN0 _
  have hc2 : c ^ 2 * r = 1 := by
    have e1 : c ^ 2 = Nr ^ (-(Real.logb Nr r)) := by
      rw [hc, sq, ← Real.rpow_add hN0]
      congr 1
      rw [ht]; ring
    rw [e1, Real.rpow_neg hN0.le, Real.rpow_logb hN0 hN1.ne' hr0, inv_mul_cancel₀ hr0.ne']
  have hcs : c * Real.sqrt r = 1 := by
    have hpos : 0 < c * Real.sqrt r := mul_pos hc0 (Real.sqrt_pos.mpr hr0)
    have hsq : (c * Real.sqrt r) ^ 2 = 1 := by
      rw [mul_pow, Real.sq_sqrt hr0.le, hc2]
    rw [← Real.sqrt_sq hpos.le, hsq, Real.sqrt_one]

  obtain ⟨R', hR'gen, hexc, -⟩ :=
    AutomorphicForm.SmoothCuspRealizationAt.exists_twist_rpow_absNorm_exceptionalSet_eq_toFun_eq_ideleNorm_det_rpow_mul
      K cK uK d₁K d₂K TK hd₁K π'' R hRgen t
  have hexcl : v ∉ R'.exceptionalSet := by rw [hexc]; exact hv
  have hndvd : ¬ v.asIdeal ∣
      (π''.twist (fun w : HeightOneSpectrum (𝓞 K) => (((Ideal.absNorm w.asIdeal : ℝ) ^ (-t) : ℝ) : ℂ))).level :=
    fun h => hv (hN'' v h)
  have hb1 : ‖(π''.twist (fun w : HeightOneSpectrum (𝓞 K) => (((Ideal.absNorm w.asIdeal : ℝ) ^ (-t) : ℝ) : ℂ))).b v‖ = 1 := by
    rw [HeckeEigensystem.twist_b, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, ← hNr, ← hc,
      abs_of_pos hc0, ← hr, hc2]
  obtain ⟨-, α, β, hsum, hprod, hα, hβ⟩ :=
    LanglandsTunnell.satake_norm_lt_sqrt_absNorm_of_norm_b_eq_one K cK uK d₁K d₂K TK hcK hd₁K hdK hcovK
      (π''.twist (fun w : HeightOneSpectrum (𝓞 K) => (((Ideal.absNorm w.asIdeal : ℝ) ^ (-t) : ℝ) : ℂ))) R' hR'gen
      v hndvd hexcl hb1

  set s : ℝ := Real.sqrt Nr with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hN0
  have hs2 : s ^ 2 = Nr := Real.sq_sqrt hN0.le
  have hα' : ‖α‖ < s := by rw [hs, hNr]; exact_mod_cast hα
  have hβ' : ‖β‖ < s := by rw [hs, hNr]; exact_mod_cast hβ
  have hαβ : ‖α‖ * ‖β‖ = 1 := by rw [← norm_mul, hprod, hb1]
  have hx0 : 0 < ‖α‖ := by
    rcases (norm_nonneg α).lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h, zero_mul] at hαβ; exact zero_ne_one hαβ
  have hβinv : ‖β‖ = ‖α‖⁻¹ := (mul_eq_one_iff_eq_inv₀ hx0.ne').mp (by rw [mul_comm]; exact hαβ)
  have hsum' : ‖α + β‖ ≤ s + s⁻¹ := by
    calc ‖α + β‖ ≤ ‖α‖ + ‖β‖ := norm_add_le α β
      _ = ‖α‖ + ‖α‖⁻¹ := by rw [hβinv]
      _ ≤ s + s⁻¹ := add_inv_le_add_inv hx0 hα' (by rw [← hβinv]; exact hβ')

  have key : c * ‖π''.a v‖ ≤ s + s⁻¹ := by
    have e : ‖α + β‖ = c * ‖π''.a v‖ := by
      rw [hsum, HeckeEigensystem.twist_a, norm_mul, Complex.norm_real, Real.norm_eq_abs, ← hNr, ← hc, abs_of_pos hc0]
    rw [← e]; exact hsum'

  have hξr : ‖ξv‖ = r / Nr := by rw [hrNξ, mul_div_cancel_left₀ _ hN0.ne']
  have hsqrt : Real.sqrt ‖ξv‖ = Real.sqrt r / s := by rw [hξr, Real.sqrt_div hr0.le, hs]
  show ‖π''.a v‖ ≤ (Nr + 1) * Real.sqrt ‖ξv‖
  rw [hsqrt]
  have e2 : (Nr + 1) * (Real.sqrt r / s) = (s + s⁻¹) * Real.sqrt r := by
    rw [← hs2]; field_simp
  rw [e2]
  calc ‖π''.a v‖ = (c * ‖π''.a v‖) * Real.sqrt r := by
        rw [mul_comm c, mul_assoc, hcs, mul_one]
    _ ≤ (s + s⁻¹) * Real.sqrt r := mul_le_mul_of_nonneg_right key (Real.sqrt_nonneg r)

end BoxK

theorem solution
    (K : Type) [Field K] [NumberField K]
    (cK uK d₁K d₂K : ℝ) (TK : Finset (AdelicGL2 (𝓞 K) K))
    (hcK : 0 < cK) (hd₁K : 0 < d₁K) (hdK : d₁K < d₂K)
    (hcovK : CoversModCentre K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (N' : Ideal (𝓞 K)) (hN' : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N' → v ∈ SK)
    (π : HeckeEigensystem K ℂ)
    (hπ : π ∈ cuspClasses K
      (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
          (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξK N' SK) :
    (fun v : HeightOneSpectrum (𝓞 K) => (π.a v, π.b v)) ∈
      {x : HeightOneSpectrum (𝓞 K) → ℂ × ℂ |
        (∀ v ∈ SK, x v = 0) ∧
        ∀ v ∉ SK,
          (x v).2 = HeckeEigensystem.cNorm v *
              ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ∧
          ‖(x v).1‖ ≤ ((Ideal.absNorm v.asIdeal : ℝ) + 1) *
              Real.sqrt ‖((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ :
                ℂˣ) : ℂ)‖ ∧
          conj (x v).1 = conj (x v).2 / ((‖(x v).2‖ : ℝ) : ℂ) * (x v).1} := by
  classical
  obtain ⟨N'', π'', hN''0, hN'', hπ'', hagree⟩ :=
    AutomorphicForm.exists_mem_cuspClasses_levelOne_of_mem_cuspClasses_principalLevel K cK uK d₁K d₂K TK hcK hd₁K hdK
      hcovK SK ξK N' hN' π hπ
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · obtain ⟨-, hSv, -⟩ := hπ
    obtain ⟨ha, hb⟩ := hSv v hv
    exact Prod.ext ha hb
  · obtain ⟨ha, hb⟩ := hagree v hv
    show π.b v = _ ∧ ‖π.a v‖ ≤ _ ∧ conj (π.a v) = conj (π.b v) / ((‖π.b v‖ : ℝ) : ℂ) * (π.a v)
    rw [← ha, ← hb]
    have hb'' := BoxK.b_eq K cK uK d₁K d₂K TK hcK hd₁K hdK hcovK ξK hξc hξt SK N'' hN'' π'' hπ'' v hv
    exact ⟨hb'', BoxK.norm_a_le K cK uK d₁K d₂K TK hcK hd₁K hdK hcovK ξK hξc hξt SK N'' hN'' π'' hπ'' v hv hb'',
      BoxK.conj_a_eq K cK uK d₁K d₂K TK hcK hd₁K hdK hcovK ξK hξc hξt SK N'' hN'' π'' hπ'' v hv⟩

end S_AutomorphicForm_table_mem_box_of_mem_cuspClasses_siegel
end P2MW
export P2MW.S_AutomorphicForm_table_mem_box_of_mem_cuspClasses_siegel (solution)
