-- Prove2me | solution 1 for CuspForm.forall_exists_eq_mul_qExpansion_alSlash_of_mem_maximal_of_forall_unitsMap_of_even
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/72bcbcba-f4fe-5785-ab45-17bac0d6dc25

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Theorems.Thm_ModularForm_exists_not_dvd_and_forall_isIntegral_mul_qExpansion_alSlash_of_isIntegralQExp_of_even
import Theorems.Thm_ModularCurve_exists_sum_smul_eq_of_isIntegralQExp_gammaH
import Theorems.Thm_ModularForm_exists_GammaH_coe_eq_alSlash_of_forall_unitsMap_atkinLehnerFactor_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_forall_exists_eq_mul_qExpansion_alSlash_of_mem_maximal_of_forall_unitsMap_of_even
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.coe_heckeAlphaHBar ModularCurve.coe_heckeBetaHBarOf AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false

open scoped MatrixGroups ModularForm

section L1SatMinor

open Module Submodule

namespace SatMinor

theorem exists_cols_isUnit_det {K : Type*} [Field K] {ι : Type*} {s : ℕ}
    (B : Fin s → ι → K) (hB : LinearIndependent K B) :
    ∃ cols : Fin s → ι, IsUnit (Matrix.of fun j l => B j (cols l)).det := by
  classical
  let col : ι → (Fin s → K) := fun a j => B j a

  have hspan : span K (Set.range col) = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ0, hφ⟩ := (span K (Set.range col)).exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hne)
    have hcol : ∀ a, φ (col a) = 0 := fun a =>
      LinearMap.mem_ker.mp (hφ (subset_span ⟨a, rfl⟩))
    let bf := Pi.basisFun K (Fin s)
    have hrel : ∑ j, φ (bf j) • B j = 0 := by
      funext a
      rw [Finset.sum_apply, Pi.zero_apply]
      simp only [Pi.smul_apply, smul_eq_mul]
      have h := hcol a
      have hx : col a = ∑ j, (col a j) • bf j := by
        have := (bf.sum_repr (col a)).symm
        simpa only [bf, Pi.basisFun_repr] using this
      rw [hx, map_sum] at h
      simp only [map_smul, smul_eq_mul] at h
      simpa [col, mul_comm] using h
    have hzero : ∀ j, φ (bf j) = 0 := Fintype.linearIndependent_iff.mp hB _ hrel
    exact hφ0 (bf.ext fun j => by rw [hzero, LinearMap.zero_apply])

  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' (K := K) col
  rw [hspan] at hsp
  let b : Basis κ K (Fin s → K) := Basis.mk hli (by rw [hsp])
  haveI : Fintype κ := FiniteDimensional.fintypeBasisIndex b
  have hcard : Fintype.card (Fin s) = Fintype.card κ := by
    rw [← Module.finrank_eq_card_basis b, Module.finrank_fin_fun, Fintype.card_fin]
  let e : Fin s ≃ κ := Fintype.equivOfCardEq hcard
  refine ⟨a ∘ e, ?_⟩
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.linearIndependent_cols_iff_isUnit]
  have hcolM : (Matrix.of fun j l => B j ((a ∘ e) l)).col = (col ∘ a) ∘ e := by
    funext l j; rfl
  rw [hcolM]
  exact hli.comp e e.injective

def intValued (ι : Type*) : Submodule ℤ (ι → ℚ) where
  carrier := {w | ∀ a, ∃ m : ℤ, w a = m}
  zero_mem' := fun a => ⟨0, by simp⟩
  add_mem' := by
    intro x y hx hy a
    obtain ⟨m, hm⟩ := hx a; obtain ⟨m', hm'⟩ := hy a
    exact ⟨m + m', by simp [hm, hm']⟩
  smul_mem' := by
    intro c x hx a
    obtain ⟨m, hm⟩ := hx a
    exact ⟨c * m, by simp [hm]⟩

theorem mem_intValued {ι : Type*} {w : ι → ℚ} : w ∈ intValued ι ↔ ∀ a, ∃ m : ℤ, w a = m := Iff.rfl

end SatMinor

open SatMinor in

theorem exists_int_saturatedBasis_det_not_dvd
    (p : ℕ) [Fact p.Prime] {ι : Type*} {n : ℕ} (v : Fin n → ι → ℤ) :
    ∃ (s : ℕ) (B : Fin s → ι → ℤ) (t : Fin s → Fin n → ℚ) (u : Fin n → Fin s → ℤ) (cols : Fin s → ι),
      (∀ j a, (B j a : ℚ) = ∑ i, t j i * (v i a : ℚ)) ∧
      (∀ i a, v i a = ∑ j, u i j * B j a) ∧
      ¬ ((p : ℤ) ∣ (Matrix.of fun j l => B j (cols l)).det) := by
  classical
  haveI : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩

  let vQ : Fin n → ι → ℚ := fun i a => (v i a : ℚ)
  let VQ : Submodule ℚ (ι → ℚ) := span ℚ (Set.range vQ)

  let Λ : Submodule ℤ (ι → ℚ) := VQ.restrictScalars ℤ ⊓ intValued ι
  have hΛ_mem : ∀ {w : ι → ℚ}, w ∈ Λ ↔ w ∈ VQ ∧ ∀ a, ∃ m : ℤ, w a = m := fun {w} => Iff.rfl
  have hvQ_mem : ∀ i, vQ i ∈ Λ := fun i =>
    (hΛ_mem).mpr ⟨subset_span ⟨i, rfl⟩, fun a => ⟨v i a, rfl⟩⟩

  obtain ⟨κ₀, a₀, ha₀, hsp₀, hli₀⟩ := exists_linearIndependent' (K := ℚ) vQ
  haveI : Fintype κ₀ := Fintype.ofInjective a₀ ha₀
  let r := Fintype.card κ₀
  let e₀ : κ₀ ≃ Fin r := Fintype.equivFin κ₀
  let w : Fin r → ι → ℚ := vQ ∘ a₀ ∘ e₀.symm
  have hwli : LinearIndependent ℚ w := hli₀.comp e₀.symm e₀.symm.injective
  have hwspan : span ℚ (Set.range w) = VQ := by
    have : Set.range w = Set.range (vQ ∘ a₀) := by
      ext x; constructor
      · rintro ⟨j, rfl⟩; exact ⟨e₀.symm j, rfl⟩
      · rintro ⟨k, rfl⟩; exact ⟨e₀ k, by simp [w]⟩
    rw [this, hsp₀]
  obtain ⟨cols₀, hdet₀⟩ := exists_cols_isUnit_det w hwli

  let A₀ℤ : Matrix (Fin r) (Fin r) ℤ := Matrix.of fun j l => v (a₀ (e₀.symm j)) (cols₀ l)
  have hA₀ : (Matrix.of fun j l => w j (cols₀ l)) = A₀ℤ.map (Int.castRingHom ℚ) := by
    ext j l; rfl
  let d : ℤ := A₀ℤ.det
  have hA₀' : (Matrix.of fun j l => w j (cols₀ l)) = (Int.castRingHom ℚ).mapMatrix A₀ℤ := by
    rw [RingHom.mapMatrix_apply]; exact hA₀
  have hd_cast : (d : ℚ) = (Matrix.of fun j l => w j (cols₀ l)).det := by
    rw [hA₀', ← RingHom.map_det, eq_intCast]
  have hd0 : d ≠ 0 := by
    intro h
    apply hdet₀.ne_zero
    rw [← hd_cast, h, Int.cast_zero]

  let S : Submodule ℤ (ι → ℚ) := span ℤ (Set.range fun j => (d : ℚ)⁻¹ • w j)
  have hΛS : Λ ≤ S := by
    intro x hx
    obtain ⟨hxV, hxint⟩ := (hΛ_mem).mp hx
    rw [← hwspan] at hxV
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hxV

    let A₀ : Matrix (Fin r) (Fin r) ℚ := Matrix.of fun j l => w j (cols₀ l)
    have hy : ∀ l, (Matrix.vecMul c A₀) l = x (cols₀ l) := by
      intro l
      rw [← hc, Finset.sum_apply]
      simp [Matrix.vecMul, dotProduct, A₀, Pi.smul_apply]
    choose y hyx using fun l => hxint (cols₀ l)

    have hcr : A₀.det • c = Matrix.vecMul (Matrix.vecMul c A₀) A₀.adjugate := by
      rw [Matrix.vecMul_vecMul, Matrix.mul_adjugate, Matrix.vecMul_smul, Matrix.vecMul_one]
    have hadj : A₀.adjugate = (Int.castRingHom ℚ).mapMatrix A₀ℤ.adjugate := by
      rw [RingHom.map_adjugate, ← hA₀']

    have hcj : ∀ j, ∃ m : ℤ, (d : ℚ) * c j = m := by
      intro j
      have h := congrFun hcr j
      rw [Pi.smul_apply, smul_eq_mul, ← hd_cast] at h
      refine ⟨∑ l, y l * (A₀ℤ.adjugate l j), ?_⟩
      have hyv : Matrix.vecMul c A₀ = fun l => (y l : ℚ) := funext fun l => by rw [hy, hyx]
      rw [h, hyv, hadj, RingHom.mapMatrix_apply]
      push_cast
      simp [Matrix.vecMul, dotProduct, Matrix.map_apply]
    choose m hm using hcj
    rw [← hc]
    refine Submodule.sum_mem _ fun j _ => ?_
    have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast hd0
    have : c j • w j = m j • ((d : ℚ)⁻¹ • w j) := by
      rw [← Int.cast_smul_eq_zsmul ℚ (m j), smul_smul, ← hm j]
      congr 1
      field_simp
    rw [this]
    exact Submodule.smul_mem _ _ (subset_span ⟨j, rfl⟩)
  have hSfg : S.FG := Submodule.fg_span (Set.finite_range _)
  have hΛfg : Λ.FG := by
    haveI : IsNoetherian ℤ S := isNoetherian_of_fg_of_noetherian _ hSfg
    have h1 : (Λ.comap S.subtype).FG := IsNoetherian.noetherian _
    have h2 : (Λ.comap S.subtype).map S.subtype = Λ := by
      rw [Submodule.map_comap_subtype, inf_eq_right.mpr hΛS]
    rw [← h2]
    exact h1.map _

  haveI : Module.Finite ℤ Λ := Module.Finite.iff_fg.mpr hΛfg
  obtain ⟨s, bΛ⟩ := (Module.basisOfFiniteTypeTorsionFree' : Σ s : ℕ, Basis (Fin s) ℤ Λ)

  have hbint : ∀ j a, ∃ m : ℤ, ((bΛ j : Λ) : ι → ℚ) a = m := fun j => ((hΛ_mem).mp (bΛ j).2).2
  choose B hB using hbint

  have hbV : ∀ j, ((bΛ j : Λ) : ι → ℚ) ∈ VQ := fun j => ((hΛ_mem).mp (bΛ j).2).1
  choose t ht using fun j => (Submodule.mem_span_range_iff_exists_fun ℚ).mp (hbV j)

  let u : Fin n → Fin s → ℤ := fun i j => bΛ.repr ⟨vQ i, hvQ_mem i⟩ j
  refine ⟨s, B, t, u, ?_⟩

  let Bp : Fin s → ι → ZMod p := fun j a => (B j a : ZMod p)
  have hBp : LinearIndependent (ZMod p) Bp := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j₀

    let lam : Fin s → ℤ := fun j => ((g j).val : ℤ)
    have hlam : ∀ j, (lam j : ZMod p) = g j := fun j => by simp [lam]

    have hdvd : ∀ a, (p : ℤ) ∣ ∑ j, lam j * B j a := by
      intro a
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      have h := congrFun hg a
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
      push_cast
      simpa [hlam, Bp] using h
    choose z hz using hdvd

    let wv : ι → ℚ := fun a => (z a : ℚ)
    have hsum : ∀ a, (∑ j, lam j • ((bΛ j : Λ) : ι → ℚ)) a = (p : ℚ) * wv a := by
      intro a
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, hB]
      simp only [zsmul_eq_mul, wv]
      exact_mod_cast (hz a)
    have hwvΛ : wv ∈ Λ := by
      refine (hΛ_mem).mpr ⟨?_, fun a => ⟨z a, rfl⟩⟩
      have hmem : (∑ j, lam j • ((bΛ j : Λ) : ι → ℚ)) ∈ VQ :=
        Submodule.sum_mem _ fun j _ => Submodule.smul_of_tower_mem _ _ (hbV j)
      have heq : wv = (p : ℚ)⁻¹ • ∑ j, lam j • ((bΛ j : Λ) : ι → ℚ) := by
        funext a
        rw [Pi.smul_apply, hsum, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀, one_mul]
        exact_mod_cast (Fact.out : p.Prime).ne_zero
      rw [heq]
      exact VQ.smul_mem _ hmem

    have hpΛ : (p : ℤ) • (⟨wv, hwvΛ⟩ : Λ) = bΛ.equivFun.symm lam := by
      rw [Basis.equivFun_symm_apply]
      apply Subtype.ext
      funext a
      have lhs : (((p : ℤ) • (⟨wv, hwvΛ⟩ : Λ) : Λ) : ι → ℚ) a = (p : ℚ) * wv a := by
        rw [Submodule.coe_smul_of_tower, Pi.smul_apply, zsmul_eq_mul]; push_cast; rfl
      have rhs : ((∑ j, lam j • bΛ j : Λ) : ι → ℚ) a = (∑ j, lam j • ((bΛ j : Λ) : ι → ℚ)) a := by
        rw [Submodule.coe_sum, Finset.sum_apply, Finset.sum_apply]
        simp only [Submodule.coe_smul_of_tower, Pi.smul_apply]
      rw [lhs, rhs, hsum a]
    have hrepr : (p : ℤ) * bΛ.repr (⟨wv, hwvΛ⟩ : Λ) j₀ = lam j₀ := by
      have h := congrArg (fun x : Λ => bΛ.equivFun x j₀) hpΛ
      simp only [map_smul, Pi.smul_apply, smul_eq_mul, LinearEquiv.apply_symm_apply,
        Basis.equivFun_apply] at h
      exact h
    rw [← hlam j₀, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ⟨_, hrepr.symm⟩

  obtain ⟨cols, hcols⟩ := exists_cols_isUnit_det Bp hBp
  refine ⟨cols, ?_, ?_, ?_⟩
  ·
    intro j a
    rw [← hB j a, ← ht j]
    simp [Finset.sum_apply, Pi.smul_apply, vQ]
  ·
    intro i a
    have h := congrArg (fun x : Λ => (x : ι → ℚ) a) (bΛ.sum_repr ⟨vQ i, hvQ_mem i⟩).symm
    simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul_of_tower, Pi.smul_apply, hB] at h
    simp only [zsmul_eq_mul] at h

    have h' : (v i a : ℚ) = ∑ j, ((u i j : ℤ) : ℚ) * (B j a : ℚ) := h
    exact_mod_cast h'
  ·
    intro hdvd
    apply hcols.ne_zero
    have : (Matrix.of fun j l => Bp j (cols l)) = (Matrix.of fun j l => B j (cols l)).map (Int.castRingHom (ZMod p)) := by
      ext j l; rfl
    rw [this, ← RingHom.mapMatrix_apply, ← RingHom.map_det, eq_intCast]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd

end L1SatMinor

namespace K2eGlueIhl

open UpperHalfPlane

theorem T_mem_GammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) : ModularGroup.T ∈ CohCarrier.GammaH M H := by
  have hT0 : ModularGroup.T ∈ CongruenceSubgroup.Gamma0 M := by
    rw [CongruenceSubgroup.Gamma0_mem]; simp [ModularGroup.T]
  refine ⟨⟨ModularGroup.T, hT0⟩, ?_, rfl⟩
  show (⟨ModularGroup.T, hT0⟩ : CongruenceSubgroup.Gamma0 M) ∈ Subgroup.comap (CohCarrier.gamma0Units M) H
  rw [Subgroup.mem_comap]
  have : CohCarrier.gamma0Units M ⟨ModularGroup.T, hT0⟩ = 1 := by
    ext
    simp [CohCarrier.gamma0Units, CongruenceSubgroup.Gamma0Map, ModularGroup.T]
  rw [this]; exact one_mem H

theorem one_mem_strictPeriods_GammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    (1 : ℝ) ∈ ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (T_mem_GammaH M H)]
  exact AddSubgroup.mem_zmultiples _

section QExp
variable {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne] {k : ℤ} {ι : Type*}

theorem coe_sum_smul (s : Finset ι) (c : ι → ℂ) (X : ι → ModularForm Γ k) :
    (⇑(∑ j ∈ s, c j • X j) : ℍ → ℂ) = ∑ j ∈ s, c j • (⇑(X j) : ℍ → ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ModularForm.coe_add, ModularForm.IsGLPos.coe_smul, ih]

theorem qExpansion_coe_sum_smul (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (s : Finset ι) (c : ι → ℂ) (X : ι → ModularForm Γ k) :
    qExpansion 1 (⇑(∑ j ∈ s, c j • X j) : ℍ → ℂ) = ∑ j ∈ s, c j • qExpansion 1 (⇑(X j) : ℍ → ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [qExpansion_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ModularForm.coe_add,
        ModularForm.qExpansion_add one_pos hΓ (c a • X a) (∑ j ∈ s, c j • X j), ih,
        ModularForm.IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos hΓ (c a) (X a)]

omit [Γ.HasDetOne] in

theorem eq_of_qExpansion_eq (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (f g : ModularForm Γ k)
    (h : qExpansion 1 (⇑f : ℍ → ℂ) = qExpansion 1 (⇑g : ℍ → ℂ)) : f = g := by
  have h0 : qExpansion 1 (⇑(f - g) : ℍ → ℂ) = 0 := by
    rw [ModularForm.coe_sub, ModularForm.qExpansion_sub one_pos hΓ f g, h, sub_self]
  exact sub_eq_zero.mp ((ModularForm.qExpansion_eq_zero_iff one_pos hΓ (f - g)).mp h0)

end QExp

section Loc
variable (𝔪 : Ideal ↥(integralClosure ℤ ℂ))

def IsLoc (z : ℂ) : Prop := ∃ x y : ↥(integralClosure ℤ ℂ), y ∉ 𝔪 ∧ (x : ℂ) = y * z

variable {𝔪}

theorem isLoc_of_mem (h1 : 𝔪 ≠ ⊤) {z : ℂ} (hz : z ∈ integralClosure ℤ ℂ) : IsLoc 𝔪 z :=
  ⟨⟨z, hz⟩, 1, fun h => h1 ((Ideal.eq_top_iff_one _).mpr h), by simp⟩

theorem IsLoc.mul [h𝔪 : 𝔪.IsPrime] {z w : ℂ} (hz : IsLoc 𝔪 z) (hw : IsLoc 𝔪 w) : IsLoc 𝔪 (z * w) := by
  obtain ⟨x, y, hy, hxy⟩ := hz
  obtain ⟨x', y', hy', hxy'⟩ := hw
  refine ⟨x * x', y * y', fun h => (h𝔪.mem_or_mem h).elim hy hy', ?_⟩
  push_cast
  rw [hxy, hxy']; ring

theorem IsLoc.add [h𝔪 : 𝔪.IsPrime] {z w : ℂ} (hz : IsLoc 𝔪 z) (hw : IsLoc 𝔪 w) : IsLoc 𝔪 (z + w) := by
  obtain ⟨x, y, hy, hxy⟩ := hz
  obtain ⟨x', y', hy', hxy'⟩ := hw
  refine ⟨x * y' + x' * y, y * y', fun h => (h𝔪.mem_or_mem h).elim hy hy', ?_⟩
  push_cast
  rw [hxy, hxy']; ring

theorem isLoc_sum [h𝔪 : 𝔪.IsPrime] {ι : Type*} (s : Finset ι) (z : ι → ℂ) (hz : ∀ i ∈ s, IsLoc 𝔪 (z i)) :
    IsLoc 𝔪 (∑ i ∈ s, z i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact isLoc_of_mem h𝔪.ne_top (Subalgebra.zero_mem _)
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hz a (Finset.mem_insert_self a s)).add (ih fun i hi => hz i (Finset.mem_insert_of_mem hi))

theorem IsLoc.of_mul_left [h𝔪 : 𝔪.IsPrime] {z : ℂ} (y₀ : ↥(integralClosure ℤ ℂ)) (hy₀ : y₀ ∉ 𝔪)
    (h : IsLoc 𝔪 ((y₀ : ℂ) * z)) : IsLoc 𝔪 z := by
  obtain ⟨x, y, hy, hxy⟩ := h
  refine ⟨x, y * y₀, fun h => (h𝔪.mem_or_mem h).elim hy hy₀, ?_⟩
  push_cast
  rw [hxy]; ring

theorem intCast_not_mem (h1 : 𝔪 ≠ ⊤) {p : ℕ} (hp : p.Prime) (hp𝔪 : ((p : ℤ) : ↥(integralClosure ℤ ℂ)) ∈ 𝔪)
    {d : ℤ} (hd : ¬ (p : ℤ) ∣ d) : ((d : ℤ) : ↥(integralClosure ℤ ℂ)) ∉ 𝔪 := by
  intro hdm
  have hcop : IsCoprime (p : ℤ) d := (Nat.prime_iff_prime_int.mp hp).irreducible.coprime_iff_not_dvd.mpr hd
  obtain ⟨a, b, hab⟩ := hcop
  apply h1
  rw [Ideal.eq_top_iff_one]
  have h1' : (1 : ↥(integralClosure ℤ ℂ)) = (a : ↥(integralClosure ℤ ℂ)) * ((p : ℤ) : ↥(integralClosure ℤ ℂ)) +
      (b : ↥(integralClosure ℤ ℂ)) * ((d : ℤ) : ↥(integralClosure ℤ ℂ)) := by
    have := congrArg (Int.cast : ℤ → ↥(integralClosure ℤ ℂ)) hab
    push_cast at this
    exact this.symm
  rw [h1']
  exact 𝔪.add_mem (𝔪.mul_mem_left _ hp𝔪) (𝔪.mul_mem_left _ hdm)

end Loc

end K2eGlueIhl

namespace K2eGlueIhl
open UpperHalfPlane

theorem locSpan (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) {k : ℤ}
    (F : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
    (𝔪 : Ideal ↥(integralClosure ℤ ℂ)) (h𝔪 : 𝔪.IsMaximal) (hp𝔪 : ((p : ℤ) : ↥(integralClosure ℤ ℂ)) ∈ 𝔪)
    (hF : ∀ n : ℕ, IsLoc 𝔪 ((qExpansion 1 (⇑F : ℍ → ℂ)).coeff n)) :
    ∃ (s : ℕ) (c : Fin s → ℂ) (𝔅 : Fin s → ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
      (r : Fin s → PowerSeries ℤ),
      (∀ j, ModularCurve.IsIntegralQExp (𝔅 j) (r j)) ∧ (∀ j, IsLoc 𝔪 (c j)) ∧
        (⇑F : ℍ → ℂ) = ∑ j, c j • (⇑(𝔅 j) : ℍ → ℂ) := by
  classical
  haveI := h𝔪.isPrime
  have hp : p.Prime := Fact.out
  have hΓ := one_mem_strictPeriods_GammaH M H

  obtain ⟨n, c, G, r, hGr, hFsum⟩ := ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gammaH M H F
  obtain ⟨s, B, t, u, cols, hBt, hvu, hdet⟩ :=
    exists_int_saturatedBasis_det_not_dvd p (ι := ℕ) (fun i a => PowerSeries.coeff a (r i))

  let 𝔅 : Fin s → ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k :=
    fun j => ∑ i, ((t j i : ℚ) : ℂ) • G i
  have hq𝔅 : ∀ j, qExpansion 1 (⇑(𝔅 j) : ℍ → ℂ) = ∑ i, ((t j i : ℚ) : ℂ) • qExpansion 1 (⇑(G i) : ℍ → ℂ) :=
    fun j => qExpansion_coe_sum_smul hΓ _ _ _
  have hcoeffG : ∀ i a, PowerSeries.coeff a (qExpansion 1 (⇑(G i) : ℍ → ℂ)) = ((PowerSeries.coeff a (r i) : ℤ) : ℂ) :=
    fun i a => ((hGr i).coeff a).symm
  have hcoeff𝔅 : ∀ j a, PowerSeries.coeff a (qExpansion 1 (⇑(𝔅 j) : ℍ → ℂ)) = ((B j a : ℤ) : ℂ) := by
    intro j a
    rw [hq𝔅, map_sum]
    simp only [PowerSeries.coeff_smul, smul_eq_mul, hcoeffG]
    have h := congrArg (fun q : ℚ => (q : ℂ)) (hBt j a)
    push_cast at h
    rw [h]
  have h𝔅int : ∀ j, ModularCurve.IsIntegralQExp (𝔅 j) (PowerSeries.mk (B j)) := by
    intro j
    rw [ModularCurve.isIntegralQExp_iff]
    intro a
    rw [PowerSeries.coeff_mk, hcoeff𝔅]

  let c' : Fin s → ℂ := fun j => ∑ i, c i * (u i j : ℂ)

  have hcoeffF : ∀ a, PowerSeries.coeff a (qExpansion 1 (⇑F : ℍ → ℂ)) = ∑ j, c' j * ((B j a : ℤ) : ℂ) := by
    intro a
    have hF' : (⇑F : ℍ → ℂ) = ⇑(∑ i, c i • G i) := by rw [coe_sum_smul]; exact hFsum
    rw [hF', qExpansion_coe_sum_smul hΓ, map_sum]
    simp only [PowerSeries.coeff_smul, smul_eq_mul, hcoeffG]
    have hv : ∀ i, ((PowerSeries.coeff a (r i) : ℤ) : ℂ) = ∑ j, (u i j : ℂ) * ((B j a : ℤ) : ℂ) := by
      intro i
      have h := congrArg (fun z : ℤ => (z : ℂ)) (hvu i a)
      push_cast at h
      exact h
    simp only [hv, Finset.mul_sum, c', Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  have hFeq : F = ∑ j, c' j • 𝔅 j := by
    apply eq_of_qExpansion_eq hΓ
    ext a
    rw [hcoeffF, qExpansion_coe_sum_smul hΓ, map_sum]
    simp only [PowerSeries.coeff_smul, smul_eq_mul, hcoeff𝔅]

  let A : Matrix (Fin s) (Fin s) ℤ := Matrix.of fun j l => B j (cols l)
  let Ac : Matrix (Fin s) (Fin s) ℂ := A.map (Int.castRingHom ℂ)
  have hw : ∀ l, (Ac.transpose.mulVec c') l = PowerSeries.coeff (cols l) (qExpansion 1 (⇑F : ℍ → ℂ)) := by
    intro l
    rw [hcoeffF, Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Ac, A, Matrix.transpose_apply, Matrix.map_apply, mul_comm]
  have hcramer : ∀ j, (Ac.det : ℂ) * c' j = (Ac.transpose.adjugate.mulVec (Ac.transpose.mulVec c')) j := by
    intro j
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.det_transpose, Matrix.smul_mulVec, Matrix.one_mulVec,
      Pi.smul_apply, smul_eq_mul]
  have hdetZ : Ac.det = ((A.det : ℤ) : ℂ) := by
    rw [show Ac = (Int.castRingHom ℂ).mapMatrix A from rfl, ← RingHom.map_det]; rfl
  have hdet𝔪 : ((A.det : ℤ) : ↥(integralClosure ℤ ℂ)) ∉ 𝔪 := intCast_not_mem h𝔪.ne_top hp hp𝔪 hdet
  have hc'loc : ∀ j, IsLoc 𝔪 (c' j) := by
    intro j
    refine IsLoc.of_mul_left ((A.det : ℤ) : ↥(integralClosure ℤ ℂ)) hdet𝔪 ?_
    rw [show (((A.det : ℤ) : ↥(integralClosure ℤ ℂ)) : ℂ) = Ac.det by rw [hdetZ]; simp, hcramer j, Matrix.mulVec, dotProduct]
    refine isLoc_sum _ _ fun l _ => IsLoc.mul ?_ ?_
    ·
      have : Ac.transpose.adjugate = ((Int.castRingHom ℂ).mapMatrix A.transpose.adjugate) := by
        rw [RingHom.map_adjugate]
        rfl
      rw [this]
      exact isLoc_of_mem h𝔪.ne_top (by simp only [RingHom.mapMatrix_apply, Matrix.map_apply]; exact Subalgebra.intCast_mem _ _)
    · rw [hw]; exact hF (cols l)
  exact ⟨s, c', 𝔅, fun j => PowerSeries.mk (B j), h𝔅int, hc'loc, by rw [hFeq, coe_sum_smul]⟩

theorem alSlash_sum_smul {M q : ℕ} [NeZero M] (W : ModularForm.AtkinLehnerDatum M q) (k : ℤ) {ι : Type*}
    (s : Finset ι) (c : ι → ℂ) (g : ι → ℍ → ℂ) :
    ModularForm.alSlash W k (∑ j ∈ s, c j • g j) = ∑ j ∈ s, c j • ModularForm.alSlash W k (g j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ModularForm.alSlash_def]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ModularForm.alSlash_add, ModularForm.alSlash_smul, ih]

end K2eGlueIhl

open K2eGlueIhl UpperHalfPlane in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (W : ModularForm.AtkinLehnerDatum M (M / p)) {k : ℤ} (f : CuspForm (CohCarrier.GammaH M H) k) (hk : Even k)
    (𝔪 : Ideal ↥(integralClosure ℤ ℂ)) (h𝔪 : 𝔪.IsMaximal) (hp𝔪 : ((p : ℤ) : ↥(integralClosure ℤ ℂ)) ∈ 𝔪)
    (hf : ∀ n : ℕ, ∃ x y : ↥(integralClosure ℤ ℂ), y ∉ 𝔪 ∧ (x : ℂ) = y * (UpperHalfPlane.qExpansion 1 ⇑f).coeff n) :
    ∀ n : ℕ, ∃ x y : ↥(integralClosure ℤ ℂ), y ∉ 𝔪 ∧
      (x : ℂ) = y * (UpperHalfPlane.qExpansion 1 (ModularForm.alSlash W k ⇑f)).coeff n := by
  classical
  haveI := h𝔪.isPrime
  have hp : p.Prime := Fact.out
  have hΓ := one_mem_strictPeriods_GammaH M H

  let fM : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k :=
    { toFun := ⇑f
      slash_action_eq' := fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ
      holo' := ModularFormClass.holo f
      bdd_at_cusps' := fun hc => ModularFormClass.bdd_at_cusps f hc }
  have hfM : (⇑fM : ℍ → ℂ) = ⇑f := rfl

  obtain ⟨s, c, 𝔅, r, h𝔅r, hc, hfsum⟩ := locSpan p M H fM 𝔪 h𝔪 hp𝔪 (by rw [hfM]; exact hf)
  rw [hfM] at hfsum

  choose X hX using fun j => ModularForm.exists_GammaH_coe_eq_alSlash_of_forall_unitsMap_atkinLehnerFactor_eq_one W H hHp k (𝔅 j)
  choose D hpD hDint using fun j =>
    ModularForm.exists_not_dvd_and_forall_isIntegral_mul_qExpansion_alSlash_of_isIntegralQExp_of_even p M H hpM hpM2 hHp W hk
      (𝔅 j) (r j) (h𝔅r j)
  have hXloc : ∀ j n, IsLoc 𝔪 (PowerSeries.coeff n (qExpansion 1 (⇑(X j) : ℍ → ℂ))) := by
    intro j n
    have hD𝔪 : (((D j : ℕ) : ℤ) : ↥(integralClosure ℤ ℂ)) ∉ 𝔪 :=
      intCast_not_mem h𝔪.ne_top hp hp𝔪 (by exact_mod_cast hpD j)
    refine IsLoc.of_mul_left _ hD𝔪 ?_
    rw [hX j]
    have h := hDint j n
    rw [← mem_integralClosure_iff] at h
    exact isLoc_of_mem h𝔪.ne_top (by push_cast; exact h)

  have hsl : ModularForm.alSlash W k ⇑f = ⇑(∑ j, c j • X j) := by
    rw [hfsum, alSlash_sum_smul, coe_sum_smul]
    exact Finset.sum_congr rfl fun j _ => by rw [hX j]
  intro n
  show IsLoc 𝔪 _
  rw [hsl, qExpansion_coe_sum_smul hΓ, map_sum]
  refine isLoc_sum _ _ fun j _ => ?_
  rw [PowerSeries.coeff_smul, smul_eq_mul]
  exact (hc j).mul (hXloc j n)

end S_CuspForm_forall_exists_eq_mul_qExpansion_alSlash_of_mem_maximal_of_forall_unitsMap_of_even
end P2MW
export P2MW.S_CuspForm_forall_exists_eq_mul_qExpansion_alSlash_of_mem_maximal_of_forall_unitsMap_of_even (solution)
