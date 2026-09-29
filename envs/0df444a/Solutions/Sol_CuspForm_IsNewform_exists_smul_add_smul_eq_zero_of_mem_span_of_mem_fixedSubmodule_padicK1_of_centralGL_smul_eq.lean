-- Prove2me | solution 1 for CuspForm.IsNewform.exists_smul_add_smul_eq_zero_of_mem_span_of_mem_fixedSubmodule_padicK1_of_centralGL_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/538b641d-d3f9-57f9-98e1-8264ec5ade30

import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_CuspForm_AdelicLiftGamma1
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_AutomorphicForm_FnTwist
import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_CuspForm_IsAdelicLiftOf_apply_mul_finEmbed_levelZero_eq_of_mem_span_fnTwist_of_fixed
import Theorems.Thm_CuspForm_IsAdelicLiftOf_exists_hasNebentypus_isAdelicLiftOfGamma1_of_mem_span_fnTwist_of_fixed
import Theorems.Thm_CuspForm_IsNormalizedEigenform_sum_apply_padicToAdelic_eq_mul_of_mem_span_fnTwist
import Theorems.Thm_CuspForm_HasNebentypus_qCoeff_hecke_eq_of_isAdelicLiftOfGamma1_of_sum_apply_padicToAdelic_eq
import Theorems.Thm_CuspForm_heckeTLin_apply_eq_smul_iff
import Theorems.Thm_CuspForm_IsNewform_iInf_eigenspace_heckeTLin_eq_span_singleton
import Theorems.Thm_AutomorphicForm_ext_of_invariant_of_forall_glFin_eq_one_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsNewform_exists_smul_add_smul_eq_zero_of_mem_span_of_mem_fixedSubmodule_padicK1_of_centralGL_smul_eq
p2m_attr_erase "instance" "FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2"
p2m_attr_erase "simp" "FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero CuspForm.coe_traceLin_apply ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply FreyPackage.ModMCarrier.coe_levelInclusionLin FreyPackage.ModMCarrier.atkinLehnerDatumOfPrimeNotDvd_R FreyPackage.ModMCarrier.latticeRed.mk_eq_tmul CuspForm.coe_heckeULowerLin_apply"

set_option autoImplicit false

open NumberField AdelicDock IsDedekindDomain

namespace NewvectorLineA

private theorem coe_finComponent {R : Type*} [CommRing R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (w : HeightOneSpectrum R) (g : GL (Fin 2) (FiniteAdeleRing R K)) :
    ((AdelicLevel.finComponent R K w g) : Matrix (Fin 2) (Fin 2) (w.adicCompletion K))
      = (AdelicLevel.finAdeleEval R K w).mapMatrix
          (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) := by
  ext i j
  rw [AdelicLevel.finComponent_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
    AdelicLevel.finAdeleEval_apply]

private theorem mapMatrix_injective {A B : Type*} [Semiring A] [Semiring B] {f : A →+* B}
    (hf : Function.Injective f) :
    Function.Injective ((RingHom.mapMatrix f : Matrix (Fin 2) (Fin 2) A →+* _)) := fun M N h => by
  ext i j
  exact hf (by simpa [RingHom.mapMatrix_apply, Matrix.map_apply] using congrFun (congrFun h i) j)

private theorem exists_glMap_eq {R : Type*} [CommRing R] {K : Type*} [CommRing K]
    (f : R →+* K) (hf : Function.Injective f) (x : GL (Fin 2) K)
    (hx : ∀ i j, ∃ r, f r = (x : Matrix (Fin 2) (Fin 2) K) i j)
    (hx' : ∀ i j, ∃ r, f r = ((x⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j) :
    ∃ c : GL (Fin 2) R, Matrix.GeneralLinearGroup.map (n := Fin 2) f c = x := by
  set M : Matrix (Fin 2) (Fin 2) R := fun i j => Classical.choose (hx i j) with hM
  set M' : Matrix (Fin 2) (Fin 2) R := fun i j => Classical.choose (hx' i j)
  have hMim : f.mapMatrix M = (x : Matrix (Fin 2) (Fin 2) K) :=
    Matrix.ext fun i j => Classical.choose_spec (hx i j)
  have hM'im : f.mapMatrix M' = ((x⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) :=
    Matrix.ext fun i j => Classical.choose_spec (hx' i j)
  have hinj : Function.Injective ((RingHom.mapMatrix f : Matrix (Fin 2) (Fin 2) R →+* _)) :=
    mapMatrix_injective hf
  have hMM' : M * M' = 1 := hinj (by
    rw [map_mul, hMim, hM'im, map_one, ← Units.val_mul, mul_inv_cancel, Units.val_one])
  have hM'M : M' * M = 1 := hinj (by
    rw [map_mul, hM'im, hMim, map_one, ← Units.val_mul, inv_mul_cancel, Units.val_one])
  refine ⟨⟨M, M', hMM', hM'M⟩, Matrix.GeneralLinearGroup.ext fun i j => ?_⟩
  rw [Matrix.GeneralLinearGroup.map_apply]
  exact congrFun (congrFun hMim i) j

end NewvectorLineA

namespace NewvectorLineB

open NumberField NumberField.AdelicLevel AdelicDock IsDedekindDomain

section Places

private theorem natGenerator_padicPlace (p : ℕ) [Fact p.Prime] :
    Rat.HeightOneSpectrum.natGenerator (R := 𝓞 ℚ) (padicPlace p) = p :=
  congrArg Subtype.val
    ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply ⟨p, Fact.out⟩)

private theorem eq_padicPlace_natGenerator (v : HeightOneSpectrum (𝓞 ℚ)) :
    haveI : Fact (Rat.HeightOneSpectrum.natGenerator v).Prime :=
      ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩
    v = padicPlace (Rat.HeightOneSpectrum.natGenerator v) := by
  haveI : Fact (Rat.HeightOneSpectrum.natGenerator v).Prime :=
    ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩
  refine ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm_apply_apply v).symm.trans ?_
  exact congrArg _ (Subtype.ext rfl)

private theorem valued_natCast_eq_of_factorization_eq (ℓ : ℕ) [Fact ℓ.Prime]
    {N M : ℕ} (hN : N ≠ 0) (hM : M ≠ 0) (hfac : N.factorization ℓ = M.factorization ℓ) :
    Valued.v (padicRingEquiv ℓ (N : ℚ_[ℓ])) = Valued.v (padicRingEquiv ℓ (M : ℚ_[ℓ])) := by
  have hN' : (N : ℚ_[ℓ]) ≠ 0 := by exact_mod_cast hN
  have hM' : (M : ℚ_[ℓ]) ≠ 0 := by exact_mod_cast hM
  refine le_antisymm ?_ ?_
  · rw [valued_le_valued_iff ℓ _ _ hM', norm_natCast_eq_zpow_neg_factorization ℓ hN,
      norm_natCast_eq_zpow_neg_factorization ℓ hM, hfac]
  · rw [valued_le_valued_iff ℓ _ _ hN', norm_natCast_eq_zpow_neg_factorization ℓ hN,
      norm_natCast_eq_zpow_neg_factorization ℓ hM, hfac]

theorem idealBound_ratLevel_eq_of_factorization_eq {q : ℕ} [Fact q.Prime] {N M : ℕ}
    (hN : N ≠ 0) (hM : M ≠ 0)
    (hfac : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ q → N.factorization ℓ = M.factorization ℓ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : v ≠ padicPlace q) :
    idealBound (𝓞 ℚ) (ratLevel N) v = idealBound (𝓞 ℚ) (ratLevel M) v := by
  haveI hℓp : Fact (Rat.HeightOneSpectrum.natGenerator v).Prime :=
    ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩
  have hvℓ : v = padicPlace (Rat.HeightOneSpectrum.natGenerator v) :=
    eq_padicPlace_natGenerator v
  have hne : Rat.HeightOneSpectrum.natGenerator v ≠ q := fun heq =>
    hv <| (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective <|
      Subtype.ext <| heq.trans (natGenerator_padicPlace q).symm
  rw [hvℓ, idealBound_ratLevel _ hN, idealBound_ratLevel _ hM,
    valued_natCast_eq_of_factorization_eq _ hN hM (hfac _ hℓp.out hne)]

end Places

section Lift

theorem exists_padicGL_map_eq_finComponent {q : ℕ} [Fact q.Prime] {I : Ideal (𝓞 ℚ)}
    {u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)} (hu : u ∈ finiteLevelZero (𝓞 ℚ) ℚ I) :
    ∃ c : GL (Fin 2) ℤ_[q],
      padicGL q (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap ℤ_[q] ℚ_[q]) c)
        = finComponent (𝓞 ℚ) ℚ (padicPlace q) u := by
  obtain ⟨hu₁, hu₂⟩ := mem_finiteLevelZero_iff.mp hu
  set cq : GL (Fin 2) ℚ_[q] := Matrix.GeneralLinearGroup.map (n := Fin 2)
    (padicRingEquiv q).symm.toRingHom (finComponent (𝓞 ℚ) ℚ (padicPlace q) u) with hcq
  have hcq_inv : padicGL q cq = finComponent (𝓞 ℚ) ℚ (padicPlace q) u :=
    Matrix.GeneralLinearGroup.ext fun i j => by
      rw [padicGL_apply, hcq, Matrix.GeneralLinearGroup.map_apply]
      exact RingEquiv.apply_symm_apply _ _
  have hex : ∀ (e : GL (Fin 2) ((padicPlace q).adicCompletion ℚ)),
      (∀ i j, (e : Matrix (Fin 2) (Fin 2) _) i j ∈ (padicPlace q).adicCompletionIntegers ℚ) →
      ∀ i j, ∃ r : ℤ_[q], algebraMap ℤ_[q] ℚ_[q] r
        = (Matrix.GeneralLinearGroup.map (n := Fin 2) (padicRingEquiv q).symm.toRingHom e
            : Matrix (Fin 2) (Fin 2) ℚ_[q]) i j := fun e he i j => by
    rw [Matrix.GeneralLinearGroup.map_apply]
    exact ⟨⟨_, (norm_le_one_iff_mem q _).mpr
      ((RingEquiv.apply_symm_apply (padicRingEquiv q) _).symm ▸ he i j)⟩,
      (PadicInt.algebraMap_apply _).trans rfl⟩
  have hmem : ∀ i j, (finComponent (𝓞 ℚ) ℚ (padicPlace q) u
      : Matrix (Fin 2) (Fin 2) _) i j ∈ (padicPlace q).adicCompletionIntegers ℚ := fun i j => by
    rw [finComponent_apply]; exact hu₁.integral i j (padicPlace q)
  have hmem' : ∀ i j, (finComponent (𝓞 ℚ) ℚ (padicPlace q) u⁻¹
      : Matrix (Fin 2) (Fin 2) _) i j ∈ (padicPlace q).adicCompletionIntegers ℚ := fun i j => by
    rw [finComponent_apply]; exact hu₂.integral i j (padicPlace q)
  obtain ⟨c, hc⟩ := NewvectorLineA.exists_glMap_eq (algebraMap ℤ_[q] ℚ_[q])
    (IsFractionRing.injective ℤ_[q] ℚ_[q]) cq (hcq ▸ hex _ hmem)
    (by rw [hcq, ← map_inv, ← map_inv]; exact hex _ hmem')
  exact ⟨c, hc ▸ hcq_inv⟩

theorem isUnit_entry_of_lowerLeft_mem {q : ℕ} [Fact q.Prime] (c : GL (Fin 2) ℤ_[q])
    (hc10 : ¬ IsUnit ((c : Matrix (Fin 2) (Fin 2) ℤ_[q]) 1 0)) :
    IsUnit ((c : Matrix (Fin 2) (Fin 2) ℤ_[q]) 1 1) := by
  have hdet : IsUnit (Matrix.det (c : Matrix (Fin 2) (Fin 2) ℤ_[q])) :=
    (Matrix.isUnit_iff_isUnit_det _).mp c.isUnit
  rw [Matrix.det_fin_two] at hdet
  by_contra h11
  have h10m : (q : ℤ_[q]) ∣ (c : Matrix (Fin 2) (Fin 2) ℤ_[q]) 1 0 :=
    (PadicInt.norm_lt_one_iff_dvd _).mp (PadicInt.not_isUnit_iff.mp hc10)
  have h11m : (q : ℤ_[q]) ∣ (c : Matrix (Fin 2) (Fin 2) ℤ_[q]) 1 1 :=
    (PadicInt.norm_lt_one_iff_dvd _).mp (PadicInt.not_isUnit_iff.mp h11)
  have hdetm : (q : ℤ_[q]) ∣
      (c : Matrix (Fin 2) (Fin 2) ℤ_[q]) 0 0 * (c : Matrix (Fin 2) (Fin 2) ℤ_[q]) 1 1
        - (c : Matrix (Fin 2) (Fin 2) ℤ_[q]) 0 1 * (c : Matrix (Fin 2) (Fin 2) ℤ_[q]) 1 0 :=
    dvd_sub (Dvd.dvd.mul_left h11m _) (Dvd.dvd.mul_left h10m _)
  exact PadicInt.not_isUnit_iff.mpr ((PadicInt.norm_lt_one_iff_dvd _).mpr hdetm) hdet

end Lift

section Split

private theorem isLevelZeroMatrix_of_finComponent_eq_and {q : ℕ} [Fact q.Prime] {N M : ℕ}
    (hsame : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ≠ padicPlace q →
      idealBound (𝓞 ℚ) (ratLevel N) v = idealBound (𝓞 ℚ) (ratLevel M) v)
    {g u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (hu : IsLevelZeroMatrix (𝓞 ℚ) ℚ (ratLevel N)
      (u : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)))
    (hgq : finComponent (𝓞 ℚ) ℚ (padicPlace q) g = 1)
    (hgaway : ∀ v ≠ padicPlace q, finComponent (𝓞 ℚ) ℚ v g = finComponent (𝓞 ℚ) ℚ v u) :
    IsLevelZeroMatrix (𝓞 ℚ) ℚ (ratLevel M)
      (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) := by
  refine ⟨fun i j v => ?_, fun v => ?_⟩
  all_goals rcases eq_or_ne v (padicPlace q) with rfl | hv
  · rw [← finComponent_apply, hgq, Units.val_one]
    rcases eq_or_ne i j with rfl | hij
    · rw [Matrix.one_apply_eq]; exact one_mem _
    · rw [Matrix.one_apply_ne hij]; exact zero_mem _
  · rw [← finComponent_apply, hgaway v hv, finComponent_apply]; exact hu.integral i j v
  · rw [← finComponent_apply, hgq, Units.val_one,
      Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), map_zero]
    exact zero_le'
  · rw [← finComponent_apply, hgaway v hv, finComponent_apply, ← hsame v hv]
    exact hu.lowerLeft v

theorem mul_padicToFinAdelic_inv_mem_finiteLevelZero {q : ℕ} [Fact q.Prime] {N M : ℕ}
    (hsame : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ≠ padicPlace q →
      idealBound (𝓞 ℚ) (ratLevel N) v = idealBound (𝓞 ℚ) (ratLevel M) v)
    {u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)} (hu : u ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel N))
    (c : GL (Fin 2) ℚ_[q]) (hc : finComponent (𝓞 ℚ) ℚ (padicPlace q) u = padicGL q c) :
    u * (padicToFinAdelic q c)⁻¹ ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel M) := by
  obtain ⟨hu₁, hu₂⟩ := mem_finiteLevelZero_iff.mp hu
  set g := u * (padicToFinAdelic q c)⁻¹ with hg
  have hgq : finComponent (𝓞 ℚ) ℚ (padicPlace q) g = 1 := by
    rw [hg, map_mul, map_inv, finComponent_padicToFinAdelic_self, hc, mul_inv_cancel]
  have hgaway : ∀ v ≠ padicPlace q,
      finComponent (𝓞 ℚ) ℚ v g = finComponent (𝓞 ℚ) ℚ v u := fun v hv => by
    rw [hg, map_mul, map_inv, finComponent_padicToFinAdelic_of_ne q c hv, inv_one, mul_one]
  rw [mem_finiteLevelZero_iff]
  exact ⟨isLevelZeroMatrix_of_finComponent_eq_and hsame hu₁ hgq hgaway,
    isLevelZeroMatrix_of_finComponent_eq_and hsame hu₂ (g := g⁻¹) (u := u⁻¹)
      (by rw [map_inv, hgq, inv_one])
      (fun v hv => by rw [map_inv, hgaway v hv, map_inv])⟩

end Split

section Rational

private theorem algebraMap_intCast_apply_padicPlace_eq (p : ℕ) [Fact p.Prime] (n : ℤ) :
    (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (n : ℚ)) (padicPlace p)
      = padicRingEquiv p ((n : ℤ_[p]) : ℚ_[p]) := by
  have hL : (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (n : ℚ)) (padicPlace p) =
      (n : (padicPlace p).adicCompletion ℚ) := by
    change ((algebraMap ℚ ((padicPlace p).adicCompletion ℚ)).comp (Int.castRingHom ℚ)) n = _
    exact eq_intCast _ n
  have hR : padicRingEquiv p ((n : ℤ_[p]) : ℚ_[p]) = (n : (padicPlace p).adicCompletion ℚ) := by
    rw [PadicInt.coe_intCast, map_intCast]
  exact hL.trans hR.symm

private theorem isLevelZeroMatrix_mapMatrix_of_int_entries {N : ℕ} (hN : N ≠ 0)
    (δ : Matrix (Fin 2) (Fin 2) ℚ) (hδ : ∀ a b, ∃ n : ℤ, δ a b = n)
    (hlow : ∃ m : ℤ, δ 1 0 = (N : ℚ) * m) :
    IsLevelZeroMatrix (𝓞 ℚ) ℚ (ratLevel N)
      ((algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)).mapMatrix δ) := by
  refine ⟨fun i j v => ?_, fun v => ?_⟩
  all_goals
    haveI : Fact (Rat.HeightOneSpectrum.natGenerator v).Prime :=
      ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩
    rw [eq_padicPlace_natGenerator v]
    set ℓ := Rat.HeightOneSpectrum.natGenerator v
  · rw [RingHom.mapMatrix_apply, Matrix.map_apply]
    obtain ⟨n, hn⟩ := hδ i j
    rw [hn, algebraMap_intCast_apply_padicPlace_eq ℓ n]
    exact padicRingEquiv_coe_mem ℓ _
  · rw [RingHom.mapMatrix_apply, Matrix.map_apply]
    obtain ⟨m, hm⟩ := hlow
    have hNm : δ 1 0 = ((N * m : ℤ) : ℚ) := by push_cast; linarith [hm]
    rw [hNm, algebraMap_intCast_apply_padicPlace_eq ℓ (N * m)]
    rw [(valued_coe_le_idealBound_iff ℓ hN _)]
    have hdvd : (ℓ : ℤ_[ℓ]) ^ N.factorization ℓ ∣ (↑(N * m) : ℤ_[ℓ]) := by
      have hdvdZ : (ℓ : ℤ) ^ N.factorization ℓ ∣ (N * m : ℤ) := by
        refine Dvd.dvd.mul_right ?_ m
        exact_mod_cast Nat.ordProj_dvd N ℓ
      obtain ⟨k, hk⟩ := hdvdZ
      exact ⟨(k : ℤ_[ℓ]), by push_cast [hk]; ring⟩
    exact Ideal.mem_span_singleton.mpr hdvd

theorem map_algebraMap_mem_finiteLevelZero {N : ℕ} (hN : N ≠ 0) (δ : GL (Fin 2) ℚ)
    (hδ : ∀ a b : Fin 2, ∃ n : ℤ, (δ : Matrix (Fin 2) (Fin 2) ℚ) a b = n)
    (hδ' : ∀ a b : Fin 2, ∃ n : ℤ, ((δ⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) a b = n)
    (hlow : ∃ m : ℤ, (δ : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = (N : ℚ) * m)
    (hlow' : ∃ m : ℤ, ((δ⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = (N : ℚ) * m) :
    Matrix.GeneralLinearGroup.map (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)) δ
      ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel N) := by
  rw [mem_finiteLevelZero_iff]
  have hcoe : ∀ (γ : GL (Fin 2) ℚ),
      (Matrix.GeneralLinearGroup.map (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)) γ
        : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
      = (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)).mapMatrix (γ : Matrix (Fin 2) (Fin 2) ℚ) :=
    fun γ => Matrix.ext fun i j => Matrix.GeneralLinearGroup.map_apply _ i j γ
  rw [hcoe δ, ← Matrix.GeneralLinearGroup.map_inv, hcoe δ⁻¹]
  exact ⟨isLevelZeroMatrix_mapMatrix_of_int_entries hN _ hδ hlow,
    isLevelZeroMatrix_mapMatrix_of_int_entries hN _ hδ' hlow'⟩

end Rational

end NewvectorLineB

namespace NewvectorLineC

open NumberField NumberField.AdelicLevel AdelicDock AutomorphicForm IsDedekindDomain
open scoped ModularForm

section GlobalPointsLemmas

private theorem isReal_rat_infinitePlace (v : InfinitePlace ℚ) : v.IsReal := IsTotallyReal.isReal v

private noncomputable def ratArchHom : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) →* GL (Fin 2) ℝ :=
  (Matrix.GeneralLinearGroup.map
    (InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default)).toRingHom).comp
    ((archComponent ℚ default).comp (glArch (𝓞 ℚ) ℚ))

private theorem ratArchHom_apply (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    ratArchHom g = LanglandsTunnell.ratArchGL2 g := rfl

theorem ratArch_mul (g g' : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    LanglandsTunnell.ratArchGL2 (g * g')
      = LanglandsTunnell.ratArchGL2 g * LanglandsTunnell.ratArchGL2 g' := by
  rw [← ratArchHom_apply, ← ratArchHom_apply, ← ratArchHom_apply, map_mul]

theorem ratArch_inv (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    LanglandsTunnell.ratArchGL2 g⁻¹ = (LanglandsTunnell.ratArchGL2 g)⁻¹ := by
  rw [← ratArchHom_apply, ← ratArchHom_apply, map_inv]

theorem ratArch_eq_one_of_glArch_eq_one {u : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)} (hu : glArch (𝓞 ℚ) ℚ u = 1) :
    LanglandsTunnell.ratArchGL2 u = 1 := by
  unfold LanglandsTunnell.ratArchGL2
  rw [hu, map_one, map_one]

theorem ratArch_finEmbed (u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    LanglandsTunnell.ratArchGL2 (finEmbed (𝓞 ℚ) ℚ u) = 1 :=
  ratArch_eq_one_of_glArch_eq_one (glArch_finEmbed (𝓞 ℚ) ℚ u)

theorem ratArch_globalPoints (γ : GL (Fin 2) ℚ) :
    LanglandsTunnell.ratArchGL2 (globalPoints (𝓞 ℚ) ℚ γ) = Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) γ := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change ((InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default)).toRingHom.comp
      ((archEval ℚ default).comp ((adeleArch (𝓞 ℚ) ℚ).comp (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)))))
      ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j) = (Rat.castHom ℝ) ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j)
  rw [eq_ratCast, eq_ratCast]

theorem glFin_globalPoints_apply (γ : GL (Fin 2) ℚ) (i j : Fin 2) :
    (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j
      = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j) := rfl

end GlobalPointsLemmas

private theorem gl_ext_of_arch_fin {x y : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)}
    (h₁ : glArch (𝓞 ℚ) ℚ x = glArch (𝓞 ℚ) ℚ y) (h₂ : glFin (𝓞 ℚ) ℚ x = glFin (𝓞 ℚ) ℚ y) : x = y := by
  refine Units.ext (Matrix.ext fun a b => Prod.ext ?_ ?_)
  · exact congrArg (fun g : GL (Fin 2) (InfiniteAdeleRing ℚ) => (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) a b) h₁
  · exact congrArg
      (fun g : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) => (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) a b) h₂

theorem finEmbed_mul_comm_of_glFin_eq_one {h : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)} (hh : glFin (𝓞 ℚ) ℚ h = 1)
    (u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    finEmbed (𝓞 ℚ) ℚ u * h = h * finEmbed (𝓞 ℚ) ℚ u := by
  refine gl_ext_of_arch_fin ?_ ?_
  · rw [map_mul, map_mul, glArch_finEmbed, one_mul, mul_one]
  · rw [map_mul, map_mul, glFin_finEmbed, hh, one_mul, mul_one]

noncomputable def archPart (γ : GL (Fin 2) ℚ) : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) :=
  globalPoints (𝓞 ℚ) ℚ γ * (finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ)))⁻¹

theorem glFin_archPart (γ : GL (Fin 2) ℚ) : glFin (𝓞 ℚ) ℚ (archPart γ) = 1 := by
  rw [archPart, map_mul, map_inv, glFin_finEmbed, mul_inv_cancel]

theorem ratArch_archPart (γ : GL (Fin 2) ℚ) :
    LanglandsTunnell.ratArchGL2 (archPart γ) = Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) γ := by
  rw [archPart, ratArch_mul, ratArch_inv, ratArch_finEmbed, inv_one, mul_one, ratArch_globalPoints]

theorem glFin_archPart_mul {h : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)} (hh : glFin (𝓞 ℚ) ℚ h = 1) (γ : GL (Fin 2) ℚ) :
    glFin (𝓞 ℚ) ℚ (archPart γ * h) = 1 := by
  rw [map_mul, glFin_archPart, hh, one_mul]

theorem ratArch_archPart_mul (h : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) (γ : GL (Fin 2) ℚ) :
    LanglandsTunnell.ratArchGL2 (archPart γ * h)
      = Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) γ * LanglandsTunnell.ratArchGL2 h := by
  rw [ratArch_mul, ratArch_archPart]

theorem σ_apply_of_det_pos {g : GL (Fin 2) ℝ} (hg : 0 < (g.det : ℝ)) (z : ℂ) :
    UpperHalfPlane.σ g z = z := by
  rw [UpperHalfPlane.σ, if_pos hg]
  rfl

private theorem continuous_denom (A : GL (Fin 2) ℝ) : Continuous fun τ : UpperHalfPlane => UpperHalfPlane.denom A τ := by
  unfold UpperHalfPlane.denom
  exact (continuous_const.mul UpperHalfPlane.continuous_coe).add continuous_const

theorem continuous_slash {f : UpperHalfPlane → ℂ} (hf : Continuous f) (k : ℤ) (A : GL (Fin 2) ℝ) :
    Continuous (f ∣[k] A) := by
  have h1 : Continuous fun τ : UpperHalfPlane => UpperHalfPlane.σ A (f (A • τ)) :=
    (UpperHalfPlane.σ A).continuous.comp (hf.comp (continuous_const_smul A))
  have h2 : Continuous fun τ : UpperHalfPlane => UpperHalfPlane.denom A τ ^ (-k) :=
    (continuous_denom A).zpow₀ _ fun τ => Or.inl (UpperHalfPlane.denom_ne_zero A τ)
  have h3 : Continuous fun τ : UpperHalfPlane =>
      UpperHalfPlane.σ A (f (A • τ)) * |A.det.val| ^ (k - 1) * UpperHalfPlane.denom A τ ^ (-k) :=
    (h1.mul continuous_const).mul h2
  convert h3 using 1
  rfl

private theorem dense_ratPoints :
    Dense (((↑) : UpperHalfPlane → ℂ) ⁻¹'
      {w : ℂ | w.re ∈ Set.range ((↑) : ℚ → ℝ) ∧ w.im ∈ Set.range ((↑) : ℚ → ℝ)}) := by
  have h1 : Dense (Set.range ((↑) : ℚ → ℝ) ×ˢ Set.range ((↑) : ℚ → ℝ)) :=
    Rat.denseRange_cast.prod Rat.denseRange_cast
  have h2 : {w : ℂ | w.re ∈ Set.range ((↑) : ℚ → ℝ) ∧ w.im ∈ Set.range ((↑) : ℚ → ℝ)} =
      Complex.equivRealProdCLM ⁻¹' (Set.range ((↑) : ℚ → ℝ) ×ˢ Set.range ((↑) : ℚ → ℝ)) := by
    ext w; simp [Set.mem_prod]
  have hS : Dense {w : ℂ | w.re ∈ Set.range ((↑) : ℚ → ℝ) ∧ w.im ∈ Set.range ((↑) : ℚ → ℝ)} := by
    rw [h2]; exact h1.preimage Complex.equivRealProdCLM.toHomeomorph.isOpenMap
  exact hS.preimage UpperHalfPlane.isOpenEmbedding_coe.isOpenMap

private theorem exists_glFin_eq_one_and_smul_I_eq (z : UpperHalfPlane) (hx : (z : ℂ).re ∈ Set.range ((↑) : ℚ → ℝ))
    (hy : (z : ℂ).im ∈ Set.range ((↑) : ℚ → ℝ)) :
    ∃ h : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ h = 1 ∧ LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ ∧
      LanglandsTunnell.ratArchGL2 h • UpperHalfPlane.I = z := by
  obtain ⟨x, hx⟩ := hx
  obtain ⟨y, hy⟩ := hy
  have hy0 : (0 : ℝ) < y := by rw [hy]; exact z.im_pos
  have hyq : (0 : ℚ) < y := by exact_mod_cast hy0
  let A : Matrix (Fin 2) (Fin 2) ℚ := !![y, x; 0, 1]
  have hdetA : A.det = y := by simp [A, Matrix.det_fin_two_of]
  let γ : GL (Fin 2) ℚ := Matrix.GeneralLinearGroup.mkOfDetNeZero A (by rw [hdetA]; exact hyq.ne')
  let h : AdelicGL2 (𝓞 ℚ) ℚ :=
    globalPoints (𝓞 ℚ) ℚ γ * finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ))⁻¹
  have hfin : glFin (𝓞 ℚ) ℚ h = 1 := by
    simp only [h, map_mul, glFin_finEmbed, mul_inv_cancel]
  have hP : LanglandsTunnell.ratArchGL2 h = Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) γ := by
    simp only [h, ratArch_mul, ratArch_finEmbed, mul_one, ratArch_globalPoints]
  have hPmat : ((LanglandsTunnell.ratArchGL2 h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(y : ℝ), (x : ℝ); 0, 1] := by
    rw [hP]
    ext i j
    change (Rat.castHom ℝ) (A i j) = _
    fin_cases i <;> fin_cases j <;> simp [A]
  have hdetP : ((LanglandsTunnell.ratArchGL2 h).det.val : ℝ) = y := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hPmat, Matrix.det_fin_two_of]; ring
  have hdetpos : (0 : ℝ) < (LanglandsTunnell.ratArchGL2 h).det.val := by rw [hdetP]; exact hy0
  refine ⟨h, hfin, (Matrix.mem_glpos _).mpr hdetpos, ?_⟩
  rw [UpperHalfPlane.coe_re] at hx
  rw [UpperHalfPlane.coe_im] at hy
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_smul_of_det_pos hdetpos]
  simp only [UpperHalfPlane.num, UpperHalfPlane.denom, hPmat, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, UpperHalfPlane.coe_I,
    Complex.ofReal_zero, zero_mul, zero_add, Complex.ofReal_one, div_one]
  apply Complex.ext <;> simp [← hx, ← hy]

theorem eq_of_forall_slash_apply_I {F G : UpperHalfPlane → ℂ} (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ h : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ h = 1 → LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ →
      (F ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I
        = (G ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I) :
    F = G := by
  refine Continuous.ext_on dense_ratPoints hF hG ?_
  rintro z ⟨hx, hy⟩
  obtain ⟨h, hfin, hpos, hz⟩ := exists_glFin_eq_one_and_smul_I_eq z hx hy
  have hdet : (0 : ℝ) < (LanglandsTunnell.ratArchGL2 h).det.val := (Matrix.mem_glpos _).mp hpos
  have key := hFG h hfin hpos
  rw [ModularForm.slash_apply, ModularForm.slash_apply, σ_apply_of_det_pos hdet, σ_apply_of_det_pos hdet, hz]
    at key
  have hne : |(LanglandsTunnell.ratArchGL2 h).det.val| ^ ((2 : ℤ) - 1)
      * UpperHalfPlane.denom (LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I ^ (-(2 : ℤ)) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast zpow_ne_zero _ (abs_ne_zero.mpr hdet.ne'))
      (zpow_ne_zero _ (UpperHalfPlane.denom_ne_zero _ _))
  rw [mul_assoc, mul_assoc] at key
  exact mul_right_cancel₀ hne key

theorem glFin_globalPoints_eq_map (δ : GL (Fin 2) ℚ) :
    glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ δ)
      = Matrix.GeneralLinearGroup.map (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)) δ := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [glFin_globalPoints_apply]
  rfl

private theorem mapGL_entry_int (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (a b : Fin 2) :
    ∃ n : ℤ, ((Matrix.SpecialLinearGroup.mapGL ℚ γ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) a b = n :=
  ⟨γ a b, by simp [Matrix.SpecialLinearGroup.mapGL]⟩

private theorem mapGL_lowerLeft_of_mem_Gamma0 {N : ℕ} {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    ∃ m : ℤ, ((Matrix.SpecialLinearGroup.mapGL ℚ γ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = (N : ℚ) * m := by
  obtain ⟨m, hm⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (γ 1 0) N).mp (CongruenceSubgroup.Gamma0_mem.mp hγ)
  refine ⟨m, ?_⟩
  simp [Matrix.SpecialLinearGroup.mapGL, hm]

theorem glFin_globalPoints_mapGL_mem_finiteLevelZero {N : ℕ} (hN : N ≠ 0) {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ γ)) ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel N) := by
  rw [glFin_globalPoints_eq_map]
  refine NewvectorLineB.map_algebraMap_mem_finiteLevelZero hN _ (mapGL_entry_int γ) ?_
    (mapGL_lowerLeft_of_mem_Gamma0 hγ) ?_
  · rw [← map_inv]
    exact mapGL_entry_int γ⁻¹
  · rw [← map_inv]
    exact mapGL_lowerLeft_of_mem_Gamma0 (Subgroup.inv_mem _ hγ)

theorem map_castHom_mapGL (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (Matrix.SpecialLinearGroup.mapGL ℚ γ)
      = Matrix.SpecialLinearGroup.mapGL ℝ γ := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  simp [Matrix.SpecialLinearGroup.mapGL]

theorem mapGL_mem_GLPos (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) ∈ Matrix.GLPos (Fin 2) ℝ := by
  rw [Matrix.mem_glpos]
  simp [Matrix.SpecialLinearGroup.mapGL]

end NewvectorLineC

namespace NewvectorLineD

open NumberField NumberField.AdelicLevel AdelicDock AutomorphicForm IsDedekindDomain LocalNewvector

variable {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}

abbrev fn (y : AdelicSpan φ) : AdelicGL2 (𝓞 ℚ) ℚ → ℂ := (AdelicSpan.toFn φ y).toFn

theorem fn_csmul (c : ℂ) (y : AdelicSpan φ) (z : AdelicGL2 (𝓞 ℚ) ℚ) : fn (c • y) z = c * fn y z := rfl

theorem fn_padic_smul {q : ℕ} [Fact q.Prime] (x : GL (Fin 2) ℚ_[q]) (y : AdelicSpan φ) (z : AdelicGL2 (𝓞 ℚ) ℚ) :
    fn (x • y) z = fn y (z * padicToAdelic q x) := by
  rw [fn, fn, AdelicSpan.padic_smul_def, AdelicSpan.toFn_smul, AdelicFnCarrier.toFn_smul]

theorem fn_self (z : AdelicGL2 (𝓞 ℚ) ℚ) : fn (AdelicSpan.self φ) z = φ z := rfl

section LevelArith

theorem level_ne_zero {M : ℕ} (hM : M ≠ 0) (q a : ℕ) (hq : q.Prime) :
    q ^ max a 1 * (M / q ^ M.factorization q) ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ hq.ne_zero) (Nat.ordCompl_pos q hM).ne'

theorem dvd_level (M q a : ℕ) : q ∣ q ^ max a 1 * (M / q ^ M.factorization q) :=
  Dvd.dvd.mul_right (dvd_pow_self q (by omega)) _

theorem prime_dvd_level {M q a r : ℕ} (hq : q.Prime) (hr : r.Prime)
    (hrN : r ∣ q ^ max a 1 * (M / q ^ M.factorization q)) : r ∣ M ∨ r = q := by
  rcases (Nat.Prime.dvd_mul hr).mp hrN with h | h
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr hq).mp (hr.dvd_of_dvd_pow h))
  · exact Or.inl (h.trans (Nat.ordCompl_dvd M q))

theorem factorization_level_self {M : ℕ} (hM : M ≠ 0) (q a : ℕ) (hq : q.Prime) :
    (q ^ max a 1 * (M / q ^ M.factorization q)).factorization q = max a 1 := by
  rw [Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) (Nat.ordCompl_pos q hM).ne', Finsupp.coe_add,
    Pi.add_apply, hq.factorization_pow, Finsupp.single_eq_same, Nat.factorization_ordCompl,
    Finsupp.erase_same, add_zero]

theorem factorization_level_of_ne {M : ℕ} (hM : M ≠ 0) {q : ℕ} (a : ℕ) (hq : q.Prime) {ℓ : ℕ}
    (hℓq : ℓ ≠ q) : (q ^ max a 1 * (M / q ^ M.factorization q)).factorization ℓ = M.factorization ℓ := by
  rw [Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) (Nat.ordCompl_pos q hM).ne', Finsupp.coe_add,
    Pi.add_apply, hq.factorization_pow, Finsupp.single_eq_of_ne hℓq, Nat.factorization_ordCompl,
    Finsupp.erase_ne hℓq, zero_add]

theorem level_eq_self_of_dvd {M q : ℕ} (hM : M ≠ 0) (hq : q.Prime) (hqM : q ∣ M) :
    q ^ max (M.factorization q) 1 * (M / q ^ M.factorization q) = M := by
  have h1 : 1 ≤ M.factorization q := (hq.dvd_iff_one_le_factorization hM).mp hqM
  rw [max_eq_left h1]
  exact Nat.ordProj_mul_ordCompl_eq_self M q

end LevelArith

section HeckeReps

variable (p : ℕ) [hp : Fact p.Prime]

private noncomputable def repZ' (i : Fin (p + 1)) : Matrix (Fin 2) (Fin 2) ℤ_[p] :=
  if (i : ℕ) < p then !![1, ((i : ℕ) : ℤ_[p]); 0, (p : ℤ_[p])] else !![(p : ℤ_[p]), 0; 0, 1]

private theorem det_repZ' (i : Fin (p + 1)) : (repZ' p i).det = (p : ℤ_[p]) := by
  unfold repZ'
  split_ifs <;> simp [Matrix.det_fin_two_of]

noncomputable def ρQ' (i : Fin (p + 1)) : GL (Fin 2) ℚ_[p] :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero ((repZ' p i).map (algebraMap ℤ_[p] ℚ_[p])) (by
    rw [show (repZ' p i).map (algebraMap ℤ_[p] ℚ_[p]) = (algebraMap ℤ_[p] ℚ_[p]).mapMatrix (repZ' p i) from rfl,
      ← RingHom.map_det, det_repZ', map_natCast]
    exact_mod_cast hp.out.ne_zero)

theorem coe_ρQ' (i : Fin (p + 1)) :
    ((ρQ' p i : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) =
      if (i : ℕ) < p then !![(1 : ℚ_[p]), ((i : ℕ) : ℚ_[p]); 0, (p : ℚ_[p])]
      else !![(p : ℚ_[p]), 0; 0, 1] := by
  change (repZ' p i).map (algebraMap ℤ_[p] ℚ_[p]) = _
  unfold repZ'
  split_ifs
  · ext i j; fin_cases i <;> fin_cases j <;> simp
  · ext i j; fin_cases i <;> fin_cases j <;> simp

end HeckeReps

end NewvectorLineD

namespace NewvectorLineE

open NumberField NumberField.AdelicLevel AdelicDock AutomorphicForm IsDedekindDomain LocalNewvector HeckeCharacter

theorem isFiniteOrderHeckeChar_one :
    IsFiniteOrderHeckeChar ℚ (1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) where
  isIdeleClassChar := isIdeleClassChar_one ℚ
  continuous := by
    have h1 : (⇑(1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)) = fun _ => 1 := funext fun x => MonoidHom.one_apply x
    rw [h1]
    exact continuous_const
  isOfFinOrder := IsOfFinOrder.one

theorem admitsModulus_one (𝔣 : Ideal (𝓞 ℚ)) :
    AdmitsModulus ℚ (1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) 𝔣 :=
  fun _ _ _ => rfl

end NewvectorLineE

namespace NewvectorLineF

open NumberField NumberField.AdelicLevel AdelicDock AutomorphicForm IsDedekindDomain LocalNewvector HeckeCharacter
open NewvectorLineB NewvectorLineC NewvectorLineD NewvectorLineE
open scoped ModularForm MatrixGroups

theorem exists_gamma0_cuspForm_coe_eq {N M : ℕ} [NeZero N] (F : CuspForm (CongruenceSubgroup.Gamma1 N) 2)
    (hinv : ∀ γ ∈ CongruenceSubgroup.Gamma0 M,
      (⇑F) ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) = ⇑F) :
    ∃ G : CuspForm (CongruenceSubgroup.Gamma0 M) 2, ⇑G = ⇑F :=
  ⟨{ toFun := ⇑F
     slash_action_eq' := by
       rintro _ ⟨γ, hγ, rfl⟩
       exact hinv γ hγ
     holo' := CuspFormClass.holo F
     zero_at_cusps' := fun hc => CuspFormClass.zero_at_cusps F
       ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mpr (hc.mono (Subgroup.map_le_range _ _))) },
   rfl⟩

variable {M : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
variable {Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} {q : ℕ} [Fact q.Prime]

theorem slash_eq_self_of_levelZero {ψ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hM : M ≠ 0) {y : AdelicSpan ψ}
    {F : UpperHalfPlane → ℂ} (hF : Continuous F)
    (hread : ∀ h : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ h = 1 →
      LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ →
        fn y h = (F ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I)
    (hleft : ∀ (γ : GL (Fin 2) ℚ) (z : AdelicGL2 (𝓞 ℚ) ℚ), fn y (globalPoints (𝓞 ℚ) ℚ γ * z) = fn y z)
    (hK0 : ∀ u ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel M), ∀ z, fn y (z * finEmbed (𝓞 ℚ) ℚ u) = fn y z)
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ} (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) :
    F ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) = F := by
  set δ : GL (Fin 2) ℚ := Matrix.SpecialLinearGroup.mapGL ℚ γ with hδ
  refine eq_of_forall_slash_apply_I (continuous_slash hF 2 _) hF fun h hh hpos => ?_
  have hpos' : LanglandsTunnell.ratArchGL2 (archPart δ * h) ∈ Matrix.GLPos (Fin 2) ℝ := by
    rw [ratArch_archPart_mul, hδ, map_castHom_mapGL]
    exact Subgroup.mul_mem _ (mapGL_mem_GLPos γ) hpos
  have h1 := hread (archPart δ * h) (glFin_archPart_mul hh δ) hpos'
  rw [ratArch_archPart_mul, hδ, map_castHom_mapGL, SlashAction.slash_mul] at h1
  rw [← hδ] at h1
  have hG : glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ δ) ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel M) :=
    glFin_globalPoints_mapGL_mem_finiteLevelZero hM hγ
  have h2 : archPart δ * h
      = globalPoints (𝓞 ℚ) ℚ δ * (h * finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ δ))⁻¹) := by
    rw [archPart, mul_assoc, ← map_inv, finEmbed_mul_comm_of_glFin_eq_one hh]
  rw [h2, hleft, hK0 _ (Subgroup.inv_mem _ hG)] at h1
  rw [← h1, hread h hh hpos]

theorem exists_fn_eq_mul (hM : M ≠ 0) (hg : g.IsNewform) (hΦg : g.IsAdelicLiftOf Φ)
    (y : AdelicSpan (fnTwist ℚ (1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) Φ))
    (hy : y ∈ Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] =>
      x • AdelicSpan.self (fnTwist ℚ (1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) Φ)))
    (hfix : y ∈ fixedSubmodule (padicK1 q (M.factorization q))
      (AdelicSpan (fnTwist ℚ (1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) Φ)))
    (hcent : ∀ z : ℚ_[q]ˣ, centralGL q z • y = y) (hy₀ : y ≠ 0) :
    ∃ c : ℂ, fn y = fun x => c * Φ x := by
  haveI : NeZero M := ⟨hM⟩
  have hq : q.Prime := Fact.out
  set n : ℕ := M.factorization q with hndef
  set N : ℕ := q ^ max n 1 * (M / q ^ M.factorization q) with hNdef
  have hN : N ≠ 0 := level_ne_zero hM q n hq
  haveI : NeZero N := ⟨hN⟩
  have hqN : q ∣ N := dvd_level M q n

  have htriv : IsFiniteOrderHeckeChar ℚ (1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) := isFiniteOrderHeckeChar_one
  have htrivb : AdmitsModulus ℚ (1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (ratLevel (q ^ 0)) := admitsModulus_one _
  have hcent' : ∀ u : ℤ_[q]ˣ,
      centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom u) • y = ((1 : ℤ_[q]ˣ →* ℂˣ) u : ℂ) • y :=
    fun u => by rw [hcent, MonoidHom.one_apply, Units.val_one, one_smul]

  obtain ⟨ε, F, hF0, hεF, hεval, hFlift⟩ :=
    hΦg.exists_hasNebentypus_isAdelicLiftOfGamma1_of_mem_span_fnTwist_of_fixed q 1 htriv 0 htrivb n 1 y hy hy₀
      hfix hcent'

  obtain ⟨hleft, hK0N⟩ :=
    hΦg.apply_mul_finEmbed_levelZero_eq_of_mem_span_fnTwist_of_fixed q 1 (isIdeleClassChar_one ℚ) 0 htrivb n 1 y
      hy hfix hcent'

  have hsame : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ≠ padicPlace q →
      idealBound (𝓞 ℚ) (ratLevel M) v = idealBound (𝓞 ℚ) (ratLevel N) v := fun v hv =>
    (idealBound_ratLevel_eq_of_factorization_eq hN hM
      (fun ℓ _ hℓq => factorization_level_of_ne hM n hq hℓq) v hv).symm
  have hK0 : ∀ u ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel M), ∀ z, fn y (z * finEmbed (𝓞 ℚ) ℚ u) = fn y z := by
    intro u hu z
    obtain ⟨c, hcfin⟩ := exists_padicGL_map_eq_finComponent (q := q) hu
    have hentry : ∀ i j, padicRingEquiv q (((c : Matrix (Fin 2) (Fin 2) ℤ_[q]) i j : ℤ_[q]) : ℚ_[q])
        = ((u : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) (padicPlace q) := fun i j => by
      rw [← finComponent_apply, ← hcfin, padicGL_apply, Matrix.GeneralLinearGroup.map_apply,
        PadicInt.algebraMap_apply]
    set cQ : GL (Fin 2) ℚ_[q] := Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap ℤ_[q] ℚ_[q]) c
      with hcQ
    by_cases hn0 : n = 0
    ·
      have hcQmem : cQ ∈ padicK1 q n := by
        rw [hn0, LocalNewvector.mem_congruenceK1_iff]
        exact ⟨c, rfl, by simp, by simp⟩
      have hcy : cQ • y = y := mem_fixedSubmodule_iff.mp hfix _ hcQmem
      have hw : u * (padicToFinAdelic q cQ)⁻¹ ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel N) :=
        mul_padicToFinAdelic_inv_mem_finiteLevelZero hsame hu cQ hcfin.symm
      have hwq : finComponent (𝓞 ℚ) ℚ (padicPlace q) (u * (padicToFinAdelic q cQ)⁻¹) = 1 := by
        rw [map_mul, map_inv, finComponent_padicToFinAdelic_self q, hcfin, mul_inv_cancel]
      have hd : Valued.v ((((u * (padicToFinAdelic q cQ)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
            Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1) (padicPlace q)
            - padicRingEquiv q (((1 : ℤ_[q]ˣ) : ℤ_[q]) : ℚ_[q]))
          ≤ idealBound (𝓞 ℚ) (ratLevel N) (padicPlace q) := by
        rw [← finComponent_apply, hwq, Units.val_one, Matrix.one_apply_eq, Units.val_one, PadicInt.coe_one,
          map_one, sub_self, Valuation.map_zero]
        exact zero_le'
      have h1 := hK0N _ hw 1 hd (z * finEmbed (𝓞 ℚ) ℚ (u * (padicToFinAdelic q cQ)⁻¹))
      have hsplit : u = u * (padicToFinAdelic q cQ)⁻¹ * padicToFinAdelic q cQ := by group
      have h2 : fn y (z * finEmbed (𝓞 ℚ) ℚ (u * (padicToFinAdelic q cQ)⁻¹)) = fn y z := by
        have := hK0N _ hw 1 hd z
        rwa [MonoidHom.one_apply, Units.val_one, one_mul] at this
      calc fn y (z * finEmbed (𝓞 ℚ) ℚ u)
          = fn y (z * finEmbed (𝓞 ℚ) ℚ (u * (padicToFinAdelic q cQ)⁻¹) * padicToAdelic q cQ) := by
            conv_lhs => rw [hsplit]
            rw [map_mul, ← mul_assoc, ← padicToAdelic_apply]
        _ = fn (cQ • y) (z * finEmbed (𝓞 ℚ) ℚ (u * (padicToFinAdelic q cQ)⁻¹)) := (fn_padic_smul _ _ _).symm
        _ = fn y z := by rw [hcy, h2]
    ·
      have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      have hNM : N = M := by
        rw [hNdef, hndef]
        exact level_eq_self_of_dvd hM hq ((hq.dvd_iff_one_le_factorization hM).mpr hn1)
      have huN : u ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel N) := by rw [hNM]; exact hu
      have hc10 : (c : Matrix (Fin 2) (Fin 2) ℤ_[q]) 1 0 ∈ Ideal.span {(q : ℤ_[q]) ^ M.factorization q} := by
        rw [← valued_coe_le_idealBound_iff q hM, hentry]
        exact (mem_finiteLevelZero_iff.mp hu).1.lowerLeft (padicPlace q)
      have hc10_nonunit : ¬ IsUnit ((c : Matrix (Fin 2) (Fin 2) ℤ_[q]) 1 0) := fun hcu => by
        have hqdvd : (q : ℤ_[q]) ∣ (c : Matrix (Fin 2) (Fin 2) ℤ_[q]) 1 0 := by
          obtain ⟨k, hk⟩ := Ideal.mem_span_singleton.mp hc10
          exact ⟨(q : ℤ_[q]) ^ (M.factorization q - 1) * k, by
            rw [hk, ← mul_assoc, ← pow_succ']
            congr 2; omega⟩
        exact PadicInt.not_isUnit_iff.mpr ((PadicInt.norm_lt_one_iff_dvd _).mpr hqdvd) hcu
      have hc11u : IsUnit ((c : Matrix (Fin 2) (Fin 2) ℤ_[q]) 1 1) :=
        isUnit_entry_of_lowerLeft_mem c hc10_nonunit
      set d : ℤ_[q]ˣ := hc11u.unit with hddef
      have hdval : (d : ℤ_[q]) = (c : Matrix (Fin 2) (Fin 2) ℤ_[q]) 1 1 := hc11u.unit_spec
      have hd : Valued.v ((((u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
            Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1) (padicPlace q)
            - padicRingEquiv q ((d : ℤ_[q]) : ℚ_[q]))
          ≤ idealBound (𝓞 ℚ) (ratLevel N) (padicPlace q) := by
        rw [hdval, hentry 1 1, sub_self, Valuation.map_zero]
        exact zero_le'
      have := hK0N u huN d hd z
      rwa [MonoidHom.one_apply, Units.val_one, one_mul] at this

  have hread : ∀ h : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ h = 1 →
      LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ →
        fn y h = ((⇑F) ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I := hFlift.2.2
  have hslash : ∀ γ ∈ CongruenceSubgroup.Gamma0 M,
      (⇑F) ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) = ⇑F := fun γ hγ =>
    slash_eq_self_of_levelZero hM (CuspFormClass.holo F).continuous hread hleft hK0 hγ
  obtain ⟨G, hGF⟩ := exists_gamma0_cuspForm_coe_eq F hslash

  have hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M), ℓ ≠ q →
      CuspForm.heckeTLin 2 hℓ hℓM G = (ModularFormClass.qCoeff g ℓ) • G := by
    intro ℓ hℓ hℓM hℓq
    haveI : Fact ℓ.Prime := ⟨hℓ⟩
    have hℓN : ¬ ℓ ∣ N := fun h => by
      rcases prime_dvd_level hq hℓ h with h' | h'
      · exact hℓM h'
      · exact hℓq h'

    have hE : ∀ x, ∑ i : Fin (ℓ + 1), fn y (x * padicToAdelic ℓ (ρQ' ℓ i)⁻¹)
        = ModularFormClass.qCoeff g ℓ * fn y x := fun x => by
      have := CuspForm.IsNormalizedEigenform.sum_apply_padicToAdelic_eq_mul_of_mem_span_fnTwist hg.1 Φ hΦg q 1
        0 htrivb ℓ hℓM hℓq (ρQ' ℓ) (coe_ρQ' ℓ) y hy x
      rwa [MonoidHom.one_apply, Units.val_one, inv_one, one_mul] at this

    have hℓu : ‖(ℓ : ℚ_[q])‖ = 1 :=
      Padic.norm_natCast_eq_one_iff.mpr ((Nat.coprime_primes hq hℓ).mpr (Ne.symm hℓq))
    set t : ℤ_[q]ˣ := PadicInt.mkUnits hℓu with htdef
    have ht : ((t : ℤ_[q]) : ℚ_[q]) = ℓ := by rw [htdef, PadicInt.mkUnits_eq]
    have hεℓ : ε (ℓ : ZMod N) = 1 := by
      have := hεval ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓN) t ht
      rw [this, MonoidHom.one_apply, inv_one, Units.val_one]

    have hcoef : ∀ m : ℕ, ModularFormClass.qCoeff F (ℓ * m) +
        (ℓ : ℂ) ^ ((2 : ℤ) - 1) * (if ℓ ∣ m then ModularFormClass.qCoeff F (m / ℓ) else 0) =
          ModularFormClass.qCoeff g ℓ * ModularFormClass.qCoeff F m := fun m => by
      have hTm := CuspForm.HasNebentypus.qCoeff_hecke_eq_of_isAdelicLiftOfGamma1_of_sum_apply_padicToAdelic_eq
        hεF _ hFlift ℓ hℓN (ρQ' ℓ) (coe_ρQ' ℓ) _ (fun h _ _ => hE h) m
      rwa [hεℓ, one_mul, one_mul] at hTm
    refine (CuspForm.heckeTLin_apply_eq_smul_iff 2 hℓ hℓM G (ModularFormClass.qCoeff g ℓ)).mpr fun m => ?_
    rw [ModularForm.coeffHeckeT, hGF, mul_comm m ℓ, ← hcoef m]
    congr 1
    split_ifs <;> simp

  have hmem : G ∈ ℂ ∙ g := by
    rw [← hg.iInf_eigenspace_heckeTLin_eq_span_singleton {q}, Submodule.mem_iInf]
    intro ℓ
    exact Module.End.mem_eigenspace_iff.mpr
      (hT ℓ.1 ℓ.2.1 ℓ.2.2.1 (fun h => ℓ.2.2.2 (Finset.mem_singleton.mpr h)))
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem

  refine ⟨c, ?_⟩
  refine AutomorphicForm.ext_of_invariant_of_forall_glFin_eq_one_rat (ratLevel_ne_bot hM) hleft
    (fun γ x => by rw [hΦg.left_inv]) (fun u hu z => hK0 u (finiteLevelOne_le_finiteLevelZero _ _ _ hu) z)
    (fun u hu x => by rw [hΦg.level_inv u hu]) fun h hh hpos => ?_
  rw [hread h hh hpos, ← hGF, ← hc, CuspForm.IsGLPos.coe_smul, ModularForm.smul_slash, Pi.smul_apply,
    σ_apply_of_det_pos ((Matrix.mem_glpos _).mp hpos), smul_eq_mul, hΦg.apply_eq h hh hpos]

theorem exists_eq_smul_self (hM : M ≠ 0) (hg : g.IsNewform) (hΦg : g.IsAdelicLiftOf Φ)
    (y : AdelicSpan (fnTwist ℚ (1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) Φ))
    (hy : y ∈ Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] =>
      x • AdelicSpan.self (fnTwist ℚ (1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) Φ)))
    (hfix : y ∈ fixedSubmodule (padicK1 q (M.factorization q))
      (AdelicSpan (fnTwist ℚ (1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) Φ)))
    (hcent : ∀ z : ℚ_[q]ˣ, centralGL q z • y = y) :
    ∃ c : ℂ, y = c • AdelicSpan.self (fnTwist ℚ (1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) Φ) := by
  by_cases hy₀ : y = 0
  · exact ⟨0, by rw [hy₀, zero_smul]⟩
  obtain ⟨c, hc⟩ := exists_fn_eq_mul hM hg hΦg y hy hfix hcent hy₀
  refine ⟨c, AdelicSpan.ext _ (AdelicFnCarrier.ext fun x => ?_)⟩
  change fn y x = fn (c • AdelicSpan.self _) x
  rw [hc, fn_csmul, fn_self, fnTwist_one]

theorem exists_smul_add_smul_eq_zero (hM : M ≠ 0) (hg : g.IsNewform) (hΦg : g.IsAdelicLiftOf Φ)
    {Ψ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hΨ : fnTwist ℚ (1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) Φ = Ψ)
    (y₁ y₂ : AdelicSpan Ψ)
    (hy₁ : y₁ ∈ Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • AdelicSpan.self Ψ))
    (hy₂ : y₂ ∈ Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • AdelicSpan.self Ψ))
    (hfix₁ : y₁ ∈ fixedSubmodule (padicK1 q (M.factorization q)) (AdelicSpan Ψ))
    (hfix₂ : y₂ ∈ fixedSubmodule (padicK1 q (M.factorization q)) (AdelicSpan Ψ))
    (hcent₁ : ∀ z : ℚ_[q]ˣ, centralGL q z • y₁ = y₁)
    (hcent₂ : ∀ z : ℚ_[q]ˣ, centralGL q z • y₂ = y₂) :
    ∃ c₁ c₂ : ℂ, (c₁ ≠ 0 ∨ c₂ ≠ 0) ∧ c₁ • y₁ + c₂ • y₂ = 0 := by
  subst hΨ
  obtain ⟨a₁, ha₁⟩ := exists_eq_smul_self hM hg hΦg y₁ hy₁ hfix₁ hcent₁
  obtain ⟨a₂, ha₂⟩ := exists_eq_smul_self hM hg hΦg y₂ hy₂ hfix₂ hcent₂
  by_cases h₂ : a₂ = 0
  · refine ⟨0, 1, Or.inr one_ne_zero, ?_⟩
    rw [ha₂, h₂, zero_smul, zero_smul, smul_zero, add_zero]
  · refine ⟨a₂, -a₁, Or.inl h₂, ?_⟩
    rw [ha₁, ha₂, smul_smul, smul_smul, ← add_smul, mul_comm a₂ a₁, neg_mul, add_neg_cancel, zero_smul]

end NewvectorLineF

open NewvectorLineF NumberField AutomorphicForm LocalNewvector in
theorem solution
    {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hg : g.IsNewform)
    (q : ℕ) [Fact q.Prime]
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hΦg : g.IsAdelicLiftOf Φ)
    (y₁ y₂ : LocalNewvector.AdelicSpan Φ)
    (hy₁ : y₁ ∈ Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self Φ))
    (hy₂ : y₂ ∈ Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self Φ))
    (hfix₁ : y₁ ∈ LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 q (M.factorization q))
      (LocalNewvector.AdelicSpan Φ))
    (hfix₂ : y₂ ∈ LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 q (M.factorization q))
      (LocalNewvector.AdelicSpan Φ))
    (hcent₁ : ∀ z : ℚ_[q]ˣ, LocalNewvector.centralGL q z • y₁ = y₁)
    (hcent₂ : ∀ z : ℚ_[q]ˣ, LocalNewvector.centralGL q z • y₂ = y₂) :
    ∃ c₁ c₂ : ℂ, (c₁ ≠ 0 ∨ c₂ ≠ 0) ∧ c₁ • y₁ + c₂ • y₂ = 0 :=
  exists_smul_add_smul_eq_zero (NeZero.ne M) hg hΦg (fnTwist_one ℚ Φ) y₁ y₂ hy₁ hy₂ hfix₁ hfix₂ hcent₁ hcent₂

end S_CuspForm_IsNewform_exists_smul_add_smul_eq_zero_of_mem_span_of_mem_fixedSubmodule_padicK1_of_centralGL_smul_eq
end P2MW
export P2MW.S_CuspForm_IsNewform_exists_smul_add_smul_eq_zero_of_mem_span_of_mem_fixedSubmodule_padicK1_of_centralGL_smul_eq (solution)
