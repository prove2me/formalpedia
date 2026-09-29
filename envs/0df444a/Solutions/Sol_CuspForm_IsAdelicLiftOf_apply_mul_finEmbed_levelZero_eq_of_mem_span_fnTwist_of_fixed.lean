-- Prove2me | solution 1 for CuspForm.IsAdelicLiftOf.apply_mul_finEmbed_levelZero_eq_of_mem_span_fnTwist_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/385a225f-67bd-5d3a-8bda-516f3ca671b4

import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_AutomorphicForm_FnTwist
import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_LocalNewvector_ConductorDatum
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Theorems.Thm_CuspForm_IsAdelicLiftOf_levelZero_inv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsAdelicLiftOf_apply_mul_finEmbed_levelZero_eq_of_mem_span_fnTwist_of_fixed

set_option autoImplicit false

open NumberField AdelicDock IsDedekindDomain

namespace DescentSupportA

private theorem coe_finComponent {R : Type*} [CommRing R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (w : HeightOneSpectrum R) (g : GL (Fin 2) (FiniteAdeleRing R K)) :
    ((AdelicLevel.finComponent R K w g) : Matrix (Fin 2) (Fin 2) (w.adicCompletion K))
      = (AdelicLevel.finAdeleEval R K w).mapMatrix
          (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) := by
  ext i j
  rw [AdelicLevel.finComponent_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
    AdelicLevel.finAdeleEval_apply]

private theorem glEq_of_forall_finComponent_eq {R : Type*} [CommRing R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {g h : GL (Fin 2) (FiniteAdeleRing R K)}
    (H : ∀ w : HeightOneSpectrum R, AdelicLevel.finComponent R K w g = AdelicLevel.finComponent R K w h) :
    g = h := by
  refine Matrix.GeneralLinearGroup.ext fun i j => congrFun (congrFun ?_ i) j
  refine matrix_eq_of_forall_mapMatrix_finAdeleEval_eq R K fun w => ?_
  rw [← coe_finComponent w g, ← coe_finComponent w h, H w]

private theorem commute_of_finComponent_eq_one (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ))
    {w x : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)} (hw : AdelicLevel.finComponent (𝓞 ℚ) ℚ v w = 1)
    (hx : ∀ w' : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ), w' ≠ v →
      AdelicLevel.finComponent (𝓞 ℚ) ℚ w' x = 1) :
    w * x = x * w := by
  refine glEq_of_forall_finComponent_eq fun w' => ?_
  rw [map_mul, map_mul]
  rcases eq_or_ne w' v with rfl | hw'
  · rw [hw, one_mul, mul_one]
  · rw [hx w' hw', mul_one, one_mul]

section S1

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

private theorem exists_finComponent_eq_padicGL_map (p : ℕ) [Fact p.Prime] (I : Ideal (𝓞 ℚ))
    {u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)} (hu : u ∈ AdelicLevel.finiteLevelOne (𝓞 ℚ) ℚ I) :
    ∃ c : GL (Fin 2) ℤ_[p],
      AdelicLevel.finComponent (𝓞 ℚ) ℚ (padicPlace p) u
        = padicGL p (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap ℤ_[p] ℚ_[p]) c) := by
  obtain ⟨hu₁, hu₂⟩ := AdelicLevel.mem_finiteLevelOne_iff.mp hu
  set cq : GL (Fin 2) ℚ_[p] := Matrix.GeneralLinearGroup.map (n := Fin 2)
    (padicRingEquiv p).symm.toRingHom (AdelicLevel.finComponent (𝓞 ℚ) ℚ (padicPlace p) u) with hcq

  have hcq_inv : padicGL p cq = AdelicLevel.finComponent (𝓞 ℚ) ℚ (padicPlace p) u :=
    Matrix.GeneralLinearGroup.ext fun i j => by
      rw [padicGL_apply, hcq, Matrix.GeneralLinearGroup.map_apply]
      exact RingEquiv.apply_symm_apply _ _

  have hex : ∀ (e : GL (Fin 2) ((padicPlace p).adicCompletion ℚ)),
      (∀ i j, (e : Matrix (Fin 2) (Fin 2) _) i j ∈ (padicPlace p).adicCompletionIntegers ℚ) →
      ∀ i j, ∃ r : ℤ_[p], algebraMap ℤ_[p] ℚ_[p] r
        = (Matrix.GeneralLinearGroup.map (n := Fin 2) (padicRingEquiv p).symm.toRingHom e
            : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j := fun e he i j => by
    rw [Matrix.GeneralLinearGroup.map_apply]
    exact ⟨⟨_, (norm_le_one_iff_mem p _).mpr
      ((RingEquiv.apply_symm_apply (padicRingEquiv p) _).symm ▸ he i j)⟩,
      (PadicInt.algebraMap_apply _).trans rfl⟩
  have hmem : ∀ i j, (AdelicLevel.finComponent (𝓞 ℚ) ℚ (padicPlace p) u
      : Matrix (Fin 2) (Fin 2) _) i j ∈ (padicPlace p).adicCompletionIntegers ℚ := fun i j => by
    rw [AdelicLevel.finComponent_apply]; exact hu₁.integral i j (padicPlace p)
  have hmem' : ∀ i j, (AdelicLevel.finComponent (𝓞 ℚ) ℚ (padicPlace p) u⁻¹
      : Matrix (Fin 2) (Fin 2) _) i j ∈ (padicPlace p).adicCompletionIntegers ℚ := fun i j => by
    rw [AdelicLevel.finComponent_apply]; exact hu₂.integral i j (padicPlace p)
  obtain ⟨c, hc⟩ := exists_glMap_eq (algebraMap ℤ_[p] ℚ_[p])
    (IsFractionRing.injective ℤ_[p] ℚ_[p]) cq (hcq ▸ hex _ hmem)
    (by rw [hcq, ← map_inv, ← map_inv]; exact hex _ hmem')
  exact ⟨c, hcq_inv ▸ congrArg (padicGL p) hc.symm⟩

end S1

end DescentSupportA

namespace DescentSupportB

open NumberField NumberField.AdelicLevel AdelicDock IsDedekindDomain

section S4c

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

private theorem padicPlace_injective {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (h : padicPlace p = padicPlace q) : p = q :=
  congrArg Subtype.val
    ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm.injective h)

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

private theorem idealBound_ratLevel_eq_of_factorization_eq {q : ℕ} [Fact q.Prime] {N M : ℕ}
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

end S4c

section S4a

private theorem exists_padicGL_map_eq_finComponent {q : ℕ} [Fact q.Prime] {I : Ideal (𝓞 ℚ)}
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
  obtain ⟨c, hc⟩ := DescentSupportA.exists_glMap_eq (algebraMap ℤ_[q] ℚ_[q])
    (IsFractionRing.injective ℤ_[q] ℚ_[q]) cq (hcq ▸ hex _ hmem)
    (by rw [hcq, ← map_inv, ← map_inv]; exact hex _ hmem')
  exact ⟨c, hc ▸ hcq_inv⟩

private theorem map_algebraMap_scalar_eq_centralGL {q : ℕ} [Fact q.Prime] (d : ℤ_[q]ˣ) :
    Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap ℤ_[q] ℚ_[q])
        (Units.map (algebraMap ℤ_[q] (Matrix (Fin 2) (Fin 2) ℤ_[q])).toMonoidHom d)
      = LocalNewvector.centralGL q (Units.map (algebraMap ℤ_[q] ℚ_[q]).toMonoidHom d) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Matrix.GeneralLinearGroup.map_apply]
  simp only [LocalNewvector.centralGL, Units.coe_map, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, Matrix.algebraMap_matrix_apply,
    apply_ite (algebraMap ℤ_[q] ℚ_[q]), map_zero]
  rfl

private theorem isUnit_entry_of_lowerLeft_mem {q : ℕ} [Fact q.Prime] (c : GL (Fin 2) ℤ_[q])
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

private theorem exists_finComponent_eq_centralGL_mul {q : ℕ} [Fact q.Prime] {N : ℕ} (hN : N ≠ 0)
    {u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)} (hu : u ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel N)) :
    ∃ (z : ℚ_[q]ˣ) (k : GL (Fin 2) ℚ_[q]), k ∈ LocalNewvector.padicK1 q (N.factorization q) ∧
      finComponent (𝓞 ℚ) ℚ (padicPlace q) u = padicGL q (LocalNewvector.centralGL q z * k) := by
  obtain ⟨c, hcfin⟩ := exists_padicGL_map_eq_finComponent (q := q) hu

  have hc10 : (c : Matrix (Fin 2) (Fin 2) ℤ_[q]) 1 0
      ∈ Ideal.span {(q : ℤ_[q]) ^ N.factorization q} := by
    rw [← valued_coe_le_idealBound_iff q hN]
    have hcoe : padicRingEquiv q (((c : Matrix (Fin 2) (Fin 2) ℤ_[q]) 1 0 : ℤ_[q]) : ℚ_[q])
        = (finComponent (𝓞 ℚ) ℚ (padicPlace q) u : Matrix (Fin 2) (Fin 2) _) 1 0 := by
      rw [← hcfin, padicGL_apply, Matrix.GeneralLinearGroup.map_apply, PadicInt.algebraMap_apply]
    rw [hcoe, finComponent_apply]
    exact (mem_finiteLevelZero_iff.mp hu).1.lowerLeft (padicPlace q)
  rcases eq_or_ne (N.factorization q) 0 with hfac | hfac
  ·
    refine ⟨1, Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap ℤ_[q] ℚ_[q]) c, ?_, ?_⟩
    · rw [hfac, LocalNewvector.padicK1_zero_eq_integralSubgroup,
        ← LocalNewvector.congruenceK1_zero_eq_integralSubgroup (K := ℚ_[q]) (q : ℤ_[q]),
        LocalNewvector.congruenceK1_zero]
      exact ⟨c, rfl⟩
    · rw [map_one, one_mul, hcfin]
  ·
    have hc10_nonunit : ¬ IsUnit ((c : Matrix (Fin 2) (Fin 2) ℤ_[q]) 1 0) := fun hcu => by
      have hqdvd : (q : ℤ_[q]) ∣ (c : Matrix (Fin 2) (Fin 2) ℤ_[q]) 1 0 := by
        obtain ⟨k, hk⟩ := Ideal.mem_span_singleton.mp hc10
        exact ⟨(q : ℤ_[q]) ^ (N.factorization q - 1) * k, by
          rw [hk, ← mul_assoc, ← pow_succ']
          congr 2; omega⟩
      exact PadicInt.not_isUnit_iff.mpr ((PadicInt.norm_lt_one_iff_dvd _).mpr hqdvd) hcu
    obtain ⟨d, hd⟩ := (isUnit_entry_of_lowerLeft_mem c hc10_nonunit)
    set sc : GL (Fin 2) ℤ_[q] :=
      Units.map (algebraMap ℤ_[q] (Matrix (Fin 2) (Fin 2) ℤ_[q])).toMonoidHom d with hsc
    set k' : GL (Fin 2) ℤ_[q] := sc⁻¹ * c with hk'

    have hsc_inv_coe : ((sc⁻¹ : GL (Fin 2) ℤ_[q]) : Matrix (Fin 2) (Fin 2) ℤ_[q])
        = (↑d⁻¹ : ℤ_[q]) • (1 : Matrix (Fin 2) (Fin 2) ℤ_[q]) := by
      rw [hsc, ← map_inv]
      simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
        Algebra.algebraMap_eq_smul_one]

    have hk'_row1 : ∀ j, (k' : Matrix (Fin 2) (Fin 2) ℤ_[q]) 1 j
        = (↑d⁻¹ : ℤ_[q]) * (c : Matrix (Fin 2) (Fin 2) ℤ_[q]) 1 j := fun j => by
      rw [hk', Units.val_mul, hsc_inv_coe, Matrix.smul_mul, one_mul, Matrix.smul_apply,
        smul_eq_mul]
    refine ⟨Units.map (algebraMap ℤ_[q] ℚ_[q]).toMonoidHom d,
      Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap ℤ_[q] ℚ_[q]) k', ?_, ?_⟩
    ·
      rw [LocalNewvector.mem_congruenceK1_iff]
      refine ⟨k', rfl, ?_, ?_⟩
      · rw [hk'_row1 0]; exact Ideal.mul_mem_left _ _ hc10
      · rw [hk'_row1 1, ← hd, d.inv_mul, sub_self]; exact Ideal.zero_mem _
    · rw [← map_algebraMap_scalar_eq_centralGL d, ← hsc, ← map_mul, hk', mul_inv_cancel_left,
        hcfin]

end S4a

section S4b

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

private theorem mul_padicToFinAdelic_inv_mem_finiteLevelZero {q : ℕ} [Fact q.Prime] {N M : ℕ}
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

end S4b

section S4d

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

private theorem map_algebraMap_mem_finiteLevelZero {N : ℕ} (hN : N ≠ 0) (δ : GL (Fin 2) ℚ)
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

end S4d

end DescentSupportB

namespace DescentEngine

open NumberField NumberField.AdelicLevel AdelicDock AutomorphicForm IsDedekindDomain LocalNewvector
open scoped ModularForm

variable {M : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}

private abbrev fn (y : AdelicSpan φ) : AdelicGL2 (𝓞 ℚ) ℚ → ℂ := (AdelicSpan.toFn φ y).toFn

private theorem fn_padic_smul_self {q : ℕ} [Fact q.Prime] (x : GL (Fin 2) ℚ_[q]) (z : AdelicGL2 (𝓞 ℚ) ℚ) :
    fn (x • AdelicSpan.self φ) z = φ (z * padicToAdelic q x) := by
  rw [fn, AdelicSpan.padic_smul_def, AdelicSpan.toFn_smul, AdelicFnCarrier.toFn_smul, AdelicSpan.toFn_self,
    AdelicFnCarrier.toFn_mk]

private theorem fn_add (y₁ y₂ : AdelicSpan φ) (z : AdelicGL2 (𝓞 ℚ) ℚ) : fn (y₁ + y₂) z = fn y₁ z + fn y₂ z := rfl

private theorem fn_csmul (c : ℂ) (y : AdelicSpan φ) (z : AdelicGL2 (𝓞 ℚ) ℚ) : fn (c • y) z = c * fn y z := rfl

private theorem fn_zero (z : AdelicGL2 (𝓞 ℚ) ℚ) : fn (0 : AdelicSpan φ) z = 0 := rfl

private theorem fn_padic_smul {q : ℕ} [Fact q.Prime] (x : GL (Fin 2) ℚ_[q]) (y : AdelicSpan φ) (z : AdelicGL2 (𝓞 ℚ) ℚ) :
    fn (x • y) z = fn y (z * padicToAdelic q x) := by
  rw [fn, fn, AdelicSpan.padic_smul_def, AdelicSpan.toFn_smul, AdelicFnCarrier.toFn_smul]

end DescentEngine

noncomputable section

namespace TwistEngineAux

open NumberField NumberField.AdelicLevel AdelicDock AutomorphicForm IsDedekindDomain LocalNewvector HeckeCharacter

section Places

private theorem padicPlace_ne_of_ne {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p ≠ q) :
    padicPlace p ≠ padicPlace q := by
  intro heq
  have h' := congrArg (fun v : HeightOneSpectrum (𝓞 ℚ) => (Rat.HeightOneSpectrum.primesEquiv v : ℕ)) heq
  simp only [padicPlace, Equiv.apply_symm_apply] at h'
  exact h h'

private theorem natGenerator_padicPlace (p : ℕ) [Fact p.Prime] :
    Rat.HeightOneSpectrum.natGenerator (padicPlace p) = p := by
  show (Rat.HeightOneSpectrum.primesEquiv (padicPlace p) : ℕ) = p
  rw [padicPlace, Equiv.apply_symm_apply]

private theorem natCast_mem_asIdeal_iff (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    ((n : ℕ) : 𝓞 ℚ) ∈ v.asIdeal ↔ Rat.HeightOneSpectrum.natGenerator v ∣ n := by
  rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff,
    show ((n : ℕ) : ℤ) = Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) ((n : ℕ) : 𝓞 ℚ) from (map_natCast _ n).symm]
  exact Ideal.apply_mem_of_equiv_iff.symm

private theorem eq_padicPlace_of_natCast_mem {q : ℕ} [hq : Fact q.Prime] {v : HeightOneSpectrum (𝓞 ℚ)}
    (hv : ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) : v = padicPlace q := by
  have h3 : Rat.HeightOneSpectrum.natGenerator v = q :=
    (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator v) hq.out).mp
      ((natCast_mem_asIdeal_iff v q).mp hv)
  unfold padicPlace
  rw [Equiv.eq_symm_apply]
  exact Subtype.ext h3

private theorem idealMultiplicity_ratLevel_pow_eq_zero {q : ℕ} [hq : Fact q.Prime] (b : ℕ)
    {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ≠ padicPlace q) :
    idealMultiplicity ℚ v (ratLevel (q ^ b)) = 0 := by
  unfold idealMultiplicity
  by_contra hne
  have hdvd : v.asIdeal ∣ ratLevel (q ^ b) :=
    (Associates.count_ne_zero_iff_dvd (ratLevel_ne_bot (pow_ne_zero b hq.out.ne_zero)) v.irreducible).mp hne
  rw [Ideal.dvd_iff_le] at hdvd
  have hmem : ((q ^ b : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := hdvd (by unfold ratLevel; exact Ideal.mem_span_singleton_self _)
  rw [Nat.cast_pow] at hmem
  exact hv (eq_padicPlace_of_natCast_mem (v.isPrime.mem_of_pow_mem b hmem))

private theorem natCast_natGenerator_ne_zero (v : HeightOneSpectrum (𝓞 ℚ)) :
    ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : 𝓞 ℚ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Rat.HeightOneSpectrum.prime_natGenerator v).ne_zero

private theorem prime_natCast_natGenerator (v : HeightOneSpectrum (𝓞 ℚ)) :
    Prime ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : 𝓞 ℚ) := by
  have hcast : ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : 𝓞 ℚ) =
      Rat.ringOfIntegersEquiv.symm ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : ℤ) :=
    (map_natCast (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) _).symm
  rw [hcast]
  exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr
    (Nat.prime_iff_prime_int.mp (Rat.HeightOneSpectrum.prime_natGenerator v))

private theorem asIdeal_eq_span_natGenerator (v : HeightOneSpectrum (𝓞 ℚ)) :
    v.asIdeal = Ideal.span {((Rat.HeightOneSpectrum.natGenerator v : ℕ) : 𝓞 ℚ)} := by
  have hmax : (Ideal.span {((Rat.HeightOneSpectrum.natGenerator v : ℕ) : 𝓞 ℚ)}).IsMaximal :=
    ((Ideal.span_singleton_prime (natCast_natGenerator_ne_zero v)).mpr (prime_natCast_natGenerator v)).isMaximal
      ((Ideal.span_singleton_eq_bot (α := 𝓞 ℚ)).not.mpr (natCast_natGenerator_ne_zero v))
  exact (hmax.eq_of_le v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).mpr
    ((natCast_mem_asIdeal_iff v _).mpr dvd_rfl))).symm

private theorem asIdeal_padicPlace (p : ℕ) [Fact p.Prime] :
    (padicPlace p).asIdeal = Ideal.span {((p : ℕ) : 𝓞 ℚ)} := by
  rw [asIdeal_eq_span_natGenerator, natGenerator_padicPlace]

private theorem valued_natCast (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    Valued.v ((n : ℕ) : v.adicCompletion ℚ) = v.intValuation ((n : ℕ) : 𝓞 ℚ) := by
  have h1 : ((n : ℕ) : v.adicCompletion ℚ) = algebraMap ℚ (v.adicCompletion ℚ) ((n : ℕ) : ℚ) :=
    (map_natCast (algebraMap ℚ (v.adicCompletion ℚ)) n).symm
  have h2 : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) ((n : ℕ) : ℚ)) = v.valuation ℚ ((n : ℕ) : ℚ) := by
    rw [HeightOneSpectrum.algebraMap_adicCompletion]
    exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
  rw [h1, h2, show ((n : ℕ) : ℚ) = algebraMap (𝓞 ℚ) ℚ ((n : ℕ) : 𝓞 ℚ) from (map_natCast (algebraMap (𝓞 ℚ) ℚ) _).symm,
    HeightOneSpectrum.valuation_of_algebraMap]

private theorem valued_natCast_self (p : ℕ) [hp : Fact p.Prime] :
    Valued.v ((p : ℕ) : (padicPlace p).adicCompletion ℚ) = WithZero.exp (-1 : ℤ) := by
  rw [valued_natCast]
  exact HeightOneSpectrum.intValuation_singleton (v := padicPlace p) (Nat.cast_ne_zero.mpr hp.out.ne_zero)
    (asIdeal_padicPlace p)

private theorem valued_natCast_of_ne (p : ℕ) [Fact p.Prime] {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ≠ padicPlace p) :
    Valued.v ((p : ℕ) : v.adicCompletion ℚ) = 1 := by
  rw [valued_natCast]
  exact HeightOneSpectrum.intValuation_eq_one_iff.mpr fun hmem => hv (eq_padicPlace_of_natCast_mem hmem)

private theorem natCast_prime_ne_zero (v : HeightOneSpectrum (𝓞 ℚ)) (p : ℕ) [hp : Fact p.Prime] :
    ((p : ℕ) : v.adicCompletion ℚ) ≠ 0 := by
  intro h
  have h1 := valued_natCast v p
  rw [h, Valuation.map_zero] at h1
  exact HeightOneSpectrum.intValuation_ne_zero v _ (Nat.cast_ne_zero.mpr hp.out.ne_zero) h1.symm

private def natUnitAt (v : HeightOneSpectrum (𝓞 ℚ)) (p : ℕ) [Fact p.Prime] : (v.adicCompletion ℚ)ˣ :=
  Units.mk0 _ (natCast_prime_ne_zero v p)

private theorem coe_natUnitAt (v : HeightOneSpectrum (𝓞 ℚ)) (p : ℕ) [Fact p.Prime] :
    ((natUnitAt v p : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = ((p : ℕ) : v.adicCompletion ℚ) := rfl

end Places

section Character

variable (η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)

private theorem apply_eq_one_of_admitsModulus {q : ℕ} [Fact q.Prime] {b : ℕ}
    (hηb : AdmitsModulus ℚ η (ratLevel (q ^ b))) (u : (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hu1 : (u : AdeleRing (𝓞 ℚ) ℚ).1 = 1)
    (hunit : ∀ v : HeightOneSpectrum (𝓞 ℚ), Valued.v ((u : AdeleRing (𝓞 ℚ) ℚ).2 v) = 1)
    (huq : (u : AdeleRing (𝓞 ℚ) ℚ).2 (padicPlace q) = 1) :
    η u = 1 := by
  refine hηb u hu1 fun v => ⟨hunit v, ?_⟩
  by_cases hv : v = padicPlace q
  · subst hv
    rw [huq, sub_self, map_zero]
    exact zero_le'
  · rw [idealMultiplicity_ratLevel_pow_eq_zero b hv, Nat.cast_zero, neg_zero, WithZero.exp_zero]
    calc Valued.v ((u : AdeleRing (𝓞 ℚ) ℚ).2 v - 1)
        ≤ max (Valued.v ((u : AdeleRing (𝓞 ℚ) ℚ).2 v)) (Valued.v (1 : (v.adicCompletion ℚ))) :=
          Valuation.map_sub _ _ _
      _ = 1 := by rw [hunit v, Valuation.map_one, max_self]

private theorem apply_finIncl_localUnit_eq_one {q : ℕ} [Fact q.Prime] {b : ℕ}
    (hηb : AdmitsModulus ℚ η (ratLevel (q ^ b))) (p : ℕ) [Fact p.Prime] (hpq : p ≠ q)
    (t : ((padicPlace p).adicCompletion ℚ)ˣ) (ht : Valued.v (t : (padicPlace p).adicCompletion ℚ) = 1) :
    η (Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ (padicPlace p) t)) = 1 := by
  refine apply_eq_one_of_admitsModulus η hηb _ ?_ ?_ ?_
  · exact finIncl_apply_fst (𝓞 ℚ) ℚ _
  · intro v
    simp only [Units.coe_map, finIncl_apply_snd]
    by_cases hv : v = padicPlace p
    · subst hv
      rw [localUnit_apply_self]
      exact ht
    · rw [localUnit_apply_of_ne _ _ _ _ hv, Valuation.map_one]
  · simp only [Units.coe_map, finIncl_apply_snd]
    exact localUnit_apply_of_ne _ _ _ _ (padicPlace_ne_of_ne hpq).symm

private theorem apply_finIncl_localUnit_natUnitAt {q : ℕ} [Fact q.Prime] {b : ℕ}
    (hηb : AdmitsModulus ℚ η (ratLevel (q ^ b))) (p : ℕ) [Fact p.Prime] (hpq : p ≠ q) :
    η (Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ (padicPlace p) (natUnitAt (padicPlace p) p))) =
      η (uniformizerIdele ℚ (padicPlace p)) := by
  have hsplit : natUnitAt (padicPlace p) p =
      uniformizerUnit ℚ (padicPlace p) * (natUnitAt (padicPlace p) p * (uniformizerUnit ℚ (padicPlace p))⁻¹) := by
    rw [mul_comm (uniformizerUnit ℚ (padicPlace p)), inv_mul_cancel_right]
  have hval : Valued.v ((natUnitAt (padicPlace p) p * (uniformizerUnit ℚ (padicPlace p))⁻¹ :
      ((padicPlace p).adicCompletion ℚ)ˣ) : (padicPlace p).adicCompletion ℚ) = 1 := by
    rw [Units.val_mul, Valuation.map_mul, Units.val_inv_eq_inv_val, map_inv₀, coe_natUnitAt, valued_natCast_self,
      valued_uniformizerUnit, mul_inv_cancel₀ WithZero.exp_ne_zero]
  rw [hsplit, map_mul, map_mul, map_mul, apply_finIncl_localUnit_eq_one η hηb p hpq _ hval, mul_one]
  rfl

end Character

section Principal

variable (η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)

private def compFin (w : HeightOneSpectrum (𝓞 ℚ)) : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* (w.adicCompletion ℚ)ˣ :=
  Units.map ((finAdeleEval (𝓞 ℚ) ℚ w).comp (adeleFin (𝓞 ℚ) ℚ)).toMonoidHom

private theorem coe_compFin (w : HeightOneSpectrum (𝓞 ℚ)) (u : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    ((compFin w u : (w.adicCompletion ℚ)ˣ) : w.adicCompletion ℚ) = (u : AdeleRing (𝓞 ℚ) ℚ).2 w := rfl

private def compArch : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* (InfiniteAdeleRing ℚ)ˣ :=
  Units.map (adeleArch (𝓞 ℚ) ℚ).toMonoidHom

private theorem coe_compArch (u : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    ((compArch u : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ) = (u : AdeleRing (𝓞 ℚ) ℚ).1 := rfl

private theorem apply_eq_one_of_comp {q : ℕ} [Fact q.Prime] {b : ℕ}
    (hηb : AdmitsModulus ℚ η (ratLevel (q ^ b))) (u : (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (h1 : compArch u = 1)
    (h2 : ∀ w : HeightOneSpectrum (𝓞 ℚ), Valued.v ((compFin w u : (w.adicCompletion ℚ)ˣ) : w.adicCompletion ℚ) = 1)
    (h3 : compFin (padicPlace q) u = 1) : η u = 1 := by
  refine apply_eq_one_of_admitsModulus η hηb u ?_ ?_ ?_
  · rw [← coe_compArch, h1, Units.val_one]
  · intro w
    rw [← coe_compFin]
    exact h2 w
  · rw [← coe_compFin, h3, Units.val_one]

end Principal

end TwistEngineAux

end

namespace TwistEngine

open NumberField NumberField.AdelicLevel AdelicDock AutomorphicForm IsDedekindDomain LocalNewvector HeckeCharacter
open DescentEngine TwistEngineAux

section DetFinEmbed

private theorem det_finEmbed_snd_apply (u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
    (w : HeightOneSpectrum (𝓞 ℚ)) :
    ((finEmbed (𝓞 ℚ) ℚ u).det : AdeleRing (𝓞 ℚ) ℚ).2 w
      = ((finComponent (𝓞 ℚ) ℚ w u).det : w.adicCompletion ℚ) := by
  have e1 : glFin (𝓞 ℚ) ℚ (finEmbed (𝓞 ℚ) ℚ u) = u := glFin_finEmbed (𝓞 ℚ) ℚ u
  have e2 := congrArg (fun g : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) =>
    ((finComponent (𝓞 ℚ) ℚ w g).det : w.adicCompletion ℚ)) e1
  simp only [glFin, finComponent, Matrix.GeneralLinearGroup.map_det, Units.coe_map] at e2 ⊢
  exact e2

private theorem det_finEmbed_fst (u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    ((finEmbed (𝓞 ℚ) ℚ u).det : AdeleRing (𝓞 ℚ) ℚ).1 = 1 := by
  have e1 : glArch (𝓞 ℚ) ℚ (finEmbed (𝓞 ℚ) ℚ u) = 1 := glArch_finEmbed (𝓞 ℚ) ℚ u
  have e2 := congrArg (fun g : GL (Fin 2) (InfiniteAdeleRing ℚ) => (g.det : InfiniteAdeleRing ℚ)) e1
  simp only [glArch, Matrix.GeneralLinearGroup.map_det, Units.coe_map, map_one, Units.val_one] at e2
  exact e2

private theorem valued_det_finComponent_eq_one_of_mem_finiteLevelZero
    {N : Ideal (𝓞 ℚ)} {u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (hu : u ∈ finiteLevelZero (𝓞 ℚ) ℚ N) (w : HeightOneSpectrum (𝓞 ℚ)) :
    Valued.v ((finComponent (𝓞 ℚ) ℚ w u).det : w.adicCompletion ℚ) = 1 := by
  have hle : ∀ g : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ),
      IsLevelZeroMatrix (𝓞 ℚ) ℚ N (g : Matrix _ _ _) →
      Valued.v ((finComponent (𝓞 ℚ) ℚ w g).det : w.adicCompletion ℚ) ≤ 1 := by
    intro g hg
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
    refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_)
    all_goals
      rw [Valuation.map_mul]
      refine mul_le_one' ?_ ?_
      all_goals
        rw [finComponent_apply]
        exact valued_apply_le_one (hg.integral _ _) w
  have h1 : Valued.v ((finComponent (𝓞 ℚ) ℚ w u).det : w.adicCompletion ℚ) ≤ 1 := hle u hu.1
  have h2 : Valued.v ((finComponent (𝓞 ℚ) ℚ w u⁻¹).det : w.adicCompletion ℚ) ≤ 1 := hle u⁻¹ hu.2
  refine le_antisymm h1 ?_
  have hprod : Valued.v ((finComponent (𝓞 ℚ) ℚ w u).det : w.adicCompletion ℚ)
      * Valued.v ((finComponent (𝓞 ℚ) ℚ w u⁻¹).det : w.adicCompletion ℚ) = 1 := by
    rw [← Valuation.map_mul, ← Units.val_mul, ← map_mul, ← map_mul, mul_inv_cancel,
      map_one, map_one, Units.val_one, map_one]
  calc (1 : _) = _ := hprod.symm
    _ ≤ Valued.v ((finComponent (𝓞 ℚ) ℚ w u).det : w.adicCompletion ℚ) * 1 := by gcongr
    _ = _ := mul_one _

private theorem padicToFinAdelic_centralGL_mem_finiteLevelZero (q : ℕ) [Fact q.Prime]
    (M : ℕ) (u : ℤ_[q]ˣ) :
    padicToFinAdelic q (centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom u))
      ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel M) := by
  have hbody : ∀ u' : ℤ_[q]ˣ, IsLevelZeroMatrix (𝓞 ℚ) ℚ (ratLevel M)
      ((padicToFinAdelic q (centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom u'))).val) := by
    intro u'
    refine ⟨fun i j w => ?_, ?_⟩
    · rw [padicToFinAdelic_apply, coe_localEmbed]
      by_cases hw : w = padicPlace q
      · subst hw
        rw [localMat_apply_self, padicGL_apply]
        show padicRingEquiv q
            ((algebraMap ℚ_[q] (Matrix (Fin 2) (Fin 2) ℚ_[q])) ((u' : ℤ_[q]) : ℚ_[q]) i j)
          ∈ (padicPlace q).adicCompletionIntegers ℚ
        rw [Matrix.algebraMap_matrix_apply]
        split_ifs
        · exact padicRingEquiv_coe_mem q (u' : ℤ_[q])
        · rw [map_zero]; exact zero_mem _
      · rw [localMat_apply_of_ne (𝓞 ℚ) ℚ (padicPlace q) _ i j hw, Matrix.one_apply]
        split_ifs
        · exact one_mem _
        · exact zero_mem _
    · intro w
      rw [padicToFinAdelic_apply, coe_localEmbed]
      by_cases hw : w = padicPlace q
      · subst hw
        rw [localMat_apply_self, padicGL_apply]
        show Valued.v (padicRingEquiv q
            ((algebraMap ℚ_[q] (Matrix (Fin 2) (Fin 2) ℚ_[q])) ((u' : ℤ_[q]) : ℚ_[q]) 1 0)) ≤ _
        rw [Matrix.algebraMap_matrix_apply, if_neg (by decide), map_zero, map_zero]
        exact zero_le'
      · rw [localMat_apply_of_ne (𝓞 ℚ) ℚ (padicPlace q) _ 1 0 hw,
          Matrix.one_apply_ne (by decide), map_zero]
        exact zero_le'
  refine mem_finiteLevelZero_iff.mpr ⟨hbody u, ?_⟩
  have hinv : (padicToFinAdelic q (centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom u)))⁻¹
      = padicToFinAdelic q (centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom u⁻¹)) := by
    rw [← map_inv, ← map_inv, ← map_inv]
  rw [hinv]
  exact hbody u⁻¹

end DetFinEmbed

section TwistSubLemmas

variable (η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)

private theorem eta_det_finEmbed_eq_one_of_finiteLevelZero_of_qtrivial
    {q : ℕ} [Fact q.Prime] {b : ℕ} (hηb : AdmitsModulus ℚ η (ratLevel (q ^ b)))
    {N : ℕ} (hN : N ≠ 0) {u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (hu : u ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel N))
    (hqtriv : finComponent (𝓞 ℚ) ℚ (padicPlace q) u = 1) :
    (η (finEmbed (𝓞 ℚ) ℚ u).det : ℂ) = 1 := by
  have _ := hN
  rw [show η (finEmbed (𝓞 ℚ) ℚ u).det = 1 from ?_, Units.val_one]
  refine apply_eq_one_of_comp η hηb _ ?_ ?_ ?_
  · ext; rw [coe_compArch, det_finEmbed_fst, Units.val_one]
  · intro w; rw [coe_compFin, det_finEmbed_snd_apply]
    exact valued_det_finComponent_eq_one_of_mem_finiteLevelZero hu w
  · ext; rw [coe_compFin, det_finEmbed_snd_apply, hqtriv, map_one, Units.val_one]

private theorem fnTwist_ne_zero_iff (Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) :
    fnTwist ℚ η Φ ≠ 0 ↔ Φ ≠ 0 := by
  refine not_congr ⟨fun h => ?_, fun h => ?_⟩
  · ext g
    have hg : chiDet (𝓞 ℚ) ℚ η g * Φ g = 0 := by have := congrFun h g; simpa [fnTwist_apply] using this
    exact (mul_eq_zero.mp hg).resolve_left (by exact_mod_cast Units.ne_zero _)
  · ext g; simp only [fnTwist_apply, h, Pi.zero_apply, mul_zero]

private theorem fnTwist_levelZero_inv_of_qtrivial {q : ℕ} [Fact q.Prime] {b : ℕ}
    (hηb : AdmitsModulus ℚ η (ratLevel (q ^ b)))
    {Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} {M : ℕ} (hM : M ≠ 0)
    (hK₀ : ∀ u ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel M), ∀ x, Φ (x * finEmbed (𝓞 ℚ) ℚ u) = Φ x)
    {u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (hu : u ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel M))
    (huq : finComponent (𝓞 ℚ) ℚ (padicPlace q) u = 1) (x : AdelicGL2 (𝓞 ℚ) ℚ) :
    fnTwist ℚ η Φ (x * finEmbed (𝓞 ℚ) ℚ u) = fnTwist ℚ η Φ x := by
  simp only [fnTwist_apply, hK₀ u hu x, chiDet, map_mul, Units.val_mul,
    eta_det_finEmbed_eq_one_of_finiteLevelZero_of_qtrivial η hηb hM hu huq, mul_one]

end TwistSubLemmas

end TwistEngine

namespace TwistEngine

open NumberField NumberField.AdelicLevel AdelicDock AutomorphicForm IsDedekindDomain LocalNewvector HeckeCharacter
open DescentEngine TwistEngineAux

section LevelArith

private theorem level_ne_zero {M : ℕ} (hM : M ≠ 0) (q a : ℕ) (hq : q.Prime) :
    q ^ max a 1 * (M / q ^ M.factorization q) ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ hq.ne_zero) (Nat.ordCompl_pos q hM).ne'

private theorem factorization_level_self {M : ℕ} (hM : M ≠ 0) (q a : ℕ) (hq : q.Prime) :
    (q ^ max a 1 * (M / q ^ M.factorization q)).factorization q = max a 1 := by
  rw [Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) (Nat.ordCompl_pos q hM).ne', Finsupp.coe_add,
    Pi.add_apply, hq.factorization_pow, Finsupp.single_eq_same, Nat.factorization_ordCompl,
    Finsupp.erase_same, add_zero]

private theorem factorization_level_of_ne {M : ℕ} (hM : M ≠ 0) {q : ℕ} (a : ℕ) (hq : q.Prime) {ℓ : ℕ}
    (hℓq : ℓ ≠ q) : (q ^ max a 1 * (M / q ^ M.factorization q)).factorization ℓ = M.factorization ℓ := by
  rw [Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) (Nat.ordCompl_pos q hM).ne', Finsupp.coe_add,
    Pi.add_apply, hq.factorization_pow, Finsupp.single_eq_of_ne hℓq, Nat.factorization_ordCompl,
    Finsupp.erase_ne hℓq, zero_add]

end LevelArith

section KZeroLift

private theorem exists_finComponent_eq_centralGL_mul' {q : ℕ} [Fact q.Prime] {N : ℕ} (hN : N ≠ 0)
    (hn : 1 ≤ N.factorization q)
    {u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)} (hu : u ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel N)) :
    ∃ (c : GL (Fin 2) ℤ_[q]) (d : ℤ_[q]ˣ) (k : GL (Fin 2) ℚ_[q]),
      k ∈ LocalNewvector.padicK1 q (N.factorization q) ∧
      (d : ℤ_[q]) = (c : Matrix (Fin 2) (Fin 2) ℤ_[q]) 1 1 ∧
      padicGL q (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap ℤ_[q] ℚ_[q]) c)
        = finComponent (𝓞 ℚ) ℚ (padicPlace q) u ∧
      Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap ℤ_[q] ℚ_[q]) c
        = LocalNewvector.centralGL q (Units.map (algebraMap ℤ_[q] ℚ_[q]).toMonoidHom d) * k := by
  obtain ⟨c, hcfin⟩ := DescentSupportB.exists_padicGL_map_eq_finComponent (q := q) hu
  have hc10 : (c : Matrix (Fin 2) (Fin 2) ℤ_[q]) 1 0
      ∈ Ideal.span {(q : ℤ_[q]) ^ N.factorization q} := by
    rw [← valued_coe_le_idealBound_iff q hN]
    have hcoe : padicRingEquiv q (((c : Matrix (Fin 2) (Fin 2) ℤ_[q]) 1 0 : ℤ_[q]) : ℚ_[q])
        = (finComponent (𝓞 ℚ) ℚ (padicPlace q) u : Matrix (Fin 2) (Fin 2) _) 1 0 := by
      rw [← hcfin, padicGL_apply, Matrix.GeneralLinearGroup.map_apply, PadicInt.algebraMap_apply]
    rw [hcoe, finComponent_apply]
    exact (mem_finiteLevelZero_iff.mp hu).1.lowerLeft (padicPlace q)
  have hc10_nonunit : ¬ IsUnit ((c : Matrix (Fin 2) (Fin 2) ℤ_[q]) 1 0) := fun hcu => by
    have hqdvd : (q : ℤ_[q]) ∣ (c : Matrix (Fin 2) (Fin 2) ℤ_[q]) 1 0 := by
      obtain ⟨k, hk⟩ := Ideal.mem_span_singleton.mp hc10
      exact ⟨(q : ℤ_[q]) ^ (N.factorization q - 1) * k, by
        rw [hk, ← mul_assoc, ← pow_succ']
        congr 2; omega⟩
    exact PadicInt.not_isUnit_iff.mpr ((PadicInt.norm_lt_one_iff_dvd _).mpr hqdvd) hcu
  obtain ⟨d, hd⟩ := DescentSupportB.isUnit_entry_of_lowerLeft_mem c hc10_nonunit
  set sc : GL (Fin 2) ℤ_[q] :=
    Units.map (algebraMap ℤ_[q] (Matrix (Fin 2) (Fin 2) ℤ_[q])).toMonoidHom d with hsc
  set k' : GL (Fin 2) ℤ_[q] := sc⁻¹ * c with hk'
  have hsc_inv_coe : ((sc⁻¹ : GL (Fin 2) ℤ_[q]) : Matrix (Fin 2) (Fin 2) ℤ_[q])
      = (↑d⁻¹ : ℤ_[q]) • (1 : Matrix (Fin 2) (Fin 2) ℤ_[q]) := by
    rw [hsc, ← map_inv]
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      Algebra.algebraMap_eq_smul_one]
  have hk'_row1 : ∀ j, (k' : Matrix (Fin 2) (Fin 2) ℤ_[q]) 1 j
      = (↑d⁻¹ : ℤ_[q]) * (c : Matrix (Fin 2) (Fin 2) ℤ_[q]) 1 j := fun j => by
    rw [hk', Units.val_mul, hsc_inv_coe, Matrix.smul_mul, one_mul, Matrix.smul_apply,
      smul_eq_mul]
  refine ⟨c, d, Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap ℤ_[q] ℚ_[q]) k', ?_, hd, hcfin, ?_⟩
  · rw [LocalNewvector.mem_congruenceK1_iff]
    refine ⟨k', rfl, ?_, ?_⟩
    · rw [hk'_row1 0]; exact Ideal.mul_mem_left _ _ hc10
    · rw [hk'_row1 1, ← hd, d.inv_mul, sub_self]; exact Ideal.zero_mem _
  · rw [← DescentSupportB.map_algebraMap_scalar_eq_centralGL d, ← hsc, ← map_mul, hk', mul_inv_cancel_left]

private theorem centralGL_mem_padicK1_of_sub_one_mem {q : ℕ} [Fact q.Prime] {n : ℕ} (e : ℤ_[q]ˣ)
    (he : (e : ℤ_[q]) - 1 ∈ Ideal.span {(q : ℤ_[q]) ^ n}) :
    LocalNewvector.centralGL q (Units.map (algebraMap ℤ_[q] ℚ_[q]).toMonoidHom e)
      ∈ LocalNewvector.padicK1 q n := by
  rw [LocalNewvector.mem_congruenceK1_iff]
  refine ⟨Units.map (algebraMap ℤ_[q] (Matrix (Fin 2) (Fin 2) ℤ_[q])).toMonoidHom e,
    DescentSupportB.map_algebraMap_scalar_eq_centralGL e, ?_, ?_⟩
  · simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Matrix.algebraMap_matrix_apply,
      if_neg (show (1 : Fin 2) ≠ 0 by decide)]
    exact Ideal.zero_mem _
  · simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Matrix.algebraMap_matrix_apply,
      if_pos rfl]
    exact he

end KZeroLift

section TwistSubLemmasD1

variable (η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)

private theorem eta_det_globalPoints_eq_one' (hη : IsIdeleClassChar (𝓞 ℚ) ℚ η) (γ : GL (Fin 2) ℚ) :
    (η (globalPoints (𝓞 ℚ) ℚ γ).det : ℂ) = 1 := by
  have hdet : (globalPoints (𝓞 ℚ) ℚ γ).det
      = Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) (Matrix.GeneralLinearGroup.det γ) := by
    rw [globalPoints, Matrix.GeneralLinearGroup.map_det]
  rw [hdet, hη (Matrix.GeneralLinearGroup.det γ), Units.val_one]

private theorem fnTwist_left_inv' (hη : IsIdeleClassChar (𝓞 ℚ) ℚ η)
    {Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hΦleft : ∀ (γ : GL (Fin 2) ℚ) (z : AdelicGL2 (𝓞 ℚ) ℚ), Φ (globalPoints (𝓞 ℚ) ℚ γ * z) = Φ z)
    (γ : GL (Fin 2) ℚ) (z : AdelicGL2 (𝓞 ℚ) ℚ) :
    fnTwist ℚ η Φ (globalPoints (𝓞 ℚ) ℚ γ * z) = fnTwist ℚ η Φ z := by
  rw [fnTwist_apply, fnTwist_apply, chiDet_globalPoints_mul ℚ η hη, hΦleft]

end TwistSubLemmasD1

section MainD1

variable {M : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
variable {Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
variable (ηc : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
variable {q : ℕ} [Fact q.Prime]

private theorem fn_globalPoints_mul_of_mem_span_twist' (hφg : g.IsAdelicLiftOf Φ)
    (hη : IsIdeleClassChar (𝓞 ℚ) ℚ ηc)
    {y : AdelicSpan (fnTwist ℚ ηc Φ)}
    (hy : y ∈ Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • AdelicSpan.self (fnTwist ℚ ηc Φ)))
    (γ : GL (Fin 2) ℚ) (z : AdelicGL2 (𝓞 ℚ) ℚ) :
    fn y (globalPoints (𝓞 ℚ) ℚ γ * z) = fn y z := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, rfl⟩ := hy
    rw [fn_padic_smul_self, fn_padic_smul_self, mul_assoc, fnTwist_left_inv' ηc hη hφg.left_inv]
  | zero => rfl
  | add y₁ y₂ _ _ ih₁ ih₂ => rw [fn_add, fn_add, ih₁, ih₂]
  | smul c y _ ih => rw [fn_csmul, fn_csmul, ih]

private theorem fn_mul_finEmbed_of_mem_span_twist_of_qtrivial (hM : M ≠ 0) (hφg : g.IsAdelicLiftOf Φ)
    {b : ℕ} (hηb : AdmitsModulus ℚ ηc (ratLevel (q ^ b)))
    {y : AdelicSpan (fnTwist ℚ ηc Φ)}
    (hy : y ∈ Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • AdelicSpan.self (fnTwist ℚ ηc Φ)))
    {w : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)} (hw : w ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel M))
    (hwq : finComponent (𝓞 ℚ) ℚ (padicPlace q) w = 1) (z : AdelicGL2 (𝓞 ℚ) ℚ) :
    fn y (z * finEmbed (𝓞 ℚ) ℚ w) = fn y z := by
  have hK₀ := hφg.levelZero_inv hM
  have hK₀q : ∀ w ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel M),
      finComponent (𝓞 ℚ) ℚ (padicPlace q) w = 1 →
      ∀ x, fnTwist ℚ ηc Φ (x * finEmbed (𝓞 ℚ) ℚ w) = fnTwist ℚ ηc Φ x :=
    fun w hwM hwq' x => fnTwist_levelZero_inv_of_qtrivial ηc hηb hM hK₀ hwM hwq' x
  induction hy using Submodule.span_induction with
  | mem y' hy' =>
    obtain ⟨x, rfl⟩ := hy'
    rw [fn_padic_smul_self, fn_padic_smul_self, padicToAdelic_apply, mul_assoc, ← map_mul,
      DescentSupportA.commute_of_finComponent_eq_one (padicPlace q) hwq
        (fun w' hw' => finComponent_padicToFinAdelic_of_ne q x hw'),
      map_mul, ← mul_assoc, hK₀q _ hw hwq]
  | zero => rfl
  | add y₁ y₂ _ _ ih₁ ih₂ => rw [fn_add, fn_add, ih₁, ih₂]
  | smul c' y' _ ih => rw [fn_csmul, fn_csmul, ih]

private theorem fn_mul_finEmbed_eq_theta_mul (hM : M ≠ 0) (hφg : g.IsAdelicLiftOf Φ)
    {b : ℕ} (hηb : AdmitsModulus ℚ ηc (ratLevel (q ^ b)))
    {a : ℕ} {θ : ℤ_[q]ˣ →* ℂˣ}
    {y : AdelicSpan (fnTwist ℚ ηc Φ)}
    (hy : y ∈ Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • AdelicSpan.self (fnTwist ℚ ηc Φ)))
    (hfix : y ∈ fixedSubmodule (padicK1 q a) (AdelicSpan (fnTwist ℚ ηc Φ)))
    (hcent : ∀ u : ℤ_[q]ˣ, centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom u) • y = (θ u : ℂ) • y)
    {u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (hu : u ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel (q ^ max a 1 * (M / q ^ M.factorization q))))
    (d : ℤ_[q]ˣ)
    (hd : Valued.v (((u : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1) (padicPlace q)
        - padicRingEquiv q ((d : ℤ_[q]) : ℚ_[q]))
      ≤ idealBound (𝓞 ℚ) (ratLevel (q ^ max a 1 * (M / q ^ M.factorization q))) (padicPlace q))
    (z : AdelicGL2 (𝓞 ℚ) ℚ) :
    fn y (z * finEmbed (𝓞 ℚ) ℚ u) = (θ d : ℂ) * fn y z := by
  have hqP : q.Prime := Fact.out
  set N : ℕ := q ^ max a 1 * (M / q ^ M.factorization q) with hNdef
  have hN : N ≠ 0 := level_ne_zero hM q a hqP
  have hvq : N.factorization q = max a 1 := factorization_level_self hM q a hqP
  obtain ⟨c, d₀, k, hk, hd₀, hcfin, hcdk⟩ :=
    exists_finComponent_eq_centralGL_mul' (q := q) hN (by rw [hvq]; exact le_max_right _ _) hu
  rw [hvq] at hk

  have hcong : (d₀ : ℤ_[q]) - d ∈ Ideal.span {(q : ℤ_[q]) ^ max a 1} := by
    rw [← hvq, ← valued_coe_le_idealBound_iff q hN, PadicInt.coe_sub, map_sub]
    have h11 : padicRingEquiv q ((d₀ : ℤ_[q]) : ℚ_[q])
        = ((u : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1) (padicPlace q) := by
      rw [← finComponent_apply, ← hcfin, padicGL_apply, Matrix.GeneralLinearGroup.map_apply,
        PadicInt.algebraMap_apply, hd₀]
    rw [h11]
    exact hd

  set e : ℤ_[q]ˣ := d⁻¹ * d₀ with hedef
  have he : (e : ℤ_[q]) - 1 ∈ Ideal.span {(q : ℤ_[q]) ^ max a 1} := by
    have : (e : ℤ_[q]) - 1 = (↑d⁻¹ : ℤ_[q]) * ((d₀ : ℤ_[q]) - d) := by
      rw [hedef, Units.val_mul, mul_sub, Units.inv_mul]
    rw [this]
    exact Ideal.mul_mem_left _ _ hcong
  have heK : LocalNewvector.centralGL q (Units.map (algebraMap ℤ_[q] ℚ_[q]).toMonoidHom e)
      ∈ padicK1 q (max a 1) := centralGL_mem_padicK1_of_sub_one_mem e he
  have hle : padicK1 q (max a 1) ≤ padicK1 q a := congruenceK1_antitone (le_max_left a 1)

  have halg : (algebraMap ℤ_[q] ℚ_[q] : ℤ_[q] →+* ℚ_[q]) = PadicInt.Coe.ringHom := rfl
  have hcy : Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap ℤ_[q] ℚ_[q]) c • y = (θ d : ℂ) • y := by
    have hsplit : Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap ℤ_[q] ℚ_[q]) c
        = LocalNewvector.centralGL q (Units.map (algebraMap ℤ_[q] ℚ_[q]).toMonoidHom d) *
          (LocalNewvector.centralGL q (Units.map (algebraMap ℤ_[q] ℚ_[q]).toMonoidHom e) * k) := by
      rw [hcdk, ← mul_assoc, ← map_mul, ← map_mul, hedef, mul_inv_cancel_left]
    rw [hsplit, mul_smul, mem_fixedSubmodule_iff.mp hfix _ (hle (mul_mem heK hk))]
    have := hcent d
    rw [← halg] at this
    exact this
  set cQ : GL (Fin 2) ℚ_[q] := Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap ℤ_[q] ℚ_[q]) c with hcQ

  have hw : u * (padicToFinAdelic q cQ)⁻¹ ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel M) :=
    DescentSupportB.mul_padicToFinAdelic_inv_mem_finiteLevelZero
      (fun v hv => DescentSupportB.idealBound_ratLevel_eq_of_factorization_eq hN hM
        (fun ℓ _ hℓq => factorization_level_of_ne hM a hqP hℓq) v hv) hu cQ hcfin.symm
  have hwq : finComponent (𝓞 ℚ) ℚ (padicPlace q) (u * (padicToFinAdelic q cQ)⁻¹) = 1 := by
    rw [map_mul, map_inv, finComponent_padicToFinAdelic_self q, hcfin, mul_inv_cancel]
  have hsplit : u = u * (padicToFinAdelic q cQ)⁻¹ * padicToFinAdelic q cQ := by group
  rw [hsplit, map_mul, ← mul_assoc, ← padicToAdelic_apply, ← fn_padic_smul, hcy, fn_csmul,
    fn_mul_finEmbed_of_mem_span_twist_of_qtrivial ηc hM hφg hηb hy hw hwq]

end MainD1

end TwistEngine

open DescentEngine TwistEngine NumberField NumberField.AdelicLevel AdelicDock AutomorphicForm LocalNewvector HeckeCharacter in
theorem solution
    {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    {Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ} (hΦg : g.IsAdelicLiftOf Φ)
    (q : ℕ) [Fact q.Prime]
    (η : (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ →* ℂˣ)
    (hη : AutomorphicForm.IsIdeleClassChar (NumberField.RingOfIntegers ℚ) ℚ η)
    (b : ℕ) (hηb : HeckeCharacter.AdmitsModulus ℚ η (AdelicDock.ratLevel (q ^ b)))
    (a : ℕ) (θ : ℤ_[q]ˣ →* ℂˣ)
    (y : LocalNewvector.AdelicSpan (AutomorphicForm.fnTwist ℚ η Φ))
    (hy : y ∈ Submodule.span ℂ
      (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self (AutomorphicForm.fnTwist ℚ η Φ)))
    (hfix : y ∈ LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 q a)
      (LocalNewvector.AdelicSpan (AutomorphicForm.fnTwist ℚ η Φ)))
    (hcent : ∀ u : ℤ_[q]ˣ,
      LocalNewvector.centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom u) • y = (θ u : ℂ) • y) :
    (∀ (γ : GL (Fin 2) ℚ) (z : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ),
        (LocalNewvector.AdelicSpan.toFn (AutomorphicForm.fnTwist ℚ η Φ) y).toFn
            (AutomorphicForm.globalPoints (NumberField.RingOfIntegers ℚ) ℚ γ * z) =
          (LocalNewvector.AdelicSpan.toFn (AutomorphicForm.fnTwist ℚ η Φ) y).toFn z) ∧
    ∀ u ∈ NumberField.AdelicLevel.finiteLevelZero (NumberField.RingOfIntegers ℚ) ℚ
        (AdelicDock.ratLevel (q ^ max a 1 * (M / q ^ M.factorization q))),
      ∀ d : ℤ_[q]ˣ,
        Valued.v
            (((u : Matrix (Fin 2) (Fin 2)
                (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)) 1 1)
                (AdelicDock.padicPlace q) -
              AdelicDock.padicRingEquiv q ((d : ℤ_[q]) : ℚ_[q])) ≤
          NumberField.AdelicLevel.idealBound (NumberField.RingOfIntegers ℚ)
            (AdelicDock.ratLevel (q ^ max a 1 * (M / q ^ M.factorization q))) (AdelicDock.padicPlace q) →
        ∀ z : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ,
          (LocalNewvector.AdelicSpan.toFn (AutomorphicForm.fnTwist ℚ η Φ) y).toFn
              (z * AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ u) =
            (θ d : ℂ) * (LocalNewvector.AdelicSpan.toFn (AutomorphicForm.fnTwist ℚ η Φ) y).toFn z :=
  ⟨fun γ z => fn_globalPoints_mul_of_mem_span_twist' η hΦg hη hy γ z,
    fun _ hu d hd z => fn_mul_finEmbed_eq_theta_mul η (NeZero.ne M) hΦg hηb hy hfix hcent hu d hd z⟩

end S_CuspForm_IsAdelicLiftOf_apply_mul_finEmbed_levelZero_eq_of_mem_span_fnTwist_of_fixed
end P2MW
export P2MW.S_CuspForm_IsAdelicLiftOf_apply_mul_finEmbed_levelZero_eq_of_mem_span_fnTwist_of_fixed (solution)
