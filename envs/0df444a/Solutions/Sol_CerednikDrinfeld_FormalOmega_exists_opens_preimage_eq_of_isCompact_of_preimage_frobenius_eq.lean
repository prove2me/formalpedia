-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.exists_opens_preimage_eq_of_isCompact_of_preimage_frobenius_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/664ce588-55ac-50d5-808f-46c9976eca2c

import Mathlib
import Theorems.Thm_CerednikDrinfeld_FormalOmega_fixedPoints_frobenius_levels
import Theorems.Thm_CerednikDrinfeld_FormalOmega_existsUnique_tmul_one_eq_of_map_frobenius_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_exists_opens_preimage_eq_of_isCompact_of_preimage_frobenius_eq

set_option autoImplicit false

open scoped TensorProduct Polynomial
p2m_open "CategoryTheory AlgebraicGeometry Polynomial AlgebraicGeometry.Polynomial"

namespace QCDesc

section CharPoly

variable {R : Type} [CommRing R] (τ : R →+* R) (k : ℕ) (f : R)

theorem iterate_mul_eq (hf : τ^[k] f = f) (q : ℕ) : τ^[k * q] f = f := by
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.mul_succ, Function.iterate_add_apply, hf, ih]

theorem iterate_mod_eq (hf : τ^[k] f = f) (n : ℕ) : τ^[n % k] f = τ^[n] f := by
  conv_rhs => rw [← Nat.div_add_mod n k, Nat.add_comm, Function.iterate_add_apply, iterate_mul_eq τ k f hf]

noncomputable def chi : R[X] := ∏ j : Fin k, (X - C (τ^[(j : ℕ)] f))

theorem chi_monic : (chi τ k f).Monic :=
  monic_prod_of_monic _ _ fun j _ => monic_X_sub_C _

theorem chi_natDegree [Nontrivial R] : (chi τ k f).natDegree = k := by
  classical
  rw [chi, natDegree_prod_of_monic _ _ fun j _ => monic_X_sub_C _]
  simp

theorem chi_eval (hk : 0 < k) : (chi τ k f).eval f = 0 := by
  classical
  rw [chi, eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ (⟨0, hk⟩ : Fin k))
  simp

theorem chi_coeff_mem (i : ℕ) (hi : i < k) :
    (chi τ k f).coeff i ∈ Ideal.span (Set.range fun j : Fin k => τ^[(j : ℕ)] f) := by
  classical
  set J := Ideal.span (Set.range fun j : Fin k => τ^[(j : ℕ)] f)
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← Polynomial.coeff_map, chi, Polynomial.map_prod]
  have : ∀ j : Fin k, Polynomial.map (Ideal.Quotient.mk J) (X - C (τ^[(j : ℕ)] f)) = X := fun j => by
    rw [Polynomial.map_sub, map_X, map_C, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self j)), map_zero,
      sub_zero]
  simp only [this, Finset.prod_const, Finset.card_univ, Fintype.card_fin, coeff_X_pow, if_neg (Nat.ne_of_lt hi)]

theorem chi_map_eq (hk : 0 < k) (hf : τ^[k] f = f) : (chi τ k f).map τ = chi τ k f := by
  classical
  rw [chi, Polynomial.map_prod]
  have hfac : ∀ j : Fin k, Polynomial.map τ (X - C (τ^[(j : ℕ)] f)) = X - C (τ^[(j : ℕ) + 1] f) := fun j => by
    rw [Polynomial.map_sub, map_X, map_C, Function.iterate_succ_apply']
  simp only [hfac]
  symm
  refine Finset.prod_bij' (fun j _ => (⟨((j : ℕ) + (k - 1)) % k, Nat.mod_lt _ hk⟩ : Fin k))
    (fun j _ => (⟨((j : ℕ) + 1) % k, Nat.mod_lt _ hk⟩ : Fin k))
    (fun _ _ => Finset.mem_univ _) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro j _
    apply Fin.ext
    show (((j : ℕ) + (k - 1)) % k + 1) % k = (j : ℕ)
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, show (j : ℕ) + (k - 1) + 1 = (j : ℕ) + k by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt j.2]
  · intro j _
    apply Fin.ext
    show (((j : ℕ) + 1) % k + (k - 1)) % k = (j : ℕ)
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, show (j : ℕ) + 1 + (k - 1) = (j : ℕ) + k by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt j.2]
  · intro j _
    show X - C (τ^[(j : ℕ)] f) = X - C (τ^[(((j : ℕ) + (k - 1)) % k) + 1] f)
    congr 2
    rw [← iterate_mod_eq τ k f hf ((((j : ℕ) + (k - 1)) % k) + 1), Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
      show (j : ℕ) + (k - 1) + 1 = (j : ℕ) + k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt j.2]

theorem exists_coeff_not_mem (hk : 0 < k) (P : Ideal R) [hP : P.IsPrime] (hfP : f ∉ P) :
    ∃ i, i < k ∧ (chi τ k f).coeff i ∉ P := by
  classical
  by_contra h
  push Not at h
  apply hfP
  apply hP.mem_of_pow_mem k
  haveI : Nontrivial R := ⟨⟨f, 0, fun h0 => hfP (h0.symm ▸ P.zero_mem)⟩⟩
  have he := chi_eval τ k f hk
  have hlead : (chi τ k f).coeff k = 1 := by
    have := (chi_monic τ k f).coeff_natDegree; rwa [chi_natDegree] at this
  rw [eval_eq_sum_range, chi_natDegree, Finset.sum_range_succ, hlead, one_mul] at he
  have : f ^ k = -(∑ x ∈ Finset.range k, (chi τ k f).coeff x * f ^ x) := by linear_combination he
  rw [this]
  exact P.neg_mem (P.sum_mem fun x hx => P.mul_mem_right _ (h x (Finset.mem_range.mp hx)))

theorem exists_conj_not_mem (P : Ideal R) (i : ℕ) (hi : i < k) (h : (chi τ k f).coeff i ∉ P) :
    ∃ j : Fin k, τ^[(j : ℕ)] f ∉ P := by
  by_contra h'
  push Not at h'
  apply h
  apply (Ideal.span_le.mpr _) (chi_coeff_mem τ k f i hi)
  rintro _ ⟨j, rfl⟩
  exact h' j

end CharPoly

section Spectrum

variable {R : Type} [CommRing R] (τ : R →+* R)

theorem mem_iterate_comap_asIdeal (n : ℕ) (x : PrimeSpectrum R) (a : R) :
    a ∈ ((PrimeSpectrum.comap τ)^[n] x).asIdeal ↔ τ^[n] a ∈ x.asIdeal := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, ih]

end Spectrum

end QCDesc

open QCDesc in
theorem solution
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (Onr : Type) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (m : ℕ) (hm : 0 < m)
    (FrS : Onr ≃ₐ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) (hFrS : ∀ x : Onr, FrS x = (Fr ^ (m : ℤ)) x)
    (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) B] [IsScalarTower 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) B]
    (hB : IsNilpotent (algebraMap 𝒪 B π))
    (U : (Spec (CommRingCat.of (B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr))).Opens) (hU : IsCompact (U : Set ↥(Spec (CommRingCat.of (B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr)))))
    (hσU : Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map (AlgHom.id ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) B) (FrS : Onr →ₐ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr)).toRingHom) ⁻¹ᵁ U = U) :
    ∃ V : (Spec (CommRingCat.of B)).Opens, IsCompact (V : Set ↥(Spec (CommRingCat.of B))) ∧
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr)) ⁻¹ᵁ V = U := by
  classical

  let σA := Algebra.TensorProduct.map (AlgHom.id ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) B) (FrS : Onr →ₐ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr)
  let τ : B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr →+* B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr := σA.toRingHom
  let ι : B →+* B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr := Algebra.TensorProduct.includeLeftRingHom
  have hτ : ∀ z, τ z = σA z := fun _ => rfl
  obtain ⟨N, hN⟩ := hB
  obtain ⟨hlev, -⟩ := CerednikDrinfeld.FormalOmega.fixedPoints_frobenius_levels 𝒪 hdvr π hπ hcomplete hres hunr Onr Fr
    hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr m hm FrS hFrS
  have haff := CerednikDrinfeld.FormalOmega.existsUnique_tmul_one_eq_of_map_frobenius_eq 𝒪 hdvr π hπ hcomplete hres hunr
    Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr m hm FrS hFrS B ⟨N, hN⟩

  have htmul : ∀ (n : ℕ) (b : B) (x : Onr), τ^[n] (b ⊗ₜ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] x) = b ⊗ₜ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] ((FrS ^ n) x) := by
    intro n b x
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Function.iterate_succ_apply', ih, pow_succ', AlgEquiv.mul_apply, hτ]
        exact Algebra.TensorProduct.map_tmul _ _ _ _

  have hper : ∀ z : B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr, ∃ k, 0 < k ∧ τ^[k] z = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨1, one_pos, by simp⟩
    | tmul b x =>
        obtain ⟨k, hk, x', hx', hd⟩ := hlev N x
        obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hd
        have hx : x = x' + y * (algebraMap 𝒪 Onr π) ^ N := by rw [hy]; ring
        have hkill : b ⊗ₜ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] (y * (algebraMap 𝒪 Onr π) ^ N) = 0 := by
          have h1 : y * (algebraMap 𝒪 Onr π) ^ N = (algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) (π ^ N)) • y := by
            rw [Algebra.smul_def, ← IsScalarTower.algebraMap_apply 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr, map_pow, mul_comm]
          have h2 : (algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) (π ^ N)) • b = 0 := by
            rw [Algebra.smul_def, ← IsScalarTower.algebraMap_apply 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) B, map_pow, hN, zero_mul]
          rw [h1, ← TensorProduct.smul_tmul, h2, TensorProduct.zero_tmul]
        have hbx : b ⊗ₜ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] x = b ⊗ₜ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] x' := by rw [hx, TensorProduct.tmul_add, hkill, add_zero]
        have hfix : (FrS ^ k) x' = x' := by
          have := (AlgHom.mem_equalizer _ _ _).mp hx'
          simpa using this
        refine ⟨k, hk, ?_⟩
        rw [hbx, htmul, hfix]
    | add z₁ z₂ h₁ h₂ =>
        obtain ⟨k₁, hk₁, e₁⟩ := h₁
        obtain ⟨k₂, hk₂, e₂⟩ := h₂
        refine ⟨k₁ * k₂, Nat.mul_pos hk₁ hk₂, ?_⟩
        rw [← RingHom.coe_pow, map_add, RingHom.coe_pow, iterate_mul_eq τ k₁ z₁ e₁ k₂, mul_comm,
          iterate_mul_eq τ k₂ z₂ e₂ k₁]

  obtain ⟨t, ht⟩ := PrimeSpectrum.isCompact_isOpen_iff.mp ⟨hU, U.isOpen⟩
  have hmemU : ∀ x : PrimeSpectrum (B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr), x ∈ U ↔ ∃ f ∈ t, f ∉ x.asIdeal := by
    intro x
    have h0 := Set.ext_iff.mp ht x
    rw [Set.mem_compl_iff, PrimeSpectrum.mem_zeroLocus, Set.not_subset] at h0
    simp only [Finset.mem_coe, SetLike.mem_coe] at h0
    exact h0.symm

  choose kf hkf hkf' using hper
  obtain ⟨K, hK, hKf⟩ : ∃ K : ℕ, 0 < K ∧ ∀ f ∈ t, τ^[K] f = f := by
    refine ⟨∏ f ∈ t, kf f, Finset.prod_pos fun f _ => hkf f, fun f hf => ?_⟩
    rw [← Finset.mul_prod_erase t kf hf]
    exact iterate_mul_eq τ _ f (hkf' f) _

  let g : PrimeSpectrum (B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) → PrimeSpectrum (B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) := PrimeSpectrum.comap τ
  have hstab : ∀ x, g x ∈ U ↔ x ∈ U := by
    intro x
    have h1 := Scheme.Hom.mem_preimage (Spec.map (CommRingCat.ofHom τ))
      (x := (x : ↥(Spec (CommRingCat.of (B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr))))) (U := U)
    rw [Spec.map_apply, CommRingCat.hom_ofHom, hσU] at h1
    exact h1.symm
  have hstabn : ∀ (n : ℕ) x, g^[n] x ∈ U ↔ x ∈ U := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih => intro x; rw [Function.iterate_succ_apply', hstab, ih]

  have hinv : ∀ f, τ^[K] f = f → ∀ i, σA ((chi τ K f).coeff i) = (chi τ K f).coeff i := by
    intro f hf i
    rw [← hτ, ← Polynomial.coeff_map, chi_map_eq τ K f hK hf]
  obtain ⟨e, he⟩ : ∃ e : B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr → ℕ → B,
      ∀ f, τ^[K] f = f → ∀ i, (chi τ K f).coeff i = e f i ⊗ₜ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] (1 : Onr) := by
    refine ⟨fun f i => if h : τ^[K] f = f then (haff _ (hinv f h i)).exists.choose else 0, fun f hf i => ?_⟩
    simp only [dif_pos hf]
    exact (haff _ (hinv f hf i)).exists.choose_spec

  refine ⟨⨆ p : ↥t × Fin K, PrimeSpectrum.basicOpen (e (p.1 : _) (p.2 : ℕ)), ?_, ?_⟩
  · have hc : IsCompact ((⨆ p : ↥t × Fin K, PrimeSpectrum.basicOpen (e (p.1 : _) (p.2 : ℕ)) :
        TopologicalSpace.Opens (PrimeSpectrum B)) : Set (PrimeSpectrum B)) := by
      simp only [TopologicalSpace.Opens.coe_iSup]
      exact isCompact_iUnion fun p => PrimeSpectrum.isCompact_basicOpen _
    exact hc
  · ext x
    rw [SetLike.mem_coe, SetLike.mem_coe, Scheme.Hom.mem_preimage, Spec.map_apply, CommRingCat.hom_ofHom]
    constructor
    ·
      intro hx'
      change PrimeSpectrum.comap ι x ∈
        (⨆ p : ↥t × Fin K, PrimeSpectrum.basicOpen (e (p.1 : _) (p.2 : ℕ)) : TopologicalSpace.Opens (PrimeSpectrum B)) at hx'
      rw [TopologicalSpace.Opens.mem_iSup] at hx'
      obtain ⟨⟨⟨f, hf⟩, ⟨i, hi⟩⟩, hfi⟩ := hx'
      rw [PrimeSpectrum.mem_basicOpen] at hfi
      rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] at hfi
      have hci : (chi τ K f).coeff i ∉ x.asIdeal := by
        rw [he f (hKf f hf) i]; exact hfi
      obtain ⟨j, hj⟩ := exists_conj_not_mem τ K f x.asIdeal i hi hci
      rw [← mem_iterate_comap_asIdeal τ] at hj
      have : g^[(j : ℕ)] x ∈ U := (hmemU _).mpr ⟨f, hf, hj⟩
      exact (hstabn _ _).mp this
    ·
      intro hx
      obtain ⟨f, hf, hfx⟩ := (hmemU x).mp hx
      haveI := x.isPrime
      obtain ⟨i, hi, hci⟩ := exists_coeff_not_mem τ K f hK x.asIdeal hfx
      change PrimeSpectrum.comap ι x ∈
        (⨆ p : ↥t × Fin K, PrimeSpectrum.basicOpen (e (p.1 : _) (p.2 : ℕ)) : TopologicalSpace.Opens (PrimeSpectrum B))
      rw [TopologicalSpace.Opens.mem_iSup]
      refine ⟨⟨⟨f, hf⟩, ⟨i, hi⟩⟩, ?_⟩
      rw [PrimeSpectrum.mem_basicOpen, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
      rw [he f (hKf f hf) i] at hci
      exact hci

end S_CerednikDrinfeld_FormalOmega_exists_opens_preimage_eq_of_isCompact_of_preimage_frobenius_eq
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_exists_opens_preimage_eq_of_isCompact_of_preimage_frobenius_eq (solution)
