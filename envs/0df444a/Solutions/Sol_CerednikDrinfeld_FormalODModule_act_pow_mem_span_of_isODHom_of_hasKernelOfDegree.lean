-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.act_pow_mem_span_of_isODHom_of_hasKernelOfDegree
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/9025b5c1-cb71-52b8-8d05-3052dd6c7fdd

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_MvFormalGroup_PointsV2
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_cover_free_and_span_range_eq_map_of_subgroup_ideal
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_hopfAlgebra_ker_eq_of_subgroup_ideal
import Theorems.Thm_HopfAlgebra_convPow_finrank_eq_one_of_isCocomm
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_X_pow_mem_span_of_hasKernelOfDegree
import Theorems.Thm_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_map_of_X_pow_mem
import Theorems.Thm_CerednikDrinfeld_FormalODModule_subst_mem_span_of_isODHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_act_pow_mem_span_of_isODHom_of_hasKernelOfDegree

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal WithConv
open scoped TensorProduct

universe u v w t

section Engine
open TensorProduct MvPowerSeries

namespace TruncBCEngine

open MvPowerSeries

section L0

variable {σ : Type w} [Finite σ] {R : Type u} [CommRing R]

omit [Finite σ] in

theorem exists_le_degree_eq (N : ℕ) (x : σ →₀ ℕ) (hx : N ≤ x.degree) :
    ∃ y : σ →₀ ℕ, y ≤ x ∧ y.degree = N := by
  classical
  induction N with
  | zero => exact ⟨0, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨y, hyx, hyn⟩ := ih ((Nat.le_succ n).trans hx)
    have hne : x - y ≠ 0 := by
      intro h
      have hle : x ≤ y := tsub_eq_zero_iff_le.mp h
      have : x = y := le_antisymm hle hyx
      subst this
      omega
    obtain ⟨i, hi⟩ : ∃ i, (x - y) i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hne (Finsupp.ext hcon)
    refine ⟨y + Finsupp.single i 1, ?_, by simp [hyn]⟩
    intro j
    simp only [Finsupp.coe_add, Pi.add_apply]
    have hyj : y j ≤ x j := hyx j
    have hij : (x - y) i = x i - y i := Finsupp.tsub_apply x y i
    by_cases h : i = j
    · subst h
      rw [Finsupp.single_eq_same]
      omega
    · rw [Finsupp.single_apply, if_neg h]
      omega

omit [Finite σ] in

theorem monomial_one_mem_pow_span_X (y : σ →₀ ℕ) :
    (monomial y (1 : R) : MvPowerSeries σ R) ∈
      Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ y.degree := by
  classical
  rw [MvPowerSeries.monomial_one_eq, Finsupp.prod, Finsupp.degree_apply,
    ← Finset.prod_pow_eq_pow_sum]
  refine Ideal.prod_mem_prod fun i _ => ?_
  exact Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self i)) _

theorem mem_of_forall_coeff_eq_zero_of_forall_monomial_mem (N : ℕ) (I : Ideal (MvPowerSeries σ R))
    (hI : ∀ y : σ →₀ ℕ, y.degree = N → (monomial y (1 : R) : MvPowerSeries σ R) ∈ I)
    (q : MvPowerSeries σ R) (hq : ∀ x : σ →₀ ℕ, x.degree < N → coeff x q = 0) : q ∈ I := by
  classical

  have hY : ∀ x : σ →₀ ℕ, ∃ y : σ →₀ ℕ, N ≤ x.degree → y ≤ x ∧ y.degree = N := by
    intro x
    by_cases hx : N ≤ x.degree
    · obtain ⟨y, hy⟩ := exists_le_degree_eq N x hx
      exact ⟨y, fun _ => hy⟩
    · exact ⟨0, fun h => absurd h hx⟩
  choose Y hY using hY
  set D : Finset (σ →₀ ℕ) := (Finsupp.finite_of_degree_le N).toFinset.filter fun y => y.degree = N
    with hD
  have hmemD : ∀ y, y ∈ D ↔ y.degree = N := by
    intro y
    simp only [hD, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq, and_iff_right_iff_imp]
    intro h; exact h.le

  let r : (σ →₀ ℕ) → MvPowerSeries σ R := fun y z =>
    if N ≤ (z + y).degree ∧ Y (z + y) = y then coeff (z + y) q else 0
  have hr : ∀ y z, coeff z (r y) = if N ≤ (z + y).degree ∧ Y (z + y) = y then coeff (z + y) q else 0 :=
    fun y z => rfl
  have hdecomp : q = ∑ y ∈ D, monomial y (1 : R) * r y := by
    ext x
    rw [map_sum]
    simp_rw [coeff_monomial_mul, one_mul]
    by_cases hx : N ≤ x.degree
    · obtain ⟨hYx, hYdeg⟩ := hY x hx
      rw [Finset.sum_eq_single (Y x)]
      · rw [if_pos hYx, hr, tsub_add_cancel_of_le hYx, if_pos ⟨hx, rfl⟩]
      · intro y _ hne
        split_ifs with hyx
        · rw [hr, tsub_add_cancel_of_le hyx]
          rw [if_neg]
          rintro ⟨_, h⟩
          exact hne h.symm
        · rfl
      · intro h
        exact absurd ((hmemD _).mpr hYdeg) h
    · rw [hq x (not_le.mp hx)]
      symm
      refine Finset.sum_eq_zero fun y hy => ?_
      split_ifs with hyx
      · exfalso
        have := Finsupp.degree_mono hyx
        rw [(hmemD y).mp hy] at this
        exact hx this
      · rfl
  rw [hdecomp]
  refine Ideal.sum_mem _ fun y hy => ?_
  exact Ideal.mul_mem_right _ _ (hI y ((hmemD y).mp hy))

theorem mem_pow_span_X_of_forall_coeff_eq_zero (N : ℕ) (q : MvPowerSeries σ R)
    (hq : ∀ x : σ →₀ ℕ, x.degree < N → coeff x q = 0) :
    q ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ N :=
  mem_of_forall_coeff_eq_zero_of_forall_monomial_mem N _
    (fun y hy => hy ▸ monomial_one_mem_pow_span_X (R := R) y) q hq

end L0

section Coe

variable {σ : Type w} {R : Type u} [CommRing R]

noncomputable def coeAlgHom (R : Type u) [CommRing R] (σ : Type w) :
    MvPolynomial σ R →ₐ[R] MvPowerSeries σ R :=
  { MvPolynomial.coeToMvPowerSeries.ringHom with
    commutes' := fun r => by
      show ((algebraMap R (MvPolynomial σ R) r : MvPolynomial σ R) : MvPowerSeries σ R) = _
      rw [MvPolynomial.algebraMap_eq, MvPolynomial.coe_C]
      rfl }

@[scoped simp] theorem coeAlgHom_apply (t : MvPolynomial σ R) : coeAlgHom R σ t = (t : MvPowerSeries σ R) :=
  rfl

theorem map_coeAlgHom_idealOfVars :
    Ideal.map (coeAlgHom R σ) (MvPolynomial.idealOfVars σ R) =
      Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) := by
  rw [MvPolynomial.idealOfVars, Ideal.map_span, ← Set.range_comp]
  congr 1
  ext q
  simp only [Set.mem_range, Function.comp_apply, coeAlgHom_apply, MvPolynomial.coe_X]

theorem coe_mem_pow_span_X_of_mem {N : ℕ} {t : MvPolynomial σ R}
    (ht : t ∈ MvPolynomial.idealOfVars σ R ^ N) :
    (t : MvPowerSeries σ R) ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ N := by
  have := Ideal.mem_map_of_mem (coeAlgHom R σ) ht
  rwa [Ideal.map_pow, map_coeAlgHom_idealOfVars] at this

end Coe

section Trunc

variable {σ : Type w} [Finite σ] {R : Type u} [CommRing R]

theorem truncTotal_map {S : Type v} [CommRing S] (f : R →+* S) (N : ℕ) (q : MvPowerSeries σ R) :
    truncTotal N (MvPowerSeries.map f q) = MvPolynomial.map f (truncTotal N q) :=
  truncFinset_map f q

theorem sub_coe_truncTotal_mem_pow_span_X (N : ℕ) (q : MvPowerSeries σ R) :
    q - ((truncTotal N q : MvPolynomial σ R) : MvPowerSeries σ R) ∈
      Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ N := by
  refine mem_pow_span_X_of_forall_coeff_eq_zero N _ fun x hx => ?_
  rw [map_sub, MvPolynomial.coeff_coe, coeff_truncTotal _ hx, sub_self]

theorem mk_coe_truncTotal (N : ℕ) (I : Ideal (MvPowerSeries σ R))
    (hI : Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ N ≤ I) (q : MvPowerSeries σ R) :
    Ideal.Quotient.mk I ((truncTotal N q : MvPolynomial σ R) : MvPowerSeries σ R) =
      Ideal.Quotient.mk I q := by
  rw [Ideal.Quotient.eq]
  have := hI (sub_coe_truncTotal_mem_pow_span_X N q)
  rwa [← neg_sub, Ideal.neg_mem_iff] at this

end Trunc

section BaseChangeIdeals

variable {σ : Type w} {R : Type u} [CommRing R] {S : Type v} [CommRing S]

theorem map_map_span_X (f : R →+* S) :
    Ideal.map (MvPowerSeries.map (σ := σ) f) (Ideal.span (Set.range (X : σ → MvPowerSeries σ R))) =
      Ideal.span (Set.range (X : σ → MvPowerSeries σ S)) := by
  rw [Ideal.map_span, ← Set.range_comp]
  congr 1
  ext q
  simp only [Set.mem_range, Function.comp_apply, MvPowerSeries.map_X]

theorem map_map_span_range {ι : Type*} (f : R →+* S) (φ : ι → MvPowerSeries σ R) :
    Ideal.map (MvPowerSeries.map (σ := σ) f) (Ideal.span (Set.range φ)) =
      Ideal.span (Set.range fun i => MvPowerSeries.map f (φ i)) := by
  rw [Ideal.map_span, ← Set.range_comp]
  rfl

theorem pow_span_X_le_span_map {ι : Type*} (f : R →+* S) (φ : ι → MvPowerSeries σ R) (N : ℕ)
    (hN : Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ N ≤ Ideal.span (Set.range φ)) :
    Ideal.span (Set.range (X : σ → MvPowerSeries σ S)) ^ N ≤
      Ideal.span (Set.range fun i => MvPowerSeries.map f (φ i)) := by
  rw [← map_map_span_X f, ← Ideal.map_pow, ← map_map_span_range f φ]
  exact Ideal.map_mono hN

end BaseChangeIdeals

section Main

variable {σ : Type w} [Finite σ] {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
variable {ι : Type*}

noncomputable def theta (φ : ι → MvPowerSeries σ R) (N : ℕ)
    (hN : Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ N ≤ Ideal.span (Set.range φ)) :
    (MvPolynomial σ R ⧸ MvPolynomial.idealOfVars σ R ^ N) →ₐ[R]
      (MvPowerSeries σ R ⧸ Ideal.span (Set.range φ)) :=
  Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ R _).comp (coeAlgHom R σ)) fun t ht => by
    rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, coeAlgHom_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact hN (coe_mem_pow_span_X_of_mem ht)

omit [Finite σ] in
theorem theta_mk (φ : ι → MvPowerSeries σ R) (N : ℕ)
    (hN : Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ N ≤ Ideal.span (Set.range φ))
    (t : MvPolynomial σ R) :
    theta φ N hN (Ideal.Quotient.mk _ t) = Ideal.Quotient.mk _ (t : MvPowerSeries σ R) :=
  rfl

scoped instance instIsScalarTowerTensorQuot (N : ℕ) :
    IsScalarTower R S (S ⊗[R] (MvPolynomial σ R ⧸ MvPolynomial.idealOfVars σ R ^ N)) :=
  TensorProduct.isScalarTower_left

noncomputable def xfam (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    (σ : Type w) (N : ℕ) : σ → S ⊗[R] (MvPolynomial σ R ⧸ MvPolynomial.idealOfVars σ R ^ N) :=
  fun i => (1 : S) ⊗ₜ[R] Ideal.Quotient.mk _ (MvPolynomial.X i)

omit [Finite σ] in
theorem aeval_xfam (N : ℕ) (t : MvPolynomial σ R) :
    MvPolynomial.aeval (xfam R S σ N) t = (1 : S) ⊗ₜ[R] Ideal.Quotient.mk _ t := by
  have h : MvPolynomial.aeval (R := R) (xfam R S σ N) =
      (Algebra.TensorProduct.includeRight (R := R) (A := S)).comp
        (Ideal.Quotient.mkₐ R (MvPolynomial.idealOfVars σ R ^ N)) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    rw [MvPolynomial.aeval_X]
    rfl
  exact congrArg (fun F => F t) h

noncomputable def beta0 (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    (σ : Type w) (N : ℕ) :
    MvPolynomial σ S →ₐ[S] S ⊗[R] (MvPolynomial σ R ⧸ MvPolynomial.idealOfVars σ R ^ N) :=
  MvPolynomial.aeval (xfam R S σ N)

omit [Finite σ] in
theorem beta0_map (N : ℕ) (t : MvPolynomial σ R) :
    beta0 R S σ N (MvPolynomial.map (algebraMap R S) t) = (1 : S) ⊗ₜ[R] Ideal.Quotient.mk _ t := by
  rw [beta0, MvPolynomial.aeval_map_algebraMap]
  exact aeval_xfam N t

omit [Finite σ] in
theorem beta0_ker (N : ℕ) (a : MvPolynomial σ S) (ha : a ∈ MvPolynomial.idealOfVars σ S ^ N) :
    beta0 R S σ N a = 0 := by
  rw [MvPolynomial.pow_idealOfVars_eq_span] at ha
  suffices h : Ideal.span ((fun y => MvPolynomial.monomial y (1 : S)) '' (Finsupp.degree ⁻¹' {N})) ≤
      RingHom.ker (beta0 R S σ N) from RingHom.mem_ker.mp (h ha)
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨y, hy, rfl⟩
  rw [SetLike.mem_coe, RingHom.mem_ker]
  have h1 : (MvPolynomial.monomial y (1 : S)) =
      MvPolynomial.map (algebraMap R S) (MvPolynomial.monomial y (1 : R)) := by
    rw [MvPolynomial.map_monomial, (algebraMap R S).map_one]
  have h2 : MvPolynomial.monomial y (1 : R) ∈ MvPolynomial.idealOfVars σ R ^ N := by
    rw [MvPolynomial.pow_idealOfVars_eq_span]
    exact Ideal.subset_span ⟨y, hy, rfl⟩
  show beta0 R S σ N (MvPolynomial.monomial y (1 : S)) = 0
  rw [h1, beta0_map, Ideal.Quotient.eq_zero_iff_mem.mpr h2, TensorProduct.tmul_zero]

noncomputable def beta (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    (σ : Type w) (N : ℕ) :
    (MvPolynomial σ S ⧸ MvPolynomial.idealOfVars σ S ^ N) →ₐ[S]
      S ⊗[R] (MvPolynomial σ R ⧸ MvPolynomial.idealOfVars σ R ^ N) :=
  Ideal.Quotient.liftₐ _ (beta0 R S σ N) (beta0_ker N)

omit [Finite σ] in
theorem beta_mk (N : ℕ) (a : MvPolynomial σ S) :
    beta R S σ N (Ideal.Quotient.mk _ a) = beta0 R S σ N a :=
  rfl

noncomputable def tau (S : Type v) [CommRing S] (σ : Type w) [Finite σ] (N : ℕ) :
    MvPowerSeries σ S →ₐ[S] (MvPolynomial σ S ⧸ MvPolynomial.idealOfVars σ S ^ N) :=
  { (truncTotalAlgHom σ S N).toRingHom with
    commutes' := fun s => by
      show truncTotalAlgHom σ S N (algebraMap S (MvPowerSeries σ S) s) = algebraMap S _ s
      have h := (truncTotalAlgHom σ S N).commutes (MvPolynomial.C s)
      rw [MvPowerSeries.algebraMap_apply', MvPolynomial.coe_C, Algebra.algebraMap_self,
        MvPowerSeries.map_id, RingHom.id_apply] at h
      rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, h]
      rfl }

theorem tau_apply (N : ℕ) (q : MvPowerSeries σ S) :
    tau S σ N q = Ideal.Quotient.mk _ (truncTotal N q) :=
  rfl

noncomputable def G0 (S : Type v) [CommRing S] [Algebra R S] (φ : ι → MvPowerSeries σ R) (N : ℕ)
    (hN : Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ N ≤ Ideal.span (Set.range φ)) :
    MvPowerSeries σ S →ₐ[S] S ⊗[R] (MvPowerSeries σ R ⧸ Ideal.span (Set.range φ)) :=
  (Algebra.TensorProduct.map (AlgHom.id S S) (theta φ N hN)).comp ((beta R S σ N).comp (tau S σ N))

theorem G0_apply (φ : ι → MvPowerSeries σ R) (N : ℕ)
    (hN : Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ N ≤ Ideal.span (Set.range φ))
    (q : MvPowerSeries σ S) :
    G0 S φ N hN q =
      Algebra.TensorProduct.map (AlgHom.id S S) (theta φ N hN) (beta0 R S σ N (truncTotal N q)) :=
  rfl

theorem G0_map (φ : ι → MvPowerSeries σ R) (N : ℕ)
    (hN : Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ N ≤ Ideal.span (Set.range φ))
    (q : MvPowerSeries σ R) :
    G0 S φ N hN (MvPowerSeries.map (algebraMap R S) q) = (1 : S) ⊗ₜ[R] Ideal.Quotient.mk _ q := by
  rw [G0_apply, truncTotal_map, beta0_map, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
    theta_mk, mk_coe_truncTotal N _ hN]

noncomputable def G (S : Type v) [CommRing S] [Algebra R S] (φ : ι → MvPowerSeries σ R) (N : ℕ)
    (hN : Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ N ≤ Ideal.span (Set.range φ)) :
    (MvPowerSeries σ S ⧸ Ideal.span (Set.range fun i => MvPowerSeries.map (algebraMap R S) (φ i)))
      →ₐ[S] S ⊗[R] (MvPowerSeries σ R ⧸ Ideal.span (Set.range φ)) :=
  Ideal.Quotient.liftₐ _ (G0 S φ N hN) fun a ha => by
    suffices h : Ideal.span (Set.range fun i => MvPowerSeries.map (algebraMap R S) (φ i)) ≤
        RingHom.ker (G0 S φ N hN) from RingHom.mem_ker.mp (h ha)
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    show G0 S φ N hN (MvPowerSeries.map (algebraMap R S) (φ i)) = 0
    rw [G0_map, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i)),
      TensorProduct.tmul_zero]

theorem G_mk (φ : ι → MvPowerSeries σ R) (N : ℕ)
    (hN : Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ N ≤ Ideal.span (Set.range φ))
    (q : MvPowerSeries σ S) :
    G S φ N hN (Ideal.Quotient.mk _ q) = G0 S φ N hN q :=
  rfl

noncomputable def mapAH (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    (σ : Type w) : MvPowerSeries σ R →ₐ[R] MvPowerSeries σ S :=
  { MvPowerSeries.map (σ := σ) (algebraMap R S) with
    commutes' := fun r => by
      show MvPowerSeries.map (algebraMap R S) (algebraMap R (MvPowerSeries σ R) r) = _
      rw [MvPowerSeries.algebraMap_apply, MvPowerSeries.algebraMap_apply, MvPowerSeries.map_C,
        Algebra.algebraMap_self, RingHom.id_apply] }

omit [Finite σ] in
@[scoped simp] theorem mapAH_apply (q : MvPowerSeries σ R) :
    mapAH R S σ q = MvPowerSeries.map (algebraMap R S) q :=
  rfl

noncomputable def chi (S : Type v) [CommRing S] [Algebra R S] (φ : ι → MvPowerSeries σ R) :
    (MvPowerSeries σ R ⧸ Ideal.span (Set.range φ)) →ₐ[R]
      (MvPowerSeries σ S ⧸ Ideal.span (Set.range fun i => MvPowerSeries.map (algebraMap R S) (φ i))) :=
  Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ R _).comp (mapAH R S σ)) fun a ha => by
    rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, mapAH_apply, Ideal.Quotient.eq_zero_iff_mem,
      ← map_map_span_range]
    exact Ideal.mem_map_of_mem _ ha

omit [Finite σ] in
theorem chi_mk (φ : ι → MvPowerSeries σ R) (q : MvPowerSeries σ R) :
    chi S φ (Ideal.Quotient.mk _ q) = Ideal.Quotient.mk _ (MvPowerSeries.map (algebraMap R S) q) :=
  rfl

private noncomputable def _root_.TruncBCEngine.F (S : Type v) [CommRing S] [Algebra R S] (φ : ι → MvPowerSeries σ R) :
    S ⊗[R] (MvPowerSeries σ R ⧸ Ideal.span (Set.range φ)) →ₐ[S]
      (MvPowerSeries σ S ⧸ Ideal.span (Set.range fun i => MvPowerSeries.map (algebraMap R S) (φ i))) :=
  Algebra.TensorProduct.lift (Algebra.ofId S _) (chi S φ) fun _ _ => Commute.all _ _

p2m_export "TruncBCEngine" "F"
omit [Finite σ] in
theorem F_tmul (φ : ι → MvPowerSeries σ R) (s : S) (q : MvPowerSeries σ R) :
    F S φ (s ⊗ₜ[R] Ideal.Quotient.mk _ q) =
      s • Ideal.Quotient.mk _ (MvPowerSeries.map (algebraMap R S) q) := by
  rw [F, Algebra.TensorProduct.lift_tmul, chi_mk, Algebra.ofId_apply]
  exact (Algebra.smul_def s _).symm

theorem G_comp_F (φ : ι → MvPowerSeries σ R) (N : ℕ)
    (hN : Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ N ≤ Ideal.span (Set.range φ)) :
    (G S φ N hN).comp (F S φ) = AlgHom.id S _ := by
  refine Algebra.TensorProduct.ext' fun s b => ?_
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [AlgHom.comp_apply, F_tmul, map_smul, G_mk, G0_map, AlgHom.id_apply, TensorProduct.smul_tmul',
    smul_eq_mul, mul_one]

theorem F_comp_G (φ : ι → MvPowerSeries σ R) (N : ℕ)
    (hN : Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ N ≤ Ideal.span (Set.range φ)) :
    (F S φ).comp (G S φ N hN) = AlgHom.id S _ := by
  have hΨ : (F S φ).comp ((Algebra.TensorProduct.map (AlgHom.id S S) (theta φ N hN)).comp
      (beta0 R S σ N)) = (Ideal.Quotient.mkₐ S _).comp (coeAlgHom S σ) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, beta0, MvPolynomial.aeval_X, xfam,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, theta_mk, F_tmul, one_smul,
      MvPolynomial.coe_X, MvPowerSeries.map_X, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      coeAlgHom_apply, MvPolynomial.coe_X]
  refine AlgHom.ext fun z => ?_
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective z
  have := congrArg (fun Ψ => Ψ (truncTotal N q)) hΨ
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, coeAlgHom_apply] at this
  rw [AlgHom.comp_apply, G_mk, G0_apply, this, AlgHom.id_apply]
  exact mk_coe_truncTotal N _ (pow_span_X_le_span_map (algebraMap R S) φ N hN) q

noncomputable def baseChangeEquiv (S : Type v) [CommRing S] [Algebra R S]
    (φ : ι → MvPowerSeries σ R) (N : ℕ)
    (hN : Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ N ≤ Ideal.span (Set.range φ)) :
    S ⊗[R] (MvPowerSeries σ R ⧸ Ideal.span (Set.range φ)) ≃ₐ[S]
      (MvPowerSeries σ S ⧸ Ideal.span (Set.range fun i => MvPowerSeries.map (algebraMap R S) (φ i))) :=
  AlgEquiv.ofAlgHom (F S φ) (G S φ N hN) (F_comp_G φ N hN) (G_comp_F φ N hN)

theorem baseChangeEquiv_tmul (φ : ι → MvPowerSeries σ R) (N : ℕ)
    (hN : Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ N ≤ Ideal.span (Set.range φ))
    (s : S) (q : MvPowerSeries σ R) :
    baseChangeEquiv S φ N hN (s ⊗ₜ[R] Ideal.Quotient.mk _ q) =
      s • Ideal.Quotient.mk _ (MvPowerSeries.map (algebraMap R S) q) :=
  F_tmul φ s q

end Main

section Bridges

variable {σ : Type w} {R : Type u} [CommRing R]

def lowVanishing (σ : Type w) (R : Type u) [CommRing R] (N : ℕ) : Ideal (MvPowerSeries σ R) where
  carrier := {q | ∀ x : σ →₀ ℕ, x.degree < N → coeff x q = 0}
  add_mem' {a b} ha hb x hx := by rw [map_add, ha x hx, hb x hx, add_zero]
  zero_mem' x _ := by rw [map_zero]
  smul_mem' a q hq x hx := by
    classical
    rw [smul_eq_mul, coeff_mul]
    refine Finset.sum_eq_zero fun ij hij => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
    have hj : ij.2 ≤ x := hij ▸ le_add_self
    rw [hq ij.2 ((Finsupp.degree_mono hj).trans_lt hx), mul_zero]

theorem mem_lowVanishing_iff (N : ℕ) (q : MvPowerSeries σ R) :
    q ∈ lowVanishing σ R N ↔ ∀ x : σ →₀ ℕ, x.degree < N → coeff x q = 0 :=
  Iff.rfl

theorem span_X_le_lowVanishing_one :
    Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ≤ lowVanishing σ R 1 := by
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩ x hx
  have hx0 : x = 0 := (Finsupp.degree_eq_zero_iff x).mp (Nat.lt_one_iff.mp hx)
  subst hx0
  exact coeff_zero_X i

theorem lowVanishing_mul_le (a b : ℕ) :
    lowVanishing σ R a * lowVanishing σ R b ≤ lowVanishing σ R (a + b) := by
  classical
  rw [Ideal.mul_le]
  intro r hr s hs x hx
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun ij hij => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
  by_cases hi : ij.1.degree < a
  · rw [hr ij.1 hi, zero_mul]
  · have hdeg : x.degree = ij.1.degree + ij.2.degree := by rw [← hij, map_add]
    have hj : ij.2.degree < b := by omega
    rw [hs ij.2 hj, mul_zero]

theorem pow_span_X_le_lowVanishing (N : ℕ) :
    Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ N ≤ lowVanishing σ R N := by
  induction N with
  | zero =>
    intro q _ x hx
    exact absurd hx (Nat.not_lt_zero _)
  | succ n ih =>
    rw [pow_succ]
    exact (Ideal.mul_mono ih span_X_le_lowVanishing_one).trans (lowVanishing_mul_le n 1)

theorem pow_span_X_le_of_forall_monomial_mem [Finite σ] (N : ℕ) (I : Ideal (MvPowerSeries σ R))
    (hI : ∀ y : σ →₀ ℕ, y.degree = N → (monomial y (1 : R) : MvPowerSeries σ R) ∈ I) :
    Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ N ≤ I := fun q hq =>
  mem_of_forall_coeff_eq_zero_of_forall_monomial_mem N I hI q (pow_span_X_le_lowVanishing N hq)

theorem pow_span_X_le_of_forall_coeff_eq_zero_imp_mem (N : ℕ) (I : Ideal (MvPowerSeries σ R))
    (hI : ∀ q : MvPowerSeries σ R, (∀ x : σ →₀ ℕ, x.degree < N → coeff x q = 0) → q ∈ I) :
    Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ N ≤ I := fun q hq =>
  hI q (pow_span_X_le_lowVanishing N hq)

theorem mem_of_pow_span_X_le [Finite σ] (N : ℕ) (I : Ideal (MvPowerSeries σ R))
    (hN : Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ N ≤ I)
    (q : MvPowerSeries σ R) (hq : ∀ x : σ →₀ ℕ, x.degree < N → coeff x q = 0) : q ∈ I :=
  hN (mem_pow_span_X_of_forall_coeff_eq_zero N q hq)

theorem pow_span_X_le_of_forall_X_pow_mem [Fintype σ] (N : ℕ) (I : Ideal (MvPowerSeries σ R))
    (hI : ∀ i : σ, (X i : MvPowerSeries σ R) ^ N ∈ I) :
    Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ (Fintype.card σ * (N - 1) + 1) ≤ I := by
  classical
  refine pow_span_X_le_of_forall_monomial_mem _ I fun y hy => ?_

  obtain ⟨i, hi⟩ : ∃ i, N ≤ y i := by
    by_contra hcon
    push Not at hcon
    have hle : y.degree ≤ Fintype.card σ * (N - 1) := by
      rw [Finsupp.degree_eq_sum]
      calc ∑ i, y i ≤ ∑ _i : σ, (N - 1) := Finset.sum_le_sum fun i _ => by have := hcon i; omega
        _ = Fintype.card σ * (N - 1) := by rw [Finset.sum_const, smul_eq_mul, Finset.card_univ]
    omega
  have hsplit : y = Finsupp.single i N + (y - Finsupp.single i N) := by
    rw [add_tsub_cancel_of_le]
    intro j
    by_cases hij : i = j
    · subst hij; rwa [Finsupp.single_eq_same]
    · rw [Finsupp.single_apply, if_neg hij]; exact Nat.zero_le _
  rw [hsplit, ← one_mul (1 : R), ← monomial_mul_monomial, ← X_pow_eq]
  exact Ideal.mul_mem_right _ _ (hI i)

end Bridges

end TruncBCEngine
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_act_pow_mem_span_of_isODHom_of_hasKernelOfDegree.TruncBCEngine"

end Engine
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_act_pow_mem_span_of_isODHom_of_hasKernelOfDegree.TruncBCEngine"

namespace DIaa

theorem mem_of_forall_map_mem_map_away
    {B : Type*} [CommRing B] {σ : Type*} (I : Ideal (MvPowerSeries σ B))
    {ι : Type*} (g : ι → B) (hg : Ideal.span (Set.range g) = ⊤)
    (hbridge : ∀ (k : ι) (G : MvPowerSeries σ B),
      MvPowerSeries.map (algebraMap B (Localization.Away (g k))) G ∈
          I.map (MvPowerSeries.map (algebraMap B (Localization.Away (g k)))) →
        (1 : Localization.Away (g k)) ⊗ₜ[B] (Ideal.Quotient.mk I G) =
          (0 : Localization.Away (g k) ⊗[B] (MvPowerSeries σ B ⧸ I)))
    (a : MvPowerSeries σ B)
    (hloc : ∀ k : ι, MvPowerSeries.map (algebraMap B (Localization.Away (g k))) a ∈
      I.map (MvPowerSeries.map (algebraMap B (Localization.Away (g k))))) :
    a ∈ I := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  refine Module.eq_zero_of_isLocalized_span (Set.range g) hg
    (fun r => Localization.Away (r : B) ⊗[B] (MvPowerSeries σ B ⧸ I))
    (fun r => TensorProduct.mk B (Localization.Away (r : B)) (MvPowerSeries σ B ⧸ I) 1)
    (Ideal.Quotient.mk I a) ?_
  rintro ⟨r, k, rfl⟩
  exact hbridge k a (hloc k)

theorem bridge_of_linearEquiv
    {B : Type*} [CommRing B] {σ : Type*} (I : Ideal (MvPowerSeries σ B))
    (B' : Type*) [CommRing B'] [Algebra B B']
    (e : B' ⊗[B] (MvPowerSeries σ B ⧸ I) →ₗ[B]
      (MvPowerSeries σ B' ⧸ I.map (MvPowerSeries.map (algebraMap B B'))))
    (he_inj : Function.Injective e)
    (he : ∀ G : MvPowerSeries σ B,
      e ((1 : B') ⊗ₜ[B] Ideal.Quotient.mk I G) =
        Ideal.Quotient.mk _ (MvPowerSeries.map (algebraMap B B') G))
    (G : MvPowerSeries σ B)
    (hG : MvPowerSeries.map (algebraMap B B') G ∈ I.map (MvPowerSeries.map (algebraMap B B'))) :
    (1 : B') ⊗ₜ[B] (Ideal.Quotient.mk I G) = (0 : B' ⊗[B] (MvPowerSeries σ B ⧸ I)) := by
  apply he_inj
  rw [he, map_zero, Ideal.Quotient.eq_zero_iff_mem]
  exact hG

end DIaa
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_act_pow_mem_span_of_isODHom_of_hasKernelOfDegree.TruncBCEngine"

theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] [IsNoetherianRing B] (hp : IsNilpotent ((p : ℕ) : B))
    (X Y : FormalODModule p B) (ρ : Series B) (hρ : FormalODModule.IsODHom X Y ρ)
    (h : ℕ) (hdeg : FormalODModule.HasKernelOfDegree ρ (p ^ h)) :
    ∀ i : Fin 2, X.act ((p : Zp2 p) ^ h) i ∈ Ideal.span (Set.range ρ) := by
  classical
  intro i
  set I : Ideal (MvPowerSeries (Fin 2) B) := Ideal.span (Set.range ρ) with hI

  have hρ0 : ∀ j, MvPowerSeries.constantCoeff (ρ j) = 0 := hρ.constantCoeff
  have hunit : ∀ f ∈ I, MvPowerSeries.constantCoeff f = 0 := by
    intro f hf
    have : I ≤ RingHom.ker (MvPowerSeries.constantCoeff : MvPowerSeries (Fin 2) B →+* B) := by
      rw [hI, Ideal.span_le]; rintro _ ⟨j, rfl⟩; exact hρ0 j
    exact this hf
  have hmul : ∀ f ∈ I, MvPowerSeries.subst X.F.toPowerSeries f ∈
      Ideal.span
        ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) '' (I : Set (MvPowerSeries (Fin 2) B)) ∪
         (MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) '' (I : Set (MvPowerSeries (Fin 2) B))) := by
    intro f hf
    have h3 := (CerednikDrinfeld.FormalODModule.subst_mem_span_of_isODHom p X Y ρ hρ).2.2 f hf
    refine Ideal.span_mono ?_ h3
    rintro x (⟨j, rfl⟩ | ⟨j, rfl⟩)
    · exact Or.inl ⟨ρ j, Ideal.subset_span ⟨j, rfl⟩, rfl⟩
    · exact Or.inr ⟨ρ j, Ideal.subset_span ⟨j, rfl⟩, rfl⟩
  have hact : ∀ (a : Zp2 p), ∀ f ∈ I, MvPowerSeries.subst (X.act a) f ∈ I := by
    exact fun a f hf => (CerednikDrinfeld.FormalODModule.subst_mem_span_of_isODHom p X Y ρ hρ).1 a f hf
  have hvarpi : ∀ f ∈ I, MvPowerSeries.subst X.varpi f ∈ I := by
    exact fun f hf => (CerednikDrinfeld.FormalODModule.subst_mem_span_of_isODHom p X Y ρ hρ).2.1 f hf
  obtain ⟨q, hq⟩ := CerednikDrinfeld.FormalODModule.exists_X_pow_mem_span_of_hasKernelOfDegree ρ hρ0 hdeg
  have hrank : ∀ (κ : Type) [Field κ] (f : B →+* κ),
      Module.finrank κ (MvPowerSeries (Fin 2) κ ⧸ I.map (MvPowerSeries.map f)) = p ^ h := by
    intro κ _ f
    have hmap : I.map (MvPowerSeries.map f) = Ideal.span (Set.range (ρ.map f)) := by
      rw [hI, Ideal.map_span, ← Set.range_comp]; rfl
    rw [hmap]; exact hdeg.2.2 κ f

  obtain ⟨n, g, hg, hcov⟩ :=
    CerednikDrinfeld.FormalODModule.exists_cover_free_and_span_range_eq_map_of_subgroup_ideal p hp X I h
      hdeg.1 hdeg.2.1 hrank ⟨q, hq⟩ hunit hmul hact hvarpi

  suffices hloc : ∀ k : Fin n,
      MvPowerSeries.map (algebraMap B (Localization.Away (g k))) (X.act ((p : Zp2 p) ^ h) i) ∈
        I.map (MvPowerSeries.map (algebraMap B (Localization.Away (g k)))) by

    have hM := TruncBCEngine.pow_span_X_le_of_forall_X_pow_mem q I hq
    refine DIaa.mem_of_forall_map_mem_map_away I g hg (fun k G hG => ?_) _ hloc
    let e := TruncBCEngine.baseChangeEquiv (Localization.Away (g k)) ρ _ hM
    have hIk' : I.map (MvPowerSeries.map (algebraMap B (Localization.Away (g k)))) =
        Ideal.span (Set.range fun i => MvPowerSeries.map (algebraMap B (Localization.Away (g k))) (ρ i)) := by
      rw [hI, Ideal.map_span, ← Set.range_comp]; rfl
    have h0 : e ((1 : Localization.Away (g k)) ⊗ₜ[B] Ideal.Quotient.mk I G) = 0 := by
      rw [TruncBCEngine.baseChangeEquiv_tmul, one_smul, Ideal.Quotient.eq_zero_iff_mem, ← hIk']
      exact hG
    exact e.injective (h0.trans (map_zero e).symm)
  intro k

  have hρk : FormalODModule.IsODHom (X.map (algebraMap B (Localization.Away (g k)))) (Y.map (algebraMap B (Localization.Away (g k))))
      (ρ.map (algebraMap B (Localization.Away (g k)))) :=
    (FormalODModule.Hom.map (algebraMap B (Localization.Away (g k))) ⟨ρ, hρ⟩).isODHom
  have hIk : I.map (MvPowerSeries.map (algebraMap B (Localization.Away (g k)))) =
      Ideal.span (Set.range (ρ.map (algebraMap B (Localization.Away (g k))))) := by
    rw [hI, Ideal.map_span, ← Set.range_comp]; rfl

  rcases subsingleton_or_nontrivial (Localization.Away (g k)) with hsub | hnt
  · haveI : Subsingleton (MvPowerSeries (Fin 2) (Localization.Away (g k))) :=
      ⟨fun a b => by ext e; exact Subsingleton.elim _ _⟩
    rw [Subsingleton.elim (MvPowerSeries.map (algebraMap B (Localization.Away (g k))) (X.act ((p : Zp2 p) ^ h) i)) 0]
    exact Ideal.zero_mem _
  obtain ⟨hfin_k, hfree_k, hnil_k, u, hu0, huΔ, huI⟩ := hcov k

  have hunit_k : ∀ f ∈ I.map (MvPowerSeries.map (algebraMap B (Localization.Away (g k)))), MvPowerSeries.constantCoeff f = 0 := by
    intro f hf
    rw [hIk] at hf
    have : Ideal.span (Set.range (ρ.map (algebraMap B (Localization.Away (g k))))) ≤
        RingHom.ker (MvPowerSeries.constantCoeff : MvPowerSeries (Fin 2) (Localization.Away (g k)) →+* _) := by
      rw [Ideal.span_le]; rintro _ ⟨j, rfl⟩; exact hρk.constantCoeff j
    exact this hf
  have hmul_k : ∀ f ∈ I.map (MvPowerSeries.map (algebraMap B (Localization.Away (g k)))),
      MvPowerSeries.subst (X.map (algebraMap B (Localization.Away (g k)))).F.toPowerSeries f ∈
      Ideal.span
        ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) (Localization.Away (g k))))) ''
            ((I.map (MvPowerSeries.map (algebraMap B (Localization.Away (g k))))) : Set (MvPowerSeries (Fin 2) (Localization.Away (g k)))) ∪
         (MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) (Localization.Away (g k))))) ''
            ((I.map (MvPowerSeries.map (algebraMap B (Localization.Away (g k))))) : Set (MvPowerSeries (Fin 2) (Localization.Away (g k))))) := by
    intro f hf
    rw [hIk] at hf ⊢
    have h3 := (CerednikDrinfeld.FormalODModule.subst_mem_span_of_isODHom p _ _ _ hρk).2.2 f hf
    refine Ideal.span_mono ?_ h3
    rintro x (⟨j, rfl⟩ | ⟨j, rfl⟩)
    · exact Or.inl ⟨_, Ideal.subset_span ⟨j, rfl⟩, rfl⟩
    · exact Or.inr ⟨_, Ideal.subset_span ⟨j, rfl⟩, rfl⟩
  haveI := hfin_k
  haveI := hfree_k
  obtain ⟨L, instL, instH, instC, instFr, instFi, π, hπsurj, hπker, hπnil, hπeval, hπΔ, hπε, hπε'⟩ :=
    CerednikDrinfeld.FormalODModule.exists_hopfAlgebra_ker_eq_of_subgroup_ideal p
      (X.map (algebraMap B (Localization.Away (g k)))) (I.map (MvPowerSeries.map (algebraMap B (Localization.Away (g k)))))
      hfin_k hfree_k hnil_k hunit_k hmul_k

  have hrk : Module.finrank (Localization.Away (g k)) L = p ^ h := by

    have e1 : L ≃ₗ[Localization.Away (g k)]
        (MvPowerSeries (Fin 2) (Localization.Away (g k)) ⧸ Ideal.span (Set.range (ρ.map (algebraMap B (Localization.Away (g k)))))) :=
      ((Ideal.quotientKerAlgEquivOfSurjective hπsurj).symm.trans
        (Ideal.quotientEquivAlgOfEq (Localization.Away (g k)) (hπker.trans hIk))).toLinearEquiv

    obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal (Localization.Away (g k))
    letI : Field (Localization.Away (g k) ⧸ 𝔪) := Ideal.Quotient.field 𝔪

    have hqk : ∀ j : Fin 2, (MvPowerSeries.X j : MvPowerSeries (Fin 2) (Localization.Away (g k))) ^ q ∈
        Ideal.span (Set.range (ρ.map (algebraMap B (Localization.Away (g k))))) := by
      intro j
      rw [← hIk]
      have := Ideal.mem_map_of_mem (MvPowerSeries.map (algebraMap B (Localization.Away (g k)))) (hq j)
      rwa [map_pow, MvPowerSeries.map_X] at this
    have hMk := TruncBCEngine.pow_span_X_le_of_forall_X_pow_mem q _ hqk
    let e2 := TruncBCEngine.baseChangeEquiv (Localization.Away (g k) ⧸ 𝔪) (ρ.map (algebraMap B (Localization.Away (g k)))) _ hMk

    have hIκ : Ideal.span (Set.range fun i => MvPowerSeries.map (algebraMap (Localization.Away (g k)) (Localization.Away (g k) ⧸ 𝔪))
          ((ρ.map (algebraMap B (Localization.Away (g k)))) i)) =
        I.map (MvPowerSeries.map ((algebraMap (Localization.Away (g k)) (Localization.Away (g k) ⧸ 𝔪)).comp (algebraMap B (Localization.Away (g k))))) := by
      rw [hI, Ideal.map_span, ← Set.range_comp]
      congr 1
    calc Module.finrank (Localization.Away (g k)) L
        = Module.finrank (Localization.Away (g k) ⧸ 𝔪) ((Localization.Away (g k) ⧸ 𝔪) ⊗[Localization.Away (g k)] L) :=
          (Module.finrank_baseChange).symm
      _ = Module.finrank (Localization.Away (g k) ⧸ 𝔪)
            ((Localization.Away (g k) ⧸ 𝔪) ⊗[Localization.Away (g k)]
              (MvPowerSeries (Fin 2) (Localization.Away (g k)) ⧸ Ideal.span (Set.range (ρ.map (algebraMap B (Localization.Away (g k))))))) :=
          LinearEquiv.finrank_eq (e1.baseChange (Localization.Away (g k)) (Localization.Away (g k) ⧸ 𝔪) _ _)
      _ = Module.finrank (Localization.Away (g k) ⧸ 𝔪)
            (MvPowerSeries (Fin 2) (Localization.Away (g k) ⧸ 𝔪) ⧸
              I.map (MvPowerSeries.map ((algebraMap (Localization.Away (g k)) (Localization.Away (g k) ⧸ 𝔪)).comp (algebraMap B (Localization.Away (g k)))))) :=
          LinearEquiv.finrank_eq (e2.toLinearEquiv.trans (Ideal.quotientEquivAlgOfEq _ hIκ).toLinearEquiv)
      _ = p ^ h := hrank _ _

  have hD := HopfAlgebra.convPow_finrank_eq_one_of_isCocomm (Localization.Away (g k)) L L
    (toConv (AlgHom.id (Localization.Away (g k)) L))
  rw [hrk] at hD
  have hconv : ∀ (m : ℕ) (j : Fin 2), ((toConv (AlgHom.id (Localization.Away (g k)) L)) ^ m) (π (MvPowerSeries.X j)) =
      π ((X.map (algebraMap B (Localization.Away (g k)))).F.nthSeries m j) := by

    have hrad : ∀ j, π (MvPowerSeries.X j) ∈ (⊥ : Ideal L).radical := fun j => by
      obtain ⟨N, hN⟩ := hπnil j
      exact ⟨N, by rw [Ideal.mem_bot]; exact hN⟩
    let xπ : MvFormalGroup.Points (X.map (algebraMap B (Localization.Away (g k)))).F L (⊥ : Ideal L) :=
      ⟨fun j => π (MvPowerSeries.X j), hrad⟩
    have hx2 : ∀ s, Sum.elim (fun j => π (MvPowerSeries.X j) ⊗ₜ[Localization.Away (g k)] (1 : L))
        (fun j => (1 : L) ⊗ₜ[Localization.Away (g k)] π (MvPowerSeries.X j)) s ∈ (⊥ : Ideal (L ⊗[Localization.Away (g k)] L)).radical := by
      rintro (j | j)
      · obtain ⟨N, hN⟩ := hπnil j
        refine ⟨N, ?_⟩
        rw [Ideal.mem_bot]
        show (π (MvPowerSeries.X j) ⊗ₜ[Localization.Away (g k)] (1 : L)) ^ N = 0
        rw [Algebra.TensorProduct.tmul_pow, hN, TensorProduct.zero_tmul]
      · obtain ⟨N, hN⟩ := hπnil j
        refine ⟨N, ?_⟩
        rw [Ideal.mem_bot]
        show ((1 : L) ⊗ₜ[Localization.Away (g k)] π (MvPowerSeries.X j)) ^ N = 0
        rw [Algebra.TensorProduct.tmul_pow, hN, TensorProduct.tmul_zero]
    have key : ∀ m : ℕ, (fun j => ((toConv (AlgHom.id (Localization.Away (g k)) L)) ^ m) (π (MvPowerSeries.X j))) = (m • xπ).val := by
      intro m
      induction m with
      | zero =>
          funext j
          rw [pow_zero, AlgHom.convOne_apply, hπε, map_zero, zero_nsmul]
          rfl
      | succ m ih =>
          funext j
          rw [pow_succ, AlgHom.convMul_apply, hπΔ, succ_nsmul, MvFormalGroup.Points.val_add,
            MvFormalGroup.map_adicEval (⊥ : Ideal (L ⊗[Localization.Away (g k)] L)) (⊥ : Ideal L) _ Submodule.fg_bot
              (fun s hs => by rw [Ideal.mem_bot] at hs; rw [hs, map_zero]; exact Ideal.zero_mem _) hx2]
          congr 1
          funext s
          rcases s with jj | jj
          · show (Algebra.TensorProduct.lift _ _ _) (π (MvPowerSeries.X jj) ⊗ₜ[Localization.Away (g k)] (1 : L)) = (m • xπ).val jj
            rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one, ← ih]
          · show (Algebra.TensorProduct.lift _ _ _) ((1 : L) ⊗ₜ[Localization.Away (g k)] π (MvPowerSeries.X jj)) = xπ.val jj
            rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
            rfl
    intro m j
    rw [show ((toConv (AlgHom.id (Localization.Away (g k)) L)) ^ m) (π (MvPowerSeries.X j)) = (m • xπ).val j from congrFun (key m) j,
      MvFormalGroup.Points.val_nsmul, hπeval]
  have hzero : π ((X.map (algebraMap B (Localization.Away (g k)))).F.nthSeries (p ^ h) i) = 0 := by
    rw [← hconv, hD, AlgHom.convOne_apply, hπε, map_zero]
  have hmem : (X.map (algebraMap B (Localization.Away (g k)))).F.nthSeries (p ^ h) i ∈
      I.map (MvPowerSeries.map (algebraMap B (Localization.Away (g k)))) := by
    rw [← hπker]; exact hzero

  have hact_eq : MvPowerSeries.map (algebraMap B (Localization.Away (g k))) (X.act ((p : Zp2 p) ^ h) i) =
      (X.map (algebraMap B (Localization.Away (g k)))).F.nthSeries (p ^ h) i := by
    have hnat := (X.map (algebraMap B (Localization.Away (g k)))).act_natCast (p ^ h)
    rw [Nat.cast_pow] at hnat
    rw [← hnat]
    rfl
  rw [hact_eq]; exact hmem

end S_CerednikDrinfeld_FormalODModule_act_pow_mem_span_of_isODHom_of_hasKernelOfDegree
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_act_pow_mem_span_of_isODHom_of_hasKernelOfDegree (solution)
