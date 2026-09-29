-- Prove2me | solution 1 for GaloisRepAdic.isFlatAt_of_forall_point_of_finite_index
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/bfbfdc93-4be3-5754-91e5-65c845b20444

import Mathlib.RingTheory.HopfAlgebra.TensorProduct
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Ideal.Quotient.Index
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_GaloisRep_exists_finiteFlat_sub_of_equivariant_injection
import Theorems.Thm_GaloisRep_exists_finiteFlat_quotient_of_equivariant_surjection
import Theorems.Thm_HopfAlgebra_exists_withConv_tensorProduct_equiv_prod
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRepAdic_isFlatAt_of_forall_point_of_finite_index

open scoped TensorProduct

theorem exists_pow_natCast_mem_of_finite_quotient {P : Type} [CommRing P] [IsLocalRing P]
    {p : ℕ} (hp : (p : P) ∈ IsLocalRing.maximalIdeal P) (I : Ideal P) (hI : Finite (P ⧸ I)) :
    ∃ m : ℕ, (p : P) ^ m ∈ I := by
  by_cases hIt : I = ⊤
  · exact ⟨0, by simp [hIt]⟩
  haveI : Nontrivial (P ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hIt
  haveI : IsLocalRing (P ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  haveI : IsArtinianRing (P ⧸ I) := isArtinian_of_finite
  obtain ⟨k, hk⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := P ⧸ I)
  have hloc : IsLocalHom (Ideal.Quotient.mk I) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hpmem : Ideal.Quotient.mk I (p : P) ∈ IsLocalRing.maximalIdeal (P ⧸ I) := by
    rw [IsLocalRing.mem_maximalIdeal] at hp ⊢
    exact fun hu => hp (hloc.map_nonunit _ hu)
  refine ⟨k, ?_⟩
  have hmk : (Ideal.Quotient.mk I (p : P)) ^ k = 0 := by
    have hle : IsLocalRing.maximalIdeal (P ⧸ I) ^ k ≤ (⊥ : Ideal (P ⧸ I)).jacobson ^ k :=
      Ideal.pow_right_mono (IsLocalRing.maximalIdeal_le_jacobson ⊥) k
    have hmem : (Ideal.Quotient.mk I (p : P)) ^ k ∈ ((⊥ : Ideal (P ⧸ I)).jacobson) ^ k :=
      hle (Ideal.pow_mem_pow hpmem k)
    rw [hk] at hmem
    simpa using hmem
  rwa [← map_pow, Ideal.Quotient.eq_zero_iff_mem] at hmk

theorem pow_dvd_of_forall_pow_dvd_algebraMap {P : Type} [CommRing P] {n : ℕ}
    {A : Fin n → Type} [∀ i, CommRing (A i)] [∀ i, Algebra P (A i)]
    (hinj : ∀ x : P, (∀ i, algebraMap P (A i) x = 0) → x = 0)
    {p c : ℕ} (hidx : ∀ a : ∀ i, A i, ∃ x : P, ∀ i, algebraMap P (A i) x = (p : A i) ^ c * a i)
    (m : ℕ) (x : P) (hx : ∀ i, (p : A i) ^ (m + c) ∣ algebraMap P (A i) x) :
    (p : P) ^ m ∣ x := by
  choose a ha using hx
  obtain ⟨y, hy⟩ := hidx a
  refine ⟨y, ?_⟩
  have h0 : ∀ i, algebraMap P (A i) (x - (p : P) ^ m * y) = 0 := by
    intro i
    rw [map_sub, map_mul, map_pow, map_natCast, ha i, hy i, pow_add]
    ring
  have := hinj _ h0
  rw [sub_eq_zero] at this
  exact this

theorem mem_span_pow_smul_of_forall_tmul_mem {P : Type} [CommRing P] {n : ℕ}
    {A : Fin n → Type} [∀ i, CommRing (A i)] [∀ i, Algebra P (A i)]
    (hinj : ∀ x : P, (∀ i, algebraMap P (A i) x = 0) → x = 0)
    {p c : ℕ} (hidx : ∀ a : ∀ i, A i, ∃ x : P, ∀ i, algebraMap P (A i) x = (p : A i) ^ c * a i)
    (m : ℕ) {V : Type} [AddCommGroup V] [Module P V] [Module.Free P V] [Module.Finite P V]
    (v : V)
    (hv : ∀ i, (1 : A i) ⊗ₜ[P] v ∈
      (Ideal.span {(p : A i) ^ (m + c)} : Ideal (A i)) • (⊤ : Submodule (A i) (A i ⊗[P] V))) :
    v ∈ (Ideal.span {(p : P) ^ m} : Ideal P) • (⊤ : Submodule P V) := by
  classical
  set b := Module.Free.chooseBasis P V with hb
  have hcoord : ∀ (i : Fin n) (j : Module.Free.ChooseBasisIndex P V),
      (p : A i) ^ (m + c) ∣ algebraMap P (A i) (b.repr v j) := by
    intro i j
    have h := hv i
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h
    obtain ⟨w, -, hw⟩ := h
    refine ⟨(Algebra.TensorProduct.basis (A i) b).repr w j, ?_⟩
    have hrepr := congrArg (fun z => (Algebra.TensorProduct.basis (A i) b).repr z j) hw.symm
    simpa [Algebra.TensorProduct.basis_repr_tmul, Finsupp.mapRange_apply, map_smul,
      Finsupp.smul_apply, smul_eq_mul] using hrepr
  have hdvd : ∀ j, (p : P) ^ m ∣ b.repr v j := fun j =>
    pow_dvd_of_forall_pow_dvd_algebraMap hinj hidx m _ (fun i => hcoord i j)
  choose y hy using hdvd
  have hvsum : v = (p : P) ^ m • (∑ j, y j • b j) := by
    conv_lhs => rw [← b.sum_repr v]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hy j, mul_smul]
  rw [Submodule.ideal_span_singleton_smul, hvsum]
  exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top

namespace FlatPts

variable {P : Type} [CommRing P] {n : ℕ} {A : Fin n → Type} [∀ i, CommRing (A i)]
  [∀ i, Algebra P (A i)] {V : Type} [AddCommGroup V] [Module P V]

variable (J : ∀ i, Ideal (A i))

noncomputable def toLevels :
    V →ₗ[P] ∀ i, (A i ⊗[P] V) ⧸ (J i • (⊤ : Submodule (A i) (A i ⊗[P] V))) :=
  LinearMap.pi fun i =>
    (((J i • (⊤ : Submodule (A i) (A i ⊗[P] V))).mkQ.restrictScalars P).comp
      ((TensorProduct.mk P (A i) V) 1))

@[scoped simp] lemma toLevels_apply (v : V) (i : Fin n) :
    toLevels (P := P) (V := V) J v i = Submodule.Quotient.mk ((1 : A i) ⊗ₜ[P] v) := rfl

lemma mem_ker_toLevels_iff (v : V) :
    v ∈ LinearMap.ker (toLevels (P := P) (V := V) J) ↔
      ∀ i, (1 : A i) ⊗ₜ[P] v ∈ (J i • (⊤ : Submodule (A i) (A i ⊗[P] V))) := by
  simp only [LinearMap.mem_ker, funext_iff, toLevels_apply, Pi.zero_apply,
    Submodule.Quotient.mk_eq_zero]

lemma map_baseChange_smul_top_le (f : Module.End P V) (i : Fin n) :
    (J i • (⊤ : Submodule (A i) (A i ⊗[P] V))).map (f.baseChange (A i)) ≤
      J i • (⊤ : Submodule (A i) (A i ⊗[P] V)) := by
  rw [Submodule.map_smul'']
  exact Submodule.smul_mono le_rfl le_top

noncomputable def levelEnd (f : Module.End P V) (i : Fin n) :
    Module.End (A i) ((A i ⊗[P] V) ⧸ (J i • (⊤ : Submodule (A i) (A i ⊗[P] V)))) :=
  Submodule.mapQ _ _ (f.baseChange (A i)) (Submodule.map_le_iff_le_comap.mp
    (map_baseChange_smul_top_le J f i))

lemma toLevels_comp_end (f : Module.End P V) (v : V) (i : Fin n) :
    toLevels (P := P) (V := V) J (f v) i = levelEnd J f i (toLevels (P := P) (V := V) J v i) := by
  simp only [toLevels_apply, levelEnd, Submodule.mapQ_apply, LinearMap.baseChange_tmul]

lemma ker_toLevels_stable (f : Module.End P V) (v : V)
    (hv : v ∈ LinearMap.ker (toLevels (P := P) (V := V) J)) : f v ∈ LinearMap.ker (toLevels (P := P) (V := V) J) := by
  rw [LinearMap.mem_ker] at hv ⊢
  funext i
  have h0 : toLevels (P := P) (V := V) J v i = 0 := by rw [hv]; rfl
  rw [toLevels_comp_end J f v i, h0, map_zero]
  rfl

noncomputable def embed :
    (V ⧸ LinearMap.ker (toLevels (P := P) (V := V) J)) →ₗ[P]
      ∀ i, (A i ⊗[P] V) ⧸ (J i • (⊤ : Submodule (A i) (A i ⊗[P] V))) :=
  letI : AddCommGroup (∀ i, (A i ⊗[P] V) ⧸ (J i • (⊤ : Submodule (A i) (A i ⊗[P] V)))) :=
    Pi.addCommGroup
  letI : Module P (∀ i, (A i ⊗[P] V) ⧸ (J i • (⊤ : Submodule (A i) (A i ⊗[P] V)))) :=
    Pi.module _ _ _
  (LinearMap.ker (toLevels (P := P) (V := V) J)).liftQ (toLevels (P := P) (V := V) J) le_rfl

@[scoped simp] lemma embed_mk (v : V) :
    embed (P := P) (V := V) J (Submodule.Quotient.mk v) = toLevels (P := P) (V := V) J v := rfl

lemma embed_injective : Function.Injective (embed (P := P) (V := V) J) := by
  letI : AddCommGroup (∀ i, (A i ⊗[P] V) ⧸ (J i • (⊤ : Submodule (A i) (A i ⊗[P] V)))) :=
    Pi.addCommGroup
  letI : Module P (∀ i, (A i ⊗[P] V) ⧸ (J i • (⊤ : Submodule (A i) (A i ⊗[P] V)))) :=
    Pi.module _ _ _
  have h := Submodule.ker_liftQ_eq_bot' (LinearMap.ker (toLevels (P := P) (V := V) J))
    (toLevels (P := P) (V := V) J) rfl
  exact LinearMap.ker_eq_bot.mp h

lemma embed_comp (f : Module.End P V) (v : V) (i : Fin n) :
    embed (P := P) (V := V) J (Submodule.Quotient.mk (f v)) i = levelEnd J f i (embed (P := P) (V := V) J (Submodule.Quotient.mk v) i) :=
  toLevels_comp_end J f v i

lemma ker_toLevels_le [Module.Free P V] [Module.Finite P V]
    (hinj : ∀ x : P, (∀ i, algebraMap P (A i) x = 0) → x = 0)
    {p c : ℕ} (hidx : ∀ a : ∀ i, A i, ∃ x : P, ∀ i, algebraMap P (A i) x = (p : A i) ^ c * a i)
    (m : ℕ) (hJ : ∀ i, J i = Ideal.span {(p : A i) ^ (m + c)}) :
    LinearMap.ker (toLevels (P := P) (V := V) J) ≤ (Ideal.span {(p : P) ^ m} : Ideal P) • (⊤ : Submodule P V) := by
  intro v hv
  rw [mem_ker_toLevels_iff] at hv
  refine mem_span_pow_smul_of_forall_tmul_mem hinj hidx m v (fun i => ?_)
  have := hv i
  rwa [hJ i] at this

end FlatPts
p2m_reactivate "P2MW.S_GaloisRepAdic_isFlatAt_of_forall_point_of_finite_index.FlatPts"

namespace GaloisRep
p2m_export "GaloisRep" "ratLocalizedAt exists_finiteFlat_sub_of_equivariant_injection exists_finiteFlat_quotient_of_equivariant_surjection"
p2m_open "GaloisRep"

def PointsModel (p : ℕ) (M : Type) [AddCommGroup M]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) M] : Prop :=
  ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra (GaloisRep.ratLocalizedAt p) H),
    Module.Finite (GaloisRep.ratLocalizedAt p) H ∧ Module.Flat (GaloisRep.ratLocalizedAt p) H ∧
    Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H ∧
    ∃ e' : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ M,
      (∀ f g, e' (f * g) = e' f + e' g) ∧
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
        (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
        (∀ x : H, g x = σ (f x)) → e' g = σ • (e' f)

theorem pointsModel_of_subsingleton (p : ℕ) (M : Type) [AddCommGroup M]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) M] [Subsingleton M] :
    PointsModel p M := by
  refine ⟨GaloisRep.ratLocalizedAt p, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, ?_⟩
  refine ⟨Equiv.ofBijective (fun _ => 0) ⟨fun f g _ => ?_, fun m => ⟨1, Subsingleton.elim _ _⟩⟩,
    fun _ _ => by simp, fun _ _ _ _ => Subsingleton.elim _ _⟩
  exact WithConv.ext (Subsingleton.elim _ _)

theorem pointsModel_prod (p : ℕ) {M₁ M₂ : Type} [AddCommGroup M₁] [AddCommGroup M₂]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) M₁]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) M₂]
    (h₁ : PointsModel p M₁) (h₂ : PointsModel p M₂) : PointsModel p (M₁ × M₂) := by
  obtain ⟨H₁, _, _, hfin₁, hfl₁, hco₁, e₁, he₁_add, he₁_act⟩ := h₁
  obtain ⟨H₂, _, _, hfin₂, hfl₂, hco₂, e₂, he₂_add, he₂_act⟩ := h₂
  obtain ⟨eT, heT_mul, heT_act⟩ :=
    HopfAlgebra.exists_withConv_tensorProduct_equiv_prod (R := GaloisRep.ratLocalizedAt p)
      (Γ := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) H₁ H₂ (L := AlgebraicClosure ℚ)
  refine ⟨H₁ ⊗[GaloisRep.ratLocalizedAt p] H₂, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, ?_⟩
  refine ⟨eT.trans (Equiv.prodCongr e₁ e₂), fun f g => ?_, fun σ f g hfg => ?_⟩
  · ext <;> simp [heT_mul, he₁_add, he₂_add]
  · obtain ⟨h1, h2⟩ := heT_act σ f g hfg
    ext
    · simpa using he₁_act σ (eT f).1 (eT g).1 h1
    · simpa using he₂_act σ (eT f).2 (eT g).2 h2

theorem pointsModel_congr (p : ℕ) {M N : Type} [AddCommGroup M] [AddCommGroup N]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) M]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) N]
    (h : PointsModel p M) (e : M ≃+ N)
    (he : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (m : M), e (σ • m) = σ • e m) :
    PointsModel p N := by
  obtain ⟨H, _, _, hfin, hfl, hco, e₀, he₀_add, he₀_act⟩ := h
  refine ⟨H, inferInstance, inferInstance, hfin, hfl, hco, e₀.trans e.toEquiv, fun f g => ?_,
    fun σ f g hfg => ?_⟩
  · simp [he₀_add]
  · simp [he₀_act σ f g hfg, he]

theorem pointsModel_pi (p : ℕ) :
    ∀ (n : ℕ) (M : Fin n → Type) [∀ i, AddCommGroup (M i)]
      [∀ i, DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (M i)],
      (∀ i, PointsModel p (M i)) → PointsModel p (∀ i, M i)
  | 0, M, _, _, _ => pointsModel_of_subsingleton p _
  | n + 1, M, _, _, h => by
    have h' := pointsModel_prod p (h 0) (pointsModel_pi p n (fun i => M i.succ) fun i => h i.succ)
    refine pointsModel_congr p h'
      { (Fin.consEquiv M) with
        map_add' := fun x y => by
          ext i
          refine Fin.cases ?_ (fun j => ?_) i <;> simp } ?_
    intro σ x
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem pointsModel_of_injective (p : ℕ) {M N : Type} [AddCommGroup M] [AddCommGroup N]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) M]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) N]
    (h : PointsModel p M) (ι : N →+ M) (hι : Function.Injective ι)
    (hι_eq : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (n : N), ι (σ • n) = σ • (ι n)) :
    PointsModel p N := by
  obtain ⟨H, _, _, hfin, hfl, hco, e, he_add, he_act⟩ := h
  exact GaloisRep.exists_finiteFlat_sub_of_equivariant_injection p H e he_add he_act ι hι hι_eq

theorem pointsModel_of_surjective (p : ℕ) {M N : Type} [AddCommGroup M] [AddCommGroup N]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) M]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) N]
    (h : PointsModel p M) (π : M →+ N) (hπ : Function.Surjective π)
    (hπ_eq : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (m : M), π (σ • m) = σ • (π m)) :
    PointsModel p N := by
  obtain ⟨H, _, _, hfin, hfl, hco, e, he_add, he_act⟩ := h
  exact GaloisRep.exists_finiteFlat_quotient_of_equivariant_surjection p H e he_add he_act π hπ hπ_eq

theorem pointsModel_of_sub_of_quotient (p n : ℕ) (M : Fin n → Type) [∀ i, AddCommGroup (M i)]
    [∀ i, DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (M i)]
    (hM : ∀ i, PointsModel p (M i))
    {N : Type} [AddCommGroup N] [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) N]
    (ι : N →+ ∀ i, M i) (hι : Function.Injective ι)
    (hι_eq : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : N), ι (σ • x) = σ • (ι x))
    {Q : Type} [AddCommGroup Q] [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) Q]
    (π : N →+ Q) (hπ : Function.Surjective π)
    (hπ_eq : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : N), π (σ • x) = σ • (π x)) :
    PointsModel p Q :=
  pointsModel_of_surjective p
    (pointsModel_of_injective p (pointsModel_pi p n M hM) ι hι hι_eq) π hπ hπ_eq

end GaloisRep
p2m_reactivate "P2MW.S_GaloisRepAdic_isFlatAt_of_forall_point_of_finite_index.FlatPts"

namespace GaloisRepAdic
p2m_export "GaloisRepAdic" "levelAction IsFlatAt baseChangeAlong Equiv ρ mk V"
p2m_open "GaloisRepAdic"

variable {A : Type} [CommRing A] [IsLocalRing A]

private noncomputable def _root_.GaloisRepAdic.levelActionHom (ρ : GaloisRepAdic A) (I : Ideal A) :
    (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End A (ρ.V ⧸ (I • (⊤ : Submodule A ρ.V))) where
  toFun := ρ.levelAction I
  map_one' := by
    refine LinearMap.ext fun x => ?_
    induction x using Submodule.Quotient.induction_on with
    | H v => simp [levelAction, Submodule.mapQ_apply]
  map_mul' σ τ := by
    refine LinearMap.ext fun x => ?_
    induction x using Submodule.Quotient.induction_on with
    | H v => simp [levelAction, Submodule.mapQ_apply]

p2m_export "GaloisRepAdic" "levelActionHom"

@[reducible] private noncomputable def _root_.GaloisRepAdic.levelDistribMulAction (ρ : GaloisRepAdic A) (I : Ideal A) :
    DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (ρ.V ⧸ (I • (⊤ : Submodule A ρ.V))) :=
  DistribMulAction.compHom _ (ρ.levelActionHom I)

p2m_export "GaloisRepAdic" "levelDistribMulAction"
theorem levelDistribMulAction_smul (ρ : GaloisRepAdic A) (I : Ideal A)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : ρ.V ⧸ (I • (⊤ : Submodule A ρ.V))) :
    letI := ρ.levelDistribMulAction I
    σ • x = ρ.levelAction I σ x := rfl

theorem pointsModel_level_of_isFlatAt (ρ : GaloisRepAdic A) {p : ℕ} (h : ρ.IsFlatAt p)
    (I : Ideal A) (hI : Finite (A ⧸ I)) :
    letI := ρ.levelDistribMulAction I
    GaloisRep.PointsModel p (ρ.V ⧸ (I • (⊤ : Submodule A ρ.V))) :=
  h.2 I hI

private theorem _root_.GaloisRepAdic.isFlatAt_of_pointsModel (ρ : GaloisRepAdic A) {p : ℕ}
    (hk : Finite (IsLocalRing.ResidueField A))
    (h : ∀ I : Ideal A, Finite (A ⧸ I) →
      letI := ρ.levelDistribMulAction I
      GaloisRep.PointsModel p (ρ.V ⧸ (I • (⊤ : Submodule A ρ.V)))) :
    ρ.IsFlatAt p :=
  ⟨hk, h⟩

p2m_export "GaloisRepAdic" "isFlatAt_of_pointsModel"

private noncomputable def _root_.GaloisRepAdic.quotActionHom (ρ : GaloisRepAdic A) (W : Submodule A ρ.V)
    (hW : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, W ≤ W.comap (ρ.ρ σ)) :
    (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End A (ρ.V ⧸ W) where
  toFun σ := W.mapQ W (ρ.ρ σ) (hW σ)
  map_one' := by
    refine LinearMap.ext fun x => ?_
    induction x using Submodule.Quotient.induction_on with
    | H v => simp [Submodule.mapQ_apply]
  map_mul' σ τ := by
    refine LinearMap.ext fun x => ?_
    induction x using Submodule.Quotient.induction_on with
    | H v => simp [Submodule.mapQ_apply]

p2m_export "GaloisRepAdic" "quotActionHom"
@[reducible] private noncomputable def _root_.GaloisRepAdic.quotDistribMulAction (ρ : GaloisRepAdic A) (W : Submodule A ρ.V)
    (hW : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, W ≤ W.comap (ρ.ρ σ)) :
    DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (ρ.V ⧸ W) :=
  DistribMulAction.compHom _ (ρ.quotActionHom W hW)

p2m_export "GaloisRepAdic" "quotDistribMulAction"
theorem quotDistribMulAction_smul_mk (ρ : GaloisRepAdic A) (W : Submodule A ρ.V)
    (hW : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, W ≤ W.comap (ρ.ρ σ))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (v : ρ.V) :
    letI := ρ.quotDistribMulAction W hW
    σ • Submodule.Quotient.mk (p := W) v = Submodule.Quotient.mk (ρ.ρ σ v) := rfl

theorem levelDistribMulAction_smul_mk (ρ : GaloisRepAdic A) (I : Ideal A)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (v : ρ.V) :
    letI := ρ.levelDistribMulAction I
    σ • Submodule.Quotient.mk (p := I • (⊤ : Submodule A ρ.V)) v =
      Submodule.Quotient.mk (ρ.ρ σ v) := rfl

private theorem _root_.GaloisRepAdic.factor_surjective_equivariant (ρ : GaloisRepAdic A) (W : Submodule A ρ.V)
    (hW : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, W ≤ W.comap (ρ.ρ σ))
    (I : Ideal A) (hWI : W ≤ I • (⊤ : Submodule A ρ.V)) :
    letI := ρ.quotDistribMulAction W hW
    letI := ρ.levelDistribMulAction I
    Function.Surjective (Submodule.factor hWI).toAddMonoidHom ∧
    ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : ρ.V ⧸ W),
      (Submodule.factor hWI).toAddMonoidHom (σ • x) = σ • (Submodule.factor hWI).toAddMonoidHom x := by
  refine ⟨Submodule.factor_surjective hWI, fun σ x => ?_⟩
  induction x using Submodule.Quotient.induction_on with
  | H v => rfl

p2m_export "GaloisRepAdic" "factor_surjective_equivariant"
end GaloisRepAdic
p2m_reactivate "P2MW.S_GaloisRepAdic_isFlatAt_of_forall_point_of_finite_index.FlatPts"

theorem solution
    {P : Type} [CommRing P] [IsLocalRing P] {n : ℕ} {A : Fin n → Type}
    [∀ i, CommRing (A i)] [∀ i, IsLocalRing (A i)]
    (χ : ∀ i, P →+* A i) (hχ : ∀ i, IsLocalHom (χ i))
    (hinj : ∀ x, (∀ i, χ i x = 0) → x = 0)
    {p c : ℕ} (hpP : (p : P) ∈ IsLocalRing.maximalIdeal P)
    (hidx : ∀ a : ∀ i, A i, ∃ x : P, ∀ i, χ i x = (p : A i) ^ c * a i)
    (hAfin : ∀ i, Finite (A i ⧸ Ideal.span {(p : A i)}))
    (ρ : GaloisRepAdic P) (hflat : ∀ i, (ρ.baseChangeAlong (χ i) (hχ i)).IsFlatAt p) :
    ρ.IsFlatAt p := by
  classical
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact absurd (hinj 1 fun i => i.elim0) one_ne_zero
  have i₀ : Fin n := ⟨0, hn⟩
  have hk : Finite (IsLocalRing.ResidueField P) := by
    haveI := hχ i₀
    haveI := (hflat i₀).1
    exact Finite.of_injective _ (IsLocalRing.ResidueField.map (χ i₀)).injective
  letI : ∀ i, Algebra P (A i) := fun i => (χ i).toAlgebra
  refine ρ.isFlatAt_of_pointsModel hk fun I hI => ?_
  obtain ⟨m, hm⟩ := exists_pow_natCast_mem_of_finite_quotient hpP I hI

  let J : ∀ i, Ideal (A i) := fun i => Ideal.span {(p : A i) ^ (m + c)}
  have hJfin : ∀ i, Finite (A i ⧸ J i) := fun i => by
    haveI := hAfin i
    have h := Ideal.finite_quotient_pow (Submodule.fg_span_singleton (p : A i)) (m + c)
    rwa [Ideal.span_singleton_pow] at h

  let M : Fin n → Type := fun i => (A i ⊗[P] ρ.V) ⧸ (J i • (⊤ : Submodule (A i) (A i ⊗[P] ρ.V)))
  letI instM : ∀ i, DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (M i) :=
    fun i => (ρ.baseChangeAlong (χ i) (hχ i)).levelDistribMulAction (J i)
  have hM : ∀ i, GaloisRep.PointsModel p (M i) := fun i => (hflat i).2 (J i) (hJfin i)

  let K : Submodule P ρ.V := LinearMap.ker (FlatPts.toLevels (P := P) (V := ρ.V) J)
  have hK : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, K ≤ K.comap (ρ.ρ σ) :=
    fun σ v hv => FlatPts.ker_toLevels_stable J (ρ.ρ σ) v hv
  letI := ρ.quotDistribMulAction K hK
  letI := ρ.levelDistribMulAction I
  have hKI : K ≤ I • (⊤ : Submodule P ρ.V) :=
    (FlatPts.ker_toLevels_le J hinj hidx m fun _ => rfl).trans
      (Submodule.smul_mono_left ((Ideal.span_singleton_le_iff_mem _).mpr hm))
  obtain ⟨hπ, hπ_eq⟩ := ρ.factor_surjective_equivariant K hK I hKI
  refine GaloisRep.pointsModel_of_sub_of_quotient p n M hM
    (FlatPts.embed (P := P) (V := ρ.V) J).toAddMonoidHom (FlatPts.embed_injective J)
    (fun σ x => ?_) _ hπ hπ_eq
  induction x using Submodule.Quotient.induction_on with
  | H v =>
    funext i
    exact FlatPts.embed_comp J (ρ.ρ σ) v i

end S_GaloisRepAdic_isFlatAt_of_forall_point_of_finite_index
end P2MW
export P2MW.S_GaloisRepAdic_isFlatAt_of_forall_point_of_finite_index (solution)
