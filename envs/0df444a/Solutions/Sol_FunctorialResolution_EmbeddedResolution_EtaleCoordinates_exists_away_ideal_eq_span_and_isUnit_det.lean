-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.EtaleCoordinates.exists_away_ideal_eq_span_and_isUnit_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:00:21.753987+00:00
-- url     : https://prove2.me/submissions/4cecb296-e5f4-4da9-beb2-cac326283663

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_FormallyEtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_IdealGeneratorsFromBase
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_SpanSingletonProduct
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_LocalNormalForm
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_algebraMap_coord
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_algebraMap_det_basisKaehler
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_basisDerivation_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_exists_away_map_ideal_eq
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_exists_basis_sum_of_linearIndependent
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_JacobianCriterion_coordBasis_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_JacobianCriterion_inducedBasis_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_JacobianCriterion_tensorKaehlerBasis_mapBaseChange
import Theorems.Thm_KaehlerDifferential_residue_tmul_D_mul_of_mem_maximalIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.basisDerivation_apply
attribute [local simp] FunctorialResolution.EmbeddedResolution.JacobianCriterion.coordBasis_apply
attribute [local simp] FunctorialResolution.EmbeddedResolution.JacobianCriterion.inducedBasis_apply
attribute [local simp] FunctorialResolution.EmbeddedResolution.JacobianCriterion.tensorKaehlerBasis_mapBaseChange


section
open scoped TensorProduct
namespace FunctorialResolution.EmbeddedResolution
namespace EtaleCoordinates
section
private theorem repr_mem_maximalIdeal_of_tmul_eq_zero {A : Type*} [CommRing A] [IsLocalRing A]
    {M : Type*} [AddCommGroup M] [Module A M] {n : Type*} [Fintype n]
    (bb : Module.Basis n A M) (x : M)
    (h : (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] x = 0) (i : n) :
    bb.repr x i ∈ IsLocalRing.maximalIdeal A := by
  classical
  obtain ⟨bk, hbk⟩ : ∃ bk : Module.Basis n (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField A ⊗[A] M),
      ∀ j, bk j = (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] bb j :=
    ⟨Algebra.TensorProduct.basis (IsLocalRing.ResidueField A) bb, fun j => by simp⟩
  have hkey : ∀ (c : A) (m : M), (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (c • m)
      = IsLocalRing.residue A c • ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] m) := by
    intro c m
    have hA1 : (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (c • m)
        = (c • (1 : IsLocalRing.ResidueField A)) ⊗ₜ[A] m := (TensorProduct.smul_tmul c 1 m).symm
    have hA2 : c • (1 : IsLocalRing.ResidueField A) = IsLocalRing.residue A c := by
      rw [Algebra.smul_def, mul_one, IsLocalRing.ResidueField.algebraMap_eq]
    have hA3 : IsLocalRing.residue A c • ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] m)
        = (IsLocalRing.residue A c * 1) ⊗ₜ[A] m := rfl
    rw [hA1, hA2, hA3, mul_one]
  have hxsum : (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] x
      = ∑ j : n, IsLocalRing.residue A (bb.repr x j) • bk j := by
    conv_lhs => rw [← bb.sum_repr x]
    rw [TensorProduct.tmul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [hkey, hbk j]
  have h2 : bk.repr ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] x) i = 0 := by
    rw [h]
    simp
  rw [hxsum, Module.Basis.repr_sum_self] at h2
  rw [← IsLocalRing.residue_eq_zero_iff]
  exact h2
private theorem residue_det_ne_zero_of_tmul_eq_basis {A : Type*} [CommRing A] [IsLocalRing A]
    {M : Type*} [AddCommGroup M] [Module A M] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (bA : Module.Basis ι A M) (G : ι → M)
    (B' : Module.Basis ι (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A ⊗[A] M))
    (hB' : ∀ i, B' i = (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] G i) :
    IsLocalRing.residue A (bA.det G) ≠ 0 := by
  classical
  obtain ⟨bk, hbk⟩ : ∃ bk : Module.Basis ι (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField A ⊗[A] M),
      ∀ i, bk i = (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] bA i :=
    ⟨Algebra.TensorProduct.basis (IsLocalRing.ResidueField A) bA, fun i => by simp⟩
  have hkey : ∀ (c : A) (m : M), (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (c • m)
      = IsLocalRing.residue A c • ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] m) := by
    intro c m
    have hA1 : (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (c • m)
        = (c • (1 : IsLocalRing.ResidueField A)) ⊗ₜ[A] m := (TensorProduct.smul_tmul c 1 m).symm
    have hA2 : c • (1 : IsLocalRing.ResidueField A) = IsLocalRing.residue A c := by
      rw [Algebra.smul_def, mul_one, IsLocalRing.ResidueField.algebraMap_eq]
    have hA3 : IsLocalRing.residue A c • ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] m)
        = (IsLocalRing.residue A c * 1) ⊗ₜ[A] m := rfl
    rw [hA1, hA2, hA3, mul_one]
  have hmat : ∀ i j : ι, bk.repr (B' j) i = IsLocalRing.residue A (bA.toMatrix G i j) := by
    intro i j
    have hGj : B' j = ∑ l : ι, IsLocalRing.residue A (bA.repr (G j) l) • bk l := by
      rw [hB' j]
      conv_lhs => rw [← bA.sum_repr (G j)]
      rw [TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hkey, hbk l]
    rw [hGj, Module.Basis.repr_sum_self, Module.Basis.toMatrix_apply]
  have hdet : bk.det (⇑B') = IsLocalRing.residue A (bA.det G) := by
    rw [Module.Basis.det_apply, Module.Basis.det_apply, RingHom.map_det]
    congr 1
    ext i j
    simp only [Module.Basis.toMatrix_apply]
    exact hmat i j
  rw [← hdet]
  exact (bk.isUnit_det B').ne_zero
private theorem mem_maximalIdeal_mul_of_tmul_D_eq_zero (k : Type*) [CommRing k] (A : Type*)
    [CommRing A] [Algebra k A] [IsLocalRing A] {n : Type*} [Fintype n]
    (bb : Module.Basis n A (KaehlerDifferential k A))
    (J : Ideal A) (hJmax : J ≤ IsLocalRing.maximalIdeal A)
    [Algebra.FormallySmooth k (A ⧸ J)] (z : A) (hz : z ∈ J)
    (h0 : (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A z = 0) :
    z ∈ IsLocalRing.maximalIdeal A * J := by
  classical
  obtain ⟨Jm, hJmdef⟩ : ∃ Jm : Ideal A, Jm = IsLocalRing.maximalIdeal A * J := ⟨_, rfl⟩
  have hmulJ : ∀ c ∈ IsLocalRing.maximalIdeal A, ∀ u ∈ J, c * u ∈ Jm := by
    intro c hc u hu
    rw [hJmdef]
    exact Ideal.mul_mem_mul hc hu
  have hJmle : Jm ≤ J := by
    rw [hJmdef]
    exact Ideal.mul_le_right
  have hsmulg : ∀ (c : A) (x : A ⧸ Jm), c • x = Ideal.Quotient.mk Jm c * x := by
    intro c x
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
  have hsmulmk : ∀ c u : A,
      c • (Ideal.Quotient.mk Jm u) = Ideal.Quotient.mk Jm (c * u) := by
    intro c u
    rw [hsmulg, ← map_mul]
  have hρ0 : ∀ a ∈ Jm, (Ideal.Quotient.mkₐ A J) a = 0 := by
    intro a ha
    show Ideal.Quotient.mk J a = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hJmle ha)
  let ρA : (A ⧸ Jm) →ₐ[A] (A ⧸ J) :=
    Ideal.Quotient.liftₐ Jm (Ideal.Quotient.mkₐ A J) hρ0
  let ρ : (A ⧸ Jm) →ₐ[k] (A ⧸ J) := ρA.restrictScalars k
  have hρmkA : ∀ a : A, ρA (Ideal.Quotient.mk Jm a) = Ideal.Quotient.mk J a := fun _ => rfl
  have hρmk : ∀ a : A, ρ (Ideal.Quotient.mk Jm a) = Ideal.Quotient.mk J a := fun _ => rfl
  have hρsurj : Function.Surjective ρ := by
    intro c
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    exact ⟨Ideal.Quotient.mk Jm a, hρmk a⟩
  have hker2 : RingHom.ker (ρ : (A ⧸ Jm) →+* (A ⧸ J)) ^ 2 = ⊥ := by
    rw [pow_two]
    refine le_antisymm (Ideal.mul_le.mpr ?_) bot_le
    intro u hu v hv
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective u
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective v
    have ha : a ∈ J := by
      have h1 : Ideal.Quotient.mk J a = 0 := by
        rw [← hρmk a]
        exact RingHom.mem_ker.mp hu
      exact Ideal.Quotient.eq_zero_iff_mem.mp h1
    have hb : b ∈ J := by
      have h1 : Ideal.Quotient.mk J b = 0 := by
        rw [← hρmk b]
        exact RingHom.mem_ker.mp hv
      exact Ideal.Quotient.eq_zero_iff_mem.mp h1
    refine (Submodule.mem_bot _).mpr ?_
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact hmulJ a (hJmax ha) b hb
  have hprod : ∀ u v : A ⧸ Jm, ρA u = 0 → ρA v = 0 → u * v = 0 := by
    intro u v hu hv
    have hmem : u * v ∈ RingHom.ker (ρ : (A ⧸ Jm) →+* (A ⧸ J)) ^ 2 := by
      rw [pow_two]
      exact Ideal.mul_mem_mul (RingHom.mem_ker.mpr hu) (RingHom.mem_ker.mpr hv)
    rw [hker2] at hmem
    simpa using hmem
  obtain ⟨σ, hσ⟩ : ∃ σ : (A ⧸ J) →ₐ[k] (A ⧸ Jm), ∀ c, ρ (σ c) = c := by
    refine ⟨Algebra.FormallySmooth.liftOfSurjective
      (AlgHom.id k (A ⧸ J)) ρ hρsurj ⟨2, hker2⟩, fun c => ?_⟩
    have h := Algebra.FormallySmooth.comp_liftOfSurjective
      (AlgHom.id k (A ⧸ J)) ρ hρsurj ⟨2, hker2⟩
    have h2 := DFunLike.congr_fun h c
    simpa using h2
  have hρσ : ∀ c : A ⧸ J, ρA (σ c) = c := fun c => hσ c
  have hkerel : ∀ a : A,
      ρA (Ideal.Quotient.mk Jm a - σ (Ideal.Quotient.mk J a)) = 0 := by
    intro a
    rw [map_sub, hρmkA a, hρσ (Ideal.Quotient.mk J a), sub_self]
  have hmkJmsmul : ∀ (c : k) (a : A),
      Ideal.Quotient.mk Jm (c • a) = c • Ideal.Quotient.mk Jm a := by
    intro c a
    rw [Algebra.smul_def, map_mul, Algebra.smul_def, ← Ideal.Quotient.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply k A (A ⧸ Jm)]
  have hmkJsmul : ∀ (c : k) (a : A),
      Ideal.Quotient.mk J (c • a) = c • Ideal.Quotient.mk J a := by
    intro c a
    rw [Algebra.smul_def, map_mul, Algebra.smul_def, ← Ideal.Quotient.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply k A (A ⧸ J)]
  have hadd : ∀ a b : A,
      Ideal.Quotient.mk Jm (a + b) - σ (Ideal.Quotient.mk J (a + b))
        = (Ideal.Quotient.mk Jm a - σ (Ideal.Quotient.mk J a))
          + (Ideal.Quotient.mk Jm b - σ (Ideal.Quotient.mk J b)) := by
    intro a b
    simp only [map_add]
    ring
  have hsmulk : ∀ (c : k) (a : A),
      Ideal.Quotient.mk Jm (c • a) - σ (Ideal.Quotient.mk J (c • a))
        = (RingHom.id k) c • (Ideal.Quotient.mk Jm a - σ (Ideal.Quotient.mk J a)) := by
    intro c a
    show Ideal.Quotient.mk Jm (c • a) - σ (Ideal.Quotient.mk J (c • a))
      = c • (Ideal.Quotient.mk Jm a - σ (Ideal.Quotient.mk J a))
    rw [hmkJmsmul c a, hmkJsmul c a, map_smul, smul_sub]
  have hleib : ∀ a b : A,
      Ideal.Quotient.mk Jm (a * b) - σ (Ideal.Quotient.mk J (a * b))
        = a • (Ideal.Quotient.mk Jm b - σ (Ideal.Quotient.mk J b))
          + b • (Ideal.Quotient.mk Jm a - σ (Ideal.Quotient.mk J a)) := by
    intro a b
    have hz2 := hprod (Ideal.Quotient.mk Jm a - σ (Ideal.Quotient.mk J a))
      (Ideal.Quotient.mk Jm b - σ (Ideal.Quotient.mk J b)) (hkerel a) (hkerel b)
    rw [hsmulg a, hsmulg b]
    simp only [map_mul]
    linear_combination -hz2
  obtain ⟨Dder, hDapp⟩ : ∃ D : Derivation k A (A ⧸ Jm),
      ∀ a : A, D a = Ideal.Quotient.mk Jm a - σ (Ideal.Quotient.mk J a) :=
    ⟨Derivation.mk'
      { toFun := fun a => Ideal.Quotient.mk Jm a - σ (Ideal.Quotient.mk J a)
        map_add' := hadd
        map_smul' := hsmulk } hleib, fun _ => rfl⟩
  have hderivLift : ∀ a : A,
      Dder.liftKaehlerDifferential (KaehlerDifferential.D k A a) = Dder a := by
    intro a
    simp [Derivation.liftKaehlerDifferential_comp_D]
  have hcomp : ∀ ω : KaehlerDifferential k A,
      ρA (Dder.liftKaehlerDifferential ω) = 0 := by
    have hker : (⊤ : Submodule A (KaehlerDifferential k A)) ≤
        LinearMap.ker (ρA.toLinearMap.comp Dder.liftKaehlerDifferential) := by
      rw [← KaehlerDifferential.span_range_derivation, Submodule.span_le]
      rintro y ⟨a, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.comp_apply]
      show ρA (Dder.liftKaehlerDifferential (KaehlerDifferential.D k A a)) = 0
      rw [hderivLift a, hDapp a]
      exact hkerel a
    intro ω
    have h2 := hker (Submodule.mem_top : ω ∈ ⊤)
    rw [LinearMap.mem_ker, LinearMap.comp_apply] at h2
    exact h2
  have hcoef : ∀ i : n,
      bb.repr (KaehlerDifferential.D k A z) i ∈ IsLocalRing.maximalIdeal A :=
    fun i => repr_mem_maximalIdeal_of_tmul_eq_zero bb (KaehlerDifferential.D k A z) h0 i
  have hLb : ∀ i : n, ∃ u : A, u ∈ J ∧
      Dder.liftKaehlerDifferential (bb i) = Ideal.Quotient.mk Jm u := by
    intro i
    obtain ⟨u, hu⟩ := Ideal.Quotient.mk_surjective (Dder.liftKaehlerDifferential (bb i))
    refine ⟨u, ?_, hu.symm⟩
    have h1 : ρA (Ideal.Quotient.mk Jm u) = 0 := by
      rw [hu]
      exact hcomp (bb i)
    rw [hρmkA u] at h1
    exact Ideal.Quotient.eq_zero_iff_mem.mp h1
  have hsum : Dder.liftKaehlerDifferential (KaehlerDifferential.D k A z) = 0 := by
    conv_lhs => rw [← bb.sum_repr (KaehlerDifferential.D k A z)]
    rw [map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    obtain ⟨u, huJ, hu⟩ := hLb i
    rw [map_smul, hu, hsmulmk, Ideal.Quotient.eq_zero_iff_mem]
    exact hmulJ _ (hcoef i) u huJ
  have hzval : Ideal.Quotient.mk Jm z
      = Dder.liftKaehlerDifferential (KaehlerDifferential.D k A z) := by
    rw [hderivLift z, hDapp z, Ideal.Quotient.eq_zero_iff_mem.mpr hz, map_zero, sub_zero]
  have hfinal : Ideal.Quotient.mk Jm z = 0 := by
    rw [hzval, hsum]
  rw [← hJmdef]
  exact Ideal.Quotient.eq_zero_iff_mem.mp hfinal
private theorem ideal_eq_span_of_tmul_D_mem_span (k : Type*) [CommRing k] (A : Type*) [CommRing A]
    [Algebra k A] [IsLocalRing A] {n : Type*} [Fintype n]
    (bb : Module.Basis n A (KaehlerDifferential k A))
    (J : Ideal A) (hJfg : J.FG)
    (hJmax : J ≤ IsLocalRing.maximalIdeal A) [Algebra.FormallySmooth k (A ⧸ J)] (r : ℕ)
    (x : Fin r → A) (hxJ : ∀ i : Fin r, x i ∈ J)
    (hspan : ∀ y ∈ J,
      (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A y ∈
        Submodule.span (IsLocalRing.ResidueField A)
          (Set.range fun i : Fin r =>
            (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (x i))) :
    J = Ideal.span (Set.range x) := by
  classical
  have hsmeq : (IsLocalRing.maximalIdeal A • J : Ideal A)
      = IsLocalRing.maximalIdeal A * J := by
    rw [Ideal.smul_eq_mul]
  refine le_antisymm ?_ ?_
  · have hstep : J ≤ Ideal.span (Set.range x) ⊔ IsLocalRing.maximalIdeal A • J := by
      rw [hsmeq]
      intro y hy
      have hy' := hspan y hy
      rw [Submodule.mem_span_range_iff_exists_fun] at hy'
      obtain ⟨c, hc⟩ := hy'
      obtain ⟨c', hc'⟩ : ∃ c' : Fin r → A, ∀ i, IsLocalRing.residue A (c' i) = c i := by
        have hsurj : Function.Surjective (IsLocalRing.residue A) :=
          Ideal.Quotient.mk_surjective
        choose c' hc' using fun i => hsurj (c i)
        exact ⟨c', hc'⟩
      have hsum : (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
          KaehlerDifferential.D k A (∑ i, c' i * x i)
          = ∑ i, c i • ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
            KaehlerDifferential.D k A (x i)) := by
        rw [map_sum, TensorProduct.tmul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_comm (c' i) (x i),
          KaehlerDifferential.residue_tmul_D_mul_of_mem_maximalIdeal, hc' i]
        exact hJmax (hxJ i)
      have h0 : (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
          KaehlerDifferential.D k A (y - ∑ i, c' i * x i) = 0 := by
        rw [map_sub, TensorProduct.tmul_sub, hsum, hc, sub_self]
      have hmemJ : y - ∑ i, c' i * x i ∈ J :=
        Submodule.sub_mem _ hy
          (Submodule.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hxJ i))
      have hsq := mem_maximalIdeal_mul_of_tmul_D_eq_zero k A bb J hJmax _ hmemJ h0
      have hrw : y = (y - ∑ i, c' i * x i) + ∑ i, c' i * x i := by ring
      rw [hrw]
      refine Submodule.add_mem _ (Submodule.mem_sup_right hsq) (Submodule.mem_sup_left ?_)
      exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
    have hbotne : (⊥ : Ideal A) ≠ ⊤ := by
      intro hcon
      have hmem1 : (1 : A) ∈ (⊥ : Ideal A) := by
        rw [hcon]; exact Submodule.mem_top
      have hz : (1 : A) = 0 := by simp at hmem1
      exact one_ne_zero hz
    exact Submodule.le_of_le_smul_of_le_jacobson_bot hJfg
      (IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal A) hbotne).ge hstep
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hxJ i
private theorem map_eq_of_map_eq_of_away_mul {S : Type*} [CommRing S] {T₁ T₂ : Type*}
    [CommRing T₁] [CommRing T₂] [Algebra S T₁] [Algebra S T₂] (g₁ d : S)
    [IsLocalization (Submonoid.powers g₁) T₁]
    [IsLocalization (Submonoid.powers (g₁ * d)) T₂] (I J : Ideal S)
    (h : Ideal.map (algebraMap S T₁) I = Ideal.map (algebraMap S T₁) J) :
    Ideal.map (algebraMap S T₂) I = Ideal.map (algebraMap S T₂) J := by
  have hgu : IsUnit (algebraMap S T₂ (g₁ * d)) :=
    IsLocalization.map_units (M := Submonoid.powers (g₁ * d)) T₂
      ⟨g₁ * d, Submonoid.mem_powers _⟩
  rw [map_mul] at hgu
  have hg1u : IsUnit (algebraMap S T₂ g₁) := isUnit_of_mul_isUnit_left hgu
  have hFu : ∀ y : Submonoid.powers g₁, IsUnit (algebraMap S T₂ (y : S)) := by
    rintro ⟨y, m, rfl⟩
    show IsUnit (algebraMap S T₂ (g₁ ^ m))
    rw [map_pow]
    exact hg1u.pow m
  obtain ⟨F, hF⟩ : ∃ F : T₁ →+* T₂, F.comp (algebraMap S T₁) = algebraMap S T₂ :=
    ⟨IsLocalization.lift (M := Submonoid.powers g₁) (S := T₁) hFu,
      RingHom.ext fun x => IsLocalization.lift_eq hFu x⟩
  calc Ideal.map (algebraMap S T₂) I
      = Ideal.map F (Ideal.map (algebraMap S T₁) I) := by rw [Ideal.map_map, hF]
    _ = Ideal.map F (Ideal.map (algebraMap S T₁) J) := by rw [h]
    _ = Ideal.map (algebraMap S T₂) J := by rw [Ideal.map_map, hF]
end
section
variable (k : Type*) [CommRing k] (ι : Type*) [Fintype ι] [DecidableEq ι]
  (S : Type*) [CommRing S] [Algebra k S] [Algebra (MvPolynomial ι k) S]
  [IsScalarTower k (MvPolynomial ι k) S] [Algebra.FormallyEtale (MvPolynomial ι k) S]
  [IsNoetherianRing S] (I q : Ideal S) [q.IsPrime]
end
end EtaleCoordinates
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
open scoped TensorProduct
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.EtaleCoordinates
variable (k : Type*) [CommRing k] (ι : Type*) [Fintype ι] [DecidableEq ι]
  (S : Type*) [CommRing S] [Algebra k S] [Algebra (MvPolynomial ι k) S]
  [IsScalarTower k (MvPolynomial ι k) S] [Algebra.FormallyEtale (MvPolynomial ι k) S]
  [IsNoetherianRing S] (I q : Ideal S) [q.IsPrime]
namespace FunctorialResolution.EmbeddedResolution.EtaleCoordinates
theorem _root_.solution
    (A : Type*) [CommRing A] [Algebra S A] [Algebra k A] [IsScalarTower k S A]
    [IsLocalization q.primeCompl A] [IsLocalRing A] [IsNoetherianRing A]
    [Algebra.FormallySmooth k (A ⧸ Ideal.map (algebraMap S A) I)]
    (hIq : I ≤ q) :
    ∃ (g : S) (w : ι → S) (T : Finset ι),
      g ∉ q ∧
      (∀ j ∈ T, w j ∈ I) ∧
      Ideal.map (algebraMap S (Localization.Away g)) (Ideal.span (w '' (↑T : Set ι))) =
        Ideal.map (algebraMap S (Localization.Away g)) I ∧
      (∀ j ∉ T, ∃ i : ι, w j = coord k ι S i) ∧
      IsUnit (algebraMap S (Localization.Away g)
        ((basisKaehler k ι S).det fun i : ι => KaehlerDifferential.D k S (w i))) := by
  classical
  have instFEloc : Algebra.FormallyEtale S A :=
    Algebra.FormallyEtale.of_isLocalization (M := q.primeCompl)
  let instPA : Algebra (MvPolynomial ι k) A :=
    ((algebraMap S A).comp (algebraMap (MvPolynomial ι k) S)).toAlgebra
  have instT1 : IsScalarTower (MvPolynomial ι k) S A :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have t2Space_cuspAdeles : IsScalarTower k (MvPolynomial ι k) A :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply k S A x,
        IsScalarTower.algebraMap_apply k (MvPolynomial ι k) S x]
      rfl
  have instFEPA : Algebra.FormallyEtale (MvPolynomial ι k) A :=
    Algebra.FormallyEtale.comp (MvPolynomial ι k) S A
  have hmapq : Ideal.map (algebraMap S A) q = IsLocalRing.maximalIdeal A :=
    IsLocalization.AtPrime.map_eq_maximalIdeal q A
  have hJAm : Ideal.map (algebraMap S A) I ≤ IsLocalRing.maximalIdeal A := by
    rw [← hmapq]
    exact Ideal.map_mono hIq
  obtain ⟨tF, htF⟩ : I.FG := IsNoetherian.noetherian I
  have hspanI : Ideal.span (↑(tF.image (algebraMap S A)) : Set A)
      = Ideal.map (algebraMap S A) I := by
    rw [Finset.coe_image, ← htF, Ideal.map_span]
  obtain ⟨bset, hbsub, hbspan, hbind⟩ :=
    exists_linearIndependent (K := IsLocalRing.ResidueField A)
      (t := ((fun a : A => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
        KaehlerDifferential.D k A a) '' (↑(tF.image (algebraMap S A)) : Set A)))
  have hbfin : bset.Finite :=
    Set.Finite.subset (Set.Finite.image _ (Finset.finite_toSet _)) hbsub
  let _ : Fintype bset := hbfin.fintype
  choose pre hpre1 hpre2 using fun v : bset => hbsub v.2
  have hpre1' : ∀ v : bset, ∃ t : S, t ∈ tF ∧ algebraMap S A t = pre v := by
    intro v
    have hv := hpre1 v
    rw [Finset.mem_coe, Finset.mem_image] at hv
    obtain ⟨t, ht, hts⟩ := hv
    exact ⟨t, ht, hts⟩
  choose pres hpres1 hpres2 using hpre1'
  obtain ⟨s, hs⟩ : ∃ s : Fin (Fintype.card bset) → S,
      ∀ i, s i = pres ((Fintype.equivFin bset).symm i) := ⟨_, fun _ => rfl⟩
  have hsI : ∀ i, s i ∈ I := by
    intro i
    rw [hs i, ← htF]
    exact Submodule.subset_span (Finset.mem_coe.mpr (hpres1 _))
  have hfun : (fun i : Fin (Fintype.card bset) => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
      KaehlerDifferential.D k A (algebraMap S A (s i)))
      = fun i : Fin (Fintype.card bset) =>
        (((Fintype.equivFin bset).symm i : bset) :
          IsLocalRing.ResidueField A ⊗[A] KaehlerDifferential k A) := by
    funext i
    rw [hs i, hpres2]
    exact hpre2 _
  have hind : LinearIndependent (IsLocalRing.ResidueField A)
      (fun i : Fin (Fintype.card bset) => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
        KaehlerDifferential.D k A (algebraMap S A (s i))) := by
    rw [hfun]
    exact hbind.comp _ (Fintype.equivFin bset).symm.injective
  have hrange : Set.range (fun i : Fin (Fintype.card bset) =>
      (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
        KaehlerDifferential.D k A (algebraMap S A (s i))) = bset := by
    rw [hfun]
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      exact ((Fintype.equivFin bset).symm i).2
    · intro hv
      exact ⟨(Fintype.equivFin bset) ⟨v, hv⟩, by simp⟩
  have hxJ : ∀ i, algebraMap S A (s i) ∈ Ideal.map (algebraMap S A) I := fun i =>
    Ideal.mem_map_of_mem _ (hsI i)
  have hgen : ∀ y ∈ Ideal.map (algebraMap S A) I,
      (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A y ∈
        Submodule.span (IsLocalRing.ResidueField A)
          ((fun a : A => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
            KaehlerDifferential.D k A a) '' (↑(tF.image (algebraMap S A)) : Set A)) := by
    intro y hy
    rw [← hspanI] at hy
    obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.mp hy
    rw [← hf, map_sum, TensorProduct.tmul_sum]
    refine Submodule.sum_mem _ fun a ha => ?_
    have ham : a ∈ IsLocalRing.maximalIdeal A := by
      refine hJAm ?_
      rw [← hspanI]
      exact Submodule.subset_span (Finset.mem_coe.mpr ha)
    have heq : (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (f a • a)
        = IsLocalRing.residue A (f a) •
          ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A a) := by
      rw [smul_eq_mul, mul_comm,
        KaehlerDifferential.residue_tmul_D_mul_of_mem_maximalIdeal]
      exact ham
    rw [heq]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨a, Finset.mem_coe.mpr ha, rfl⟩)
  have hspanx : ∀ y ∈ Ideal.map (algebraMap S A) I,
      (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A y ∈
        Submodule.span (IsLocalRing.ResidueField A)
          (Set.range fun i : Fin (Fintype.card bset) =>
            (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
              KaehlerDifferential.D k A (algebraMap S A (s i))) := by
    intro y hy
    rw [hrange, hbspan]
    exact hgen y hy
  have hJAeq : Ideal.map (algebraMap S A) I
      = Ideal.span (Set.range fun i : Fin (Fintype.card bset) => algebraMap S A (s i)) :=
    ideal_eq_span_of_tmul_D_mem_span k A (basisKaehler k ι A) (Ideal.map (algebraMap S A) I)
      (IsNoetherian.noetherian _) hJAm
      (Fintype.card bset) (fun i => algebraMap S A (s i)) hxJ hspanx
  obtain ⟨bkk, hbk⟩ : ∃ bkk : Module.Basis ι (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField A ⊗[A] KaehlerDifferential k A),
      ∀ i, bkk i = (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (basisKaehler k ι A i) :=
    ⟨Algebra.TensorProduct.basis (IsLocalRing.ResidueField A) (basisKaehler k ι A),
      fun i => by simp⟩
  obtain ⟨Jst, B, hbasisInl, hbasisInr⟩ := exists_basis_sum_of_linearIndependent bkk (Fintype.card bset)
    (fun i : Fin (Fintype.card bset) => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
      KaehlerDifferential.D k A (algebraMap S A (s i))) hind
  have hcard1 : Module.finrank (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField A ⊗[A] KaehlerDifferential k A)
      = Fintype.card (Fin (Fintype.card bset) ⊕ {j : ι // j ∈ Jst}) :=
    Module.finrank_eq_card_basis B
  have hcard2 : Module.finrank (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField A ⊗[A] KaehlerDifferential k A) = Fintype.card ι :=
    Module.finrank_eq_card_basis bkk
  have hcard3 : Fintype.card {j : ι // j ∈ Jst} + Fintype.card {j : ι // ¬ (j ∈ Jst)}
      = Fintype.card ι := by
    rw [← Fintype.card_sum]
    exact Fintype.card_congr (Equiv.sumCompl (fun j : ι => j ∈ Jst))
  rw [Fintype.card_sum, Fintype.card_fin] at hcard1
  have hcard4 : Fintype.card {j : ι // ¬ (j ∈ Jst)} = Fintype.card bset := by omega
  have e : {j : ι // ¬ (j ∈ Jst)} ≃ Fin (Fintype.card bset) := Fintype.equivFinOfCardEq hcard4
  obtain ⟨τ, hτl, hτr⟩ : ∃ τ : Fin (Fintype.card bset) ⊕ {j : ι // j ∈ Jst} ≃ ι,
      (∀ l : Fin (Fintype.card bset), τ (Sum.inl l) = ((e.symm l : ι))) ∧
      (∀ j : {j : ι // j ∈ Jst}, τ (Sum.inr j) = (j : ι)) :=
    ⟨(Equiv.sumCongr e.symm (Equiv.refl {j : ι // j ∈ Jst})).trans
      ((Equiv.sumComm _ _).trans (Equiv.sumCompl (fun j : ι => j ∈ Jst))),
      fun l => rfl, fun j => rfl⟩
  obtain ⟨w, hwJ, hwn⟩ : ∃ w : ι → S, (∀ j, j ∈ Jst → w j = coord k ι S j) ∧
      (∀ x : {j : ι // ¬ (j ∈ Jst)}, w (x : ι) = s (e x)) := by
    refine ⟨fun j => if hj : j ∈ Jst then coord k ι S j else s (e ⟨j, hj⟩),
      fun j hj => ?_, fun x => ?_⟩
    · exact dif_pos hj
    · exact dif_neg x.2
  have hbasisApply : ∀ x : Fin (Fintype.card bset) ⊕ {j : ι // j ∈ Jst},
      B x = (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
        KaehlerDifferential.D k A (algebraMap S A (w (τ x))) := by
    rintro (l | j)
    · rw [hbasisInl l, hτl l, hwn (e.symm l), Equiv.apply_symm_apply]
    · rw [hbasisInr j, hτr j, hwJ (j : ι) j.2, hbk (j : ι), basisKaehler_apply,
        algebraMap_coord]
  have hB'G : ∀ i : ι, (B.reindex τ) i = (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
      KaehlerDifferential.D k A (algebraMap S A (w i)) := by
    intro i
    rw [Module.Basis.reindex_apply, hbasisApply (τ.symm i), Equiv.apply_symm_apply]
  have hdetne := residue_det_ne_zero_of_tmul_eq_basis (basisKaehler k ι A)
    (fun i : ι => KaehlerDifferential.D k A (algebraMap S A (w i))) (B.reindex τ) hB'G
  have hdetA : algebraMap S A ((basisKaehler k ι S).det
      (fun i : ι => KaehlerDifferential.D k S (w i)))
      = (basisKaehler k ι A).det
        (fun i : ι => KaehlerDifferential.D k A (algebraMap S A (w i))) :=
    algebraMap_det_basisKaehler k ι S A w
  have hg₀q : ((basisKaehler k ι S).det fun i : ι => KaehlerDifferential.D k S (w i)) ∉ q := by
    intro hgq
    apply hdetne
    rw [← hdetA, IsLocalRing.residue_eq_zero_iff, ← hmapq]
    exact Ideal.mem_map_of_mem _ hgq
  have hspanA : Ideal.map (algebraMap S A) (Ideal.span (w '' (↑(Jstᶜ) : Set ι)))
      = Ideal.map (algebraMap S A) I := by
    rw [Ideal.map_span, hJAeq]
    congr 1
    ext v
    constructor
    · rintro ⟨u, ⟨j, hj, rfl⟩, rfl⟩
      have hj' : ¬ (j ∈ Jst) := Finset.mem_compl.mp (Finset.mem_coe.mp hj)
      have hwj : w j = s (e ⟨j, hj'⟩) := hwn ⟨j, hj'⟩
      exact ⟨e ⟨j, hj'⟩, by rw [hwj]⟩
    · rintro ⟨i, rfl⟩
      refine ⟨w ((e.symm i : ι)), ⟨(e.symm i : ι), ?_, rfl⟩, ?_⟩
      · exact Finset.mem_coe.mpr (Finset.mem_compl.mpr (e.symm i).2)
      · have hwj : w ((e.symm i : ι)) = s (e (e.symm i)) := hwn (e.symm i)
        rw [hwj, Equiv.apply_symm_apply]
  obtain ⟨g₁, hg₁q, hg₁eq⟩ := exists_away_map_ideal_eq q A
    (Ideal.span (w '' (↑(Jstᶜ) : Set ι))) I
    (Submodule.fg_span (Set.Finite.image w (Finset.finite_toSet _)))
    (IsNoetherian.noetherian I) hspanA
  refine ⟨g₁ * ((basisKaehler k ι S).det fun i : ι => KaehlerDifferential.D k S (w i)), w,
    Jstᶜ, ?_, ?_, ?_, ?_, ?_⟩
  · intro hmem
    rcases Ideal.IsPrime.mem_or_mem ‹q.IsPrime› hmem with h1 | h2
    · exact hg₁q h1
    · exact hg₀q h2
  · intro j hj
    have hj' : ¬ (j ∈ Jst) := Finset.mem_compl.mp hj
    have hwj : w j = s (e ⟨j, hj'⟩) := hwn ⟨j, hj'⟩
    rw [hwj]
    exact hsI _
  · exact map_eq_of_map_eq_of_away_mul g₁
      ((basisKaehler k ι S).det fun i : ι => KaehlerDifferential.D k S (w i)) _ _ hg₁eq
  · intro j hj
    have hj' : j ∈ Jst := by
      by_contra hc
      exact hj (Finset.mem_compl.mpr hc)
    exact ⟨j, hwJ j hj'⟩
  · have hu : IsUnit (algebraMap S
        (Localization.Away (g₁ *
          ((basisKaehler k ι S).det fun i : ι => KaehlerDifferential.D k S (w i))))
        (g₁ * ((basisKaehler k ι S).det fun i : ι => KaehlerDifferential.D k S (w i)))) :=
      IsLocalization.map_units _ ⟨_, Submonoid.mem_powers _⟩
    rw [map_mul] at hu
    exact isUnit_of_mul_isUnit_right hu
end FunctorialResolution.EmbeddedResolution.EtaleCoordinates
