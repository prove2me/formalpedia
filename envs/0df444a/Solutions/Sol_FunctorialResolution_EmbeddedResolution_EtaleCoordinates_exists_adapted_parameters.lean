-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.EtaleCoordinates.exists_adapted_parameters
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:15:24.608613+00:00
-- url     : https://prove2.me/submissions/59292aa3-b945-4d63-8fa4-df242a861f5e

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_FormallyEtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_JacobianCriterion
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_SpanSingletonProduct
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_AdaptedParameters
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_algebraMap_coord
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_algebraMap_det_basisKaehler
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_basisDerivation_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_exists_basis_sum_of_linearIndependent
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_exists_generators_maximalIdeal_of_linearIndependent_D
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
private theorem exists_section_mod_maximalIdeal_sq (k : Type*) [CommRing k] (A : Type*)
    [CommRing A] [Algebra k A] [IsLocalRing A] [Algebra k (IsLocalRing.ResidueField A)]
    [IsScalarTower k A (IsLocalRing.ResidueField A)]
    [Algebra.FormallySmooth k (IsLocalRing.ResidueField A)] :
    ∃ w : A → A,
      (∀ a : A, a - w a ∈ IsLocalRing.maximalIdeal A) ∧
      (∀ a b : A, w a + w b - w (a + b) ∈ IsLocalRing.maximalIdeal A ^ 2) ∧
      (∀ (c : k) (a : A), c • w a - w (c • a) ∈ IsLocalRing.maximalIdeal A ^ 2) ∧
      (∀ a b : A, w a * w b - w (a * b) ∈ IsLocalRing.maximalIdeal A ^ 2) ∧
      (∀ a : A, a ∈ IsLocalRing.maximalIdeal A → w a ∈ IsLocalRing.maximalIdeal A ^ 2) := by
  classical
  have hsq : ∀ a ∈ IsLocalRing.maximalIdeal A ^ 2,
      (IsScalarTower.toAlgHom k A (IsLocalRing.ResidueField A)) a = 0 := by
    intro a ha
    show algebraMap A (IsLocalRing.ResidueField A) a = 0
    rw [IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.residue_eq_zero_iff]
    exact Ideal.pow_le_self (by norm_num) ha
  obtain ⟨ρ, hρmk⟩ : ∃ ρ : (A ⧸ IsLocalRing.maximalIdeal A ^ 2) →ₐ[k]
      IsLocalRing.ResidueField A,
      ∀ a : A, ρ (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ 2) a)
        = IsLocalRing.residue A a := by
    refine ⟨Ideal.Quotient.liftₐ (IsLocalRing.maximalIdeal A ^ 2)
      (IsScalarTower.toAlgHom k A (IsLocalRing.ResidueField A)) hsq, fun a => ?_⟩
    show algebraMap A (IsLocalRing.ResidueField A) a = IsLocalRing.residue A a
    rw [IsLocalRing.ResidueField.algebraMap_eq]
  have hρsurj : Function.Surjective ρ := by
    intro c
    obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (R := A) c
    exact ⟨Ideal.Quotient.mk _ a, by rw [hρmk a]; exact ha⟩
  have hker2 : RingHom.ker (ρ : (A ⧸ IsLocalRing.maximalIdeal A ^ 2) →+*
      IsLocalRing.ResidueField A) ^ 2 = ⊥ := by
    have hexp : RingHom.ker (ρ : (A ⧸ IsLocalRing.maximalIdeal A ^ 2) →+*
        IsLocalRing.ResidueField A) ^ 2
        = RingHom.ker (ρ : (A ⧸ IsLocalRing.maximalIdeal A ^ 2) →+*
            IsLocalRing.ResidueField A)
          * RingHom.ker (ρ : (A ⧸ IsLocalRing.maximalIdeal A ^ 2) →+*
            IsLocalRing.ResidueField A) := pow_two _
    rw [hexp]
    refine le_antisymm ?_ bot_le
    rw [Ideal.mul_le]
    intro u hu v hv
    have hu' : ρ u = 0 := RingHom.mem_ker.mp hu
    have hv' : ρ v = 0 := RingHom.mem_ker.mp hv
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective u
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective v
    have ha : a ∈ IsLocalRing.maximalIdeal A := by
      rw [← IsLocalRing.residue_eq_zero_iff, ← hρmk a]
      exact hu'
    have hb : b ∈ IsLocalRing.maximalIdeal A := by
      rw [← IsLocalRing.residue_eq_zero_iff, ← hρmk b]
      exact hv'
    refine (Submodule.mem_bot _).mpr ?_
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, pow_two]
    exact Ideal.mul_mem_mul ha hb
  obtain ⟨σ, hσ⟩ : ∃ σ : IsLocalRing.ResidueField A →ₐ[k]
      (A ⧸ IsLocalRing.maximalIdeal A ^ 2), ∀ c, ρ (σ c) = c := by
    refine ⟨Algebra.FormallySmooth.liftOfSurjective
      (AlgHom.id k (IsLocalRing.ResidueField A)) ρ hρsurj ⟨2, hker2⟩, fun c => ?_⟩
    have h := Algebra.FormallySmooth.comp_liftOfSurjective
      (AlgHom.id k (IsLocalRing.ResidueField A)) ρ hρsurj ⟨2, hker2⟩
    have h2 := DFunLike.congr_fun h c
    simpa using h2
  obtain ⟨w, hw⟩ : ∃ w : A → A, ∀ a : A,
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ 2) (w a)
        = σ (IsLocalRing.residue A a) := by
    refine ⟨fun a => Function.surjInv Ideal.Quotient.mk_surjective
      (σ (IsLocalRing.residue A a)), fun a => ?_⟩
    exact Function.surjInv_eq Ideal.Quotient.mk_surjective _
  refine ⟨w, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero, ← hρmk (w a), hw a,
      hσ (IsLocalRing.residue A a)]
  · intro a b
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_add, hw a, hw b, hw (a + b), map_add,
      map_add, sub_self]
  · intro c a
    have hres : IsLocalRing.residue A (c • a) = c • IsLocalRing.residue A a := by
      rw [Algebra.smul_def, map_mul, Algebra.smul_def,
        ← IsLocalRing.ResidueField.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply k A (IsLocalRing.ResidueField A)]
    have hmk : Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ 2) (c • w a)
        = c • Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ 2) (w a) := by
      rw [Algebra.smul_def, map_mul, Algebra.smul_def, ← Ideal.Quotient.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply k A (A ⧸ IsLocalRing.maximalIdeal A ^ 2)]
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hw (c • a), hmk, hres, map_smul, hw a,
      sub_self]
  · intro a b
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hw a, hw b, hw (a * b), map_mul,
      map_mul, sub_self]
  · intro a ha
    have hres : IsLocalRing.residue A a = 0 := by
      rw [IsLocalRing.residue_eq_zero_iff]
      exact ha
    rw [← Ideal.Quotient.eq_zero_iff_mem, hw a, hres, map_zero]
private theorem mem_maximalIdeal_sq_of_tmul_D_eq_zero (k : Type*) [CommRing k] (A : Type*)
    [CommRing A] [Algebra k A] [IsLocalRing A] [Algebra k (IsLocalRing.ResidueField A)]
    [IsScalarTower k A (IsLocalRing.ResidueField A)]
    [Algebra.FormallySmooth k (IsLocalRing.ResidueField A)]
    (x : A) (hx : x ∈ IsLocalRing.maximalIdeal A)
    (h0 : (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A x = 0) :
    x ∈ IsLocalRing.maximalIdeal A ^ 2 := by
  classical
  obtain ⟨w, h1, h2, h3, h4, h5⟩ := exists_section_mod_maximalIdeal_sq k A
  have hco : ∀ (a b : A) (ha : a ∈ IsLocalRing.maximalIdeal A)
      (hb : b ∈ IsLocalRing.maximalIdeal A),
      a - b ∈ IsLocalRing.maximalIdeal A ^ 2 →
      Ideal.toCotangent (IsLocalRing.maximalIdeal A) ⟨a, ha⟩
        = Ideal.toCotangent (IsLocalRing.maximalIdeal A) ⟨b, hb⟩ := by
    intro a b ha hb hab
    exact (Ideal.toCotangent_eq _).mpr hab
  have hadd : ∀ a b : A,
      Ideal.toCotangent (IsLocalRing.maximalIdeal A) ⟨a + b - w (a + b), h1 (a + b)⟩
        = Ideal.toCotangent (IsLocalRing.maximalIdeal A) ⟨a - w a, h1 a⟩
          + Ideal.toCotangent (IsLocalRing.maximalIdeal A) ⟨b - w b, h1 b⟩ := by
    intro a b
    rw [← map_add]
    refine hco _ _ _ _ ?_
    show a + b - w (a + b) - ((a - w a) + (b - w b)) ∈ IsLocalRing.maximalIdeal A ^ 2
    have heq : a + b - w (a + b) - ((a - w a) + (b - w b)) = w a + w b - w (a + b) := by ring
    rw [heq]
    exact h2 a b
  have hsmul : ∀ (c : k) (a : A),
      Ideal.toCotangent (IsLocalRing.maximalIdeal A) ⟨c • a - w (c • a), h1 (c • a)⟩
        = (RingHom.id k) c •
          Ideal.toCotangent (IsLocalRing.maximalIdeal A) ⟨a - w a, h1 a⟩ := by
    intro c a
    show Ideal.toCotangent (IsLocalRing.maximalIdeal A) ⟨c • a - w (c • a), h1 (c • a)⟩
      = c • Ideal.toCotangent (IsLocalRing.maximalIdeal A) ⟨a - w a, h1 a⟩
    rw [← algebraMap_smul A c
      (Ideal.toCotangent (IsLocalRing.maximalIdeal A) ⟨a - w a, h1 a⟩), ← map_smul]
    refine hco _ _ _ _ ?_
    show c • a - w (c • a) - (algebraMap k A c) • (a - w a)
      ∈ IsLocalRing.maximalIdeal A ^ 2
    have heq : c • a - w (c • a) - (algebraMap k A c) • (a - w a)
        = c • w a - w (c • a) := by
      rw [Algebra.smul_def c a, Algebra.smul_def c (w a), smul_eq_mul]
      ring
    rw [heq]
    exact h3 c a
  have hleib : ∀ a b : A,
      Ideal.toCotangent (IsLocalRing.maximalIdeal A) ⟨a * b - w (a * b), h1 (a * b)⟩
        = a • Ideal.toCotangent (IsLocalRing.maximalIdeal A) ⟨b - w b, h1 b⟩
          + b • Ideal.toCotangent (IsLocalRing.maximalIdeal A) ⟨a - w a, h1 a⟩ := by
    intro a b
    rw [← map_smul, ← map_smul, ← map_add]
    refine hco _ _ _ _ ?_
    show a * b - w (a * b) - (a • (b - w b) + b • (a - w a))
      ∈ IsLocalRing.maximalIdeal A ^ 2
    have heq : a * b - w (a * b) - (a • (b - w b) + b • (a - w a))
        = -((a - w a) * (b - w b)) + (w a * w b - w (a * b)) := by
      simp only [smul_eq_mul]
      ring
    rw [heq]
    refine Submodule.add_mem _ (neg_mem ?_) (h4 a b)
    rw [pow_two]
    exact Ideal.mul_mem_mul (h1 a) (h1 b)
  obtain ⟨Dder, hDderapp⟩ : ∃ D : Derivation k A (IsLocalRing.maximalIdeal A).Cotangent,
      ∀ a : A, D a = Ideal.toCotangent (IsLocalRing.maximalIdeal A) ⟨a - w a, h1 a⟩ :=
    ⟨Derivation.mk'
      { toFun := fun a => Ideal.toCotangent (IsLocalRing.maximalIdeal A) ⟨a - w a, h1 a⟩
        map_add' := hadd
        map_smul' := hsmul } hleib, fun a => rfl⟩
  have hDx : Dder x = Ideal.toCotangent (IsLocalRing.maximalIdeal A) ⟨x, hx⟩ := by
    rw [hDderapp x]
    refine hco _ _ _ _ ?_
    show x - w x - x ∈ IsLocalRing.maximalIdeal A ^ 2
    have heq : x - w x - x = -(w x) := by ring
    rw [heq]
    exact neg_mem (h5 x hx)
  let instModKappa : Module (IsLocalRing.ResidueField A)
      (IsLocalRing.maximalIdeal A).Cotangent :=
    inferInstanceAs (Module (A ⧸ IsLocalRing.maximalIdeal A) _)
  let instTowerKappa : IsScalarTower A (IsLocalRing.ResidueField A)
      (IsLocalRing.maximalIdeal A).Cotangent :=
    inferInstanceAs (IsScalarTower A (A ⧸ IsLocalRing.maximalIdeal A) _)
  have hlin := congrArg (fun z => (Dder.liftKaehlerDifferential.liftBaseChange
    (IsLocalRing.ResidueField A)) z) h0
  have hDx0 : Dder x = 0 := by
    simpa [LinearMap.liftBaseChange_tmul, Derivation.liftKaehlerDifferential_comp_D] using hlin
  have hz : Ideal.toCotangent (IsLocalRing.maximalIdeal A) ⟨x, hx⟩ = 0 := by
    rw [← hDx]
    exact hDx0
  exact (Ideal.toCotangent_eq_zero _ ⟨x, hx⟩).mp hz
private theorem exists_fun_sum_smul_eq_of_mem_span {K M : Type*} [CommRing K] [AddCommGroup M]
    [Module K M] {n : ℕ} (v : Fin n → M) {x : M}
    (hx : x ∈ Submodule.span K (Set.range v)) :
    ∃ c : Fin n → K, ∑ i, c i • v i = x := by
  classical
  let P : Submodule K M :=
    { carrier := {y : M | ∃ c : Fin n → K, ∑ i, c i • v i = y}
      zero_mem' := ⟨0, by simp⟩
      add_mem' := by
        intro a b ha hb
        obtain ⟨ca, hca⟩ := ha
        obtain ⟨cb, hcb⟩ := hb
        refine ⟨ca + cb, ?_⟩
        rw [← hca, ← hcb, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Pi.add_apply, add_smul]
      smul_mem' := by
        intro r a ha
        obtain ⟨ca, hca⟩ := ha
        refine ⟨r • ca, ?_⟩
        rw [← hca, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Pi.smul_apply, smul_assoc] }
  have hsub : Set.range v ⊆ (P : Set M) := by
    rintro _ ⟨i, rfl⟩
    show ∃ c : Fin n → K, ∑ j, c j • v j = v i
    refine ⟨Pi.single i 1, ?_⟩
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
    · simp
    · intro j _ hj
      simp [hj]
  exact (Submodule.span_le.mpr hsub) hx
private theorem exists_local_parameters (k : Type*) [CommRing k] (A : Type*) [CommRing A]
    [Algebra k A] [IsLocalRing A] [IsNoetherianRing A]
    [Algebra k (IsLocalRing.ResidueField A)]
    [IsScalarTower k A (IsLocalRing.ResidueField A)]
    [Algebra.FormallySmooth k (IsLocalRing.ResidueField A)] :
    ∃ (h : ℕ) (y : Fin h → A),
      Ideal.span (Set.range y) = IsLocalRing.maximalIdeal A ∧
      LinearIndependent (IsLocalRing.ResidueField A)
        (fun i : Fin h => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
          KaehlerDifferential.D k A (y i)) := by
  classical
  obtain ⟨sF, hsF0⟩ : (IsLocalRing.maximalIdeal A).FG := IsNoetherian.noetherian _
  have hsF : Ideal.span (↑sF : Set A) = IsLocalRing.maximalIdeal A := hsF0
  obtain ⟨b, hbsub, hbspan, hbind⟩ :=
    exists_linearIndependent (K := IsLocalRing.ResidueField A)
      (t := ((fun a : A => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
        KaehlerDifferential.D k A a) '' (↑sF : Set A)))
  have hbfin : b.Finite := Set.Finite.subset (Set.Finite.image _ sF.finite_toSet) hbsub
  let instFintypeB : Fintype b := hbfin.fintype
  choose pre hpre1 hpre2 using fun x : b => hbsub x.2
  obtain ⟨y, hy⟩ : ∃ y : Fin (Fintype.card b) → A,
      ∀ i, y i = pre ((Fintype.equivFin b).symm i) := ⟨_, fun _ => rfl⟩
  have hfun : (fun i : Fin (Fintype.card b) => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
      KaehlerDifferential.D k A (y i))
      = fun i : Fin (Fintype.card b) =>
        ((((Fintype.equivFin b).symm i : b) : IsLocalRing.ResidueField A ⊗[A]
          KaehlerDifferential k A)) := by
    funext i
    rw [hy i]
    exact hpre2 _
  have hind : LinearIndependent (IsLocalRing.ResidueField A)
      (fun i : Fin (Fintype.card b) => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
        KaehlerDifferential.D k A (y i)) := by
    rw [hfun]
    exact hbind.comp _ (Fintype.equivFin b).symm.injective
  have hrange : Set.range (fun i : Fin (Fintype.card b) =>
      (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (y i)) = b := by
    rw [hfun]
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      exact ((Fintype.equivFin b).symm i).2
    · intro hv
      exact ⟨(Fintype.equivFin b) ⟨v, hv⟩, by simp⟩
  have hymem : ∀ i, y i ∈ IsLocalRing.maximalIdeal A := by
    intro i
    rw [← hsF, hy i]
    exact Submodule.subset_span (hpre1 _)
  refine ⟨Fintype.card b, y, ?_, hind⟩
  refine le_antisymm ?_ ?_
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hymem i
  · have hkey : ∀ a ∈ (↑sF : Set A),
        a ∈ Ideal.span (Set.range y) ⊔ IsLocalRing.maximalIdeal A ^ 2 := by
      intro a ha
      have hav : (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A a
          ∈ Submodule.span (IsLocalRing.ResidueField A)
            (Set.range (fun i : Fin (Fintype.card b) =>
              (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
                KaehlerDifferential.D k A (y i))) := by
        rw [hrange, hbspan]
        exact Submodule.subset_span ⟨a, ha, rfl⟩
      obtain ⟨c, hc0⟩ := exists_fun_sum_smul_eq_of_mem_span
        (fun i : Fin (Fintype.card b) => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
          KaehlerDifferential.D k A (y i)) hav
      have hc : (∑ i, c i • ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
          KaehlerDifferential.D k A (y i)))
          = (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A a := hc0
      obtain ⟨c', hc'⟩ : ∃ c' : Fin (Fintype.card b) → A,
          ∀ i, IsLocalRing.residue A (c' i) = c i := by
        have hsurj : Function.Surjective (IsLocalRing.residue A) :=
          Ideal.Quotient.mk_surjective
        choose c' hc' using fun i => hsurj (c i)
        exact ⟨c', hc'⟩
      have hsum : (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
          KaehlerDifferential.D k A (∑ i, c' i * y i)
          = ∑ i, c i • ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
            KaehlerDifferential.D k A (y i)) := by
        rw [map_sum, TensorProduct.tmul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_comm (c' i) (y i),
          KaehlerDifferential.residue_tmul_D_mul_of_mem_maximalIdeal k A (y i) (c' i) (hymem i),
          hc' i]
      have hx0 : (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
          KaehlerDifferential.D k A (a - ∑ i, c' i * y i) = 0 := by
        rw [map_sub, TensorProduct.tmul_sub, hsum, hc, sub_self]
      have hxm : a - ∑ i, c' i * y i ∈ IsLocalRing.maximalIdeal A := by
        refine Submodule.sub_mem _ ?_
          (Submodule.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hymem i))
        rw [← hsF]
        exact Submodule.subset_span ha
      have hxsq := mem_maximalIdeal_sq_of_tmul_D_eq_zero k A _ hxm hx0
      have hrewrite : a = (a - ∑ i, c' i * y i) + ∑ i, c' i * y i := by ring
      rw [hrewrite]
      refine Submodule.add_mem _ (Submodule.mem_sup_right hxsq) (Submodule.mem_sup_left ?_)
      exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
    have hsmul : (IsLocalRing.maximalIdeal A • IsLocalRing.maximalIdeal A : Ideal A)
        = IsLocalRing.maximalIdeal A ^ 2 := by
      rw [Ideal.smul_eq_mul, pow_two]
    have hstep : Ideal.span (↑sF : Set A) ≤ Ideal.span (Set.range y)
        ⊔ IsLocalRing.maximalIdeal A • IsLocalRing.maximalIdeal A := by
      rw [Ideal.span_le]
      intro a ha
      rw [SetLike.mem_coe, hsmul]
      exact hkey a ha
    rw [hsF] at hstep
    have hbotne : (⊥ : Ideal A) ≠ ⊤ := by
      intro hcon
      have hmem1 : (1 : A) ∈ (⊥ : Ideal A) := by
        rw [hcon]; exact Submodule.mem_top
      simp at hmem1
    exact Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
      (IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal A) hbotne).ge hstep
private theorem residue_det_ne_zero_of_basis_tmul {A : Type*} [CommRing A] [IsLocalRing A]
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
    rw [hGj, Module.Basis.toMatrix_apply]
    simp only [Module.Basis.repr_sum_self]
  have hdet : bk.det (⇑B') = IsLocalRing.residue A (bA.det G) := by
    rw [Module.Basis.det_apply, Module.Basis.det_apply, RingHom.map_det]
    congr 1
    ext i j
    simp only [Module.Basis.toMatrix_apply]
    exact hmat i j
  rw [← hdet]
  exact (bk.isUnit_det B').ne_zero
end
end EtaleCoordinates
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
open scoped TensorProduct
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.EtaleCoordinates
namespace FunctorialResolution.EmbeddedResolution.EtaleCoordinates
theorem _root_.solution (k : Type*) [CommRing k] (ι : Type*) [Fintype ι] [DecidableEq ι]
    (S : Type*) [CommRing S] [Algebra k S] [Algebra (MvPolynomial ι k) S]
    [IsScalarTower k (MvPolynomial ι k) S] [Algebra.FormallyEtale (MvPolynomial ι k) S]
    (q : Ideal S) [q.IsPrime] (A : Type*) [CommRing A] [Algebra S A] [Algebra k A]
    [IsScalarTower k S A] [IsLocalization q.primeCompl A] [IsLocalRing A] [IsNoetherianRing A]
    [Algebra k (IsLocalRing.ResidueField A)] [IsScalarTower k A (IsLocalRing.ResidueField A)]
    [Algebra.FormallySmooth k (IsLocalRing.ResidueField A)] :
    ∃ (g : S) (w : ι → S) (J : Finset ι),
      g ∉ q ∧
      (∀ j ∈ J, w j ∈ q) ∧
      Ideal.map (algebraMap S A) (Ideal.span (w '' (↑J : Set ι))) =
        IsLocalRing.maximalIdeal A ∧
      (∀ j ∉ J, ∃ i : ι, w j = coord k ι S i) ∧
      g = (basisKaehler k ι S).det (fun i : ι => KaehlerDifferential.D k S (w i)) ∧
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
  obtain ⟨h, y, hyspan, hyind⟩ := exists_local_parameters k A
  obtain ⟨s, hsq, hsspan, hsind⟩ := exists_generators_maximalIdeal_of_linearIndependent_D k S q A h y hyspan hyind
  obtain ⟨bk, hbk⟩ : ∃ bk : Module.Basis ι (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField A ⊗[A] KaehlerDifferential k A),
      ∀ i, bk i = (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (basisKaehler k ι A i) :=
    ⟨Algebra.TensorProduct.basis (IsLocalRing.ResidueField A) (basisKaehler k ι A),
      fun i => by simp⟩
  obtain ⟨Jst, B, hbasisInl, hbasisInr⟩ := exists_basis_sum_of_linearIndependent bk h
    (fun i : Fin h => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
      KaehlerDifferential.D k A (algebraMap S A (s i))) hsind
  have hcard1 : Module.finrank (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField A ⊗[A] KaehlerDifferential k A)
      = Fintype.card (Fin h ⊕ {j : ι // j ∈ Jst}) := Module.finrank_eq_card_basis B
  have hcard2 : Module.finrank (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField A ⊗[A] KaehlerDifferential k A) = Fintype.card ι :=
    Module.finrank_eq_card_basis bk
  have hcard3 : Fintype.card {j : ι // j ∈ Jst} + Fintype.card {j : ι // ¬ (j ∈ Jst)}
      = Fintype.card ι := by
    rw [← Fintype.card_sum]
    exact Fintype.card_congr (Equiv.sumCompl (fun j : ι => j ∈ Jst))
  rw [Fintype.card_sum, Fintype.card_fin] at hcard1
  have hcard4 : Fintype.card {j : ι // ¬ (j ∈ Jst)} = h := by omega
  have e : {j : ι // ¬ (j ∈ Jst)} ≃ Fin h := Fintype.equivFinOfCardEq hcard4
  obtain ⟨τ, hτl, hτr⟩ : ∃ τ : Fin h ⊕ {j : ι // j ∈ Jst} ≃ ι,
      (∀ l : Fin h, τ (Sum.inl l) = ((e.symm l : ι))) ∧
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
  have hbasisApply : ∀ x : Fin h ⊕ {j : ι // j ∈ Jst},
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
  have hdetne := residue_det_ne_zero_of_basis_tmul (basisKaehler k ι A)
    (fun i : ι => KaehlerDifferential.D k A (algebraMap S A (w i))) (B.reindex τ) hB'G
  have hdetA : algebraMap S A ((basisKaehler k ι S).det
      (fun i : ι => KaehlerDifferential.D k S (w i)))
      = (basisKaehler k ι A).det
        (fun i : ι => KaehlerDifferential.D k A (algebraMap S A (w i))) :=
    algebraMap_det_basisKaehler k ι S A w
  have hmapq : Ideal.map (algebraMap S A) q = IsLocalRing.maximalIdeal A :=
    IsLocalization.AtPrime.map_eq_maximalIdeal q A
  refine ⟨(basisKaehler k ι S).det (fun i : ι => KaehlerDifferential.D k S (w i)), w, Jstᶜ,
    ?_, ?_, ?_, ?_, rfl, ?_⟩
  · intro hgq
    apply hdetne
    rw [← hdetA, IsLocalRing.residue_eq_zero_iff, ← hmapq]
    exact Ideal.mem_map_of_mem _ hgq
  · intro j hj
    have hj' : ¬ (j ∈ Jst) := Finset.mem_compl.mp hj
    have hwj : w j = s (e ⟨j, hj'⟩) := hwn ⟨j, hj'⟩
    rw [hwj]
    exact hsq _
  · rw [Ideal.map_span, ← hsspan]
    congr 1
    ext x
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
  · intro j hj
    have hj' : j ∈ Jst := by
      by_contra hc
      exact hj (Finset.mem_compl.mpr hc)
    exact ⟨j, hwJ j hj'⟩
  · exact IsLocalization.map_units
      (Localization.Away ((basisKaehler k ι S).det fun i : ι => KaehlerDifferential.D k S (w i)))
      ⟨_, Submonoid.mem_powers _⟩
end FunctorialResolution.EmbeddedResolution.EtaleCoordinates
