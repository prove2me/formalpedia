-- Prove2me | solution 1 for GaloisRepAdic.exists_submodule_finrank_le_invariants_mem_of_isUnipotentOnInertiaAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/bf228c27-e09b-5dff-b985-a7099005ca83

import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousH1
import Theorems.Thm_ValuationSubring_exists_tame_generator_inertiaSubgroupIn
import Theorems.Thm_groupCohomology_exists_bijective_H1_map_of_restrictScalars
import Theorems.Thm_ExtCitation_finrank_unramifiedContinuousClasses_eq_finrank_invariants
import Theorems.Thm_groupCohomology_finiteDimensional_continuousH1_of_isOpen_of_primeLocal
import Theorems.Thm_groupCohomology_map_apply_mem_continuousH1_comp
import Theorems.Thm_ValuationSubring_exists_algEquiv_smul_eq_of_liesOverPrime
import Theorems.Thm_ValuationSubring_mem_inertiaSubgroupIn_pointwise_smul_iff
import Theorems.Thm_ExtCitation_liesOverPrime_primeLocalPlace
import Theorems.Thm_groupCohomology_dualLift_unipotentOn_iff_exists_cochain_eq_sub_conj
import Theorems.Thm_GaloisRepAdic_isLocallyConstant_dualLiftToCochain_and_eq_zero_of_isUnramifiedAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRepAdic_exists_submodule_finrank_le_invariants_mem_of_isUnipotentOnInertiaAt
p2m_attr_erase "instance" "GaloisRep.DeformationRingData.instIsLocalHom GaloisRep.DeformationRingData.instCommRing GaloisRep.DeformationRingData.instIsLocalRing GaloisRep.DeformationRingData.instIsNoetherianRing GaloisRep.DeformationRingData.instIsAdicComplete GaloisRep.DeformationRingData.instAlgebra ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete groupCohomology.normal_comap_fixingSubgroup groupCohomology.finiteIndex_comap_fixingSubgroup groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO"
p2m_attr_erase "simp" "GaloisRep.DeformationRingData.mk.injEq GaloisRep.DeformationRingData.mk.sizeOf_spec groupCohomology.Kummer.coe_kummerCocycleRoots groupCohomology.Kummer.mem_powerSubgroup_iff groupCohomology.Kummer.val_smul_units groupCohomology.Kummer.kummerHom_apply groupCohomology.Kummer.coe_smul_rootsOfUnity ExtCitation.LocalLevel.coe_smul_OO IsLocalRing.principalUnits_zero"

set_option autoImplicit false

open CategoryTheory groupCohomology TrivSqZeroExt ExtCitation Polynomial Module
open scoped Pointwise

noncomputable section

namespace P2mBEll

section DualAlgebra

variable {R : Type} [Ring R]

lemma fst_sub_one_sq (x : DualNumber R) :
    ((x - 1) ^ 2).fst = (x.fst - 1) ^ 2 := by
  rw [fst_pow, fst_sub, fst_one]

lemma snd_sub_one_sq (x : DualNumber R) :
    ((x - 1) ^ 2).snd = (x.fst - 1) * x.snd + x.snd * (x.fst - 1) := by
  rw [pow_two, snd_mul, fst_sub, fst_one, snd_sub, snd_one, sub_zero]
  rfl

lemma sub_one_sq_eq_zero_iff (x : DualNumber R) :
    (x - 1) ^ 2 = 0 ↔ (x.fst - 1) ^ 2 = 0 ∧ (x.fst - 1) * x.snd + x.snd * (x.fst - 1) = 0 := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [← fst_sub_one_sq, h, fst_zero]
    · rw [← snd_sub_one_sq, h, snd_zero]
  · rintro ⟨h1, h2⟩
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [fst_sub_one_sq, h1, fst_zero]
    · rw [snd_sub_one_sq, h2, snd_zero]

lemma pow_eq_one_add_nsmul_of_sub_one_sq {S : Type} [Ring S] (x : S) (hx : (x - 1) ^ 2 = 0) (n : ℕ) :
    x ^ n = 1 + n • (x - 1) := by
  set N := x - 1 with hN
  have hxN : x = 1 + N := by rw [hN]; abel
  have hN2 : N * N = 0 := by rw [← pow_two]; exact hx
  induction n with
  | zero => rw [pow_zero, zero_smul, add_zero]
  | succ n ih =>
    rw [pow_succ, ih, hxN, add_mul, one_mul, mul_add, mul_one, smul_mul_assoc, hN2, smul_zero,
      add_zero, add_smul, one_smul, add_assoc, add_comm N]

end DualAlgebra

section Framing

variable {k : Type} [Field k]

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

variable (ρbar : ResidualGaloisRep k) (ρA : GaloisRepAdic (DualNumber k))
  (ρd : Γℚ →* (DualNumber (Module.End k ρbar.V))ˣ)
  (b : Module.Basis (Fin 2) (DualNumber k) ρA.V) (bbar : Module.Basis (Fin 2) k ρbar.V)
  (hfr : ∀ σ, LinearMap.toMatrix b b (ρA.ρ σ) =
      Matrix.dualNumberEquiv.symm
        ⟨LinearMap.toMatrix bbar bbar ((ρd σ : DualNumber (Module.End k ρbar.V)).fst),
          LinearMap.toMatrix bbar bbar ((ρd σ : DualNumber (Module.End k ρbar.V)).snd)⟩)

include hfr

theorem val_sub_one_sq_eq_zero_of_charpoly {σ : Γℚ}
    (hσ : LinearMap.charpoly (ρA.ρ σ) = (X - 1) ^ 2) :
    ((ρd σ : DualNumber (Module.End k ρbar.V)) - 1) ^ 2 = 0 := by
  classical

  have hCH : (ρA.ρ σ - 1) ^ 2 = 0 := by
    have := LinearMap.aeval_self_charpoly (ρA.ρ σ)
    rwa [hσ, map_pow, map_sub, aeval_X, map_one] at this

  set T := LinearMap.toMatrix b b (ρA.ρ σ) with hT
  have hT2 : (T - 1) ^ 2 = 0 := by
    have := congrArg (LinearMap.toMatrixAlgEquiv b) hCH
    rw [map_pow, map_sub, map_one, map_zero] at this
    exact this
  set u := ((ρd σ : DualNumber (Module.End k ρbar.V)).fst) with hu
  set s := ((ρd σ : DualNumber (Module.End k ρbar.V)).snd) with hs
  have hDf : (Matrix.dualNumberEquiv T).fst = LinearMap.toMatrix bbar bbar u := by
    rw [hT, hfr σ, AlgEquiv.apply_symm_apply]; rfl
  have hDs : (Matrix.dualNumberEquiv T).snd = LinearMap.toMatrix bbar bbar s := by
    rw [hT, hfr σ, AlgEquiv.apply_symm_apply]; rfl
  have hD2 := congrArg Matrix.dualNumberEquiv hT2
  rw [map_pow, map_sub, map_one, map_zero] at hD2
  obtain ⟨h1, h2⟩ := (sub_one_sq_eq_zero_iff _).1 hD2
  rw [hDf, hDs] at h2
  rw [hDf] at h1

  have e1 : LinearMap.toMatrixAlgEquiv bbar ((u - 1) ^ 2) = 0 := by
    rw [map_pow, map_sub, map_one]
    exact h1
  have e2 : LinearMap.toMatrixAlgEquiv bbar ((u - 1) * s + s * (u - 1)) = 0 := by
    rw [map_add, map_mul, map_mul, map_sub, map_one]
    exact h2
  rw [map_eq_zero_iff _ (LinearMap.toMatrixAlgEquiv bbar).injective] at e1 e2
  exact (sub_one_sq_eq_zero_iff _).2 ⟨e1, e2⟩

theorem residual_sub_one_sq_eq_zero_of_charpoly (hd : IsDualLift ρbar.ρ.toHomUnits ρd) {σ : Γℚ}
    (hσ : LinearMap.charpoly (ρA.ρ σ) = (X - 1) ^ 2) :
    (ρbar.ρ σ - 1) ^ 2 = 0 := by
  have h := ((sub_one_sq_eq_zero_iff _).1
    (val_sub_one_sq_eq_zero_of_charpoly ρbar ρA ρd b bbar hfr hσ)).1
  rwa [hd σ] at h

end Framing

section CardWorld

lemma tame_generator_card {p q : ℕ} (hp : p.Prime) (hq' : q.Prime) (hpq : p ≠ q)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hq : P.LiesOverPrime q) (m : ℕ) :
    ∃ γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, γ ∈ P.inertiaSubgroupIn ℚ ∧
      ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∃ (j : ℕ) (x w : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
        x ∈ P.inertiaSubgroupIn ℚ ∧ w ∈ P.inertiaSubgroupIn ℚ ∧
          τ = γ ^ j * x ^ (p ^ m) * w ^ (p ^ m) :=
  ValuationSubring.exists_tame_generator_inertiaSubgroupIn hp hq' hpq P hq m

lemma tame_generator_map {p q : ℕ} (hp : p.Prime) (hq' : q.Prime) (hpq : p ≠ q)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hq : P.LiesOverPrime q) (m : ℕ)
    {X : Type} [Monoid X] (f : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* X) :
    ∃ γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, γ ∈ P.inertiaSubgroupIn ℚ ∧
      ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∃ (j : ℕ) (x w : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
        x ∈ P.inertiaSubgroupIn ℚ ∧ w ∈ P.inertiaSubgroupIn ℚ ∧
          f τ = f γ ^ j * f x ^ (p ^ m) * f w ^ (p ^ m) := by
  obtain ⟨γ, hγ, hgen⟩ := tame_generator_card hp hq' hpq P hq m
  refine ⟨γ, hγ, fun τ hτ => ?_⟩
  obtain ⟨j, x, w, hx, hw, hτeq⟩ := hgen τ hτ
  refine ⟨j, x, w, hx, hw, ?_⟩
  rw [hτeq, map_mul, map_mul, map_pow, map_pow, map_pow]

end CardWorld

section Cyclic

variable {k : Type} [Field k] (p : ℕ) [CharP k p]

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

lemma pow_p_eq_one {V : Type} [AddCommGroup V] [Module k V]
    (x : DualNumber (Module.End k V)) (hx : (x - 1) ^ 2 = 0) : x ^ p = 1 := by
  rw [pow_eq_one_add_nsmul_of_sub_one_sq x hx p]
  have : (p : ℕ) • (x - 1) = ((p : k) • (x - 1)) := (Nat.cast_smul_eq_nsmul k p (x - 1)).symm
  rw [this, CharP.cast_eq_zero, zero_smul, add_zero]

variable [Fact p.Prime] {V : Type} [AddCommGroup V] [Module k V]

theorem isCyclic_map_inertia (ρd : Γℚ →* (DualNumber (Module.End k V))ˣ)
    {q : ℕ} (hq : q.Prime) (hpq : p ≠ q)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (hunip : ∀ σ ∈ P.inertiaSubgroupIn ℚ,
      ((ρd σ : DualNumber (Module.End k V)) - 1) ^ 2 = 0) :
    IsCyclic ((P.inertiaSubgroupIn ℚ).map ρd) := by
  obtain ⟨γ, hγ, hgen⟩ := tame_generator_map (Fact.out : p.Prime) hq hpq P hP 1 ρd
  have hpow : ∀ x ∈ P.inertiaSubgroupIn ℚ, ρd x ^ p = 1 := by
    intro x hx
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact pow_p_eq_one p _ (hunip x hx)
  rw [isCyclic_iff_exists_zpowers_eq_top]
  refine ⟨⟨ρd γ, Subgroup.mem_map.2 ⟨γ, hγ, rfl⟩⟩, ?_⟩
  rw [eq_top_iff]
  rintro ⟨y, hy⟩ -
  obtain ⟨τ, hτ, rfl⟩ := Subgroup.mem_map.1 hy
  obtain ⟨j, x, w, hx, hw, hτeq⟩ := hgen τ hτ

  have hτeq' : ρd τ = ρd γ ^ j * ρd x ^ (p ^ 1) * ρd w ^ (p ^ 1) := hτeq
  rw [pow_one, hpow x hx, hpow w hw, mul_one, mul_one] at hτeq'
  rw [Subgroup.mem_zpowers_iff]
  refine ⟨j, Subtype.ext ?_⟩
  change ρd γ ^ (j : ℤ) = ρd τ
  rw [zpow_natCast, hτeq']

end Cyclic

section UrClasses

variable {K : Type} [CommRing K] (ℓ : Nat.Primes)

theorem H1π_surj {G : Type} [Group G] (B : Rep K G) (x : H1 B) :
    ∃ c : cocycles₁ B, (H1π B).hom c = x :=
  H1_induction_on x (fun c => ⟨c, rfl⟩)

def urCocycles (N : Rep K (primeLocalGaloisGroup ℓ)) : Submodule K (cocycles₁ N) where
  carrier := {c |
    (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ (g s : primeLocalGaloisGroup ℓ),
          primeLocalToGlobal ℓ s ∈ F.fixingSubgroup → c.val (g * s) = c.val g) ∧
      ∃ m : N, ∀ g : primeLocalGaloisGroup ℓ,
        primeLocalToGlobal ℓ g ∈ (primeLocalPlace ℓ).inertiaSubgroupIn ℚ → c.val g = N.ρ g m - m}
  zero_mem' := ⟨⟨⊥, inferInstance, fun _ _ _ => rfl⟩, 0, fun g _ => by
    change (0 : primeLocalGaloisGroup ℓ → N) g = _
    rw [Pi.zero_apply, map_zero, sub_zero]⟩
  add_mem' := by
    rintro c d ⟨⟨F, hF, hc⟩, m, hm⟩ ⟨⟨F', hF', hd⟩, m', hm'⟩
    haveI := hF; haveI := hF'
    refine ⟨⟨F ⊔ F', inferInstance, fun g s hs => ?_⟩, m + m', fun g hg => ?_⟩
    · change c.val (g * s) + d.val (g * s) = c.val g + d.val g
      rw [hc g s (IntermediateField.fixingSubgroup_antitone le_sup_left hs),
        hd g s (IntermediateField.fixingSubgroup_antitone le_sup_right hs)]
    · change c.val g + d.val g = _
      rw [hm g hg, hm' g hg, map_add]
      abel
  smul_mem' := by
    rintro a c ⟨⟨F, hF, hc⟩, m, hm⟩
    refine ⟨⟨F, hF, fun g s hs => ?_⟩, a • m, fun g hg => ?_⟩
    · change a • c.val (g * s) = a • c.val g
      rw [hc g s hs]
    · change a • c.val g = _
      rw [hm g hg, map_smul, smul_sub]

def urClasses (N : Rep K (primeLocalGaloisGroup ℓ)) : Submodule K (H1 N) :=
  (urCocycles ℓ N).map (H1π N).hom

lemma mem_urClasses_iff (N : Rep K (primeLocalGaloisGroup ℓ)) (x : H1 N) :
    x ∈ urClasses ℓ N ↔ ∃ c : cocycles₁ N,
      (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ (g s : primeLocalGaloisGroup ℓ),
          primeLocalToGlobal ℓ s ∈ F.fixingSubgroup → c.val (g * s) = c.val g)
      ∧ (∃ m : N, ∀ g : primeLocalGaloisGroup ℓ,
          primeLocalToGlobal ℓ g ∈ (primeLocalPlace ℓ).inertiaSubgroupIn ℚ → c.val g = N.ρ g m - m)
      ∧ (H1π N).hom c = x := by
  simp only [urClasses, Submodule.mem_map]
  constructor
  · rintro ⟨c, ⟨h1, h2⟩, h3⟩
    exact ⟨c, h1, h2, h3⟩
  · rintro ⟨c, h1, h2, h3⟩
    exact ⟨c, ⟨h1, h2⟩, h3⟩

lemma H1π_mem_urClasses {N : Rep K (primeLocalGaloisGroup ℓ)} {c : cocycles₁ N}
    (h1 : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ (g s : primeLocalGaloisGroup ℓ),
          primeLocalToGlobal ℓ s ∈ F.fixingSubgroup → c.val (g * s) = c.val g)
    (h2 : ∃ m : N, ∀ g : primeLocalGaloisGroup ℓ,
          primeLocalToGlobal ℓ g ∈ (primeLocalPlace ℓ).inertiaSubgroupIn ℚ → c.val g = N.ρ g m - m) :
    (H1π N).hom c ∈ urClasses ℓ N :=
  (mem_urClasses_iff ℓ N _).2 ⟨c, h1, h2, rfl⟩

lemma urClasses_le_continuousH1 (N : Rep K (primeLocalGaloisGroup ℓ)) :
    urClasses ℓ N ≤ continuousH1 (primeLocalToGlobal ℓ) N := by
  intro x hx
  obtain ⟨c, h1, -, rfl⟩ := (mem_urClasses_iff ℓ N x).1 hx
  exact H1π_mem_continuousH1 _ N h1

theorem map_top_injective {G : Type} [Group G] (N : Rep K G) :
    Function.Injective
      (map (⊤ : Subgroup G).subtype (𝟙 (Rep.res (⊤ : Subgroup G).subtype N)) 1).hom := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨c, rfl⟩ := H1π_surj N x
  have h := hx
  erw [H1π_comp_map_apply] at h
  rw [H1π_eq_zero_iff] at h
  obtain ⟨m, hm⟩ := h
  rw [H1π_eq_zero_iff]
  refine ⟨m, funext fun g => ?_⟩
  have := congrFun hm ⟨g, Subgroup.mem_top g⟩
  rw [d₀₁_hom_apply] at this ⊢
  exact this

end UrClasses

section ResScalars

variable (k₀ : Type) {k : Type} [Field k₀] [Field k] [Algebra k₀ k]
  {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module k V] [Module k₀ V] [IsScalarTower k₀ k V]

def resScalars (ρ : Representation k G V) : Representation k₀ G V where
  toFun g := (ρ g).restrictScalars k₀
  map_one' := by ext v; simp
  map_mul' g h := by ext v; simp

@[scoped simp] lemma resScalars_apply (ρ : Representation k G V) (g : G) (v : V) :
    resScalars k₀ ρ g v = ρ g v := rfl

lemma invariants_resScalars (ρ : Representation k G V) :
    (resScalars k₀ ρ).invariants = ρ.invariants.restrictScalars k₀ := by
  ext v
  simp only [Submodule.restrictScalars_mem, Representation.mem_invariants, resScalars_apply]

end ResScalars

section Compare

variable {k : Type} [Field k] (p : ℕ) [Fact p.Prime]
  [Algebra (ZMod p) k] (ℓ : Nat.Primes)
  {V : Type} [AddCommGroup V] [Module k V] [Module (ZMod p) V] [IsScalarTower (ZMod p) k V]
  (ρ : Representation k (primeLocalGaloisGroup ℓ) V)

theorem comap_urClasses
    (Ψ : H1 (Rep.of (resScalars (ZMod p) ρ)) →ₛₗ[algebraMap (ZMod p) k] H1 (Rep.of ρ))
    (hinj : Function.Injective Ψ)
    (hΨ : ∀ (c₀ : cocycles₁ (Rep.of (resScalars (ZMod p) ρ))) (c : cocycles₁ (Rep.of ρ)),
      (c₀ : primeLocalGaloisGroup ℓ → V) = c →
        Ψ ((H1π (Rep.of (resScalars (ZMod p) ρ))).hom c₀) = (H1π (Rep.of ρ)).hom c) :
    (urClasses ℓ (Rep.of ρ)).comap Ψ = urClasses ℓ (Rep.of (resScalars (ZMod p) ρ)) := by
  have hcyc : ∀ f : primeLocalGaloisGroup ℓ → V,
      f ∈ cocycles₁ (Rep.of (resScalars (ZMod p) ρ)) ↔ f ∈ cocycles₁ (Rep.of ρ) := by
    intro f
    rw [mem_cocycles₁_iff, mem_cocycles₁_iff]
    rfl
  ext x₀
  rw [Submodule.mem_comap, mem_urClasses_iff, mem_urClasses_iff]
  constructor
  · rintro ⟨c, h1, ⟨m, hm⟩, h3⟩
    obtain ⟨c₀, rfl⟩ := H1π_surj _ x₀
    let c' : cocycles₁ (Rep.of (resScalars (ZMod p) ρ)) := ⟨(c : primeLocalGaloisGroup ℓ → V), (hcyc _).2 c.2⟩
    have hc' : Ψ ((H1π _).hom c') = Ψ ((H1π _).hom c₀) := by rw [hΨ c' c rfl, h3]
    refine ⟨c', h1, ⟨m, hm⟩, hinj hc'⟩
  · rintro ⟨c₀, h1, ⟨m, hm⟩, rfl⟩
    let c : cocycles₁ (Rep.of ρ) := ⟨(c₀ : primeLocalGaloisGroup ℓ → V), (hcyc _).1 c₀.2⟩
    exact ⟨c, h1, ⟨m, hm⟩, (hΨ c₀ c rfl).symm⟩

end Compare

section AdZero

variable {k : Type} [Field k] [Finite k] (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) k]
  (ρbar : ResidualGaloisRep k) (ℓ : Nat.Primes)
  [Module (ZMod p) (LinearMap.ker (LinearMap.trace k ρbar.V))]
  [IsScalarTower (ZMod p) k (LinearMap.ker (LinearMap.trace k ρbar.V))]

abbrev Mloc : Rep k (primeLocalGaloisGroup ℓ) := Rep.res (primeLocalToGlobal ℓ) ρbar.adZero

abbrev Mzero : Rep (ZMod p) (primeLocalGaloisGroup ℓ) := Rep.of (resScalars (ZMod p) (Mloc ρbar ℓ).ρ)

local notation "W" => LinearMap.ker (LinearMap.trace k ρbar.V)
local notation "Mℓ" => Mloc ρbar ℓ
local notation "M₀" => Mzero p ρbar ℓ

omit [Finite k] in

lemma hsm₀ : ∀ m : M₀, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
    ∀ s, primeLocalToGlobal ℓ s ∈ F.fixingSubgroup → (M₀).ρ s m = m := by
  intro m
  obtain ⟨L, hLfd, hL⟩ := ρbar.factorsThroughFiniteLevel
  refine ⟨L, hLfd, fun s hs => ?_⟩
  have h1 : ρbar.ρ (primeLocalToGlobal ℓ s) = 1 :=
    hL _ ((IntermediateField.mem_fixingSubgroup_iff L _).mp hs)
  have h2 : ρbar.ρ (primeLocalToGlobal ℓ s)⁻¹ = 1 := by
    have : ρbar.ρ (primeLocalToGlobal ℓ s)⁻¹ * ρbar.ρ (primeLocalToGlobal ℓ s) = 1 := by
      rw [← map_mul, inv_mul_cancel, map_one]
    rwa [h1, mul_one] at this
  change resScalars (ZMod p) (Mℓ).ρ s m = m
  rw [resScalars_apply]
  apply Subtype.ext
  change ((ρbar.adZeroRep (primeLocalToGlobal ℓ s) m : W) : Module.End k ρbar.V) = m
  rw [ResidualGaloisRep.adZeroRep_apply_coe, h1, h2, one_mul, mul_one]

theorem finiteDimensional_urClasses₀ :
    FiniteDimensional (ZMod p) (urClasses ℓ M₀) := by
  haveI : Finite (Module.End k ρbar.V) := Module.finite_of_finite k
  haveI : Module.Finite (ZMod p) W := Module.Finite.of_finite
  haveI : FiniteDimensional (ZMod p) M₀ := by
    change Module.Finite (ZMod p) W; infer_instance
  let T : Subgroup (primeLocalGaloisGroup ℓ) := ⊤
  let N : Rep (ZMod p) T := Rep.res T.subtype M₀
  haveI : FiniteDimensional (ZMod p) N := by
    change Module.Finite (ZMod p) W; infer_instance
  have hS : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
      F₀.fixingSubgroup.comap (primeLocalToGlobal ℓ) ≤ T := ⟨⊥, inferInstance, fun _ _ => trivial⟩
  have hsmN : ∀ n : N, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : T, ((primeLocalToGlobal ℓ).comp T.subtype) s ∈ F.fixingSubgroup → N.ρ s n = n := by
    intro n
    obtain ⟨F, hF, h⟩ := hsm₀ p ρbar ℓ n
    exact ⟨F, hF, fun s hs => h s.1 hs⟩
  haveI hfin := groupCohomology.finiteDimensional_continuousH1_of_isOpen_of_primeLocal (p := p) ℓ T hS N hsmN

  let φ := (map T.subtype (𝟙 N) 1).hom
  have hφ : ∀ x ∈ continuousH1 (primeLocalToGlobal ℓ) M₀,
      φ x ∈ continuousH1 ((primeLocalToGlobal ℓ).comp T.subtype) N :=
    fun x hx => groupCohomology.map_apply_mem_continuousH1_comp (primeLocalToGlobal ℓ) T.subtype M₀ x hx
  let φ' : continuousH1 (primeLocalToGlobal ℓ) M₀ →ₗ[ZMod p]
      continuousH1 ((primeLocalToGlobal ℓ).comp T.subtype) N :=
    (φ.domRestrict _).codRestrict _ (fun x => hφ x.1 x.2)
  have hφ' : Function.Injective φ' := by
    intro x y hxy
    apply Subtype.ext
    apply map_top_injective M₀
    exact congrArg Subtype.val hxy
  haveI : FiniteDimensional (ZMod p) (continuousH1 (primeLocalToGlobal ℓ) M₀) := Module.Finite.of_injective φ' hφ'
  exact Submodule.finiteDimensional_of_le (urClasses_le_continuousH1 ℓ M₀)

include p in

theorem finiteDimensional_and_finrank_urClasses :
    FiniteDimensional k (urClasses ℓ Mℓ) ∧
      Module.finrank k (urClasses ℓ Mℓ) = Module.finrank k (Mℓ).ρ.invariants := by
  haveI : Finite (Module.End k ρbar.V) := Module.finite_of_finite k
  haveI : Module.Finite (ZMod p) W := Module.Finite.of_finite
  haveI : FiniteDimensional (ZMod p) M₀ := by
    change Module.Finite (ZMod p) W; infer_instance
  haveI : FiniteDimensional (ZMod p) k := Module.Finite.of_finite
  haveI := finiteDimensional_urClasses₀ p ρbar ℓ

  obtain ⟨Ψ, hbij, hΨ, hfin⟩ := groupCohomology.exists_bijective_H1_map_of_restrictScalars
    (k := ZMod p) (K := k) (Mℓ).ρ (resScalars (ZMod p) (Mℓ).ρ) (fun _ _ => rfl)
  have hcomap : (urClasses ℓ Mℓ).comap Ψ = urClasses ℓ M₀ :=
    comap_urClasses p ℓ (Mℓ).ρ Ψ hbij.1 hΨ

  have h76 := ExtCitation.finrank_unramifiedContinuousClasses_eq_finrank_invariants (p := p) ℓ M₀
    (hsm₀ p ρbar ℓ) (urClasses ℓ M₀) (mem_urClasses_iff ℓ M₀)

  haveI : Finite (urClasses ℓ M₀) := Module.finite_of_finite (ZMod p)
  have hsurj : Function.Surjective
      (fun x : urClasses ℓ M₀ => (⟨Ψ x.1, by
        have : x.1 ∈ (urClasses ℓ Mℓ).comap Ψ := by rw [hcomap]; exact x.2
        exact this⟩ : urClasses ℓ Mℓ)) := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hbij.2 y
    have hx : x ∈ urClasses ℓ M₀ := by rw [← hcomap]; exact hy
    exact ⟨⟨x, hx⟩, rfl⟩
  haveI : Finite (urClasses ℓ Mℓ) := Finite.of_surjective _ hsurj
  refine ⟨inferInstance, ?_⟩

  have e1 : Module.finrank (ZMod p) ((urClasses ℓ Mℓ).comap Ψ) =
      Module.finrank (ZMod p) k * Module.finrank k (urClasses ℓ Mℓ) := hfin _
  have e2 : Module.finrank (ZMod p) (M₀).ρ.invariants =
      Module.finrank (ZMod p) k * Module.finrank k (Mℓ).ρ.invariants := by
    have : (M₀).ρ.invariants = ((Mℓ).ρ.invariants).restrictScalars (ZMod p) :=
      invariants_resScalars (ZMod p) (Mℓ).ρ
    rw [this]
    change Module.finrank (ZMod p) ↥((Mℓ).ρ.invariants) = _
    rw [Module.finrank_mul_finrank]
  rw [hcomap, h76, e2] at e1
  have hpos : 0 < Module.finrank (ZMod p) k := Module.finrank_pos
  exact (Nat.eq_of_mul_eq_mul_left hpos e1).symm

end AdZero

section Membership

variable {k : Type} [Field k] (ρbar : ResidualGaloisRep k) (ℓ : Nat.Primes)

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

lemma two_ne_zero_of_charP (p : ℕ) [Fact p.Prime] [CharP k p] (hp2 : p ≠ 2) : (2 : k) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : k) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff k p] at h'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h')

lemma exists_inertia_ne_one (hram : ¬ ρbar.IsUnramifiedAt ℓ) :
    ∃ g ∈ (primeLocalPlace ℓ).inertiaSubgroupIn ℚ, ρbar.ρ g ≠ 1 := by
  simp only [ResidualGaloisRep.IsUnramifiedAt, not_forall] at hram
  obtain ⟨A, hA, σ, hσ, hne⟩ := hram
  obtain ⟨g, hg⟩ := ValuationSubring.exists_algEquiv_smul_eq_of_liesOverPrime ℓ.2 A (primeLocalPlace ℓ)
    hA (liesOverPrime_primeLocalPlace ℓ)
  refine ⟨g * σ * g⁻¹, ?_, ?_⟩
  · rw [← hg, ValuationSubring.mem_inertiaSubgroupIn_pointwise_smul_iff]
    have : g⁻¹ * (g * σ * g⁻¹) * g = σ := by group
    rw [this]
    exact hσ
  · intro h
    apply hne
    have e : ρbar.ρ σ = ρbar.ρ g⁻¹ * ρbar.ρ (g * σ * g⁻¹) * ρbar.ρ g := by
      rw [← map_mul, ← map_mul]
      congr 1
      group
    rw [e, h, mul_one, ← map_mul, inv_mul_cancel, map_one]

lemma exists_traceZero_coboundary (h2 : (2 : k) ≠ 0) (m : Module.End k ρbar.V) :
    ∃ n : LinearMap.ker (LinearMap.trace k ρbar.V), ∀ g : Γℚ,
      m - ρbar.ρ g * m * ρbar.ρ g⁻¹ =
        ((ρbar.adZeroRep g n : LinearMap.ker (LinearMap.trace k ρbar.V)) : Module.End k ρbar.V) - n := by
  set t : k := (2 : k)⁻¹ * LinearMap.trace k ρbar.V m with ht
  set m₀ : Module.End k ρbar.V := m - t • (1 : Module.End k ρbar.V) with hm₀
  have htr : LinearMap.trace k ρbar.V m₀ = 0 := by
    rw [hm₀, map_sub, map_smul, LinearMap.trace_one, ρbar.finrank_eq, ht, smul_eq_mul]
    push_cast
    field_simp
    ring
  have hneg : LinearMap.trace k ρbar.V (-m₀) = 0 := by rw [map_neg, htr, neg_zero]
  refine ⟨⟨-m₀, LinearMap.mem_ker.2 hneg⟩, fun g => ?_⟩
  have hunit : ρbar.ρ g * ρbar.ρ g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  rw [ResidualGaloisRep.adZeroRep_apply_coe]
  change m - ρbar.ρ g * m * ρbar.ρ g⁻¹ = ρbar.ρ g * (-m₀) * ρbar.ρ g⁻¹ - (-m₀)
  rw [hm₀]
  simp only [neg_sub, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, hunit]
  abel

end Membership

section Main

variable {k : Type} [Field k] [Finite k] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) [CharP k p]
  (ρbar : ResidualGaloisRep k) (ℓ : Nat.Primes) (hℓp : (ℓ : ℕ) ≠ p) (hram : ¬ ρbar.IsUnramifiedAt ℓ)

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

omit [Finite k] in
include hp2 hℓp hram in

theorem mem_urClasses (ρA : GaloisRepAdic (DualNumber k)) (hunipA : ρA.IsUnipotentOnInertiaAt ℓ)
    (ρd : Γℚ →* (DualNumber (Module.End k ρbar.V))ˣ) (hd : IsDualLift ρbar.ρ.toHomUnits ρd)
    (b : Module.Basis (Fin 2) (DualNumber k) ρA.V) (bbar : Module.Basis (Fin 2) k ρbar.V)
    (hfr : ∀ σ, LinearMap.toMatrix b b (ρA.ρ σ) =
      Matrix.dualNumberEquiv.symm
        ⟨LinearMap.toMatrix bbar bbar ((ρd σ : DualNumber (Module.End k ρbar.V)).fst),
          LinearMap.toMatrix bbar bbar ((ρd σ : DualNumber (Module.End k ρbar.V)).snd)⟩)
    (c : cocycles₁ ρbar.adZero)
    (hc : ∀ σ, ((c : Γℚ → ↥(LinearMap.ker (LinearMap.trace k ρbar.V))) σ : Module.End k ρbar.V) =
      dualLiftToCochain ρbar.ρ.toHomUnits ρd σ) :
    (groupCohomology.map (primeLocalToGlobal ℓ)
      (𝟙 (Rep.res (primeLocalToGlobal ℓ) ρbar.adZero)) 1).hom (H1π ρbar.adZero c) ∈
      urClasses ℓ (Mloc ρbar ℓ) := by
  classical
  set P := primeLocalPlace ℓ with hPdef
  have hP : P.LiesOverPrime ℓ := liesOverPrime_primeLocalPlace ℓ
  set I := P.inertiaSubgroupIn ℚ with hIdef

  have hcp : ∀ σ ∈ I, LinearMap.charpoly (ρA.ρ σ) = (X - 1) ^ 2 := fun σ hσ => hunipA P hP σ hσ
  have hsq : ∀ σ ∈ I, ((ρd σ : DualNumber (Module.End k ρbar.V)) - 1) ^ 2 = 0 :=
    fun σ hσ => val_sub_one_sq_eq_zero_of_charpoly ρbar ρA ρd b bbar hfr (hcp σ hσ)
  have hunip : ∀ σ ∈ I, (ρbar.ρ σ - 1) ^ 2 = 0 :=
    fun σ hσ => residual_sub_one_sq_eq_zero_of_charpoly ρbar ρA ρd b bbar hfr hd (hcp σ hσ)

  have hcyc : IsCyclic (I.map ρd) :=
    isCyclic_map_inertia p ρd ℓ.2 (fun h => hℓp h.symm) P hP hsq

  have hne : ∃ g ∈ I, ρbar.ρ g ≠ 1 := exists_inertia_ne_one ρbar ℓ hram

  obtain ⟨m, hm⟩ := (groupCohomology.dualLift_unipotentOn_iff_exists_cochain_eq_sub_conj ρbar.finrank_eq
    ρbar.ρ ρd hd I hcyc hne hunip).1 hsq

  obtain ⟨n, hn⟩ := exists_traceZero_coboundary ρbar (two_ne_zero_of_charP p hp2) m

  obtain ⟨-, ⟨F, hF, -, hlev⟩, -⟩ :=
    GaloisRepAdic.isLocallyConstant_dualLiftToCochain_and_eq_zero_of_isUnramifiedAt ρbar ρA ρd hd b bbar hfr

  set cres : cocycles₁ (Mloc ρbar ℓ) :=
    (mapCocycles₁ (primeLocalToGlobal ℓ) (𝟙 (Rep.res (primeLocalToGlobal ℓ) ρbar.adZero))) c with hcres
  have hval : ∀ g, cres.val g = c (primeLocalToGlobal ℓ g) := fun g => rfl
  have hres : (groupCohomology.map (primeLocalToGlobal ℓ)
      (𝟙 (Rep.res (primeLocalToGlobal ℓ) ρbar.adZero)) 1).hom (H1π ρbar.adZero c) =
      (H1π (Mloc ρbar ℓ)).hom cres := by
    erw [H1π_comp_map_apply]
  rw [hres]
  refine H1π_mem_urClasses ℓ ⟨F, hF, fun g s hs => ?_⟩ ⟨n, fun g hg => ?_⟩
  · rw [hval, hval, map_mul]
    apply Subtype.ext
    rw [hc, hc]
    exact hlev _ _ ((IntermediateField.mem_fixingSubgroup_iff F _).1 hs)
  · rw [hval]
    apply Subtype.ext
    rw [hc, hm _ hg, hn]
    rfl

include hp2 hℓp hram in
theorem main :
    ∃ L : Submodule k (H1 (Rep.res (primeLocalToGlobal ℓ) ρbar.adZero)),
      FiniteDimensional k L ∧
      Module.finrank k L ≤
        Module.finrank k (Rep.res (primeLocalToGlobal ℓ) ρbar.adZero).ρ.invariants ∧
      ∀ (ρA : GaloisRepAdic (DualNumber k)), ρA.IsUnipotentOnInertiaAt ℓ →
        ∀ ρd : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (DualNumber (Module.End k ρbar.V))ˣ,
          IsDualLift ρbar.ρ.toHomUnits ρd →
          (∃ (b : Module.Basis (Fin 2) (DualNumber k) ρA.V) (bbar : Module.Basis (Fin 2) k ρbar.V),
            ∀ σ, LinearMap.toMatrix b b (ρA.ρ σ) =
              Matrix.dualNumberEquiv.symm
                ⟨LinearMap.toMatrix bbar bbar ((ρd σ : DualNumber (Module.End k ρbar.V)).fst),
                  LinearMap.toMatrix bbar bbar ((ρd σ : DualNumber (Module.End k ρbar.V)).snd)⟩) →
          ∀ c : cocycles₁ ρbar.adZero,
            (∀ σ, ((c : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →
                ↥(LinearMap.ker (LinearMap.trace k ρbar.V))) σ : Module.End k ρbar.V) =
              dualLiftToCochain ρbar.ρ.toHomUnits ρd σ) →
            (groupCohomology.map (primeLocalToGlobal ℓ)
              (𝟙 (Rep.res (primeLocalToGlobal ℓ) ρbar.adZero)) 1).hom (H1π ρbar.adZero c) ∈ L := by
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  letI : Module (ZMod p) (LinearMap.ker (LinearMap.trace k ρbar.V)) :=
    Module.compHom _ (algebraMap (ZMod p) k)
  haveI : IsScalarTower (ZMod p) k (LinearMap.ker (LinearMap.trace k ρbar.V)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  obtain ⟨hfd, hrank⟩ := finiteDimensional_and_finrank_urClasses p ρbar ℓ
  refine ⟨urClasses ℓ (Mloc ρbar ℓ), hfd, hrank.le, ?_⟩
  rintro ρA hunipA ρd hd ⟨b, bbar, hfr⟩ c hc
  exact mem_urClasses p hp2 ρbar ℓ hℓp hram ρA hunipA ρd hd b bbar hfr c hc

end Main

end P2mBEll
p2m_reactivate "P2MW.S_GaloisRepAdic_exists_submodule_finrank_le_invariants_mem_of_isUnipotentOnInertiaAt.P2mBEll"

end
p2m_reactivate "P2MW.S_GaloisRepAdic_exists_submodule_finrank_le_invariants_mem_of_isUnipotentOnInertiaAt.P2mBEll"

theorem solution
    {k : Type} [Field k] [Finite k] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) [CharP k p]
    (ρbar : ResidualGaloisRep k) (ℓ : Nat.Primes) (hℓp : (ℓ : ℕ) ≠ p)
    (hram : ¬ ρbar.IsUnramifiedAt ℓ) :
    ∃ L : Submodule k (H1 (Rep.res (primeLocalToGlobal ℓ) ρbar.adZero)),
      FiniteDimensional k L ∧
      Module.finrank k L ≤
        Module.finrank k (Rep.res (primeLocalToGlobal ℓ) ρbar.adZero).ρ.invariants ∧
      ∀ (ρA : GaloisRepAdic (DualNumber k)), ρA.IsUnipotentOnInertiaAt ℓ →
        ∀ ρd : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (DualNumber (Module.End k ρbar.V))ˣ,
          IsDualLift ρbar.ρ.toHomUnits ρd →
          (∃ (b : Module.Basis (Fin 2) (DualNumber k) ρA.V) (bbar : Module.Basis (Fin 2) k ρbar.V),
            ∀ σ, LinearMap.toMatrix b b (ρA.ρ σ) =
              Matrix.dualNumberEquiv.symm
                ⟨LinearMap.toMatrix bbar bbar ((ρd σ : DualNumber (Module.End k ρbar.V)).fst),
                  LinearMap.toMatrix bbar bbar ((ρd σ : DualNumber (Module.End k ρbar.V)).snd)⟩) →
          ∀ c : cocycles₁ ρbar.adZero,
            (∀ σ, ((c : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →
                ↥(LinearMap.ker (LinearMap.trace k ρbar.V))) σ : Module.End k ρbar.V) =
              dualLiftToCochain ρbar.ρ.toHomUnits ρd σ) →
            (groupCohomology.map (primeLocalToGlobal ℓ)
              (𝟙 (Rep.res (primeLocalToGlobal ℓ) ρbar.adZero)) 1).hom (H1π ρbar.adZero c) ∈ L :=
  P2mBEll.main p hp2 ρbar ℓ hℓp hram

end S_GaloisRepAdic_exists_submodule_finrank_le_invariants_mem_of_isUnipotentOnInertiaAt
end P2MW
export P2MW.S_GaloisRepAdic_exists_submodule_finrank_le_invariants_mem_of_isUnipotentOnInertiaAt (solution)
