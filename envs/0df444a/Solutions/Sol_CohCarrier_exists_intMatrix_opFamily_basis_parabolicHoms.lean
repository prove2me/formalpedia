-- Prove2me | solution 1 for CohCarrier.exists_intMatrix_opFamily_basis_parabolicHoms
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/82a7f1b3-224e-5dd4-8c6e-8fca814c5827

import Mathlib
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_ModularCurve_PeriodMap
import Theorems.Thm_ModularCurve_Period_exists_basis_parabolicHoms_of_isAddTorsionFree
import Theorems.Thm_CohCarrier_opFamily_apply_mem_parabolicHoms_gammaH
import Theorems.Thm_CohCarrier_heckeT_comp_coeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_exists_intMatrix_opFamily_basis_parabolicHoms
p2m_attr_erase "instance" "ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 HeckeEis.instFiniteIndexHeckeUpper"
p2m_attr_erase "simp" "HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero"

set_option autoImplicit false

open scoped MatrixGroups
open CongruenceSubgroup
open Module

namespace IntMatrixOrder

def uncurryEquiv (n : ℕ) (A : Type*) [CommRing A] :
    Matrix (Fin n) (Fin n) A ≃ₗ[A] (Fin n × Fin n → A) where
  toFun M p := M p.1 p.2
  invFun v := Matrix.of fun i j => v (i, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem linearIndependent_map_intCast_of_basis {κ : Type*} [Fintype κ] {n : ℕ}
    (b : Basis κ ℤ (Matrix (Fin n) (Fin n) ℤ)) (R : Type*) [CommRing R] :
    LinearIndependent R (fun i => (b i).map (Int.castRingHom R)) := by
  classical
  let b' : Basis κ ℤ (Fin n × Fin n → ℤ) := b.map (uncurryEquiv n ℤ)
  let B : Basis κ R (Fin n × Fin n → R) :=
    (Algebra.TensorProduct.basis R b').map (TensorProduct.piScalarRight ℤ R R (Fin n × Fin n))
  have hB : ∀ i, B i = uncurryEquiv n R ((b i).map (Int.castRingHom R)) := by
    intro i
    ext p
    simp [B, b', uncurryEquiv, Algebra.TensorProduct.basis_apply,
      TensorProduct.piScalarRightHom_tmul]
  have hli := B.linearIndependent
  have hfun : (⇑B) = (uncurryEquiv n R) ∘ (fun i => (b i).map (Int.castRingHom R)) :=
    funext hB
  rw [hfun] at hli
  exact LinearIndependent.of_comp (uncurryEquiv n R).toLinearMap hli

theorem map_intCast_sum_zsmul {n K : ℕ} (R : Type*) [CommRing R]
    (d : Fin K → ℤ) (u : Fin K → Matrix (Fin n) (Fin n) ℤ) :
    (∑ m, d m • u m).map (Int.castRingHom R) =
      ∑ m, (d m : R) • (u m).map (Int.castRingHom R) := by
  change (Int.castRingHom R).mapMatrix (∑ m, d m • u m) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_zsmul, Int.cast_smul_eq_zsmul]
  rfl

end IntMatrixOrder

namespace IntMatrixSol

theorem Gamma_le_GammaH (M : ℕ) (H : Subgroup (ZMod M)ˣ) : Gamma M ≤ CohCarrier.GammaH M H := by
  intro A hA
  obtain ⟨-, -, h10, h11⟩ := Gamma_mem.mp hA
  rw [CohCarrier.mem_GammaH_iff]
  have hA0 : A ∈ Gamma0 M := by rw [Gamma0_mem]; exact h10
  refine ⟨hA0, ?_⟩
  have h1 : CohCarrier.gamma0Units M ⟨A, hA0⟩ = 1 := by
    apply Units.ext
    rw [CohCarrier.val_gamma0Units, Units.val_one]
    exact h11
  rw [h1]; exact one_mem H

scoped instance GammaH.finiteIndex (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    (CohCarrier.GammaH M H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma_le_GammaH M H)

p2m_reactivate "P2MW.S_CohCarrier_exists_intMatrix_opFamily_basis_parabolicHoms.IntMatrixSol.GammaH"

theorem opFamily_comp_castAddHom (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ)
    (R : Type) [CommRing R] (g : CohCarrier.Gen M S) (φ : CohCarrier.H1 M H ℤ) :
    CohCarrier.opFamily M H S R g ((Int.castAddHom R).comp φ) =
      (Int.castAddHom R).comp (CohCarrier.opFamily M H S ℤ g φ) := by
  cases g with
  | T ℓ hℓ hℓS hℓM =>
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    show CohCarrier.heckeTL M H R ℓ _ = (Int.castAddHom R).comp (CohCarrier.heckeTL M H ℤ ℓ φ)
    rw [CohCarrier.heckeTL_apply, CohCarrier.heckeTL_apply]
    exact CohCarrier.heckeT_comp_coeff M H ℓ (Int.castAddHom R) φ
  | U q hq hqM =>
    haveI : NeZero q := ⟨hq.ne_zero⟩
    show CohCarrier.heckeTL M H R q _ = (Int.castAddHom R).comp (CohCarrier.heckeTL M H ℤ q φ)
    rw [CohCarrier.heckeTL_apply, CohCarrier.heckeTL_apply]
    exact CohCarrier.heckeT_comp_coeff M H q (Int.castAddHom R) φ
  | dia d =>
    show CohCarrier.diamondL M H R d _ = (Int.castAddHom R).comp (CohCarrier.diamondL M H ℤ d φ)
    ext γ
    rfl

set_option maxHeartbeats 6400000 in
private theorem _root_.IntMatrixOrder.exists_intBasis_adjoin
    {ι : Type} (n : ℕ) (T : ι → Matrix (Fin n) (Fin n) ℤ) :
    ∃ (K : ℕ) (u : Fin K → Matrix (Fin n) (Fin n) ℤ)
      (c : Fin K → Fin K → Fin K → ℤ) (c₁ : Fin K → ℤ) (cT : ι → Fin K → ℤ),
      (∀ k l : Fin K, u k * u l = ∑ m, c k l m • u m) ∧
      (∑ m, c₁ m • u m = 1) ∧
      (∀ g : ι, ∑ m, cT g m • u m = T g) ∧
      (∀ k : Fin K, u k ∈ Algebra.adjoin ℤ (Set.range T)) ∧
      ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R],
        LinearIndependent R (fun k : Fin K => (u k).map (Int.castRingHom R)) ∧
        Submodule.span R (Set.range fun k : Fin K => (u k).map (Int.castRingHom R)) =
          Subalgebra.toSubmodule
            (Algebra.adjoin R (Set.range fun g : ι => (T g).map (Int.castRingHom R))) := by
  classical

  let O : Subalgebra ℤ (Matrix (Fin n) (Fin n) ℤ) := Algebra.adjoin ℤ (Set.range T)
  let S : Submodule ℤ (Matrix (Fin n) (Fin n) ℤ) := Subalgebra.toSubmodule O

  obtain ⟨K, snf⟩ := Submodule.smithNormalForm (Matrix.stdBasis ℤ (Fin n) (Fin n)) S
  let bN : Basis (Fin K) ℤ S := snf.bN
  let u : Fin K → Matrix (Fin n) (Fin n) ℤ := fun k => (bN k : Matrix (Fin n) (Fin n) ℤ)
  have hu_mem : ∀ k, u k ∈ O := fun k => (bN k).2

  have hsum : ∀ x : S, ∑ m, bN.repr x m • u m = (x : Matrix (Fin n) (Fin n) ℤ) := by
    intro x
    have h := congrArg (Subtype.val : S → Matrix (Fin n) (Fin n) ℤ) (bN.sum_repr x)
    refine Eq.trans ?_ h
    rw [Submodule.coe_sum]
    rfl
  let c : Fin K → Fin K → Fin K → ℤ := fun k l m =>
    bN.repr ⟨u k * u l, O.mul_mem (hu_mem k) (hu_mem l)⟩ m
  let c₁ : Fin K → ℤ := fun m => bN.repr ⟨1, O.one_mem⟩ m
  let cT : ι → Fin K → ℤ := fun g m =>
    bN.repr ⟨T g, Algebra.subset_adjoin (Set.mem_range_self g)⟩ m
  have hmul : ∀ k l : Fin K, u k * u l = ∑ m, c k l m • u m :=
    fun k l => (hsum ⟨u k * u l, O.mul_mem (hu_mem k) (hu_mem l)⟩).symm
  have hone : ∑ m, c₁ m • u m = 1 := hsum ⟨1, O.one_mem⟩
  have hT : ∀ g : ι, ∑ m, cT g m • u m = T g :=
    fun g => hsum ⟨T g, Algebra.subset_adjoin (Set.mem_range_self g)⟩
  refine ⟨K, u, c, c₁, cT, hmul, hone, hT, hu_mem, ?_⟩
  intro R _ _ _

  let φ : Matrix (Fin n) (Fin n) ℤ →ₐ[ℤ] Matrix (Fin n) (Fin n) R := (Algebra.ofId ℤ R).mapMatrix
  have hφ : ∀ M : Matrix (Fin n) (Fin n) ℤ, φ M = M.map (Int.castRingHom R) := fun M => rfl

  have ha : ∀ k, snf.a k ≠ 0 := by
    intro k hk
    have h := snf.snf k
    rw [hk, zero_smul] at h
    exact bN.ne_zero k (Subtype.ext h)
  have indep : LinearIndependent R (fun k : Fin K => (u k).map (Int.castRingHom R)) := by
    have hli := (IntMatrixOrder.linearIndependent_map_intCast_of_basis snf.bM R).comp snf.f snf.f.injective
    rw [Fintype.linearIndependent_iff] at hli ⊢
    intro r hr k
    have hu' : ∀ k, (u k).map (Int.castRingHom R) =
        (snf.a k : R) • (snf.bM (snf.f k)).map (Int.castRingHom R) := by
      intro k
      change ((bN k : Matrix (Fin n) (Fin n) ℤ)).map _ = _
      rw [snf.snf k]
      change (Int.castRingHom R).mapMatrix _ = _
      rw [map_zsmul, Int.cast_smul_eq_zsmul]
      rfl
    have key : ∑ k, (r k * (snf.a k : R)) • (snf.bM (snf.f k)).map (Int.castRingHom R) = 0 := by
      rw [← hr]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hu' k, smul_smul]
    have h0 := hli (fun k => r k * (snf.a k : R)) key k
    have hak : (snf.a k : R) ≠ 0 := Int.cast_ne_zero.mpr (ha k)
    exact (mul_eq_zero.mp h0).resolve_right hak

  have hφu : ∀ k, (u k).map (Int.castRingHom R) ∈
      Algebra.adjoin R (Set.range fun g : ι => (T g).map (Int.castRingHom R)) := by
    intro k
    have h1 : φ (u k) ∈ (Algebra.adjoin ℤ (Set.range T)).map φ :=
      Subalgebra.mem_map.mpr ⟨u k, hu_mem k, rfl⟩
    rw [AlgHom.map_adjoin, ← Set.range_comp] at h1
    have h2 : Algebra.adjoin ℤ (Set.range (⇑φ ∘ T)) ≤
        (Algebra.adjoin R (Set.range fun g : ι => (T g).map (Int.castRingHom R))).restrictScalars
          ℤ := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨g, rfl⟩
      exact Algebra.subset_adjoin ⟨g, rfl⟩
    exact h2 h1
  refine ⟨indep, le_antisymm ?_ ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact hφu k
  · set sp := Submodule.span R (Set.range fun k : Fin K => (u k).map (Int.castRingHom R))
      with hsp
    have mem_of : ∀ d : Fin K → ℤ, (∑ m, d m • u m).map (Int.castRingHom R) ∈ sp := by
      intro d
      rw [IntMatrixOrder.map_intCast_sum_zsmul]
      exact Submodule.sum_mem _ fun m _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
    have one_mem : (1 : Matrix (Fin n) (Fin n) R) ∈ sp := by
      have h := mem_of c₁
      rwa [hone, Matrix.map_one _ (map_zero _) (map_one _)] at h
    have T_mem : ∀ g, (T g).map (Int.castRingHom R) ∈ sp := by
      intro g
      have h := mem_of (cT g)
      rwa [hT g] at h
    have mul_mem : ∀ x y, x ∈ sp → y ∈ sp → x * y ∈ sp := by
      intro x y hx hy
      have hxy : x * y ∈ sp * sp := Submodule.mul_mem_mul hx hy
      rw [hsp, Submodule.span_mul_span] at hxy
      refine (Submodule.span_le.mpr ?_) hxy
      rintro _ ⟨_, ⟨k, rfl⟩, _, ⟨l, rfl⟩, rfl⟩
      change (u k).map (Int.castRingHom R) * (u l).map (Int.castRingHom R) ∈ sp
      rw [← Matrix.map_mul, hmul k l]
      exact mem_of _
    have hle : Algebra.adjoin R (Set.range fun g : ι => (T g).map (Int.castRingHom R)) ≤
        sp.toSubalgebra one_mem mul_mem :=
      Algebra.adjoin_le (by rintro _ ⟨g, rfl⟩; exact T_mem g)
    intro x hx
    exact hle hx

p2m_alias "P2MW.S_CohCarrier_exists_intMatrix_opFamily_basis_parabolicHoms.IntMatrixOrder.exists_intBasis_adjoin" "IntMatrixOrder.exists_intBasis_adjoin"

theorem exists_intMatrix_basis (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ) :
    ∃ (n : ℕ) (T : CohCarrier.Gen M S → Matrix (Fin n) (Fin n) ℤ),
      ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R],
        ∃ bR : Module.Basis (Fin n) R ↥(ModularCurve.Period.parabolicHoms R (CohCarrier.GammaH M H) R),
          ∀ (g : CohCarrier.Gen M S) (j : Fin n),
            CohCarrier.opFamily M H S R g
                ((bR j : ↥(ModularCurve.Period.parabolicHoms R (CohCarrier.GammaH M H) R)) :
                  CohCarrier.H1 M H R) =
              ∑ i, ((T g i j : ℤ) : R) •
                ((bR i : ↥(ModularCurve.Period.parabolicHoms R (CohCarrier.GammaH M H) R)) :
                  CohCarrier.H1 M H R) := by
  classical
  obtain ⟨n, b, hb⟩ :=
    ModularCurve.Period.exists_basis_parabolicHoms_of_isAddTorsionFree (CohCarrier.GammaH M H)

  have hmem : ∀ (g : CohCarrier.Gen M S) (j : Fin n),
      CohCarrier.opFamily M H S ℤ g
          ((b j : ↥(ModularCurve.Period.parabolicHoms ℤ (CohCarrier.GammaH M H) ℤ)) : CohCarrier.H1 M H ℤ) ∈
        ModularCurve.Period.parabolicHoms ℤ (CohCarrier.GammaH M H) ℤ :=
    fun g j => CohCarrier.opFamily_apply_mem_parabolicHoms_gammaH M H S ℤ g _ (b j).2

  refine ⟨n, fun g => Matrix.of fun i j => b.repr ⟨_, hmem g j⟩ i, ?_⟩
  intro R _ _ _
  obtain ⟨bR, hbR⟩ := hb R
  refine ⟨bR, fun g j => ?_⟩

  have hZ : CohCarrier.opFamily M H S ℤ g
        ((b j : ↥(ModularCurve.Period.parabolicHoms ℤ (CohCarrier.GammaH M H) ℤ)) : CohCarrier.H1 M H ℤ) =
      ∑ i, (b.repr ⟨_, hmem g j⟩ i) •
        ((b i : ↥(ModularCurve.Period.parabolicHoms ℤ (CohCarrier.GammaH M H) ℤ)) : CohCarrier.H1 M H ℤ) := by
    have h := b.sum_repr ⟨_, hmem g j⟩
    have h' := congrArg (fun x : ↥(ModularCurve.Period.parabolicHoms ℤ (CohCarrier.GammaH M H) ℤ) =>
      (x : CohCarrier.H1 M H ℤ)) h
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h'
    exact h'.symm

  have hj : ((bR j : ↥(ModularCurve.Period.parabolicHoms R (CohCarrier.GammaH M H) R)) : CohCarrier.H1 M H R) =
      (Int.castAddHom R).comp
        ((b j : ↥(ModularCurve.Period.parabolicHoms ℤ (CohCarrier.GammaH M H) ℤ)) : CohCarrier.H1 M H ℤ) :=
    hbR j
  rw [hj, opFamily_comp_castAddHom, hZ]
  refine DFunLike.ext _ _ fun γ => ?_
  rw [AddMonoidHom.comp_apply, AddMonoidHom.finset_sum_apply, AddMonoidHom.finset_sum_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  dsimp only [Matrix.of_apply]
  rw [AddMonoidHom.smul_apply, AddMonoidHom.smul_apply, hbR i, AddMonoidHom.comp_apply,
    zsmul_eq_mul, smul_eq_mul]
  exact Int.cast_mul _ _

end IntMatrixSol
p2m_reactivate "P2MW.S_CohCarrier_exists_intMatrix_opFamily_basis_parabolicHoms.IntMatrixSol.GammaH P2MW.S_CohCarrier_exists_intMatrix_opFamily_basis_parabolicHoms.IntMatrixSol"

theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ) :
    ∃ (n K : ℕ) (T : CohCarrier.Gen M S → Matrix (Fin n) (Fin n) ℤ) (u : Fin K → Matrix (Fin n) (Fin n) ℤ)
      (c : Fin K → Fin K → Fin K → ℤ) (c₁ : Fin K → ℤ) (cT : CohCarrier.Gen M S → Fin K → ℤ),
      (∀ k l : Fin K, u k * u l = ∑ m, c k l m • u m) ∧
      (∑ m, c₁ m • u m = 1) ∧
      (∀ g : CohCarrier.Gen M S, ∑ m, cT g m • u m = T g) ∧
      (∀ k : Fin K, u k ∈ Algebra.adjoin ℤ (Set.range T)) ∧
      ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R],
        LinearIndependent R (fun k : Fin K => (u k).map (Int.castRingHom R)) ∧
        Submodule.span R (Set.range fun k : Fin K => (u k).map (Int.castRingHom R)) =
          Subalgebra.toSubmodule
            (Algebra.adjoin R (Set.range fun g : CohCarrier.Gen M S => (T g).map (Int.castRingHom R))) ∧
        ∃ bR : Module.Basis (Fin n) R ↥(ModularCurve.Period.parabolicHoms R (CohCarrier.GammaH M H) R),
          ∀ (g : CohCarrier.Gen M S) (j : Fin n),
            CohCarrier.opFamily M H S R g
                ((bR j : ↥(ModularCurve.Period.parabolicHoms R (CohCarrier.GammaH M H) R)) :
                  CohCarrier.H1 M H R) =
              ∑ i, ((T g i j : ℤ) : R) •
                ((bR i : ↥(ModularCurve.Period.parabolicHoms R (CohCarrier.GammaH M H) R)) :
                  CohCarrier.H1 M H R) := by
  obtain ⟨n, T, hA⟩ := IntMatrixSol.exists_intMatrix_basis M H S
  obtain ⟨K, u, c, c₁, cT, h1, h2, h3, h4, hR⟩ := IntMatrixOrder.exists_intBasis_adjoin n T
  refine ⟨n, K, T, u, c, c₁, cT, h1, h2, h3, h4, fun R _ _ _ => ?_⟩
  obtain ⟨hli, hsp⟩ := hR R
  obtain ⟨bR, hbR⟩ := hA R
  exact ⟨hli, hsp, bR, hbR⟩

end S_CohCarrier_exists_intMatrix_opFamily_basis_parabolicHoms
end P2MW
export P2MW.S_CohCarrier_exists_intMatrix_opFamily_basis_parabolicHoms (solution)
