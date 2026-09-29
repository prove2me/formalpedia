-- Prove2me | solution 1 for CohCarrier.exists_H1_int_mem_parabolicHoms_not_exists_eq_smul_of_mem_parabolicHoms_of_diamondRaw_eq_of_heckeT_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/482a7888-398b-52a9-a8d9-3dd0609cc5b1

import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_PeriodMap
import Theorems.Thm_ModularCurve_Period_exists_basis_parabolicHoms_of_isAddTorsionFree
import Theorems.Thm_CohCarrier_exists_linearMap_baseChange_parabolicHoms_gammaH_bot_range_eq_parabolicHoms_of_four_le
import Theorems.Thm_CohCarrier_heckeT_comp_coeff
import Theorems.Thm_Module_Basis_exists_not_exists_eq_smul_and_forall_exists_sub_smul_eq_smul_of_mulVec_eq_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_exists_H1_int_mem_parabolicHoms_not_exists_eq_smul_of_mem_parabolicHoms_of_diamondRaw_eq_of_heckeT_eq_smul
p2m_attr_erase "instance" "ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 HeckeEis.instFiniteIndexHeckeUpper"
p2m_attr_erase "simp" "HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

namespace Ws23
namespace K4b

open CongruenceSubgroup CohCarrier
open scoped MatrixGroups TensorProduct

theorem gamma_le_gammaH (N : ℕ) (H : Subgroup (ZMod N)ˣ) :
    Gamma N ≤ GammaH N H := by
  intro A hA
  rw [Gamma_mem] at hA
  obtain ⟨-, -, h10, h11⟩ := hA
  have hA0 : A ∈ Gamma0 N := by
    rw [Gamma0_mem]
    exact h10
  rw [mem_GammaH_iff]
  refine ⟨hA0, ?_⟩
  have h1 : gamma0Units N ⟨A, hA0⟩ = 1 := by
    ext
    simp only [gamma0Units, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_one, Gamma0Map]
    exact h11
  rw [h1]
  exact one_mem H

theorem finiteIndex_gammaH (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) :
    (GammaH N H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (gamma_le_gammaH N H)

theorem trace_coe_conj (a z : SL(2, ℤ)) :
    ((a * z * a⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace =
      (z : Matrix (Fin 2) (Fin 2) ℤ).trace := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_mul_comm, ← Matrix.SpecialLinearGroup.coe_mul,
    inv_mul_cancel_left]

theorem trace_coe_inv_conj (a z : SL(2, ℤ)) :
    ((a⁻¹ * z * a : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace =
      (z : Matrix (Fin 2) (Fin 2) ℤ).trace := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_mul_comm, ← Matrix.SpecialLinearGroup.coe_mul,
    mul_inv_cancel_left]

theorem trace_mul_mul_self {A : Matrix (Fin 2) (Fin 2) ℤ} (hdet : A.det = 1)
    (B : Matrix (Fin 2) (Fin 2) ℤ) : (B * (A * A)).trace = A.trace * (B * A).trace - B.trace := by
  rw [Matrix.det_fin_two] at hdet
  simp only [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination (-(B 0 0 + B 1 1)) * hdet

theorem trace_pow_sq_eq_four {A : Matrix (Fin 2) (Fin 2) ℤ} (hdet : A.det = 1)
    (htr : A.trace ^ 2 = 4) (k : ℕ) : (A ^ k).trace ^ 2 = 4 := by
  have hrec : ∀ k : ℕ, (A ^ (k + 1 + 1)).trace = A.trace * (A ^ (k + 1)).trace - (A ^ k).trace := by
    intro k
    rw [pow_succ _ (k + 1), pow_succ _ k, mul_assoc, trace_mul_mul_self hdet]
  have h0 : (A ^ 0).trace = 2 := by
    rw [pow_zero, Matrix.trace_one, Fintype.card_fin]
    norm_num
  have hcases : A.trace = 2 ∨ A.trace = -2 := by
    have h : (A.trace - 2) * (A.trace + 2) = 0 := by linear_combination htr
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  rcases hcases with h2 | h2
  · have key : ∀ k : ℕ, (A ^ k).trace = 2 ∧ (A ^ (k + 1)).trace = 2 := by
      intro k
      induction k with
      | zero => exact ⟨h0, by rw [zero_add, pow_one, h2]⟩
      | succ k ih =>
        refine ⟨ih.2, ?_⟩
        rw [hrec, h2, ih.1, ih.2]
        norm_num
    rw [(key k).1]
    norm_num
  · have key : ∀ k : ℕ, (A ^ k).trace = 2 * (-1) ^ k ∧ (A ^ (k + 1)).trace = 2 * (-1) ^ (k + 1) := by
      intro k
      induction k with
      | zero =>
        refine ⟨?_, ?_⟩
        · rw [h0]
          norm_num
        · rw [zero_add, pow_one, h2]
          norm_num
      | succ k ih =>
        refine ⟨ih.2, ?_⟩
        rw [hrec, h2, ih.1, ih.2]
        ring
    rw [(key k).1, mul_pow, ← pow_mul, mul_comm k 2, pow_mul]
    norm_num

theorem diamondRaw_mem_parabolicHoms (N : ℕ) (H : Subgroup (ZMod N)ˣ) {R A : Type*}
    [Semiring R] [AddCommGroup A] [Module R A] (σ : Gamma0 N) {φ : H1 N H A}
    (hφ : φ ∈ ModularCurve.Period.parabolicHoms R (GammaH N H) A) :
    diamondRaw N H A σ φ ∈ ModularCurve.Period.parabolicHoms R (GammaH N H) A := by
  rw [ModularCurve.Period.mem_parabolicHoms_iff] at hφ ⊢
  intro γ hγ
  show φ (Additive.ofMul (conjHom N H σ γ)) = 0
  apply hφ
  show (((σ : SL(2, ℤ)) * (γ : SL(2, ℤ)) * (σ : SL(2, ℤ))⁻¹ : SL(2, ℤ)) :
      Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4
  rw [trace_coe_conj]
  exact hγ

theorem trace_conjL (N : ℕ) (H : Subgroup (ZMod N)ˣ) (ℓ : ℕ) (y : ↥(GammaHUpper N H ℓ)) :
    (((conjL N H ℓ y : ↥(GammaH N H)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace =
      ((((y : ↥(GammaHUpper N H ℓ)) : ↥(GammaH N H)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace := by
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two]
  simp [conjL, conjUpperMat]

theorem heckeT_mem_parabolicHoms (N : ℕ) (H : Subgroup (ZMod N)ˣ) (ℓ : ℕ) [NeZero ℓ]
    {R A : Type*} [Semiring R] [AddCommGroup A] [Module R A] {φ : H1 N H A}
    (hφ : φ ∈ ModularCurve.Period.parabolicHoms R (GammaH N H) A) :
    heckeT N H ℓ A φ ∈ ModularCurve.Period.parabolicHoms R (GammaH N H) A := by
  classical
  rw [ModularCurve.Period.mem_parabolicHoms_iff] at hφ ⊢
  intro g hg
  have key : ∀ (r : ↥(GammaH N H)) (k : ℕ),
      (((r⁻¹ * g ^ k * r : ↥(GammaH N H)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 := by
    intro r k
    have e : ((r⁻¹ * g ^ k * r : ↥(GammaH N H)) : SL(2, ℤ)) =
        (r : SL(2, ℤ))⁻¹ * (g : SL(2, ℤ)) ^ k * (r : SL(2, ℤ)) := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
    rw [e, trace_coe_inv_conj, Matrix.SpecialLinearGroup.coe_pow]
    exact trace_pow_sq_eq_four (Matrix.SpecialLinearGroup.det_coe _) hg k
  show Multiplicative.toAdd
      (MonoidHom.transfer ((AddMonoidHom.toMultiplicativeRight φ).comp (conjL N H ℓ)) g) = 0
  haveI : Fintype (Quotient (MulAction.orbitRel (Subgroup.zpowers g)
      (↥(GammaH N H) ⧸ GammaHUpper N H ℓ))) := Fintype.ofFinite _
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot, toAdd_prod]
  refine Finset.sum_eq_zero fun q _ => ?_
  simp only [MonoidHom.comp_apply, AddMonoidHom.coe_toMultiplicativeRight, Function.comp_apply,
    toAdd_ofAdd]
  apply hφ
  rw [trace_conjL]
  exact key _ _

def diamondLin (N : ℕ) (H : Subgroup (ZMod N)ˣ) (R : Type) [CommRing R] (σ : Gamma0 N) :
    H1 N H R →ₗ[R] H1 N H R where
  toFun := diamondRaw N H R σ
  map_add' := map_add _
  map_smul' c φ := by
    ext
    rfl

noncomputable def latticeMatrix (N : ℕ) (H : Subgroup (ZMod N)ˣ) {t : ℕ}
    (b : Module.Basis (Fin t) ℤ ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH N H) ℤ))
    (T : H1 N H ℤ →+ H1 N H ℤ)
    (hT : ∀ ψ ∈ ModularCurve.Period.parabolicHoms ℤ (GammaH N H) ℤ,
      T.toIntLinearMap ψ ∈ ModularCurve.Period.parabolicHoms ℤ (GammaH N H) ℤ) :
    Matrix (Fin t) (Fin t) ℤ :=
  LinearMap.toMatrix b b (T.toIntLinearMap.restrict hT)

theorem castAddHom_comp_sum_smul (N : ℕ) (H : Subgroup (ZMod N)ˣ) (κ : Type) [CommRing κ] {ι : Type*}
    (s : Finset ι) (c : ι → ℤ) (ψ : ι → H1 N H ℤ) :
    (Int.castAddHom κ).comp (∑ i ∈ s, c i • ψ i) =
      ∑ i ∈ s, (c i : κ) • (Int.castAddHom κ).comp (ψ i) := by
  refine AddMonoidHom.ext fun x => ?_
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.finsetSum_apply,
    AddMonoidHom.smul_apply, Int.coe_castAddHom, smul_eq_mul, Int.cast_sum, Int.cast_mul]

theorem toMatrix_restrict_eq_map (N : ℕ) (H : Subgroup (ZMod N)ˣ) (κ : Type) [CommRing κ] {t : ℕ}
    (b : Module.Basis (Fin t) ℤ ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH N H) ℤ))
    (bC : Module.Basis (Fin t) κ ↥(ModularCurve.Period.parabolicHoms κ (GammaH N H) κ))
    (hbC : ∀ i, (bC i : H1 N H κ) = (Int.castAddHom κ).comp (b i : H1 N H ℤ))
    (T : H1 N H ℤ →+ H1 N H ℤ)
    (hT : ∀ ψ ∈ ModularCurve.Period.parabolicHoms ℤ (GammaH N H) ℤ,
      T.toIntLinearMap ψ ∈ ModularCurve.Period.parabolicHoms ℤ (GammaH N H) ℤ)
    (TC : H1 N H κ →ₗ[κ] H1 N H κ)
    (hTC : ∀ ψ ∈ ModularCurve.Period.parabolicHoms κ (GammaH N H) κ,
      TC ψ ∈ ModularCurve.Period.parabolicHoms κ (GammaH N H) κ)
    (hnat : ∀ ψ : H1 N H ℤ, TC ((Int.castAddHom κ).comp ψ) = (Int.castAddHom κ).comp (T ψ)) :
    LinearMap.toMatrix bC bC (TC.restrict hTC) = (latticeMatrix N H b T hT).map (Int.cast : ℤ → κ) := by
  ext i j
  rw [Matrix.map_apply, LinearMap.toMatrix_apply]

  have hcolP : (T.toIntLinearMap.restrict hT) (b j) = ∑ i, latticeMatrix N H b T hT i j • b i := by
    simp_rw [latticeMatrix, LinearMap.toMatrix_apply]
    exact (b.sum_repr ((T.toIntLinearMap.restrict hT) (b j))).symm
  have hcolZ : T (b j : H1 N H ℤ) = ∑ i, latticeMatrix N H b T hT i j • (b i : H1 N H ℤ) := by
    have h2 := congrArg Subtype.val hcolP
    simpa only [LinearMap.coe_restrict_apply, AddMonoidHom.coe_toIntLinearMap, Submodule.coe_sum,
      Submodule.coe_smul] using h2

  have hcolC : TC (bC j : H1 N H κ) = ∑ i, (latticeMatrix N H b T hT i j : κ) • (bC i : H1 N H κ) := by
    rw [hbC j, hnat, hcolZ, castAddHom_comp_sum_smul N H κ]
    simp only [hbC]
  have h3 : TC.restrict hTC (bC j) = ∑ i, (latticeMatrix N H b T hT i j : κ) • bC i := by
    apply Subtype.ext
    rw [LinearMap.coe_restrict_apply, hcolC, Submodule.coe_sum]
    simp only [Submodule.coe_smul]
  rw [h3, bC.repr_sum_self]

theorem map_latticeMatrix_mulVec_repr (N : ℕ) (H : Subgroup (ZMod N)ˣ) (κ : Type) [CommRing κ] {t : ℕ}
    (b : Module.Basis (Fin t) ℤ ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH N H) ℤ))
    (bC : Module.Basis (Fin t) κ ↥(ModularCurve.Period.parabolicHoms κ (GammaH N H) κ))
    (hbC : ∀ i, (bC i : H1 N H κ) = (Int.castAddHom κ).comp (b i : H1 N H ℤ))
    (T : H1 N H ℤ →+ H1 N H ℤ)
    (hT : ∀ ψ ∈ ModularCurve.Period.parabolicHoms ℤ (GammaH N H) ℤ,
      T.toIntLinearMap ψ ∈ ModularCurve.Period.parabolicHoms ℤ (GammaH N H) ℤ)
    (TC : H1 N H κ →ₗ[κ] H1 N H κ)
    (hTC : ∀ ψ ∈ ModularCurve.Period.parabolicHoms κ (GammaH N H) κ,
      TC ψ ∈ ModularCurve.Period.parabolicHoms κ (GammaH N H) κ)
    (hnat : ∀ ψ : H1 N H ℤ, TC ((Int.castAddHom κ).comp ψ) = (Int.castAddHom κ).comp (T ψ))
    (x : ↥(ModularCurve.Period.parabolicHoms κ (GammaH N H) κ)) (a : κ)
    (hx : TC x = a • (x : H1 N H κ)) :
    ((latticeMatrix N H b T hT).map (Int.cast : ℤ → κ)).mulVec ⇑(bC.repr x) = a • ⇑(bC.repr x) := by
  rw [← toMatrix_restrict_eq_map N H κ b bC hbC T hT TC hTC hnat, LinearMap.toMatrix_mulVec_repr]
  have h : TC.restrict hTC x = a • x := by
    apply Subtype.ext
    rw [LinearMap.coe_restrict_apply, hx, Submodule.coe_smul]
  rw [h, map_smul, Finsupp.coe_smul]

noncomputable def heckeLin (N : ℕ) (H : Subgroup (ZMod N)ˣ) (R : Type) [CommRing R] (ℓ : ℕ) [NeZero ℓ] :
    H1 N H R →ₗ[R] H1 N H R where
  toFun φ := coresAdd _ (φ.comp (MonoidHom.toAdditive (conjL N H ℓ)))
  map_add' φ ψ := by
    have : (φ + ψ).comp (MonoidHom.toAdditive (conjL N H ℓ)) =
        φ.comp (MonoidHom.toAdditive (conjL N H ℓ)) + ψ.comp (MonoidHom.toAdditive (conjL N H ℓ)) := by
      ext; rfl
    rw [this, coresAdd_add]
  map_smul' r φ := by
    have : (r • φ).comp (MonoidHom.toAdditive (conjL N H ℓ)) =
        r • φ.comp (MonoidHom.toAdditive (conjL N H ℓ)) := by ext; rfl
    rw [this, coresAdd_smul]
    rfl

theorem heckeLin_apply (N : ℕ) (H : Subgroup (ZMod N)ˣ) (R : Type) [CommRing R] (ℓ : ℕ) [NeZero ℓ] (φ : H1 N H R) :
    heckeLin N H R ℓ φ = heckeT N H ℓ R φ := rfl

open ModularCurve.Period in
theorem main (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (hN : 4 ≤ N)
    (κ : Type) [Field κ] [CharP κ p]
    (v : CohCarrier.H1 N ⊥ κ) (hv : v ≠ 0)
    (hpar : v ∈ ModularCurve.Period.parabolicHoms κ (CohCarrier.GammaH N ⊥) κ)
    (hdia : ∀ σ : CongruenceSubgroup.Gamma0 N, CohCarrier.diamondRaw N ⊥ κ σ v = v)
    (E : Set ℕ) (n : ℕ → ℤ)
    (heig : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ E →
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      CohCarrier.heckeT N ⊥ ℓ κ v = (n ℓ : κ) • v) :
    ∃ φ₀ : CohCarrier.H1 N ⊥ ℤ,
      φ₀ ∈ ModularCurve.Period.parabolicHoms ℤ (CohCarrier.GammaH N ⊥) ℤ ∧
      (¬ ∃ ψ : CohCarrier.H1 N ⊥ ℤ, φ₀ = (p : ℤ) • ψ) ∧
      (∀ σ : CongruenceSubgroup.Gamma0 N, ∃ ψ : CohCarrier.H1 N ⊥ ℤ,
        CohCarrier.diamondRaw N ⊥ ℤ σ φ₀ - φ₀ = (p : ℤ) • ψ) ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ E →
        haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
        ∃ ψ : CohCarrier.H1 N ⊥ ℤ, CohCarrier.heckeT N ⊥ ℓ ℤ φ₀ - (n ℓ) • φ₀ = (p : ℤ) • ψ) := by
  classical
  haveI := finiteIndex_gammaH N (⊥ : Subgroup (ZMod N)ˣ)
  set Γ := CohCarrier.GammaH N (⊥ : Subgroup (ZMod N)ˣ) with hΓ
  set L := ModularCurve.Period.parabolicHoms ℤ Γ ℤ with hL

  obtain ⟨t, b, -⟩ := ModularCurve.Period.exists_basis_parabolicHoms_of_isAddTorsionFree.{0} Γ
  obtain ⟨ι, hι, hιinj, hιrange⟩ :=
    CohCarrier.exists_linearMap_baseChange_parabolicHoms_gammaH_bot_range_eq_parabolicHoms_of_four_le p N hN κ

  let eι : (κ ⊗[ℤ] ↥L) ≃ₗ[κ] ↥(ModularCurve.Period.parabolicHoms κ Γ κ) :=
    (LinearEquiv.ofInjective ι hιinj).trans (LinearEquiv.ofEq _ _ hιrange)
  have heι : ∀ x, ((eι x : ↥(ModularCurve.Period.parabolicHoms κ Γ κ)) : CohCarrier.H1 N ⊥ κ) = ι x := fun x => rfl
  let bκ : Module.Basis (Fin t) κ ↥(ModularCurve.Period.parabolicHoms κ Γ κ) :=
    (Algebra.TensorProduct.basis κ b).map eι
  have hbκ : ∀ i, (bκ i : CohCarrier.H1 N ⊥ κ) = (Int.castAddHom κ).comp (b i : CohCarrier.H1 N ⊥ ℤ) := by
    intro i
    show ((eι (Algebra.TensorProduct.basis κ b i) : ↥(ModularCurve.Period.parabolicHoms κ Γ κ)) : CohCarrier.H1 N ⊥ κ) = _
    rw [heι, Algebra.TensorProduct.basis_apply]
    refine AddMonoidHom.ext fun g => ?_
    have h1 := hι 1 (b i) (Additive.toMul g)
    rw [one_mul] at h1
    exact h1

  let I := {ℓ : ℕ // ℓ.Prime ∧ ℓ ∉ E} ⊕ CongruenceSubgroup.Gamma0 N
  haveI hNZ : ∀ l : {ℓ : ℕ // ℓ.Prime ∧ ℓ ∉ E}, NeZero (l : ℕ) := fun l => ⟨l.2.1.ne_zero⟩
  let Tz : I → (CohCarrier.H1 N ⊥ ℤ →+ CohCarrier.H1 N ⊥ ℤ) := fun i => match i with
    | Sum.inl l => CohCarrier.heckeT N ⊥ (l : ℕ) ℤ
    | Sum.inr σ => CohCarrier.diamondRaw N ⊥ ℤ σ
  have hTz : ∀ i, ∀ ψ ∈ L, (Tz i).toIntLinearMap ψ ∈ L := by
    rintro (l | σ) ψ hψ
    · exact heckeT_mem_parabolicHoms N ⊥ (l : ℕ) hψ
    · exact diamondRaw_mem_parabolicHoms N ⊥ σ hψ
  let Tκ : I → (CohCarrier.H1 N ⊥ κ →ₗ[κ] CohCarrier.H1 N ⊥ κ) := fun i => match i with
    | Sum.inl l => heckeLin N ⊥ κ (l : ℕ)
    | Sum.inr σ => diamondLin N ⊥ κ σ
  have hTκ : ∀ i, ∀ ψ ∈ ModularCurve.Period.parabolicHoms κ Γ κ, Tκ i ψ ∈ ModularCurve.Period.parabolicHoms κ Γ κ := by
    rintro (l | σ) ψ hψ
    · show heckeLin N ⊥ κ (l : ℕ) ψ ∈ _
      rw [heckeLin_apply]
      exact heckeT_mem_parabolicHoms N ⊥ (l : ℕ) hψ
    · exact diamondRaw_mem_parabolicHoms N ⊥ σ hψ
  have hnat : ∀ i (ψ : CohCarrier.H1 N ⊥ ℤ), Tκ i ((Int.castAddHom κ).comp ψ) = (Int.castAddHom κ).comp (Tz i ψ) := by
    rintro (l | σ) ψ
    · show heckeLin N ⊥ κ (l : ℕ) _ = _
      rw [heckeLin_apply]
      exact CohCarrier.heckeT_comp_coeff N ⊥ (l : ℕ) (Int.castAddHom κ) ψ
    · rfl

  let nI : I → ℤ := fun i => match i with
    | Sum.inl l => n l
    | Sum.inr _ => 1

  let x : ↥(ModularCurve.Period.parabolicHoms κ Γ κ) := ⟨v, hpar⟩
  have hx : ∀ i, Tκ i x = (nI i : κ) • (x : CohCarrier.H1 N ⊥ κ) := by
    rintro (l | σ)
    · show heckeLin N ⊥ κ (l : ℕ) v = ((n l : ℤ) : κ) • v
      rw [heckeLin_apply]
      exact heig l l.2.1 l.2.2
    · show CohCarrier.diamondRaw N ⊥ κ σ v = ((1 : ℤ) : κ) • v
      rw [hdia σ, Int.cast_one, one_smul]

  set m : Fin t → κ := ⇑(bκ.repr x) with hm
  have hm0 : m ≠ 0 := by
    intro h
    apply hv
    have : x = 0 := by
      apply bκ.repr.injective
      ext i
      have := congrFun h i
      simpa [hm] using this
    exact congrArg Subtype.val this
  have heigM : ∀ i, ((LinearMap.toMatrix b b ((Tz i).toIntLinearMap.restrict (hTz i))).map (Int.cast : ℤ → κ)).mulVec m =
      (nI i : κ) • m := by
    intro i
    have := map_latticeMatrix_mulVec_repr N ⊥ κ b bκ hbκ (Tz i) (hTz i) (Tκ i) (hTκ i) (hnat i) x (nI i : κ) (hx i)
    exact this

  obtain ⟨v₀, hv₀p, hv₀⟩ :=
    Module.Basis.exists_not_exists_eq_smul_and_forall_exists_sub_smul_eq_smul_of_mulVec_eq_smul b
      (fun i => (Tz i).toIntLinearMap.restrict (hTz i)) nI p κ m hm0 heigM
  refine ⟨(v₀ : CohCarrier.H1 N ⊥ ℤ), v₀.2, ?_, fun σ => ?_, fun ℓ hℓ hℓE => ?_⟩
  ·
    rintro ⟨ψ, hψ⟩
    apply hv₀p
    have hψpar : ψ ∈ L := by
      rw [hL, ModularCurve.Period.mem_parabolicHoms_iff]
      intro γ hγ
      have h := v₀.2 γ hγ
      rw [hψ, AddMonoidHom.smul_apply, smul_eq_zero] at h
      exact h.resolve_left (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
    refine ⟨⟨ψ, hψpar⟩, Subtype.ext ?_⟩
    rw [Submodule.coe_smul]
    exact hψ
  · obtain ⟨w, hw⟩ := hv₀ (Sum.inr σ)
    refine ⟨(w : CohCarrier.H1 N ⊥ ℤ), ?_⟩
    have := congrArg Subtype.val hw
    simpa [Tz, nI] using this
  · obtain ⟨w, hw⟩ := hv₀ (Sum.inl ⟨ℓ, hℓ, hℓE⟩)
    refine ⟨(w : CohCarrier.H1 N ⊥ ℤ), ?_⟩
    have := congrArg Subtype.val hw
    simpa [Tz, nI] using this

end Ws23.K4b

open scoped MatrixGroups

theorem solution
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (hN : 4 ≤ N)
    (κ : Type) [Field κ] [CharP κ p]
    (v : CohCarrier.H1 N ⊥ κ) (hv : v ≠ 0)
    (hpar : v ∈ ModularCurve.Period.parabolicHoms κ (CohCarrier.GammaH N ⊥) κ)
    (hdia : ∀ σ : CongruenceSubgroup.Gamma0 N, CohCarrier.diamondRaw N ⊥ κ σ v = v)
    (E : Set ℕ) (n : ℕ → ℤ)
    (heig : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ E →
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      CohCarrier.heckeT N ⊥ ℓ κ v = (n ℓ : κ) • v) :
    ∃ φ₀ : CohCarrier.H1 N ⊥ ℤ,
      φ₀ ∈ ModularCurve.Period.parabolicHoms ℤ (CohCarrier.GammaH N ⊥) ℤ ∧
      (¬ ∃ ψ : CohCarrier.H1 N ⊥ ℤ, φ₀ = (p : ℤ) • ψ) ∧
      (∀ σ : CongruenceSubgroup.Gamma0 N, ∃ ψ : CohCarrier.H1 N ⊥ ℤ,
        CohCarrier.diamondRaw N ⊥ ℤ σ φ₀ - φ₀ = (p : ℤ) • ψ) ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ E →
        haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
        ∃ ψ : CohCarrier.H1 N ⊥ ℤ, CohCarrier.heckeT N ⊥ ℓ ℤ φ₀ - (n ℓ) • φ₀ = (p : ℤ) • ψ) :=
  Ws23.K4b.main p N hN κ v hv hpar hdia E n heig

end S_CohCarrier_exists_H1_int_mem_parabolicHoms_not_exists_eq_smul_of_mem_parabolicHoms_of_diamondRaw_eq_of_heckeT_eq_smul
end P2MW
export P2MW.S_CohCarrier_exists_H1_int_mem_parabolicHoms_not_exists_eq_smul_of_mem_parabolicHoms_of_diamondRaw_eq_of_heckeT_eq_smul (solution)
