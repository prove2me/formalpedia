-- Prove2me | solution 1 for GaloisRep.DeformationRingData.exists_generators_maximalIdeal_card_le_finrank_span_dualNumberClasses
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/ae90d155-a60c-5795-aef1-27a92eb81074

import Mathlib
import Definitions.Def_GaloisRep_DeformationRingData
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_TangentSpace
import Theorems.Thm_IsLocalRing_exists_generators_maximalIdeal_natCard_algHom_dualNumber_eq_pow
import Theorems.Thm_GaloisRepAdic_detIsCyclotomic_baseChangeAlong
import Theorems.Thm_GaloisRepAdic_detIsCyclotomic_iff_forall_trace_dualLiftToCochain_eq_zero
import Theorems.Thm_ResidualGaloisRep_H1Pi_adZero_eq_iff_exists_dualNumber_conj
import Theorems.Thm_GaloisRep_DeformationRingData_algHom_eq_of_isEquiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_DeformationRingData_exists_generators_maximalIdeal_card_le_finrank_span_dualNumberClasses

set_option autoImplicit false

open IsLocalRing groupCohomology TrivSqZeroExt
open scoped DualNumber TensorProduct

namespace P2mK4T

section DualNumberAlgebra

variable {k : Type} [Field k]

theorem isAdicComplete_of_pow_eq_bot {A : Type} [CommRing A] (I : Ideal A) {N : ℕ}
    (hN : I ^ N = ⊥) : IsAdicComplete I A := by
  have hbot : ∀ n, N ≤ n → (I ^ n • ⊤ : Submodule A A) = ⊥ := by
    intro n hn
    have : I ^ n ≤ I ^ N := Ideal.pow_le_pow_right hn
    rw [hN, le_bot_iff] at this
    rw [this, Submodule.bot_smul]
  haveI : IsHausdorff I A := ⟨fun x hx => ?haus⟩
  haveI : IsPrecomplete I A := ⟨fun f hf => ⟨f N, fun n => ?prec⟩⟩
  · exact ⟨⟩
  case haus =>
    have h := hx N
    rw [SModEq.sub_mem, sub_zero, hbot N le_rfl] at h
    simpa using h
  case prec =>
    rcases le_total n N with hn | hn
    · exact hf hn
    · have h := hf hn
      rw [SModEq.sub_mem, hbot N le_rfl, Submodule.mem_bot, sub_eq_zero] at h
      rw [SModEq.sub_mem, ← h, sub_self]
      exact Submodule.zero_mem _

scoped instance instIsAdicCompleteDualNumber :
    IsAdicComplete (maximalIdeal k[ε]) k[ε] := by
  refine isAdicComplete_of_pow_eq_bot _ (N := 2) ?_
  rw [DualNumber.maximalIdeal_eq_span_singleton_eps, Ideal.span_singleton_pow,
    DualNumber.eps_pow_two, Ideal.span_singleton_eq_bot]

theorem residue_dualNumber_eq (x : k[ε]) : residue k[ε] x = residue k[ε] (inl x.fst) := by
  rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff,
    isUnit_iff_isUnit_fst]
  simp

theorem residue_dualNumber_mk (a b : k) : residue k[ε] (⟨a, b⟩ : k[ε]) = residue k[ε] (inl a) :=
  residue_dualNumber_eq _

end DualNumberAlgebra

section Frame

variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k V]
variable {n : Type} [Fintype n] [DecidableEq n]

noncomputable def frame (bbar : Module.Basis n k V) : Matrix n n k[ε] →* DualNumber (Module.End k V) where
  toFun X := ⟨Matrix.toLin bbar bbar (Matrix.dualNumberEquiv X).fst,
    Matrix.toLin bbar bbar (Matrix.dualNumberEquiv X).snd⟩
  map_one' := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp only [map_one, fst_one, fst_mk, Matrix.toLin_one]; rfl
    · simp only [map_one, snd_one, snd_mk, map_zero]
  map_mul' X Y := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp only [map_mul, fst_mul, fst_mk]
      rw [Matrix.toLin_mul bbar bbar bbar]; rfl
    · simp only [map_mul, DualNumber.snd_mul, snd_mk, fst_mk, map_add]
      rw [Matrix.toLin_mul bbar bbar bbar, Matrix.toLin_mul bbar bbar bbar]; rfl

noncomputable def unframe (bbar : Module.Basis n k V) : DualNumber (Module.End k V) →* Matrix n n k[ε] where
  toFun y := Matrix.dualNumberEquiv.symm ⟨LinearMap.toMatrix bbar bbar y.fst,
    LinearMap.toMatrix bbar bbar y.snd⟩
  map_one' := by
    apply Matrix.dualNumberEquiv.injective
    rw [AlgEquiv.apply_symm_apply, map_one]
    refine TrivSqZeroExt.ext ?_ ?_
    · simp only [fst_one, fst_mk]
      exact LinearMap.toMatrix_one bbar
    · simp only [snd_one, snd_mk, map_zero]
  map_mul' x y := by
    rw [← map_mul]
    congr 1
    refine TrivSqZeroExt.ext ?_ ?_
    · simp only [fst_mul, fst_mk, LinearMap.toMatrix_mul]
    · simp only [DualNumber.snd_mul, snd_mk, fst_mk, map_add, LinearMap.toMatrix_mul]

@[scoped simp] theorem frame_apply_fst (bbar : Module.Basis n k V) (X : Matrix n n k[ε]) :
    (frame bbar X).fst = Matrix.toLin bbar bbar (Matrix.dualNumberEquiv X).fst := rfl

@[scoped simp] theorem frame_apply_snd (bbar : Module.Basis n k V) (X : Matrix n n k[ε]) :
    (frame bbar X).snd = Matrix.toLin bbar bbar (Matrix.dualNumberEquiv X).snd := rfl

theorem unframe_apply (bbar : Module.Basis n k V) (y : DualNumber (Module.End k V)) :
    unframe bbar y = Matrix.dualNumberEquiv.symm ⟨LinearMap.toMatrix bbar bbar y.fst,
      LinearMap.toMatrix bbar bbar y.snd⟩ := rfl

theorem frame_unframe (bbar : Module.Basis n k V) (y : DualNumber (Module.End k V)) :
    frame bbar (unframe bbar y) = y := by
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [frame_apply_fst, unframe_apply, AlgEquiv.apply_symm_apply, fst_mk, Matrix.toLin_toMatrix]
  · rw [frame_apply_snd, unframe_apply, AlgEquiv.apply_symm_apply, snd_mk, Matrix.toLin_toMatrix]

theorem unframe_frame (bbar : Module.Basis n k V) (X : Matrix n n k[ε]) :
    unframe bbar (frame bbar X) = X := by
  rw [unframe_apply, frame_apply_fst, frame_apply_snd, LinearMap.toMatrix_toLin,
    LinearMap.toMatrix_toLin]
  exact (Matrix.dualNumberEquiv).symm_apply_apply X

theorem frame_injective (bbar : Module.Basis n k V) : Function.Injective (frame bbar) :=
  fun X Y h => by rw [← unframe_frame bbar X, h, unframe_frame]

theorem unframe_injective (bbar : Module.Basis n k V) : Function.Injective (unframe bbar) :=
  fun x y h => by rw [← frame_unframe bbar x, h, frame_unframe]

noncomputable abbrev inlMat : Matrix n n k →+* Matrix n n k[ε] := (algebraMap k k[ε]).mapMatrix

theorem inlMat_apply (P : Matrix n n k) (i j : n) : inlMat P i j = inl (P i j) := by
  simp [RingHom.mapMatrix_apply, algebraMap_eq_inl]

theorem dualNumberEquiv_symm_inl_zero (P : Matrix n n k) :
    Matrix.dualNumberEquiv.symm (⟨P, 0⟩ : DualNumber (Matrix n n k)) = inlMat P := by
  ext i j
  · rw [inlMat_apply, Matrix.dualNumberEquiv_symm_apply]; simp
  · rw [inlMat_apply, Matrix.dualNumberEquiv_symm_apply]; simp

theorem dualNumberEquiv_symm_conj (P A B Q : Matrix n n k) :
    Matrix.dualNumberEquiv.symm (⟨P * A * Q, P * B * Q⟩ : DualNumber (Matrix n n k)) =
      inlMat P * Matrix.dualNumberEquiv.symm ⟨A, B⟩ * inlMat Q := by
  rw [← dualNumberEquiv_symm_inl_zero, ← dualNumberEquiv_symm_inl_zero, ← map_mul, ← map_mul]
  congr 1
  refine TrivSqZeroExt.ext ?_ ?_
  · simp only [fst_mul, fst_mk]
  · simp only [DualNumber.snd_mul, fst_mk, snd_mk, mul_zero, zero_add, zero_mul, add_zero]

theorem unframe_basis_change (bbar bbar' : Module.Basis n k V) (y : DualNumber (Module.End k V)) :
    unframe bbar' y = inlMat (LinearMap.toMatrix bbar bbar' LinearMap.id) * unframe bbar y *
      inlMat (LinearMap.toMatrix bbar' bbar LinearMap.id) := by
  rw [unframe_apply, unframe_apply, ← dualNumberEquiv_symm_conj]
  congr 2
  · rw [← LinearMap.toMatrix_comp bbar bbar bbar', ← LinearMap.toMatrix_comp bbar' bbar bbar',
      LinearMap.id_comp, LinearMap.comp_id]
  · rw [← LinearMap.toMatrix_comp bbar bbar bbar', ← LinearMap.toMatrix_comp bbar' bbar bbar',
      LinearMap.id_comp, LinearMap.comp_id]

theorem toMatrix_id_mul_toMatrix_id (bbar bbar' : Module.Basis n k V) :
    LinearMap.toMatrix bbar bbar' LinearMap.id * LinearMap.toMatrix bbar' bbar LinearMap.id = 1 := by
  rw [← LinearMap.toMatrix_comp bbar' bbar bbar', LinearMap.id_comp, LinearMap.toMatrix_id]

end Frame

section Framed

variable {k : Type} [Field k]

local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

def IsFramedBy (ρbar : ResidualGaloisRep k) (ρA : GaloisRepAdic k[ε])
    (ρd : Γ →* (DualNumber (Module.End k ρbar.V))ˣ)
    (b : Module.Basis (Fin 2) k[ε] ρA.V) (bbar : Module.Basis (Fin 2) k ρbar.V) : Prop :=
  ∀ σ, LinearMap.toMatrix b b (ρA.ρ σ) =
    Matrix.dualNumberEquiv.symm
      ⟨LinearMap.toMatrix bbar bbar ((ρd σ : DualNumber (Module.End k ρbar.V)).fst),
        LinearMap.toMatrix bbar bbar ((ρd σ : DualNumber (Module.End k ρbar.V)).snd)⟩

variable {ρbar : ResidualGaloisRep k}

theorem IsFramedBy.toMatrix_eq {ρA : GaloisRepAdic k[ε]}
    {ρd : Γ →* (DualNumber (Module.End k ρbar.V))ˣ}
    {b : Module.Basis (Fin 2) k[ε] ρA.V} {bbar : Module.Basis (Fin 2) k ρbar.V}
    (h : IsFramedBy ρbar ρA ρd b bbar) (σ : Γ) :
    LinearMap.toMatrix b b (ρA.ρ σ) = unframe bbar (ρd σ : DualNumber (Module.End k ρbar.V)) :=
  h σ

theorem IsFramedBy.residual_isEquiv {ρA : GaloisRepAdic k[ε]}
    {ρd : Γ →* (DualNumber (Module.End k ρbar.V))ˣ}
    {b : Module.Basis (Fin 2) k[ε] ρA.V} {bbar : Module.Basis (Fin 2) k ρbar.V}
    (h : IsFramedBy ρbar ρA ρd b bbar) (hlift : IsDualLift ρbar.ρ.toHomUnits ρd) :
    ρA.residual.IsEquiv
      (ρbar.baseChangeAlong ((residue k[ε]).comp (algebraMap k k[ε]))) := by
  set χ : k →+* ResidueField k[ε] := (residue k[ε]).comp (algebraMap k k[ε]) with hχ
  letI : Algebra k (ResidueField k[ε]) := χ.toAlgebra
  let bκ : Module.Basis (Fin 2) (ResidueField k[ε]) ρA.residual.V :=
    Algebra.TensorProduct.basis (ResidueField k[ε]) b
  let cκ : Module.Basis (Fin 2) (ResidueField k[ε]) (ρbar.baseChangeAlong χ).V :=
    Algebra.TensorProduct.basis (ResidueField k[ε]) bbar
  have hres : ∀ σ : Γ, LinearMap.toMatrix bκ bκ (ρA.residual.ρ σ) =
      (LinearMap.toMatrix b b (ρA.ρ σ)).map (residue k[ε]) := fun σ => by
    have : ρA.residual.ρ σ = (ρA.ρ σ).baseChange (ResidueField k[ε]) := rfl
    rw [this, ← ResidueField.algebraMap_eq]
    exact LinearMap.toMatrix_baseChange _ _ _ _
  have hbc : ∀ σ : Γ, LinearMap.toMatrix cκ cκ ((ρbar.baseChangeAlong χ).ρ σ) =
      (LinearMap.toMatrix bbar bbar (ρbar.ρ σ)).map χ := fun σ => by
    have : (ρbar.baseChangeAlong χ).ρ σ = (ρbar.ρ σ).baseChange (ResidueField k[ε]) := rfl
    rw [this]
    exact LinearMap.toMatrix_baseChange _ _ _ _
  have hkey : ∀ σ : Γ, (LinearMap.toMatrix b b (ρA.ρ σ)).map (residue k[ε]) =
      (LinearMap.toMatrix bbar bbar (ρbar.ρ σ)).map χ := fun σ => by
    rw [h σ]
    ext i j
    rw [Matrix.map_apply, Matrix.dualNumberEquiv_symm_apply, Matrix.of_apply, Matrix.map_apply,
      hlift σ, MonoidHom.coe_toHomUnits, hχ, RingHom.comp_apply, algebraMap_eq_inl]
    exact residue_dualNumber_mk _ _
  let T : ρA.residual.V ≃ₗ[ResidueField k[ε]] (ρbar.baseChangeAlong χ).V := bκ.equiv cκ (Equiv.refl _)
  refine ⟨⟨T, fun σ x => ?_⟩⟩
  have hT : (T : ρA.residual.V →ₗ[ResidueField k[ε]] (ρbar.baseChangeAlong χ).V) ∘ₗ
      ρA.residual.ρ σ = (ρbar.baseChangeAlong χ).ρ σ ∘ₗ
        (T : ρA.residual.V →ₗ[ResidueField k[ε]] (ρbar.baseChangeAlong χ).V) := by
    apply (LinearMap.toMatrix bκ cκ).injective
    rw [LinearMap.toMatrix_comp bκ bκ cκ, LinearMap.toMatrix_comp bκ cκ cκ,
      LinearMap.toMatrix_basis_equiv, hres, hbc, hkey, Matrix.one_mul, Matrix.mul_one]
  exact LinearMap.congr_fun hT x

theorem IsFramedBy.isEquiv_of_conj {ρA ρA' : GaloisRepAdic k[ε]}
    {ρd ρd' : Γ →* (DualNumber (Module.End k ρbar.V))ˣ}
    {b : Module.Basis (Fin 2) k[ε] ρA.V} {b' : Module.Basis (Fin 2) k[ε] ρA'.V}
    {bbar bbar' : Module.Basis (Fin 2) k ρbar.V}
    (h : IsFramedBy ρbar ρA ρd b bbar) (h' : IsFramedBy ρbar ρA' ρd' b' bbar')
    (w : (DualNumber (Module.End k ρbar.V))ˣ) (hw : ∀ σ, ρd' σ = w * ρd σ * w⁻¹) :
    ρA.IsEquiv ρA' := by

  set P : Matrix (Fin 2) (Fin 2) k[ε] := inlMat (LinearMap.toMatrix bbar bbar' LinearMap.id) with hP
  set Q : Matrix (Fin 2) (Fin 2) k[ε] := inlMat (LinearMap.toMatrix bbar' bbar LinearMap.id) with hQ
  have hPQ : P * Q = 1 := by rw [hP, hQ, ← map_mul, toMatrix_id_mul_toMatrix_id, map_one]
  have hQP : Q * P = 1 := by rw [hP, hQ, ← map_mul, toMatrix_id_mul_toMatrix_id, map_one]

  set W : Matrix (Fin 2) (Fin 2) k[ε] := unframe bbar (w : DualNumber (Module.End k ρbar.V)) with hW
  set W' : Matrix (Fin 2) (Fin 2) k[ε] :=
    unframe bbar ((w⁻¹ : (DualNumber (Module.End k ρbar.V))ˣ) : DualNumber (Module.End k ρbar.V))
    with hW'
  have hWW' : W * W' = 1 := by rw [hW, hW', ← map_mul, Units.mul_inv, map_one]
  have hW'W : W' * W = 1 := by rw [hW, hW', ← map_mul, Units.inv_mul, map_one]
  have h1 : P * W * (W' * Q) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc W, hWW', Matrix.one_mul, hPQ]
  have h2 : W' * Q * (P * W) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Q, hQP, Matrix.one_mul, hW'W]

  have hint : ∀ σ : Γ, P * W * LinearMap.toMatrix b b (ρA.ρ σ) =
      LinearMap.toMatrix b' b' (ρA'.ρ σ) * (P * W) := fun σ => by
    rw [h.toMatrix_eq, h'.toMatrix_eq, unframe_basis_change bbar bbar', hw σ, Units.val_mul,
      Units.val_mul, map_mul, map_mul, ← hP, ← hQ, ← hW, ← hW']
    symm
    calc P * (W * unframe bbar (ρd σ : DualNumber (Module.End k ρbar.V)) * W') * Q * (P * W)
        = P * (W * unframe bbar (ρd σ : DualNumber (Module.End k ρbar.V)) * W') * (Q * P) * W := by
          simp only [Matrix.mul_assoc]
      _ = P * (W * unframe bbar (ρd σ : DualNumber (Module.End k ρbar.V)) * (W' * W)) := by
          rw [hQP, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = P * W * unframe bbar (ρd σ : DualNumber (Module.End k ρbar.V)) := by
          rw [hW'W, Matrix.mul_one, Matrix.mul_assoc]

  refine ⟨⟨LinearEquiv.ofLinear (Matrix.toLin b b' (P * W)) (Matrix.toLin b' b (W' * Q)) ?_ ?_,
    fun σ x => ?_⟩⟩
  · rw [← Matrix.toLin_mul b' b b', h1, Matrix.toLin_one]
  · rw [← Matrix.toLin_mul b b' b, h2, Matrix.toLin_one]
  · have hT : (Matrix.toLin b b' (P * W)) ∘ₗ ρA.ρ σ = ρA'.ρ σ ∘ₗ Matrix.toLin b b' (P * W) := by
      apply (LinearMap.toMatrix b b').injective
      rw [LinearMap.toMatrix_comp b b b', LinearMap.toMatrix_comp b b' b', LinearMap.toMatrix_toLin,
        hint]
    exact LinearMap.congr_fun hT x

theorem IsFramedBy.exists_conj_of_isEquiv {ρA ρA' : GaloisRepAdic k[ε]}
    {ρd ρd' : Γ →* (DualNumber (Module.End k ρbar.V))ˣ}
    {b : Module.Basis (Fin 2) k[ε] ρA.V} {b' : Module.Basis (Fin 2) k[ε] ρA'.V}
    {bbar bbar' : Module.Basis (Fin 2) k ρbar.V}
    (h : IsFramedBy ρbar ρA ρd b bbar) (h' : IsFramedBy ρbar ρA' ρd' b' bbar')
    (he : ρA.IsEquiv ρA') :
    ∃ w : (DualNumber (Module.End k ρbar.V))ˣ, ∀ σ, ρd' σ = w * ρd σ * w⁻¹ := by
  obtain ⟨L⟩ := he
  set P : Matrix (Fin 2) (Fin 2) k[ε] := inlMat (LinearMap.toMatrix bbar bbar' LinearMap.id) with hP
  set Q : Matrix (Fin 2) (Fin 2) k[ε] := inlMat (LinearMap.toMatrix bbar' bbar LinearMap.id) with hQ
  have hPQ : P * Q = 1 := by rw [hP, hQ, ← map_mul, toMatrix_id_mul_toMatrix_id, map_one]
  have hQP : Q * P = 1 := by rw [hP, hQ, ← map_mul, toMatrix_id_mul_toMatrix_id, map_one]
  set M : Matrix (Fin 2) (Fin 2) k[ε] :=
    LinearMap.toMatrix b b' (L.toLinearEquiv : ρA.V →ₗ[k[ε]] ρA'.V) with hM
  set M' : Matrix (Fin 2) (Fin 2) k[ε] :=
    LinearMap.toMatrix b' b (L.toLinearEquiv.symm : ρA'.V →ₗ[k[ε]] ρA.V) with hM'
  have hMM' : M * M' = 1 := by
    rw [hM, hM', ← LinearMap.toMatrix_comp b' b b', ← LinearMap.toMatrix_id b']
    congr 1
    exact LinearMap.ext fun x => L.toLinearEquiv.apply_symm_apply x
  have hM'M : M' * M = 1 := by
    rw [hM, hM', ← LinearMap.toMatrix_comp b b' b, ← LinearMap.toMatrix_id b]
    congr 1
    exact LinearMap.ext fun x => L.toLinearEquiv.symm_apply_apply x

  have hint : ∀ σ : Γ, M * LinearMap.toMatrix b b (ρA.ρ σ) = LinearMap.toMatrix b' b' (ρA'.ρ σ) * M :=
    fun σ => by
    rw [hM, ← LinearMap.toMatrix_comp b b b', ← LinearMap.toMatrix_comp b b' b']
    congr 1
    exact LinearMap.ext fun x => L.map_apply σ x

  set X : Matrix (Fin 2) (Fin 2) k[ε] := Q * M with hX
  set X' : Matrix (Fin 2) (Fin 2) k[ε] := M' * P with hX'
  have hXX' : X * X' = 1 := by
    rw [hX, hX', Matrix.mul_assoc, ← Matrix.mul_assoc M, hMM', Matrix.one_mul, hQP]
  have hX'X : X' * X = 1 := by
    rw [hX, hX', Matrix.mul_assoc, ← Matrix.mul_assoc P, hPQ, Matrix.one_mul, hM'M]
  let w : (DualNumber (Module.End k ρbar.V))ˣ :=
    ⟨frame bbar X, frame bbar X', by rw [← map_mul, hXX', map_one], by rw [← map_mul, hX'X, map_one]⟩
  refine ⟨w, fun σ => Units.ext ?_⟩

  have hmat : unframe bbar (ρd' σ : DualNumber (Module.End k ρbar.V)) =
      X * unframe bbar (ρd σ : DualNumber (Module.End k ρbar.V)) * X' := by
    have h1 : X * unframe bbar (ρd σ : DualNumber (Module.End k ρbar.V)) =
        unframe bbar (ρd' σ : DualNumber (Module.End k ρbar.V)) * X := by
      rw [← h.toMatrix_eq, hX, Matrix.mul_assoc, hint σ, h'.toMatrix_eq,
        unframe_basis_change bbar bbar', ← hP, ← hQ]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Q P, hQP, Matrix.one_mul]
    rw [h1, Matrix.mul_assoc, hXX', Matrix.mul_one]
  rw [Units.val_mul, Units.val_mul, ← frame_unframe bbar (ρd' σ : DualNumber (Module.End k ρbar.V)),
    hmat, map_mul, map_mul, frame_unframe]
  rfl

end Framed

section Universal

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
variable {ρbar : ResidualGaloisRep (ResidueField 𝒪)}
variable {𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}

local notation "𝕜" => ResidueField 𝒪
local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem toMatrix_basis_map {ι K W : Type} [Fintype ι] [DecidableEq ι] [CommRing K] [AddCommGroup W]
    [Module K W] (b₀ : Module.Basis ι K W) (g : W ≃ₗ[K] W) (f : W →ₗ[K] W) :
    LinearMap.toMatrix (b₀.map g) (b₀.map g) f =
      LinearMap.toMatrix b₀ b₀ ((g.symm : W →ₗ[K] W) ∘ₗ f ∘ₗ (g : W →ₗ[K] W)) := by
  ext i j
  simp [LinearMap.toMatrix_apply, Module.Basis.map_apply, Module.Basis.map_repr]

variable (D : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟)

noncomputable def ebasis : Module.Basis (Fin 2) D.R D.ρ.V :=
  Module.finBasisOfFinrankEq D.R D.ρ.V D.ρ.finrank_eq

noncomputable def matRep (σ : Γ) : Matrix (Fin 2) (Fin 2) D.R :=
  LinearMap.toMatrix (ebasis D) (ebasis D) (D.ρ.ρ σ)

theorem matRep_mul (σ τ : Γ) : matRep D (σ * τ) = matRep D σ * matRep D τ := by
  rw [matRep, map_mul, LinearMap.toMatrix_mul]; rfl

theorem matRep_one : matRep D 1 = 1 := by
  rw [matRep, map_one]; exact LinearMap.toMatrix_one _

noncomputable def ψ : 𝕜 →+* ResidueField D.R := ResidueField.map (algebraMap 𝒪 D.R)

theorem ψ_residue (x : 𝒪) : ψ D (residue 𝒪 x) = residue D.R (algebraMap 𝒪 D.R x) :=
  ResidueField.map_residue _ _

theorem ψ_bijective : Function.Bijective (ψ D) := by
  refine ⟨(ψ D).injective, fun z => ?_⟩
  obtain ⟨x, hx⟩ := D.residue_surjective z
  exact ⟨residue 𝒪 x, by rw [ψ_residue]; exact hx⟩

noncomputable def θ : ResidueField D.R ≃+* 𝕜 :=
  (RingEquiv.ofBijective (ψ D) (ψ_bijective D)).symm

theorem θ_ψ (y : 𝕜) : θ D (ψ D y) = y :=
  (RingEquiv.ofBijective (ψ D) (ψ_bijective D)).symm_apply_apply y

noncomputable def θres : D.R →+* 𝕜 := (θ D).toRingHom.comp (residue D.R)

theorem θres_apply (r : D.R) : θres D r = θ D (residue D.R r) := rfl

theorem exists_bbar : ∃ bbar : Module.Basis (Fin 2) 𝕜 ρbar.V,
    ∀ σ : Γ, (matRep D σ).map (θres D) = LinearMap.toMatrix bbar bbar (ρbar.ρ σ) := by
  obtain ⟨T⟩ := D.residual_isEquiv
  letI : Algebra 𝕜 (ResidueField D.R) := (ResidueField.map (algebraMap 𝒪 D.R)).toAlgebra
  let bbar₀ : Module.Basis (Fin 2) 𝕜 ρbar.V := Module.finBasisOfFinrankEq 𝕜 ρbar.V ρbar.finrank_eq
  let eκ : Module.Basis (Fin 2) (ResidueField D.R) D.ρ.residual.V :=
    Algebra.TensorProduct.basis (ResidueField D.R) (ebasis D)
  let cκ : Module.Basis (Fin 2) (ResidueField D.R)
      (ρbar.baseChangeAlong (ResidueField.map (algebraMap 𝒪 D.R))).V :=
    Algebra.TensorProduct.basis (ResidueField D.R) bbar₀
  have hres : ∀ σ : Γ, LinearMap.toMatrix eκ eκ (D.ρ.residual.ρ σ) =
      (matRep D σ).map (residue D.R) := fun σ => by
    have : D.ρ.residual.ρ σ = (D.ρ.ρ σ).baseChange (ResidueField D.R) := rfl
    rw [this, matRep, ← ResidueField.algebraMap_eq]
    exact LinearMap.toMatrix_baseChange _ _ _ _
  have hbc : ∀ σ : Γ,
      LinearMap.toMatrix cκ cκ ((ρbar.baseChangeAlong (ResidueField.map (algebraMap 𝒪 D.R))).ρ σ) =
        (LinearMap.toMatrix bbar₀ bbar₀ (ρbar.ρ σ)).map (ψ D) := fun σ => by
    have : (ρbar.baseChangeAlong (ResidueField.map (algebraMap 𝒪 D.R))).ρ σ =
        (ρbar.ρ σ).baseChange (ResidueField D.R) := rfl
    rw [this]
    exact LinearMap.toMatrix_baseChange _ _ _ _
  set Pκ : Matrix (Fin 2) (Fin 2) (ResidueField D.R) :=
    LinearMap.toMatrix eκ cκ (T.toLinearEquiv : _ →ₗ[ResidueField D.R] _) with hPκ
  set Pκ' : Matrix (Fin 2) (Fin 2) (ResidueField D.R) :=
    LinearMap.toMatrix cκ eκ (T.toLinearEquiv.symm : _ →ₗ[ResidueField D.R] _) with hPκ'
  have hPP' : Pκ * Pκ' = 1 := by
    rw [hPκ, hPκ', ← LinearMap.toMatrix_comp cκ eκ cκ, ← LinearMap.toMatrix_id cκ]
    congr 1
    exact LinearMap.ext fun x => T.toLinearEquiv.apply_symm_apply x
  have hP'P : Pκ' * Pκ = 1 := by
    rw [hPκ, hPκ', ← LinearMap.toMatrix_comp eκ cκ eκ, ← LinearMap.toMatrix_id eκ]
    congr 1
    exact LinearMap.ext fun x => T.toLinearEquiv.symm_apply_apply x
  have hintκ : ∀ σ : Γ, Pκ * (matRep D σ).map (residue D.R) =
      (LinearMap.toMatrix bbar₀ bbar₀ (ρbar.ρ σ)).map (ψ D) * Pκ := fun σ => by
    rw [← hres, ← hbc, hPκ, ← LinearMap.toMatrix_comp eκ eκ cκ, ← LinearMap.toMatrix_comp eκ cκ cκ]
    congr 1
    exact LinearMap.ext fun x => T.map_apply σ x

  set P₀ : Matrix (Fin 2) (Fin 2) 𝕜 := Pκ.map (θ D) with hP₀
  set P₀' : Matrix (Fin 2) (Fin 2) 𝕜 := Pκ'.map (θ D) with hP₀'
  have hmap1 : (1 : Matrix (Fin 2) (Fin 2) (ResidueField D.R)).map (θ D) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have hP₀P₀' : P₀ * P₀' = 1 := by rw [hP₀, hP₀', ← Matrix.map_mul, hPP', hmap1]
  have hP₀'P₀ : P₀' * P₀ = 1 := by rw [hP₀, hP₀', ← Matrix.map_mul, hP'P, hmap1]
  have hθψ : ((θ D : ResidueField D.R → 𝕜) ∘ (ψ D : 𝕜 → ResidueField D.R)) = id := funext (θ_ψ D)
  have hint₀ : ∀ σ : Γ, P₀ * (matRep D σ).map (θres D) =
      LinearMap.toMatrix bbar₀ bbar₀ (ρbar.ρ σ) * P₀ := fun σ => by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) (ResidueField D.R) => M.map (θ D)) (hintκ σ)
    simp only [Matrix.map_mul, Matrix.map_map, hθψ, Matrix.map_id] at h
    rw [hP₀]
    exact h

  let g : ρbar.V ≃ₗ[𝕜] ρbar.V :=
    LinearEquiv.ofLinear (Matrix.toLin bbar₀ bbar₀ P₀) (Matrix.toLin bbar₀ bbar₀ P₀')
      (by rw [← Matrix.toLin_mul bbar₀ bbar₀ bbar₀, hP₀P₀', Matrix.toLin_one])
      (by rw [← Matrix.toLin_mul bbar₀ bbar₀ bbar₀, hP₀'P₀, Matrix.toLin_one])
  refine ⟨bbar₀.map g, fun σ => ?_⟩
  rw [toMatrix_basis_map, LinearMap.toMatrix_comp bbar₀ bbar₀ bbar₀,
    LinearMap.toMatrix_comp bbar₀ bbar₀ bbar₀, LinearEquiv.ofLinear_symm_toLinearMap,
    LinearEquiv.ofLinear_toLinearMap, LinearMap.toMatrix_toLin, LinearMap.toMatrix_toLin,
    ← hint₀, ← Matrix.mul_assoc, hP₀'P₀, Matrix.one_mul]

noncomputable def bbarD : Module.Basis (Fin 2) 𝕜 ρbar.V := (exists_bbar D).choose

theorem bbarD_spec (σ : Γ) :
    (matRep D σ).map (θres D) = LinearMap.toMatrix (bbarD D) (bbarD D) (ρbar.ρ σ) :=
  (exists_bbar D).choose_spec σ

variable {D}

def CompatO (φ : D.R →+* 𝕜[ε]) : Prop := ∀ x : 𝒪, φ (algebraMap 𝒪 D.R x) = inl (residue 𝒪 x)

theorem fst_apply_eq {φ : D.R →+* 𝕜[ε]} (hφ : IsLocalHom φ) (hφ𝒪 : CompatO φ) (r : D.R) :
    (φ r).fst = θres D r := by
  let f : D.R →+* 𝕜 := (TrivSqZeroExt.fstHom 𝕜 𝕜 𝕜).toRingHom.comp φ
  have hf : ∀ r, f r = (φ r).fst := fun r => rfl
  haveI : IsLocalHom f := ⟨fun r hr => by
    rw [hf] at hr
    exact hφ.map_nonunit r (isUnit_iff_isUnit_fst.mpr hr)⟩
  have hlift : ResidueField.lift f = (θ D).toRingHom := by
    refine RingHom.ext fun z => ?_
    obtain ⟨x, hx⟩ := D.residue_surjective z
    simp only [Function.comp_apply] at hx
    rw [← hx, ResidueField.lift_residue_apply, hf, hφ𝒪, fst_inl]
    change residue 𝒪 x = θ D (residue D.R (algebraMap 𝒪 D.R x))
    rw [← ψ_residue, θ_ψ]
  rw [← hf, ← ResidueField.lift_residue_apply f r, hlift]
  rfl

variable (D)

noncomputable def bφ (φ : D.R →+* 𝕜[ε]) (hφ : IsLocalHom φ) :
    Module.Basis (Fin 2) 𝕜[ε] (D.ρ.baseChangeAlong φ hφ).V :=
  letI : Algebra D.R 𝕜[ε] := φ.toAlgebra
  Algebra.TensorProduct.basis 𝕜[ε] (ebasis D)

theorem toMatrix_bφ (φ : D.R →+* 𝕜[ε]) (hφ : IsLocalHom φ) (σ : Γ) :
    LinearMap.toMatrix (bφ D φ hφ) (bφ D φ hφ) ((D.ρ.baseChangeAlong φ hφ).ρ σ) =
      (matRep D σ).map φ := by
  letI : Algebra D.R 𝕜[ε] := φ.toAlgebra
  have : (D.ρ.baseChangeAlong φ hφ).ρ σ = (D.ρ.ρ σ).baseChange 𝕜[ε] := rfl
  rw [this]
  exact LinearMap.toMatrix_baseChange _ _ _ _

noncomputable def dualFormFun (φ : D.R →+* 𝕜[ε]) : Γ →* DualNumber (Module.End 𝕜 ρbar.V) where
  toFun σ := frame (bbarD D) ((matRep D σ).map φ)
  map_one' := by rw [matRep_one, Matrix.map_one φ (map_zero φ) (map_one φ), map_one]
  map_mul' σ τ := by rw [matRep_mul, Matrix.map_mul, map_mul]

noncomputable def dualForm (φ : D.R →+* 𝕜[ε]) : Γ →* (DualNumber (Module.End 𝕜 ρbar.V))ˣ :=
  (dualFormFun D φ).toHomUnits

theorem dualForm_apply (φ : D.R →+* 𝕜[ε]) (σ : Γ) :
    (dualForm D φ σ : DualNumber (Module.End 𝕜 ρbar.V)) = frame (bbarD D) ((matRep D σ).map φ) :=
  MonoidHom.coe_toHomUnits _ _

theorem dualNumberEquiv_map_fst (X : Matrix (Fin 2) (Fin 2) D.R) (φ : D.R →+* 𝕜[ε]) :
    (Matrix.dualNumberEquiv (X.map φ)).fst = X.map (fun r => (φ r).fst) := by
  ext i j
  simp [Matrix.dualNumberEquiv_apply]

theorem isDualLift_dualForm {φ : D.R →+* 𝕜[ε]} (hφ : IsLocalHom φ) (hφ𝒪 : CompatO φ) :
    IsDualLift ρbar.ρ.toHomUnits (dualForm D φ) := fun σ => by
  rw [dualForm_apply, frame_apply_fst, dualNumberEquiv_map_fst, MonoidHom.coe_toHomUnits]
  have : (matRep D σ).map (fun r => (φ r).fst) = (matRep D σ).map (θres D) := by
    congr 1
    funext r
    exact fst_apply_eq hφ hφ𝒪 r
  rw [this, bbarD_spec, Matrix.toLin_toMatrix]

theorem isFramedBy_dualForm (φ : D.R →+* 𝕜[ε]) (hφ : IsLocalHom φ) :
    IsFramedBy ρbar (D.ρ.baseChangeAlong φ hφ) (dualForm D φ) (bφ D φ hφ) (bbarD D) := fun σ => by
  rw [toMatrix_bφ, ← unframe_apply, dualForm_apply, unframe_frame]

end Universal

section OddChar

theorem residue_natCast_eq_zero {A : Type} [CommRing A] [IsLocalRing A] (p : ℕ)
    (hp : (p : A) ∈ maximalIdeal A) : (p : ResidueField A) = 0 := by
  have h := (residue_eq_zero_iff (p : A)).mpr hp
  rwa [map_natCast] at h

theorem isUnit_two {K : Type} [Field K] (p : ℕ) [Fact p.Prime] (hp : (p : K) = 0) (hp2 : p ≠ 2) :
    IsUnit (2 : K) := by
  rw [isUnit_iff_ne_zero]
  intro h2
  have hprime : p.Prime := Fact.out
  have hchar : ringChar K = p := by
    have hdvd : ringChar K ∣ p := (ringChar.spec K p).mp hp
    rcases (Nat.dvd_prime hprime).mp hdvd with h | h
    · exact absurd h CharP.ringChar_ne_one
    · exact h
  have h2' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h2
  have hdvd2 : p ∣ 2 := hchar ▸ (ringChar.spec K 2).mp h2'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).mp hdvd2)

end OddChar

section Classes

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
variable {ρbar : ResidualGaloisRep (ResidueField 𝒪)}
variable {𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}

local notation "𝕜" => ResidueField 𝒪
local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

variable (p : ℕ) [Fact p.Prime]
variable (D : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟)

theorem trace_dualForm_eq_zero (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)
    (hdet : (GaloisRepAdic.ofResidualGaloisRep ρbar).DetIsCyclotomic p) (hdetR : D.ρ.DetIsCyclotomic p)
    {φ : D.R →+* 𝕜[ε]} (hφ : IsLocalHom φ) (hφ𝒪 : CompatO φ) (σ : Γ) :
    LinearMap.trace 𝕜 ρbar.V (dualLiftToCochain ρbar.ρ.toHomUnits (dualForm D φ) σ) = 0 := by
  have hp : (p : 𝕜) = 0 := residue_natCast_eq_zero p hp𝒪
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hdet' : ∀ (σ : Γ) (a : ℕ), (∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 → σ μ = μ ^ a) →
      LinearMap.det (ρbar.ρ σ) = (a : 𝕜) := fun σ a ha => by
    have h := hdet.2 1 σ a (fun μ hμ => ha μ (by rwa [pow_one] at hμ))
    rw [pow_one, hp, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.mem_bot, sub_eq_zero] at h
    exact h
  have hcyc : (D.ρ.baseChangeAlong φ hφ).DetIsCyclotomic p :=
    GaloisRepAdic.detIsCyclotomic_baseChangeAlong φ hφ D.ρ hdetR
  exact (GaloisRepAdic.detIsCyclotomic_iff_forall_trace_dualLiftToCochain_eq_zero 𝕜 ρbar p hp hp0
    hdet' (D.ρ.baseChangeAlong φ hφ) (dualForm D φ) (isDualLift_dualForm D hφ hφ𝒪) (bφ D φ hφ)
    (bbarD D) (isFramedBy_dualForm D φ hφ)).mp hcyc σ

noncomputable def cocycleOf (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)
    (hdet : (GaloisRepAdic.ofResidualGaloisRep ρbar).DetIsCyclotomic p) (hdetR : D.ρ.DetIsCyclotomic p)
    {φ : D.R →+* 𝕜[ε]} (hφ : IsLocalHom φ) (hφ𝒪 : CompatO φ) : cocycles₁ ρbar.adZero :=
  ⟨fun σ => ⟨dualLiftToCochain ρbar.ρ.toHomUnits (dualForm D φ) σ,
      LinearMap.mem_ker.mpr (trace_dualForm_eq_zero p D hp𝒪 hdet hdetR hφ hφ𝒪 σ)⟩, by
    rw [mem_cocycles₁_iff]
    intro g h
    apply Subtype.ext
    have hc := (mem_cocycles₁_iff (A := adjointRep 𝕜 ρbar.ρ.toHomUnits) _).mp
      (dualLiftToCochain_mem_cocycles₁ (k := 𝕜) (isDualLift_dualForm D hφ hφ𝒪)) g h
    rw [adjointRep_ρ_apply] at hc
    exact hc⟩

theorem cocycleOf_apply (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)
    (hdet : (GaloisRepAdic.ofResidualGaloisRep ρbar).DetIsCyclotomic p) (hdetR : D.ρ.DetIsCyclotomic p)
    {φ : D.R →+* 𝕜[ε]} (hφ : IsLocalHom φ) (hφ𝒪 : CompatO φ) (σ : Γ) :
    ((cocycleOf p D hp𝒪 hdet hdetR hφ hφ𝒪 : Γ → ↥(LinearMap.ker (LinearMap.trace 𝕜 ρbar.V))) σ :
        Module.End 𝕜 ρbar.V) = dualLiftToCochain ρbar.ρ.toHomUnits (dualForm D φ) σ :=
  rfl

end Classes

section OAlgebra

variable {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]

local notation "𝕜" => ResidueField 𝒪

@[reducible] noncomputable def algOK (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪] :
    Algebra 𝒪 (DualNumber (ResidueField 𝒪)) :=
  ((algebraMap (ResidueField 𝒪) (DualNumber (ResidueField 𝒪))).comp
    (algebraMap 𝒪 (ResidueField 𝒪))).toAlgebra

attribute [local instance 10000] algOK

theorem algebraMap_OK_apply (x : 𝒪) : algebraMap 𝒪 𝕜[ε] x = inl (residue 𝒪 x) := by
  show ((algebraMap 𝕜 𝕜[ε]).comp (algebraMap 𝒪 𝕜)) x = inl (residue 𝒪 x)
  rw [RingHom.comp_apply, algebraMap_eq_inl]
  rfl

scoped instance isLocalHom_algebraMap_OK : IsLocalHom (algebraMap 𝒪 𝕜[ε]) := ⟨fun x hx => by
  rw [algebraMap_OK_apply, isUnit_iff_isUnit_fst, fst_inl] at hx
  by_contra h
  exact hx.ne_zero ((residue_eq_zero_iff x).mpr h)⟩

theorem residue_comp_algebraMap_OK_surjective :
    Function.Surjective (residue 𝕜[ε] ∘ algebraMap 𝒪 𝕜[ε]) := fun z => by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (I := maximalIdeal 𝒪) y.fst
  refine ⟨x, ?_⟩
  simp only [Function.comp_apply, algebraMap_OK_apply]
  change residue 𝕜[ε] (inl (residue 𝒪 x)) = residue 𝕜[ε] y
  rw [residue_dualNumber_eq y]
  congr 2

theorem residueField_map_algebraMap_OK :
    ResidueField.map (algebraMap 𝒪 𝕜[ε]) = (residue 𝕜[ε]).comp (algebraMap 𝕜 𝕜[ε]) := by
  refine RingHom.ext fun z => ?_
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  change ResidueField.map (algebraMap 𝒪 𝕜[ε]) (residue 𝒪 x) = residue 𝕜[ε] (algebraMap 𝕜 𝕜[ε] (residue 𝒪 x))
  rw [ResidueField.map_residue, algebraMap_OK_apply, algebraMap_eq_inl]

end OAlgebra

section Assembly

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
variable {ρbar : ResidualGaloisRep (ResidueField 𝒪)}
variable {𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}

local notation "𝕜" => ResidueField 𝒪
local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

attribute [local instance 10000] algOK

variable (D : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟)

theorem compatO_algHom (φ : D.R →ₐ[𝒪] 𝕜[ε]) : CompatO (φ : D.R →+* 𝕜[ε]) := fun x => by
  rw [RingHom.coe_coe, φ.commutes, algebraMap_OK_apply]

theorem isLocalHom_algHom (φ : D.R →ₐ[𝒪] 𝕜[ε]) : IsLocalHom (φ : D.R →+* 𝕜[ε]) := by
  let f : D.R →+* 𝕜 := (TrivSqZeroExt.fstHom 𝕜 𝕜 𝕜).toRingHom.comp (φ : D.R →+* 𝕜[ε])
  have hf : ∀ r, f r = (φ r).fst := fun r => rfl
  have hfs : Function.Surjective f := fun y => by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨algebraMap 𝒪 D.R x, ?_⟩
    rw [hf, φ.commutes, algebraMap_OK_apply, fst_inl]
    rfl
  have hker : RingHom.ker f = maximalIdeal D.R :=
    eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective f hfs)
  refine ⟨fun r hr => ?_⟩
  by_contra hru
  have hmem : r ∈ RingHom.ker f := by rw [hker]; exact hru
  rw [RingHom.mem_ker, hf] at hmem
  rw [RingHom.coe_coe, isUnit_iff_isUnit_fst, hmem] at hr
  exact not_isUnit_zero hr

variable (ρbar 𝒟) in

def Sset : Set (H1 ρbar.adZero) :=
  {x : H1 ρbar.adZero |
    ∃ c : cocycles₁ ρbar.adZero, H1π ρbar.adZero c = x ∧
    ∃ ρA : GaloisRepAdic (DualNumber (ResidueField 𝒪)),
      𝒟 ρA ∧
    ∃ ρd : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →*
        (DualNumber (Module.End (ResidueField 𝒪) ρbar.V))ˣ,
      IsDualLift ρbar.ρ.toHomUnits ρd ∧
      (∀ σ, ((c : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →
          ↥(LinearMap.ker (LinearMap.trace (ResidueField 𝒪) ρbar.V))) σ :
            Module.End (ResidueField 𝒪) ρbar.V) =
        dualLiftToCochain ρbar.ρ.toHomUnits ρd σ) ∧
      ∃ (b : Module.Basis (Fin 2) (DualNumber (ResidueField 𝒪)) ρA.V)
        (bbar : Module.Basis (Fin 2) (ResidueField 𝒪) ρbar.V),
        ∀ σ, LinearMap.toMatrix b b (ρA.ρ σ) =
          Matrix.dualNumberEquiv.symm
            ⟨LinearMap.toMatrix bbar bbar
                ((ρd σ : DualNumber (Module.End (ResidueField 𝒪) ρbar.V)).fst),
              LinearMap.toMatrix bbar bbar
                ((ρd σ : DualNumber (Module.End (ResidueField 𝒪) ρbar.V)).snd)⟩}

variable (p : ℕ) [Fact p.Prime] (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)
  (hdet : (GaloisRepAdic.ofResidualGaloisRep ρbar).DetIsCyclotomic p) (hdetR : D.ρ.DetIsCyclotomic p)
  (h𝒟 : ∀ (φ : D.R →ₐ[𝒪] DualNumber (ResidueField 𝒪))
      (hφ : IsLocalHom (φ : D.R →+* DualNumber (ResidueField 𝒪))),
      𝒟 (D.ρ.baseChangeAlong (φ : D.R →+* DualNumber (ResidueField 𝒪)) hφ))

noncomputable def classOf (φ : D.R →ₐ[𝒪] 𝕜[ε]) : cocycles₁ ρbar.adZero :=
  cocycleOf p D hp𝒪 hdet hdetR (isLocalHom_algHom D φ) (compatO_algHom D φ)

include h𝒟 in
theorem classOf_mem (φ : D.R →ₐ[𝒪] 𝕜[ε]) :
    H1π ρbar.adZero (classOf D p hp𝒪 hdet hdetR φ) ∈ Sset ρbar 𝒟 :=
  ⟨classOf D p hp𝒪 hdet hdetR φ, rfl, D.ρ.baseChangeAlong _ (isLocalHom_algHom D φ), h𝒟 φ _,
    dualForm D φ, isDualLift_dualForm D (isLocalHom_algHom D φ) (compatO_algHom D φ), fun _ => rfl,
    bφ D φ (isLocalHom_algHom D φ), bbarD D, isFramedBy_dualForm D φ (isLocalHom_algHom D φ)⟩

noncomputable def Φ (φ : D.R →ₐ[𝒪] 𝕜[ε]) : Submodule.span 𝕜 (Sset ρbar 𝒟) :=
  ⟨H1π ρbar.adZero (classOf D p hp𝒪 hdet hdetR φ),
    Submodule.subset_span (classOf_mem D p hp𝒪 hdet hdetR h𝒟 φ)⟩

theorem Φ_injective (hp2 : p ≠ 2) : Function.Injective (Φ D p hp𝒪 hdet hdetR h𝒟) := by
  intro φ₁ φ₂ heq
  have h12 : H1π ρbar.adZero (classOf D p hp𝒪 hdet hdetR φ₁) =
      H1π ρbar.adZero (classOf D p hp𝒪 hdet hdetR φ₂) := congrArg Subtype.val heq
  have h2 : IsUnit (2 : 𝕜) := isUnit_two p (residue_natCast_eq_zero p hp𝒪) hp2
  have hl₁ := isLocalHom_algHom D φ₁
  have hl₂ := isLocalHom_algHom D φ₂
  obtain ⟨w, -, hw⟩ := (ResidualGaloisRep.H1Pi_adZero_eq_iff_exists_dualNumber_conj 𝕜 ρbar h2
    (dualForm D φ₁) (dualForm D φ₂) (isDualLift_dualForm D hl₁ (compatO_algHom D φ₁))
    (isDualLift_dualForm D hl₂ (compatO_algHom D φ₂)) (classOf D p hp𝒪 hdet hdetR φ₁)
    (classOf D p hp𝒪 hdet hdetR φ₂) (fun _ => rfl) (fun _ => rfl)).mp h12
  have he : (D.ρ.baseChangeAlong (φ₁ : D.R →+* 𝕜[ε]) hl₁).IsEquiv
      (D.ρ.baseChangeAlong (φ₂ : D.R →+* 𝕜[ε]) hl₂) :=
    (isFramedBy_dualForm D φ₁ hl₁).isEquiv_of_conj (isFramedBy_dualForm D φ₂ hl₂) w hw
  have hres := (isFramedBy_dualForm D (φ₂ : D.R →+* 𝕜[ε]) hl₂).residual_isEquiv
    (isDualLift_dualForm D hl₂ (compatO_algHom D φ₂))
  rw [← residueField_map_algebraMap_OK] at hres
  exact GaloisRep.DeformationRingData.algHom_eq_of_isEquiv D 𝕜[ε] residue_comp_algebraMap_OK_surjective
    _ (h𝒟 φ₂ hl₂) hres φ₁ φ₂ hl₁ hl₂ he ⟨GaloisRepAdic.Equiv.refl _⟩

theorem Sset_finite [Finite 𝕜] [Finite (D.R →ₐ[𝒪] 𝕜[ε])] : (Sset ρbar 𝒟).Finite := by
  let F : (D.R →ₐ[𝒪] 𝕜[ε]) × (DualNumber (Module.End 𝕜 ρbar.V))ˣ → (Γ → Module.End 𝕜 ρbar.V) :=
    fun q σ => dualLiftToCochain ρbar.ρ.toHomUnits
      ((MulAut.conj q.2).toMonoidHom.comp (dualForm D (q.1 : D.R →+* 𝕜[ε]))) σ
  haveI : Finite (Module.End 𝕜 ρbar.V) := Module.finite_of_finite 𝕜
  haveI : Finite (DualNumber (Module.End 𝕜 ρbar.V)) :=
    inferInstanceAs (Finite (Module.End 𝕜 ρbar.V × Module.End 𝕜 ρbar.V))
  let coeF : cocycles₁ ρbar.adZero → (Γ → Module.End 𝕜 ρbar.V) :=
    fun c σ => ((c : Γ → ↥(LinearMap.ker (LinearMap.trace 𝕜 ρbar.V))) σ : Module.End 𝕜 ρbar.V)
  have hinj : Function.Injective coeF := fun c c' h =>
    Subtype.ext (funext fun σ => Subtype.ext (congrFun h σ))
  have hCfin : (coeF ⁻¹' Set.range F).Finite := (Set.finite_range F).preimage hinj.injOn
  refine (hCfin.image (fun c => H1π ρbar.adZero c)).subset ?_
  rintro x ⟨c, hcx, ρA, h𝒟A, ρd, hlift, hc, b', bbar', hdict'⟩
  refine ⟨c, ?_, hcx⟩
  have hfr : IsFramedBy ρbar ρA ρd b' bbar' := hdict'
  have hresA := hfr.residual_isEquiv hlift
  rw [← residueField_map_algebraMap_OK] at hresA
  obtain ⟨φ, ⟨hφ, heq⟩, -⟩ :=
    D.universal 𝕜[ε] residue_comp_algebraMap_OK_surjective ρA h𝒟A hresA
  obtain ⟨w, hw⟩ := (isFramedBy_dualForm D (φ : D.R →+* 𝕜[ε]) hφ).exists_conj_of_isEquiv hfr heq
  refine ⟨(φ, w), funext fun σ => ?_⟩
  show F (φ, w) σ = ((c : Γ → ↥(LinearMap.ker (LinearMap.trace 𝕜 ρbar.V))) σ : Module.End 𝕜 ρbar.V)
  rw [hc σ]
  show ((((MulAut.conj w).toMonoidHom.comp (dualForm D (φ : D.R →+* 𝕜[ε]))) σ :
      (DualNumber (Module.End 𝕜 ρbar.V))ˣ) : DualNumber (Module.End 𝕜 ρbar.V)).snd * _ =
    ((ρd σ : DualNumber (Module.End 𝕜 ρbar.V))).snd * _
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← hw σ]

include hp𝒪 hdet hdetR h𝒟 in

theorem main [Finite 𝕜] (hp2 : p ≠ 2) :
    ∃ (m : ℕ) (a : Fin m → D.R), (∀ i, a i ∈ maximalIdeal D.R) ∧
      maximalIdeal D.R ≤ Ideal.span (Set.range a) ⊔ maximalIdeal D.R ^ 2 ⊔
        (maximalIdeal 𝒪).map (algebraMap 𝒪 D.R) ∧
      m ≤ Module.finrank 𝕜 (Submodule.span 𝕜 (Sset ρbar 𝒟)) := by
  obtain ⟨m, a, ha, hgen, hcard⟩ :=
    IsLocalRing.exists_generators_maximalIdeal_natCard_algHom_dualNumber_eq_pow (𝒪 := 𝒪) (R := D.R)
      D.residue_surjective
  have hkpos : 0 < Nat.card 𝕜 := Nat.card_pos
  haveI : Finite (D.R →ₐ[𝒪] 𝕜[ε]) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hkpos.ne')
  have hfin : (Sset ρbar 𝒟).Finite := Sset_finite D
  haveI : Module.Finite 𝕜 (Submodule.span 𝕜 (Sset ρbar 𝒟)) :=
    Module.Finite.iff_fg.mpr (Submodule.fg_span hfin)
  haveI : Finite (Submodule.span 𝕜 (Sset ρbar 𝒟)) := Module.finite_of_finite 𝕜
  have hle := Nat.card_le_card_of_injective _ (Φ_injective D p hp𝒪 hdet hdetR h𝒟 hp2)
  rw [hcard, Module.natCard_eq_pow_finrank (K := 𝕜) (V := Submodule.span 𝕜 (Sset ρbar 𝒟))] at hle
  refine ⟨m, a, ha, hgen.trans (sup_le_sup_right le_sup_left _), ?_⟩
  exact (Nat.pow_le_pow_iff_right Finite.one_lt_card).mp hle

end Assembly

end P2mK4T
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_generators_maximalIdeal_card_le_finrank_span_dualNumberClasses.P2mK4T"

open P2mK4T in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)
    {ρbar : ResidualGaloisRep (ResidueField 𝒪)}
    (hdet : (GaloisRepAdic.ofResidualGaloisRep ρbar).DetIsCyclotomic p)
    {𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
    (D : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟) (hdetR : D.ρ.DetIsCyclotomic p) :
    letI : Algebra 𝒪 (DualNumber (ResidueField 𝒪)) :=
      ((algebraMap (ResidueField 𝒪) (DualNumber (ResidueField 𝒪))).comp
        (algebraMap 𝒪 (ResidueField 𝒪))).toAlgebra
    (∀ (φ : D.R →ₐ[𝒪] DualNumber (ResidueField 𝒪))
        (hφ : IsLocalHom (φ : D.R →+* DualNumber (ResidueField 𝒪))),
        𝒟 (D.ρ.baseChangeAlong (φ : D.R →+* DualNumber (ResidueField 𝒪)) hφ)) →
    ∃ (m : ℕ) (a : Fin m → D.R), (∀ i, a i ∈ maximalIdeal D.R) ∧
      maximalIdeal D.R ≤ Ideal.span (Set.range a) ⊔ maximalIdeal D.R ^ 2 ⊔
        (maximalIdeal 𝒪).map (algebraMap 𝒪 D.R) ∧
      m ≤ Module.finrank (ResidueField 𝒪) (Submodule.span (ResidueField 𝒪)
        {x : H1 ρbar.adZero |
          ∃ c : cocycles₁ ρbar.adZero, H1π ρbar.adZero c = x ∧
          ∃ ρA : GaloisRepAdic (DualNumber (ResidueField 𝒪)),
            𝒟 ρA ∧
          ∃ ρd : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →*
              (DualNumber (Module.End (ResidueField 𝒪) ρbar.V))ˣ,
            IsDualLift ρbar.ρ.toHomUnits ρd ∧
            (∀ σ, ((c : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →
                ↥(LinearMap.ker (LinearMap.trace (ResidueField 𝒪) ρbar.V))) σ :
                  Module.End (ResidueField 𝒪) ρbar.V) =
              dualLiftToCochain ρbar.ρ.toHomUnits ρd σ) ∧
            ∃ (b : Module.Basis (Fin 2) (DualNumber (ResidueField 𝒪)) ρA.V)
              (bbar : Module.Basis (Fin 2) (ResidueField 𝒪) ρbar.V),
              ∀ σ, LinearMap.toMatrix b b (ρA.ρ σ) =
                Matrix.dualNumberEquiv.symm
                  ⟨LinearMap.toMatrix bbar bbar
                      ((ρd σ : DualNumber (Module.End (ResidueField 𝒪) ρbar.V)).fst),
                    LinearMap.toMatrix bbar bbar
                      ((ρd σ : DualNumber (Module.End (ResidueField 𝒪) ρbar.V)).snd)⟩}) := by
  intro h𝒟
  exact P2mK4T.main D p hp𝒪 hdet hdetR h𝒟 hp2

end S_GaloisRep_DeformationRingData_exists_generators_maximalIdeal_card_le_finrank_span_dualNumberClasses
end P2MW
export P2MW.S_GaloisRep_DeformationRingData_exists_generators_maximalIdeal_card_le_finrank_span_dualNumberClasses (solution)
