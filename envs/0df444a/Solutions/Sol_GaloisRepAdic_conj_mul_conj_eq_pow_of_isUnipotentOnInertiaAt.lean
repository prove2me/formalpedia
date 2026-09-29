-- Prove2me | solution 1 for GaloisRepAdic.conj_mul_conj_eq_pow_of_isUnipotentOnInertiaAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/f7a10170-f2eb-5634-82aa-6ab3383554d8

import Definitions.Def_GaloisRep_DeformationRingData
import Definitions.Def_GaloisRep_LocalConditions
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.RingTheory.Length
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.RingTheory.Filtration
import Mathlib.Tactic.Group
import Definitions.Def_GaloisRep_Adic
import Definitions.Def_FLTPrelim_Ramification
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRepAdic_conj_mul_conj_eq_pow_of_isUnipotentOnInertiaAt

set_option autoImplicit false

open GaloisRep Module

namespace COTGlue

noncomputable def twAd {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    Module.End A ρ.V →ₗ[A] Module.End A ρ.V :=
  (ρ.det σ : A) • {
    toFun := fun f => ρ.ρ σ * f * ρ.ρ σ⁻¹
    map_add' := fun f g => by simp only [mul_add, add_mul]
    map_smul' := fun c f => by
      simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, RingHom.id_apply] }

noncomputable abbrev adZero {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A) :
    Submodule A (Module.End A ρ.V) :=
  LinearMap.ker (LinearMap.trace A ρ.V)

noncomputable def adZeroInertiaInv {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A)
    (P : ValuationSubring (AlgebraicClosure ℚ)) : Submodule A (Module.End A ρ.V) :=
  adZero ρ ⊓ ⨅ τ ∈ P.inertiaSubgroupIn ℚ, LinearMap.ker (twAd ρ τ - LinearMap.id)

noncomputable def localCotangentTermDenom {A : Type} [CommRing A] [IsLocalRing A]
    (ρ : GaloisRepAdic A) (P : ValuationSubring (AlgebraicClosure ℚ))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    Submodule A (adZeroInertiaInv ρ P) :=
  Submodule.comap (adZeroInertiaInv ρ P).subtype
    ((adZeroInertiaInv ρ P).map (twAd ρ σ - LinearMap.id))

variable {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A) (b : Basis (Fin 2) A ρ.V)

noncomputable abbrev endToMatrix : Module.End A ρ.V ≃ₐ[A] Matrix (Fin 2) (Fin 2) A :=
  LinearMap.toMatrixAlgEquiv b

theorem trace_endToMatrix (f : Module.End A ρ.V) :
    LinearMap.trace A ρ.V f = Matrix.trace (endToMatrix ρ b f) :=
  LinearMap.trace_eq_matrix_trace A b f

noncomputable def adZeroEquivSl2 :
    adZero ρ ≃ₗ[A] LinearMap.ker (Matrix.traceLinearMap (Fin 2) A A) :=
  LinearEquiv.ofBijective
    ((endToMatrix ρ b).toLinearEquiv.toLinearMap.restrict
      (p := adZero ρ) (q := LinearMap.ker (Matrix.traceLinearMap (Fin 2) A A))
      (fun f hf => by
        show Matrix.trace (endToMatrix ρ b f) = 0
        rw [← trace_endToMatrix ρ b]; exact hf))
    ⟨fun f g h => Subtype.ext ((endToMatrix ρ b).toLinearEquiv.injective (Subtype.ext_iff.mp h)),
     fun ⟨M, hM⟩ => ⟨⟨(endToMatrix ρ b).symm M, by
        simp only [adZero, LinearMap.mem_ker, trace_endToMatrix ρ b,
          AlgEquiv.apply_symm_apply]; exact hM⟩,
       Subtype.ext (by
        simp only [LinearMap.restrict_apply]
        exact (endToMatrix ρ b).apply_symm_apply M)⟩⟩

theorem coe_det_eq_matrix_det (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    (ρ.det σ : A) = Matrix.det (endToMatrix ρ b (ρ.ρ σ)) := by
  have h1 : (ρ.det σ : A) = LinearMap.det (ρ.ρ σ) := rfl
  rw [h1, ← LinearMap.det_toMatrix b]
  rfl

theorem endToMatrix_twAd (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : Module.End A ρ.V) :
    endToMatrix ρ b (twAd ρ σ f) =
      endToMatrix ρ b (ρ.ρ σ) * endToMatrix ρ b f * Matrix.adjugate (endToMatrix ρ b (ρ.ρ σ)) := by
  have hFG : endToMatrix ρ b (ρ.ρ σ) * endToMatrix ρ b (ρ.ρ σ⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one]
  have hadj : (endToMatrix ρ b (ρ.ρ σ)).adjugate
      = (endToMatrix ρ b (ρ.ρ σ)).det • endToMatrix ρ b (ρ.ρ σ⁻¹) := by
    have key : (endToMatrix ρ b (ρ.ρ σ)).adjugate *
        (endToMatrix ρ b (ρ.ρ σ) * endToMatrix ρ b (ρ.ρ σ⁻¹))
        = (endToMatrix ρ b (ρ.ρ σ)).det • endToMatrix ρ b (ρ.ρ σ⁻¹) := by
      rw [← mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, one_mul]
    rwa [hFG, mul_one] at key
  have hdet : (ρ.det σ : A) = (endToMatrix ρ b (ρ.ρ σ)).det := coe_det_eq_matrix_det ρ b σ
  simp only [twAd, LinearMap.smul_apply, LinearMap.coe_mk, AddHom.coe_mk, map_smul, map_mul,
    hadj, hdet, Matrix.mul_smul]

end COTGlue

namespace WCOTGlueBCore
variable {R : Type} [CommRing R]
def conjAdj (F : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 2) (Fin 2) R →ₗ[R] Matrix (Fin 2) (Fin 2) R where
  toFun X := F * X * F.adjugate
  map_add' X Y := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by rw [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]
@[scoped simp] theorem conjAdj_apply (F X : Matrix (Fin 2) (Fin 2) R) : conjAdj F X = F * X * F.adjugate := rfl
def trLin : Matrix (Fin 2) (Fin 2) R →ₗ[R] R where
  toFun X := X 0 0 + X 1 1
  map_add' X Y := by simp only [Matrix.add_apply]; ring
  map_smul' c X := by simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]; ring
def invM (𝒯 : Set (Matrix (Fin 2) (Fin 2) R)) : Submodule R (Matrix (Fin 2) (Fin 2) R) :=
  LinearMap.ker (trLin (R := R)) ⊓ ⨅ T ∈ 𝒯, LinearMap.ker (conjAdj T - LinearMap.id)
def denM (𝒯 : Set (Matrix (Fin 2) (Fin 2) R)) (F : Matrix (Fin 2) (Fin 2) R) : Submodule R (invM 𝒯) :=
  Submodule.comap (invM 𝒯).subtype ((invM 𝒯).map (conjAdj F - LinearMap.id))
end WCOTGlueBCore
p2m_reactivate "P2MW.S_GaloisRepAdic_conj_mul_conj_eq_pow_of_isUnipotentOnInertiaAt.WCOTGlueBCore"

namespace COTGlue
open WCOTGlueBCore
variable {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A) (b : Basis (Fin 2) A ρ.V)

theorem endToMatrix_comp_twAd (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    (endToMatrix ρ b).toLinearMap ∘ₗ (twAd ρ τ) =
      conjAdj (endToMatrix ρ b (ρ.ρ τ)) ∘ₗ (endToMatrix ρ b).toLinearMap := by
  ext f; simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, conjAdj_apply,
    endToMatrix_twAd]

theorem mem_adZeroInertiaInv_iff_endToMatrix_mem_invM (P : ValuationSubring (AlgebraicClosure ℚ))
    (f : Module.End A ρ.V) :
    f ∈ adZeroInertiaInv ρ P ↔
      endToMatrix ρ b f ∈ invM ((fun τ => endToMatrix ρ b (ρ.ρ τ)) '' (P.inertiaSubgroupIn ℚ)) := by
  unfold adZeroInertiaInv invM
  rw [Submodule.mem_inf, Submodule.mem_inf]
  apply and_congr
  ·
    rw [LinearMap.mem_ker, LinearMap.mem_ker, trace_endToMatrix ρ b, Matrix.trace_fin_two]
    rfl
  ·
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero, conjAdj_apply, Set.forall_mem_image]
    refine forall_congr' fun τ => forall_congr' fun _ => ?_
    rw [← endToMatrix_twAd ρ b]
    exact ⟨fun h => congrArg _ h, fun h => (endToMatrix ρ b).injective h⟩

theorem map_adZeroInertiaInv_eq_invM (P : ValuationSubring (AlgebraicClosure ℚ)) :
    Submodule.map (endToMatrix ρ b).toLinearMap (adZeroInertiaInv ρ P) =
      invM ((fun τ => endToMatrix ρ b (ρ.ρ τ)) '' (P.inertiaSubgroupIn ℚ)) := by
  ext M
  simp only [Submodule.mem_map, AlgEquiv.toLinearMap_apply]
  constructor
  · rintro ⟨f, hf, rfl⟩; exact (mem_adZeroInertiaInv_iff_endToMatrix_mem_invM ρ b P f).mp hf
  · intro hM
    exact ⟨(endToMatrix ρ b).symm M,
      (mem_adZeroInertiaInv_iff_endToMatrix_mem_invM ρ b P _).mpr
        (by rwa [AlgEquiv.apply_symm_apply]),
      (endToMatrix ρ b).apply_symm_apply M⟩

noncomputable def adZeroInertiaInvEquivInvM (P : ValuationSubring (AlgebraicClosure ℚ)) :
    (adZeroInertiaInv ρ P : Submodule A _) ≃ₗ[A]
      (invM (R := A) ((fun τ => endToMatrix ρ b (ρ.ρ τ)) '' (P.inertiaSubgroupIn ℚ)) :
        Submodule A _) :=
  ((endToMatrix ρ b).toLinearEquiv.submoduleMap (adZeroInertiaInv ρ P)).trans
    (LinearEquiv.ofEq _ _ (map_adZeroInertiaInv_eq_invM ρ b P))

theorem adZeroInertiaInvEquivInvM_coe (P : ValuationSubring (AlgebraicClosure ℚ))
    (x : adZeroInertiaInv ρ P) :
    ((adZeroInertiaInvEquivInvM ρ b P) x : Matrix (Fin 2) (Fin 2) A) = endToMatrix ρ b ↑x := rfl

theorem endToMatrix_twAd_sub_id (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (g : Module.End A ρ.V) :
    endToMatrix ρ b (twAd ρ σ g - g) =
      conjAdj (endToMatrix ρ b (ρ.ρ σ)) (endToMatrix ρ b g) - endToMatrix ρ b g := by
  rw [map_sub, conjAdj_apply, endToMatrix_twAd]

theorem map_localCotangentTermDenom_eq_denM (P : ValuationSubring (AlgebraicClosure ℚ))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    Submodule.map (adZeroInertiaInvEquivInvM ρ b P : _ →ₗ[A] _)
        (localCotangentTermDenom ρ P σ) =
      denM ((fun τ => endToMatrix ρ b (ρ.ρ τ)) '' (P.inertiaSubgroupIn ℚ))
        (endToMatrix ρ b (ρ.ρ σ)) := by
  ext ⟨M, hM⟩
  simp only [Submodule.mem_map, localCotangentTermDenom, denM, Submodule.mem_comap,
    Submodule.subtype_apply, LinearMap.sub_apply, LinearMap.id_apply]
  constructor
  · rintro ⟨⟨f, hf⟩, ⟨g, hg, hgf⟩, heq⟩
    refine ⟨endToMatrix ρ b g, (mem_adZeroInertiaInv_iff_endToMatrix_mem_invM ρ b P g).mp hg, ?_⟩
    have hMf : M = endToMatrix ρ b f := (congrArg Subtype.val heq).symm
    have hfg : f = twAd ρ σ g - g := hgf.symm
    rw [hMf, hfg]
    exact (endToMatrix_twAd_sub_id ρ b σ g).symm
  · rintro ⟨N, hN, hNM⟩
    set g := (endToMatrix ρ b).symm N
    have hgN : endToMatrix ρ b g = N := (endToMatrix ρ b).apply_symm_apply N
    have hgmem : g ∈ adZeroInertiaInv ρ P :=
      (mem_adZeroInertiaInv_iff_endToMatrix_mem_invM ρ b P g).mpr (by rw [hgN]; exact hN)
    have hfeq : endToMatrix ρ b (twAd ρ σ g - g) = M := by
      rw [endToMatrix_twAd_sub_id, hgN, conjAdj_apply]; exact hNM
    have hfmem : twAd ρ σ g - g ∈ adZeroInertiaInv ρ P :=
      (mem_adZeroInertiaInv_iff_endToMatrix_mem_invM ρ b P _).mpr (hfeq ▸ hM)
    exact ⟨⟨twAd ρ σ g - g, hfmem⟩, ⟨g, hgmem, rfl⟩, Subtype.ext hfeq⟩

theorem length_localCotangentTerm_eq_invM_quotient (P : ValuationSubring (AlgebraicClosure ℚ))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    Module.length A (adZeroInertiaInv ρ P ⧸ localCotangentTermDenom ρ P σ) =
      Module.length A (invM (R := A) ((fun τ => endToMatrix ρ b (ρ.ρ τ)) '' (P.inertiaSubgroupIn ℚ))
        ⧸ denM ((fun τ => endToMatrix ρ b (ρ.ρ τ)) '' (P.inertiaSubgroupIn ℚ))
            (endToMatrix ρ b (ρ.ρ σ))) :=
  (Submodule.Quotient.equiv _ _ (adZeroInertiaInvEquivInvM ρ b P)
    (map_localCotangentTermDenom_eq_denM ρ b P σ)).length_eq

end COTGlue
p2m_reactivate "P2MW.S_GaloisRepAdic_conj_mul_conj_eq_pow_of_isUnipotentOnInertiaAt.WCOTGlueBCore"

namespace WCOTGlueBCore

variable {R : Type} [CommRing R]

private def _root_.WCOTGlueBCore.sl2M (s t u : R) : Matrix (Fin 2) (Fin 2) R := Matrix.of ![![s, t], ![u, -s]]

p2m_export "WCOTGlueBCore" "sl2M"
theorem mem_invM_iff (𝒯 : Set (Matrix (Fin 2) (Fin 2) R)) (X : Matrix (Fin 2) (Fin 2) R) :
    X ∈ invM 𝒯 ↔ X 0 0 + X 1 1 = 0 ∧ ∀ T ∈ 𝒯, T * X * T.adjugate = X := by
  simp only [invM, Submodule.mem_inf, LinearMap.mem_ker, Submodule.mem_iInf, LinearMap.sub_apply,
    LinearMap.id_apply, conjAdj_apply, sub_eq_zero]
  rfl

theorem adjugate_one_add_sl2M (b : R) : (1 + sl2M 0 b 0).adjugate = 1 - sl2M 0 b 0 := by
  have h : 1 + sl2M 0 b 0 = Matrix.of ![![1, b], ![0, 1]] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [sl2M]
  rw [h, Matrix.adjugate_fin_two_of]
  ext i j; fin_cases i <;> fin_cases j <;> simp [sl2M]

theorem sl2M_mem_invM (𝒯 : Set (Matrix (Fin 2) (Fin 2) R)) (hline : ∀ T ∈ 𝒯, ∃ b : R, T = 1 + sl2M 0 b 0)
    (s : R) : sl2M 0 s 0 ∈ invM 𝒯 := by
  rw [mem_invM_iff]
  refine ⟨by simp [sl2M], fun T hT => ?_⟩
  obtain ⟨b, rfl⟩ := hline T hT
  rw [adjugate_one_add_sl2M]
  ext i j; fin_cases i <;> fin_cases j <;> simp [sl2M, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

theorem eq_sl2M_of_mem_invM [IsDomain R] (𝒯 : Set (Matrix (Fin 2) (Fin 2) R)) (t : R) (ht : t ≠ 0)
    (h2 : (2 : R) ≠ 0) (hT₀ : 1 + sl2M 0 t 0 ∈ 𝒯) (X : Matrix (Fin 2) (Fin 2) R) (hX : X ∈ invM 𝒯) :
    X = sl2M 0 (X 0 1) 0 := by
  rw [mem_invM_iff] at hX
  obtain ⟨htr, hfix⟩ := hX
  have h := hfix _ hT₀
  rw [adjugate_one_add_sl2M] at h

  have e00 : ((1 + sl2M 0 t 0) * X * (1 - sl2M 0 t 0)) 0 0 = X 0 0 + t * X 1 0 := by
    simp [sl2M, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
  have e01 : ((1 + sl2M 0 t 0) * X * (1 - sl2M 0 t 0)) 0 1 =
      X 0 1 + t * (X 1 1 - X 0 0) - t * t * X 1 0 := by
    simp [sl2M, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
    try ring
  have h10 : t * X 1 0 = 0 := by
    have := congrFun (congrFun h 0) 0
    rw [e00] at this
    linear_combination this
  have hu : X 1 0 = 0 := (mul_eq_zero.mp h10).resolve_left ht
  have hd : X 1 1 = -X 0 0 := by linear_combination htr
  have h01 : (2 : R) * (t * X 0 0) = 0 := by
    have := congrFun (congrFun h 0) 1
    rw [e01, hu, hd] at this
    linear_combination -this
  have hs : X 0 0 = 0 := by
    have := (mul_eq_zero.mp h01).resolve_left h2
    exact (mul_eq_zero.mp this).resolve_left ht
  ext i j; fin_cases i <;> fin_cases j <;> simp [sl2M, hu, hs, hd]

theorem conjAdj_sl2M_eq [IsDomain R] (F : Matrix (Fin 2) (Fin 2) R) (t q : R) (ht : t ≠ 0)
    (hFN : F * sl2M 0 t 0 = q • (sl2M 0 t 0 * F)) (hdet : F.det = q) (s : R) :
    F * sl2M 0 s 0 * F.adjugate = (q ^ 2) • sl2M 0 s 0 := by
  have hE : sl2M 0 t 0 = t • sl2M (0 : R) 1 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [sl2M]
  have hsE : sl2M 0 s 0 = s • sl2M (0 : R) 1 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [sl2M]
  have hFE : F * sl2M 0 1 0 = q • (sl2M 0 1 0 * F) := by
    have h1 : t • (F * sl2M 0 1 0) = t • (q • (sl2M 0 1 0 * F)) := by
      rw [← Matrix.mul_smul, ← hE, hFN, hE, Matrix.smul_mul, smul_comm]
    exact smul_right_injective _ ht h1
  rw [hsE, Matrix.mul_smul, Matrix.smul_mul, hFE, Matrix.smul_mul, Matrix.mul_assoc, Matrix.mul_adjugate, hdet,
    Matrix.mul_smul, Matrix.mul_one]
  simp only [smul_smul, sq]
  congr 1
  ring

theorem length_quotient_le [IsDomain R] (𝒯 : Set (Matrix (Fin 2) (Fin 2) R)) (t : R) (ht : t ≠ 0)
    (h2 : (2 : R) ≠ 0) (hT₀ : 1 + sl2M 0 t 0 ∈ 𝒯) (hline : ∀ T ∈ 𝒯, ∃ b : R, T = 1 + sl2M 0 b 0)
    (F : Matrix (Fin 2) (Fin 2) R) (q : R) (hFN : F * sl2M 0 t 0 = q • (sl2M 0 t 0 * F)) (hdet : F.det = q) :
    Module.length R (invM 𝒯 ⧸ denM 𝒯 F) ≤ Module.length R (R ⧸ Ideal.span {q ^ 2 - 1}) := by

  let E' : invM 𝒯 := ⟨sl2M 0 1 0, sl2M_mem_invM 𝒯 hline 1⟩
  let ψ : R →ₗ[R] invM 𝒯 ⧸ denM 𝒯 F := (denM 𝒯 F).mkQ.comp (LinearMap.toSpanSingleton R (invM 𝒯) E')

  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (denM 𝒯 F) y
    refine ⟨(x : Matrix (Fin 2) (Fin 2) R) 0 1, ?_⟩
    have hx := eq_sl2M_of_mem_invM 𝒯 t ht h2 hT₀ x x.2
    have hxE : ((x : Matrix (Fin 2) (Fin 2) R) 0 1) • E' = x := by
      apply Subtype.ext
      rw [Submodule.coe_smul]
      change ((x : Matrix (Fin 2) (Fin 2) R) 0 1) • sl2M (0 : R) 1 0 = (x : Matrix (Fin 2) (Fin 2) R)
      conv_rhs => rw [hx]
      ext i j; fin_cases i <;> fin_cases j <;> simp [sl2M]
    simp only [ψ, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply, hxE]

  have hker : Ideal.span {q ^ 2 - 1} ≤ LinearMap.ker ψ := by
    rw [Ideal.span_le]
    rintro _ rfl
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    simp only [ψ, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    rw [denM, Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_smul]
    refine ⟨sl2M 0 1 0, sl2M_mem_invM 𝒯 hline 1, ?_⟩
    rw [LinearMap.sub_apply, LinearMap.id_apply, conjAdj_apply, conjAdj_sl2M_eq F t q ht hFN hdet 1, sub_smul,
      one_smul]
  have hsurj : Function.Surjective ((Ideal.span {q ^ 2 - 1}).liftQ ψ hker) := by
    intro y
    obtain ⟨r, rfl⟩ := hψ y
    exact ⟨Submodule.Quotient.mk r, rfl⟩
  exact Module.length_le_of_surjective _ hsurj

end WCOTGlueBCore
p2m_reactivate "P2MW.S_GaloisRepAdic_conj_mul_conj_eq_pow_of_isUnipotentOnInertiaAt.WCOTGlueBCore"

namespace WCOTGlueBCore

open Polynomial

variable {R : Type} [CommRing R]

theorem sub_one_mul_sub_one_eq_zero_of_charpoly (M : Matrix (Fin 2) (Fin 2) R)
    (h : M.charpoly = (X - 1) ^ 2) : (M - 1) * (M - 1) = 0 := by
  have h0 := M.aeval_self_charpoly
  rw [h, map_pow, map_sub, aeval_X, map_one] at h0
  simpa [sq] using h0

theorem trace_eq_two_of_charpoly (M : Matrix (Fin 2) (Fin 2) R)
    (h : M.charpoly = (X - 1) ^ 2) : M.trace = 2 := by
  have ht := Matrix.trace_eq_neg_charpoly_coeff M
  rw [h] at ht
  have hc : ((X - 1 : Polynomial R) ^ 2).coeff 1 = -2 := by
    rw [sub_sq, mul_one, one_pow]
    simp [coeff_X_pow, coeff_one]
  simp only [Fintype.card_fin] at ht
  rw [hc] at ht
  rw [ht]
  ring

theorem one_add_pow_of_mul_self_eq_zero (N : Matrix (Fin 2) (Fin 2) R) (hN : N * N = 0)
    (n : ℕ) : (1 + N) ^ n = 1 + (n : R) • N := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ih, add_mul, one_mul, mul_add, mul_one, Matrix.smul_mul, hN, smul_zero,
        add_zero, Nat.cast_succ, add_smul, one_smul, add_assoc, add_comm N]

theorem mul_eq_smul_mul_of_conj_pow (F G N : Matrix (Fin 2) (Fin 2) R) (q : ℕ)
    (hFG : F * G = 1) (hGF : G * F = 1) (hN : N * N = 0)
    (hconj : F * (1 + N) * G = (1 + N) ^ q) : F * N = (q : R) • (N * F) := by
  rw [one_add_pow_of_mul_self_eq_zero N hN q] at hconj
  have h1 : F * (1 + N) * G = 1 + F * N * G := by
    rw [mul_add, mul_one, add_mul, hFG]
  rw [h1] at hconj
  have h2 : F * N * G = (q : R) • N := add_left_cancel hconj
  have h3 := congrArg (· * F) h2
  rw [mul_assoc, hGF, mul_one, Matrix.smul_mul] at h3
  exact h3

example : (Matrix.of ![![(1 : ℤ), 1], ![0, 1]]).charpoly = (X - 1) ^ 2 := by
  rw [Matrix.charpoly_fin_two]
  simp [Matrix.trace_fin_two, Matrix.det_fin_two]
  ring

example :
    ¬ ((1 + Matrix.of ![![(1 : ℤ), 0], ![0, 0]]) ^ 2 =
      1 + ((2 : ℕ) : ℤ) • Matrix.of ![![(1 : ℤ), 0], ![0, 0]]) := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply, Matrix.one_apply] at h00

end WCOTGlueBCore
p2m_reactivate "P2MW.S_GaloisRepAdic_conj_mul_conj_eq_pow_of_isUnipotentOnInertiaAt.WCOTGlueBCore"

namespace WCOTDevB6

variable {R : Type} [CommRing R] [NoZeroDivisors R]

private def _root_.WCOTDevB6.sl2M (s t u : R) : Matrix (Fin 2) (Fin 2) R := Matrix.of ![![s, t], ![u, -s]]

p2m_export "WCOTDevB6" "sl2M"

theorem trace_eq_zero_of_mul_self_eq_zero (N : Matrix (Fin 2) (Fin 2) R) (hN : N * N = 0) : N.trace = 0 := by
  have h00 : N 0 0 * N 0 0 + N 0 1 * N 1 0 = 0 := by
    have := congrFun (congrFun hN 0) 0; simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h01 : N 0 0 * N 0 1 + N 0 1 * N 1 1 = 0 := by
    have := congrFun (congrFun hN 0) 1; simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h10 : N 1 0 * N 0 0 + N 1 1 * N 1 0 = 0 := by
    have := congrFun (congrFun hN 1) 0; simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h11 : N 1 0 * N 0 1 + N 1 1 * N 1 1 = 0 := by
    have := congrFun (congrFun hN 1) 1; simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  rw [Matrix.trace_fin_two]
  by_contra h
  have hb : N 0 1 = 0 := by
    have : N 0 1 * (N 0 0 + N 1 1) = 0 := by rw [← h01]; ring
    exact (mul_eq_zero.mp this).resolve_right h
  have hc : N 1 0 = 0 := by
    have : N 1 0 * (N 0 0 + N 1 1) = 0 := by rw [← h10]; ring
    exact (mul_eq_zero.mp this).resolve_right h
  have ha : N 0 0 = 0 := by
    have : N 0 0 * N 0 0 = 0 := by rw [← h00, hb]; ring
    exact (mul_self_eq_zero.mp this)
  have hd : N 1 1 = 0 := by
    have : N 1 1 * N 1 1 = 0 := by rw [← h11, hc]; ring
    exact (mul_self_eq_zero.mp this)
  exact h (by rw [ha, hd, add_zero])

theorem eq_line_of_unipotent_mul (t : R) (ht : t ≠ 0) (N : Matrix (Fin 2) (Fin 2) R) (hN : N * N = 0)
    (hu : ((1 + sl2M 0 t 0) * (1 + N)).trace = 2) : N = sl2M 0 (N 0 1) 0 := by
  have htrN : N 0 0 + N 1 1 = 0 := by rw [← Matrix.trace_fin_two]; exact trace_eq_zero_of_mul_self_eq_zero N hN
  have htr : ((1 + sl2M 0 t 0) * (1 + N)).trace = 2 + (N 0 0 + N 1 1) + t * N 1 0 := by
    simp [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, sl2M, Matrix.one_apply]
    ring
  have hc : N 1 0 = 0 := by
    have : t * N 1 0 = 0 := by
      have h2 := hu; rw [htr, htrN, add_zero] at h2
      simpa using h2
    exact (mul_eq_zero.mp this).resolve_left ht
  have h00 : N 0 0 * N 0 0 + N 0 1 * N 1 0 = 0 := by
    have := congrFun (congrFun hN 0) 0; simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have ha : N 0 0 = 0 := by
    have : N 0 0 * N 0 0 = 0 := by rw [← h00, hc]; ring
    exact mul_self_eq_zero.mp this
  have hd : N 1 1 = 0 := by rw [ha, zero_add] at htrN; exact htrN
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2M, ha, hc, hd]

end WCOTDevB6
p2m_reactivate "P2MW.S_GaloisRepAdic_conj_mul_conj_eq_pow_of_isUnipotentOnInertiaAt.WCOTGlueBCore"

namespace WCOTGlueBAdapt

variable {R : Type} [CommRing R]

private def _root_.WCOTGlueBAdapt.sl2M (s t u : R) : Matrix (Fin 2) (Fin 2) R := Matrix.of ![![s, t], ![u, -s]]

p2m_export "WCOTGlueBAdapt" "sl2M"

theorem trace_eq_zero_of_mul_self_eq_zero [NoZeroDivisors R] (N : Matrix (Fin 2) (Fin 2) R) (hN : N * N = 0) :
    N.trace = 0 := by
  have h00 : N 0 0 * N 0 0 + N 0 1 * N 1 0 = 0 := by
    have := congrFun (congrFun hN 0) 0; simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h01 : N 0 0 * N 0 1 + N 0 1 * N 1 1 = 0 := by
    have := congrFun (congrFun hN 0) 1; simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h10 : N 1 0 * N 0 0 + N 1 1 * N 1 0 = 0 := by
    have := congrFun (congrFun hN 1) 0; simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h11 : N 1 0 * N 0 1 + N 1 1 * N 1 1 = 0 := by
    have := congrFun (congrFun hN 1) 1; simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  rw [Matrix.trace_fin_two]
  by_contra h
  have hb : N 0 1 = 0 := by
    have : N 0 1 * (N 0 0 + N 1 1) = 0 := by rw [← h01]; ring
    exact (mul_eq_zero.mp this).resolve_right h
  have hc : N 1 0 = 0 := by
    have : N 1 0 * (N 0 0 + N 1 1) = 0 := by rw [← h10]; ring
    exact (mul_eq_zero.mp this).resolve_right h
  have ha : N 0 0 = 0 := by
    have : N 0 0 * N 0 0 = 0 := by rw [← h00, hb]; ring
    exact (mul_self_eq_zero.mp this)
  have hd : N 1 1 = 0 := by
    have : N 1 1 * N 1 1 = 0 := by rw [← h11, hc]; ring
    exact (mul_self_eq_zero.mp this)
  exact h (by rw [ha, hd, add_zero])

theorem exists_conj_eq_sl2M [IsDomain R] [ValuationRing R] (M : Matrix (Fin 2) (Fin 2) R)
    (hM : M * M = 0) (hM0 : M ≠ 0) :
    ∃ P : Matrix (Fin 2) (Fin 2) R, IsUnit P.det ∧ ∃ t : R, t ≠ 0 ∧ M * P = P * sl2M 0 t 0 := by

  have htr : M 0 0 + M 1 1 = 0 := by
    rw [← Matrix.trace_fin_two]; exact trace_eq_zero_of_mul_self_eq_zero M hM
  have hd : M 1 1 = -M 0 0 := by rw [← sub_eq_zero, sub_neg_eq_add, add_comm]; exact htr
  have h00 : M 0 0 * M 0 0 + M 0 1 * M 1 0 = 0 := by
    have := congrFun (congrFun hM 0) 0; simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have hMe : M = Matrix.of ![![M 0 0, M 0 1], ![M 1 0, -M 0 0]] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [hd]

  rcases ValuationRing.dvd_total (M 0 1) (M 0 0) with ⟨l, hl⟩ | ⟨m, hm⟩
  ·
    by_cases hb : M 0 1 = 0
    ·
      have ha : M 0 0 = 0 := by rw [hl, hb, zero_mul]
      have hc : M 1 0 ≠ 0 := by
        intro hc; apply hM0; rw [hMe]; ext i j; fin_cases i <;> fin_cases j <;> simp [ha, hb, hc]
      refine ⟨Matrix.of ![![0, 1], ![1, 0]], ?_, M 1 0, hc, ?_⟩
      · simp [Matrix.det_fin_two]
      · rw [hMe]; ext i j
        fin_cases i <;> fin_cases j <;> simp [sl2M, Matrix.mul_apply, Fin.sum_univ_two, ha, hb]
    ·
      have hc : M 1 0 = -(l * l * M 0 1) := by
        have : M 0 1 * (M 1 0 + l * l * M 0 1) = 0 := by rw [← h00, hl]; ring
        have h2 := (mul_eq_zero.mp this).resolve_left hb
        exact eq_neg_of_add_eq_zero_left h2
      refine ⟨Matrix.of ![![1, 0], ![-l, 1]], ?_, M 0 1, hb, ?_⟩
      · simp [Matrix.det_fin_two]
      · rw [hMe]; ext i j
        fin_cases i <;> fin_cases j <;>
          simp [sl2M, Matrix.mul_apply, Fin.sum_univ_two, hl, hc] <;> ring
  ·
    by_cases ha : M 0 0 = 0
    ·
      have hb : M 0 1 = 0 := by rw [hm, ha, zero_mul]
      have hc : M 1 0 ≠ 0 := by
        intro hc; apply hM0; rw [hMe]; ext i j; fin_cases i <;> fin_cases j <;> simp [ha, hb, hc]
      refine ⟨Matrix.of ![![0, 1], ![1, 0]], ?_, M 1 0, hc, ?_⟩
      · simp [Matrix.det_fin_two]
      · rw [hMe]; ext i j
        fin_cases i <;> fin_cases j <;> simp [sl2M, Matrix.mul_apply, Fin.sum_univ_two, ha, hb]
    ·
      have hac : M 0 0 = -(m * M 1 0) := by
        have : M 0 0 * (M 0 0 + m * M 1 0) = 0 := by rw [← h00, hm]; ring
        have h2 := (mul_eq_zero.mp this).resolve_left ha
        exact eq_neg_of_add_eq_zero_left h2
      have hc : M 1 0 ≠ 0 := by intro hc; apply ha; rw [hac, hc, mul_zero, neg_zero]
      refine ⟨Matrix.of ![![-m, 1], ![1, 0]], ?_, M 1 0, hc, ?_⟩
      · simp [Matrix.det_fin_two]
      · rw [hMe]; ext i j
        fin_cases i <;> fin_cases j <;>
          simp [sl2M, Matrix.mul_apply, Fin.sum_univ_two, hm, hac]
        all_goals ring

end WCOTGlueBAdapt
p2m_reactivate "P2MW.S_GaloisRepAdic_conj_mul_conj_eq_pow_of_isUnipotentOnInertiaAt.WCOTGlueBCore"

namespace WCOTGlueBT1

variable {A : Type} [CommRing A] {V : Type} [AddCommGroup V] [Module A V] {n : Type} [Fintype n] [DecidableEq n]

theorem toMatrixAlgEquiv_basis_map (b₀ : Basis n A V) (P : Matrix n n A) (hP : IsUnit P.det)
    (f : Module.End A V) :
    LinearMap.toMatrixAlgEquiv (b₀.map (Matrix.toLinearEquiv b₀ P hP)) f =
      P⁻¹ * LinearMap.toMatrixAlgEquiv b₀ f * P := by
  have hg : ((Matrix.toLinearEquiv b₀ P hP : V ≃ₗ[A] V) : V →ₗ[A] V) = Matrix.toLin b₀ b₀ P :=
    LinearMap.ext fun _ => rfl
  have hgs : ((Matrix.toLinearEquiv b₀ P hP).symm : V →ₗ[A] V) = Matrix.toLin b₀ b₀ P⁻¹ :=
    LinearMap.ext fun _ => rfl
  change LinearMap.toMatrix _ _ f = P⁻¹ * LinearMap.toMatrix b₀ b₀ f * P
  rw [LinearMap.toMatrix_map_left, LinearMap.toMatrix_map_right]
  change LinearMap.toMatrix b₀ b₀
      (((Matrix.toLinearEquiv b₀ P hP).symm : V →ₗ[A] V) * f * ((Matrix.toLinearEquiv b₀ P hP : V ≃ₗ[A] V) : V →ₗ[A] V))
    = _
  rw [LinearMap.toMatrix_mul, LinearMap.toMatrix_mul, hg, hgs, LinearMap.toMatrix_toLin, LinearMap.toMatrix_toLin]

theorem toMatrixAlgEquiv_basis_map_eq (b₀ : Basis n A V) (P : Matrix n n A) (hP : IsUnit P.det)
    (f : Module.End A V) (T : Matrix n n A) (h : LinearMap.toMatrixAlgEquiv b₀ f * P = P * T) :
    LinearMap.toMatrixAlgEquiv (b₀.map (Matrix.toLinearEquiv b₀ P hP)) f = T := by
  rw [toMatrixAlgEquiv_basis_map, Matrix.mul_assoc, h, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP,
    Matrix.one_mul]

end WCOTGlueBT1
p2m_reactivate "P2MW.S_GaloisRepAdic_conj_mul_conj_eq_pow_of_isUnipotentOnInertiaAt.WCOTGlueBCore"

namespace WCOTGlueBFinal

open WCOTGlueBCore

variable {R : Type} [CommRing R]

theorem sl2M_B6_eq (s t u : R) : WCOTDevB6.sl2M s t u = sl2M s t u := rfl

theorem sl2M_adapt_eq (s t u : R) : WCOTGlueBAdapt.sl2M s t u = sl2M s t u := rfl

theorem matrix_length_le [IsDomain R] (𝒯 : Set (Matrix (Fin 2) (Fin 2) R)) (t : R) (ht : t ≠ 0)
    (h2 : (2 : R) ≠ 0) (hT₀ : 1 + sl2M 0 t 0 ∈ 𝒯)
    (hsq : ∀ T ∈ 𝒯, (T - 1) * (T - 1) = 0)
    (htr : ∀ T ∈ 𝒯, ((1 + sl2M 0 t 0) * T).trace = 2)
    (F G : Matrix (Fin 2) (Fin 2) R) (hFG : F * G = 1) (hGF : G * F = 1) (q : ℕ)
    (htame : F * (1 + sl2M 0 t 0) * G = (1 + sl2M 0 t 0) ^ q) (hdet : F.det = q) :
    Module.length R (invM 𝒯 ⧸ denM 𝒯 F) ≤ Module.length R (R ⧸ Ideal.span {(q : R) ^ 2 - 1}) := by

  have hline : ∀ T ∈ 𝒯, ∃ b : R, T = 1 + sl2M 0 b 0 := by
    intro T hT
    have hT1 : 1 + (T - 1) = T := by rw [add_comm, sub_add_cancel]
    have hN : (T - 1) * (T - 1) = 0 := hsq T hT
    have hu : ((1 + WCOTDevB6.sl2M 0 t 0) * (1 + (T - 1))).trace = 2 := by
      rw [hT1, sl2M_B6_eq]; exact htr T hT
    have key := WCOTDevB6.eq_line_of_unipotent_mul t ht (T - 1) hN hu
    refine ⟨(T - 1) 0 1, ?_⟩
    rw [← sl2M_B6_eq, ← key, hT1]

  have hE2 : sl2M (0 : R) t 0 * sl2M 0 t 0 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [sl2M, Matrix.mul_apply, Fin.sum_univ_two]
  have hFN : F * sl2M 0 t 0 = (q : R) • (sl2M 0 t 0 * F) :=
    mul_eq_smul_mul_of_conj_pow F G (sl2M 0 t 0) q hFG hGF hE2 htame

  exact length_quotient_le 𝒯 t ht h2 hT₀ hline F (q : R) hFN hdet

end WCOTGlueBFinal
p2m_reactivate "P2MW.S_GaloisRepAdic_conj_mul_conj_eq_pow_of_isUnipotentOnInertiaAt.WCOTGlueBCore"

namespace COTGlue

open WCOTGlueBCore Polynomial

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]

theorem localCotangentTerm_length_le_phaseB (ρ : GaloisRepAdic 𝒪) (q : ℕ)
    (hunip : ∀ P' : ValuationSubring (AlgebraicClosure ℚ), P'.LiesOverPrime q →
      ∀ τ ∈ P'.inertiaSubgroupIn ℚ, LinearMap.charpoly (ρ.ρ τ) = (X - 1) ^ 2)
    (h2 : (2 : 𝒪) ≠ 0)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (_hσ : P.IsFrobeniusAt σ q)
    (τ₀ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hτ₀P : τ₀ ∈ P.inertiaSubgroupIn ℚ)
    (hτ₀ne : ρ.ρ τ₀ ≠ 1)
    (htame : ρ.ρ σ * ρ.ρ τ₀ * ρ.ρ σ⁻¹ = ρ.ρ τ₀ ^ q)
    (hdet : LinearMap.det (ρ.ρ σ) = (q : 𝒪)) :
    Module.length 𝒪 (adZeroInertiaInv ρ P ⧸ localCotangentTermDenom ρ P σ) ≤
      Module.length 𝒪 (𝒪 ⧸ Ideal.span {((q : 𝒪)) ^ 2 - 1}) := by
  classical

  have hchar : ∀ (b : Basis (Fin 2) 𝒪 ρ.V), ∀ τ ∈ P.inertiaSubgroupIn ℚ,
      (endToMatrix ρ b (ρ.ρ τ)).charpoly = (X - 1) ^ 2 := by
    intro b τ hτ
    rw [show endToMatrix ρ b (ρ.ρ τ) = LinearMap.toMatrix b b (ρ.ρ τ) from rfl, LinearMap.charpoly_toMatrix]
    exact hunip P hP τ hτ

  let b₀ : Basis (Fin 2) 𝒪 ρ.V := Module.finBasisOfFinrankEq 𝒪 ρ.V ρ.finrank_eq
  have hN₀sq : (endToMatrix ρ b₀ (ρ.ρ τ₀) - 1) * (endToMatrix ρ b₀ (ρ.ρ τ₀) - 1) = 0 :=
    sub_one_mul_sub_one_eq_zero_of_charpoly _ (hchar b₀ τ₀ hτ₀P)
  have hN₀ne : endToMatrix ρ b₀ (ρ.ρ τ₀) - 1 ≠ 0 := by
    intro h
    apply hτ₀ne
    apply (endToMatrix ρ b₀).injective
    rw [map_one]
    exact sub_eq_zero.mp h

  obtain ⟨Pm, hPm, t, ht, hconj⟩ := WCOTGlueBAdapt.exists_conj_eq_sl2M _ hN₀sq hN₀ne
  rw [WCOTGlueBFinal.sl2M_adapt_eq] at hconj

  let b : Basis (Fin 2) 𝒪 ρ.V := b₀.map (Matrix.toLinearEquiv b₀ Pm hPm)
  have hT₀b : endToMatrix ρ b (ρ.ρ τ₀) = 1 + sl2M 0 t 0 := by
    apply WCOTGlueBT1.toMatrixAlgEquiv_basis_map_eq b₀ Pm hPm
    change endToMatrix ρ b₀ (ρ.ρ τ₀) * Pm = Pm * (1 + sl2M 0 t 0)
    have h1 : endToMatrix ρ b₀ (ρ.ρ τ₀) = 1 + (endToMatrix ρ b₀ (ρ.ρ τ₀) - 1) := by
      rw [add_comm, sub_add_cancel]
    rw [h1, add_mul, one_mul, hconj, Matrix.mul_add, Matrix.mul_one]

  have hT₀ : 1 + sl2M 0 t 0 ∈ (fun τ => endToMatrix ρ b (ρ.ρ τ)) '' (P.inertiaSubgroupIn ℚ) :=
    ⟨τ₀, hτ₀P, hT₀b⟩
  have hsq : ∀ T ∈ (fun τ => endToMatrix ρ b (ρ.ρ τ)) '' (P.inertiaSubgroupIn ℚ), (T - 1) * (T - 1) = 0 := by
    rintro _ ⟨τ, hτ, rfl⟩
    exact sub_one_mul_sub_one_eq_zero_of_charpoly _ (hchar b τ hτ)
  have htr : ∀ T ∈ (fun τ => endToMatrix ρ b (ρ.ρ τ)) '' (P.inertiaSubgroupIn ℚ),
      ((1 + sl2M 0 t 0) * T).trace = 2 := by
    rintro _ ⟨τ, hτ, rfl⟩
    show ((1 + sl2M 0 t 0) * endToMatrix ρ b (ρ.ρ τ)).trace = 2
    rw [← hT₀b, ← map_mul, ← map_mul]
    exact trace_eq_two_of_charpoly _ (hchar b (τ₀ * τ) ((P.inertiaSubgroupIn ℚ).mul_mem hτ₀P hτ))
  have hFG : endToMatrix ρ b (ρ.ρ σ) * endToMatrix ρ b (ρ.ρ σ⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one]
  have hGF : endToMatrix ρ b (ρ.ρ σ⁻¹) * endToMatrix ρ b (ρ.ρ σ) = 1 := by
    rw [← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one]
  have htame_b : endToMatrix ρ b (ρ.ρ σ) * (1 + sl2M 0 t 0) * endToMatrix ρ b (ρ.ρ σ⁻¹) =
      (1 + sl2M 0 t 0) ^ q := by
    rw [← hT₀b, ← map_mul, ← map_mul, htame, map_pow]
  have hdet_b : (endToMatrix ρ b (ρ.ρ σ)).det = (q : 𝒪) := by
    rw [show endToMatrix ρ b (ρ.ρ σ) = LinearMap.toMatrix b b (ρ.ρ σ) from rfl, LinearMap.det_toMatrix]
    exact hdet

  rw [length_localCotangentTerm_eq_invM_quotient ρ b P σ]
  exact WCOTGlueBFinal.matrix_length_le _ t ht h2 hT₀ hsq htr _ _ hFG hGF q htame_b hdet_b

end COTGlue
p2m_reactivate "P2MW.S_GaloisRepAdic_conj_mul_conj_eq_pow_of_isUnipotentOnInertiaAt.WCOTGlueBCore"

namespace WCOTTame3

variable {R : Type} [CommRing R]

theorem eq_zero_of_forall_pow_dvd [IsNoetherianRing R] [IsLocalRing R] (p : R)
    (hp : p ∈ IsLocalRing.maximalIdeal R) (d : R) (h : ∀ k : ℕ, p ^ k ∣ d) : d = 0 := by
  have hmem : d ∈ ⨅ k : ℕ, (IsLocalRing.maximalIdeal R) ^ k := by
    refine Ideal.mem_iInf.mpr fun k => ?_
    obtain ⟨e, rfl⟩ := h k
    exact Ideal.mul_mem_right e _ (Ideal.pow_mem_pow hp k)
  rwa [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal R).ne_top] at hmem

variable {n : Type} [Fintype n] [DecidableEq n] {G : Type} [Group G]

theorem conj_eq_pow_of_tameQ (N : Matrix n n R) (hN : N * N = 0) (hNreg : ∀ a : R, a • N = 0 → a = 0)
    (p : R) (hsep : ∀ d : R, (∀ k : ℕ, p ^ k ∣ d) → d = 0)
    (f : G →* Matrix n n R) (hline : ∀ g, ∃ a : R, f g = 1 + a • N)
    (F F' : Matrix n n R) (κ : G → G) (hκ : ∀ τ, f (κ τ) = F * f τ * F') (q : ℕ) (pn : ℕ → ℕ)
    (hpn : ∀ k, (pn k : R) = p ^ k)
    (htameQ : ∀ k : ℕ, ∀ τ : G, ∃ c ∈ commutator G, ∃ w : G, κ τ = τ ^ q * c * w ^ (pn k)) :
    ∀ τ, F * f τ * F' = (f τ) ^ q := by

  choose a ha using hline
  have hmulN : ∀ x y : R, (1 + x • N) * (1 + y • N) = 1 + (x + y) • N := by
    intro x y
    rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, smul_mul_smul_comm, hN, smul_zero, add_zero, add_smul]
    abel
  have hadd : ∀ g h, a (g * h) = a g + a h := by
    intro g h
    have h1 : f (g * h) = 1 + (a g + a h) • N := by rw [map_mul, ha g, ha h, hmulN]
    rw [ha (g * h)] at h1
    have h2 : (a (g * h) - (a g + a h)) • N = 0 := by rw [sub_smul, sub_eq_zero]; exact add_left_cancel h1
    exact sub_eq_zero.mp (hNreg _ h2)
  have hone : a 1 = 0 := by
    have h1 := hadd 1 1
    rw [mul_one] at h1
    exact add_left_cancel (h1.symm.trans (add_zero _).symm)
  let φ : G →* Multiplicative R :=
    { toFun := fun g => Multiplicative.ofAdd (a g)
      map_one' := by simp [hone]
      map_mul' := fun g h => by simp [hadd, ofAdd_add] }
  have hcomm : ∀ c ∈ commutator G, a c = 0 := by
    intro c hc
    have := Abelianization.commutator_subset_ker φ hc
    rw [MonoidHom.mem_ker] at this
    exact ofAdd_eq_one.mp this
  have hpow : ∀ (w : G) (m : ℕ), a (w ^ m) = (m : R) * a w := by
    intro w m
    induction m with
    | zero => simp [hone]
    | succ m ih => rw [pow_succ, hadd, ih]; push_cast; ring
  have hfpow : ∀ (g : G) (m : ℕ), (f g) ^ m = 1 + ((m : R) * a g) • N := by
    intro g m; rw [← map_pow, ha, hpow]

  intro τ
  set d : R := a (κ τ) - (q : R) * a τ with hd
  have hdvd : ∀ k : ℕ, p ^ k ∣ d := by
    intro k
    obtain ⟨c, hc, w, hw⟩ := htameQ k τ
    have : a (κ τ) = (q : R) * a τ + 0 + (pn k : R) * a w := by
      rw [hw, hadd, hadd, hpow, hcomm c hc, hpow]
    refine ⟨a w, ?_⟩
    rw [hd, this, hpn]; ring
  have hd0 : d = 0 := hsep d hdvd
  have hκa : a (κ τ) = (q : R) * a τ := by rw [← sub_eq_zero]; exact hd0
  rw [← hκ, ha (κ τ), hκa, hfpow]

end WCOTTame3
p2m_reactivate "P2MW.S_GaloisRepAdic_conj_mul_conj_eq_pow_of_isUnipotentOnInertiaAt.WCOTGlueBCore"

namespace COTGlue

open WCOTGlueBCore Polynomial

theorem conj_pow_aux {G : Type} [Group G] (a w : G) (n : ℕ) : (a⁻¹ * w * a) ^ n = a⁻¹ * w ^ n * a := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, pow_succ]; group

theorem sl2M_smul_eq {R : Type} [CommRing R] (b : R) : sl2M (0 : R) b 0 = b • sl2M 0 1 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [sl2M]

theorem frob_tame_rel {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    (ρ : GaloisRepAdic 𝒪) (q : ℕ)
    (hunip : ∀ P' : ValuationSubring (AlgebraicClosure ℚ), P'.LiesOverPrime q →
      ∀ τ ∈ P'.inertiaSubgroupIn ℚ, LinearMap.charpoly (ρ.ρ τ) = (X - 1) ^ 2)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (p : ℕ) (hp𝔪 : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪)
    (hdivI : ∀ (n : ℕ) (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), τ ∈ P.inertiaSubgroupIn ℚ →
      ∃ w : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, w ∈ P.inertiaSubgroupIn ℚ ∧
        w ^ (p ^ n) = σ * τ * σ⁻¹ * (τ ^ q)⁻¹)
    (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hτ : τ ∈ P.inertiaSubgroupIn ℚ) :
    ρ.ρ σ * ρ.ρ τ * ρ.ρ σ⁻¹ = ρ.ρ τ ^ q := by
  classical
  set I := P.inertiaSubgroupIn ℚ with hI

  have hconjI : ∀ τ ∈ I, σ * τ * σ⁻¹ ∈ I := by
    intro τ hτ
    obtain ⟨w, hwI, hw⟩ := hdivI 0 τ hτ
    rw [pow_zero, pow_one] at hw
    have : σ * τ * σ⁻¹ = w * τ ^ q := by rw [hw]; group
    rw [this]
    exact I.mul_mem hwI (I.pow_mem hτ q)
  by_cases hram : ∃ τ₀ ∈ I, ρ.ρ τ₀ ≠ 1
  swap
  ·
    simp only [not_exists, not_and, ne_eq, not_not] at hram
    rw [hram τ hτ, one_pow, mul_one, ← map_mul, mul_inv_cancel, map_one]
  obtain ⟨τ₀, hτ₀P, hτ₀ne⟩ := hram

  have hchar : ∀ (b : Basis (Fin 2) 𝒪 ρ.V), ∀ τ ∈ I, (endToMatrix ρ b (ρ.ρ τ)).charpoly = (X - 1) ^ 2 := by
    intro b τ hτ
    rw [show endToMatrix ρ b (ρ.ρ τ) = LinearMap.toMatrix b b (ρ.ρ τ) from rfl, LinearMap.charpoly_toMatrix]
    exact hunip P hP τ hτ
  let b₀ : Basis (Fin 2) 𝒪 ρ.V := Module.finBasisOfFinrankEq 𝒪 ρ.V ρ.finrank_eq
  have hN₀sq : (endToMatrix ρ b₀ (ρ.ρ τ₀) - 1) * (endToMatrix ρ b₀ (ρ.ρ τ₀) - 1) = 0 :=
    sub_one_mul_sub_one_eq_zero_of_charpoly _ (hchar b₀ τ₀ hτ₀P)
  have hN₀ne : endToMatrix ρ b₀ (ρ.ρ τ₀) - 1 ≠ 0 := by
    intro h
    apply hτ₀ne
    apply (endToMatrix ρ b₀).injective
    rw [map_one]
    exact sub_eq_zero.mp h
  obtain ⟨Pm, hPm, t, ht, hconj⟩ := WCOTGlueBAdapt.exists_conj_eq_sl2M _ hN₀sq hN₀ne
  rw [WCOTGlueBFinal.sl2M_adapt_eq] at hconj
  let b : Basis (Fin 2) 𝒪 ρ.V := b₀.map (Matrix.toLinearEquiv b₀ Pm hPm)
  have hT₀b : endToMatrix ρ b (ρ.ρ τ₀) = 1 + sl2M 0 t 0 := by
    apply WCOTGlueBT1.toMatrixAlgEquiv_basis_map_eq b₀ Pm hPm
    change endToMatrix ρ b₀ (ρ.ρ τ₀) * Pm = Pm * (1 + sl2M 0 t 0)
    have h1 : endToMatrix ρ b₀ (ρ.ρ τ₀) = 1 + (endToMatrix ρ b₀ (ρ.ρ τ₀) - 1) := by
      rw [add_comm, sub_add_cancel]
    rw [h1, add_mul, one_mul, hconj, Matrix.mul_add, Matrix.mul_one]

  have hline' : ∀ τ ∈ I, ∃ a : 𝒪, endToMatrix ρ b (ρ.ρ τ) = 1 + a • sl2M 0 1 0 := by
    intro τ hτ
    set T := endToMatrix ρ b (ρ.ρ τ) with hT
    have hT1 : 1 + (T - 1) = T := by rw [add_comm, sub_add_cancel]
    have hN : (T - 1) * (T - 1) = 0 := sub_one_mul_sub_one_eq_zero_of_charpoly _ (hchar b τ hτ)
    have hu : ((1 + WCOTDevB6.sl2M 0 t 0) * (1 + (T - 1))).trace = 2 := by
      rw [hT1, WCOTGlueBFinal.sl2M_B6_eq, hT, ← hT₀b, ← map_mul, ← map_mul]
      exact trace_eq_two_of_charpoly _ (hchar b (τ₀ * τ) (I.mul_mem hτ₀P hτ))
    have key := WCOTDevB6.eq_line_of_unipotent_mul t ht (T - 1) hN hu
    refine ⟨(T - 1) 0 1, ?_⟩
    rw [← sl2M_smul_eq, ← WCOTGlueBFinal.sl2M_B6_eq, ← key, hT1]

  let f : I →* Matrix (Fin 2) (Fin 2) 𝒪 :=
    ((endToMatrix ρ b).toRingEquiv.toMonoidHom.comp ρ.ρ).comp I.subtype
  have hf : ∀ g : I, f g = endToMatrix ρ b (ρ.ρ g) := fun _ => rfl
  have hline : ∀ g : I, ∃ a : 𝒪, f g = 1 + a • sl2M 0 1 0 := fun g => by rw [hf]; exact hline' g g.2
  have hE2 : sl2M (0 : 𝒪) 1 0 * sl2M 0 1 0 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [sl2M, Matrix.mul_apply, Fin.sum_univ_two]
  have hEreg : ∀ a : 𝒪, a • sl2M (0 : 𝒪) 1 0 = 0 → a = 0 := by
    intro a h
    have := congrFun (congrFun h 0) 1
    simpa [sl2M] using this
  have hsep : ∀ d : 𝒪, (∀ k : ℕ, (p : 𝒪) ^ k ∣ d) → d = 0 := WCOTTame3.eq_zero_of_forall_pow_dvd (p : 𝒪) hp𝔪
  let κ : I → I := fun g => ⟨σ * g * σ⁻¹, hconjI g g.2⟩
  have hκ : ∀ g : I, f (κ g) = endToMatrix ρ b (ρ.ρ σ) * f g * endToMatrix ρ b (ρ.ρ σ⁻¹) := by
    intro g
    rw [hf, hf]
    change endToMatrix ρ b (ρ.ρ (σ * g * σ⁻¹)) = _
    rw [map_mul, map_mul, map_mul, map_mul]
  have htameQ : ∀ (k : ℕ) (g : I), ∃ c ∈ commutator I, ∃ w : I, κ g = g ^ q * c * w ^ (p ^ k) := by
    intro k g
    obtain ⟨w, hwI, hw⟩ := hdivI k g g.2
    refine ⟨1, Subgroup.one_mem _,
      ⟨((g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ^ q)⁻¹ * w * (g : _) ^ q,
        I.mul_mem (I.mul_mem (I.inv_mem (I.pow_mem g.2 q)) hwI) (I.pow_mem g.2 q)⟩, ?_⟩
    apply Subtype.ext
    simp only [κ, Subgroup.coe_mul, OneMemClass.coe_one, SubmonoidClass.coe_pow]
    rw [conj_pow_aux, hw]
    group

  have key := WCOTTame3.conj_eq_pow_of_tameQ (sl2M (0 : 𝒪) 1 0) hE2 hEreg (p : 𝒪) hsep f hline
    (endToMatrix ρ b (ρ.ρ σ)) (endToMatrix ρ b (ρ.ρ σ⁻¹)) κ hκ q (fun k => p ^ k) (fun k => by push_cast; rfl)
    htameQ ⟨τ, hτ⟩
  rw [hf] at key
  apply (endToMatrix ρ b).injective
  rw [map_mul, map_mul, map_pow]
  exact key

end COTGlue
p2m_reactivate "P2MW.S_GaloisRepAdic_conj_mul_conj_eq_pow_of_isUnipotentOnInertiaAt.WCOTGlueBCore"

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    (ρ : GaloisRepAdic 𝒪) (q : ℕ)
    (hunip : ∀ P' : ValuationSubring (AlgebraicClosure ℚ), P'.LiesOverPrime q →
      ∀ τ ∈ P'.inertiaSubgroupIn ℚ, LinearMap.charpoly (ρ.ρ τ) = (Polynomial.X - 1) ^ 2)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (p : ℕ) (hp𝔪 : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪)
    (hdivI : ∀ (n : ℕ) (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), τ ∈ P.inertiaSubgroupIn ℚ →
      ∃ w : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, w ∈ P.inertiaSubgroupIn ℚ ∧
        w ^ (p ^ n) = σ * τ * σ⁻¹ * (τ ^ q)⁻¹)
    (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hτ : τ ∈ P.inertiaSubgroupIn ℚ) :
    ρ.ρ σ * ρ.ρ τ * ρ.ρ σ⁻¹ = ρ.ρ τ ^ q := by
  exact COTGlue.frob_tame_rel ρ q hunip P hP σ p hp𝔪 hdivI τ hτ

end S_GaloisRepAdic_conj_mul_conj_eq_pow_of_isUnipotentOnInertiaAt
end P2MW
export P2MW.S_GaloisRepAdic_conj_mul_conj_eq_pow_of_isUnipotentOnInertiaAt (solution)
