-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.CoefficientBoundLemmas.key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:27:18.104657+00:00
-- url     : https://prove2.me/submissions/0e125bd0-f2de-4082-8d8a-50e2d5d559de

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_CoefficientBoundHolds
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_CoefficientBoundLemmas_addVal_prod
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_CoefficientBoundLemmas_length_quot_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.NormUnitaryCountingLemmas Formalism.NormUnitaryCountingLemmas.CoefficientBoundLemmas
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
namespace Formalism.NormUnitaryCountingLemmas.CoefficientBoundLemmas
theorem _root_.solution {ρ : ℕ} (P : Submodule R (Fin ρ → R)) (n : ℕ)
    (hP : Module.length R ((Fin ρ → R) ⧸ P) ≤ n) (ϖ : R) (hϖ : Irreducible ϖ) :
    ∃ G : Matrix (Fin ρ) (Fin ρ) R, (∀ i, G i ∈ P) ∧ G.det ∣ ϖ ^ n := by
  classical
  obtain ⟨n', snf⟩ := P.smithNormalForm (Pi.basisFun R (Fin ρ))
  have hsurj : Function.Surjective snf.f := by
    by_contra h
    obtain ⟨k, hk⟩ : ∃ k, k ∉ Set.range snf.f := by
      simp only [Function.Surjective, not_forall] at h
      obtain ⟨k, hk⟩ := h
      exact ⟨k, by simpa using hk⟩
    let L : (Fin ρ → R) →ₗ[R] R ⧸ Ideal.span ({0} : Set R) :=
      (Ideal.span ({0} : Set R)).mkQ ∘ₗ snf.bM.coord k
    have hle : P ≤ LinearMap.ker L := fun x hx => by
      have := snf.le_ker_coord_of_notMem_range hk hx
      rw [LinearMap.mem_ker] at this ⊢
      simp [L, this]
    have hLs : Function.Surjective (P.liftQ L hle) := by
      intro y
      obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      exact ⟨Submodule.Quotient.mk (r • snf.bM k), by
        simp [L]; rw [Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq]⟩
    have h1 := Module.length_le_of_surjective (P.liftQ L hle) hLs
    rw [length_quot_zero] at h1
    exact absurd (h1.trans hP) (by simp)
  let σ : Fin n' ≃ Fin ρ := Equiv.ofBijective snf.f ⟨snf.f.injective, hsurj⟩
  have hσ : ∀ k, snf.f (σ.symm k) = k := fun k => σ.apply_symm_apply k
  let c : Fin ρ → R := fun k => snf.a (σ.symm k)
  let G : Matrix (Fin ρ) (Fin ρ) R := fun k => (snf.bN (σ.symm k) : Fin ρ → R)
  have hGrow : ∀ k, G k = c k • snf.bM k := fun k => by
    simp only [G, c, snf.snf, hσ]
  refine ⟨G, fun k => (snf.bN (σ.symm k)).2, ?_⟩

  have hdetG : G.det = (∏ k, c k) * (Matrix.of fun k j => snf.bM k j).det := by
    rw [← Matrix.det_mul_column]
    congr 1
    ext k j
    simp [hGrow]
  have hunit : IsUnit (Matrix.of fun k j => snf.bM k j).det := by
    have := (Pi.basisFun R (Fin ρ)).isUnit_det snf.bM
    rw [Basis.det_apply] at this
    have heq : (Matrix.of fun k j => snf.bM k j) = ((Pi.basisFun R (Fin ρ)).toMatrix snf.bM).transpose := by
      ext k j; simp [Basis.toMatrix_apply]
    rw [heq, Matrix.det_transpose]; exact this

  let L : (Fin ρ → R) →ₗ[R] (Π k : Fin ρ, R ⧸ Ideal.span ({c k} : Set R)) :=
    LinearMap.pi fun k => (Ideal.span ({c k} : Set R)).mkQ ∘ₗ snf.bM.coord k
  have hle : P ≤ LinearMap.ker L := fun x hx => by
    rw [LinearMap.mem_ker]
    funext k
    simp only [L, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.mkQ_apply, Pi.zero_apply,
      Submodule.Quotient.mk_eq_zero, Basis.coord_apply]
    have := snf.repr_apply_embedding_eq_repr_smul ⟨x, hx⟩ (i := σ.symm k)
    rw [hσ] at this
    simp only at this
    rw [this, map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  have hLs : Function.Surjective (P.liftQ L hle) := by
    intro y
    choose r hr using fun k => Submodule.Quotient.mk_surjective _ (y k)
    refine ⟨Submodule.Quotient.mk (snf.bM.equivFun.symm r), ?_⟩
    funext k
    have hrep : snf.bM.repr (snf.bM.equivFun.symm r) k = r k := by
      rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    simp only [L, Submodule.liftQ_apply, LinearMap.pi_apply, LinearMap.comp_apply,
      Basis.coord_apply, hrep, Submodule.mkQ_apply, hr]
  have h1 := Module.length_le_of_surjective (P.liftQ L hle) hLs
  rw [Module.length_pi_of_fintype] at h1
  have h2 : IsDiscreteValuationRing.addVal R (∏ k, c k) ≤ IsDiscreteValuationRing.addVal R (ϖ ^ n) := by
    rw [addVal_prod, IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hϖ]
    simp only [nsmul_eq_mul, mul_one]
    refine le_trans (le_of_eq ?_) (h1.trans hP)
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Ring.ord_eq_addVal]; rfl
  rw [IsDiscreteValuationRing.addVal_le_iff_dvd] at h2
  rw [hdetG]
  exact (IsUnit.mul_right_dvd hunit).mpr h2
end Formalism.NormUnitaryCountingLemmas.CoefficientBoundLemmas
