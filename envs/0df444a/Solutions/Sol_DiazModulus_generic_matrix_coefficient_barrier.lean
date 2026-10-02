-- Prove2me | solution 1 for DiazModulus.generic_matrix_coefficient_barrier
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-01T12:35:39.24627+00:00
-- url     : https://prove2.me/submissions/5f184277-f581-4041-bb40-f2f06f91a198

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_generic_no_homogeneous_relation
import Theorems.Thm_Transcendence_singular_matrix_subspace_annihilating_pair

open Complex ComplexConjugate Matrix

namespace GenericMatrixCoefficientBarrier

open DiazModulus

/-- If `M = A u + B ū + C iπ` with `A, B, C` over `Q̄` and `det M = 0`, then every `Q̄`-combination
`a A + b B + c C` is singular: `det (X₀ A + X₁ B + X₂ C)` is homogeneous of degree `n` and vanishes
at `(u, ū, iπ)`, so it is the zero polynomial by `generic_no_homogeneous_relation`. -/
theorem det_comb_eq_zero (u : ℂ) (hu : u ≠ 0) (hρ : IsAlgebraic ℚ (u * conj u))
    (hgen : AlgebraicIndependent (↥Qbar) ![u, ((Real.pi : ℝ) : ℂ) * Complex.I]) {n : ℕ}
    (A B C : Matrix (Fin n) (Fin n) ↥Qbar) (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : ∀ i j, M i j = (A i j : ℂ) * u + (B i j : ℂ) * conj u +
      (C i j : ℂ) * (((Real.pi : ℝ) : ℂ) * Complex.I))
    (hdet : M.det = 0) (a b c : ↥Qbar) : (a • A + b • B + c • C).det = 0 := by
  classical
  set N : Matrix (Fin n) (Fin n) (MvPolynomial (Fin 3) ↥Qbar) := Matrix.of fun i j =>
    MvPolynomial.C (A i j) * MvPolynomial.X 0 + MvPolynomial.C (B i j) * MvPolynomial.X 1 +
      MvPolynomial.C (C i j) * MvPolynomial.X 2 with hN
  have hPh : N.det.IsHomogeneous n := by
    rw [det_apply']
    refine MvPolynomial.IsHomogeneous.sum _ _ _ fun σ _ => ?_
    have hprod := MvPolynomial.IsHomogeneous.prod Finset.univ (fun i => N (σ i) i) (fun _ => 1)
      fun i _ => ((MvPolynomial.isHomogeneous_C_mul_X _ _).add
        (MvPolynomial.isHomogeneous_C_mul_X _ _)).add (MvPolynomial.isHomogeneous_C_mul_X _ _)
    have hsign : (((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin 3) ↥Qbar)).IsHomogeneous 0 := by
      rw [← map_intCast (MvPolynomial.C : ↥Qbar →+* MvPolynomial (Fin 3) ↥Qbar)]
      exact MvPolynomial.isHomogeneous_C _ _
    simpa using hsign.mul hprod
  have hPe : MvPolynomial.aeval ![u, conj u, ((Real.pi : ℝ) : ℂ) * Complex.I] N.det = 0 := by
    rw [AlgHom.map_det, ← hdet]
    congr 1
    ext i j
    simp [hN, hM]
    rfl
  have hP0 := generic_no_homogeneous_relation u hu hρ hgen N.det hPh hPe
  have hev : (a • A + b • B + c • C).det = MvPolynomial.eval ![a, b, c] N.det := by
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp [hN]
    ring
  rw [hev, hP0, map_zero]

/-- `wᵀ M v`, for `M = A x + B y + C z` and `v, w` pushed forward along `φ`. -/
theorem dot_eq {K : Type*} [CommRing K] (φ : K →+* ℂ) {n : ℕ} (A B C : Matrix (Fin n) (Fin n) K)
    (x y z : ℂ) (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : ∀ i j, M i j = φ (A i j) * x + φ (B i j) * y + φ (C i j) * z) (v w : Fin n → K) :
    (fun i => φ (w i)) ⬝ᵥ (M *ᵥ fun i => φ (v i)) =
      x * φ (w ⬝ᵥ (A *ᵥ v)) + y * φ (w ⬝ᵥ (B *ᵥ v)) + z * φ (w ⬝ᵥ (C *ᵥ v)) := by
  simp only [dotProduct, mulVec, map_sum, map_mul, hM, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- Elements of the span of `A, B, C` are combinations `a A + b B + c C`. -/
theorem mem_span_triple {F : Type*} [Field F] {n : ℕ} {A B C X : Matrix (Fin n) (Fin n) F}
    (hX : X ∈ Submodule.span F ({A, B, C} : Set (Matrix (Fin n) (Fin n) F))) :
    ∃ a b c : F, X = a • A + b • B + c • C := by
  obtain ⟨a, Z, hZ, rfl⟩ := Submodule.mem_span_insert.1 hX
  obtain ⟨b, c, rfl⟩ := Submodule.mem_span_pair.1 hZ
  exact ⟨a, b, c, (add_assoc _ _ _).symm⟩

end GenericMatrixCoefficientBarrier

open GenericMatrixCoefficientBarrier DiazModulus in
/-- Both parts reduce to Roy's lemma for the span of the coefficient matrices `A, B, C`, whose
elements are all singular by `det_comb_eq_zero`. Over `ℚ` the rational coefficient matrices are first
pushed into `Q̄`. For `n = 0` the hypothesis `det M = 0` is false, so nothing is special. -/
theorem solution (u : ℂ) (hu : u ≠ 0)
    (hρ : IsAlgebraic ℚ (u * conj u))
    (hgen : AlgebraicIndependent (↥Qbar) ![u, ((Real.pi : ℝ) : ℂ) * Complex.I]) (n : ℕ) :
    (∀ M : Matrix (Fin n) (Fin n) ℂ,
      (∀ i j, ∃ a b c : ℚ, M i j = a * u + b * conj u + c * (((Real.pi : ℝ) : ℂ) * Complex.I)) →
      M.det = 0 →
      ∃ v w : Fin n → ℚ, v ≠ 0 ∧ w ≠ 0 ∧
        (fun i => (w i : ℂ)) ⬝ᵥ (M *ᵥ (fun i => (v i : ℂ))) = 0) ∧
    (∀ M : Matrix (Fin n) (Fin n) ℂ,
      (∀ i j, M i j ∈ Submodule.span Qbar ({u, conj u, ((Real.pi : ℝ) : ℂ) * Complex.I} : Set ℂ)) →
      M.det = 0 →
      ∃ v w : Fin n → ℂ, v ≠ 0 ∧ w ≠ 0 ∧ (∀ i, v i ∈ Qbar) ∧ (∀ i, w i ∈ Qbar) ∧
        w ⬝ᵥ (M *ᵥ v) = 0) := by
  classical
  refine ⟨fun M hM hdet => ?_, fun M hM hdet => ?_⟩
  · -- the `ℚ` part
    choose A B C hABC using hM
    set ι : ℚ →+* ↥Qbar := Rat.castHom ↥Qbar
    have hcast : ∀ q : ℚ, ((ι q : ↥Qbar) : ℂ) = (q : ℂ) := fun q => by simp [ι]
    have hE : ∀ X ∈ Submodule.span ℚ
        ({Matrix.of A, Matrix.of B, Matrix.of C} : Set (Matrix (Fin n) (Fin n) ℚ)), X.det = 0 := by
      intro X hX
      obtain ⟨a, b, c, rfl⟩ := mem_span_triple hX
      apply ι.injective
      rw [RingHom.map_det, map_zero]
      have h0 := det_comb_eq_zero u hu hρ hgen ((Matrix.of A).map ι) ((Matrix.of B).map ι)
        ((Matrix.of C).map ι) M (fun i j => by simp only [map_apply, of_apply, hcast]; exact hABC i j)
        hdet (ι a) (ι b) (ι c)
      convert h0 using 2
      ext i j
      simp
    obtain ⟨v, w, hv, hw, hvw⟩ := Transcendence.singular_matrix_subspace_annihilating_pair _ hE
    refine ⟨v, w, hv, hw, ?_⟩
    have h := dot_eq (Rat.castHom ℂ) (Matrix.of A) (Matrix.of B) (Matrix.of C) u (conj u)
      (((Real.pi : ℝ) : ℂ) * Complex.I) M (fun i j => hABC i j) v w
    simp only [Rat.coe_castHom] at h
    rw [h, hvw _ (Submodule.subset_span (by simp)), hvw _ (Submodule.subset_span (by simp)),
      hvw _ (Submodule.subset_span (by simp))]
    simp
  · -- the `Q̄` part
    have hM' : ∀ i j, ∃ a b c : ↥Qbar,
        M i j = (a : ℂ) * u + (b : ℂ) * conj u + (c : ℂ) * (((Real.pi : ℝ) : ℂ) * Complex.I) := by
      intro i j
      obtain ⟨a, z, hz, hza⟩ := Submodule.mem_span_insert.1 (hM i j)
      obtain ⟨b, c, rfl⟩ := Submodule.mem_span_pair.1 hz
      exact ⟨a, b, c, by rw [hza, add_assoc]; rfl⟩
    choose A B C hABC using hM'
    have hE : ∀ X ∈ Submodule.span ↥Qbar
        ({Matrix.of A, Matrix.of B, Matrix.of C} : Set (Matrix (Fin n) (Fin n) ↥Qbar)),
        X.det = 0 := by
      intro X hX
      obtain ⟨a, b, c, rfl⟩ := mem_span_triple hX
      exact det_comb_eq_zero u hu hρ hgen _ _ _ M hABC hdet a b c
    obtain ⟨v, w, hv, hw, hvw⟩ := Transcendence.singular_matrix_subspace_annihilating_pair _ hE
    refine ⟨fun i => (v i : ℂ), fun i => (w i : ℂ), ?_, ?_, fun i => (v i).2, fun i => (w i).2, ?_⟩
    · intro h0
      exact hv (funext fun i => by simpa using congrFun h0 i)
    · intro h0
      exact hw (funext fun i => by simpa using congrFun h0 i)
    have h := dot_eq Qbar.subtype (Matrix.of A) (Matrix.of B) (Matrix.of C) u (conj u)
      (((Real.pi : ℝ) : ℂ) * Complex.I) M (fun i j => hABC i j) v w
    rw [show (fun i => (w i : ℂ)) = fun i => Qbar.subtype (w i) from rfl,
      show (fun i => (v i : ℂ)) = fun i => Qbar.subtype (v i) from rfl, h,
      hvw _ (Submodule.subset_span (by simp)), hvw _ (Submodule.subset_span (by simp)),
      hvw _ (Submodule.subset_span (by simp))]
    simp
