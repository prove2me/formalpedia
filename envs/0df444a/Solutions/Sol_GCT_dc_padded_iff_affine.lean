-- Prove2me | solution 1 for GCT.dc_padded_iff_affine
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T12:54:43.52378+00:00
-- url     : https://prove2.me/submissions/311b4b18-0d3d-49ea-900c-b1e5efcce412

import Definitions.Def_GCT_determinantal_complexity

namespace GCT_4a8940e7

open MvPolynomial

noncomputable def ψ (σ : Type*) : MvPolynomial (Option σ) ℂ →ₐ[ℂ] MvPolynomial σ ℂ :=
  aeval (fun o : Option σ => Option.elim o (1 : MvPolynomial σ ℂ) X)

lemma ψ_monomial {σ : Type*} (d : Option σ →₀ ℕ) (c : ℂ) :
    ψ σ (monomial d c) = monomial d.some c := by
  rw [ψ, aeval_monomial, Finsupp.prod_option_index _ _ (fun _ => pow_zero _)
    (fun _ _ _ => pow_add _ _ _)]
  simp [monomial_eq]

lemma degree_option {σ : Type*} [Fintype σ] (d : Option σ →₀ ℕ) :
    d.degree = d none + d.some.degree := by
  rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum, Fintype.sum_option]
  simp [Finsupp.some_apply]

lemma ψ_eq {σ : Type*} (p : MvPolynomial (Option σ) ℂ) :
    ψ σ p = ∑ v ∈ p.support, monomial v.some (coeff v p) := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  simp [ψ_monomial]

lemma totalDegree_ψ_le {σ : Type*} [Fintype σ] (p : MvPolynomial (Option σ) ℂ) :
    (ψ σ p).totalDegree ≤ p.totalDegree := by
  rw [ψ_eq]
  refine totalDegree_finsetSum_le (fun v hv => ?_)
  refine (totalDegree_monomial_le _ _).trans ?_
  have := le_totalDegree hv
  have h1 : (v.some.sum fun _ => id) = v.some.degree := by
    simp [Finsupp.degree_apply, Finsupp.sum]
  have h2 : (v.sum fun _ e => e) = v.degree := by
    simp [Finsupp.degree_apply, Finsupp.sum]
  rw [h2, degree_option] at this
  rw [h1]
  omega

lemma ψ_inj {σ : Type*} [Fintype σ] [DecidableEq σ] {n : ℕ} {p : MvPolynomial (Option σ) ℂ}
    (hp : p.IsHomogeneous n) (h0 : ψ σ p = 0) : p = 0 := by
  classical
  ext d
  rw [coeff_zero]
  by_cases hd : d.degree = n
  · have := congrArg (coeff d.some) h0
    rw [ψ_eq, coeff_sum, coeff_zero] at this
    rw [Finset.sum_eq_single d] at this
    · simpa using this
    · intro e he hne
      rw [coeff_monomial, if_neg]
      intro hes
      apply hne
      have he' : e.degree = n := by
        by_contra hc
        exact (mem_support_iff.mp he) (hp.coeff_eq_zero hc)
      rw [degree_option] at he' hd
      have key : e none = d none := by rw [hes] at he'; omega
      refine Finsupp.ext fun o => ?_
      cases o with
      | none => exact key
      | some a => simpa [Finsupp.some_apply] using DFunLike.congr_fun hes a
    · intro hd'
      rw [notMem_support_iff] at hd'
      simp [hd']
  · exact hp.coeff_eq_zero hd

lemma det_homog {σ : Type*} {n : ℕ} (B : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ))
    (hB : ∀ i j, (B i j).IsHomogeneous 1) : B.det.IsHomogeneous n := by
  rw [Matrix.det_apply']
  refine IsHomogeneous.sum _ _ _ (fun s _ => ?_)
  have h1 : ((((Equiv.Perm.sign s : ℤ)) : MvPolynomial σ ℂ)).IsHomogeneous 0 := by
    rw [← map_intCast (C : ℂ →+* MvPolynomial σ ℂ)]
    exact isHomogeneous_C _ _
  have h2 := IsHomogeneous.prod Finset.univ (fun i => B (s i) i) (fun _ => 1)
    (fun i _ => hB _ _)
  simpa using h1.mul h2

end GCT_4a8940e7

open GCT_4a8940e7 MvPolynomial in
theorem solution (m n : ℕ) (hmn : m ≤ n) :
    GCT.HasLinearDetRep n (GCT.paddedPerm m n) ↔ GCT.HasAffineDetRep n (GCT.permPoly m) := by
  have hψP : ψ (Fin m × Fin m) (GCT.paddedPerm m n) = GCT.permPoly m := by
    simp [GCT.paddedPerm, GCT.permPolyPad, GCT.permPoly, Matrix.permanent, ψ, map_sum, map_prod]
  constructor
  · rintro ⟨A, hA, hdet⟩
    refine ⟨(ψ _).mapMatrix A, fun i j => ?_, ?_⟩
    · exact (totalDegree_ψ_le _).trans (hA i j).totalDegree_le
    · rw [← AlgHom.map_det, hdet, hψP]
  · rintro ⟨A, hA, hdet⟩
    let B : Matrix (Fin n) (Fin n) (MvPolynomial (GCT.PadVars m) ℂ) := fun i j =>
      C (coeff 0 (A i j)) * X none + rename some (homogeneousComponent 1 (A i j))
    have hB : ∀ i j, (B i j).IsHomogeneous 1 := fun i j =>
      (isHomogeneous_C_mul_X _ _).add
        (homogeneousComponent_isHomogeneous 1 _).rename_isHomogeneous
    have hBA : (ψ _).mapMatrix B = A := by
      refine Matrix.ext fun i j => ?_
      show ψ _ (C (coeff 0 (A i j)) * X none + rename some (homogeneousComponent 1 (A i j))) = A i j
      rw [map_add, map_mul, ψ, aeval_C, aeval_X, aeval_rename]
      have hc : ((fun o : Option (Fin m × Fin m) => Option.elim o
          (1 : MvPolynomial (Fin m × Fin m) ℂ) X) ∘ some) = X := rfl
      rw [hc, aeval_X_left]
      simp only [Option.elim_none, mul_one, AlgHom.id_apply, algebraMap_eq]
      rw [← homogeneousComponent_zero]
      conv_rhs => rw [← sum_homogeneousComponent (A i j)]
      have h1 := hA i j
      rcases Nat.lt_or_ge (A i j).totalDegree 1 with h | h
      · have h0 : (A i j).totalDegree = 0 := by omega
        rw [h0, homogeneousComponent_eq_zero 1 _ (by omega)]
        simp
      · have h0 : (A i j).totalDegree = 1 := by omega
        rw [h0, Finset.sum_range_succ, Finset.sum_range_one]
    refine ⟨B, hB, ?_⟩
    have hpad : (GCT.paddedPerm m n).IsHomogeneous n := by
      have h1 := isHomogeneous_X_pow (R := ℂ) (none : GCT.PadVars m) (n - m)
      have h2 : (GCT.permPolyPad m).IsHomogeneous m := by
        unfold GCT.permPolyPad Matrix.permanent
        refine IsHomogeneous.sum _ _ _ (fun s _ => ?_)
        simpa using IsHomogeneous.prod Finset.univ
          (fun i => (Matrix.of fun i j => (X (some (i, j)) : MvPolynomial (GCT.PadVars m) ℂ)) (s i) i)
          (fun _ => 1) (fun i _ => isHomogeneous_X _ _)
      have := h1.mul h2
      rwa [Nat.sub_add_cancel hmn] at this
    have hsub := (det_homog B hB).sub hpad
    have := ψ_inj hsub (by rw [map_sub, AlgHom.map_det, hBA, hdet, hψP, sub_self])
    exact sub_eq_zero.mp this
