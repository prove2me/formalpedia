-- Prove2me | solution 1 for DeepQOperator.spectral_tail
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-22T19:48:03.918461+00:00
-- url     : https://prove2.me/submissions/b27f9e52-2723-48e9-abe2-b4be3ab31adc

import Mathlib

open Matrix

namespace DeepQOperator.SpectralTailAux

/-- Ky Fan type bound: weights in `[0,1]` of total mass at most `N` against a nonnegative
decreasing sequence give at most the sum of the first `N` terms. -/
lemma comb {m N : ℕ} (μ w : Fin m → ℝ) (hμ : Antitone μ) (hμ0 : ∀ k, 0 ≤ μ k)
    (hw0 : ∀ k, 0 ≤ w k) (hw1 : ∀ k, w k ≤ 1) (hsum : ∑ k, w k ≤ N) :
    ∑ k, w k * μ k ≤ ∑ k ∈ Finset.univ.filter (fun k : Fin m => k.val < N), μ k := by
  by_cases h : N < m
  · set c := μ ⟨N, h⟩ with hc
    have hc0 : 0 ≤ c := hμ0 _
    have key : ∀ k, w k * μ k ≤ (if k.val < N then μ k else 0)
        + c * (w k - if k.val < N then 1 else 0) := by
      intro k
      split_ifs with hk
      · have : c ≤ μ k := hμ (show k ≤ ⟨N, h⟩ from Fin.mk_le_mk.mpr hk.le)
        nlinarith [hw1 k]
      · have : μ k ≤ c := hμ (show (⟨N, h⟩ : Fin m) ≤ k from Fin.mk_le_mk.mpr (by omega))
        nlinarith [hw0 k]
    have hcard : ∑ k : Fin m, (if k.val < N then (1:ℝ) else 0) = N := by
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
        mul_one]
      have : (Finset.univ.filter (fun k : Fin m => k.val < N)).card = N := by
        rw [Fin.card_filter_val_lt]
        omega
      rw [this]
    calc ∑ k, w k * μ k ≤ ∑ k, ((if k.val < N then μ k else 0)
        + c * (w k - if k.val < N then 1 else 0)) := Finset.sum_le_sum (fun k _ => key k)
      _ = ∑ k ∈ Finset.univ.filter (fun k : Fin m => k.val < N), μ k
          + c * (∑ k, w k - N) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hcard,
          Finset.sum_ite, Finset.sum_const_zero, add_zero]
      _ ≤ _ := by nlinarith
  · have hf : Finset.univ.filter (fun k : Fin m => k.val < N) = Finset.univ := by
      ext k; simp; omega
    rw [hf]
    exact Finset.sum_le_sum (fun k _ => by nlinarith [hw1 k, hμ0 k])

/-- The trace computed in the orthonormal eigenbasis of a Hermitian matrix. -/
lemma trace_eq_sum_basis {d : ℕ} (B A : Matrix (Fin d) (Fin d) ℝ) (hB : B.IsHermitian) :
    A.trace = ∑ b, (⇑(hB.eigenvectorBasis b)) ⬝ᵥ (A *ᵥ ⇑(hB.eigenvectorBasis b)) := by
  have hU := Unitary.coe_mul_star_self hB.eigenvectorUnitary
  have hδ : ∀ a c, ∑ b, (hB.eigenvectorBasis b) a * (hB.eigenvectorBasis b) c
      = (1 : Matrix (Fin d) (Fin d) ℝ) a c := by
    intro a c
    rw [← hU, Matrix.mul_apply]
    simp [Matrix.star_apply]
  calc A.trace = ∑ a, ∑ c, A a c * (1 : Matrix (Fin d) (Fin d) ℝ) a c := by
        simp [Matrix.trace, Matrix.one_apply]
    _ = ∑ a, ∑ c, ∑ b, A a c * ((hB.eigenvectorBasis b) a * (hB.eigenvectorBasis b) c) := by
        simp_rw [← hδ, Finset.mul_sum]
    _ = ∑ a, ∑ b, ∑ c, (hB.eigenvectorBasis b) a * (A a c * (hB.eigenvectorBasis b) c) := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => ?_))
        ring
    _ = _ := by
        rw [Finset.sum_comm]
        simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]

lemma trace_eq_rank_of_idem {d : ℕ} (P : Matrix (Fin d) (Fin d) ℝ) (hP : P * P = P) :
    P.trace = (P.rank : ℝ) := by
  have hid : IsIdempotentElem (Matrix.toLin' P) := by
    have h := congrArg Matrix.toLin' hP
    rw [Matrix.toLin'_mul] at h
    exact h
  rw [← Matrix.trace_toLin'_eq,
    (LinearMap.IsIdempotentElem.isProj_range (Matrix.toLin' P) hid).trace, Matrix.rank]
  rfl

lemma quad_eq {d : ℕ} (P : Matrix (Fin d) (Fin d) ℝ) (hPh : P.IsHermitian) (hP : P * P = P)
    (u : Fin d → ℝ) : u ⬝ᵥ (P *ᵥ u) = (P *ᵥ u) ⬝ᵥ (P *ᵥ u) := by
  have hT : Pᵀ = P := by
    have := hPh.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  conv_lhs => rw [← hP, ← Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hT]

lemma quad_nonneg {d : ℕ} (P : Matrix (Fin d) (Fin d) ℝ) (hPh : P.IsHermitian) (hP : P * P = P)
    (u : Fin d → ℝ) : 0 ≤ u ⬝ᵥ (P *ᵥ u) := by
  rw [quad_eq P hPh hP u]
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)

lemma basis_self {d : ℕ} (B : Matrix (Fin d) (Fin d) ℝ) (hB : B.IsHermitian) (b : Fin d) :
    (⇑(hB.eigenvectorBasis b)) ⬝ᵥ (⇑(hB.eigenvectorBasis b)) = 1 := by
  have hU := Unitary.coe_star_mul_self hB.eigenvectorUnitary
  have h := congrFun (congrFun hU b) b
  rw [Matrix.mul_apply] at h
  simpa [Matrix.star_apply, dotProduct] using h

lemma rank_le_of_ker {d k : ℕ} (M : Matrix (Fin k) (Fin d) ℝ) (P : Matrix (Fin d) (Fin d) ℝ)
    (h : ∀ x, M *ᵥ x = 0 → P *ᵥ x = 0) : P.rank ≤ M.rank := by
  have hker : LinearMap.ker M.mulVecLin ≤ LinearMap.ker P.mulVecLin := by
    intro x hx
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hx ⊢
    exact h x hx
  have h1 := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  have h2 := LinearMap.finrank_range_add_finrank_ker P.mulVecLin
  have h3 := Submodule.finrank_mono hker
  unfold Matrix.rank
  omega

end DeepQOperator.SpectralTailAux

open DeepQOperator.SpectralTailAux in
theorem solution {d N : ℕ} (B Pi : Matrix (Fin d) (Fin d) ℝ) (hB : B.PosSemidef)
    (hPh : Pi.IsHermitian) (hPi : Pi * Pi = Pi) :
    (∀ {k : ℕ} (M : Matrix (Fin k) (Fin d) ℝ), M.rank ≤ N → (∀ x, M *ᵥ (Pi *ᵥ x) = 0) →
      (∀ x, M *ᵥ x = 0 → Pi *ᵥ x = x) →
        (1 - Pi).IsHermitian ∧ (1 - Pi) * (1 - Pi) = 1 - Pi ∧ (1 - Pi).rank ≤ N) ∧
    ((1 - Pi).rank ≤ N →
      ((1 - Pi) * B).trace ≤
          ∑ k ∈ Finset.univ.filter (fun k : Fin (Fintype.card (Fin d)) => k.val < N),
            hB.isHermitian.eigenvalues₀ k ∧
        ∑ k ∈ Finset.univ.filter (fun k : Fin (Fintype.card (Fin d)) => N ≤ k.val),
            hB.isHermitian.eigenvalues₀ k ≤ (Pi * B).trace) := by
  have hQh : (1 - Pi).IsHermitian := Matrix.isHermitian_one.sub hPh
  have hQ : (1 - Pi) * (1 - Pi) = 1 - Pi := by
    rw [sub_mul, mul_sub, mul_sub, hPi]
    simp
  refine ⟨fun M hM _ hfix => ⟨hQh, hQ, ?_⟩, fun hrank => ?_⟩
  · refine le_trans (rank_le_of_ker M (1 - Pi) (fun x hx => ?_)) hM
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hfix x hx, sub_self]
  set hBh := hB.isHermitian
  set u : Fin d → (Fin d → ℝ) := fun b => ⇑(hBh.eigenvectorBasis b) with hu
  set e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin d))) with he
  have hev : ∀ k, hBh.eigenvalues (e k) = hBh.eigenvalues₀ k := by
    intro k
    simp [Matrix.IsHermitian.eigenvalues, he]
  have htr : ((1 - Pi) * B).trace
      = ∑ k, (u (e k) ⬝ᵥ ((1 - Pi) *ᵥ u (e k))) * hBh.eigenvalues₀ k := by
    rw [trace_eq_sum_basis B _ hBh, ← Equiv.sum_comp e]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← Matrix.mulVec_mulVec, hBh.mulVec_eigenvectorBasis, Matrix.mulVec_smul,
      dotProduct_smul, hev, smul_eq_mul, mul_comm]
  have hsumw : ∑ k, (u (e k) ⬝ᵥ ((1 - Pi) *ᵥ u (e k))) = ((1 - Pi).rank : ℝ) := by
    rw [← trace_eq_rank_of_idem _ hQ, trace_eq_sum_basis B _ hBh, ← Equiv.sum_comp e]
  have hfirst : ((1 - Pi) * B).trace ≤
      ∑ k ∈ Finset.univ.filter (fun k : Fin (Fintype.card (Fin d)) => k.val < N),
        hBh.eigenvalues₀ k := by
    rw [htr]
    refine comb _ _ hBh.eigenvalues₀_antitone ?_ ?_ ?_ ?_
    · intro k
      rw [← hev]
      exact hB.eigenvalues_nonneg _
    · intro k
      exact quad_nonneg _ hQh hQ _
    · intro k
      have h1 := quad_nonneg _ hPh hPi (u (e k))
      have h2 := basis_self B hBh (e k)
      have h3 : u (e k) ⬝ᵥ ((1 - Pi) *ᵥ u (e k))
          = u (e k) ⬝ᵥ u (e k) - u (e k) ⬝ᵥ (Pi *ᵥ u (e k)) := by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub]
      rw [h3]
      simp only [hu] at h1 ⊢
      linarith
    · rw [hsumw]
      exact_mod_cast hrank
  refine ⟨hfirst, ?_⟩
  have htB : B.trace = ∑ k, hBh.eigenvalues₀ k := by
    rw [hBh.trace_eq_sum_eigenvalues, ← Equiv.sum_comp e]
    simp only [hev]
    rfl
  have hsplit : ∑ k, hBh.eigenvalues₀ k
      = ∑ k ∈ Finset.univ.filter (fun k : Fin (Fintype.card (Fin d)) => k.val < N),
          hBh.eigenvalues₀ k
        + ∑ k ∈ Finset.univ.filter (fun k : Fin (Fintype.card (Fin d)) => N ≤ k.val),
          hBh.eigenvalues₀ k := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun k : Fin _ => k.val < N)]
    congr 1
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext k
    simp
  have hPB : (Pi * B).trace = B.trace - ((1 - Pi) * B).trace := by
    rw [sub_mul, one_mul, Matrix.trace_sub]
    ring
  linarith
