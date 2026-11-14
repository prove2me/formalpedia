-- Prove2me | solution 1 for BosonicLearn.occupation_count_separation
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-14T02:19:18.360751+00:00
-- url     : https://prove2.me/submissions/f006da39-f6b9-45a0-8699-f3c1098f07a6

import Mathlib
import Definitions.Def_BosonicLearn_fugacityCoeff
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Theorems.Thm_BosonicLearn_geometric_threshold_scaled
import Theorems.Thm_BosonicLearn_fugacity_count_pgf
import Theorems.Thm_BosonicLearn_fugacity_count_test
import Theorems.Thm_BosonicLearn_loewner_eigenvalue_pairing

open QAlgorithms.Papers.Independent.Dependency50.P33 (traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped ENNReal Matrix ComplexOrder

open BosonicLearn

noncomputable section

/-- Unitary diagonalization of a Hermitian matrix, in the form `U D Uᴴ = diag(e)`. -/
private lemma diag_data {n : ℕ} (D : Matrix (Fin n) (Fin n) ℂ) (hD : D.IsHermitian) :
    ∃ (U : Matrix (Fin n) (Fin n) ℂ) (e : Fin n → ℝ), Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      U * D * Uᴴ = Matrix.diagonal (fun i => ((e i : ℝ) : ℂ)) := by
  obtain ⟨V, hVdef⟩ : ∃ V : Matrix (Fin n) (Fin n) ℂ,
      V = (hD.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) := ⟨_, rfl⟩
  have hV1 : Vᴴ * V = 1 := by
    rw [← Matrix.star_eq_conjTranspose, hVdef]
    exact Unitary.coe_star_mul_self _
  have hV2 : V * Vᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose, hVdef]
    exact Unitary.coe_mul_star_self _
  have hspec : D = V * Matrix.diagonal (fun i => ((hD.eigenvalues i : ℝ) : ℂ)) * Vᴴ := by
    have h := hD.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    rw [hVdef, ← Matrix.star_eq_conjTranspose]
    exact h
  refine ⟨Vᴴ, hD.eigenvalues, ?_, ?_, ?_⟩
  · rw [Matrix.conjTranspose_conjTranspose]; exact hV2
  · rw [Matrix.conjTranspose_conjTranspose]; exact hV1
  · rw [Matrix.conjTranspose_conjTranspose]
    conv_lhs => rw [hspec]
    have h : Vᴴ * (V * Matrix.diagonal (fun i => ((hD.eigenvalues i : ℝ) : ℂ)) * Vᴴ) * V =
        (Vᴴ * V) * Matrix.diagonal (fun i => ((hD.eigenvalues i : ℝ) : ℂ)) * (Vᴴ * V) := by
      simp only [Matrix.mul_assoc]
    rw [h, hV1, Matrix.one_mul, Matrix.mul_one]

/-- Spectral data of a traceless Hermitian matrix with `-b ⪯ D ⪯ b`. -/
private lemma spec_facts {n : ℕ} (D : Matrix (Fin n) (Fin n) ℂ) (b : ℝ) (hDh : D.IsHermitian)
    (htr : D.trace = 0)
    (hhi : (((b : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - D).PosSemidef)
    (hlo : (((b : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + D).PosSemidef) :
    ∃ (U : Matrix (Fin n) (Fin n) ℂ) (e : Fin n → ℝ), Uᴴ * U = 1 ∧
      U * D * Uᴴ = Matrix.diagonal (fun i => ((e i : ℝ) : ℂ)) ∧
      (∀ i, e i ≤ b) ∧ (∀ i, -b ≤ e i) ∧ ∑ i, e i = 0 ∧ (D * D).trace.re = ∑ i, e i ^ 2 := by
  obtain ⟨U, e, hU1, hU2, hUe⟩ := diag_data D hDh
  refine ⟨U, e, hU1, hUe, ?_, ?_, ?_, ?_⟩
  · intro i
    have h := (hhi.mul_mul_conjTranspose_same U).diag_nonneg (i := i)
    have e' : U * (((b : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - D) * Uᴴ =
        ((b : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) -
          Matrix.diagonal (fun i => ((e i : ℝ) : ℂ)) := by
      rw [Matrix.mul_sub, Matrix.sub_mul, hUe, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hU2]
    rw [e', Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, Matrix.diagonal_apply_eq,
      smul_eq_mul, mul_one, ← Complex.ofReal_sub] at h
    linarith [Complex.zero_le_real.mp h]
  · intro i
    have h := (hlo.mul_mul_conjTranspose_same U).diag_nonneg (i := i)
    have e' : U * (((b : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + D) * Uᴴ =
        ((b : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) +
          Matrix.diagonal (fun i => ((e i : ℝ) : ℂ)) := by
      rw [Matrix.mul_add, Matrix.add_mul, hUe, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hU2]
    rw [e', Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, Matrix.diagonal_apply_eq,
      smul_eq_mul, mul_one, ← Complex.ofReal_add] at h
    linarith [Complex.zero_le_real.mp h]
  · have h1 : (U * D * Uᴴ).trace = D.trace := by
      rw [Matrix.trace_mul_cycle, hU1, Matrix.one_mul]
    rw [hUe, htr, Matrix.trace_diagonal] at h1
    have h2 : ((∑ i, e i : ℝ) : ℂ) = 0 := by
      rw [← h1]; push_cast; rfl
    exact_mod_cast h2
  · have h0 : U * (D * D) * Uᴴ = (U * D * Uᴴ) * (U * D * Uᴴ) := by
      have h : (U * D * Uᴴ) * (U * D * Uᴴ) = U * (D * (Uᴴ * U) * D) * Uᴴ := by
        simp only [Matrix.mul_assoc]
      rw [h, hU1, Matrix.mul_one]
    have h1 : (U * (D * D) * Uᴴ).trace = (D * D).trace := by
      rw [Matrix.trace_mul_cycle, hU1, Matrix.one_mul]
    rw [h0, hUe, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal] at h1
    rw [← h1, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Complex.ofReal_mul, Complex.ofReal_re, sq]

/-- `∑ eᵢ² ≤ 2b ∑_{eᵢ>0} eᵢ` for a traceless family with `|eᵢ| ≤ b`. -/
private lemma sum_sq_le {n : ℕ} (e : Fin n → ℝ) (b : ℝ) (hup : ∀ i, e i ≤ b) (hlo : ∀ i, -b ≤ e i)
    (hsum : ∑ i, e i = 0) :
    ∑ i, e i ^ 2 ≤ 2 * b * ∑ i ∈ Finset.univ.filter (fun i => 0 < e i), e i := by
  have h1 : ∀ i, e i ^ 2 ≤ b * (2 * (if 0 < e i then e i else 0) - e i) := by
    intro i
    split_ifs with h
    · nlinarith [hup i]
    · have h' := not_lt.mp h
      nlinarith [hlo i]
  calc ∑ i, e i ^ 2 ≤ ∑ i, b * (2 * (if 0 < e i then e i else 0) - e i) :=
        Finset.sum_le_sum fun i _ => h1 i
    _ = 2 * b * ∑ i ∈ Finset.univ.filter (fun i => 0 < e i), e i := by
        rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum, hsum, Finset.sum_filter]
        ring

/-- From an occupation matrix `N ⪰ a ≥ 0` to the fugacity matrix `R = N(1 + N)⁻¹`. -/
private lemma occ_facts {n : ℕ} (N : Matrix (Fin n) (Fin n) ℂ) (a : ℝ) (ha : 0 ≤ a)
    (hN : (N - ((a : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef) :
    N.PosSemidef ∧ (N * (1 + N)⁻¹).PosSemidef ∧ (1 - N * (1 + N)⁻¹).PosDef ∧
      N * (1 + N)⁻¹ * (1 - N * (1 + N)⁻¹)⁻¹ = N := by
  have hNpsd : N.PosSemidef := by
    have e : N = (N - ((a : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) +
        ((a : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by rw [sub_add_cancel]
    rw [e]
    exact hN.add (Matrix.PosSemidef.one.smul (Complex.zero_le_real.mpr ha))
  have hM : (1 + N).PosDef := Matrix.PosDef.one.add_posSemidef hNpsd
  have hdet : IsUnit (1 + N).det := (Matrix.isUnit_iff_isUnit_det _).mp hM.isUnit
  have h1 : N * (1 + N)⁻¹ = 1 - (1 + N)⁻¹ := by
    have h := Matrix.mul_nonsing_inv (1 + N) hdet
    rw [Matrix.add_mul, Matrix.one_mul] at h
    exact eq_sub_of_add_eq' h
  have h2 : 1 - N * (1 + N)⁻¹ = (1 + N)⁻¹ := by rw [h1, sub_sub_cancel]
  have hMN : ((1 + N) * N).PosSemidef := by
    rw [Matrix.add_mul, Matrix.one_mul]
    have h := Matrix.posSemidef_self_mul_conjTranspose N
    rw [hNpsd.isHermitian.eq] at h
    exact hNpsd.add h
  refine ⟨hNpsd, ?_, ?_, ?_⟩
  · have h := hMN.mul_mul_conjTranspose_same (1 + N)⁻¹
    rw [hM.isHermitian.inv.eq, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet,
      Matrix.one_mul] at h
    exact h
  · rw [h2]
    exact hM.inv
  · rw [h2, Matrix.nonsing_inv_nonsing_inv _ hdet, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet,
      Matrix.mul_one]

/-- The coordinate projector onto the modes in `A`. -/
private abbrev proj {n : ℕ} (A : Finset (Fin n)) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0)

private lemma proj_conj {n : ℕ} (A : Finset (Fin n)) : (proj A)ᴴ = proj A := by
  rw [proj, Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  rw [Pi.star_apply]
  split_ifs <;> simp

private lemma proj_mul {n : ℕ} (A : Finset (Fin n)) : proj A * proj A = proj A := by
  rw [proj, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp

private lemma proj_trace {n : ℕ} (A : Finset (Fin n)) : (proj A).trace = (A.card : ℂ) := by
  rw [proj, Matrix.trace_diagonal]
  simp

private lemma proj_compress {n : ℕ} (A : Finset (Fin n)) {K : Matrix (Fin n) (Fin n) ℂ}
    (hK : K.PosSemidef) : (proj A * K * proj A).PosSemidef := by
  have h := hK.mul_mul_conjTranspose_same (proj A)
  rwa [proj_conj] at h

private lemma proj_smul {n : ℕ} (A : Finset (Fin n)) (c : ℂ) :
    proj A * (c • (1 : Matrix (Fin n) (Fin n) ℂ)) * proj A = c • proj A := by
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, proj_mul]

/-- The compressions `B± = P_A Y± P_A` of `Y± = U N± Uᴴ`. -/
private lemma compress {n : ℕ} (Yp Ym : Matrix (Fin n) (Fin n) ℂ) (e : Fin n → ℝ) (A : Finset (Fin n))
    (ν c' : ℝ) (hν : 0 ≤ ν)
    (hdiff : Yp - Ym = Matrix.diagonal (fun i => ((e i : ℝ) : ℂ)))
    (hA : ∀ i ∈ A, 0 ≤ e i)
    (hlow : (Ym - ((ν : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef)
    (hupp : (((c' : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - Yp).PosSemidef) (hc' : 0 ≤ c') :
    (proj A * Ym * proj A).PosSemidef ∧
    (proj A * Yp * proj A - proj A * Ym * proj A).PosSemidef ∧
    (((c' : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - proj A * Yp * proj A).PosSemidef ∧
    (proj A * Yp * proj A - proj A * Ym * proj A).trace.re = ∑ i ∈ A, e i ∧
    ν ^ 2 * A.card ≤ (proj A * Ym * proj A * (proj A * Ym * proj A)).trace.re := by
  have hYm : Ym.PosSemidef := by
    have e : Ym = (Ym - ((ν : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) +
        ((ν : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by rw [sub_add_cancel]
    rw [e]
    exact hlow.add (Matrix.PosSemidef.one.smul (Complex.zero_le_real.mpr hν))
  have hdiag : proj A * Yp * proj A - proj A * Ym * proj A =
      Matrix.diagonal (fun i => ((if i ∈ A then e i else 0 : ℝ) : ℂ)) := by
    rw [← Matrix.sub_mul, ← Matrix.mul_sub, hdiff, proj, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    split_ifs <;> simp
  refine ⟨proj_compress A hYm, ?_, ?_, ?_, ?_⟩
  · rw [hdiag, Matrix.posSemidef_diagonal_iff]
    intro i
    refine Complex.zero_le_real.mpr ?_
    split_ifs with h
    · exact hA i h
    · exact le_rfl
  · have hd : Matrix.diagonal (fun i => ((c' - (if i ∈ A then c' else 0) : ℝ) : ℂ)) =
        ((c' : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - ((c' : ℝ) : ℂ) • proj A := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp only [Matrix.diagonal_apply_eq, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq,
          smul_eq_mul, mul_one]
        split_ifs <;> simp
      · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
    have e : ((c' : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - proj A * Yp * proj A =
        proj A * (((c' : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - Yp) * proj A +
          Matrix.diagonal (fun i => ((c' - (if i ∈ A then c' else 0) : ℝ) : ℂ)) := by
      rw [hd, Matrix.mul_sub, Matrix.sub_mul, proj_smul]
      abel
    rw [e]
    refine (proj_compress A hupp).add ?_
    rw [Matrix.posSemidef_diagonal_iff]
    intro i
    refine Complex.zero_le_real.mpr ?_
    split_ifs <;> linarith
  · rw [hdiag, Matrix.trace_diagonal, Complex.re_sum]
    simp only [Complex.ofReal_re]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  · set W : Matrix (Fin n) (Fin n) ℂ :=
      proj A * (Ym - ((ν : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) * proj A with hW
    have hWpsd : W.PosSemidef := proj_compress A hlow
    have hWP : W * proj A = W := by
      rw [hW, Matrix.mul_assoc, proj_mul]
    have hPW : proj A * W = W := by
      rw [hW, ← Matrix.mul_assoc, ← Matrix.mul_assoc, proj_mul]
    have hB : proj A * Ym * proj A = W + ((ν : ℝ) : ℂ) • proj A := by
      rw [hW, Matrix.mul_sub, Matrix.sub_mul, proj_smul, sub_add_cancel]
    have hsq : (W + ((ν : ℝ) : ℂ) • proj A) * (W + ((ν : ℝ) : ℂ) • proj A) =
        W * W + ((2 * ν : ℝ) : ℂ) • W + ((ν ^ 2 : ℝ) : ℂ) • proj A := by
      rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.smul_mul, Matrix.mul_smul, hWP, hPW, proj_mul, smul_smul]
      push_cast
      module
    have hWW : (0 : ℝ) ≤ (W * W).trace.re := by
      have h := Matrix.posSemidef_self_mul_conjTranspose W
      rw [hWpsd.isHermitian.eq] at h
      exact (Complex.nonneg_iff.mp h.trace_nonneg).1
    have hW0 : (0 : ℝ) ≤ W.trace.re := (Complex.nonneg_iff.mp hWpsd.trace_nonneg).1
    rw [hB, hsq, Matrix.trace_add, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
      proj_trace]
    simp only [Complex.add_re, smul_eq_mul, Complex.re_ofReal_mul, Complex.natCast_re]
    nlinarith [mul_nonneg hν hW0]

/-- Numerical step: the hypothesis `δ² ≤ s²` of the threshold lemma. -/
private lemma num_hyp {θ m k n δ T : ℝ} (hθ : 0 < θ) (hm : 0 < m) (hk0 : 0 ≤ k) (hkn : k ≤ n)
    (hθn : θ * Real.sqrt n ≤ 7 / 8) (hδ0 : 0 < δ) (hδ : δ ≤ θ * m * k)
    (hT : (7 / 8 * m) ^ 2 * k ≤ T) : δ ^ 2 ≤ T := by
  have hn : 0 ≤ n := hk0.trans hkn
  have h1 : θ ^ 2 * n ≤ 49 / 64 := by
    have h := pow_le_pow_left₀ (by positivity) hθn 2
    rw [mul_pow, Real.sq_sqrt hn] at h
    linarith
  have h2 : δ ^ 2 ≤ (θ * m * k) ^ 2 := pow_le_pow_left₀ hδ0.le hδ 2
  have h3 : (θ * m * k) ^ 2 ≤ (7 / 8 * m) ^ 2 * k := by
    have h4 : k * k ≤ k * n := mul_le_mul_of_nonneg_left hkn hk0
    have h5 : θ ^ 2 * (k * k) ≤ θ ^ 2 * (k * n) := mul_le_mul_of_nonneg_left h4 (by positivity)
    have h6 : θ ^ 2 * n * k ≤ 49 / 64 * k := mul_le_mul_of_nonneg_right h1 hk0
    have h7 : θ ^ 2 * (k * k) ≤ 49 / 64 * k := by linarith
    calc (θ * m * k) ^ 2 = m ^ 2 * (θ ^ 2 * (k * k)) := by ring
      _ ≤ m ^ 2 * (49 / 64 * k) := mul_le_mul_of_nonneg_left h7 (by positivity)
      _ = (7 / 8 * m) ^ 2 * k := by ring
  exact h2.trans (h3.trans hT)

/-- Numerical step: the final constant. -/
private lemma num_final {c₀ θ m n S δ sg : ℝ} (hc₀ : 0 < c₀) (hθ : 0 < θ) (hm : 0 < m)
    (hn : 1 ≤ n) (hS : S ≤ 2 * (θ * m) * δ) (hδ : 0 ≤ δ) (hsg0 : 0 ≤ sg) (hsg : sg ≤ 2 * n) :
    c₀ / 5 * S / (θ * m ^ 2 * Real.sqrt n) ≤
      c₀ * (δ / (9 / 8 * m)) / Real.sqrt (1 + sg) := by
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by linarith)
  have hsq : Real.sqrt (1 + sg) ≤ 2 * Real.sqrt n := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt (by linarith)]
    linarith
  have hsq0 : 0 < Real.sqrt (1 + sg) := Real.sqrt_pos.mpr (by linarith)
  have h1 : c₀ / 5 * S / (θ * m ^ 2 * Real.sqrt n) ≤
      c₀ / 5 * (2 * (θ * m) * δ) / (θ * m ^ 2 * Real.sqrt n) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left hS (by positivity)
  have h2 : c₀ / 5 * (2 * (θ * m) * δ) / (θ * m ^ 2 * Real.sqrt n) =
      2 / 5 * (c₀ * δ / (m * Real.sqrt n)) := by
    field_simp
  have h3 : c₀ * (δ / (9 / 8 * m)) / (2 * Real.sqrt n) = 4 / 9 * (c₀ * δ / (m * Real.sqrt n)) := by
    field_simp
    ring
  have h4 : 0 ≤ c₀ * δ / (m * Real.sqrt n) := by positivity
  have h5 : c₀ * (δ / (9 / 8 * m)) / (2 * Real.sqrt n) ≤
      c₀ * (δ / (9 / 8 * m)) / Real.sqrt (1 + sg) :=
    div_le_div_of_nonneg_left (by positivity) hsq0 hsq
  calc c₀ / 5 * S / (θ * m ^ 2 * Real.sqrt n)
      ≤ 2 / 5 * (c₀ * δ / (m * Real.sqrt n)) := h1.trans_eq h2
    _ ≤ 4 / 9 * (c₀ * δ / (m * Real.sqrt n)) := by nlinarith
    _ = c₀ * (δ / (9 / 8 * m)) / (2 * Real.sqrt n) := h3.symm
    _ ≤ _ := h5

theorem solution :
    ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ) (m θ : ℝ), 1 ≤ m → 0 < θ → θ * Real.sqrt n ≤ 7 / 8 →
      ∀ N₁ N₂ : Matrix (Fin n) (Fin n) ℂ,
        (N₁ - ((7 / 8 * m : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef →
        (((9 / 8 * m : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - N₁).PosSemidef →
        (N₂ - ((7 / 8 * m : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef →
        (((9 / 8 * m : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - N₂).PosSemidef →
        (N₁ - N₂).trace = 0 →
        (((θ * m : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - (N₁ - N₂)).PosSemidef →
        (((θ * m : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + (N₁ - N₂)).PosSemidef →
        ENNReal.ofReal (c * ((N₁ - N₂) * (N₁ - N₂)).trace.re / (θ * m ^ 2 * Real.sqrt n)) ≤
          traceSize (fugacityCoeff (N₁ * (1 + N₁)⁻¹) - fugacityCoeff (N₂ * (1 + N₂)⁻¹)) := by
  obtain ⟨c₀, hc₀, hgeo⟩ := geometric_threshold_scaled
  refine ⟨c₀ / 5, by positivity, ?_⟩
  intro n m θ hm hθ hθn N₁ N₂ h1lo h1hi h2lo h2hi htr hDhi hDlo
  have hm0 : 0 < m := by linarith
  have hθm : 0 < θ * m := mul_pos hθ hm0
  obtain ⟨hN1psd, hR1psd, hR1pd, hRN1⟩ := occ_facts N₁ (7 / 8 * m) (by positivity) h1lo
  obtain ⟨hN2psd, hR2psd, hR2pd, hRN2⟩ := occ_facts N₂ (7 / 8 * m) (by positivity) h2lo
  have hDh : (N₁ - N₂).IsHermitian := hN1psd.isHermitian.sub hN2psd.isHermitian
  obtain ⟨U, e, hU1, hUe, he_up, he_lo, hesum, hS⟩ :=
    spec_facts (N₁ - N₂) (θ * m) hDh htr hDhi hDlo
  have hU2 : U * Uᴴ = 1 := mul_eq_one_comm.mp hU1
  have hSle := sum_sq_le e (θ * m) he_up he_lo hesum
  rw [hS]
  -- the trivial case `N₁ = N₂`
  by_cases hS0 : ∑ i, e i ^ 2 ≤ 0
  · have h0 : c₀ / 5 * (∑ i, e i ^ 2) / (θ * m ^ 2 * Real.sqrt n) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by positivity) hS0)
        (by positivity)
    rw [ENNReal.ofReal_of_nonpos h0]
    exact bot_le
  have hSpos : 0 < ∑ i, e i ^ 2 := not_le.mp hS0
  have hn1 : (1 : ℝ) ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      simp at hSpos
    · exact_mod_cast h
  set A : Finset (Fin n) := Finset.univ.filter (fun i => 0 < e i) with hA
  have hδpos : 0 < ∑ i ∈ A, e i := by
    by_contra hneg
    have h1 : 2 * (θ * m) * ∑ i ∈ A, e i ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (not_lt.mp hneg)
    linarith
  -- the compressions
  have hconj1 : ∀ (N : Matrix (Fin n) (Fin n) ℂ) (c : ℂ),
      U * (N - c • (1 : Matrix (Fin n) (Fin n) ℂ)) * Uᴴ = U * N * Uᴴ - c • 1 := by
    intro N c
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hU2]
  have hconj2 : ∀ (N : Matrix (Fin n) (Fin n) ℂ) (c : ℂ),
      U * (c • (1 : Matrix (Fin n) (Fin n) ℂ) - N) * Uᴴ = c • 1 - U * N * Uᴴ := by
    intro N c
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hU2]
  obtain ⟨hBm, hBd, hBΛ, hBδ, hBlow⟩ := compress (U * N₁ * Uᴴ) (U * N₂ * Uᴴ) e A (7 / 8 * m)
    (9 / 8 * m) (by positivity)
    (by rw [← Matrix.sub_mul, ← Matrix.mul_sub]; exact hUe)
    (fun i hi => (Finset.mem_filter.mp hi).2.le)
    (by rw [← hconj1]; exact h2lo.mul_mul_conjTranspose_same U)
    (by rw [← hconj2]; exact h1hi.mul_mul_conjTranspose_same U) (by positivity)
  set P : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0) with hP
  set Bp : Matrix (Fin n) (Fin n) ℂ := P * (U * N₁ * Uᴴ) * P with hBp
  set Bm : Matrix (Fin n) (Fin n) ℂ := P * (U * N₂ * Uᴴ) * P with hBmdef
  obtain ⟨lp, lm, hlm0, hle, hlpΛ, hdetp, hdetm, htrp, htrm, htrm2⟩ :=
    loewner_eigenvalue_pairing Bm Bp hBm hBd (9 / 8 * m) hBΛ
  obtain ⟨hpp0, hppgf⟩ := fugacity_count_pgf (N₁ * (1 + N₁)⁻¹) hR1psd hR1pd U hU1 A
  obtain ⟨hpm0, hpmgf⟩ := fugacity_count_pgf (N₂ * (1 + N₂)⁻¹) hR2psd hR2pd U hU1 A
  rw [hRN1] at hppgf
  rw [hRN2] at hpmgf
  set pp : ℕ → ℝ := fun k => ∑' w : Occupation (Fin n),
    if ∑ i ∈ A, w i = k then (fugacityCoeff (U * (N₁ * (1 + N₁)⁻¹) * Uᴴ) w w).re else 0 with hpp
  set pm : ℕ → ℝ := fun k => ∑' w : Occupation (Fin n),
    if ∑ i ∈ A, w i = k then (fugacityCoeff (U * (N₂ * (1 + N₂)⁻¹) * Uᴴ) w w).re else 0 with hpm
  -- generating functions in product form
  have hPGFp : ∀ z : ℝ, 0 ≤ z → z ≤ 1 →
      HasSum (fun k => pp k * z ^ k) (∏ i, (1 + lp i * (1 - z))⁻¹) := by
    intro z hz0 hz1
    have h := (hppgf z hz0 hz1).2
    have e : (1 + ((1 - z : ℝ) : ℂ) • Bp).det.re = ∏ i, (1 + lp i * (1 - z)) := by
      rw [hdetp (1 - z), ← Complex.ofReal_prod, Complex.ofReal_re]
      exact Finset.prod_congr rfl fun i _ => by ring
    rw [e, ← Finset.prod_inv_distrib] at h
    exact h
  have hPGFm : ∀ z : ℝ, 0 ≤ z → z ≤ 1 →
      HasSum (fun k => pm k * z ^ k) (∏ i, (1 + lm i * (1 - z))⁻¹) := by
    intro z hz0 hz1
    have h := (hpmgf z hz0 hz1).2
    have e : (1 + ((1 - z : ℝ) : ℂ) • Bm).det.re = ∏ i, (1 + lm i * (1 - z)) := by
      rw [hdetm (1 - z), ← Complex.ofReal_prod, Complex.ofReal_re]
      exact Finset.prod_congr rfl fun i _ => by ring
    rw [e, ← Finset.prod_inv_distrib] at h
    exact h
  -- `δ` and `∑ (λ⁻)²` in terms of the traces
  have hδ : ∑ i, (lp i - lm i) = ∑ i ∈ A, e i := by
    rw [← hBδ, Matrix.trace_sub, htrp, htrm, ← Complex.ofReal_sub, Complex.ofReal_re,
      Finset.sum_sub_distrib]
  have hlm2 : (7 / 8 * m) ^ 2 * A.card ≤ ∑ i, lm i ^ 2 := by
    have h : (Bm * Bm).trace.re = ∑ i, lm i ^ 2 := by rw [htrm2, Complex.ofReal_re]
    rw [← h]
    exact hBlow
  have hcard : (A.card : ℝ) ≤ n := by
    have := Finset.card_le_univ A
    simp only [Fintype.card_fin] at this
    exact_mod_cast this
  have hcard0 : (0 : ℝ) ≤ A.card := Nat.cast_nonneg _
  have hδle : ∑ i ∈ A, e i ≤ θ * m * A.card := by
    calc ∑ i ∈ A, e i ≤ ∑ _i ∈ A, θ * m := Finset.sum_le_sum fun i _ => he_up i
      _ = θ * m * A.card := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
  have hδs : (∑ i, (lp i - lm i)) ^ 2 ≤ 1 + ∑ i, lm i * (1 + lm i) := by
    rw [hδ]
    have h1 := num_hyp hθ hm0 hcard0 hcard hθn hδpos hδle hlm2
    have h2 : ∑ i, lm i ^ 2 ≤ ∑ i, lm i * (1 + lm i) :=
      Finset.sum_le_sum fun i _ => by nlinarith [hlm0 i]
    linarith
  have hΛ1 : (1 : ℝ) ≤ 9 / 8 * m := by linarith
  obtain ⟨τ, hτ⟩ := hgeo (9 / 8 * m) hΛ1 n lp lm hlm0 hle hlpΛ pp pm hpp0 hpm0 hPGFp hPGFm
    (by rw [hδ]; exact hδpos) hδs
  -- data processing
  have htest := fugacity_count_test (N₂ * (1 + N₂)⁻¹) (N₁ * (1 + N₁)⁻¹) hR2psd hR2pd hR1psd hR1pd
    U hU1 A τ
  -- the constant
  have hsg0 : 0 ≤ ∑ i, lm i / (9 / 8 * m) * (1 + lm i / (9 / 8 * m)) :=
    Finset.sum_nonneg fun i _ => by
      have h1 : 0 ≤ lm i / (9 / 8 * m) := div_nonneg (hlm0 i) (by positivity)
      positivity
  have hsg : ∑ i, lm i / (9 / 8 * m) * (1 + lm i / (9 / 8 * m)) ≤ 2 * n := by
    have h : ∀ i, lm i / (9 / 8 * m) * (1 + lm i / (9 / 8 * m)) ≤ 2 := by
      intro i
      have h1 : 0 ≤ lm i / (9 / 8 * m) := div_nonneg (hlm0 i) (by positivity)
      have h2 : lm i / (9 / 8 * m) ≤ 1 := by
        rw [div_le_one (by positivity)]
        exact (hle i).trans (hlpΛ i)
      nlinarith
    calc ∑ i, lm i / (9 / 8 * m) * (1 + lm i / (9 / 8 * m)) ≤ ∑ _i : Fin n, (2 : ℝ) :=
          Finset.sum_le_sum fun i _ => h i
      _ = 2 * n := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hfinal := num_final hc₀ hθ hm0 hn1 hSle hδpos.le hsg0 hsg
  rw [← hδ] at hfinal
  calc ENNReal.ofReal (c₀ / 5 * (∑ i, e i ^ 2) / (θ * m ^ 2 * Real.sqrt n))
      ≤ ENNReal.ofReal (c₀ * ((∑ i, (lp i - lm i)) / (9 / 8 * m)) /
          Real.sqrt (1 + ∑ i, lm i / (9 / 8 * m) * (1 + lm i / (9 / 8 * m)))) :=
        ENNReal.ofReal_le_ofReal hfinal
    _ ≤ ENNReal.ofReal |(∑' k, if τ < k then pp k else 0) - ∑' k, if τ < k then pm k else 0| :=
        ENNReal.ofReal_le_ofReal (hτ.trans (le_abs_self _))
    _ ≤ _ := htest
