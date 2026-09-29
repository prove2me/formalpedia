-- Prove2me | solution 1 for FatkhullinPolyak.Discrete.lyapY_eigen_upper
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:27:27.800301+00:00
-- url     : https://prove2.me/submissions/cc3321c1-c4dd-4e3e-bec3-97f12587a706

import Mathlib
import Definitions.Def_FatkhullinPolyak_Discrete_LQR

open Filter Topology

namespace FatkhullinPolyak.Discrete

open Matrix

lemma aux_lyeu_mem_spec {n : ℕ} (N : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    z ∈ spectrum ℂ N ↔ (Matrix.scalar (Fin n) z - N).det = 0 := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not]
  rfl

lemma aux_lyeu_hurwitz_transpose {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsHurwitz M) :
    IsHurwitz M.transpose := by
  intro z hz
  apply hM z
  rw [aux_lyeu_mem_spec] at hz ⊢
  rw [← Matrix.det_transpose]
  convert hz using 2
  rw [Matrix.transpose_sub, Matrix.transpose_map]
  simp

lemma aux_lyeu_det_map {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    (M.map (algebraMap ℝ ℂ)).det = (M.det : ℂ) := by
  rw [show M.map (algebraMap ℝ ℂ) = (algebraMap ℝ ℂ).mapMatrix M from rfl, ← RingHom.map_det]
  rfl

lemma aux_lyeu_one_sub_det {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsHurwitz M) :
    (1 - M).det ≠ 0 := by
  intro h
  have h1 : (1 : ℂ) ∈ spectrum ℂ (M.map (algebraMap ℝ ℂ)) := by
    rw [aux_lyeu_mem_spec]
    have : Matrix.scalar (Fin n) (1 : ℂ) - M.map (algebraMap ℝ ℂ) = (1 - M).map (algebraMap ℝ ℂ) := by
      rw [Matrix.map_sub _ (fun a b => map_sub _ a b)]
      simp
    rw [this, aux_lyeu_det_map, h]
    simp
  have := hM 1 h1
  norm_num at this


lemma aux_lyeu_mem_spec' {n : ℕ} (N : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    z ∈ spectrum ℂ N ↔ (z • (1 : Matrix (Fin n) (Fin n) ℂ) - N).det = 0 := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not,
    Algebra.algebraMap_eq_smul_one]

lemma aux_lyeu_re_div (z : ℂ) (hz : 1 ≤ ‖z‖) (hz1 : z + 1 ≠ 0) :
    0 ≤ ((z - 1) / (z + 1)).re := by
  rw [Complex.div_re]
  have hN : 0 < Complex.normSq (z + 1) := Complex.normSq_pos.mpr hz1
  have h2 : 1 ≤ z.re * z.re + z.im * z.im := by
    have := Complex.normSq_eq_norm_sq z
    rw [Complex.normSq_apply] at this
    nlinarith [norm_nonneg z]
  rw [← add_div]
  apply div_nonneg _ hN.le
  simp only [Complex.sub_re, Complex.one_re, Complex.add_re, Complex.sub_im, Complex.one_im,
    Complex.add_im]
  nlinarith

lemma aux_lyeu_T_spec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsHurwitz M) :
    ∀ z ∈ spectrum ℂ (((1 + M) * (1 - M)⁻¹).map (algebraMap ℝ ℂ)), ‖z‖ < 1 := by
  intro z hz
  have hG := aux_lyeu_one_sub_det M hM
  have hGu : IsUnit (1 - M).det := isUnit_iff_ne_zero.mpr hG
  have hTG : (1 + M) * (1 - M)⁻¹ * (1 - M) = 1 + M := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hGu, Matrix.mul_one]
  set f := algebraMap ℝ ℂ
  set T := (1 + M) * (1 - M)⁻¹
  set M' := M.map f
  have hmap : ∀ A B : Matrix (Fin n) (Fin n) ℝ, (A * B).map f = A.map f * B.map f :=
    fun A B => Matrix.map_mul
  have hTG' : T.map f * (1 - M') = 1 + M' := by
    have h1 : (1 - M).map f = 1 - M' := by
      rw [Matrix.map_sub _ (fun a b => map_sub _ a b)]; simp [M']
    have h2 : (1 + M).map f = 1 + M' := by
      rw [Matrix.map_add _ (fun a b => map_add _ a b)]; simp [M']
    rw [← h1, ← h2, ← hmap, hTG]
  rw [aux_lyeu_mem_spec'] at hz
  have hdet : ((z - 1) • (1 : Matrix (Fin n) (Fin n) ℂ) - (z + 1) • M').det = 0 := by
    have : (z • (1 : Matrix (Fin n) (Fin n) ℂ) - T.map f) * (1 - M')
        = (z - 1) • (1 : Matrix (Fin n) (Fin n) ℂ) - (z + 1) • M' := by
      rw [Matrix.sub_mul, hTG', Matrix.smul_mul, Matrix.one_mul, smul_sub, sub_smul, add_smul,
        one_smul, one_smul]
      abel
    rw [← this, Matrix.det_mul, hz, zero_mul]
  by_contra hlt
  push Not at hlt
  by_cases hz1 : z + 1 = 0
  · have hz' : z = -1 := by linear_combination hz1
    rw [hz1, zero_smul, sub_zero, Matrix.det_smul, Matrix.det_one, mul_one, hz'] at hdet
    norm_num at hdet
  · set μ := (z - 1) / (z + 1)
    have hμ : μ ∈ spectrum ℂ M' := by
      rw [aux_lyeu_mem_spec']
      have : (z - 1) • (1 : Matrix (Fin n) (Fin n) ℂ) - (z + 1) • M'
          = (z + 1) • (μ • (1 : Matrix (Fin n) (Fin n) ℂ) - M') := by
        rw [smul_sub, smul_smul]
        congr 2
        simp only [μ]
        field_simp
      rw [this, Matrix.det_smul] at hdet
      exact (mul_eq_zero.mp hdet).resolve_left (pow_ne_zero _ hz1)
    have := hM μ hμ
    have := aux_lyeu_re_div z hlt hz1
    linarith


section gelfand
open scoped Matrix.Norms.L2Operator NNReal ENNReal

lemma aux_lyeu_cplx_pow_tendsto {n : ℕ} [NeZero n] (N' : Matrix (Fin n) (Fin n) ℂ)
    (hN : ∀ z ∈ spectrum ℂ N', ‖z‖ < 1) :
    Tendsto (fun k : ℕ => ‖N' ^ k‖) atTop (𝓝 0) := by
  have hsr : spectralRadius ℂ N' < ((1 : ℝ≥0) : ℝ≥0∞) :=
    spectrum.spectralRadius_lt_of_forall_lt N' (fun z hz => by
      have := hN z hz
      exact_mod_cast this)
  obtain ⟨r, hr1, hr2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hsr
  have hg := spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius N'
  have hev := hg.eventually (gt_mem_nhds hr1)
  have hr2' : (r : ℝ) < 1 := by exact_mod_cast hr2
  apply squeeze_zero' (Eventually.of_forall fun k => norm_nonneg _) _
    (tendsto_pow_atTop_nhds_zero_of_lt_one r.coe_nonneg hr2')
  filter_upwards [hev, eventually_ge_atTop 1] with k hk hk1
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
  have h1 : ((‖N' ^ k‖₊ : ℝ≥0∞) ^ (1 / (k : ℝ))) ^ (k : ℝ) < (r : ℝ≥0∞) ^ (k : ℝ) :=
    ENNReal.rpow_lt_rpow hk hkpos
  rw [← ENNReal.rpow_mul, one_div_mul_cancel hkpos.ne', ENNReal.rpow_one,
    ENNReal.rpow_natCast] at h1
  have h2 : ‖N' ^ k‖₊ < r ^ k := by exact_mod_cast h1
  have h3 : (‖N' ^ k‖₊ : ℝ) < ((r ^ k : ℝ≥0) : ℝ) := by exact_mod_cast h2
  simpa using h3.le


lemma aux_lyeu_cplx_pow_tendsto' {n : ℕ} [NeZero n] (N' : Matrix (Fin n) (Fin n) ℂ)
    (hN : ∀ z ∈ spectrum ℂ N', ‖z‖ < 1) (i j : Fin n) :
    Tendsto (fun k : ℕ => (N' ^ k) i j) atTop (𝓝 0) := by
  have h := tendsto_zero_iff_norm_tendsto_zero.mpr (aux_lyeu_cplx_pow_tendsto N' hN)
  have hc : Continuous (fun A : Matrix (Fin n) (Fin n) ℂ => A i j) :=
    (continuous_apply j).comp (continuous_apply i)
  have := (hc.tendsto 0).comp h
  exact this

end gelfand


lemma aux_lyeu_pow_tendsto {n : ℕ} (N : Matrix (Fin n) (Fin n) ℝ)
    (hN : ∀ z ∈ spectrum ℂ (N.map (algebraMap ℝ ℂ)), ‖z‖ < 1) :
    Tendsto (fun k : ℕ => N ^ k) atTop (𝓝 0) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : (fun k : ℕ => N ^ k) = fun _ => 0 := funext fun _ => Subsingleton.elim _ _
    rw [this]; exact tendsto_const_nhds
  have : NeZero n := ⟨hn.ne'⟩
  refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
  have h := aux_lyeu_cplx_pow_tendsto' (N.map (algebraMap ℝ ℂ)) hN i j
  have h2 := (Complex.continuous_re.tendsto 0).comp h
  have hk : ∀ k : ℕ, ((N.map (algebraMap ℝ ℂ)) ^ k) i j = (((N ^ k) i j : ℝ) : ℂ) := by
    intro k
    have : (N.map (algebraMap ℝ ℂ)) ^ k = (N ^ k).map (algebraMap ℝ ℂ) := by
      change ((algebraMap ℝ ℂ).mapMatrix N) ^ k = (algebraMap ℝ ℂ).mapMatrix (N ^ k)
      rw [map_pow]
    rw [this]; rfl
  simp only [Function.comp_def, hk, Complex.ofReal_re, Complex.zero_re] at h2
  exact h2

lemma aux_lyeu_stein {n : ℕ} (M Y W : Matrix (Fin n) (Fin n) ℝ) (hM : IsHurwitz M)
    (hY : M.transpose * Y + Y * M + W = 0) :
    Y - ((1 + M) * (1 - M)⁻¹).transpose * Y * ((1 + M) * (1 - M)⁻¹)
      = (2 : ℝ) • (((1 - M)⁻¹).transpose * W * (1 - M)⁻¹) := by
  have hGu : IsUnit (1 - M).det := isUnit_iff_ne_zero.mpr (aux_lyeu_one_sub_det M hM)
  have hGGi : (1 - M) * (1 - M)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hGu
  set Gi := (1 - M)⁻¹
  have hW : W = -(M.transpose * Y + Y * M) := eq_neg_of_add_eq_zero_right hY
  have e1 : (1 - M).transpose * Y * (1 - M) - (1 + M).transpose * Y * (1 + M) = (2 : ℝ) • W := by
    rw [hW, Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_one, two_smul]
    noncomm_ring
  have e2 : Y = Gi.transpose * ((1 - M).transpose * Y * (1 - M)) * Gi := by
    have : Gi.transpose * (1 - M).transpose = 1 := by
      rw [← Matrix.transpose_mul, hGGi, Matrix.transpose_one]
    calc Y = (Gi.transpose * (1 - M).transpose) * Y * ((1 - M) * Gi) := by
            rw [this, hGGi, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  have e3 : ((1 + M) * Gi).transpose * Y * ((1 + M) * Gi)
      = Gi.transpose * ((1 + M).transpose * Y * (1 + M)) * Gi := by
    rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
  rw [e3, ← Matrix.smul_mul, ← Matrix.mul_smul, ← e1, Matrix.mul_sub, Matrix.sub_mul, ← e2]

lemma aux_lyeu_lyap_unique {n : ℕ} (M X : Matrix (Fin n) (Fin n) ℝ) (hM : IsHurwitz M)
    (hX : M.transpose * X + X * M = 0) : X = 0 := by
  set T := (1 + M) * (1 - M)⁻¹
  have hs := aux_lyeu_stein M X 0 hM (by rw [hX, add_zero])
  simp only [Matrix.mul_zero, Matrix.zero_mul, smul_zero, sub_eq_zero] at hs
  -- hs : X = T^T X T
  have hk : ∀ k : ℕ, (T ^ k).transpose * X * T ^ k = X := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, Matrix.transpose_mul]
      calc T.transpose * (T ^ k).transpose * X * (T ^ k * T)
          = T.transpose * ((T ^ k).transpose * X * T ^ k) * T := by
            simp only [Matrix.mul_assoc]
        _ = X := by rw [ih, ← hs]
  have htend := aux_lyeu_pow_tendsto T (aux_lyeu_T_spec M hM)
  have hc : Continuous (fun A : Matrix (Fin n) (Fin n) ℝ => A.transpose * X * A) := by
    fun_prop
  have h1 := (hc.tendsto 0).comp htend
  simp only [Matrix.transpose_zero, Matrix.zero_mul, Matrix.mul_zero] at h1
  have h2 : Tendsto (fun k : ℕ => (T ^ k).transpose * X * T ^ k) atTop (𝓝 X) := by
    simp only [hk]; exact tendsto_const_nhds
  exact tendsto_nhds_unique h2 h1

lemma aux_lyeu_lyap_exists_unique {n : ℕ} (M W : Matrix (Fin n) (Fin n) ℝ) (hM : IsHurwitz M) :
    ∃! X : Matrix (Fin n) (Fin n) ℝ, M.transpose * X + X * M + W = 0 := by
  let L : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ :=
    LinearMap.mulLeft ℝ M.transpose + LinearMap.mulRight ℝ M
  have hL : ∀ X, L X = M.transpose * X + X * M := fun X => rfl
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro X hX
    exact aux_lyeu_lyap_unique M X hM (by rw [← hL]; exact hX)
  have hsurj := LinearMap.injective_iff_surjective.mp hinj
  obtain ⟨X, hX⟩ := hsurj (-W)
  have hX' : M.transpose * X + X * M = -W := by rw [← hL]; exact hX
  refine ⟨X, ?_, fun Z hZ => ?_⟩
  · show M.transpose * X + X * M + W = 0
    rw [hX', neg_add_cancel]
  · have hZ' : M.transpose * Z + Z * M + W = 0 := hZ
    have := aux_lyeu_lyap_unique M (Z - X) hM (by
      rw [Matrix.mul_sub, Matrix.sub_mul]
      calc _ = (M.transpose * Z + Z * M + W) - (M.transpose * X + X * M + W) := by abel
        _ = 0 := by rw [hZ', hX', neg_add_cancel, sub_zero])
    exact sub_eq_zero.mp this


lemma aux_lyeu_lyapSol_spec {n : ℕ} (M W : Matrix (Fin n) (Fin n) ℝ) (hM : IsHurwitz M) :
    M.transpose * lyapSol M W + lyapSol M W * M + W = 0 := by
  have h := aux_lyeu_lyap_exists_unique M W hM
  unfold lyapSol
  rw [dif_pos h]
  exact h.choose_spec.1

lemma aux_lyeu_quad {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) :
    u ⬝ᵥ (A.transpose * B * A) *ᵥ u = (A *ᵥ u) ⬝ᵥ B *ᵥ (A *ᵥ u) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

lemma aux_lyeu_lyap_psd {n : ℕ} (M Y W : Matrix (Fin n) (Fin n) ℝ) (hM : IsHurwitz M)
    (hW : ∀ v, 0 ≤ v ⬝ᵥ W *ᵥ v) (hY : M.transpose * Y + Y * M + W = 0) :
    ∀ v, 0 ≤ v ⬝ᵥ Y *ᵥ v := by
  intro v
  set T := (1 + M) * (1 - M)⁻¹ with hT
  set Gi := (1 - M)⁻¹
  have hs := aux_lyeu_stein M Y W hM hY
  have hs' : T.transpose * Y * T = Y - (2 : ℝ) • (Gi.transpose * W * Gi) := by
    rw [← hs]; abel
  have hq : ∀ u, (T *ᵥ u) ⬝ᵥ Y *ᵥ (T *ᵥ u) ≤ u ⬝ᵥ Y *ᵥ u := by
    intro u
    rw [← aux_lyeu_quad, hs', Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
      dotProduct_smul, aux_lyeu_quad]
    have := hW (Gi *ᵥ u)
    simp only [smul_eq_mul]
    linarith
  let q : ℕ → ℝ := fun k => (T ^ k *ᵥ v) ⬝ᵥ Y *ᵥ (T ^ k *ᵥ v)
  have hanti : Antitone q := by
    apply antitone_nat_of_succ_le
    intro k
    simp only [q]
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    exact hq _
  have htend := aux_lyeu_pow_tendsto T (aux_lyeu_T_spec M hM)
  have hc : Continuous (fun A : Matrix (Fin n) (Fin n) ℝ => (A *ᵥ v) ⬝ᵥ Y *ᵥ (A *ᵥ v)) := by
    fun_prop
  have h1 := (hc.tendsto 0).comp htend
  simp only [Matrix.zero_mulVec, Matrix.mulVec_zero, dotProduct_zero] at h1
  have := hanti.le_of_tendsto h1 0
  simpa [q] using this

lemma aux_lyeu_lyap_symm {n : ℕ} (M Y W : Matrix (Fin n) (Fin n) ℝ) (hM : IsHurwitz M)
    (hW : W.transpose = W) (hY : M.transpose * Y + Y * M + W = 0) : Y.transpose = Y := by
  have hY' : M.transpose * Y.transpose + Y.transpose * M + W = 0 := by
    have := congrArg Matrix.transpose hY
    rw [Matrix.transpose_add, Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, hW, Matrix.transpose_zero] at this
    rw [← this]; abel
  have := aux_lyeu_lyap_unique M (Y.transpose - Y) hM (by
    rw [Matrix.mul_sub, Matrix.sub_mul]
    calc _ = (M.transpose * Y.transpose + Y.transpose * M + W)
          - (M.transpose * Y + Y * M + W) := by abel
      _ = 0 := by rw [hY, hY', sub_zero])
  exact sub_eq_zero.mp this


theorem aux_lyeu_decomp {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) (hB : B.PosSemidef) :
    ∃ c : Fin n → ℝ, (∀ i, 0 ≤ c i) ∧ Matrix.trace B = ∑ i, c i ∧
      Matrix.trace (A * B) = ∑ i, hA.eigenvalues i * c i := by
  set U : Matrix (Fin n) (Fin n) ℝ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) with hU
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self _
  set C := star U * B * U with hC
  have hCpsd : C.PosSemidef := by
    have := hB.conjTranspose_mul_mul_same U
    simpa [hC, Matrix.star_eq_conjTranspose] using this
  refine ⟨fun i => C i i, fun i => hCpsd.diag_nonneg, ?_, ?_⟩
  · have h1 : Matrix.trace C = Matrix.trace B := by
      rw [hC, Matrix.trace_mul_cycle, hUU', Matrix.one_mul]
    rw [← h1]
    rfl
  · have hspec := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at hspec
    have hD : (Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) : Matrix (Fin n) (Fin n) ℝ)
        = Matrix.diagonal hA.eigenvalues := by
      congr 1
    rw [hD] at hspec
    have : Matrix.trace (A * B) = Matrix.trace (Matrix.diagonal hA.eigenvalues * C) := by
      conv_lhs => rw [hspec]
      rw [hC]
      simp only [← hU]
      rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc,
        Matrix.mul_assoc]
    rw [this, Matrix.trace]
    simp [Matrix.diagonal_mul]

lemma aux_lyeu_lamMin_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (hn : 0 < n) :
    lamMin A = Finset.univ.inf' (⟨⟨0, hn⟩, Finset.mem_univ _⟩ : (Finset.univ : Finset (Fin n)).Nonempty)
      hA.eigenvalues := by
  unfold lamMin; rw [dif_pos hA, dif_pos hn]

lemma aux_lyeu_lamMin_le_trace {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) (hB : B.PosSemidef) :
    lamMin A * Matrix.trace B ≤ Matrix.trace (A * B) := by
  obtain ⟨c, hc0, htr, hAB⟩ := aux_lyeu_decomp A B hA hB
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h1 : Matrix.trace B = 0 := by simp [Matrix.trace]
    have h2 : Matrix.trace (A * B) = 0 := by simp [Matrix.trace]
    rw [h1, h2]; simp
  · rw [htr, hAB, Finset.mul_sum, aux_lyeu_lamMin_eq A hA hn]
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_right _ (hc0 i)
    exact Finset.inf'_le _ (Finset.mem_univ i)

lemma aux_lyeu_lamMin_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef) :
    0 ≤ lamMin A := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · unfold lamMin; simp
  · rw [aux_lyeu_lamMin_eq A hA.isHermitian hn]
    exact Finset.le_inf' _ _ fun i _ => hA.eigenvalues_nonneg i

lemma aux_lyeu_lamMin_pos {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (hn : 0 < n) :
    0 < lamMin A := by
  rw [aux_lyeu_lamMin_eq A hA.isHermitian hn]
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf'
    (⟨⟨0, hn⟩, Finset.mem_univ _⟩ : (Finset.univ : Finset (Fin n)).Nonempty) hA.isHermitian.eigenvalues
  rw [hi]
  exact hA.eigenvalues_pos i
lemma aux_lyeu_tdl {n : ℕ} (A X Y W V : Matrix (Fin n) (Fin n) ℝ)
    (hX : A.transpose * X + X * A + W = 0)
    (hY : A * Y + Y * A.transpose + V = 0) :
    Matrix.trace (X * V) = Matrix.trace (Y * W) := by
  have hW : W = -(A.transpose * X + X * A) := eq_neg_of_add_eq_zero_right hX
  have hV : V = -(A * Y + Y * A.transpose) := eq_neg_of_add_eq_zero_right hY
  subst hW hV
  simp only [Matrix.mul_neg, Matrix.trace_neg, Matrix.mul_add, Matrix.trace_add, neg_inj]
  have h1 : Matrix.trace (X * (A * Y)) = Matrix.trace (Y * (X * A)) := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
  have h2 : Matrix.trace (X * (Y * A.transpose)) = Matrix.trace (Y * (A.transpose * X)) := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
  rw [h1, h2, add_comm]


lemma aux_lyeu_lamMax_le_trace {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℝ) (hY : Y.PosSemidef) :
    lamMax Y ≤ Matrix.trace Y := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · unfold lamMax; simp [Matrix.trace]
  · unfold lamMax
    rw [dif_pos hY.isHermitian, dif_pos hn, hY.isHermitian.trace_eq_sum_eigenvalues]
    apply Finset.sup'_le
    intro i _
    simp only [RCLike.ofReal_real_eq_id, id_eq]
    exact Finset.single_le_sum (fun j _ => hY.eigenvalues_nonneg j) (Finset.mem_univ i)

theorem aux_lyeu_main {n m r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (Sig : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q.PosDef) (hR : R.PosDef) (hSig : Sig.PosDef)
    (K : Matrix (Fin m) (Fin r) ℝ) (hK : K ∈ stabSet A B C) :
    lamMax (lyapY A B C Sig K) ≤
      lqrCost A B C Q R Sig K / lamMin (Q + C.transpose * K.transpose * R * K * C) := by
  set AK := A - B * K * C with hAK
  have hKH : IsHurwitz AK := hK
  have hKHt : IsHurwitz AK.transpose := aux_lyeu_hurwitz_transpose AK hKH
  set W := C.transpose * K.transpose * R * K * C + Q with hW
  set X := lyapX A B C Q R K with hXdef
  set Y := lyapY A B C Sig K with hYdef
  have hX : AK.transpose * X + X * AK + W = 0 := aux_lyeu_lyapSol_spec AK W hKH
  have hY0 : AK.transpose.transpose * Y + Y * AK.transpose + Sig = 0 :=
    aux_lyeu_lyapSol_spec AK.transpose Sig hKHt
  have hY : AK * Y + Y * AK.transpose + Sig = 0 := by
    rwa [Matrix.transpose_transpose] at hY0
  have hf : lqrCost A B C Q R Sig K = Matrix.trace (Y * W) := aux_lyeu_tdl AK X Y W Sig hX hY
  have hSigT : Sig.transpose = Sig := by
    have := hSig.isHermitian
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hYT : Y.transpose = Y := aux_lyeu_lyap_symm AK.transpose Y Sig hKHt hSigT hY0
  have hYpsd' : ∀ v, 0 ≤ v ⬝ᵥ Y *ᵥ v := aux_lyeu_lyap_psd AK.transpose Y Sig hKHt
    (fun v => by simpa using hSig.posSemidef.dotProduct_mulVec_nonneg v) hY0
  have hYh : Y.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]; exact hYT
  have hYpsd : Y.PosSemidef :=
    Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hYh (fun x => by simpa using hYpsd' x)
  -- the weight matrix is positive definite
  have hKC : (C.transpose * K.transpose * R * K * C).PosSemidef := by
    have := hR.posSemidef.conjTranspose_mul_mul_same (K * C)
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_mul] at this
    simpa only [Matrix.mul_assoc] using this
  have hWpd : (Q + C.transpose * K.transpose * R * K * C).PosDef := hQ.add_posSemidef hKC
  have hWeq : Q + C.transpose * K.transpose * R * K * C = W := by rw [hW, add_comm]
  rw [hWeq] at hWpd ⊢
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    have h1 : lamMax Y = 0 := by
      unfold lamMax; split_ifs <;> first | rfl | omega
    rw [h1]
    have h2 : lamMin W = 0 := by
      unfold lamMin; split_ifs <;> first | rfl | omega
    rw [h2, div_zero]
  · have hlW : 0 < lamMin W := aux_lyeu_lamMin_pos W hWpd hn
    rw [le_div_iff₀ hlW, hf]
    have i1 := aux_lyeu_lamMin_le_trace W Y hWpd.isHermitian hYpsd
    have i2 := aux_lyeu_lamMax_le_trace Y hYpsd
    rw [Matrix.trace_mul_comm] at i1
    nlinarith

end FatkhullinPolyak.Discrete

open FatkhullinPolyak.Discrete
open Filter Topology

theorem solution {n m r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (Sig : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q.PosDef) (hR : R.PosDef) (hSig : Sig.PosDef) (hC : C.rank = r) (hB : B ≠ 0)
    (K : Matrix (Fin m) (Fin r) ℝ) (hK : K ∈ stabSet A B C) :
    lamMax (lyapY A B C Sig K) ≤
      lqrCost A B C Q R Sig K / lamMin (Q + C.transpose * K.transpose * R * K * C) :=
  aux_lyeu_main A B C Q R Sig hQ hR hSig K hK
