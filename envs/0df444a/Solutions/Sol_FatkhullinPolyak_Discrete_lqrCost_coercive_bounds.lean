-- Prove2me | solution 1 for FatkhullinPolyak.Discrete.lqrCost_coercive_bounds
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:58:05.270737+00:00
-- url     : https://prove2.me/submissions/557f7469-4970-49ab-980d-11fe88641e00

import Mathlib
import Definitions.Def_FatkhullinPolyak_Discrete_LQR

open Filter Topology

namespace FatkhullinPolyak.Discrete

open Matrix

lemma aux_lcb_mem_spec {n : ℕ} (N : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    z ∈ spectrum ℂ N ↔ (Matrix.scalar (Fin n) z - N).det = 0 := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not]
  rfl

lemma aux_lcb_hurwitz_transpose {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsHurwitz M) :
    IsHurwitz M.transpose := by
  intro z hz
  apply hM z
  rw [aux_lcb_mem_spec] at hz ⊢
  rw [← Matrix.det_transpose]
  convert hz using 2
  rw [Matrix.transpose_sub, Matrix.transpose_map]
  simp

lemma aux_lcb_det_map {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    (M.map (algebraMap ℝ ℂ)).det = (M.det : ℂ) := by
  rw [show M.map (algebraMap ℝ ℂ) = (algebraMap ℝ ℂ).mapMatrix M from rfl, ← RingHom.map_det]
  rfl

lemma aux_lcb_one_sub_det {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsHurwitz M) :
    (1 - M).det ≠ 0 := by
  intro h
  have h1 : (1 : ℂ) ∈ spectrum ℂ (M.map (algebraMap ℝ ℂ)) := by
    rw [aux_lcb_mem_spec]
    have : Matrix.scalar (Fin n) (1 : ℂ) - M.map (algebraMap ℝ ℂ) = (1 - M).map (algebraMap ℝ ℂ) := by
      rw [Matrix.map_sub _ (fun a b => map_sub _ a b)]
      simp
    rw [this, aux_lcb_det_map, h]
    simp
  have := hM 1 h1
  norm_num at this


lemma aux_lcb_mem_spec' {n : ℕ} (N : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    z ∈ spectrum ℂ N ↔ (z • (1 : Matrix (Fin n) (Fin n) ℂ) - N).det = 0 := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not,
    Algebra.algebraMap_eq_smul_one]

lemma aux_lcb_re_div (z : ℂ) (hz : 1 ≤ ‖z‖) (hz1 : z + 1 ≠ 0) :
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

lemma aux_lcb_T_spec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsHurwitz M) :
    ∀ z ∈ spectrum ℂ (((1 + M) * (1 - M)⁻¹).map (algebraMap ℝ ℂ)), ‖z‖ < 1 := by
  intro z hz
  have hG := aux_lcb_one_sub_det M hM
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
  rw [aux_lcb_mem_spec'] at hz
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
      rw [aux_lcb_mem_spec']
      have : (z - 1) • (1 : Matrix (Fin n) (Fin n) ℂ) - (z + 1) • M'
          = (z + 1) • (μ • (1 : Matrix (Fin n) (Fin n) ℂ) - M') := by
        rw [smul_sub, smul_smul]
        congr 2
        simp only [μ]
        field_simp
      rw [this, Matrix.det_smul] at hdet
      exact (mul_eq_zero.mp hdet).resolve_left (pow_ne_zero _ hz1)
    have := hM μ hμ
    have := aux_lcb_re_div z hlt hz1
    linarith


section gelfand
open scoped Matrix.Norms.L2Operator NNReal ENNReal

lemma aux_lcb_cplx_pow_tendsto {n : ℕ} [NeZero n] (N' : Matrix (Fin n) (Fin n) ℂ)
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


lemma aux_lcb_cplx_pow_tendsto' {n : ℕ} [NeZero n] (N' : Matrix (Fin n) (Fin n) ℂ)
    (hN : ∀ z ∈ spectrum ℂ N', ‖z‖ < 1) (i j : Fin n) :
    Tendsto (fun k : ℕ => (N' ^ k) i j) atTop (𝓝 0) := by
  have h := tendsto_zero_iff_norm_tendsto_zero.mpr (aux_lcb_cplx_pow_tendsto N' hN)
  have hc : Continuous (fun A : Matrix (Fin n) (Fin n) ℂ => A i j) :=
    (continuous_apply j).comp (continuous_apply i)
  have := (hc.tendsto 0).comp h
  exact this

end gelfand


lemma aux_lcb_pow_tendsto {n : ℕ} (N : Matrix (Fin n) (Fin n) ℝ)
    (hN : ∀ z ∈ spectrum ℂ (N.map (algebraMap ℝ ℂ)), ‖z‖ < 1) :
    Tendsto (fun k : ℕ => N ^ k) atTop (𝓝 0) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : (fun k : ℕ => N ^ k) = fun _ => 0 := funext fun _ => Subsingleton.elim _ _
    rw [this]; exact tendsto_const_nhds
  have : NeZero n := ⟨hn.ne'⟩
  refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
  have h := aux_lcb_cplx_pow_tendsto' (N.map (algebraMap ℝ ℂ)) hN i j
  have h2 := (Complex.continuous_re.tendsto 0).comp h
  have hk : ∀ k : ℕ, ((N.map (algebraMap ℝ ℂ)) ^ k) i j = (((N ^ k) i j : ℝ) : ℂ) := by
    intro k
    have : (N.map (algebraMap ℝ ℂ)) ^ k = (N ^ k).map (algebraMap ℝ ℂ) := by
      change ((algebraMap ℝ ℂ).mapMatrix N) ^ k = (algebraMap ℝ ℂ).mapMatrix (N ^ k)
      rw [map_pow]
    rw [this]; rfl
  simp only [Function.comp_def, hk, Complex.ofReal_re, Complex.zero_re] at h2
  exact h2

lemma aux_lcb_stein {n : ℕ} (M Y W : Matrix (Fin n) (Fin n) ℝ) (hM : IsHurwitz M)
    (hY : M.transpose * Y + Y * M + W = 0) :
    Y - ((1 + M) * (1 - M)⁻¹).transpose * Y * ((1 + M) * (1 - M)⁻¹)
      = (2 : ℝ) • (((1 - M)⁻¹).transpose * W * (1 - M)⁻¹) := by
  have hGu : IsUnit (1 - M).det := isUnit_iff_ne_zero.mpr (aux_lcb_one_sub_det M hM)
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

lemma aux_lcb_lyap_unique {n : ℕ} (M X : Matrix (Fin n) (Fin n) ℝ) (hM : IsHurwitz M)
    (hX : M.transpose * X + X * M = 0) : X = 0 := by
  set T := (1 + M) * (1 - M)⁻¹
  have hs := aux_lcb_stein M X 0 hM (by rw [hX, add_zero])
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
  have htend := aux_lcb_pow_tendsto T (aux_lcb_T_spec M hM)
  have hc : Continuous (fun A : Matrix (Fin n) (Fin n) ℝ => A.transpose * X * A) := by
    fun_prop
  have h1 := (hc.tendsto 0).comp htend
  simp only [Matrix.transpose_zero, Matrix.zero_mul, Matrix.mul_zero] at h1
  have h2 : Tendsto (fun k : ℕ => (T ^ k).transpose * X * T ^ k) atTop (𝓝 X) := by
    simp only [hk]; exact tendsto_const_nhds
  exact tendsto_nhds_unique h2 h1

lemma aux_lcb_lyap_exists_unique {n : ℕ} (M W : Matrix (Fin n) (Fin n) ℝ) (hM : IsHurwitz M) :
    ∃! X : Matrix (Fin n) (Fin n) ℝ, M.transpose * X + X * M + W = 0 := by
  let L : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ :=
    LinearMap.mulLeft ℝ M.transpose + LinearMap.mulRight ℝ M
  have hL : ∀ X, L X = M.transpose * X + X * M := fun X => rfl
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro X hX
    exact aux_lcb_lyap_unique M X hM (by rw [← hL]; exact hX)
  have hsurj := LinearMap.injective_iff_surjective.mp hinj
  obtain ⟨X, hX⟩ := hsurj (-W)
  have hX' : M.transpose * X + X * M = -W := by rw [← hL]; exact hX
  refine ⟨X, ?_, fun Z hZ => ?_⟩
  · show M.transpose * X + X * M + W = 0
    rw [hX', neg_add_cancel]
  · have hZ' : M.transpose * Z + Z * M + W = 0 := hZ
    have := aux_lcb_lyap_unique M (Z - X) hM (by
      rw [Matrix.mul_sub, Matrix.sub_mul]
      calc _ = (M.transpose * Z + Z * M + W) - (M.transpose * X + X * M + W) := by abel
        _ = 0 := by rw [hZ', hX', neg_add_cancel, sub_zero])
    exact sub_eq_zero.mp this


lemma aux_lcb_lyapSol_spec {n : ℕ} (M W : Matrix (Fin n) (Fin n) ℝ) (hM : IsHurwitz M) :
    M.transpose * lyapSol M W + lyapSol M W * M + W = 0 := by
  have h := aux_lcb_lyap_exists_unique M W hM
  unfold lyapSol
  rw [dif_pos h]
  exact h.choose_spec.1

lemma aux_lcb_quad {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) :
    u ⬝ᵥ (A.transpose * B * A) *ᵥ u = (A *ᵥ u) ⬝ᵥ B *ᵥ (A *ᵥ u) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

lemma aux_lcb_lyap_psd {n : ℕ} (M Y W : Matrix (Fin n) (Fin n) ℝ) (hM : IsHurwitz M)
    (hW : ∀ v, 0 ≤ v ⬝ᵥ W *ᵥ v) (hY : M.transpose * Y + Y * M + W = 0) :
    ∀ v, 0 ≤ v ⬝ᵥ Y *ᵥ v := by
  intro v
  set T := (1 + M) * (1 - M)⁻¹ with hT
  set Gi := (1 - M)⁻¹
  have hs := aux_lcb_stein M Y W hM hY
  have hs' : T.transpose * Y * T = Y - (2 : ℝ) • (Gi.transpose * W * Gi) := by
    rw [← hs]; abel
  have hq : ∀ u, (T *ᵥ u) ⬝ᵥ Y *ᵥ (T *ᵥ u) ≤ u ⬝ᵥ Y *ᵥ u := by
    intro u
    rw [← aux_lcb_quad, hs', Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
      dotProduct_smul, aux_lcb_quad]
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
  have htend := aux_lcb_pow_tendsto T (aux_lcb_T_spec M hM)
  have hc : Continuous (fun A : Matrix (Fin n) (Fin n) ℝ => (A *ᵥ v) ⬝ᵥ Y *ᵥ (A *ᵥ v)) := by
    fun_prop
  have h1 := (hc.tendsto 0).comp htend
  simp only [Matrix.zero_mulVec, Matrix.mulVec_zero, dotProduct_zero] at h1
  have := hanti.le_of_tendsto h1 0
  simpa [q] using this

lemma aux_lcb_lyap_symm {n : ℕ} (M Y W : Matrix (Fin n) (Fin n) ℝ) (hM : IsHurwitz M)
    (hW : W.transpose = W) (hY : M.transpose * Y + Y * M + W = 0) : Y.transpose = Y := by
  have hY' : M.transpose * Y.transpose + Y.transpose * M + W = 0 := by
    have := congrArg Matrix.transpose hY
    rw [Matrix.transpose_add, Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, hW, Matrix.transpose_zero] at this
    rw [← this]; abel
  have := aux_lcb_lyap_unique M (Y.transpose - Y) hM (by
    rw [Matrix.mul_sub, Matrix.sub_mul]
    calc _ = (M.transpose * Y.transpose + Y.transpose * M + W)
          - (M.transpose * Y + Y * M + W) := by abel
      _ = 0 := by rw [hY, hY', sub_zero])
  exact sub_eq_zero.mp this


theorem aux_lcb_decomp {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
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

lemma aux_lcb_lamMin_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (hn : 0 < n) :
    lamMin A = Finset.univ.inf' (⟨⟨0, hn⟩, Finset.mem_univ _⟩ : (Finset.univ : Finset (Fin n)).Nonempty)
      hA.eigenvalues := by
  unfold lamMin; rw [dif_pos hA, dif_pos hn]

lemma aux_lcb_lamMin_le_trace {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) (hB : B.PosSemidef) :
    lamMin A * Matrix.trace B ≤ Matrix.trace (A * B) := by
  obtain ⟨c, hc0, htr, hAB⟩ := aux_lcb_decomp A B hA hB
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h1 : Matrix.trace B = 0 := by simp [Matrix.trace]
    have h2 : Matrix.trace (A * B) = 0 := by simp [Matrix.trace]
    rw [h1, h2]; simp
  · rw [htr, hAB, Finset.mul_sum, aux_lcb_lamMin_eq A hA hn]
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_right _ (hc0 i)
    exact Finset.inf'_le _ (Finset.mem_univ i)

lemma aux_lcb_lamMin_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef) :
    0 ≤ lamMin A := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · unfold lamMin; simp
  · rw [aux_lcb_lamMin_eq A hA.isHermitian hn]
    exact Finset.le_inf' _ _ fun i _ => hA.eigenvalues_nonneg i

lemma aux_lcb_lamMin_pos {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (hn : 0 < n) :
    0 < lamMin A := by
  rw [aux_lcb_lamMin_eq A hA.isHermitian hn]
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf'
    (⟨⟨0, hn⟩, Finset.mem_univ _⟩ : (Finset.univ : Finset (Fin n)).Nonempty) hA.isHermitian.eigenvalues
  rw [hi]
  exact hA.eigenvalues_pos i

lemma aux_lcb_quad_ge {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (v : Fin n → ℝ) : lamMin A * (v ⬝ᵥ v) ≤ v ⬝ᵥ A *ᵥ v := by
  have h := aux_lcb_lamMin_le_trace A (Matrix.vecMulVec v v) hA
    (by simpa using Matrix.posSemidef_vecMulVec_self_star v)
  rw [Matrix.trace_vecMulVec, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec,
    dotProduct_comm (A *ᵥ v) v] at h
  exact h


lemma aux_lcb_dot_self_nonneg {p : ℕ} (a : Fin p → ℝ) : 0 ≤ a ⬝ᵥ a :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (a i)

lemma aux_lcb_cs {p : ℕ} (a b : Fin p → ℝ) : |a ⬝ᵥ b| ≤ √(a ⬝ᵥ a) * √(b ⬝ᵥ b) := by
  rw [← Real.sqrt_mul (aux_lcb_dot_self_nonneg a)]
  apply Real.abs_le_sqrt
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
  simpa [dotProduct, sq] using h

section l2
open scoped Matrix.Norms.L2Operator

lemma aux_lcb_nv {p : ℕ} (u : Fin p → ℝ) :
    ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin p))‖ = √(u ⬝ᵥ u) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp [dotProduct, sq]

lemma aux_lcb_spec_bound {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℝ) (w : Fin q → ℝ) :
    √((M *ᵥ w) ⬝ᵥ (M *ᵥ w)) ≤ specNorm M * √(w ⬝ᵥ w) := by
  have h := M.l2_opNorm_mulVec (WithLp.toLp 2 w)
  rw [← aux_lcb_nv, ← aux_lcb_nv]
  exact h

end l2

lemma aux_lcb_frob_bound {p q : ℕ} (K : Matrix (Fin p) (Fin q) ℝ) (w : Fin q → ℝ) :
    √((K *ᵥ w) ⬝ᵥ (K *ᵥ w)) ≤ frobNorm K * √(w ⬝ᵥ w) := by
  unfold frobNorm
  have hnn : 0 ≤ ∑ i, ∑ j, K i j ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg (K i j)
  rw [← Real.sqrt_mul hnn]
  apply Real.sqrt_le_sqrt
  rw [Finset.sum_mul]
  unfold dotProduct
  apply Finset.sum_le_sum
  intro i _
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => K i j) w
  simp only [Matrix.mulVec, dotProduct] at h ⊢
  rw [← sq]
  convert h using 2
  simp [sq]

lemma aux_lcb_frob_sq {p q : ℕ} (K : Matrix (Fin p) (Fin q) ℝ) :
    frobNorm K ^ 2 = Matrix.trace (K.transpose * K) := by
  unfold frobNorm
  have hnn : 0 ≤ ∑ i, ∑ j, K i j ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg (K i j)
  rw [Real.sq_sqrt hnn]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, sq]
  exact Finset.sum_comm

/-- The Lyapunov operator `X ↦ Mᵀ X + X M`. -/
noncomputable def aux_lcb_L {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ where
  toFun X := M.transpose * X + X * M
  map_add' X Y := by simp only [Matrix.mul_add, Matrix.add_mul]; abel
  map_smul' c X := by simp [smul_add]

lemma aux_lcb_L_apply {n : ℕ} (M X : Matrix (Fin n) (Fin n) ℝ) :
    aux_lcb_L M X = M.transpose * X + X * M := rfl

lemma aux_lcb_tr_vmv {n : ℕ} (u : Fin n → ℝ) (P : Matrix (Fin n) (Fin n) ℝ) :
    (vecMulVec u (star u) * P).trace = u ⬝ᵥ (P *ᵥ u) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec_apply, star_trivial,
    dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma aux_lcb_rank_inj {n r : ℕ} (C : Matrix (Fin r) (Fin n) ℝ) (hC : C.rank = r)
    (u : Fin r → ℝ) (hu : C.transpose *ᵥ u = 0) : u = 0 := by
  have h1 : C.transpose.rank = r := by rw [Matrix.rank_transpose, hC]
  have h2 := LinearMap.finrank_range_add_finrank_ker (C.transpose.mulVecLin)
  rw [show Module.finrank ℝ (LinearMap.range C.transpose.mulVecLin) = C.transpose.rank from rfl,
    h1, Module.finrank_fin_fun] at h2
  have h3 : Module.finrank ℝ (LinearMap.ker C.transpose.mulVecLin) = 0 := by omega
  rw [Submodule.finrank_eq_zero] at h3
  have : u ∈ LinearMap.ker C.transpose.mulVecLin := by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]; exact hu
  rw [h3] at this
  simpa using this


noncomputable def aux_lcb_LE {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    (Fin n → Fin n → ℝ) →ₗ[ℝ] (Fin n → Fin n → ℝ) where
  toFun X := (M.transpose * Matrix.of X + Matrix.of X * M : Matrix (Fin n) (Fin n) ℝ)
  map_add' X Y := (aux_lcb_L M).map_add X Y
  map_smul' c X := (aux_lcb_L M).map_smul c X

/-- Quadratic form bounded by trace for PSD matrices. -/
lemma aux_lcb_quad_le_trace {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) (hX : X.PosSemidef)
    (a : Fin n → ℝ) : a ⬝ᵥ X *ᵥ a ≤ X.trace * (a ⬝ᵥ a) := by
  obtain ⟨k, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hX
  have e1 : a ⬝ᵥ X *ᵥ a = (vecMulVec a (star a) * X).trace := (aux_lcb_tr_vmv a X).symm
  rw [e1, hv, Matrix.mul_sum, Matrix.trace_sum, Matrix.trace_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [aux_lcb_tr_vmv]
  have h2 : (vecMulVec (v i) (star (v i))).trace = v i ⬝ᵥ v i := by simp
  rw [h2]
  have h3 : a ⬝ᵥ (vecMulVec (v i) (star (v i)) *ᵥ a) = (v i ⬝ᵥ a) * (v i ⬝ᵥ a) := by
    simp only [star_trivial, Matrix.vecMulVec_mulVec, dotProduct_smul]
    rw [dotProduct_comm a (v i), op_smul_eq_mul]
  rw [h3]
  have := aux_lcb_cs (v i) a
  have h4 := aux_lcb_dot_self_nonneg (v i)
  have h5 := aux_lcb_dot_self_nonneg a
  have h6 : |v i ⬝ᵥ a| ^ 2 ≤ (√(v i ⬝ᵥ v i) * √(a ⬝ᵥ a)) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) this 2
  rw [sq_abs, mul_pow, Real.sq_sqrt h4, Real.sq_sqrt h5] at h6
  nlinarith

lemma aux_lcb_trace_bound {n : ℕ} (X M : Matrix (Fin n) (Fin n) ℝ) (hX : X.PosSemidef) (c : ℝ)
    (hM : ∀ u : Fin n → ℝ, -(u ⬝ᵥ M *ᵥ u) ≤ c * (u ⬝ᵥ u)) :
    -(X * M).trace ≤ c * X.trace := by
  obtain ⟨k, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hX
  rw [hv, Finset.sum_mul, Matrix.trace_sum, Matrix.trace_sum, Finset.mul_sum,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [aux_lcb_tr_vmv]
  have h2 : (vecMulVec (v i) (star (v i))).trace = v i ⬝ᵥ v i := by simp
  rw [h2]
  exact hM (v i)

lemma aux_lcb_eig_real {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (z : ℂ)
    (hz : z ∈ spectrum ℂ (M.map (algebraMap ℝ ℂ))) :
    ∃ a b : Fin n → ℝ, 0 < a ⬝ᵥ a + b ⬝ᵥ b ∧ M *ᵥ a = z.re • a - z.im • b ∧
      M *ᵥ b = z.im • a + z.re • b := by
  rw [aux_lcb_mem_spec'] at hz
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hz
  have hv' : ∀ i, ∑ j, (M i j : ℂ) * v j = z * v i := by
    intro i
    have := congrFun hv i
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at this
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, sub_eq_zero] at this
    rw [this]
    simp [Matrix.mulVec, dotProduct]
  refine ⟨fun i => (v i).re, fun i => (v i).im, ?_, ?_, ?_⟩
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hv0
    have hpos : 0 < Complex.normSq (v i) := Complex.normSq_pos.mpr hi
    have e : (fun i => (v i).re) ⬝ᵥ (fun i => (v i).re) + (fun i => (v i).im) ⬝ᵥ (fun i => (v i).im)
        = ∑ j, Complex.normSq (v j) := by
      simp only [dotProduct, ← Finset.sum_add_distrib, Complex.normSq_apply]
    rw [e]
    refine lt_of_lt_of_le hpos ?_
    exact Finset.single_le_sum (f := fun j => Complex.normSq (v j))
      (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
  · funext i
    have := congrArg Complex.re (hv' i)
    simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero] at this
    simp only [Matrix.mulVec, dotProduct, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [this]
  · funext i
    have := congrArg Complex.im (hv' i)
    simp only [Complex.im_sum, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      add_zero] at this
    simp only [Matrix.mulVec, dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [this]
    ring

lemma aux_lcb_lyap_eig {n : ℕ} (M X W : Matrix (Fin n) (Fin n) ℝ)
    (hX : M.transpose * X + X * M + W = 0) (a b : Fin n → ℝ) (α β : ℝ)
    (ha : M *ᵥ a = α • a - β • b) (hb : M *ᵥ b = β • a + α • b) :
    a ⬝ᵥ W *ᵥ a + b ⬝ᵥ W *ᵥ b = -2 * α * (a ⬝ᵥ X *ᵥ a + b ⬝ᵥ X *ᵥ b) := by
  have hW : W = -(M.transpose * X + X * M) := eq_neg_of_add_eq_zero_right hX
  have q1 : ∀ u : Fin n → ℝ, u ⬝ᵥ W *ᵥ u = -((M *ᵥ u) ⬝ᵥ X *ᵥ u + u ⬝ᵥ X *ᵥ (M *ᵥ u)) := by
    intro u
    rw [hW, Matrix.neg_mulVec, dotProduct_neg, Matrix.add_mulVec, dotProduct_add,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec u M.transpose,
      Matrix.vecMul_transpose]
  rw [q1, q1, ha, hb]
  simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_add,
    dotProduct_sub, add_dotProduct, sub_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring


lemma aux_lcb_spec_finite {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    (spectrum ℂ (M.map (algebraMap ℝ ℂ))).Finite := Matrix.finite_spectrum _

lemma aux_lcb_spec_nonempty {n : ℕ} (hn : 0 < n) (M : Matrix (Fin n) (Fin n) ℝ) :
    (spectrum ℂ (M.map (algebraMap ℝ ℂ))).Nonempty := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (M.map (algebraMap ℝ ℂ)).charpoly (by
    rw [Matrix.charpoly_degree_eq_dim, Fintype.card_fin]
    exact_mod_cast hn.ne')
  exact ⟨z, Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hz⟩

lemma aux_lcb_le_maxRe {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (z : ℂ)
    (hz : z ∈ spectrum ℂ (M.map (algebraMap ℝ ℂ))) : z.re ≤ maxRe M :=
  le_csSup ((aux_lcb_spec_finite M).image _).bddAbove (Set.mem_image_of_mem _ hz)

lemma aux_lcb_maxRe_mem {n : ℕ} (hn : 0 < n) (M : Matrix (Fin n) (Fin n) ℝ) :
    ∃ z ∈ spectrum ℂ (M.map (algebraMap ℝ ℂ)), z.re = maxRe M :=
  ((aux_lcb_spec_nonempty hn M).image _).csSup_mem ((aux_lcb_spec_finite M).image _)

lemma aux_lcb_maxRe_neg {n : ℕ} (hn : 0 < n) (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsHurwitz M) :
    maxRe M < 0 := by
  obtain ⟨z, hz, hzr⟩ := aux_lcb_maxRe_mem hn M
  rw [← hzr]; exact hM z hz

/-- Core of (3.1): `λ₁(Q) / (-2 maxRe M) ≤ tr X`. -/
lemma aux_lcb_trace_lower {n : ℕ} (hn : 0 < n) (M X W : Matrix (Fin n) (Fin n) ℝ)
    (hM : IsHurwitz M) (hXpsd : X.PosSemidef) (hX : M.transpose * X + X * M + W = 0) (q : ℝ)
    (hW : ∀ v : Fin n → ℝ, q * (v ⬝ᵥ v) ≤ v ⬝ᵥ W *ᵥ v) :
    q / (-2 * maxRe M) ≤ X.trace := by
  obtain ⟨z, hz, hzr⟩ := aux_lcb_maxRe_mem hn M
  have hneg := aux_lcb_maxRe_neg hn M hM
  obtain ⟨a, b, hab, ha, hb⟩ := aux_lcb_eig_real M z hz
  have hid := aux_lcb_lyap_eig M X W hX a b z.re z.im ha hb
  have h1 := hW a
  have h2 := hW b
  have h3 := aux_lcb_quad_le_trace X hXpsd a
  have h4 := aux_lcb_quad_le_trace X hXpsd b
  rw [hzr] at hid
  have hpos : 0 < -2 * maxRe M := by linarith
  rw [div_le_iff₀ hpos]
  have h5 : q * (a ⬝ᵥ a + b ⬝ᵥ b) ≤ -2 * maxRe M * (X.trace * (a ⬝ᵥ a + b ⬝ᵥ b)) := by
    have : a ⬝ᵥ X *ᵥ a + b ⬝ᵥ X *ᵥ b ≤ X.trace * (a ⬝ᵥ a + b ⬝ᵥ b) := by nlinarith
    nlinarith
  have h6 : q ≤ -2 * maxRe M * X.trace := by
    by_contra hc
    push Not at hc
    have : -2 * maxRe M * X.trace * (a ⬝ᵥ a + b ⬝ᵥ b) < q * (a ⬝ᵥ a + b ⬝ᵥ b) :=
      mul_lt_mul_of_pos_right hc hab
    nlinarith
  linarith

lemma aux_lcb_det_lower {n : ℕ} (N : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ) (ε : ℝ) (hε : 0 ≤ ε)
    (hε1 : ε ≤ 1) (h : ∀ z ∈ spectrum ℂ N, ε ≤ ‖μ - z‖) :
    ε ^ n ≤ ‖(Matrix.scalar (Fin n) μ - N).det‖ := by
  rw [← Matrix.eval_charpoly,
    (IsAlgClosed.splits N.charpoly).eval_eq_prod_roots_of_monic N.charpoly_monic]
  have hcard : Multiset.card N.charpoly.roots ≤ n := by
    have := Polynomial.card_roots' N.charpoly
    rwa [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at this
  have key : ∀ s : Multiset ℂ, (∀ z ∈ s, ε ≤ ‖μ - z‖) →
      ε ^ Multiset.card s ≤ ‖(s.map (μ - ·)).prod‖ := by
    intro s
    induction s using Multiset.induction_on with
    | empty => intro _; simp
    | cons a s ih =>
      intro hs
      rw [Multiset.map_cons, Multiset.prod_cons, norm_mul, Multiset.card_cons, pow_succ]
      have h1 := ih (fun z hz => hs z (Multiset.mem_cons_of_mem hz))
      have h2 := hs a (Multiset.mem_cons_self a s)
      calc ε ^ Multiset.card s * ε ≤ ‖(s.map (μ - ·)).prod‖ * ‖μ - a‖ :=
            mul_le_mul h1 h2 hε (norm_nonneg _)
        _ = _ := mul_comm _ _
  have := key N.charpoly.roots (fun z hz => h z (by
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
    exact (Polynomial.mem_roots N.charpoly_monic.ne_zero).mp hz))
  exact (pow_le_pow_of_le_one hε hε1 hcard).trans this

lemma aux_lcb_cont_map {n : ℕ} :
    Continuous (fun M : Matrix (Fin n) (Fin n) ℝ => M.map (algebraMap ℝ ℂ)) :=
  continuous_id.matrix_map (by rw [Complex.coe_algebraMap]; exact Complex.continuous_ofReal)

lemma aux_lcb_eig_approx {n : ℕ} (Ms : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (M : Matrix (Fin n) (Fin n) ℝ) (hlim : Tendsto Ms atTop (𝓝 M)) (μ : ℂ)
    (hμ : μ ∈ spectrum ℂ (M.map (algebraMap ℝ ℂ))) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ j in atTop, ∃ z ∈ spectrum ℂ ((Ms j).map (algebraMap ℝ ℂ)), ‖μ - z‖ < ε := by
  set δ := min ε 1 with hδdef
  have hδ : 0 < δ := lt_min hε one_pos
  have hdet0 : (Matrix.scalar (Fin n) μ - M.map (algebraMap ℝ ℂ)).det = 0 :=
    (aux_lcb_mem_spec _ _).mp hμ
  have hc : Continuous (fun M' : Matrix (Fin n) (Fin n) ℝ =>
      ‖(Matrix.scalar (Fin n) μ - M'.map (algebraMap ℝ ℂ)).det‖) :=
    Continuous.norm (Continuous.matrix_det (continuous_const.sub aux_lcb_cont_map))
  have ht := (hc.tendsto M).comp hlim
  simp only [hdet0, norm_zero] at ht
  have hev := ht.eventually (gt_mem_nhds (pow_pos hδ n))
  filter_upwards [hev] with j hj
  by_contra hcon
  push Not at hcon
  have := aux_lcb_det_lower ((Ms j).map (algebraMap ℝ ℂ)) μ δ hδ.le (min_le_right _ _)
    (fun z hz => (min_le_left _ _).trans (hcon z hz))
  simp only [Function.comp_apply] at hj
  linarith


section openness
open scoped Matrix.Norms.L2Operator

noncomputable def aux_lcb_nrm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ‖M.map (algebraMap ℝ ℂ)‖ * ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖

lemma aux_lcb_eig_norm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (z : ℂ)
    (hz : z ∈ spectrum ℂ (M.map (algebraMap ℝ ℂ))) : ‖z‖ ≤ aux_lcb_nrm M :=
  spectrum.norm_le_norm_mul_of_mem hz

lemma aux_lcb_cont_nrm {n : ℕ} : Continuous (aux_lcb_nrm (n := n)) :=
  (continuous_norm.comp aux_lcb_cont_map).mul continuous_const

end openness

lemma aux_lcb_nonhurwitz_closed {n : ℕ} :
    IsClosed {M : Matrix (Fin n) (Fin n) ℝ | ¬ IsHurwitz M} := by
  have : SequentialSpace (Matrix (Fin n) (Fin n) ℝ) :=
    inferInstanceAs (SequentialSpace (Fin n → Fin n → ℝ))
  apply IsSeqClosed.isClosed
  intro Ms M hMs hlim
  simp only [Set.mem_ofPred_eq, IsHurwitz, not_forall, not_lt] at hMs ⊢
  choose z hz hzre using hMs
  have hnt := (aux_lcb_cont_nrm.tendsto M).comp hlim
  obtain ⟨B0, hB0⟩ := hnt.bddAbove_range
  have hB : ∀ j, z j ∈ Metric.closedBall (0 : ℂ) B0 := by
    intro j
    rw [mem_closedBall_zero_iff]
    exact (aux_lcb_eig_norm _ _ (hz j)).trans (hB0 ⟨j, rfl⟩)
  obtain ⟨w, -, φ, hφ, hzφ⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hB
  refine ⟨w, ?_, ?_⟩
  · rw [aux_lcb_mem_spec']
    have hc : Continuous (fun p : ℂ × Matrix (Fin n) (Fin n) ℝ =>
        (p.1 • (1 : Matrix (Fin n) (Fin n) ℂ) - p.2.map (algebraMap ℝ ℂ)).det) :=
      Continuous.matrix_det ((continuous_fst.smul continuous_const).sub
        (aux_lcb_cont_map.comp continuous_snd))
    have h1 := (hc.tendsto (w, M)).comp (hzφ.prodMk_nhds (hlim.comp hφ.tendsto_atTop))
    have h2 : ∀ j, ((z (φ j)) • (1 : Matrix (Fin n) (Fin n) ℂ)
        - (Ms (φ j)).map (algebraMap ℝ ℂ)).det = 0 :=
      fun j => (aux_lcb_mem_spec' _ _).mp (hz (φ j))
    have h3 : (fun j => ((z (φ j)) • (1 : Matrix (Fin n) (Fin n) ℂ)
        - (Ms (φ j)).map (algebraMap ℝ ℂ)).det) = fun _ => 0 := funext h2
    have h4 : Tendsto (fun j => ((z (φ j)) • (1 : Matrix (Fin n) (Fin n) ℂ)
        - (Ms (φ j)).map (algebraMap ℝ ℂ)).det) atTop
        (𝓝 ((w • (1 : Matrix (Fin n) (Fin n) ℂ) - M.map (algebraMap ℝ ℂ)).det)) := h1
    rw [h3] at h4
    exact tendsto_nhds_unique h4 tendsto_const_nhds
  · have := (Complex.continuous_re.tendsto w).comp hzφ
    exact ge_of_tendsto this (Eventually.of_forall fun j => hzre (φ j))

lemma aux_lcb_stab_open {n m r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) : IsOpen (stabSet A B C) := by
  have h1 : IsOpen {M : Matrix (Fin n) (Fin n) ℝ | IsHurwitz M} := by
    have := (aux_lcb_nonhurwitz_closed (n := n)).isOpen_compl
    simpa [Set.compl_ofPred] using this
  have hc : Continuous (fun K : Matrix (Fin m) (Fin r) ℝ => A - B * K * C) :=
    continuous_const.sub ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)
  exact h1.preimage hc

/-- Continuity of the Lyapunov solution along a continuous family of Hurwitz matrices. -/
lemma aux_lcb_lyap_contOn {n : ℕ} {P : Type*} [TopologicalSpace P]
    (Mf Wf : P → Matrix (Fin n) (Fin n) ℝ) (hMc : Continuous Mf) (hWc : Continuous Wf)
    (S : Set P) (hS : ∀ p ∈ S, IsHurwitz (Mf p)) :
    ContinuousOn (fun p => lyapSol (Mf p) (Wf p)) S := by
  set Lc : P → ((Fin n → Fin n → ℝ) →L[ℝ] (Fin n → Fin n → ℝ)) :=
    fun p => LinearMap.toContinuousLinearMap (aux_lcb_LE (Mf p)) with hLc
  have hLc_cont : Continuous Lc := by
    refine continuous_clm_apply.mpr fun Y => ?_
    show Continuous fun p => ((Mf p).transpose * Matrix.of Y + Matrix.of Y * Mf p :
      Matrix (Fin n) (Fin n) ℝ)
    exact (hMc.matrix_transpose.matrix_mul continuous_const).add
      (continuous_const.matrix_mul hMc)
  have hunit : ∀ p ∈ S, ∃ u : ((Fin n → Fin n → ℝ) →L[ℝ] (Fin n → Fin n → ℝ))ˣ,
      (u : (Fin n → Fin n → ℝ) →L[ℝ] (Fin n → Fin n → ℝ)) = Lc p := by
    intro p hp
    have hinj : Function.Injective (aux_lcb_LE (Mf p)) := by
      intro Y Z h
      have h' : (Mf p).transpose * Matrix.of Y + Matrix.of Y * Mf p
          = (Mf p).transpose * Matrix.of Z + Matrix.of Z * Mf p := h
      have hYZ : (Mf p).transpose * (Matrix.of Y - Matrix.of Z)
          + (Matrix.of Y - Matrix.of Z) * Mf p = 0 := by
        rw [Matrix.mul_sub, Matrix.sub_mul]
        calc _ = ((Mf p).transpose * Matrix.of Y + Matrix.of Y * Mf p)
              - ((Mf p).transpose * Matrix.of Z + Matrix.of Z * Mf p) := by abel
          _ = 0 := by rw [h', sub_self]
      have := aux_lcb_lyap_unique (Mf p) _ (hS p hp) hYZ
      exact sub_eq_zero.mp this
    have hsurj := LinearMap.injective_iff_surjective.mp hinj
    let e := (LinearEquiv.ofBijective (aux_lcb_LE (Mf p)) ⟨hinj, hsurj⟩).toContinuousLinearEquiv
    refine ⟨ContinuousLinearEquiv.toUnit e, ?_⟩
    ext1 Y
    rfl
  set w : P → (Fin n → Fin n → ℝ) := fun p => -(Matrix.of.symm (Wf p)) with hw
  have hw_cont : Continuous w := hWc.neg
  set g : P → Matrix (Fin n) (Fin n) ℝ := fun p => Matrix.of (Ring.inverse (Lc p) (w p)) with hg
  have hg_spec : ∀ p ∈ S, (Mf p).transpose * g p + g p * Mf p + Wf p = 0 := by
    intro p hp
    obtain ⟨u, hu⟩ := hunit p hp
    have h1 : Lc p (Ring.inverse (Lc p) (w p)) = w p := by
      rw [← hu, Ring.inverse_unit]
      show ((u : (Fin n → Fin n → ℝ) →L[ℝ] (Fin n → Fin n → ℝ)) * ↑u⁻¹) (w p) = w p
      rw [Units.mul_inv]; rfl
    have h2 : (Mf p).transpose * g p + g p * Mf p = -Wf p := h1
    rw [h2, neg_add_cancel]
  have hg_cont : ∀ p ∈ S, ContinuousAt g p := by
    intro p hp
    obtain ⟨u, hu⟩ := hunit p hp
    have h1 : ContinuousAt (fun t => Ring.inverse (Lc t)) p := by
      have := NormedRing.inverse_continuousAt u
      rw [hu] at this
      exact this.comp hLc_cont.continuousAt
    exact h1.clm_apply hw_cont.continuousAt
  refine ContinuousOn.congr (f := g) (continuousOn_of_forall_continuousAt hg_cont) ?_
  intro p hp
  obtain ⟨Z, _, hZ⟩ := aux_lcb_lyap_exists_unique (Mf p) (Wf p) (hS p hp)
  show lyapSol (Mf p) (Wf p) = g p
  rw [hZ _ (aux_lcb_lyapSol_spec _ _ (hS p hp)), hZ _ (hg_spec p hp)]


section l2b
open scoped Matrix.Norms.L2Operator

lemma aux_lcb_specNorm_nonneg {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℝ) : 0 ≤ specNorm M :=
  norm_nonneg M

lemma aux_lcb_specNorm_pos {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℝ) (h : M ≠ 0) :
    0 < specNorm M :=
  norm_pos_iff.mpr h

end l2b

lemma aux_lcb_arith1 (LS LR LC N a b0 b1 : ℝ) (hc : 0 < LS * LR * LC) (ha : 0 ≤ a)
    (hb : 0 < b0 * b1) (hN : 1 ≤ N) :
    LS * LR * LC / (2 * (a + b0 * b1)) * N ≤
      LS * LR * N ^ 2 * LC / (2 * a + 2 * N * b0 * b1) := by
  have hN0 : 0 < N := by linarith
  have hd1 : 0 < 2 * (a + b0 * b1) := by positivity
  have hd2 : 0 < 2 * a + 2 * N * b0 * b1 := by
    have : 0 < N * (b0 * b1) := mul_pos hN0 hb
    nlinarith
  rw [div_mul_eq_mul_div, div_le_div_iff₀ hd1 hd2]
  have key : 0 ≤ (LS * LR * LC) * N * (2 * a * (N - 1)) := by
    have : 0 ≤ N - 1 := by linarith
    positivity
  nlinarith [key]

lemma aux_lcb_arith2 (b c1 ε m : ℝ) (_hc1 : 0 < c1) (hε : 2 * ε * (|b| + 1) = c1)
    (hm0 : m < 0) (hm : -ε < m) : b ≤ c1 / (-2 * m) := by
  have hpos : 0 < -2 * m := by linarith
  rw [le_div_iff₀ hpos]
  have h1 : b * (-2 * m) ≤ |b| * (-2 * m) := mul_le_mul_of_nonneg_right (le_abs_self b) hpos.le
  have h2 : |b| * (-2 * m) ≤ (|b| + 1) * (-2 * m) := by nlinarith
  have h3 : (|b| + 1) * (-2 * m) ≤ (|b| + 1) * (2 * ε) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  nlinarith

theorem aux_lcb_main {n m r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (Sig : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q.PosDef) (hR : R.PosDef) (hSig : Sig.PosDef) (hC : C.rank = r) (hB : B ≠ 0) :
    ContinuousOn (lqrCost A B C Q R Sig) (stabSet A B C) ∧
    (∀ Ks : ℕ → Matrix (Fin m) (Fin r) ℝ, (∀ j, Ks j ∈ stabSet A B C) →
      Tendsto (fun j => frobNorm (Ks j)) atTop atTop →
      Tendsto (fun j => lqrCost A B C Q R Sig (Ks j)) atTop atTop) ∧
    (∀ (Ks : ℕ → Matrix (Fin m) (Fin r) ℝ) (K : Matrix (Fin m) (Fin r) ℝ),
      (∀ j, Ks j ∈ stabSet A B C) → K ∈ frontier (stabSet A B C) →
      Tendsto Ks atTop (𝓝 K) →
      Tendsto (fun j => lqrCost A B C Q R Sig (Ks j)) atTop atTop) ∧
    (∀ K ∈ stabSet A B C,
      lamMin Sig * lamMin Q / (-2 * maxRe (A - B * K * C)) ≤ lqrCost A B C Q R Sig K ∧
      lamMin Sig * lamMin R * frobNorm K ^ 2 * lamMin (C * C.transpose) /
          (2 * specNorm A + 2 * frobNorm K * specNorm B * specNorm C)
        ≤ lqrCost A B C Q R Sig K) := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exact absurd (by ext i j; exact i.elim0) hB
    · exact h
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · exact absurd (by ext i j; exact j.elim0) hB
    · exact h
  have hcontAK : Continuous (fun K : Matrix (Fin m) (Fin r) ℝ => A - B * K * C) :=
    continuous_const.sub ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)
  have hLS0 : 0 ≤ lamMin Sig := aux_lcb_lamMin_nonneg Sig hSig.posSemidef
  have hLR0 : 0 ≤ lamMin R := aux_lcb_lamMin_nonneg R hR.posSemidef
  have hLS : 0 < lamMin Sig := aux_lcb_lamMin_pos Sig hSig hn
  have hLQ : 0 < lamMin Q := aux_lcb_lamMin_pos Q hQ hn
  have hCC : (C * C.transpose).PosSemidef := by
    have := Matrix.posSemidef_self_mul_conjTranspose C
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hLC0 : 0 ≤ lamMin (C * C.transpose) := aux_lcb_lamMin_nonneg _ hCC
  -- facts about `X(K)`
  have hXfacts : ∀ K ∈ stabSet A B C,
      (A - B * K * C).transpose * lyapX A B C Q R K + lyapX A B C Q R K * (A - B * K * C)
        + (C.transpose * K.transpose * R * K * C + Q) = 0 ∧
      (lyapX A B C Q R K).PosSemidef ∧
      lamMin Sig * (lyapX A B C Q R K).trace ≤ lqrCost A B C Q R Sig K ∧
      (C.transpose * K.transpose * R * K * C).PosSemidef := by
    intro K hK
    have hKH : IsHurwitz (A - B * K * C) := hK
    have hX : (A - B * K * C).transpose * lyapX A B C Q R K + lyapX A B C Q R K * (A - B * K * C)
        + (C.transpose * K.transpose * R * K * C + Q) = 0 := aux_lcb_lyapSol_spec _ _ hKH
    have hKC : (C.transpose * K.transpose * R * K * C).PosSemidef := by
      have := hR.posSemidef.conjTranspose_mul_mul_same (K * C)
      rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_mul] at this
      simpa only [Matrix.mul_assoc] using this
    have hWpsd : (C.transpose * K.transpose * R * K * C + Q).PosSemidef := hKC.add hQ.posSemidef
    have hWt : (C.transpose * K.transpose * R * K * C + Q).transpose =
        C.transpose * K.transpose * R * K * C + Q := by
      have := hWpsd.isHermitian
      rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
    have hXt := aux_lcb_lyap_symm _ _ _ hKH hWt hX
    have hXq := aux_lcb_lyap_psd _ _ _ hKH
      (fun v => by simpa using hWpsd.dotProduct_mulVec_nonneg v) hX
    have hXh : (lyapX A B C Q R K).IsHermitian := by
      rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]; exact hXt
    have hXpsd : (lyapX A B C Q R K).PosSemidef :=
      Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hXh (fun x => by simpa using hXq x)
    refine ⟨hX, hXpsd, ?_, hKC⟩
    have := aux_lcb_lamMin_le_trace Sig (lyapX A B C Q R K) hSig.isHermitian hXpsd
    rw [Matrix.trace_mul_comm] at this
    exact this
  -- bound (3.1)
  have hb1 : ∀ K ∈ stabSet A B C,
      lamMin Sig * lamMin Q / (-2 * maxRe (A - B * K * C)) ≤ lqrCost A B C Q R Sig K := by
    intro K hK
    obtain ⟨hX, hXpsd, hf, hKC⟩ := hXfacts K hK
    have hW : ∀ v : Fin n → ℝ, lamMin Q * (v ⬝ᵥ v) ≤
        v ⬝ᵥ (C.transpose * K.transpose * R * K * C + Q) *ᵥ v := by
      intro v
      rw [Matrix.add_mulVec, dotProduct_add]
      have h1 : 0 ≤ v ⬝ᵥ (C.transpose * K.transpose * R * K * C) *ᵥ v := by
        simpa using hKC.dotProduct_mulVec_nonneg v
      have h2 := aux_lcb_quad_ge Q hQ.isHermitian v
      linarith
    have ht := aux_lcb_trace_lower hn _ _ _ hK hXpsd hX (lamMin Q) hW
    rw [mul_div_assoc]
    exact (mul_le_mul_of_nonneg_left ht hLS0).trans hf
  -- bound (3.2)
  have hb2 : ∀ K ∈ stabSet A B C,
      lamMin Sig * lamMin R * frobNorm K ^ 2 * lamMin (C * C.transpose) /
          (2 * specNorm A + 2 * frobNorm K * specNorm B * specNorm C)
        ≤ lqrCost A B C Q R Sig K := by
    intro K hK
    obtain ⟨hX, hXpsd, hf, hKC⟩ := hXfacts K hK
    set X := lyapX A B C Q R K with hXdef
    set M := A - B * K * C with hMdef
    set N := frobNorm K with hNdef
    have hN0 : 0 ≤ N := Real.sqrt_nonneg _
    have hAn : 0 ≤ specNorm A := aux_lcb_specNorm_nonneg A
    have hBn : 0 ≤ specNorm B := aux_lcb_specNorm_nonneg B
    have hCn : 0 ≤ specNorm C := aux_lcb_specNorm_nonneg C
    have hTX : 0 ≤ X.trace := hXpsd.trace_nonneg
    have hf0 : 0 ≤ lqrCost A B C Q R Sig K := le_trans (mul_nonneg hLS0 hTX) hf
    set c := specNorm A + N * specNorm B * specNorm C with hc
    have hc0 : 0 ≤ c := by positivity
    have hMb : ∀ u : Fin n → ℝ, -(u ⬝ᵥ M *ᵥ u) ≤ c * (u ⬝ᵥ u) := by
      intro u
      set s := √(u ⬝ᵥ u) with hs
      have hss : s * s = u ⬝ᵥ u := Real.mul_self_sqrt (aux_lcb_dot_self_nonneg u)
      have hs0 : 0 ≤ s := Real.sqrt_nonneg _
      have e : M *ᵥ u = A *ᵥ u - B *ᵥ (K *ᵥ (C *ᵥ u)) := by
        rw [hMdef, Matrix.sub_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
      have i1 : |u ⬝ᵥ A *ᵥ u| ≤ specNorm A * (s * s) := by
        refine (aux_lcb_cs _ _).trans ?_
        have := mul_le_mul_of_nonneg_left (aux_lcb_spec_bound A u) hs0
        rw [← hs] at this
        linarith
      have i2 : |u ⬝ᵥ B *ᵥ (K *ᵥ (C *ᵥ u))| ≤ N * specNorm B * specNorm C * (s * s) := by
        refine (aux_lcb_cs _ _).trans ?_
        have j1 := aux_lcb_spec_bound B (K *ᵥ (C *ᵥ u))
        have j2 := aux_lcb_frob_bound K (C *ᵥ u)
        have j3 := aux_lcb_spec_bound C u
        rw [← hs] at j3
        rw [← hNdef] at j2
        have k1 : √((K *ᵥ (C *ᵥ u)) ⬝ᵥ (K *ᵥ (C *ᵥ u))) ≤ N * (specNorm C * s) :=
          j2.trans (mul_le_mul_of_nonneg_left j3 hN0)
        have k2 : √((B *ᵥ (K *ᵥ (C *ᵥ u))) ⬝ᵥ (B *ᵥ (K *ᵥ (C *ᵥ u)))) ≤
            specNorm B * (N * (specNorm C * s)) :=
          j1.trans (mul_le_mul_of_nonneg_left k1 hBn)
        have := mul_le_mul_of_nonneg_left k2 hs0
        rw [← hs]
        nlinarith
      rw [e, dotProduct_sub, hc, ← hss]
      have := neg_le_abs (u ⬝ᵥ A *ᵥ u)
      have := le_abs_self (u ⬝ᵥ B *ᵥ (K *ᵥ (C *ᵥ u)))
      nlinarith
    have hXt : X.transpose = X := by
      have := hXpsd.isHermitian
      rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
    have htr1 : (M.transpose * X).trace = (X * M).trace := by
      rw [← Matrix.trace_transpose, Matrix.transpose_mul, Matrix.transpose_transpose, hXt]
    have hTW : (C.transpose * K.transpose * R * K * C + Q).trace = -2 * (X * M).trace := by
      have hW := eq_neg_of_add_eq_zero_right hX
      rw [hW, Matrix.trace_neg, Matrix.trace_add, htr1]
      ring
    have hTB := aux_lcb_trace_bound X M hXpsd c hMb
    -- lower bound on `tr W`
    have hKCC : (K * C * (C.transpose * K.transpose)).PosSemidef := by
      have := Matrix.posSemidef_self_mul_conjTranspose (K * C)
      rwa [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_mul] at this
    have hKK : (K.transpose * K).PosSemidef := by
      have := Matrix.posSemidef_conjTranspose_mul_self K
      rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
    have t1 : (C.transpose * K.transpose * R * K * C).trace =
        (R * (K * C * (C.transpose * K.transpose))).trace := by
      rw [show C.transpose * K.transpose * R * K * C
          = (C.transpose * K.transpose) * (R * K * C) by simp only [Matrix.mul_assoc],
        Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]
    have t2 : (K * C * (C.transpose * K.transpose)).trace =
        (C * C.transpose * (K.transpose * K)).trace := by
      rw [show K * C * (C.transpose * K.transpose) = (K * (C * C.transpose)) * K.transpose by
          simp only [Matrix.mul_assoc], Matrix.trace_mul_comm, ← Matrix.mul_assoc,
        Matrix.trace_mul_comm]
    have i1 := aux_lcb_lamMin_le_trace R _ hR.isHermitian hKCC
    have i2 := aux_lcb_lamMin_le_trace (C * C.transpose) _ hCC.isHermitian hKK
    rw [← aux_lcb_frob_sq, ← hNdef] at i2
    rw [t2] at i1
    have hTQ : 0 ≤ Q.trace := hQ.posSemidef.trace_nonneg
    have hTW2 : lamMin R * (lamMin (C * C.transpose) * N ^ 2) ≤
        (C.transpose * K.transpose * R * K * C + Q).trace := by
      rw [Matrix.trace_add, t1]
      have := mul_le_mul_of_nonneg_left i2 hLR0
      linarith
    have hmain : lamMin Sig * lamMin R * N ^ 2 * lamMin (C * C.transpose) ≤
        lqrCost A B C Q R Sig K * (2 * specNorm A + 2 * N * specNorm B * specNorm C) := by
      have e1 : lamMin R * (lamMin (C * C.transpose) * N ^ 2) ≤ 2 * c * X.trace := by linarith
      have e2 := mul_le_mul_of_nonneg_left e1 hLS0
      have e3 := mul_le_mul_of_nonneg_left hf (by positivity : (0 : ℝ) ≤ 2 * c)
      have e4 : (2 * specNorm A + 2 * N * specNorm B * specNorm C) = 2 * c := by rw [hc]; ring
      rw [e4]
      nlinarith
    exact div_le_of_le_mul₀ (by positivity) hf0 hmain
  refine ⟨?_, ?_, ?_, fun K hK => ⟨hb1 K hK, hb2 K hK⟩⟩
  · -- continuity
    have hWc : Continuous (fun K : Matrix (Fin m) (Fin r) ℝ =>
        C.transpose * K.transpose * R * K * C + Q) :=
      ((((continuous_const.matrix_mul continuous_id.matrix_transpose).matrix_mul
        continuous_const).matrix_mul continuous_id).matrix_mul continuous_const).add
        continuous_const
    have hc := aux_lcb_lyap_contOn (fun K => A - B * K * C)
      (fun K => C.transpose * K.transpose * R * K * C + Q) hcontAK hWc (stabSet A B C)
      (fun K hK => hK)
    have ht : Continuous (fun X : Matrix (Fin n) (Fin n) ℝ => (X * Sig).trace) :=
      (continuous_id.matrix_mul continuous_const).matrix_trace
    exact ht.comp_continuousOn hc
  · -- blow-up at infinity
    intro Ks hKs hN
    rcases Nat.eq_zero_or_pos r with hr0 | hr
    · subst hr0
      exfalso
      have h0 : ∀ j, frobNorm (Ks j) = 0 := fun j => by simp [frobNorm]
      simp only [h0] at hN
      exact not_tendsto_const_atTop _ _ hN
    · have hCpd : (C * C.transpose).PosDef := by
        refine Matrix.PosDef.of_dotProduct_mulVec_pos hCC.isHermitian fun u hu => ?_
        have hw : C.transpose *ᵥ u ≠ 0 := fun h => hu (aux_lcb_rank_inj C hC u h)
        have e : star u ⬝ᵥ ((C * C.transpose) *ᵥ u) =
            (C.transpose *ᵥ u) ⬝ᵥ (C.transpose *ᵥ u) := by
          rw [star_trivial, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
            ← Matrix.mulVec_transpose]
        rw [e]
        refine lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg _) ?_
        intro h
        exact hw (dotProduct_self_eq_zero.mp h.symm)
      have hLC : 0 < lamMin (C * C.transpose) := aux_lcb_lamMin_pos _ hCpd hr
      have hLR : 0 < lamMin R := aux_lcb_lamMin_pos R hR hm
      have hC0 : C ≠ 0 := by
        intro h
        rw [h, Matrix.rank_zero] at hC
        omega
      have hBn : 0 < specNorm B := aux_lcb_specNorm_pos B hB
      have hCn : 0 < specNorm C := aux_lcb_specNorm_pos C hC0
      have hAn : 0 ≤ specNorm A := aux_lcb_specNorm_nonneg A
      have hc0 : 0 < lamMin Sig * lamMin R * lamMin (C * C.transpose) := by positivity
      have hbnd : ∀ᶠ j in atTop,
          lamMin Sig * lamMin R * lamMin (C * C.transpose) /
            (2 * (specNorm A + specNorm B * specNorm C)) * frobNorm (Ks j)
            ≤ lqrCost A B C Q R Sig (Ks j) := by
        filter_upwards [hN.eventually_ge_atTop 1] with j hj
        refine le_trans ?_ (hb2 (Ks j) (hKs j))
        exact aux_lcb_arith1 _ _ _ _ _ _ _ hc0 hAn (mul_pos hBn hCn) hj
      exact tendsto_atTop_mono' atTop hbnd (Tendsto.const_mul_atTop (by positivity) hN)
  · -- blow-up at the boundary
    intro Ks K hKs hKf hlim
    have hKnot : K ∉ stabSet A B C := by
      rw [(aux_lcb_stab_open A B C).frontier_eq] at hKf
      exact hKf.2
    have hnH : ¬ IsHurwitz (A - B * K * C) := hKnot
    simp only [IsHurwitz, not_forall, not_lt] at hnH
    obtain ⟨μ, hμ, hμre⟩ := hnH
    have hMlim : Tendsto (fun j => A - B * Ks j * C) atTop (𝓝 (A - B * K * C)) :=
      (hcontAK.tendsto K).comp hlim
    have hc1 : 0 < lamMin Sig * lamMin Q := mul_pos hLS hLQ
    rw [tendsto_atTop]
    intro b
    have hε : 0 < lamMin Sig * lamMin Q / (2 * (|b| + 1)) := by positivity
    filter_upwards [aux_lcb_eig_approx _ _ hMlim μ hμ _ hε] with j hj
    obtain ⟨z, hz, hzμ⟩ := hj
    have h1 := hb1 (Ks j) (hKs j)
    have hneg := aux_lcb_maxRe_neg hn _ (hKs j)
    have hzle := aux_lcb_le_maxRe _ z hz
    have hre : μ.re - z.re ≤ ‖μ - z‖ := by
      have := Complex.abs_re_le_norm (μ - z)
      rw [Complex.sub_re] at this
      exact (le_abs_self _).trans this
    have h2e : 2 * (lamMin Sig * lamMin Q / (2 * (|b| + 1))) * (|b| + 1) =
        lamMin Sig * lamMin Q := by
      field_simp
    have := aux_lcb_arith2 b _ _ _ hc1 h2e hneg (by linarith)
    linarith

end FatkhullinPolyak.Discrete

open FatkhullinPolyak.Discrete
open Filter Topology

theorem solution {n m r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (Sig : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q.PosDef) (hR : R.PosDef) (hSig : Sig.PosDef) (hC : C.rank = r) (hB : B ≠ 0) :
    ContinuousOn (lqrCost A B C Q R Sig) (stabSet A B C) ∧
    (∀ Ks : ℕ → Matrix (Fin m) (Fin r) ℝ, (∀ j, Ks j ∈ stabSet A B C) →
      Tendsto (fun j => frobNorm (Ks j)) atTop atTop →
      Tendsto (fun j => lqrCost A B C Q R Sig (Ks j)) atTop atTop) ∧
    (∀ (Ks : ℕ → Matrix (Fin m) (Fin r) ℝ) (K : Matrix (Fin m) (Fin r) ℝ),
      (∀ j, Ks j ∈ stabSet A B C) → K ∈ frontier (stabSet A B C) →
      Tendsto Ks atTop (𝓝 K) →
      Tendsto (fun j => lqrCost A B C Q R Sig (Ks j)) atTop atTop) ∧
    (∀ K ∈ stabSet A B C,
      lamMin Sig * lamMin Q / (-2 * maxRe (A - B * K * C)) ≤ lqrCost A B C Q R Sig K ∧
      lamMin Sig * lamMin R * frobNorm K ^ 2 * lamMin (C * C.transpose) /
          (2 * specNorm A + 2 * frobNorm K * specNorm B * specNorm C)
        ≤ lqrCost A B C Q R Sig K) :=
  aux_lcb_main A B C Q R Sig hQ hR hSig hC hB
