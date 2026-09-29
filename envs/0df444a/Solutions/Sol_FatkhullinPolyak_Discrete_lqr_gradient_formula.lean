-- Prove2me | solution 1 for FatkhullinPolyak.Discrete.lqr_gradient_formula
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:10:12.669469+00:00
-- url     : https://prove2.me/submissions/e4a91246-2cad-49e7-9373-f801c5451e2b

import Mathlib
import Definitions.Def_FatkhullinPolyak_Discrete_LQR

open Filter Topology

namespace FatkhullinPolyak.Discrete

theorem aux_lqrg_syl {n : ℕ} (P S Z : Matrix (Fin n) (Fin n) ℂ) (h : P * Z = Z * S)
    (hdisj : ∀ z, z ∈ spectrum ℂ P → z ∈ spectrum ℂ S → False) : Z = 0 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; ext i; exact i.elim0
  have hpow : ∀ k : ℕ, P ^ k * Z = Z * S ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih,
        Matrix.mul_assoc]
  set q := P.charpoly
  have hint : Polynomial.aeval P q * Z = Z * Polynomial.aeval S q := by
    rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range, Finset.sum_mul,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc, mul_smul_comm, hpow]
  rw [Matrix.aeval_self_charpoly, zero_mul] at hint
  have hunit : IsUnit (Polynomial.aeval S q) := by
    apply (spectrum.zero_notMem_iff ℂ).mp
    intro h0
    have hdeg : 0 < q.degree := by
      rw [Matrix.charpoly_degree_eq_dim]; simp [hn]
    rw [spectrum.map_polynomial_aeval_of_degree_pos S q hdeg] at h0
    obtain ⟨k, hk, hk0⟩ := h0
    exact hdisj k (Matrix.mem_spectrum_of_isRoot_charpoly hk0) hk
  exact (hunit.mul_left_eq_zero).mp hint.symm

theorem aux_lqrg_hurT {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsHurwitz M) :
    IsHurwitz M.transpose := by
  intro z hz
  apply hM
  rw [Matrix.transpose_map, Matrix.mem_spectrum_iff_isRoot_charpoly,
    Matrix.charpoly_transpose, ← Matrix.mem_spectrum_iff_isRoot_charpoly] at hz
  exact hz

theorem aux_lqrg_disj {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsHurwitz M) :
    ∀ z, z ∈ spectrum ℂ (M.map (algebraMap ℝ ℂ)) →
      z ∈ spectrum ℂ (-(M.map (algebraMap ℝ ℂ))) → False := by
  intro z h1 h2
  rw [← spectrum.neg_eq, Set.mem_neg] at h2
  have a1 := hM z h1
  have a2 := hM _ h2
  rw [Complex.neg_re] at a2
  linarith

theorem aux_lqrg_inj {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsHurwitz M)
    (Z : Matrix (Fin n) (Fin n) ℝ) (hZ : M.transpose * Z + Z * M = 0) : Z = 0 := by
  set f := algebraMap ℝ ℂ
  have hc : (M.map f).transpose * Z.map f = Z.map f * (-(M.map f)) := by
    have : (M.transpose * Z + Z * M).map f = (0 : Matrix (Fin n) (Fin n) ℝ).map f := by rw [hZ]
    rw [Matrix.map_add _ (map_add f), Matrix.map_zero _ (map_zero f)] at this
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map] at this
    rw [Matrix.mul_neg, eq_neg_iff_add_eq_zero]
    exact this
  have hZc := aux_lqrg_syl _ _ _ hc (by
    intro z h1 h2
    rw [← Matrix.transpose_map] at h1
    have h1' : z ∈ spectrum ℂ (M.map f) := by
      rw [Matrix.transpose_map, Matrix.mem_spectrum_iff_isRoot_charpoly,
        Matrix.charpoly_transpose, ← Matrix.mem_spectrum_iff_isRoot_charpoly] at h1
      exact h1
    exact aux_lqrg_disj M hM z h1' h2)
  ext i j
  have := congrFun (congrFun hZc i) j
  simpa [f] using this

theorem aux_lqrg_sol {n : ℕ} (M W : Matrix (Fin n) (Fin n) ℝ)
    (hinj : ∀ Z, M.transpose * Z + Z * M = 0 → Z = 0) :
    M.transpose * lyapSol M W + lyapSol M W * M + W = 0 ∧
    ∀ X, M.transpose * X + X * M + W = 0 → X = lyapSol M W := by
  let L : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ :=
    LinearMap.mulLeft ℝ M.transpose + LinearMap.mulRight ℝ M
  have hL : ∀ Z, L Z = M.transpose * Z + Z * M := fun Z => rfl
  have hinjL : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    intro Z hZ
    exact hinj Z (by rw [← hL]; exact hZ)
  obtain ⟨X0, hX0⟩ := (LinearMap.injective_iff_surjective.mp hinjL) (-W)
  have h1 : M.transpose * X0 + X0 * M = -W := by rw [← hL]; exact hX0
  have hex : ∃! X, M.transpose * X + X * M + W = 0 := by
    refine ⟨X0, by show M.transpose * X0 + X0 * M + W = 0; rw [h1]; simp, fun X hX => ?_⟩
    have e : M.transpose * (X - X0) + (X - X0) * M
        = (M.transpose * X + X * M + W) - (M.transpose * X0 + X0 * M) - W := by
      rw [Matrix.mul_sub, Matrix.sub_mul]; abel
    rw [hX, h1] at e
    simp only [zero_sub, neg_neg, sub_self] at e
    exact sub_eq_zero.mp (hinj _ e)
  unfold lyapSol
  rw [dif_pos hex]
  exact ⟨hex.choose_spec.1, fun X hX => hex.choose_spec.2 X hX⟩

theorem aux_lqrg_symm {n : ℕ} (M W : Matrix (Fin n) (Fin n) ℝ)
    (hinj : ∀ Z, M.transpose * Z + Z * M = 0 → Z = 0) (hW : W.transpose = W) :
    (lyapSol M W).transpose = lyapSol M W := by
  obtain ⟨h1, h2⟩ := aux_lqrg_sol M W hinj
  apply h2
  have := congrArg Matrix.transpose h1
  rw [Matrix.transpose_add, Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose, hW, Matrix.transpose_zero] at this
  rw [← this]; abel

section aux_lqrg_norms

attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup
  Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

theorem aux_lqrg_frob {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℝ) : frobNorm M = ‖M‖ := by
  rw [frobNorm, Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
  congr 1
  simp [sq_abs]

theorem aux_lqrg_entry {p q : ℕ} (P : Matrix (Fin p) (Fin q) ℝ) (i : Fin p) (j : Fin q) :
    |P i j| ≤ ‖P‖ := by
  rw [← aux_lqrg_frob, frobNorm, ← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  calc P i j ^ 2 ≤ ∑ j', P i j' ^ 2 :=
        Finset.single_le_sum (f := fun j' => P i j' ^ 2) (fun _ _ => sq_nonneg _)
          (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', P i' j' ^ 2 :=
        Finset.single_le_sum (f := fun i' => ∑ j', P i' j' ^ 2)
          (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)

theorem aux_lqrg_trace {p : ℕ} (P : Matrix (Fin p) (Fin p) ℝ) :
    |Matrix.trace P| ≤ p * ‖P‖ := by
  unfold Matrix.trace Matrix.diag
  calc |∑ i, P i i| ≤ ∑ i, |P i i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin p, ‖P‖ := Finset.sum_le_sum fun i _ => aux_lqrg_entry P i i
    _ = p * ‖P‖ := by simp

theorem aux_lqrg_coer {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hinj : ∀ Z, M.transpose * Z + Z * M = 0 → Z = 0) :
    ∃ κ, 0 ≤ κ ∧ ∀ Z, ‖Z‖ ≤ κ * ‖M.transpose * Z + Z * M‖ := by
  let L : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ :=
    LinearMap.mulLeft ℝ M.transpose + LinearMap.mulRight ℝ M
  have hL : ∀ Z, L Z = M.transpose * Z + Z * M := fun Z => rfl
  have hinjL : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    intro Z hZ
    exact hinj Z (by rw [← hL]; exact hZ)
  obtain ⟨K, _, hK⟩ := (LinearMap.injective_iff_antilipschitz L).mp hinjL
  refine ⟨K, K.2, fun Z => ?_⟩
  have := hK.le_mul_dist Z 0
  rw [map_zero, dist_zero_right, dist_zero_right, hL] at this
  exact this

theorem aux_lqrg_n3 {a b c d : ℕ} (A1 : Matrix (Fin a) (Fin b) ℝ) (A2 : Matrix (Fin b) (Fin c) ℝ)
    (A3 : Matrix (Fin c) (Fin d) ℝ) : ‖A1 * A2 * A3‖ ≤ ‖A1‖ * ‖A2‖ * ‖A3‖ :=
  (Matrix.frobenius_norm_mul _ _).trans
    (mul_le_mul_of_nonneg_right (Matrix.frobenius_norm_mul _ _) (norm_nonneg _))

theorem aux_lqrg_n4 {a b c d e : ℕ} (A1 : Matrix (Fin a) (Fin b) ℝ) (A2 : Matrix (Fin b) (Fin c) ℝ)
    (A3 : Matrix (Fin c) (Fin d) ℝ) (A4 : Matrix (Fin d) (Fin e) ℝ) :
    ‖A1 * A2 * A3 * A4‖ ≤ ‖A1‖ * ‖A2‖ * ‖A3‖ * ‖A4‖ :=
  (Matrix.frobenius_norm_mul _ _).trans
    (mul_le_mul_of_nonneg_right (aux_lqrg_n3 _ _ _) (norm_nonneg _))

theorem aux_lqrg_n5 {a b c d e f : ℕ} (A1 : Matrix (Fin a) (Fin b) ℝ)
    (A2 : Matrix (Fin b) (Fin c) ℝ) (A3 : Matrix (Fin c) (Fin d) ℝ) (A4 : Matrix (Fin d) (Fin e) ℝ)
    (A5 : Matrix (Fin e) (Fin f) ℝ) :
    ‖A1 * A2 * A3 * A4 * A5‖ ≤ ‖A1‖ * ‖A2‖ * ‖A3‖ * ‖A4‖ * ‖A5‖ :=
  (Matrix.frobenius_norm_mul _ _).trans
    (mul_le_mul_of_nonneg_right (aux_lqrg_n4 _ _ _ _) (norm_nonneg _))

theorem aux_lqrg_n6 {a b c d e f g : ℕ} (A1 : Matrix (Fin a) (Fin b) ℝ)
    (A2 : Matrix (Fin b) (Fin c) ℝ) (A3 : Matrix (Fin c) (Fin d) ℝ) (A4 : Matrix (Fin d) (Fin e) ℝ)
    (A5 : Matrix (Fin e) (Fin f) ℝ) (A6 : Matrix (Fin f) (Fin g) ℝ) :
    ‖A1 * A2 * A3 * A4 * A5 * A6‖ ≤ ‖A1‖ * ‖A2‖ * ‖A3‖ * ‖A4‖ * ‖A5‖ * ‖A6‖ :=
  (Matrix.frobenius_norm_mul _ _).trans
    (mul_le_mul_of_nonneg_right (aux_lqrg_n5 _ _ _ _ _) (norm_nonneg _))

theorem aux_lqrg_ar1 (κ b c e x d rr k tT : ℝ) (hκ : 0 ≤ κ) (_hb : 0 ≤ b) (hc : 0 ≤ c)
    (he : 0 ≤ e) (he1 : e ≤ 1) (_hx : 0 ≤ x) (hd : 0 ≤ d) (hr : 0 ≤ rr) (_hk : 0 ≤ k)
    (hs : κ * (2 * b * c * e) ≤ 1 / 2)
    (hT : tT ≤ c * e * rr * k * c + c * k * rr * e * c + c * e * rr * e * c)
    (hD : d ≤ κ * (2 * b * c * e * x + 2 * b * c * e * d + tT)) :
    d ≤ 2 * κ * (2 * b * c * x + c * c * rr * (2 * k + 1)) * e := by
  have h1 : κ * (2 * b * c * e * d) ≤ d / 2 := by
    have := mul_le_mul_of_nonneg_right hs hd
    nlinarith
  have hT' : tT ≤ c * c * rr * (2 * k + 1) * e := by
    have h0 : 0 ≤ c * c * rr * e := by positivity
    have : c * e * rr * e * c ≤ c * c * rr * e := by
      have := mul_le_mul_of_nonneg_left he1 h0
      nlinarith
    nlinarith
  have h2 : κ * tT ≤ κ * (c * c * rr * (2 * k + 1) * e) := mul_le_mul_of_nonneg_left hT' hκ
  have h3 : d ≤ κ * (2 * b * c * e * x) + κ * (2 * b * c * e * d) + κ * tT := by
    have : κ * (2 * b * c * e * x + 2 * b * c * e * d + tT)
        = κ * (2 * b * c * e * x) + κ * (2 * b * c * e * d) + κ * tT := by ring
    linarith
  have h4 : 2 * κ * (2 * b * c * x + c * c * rr * (2 * k + 1)) * e
      = 2 * (κ * (2 * b * c * e * x)) + 2 * (κ * (c * c * rr * (2 * k + 1) * e)) := by ring
  linarith

theorem aux_lqrg_trT {n : ℕ} (P Y : Matrix (Fin n) (Fin n) ℝ) (hY : Y.transpose = Y) :
    Matrix.trace (P * Y) = Matrix.trace (P.transpose * Y) := by
  rw [← Matrix.trace_transpose, Matrix.transpose_mul, hY, Matrix.trace_mul_comm]

theorem aux_lqrg_fi {p q : ℕ} (G E : Matrix (Fin p) (Fin q) ℝ) :
    frobInner G E = Matrix.trace (E.transpose * G) := by
  simp only [frobInner, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  simp [mul_comm]

set_option maxHeartbeats 1000000 in
theorem aux_lqrg_main {n m r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (Sig : Matrix (Fin n) (Fin n) ℝ)
    (hQs : Q.transpose = Q) (hRs : R.transpose = R) (hSs : Sig.transpose = Sig)
    (K : Matrix (Fin m) (Fin r) ℝ) (hK : K ∈ stabSet A B C) :
    ∀ ε > 0, ∃ δ > 0, ∀ E : Matrix (Fin m) (Fin r) ℝ, frobNorm E < δ →
      |lqrCost A B C Q R Sig (K + E) - lqrCost A B C Q R Sig K
          - frobInner (lqrGrad A B C Q R Sig K) E| ≤ ε * frobNorm E := by
  intro ε hε
  obtain ⟨M, hMdef⟩ : ∃ M, M = A - B * K * C := ⟨_, rfl⟩
  have hM : IsHurwitz M := by rw [hMdef]; exact hK
  have hinjM := aux_lqrg_inj M hM
  have hinjMT : ∀ Z, M.transpose.transpose * Z + Z * M.transpose = 0 → Z = 0 :=
    aux_lqrg_inj _ (aux_lqrg_hurT M hM)
  obtain ⟨W, hWdef⟩ : ∃ W, W = C.transpose * K.transpose * R * K * C + Q := ⟨_, rfl⟩
  have hWs : W.transpose = W := by
    rw [hWdef]
    simp only [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose, hQs, hRs,
      Matrix.mul_assoc]
  obtain ⟨X, hXdef⟩ : ∃ X, X = lyapX A B C Q R K := ⟨_, rfl⟩
  have hXl : X = lyapSol M W := by rw [hXdef, hMdef, hWdef]; rfl
  have hX : M.transpose * X + X * M + W = 0 := by rw [hXl]; exact (aux_lqrg_sol M W hinjM).1
  have hXs : X.transpose = X := by rw [hXl]; exact aux_lqrg_symm M W hinjM hWs
  obtain ⟨Y, hYdef⟩ : ∃ Y, Y = lyapY A B C Sig K := ⟨_, rfl⟩
  have hYl : Y = lyapSol M.transpose Sig := by rw [hYdef, hMdef]; rfl
  have hY : M * Y + Y * M.transpose + Sig = 0 := by
    have := (aux_lqrg_sol M.transpose Sig hinjMT).1
    rw [Matrix.transpose_transpose] at this
    rw [hYl]; exact this
  have hYs : Y.transpose = Y := by rw [hYl]; exact aux_lqrg_symm _ _ hinjMT hSs
  obtain ⟨κ, hκ, hcoer⟩ := aux_lqrg_coer M hinjM
  obtain ⟨b, hb⟩ : ∃ b, b = ‖B‖ := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = ‖C‖ := ⟨_, rfl⟩
  obtain ⟨rr, hrr⟩ : ∃ rr, rr = ‖R‖ := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k, k = ‖K‖ := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x, x = ‖X‖ := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = ‖Y‖ := ⟨_, rfl⟩
  have hb0 : 0 ≤ b := hb ▸ norm_nonneg _
  have hc0 : 0 ≤ c := hc ▸ norm_nonneg _
  have hrr0 : 0 ≤ rr := hrr ▸ norm_nonneg _
  have hk0 : 0 ≤ k := hk ▸ norm_nonneg _
  have hx0 : 0 ≤ x := hx ▸ norm_nonneg _
  have hy0 : 0 ≤ y := hy ▸ norm_nonneg _
  obtain ⟨γ, hγ⟩ : ∃ γ, γ = 2 * κ * (2 * b * c * x + c * c * rr * (2 * k + 1)) := ⟨_, rfl⟩
  have hγ0 : 0 ≤ γ := by rw [hγ]; positivity
  obtain ⟨Λ, hΛ⟩ : ∃ Λ, Λ = (n : ℝ) * y * (c * c * rr + 2 * b * c * γ) := ⟨_, rfl⟩
  have hΛ0 : 0 ≤ Λ := by rw [hΛ]; positivity
  refine ⟨min 1 (min (1 / (4 * κ * b * c + 1)) (ε / (Λ + 1))), ?_, ?_⟩
  · have h1 : 0 < 1 / (4 * κ * b * c + 1) := by positivity
    have h2 : 0 < ε / (Λ + 1) := by positivity
    exact lt_min one_pos (lt_min h1 h2)
  intro E hE
  rw [aux_lqrg_frob] at hE ⊢
  obtain ⟨e, he⟩ : ∃ e, e = ‖E‖ := ⟨_, rfl⟩
  rw [← he] at hE ⊢
  have he0 : 0 ≤ e := he ▸ norm_nonneg _
  have he1 : e ≤ 1 := le_of_lt (lt_of_lt_of_le hE (min_le_left _ _))
  have he2 : e < 1 / (4 * κ * b * c + 1) :=
    lt_of_lt_of_le hE ((min_le_right _ _).trans (min_le_left _ _))
  have he3 : e < ε / (Λ + 1) :=
    lt_of_lt_of_le hE ((min_le_right _ _).trans (min_le_right _ _))
  have hs : κ * (2 * b * c * e) ≤ 1 / 2 := by
    have h0 : 0 ≤ κ * b * c := by positivity
    rw [lt_div_iff₀ (by positivity)] at he2
    nlinarith
  -- norms of transposes
  have hCt : ‖C.transpose‖ = c := by rw [Matrix.frobenius_norm_transpose, hc]
  have hBt : ‖B.transpose‖ = b := by rw [Matrix.frobenius_norm_transpose, hb]
  have hEt : ‖E.transpose‖ = e := by rw [Matrix.frobenius_norm_transpose, he]
  have hKt : ‖K.transpose‖ = k := by rw [Matrix.frobenius_norm_transpose, hk]
  have hPE : ∀ Z : Matrix (Fin n) (Fin n) ℝ,
      ‖C.transpose * E.transpose * B.transpose * Z + Z * B * E * C‖ ≤ 2 * b * c * e * ‖Z‖ := by
    intro Z
    calc _ ≤ ‖C.transpose * E.transpose * B.transpose * Z‖ + ‖Z * B * E * C‖ := norm_add_le _ _
      _ ≤ ‖C.transpose‖ * ‖E.transpose‖ * ‖B.transpose‖ * ‖Z‖ + ‖Z‖ * ‖B‖ * ‖E‖ * ‖C‖ :=
          add_le_add (aux_lqrg_n4 _ _ _ _) (aux_lqrg_n4 _ _ _ _)
      _ = 2 * b * c * e * ‖Z‖ := by rw [hCt, hEt, hBt, ← hb, ← hc, ← he]; ring
  -- perturbed closed loop
  obtain ⟨M', hM'def⟩ : ∃ M', M' = A - B * (K + E) * C := ⟨_, rfl⟩
  have hM' : M' = M - B * E * C := by
    rw [hM'def, hMdef, Matrix.mul_add, Matrix.add_mul]; abel
  have hLM' : ∀ Z : Matrix (Fin n) (Fin n) ℝ, M'.transpose * Z + Z * M'
      = (M.transpose * Z + Z * M) - (C.transpose * E.transpose * B.transpose * Z + Z * B * E * C) := by
    intro Z
    rw [hM']
    simp only [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.mul_assoc]
    abel
  have hinjM' : ∀ Z, M'.transpose * Z + Z * M' = 0 → Z = 0 := by
    intro Z hZ
    have e1 : M.transpose * Z + Z * M
        = C.transpose * E.transpose * B.transpose * Z + Z * B * E * C := by
      have := hLM' Z
      rw [hZ] at this
      exact sub_eq_zero.mp this.symm
    have h2 := hcoer Z
    rw [e1] at h2
    have h3 := hPE Z
    have h4 : ‖Z‖ ≤ (1 / 2) * ‖Z‖ := by
      calc ‖Z‖ ≤ κ * (2 * b * c * e * ‖Z‖) := h2.trans (mul_le_mul_of_nonneg_left h3 hκ)
        _ = (κ * (2 * b * c * e)) * ‖Z‖ := by ring
        _ ≤ (1 / 2) * ‖Z‖ := mul_le_mul_of_nonneg_right hs (norm_nonneg _)
    have : ‖Z‖ ≤ 0 := by linarith [norm_nonneg Z]
    exact norm_le_zero_iff.mp this
  obtain ⟨W', hW'def⟩ : ∃ W', W' = C.transpose * (K + E).transpose * R * (K + E) * C + Q :=
    ⟨_, rfl⟩
  obtain ⟨X', hX'def⟩ : ∃ X', X' = lyapX A B C Q R (K + E) := ⟨_, rfl⟩
  have hX'l : X' = lyapSol M' W' := by rw [hX'def, hM'def, hW'def]; rfl
  have hX' : M'.transpose * X' + X' * M' + W' = 0 := by
    rw [hX'l]; exact (aux_lqrg_sol M' W' hinjM').1
  obtain ⟨D, hDdef⟩ : ∃ D, D = X' - X := ⟨_, rfl⟩
  have hX'D : X' = D + X := by rw [hDdef]; abel
  -- the equation for D
  have hDeq : M.transpose * D + D * M
      = (C.transpose * E.transpose * B.transpose * X + X * B * E * C)
        + (C.transpose * E.transpose * B.transpose * D + D * B * E * C)
        - (C.transpose * E.transpose * R * K * C + C.transpose * K.transpose * R * E * C
            + C.transpose * E.transpose * R * E * C) := by
    have key : M.transpose * D + D * M
        - ((C.transpose * E.transpose * B.transpose * X + X * B * E * C)
        + (C.transpose * E.transpose * B.transpose * D + D * B * E * C)
        - (C.transpose * E.transpose * R * K * C + C.transpose * K.transpose * R * E * C
            + C.transpose * E.transpose * R * E * C))
        = (M'.transpose * X' + X' * M' + W') - (M.transpose * X + X * M + W) := by
      rw [hX'D, hLM', hW'def, hWdef]
      simp only [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose,
        Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
      abel
    rw [hX', hX, sub_zero] at key
    exact sub_eq_zero.mp key
  -- bound on D
  have hTn : ‖C.transpose * E.transpose * R * K * C + C.transpose * K.transpose * R * E * C
      + C.transpose * E.transpose * R * E * C‖
      ≤ c * e * rr * k * c + c * k * rr * e * c + c * e * rr * e * c := by
    calc _ ≤ ‖C.transpose * E.transpose * R * K * C‖ + ‖C.transpose * K.transpose * R * E * C‖
          + ‖C.transpose * E.transpose * R * E * C‖ := norm_add₃_le
      _ ≤ ‖C.transpose‖ * ‖E.transpose‖ * ‖R‖ * ‖K‖ * ‖C‖
          + ‖C.transpose‖ * ‖K.transpose‖ * ‖R‖ * ‖E‖ * ‖C‖
          + ‖C.transpose‖ * ‖E.transpose‖ * ‖R‖ * ‖E‖ * ‖C‖ :=
          add_le_add_three (aux_lqrg_n5 _ _ _ _ _) (aux_lqrg_n5 _ _ _ _ _)
            (aux_lqrg_n5 _ _ _ _ _)
      _ = _ := by rw [hCt, hEt, hKt, ← hc, ← he, ← hrr, ← hk]
  have hDb : ‖D‖ ≤ γ * e := by
    have h1 := hcoer D
    rw [hDeq] at h1
    have h2 := norm_sub_le
      ((C.transpose * E.transpose * B.transpose * X + X * B * E * C)
        + (C.transpose * E.transpose * B.transpose * D + D * B * E * C))
      (C.transpose * E.transpose * R * K * C + C.transpose * K.transpose * R * E * C
            + C.transpose * E.transpose * R * E * C)
    have h3 := norm_add_le (C.transpose * E.transpose * B.transpose * X + X * B * E * C)
      (C.transpose * E.transpose * B.transpose * D + D * B * E * C)
    have h4 := hPE X
    have h5 := hPE D
    rw [← hx] at h4
    have h6 : ‖D‖ ≤ κ * (2 * b * c * e * x + 2 * b * c * e * ‖D‖ +
        ‖C.transpose * E.transpose * R * K * C + C.transpose * K.transpose * R * E * C
            + C.transpose * E.transpose * R * E * C‖) := by
      refine h1.trans (mul_le_mul_of_nonneg_left ?_ hκ)
      linarith
    rw [hγ]
    exact aux_lqrg_ar1 κ b c e x ‖D‖ rr k _ hκ hb0 hc0 he0 he1 hx0 (norm_nonneg _) hrr0 hk0 hs
      hTn h6
  -- the exact remainder identity
  have hcost : lqrCost A B C Q R Sig (K + E) - lqrCost A B C Q R Sig K
      = Matrix.trace (D * Sig) := by
    simp only [lqrCost]
    rw [← hXdef, ← hX'def, hDdef, Matrix.sub_mul, Matrix.trace_sub]
  have hSig : Sig = -(M * Y + Y * M.transpose) := eq_neg_of_add_eq_zero_right hY
  have h1 : Matrix.trace (D * Sig) = - Matrix.trace ((M.transpose * D + D * M) * Y) := by
    rw [hSig, Matrix.mul_neg, Matrix.trace_neg, Matrix.mul_add, Matrix.add_mul, Matrix.trace_add,
      Matrix.trace_add]
    have := Matrix.trace_mul_comm (D * Y) M.transpose
    simp only [Matrix.mul_assoc] at this ⊢
    linarith
  rw [hDeq] at h1
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.trace_add, Matrix.trace_sub,
    Matrix.mul_assoc] at h1
  have h4 : Matrix.trace (X * B * E * C * Y)
      = Matrix.trace (C.transpose * E.transpose * B.transpose * X * Y) := by
    rw [aux_lqrg_trT _ _ hYs]
    simp only [Matrix.transpose_mul, hXs, Matrix.mul_assoc]
  have h5 : Matrix.trace (C.transpose * K.transpose * R * E * C * Y)
      = Matrix.trace (C.transpose * E.transpose * R * K * C * Y) := by
    rw [aux_lqrg_trT _ _ hYs]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hRs, Matrix.mul_assoc]
  have h6 : frobInner (lqrGrad A B C Q R Sig K) E
      = 2 * Matrix.trace (C.transpose * E.transpose * R * K * C * Y)
        - 2 * Matrix.trace (C.transpose * E.transpose * B.transpose * X * Y) := by
    rw [aux_lqrg_fi]
    simp only [lqrGrad]
    rw [← hXdef, ← hYdef, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Matrix.sub_mul,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub]
    have a1 := Matrix.trace_mul_comm (E.transpose * R * K * C * Y) C.transpose
    have a2 := Matrix.trace_mul_comm (E.transpose * B.transpose * X * Y) C.transpose
    simp only [Matrix.mul_assoc] at a1 a2 ⊢
    rw [a1, a2]; ring
  simp only [Matrix.mul_assoc] at h4 h5 h6
  have hrem : lqrCost A B C Q R Sig (K + E) - lqrCost A B C Q R Sig K
      - frobInner (lqrGrad A B C Q R Sig K) E
      = Matrix.trace (C.transpose * E.transpose * R * E * C * Y)
        - Matrix.trace (C.transpose * E.transpose * B.transpose * D * Y)
        - Matrix.trace (D * B * E * C * Y) := by
    rw [hcost, h1, h6]
    simp only [Matrix.mul_assoc]
    linarith
  rw [hrem]
  -- estimates
  have t1 : |Matrix.trace (C.transpose * E.transpose * R * E * C * Y)|
      ≤ n * (c * e * rr * e * c * y) := by
    refine (aux_lqrg_trace _).trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
    have := aux_lqrg_n6 C.transpose E.transpose R E C Y
    rw [hCt, hEt, ← hrr, ← he, ← hc, ← hy] at this
    exact this
  have t2 : |Matrix.trace (C.transpose * E.transpose * B.transpose * D * Y)|
      ≤ n * (c * e * b * ‖D‖ * y) := by
    refine (aux_lqrg_trace _).trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
    have := aux_lqrg_n5 C.transpose E.transpose B.transpose D Y
    rw [hCt, hEt, hBt, ← hy] at this
    exact this
  have t3 : |Matrix.trace (D * B * E * C * Y)| ≤ n * (‖D‖ * b * e * c * y) := by
    refine (aux_lqrg_trace _).trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
    have := aux_lqrg_n5 D B E C Y
    rw [← hb, ← he, ← hc, ← hy] at this
    exact this
  have hsum : (n : ℝ) * (c * e * rr * e * c * y) + n * (c * e * b * ‖D‖ * y)
      + n * (‖D‖ * b * e * c * y) ≤ Λ * e * e := by
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have hq : 0 ≤ (n : ℝ) * y * b * c * e := by positivity
    have := mul_le_mul_of_nonneg_left hDb hq
    have eq1 : (n : ℝ) * (c * e * rr * e * c * y) + n * (c * e * b * ‖D‖ * y)
        + n * (‖D‖ * b * e * c * y)
        = (n : ℝ) * y * c * c * rr * e * e + 2 * ((n : ℝ) * y * b * c * e * ‖D‖) := by ring
    have eq2 : Λ * e * e = (n : ℝ) * y * c * c * rr * e * e
        + 2 * ((n : ℝ) * y * b * c * e * (γ * e)) := by rw [hΛ]; ring
    rw [eq1, eq2]
    linarith
  have hfin : Λ * e * e ≤ ε * e := by
    have : Λ * e ≤ ε := by
      rw [lt_div_iff₀ (by positivity)] at he3
      have : e * (Λ + 1) = Λ * e + e := by ring
      linarith only [he3, this, he0]
    exact mul_le_mul_of_nonneg_right this he0
  have habs := abs_sub (Matrix.trace (C.transpose * E.transpose * R * E * C * Y)
        - Matrix.trace (C.transpose * E.transpose * B.transpose * D * Y))
      (Matrix.trace (D * B * E * C * Y))
  have habs2 := abs_sub (Matrix.trace (C.transpose * E.transpose * R * E * C * Y))
      (Matrix.trace (C.transpose * E.transpose * B.transpose * D * Y))
  linarith only [habs, habs2, t1, t2, t3, hsum, hfin]

end aux_lqrg_norms

end FatkhullinPolyak.Discrete

open FatkhullinPolyak.Discrete

theorem solution {n m r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (Sig : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q.PosDef) (hR : R.PosDef) (hSig : Sig.PosDef) (hC : C.rank = r) (hB : B ≠ 0)
    (K : Matrix (Fin m) (Fin r) ℝ) (hK : K ∈ stabSet A B C) :
    ∀ ε > 0, ∃ δ > 0, ∀ E : Matrix (Fin m) (Fin r) ℝ, frobNorm E < δ →
      |lqrCost A B C Q R Sig (K + E) - lqrCost A B C Q R Sig K
          - frobInner (lqrGrad A B C Q R Sig K) E| ≤ ε * frobNorm E := by
  have hQs : Q.transpose = Q := by
    have := hQ.isHermitian
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hRs : R.transpose = R := by
    have := hR.isHermitian
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hSs : Sig.transpose = Sig := by
    have := hSig.isHermitian
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  exact aux_lqrg_main A B C Q R Sig hQs hRs hSs K hK
