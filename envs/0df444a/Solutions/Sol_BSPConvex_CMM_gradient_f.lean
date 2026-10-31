-- Prove2me | solution 1 for BSPConvex.CMM.gradient_f
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T14:58:25.315137+00:00
-- url     : https://prove2.me/submissions/8da20ab6-9110-4819-bd04-b40c05f8e82f

import Mathlib
import Definitions.Def_BSPConvex_CMM_Model

open Matrix
open scoped MatrixOrder

namespace BSPCMMAuxG
open BSPConvex.CMM

/-- `S(q)` is positive definite on the open simplex. -/
theorem S_posDef {m : ℕ} (x : Fin m → ℝ) (hx : x ∈ intSimplex m) : (Smat x).PosDef := by
  obtain ⟨hx0, hx1⟩ := hx
  have hH : (Smat x).IsHermitian := by
    ext i j
    simp only [Smat, conjTranspose_apply, Matrix.sub_apply, diagonal_apply, vecMulVec_apply,
      star_trivial]
    by_cases h : i = j
    · subst h; rfl
    · rw [if_neg h, if_neg (Ne.symm h)]
      ring
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hH ?_
  intro v hv
  set S := ∑ j, x j * v j with hS
  have e1 : ∀ i, (Smat x *ᵥ v) i = x i * v i - x i * S := by
    intro i
    rw [Smat, sub_mulVec, Pi.sub_apply, mulVec_diagonal]
    congr 1
    simp only [mulVec, dotProduct, vecMulVec_apply]
    rw [hS, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have e2 : ∀ i, v i * (x i * v i - x i * S) = x i * v i ^ 2 - (x i * v i) * S := by
    intro i; ring
  have key : star v ⬝ᵥ (Smat x *ᵥ v) = ∑ i, x i * v i ^ 2 - S ^ 2 := by
    rw [star_trivial]
    simp only [dotProduct, e1]
    rw [Finset.sum_congr rfl (fun i _ => e2 i), Finset.sum_sub_distrib, ← Finset.sum_mul, ← hS,
      sq]
  rw [key]
  have hcs : S ^ 2 ≤ (∑ i, x i) * ∑ i, x i * v i ^ 2 := by
    rw [hS]
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    · intro i _; exact (hx0 i).le
    · intro i _; exact mul_nonneg (hx0 i).le (sq_nonneg _)
    · intro i _; apply le_of_eq; ring
  have hq : 0 < ∑ i, x i * v i ^ 2 := by
    obtain ⟨k, hk⟩ : ∃ k, v k ≠ 0 := by
      by_contra h
      push Not at h
      exact hv (funext h)
    calc (0 : ℝ) < x k * v k ^ 2 := mul_pos (hx0 k) (by positivity)
      _ ≤ ∑ i, x i * v i ^ 2 :=
        Finset.single_le_sum (f := fun i => x i * v i ^ 2)
          (fun i _ => mul_nonneg (hx0 i).le (sq_nonneg _)) (Finset.mem_univ k)
  have : (∑ i, x i) * ∑ i, x i * v i ^ 2 < ∑ i, x i * v i ^ 2 := by
    calc (∑ i, x i) * ∑ i, x i * v i ^ 2 < 1 * ∑ i, x i * v i ^ 2 :=
          mul_lt_mul_of_pos_right hx1 hq
      _ = ∑ i, x i * v i ^ 2 := one_mul _
  linarith

theorem sqrtSig_psd {m : ℕ} (Sig : Matrix (Fin m) (Fin m) ℝ) :
    (CFC.sqrt Sig).PosSemidef := Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg Sig)

theorem sqrtSig_unit {m : ℕ} (Sig : Matrix (Fin m) (Fin m) ℝ) (hSig : Sig.PosDef) :
    IsUnit (CFC.sqrt Sig) :=
  (CFC.isUnit_sqrt_iff Sig hSig.posSemidef.nonneg).2 hSig.isUnit

theorem T_posDef {m : ℕ} (Sig : Matrix (Fin m) (Fin m) ℝ) (hSig : Sig.PosDef)
    (q : Fin m → ℝ) (hq : q ∈ intSimplex m) : (Tmat Sig q).PosDef := by
  have hs := sqrtSig_psd Sig
  have hH : (CFC.sqrt Sig)ᴴ = CFC.sqrt Sig := hs.isHermitian.eq
  have hpsd := (S_posDef q hq).posSemidef.conjTranspose_mul_mul_same (CFC.sqrt Sig)
  rw [hH] at hpsd
  change (CFC.sqrt Sig * Smat q * CFC.sqrt Sig).PosDef
  rw [hpsd.posDef_iff_isUnit]
  exact ((sqrtSig_unit Sig hSig).mul (S_posDef q hq).isUnit).mul (sqrtSig_unit Sig hSig)

theorem sqrtT_posDef {m : ℕ} (Sig : Matrix (Fin m) (Fin m) ℝ) (hSig : Sig.PosDef)
    (q : Fin m → ℝ) (hq : q ∈ intSimplex m) : (CFC.sqrt (Tmat Sig q)).PosDef := by
  have hT := T_posDef Sig hSig q hq
  have hpsd : (CFC.sqrt (Tmat Sig q)).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg _)
  rw [hpsd.posDef_iff_isUnit]
  exact (CFC.isUnit_sqrt_iff _ hT.posSemidef.nonneg).2 hT.isUnit

/-- `tr(S(q) M) = qᵀ diag M − qᵀ M q` for any matrix `M`. -/
theorem trace_S_mul {m : ℕ} (q : Fin m → ℝ) (M : Matrix (Fin m) (Fin m) ℝ) :
    Matrix.trace (Smat q * M) = q ⬝ᵥ Matrix.diag M - q ⬝ᵥ (M *ᵥ q) := by
  rw [Matrix.trace_mul_comm, Smat, Matrix.mul_sub, Matrix.trace_sub]
  congr 1
  · simp [Matrix.trace, Matrix.mul_diagonal, dotProduct, mul_comm]
  · simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, vecMulVec_apply, dotProduct,
      mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    ring

theorem trace_SM {m : ℕ} (Sig : Matrix (Fin m) (Fin m) ℝ) (hSig : Sig.PosDef)
    (q : Fin m → ℝ) (hq : q ∈ intSimplex m) :
    Matrix.trace (Smat q * Mmat Sig q) = Matrix.trace (CFC.sqrt (Tmat Sig q)) := by
  set s := CFC.sqrt Sig
  set r := CFC.sqrt (Tmat Sig q)
  have hr : IsUnit r.det := (Matrix.isUnit_iff_isUnit_det r).1 (sqrtT_posDef Sig hSig q hq).isUnit
  have hrr : r * r = Tmat Sig q := CFC.sqrt_mul_sqrt_self _ (T_posDef Sig hSig q hq).posSemidef.nonneg
  have h1 : Smat q * Mmat Sig q = (Smat q * s * r⁻¹) * s := by
    simp only [Mmat, s, r, Matrix.mul_assoc]
  rw [h1, Matrix.trace_mul_comm]
  have h2 : s * (Smat q * s * r⁻¹) = r * (r * r⁻¹) := by
    rw [← Matrix.mul_assoc r r, hrr]
    simp only [Tmat, s, Matrix.mul_assoc]
  rw [h2, Matrix.mul_nonsing_inv _ hr, Matrix.mul_one]


/-- Entrywise `ℓ¹` size of a matrix. -/
noncomputable def N1 {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) : ℝ := ∑ a, ∑ b, |A a b|

theorem N1_nonneg {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) : 0 ≤ N1 A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem entry_le_N1 {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (a b : Fin m) : |A a b| ≤ N1 A := by
  unfold N1
  calc |A a b| ≤ ∑ b', |A a b'| :=
        Finset.single_le_sum (f := fun b' => |A a b'|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ b)
    _ ≤ ∑ a', ∑ b', |A a' b'| :=
        Finset.single_le_sum (f := fun a' => ∑ b', |A a' b'|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ a)

theorem quad_le {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (v : Fin m → ℝ) (c : ℝ)
    (hv : ∀ a, |v a| ≤ c) : |v ⬝ᵥ (A *ᵥ v)| ≤ N1 A * c ^ 2 := by
  have e : v ⬝ᵥ (A *ᵥ v) = ∑ a, ∑ b, v a * A a b * v b := by
    simp only [dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  rw [e, N1, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  rw [abs_mul, abs_mul]
  have h1 := hv a
  have h2 := hv b
  have h3 := abs_nonneg (A a b)
  have h4 := abs_nonneg (v a)
  have h5 := abs_nonneg (v b)
  calc |v a| * |A a b| * |v b| ≤ c * |A a b| * c := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right h1 h3) h2 h5
        exact mul_nonneg (h4.trans h1) h3
    _ = |A a b| * c ^ 2 := by ring

theorem N1_conj {m : ℕ} (s D : Matrix (Fin m) (Fin m) ℝ) :
    N1 (s * D * s) ≤ (m : ℝ) ^ 2 * N1 s ^ 2 * N1 D := by
  have hent : ∀ a b, |(s * D * s) a b| ≤ N1 s ^ 2 * N1 D := by
    intro a b
    have e : (s * D * s) a b = ∑ d, ∑ c, s a c * D c d * s d b := by
      simp only [Matrix.mul_apply, Finset.sum_mul]
    rw [e]
    calc |∑ d, ∑ c, s a c * D c d * s d b|
        ≤ ∑ d, |∑ c, s a c * D c d * s d b| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d, ∑ c, |s a c * D c d * s d b| :=
          Finset.sum_le_sum fun d _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d, ∑ c, N1 s ^ 2 * |D c d| := by
          refine Finset.sum_le_sum fun d _ => Finset.sum_le_sum fun c _ => ?_
          rw [abs_mul, abs_mul]
          have h1 := entry_le_N1 s a c
          have h2 := entry_le_N1 s d b
          calc |s a c| * |D c d| * |s d b| ≤ N1 s * |D c d| * N1 s := by
                apply mul_le_mul (mul_le_mul_of_nonneg_right h1 (abs_nonneg _)) h2
                  (abs_nonneg _)
                exact mul_nonneg (N1_nonneg s) (abs_nonneg _)
            _ = N1 s ^ 2 * |D c d| := by ring
      _ = N1 s ^ 2 * N1 D := by
          rw [Finset.sum_comm]; simp only [N1, Finset.mul_sum]
  calc N1 (s * D * s) = ∑ a, ∑ b, |(s * D * s) a b| := rfl
    _ ≤ ∑ a : Fin m, ∑ b : Fin m, N1 s ^ 2 * N1 D :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hent a b
    _ = (m : ℝ) ^ 2 * N1 s ^ 2 * N1 D := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring

/-- For positive definite `R` and a unit vector `v`, `1 ≤ (vᵀRv)(vᵀR⁻¹v)`. -/
theorem cs_lower {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} (hR : R.PosDef) (v : Fin m → ℝ)
    (hv : v ⬝ᵥ v = 1) : 1 ≤ (v ⬝ᵥ (R *ᵥ v)) * (v ⬝ᵥ (R⁻¹ *ᵥ v)) ∧ 0 < v ⬝ᵥ (R⁻¹ *ᵥ v) := by
  have hRt : Rᵀ = R := by
    have := hR.isHermitian.eq; rwa [conjTranspose_eq_transpose_of_trivial] at this
  have hd : IsUnit R.det := (Matrix.isUnit_iff_isUnit_det R).1 hR.isUnit
  have hRR : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have hv0 : v ≠ 0 := by
    rintro rfl; simp at hv
  have hc : 0 < v ⬝ᵥ (R⁻¹ *ᵥ v) := by
    have := hR.inv.dotProduct_mulVec_pos hv0
    simpa using this
  refine ⟨?_, hc⟩
  set c := v ⬝ᵥ (R⁻¹ *ᵥ v)
  set y := R⁻¹ *ᵥ v
  have hy : R *ᵥ y = v := by simp only [y]; rw [mulVec_mulVec, hRR, one_mulVec]
  have h0 := hR.posSemidef.dotProduct_mulVec_nonneg (c • v - y)
  have e1 : y ⬝ᵥ v = c := dotProduct_comm _ _
  have e2 : y ⬝ᵥ (R *ᵥ v) = 1 := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hRt, dotProduct_comm, hy, hv]
  simp only [star_trivial, mulVec_sub, mulVec_smul, hy, dotProduct_sub, sub_dotProduct,
    dotProduct_smul, smul_dotProduct, smul_eq_mul, hv, e1, e2] at h0
  have : c * (c * (v ⬝ᵥ (R *ᵥ v)) - 1) ≥ 0 := by nlinarith
  have := (mul_nonneg_iff_of_pos_left hc).1 this
  nlinarith

theorem eig_unit {m : ℕ} {Δ : Matrix (Fin m) (Fin m) ℝ} (hΔ : Δ.IsHermitian) (j : Fin m) :
    (⇑(hΔ.eigenvectorBasis j) : Fin m → ℝ) ⬝ᵥ ⇑(hΔ.eigenvectorBasis j) = 1 := by
  have h := congrFun (congrFun (Unitary.coe_star_mul_self hΔ.eigenvectorUnitary) j) j
  simpa [Matrix.mul_apply, Matrix.star_apply, dotProduct] using h

theorem eig_trace {m : ℕ} {Δ : Matrix (Fin m) (Fin m) ℝ} (hΔ : Δ.IsHermitian)
    (B : Matrix (Fin m) (Fin m) ℝ) :
    Matrix.trace B = ∑ j, (⇑(hΔ.eigenvectorBasis j) : Fin m → ℝ) ⬝ᵥ
      (B *ᵥ ⇑(hΔ.eigenvectorBasis j)) := by
  set U : Matrix (Fin m) (Fin m) ℝ := (hΔ.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ)
  have hU : U * star U = 1 := Unitary.coe_mul_star_self hΔ.eigenvectorUnitary
  have : Matrix.trace B = Matrix.trace (star U * (B * U)) := by
    rw [← Matrix.trace_mul_comm, Matrix.mul_assoc, hU, Matrix.mul_one]
  rw [this]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.star_apply, star_trivial,
    dotProduct, mulVec, U, Matrix.IsHermitian.eigenvectorUnitary_apply]

theorem unit_coord {m : ℕ} (v : Fin m → ℝ) (hv : v ⬝ᵥ v = 1) (a : Fin m) : |v a| ≤ 1 := by
  have h : v a * v a ≤ v ⬝ᵥ v := by
    unfold dotProduct
    exact Finset.single_le_sum (f := fun i => v i * v i) (fun i _ => mul_self_nonneg _)
      (Finset.mem_univ a)
  rw [hv] at h
  rw [abs_le]; constructor <;> nlinarith

/-- The key second-order estimate for `√·` at a positive definite point. -/
theorem remainder_bound {m : ℕ} {R R' : Matrix (Fin m) (Fin m) ℝ} (hR : R.PosDef)
    (hR' : R'.PosSemidef) :
    |Matrix.trace (R⁻¹ * (R' - R) * (R' - R))| ≤
      (m : ℝ) * ((N1 (R' * R' - R * R) * N1 R⁻¹) ^ 2 * N1 R⁻¹) := by
  set Δ := R' - R with hΔdef
  set K := R' * R' - R * R
  set Ri := R⁻¹
  have hΔ : Δ.IsHermitian := hR'.1.sub hR.1
  have hΔt : Δᵀ = Δ := by
    have := hΔ.eq; rwa [conjTranspose_eq_transpose_of_trivial] at this
  have hRi : Ri.PosDef := hR.inv
  have hRit : Riᵀ = Ri := by
    have := hRi.isHermitian.eq; rwa [conjTranspose_eq_transpose_of_trivial] at this
  have hK : K = Δ * R' + R * Δ := by simp only [K, Δ]; noncomm_ring
  rw [Matrix.trace_mul_comm, eig_trace hΔ]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hcard : (m : ℝ) * ((N1 K * N1 Ri) ^ 2 * N1 Ri) =
      ∑ _j : Fin m, (N1 K * N1 Ri) ^ 2 * N1 Ri := by simp
  rw [hcard]
  refine Finset.sum_le_sum fun j _ => ?_
  set v : Fin m → ℝ := ⇑(hΔ.eigenvectorBasis j)
  set μ := hΔ.eigenvalues j
  have hv : Δ *ᵥ v = μ • v := hΔ.mulVec_eigenvectorBasis j
  have hvv : v ⬝ᵥ v = 1 := eig_unit hΔ j
  have hcoord := unit_coord v hvv
  have hterm : v ⬝ᵥ ((Δ * (Ri * Δ)) *ᵥ v) = μ ^ 2 * (v ⬝ᵥ (Ri *ᵥ v)) := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, hv, dotProduct_mulVec, ← mulVec_transpose, hΔt, hv,
      mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    ring
  have hKv : v ⬝ᵥ (K *ᵥ v) = μ * (v ⬝ᵥ (R' *ᵥ v) + v ⬝ᵥ (R *ᵥ v)) := by
    rw [hK, add_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hv, dotProduct_add,
      dotProduct_mulVec v Δ, ← mulVec_transpose, hΔt, hv, mulVec_smul, dotProduct_smul,
      smul_dotProduct, smul_eq_mul, smul_eq_mul]
    ring
  obtain ⟨hcs, hc⟩ := cs_lower hR v hvv
  have ha' : 0 ≤ v ⬝ᵥ (R' *ᵥ v) := by simpa using hR'.dotProduct_mulVec_nonneg v
  have ha : 0 ≤ v ⬝ᵥ (R *ᵥ v) := by simpa using hR.posSemidef.dotProduct_mulVec_nonneg v
  set c := v ⬝ᵥ (Ri *ᵥ v)
  have hcN : c ≤ N1 Ri := by
    have := quad_le Ri v 1 hcoord
    rw [one_pow, mul_one] at this
    exact (le_abs_self _).trans this
  have hKN : |v ⬝ᵥ (K *ᵥ v)| ≤ N1 K := by
    have := quad_le K v 1 hcoord
    rwa [one_pow, mul_one] at this
  have hμ : |μ| ≤ N1 K * N1 Ri := by
    have h1 : |μ| * (v ⬝ᵥ (R *ᵥ v)) ≤ |v ⬝ᵥ (K *ᵥ v)| := by
      rw [hKv, abs_mul, abs_of_nonneg (add_nonneg ha' ha)]
      exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    have h2 : |μ| ≤ |μ| * (v ⬝ᵥ (R *ᵥ v)) * c := by
      rw [mul_assoc]; exact le_mul_of_one_le_right (abs_nonneg _) hcs
    calc |μ| ≤ |μ| * (v ⬝ᵥ (R *ᵥ v)) * c := h2
      _ ≤ |v ⬝ᵥ (K *ᵥ v)| * c := mul_le_mul_of_nonneg_right h1 hc.le
      _ ≤ N1 K * N1 Ri := mul_le_mul hKN hcN hc.le (N1_nonneg K)
  rw [hterm, abs_mul, abs_of_pos hc, abs_pow]
  have hμ2 : |μ| ^ 2 ≤ (N1 K * N1 Ri) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hμ 2
  exact mul_le_mul hμ2 hcN hc.le (sq_nonneg _)

theorem intSimplex_open (m : ℕ) : IsOpen (intSimplex m) := by
  have : intSimplex m = (⋂ i, {x : Fin m → ℝ | 0 < x i}) ∩ {x | ∑ i, x i < 1} := by
    ext x; simp [intSimplex]
  rw [this]
  refine IsOpen.inter (isOpen_iInter_of_finite fun i => ?_) ?_
  · exact isOpen_lt continuous_const (continuous_apply i)
  · exact isOpen_lt (continuous_finset_sum _ fun i _ => continuous_apply i) continuous_const

theorem M_symm {m : ℕ} (Sig : Matrix (Fin m) (Fin m) ℝ) (hSig : Sig.PosDef) (q : Fin m → ℝ)
    (hq : q ∈ intSimplex m) : (Mmat Sig q)ᵀ = Mmat Sig q := by
  have hst : (CFC.sqrt Sig)ᵀ = CFC.sqrt Sig := by
    have := (sqrtSig_psd Sig).isHermitian.eq
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  have hRit : ((CFC.sqrt (Tmat Sig q))⁻¹)ᵀ = (CFC.sqrt (Tmat Sig q))⁻¹ := by
    have := (sqrtT_posDef Sig hSig q hq).inv.isHermitian.eq
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  simp only [Mmat, Matrix.transpose_mul, hst, hRit, Matrix.mul_assoc]

/-- Exact second-order expansion of `f` around an interior point. -/
theorem expansion {m : ℕ} (Sig : Matrix (Fin m) (Fin m) ℝ) (hSig : Sig.PosDef)
    (q : Fin m → ℝ) (hq : q ∈ intSimplex m) (h : Fin m → ℝ) (hx : q + h ∈ intSimplex m) :
    fCMM Sig (q + h) - fCMM Sig q - h ⬝ᵥ gradF Sig q =
      -(1 / 2 : ℝ) * Matrix.trace ((CFC.sqrt (Tmat Sig q))⁻¹ *
          (CFC.sqrt (Tmat Sig (q + h)) - CFC.sqrt (Tmat Sig q)) *
          (CFC.sqrt (Tmat Sig (q + h)) - CFC.sqrt (Tmat Sig q))) -
        (1 / 2 : ℝ) * (h ⬝ᵥ (Mmat Sig q *ᵥ h)) := by
  set s := CFC.sqrt Sig
  set R := CFC.sqrt (Tmat Sig q)
  set R' := CFC.sqrt (Tmat Sig (q + h))
  set Ri := R⁻¹
  set M := Mmat Sig q
  set Δ := R' - R
  have hRd : IsUnit R.det := (Matrix.isUnit_iff_isUnit_det R).1 (sqrtT_posDef Sig hSig q hq).isUnit
  have hRiR : Ri * R = 1 := Matrix.nonsing_inv_mul _ hRd
  have hRR : R * R = Tmat Sig q :=
    CFC.sqrt_mul_sqrt_self _ (T_posDef Sig hSig q hq).posSemidef.nonneg
  have hRR' : R' * R' = Tmat Sig (q + h) :=
    CFC.sqrt_mul_sqrt_self _ (T_posDef Sig hSig (q + h) hx).posSemidef.nonneg
  set D := Smat (q + h) - Smat q
  have hK : Tmat Sig (q + h) - Tmat Sig q = s * D * s := by
    simp only [Tmat, D, s, Matrix.mul_sub, Matrix.sub_mul]
  have hK2 : Tmat Sig (q + h) - Tmat Sig q = R * Δ + Δ * R + Δ * Δ := by
    rw [← hRR, ← hRR']; simp only [Δ]; noncomm_ring
  -- trace of `Ri K`
  have htr1 : Matrix.trace (Ri * (Tmat Sig (q + h) - Tmat Sig q)) =
      2 * Matrix.trace Δ + Matrix.trace (Ri * Δ * Δ) := by
    rw [hK2, Matrix.mul_add, Matrix.mul_add, Matrix.trace_add, Matrix.trace_add,
      ← Matrix.mul_assoc, hRiR, Matrix.one_mul, ← Matrix.mul_assoc]
    have hRRi : R * Ri = 1 := Matrix.mul_nonsing_inv _ hRd
    have : Matrix.trace (Ri * Δ * R) = Matrix.trace Δ := by
      rw [Matrix.trace_mul_comm (Ri * Δ) R, ← Matrix.mul_assoc, hRRi, Matrix.one_mul]
    rw [this, Matrix.mul_assoc Ri Δ Δ]; ring
  have htr2 : Matrix.trace (Ri * (Tmat Sig (q + h) - Tmat Sig q)) = Matrix.trace (D * M) := by
    rw [hK]
    have e : Ri * (s * D * s) = (Ri * s * D) * s := by simp only [Matrix.mul_assoc]
    rw [e, Matrix.trace_mul_comm]
    have e2 : s * (Ri * s * D) = M * D := by simp only [M, Mmat, s, Ri, R, Matrix.mul_assoc]
    rw [e2, Matrix.trace_mul_comm]
  have htr3 : Matrix.trace (D * M) =
      (q + h) ⬝ᵥ Matrix.diag M - (q + h) ⬝ᵥ (M *ᵥ (q + h)) -
        (q ⬝ᵥ Matrix.diag M - q ⬝ᵥ (M *ᵥ q)) := by
    rw [Matrix.sub_mul, Matrix.trace_sub, trace_S_mul, trace_S_mul]
  have hMt : Mᵀ = M := M_symm Sig hSig q hq
  have hsym : q ⬝ᵥ (M *ᵥ h) = h ⬝ᵥ (M *ᵥ q) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hMt, dotProduct_comm]
  have hfx : fCMM Sig (q + h) - fCMM Sig q = Matrix.trace Δ := by
    simp only [fCMM, Δ, Matrix.trace_sub, R, R']
  have hgrad : h ⬝ᵥ gradF Sig q = (1 / 2 : ℝ) * (h ⬝ᵥ Matrix.diag M) - h ⬝ᵥ (M *ᵥ q) := by
    simp only [gradF, M, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  rw [hfx, hgrad]
  have hexp : (q + h) ⬝ᵥ (M *ᵥ (q + h)) =
      q ⬝ᵥ (M *ᵥ q) + 2 * (h ⬝ᵥ (M *ᵥ q)) + h ⬝ᵥ (M *ᵥ h) := by
    rw [mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, hsym]; ring
  have hd : (q + h) ⬝ᵥ Matrix.diag M = q ⬝ᵥ Matrix.diag M + h ⬝ᵥ Matrix.diag M :=
    add_dotProduct _ _ _
  rw [htr2, htr3, hexp, hd] at htr1
  linarith

theorem D_entry {m : ℕ} (q h : Fin m → ℝ) (hq : q ∈ intSimplex m) (hh : ‖h‖ ≤ 1) (a b : Fin m) :
    |(Smat (q + h) - Smat q) a b| ≤ 4 * ‖h‖ := by
  have hqa : ∀ i, |q i| ≤ 1 := by
    intro i
    have h1 : q i ≤ ∑ j, q j :=
      Finset.single_le_sum (f := q) (fun j _ => (hq.1 j).le) (Finset.mem_univ i)
    rw [abs_of_pos (hq.1 i)]; linarith [hq.2]
  have hha : ∀ i, |h i| ≤ ‖h‖ := fun i => by
    have := norm_le_pi_norm h i; rwa [Real.norm_eq_abs] at this
  have e : (Smat (q + h) - Smat q) a b =
      (if a = b then h a else 0) - (q a * h b + h a * q b + h a * h b) := by
    simp only [Smat, Matrix.sub_apply, diagonal_apply, vecMulVec_apply, Pi.add_apply]
    split_ifs <;> ring
  rw [e]
  have hn : 0 ≤ ‖h‖ := norm_nonneg h
  have t1 : |(if a = b then h a else 0)| ≤ ‖h‖ := by
    split_ifs
    · exact hha a
    · simpa using hn
  have t2 : |q a * h b| ≤ ‖h‖ := by
    rw [abs_mul]; nlinarith [hqa a, hha b, abs_nonneg (q a), abs_nonneg (h b)]
  have t3 : |h a * q b| ≤ ‖h‖ := by
    rw [abs_mul]; nlinarith [hqa b, hha a, abs_nonneg (q b), abs_nonneg (h a)]
  have t4 : |h a * h b| ≤ ‖h‖ := by
    rw [abs_mul]; nlinarith [hha b, hha a, abs_nonneg (h b), abs_nonneg (h a)]
  calc |(if a = b then h a else 0) - (q a * h b + h a * q b + h a * h b)|
      ≤ |(if a = b then h a else 0)| + (|q a * h b| + |h a * q b| + |h a * h b|) := by
        refine (abs_sub _ _).trans (add_le_add le_rfl ?_)
        exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 4 * ‖h‖ := by linarith

theorem N1_D {m : ℕ} (q h : Fin m → ℝ) (hq : q ∈ intSimplex m) (hh : ‖h‖ ≤ 1) :
    N1 (Smat (q + h) - Smat q) ≤ (m : ℝ) ^ 2 * (4 * ‖h‖) := by
  calc N1 (Smat (q + h) - Smat q) ≤ ∑ a : Fin m, ∑ b : Fin m, 4 * ‖h‖ :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => D_entry q h hq hh a b
    _ = (m : ℝ) ^ 2 * (4 * ‖h‖) := by simp; ring

end BSPCMMAuxG

open BSPConvex.CMM in
theorem solution {m : ℕ} (Sig : Matrix (Fin m) (Fin m) ℝ) (hSig : Sig.PosDef)
    (q : Fin m → ℝ) (hq : q ∈ intSimplex m) :
    HasFDerivAt (fCMM Sig)
      (∑ i, gradF Sig q i • (ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ)) q := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (BSPCMMAuxG.intSimplex_open m) q hq
  set s := CFC.sqrt Sig
  set R := CFC.sqrt (Tmat Sig q)
  set C : ℝ := (1 / 2 : ℝ) * ((m : ℝ) * (((m : ℝ) ^ 2 * BSPCMMAuxG.N1 s ^ 2 *
      ((m : ℝ) ^ 2 * 4) * BSPCMMAuxG.N1 R⁻¹) ^ 2 * BSPCMMAuxG.N1 R⁻¹)) +
      (1 / 2 : ℝ) * BSPCMMAuxG.N1 (Mmat Sig q)
  have hL : ∀ h : Fin m → ℝ,
      (∑ i, gradF Sig q i • (ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ)) h =
        h ⬝ᵥ gradF Sig q := by
    intro h
    simp [ContinuousLinearMap.sum_apply, dotProduct, mul_comm]
  have hbig : (fun h => fCMM Sig (q + h) - fCMM Sig q -
      (∑ i, gradF Sig q i • (ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ)) h) =O[nhds 0]
      (fun h : Fin m → ℝ => ‖h‖ ^ 2) := by
    refine Asymptotics.IsBigO.of_bound C ?_
    have hmem : Metric.ball (0 : Fin m → ℝ) (min ε 1) ∈ nhds (0 : Fin m → ℝ) :=
      Metric.ball_mem_nhds _ (lt_min hε one_pos)
    filter_upwards [hmem] with h hh
    rw [Metric.mem_ball, dist_zero_right] at hh
    have hhε : ‖h‖ < ε := lt_of_lt_of_le hh (min_le_left _ _)
    have hh1 : ‖h‖ ≤ 1 := (lt_of_lt_of_le hh (min_le_right _ _)).le
    have hx : q + h ∈ intSimplex m := by
      apply hball
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]; exact hhε
    rw [hL, BSPCMMAuxG.expansion Sig hSig q hq h hx]
    have hR := BSPCMMAuxG.sqrtT_posDef Sig hSig q hq
    have hR' := (BSPCMMAuxG.sqrtT_posDef Sig hSig (q + h) hx).posSemidef
    have hrem := BSPCMMAuxG.remainder_bound hR hR'
    have hKeq : CFC.sqrt (Tmat Sig (q + h)) * CFC.sqrt (Tmat Sig (q + h)) -
        CFC.sqrt (Tmat Sig q) * CFC.sqrt (Tmat Sig q) =
        s * (Smat (q + h) - Smat q) * s := by
      rw [CFC.sqrt_mul_sqrt_self _ (BSPCMMAuxG.T_posDef Sig hSig (q + h) hx).posSemidef.nonneg,
        CFC.sqrt_mul_sqrt_self _ (BSPCMMAuxG.T_posDef Sig hSig q hq).posSemidef.nonneg]
      simp only [Tmat, s, Matrix.mul_sub, Matrix.sub_mul]
    rw [hKeq] at hrem
    have hND := BSPCMMAuxG.N1_D q h hq hh1
    have hNK := BSPCMMAuxG.N1_conj s (Smat (q + h) - Smat q)
    have hNs := BSPCMMAuxG.N1_nonneg s
    have hNRi := BSPCMMAuxG.N1_nonneg R⁻¹
    have hNK' : BSPCMMAuxG.N1 (s * (Smat (q + h) - Smat q) * s) ≤
        (m : ℝ) ^ 2 * BSPCMMAuxG.N1 s ^ 2 * ((m : ℝ) ^ 2 * 4) * ‖h‖ := by
      calc _ ≤ (m : ℝ) ^ 2 * BSPCMMAuxG.N1 s ^ 2 * BSPCMMAuxG.N1 (Smat (q + h) - Smat q) := hNK
        _ ≤ (m : ℝ) ^ 2 * BSPCMMAuxG.N1 s ^ 2 * ((m : ℝ) ^ 2 * (4 * ‖h‖)) :=
            mul_le_mul_of_nonneg_left hND (by positivity)
        _ = _ := by ring
    have hNK0 := BSPCMMAuxG.N1_nonneg (s * (Smat (q + h) - Smat q) * s)
    set A := (m : ℝ) ^ 2 * BSPCMMAuxG.N1 s ^ 2 * ((m : ℝ) ^ 2 * 4)
    have hA : 0 ≤ A := by positivity
    have hsq : (BSPCMMAuxG.N1 (s * (Smat (q + h) - Smat q) * s) * BSPCMMAuxG.N1 R⁻¹) ^ 2 ≤
        (A * BSPCMMAuxG.N1 R⁻¹) ^ 2 * ‖h‖ ^ 2 := by
      rw [← mul_pow]
      apply pow_le_pow_left₀ (mul_nonneg hNK0 hNRi)
      calc BSPCMMAuxG.N1 (s * (Smat (q + h) - Smat q) * s) * BSPCMMAuxG.N1 R⁻¹
          ≤ A * ‖h‖ * BSPCMMAuxG.N1 R⁻¹ := mul_le_mul_of_nonneg_right hNK' hNRi
        _ = _ := by ring
    have hrem2 : |Matrix.trace (R⁻¹ * (CFC.sqrt (Tmat Sig (q + h)) - R) *
        (CFC.sqrt (Tmat Sig (q + h)) - R))| ≤
        (m : ℝ) * ((A * BSPCMMAuxG.N1 R⁻¹) ^ 2 * BSPCMMAuxG.N1 R⁻¹) * ‖h‖ ^ 2 := by
      refine hrem.trans ?_
      have := mul_le_mul_of_nonneg_right hsq hNRi
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      nlinarith [mul_le_mul_of_nonneg_left this hm]
    have hquad : |h ⬝ᵥ (Mmat Sig q *ᵥ h)| ≤ BSPCMMAuxG.N1 (Mmat Sig q) * ‖h‖ ^ 2 :=
      BSPCMMAuxG.quad_le _ h ‖h‖ fun i => by
        have := norm_le_pi_norm h i; rwa [Real.norm_eq_abs] at this
    rw [Real.norm_eq_abs, norm_pow, norm_norm]
    calc |-(1 / 2 : ℝ) * Matrix.trace (R⁻¹ * (CFC.sqrt (Tmat Sig (q + h)) - R) *
          (CFC.sqrt (Tmat Sig (q + h)) - R)) - (1 / 2 : ℝ) * (h ⬝ᵥ (Mmat Sig q *ᵥ h))|
        ≤ (1 / 2 : ℝ) * |Matrix.trace (R⁻¹ * (CFC.sqrt (Tmat Sig (q + h)) - R) *
          (CFC.sqrt (Tmat Sig (q + h)) - R))| + (1 / 2 : ℝ) * |h ⬝ᵥ (Mmat Sig q *ᵥ h)| := by
          refine (abs_sub _ _).trans (le_of_eq ?_)
          rw [abs_mul, abs_mul]; norm_num
      _ ≤ C * ‖h‖ ^ 2 := by
          simp only [C]
          nlinarith [hrem2, hquad]
  exact hbig.trans_isLittleO (Asymptotics.isLittleO_norm_pow_id one_lt_two)
