-- Prove2me | solution 1 for GaoQuantumUnion.disturbance
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-23T06:17:41.470725+00:00
-- url     : https://prove2.me/submissions/78058e18-aa90-462f-8804-48e144a81fa7

import Definitions.Def_GaoQuantumUnion_Model
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Tactic.NoncommRing
open Matrix WildeQIT GaoQuantumUnion
open scoped MatrixOrder ComplexOrder ComplexConjugate
set_option autoImplicit false

namespace GaoDist

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem conj_diag_mul (U : Matrix ι ι ℂ) (hU : star U * U = 1) (f g : ι → ℂ) :
    U * diagonal f * star U * (U * diagonal g * star U) =
      U * diagonal (fun i => f i * g i) * star U := by
  calc U * diagonal f * star U * (U * diagonal g * star U)
      = U * diagonal f * (star U * U) * diagonal g * star U := by simp only [mul_assoc]
    _ = _ := by rw [hU, mul_one, mul_assoc U, diagonal_mul_diagonal]

/-- Trace norm of a Hermitian matrix: `√(XᴴX) = S X` with `S` unitary. -/
theorem herm_sign (X : Matrix ι ι ℂ) (hX : X.IsHermitian) :
    ∃ S : Matrix ι ι ℂ, Sᴴ * S = 1 ∧ CFC.sqrt (Xᴴ * X) = S * X := by
  set U : Matrix ι ι ℂ := (hX.eigenvectorUnitary : Matrix ι ι ℂ)
  have hU1 : star U * U = 1 := Unitary.coe_star_mul_self _
  have hU2 : U * star U = 1 := Unitary.coe_mul_star_self _
  set l := hX.eigenvalues
  have hspec : X = U * diagonal (fun i => (l i : ℂ)) * star U := by
    have := hX.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  set s : ι → ℂ := fun i => if 0 ≤ l i then 1 else -1
  set a : ι → ℂ := fun i => ((|l i| : ℝ) : ℂ)
  refine ⟨U * diagonal s * star U, ?_, ?_⟩
  · have hSh : (U * diagonal s * star U)ᴴ = U * diagonal s * star U := by
      rw [conjTranspose_mul, conjTranspose_mul, ← star_eq_conjTranspose (star U), star_star,
        diagonal_conjTranspose, ← star_eq_conjTranspose U, mul_assoc]
      have : star s = s := by
        funext i; simp only [Pi.star_apply, s]; split_ifs <;> simp
      rw [this]
    rw [hSh, conj_diag_mul U hU1]
    have : (fun i => s i * s i) = fun _ => (1 : ℂ) := by
      ext i; simp only [s]; split_ifs <;> simp
    rw [this, diagonal_one, Matrix.mul_one, hU2]
  · have hSX : U * diagonal s * star U * X = U * diagonal a * star U := by
      conv_lhs => rw [hspec]
      rw [conj_diag_mul U hU1]
      have : (fun i => s i * (l i : ℂ)) = a := by
        funext i
        simp only [s, a]
        split_ifs with h
        · rw [abs_of_nonneg h]; simp
        · rw [abs_of_neg (lt_of_not_ge h)]; push_cast; ring
      rw [this]
    rw [hSX]
    refine CFC.sqrt_unique ?_ ?_
    · rw [conj_diag_mul U hU1, hX.eq, hspec, conj_diag_mul U hU1]
      have : (fun i => a i * a i) = fun i => (l i : ℂ) * (l i : ℂ) := by
        funext i
        simp only [a]
        rw [← Complex.ofReal_mul, abs_mul_abs_self]; push_cast; ring
      rw [this]
    · rw [Matrix.nonneg_iff_posSemidef, star_eq_conjTranspose]
      refine PosSemidef.mul_mul_conjTranspose_same ?_ U
      rw [posSemidef_diagonal_iff]
      intro i
      exact Complex.zero_le_real.mpr (abs_nonneg _)

/-- Cauchy–Schwarz for `star x ⬝ᵥ y`, squared form. -/
theorem norm_dot_sq_le {κ : Type} [Fintype κ] (x y : κ → ℂ) :
    ‖star x ⬝ᵥ y‖ ^ 2 ≤ (star x ⬝ᵥ x).re * (star y ⬝ᵥ y).re := by
  have hn : ∀ z : κ → ℂ, ‖(WithLp.toLp 2 z : EuclideanSpace ℂ κ)‖ ^ 2 = (star z ⬝ᵥ z).re := by
    intro z
    have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (WithLp.toLp 2 z : EuclideanSpace ℂ κ)
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at this
    rw [this]; norm_cast
  have hi : inner ℂ (WithLp.toLp 2 x : EuclideanSpace ℂ κ) (WithLp.toLp 2 y) = star x ⬝ᵥ y := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  have h := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 x : EuclideanSpace ℂ κ) (WithLp.toLp 2 y)
  rw [hi] at h
  rw [← hn, ← hn, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

/-- Frobenius norm squared. -/
noncomputable def fn (A : Matrix ι ι ℂ) : ℝ := (trace (Aᴴ * A)).re

def vec (A : Matrix ι ι ℂ) : ι × ι → ℂ := fun p => A p.1 p.2

theorem trace_eq_dot (A B : Matrix ι ι ℂ) : trace (Aᴴ * B) = star (vec A) ⬝ᵥ vec B := by
  simp only [trace, diag, mul_apply, conjTranspose_apply, dotProduct, vec, Pi.star_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_comm]

theorem fn_ofReal (A : Matrix ι ι ℂ) : trace (Aᴴ * A) = ((fn A : ℝ) : ℂ) := by
  have h := Complex.nonneg_iff.mp (posSemidef_conjTranspose_mul_self A).trace_nonneg
  apply Complex.ext
  · simp [fn]
  · simp [fn, ← h.2]

theorem fn_nonneg (A : Matrix ι ι ℂ) : 0 ≤ fn A :=
  (Complex.nonneg_iff.mp (posSemidef_conjTranspose_mul_self A).trace_nonneg).1

theorem cs (A B : Matrix ι ι ℂ) : ‖trace (Aᴴ * B)‖ ≤ Real.sqrt (fn A) * Real.sqrt (fn B) := by
  have h := norm_dot_sq_le (vec A) (vec B)
  rw [← trace_eq_dot, ← trace_eq_dot, ← trace_eq_dot] at h
  rw [← Real.sqrt_mul (fn_nonneg A)]
  have := Real.abs_le_sqrt h
  rwa [abs_of_nonneg (norm_nonneg _)] at this

theorem cs_sq (A B : Matrix ι ι ℂ) : ‖trace (Aᴴ * B)‖ ^ 2 ≤ fn A * fn B := by
  have h := norm_dot_sq_le (vec A) (vec B)
  rwa [← trace_eq_dot, ← trace_eq_dot, ← trace_eq_dot] at h

theorem proj_compl {P : Matrix ι ι ℂ} (hP : IsProjector P) : IsProjector (1 - P) := by
  refine ⟨?_, ?_⟩
  · unfold IsHermitian; rw [conjTranspose_sub, conjTranspose_one, hP.1.eq]
  · have := hP.2
    rw [sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul, this]; abel

theorem proj_sq {R : Matrix ι ι ℂ} (hR : IsProjector R) (A B : Matrix ι ι ℂ) :
    (R * A)ᴴ * (R * B) = Aᴴ * (R * B) := by
  rw [conjTranspose_mul, hR.1.eq, mul_assoc, ← mul_assoc R R, hR.2]

theorem decomp {R : Matrix ι ι ℂ} (hR : IsProjector R) (A B : Matrix ι ι ℂ) :
    trace (Aᴴ * B) = trace ((R * A)ᴴ * (R * B)) + trace (((1 - R) * A)ᴴ * ((1 - R) * B)) := by
  rw [proj_sq hR, proj_sq (proj_compl hR), ← trace_add, ← mul_add, ← add_mul]
  simp

theorem fn_decomp {R : Matrix ι ι ℂ} (hR : IsProjector R) (A : Matrix ι ι ℂ) :
    fn A = fn (R * A) + fn ((1 - R) * A) := by
  unfold fn; rw [decomp hR A A, Complex.add_re]

theorem scalar (n q p X m S E : ℝ) (hq0 : 0 ≤ q) (hnq : 0 ≤ n - q) (hp1 : 0 ≤ 1 - p)
    (_hX : 0 ≤ X) (hm : 0 ≤ m) (hS : 0 ≤ S) (hSXm : S ≤ X + m)
    (hm2 : m ^ 2 ≤ (n - q) * (1 - p)) (hih : (1 - E) * n ≤ S ^ 2) :
    (1 - (E + (1 - p))) * q ≤ X ^ 2 := by
  rcases (show 0 ≤ n by linarith).eq_or_lt with h0 | hn
  · have : q = 0 := by linarith
    subst this; simp; positivity
  · have key : 0 ≤ n * X ^ 2 - q * (X + m) ^ 2 - q * n * (p - 1) := by
      rcases hnq.eq_or_lt with h | h
      · have hm0 : m = 0 := by
          rw [← h, zero_mul] at hm2; nlinarith
        have : q = n := by linarith
        subst hm0; rw [this]; nlinarith
      · have iden : (n - q) * (n * X ^ 2 - q * (X + m) ^ 2 - q * n * (p - 1)) =
            ((n - q) * X - q * m) ^ 2 + q * n * ((1 - p) * (n - q) - m ^ 2) := by ring
        have : 0 ≤ (n - q) * (n * X ^ 2 - q * (X + m) ^ 2 - q * n * (p - 1)) := by
          rw [iden]
          have h1 : 0 ≤ q * n * ((1 - p) * (n - q) - m ^ 2) := by
            apply mul_nonneg (mul_nonneg hq0 hn.le); nlinarith
          positivity
        exact (mul_nonneg_iff_of_pos_left h).mp this
    have hS2 : S ^ 2 ≤ (X + m) ^ 2 := pow_le_pow_left₀ hS hSXm 2
    have h1 : q * S ^ 2 ≤ q * (X + m) ^ 2 := mul_le_mul_of_nonneg_left hS2 hq0
    have h2 : q * ((1 - E) * n) ≤ q * S ^ 2 := mul_le_mul_of_nonneg_left hih hq0
    have h3 : n * ((1 - (E + (1 - p))) * q) ≤ n * X ^ 2 := by nlinarith
    exact le_of_mul_le_mul_left h3 hn

lemma seqOp_succ {n : ℕ} (P : Fin (n+1) → Matrix ι ι ℂ) :
    seqOp P = P (Fin.last n) * seqOp (fun i => P i.castSucc) := by
  unfold seqOp
  rw [List.ofFn_succ', List.concat_eq_append, List.foldl_concat]

theorem induct (W : Matrix ι ι ℂ) (hW : fn W = 1) {N : ℕ} (P : Fin N → Matrix ι ι ℂ)
    (hP : ∀ i, IsProjector (P i)) :
    (1 - ∑ i, (1 - fn (P i * W))) * fn (seqOp P * W) ≤ ‖trace (Wᴴ * (seqOp P * W))‖ ^ 2 := by
  induction N with
  | zero =>
    have h1 : seqOp P = 1 := by simp [seqOp]
    rw [h1, one_mul, fn_ofReal, hW]
    simp
  | succ n ih =>
    have ih' := ih (fun i => P i.castSucc) (fun i => hP _)
    rw [seqOp_succ, Fin.sum_univ_castSucc]
    set K := seqOp (fun i => P i.castSucc)
    set R := P (Fin.last n)
    have hR : IsProjector R := hP _
    set E := ∑ i : Fin n, (1 - fn (P i.castSucc * W))
    rw [mul_assoc R K W]
    set x := K * W
    have hdec := decomp hR W x
    rw [proj_sq hR] at hdec
    have hSXm : ‖trace (Wᴴ * x)‖ ≤ ‖trace (Wᴴ * (R * x))‖
        + ‖trace (((1 - R) * W)ᴴ * ((1 - R) * x))‖ := by
      rw [hdec]; exact norm_add_le _ _
    have hm2 := cs_sq ((1 - R) * W) ((1 - R) * x)
    have hfW := fn_decomp hR W
    have hfx := fn_decomp hR x
    rw [hW] at hfW
    refine scalar (fn x) (fn (R * x)) (fn (R * W)) _ _ _ E (fn_nonneg _) (by
      linarith [fn_nonneg ((1 - R) * x)]) (by linarith [fn_nonneg ((1 - R) * W)])
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hSXm ?_ ih'
    have e1 : fn ((1 - R) * W) = 1 - fn (R * W) := by linarith
    have e2 : fn ((1 - R) * x) = fn x - fn (R * x) := by linarith
    rw [e1, e2] at hm2; linarith

theorem tn_bound (A B : Matrix ι ι ℂ) :
    traceNorm (A * Aᴴ - B * Bᴴ) ≤ Real.sqrt (fn (A + B)) * Real.sqrt (fn (A - B)) := by
  set X := A * Aᴴ - B * Bᴴ
  have hX : X.IsHermitian := by
    unfold IsHermitian
    simp [X, conjTranspose_sub, conjTranspose_mul]
  obtain ⟨S, hS1, hS⟩ := herm_sign X hX
  unfold traceNorm
  rw [hS]
  clear hX
  set C := A + B
  set D := A - B
  have hX2 : (2 : ℂ) • X = C * Dᴴ + D * Cᴴ := by
    simp only [X, C, D, conjTranspose_add, conjTranspose_sub, add_mul, mul_add, sub_mul,
      mul_sub, two_smul]
    abel
  have h2 := congrArg (fun M => (trace (S * M)).re) hX2
  simp only [Matrix.mul_smul, trace_smul, mul_add, trace_add, Complex.add_re, smul_eq_mul] at h2
  have hSC : ∀ M : Matrix ι ι ℂ, fn (S * M) = fn M := by
    intro M; unfold fn
    rw [conjTranspose_mul, mul_assoc, ← mul_assoc Sᴴ S, hS1, one_mul]
  have b1 : (trace (S * (C * Dᴴ))).re ≤ Real.sqrt (fn D) * Real.sqrt (fn C) := by
    rw [← mul_assoc, trace_mul_comm]
    refine (Complex.re_le_norm _).trans ?_
    have := cs D (S * C); rwa [hSC] at this
  have b2 : (trace (S * (D * Cᴴ))).re ≤ Real.sqrt (fn C) * Real.sqrt (fn D) := by
    rw [← mul_assoc, trace_mul_comm]
    refine (Complex.re_le_norm _).trans ?_
    have := cs C (S * D); rwa [hSC] at this
  simp only [Complex.mul_re] at h2
  norm_num at h2
  nlinarith [b1, b2]

end GaoDist

namespace GaoDist

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem phase (t : ℂ) (q : ℝ) (hq : 0 < q) :
    ∃ c : ℂ, star c * c = ((q : ℂ))⁻¹ ∧ c * t = ((‖t‖ / Real.sqrt q : ℝ) : ℂ) := by
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  have hsq : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt hq.le
  by_cases ht : t = 0
  · refine ⟨((Real.sqrt q)⁻¹ : ℝ), ?_, ?_⟩
    · rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_inv]
      congr 1
      rw [← mul_inv, Real.mul_self_sqrt hq.le]
    · subst ht; simp
  · have hn : 0 < ‖t‖ := norm_pos_iff.mpr ht
    refine ⟨star t * ((‖t‖ * Real.sqrt q)⁻¹ : ℝ), ?_, ?_⟩
    · rw [star_mul, star_star, Complex.star_def, Complex.conj_ofReal]
      have e : t * star t = ((‖t‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      calc ((((‖t‖ * Real.sqrt q)⁻¹ : ℝ) : ℂ) * t) * (star t * (((‖t‖ * Real.sqrt q)⁻¹ : ℝ) : ℂ))
          = (((‖t‖ * Real.sqrt q)⁻¹ : ℝ) : ℂ) * (((‖t‖ * Real.sqrt q)⁻¹ : ℝ) : ℂ)
              * (t * star t) := by ring
        _ = _ := by
          rw [e, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_inv]
          congr 1
          field_simp
          rw [hsq]
    · have e : star t * t = ((‖t‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      rw [mul_comm, ← mul_assoc, mul_comm t, e]
      push_cast; field_simp

theorem main {N : ℕ} (ρ : Matrix ι ι ℂ) (hρ : IsDensityOperator ρ)
    (P : Fin N → Matrix ι ι ℂ) (hP : ∀ i, IsProjector (P i)) (hq : 0 < successProb P ρ) :
    traceDist ρ (postState P ρ) ≤ 2 * Real.sqrt (failureSum P ρ) := by
  obtain ⟨hpsd, htr⟩ := hρ
  set W := CFC.sqrt ρ
  have hW0 : 0 ≤ W := CFC.sqrt_nonneg ρ
  have hWh : Wᴴ = W := (Matrix.nonneg_iff_posSemidef.mp hW0).1.eq
  have hWW : W * W = ρ := CFC.sqrt_mul_sqrt_self ρ (Matrix.nonneg_iff_posSemidef.mpr hpsd)
  have hfW : fn W = 1 := by unfold fn; rw [hWh, hWW, htr]; simp
  have hfP : ∀ Q : Matrix ι ι ℂ, IsProjector Q → 1 - fn (Q * W) = failureTerm Q ρ := by
    intro Q hQ
    unfold fn failureTerm
    rw [proj_sq hQ, hWh, trace_mul_comm W, mul_assoc, hWW, sub_mul, one_mul, trace_sub,
      Complex.sub_re, htr]
    simp
  set K := seqOp P
  set q := successProb P ρ
  have hfK : fn (K * W) = q := by
    unfold fn
    rw [conjTranspose_mul, hWh, trace_mul_comm]
    simp only [q, successProb, seqOutput, ← hWW, K, mul_assoc]
  have hind := induct W hfW P hP
  have hE : ∑ i, (1 - fn (P i * W)) = failureSum P ρ := by
    unfold failureSum; exact Finset.sum_congr rfl (fun i _ => hfP _ (hP i))
  rw [hE, hfK] at hind
  set t := trace (Wᴴ * (K * W))
  set E := failureSum P ρ
  obtain ⟨c, hc1, hct⟩ := phase t q hq
  set B := c • (K * W)
  have hAA : W * Wᴴ = ρ := by rw [hWh, hWW]
  have hBB : B * Bᴴ = postState P ρ := by
    simp only [B, conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, postState,
      seqOutput, conjTranspose_mul, hWh]
    rw [hc1, show K * W * (W * Kᴴ) = K * ρ * Kᴴ by rw [← hWW]; simp only [mul_assoc]]
  have hfB : fn B = 1 := by
    unfold fn
    simp only [B, conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, trace_smul,
      smul_eq_mul]
    rw [mul_comm c, hc1, fn_ofReal, hfK]
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.ofReal_re, inv_mul_cancel₀ hq.ne']
  set r := ‖t‖ / Real.sqrt q
  have hr0 : 0 ≤ r := div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  have hAB : (trace (Wᴴ * B)).re = r := by
    simp only [B, Matrix.mul_smul, trace_smul, smul_eq_mul]
    rw [hct, Complex.ofReal_re]
  have hBA : (trace (Bᴴ * W)).re = r := by
    rw [← hAB, show Bᴴ * W = (Wᴴ * B)ᴴ by rw [conjTranspose_mul, conjTranspose_conjTranspose],
      trace_conjTranspose]
    simp
  have hplus : fn (W + B) = 2 + 2 * r := by
    unfold fn at hfW hfB ⊢
    rw [conjTranspose_add, add_mul, mul_add, mul_add, trace_add, trace_add, trace_add]
    simp only [Complex.add_re]; rw [hfW, hfB, hAB, hBA]; ring
  have hminus : fn (W - B) = 2 - 2 * r := by
    unfold fn at hfW hfB ⊢
    rw [conjTranspose_sub, sub_mul, mul_sub, mul_sub, trace_sub, trace_sub, trace_sub]
    simp only [Complex.sub_re]; rw [hfW, hfB, hAB, hBA]; ring
  have hb := tn_bound W B
  rw [hAA, hBB, hplus, hminus] at hb
  unfold traceDist
  refine hb.trans ?_
  have hr2 : 1 - E ≤ r ^ 2 := by
    have : r ^ 2 = ‖t‖ ^ 2 / q := by
      simp only [r]; rw [div_pow, Real.sq_sqrt hq.le]
    rw [this, le_div_iff₀ hq]; linarith
  rw [← Real.sqrt_mul (by linarith)]
  calc Real.sqrt ((2 + 2 * r) * (2 - 2 * r)) ≤ Real.sqrt (2 ^ 2 * E) :=
        Real.sqrt_le_sqrt (by nlinarith)
    _ = 2 * Real.sqrt E := by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]

end GaoDist

theorem solution {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ}
    (ρ : Matrix ι ι ℂ) (hρ : IsDensityOperator ρ)
    (P : Fin N → Matrix ι ι ℂ) (hP : ∀ i, IsProjector (P i)) (hq : 0 < successProb P ρ) :
    traceDist ρ (postState P ρ) ≤ 2*Real.sqrt (failureSum P ρ) :=
  GaoDist.main ρ hρ P hP hq
