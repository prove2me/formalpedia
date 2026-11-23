-- Prove2me | solution 1 for GaoQuantumUnion.one_step_disturbance
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-23T06:06:32.389287+00:00
-- url     : https://prove2.me/submissions/5a58a16c-b3bf-43d2-9b62-e9cdeab715e5

import Definitions.Def_GaoQuantumUnion_Model
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.NoncommRing
open Matrix WildeQIT GaoQuantumUnion
open scoped MatrixOrder ComplexOrder ComplexConjugate
set_option autoImplicit false

namespace GaoOneStep

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Cauchy–Schwarz for `star x ⬝ᵥ y`, squared form. -/
theorem norm_dot_sq_le (x y : ι → ℂ) :
    ‖star x ⬝ᵥ y‖ ^ 2 ≤ (star x ⬝ᵥ x).re * (star y ⬝ᵥ y).re := by
  have hn : ∀ z : ι → ℂ, ‖(WithLp.toLp 2 z : EuclideanSpace ℂ ι)‖ ^ 2 = (star z ⬝ᵥ z).re := by
    intro z
    have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (WithLp.toLp 2 z : EuclideanSpace ℂ ι)
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at this
    rw [this]; norm_cast
  have hi : inner ℂ (WithLp.toLp 2 x : EuclideanSpace ℂ ι) (WithLp.toLp 2 y) = star x ⬝ᵥ y := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  have h := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 x : EuclideanSpace ℂ ι) (WithLp.toLp 2 y)
  rw [hi] at h
  rw [← hn, ← hn, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

theorem cube {R : Type*} [Ring R] [Algebra ℂ R] (A B : R) (k : ℂ) (hA : A * A = A)
    (hB : B * B = B) (h1 : A * B * A = k • A) (h2 : B * A * B = k • B) :
    (A - B) * (A - B) * (A - B) = (1 - k) • (A - B) := by
  have e : (A - B) * (A - B) * (A - B) = A * A * A - A * A * B - A * B * A + A * B * B
      - B * A * A + B * A * B + B * B * A - B * B * B := by noncomm_ring
  rw [e, h1, h2, hA, hA, mul_assoc A B B, hB, mul_assoc B A A, hA, hB]
  rw [sub_smul, one_smul, smul_sub]; abel

/-- **Pure-state trace distance.** For unit vectors `u`, `v`,
`‖|u⟩⟨u| - |v⟩⟨v|‖₁ = 2 √(1 - |⟨v,u⟩|²)`. -/
theorem traceNorm_pureState_sub (u v : ι → ℂ) (hu : star u ⬝ᵥ u = 1) (hv : star v ⬝ᵥ v = 1) :
    traceNorm (pureState u - pureState v) = 2 * Real.sqrt (1 - ‖star v ⬝ᵥ u‖ ^ 2) := by
  set s : ℂ := star v ⬝ᵥ u with hs
  have hvu : star v ⬝ᵥ u = s := rfl
  have huv : star u ⬝ᵥ v = star s := by
    rw [hs, ← star_dotProduct_star, star_star, dotProduct_comm]
  set A := vecMulVec u (star u)
  set B := vecMulVec v (star v)
  set k : ℂ := star s * s
  have hA : A * A = A := by simp [A, vecMulVec_mul_vecMulVec, hu]
  have hB : B * B = B := by simp [B, vecMulVec_mul_vecMulVec, hv]
  have h1 : A * B * A = k • A := by
    simp only [A, B, vecMulVec_mul_vecMulVec, huv, hvu, vecMulVec_smul, smul_smul, k,
      Matrix.smul_mul]
  have h2 : B * A * B = k • B := by
    simp only [A, B, vecMulVec_mul_vecMulVec, huv, hvu, vecMulVec_smul, smul_smul, k,
      Matrix.smul_mul]
    rw [mul_comm]
  set D := A - B
  have hDh : Dᴴ = D := by
    simp [D, A, B, conjTranspose_sub, conjTranspose_vecMulVec]
  have hD3 := cube A B k hA hB h1 h2
  have hk : k = ((‖s‖ ^ 2 : ℝ) : ℂ) := by
    simp only [k]; rw [mul_comm, Complex.star_def, Complex.mul_conj']; push_cast; ring
  set c : ℝ := 1 - ‖s‖ ^ 2
  have hc0 : 0 ≤ c := by
    have := norm_dot_sq_le v u
    rw [hu, hv] at this
    simp only [c]; simpa [s] using this
  have h1k : (1 - k) = (c : ℂ) := by rw [hk]; simp [c]
  rw [h1k] at hD3
  have htr : (trace (D * D)).re = 2 * c := by
    simp only [D, sub_mul, mul_sub, trace_sub, A, B, vecMulVec_mul_vecMulVec, trace_vecMulVec,
      hu, hv, huv, hvu, one_smul, vecMulVec_smul, trace_smul, smul_eq_mul]
    rw [dotProduct_comm u (star u), dotProduct_comm v (star u), dotProduct_comm u (star v),
      dotProduct_comm v (star v), hu, hv, huv, hvu]
    have : star s * s = ((‖s‖ ^ 2 : ℝ) : ℂ) := hk
    rw [mul_comm s, this]
    simp [c]; rw [← Complex.ofReal_pow, Complex.ofReal_re]; ring
  have hDD : D * D * D * D = (c : ℂ) • (D * D) := by
    rw [hD3, Matrix.smul_mul]
  unfold traceNorm
  change (trace (CFC.sqrt (Dᴴ * D))).re = _
  rw [hDh]
  have hpsd : (D * D).PosSemidef := by
    have := Matrix.posSemidef_conjTranspose_mul_self D; rwa [hDh] at this
  rcases hc0.eq_or_lt with h0 | hpos
  · have e1 : (D * D)ᴴ * (D * D) = 0 := by
      rw [hpsd.1.eq, ← mul_assoc, hDD, ← h0]; simp
    have e2 : D * D = 0 := Matrix.conjTranspose_mul_self_eq_zero.mp e1
    rw [e2, ← h0]; simp
  · set l := Real.sqrt c
    have hl : 0 < l := Real.sqrt_pos.mpr hpos
    have hll : l * l = c := Real.mul_self_sqrt hc0
    have hsq : CFC.sqrt (D * D) = ((l⁻¹ : ℝ) : ℂ) • (D * D) := by
      refine CFC.sqrt_unique ?_ ?_
      · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← mul_assoc, hDD, smul_smul]
        rw [show ((l⁻¹ : ℝ) : ℂ) * ((l⁻¹ : ℝ) : ℂ) * (c : ℂ) = 1 by
          rw [← hll]; push_cast; field_simp]
        rw [one_smul]
      · rw [Matrix.nonneg_iff_posSemidef]
        exact hpsd.smul (by exact_mod_cast (inv_pos.mpr hl).le)
    rw [hsq, trace_smul, smul_eq_mul, Complex.re_ofReal_mul, htr]
    rw [← hll]; field_simp


/-- `star w ⬝ᵥ w` is the real number `∑ ‖w i‖²`. -/
theorem dot_self_eq (w : ι → ℂ) : star w ⬝ᵥ w = ((∑ i, ‖w i‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_mul']
  push_cast; rfl

theorem dot_self_ofReal (w : ι → ℂ) : star w ⬝ᵥ w = ((star w ⬝ᵥ w).re : ℂ) := by
  rw [dot_self_eq, Complex.ofReal_re]

theorem dot_self_re_nonneg (w : ι → ℂ) : 0 ≤ (star w ⬝ᵥ w).re := by
  rw [dot_self_eq, Complex.ofReal_re]; positivity

theorem unit_dot (ψ : ι → ℂ) (hψ : IsUnitVector ψ) : star ψ ⬝ᵥ ψ = 1 := by
  rw [dot_self_eq]; unfold IsUnitVector at hψ; rw [hψ]; simp

/-- Trace distance between unit pure states, in `traceDist` form. -/
theorem traceDist_pureState (u v : ι → ℂ) (hu : star u ⬝ᵥ u = 1) (hv : star v ⬝ᵥ v = 1) :
    traceDist (pureState u) (pureState v) = 2 * Real.sqrt (1 - ‖star v ⬝ᵥ u‖ ^ 2) :=
  traceNorm_pureState_sub u v hu hv

theorem one_sub_norm_dot_sq_nonneg (u v : ι → ℂ) (hu : star u ⬝ᵥ u = 1)
    (hv : star v ⬝ᵥ v = 1) : 0 ≤ 1 - ‖star v ⬝ᵥ u‖ ^ 2 := by
  have := norm_dot_sq_le v u
  rw [hu, hv] at this
  simp at this; nlinarith [norm_nonneg (star v ⬝ᵥ u)]

theorem proj_dot {Q : Matrix ι ι ℂ} (hQ : IsProjector Q) (x y : ι → ℂ) :
    star (Q *ᵥ x) ⬝ᵥ (Q *ᵥ y) = star x ⬝ᵥ (Q *ᵥ y) := by
  rw [star_mulVec, hQ.1.eq, ← dotProduct_mulVec, mulVec_mulVec, hQ.2]

theorem proj_dot_left {Q : Matrix ι ι ℂ} (hQ : IsProjector Q) (x y : ι → ℂ) :
    star (Q *ᵥ x) ⬝ᵥ y = star x ⬝ᵥ (Q *ᵥ y) := by
  rw [star_mulVec, hQ.1.eq, ← dotProduct_mulVec]

theorem proj_compl {P : Matrix ι ι ℂ} (hP : IsProjector P) : IsProjector (1 - P) := by
  refine ⟨?_, ?_⟩
  · unfold IsHermitian; rw [conjTranspose_sub, conjTranspose_one, hP.1.eq]
  · have := hP.2
    rw [sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul, this]; abel

theorem dot_decomp {P : Matrix ι ι ℂ} (hP : IsProjector P) (x y : ι → ℂ) :
    star x ⬝ᵥ y = star (P *ᵥ x) ⬝ᵥ (P *ᵥ y) + star ((1 - P) *ᵥ x) ⬝ᵥ ((1 - P) *ᵥ y) := by
  rw [proj_dot hP, proj_dot (proj_compl hP), sub_mulVec, one_mulVec, dotProduct_sub]
  ring

theorem seqOp_one (P : Matrix ι ι ℂ) : seqOp (fun _ : Fin 1 => P) = P := by
  simp [seqOp]

theorem seqOutput_pure {P : Matrix ι ι ℂ} (hP : IsProjector P) (φ : ι → ℂ) :
    seqOutput (fun _ : Fin 1 => P) (pureState φ) = pureState (P *ᵥ φ) := by
  rw [seqOutput, seqOp_one, pureState, pureState, mul_vecMulVec, vecMulVec_mul, star_mulVec]

theorem successProb_pure {P : Matrix ι ι ℂ} (hP : IsProjector P) (φ : ι → ℂ) :
    successProb (fun _ : Fin 1 => P) (pureState φ) = (star (P *ᵥ φ) ⬝ᵥ (P *ᵥ φ)).re := by
  rw [successProb, seqOutput_pure hP, pureState, trace_vecMulVec, dotProduct_comm]

theorem pureState_real_smul (r : ℝ) (w : ι → ℂ) :
    pureState (((r : ℝ) : ℂ) • w) = ((r ^ 2 : ℝ) : ℂ) • pureState w := by
  unfold pureState
  rw [star_smul, smul_vecMulVec, vecMulVec_smul, smul_smul, Complex.star_def,
    Complex.conj_ofReal]
  push_cast; ring_nf

theorem postState_pure {P : Matrix ι ι ℂ} (hP : IsProjector P) (φ : ι → ℂ)
    (hq : 0 < successProb (fun _ : Fin 1 => P) (pureState φ)) :
    postState (fun _ : Fin 1 => P) (pureState φ) =
      pureState ((((Real.sqrt (star (P *ᵥ φ) ⬝ᵥ (P *ᵥ φ)).re)⁻¹ : ℝ) : ℂ) • (P *ᵥ φ)) := by
  rw [successProb_pure hP] at hq
  rw [postState, successProb_pure hP, seqOutput_pure hP, pureState_real_smul, inv_pow,
    Real.sq_sqrt hq.le]
  push_cast; rfl

theorem real_smul_unit (r : ℝ) (w : ι → ℂ) (hr : r = (Real.sqrt (star w ⬝ᵥ w).re)⁻¹)
    (hw : 0 < (star w ⬝ᵥ w).re) :
    star (((r : ℝ) : ℂ) • w) ⬝ᵥ (((r : ℝ) : ℂ) • w) = 1 := by
  rw [star_smul, smul_dotProduct, dotProduct_smul, Complex.star_def, Complex.conj_ofReal,
    dot_self_ofReal w, smul_eq_mul, smul_eq_mul, hr]
  have h1 : Real.sqrt (star w ⬝ᵥ w).re ^ 2 = (star w ⬝ᵥ w).re := Real.sq_sqrt hw.le
  have h2 : Real.sqrt (star w ⬝ᵥ w).re ≠ 0 := (Real.sqrt_pos.mpr hw).ne'
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
  norm_cast
  field_simp
  linarith

theorem norm_real_smul_dot_sq (r : ℝ) (w x : ι → ℂ) :
    ‖star (((r : ℝ) : ℂ) • w) ⬝ᵥ x‖ ^ 2 = r ^ 2 * ‖star w ⬝ᵥ x‖ ^ 2 := by
  rw [star_smul, smul_dotProduct, Complex.star_def, Complex.conj_ofReal, smul_eq_mul, norm_mul,
    Complex.norm_real, mul_pow, Real.norm_eq_abs, sq_abs]

/-- The scalar core of Gao's one-step lemma (Cauchy–Schwarz in `ℝ²`). -/
theorem scalar_core (p q S X m : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) (hp1 : p ≤ 1) (hX : 0 ≤ X)
    (hm : 0 ≤ m) (hS : 0 ≤ S) (hSXm : S ≤ X + m) (hm2 : m ^ 2 ≤ (1 - q) * (1 - p)) :
    4 * (1 - X ^ 2 / q) ≤ 4 * (1 - S ^ 2) + 4 * (1 - p) := by
  have hS2 : S ^ 2 ≤ (X + m) ^ 2 := pow_le_pow_left₀ hS hSXm 2
  have hE : 0 ≤ X ^ 2 - q * (X + m) ^ 2 - q * (p - 1) := by
    rcases hq1.lt_or_eq with hlt | heq
    · have key : (1 - q) * (X ^ 2 - q * (X + m) ^ 2 - q * (p - 1)) =
          ((1 - q) * X - q * m) ^ 2 + q * ((1 - p) * (1 - q) - m ^ 2) := by ring
      have : 0 ≤ (1 - q) * (X ^ 2 - q * (X + m) ^ 2 - q * (p - 1)) := by
        rw [key]; have := sq_nonneg ((1 - q) * X - q * m); nlinarith
      exact (mul_nonneg_iff_of_pos_left (by linarith)).mp this
    · subst heq
      have : m = 0 := by nlinarith
      subst this; nlinarith
  have hXq : q * (S ^ 2 + p - 1) ≤ X ^ 2 := by nlinarith
  have : S ^ 2 + p - 1 ≤ X ^ 2 / q := by rw [le_div_iff₀ hq]; linarith
  linarith

end GaoOneStep

namespace GaoOneStep

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem main (ψ φ : ι → ℂ) (hψ : IsUnitVector ψ) (hφ : IsUnitVector φ)
    (P : Matrix ι ι ℂ) (hP : IsProjector P)
    (hψq : 0 < successProb (fun _ : Fin 1 => P) (pureState ψ))
    (hφq : 0 < successProb (fun _ : Fin 1 => P) (pureState φ)) :
    (traceDist (pureState ψ) (postState (fun _ : Fin 1 => P) (pureState φ)))^2 ≤
      (traceDist (pureState ψ) (pureState φ))^2+
      (traceDist (pureState ψ) (postState (fun _ : Fin 1 => P) (pureState ψ)))^2 := by
  have hψ1 := unit_dot ψ hψ
  have hφ1 := unit_dot φ hφ
  rw [postState_pure hP φ hφq, postState_pure hP ψ hψq]
  rw [successProb_pure hP] at hψq hφq
  set a := P *ᵥ ψ with ha
  set c := P *ᵥ φ with hc
  set b := (1 - P) *ᵥ ψ with hb
  set d := (1 - P) *ᵥ φ with hd
  set p := (star a ⬝ᵥ a).re with hp
  set q := (star c ⬝ᵥ c).re with hq
  set rc : ℝ := (Real.sqrt q)⁻¹ with hrc
  set ra : ℝ := (Real.sqrt p)⁻¹ with hra
  have hcu := real_smul_unit rc c hrc hφq
  have hau := real_smul_unit ra a hra hψq
  rw [traceDist_pureState ψ _ hψ1 hcu, traceDist_pureState ψ _ hψ1 hφ1,
    traceDist_pureState ψ _ hψ1 hau]
  rw [mul_pow, mul_pow, mul_pow,
    Real.sq_sqrt (one_sub_norm_dot_sq_nonneg ψ _ hψ1 hcu),
    Real.sq_sqrt (one_sub_norm_dot_sq_nonneg ψ _ hψ1 hφ1),
    Real.sq_sqrt (one_sub_norm_dot_sq_nonneg ψ _ hψ1 hau),
    norm_real_smul_dot_sq, norm_real_smul_dot_sq]
  -- rewrite the overlaps
  have e1 : star c ⬝ᵥ ψ = star c ⬝ᵥ a := by
    rw [hc, ha, proj_dot hP, proj_dot_left hP]
  have e2 : star a ⬝ᵥ ψ = (p : ℂ) := by
    rw [ha, proj_dot_left hP, ← proj_dot hP, ← ha, hp, ← dot_self_ofReal]
  have hdec := dot_decomp hP φ ψ
  rw [← hc, ← hd, ← ha, ← hb] at hdec
  have hφdec := dot_decomp hP φ φ
  rw [← hc, ← hd, hφ1] at hφdec
  have hψdec := dot_decomp hP ψ ψ
  rw [← ha, ← hb, hψ1] at hψdec
  have hq1 : q + (star d ⬝ᵥ d).re = 1 := by
    have := congrArg Complex.re hφdec; simpa [Complex.add_re] using this.symm
  have hp1 : p + (star b ⬝ᵥ b).re = 1 := by
    have := congrArg Complex.re hψdec; simpa [Complex.add_re] using this.symm
  have hrc2 : rc ^ 2 = 1 / q := by
    rw [hrc, inv_pow, Real.sq_sqrt hφq.le, one_div]
  have hra2 : ra ^ 2 = 1 / p := by
    rw [hra, inv_pow, Real.sq_sqrt hψq.le, one_div]
  rw [e1, e2, hrc2, hra2, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hpp : 1 / p * p ^ 2 = p := by field_simp
  rw [hpp]
  have hcs := norm_dot_sq_le d b
  have hSle : ‖star φ ⬝ᵥ ψ‖ ≤ ‖star c ⬝ᵥ a‖ + ‖star d ⬝ᵥ b‖ := by
    rw [hdec]; exact norm_add_le _ _
  have h := scalar_core p q ‖star φ ⬝ᵥ ψ‖ ‖star c ⬝ᵥ a‖ ‖star d ⬝ᵥ b‖ hφq
    (by linarith [dot_self_re_nonneg d]) (by linarith [dot_self_re_nonneg b])
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hSle
    (by
      have e3 : 1 - q = (star d ⬝ᵥ d).re := by linarith
      have e4 : 1 - p = (star b ⬝ᵥ b).re := by linarith
      rw [e3, e4]; exact hcs)
  rw [one_div_mul_eq_div]
  linarith

end GaoOneStep

theorem solution {ι : Type} [Fintype ι] [DecidableEq ι]
    (ψ φ : ι → ℂ) (hψ : IsUnitVector ψ) (hφ : IsUnitVector φ)
    (P : Matrix ι ι ℂ) (hP : IsProjector P)
    (hψq : 0 < successProb (fun _ : Fin 1 => P) (pureState ψ))
    (hφq : 0 < successProb (fun _ : Fin 1 => P) (pureState φ)) :
    (traceDist (pureState ψ) (postState (fun _ : Fin 1 => P) (pureState φ)))^2 ≤
      (traceDist (pureState ψ) (pureState φ))^2+
      (traceDist (pureState ψ) (postState (fun _ : Fin 1 => P) (pureState ψ)))^2 :=
  GaoOneStep.main ψ φ hψ hφ P hP hψq hφq
