-- Prove2me | solution 1 for BosonicLearn.effect_trace_pairing
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T04:58:27.491114+00:00
-- url     : https://prove2.me/submissions/b86b3da2-3617-44c8-b0f3-1f34ff3f3486

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33

open QAlgorithms.Papers.Independent.Dependency50.P33 (NuclearExpansion)
open QAlgorithms.RealRegisters (Hilbert)
open scoped ENNReal

noncomputable section

/-- Cauchy–Schwarz for the coordinates of two vectors of `ℓ²`, with absolute values. -/
private lemma tsum_norm_mul_le {I : Type} (x y : Hilbert I) :
    Summable (fun i => ‖x i‖ * ‖y i‖) ∧ ∑' i, ‖x i‖ * ‖y i‖ ≤ ‖x‖ * ‖y‖ := by
  have hx2 : Summable fun i => ‖x i‖ ^ 2 := by
    simpa using (lp.memℓp x).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  have hy2 : Summable fun i => ‖y i‖ ^ 2 := by
    simpa using (lp.memℓp y).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  have hx : Summable fun i => ‖x i‖ ^ (2 : ℝ) := by simpa [Real.rpow_two] using hx2
  have hy : Summable fun i => ‖y i‖ ^ (2 : ℝ) := by simpa [Real.rpow_two] using hy2
  refine ⟨?_, ?_⟩
  · refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) ((hx2.add hy2).mul_left (1 / 2))
    nlinarith [sq_nonneg (‖x i‖ - ‖y i‖)]
  · have h := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg (p := 2) (q := 2) (by constructor <;> norm_num)
      (fun i => norm_nonneg (x i)) (fun i => norm_nonneg (y i)) hx hy
    have ex := lp.norm_eq_tsum_rpow (p := (2 : ℝ≥0∞)) (by norm_num) x
    have ey := lp.norm_eq_tsum_rpow (p := (2 : ℝ≥0∞)) (by norm_num) y
    rw [ENNReal.toReal_ofNat] at ex ey
    rw [ex, ey]
    exact h

theorem solution {I : Type} (E : Matrix I I ℂ) (F : Hilbert I →L[ℂ] Hilbert I)
    (hF : ∀ (z : Hilbert I) (i : I), HasSum (fun j => E i j * z j) (F z i))
    (X : Matrix I I ℂ) (e : NuclearExpansion X) :
    (∀ i, Summable fun j => E i j * X j i) ∧
    Summable (fun i => ∑' j, E i j * X j i) ∧
    Summable (fun a => inner ℂ (e.right a) (F (e.left a))) ∧
    ∑' i, ∑' j, E i j * X j i = ∑' a, inner ℂ (e.right a) (F (e.left a)) := by
  have hw : Summable fun a => ‖e.left a‖ * ‖e.right a‖ := e.summable
  have hev : ∀ (j : I) (v : Hilbert I), lp.evalCLM ℂ (fun _ : I => ℂ) 2 j v = v j := fun _ _ => rfl
  -- the `i`-th column of `X` as a norm-convergent series in `ℓ²`
  have hcolS : ∀ i, Summable fun a => star (e.right a i) • e.left a := by
    intro i
    refine Summable.of_norm_bounded hw fun a => ?_
    rw [norm_smul, norm_star, mul_comm]
    exact mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm (by norm_num) (e.right a) i) (norm_nonneg _)
  let col : I → Hilbert I := fun i => ∑' a, star (e.right a i) • e.left a
  have hcol : ∀ i, HasSum (fun a => star (e.right a i) • e.left a) (col i) := fun i => (hcolS i).hasSum
  have hcoord : ∀ i j, col i j = X j i := by
    intro i j
    have h1 : HasSum (fun a => star (e.right a i) * e.left a j) (col i j) := by
      have h := (hcol i).mapL (lp.evalCLM ℂ (fun _ : I => ℂ) 2 j)
      simpa [hev] using h
    have h2 : HasSum (fun a => e.left a j * star (e.right a i)) (X j i) := by
      have hs : Summable fun a => e.left a j * star (e.right a i) := by
        refine Summable.of_norm_bounded hw fun a => ?_
        rw [norm_mul, norm_star]
        exact mul_le_mul (lp.norm_apply_le_norm (by norm_num) (e.left a) j)
          (lp.norm_apply_le_norm (by norm_num) (e.right a) i) (norm_nonneg _) (norm_nonneg _)
      rw [e.coefficients j i]
      exact hs.hasSum
    have h1' : HasSum (fun a => e.left a j * star (e.right a i)) (col i j) := by
      simpa [mul_comm] using h1
    exact h1'.unique h2
  -- the inner sums
  have hinner : ∀ i, HasSum (fun j => E i j * X j i) (F (col i) i) := by
    intro i
    have h := hF (col i) i
    simpa [hcoord] using h
  have hFcol : ∀ i, HasSum (fun a => star (e.right a i) * F (e.left a) i) (F (col i) i) := by
    intro i
    have h := ((hcol i).mapL F).mapL (lp.evalCLM ℂ (fun _ : I => ℂ) 2 i)
    simpa [hev] using h
  -- the double family over `ℕ × I`
  let f : ℕ × I → ℂ := fun p => star (e.right p.1 p.2) * F (e.left p.1) p.2
  have hrow : ∀ a, HasSum (fun i => f (a, i)) (inner ℂ (e.right a) (F (e.left a))) := by
    intro a
    have h := lp.hasSum_inner (𝕜 := ℂ) (e.right a) (F (e.left a))
    simpa [f, RCLike.inner_apply, mul_comm] using h
  have hnorm : Summable fun p : ℕ × I => ‖f p‖ := by
    rw [summable_prod_of_nonneg (fun p => norm_nonneg _)]
    refine ⟨fun a => ?_, ?_⟩
    · have h := (tsum_norm_mul_le (e.right a) (F (e.left a))).1
      simpa [f] using h
    · refine Summable.of_nonneg_of_le (fun a => tsum_nonneg fun i => norm_nonneg _) (fun a => ?_)
        (hw.mul_left ‖F‖)
      have h1 := (tsum_norm_mul_le (e.right a) (F (e.left a))).2
      have h2 : ∑' i, ‖f (a, i)‖ = ∑' i, ‖e.right a i‖ * ‖F (e.left a) i‖ := by simp [f]
      rw [h2]
      calc ∑' i, ‖e.right a i‖ * ‖F (e.left a) i‖ ≤ ‖e.right a‖ * ‖F (e.left a)‖ := h1
        _ ≤ ‖e.right a‖ * (‖F‖ * ‖e.left a‖) :=
            mul_le_mul_of_nonneg_left (F.le_opNorm _) (norm_nonneg _)
        _ = ‖F‖ * (‖e.left a‖ * ‖e.right a‖) := by ring
  have hf : Summable f := hnorm.of_norm
  have hinner_eq : ∀ i, ∑' j, E i j * X j i = ∑' a, f (a, i) := fun i => by
    rw [(hinner i).tsum_eq, (hFcol i).tsum_eq]
  refine ⟨fun i => (hinner i).summable, ?_, ?_, ?_⟩
  · have h : Summable fun i => ∑' a, f (a, i) := hf.prod_symm.prod
    simpa [hinner_eq] using h
  · have h : Summable fun a => ∑' i, f (a, i) := hf.prod
    simpa [fun a => (hrow a).tsum_eq] using h
  · calc ∑' i, ∑' j, E i j * X j i = ∑' i, ∑' a, f (a, i) := tsum_congr hinner_eq
      _ = ∑' a, ∑' i, f (a, i) := Summable.tsum_comm (f := fun a i => f (a, i)) hf
      _ = ∑' a, inner ℂ (e.right a) (F (e.left a)) := tsum_congr fun a => (hrow a).tsum_eq
