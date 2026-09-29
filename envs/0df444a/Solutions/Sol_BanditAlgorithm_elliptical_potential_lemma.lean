-- Prove2me | solution 1 for BanditAlgorithm.elliptical_potential_lemma
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-23T18:33:04.151399+00:00
-- url     : https://prove2.me/submissions/f2ee5d75-191f-4757-a2a7-0e950a96d621

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
Lattimore–Szepesvári, *Bandit Algorithms*, Lemma 19.4 (elliptical potential lemma).
-/

namespace EPL

open Matrix Finset
open scoped BigOperators

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

variable {d : ℕ}

/-- `VM V₀ a t = V₀ + ∑_{s < t} a_{s+1} a_{s+1}ᵀ`. -/
def VM (V₀ : Matrix (Fin d) (Fin d) ℝ) (a : ℕ → Fin d → ℝ) (t : ℕ) :
    Matrix (Fin d) (Fin d) ℝ :=
  V₀ + ∑ s ∈ Finset.range t, vecMulVec (a (s + 1)) (a (s + 1))

lemma VM_zero (V₀ : Matrix (Fin d) (Fin d) ℝ) (a : ℕ → Fin d → ℝ) : VM V₀ a 0 = V₀ := by
  simp [VM]

lemma VM_succ (V₀ : Matrix (Fin d) (Fin d) ℝ) (a : ℕ → Fin d → ℝ) (t : ℕ) :
    VM V₀ a (t + 1) = VM V₀ a t + vecMulVec (a (t + 1)) (a (t + 1)) := by
  simp [VM, Finset.sum_range_succ, add_assoc]

lemma posSemidef_rankOne (x : Fin d → ℝ) : (vecMulVec x x).PosSemidef := by
  have h := Matrix.posSemidef_vecMulVec_self_star (R := ℝ) x
  simpa using h

lemma VM_posDef {V₀ : Matrix (Fin d) (Fin d) ℝ} (hV₀ : V₀.PosDef) (a : ℕ → Fin d → ℝ) (t : ℕ) :
    (VM V₀ a t).PosDef := by
  induction t with
  | zero => rw [VM_zero]; exact hV₀
  | succ t ih => rw [VM_succ]; exact ih.add_posSemidef (posSemidef_rankOne _)

lemma quad_nonneg {W : Matrix (Fin d) (Fin d) ℝ} (hW : W.PosDef) (x : Fin d → ℝ) :
    0 ≤ x ⬝ᵥ (W⁻¹ *ᵥ x) := by
  have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hW.inv.posSemidef).2 x
  simpa using h

/-- The matrix determinant lemma for a rank-one update. -/
lemma det_rank_one_update {W : Matrix (Fin d) (Fin d) ℝ} (hW : W.PosDef) (x : Fin d → ℝ) :
    (W + vecMulVec x x).det = W.det * (1 + x ⬝ᵥ (W⁻¹ *ᵥ x)) := by
  have hu : IsUnit W.det := (hW.det_pos).ne'.isUnit
  have hentry : (Matrix.replicateRow Unit x * W⁻¹ * Matrix.replicateCol Unit x) default default
      = x ⬝ᵥ (W⁻¹ *ᵥ x) := by
    simp only [Matrix.mul_apply, Matrix.replicateRow_apply, Matrix.replicateCol_apply,
      Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hdetU : (1 + Matrix.replicateRow Unit x * W⁻¹ * Matrix.replicateCol Unit x).det
      = 1 + x ⬝ᵥ (W⁻¹ *ᵥ x) := by
    rw [Matrix.det_unique, Matrix.add_apply, Matrix.one_apply_eq, hentry]
  rw [Matrix.vecMulVec_eq Unit x x,
    Matrix.det_add_mul (Matrix.replicateCol Unit x) (Matrix.replicateRow Unit x) hu, hdetU]

lemma det_VM_succ {V₀ : Matrix (Fin d) (Fin d) ℝ} (hV₀ : V₀.PosDef) (a : ℕ → Fin d → ℝ) (t : ℕ) :
    (VM V₀ a (t + 1)).det
      = (VM V₀ a t).det * (1 + a (t + 1) ⬝ᵥ ((VM V₀ a t)⁻¹ *ᵥ a (t + 1))) := by
  rw [VM_succ]
  exact det_rank_one_update (VM_posDef hV₀ a t) _

lemma half_le_log_two : (1:ℝ)/2 ≤ Real.log 2 := by
  have hmul : Real.exp ((1:ℝ)/2) * Real.exp ((1:ℝ)/2) = Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  have hlt : Real.exp ((1:ℝ)/2) < 2 := by
    by_contra hc
    push_neg at hc
    have h4 : (4:ℝ) ≤ Real.exp 1 := by nlinarith [Real.exp_pos ((1:ℝ)/2)]
    linarith [Real.exp_one_lt_d9]
  have h := Real.log_lt_log (Real.exp_pos ((1:ℝ)/2)) hlt
  rw [Real.log_exp] at h
  linarith

/-- `min 1 x ≤ 2 log (1 + x)` for `x ≥ 0`. -/
lemma min_one_le_two_log {x : ℝ} (hx : 0 ≤ x) : min 1 x ≤ 2 * Real.log (1 + x) := by
  have hpos : (0:ℝ) < 1 + x := by linarith
  have hlb : 1 - 1 / (1 + x) ≤ Real.log (1 + x) := by
    have h := Real.add_one_le_exp (-Real.log (1 + x))
    have he : Real.exp (-Real.log (1 + x)) = 1 / (1 + x) := by
      rw [Real.exp_neg, Real.exp_log hpos, one_div]
    rw [he] at h
    linarith
  rcases le_or_gt x 1 with hle | hgt
  · have h1 : min 1 x = x := min_eq_right hle
    have hrw : 2 * (1 - 1 / (1 + x)) = 2 * x / (1 + x) := by
      field_simp
      ring
    have h2 : x ≤ 2 * (1 - 1 / (1 + x)) := by
      rw [hrw, le_div_iff₀ hpos]
      nlinarith
    rw [h1]
    linarith
  · have h1 : min 1 x = 1 := min_eq_left (le_of_lt hgt)
    have h2 : Real.log 2 ≤ Real.log (1 + x) :=
      Real.log_le_log (by norm_num) (by linarith)
    rw [h1]
    linarith [half_le_log_two]

/-! ### Part 1: telescoping the log-determinant -/

lemma part_one {V₀ : Matrix (Fin d) (Fin d) ℝ} (hV₀ : V₀.PosDef) (a : ℕ → Fin d → ℝ) (n : ℕ) :
    ∑ t ∈ Finset.range n, min 1 (a (t + 1) ⬝ᵥ ((VM V₀ a t)⁻¹ *ᵥ a (t + 1)))
      ≤ 2 * Real.log ((VM V₀ a n).det / V₀.det) := by
  induction n with
  | zero =>
      rw [Finset.sum_range_zero, VM_zero, div_self (ne_of_gt hV₀.det_pos), Real.log_one]
      norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hWpos := VM_posDef hV₀ a n
      have hq := quad_nonneg hWpos (a (n + 1))
      have hd0 : 0 < (VM V₀ a n).det / V₀.det := div_pos hWpos.det_pos hV₀.det_pos
      have hstep : (VM V₀ a (n + 1)).det / V₀.det
          = ((VM V₀ a n).det / V₀.det) * (1 + a (n + 1) ⬝ᵥ ((VM V₀ a n)⁻¹ *ᵥ a (n + 1))) := by
        rw [det_VM_succ hV₀]
        ring
      rw [hstep, Real.log_mul (ne_of_gt hd0) (by linarith)]
      have hml := min_one_le_two_log hq
      linarith [ih]

/-! ### Part 2: AM-GM on the eigenvalues -/

lemma det_le_trace_pow {A : Matrix (Fin d) (Fin d) ℝ} (hd : 0 < d) (hA : A.PosDef) :
    A.det ≤ (A.trace / (d:ℝ)) ^ d := by
  classical
  have hherm : A.IsHermitian := hA.1
  set lam : Fin d → ℝ := hherm.eigenvalues with hlamdef
  have hlnn : ∀ i, 0 ≤ lam i := fun i => (hA.eigenvalues_pos i).le
  have hdet : A.det = ∏ i, lam i := by
    have h := hherm.det_eq_prod_eigenvalues
    simpa using h
  have htr : A.trace = ∑ i, lam i := by
    have h := hherm.trace_eq_sum_eigenvalues
    simpa using h
  have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
  have hw : ∑ _i : Fin d, ((1:ℝ)/(d:ℝ)) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hgm := Real.geom_mean_le_arith_mean_weighted Finset.univ (fun _ => (1:ℝ)/(d:ℝ)) lam
      (fun i _ => by positivity) hw (fun i _ => hlnn i)
  have hprod : (∏ i, lam i ^ ((1:ℝ)/(d:ℝ))) ^ d = ∏ i, lam i := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Real.rpow_natCast (lam i ^ ((1:ℝ)/(d:ℝ))) d, ← Real.rpow_mul (hlnn i),
      one_div, inv_mul_cancel₀ (ne_of_gt hdR), Real.rpow_one]
  have hnn : (0:ℝ) ≤ ∏ i, lam i ^ ((1:ℝ)/(d:ℝ)) :=
    Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hlnn i) _
  have hrhs : ∑ i, ((1:ℝ)/(d:ℝ)) * lam i = A.trace / (d:ℝ) := by
    rw [← Finset.mul_sum, ← htr]; ring
  calc A.det = (∏ i, lam i ^ ((1:ℝ)/(d:ℝ))) ^ d := by rw [hprod, hdet]
    _ ≤ (A.trace / (d:ℝ)) ^ d := by
        refine pow_le_pow_left₀ hnn ?_ d
        rw [← hrhs]
        exact hgm

lemma trace_VM (V₀ : Matrix (Fin d) (Fin d) ℝ) (a : ℕ → Fin d → ℝ) (n : ℕ) :
    (VM V₀ a n).trace = V₀.trace + ∑ s ∈ Finset.range n, (a (s + 1) ⬝ᵥ a (s + 1)) := by
  unfold VM
  rw [Matrix.trace_add, Matrix.trace_sum]
  congr 1

lemma part_two {V₀ : Matrix (Fin d) (Fin d) ℝ} (hd : 0 < d) (hV₀ : V₀.PosDef)
    {L : ℝ} (a : ℕ → Fin d → ℝ) (n : ℕ)
    (ha : ∀ t ∈ Finset.range n, Real.sqrt (a (t + 1) ⬝ᵥ a (t + 1)) ≤ L) :
    2 * Real.log ((VM V₀ a n).det / V₀.det)
      ≤ 2 * (d:ℝ) * Real.log
          ((V₀.trace + (n:ℝ) * L ^ 2) / ((d:ℝ) * V₀.det ^ ((1:ℝ)/(d:ℝ)))) := by
  have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
  have hWpos := VM_posDef hV₀ a n
  have hdet0 : (0:ℝ) < V₀.det := hV₀.det_pos
  have hdotnn : ∀ t : ℕ, 0 ≤ a (t + 1) ⬝ᵥ a (t + 1) := by
    intro t
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hL2 : ∀ t ∈ Finset.range n, a (t + 1) ⬝ᵥ a (t + 1) ≤ L ^ 2 := by
    intro t ht
    have h0 := hdotnn t
    have hs := ha t ht
    have hsq : Real.sqrt (a (t + 1) ⬝ᵥ a (t + 1)) ^ 2 = a (t + 1) ⬝ᵥ a (t + 1) :=
      Real.sq_sqrt h0
    nlinarith [Real.sqrt_nonneg (a (t + 1) ⬝ᵥ a (t + 1))]
  have htrle : (VM V₀ a n).trace ≤ V₀.trace + (n:ℝ) * L ^ 2 := by
    rw [trace_VM]
    have hsum : ∑ s ∈ Finset.range n, (a (s + 1) ⬝ᵥ a (s + 1))
        ≤ ∑ _s ∈ Finset.range n, L ^ 2 := Finset.sum_le_sum hL2
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
    linarith
  have htrnn : 0 ≤ (VM V₀ a n).trace := hWpos.posSemidef.trace_nonneg
  have hdetle : (VM V₀ a n).det ≤ ((V₀.trace + (n:ℝ) * L ^ 2) / (d:ℝ)) ^ d := by
    refine le_trans (det_le_trace_pow hd hWpos) ?_
    refine pow_le_pow_left₀ (div_nonneg htrnn hdR.le) ?_ d
    gcongr
  have hroot : (0:ℝ) < V₀.det ^ ((1:ℝ)/(d:ℝ)) := Real.rpow_pos_of_pos hdet0 _
  have hrootpow : (V₀.det ^ ((1:ℝ)/(d:ℝ))) ^ d = V₀.det := by
    rw [← Real.rpow_natCast (V₀.det ^ ((1:ℝ)/(d:ℝ))) d, ← Real.rpow_mul hdet0.le,
      one_div, inv_mul_cancel₀ (ne_of_gt hdR), Real.rpow_one]
  have hTpow : ((V₀.trace + (n:ℝ) * L ^ 2) / ((d:ℝ) * V₀.det ^ ((1:ℝ)/(d:ℝ)))) ^ d
      = ((V₀.trace + (n:ℝ) * L ^ 2) / (d:ℝ)) ^ d / V₀.det := by
    rw [div_pow, div_pow, mul_pow, hrootpow, div_div]
  have hratio : (VM V₀ a n).det / V₀.det
      ≤ ((V₀.trace + (n:ℝ) * L ^ 2) / ((d:ℝ) * V₀.det ^ ((1:ℝ)/(d:ℝ)))) ^ d := by
    rw [hTpow]
    gcongr
  have hlog : Real.log ((VM V₀ a n).det / V₀.det)
      ≤ Real.log (((V₀.trace + (n:ℝ) * L ^ 2) / ((d:ℝ) * V₀.det ^ ((1:ℝ)/(d:ℝ)))) ^ d) :=
    Real.log_le_log (div_pos hWpos.det_pos hdet0) hratio
  rw [Real.log_pow] at hlog
  linarith

end EPL

open Matrix in
theorem solution {d n : ℕ} (hd : 0 < d)
    {V₀ : Matrix (Fin d) (Fin d) ℝ} (hV₀ : V₀.PosDef)
    {L : ℝ} (a : ℕ → Fin d → ℝ)
    (ha : ∀ t ∈ Finset.range n, Real.sqrt (a (t + 1) ⬝ᵥ a (t + 1)) ≤ L) :
    ∑ t ∈ Finset.range n,
        min 1 (a (t + 1) ⬝ᵥ
          (V₀ + ∑ s ∈ Finset.range t,
            vecMulVec (a (s + 1)) (a (s + 1)))⁻¹ *ᵥ a (t + 1)) ≤
      2 * Real.log
        ((V₀ + ∑ s ∈ Finset.range n,
          vecMulVec (a (s + 1)) (a (s + 1))).det / V₀.det) ∧
    2 * Real.log
        ((V₀ + ∑ s ∈ Finset.range n,
          vecMulVec (a (s + 1)) (a (s + 1))).det / V₀.det) ≤
      2 * d * Real.log
        ((V₀.trace + n * L ^ 2) / (d * V₀.det ^ ((1 : ℝ) / d))) :=
  ⟨EPL.part_one hV₀ a n, EPL.part_two hd hV₀ a n ha⟩
