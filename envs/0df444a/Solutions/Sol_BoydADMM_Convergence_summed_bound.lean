-- Prove2me | solution 1 for BoydADMM.Convergence.summed_bound
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-07T12:32:30.571198+00:00
-- url     : https://prove2.me/submissions/8016e693-aa6f-4aa6-8bc3-46e8100b508a

import Definitions.Def_BoydADMM_Convergence_Model
import Definitions.Def_ShorNonsmooth_Subdiff_Subdifferential
import Theorems.Thm_BoydADMM_Convergence_ineq_A1
open Filter
open scoped Topology
namespace BoydADMM.Convergence


end BoydADMM.Convergence
open BoydADMM.Convergence
/-- p. 107: iterating (A.1) gives
`ρ ∑_{k ≥ 1} (‖r^{k+1}‖₂² + ‖B(z^{k+1} − z^k)‖₂²) ≤ V^1` (every partial sum is bounded by
`V^1`), which implies `r^k → 0` and `B(z^{k+1} − z^k) → 0`. -/
theorem solution
  {n m p : ℕ} (P : Problem n m p) (hA1 : P.Assumption1) {ρ : ℝ} (hρ : 0 < ρ)
    {xs : EuclideanSpace ℝ (Fin n)} {zs : EuclideanSpace ℝ (Fin m)}
    {ys : EuclideanSpace ℝ (Fin p)} (hsp : P.IsSaddlePoint xs zs ys)
    {x : ℕ → EuclideanSpace ℝ (Fin n)} {z : ℕ → EuclideanSpace ℝ (Fin m)}
    {y : ℕ → EuclideanSpace ℝ (Fin p)} (hrun : P.IsADMMSeq ρ x z y) :
    (∀ N : ℕ, ρ * ∑ j ∈ Finset.range N,
        (‖P.resid (x (j + 2)) (z (j + 2))‖ ^ 2 + ‖P.Bmul (z (j + 2) - z (j + 1))‖ ^ 2) ≤
      P.lyapunov ρ zs ys (z 1) (y 1)) ∧
    Filter.Tendsto (fun k => P.resid (x k) (z k)) Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun k => P.Bmul (z (k + 1) - z k)) Filter.atTop (nhds 0) := by
  let V : ℕ → ℝ := fun k => P.lyapunov ρ zs ys (z (k+1)) (y (k+1))
  let q : ℕ → ℝ := fun k => ‖P.resid (x (k+2)) (z (k+2))‖^2 +
    ‖P.Bmul (z (k+2)-z (k+1))‖^2
  have hV (k : ℕ) : 0 ≤ V k := by
    dsimp [V,Problem.lyapunov]
    positivity
  have hq (k : ℕ) : 0 ≤ q k := by dsimp [q]; positivity
  have hstep (k : ℕ) : V (k+1) ≤ V k - ρ*q k := by
    have h := ineq_A1 P hA1 hρ hsp hrun k
    dsimp [V,q]
    linarith
  have htel (N : ℕ) : ρ * ∑ j ∈ Finset.range N, q j + V N ≤ V 0 := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have := hstep N
      nlinarith
  have hbound (N : ℕ) : ρ * ∑ j ∈ Finset.range N, q j ≤ V 0 := by
    linarith [htel N,hV N]
  have hsum : Summable q := summable_of_sum_range_le hq (c := V 0/ρ) (fun N => by
    apply (le_div_iff₀ hρ).2
    simpa [mul_comm] using hbound N)
  have ht := hsum.tendsto_atTop_zero
  have hr2 : Tendsto (fun k => ‖P.resid (x (k+2)) (z (k+2))‖^2) atTop (nhds 0) :=
    squeeze_zero (fun _ => sq_nonneg _) (fun k => by dsimp [q]; nlinarith [sq_nonneg ‖P.Bmul (z (k+2)-z (k+1))‖]) ht
  have hd2 : Tendsto (fun k => ‖P.Bmul (z (k+2)-z (k+1))‖^2) atTop (nhds 0) :=
    squeeze_zero (fun _ => sq_nonneg _) (fun k => by dsimp [q]; nlinarith [sq_nonneg ‖P.resid (x (k+2)) (z (k+2))‖]) ht
  have hr : Tendsto (fun k => P.resid (x (k+2)) (z (k+2))) atTop (nhds 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.2
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using Real.continuous_sqrt.continuousAt.tendsto.comp hr2
  have hd : Tendsto (fun k => P.Bmul (z (k+2)-z (k+1))) atTop (nhds 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.2
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using Real.continuous_sqrt.continuousAt.tendsto.comp hd2
  exact ⟨hbound, (tendsto_add_atTop_iff_nat 2).1 hr,
    (tendsto_add_atTop_iff_nat 1).1 hd⟩


