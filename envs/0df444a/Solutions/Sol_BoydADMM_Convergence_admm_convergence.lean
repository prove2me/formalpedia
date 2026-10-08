-- Prove2me | solution 1 for BoydADMM.Convergence.admm_convergence
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-07T12:33:06.560378+00:00
-- url     : https://prove2.me/submissions/fbbb6733-54cd-4144-9ae3-41b510519348

import Definitions.Def_BoydADMM_Convergence_Model
import Definitions.Def_ShorNonsmooth_Subdiff_Subdifferential
import Theorems.Thm_BoydADMM_Convergence_summed_bound
import Theorems.Thm_BoydADMM_Convergence_ineq_A1
import Theorems.Thm_BoydADMM_Convergence_ineq_A2
import Theorems.Thm_BoydADMM_Convergence_ineq_A3
open Filter
open scoped Topology
namespace BoydADMM.Convergence


end BoydADMM.Convergence
open BoydADMM.Convergence
/-- §3.2.1, p. 17, as proved in Appendix A (p. 106): under Assumptions 1 and 2, every ADMM
run satisfies residual convergence `r^k → 0`, objective convergence `f(x^k) + g(z^k) → p⋆`, and
dual residual convergence `s^k = ρAᵀB(z^k − z^{k−1}) → 0`. -/
theorem solution
  {n m p : ℕ} (P : Problem n m p) (hA1 : P.Assumption1) {ρ : ℝ} (hρ : 0 < ρ)
    {xs : EuclideanSpace ℝ (Fin n)} {zs : EuclideanSpace ℝ (Fin m)}
    {ys : EuclideanSpace ℝ (Fin p)} (hsp : P.IsSaddlePoint xs zs ys)
    {x : ℕ → EuclideanSpace ℝ (Fin n)} {z : ℕ → EuclideanSpace ℝ (Fin m)}
    {y : ℕ → EuclideanSpace ℝ (Fin p)} (hrun : P.IsADMMSeq ρ x z y) :
    Filter.Tendsto (fun k => P.resid (x k) (z k)) Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun k => P.f (x k) + P.g (z k)) Filter.atTop (nhds P.optVal) ∧
    Filter.Tendsto (fun k => P.dualResid ρ (z k) (z (k + 1))) Filter.atTop (nhds 0) := by
  obtain ⟨hbound,hr,hd⟩ := summed_bound P hA1 hρ hsp hrun
  let V : ℕ → ℝ := fun k => P.lyapunov ρ zs ys (z (k+1)) (y (k+1))
  have hV (k : ℕ) : 0 ≤ V k := by dsimp [V,Problem.lyapunov]; positivity
  have hVle (k : ℕ) : V k ≤ V 0 := by
    induction k with
    | zero => rfl
    | succ k ih =>
      have h := ineq_A1 P hA1 hρ hsp hrun k
      have hnon1 := mul_nonneg hρ.le (sq_nonneg ‖P.resid (x (k+2)) (z (k+2))‖)
      have hnon2 := mul_nonneg hρ.le (sq_nonneg ‖P.Bmul (z (k+2)-z (k+1))‖)
      change V (k+1) ≤ V k - _ - _ at h
      linarith
  let Cy := ρ * V 0 + 1 + ‖ys‖
  let Cz := V 0 / ρ + 1
  have hyb (k : ℕ) : ‖y (k+1)‖ ≤ Cy := by
    have hv := hVle k
    have hb : (1/ρ)*‖y (k+1)-ys‖^2 ≤ V 0 := by
      change (1/ρ)*‖y (k+1)-ys‖^2 + ρ*‖P.Bmul (z (k+1)-zs)‖^2 ≤ V 0 at hv
      have := mul_nonneg hρ.le (sq_nonneg ‖P.Bmul (z (k+1)-zs)‖)
      linarith
    have hb' : ‖y (k+1)-ys‖^2 ≤ ρ*V 0 := by
      have := mul_le_mul_of_nonneg_left hb hρ.le
      field_simp [ne_of_gt hρ] at this
      nlinarith
    have ht := norm_add_le (y (k+1)-ys) ys
    rw [sub_add_cancel] at ht
    dsimp [Cy]
    nlinarith [sq_nonneg (‖y (k+1)-ys‖-1/2)]
  have hzb (k : ℕ) : ‖P.Bmul (z (k+1)-zs)‖ ≤ Cz := by
    have hv := hVle k
    have hb : ρ*‖P.Bmul (z (k+1)-zs)‖^2 ≤ V 0 := by
      change (1/ρ)*‖y (k+1)-ys‖^2 + ρ*‖P.Bmul (z (k+1)-zs)‖^2 ≤ V 0 at hv
      have := mul_nonneg (one_div_nonneg.mpr hρ.le) (sq_nonneg ‖y (k+1)-ys‖)
      linarith
    have hb' : ‖P.Bmul (z (k+1)-zs)‖^2 ≤ V 0/ρ := by
      apply (le_div_iff₀ hρ).2
      simpa [mul_comm] using hb
    dsimp [Cz]
    nlinarith [sq_nonneg (‖P.Bmul (z (k+1)-zs)‖-1/2)]
  have hr1 : Tendsto (fun k => P.resid (x (k+1)) (z (k+1))) atTop (nhds 0) :=
    (tendsto_add_atTop_iff_nat 1).2 hr
  have hnr : Tendsto (fun k => ‖P.resid (x (k+1)) (z (k+1))‖) atTop (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.1 hr1
  have hnd : Tendsto (fun k => ‖P.Bmul (z (k+1)-z k)‖) atTop (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.1 hd
  have hlower : Tendsto (fun k => -‖ys‖*‖P.resid (x (k+1)) (z (k+1))‖) atTop (nhds 0) := by
    simpa using hnr.const_mul (-‖ys‖)
  have hupper : Tendsto (fun k => Cy*‖P.resid (x (k+1)) (z (k+1))‖ +
      ρ*‖P.Bmul (z (k+1)-z k)‖*(‖P.resid (x (k+1)) (z (k+1))‖+Cz)) atTop (nhds 0) := by
    simpa using (hnr.const_mul Cy).add ((hnd.const_mul ρ).mul (hnr.add_const Cz))
  have hobj : Tendsto (fun k => P.f (x (k+1))+P.g (z (k+1))-P.optVal) atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlower hupper
    · intro k
      have h := ineq_A3 P hA1 hρ hsp hrun k
      have hcs := real_inner_le_norm ys (P.resid (x (k+1)) (z (k+1)))
      linarith
    · intro k
      have h := ineq_A2 P hA1 hρ hsp hrun k
      have hcs1 := real_inner_le_norm (-(y (k+1))) (P.resid (x (k+1)) (z (k+1)))
      simp only [inner_neg_left,norm_neg] at hcs1
      have hy := mul_le_mul_of_nonneg_right (hyb k) (norm_nonneg (P.resid (x (k+1)) (z (k+1))))
      have hcs2 := real_inner_le_norm (-(P.Bmul (z (k+1)-z k)))
        (-P.resid (x (k+1)) (z (k+1)) + P.Bmul (z (k+1)-zs))
      simp only [inner_neg_left,norm_neg] at hcs2
      have hn := norm_add_le (-P.resid (x (k+1)) (z (k+1))) (P.Bmul (z (k+1)-zs))
      rw [norm_neg] at hn
      have ht : ‖-P.resid (x (k+1)) (z (k+1))+P.Bmul (z (k+1)-zs)‖ ≤
          ‖P.resid (x (k+1)) (z (k+1))‖+Cz := by linarith [hzb k]
      have hm := mul_le_mul_of_nonneg_left ht (norm_nonneg (P.Bmul (z (k+1)-z k)))
      have hmρ := mul_le_mul_of_nonneg_left (hcs2.trans hm) hρ.le
      nlinarith
  have ho : Tendsto (fun k => P.f (x k)+P.g (z k)) atTop (nhds P.optVal) := by
    apply (tendsto_add_atTop_iff_nat 1).1
    simpa using hobj.add_const P.optVal
  have hdual : Tendsto (fun k => P.dualResid ρ (z k) (z (k+1))) atTop (nhds 0) := by
    have hc := (Matrix.toEuclideanLin P.A.transpose).continuous_of_finiteDimensional.tendsto 0
    have ht := hc.comp hd
    simpa [Problem.dualResid,Problem.ATmul] using ht.const_smul ρ
  exact ⟨hr,ho,hdual⟩


