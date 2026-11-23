-- Prove2me | solution 1 for DedekindZeta.MellinPrinciple.reducedMellin_isBigO_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:24:31.967822+00:00
-- url     : https://prove2.me/submissions/a3764885-5bff-4920-9eaa-92f219fbaa28

import Mathlib
import Definitions.Def_DedekindZeta_MellinPrinciple

set_option autoImplicit true
open MeasureTheory Set Filter Asymptotics Topology Complex
open DedekindZeta DedekindZeta.MellinPrinciple
variable {f g : ℝ → ℂ} {a₀ b₀ C : ℂ} {k c α : ℝ}
namespace DedekindZeta.MellinPrinciple
theorem _root_.solution (h : IsMellinPair f g a₀ b₀ C k c α) :
    (fun y : ℝ => f y - a₀) =O[𝓝[>] (0 : ℝ)] (fun y : ℝ => y ^ (-k)) := by
  set l : Filter ℝ := 𝓝[>] (0 : ℝ) with hl
  -- `g(y) → b₀` at `+∞` (exponential decay to its constant term).
  have hatbot : Tendsto (fun y : ℝ => -c * y ^ α) atTop atBot :=
    (tendsto_rpow_atTop h.hα).const_mul_atTop_of_neg (by linarith [h.hc])
  have hexp0 : Tendsto (fun y : ℝ => Real.exp (-c * y ^ α)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hatbot
  have hgz : Tendsto (fun y : ℝ => g y - b₀) atTop (𝓝 0) :=
    h.hg_decay.trans_tendsto hexp0
  have hg_top : Tendsto g atTop (𝓝 b₀) := by
    rwa [tendsto_sub_nhds_zero_iff] at hgz
  -- hence `g(1/y) → b₀` as `y → 0⁺`, so `C·g(1/y)` is bounded there.
  have hg_inv : Tendsto (fun y : ℝ => g (1 / y)) l (𝓝 b₀) := by
    simp only [one_div]; exact hg_top.comp tendsto_inv_nhdsGT_zero
  have hbdd : (fun y : ℝ => C * g (1 / y)) =O[l] (fun _ : ℝ => (1 : ℝ)) :=
    (hg_inv.const_mul C).isBigO_one ℝ
  -- `↑(y^{-k}) =O y^{-k}` (norms agree under the real-to-complex coercion).
  have hcast : (fun y : ℝ => ((y ^ (-k) : ℝ) : ℂ)) =O[l] (fun y : ℝ => y ^ (-k)) :=
    Asymptotics.isBigO_of_le _ (fun y => by simp [Complex.norm_real])
  -- the bounded factor times `y^{-k}` is `O(y^{-k})`.
  have hA : (fun y : ℝ => C * ((y ^ (-k) : ℝ) : ℂ) * g (1 / y)) =O[l]
      (fun y : ℝ => y ^ (-k)) := by
    have hmul := hcast.mul hbdd
    refine hmul.congr' ?_ ?_
    · filter_upwards with y; ring
    · filter_upwards with y; ring
  -- the constant `a₀` is `O(y^{-k})` since `y^{-k} → +∞` as `y → 0⁺`.
  have ha0 : (fun _ : ℝ => a₀) =O[l] (fun y : ℝ => y ^ (-k)) := by
    have h1 : (fun _ : ℝ => (1 : ℝ)) =o[l] (fun y : ℝ => y ^ (-k)) := by
      rw [isLittleO_one_left_iff]
      simp only [Real.norm_eq_abs]
      exact tendsto_abs_atTop_atTop.comp (tendsto_rpow_neg_nhdsGT_zero (by linarith [h.hk]))
    exact (isBigO_const_const a₀ one_ne_zero _).trans h1.isBigO
  -- on `𝓝[>] 0`, `f y - a₀ = C·↑(y^{-k})·g(1/y) - a₀` by the inversion law.
  have hev : (fun y : ℝ => f y - a₀) =ᶠ[l]
      (fun y : ℝ => C * ((y ^ (-k) : ℝ) : ℂ) * g (1 / y) - a₀) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy0 : (0 : ℝ) < y := hy
    have hfe := h.hfe (1 / y) (by positivity)
    rw [one_div_one_div] at hfe
    have heq : ((1 / y) ^ k : ℝ) = y ^ (-k) := by
      rw [one_div, Real.inv_rpow hy0.le, ← Real.rpow_neg hy0.le]
    rw [hfe, heq]
  exact (hA.sub ha0).congr' hev.symm (Filter.EventuallyEq.rfl)
end DedekindZeta.MellinPrinciple
