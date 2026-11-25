-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.deuring_heilbronn_cauchy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:48:57.726003+00:00
-- url     : https://prove2.me/submissions/f3526fd8-ace4-40dc-9b36-b91a7664d99e

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHSt
import Definitions.Def_Formalism_LandauZeroFreeBounds_SiegelWalfiszAPOfSiegelLower
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHCauchy
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_dhc_removable
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_dhc_iter
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_dhc_cauchy
import Theorems.Thm_Formalism_ZeroFreeDirichlet_landau_local3


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Classical Filter Topology
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution : DHCauchy := by
  intro f z₀ r B hr hB hfd hf0 hfb
  obtain ⟨Z, m, hZ, hm1, -, -, hsum, hbd⟩ := landau_local3 f z₀ r B hr hB hfd hf0 hfb
  refine ⟨Z, m, hZ, hm1, hsum, ?_⟩
  have hfan : ∀ z ∈ Metric.ball z₀ (r / 6), AnalyticAt ℂ f z := fun z hz =>
    (hfd.mono Metric.ball_subset_closedBall).analyticAt
      (Metric.isOpen_ball.mem_nhds (Metric.ball_subset_ball (by linarith) hz))
  have hnz : ∀ z ∈ Metric.ball z₀ (r / 6) \ (Z : Set ℂ), f z ≠ 0 := fun z hz h0 =>
    hz.2 (Finset.mem_coe.2 ((hZ z).2
      ⟨Metric.closedBall_subset_closedBall (by linarith) (Metric.ball_subset_closedBall hz.1), h0⟩))
  have hGd : DifferentiableOn ℂ (fun z => deriv f z / f z - ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ))
      (Metric.ball z₀ (r / 6) \ (Z : Set ℂ)) := by
    intro z hz
    have h1 := hfan z hz.1
    refine DifferentiableAt.differentiableWithinAt ?_
    refine (h1.deriv.differentiableAt.div h1.differentiableAt (hnz z hz)).sub ?_
    refine DifferentiableAt.fun_sum (fun ρ hρ => ?_)
    exact (differentiableAt_const _).div (differentiableAt_id.sub_const ρ)
      (sub_ne_zero.2 (fun h => hz.2 (h ▸ Finset.mem_coe.2 hρ)))
  obtain ⟨H, hHd, hHe, hHb⟩ := dhc_removable Z _ _ (72 * Real.log B / r) Metric.isOpen_ball hGd
    (fun z hz => hbd z (Metric.ball_subset_closedBall hz.1) (hnz z hz))
  intro k s hs hfs
  have hsZ : s ∉ (Z : Set ℂ) := fun h => hfs ((hZ s).1 (Finset.mem_coe.1 h)).2
  have hsU : s ∈ Metric.ball z₀ (r / 6) := by
    rw [Metric.mem_closedBall] at hs
    rw [Metric.mem_ball]
    linarith
  have hev : (fun z => -(deriv f z / f z)) =ᶠ[𝓝 s]
      fun z => -(∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ)) - H z := by
    have hn : Metric.ball z₀ (r / 6) \ (Z : Set ℂ) ∈ 𝓝 s :=
      (Metric.isOpen_ball.sdiff Z.finite_toSet.isClosed).mem_nhds ⟨hsU, hsZ⟩
    filter_upwards [hn] with z hz
    rw [hHe z hz]
    ring
  have hHan : AnalyticAt ℂ H s := hHd.analyticAt (Metric.isOpen_ball.mem_nhds hsU)
  have hcd : ∀ ρ ∈ Z, ContDiffAt ℂ k (fun z => (m ρ : ℂ) / (z - ρ)) s := fun ρ hρ =>
    contDiffAt_const.div (contDiffAt_id.sub contDiffAt_const)
      (sub_ne_zero.2 (fun h => hsZ (h ▸ Finset.mem_coe.2 hρ)))
  have hkey : ‖iteratedDeriv k H s‖ ≤ k.factorial * (72 * Real.log B / r) / (r / 12) ^ k := by
    have h2 : 2 * (r / 12) = r / 6 := by ring
    exact dhc_cauchy H z₀ s (r / 12) _ (by positivity) (h2 ▸ hHd) (h2 ▸ hHb) hs k
  have hfac : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have hpm : ((-1 : ℂ) ^ k * (-1) ^ k) = 1 := by rw [← mul_pow]; simp
  rw [hev.iteratedDeriv_eq k, iteratedDeriv_fun_sub (ContDiffAt.neg (ContDiffAt.sum hcd)) hHan.contDiffAt,
    iteratedDeriv_fun_neg, iteratedDeriv_fun_sum hcd]
  simp_rw [dhc_iter]
  have he : (-1 : ℂ) ^ k / (k.factorial : ℂ) *
        (-∑ ρ ∈ Z, (m ρ : ℂ) * ((-1) ^ k * (k.factorial : ℂ)) * ((s - ρ) ^ (k + 1))⁻¹ -
          iteratedDeriv k H s) + ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) ^ (k + 1) =
      -((-1 : ℂ) ^ k / (k.factorial : ℂ) * iteratedDeriv k H s) := by
    have : ∑ ρ ∈ Z, (m ρ : ℂ) * ((-1) ^ k * (k.factorial : ℂ)) * ((s - ρ) ^ (k + 1))⁻¹ =
        ((-1) ^ k * (k.factorial : ℂ)) * ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) ^ (k + 1) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun ρ _ => ?_)
      rw [div_eq_mul_inv]
      ring
    rw [this]
    generalize (∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) ^ (k + 1)) = S
    field_simp
    linear_combination (-(k.factorial : ℂ) * S) * hpm
  rw [he, norm_neg, norm_mul, norm_div, norm_pow, norm_neg, norm_one, one_pow, Complex.norm_natCast]
  have hfr : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  calc 1 / (k.factorial : ℝ) * ‖iteratedDeriv k H s‖
      ≤ 1 / (k.factorial : ℝ) * (k.factorial * (72 * Real.log B / r) / (r / 12) ^ k) := by gcongr
    _ = 72 * Real.log B / r * (12 / r) ^ k := by
      rw [div_pow, div_pow]
      field_simp
end Formalism.HermitianLattices.Ext.PrimesInProgressions
