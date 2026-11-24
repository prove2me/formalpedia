-- Prove2me | solution 1 for Formalism.MainNotions.LeviCoordinates.pj_dens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:29:53.21511+00:00
-- url     : https://prove2.me/submissions/07c51c54-8ae3-47b5-a2a7-9ab22fc7b7f5

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_PjDensUpper
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_pj_dens_real
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_pj_dens_upper

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.LeviCoordinates
open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal
variable {G : Type} [MeasurableSpace G] (μ : Measure G) {Hs : Type} [NormedAddCommGroup Hs]
  [InnerProductSpace ℂ Hs] (σ : G → (Hs →L[ℂ] Hs))
namespace Formalism.MainNotions.LeviCoordinates
theorem _root_.solution (_hU : ∀ g x, ‖σ g x‖ = ‖x‖)
    (hm : ∀ x y : Hs, AEStronglyMeasurable (fun g => ⟪y, σ g x⟫_ℂ) μ)
    (V : Submodule ℂ Hs) (hV : Dense (V : Set Hs)) (d : ℝ) (hd : 0 < d)
    (h : ∀ x ∈ V, ∀ y ∈ V, Integrable (fun g => ‖⟪y, σ g x⟫_ℂ‖ ^ 2) μ ∧
      ∫ g, ‖⟪y, σ g x⟫_ℂ‖ ^ 2 ∂μ = ‖x‖ ^ 2 * ‖y‖ ^ 2 / d) :
    ∀ x y : Hs, Integrable (fun g => ‖⟪y, σ g x⟫_ℂ‖ ^ 2) μ ∧
      ∫ g, ‖⟪y, σ g x⟫_ℂ‖ ^ 2 ∂μ = ‖x‖ ^ 2 * ‖y‖ ^ 2 / d := by
  intro x y
  have up := pj_dens_upper μ σ hm V hV d h hd
  refine ⟨(up x y).1, le_antisymm (up x y).2 ?_⟩
  obtain ⟨u, hu, hux⟩ := mem_closure_iff_seq_limit.1 (hV x)
  obtain ⟨v, hv, hvy⟩ := mem_closure_iff_seq_limit.1 (hV y)
  set N : ℝ := ∫ g, ‖⟪y, σ g x⟫_ℂ‖ ^ 2 ∂μ with hN
  have hN0 : 0 ≤ N := integral_nonneg fun g => by positivity
  have key : ∀ t : ℝ, 0 < t → ‖x‖ ^ 2 * ‖y‖ ^ 2 / d ≤ (1 + t) * N := by
    intro t ht
    have hn : ∀ n, ‖u n‖ ^ 2 * ‖v n‖ ^ 2 / d ≤ (1 + t) * N +
        (1 + 1 / t) * (2 * (‖u n - x‖ ^ 2 * ‖v n‖ ^ 2 / d) + 2 * (‖x‖ ^ 2 * ‖v n - y‖ ^ 2 / d)) := by
      intro n
      have i0 := (up x y).1
      have i1 := (up (u n - x) (v n)).1
      have i2 := (up x (v n - y)).1
      have hle : ∫ g, ‖⟪v n, σ g (u n)⟫_ℂ‖ ^ 2 ∂μ ≤
          ∫ g, ((1 + t) * ‖⟪y, σ g x⟫_ℂ‖ ^ 2 + (1 + 1 / t) *
            (2 * ‖⟪v n, σ g (u n - x)⟫_ℂ‖ ^ 2 + 2 * ‖⟪v n - y, σ g x⟫_ℂ‖ ^ 2)) ∂μ := by
        refine integral_mono (h _ (hu n) _ (hv n)).1
          ((i0.const_mul _).add (((i1.const_mul 2).add (i2.const_mul 2)).const_mul _)) fun g => ?_
        have hsum : ⟪v n, σ g (u n)⟫_ℂ = ⟪y, σ g x⟫_ℂ + ⟪v n, σ g (u n - x)⟫_ℂ + ⟪v n - y, σ g x⟫_ℂ := by
          rw [map_sub, inner_sub_right, inner_sub_left]
          ring
        have h1 : ‖⟪v n, σ g (u n)⟫_ℂ‖ ≤ ‖⟪y, σ g x⟫_ℂ‖ + ‖⟪v n, σ g (u n - x)⟫_ℂ‖ + ‖⟪v n - y, σ g x⟫_ℂ‖ := by
          rw [hsum]
          exact norm_add₃_le
        exact le_trans (pow_le_pow_left₀ (norm_nonneg _) h1 2) (pj_dens_real t _ _ _ ht)
      have heq : ∫ g, ((1 + t) * ‖⟪y, σ g x⟫_ℂ‖ ^ 2 + (1 + 1 / t) *
            (2 * ‖⟪v n, σ g (u n - x)⟫_ℂ‖ ^ 2 + 2 * ‖⟪v n - y, σ g x⟫_ℂ‖ ^ 2)) ∂μ =
          (1 + t) * N + (1 + 1 / t) * (2 * (∫ g, ‖⟪v n, σ g (u n - x)⟫_ℂ‖ ^ 2 ∂μ) +
            2 * ∫ g, ‖⟪v n - y, σ g x⟫_ℂ‖ ^ 2 ∂μ) := by
        have i12 : Integrable (fun g => 2 * ‖⟪v n, σ g (u n - x)⟫_ℂ‖ ^ 2 + 2 * ‖⟪v n - y, σ g x⟫_ℂ‖ ^ 2) μ :=
          (i1.const_mul 2).add (i2.const_mul 2)
        have i3 : Integrable (fun g => (1 + 1 / t) *
            (2 * ‖⟪v n, σ g (u n - x)⟫_ℂ‖ ^ 2 + 2 * ‖⟪v n - y, σ g x⟫_ℂ‖ ^ 2)) μ := i12.const_mul _
        rw [integral_add (i0.const_mul (1 + t)) i3, integral_const_mul, integral_const_mul,
          integral_add (i1.const_mul 2) (i2.const_mul 2), integral_const_mul, integral_const_mul]
      rw [(h _ (hu n) _ (hv n)).2, heq] at hle
      have b1 := (up (u n - x) (v n)).2
      have b2 := (up x (v n - y)).2
      have hpos : 0 ≤ 1 + 1 / t := by positivity
      have : (1 + 1 / t) * (2 * (∫ g, ‖⟪v n, σ g (u n - x)⟫_ℂ‖ ^ 2 ∂μ) + 2 * ∫ g, ‖⟪v n - y, σ g x⟫_ℂ‖ ^ 2 ∂μ) ≤
          (1 + 1 / t) * (2 * (‖u n - x‖ ^ 2 * ‖v n‖ ^ 2 / d) + 2 * (‖x‖ ^ 2 * ‖v n - y‖ ^ 2 / d)) :=
        mul_le_mul_of_nonneg_left (by linarith) hpos
      linarith
    have h0x : Tendsto (fun n => ‖u n - x‖) atTop (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.1 hux
    have h0y : Tendsto (fun n => ‖v n - y‖) atTop (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.1 hvy
    have hL : Tendsto (fun n => ‖u n‖ ^ 2 * ‖v n‖ ^ 2 / d) atTop (𝓝 (‖x‖ ^ 2 * ‖y‖ ^ 2 / d)) :=
      ((hux.norm.pow 2).mul (hvy.norm.pow 2)).div_const d
    have a1 := ((h0x.pow 2).mul (hvy.norm.pow 2)).div_const d
    have a2 := ((tendsto_const_nhds (x := ‖x‖ ^ 2) (f := atTop (α := ℕ))).mul (h0y.pow 2)).div_const d
    have hR : Tendsto (fun n => (1 + t) * N +
        (1 + 1 / t) * (2 * (‖u n - x‖ ^ 2 * ‖v n‖ ^ 2 / d) + 2 * (‖x‖ ^ 2 * ‖v n - y‖ ^ 2 / d))) atTop
        (𝓝 ((1 + t) * N + (1 + 1 / t) * (2 * ((0 : ℝ) ^ 2 * ‖y‖ ^ 2 / d) + 2 * (‖x‖ ^ 2 * (0 : ℝ) ^ 2 / d)))) :=
      tendsto_const_nhds.add (((a1.const_mul 2).add (a2.const_mul 2)).const_mul _)
    have hfin := le_of_tendsto_of_tendsto' hL hR hn
    simpa using hfin
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have h1 := key (ε / (N + 1)) (by positivity)
  have h2 : ε / (N + 1) * N ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  nlinarith
end Formalism.MainNotions.LeviCoordinates
