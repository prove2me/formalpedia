-- Prove2me | solution 1 for Formalism.GM.windowMeanAP_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:53:29.267649+00:00
-- url     : https://prove2.me/submissions/ff4469ca-bdf5-4849-a8f8-6ed53c60d1f6

import Definitions.Def_Formalism_MahlerMeasure_QuotientUpperBoundsOfPowerBounds
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_DeterminantBlockLeadingTerm
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WindowMeanAP
import Theorems.Thm_Formalism_GM_ProgressionMeanBounds_sumS
import Theorems.Thm_Formalism_GM_ProgressionMeanBounds_swap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open Finset Polynomial ProgressionMeanBounds
namespace Formalism.GM
theorem _root_.solution (hC : WindowCountAP) (hD : DiscsDisjointAP) : WindowMeanAP := by
  intro p _ K _ _ _ roots lam La₀ E n₀ del₀ t₀ d Y₀ h β hd hY hYp hE hcard hlam hj
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
  have hY0 : (0 : ℝ) < Y₀ := by exact_mod_cast hY
  have hsum : (∑ j ∈ range Y₀, (β (progr t₀ d j) : ℝ)) * E ≤
      ∑ j ∈ range Y₀, ((lam + (roots.map (fun ζ => vmin p h ((progr t₀ d j : K) - ζ))).sum) +
        E * ((roots.filter (fun ζ => ‖(progr t₀ d j : K) - ζ‖ ≤ (p : ℝ) ^ (-(h : ℤ)))).card : ℝ)) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum hj
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, card_range, nsmul_eq_mul,
    ← Finset.mul_sum, swap (range Y₀) roots (fun j ζ => vmin p h ((progr t₀ d j : K) - ζ))] at hsum
  have hV : (roots.map (fun ζ => ∑ j ∈ range Y₀, vmin p h ((progr t₀ d j : K) - ζ))).sum ≤
      (roots.card : ℝ) * ((Y₀ : ℝ) / ((p : ℝ) - 1) + h) := by
    calc _ ≤ (roots.map (fun _ => (Y₀ : ℝ) / ((p : ℝ) - 1) + h)).sum :=
          Multiset.sum_map_le_sum_map _ _
            (fun ζ _ => (hC p K ζ t₀ d Y₀ h hd).trans (sumS p hp2 Y₀ h))
      _ = _ := by rw [Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul]
  have hDD : (∑ j ∈ range Y₀,
      ((roots.filter (fun ζ => ‖(progr t₀ d j : K) - ζ‖ ≤ (p : ℝ) ^ (-(h : ℤ)))).card : ℝ)) ≤
      (roots.card : ℝ) := by
    have := hD p K roots t₀ d Y₀ h hd hYp
    exact_mod_cast this
  have hNc : (roots.card : ℝ) ≤ (del₀ : ℝ) * n₀ := by exact_mod_cast hcard
  have hN0 : (0 : ℝ) ≤ roots.card := Nat.cast_nonneg _
  have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg _
  have h1 : (Y₀ : ℝ) * lam + (roots.card : ℝ) * ((Y₀ : ℝ) / ((p : ℝ) - 1)) =
      (Y₀ : ℝ) * (lam + (roots.card : ℝ) / ((p : ℝ) - 1)) := by ring
  have h2 : (Y₀ : ℝ) * (lam + (roots.card : ℝ) / ((p : ℝ) - 1)) ≤ (Y₀ : ℝ) * ((n₀ : ℝ) * La₀) :=
    mul_le_mul_of_nonneg_left hlam hY0.le
  have h3 : (roots.card : ℝ) * h ≤ (del₀ : ℝ) * n₀ * h := mul_le_mul_of_nonneg_right hNc hh0
  have h4 : E * (roots.card : ℝ) ≤ E * ((del₀ : ℝ) * n₀) := mul_le_mul_of_nonneg_left hNc hE.le
  have h5 : E * (∑ j ∈ range Y₀,
      ((roots.filter (fun ζ => ‖(progr t₀ d j : K) - ζ‖ ≤ (p : ℝ) ^ (-(h : ℤ)))).card : ℝ)) ≤
      E * (roots.card : ℝ) := mul_le_mul_of_nonneg_left hDD hE.le
  have hS : (∑ j ∈ range Y₀, (β (progr t₀ d j) : ℝ)) * E ≤
      (Y₀ : ℝ) * ((n₀ : ℝ) * La₀) + (del₀ : ℝ) * n₀ * h + E * ((del₀ : ℝ) * n₀) := by
    nlinarith
  have eR : (n₀ : ℝ) * ((del₀ : ℝ) / Y₀ + (La₀ + (del₀ : ℝ) * h / Y₀) / E) * Y₀ * E =
      (Y₀ : ℝ) * ((n₀ : ℝ) * La₀) + (del₀ : ℝ) * n₀ * h + E * ((del₀ : ℝ) * n₀) := by
    field_simp
    ring
  rw [div_le_iff₀ hY0, ← mul_le_mul_iff_of_pos_right hE, eR]
  exact hS
end Formalism.GM
