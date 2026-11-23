-- Prove2me | solution 1 for Formalism.CorankShareLayerCake.FR.layer_cake_formula
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:48:11.364394+00:00
-- url     : https://prove2.me/submissions/cb240b6a-2b43-4163-b9c5-056dd8e37e25

import Mathlib
import Definitions.Def_Formalism_CorankShare_StatementFR
import Definitions.Def_Formalism_CorankShare_CorankShareProofs_LayerCakeFormula
import Theorems.Thm_Formalism_CorankShareLayerCake_FR_Pgsn2pfran_ind_anti
import Theorems.Thm_Formalism_CorankShareLayerCake_FR_Pgsn2pfran_ind_lb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.CorankShareLayerCake Formalism.CorankShareLayerCake.FR
open Finset MeasureTheory
open Pgsn2pfran
namespace Formalism.CorankShareLayerCake.FR
theorem _root_.solution : LayerCake := by
  unfold LayerCake
  intro D x a HH w hD hHH hx hw hcnt
  have hDpos : (0:ℝ) < D := by exact_mod_cast hD
  have hcount : ∀ τ : ℝ, ∑ j, (if τ < a - x j then (1:ℝ) else 0) =
      ((Finset.univ.filter fun j => x j < a - τ).card : ℝ) := by
    intro τ
    rw [Finset.sum_boole]
    have hf : (Finset.univ.filter fun j => τ < a - x j) =
        (Finset.univ.filter fun j => x j < a - τ) :=
      Finset.filter_congr (fun j _ => by constructor <;> intro hh <;> linarith)
    rw [hf]
  have hanti : Antitone (fun τ : ℝ => ∑ j, (if τ < a - x j then (1:ℝ) else 0)) :=
    fun t1 t2 ht => Finset.sum_le_sum fun j _ => ind_anti (a - x j) ht
  have hint : ∫ τ in (0:ℝ)..HH, ∑ j, (if τ < a - x j then (1:ℝ) else 0) =
      ∑ j, ∫ τ in (0:ℝ)..HH, (if τ < a - x j then (1:ℝ) else 0) :=
    intervalIntegral.integral_finset_sum fun j _ => (ind_anti (a - x j)).intervalIntegrable
  have hsum : ∑ j, (a - x j) ≤ ∑ j, ∫ τ in (0:ℝ)..HH, (if τ < a - x j then (1:ℝ) else 0) :=
    Finset.sum_le_sum fun j _ => ind_lb a (x j) HH (hx j) hHH
  have hL : ∑ j, (a - x j) = (D:ℝ) * a - ∑ j, x j := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hmono : ∫ τ in (0:ℝ)..HH, ∑ j, (if τ < a - x j then (1:ℝ) else 0) ≤
      ∫ τ in (0:ℝ)..HH, (D:ℝ) * min 1 (w τ) := by
    apply intervalIntegral.integral_mono_on hHH hanti.intervalIntegrable (hw.const_mul (D:ℝ))
    intro τ hτ
    show ∑ j, (if τ < a - x j then (1:ℝ) else 0) ≤ (D:ℝ) * min 1 (w τ)
    rw [hcount τ]
    have hc1 : (Finset.univ.filter fun j => x j < a - τ).card ≤ D := by
      calc _ ≤ (Finset.univ : Finset (Fin D)).card := Finset.card_filter_le _ _
        _ = D := by simp
    have hc1' : ((Finset.univ.filter fun j => x j < a - τ).card : ℝ) ≤ D := by
      exact_mod_cast hc1
    have hc2 := hcnt τ hτ
    rcases le_total 1 (w τ) with hw1 | hw1
    · rw [min_eq_left hw1]
      linarith
    · rw [min_eq_right hw1]
      linarith
  rw [intervalIntegral.integral_const_mul] at hmono
  rw [le_div_iff₀ hDpos]
  linarith
end Formalism.CorankShareLayerCake.FR
