-- Prove2me | solution 1 for Formalism.GM.MeanGammaLemmas.lead_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:48:51.962803+00:00
-- url     : https://prove2.me/submissions/5ab3ba1f-70b6-4e9a-8d80-025e284d3153

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Definitions.Def_Formalism_MahlerMeasure_LegendreDigits
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_MeanGam
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.QuotientRingDecomposition.E_apply
attribute [local simp] Formalism.GM.QuotientRingDecomposition.divQ_apply



set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.MeanGammaLemmas
open Polynomial Finset Formalism.GM.M
namespace Formalism.GM.MeanGammaLemmas
theorem _root_.solution (p : ℕ) [hp : Fact p.Prime] {n : ℕ} (β : Fin n → ℝ) (dgs : Fin n → ℕ) (κ La Lnorm : ℝ)
    (hβ : ∀ b, 0 < β b) (hprod : ∏ b, (β b * (p : ℝ) ^ (-κ)) ≤ Lnorm)
    (hrow : ∀ b, -Real.logb p (β b) + (dgs b : ℝ) / ((p : ℝ) - 1) + κ ≤ La) :
    -Real.logb p Lnorm + ((∑ b, dgs b : ℕ) : ℝ) / ((p : ℝ) - 1) ≤ n * La := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hpos : 0 < ∏ b, (β b * (p : ℝ) ^ (-κ)) :=
    Finset.prod_pos (fun b _ => mul_pos (hβ b) (Real.rpow_pos_of_pos hp0 _))
  have h1 : Real.logb p (∏ b, (β b * (p : ℝ) ^ (-κ))) ≤ Real.logb p Lnorm :=
    Real.logb_le_logb_of_le hp1 hpos hprod
  have hlogp : 0 < Real.log p := Real.log_pos hp1
  have h2 : Real.logb p (∏ b, (β b * (p : ℝ) ^ (-κ))) = ∑ b, (Real.logb p (β b) - κ) := by
    simp only [Real.logb]
    rw [Real.log_prod (fun b _ => (mul_pos (hβ b) (Real.rpow_pos_of_pos hp0 _)).ne'), Finset.sum_div]
    apply Finset.sum_congr rfl
    intro b _
    rw [Real.log_mul (hβ b).ne' (Real.rpow_pos_of_pos hp0 _).ne', Real.log_rpow hp0, add_div,
      mul_div_assoc, div_self hlogp.ne']
    ring
  have h3 : ∑ b, (-Real.logb p (β b) + (dgs b : ℝ) / ((p : ℝ) - 1) + κ) ≤ n * La := by
    calc _ ≤ ∑ _b : Fin n, La := Finset.sum_le_sum (fun b _ => hrow b)
      _ = n * La := by simp
  have h4 : ∑ b, (-Real.logb p (β b) + (dgs b : ℝ) / ((p : ℝ) - 1) + κ) =
      -(∑ b, (Real.logb p (β b) - κ)) + ((∑ b, dgs b : ℕ) : ℝ) / ((p : ℝ) - 1) := by
    rw [Nat.cast_sum, Finset.sum_div, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _
    ring
  linarith
end Formalism.GM.MeanGammaLemmas
