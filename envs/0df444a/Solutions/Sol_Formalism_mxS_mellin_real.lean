-- Prove2me | solution 1 for Formalism.mxS_mellin_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:46:35.121709+00:00
-- url     : https://prove2.me/submissions/9c3b549e-67c3-449d-9fc7-a8cefedb086f

import Definitions.Def_Formalism_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSAux
import Theorems.Thm_Formalism_mxS_eq_indicator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Formalism
namespace Formalism
theorem _root_.solution {n : ℕ} (hn : 1 ≤ n) {σ : ℝ} (hσ : 1 < σ) :
    IntegrableOn (fun x : ℝ => mxS n x * x ^ (-σ - 1)) (Ioi 1) ∧
    ∫ x in Ioi (1 : ℝ), mxS n x * x ^ (-σ - 1) = (n : ℝ) ^ (-σ) / (σ * (σ - 1)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsub : Ioi (n : ℝ) ⊆ Ioi 1 := Ioi_subset_Ioi hn1
  have ha : -σ < -1 := by linarith
  have hb : -σ - 1 < -1 := by linarith
  have hσ0 : σ ≠ 0 := (by linarith : (0 : ℝ) < σ).ne'
  have hσ1 : σ - 1 ≠ 0 := (by linarith : (0 : ℝ) < σ - 1).ne'
  have hσ2 : -σ + 1 ≠ 0 := (by linarith : -σ + 1 < 0).ne
  have hnR : (n : ℝ) ≠ 0 := hn0.ne'

  have hfun : (fun x : ℝ => mxS n x * x ^ (-σ - 1)) =
      (Ioi (n : ℝ)).indicator (fun x : ℝ => (x / n - 1) * x ^ (-σ - 1)) := by
    funext x
    rw [mxS_eq_indicator hn x]
    by_cases hx : x ∈ Ioi (n : ℝ)
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]
  have heq : EqOn (fun x : ℝ => (x / n - 1) * x ^ (-σ - 1))
      (fun x : ℝ => 1 / (n : ℝ) * x ^ (-σ) - x ^ (-σ - 1)) (Ioi (n : ℝ)) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_trans hn0 (Set.mem_Ioi.mp hx)
    have hpow : x ^ (-σ) = x ^ (-σ - 1) * x := by
      calc x ^ (-σ) = x ^ ((-σ - 1) + 1) := by rw [sub_add_cancel]
        _ = x ^ (-σ - 1) * x := by rw [Real.rpow_add hx0, Real.rpow_one]
    show (x / n - 1) * x ^ (-σ - 1) = 1 / (n : ℝ) * x ^ (-σ) - x ^ (-σ - 1)
    rw [hpow]
    ring
  have hA : Integrable (fun x : ℝ => 1 / (n : ℝ) * x ^ (-σ)) (volume.restrict (Ioi (n : ℝ))) :=
    Integrable.const_mul (integrableOn_Ioi_rpow_of_lt ha hn0) (1 / (n : ℝ))
  have hB : Integrable (fun x : ℝ => x ^ (-σ - 1)) (volume.restrict (Ioi (n : ℝ))) :=
    integrableOn_Ioi_rpow_of_lt hb hn0
  have hint : IntegrableOn (fun x : ℝ => 1 / (n : ℝ) * x ^ (-σ) - x ^ (-σ - 1))
      (Ioi (n : ℝ)) := hA.sub hB
  have hg := hint.congr_fun heq.symm measurableSet_Ioi
  rw [hfun]
  refine ⟨((integrable_indicator_iff measurableSet_Ioi).mpr hg).integrableOn, ?_⟩
  rw [setIntegral_indicator measurableSet_Ioi, inter_eq_right.mpr hsub,
    setIntegral_congr_fun measurableSet_Ioi heq, integral_sub hA hB, integral_const_mul,
    integral_Ioi_rpow_of_lt ha hn0, integral_Ioi_rpow_of_lt hb hn0, sub_add_cancel,
    Real.rpow_add hn0, Real.rpow_one]
  field_simp
  ring
end Formalism
