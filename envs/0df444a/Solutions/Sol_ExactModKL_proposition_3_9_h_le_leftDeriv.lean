-- Prove2me | solution 1 for ExactModKL.proposition_3_9_h_le_leftDeriv
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:30:10.062094+00:00
-- url     : https://prove2.me/submissions/5809af70-b6fb-44a3-b20b-bdc80b589ebb

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexSplitting_Shared_StandingAssumptions
import Definitions.Def_ExactModKL_Ieta
import Definitions.Def_ExactModKL_leftDeriv
import Definitions.Def_ExactModKL_PhiClass
import Definitions.Def_ExactModKL_KLIneq
import Definitions.Def_ExactModKL_dist0
import Definitions.Def_ExactModKL_hfun
import Definitions.Def_ExactModKL_exactModulus
import Theorems.Thm_ExactModKL_lemma_3_1_ii

set_option autoImplicit false

open scoped ENNReal NNReal
open MeasureTheory Filter Topology ExactModKL NonconvexSplitting.Shared

theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (hf : IsProperFn f)
    (hlsc : LowerSemicontinuous f) (xbar : EuclideanSpace ℝ (Fin n))
    (hxbar : (LimitingSubdiff f xbar).Nonempty) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : U ∈ 𝓝 xbar) (η : ℝ≥0∞) (hη : 0 < η)
    (ϕ : ℝ → ℝ) (hconc : ConcaveOn ℝ (Ieta η) ϕ) (hϕ : PhiClass η ϕ)
    (hKL : KLIneq f xbar U η ϕ) :
    ∀ s : ℝ, 0 < s → ENNReal.ofReal s < η →
      hfun f xbar U η s ≤ ENNReal.ofReal (leftDeriv ϕ s) := by
  obtain ⟨hanti, hpos⟩ := ExactModKL.lemma_3_1_ii η hη ϕ hconc hϕ
  intro s hs0 hsη
  unfold hfun
  refine iSup₂_le fun x ⟨hxU, h0lt, hltη, hsle⟩ => ?_
  set d : EReal := f x - f xbar
  have hd_bot : d ≠ ⊥ := fun h => by
    rw [h] at hsle
    exact not_le_of_gt (EReal.bot_lt_coe s) hsle
  have hd_top : d ≠ ⊤ := (lt_of_lt_of_le hltη le_top).ne
  set t : ℝ := d.toReal
  have hdt : (t : EReal) = d := EReal.coe_toReal hd_top hd_bot
  have hst : s ≤ t := EReal.coe_le_coe_iff.mp (hdt.symm ▸ hsle)
  have ht0 : 0 < t := lt_of_lt_of_le hs0 hst
  have htη : ENNReal.ofReal t < η := by
    cases η using ENNReal.recTopCoe with
    | top => exact ENNReal.ofReal_lt_top
    | coe a =>
      have hcoe : (((a : ℝ≥0) : ℝ≥0∞) : EReal) = ((a : ℝ) : EReal) := by simp [ENNReal.toEReal]
      have hta : t < (a : ℝ) := EReal.coe_lt_coe_iff.mp (by rw [hdt]; exact hcoe ▸ hltη)
      rw [← ENNReal.ofReal_coe_nnreal]
      exact (ENNReal.ofReal_lt_ofReal_iff (lt_trans ht0 hta)).mpr hta
  have ht_deriv_pos : 0 < leftDeriv ϕ t := hpos t ht0 htη
  have hts_deriv : leftDeriv ϕ t ≤ leftDeriv ϕ s :=
    hanti ⟨hs0, hsη⟩ ⟨ht0, htη⟩ hst
  have hdist_le : (dist0 f x)⁻¹ ≤ ENNReal.ofReal (leftDeriv ϕ t) := by
    rw [ENNReal.inv_le_iff_inv_le, ← ENNReal.ofReal_inv_of_pos ht_deriv_pos]
    unfold dist0
    refine Metric.le_infEDist.mpr fun v hv => ?_
    have hkl := hKL x hxU h0lt hltη v hv
    have hv_ge : (leftDeriv ϕ t)⁻¹ ≤ ‖v‖ := by
      rw [inv_eq_one_div, div_le_iff₀ ht_deriv_pos, mul_comm]
      exact hkl
    rw [edist_dist, dist_zero_left]
    exact ENNReal.ofReal_le_ofReal hv_ge
  exact hdist_le.trans (ENNReal.ofReal_le_ofReal hts_deriv)
