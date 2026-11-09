-- Prove2me | solution 1 for ExactModKL.proposition_3_9_h_antitone
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T11:04:51.163444+00:00
-- url     : https://prove2.me/submissions/f983d372-73b3-4fba-9021-c0b02fdcb614

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

open scoped ENNReal
open MeasureTheory Filter Topology

open ExactModKL NonconvexSplitting.Shared in
theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (hf : IsProperFn f)
    (hlsc : LowerSemicontinuous f) (xbar : EuclideanSpace ℝ (Fin n))
    (hxbar : (LimitingSubdiff f xbar).Nonempty) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : U ∈ 𝓝 xbar) (η : ℝ≥0∞) (hη : 0 < η) :
    AntitoneOn (hfun f xbar U η) {s | 0 < s ∧ ENNReal.ofReal s < η} ∧
      ∀ s : ℝ, 0 < s → ENNReal.ofReal s < η →
        (∃ x ∈ U, (LimitingSubdiff f x).Nonempty ∧ (s : EReal) ≤ f x - f xbar ∧
          f x - f xbar < (η : EReal)) →
        0 < hfun f xbar U η s := by
  refine ⟨?_, ?_⟩
  · intro s _ s' _ hss'
    unfold hfun
    refine iSup₂_le fun x hx => ?_
    have hle : (s : EReal) ≤ (s' : EReal) := by exact_mod_cast hss'
    exact le_iSup₂_of_le (f := fun (x : EuclideanSpace ℝ (Fin n))
      (_ : x ∈ U ∧ 0 < f x - f xbar ∧ f x - f xbar < (η : EReal) ∧ (s : EReal) ≤ f x - f xbar) =>
        (dist0 f x)⁻¹) x ⟨hx.1, hx.2.1, hx.2.2.1, le_trans hle hx.2.2.2⟩ le_rfl
  · rintro s hs _ ⟨x, hxU, ⟨v, hv⟩, hsx, hxη⟩
    have hpos : (0 : EReal) < f x - f xbar := lt_of_lt_of_le (EReal.coe_pos.mpr hs) hsx
    have hd : dist0 f x ≠ ∞ := by
      unfold dist0
      exact ne_top_of_le_ne_top (edist_ne_top _ _) (Metric.infEDist_le_edist_of_mem hv)
    have h1 : 0 < (dist0 f x)⁻¹ := ENNReal.inv_pos.mpr hd
    unfold hfun
    exact lt_of_lt_of_le h1 (le_iSup₂_of_le (f := fun (x : EuclideanSpace ℝ (Fin n))
      (_ : x ∈ U ∧ 0 < f x - f xbar ∧ f x - f xbar < (η : EReal) ∧ (s : EReal) ≤ f x - f xbar) =>
        (dist0 f x)⁻¹) x ⟨hxU, hpos, hxη, hsx⟩ le_rfl)
