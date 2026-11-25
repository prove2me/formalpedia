-- Prove2me | solution 1 for Formalism.FN.LowerVolumeBound.cross_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:30:31.060187+00:00
-- url     : https://prove2.me/submissions/39a2e23a-7c52-4794-b2a8-e12f1e8451ff

import Definitions.Def_Formalism_SuccessiveMinima_DefsMink
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_MinkowskiIILowerOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module Metric Set ZSpan
open scoped Pointwise ENNReal
noncomputable section
open Formalism Formalism.FN Formalism.FN.LowerVolumeBound
namespace Formalism.FN.LowerVolumeBound
theorem _root_.solution {E : Type*} [AddCommGroup E] [Module ℝ E] {K : Set E} (hK : Convex ℝ K)
    (hs : ∀ x ∈ K, -x ∈ K) (h0 : (0 : E) ∈ K) {n : ℕ} (w : Fin n → E) (hw : ∀ i, w i ∈ K)
    (c : Fin n → ℝ) (hc : ∑ i, |c i| ≤ 1) : ∑ i, c i • w i ∈ K := by
  classical
  set s := ∑ i, |c i| with hsdef
  let p : Fin n → E := fun i => if 0 ≤ c i then w i else -w i
  have hp : ∀ i, p i ∈ K := fun i => by
    dsimp only [p]; split_ifs
    · exact hw i
    · exact hs _ (hw i)
  have hcp : ∀ i, c i • w i = |c i| • p i := fun i => by
    dsimp only [p]; split_ifs with h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg (not_le.mp h), neg_smul, smul_neg, neg_neg]
  have hs_nonneg : 0 ≤ s := Finset.sum_nonneg (fun i _ => abs_nonneg (c i))
  rcases hs_nonneg.eq_or_lt with hs0 | hs0
  · have hz : ∀ i, c i = 0 := fun i => abs_eq_zero.mp (le_antisymm
      ((Finset.single_le_sum (fun j _ => abs_nonneg (c j)) (Finset.mem_univ i)).trans hs0.symm.le)
      (abs_nonneg _))
    simpa [hz] using h0
  · have hx : ∑ i, (|c i| / s) • p i ∈ K :=
      hK.sum_mem (fun i _ => div_nonneg (abs_nonneg _) hs0.le)
        (by rw [← Finset.sum_div, div_self hs0.ne']) (fun i _ => hp i)
    have h2 := hK.smul_mem_of_zero_mem h0 hx ⟨hs0.le, hc⟩
    convert h2 using 1
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, mul_div_cancel₀ _ hs0.ne', hcp]
end Formalism.FN.LowerVolumeBound
