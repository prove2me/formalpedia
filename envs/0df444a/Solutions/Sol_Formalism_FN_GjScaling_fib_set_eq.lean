-- Prove2me | solution 1 for Formalism.FN.GjScaling.fib_set_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:48.816869+00:00
-- url     : https://prove2.me/submissions/c414e306-2d3d-4df0-886b-508d5a5096ef

import Definitions.Def_Formalism_SuccessiveMinima_DefsMink
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_GjScale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module Metric Set
open scoped Pointwise ENNReal
noncomputable section
open Formalism Formalism.FN
open Formalism.FN.GjScaling
variable {ι : Type*} [Fintype ι]
variable (n j : ℕ)
namespace Formalism.FN.GjScaling
theorem _root_.solution (A : Set (Fin n → ℝ)) (y : {i : Fin n // ¬ (i : ℕ) < j} → ℝ) :
    {u | emb n j u y ∈ boxJ n j ∩ (A + latJ n j)} = Qv _ ∩ (fib n j A y + Zv _) := by
  ext u
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
  constructor
  · rintro ⟨hbox, a, ha, k, hk, hak⟩
    refine ⟨fun i => ?_, fun i => a i, ?_, fun i => k i, fun i => hk.1 i, ?_⟩
    · simpa only [emb, dif_pos i.2, Subtype.coe_eta] using hbox i.1 i.2
    · show emb n j (fun i => a i) y ∈ A
      convert ha using 1
      funext i
      by_cases hi : (i : ℕ) < j
      · simp only [emb, dif_pos hi]
      · have h := congrFun hak i
        simp only [emb, dif_neg hi, Pi.add_apply, hk.2 i (not_lt.mp hi), add_zero] at h
        simp only [emb, dif_neg hi, h]
    · funext i
      have h := congrFun hak i.1
      simp only [emb, dif_pos i.2, Pi.add_apply, Subtype.coe_eta] at h
      simpa only [Pi.add_apply] using h
  · rintro ⟨hcube, v, hv, w, hw, rfl⟩
    refine ⟨fun i hi => ?_, emb n j v y, hv, emb n j w 0,
      ⟨fun i => ?_, fun i hi => ?_⟩, ?_⟩
    · simp only [emb, dif_pos hi]
      exact hcube ⟨i, hi⟩
    · by_cases hi : (i : ℕ) < j
      · simp only [emb, dif_pos hi]
        exact hw ⟨i, hi⟩
      · exact ⟨0, by simp only [emb, dif_neg hi, Pi.zero_apply, Int.cast_zero]⟩
    · simp only [emb, dif_neg (not_lt.mpr hi), Pi.zero_apply]
    · funext i
      by_cases hi : (i : ℕ) < j
      · simp only [emb, dif_pos hi, Pi.add_apply]
      · simp only [emb, dif_neg hi, Pi.add_apply, Pi.zero_apply, add_zero]
end Formalism.FN.GjScaling
