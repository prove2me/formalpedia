-- Prove2me | solution 1 for BKAR.Forest.OrderedGrowth.params_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:38:11.540292+00:00
-- url     : https://prove2.me/submissions/bf48965f-d246-465c-920b-0e8d199e2603

import Definitions.Def_BKAR_OrderedSimplex
import Definitions.Def_BKAR_OrderedParams
import Theorems.Thm_BKAR_Forest_EdgeExtension_extendParam_mem_Icc
import Theorems.Thm_BKAR_OrderedSimplexParams_tail


set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}
namespace BKAR.Forest.OrderedGrowth
theorem _root_.solution (h : OrderedGrowth F order G)
    (u : F.EdgeParam → ℝ) (ts : List ℝ)
    (hu : ∀ e : F.EdgeParam, 0 ≤ u e ∧ u e ≤ 1)
    (hts : ∀ t ∈ ts, 0 ≤ t ∧ t ≤ 1) :
    ∀ e : G.EdgeParam, 0 ≤ h.params u ts e ∧ h.params u ts e ≤ 1 := by
  induction h generalizing ts with
  | nil F =>
      intro e
      exact hu e
  | cons step tail ih =>
      cases ts with
      | nil =>
          exact ih (step.extendParam u 0) []
            (fun e => step.extendParam_mem_Icc u hu ⟨le_rfl, zero_le_one⟩ e)
            (fun _ ht => by
              cases ht)
      | cons t ts =>
          exact ih (step.extendParam u t) ts
            (fun e => step.extendParam_mem_Icc u hu
              (hts t (by rw [List.mem_cons]; exact Or.inl rfl)) e)
            (fun s hs => hts s (by rw [List.mem_cons]; exact Or.inr hs))
end BKAR.Forest.OrderedGrowth
