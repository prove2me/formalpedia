-- Prove2me | solution 1 for Eden.tendsto_log_finset_sum_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:32:34.517268+00:00
-- url     : https://prove2.me/submissions/dd4485d8-89a7-43b2-8806-ec4f8411edf9

import Definitions.Def_Eden_RealTimeAverages
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_Eden_LogarithmicSums
import Theorems.Thm_Eden_tendsto_log_add_div

set_option autoImplicit true
noncomputable section
open Filter Set
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution {I : Type*} (s : Finset I) (hs : s.Nonempty)
    (f : I → ℝ → ℝ) (a : I → ℝ)
    (hfpos : ∀ i ∈ s, ∀ᶠ t in atTop, 0 < f i t)
    (hf : ∀ i ∈ s, Tendsto (fun t => Real.log (f i t) / t) atTop (𝓝 (a i))) :
    Tendsto (fun t => Real.log (∑ i ∈ s, f i t) / t) atTop (𝓝 (s.sup' hs a)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hs
  | @insert i s hi ih =>
    by_cases hs' : s.Nonempty
    · have hsumpos : ∀ᶠ t in atTop, 0 < ∑ j ∈ s, f j t := by
        have hpos : ∀ᶠ t in atTop, ∀ j ∈ s, 0 < f j t :=
          (eventually_all_finset s).mpr (fun j hj => hfpos j (Finset.mem_insert_of_mem hj))
        filter_upwards [hpos] with t ht
        exact Finset.sum_pos ht hs'
      have h := tendsto_log_add_div (hfpos i (Finset.mem_insert_self _ _)) hsumpos
        (hf i (Finset.mem_insert_self _ _))
        (ih hs' (fun j hj => hfpos j (Finset.mem_insert_of_mem hj))
          (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
      simpa [Finset.sum_insert hi, Finset.sup'_insert hs'] using h
    · have hz : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs'
      subst s
      simpa using hf i (Finset.mem_insert_self _ _)
end Eden
