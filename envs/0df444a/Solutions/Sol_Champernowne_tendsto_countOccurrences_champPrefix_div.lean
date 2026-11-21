-- Prove2me | solution 1 for Champernowne.tendsto_countOccurrences_champPrefix_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:46:17.441565+00:00
-- url     : https://prove2.me/submissions/77a7c89d-544c-41b0-b124-ac99d3f77e26

module
public import Definitions.Def_LeanPool_Champernowne_Positions
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.SpecificLimits.Basic
public import Definitions.Def_LeanPool_Champernowne_Asymptotics
public import Theorems.Thm_Champernowne_countOccurrences_champPrefix_sub_isLittleO

set_option autoImplicit true
@[expose] public section
public section
open Champernowne
open Filter Asymptotics Topology
namespace Champernowne
theorem _root_.solution {b : ℕ} (hb : 1 < b) {w : List ℕ}
    (hw : ∀ d ∈ w, d < b) (hwne : w ≠ []) :
    Tendsto (fun n => (countOccurrences w (champPrefix b n) : ℝ) / n)
      atTop (𝓝 (((b : ℝ) ^ w.length)⁻¹)) := by
  have hb0 : ((b : ℝ) ^ w.length) ≠ 0 := by positivity
  have ho := countOccurrences_champPrefix_sub_isLittleO hb hw hwne
  rw [Asymptotics.isLittleO_iff_tendsto'
    (by
      filter_upwards [Filter.eventually_ge_atTop 1] with n hn h0
      have : (0 : ℝ) < n := by exact_mod_cast hn
      exact absurd h0 (ne_of_gt this))] at ho
  have hsum := ho.add_const ((1 : ℝ) / (b : ℝ) ^ w.length)
  rw [zero_add] at hsum
  rw [← one_div]
  refine Tendsto.congr' ?_ hsum
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have h0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [one_div]
  field_simp
  ring
end Champernowne
