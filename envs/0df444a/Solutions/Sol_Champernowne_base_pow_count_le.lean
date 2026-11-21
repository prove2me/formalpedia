-- Prove2me | solution 1 for Champernowne.base_pow_count_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:44:39.658318+00:00
-- url     : https://prove2.me/submissions/75c371c3-1857-4656-bd69-f22b30ed5e01

module
public import Definitions.Def_LeanPool_Champernowne_Positions
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.SpecificLimits.Basic
public import Definitions.Def_LeanPool_Champernowne_Asymptotics
public import Theorems.Thm_Champernowne_champM_pos
public import Theorems.Thm_Champernowne_pow_champM_le
public import Theorems.Thm_Champernowne_le_pow_champM
public import Theorems.Thm_Champernowne_tendsto_champM_atTop
public import Theorems.Thm_Champernowne_base_pow_countOccurrences_champPrefix_le


set_option autoImplicit true
@[expose] public section
public section
open Champernowne
open Filter Asymptotics Topology
namespace Champernowne
theorem _root_.solution {b : ℕ} (hb : 1 < b) {w : List ℕ}
    (hw : ∀ d ∈ w, d < b) (hwne : w ≠ []) :
    ∀ᶠ n in atTop, b ^ w.length * countOccurrences w (champPrefix b n)
      ≤ n + 7 * (w.length + 1) * b ^ (2 * w.length) * b ^ champM b n := by
  filter_upwards [(tendsto_champM_atTop hb).eventually_ge_atTop w.length] with n hn
  exact base_pow_countOccurrences_champPrefix_le hb n (champM b n) hw hwne
    (champM_pos b n) hn (pow_champM_le b n) (le_pow_champM hb n)
end Champernowne
