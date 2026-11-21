-- Prove2me | solution 1 for Champernowne.le_base_pow_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:44:06.191541+00:00
-- url     : https://prove2.me/submissions/d0876296-ccb0-4790-91a6-767f3693daf9

module
public import Definitions.Def_LeanPool_Champernowne_Positions
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.SpecificLimits.Basic
public import Definitions.Def_LeanPool_Champernowne_Asymptotics
public import Theorems.Thm_Champernowne_champM_pos
public import Theorems.Thm_Champernowne_pow_champM_le
public import Theorems.Thm_Champernowne_le_pow_champM
public import Theorems.Thm_Champernowne_tendsto_champM_atTop
public import Theorems.Thm_Champernowne_le_base_pow_countOccurrences_champPrefix


set_option autoImplicit true
@[expose] public section
public section
open Champernowne
open Filter Asymptotics Topology
namespace Champernowne
theorem _root_.solution {b : ℕ} (hb : 1 < b) {w : List ℕ}
    (hw : ∀ d ∈ w, d < b) (hwne : w ≠ []) :
    ∀ᶠ n in atTop, n ≤ b ^ w.length * countOccurrences w (champPrefix b n)
      + 7 * (w.length + 1) * b ^ w.length * b ^ champM b n := by
  filter_upwards [(tendsto_champM_atTop hb).eventually_ge_atTop w.length] with n hn
  exact le_base_pow_countOccurrences_champPrefix hb n (champM b n) hw hwne
    (champM_pos b n) hn (pow_champM_le b n) (le_pow_champM hb n)
end Champernowne
