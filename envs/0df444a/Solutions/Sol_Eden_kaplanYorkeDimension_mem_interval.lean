-- Prove2me | solution 1 for Eden.kaplanYorkeDimension_mem_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:53:35.087465+00:00
-- url     : https://prove2.me/submissions/aa8ff29e-0a02-4d44-9cf5-51cbe1f301c8

import Definitions.Def_Eden_LyapunovExponents
import Mathlib.Data.Finset.Max
import Definitions.Def_Eden_KaplanYorke
import Theorems.Thm_Eden_kaplanYorkeIndex_mem
import Theorems.Thm_Eden_kaplanYorkeDimension_of_index_zero
import Theorems.Thm_Eden_kaplanYorkeDimension_of_index_five
import Theorems.Thm_Eden_kaplanYorkeDimension_between_index

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution (a : Fin 5 → ℝ) :
    kaplanYorkeDimension a ∈ Set.Icc 0 5 := by
  by_cases h₀ : kaplanYorkeIndex a = 0
  · rw [kaplanYorkeDimension_of_index_zero h₀]
    norm_num
  by_cases h₅ : kaplanYorkeIndex a = 5
  · rw [kaplanYorkeDimension_of_index_five h₅]
    norm_num
  have hj₀ : 0 < kaplanYorkeIndex a := by omega
  have hj₅ : kaplanYorkeIndex a < 5 := lt_of_le_of_ne (kaplanYorkeIndex_mem a).1 h₅
  have h := kaplanYorkeDimension_between_index hj₀ hj₅
  have hj : (kaplanYorkeIndex a : ℝ) + 1 ≤ 5 := by exact_mod_cast hj₅
  constructor
  · exact (Nat.cast_nonneg _).trans h.1
  · exact h.2.le.trans hj
end Eden
