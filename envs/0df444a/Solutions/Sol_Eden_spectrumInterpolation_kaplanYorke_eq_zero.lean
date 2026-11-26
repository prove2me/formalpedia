-- Prove2me | solution 1 for Eden.spectrumInterpolation_kaplanYorke_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:53:19.109969+00:00
-- url     : https://prove2.me/submissions/491736a9-8a05-444b-86a2-0dae78bbcebc

import Definitions.Def_Eden_DimensionConvergence
import Definitions.Def_Eden_EventualDimensionFormulas
import Theorems.Thm_Eden_kaplanYorkeDimension_formula_of_index_lt_five
import Theorems.Thm_Eden_kaplanYorkeDimension_lt_succ_index
import Theorems.Thm_Eden_kaplanYorkeIndex_le_dimension
import Theorems.Thm_Eden_spectrumEntry_at_kaplanYorkeIndex_neg
import Theorems.Thm_Eden_spectrumInterpolation_interpolate


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution {a : Fin 5 → ℝ}
    (hj : kaplanYorkeIndex a < 5) :
    spectrumInterpolation a (kaplanYorkeDimension a) = 0 := by
  have hα₀ : 0 ≤ kaplanYorkeDimension a - kaplanYorkeIndex a :=
    sub_nonneg.mpr (kaplanYorkeIndex_le_dimension a)
  have hα₁ : kaplanYorkeDimension a - kaplanYorkeIndex a ≤ 1 := by
    linarith [kaplanYorkeDimension_lt_succ_index hj]
  calc
    _ = spectrumPartialSum a (kaplanYorkeIndex a) +
        (kaplanYorkeDimension a - kaplanYorkeIndex a) *
          spectrumEntry a (kaplanYorkeIndex a) := by
      have h := spectrumInterpolation_interpolate a hj hα₀ hα₁
      have heq : (kaplanYorkeIndex a : ℝ) +
          (kaplanYorkeDimension a - kaplanYorkeIndex a) = kaplanYorkeDimension a := by ring
      rw [heq] at h
      exact h
    _ = 0 := by
      rw [kaplanYorkeDimension_formula_of_index_lt_five hj]
      have hn := ne_of_lt (spectrumEntry_at_kaplanYorkeIndex_neg hj)
      field_simp [hn]
      ring
end Eden
