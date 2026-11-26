-- Prove2me | solution 1 for Eden.kaplanYorkeIndex_eq_of_adjacent_signs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:59:10.079849+00:00
-- url     : https://prove2.me/submissions/96e6d094-e80c-43f6-a65a-85a3a28b9144

import Definitions.Def_Eden_DimensionConvergence
import Definitions.Def_Eden_EventualDimensionFormulas
import Theorems.Thm_Eden_kaplanYorkeIndex_mem
import Theorems.Thm_Eden_le_kaplanYorkeIndex
import Theorems.Thm_Eden_spectrumPartialSum_nonneg_of_le


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution {a : Fin 5 → ℝ} (ha : Antitone a)
    {k : ℕ} (hk : k < 5) (h₀ : 0 ≤ spectrumPartialSum a k)
    (h₁ : spectrumPartialSum a (k + 1) < 0) : kaplanYorkeIndex a = k := by
  apply le_antisymm
  · by_contra h
    have hle : k + 1 ≤ kaplanYorkeIndex a := by omega
    exact (not_le_of_gt h₁) (spectrumPartialSum_nonneg_of_le ha hle
      (kaplanYorkeIndex_mem a).1 (kaplanYorkeIndex_mem a).2)
  · exact le_kaplanYorkeIndex hk.le h₀
end Eden
