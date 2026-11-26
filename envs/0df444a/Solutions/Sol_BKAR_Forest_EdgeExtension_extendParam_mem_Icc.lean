-- Prove2me | solution 1 for BKAR.Forest.EdgeExtension.extendParam_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:37:13.080608+00:00
-- url     : https://prove2.me/submissions/88f54fa2-1cbf-4b63-8507-80b3f02cc396

import Definitions.Def_BKAR_OrderedSimplex
import Definitions.Def_BKAR_OrderedParams
import Theorems.Thm_BKAR_Forest_EdgeExtension_mem_old_of_mem_of_ne


set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.EdgeExtension
variable {F F' : Forest V} {e : Edge V}
namespace BKAR.Forest.EdgeExtension
theorem _root_.solution (h : EdgeExtension F F' e)
    (u : F.EdgeParam → ℝ) {s : ℝ}
    (hu : ∀ e : F.EdgeParam, 0 ≤ u e ∧ u e ≤ 1)
    (hs : 0 ≤ s ∧ s ≤ 1) (e' : F'.EdgeParam) :
    0 ≤ h.extendParam u s e' ∧ h.extendParam u s e' ≤ 1 := by
  by_cases he' : e'.val = e
  · rw [extendParam, dif_pos he']
    exact hs
  · rw [extendParam, dif_neg he']
    exact hu ⟨e'.val, h.mem_old_of_mem_of_ne e'.property he'⟩
end BKAR.Forest.EdgeExtension
