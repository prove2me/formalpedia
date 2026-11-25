-- Prove2me | solution 1 for ChromaticReconstruction.degree_one_of_repeated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:06:27.147921+00:00
-- url     : https://prove2.me/submissions/fb795011-4dc5-4b68-b7e8-1aea7c300733

import Definitions.Def_RequestProject_RecoveryThm
import Definitions.Def_RequestProject_WeightedIso
import Theorems.Thm_ChromaticReconstruction_exists_ne_of_count_ne_one

set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {K : Type*} [Fintype K] {S : SimpleGraph K}
namespace ChromaticReconstruction
theorem _root_.solution {w : K → ℕ} (hMI : MIso S w) {x : K}
    (h : Multiset.count (w x) (wts w) ≠ 1) : S.degree x = 1 := by
  obtain ⟨y, hyx, hy⟩ := exists_ne_of_count_ne_one h
  exact (hMI x y (Ne.symm hyx) hy.symm).1
end ChromaticReconstruction
