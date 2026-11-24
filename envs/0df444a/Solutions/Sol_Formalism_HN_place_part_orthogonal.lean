-- Prove2me | solution 1 for Formalism.HN.place_part_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:28.115208+00:00
-- url     : https://prove2.me/submissions/5a2a7d53-85f7-4f9f-9759-b4228109ccd4

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_HarderNarasimhan_DefsPl
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_GramBlock
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtImage
import Theorems.Thm_Formalism_HN_mem_place_part_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.HN
namespace Formalism.HN
theorem _root_.solution {P ι : Type*} [Fintype P] [Fintype ι] {v w : P} (h : v ≠ w)
    (x : EuclideanSpace ℝ (P × ι × Fin 2)) (hx : x ∈ placePart v)
    (y : EuclideanSpace ℝ (P × ι × Fin 2)) (hy : y ∈ placePart w) : inner ℝ x y = 0 := by
  rw [mem_place_part_iff] at hx hy
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro p _
  by_cases hp : p.1 = v
  · rw [hy p (by rw [hp]; exact h)]
    simp
  · rw [hx p hp]
    simp
end Formalism.HN
