-- Prove2me | solution 1 for CSeparatedNPComplete.SquareReduction.values_eq_encode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:58:18.473144+00:00
-- url     : https://prove2.me/submissions/4a6ca634-bfcd-488f-ad74-9f78a95d1a24

module
public import Definitions.Def_CSeparatedNPComplete_SquarePartition
public import Definitions.Def_CSeparatedNPComplete_SquareReduction

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.SquareReduction
namespace CSeparatedNPComplete.SquareReduction
theorem _root_.solution {n : ℕ} (a : Fin n → ℕ) :
    values a = fun i => (encode a i : ℝ) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j; simp only [values, encode, Fin.append_left]
  · intro j; simp only [values, encode, Fin.append_right]
end CSeparatedNPComplete.SquareReduction
