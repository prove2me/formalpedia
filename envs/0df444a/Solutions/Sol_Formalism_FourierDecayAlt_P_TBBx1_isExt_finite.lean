-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TBBx1.isExt_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:59:50.949547+00:00
-- url     : https://prove2.me/submissions/a9e958cd-1836-41cd-bac5-418c781b83f1

import Definitions.Def_Formalism_HermitianCurvature_StatementTBB
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MinLeTruncatedExponential

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TBBx1
open Finset Filter Topology MeasureTheory Real
open Formalism.FourierDecayAlt.TBB
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
variable {P : M.Par} {l0 : ℕ} {Y : Finset ℝ} {N : ℕ}
namespace Formalism.FourierDecayAlt.P.TBBx1
theorem _root_.solution (m : ℕ) (w : List C.Letter) : {w' | IsExt P l0 Y N m w w'}.Finite := by
  let A : Finset C.Letter := Y.image (fun y => (true, y)) ∪ Y.image (fun y => (false, y + 1))
  have hfin : {L : List A | L.length ≤ m}.Finite := List.finite_length_le A m
  refine (hfin.image (fun L => L.map Subtype.val ++ w)).subset ?_
  rintro w' ⟨-, -, L, rfl, hLm, hY⟩
  have hA : ∀ l ∈ L, l ∈ A := by
    intro l hl
    obtain ⟨y, hy, h | h⟩ := hY l hl
    · exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨y, hy, h.symm⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨y, hy, h.symm⟩)
  refine ⟨L.attach.map (fun x => ⟨x.1, hA x.1 x.2⟩), by simpa using hLm, ?_⟩
  show List.map Subtype.val (List.map _ L.attach) ++ w = L ++ w
  rw [List.map_map]
  congr 1
  exact List.attach_map_subtype_val L
end Formalism.FourierDecayAlt.P.TBBx1
