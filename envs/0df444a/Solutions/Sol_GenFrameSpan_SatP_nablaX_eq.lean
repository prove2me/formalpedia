-- Prove2me | solution 1 for GenFrameSpan.SatP.nablaX_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:16:12.422786+00:00
-- url     : https://prove2.me/submissions/5d5d515e-2eb2-4c90-a326-01da192233e7

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_SatDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_SatProj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open GenFrameSpan
open CutKW MvPolynomial
open GenFrameSpan.SatP
variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N0 : ℕ}
namespace GenFrameSpan.SatP
theorem _root_.solution (nu : Lt → YoungDiagram) (J : ColChoice N0 nu) :
    nablaX N0 nu J = ∏ s, rename (emb s) (∏ c : Fin ((nu s).rowLen 0), minorX ℤ N0 ((nu s).colLen c) (J s c)) := by
  unfold nablaX minorX
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [AlgHom.map_det]
  congr 1
  ext i k
  simp [emb]
end GenFrameSpan.SatP
