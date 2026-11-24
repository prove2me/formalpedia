-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.ringDataObjects.listDiag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:36:43.42994+00:00
-- url     : https://prove2.me/submissions/4e191bd7-8e96-49c9-823f-3e4f1647d4b4

import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_IdempotentImageSurjective
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_CharpolyRevMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.RepresentationBoundsCohomology Formalism.RepresentationBoundsCohomology.ringDataObjects
open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities
namespace Formalism.RepresentationBoundsCohomology.ringDataObjects
theorem _root_.solution {A : Type*} [CommRing A] {d : Type*} [Fintype d] [DecidableEq d] (f : ℕ → d → A)
    (l : List ℕ) :
    (l.map fun i => (Matrix.diagonal (f i) : Matrix d d A)).prod =
      Matrix.diagonal fun a => (l.map fun i => f i a).prod := by
  induction l with
  | nil => simp
  | cons i l ih => simp [ih, Matrix.diagonal_mul_diagonal]
end Formalism.RepresentationBoundsCohomology.ringDataObjects
