-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PositiveSemidefinitePullback.star_ind
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:40:11.017327+00:00
-- url     : https://prove2.me/submissions/409cfae1-9e41-423c-8a80-868a644368fa

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositiveSemidefinitePullback

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PositiveSemidefinitePullback
open Finset Matrix Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data
open scoped ComplexOrder
noncomputable section
open Classical
namespace Formalism.FourierDecayAlt.P.PositiveSemidefinitePullback
theorem _root_.solution {α : Type} (Y A : Finset α) : star (ind Y A) = ind Y A := by
  funext p
  simp only [Pi.star_apply, ind]
  split_ifs <;> simp
end Formalism.FourierDecayAlt.P.PositiveSemidefinitePullback
