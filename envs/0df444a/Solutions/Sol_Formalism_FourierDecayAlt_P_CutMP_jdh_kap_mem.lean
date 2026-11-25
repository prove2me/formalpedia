-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.jdh_kap_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:59:11.478205+00:00
-- url     : https://prove2.me/submissions/8e3e57a9-3050-48a9-b796-241c8308cd3a

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGaugeCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDHat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP
open NumberField
noncomputable section
variable (P : M.Par)
namespace Formalism.FourierDecayAlt.P.CutMP
theorem _root_.solution (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (g : M.Ty P → ℂ) :
    MA.kap P (MA.DQ P) g ∈ Submonoid.closure (MA.bddSet P L) :=
  Submonoid.subset_closure (Or.inl (Or.inl (Or.inr ⟨g, rfl⟩)))
end Formalism.FourierDecayAlt.P.CutMP
