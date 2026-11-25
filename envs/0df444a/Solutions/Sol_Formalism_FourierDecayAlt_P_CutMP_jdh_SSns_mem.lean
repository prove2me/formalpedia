-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.jdh_SSns_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:54:43.953236+00:00
-- url     : https://prove2.me/submissions/4420f0b1-0d1f-4d2a-b73e-0f933ce32d70

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
theorem _root_.solution (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (l : ℕ) (hl : l ∈ Finset.Icc 1 (P.k - 1)) :
    star (SSn P L l) ∈ Submonoid.closure (MA.bddSet P L) :=
  Submonoid.subset_closure (Or.inr ⟨l, Finset.mem_Icc.1 hl, rfl⟩)
end Formalism.FourierDecayAlt.P.CutMP
