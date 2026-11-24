-- Prove2me | solution 1 for CompanionTheory.ThKR.Mp.MpA.G_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:21:27.060206+00:00
-- url     : https://prove2.me/submissions/d23af605-aa96-4e45-b3fb-49f6b2a56176

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousOm
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousTo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology CompanionTheory.ThKR.LL LineDeriv
open scoped Real ContDiff
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
open CompanionTheory.ThKR.Mp.MpA
namespace CompanionTheory.ThKR.Mp.MpA
theorem _root_.solution {g h : G l} (h1 : pr g = pr h) (h2 : om g = om h) (h3 : omS g = omS h) : g = h :=
  Subtype.ext (p := (· ∈ sub l)) (Prod.ext h1 (Prod.ext h2 (Units.ext h3)))
end CompanionTheory.ThKR.Mp.MpA
