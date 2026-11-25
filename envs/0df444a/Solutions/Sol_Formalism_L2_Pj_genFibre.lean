-- Prove2me | solution 1 for Formalism.L2.Pj.genFibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:55:37.469567+00:00
-- url     : https://prove2.me/submissions/96ffcc4b-948b-4d6c-96b5-05ba684947e6

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_VAtVNeBot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntFrames
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_pullCubCancel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_pullCubComp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sabCancel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sabComp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sabPull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)
namespace Formalism.L2.Pj
theorem _root_.solution (hC : ReciprocityTheory.ChartRestriction.G.Out.CubePullSt) : GenFibreSt Xo c := by
  intro T io O _ β Y yt z h1 h2 G m
  obtain ⟨PP', cub, sym, adj, prim, m2, -⟩ := sabPull hC (spMap (algebraMap T.V T.Fr)) G
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ Y.t G _ yt _ m m2
  rw [← h1] at n
  have n' : SABMap _ Y.t (z ≫ (Y.jQ ≫ pullback.fst _ _)) := n
  obtain ⟨m1, -⟩ := sabCancel pullCubCancel E H _ _ _ Y.t Y.oF.t _ _ z Y.m n'
  obtain ⟨n2, -⟩ := sabComp pullCubComp E H _ _ _ Xo.univ.t Y.oF.t _ _ z Y.m0.toSABMap m1
  exact ⟨_, n2, m2, trivial⟩
end Formalism.L2.Pj
