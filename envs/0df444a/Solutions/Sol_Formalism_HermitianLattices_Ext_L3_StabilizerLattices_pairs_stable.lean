-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.StabilizerLattices.pairs_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:38:41.746794+00:00
-- url     : https://prove2.me/submissions/46c1f5ca-7d9b-462f-b821-13cee9678584

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsVecOfHermRep
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardStabilizerAutSub
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsRepsOfCover
import Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_ClassRepsDefinite
import Definitions.Def_Lemmata_GeneralBFactSecondForm_Imports
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSmulMem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_StabilizerLattices_apply_mem_gmap
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_OrbitRepresentatives_gmap_mem_genus


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
open Formalism.HermitianLattices.Ext.L3.StabilizerLattices
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {h : V →ₗ⋆[K] V →ₗ[K] K}
namespace Formalism.HermitianLattices.Ext.L3.StabilizerLattices
theorem _root_.solution (hs : h.IsSymm) (L : Submodule (𝓞 K) V) (n : K) (g : Formalism.HermitianLatticesTheory.isom h)
    (p : Submodule (𝓞 K) V × V) (hp : p ∈ pairs h L n) : g • p ∈ pairs h L n :=
  ⟨OrbitRepresentatives.gmap_mem_genus hs hp.1 g.2, apply_mem_gmap g.1 hp.2.1, (g.2 p.2 p.2).trans hp.2.2⟩
end Formalism.HermitianLattices.Ext.L3.StabilizerLattices
