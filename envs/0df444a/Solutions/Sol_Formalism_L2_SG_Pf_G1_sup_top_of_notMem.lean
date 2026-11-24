-- Prove2me | solution 1 for Formalism.L2.SG.Pf.G1.sup_top_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:18:33.125852+00:00
-- url     : https://prove2.me/submissions/8da675ee-d722-4144-9250-41f9657188a6

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExistsOrthGen
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtIffVd
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsFracOfFixed
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtPPowLeSpanSup
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_AlmostEverywhereSpherical

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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.G1
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA
namespace Formalism.L2.SG.Pf.G1
theorem _root_.solution {R : Type*} [CommRing R] {P : Ideal R} (hP : P.IsMaximal) {u : R}
    (hu : u ∉ P) : Ideal.span {u} ⊔ P = ⊤ := by
  by_contra hne
  apply hu
  rw [hP.eq_of_le hne le_sup_right]
  exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self u)
end Formalism.L2.SG.Pf.G1
