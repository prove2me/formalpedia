-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.OrbSum.card_stab_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:33.64727+00:00
-- url     : https://prove2.me/submissions/1bf3f005-0115-423e-af35-187c0cb8881c

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteRepSetOfOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsRepsOfCover

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
open Formalism.HermitianLattices.Ext.L3.OrbSum
variable {G X Y : Type*} [Group G] [MulAction G X] [MulAction G Y]
namespace Formalism.HermitianLattices.Ext.L3.OrbSum
theorem _root_.solution (g : G) (x : X) :
    Nat.card (MulAction.stabilizer G (g • x)) = Nat.card (MulAction.stabilizer G x) := by
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective
end Formalism.HermitianLattices.Ext.L3.OrbSum
