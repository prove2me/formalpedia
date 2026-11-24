-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.U0.unit_star
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:20:01.333064+00:00
-- url     : https://prove2.me/submissions/430a1cb9-25ba-4011-8c92-01420a21b070

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AddMulInvMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormRepresentation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0
open WA
variable {K : Type*} [Field K] [StarRing K]
variable {S : Subring K} {π : K}
namespace Formalism.HermitianLattices.Ext.L3.U0
theorem _root_.solution (hS : IsHermSemilocal S) {a : K} (ha : IsUnitIn S a) :
    IsUnitIn S (star a) :=
  ⟨star_ne_zero.mpr ha.1, hS.star_mem _ ha.2.1, by
    rw [← star_inv₀]; exact hS.star_mem _ ha.2.2⟩
end Formalism.HermitianLattices.Ext.L3.U0
