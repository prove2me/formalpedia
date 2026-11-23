-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LocF.isUnitIn_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:09:45.036137+00:00
-- url     : https://prove2.me/submissions/221b9c2a-0cf6-4c2f-8dba-4bb786d98866

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthUnitFrame
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_GmapLocEqOfFrame
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LinearIndependentOfGramDetNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LocF
open Formalism.HermitianLattices.Ext.L3.WA
variable {K : Type*} [Field K] {S : Subring K}
namespace Formalism.HermitianLattices.Ext.L3.LocF
theorem _root_.solution {a b : K} (ha : IsUnitIn S a) (hb : IsUnitIn S b) : IsUnitIn S (a * b) :=
  ⟨mul_ne_zero ha.1 hb.1, S.mul_mem ha.2.1 hb.2.1, by rw [mul_inv]; exact S.mul_mem ha.2.2 hb.2.2⟩
end Formalism.HermitianLattices.Ext.L3.LocF
