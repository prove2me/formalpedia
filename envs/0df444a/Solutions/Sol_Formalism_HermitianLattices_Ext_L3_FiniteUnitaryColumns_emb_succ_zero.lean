-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_succ_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:30:28.625472+00:00
-- url     : https://prove2.me/submissions/cdb0e251-0b6b-414e-9159-fc208e533f2f

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardSumNormFibres
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardUnitaryFin

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns
open Matrix
variable {k : Type*} [Field k]
namespace Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns
theorem _root_.solution {m : ℕ} (Y : Matrix (Fin m) (Fin m) k) (i : Fin m) :
    emb Y i.succ 0 = 0 := rfl
end Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns
