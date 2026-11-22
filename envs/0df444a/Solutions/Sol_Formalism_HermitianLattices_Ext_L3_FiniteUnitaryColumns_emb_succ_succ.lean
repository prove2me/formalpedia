-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_succ_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:30:28.512867+00:00
-- url     : https://prove2.me/submissions/6f9e8bad-9dc6-446d-9e94-7d4cefd49396

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
theorem _root_.solution {m : ℕ} (Y : Matrix (Fin m) (Fin m) k) (i j : Fin m) :
    emb Y i.succ j.succ = Y i j := rfl
end Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns
