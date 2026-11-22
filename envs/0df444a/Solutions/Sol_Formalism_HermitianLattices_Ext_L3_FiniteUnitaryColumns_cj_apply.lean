-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.cj_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:30:37.169364+00:00
-- url     : https://prove2.me/submissions/fb585dcf-68bf-4a41-aaaf-e9d675c72144

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
theorem _root_.solution {n n' : Type*} (σ : k ≃+* k) (X : Matrix n n' k) (i : n') (j : n) :
    cj σ X i j = σ (X j i) := rfl
end Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns
