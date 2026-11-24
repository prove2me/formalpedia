-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.cj_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:20:43.308295+00:00
-- url     : https://prove2.me/submissions/f943447a-6c57-42a6-aef2-e72b1467b2d6

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardSumNormFibres
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardUnitaryFin
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_cj_apply

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
theorem _root_.solution {n : Type*} [DecidableEq n] (σ : k ≃+* k) : cj σ (1 : Matrix n n k) = 1 := by
  ext i j
  by_cases h : i = j
  · subst h; simp [cj_apply]
  · simp [cj_apply, Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h)]
end Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns
