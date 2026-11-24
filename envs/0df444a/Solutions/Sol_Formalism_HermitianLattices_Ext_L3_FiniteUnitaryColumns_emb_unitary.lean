-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_unitary
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:06.706794+00:00
-- url     : https://prove2.me/submissions/b6f01884-2de5-4120-b8e3-074ac3954c6b

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardSumNormFibres
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardUnitaryFin
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_cj_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_one_succ_succ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_zero_zero
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_zero_succ
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_succ_zero
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_succ_succ

set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns
open Matrix
variable {k : Type*} [Field k]
namespace Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns
theorem _root_.solution {m : ℕ} (σ : k ≃+* k) (Y : Matrix (Fin m) (Fin m) k) (h : cj σ Y * Y = 1) :
    cj σ (emb Y) * emb Y = 1 := by
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
  · simp [Matrix.mul_apply, Fin.sum_univ_succ, cj_apply]
  · simp [Matrix.mul_apply, Fin.sum_univ_succ, cj_apply, (Fin.succ_ne_zero j').symm]
  · simp [Matrix.mul_apply, Fin.sum_univ_succ, cj_apply, Fin.succ_ne_zero i']
  · have := congrFun (congrFun h i') j'
    rw [one_succ_succ, ← this]
    simp [Matrix.mul_apply, Fin.sum_univ_succ, cj_apply]
end Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns
