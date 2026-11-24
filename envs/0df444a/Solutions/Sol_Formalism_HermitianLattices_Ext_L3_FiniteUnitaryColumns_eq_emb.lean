-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.eq_emb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:20:43.919416+00:00
-- url     : https://prove2.me/submissions/b8469480-59b9-42a2-90f7-9daa6bf104b1

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
theorem _root_.solution {m : ℕ} (σ : k ≃+* k) (Z : Matrix (Fin (m + 1)) (Fin (m + 1)) k)
    (h : cj σ Z * Z = 1) (h0 : Z 0 0 = 1) (hs : ∀ i : Fin m, Z i.succ 0 = 0) :
    Z = emb (Z.submatrix Fin.succ Fin.succ) ∧
      cj σ (Z.submatrix Fin.succ Fin.succ) * Z.submatrix Fin.succ Fin.succ = 1 := by
  have hrow : ∀ j : Fin m, Z 0 j.succ = 0 := by
    intro j
    have := congrFun (congrFun h 0) j.succ
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, cj_apply, h0, hs, Matrix.one_apply,
      (Fin.succ_ne_zero j).symm] using this
  constructor
  · ext i j
    refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
    · simp [h0]
    · simp [hrow]
    · simp [hs]
    · simp
  · ext i j
    have := congrFun (congrFun h i.succ) j.succ
    rw [one_succ_succ] at this
    rw [← this]
    simp [Matrix.mul_apply, Fin.sum_univ_succ, cj_apply, hrow]
end Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns
