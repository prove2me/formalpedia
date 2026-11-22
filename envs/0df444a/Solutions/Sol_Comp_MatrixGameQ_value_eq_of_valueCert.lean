-- Prove2me | solution 1 for Comp.MatrixGameQ.value_eq_of_valueCert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:42:07.874845+00:00
-- url     : https://prove2.me/submissions/ed554725-9b46-4702-a625-4efef947fb89

import Definitions.Def_Comp_Basic
import Definitions.Def_Comp_MatrixGameQ
import Theorems.Thm_Comp_mem_stdSimplex_of_isStratQ
import Theorems.Thm_Comp_MatrixGameQ_toMatrixGame_A
import Theorems.Thm_Csg_MatrixGame_value_isGreatest_colLPFeasible
import Theorems.Thm_Csg_MatrixGame_value_isLeast_rowLPFeasible

attribute [local simp] Comp.MatrixGameQ.toMatrixGame_A

set_option autoImplicit true
open Comp
open Csg
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]
open Comp.MatrixGameQ
namespace Comp.MatrixGameQ
theorem _root_.solution {G : MatrixGameQ I J} {t : ℚ} {p : I → ℚ} {q : J → ℚ}
    (h : G.ValueCert t p q) : G.toMatrixGame.value = ((t : ℚ) : ℝ) := by
  obtain ⟨hp, hq, hrow, hcol⟩ := h
  refine le_antisymm ?_ ?_
  · refine G.toMatrixGame.value_isLeast_rowLPFeasible.2 ?_
    refine ⟨fun i => ((p i : ℚ) : ℝ), mem_stdSimplex_of_isStratQ hp, fun j => ?_⟩
    have hc : ((∑ i, p i * G.A i j : ℚ) : ℝ) ≤ ((t : ℚ) : ℝ) := by exact_mod_cast hrow j
    push_cast at hc
    simpa using hc
  · refine G.toMatrixGame.value_isGreatest_colLPFeasible.2 ?_
    refine ⟨fun j => ((q j : ℚ) : ℝ), mem_stdSimplex_of_isStratQ hq, fun i => ?_⟩
    have hc : ((t : ℚ) : ℝ) ≤ ((∑ j, G.A i j * q j : ℚ) : ℝ) := by exact_mod_cast hcol i
    push_cast at hc
    simpa using hc
end Comp.MatrixGameQ
