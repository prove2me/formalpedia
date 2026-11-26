-- Prove2me | solution 1 for FourierJacobi.Analysis.i1r9_cartan
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:03:27.825062+00:00
-- url     : https://prove2.me/submissions/0ea56254-93a6-4844-a85d-8c73a39f2ebc

import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Definitions.Def_FourierJacobi_Analysis_I1Complete
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
import Theorems.Thm_FourierJacobi_Analysis_masterTerm_zero
import Theorems.Thm_FourierJacobi_Analysis_shellMonomial_zero
import Theorems.Thm_FourierJacobi_Valuations_tableOne_correct
attribute [local simp] FourierJacobi.Analysis.i0NegativeRowEquiv_val
attribute [local simp] FourierJacobi.Analysis.masterTerm_zero
attribute [local simp] FourierJacobi.Analysis.shellMonomial_zero



set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
namespace FourierJacobi.Analysis
theorem _root_.solution (p : I1R9Row) (depth : ℕ) :
    cartanIndices 1 p.val.1 p.val.2.1 p.val.2.2 depth = (2*p.val.2.1-4*p.val.2.2,2*p.val.2.2-2*p.val.2.1-p.val.1) := by
  rw [← tableOne_correct _ _ _ _ (by omega)]
  rcases p with ⟨⟨k,j,h⟩,hp⟩
  dsimp at hp ⊢
  
  unfold tableOne collisionRows
  split_ifs <;> simp only [Prod.mk.injEq] <;> omega
end FourierJacobi.Analysis
