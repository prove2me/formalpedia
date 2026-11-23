-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.Vol.piece_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:52:26.878076+00:00
-- url     : https://prove2.me/submissions/760f7ecb-7221-4e21-87f4-93ce8b790baa

import Definitions.Def_Formalism_DoubleCosetMeasures_StatementV
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MeasureUniformizerMatrixSetMulCard
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Vol_mem_piece
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Vol_sub_mem_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Matrix
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.Vol
variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalRing F] [MeasurableSpace F]
  [BorelSpace F]
namespace Formalism.DoubleCosetMeasures.P.Vol
theorem _root_.solution (O : Subring F) (ϖ : F) (hϖ : ϖ ∈ O) (n a : ℕ) :
    Pairwise (Function.onFun Disjoint
      (fun c : Fin n → Fin a → kF O ϖ hϖ => piece O ϖ (repM O ϖ hϖ c))) := by
  intro c c' hne
  rw [Function.onFun, Set.disjoint_left]
  intro y h1 h2
  apply hne
  rw [mem_piece] at h1 h2
  funext i j
  obtain ⟨o, ho, e⟩ := h1 i j
  obtain ⟨o', ho', e'⟩ := h2 i j
  simp only [repM] at e e'
  have key : ∃ o ∈ O, ((Quotient.out (c' i j) : O) : F) - ((Quotient.out (c i j) : O) : F) =
      ϖ * o := ⟨o - o', O.sub_mem ho ho', by linear_combination e - e'⟩
  rw [sub_mem_iff hϖ (Quotient.out (c' i j)).2 (Quotient.out (c i j)).2, Subtype.coe_eta, Subtype.coe_eta,
    Ideal.Quotient.mk_out, Ideal.Quotient.mk_out] at key
  exact key.symm
end Formalism.DoubleCosetMeasures.P.Vol
