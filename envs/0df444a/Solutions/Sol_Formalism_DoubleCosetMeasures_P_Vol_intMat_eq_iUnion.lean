-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.Vol.intMat_eq_iUnion
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:52:09.879002+00:00
-- url     : https://prove2.me/submissions/dbbdf470-e977-41eb-b063-a5237e0237bc

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
    intMat O n a = ⋃ c : Fin n → Fin a → kF O ϖ hϖ, piece O ϖ (repM O ϖ hϖ c) := by
  ext y
  simp only [intMat, Set.mem_setOf_eq, Set.mem_iUnion, mem_piece]
  constructor
  · intro hy
    refine ⟨fun i j => Ideal.Quotient.mk _ ⟨y i j, hy i j⟩, fun i j => ?_⟩
    show ∃ o ∈ O, y i j - ((Quotient.out (Ideal.Quotient.mk (Ideal.span {(⟨ϖ, hϖ⟩ : O)})
      ⟨y i j, hy i j⟩) : O) : F) = ϖ * o
    rw [sub_mem_iff hϖ (hy i j) (Quotient.out (Ideal.Quotient.mk (Ideal.span {(⟨ϖ, hϖ⟩ : O)})
      ⟨y i j, hy i j⟩)).2, Subtype.coe_eta, Ideal.Quotient.mk_out]
  · rintro ⟨c, hc⟩ i j
    obtain ⟨o, ho, e⟩ := hc i j
    have h1 : y i j = repM O ϖ hϖ c i j + ϖ * o := by rw [← e]; ring
    rw [h1]
    exact O.add_mem (Quotient.out (c i j)).2 (O.mul_mem hϖ ho)
end Formalism.DoubleCosetMeasures.P.Vol
