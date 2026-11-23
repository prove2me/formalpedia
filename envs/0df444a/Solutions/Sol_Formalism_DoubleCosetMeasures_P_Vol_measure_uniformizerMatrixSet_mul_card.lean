-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.Vol.measure_uniformizerMatrixSet_mul_card
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:30.72348+00:00
-- url     : https://prove2.me/submissions/23b38fa6-4bdd-4a28-b9c6-27eaff6cdedc

import Definitions.Def_Formalism_DoubleCosetMeasures_StatementV
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MeasureUniformizerMatrixSetMulCard
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Vol_meas_piece
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Vol_measure_piece
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Vol_intMat_eq_iUnion
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Vol_piece_disjoint

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
theorem _root_.solution (O : Subring F) (hO : IsOpen (O : Set F)) (ϖ : F) (hϖ : ϖ ∈ O) (hϖ0 : ϖ ≠ 0)
    [Finite (kF O ϖ hϖ)] (n a : ℕ) (ν : Measure (Matrix (Fin n) (Fin a) F))
    [ν.IsAddLeftInvariant] :
    ν (IIset O ϖ) * (Nat.card (kF O ϖ hϖ) : ENNReal) ^ (n * a) = ν (intMat O n a) := by
  classical
  haveI : Fintype (kF O ϖ hϖ) := Fintype.ofFinite _
  rw [intMat_eq_iUnion O ϖ hϖ n a,
    measure_iUnion (piece_disjoint O ϖ hϖ n a) (fun c => meas_piece O hO ϖ hϖ0 _), tsum_fintype]
  simp only [measure_piece]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm, Fintype.card_fun,
    Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, Nat.card_eq_fintype_card]
  push_cast
  ring
end Formalism.DoubleCosetMeasures.P.Vol
