-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x5.prod_addBlock
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:19.240823+00:00
-- url     : https://prove2.me/submissions/3d7c4827-9ead-439e-b3ef-c563fdf834ed

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_blk_lt
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_blk_append_lt
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_blk_append_ge
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val


attribute [local simp] Formalism.FourierDecayAlt.P.A5x5.mv_apply

set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x5
variable {K : Type} [CommRing K] {R : Subring K}
namespace Formalism.FourierDecayAlt.P.A5x5
theorem _root_.solution (h : Point K) (s : ℕ) (t : Kˣ) :
    (∏ a : Fin (addBlock h s t).1.sum,
      (((addBlock h s t).2 (blk (addBlock h s t).1 a) : Kˣ) : K)) =
      (∏ a : Fin h.1.sum, ((h.2 (blk h.1 a) : Kˣ) : K)) * (t : K) ^ s := by
  have e1 : (∏ a : Fin (addBlock h s t).1.sum,
      (((addBlock h s t).2 (blk (addBlock h s t).1 a) : Kˣ) : K)) =
      ∏ i ∈ Finset.range (addBlock h s t).1.sum,
        (((addBlock h s t).2 (blk (addBlock h s t).1 i) : Kˣ) : K) :=
    Fin.prod_univ_eq_prod_range (fun i => (((addBlock h s t).2 (blk (addBlock h s t).1 i) : Kˣ) : K)) _
  have e2 : (∏ a : Fin h.1.sum, ((h.2 (blk h.1 a) : Kˣ) : K)) =
      ∏ i ∈ Finset.range h.1.sum, ((h.2 (blk h.1 i) : Kˣ) : K) :=
    Fin.prod_univ_eq_prod_range (fun i => ((h.2 (blk h.1 i) : Kˣ) : K)) _
  rw [e1, e2]
  simp only [addBlock]
  rw [List.sum_append, List.sum_singleton, Finset.prod_range_add]
  congr 1
  · refine Finset.prod_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [blk_append_lt h.1 s i hi, Function.update_of_ne (blk_lt h.1 i hi).ne]
  · have e : ∀ j ∈ Finset.range s,
        (((Function.update h.2 h.1.length t) (blk (h.1 ++ [s]) (h.1.sum + j)) : Kˣ) : K) = (t : K) :=
      fun j hj => by
        rw [Finset.mem_range] at hj
        rw [blk_append_ge h.1 s j hj, Function.update_self]
    rw [Finset.prod_congr rfl e, Finset.prod_const, Finset.card_range]
end Formalism.FourierDecayAlt.P.A5x5
