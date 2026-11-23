-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ReversedIndexLastBlock.pt_inv_last
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:50:40.485147+00:00
-- url     : https://prove2.me/submissions/398b224a-d64c-4790-aaf2-084e744ec44d

import Definitions.Def_Formalism_HermitianCurvature_StatementA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondKernelPropertyKernel
import Theorems.Thm_Formalism_FourierDecayAlt_P_LastBlockReversal_blk_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_LastBlockReversal_revIn_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_ReversedIndexLastBlock_pt_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ReversedIndexLastBlock
open Formalism.DoubleCosetMeasures
namespace Formalism.FourierDecayAlt.P.ReversedIndexLastBlock
theorem _root_.solution {K : Type} [CommRing K] (l : List ℕ) (t : ℕ → Kˣ) (N : Fin (l ++ [1]).sum)
    (hN : N.val + 1 = (l ++ [1]).sum) : (pt (l ++ [1]) t)⁻¹ N N = (((t l.length)⁻¹ : Kˣ) : K) := by
  rw [Matrix.inv_eq_right_inv (pt_mul _ t)]
  have hN' : (N : ℕ) = l.sum := by
    simp at hN
    omega
  simp only [pt]
  rw [hN', Formalism.FourierDecayAlt.P.LastBlockReversal.revIn_last, if_pos rfl, Formalism.FourierDecayAlt.P.LastBlockReversal.blk_last]
end Formalism.FourierDecayAlt.P.ReversedIndexLastBlock
