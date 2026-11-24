-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux5.entry_le_gN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:13:42.558667+00:00
-- url     : https://prove2.me/submissions/68069774-0f3d-4d42-81c1-497fdd398072

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DetNormLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux5
namespace Formalism.FourierDecayAlt.P.Ux5
theorem _root_.solution {k r : ℕ} (M : B.Mat k r) (i j : Fin (2 * r + k + 1)) : ‖M i j‖ ≤ B.gN M := by
  unfold B.gN
  rw [← Real.sqrt_sq (norm_nonneg (M i j))]
  apply Real.sqrt_le_sqrt
  rw [← Complex.normSq_eq_norm_sq]
  calc Complex.normSq (M i j) ≤ ∑ j', Complex.normSq (M i j') :=
        Finset.single_le_sum (f := fun j' => Complex.normSq (M i j')) (fun _ _ => Complex.normSq_nonneg _)
          (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', Complex.normSq (M i' j') :=
        Finset.single_le_sum (f := fun i' => ∑ j', Complex.normSq (M i' j'))
          (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
end Formalism.FourierDecayAlt.P.Ux5
