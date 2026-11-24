-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux6.entry_le_gN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:55:28.092972+00:00
-- url     : https://prove2.me/submissions/ae31a8c0-d823-4b80-8d48-c63f3a49cc9c

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux6
variable {k j ρ : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux6
theorem _root_.solution {r : ℕ} (M : B.Mat k r) (i l : Fin (2 * r + k + 1)) : ‖M i l‖ ≤ B.gN M := by
  unfold B.gN
  calc ‖M i l‖ = Real.sqrt (Complex.normSq (M i l)) := by
        rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
    _ ≤ Real.sqrt (∑ i, ∑ l, Complex.normSq (M i l)) := by
        apply Real.sqrt_le_sqrt
        calc Complex.normSq (M i l) ≤ ∑ l, Complex.normSq (M i l) :=
              Finset.single_le_sum (f := fun l => Complex.normSq (M i l)) (fun _ _ => Complex.normSq_nonneg _)
                (Finset.mem_univ l)
          _ ≤ ∑ i, ∑ l, Complex.normSq (M i l) :=
              Finset.single_le_sum (f := fun i => ∑ l, Complex.normSq (M i l))
                (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
end Formalism.FourierDecayAlt.P.Ux6
