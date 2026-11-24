-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x9.cornerCount
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:04:56.765941+00:00
-- url     : https://prove2.me/submissions/6f84c4ce-0375-4ca6-94a3-4b29302895e4

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Minors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block32EqZeroOfUnipotent
import Theorems.Thm_Formalism_FourierDecayAlt_P_leading_minors_count


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x9
open Matrix Finset
open Formalism.FourierDecayAlt.S3
open Formalism.DoubleCosetMeasures (IsUpUni IsLowUni upUniG)
namespace Formalism.FourierDecayAlt.P.S3x9
theorem _root_.solution (K : Type) [Field K] [Fintype K] (r : ℕ) :
    Nat.card {X : Matrix (Fin r) (Fin r) K // ∀ (l : ℕ) (hl : l ≤ r), cm X l hl ≠ 0} =
      Fintype.card K ^ (r ^ 2 - r) * (Fintype.card K - 1) ^ r := by
  rw [← Formalism.FourierDecayAlt.P.leading_minors_count K r]
  exact Nat.card_congr ((revRows K r).subtypeEquiv fun X => Iff.rfl)
end Formalism.FourierDecayAlt.P.S3x9
