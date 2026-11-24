-- Prove2me | solution 1 for Formalism.L2.Th1.D.TraceDualSums.inv_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:47:18.55477+00:00
-- url     : https://prove2.me/submissions/b8ce11f9-7313-40a3-9379-1749bd34b815

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionHypothesesOfLevelOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementK
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_TraceDualExists

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.InvariantFactorPaths.G7 (UnrOK)
open Formalism.L2.Th1.D.TraceDualSums
namespace Formalism.L2.Th1.D.TraceDualSums
theorem _root_.solution {K : Type} [Field K] {m : ℕ} [NeZero m] (τ : K →+* K)
    (V P : Matrix (Fin m) (Fin m) K) (hVP : V * P = 1)
    (hV : ∀ k r, τ (V k r) = V (k + 1) r) : ∀ r k, τ (P r k) = P r (k + 1) := by
  have h1 : (V.map τ) * (P.map τ) = 1 := by
    rw [← Matrix.map_mul, hVP]
    exact Matrix.map_one τ (map_zero τ) (map_one τ)
  have h2 : V.map τ = V.submatrix (Equiv.addRight (1 : Fin m)) id := by
    ext k r
    exact hV k r
  have h3 : (V.submatrix (Equiv.addRight (1 : Fin m)) id) *
      (P.submatrix id (Equiv.addRight (1 : Fin m))) = 1 := by
    rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, hVP, Matrix.submatrix_one_equiv]
  have h4 : P.map τ = P.submatrix id (Equiv.addRight (1 : Fin m)) := by
    rw [← Matrix.inv_eq_right_inv h1, h2, Matrix.inv_eq_right_inv h3]
  intro r k
  exact congrFun (congrFun h4 r) k
end Formalism.L2.Th1.D.TraceDualSums
