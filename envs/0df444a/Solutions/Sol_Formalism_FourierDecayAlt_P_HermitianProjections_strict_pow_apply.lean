-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianProjections.strict_pow_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:17:08.36431+00:00
-- url     : https://prove2.me/submissions/08732a55-d9fa-4173-ab2b-e288dd22ae48

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormBasics

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianProjections
namespace Formalism.FourierDecayAlt.P.HermitianProjections
theorem _root_.solution {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (hM : ∀ i j : Fin m, j ≤ i → M i j = 0) :
    ∀ p : ℕ, ∀ i j : Fin m, j.val < i.val + p → (M ^ p) i j = 0 := by
  intro p
  induction p with
  | zero =>
    intro i j hij
    rw [pow_zero]
    exact Matrix.one_apply_ne (fun h => by subst h; omega)
  | succ p ih =>
    intro i j hij
    rw [pow_succ, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : k.val < i.val + p
    · rw [ih i k hk, zero_mul]
    · rw [hM k j (Fin.le_iff_val_le_val.mpr (by omega)), mul_zero]
end Formalism.FourierDecayAlt.P.HermitianProjections
