-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.gj_cols
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:53.015523+00:00
-- url     : https://prove2.me/submissions/e32ae8d6-4c46-4965-b480-e9b85a427698

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.ExpansionTerms Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts Matrix Finset
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {m n : ℕ} (s : Matrix (Fin m) (Fin m) ℂ) (F : Matrix (Fin m) (Fin n) ℂ)
    (U : Matrix (Fin n) (Fin n) ℂ) :
    s * F = F * U ↔ ∀ b, s *ᵥ (fun i => F i b) = ∑ e, U e b • (fun i => F i e) := by
  constructor
  · intro h b
    funext i
    have e := congrFun (congrFun h i) b
    rw [Matrix.mul_apply, Matrix.mul_apply] at e
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [e]
    exact Finset.sum_congr rfl fun e _ => mul_comm _ _
  · intro h
    ext i b
    have e := congrFun (h b) i
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at e
    rw [Matrix.mul_apply, Matrix.mul_apply, e]
    exact Finset.sum_congr rfl fun e _ => mul_comm _ _
end Formalism.HermitianLatticeCounting.P
