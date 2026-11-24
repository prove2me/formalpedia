-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianXiVector.nEich_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:26:05.279996+00:00
-- url     : https://prove2.me/submissions/a57d9571-609c-4d80-bf88-e3152372a653

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FlagSpanVanishing
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianXiVector
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianXiVector_herm_X_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianXiVector_herm_X_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianXiVector_xiV_X
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianXiVector_nEich_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_FlagSpanVanishing_mulVec_bvec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.HermitianXiVector
open C2x5 FlagSpanVanishing
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.HermitianXiVector
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (ξ : Fin r → ℂ) :
    WeylGroupFacts.col k r (C2.nEich k r z ξ) := by
  intro i j hj hij
  have e : (C2.nEich k r z ξ *ᵥ bvec j) i = C2.nEich k r z ξ i j := by rw [mulVec_bvec]
  rw [← e, nEich_apply]
  have hjx : herm (Hpk k r) (bvec j) (C2.xiV k r ξ) = 0 :=
    herm_X_right (C2.xiV k r ξ) (bvec j) (xiV_X ξ) (fun p hp => by
      simp only [bvec, Pi.single_apply]; rw [if_neg (fun e => by rw [e] at hp; omega)])
  rw [hjx]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, bvec, Pi.single_apply, Pi.neg_apply, zero_mul, mul_zero,
    add_zero]
  by_cases hir : r ≤ i.val
  · rw [xiV_X ξ i hir]; simp
  · have hjr : j.val < r := by omega
    have hjz : herm (Hpk k r) (Pi.single j 1) z = 0 :=
      herm_X_left (Pi.single j 1) z (fun p hp => by
        simp only [Pi.single_apply]; rw [if_neg (fun e => by rw [e] at hp; omega)])
        (fun p hp => hz.1 p (Or.inr hp))
    rw [hjz]; simp
end Formalism.FourierDecayAlt.P.HermitianXiVector
