-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.isPF_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:39:38.223815+00:00
-- url     : https://prove2.me/submissions/367d14c1-e858-4b3c-b544-d1becd1249bb

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Polynomial
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NFx2
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.NF
noncomputable section
variable {A : Type} [Ring A] [Algebra ℂ A]
namespace Formalism.FourierDecayAlt.P.NFx2
theorem _root_.solution {f : ℂ → A} (hf : IsPF f) {S : Set ℂ} (hS : S.Infinite) (h0 : ∀ Y ∈ S, f Y = 0) :
    ∀ Y, f Y = 0 := by
  obtain ⟨p, hp⟩ := hf
  intro Y
  rw [hp, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  let q : ℂ[X] := p.sum fun n a => monomial n (φ a)
  have hq : ∀ Z, q.eval Z = φ (ev p Z) := by
    intro Z
    simp only [q, ev, eval₂_eq_sum, Polynomial.sum, eval_finsetSum, eval_monomial, map_sum, RingHom.id_apply]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← map_pow, ← Algebra.commutes, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  have : q = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine hS.mono fun Z hZ => ?_
    simp only [Set.mem_ofPred_eq, IsRoot, hq, ← hp, h0 Z hZ, map_zero]
  rw [← hq, this, eval_zero]
end Formalism.FourierDecayAlt.P.NFx2
