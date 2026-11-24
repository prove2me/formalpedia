-- Prove2me | solution 1 for Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.sum_C_C_mul_sum_of_mul_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:08:31.580872+00:00
-- url     : https://prove2.me/submissions/8cc0b15a-b525-4829-9fe5-8da09b8bb1cf

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_AlmostEverywhereSpherical
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_SumCCMulSumOfMulEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.TestSideWords Formalism.MainNotions.TestSideWords.TwistedFiltration Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
open Formalism.MainNotions.G
namespace Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
theorem _root_.solution {B : Type*} [CommRing B] {σ' σ'' : Type*} {n : ℕ} (P Q : Matrix (Fin n) (Fin n) B)
    (h : Q * P = 1) (Y : Fin n → MvPolynomial σ' (MvPolynomial σ'' B)) (d : Fin n) :
    ∑ b, C (C (P b d)) * ∑ c, C (C (Q c b)) * Y c = Y d := by
  simp_rw [Finset.mul_sum, ← mul_assoc, ← map_mul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, ← map_sum]
  have hcd : ∀ c, ∑ b, P b d * Q c b = (1 : Matrix (Fin n) (Fin n) B) c d := fun c => by
    rw [← h, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  simp_rw [hcd, Matrix.one_apply]
  simp
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
