-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TBBx2.Tri.cs_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:57:28.091802+00:00
-- url     : https://prove2.me/submissions/fc05048c-d78c-447d-89ee-25b15b82870a

import Definitions.Def_Formalism_HermitianCurvature_StatementTBB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TriangleInequalityAtPlace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TBBx2 Formalism.FourierDecayAlt.P.TBBx2.Tri
open Finset Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB
open scoped ENNReal
noncomputable section
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
variable {P : M.Par}
namespace Formalism.FourierDecayAlt.P.TBBx2.Tri
theorem _root_.solution {n : ℕ} (a x : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) :
    (∑ i, a i * x i) ^ 2 ≤ (∑ i, a i) * ∑ i, a i * x i ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => Real.sqrt (a i))
    (fun i => Real.sqrt (a i) * x i)
  have e1 : ∀ i, Real.sqrt (a i) * (Real.sqrt (a i) * x i) = a i * x i := fun i => by
    rw [← mul_assoc, Real.mul_self_sqrt (ha i)]
  have e2 : ∀ i, Real.sqrt (a i) ^ 2 = a i := fun i => Real.sq_sqrt (ha i)
  have e3 : ∀ i, (Real.sqrt (a i) * x i) ^ 2 = a i * x i ^ 2 := fun i => by
    rw [mul_pow, e2]
  simp only [e1, e2, e3] at h
  exact h
end Formalism.FourierDecayAlt.P.TBBx2.Tri
