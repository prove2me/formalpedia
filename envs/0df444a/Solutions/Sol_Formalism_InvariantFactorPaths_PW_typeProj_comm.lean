-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.typeProj_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:58:49.111496+00:00
-- url     : https://prove2.me/submissions/4aa438b1-e629-45dc-ad58-8bc075922f32

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_WeightCompApply
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_CommProjectionHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_iSup_isoC_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (T : Set (Fin r → ℤ))
    (P : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hP : IsTypeProj p LL j Cs T P)
    (A : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hA : ∀ la, ∀ x ∈ IsoC p LL j Cs la, A x ∈ IsoC p LL j Cs la) : P ∘ₗ A = A ∘ₗ P := by
  obtain ⟨hPP, hr, hk⟩ := hP
  have hPP' : ∀ x, P (P x) = P x := fun x => congrArg (fun f => f x) hPP
  have hR : ∀ x ∈ LinearMap.range P, A x ∈ LinearMap.range P := by
    rw [hr]; exact iSup_isoC_map LL j Cs (fun la => la ∈ T) A hA
  have hK : ∀ x ∈ LinearMap.ker P, A x ∈ LinearMap.ker P := by
    rw [hk]; exact iSup_isoC_map LL j Cs (fun la => la ∉ T) A hA
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  have h1 : P (A (P x)) = A (P x) := by
    obtain ⟨y, hy⟩ := hR (P x) ⟨x, rfl⟩
    rw [← hy, hPP']
  have h2 : P (A (x - P x)) = 0 := by
    apply hK
    rw [LinearMap.mem_ker, map_sub, hPP', sub_self]
  rw [map_sub, map_sub, h1, sub_eq_zero] at h2
  exact h2
end Formalism.InvariantFactorPaths.PW
