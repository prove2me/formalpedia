-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.smithPairing
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:53:49.77874+00:00
-- url     : https://prove2.me/submissions/63818b5e-8c1f-439a-8aa4-efadbe469ca4

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_BinomialRatio_SmithPairing
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_smithMatrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.KP
open Module
namespace Formalism.InvariantFactorPaths.KP
theorem _root_.solution (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] (n : ℕ) (G : Matrix (Fin n) (Fin n) K) :
    ∃ P Q : Matrix (Fin n) (Fin n) O, IsUnit P.det ∧ IsUnit Q.det ∧
      ∀ i j, i ≠ j → (P.map (algebraMap O K) * G * Q.map (algebraMap O K)) i j = 0 := by
  classical
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O)
    (Finset.univ : Finset (Fin n × Fin n)) (fun p => G p.1 p.2)
  have hA : ∀ i j, ∃ a : O, algebraMap O K a = (d : O) • G i j := fun i j => by
    obtain ⟨a, ha⟩ := hd (i, j) (Finset.mem_univ _)
    exact ⟨a, ha⟩
  choose A hA using hA
  obtain ⟨P, Q, hP, hQ, hPQ⟩ := smithMatrix n (Matrix.of A)
  refine ⟨P, Q, hP, hQ, fun i j hij => ?_⟩
  have hd0 : algebraMap O K (d : O) ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap O K), (IsFractionRing.injective O K).eq_iff]
    exact nonZeroDivisors.coe_ne_zero d
  have key : (Matrix.of A).map (algebraMap O K) = algebraMap O K (d : O) • G := by
    ext i j
    simp [hA, Algebra.smul_def]
  have h2 : (P * Matrix.of A * Q).map (algebraMap O K) =
      algebraMap O K (d : O) • (P.map (algebraMap O K) * G * Q.map (algebraMap O K)) := by
    rw [Matrix.map_mul, Matrix.map_mul, key, Matrix.mul_smul, Matrix.smul_mul]
  have h3 := congrFun (congrFun h2 i) j
  rw [Matrix.map_apply, hPQ i j hij, map_zero, Matrix.smul_apply, smul_eq_mul] at h3
  exact (mul_eq_zero.1 h3.symm).resolve_left hd0
end Formalism.InvariantFactorPaths.KP
