-- Prove2me | solution 1 for ExpConeIPM.Corrector.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T23:49:39.499963+00:00
-- url     : https://prove2.me/submissions/f27316e6-b585-4ac7-a0a7-b3bc2c326029

import Mathlib
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_ExpConeIPM_Corrector_HomogeneousModel
import Definitions.Def_ExpConeIPM_Corrector_SearchDirections

open scoped InnerProductSpace

namespace Aux_ECI_l2

open ExpConeIPM.Corrector

lemma split {n : ℕ} (u v : EuclideanSpace ℝ (Fin (n + 1))) :
    ⟪u, v⟫_ℝ = ⟪hatPart u, hatPart v⟫_ℝ + lastCoord u * lastCoord v := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, Fin.sum_univ_castSucc, hatPart, lastCoord, star_trivial,
    WithLp.ofLp_toLp]
  ring

noncomputable def bet {n m : ℕ}
    (r : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) × ℝ)
    (x' : EuclideanSpace ℝ (Fin (n + 1))) (y' : EuclideanSpace ℝ (Fin m)) : ℝ :=
  ⟪r.1, y'⟫_ℝ + ⟪hatPart x', r.2.1⟫_ℝ + lastCoord x' * r.2.2

lemma polar {n m : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) (c : EuclideanSpace ℝ (Fin n))
    (x s : EuclideanSpace ℝ (Fin (n + 1))) (y : EuclideanSpace ℝ (Fin m))
    (x' s' : EuclideanSpace ℝ (Fin (n + 1))) (y' : EuclideanSpace ℝ (Fin m)) :
    bet (residual A b c x s y) x' y' + bet (residual A b c x' s' y') x y =
      -(⟪x, s'⟫_ℝ + ⟪x', s⟫_ℝ) := by
  rw [split x s', split x' s]
  simp only [bet, ExpConeIPM.Corrector.residual, inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
    inner_neg_left, inner_neg_right, real_inner_smul_left, real_inner_smul_right,
    ContinuousLinearMap.adjoint_inner_right]
  rw [real_inner_comm (hatPart x') c, real_inner_comm (hatPart x) c]
  ring

lemma bet_neg {n m : ℕ} (r : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) × ℝ)
    (x' : EuclideanSpace ℝ (Fin (n + 1))) (y' : EuclideanSpace ℝ (Fin m)) :
    bet (-r) x' y' = -bet r x' y' := by
  simp only [bet, Prod.fst_neg, Prod.snd_neg, inner_neg_left, inner_neg_right]
  ring

end Aux_ECI_l2

open ExpConeIPM.Corrector Aux_ECI_l2 in
theorem solution {n m : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) (c : EuclideanSpace ℝ (Fin n))
    (hA : Function.Surjective A)
    (Khat : Set (EuclideanSpace ℝ (Fin n))) (Fhat : EuclideanSpace ℝ (Fin n) → ℝ) (ϑhat : ℝ)
    (hK : SelfScaledIPM.ShortStep.IsProperCone Khat)
    (hF : SelfScaledIPM.ShortStep.IsLogHomBarrier Khat Fhat ϑhat)
    (x s : EuclideanSpace ℝ (Fin (n + 1))) (y : EuclideanSpace ℝ (Fin m))
    (hz : IsInteriorIterate Khat x s)
    (W : EuclideanSpace ℝ (Fin (n + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (hW : IsDoubleSecantScaling (augCone Khat) (augBarrier Fhat) x s W)
    (dxa dsa : EuclideanSpace ℝ (Fin (n + 1))) (dya : EuclideanSpace ℝ (Fin m))
    (ha : IsAffineDirection A b c x s y W dxa dsa dya) :
    ⟪s, dxa⟫_ℝ + ⟪x, dsa⟫_ℝ = -⟪x, s⟫_ℝ ∧ ⟪dxa, dsa⟫_ℝ = 0 ∧
      ∀ α : ℝ, ⟪x + α • dxa, s + α • dsa⟫_ℝ = (1 - α) * ⟪x, s⟫_ℝ := by
  -- key adjoint identity
  have hadj : ∀ u v, ⟪invT W u, W v⟫_ℝ = ⟪u, v⟫_ℝ := by
    intro u v
    unfold invT
    rw [ContinuousLinearMap.adjoint_inner_left]
    congr 1
    exact W.symm_apply_apply v
  have h1 : ⟪s, dxa⟫_ℝ + ⟪x, dsa⟫_ℝ = -⟪x, s⟫_ℝ := by
    have e1 : ⟪s, dxa⟫_ℝ = ⟪W x, W dxa⟫_ℝ := by rw [hW.1, hadj]
    have e2 : ⟪x, dsa⟫_ℝ = ⟪W x, invT W dsa⟫_ℝ := by
      rw [real_inner_comm, ← hadj dsa x, real_inner_comm]
    have e3 : ⟪x, s⟫_ℝ = ⟪W x, W x⟫_ℝ := by
      rw [real_inner_comm, ← hadj s x, ← hW.1]
    rw [e1, e2, e3, ← inner_add_right, ha.2, inner_neg_right]
  have hr := ha.1
  -- polarization identities
  have pzz := polar A b c x s y x s y
  have pdd := polar A b c dxa dsa dya dxa dsa dya
  have pzd := polar A b c x s y dxa dsa dya
  rw [hr, bet_neg] at pdd pzd
  have h2 : ⟪dxa, dsa⟫_ℝ = 0 := by
    have c1 : ⟪x, dsa⟫_ℝ + ⟪dxa, s⟫_ℝ = -⟪x, s⟫_ℝ := by
      rw [real_inner_comm s dxa]; linarith
    linarith
  refine ⟨h1, h2, fun α => ?_⟩
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm s dxa]
  have : ⟪s, dxa⟫_ℝ + ⟪x, dsa⟫_ℝ = -⟪x, s⟫_ℝ := h1
  rw [h2]
  linear_combination α * this
