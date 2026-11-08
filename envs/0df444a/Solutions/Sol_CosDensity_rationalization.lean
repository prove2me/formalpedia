-- Prove2me | solution 1 for CosDensity.rationalization
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T05:56:46.30127+00:00
-- url     : https://prove2.me/submissions/2be35451-1bfa-436b-ac54-2480650af5d6

import Mathlib
import Definitions.Def_CosDensity_Stream
import Definitions.Def_CosDensity_Perturb

open scoped RealInnerProductSpace

open CosDensity in
theorem solution {ι : Type*} [Fintype ι] {n : ℕ} (u : Fin n → EuclideanSpace ℝ ι)
    (hu : ∀ i, ‖u i‖ = 1) (ξ : ℝ) (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1) (η : ℝ)
    (uh : Fin n → EuclideanSpace ℝ (Option ι)) (huh : ∀ i, ‖uh i‖ = 1)
    (hη : ∀ i, ‖uh i - perturb ξ (u i)‖ ≤ η) :
    (∀ i j, |⟪uh i, uh j⟫ - ⟪perturb ξ (u i), perturb ξ (u j)⟫| ≤
      ‖uh i - perturb ξ (u i)‖ + ‖uh j - perturb ξ (u j)‖ ∧
      ‖uh i - perturb ξ (u i)‖ + ‖uh j - perturb ξ (u j)‖ ≤ 2 * η) ∧
    ∀ i, |densityF uh i - densityF (fun k => perturb ξ (u k)) i| ≤ 2 * n * η := by
  have h1ξ : 0 ≤ 1 - ξ ^ 2 := by nlinarith
  have hu2 : ∀ i, ∑ k, (u i k) ^ 2 = 1 := by
    intro i
    have := hu i
    rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one] at this
    simpa [Real.norm_eq_abs, sq_abs] using this
  have hp : ∀ i, ‖perturb ξ (u i)‖ = 1 := by
    intro i
    rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one, Fintype.sum_option]
    simp only [perturb, PiLp.toLp_apply, Real.norm_eq_abs, sq_abs, mul_pow,
      Real.sq_sqrt h1ξ]
    rw [← Finset.mul_sum, hu2]
    ring
  have key : ∀ a a' b b' : EuclideanSpace ℝ (Option ι), ‖b‖ = 1 → ‖a'‖ = 1 →
      |⟪a, b⟫ - ⟪a', b'⟫| ≤ ‖a - a'‖ + ‖b - b'‖ := by
    intro a a' b b' hb ha'
    have e : ⟪a, b⟫ - ⟪a', b'⟫ = ⟪a - a', b⟫ + ⟪a', b - b'⟫ := by
      rw [inner_sub_left, inner_sub_right]; ring
    rw [e]
    calc |⟪a - a', b⟫ + ⟪a', b - b'⟫| ≤ |⟪a - a', b⟫| + |⟪a', b - b'⟫| := abs_add_le _ _
      _ ≤ ‖a - a'‖ * ‖b‖ + ‖a'‖ * ‖b - b'‖ :=
          add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
      _ = ‖a - a'‖ + ‖b - b'‖ := by rw [hb, ha']; ring
  refine ⟨fun i j => ⟨key _ _ _ _ (huh j) (hp i), by linarith [hη i, hη j]⟩, fun i => ?_⟩
  have hun : ∀ x : EuclideanSpace ℝ (Option ι), ‖x‖ = 1 → unitize x = x := by
    intro x hx; unfold unitize; rw [hx, inv_one, one_smul]
  have hu1 : ∀ j, unitize (uh j) = uh j := fun j => hun _ (huh j)
  have hu2' : ∀ j, unitize (perturb ξ (u j)) = perturb ξ (u j) := fun j => hun _ (hp j)
  unfold densityF
  simp only [hu1, hu2']
  rw [← Finset.sum_sub_distrib]
  calc |∑ j, (⟪uh i, uh j⟫ - ⟪perturb ξ (u i), perturb ξ (u j)⟫)|
      ≤ ∑ j, |⟪uh i, uh j⟫ - ⟪perturb ξ (u i), perturb ξ (u j)⟫| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin n, 2 * η := Finset.sum_le_sum fun j _ =>
        (key _ _ _ _ (huh j) (hp i)).trans (by linarith [hη i, hη j])
    _ = 2 * n * η := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
