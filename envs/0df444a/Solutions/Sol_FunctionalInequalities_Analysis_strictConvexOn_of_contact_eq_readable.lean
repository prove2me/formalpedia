-- Prove2me | solution 1 for FunctionalInequalities.Analysis.strictConvexOn_of_contact_eq_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:31:36.880953+00:00
-- url     : https://prove2.me/submissions/d5444550-a34e-4d12-9831-80d7cc403a4f

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Caffarelli
import Theorems.Thm_FunctionalInequalities_Analysis_exists_subgradient_slope_le_inner_add_readable

noncomputable section
open Set Metric
open scoped RealInnerProductSpace
section LT11F1StrictConvexityElementary
open Set
section InnerProduct
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section FiniteDimensional
variable [FiniteDimensional ℝ E]
/-- **Singleton contact sets give strict convexity** (weak Letwin route): if every
supporting affine function of the convex `u` touches its graph at exactly one point, `u` is strictly
convex. -/
theorem solution {u : E → ℝ} (hconv : ConvexOn ℝ univ u)
    (hcontact : ∀ x p : E, (∀ y, u x + ⟪p, y - x⟫ ≤ u y) →
      ∀ y, u y = u x + ⟪p, y - x⟫ → y = x) :
    StrictConvexOn ℝ univ u := by
  refine ⟨hconv.1, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hle := hconv.2 hx hy ha.le hb.le hab
  simp only [smul_eq_mul] at hle ⊢
  by_contra hn
  let z := a • x + b • y
  have heq : u z = a * u x + b * u y :=
    le_antisymm hle (le_of_not_gt hn)
  obtain ⟨p, hp, _⟩ := FunctionalInequalities.Analysis.exists_subgradient_slope_le_inner_add_readable hconv z (0 : E)
  have hzinner : ⟪p, z⟫ = a * ⟪p, x⟫ + b * ⟪p, y⟫ := by
    simp only [z, inner_add_right, real_inner_smul_right]
  have hlinear : a * ⟪p, x - z⟫ + b * ⟪p, y - z⟫ = 0 := by
    simp only [inner_sub_right]
    calc
      a * (⟪p, x⟫ - ⟪p, z⟫) + b * (⟪p, y⟫ - ⟪p, z⟫) =
          (a * ⟪p, x⟫ + b * ⟪p, y⟫) - (a + b) * ⟪p, z⟫ := by ring
      _ = 0 := by rw [← hzinner, hab, one_mul, sub_self]
  let A := u x - u z - ⟪p, x - z⟫
  let B := u y - u z - ⟪p, y - z⟫
  have hA : 0 ≤ A := by
    dsimp [A]
    linarith [hp x]
  have hB : 0 ≤ B := by
    dsimp [B]
    linarith [hp y]
  have hsum : a * A + b * B = 0 := by
    dsimp [A, B]
    calc
      a * (u x - u z - ⟪p, x - z⟫) +
          b * (u y - u z - ⟪p, y - z⟫) =
          (a * u x + b * u y) - (a + b) * u z -
            (a * ⟪p, x - z⟫ + b * ⟪p, y - z⟫) := by ring
      _ = 0 := by rw [← heq, hab, hlinear, one_mul, sub_self, sub_zero]
  have haA : 0 ≤ a * A := mul_nonneg ha.le hA
  have hbB : 0 ≤ b * B := mul_nonneg hb.le hB
  have hAz : A = 0 := by
    have h : a * A = 0 := by linarith
    exact (mul_eq_zero.mp h).resolve_left (ne_of_gt ha)
  have hBz : B = 0 := by
    have h : b * B = 0 := by linarith
    exact (mul_eq_zero.mp h).resolve_left (ne_of_gt hb)
  have hxz : x = z := hcontact z p hp x (by dsimp [A] at hAz; linarith)
  have hyz : y = z := hcontact z p hp y (by dsimp [B] at hBz; linarith)
  exact hxy (hxz.trans hyz.symm)
