-- Prove2me | solution 1 for FiniteEnergyPlane.isLittleO_sub_nhdsWithin_range_of_isPrime
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-27T00:15:17.732798+00:00
-- url     : https://prove2.me/submissions/888e5b88-d97f-4313-be46-2cb4e820c44a

import Definitions.Def_FiniteEnergyPlane_Winding
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_exists_mul_abs_sub_le_norm_sub_of_isPrime



namespace FiniteEnergyPlane

open Metric Filter Topology Asymptotics

/-- Near a point `q = x(τ₀)` of a prime periodic Reeb orbit `P = (x, T)`, every continuous linear map
`L` killing the Reeb vector `R(q)` satisfies `L(p - q) = o(‖p - q‖)` as `p → q` inside `x(ℝ)`. -/
theorem isLittleO_sub_nhdsWithin_range_of_isPrime_aux {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (P : ReebOrbit H) (hP : P.IsPrime) (τ₀ : ℝ)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : V n →L[ℝ] F)
    (hL : L (reeb H (P.x τ₀)) = 0) :
    (fun p => L (p - P.x τ₀)) =o[𝓝[Set.range P.x] (P.x τ₀)] (fun p => p - P.x τ₀) := by
  obtain ⟨c, hc, hlow⟩ := exists_mul_abs_sub_le_norm_sub_of_isPrime H hH P hP
  have hder := P.hasDerivAt τ₀
  rw [hasDerivAt_iff_isLittleO] at hder
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  have hε' : 0 < ε * c / (‖L‖ + 1) := by positivity
  have h1 := (Asymptotics.isLittleO_iff.mp hder) hε'
  obtain ⟨δ, hδ, hδb⟩ := Metric.eventually_nhds_iff.mp h1
  have hper : Function.Periodic P.x P.T := P.periodic
  have hT := P.T_pos
  have hm : 0 < c * min δ (P.T / 2) := by positivity
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Metric.ball_mem_nhds (P.x τ₀) hm] with p hp hpr
  obtain ⟨τ₁, rfl⟩ := hpr
  obtain ⟨τ, hτ, hτeq⟩ := hper.exists_mem_Ico hT τ₁ (τ₀ - P.T / 2)
  rw [hτeq]
  rw [hτeq, Metric.mem_ball, dist_eq_norm] at hp
  have hτ2 : |τ - τ₀| ≤ P.T / 2 := by
    rw [abs_le]; constructor <;> linarith [hτ.1, hτ.2]
  have hl := hlow τ τ₀ hτ2
  have hmin : min δ (P.T / 2) ≤ δ := min_le_left _ _
  have hσ : |τ - τ₀| < δ := by
    by_contra hcon
    push_neg at hcon
    have : c * min δ (P.T / 2) ≤ c * |τ - τ₀| := by
      apply mul_le_mul_of_nonneg_left _ hc.le; linarith
    linarith
  have hb := hδb (show dist τ τ₀ < δ by rwa [Real.dist_eq])
  rw [Real.norm_eq_abs] at hb
  set e := P.x τ - P.x τ₀ - (τ - τ₀) • reeb H (P.x τ₀) with he
  have hsplit : P.x τ - P.x τ₀ = e + (τ - τ₀) • reeb H (P.x τ₀) := by rw [he]; abel
  have hLe : L (P.x τ - P.x τ₀) = L e := by
    rw [hsplit, map_add, map_smul, hL, smul_zero, add_zero]
  rw [hLe]
  have hLn : 0 ≤ ‖L‖ := norm_nonneg _
  have hfrac : ‖L‖ * (ε * c / (‖L‖ + 1)) ≤ ε * c := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith [mul_pos hε hc]
  calc ‖L e‖ ≤ ‖L‖ * ‖e‖ := L.le_opNorm e
    _ ≤ ‖L‖ * (ε * c / (‖L‖ + 1) * |τ - τ₀|) := mul_le_mul_of_nonneg_left hb hLn
    _ = (‖L‖ * (ε * c / (‖L‖ + 1))) * |τ - τ₀| := by ring
    _ ≤ (ε * c) * |τ - τ₀| := mul_le_mul_of_nonneg_right hfrac (abs_nonneg _)
    _ = ε * (c * |τ - τ₀|) := by ring
    _ ≤ ε * ‖P.x τ - P.x τ₀‖ := mul_le_mul_of_nonneg_left hl hε.le

end FiniteEnergyPlane

open FiniteEnergyPlane

open Metric Filter Topology Asymptotics

theorem solution {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (P : ReebOrbit H) (hP : P.IsPrime) (τ₀ : ℝ)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : V n →L[ℝ] F)
    (hL : L (reeb H (P.x τ₀)) = 0) :
    (fun p => L (p - P.x τ₀)) =o[𝓝[Set.range P.x] (P.x τ₀)] (fun p => p - P.x τ₀) :=
  FiniteEnergyPlane.isLittleO_sub_nhdsWithin_range_of_isPrime_aux H hH P hP τ₀ L hL
