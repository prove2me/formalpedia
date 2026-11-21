-- Prove2me | solution 1 for FiniteEnergyPlane.tendstoCInftyLocOn_shiftA
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-20T19:49:06.43094+00:00
-- url     : https://prove2.me/submissions/59d8804f-6e48-470d-a97c-7fc57816c334

import Definitions.Def_FiniteEnergyPlane_Fredholm



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem tendstoCInftyLocOn_shiftA_aux {n : ℕ} (u : ℂ → V n) (hu : ContDiff ℝ ∞ u)
    (c : ℕ → ℝ) (c₀ : ℝ) (hc : Tendsto c atTop (𝓝 c₀)) (O : Set ℂ) :
    JHolomorphic.TendstoCInftyLocOn (fun k => shiftA (c k) u) (shiftA c₀ u) O := by
  intro K _ hK m
  have hsh : ∀ a : ℝ, iteratedFDeriv ℝ m (shiftA a u) = fun x =>
      Real.exp (2 * a) • iteratedFDeriv ℝ m u x := by
    intro a; funext x
    have e : shiftA a u = Real.exp (2 * a) • u := rfl
    rw [e]
    exact iteratedFDeriv_const_smul_apply (hu.contDiffAt.of_le (by exact_mod_cast le_top))
  have hcont : Continuous (iteratedFDeriv ℝ m u) :=
    hu.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  have hexp : Tendsto (fun k => Real.exp (2 * c k)) atTop (𝓝 (Real.exp (2 * c₀))) :=
    (Real.continuous_exp.tendsto _).comp (tendsto_const_nhds.mul hc)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hB1 : 0 < |B| + 1 := by positivity
  have hev := (Metric.tendsto_nhds.1 hexp) (ε / (|B| + 1)) (div_pos hε hB1)
  filter_upwards [hev] with k hk x hx
  rw [hsh, hsh, dist_eq_norm, ← sub_smul, norm_smul]
  have h1 : ‖Real.exp (2 * c₀) - Real.exp (2 * c k)‖ < ε / (|B| + 1) := by
    rw [Real.norm_eq_abs, abs_sub_comm]; exact hk
  have h2 : ‖iteratedFDeriv ℝ m u x‖ ≤ |B| + 1 := (hB x hx).trans ((le_abs_self B).trans (by linarith))
  calc ‖Real.exp (2 * c₀) - Real.exp (2 * c k)‖ * ‖iteratedFDeriv ℝ m u x‖
      ≤ ‖Real.exp (2 * c₀) - Real.exp (2 * c k)‖ * (|B| + 1) :=
        mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ < ε / (|B| + 1) * (|B| + 1) := mul_lt_mul_of_pos_right h1 hB1
    _ = ε := by field_simp

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (u : ℂ → V n) (hu : ContDiff ℝ ∞ u)
    (c : ℕ → ℝ) (c₀ : ℝ) (hc : Tendsto c atTop (𝓝 c₀)) (O : Set ℂ) :
    JHolomorphic.TendstoCInftyLocOn (fun k => shiftA (c k) u) (shiftA c₀ u) O :=
  tendstoCInftyLocOn_shiftA_aux u hu c c₀ hc O
