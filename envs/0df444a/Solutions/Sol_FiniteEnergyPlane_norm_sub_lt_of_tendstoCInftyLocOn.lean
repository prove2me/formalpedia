-- Prove2me | solution 1 for FiniteEnergyPlane.norm_sub_lt_of_tendstoCInftyLocOn
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-05T20:46:51.78319+00:00
-- url     : https://prove2.me/submissions/fb175263-90cc-4e00-af6f-6ce80e526b38

import Definitions.Def_JHolomorphic_Setting

open Metric Filter Topology

namespace FiniteEnergyPlane

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y]

lemma norm_sub_lt_of_tendstoCInftyLocOn_aux {f : ℕ → X → Y} {g : X → Y} {O K : Set X}
    (hc : JHolomorphic.TendstoCInftyLocOn f g O) (hK : K ⊆ O) (hKc : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ k in atTop, ∀ x ∈ K, ‖f k x - g x‖ < ε := by
  have h := (Metric.tendstoUniformlyOn_iff.1 (hc K hK hKc 0)) ε hε
  filter_upwards [h] with k hk x hx
  have h1 := hk x hx
  rw [dist_comm, dist_eq_norm] at h1
  have h2 := (iteratedFDeriv ℝ 0 (f k) x - iteratedFDeriv ℝ 0 g x).le_opNorm Fin.elim0
  simp only [ContinuousMultilinearMap.sub_apply, iteratedFDeriv_zero_apply, Finset.univ_eq_empty,
    Finset.prod_empty, mul_one] at h2
  exact lt_of_le_of_lt h2 h1

lemma norm_fderiv_sub_le_of_tendstoCInftyLocOn_aux {f : ℕ → X → Y} {g : X → Y} {O K : Set X}
    (hc : JHolomorphic.TendstoCInftyLocOn f g O) (hK : K ⊆ O) (hKc : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ k in atTop, ∀ x ∈ K, ‖fderiv ℝ (f k) x - fderiv ℝ g x‖ ≤ ε := by
  have h := (Metric.tendstoUniformlyOn_iff.1 (hc K hK hKc 1)) ε hε
  filter_upwards [h] with k hk x hx
  have h1 := hk x hx
  rw [dist_comm, dist_eq_norm] at h1
  refine ContinuousLinearMap.opNorm_le_bound _ hε.le fun a => ?_
  have h2 := (iteratedFDeriv ℝ 1 (f k) x - iteratedFDeriv ℝ 1 g x).le_opNorm (fun _ : Fin 1 => a)
  simp only [ContinuousMultilinearMap.sub_apply, iteratedFDeriv_one_apply, Fin.prod_univ_one]
    at h2
  rw [ContinuousLinearMap.sub_apply]
  exact h2.trans (mul_le_mul_of_nonneg_right h1.le (norm_nonneg _))

end FiniteEnergyPlane

open FiniteEnergyPlane

open Filter

theorem solution {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {f : ℕ → X → Y} {g : X → Y} {O K : Set X}
    (hc : JHolomorphic.TendstoCInftyLocOn f g O) (hK : K ⊆ O) (hKc : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ k in atTop, ∀ x ∈ K, ‖f k x - g x‖ < ε :=
  FiniteEnergyPlane.norm_sub_lt_of_tendstoCInftyLocOn_aux hc hK hKc hε
