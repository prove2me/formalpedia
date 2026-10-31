-- Prove2me | solution 1 for FiniteEnergyPlane.exists_period_near_of_forall_shift_close
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-30T14:50:07.487+00:00
-- url     : https://prove2.me/submissions/7340d0d9-0d6c-4c3d-932a-eaecdf2d1ce9

import Mathlib



namespace FiniteEnergyPlane

open Filter Topology

theorem exists_period_near_of_forall_shift_close_aux {E : Type*} [NormedAddCommGroup E]
    {x : ℝ → E} {T : ℝ} (hT : 0 < T) (hx : Continuous x) (hxT : Function.Periodic x T)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ η > 0, ∀ a : ℝ, (∀ y : ℝ, ‖x (y + a) - x y‖ ≤ η) →
      ∃ p : ℝ, (∀ y : ℝ, x (y + p) = x y) ∧ |a - p| < δ := by
  by_contra hcon
  push_neg at hcon
  choose A hA1 hA2 using fun n : ℕ => hcon (1 / ((n : ℝ) + 1)) (by positivity)
  -- reduce the phases to one period
  set a' : ℕ → ℝ := fun n => toIcoMod hT 0 (A n) with ha'
  have hAeq : ∀ n, A n = a' n + toIcoDiv hT 0 (A n) • T := by
    intro n
    have := self_sub_toIcoMod hT 0 (A n)
    simp only [ha']
    linarith
  have hzper : ∀ (z : ℤ) (y : ℝ), x (y + z • T) = x y := fun z y => (hxT.zsmul z) y
  have ha'1 : ∀ n, ∀ y, ‖x (y + a' n) - x y‖ ≤ 1 / ((n : ℝ) + 1) := by
    intro n y
    have h := hA1 n y
    rwa [hAeq n, ← add_assoc, hzper] at h
  have ha'2 : ∀ n, ∀ p : ℝ, (∀ y, x (y + p) = x y) → δ ≤ |a' n - p| := by
    intro n p hp
    obtain ⟨z, hz⟩ : ∃ z : ℤ, A n = a' n + z • T := ⟨_, hAeq n⟩
    have h := hA2 n (p + z • T) (fun y => by rw [← add_assoc, hzper, hp])
    rwa [hz, show a' n + z • T - (p + z • T) = a' n - p by ring] at h
  have hmem : ∀ n, a' n ∈ Set.Icc 0 T := fun n => by
    have := toIcoMod_mem_Ico hT 0 (A n)
    rw [zero_add] at this
    exact ⟨this.1, this.2.le⟩
  obtain ⟨α, -, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq hmem
  -- the limit phase is an exact period
  have hα : ∀ y, x (y + α) = x y := by
    intro y
    have h1 : Tendsto (fun n => ‖x (y + a' (φ n)) - x y‖) atTop (𝓝 ‖x (y + α) - x y‖) :=
      (((hx.tendsto _).comp (tendsto_const_nhds.add hlim)).sub tendsto_const_nhds).norm
    have h2 : Tendsto (fun n => 1 / ((φ n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
    have h3 := le_of_tendsto_of_tendsto' h1 h2 (fun n => ha'1 (φ n) y)
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h3)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hlim δ hδ
  have h1 := hN N le_rfl
  have h2 := ha'2 (φ N) α hα
  rw [Function.comp_apply, Real.dist_eq] at h1
  linarith

end FiniteEnergyPlane

open FiniteEnergyPlane

open Filter Topology

theorem solution {E : Type*} [NormedAddCommGroup E]
    {x : ℝ → E} {T : ℝ} (hT : 0 < T) (hx : Continuous x) (hxT : Function.Periodic x T)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ η > 0, ∀ a : ℝ, (∀ y : ℝ, ‖x (y + a) - x y‖ ≤ η) →
      ∃ p : ℝ, (∀ y : ℝ, x (y + p) = x y) ∧ |a - p| < δ :=
  exists_period_near_of_forall_shift_close_aux hT hx hxT δ hδ
