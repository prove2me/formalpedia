-- Prove2me | solution 1 for BanditAlgorithm.partial_monitoring_easy_geometric_alternatives_of_outside
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-13T17:08:07.220417+00:00
-- url     : https://prove2.me/submissions/97698cff-a30a-4437-88b7-12958d6f4e57

import Definitions.Def_PartialMonitoringGame
import Theorems.Thm_BanditAlgorithm_partial_monitoring_neighbour_transverse_direction
import Theorems.Thm_BanditAlgorithm_partial_monitoring_uniform_outside_gap
import Theorems.Thm_BanditAlgorithm_partial_monitoring_neighbour_positive_common_point
import Theorems.Thm_BanditAlgorithm_partial_monitoring_neighbour_loss_interpolation
import Theorems.Thm_stdSimplex_small_perturbation
import Theorems.Thm_finite_linear_gaps_stable
import Mathlib.Analysis.Convex.Combination
import Mathlib.Tactic

open Set

namespace BanditAlgorithm

private theorem convex_pmCell' {k d : ℕ} {𝕊 : Type*}
    (G : PartialMonitoringGame k d 𝕊) (a : Fin k) : Convex ℝ (pmCell G a) := by
  intro x hx y hy α β hα hβ hsum
  refine ⟨(convex_stdSimplex ℝ (Fin d)) hx.1 hy.1 hα hβ hsum, ?_⟩
  intro c
  have hxc := hx.2 c
  have hyc := hy.2 c
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hid : (∑ i, (G.L a i - G.L c i) * (α * x i + β * y i)) =
      α * ∑ i, (G.L a i - G.L c i) * x i +
        β * ∑ i, (G.L a i - G.L c i) * y i := by
    calc
      _ = ∑ i, (α * ((G.L a i - G.L c i) * x i) +
          β * ((G.L a i - G.L c i) * y i)) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  rw [hid]
  exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos hα hxc)
    (mul_nonpos_of_nonneg_of_nonpos hβ hyc)

/-!
Lattimore--Szepesvari, *Bandit Algorithms*, Theorems 37.12--37.13,
printed pp.488--492. This is the shared perturbation geometry for a
non-globally-observable neighbouring edge with an outside action.
-/

theorem partial_monitoring_easy_geometric_alternatives_of_outside
    {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊] [DecidableEq 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (a b : Fin k)
    (hab : NeighbouringActions G a b)
    (hout : ∃ c : Fin k, c ∉ pmNeighbourhood G a b) :
    ∃ a b : Fin k, ∃ u q : Fin d → ℝ, ∃ ε δ : ℝ,
      NeighbouringActions G a b ∧ 0 < ε ∧ 0 < δ ∧
      (∑ i, q i) = 0 ∧
      (∑ i, (G.L a i - G.L b i) * q i) = 1 ∧
      ∀ Δ : ℝ, 0 < Δ → Δ ≤ δ →
        let ua := fun i ↦ u i - Δ * q i
        let ub := fun i ↦ u i + Δ * q i
        ua ∈ pmCell G a ∧ ub ∈ pmCell G b ∧
        (∀ c : Fin k, c ∉ pmNeighbourhood G a b →
          ε / 2 ≤ ∑ i, (G.L c i - G.L a i) * ua i ∧
          ε / 2 ≤ ∑ i, (G.L c i - G.L b i) * ub i) ∧
        (∀ c : Fin k, c ∈ pmNeighbourhood G a b →
          (∑ i, (G.L c i - G.L a i) * ua i) +
          (∑ i, (G.L c i - G.L b i) * ub i) = Δ) := by
  classical
  obtain ⟨q, hqsum, hqnorm⟩ :=
    partial_monitoring_neighbour_transverse_direction G a b hab
  obtain ⟨ug, hug, ε₀, hε₀, hgapg⟩ :=
    partial_monitoring_uniform_outside_gap G a b hout
  obtain ⟨up, hup, huppos⟩ :=
    partial_monitoring_neighbour_positive_common_point G a b hab
  let u : Fin d → ℝ := fun i ↦ (ug i + up i) / 2
  have hu : u ∈ pmCell G a ∩ pmCell G b := by
    constructor
    · have h : (1 / 2 : ℝ) • ug + (1 / 2 : ℝ) • up ∈ pmCell G a :=
        convex_pmCell' G a hug.1 hup.1 (by norm_num) (by norm_num) (by norm_num)
      convert h using 1 <;>
        ext i <;> simp [u] <;> ring
    · have h : (1 / 2 : ℝ) • ug + (1 / 2 : ℝ) • up ∈ pmCell G b :=
        convex_pmCell' G b hug.2 hup.2 (by norm_num) (by norm_num) (by norm_num)
      convert h using 1 <;>
        ext i <;> simp [u] <;> ring
  have hupos : ∀ i, 0 < u i := by
    intro i
    have := hug.1.1.1 i
    dsimp [u]
    linarith [huppos i]
  let ε := ε₀ / 2
  have hε : 0 < ε := div_pos hε₀ (by norm_num)
  have hgapA : ∀ c : {c : Fin k // c ∉ pmNeighbourhood G a b},
      ε ≤ ∑ i, (G.L c.1 i - G.L a i) * u i := by
    intro c
    have hg := (hgapg c.1 c.2).1
    have hp0 : 0 ≤ ∑ i, (G.L c.1 i - G.L a i) * up i := by
      have h := hup.1.2 c.1
      have hid : (∑ i, (G.L c.1 i - G.L a i) * up i) =
          -(∑ i, (G.L a i - G.L c.1 i) * up i) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hid]
      linarith
    dsimp [ε, u]
    have havg : (∑ i, (G.L c.1 i - G.L a i) * ((ug i + up i) / 2)) =
        ((∑ i, (G.L c.1 i - G.L a i) * ug i) +
         (∑ i, (G.L c.1 i - G.L a i) * up i)) / 2 := by
      calc
        _ = (∑ i, ((G.L c.1 i - G.L a i) * ug i +
            (G.L c.1 i - G.L a i) * up i)) / 2 := by
              rw [Finset.sum_div]
              apply Finset.sum_congr rfl
              intro i _
              ring
        _ = _ := by rw [Finset.sum_add_distrib]
    rw [havg]
    linarith
  have hgapB : ∀ c : {c : Fin k // c ∉ pmNeighbourhood G a b},
      ε ≤ ∑ i, (G.L c.1 i - G.L b i) * u i := by
    intro c
    have hg := (hgapg c.1 c.2).2
    have hp0 : 0 ≤ ∑ i, (G.L c.1 i - G.L b i) * up i := by
      have h := hup.2.2 c.1
      have hid : (∑ i, (G.L c.1 i - G.L b i) * up i) =
          -(∑ i, (G.L b i - G.L c.1 i) * up i) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hid]
      linarith
    dsimp [ε, u]
    have havg : (∑ i, (G.L c.1 i - G.L b i) * ((ug i + up i) / 2)) =
        ((∑ i, (G.L c.1 i - G.L b i) * ug i) +
         (∑ i, (G.L c.1 i - G.L b i) * up i)) / 2 := by
      calc
        _ = (∑ i, ((G.L c.1 i - G.L b i) * ug i +
            (G.L c.1 i - G.L b i) * up i)) / 2 := by
              rw [Finset.sum_div]
              apply Finset.sum_congr rfl
              intro i _
              ring
        _ = _ := by rw [Finset.sum_add_distrib]
    rw [havg]
    linarith
  obtain ⟨δs, hδs, hsimp⟩ := stdSimplex_small_perturbation u q hu.1.1 hupos hqsum
  obtain ⟨δa, hδa, hstableA⟩ := finite_linear_gaps_stable
    (fun (c : {c : Fin k // c ∉ pmNeighbourhood G a b}) (i : Fin d) ↦
      G.L c.1 i - G.L a i)
    u (fun i ↦ -q i) ε hε hgapA
  obtain ⟨δb, hδb, hstableB⟩ := finite_linear_gaps_stable
    (fun (c : {c : Fin k // c ∉ pmNeighbourhood G a b}) (i : Fin d) ↦
      G.L c.1 i - G.L b i)
    u q ε hε hgapB
  let δ := min δs (min δa δb)
  have hδ : 0 < δ := lt_min hδs (lt_min hδa hδb)
  refine ⟨a, b, u, q, ε, δ, hab, hε, hδ, hqsum, hqnorm, ?_⟩
  intro Δ hΔ hΔδ
  dsimp only
  have hΔabs : |Δ| = Δ := abs_of_pos hΔ
  have hDs : |Δ| ≤ δs := by rw [hΔabs]; exact hΔδ.trans (min_le_left _ _)
  have hDa : |Δ| ≤ δa := by
    rw [hΔabs]
    exact hΔδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hDb : |Δ| ≤ δb := by
    rw [hΔabs]
    exact hΔδ.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hsplus := hsimp Δ hDs
  have hsminus := hsimp (-Δ) (by simpa [abs_neg] using hDs)
  have hA := hstableA Δ hDa
  have hB := hstableB Δ hDb
  have huv : ∑ i, (G.L a i - G.L b i) * u i = 0 := by
    have habu := hu.1.2 b
    have hbau := hu.2.2 a
    have hneg : (∑ i, (G.L b i - G.L a i) * u i) =
        -(∑ i, (G.L a i - G.L b i) * u i) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hneg] at hbau
    linarith
  have hbu : ∑ i, (G.L b i - G.L a i) * u i = 0 := by
    have hneg : (∑ i, (G.L b i - G.L a i) * u i) =
        -(∑ i, (G.L a i - G.L b i) * u i) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hneg, huv, neg_zero]
  have hbq : ∑ i, (G.L b i - G.L a i) * q i = -1 := by
    have hneg : (∑ i, (G.L b i - G.L a i) * q i) =
        -(∑ i, (G.L a i - G.L b i) * q i) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hneg, hqnorm]
  have huaS : (fun i ↦ u i - Δ * q i) ∈ stdSimplex ℝ (Fin d) := by
    convert hsminus using 1
    ext i
    ring
  have hubS : (fun i ↦ u i + Δ * q i) ∈ stdSimplex ℝ (Fin d) := hsplus
  have houtside : ∀ c : Fin k, c ∉ pmNeighbourhood G a b →
      ε / 2 ≤ ∑ i, (G.L c i - G.L a i) * (u i - Δ * q i) ∧
      ε / 2 ≤ ∑ i, (G.L c i - G.L b i) * (u i + Δ * q i) := by
    intro c hc
    constructor
    · have h := hA ⟨c, hc⟩
      convert h using 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring
    · exact hB ⟨c, hc⟩
  have hinsideA : ∀ c : Fin k, c ∈ pmNeighbourhood G a b →
      ∃ α : ℝ, 0 ≤ α ∧ α ≤ 1 ∧
        (∑ i, (G.L c i - G.L a i) * (u i - Δ * q i)) = (1 - α) * Δ := by
    intro c hc
    obtain ⟨α, hα0, hα1, hα⟩ :=
      partial_monitoring_neighbour_loss_interpolation G a b hab c hc
    refine ⟨α, hα0, hα1, ?_⟩
    calc
      (∑ i, (G.L c i - G.L a i) * (u i - Δ * q i)) =
          ∑ i, ((1 - α) * (G.L b i - G.L a i)) * (u i - Δ * q i) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [hα i]
            ring
      _ = (1 - α) * ∑ i, (G.L b i - G.L a i) * (u i - Δ * q i) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = (1 - α) *
          ((∑ i, (G.L b i - G.L a i) * u i) -
            Δ * ∑ i, (G.L b i - G.L a i) * q i) := by
            congr 1
            calc
              _ = ∑ i, ((G.L b i - G.L a i) * u i -
                  Δ * ((G.L b i - G.L a i) * q i)) := by
                    apply Finset.sum_congr rfl
                    intro i _
                    ring
              _ = _ := by rw [Finset.sum_sub_distrib, Finset.mul_sum]
      _ = (1 - α) * Δ := by rw [hbu, hbq]; ring
  have hinsideB : ∀ c : Fin k, c ∈ pmNeighbourhood G a b →
      ∃ α : ℝ, 0 ≤ α ∧ α ≤ 1 ∧
        (∑ i, (G.L c i - G.L b i) * (u i + Δ * q i)) = α * Δ := by
    intro c hc
    obtain ⟨α, hα0, hα1, hα⟩ :=
      partial_monitoring_neighbour_loss_interpolation G a b hab c hc
    refine ⟨α, hα0, hα1, ?_⟩
    calc
      (∑ i, (G.L c i - G.L b i) * (u i + Δ * q i)) =
          ∑ i, (α * (G.L a i - G.L b i)) * (u i + Δ * q i) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [hα i]
            ring
      _ = α * ∑ i, (G.L a i - G.L b i) * (u i + Δ * q i) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = α * ((∑ i, (G.L a i - G.L b i) * u i) +
            Δ * ∑ i, (G.L a i - G.L b i) * q i) := by
            congr 1
            calc
              _ = ∑ i, ((G.L a i - G.L b i) * u i +
                  Δ * ((G.L a i - G.L b i) * q i)) := by
                    apply Finset.sum_congr rfl
                    intro i _
                    ring
              _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = α * Δ := by rw [huv, hqnorm]; ring
  have hua : (fun i ↦ u i - Δ * q i) ∈ pmCell G a := by
    refine ⟨huaS, ?_⟩
    intro c
    by_cases hc : c ∈ pmNeighbourhood G a b
    · obtain ⟨α, hα0, hα1, hca⟩ := hinsideA c hc
      have hnonneg : 0 ≤ ∑ i, (G.L c i - G.L a i) * (u i - Δ * q i) := by
        rw [hca]
        exact mul_nonneg (sub_nonneg.mpr hα1) hΔ.le
      have hneg : (∑ i, (G.L a i - G.L c i) * (u i - Δ * q i)) =
          -(∑ i, (G.L c i - G.L a i) * (u i - Δ * q i)) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hneg]
      linarith
    · have hpos := (houtside c hc).1
      have hneg : (∑ i, (G.L a i - G.L c i) * (u i - Δ * q i)) =
          -(∑ i, (G.L c i - G.L a i) * (u i - Δ * q i)) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hneg]
      linarith [hε]
  have hub' : (fun i ↦ u i + Δ * q i) ∈ pmCell G b := by
    refine ⟨hubS, ?_⟩
    intro c
    by_cases hc : c ∈ pmNeighbourhood G a b
    · obtain ⟨α, hα0, hα1, hcb⟩ := hinsideB c hc
      have hnonneg : 0 ≤ ∑ i, (G.L c i - G.L b i) * (u i + Δ * q i) := by
        rw [hcb]
        exact mul_nonneg hα0 hΔ.le
      have hneg : (∑ i, (G.L b i - G.L c i) * (u i + Δ * q i)) =
          -(∑ i, (G.L c i - G.L b i) * (u i + Δ * q i)) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hneg]
      linarith
    · have hpos := (houtside c hc).2
      have hneg : (∑ i, (G.L b i - G.L c i) * (u i + Δ * q i)) =
          -(∑ i, (G.L c i - G.L b i) * (u i + Δ * q i)) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hneg]
      linarith [hε]
  refine ⟨hua, hub', houtside, ?_⟩
  intro c hc
  obtain ⟨α, -, -, hα⟩ :=
    partial_monitoring_neighbour_loss_interpolation G a b hab c hc
  calc
    (∑ i, (G.L c i - G.L a i) * (u i - Δ * q i)) +
        (∑ i, (G.L c i - G.L b i) * (u i + Δ * q i)) =
      ∑ i, (((2 * α - 1) * (G.L a i - G.L b i)) * u i +
        Δ * ((G.L a i - G.L b i) * q i)) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          rw [hα i]
          ring
    _ = (2 * α - 1) * (∑ i, (G.L a i - G.L b i) * u i) +
        Δ * (∑ i, (G.L a i - G.L b i) * q i) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
          congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring
    _ = Δ := by rw [huv, hqnorm]; ring

end BanditAlgorithm

theorem solution
    {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊] [DecidableEq 𝕊]
    (G : BanditAlgorithm.PartialMonitoringGame k d 𝕊) (a b : Fin k)
    (hab : BanditAlgorithm.NeighbouringActions G a b)
    (hout : ∃ c : Fin k, c ∉ BanditAlgorithm.pmNeighbourhood G a b) :
    ∃ a b : Fin k, ∃ u q : Fin d → ℝ, ∃ ε δ : ℝ,
      BanditAlgorithm.NeighbouringActions G a b ∧ 0 < ε ∧ 0 < δ ∧
      (∑ i, q i) = 0 ∧
      (∑ i, (G.L a i - G.L b i) * q i) = 1 ∧
      ∀ Δ : ℝ, 0 < Δ → Δ ≤ δ →
        let ua := fun i ↦ u i - Δ * q i
        let ub := fun i ↦ u i + Δ * q i
        ua ∈ BanditAlgorithm.pmCell G a ∧ ub ∈ BanditAlgorithm.pmCell G b ∧
        (∀ c : Fin k, c ∉ BanditAlgorithm.pmNeighbourhood G a b →
          ε / 2 ≤ ∑ i, (G.L c i - G.L a i) * ua i ∧
          ε / 2 ≤ ∑ i, (G.L c i - G.L b i) * ub i) ∧
        (∀ c : Fin k, c ∈ BanditAlgorithm.pmNeighbourhood G a b →
          (∑ i, (G.L c i - G.L a i) * ua i) +
          (∑ i, (G.L c i - G.L b i) * ub i) = Δ) :=
  BanditAlgorithm.partial_monitoring_easy_geometric_alternatives_of_outside
    G a b hab hout
