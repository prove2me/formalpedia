-- Prove2me | solution 1 for BanditAlgorithm.partial_monitoring_uniform_outside_gap
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-05T17:29:06.494046+00:00
-- url     : https://prove2.me/submissions/6d20fc5e-5a16-476e-b29b-1a0ee17eef85

import Definitions.Def_PartialMonitoringGame
import Theorems.Thm_BanditAlgorithm_partial_monitoring_outside_neighbourhood_strict_gap
import Mathlib.Analysis.Convex.Combination
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

open Set

namespace BanditAlgorithm

theorem convex_pmCell {k d : ℕ} {𝕊 : Type*}
    (G : PartialMonitoringGame k d 𝕊) (a : Fin k) :
    Convex ℝ (pmCell G a) := by
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
Lattimore--Szepesvari, *Bandit Algorithms*, Theorem 37.12, Step 1,
printed pp.488--489, Eq. (37.5).  Averaging one strict-gap witness for each
action outside `N_ab` produces a single point of the common cell with a
uniform positive gap to every outside action.
-/

theorem partial_monitoring_uniform_outside_gap
    {k d : ℕ} {𝕊 : Type*} (G : PartialMonitoringGame k d 𝕊)
    (a b : Fin k) (hout : ∃ c : Fin k, c ∉ pmNeighbourhood G a b) :
    ∃ u ∈ pmCell G a ∩ pmCell G b, ∃ ε : ℝ, 0 < ε ∧
      ∀ c : Fin k, c ∉ pmNeighbourhood G a b →
        ε ≤ ∑ i, (G.L c i - G.L a i) * u i ∧
        ε ≤ ∑ i, (G.L c i - G.L b i) * u i := by
  classical
  let O := {c : Fin k // c ∉ pmNeighbourhood G a b}
  haveI : Nonempty O := by
    obtain ⟨c, hc⟩ := hout
    exact ⟨⟨c, hc⟩⟩
  have hwit : ∀ c : O, ∃ u ∈ pmCell G a ∩ pmCell G b,
      0 < ∑ i, (G.L c.1 i - G.L a i) * u i ∧
      0 < ∑ i, (G.L c.1 i - G.L b i) * u i := by
    intro c
    exact partial_monitoring_outside_neighbourhood_strict_gap G a b c.1 c.2
  choose z hzmem hzgapa hzgapb using hwit
  let u : Fin d → ℝ :=
    (Finset.univ : Finset O).centerMass (fun _ ↦ (1 : ℝ)) z
  have hu : u ∈ pmCell G a ∩ pmCell G b := by
    apply (convex_pmCell G a).inter (convex_pmCell G b) |>.centerMass_mem
    · intro c _
      norm_num
    · simpa using (Fintype.card_pos : 0 < Fintype.card O)
    · intro c _
      exact hzmem c
  have hgapA : ∀ c : O, 0 < ∑ i, (G.L c.1 i - G.L a i) * u i := by
    intro c
    have hnonneg : ∀ x : O, 0 ≤ ∑ i, (G.L c.1 i - G.L a i) * z x i := by
      intro x
      have := (hzmem x).1.2 c.1
      have hid : (∑ i, (G.L c.1 i - G.L a i) * z x i) =
          -(∑ i, (G.L a i - G.L c.1 i) * z x i) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hid]
      linarith
    have hsumpos : 0 < ∑ x : O, ∑ i, (G.L c.1 i - G.L a i) * z x i := by
      exact Finset.sum_pos' (fun x _ ↦ hnonneg x) ⟨c, Finset.mem_univ _, hzgapa c⟩
    have hcard : 0 < (Fintype.card O : ℝ) := by positivity
    have hformula : (∑ i, (G.L c.1 i - G.L a i) * u i) =
        (Fintype.card O : ℝ)⁻¹ *
          ∑ x : O, ∑ i, (G.L c.1 i - G.L a i) * z x i := by
      simp only [u, Finset.centerMass, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_one, one_smul]
      simp_rw [Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
      calc
        (∑ i, (G.L c.1 i - G.L a i) *
            ((Fintype.card O : ℝ)⁻¹ * ∑ x : O, z x i)) =
            ∑ i, (Fintype.card O : ℝ)⁻¹ *
              ∑ x : O, (G.L c.1 i - G.L a i) * z x i := by
                apply Finset.sum_congr rfl
                intro i _
                rw [Finset.mul_sum]
                rw [Finset.mul_sum, Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro x _
                ring
        _ = (Fintype.card O : ℝ)⁻¹ *
              ∑ i, ∑ x : O, (G.L c.1 i - G.L a i) * z x i := by
                rw [Finset.mul_sum]
        _ = _ := by rw [Finset.sum_comm]
    rw [hformula]
    positivity
  have hgapB : ∀ c : O, 0 < ∑ i, (G.L c.1 i - G.L b i) * u i := by
    intro c
    have hnonneg : ∀ x : O, 0 ≤ ∑ i, (G.L c.1 i - G.L b i) * z x i := by
      intro x
      have := (hzmem x).2.2 c.1
      have hid : (∑ i, (G.L c.1 i - G.L b i) * z x i) =
          -(∑ i, (G.L b i - G.L c.1 i) * z x i) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hid]
      linarith
    have hsumpos : 0 < ∑ x : O, ∑ i, (G.L c.1 i - G.L b i) * z x i := by
      exact Finset.sum_pos' (fun x _ ↦ hnonneg x) ⟨c, Finset.mem_univ _, hzgapb c⟩
    have hcard : 0 < (Fintype.card O : ℝ) := by positivity
    have hformula : (∑ i, (G.L c.1 i - G.L b i) * u i) =
        (Fintype.card O : ℝ)⁻¹ *
          ∑ x : O, ∑ i, (G.L c.1 i - G.L b i) * z x i := by
      simp only [u, Finset.centerMass, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_one, one_smul]
      simp_rw [Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
      calc
        (∑ i, (G.L c.1 i - G.L b i) *
            ((Fintype.card O : ℝ)⁻¹ * ∑ x : O, z x i)) =
            ∑ i, (Fintype.card O : ℝ)⁻¹ *
              ∑ x : O, (G.L c.1 i - G.L b i) * z x i := by
                apply Finset.sum_congr rfl
                intro i _
                rw [Finset.mul_sum]
                rw [Finset.mul_sum, Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro x _
                ring
        _ = (Fintype.card O : ℝ)⁻¹ *
              ∑ i, ∑ x : O, (G.L c.1 i - G.L b i) * z x i := by
                rw [Finset.mul_sum]
        _ = _ := by rw [Finset.sum_comm]
    rw [hformula]
    positivity
  let gaps : Finset ℝ :=
    (Finset.univ.image fun c : O ↦ ∑ i, (G.L c.1 i - G.L a i) * u i) ∪
    (Finset.univ.image fun c : O ↦ ∑ i, (G.L c.1 i - G.L b i) * u i)
  have hgaps : gaps.Nonempty := by
    apply Finset.union_nonempty.mpr
    left
    exact Finset.image_nonempty.mpr Finset.univ_nonempty
  let ε := gaps.min' hgaps
  have hε : 0 < ε := by
    apply (Finset.lt_min'_iff gaps hgaps).2
    intro r hr
    rcases Finset.mem_union.mp hr with hr | hr
    · obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hr
      exact hgapA c
    · obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hr
      exact hgapB c
  refine ⟨u, hu, ε, hε, ?_⟩
  intro c hc
  let cO : O := ⟨c, hc⟩
  constructor
  · apply Finset.min'_le
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨cO, Finset.mem_univ _, rfl⟩
  · apply Finset.min'_le
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨cO, Finset.mem_univ _, rfl⟩

end BanditAlgorithm

theorem solution
    {k d : ℕ} {𝕊 : Type*}
    (G : BanditAlgorithm.PartialMonitoringGame k d 𝕊)
    (a b : Fin k)
    (hout : ∃ c : Fin k, c ∉ BanditAlgorithm.pmNeighbourhood G a b) :
    ∃ u ∈ BanditAlgorithm.pmCell G a ∩ BanditAlgorithm.pmCell G b,
      ∃ ε : ℝ, 0 < ε ∧
      ∀ c : Fin k, c ∉ BanditAlgorithm.pmNeighbourhood G a b →
        ε ≤ ∑ i, (G.L c i - G.L a i) * u i ∧
        ε ≤ ∑ i, (G.L c i - G.L b i) * u i :=
  BanditAlgorithm.partial_monitoring_uniform_outside_gap G a b hout
