-- Prove2me | solution 1 for BellmanDP.ExistUnique.type_one_exists_unique
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-07T11:40:23.336439+00:00
-- url     : https://prove2.me/submissions/9955aedd-5198-4000-9a4d-fb049111a43f

import Mathlib
import Definitions.Def_BellmanDP_ExistUnique_SupEquation
import Definitions.Def_BellmanDP_ExistUnique_EquationTypes

open Filter Topology

namespace BellmanDP.ExistUnique

namespace T1Cex

abbrev E := EuclideanSpace ℝ (Fin 1)

variable {S : Type*} [Nonempty S]

noncomputable def gc : E → S → ℝ := fun p _ => if p = 0 then 0 else 1
def hc : E → S → ℝ := fun _ _ => 0
def Tc : E → S → E := fun _ _ => 0

lemma rs_zero : radialSup (Set.univ : Set E) (gc (S := S)) 0 = 0 := by
  unfold radialSup
  have : {x : ℝ | ∃ p ∈ (Set.univ : Set E), ‖p‖ ≤ 0 ∧ ∃ q : S, x = |gc p q|} = {0} := by
    ext x; simp only [Set.mem_setOf_eq, Set.mem_univ, true_and, Set.mem_singleton_iff]
    constructor
    · rintro ⟨p, hp, q, rfl⟩
      have : p = 0 := norm_le_zero_iff.mp hp
      simp [gc, this]
    · rintro rfl; exact ⟨0, by simp, Classical.arbitrary S, by simp [gc]⟩
  rw [this, csSup_singleton]

lemma typeOne : TypeOne (Set.univ : Set E) (gc (S := S)) hc Tc 0 where
  zero_mem := trivial
  mapsTo := fun _ _ _ => trivial
  g_bdd := fun _ => ⟨1, fun p _ _ _ => by unfold gc; split_ifs <;> simp⟩
  g_zero := fun _ => by simp [gc]
  h_le_one := fun _ _ _ => by simp [hc]
  a_nonneg := le_refl _
  a_lt_one := by norm_num
  T_le := fun _ _ _ => by simp [Tc]
  summable_v := by
    intro c _
    apply summable_of_ne_finset_zero (s := {0})
    intro n hn
    have : n ≠ 0 := by simpa using hn
    rw [zero_pow this, zero_mul, rs_zero]

theorem t1_core : ¬ ∃ f : E → ℝ,
      (ContinuousWithinAt f Set.univ 0 ∧ f 0 = 0 ∧ ∀ p ∈ (Set.univ : Set E), p ≠ 0 → SolvesAt (gc (S := S)) hc Tc f p) := by
  rintro ⟨f, hc0, hf0, hsol⟩
  have hone : ∀ p : E, p ≠ 0 → f p = 1 := by
    intro p hp
    have := hsol p trivial hp
    unfold SolvesAt at this
    have hr : Set.range (stageReturn (gc (S := S)) hc Tc f p) = {1} := by
      ext x; simp [stageReturn, gc, hc, hp, eq_comm]
    rw [hr] at this
    exact this.unique isLUB_singleton
  have hcont : ContinuousAt f 0 := by
    rw [← continuousWithinAt_univ]; exact hc0
  have h1 : Tendsto f (𝓝[≠] (0 : E)) (𝓝 (f 0)) := hcont.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto f (𝓝[≠] (0 : E)) (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with p hp
    exact (hone p hp).symm
  have := tendsto_nhds_unique h1 h2
  rw [hf0] at this
  norm_num at this

end T1Cex

end BellmanDP.ExistUnique

open BellmanDP.ExistUnique BellmanDP.ExistUnique.T1Cex

theorem solution : ¬ (∀ {N : ℕ} {S : Type} [Nonempty S]
    (D : Set (EuclideanSpace ℝ (Fin N))) (g h : EuclideanSpace ℝ (Fin N) → S → ℝ)
    (T : EuclideanSpace ℝ (Fin N) → S → EuclideanSpace ℝ (Fin N)) (a : ℝ) (hType : TypeOne D g h T a),
    ∃ f : EuclideanSpace ℝ (Fin N) → ℝ,
      (ContinuousWithinAt f D 0 ∧ f 0 = 0 ∧ ∀ p ∈ D, p ≠ 0 → SolvesAt g h T f p) ∧
      (∀ F : EuclideanSpace ℝ (Fin N) → ℝ, ContinuousWithinAt F D 0 → F 0 = 0 →
        (∀ p ∈ D, p ≠ 0 → SolvesAt g h T F p) → ∀ p ∈ D, F p = f p) ∧
      (∀ p ∈ D, Tendsto (fun n => succApprox g h T (supG g) n p) atTop (𝓝 (f p))) ∧
      (∀ f₀ : EuclideanSpace ℝ (Fin N) → ℝ, ContinuousWithinAt f₀ D 0 → f₀ 0 = 0 →
        BoundedOnBoundedParts D f₀ →
        ∀ p ∈ D, Tendsto (fun n => succApprox g h T f₀ n p) atTop (𝓝 (f p))) ∧
      (UnifContInP D g → UnifContInP D h → UnifContInP D T →
        ∀ c : ℝ, ContinuousOn f (D ∩ Metric.closedBall 0 c))) := by
  intro H
  obtain ⟨f, h1, -⟩ := H (S := Unit) (Set.univ : Set E) gc hc Tc 0 typeOne
  exact t1_core ⟨f, h1⟩
