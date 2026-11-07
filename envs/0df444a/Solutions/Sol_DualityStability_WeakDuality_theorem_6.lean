-- Prove2me | solution 1 for DualityStability.WeakDuality.theorem_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T12:41:05.366801+00:00
-- url     : https://prove2.me/submissions/66bcc0be-c17e-4f31-b23b-58e89df95f0d

import Theorems.Thm_DualityStability_WeakDuality_hull_lsc_convex
import Theorems.Thm_DualityStability_WeakDuality_hull_conjugate_identity
import Theorems.Thm_DualityStability_WeakDuality_biconjugation_at_zero
import Theorems.Thm_DualityStability_WeakDuality_improper_case

open DualityStability.WeakDuality

variable {E E' F F' : Type*}
variable [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
variable [AddCommGroup E'] [Module ℝ E'] [TopologicalSpace E']
  [IsTopologicalAddGroup E'] [ContinuousSMul ℝ E'] [LocallyConvexSpace ℝ E'] [T2Space E']
variable [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
variable [AddCommGroup F'] [Module ℝ F'] [TopologicalSpace F']
  [IsTopologicalAddGroup F'] [ContinuousSMul ℝ F'] [LocallyConvexSpace ℝ F'] [T2Space F']

theorem solution (P : Problem E E' F F')
    (hexception : ¬ (P.dualSup = ⊥ ∧ Filter.liminf P.perturbation (nhds 0) = ⊤)) :
    P.dualSup = Filter.liminf P.perturbation (nhds 0) := by
  change P.dualSup = P.hull 0
  by_cases hp : Proper P.hull
  · rw [biconjugation_at_zero P hp, Problem.dualSup]
    congr 1
    funext y'
    have h1 := hull_conjugate_identity P y'
    rw [map_zero, LinearMap.zero_apply, EReal.coe_zero, zero_sub, h1.1, h1.2.1, h1.2.2]
  · have hbot : P.dualSup = ⊥ := by
      rw [Problem.dualSup]; simp [improper_case P hp]
    rw [hbot]
    have hne : P.hull 0 ≠ ⊤ := fun h => hexception ⟨hbot, h⟩
    obtain ⟨y0, hy0⟩ : ∃ y0, P.hull y0 = ⊥ := by
      by_contra hcon
      push_neg at hcon
      exact hp ⟨hcon, ⟨0, hne⟩⟩
    obtain ⟨hlsc, hconv⟩ := hull_lsc_convex P
    by_contra hb
    have hb' : P.hull 0 ≠ ⊥ := fun h => hb h.symm
    obtain ⟨c, hc⟩ : ∃ c : ℝ, P.hull 0 = c := ⟨(P.hull 0).toReal, (EReal.coe_toReal hne hb').symm⟩
    have hev := hlsc 0 ((c - 1 : ℝ) : EReal) (by show (((c - 1 : ℝ) : EReal)) < P.hull 0; rw [hc]; exact_mod_cast (by linarith : c - 1 < c))
    have htend : Filter.Tendsto (fun t : ℝ => t • y0) (nhdsWithin 0 (Set.Ioo 0 1)) (nhds 0) := by
      have : Filter.Tendsto (fun t : ℝ => t • y0) (nhds 0) (nhds ((0:ℝ) • y0)) :=
        (continuous_id.smul continuous_const).tendsto 0
      rw [zero_smul] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hmem : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioo 0 1), t ∈ Set.Ioo (0:ℝ) 1 :=
      self_mem_nhdsWithin
    haveI : (nhdsWithin (0:ℝ) (Set.Ioo 0 1)).NeBot := left_nhdsWithin_Ioo_neBot zero_lt_one
    obtain ⟨t, ht1, ⟨ht0, ht1'⟩⟩ := ((htend.eventually hev).and hmem).exists
    -- convexity: hull (t • y0) ≤ c - 2
    set μ : ℝ := ((c - 2) - (1 - t) * c) / t with hμ
    have hA : (y0, μ) ∈ {p : F × ℝ | P.hull p.1 ≤ (p.2 : EReal)} := by
      simp [hy0]
    have hB : ((0:F), c) ∈ {p : F × ℝ | P.hull p.1 ≤ (p.2 : EReal)} := by
      simp [hc]
    have hC := hconv hA hB ht0.le (by linarith : (0:ℝ) ≤ 1 - t) (by ring)
    simp only [Set.mem_setOf_eq, Prod.smul_mk, Prod.mk_add_mk, smul_zero, add_zero,
      smul_eq_mul] at hC
    have heq : t * μ + (1 - t) * c = c - 2 := by
      rw [hμ]; field_simp; ring
    rw [heq] at hC
    have := lt_of_lt_of_le ht1 hC
    have : (c - 1 : ℝ) < c - 2 := by exact_mod_cast this
    linarith

