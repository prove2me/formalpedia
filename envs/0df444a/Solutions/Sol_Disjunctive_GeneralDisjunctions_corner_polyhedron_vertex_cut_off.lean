-- Prove2me | solution 1 for Disjunctive.GeneralDisjunctions.corner_polyhedron_vertex_cut_off
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:20:29.984075+00:00
-- url     : https://prove2.me/submissions/385ea083-9257-4051-890f-afb4d8ea1be5

import Mathlib
import Definitions.Def_Disjunctive_GeneralDisjunctions_Basic
import Definitions.Def_Disjunctive_GeneralDisjunctions_Corner

open Disjunctive.GeneralDisjunctions

theorem solution : ¬ (∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (I J : Finset ι) (abar : ι → ι → ℝ) (w : ι → ℝ) (Nprime : Finset ι) (PI : Set (ι → ℝ))
    (v : ι → ℝ) (hv : v ∈ Set.extremePoints ℝ (cornerPolyhedron I J abar w Nprime))
    (hvPI : v ∉ convexHull ℝ PI),
    ∃ (I' J' : Finset ι) (abar' : ι → ι → ℝ) (S : Set (ι → ℝ)) (lam : ι → ℝ),
      (∀ j ∈ J', v j = 0) ∧ PIFree S PI v ∧
        (∀ j ∈ J', IsGreatest {t : ℝ | v + t • extremeRay I' abar' j ∈ S} (lam j)) ∧
        PI ⊆ IntersectionCutSet J' lam ∧ v ∉ IntersectionCutSet J' lam) := by
  intro h
  set PI : Set (Fin 1 → ℝ) := {x | 0 < x 0} with hPI
  have hray : ∀ (I' : Finset (Fin 1)) (abar' : Fin 1 → Fin 1 → ℝ) (j : Fin 1),
      extremeRay I' abar' j = fun _ => 1 := by
    intro I' abar' j
    funext i
    have : i = j := Subsingleton.elim _ _
    simp [extremeRay, this]
  set C := cornerPolyhedron (∅ : Finset (Fin 1)) Finset.univ 0 0 ∅ with hC
  have hCsub : C ⊆ {x | 0 ≤ x 0} := by
    apply convexHull_min
    · rintro x ⟨⟨lam, hlam, rfl⟩, -⟩
      simp [hray, hlam 0 (Finset.mem_univ 0)]
    · intro a ha b hb s t hs ht _
      simp only [Set.mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ha hb ⊢
      positivity
  have h0C : (0 : Fin 1 → ℝ) ∈ C := by
    apply subset_convexHull
    refine ⟨⟨0, fun _ _ => le_rfl, by simp⟩, fun j hj => by simp at hj⟩
  have hv : (0 : Fin 1 → ℝ) ∈ Set.extremePoints ℝ C := by
    refine ⟨h0C, fun a ha b hb hab => ?_⟩
    obtain ⟨s, t, hs, ht, hst, hsum⟩ := hab
    have ha0 : 0 ≤ a 0 := hCsub ha
    have hb0 : 0 ≤ b 0 := hCsub hb
    have e0 := congrFun hsum 0
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e0
    have : a 0 = 0 := by nlinarith
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    simpa using this
  have hvPI : (0 : Fin 1 → ℝ) ∉ convexHull ℝ PI := by
    have hconv : Convex ℝ PI := by
      intro a ha b hb s t hs ht hst
      simp only [hPI, Set.mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ha hb ⊢
      rcases hs.lt_or_eq with hs' | hs'
      · nlinarith
      · subst hs'; simp at hst; subst hst; simpa using hb
    rw [hconv.convexHull_eq]
    simp [hPI]
  obtain ⟨I', J', abar', S, lam, -, ⟨-, hvint, -⟩, hgreat, hsub, -⟩ :=
    h (ι := Fin 1) ∅ Finset.univ 0 0 ∅ PI 0 hv hvPI
  by_cases hJ : (0 : Fin 1) ∈ J'
  · obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hvint)
    have hmem : ε / 2 ∈ {t : ℝ | (0 : Fin 1 → ℝ) + t • extremeRay I' abar' 0 ∈ S} := by
      apply hball
      rw [hray, Metric.mem_ball, zero_add, dist_zero_right]
      have : ‖(ε / 2) • (fun _ => (1 : ℝ) : Fin 1 → ℝ)‖ = ε / 2 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
        simp
      rw [this]; linarith
    have hlam : ε / 2 ≤ lam 0 := (hgreat 0 hJ).2 hmem
    have hlampos : 0 < lam 0 := by linarith
    have hx : (fun _ => lam 0 / 2 : Fin 1 → ℝ) ∈ PI := by
      simp only [hPI, Set.mem_setOf_eq]; linarith
    have := hsub hx
    simp only [IntersectionCutSet, Set.mem_setOf_eq] at this
    rw [Finset.sum_eq_single (0 : Fin 1) (fun b _ hb => absurd (Subsingleton.elim b 0) hb)
      (fun h' => absurd hJ h')] at this
    field_simp at this
    linarith
  · have hJe : J' = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro j hj
      exact hJ (by simpa [Subsingleton.elim j 0] using hj)
    have hx : (fun _ => 1 : Fin 1 → ℝ) ∈ PI := by simp [hPI]
    have := hsub hx
    simp [IntersectionCutSet, hJe] at this
    linarith

#print axioms solution
