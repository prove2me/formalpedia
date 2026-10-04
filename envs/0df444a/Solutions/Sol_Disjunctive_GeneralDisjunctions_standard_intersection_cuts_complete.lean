-- Prove2me | solution 1 for Disjunctive.GeneralDisjunctions.standard_intersection_cuts_complete
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:33:23.441978+00:00
-- url     : https://prove2.me/submissions/73fdc262-6cfa-4272-946b-2993d6ed9f98

import Mathlib
import Definitions.Def_Disjunctive_GeneralDisjunctions_Basic

open Disjunctive.GeneralDisjunctions

theorem solution : ¬ (∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (I J : Finset ι) (abar : ι → ι → ℝ) (v : ι → ℝ) (PI P : Set (ι → ℝ))
    (phi : ι → ℝ) (phi0 : ℝ) (lam : ι → ℝ)
    (hvP : v ∈ Set.extremePoints ℝ P) (hvJ : ∀ j ∈ J, v j = 0)
    (hPIsub : PI ⊆ P) (hPcone : ∀ x ∈ P, ∀ j ∈ J, 0 ≤ x j)
    (hvalid : ∀ x ∈ PI, phi0 ≤ dotProduct phi x)
    (hviolated : ∃ x ∈ P, dotProduct phi x < phi0)
    (hcutoff : dotProduct phi v < phi0)
    (hfacet : IsFacet (convexHull ℝ PI) {x ∈ convexHull ℝ PI | dotProduct phi x = phi0})
    (hlam_exit : ∀ j ∈ J,
      IsGreatest {t : ℝ | dotProduct phi (v + t • extremeRay I abar j) ≤ phi0} (lam j)),
    PIFree {x | dotProduct phi x ≤ phi0} PI v ∧
      IntersectionCutSet J lam = {x | phi0 ≤ dotProduct phi x}) := by
  intro h
  set P : Set (Fin 2 → ℝ) := {x | x 0 = 0 ∧ 0 ≤ x 1} with hP
  set PI : Set (Fin 2 → ℝ) := {x | x 0 = 0 ∧ 1 ≤ x 1} with hPI
  set phi : Fin 2 → ℝ := fun _ => 1 with hphi
  have hdot : ∀ x : Fin 2 → ℝ, dotProduct phi x = x 0 + x 1 := by
    intro x; simp [hphi, dotProduct, Fin.sum_univ_two]
  have hray : extremeRay ({0} : Finset (Fin 2)) 0 1 = ![0, 1] := by
    funext i; fin_cases i <;> simp [extremeRay]
  have hPIconv : Convex ℝ PI := by
    intro a ha b hb s t hs ht hst
    obtain ⟨ha0, ha1⟩ := ha
    obtain ⟨hb0, hb1⟩ := hb
    refine ⟨by simp [ha0, hb0], ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith
  have hvP : (0 : Fin 2 → ℝ) ∈ Set.extremePoints ℝ P := by
    refine ⟨⟨rfl, le_rfl⟩, fun a ha b hb hab => ?_⟩
    obtain ⟨s, t, hs, ht, hst, hsum⟩ := hab
    have e1 := congrFun hsum 1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e1
    have : a 1 = 0 := by nlinarith [ha.2, hb.2]
    funext i; fin_cases i
    · exact ha.1
    · exact this
  have hF : {x ∈ convexHull ℝ PI | dotProduct phi x = 1} = {![0, 1]} := by
    rw [hPIconv.convexHull_eq]
    ext x
    simp only [Set.mem_setOf_eq, hPI, hdot, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨h0, h1⟩, hs⟩
      funext i; fin_cases i <;> simp <;> linarith
    · rintro rfl; simp
  have hdimPI : PolyDim PI = 1 := by
    have hne : PI.Nonempty := ⟨![0, 1], by simp [hPI]⟩
    rw [PolyDim, if_pos hne]
    have : vectorSpan ℝ PI = Submodule.span ℝ {(![0, 1] : Fin 2 → ℝ)} := by
      apply le_antisymm
      · rw [vectorSpan_def, Submodule.span_le]
        rintro _ ⟨x, ⟨hx0, -⟩, y, ⟨hy0, -⟩, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_span_singleton]
        refine ⟨x 1 - y 1, ?_⟩
        funext i; fin_cases i <;> simp [hx0, hy0]
      · rw [Submodule.span_le, Set.singleton_subset_iff, vectorSpan_def]
        apply Submodule.subset_span
        refine ⟨![0, 2], by simp [hPI], ![0, 1], by simp [hPI], ?_⟩
        funext i; fin_cases i <;> simp <;> norm_num
    rw [this, finrank_span_singleton]
    · rfl
    · intro h0; have := congrFun h0 1; simp at this
  have hfacet : IsFacet (convexHull ℝ PI) {x ∈ convexHull ℝ PI | dotProduct phi x = 1} := by
    refine ⟨⟨fun x hx => hx.1, ?_⟩, ?_, ?_⟩
    · rintro a ha b hb x hx ⟨s, t, hs, ht, hst, rfl⟩
      rw [hPIconv.convexHull_eq] at ha hb
      rw [hF] at hx
      have hx1 := congrFun hx 1
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx1
      simp at hx1
      have : a 1 = 1 := by nlinarith [ha.2, hb.2]
      refine ⟨by rw [hPIconv.convexHull_eq]; exact ha, ?_⟩
      rw [hdot, ha.1, this]; norm_num
    · rw [hF]; exact Set.singleton_nonempty _
    · rw [hF, hPIconv.convexHull_eq, hdimPI, PolyDim, if_pos (Set.singleton_nonempty _),
        vectorSpan_singleton, finrank_bot]
      norm_num
  have key := (h (ι := Fin 2) {0} {1} 0 0 PI P phi 1 (fun _ => 1) hvP
    (fun j hj => by simp at hj; subst hj; rfl)
    (fun x hx => ⟨hx.1, by linarith [hx.2]⟩)
    (fun x hx j hj => by simp at hj; subst hj; exact hx.2)
    (fun x hx => by rw [hdot, hx.1]; linarith [hx.2])
    ⟨0, ⟨rfl, le_rfl⟩, by simp [hdot]⟩ (by simp [hdot]) hfacet
    (fun j hj => by
      simp at hj; subst hj
      rw [hray]
      refine ⟨by simp [hdot], fun t ht => ?_⟩
      simp only [Set.mem_setOf_eq, hdot] at ht
      simpa using ht)).2
  have hmem : (![1, 1 / 2] : Fin 2 → ℝ) ∈ {x : Fin 2 → ℝ | 1 ≤ dotProduct phi x} := by
    simp only [Set.mem_setOf_eq, hdot]; norm_num
  rw [← key] at hmem
  simp [IntersectionCutSet] at hmem
  norm_num at hmem

#print axioms solution
