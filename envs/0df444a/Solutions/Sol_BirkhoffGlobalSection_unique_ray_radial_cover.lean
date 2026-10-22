-- Prove2me | solution 1 for BirkhoffGlobalSection.unique_ray_radial_cover
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T17:46:24.505592+00:00
-- url     : https://prove2.me/submissions/3f97911f-cba2-451e-8dae-9d414b6dfc92

import Definitions.Def_BirkhoffGlobalSection
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

open BirkhoffGlobalSection

theorem solution (S : Set Phase)
    (hzero : (fun _ : Fin 4 => (0 : ℝ)) ∉ S)
    (hunique : ∀ x : {x : Phase // x ∈ unitThreeSphere},
      ∃! r : ℝ, 0 < r ∧
        (fun i : Fin 4 => r * (x : Phase) i) ∈ S) :
    S = Set.range (fun x : {x : Phase // x ∈ unitThreeSphere} =>
      (fun i : Fin 4 =>
        Classical.choose (hunique x).exists * (x : Phase) i)) := by
  apply Set.Subset.antisymm
  · intro s hs
    let E := EuclideanSpace ℝ (Fin 4)
    let e : E ≃L[ℝ] Phase := EuclideanSpace.equiv (Fin 4) ℝ
    let v : E := e.symm s
    let r : ℝ := ‖v‖
    have hsne : s ≠ (fun _ : Fin 4 => (0 : ℝ)) := by
      intro hz
      apply hzero
      simpa only [hz] using hs
    have hvne : v ≠ 0 := by
      intro hv
      apply hsne
      have he : e v = s := e.apply_symm_apply s
      rw [hv] at he
      funext i
      simpa using congrFun he.symm i
    have hr : 0 < r := norm_pos_iff.mpr hvne
    have hsum : r ^ 2 = zNormSq s + wNormSq s := by
      have h := EuclideanSpace.real_norm_sq_eq v
      have hcoords : (∑ i : Fin 4, s i ^ 2) = zNormSq s + wNormSq s := by
        simp [Fin.sum_univ_succ, zNormSq, wNormSq] <;> ring
      have hcoord (i : Fin 4) : v i = s i := by
        exact congrFun (e.apply_symm_apply s) i
      simp_rw [hcoord] at h
      exact h.trans hcoords
    let x : Phase := fun i => s i / r
    have hx : x ∈ unitThreeSphere := by
      change zNormSq x + wNormSq x = 1
      dsimp [x, zNormSq, wNormSq]
      dsimp [zNormSq, wNormSq] at hsum
      field_simp [hr.ne']
      nlinarith [hsum]
    let X : {x : Phase // x ∈ unitThreeSphere} := ⟨x, hx⟩
    have hray : (fun i : Fin 4 => r * (X : Phase) i) = s := by
      funext i
      dsimp [X, x]
      field_simp [hr.ne']
    have hchoice : Classical.choose (hunique X).exists = r := by
      exact (hunique X).unique
        (Classical.choose_spec (hunique X).exists) ⟨hr, by simpa only [hray] using hs⟩
    refine ⟨X, ?_⟩
    simpa only [hchoice] using hray
  · rintro s ⟨x, rfl⟩
    exact (Classical.choose_spec (hunique x).exists).2
