-- Prove2me | solution 1 for Disjunctive.GeneralDisjunctions.lp_cut_equals_intersection_cut
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T19:34:25.517775+00:00
-- url     : https://prove2.me/submissions/cbc2add5-b62f-459f-947f-a84915b4c337

import Mathlib
import Definitions.Def_Disjunctive_GeneralDisjunctions_Basic
import Definitions.Def_Disjunctive_GeneralDisjunctions_Cglp

open Disjunctive.GeneralDisjunctions

theorem solution : ¬ (∀ {n : ℕ} {M T : Type} [Fintype M] [Fintype T]
    [Nonempty T] [DecidableEq M] [DecidableEq (Fin n)]
    (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (d : T → Fin n → ℝ) (d0 : T → ℝ)
    (α : Fin n → ℝ) (β : ℝ) (u : T → M → ℝ) (u0 : T → ℝ)
    (hfeas : IsCGLP116Feasible Atil btil d d0 α u u0 β)
    (hu0pos : ∀ t, 0 < u0 t)
    (ι : Fin n → M) (hι_inj : Function.Injective ι)
    (hnonsing : IsUnit (Ahat Atil ι).det)
    (hsupp : ∀ t, ∀ i, i ∉ Finset.image ι Finset.univ → u t i = 0),
    {x | β ≤ dotProduct α x} = IntersectionCutFromS Atil btil ι d d0) := by
  intro h
  have hfeas : IsCGLP116Feasible (1 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ => 0)
      (fun (_ : Fin 1) (_ : Fin 1) => (1 : ℝ)) (fun (_ : Fin 1) => (1 : ℝ)) (fun _ => 1)
      (fun (_ : Fin 1) (_ : Fin 1) => (1 / 2 : ℝ)) (fun (_ : Fin 1) => (1 / 2 : ℝ)) (1 / 2) := by
    refine ⟨fun t => ?_, fun t => ?_, ?_, fun t i => by norm_num, fun t => by norm_num⟩
    · funext i; fin_cases i; simp [Matrix.vecMul, dotProduct]; norm_num
    · simp [dotProduct]
    · simp; norm_num
  have hAhat : Ahat (1 : Matrix (Fin 1) (Fin 1) ℝ) id = 1 := by
    ext i j; rfl
  have key := h (1 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ => 0)
    (fun (_ : Fin 1) (_ : Fin 1) => (1 : ℝ)) (fun (_ : Fin 1) => (1 : ℝ))
    (fun _ => 1) (1 / 2) (fun (_ : Fin 1) (_ : Fin 1) => (1 / 2 : ℝ)) (fun (_ : Fin 1) => (1 / 2 : ℝ)) hfeas (fun _ => by norm_num)
    id Function.injective_id (by rw [hAhat]; simp)
    (fun t i hi => absurd (Finset.mem_image_of_mem id (Finset.mem_univ i)) hi)
  have hx : (fun _ => (3 / 4 : ℝ)) ∈ {x : Fin 1 → ℝ | (1 / 2 : ℝ) ≤ dotProduct (fun _ => 1) x} := by
    simp [dotProduct]; norm_num
  rw [key] at hx
  simp [IntersectionCutFromS, piCoef, piT, Abar, Abar0, SurplusM, hAhat, Bhat, dotProduct] at hx
  simp [Matrix.one_apply] at hx
  norm_num at hx

#print axioms solution
