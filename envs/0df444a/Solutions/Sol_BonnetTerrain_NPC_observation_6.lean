-- Prove2me | solution 1 for BonnetTerrain.NPC.observation_6
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-29T04:33:03.731966+00:00
-- url     : https://prove2.me/submissions/4e1998b2-ad04-437b-9fab-3c5564234bc7

import Mathlib
import Definitions.Def_BonnetTerrain_NPC_Geometry

open BonnetTerrain.NPC

noncomputable abbrev s225T : Chain := ⟨2, ![((0:ℝ), (1:ℝ)), (0, 0), (1, 0)]⟩

theorem s225_carrier (p : Point) : p ∈ s225T.carrier ↔
    (p.1 = 0 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1) ∨ (p.2 = 0 ∧ 0 ≤ p.1 ∧ p.1 ≤ 1) := by
  constructor
  · rintro (⟨i, rfl⟩ | ⟨i, t, ht0, ht1, rfl⟩)
    · fin_cases i <;> simp [s225T]
    · fin_cases i
      · left; simp [s225T]; constructor <;> linarith
      · right; simp [s225T]; exact ⟨ht0, ht1⟩
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · right; refine ⟨0, 1 - p.2, by linarith, by linarith, ?_⟩
      ext <;> simp [s225T, h1]
    · right; refine ⟨1, p.1, h2, h3, ?_⟩
      ext <;> simp [s225T, h1]

theorem solution : ¬ (∀ (T : BonnetTerrain.NPC.Chain) (hT : T.IsTerrain) (hO : T.IsOrthogonal)
    (S : Finset (Fin (T.edgeCount + 1))) (hS : T.Guards S),
    T.GuardsDownward S) := by
  intro H
  have hT : s225T.IsTerrain := by
    refine ⟨?_, ?_, ?_⟩
    · intro i j h
      fin_cases i <;> fin_cases j <;> simp [s225T, Prod.ext_iff] at h ⊢
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp [s225T, Fin.le_def] at hij ⊢
    · intro i j hij p hp1 hp2
      fin_cases i <;> fin_cases j <;> simp [Fin.lt_def] at hij
      obtain ⟨t, ht0, ht1, rfl⟩ := hp1
      obtain ⟨u, hu0, hu1, hu⟩ := hp2
      simp [s225T, Prod.ext_iff] at hu ⊢
      first | exact hu.2 | exact ⟨rfl, hu.2⟩ | linarith [hu.2]
  have hO : s225T.IsOrthogonal := by
    intro i; fin_cases i <;> simp [s225T]
  have hS : s225T.Guards {1} := by
    intro p hp
    refine ⟨1, Finset.mem_singleton_self _, (s225_carrier _).mpr (Or.inl ⟨by simp [s225T],
      by simp [s225T], by simp [s225T]⟩), hp, ?_⟩
    rintro q ⟨t, ht0, ht1, rfl⟩
    have hq : ((1 - t) * (s225T.vertex 1).1 + t * p.1, (1 - t) * (s225T.vertex 1).2 + t * p.2)
        ∈ s225T.carrier := by
      rw [s225_carrier] at hp ⊢
      simp only [s225T, Matrix.cons_val_one, Matrix.cons_val_zero, mul_zero, zero_add]
      rcases hp with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · left; refine ⟨by simp [h1], mul_nonneg ht0 h2, by nlinarith [mul_le_mul ht1 h3 h2 zero_le_one]⟩
      · right; refine ⟨by simp [h1], mul_nonneg ht0 h2, by nlinarith [mul_le_mul ht1 h3 h2 zero_le_one]⟩
    exact ⟨_, hq, rfl, le_rfl⟩
  have := H s225T hT hO {1} hS
  obtain ⟨i, hi, -, hle⟩ := this (s225T.vertex 0) (Or.inl ⟨0, rfl⟩)
  rw [Finset.mem_singleton] at hi
  subst hi
  simp [s225T] at hle
  norm_num at hle
