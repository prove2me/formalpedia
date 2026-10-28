-- Prove2me | solution 1 for DaiWeissFluid.LuKumar.theta_choice
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T13:54:05.586982+00:00
-- url     : https://prove2.me/submissions/3dd7e0ad-7f7e-4c57-bda5-b6c893d0395a

import Mathlib
import Definitions.Def_DaiWeissFluid_LuKumar_FluidModel
import Definitions.Def_DaiWeissFluid_LuKumar_Network

open DaiWeissFluid.LuKumar in
theorem solution (m : Fin 4 → ℝ) (hm : ∀ k, 0 < m k)
    (h51₁ : m 0 + m 3 < 1) (h51₂ : m 1 + m 2 < 1)
    (h52 : m 1 + m 3 < 1) :
    let δ1 := (1 - m 0 - m 3) / 2
    let δ2 := (1 - m 1 - m 2) / 2
    let δ3 := (1 - m 1 - m 3) / 3
    let θ1 := 1 - m 3 - min δ1 δ3
    let θ2 := m 1 + min δ2 δ3
    0 < δ1 ∧ 0 < δ2 ∧ 0 < δ3 ∧
    m 0 < θ1 ∧ θ1 < 1 - m 3 ∧
    m 1 < θ2 ∧ θ2 < 1 - m 2 ∧ θ2 ≤ θ1 := by
  intro δ1 δ2 δ3 θ1 θ2
  have e1 : δ1 = (1 - m 0 - m 3) / 2 := rfl
  have e2 : δ2 = (1 - m 1 - m 2) / 2 := rfl
  have e3 : δ3 = (1 - m 1 - m 3) / 3 := rfl
  have f1 : θ1 = 1 - m 3 - min δ1 δ3 := rfl
  have f2 : θ2 = m 1 + min δ2 δ3 := rfl
  have a1 := min_le_left δ1 δ3
  have a2 := min_le_right δ1 δ3
  have b1 := min_le_left δ2 δ3
  have b2 := min_le_right δ2 δ3
  have p1 : 0 < δ1 := by rw [e1]; linarith
  have p2 : 0 < δ2 := by rw [e2]; linarith
  have p3 : 0 < δ3 := by rw [e3]; linarith
  have q1 : 0 < min δ1 δ3 := lt_min p1 p3
  have q2 : 0 < min δ2 δ3 := lt_min p2 p3
  refine ⟨p1, p2, p3, ?_, ?_, ?_, ?_, ?_⟩
  · rw [f1]; rw [e1] at a1; linarith
  · rw [f1]; linarith
  · rw [f2]; linarith
  · rw [f2]; rw [e2] at b1; linarith
  · rw [f1, f2]; rw [e3] at a2 b2; linarith
