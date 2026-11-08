-- Prove2me | solution 1 for AvgCaseTI.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:09:23.972245+00:00
-- url     : https://prove2.me/submissions/37cc4e97-60b0-4119-92cf-dabaa93fad26

import Mathlib
import Definitions.Def_AvgCaseTI_hull

set_option autoImplicit false

open AvgCaseTI in
theorem solution {K : Type*} [Field K] {n : ℕ} (T : GL (Fin n) K)
    (C : Submodule K (AvgCaseTI.Mat K n)) :
    AvgCaseTI.hull (AvgCaseTI.conjCode T C) = AvgCaseTI.conjCode T (AvgCaseTI.hull C) := by
  obtain ⟨t, ht⟩ : ∃ t : AvgCaseTI.Mat K n, t = (T : AvgCaseTI.Mat K n) := ⟨_, rfl⟩
  obtain ⟨ti, hti⟩ : ∃ ti : AvgCaseTI.Mat K n, ti = ((T⁻¹ : GL (Fin n) K) : AvgCaseTI.Mat K n) :=
    ⟨_, rfl⟩
  have h1 : t * ti = 1 := by rw [ht, hti]; exact Units.mul_inv T
  have h2 : ti * t = 1 := by rw [ht, hti]; exact Units.inv_mul T
  have hφ : ∀ X, AvgCaseTI.conjMap T X = t * (X * ti) := fun X => by rw [ht, hti]; rfl
  have e : ∀ M : AvgCaseTI.Mat K n, ti * (t * (M * ti)) * t = M := by
    intro M
    rw [← Matrix.mul_assoc ti t, h2, Matrix.one_mul, Matrix.mul_assoc, h2, Matrix.mul_one]
  have hinj : Function.Injective (AvgCaseTI.conjMap T) := by
    intro X Y h
    rw [hφ, hφ] at h
    calc X = ti * (t * (X * ti)) * t := (e X).symm
      _ = ti * (t * (Y * ti)) * t := by rw [h]
      _ = Y := e Y
  have hperp : AvgCaseTI.perp (C.map (AvgCaseTI.conjMap T)) =
      (AvgCaseTI.perp C).map (AvgCaseTI.conjMap T) := by
    ext Y
    constructor
    · intro hY
      rw [Submodule.mem_map]
      refine ⟨ti * (Y * t), ?_, ?_⟩
      · intro X hX
        have := hY _ (Submodule.mem_map_of_mem hX)
        rw [hφ] at this
        rw [show X * (ti * (Y * t)) = (X * ti * Y) * t by simp only [Matrix.mul_assoc],
          Matrix.trace_mul_comm, ← this]
        simp only [Matrix.mul_assoc]
      · rw [hφ]
        have : t * (ti * (Y * t) * ti) = (t * ti) * Y * (t * ti) := by
          simp only [Matrix.mul_assoc]
        rw [this, h1, Matrix.one_mul, Matrix.mul_one]
    · intro hY
      rw [Submodule.mem_map] at hY
      obtain ⟨Z, hZ, rfl⟩ := hY
      intro W hW
      rw [Submodule.mem_map] at hW
      obtain ⟨X, hX, rfl⟩ := hW
      rw [hφ, hφ]
      have hz := hZ X hX
      have e2 : t * (X * ti) * (t * (Z * ti)) = t * ((X * Z) * ti) := by
        calc t * (X * ti) * (t * (Z * ti)) = t * (X * (ti * t) * (Z * ti)) := by
              simp only [Matrix.mul_assoc]
          _ = t * ((X * Z) * ti) := by rw [h2, Matrix.mul_one, Matrix.mul_assoc]
      rw [e2, Matrix.trace_mul_comm, Matrix.mul_assoc, h2, Matrix.mul_one]
      exact hz
  unfold AvgCaseTI.hull AvgCaseTI.conjCode
  rw [Submodule.map_inf _ hinj, hperp]
