-- Prove2me | solution 1 for BellmanDP.Allocation.max_of_jointly_concave_is_concave
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T12:01:06.835554+00:00
-- url     : https://prove2.me/submissions/8a61e9db-8fbf-4ec3-977e-1c852722eeb5

import Mathlib



namespace BellmanDP.Allocation

theorem maxconc_core (G : ℝ → ℝ → ℝ)
    (hG : ConcaveOn ℝ (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ)) (fun p : ℝ × ℝ => G p.1 p.2))
    (f : ℝ → ℝ) (hf : ∀ x : ℝ, 0 ≤ x → IsGreatest ((G x) '' Set.Icc 0 x) (f x)) :
    ConcaveOn ℝ (Set.Ici 0) f := by
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx z hz α β hα hβ hαβ
  simp only [Set.mem_Ici] at hx hz
  obtain ⟨y1, hy1, e1⟩ := (hf x hx).1
  obtain ⟨y2, hy2, e2⟩ := (hf z hz).1
  have hxz : 0 ≤ α * x + β * z := by positivity
  have hmem : α * y1 + β * y2 ∈ Set.Icc 0 (α * x + β * z) := by
    constructor
    · have := hy1.1; have := hy2.1; positivity
    · nlinarith [hy1.2, hy2.2]
  have h1 := (hf _ hxz).2 ⟨_, hmem, rfl⟩
  have h2 := hG.2 (x := (x, y1)) (y := (z, y2)) ⟨hx, hy1.1⟩ ⟨hz, hy2.1⟩ hα hβ hαβ
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at h2
  rw [← e1, ← e2]; simp only [smul_eq_mul]; linarith

end BellmanDP.Allocation

open BellmanDP.Allocation


theorem solution (G : ℝ → ℝ → ℝ)
    (hG : ConcaveOn ℝ (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ)) (fun p : ℝ × ℝ => G p.1 p.2))
    (f : ℝ → ℝ) (hf : ∀ x : ℝ, 0 ≤ x → IsGreatest ((G x) '' Set.Icc 0 x) (f x)) :
    ConcaveOn ℝ (Set.Ici 0) f := by
  exact maxconc_core G hG f hf
