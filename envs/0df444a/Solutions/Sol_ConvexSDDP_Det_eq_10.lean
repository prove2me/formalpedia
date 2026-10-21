-- Prove2me | solution 1 for ConvexSDDP.Det.eq_10
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:52:06.929976+00:00
-- url     : https://prove2.me/submissions/27ba984c-ac60-478e-b995-3c2eaab438f9

import Mathlib
import Definitions.Def_ConvexSDDP_Det_Basic
import Definitions.Def_ConvexSDDP_Det_Model

set_option autoImplicit false
open Filter Topology
open ConvexSDDP.Det

namespace CSDAux
variable {d p : ℕ} (M : Model d p)

theorem approx_mono (θ : ℕ → ℕ → EReal) (β x : ℕ → ℕ → EuclideanSpace ℝ (Fin d)) (k t : ℕ)
    (y : EuclideanSpace ℝ (Fin d)) :
    M.approx θ β x k t y ≤ M.approx θ β x (k + 1) t y := by
  by_cases h : M.T ≤ t
  · cases k <;> simp [Model.approx, h]
  · simp only [Model.approx, h, if_false]
    exact le_max_left _ _

theorem wapprox_mono (θ : ℕ → ℕ → EReal) (β x : ℕ → ℕ → EuclideanSpace ℝ (Fin d)) (k t : ℕ)
    (y : EuclideanSpace ℝ (Fin d)) (u : EuclideanSpace ℝ (Fin p)) :
    M.Wapprox θ β x k t y u ≤ M.Wapprox θ β x (k + 1) t y u := by
  unfold Model.Wapprox
  exact add_le_add le_rfl (approx_mono M θ β x k (t + 1) _)

theorem stage_mono (θ : ℕ → ℕ → EReal) (β x : ℕ → ℕ → EuclideanSpace ℝ (Fin d)) (k t : ℕ)
    (y : EuclideanSpace ℝ (Fin d)) :
    M.stageValue θ β x k t y ≤ M.stageValue θ β x (k + 1) t y := by
  unfold Model.stageValue
  exact iInf_mono fun u => iInf_mono fun _ => wapprox_mono M θ β x k t y u

theorem approx_le_stage {x : ℕ → ℕ → EuclideanSpace ℝ (Fin d)} {u : ℕ → ℕ → EuclideanSpace ℝ (Fin p)}
    {θ : ℕ → ℕ → EReal} {β : ℕ → ℕ → EuclideanSpace ℝ (Fin d)}
    (hrun : M.IsRun x u θ β) (t : ℕ) (ht : t < M.T) (k : ℕ) :
    ∀ y ∈ affineSpan ℝ (M.X t), M.approx θ β x k t y ≤ M.stageValue θ β x k t y := by
  induction k with
  | zero =>
    intro y _
    have : ¬ M.T ≤ t := not_le.mpr ht
    simp [Model.approx, this]
  | succ k ih =>
    intro y hy
    have hne : ¬ M.T ≤ t := not_le.mpr ht
    simp only [Model.approx, hne, if_false]
    refine max_le ?_ ?_
    · exact (ih y hy).trans (stage_mono M θ β x k t y)
    · exact ((hrun k).2 t ht).2.2.2.2 y hy |>.trans (stage_mono M θ β x k t y)

theorem state_mem {x : ℕ → ℕ → EuclideanSpace ℝ (Fin d)} {u : ℕ → ℕ → EuclideanSpace ℝ (Fin p)}
    {θ : ℕ → ℕ → EReal} {β : ℕ → ℕ → EuclideanSpace ℝ (Fin d)}
    (hx0 : M.x0 ∈ M.X 0) (hrun : M.IsRun x u θ β) (k : ℕ) :
    ∀ t, t < M.T → x (k + 1) t ∈ M.X t := by
  intro t
  induction t with
  | zero => intro _; rw [(hrun k).1]; exact hx0
  | succ t ih =>
    intro ht
    have h := (hrun k).2 t (by omega)
    rw [h.2.2.1]
    exact (h.1.1).2

end CSDAux

theorem solution {d p : ℕ} (M : Model d p) (hx0 : M.x0 ∈ M.X 0)
    (x : ℕ → ℕ → EuclideanSpace ℝ (Fin d)) (u : ℕ → ℕ → EuclideanSpace ℝ (Fin p))
    (θ : ℕ → ℕ → EReal) (β : ℕ → ℕ → EuclideanSpace ℝ (Fin d))
    (hrun : M.IsRun x u θ β) :
    ∀ k, ∀ t < M.T,
      M.approx θ β x (k + 1) t (x (k + 1) t) = θ (k + 1) t ∧
        θ (k + 1) t = M.Wapprox θ β x k t (x (k + 1) t) (u (k + 1) t) := by
  intro k t ht
  have h := (hrun k).2 t ht
  refine ⟨?_, h.2.1⟩
  have hmem : x (k + 1) t ∈ affineSpan ℝ (M.X t) :=
    subset_affineSpan ℝ _ (CSDAux.state_mem M hx0 hrun k t ht)
  have h1 : M.approx θ β x k t (x (k + 1) t) ≤ θ (k + 1) t := by
    calc M.approx θ β x k t (x (k + 1) t) ≤ M.stageValue θ β x k t (x (k + 1) t) :=
          CSDAux.approx_le_stage M hrun t ht k _ hmem
      _ ≤ M.Wapprox θ β x k t (x (k + 1) t) (u (k + 1) t) := by
          unfold Model.stageValue
          exact iInf₂_le (u (k + 1) t) h.1.1
      _ = θ (k + 1) t := h.2.1.symm
  have hne : ¬ M.T ≤ t := not_le.mpr ht
  simp only [Model.approx, hne, if_false]
  simp [h1]
