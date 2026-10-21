-- Prove2me | solution 1 for ConvexSDDP.Det.lemma_2_2_ii
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:56:53.009931+00:00
-- url     : https://prove2.me/submissions/3371e5d6-0455-4ed3-8c3b-9f345b721b07

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


theorem V_top_of_not_mem (t : ℕ) (ht : t < M.T) (z : EuclideanSpace ℝ (Fin d)) (hz : z ∉ M.X (t + 1)) :
    M.V (t + 1) z = ⊤ := by
  rw [Model.V]
  by_cases h : t + 1 < M.T
  · simp [h, hz]
  · have : t + 1 = M.T := by omega
    simp only [h, if_false]
    rw [this] at hz
    simp [hz]

theorem vt_le_v (t : ℕ) (ht : t ≤ M.T) (y : EuclideanSpace ℝ (Fin d)) : M.Vtilde t y ≤ M.V t y := by
  by_cases h : t < M.T
  · have hn : ¬ M.T ≤ t := not_le.mpr h
    unfold Model.Vtilde
    simp only [hn, if_false]
    rw [Model.V]
    simp only [h, if_true]
    split_ifs with hy
    · exact le_of_eq rfl
    · exact le_top
  · have : t = M.T := by omega
    subst this
    simp [Model.Vtilde]

theorem stage_le_W {x : ℕ → ℕ → EuclideanSpace ℝ (Fin d)}
    {θ : ℕ → ℕ → EReal} {β : ℕ → ℕ → EuclideanSpace ℝ (Fin d)}
    (hC : ∀ t < M.T, ∀ y v, M.C t y v ≠ ⊥)
    (t : ℕ) (ht : t < M.T) (k : ℕ)
    (ih : ∀ z ∈ M.X (t + 1), M.approx θ β x k (t + 1) z ≤ M.Vtilde (t + 1) z)
    (y : EuclideanSpace ℝ (Fin d)) (v : EuclideanSpace ℝ (Fin p)) (hv : v ∈ M.U t y) :
    M.stageValue θ β x k t y ≤ M.W t y v := by
  by_cases hf : M.f t (y, v) ∈ M.X (t + 1)
  · have hmem : v ∈ M.Ut t y := ⟨hv, hf⟩
    calc M.stageValue θ β x k t y ≤ M.Wapprox θ β x k t y v := by
          unfold Model.stageValue
          exact iInf₂_le v hmem
      _ ≤ M.W t y v := by
          unfold Model.Wapprox Model.W
          exact add_le_add le_rfl ((ih _ hf).trans (vt_le_v M (t + 1) (by omega) _))
  · have : M.W t y v = ⊤ := by
      unfold Model.W
      rw [V_top_of_not_mem M t ht _ hf]
      exact EReal.add_top_of_ne_bot (hC t ht y v)
    rw [this]; exact le_top

end CSDAux


theorem solution {d p : ℕ} (M : Model d p) (hH1 : M.H1)
    (x : ℕ → ℕ → EuclideanSpace ℝ (Fin d)) (u : ℕ → ℕ → EuclideanSpace ℝ (Fin p))
    (θ : ℕ → ℕ → EReal) (β : ℕ → ℕ → EuclideanSpace ℝ (Fin d))
    (hrun : M.IsRun x u θ β) :
    ∀ k, ∀ t < M.T,
      (∀ y ∈ affineSpan ℝ (M.X t), M.approx θ β x k t y ≤ M.Vtilde t y) ∧
        ∀ y, M.Vtilde t y ≤ M.V t y := by
  obtain ⟨hT, hXc, hx0, hU, hCp, -⟩ := hH1
  have hC : ∀ t < M.T, ∀ y v, M.C t y v ≠ ⊥ := fun t ht y v => (hCp t ht).1.1 (y, v)
  have key : ∀ m t, t + m = M.T → ∀ k, ∀ y ∈ affineSpan ℝ (M.X t),
      M.approx θ β x k t y ≤ M.Vtilde t y := by
    intro m
    induction m with
    | zero =>
      intro t ht k y _
      have : t = M.T := by omega
      subst this
      have h1 : M.approx θ β x k M.T y = M.V M.T y := by cases k <;> simp [Model.approx]
      rw [h1]
      simp [Model.Vtilde]
    | succ m ih =>
      intro t ht k y hy
      have htT : t < M.T := by omega
      have ih' := ih (t + 1) (by omega) k
      calc M.approx θ β x k t y ≤ M.stageValue θ β x k t y :=
            CSDAux.approx_le_stage M hrun t htT k y hy
        _ ≤ M.Vtilde t y := by
            have hn : ¬ M.T ≤ t := not_le.mpr htT
            unfold Model.Vtilde
            simp only [hn, if_false]
            refine le_iInf₂ fun v hv => ?_
            exact CSDAux.stage_le_W M hC t htT k
              (fun z hz => ih' z (subset_affineSpan ℝ _ hz)) y v hv
  intro k t ht
  exact ⟨key (M.T - t) t (by omega) k, CSDAux.vt_le_v M t ht.le⟩
