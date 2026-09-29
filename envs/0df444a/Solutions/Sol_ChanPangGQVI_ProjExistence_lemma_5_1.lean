-- Prove2me | solution 1 for ChanPangGQVI.ProjExistence.lemma_5_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T21:22:38.492675+00:00
-- url     : https://prove2.me/submissions/da4062c4-9352-4bdc-bd1a-192f6995bf1e

import Mathlib
import Definitions.Def_ChanPangGQVI_Shared_Projection

open scoped RealInnerProductSpace Topology

namespace ChanPangGQVI.ProjExistence

theorem l51_isProj {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n))) (hne : S.Nonempty)
    (hc : IsClosed S) (hconv : Convex ℝ S) (z : EuclideanSpace ℝ (Fin n)) :
    ChanPangGQVI.Shared.IsProj S z (ChanPangGQVI.Shared.proj S z) := by
  obtain ⟨v, hv, heq⟩ := exists_norm_eq_iInf_of_complete_convex hne hc.isComplete hconv z
  have h : ∃ p, ChanPangGQVI.Shared.IsProj S z p := by
    refine ⟨v, hv, fun q hq => ?_⟩
    rw [norm_sub_rev, heq, norm_sub_rev]
    exact ciInf_le ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩ (⟨q, hq⟩ : S)
  unfold ChanPangGQVI.Shared.proj
  rw [dif_pos h]
  exact h.choose_spec

theorem l51_var {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n)))
    (hconv : Convex ℝ S) (z p : EuclideanSpace ℝ (Fin n))
    (hp : ChanPangGQVI.Shared.IsProj S z p) :
    ∀ r ∈ S, ‖r - p‖ ^ 2 + ‖p - z‖ ^ 2 ≤ ‖r - z‖ ^ 2 := by
  have : Nonempty S := ⟨⟨p, hp.1⟩⟩
  have heq : ‖z - p‖ = ⨅ w : S, ‖z - w‖ := by
    apply le_antisymm
    · apply le_ciInf
      intro w
      rw [norm_sub_rev z p, norm_sub_rev z]
      exact hp.2 w w.2
    · exact ciInf_le ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩ (⟨p, hp.1⟩ : S)
  have hvi := (norm_eq_iInf_iff_real_inner_le_zero hconv hp.1).1 heq
  intro r hr
  have h1 := hvi r hr
  have e : r - z = (r - p) + (p - z) := by abel
  rw [e, norm_add_sq_real]
  have e2 : ⟪r - p, p - z⟫ = - ⟪z - p, r - p⟫ := by
    rw [real_inner_comm, ← inner_neg_left, neg_sub]
  rw [e2]
  linarith

theorem l51_core {n : ℕ}
    (K : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (x₀ : EuclideanSpace ℝ (Fin n))
    (hK_upper : UpperHemicontinuousAt K x₀) (hK_lower : LowerHemicontinuousAt K x₀)
    (hK_closed : ∀ x, IsClosed (K x)) (hK_convex : ∀ x, Convex ℝ (K x))
    (hK_nonempty : ∀ x, (K x).Nonempty)
    (y₀ : EuclideanSpace ℝ (Fin n)) :
    ContinuousAt
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        ChanPangGQVI.Shared.proj (K p.1) p.2)
      (x₀, y₀) := by
  set p₀ := ChanPangGQVI.Shared.proj (K x₀) y₀ with hp₀def
  have hp₀ := l51_isProj (K x₀) (hK_nonempty x₀) (hK_closed x₀) (hK_convex x₀) y₀
  rw [← hp₀def] at hp₀
  set d₀ := ‖p₀ - y₀‖ with hd₀
  have hd₀nn : 0 ≤ d₀ := norm_nonneg _
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  set s : ℝ := min (ε / 2) (min 1 (ε ^ 2 / (4 * (2 * d₀ + 1)))) with hs
  have hs0 : 0 < s := lt_min (by linarith) (lt_min one_pos (by positivity))
  have hs1 : s ≤ ε / 2 := min_le_left _ _
  have hs2 : s ≤ 1 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hs3 : s ≤ ε ^ 2 / (4 * (2 * d₀ + 1)) := le_trans (min_le_right _ _) (min_le_right _ _)
  set η := s / 4 with hη
  have hη0 : 0 < η := by positivity
  -- lower hemicontinuity
  have hL := (lowerHemicontinuousAt_iff.1 hK_lower) (Metric.ball p₀ η) Metric.isOpen_ball
    ⟨p₀, hp₀.1, Metric.mem_ball_self hη0⟩
  -- upper hemicontinuity
  have hU := (upperHemicontinuousAt_iff.1 hK_upper) (Metric.thickening η (K x₀))
    ((Metric.isOpen_thickening).mem_nhdsSet.2 (Metric.self_subset_thickening hη0 _))
  have hL' := (continuous_fst.continuousAt (x := (x₀, y₀))).eventually hL
  have hU' := (continuous_fst.continuousAt (x := (x₀, y₀))).eventually hU
  have hY : ∀ᶠ q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) in 𝓝 (x₀, y₀),
      dist q.2 y₀ < η :=
    (continuous_snd.continuousAt (x := (x₀, y₀))).eventually (Metric.ball_mem_nhds y₀ hη0)
  filter_upwards [hL', hU', hY] with q hqL hqU hqY
  obtain ⟨x, y⟩ := q
  simp only at hqL hqU hqY ⊢
  rw [← hp₀def]
  have hq := l51_isProj (K x) (hK_nonempty x) (hK_closed x) (hK_convex x) y
  set u := ChanPangGQVI.Shared.proj (K x) y
  obtain ⟨z, hzK, hzB⟩ := hqL
  rw [Metric.mem_ball, dist_eq_norm] at hzB
  rw [dist_eq_norm] at hqY
  have hu1 : ‖u - y‖ ≤ ‖z - y‖ := hq.2 z hzK
  have hzy : ‖z - y‖ ≤ ‖z - p₀‖ + ‖p₀ - y₀‖ + ‖y₀ - y‖ := by
    have e : z - y = (z - p₀) + (p₀ - y₀) + (y₀ - y) := by abel
    rw [e]; exact norm_add₃_le
  have hyy : ‖y₀ - y‖ = ‖y - y₀‖ := norm_sub_rev _ _
  have huy0 : ‖u - y₀‖ ≤ ‖u - y‖ + ‖y - y₀‖ := by
    have e : u - y₀ = (u - y) + (y - y₀) := by abel
    rw [e]; exact norm_add_le _ _
  have hKsub := subset_of_mem_nhdsSet hqU
  obtain ⟨r, hrK, hur⟩ := Metric.mem_thickening_iff.1 (hKsub hq.1)
  rw [dist_eq_norm] at hur
  have hry0 : ‖r - y₀‖ ≤ ‖r - u‖ + ‖u - y₀‖ := by
    have e : r - y₀ = (r - u) + (u - y₀) := by abel
    rw [e]; exact norm_add_le _ _
  have hru : ‖r - u‖ = ‖u - r‖ := norm_sub_rev _ _
  have hrb : ‖r - y₀‖ < d₀ + s := by linarith
  have hvar := l51_var (K x₀) (hK_convex x₀) y₀ p₀ hp₀ r hrK
  have hrp : ‖r - p₀‖ ^ 2 < (ε / 2) ^ 2 := by
    have h1 : ‖r - y₀‖ ^ 2 < (d₀ + s) ^ 2 := by
      have := norm_nonneg (r - y₀)
      nlinarith
    have h2 : (d₀ + s) ^ 2 - d₀ ^ 2 ≤ (2 * d₀ + 1) * s := by nlinarith
    have h3 : (2 * d₀ + 1) * s ≤ ε ^ 2 / 4 := by
      rw [le_div_iff₀ (by positivity)] at hs3
      nlinarith
    nlinarith
  have hrp' : ‖r - p₀‖ < ε / 2 := by
    have := norm_nonneg (r - p₀)
    nlinarith
  have e : u - p₀ = (u - r) + (r - p₀) := by abel
  rw [dist_eq_norm, e]
  calc ‖(u - r) + (r - p₀)‖ ≤ ‖u - r‖ + ‖r - p₀‖ := norm_add_le _ _
    _ < ε := by linarith

end ChanPangGQVI.ProjExistence

open ChanPangGQVI.ProjExistence


theorem solution {n : ℕ}
    (K : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (x₀ : EuclideanSpace ℝ (Fin n))
    (hK_upper : UpperHemicontinuousAt K x₀) (hK_lower : LowerHemicontinuousAt K x₀)
    (hK_closed : ∀ x, IsClosed (K x)) (hK_convex : ∀ x, Convex ℝ (K x))
    (hK_nonempty : ∀ x, (K x).Nonempty)
    (y₀ : EuclideanSpace ℝ (Fin n)) :
    ContinuousAt
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        ChanPangGQVI.Shared.proj (K p.1) p.2)
      (x₀, y₀) := by
  exact l51_core K x₀ hK_upper hK_lower hK_closed hK_convex hK_nonempty y₀
