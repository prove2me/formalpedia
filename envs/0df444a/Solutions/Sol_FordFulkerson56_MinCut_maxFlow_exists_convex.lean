-- Prove2me | solution 1 for FordFulkerson56.MinCut.maxFlow_exists_convex
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T20:15:16.899517+00:00
-- url     : https://prove2.me/submissions/00eb0513-847f-4a3b-848f-9c4dc15e718f

import Mathlib
import Definitions.Def_FordFulkerson56_MinCut_Network
import Definitions.Def_FordFulkerson56_MinCut_IsChain
import Definitions.Def_FordFulkerson56_MinCut_IsFlow



namespace FordFulkerson56.MinCut

section
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

lemma ff_load_add (f g : Finset E → ℝ) (e : E) : load (f + g) e = load f e + load g e := by
  simp [load, Finset.sum_add_distrib]

lemma ff_load_smul (c : ℝ) (f : Finset E → ℝ) (e : E) : load (c • f) e = c * load f e := by
  simp [load, Finset.mul_sum]

lemma ff_value_add (f g : Finset E → ℝ) : value (f + g) = value f + value g := by
  simp [value, Finset.sum_add_distrib]

lemma ff_value_smul (c : ℝ) (f : Finset E → ℝ) : value (c • f) = c * value f := by
  simp [value, Finset.mul_sum]

lemma ff_chain_nonempty (N : Network V E) {C : Finset E}
    (h : IsChain N N.source N.sink C) : C.Nonempty := by
  obtain ⟨p, vs, ⟨hl, hh, hlast, -⟩, rfl⟩ := h
  rcases p with _ | ⟨a, p⟩
  · obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp hl
    simp at hh hlast
    exact absurd (hh.symm.trans hlast) N.source_ne_sink
  · exact ⟨a, by simp⟩

lemma ff_le_load (f : Finset E → ℝ) (hf : ∀ C, 0 ≤ f C) {C : Finset E} {e : E} (he : e ∈ C) :
    f C ≤ load f e := by
  unfold load
  exact Finset.single_le_sum (f := f) (fun D _ => hf D) (by simp [he])

lemma ff_flow_le (N : Network V E) {f : Finset E → ℝ} (hf : IsFlow N f) (C : Finset E) :
    f C ≤ ∑ e, N.cap e := by
  by_cases h0 : f C = 0
  · rw [h0]; exact Finset.sum_nonneg (fun e _ => (N.cap_pos e).le)
  · obtain ⟨e, he⟩ := ff_chain_nonempty N (hf.2.1 C h0)
    calc f C ≤ load f e := ff_le_load f hf.1 he
      _ ≤ N.cap e := hf.2.2 e
      _ ≤ ∑ e, N.cap e := Finset.single_le_sum (fun e _ => (N.cap_pos e).le) (Finset.mem_univ e)

lemma ff_isClosed_flow (N : Network V E) : IsClosed {f : Finset E → ℝ | IsFlow N f} := by
  have h1 : IsClosed {f : Finset E → ℝ | ∀ C, 0 ≤ f C} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter (fun C => isClosed_le continuous_const (continuous_apply C))
  have h2 : IsClosed {f : Finset E → ℝ | ∀ C, f C ≠ 0 → IsChain N N.source N.sink C} := by
    simp only [Set.setOf_forall]
    refine isClosed_iInter (fun C => ?_)
    by_cases hC : IsChain N N.source N.sink C
    · simp [hC]
    · have : {f : Finset E → ℝ | f C ≠ 0 → IsChain N N.source N.sink C} = {f | f C = 0} := by
        ext f; simp [hC]
      rw [this]
      exact isClosed_eq (continuous_apply C) continuous_const
  have h3 : IsClosed {f : Finset E → ℝ | ∀ e, load f e ≤ N.cap e} := by
    simp only [Set.setOf_forall]
    refine isClosed_iInter (fun e => isClosed_le ?_ continuous_const)
    unfold load
    exact continuous_finset_sum _ (fun C _ => continuous_apply C)
  have : {f : Finset E → ℝ | IsFlow N f} = {f : Finset E → ℝ | ∀ C, 0 ≤ f C} ∩
      ({f : Finset E → ℝ | ∀ C, f C ≠ 0 → IsChain N N.source N.sink C} ∩
        {f : Finset E → ℝ | ∀ e, load f e ≤ N.cap e}) := by
    ext f; simp [IsFlow]
  rw [this]
  exact h1.inter (h2.inter h3)

lemma ff_zero_flow (N : Network V E) : IsFlow N (0 : Finset E → ℝ) := by
  refine ⟨fun C => le_rfl, fun C h => absurd rfl h, fun e => ?_⟩
  simp [load]; exact (N.cap_pos e).le

lemma ff_exists_max (N : Network V E) : ∃ f, IsMaxFlow N f := by
  have hc : IsCompact {f : Finset E → ℝ | IsFlow N f} := by
    refine Metric.isCompact_of_isClosed_isBounded (ff_isClosed_flow N) ?_
    refine (Metric.isBounded_closedBall (x := (0 : Finset E → ℝ)) (r := ∑ e, N.cap e)).subset ?_
    intro f hf
    have hM : 0 ≤ ∑ e, N.cap e := Finset.sum_nonneg (fun e _ => (N.cap_pos e).le)
    simp only [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg hM).2 (fun C => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hf.1 C)]
    exact ff_flow_le N hf C
  have hv : Continuous (fun f : Finset E → ℝ => value f) := by
    unfold value
    exact continuous_finset_sum _ (fun C _ => continuous_apply C)
  obtain ⟨f, hf, hmax⟩ := hc.exists_isMaxOn ⟨0, ff_zero_flow N⟩ hv.continuousOn
  exact ⟨f, hf, fun g hg => hmax hg⟩

lemma ff_convex (N : Network V E) : Convex ℝ {f : Finset E → ℝ | IsMaxFlow N f} := by
  intro f hf g hg a b ha hb hab
  simp only [Set.mem_setOf_eq] at hf hg ⊢
  refine ⟨⟨fun C => ?_, fun C hC => ?_, fun e => ?_⟩, fun h hh => ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := hf.1.1 C; have := hg.1.1 C; positivity
  · by_cases h1 : f C = 0
    · by_cases h2 : g C = 0
      · simp [h1, h2] at hC
      · exact hg.1.2.1 C h2
    · exact hf.1.2.1 C h1
  · rw [ff_load_add, ff_load_smul, ff_load_smul]
    have h1 := mul_le_mul_of_nonneg_left (hf.1.2.2 e) ha
    have h2 := mul_le_mul_of_nonneg_left (hg.1.2.2 e) hb
    have : a * N.cap e + b * N.cap e = N.cap e := by rw [← add_mul, hab, one_mul]
    linarith
  · rw [ff_value_add, ff_value_smul, ff_value_smul]
    have h1 := mul_le_mul_of_nonneg_left (hf.2 h hh) ha
    have h2 := mul_le_mul_of_nonneg_left (hg.2 h hh) hb
    have : a * value h + b * value h = value h := by rw [← add_mul, hab, one_mul]
    linarith

theorem maxFlow_exists_convex_core (N : Network V E) :
    (∃ f, IsMaxFlow N f) ∧ Convex ℝ {f : Finset E → ℝ | IsMaxFlow N f} :=
  ⟨ff_exists_max N, ff_convex N⟩

end
end FordFulkerson56.MinCut

open FordFulkerson56.MinCut


theorem solution {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (N : Network V E) :
    (∃ f, IsMaxFlow N f) ∧ Convex ℝ {f : Finset E → ℝ | IsMaxFlow N f} := by
  exact maxFlow_exists_convex_core N
