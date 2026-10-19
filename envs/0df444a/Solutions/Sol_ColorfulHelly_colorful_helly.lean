-- Prove2me | solution 1 for ColorfulHelly.colorful_helly
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T15:49:36.03771+00:00
-- url     : https://prove2.me/submissions/6ed02c5c-1b9c-4616-a35a-444e2bb72c99

import Mathlib.Analysis.Convex.Radon
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push

open Set Finset

private lemma support_minimum (d : ℕ)
    (F : Fin (d + 1) → Set (EuclideanSpace ℝ (Fin d)))
    (hF : ∀ i, Convex ℝ (F i))
    (p : EuclideanSpace ℝ (Fin d)) (hp : ∀ i, p ∈ F i)
    (hmin : ∀ x, (∀ i, x ∈ F i) → ‖p‖ ≤ ‖x‖) :
    ∃ i, ∀ x, (∀ k, k ≠ i → x ∈ F k) → ‖p‖ ≤ ‖x‖ := by
  classical
  by_contra! hn
  choose x hx hnorm using hn
  let G : Option (Fin (d + 1)) → Set (EuclideanSpace ℝ (Fin d)) :=
    fun j => match j with
    | none => Metric.ball 0 ‖p‖
    | some i => F i
  have hconv : ∀ j ∈ (univ : Finset (Option (Fin (d + 1)))), Convex ℝ (G j) := by
    intro j _
    cases j with
    | none => exact convex_ball 0 ‖p‖
    | some i => exact hF i
  have hsmall : ∀ I ⊆ (univ : Finset (Option (Fin (d + 1)))),
      I.card ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) + 1 →
      (⋂ j ∈ I, G j).Nonempty := by
    intro I hI hcard
    have hc : I.card < (univ : Finset (Option (Fin (d + 1)))).card := by
      have hh : I.card ≤ d + 1 := by simpa using hcard
      simp only [Finset.card_univ, Fintype.card_option, Fintype.card_fin]
      omega
    obtain ⟨j, _, hj⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
    cases j with
    | none =>
      refine ⟨p, mem_iInter₂.mpr ?_⟩
      intro j hjI
      cases j with
      | none => exact False.elim (hj hjI)
      | some i => exact hp i
    | some i =>
      refine ⟨x i, mem_iInter₂.mpr ?_⟩
      intro j hjI
      cases j with
      | none => simpa [G, Metric.mem_ball, dist_zero_right] using hnorm i
      | some k =>
        apply hx i k
        intro hki
        subst k
        exact hj hjI
  obtain ⟨q, hq⟩ := Convex.helly_theorem' hconv hsmall
  have hqF : ∀ i, q ∈ F i := fun i => mem_iInter₂.mp hq (some i) (mem_univ _)
  have hqnorm : ‖q‖ < ‖p‖ := by
    simpa [G, Metric.mem_ball, dist_zero_right] using
      (mem_iInter₂.mp hq none (mem_univ _))
  exact (not_lt_of_ge (hmin q hqF)) hqnorm

private lemma minimum_unique {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))}
    (hK : Convex ℝ K) {p q : EuclideanSpace ℝ (Fin d)} (hp : p ∈ K) (hq : q ∈ K)
    (hmin : ∀ x ∈ K, ‖p‖ ≤ ‖x‖) (hn : ‖q‖ ≤ ‖p‖) : q = p := by
  have hm : (1 / 2 : ℝ) • p + (1 / 2 : ℝ) • q ∈ K :=
    hK hp hq (by norm_num) (by norm_num) (by norm_num)
  have hm' := hmin _ hm
  rw [← smul_add, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at hm'
  have hpar := parallelogram_law_with_norm ℝ p q
  have hs : ‖p - q‖ = 0 := by
    nlinarith [norm_nonneg (p - q), norm_nonneg (p + q), norm_nonneg p, norm_nonneg q]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hs)).symm

private lemma compact_colorful (d : ℕ) (N : Fin (d + 1) → ℕ)
    [∀ i, Nonempty (Fin (N i))]
    (F : (i : Fin (d + 1)) → Fin (N i) → Set (EuclideanSpace ℝ (Fin d)))
    (hF : ∀ i j, Convex ℝ (F i j)) (hK : ∀ i j, IsCompact (F i j))
    (h : ∀ c : (i : Fin (d + 1)) → Fin (N i), (⋂ i, F i (c i)).Nonempty) :
    ∃ i, (⋂ j, F i j).Nonempty := by
  classical
  have hcompact : ∀ c : (i : Fin (d + 1)) → Fin (N i), IsCompact (⋂ i, F i (c i)) := by
    intro c
    exact (hK 0 (c 0)).of_isClosed_subset
      (isClosed_iInter fun i => (hK i (c i)).isClosed) (iInter_subset _ 0)
  have hmins : ∀ c : (i : Fin (d + 1)) → Fin (N i),
      ∃ p ∈ (⋂ i, F i (c i)), ∀ x ∈ (⋂ i, F i (c i)), ‖p‖ ≤ ‖x‖ := by
    intro c
    exact (hcompact c).exists_isMinOn (h c) continuous_norm.continuousOn
  choose p hp hmin using hmins
  obtain ⟨c, _, hc⟩ := (univ : Finset ((i : Fin (d + 1)) → Fin (N i))).exists_max_image
    (fun c => ‖p c‖) (by simp)
  obtain ⟨i, hi⟩ := support_minimum d (fun i => F i (c i)) (fun i => hF i (c i))
    (p c) (fun i => mem_iInter.mp (hp c) i) (fun x hx => hmin c x (mem_iInter.mpr hx))
  refine ⟨i, p c, mem_iInter.mpr ?_⟩
  intro j
  let c' : (k : Fin (d + 1)) → Fin (N k) := Function.update c i j
  have hp' : ∀ k, k ≠ i → p c' ∈ F k (c k) := by
    intro k hk
    have := mem_iInter.mp (hp c') k
    simpa [c', Function.update_of_ne hk] using this
  have heq : p c' = p c := by
    apply minimum_unique (K := ⋂ k, ⋂ (_ : k ≠ i), F k (c k))
      (convex_iInter fun k => convex_iInter fun _ => hF k (c k))
    · exact mem_iInter.mpr fun k => mem_iInter.mpr fun _ => mem_iInter.mp (hp c) k
    · exact mem_iInter.mpr fun k => mem_iInter.mpr (hp' k)
    · intro x hx
      exact hi x (fun k hk => mem_iInter.mp (mem_iInter.mp hx k) hk)
    · exact hc c' (mem_univ _)
  have := mem_iInter.mp (hp c') i
  simpa [heq, c'] using this

theorem solution (d : ℕ) (N : Fin (d + 1) → ℕ)
    (F : (i : Fin (d + 1)) → Fin (N i) → Set (EuclideanSpace ℝ (Fin d)))
    (hF : ∀ i j, Convex ℝ (F i j))
    (h : ∀ c : (i : Fin (d + 1)) → Fin (N i), (⋂ i, F i (c i)).Nonempty) :
    ∃ i, (⋂ j, F i j).Nonempty := by
  classical
  by_cases hN : ∀ i, Nonempty (Fin (N i))
  · let _ := hN
    choose w hw using h
    let A (i : Fin (d + 1)) (j : Fin (N i)) : Set (EuclideanSpace ℝ (Fin d)) :=
      w '' {c | c i = j}
    let K (i : Fin (d + 1)) (j : Fin (N i)) := convexHull ℝ (A i j)
    have hsub : ∀ i j, K i j ⊆ F i j := by
      intro i j
      apply convexHull_min
      · rintro x ⟨c, hc, rfl⟩
        have := mem_iInter.mp (hw c) i
        simpa only [show c i = j from hc] using this
      · exact hF i j
    have hK : ∀ i j, IsCompact (K i j) := by
      intro i j
      exact ((Set.toFinite {c : (i : Fin (d + 1)) → Fin (N i) | c i = j}).image w).isCompact_convexHull ℝ
    have hchoice : ∀ c : (i : Fin (d + 1)) → Fin (N i), (⋂ i, K i (c i)).Nonempty := by
      intro c
      refine ⟨w c, mem_iInter.mpr fun i => ?_⟩
      exact subset_convexHull ℝ (A i (c i)) ⟨c, rfl, rfl⟩
    obtain ⟨i, x, hx⟩ := compact_colorful d N K (fun _ _ => convex_convexHull ℝ _) hK hchoice
    exact ⟨i, x, mem_iInter.mpr fun j => hsub i j (mem_iInter.mp hx j)⟩
  · push Not at hN
    obtain ⟨i, hi⟩ := hN
    have : IsEmpty (Fin (N i)) := hi
    exact ⟨i, 0, mem_iInter.mpr fun j => isEmptyElim j⟩
