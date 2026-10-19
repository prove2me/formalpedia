-- Prove2me | solution 1 for ColorfulHelly.colorful_fractional_helly
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T15:55:10.91266+00:00
-- url     : https://prove2.me/submissions/75b4ae74-9643-4529-9d9f-5f81f6c38c42

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


private lemma compact_fractional (d : ℕ) (α : ℝ) (hα : 0 < α)
    (N : Fin (d + 1) → ℕ) (hN : ∀ i, 0 < N i)
    (F : (i : Fin (d + 1)) → Fin (N i) → Set (EuclideanSpace ℝ (Fin d)))
    (hF : ∀ i j, Convex ℝ (F i j)) (hK : ∀ i j, IsCompact (F i j))
    (h : α * ∏ i, (N i : ℝ) ≤
      ({c : (i : Fin (d + 1)) → Fin (N i) | (⋂ i, F i (c i)).Nonempty}.ncard : ℝ)) :
    ∃ i, ∃ G : Finset (Fin (N i)),
      α / (d + 1) * (N i : ℝ) ≤ (G.card : ℝ) ∧ (⋂ j ∈ G, F i j).Nonempty := by
  classical
  let C := (i : Fin (d + 1)) → Fin (N i)
  let T := {c : C // (⋂ i, F i (c i)).Nonempty}
  let B (i : Fin (d + 1)) := (k : {k : Fin (d + 1) // k ≠ i}) → Fin (N k.1)
  have (i : Fin (d + 1)) : Nonempty (Fin (N i)) := ⟨⟨0, hN i⟩⟩
  have hmins : ∀ c : T, ∃ p ∈ (⋂ i, F i (c.1 i)),
      ∀ x ∈ (⋂ i, F i (c.1 i)), ‖p‖ ≤ ‖x‖ := by
    intro c
    have hc : IsCompact (⋂ i, F i (c.1 i)) :=
      (hK 0 (c.1 0)).of_isClosed_subset
        (isClosed_iInter fun i => (hK i (c.1 i)).isClosed) (iInter_subset _ 0)
    exact hc.exists_isMinOn c.2 continuous_norm.continuousOn
  choose p hp hmin using hmins
  have hsupp : ∀ c : T, ∃ i, ∀ x,
      (∀ k, k ≠ i → x ∈ F k (c.1 k)) → ‖p c‖ ≤ ‖x‖ := by
    intro c
    exact support_minimum d (fun i => F i (c.1 i)) (fun i => hF i (c.1 i))
      (p c) (fun i => mem_iInter.mp (hp c) i)
      (fun x hx => hmin c x (mem_iInter.mpr hx))
  choose col hcol using hsupp
  let key (c : T) : Sigma B := ⟨col c, fun k => c.1 k.1⟩
  let S (i : Fin (d + 1)) (b : B i) : Finset T :=
    univ.filter (fun c => key c = ⟨i, b⟩)
  have key_rest (c : T) (i : Fin (d + 1)) (b : B i)
      (hc : key c = ⟨i, b⟩) : (fun k : {k // k ≠ i} => c.1 k.1) = b := by
    have hci : col c = i := congrArg Sigma.fst hc
    subst i
    exact eq_of_heq (by simpa only [key, Sigma.mk.inj_iff, true_and] using hc)
  have same_point (i : Fin (d + 1)) (b : B i) {c e : T}
      (hc : c ∈ S i b) (he : e ∈ S i b) : p c = p e := by
    have hkc : key c = ⟨i, b⟩ := (mem_filter.mp hc).2
    have hke : key e = ⟨i, b⟩ := (mem_filter.mp he).2
    have hci : col c = i := congrArg Sigma.fst hkc
    have hei : col e = i := congrArg Sigma.fst hke
    have hrest : ∀ k, k ≠ i → c.1 k = e.1 k := by
      intro k hk
      have hc' : (fun k : {k // k ≠ i} => c.1 k.1) = b := by
        exact key_rest c i b hkc
      have he' : (fun k : {k // k ≠ i} => e.1 k.1) = b := by
        exact key_rest e i b hke
      exact congrFun (hc'.trans he'.symm) ⟨k, hk⟩
    have hpc : ∀ k, k ≠ i → p c ∈ F k (c.1 k) := fun k _ => mem_iInter.mp (hp c) k
    have hpe : ∀ k, k ≠ i → p e ∈ F k (c.1 k) := by
      intro k hk
      rw [hrest k hk]
      exact mem_iInter.mp (hp e) k
    apply (minimum_unique (K := ⋂ k, ⋂ (_ : k ≠ i), F k (c.1 k))
      (convex_iInter fun k => convex_iInter fun _ => hF k (c.1 k))
      (mem_iInter.mpr fun k => mem_iInter.mpr (hpc k))
      (mem_iInter.mpr fun k => mem_iInter.mpr (hpe k))
      (fun x hx => hcol c x (by simpa only [hci] using
        (fun k hk => mem_iInter.mp (mem_iInter.mp hx k) hk))) ?_).symm
    apply hcol e
    intro k hk
    have hki : k ≠ i := by simpa only [hei] using hk
    rw [← hrest k hki]
    exact hpc k hki
  by_contra! hn
  have hbound (i : Fin (d + 1)) (b : B i) :
      ((S i b).card : ℝ) < α / (d + 1) * (N i : ℝ) := by
    let G := (S i b).image (fun c => c.1 i)
    have hcommon : (⋂ j ∈ G, F i j).Nonempty := by
      by_cases hs : (S i b).Nonempty
      · obtain ⟨c, hc⟩ := hs
        refine ⟨p c, mem_iInter₂.mpr ?_⟩
        intro j hj
        obtain ⟨e, he, rfl⟩ := mem_image.mp hj
        rw [same_point i b hc he]
        exact mem_iInter.mp (hp e) i
      · have : G = ∅ := by simp [G, Finset.not_nonempty_iff_eq_empty.mp hs]
        simp [this]
    have hinj : Set.InjOn (fun c : T => c.1 i) (S i b) := by
      intro c hc e he hce
      apply Subtype.ext
      funext k
      by_cases hki : k = i
      · subst k; exact hce
      · have hkc : key c = ⟨i, b⟩ := (mem_filter.mp hc).2
        have hke : key e = ⟨i, b⟩ := (mem_filter.mp he).2
        have hc' : (fun k : {k // k ≠ i} => c.1 k.1) = b := by
          exact key_rest c i b hkc
        have he' : (fun k : {k // k ≠ i} => e.1 k.1) = b := by
          exact key_rest e i b hke
        exact congrFun (hc'.trans he'.symm) ⟨k, hki⟩
    have hcard : G.card = (S i b).card := card_image_iff.mpr hinj
    have := lt_of_not_ge (fun hh => hcommon.ne_empty (hn i G hh))
    simpa only [hcard] using this
  have hcount : Fintype.card T = ∑ i, ∑ b : B i, (S i b).card := by
    have hh := Finset.card_eq_sum_card_fiberwise
      (s := (univ : Finset T)) (t := (univ : Finset (Sigma B)))
      (f := key) (fun _ _ => mem_univ _)
    simpa only [card_univ, Fintype.sum_sigma] using hh
  have hprod (i : Fin (d + 1)) :
      (Fintype.card (B i) : ℝ) * (N i : ℝ) = ∏ k, (N k : ℝ) := by
    simp only [B, Fintype.card_pi, Fintype.card_fin, Nat.cast_prod]
    rw [Fintype.prod_eq_mul_prod_subtype_ne (fun k => (N k : ℝ)) i]
    ring
  have hsum (i : Fin (d + 1)) :
      (∑ b : B i, ((S i b).card : ℝ)) < α / (d + 1) * ∏ k, (N k : ℝ) := by
    calc
      _ < ∑ _b : B i, α / (d + 1) * (N i : ℝ) :=
        Finset.sum_lt_sum_of_nonempty (by simp) (fun b _ => hbound i b)
      _ = α / (d + 1) * ∏ k, (N k : ℝ) := by
        simp only [sum_const, card_univ, nsmul_eq_mul]
        rw [← mul_assoc, mul_comm (Fintype.card (B i) : ℝ), mul_assoc, hprod i]
  have ht : (Fintype.card T : ℝ) < α * ∏ k, (N k : ℝ) := by
    calc
      _ = ∑ i, ∑ b : B i, ((S i b).card : ℝ) := by exact_mod_cast hcount
      _ < ∑ _i : Fin (d + 1), α / (d + 1) * ∏ k, (N k : ℝ) :=
        Finset.sum_lt_sum_of_nonempty (by simp) (fun i _ => hsum i)
      _ = α * ∏ k, (N k : ℝ) := by
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add,
          Nat.cast_one]
        field_simp
  have hc : {c : C | (⋂ i, F i (c i)).Nonempty}.ncard = Fintype.card T := by
    exact Set.ncard_eq_toFinset_card _ |>.trans (by simp [T, Fintype.card_subtype])
  rw [hc] at h
  exact (not_lt_of_ge h) ht

theorem solution (d : ℕ) (α : ℝ) (hα : 0 < α ∧ α ≤ 1)
    (N : Fin (d + 1) → ℕ)
    (F : (i : Fin (d + 1)) → Fin (N i) → Set (EuclideanSpace ℝ (Fin d)))
    (hF : ∀ i j, Convex ℝ (F i j))
    (h : α * ∏ i, (N i : ℝ) ≤
      ({c : (i : Fin (d + 1)) → Fin (N i) | (⋂ i, F i (c i)).Nonempty}.ncard : ℝ)) :
    ∃ i, ∃ G : Finset (Fin (N i)),
      α / (d + 1) * (N i : ℝ) ≤ (G.card : ℝ) ∧ (⋂ j ∈ G, F i j).Nonempty := by
  classical
  by_cases hN : ∀ i, 0 < N i
  · let C := (i : Fin (d + 1)) → Fin (N i)
    let T := {c : C // (⋂ i, F i (c i)).Nonempty}
    have hw : ∀ c : T, ∃ w, w ∈ ⋂ i, F i (c.1 i) := fun c => c.2
    choose w hw using hw
    let A (i : Fin (d + 1)) (j : Fin (N i)) : Set (EuclideanSpace ℝ (Fin d)) :=
      w '' {c : T | c.1 i = j}
    let K (i : Fin (d + 1)) (j : Fin (N i)) := convexHull ℝ (A i j)
    have hsub : ∀ i j, K i j ⊆ F i j := by
      intro i j
      apply convexHull_min
      · rintro x ⟨c, hc, rfl⟩
        have := mem_iInter.mp (hw c) i
        simpa only [show c.1 i = j from hc] using this
      · exact hF i j
    have hK : ∀ i j, IsCompact (K i j) := by
      intro i j
      exact ((Set.toFinite {c : T | c.1 i = j}).image w).isCompact_convexHull ℝ
    have hchoice : {c : C | (⋂ i, F i (c i)).Nonempty} ⊆
        {c : C | (⋂ i, K i (c i)).Nonempty} := by
      intro c hc
      refine ⟨w ⟨c, hc⟩, mem_iInter.mpr fun i => ?_⟩
      exact subset_convexHull ℝ (A i (c i)) ⟨⟨c, hc⟩, rfl, rfl⟩
    have hcount := Set.ncard_le_ncard hchoice
    have h' : α * ∏ i, (N i : ℝ) ≤
        ({c : C | (⋂ i, K i (c i)).Nonempty}.ncard : ℝ) :=
      h.trans (by exact_mod_cast hcount)
    obtain ⟨i, G, hG, x, hx⟩ := compact_fractional d α hα.1 N hN K
      (fun _ _ => convex_convexHull ℝ _) hK h'
    exact ⟨i, G, hG, x, mem_iInter₂.mpr fun j hj => hsub i j (mem_iInter₂.mp hx j hj)⟩
  · push Not at hN
    obtain ⟨i, hi⟩ := hN
    have hz : N i = 0 := by omega
    refine ⟨i, ∅, ?_, ?_⟩
    · simp [hz]
    · simp
