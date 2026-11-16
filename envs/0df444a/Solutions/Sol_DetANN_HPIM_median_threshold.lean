-- Prove2me | solution 1 for DetANN.HPIM.median_threshold
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-16T05:54:31.458404+00:00
-- url     : https://prove2.me/submissions/e5478abe-a385-4625-a27e-d8938169c874

import Mathlib
import Definitions.Def_DetANN_HPIMThreshold

namespace DetANN.HPIMThrAux

open DetANN.HPIM

variable {m : ℕ}

section M4

open Classical

variable {n : ℕ} (P : Fin n → EuclideanSpace ℝ (Fin m))

lemma thrReach_of_dist {d : ℝ} {i j : Fin n} (h : dist (P i) (P j) ≤ d) : thrReach P d i j := by
  by_cases hij : i = j
  · subst hij; exact SimpleGraph.Reachable.refl _
  · exact SimpleGraph.Adj.reachable (by rw [SimpleGraph.fromRel_adj]; exact ⟨hij, Or.inl h⟩)

lemma thrReach_symm {d : ℝ} {i j : Fin n} (h : thrReach P d i j) : thrReach P d j i :=
  SimpleGraph.Reachable.symm h

lemma thrReach_trans {d : ℝ} {i j k : Fin n} (h : thrReach P d i j) (h' : thrReach P d j k) :
    thrReach P d i k :=
  SimpleGraph.Reachable.trans h h'

lemma dist_le_of_walk {d : ℝ} {i j : Fin n}
    (w : (SimpleGraph.fromRel fun a b => dist (P a) (P b) ≤ d).Walk i j) :
    dist (P i) (P j) ≤ w.length * d := by
  induction w with
  | nil => simp
  | @cons u v w' hadj w ih =>
    rw [SimpleGraph.fromRel_adj] at hadj
    have h1 : dist (P u) (P v) ≤ d := by
      rcases hadj.2 with h | h
      · exact h
      · rwa [dist_comm]
    rw [SimpleGraph.Walk.length_cons]; push_cast
    linarith [dist_triangle (P u) (P v) (P w')]

/-- Points joined in the threshold graph are within `(n − 1)·d` of each other. -/
lemma dist_le_of_thrReach {d : ℝ} (hd : 0 ≤ d) {i j : Fin n} (h : thrReach P d i j) :
    dist (P i) (P j) ≤ ((n : ℝ) - 1) * d := by
  obtain ⟨w⟩ := h
  have hp := (w.bypass_isPath).length_lt
  have hlen : (w.bypass.length : ℝ) ≤ (n : ℝ) - 1 := by
    have : w.bypass.length + 1 ≤ n := by simpa [Fintype.card_fin] using hp
    have : ((w.bypass.length + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast this
    push_cast at this; linarith
  exact (dist_le_of_walk P w.bypass).trans (by gcongr)

lemma thrReach_eq_of_noedge {d : ℝ} (hno : ∀ a b : Fin n, a ≠ b → d < dist (P a) (P b))
    {i j : Fin n} (h : thrReach P d i j) : i = j := by
  obtain ⟨w⟩ := h
  cases w with
  | nil => rfl
  | cons hadj _ =>
    rw [SimpleGraph.fromRel_adj] at hadj
    exfalso
    rcases hadj.2 with h | h
    · exact absurd h (not_le.2 (hno _ _ hadj.1))
    · exact absurd h (not_le.2 (hno _ _ (Ne.symm hadj.1)))

lemma card_reach_of_noedge {d : ℝ} (hno : ∀ a b : Fin n, a ≠ b → d < dist (P a) (P b)) (i : Fin n) :
    (Finset.univ.filter (thrReach P d i)).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨i, ?_⟩
  ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact ⟨fun h => (thrReach_eq_of_noedge P hno h).symm, fun h => h ▸ SimpleGraph.Reachable.refl _⟩

/-- **M4 (median threshold).** For `n ≥ 2` distinct points: the threshold has a component with
`≥ ⌊n/2⌋+1` points, it is positive, and below it every component has `≤ ⌊n/2⌋` points. -/
lemma medThreshold_spec (hn : 2 ≤ n) (hP : Function.Injective P) :
    (∃ i, n / 2 + 1 ≤ (Finset.univ.filter (thrReach P (medThreshold P) i)).card) ∧
    0 < medThreshold P ∧
    ∀ d' < medThreshold P, ∀ i, (Finset.univ.filter (thrReach P d' i)).card ≤ n / 2 := by
  have i0 : Fin n := ⟨0, by omega⟩
  set D : Finset ℝ := (Finset.univ ×ˢ Finset.univ).image
    fun ij : Fin n × Fin n => dist (P ij.1) (P ij.2) with hD
  set cand := D.filter fun d => ∃ i, n / 2 + 1 ≤ (Finset.univ.filter (thrReach P d i)).card
    with hcand
  -- the largest distance is a candidate
  have hDne : D.Nonempty := ⟨dist (P i0) (P i0), Finset.mem_image.2 ⟨(i0, i0), by simp, rfl⟩⟩
  have hmaxc : D.max' hDne ∈ cand := by
    refine Finset.mem_filter.2 ⟨D.max'_mem hDne, i0, ?_⟩
    have : Finset.univ.filter (thrReach P (D.max' hDne) i0) = Finset.univ := by
      ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact thrReach_of_dist P (D.le_max' _ (Finset.mem_image.2 ⟨(i0, j), by simp, rfl⟩))
    rw [this, Finset.card_univ, Fintype.card_fin]; omega
  have hne : cand.Nonempty := ⟨_, hmaxc⟩
  have hmed : medThreshold P = cand.min' hne := by
    unfold medThreshold; rw [dif_pos hne]
  have hmem := cand.min'_mem hne
  rw [← hmed] at hmem
  obtain ⟨hmD, hbig⟩ := Finset.mem_filter.1 hmem
  -- no edges below a value `d` if every pairwise distance exceeds `d`
  have hpos : 0 < medThreshold P := by
    obtain ⟨⟨a, b⟩, -, hab⟩ := Finset.mem_image.1 hmD
    have h0 : 0 ≤ medThreshold P := hab ▸ dist_nonneg
    rcases h0.lt_or_eq with h | h
    · exact h
    · exfalso
      obtain ⟨i, hi⟩ := hbig
      have hno : ∀ a b : Fin n, a ≠ b → medThreshold P < dist (P a) (P b) := by
        intro a b hab'; rw [← h]; exact dist_pos.2 (fun e => hab' (hP e))
      rw [card_reach_of_noedge P hno] at hi; omega
  refine ⟨hbig, hpos, fun d' hd' i => ?_⟩
  by_contra hcon
  push Not at hcon
  -- reduce `d'` to the largest pairwise distance below it
  by_cases hneg : d' < 0
  · have hno : ∀ a b : Fin n, a ≠ b → d' < dist (P a) (P b) := fun a b _ =>
      lt_of_lt_of_le hneg dist_nonneg
    rw [card_reach_of_noedge P hno] at hcon; omega
  push Not at hneg
  set Dl := D.filter (· ≤ d')
  have hDl : Dl.Nonempty := ⟨0, Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨(i0, i0),
    Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_univ _⟩, dist_self _⟩, hneg⟩⟩
  set d'' := Dl.max' hDl
  have hd''D : d'' ∈ D := (Finset.mem_filter.1 (Dl.max'_mem hDl)).1
  have hd''le : d'' ≤ d' := (Finset.mem_filter.1 (Dl.max'_mem hDl)).2
  have hsame : ∀ j, thrReach P d' i j ↔ thrReach P d'' i j := by
    have hG : (SimpleGraph.fromRel fun a b => dist (P a) (P b) ≤ d') =
        (SimpleGraph.fromRel fun a b => dist (P a) (P b) ≤ d'') := by
      ext a b
      simp only [SimpleGraph.fromRel_adj]
      have key : ∀ a b : Fin n, dist (P a) (P b) ≤ d' ↔ dist (P a) (P b) ≤ d'' := by
        intro a b
        refine ⟨fun h => Dl.le_max' _ (Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨(a, b),
          Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_univ _⟩, rfl⟩, h⟩),
          fun h => h.trans hd''le⟩
      rw [key a b, key b a]
    intro j; unfold thrReach; rw [hG]
  have hcand'' : d'' ∈ cand := by
    refine Finset.mem_filter.2 ⟨hd''D, i, ?_⟩
    have : Finset.univ.filter (thrReach P d'' i) = Finset.univ.filter (thrReach P d' i) := by
      ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact (hsame j).symm
    rw [this]; omega
  have := cand.min'_le _ hcand''
  rw [← hmed] at this
  linarith

/-- Every point has a representative in its component. -/
lemma exists_rep (d : ℝ) (i : Fin n) : ∃ j, thrReach P d i j ∧ IsRep P d j := by
  set C := Finset.univ.filter (thrReach P d i)
  have hC : C.Nonempty := ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, SimpleGraph.Reachable.refl _⟩⟩
  refine ⟨C.min' hC, (Finset.mem_filter.1 (C.min'_mem hC)).2, fun k hk => ?_⟩
  exact C.min'_le _ (Finset.mem_filter.2 ⟨Finset.mem_univ _,
    thrReach_trans P (Finset.mem_filter.1 (C.min'_mem hC)).2 (thrReach_symm P hk)⟩)

/-- **M4 (representatives).** If some component has `≥ ⌊n/2⌋+1` points, there are at most
`⌈n/2⌉` representatives. -/
lemma card_reps_le (d : ℝ) (i₀ : Fin n)
    (hbig : n / 2 + 1 ≤ (Finset.univ.filter (thrReach P d i₀)).card) :
    (Finset.univ.filter (IsRep P d)).card ≤ (n + 1) / 2 := by
  set C := Finset.univ.filter (thrReach P d i₀)
  set R := Finset.univ.filter (IsRep P d)
  have hRC : (R.filter (· ∈ C)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [R, C, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    have hab : thrReach P d a b := thrReach_trans P (thrReach_symm P ha.2) hb.2
    exact le_antisymm (ha.1 b (thrReach_symm P hab)) (hb.1 a hab)
  have hRnC : (R.filter (· ∉ C)).card ≤ n - C.card := by
    have : R.filter (· ∉ C) ⊆ Finset.univ \ C := by
      intro a ha; simp only [Finset.mem_filter] at ha; simp [ha.2]
    refine (Finset.card_le_card this).trans ?_
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
  have hsplit := Finset.card_filter_add_card_filter_not (s := R) (p := fun a => a ∈ C)
  have hCn : C.card ≤ n := by
    simpa [Fintype.card_fin] using Finset.card_le_univ C
  omega

end M4

end DetANN.HPIMThrAux

open Classical in
open DetANN.HPIM DetANN.HPIMThrAux in
theorem solution {m n : ℕ} (P : Fin n → EuclideanSpace ℝ (Fin m)) :
    (∀ d : ℝ, 0 ≤ d → ∀ i j, thrReach P d i j → dist (P i) (P j) ≤ ((n : ℝ) - 1) * d) ∧
    (∀ (d : ℝ) (i : Fin n), ∃ j, thrReach P d i j ∧ IsRep P d j) ∧
    (∀ (d : ℝ) (i₀ : Fin n), n / 2 + 1 ≤ (Finset.univ.filter (thrReach P d i₀)).card →
      (Finset.univ.filter (IsRep P d)).card ≤ (n + 1) / 2) ∧
    (2 ≤ n → Function.Injective P →
      (∃ i, n / 2 + 1 ≤ (Finset.univ.filter (thrReach P (medThreshold P) i)).card) ∧
      0 < medThreshold P ∧
      ∀ d < medThreshold P, ∀ i, (Finset.univ.filter (thrReach P d i)).card ≤ n / 2) :=
  ⟨fun _ hd _ _ h => dist_le_of_thrReach P hd h, fun d i => exists_rep P d i,
    fun d i₀ h => card_reps_le P d i₀ h, fun hn hP => medThreshold_spec P hn hP⟩
