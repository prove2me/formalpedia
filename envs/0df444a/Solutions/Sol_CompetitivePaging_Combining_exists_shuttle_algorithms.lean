-- Prove2me | solution 1 for CompetitivePaging.Combining.exists_shuttle_algorithms
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T05:11:10.696621+00:00
-- url     : https://prove2.me/submissions/1d39fcd4-79e2-4911-8d6f-0aa227bee20d

import Mathlib
import Definitions.Def_KServer_model



namespace CompetitivePaging.Combining

theorem card_ne_aux {m : ℕ} (i : Fin m) :
    Fintype.card {p : Fin m × Fin 2 // p ≠ (i, 1)} = 2 * m - 1 := by
  rw [Fintype.card_subtype_compl, Fintype.card_prod]
  simp; ring_nf

noncomputable def shG {m : ℕ} (i : Fin m) : Fin (2 * m - 1) ≃ {p : Fin m × Fin 2 // p ≠ (i, 1)} :=
  (Fintype.equivFinOfCardEq (card_ne_aux i)).symm

def sideR {m : ℕ} {M : Type} (e : Fin m × Fin 2 ≃ M) (i : Fin m) : List M → Fin 2
  | [] => 0
  | x :: t => if (e.symm x).1 = i then (e.symm x).2 else sideR e i t

theorem sideR_snoc {m : ℕ} {M : Type} (e : Fin m × Fin 2 ≃ M) (i : Fin m) (l : List M) (x : M) :
    sideR e i (l ++ [x]).reverse = if (e.symm x).1 = i then (e.symm x).2 else sideR e i l.reverse := by
  simp [sideR]

theorem ne_i1 {m : ℕ} (i : Fin m) : ((i, 0) : Fin m × Fin 2) ≠ (i, 1) := by simp

noncomputable def shConf {m : ℕ} {M : Type} (e : Fin m × Fin 2 ≃ M) (i : Fin m)
    (l : List M) (j : Fin (2 * m - 1)) : M :=
  if ((shG i) j).1 = (i, 0) then e (i, sideR e i l.reverse) else e ((shG i) j).1

noncomputable def shuttle {m : ℕ} {M : Type} [MetricSpace M] (e : Fin m × Fin 2 ≃ M) (i : Fin m) :
    KServer.OnlineAlgorithm (2 * m - 1) M where
  conf := shConf e i
  serves := by
    intro l r
    by_cases hr : (e.symm r).1 = i
    · refine ⟨(shG i).symm ⟨(i, 0), ne_i1 i⟩, ?_⟩
      simp only [shConf, Equiv.apply_symm_apply, if_true, sideR_snoc, hr]
      rw [← hr]; simp
    · have hp : e.symm r ≠ (i, 1) := fun h => hr (by rw [h])
      refine ⟨(shG i).symm ⟨e.symm r, hp⟩, ?_⟩
      have hp0 : e.symm r ≠ (i, 0) := fun h => hr (by rw [h])
      simp [shConf, hp0]

theorem shuttle_cover {m : ℕ} {M : Type} [MetricSpace M] (e : Fin m × Fin 2 ≃ M) (i : Fin m)
    (l : List M) (x : M) (h0 : x ≠ e (i, 0)) (h1 : x ≠ e (i, 1)) :
    ∃ j, (shuttle e i).conf l j = x := by
  have hp : e.symm x ≠ (i, 1) := fun h => h1 (by rw [← h]; simp)
  have hp0 : e.symm x ≠ (i, 0) := fun h => h0 (by rw [← h]; simp)
  refine ⟨(shG i).symm ⟨e.symm x, hp⟩, ?_⟩
  simp [shuttle, shConf, hp0]

theorem shuttle_step {m : ℕ} {M : Type} [MetricSpace M]
    (hM : ∀ x y : M, x ≠ y → dist x y = 1) (e : Fin m × Fin 2 ≃ M) (i : Fin m)
    (l : List M) (x : M) :
    KServer.moveCost ((shuttle e i).conf l) ((shuttle e i).conf (l ++ [x])) ≤
      if (e.symm x).1 = i then 1 else 0 := by
  unfold KServer.moveCost
  set j0 := (shG i).symm ⟨(i, 0), ne_i1 i⟩
  rw [Finset.sum_eq_single j0]
  · simp only [shuttle, shConf, j0, Equiv.apply_symm_apply, if_true, sideR_snoc]
    split_ifs with h
    · by_cases hd : e (i, sideR e i l.reverse) = e (i, (e.symm x).2)
      · rw [hd, dist_self]; norm_num
      · rw [hM _ _ hd]
    · simp
  · intro j _ hj
    have : ((shG i) j).1 ≠ (i, 0) := by
      intro h
      apply hj
      simp only [j0]
      rw [Equiv.eq_symm_apply]
      exact Subtype.ext h
    simp [shuttle, shConf, this]
  · simp

theorem shuttle_core {m : ℕ} (hm : 0 < m) {M : Type} [MetricSpace M]
    (hM : ∀ x y : M, x ≠ y → dist x y = 1) (e : Fin m × Fin 2 ≃ M) :
    ∃ B : Fin m → KServer.OnlineAlgorithm (2 * m - 1) M,
      (∀ (i : Fin m) (l : List M) (x : M), x ≠ e (i, 0) → x ≠ e (i, 1) →
          ∃ j, (B i).conf l j = x) ∧
      (∀ (σ : List M) (s : ℕ), s < σ.length →
          ∑ i, KServer.moveCost ((B i).conf (σ.take s)) ((B i).conf (σ.take (s + 1))) ≤ 1) ∧
      ∀ σ : List M, ∑ i, (B i).cost σ ≤ (σ.length : ℝ) := by
  have hstep : ∀ (σ : List M) (s : ℕ), s < σ.length →
      ∑ i, KServer.moveCost ((shuttle e i).conf (σ.take s)) ((shuttle e i).conf (σ.take (s + 1))) ≤ 1 := by
    intro σ s hs
    rw [List.take_succ, List.getElem?_eq_getElem hs]
    simp only [Option.toList_some]
    calc _ ≤ ∑ i, (if (e.symm σ[s]).1 = i then (1 : ℝ) else 0) :=
          Finset.sum_le_sum fun i _ => shuttle_step hM e i _ _
      _ = 1 := by simp
  refine ⟨fun i => shuttle e i, fun i l x h0 h1 => shuttle_cover e i l x h0 h1, hstep, ?_⟩
  intro σ
  unfold KServer.OnlineAlgorithm.cost
  rw [Finset.sum_comm]
  calc _ ≤ ∑ s ∈ Finset.range σ.length, (1 : ℝ) :=
        Finset.sum_le_sum fun s hs => hstep σ s (Finset.mem_range.1 hs)
    _ = σ.length := by simp

end CompetitivePaging.Combining

open CompetitivePaging.Combining


theorem solution {m : ℕ} (hm : 0 < m) {M : Type} [MetricSpace M]
    (hM : ∀ x y : M, x ≠ y → dist x y = 1) (e : Fin m × Fin 2 ≃ M) :
    ∃ B : Fin m → KServer.OnlineAlgorithm (2 * m - 1) M,
      (∀ (i : Fin m) (l : List M) (x : M), x ≠ e (i, 0) → x ≠ e (i, 1) →
          ∃ j, (B i).conf l j = x) ∧
      (∀ (σ : List M) (s : ℕ), s < σ.length →
          ∑ i, KServer.moveCost ((B i).conf (σ.take s)) ((B i).conf (σ.take (s + 1))) ≤ 1) ∧
      ∀ σ : List M, ∑ i, (B i).cost σ ≤ (σ.length : ℝ) := by
  exact shuttle_core hm hM e
