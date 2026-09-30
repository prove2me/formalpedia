-- Prove2me | solution 1 for EdmondsKarp.Scaling.isMaxFlow_iff_no_augPath
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-30T06:28:30.548162+00:00
-- url     : https://prove2.me/submissions/079de176-af3a-4795-9d8b-7dab4ee69fed

import Mathlib
import Definitions.Def_EdmondsKarp_Scaling_Transport
import Definitions.Def_EdmondsKarp_Scaling_Augmentation

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace EdmondsKarp.Scaling

variable {m n : ℕ}

lemma ekAux_sum_update {m : ℕ} (f : Fin m → ℝ) (i : Fin m) (v : ℝ) :
    (∑ k, Function.update f i v k) = (∑ k, f k) - f i + v := by
  have h := Finset.sum_erase_add Finset.univ (fun k => Function.update f i v k) (Finset.mem_univ i)
  rw [← h]
  have h2 : ∑ k ∈ Finset.univ.erase i, Function.update f i v k = ∑ k ∈ Finset.univ.erase i, f k := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_erase] at hk
    exact Function.update_of_ne hk.1 v f
  rw [h2, Function.update_self]
  have h3 := Finset.sum_erase_add Finset.univ f (Finset.mem_univ i)
  rw [← h3]
  ring

lemma ekAux_exists_src {T : Transport m n} {x : Flow m n} {L : List (Node m n)}
    (hL : IsAugPath T x L) : ∃ i : Fin m, x.f0 i < T.a i := by
  obtain ⟨hnd, hhead, hlast, hpairs⟩ := hL
  cases L with
  | nil => exact absurd hhead (by simp)
  | cons a l =>
    rw [List.head?_cons, Option.some.injEq] at hhead
    subst hhead
    cases l with
    | nil =>
      rw [List.getLast?_singleton, Option.some.injEq] at hlast
      exact absurd hlast (by simp)
    | cons b l' =>
      have hpair : (Node.s, b) ∈ (Node.s :: b :: l').zip (Node.s :: b :: l').tail := by
        rw [List.tail_cons, List.zip_cons_cons]
        exact List.mem_cons_self
      have hp := hpairs (.s, b) hpair
      cases b with
      | s => exact absurd hp (by simp [resCap])
      | t => exact absurd hp (by simp [resCap])
      | src i =>
        refine ⟨i, ?_⟩
        have hp' : (0 : WithTop ℝ) < ((T.a i - x.f0 i : ℝ) : WithTop ℝ) := hp
        have hpos : (0 : ℝ) < T.a i - x.f0 i := by
          rw [← WithTop.coe_zero] at hp'
          exact WithTop.coe_lt_coe.mp hp'
        linarith
      | dst j => exact absurd hp (by simp [resCap])

lemma ekAux_exists_pair_getLast? :
    ∀ (L : List (Node m n)) (u v : Node m n),
      L.head? = some u → L.getLast? = some v → u ≠ v →
        ∃ w : Node m n, (w, v) ∈ L.zip L.tail
  | [], u, v, h1, _, _ => by exact absurd h1 (by simp)
  | a :: [], u, v, h1, h2, huv => by
      rw [List.head?_cons, Option.some.injEq] at h1
      rw [List.getLast?_singleton, Option.some.injEq] at h2
      exact absurd (h1.symm.trans h2) huv
  | a :: b :: l, u, v, h1, h2, huv => by
      by_cases hbv : b = v
      · refine ⟨a, ?_⟩
        rw [List.tail_cons, List.zip_cons_cons]
        simp [hbv]
      · have h2' : (b :: l).getLast? = some v := by
          simpa only [List.getLast?_cons_cons] using h2
        obtain ⟨w, hw⟩ := ekAux_exists_pair_getLast? (b :: l) b v rfl h2' hbv
        refine ⟨w, ?_⟩
        rw [List.tail_cons, List.zip_cons_cons]
        exact List.mem_cons_of_mem _ hw

lemma ekAux_exists_dst {T : Transport m n} {x : Flow m n} {L : List (Node m n)}
    (hL : IsAugPath T x L) : ∃ j : Fin n, x.fz j < T.b j := by
  obtain ⟨hnd, hhead, hlast, hpairs⟩ := hL
  obtain ⟨w, hw⟩ := ekAux_exists_pair_getLast? L .s .t hhead hlast (by simp)
  have hp := hpairs (w, .t) hw
  cases w with
  | s => exact absurd hp (by simp [resCap])
  | t => exact absurd hp (by simp [resCap])
  | src i => exact absurd hp (by simp [resCap])
  | dst j =>
    refine ⟨j, ?_⟩
    have hp' : (0 : WithTop ℝ) < ((T.b j - x.fz j : ℝ) : WithTop ℝ) := hp
    have hpos : (0 : ℝ) < T.b j - x.fz j := by
      rw [← WithTop.coe_zero] at hp'
      exact WithTop.coe_lt_coe.mp hp'
    linarith

lemma ekAux_simple_augPath {T : Transport m n} {x : Flow m n} {i : Fin m} {j : Fin n}
    (hi : x.f0 i < T.a i) (hj : x.fz j < T.b j) :
    IsAugPath T x [.s, .src i, .dst j, .t] := by
  refine ⟨by simp, rfl, rfl, ?_⟩
  intro e he
  simp at he
  rcases he with rfl | rfl | rfl
  · show (0 : WithTop ℝ) < ((T.a i - x.f0 i : ℝ) : WithTop ℝ)
    rw [← WithTop.coe_zero]
    exact WithTop.coe_lt_coe.mpr (sub_pos.mpr hi)
  · show (0 : WithTop ℝ) < (⊤ : WithTop ℝ)
    simp
  · show (0 : WithTop ℝ) < ((T.b j - x.fz j : ℝ) : WithTop ℝ)
    rw [← WithTop.coe_zero]
    exact WithTop.coe_lt_coe.mpr (sub_pos.mpr hj)

lemma ekAux_saturated_or {T : Transport m n} {x : Flow m n} (hx : IsFlow T x)
    (hno : ¬ ∃ L : List (Node m n), IsAugPath T x L) :
    (∀ i : Fin m, x.f0 i = T.a i) ∨ (∀ j : Fin n, x.fz j = T.b j) := by
  by_cases h : ∃ i : Fin m, x.f0 i < T.a i
  · right
    intro j
    have hle : x.fz j ≤ T.b j := hx.2.2.2.2.2.1 j
    by_contra hne
    have hlt : x.fz j < T.b j := lt_of_le_of_ne hle hne
    exact hno ⟨_, ekAux_simple_augPath h.choose_spec hlt⟩
  · left
    intro i
    have hle : x.f0 i ≤ T.a i := hx.2.2.2.2.1 i
    exact le_antisymm hle (not_lt.mp fun hlt => h ⟨i, hlt⟩)

end EdmondsKarp.Scaling

open EdmondsKarp.Scaling

theorem solution {m n : ℕ} (T : Transport m n) (x : Flow m n) (hx : IsFlow T x) :
    IsMaxFlow T x ↔ ¬ ∃ L : List (Node m n), IsAugPath T x L := by
  constructor
  · rintro ⟨hmaxf, hmax⟩ ⟨L, hL⟩
    obtain ⟨i, hi⟩ := ekAux_exists_src hL
    obtain ⟨j, hj⟩ := ekAux_exists_dst hL
    have hi0 : 0 < T.a i - x.f0 i := by linarith
    have hj0 : 0 < T.b j - x.fz j := by linarith
    let ε : ℝ := min (T.a i - x.f0 i) (T.b j - x.fz j)
    have hεpos : 0 < ε := lt_min hi0 hj0
    have hεa : ε ≤ T.a i - x.f0 i := min_le_left _ _
    have hεb : ε ≤ T.b j - x.fz j := min_le_right _ _
    let y : Flow m n :=
      { f0 := Function.update x.f0 i (x.f0 i + ε)
        fx := Function.update x.fx i (Function.update (x.fx i) j (x.fx i j + ε))
        fz := Function.update x.fz j (x.fz j + ε)
        ret := x.ret + ε }
    have hf0_i : y.f0 i = x.f0 i + ε := by simp only [y, Function.update_self]
    have hf0_ne : ∀ k, k ≠ i → y.f0 k = x.f0 k := by
      intro k hk
      simp only [y, Function.update_of_ne hk]
    have hfz_j : y.fz j = x.fz j + ε := by simp only [y, Function.update_self]
    have hfz_ne : ∀ k, k ≠ j → y.fz k = x.fz k := by
      intro k hk
      simp only [y, Function.update_of_ne hk]
    have hfx_ij : y.fx i j = x.fx i j + ε := by simp only [y, Function.update_self]
    have hfx_i_ne : ∀ l, l ≠ j → y.fx i l = x.fx i l := by
      intro l hl
      simp only [y, Function.update_self, Function.update_of_ne hl]
    have hfx_ne : ∀ k, k ≠ i → y.fx k = x.fx k := by
      intro k hk
      funext l
      simp only [y, Function.update_of_ne hk]
    have hsum_f0 : (∑ k, y.f0 k) = (∑ k, x.f0 k) + ε := by
      dsimp only [y]
      rw [ekAux_sum_update]
      ring
    have hsum_fz : (∑ k, y.fz k) = (∑ k, x.fz k) + ε := by
      dsimp only [y]
      rw [ekAux_sum_update]
      ring
    have hsum_fx_row : ∀ k, (∑ l, y.fx k l) = (∑ l, x.fx k l) + (if k = i then ε else 0) := by
      intro k
      by_cases hk : k = i
      · subst hk
        dsimp only [y]
        rw [Function.update_self, ekAux_sum_update]
        simp
        ring
      · rw [hfx_ne k hk]
        simp [hk]
    have hsum_fx_col : ∀ l, (∑ k, y.fx k l) = (∑ k, x.fx k l) + (if l = j then ε else 0) := by
      intro l
      by_cases hl : l = j
      · have hfun : (fun k => y.fx k l) =
            Function.update (fun k => x.fx k l) i (x.fx i l + ε) := by
          funext k
          by_cases hk : k = i
          · subst hk
            simp only [y, Function.update_self]
            rw [← hl, Function.update_self]
          · simp only [y, Function.update_of_ne hk]
        rw [hfun, ekAux_sum_update, if_pos hl]
        ring
      · have hfun : (fun k => y.fx k l) = (fun k => x.fx k l) := by
          funext k
          by_cases hk : k = i
          · subst hk
            exact hfx_i_ne l hl
          · exact congrFun (hfx_ne k hk) l
        rw [hfun]
        simp [hl]
    have hyret : y.ret = x.ret + ε := rfl
    have hy : IsFlow T y := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro k
        by_cases hk : k = i
        · subst hk
          rw [hf0_i]
          linarith [hx.1 k, hεpos]
        · rw [hf0_ne k hk]
          exact hx.1 k
      · intro k l
        by_cases hk : k = i
        · subst hk
          by_cases hl : l = j
          · subst hl
            rw [hfx_ij]
            linarith [hx.2.1 k l, hεpos]
          · rw [hfx_i_ne l hl]
            exact hx.2.1 k l
        · rw [congrFun (hfx_ne k hk) l]
          exact hx.2.1 k l
      · intro k
        by_cases hk : k = j
        · subst hk
          rw [hfz_j]
          linarith [hx.2.2.1 k, hεpos]
        · rw [hfz_ne k hk]
          exact hx.2.2.1 k
      · rw [hyret]
        linarith [hx.2.2.2.1, hεpos]
      · intro k
        by_cases hk : k = i
        · subst hk
          rw [hf0_i]
          linarith [hεa, hx.2.2.2.2.1 k]
        · rw [hf0_ne k hk]
          exact hx.2.2.2.2.1 k
      · intro k
        by_cases hk : k = j
        · subst hk
          rw [hfz_j]
          linarith [hεb, hx.2.2.2.2.2.1 k]
        · rw [hfz_ne k hk]
          exact hx.2.2.2.2.2.1 k
      · rw [hsum_f0, hyret]
        linarith [hx.2.2.2.2.2.2.1]
      · intro k
        rw [hsum_fx_row k]
        by_cases hk : k = i
        · subst hk
          rw [if_pos rfl, hf0_i]
          linarith [hx.2.2.2.2.2.2.2.1 k]
        · rw [if_neg hk, hf0_ne k hk]
          simpa using hx.2.2.2.2.2.2.2.1 k
      · intro l
        rw [hsum_fx_col l]
        by_cases hl : l = j
        · subst hl
          rw [if_pos rfl, hfz_j]
          linarith [hx.2.2.2.2.2.2.2.2.1 l]
        · rw [if_neg hl, hfz_ne l hl]
          simpa using hx.2.2.2.2.2.2.2.2.1 l
      · rw [hsum_fz, hyret]
        linarith [hx.2.2.2.2.2.2.2.2.2]
    have hle := hmax y hy
    rw [hyret] at hle
    linarith
  · intro hno
    refine ⟨hx, fun y hy => ?_⟩
    rcases ekAux_saturated_or hx hno with hsat | hsat
    · calc y.ret = ∑ i, y.f0 i := by linarith [hy.2.2.2.2.2.2.1]
        _ ≤ ∑ i, T.a i := Finset.sum_le_sum fun i _ => hy.2.2.2.2.1 i
        _ = ∑ i, x.f0 i := by
            apply Finset.sum_congr rfl
            intro i _
            exact (hsat i).symm
        _ = x.ret := by linarith [hx.2.2.2.2.2.2.1]
    · calc y.ret = ∑ j, y.fz j := by linarith [hy.2.2.2.2.2.2.2.2.2]
        _ ≤ ∑ j, T.b j := Finset.sum_le_sum fun j _ => hy.2.2.2.2.2.1 j
        _ = ∑ j, x.fz j := by
            apply Finset.sum_congr rfl
            intro j _
            exact (hsat j).symm
        _ = x.ret := by linarith [hx.2.2.2.2.2.2.2.2.2]
