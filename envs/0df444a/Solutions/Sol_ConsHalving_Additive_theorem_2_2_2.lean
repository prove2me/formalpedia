-- Prove2me | solution 2 for ConsHalving.Additive.theorem_2_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T15:28:39.223555+00:00
-- url     : https://prove2.me/submissions/ed6f9113-8291-42c4-bcaa-b5da34b72cfb

import Mathlib
import Definitions.Def_ConsHalving_Additive_Setting

set_option autoImplicit false
open ConsHalving.Additive

theorem ch_affine {n m : ℕ} (u : Fin n → Fin m → ℝ) (x y : Fin m → ℝ) (γ : ℝ)
    (hx : SolvesS u x) (hy : SolvesS u y) : SolvesS u (stepPoint x y γ) := by
  intro i
  have h1 := hx i
  have h2 := hy i
  have : ∑ j, (stepPoint x y γ j - 1/2) * u i j
      = (1-γ) * ∑ j, (x j - 1/2) * u i j + γ * ∑ j, (y j - 1/2) * u i j := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [stepPoint]; ring
  rw [this, h1, h2]; ring
theorem ch_gamma_nonneg {m : ℕ} (x y : Fin m → ℝ) (hx : IsFractional x) (j : Fin m)
    (hne : y j ≠ x j) : 0 ≤ gamma x y j := by
  unfold gamma
  split_ifs with h
  · exact div_nonneg (by linarith [(hx j).2]) (by linarith)
  · have : y j < x j := lt_of_le_of_ne (not_lt.mp h) hne
    exact div_nonneg (hx j).1 (by linarith)

theorem ch_step_mem {m : ℕ} (x y : Fin m → ℝ) (hx : IsFractional x) (j : Fin m)
    (hne : y j ≠ x j) (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ gamma x y j) :
    0 ≤ stepPoint x y γ j ∧ stepPoint x y γ j ≤ 1 := by
  unfold gamma at h1
  unfold stepPoint
  have hxj := hx j
  split_ifs at h1 with h
  · have hpos : 0 < y j - x j := by linarith
    have := (le_div_iff₀ hpos).mp h1
    constructor <;> nlinarith [hxj.1, hxj.2, mul_nonneg h0 hpos.le]
  · have hlt : y j < x j := lt_of_le_of_ne (not_lt.mp h) hne
    have hpos : 0 < x j - y j := by linarith
    have := (le_div_iff₀ hpos).mp h1
    constructor <;> nlinarith [hxj.1, hxj.2, mul_nonneg h0 hpos.le]

theorem ch_step_jstar {m : ℕ} (x y : Fin m → ℝ) (j : Fin m) (hne : y j ≠ x j) :
    stepPoint x y (gamma x y j) j = 0 ∨ stepPoint x y (gamma x y j) j = 1 := by
  unfold stepPoint gamma
  split_ifs with h
  · right
    have hd : y j - x j ≠ 0 := sub_ne_zero.mpr hne
    field_simp
    ring
  · left
    have hlt : y j < x j := lt_of_le_of_ne (not_lt.mp h) hne
    have hd : x j - y j ≠ 0 := by linarith
    field_simp
    ring

theorem ch_3c {m : ℕ} (x y : Fin m → ℝ) (jstar : Fin m)
    (hx : IsFractional x) (hstar : y jstar ≠ x jstar)
    (hmin : ∀ j, y j ≠ x j → gamma x y jstar ≤ gamma x y j) :
    IsFractional (stepPoint x y (gamma x y jstar)) ∧
      (∀ j, y j = x j → stepPoint x y (gamma x y jstar) j = x j) ∧
      (stepPoint x y (gamma x y jstar) jstar = 0 ∨
        stepPoint x y (gamma x y jstar) jstar = 1) := by
  have h0 : 0 ≤ gamma x y jstar := ch_gamma_nonneg x y hx jstar hstar
  have key : ∀ j, y j = x j → stepPoint x y (gamma x y jstar) j = x j := by
    intro j hj
    simp only [stepPoint, hj]
    ring
  refine ⟨fun j => ?_, key, ch_step_jstar x y jstar hstar⟩
  by_cases hne : y j = x j
  · rw [key j hne]
    exact hx j
  · exact ch_step_mem x y hx j hne _ h0 (hmin j hne)
theorem ch_solvesS_iff {n m : ℕ} (u : Fin n → Fin m → ℝ) (x : Fin m → ℝ) :
    SolvesS u x ↔ ∀ i, util u i x = util u i (fun j => 1 - x j) := by
  have key : ∀ i, util u i x - util u i (fun j => 1 - x j) = 2 * ∑ j, (x j - 1 / 2) * u i j := by
    intro i
    unfold util
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  constructor
  · intro h i
    have := key i
    rw [h i] at this
    linarith
  · intro h i
    have := key i
    rw [h i] at this
    linarith

theorem ch_inv {n m : ℕ} (u : Fin n → Fin m → ℝ) (T : Finset (Fin m))
    (x y : Fin m → ℝ) (jstar : Fin m)
    (hx : IsConsensusHalving u x) (hT : ∀ j ∈ T, x j = 0 ∨ x j = 1)
    (hy : SolvesST u T x y) (hstar : y jstar ≠ x jstar)
    (hmin : ∀ j, y j ≠ x j → gamma x y jstar ≤ gamma x y j) :
    IsConsensusHalving u (stepPoint x y (gamma x y jstar)) ∧ jstar ∉ T ∧
      ∀ j ∈ insert jstar T,
        stepPoint x y (gamma x y jstar) j = 0 ∨ stepPoint x y (gamma x y jstar) j = 1 := by
  have hxS : SolvesS u x := (ch_solvesS_iff u x).2 hx.2
  have hsS : SolvesS u (stepPoint x y (gamma x y jstar)) := ch_affine u x y _ hxS hy.1
  have h3 := ch_3c x y jstar hx.1 hstar hmin
  have hnT : jstar ∉ T := fun h => hstar (hy.2 jstar h)
  refine ⟨⟨h3.1, (ch_solvesS_iff u _).1 hsS⟩, hnT, ?_⟩
  intro j hj
  rcases Finset.mem_insert.1 hj with h | h
  · rw [h]
    exact h3.2.2
  · rw [h3.2.1 j (hy.2 j h)]
    exact hT j h
theorem ch_term {n m : ℕ} (u : Fin n → Fin m → ℝ) (T : Finset (Fin m))
    (x : Fin m → ℝ) (hx : SolvesS u x) (huniq : ∀ y, SolvesST u T x y → y = x) :
    m ≤ n + T.card := by
  classical
  let L : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ) × (T → ℝ) :=
    { toFun := fun d => (fun i => ∑ j, d j * u i j, fun t => d t)
      map_add' := by
        intro a b
        ext <;> simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro c a
        ext <;> simp [Finset.mul_sum, mul_assoc] }
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro d hd
    have hd1 : ∀ i, ∑ j, d j * u i j = 0 := fun i => by
      have := congrArg (fun p => p.1 i) hd
      simpa [L] using this
    have hd2 : ∀ j ∈ T, d j = 0 := fun j hj => by
      have := congrArg (fun p => p.2 ⟨j, hj⟩) hd
      simpa [L] using this
    have hy : SolvesST u T x (fun j => x j + d j) := by
      refine ⟨fun i => ?_, fun j hj => ?_⟩
      · have h1 := hx i
        have h2 := hd1 i
        have : ∑ j, (x j + d j - 1 / 2) * u i j
            = ∑ j, (x j - 1 / 2) * u i j + ∑ j, d j * u i j := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun j _ => by ring
        rw [this, h1, h2]; ring
      · simp [hd2 j hj]
    have := huniq _ hy
    funext j
    have := congrFun this j
    simpa using this
  have := LinearMap.finrank_le_finrank_of_injective hinj
  simpa using this
theorem ch_main {n m : ℕ} (u : Fin n → Fin m → ℝ) :
    ∀ k : ℕ, ∀ x : Fin m → ℝ, IsConsensusHalving u x → numCuts x = k →
      ∃ x' : Fin m → ℝ, IsConsensusHalving u x' ∧ numCuts x' ≤ n := by
  classical
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro x hx hk
    by_cases hle : numCuts x ≤ n
    · exact ⟨x, hx, hle⟩
    · push_neg at hle
      have hxS : SolvesS u x := (ch_solvesS_iff u x).2 hx.2
      let T : Finset (Fin m) := Finset.univ.filter (fun j => ¬ IsCut x j)
      have hcard : numCuts x + T.card = m := by
        have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m)))
          (fun j => IsCut x j)
        simpa [numCuts, T] using this
      have hnot : ¬ ∀ y, SolvesST u T x y → y = x := by
        intro h
        have := ch_term u T x hxS h
        omega
      push_neg at hnot
      obtain ⟨y, hy, hyx⟩ := hnot
      obtain ⟨j0, hj0⟩ : ∃ j, y j ≠ x j := by
        by_contra hcon
        push_neg at hcon
        exact hyx (funext hcon)
      let D : Finset (Fin m) := Finset.univ.filter (fun j => y j ≠ x j)
      have hD : D.Nonempty := ⟨j0, by simp [D, hj0]⟩
      obtain ⟨jstar, hjD, hjmin⟩ := Finset.exists_min_image D (gamma x y) hD
      have hstar : y jstar ≠ x jstar := by simpa [D] using hjD
      have hmin : ∀ j, y j ≠ x j → gamma x y jstar ≤ gamma x y j :=
        fun j hj => hjmin j (by simp [D, hj])
      have hT : ∀ j ∈ T, x j = 0 ∨ x j = 1 := by
        intro j hj
        have hj' : ¬ IsCut x j := by simpa [T] using hj
        have h1 := hx.1 j
        by_contra hcon
        push_neg at hcon
        apply hj'
        exact ⟨lt_of_le_of_ne h1.1 (Ne.symm hcon.1), by
          have := lt_of_le_of_ne h1.2 hcon.2
          linarith⟩
      obtain ⟨hs, hjT, hs01⟩ := ch_inv u T x y jstar hx hT hy hstar hmin
      have hlt : numCuts (stepPoint x y (gamma x y jstar)) < numCuts x := by
        unfold numCuts
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset]
        · refine ⟨jstar, ?_, ?_⟩
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            by_contra hc
            exact hjT (by simpa [T] using hc)
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            rintro ⟨h1, h2⟩
            rcases hs01 jstar (Finset.mem_insert_self _ _) with h | h
            · rw [h] at h1; exact lt_irrefl _ h1
            · rw [h] at h2; simp at h2
        · intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
          by_contra hc
          have hjT' : j ∈ T := by simpa [T] using hc
          rcases hs01 j (Finset.mem_insert_of_mem hjT') with h | h
          · obtain ⟨h1, h2⟩ := hj
            rw [h] at h1; exact lt_irrefl _ h1
          · obtain ⟨h1, h2⟩ := hj
            rw [h] at h2; simp at h2
      exact ih _ (hk ▸ hlt) _ hs rfl

theorem solution {n m : ℕ} (u : Fin n → Fin m → ℝ) (hu : ∀ i j, 0 ≤ u i j) :
    ∃ x : Fin m → ℝ, IsConsensusHalving u x ∧ numCuts x ≤ min n m := by
  have h0 : IsConsensusHalving u (fun _ : Fin m => (1 / 2 : ℝ)) :=
    ⟨fun j => ⟨by norm_num, by norm_num⟩, fun i => by
      unfold util
      exact Finset.sum_congr rfl fun j _ => by norm_num⟩
  obtain ⟨x, hx, hn⟩ := ch_main u _ _ h0 rfl
  refine ⟨x, hx, le_min hn ?_⟩
  unfold numCuts
  classical
  calc _ ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_filter_le _ _
    _ = m := by simp
