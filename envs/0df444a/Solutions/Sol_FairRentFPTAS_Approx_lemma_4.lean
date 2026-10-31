-- Prove2me | solution 1 for FairRentFPTAS.Approx.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T12:36:19.425384+00:00
-- url     : https://prove2.me/submissions/41c63ba7-d8ae-438d-b5ea-82ebd2fe4cb6

import Mathlib
import Definitions.Def_FairRentFPTAS_Approx_Model
import Theorems.Thm_FairRentFPTAS_Approx_lemma_2

open FairRentFPTAS.Approx

namespace FRFL4Aux

/-- `drop` vanishes at a point below every start of a sorted list. -/
lemma drop_eq_zero (x : ℝ) : ∀ (l : List (ℝ × ℝ)), (l.map Prod.fst).Pairwise (· < ·) →
    (∀ e ∈ l, x ≤ e.1) → PLFun.drop l x = 0 := by
  intro l
  induction l with
  | nil => intro _ _; simp [PLFun.drop]
  | cons e t ih =>
    intro hs hx
    cases t with
    | nil =>
      have := hx e (by simp)
      simp [PLFun.drop, max_eq_right this]
    | cons e' t' =>
      have hs' : ((e' :: t').map Prod.fst).Pairwise (· < ·) := (List.pairwise_cons.mp hs).2
      have hee' : e.1 < e'.1 := (List.pairwise_cons.mp hs).1 e'.1 (by simp)
      have := hx e (by simp)
      simp only [PLFun.drop]
      rw [ih hs' (fun y hy => hx y (List.mem_cons_of_mem _ hy)), max_eq_right this,
        min_eq_left hee'.le]
      ring

lemma starts_nonneg (f : PLFun) (hf : f.WF) : ∀ e ∈ f.pieces, 0 ≤ e.1 := by
  obtain ⟨hne, hhead, hsort, _⟩ := hf
  cases h : f.pieces with
  | nil => exact absurd h hne
  | cons e t =>
    rw [h] at hhead hsort
    simp at hhead
    intro y hy
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · rw [hhead]
    · have := (List.pairwise_cons.mp (by simpa using hsort)).1 y.1 (List.mem_map_of_mem hy)
      rw [hhead] at this; exact this.le

lemma eval_zero (f : PLFun) (hf : f.WF) : f.eval 0 = f.base := by
  unfold PLFun.eval
  simp only [lt_irrefl, if_false]
  rw [drop_eq_zero 0 _ hf.2.2.1 (starts_nonneg f hf)]; ring

lemma firstSlope_pos (f : PLFun) (hf : f.WF) : 0 < f.firstSlope := by
  unfold PLFun.firstSlope
  cases h : f.pieces with
  | nil => exact absurd h hf.1
  | cons e t =>
    simp only [List.headD_cons]
    exact hf.2.2.2 e (by rw [h]; simp)

lemma M_pos {n : ℕ} (hn : 1 ≤ n) (J : Instance n) (hJ : Standing J) (M : ℝ)
    (hM : IsThreshold J M) : 0 < M := by
  have a0 : Fin n := ⟨0, by omega⟩
  have h := hM a0 a0 a0
  rw [eval_zero _ (hJ a0 a0)] at h
  by_contra hle
  push_neg at hle
  rcases hle.lt_or_eq with hlt | heq
  · unfold PLFun.eval at h
    rw [if_pos hlt] at h
    have := firstSlope_pos _ (hJ a0 a0)
    nlinarith
  · subst heq
    rw [eval_zero _ (hJ a0 a0)] at h
    exact lt_irrefl _ h

lemma hat_sorted (M : ℝ) (f : PLFun) (hf : f.WF) :
    ((extendQL M f).pieces.map Prod.fst).Pairwise (· < ·) := by
  unfold extendQL
  simp only [List.map_append, List.map_cons, List.map_nil]
  rw [List.pairwise_append]
  refine ⟨?_, by simp, ?_⟩
  · exact hf.2.2.1.sublist ((List.filter_sublist).map _)
  · intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst hb
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp ha
    have := (List.mem_filter.mp hz).2
    simpa using this

lemma hat_WF (M : ℝ) (hM : 0 < M) (f : PLFun) (hf : f.WF) : (extendQL M f).WF := by
  refine ⟨?_, ?_, hat_sorted M f hf, ?_⟩
  · unfold extendQL; simp
  · obtain ⟨hne, hhead, _, _⟩ := hf
    unfold extendQL
    cases h : f.pieces with
    | nil => exact absurd h hne
    | cons e t =>
      rw [h] at hhead
      simp at hhead
      have hfe : (e :: t).filter (fun e => decide (e.1 < M)) =
          e :: t.filter (fun e => decide (e.1 < M)) :=
        List.filter_cons_of_pos (by simp [hhead, hM])
      show Option.map Prod.fst (((e :: t).filter (fun e : ℝ × ℝ => decide (e.1 < M))) ++
        [((M : ℝ), (1 : ℝ))]).head? = some (0 : ℝ)
      rw [hfe]
      simp [hhead]
  · intro e he
    unfold extendQL at he
    simp only [List.mem_append, List.mem_filter, List.mem_singleton] at he
    rcases he with ⟨he, _⟩ | rfl
    · exact hf.2.2.2 e he
    · norm_num

end FRFL4Aux

open FRFL4Aux in
theorem solution {n : ℕ} (hn : 1 ≤ n) (J : Instance n) (M : ℝ) (hJ : Standing J)
    (hM : IsThreshold J M) (T : ℕ) (π : ℕ → Equiv.Perm (Fin n)) (p : ℕ → Fin n → ℝ)
    (hrun : IsRun J M T π p) (i : ℕ) (hi : 1 ≤ i) (hiT : i + 1 ≤ T)
    (hdom : domL (hatInst M J) (p (i - 1)) = domL (hatInst M J) (p i) ∧
      domU (hatInst M J) (p (i - 1)) = domU (hatInst M J) (p i)) :
    weight (hatInst M J) (p i) (π i) < weight (hatInst M J) (p i) (π (i + 1)) := by
  classical
  set Ĵ := hatInst M J
  have hM0 : 0 < M := M_pos hn J hJ M hM
  have hĴ : Standing Ĵ := fun a r => hat_WF M hM0 (J.v a r) (hJ a r)
  obtain ⟨hpos, hmax1, _⟩ := hrun.2.2 i (by omega)
  obtain ⟨_, _, hLP⟩ := hrun.2.2 (i - 1) (by omega)
  rw [show i - 1 + 1 = i by omega] at hLP
  obtain ⟨⟨hL1, hU1, hEF, hnn⟩, hopt⟩ := hLP
  by_contra hcon
  push_neg at hcon
  -- `π i` is also a maximum-weight perfect matching of `F_w(p i)`
  have hmaxi : IsMaxWeightPM Ĵ (p i) (π i) := by
    refine ⟨fun a r' => hEF a r', ?_⟩
    intro τ hτ
    exact le_trans (hmax1.2 τ hτ) hcon
  obtain ⟨δ₀, hδ₀, hδ⟩ := lemma_2 Ĵ hĴ (π i) (π i) (p i) hEF hmaxi
  -- room-wise slack to the lower box constraint and to zero
  have hslack : ∀ r, ∃ d : ℝ, 0 < d ∧ d ≤ p i r ∧
      ∀ l : ℝ, domL Ĵ (p (i - 1)) r = (l : WithBot ℝ) → d ≤ p i r - l := by
    intro r
    rw [hdom.1]
    cases hL : domL Ĵ (p i) r with
    | bot => exact ⟨p i r, hpos r, le_rfl, fun l h => by simp at h⟩
    | coe l =>
      have hl : l < p i r := by
        unfold domL at hL
        have := Finset.mem_of_max hL
        exact (Finset.mem_filter.mp this).2
      refine ⟨min (p i r) (p i r - l), lt_min (hpos r) (by linarith), min_le_left _ _, ?_⟩
      intro l' hl'
      have : l' = l := by
        have := hl'.symm
        exact WithBot.coe_injective this
      subst this
      exact min_le_right _ _
  choose d hd0 hd1 hd2 using hslack
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  set δ := min δ₀ (Finset.univ.inf' hne d) with hδdef
  have hδpos : 0 < δ := lt_min hδ₀ ((Finset.lt_inf'_iff hne).mpr (fun r _ => hd0 r))
  have hδd : ∀ r, δ ≤ d r := fun r =>
    le_trans (min_le_right _ _) (Finset.inf'_le _ (Finset.mem_univ r))
  obtain ⟨q, hqEF, hq⟩ := hδ δ hδpos (min_le_left _ _)
  have hqfeas : LPFeasible Ĵ (domL Ĵ (p (i - 1))) (domU Ĵ (p (i - 1))) (π i) q := by
    refine ⟨?_, ?_, hqEF, ?_⟩
    · intro r
      cases hL : domL Ĵ (p (i - 1)) r with
      | bot => exact bot_le
      | coe l =>
        apply WithBot.coe_le_coe.mpr
        have := hd2 r l hL
        linarith [(hq r).1, hδd r]
    · intro r
      refine le_trans ?_ (hU1 r)
      exact WithTop.coe_le_coe.mpr (hq r).2.le
    · intro r
      linarith [(hq r).1, hδd r, hd1 r]
  have h1 := hopt q hqfeas
  have h2 : ∑ r, q r < ∑ r, p i r :=
    Finset.sum_lt_sum_of_nonempty hne (fun r _ => (hq r).2)
  linarith
