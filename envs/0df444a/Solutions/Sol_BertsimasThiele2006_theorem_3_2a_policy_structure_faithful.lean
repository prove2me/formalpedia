-- Prove2me | solution 1 for BertsimasThiele2006.theorem_3_2a_policy_structure_faithful
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T05:56:34.097486+00:00
-- url     : https://prove2.me/submissions/5f62bb49-b26d-48a4-9147-f2378085f282

import Mathlib
import Definitions.Def_RobustInventory_SingleStation_Deviation
import Definitions.Def_RobustInventory_SingleStation_Robust
import Theorems.Thm_RobustInventory_SingleStation_theorem_3_2

open Finset RobustInventory.SingleStation

namespace BT87b

lemma C_nonneg (M : Model) (u : ℝ) : 0 ≤ M.C u := by
  unfold Model.C; split_ifs with h
  · have := M.hK; have := M.hc; positivity
  · exact le_rfl

lemma C_ge (M : Model) {u : ℝ} (hu : 0 ≤ u) : M.c * u ≤ M.C u := by
  unfold Model.C; split_ifs with h
  · linarith [M.hK]
  · have : u = 0 := by linarith
    subst this; simp

lemma R_nonneg (M : Model) (x : ℝ) : 0 ≤ M.R x := by
  unfold Model.R
  rcases le_total 0 x with hx | hx
  · exact le_max_of_le_left (mul_nonneg M.hh hx)
  · have : 0 < M.p := lt_trans M.hc M.hpc
    exact le_max_of_le_right (by nlinarith)

lemma C_lsc (M : Model) : LowerSemicontinuous M.C := by
  intro x y hy
  by_cases hx : 0 < x
  · have hcont : ContinuousAt (fun u => M.K + M.c * u) x := by fun_prop
    have heq : M.C =ᶠ[nhds x] (fun u => M.K + M.c * u) := by
      filter_upwards [lt_mem_nhds hx] with u hu
      simp [Model.C, hu]
    have hCx : M.C x = M.K + M.c * x := by simp [Model.C, hx]
    rw [hCx] at hy
    filter_upwards [heq, hcont.eventually (lt_mem_nhds hy)] with u h1 h2
    rw [h1]; exact h2
  · have hCx : M.C x = 0 := by simp [Model.C, hx]
    rw [hCx] at hy
    exact Filter.Eventually.of_forall (fun u => lt_of_lt_of_le hy (C_nonneg M u))

noncomputable def ext {T : ℕ} (v : Fin T → ℝ) (k : ℕ) : ℝ := if h : k < T then v ⟨k, h⟩ else 0

lemma ext_cont {T : ℕ} (k : ℕ) : Continuous (fun v : Fin T → ℝ => ext v k) := by
  unfold ext
  by_cases h : k < T
  · simp only [h, dite_true]; exact continuous_apply _
  · simp only [h, dite_false]; exact continuous_const

lemma cost_congr (M : Model) (w u u' : ℕ → ℝ) (h : ∀ k < M.T, u k = u' k) :
    M.nominalCost w u = M.nominalCost w u' := by
  unfold Model.nominalCost Model.stock
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  rw [h k hk]
  congr 2
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rw [h i (by omega)]

lemma cost_ge (M : Model) (w u : ℕ → ℝ) (hu : ∀ k < M.T, 0 ≤ u k) (k : ℕ) (hk : k < M.T) :
    M.c * u k ≤ M.nominalCost w u := by
  unfold Model.nominalCost
  have hterm : ∀ j ∈ range M.T, 0 ≤ M.C (u j) + M.R (M.stock w u j) :=
    fun j _ => add_nonneg (C_nonneg M _) (R_nonneg M _)
  have h1 := Finset.single_le_sum hterm (Finset.mem_range.2 hk)
  have h2 := C_ge M (hu k hk)
  have h3 := R_nonneg M (M.stock w u k)
  linarith

lemma exists_nominal_opt (M : Model) (w : ℕ → ℝ) : ∃ u, M.IsNominalOptimal w u := by
  set B : ℝ := M.nominalCost w (fun _ => 0) / M.c + 1 with hB
  set F : (Fin M.T → ℝ) → ℝ := fun v => M.nominalCost w (ext v) with hF
  have hlsc : LowerSemicontinuous F := by
    simp only [hF, Model.nominalCost, Model.stock]
    apply lowerSemicontinuous_sum
    intro k _
    apply LowerSemicontinuous.add
    · exact (C_lsc M).comp (ext_cont k)
    · apply Continuous.lowerSemicontinuous
      unfold Model.R
      have : Continuous (fun v : Fin M.T → ℝ =>
          M.x0 + ∑ i ∈ range (k + 1), (ext v i - w i)) := by
        apply continuous_const.add
        apply continuous_finsetSum
        intro i _
        exact (ext_cont i).sub continuous_const
      fun_prop
  set S : Set (Fin M.T → ℝ) := Set.Icc (fun _ => 0) (fun _ => B) with hS
  have hB0 : 0 ≤ B := by
    have := cost_ge M w (fun _ => 0) (fun _ _ => le_rfl)
    have h0 : 0 ≤ M.nominalCost w (fun _ => 0) := by
      unfold Model.nominalCost
      exact Finset.sum_nonneg (fun j _ => add_nonneg (C_nonneg M _) (R_nonneg M _))
    have := M.hc
    positivity
  have hne : S.Nonempty := ⟨fun _ => 0, by simp [hS, hB0, Pi.le_def]⟩
  obtain ⟨v, hvS, hvmin⟩ := (hlsc.lowerSemicontinuousOn S).exists_isMinOn hne isCompact_Icc
  refine ⟨ext v, ?_, ?_⟩
  · intro k hk
    simp only [ext, hk, dite_true]
    exact hvS.1 ⟨k, hk⟩
  · intro u' hu'
    by_cases hbig : ∃ k < M.T, B < u' k
    · obtain ⟨k, hk, hkB⟩ := hbig
      have h1 := cost_ge M w u' hu' k hk
      have h0S : (fun _ => (0 : ℝ)) ∈ S := by simp [hS, hB0, Pi.le_def]
      have h2 : F v ≤ F (fun _ => 0) := hvmin h0S
      have h3 : F (fun _ => 0) = M.nominalCost w (fun _ => 0) := by
        simp only [hF]; apply cost_congr; intro j hj; simp [ext, hj]
      have hc := M.hc
      have h4 : M.nominalCost w (fun _ => 0) < M.c * u' k := by
        have : M.nominalCost w (fun _ => 0) / M.c < u' k := by linarith
        rwa [div_lt_iff₀ hc, mul_comm] at this
      show F v ≤ _
      linarith
    · push Not at hbig
      set v' : Fin M.T → ℝ := fun k => u' k with hv'
      have hv'S : v' ∈ S := ⟨fun k => hu' k k.2, fun k => hbig k k.2⟩
      have h1 := hvmin hv'S
      have h2 : F v' = M.nominalCost w u' := by
        simp only [hF]; apply cost_congr; intro j hj; simp [ext, hj, hv']
      show F v ≤ _
      rw [← h2]; exact h1

end BT87b

theorem solution (M : Model) :
    ∃ (s S u y q : ℕ → ℝ) (r : ℕ → ℕ → ℝ), M.IsRobustOptimal u y q r ∧
      (M.K = 0 → ∀ k < M.T, s k = S k) ∧
      ∀ k < M.T, s k ≤ S k ∧
        u k = if M.x0 + ∑ i ∈ range k, (u i - M.wmod i) < s k
          then S k - (M.x0 + ∑ i ∈ range k, (u i - M.wmod i)) else 0 := by
  obtain ⟨u, hu⟩ := BT87b.exists_nominal_opt M M.wmod
  obtain ⟨-, ha, -, -⟩ := theorem_3_2 M
  obtain ⟨y, q, r, hopt⟩ := (ha u).2 hu
  set xp : ℕ → ℝ := fun k => M.x0 + ∑ i ∈ range k, (u i - M.wmod i) with hxp
  refine ⟨fun k => xp k + u k, fun k => xp k + u k, u, y, q, r, hopt, fun _ _ _ => rfl, ?_⟩
  intro k hk
  refine ⟨le_rfl, ?_⟩
  have hu0 := hu.1 k hk
  show u k = if xp k < xp k + u k then xp k + u k - xp k else 0
  rcases hu0.lt_or_eq with h | h
  · rw [if_pos (by linarith)]; ring
  · rw [if_neg (by linarith)]; exact h.symm
