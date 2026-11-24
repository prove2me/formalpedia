-- Prove2me | solution 1 for GeneralAgentsWorldModels.theorem2_myopic_agents_no_world_model
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T20:49:17.951794+00:00
-- url     : https://prove2.me/submissions/23c4ad0a-3da8-4f4c-849b-1b8665507454

import Mathlib
import Definitions.Def_GeneralAgentsWorldModels_Basic

open Finset

set_option autoImplicit false

universe u v

namespace GeneralAgentsWorldModels

section
variable {S A : Type*} [Fintype S]
set_option linter.unusedSectionVars false

private lemma ex_sum_succ {β : Type*} [AddCommMonoid β] (n : ℕ) (F : List S → β) :
    ∑ ss : Fin (n+1) → S, F (List.ofFn ss) = ∑ s1 : S, ∑ ss : Fin n → S, F (s1 :: List.ofFn ss) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => S)).sum_comp, Fintype.sum_prod_type]
  simp [Fin.consEquiv, List.ofFn_succ]

private lemma ex_prefix_cons (π : Policy S A) : ∀ (ss : List S) (h : List (S × A)) (s : S),
    ∃ r, pathPrefix π h s ss = h ++ (s, π h s) :: r
  | [], h, s => ⟨[], rfl⟩
  | s' :: ss, h, s => by
    obtain ⟨r, hr⟩ := ex_prefix_cons π ss (h ++ [(s, π h s)]) s'
    exact ⟨(s', π (h ++ [(s, π h s)]) s') :: r, by rw [pathPrefix, hr]; simp⟩

private lemma ex_prefix_length (π : Policy S A) : ∀ (ss : List S) (h : List (S × A)) (s : S),
    (pathPrefix π h s ss).length = h.length + ss.length + 1
  | [], h, s => by simp [pathPrefix]
  | s' :: ss, h, s => by
    rw [pathPrefix, ex_prefix_length π ss]; simp; omega

private lemma ex_take_prefix (π : Policy S A) (ss : List S) (h : List (S × A)) (s : S) :
    (pathPrefix π h s ss).take (h.length + 1) = h ++ [(s, π h s)] := by
  obtain ⟨r, hr⟩ := ex_prefix_cons π ss h s
  rw [hr]; simp [List.take_append]

private lemma ex_pw_nonneg (M : CMP S A) (π : Policy S A) : ∀ (ss : List S) (h : List (S × A))
    (s : S), 0 ≤ pathWeight M π h s ss
  | [], h, s => by simp [pathWeight]
  | s' :: ss, h, s => by
    rw [pathWeight]; exact mul_nonneg (M.nonneg _ _ _) (ex_pw_nonneg M π ss _ _)

private lemma ex_sum_one (M : CMP S A) (π : Policy S A) : ∀ (k : ℕ) (h : List (S × A)) (s : S),
    ∑ ss : Fin k → S, pathWeight M π h s (List.ofFn ss) = 1
  | 0, h, s => by simp [pathWeight]
  | k+1, h, s => by
    rw [ex_sum_succ]
    simp only [pathWeight, ← Finset.mul_sum, ex_sum_one M π k, mul_one]
    exact M.sum_one s (π h s)

private lemma ex_split (M : CMP S A) (π : Policy S A) (f : List (S × A) → ℝ) (k : ℕ) :
    ∀ (T : ℕ) (h : List (S × A)) (s : S),
    ∑ ss : Fin (k + T) → S, pathWeight M π h s (List.ofFn ss) *
        f ((pathPrefix π h s (List.ofFn ss)).take (h.length + T + 1)) =
      ∑ ss : Fin T → S, pathWeight M π h s (List.ofFn ss) * f (pathPrefix π h s (List.ofFn ss))
  | 0, h, s => by
    simp only [Nat.add_zero, ex_take_prefix]
    rw [← Finset.sum_mul, ex_sum_one]
    simp [pathWeight, pathPrefix]
  | T+1, h, s => by
    have e : h.length + (T + 1) + 1 = (h ++ [(s, π h s)]).length + T + 1 := by simp; omega
    show ∑ ss : Fin (k + T + 1) → S, _ = _
    rw [ex_sum_succ (k + T) (fun L => pathWeight M π h s L *
      f ((pathPrefix π h s L).take (h.length + (T + 1) + 1))),
      ex_sum_succ T (fun L => pathWeight M π h s L * f (pathPrefix π h s L)), e]
    simp only [pathWeight, pathPrefix, mul_assoc, ← Finset.mul_sum]
    refine Finset.sum_congr rfl fun s1 _ => ?_
    rw [ex_split M π f k T]

private lemma ex_dec_take {ψ : CompGoal S A} {P : List (S × A)} (n : ℕ)
    (hd : Decides ψ (P.take n)) : Decides ψ P := by
  intro τ hτ
  apply hd τ
  intro i hi
  rw [List.getElem_take]
  exact hτ i (by simp at hi; omega)

open Classical in
private lemma ex_upTo_mono (M : CMP S A) (ψ : CompGoal S A) (π : Policy S A) (s₀ : S)
    (k T : ℕ) : succProbUpTo M ψ π s₀ T ≤ succProbUpTo M ψ π s₀ (k + T) := by
  unfold succProbUpTo
  rw [← ex_split M π (fun L => if Decides ψ L then 1 else 0) k T [] s₀]
  apply Finset.sum_le_sum
  intro ss _
  apply mul_le_mul_of_nonneg_left _ (ex_pw_nonneg _ _ _ _ _)
  by_cases h1 : Decides ψ ((pathPrefix π [] s₀ (List.ofFn ss)).take
      (([] : List (S × A)).length + T + 1))
  · rw [if_pos h1, if_pos (ex_dec_take _ h1)]
  · rw [if_neg h1]; split_ifs <;> norm_num

private lemma ex_upTo_le_one (M : CMP S A) (ψ : CompGoal S A) (π : Policy S A) (s₀ : S)
    (T : ℕ) : succProbUpTo M ψ π s₀ T ≤ 1 := by
  unfold succProbUpTo
  refine le_trans (Finset.sum_le_sum fun ss _ => ?_) (ex_sum_one M π T [] s₀).le
  have := ex_pw_nonneg M π (List.ofFn ss) [] s₀
  split_ifs <;> nlinarith

private lemma ex_upTo_nonneg (M : CMP S A) (ψ : CompGoal S A) (π : Policy S A) (s₀ : S)
    (T : ℕ) : 0 ≤ succProbUpTo M ψ π s₀ T := by
  unfold succProbUpTo
  apply Finset.sum_nonneg
  intro ss _
  have := ex_pw_nonneg M π (List.ofFn ss) [] s₀
  split_ifs <;> nlinarith

private lemma ex_le_succProb (M : CMP S A) (ψ : CompGoal S A) (π : Policy S A) (s₀ : S)
    (T : ℕ) : succProbUpTo M ψ π s₀ T ≤ succProb M ψ π s₀ :=
  le_ciSup ⟨1, by rintro _ ⟨T, rfl⟩; exact ex_upTo_le_one M ψ π s₀ T⟩ T

private lemma ex_succProb_le_one (M : CMP S A) (ψ : CompGoal S A) (π : Policy S A) (s₀ : S) :
    succProb M ψ π s₀ ≤ 1 :=
  ciSup_le fun T => ex_upTo_le_one M ψ π s₀ T

private lemma ex_le_optProb (M : CMP S A) (ψ : CompGoal S A) (π : Policy S A) (s₀ : S) :
    succProb M ψ π s₀ ≤ optProb M ψ s₀ :=
  le_ciSup (f := fun π => succProb M ψ π s₀)
    ⟨1, by rintro _ ⟨π, rfl⟩; exact ex_succProb_le_one M ψ π s₀⟩ π


end

section
variable {S A : Type*} [Fintype S]
set_option linter.unusedSectionVars false

/-- Union of the goal sets of a composite goal. -/
private def ex_G (ψ : CompGoal S A) : Set (S × A) := {x | ∃ φ ∈ ψ, ∃ sg ∈ φ, x ∈ sg.g}

open Classical in
private noncomputable def ex_H (ψ : CompGoal S A) (s1 : S) : ℝ := if ∃ b, (s1, b) ∈ ex_G ψ then 1 else 0

private lemma ex_myopic_seq (sg : SubGoal S A) (h : sg.op = opNext) (τ : ℕ → S × A) :
    seqSat τ [sg] 0 ↔ τ 1 ∈ sg.g := by
  rw [seqSat, if_neg (by rw [h]; decide), if_pos h]
  simp [seqSat]

private lemma ex_myopic_sat {ψ : CompGoal S A} (hψ : ψ ∈ PsiMyopic) (τ : ℕ → S × A) :
    compSat ψ τ ↔ τ 1 ∈ ex_G ψ := by
  obtain ⟨⟨_, hlen⟩, hop⟩ := hψ
  have key : ∀ φ ∈ ψ, ∃ sg, φ = [sg] ∧ sg.op = opNext := by
    intro φ hφ
    obtain ⟨hne, hl⟩ := hlen φ hφ
    match φ, hne, hl with
    | [sg], _, _ => exact ⟨sg, rfl, hop _ hφ sg (by simp)⟩
  constructor
  · rintro ⟨φ, hφ, hs⟩
    obtain ⟨sg, rfl, hsg⟩ := key φ hφ
    exact ⟨[sg], hφ, sg, by simp, (ex_myopic_seq sg hsg τ).1 hs⟩
  · rintro ⟨φ, hφ, sg, hsg, hx⟩
    obtain ⟨sg', rfl, hsg'⟩ := key φ hφ
    simp at hsg; subst hsg
    exact ⟨[sg], hφ, (ex_myopic_seq sg hsg' τ).2 hx⟩

private lemma ex_myopic_dec {ψ : CompGoal S A} (hψ : ψ ∈ PsiMyopic) (P : List (S × A))
    (hP : 2 ≤ P.length) : Decides ψ P ↔ P[1] ∈ ex_G ψ := by
  constructor
  · intro hd
    let τ : ℕ → S × A := fun i => if h : i < P.length then P[i] else P[0]
    have := (ex_myopic_sat hψ τ).1 (hd τ fun i hi => by simp [τ, hi])
    simpa [τ, show 1 < P.length by omega] using this
  · intro hm τ hτ
    rw [ex_myopic_sat hψ, hτ 1 (by omega)]
    exact hm

open Classical in
private lemma ex_upTo_one (M : CMP S A) (ψ : CompGoal S A) (π : Policy S A) (s₀ : S) :
    succProbUpTo M ψ π s₀ 1 = ∑ s1 : S, M.P s₀ (π [] s₀) s1 *
      (if Decides ψ [(s₀, π [] s₀), (s1, π [(s₀, π [] s₀)] s1)] then 1 else 0) := by
  unfold succProbUpTo
  rw [ex_sum_succ 0 (fun L => pathWeight M π [] s₀ L *
    if Decides ψ (pathPrefix π [] s₀ L) then 1 else 0)]
  simp [pathWeight, pathPrefix]

open Classical in
private lemma ex_myopic_succ (M : CMP S A) {ψ : CompGoal S A} (hψ : ψ ∈ PsiMyopic)
    (π : Policy S A) (s₀ : S) :
    succProb M ψ π s₀ = ∑ s1 : S, M.P s₀ (π [] s₀) s1 *
      (if (s1, π [(s₀, π [] s₀)] s1) ∈ ex_G ψ then 1 else 0) := by
  have hk : ∀ k, succProbUpTo M ψ π s₀ (k + 1) = succProbUpTo M ψ π s₀ 1 := by
    intro k
    unfold succProbUpTo
    rw [← ex_split M π (fun L => if Decides ψ L then 1 else 0) k 1 [] s₀]
    refine Finset.sum_congr rfl fun ss _ => ?_
    have hl := ex_prefix_length π (List.ofFn ss) [] s₀
    simp only [List.length_ofFn, List.length_nil] at hl
    congr 1
    apply if_congr _ rfl rfl
    rw [ex_myopic_dec hψ (List.take _ _) (by simp only [List.length_take, hl, List.length_nil]; omega),
      ex_myopic_dec hψ (pathPrefix π [] s₀ (List.ofFn ss)) (by omega)]
    simp
  have h1 : succProb M ψ π s₀ = succProbUpTo M ψ π s₀ 1 := by
    apply le_antisymm
    · apply ciSup_le
      intro T
      cases T with
      | zero => exact ex_upTo_mono M ψ π s₀ 1 0
      | succ k => rw [hk]
    · exact ex_le_succProb M ψ π s₀ 1
  rw [h1, ex_upTo_one]
  refine Finset.sum_congr rfl fun s1 _ => ?_
  congr 1
  apply if_congr _ rfl rfl
  rw [ex_myopic_dec hψ _ (by simp)]
  simp

private lemma ex_opt (M : CMP S A) {ψ : CompGoal S A} (hψ : ψ ∈ PsiMyopic) (s₀ : S)
    (p : Policy S A)
    (h1 : ∀ a, ∑ s1, M.P s₀ a s1 * ex_H ψ s1 ≤ ∑ s1, M.P s₀ (p [] s₀) s1 * ex_H ψ s1)
    (h2 : ∀ s1, (∃ b, (s1, b) ∈ ex_G ψ) → (s1, p [(s₀, p [] s₀)] s1) ∈ ex_G ψ) :
    succProb M ψ p s₀ = optProb M ψ s₀ := by
  classical
  have hle : ∀ π : Policy S A, succProb M ψ π s₀ ≤ ∑ s1, M.P s₀ (π [] s₀) s1 * ex_H ψ s1 := by
    intro π
    rw [ex_myopic_succ M hψ]
    refine Finset.sum_le_sum fun s1 _ => mul_le_mul_of_nonneg_left ?_ (M.nonneg _ _ _)
    unfold ex_H
    by_cases ha : (s1, π [(s₀, π [] s₀)] s1) ∈ ex_G ψ
    · rw [if_pos ha, if_pos ⟨_, ha⟩]
    · rw [if_neg ha]; split_ifs <;> norm_num
  have heq : succProb M ψ p s₀ = ∑ s1, M.P s₀ (p [] s₀) s1 * ex_H ψ s1 := by
    rw [ex_myopic_succ M hψ]
    refine Finset.sum_congr rfl fun s1 _ => ?_
    unfold ex_H
    by_cases hb : ∃ b, (s1, b) ∈ ex_G ψ
    · rw [if_pos (h2 s1 hb), if_pos hb]
    · rw [if_neg hb, if_neg fun h => hb ⟨_, h⟩]
  apply le_antisymm (ex_le_optProb M ψ p s₀)
  have : Nonempty (Policy S A) := ⟨p⟩
  apply ciSup_le
  intro π
  rw [heq]
  exact (hle π).trans (h1 _)

variable [Fintype A]

private noncomputable def ex_first [Nonempty A] (M : CMP S A) (ψ : CompGoal S A) (s₀ : S) : A :=
  Classical.choose (Finset.exists_max_image (univ : Finset A)
    (fun a => ∑ s1, M.P s₀ a s1 * ex_H ψ s1) univ_nonempty)

private lemma ex_first_spec [Nonempty A] (M : CMP S A) (ψ : CompGoal S A) (s₀ : S) (a : A) :
    ∑ s1, M.P s₀ a s1 * ex_H ψ s1 ≤ ∑ s1, M.P s₀ (ex_first M ψ s₀) s1 * ex_H ψ s1 :=
  (Classical.choose_spec (Finset.exists_max_image (univ : Finset A)
    (fun a => ∑ s1, M.P s₀ a s1 * ex_H ψ s1) univ_nonempty)).2 a (mem_univ a)

open Classical in
private noncomputable def ex_second [Nonempty A] (ψ : CompGoal S A) (s : S) : A :=
  if hb : ∃ b, (s, b) ∈ ex_G ψ then hb.choose else Classical.arbitrary A

private lemma ex_second_spec [Nonempty A] (ψ : CompGoal S A) (s : S)
    (hb : ∃ b, (s, b) ∈ ex_G ψ) : (s, ex_second ψ s) ∈ ex_G ψ := by
  unfold ex_second; rw [dif_pos hb]; exact hb.choose_spec

private noncomputable def ex_pstar [Nonempty A] (M : CMP S A) : GCPolicy S A :=
  fun ψ h s => match h with
    | [] => ex_first M ψ s
    | _ :: _ => ex_second ψ s

private noncomputable def ex_row [DecidableEq S] (s s' : S) (q : ℝ) (x y : S) : ℝ :=
  if x = s then (if y = s' then q else (1 - q) / ((Fintype.card S : ℝ) - 1))
  else 1 / (Fintype.card S : ℝ)

private lemma ex_row_pos [DecidableEq S] (hS : 2 ≤ Fintype.card S) (s s' : S) (q : ℝ)
    (hq0 : 0 < q) (hq1 : q < 1) (x y : S) : 0 < ex_row s s' q x y := by
  have hc : (2 : ℝ) ≤ Fintype.card S := by exact_mod_cast hS
  unfold ex_row
  split_ifs
  · exact hq0
  · apply div_pos <;> linarith
  · apply div_pos <;> linarith

private lemma ex_row_sum [DecidableEq S] (hS : 2 ≤ Fintype.card S) (s s' : S) (q : ℝ) (x : S) :
    ∑ y, ex_row s s' q x y = 1 := by
  have hc : (2 : ℝ) ≤ Fintype.card S := by exact_mod_cast hS
  have hc1 : ((Fintype.card S : ℝ) - 1) ≠ 0 := by linarith
  have hc0 : (Fintype.card S : ℝ) ≠ 0 := by linarith
  unfold ex_row
  split_ifs with hx
  · set c := (1 - q) / ((Fintype.card S : ℝ) - 1) with hcdef
    rw [show (fun y => if y = s' then q else c) = fun y => (if y = s' then q - c else 0) + c from
      funext fun y => by split_ifs <;> ring]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq' univ s', if_pos (mem_univ _), sum_const,
      card_univ, nsmul_eq_mul, hcdef]
    field_simp; ring
  · rw [sum_const, card_univ, nsmul_eq_mul]; field_simp

private noncomputable def ex_Mq [DecidableEq S] (hS : 2 ≤ Fintype.card S) (s s' : S) (q : ℝ)
    (hq0 : 0 < q) (hq1 : q < 1) : CMP S A where
  P x _ y := ex_row s s' q x y
  nonneg x _ y := (ex_row_pos hS s s' q hq0 hq1 x y).le
  sum_one x _ := ex_row_sum hS s s' q x

end
end GeneralAgentsWorldModels

open GeneralAgentsWorldModels in
theorem solution {S : Type u} {A : Type v} [Fintype S] [DecidableEq S]
    [Fintype A] (hS : 2 ≤ Fintype.card S) (M : CMP S A) (hM : SatisfiesAssumption1 M) :
    ∃ πstar : GCPolicy S A, IsOptimalAgent M PsiMyopic πstar ∧
      ∀ (s : S) (a : A) (s' : S) (q : ℝ), 0 < q → q < 1 →
        ∃ M' : CMP S A, SatisfiesAssumption1 M' ∧ M'.P s a s' = q ∧
          IsOptimalAgent M' PsiMyopic πstar := by
  have hA : Nonempty A := Fintype.card_pos_iff.1 (by have := hM.2; omega)
  refine ⟨ex_pstar M, fun ψ hψ s₀ => ?_, fun s a s' q hq0 hq1 => ?_⟩
  · exact ex_opt M hψ s₀ _ (fun a => ex_first_spec M ψ s₀ a) (fun s1 hb => ex_second_spec ψ s1 hb)
  · refine ⟨ex_Mq hS s s' q hq0 hq1, ⟨fun x y _ => Relation.TransGen.single
      ⟨Classical.arbitrary A, ex_row_pos hS s s' q hq0 hq1 x y⟩, hM.2⟩, ?_, fun ψ hψ s₀ => ?_⟩
    · simp [ex_Mq, ex_row]
    · exact ex_opt _ hψ s₀ _ (fun a => le_refl _) (fun s1 hb => ex_second_spec ψ s1 hb)
