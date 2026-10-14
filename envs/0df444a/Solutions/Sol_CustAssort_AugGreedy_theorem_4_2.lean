-- Prove2me | solution 1 for CustAssort.AugGreedy.theorem_4_2
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T11:56:08.219434+00:00
-- url     : https://prove2.me/submissions/8b8c438f-ffb0-4a52-bc10-6a3a41d94016

import Mathlib
import Definitions.Def_CustAssort_AugGreedy_Setting

namespace RRAux_CustAssort_AugGreedy_theorem_4_2

open CustAssort.AugGreedy

/-! ### Greedy for monotone submodular functions -/

section Greedy

variable {α : Type*} [DecidableEq α]

lemma reach_sub (g : Finset α → ℝ) (P : Finset α) (k : ℕ) {Δ : Finset α}
    (h : GreedyReach g P k Δ) : Δ ⊆ P ∧ Δ.card ≤ k := by
  induction h with
  | nil => simp
  | @step Δ i _ hc hi _ ih =>
    refine ⟨Finset.insert_subset (Finset.mem_sdiff.mp hi).1 ih.1, ?_⟩
    rw [Finset.card_insert_of_notMem (Finset.mem_sdiff.mp hi).2]
    omega

lemma union_bound (g : Finset α → ℝ) (P : Finset α) (hsub : SubmodularOn g P)
    (Δ : Finset α) (hΔ : Δ ⊆ P) (T : Finset α) (hT : T ⊆ P) :
    g (Δ ∪ T) ≤ g Δ + ∑ q ∈ T, (g (insert q Δ) - g Δ) := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert x T hx ih =>
    have hT' : T ⊆ P := fun y hy => hT (Finset.mem_insert_of_mem hy)
    have hxP : x ∈ P := hT (Finset.mem_insert_self x T)
    have ih' := ih hT'
    rw [Finset.sum_insert hx, Finset.union_insert]
    by_cases hxB : x ∈ Δ ∪ T
    · have hxΔ : x ∈ Δ := by
        rcases Finset.mem_union.mp hxB with h | h
        · exact h
        · exact absurd h hx
      rw [Finset.insert_eq_of_mem hxB, Finset.insert_eq_of_mem hxΔ]
      linarith
    · have hB : Δ ∪ T ⊆ P := Finset.union_subset hΔ hT'
      have := hsub Δ (Δ ∪ T) Finset.subset_union_left hB x (Finset.mem_sdiff.mpr ⟨hxP, hxB⟩)
      linarith

lemma step_ineq (D E c : ℝ) (hc : 1 ≤ c) (h : D ≤ c * E) (gQ t : ℝ)
    (ih : D ≤ t * gQ) : D - E ≤ (1 - 1 / c) * (t * gQ) := by
  have hc0 : 0 < c := by linarith
  have h1 : D / c ≤ E := by rw [div_le_iff₀ hc0]; linarith
  have h2 : 0 ≤ 1 - 1 / c := by
    rw [sub_nonneg, div_le_one hc0]; exact hc
  have h3 : (1 - 1 / c) * D ≤ (1 - 1 / c) * (t * gQ) := mul_le_mul_of_nonneg_left ih h2
  have h4 : (1 - 1 / c) * D = D - D / c := by ring
  linarith

lemma reach_bound (g : Finset α → ℝ) (P Q : Finset α) (k : ℕ) (hk : 1 ≤ k)
    (hQP : Q ⊆ P) (hQk : Q.card ≤ k)
    (hmono : ∀ A B, A ⊆ B → B ⊆ P → g A ≤ g B) (hsub : SubmodularOn g P) (h0 : g ∅ = 0)
    {Δ : Finset α} (h : GreedyReach g P k Δ) :
    g Q - g Δ ≤ (1 - 1 / (k : ℝ)) ^ Δ.card * g Q := by
  induction h with
  | nil => simp [h0]
  | @step Δ i hreach hc hi hbest ih =>
    have hΔP := (reach_sub g P k hreach).1
    have hiP := (Finset.mem_sdiff.mp hi).1
    have hiΔ := (Finset.mem_sdiff.mp hi).2
    have hΔ'P : insert i Δ ⊆ P := Finset.insert_subset hiP hΔP
    have hEnn : 0 ≤ g (insert i Δ) - g Δ := by
      have := hmono Δ (insert i Δ) (Finset.subset_insert i Δ) hΔ'P
      linarith
    have hmar : ∀ q ∈ Q, g (insert q Δ) - g Δ ≤ g (insert i Δ) - g Δ := by
      intro q hq
      by_cases hqΔ : q ∈ Δ
      · rw [Finset.insert_eq_of_mem hqΔ, sub_self]; exact hEnn
      · have := hbest q (Finset.mem_sdiff.mpr ⟨hQP hq, hqΔ⟩)
        linarith
    have hU := union_bound g P hsub Δ hΔP Q hQP
    have hsum := Finset.sum_le_card_nsmul Q _ _ hmar
    rw [nsmul_eq_mul] at hsum
    have hcardk : (Q.card : ℝ) * (g (insert i Δ) - g Δ) ≤ (k : ℝ) * (g (insert i Δ) - g Δ) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hQk) hEnn
    have hQU : g Q ≤ g (Δ ∪ Q) :=
      hmono Q (Δ ∪ Q) Finset.subset_union_right (Finset.union_subset hΔP hQP)
    have hD : g Q - g Δ ≤ (k : ℝ) * (g (insert i Δ) - g Δ) := by linarith
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have := step_ineq (g Q - g Δ) (g (insert i Δ) - g Δ) k hk1 hD (g Q) _ ih
    rw [Finset.card_insert_of_notMem hiΔ, pow_succ]
    have e : (1 - 1 / (k : ℝ)) ^ Δ.card * (1 - 1 / (k : ℝ)) * g Q =
        (1 - 1 / (k : ℝ)) * ((1 - 1 / (k : ℝ)) ^ Δ.card * g Q) := by ring
    rw [e]
    linarith

lemma greedy_bound (g : Finset α → ℝ) (P Q : Finset α) (k : ℕ)
    (hQP : Q ⊆ P) (hQk : Q.card ≤ k)
    (hmono : ∀ A B, A ⊆ B → B ⊆ P → g A ≤ g B) (hsub : SubmodularOn g P) (h0 : g ∅ = 0)
    (Δ : Finset α) (hΔ : IsGreedyOutput g P k Δ) :
    (1 - Real.exp (-1)) * g Q ≤ g Δ := by
  obtain ⟨hreach, hstop⟩ := hΔ
  have hΔP := (reach_sub g P k hreach).1
  have hgQ : 0 ≤ g Q := by
    have := hmono ∅ Q (Finset.empty_subset Q) hQP
    linarith
  have hgΔ : 0 ≤ g Δ := by
    have := hmono ∅ Δ (Finset.empty_subset Δ) hΔP
    linarith
  have hexp0 : 0 ≤ Real.exp (-1) := (Real.exp_pos _).le
  have hexp1 : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    have hQe : Q = ∅ := Finset.card_eq_zero.mp (by omega)
    subst hQe
    rw [h0]; simpa using hgΔ
  by_cases hc : Δ.card < k
  · have hPΔ : P ⊆ Δ := by
      by_contra hne
      apply hstop
      refine ⟨hc, ?_⟩
      rw [Finset.nonempty_iff_ne_empty]
      intro he
      exact hne (Finset.sdiff_eq_empty_iff_subset.mp he)
    have := hmono Q Δ (hQP.trans hPΔ) hΔP
    nlinarith
  · rw [not_lt] at hc
    have hb := reach_bound g P Q k hkpos hQP hQk hmono hsub h0 hreach
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hkpos
    have hx0 : 0 ≤ 1 - 1 / (k : ℝ) := by
      rw [sub_nonneg, div_le_one (by linarith)]; exact hk1
    have hx1 : 1 - 1 / (k : ℝ) ≤ 1 := by
      have : 0 ≤ 1 / (k : ℝ) := by positivity
      linarith
    have hp1 : (1 - 1 / (k : ℝ)) ^ Δ.card ≤ (1 - 1 / (k : ℝ)) ^ k :=
      pow_le_pow_of_le_one hx0 hx1 hc
    have hp2 : (1 - 1 / (k : ℝ)) ^ k ≤ Real.exp (-1) :=
      Real.one_sub_div_pow_le_exp_neg hk1
    have h3 : (1 - 1 / (k : ℝ)) ^ Δ.card * g Q ≤ Real.exp (-1) * g Q :=
      mul_le_mul_of_nonneg_right (hp1.trans hp2) hgQ
    nlinarith

end Greedy

/-! ### Capped MNL revenue -/

/-- `τ - min(R(S), τ)` written through the additive quantities `W` and `V`. -/
noncomputable def phi {n m : ℕ} (v : Fin n → Fin m → ℝ) (r : Fin n → ℝ) (τ : ℝ) (j : Fin m)
    (S : Finset (Fin n)) : ℝ :=
  max (τ - ∑ i ∈ S, (r i - τ) * v i j) 0 / (1 + ∑ i ∈ S, v i j)

lemma num_anti (τ W W' V V' : ℝ) (hW : W ≤ W') (hV0 : 0 ≤ V) (hV : V ≤ V') :
    max (τ - W') 0 / (1 + V') ≤ max (τ - W) 0 / (1 + V) := by
  apply div_le_div₀ (le_max_right _ _) _ (by linarith) (by linarith)
  exact max_le_max (by linarith) le_rfl

lemma convex_u (τ W W' w : ℝ) (hW : W ≤ W') (hw : 0 ≤ w) :
    max (τ - (W + w)) 0 - max (τ - (W' + w)) 0 ≤ max (τ - W) 0 - max (τ - W') 0 := by
  rcases le_total (τ - (W + w)) 0 with h1 | h1 <;>
  rcases le_total (τ - (W' + w)) 0 with h2 | h2 <;>
  rcases le_total (τ - W) 0 with h3 | h3 <;>
  rcases le_total (τ - W') 0 with h4 | h4 <;>
  simp only [max_eq_left, max_eq_right, h1, h2, h3, h4] <;> linarith

lemma step_V (p q a a' ν : ℝ) (hq : 0 ≤ q) (hpq : q ≤ p) (ha : 1 ≤ a) (haa : a ≤ a')
    (hν : 0 ≤ ν) : p / a' - q / (a' + ν) ≤ p / a - q / (a + ν) := by
  have ha0 : 0 < a := by linarith
  have ha0' : 0 < a' := by linarith
  have key : p / a - q / (a + ν) - (p / a' - q / (a' + ν)) =
      (a' - a) * (p * ((a + ν) * (a' + ν)) - q * (a * a')) /
        (a * a' * ((a + ν) * (a' + ν))) := by
    field_simp
    ring
  have hprod : q * (a * a') ≤ p * ((a + ν) * (a' + ν)) := by
    apply mul_le_mul hpq _ (by positivity) (by linarith)
    nlinarith
  have : 0 ≤ (a' - a) * (p * ((a + ν) * (a' + ν)) - q * (a * a')) /
      (a * a' * ((a + ν) * (a' + ν))) := by
    apply div_nonneg
    · exact mul_nonneg (by linarith) (by linarith)
    · positivity
  linarith

lemma super_num (τ W W' V V' w ν : ℝ) (hW : W ≤ W') (hV0 : 0 ≤ V) (hV : V ≤ V')
    (hw : 0 ≤ w) (hν : 0 ≤ ν) :
    max (τ - W') 0 / (1 + V') - max (τ - (W' + w)) 0 / (1 + V' + ν) ≤
      max (τ - W) 0 / (1 + V) - max (τ - (W + w)) 0 / (1 + V + ν) := by
  have hc := convex_u τ W W' w hW hw
  have hd1 : 0 ≤ max (τ - W) 0 - max (τ - W') 0 := by
    have : max (τ - W') 0 ≤ max (τ - W) 0 := max_le_max (by linarith) le_rfl
    linarith
  -- step in W
  have s1 : (max (τ - (W + w)) 0 - max (τ - (W' + w)) 0) / (1 + V + ν) ≤
      (max (τ - W) 0 - max (τ - W') 0) / (1 + V) := by
    calc (max (τ - (W + w)) 0 - max (τ - (W' + w)) 0) / (1 + V + ν)
        ≤ (max (τ - W) 0 - max (τ - W') 0) / (1 + V + ν) :=
          div_le_div_of_nonneg_right hc (by linarith)
      _ ≤ (max (τ - W) 0 - max (τ - W') 0) / (1 + V) :=
          div_le_div_of_nonneg_left hd1 (by linarith) (by linarith)
  -- step in V
  have s2 := step_V (max (τ - W') 0) (max (τ - (W' + w)) 0) (1 + V) (1 + V') ν
    (le_max_right _ _) (max_le_max (by linarith) le_rfl) (by linarith) (by linarith) hν
  rw [sub_div, sub_div] at s1
  have e1 : 1 + V' + ν = (1 + V') + ν := rfl
  linarith

lemma min_identity (τ W V : ℝ) (hV : 0 ≤ V) :
    min ((τ * V + W) / (V + 1)) τ = τ - max (τ - W) 0 / (1 + V) := by
  have hV1 : 0 < V + 1 := by linarith
  rcases le_total W τ with h | h
  · rw [max_eq_left (by linarith)]
    have hle : (τ * V + W) / (V + 1) ≤ τ := by
      rw [div_le_iff₀ hV1]; nlinarith
    rw [min_eq_left hle]
    field_simp
    ring
  · rw [max_eq_right (by linarith)]
    have hle : τ ≤ (τ * V + W) / (V + 1) := by
      rw [le_div_iff₀ hV1]; nlinarith
    rw [min_eq_right hle]
    simp

lemma rev_min_eq {n m : ℕ} (v : Fin n → Fin m → ℝ) (r : Fin n → ℝ) (hv : ∀ i j, 0 ≤ v i j)
    (τ : ℝ) (j : Fin m) (S : Finset (Fin n)) :
    min (rev v r j S) τ = τ - phi v r τ j S := by
  unfold rev ChoiceCDLP.MNL.mnlObjective phi
  have hV : 0 ≤ ∑ i ∈ S, v i j := Finset.sum_nonneg (fun i _ => hv i j)
  have hN : ∑ i ∈ S, r i * v i j = τ * ∑ i ∈ S, v i j + ∑ i ∈ S, (r i - τ) * v i j := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _; ring
  rw [hN]
  exact min_identity τ _ _ hV

lemma phi_anti {n m : ℕ} (v : Fin n → Fin m → ℝ) (r : Fin n → ℝ) (hv : ∀ i j, 0 ≤ v i j)
    (τ : ℝ) (j : Fin m) (A B : Finset (Fin n)) (hAB : A ⊆ B) (hB : ∀ i ∈ B, τ ≤ r i) :
    phi v r τ j B ≤ phi v r τ j A := by
  unfold phi
  apply num_anti
  · exact Finset.sum_le_sum_of_subset_of_nonneg hAB
      (fun i hi _ => mul_nonneg (by linarith [hB i hi]) (hv i j))
  · exact Finset.sum_nonneg (fun i _ => hv i j)
  · exact Finset.sum_le_sum_of_subset_of_nonneg hAB (fun i _ _ => hv i j)

lemma phi_super {n m : ℕ} (v : Fin n → Fin m → ℝ) (r : Fin n → ℝ) (hv : ∀ i j, 0 ≤ v i j)
    (τ : ℝ) (j : Fin m) (A B : Finset (Fin n)) (hAB : A ⊆ B) (x : Fin n) (hxB : x ∉ B)
    (hB : ∀ i ∈ insert x B, τ ≤ r i) :
    phi v r τ j B - phi v r τ j (insert x B) ≤ phi v r τ j A - phi v r τ j (insert x A) := by
  have hxA : x ∉ A := fun h => hxB (hAB h)
  unfold phi
  rw [Finset.sum_insert hxB, Finset.sum_insert hxB, Finset.sum_insert hxA,
    Finset.sum_insert hxA]
  have hBr : ∀ i ∈ B, τ ≤ r i := fun i hi => hB i (Finset.mem_insert_of_mem hi)
  have hx : τ ≤ r x := hB x (Finset.mem_insert_self x B)
  have hW : ∑ i ∈ A, (r i - τ) * v i j ≤ ∑ i ∈ B, (r i - τ) * v i j :=
    Finset.sum_le_sum_of_subset_of_nonneg hAB
      (fun i hi _ => mul_nonneg (by linarith [hBr i hi]) (hv i j))
  have hV0 : 0 ≤ ∑ i ∈ A, v i j := Finset.sum_nonneg (fun i _ => hv i j)
  have hV : ∑ i ∈ A, v i j ≤ ∑ i ∈ B, v i j :=
    Finset.sum_le_sum_of_subset_of_nonneg hAB (fun i _ _ => hv i j)
  have := super_num τ _ _ _ _ ((r x - τ) * v x j) (v x j) hW hV0 hV
    (mul_nonneg (by linarith) (hv x j)) (hv x j)
  have e1 : ∀ W : ℝ, τ - ((r x - τ) * v x j + W) = τ - (W + (r x - τ) * v x j) := by
    intro W; ring
  have e2 : ∀ V : ℝ, 1 + (v x j + V) = 1 + V + v x j := by intro V; ring
  rw [e1, e1, e2, e2]
  exact this

lemma fj_min_eq {n m : ℕ} (v : Fin n → Fin m → ℝ) (r : Fin n → ℝ) (hv : ∀ i j, 0 ≤ v i j)
    (τ : ℝ) (j : Fin m) (S : Finset (Fin n)) (hS : ∀ i ∈ S, τ ≤ r i) :
    min (fj v r j S) τ = τ - phi v r τ j S := by
  apply le_antisymm
  · obtain ⟨T, hT, hTeq⟩ :=
      Finset.exists_mem_eq_sup' (Finset.powerset_nonempty S) (rev v r j)
    unfold fj
    rw [hTeq, rev_min_eq v r hv τ j T]
    have := phi_anti v r hv τ j T S (Finset.mem_powerset.mp hT) hS
    linarith
  · rw [← rev_min_eq v r hv τ j S]
    exact min_le_min_right τ (Finset.le_sup' (rev v r j) (Finset.mem_powerset_self S))

lemma rev_nonneg {n m : ℕ} (v : Fin n → Fin m → ℝ) (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (hv : ∀ i j, 0 ≤ v i j) (j : Fin m) (S : Finset (Fin n)) : 0 ≤ rev v r j S := by
  unfold rev ChoiceCDLP.MNL.mnlObjective
  apply div_nonneg
  · exact Finset.sum_nonneg (fun i _ => mul_nonneg (hr i).le (hv i j))
  · have := Finset.sum_nonneg (fun i (_ : i ∈ S) => hv i j)
    linarith

lemma fj_nonneg {n m : ℕ} (v : Fin n → Fin m → ℝ) (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (hv : ∀ i j, 0 ≤ v i j) (j : Fin m) (S : Finset (Fin n)) : 0 ≤ fj v r j S :=
  le_trans (rev_nonneg v r hr hv j S)
    (Finset.le_sup' (rev v r j) (Finset.mem_powerset_self S))

lemma fj_mono {n m : ℕ} (v : Fin n → Fin m → ℝ) (r : Fin n → ℝ) (j : Fin m)
    (A B : Finset (Fin n)) (hAB : A ⊆ B) : fj v r j A ≤ fj v r j B := by
  unfold fj
  exact Finset.sup'_mono _ (Finset.powerset_mono.mpr hAB) _

/-! ### The truncated objective on `Vset i` -/

lemma trunc_eq {n m : ℕ} (θ : Fin m → ℝ) (v : Fin n → Fin m → ℝ) (r : Fin n → ℝ)
    (hv : ∀ i j, 0 ≤ v i j) (C : Finset (Fin m)) (i : Fin n) (S : Finset (Fin n))
    (hS : ∀ p ∈ S, r i ≤ r p) :
    truncObj θ v r C i S = ∑ j ∈ C, θ j * (r i - phi v r (r i) j S) := by
  unfold truncObj
  apply Finset.sum_congr rfl
  intro j _
  rw [fj_min_eq v r hv (r i) j S hS]

lemma vset_r {n : ℕ} (r : Fin n → ℝ) (hanti : Antitone r) (i : Fin n) (S : Finset (Fin n))
    (hS : S ⊆ Vset i) : ∀ p ∈ S, r i ≤ r p := by
  intro p hp
  have := hS hp
  simp only [Vset, Finset.mem_filter, Finset.mem_univ, true_and] at this
  exact hanti this

lemma trunc_mono {n m : ℕ} (θ : Fin m → ℝ) (v : Fin n → Fin m → ℝ) (r : Fin n → ℝ)
    (hv : ∀ i j, 0 ≤ v i j) (hθ : ∀ j, 0 ≤ θ j) (hanti : Antitone r)
    (C : Finset (Fin m)) (i : Fin n) :
    ∀ A B, A ⊆ B → B ⊆ Vset i → truncObj θ v r C i A ≤ truncObj θ v r C i B := by
  intro A B hAB hB
  have hBr := vset_r r hanti i B hB
  have hAr := vset_r r hanti i A (hAB.trans hB)
  rw [trunc_eq θ v r hv C i A hAr, trunc_eq θ v r hv C i B hBr]
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_left _ (hθ j)
  have := phi_anti v r hv (r i) j A B hAB hBr
  linarith

lemma trunc_sub {n m : ℕ} (θ : Fin m → ℝ) (v : Fin n → Fin m → ℝ) (r : Fin n → ℝ)
    (hv : ∀ i j, 0 ≤ v i j) (hθ : ∀ j, 0 ≤ θ j) (hanti : Antitone r)
    (C : Finset (Fin m)) (i : Fin n) :
    SubmodularOn (truncObj θ v r C i) (Vset i) := by
  intro A B hAB hB x hx
  have hxV := (Finset.mem_sdiff.mp hx).1
  have hxB := (Finset.mem_sdiff.mp hx).2
  have hxBs : insert x B ⊆ Vset i := Finset.insert_subset hxV hB
  have hxAs : insert x A ⊆ Vset i := Finset.insert_subset hxV (hAB.trans hB)
  rw [trunc_eq θ v r hv C i _ (vset_r r hanti i _ hxBs),
    trunc_eq θ v r hv C i _ (vset_r r hanti i _ hB),
    trunc_eq θ v r hv C i _ (vset_r r hanti i _ hxAs),
    trunc_eq θ v r hv C i _ (vset_r r hanti i _ (hAB.trans hB)),
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro j _
  have := phi_super v r hv (r i) j A B hAB x hxB (vset_r r hanti i _ hxBs)
  have := mul_le_mul_of_nonneg_left this (hθ j)
  nlinarith

lemma trunc_empty {n m : ℕ} (θ : Fin m → ℝ) (v : Fin n → Fin m → ℝ) (r : Fin n → ℝ)
    (hv : ∀ i j, 0 ≤ v i j) (hr : ∀ i, 0 < r i) (C : Finset (Fin m)) (i : Fin n) :
    truncObj θ v r C i ∅ = 0 := by
  rw [trunc_eq θ v r hv C i ∅ (by simp)]
  apply Finset.sum_eq_zero
  intro j _
  unfold phi
  simp [(hr i).le]

end RRAux_CustAssort_AugGreedy_theorem_4_2

open RRAux_CustAssort_AugGreedy_theorem_4_2 in
open CustAssort.AugGreedy in
-- Theorem 4.2, p. 11: Augmented Greedy captures a 1−1/e fraction of complete-type revenue.
theorem solution {n m : ℕ} (θ : Fin m → ℝ) (v : Fin n → Fin m → ℝ)
    (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) (hv : ∀ i j, 0 ≤ v i j)
    (hθ : ∀ j, 0 ≤ θ j) (hθsum : ∑ j, θ j = 1) (hanti : Antitone r)
    (K : ℕ) (Sstar : Finset (Fin n)) (hS : IsCAPOpt θ v r K Sstar)
    (C : Finset (Fin m)) (P : Finset (Fin n)) (k : ℕ)
    (hk : (P ∩ Sstar).card ≤ k) (Δ : Finset (Fin n))
    (hΔ : IsAugGreedyOutput θ v r C k Δ) :
    (1 - Real.exp (-1)) *
      fC θ v r (completeTypes v r Sstar C P) (P ∩ Sstar) ≤ fC θ v r C Δ := by
  have hfCnn : 0 ≤ fC θ v r C Δ :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (hθ j) (fj_nonneg v r hr hv j Δ))
  have hexp0 : 0 ≤ 1 - Real.exp (-1) := by
    have : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    linarith
  rcases (P ∩ Sstar).eq_empty_or_nonempty with hQ | hQ
  · have h0 : fC θ v r (completeTypes v r Sstar C P) (P ∩ Sstar) = 0 := by
      rw [hQ]
      unfold fC
      apply Finset.sum_eq_zero
      intro j _
      have : fj v r j ∅ = 0 := by
        unfold fj rev ChoiceCDLP.MNL.mnlObjective
        simp
      rw [this, mul_zero]
    rw [h0, mul_zero]
    exact hfCnn
  set Q := P ∩ Sstar with hQdef
  set istar := Q.max' hQ with histar
  have histarQ : istar ∈ Q := Finset.max'_mem Q hQ
  have hQV : Q ⊆ Vset istar := by
    intro p hp
    simp only [Vset, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Finset.le_max' Q p hp
  obtain ⟨Δs, hgr, i0, hΔeq, hbest⟩ := hΔ
  have hG := greedy_bound (truncObj θ v r C istar) (Vset istar) Q k hQV hk
    (trunc_mono θ v r hv hθ hanti C istar) (trunc_sub θ v r hv hθ hanti C istar)
    (trunc_empty θ v r hv hr C istar) (Δs istar) (hgr istar)
  -- complete-type revenue is dominated by the truncated objective at `Q`
  have hCP : fC θ v r (completeTypes v r Sstar C P) Q ≤ truncObj θ v r C istar Q := by
    unfold fC truncObj
    calc ∑ j ∈ completeTypes v r Sstar C P, θ j * fj v r j Q
        = ∑ j ∈ completeTypes v r Sstar C P, θ j * min (fj v r j Q) (r istar) := by
          apply Finset.sum_congr rfl
          intro j hj
          congr 1
          symm
          apply min_eq_left
          simp only [completeTypes, Finset.mem_filter] at hj
          have hmem : istar ∈ P ∩ SstarJ v r Sstar j := by
            rw [hj.2]; exact histarQ
          have hthr := (Finset.mem_filter.mp (Finset.mem_inter.mp hmem).2).2
          exact le_trans (fj_mono v r j Q Sstar Finset.inter_subset_right) hthr
      _ ≤ ∑ j ∈ C, θ j * min (fj v r j Q) (r istar) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro j _ _
          exact mul_nonneg (hθ j) (le_min (fj_nonneg v r hr hv j Q) (hr istar).le)
  have hGf : truncObj θ v r C istar (Δs istar) ≤ fC θ v r C (Δs istar) := by
    unfold truncObj fC
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_left (min_le_left _ _) (hθ j)
  have hΔbest : fC θ v r C (Δs istar) ≤ fC θ v r C Δ := by
    rw [hΔeq]; exact hbest istar
  have := mul_le_mul_of_nonneg_left hCP hexp0
  linarith

#print axioms solution
