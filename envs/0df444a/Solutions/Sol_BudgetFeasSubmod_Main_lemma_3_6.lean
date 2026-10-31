-- Prove2me | solution 1 for BudgetFeasSubmod.Main.lemma_3_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T19:58:29.217047+00:00
-- url     : https://prove2.me/submissions/3de23b5b-07bc-47e3-aff9-2118599390d0

import Mathlib
import Definitions.Def_BudgetFeasSubmod_Main_Model

open BudgetFeasSubmod.Main Finset

namespace BFSsg

variable {A : Type} [Fintype A] [DecidableEq A]

/-- the while test of Simultaneous Greedy -/
def Test (v : Finset A → ℝ) (st : SGState A) : Prop :=
  ∃ i ∈ st.U, ∃ j : Fin 2, 0 < marg v i (st.S j)

/-- acceptance condition of line 4 -/
def Acc (v : Finset A → ℝ) (tb : Finset A → (Fin 2 → Finset A) → A × Fin 2) (β B x : ℝ)
    (b : A → ℝ) (st : SGState A) : Prop :=
  b (tb st.U st.S).1 ≤ price v β B x (tb st.U st.S).1 (st.S (tb st.U st.S).2) ∧
    price v β B x (tb st.U st.S).1 (st.S (tb st.U st.S).2) ≤ st.Bud (tb st.U st.S).2

section
variable (v : Finset A → ℝ) (tb : Finset A → (Fin 2 → Finset A) → A × Fin 2) (β B x : ℝ)

lemma step_fail (b : A → ℝ) (st : SGState A) (h : ¬ Test v st) :
    sgStep v tb β B x b st = st := by
  unfold Test at h; unfold sgStep; rw [if_neg h]

lemma step_acc (b : A → ℝ) (st : SGState A) (h : Test v st) (ha : Acc v tb β B x b st) :
    sgStep v tb β B x b st =
      ⟨Function.update st.S (tb st.U st.S).2 (insert (tb st.U st.S).1 (st.S (tb st.U st.S).2)),
       Function.update st.Bud (tb st.U st.S).2
         (st.Bud (tb st.U st.S).2 - price v β B x (tb st.U st.S).1 (st.S (tb st.U st.S).2)),
       st.U.erase (tb st.U st.S).1⟩ := by
  unfold Test at h; unfold sgStep; rw [if_pos h]; exact if_pos ha

lemma step_rej (b : A → ℝ) (st : SGState A) (h : Test v st) (ha : ¬ Acc v tb β B x b st) :
    sgStep v tb β B x b st = ⟨st.S, st.Bud, st.U.erase (tb st.U st.S).1⟩ := by
  unfold Test at h; unfold sgStep; rw [if_pos h]; exact if_neg ha

end

end BFSsg

namespace BFS36

open BFSsg NonmonotoneSubmod.Shared

variable {A : Type} [Fintype A] [DecidableEq A]

lemma dim_ret (v : Finset A → ℝ) (hsub : Submodular v) (a : A) (S T : Finset A) (hST : S ⊆ T)
    (ha : a ∉ T) : marg v a T ≤ marg v a S := by
  unfold marg
  have h := hsub (insert a S) T
  have e1 : insert a S ∪ T = insert a T := by
    rw [Finset.insert_union, Finset.union_eq_right.mpr hST]
  have e2 : insert a S ∩ T = S := by
    rw [Finset.insert_inter_of_notMem ha, Finset.inter_eq_left.mpr hST]
  rw [e1, e2] at h
  linarith

lemma marg_le_single (v : Finset A → ℝ) (hv : IsValuation v) (a : A) (S : Finset A)
    (ha : a ∉ S) : marg v a S ≤ v {a} := by
  have := dim_ret v hv.2.2 a ∅ S (Finset.empty_subset _) ha
  unfold marg at this ⊢
  rw [hv.1] at this
  simpa using this

lemma sub_add (v : Finset A → ℝ) (hv : IsValuation v) (X Y : Finset A) :
    v (X ∪ Y) ≤ v X + v Y := by
  have := hv.2.2 X Y; have := hv.2.1 (X ∩ Y); linarith

lemma sum_marg (v : Finset A → ℝ) (hsub : Submodular v) (S T : Finset A) :
    v (S ∪ T) ≤ v S + ∑ a ∈ T, marg v a S := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T haT ih =>
    rw [Finset.sum_insert haT]
    have h := hsub (insert a S) (S ∪ T)
    have e1 : insert a S ∪ (S ∪ T) = S ∪ insert a T := by
      ext y; simp only [Finset.mem_union, Finset.mem_insert]; tauto
    have e2 : insert a S ∩ (S ∪ T) = S := by
      ext y; simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | h1, h2⟩
        · rcases h2 with h2 | h2
          · exact h2
          · exact absurd h2 haT
        · exact h1
      · intro h; exact ⟨Or.inr h, Or.inl h⟩
    rw [e1, e2] at h
    unfold marg at ih ⊢
    linarith

lemma better_ge (v : Finset A → ℝ) (X Y : Finset A) :
    v X ≤ v (better v X Y) ∧ v Y ≤ v (better v X Y) := by
  unfold better; split_ifs with h
  · exact ⟨le_of_lt h, le_refl _⟩
  · exact ⟨le_refl _, not_lt.mp h⟩

section
variable (v : Finset A → ℝ) (tb : Finset A → (Fin 2 → Finset A) → A × Fin 2) (β B x : ℝ)
  (D : Finset A) (c : A → ℝ) (ℓ : ℕ)

def Inv36 (st : SGState A) : Prop :=
  (∀ j, Disjoint (st.S j) st.U) ∧ (∀ a ∈ st.S 0, a ∉ st.S 1) ∧ (∀ j, st.S j ⊆ D) ∧
    st.U ⊆ D ∧ (∀ j, st.Bud j = B - β * B / x * v (st.S j)) ∧
    (∀ j, ∀ u ∈ st.U, ((st.S j).card : ℝ) * marg v u (st.S j) ≤ v (st.S j)) ∧
    (∀ j, v (st.S j) ≤ ∑ a ∈ st.S j, v {a}) ∧
    ((∃ j, (ℓ : ℝ) * x / (((ℓ : ℝ) + 1) * β) ≤ v (st.S j)) ∨
      (∀ a ∈ D, a ∉ st.U → a ∉ st.S 0 → a ∉ st.S 1 → ∀ j,
        β * B / x * marg v a (st.S j) < c a))

lemma inv36_init (hv : IsValuation v) : Inv36 v β B x D c ℓ (sgInit D B) := by
  refine ⟨fun j => by simp [sgInit], fun a ha => by simp [sgInit] at ha, fun j => by simp [sgInit],
    by simp [sgInit], fun j => by simp [sgInit, hv.1], fun j u _ => by simp [sgInit, hv.1],
    fun j => by simp [sgInit, hv.1], Or.inr ?_⟩
  intro a ha haU
  simp [sgInit] at haU
  exact absurd ha haU

lemma inv36_step (hv : IsValuation v) (htb : IsArgmaxRule v tb) (hβ : 0 < β) (hB : 0 < B)
    (hx : 0 < x) (hc : InDomain B c) (hℓ : 0 < ℓ)
    (hmax : ∀ i ∈ D, v {i} < x / ((ℓ : ℝ) * β))
    (st : SGState A) (hI : Inv36 v β B x D c ℓ st) :
    Inv36 v β B x D c ℓ (sgStep v tb β B x c st) := by
  obtain ⟨I1, I2, I3, I4, I5, I6, I7, I8⟩ := hI
  have hκ : 0 < β * B / x := by positivity
  by_cases ht : Test v st
  · obtain ⟨hiU, hargmax⟩ := htb _ _ ht
    set i := (tb st.U st.S).1 with hi
    set j := (tb st.U st.S).2 with hj
    set m := marg v i (st.S j) with hm
    have hiS : ∀ j', i ∉ st.S j' := fun j' hh => Finset.disjoint_left.mp (I1 j') hh hiU
    have hmpos : 0 < m := by
      obtain ⟨i0, hi0, j0, hpos⟩ := ht
      exact lt_of_lt_of_le hpos (hargmax i0 hi0 j0)
    have hmle : m ≤ v {i} := marg_le_single v hv i _ (hiS j)
    have hiD : i ∈ D := I4 hiU
    have hπ : price v β B x i (st.S j) = β * B / x * m := rfl
    by_cases ha : Acc v tb β B x c st
    · rw [step_acc v tb β B x c st ht ha]
      unfold Inv36
      dsimp only
      have hvins : v (insert i (st.S j)) = v (st.S j) + m := by rw [hm]; unfold marg; ring
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro j'
        by_cases hjj : j' = j
        · subst hjj; rw [Function.update_self, Finset.disjoint_insert_left]
          exact ⟨Finset.notMem_erase _ _,
            Finset.disjoint_of_subset_right (Finset.erase_subset _ _) (I1 _)⟩
        · rw [Function.update_of_ne hjj]
          exact Finset.disjoint_of_subset_right (Finset.erase_subset _ _) (I1 _)
      · intro a ha0 ha1
        have hmem : ∀ j', a ∈ Function.update st.S j (insert i (st.S j)) j' →
            a = i ∧ j' = j ∨ a ∈ st.S j' := by
          intro j' hh
          by_cases hjj : j' = j
          · subst hjj
            rw [Function.update_self] at hh
            rcases Finset.mem_insert.mp hh with h | h
            · exact Or.inl ⟨h, rfl⟩
            · exact Or.inr h
          · rw [Function.update_of_ne hjj] at hh; exact Or.inr hh
        rcases hmem 0 ha0 with ⟨rfl, hj0⟩ | h0 <;> rcases hmem 1 ha1 with ⟨hai, hj1⟩ | h1'
        · exact absurd (hj0.trans hj1.symm) (by decide)
        · exact hiS 1 h1'
        · exact hiS 0 (hai ▸ h0)
        · exact I2 a h0 h1'
      · intro j'
        by_cases hjj : j' = j
        · subst hjj; rw [Function.update_self]; exact Finset.insert_subset hiD (I3 _)
        · rw [Function.update_of_ne hjj]; exact I3 j'
      · exact le_trans (Finset.erase_subset _ _) I4
      · intro j'
        by_cases hjj : j' = j
        · subst hjj; rw [Function.update_self, Function.update_self, I5, hvins, hπ]; ring
        · rw [Function.update_of_ne hjj, Function.update_of_ne hjj]; exact I5 j'
      · intro j' u hu
        have huU : u ∈ st.U := Finset.mem_of_mem_erase hu
        have hui : u ≠ i := Finset.ne_of_mem_erase hu
        by_cases hjj : j' = j
        · subst hjj
          rw [Function.update_self, Finset.card_insert_of_notMem (hiS _), hvins]
          have huS : u ∉ insert i (st.S j) := by
            rw [Finset.mem_insert]; rintro (h | h)
            · exact hui h
            · exact Finset.disjoint_left.mp (I1 j) h huU
          have hd := dim_ret v hv.2.2 u (st.S j) (insert i (st.S j)) (Finset.subset_insert _ _) huS
          have hag := hargmax u huU j
          have h6 := I6 j u huU
          have hs0 : (0 : ℝ) ≤ (st.S j).card := Nat.cast_nonneg _
          push_cast
          nlinarith [mul_le_mul_of_nonneg_left hd hs0]
        · rw [Function.update_of_ne hjj]; exact I6 j' u huU
      · intro j'
        by_cases hjj : j' = j
        · subst hjj
          rw [Function.update_self, Finset.sum_insert (hiS _), hvins]
          linarith [I7 j]
        · rw [Function.update_of_ne hjj]; exact I7 j'
      · rcases I8 with ⟨j0, hj0⟩ | hK
        · left; refine ⟨j0, le_trans hj0 ?_⟩
          by_cases hjj : j0 = j
          · subst hjj; rw [Function.update_self, hvins]; linarith
          · rw [Function.update_of_ne hjj]
        · right
          intro a haD haU ha0 ha1 j'
          have haU' : a ∉ st.U := fun h => by
            by_cases hai : a = i
            · rw [hai] at ha0 ha1
              by_cases hjj : j = 0
              · rw [← hjj, Function.update_self] at ha0; exact ha0 (Finset.mem_insert_self _ _)
              · have hj1 : j = 1 := (by decide : ∀ j : Fin 2, j ≠ 0 → j = 1) j hjj
                rw [← hj1, Function.update_self] at ha1; exact ha1 (Finset.mem_insert_self _ _)
            · exact haU (Finset.mem_erase.mpr ⟨hai, h⟩)
          have hai : a ≠ i := fun h => haU' (h ▸ hiU)
          have hnot : ∀ j'', a ∉ st.S j'' := by
            intro j'' hh
            have : a ∈ Function.update st.S j (insert i (st.S j)) j'' := by
              by_cases hjj : j'' = j
              · subst hjj; rw [Function.update_self]; exact Finset.mem_insert_of_mem hh
              · rw [Function.update_of_ne hjj]; exact hh
            have h01 : j'' = 0 ∨ j'' = 1 := by fin_cases j'' <;> simp
            rcases h01 with rfl | rfl
            · exact ha0 this
            · exact ha1 this
          have hK' := hK a haD haU' (hnot 0) (hnot 1) j'
          by_cases hjj : j' = j
          · subst hjj
            have hK'' := hK'
            rw [Function.update_self]
            have hd := dim_ret v hv.2.2 a (st.S j) (insert i (st.S j)) (Finset.subset_insert _ _)
              (by rw [Finset.mem_insert]; rintro (h | h); exact hai h; exact hnot _ h)
            nlinarith [mul_le_mul_of_nonneg_left hd hκ.le]
          · rw [Function.update_of_ne hjj]; exact hK'
    · rw [step_rej v tb β B x c st ht ha]
      unfold Inv36
      dsimp only
      refine ⟨fun j' => Finset.disjoint_of_subset_right (Finset.erase_subset _ _) (I1 j'), I2, I3,
        le_trans (Finset.erase_subset _ _) I4, I5,
        fun j' u hu => I6 j' u (Finset.mem_of_mem_erase hu), I7, ?_⟩
      rcases I8 with hG | hK
      · exact Or.inl hG
      · by_cases hbud : β * B / x * m ≤ st.Bud j
        · -- rejected because of its cost
          have hcost : β * B / x * m < c i := by
            by_contra hh; push Not at hh
            exact ha ⟨by rw [hπ]; exact hh, by rw [hπ]; exact hbud⟩
          right
          intro a haD haU ha0 ha1 j'
          by_cases hai : a = i
          · rw [hai]
            have hag := hargmax i hiU j'
            nlinarith [mul_le_mul_of_nonneg_left hag hκ.le]
          · exact hK a haD (fun h => haU (Finset.mem_erase.mpr ⟨hai, h⟩)) ha0 ha1 j'
        · -- rejected because the budget is exhausted: Case 1 of the source
          left
          refine ⟨j, ?_⟩
          push Not at hbud
          rw [I5 j] at hbud
          set V := v (st.S j)
          set s := ((st.S j).card : ℝ)
          set q := x / ((ℓ : ℝ) * β) with hq
          have hℓR : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
          -- (a) V + m > x/β
          have hVm : x / β < V + m := by
            have : B < β * B / x * (V + m) := by linarith
            rw [div_lt_iff₀ hβ]
            have e : β * B / x * (V + m) = B * (β * (V + m)) / x := by ring
            rw [e, lt_div_iff₀ hx] at this
            nlinarith
          -- (b) V ≤ s q, m < q
          have hVs : V ≤ s * q := by
            refine le_trans (I7 j) ?_
            have : ∑ a ∈ st.S j, v {a} ≤ ∑ a ∈ st.S j, q :=
              Finset.sum_le_sum fun a ha => le_of_lt (hmax a (I3 j ha))
            rw [Finset.sum_const, nsmul_eq_mul] at this
            exact this
          have hmq : m < q := lt_of_le_of_lt hmle (hmax i hiD)
          have hqdef : q * ((ℓ : ℝ) * β) = x := by rw [hq]; field_simp
          -- (c) s ≥ ℓ
          have hsℓ : (ℓ : ℝ) ≤ s := by
            have h1 : x / β < (s + 1) * q := by nlinarith
            have h2 : x / β = (ℓ : ℝ) * q := by
              rw [div_eq_iff hβ.ne']; nlinarith
            rw [h2] at h1
            have hq0 : 0 < q := by rw [hq]; positivity
            have h3 : (ℓ : ℝ) < s + 1 := lt_of_mul_lt_mul_right (by linarith) hq0.le
            have hsn : ∃ n : ℕ, s = n := ⟨_, rfl⟩
            obtain ⟨n, hn⟩ := hsn
            rw [hn] at h3 ⊢
            have : ℓ < n + 1 := by exact_mod_cast h3
            exact_mod_cast Nat.lt_succ_iff.mp this
          -- (d) s m ≤ V
          have hsm : s * m ≤ V := I6 j i hiU
          -- conclude
          have hs0 : 0 < s := lt_of_lt_of_le (by exact_mod_cast hℓ) hsℓ
          have key : s * (x / β) < (s + 1) * V := by nlinarith
          have hxb : 0 < x / β := by positivity
          rw [show (ℓ : ℝ) * x / (((ℓ : ℝ) + 1) * β) = (ℓ : ℝ) / ((ℓ : ℝ) + 1) * (x / β) by
            field_simp]
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          -- ℓ (x/β) ≤ V (ℓ+1): from s(x/β) < (s+1) V and ℓ ≤ s
          have hV0 : 0 ≤ V := hv.2.1 _
          nlinarith [mul_le_mul_of_nonneg_right hsℓ hxb.le, mul_le_mul_of_nonneg_right hsℓ hV0]
  · rw [step_fail v tb β B x c st ht]
    exact ⟨I1, I2, I3, I4, I5, I6, I7, I8⟩

lemma inv36_iter (hv : IsValuation v) (htb : IsArgmaxRule v tb) (hβ : 0 < β) (hB : 0 < B)
    (hx : 0 < x) (hc : InDomain B c) (hℓ : 0 < ℓ)
    (hmax : ∀ i ∈ D, v {i} < x / ((ℓ : ℝ) * β)) (n : ℕ) :
    Inv36 v β B x D c ℓ ((sgStep v tb β B x c)^[n] (sgInit D B)) := by
  induction n with
  | zero => exact inv36_init v β B x D c ℓ hv
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact inv36_step v tb β B x D c ℓ hv htb hβ hB hx hc hℓ hmax _ ih

lemma term_iter (htb : IsArgmaxRule v tb) (n : ℕ) :
    ¬ Test v ((sgStep v tb β B x c)^[n] (sgInit D B)) ∨
      ((sgStep v tb β B x c)^[n] (sgInit D B)).U.card + n ≤ D.card := by
  induction n with
  | zero => right; simp [sgInit]
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    set st := (sgStep v tb β B x c)^[n] (sgInit D B)
    by_cases ht : Test v st
    · have hiU := (htb _ _ ht).1
      right
      have hle := ih.resolve_left (not_not.mpr ht)
      by_cases ha : Acc v tb β B x c st
      · rw [step_acc v tb β B x c st ht ha]
        simp only
        rw [Finset.card_erase_of_mem hiU]
        have := Finset.card_pos.mpr ⟨_, hiU⟩
        omega
      · rw [step_rej v tb β B x c st ht ha]
        simp only
        rw [Finset.card_erase_of_mem hiU]
        have := Finset.card_pos.mpr ⟨_, hiU⟩
        omega
    · left; rw [step_fail v tb β B x c st ht]; exact ht

end

end BFS36

open BFSsg BFS36 in
theorem solution {A : Type} [Fintype A] [DecidableEq A] (v : Finset A → ℝ)
    (alg2 : Finset A → Finset A) (tb : Finset A → (Fin 2 → Finset A) → A × Fin 2)
    (β B x : ℝ) (D : Finset A) (c : A → ℝ) (ℓ : ℕ)
    (hv : IsValuation v) (h2 : IsUnconstrainedTwoApprox v alg2) (htb : IsArgmaxRule v tb)
    (hβ : 0 < β) (hB : 0 < B) (hc : InDomain B c) (hℓ : 0 < ℓ)
    (hmax : ∀ i ∈ D, v {i} < x / ((ℓ : ℝ) * β)) :
    min ((ℓ : ℝ) * x / (((ℓ : ℝ) + 1) * β)) ((opt v c B D - 2 * x / β) / 6) ≤
      v (simGreedy v alg2 tb β B x D c) := by
  have hv0 : ∀ S, 0 ≤ v S := hv.2.1
  -- an optimal solution inside D
  have hne : (D.powerset.filter (fun T => ∑ i ∈ T, c i ≤ B)).Nonempty :=
    ⟨∅, Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset D, by simpa using hB.le⟩⟩
  obtain ⟨C, hCmem, hCeq⟩ := Finset.exists_mem_eq_sup' hne v
  rw [Finset.mem_filter, Finset.mem_powerset] at hCmem
  have hopt : opt v c B D = v C := by unfold opt; rw [dif_pos hne, hCeq]
  have hℓR : (0 : ℝ) < ℓ := Nat.cast_pos.mpr hℓ
  rcases Finset.eq_empty_or_nonempty D with hD | ⟨d0, hd0⟩
  · -- empty ground set
    have hC : C = ∅ := Finset.subset_empty.mp (hD ▸ hCmem.1)
    rw [hopt, hC, hv.1]
    apply le_trans _ (hv0 _)
    rcases le_or_gt 0 x with hx | hx
    · apply le_trans (min_le_right _ _); have : 0 ≤ 2 * x / β := by positivity
      linarith
    · apply le_trans (min_le_left _ _)
      apply div_nonpos_of_nonpos_of_nonneg (by nlinarith) (by positivity)
  · have hx : 0 < x := by
      have h := hmax d0 hd0
      have h0 := hv0 {d0}
      have : 0 < x / ((ℓ : ℝ) * β) := lt_of_le_of_lt h0 h
      exact (div_pos_iff_of_pos_right (by positivity)).mp this
    set st := (sgStep v tb β B x c)^[D.card] (sgInit D B) with hst
    have hout : simGreedy v alg2 tb β B x D c =
        better v (better v (better v (st.S 0) (st.S 1)) (alg2 (st.S 0))) (alg2 (st.S 1)) := rfl
    set S := simGreedy v alg2 tb β B x D c
    have g1 := better_ge v (better v (better v (st.S 0) (st.S 1)) (alg2 (st.S 0))) (alg2 (st.S 1))
    have g2 := better_ge v (better v (st.S 0) (st.S 1)) (alg2 (st.S 0))
    have g3 := better_ge v (st.S 0) (st.S 1)
    rw [← hout] at g1
    have hS0 : v (st.S 0) ≤ v S := by linarith [g1.1, g2.1, g3.1]
    have hS1 : v (st.S 1) ≤ v S := by linarith [g1.1, g2.1, g3.2]
    have hT0 : v (alg2 (st.S 0)) ≤ v S := by linarith [g1.1, g2.2]
    have hT1 : v (alg2 (st.S 1)) ≤ v S := g1.2
    have hI := inv36_iter v tb β B x D c ℓ hv htb hβ hB hx hc hℓ hmax D.card
    rw [← hst] at hI
    obtain ⟨I1, I2, I3, I4, I5, I6, I7, I8⟩ := hI
    have hterm : ¬ Test v st := by
      rcases term_iter v tb β B x D c htb D.card with h | h
      · exact h
      · rw [← hst] at h
        intro ht
        obtain ⟨i0, hi0, -⟩ := ht
        have : st.U.card = 0 := by omega
        rw [Finset.card_eq_zero] at this
        rw [this] at hi0; simp at hi0
    rcases I8 with ⟨j0, hj0⟩ | hK
    · -- Case 1
      apply le_trans (min_le_left _ _)
      have h01 : j0 = 0 ∨ j0 = 1 := by fin_cases j0 <;> simp
      rcases h01 with rfl | rfl
      · linarith
      · linarith
    · -- Case 2
      apply le_trans (min_le_right _ _)
      rw [hopt]
      set C1 := C ∩ st.S 0
      set C2 := C ∩ st.S 1
      set C3 := C \ (st.S 0 ∪ st.S 1) with hC3
      have hCsplit : C = C1 ∪ (C2 ∪ C3) := by
        ext a; simp only [C1, C2, hC3, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
      have e1 : v C ≤ v C1 + v C2 + v C3 := by
        have := sub_add v hv C1 (C2 ∪ C3)
        have := sub_add v hv C2 C3
        rw [← hCsplit] at *; linarith
      have hoi : ∀ (Sj Cj : Finset A), Cj ⊆ Sj → v Cj ≤ 2 * v (alg2 Sj) := by
        intro Sj Cj h
        refine le_trans ?_ (h2 Sj).2
        unfold optInf
        exact Finset.le_sup' v (Finset.mem_powerset.mpr h)
      have e2 := hoi (st.S 0) C1 Finset.inter_subset_right
      have e3 := hoi (st.S 1) C2 Finset.inter_subset_right
      -- v(C3) ≤ v(S0 ∪ C3) + v(S1 ∪ C3)
      have e4 : v C3 ≤ v (st.S 0 ∪ C3) + v (st.S 1 ∪ C3) := by
        have h := hv.2.2 (st.S 0 ∪ C3) (st.S 1 ∪ C3)
        have hi : (st.S 0 ∪ C3) ∩ (st.S 1 ∪ C3) = C3 := by
          ext a; simp only [Finset.mem_inter, Finset.mem_union]
          constructor
          · rintro ⟨h0 | h0, h1 | h1⟩
            · exact absurd h1 (I2 a h0)
            · exact h1
            · exact h0
            · exact h0
          · intro h; exact ⟨Or.inr h, Or.inr h⟩
        rw [hi] at h
        have := hv0 ((st.S 0 ∪ C3) ∪ (st.S 1 ∪ C3))
        linarith
      -- the marginal bound
      have hκ : 0 < β * B / x := by positivity
      have e5 : ∀ j, v (st.S j ∪ C3) ≤ v (st.S j) + x / β := by
        intro j
        refine le_trans (sum_marg v hv.2.2 (st.S j) C3) ?_
        have hterm' : ∑ a ∈ C3, marg v a (st.S j) ≤ ∑ a ∈ C3, c a / (β * B / x) := by
          apply Finset.sum_le_sum
          intro a ha
          rw [hC3, Finset.mem_sdiff, Finset.mem_union] at ha
          have haD : a ∈ D := hCmem.1 ha.1
          have ha0 : a ∉ st.S 0 := fun h => ha.2 (Or.inl h)
          have ha1 : a ∉ st.S 1 := fun h => ha.2 (Or.inr h)
          by_cases haU : a ∈ st.U
          · have : marg v a (st.S j) ≤ 0 := by
              by_contra hh; push Not at hh; exact hterm ⟨a, haU, j, hh⟩
            exact le_trans this (div_nonneg (hc a).1 hκ.le)
          · have := hK a haD haU ha0 ha1 j
            rw [le_div_iff₀ hκ]; linarith
        have hsumc : ∑ a ∈ C3, c a / (β * B / x) ≤ x / β := by
          rw [← Finset.sum_div]
          have : ∑ a ∈ C3, c a ≤ B :=
            le_trans (Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
              (fun i _ _ => (hc i).1)) hCmem.2
          rw [div_le_iff₀ hκ]
          have e : x / β * (β * B / x) = B := by field_simp
          rw [e]; exact this
        linarith
      have e6 := e5 0
      have e7 := e5 1
      have : 2 * x / β = 2 * (x / β) := by ring
      linarith
