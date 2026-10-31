-- Prove2me | solution 1 for BudgetFeasSubmod.Main.corollary_3_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T19:47:15.503222+00:00
-- url     : https://prove2.me/submissions/2a2de2f0-fb75-4e77-ba30-eb7b7aab389f

import Mathlib
import Definitions.Def_BudgetFeasSubmod_Main_Model
import Theorems.Thm_BudgetFeasSubmod_Main_lemma_2_4

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

open Classical in
/-- Simultaneous Greedy augmented with a record of the price paid to each accepted agent. -/
noncomputable def augStep (b : A → ℝ) (p : SGState A × (A → ℝ)) : SGState A × (A → ℝ) :=
  (sgStep v tb β B x b p.1,
    if Test v p.1 ∧ Acc v tb β B x b p.1 then
      Function.update p.2 (tb p.1.U p.1.S).1
        (price v β B x (tb p.1.U p.1.S).1 (p.1.S (tb p.1.U p.1.S).2))
    else p.2)

lemma aug_fst (b : A → ℝ) (n : ℕ) (p : SGState A × (A → ℝ)) :
    ((augStep v tb β B x b)^[n] p).1 = (sgStep v tb β B x b)^[n] p.1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
    rfl

/-- invariants of the augmented run -/
def Inv (b : A → ℝ) (p : SGState A × (A → ℝ)) : Prop :=
  (∀ j, Disjoint (p.1.S j) p.1.U) ∧ (∀ j, p.1.Bud j = B - ∑ a ∈ p.1.S j, p.2 a) ∧
    (∀ j, ∀ a ∈ p.1.S j, b a ≤ p.2 a) ∧ (∀ j, 0 ≤ p.1.Bud j) ∧
    (∀ a, a ∈ p.1.S 0 → a ∉ p.1.S 1)

lemma fin2_ne (j j' : Fin 2) (h : j' ≠ j) : j' = 1 - j := by
  fin_cases j <;> fin_cases j' <;> simp_all <;> decide

lemma inv_step (htb : IsArgmaxRule v tb) (b : A → ℝ) (p : SGState A × (A → ℝ))
    (hp : Inv B b p) : Inv B b (augStep v tb β B x b p) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hp
  by_cases ht : Test v p.1
  · have hiU : (tb p.1.U p.1.S).1 ∈ p.1.U := (htb _ _ ht).1
    set i := (tb p.1.U p.1.S).1 with hi
    set j := (tb p.1.U p.1.S).2 with hj
    have hiS : ∀ j', i ∉ p.1.S j' := fun j' hh =>
      Finset.disjoint_left.mp (h1 j') hh hiU
    by_cases ha : Acc v tb β B x b p.1
    · unfold augStep
      rw [step_acc v tb β B x b p.1 ht ha, if_pos ⟨ht, ha⟩]
      unfold Inv
      dsimp only
      simp only [← hi, ← hj]
      set π := price v β B x i (p.1.S j)
      have hsum : ∀ T : Finset A, i ∉ T →
          ∑ a ∈ T, Function.update p.2 i π a = ∑ a ∈ T, p.2 a := by
        intro T hT
        apply Finset.sum_congr rfl
        intro a ha'
        rw [Function.update_of_ne (fun h => hT (by rw [← h]; exact ha'))]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro j'
        by_cases hjj : j' = j
        · subst hjj
          rw [Function.update_self]
          rw [Finset.disjoint_insert_left]
          exact ⟨Finset.notMem_erase _ _,
            Finset.disjoint_of_subset_right (Finset.erase_subset _ _) (h1 _)⟩
        · rw [Function.update_of_ne hjj]
          exact Finset.disjoint_of_subset_right (Finset.erase_subset _ _) (h1 _)
      · intro j'
        by_cases hjj : j' = j
        · subst hjj
          rw [Function.update_self, Function.update_self, Finset.sum_insert (hiS _),
            Function.update_self, hsum _ (hiS _), h2]
          ring
        · rw [Function.update_of_ne hjj, Function.update_of_ne hjj, hsum _ (hiS _), h2]
      · intro j' a ha'
        by_cases hai : a = i
        · subst hai
          rw [Function.update_self]; exact ha.1
        · rw [Function.update_of_ne hai]
          by_cases hjj : j' = j
          · subst hjj
            rw [Function.update_self] at ha'
            exact h3 _ a ((Finset.mem_insert.mp ha').resolve_left hai)
          · rw [Function.update_of_ne hjj] at ha'
            exact h3 j' a ha'
      · intro j'
        by_cases hjj : j' = j
        · subst hjj
          rw [Function.update_self]; linarith [ha.2]
        · rw [Function.update_of_ne hjj]; exact h4 j'
      · intro a ha0 ha1
        have hmem : ∀ j', a ∈ Function.update p.1.S j (insert i (p.1.S j)) j' →
            a = i ∧ j' = j ∨ a ∈ p.1.S j' := by
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
        · exact h5 a h0 h1'
    · unfold augStep
      rw [step_rej v tb β B x b p.1 ht ha, if_neg (fun h => ha h.2)]
      exact ⟨fun j' => Finset.disjoint_of_subset_right (Finset.erase_subset _ _) (h1 j'),
        h2, h3, h4, h5⟩
  · unfold augStep
    rw [step_fail v tb β B x b p.1 ht, if_neg (fun h => ht h.1)]
    exact ⟨h1, h2, h3, h4, h5⟩

lemma inv_init (hB : 0 ≤ B) (b : A → ℝ) (D : Finset A) :
    Inv B b (sgInit D B, fun _ => 0) := by
  refine ⟨fun j => by simp [sgInit], fun j => by simp [sgInit], fun j a ha => by simp [sgInit] at ha,
    fun j => by simp [sgInit, hB], fun a ha => by simp [sgInit] at ha⟩

lemma inv_iter (htb : IsArgmaxRule v tb) (hB : 0 ≤ B) (b : A → ℝ) (D : Finset A) (n : ℕ) :
    Inv B b ((augStep v tb β B x b)^[n] (sgInit D B, fun _ => 0)) := by
  induction n with
  | zero => exact inv_init B hB b D
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact inv_step v tb β B x htb b _ ih

/-- "agent `a` is out" of a state: neither active nor selected -/
def Out (a : A) (st : SGState A) : Prop := a ∉ st.U ∧ ∀ j, a ∉ st.S j

lemma out_step (htb : IsArgmaxRule v tb) (b : A → ℝ) (a : A) (st : SGState A)
    (h : Out a st) : Out a (sgStep v tb β B x b st) := by
  by_cases ht : Test v st
  · have hiU : (tb st.U st.S).1 ∈ st.U := (htb _ _ ht).1
    have hne : (tb st.U st.S).1 ≠ a := fun e => h.1 (e ▸ hiU)
    by_cases ha : Acc v tb β B x b st
    · rw [step_acc v tb β B x b st ht ha]
      refine ⟨fun hh => h.1 (Finset.mem_of_mem_erase hh), fun j' hh => ?_⟩
      simp only at hh
      by_cases hjj : j' = (tb st.U st.S).2
      · subst hjj
        rw [Function.update_self] at hh
        rcases Finset.mem_insert.mp hh with e | e
        · exact hne e.symm
        · exact h.2 _ e
      · rw [Function.update_of_ne hjj] at hh; exact h.2 _ hh
    · rw [step_rej v tb β B x b st ht ha]
      exact ⟨fun hh => h.1 (Finset.mem_of_mem_erase hh), h.2⟩
  · rw [step_fail v tb β B x b st ht]; exact h

/-- Two runs whose bids differ only at agent `a`. -/
lemma traj (htb : IsArgmaxRule v tb) (hB : 0 ≤ B) (b b' : A → ℝ) (a : A)
    (hbb : ∀ i, i ≠ a → b i = b' i) (D : Finset A) (n : ℕ) :
    let p := (augStep v tb β B x b)^[n] (sgInit D B, fun _ => 0)
    let p' := (augStep v tb β B x b')^[n] (sgInit D B, fun _ => 0)
    (p.1 = p'.1 ∧ p.2 a = p'.2 a) ∨ (Out a p'.1 ∧ b a < b' a) ∨ (Out a p.1 ∧ b' a < b a) := by
  induction n with
  | zero => exact Or.inl ⟨rfl, rfl⟩
  | succ n ih =>
    intro p p'
    have hp : p = augStep v tb β B x b ((augStep v tb β B x b)^[n] (sgInit D B, fun _ => 0)) :=
      Function.iterate_succ_apply' _ _ _
    have hp' : p' = augStep v tb β B x b'
        ((augStep v tb β B x b')^[n] (sgInit D B, fun _ => 0)) :=
      Function.iterate_succ_apply' _ _ _
    set q := (augStep v tb β B x b)^[n] (sgInit D B, fun _ => 0) with hq
    set q' := (augStep v tb β B x b')^[n] (sgInit D B, fun _ => 0) with hq'
    have inv' := inv_iter v tb β B x htb hB b' D n
    rw [← hq'] at inv'
    have inv := inv_iter v tb β B x htb hB b D n
    rw [← hq] at inv
    rcases ih with ⟨e1, e2⟩ | ⟨ho, hlt⟩ | ⟨ho, hlt⟩
    · -- equal states
      by_cases ht : Test v q.1
      · have ht' : Test v q'.1 := e1 ▸ ht
        set i := (tb q.1.U q.1.S).1 with hi
        have hiU : i ∈ q.1.U := (htb _ _ ht).1
        by_cases hia : i = a
        · -- the agent `a` is examined now
          by_cases ha : Acc v tb β B x b q.1 <;> by_cases ha' : Acc v tb β B x b' q'.1
          · left
            rw [hp, hp']
            unfold augStep
            have ha1 : Acc v tb β B x b q'.1 := e1 ▸ ha
            rw [if_pos ⟨ht, ha⟩, if_pos ⟨ht', ha'⟩, e1]
            refine ⟨?_, ?_⟩
            · dsimp only
              rw [step_acc v tb β B x b q'.1 ht' ha1, step_acc v tb β B x b' q'.1 ht' ha']
            simp only
            rw [← e1, ← hi, hia, Function.update_self, Function.update_self]
          · right; left
            refine ⟨?_, ?_⟩
            · rw [hp']
              show Out a (sgStep v tb β B x b' q'.1)
              rw [step_rej v tb β B x b' q'.1 ht' ha']
              have hi' : (tb q'.1.U q'.1.S).1 = a := by rw [← e1]; exact hia
              refine ⟨by simp only; rw [hi']; exact Finset.notMem_erase _ _, fun j hh => ?_⟩
              have hU : a ∈ q'.1.U := by rw [← e1, ← hia]; exact hiU
              exact Finset.disjoint_left.mp (inv'.1 j) hh hU
            · have hAcc : Acc v tb β B x b q'.1 := e1 ▸ ha
              unfold Acc at hAcc ha'
              have hi' : (tb q'.1.U q'.1.S).1 = a := by rw [← e1]; exact hia
              rw [hi'] at hAcc ha'
              by_contra hh
              exact ha' ⟨le_trans (not_lt.mp hh) hAcc.1, hAcc.2⟩
          · right; right
            refine ⟨?_, ?_⟩
            · rw [hp]
              show Out a (sgStep v tb β B x b q.1)
              rw [step_rej v tb β B x b q.1 ht ha]
              refine ⟨by simp only; rw [← hi, hia]; exact Finset.notMem_erase _ _, fun j hh => ?_⟩
              have hU : a ∈ q.1.U := by rw [← hia]; exact hiU
              exact Finset.disjoint_left.mp (inv.1 j) hh hU
            · have hAcc : Acc v tb β B x b' q.1 := e1 ▸ ha'
              unfold Acc at hAcc ha
              rw [← hi, hia] at hAcc ha
              by_contra hh
              exact ha ⟨le_trans (not_lt.mp hh) hAcc.1, hAcc.2⟩
          · left
            rw [hp, hp']
            unfold augStep
            rw [if_neg (fun h => ha h.2), if_neg (fun h => ha' h.2),
              step_rej v tb β B x b q.1 ht ha, step_rej v tb β B x b' q'.1 ht' ha', e1]
            exact ⟨rfl, e2⟩
        · -- another agent is examined: the bids agree there
          have hbi : b i = b' i := hbb i hia
          have hAcc : Acc v tb β B x b q.1 ↔ Acc v tb β B x b' q'.1 := by
            rw [← e1]; unfold Acc; rw [← hi, hbi]
          have hstep : sgStep v tb β B x b q.1 = sgStep v tb β B x b' q'.1 := by
            by_cases ha : Acc v tb β B x b q.1
            · rw [step_acc v tb β B x b q.1 ht ha, step_acc v tb β B x b' q'.1 ht' (hAcc.mp ha), e1]
            · rw [step_rej v tb β B x b q.1 ht ha,
                step_rej v tb β B x b' q'.1 ht' (fun h => ha (hAcc.mpr h)), e1]
          left
          rw [hp, hp']
          unfold augStep
          refine ⟨hstep, ?_⟩
          simp only
          by_cases ha : Acc v tb β B x b q.1
          · rw [if_pos ⟨ht, ha⟩, if_pos ⟨ht', hAcc.mp ha⟩, ← e1, ← hi,
              Function.update_of_ne (Ne.symm hia), Function.update_of_ne (Ne.symm hia), e2]
          · rw [if_neg (fun h => ha h.2), if_neg (fun h => ha (hAcc.mpr h.2)), e2]
      · have ht' : ¬ Test v q'.1 := e1 ▸ ht
        left
        rw [hp, hp']
        unfold augStep
        rw [if_neg (fun h => ht h.1), if_neg (fun h => ht' h.1),
          step_fail v tb β B x b q.1 ht, step_fail v tb β B x b' q'.1 ht']
        exact ⟨e1, e2⟩
    · right; left
      refine ⟨?_, hlt⟩
      rw [hp']
      exact out_step v tb β B x htb b' a q'.1 ho
    · right; right
      refine ⟨?_, hlt⟩
      rw [hp]
      exact out_step v tb β B x htb b a q.1 ho


/-- the output of Simultaneous Greedy, as a function of the final state -/
noncomputable def outOf (alg2 : Finset A → Finset A) (st : SGState A) : Finset A :=
  better v (better v (better v (st.S 0) (st.S 1)) (alg2 (st.S 0))) (alg2 (st.S 1))

lemma simGreedy_eq (alg2 : Finset A → Finset A) (D : Finset A) (b : A → ℝ) :
    simGreedy v alg2 tb β B x D b =
      outOf v alg2 ((augStep v tb β B x b)^[D.card] (sgInit D B, fun _ => 0)).1 := by
  unfold simGreedy sgRun outOf
  rw [aug_fst]

lemma better_cases (X Y : Finset A) : better v X Y = X ∨ better v X Y = Y := by
  unfold better; split_ifs <;> simp

lemma outOf_sub (alg2 : Finset A → Finset A) (h2 : ∀ S, alg2 S ⊆ S) (st : SGState A) :
    outOf v alg2 st ⊆ st.S 0 ∨ outOf v alg2 st ⊆ st.S 1 := by
  unfold outOf
  rcases better_cases v (better v (better v (st.S 0) (st.S 1)) (alg2 (st.S 0))) (alg2 (st.S 1))
    with h | h <;> rw [h]
  · rcases better_cases v (better v (st.S 0) (st.S 1)) (alg2 (st.S 0)) with h' | h' <;> rw [h']
    · rcases better_cases v (st.S 0) (st.S 1) with h'' | h'' <;> rw [h''] <;> simp
    · exact Or.inl (h2 _)
  · exact Or.inr (h2 _)

lemma mem_outOf (alg2 : Finset A → Finset A) (h2 : ∀ S, alg2 S ⊆ S) (st : SGState A) (a : A)
    (h : a ∈ outOf v alg2 st) : ∃ j, a ∈ st.S j := by
  rcases outOf_sub v alg2 h2 st with h' | h'
  · exact ⟨0, h' h⟩
  · exact ⟨1, h' h⟩

lemma out_not_mem (alg2 : Finset A → Finset A) (h2 : ∀ S, alg2 S ⊆ S) (st : SGState A) (a : A)
    (h : Out a st) : a ∉ outOf v alg2 st := by
  intro hh
  obtain ⟨j, hj⟩ := mem_outOf v alg2 h2 st a hh
  exact h.2 j hj

/-- Lemma 3.3 (with `alg2 S ⊆ S`): monotonicity of Simultaneous Greedy. -/
lemma sg_mono (alg2 : Finset A → Finset A) (h2 : ∀ S, alg2 S ⊆ S) (htb : IsArgmaxRule v tb)
    (hB : 0 ≤ B) (D : Finset A) : IsMonotoneRule (simGreedy v alg2 tb β B x D) B := by
  intro b a t _ _ hta ha
  rw [simGreedy_eq] at ha ⊢
  have hbb : ∀ i, i ≠ a → b i = Function.update b a t i :=
    fun i hi => (Function.update_of_ne hi _ _).symm
  rcases traj v tb β B x htb hB b (Function.update b a t) a hbb D D.card with
    ⟨e1, _⟩ | ⟨_, hlt⟩ | ⟨ho, _⟩
  · rw [← e1]; exact ha
  · rw [Function.update_self] at hlt; linarith
  · exact absurd ha (out_not_mem v alg2 h2 _ a ho)

/-- Lemma 3.4: budget feasibility of Simultaneous Greedy. -/
lemma sg_bf (alg2 : Finset A → Finset A) (h2 : ∀ S, alg2 S ⊆ S) (htb : IsArgmaxRule v tb)
    (hB : 0 ≤ B) (D : Finset A) : IsBudgetFeasible (simGreedy v alg2 tb β B x D) B := by
  intro b hb
  set p := (augStep v tb β B x b)^[D.card] (sgInit D B, fun _ => 0) with hp
  have inv := inv_iter v tb β B x htb hB b D D.card
  rw [← hp] at inv
  -- each threshold is at most the recorded price
  have hthr : ∀ a ∈ simGreedy v alg2 tb β B x D b,
      thr (simGreedy v alg2 tb β B x D) B b a ≤ p.2 a := by
    intro a ha
    unfold thr
    rw [if_pos ha]
    have hne : ({t : ℝ | t ∈ Set.Icc (b a) B ∧
        a ∈ simGreedy v alg2 tb β B x D (Function.update b a t)}).Nonempty :=
      ⟨b a, ⟨le_refl _, (hb a).2⟩, by rw [Function.update_eq_self]; exact ha⟩
    apply csSup_le hne
    intro t htt
    have ht := htt.2
    rw [simGreedy_eq] at ha ht
    rw [← hp] at ha
    have hbb : ∀ i, i ≠ a → b i = Function.update b a t i :=
      fun i hi => (Function.update_of_ne hi _ _).symm
    have inv' := inv_iter v tb β B x htb hB (Function.update b a t) D D.card
    rcases traj v tb β B x htb hB b (Function.update b a t) a hbb D D.card with
      ⟨_, e2⟩ | ⟨ho, _⟩ | ⟨ho, _⟩
    · obtain ⟨j, hj⟩ := mem_outOf v alg2 h2 _ a ht
      have := inv'.2.2.1 j a hj
      rw [Function.update_self] at this
      rw [hp, e2]; exact this
    · exact absurd ht (out_not_mem v alg2 h2 _ a ho)
    · exact absurd ha (out_not_mem v alg2 h2 _ a ho)
  have hzero : ∀ a ∉ simGreedy v alg2 tb β B x D b,
      thr (simGreedy v alg2 tb β B x D) B b a = 0 := by
    intro a ha; unfold thr; rw [if_neg ha]
  rw [← Finset.sum_subset (Finset.subset_univ (simGreedy v alg2 tb β B x D b))
    (fun a _ ha => hzero a ha)]
  have hsg := simGreedy_eq v tb β B x alg2 D b
  rw [← hp] at hsg
  rcases outOf_sub v alg2 h2 p.1 with hs | hs <;>
  · rw [← hsg] at hs
    refine le_trans (Finset.sum_le_sum hthr) (le_trans (Finset.sum_le_sum_of_subset_of_nonneg hs
      (fun a ha _ => le_trans (hb a).1 (inv.2.2.1 _ a ha))) ?_)
    have h1 := inv.2.1
    have h2' := inv.2.2.2.1
    first
      | (have := h1 0; have := h2' 0; linarith)
      | (have := h1 1; have := h2' 1; linarith)

lemma sub_step (htb : IsArgmaxRule v tb) (b : A → ℝ) (D : Finset A) (st : SGState A)
    (h : (∀ j, st.S j ⊆ D) ∧ st.U ⊆ D) :
    (∀ j, (sgStep v tb β B x b st).S j ⊆ D) ∧ (sgStep v tb β B x b st).U ⊆ D := by
  by_cases ht : Test v st
  · have hiU : (tb st.U st.S).1 ∈ st.U := (htb _ _ ht).1
    by_cases ha : Acc v tb β B x b st
    · rw [step_acc v tb β B x b st ht ha]
      refine ⟨fun j => ?_, fun a ha' => h.2 (Finset.mem_of_mem_erase ha')⟩
      simp only
      by_cases hjj : j = (tb st.U st.S).2
      · subst hjj; rw [Function.update_self]
        exact Finset.insert_subset (h.2 hiU) (h.1 _)
      · rw [Function.update_of_ne hjj]; exact h.1 j
    · rw [step_rej v tb β B x b st ht ha]
      exact ⟨h.1, fun a ha' => h.2 (Finset.mem_of_mem_erase ha')⟩
  · rw [step_fail v tb β B x b st ht]; exact h

lemma simGreedy_sub (alg2 : Finset A → Finset A) (h2 : ∀ S, alg2 S ⊆ S)
    (htb : IsArgmaxRule v tb) (D : Finset A) (b : A → ℝ) :
    simGreedy v alg2 tb β B x D b ⊆ D := by
  have key : ∀ n, (∀ j, ((sgStep v tb β B x b)^[n] (sgInit D B)).S j ⊆ D) ∧
      ((sgStep v tb β B x b)^[n] (sgInit D B)).U ⊆ D := by
    intro n
    induction n with
    | zero => exact ⟨fun j => by simp [sgInit], by simp [sgInit]⟩
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact sub_step v tb β B x htb b D _ ih
  intro a ha
  rw [simGreedy_eq, aug_fst] at ha
  obtain ⟨j, hj⟩ := mem_outOf v alg2 h2 _ a ha
  exact (key D.card).1 j hj

end

end BFSsg



open BFSsg in
lemma thr_congr {A : Type} [Fintype A] [DecidableEq A] (f g : (A → ℝ) → Finset A) (B : ℝ)
    (b : A → ℝ) (i : A) (h : ∀ t, f (Function.update b i t) = g (Function.update b i t)) :
    thr f B b i = thr g B b i := by
  have hb : f b = g b := by have := h (b i); rwa [Function.update_eq_self] at this
  unfold thr
  rw [hb]
  simp_rw [h]

open BFSsg in
theorem solution {A : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    (v : Finset A → ℝ) (alg1 : Finset A → (A → ℝ) → Finset A) (alg2 : Finset A → Finset A)
    (tb : Finset A → (Fin 2 → Finset A) → A × Fin 2) (B : ℝ)
    (hv : IsValuation v) (h1 : IsCostLocal alg1) (h2 : IsUnconstrainedTwoApprox v alg2)
    (htb : IsArgmaxRule v tb) (hB : 0 < B) :
    ∀ ω : Option (Finset A),
      IsTruthful (genSmMain v alg1 alg2 tb B ω) B ∧
        IsIR (genSmMain v alg1 alg2 tb B ω) B ∧
        IsBudgetFeasible (genSmMain v alg1 alg2 tb B ω) B := by
  have h2' : ∀ S, alg2 S ⊆ S := fun S => (h2 S).1
  intro ω
  cases ω with
  | none =>
    have hf : genSmMain v alg1 alg2 tb B none = fun _ => {istar v} := rfl
    rw [hf]
    have hmono : IsMonotoneRule (fun _ : A → ℝ => ({istar v} : Finset A)) B :=
      fun _ _ _ _ _ _ h => h
    obtain ⟨hT, hI⟩ := lemma_2_4 _ B hB hmono
    refine ⟨hT, hI, fun b hb => ?_⟩
    rw [Finset.sum_eq_single (istar v)]
    · unfold thr
      rw [if_pos (Finset.mem_singleton_self _)]
      have hne : ({t : ℝ | t ∈ Set.Icc (b (istar v)) B ∧
          istar v ∈ (fun _ : A → ℝ => ({istar v} : Finset A)) (Function.update b (istar v) t)}).Nonempty :=
        ⟨b (istar v), ⟨le_refl _, (hb _).2⟩, Finset.mem_singleton_self _⟩
      apply csSup_le hne
      intro t ht; exact ht.1.2
    · intro i _ hi
      unfold thr
      rw [if_neg (by simpa using hi)]
    · intro h; exact absurd (Finset.mem_univ _) h
  | some A₁ =>
    have hf : genSmMain v alg1 alg2 tb B (some A₁) = sampleThenGreedy v alg1 alg2 tb beta B A₁ :=
      rfl
    rw [hf]
    -- for an agent outside the sample, the rate `x` does not depend on its bid
    have hx : ∀ (b : A → ℝ) (i : A) (t : ℝ), i ∉ A₁ →
        alg1 A₁ (Function.update b i t) = alg1 A₁ b := by
      intro b i t hi
      apply h1
      intro j hj
      rw [Function.update_of_ne (fun e => hi (by rw [← e]; exact hj))]
    have heq : ∀ (b : A → ℝ) (i : A), i ∉ A₁ → ∀ t,
        sampleThenGreedy v alg1 alg2 tb beta B A₁ (Function.update b i t) =
          simGreedy v alg2 tb beta B (v (alg1 A₁ b)) (univ \ A₁) (Function.update b i t) := by
      intro b i hi t
      unfold sampleThenGreedy
      rw [hx b i t hi]
    have hsub : ∀ b : A → ℝ, sampleThenGreedy v alg1 alg2 tb beta B A₁ b ⊆ univ \ A₁ :=
      fun b => simGreedy_sub v tb beta B _ alg2 h2' htb _ b
    have hmono : IsMonotoneRule (sampleThenGreedy v alg1 alg2 tb beta B A₁) B := by
      intro b a t hb ht0 hta ha
      have haD : a ∉ A₁ := by
        have := hsub b ha; simp at this; exact this
      rw [heq b a haD t]
      have ha' : a ∈ simGreedy v alg2 tb beta B (v (alg1 A₁ b)) (univ \ A₁) b := ha
      exact sg_mono v tb beta B _ alg2 h2' htb hB.le _ b a t hb ht0 hta ha'
    obtain ⟨hT, hI⟩ := lemma_2_4 _ B hB hmono
    refine ⟨hT, hI, fun b hb => ?_⟩
    have hbf := sg_bf v tb beta B (v (alg1 A₁ b)) alg2 h2' htb hB.le (univ \ A₁) b hb
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_)) hbf
    by_cases hi : i ∈ A₁
    · have n1 : i ∉ sampleThenGreedy v alg1 alg2 tb beta B A₁ b := by
        intro hh; have := hsub b hh; simp at this; exact this hi
      have n2 : i ∉ simGreedy v alg2 tb beta B (v (alg1 A₁ b)) (univ \ A₁) b := n1
      unfold thr; rw [if_neg n1, if_neg n2]
    · exact thr_congr _ _ B b i (heq b i hi)
