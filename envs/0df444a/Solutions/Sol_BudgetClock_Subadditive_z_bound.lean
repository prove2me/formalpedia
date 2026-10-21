-- Prove2me | solution 1 for BudgetClock.Subadditive.z_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T20:49:23.436263+00:00
-- url     : https://prove2.me/submissions/ce6fdf55-dcaa-4079-a19e-ff5af8785479

import Mathlib
import Definitions.Def_BudgetClock_Subadditive_Mechanism

set_option autoImplicit false
open BudgetClock.Subadditive

lemma better_ge_left {n : ℕ} (v : Finset (Fin n) → ℝ) (S₁ S₂ : Finset (Fin n)) :
    v S₁ ≤ v (better v S₁ S₂) := by
  unfold better
  split_ifs with h
  · exact h.le
  · exact le_rfl

lemma better_ge_right {n : ℕ} (v : Finset (Fin n) → ℝ) (S₁ S₂ : Finset (Fin n)) :
    v S₂ ≤ v (better v S₁ S₂) := by
  unfold better
  split_ifs with h
  · exact le_rfl
  · exact not_lt.1 h

lemma better_mem {n : ℕ} (v : Finset (Fin n) → ℝ) (S₁ S₂ : Finset (Fin n)) :
    better v S₁ S₂ = S₁ ∨ better v S₁ S₂ = S₂ := by
  unfold better
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

section
variable {n : ℕ} (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ)
  (alg : ℕ → Finset (Fin n) → Finset (Fin n))

def Cnd (s : State n) : Prop := (s.A \ (s.Sprev ∪ s.Scurr)).Nonempty

lemma run_iter (F : ℕ) : ∀ s : State n, ∃ m ≤ F, run v c B alg F s = (phase v c B alg)^[m] s ∧
    (∀ j < m, Cnd ((phase v c B alg)^[j] s)) ∧
    (m < F → ¬ Cnd ((phase v c B alg)^[m] s)) := by
  induction F with
  | zero =>
    intro s
    exact ⟨0, le_rfl, by simp [run], by simp, by simp⟩
  | succ F ih =>
    intro s
    by_cases hc : Cnd s
    · obtain ⟨m, hmF, hrun, hcond, hstop⟩ := ih (phase v c B alg s)
      refine ⟨m + 1, by omega, ?_, ?_, ?_⟩
      · have : run v c B alg (F + 1) s = run v c B alg F (phase v c B alg s) := by
          have hc' : (s.A \ (s.Sprev ∪ s.Scurr)).Nonempty := hc
          simp only [run, if_pos hc']
        rw [this, hrun, Function.iterate_succ_apply]
      · intro j hj
        rcases j with _ | j
        · simpa using hc
        · rw [Function.iterate_succ_apply]
          exact hcond j (by omega)
      · intro hlt
        rw [Function.iterate_succ_apply]
        exact hstop (by omega)
    · refine ⟨0, by omega, ?_, by simp, ?_⟩
      · have hc' : ¬ (s.A \ (s.Sprev ∪ s.Scurr)).Nonempty := hc
        simp only [run, if_neg hc']; rfl
      · intro _; simpa using hc

noncomputable def traj (j : ℕ) : State n := (phase v c B alg)^[j] (initState n B)

lemma traj_succ (j : ℕ) : traj v c B alg (j + 1) = phase v c B alg (traj v c B alg j) := by
  unfold traj; rw [Function.iterate_succ_apply']

lemma traj_t (j : ℕ) : (traj v c B alg j).t = j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [traj_succ]; show (traj v c B alg j).t + 1 = j + 1; rw [ih]

def Good (S : Finset (Fin n)) : Prop := S = ∅ ∨ ∃ t X, S = alg t X

lemma traj_good (j : ℕ) :
    Good alg (traj v c B alg j).Sprev ∧ Good alg (traj v c B alg j).Scurr := by
  induction j with
  | zero => exact ⟨Or.inl rfl, Or.inl rfl⟩
  | succ j ih =>
    rw [traj_succ]
    refine ⟨?_, Or.inr ⟨_, _, rfl⟩⟩
    show Good alg (better v (traj v c B alg j).Sprev (traj v c B alg j).Scurr)
    rcases better_mem v (traj v c B alg j).Sprev (traj v c B alg j).Scurr with h | h
    · rw [h]; exact ih.1
    · rw [h]; exact ih.2

noncomputable def val (s : State n) : ℝ := v (better v s.Sprev s.Scurr)

lemma val_phase (s : State n) : val v s ≤ val v (phase v c B alg s) := by
  unfold val
  have h1 : (phase v c B alg s).Sprev = better v s.Sprev s.Scurr := rfl
  rw [h1]
  exact better_ge_left v _ _

lemma val_traj_mono {j j' : ℕ} (h : j ≤ j') : val v (traj v c B alg j) ≤ val v (traj v c B alg j') := by
  have : Monotone (fun j => val v (traj v c B alg j)) := by
    apply monotone_nat_of_le_succ
    intro j
    simp only [traj_succ]
    exact val_phase v c B alg _
  exact this h

lemma good_bound (hv : ∀ S, 0 ≤ v S) (halg : IsTwoApproxOracle v alg) {S Y : Finset (Fin n)}
    (hS : Good alg S) (hY : Y ⊆ S) : v Y ≤ 2 * v S := by
  rcases hS with rfl | ⟨t, X, rfl⟩
  · have : Y = ∅ := Finset.subset_empty.1 hY
    subst this
    have := hv ∅
    linarith
  · obtain ⟨h1, h2, h3⟩ := halg t X
    exact h3 Y (hY.trans h1) ((Finset.card_le_card hY).trans h2)

lemma traj_Z (hB : 0 < B) (Z : Finset (Fin n)) (k : ℕ) (hZc : ∀ i ∈ Z, c i ≤ B / (k : ℝ)) :
    ∀ j ≤ k, Z ⊆ (traj v c B alg j).A := by
  intro j
  induction j with
  | zero => intro _; intro i _; simp [traj, initState]
  | succ j ih =>
    intro hj
    rw [traj_succ]
    intro i hi
    have hi' := ih (by omega) hi
    show i ∈ (traj v c B alg j).A \ _
    rw [Finset.mem_sdiff]
    refine ⟨hi', ?_⟩
    intro hmem
    rw [Finset.mem_filter] at hmem
    have hlt := hmem.2
    rw [traj_t] at hlt
    have hk : (((j + 1 : ℕ)) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hj
    have hj0 : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
    have : B / (k : ℝ) ≤ B / ((j + 1 : ℕ) : ℝ) := div_le_div_of_nonneg_left hB.le hj0 hk
    have := hZc i hi
    linarith

end

theorem solution {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : ∀ S, 0 ≤ v S) (hsub : IsSubadditive v)
    (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i) (B : ℝ) (hB : 0 < B)
    (alg : ℕ → Finset (Fin n) → Finset (Fin n)) (halg : IsTwoApproxOracle v alg)
    (F : ℕ) (Z : Finset (Fin n)) (hZ : 1 ≤ Z.card) (hZF : Z.card ≤ F)
    (hZc : ∀ i ∈ Z, c i ≤ B / (Z.card : ℝ)) :
    v Z ≤ 4 * v (mechanism4 v c B alg F).1 := by
  set k := Z.card with hk
  have hsplit : ∀ S : Finset (Fin n), v Z ≤ v (Z ∩ S) + v (Z \ S) := by
    intro S
    have : Z = (Z ∩ S) ∪ (Z \ S) := by
      ext x; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
    calc v Z = v ((Z ∩ S) ∪ (Z \ S)) := by rw [← this]
      _ ≤ _ := hsub _ _
  obtain ⟨m, hmF, hrun, hcond, hstop⟩ := run_iter v c B alg F (initState n B)
  have hfinal : (mechanism4 v c B alg F).1 = better v (traj v c B alg m).Sprev (traj v c B alg m).Scurr := by
    show better v (run v c B alg F (initState n B)).Sprev (run v c B alg F (initState n B)).Scurr = _
    rw [hrun]; rfl
  rw [hfinal]
  change v Z ≤ 4 * val v (traj v c B alg m)
  have hZsub := traj_Z v c B alg hB Z k hZc
  by_cases hmk : m < k
  · have hnc := hstop (by omega)
    have hnc' : ¬ Cnd (traj v c B alg m) := hnc
    unfold Cnd at hnc'
    rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hnc'
    have hZA := hZsub m hmk.le
    have h1 : Z ∩ (traj v c B alg m).Sprev ⊆ (traj v c B alg m).Sprev := Finset.inter_subset_right
    have h2 : Z \ (traj v c B alg m).Sprev ⊆ (traj v c B alg m).Scurr := by
      intro x hx
      rw [Finset.mem_sdiff] at hx
      have := hnc' (hZA hx.1)
      rw [Finset.mem_union] at this
      tauto
    have hg := traj_good v c B alg m
    have e1 := good_bound v alg hv halg hg.1 h1
    have e2 := good_bound v alg hv halg hg.2 h2
    have l1 := better_ge_left v (traj v c B alg m).Sprev (traj v c B alg m).Scurr
    have l2 := better_ge_right v (traj v c B alg m).Sprev (traj v c B alg m).Scurr
    have := hsplit (traj v c B alg m).Sprev
    unfold val
    linarith
  · push_neg at hmk
    obtain ⟨k', hk'⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hZA := hZsub k le_rfl
    have hg := traj_good v c B alg k
    have hdef : traj v c B alg k = phase v c B alg (traj v c B alg k') := by
      rw [hk']; exact traj_succ v c B alg k'
    have hScurr : (traj v c B alg k).Scurr =
        alg k ((traj v c B alg k).A \ (traj v c B alg k).Sprev) := by
      have h1 : (traj v c B alg k).Scurr = alg ((traj v c B alg k').t + 1)
          ((phase v c B alg (traj v c B alg k')).A \ (phase v c B alg (traj v c B alg k')).Sprev) := by
        rw [hdef]; rfl
      rw [h1, traj_t, ← hdef, hk']
    have h1 : Z ∩ (traj v c B alg k).Sprev ⊆ (traj v c B alg k).Sprev := Finset.inter_subset_right
    have e1 := good_bound v alg hv halg hg.1 h1
    have hX : Z \ (traj v c B alg k).Sprev ⊆ (traj v c B alg k).A \ (traj v c B alg k).Sprev :=
      Finset.sdiff_subset_sdiff hZA le_rfl
    obtain ⟨_, _, h3⟩ := halg k ((traj v c B alg k).A \ (traj v c B alg k).Sprev)
    have e2 : v (Z \ (traj v c B alg k).Sprev) ≤ 2 * v (traj v c B alg k).Scurr := by
      rw [hScurr]
      exact h3 _ hX ((Finset.card_le_card Finset.sdiff_subset).trans le_rfl)
    have l1 := better_ge_left v (traj v c B alg k).Sprev (traj v c B alg k).Scurr
    have l2 := better_ge_right v (traj v c B alg k).Sprev (traj v c B alg k).Scurr
    have hmono := val_traj_mono v c B alg hmk
    have := hsplit (traj v c B alg k).Sprev
    unfold val at hmono ⊢
    linarith
