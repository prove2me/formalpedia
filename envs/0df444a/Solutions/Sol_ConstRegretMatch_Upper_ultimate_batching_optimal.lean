-- Prove2me | solution 1 for ConstRegretMatch.Upper.ultimate_batching_optimal
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T22:59:03.938682+00:00
-- url     : https://prove2.me/submissions/3522ffad-4f09-4abe-ae26-f960832ac76e

import Mathlib
import Definitions.Def_ConstRegretMatch_Upper_Network
import Definitions.Def_ConstRegretMatch_Upper_SPP
import Definitions.Def_ConstRegretMatch_Upper_Arrivals
import Definitions.Def_ConstRegretMatch_Upper_Policy

open ConstRegretMatch.Upper

namespace CRMUBSol

variable {n d : ℕ}

/-- Every feasible `y` lies in the box `{0,…,∑ u}^d`. -/
lemma feas_le_sum (N : MatchingNetwork n d) (u : Fin n → ℕ) (y : Fin d → ℕ)
    (hy : StaticFeasible N u y) (m : Fin d) : y m ≤ ∑ i, u i := by
  obtain ⟨i, hi⟩ : (N.A m).Nonempty := by
    have := N.two_le_card m
    exact Finset.card_pos.mp (by omega)
  have h1 : y m ≤ ∑ m', N.inc i m' * y m' := by
    have : N.inc i m * y m = y m := by simp [MatchingNetwork.inc, hi]
    rw [← this]
    exact Finset.single_le_sum (f := fun m' => N.inc i m' * y m') (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ m)
  exact h1.trans ((hy i).trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ i)))

lemma le_staticOpt (N : MatchingNetwork n d) (r : Fin d → ℝ) (u : Fin n → ℕ) (y : Fin d → ℕ)
    (hy : StaticFeasible N u y) : ∑ m, r m * (y m : ℝ) ≤ staticOpt N r u := by
  unfold staticOpt
  apply Finset.le_max'
  apply Finset.mem_insert_of_mem
  apply Finset.mem_image_of_mem
  rw [Finset.mem_filter]
  refine ⟨?_, hy⟩
  rw [Fintype.mem_piFinset]
  intro m
  rw [Finset.mem_range]
  exact Nat.lt_succ_of_le (feas_le_sum N u y hy m)

lemma exists_opt (N : MatchingNetwork n d) (r : Fin d → ℝ) (u : Fin n → ℕ) :
    ∃ y : Fin d → ℕ, StaticFeasible N u y ∧ ∑ m, r m * (y m : ℝ) = staticOpt N r u := by
  have hmem := Finset.max'_mem (insert 0 (((Fintype.piFinset
      (fun _ : Fin d => Finset.range (∑ i, u i + 1))).filter
      (fun y => StaticFeasible N u y)).image (fun y => ∑ m, r m * (y m : ℝ))))
    (Finset.insert_nonempty _ _)
  rw [Finset.mem_insert] at hmem
  rcases hmem with h | h
  · refine ⟨0, fun i => by simp, ?_⟩
    unfold staticOpt
    rw [h]
    simp
  · rw [Finset.mem_image] at h
    obtain ⟨y, hy, hyv⟩ := h
    exact ⟨y, (Finset.mem_filter.mp hy).2, hyv⟩

lemma feas_zero (N : MatchingNetwork n d) (y : Fin d → ℕ) (hy : StaticFeasible N 0 y) :
    y = 0 := by
  funext m
  have := feas_le_sum N 0 y hy m
  simpa using this

lemma arrivals_mono (ω : ℕ → Fin n) {s t : ℕ} (h : t ≤ s) (i : Fin n) :
    arrivals ω t i ≤ arrivals ω s i := by
  unfold arrivals arrivalsBetween
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  exact Finset.Ico_subset_Ico_right h

lemma arrivals_congr (ω ω' : ℕ → Fin n) (t : ℕ) (h : ∀ s < t, ω s = ω' s) :
    arrivals ω t = arrivals ω' t := by
  funext i
  unfold arrivals arrivalsBetween
  congr 1
  apply Finset.filter_congr
  intro x hx
  rw [Finset.mem_Ico] at hx
  rw [h x hx.2]

lemma expect_mono (lam : Fin n → ℝ) (hlam : IsArrivalRates lam) (t : ℕ)
    (F G : (ℕ → Fin n) → ℝ) (h : ∀ ω, F ω ≤ G ω) : expect lam t F ≤ expect lam t G := by
  unfold expect
  split_ifs with hn
  · apply Finset.sum_le_sum
    intro w _
    apply mul_le_mul_of_nonneg_left (h _)
    exact Finset.prod_nonneg (fun s _ => (hlam.1 _).le)
  · exact le_refl _

end CRMUBSol

open CRMUBSol in
theorem solution {n d : ℕ} (N : MatchingNetwork n d) (r : Fin d → ℝ)
    (hr : IsMatchValues r) (lam : Fin n → ℝ) (hlam : IsArrivalRates lam) (t : ℕ) :
    (∀ D : Policy n d, IsAdmissible N D → valueOf lam r D t ≤ Rstar N lam r t) ∧
      ∃ D : Policy n d, IsAdmissible N D ∧ valueOf lam r D t = Rstar N lam r t := by
  constructor
  · intro D hD
    unfold valueOf Rstar
    apply expect_mono lam hlam
    intro ω
    exact le_staticOpt N r _ _ (fun i => hD.2.2.2 t ω i)
  · choose opt hopt using fun u => exists_opt N r u
    let D : Policy n d := fun s ω => if s < t then 0 else opt (arrivals ω t)
    refine ⟨D, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · intro ω
      by_cases ht : 0 < t
      · simp [D, ht]
      · have ht0 : t = 0 := by omega
        have harr : arrivals ω t = 0 := by
          funext i; simp [ht0, arrivals, arrivalsBetween]
        have := feas_zero N _ (harr ▸ (hopt (arrivals ω t)).1)
        simp only [D, ht, if_false]
        rw [harr]
        exact this
    · intro s ω m
      simp only [D]
      split_ifs with h1 h2 h2
      · exact le_refl _
      · exact Nat.zero_le _
      · omega
      · exact le_refl _
    · intro s ω ω' h
      simp only [D]
      split_ifs with h1
      · rfl
      · rw [arrivals_congr ω ω' t (fun k hk => h k (by omega))]
    · intro s ω i
      simp only [D]
      split_ifs with h1
      · simp
      · exact ((hopt (arrivals ω t)).1 i).trans (arrivals_mono ω (by omega) i)
    · unfold valueOf Rstar
      congr 1
      funext ω
      simp only [D, lt_irrefl, if_false]
      exact (hopt _).2
