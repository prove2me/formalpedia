-- Prove2me | solution 1 for ExactLearningSeparation678.Randomized.Supplement.proposition_4_8
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T21:40:18.853245+00:00
-- url     : https://prove2.me/submissions/d39ba1f2-7fbd-4e6e-83a8-a82a7210ad6b

import Definitions.Def_ExactLearningSeparation678_Randomized_Supplement_Teaching

open Classical
set_option autoImplicit false

open ExactLearningSeparation678.Randomized.Supplement QAlgorithms.Learning

theorem ELS48_fetdAt_le (ι : Type) [Fintype ι] [DecidableEq ι] (C : Finset (ι → Bool))
    (h : ι → Bool) : fetdAt C h ≤ (etd C : ℝ) := by
  by_cases hC : C.Nonempty
  · -- choose a minimal specifying set
    have hne : {k : ℕ | ∃ S : Finset ι, S.card = k ∧
        (C.filter fun c => ∀ i ∈ S, c i = h i).card ≤ 1}.Nonempty := by
      refine ⟨_, Finset.univ, rfl, ?_⟩
      apply Finset.card_le_one.2
      intro a ha b hb
      simp only [Finset.mem_filter, Finset.mem_univ, forall_true_left] at ha hb
      funext i; rw [ha.2 i, hb.2 i]
    obtain ⟨S, hScard, hSfil⟩ := Nat.sInf_mem hne
    have hSet : S.card = etdAt C h := by unfold etdAt; convert hScard
    set F := C.filter fun c => ∀ i ∈ S, c i = h i with hF
    -- choose the exempt concept
    obtain ⟨cs, hcsC, hcsF⟩ : ∃ cs ∈ C, ∀ c ∈ F, c = cs := by
      by_cases hFn : F.Nonempty
      · obtain ⟨a, ha⟩ := hFn
        refine ⟨a, (Finset.mem_filter.1 ha).1, fun c hc => ?_⟩
        exact Finset.card_le_one.1 hSfil c hc a ha
      · obtain ⟨a, ha⟩ := hC
        refine ⟨a, ha, fun c hc => ?_⟩
        exact absurd ⟨c, hc⟩ hFn
    let w : ι → ℝ := fun i => if i ∈ S then 1 else 0
    have hw0 : ∀ i, 0 ≤ w i := fun i => by simp only [w]; split_ifs <;> norm_num
    have hfeas : IsFetdFeasible C h (cs, w) := by
      refine ⟨hcsC, hw0, ?_⟩
      intro c hc hne'
      have hnotF : c ∉ F := fun hcF => hne' (hcsF c hcF)
      simp only [hF, Finset.mem_filter, not_and, not_forall] at hnotF
      obtain ⟨i0, hi0S, hi0⟩ := hnotF hc
      have hmem : i0 ∈ Finset.univ.filter (fun i => c i ≠ h i) := by simp [hi0]
      have := Finset.single_le_sum (f := w) (fun i _ => hw0 i) hmem
      simpa [w, hi0S] using this
    have hbdd : BddBelow (Set.range fun p : {p : (ι → Bool) × (ι → ℝ) // IsFetdFeasible C h p} =>
        ∑ i, p.1.2 i) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨p, rfl⟩
      exact Finset.sum_nonneg (fun i _ => p.2.2.1 i)
    have h1 : fetdAt C h ≤ ∑ i, w i :=
      ciInf_le hbdd (⟨(cs, w), hfeas⟩ : {p : (ι → Bool) × (ι → ℝ) // IsFetdFeasible C h p})
    have h2 : ∑ i, w i = (S.card : ℝ) := by
      simp [w]
    have h3 : etdAt C h ≤ etd C := by
      unfold etd
      exact Finset.le_sup (f := fun h => etdAt C h) (by simp)
    have h3' : ((etdAt C h : ℕ) : ℝ) ≤ (etd C : ℝ) := by exact_mod_cast h3
    rw [h2, hSet] at h1
    linarith
  · have hCe : C = ∅ := Finset.not_nonempty_iff_eq_empty.1 hC
    have hemp : IsEmpty {p : (ι → Bool) × (ι → ℝ) // IsFetdFeasible C h p} :=
      ⟨fun p => by have := p.2.1; simp [hCe] at this⟩
    have : fetdAt C h = 0 := by
      unfold fetdAt
      exact Real.iInf_of_isEmpty _
    rw [this]; positivity

theorem solution (ι : Type) [Fintype ι] [DecidableEq ι] (C : Finset (ι → Bool)) :
    fetd C ≤ (etd C : ℝ) := by
  unfold fetd
  exact ciSup_le (fun h => ELS48_fetdAt_le ι C h)
