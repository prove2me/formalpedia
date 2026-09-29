-- Prove2me | solution 1 for FoundationsML.Boosting.rademacher_complexity_conv_hull
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:14:53.303854+00:00
-- url     : https://prove2.me/submissions/a30cdf09-0528-4638-bba0-dc032fdd9d6a

import Mathlib
import Definitions.Def_FoundationsML_Boosting_EmpiricalRademacherComplexity
import Definitions.Def_FoundationsML_Boosting_ConvHull

namespace FoundationsML.Boosting

open Classical in
/-- Value of the Prop-indexed real supremum. -/
lemma aux_rchull_gval {α : Type*} (S : Set α) (F : α → ℝ) (x : α) :
    (⨆ (_ : x ∈ S), F x) = if x ∈ S then F x else 0 := by
  by_cases hx : x ∈ S
  · rw [if_pos hx, ciSup_pos hx]
  · rw [if_neg hx]
    have : IsEmpty (x ∈ S) := ⟨hx⟩
    exact Real.iSup_of_isEmpty _

open Classical in
/-- Abstract comparison of bounded real suprema `⨆ x ∈ A, F x` and `⨆ x ∈ B, F x`. -/
lemma aux_rchull_biSup_eq {α : Type*} (A B : Set α) (F : α → ℝ) (hAB : A ⊆ B)
    (hdom : ∀ b ∈ B, F b ≤ 0 ∨ ∃ a ∈ A, F b ≤ F a)
    (hzero : B.Nonempty → ∃ b ∈ B, 0 ≤ F b) :
    (⨆ x ∈ A, F x) = ⨆ x ∈ B, F x := by
  set gA : α → ℝ := fun x => ⨆ (_ : x ∈ A), F x with hgA
  set gB : α → ℝ := fun x => ⨆ (_ : x ∈ B), F x with hgB
  have eA : ∀ x, gA x = if x ∈ A then F x else 0 := fun x => aux_rchull_gval A F x
  have eB : ∀ x, gB x = if x ∈ B then F x else 0 := fun x => aux_rchull_gval B F x
  show (⨆ x, gA x) = ⨆ x, gB x
  rcases isEmpty_or_nonempty α with hα | hα
  · simp
  obtain x0 := hα.some
  -- some value of gB is nonnegative
  have hB0 : ∃ y, 0 ≤ gB y := by
    by_cases hx0 : x0 ∈ B
    · obtain ⟨b, hb, hFb⟩ := hzero ⟨x0, hx0⟩
      exact ⟨b, by rw [eB, if_pos hb]; exact hFb⟩
    · exact ⟨x0, by rw [eB, if_neg hx0]⟩
  by_cases hbA : BddAbove (Set.range gA)
  · obtain ⟨M, hM⟩ := hbA
    have hMA : ∀ x, gA x ≤ M := fun x => hM ⟨x, rfl⟩
    have hbB : BddAbove (Set.range gB) := by
      refine ⟨max M 0, ?_⟩
      rintro _ ⟨x, rfl⟩
      rw [eB]
      split_ifs with hx
      · rcases hdom x hx with h | ⟨a, ha, h⟩
        · exact h.trans (le_max_right _ _)
        · have := hMA a
          rw [eA, if_pos ha] at this
          exact h.trans (this.trans (le_max_left _ _))
      · exact le_max_right _ _
    have hbA' : BddAbove (Set.range gA) := ⟨M, hM⟩
    apply le_antisymm
    · apply ciSup_le
      intro x
      by_cases hxA : x ∈ A
      · have h1 : gA x = gB x := by rw [eA, eB, if_pos hxA, if_pos (hAB hxA)]
        rw [h1]
        exact le_ciSup hbB x
      · rw [eA, if_neg hxA]
        obtain ⟨y, hy⟩ := hB0
        exact hy.trans (le_ciSup hbB y)
    · apply ciSup_le
      intro x
      by_cases hxA : x ∈ A
      · have h1 : gB x = gA x := by rw [eA, eB, if_pos hxA, if_pos (hAB hxA)]
        rw [h1]
        exact le_ciSup hbA' x
      · have h0 : 0 ≤ ⨆ x, gA x := by
          have := le_ciSup hbA' x
          rw [eA, if_neg hxA] at this
          exact this
        rw [eB]
        split_ifs with hxB
        · rcases hdom x hxB with h | ⟨a, ha, h⟩
          · exact h.trans h0
          · have := le_ciSup hbA' a
            rw [eA, if_pos ha] at this
            exact h.trans this
        · exact h0
  · have hbB : ¬ BddAbove (Set.range gB) := by
      rintro ⟨M, hM⟩
      apply hbA
      refine ⟨M, ?_⟩
      rintro _ ⟨x, rfl⟩
      rw [eA]
      split_ifs with hx
      · have := hM ⟨x, rfl⟩
        rw [eB, if_pos (hAB hx)] at this
        exact this
      · obtain ⟨y, hy⟩ := hB0
        exact hy.trans (hM ⟨y, rfl⟩)
    rw [Real.iSup_of_not_bddAbove hbA, Real.iSup_of_not_bddAbove hbB]

/-- Linearity of the Rademacher correlation functional. -/
lemma aux_rchull_lin {X : Type*} {m : ℕ} (c : Fin m → ℝ) (S : Fin m → X) {p : ℕ}
    (μ : Fin p → ℝ) (hs : Fin p → (X → ℝ)) :
    (1 / (m : ℝ)) * ∑ i : Fin m, c i * (fun x => ∑ k, μ k * hs k x) (S i)
      = ∑ k, μ k * ((1 / (m : ℝ)) * ∑ i : Fin m, c i * hs k (S i)) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  ring

end FoundationsML.Boosting

open FoundationsML.Boosting

theorem solution {X : Type*} {m : ℕ}
    (H : Set (X → ℝ)) (S : Fin m → X) :
    EmpiricalRademacherComplexity (ConvHull H) S = EmpiricalRademacherComplexity H S := by
  unfold EmpiricalRademacherComplexity
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  set c : Fin m → ℝ := fun i => if σ i then (1 : ℝ) else -1 with hc
  set F : (X → ℝ) → ℝ := fun g => (1 / (m : ℝ)) * ∑ i : Fin m, c i * g (S i) with hF
  show (⨆ g ∈ ConvHull H, F g) = ⨆ g ∈ H, F g
  symm
  apply aux_rchull_biSup_eq
  · -- H ⊆ conv H
    intro h hh
    refine ⟨1, fun _ => 1, fun _ => h, le_refl _, fun _ => zero_le_one, fun _ => hh, ?_, ?_⟩
    · simp
    · funext x; simp
  · -- domination
    rintro f ⟨p, μ, hs, hp, hμ, hsH, hsum, rfl⟩
    have hlin : F (fun x => ∑ k, μ k * hs k x) = ∑ k, μ k * F (hs k) :=
      aux_rchull_lin c S μ hs
    rw [hlin]
    have hne : (Finset.univ : Finset (Fin p)).Nonempty :=
      ⟨⟨0, hp⟩, Finset.mem_univ _⟩
    obtain ⟨k0, -, hk0⟩ := Finset.exists_max_image Finset.univ (fun k => F (hs k)) hne
    by_cases hpos : F (hs k0) ≤ 0
    · left
      apply Finset.sum_nonpos
      intro k _
      exact mul_nonpos_of_nonneg_of_nonpos (hμ k) ((hk0 k (Finset.mem_univ _)).trans hpos)
    · right
      rw [not_le] at hpos
      refine ⟨hs k0, hsH k0, ?_⟩
      calc ∑ k, μ k * F (hs k) ≤ ∑ k, μ k * F (hs k0) := by
            apply Finset.sum_le_sum
            intro k _
            exact mul_le_mul_of_nonneg_left (hk0 k (Finset.mem_univ _)) (hμ k)
        _ = (∑ k, μ k) * F (hs k0) := by rw [Finset.sum_mul]
        _ ≤ 1 * F (hs k0) := mul_le_mul_of_nonneg_right hsum hpos.le
        _ = F (hs k0) := one_mul _
  · -- zero function in conv H
    rintro ⟨f, p, μ, hs, hp, hμ, hsH, hsum, rfl⟩
    refine ⟨fun x => ∑ k, (0 : ℝ) * hs k x,
      ⟨p, fun _ => 0, hs, hp, fun _ => le_refl _, hsH, by simp, rfl⟩, ?_⟩
    simp [hF]
