-- Prove2me | solution 1 for Erdos287.greedy_omissions_give_sharp_mass_bounds
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T06:27:55.453682+00:00
-- url     : https://prove2.me/submissions/494f0ef2-eeee-4355-acfe-d991f1e14b01

import Mathlib

open Finset

set_option autoImplicit false

private theorem left_cover (S : Finset ℕ) :
    ∃ A ⊆ S, (∀ n ∈ A, n + 1 ∉ A) ∧
      (∀ n ∈ S, n ∈ A ∨ ∃ a ∈ A, a + 1 = n) := by
  refine S.strongInductionOn ?_
  intro V ih
  by_cases hn : V.Nonempty
  · let a := V.min' hn
    let T := (V.erase a).erase (a + 1)
    have ha : a ∈ V := V.min'_mem hn
    have hsub : T ⊆ V := (erase_subset _ _).trans (erase_subset _ _)
    have hlt : T ⊂ V := Finset.ssubset_of_subset_of_ssubset (erase_subset _ _) (erase_ssubset ha)
    obtain ⟨A, hAT, hAnext, hcover⟩ := ih T hlt
    have ha' : a + 1 ∉ A := by
      intro hh
      exact (mem_erase.mp (hAT hh)).1 rfl
    refine ⟨insert a A, insert_subset ha (hAT.trans hsub), ?_, ?_⟩
    · intro n hn' hh
      rcases mem_insert.mp hn' with rfl | hnA
      · rcases mem_insert.mp hh with he | hA
        · omega
        · exact ha' hA
      · have hle := V.min'_le n (hsub (hAT hnA))
        rcases mem_insert.mp hh with he | hA
        · change a ≤ n at hle
          omega
        · exact hAnext n hnA hA
    · intro n hnV
      by_cases he : n = a
      · exact Or.inl (mem_insert.mpr (Or.inl he))
      by_cases he' : n = a + 1
      · exact Or.inr ⟨a, mem_insert_self a A, he'.symm⟩
      have hnT : n ∈ T := mem_erase.mpr ⟨he', mem_erase.mpr ⟨he, hnV⟩⟩
      rcases hcover n hnT with hA | ⟨j, hj, hstep⟩
      · exact Or.inl (mem_insert_of_mem hA)
      · exact Or.inr ⟨j, mem_insert_of_mem hj, hstep⟩
  · rw [not_nonempty_iff_eq_empty] at hn
    subst V
    simp

private def eligible (I H R : Finset ℕ) : Finset ℕ :=
  ((I \ H) \ R).filter (fun n => n + 1 ∉ H ∧ (n = 0 ∨ n - 1 ∉ H))

private theorem bounds_from_left_cover (I H R : Finset ℕ) (w : ℕ → ℚ)
    (hH : H ⊆ I) (hdisj : Disjoint H R)
    (hsep : ∀ n ∈ H, n + 1 ∉ H)
    (hw : ∀ a ∈ I, ∀ b ∈ I, a ≤ b → w b ≤ w a)
    (hnonneg : ∀ n ∈ I, 0 ≤ w n)
    (A : Finset ℕ) (hAE : A ⊆ eligible I H R) (hAsep : ∀ n ∈ A, n + 1 ∉ A)
    (hcov : ∀ n ∈ eligible I H R, n ∈ A ∨ ∃ a ∈ A, a + 1 = n) :
    (H ∪ A) ⊆ I ∧ Disjoint (H ∪ A) R ∧
      (∀ n ∈ H ∪ A, n + 1 ∉ H ∪ A) ∧
      ∀ T : Finset ℕ, H ⊆ T → T ⊆ I → Disjoint T R →
        (∀ n ∈ T, n + 1 ∉ T) →
        (∑ n ∈ I \ (H ∪ A), w n) ≤ (∑ n ∈ I \ T, w n) ∧
          (∑ n ∈ I \ T, w n) ≤ ∑ n ∈ I \ H, w n := by
  let E := ((I \ H) \ R).filter (fun n => n + 1 ∉ H ∧ (n = 0 ∨ n - 1 ∉ H))
  change A ⊆ E at hAE
  change ∀ n ∈ E, n ∈ A ∨ ∃ a ∈ A, a + 1 = n at hcov
  let G := H ∪ A
  have hEI : E ⊆ I := fun n hn => (mem_sdiff.mp (mem_sdiff.mp (mem_filter.mp hn).1).1).1
  have hAI : A ⊆ I := hAE.trans hEI
  have hHA : Disjoint H A := by
    refine disjoint_left.mpr fun n hn hna => ?_
    exact (mem_sdiff.mp (mem_sdiff.mp (mem_filter.mp (hAE hna)).1).1).2 hn
  have hAR : Disjoint A R := by
    exact disjoint_left.mpr fun _ ha hr => (mem_sdiff.mp (mem_filter.mp (hAE ha)).1).2 hr
  have hGI : G ⊆ I := union_subset hH hAI
  refine ⟨hGI, disjoint_union_left.mpr ⟨hdisj, hAR⟩, ?_, ?_⟩
  · intro n hn hn'
    rcases mem_union.mp hn with h | h <;> rcases mem_union.mp hn' with h' | h'
    · exact hsep n h h'
    · have ht := (mem_filter.mp (hAE h')).2.2
      rcases ht with hz | hm
      · omega
      · exact hm (by simpa only [Nat.add_sub_cancel] using h)
    · exact (mem_filter.mp (hAE h)).2.1 h'
    · exact hAsep n h h'
  · intro T hHT hTI hTR hTsep
    let O := T \ H
    have hOE : O ⊆ E := by
      intro n hn
      obtain ⟨hnT, hnH⟩ := mem_sdiff.mp hn
      refine mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨hTI hnT, hnH⟩,
        fun hnR => disjoint_left.mp hTR hnT hnR⟩, fun h => hTsep n hnT (hHT h), ?_⟩
      by_cases hz : n = 0
      · exact Or.inl hz
      · refine Or.inr fun h => ?_
        have eq : n - 1 + 1 = n := by omega
        exact hTsep (n - 1) (hHT h) (eq ▸ hnT)
    let g (n : ℕ) := if n ∈ A then n else n - 1
    have hg (n : ℕ) (hn : n ∈ O) : g n ∈ A ∧ g n ≤ n ∧ n ≤ g n + 1 := by
      by_cases hnA : n ∈ A
      · simp [g, hnA]
      · rcases hcov n (hOE hn) with hh | ⟨a, ha, hstep⟩
        · exact (hnA hh).elim
        · have he : g n = a := by simp only [g, if_neg hnA]; omega
          rw [he]
          exact ⟨ha, by omega, by omega⟩
    have hinj : Set.InjOn g (↑O : Set ℕ) := by
      intro n hn k hk hnk
      have hn' := hg n hn
      have hk' := hg k hk
      by_contra he
      rcases lt_or_gt_of_ne he with hlt | hlt
      · have hsucc : n + 1 = k := by omega
        exact hTsep n (mem_sdiff.mp hn).1 (hsucc ▸ (mem_sdiff.mp hk).1)
      · have hsucc : k + 1 = n := by omega
        exact hTsep k (mem_sdiff.mp hk).1 (hsucc ▸ (mem_sdiff.mp hn).1)
    have himage : O.image g ⊆ A := by
      intro n hn
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hn
      exact (hg j hj).1
    have hweights : (∑ n ∈ O, w n) ≤ ∑ n ∈ A, w n := calc
      _ ≤ ∑ n ∈ O, w (g n) := sum_le_sum fun n hn =>
        hw (g n) (hAI (hg n hn).1) n (hTI (mem_sdiff.mp hn).1) (hg n hn).2.1
      _ = ∑ n ∈ O.image g, w n := (sum_image hinj).symm
      _ ≤ ∑ n ∈ A, w n := sum_le_sum_of_subset_of_nonneg himage
        (fun n hn _ => hnonneg n (hAI hn))
    have hsplit := sum_sdiff (f := w) hHT
    have hGsum : (∑ n ∈ G, w n) = (∑ n ∈ H, w n) + ∑ n ∈ A, w n := sum_union hHA
    have htI := sum_sdiff (f := w) hTI
    have hgI := sum_sdiff (f := w) hGI
    refine ⟨?_, sum_le_sum_of_subset_of_nonneg ?_ (fun n hn _ => hnonneg n (mem_sdiff.mp hn).1)⟩
    · change (∑ n ∈ O, w n) + (∑ n ∈ H, w n) = ∑ n ∈ T, w n at hsplit
      linarith only [hweights, hsplit, hGsum, htI, hgI]
    · intro n hn
      exact mem_sdiff.mpr ⟨(mem_sdiff.mp hn).1, fun hin => (mem_sdiff.mp hn).2 (hHT hin)⟩


/-- Greedy omission from left to right gives the exact minimum retained mass
under forced omissions, forced inclusions, and no consecutive omissions. -/
theorem solution (I H R : Finset ℕ) (w : ℕ → ℚ)
    (hH : H ⊆ I) (hdisj : Disjoint H R)
    (hsep : ∀ n ∈ H, n + 1 ∉ H)
    (hw : ∀ a ∈ I, ∀ b ∈ I, a ≤ b → w b ≤ w a)
    (hnonneg : ∀ n ∈ I, 0 ≤ w n) :
    ∃ G : Finset ℕ, H ⊆ G ∧ G ⊆ I ∧ Disjoint G R ∧
      (∀ n ∈ G, n + 1 ∉ G) ∧
      ∀ T : Finset ℕ, H ⊆ T → T ⊆ I → Disjoint T R →
        (∀ n ∈ T, n + 1 ∉ T) →
        (∑ n ∈ I \ G, w n) ≤ (∑ n ∈ I \ T, w n) ∧
          (∑ n ∈ I \ T, w n) ≤ ∑ n ∈ I \ H, w n := by
  obtain ⟨A, hAE, hAsep, hcov⟩ := left_cover (eligible I H R)
  exact ⟨H ∪ A, subset_union_left,
    bounds_from_left_cover I H R w hH hdisj hsep hw hnonneg A hAE hAsep hcov⟩

