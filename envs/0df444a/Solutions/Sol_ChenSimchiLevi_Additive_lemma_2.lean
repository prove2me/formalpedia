-- Prove2me | solution 1 for ChenSimchiLevi.Additive.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T00:56:21.719865+00:00
-- url     : https://prove2.me/submissions/8b7137d9-1009-4cab-bfb4-e681daa56756

import Mathlib
import Definitions.Def_ChenSimchiLevi_Additive_Model

set_option autoImplicit false

open MeasureTheory ChenSimchiLevi.Additive

theorem solution (M : Model) (hA : M.Assumptions) (hadd : M.IsAdditive)
    (t : ℕ) (ht : t ∈ Finset.Icc 1 M.T) (V : ℝ → ℝ)
    (hcont : ContinuousOn (Function.uncurry (M.gWith V t))
      (Set.univ ×ˢ Set.Icc (M.dlo t) (M.dhi t))) :
    ∃ dsel : ℝ → ℝ,
      (∀ y : ℝ, dsel y ∈ Set.Icc (M.dlo t) (M.dhi t) ∧
        IsMaxOn (M.gWith V t y) (Set.Icc (M.dlo t) (M.dhi t)) (dsel y)) ∧
      Monotone (fun y => y - dsel y) := by
  set I : Set ℝ := Set.Icc (M.dlo t) (M.dhi t) with hI
  have hne : I.Nonempty := Set.nonempty_Icc.mpr (hA.dlo_le_dhi t ht)
  have hRc : ConcaveOn ℝ I (M.R t) := hA.R_concave t ht
  -- structure of g
  have hgform : ∀ y d : ℝ, M.gWith V t y d = M.R t d - M.c t * y +
      ∫ ε, (-M.h t ((y - d) - ε.2) + V ((y - d) - ε.2)) ∂(M.μ t) := by
    intro y d
    unfold Model.gWith
    congr 1
    apply integral_congr_ae
    filter_upwards [hadd t ht] with ε hε
    have : y - (ε.1 * d + ε.2) = (y - d) - ε.2 := by rw [hε]; ring
    simp only [this]
  -- continuity of g y on I
  have hgc : ∀ y, ContinuousOn (M.gWith V t y) I := by
    intro y
    have h1 : ContinuousOn (fun d : ℝ => Function.uncurry (M.gWith V t) (y, d)) I :=
      hcont.comp (Continuous.continuousOn (by fun_prop)) (fun d hd => ⟨Set.mem_univ _, hd⟩)
    exact h1
  -- least maximiser
  have hsel : ∀ y, ∃ d, d ∈ I ∧ IsMaxOn (M.gWith V t y) I d ∧
      ∀ d', d' ∈ I → IsMaxOn (M.gWith V t y) I d' → d ≤ d' := by
    intro y
    obtain ⟨dm, hdm, hdmax⟩ := isCompact_Icc.exists_isMaxOn hne (hgc y)
    set Mset : Set ℝ := I ∩ (M.gWith V t y) ⁻¹' Set.Ici (M.gWith V t y dm) with hMset
    have hMclosed : IsClosed Mset :=
      (hgc y).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    have hMne : Mset.Nonempty := ⟨dm, hdm, Set.mem_preimage.mpr (Set.mem_Ici.mpr le_rfl)⟩
    have hMbdd : BddBelow Mset := ⟨M.dlo t, fun d hd => hd.1.1⟩
    have hleast := hMclosed.isLeast_csInf hMne hMbdd
    refine ⟨sInf Mset, hleast.1.1, ?_, ?_⟩
    · intro d hd
      have := hdmax hd
      have h2 : M.gWith V t y dm ≤ M.gWith V t y (sInf Mset) := hleast.1.2
      simp only [Set.mem_setOf_eq] at this ⊢
      linarith
    · intro d' hd' hmax'
      apply hleast.2
      refine ⟨hd', ?_⟩
      exact hmax' hdm
  choose dsel hdI hdmax hdleast using hsel
  refine ⟨dsel, fun y => ⟨hdI y, hdmax y⟩, ?_⟩
  intro y1 y2 hy
  simp only
  rcases hy.eq_or_lt with h | h
  · rw [h]
  by_contra hcon
  push_neg at hcon
  -- d2 - d1 > δ
  set δ : ℝ := y2 - y1 with hδ
  set d1 := dsel y1 with hd1
  set d2 := dsel y2 with hd2
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hgap : δ < d2 - d1 := by rw [hδ]; linarith
  have hd1I : d1 ∈ I := hdI y1
  have hd2I : d2 ∈ I := hdI y2
  set d1' := d1 + δ with hd1'
  set d2' := d2 - δ with hd2'
  have hmem : ∀ d, d1 ≤ d → d ≤ d2 → d ∈ I := fun d h1 h2 =>
    ⟨le_trans hd1I.1 h1, le_trans h2 hd2I.2⟩
  have hd1'I : d1' ∈ I := hmem _ (by rw [hd1']; linarith) (by rw [hd1']; linarith)
  have hd2'I : d2' ∈ I := hmem _ (by rw [hd2']; linarith) (by rw [hd2']; linarith)
  -- concavity: R d1 + R d2 ≤ R d1' + R d2'
  have hC : M.R t d1 + M.R t d2 ≤ M.R t d1' + M.R t d2' := by
    set lam : ℝ := δ / (d2 - d1) with hlam
    have hpos : 0 < d2 - d1 := by linarith
    have hl0 : 0 ≤ lam := by rw [hlam]; positivity
    have hl1 : lam ≤ 1 := by rw [hlam, div_le_one hpos]; linarith
    have e1 : d1' = (1 - lam) • d1 + lam • d2 := by
      simp only [smul_eq_mul, hd1', hlam]; field_simp; ring
    have e2 : d2' = lam • d1 + (1 - lam) • d2 := by
      simp only [smul_eq_mul, hd2', hlam]; field_simp; ring
    have c1 := hRc.2 hd1I hd2I (by linarith : 0 ≤ 1 - lam) hl0 (by ring)
    have c2 := hRc.2 hd1I hd2I hl0 (by linarith : 0 ≤ 1 - lam) (by ring)
    rw [← e1] at c1
    rw [← e2] at c2
    simp only [smul_eq_mul] at c1 c2
    nlinarith
  -- optimality comparisons
  have hA1 : M.gWith V t y1 d2' ≤ M.gWith V t y1 d1 := hdmax y1 hd2'I
  have hB1 : M.gWith V t y2 d1' ≤ M.gWith V t y2 d2 := hdmax y2 hd1'I
  have hu1 : y2 - d1' = y1 - d1 := by rw [hd1', hδ]; ring
  have hu2 : y1 - d2' = y2 - d2 := by rw [hd2', hδ]; ring
  rw [hgform, hgform] at hA1 hB1
  rw [hu2] at hA1
  rw [hu1] at hB1
  -- so d1' is a maximiser at y2
  have hEq : M.gWith V t y2 d2 ≤ M.gWith V t y2 d1' := by
    rw [hgform, hgform, hu1]
    have hy : M.c t * y1 = M.c t * y1 := rfl
    nlinarith
  have hmax' : IsMaxOn (M.gWith V t y2) I d1' := by
    intro d hd
    have := hdmax y2 hd
    simp only [Set.mem_setOf_eq] at this ⊢
    linarith
  have := hdleast y2 d1' hd1'I hmax'
  rw [← hd2] at this
  linarith
