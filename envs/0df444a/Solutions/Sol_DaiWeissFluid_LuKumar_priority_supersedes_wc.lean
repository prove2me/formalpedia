-- Prove2me | solution 1 for DaiWeissFluid.LuKumar.priority_supersedes_wc
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T01:43:03.579666+00:00
-- url     : https://prove2.me/submissions/15e9cbda-7e56-49b8-8340-66c37d5fe8b6

import Mathlib
import Definitions.Def_DaiWeissFluid_LuKumar_FluidModel
import Definitions.Def_DaiWeissFluid_LuKumar_Network

open DaiWeissFluid.LuKumar in
theorem solution {I K : ℕ} (L : ReentrantLine I K)
    (hm : ∀ k, 0 < L.m k) (π : Equiv.Perm (Fin K))
    (Q T : ℝ → Fin K → ℝ) :
    L.IsPrioritySolution π Q T → L.IsWorkConserving Q T := by
  rintro ⟨hsol, hpri⟩
  refine ⟨hsol, fun i s t hs hst hpos => ?_⟩
  have hne : (L.C i).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have := hpos s ⟨le_rfl, hst⟩
    simp [h] at this
  obtain ⟨k, hk, hkmax⟩ := Finset.exists_max_image (L.C i) (fun l => π l) hne
  have hσk : L.σ k = i := by simpa [ReentrantLine.C] using hk
  have hH : L.H π k = L.C i := by
    ext l
    simp only [ReentrantLine.H, ReentrantLine.C, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, _⟩; rw [h1, hσk]
    · intro h1
      refine ⟨by rw [h1, hσk], hkmax l ?_⟩
      simp [ReentrantLine.C, h1]
  have hU : ∀ x, L.Uplus π T k x = L.idle T i x := by
    intro x
    simp only [ReentrantLine.Uplus, ReentrantLine.Tplus, ReentrantLine.idle,
      ReentrantLine.busy, hH]
  have key := hpri k s t hs hst (by
    intro u hu
    have hu0 : 0 ≤ u := le_trans hs hu.1
    have hp := hpos u hu
    simp only [ReentrantLine.Wplus, hH]
    obtain ⟨l, hl, hql⟩ : ∃ l ∈ L.C i, 0 < Q u l := by
      by_contra h
      push Not at h
      have : ∑ k ∈ L.C i, Q u k ≤ 0 := Finset.sum_nonpos h
      linarith
    apply Finset.sum_pos'
    · intro j _
      exact mul_nonneg (hm j).le (hsol.nonneg u hu0 j)
    · exact ⟨l, hl, mul_pos (hm l) hql⟩)
  rw [hU, hU] at key
  exact key
