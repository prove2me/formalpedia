-- Prove2me | solution 1 for FairChores.wtSum_univ_le_nsmul_MMS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:22:05.010928+00:00
-- url     : https://prove2.me/submissions/83da8c5d-1e0a-45a4-9613-fe4ccb8944bd

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Theorems.Thm_FairChores_cbarSum_empty
import Theorems.Thm_FairChores_MMSset_nonempty
import Theorems.Thm_FairChores_wtSum_univ_le_of_mem_MMSset
attribute [local simp] FairChores.cbarSum_empty

set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
variable {n : ℕ}
variable {c p : T → ℝ} {mu : ℝ}
namespace FairChores
theorem _root_.solution (hc : ∀ t, 0 ≤ c t) (hn : 0 < n) :
    wtSum c p (MMS n c p) Finset.univ ≤ n * MMS n c p := by
  classical
  set mu := MMS n c p with hmudef
  obtain ⟨d, hd, hgapd⟩ :
      ∃ d : ℝ, 0 < d ∧ ∀ t, mu < cbar c p t → mu + d ≤ cbar c p t := by
    set S := (Finset.univ.image fun t => cbar c p t).filter (fun x => mu < x) with hS
    rcases S.eq_empty_or_nonempty with hemp | hne
    · refine ⟨1, one_pos, fun t ht => ?_⟩
      exfalso
      have hmem : cbar c p t ∈ S := by
        simp only [hS, Finset.mem_filter, Finset.mem_image]
        exact ⟨⟨t, Finset.mem_univ t, rfl⟩, ht⟩
      rw [hemp] at hmem
      exact absurd hmem (Finset.notMem_empty _)
    · refine ⟨S.min' hne - mu, ?_, fun t ht => ?_⟩
      · have hmin := S.min'_mem hne
        simp only [hS, Finset.mem_filter] at hmin
        linarith [hmin.2]
      · have hmem : cbar c p t ∈ S := by
          simp only [hS, Finset.mem_filter, Finset.mem_image]
          exact ⟨⟨t, Finset.mem_univ t, rfl⟩, ht⟩
        have := S.min'_le _ hmem
        linarith
  have hkey : ∀ ε : ℝ, 0 < ε → ε < d → wtSum c p mu Finset.univ ≤ n * mu + n * ε := by
    intro ε hε hεd
    obtain ⟨r, hrmem, hrlt⟩ : ∃ r ∈ MMSset n c p, r < mu + ε :=
      exists_lt_of_csInf_lt (MMSset_nonempty hc hn) (by
        show MMS n c p < mu + ε
        rw [← hmudef]; linarith)
    have hgap : ∀ t, mu < cbar c p t → r < cbar c p t := by
      intro t ht
      have := hgapd t ht
      linarith
    have hbd := wtSum_univ_le_of_mem_MMSset hc hgap hrmem
    have hn' : (0:ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  refine le_of_forall_pos_le_add ?_
  intro ε' hε'
  set ε := min (d / 2) (ε' / n) with hεdef
  have hε : 0 < ε := lt_min (by linarith) (by positivity)
  have hεd : ε < d := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have h1 := hkey ε hε hεd
  have h2 : (n:ℝ) * ε ≤ ε' := by
    have h3 : ε ≤ ε' / n := min_le_right _ _
    calc (n:ℝ) * ε ≤ n * (ε' / n) := by nlinarith
      _ = ε' := by field_simp
  linarith
end FairChores
