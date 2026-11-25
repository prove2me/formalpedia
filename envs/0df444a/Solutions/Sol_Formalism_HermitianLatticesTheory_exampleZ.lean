-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.exampleZ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:07:31.74378+00:00
-- url     : https://prove2.me/submissions/2469c14a-bd08-4a2c-8710-23257624b229

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ExampleZ
import Theorems.Thm_Formalism_HermitianLatticesTheory_exampleZ_mem_one
import Theorems.Thm_Formalism_HermitianLatticesTheory_exampleZ_mem_span
import Theorems.Thm_Formalism_HermitianLatticesTheory_exampleZ_mem_dual
import Theorems.Thm_Formalism_HermitianLatticesTheory_exampleZ_len_top
import Theorems.Thm_Formalism_HermitianLatticesTheory_exampleZ_inf
import Theorems.Thm_Formalism_HermitianLatticesTheory_exampleZ_coatom
import Theorems.Thm_Formalism_HermitianLatticesTheory_exampleZ_all
import Theorems.Thm_Formalism_HermitianLatticesTheory_exampleZ_len_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution : ExampleZ := by
  intro h hh
  have hd : ∀ (L : Submodule ℤ ℚ) (x : ℚ), x ∈ dual h L ↔ ∀ y ∈ L, y * x ∈ (1 : Submodule ℤ ℚ) := by
    intro L x
    rw [exampleZ_mem_dual]
    simp only [hh]
  have hdual2 : dual h (Submodule.span ℤ {(2 : ℚ)}) = Submodule.span ℤ {(1 / 2 : ℚ)} := by
    ext x
    rw [hd, exampleZ_mem_span]
    constructor
    · intro H
      obtain ⟨n, hn⟩ := (exampleZ_mem_one _).mp (H 2 (Submodule.mem_span_singleton_self _))
      exact ⟨n, by rw [hn]; ring⟩
    · rintro ⟨n, rfl⟩ y hy
      obtain ⟨m, rfl⟩ := (exampleZ_mem_span _ _).mp hy
      exact (exampleZ_mem_one _).mpr ⟨m * n, by push_cast; ring⟩
  refine ⟨?_, ?_, ?_, hdual2, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _
    · rw [eq_top_iff]
      intro x _
      have h1 : (1 : ℚ) ∈ ((1 : Submodule ℤ ℚ) : Set ℚ) := (exampleZ_mem_one _).mpr ⟨1, by norm_num⟩
      have := Submodule.smul_mem (Submodule.span ℚ ((1 : Submodule ℤ ℚ) : Set ℚ)) x
        (Submodule.subset_span h1)
      simpa using this
  · unfold IsUnimodular
    ext x
    rw [hd]
    constructor
    · intro H
      simpa using H 1 ((exampleZ_mem_one _).mpr ⟨1, by norm_num⟩)
    · intro hx y hy
      obtain ⟨n, rfl⟩ := (exampleZ_mem_one _).mp hy
      obtain ⟨m, rfl⟩ := (exampleZ_mem_one _).mp hx
      exact (exampleZ_mem_one _).mpr ⟨n * m, by push_cast; ring⟩
  · intro x hx y hy
    rw [hh]
    obtain ⟨n, rfl⟩ := (exampleZ_mem_span _ _).mp hx
    obtain ⟨m, rfl⟩ := (exampleZ_mem_span _ _).mp hy
    exact (exampleZ_mem_one _).mpr ⟨n * 2 * (m * 2), by push_cast; ring⟩
  · intro H
    unfold IsUnimodular at H
    rw [hdual2] at H
    have : (1 / 2 : ℚ) ∈ Submodule.span ℤ {(2 : ℚ)} := by
      rw [← H]; exact Submodule.mem_span_singleton_self _
    obtain ⟨n, hn⟩ := (exampleZ_mem_span _ _).mp this
    have h4 : (n : ℚ) * 4 = 1 := by linear_combination 2 * hn
    have h4' : n * 4 = 1 := by exact_mod_cast h4
    omega
  · intro p _ hp
    unfold lidx
    rw [exampleZ_inf, exampleZ_len_self]
    unfold locLen
    rw [Module.length_eq_one_iff.mpr ((isSimpleModule_iff_isCoatom).mpr (exampleZ_coatom p hp))]
    rfl
  · intro p _ hp
    unfold lidx
    rw [exampleZ_inf, exampleZ_len_self]
    unfold locLen
    rw [exampleZ_len_top _ (exampleZ_all p hp)]
    rfl
end Formalism.HermitianLatticesTheory
