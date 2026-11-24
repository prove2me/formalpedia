-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.exampleZ_coatom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:19.251186+00:00
-- url     : https://prove2.me/submissions/1549fb6d-dc17-490a-9b1e-dde295f35698

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ExampleZ
import Theorems.Thm_Formalism_HermitianLatticesTheory_exampleZ_mem_one
import Theorems.Thm_Formalism_HermitianLatticesTheory_exampleZ_mem_span
import Theorems.Thm_Formalism_HermitianLatticesTheory_exampleZ_mem_locP
import Theorems.Thm_Formalism_HermitianLatticesTheory_exampleZ_odd
import Theorems.Thm_Formalism_HermitianLatticesTheory_exampleZ_not_mem_of_odd

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
theorem _root_.solution (p : Ideal ℤ) [p.IsPrime] (hp : p = Ideal.span {2}) :
    IsCoatom ((localization₂ p (Submodule.span ℤ {(2 : ℚ)})).comap (localization₂ p (1 : Submodule ℤ ℚ)).subtype) := by
  have memL : ∀ (L : Submodule ℤ ℚ) (x : ℚ), x ∈ localization₂ p L ↔ ∃ s : ℤ, Odd s ∧ (s : ℚ) * x ∈ L := by
    intro L x
    rw [exampleZ_mem_locP, hp]
    constructor
    · rintro ⟨s, hs, h⟩; exact ⟨s, exampleZ_odd hs, h⟩
    · rintro ⟨s, hs, h⟩; exact ⟨s, exampleZ_not_mem_of_odd hs, h⟩
  constructor
  · intro htop
    have h1 : (1 : ℚ) ∈ localization₂ p (1 : Submodule ℤ ℚ) :=
      (memL _ _).mpr ⟨1, odd_one, (exampleZ_mem_one _).mpr ⟨1, by norm_num⟩⟩
    have h2 : (⟨1, h1⟩ : localization₂ p (1 : Submodule ℤ ℚ)) ∈
        (localization₂ p (Submodule.span ℤ {(2 : ℚ)})).comap (localization₂ p (1 : Submodule ℤ ℚ)).subtype := by
      rw [htop]; trivial
    rw [Submodule.mem_comap] at h2
    obtain ⟨s, hs, h⟩ := (memL _ _).mp h2
    obtain ⟨n, hn⟩ := (exampleZ_mem_span _ _).mp h
    simp only [Submodule.coe_subtype, mul_one] at hn
    have : n * 2 = s := by exact_mod_cast hn
    obtain ⟨k, hk⟩ := hs
    omega
  · intro b hb
    obtain ⟨x, hxb, hxN⟩ := SetLike.exists_of_lt hb
    rw [Submodule.mem_comap, Submodule.coe_subtype, memL] at hxN
    obtain ⟨t, ht, hx⟩ := (memL _ _).mp x.2
    obtain ⟨m, hm⟩ := (exampleZ_mem_one _).mp hx
    have hmodd : Odd m := by
      rw [← Int.not_even_iff_odd]
      rintro ⟨j, hj⟩
      apply hxN
      refine ⟨t, ht, (exampleZ_mem_span _ _).mpr ⟨j, ?_⟩⟩
      rw [← hm, hj]; push_cast; ring
    rw [eq_top_iff]
    intro y _
    obtain ⟨u, hu, hy⟩ := (memL _ _).mp y.2
    obtain ⟨k, hk⟩ := (exampleZ_mem_one _).mp hy
    rcases Int.even_or_odd k with ⟨j, hj⟩ | hkodd
    · apply hb.le
      rw [Submodule.mem_comap, Submodule.coe_subtype, memL]
      refine ⟨u, hu, (exampleZ_mem_span _ _).mpr ⟨j, ?_⟩⟩
      rw [← hk, hj]; push_cast; ring
    · have hev : Even (t * k - u * m) := Odd.sub_odd (ht.mul hkodd) (hu.mul hmodd)
      obtain ⟨j, hj⟩ := hev
      have hj' : ((t : ℚ) * k - u * m) = j + j := by exact_mod_cast hj
      have hyx : y - x ∈ (localization₂ p (Submodule.span ℤ {(2 : ℚ)})).comap
          (localization₂ p (1 : Submodule ℤ ℚ)).subtype := by
        rw [Submodule.mem_comap, Submodule.coe_subtype, memL]
        refine ⟨t * u, ht.mul hu, (exampleZ_mem_span _ _).mpr ⟨j, ?_⟩⟩
        simp only [Submodule.coe_sub]
        push_cast
        linear_combination (u : ℚ) * hm.symm - (t : ℚ) * hk.symm - hj'
      have := b.add_mem (hb.le hyx) hxb
      simpa using this
end Formalism.HermitianLatticesTheory
