-- Prove2me | solution 1 for Erdos1219.good_case
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:46:20.701792+00:00
-- url     : https://prove2.me/submissions/60eef9d2-5f55-4a0d-b5d1-12a5e79c42e6

import Definitions.Def_Erdos1219_Defs
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Definitions.Def_Erdos1219_UnbalancedErdosRado
import Theorems.Thm_Erdos1219_exists_maximal_homog
import Theorems.Thm_Erdos1219_Homog_mono


set_option autoImplicit false
open Cardinal Ordinal Set
open Erdos1219
universe u
variable {W : Type u} [LinearOrder W] [WellFoundedLT W]
omit [WellFoundedLT W]
namespace Erdos1219
theorem _root_.solution {f : W → W → Bool} (hf : ∀ x y, f x y = f y x) {c : Bool}
    {μ : Cardinal.{u}} {α : W} (hgood : IsGood f c μ α) :
    ∃ H : Set W, #H = Order.succ μ ∧ Homog f (!c) H := by
  obtain ⟨Z, hZ⟩ := exists_maximal_homog f (!c) (nbr f c α)
  obtain ⟨hZA, hZh⟩ := hZ.1
  have hlt : μ < #Z := by
    by_contra hle
    rw [not_lt] at hle
    obtain ⟨β, hβα, hZβ⟩ := hgood.1 Z (fun z hz => (hZA hz).1) hle
    obtain ⟨γ, ⟨hγA, hγD⟩, hβγ⟩ := hgood.2 Z hZA hZh hle β hβα hZβ
    have hins : insert γ Z ∈ {Z : Set W | Z ⊆ nbr f c α ∧ Homog f (!c) Z} := by
      refine ⟨insert_subset hγA hZA, ?_⟩
      intro x hx y hy hxy
      rcases mem_insert_iff.1 hx with hxγ | hxZ <;> rcases mem_insert_iff.1 hy with hyγ | hyZ
      · exact absurd (hxγ.trans hyγ.symm) hxy
      · rw [hxγ, hf]; exact hγD y hyZ
      · rw [hyγ]; exact hγD x hxZ
      · exact hZh x hxZ y hyZ hxy
    have heq := hZ.eq_of_subset hins (subset_insert γ Z)
    have hγZ : γ ∈ Z := heq ▸ mem_insert γ Z
    exact absurd (hZβ hγZ) (not_lt.2 hβγ)
  obtain ⟨H, hHZ, hH⟩ := le_mk_iff_exists_subset.1 (Order.succ_le_of_lt hlt)
  exact ⟨H, hH, hZh.mono hHZ⟩
end Erdos1219
