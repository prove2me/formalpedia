-- Prove2me | solution 1 for BooleanIsoperimetry.familyUpMap_compl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:36:09.238058+00:00
-- url     : https://prove2.me/submissions/b4779b95-b0af-4259-aad6-cb6d31c5df30

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression
public import Definitions.Def_LeanPool_BooleanIsoperimetry_LayerWindows
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Combinatorics.SetFamily.Compression.UV
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Compression
public import Theorems.Thm_BooleanIsoperimetry_blockReplace_compl

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} {U V : Cube N} (hd : Disjoint U V)
    (A : Finset (Cube N)) (S : Cube N) :
    (familyUpMap U V A S)ᶜ = familyUpMap V U (Aᶜˢ) Sᶜ := by
  unfold familyUpMap
  have hbr := blockReplace_compl hd S
  by_cases hc : U ⊆ S ∧ Disjoint V S ∧ blockReplace U V S ∉ A
  · obtain ⟨hUS, hVS, hnA⟩ := hc
    rw [if_pos ⟨hUS, hVS, hnA⟩]
    have hUSc : Disjoint U Sᶜ := by
      rw [← subset_compl_iff_disjoint_right, compl_compl]; exact hUS
    have hc2 : V ⊆ Sᶜ ∧ Disjoint U Sᶜ ∧ blockReplace V U Sᶜ ∉ Aᶜˢ := by
      refine ⟨subset_compl_iff_disjoint_right.mpr hVS, hUSc, ?_⟩
      rw [Finset.mem_compls, ← hbr, compl_compl]; exact hnA
    rw [if_pos hc2, hbr]
  · rw [if_neg hc]
    have hc2 : ¬ (V ⊆ Sᶜ ∧ Disjoint U Sᶜ ∧ blockReplace V U Sᶜ ∉ Aᶜˢ) := by
      rintro ⟨hVSc, hUSc, hnAc⟩
      apply hc
      refine ⟨?_, subset_compl_iff_disjoint_right.mp hVSc, ?_⟩
      · have : U ⊆ Sᶜᶜ := subset_compl_iff_disjoint_right.mpr hUSc
        rwa [compl_compl] at this
      · rw [Finset.mem_compls, ← hbr, compl_compl] at hnAc; exact hnAc
    rw [if_neg hc2]
end BooleanIsoperimetry
