-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.crossing_length_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:26:17.541149+00:00
-- url     : https://prove2.me/submissions/2d355162-ca12-41b3-bf5f-c0d4bde964e5

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Deletion
public import Theorems.Thm_DeciSigma1_Holes_Fresh_prefix_drop_of_occ
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_suffix_of_le
public import Theorems.Thm_DeciSigma1_Holes_Fresh_active_anti
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_occurrences_eq_of_nested
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_occurrences_in_next_marker
public import Theorems.Thm_DeciSigma1_Holes_Fresh_suffix_take_iff
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers DeciSigma1.Words
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution {W : Fin k → List α} {t r : ℕ} (ht : 1 ≤ t)
    (hr : r ≤ t + 1) {m m0 : Fin k} (hm : m ∈ active W r) (hm0 : m0 ∈ active W t)
    {u : List α} {p e : ℕ} (hτ : marker W t m0 <:+ u.take p) (hμ : marker W r m <:+ u.take e)
    (hpe : p < e) (he : e ≤ u.length) :
    (marker W r m).length ≤ (e - p) + (marker W t m0).length := by
  by_contra hcon
  have hpu : p ≤ u.length := by omega
  obtain ⟨hμl, hμo⟩ := (suffix_take_iff he).mp hμ
  obtain ⟨hτl, hτo⟩ := (suffix_take_iff hpu).mp hτ
  rcases Nat.lt_or_ge r (t + 1) with hrt | hrt
  · -- r ≤ t: the level-`r` suffix of `τ` sits strictly inside the occurrence
    have hrt' : r ≤ t := by omega
    have hm0r : m0 ∈ active W r := active_anti W hrt' hm0
    have hsuf : marker W r m0 <:+ u.take p := (marker_suffix_of_le hrt' hm0).trans hτ
    have hsl := (marker_suffix_of_le hrt' hm0).length_le
    obtain ⟨-, hro⟩ := (suffix_take_iff hpu).mp hsuf
    obtain ⟨heq, -⟩ := marker_occurrences_eq_of_nested hm hm0r hμo hro (by omega) (by omega)
    omega
  · -- r = t + 1: `τ` is a complete internal occurrence, against
    -- `marker_occurrences_in_next_marker`
    have hr' : r = t + 1 := by omega
    subst hr'
    have hin := prefix_drop_of_occ hμo hτo (by omega) (by omega)
    rcases (marker_occurrences_in_next_marker ht hm).2.2 m0 hm0 _ hin with h | h <;> omega
end DeciSigma1.Holes.Fresh
