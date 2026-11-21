-- Prove2me | solution 1 for Corless.corless_conjecture
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:51:03.909335+00:00
-- url     : https://prove2.me/submissions/53dcdff6-5dbd-4cdf-a15f-3e83e4b22ec6

module
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Set.Card
public import Definitions.Def_LeanPool_CorlessNilpotent_Matrix
public import Definitions.Def_LeanPool_CorlessNilpotent_Vectors
public import Theorems.Thm_Corless_CorlessVec_length_eq
public import Theorems.Thm_Corless_CorlessVec_fam
public import Theorems.Thm_Corless_getD_mem
public import Theorems.Thm_Corless_CorlessVec_of_fam
public import Theorems.Thm_Corless_T_nilpotent_iff
public import Theorems.Thm_Corless_two_le_pow


set_option autoImplicit true
@[expose] public section
public section
open Polynomial
open Corless
namespace Corless
theorem _root_.solution {u : List ℂ} (hu : ∀ x ∈ u, x = 1 ∨ x = Complex.I) :
    IsNilpotent (T (u.length + 1) (fun i => u.getD i 1)) ↔ ∃ k, CorlessVec k u := by
  rw [T_nilpotent_iff (fun i hi => getD_mem hu i (by omega)) (by omega)]
  constructor
  · rintro ⟨k, hk, hfam⟩
    exact ⟨k, CorlessVec.of_fam k (by omega) hu hfam⟩
  · rintro ⟨k, hk⟩
    have hp := two_le_pow k
    exact ⟨k, by rw [hk.length_eq]; omega, hk.fam⟩
end Corless
