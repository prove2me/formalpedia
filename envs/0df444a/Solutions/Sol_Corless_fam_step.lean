-- Prove2me | solution 1 for Corless.fam_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:44:06.168229+00:00
-- url     : https://prove2.me/submissions/52098ada-6291-4606-95ff-9e62b57904bc

module
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Set.Card
public import Definitions.Def_LeanPool_CorlessNilpotent_Matrix
public import Definitions.Def_LeanPool_CorlessNilpotent_Vectors
public import Theorems.Thm_Corless_Fam_congr
public import Theorems.Thm_Corless_getD_step_left
public import Theorems.Thm_Corless_getD_step_a
public import Theorems.Thm_Corless_getD_step_b
public import Theorems.Thm_Corless_getD_step_right
public import Theorems.Thm_Corless_Dv_one
public import Theorems.Thm_Corless_Dv_zero
public import Theorems.Thm_Corless_entrySign_I
public import Theorems.Thm_Corless_entrySign_one
attribute [local simp] Corless.Dv_one
attribute [local simp] Corless.Dv_zero
attribute [local simp] Corless.entrySign_I
attribute [local simp] Corless.entrySign_one



set_option autoImplicit true
@[expose] public section
public section
open Polynomial
open Corless
namespace Corless
theorem _root_.solution {k : ℕ} {u : List ℂ} {a b : ℂ} (hlen : u.length = 2 ^ (k + 1) - 2)
    (hfam : Fam k (sgns u)) (hab : (a = 1 ∧ b = Complex.I) ∨ (a = Complex.I ∧ b = 1)) :
    Fam (k + 1) (sgns (foldVector u a b)) := by
  simp only [Fam, IsFolded, ← hlen]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · unfold sgns
    rw [getD_step_a, getD_step_b]
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  · intro i hi
    unfold sgns
    rw [getD_step_right _ _ _ hi, getD_step_left _ _ _ hi]
  · rw [Fam_congr k (t := sgns u) (fun i hi => by
      unfold sgns
      rw [getD_step_left _ _ _ (by omega)])]
    exact hfam
end Corless
