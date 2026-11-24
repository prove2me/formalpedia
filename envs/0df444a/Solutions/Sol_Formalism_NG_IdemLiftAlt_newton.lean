-- Prove2me | solution 1 for Formalism.NG.IdemLiftAlt.newton
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:40:52.03893+00:00
-- url     : https://prove2.me/submissions/1ca5708c-7dfd-4f08-820b-75f02182f323

import Definitions.Def_Formalism_CharacterColumnKernels_StatOntoLattice
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_SpacedProductLowerBound
import Theorems.Thm_Formalism_NG_IdemLiftAlt_pow_dvd_nP_sq_sub
import Theorems.Thm_Formalism_NG_IdemLiftAlt_mul_mem_left
import Theorems.Thm_Formalism_NG_IdemLiftAlt_mul_mem_right
import Theorems.Thm_Formalism_NG_IdemLiftAlt_mul_mem_pow
import Theorems.Thm_Formalism_NG_IdemLiftAlt_pow_smul_mono
import Theorems.Thm_Formalism_NG_IdemLiftAlt_precomplete_of_finite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.NG
open Formalism.NG.IdemLiftAlt
variable {O A : Type*} [CommRing O] [Ring A] [Algebra O A]
variable [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
  [Module.Finite O A]
namespace Formalism.NG.IdemLiftAlt
theorem _root_.solution (a : A) (n : ℕ)
    (hn : (a ^ 2 - a) ^ n ∈ IsLocalRing.maximalIdeal O • (⊤ : Submodule O A)) :
    ∃ L : A, IsIdempotentElem L ∧ ∀ j : ℕ,
      aeval a (nP (n + j)) - L ∈ IsLocalRing.maximalIdeal O ^ j • (⊤ : Submodule O A) := by
  set I := IsLocalRing.maximalIdeal O
  set S : ℕ → Submodule O A := fun j => I ^ j • (⊤ : Submodule O A) with hS
  have hS1 : S 1 = I • ⊤ := by simp [hS]
  set ak : ℕ → A := fun k => aeval a (nP k) with hak
  have hrec : ∀ k, ak (k + 1) = 3 * ak k ^ 2 - 2 * ak k ^ 3 := by
    intro k; simp [hak, nP, map_ofNat]
  have hxrec : ∀ k, ak (k + 1) ^ 2 - ak (k + 1) =
      (ak k ^ 2 - ak k) * ((ak k ^ 2 - ak k) * (4 * (ak k ^ 2 - ak k) - 3)) := by
    intro k; rw [hrec]; noncomm_ring
  have hdiff : ∀ k, ak (k + 1) - ak k = (ak k ^ 2 - ak k) * (1 - 2 * ak k) := by
    intro k; rw [hrec]; noncomm_ring
  have hx0 : ak n ^ 2 - ak n ∈ S 1 := by
    obtain ⟨U, hU⟩ := pow_dvd_nP_sq_sub n
    have h1 : ak n ^ 2 - ak n = (a ^ 2 - a) ^ (2 ^ n) * aeval a U := by
      have := congrArg (aeval a) hU
      simpa [hak] using this
    rw [h1, hS1]
    apply mul_mem_left
    have h2 : 2 ^ n = n + (2 ^ n - n) := (Nat.add_sub_cancel' (Nat.lt_two_pow_self).le).symm
    rw [h2, pow_add]
    exact mul_mem_left _ _ hn
  have hx : ∀ j, ak (n + j) ^ 2 - ak (n + j) ∈ S (j + 1) := by
    intro j
    induction j with
    | zero => simpa using hx0
    | succ j ih =>
      rw [← add_assoc, hxrec]
      have h3 : (ak (n + j) ^ 2 - ak (n + j)) * (4 * (ak (n + j) ^ 2 - ak (n + j)) - 3) ∈ S 1 := by
        rw [hS1]; apply mul_mem_left
        have := pow_smul_mono I (show 1 ≤ j + 1 by omega) ih
        simpa using this
      exact mul_mem_pow I ih h3
  set b : ℕ → A := fun j => ak (n + j) with hb
  have hbstep : ∀ k, b (k + 1) - b k ∈ S (k + 1) := by
    intro k
    simp only [hb]
    rw [← add_assoc, hdiff]
    exact mul_mem_left _ _ (hx k)
  have hcauchy : ∀ m k, m ≤ k → b m - b k ∈ S m := by
    intro m k hmk
    induction k, hmk using Nat.le_induction with
    | base => simp
    | succ k hmk ih =>
      have e : b m - b (k + 1) = (b m - b k) - (b (k + 1) - b k) := by abel
      rw [e]
      exact Submodule.sub_mem _ ih (pow_smul_mono I (by omega) (hbstep k))
  have hpre : IsPrecomplete I A := precomplete_of_finite I A
  obtain ⟨L, hL⟩ := hpre.prec (f := b) (fun {m k} hmk => (SModEq.sub_mem).2 (hcauchy m k hmk))
  have hL' : ∀ j, b j - L ∈ S j := fun j => (SModEq.sub_mem).1 (hL j)
  refine ⟨L, ?_, hL'⟩
  have hzero : L * L - L = 0 := by
    refine IsHausdorff.haus (inferInstance : IsHausdorff I A) _ (fun j => ?_)
    rw [SModEq.sub_mem, sub_zero]
    have hLb : L - b j ∈ S j := by
      have := Submodule.neg_mem _ (hL' j); simpa using this
    have e : L * L - L = (L - b j) * L + b j * (L - b j) + (b j ^ 2 - b j) - (L - b j) := by
      noncomm_ring
    rw [e]
    refine Submodule.sub_mem _ (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_) hLb
    · exact mul_mem_left _ _ hLb
    · exact mul_mem_right _ _ hLb
    · exact pow_smul_mono I (by omega) (hx j)
  exact sub_eq_zero.1 hzero
end Formalism.NG.IdemLiftAlt
