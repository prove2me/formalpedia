-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.enum_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:08:19.249645+00:00
-- url     : https://prove2.me/submissions/5d04c4fd-2f90-45e9-95fb-572b17fbcd2e

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_Sl2RaisePowSuccLowerApplyEq
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_EArith
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_TypesLELeYcondC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_OmegaInjectiveHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_sum_erase_last
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_exponent_arithmetic_holds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.QuotientRingDecomposition.E_apply
attribute [local simp] Formalism.GM.QuotientRingDecomposition.divQ_apply



set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution {r : ℕ} [NeZero r] (ρ : Fin r) (hr : 2 ≤ r) (hρ : (ρ : ℕ) = r - 1) (c : ℤ) (o : ℕ)
    (th β : Fin r → ℤ) (hβ : ∀ a, 0 ≤ β a) (hβρ : β ρ = 0) (hsum : ∑ a, β a = o + 1) (h0 : th 0 ≤ c)
    (hstrip : ∀ a ∈ univ.erase ρ, ∀ a' ∈ univ.erase ρ, a < a' → th a' ≤ th a - β a) : 0 < Enum ρ c o th β := by
  classical
  let ka : ℕ → ℤ := fun i => if h : i < r then th ⟨i, h⟩ - β ⟨i, h⟩ else 0
  let bN : ℕ → ℕ := fun i => if h : i < r then (β ⟨i, h⟩).toNat else 0
  have hka : ∀ a : Fin r, ka (a : ℕ) = th a - β a := fun a => by simp only [ka, dif_pos a.isLt, Fin.eta]
  have hbN : ∀ a : Fin r, ((bN (a : ℕ) : ℕ) : ℤ) = β a := fun a => by
    simp only [bN, dif_pos a.isLt, Fin.eta]; exact Int.toNat_of_nonneg (hβ a)
  have hmem : ∀ i, (h : i < r - 1) → (⟨i, by omega⟩ : Fin r) ∈ univ.erase ρ := by
    intro i h
    refine Finset.mem_erase.mpr ⟨fun he => ?_, Finset.mem_univ _⟩
    have := congrArg Fin.val he
    simp only at this
    omega
  have hS : ∑ a ∈ range (r - 1), ((bN a : ℕ) : ℤ) = o + 1 := by
    rw [← sum_erase_last ρ hρ (fun i => ((bN i : ℕ) : ℤ)), ← hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ ρ),
      hβρ, zero_add]
    exact Finset.sum_congr rfl fun a _ => hbN a
  have key := exponent_arithmetic_holds (r - 1) ka bN c ?_ ?_ ?_
  · rw [hS] at key
    have h1 : ∑ a ∈ range (r - 1), ((bN a : ℕ) : ℤ) * ka a = ∑ a ∈ univ.erase ρ, β a * (th a - β a) := by
      rw [← sum_erase_last ρ hρ (fun i => ((bN i : ℕ) : ℤ) * ka i)]
      exact Finset.sum_congr rfl fun a _ => by rw [hbN, hka]
    have h2 : ∑ b ∈ range (r - 1), ∑ a ∈ range b, (((bN a : ℕ) : ℤ) + 1) * ((bN b : ℕ) : ℤ) =
        ∑ a ∈ univ.erase ρ, ∑ b ∈ univ.erase ρ, (if a < b then (β a + 1) * β b else 0) := by
      rw [← sum_erase_last ρ hρ (fun j => ∑ a ∈ range j, (((bN a : ℕ) : ℤ) + 1) * ((bN j : ℕ) : ℤ)),
        Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      have hb : (b : ℕ) ≤ r - 1 := by have := b.isLt; omega
      have e1 : ∑ a ∈ range (b : ℕ), (((bN a : ℕ) : ℤ) + 1) * ((bN (b : ℕ) : ℕ) : ℤ) =
          ∑ a ∈ range (r - 1), (if a < (b : ℕ) then (((bN a : ℕ) : ℤ) + 1) * ((bN (b : ℕ) : ℕ) : ℤ) else 0) := by
        rw [← Finset.sum_filter]
        refine Finset.sum_congr ?_ fun _ _ => rfl
        ext i
        simp only [Finset.mem_range, Finset.mem_filter]
        omega
      rw [e1, ← sum_erase_last ρ hρ
        (fun i => if i < (b : ℕ) then (((bN i : ℕ) : ℤ) + 1) * ((bN (b : ℕ) : ℕ) : ℤ) else 0)]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hbN, hbN]
      simp only [Fin.lt_def]
    rw [h1, h2] at key
    unfold Enum
    simp only [Finset.sum_sub_distrib]
    have h3 : ∑ a ∈ univ.erase ρ, ∑ b ∈ univ.erase ρ, (if a = b then β a * (th a - β a) else 0) =
        ∑ a ∈ univ.erase ρ, β a * (th a - β a) := by
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [Finset.sum_ite_eq, if_pos ha]
    rw [h3]
    have e2 : (c - ((o : ℤ) + 1) + 1) * ((o : ℤ) + 1) = (c - o) * (o + 1) := by ring
    rw [e2] at key
    linarith
  · intro i hi
    have h1 := hstrip ⟨i, by omega⟩ (hmem i (by omega)) ⟨i + 1, by omega⟩ (hmem (i + 1) hi)
      (by simp only [Fin.lt_def]; omega)
    have h2 := hka ⟨i, by omega⟩
    have h3 := hka ⟨i + 1, by omega⟩
    have h4 := hbN ⟨i + 1, by omega⟩
    simp only at h2 h3 h4
    rw [h2, h3, h4]
    linarith
  · intro _
    have h2 := hka 0
    have h4 := hbN 0
    rw [Fin.val_zero] at h2 h4
    rw [h2, h4]
    linarith
  · have : ((1 : ℕ) : ℤ) ≤ ((∑ a ∈ range (r - 1), bN a : ℕ) : ℤ) := by
      push_cast
      rw [hS]
      have := Int.natCast_nonneg o
      linarith
    exact_mod_cast this
end Formalism.InvariantFactorPaths.L4
