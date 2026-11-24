-- Prove2me | solution 1 for Formalism.IndefR.LocBrg.two_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:15:04.114872+00:00
-- url     : https://prove2.me/submissions/101fb177-695c-400c-8bfa-a7d73d8d392b

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LocalNormSurjectivity_WittDiag
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LocalNormSurjectivity_FinNormSurj
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LocalNormSurjectivity_MemMaxVAIff
import Theorems.Thm_Formalism_IndefR_LocBrg_mem_max_VA_iff
import Theorems.Thm_Formalism_IndefR_LocBrg_Witt_corner_block_succ_succ
import Theorems.Thm_Formalism_IndefR_LocBrg_Witt_corner_block_succ_zero
import Theorems.Thm_Formalism_IndefR_LocBrg_Witt_corner_block_zero_succ
import Theorems.Thm_Formalism_IndefR_LocBrg_Witt_corner_block_zero_zero
import Theorems.Thm_Formalism_IndefR_LocBrg_Witt_gsR_succ_succ
import Theorems.Thm_Formalism_IndefR_LocBrg_Witt_gsR_succ_zero
import Theorems.Thm_Formalism_IndefR_LocBrg_Witt_gsR_zero_succ
import Theorems.Thm_Formalism_IndefR_LocBrg_Witt_gsR_zero_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.IndefR.LocBrg.Witt.corner_block_succ_succ
attribute [local simp] Formalism.IndefR.LocBrg.Witt.corner_block_succ_zero
attribute [local simp] Formalism.IndefR.LocBrg.Witt.corner_block_zero_succ
attribute [local simp] Formalism.IndefR.LocBrg.Witt.corner_block_zero_zero
attribute [local simp] Formalism.IndefR.LocBrg.Witt.gsR_succ_succ
attribute [local simp] Formalism.IndefR.LocBrg.Witt.gsR_succ_zero
attribute [local simp] Formalism.IndefR.LocBrg.Witt.gsR_zero_succ
attribute [local simp] Formalism.IndefR.LocBrg.Witt.gsR_zero_zero


section
noncomputable section
open Matrix
namespace Formalism.IndefR.LocBrg
section Glue
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
variable (σ : L →+* L) (hv : ∀ x, Valued.v (σ x) = Valued.v x)
end Glue
section Norm
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
private theorem valuation_two_eq_one_of_unramInv_odd {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : Formalism.UG.IsUnramInv ϖ σ q) (hq : Odd q) :
    Valued.v (2 : L) = 1 := by
  obtain ⟨-, -, -, -, -, hq2, hcard⟩ := hU
  have hle : Valued.v (2 : L) ≤ 1 := by
    calc Valued.v (2 : L) = Valued.v ((1 : L) + 1) := by norm_num
      _ ≤ max (Valued.v (1 : L)) (Valued.v (1 : L)) := Valuation.map_add _ _ _
      _ = 1 := by simp
  by_contra h2
  have hlt := lt_of_le_of_ne hle h2
  have hmem : (2 : VA L) ∈ IsLocalRing.maximalIdeal (VA L) := by
    rw [mem_max_VA_iff]
    first
      | simpa using hlt
      | exact_mod_cast hlt
  haveI : Finite ((Valued.v : Valuation L (WithZero (Multiplicative ℤ))).integer ⧸
      IsLocalRing.maximalIdeal (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  letI := Fintype.ofFinite ((Valued.v : Valuation L (WithZero (Multiplicative ℤ))).integer ⧸
      IsLocalRing.maximalIdeal (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring)
  have h2Q : (2 : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).integer ⧸
      IsLocalRing.maximalIdeal (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring) = 0 := by
    have h := Ideal.Quotient.eq_zero_iff_mem.2 hmem
    rw [map_ofNat] at h
    exact h
  have hc0 := Nat.cast_card_eq_zero ((Valued.v : Valuation L (WithZero (Multiplicative ℤ))).integer ⧸
      IsLocalRing.maximalIdeal (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring)
  rw [← Nat.card_eq_fintype_card, hcard] at hc0
  obtain ⟨m, hm⟩ : Odd (q ^ 2) := hq.pow
  rw [hm] at hc0
  push_cast at hc0
  rw [h2Q, zero_mul, zero_add] at hc0
  have hsub := subsingleton_of_zero_eq_one hc0.symm
  haveI : Unique ((Valued.v : Valuation L (WithZero (Multiplicative ℤ))).integer ⧸
      IsLocalRing.maximalIdeal (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring) :=
    ⟨⟨0⟩, fun _ => Subsingleton.elim _ _⟩
  have hc1 := Nat.card_unique (α := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).integer ⧸
      IsLocalRing.maximalIdeal (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring)
  rw [hcard] at hc1
  nlinarith
end Norm
section Final
end Final
end Formalism.IndefR.LocBrg
end
end

set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.IndefR Formalism.IndefR.LocBrg
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
namespace Formalism.IndefR.LocBrg
theorem _root_.solution {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : Formalism.UG.IsUnramInv ϖ σ q) (hq : Odd q) :
    Valued.v (2 : L) = 1 := by
  exact valuation_two_eq_one_of_unramInv_odd hU hq
end Formalism.IndefR.LocBrg
