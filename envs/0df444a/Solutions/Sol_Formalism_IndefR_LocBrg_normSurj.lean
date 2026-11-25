-- Prove2me | solution 1 for Formalism.IndefR.LocBrg.normSurj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:09:38.844347+00:00
-- url     : https://prove2.me/submissions/83c179e8-382d-4dda-9c44-f1b112d1976d

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LocalNormSurjectivity_WittDiag
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LocalNormSurjectivity_FinNormSurj
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LocalNormSurjectivity_MemMaxVAIff
import Theorems.Thm_Formalism_IndefR_LocBrg_mem_intL
import Theorems.Thm_Formalism_IndefR_LocBrg_mem_max_VA_iff
import Theorems.Thm_Formalism_IndefR_LocBrg_sigA_inv
import Theorems.Thm_Formalism_IndefR_LocBrg_two_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.IndefR Formalism.IndefR.LocBrg
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
namespace Formalism.IndefR.LocBrg
theorem _root_.solution [CompleteSpace L] (hF : FinNormSurj) (hS : HenselSqrt) {ϖ : L} {σ : L →+* L} {q : ℕ}
    (hU : Formalism.UG.IsUnramInv ϖ σ q) (hq : Odd q) (c : VA L) (hcσ : sigA σ hU.2.1 c = c) (hc : IsUnit c) :
    ∃ t : VA L, sigA σ hU.2.1 t * t = c := by
  obtain ⟨hσσ, hv, -, -, ⟨x₀, hx₀, hx₀v⟩, hq2, hcard⟩ := id hU
  haveI : Finite (IsLocalRing.ResidueField (VA L)) :=
    Nat.finite_of_card_ne_zero (by rw [show Nat.card (IsLocalRing.ResidueField (VA L)) = q ^ 2 from hcard]; positivity)
  letI : Fintype (IsLocalRing.ResidueField (VA L)) := Fintype.ofFinite _
  have hτres : ∀ a : VA L, IsLocalRing.ResidueField.map (sigA σ hU.2.1) (IsLocalRing.residue (VA L) a) =
      IsLocalRing.residue (VA L) (sigA σ hU.2.1 a) := fun a => IsLocalRing.ResidueField.map_residue _ a
  have hττ : ∀ y, IsLocalRing.ResidueField.map (sigA σ hU.2.1)
      (IsLocalRing.ResidueField.map (sigA σ hU.2.1) y) = y := by
    intro y
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
    rw [hτres, hτres, sigA_inv σ _ hσσ]
  have hne : ∃ y, IsLocalRing.ResidueField.map (sigA σ hU.2.1) y ≠ y := by
    refine ⟨IsLocalRing.residue (VA L) ⟨x₀, mem_VA.2 (mem_intL.1 hx₀)⟩, ?_⟩
    rw [hτres]
    intro h
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, mem_max_VA_iff] at h
    have h' : Valued.v (σ x₀ - x₀) < 1 := h
    rw [hx₀v] at h'
    exact lt_irrefl _ h'
  have hcfix : IsLocalRing.ResidueField.map (sigA σ hU.2.1) (IsLocalRing.residue (VA L) c) =
      IsLocalRing.residue (VA L) c := by
    rw [hτres, hcσ]
  have hc0 : IsLocalRing.residue (VA L) c ≠ 0 := by
    rw [Ne, IsLocalRing.residue_eq_zero_iff]
    exact fun h => (IsLocalRing.mem_maximalIdeal _).1 h hc
  obtain ⟨ybar, hy⟩ := hF _ _ hττ hne _ hcfix hc0
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective ybar
  rw [hτres, ← map_mul] at hy
  have hdiff : sigA σ hU.2.1 y * y - c ∈ IsLocalRing.maximalIdeal (VA L) := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hy, sub_self]
  rw [mem_max_VA_iff] at hdiff
  have hcv : Valued.v (c : L) = 1 := (isUnit_VA_iff c).1 hc
  have hdiff' : Valued.v (σ (y : L) * (y : L) - c) < 1 := hdiff
  have hav : Valued.v (σ (y : L) * (y : L)) = 1 := by
    have h1 : Valued.v ((c : L) + (σ (y : L) * (y : L) - c)) = Valued.v (c : L) :=
      Valuation.map_add_eq_of_lt_left _ (by rw [hcv]; exact hdiff')
    rwa [add_sub_cancel, hcv] at h1
  have ha0 : σ (y : L) * (y : L) ≠ 0 := fun h => by
    rw [h, map_zero] at hav
    exact zero_ne_one hav
  have hu1 : Valued.v ((c : L) * (σ (y : L) * (y : L))⁻¹ - 1) < 1 := by
    have h1 : (c : L) * (σ (y : L) * (y : L))⁻¹ - 1 =
        -(σ (y : L) * (y : L) - c) * (σ (y : L) * (y : L))⁻¹ := by
      rw [neg_sub, sub_mul, mul_inv_cancel₀ ha0]
    rw [h1, map_mul, map_inv₀, hav, inv_one, mul_one, Valuation.map_neg]
    exact hdiff'
  have h2v : Valued.v (2 : L) = 1 := two_val hU hq
  obtain ⟨s, hss, hs1⟩ := hS L h2v _ hu1
  have hσc : σ (c : L) = c := congrArg Subtype.val hcσ
  have hσu : σ ((c : L) * (σ (y : L) * (y : L))⁻¹) = (c : L) * (σ (y : L) * (y : L))⁻¹ := by
    rw [map_mul, map_inv₀, map_mul, hσσ, hσc, mul_comm (y : L)]
  have hvs : Valued.v s = 1 := by
    have h1 : Valued.v ((1 : L) + (s - 1)) = Valued.v (1 : L) :=
      Valuation.map_add_eq_of_lt_left _ (by rw [map_one]; exact hs1)
    rwa [add_sub_cancel, map_one] at h1
  have hσs : σ s = s := by
    have hsq : (σ s - s) * (σ s + s) = 0 := by
      have h1 : σ s * σ s = s * s := by rw [← map_mul, hss, hσu]
      linear_combination h1
    have hσs1 : Valued.v (σ s - 1) < 1 := by
      rw [← map_one σ, ← map_sub, hv]
      exact hs1
    have hsmall : Valued.v ((σ s - 1) + (s - 1)) < 1 :=
      lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hσs1 hs1)
    have hsum : Valued.v (σ s + s) = 1 := by
      have h1 : Valued.v ((2 : L) + ((σ s - 1) + (s - 1))) = Valued.v (2 : L) :=
        Valuation.map_add_eq_of_lt_left _ (by rw [h2v]; exact hsmall)
      rw [h2v] at h1
      rw [← h1]
      congr 1
      ring
    have hne0 : σ s + s ≠ 0 := fun h => by
      rw [h, map_zero] at hsum
      exact zero_ne_one hsum
    rcases mul_eq_zero.1 hsq with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hne0
  refine ⟨⟨(y : L) * s, ?_⟩, ?_⟩
  · rw [mem_VA, map_mul, hvs, mul_one]
    exact mem_VA.1 y.2
  · apply Subtype.ext
    show σ ((y : L) * s) * ((y : L) * s) = (c : L)
    rw [map_mul, hσs]
    have hcu : (c : L) = (c : L) * (σ (y : L) * (y : L))⁻¹ * (σ (y : L) * (y : L)) := by
      rw [mul_assoc, inv_mul_cancel₀ ha0, mul_one]
    rw [hcu, ← hss]
    ring
end Formalism.IndefR.LocBrg
