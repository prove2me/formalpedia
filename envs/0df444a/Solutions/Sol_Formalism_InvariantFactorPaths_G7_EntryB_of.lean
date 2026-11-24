-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.EntryB_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:53:21.800312+00:00
-- url     : https://prove2.me/submissions/143282c3-b130-453b-844c-5d4fb1259934

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_GrowthSums_StatementG
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EntryATwoAndB
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ParitySumsOverFilteredPairs_phi_parity
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ParitySumsOverFilteredPairs_iN_of_not_mem
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ParitySumsOverFilteredPairs_sum_iN
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ParitySumsOverFilteredPairs_pay_le
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ParitySumsOverFilteredPairs_iN_le_min
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ParitySumsOverFilteredPairs_sum_iN_tops
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ParitySumsOverFilteredPairs_low_pay

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral jetPair mfact)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)
open ParitySumsOverFilteredPairs
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution (hS : EntryStar) (hC : HitsCapPos) (hJ : HitsColumnsPos) (hB : BCore) :
    EntryB := by
  intro K _ _ p ν r0 r1 C _ u F TT ξ e l sf T I J hH
  have hH' := hH
  obtain ⟨-, hp2, hpn, -, -, -, -, -⟩ := hH'
  have hp : 0 < p := by omega
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  set N := ∑ x : TpV ν r1, (if (x.1.val % 2 = 0 ∧ x.2 ∉ J) ∨ (x.1.val % 2 = 1 ∧ x.2 ∈ J)
          then e x else 0) +
        ∑ c, (if (sf c).val % 2 = 1 then ((univ.image (I c)) ∩ J).card else 0) with hN
  rw [norm_mul, norm_pow, hpn]
  rcases hS K p ν r0 r1 C u F TT ξ e l sf T I hH with h0 | ⟨E, α, β, hα, hβ, h3, h4, hn⟩
  · rw [h0, norm_zero, mul_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg p) _
  · have hpinv : ((p : ℝ)⁻¹) ^ N = (p : ℝ) ^ (-(N : ℝ)) := by
      rw [Real.rpow_neg (Nat.cast_nonneg p), Real.rpow_natCast, inv_pow]
    rw [hpinv]
    refine le_trans (mul_le_mul_of_nonneg_left hn (Real.rpow_nonneg (Nat.cast_nonneg p) _)) ?_
    rw [← Real.rpow_add (by exact_mod_cast hp)]
    refine Real.rpow_le_rpow_of_exponent_le hp1.le ?_
    set P : Finset (TpV ν r1) := univ.filter (fun x : TpV ν r1 =>
      (x.1.val % 2 = 0 ∧ x.2 ∉ J) ∨ (x.1.val % 2 = 1 ∧ x.2 ∈ J)) with hPdef
    have hP : ∀ φ, α φ ≠ 0 → (pairFirst φ, φ.2.2.2.2) ∈ P ∨ (pairSecond φ, φ.2.2.2.2) ∈ P := by
      intro φ _
      have hpar := phi_parity φ
      simp only [hPdef, Finset.mem_filter, Finset.mem_univ, true_and]
      show ((pairFirst φ).val % 2 = 0 ∧ φ.2.2.2.2 ∉ J ∨ (pairFirst φ).val % 2 = 1 ∧ φ.2.2.2.2 ∈ J) ∨
        ((pairSecond φ).val % 2 = 0 ∧ φ.2.2.2.2 ∉ J ∨ (pairSecond φ).val % 2 = 1 ∧ φ.2.2.2.2 ∈ J)
      by_cases hb : φ.2.2.2.2 ∈ J
      · by_cases hv : (pairFirst φ).val % 2 = 1
        · exact Or.inl (Or.inr ⟨hv, hb⟩)
        · exact Or.inr (Or.inr ⟨by omega, hb⟩)
      · by_cases hv : (pairFirst φ).val % 2 = 0
        · exact Or.inl (Or.inl ⟨hv, hb⟩)
        · exact Or.inr (Or.inl ⟨by omega, hb⟩)
    have keyB : ∑ φ, α φ + ∑ s ∈ TT \ oddT TT, ∑ e' ∈ range E, iN β s e' ≤ N := by
      rw [sum_iN β (TT \ oddT TT)]
      have hpay := pay_le hp α β e h3 P hP
      have hlow := low_pay hJ p ξ β l sf T I h4 J
      have hNe : ∑ x : TpV ν r1, (if (x.1.val % 2 = 0 ∧ x.2 ∉ J) ∨ (x.1.val % 2 = 1 ∧ x.2 ∈ J)
          then e x else 0) = ∑ τ ∈ P, e τ := by
        rw [hPdef, Finset.sum_filter]
      have hsplit : ∑ k ∈ univ.filter (fun k : KapI ν r1 E => k.1 ∈ TT \ oddT TT), β k ≤
          ∑ k ∈ univ.filter (fun k : KapI ν r1 E => (k.1, k.2.2) ∈ P), β k +
          ∑ k ∈ univ.filter (fun k : KapI ν r1 E => k.1.val % 2 = 0 ∧ k.2.2 ∈ J), β k := by
        simp only [Finset.sum_filter]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_le_sum (fun k _ => ?_)
        by_cases h1 : k.1 ∈ TT \ oddT TT
        · have hev : k.1.val % 2 = 0 := by
            simp only [oddT, Finset.mem_sdiff, Finset.mem_filter, not_and] at h1
            have := h1.2 h1.1
            omega
          rw [if_pos h1]
          by_cases hb : k.2.2 ∈ J
          · rw [if_pos (show k.1.val % 2 = 0 ∧ k.2.2 ∈ J from ⟨hev, hb⟩)]
            exact Nat.le_add_left _ _
          · rw [if_pos (show (k.1, k.2.2) ∈ P by simp [hPdef, hev, hb])]
            exact Nat.le_add_right _ _
        · rw [if_neg h1]
          exact Nat.zero_le _
      rw [hN]
      omega
    have hsumβ : ∑ s ∈ TT, ∑ e' ∈ range E, (iN β s e' : ℝ) = ∑ k, (β k : ℝ) := by
      exact_mod_cast sum_iN_tops β TT hβ
    have keyR : ∑ φ, (α φ : ℝ) + ∑ s ∈ TT \ oddT TT, ∑ e' ∈ range E, (iN β s e' : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast keyB
    have core := hB (2 * ν) (p : ℝ) TT (oddT TT) (fun s => (alN e s : ℝ)) (fun s => (capN sf s : ℝ))
      (deLoss p r0 r1 TT (alN e) (lsN l sf))
      ((N : ℝ) + gamP p * ∑ s ∈ TT, (alN e s : ℝ) - ∑ φ, (α φ : ℝ) - ∑ k, (β k : ℝ) -
        deLoss p r0 r1 TT (alN e) (lsN l sf))
      ((N : ℝ) - ∑ φ, (α φ : ℝ)) (fun s e' => (iN β s e' : ℝ)) (range E)
      hp1 (Finset.filter_subset _ _) (fun s => Nat.cast_nonneg _) (fun s => Nat.cast_nonneg _)
      (fun s e' => Nat.cast_nonneg _) (fun s e' he => by simp [iN_of_not_mem β s e' he])
      (by beta_reduce; linarith [hsumβ]) (by beta_reduce; linarith [keyR])
      (fun s _ e' => iN_le_min hC hp ξ α β e l sf T I h3 h4 s e')
    beta_reduce at core
    linarith [core]
end Formalism.InvariantFactorPaths.G7
