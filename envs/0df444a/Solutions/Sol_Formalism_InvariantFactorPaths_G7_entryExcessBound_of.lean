-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.entryExcessBound_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:00:50.849884+00:00
-- url     : https://prove2.me/submissions/5905e2be-226f-4de6-9f82-7e0303bbe8be

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EntryAOneParity
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ValuationParity_charge_exists
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ValuationParity_sum_charge
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ValuationParity_level_le

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
open ValuationParity
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution (hS : EntryStar) (hC : HitsCapPos) (hA : ExcessGainBound) (hL : ChargeLemma) : EntryExcessBound := by
  intro K _ _ p ν r0 r1 C _ u F TT ξ e l sf T I hyp
  rcases hS K p ν r0 r1 C u F TT ξ e l sf T I hyp with h0 | ⟨E, α, β, hαTT, hβTT, hτ, hhasse, hbound⟩
  · rw [h0, norm_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  classical
  have hp : 2 < p := hyp.2.1
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  choose sφ s'φ hor hodd hpar hle using fun φ : PhiI ν r0 r1 E => charge_exists hL p (by omega) φ
  obtain ⟨c, hcdef⟩ : ∃ c : PhiI ν r0 r1 E → ZMod (2 * ν) × ℕ,
      ∀ φ, c φ = (sφ φ, ((s'φ φ - sφ φ).val - 1) / 2) := ⟨_, fun _ => rfl⟩
  have hc2 : ∀ φ, 2 * (c φ).2 + 1 = (s'φ φ - sφ φ).val := by
    intro φ
    have := hodd φ
    rw [hcdef]
    omega
  have hc1 : ∀ φ, (c φ).1 = sφ φ := fun φ => by rw [hcdef]
  have hc : ∀ φ, p ^ (2 * (c φ).2 + 1) ≤ dAof p φ ((c φ).1, φ.2.2.2.2) := fun φ => by
    rw [hc2, hc1]
    exact hle φ
  have hsTT : ∀ φ, α φ ≠ 0 → sφ φ ∈ TT ∧ s'φ φ ∈ TT := by
    intro φ hα
    obtain ⟨h1, h2⟩ := hαTT φ hα
    rcases hor φ with ⟨hs1, hs2⟩ | ⟨hs1, hs2⟩
    · exact ⟨hs1 ▸ h1, hs2 ▸ h2⟩
    · exact ⟨hs1 ▸ h2, hs2 ▸ h1⟩
  obtain ⟨Ee, hEe⟩ : ∃ Ee : Finset ℕ, Ee = (Finset.univ.image fun φ => (c φ).2) ∪
      (Finset.univ.image fun k : KapI ν r1 E => k.2.1.val) := ⟨_, rfl⟩
  obtain ⟨chN, hchN⟩ : ∃ chN : ZMod (2 * ν) → ℕ → ℕ,
      ∀ s e', chN s e' = ∑ φ, if c φ = (s, e') then α φ else 0 := ⟨_, fun _ _ => rfl⟩
  obtain ⟨iN, hiN⟩ : ∃ iN : ZMod (2 * ν) → ℕ → ℕ,
      ∀ s e', iN s e' = ∑ k : KapI ν r1 E, if (k.1, k.2.1.val) = (s, e') then β k else 0 :=
    ⟨_, fun _ _ => rfl⟩
  have hlev : ∀ s e', p ^ (2 * e' + 1) * (chN s e' + iN s e') ≤ alN e s := fun s e' => by
    rw [hchN, hiN]
    exact level_le p e α β hτ c hc s e'
  have hcapN : ∀ s e', iN s e' ≤ capN sf (s + ((2 * e' + 1 : ℕ) : ZMod (2 * ν))) := by
    intro s e'
    by_contra hlt
    push_neg at hlt
    apply hhasse
    refine hC K (ZMod (2 * ν)) (KapI ν r1 E) r0 r1 C l sf T I
      (fun k => k.1 + ((2 * k.2.1.val + 1 : ℕ) : ZMod (2 * ν)))
      (fun k a => ξ k.1 a ^ (p ^ (2 * k.2.1.val + 1))) (fun k => k.2.2)
      (Finset.univ.filter fun k : KapI ν r1 E => (k.1, k.2.1.val) = (s, e'))
      (s + ((2 * e' + 1 : ℕ) : ZMod (2 * ν))) ?_ ?_ β ?_
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq] at hk
      rw [hk.1, hk.2]
    · intro k hk k' hk'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq] at hk hk'
      funext a
      rw [hk.1, hk.2, hk'.1, hk'.2]
    · rw [hiN, ← Finset.sum_filter] at hlt
      exact hlt
  have hcoreA := hA (2 * ν) (p : ℝ) TT (dSet TT) (fun s => (alN e s : ℝ)) (fun s => (capN sf s : ℝ))
    (deLoss p r0 r1 TT (alN e) (lsN l sf))
    (gamP p * ∑ s ∈ TT, (alN e s : ℝ) - (∑ φ, (α φ : ℝ)) - (∑ k, (β k : ℝ)) -
      deLoss p r0 r1 TT (alN e) (lsN l sf))
    (fun s e' => (iN s e' : ℝ)) (fun s e' => (chN s e' : ℝ)) Ee hp1
    (fun _ => Nat.cast_nonneg _) (fun _ => Nat.cast_nonneg _) (fun _ _ => Nat.cast_nonneg _)
    (fun _ _ => Nat.cast_nonneg _) ?hE ?hD ?hmain ?h6 ?h7
  case hE =>
    intro s e' he'
    constructor
    · show (iN s e' : ℝ) = 0
      rw [hiN, Nat.cast_eq_zero]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [if_neg]
      intro hk
      apply he'
      simp only [Prod.mk.injEq] at hk
      rw [hEe, ← hk.2]
      exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
    · show (chN s e' : ℝ) = 0
      rw [hchN, Nat.cast_eq_zero]
      refine Finset.sum_eq_zero fun φ _ => ?_
      rw [if_neg]
      intro hφ
      apply he'
      have he2 : (c φ).2 = e' := by rw [hφ]
      rw [hEe, ← he2]
      exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  case hD =>
    intro s e' hn
    show (chN s e' : ℝ) = 0
    rw [hchN, Nat.cast_eq_zero]
    refine Finset.sum_eq_zero fun φ _ => ?_
    split_ifs with hφ
    · by_contra hα
      apply hn
      obtain ⟨h1, h2⟩ := hsTT φ hα
      have hs : sφ φ = s := by rw [← hc1, hφ]
      have he : (c φ).2 = e' := by rw [hφ]
      rw [dSet, Finset.mem_image]
      refine ⟨s'φ φ, Finset.mem_filter.mpr ⟨h2, ?_⟩, ?_⟩
      · rw [← hs]
        exact hpar φ
      · rw [← hs, ← hc2, he]
    · rfl
  case hmain =>
    have hsumch : ∑ s ∈ TT, ∑ e' ∈ Ee, (chN s e' : ℝ) = ∑ φ, (α φ : ℝ) := by
      have h := sum_charge TT Ee c (fun φ => α φ) (fun φ hα => ⟨by rw [hc1]; exact (hsTT φ hα).1,
        by rw [hEe]; exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))⟩)
      simp only [← hchN] at h
      exact_mod_cast h
    have hsumi : ∑ s ∈ TT, ∑ e' ∈ Ee, (iN s e' : ℝ) = ∑ k, (β k : ℝ) := by
      have h := sum_charge TT Ee (fun k : KapI ν r1 E => (k.1, k.2.1.val)) (fun k => β k)
        (fun k hk => ⟨hβTT k hk, by
          rw [hEe]; exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))⟩)
      simp only [← hiN] at h
      exact_mod_cast h
    show gamP (p : ℝ) * ∑ s ∈ TT, (alN e s : ℝ) - ∑ s ∈ TT, ∑ e' ∈ Ee, (chN s e' : ℝ) -
      ∑ s ∈ TT, ∑ e' ∈ Ee, (iN s e' : ℝ) - deLoss p r0 r1 TT (alN e) (lsN l sf) ≤ _
    rw [hsumch, hsumi]
  case h6 =>
    intro s _ e' _
    show (chN s e' : ℝ) + (iN s e' : ℝ) ≤ (alN e s : ℝ) / (p : ℝ) ^ (2 * e' + 1)
    rw [le_div_iff₀ (pow_pos (by positivity) _)]
    have h := hlev s e'
    rw [mul_comm] at h
    exact_mod_cast h
  case h7 =>
    intro s _ e' _
    show (iN s e' : ℝ) ≤ min ((alN e s : ℝ) / (p : ℝ) ^ (2 * e' + 1))
      ((capN sf (s + ((2 * e' + 1 : ℕ) : ZMod (2 * ν))) : ℝ))
    apply le_min
    · rw [le_div_iff₀ (pow_pos (by positivity) _)]
      have h := hlev s e'
      have h' : iN s e' * p ^ (2 * e' + 1) ≤ alN e s := by
        rw [mul_comm]
        exact le_trans (Nat.mul_le_mul_left _ (Nat.le_add_left _ _)) h
      exact_mod_cast h'
    · exact_mod_cast hcapN s e'
  refine le_trans hbound (Real.rpow_le_rpow_of_exponent_le hp1.le ?_)
  linarith [hcoreA]
end Formalism.InvariantFactorPaths.G7
