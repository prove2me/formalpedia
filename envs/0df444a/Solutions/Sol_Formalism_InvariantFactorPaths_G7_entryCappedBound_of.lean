-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.entryCappedBound_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:46:33.455244+00:00
-- url     : https://prove2.me/submissions/3f1572f3-d498-4b4d-87e9-0decc8cecdff

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_GrowthSums_StatementG
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EntryATwoAndB
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ParitySumsOverFilteredPairs_sum_filter_fst
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ParitySumsOverFilteredPairs_phi_parity
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ParitySumsOverFilteredPairs_iN_of_not_mem
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ParitySumsOverFilteredPairs_sum_iN
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ParitySumsOverFilteredPairs_pay_le
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ParitySumsOverFilteredPairs_iN_le_min
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ParitySumsOverFilteredPairs_sum_iN_tops

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
theorem _root_.solution (hS : EntryStar) (hC : HitsCapPos) (hA : Formalism.GrowthSums.CappedGainSubLE) : EntryCappedBound := by
  intro K _ _ p ν r0 r1 C _ u F TT ξ e l sf T I hH
  have hH' := hH
  obtain ⟨-, hp2, -, -, -, -, -, -⟩ := hH'
  have hp : 0 < p := by omega
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  rcases hS K p ν r0 r1 C u F TT ξ e l sf T I hH with h0 | ⟨E, α, β, hα, hβ, h3, h4, hn⟩
  · rw [h0, norm_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg p) _
  · refine le_trans hn (Real.rpow_le_rpow_of_exponent_le hp1.le ?_)
    set P2 : Finset (TpV ν r1) := univ.filter (fun x : TpV ν r1 => x.1 ∈ TT \ oddT TT) with hP2def
    have hP : ∀ φ, α φ ≠ 0 → (pairFirst φ, φ.2.2.2.2) ∈ P2 ∨ (pairSecond φ, φ.2.2.2.2) ∈ P2 := by
      intro φ hφ
      obtain ⟨h1, h2⟩ := hα φ hφ
      have hpar := phi_parity φ
      simp only [hP2def, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, oddT, not_and]
      by_cases hv : (pairFirst φ).val % 2 = 1
      · right
        exact ⟨h2, fun _ => by show ¬ (pairSecond φ).val % 2 = 1; omega⟩
      · left
        exact ⟨h1, fun _ => hv⟩
    have key : ∑ φ, α φ + ∑ s ∈ TT \ oddT TT, ∑ e' ∈ range E, iN β s e' ≤
        ∑ s ∈ TT \ oddT TT, alN e s := by
      rw [sum_iN β (TT \ oddT TT)]
      have hfil : univ.filter (fun k : KapI ν r1 E => k.1 ∈ TT \ oddT TT) =
          univ.filter (fun k : KapI ν r1 E => (k.1, k.2.2) ∈ P2) := by
        ext k
        simp [hP2def]
      rw [hfil]
      refine le_trans (pay_le hp α β e h3 P2 hP) (le_of_eq ?_)
      exact sum_filter_fst (A := ZMod (2 * ν)) (B := Fin r1) (TT \ oddT TT) e
    have hsumβ : ∑ s ∈ TT, ∑ e' ∈ range E, (iN β s e' : ℝ) = ∑ k, (β k : ℝ) := by
      exact_mod_cast sum_iN_tops β TT hβ
    have keyR : ∑ φ, (α φ : ℝ) + ∑ s ∈ TT \ oddT TT, ∑ e' ∈ range E, (iN β s e' : ℝ) ≤
        ∑ s ∈ TT \ oddT TT, (alN e s : ℝ) := by
      exact_mod_cast key
    have core := hA (2 * ν) (p : ℝ) TT (oddT TT) (fun s => (alN e s : ℝ)) (fun s => (capN sf s : ℝ))
      (deLoss p r0 r1 TT (alN e) (lsN l sf))
      (gamP p * ∑ s ∈ TT, (alN e s : ℝ) - ∑ φ, (α φ : ℝ) - ∑ k, (β k : ℝ) -
        deLoss p r0 r1 TT (alN e) (lsN l sf))
      (∑ φ, (α φ : ℝ)) (fun s e' => (iN β s e' : ℝ)) (range E)
      hp1 (Finset.filter_subset _ _) (fun s => Nat.cast_nonneg _) (fun s => Nat.cast_nonneg _)
      (fun s e' => Nat.cast_nonneg _) (fun s e' he => by simp [iN_of_not_mem β s e' he])
      (by beta_reduce; linarith [hsumβ]) (by beta_reduce; exact keyR)
      (fun s _ e' => iN_le_min hC hp ξ α β e l sf T I h3 h4 s e')
    beta_reduce at core
    linarith [core]
end Formalism.InvariantFactorPaths.G7
