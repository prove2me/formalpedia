-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.EGauss.reduce
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:59:07.62655+00:00
-- url     : https://prove2.me/submissions/f5835d87-1e69-45ae-a2df-b639febf996b

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementG
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_GField
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FJEval
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Labels
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_KOneConsequence
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EGauss
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_EGauss_map_hhS
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_EGauss_inClass_map
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_EGauss_struct
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_EGauss_norm_p_complex
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_bddAbove_norm_coeff
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_residuallyGenericExists
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_ringMap_minorProd
import Theorems.Thm_P2M_Formalism_DworkPowerSeriesWeights_eval__jetPairPoly_5113198bcf9c


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
open Formalism.DworkPowerSeriesWeights (Integral frameJet jetPair minorProd)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)
open Formalism.InvariantFactorPaths.G7.EGauss
namespace Formalism.InvariantFactorPaths.G7.EGauss
theorem _root_.solution (p : ℕ) [Fact p.Prime] (ν r0 r1 : ℕ) [NeZero ν] (u : ZMod (2 * ν) → ℂ_[p])
    (F : MvPowerSeries (ZV ν r0 r1) ℂ_[p]) (TT : Finset (ZMod (2 * ν))) (colN : ZMod (2 * ν) → ℕ)
    (hts : ∀ s, Fin (colN s) → ℕ) (hp : ∀ s c, hts s c ≤ r0) (I : ∀ s c, Fin (hts s c) → Fin r1)
    (hp2 : 2 < p) (hu : ∀ s, ‖u s‖ ≤ 1) (hF : InClass (p : ℂ_[p]) (hhS p u) F) :
    ∃ (K : Type) (_ : NormedField K), IsUltrametricDist K ∧
      ∃ (C : ℕ) (u' : ZMod (2 * ν) → K) (F' : MvPowerSeries (ZV ν r0 r1) K)
        (ξ : ZMod (2 * ν) → Fin r0 → K) (e : TpV ν r1 → ℕ) (l : Fin C → ℕ)
        (sf : Fin C → ZMod (2 * ν)) (T : ∀ c, Fin (l c) → Fin r0 → K)
        (I' : ∀ c, Fin (l c) → Fin r1),
        EntryHyp p ν r0 r1 C u' F' TT ξ e l T ∧
        (∀ n, ‖MvPolynomial.coeff n (frameJet colN hts hp I F)‖ ≤
          ‖jetPair (entryOp ξ e l sf T I') F'‖) ∧
        alN e = alG TT colN hts ∧ capN sf = capG TT colN hts ∧ lsN l sf = lsG TT colN hts ∧
        ∀ (J : Finset (Fin r1)) (i : ℕ), 1 ≤ i →
          (∑ x : TpV ν r1, (if (x.1.val % 2 = 0 ∧ x.2 ∉ J) ∨ (x.1.val % 2 = 1 ∧ x.2 ∈ J)
              then e x else 0) +
            ∑ c, (if (sf c).val % 2 = 1 then ((univ.image (I' c)) ∩ J).card else 0)) ≤
          ∑ s : ZMod (2 * ν), ∑ c : Fin (colN s),
            (if s.val % 2 = 0 then min (hts s c) i - ((univ.image (I s c)) ∩ J).card
            else ((univ.image (I s c)) ∩ J).card) := by
  have hpp : p.Prime := Fact.out
  obtain ⟨K, instK, hult, hchar, φ, Y, hφ, hgauss, hgen⟩ :=
    Formalism.DworkPowerSeriesWeights.residuallyGenericExists p (ZMod (2 * ν) × Fin r0 × Fin r0)
  have hnp : ‖(p : K)‖ = (p : ℝ)⁻¹ := by rw [← map_natCast φ, hφ, norm_p_complex]
  have hY : ∀ y, ‖Y y‖ ≤ 1 := by
    intro y
    have h := hgauss (MvPolynomial.X y)
    rw [MvPolynomial.eval₂_X] at h
    rw [h]
    refine ciSup_le fun m => ?_
    classical
    rw [MvPolynomial.coeff_X]
    split_ifs <;> simp
  obtain ⟨C, ξ, e, l, sf, T, I', hop, hξ, hT, hal, hcap, hls, hB⟩ :=
    struct TT colN hts hp I Y
  refine ⟨K, instK, hult, C, fun s => φ (u s), MvPowerSeries.map φ F, ξ, e, l, sf, T, I',
    ⟨hpp, hp2, hnp, fun s => by rw [hφ]; exact hu s, ?_, ?_, ?_, ?_⟩, ?_, hal, hcap, hls, hB⟩
  · have h := inClass_map φ hφ _ _ _ hF
    rwa [map_natCast, map_hhS] at h
  · intro s a
    obtain ⟨y, h⟩ := hξ s a
    rw [h]
    exact hY y
  · intro c i a
    obtain ⟨y, h⟩ := hT c i a
    rw [h]
    exact hY y
  · intro x hx
    have h : alN e x.1 = 0 := by
      rw [hal]
      unfold alG
      rw [if_neg hx]
    unfold alN at h
    exact (Finset.sum_eq_zero_iff.1 h) x.2 (Finset.mem_univ _)
  · intro n
    refine le_trans (le_ciSup (Formalism.DworkPowerSeriesWeights.bddAbove_norm_coeff _) n) ?_
    rw [← hgauss, ← hop]
    unfold frameJet
    rw [Formalism.DworkPowerSeriesWeights.eval₂_jetPairPoly, map_prod]
    simp only [Formalism.DworkPowerSeriesWeights.ringMap_minorProd, map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_X,
      MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
    exact le_rfl
end Formalism.InvariantFactorPaths.G7.EGauss
