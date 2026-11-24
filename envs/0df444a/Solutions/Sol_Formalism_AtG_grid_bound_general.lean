-- Prove2me | solution 1 for Formalism.AtG.grid_bound_general
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:24:05.769882+00:00
-- url     : https://prove2.me/submissions/20f387db-a16f-4fcb-972b-75a71a7b7ebd

import Definitions.Def_Formalism_LocalToGlobal_ExponentGrids_ScaledCoordinatesValuationLemma
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TruncatedLatticeHolds
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_KappaNormalise
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondComplementParameterBounds
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_PairingDivisors_PairingDivisorProofs_Height
import Definitions.Def_Formalism_PairingDivisors_PairingDivisorProofs_SumValuationNat
import Definitions.Def_Formalism_PairingDivisors_PairingDivisorProofs_ValAdd
import Definitions.Def_Formalism_TowerValuationBounds_TowerValuationProofs_SumAdditiveCharacterEqZero
import Definitions.Def_Lemmata_PlaneOverMembership_PlOverOfMem
import Definitions.Def_Formalism_LocalToGlobal_ExponentGrids_ExponentGridsProofs_FrameHeightOfDualSlope
import Theorems.Thm_Formalism_AtG_grid_ell_bound
import Theorems.Thm_Formalism_AtG_partial_nat
import Theorems.Thm_Formalism_AtG_partial_ht
import Theorems.Thm_Formalism_AtG_j3Wt
import Theorems.Thm_Formalism_PairingDivisionLocalBalance_lw_nonneg
import Theorems.Thm_Formalism_PairingDivisionLocalBalance_vw_natCast_nonneg
import Theorems.Thm_Formalism_PairingDivisionLocalBalance_vw_prod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw lw PlOver meanLog)
open Formalism.PairingDivisionLocalBalance (Pl wt HtLe meanInf)
open Formalism.HN (muMaxDef muMinDef htMap dualLat dualFrame)
noncomputable section
open Formalism Formalism.AtG
namespace Formalism.AtG
theorem _root_.solution : GridHeightBound := by
  intro K _ _ _ _ Sq m N dl S Se N0 rr zA zA' zT zTd gT ch dd hh yy S0 cc ee qq B BN0 Bδ W0
    hdl hS hSe hrr hdd hddN hyy hcc hsq hA hT hTd hN0 hBδ
  obtain ⟨ell, hell⟩ := grid_ell_bound K
  classical
  have he : ∀ w : Pl K, (0 : ℝ) < (vw w (ell w : K) : ℝ) := by
    intro w
    have := (hell w).2
    unfold Formalism.DivisionValues.PlOver at this
    exact_mod_cast this
  have hlam : ∀ (w : Pl K) (t : ℝ),
      lw w * (vw w (ell w : K) : ℝ) * (t / (vw w (ell w : K) : ℝ)) = lw w * t := by
    intro w t
    have := (he w).ne'
    field_simp
  have habs : ∀ (w : Pl K) (t : ℝ),
      |t / (vw w (ell w : K) : ℝ)| = |t| / (vw w (ell w : K) : ℝ) := by
    intro w t
    rw [abs_div, abs_of_pos (he w)]
  have hbud : ∀ P : Finset ℕ, (∀ l ∈ P, l.Prime) →
      ∑ l ∈ P, (if l ∈ S then N0 l else 0) * Real.log l ≤ BN0 := by
    intro P _
    refine le_trans ?_ hN0
    have h1 : ∑ l ∈ P, (if l ∈ S then N0 l else 0) * Real.log l =
        ∑ l ∈ P.filter (· ∈ S), N0 l * Real.log l := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro l _
      split_ifs <;> simp
    rw [h1]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro l hl
      exact (Finset.mem_filter.1 hl).2
    · intro l hl _
      exact mul_nonneg (hS l hl).2 (Real.log_natCast_nonneg l)
  have key := Formalism.ValuationGridEstimates.grid_squares_bound (Pl K) Sq m N
    (fun w => lw w * (vw w (ell w : K) : ℝ)) (fun w => dl w / (vw w (ell w : K) : ℝ)) ell
    (fun l => if l ∈ S then N0 l else 0)
    (fun w ij => (vw w (rr w ij) : ℝ) / (vw w (ell w : K) : ℝ))
    (fun w ij => (vw w (zA ij) : ℝ) / (vw w (ell w : K) : ℝ))
    (fun w ij => (vw w (zA' ij) : ℝ) / (vw w (ell w : K) : ℝ))
    (fun w ij s => ((vw w (zT ij s) + gT ij s w : ℤ) : ℝ) / (vw w (ell w : K) : ℝ))
    (fun w ij b s => ((vw w (zTd ij b s) + gT ij s w : ℤ) : ℝ) / (vw w (ell w : K) : ℝ))
    ch dd hh yy S0 cc ee qq
    (fun w s => (vw w (qq s : K) : ℝ) / (vw w (ell w : K) : ℝ)) B (BN0 + 1) Bδ W0
    (fun w => mul_nonneg (Formalism.PairingDivisionLocalBalance.lw_nonneg w) (he w).le)
    (fun w => div_nonneg (hdl w) (he w).le)
    (fun l => by
      show (0 : ℝ) ≤ if l ∈ S then N0 l else 0
      split_ifs with h
      · exact (hS l h).2
      · exact le_rfl)
    (fun w s => div_nonneg (by exact_mod_cast Formalism.PairingDivisionLocalBalance.vw_natCast_nonneg w (qq s)) (he w).le)
    (fun w => (hell w).1)
    (fun l F hF => by
      refine le_trans (le_of_eq ?_) (partial_nat K l F)
      apply Finset.sum_congr rfl
      intro w hw
      rw [hF w hw])
    hdd hddN hyy hcc
    (fun w hw ij => by
      have hE := he w
      have h0 := hsq w hw ij
      rw [j3Wt K ell hell S N0 (fun l hl => (hS l hl).1) w,
        j3Wt K ell hell Se (fun l => 1 / (l : ℝ) ^ 2) hSe w] at h0
      simp only [habs]
      have hs1 : ∑ s ∈ Icc (1 : ℤ) (hh ij),
          (|((vw w (zT ij s) + gT ij s w : ℤ) : ℝ)| / (vw w (ell w : K) : ℝ) +
            |((vw w (zTd ij (ch w) s) + gT ij s w : ℤ) : ℝ)| / (vw w (ell w : K) : ℝ)) =
          (∑ s ∈ Icc (1 : ℤ) (hh ij), (|((vw w (zT ij s) + gT ij s w : ℤ) : ℝ)| +
            |((vw w (zTd ij (ch w) s) + gT ij s w : ℤ) : ℝ)|)) / (vw w (ell w : K) : ℝ) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro s _
        ring
      have hs2 : ∑ s ∈ S0, (cc s : ℝ) * ((vw w (qq s : K) : ℝ) / (vw w (ell w : K) : ℝ)) =
          (∑ s ∈ S0, (cc s : ℝ) * (vw w (qq s : K) : ℝ)) / (vw w (ell w : K) : ℝ) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro s _
        ring
      rw [hs1, hs2, div_le_iff₀ hE]
      refine le_trans h0 ?_
      generalize (∑ s ∈ Icc (1 : ℤ) (hh ij), (|((vw w (zT ij s) + gT ij s w : ℤ) : ℝ)| +
            |((vw w (zTd ij (ch w) s) + gT ij s w : ℤ) : ℝ)|)) = T1
      generalize (∑ s ∈ S0, (cc s : ℝ) * (vw w (qq s : K) : ℝ)) = T2
      generalize (vw w (ell w : K) : ℝ) = E at hE ⊢
      have hε : (if ell w ∈ Se then 1 / ((ell w : ℕ) : ℝ) ^ 2 else 0) ≤ (((ell w : ℕ) : ℝ) ^ 2)⁻¹ := by
        split_ifs
        · rw [one_div]
        · positivity
      have hdd0 : (0 : ℝ) ≤ (dd ij : ℝ) := Nat.cast_nonneg _
      have h5 : (dd ij : ℝ) * ((if ell w ∈ Se then 1 / ((ell w : ℕ) : ℝ) ^ 2 else 0) * E) ≤
          (dd ij : ℝ) * ((((ell w : ℕ) : ℝ) ^ 2)⁻¹ * E) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hε hE.le) hdd0
      have h6 : (|(vw w (zA ij) : ℝ)| / E + |(vw w (zA' ij) : ℝ)| / E + 4 * (T1 / E) +
          (dd ij : ℝ) * ((if ell w ∈ S then N0 (ell w) else 0) + (((ell w : ℕ) : ℝ) ^ 2)⁻¹) +
          6 * (dl w / E) + (yy ij : ℝ) * (2 * (T2 / E))) * E =
          |(vw w (zA ij) : ℝ)| + |(vw w (zA' ij) : ℝ)| + 4 * T1 +
          (dd ij : ℝ) * ((if ell w ∈ S then N0 (ell w) else 0) * E + (((ell w : ℕ) : ℝ) ^ 2)⁻¹ * E) +
          6 * dl w + (yy ij : ℝ) * (2 * T2) := by
        have := hE.ne'
        field_simp
      rw [h6]
      linarith)
    (fun ij F => by
      refine le_trans (le_of_eq ?_) (partial_ht (hA ij).1 F)
      apply Finset.sum_congr rfl
      intro w _
      simp only [habs, hlam, add_zero])
    (fun ij F => by
      refine le_trans (le_of_eq ?_) (partial_ht (hA ij).2 F)
      apply Finset.sum_congr rfl
      intro w _
      simp only [habs, hlam, add_zero])
    (fun ij s F => by
      refine le_trans (le_of_eq ?_) (partial_ht (hT ij s) F)
      apply Finset.sum_congr rfl
      intro w _
      simp only [habs, hlam])
    (fun ij b s F => by
      refine le_trans (le_of_eq ?_) (partial_ht (hTd ij b s) F)
      apply Finset.sum_congr rfl
      intro w _
      simp only [habs, hlam])
    (Formalism.ValuationGridEstimates.prime_budget_bound (fun l => if l ∈ S then N0 l else 0) BN0 hbud)
    (fun F => by
      refine le_trans (le_of_eq ?_) (hBδ F)
      apply Finset.sum_congr rfl
      intro w _
      simp only [hlam])
    (fun s _ F => by
      refine le_trans (le_of_eq ?_) (partial_nat K (qq s) F)
      apply Finset.sum_congr rfl
      intro w _
      simp only [hlam])
  unfold gridBudget
  refine le_trans (le_of_eq ?_) key
  apply Finset.sum_congr rfl
  intro w _
  rw [Formalism.PairingDivisionLocalBalance.vw_prod w Finset.univ (fun ij => rr w ij) (fun ij _ => hrr w ij), ← Finset.sum_div, hlam]
  push_cast
  rfl
end Formalism.AtG
