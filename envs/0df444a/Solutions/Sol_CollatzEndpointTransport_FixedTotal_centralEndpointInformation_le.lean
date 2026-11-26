-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.centralEndpointInformation_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:43:39.951282+00:00
-- url     : https://prove2.me/submissions/480a99ef-df45-4644-a3ec-3e289844d9ff

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Definitions.Def_CollatzEndpointTransport_Linear_FiniteFiberMixture
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalActualEndpointMoment
import Definitions.Def_CollatzEndpointTransport_Common_TerrasPrefixEvents
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_mixedFiberRenyi_le
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_central_cohort_normalized_le
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_sourceOddLevel
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralMomentConstant_pos
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedRenyiMoment_nonneg
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedSourceWeight_mul_fixedRenyiMoment_le
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedSourceWeight_nonneg
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_normalizedReverseLift_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseLiftNumerator_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseLiftNumerator_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseMomentMajorant_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseMomentMajorant_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumerator_prependOne
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_wordCorrectionFrom_nil
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_card_positivePrefix
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_mem_basePullback
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_mem_collatzPullback
import Theorems.Thm_CollatzEndpointTransport_Terras_integerCorrection_zero
attribute [local simp] CollatzEndpointTransport.FixedTotal.encodeBlocks_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.encodeBlocks_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.normalizedReverseLift_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.reverseLiftNumerator_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.reverseLiftNumerator_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.reverseMomentMajorant_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.reverseMomentMajorant_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumerator_prependOne
attribute [local simp] CollatzEndpointTransport.FixedTotal.wordCorrectionFrom_nil
attribute [local simp] CollatzEndpointTransport.QuantitativeDensity.card_positivePrefix
attribute [local simp] CollatzEndpointTransport.QuantitativeDensity.mem_basePullback
attribute [local simp] CollatzEndpointTransport.QuantitativeDensity.mem_collatzPullback
attribute [local simp] CollatzEndpointTransport.Terras.integerCorrection_zero



set_option autoImplicit false
set_option maxHeartbeats 4000000
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.centralShellCompositionDecidableEq
attribute [local instance] CollatzEndpointTransport.FixedTotal.centralRenyiAdmissibleDecidable
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {M : ℕ} {theta eta : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2) :
    centralEndpointInformation M theta eta ≤
      (3 : ℝ) ^ theta * centralMomentConstant theta eta *
        (M + 1 : ℝ) ^ 6 := by
  classical
  have hconst0 := (centralMomentConstant_pos
    htheta0 htheta1 heta0 heta1).le
  have hMpow : (M : ℝ) ^ theta ≤ (M + 1 : ℝ) := by
    by_cases hM0 : M = 0
    · subst M
      simp [htheta0.ne']
    · have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hM0
      calc
        (M : ℝ) ^ theta ≤ (M : ℝ) ^ 1 :=
          Real.rpow_le_rpow_of_exponent_le hM1 htheta1.le
        _ = (M : ℝ) := Real.rpow_one _
        _ ≤ (M + 1 : ℝ) := by push_cast; linarith
  unfold centralEndpointInformation
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ M)).2
  calc
    (∑ s ∈ Finset.range (M + 1),
        centralLevelRenyiInformation M s theta eta) ≤
      ∑ _s ∈ Finset.range (M + 1),
        (3 : ℝ) ^ theta * (M : ℝ) ^ theta *
          ((M : ℝ) *
            ((2 : ℝ) ^ M * centralMomentConstant theta eta * (M + 1))) := by
      apply Finset.sum_le_sum
      intro s hs
      have hsM : s ≤ M := Nat.le_of_lt_succ (Finset.mem_range.mp hs)
      have hmix := mixedFiberRenyi_le
        (Finset.univ : Finset (Fin M))
        (centralLevelCohortSet M s theta eta)
        (fun u => cohortEndpoint u) htheta0
      have hlevelCard : 0 < (sourceOddLevel M s).card := by
        rw [card_sourceOddLevel]
        exact Nat.choose_pos hsM
      unfold centralLevelRenyiInformation
      let scale := (((3 : ℝ) ^ (s + 1)) ^ theta /
        (((sourceOddLevel M s).card : ℝ) ^ theta))
      have hscale0 : 0 ≤ scale := by
        dsimp [scale]
        positivity
      have hscaled :
          scale *
              (∑ y ∈ centralLevelEndpointSet M s theta eta,
                (centralLevelFiberCard M s theta eta y : ℝ) ^ (1 + theta)) ≤
            scale *
              ((M : ℝ) ^ theta *
                ∑ u : Fin M,
                  ∑ c ∈ centralLevelCohortSet M s theta eta u,
                    ((mapFiberCardAt
                      (centralLevelCohortSet M s theta eta u)
                      (cohortEndpoint u) c : ℕ) : ℝ) ^ theta) := by
        simpa [scale, centralLevelEndpointSet, centralLevelFiberCard] using
          mul_le_mul_of_nonneg_left hmix hscale0
      calc
        ((((3 : ℝ) ^ (s + 1)) ^ theta /
              (((sourceOddLevel M s).card : ℝ) ^ theta)) *
            ∑ y ∈ centralLevelEndpointSet M s theta eta,
              (centralLevelFiberCard M s theta eta y : ℝ) ^ (1 + theta)) ≤
          (((3 : ℝ) ^ (s + 1)) ^ theta /
              (((sourceOddLevel M s).card : ℝ) ^ theta)) *
            ((M : ℝ) ^ theta *
              ∑ u : Fin M, ∑ c ∈ centralLevelCohortSet M s theta eta u,
                ((mapFiberCardAt
                  (centralLevelCohortSet M s theta eta u)
                  (cohortEndpoint u) c : ℕ) : ℝ) ^ theta) := by
          simpa [scale] using hscaled
        _ = (3 : ℝ) ^ theta * (M : ℝ) ^ theta *
            ∑ u : Fin M,
              ((((3 : ℝ) ^ s) ^ theta /
                  (((sourceOddLevel M s).card : ℝ) ^ theta)) *
                ∑ c ∈ centralLevelCohortSet M s theta eta u,
                  ((mapFiberCardAt
                    (centralLevelCohortSet M s theta eta u)
                    (cohortEndpoint u) c : ℕ) : ℝ) ^ theta) := by
          rw [pow_succ, Real.mul_rpow (by positivity) (by positivity)]
          rw [← Finset.mul_sum]
          ring
        _ ≤ (3 : ℝ) ^ theta * (M : ℝ) ^ theta *
            ∑ u : Fin M,
              (if CentralRenyiAdmissible (M - (u : ℕ)) s theta eta then
                ((fixedSet (M - (u : ℕ)) s).card : ℝ) *
                  fixedRenyiMoment (M - (u : ℕ)) s theta
               else 0) := by
          gcongr with u
          exact central_cohort_normalized_le u htheta0 htheta1
        _ ≤ (3 : ℝ) ^ theta * (M : ℝ) ^ theta *
            ((M : ℝ) *
              ((2 : ℝ) ^ M * centralMomentConstant theta eta * (M + 1))) := by
          apply mul_le_mul_of_nonneg_left _
            (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
              (Real.rpow_nonneg (Nat.cast_nonneg M) _))
          calc
            (∑ u : Fin M,
                (if CentralRenyiAdmissible (M - (u : ℕ)) s theta eta then
                  ((fixedSet (M - (u : ℕ)) s).card : ℝ) *
                    fixedRenyiMoment (M - (u : ℕ)) s theta
                 else 0)) ≤
              ∑ _u : Fin M,
                ((2 : ℝ) ^ M * centralMomentConstant theta eta * (M + 1)) := by
              apply Finset.sum_le_sum
              intro u hu
              by_cases hadm : CentralRenyiAdmissible (M - (u : ℕ)) s theta eta
              · rw [if_pos hadm]
                have hpoint := fixedSourceWeight_mul_fixedRenyiMoment_le
                  htheta0 htheta1 heta0 heta1 hadm.1 hadm.2.1
                  hadm.2.2.1 hadm.2.2.2.1 hadm.2.2.2.2.1 hadm.2.2.2.2.2
                have hpowNM : (2 : ℝ) ^ (M - (u : ℕ)) ≤ (2 : ℝ) ^ M := by
                  exact_mod_cast pow_le_pow_right'
                    (by norm_num : (1 : ℕ) ≤ 2) (Nat.sub_le M (u : ℕ))
                have hrewrite :
                    ((fixedSet (M - (u : ℕ)) s).card : ℝ) *
                        fixedRenyiMoment (M - (u : ℕ)) s theta =
                      (2 : ℝ) ^ (M - (u : ℕ)) *
                        (fixedSourceWeight (M - (u : ℕ)) s *
                          fixedRenyiMoment (M - (u : ℕ)) s theta) := by
                  unfold fixedSourceWeight
                  have hp : 0 < (2 : ℝ) ^ (M - (u : ℕ)) := by positivity
                  field_simp [hp.ne']
                rw [hrewrite]
                have hNleM :
                    ((M - (u : ℕ) : ℕ) : ℝ) + 1 ≤ (M : ℝ) + 1 := by
                  exact_mod_cast
                    Nat.add_le_add_right (Nat.sub_le M (u : ℕ)) 1
                have hpointM :
                    fixedSourceWeight (M - (u : ℕ)) s *
                        fixedRenyiMoment (M - (u : ℕ)) s theta ≤
                      centralMomentConstant theta eta * ((M : ℝ) + 1) := by
                  calc
                    fixedSourceWeight (M - (u : ℕ)) s *
                          fixedRenyiMoment (M - (u : ℕ)) s theta ≤
                        centralMomentConstant theta eta *
                          (((M - (u : ℕ) : ℕ) : ℝ) + 1) := hpoint
                    _ ≤ centralMomentConstant theta eta * ((M : ℝ) + 1) :=
                      mul_le_mul_of_nonneg_left hNleM hconst0
                have hweightMoment0 :
                    0 ≤ fixedSourceWeight (M - (u : ℕ)) s *
                      fixedRenyiMoment (M - (u : ℕ)) s theta :=
                  mul_nonneg (fixedSourceWeight_nonneg _ _)
                    (fixedRenyiMoment_nonneg _ _ _)
                calc
                  (2 : ℝ) ^ (M - (u : ℕ)) *
                        (fixedSourceWeight (M - (u : ℕ)) s *
                          fixedRenyiMoment (M - (u : ℕ)) s theta) ≤
                      (2 : ℝ) ^ M *
                        (fixedSourceWeight (M - (u : ℕ)) s *
                          fixedRenyiMoment (M - (u : ℕ)) s theta) :=
                    mul_le_mul_of_nonneg_right hpowNM hweightMoment0
                  _ ≤ (2 : ℝ) ^ M *
                        (centralMomentConstant theta eta * (M + 1 : ℝ)) :=
                    mul_le_mul_of_nonneg_left hpointM (by positivity)
                  _ = (2 : ℝ) ^ M * centralMomentConstant theta eta *
                        (M + 1 : ℝ) := by ring
              · rw [if_neg hadm]
                positivity
            _ = (M : ℝ) *
                ((2 : ℝ) ^ M * centralMomentConstant theta eta * (M + 1)) := by
              simp
    _ = (M + 1 : ℝ) *
        ((3 : ℝ) ^ theta * (M : ℝ) ^ theta * (M : ℝ) *
          ((2 : ℝ) ^ M * centralMomentConstant theta eta * (M + 1))) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      ring
    _ ≤ ((3 : ℝ) ^ theta * centralMomentConstant theta eta *
          (M + 1 : ℝ) ^ 6) * (2 : ℝ) ^ M := by
      have hM0 : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
      have hMle : (M : ℝ) ≤ (M + 1 : ℝ) := by push_cast; linarith
      have hbase1 : (1 : ℝ) ≤ (M + 1 : ℝ) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le M)
      have hpoly :
          (M : ℝ) ^ theta * (M : ℝ) * (M + 1 : ℝ) ^ 2 ≤
            (M + 1 : ℝ) ^ 6 := by
        calc
          (M : ℝ) ^ theta * (M : ℝ) * (M + 1 : ℝ) ^ 2 ≤
              (M + 1 : ℝ) * (M + 1 : ℝ) * (M + 1 : ℝ) ^ 2 := by
            gcongr
          _ = (M + 1 : ℝ) ^ 4 := by ring
          _ ≤ (M + 1 : ℝ) ^ 6 := by
            have hsq : (1 : ℝ) ≤ (M + 1 : ℝ) ^ 2 := by
              nlinarith [sq_nonneg (M : ℝ)]
            calc
              (M + 1 : ℝ) ^ 4 = (M + 1 : ℝ) ^ 4 * 1 := by ring
              _ ≤ (M + 1 : ℝ) ^ 4 * (M + 1 : ℝ) ^ 2 :=
                mul_le_mul_of_nonneg_left hsq (by positivity)
              _ = (M + 1 : ℝ) ^ 6 := by ring
      rw [show
        (M + 1 : ℝ) *
              ((3 : ℝ) ^ theta * (M : ℝ) ^ theta * (M : ℝ) *
                ((2 : ℝ) ^ M * centralMomentConstant theta eta *
                  (M + 1 : ℝ))) =
            ((3 : ℝ) ^ theta * centralMomentConstant theta eta *
              (2 : ℝ) ^ M) *
              ((M : ℝ) ^ theta * (M : ℝ) * (M + 1 : ℝ) ^ 2) by ring]
      rw [show
        ((3 : ℝ) ^ theta * centralMomentConstant theta eta *
              (M + 1 : ℝ) ^ 6) * (2 : ℝ) ^ M =
            ((3 : ℝ) ^ theta * centralMomentConstant theta eta *
              (2 : ℝ) ^ M) * (M + 1 : ℝ) ^ 6 by ring]
      have hfactor0 :
          0 ≤ (3 : ℝ) ^ theta * centralMomentConstant theta eta *
            (2 : ℝ) ^ M :=
        mul_nonneg
          (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hconst0)
          (by positivity)
      exact mul_le_mul_of_nonneg_left hpoly hfactor0
end CollatzEndpointTransport.FixedTotal
