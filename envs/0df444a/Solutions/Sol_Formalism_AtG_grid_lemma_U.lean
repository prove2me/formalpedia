-- Prove2me | solution 1 for Formalism.AtG.grid_lemma_U
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:20:10.903623+00:00
-- url     : https://prove2.me/submissions/597b0c46-c7e3-43a7-8278-4a0f72ac4d11

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
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_inv
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_mul
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_one
import Theorems.Thm_Formalism_ValuationGridEstimates_lemma_u_units


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
theorem _root_.solution : HeightBoundedDenominators := by
  intro K _ _ _ w Sq S0 ζ Ga Ga' Gb Gb' cc qq hζ hζ0 hq hGa hGb
  have vmul := Formalism.DivisionValues.ValuationRepresentative.vw_mul w
  have vinv := Formalism.DivisionValues.ValuationRepresentative.vw_inv w
  have hq0 : ∀ s ∈ S0, ((qq s : K) ^ cc s) ≠ 0 := fun s hs =>
    pow_ne_zero _ (by exact_mod_cast (hq s hs).ne')
  have nGa : ∀ s ∈ S0, Ga s ≠ 0 ∧ Ga' s ≠ 0 := by
    intro s hs
    have := hq0 s hs
    rw [← (hGa s hs).2.2] at this
    exact ⟨left_ne_zero_of_mul this, right_ne_zero_of_mul this⟩
  have nGb : ∀ s ∈ S0, Gb s ≠ 0 ∧ Gb' s ≠ 0 := by
    intro s hs
    have := hq0 s hs
    rw [← (hGb s hs).2.2] at this
    exact ⟨left_ne_zero_of_mul this, right_ne_zero_of_mul this⟩
  let M : K → Multiplicative ℝ := fun z => Multiplicative.ofAdd ((vw w z : ℤ) : ℝ)
  have Mmul : ∀ a b : K, a ≠ 0 → b ≠ 0 → M (a * b) = M a * M b := by
    intro a b ha hb
    simp only [M, vmul a b ha hb, Int.cast_add, ofAdd_add]
  have Mpow : ∀ (a : K) (n : ℕ), a ≠ 0 → M (a ^ n) = M a ^ n := by
    intro a n ha
    induction n with
    | zero => simp [M, Formalism.DivisionValues.ValuationRepresentative.vw_one]
    | succ n ih => rw [pow_succ, pow_succ, Mmul _ _ (pow_ne_zero _ ha) ha, ih]
  have key := (Formalism.ValuationGridEstimates.lemma_u_units (Multiplicative ℝ) (fun z => Multiplicative.toAdd z) (fun _ _ => rfl)
    Sq S0 (M ζ) (fun s => M (Ga s)) (fun s => M (Ga' s)) (fun s => M (Gb s)) (fun s => M (Gb' s))
    (fun s => M (qq s : K)) cc (by simp [M, hζ0])
    (fun s hs => ⟨Int.cast_nonneg (R := ℝ) (hGa s hs).1, Int.cast_nonneg (R := ℝ) (hGa s hs).2.1, by
      rw [← Mmul _ _ (nGa s hs).1 (nGa s hs).2, (hGa s hs).2.2,
        Mpow _ _ (by exact_mod_cast (hq s hs).ne')]⟩)
    (fun s hs => ⟨Int.cast_nonneg (R := ℝ) (hGb s hs).1, Int.cast_nonneg (R := ℝ) (hGb s hs).2.1, by
      rw [← Mmul _ _ (nGb s hs).1 (nGb s hs).2, (hGb s hs).2.2,
        Mpow _ _ (by exact_mod_cast (hq s hs).ne')]⟩)).2
  have e1 : M (ζ * ∏ s ∈ S0, Ga s / Gb s) = M ζ * ∏ s ∈ S0, M (Ga s) / M (Gb s) := by
    have hp : ∀ T : Finset Sq, T ⊆ S0 →
        (∏ s ∈ T, Ga s / Gb s ≠ 0 ∧ M (∏ s ∈ T, Ga s / Gb s) = ∏ s ∈ T, M (Ga s) / M (Gb s)) := by
      intro T
      classical
      induction T using Finset.induction_on with
      | empty => intro _; simp [M, Formalism.DivisionValues.ValuationRepresentative.vw_one]
      | insert i s hi ih =>
        intro hT
        have hi0 : i ∈ S0 := hT (Finset.mem_insert_self _ _)
        obtain ⟨i1, i2⟩ := ih (fun t ht => hT (Finset.mem_insert_of_mem ht))
        have hd : Ga i / Gb i ≠ 0 := div_ne_zero (nGa i hi0).1 (nGb i hi0).1
        refine ⟨by rw [Finset.prod_insert hi]; exact mul_ne_zero hd i1, ?_⟩
        rw [Finset.prod_insert hi, Finset.prod_insert hi, Mmul _ _ hd i1, i2, div_eq_mul_inv,
          Mmul _ _ (nGa i hi0).1 (inv_ne_zero (nGb i hi0).1)]
        congr 1
        simp only [M, vinv, Int.cast_neg, ofAdd_neg, div_eq_mul_inv]
    rw [Mmul _ _ hζ (hp S0 (Finset.Subset.refl _)).1, (hp S0 (Finset.Subset.refl _)).2]
  rw [← e1] at key
  have e2 : ∑ s ∈ S0, 2 * (cc s : ℝ) * (vw w (qq s : K) : ℝ) =
      2 * ∑ s ∈ S0, (cc s : ℝ) * (vw w (qq s : K) : ℝ) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => by ring
  rw [← e2]
  exact key
end Formalism.AtG
