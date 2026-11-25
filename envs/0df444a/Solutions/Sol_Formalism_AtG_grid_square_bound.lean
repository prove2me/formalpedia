-- Prove2me | solution 1 for Formalism.AtG.grid_square_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:38:07.751136+00:00
-- url     : https://prove2.me/submissions/bcbb464f-1b30-4a20-b79b-ed0024b0416b

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
import Theorems.Thm_P2M_Formalism_AtG_wt_nonneg__3d7a0657db25
import Theorems.Thm_Formalism_DivisionValues_valuation_basic_properties


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
theorem _root_.solution : SquareAtPlaceBound := by
  intro K _ _ _ w a a' d h p q e h1 h2 h3 h4 h5 x xd y E g S Se N0 δ σ hN0 hne hy hE
    c0 c00 A A0 A0' hc0 hc00 hA hA0 hA0' hcA hcA' hAA ub ua hu hub hua r hr
  obtain ⟨vmul, -, -, -, vone, vinv, -⟩ := Formalism.DivisionValues.valuation_basic_properties K w
  let M : K → Multiplicative ℝ := fun z => Multiplicative.ofAdd ((vw w z : ℤ) : ℝ)
  have Mmul : ∀ a b : K, a ≠ 0 → b ≠ 0 → M (a * b) = M a * M b := by
    intro a b ha hb
    simp only [M, vmul a b ha hb, Int.cast_add, ofAdd_add]
  have Minv : ∀ a : K, M a⁻¹ = (M a)⁻¹ := by
    intro a; simp only [M, vinv a, Int.cast_neg, ofAdd_neg]
  have Mdiv : ∀ a b : K, a ≠ 0 → b ≠ 0 → M (a / b) = M a / M b := by
    intro a b ha hb
    rw [div_eq_mul_inv, Mmul a _ ha (inv_ne_zero hb), Minv, div_eq_mul_inv]
  have Mprod : ∀ (ι : Type) (s : Finset ι) (f : ι → K), (∀ i ∈ s, f i ≠ 0) →
      M (∏ i ∈ s, f i) = ∏ i ∈ s, M (f i) := by
    intro ι s f
    classical
    induction s using Finset.induction_on with
    | empty => intro _; simp [M, vone]
    | insert i s hi ih =>
      intro hf
      rw [Finset.prod_insert hi, Finset.prod_insert hi,
        Mmul _ _ (hf i (by simp)) (Finset.prod_ne_zero_iff.2 fun j hj => hf j (by simp [hj])),
        ih (fun j hj => hf j (by simp [hj]))]
  have hρ : ∀ s, rhoAt x y E s ≠ 0 := by
    intro s; unfold rhoAt; split_ifs
    · exact div_ne_zero (hne s).2.2.1 (hne s).1
    · exact mul_ne_zero (hne s).2.2.2 (div_ne_zero (hne _).2.2.1 (hne _).1)
  have s1 : ∀ s : ℤ, 1 ≤ s → s ≤ h →
      M (rhoAt x y E s) = Multiplicative.ofAdd (((vw w (y s) + g s : ℤ)) : ℝ) /
        Multiplicative.ofAdd (((vw w (x s) + g s : ℤ)) : ℝ) ∧
      - wt S N0 w ≤ Multiplicative.toAdd (Multiplicative.ofAdd (((vw w (y s) + g s : ℤ)) : ℝ)) ∧
      Multiplicative.toAdd (Multiplicative.ofAdd (((vw w (y s) + g s : ℤ)) : ℝ)) ≤
        Multiplicative.toAdd (Multiplicative.ofAdd (((vw w (xd s) + g s : ℤ)) : ℝ)) +
          wt Se (fun l => 1 / (l : ℝ) ^ 2) w := by
    intro s hs1 hs2
    refine ⟨?_, (hy s hs1 hs2).1, (hy s hs1 hs2).2⟩
    have : rhoAt x y E s = y s / x s := by unfold rhoAt; rw [if_pos hs1]
    rw [this, Mdiv _ _ (hne s).2.2.1 (hne s).1]
    simp only [M, ← ofAdd_sub]
    congr 1
    push_cast
    ring
  have s2 : ∀ s : ℤ, 1 - ((e : ℤ) + q - p) ≤ s → s ≤ 0 →
      M (rhoAt x y E s) = M (E s) * M (rhoAt x y E (1 - s)) ∧
      Multiplicative.toAdd (M (E s)) = 0 := by
    intro s hs1 hs2
    constructor
    · have e1 : rhoAt x y E s = E s * (y (1 - s) / x (1 - s)) := by
        unfold rhoAt; rw [if_neg (by omega)]
      have e2 : rhoAt x y E (1 - s) = y (1 - s) / x (1 - s) := by
        unfold rhoAt; rw [if_pos (by omega)]
      rw [e1, e2, Mmul _ _ (hne s).2.2.2 (div_ne_zero (hne _).2.2.1 (hne _).1)]
    · simp [M, hE s hs1 hs2]
  have s3 : M A / M A0 =
      ∏ s ∈ Icc (1 - ((e : ℤ) + q - p)) ((h : ℤ) - (p + q)), M (rhoAt x y E s) := by
    rw [← Mdiv _ _ hA hA0, hAA, Mprod _ _ _ (fun s _ => hρ s)]
  have n1 : (∏ j ∈ range q, ub j) ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => (hu j).1
  have n2 : (∏ i ∈ range p, ua i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => (hu j).2
  have n3 : c0 / c00 ≠ 0 := div_ne_zero hc0 hc00
  have n4 : (∏ k ∈ Icc 1 p, rhoAt x y E ((e : ℤ) + q - k + 1)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun j _ => hρ _
  have n5 : (∏ k ∈ Icc 1 q, rhoAt x y E ((e : ℤ) + k)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun j _ => hρ _
  have s4 : M r = ((∏ j ∈ range q, M (ub j)) * ∏ i ∈ range p, M (ua i)) * (M c0 / M c00) *
        (∏ k ∈ Icc 1 p, M (rhoAt x y E ((e : ℤ) + q - k + 1))) *
        (∏ k ∈ Icc 1 q, M (rhoAt x y E ((e : ℤ) + k)))⁻¹ := by
    rw [hr, Mmul _ _ (mul_ne_zero (mul_ne_zero (mul_ne_zero n1 n2) n3) n4) (inv_ne_zero n5),
      Mmul _ _ (mul_ne_zero (mul_ne_zero n1 n2) n3) n4, Mmul _ _ (mul_ne_zero n1 n2) n3,
      Mmul _ _ n1 n2, Minv, Mdiv _ _ hc0 hc00, Mprod _ _ _ (fun j _ => (hu j).1),
      Mprod _ _ _ (fun j _ => (hu j).2), Mprod _ _ _ (fun j _ => hρ _),
      Mprod _ _ _ (fun j _ => hρ _)]
  exact Formalism.ValuationGridEstimates.valuation_ratio_bound (Multiplicative ℝ) (fun z => Multiplicative.toAdd z)
    (fun _ _ => rfl) a a' d h p q e h1 h2 h3 h4 h5
    (fun s => Multiplicative.ofAdd (((vw w (x s) + g s : ℤ)) : ℝ))
    (fun s => Multiplicative.ofAdd (((vw w (xd s) + g s : ℤ)) : ℝ))
    (fun s => Multiplicative.ofAdd (((vw w (y s) + g s : ℤ)) : ℝ))
    (fun s => M (rhoAt x y E s)) (fun s => M (E s))
    (wt S N0 w) (wt Se (fun l => 1 / (l : ℝ) ^ 2) w) δ σ
    (wt_nonneg' S N0 hN0 w) (wt_nonneg' Se _ (fun l _ => by positivity) w)
    s1 s2 (M c0) (M c00) (M A) (M A0) (M A0') hcA hcA' s3
    (fun j => M (ub j)) (fun i => M (ua i)) hub hua (M r) s4
end Formalism.AtG
