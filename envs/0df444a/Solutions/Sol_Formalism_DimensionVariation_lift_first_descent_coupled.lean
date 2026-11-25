-- Prove2me | solution 1 for Formalism.DimensionVariation.lift_first_descent_coupled
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:27:18.015968+00:00
-- url     : https://prove2.me/submissions/6833c377-0207-47f3-80c1-e4f9ecac1214

import Mathlib
import Definitions.Def_Formalism_ThetaSupremumBounds_StatementCB
import Definitions.Def_Formalism_ThetaSupremumBounds_DivIneqRecordTwoConst6
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DescendedNorm
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_PerEmbeddingCoupledBound
import Theorems.Thm_Formalism_DimensionVariation_lift_sharp_bound
import Theorems.Thm_Formalism_DimensionVariation_first_descent_coupled_bound
import Theorems.Thm_Formalism_DimensionVariation_sharp_three_halves_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField
open scoped Real
open Formalism Formalism.DimensionVariation
open Formalism.LatticeIndexTer (ph)
open Formalism.DivisionValues (fnorm chainFun chainMat)
open CB
namespace Formalism.DimensionVariation
theorem _root_.solution : LiftStepDiCB := by
  intro J Pl Emb _ _ _ _ ι AA AA' Cl Cl' _ _ _ _ _ _ _ _ _ A B _ _ _ _ _ r ν n s Th c Rc lam Om S kc th0sq
    γ γ' ε hK hcl hcl' logOm v f m N L La logT logg C2 C3 C4 c5 c6 C7 C8 C0 hν0 hν hs0 hs hTh hHas hThb
    hsupp hRc hOm hlam hγ hγ' hε hS hLpos hkc hth0 hv hKd hOmd hkcb hthb hCl hCl' hhcl hhcl' hAA hAA'
    hT0 hPl hι hm hN hL hLLa hLa hc5 hc6 hT hg p2 p3 p4 p5 p6 p7 p8 hC0 j
  have hLS := fun j σ => lift_sharp_bound Pl (ι j) (AA j) (AA' j) (Cl j) (Cl' j) (A j σ) (B j σ) r
    (ν j) (n j) (s j σ) (Th j σ) (c j σ) (Rc j σ) (fun τ => lam τ σ) (fun τ => Om τ σ) (S j σ) (γ j)
    (γ' j) (ε j σ) (hcl j) (hcl' j) (hν0 j) (hν j) (hs0 j σ) (hs j σ) (hTh j σ) (hHas j σ) (hThb j σ)
    (hsupp j σ) (hRc j σ) (fun τ => hOm τ σ) (fun τ => hlam τ σ) (hγ j) (hγ' j) (hε j σ) (hCl j)
    (hCl' j)
  have hnn : ∀ j, (0 : ℝ) < (Fintype.card (AA j) : ℝ) := fun j => Nat.cast_pos.mpr Fintype.card_pos
  have hnn' : ∀ j, (0 : ℝ) < (Fintype.card (AA' j) : ℝ) := fun j => Nat.cast_pos.mpr Fintype.card_pos
  have hclp : ∀ j, 0 < hcl j := fun j =>
    lt_of_lt_of_le (Nat.cast_pos.mpr Fintype.card_pos) (hCl j (Classical.arbitrary (AA j)))
  have hclp' : ∀ j, 0 < hcl' j := fun j =>
    lt_of_lt_of_le (Nat.cast_pos.mpr Fintype.card_pos) (hCl' j (Classical.arbitrary (AA' j)))
  have h32 := sharp_three_halves_bound J Pl Emb r ν n (fun j => Fintype.card (ι j))
    (fun j σ => liftNormSq (γ j) (γ' j) (ε j σ) (fun L L' => liftBlock (c j σ L L') (Rc j σ) (fun τ => lam τ σ))) kc Om th0sq
    (fun j => (Fintype.card (AA j) : ℝ)) (fun j => (Fintype.card (AA' j) : ℝ)) hcl hcl' v hν hLpos hkc hOm
    hth0 hnn hnn' hclp hclp' hv (fun j σ => by
      have := hLS j σ
      rw [hS j σ] at this
      exact this)
  have hg0' : ∀ j, 0 ≤ (Fintype.card (ι j) : ℝ) ∧ (Fintype.card (ι j) : ℝ) ≤ N ^ 2 :=
    fun j => ⟨Nat.cast_nonneg _, hι j⟩
  have hc5' : ∀ j, Real.log (8 + 32 * ((Fintype.card Pl : ℝ) * (Fintype.card (ι j) : ℝ)) * v) ≤ c5 * La :=
    fun j => by
      have := hc5 j
      push_cast at this
      exact this
  have hc6' : ∀ j τ, Real.log (2 * (∑ i, ν j τ i) + 2) ≤ c6 * La := fun j τ => by
    rw [hν j τ]
    exact hc6 j τ
  have hC0' : C3 + c5 + 2 * c6 + 1 + 2 * C2 * (C7 + C8) + 2 * C4 * (1 + C7 + C8) + 2 * C8 ≤ C0 := by
    nlinarith
  have hstep := first_descent_coupled_bound J Pl Emb r ν (fun j => (Fintype.card (ι j) : ℝ))
    (fun j σ => Real.log (liftNormSq (γ j) (γ' j) (ε j σ) (fun L L' => liftBlock (c j σ L L') (Rc j σ) (fun τ => lam τ σ)))) (fun j σ => Real.log (kc j σ)) (fun τ σ => Real.log (Om τ σ))
    (fun σ => Real.log (th0sq σ)) (fun j => Real.log (hcl j)) (fun j => Real.log (hcl' j))
    (fun j => Real.log (Fintype.card (AA j) : ℝ)) (fun j => Real.log (Fintype.card (AA' j) : ℝ)) hK logOm v
    f m N L La logT logg C2 C3 C4 c5 c6 C7 C8 C0 h32 hAA hAA' hKd hOmd hkcb hthb hhcl hhcl' hPl hg0' hm hN
    hL hLLa hLa hc5' hc6' hT hg p2 p3 p4 p5 p6 p7 p8 hC0'
  exact hstep.2.2.2.1 j
end Formalism.DimensionVariation
