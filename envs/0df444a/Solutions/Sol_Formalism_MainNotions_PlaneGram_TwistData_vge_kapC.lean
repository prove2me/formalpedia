-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.vge_kapC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:33:20.374056+00:00
-- url     : https://prove2.me/submissions/b6b16075-29bc-4c88-be23-3d1859d45382

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_TestBoundOfRhoAndNormSets
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_GlobalTheory
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_fact_eq_kapC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
open Formalism.MainNotions.PlaneGram.TwistData
variable {K : Type} [Field K] (D : TwistData K)
variable [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ}
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution (hD : DVRHyp v p) {cst : D.Tau → (Fin D.r → ℕ) → ℕ → K}
    {gam : D.Tau → (Fin D.r → ℕ) → (Fin D.r → ℕ) → K} (hdig : D.DigOK v p cst gam) {ζ : D.EM}
    (hζ : D.LabLowE p ζ) :
    vge v (vN v (fact (D.collapseExponent p ζ)) + vN v (fact (D.tpE ζ)) - vN v (fact ζ)) (D.kapC cst ζ) := by
  have hd := hdig
  unfold DigOK at hd
  obtain ⟨h1, _⟩ := hd
  have heq := D.fact_eq_kapC hdig hζ
  have hG : v (∏ t, gam t (D.labF ζ t) (D.wF ζ t)) = 0 :=
    Finset.prod_induction _ (fun x => v x = 0)
      (fun a b ha hb => by rw [AddValuation.map_mul, ha, hb, add_zero]) (AddValuation.map_one v)
      (fun t _ => ((h1 t (D.labF ζ t) (fun a => hζ t a)).2 (D.wF ζ t)).1)
  have hfact : ∀ {σ : Type} (α : σ →₀ ℕ), ((fact α : ℕ) : K) ≠ 0 := fun α =>
    Nat.cast_ne_zero.2 (by
      unfold fact Finsupp.prod
      exact Finset.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _)
  have hA := hfact (D.collapseExponent p ζ)
  have hB := hfact (D.tpE ζ)
  have hZ := hfact ζ
  have hX : D.kapC cst ζ ≠ 0 := by
    intro h0
    rw [h0, zero_mul, zero_mul] at heq
    exact mul_ne_zero hA hB heq
  obtain ⟨qA, hqA⟩ := WithTop.ne_top_iff_exists.1 ((AddValuation.top_iff v).not.2 hA)
  obtain ⟨qB, hqB⟩ := WithTop.ne_top_iff_exists.1 ((AddValuation.top_iff v).not.2 hB)
  obtain ⟨qZ, hqZ⟩ := WithTop.ne_top_iff_exists.1 ((AddValuation.top_iff v).not.2 hZ)
  obtain ⟨qX, hqX⟩ := WithTop.ne_top_iff_exists.1 ((AddValuation.top_iff v).not.2 hX)
  have hv := congrArg v heq
  rw [AddValuation.map_mul, AddValuation.map_mul, AddValuation.map_mul, hG, ← hqA, ← hqB, ← hqZ,
    ← hqX] at hv
  have hq : qA + qB = qX + qZ := by
    have h2 : ((qA + qB : ℚ) : WithTop ℚ) = ((qX + qZ : ℚ) : WithTop ℚ) := by
      rw [WithTop.coe_add, WithTop.coe_add, hv, add_zero]
    exact WithTop.coe_eq_coe.1 h2
  unfold vge vR vN
  rw [← hqA, ← hqB, ← hqZ, ← hqX]
  simp only [WithTop.untopD_coe, WithTop.map_coe]
  have hle : (qA : ℝ) + qB - qZ ≤ qX := by
    have h3 : (qA : ℝ) + qB = qX + qZ := by exact_mod_cast hq
    linarith
  exact WithTop.coe_le_coe.2 hle
end Formalism.MainNotions.PlaneGram.TwistData
