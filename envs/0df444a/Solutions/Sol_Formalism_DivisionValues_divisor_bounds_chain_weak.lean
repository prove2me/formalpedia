-- Prove2me | solution 1 for Formalism.DivisionValues.divisor_bounds_chain_weak
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:42:14.578106+00:00
-- url     : https://prove2.me/submissions/0b63c7da-fe9a-40ea-ac31-6917b67abb68

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_RatHermLcvTwist
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DivIntoDual
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_BoundsChain
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_JwConj
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DualMu
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Theorems.Thm_Formalism_DivisionValues_second_step_refined_weak
import Theorems.Thm_Formalism_DivisionValues_divisor_bounds_sum
import Theorems.Thm_P2M_Formalism_DivisionValues_lw_nonneg__acf346c58d0a


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open RationalHermitianForm
namespace Formalism.DivisionValues
theorem _root_.solution : BoundsChainW := by
  intro K _ _ _ _ K0 hK0 v0 hv0 D XE hXE Tup μ0 μ hμc hμfin XQ hXQ abelian₂ hLam ι hι J _ d XW hXW
    M hM HT XT hHT0 hHTw T hT θ hθ κ hκ ρ ρr hρr hρ0 hρpos hρv hdet0 hdet G e hLB hG n H hH hHpos P hP
    hQ Mt hMt hLamP hGR R hR hRloc S hS LG E3 L E1 E2 ell g F err Jx η hD hGb hLG hL hI hJ hE1 hE2 hE3
  obtain ⟨-, hB⟩ := second_step_refined_weak K K0 hK0 v0 hv0 D XE hXE Tup μ0 μ hμc hμfin XQ hXQ abelian₂ hLam ι hι
    J d XW hXW M hM HT XT hHT0 hHTw T hT θ hθ κ hκ ρ ρr hρr hρ0 hρpos hρv hdet0 hdet G e hLB hG n H hH
    hHpos P hP hQ Mt hMt hLamP hGR R hR hRloc
  have hsupp : (Function.support fun w => lw w * ((vw w (G (μ w) w) : ℝ) + ∑ j,
        ((idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
         (idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
         (jw (HT j (μ w)) w (T j (μ w)) : ℝ)))) ⊆ (S : Set (HeightOneSpectrum (𝓞 K))) := by
    intro w hw
    by_contra hwS
    exact hw (hS w hwS)
  rw [finsum_eq_sum_of_support_subset _ hsupp] at hB
  exact divisor_bounds_sum (HeightOneSpectrum (𝓞 K)) J S D hD (lcv XE R) (meanLog κ) LG E3
    (fun j => lcv (XW j) (M j)) L E1 E2 lw ell (fun w => (vw w (G (μ w) w) : ℝ)) g
    (fun w j => (idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ))
    (fun w j => (idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ))
    (fun w j => (jw (HT j (μ w)) w (T j (μ w)) : ℝ)) F err Jx η
    lw_nonneg' hB hGb hLG hL hI hJ hE1 hE2 hE3
end Formalism.DivisionValues
