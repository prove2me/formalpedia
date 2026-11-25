-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.OddLevelGainBounds.one_letter_unramified_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:45:10.319017+00:00
-- url     : https://prove2.me/submissions/c494069b-bd0b-429b-b210-1b6fdab3b2cb

import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_StatementG
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OneGauss
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_WeightsAddOverOrbitFamily
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OrbMul
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_OneLetterGaussProofs_OneLetterUnramifiedBound
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_lemma_R_core_log_loss
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_logarithm_weight_comparison
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_oneLetterRadius
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_one_letter_exponent_weight
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_unipotent_weight_bound
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qi22_homW_prod__0e07eaea3260
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk29_wtGe_prod__77285e911b46


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
universe u v
open Formalism Formalism.DworkPowerSeriesWeights Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
theorem _root_.solution (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K]
    (l N0 N1 : ℕ) (hl : l.Prime) (hodd : Odd l) (hpi : ‖(l : K)‖ < 1)
    (K0 : Subfield K) (hK0 : Unram l K0) (ζ : K) (hζ : IsPrimitiveRoot ζ (l ^ 2 - 1))
    (be : MvPowerSeries (ZMod 2) K) (hbe : BHyp l 2 K0 ζ be) (ep : K) (hep : ‖ep‖ = 1)
    (ι : Type v) [Fintype ι] (M : Fin N0 × Fin N1 → ι → K) (hM1 : ∀ x i, ‖M x i‖ ≤ 1)
    (g : Fin N0 × Fin N1 → MvPowerSeries (Fin N0 × Fin N1) K)
    (hg0 : ∀ x, MvPowerSeries.constantCoeff (g x) = 0)
    (hg : ∀ x, MvPowerSeries.subst g (oneLog (K := K) l x) = MvPowerSeries.X x)
    (U : MvPowerSeries (Fin N0 × Fin N1) K) (hU : Integral U)
    (sgn : K) (hsgn : sgn = 1 ∨ sgn = -1) (κ : ι →₀ ℕ) (a : ℕ) (ha : 1 ≤ a)
    (hκa : ∀ i, κ i ≤ a) :
    ‖((mfact κ : ℕ) : K) * MvPowerSeries.coeff κ
        (MvPowerSeries.subst (fun x => ∑ i, MvPowerSeries.C (M x i) * MvPowerSeries.X i)
            (MvPowerSeries.subst g U) *
          mvExp ((sgn / 2) • ∑ x : Fin N0 × Fin N1, MvPowerSeries.subst
            (fun s : ZMod 2 => (if s = 0 then (1 : K) else ep) •
              ∑ i, MvPowerSeries.C (M x i) * MvPowerSeries.X i) be))‖ ≤
      ‖(l : K)‖ ^ (rho l * (κ.degree : ℝ) -
        (Fintype.card ι : ℝ) * (Real.logb l (a : ℝ) + 1)) := by
  have hl3 : 3 ≤ l := by
    obtain ⟨k, hk⟩ := hodd
    have := hl.two_le
    omega
  obtain ⟨-, hOR2⟩ := oneLetterRadius l hl3
  obtain ⟨hBc, hBw⟩ := one_letter_exponent_weight.{u, v} K l N0 N1 hl hodd hpi K0 hK0 ζ hζ be hbe ep hep ι M
    hM1 sgn hsgn
  have hg' : ∀ x, MvPowerSeries.subst g (genLog (K := K) l (id : Fin N0 × Fin N1 → _) x) =
      MvPowerSeries.X x := by
    intro x
    rw [← (logarithm_weight_comparison K l 2 N0 N1).2.2 x]
    exact hg x
  have hsig : ∀ _ : ι, (0 : ℝ) ≤ 1 / ((l : ℝ) + 1) := fun _ => by positivity
  have hUw := unipotent_weight_bound.{u, v, 0} K l hl hpi (Fin N0 × Fin N1) id g hg0 hg' U hU ι M hM1
    (fun _ => 1 / ((l : ℝ) + 1)) hsig
  have h := lemma_R_core_log_loss.{u, v} K l hl hpi ι (fun _ => 1 / ((l : ℝ) + 1)) κ a ha hκa _ _ hBc
    (fun n _ => hBw n) (fun n _ => hUw n)
  refine le_of_le_of_eq h ?_
  congr 2
  rw [hOR2, ← Finset.sum_mul, mul_comm, Finsupp.degree_eq_sum]
  push_cast
  rfl
end Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
