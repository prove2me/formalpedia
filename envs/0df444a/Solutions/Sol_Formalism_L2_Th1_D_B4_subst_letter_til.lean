-- Prove2me | solution 1 for Formalism.L2.Th1.D.B4.subst_letter_til
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:28:38.379697+00:00
-- url     : https://prove2.me/submissions/fa979625-5a96-4d6a-b011-0e13205465f9

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Transfer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_BiextensionHypothesesOfConditions
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_Transfer_cc_letterLog


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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral mvExp torus BHyp NoLowBidegree letterLog de1 de2 s0 s1 s2 s1' s2' V2 degE)
open Formalism.InvariantFactorPaths.G7 (Simeq DivAB UnrOK IsLawOfLog)
open MvPowerSeries (subst HasSubst constantCoeff)
open Formalism.L2.Th1.D.B4
namespace Formalism.L2.Th1.D.B4
theorem _root_.solution (hS : SubstTil) {K : Type} [NormedField K] (l d : ℕ) [NeZero d]
    (σ : K →+* K) (hl : 2 ≤ l) (be0 : MvPowerSeries (Fin 2) K) (ι : Type) [Fintype ι]
    (om oms : ι → K) (S : ZMod d → MvPowerSeries (V2 d) K) (hS0 : ∀ s, constantCoeff (S s) = 0) :
    subst (letterLog (K := K) l) (subst S (beTil l σ be0 om oms)) =
      ∑ r, subst ![linEL σ (oms r) (fun s => subst (letterLog (K := K) l) (S s)),
        linOL σ (om r) (fun s => subst (letterLog (K := K) l) (S s))] (addC l be0) := by
  have hc : ∀ x : V2 d, constantCoeff (letterLog (K := K) l x) = 0 :=
    Formalism.DworkPowerSeriesWeights.Transfer.cc_letterLog l
  have hLL : HasSubst (letterLog (K := K) (d := d) l) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero hc
  rw [MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero hS0) hLL]
  exact hS K l d σ hl be0 ι om oms (V2 d) _
    (fun s => MvPowerSeries.constantCoeff_subst_eq_zero hLL hc (hS0 s))
end Formalism.L2.Th1.D.B4
