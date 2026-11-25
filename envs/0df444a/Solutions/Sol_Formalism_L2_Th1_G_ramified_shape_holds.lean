-- Prove2me | solution 1 for Formalism.L2.Th1.G.ramified_shape_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:15:26.008167+00:00
-- url     : https://prove2.me/submissions/f97ca31f-07e0-4304-8cad-3fba178fdb86

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementR
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_FirstLevelFromUniversalLaw
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_Hurwitz
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_HurwitzB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_InverseEndoIntegralHolds
import Theorems.Thm_Formalism_L2_Th1_G_half_valuation_holds
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs
import Theorems.Thm_Formalism_L2_Th1_B_Ph_hs
import Theorems.Thm_Formalism_L2_Th1_C_Clo_CoeffCont_subst
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_cc_subst1
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_hs1
import Theorems.Thm_Formalism_L2_Th1_C_derivation_cube_integral_jet
import Theorems.Thm_Formalism_L2_Th1_C_jetOne
import Theorems.Thm_Formalism_L2_Th1_C_jetsShape
import Theorems.Thm_Formalism_L2_Th1_C_logDerivInt
import Theorems.Thm_Formalism_L2_Th1_C_mvExpLaws
import Theorems.Thm_Formalism_L2_Th1_C_mvExpSubst
import Theorems.Thm_Formalism_L2_Th1_G_jets_of_dist_jets_holds


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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.G
open Formalism.L2.Th1.C
open Formalism.G (unitBall)
namespace Formalism.L2.Th1.G
theorem _root_.solution : RamifiedShape := by
  intro K _ _ _ l linv ph a b d hFr hF1 hNeg h2 hAdj hab hd
  have hlp : IsLogPair l linv := hFr.1
  have h2i : (2 : K)⁻¹ ∈ unitBall K := by
    show ‖(2 : K)⁻¹‖ ≤ 1
    rw [norm_inv, h2, inv_one]
  have hdK : (d : K) ≠ 0 := Nat.cast_ne_zero.mpr hd
  obtain ⟨⟨H, hH, hexp⟩, hS⟩ := jetsShape K (unitBall K) l linv ph hFr hF1 hNeg h2i
  have hl' : IsOneUnit (unitBall K) (PowerSeries.derivative K l) :=
    logDerivInt K (unitBall K) l linv hlp hFr.2.1
  refine ⟨half_valuation_holds K _ (a - b) d hab hdK (hS a b hAdj), ?_, ?_⟩
  · intro i hi hi2
    rcases Nat.lt_or_ge i 3 with h3 | h3
    · have : i = 1 := by omega
      subst this
      exact jetOne K (unitBall K) l linv ph hlp hl' hFr.2.2 hNeg h2i
    · exact (derivation_cube_integral_jet K (unitBall K) l linv ph hFr hF1).2 i h3
  · have hs : PowerSeries.HasSubst linv := JetSubstitutionLemmas.hs1 hlp.2.2.1
    set c : K := jet l ph 2 / 2 with hc
    have hq0 : PowerSeries.constantCoeff (-(PowerSeries.C c * l ^ 2)) = 0 := by
      rw [map_neg, map_mul, map_pow, hlp.1]
      simp
    have hq0' : PowerSeries.constantCoeff (-(PowerSeries.C c * PowerSeries.X ^ 2) : PowerSeries K) = 0 := by
      simp
    have hph0 : PowerSeries.constantCoeff (-ph) = 0 := by rw [map_neg, hFr.2.2, neg_zero]
    have hsub : PowerSeries.subst linv (-(PowerSeries.C c * l ^ 2)) =
        (-(PowerSeries.C c * PowerSeries.X ^ 2) : PowerSeries K) := by
      rw [← PowerSeries.coe_substAlgHom hs, map_neg, map_mul, map_pow, PowerSeries.coe_substAlgHom hs,
        PowerSeries.subst_C, hlp.2.2.2.2]
      rfl
    have hid : PowerSeries.subst linv (mvExp (-ph) : PowerSeries K) =
        (mvExp (-(PowerSeries.C c * PowerSeries.X ^ 2)) : PowerSeries K) * PowerSeries.subst linv H := by
      rw [hexp, PowerSeries.subst_mul hs, mvExpSubst K Unit _ linv hq0 hlp.2.2.1, hsub]
    refine ⟨PowerSeries.subst linv H, (jets_of_dist_jets_holds K (unitBall K) l linv H hlp).1 hH, ?_, hid⟩
    have hcc := congrArg PowerSeries.constantCoeff hid
    rw [map_mul, JetSubstitutionLemmas.cc_subst1 hlp.2.2.1] at hcc
    have e1 : PowerSeries.constantCoeff (mvExp (-ph) : PowerSeries K) = 1 :=
      (mvExpLaws K Unit).2.1 _ hph0
    have e2 : PowerSeries.constantCoeff
        (mvExp (-(PowerSeries.C c * PowerSeries.X ^ 2)) : PowerSeries K) = 1 :=
      (mvExpLaws K Unit).2.1 _ hq0'
    rw [e1, e2, one_mul] at hcc
    exact hcc.symm
end Formalism.L2.Th1.G
