-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.jet_subst_linS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:11:24.49661+00:00
-- url     : https://prove2.me/submissions/44851be0-8e6f-4fb3-a69b-ff0b6115993c

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ThmPJet
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMJet
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_jet_smul_right
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_jet_sum_right
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_jet_C
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_jet_mul_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_jet_mul_C
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_add
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_add
import Theorems.Thm_Formalism_IncomingBounds_tpjet_jetAt0_add
import Theorems.Thm_Formalism_IncomingBounds_tpjet_jetAt0_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_add
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_subst_linS_congr
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_dVar_subst_linS
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_subst_linS_C


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
open Classical
open MvPowerSeries
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
open Formalism.BaseCaseIdentities (OrdGE)
variable {C : Type} [Field C] {σ τ : Type}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution [Fintype σ] [Fintype τ] (M : τ → σ → C) (Q : MvPolynomial τ C)
    (F : MvPowerSeries σ C) :
    jetAt0 Q (subst (linS M) F) = jetAt0 (linT M Q) F := by
  induction Q using MvPolynomial.induction_on generalizing F with
  | C a =>
    have h : linT M (MvPolynomial.C a) = MvPolynomial.C a := by
      unfold linT; rw [MvPolynomial.aeval_C]; rfl
    rw [h, jet_C, jet_C]
    congr 1
    have h0 := coeff_subst_linS_congr M (F := F) (G := MvPowerSeries.C (constantCoeff F)) (N := 0)
      (fun μ hμ => by
        have : μ = 0 := by
          rw [← Finsupp.degree_eq_zero_iff]; omega
        subst this
        simp) 0 (by simp)
    rw [subst_linS_C] at h0
    simpa using h0
  | add p q hp hq => rw [map_add, tpjet_jetAt0_add, tpjet_jetAt0_add, hp, hq]
  | mul_X p c hp =>
    rw [jet_mul_X, dVar_subst_linS, jet_sum_right, map_mul]
    have h : linT M (MvPolynomial.X c) = ∑ w, MvPolynomial.C (M c w) * MvPolynomial.X w := by
      unfold linT; rw [MvPolynomial.aeval_X]
    rw [h, Finset.mul_sum, tpjet_jetAt0_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [jet_smul_right, hp, ← mul_assoc, jet_mul_X, jet_mul_C]
end Formalism.L2.FormalSeriesBounds
