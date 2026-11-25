-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.thmAGauss_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:28:24.025974+00:00
-- url     : https://prove2.me/submissions/7a027bc7-3b4e-4f82-b9c1-34110f5546a1

import Definitions.Def_Formalism_GaussJetBounds_FrameJetEval
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Generic
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_GField
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffEvenDerivativeEqZero
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAGaussOf
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmS_cc_be
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_intCast_padicComplex
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_residuallyGenericExists
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_theorem_A_generic
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
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (hT : TransferB) (hF : FrameJetEval) (hL : LabelsExist) (hG : GaussPow) :
    ThmAGauss := by
  intro l _ d N0 N1 _ hl3 hd hde K0 hK0 ζ hζ be hbe g hg0 hg U hU ε hε TT colN p hp hp1 I
    nu1 nu2 size hnu1 hnu2 hsize a ha hsa hthr n
  have hlp : l.Prime := Fact.out
  obtain ⟨K, instK, hult, hchar, φ, Y, hφ, hgauss, hgen⟩ :=
    residuallyGenericExists l (ZMod d × Fin N0 × Fin N0)
  have := hult
  have := hchar
  have hnl : ‖(l : K)‖ = ‖(l : ℂ_[l])‖ := by rw [← map_natCast φ, hφ]
  have hl1 : ‖(l : ℂ_[l])‖ < 1 := by
    have h := norm_intCast_padicComplex l (l : ℤ)
    rw [Int.cast_natCast, Int.cast_natCast] at h
    rw [h]
    exact Padic.norm_p_lt_one
  have hN0 : 0 < N0 := by
    have h0 : 0 ≤ Real.logb l a :=
      Real.logb_nonneg (by exact_mod_cast hlp.one_lt) (by exact_mod_cast ha)
    have h1 : (0 : ℝ) < N0 := by linarith
    exact_mod_cast h1
  have hnu1a : ∀ s, nu1 s ≤ a := fun s => le_trans (by
    rw [hnu1, hsize]
    calc colN s = ∑ _c : Fin (colN s), 1 := by simp
      _ ≤ _ := Finset.sum_le_sum fun c _ => hp1 s c) (hsa s)
  obtain ⟨J, lab, m, hinj, hlab, hJ, hm⟩ := hL l d N0 hlp.two_le TT nu1 size a ha hnu1a hsa hthr
  obtain ⟨hT1, hT2, hT3, hT4⟩ := hT ℂ_[l] K φ hφ l d N0 N1 K0 ζ be
  obtain ⟨hg0', hg'⟩ := hT3 g hg0 hg
  have hA := theorem_A_generic.{0} K l d N0 N1 hlp hl3 hd hde (hnl ▸ hl1) hN0 (K0.map φ) (hT1 hK0)
    (φ ζ) (hζ.map_of_injective φ.injective) _ (hT2 hbe) _ hg0' hg' _ (hT4 U hU) (φ ε)
    (by rcases hε with rfl | rfl <;> simp) TT colN p hp hp1 I Y hgen nu1 nu2 size hnu1 hnu2 hsize
    a ha hsa J lab hinj hlab hJ m hm
  rw [← hF ℂ_[l] K φ d N0 N1 g U ε be hg0 (asmS_cc_be hbe.2.2.1) colN p hp I (genFrame TT l m Y),
    hnl] at hA
  refine le_trans ?_ hA
  have hk : genFrame TT l m Y =
      fun y => Y y ^ (if y.1 ∈ TT ∧ y.2.1.val = 0 then l ^ m else 1) := by
    funext y
    unfold genFrame
    split_ifs <;> simp
  rw [hk]
  refine hG ℂ_[l] K φ _ Y hgauss _ (fun y => ?_) _ n
  split_ifs
  · exact pow_ne_zero _ hlp.ne_zero
  · exact one_ne_zero
end Formalism.DworkPowerSeriesWeights
