-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.SmallOrderPrimeLosses.joint_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:25:07.456874+00:00
-- url     : https://prove2.me/submissions/10db1524-fc57-4393-aba8-3bf48e155d30

import Definitions.Def_Formalism_SizeWindowBrackets_PrimeClassLossHypothesesSatisfiable
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_OneLeThresholdMulPowers
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_DiscriminantSettingSatisfied
import Theorems.Thm_Formalism_LFunctionChainParameters_SmallOrderPrimeLosses_out_discriminant_bound
import Theorems.Thm_Formalism_LFunctionChainParameters_SmallOrderPrimeLosses_second_discriminant_bound
import Theorems.Thm_Formalism_LFunctionChainParameters_SmallOrderPrimeLosses_io_discriminant_bound
import Theorems.Thm_Formalism_LFunctionChainParameters_SmallOrderPrimeLosses_sizeIo_core
import Theorems.Thm_Formalism_LFunctionChainParameters_SmallOrderPrimeLosses_size_core
import Theorems.Thm_Formalism_LFunctionChainParameters_DeficitSplitLemmas_loss_bound
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_apos
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_sg1
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_facts
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_first_kind_bound
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_first_le
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_log_four_le_three_halves
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_side_condition_of_windows
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_unitU_nonneg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.SmallOrderPrimeLosses
open Finset Classical
open Formalism.LFunctionChainParameters.DeficitSplitLemmas Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
namespace Formalism.LFunctionChainParameters.SmallOrderPrimeLosses
theorem _root_.solution : ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ (P : Par) (e K : ℝ), P.Cord = Cord → Windows P e K →
    LargeX P.x P.ε e K →
    ∀ (ι κ τ U : Type) (Ps cand PR : Finset ℕ) (J : Finset κ) (TT : Finset τ)
      (BAD : ℕ → τ → Prop) (Sig : ℕ → ℝ) (io : U → ℕ → ℝ) (D : U → LD ι κ τ),
      PrimeClassLossHypotheses P Ps cand PR J TT BAD Sig io D →
      ExplicitLossAndPrimeLogSumBounds P K Ps cand J TT io D ∧ ExcessAndPrimeLogSumUnitBounds P Ps cand J TT io D := by
  obtain ⟨C₁, hC₁⟩ := first_kind_bound
  refine ⟨max C₁ 0, le_max_right _ _, ?_⟩
  intro P e K hCord hW hL ι κ τ U Ps cand PR J TT BAD Sig io D hS
  obtain ⟨hTT, hPs, hSig0, hWW, hT2, hio, hAll⟩ := hS
  obtain ⟨z, u, E, X, S, sb, v, w8, F⟩ := facts hW hL
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, -⟩ :=
    side_condition_of_windows P e K hW hL
  have hm : (0 : ℝ) ≤ (J.card : ℝ) := Nat.cast_nonneg _
  have hT : (1 : ℝ) ≤ (TT.card : ℝ) := by exact_mod_cast Finset.card_pos.2 hTT
  have hT0 : (0 : ℝ) ≤ (TT.card : ℝ) := Nat.cast_nonneg _
  have ha0 : 0 ≤ P.a := F.apos.le
  have hU := unitU_nonneg (P := P) hm hT
  have hA : ∀ υ, (D υ).ASK P.d Ps J TT - (D υ).Ga J ≤
      (2 * Real.log 4 * P.C + 13 * sg P K) * unitU P J.card TT.card := by
    intro υ
    obtain ⟨hLed, hFirst, hSecond, hBad⟩ := hAll υ
    obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11⟩ := hLed
    have led := loss_bound ι κ τ (D υ).W (D υ).below (D υ).l Ps (D υ).cl J TT (D υ).TTp
      (D υ).Iex (D υ).at_ (D υ).wz (D υ).Id (D υ).wd P.d (D υ).gainW (D υ).tauW
      (D υ).gain (D υ).tau (D υ).lo (D υ).fl P.a P.th P.wpp P.Xpp P.Xp P.C P.f P.N P.Sk P.Q₁ P.Q₂
      P.lx P.La P.k P.K₀ (D υ).L₁ P.p₀ l1 (fun p hp => (hPs p hp).1) s1 s2 s3 s4 s5 s6 s7 s8 s9 s10
      s11 s12 s13 s14 s15 s16 s17 s18 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11
    have out := out_discriminant_bound τ Ps PR (D υ).cl TT (D υ).TTp BAD J.card P.a _ hm ha0 hT2 hBad
    have first := first_le hC₁ (by rw [hCord]; exact le_max_left _ _) hW hL Ps (D υ).cl hPs hFirst
      J.card TT.card hm hT0
    have second := second_discriminant_bound Ps cand (D υ).cl Sig P.θ J.card TT.card P.a _ hm hT0 ha0 hSig0 hWW hSecond
    have size := size_core hW hL hm hT
    unfold tDetD tFloors tCp tPrLow tPrHigh tOr tHigh tD tOutD tSecondD at size
    unfold LD.ASK LD.Ga
    linarith
  have hI : ∀ υ, ∑ p ∈ cand, Real.log p * io υ p ≤ sg P K * unitU P J.card TT.card := by
    intro υ
    have h := io_discriminant_bound cand Sig (io υ) P.θ J.card TT.card P.a _ hm hT0 ha0 hWW (hio υ)
    have size := sizeIo_core hW hL hm hT
    unfold tIoD at size
    linarith
  refine ⟨⟨hA, hI⟩, fun υ => (hA υ).trans ?_, fun υ => (hI υ).trans ?_⟩
  · have h1 : 2 * Real.log 4 * P.C + 13 * sg P K ≤ 3 * P.C + 13 := by
      have := mul_le_mul_of_nonneg_right (show 2 * Real.log 4 ≤ 3 by linarith [log_four_le_three_halves]) F.C0
      linarith [F.sg1]
    exact mul_le_mul_of_nonneg_right h1 hU
  · have := mul_le_mul_of_nonneg_right F.sg1 hU
    linarith
end Formalism.LFunctionChainParameters.SmallOrderPrimeLosses
