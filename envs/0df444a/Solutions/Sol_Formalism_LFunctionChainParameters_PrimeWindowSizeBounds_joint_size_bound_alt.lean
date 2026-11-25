-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.joint_size_bound_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:37:49.942272+00:00
-- url     : https://prove2.me/submissions/5578e3cc-235d-4bef-8fb3-37482f400b11

import Definitions.Def_Formalism_SizeWindowBrackets_WindowSettingSatisfiable
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_OneLeThresholdMulPowers
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_facts
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_zpos
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_apos
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_size_total_bound
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_secondIo_le_unit
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_side_condition_of_windows
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_loss_choice_uniform
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_second_term_le
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_first_kind_bound
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_bad_le
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_first_le
import Theorems.Thm_Formalism_LFunctionChainParameters_DeficitSplitLemmas_loss_bound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
open Finset Classical
open Formalism.LFunctionChainParameters.DeficitSplitLemmas Formalism.LFunctionChainParameters.LErr
namespace Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
theorem _root_.solution : WindowLossesBound := by
  obtain ⟨C₁, hC₁⟩ := first_kind_bound
  refine ⟨max C₁ 0, le_max_right _ _, ?_⟩
  intro P e K hCord hW hL ι κ τ U Ω _ π Ps s sB J TT BAD Sig io D hS
  obtain ⟨hTT, hPs, hπ0, hπ1, hs, hSig0, hSigm, hio, hsB, hTops, hAll⟩ := hS
  obtain ⟨z, u, E, X, S, sb, v, w8, F⟩ := facts hW hL
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, -⟩ :=
    side_condition_of_windows P e K hW hL
  have hm : (0 : ℝ) ≤ (J.card : ℝ) := Nat.cast_nonneg _
  have hT : (1 : ℝ) ≤ (TT.card : ℝ) := by exact_mod_cast Finset.card_pos.2 hTT
  have hT0 : (0 : ℝ) ≤ (TT.card : ℝ) := Nat.cast_nonneg _
  have ha0 : 0 ≤ P.a := F.apos.le
  have hdet : ∀ υ o, (D υ o).ASK P.d Ps J TT - (D υ o).Ga J ≤ tDet P J.card TT.card +
      ∑ p ∈ s, (if P.θ < Sig p o then 4 * ((J.card : ℝ) * TT.card * P.a) * Real.log p / p else 0) := by
    intro υ o
    obtain ⟨hLed, hFirst, hSecond, hBad⟩ := hAll υ o
    obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11⟩ := hLed
    have led := loss_bound ι κ τ (D υ o).W (D υ o).below (D υ o).l Ps (D υ o).cl J TT (D υ o).TTp
      (D υ o).Iex (D υ o).at_ (D υ o).wz (D υ o).Id (D υ o).wd P.d (D υ o).gainW (D υ o).tauW
      (D υ o).gain (D υ o).tau (D υ o).lo (D υ o).fl P.a P.th P.wpp P.Xpp P.Xp P.C P.f P.N P.Sk P.Q₁ P.Q₂
      P.lx P.La P.k P.K₀ (D υ o).L₁ P.p₀ l1 (fun p hp => (hPs p hp).1) s1 s2 s3 s4 s5 s6 s7 s8 s9 s10
      s11 s12 s13 s14 s15 s16 s17 s18 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11
    have bad := bad_le P Ps sB (D υ o).cl TT (D υ o).TTp BAD J.card hm ha0 F.β0 s7 hsB hTops hBad
    have first := first_le hC₁ (by rw [hCord]; exact le_max_left _ _) hW hL Ps (D υ o).cl hPs hFirst
      J.card TT.card hm hT0
    have second := second_term_le Ps s (D υ o).cl (fun p => Sig p o) P.θ J.card TT.card P.a hm hT0 ha0
      hSecond
    unfold LD.ASK LD.Ga tDet tFloors tCp tPrLow tPrHigh tOr tHigh tD
    linarith
  have hθ : 0 < P.θ := by rw [F.hθ]; exact inv_pos.2 F.zpos
  obtain ⟨o, o1, o2, o3⟩ := loss_choice_uniform Ω U π
    (fun υ o => (D υ o).ASK P.d Ps J TT - (D υ o).Ga J) s Sig io (fun _ => tDet P J.card TT.card)
    P.Y P.θ P.s₀ ((J.card : ℝ) * TT.card * P.a) hπ0 hπ1 hθ F.s0 (by positivity) F.Y1 hs hSig0 hSigm
    hdet hio
  refine ⟨o, o1, fun υ => ?_, fun υ => ?_⟩
  · have h1 := o2 υ
    have h2 := size_total_bound P e K J.card TT.card hW hL hm hT
    unfold tSecondIo at h2
    linarith
  · have h1 := o3 υ
    have h2 := secondIo_le_unit hW hL hm hT
    unfold tSecondIo at h2
    linarith
end Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
