-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.A.book_constants_pos_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:57:43.725423+00:00
-- url     : https://prove2.me/submissions/58bd3fcf-3a6b-4dcd-a863-4c4115f94fe4

import Definitions.Def_Formalism_HermitianCurvature_StatementPN
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalVolumePositivity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentBlockMeasure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormNormLemmas Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.A
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
open Finset
open Formalism.FourierDecayAlt
namespace Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.A
theorem _root_.solution {P : Type} [Fintype P] (B : S3.MassData P) (h : B.Pos) :
    0 < B.Gam1 ∧ 0 < B.μK ∧ 0 < B.μKpp ∧ 0 < B.μSpp ∧ 0 < B.μSpp' ∧ 0 < B.MM ∧ 0 < B.unitLevelVolume ∧
    0 < B.c0 ∧ 0 < B.c0' ∧ 0 < B.tt ∧ 0 < B.AA ∧ 0 < B.Dstar := by
  obtain ⟨hp, hKo, hSo, hSo', hMo, hU00o, hμH, hμH', hHpp, hHpp', hμN, hμN', hZZ, hPP, hal, hG, hHa, hHa',
    hNa, hNa', hB, hVH, hVH', hVN, hVN', hCoo, hdeg, hdimπ, hdimπ', hρ0, hρ0', hd, hd', hn0c, hsup, hδ⟩ := h
  have hg : ∀ p, 0 < B.g p := fun p => (hp p).1
  have hglk : ∀ p, 0 < B.glk p := fun p => (hp p).2.1
  have huk : ∀ p, 0 < B.uk p := fun p => (hp p).2.2.1
  have hKp : ∀ p, 0 < B.μKp p := fun p => (hp p).2.2.2.2.2.1
  have hKppp : ∀ p, 0 < B.μKppp p := fun p => (hp p).2.2.2.2.2.2.2.1
  have hSppp : ∀ p, 0 < B.μSppp p := fun p => (hp p).2.2.2.2.2.2.2.2.2.2.1
  have hSppp' : ∀ p, 0 < B.μSppp' p := fun p => (hp p).2.2.2.2.2.2.2.2.2.2.2.1
  have hMp : ∀ p, 0 < B.Mp p := fun p => (hp p).2.2.2.2.2.2.2.2.2.2.2.2.1
  have hU00p : ∀ p, 0 < B.localVolumeAtPlace p := fun p => (hp p).2.2.2.2.2.2.2.2.2.2.2.2.2
  have hμK : 0 < B.μK := show 0 < B.μKo * ∏ p, B.μKp p from mul_pos hKo (Finset.prod_pos fun p _ => hKp p)
  have hμKpp : 0 < B.μKpp := show 0 < B.μKo * ∏ p, B.μKppp p from
    mul_pos hKo (Finset.prod_pos fun p _ => hKppp p)
  have hMM : 0 < B.MM := show 0 < B.Mo * ∏ p, B.Mp p from mul_pos hMo (Finset.prod_pos fun p _ => hMp p)
  refine ⟨?_, hμK, hμKpp, ?_, ?_, hMM, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show 0 < ∏ p, B.glk p / B.uk p
    exact Finset.prod_pos fun p _ => div_pos (hglk p) (huk p)
  · show 0 < B.μSo * ∏ p, B.μSppp p
    exact mul_pos hSo (Finset.prod_pos fun p _ => hSppp p)
  · show 0 < B.μSo' * ∏ p, B.μSppp' p
    exact mul_pos hSo' (Finset.prod_pos fun p _ => hSppp' p)
  · show 0 < B.localVolumeArchimedean * ∏ p, B.localVolumeAtPlace p
    exact mul_pos hU00o (Finset.prod_pos fun p _ => hU00p p)
  · show 0 < B.volN * B.volH / B.dimπ
    exact div_pos (mul_pos hVN hVH) hdimπ
  · show 0 < B.volN' * B.volH' / B.dimπ'
    exact div_pos (mul_pos hVN' hVH') hdimπ'
  · show 0 < ∏ p, (1 + 3 / B.g p)
    exact Finset.prod_pos fun p _ => by have := hg p; positivity
  · show 0 < B.volB * B.Coo * (B.MM / B.volZZ) / B.μK
    exact div_pos (mul_pos (mul_pos hB hCoo) (div_pos hMM hZZ)) hμK
  · show 0 < B.deg * (B.volG / B.μKpp)
    exact mul_pos hdeg (div_pos hG hμKpp)
end Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.A
