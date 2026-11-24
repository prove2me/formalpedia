-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd11.planeWaveVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:28:54.746801+00:00
-- url     : https://prove2.me/submissions/43e03b89-dfff-4e96-b258-b2da4520e2ad

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_free_io
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_comm_insL
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_cen_Uinv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_vlet_wave
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_free_bT

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd11
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.Wd1
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd11
theorem _root_.solution (σ : Site A) (f fi : A) (s : K) (w : List (Letter K S))
    (hW : IsWave f fi) (hc : f * σ.c = σ.c * f) (hci : f * σ.ci = σ.ci * f)
    (hp : σ.p * f = f * σ.p + algebraMap K A s * f * σ.c) (hw : (w.map Letter.intersection_update_fsHerm_neg_one).Nodup) :
    bT σ w * Vw f s w = io f * bT σ w := by
  induction w with
  | nil => simp [bT, Vw, UUiw]
  | cons l w ih =>
    rw [List.map_cons, List.nodup_cons] at hw
    have ih' : bT σ w * (io f * UUiw s w) = io f * bT σ w := ih hw.2
    have c1 : Commute (bT σ w) (ins l.intersection_update_fsHerm_neg_one (lift0 (Uinv (A := A) (if l.plus then s else star s)))) :=
      comm_insL (cen_Uinv _) (free_bT σ w _ hw.1)
    have c2 : Commute (io f : SlopeTestRemainingChoices S A)
        (ins l.intersection_update_fsHerm_neg_one (lift0 (Uinv (A := A) (if l.plus then s else star s)))) :=
      comm_insL (cen_Uinv _) (free_io _ f)
    show vlet σ l * bT σ w *
      (io f * (ins l.intersection_update_fsHerm_neg_one (lift0 (Uinv (A := A) (if l.plus then s else star s))) * UUiw s w)) =
      io f * (vlet σ l * bT σ w)
    rw [c2.left_comm, mul_assoc, c1.left_comm, ih', ← c2.left_comm, ← mul_assoc, ← mul_assoc,
      mul_assoc (vlet σ l), vlet_wave σ f fi s l hW hc hci hp, mul_assoc]
end Formalism.FourierDecayAlt.P.Wd11
