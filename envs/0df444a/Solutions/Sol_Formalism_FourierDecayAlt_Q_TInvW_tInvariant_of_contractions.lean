-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TInvW.tInvariant_of_contractions
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:38:51.619852+00:00
-- url     : https://prove2.me/submissions/bf99c8a4-8d80-4e88-af66-814139dad8dc

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_Development
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_chatA_inter
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_second_capelli_minor_intertwines
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_qdet_inter
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_chat_rep
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_second_capelli_minor_represents
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_qdet_rep
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_Ealg_gl
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_RL_inter
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_RL_apply
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_tl00
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_tl01
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_tl10
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_tl11
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_left_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TInvW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.Q.TInvW
theorem _root_.solution (hCC : ContractionsCovariant) (hP : EabPres) (hG : EabGlLev) (hL : QMinorLeftH)
    (hS : StepS) (hGr : StepGrp) (hV : StepVec) (hC : StepCongr) (hRt : StepRight) (hRS : StepRSm) :
    TInvariant := by
  intro E _ _ k r z z' i D f Y p q hz hz' hDom hf s hs s' hs' g hg
  have hDo : IsOpen D := hDom.1
  obtain ⟨hVl, hVr⟩ := hV k r z z' i hz hz'
  have hsG : s ∈ Glev k r i := ((hS k r z i hz).2 s hs).1
  have hs'G : s' ∈ Glev k r i := ((hS k r z' i hz').2 s' hs').1
  have h1z : (1 : Mx k r) ∈ Slev k r z i := (hS k r z i hz).1
  have h1z' : (1 : Mx k r) ∈ Slev k r z' i := (hS k r z' i hz').1
  have hh : s * g ∈ Glev k r i ∩ D := by
    refine ⟨hGr k r i s hsG g hg.1, ?_⟩
    simpa using hDom.2 g hg s hs 1 h1z'
  have hR : ∀ y ∈ Glev k r i ∩ D, y * s' ∈ Glev k r i ∩ D := fun y hy =>
    ⟨hGr k r i y hy.1 s' hs'G, by simpa using hDom.2 y hy 1 h1z s' hs'⟩
  rw [left_step hL k r z z' i Y p q (fun y => f (y * s')) s g (hVl s hs g).1 (hVl s hs g).2]
  obtain ⟨hQP, hPQ, hxv, hxbv, hyv⟩ := hVr s' hs'
  have hf' : SmoothLev k r i D (ext k r i D (fun p : Pt k r i D => f p.1)) :=
    lev_congr hDo (fun y hy => (ext_at (φ := fun p : Pt k r i D => f p.1) hy).symm) hf
  let x0 : Sm E k r i D := ⟨fun p => f p.1, hf'⟩
  have hrep : Rep f x0.1 := fun _ _ => rfl
  have hrep' : Rep (fun x => f (x * s')) (RL (E := E) hP hC hDo hR hRS hs'G x0).1 := fun _ _ => rfl
  have hint : ∀ a b, Ealg (E := E) (i := i) hP hC hDo a b * RL (E := E) hP hC hDo hR hRS hs'G =
      RL (E := E) hP hC hDo hR hRS hs'G * Econj (Ealg (E := E) (i := i) hP hC hDo) (blk i s'⁻¹) (blk i s') a b :=
    fun a b => RL_inter hP hC hDo hR hRS hs'G hRt a b
  have hGl : GlRel (Ealg (E := E) (i := i) hP hC hDo) := Ealg_gl hP hC hDo hG
  have cov := hCC (Module.End ℂ (Sm E k r i D)) (mdim k r i) (Ealg (E := E) (i := i) hP hC hDo)
    (blk i s'⁻¹) (blk i s') hGl hQP hPQ
  obtain ⟨hyvy, hybvy⟩ := hyv (s * g) hh.1
  have hy' := hR (s * g) hh
  match p, q with
  | 0, 0 =>
    rw [tl00, tl00, qdet_rep hP hC hDo _ hrep' (s * g) hh, qdet_rep hP hC hDo _ hrep (s * g * s') hy',
      RL_apply hP hC hDo hR hRS hs'G _ _ (qdet_inter _ _ _ hint _) x0 (s * g) hh,
      (cov (uC k r i Y) 0 0 0 0).1]
  | 0, 1 =>
    have e := (cov (uC k r i Y - 1) (xv k r z' i) 0 (ybv k r z i (s * g * s')) 0).2.1
    rw [hxv, ← hybvy] at e
    rw [tl01, tl01, Pi.neg_apply, Pi.neg_apply, chat_rep hP hC hDo _ _ _ hrep' (s * g) hh,
      chat_rep hP hC hDo _ _ _ hrep (s * g * s') hy',
      RL_apply hP hC hDo hR hRS hs'G _ _ (chatA_inter _ _ _ hint _ _ _) x0 (s * g) hh, e]
  | 1, 0 =>
    have e := (cov (uC k r i Y) (yv k r z i (s * g * s')) 0 (xbv k r z' i) 0).2.1
    rw [← hyvy, hxbv] at e
    rw [tl10, tl10, Pi.neg_apply, Pi.neg_apply, chat_rep hP hC hDo _ _ _ hrep' (s * g) hh,
      chat_rep hP hC hDo _ _ _ hrep (s * g * s') hy',
      RL_apply hP hC hDo hR hRS hs'G _ _ (chatA_inter _ _ _ hint _ _ _) x0 (s * g) hh, e]
  | 1, 1 =>
    have e := (cov (uC k r i Y - 1) (yv k r z i (s * g * s')) (xv k r z' i) (ybv k r z i (s * g * s'))
      (xbv k r z' i)).2.2
    rw [← hyvy, hxv, ← hybvy, hxbv] at e
    rw [tl11, tl11, Pi.neg_apply, Pi.neg_apply, second_capelli_minor_represents hP hC hDo _ _ _ _ _ hrep' (s * g) hh,
      second_capelli_minor_represents hP hC hDo _ _ _ _ _ hrep (s * g * s') hy',
      RL_apply hP hC hDo hR hRS hs'G _ _ (second_capelli_minor_intertwines _ _ _ hint _ _ _ _ _) x0 (s * g) hh, e]
end Formalism.FourierDecayAlt.Q.TInvW
