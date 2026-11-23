-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx8.t_UniformMajorant
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:39:03.283533+00:00
-- url     : https://prove2.me/submissions/3bf5a860-098d-4758-8f3d-0ec627240112

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OutsideSystemsBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx8_psd_diag
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx8_psd_off
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx8_closed_and
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx8_closed_psd
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx8_ok_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx8_ok_congr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexOrder ComplexConjugate Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx8
namespace Formalism.FourierDecayAlt.P.Jx8
theorem _root_.solution : UniformMajorant := by
  classical
  intro E α _ N B L L' hyp
  have hS : IsCompact (Set.pi Set.univ fun _ : E => Set.pi Set.univ fun h : α => Set.pi Set.univ fun h' : α =>
      Metric.closedBall (0 : ℂ) ((B h h).re + (B h' h').re)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun h => isCompact_univ_pi fun h' => isCompact_closedBall _ _
  have hcl : ∀ F : Finset α, IsClosed {Th : E → α → α → ℂ | (LocSys.mk N Th B L L').Ok F} := by
    intro F
    simp only [LocSys.Ok]
    refine closed_and isClosed_const (closed_and isClosed_const (closed_and ?_ (closed_and ?_
      (closed_and ?_ ?_))))
    · simp only [Set.ofPred_forall]
      exact isClosed_iInter fun t => isClosed_iInter fun t' => isClosed_iInter fun _ =>
        isClosed_iInter fun h => isClosed_iInter fun _ => isClosed_iInter fun h' =>
        isClosed_iInter fun _ => isClosed_eq (by fun_prop) (by fun_prop)
    · simp only [Set.ofPred_forall]
      exact isClosed_iInter fun t => closed_psd F _ (fun x y => by fun_prop)
    · simp only [Set.ofPred_forall]
      exact isClosed_iInter fun t => isClosed_iInter fun _ => closed_psd F _ (fun x y => by fun_prop)
    · simp only [Set.ofPred_forall]
      exact isClosed_iInter fun R => isClosed_iInter fun _ => closed_psd F _ (fun x y => by fun_prop)
  have hdiag : ∀ (G : Finset α) (Th : E → α → α → ℂ), (LocSys.mk N Th B L L').Ok G → ∀ t, ∀ h ∈ G,
      0 ≤ (Th t h h).re ∧ (Th t h h).re ≤ (B h h).re := by
    intro G Th hOk t h hh
    simp only [LocSys.Ok] at hOk
    obtain ⟨_, _, _, h4, _, h6⟩ := hOk
    refine ⟨(psd_diag (h4 t) hh).2, ?_⟩
    have := (psd_diag (h6 {t} (by
      intro a ha b hb _; rw [mem_singleton.1 ha, mem_singleton.1 hb])) hh).2
    simp only [sum_singleton, Complex.sub_re] at this
    linarith
  have hB : ∀ h, 0 ≤ (B h h).re := by
    intro h
    obtain ⟨Th, hOk⟩ := hyp {h}
    have := hdiag {h} Th hOk 0 h (mem_singleton_self h)
    linarith [this.1, this.2]
  have key := hS.inter_iInter_nonempty
    (fun F : Finset α => {Th : E → α → α → ℂ | (LocSys.mk N Th B L L').Ok F}) hcl ?_
  · obtain ⟨Th, _, hTh⟩ := key
    exact ⟨Th, fun F => Set.mem_iInter.1 hTh F⟩
  · intro u
    obtain ⟨Th, hOk⟩ := hyp (u.biUnion id)
    have hOk' : (LocSys.mk N (fun t h h' => if h ∈ u.biUnion id ∧ h' ∈ u.biUnion id then Th t h h' else 0)
        B L L').Ok (u.biUnion id) :=
      ok_congr (fun t x hx y hy => by rw [if_pos ⟨hx, hy⟩]) hOk
    refine ⟨_, ?_, Set.mem_iInter₂.2 fun F hF => ok_mono (subset_biUnion_of_mem id hF) hOk'⟩
    intro t _ h _ h' _
    rw [mem_closedBall_zero_iff]
    beta_reduce
    by_cases hc : h ∈ u.biUnion id ∧ h' ∈ u.biUnion id
    · rw [if_pos hc]
      have hOk2 := hOk
      simp only [LocSys.Ok] at hOk2
      have a0 := psd_off (hOk2.2.2.2.1 t) hc.1 hc.2
      have a1 := (hdiag _ Th hOk t h hc.1).2
      have a2 := (hdiag _ Th hOk t h' hc.2).2
      linarith
    · rw [if_neg hc, norm_zero]; exact add_nonneg (hB h) (hB h')
end Formalism.FourierDecayAlt.P.Jx8
