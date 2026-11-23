-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DensitySumsAndDomination.domAfterOfLocal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:07:45.223304+00:00
-- url     : https://prove2.me/submissions/25ce81a3-cd41-4779-955c-03531d1d9826

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DensitySumsAndDomination
import Theorems.Thm_Formalism_FourierDecayAlt_P_DensitySumsAndDomination_psd_congr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TC
open scoped ComplexInnerProductSpace ComplexOrder ComplexConjugate
noncomputable section
open Classical
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DensitySumsAndDomination
namespace Formalism.FourierDecayAlt.P.DensitySumsAndDomination
theorem _root_.solution : DomAfterOfLocal := by
  intro hP hS hM E W _ D h
  have key : ∀ T : TB.Tower E, ∃ Th, DomText D T Th := by
    intro T
    have h' : ∀ i s : ℕ, ∃ Th0 : E → TB.Pt E → TB.Pt E → ℂ, 1 ≤ s → s ≤ i → i ≤ D.r + 1 →
        (∀ t : E, TB.PSDOn (T.X (i - s)) (Th0 t)) ∧
        (∀ t : E, t ≠ 0 →
          TB.PSDOn (T.X (i - s)) (fun h h' => Th0 t h h' - TB.blk (D.Kr i) s t t h h')) ∧
        (∀ t t' : E, t - t' ∈ D.La (i - s + 1) s →
          ∀ h ∈ T.X (i - s), ∀ h' ∈ T.X (i - s), Th0 t h h' = Th0 t' h h') ∧
        (∀ S : Finset E, (∀ t ∈ S, ∀ t' ∈ S, t - t' ∈ D.La (i - s + 1) s → t = t') →
          TB.PSDOn (T.X (i - s))
            (fun h h' => (1 + (D.e i : ℂ)) * D.Kr (i - s) h h' - ∑ t ∈ S, Th0 t h h')) := by
      intro i s
      by_cases hr : 1 ≤ s ∧ s ≤ i ∧ i ≤ D.r + 1
      · obtain ⟨P, _, S, a, hok, hN, hB, hL⟩ := h T i s hr.1 hr.2.1 hr.2.2
        obtain ⟨_, _, o3, o4, o5, o6⟩ := hS _ _ a _ _ (hP _ _ _ S _ hok)
        have hL' : D.La (i - s + 1) s = (J.scaleSys a (J.prodSys S)).L := hL
        refine ⟨(J.scaleSys a (J.prodSys S)).Th, fun _ _ _ => ⟨o4, fun t ht => ?_, fun t t' htt => ?_,
          fun R hR => ?_⟩⟩
        · refine psd_congr (fun x hx y hy => ?_) (o5 t ht)
          rw [← hN t ht x hx y hy]; rfl
        · exact o3 t t' (hL' ▸ htt)
        · refine psd_congr (fun x hx y hy => ?_) (o6 R (fun t ht t' ht' htt => hR t ht t' ht' (hL' ▸ htt)))
          rw [← hB x hx y hy]; rfl
      · exact ⟨fun _ _ _ => 0, fun a b c => absurd ⟨a, b, c⟩ hr⟩
    choose Th0 hTh0 using h'
    exact ⟨fun i s => Th0 i s, fun i s hs hsi hi => hTh0 i s hs hsi hi⟩
  refine ⟨key, fun T => ?_⟩
  obtain ⟨Th, hTh⟩ := key T
  exact ⟨Th, hM E W D T Th hTh⟩
end Formalism.FourierDecayAlt.P.DensitySumsAndDomination
