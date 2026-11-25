-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.global_of_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:53:07.975088+00:00
-- url     : https://prove2.me/submissions/055e66b2-afeb-40f4-8010-88788c4eb450

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AxiomsFromFamilies
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx9_tb_congr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexConjugate ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : GlobalOfLocal := by
  intro hP hS E W P _ _ D i s S a Y hN hB hL hL' hok
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hS E _ a (prodSys S) Y (hP E _ P S Y hok)
  refine ⟨(scaleSys a (prodSys S)).Th, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t t' ht ht' h hh h' hh' hne
    apply hL'
    exact h1 t t' ht ht' h hh h' hh' (by rw [← hN t t' ht ht' h hh h' hh']; exact hne)
  · intro t ht
    exact Jx9.tb_congr (fun x hx y hy => (hN t t ht ht x hx y hy).symm) (h2 t ht)
  · intro t t' htt h hh h' hh'
    have h0 : t - t' ∈ (sysOf D i s).L := htt
    rw [hL] at h0
    exact h3 t t' h0 h hh h' hh'
  · exact h4
  · intro t ht
    refine Jx9.tb_congr (fun x hx y hy => ?_) (h5 t ht)
    show (scaleSys a (prodSys S)).Th t x y - (scaleSys a (prodSys S)).N t t x y =
      (scaleSys a (prodSys S)).Th t x y - (sysOf D i s).N t t x y
    rw [hN t t ht ht x hx y hy]
  · intro R hR
    refine Jx9.tb_congr (fun x hx y hy => ?_) (h6 R fun t ht t' ht' h => hR t ht t' ht' ?_)
    · show (scaleSys a (prodSys S)).B x y - ∑ t ∈ R, (scaleSys a (prodSys S)).Th t x y =
        (sysOf D i s).B x y - ∑ t ∈ R, (scaleSys a (prodSys S)).Th t x y
      rw [hB x hx y hy]
    · show t - t' ∈ (sysOf D i s).L
      rw [hL]; exact h
end Formalism.FourierDecayAlt.P
