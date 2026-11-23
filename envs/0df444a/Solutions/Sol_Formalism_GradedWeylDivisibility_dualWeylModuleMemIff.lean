-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.dualWeylModuleMemIff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:15:48.765249+00:00
-- url     : https://prove2.me/submissions/1615b453-3b05-4f5c-b172-205f9a21c4b2

import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LSatLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylPoint
import Theorems.Thm_Formalism_GradedWeylDivisibility_lsat_spec_colAddGen
import Theorems.Thm_Formalism_GradedWeylDivisibility_lsat_spec_rename
import Theorems.Thm_Formalism_GradedWeylDivisibility_lsat_eval_colAddGen
import Theorems.Thm_Formalism_GradedWeylDivisibility_lsat_mem_dualWeyl


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution : DualWeylPoint := by
  intro R _ _ _ r n ν f
  rw [lsat_mem_dualWeyl]
  refine and_congr_right fun _ => forall₂_congr fun l j => imp_congr_right fun _ => ?_
  constructor
  · intro h c
    let ψ : Option (Fin r × Fin n) → MvPolynomial (Fin r × Fin n) R :=
      fun o => Option.elim o (C c) X
    have h1 : aeval ψ (colAddGen R l j f) = aeval ψ (rename some f) := by rw [h]
    have e1 : aeval ψ (colAddGen R l j f) = colAdd R l j c f := by
      rw [← AlgHom.comp_apply, lsat_spec_colAddGen]
    have e2 : aeval ψ (rename some f) = f := by
      rw [← AlgHom.comp_apply, lsat_spec_rename, AlgHom.id_apply]
    rw [← e1, h1, e2]
  · intro h
    apply MvPolynomial.funext
    intro x
    have e := congrArg (fun φ => φ f) (lsat_eval_colAddGen (R := R) l j x)
    simp only [AlgHom.comp_apply, h] at e
    change aeval x (colAddGen R l j f) = aeval x (rename some f)
    rw [e, aeval_rename]
end Formalism.GradedWeylDivisibility
