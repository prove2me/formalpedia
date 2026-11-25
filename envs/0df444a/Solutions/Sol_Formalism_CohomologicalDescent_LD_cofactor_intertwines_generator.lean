-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.cofactor_intertwines_generator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:40:01.806805+00:00
-- url     : https://prove2.me/submissions/60671473-367f-417e-89e5-256de4516b4f

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Theorems.Thm_Formalism_CohomologicalDescent_LD_cofactor_of_variable
import Theorems.Thm_P2M_Formalism_CohomologicalDescent_LD_adjugate_transvection__6d6fcccee0b9
import Theorems.Thm_Formalism_CohomologicalDescent_LD_generator_map_generic_matrix
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowGen_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LA
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution {r : ℕ} (a b : Fin r) (hab : a ≠ b) (x : MvPolynomial (Fin r × Fin r) ℤ) :
    rowGen ℤ a b (cofMap r x) =
      Polynomial.eval₂ (Polynomial.C.comp (cofMap r).toRingHom) (-Polynomial.X)
        (rowGen ℤ (Fin.rev b) (Fin.rev a) x) := by
  have key : (rowGen ℤ a b).toRingHom.comp (cofMap r).toRingHom =
      (Polynomial.eval₂RingHom (Polynomial.C.comp (cofMap r).toRingHom) (-Polynomial.X)).comp
        (rowGen ℤ (Fin.rev b) (Fin.rev a)).toRingHom := by
    refine MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun v => ?_
    obtain ⟨c, s⟩ := v
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.coe_eval₂RingHom]
    rw [cofactor_of_variable, rowGen_X]
    have h2 : rowGen ℤ a b ((genericMatrix' ℤ r).adjugate (Fin.rev s) (Fin.rev c)) =
        (rowGen ℤ a b).mapMatrix (genericMatrix' ℤ r).adjugate (Fin.rev s) (Fin.rev c) := rfl
    rw [h2, AlgHom.map_adjugate, generator_map_generic_matrix, Matrix.adjugate_mul_distrib,
      adjugate_transvection' b a hab.symm, ← RingHom.map_adjugate]
    by_cases hc : c = Fin.rev a
    · subst hc
      rw [Fin.rev_rev, Matrix.mul_transvection_apply_same]
      simp [cofactor_of_variable]
    · have hc' : Fin.rev c ≠ a := fun h => hc (by rw [← h, Fin.rev_rev])
      rw [Matrix.mul_transvection_apply_of_ne _ _ _ _ hc']
      simp [cofactor_of_variable, hc]
  exact congrArg (fun F => F x) key
end Formalism.CohomologicalDescent.LD
