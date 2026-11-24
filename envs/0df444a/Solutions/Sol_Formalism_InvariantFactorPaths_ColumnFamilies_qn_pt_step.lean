-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qn_pt_step
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:27.716883+00:00
-- url     : https://prove2.me/submissions/28ab75c9-45a2-4352-a493-29e4be3490a4

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QnPtEmpty
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
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
noncomputable section
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (n : ℕ) (D : Finset (Fin n × Fin n)) (a s : Fin n) (hw : (a, s) ∉ D)
    (hs : ∀ c, (s, c) ∉ D) (F : MvPolynomial (Fin n × Fin n) ℚ) :
    aeval (qn_pt n (insert (a, s) D)) F =
      Polynomial.eval₂ (aeval (qn_pt n D)).toRingHom (X (a, s)) (rowGen ℚ s a F) := by
  classical
  have h : (aeval (qn_pt n (insert (a, s) D))).toRingHom =
      (Polynomial.eval₂RingHom (aeval (qn_pt n D)).toRingHom (X (a, s))).comp (rowGen ℚ s a).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [rowGen, algebraMap_eq, Polynomial.algebraMap_apply]
    · rintro ⟨b, c⟩
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        rowGen, aeval_X, Polynomial.coe_eval₂RingHom]
      by_cases hb : b = a
      · subst hb
        by_cases hc : c = s
        · subst hc
          simp [qn_pt, hw, hs]
        · have h1 : (b, c) ≠ (b, s) := by simp [hc]
          have h2 : s ≠ c := fun h => hc h.symm
          simp [qn_pt, hs, h1, h2, hc]
      · have h1 : (b, c) ≠ (a, s) := by simp [hb]
        simp [qn_pt, h1, hb]
  exact congrArg (fun φ => φ F) h
end Formalism.InvariantFactorPaths.ColumnFamilies
