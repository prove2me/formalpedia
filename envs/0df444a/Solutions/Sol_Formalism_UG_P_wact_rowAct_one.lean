-- Prove2me | solution 1 for Formalism.UG.P.wact_rowAct_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:40:56.150484+00:00
-- url     : https://prove2.me/submissions/dfa01345-a8ab-4531-8a4c-2a751e1d1415

import Definitions.Def_Formalism_SatakeDualWeyl_StatementW
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_DualWeylModuleStable
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
noncomputable section
open MvPolynomial
open Formalism Formalism.UG Formalism.UG.P
namespace Formalism.UG.P
theorem _root_.solution (R : Type) [CommRing R] (r n : ℕ) :
    Formalism.GradedWeylDivisibility.rowAct R (n := n) (1 : Matrix (Fin r) (Fin r) R) = AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  rintro ⟨i, j⟩
  simp [Formalism.GradedWeylDivisibility.rowAct, Matrix.one_apply, apply_ite C, ite_mul]
end Formalism.UG.P
