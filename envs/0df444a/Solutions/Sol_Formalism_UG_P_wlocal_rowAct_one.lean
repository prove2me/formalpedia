-- Prove2me | solution 1 for Formalism.UG.P.wlocal_rowAct_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:36:42.598707+00:00
-- url     : https://prove2.me/submissions/d5cd724b-0be6-4ceb-abb3-cc873045c5c4

import Definitions.Def_Formalism_SatakeDualWeyl_StatementW
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal
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
open Formalism Formalism.UG Formalism.UG.P
open Formalism.GradedWeylDivisibility
variable {R : Type} [CommRing R]
namespace Formalism.UG.P
theorem _root_.solution {r n : ℕ} : rowAct R (n := n) (1 : Matrix (Fin r) (Fin r) R) = AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [rowAct, aeval_X, AlgHom.id_apply]
  rw [Finset.sum_eq_single v.1]
  · simp [Matrix.one_apply_eq]
  · intro b _ hb
    simp [Matrix.one_apply_ne (Ne.symm hb)]
  · intro h
    exact absurd (Finset.mem_univ _) h
end Formalism.UG.P
