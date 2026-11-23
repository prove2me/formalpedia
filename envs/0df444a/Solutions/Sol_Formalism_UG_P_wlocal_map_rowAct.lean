-- Prove2me | solution 1 for Formalism.UG.P.wlocal_map_rowAct
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:32:28.84814+00:00
-- url     : https://prove2.me/submissions/be52510e-39de-4833-a291-9dff3a0c5351

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
variable {R S : Type} [CommRing R] [CommRing S]
namespace Formalism.UG.P
theorem _root_.solution (φ : R →+* S) {r n : ℕ} (g : Matrix (Fin r) (Fin r) R)
    (f : MvPolynomial (Fin r × Fin n) R) :
    map φ (rowAct R g f) = rowAct S (g.map φ) (map φ f) := by
  have key : (map φ).comp (rowAct R (n := n) g).toRingHom =
      (rowAct S (n := n) (g.map φ)).toRingHom.comp (map φ) := by
    apply MvPolynomial.ringHom_ext
    · intro x
      simp [rowAct, MvPolynomial.algebraMap_eq]
    · intro v
      simp [rowAct, Matrix.map_apply]
  exact RingHom.congr_fun key f
end Formalism.UG.P
