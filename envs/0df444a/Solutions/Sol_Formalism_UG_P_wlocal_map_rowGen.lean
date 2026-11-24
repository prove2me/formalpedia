-- Prove2me | solution 1 for Formalism.UG.P.wlocal_map_rowGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:40:54.586106+00:00
-- url     : https://prove2.me/submissions/bc98e84b-185b-4fad-b08c-394f5b62b873

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
theorem _root_.solution (φ : R →+* S) {r n : ℕ} (a b : Fin r) (f : MvPolynomial (Fin r × Fin n) R) :
    rowGen S a b (map φ f) = Polynomial.map (map φ) (rowGen R a b f) := by
  have key : ((rowGen S a b).toRingHom.comp (map φ) : MvPolynomial (Fin r × Fin n) R →+* _) =
      (Polynomial.mapRingHom (map φ)).comp (rowGen R a b).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro x
      simp [rowGen, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
    · intro v
      by_cases h : v.1 = b <;> simp [rowGen, h]
  exact RingHom.congr_fun key f
end Formalism.UG.P
