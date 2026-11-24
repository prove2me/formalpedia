-- Prove2me | solution 1 for Formalism.UG.P.wlocal_map_applyWord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:10:39.793844+00:00
-- url     : https://prove2.me/submissions/7ecce653-1343-42df-b44d-a442b7d5de46

import Definitions.Def_Formalism_SatakeDualWeyl_StatementW
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal
import Theorems.Thm_Formalism_UG_P_wlocal_map_rowDiv

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
open Formalism Formalism.UG Formalism.UG.P
open Formalism.GradedWeylDivisibility
variable {R S : Type} [CommRing R] [CommRing S]
namespace Formalism.UG.P
theorem _root_.solution (φ : R →+* S) {r n : ℕ} (w : List (Fin r × Fin r × ℕ))
    (f : MvPolynomial (Fin r × Fin n) R) :
    map φ (applyWord R w f) = applyWord S w (map φ f) := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    show map φ (rowDiv R x.1 x.2.1 x.2.2 (applyWord R w f)) =
      rowDiv S x.1 x.2.1 x.2.2 (applyWord S w (map φ f))
    rw [wlocal_map_rowDiv, ih]
end Formalism.UG.P
