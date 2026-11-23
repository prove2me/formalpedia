-- Prove2me | solution 1 for Formalism.UG.P.wlocal_map_hw
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:37:20.303314+00:00
-- url     : https://prove2.me/submissions/e1df0de2-10d9-42f0-8691-705daab1ae80

import Definitions.Def_Formalism_SatakeDualWeyl_StatementW
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal
import Theorems.Thm_Formalism_UG_P_wlocal_map_lpMinor

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
theorem _root_.solution (φ : R →+* S) {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) :
    map φ (hw R hn ν) = hw S hn ν := by
  unfold hw
  rw [map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_pow, wlocal_map_lpMinor]
end Formalism.UG.P
