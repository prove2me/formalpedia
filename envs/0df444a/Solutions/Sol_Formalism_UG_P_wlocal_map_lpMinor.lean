-- Prove2me | solution 1 for Formalism.UG.P.wlocal_map_lpMinor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:32:28.457329+00:00
-- url     : https://prove2.me/submissions/66925d53-48c9-432b-9539-b4512dd9c41b

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
theorem _root_.solution (φ : R →+* S) {r n : ℕ} (s : ℕ) (hr : s ≤ r) (hn : s ≤ n) :
    map φ (lpMinor R (r := r) (n := n) s hr hn) = lpMinor S s hr hn := by
  unfold lpMinor
  rw [RingHom.map_det]
  congr 1
  ext p q
  simp
end Formalism.UG.P
