-- Prove2me | solution 1 for Formalism.L2.DIV.fk_map_initMinor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:09:05.569744+00:00
-- url     : https://prove2.me/submissions/486a8b10-fdd6-4db0-8acb-4dad1bfdc513

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefModLemmas
import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_FkMapInitMinor
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open MvPolynomial
open scoped Matrix
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.BasicNotions
namespace Formalism.L2.DIV
theorem _root_.solution {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {r n s : ℕ} (I : Fin s → Fin r)
    (hs : s ≤ n) : map φ (Formalism.GradedWeylDivisibility.initMinor R I hs) = Formalism.GradedWeylDivisibility.initMinor S I hs := by
  unfold Formalism.GradedWeylDivisibility.initMinor
  rw [RingHom.map_det]
  congr 1
  ext p q
  simp
end Formalism.L2.DIV
