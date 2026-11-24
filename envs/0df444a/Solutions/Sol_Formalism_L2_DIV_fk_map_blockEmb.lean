-- Prove2me | solution 1 for Formalism.L2.DIV.fk_map_blockEmb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:07:14.854394+00:00
-- url     : https://prove2.me/submissions/0a9b8bed-32a4-4093-95d5-c29bb87bb461

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
theorem _root_.solution {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {ι : Type} {k n : ℕ} (τ : ι)
    (f : MvPolynomial (Fin k × Fin n) R) :
    map φ (Formalism.GradedWeylDivisibility.blockEmb R τ f) = Formalism.GradedWeylDivisibility.blockEmb S τ (map φ f) := by
  simp only [Formalism.GradedWeylDivisibility.blockEmb]
  exact map_rename φ _ f
end Formalism.L2.DIV
