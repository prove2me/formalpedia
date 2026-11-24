-- Prove2me | solution 1 for Formalism.HC.Der.Rd.log_rd_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:05:11.306312+00:00
-- url     : https://prove2.me/submissions/806e20c9-9573-4281-9ca0-64a2e56bcd6e

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DecompTypeI
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdDiff
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdBound
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DvdDiscrOfInertia
import Theorems.Thm_Formalism_HC_Der_Rd_cycRat
import Theorems.Thm_Formalism_HC_Der_Rd_abel
import Theorems.Thm_Formalism_HC_Der_Rd_log_rd
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits
open Formalism.HC.Der.Rd
variable {φ : Frame} (H : HostRaw φ)
namespace Formalism.HC.Der.Rd
theorem _root_.solution : Real.log H.rd = SS H.art.ker := by
  have := cycRat H.condN
  let : Algebra H.E (CyclotomicField H.condN ℚ) := H.cycEmb.toRingHom.toAlgebra
  have h1 := log_rd H.cycZeta_prim H.E H.art.ker (fun σ u hσ => by
    have h2 := H.art_spec u σ hσ
    rw [MonoidHom.mem_ker, ← H.gal.symm.map_eq_one_iff]
    constructor
    · intro h3
      exact AlgEquiv.ext fun x => H.cycEmb.injective ((h2 x).trans (h3 x))
    · intro h3 x
      rw [h3] at h2
      exact (h2 x).symm)
  have h0 : (0 : ℝ) < |(discr H.E : ℝ)| := by simpa using discr_ne_zero H.E
  rw [HostRaw.rd, Real.log_rpow h0, one_div_mul_eq_div, h1, SS, ← abel]
end Formalism.HC.Der.Rd
