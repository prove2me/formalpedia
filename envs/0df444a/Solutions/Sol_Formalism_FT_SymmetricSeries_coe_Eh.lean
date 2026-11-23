-- Prove2me | solution 1 for Formalism.FT.SymmetricSeries.coe_Eh
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:43:09.742597+00:00
-- url     : https://prove2.me/submissions/b1eb0f4a-0571-4c5a-b10d-dc6c52e53175

import Definitions.Def_Formalism_ArtinHasse_Statement
import Definitions.Def_Formalism_ArtinHasse_ArtinHasseProofs_SymmSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.FT Formalism.FT.SymmetricSeries
variable {R : Type*} [CommRing R] {n : ℕ}
namespace Formalism.FT.SymmetricSeries
theorem _root_.solution (P : MvPolynomial (Fin n) R) :
    ((Eh R n P : MvPolynomial (Fin n) R) : MvPowerSeries (Fin n) R) =
      MvPowerSeries.subst (hv R n) (P : MvPowerSeries (Fin n) R) := by
  rw [MvPowerSeries.subst_coe]
  induction P using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.aeval_C, MvPowerSeries.algebraMap_apply]
    simp [Eh]
  | add p q hp hq => rw [map_add, MvPolynomial.coe_add, hp, hq, map_add]
  | mul_X p j hp =>
    rw [map_mul, MvPolynomial.coe_mul, hp, map_mul]
    congr 1
    simp [Eh, hv, Formalism.FT.hPS]
end Formalism.FT.SymmetricSeries
