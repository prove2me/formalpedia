-- Prove2me | solution 1 for Formalism.L2.SG.Pf.ColDictValCPf.isUnit_det_of_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:40:34.492528+00:00
-- url     : https://prove2.me/submissions/284d1cf9-dfc1-41ba-993e-728d42319e08

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_DivClosedOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_IsUnitDetOfUnitary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.ColDictValCPf
open Formalism.BasicNotions Formalism.GradedWeylDivisibility Formalism.L2.SG.Pf.ColDictPf Matrix MvPolynomial
open scoped ComplexOrder
variable {ι : Type} [Fintype ι] {n : ℕ}
namespace Formalism.L2.SG.Pf.ColDictValCPf
theorem _root_.solution {G g : Matrix (Fin n) (Fin n) ℂ} (hG : G.PosDef ∨ (-G).PosDef)
    (hg : gᴴ * G * g = G) : IsUnit g.det := by
  have hGd : G.det ≠ 0 := by
    rcases hG with h | h
    · exact h.det_pos.ne'
    · have h2 := h.det_pos.ne'
      rw [Matrix.det_neg] at h2
      intro h0
      apply h2
      rw [h0, mul_zero]
  rw [isUnit_iff_ne_zero]
  intro hg0
  have h3 := congrArg Matrix.det hg
  rw [Matrix.det_mul, Matrix.det_mul, hg0, mul_zero] at h3
  exact hGd h3.symm
end Formalism.L2.SG.Pf.ColDictValCPf
