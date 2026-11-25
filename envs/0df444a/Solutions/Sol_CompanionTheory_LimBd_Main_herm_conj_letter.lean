-- Prove2me | solution 1 for CompanionTheory.LimBd.Main.herm_conj_letter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:14:20.629376+00:00
-- url     : https://prove2.me/submissions/84b44dec-bdb6-45f0-8bf1-055da3b1f017

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_ZuckDualTOfZuckDual
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CapelliEigenvalues_HeckeMultiplication
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_GeneratingFunctionPolynomial
import Theorems.Thm_CompanionTheory_LimBd_Main_hpk_herm
import Theorems.Thm_PI_UnitaryGroupMassFormula_CapelliEig_unitary_Hecke_group


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory CompanionTheory.LimBd CompanionTheory.LimBd.Main
open Formalism.FourierDecayAlt PI.UpqRep Matrix
open scoped ComplexConjugate
variable {k r : ℕ}
namespace CompanionTheory.LimBd.Main
theorem _root_.solution (x y : Fin (2 * r + k + 1) → ℂ) :
    (fun g : B.Mat k r => star (Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (g *ᵥ x) y)) ∈ Letters k r := by
  refine Submodule.subset_span (Or.inr ⟨y, Formalism.QuantumDeterminants.Hpk k r *ᵥ x, Or.inr fun g hg => ?_⟩)
  have hu := (PI.UnitaryGroupMassFormula.CapelliEig.unitary_Hecke_group k r g hg).1
  have hg' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
  have e : gᴴ * Formalism.QuantumDeterminants.Hpk k r = Formalism.QuantumDeterminants.Hpk k r * g⁻¹ := by
    conv_rhs => rw [← hg']
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hu), Matrix.mul_one]
  simp only [Formalism.QuantumDeterminants.herm]
  rw [← Matrix.star_dotProduct_star, star_star, Matrix.mulVec_mulVec, Matrix.star_mulVec,
    Matrix.star_mulVec, Matrix.conjTranspose_mul, hpk_herm, e, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
end CompanionTheory.LimBd.Main
