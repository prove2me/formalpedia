-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.AdmissibleUnits.span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:08:57.382791+00:00
-- url     : https://prove2.me/submissions/99700548-e7b9-4e2c-9df2-10f46544e8ed

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_DedekindFactorK
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_UnitsEqOneOrNegOne
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_AdmissibleUnits_indep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
open NumberField Classical
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.AdmissibleUnits
variable {K : Type} [Field K] [NumberField K]
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.AdmissibleUnits
theorem _root_.solution (d : ℕ) (hd : 0 < d) (x : K) (hx : x ^ 2 = -(d : K)) (hK : Module.finrank ℚ K = 2)
    (y : K) : ∃ a b : ℚ, y = (a : K) + (b : K) * x := by
  have hli : LinearIndependent ℚ ![(1 : K), x] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    apply indep d hd x hx s t
    simpa [Algebra.smul_def, eq_ratCast] using hst
  let B := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hK])
  refine ⟨B.repr y 0, B.repr y 1, ?_⟩
  have := B.sum_repr y
  rw [Fin.sum_univ_two] at this
  simp only [B, coe_basisOfLinearIndependentOfCardEqFinrank, Matrix.cons_val_zero,
    Matrix.cons_val_one] at this
  conv_lhs => rw [← this]
  simp [Algebra.smul_def, eq_ratCast, B]
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.AdmissibleUnits
