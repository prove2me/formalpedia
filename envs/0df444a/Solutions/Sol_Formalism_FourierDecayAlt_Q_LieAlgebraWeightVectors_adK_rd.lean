-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.adK_rd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:49:36.179068+00:00
-- url     : https://prove2.me/submissions/e648721b-50aa-4ddc-b813-a59c6ed50174

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_GANormSqStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_AdUnitBCtMulVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_AdUnitBLie
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_curve_contDiff
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_curve_lev
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_rd_hasDeriv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_rd_smooth


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx2
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
  {D : Set (Mx k r)}
namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
theorem _root_.solution (hD : IsOpen D) {X : Mx k r} (hX : inLieLev k r (Fin.last r) X)
    {F : Mx k r → (Wq →L[ℂ] Wp)} (hF : F ∈ AdK k r z π D) : RdV X F ∈ AdK k r z π D := by
  refine ⟨rd_smooth hF.1 hX, ?_⟩
  intro x hx h hh
  have hd := rd_hasDeriv hF.1 hx hX
  have hd2 : HasDerivAt (fun t : ℝ => (π h).comp (F (x * NormedSpace.exp ((t : ℂ) • X))))
      ((π h).comp (RdV X F x)) 0 := by
    have := ((ContinuousLinearMap.compL ℂ Wq Wp Wp (π h)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
      (0 : ℝ) hd
    simpa [Function.comp_def] using this
  have hc : Continuous (fun t : ℝ => x * NormedSpace.exp ((t : ℂ) • X)) := by
    first
      | exact (Formalism.FourierDecayAlt.P.B5.curve_contDiff x X).continuous
      | fun_prop
  have hD0 : ∀ᶠ t : ℝ in 𝓝 0, x * NormedSpace.exp ((t : ℂ) • X) ∈ D :=
    hc.continuousAt.preimage_mem_nhds (by simpa using hD.mem_nhds hx.2)
  have hev : (fun t : ℝ => F (h * x * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[𝓝 0]
      fun t => (π h).comp (F (x * NormedSpace.exp ((t : ℂ) • X))) := by
    filter_upwards [hD0] with t ht
    rw [Matrix.mul_assoc]
    exact hF.2 _ ⟨curve_lev hx.1 hX t, ht⟩ h hh
  exact (hd2.congr_of_eventuallyEq hev).deriv
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
