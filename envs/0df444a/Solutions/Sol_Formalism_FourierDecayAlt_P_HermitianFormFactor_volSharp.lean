-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.volSharp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:45:17.456813+00:00
-- url     : https://prove2.me/submissions/3dea98e7-35c9-4b74-ab28-d6737ab3d0e0

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_volExact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormFactor
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {m P Q : Type} [Fintype m] [DecidableEq m] [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  {H : Matrix m m ℂ} {Ep : Matrix m P ℂ} {Em : Matrix m Q ℂ}
attribute [local instance] isAddHaarMeasure_matrix_volume
attribute [local instance] haar_prod2
open scoped Pointwise
namespace Formalism.FourierDecayAlt.P.HermitianFormFactor
theorem _root_.solution : VolSharp := by
  intro k r μG hμ
  obtain ⟨C, -, hC⟩ := volExact k r μG hμ
  refine ⟨C, fun R hR => ?_⟩
  have hR0 : 0 ≤ R := by linarith
  have hsub : {g : Mt k r | gN (Matrix.of g) ≤ R} ⊆
      {g | gN (Matrix.of g) ^ 2 ≤ ((2 * r + k + 1 : ℕ) : ℝ) + 4 * R ^ 2} := by
    intro g hg
    have h0 : 0 ≤ gN (Matrix.of g) := Real.sqrt_nonneg _
    have h1 : gN (Matrix.of g) ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ h0 hg 2
    have h2 : (0 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    show gN (Matrix.of g) ^ 2 ≤ _
    nlinarith [sq_nonneg R]
  refine (measure_mono hsub).trans ?_
  rw [hC R hR0]
  have e : R ^ (2 * ((k : ℝ) + r) * ((r : ℝ) + 1)) = R ^ (2 * (k + r) * (r + 1)) := by
    rw [← Real.rpow_natCast]; push_cast; rfl
  rw [e, ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_coe_nnreal]
end Formalism.FourierDecayAlt.P.HermitianFormFactor
