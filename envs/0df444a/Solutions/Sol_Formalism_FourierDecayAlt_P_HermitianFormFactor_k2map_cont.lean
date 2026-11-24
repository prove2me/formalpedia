-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.k2map_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:19:51.705111+00:00
-- url     : https://prove2.me/submissions/78c6f06d-acfe-4a42-88d8-7869b6fc4c81

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_gram_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_cm_cont

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
theorem _root_.solution : Continuous (swapBlockPair : (Q → P → ℂ) × (Q → Q → ℂ) → (Q → Q → ℂ) × (Q → P → ℂ)) := by
  have hB : Continuous (fun p : (Q → P → ℂ) × (Q → Q → ℂ) => cm p.1) := cm_cont.comp continuous_fst
  have h1 : Continuous (fun p : (Q → P → ℂ) × (Q → Q → ℂ) =>
      ((gram p.2 - (cm p.1)ᴴ * cm p.1 : Matrix Q Q ℂ) : Q → Q → ℂ)) :=
    (gram_cont.comp continuous_snd).sub (hB.matrix_conjTranspose.matrix_mul hB)
  unfold swapBlockPair
  first
  | exact h1.prodMk continuous_fst
  | exact h1.prod_mk continuous_fst
end Formalism.FourierDecayAlt.P.HermitianFormFactor
