-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLG.sum_unitB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:31:52.24395+00:00
-- url     : https://prove2.me/submissions/319a2126-7c0e-4e6f-88ac-23965d83d05e

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormRankFour
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ExistsFrameTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreKLLieGrpGeo
import Theorems.Thm_Formalism_FourierDecayAlt_P_OperatorRepresentations_Rep_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.QrD
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
noncomputable section
open Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLG
open Formalism.FourierDecayAlt.P.HermitianFormRankFour
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLG
theorem _root_.solution {m : ℕ} (Bs : Fin m → Fin (2 * r + k + 1) → ℂ) (B : Matrix (Fin m) (Fin m) ℂ) :
    colM Bs * B * ((colM Bs)ᴴ * Hpk k r) = ∑ p : Fin m × Fin m, B p.1 p.2 • unitB (Hpk k r) Bs p.1 p.2 := by
  ext i j
  have hu : ∀ a b, unitB (Hpk k r) Bs a b i j = Bs a i * ∑ q, star (Bs b q) * Hpk k r q j := by
    intro a b
    simp only [unitB, Matrix.of_apply, herm, dotProduct, Matrix.mulVec, bvec, Pi.star_apply]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    simp [Pi.single_apply]
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, smul_eq_mul, hu, Matrix.mul_apply, colM, Matrix.of_apply,
    Matrix.conjTranspose_apply]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, b]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro q _
  ring
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLG
