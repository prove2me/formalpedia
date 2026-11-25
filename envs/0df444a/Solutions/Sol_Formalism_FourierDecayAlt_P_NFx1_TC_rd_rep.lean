-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx1.TC.rd_rep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:51:37.814789+00:00
-- url     : https://prove2.me/submissions/51528258-2af6-43ac-838e-ad1d70fc5d39

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelCoordinatesCommute
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_curve_lev
import Theorems.Thm_Formalism_REAL_hasDerivAt_mul_exp_smul_zero


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
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NFx1 Formalism.FourierDecayAlt.P.NFx1.TC
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.NF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)}
namespace Formalism.FourierDecayAlt.P.NFx1.TC
theorem _root_.solution {Φ : Fn k r E} {U : Set ((Fin r → ℂ) × Mx k r)} {F : (Fin r → ℂ) × Mx k r → E}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) (hΦ : ∀ y ∈ U, y.2 ∈ Glev k r i → Φ y.1 y.2 = F y)
    {X : Mx k r} (hX : inLieLev k r i X) {y : (Fin r → ℂ) × Mx k r} (hy : y ∈ U) (hyG : y.2 ∈ Glev k r i) :
    RdV X (Φ y.1) y.2 = fderiv ℝ F y ((0 : Fin r → ℂ), y.2 * X) := by
  have hγ : HasDerivAt (fun t : ℝ => ((y.1, y.2 * NormedSpace.exp ((t : ℂ) • X)) : (Fin r → ℂ) × Mx k r))
      ((0 : Fin r → ℂ), y.2 * X) 0 :=
    (hasDerivAt_const (0 : ℝ) y.1).prodMk (hasDerivAt_mul_exp_smul_zero y.2 X)
  have hγ0 : ((y.1, y.2 * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) : (Fin r → ℂ) × Mx k r) = y := by
    simp [NormedSpace.exp_zero]
  have hFd : DifferentiableAt ℝ F y := (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hy)
  have hcomp : HasDerivAt (fun t : ℝ => F (y.1, y.2 * NormedSpace.exp ((t : ℂ) • X)))
      (fderiv ℝ F y ((0 : Fin r → ℂ), y.2 * X)) 0 :=
    hFd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm
  have hev : (fun t : ℝ => Φ y.1 (y.2 * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[𝓝 0]
      (fun t : ℝ => F (y.1, y.2 * NormedSpace.exp ((t : ℂ) • X))) := by
    have hmem : ∀ᶠ t : ℝ in 𝓝 0, ((y.1, y.2 * NormedSpace.exp ((t : ℂ) • X)) : (Fin r → ℂ) × Mx k r) ∈ U :=
      hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hU.mem_nhds hy)
    filter_upwards [hmem] with t ht
    exact hΦ _ ht (Qx2.curve_lev hyG hX t)
  show deriv (fun t : ℝ => Φ y.1 (y.2 * NormedSpace.exp ((t : ℂ) • X))) 0 = _
  rw [hev.deriv_eq]
  exact hcomp.deriv
end Formalism.FourierDecayAlt.P.NFx1.TC
