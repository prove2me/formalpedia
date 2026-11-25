-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx1.TC.transfer_operator_linear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:51:44.64098+00:00
-- url     : https://prove2.me/submissions/444f3f51-4b5e-4116-a69e-22471257d47f

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelCoordinatesCommute
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_ll_tL
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_smooth_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_smooth_zero


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
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
  [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
namespace Formalism.FourierDecayAlt.P.NFx1.TC
theorem _root_.solution {f₁ f₂ : Mx k r → (Wq →L[ℂ] Wp)} (h₁ : SmoothLev k r (Fin.last r) (Qx5.Dp k r z z') f₁)
    (h₂ : SmoothLev k r (Fin.last r) (Qx5.Dp k r z z') f₂) (Y : ℂ) (a b : Fin 2) (s₁ s₂ : ℂ) {g : Mx k r}
    (hg : g ∈ Glev k r (Fin.last r) ∩ Qx5.Dp k r z z') :
    tL k r z z' (Fin.last r) Y a b (fun y => s₁ • f₁ y + s₂ • f₂ y) g =
      s₁ • tL k r z z' (Fin.last r) Y a b f₁ g + s₂ • tL k r z z' (Fin.last r) Y a b f₂ g := by
  have hll := Qx2.ll_tL (E := Wq →L[ℂ] Wp) (i := Fin.last r) (Qx5.Dp_open k r z z') z z' Y a b
  have h0 := hll.lin (fun _ => 0) (fun _ => 0) 1 Qx2.smooth_zero Qx2.smooth_zero g hg
  have hs := hll.lin (fun _ => 0) f₁ s₁ Qx2.smooth_zero h₁ g hg
  have hm := hll.lin (fun y => s₁ • f₁ y) f₂ s₂ (Qx2.smooth_smul h₁ s₁) h₂ g hg
  simp only [one_smul, add_zero, zero_add, smul_zero] at h0 hs hm
  have h0' : tL k r z z' (Fin.last r) Y a b (fun _ => (0 : Wq →L[ℂ] Wp)) g = 0 :=
    add_left_cancel (h0.symm.trans (add_zero _).symm)
  rw [h0', zero_add] at hs
  rw [hm, hs]
end Formalism.FourierDecayAlt.P.NFx1.TC
