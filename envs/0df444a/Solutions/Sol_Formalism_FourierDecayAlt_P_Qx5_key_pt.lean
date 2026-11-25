-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx5.key_pt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:00:18.037606+00:00
-- url     : https://prove2.me/submissions/d1405184-df42-449e-8826-2aa640b7c067

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx5_ntw_tL
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_map_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset MeasureTheory
open scoped ContDiff InnerProductSpace
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Qx2
variable {k r : ℕ}
variable {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
namespace Formalism.FourierDecayAlt.P.Qx5
theorem _root_.solution (X : ActualOps k r z z' π π') (Φ Ψ : RadSp k r z z' π π') {c : Fin r → ℂ} (hc : c ∈ OmX r) (Y : ℂ)
    (a b : Fin 2) (φ : (Wq →L[ℂ] Wp) →L[ℂ] ℂ) (x : Mx k r) :
    φ ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c x) * star (φ ((X.t Y a b Φ : Fn k r (Wq →L[ℂ] Wp)) c x)) =
      φ ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c x) *
        star (tL k r z z' (Fin.last r) Y a b (fun y => φ ((Φ : Fn k r (Wq →L[ℂ] Wp)) c y)) x) := by
  by_cases hx : (c, x) ∈ DomR k r z z'
  · have e1 := X.t_apply Y a b Φ (c, x) hx
    have e2 : tL k r z z' (Fin.last r) Y a b (fun y => φ ((Φ : Fn k r (Wq →L[ℂ] Wp)) c y)) x =
        φ (tL k r z z' (Fin.last r) Y a b ((Φ : Fn k r (Wq →L[ℂ] Wp)) c) x) :=
      ntw_tL (Dp_open k r z z') φ z z' Y a b _ (slice_smooth Φ.2 hc) x ⟨hx.2.1, hx.2.2⟩
    rw [e2, ← e1]
  · rw [Ψ.2.1 (c, x) hx, map_zero, zero_mul, zero_mul]
end Formalism.FourierDecayAlt.P.Qx5
