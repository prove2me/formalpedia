-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx5.smooth_univ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:27:37.978879+00:00
-- url     : https://prove2.me/submissions/7a6060e8-3639-4d7f-b5fe-a9135fa6334b

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian

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
theorem _root_.solution {Φ : Fn k r (Wq →L[ℂ] Wp)} (hΦ : Φ ∈ RadSp k r z z' π π') {c : Fin r → ℂ} (hc : c ∈ OmX r)
    {K : Set (Mx k r)} (hK : IsCompact K) (hKD : K ⊆ Dp k r z z')
    (h0 : ∀ g ∈ Glev k r (Fin.last r), g ∉ K → Φ c g = 0) : SmoothLev k r (Fin.last r) Set.univ (Φ c) := by
  intro g₀ hg₀
  by_cases hgK : g₀ ∈ K
  · exact slice_smooth hΦ hc g₀ ⟨hg₀.1, hKD hgK⟩
  · exact ⟨Kᶜ, fun _ => 0, hK.isClosed.isOpen_compl, hgK, contDiffOn_const, fun g hg hgl => h0 g hgl hg⟩
end Formalism.FourierDecayAlt.P.Qx5
