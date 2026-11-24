-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.good_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:37:54.910161+00:00
-- url     : https://prove2.me/submissions/41ce9dc6-b651-4f2b-833c-44f44e1d3a45

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
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
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
variable {L : Fin (r + 1)} {Dc : (Fin r → ℂ) → Set (Mx k r)}
namespace Formalism.FourierDecayAlt.P.Qx6
theorem _root_.solution (hS : SData z z' L Dc Dc (OmX r)) {T : Fn k r (Wq →L[ℂ] Wp) → Fn k r (Wq →L[ℂ] Wp)}
    (hP : Pres2 (RS z z' π π' L Dc Dc (OmX r)) T T)
    (hl : ∀ Φ Ψ, FamFF k r z z' π π' L Dc Φ → FamFF k r z z' π π' L Dc Ψ → ∀ s : ℂ, ∀ c ∈ OmX r,
      ∀ g ∈ Glev k r L, g ∈ Dc c → T (Φ + s • Ψ) c g = T Φ c g + s • T Ψ c g) :
    (famData π π' hS).Good T where
  mem := fun Φ h => (hP Φ Φ ⟨h, h, fun _ _ _ _ _ => rfl⟩).1
  congr := fun Φ h Ψ h' he => (cutP_eq_iff _ _).2 (hP Φ Ψ ⟨h, h', (cutP_eq_iff _ _).1 he⟩).2.2
  lin := fun Φ h Ψ h' s => by
    show cutP L Dc _ = cutP L Dc _ + s • cutP L Dc _
    rw [← map_smul, ← map_add]
    exact (cutP_eq_iff _ _).2 (hl Φ Ψ h h' s)
end Formalism.FourierDecayAlt.P.Qx6
