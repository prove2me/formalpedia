-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.RS_QL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:02:47.041866+00:00
-- url     : https://prove2.me/submissions/99e16096-bf08-488d-8a37-be6be2e78b73

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_fam_QL

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
variable {L : Fin (r + 1)} {Dc Dc₀ : (Fin r → ℂ) → Set (Mx k r)}
variable {S : Set (Fin r → ℂ)}
namespace Formalism.FourierDecayAlt.P.Qx6
theorem _root_.solution (hTP : TPreservesFF) (hLL : TLinLoc) (hz : inWb k r z) (hz' : inWb k r z')
    (hS : SData z z' L Dc Dc₀ S) (Y : ℂ) (a b : Fin 2) :
    Pres2 (RS z z' π π' L Dc Dc₀ S) (QL k r z z' L Y a b) (QL k r z z' L Y a b) := by
  intro Φ Ψ h
  refine ⟨fam_QL hTP hz hz' hS.d Y a b h.1, fam_QL hTP hz hz' hS.d₀ Y a b h.2.1, ?_⟩
  intro c hc g hg hgD
  have hcΩ := hS.sub hc
  have h2 : SmoothLev k r L (Dc c) (Ψ c) := by
    rw [hS.eq c hc]
    exact (h.2.1.2 c hcΩ).1
  exact ((hLL _ k r z z' L (Dc c) Y a b (Φ c) (Ψ c) 0 (hS.d c hcΩ).1 (h.1.2 c hcΩ).1 h2 g ⟨hg, hgD⟩).2)
    (fun x hx => h.2.2 c hc x hx.1 hx.2)
end Formalism.FourierDecayAlt.P.Qx6
