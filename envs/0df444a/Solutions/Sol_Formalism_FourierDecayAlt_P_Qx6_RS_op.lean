-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.RS_op
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:38:37.511157+00:00
-- url     : https://prove2.me/submissions/d35b0c44-fa37-4603-81a8-e1b96529ed56

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_opL_dir
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_fam_diff
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_near_update
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


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
theorem _root_.solution (hFO : FamOps) (hz : inWb k r z) (hz' : inWb k r z') (hS : SData z z' L Dc Dc₀ S) (l : Fin r)
    (hSl : ∀ c ∈ S, ∀ᶠ s in 𝓝 (c l), Function.update c l s ∈ S) (q : Fin 6) :
    Pres2 (RS z z' π π' L Dc Dc₀ S) (crd (opL l q)) (crd (opL l q)) := by
  intro Φ Ψ h
  refine ⟨hFO Wp Wq k r z z' π π' L Dc Φ hz hz' hS.o h.1 l q, hFO Wp Wq k r z z' π π' L Dc₀ Ψ hz hz' hS.o₀ h.2.1 l q,
    ?_⟩
  intro c hc g hg hgD
  have hcΩ := hS.sub hc
  have := opL_dir l q (f₁ := fun c' => Φ c' g) (f₂ := fun c' => Ψ c' g) (c := c) 1
    (fam_diff h.1 hcΩ hg hgD) (fam_diff h.2.1 hcΩ hg (hS.eq c hc ▸ hgD))
    (by
      filter_upwards [hSl c hc, near_update hS.o hcΩ hgD l] with s hs1 hs2
      rw [one_smul]
      exact h.2.2 _ hs1 g hg hs2.2)
  rw [one_smul] at this
  exact this
end Formalism.FourierDecayAlt.P.Qx6
