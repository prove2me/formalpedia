-- Prove2me | solution 1 for Formalism.RankSupermodularCovolume.covol_le_of_contraction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:35:55.585826+00:00
-- url     : https://prove2.me/submissions/e00e953d-9e19-4261-a981-a0a721acbb0e

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Theorems.Thm_Formalism_F_covol_eq_gram
import Theorems.Thm_Formalism_F_gram_det_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.RankSupermodularCovolume
open Formalism.F
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
namespace Formalism.RankSupermodularCovolume
theorem _root_.solution (Q1 Q2 : Submodule ℤ E) [DiscreteTopology Q1]
    [DiscreteTopology Q2] (φ : Q1 ≃ₗ[ℤ] Q2) (f : E →L[ℝ] E)
    (hf : ∀ x : Q1, ((φ x : Q2) : E) = f x) (hn : ∀ v, ‖f v‖ ≤ ‖v‖) : covol Q2 ≤ covol Q1 := by
  let v := Module.finBasis ℤ Q1
  let w := v.map φ
  rw [covol_eq_gram E Q1 _ v, covol_eq_gram E Q2 _ w]
  apply Real.sqrt_le_sqrt
  have h := gram_det_le E E _ (fun i => (v i : E)) (fun i => (w i : E)) 1 (fun c => by
    have : ∑ i, c i • ((w i : Q2) : E) = f (∑ i, c i • ((v i : Q1) : E)) := by
      simp only [w, Basis.map_apply, hf, map_sum, map_smul]
    rw [this, one_mul]
    exact hn _)
  simpa using h
end Formalism.RankSupermodularCovolume
