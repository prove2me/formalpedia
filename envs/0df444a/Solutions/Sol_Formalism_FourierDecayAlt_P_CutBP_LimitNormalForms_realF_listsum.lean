-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms.realF_listsum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:33:12.935133+00:00
-- url     : https://prove2.me/submissions/6559d0d4-bcaa-4c65-98b3-2ef53d7127b0

import Definitions.Def_CompanionTheory_AutomorphicTheory_LocalBesselUniqueness_OpLocal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellHermitian
import Definitions.Def_CompanionTheory_AutomorphicTheory_LocalBesselUniqueness_HatProd
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutBP_LimitNormalForms_realF_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutBP_LimitNormalForms_realF_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
set_option linter.unusedSectionVars false
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms
open Formalism.FourierDecayAlt.P.CutMP
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
variable {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}
variable {e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)} {L : R.LevelData (MA.A P (MA.DQ P)) P.r} {o κ : ℕ}
namespace Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms
theorem _root_.solution {ι : Type} (l : List ι)
    (Φ : ι → (B.Mat P.k P.r → (Wq →L[ℂ] Wp)) → M.Ty P → MA.SmQ P.r P.TT)
    (h : ∀ i ∈ l, RealF P Bs e L o κ (Φ i)) : RealF P Bs e L o κ (fun J => (l.map fun i => Φ i J).sum) := by
  induction l with
  | nil => exact realF_zero
  | cons i l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact realF_add (h i (by simp)) (ih fun j hj => h j (by simp [hj]))
end Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms
