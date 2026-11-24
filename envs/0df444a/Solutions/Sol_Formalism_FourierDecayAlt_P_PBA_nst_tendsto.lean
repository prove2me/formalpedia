-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBA.nst_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:09:45.851857+00:00
-- url     : https://prove2.me/submissions/db209ad5-fc1f-451e-ba3d-12da86a7cd3f

import Definitions.Def_Formalism_HermitianCurvature_StatementKB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockOfCauchySchwarz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalNormNonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_gram_tendsto

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBA
open Formalism.FourierDecayAlt NumberField
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq)
  (RR : ℕ → Fin S.f → ℝ → ℕ → List C.Letter → C.LPt → C.LPt → ℂ)
variable {S RR}
namespace Formalism.FourierDecayAlt.P.PBA
theorem _root_.solution
    (hconv : ∀ v ε, 0 < ε → ∀ i a, D.AdmAt S v a → ∀ p q,
      Tendsto (fun n => RR n v ε i a p q) atTop (𝓝 ((S.pd v).RR ε i a p q)))
    {ε : ℝ} (hε : 0 < ε) (i s : ℕ) (w : S.W) (Y : Finset (TB.Pt E)) (κ : TB.Pt E → TB.Pt E → ℂ) (t t' : E) :
    Tendsto (fun n => (KB.withRR S (RR n)).base.Nst ε i s w Y κ t t') atTop
      (𝓝 (S.base.Nst ε i s w Y κ t t')) := by
  have e1 : ∀ n, (KB.withRR S (RR n)).base.Nst ε i s w Y κ t t' = (∑ h ∈ Y, ∑ h' ∈ Y,
      κ h h' * (KB.withRR S (RR n)).gram ε i w.1 (TB.join h s t) (TB.join h' s t')) / (S.base.wt w : ℂ) :=
    fun n => rfl
  have e2 : S.base.Nst ε i s w Y κ t t' = (∑ h ∈ Y, ∑ h' ∈ Y,
      κ h h' * S.gram ε i w.1 (TB.join h s t) (TB.join h' s t')) / (S.base.wt w : ℂ) := rfl
  rw [e2]; simp only [e1]
  apply Tendsto.div_const
  apply tendsto_finsetSum; intro h _
  apply tendsto_finsetSum; intro h' _
  exact tendsto_const_nhds.mul (gram_tendsto hconv hε i w _ _)
end Formalism.FourierDecayAlt.P.PBA
