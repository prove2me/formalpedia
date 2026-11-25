-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.hReal_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:27:31.882919+00:00
-- url     : https://prove2.me/submissions/65d46b83-40fd-4fb6-b031-5f718f48fa13

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGaugeCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDHat
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_hReal_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_hReal_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP
open NumberField
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cc : ℝ} {S : C.HidaSetting E Wp Wq} {T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))}
  {v : Fin S.f} {e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))}
  {L : R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r}
namespace Formalism.FourierDecayAlt.P.CutMP
theorem _root_.solution {ι : Type} (s : Finset ι) (X : ι → MA.A (D.parOf S v) (MA.DQ (D.parOf S v)))
    (h : ∀ i ∈ s, HReal Cc S T v e L (X i)) : HReal Cc S T v e L (∑ i ∈ s, X i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact hReal_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact hReal_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
end Formalism.FourierDecayAlt.P.CutMP
