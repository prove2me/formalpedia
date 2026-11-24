-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBA.pw_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:53:59.351567+00:00
-- url     : https://prove2.me/submissions/68d90fba-2dda-4682-b0b2-08265c2610d4

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockOfCauchySchwarz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleOfPlaces

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField
open scoped ComplexConjugate ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBA
open Formalism.FourierDecayAlt
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq)
variable {S}
variable {A : Finset (Fin S.f)} {w : S.W} {n : ℕ} {U : Fin S.f → Finset (List C.Letter)}
  {θ : Fin S.f → List C.Letter → ℝ}
namespace Formalism.FourierDecayAlt.P.PBA
theorem _root_.solution (hP : ∀ v ∈ A, TB.IsProb (U v) (θ v)) (v : Fin S.f) (a : List C.Letter) :
    0 ≤ pw S A w θ v a := by
  unfold pw
  split_ifs with h1 h2
  · exact (hP v h1).1 a
  · exact zero_le_one
  · exact le_refl 0
end Formalism.FourierDecayAlt.P.PBA
