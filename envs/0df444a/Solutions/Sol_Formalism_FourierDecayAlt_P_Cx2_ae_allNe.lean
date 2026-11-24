-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Cx2.ae_allNe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:22:57.791099+00:00
-- url     : https://prove2.me/submissions/50a4599d-8a69-41dc-b3db-998b67a5b30d

import Definitions.Def_Formalism_HermitianCurvature_StatementC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelZeroEstimateProduct
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwistedIsRealOrderLattice
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstNormRealNonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Filter Topology Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C NumberField MeasureTheory
open scoped ComplexOrder ComplexConjugate RealInnerProductSpace
noncomputable section
open Formalism.FourierDecayAlt.P.Cx2
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {Wp Wq : InfinitePlace E → Type} [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
namespace Formalism.FourierDecayAlt.P.Cx2
theorem _root_.solution (S : HidaSetting E Wp Wq) : ∀ᵐ c : J.CV E, ∀ v, c (S.pl v) ≠ 0 := by
  classical
  rw [ae_all_iff]
  intro v
  let p : J.CV E →ₗ[ℝ] ℂ :=
    ((EuclideanSpace.proj (S.pl v) : J.CV E →L[ℂ] ℂ) : J.CV E →ₗ[ℂ] ℂ).restrictScalars ℝ
  have hne : LinearMap.ker p ≠ ⊤ := by
    intro htop
    have hm : EuclideanSpace.single (S.pl v) (1 : ℂ) ∈ LinearMap.ker p := htop ▸ Submodule.mem_top
    simp [p] at hm
  have h0 := MeasureTheory.Measure.addHaar_submodule volume (LinearMap.ker p) hne
  rw [ae_iff]
  refine measure_mono_null (fun c hc => ?_) h0
  simp only [Set.mem_setOf_eq, not_not] at hc
  simp [p, hc]
end Formalism.FourierDecayAlt.P.Cx2
