-- Prove2me | solution 1 for Formalism.HN.HeightGram.linIndep_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:17.708815+00:00
-- url     : https://prove2.me/submissions/d1c298b1-6288-4331-91f8-35537e1ed31e

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
noncomputable section
open Formalism Formalism.HN
open Formalism.HN.HeightGram
variable {K : Type} [Field K] [NumberField K]
  {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.HN.HeightGram
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (ρ : V →+ E) (hρ : Function.Injective ρ) {ι' : Type} [Fintype ι']
    (e : ι' → V) (he : LinearIndependent K e) :
    LinearIndependent ℤ (fun p : Free.ChooseBasisIndex ℤ (𝓞 K) × ι' =>
        ρ (integralBasis K p.1 • e p.2)) := by
  have hω : LinearIndependent ℤ (integralBasis K) := by
    first
    | exact (integralBasis K).linearIndependent.restrict_scalars (by intro a b h; simpa using h)
    | exact (integralBasis K).linearIndependent.restrict_scalars'
  have he' : LinearIndependent ℤ (fun p : Free.ChooseBasisIndex ℤ (𝓞 K) × ι' =>
      integralBasis K p.1 • e p.2) :=
    linearIndependent_smul hω he
  exact he'.map' ρ.toIntLinearMap (LinearMap.ker_eq_bot.2 hρ)
end Formalism.HN.HeightGram
