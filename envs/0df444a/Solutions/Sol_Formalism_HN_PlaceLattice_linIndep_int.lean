-- Prove2me | solution 1 for Formalism.HN.PlaceLattice.linIndep_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:31:20.70934+00:00
-- url     : https://prove2.me/submissions/b8bdba4f-bb3f-4fb9-81ee-84cedf705b5f

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.HN
open Formalism.HN.PlaceLattice
variable {K : Type} [Field K] [NumberField K]
  {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.HN.PlaceLattice
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (ρ : V →+ E) (hρ : Function.Injective ρ) {ι' : Type} [Fintype ι']
    (e : ι' → V) (he : LinearIndependent K e) :
    LinearIndependent ℤ (fun p : Free.ChooseBasisIndex ℤ (𝓞 K) × ι' =>
        ρ (integralBasis K p.1 • e p.2)) := by
  have hb : LinearIndependent ℤ (integralBasis K) :=
    (integralBasis K).linearIndependent.restrict_scalars' ℤ
  have hc : LinearIndependent ℤ fun p : Free.ChooseBasisIndex ℤ (𝓞 K) × ι' =>
      integralBasis K p.1 • e p.2 :=
    linearIndependent_smul hb he
  exact hc.map' ρ.toIntLinearMap (LinearMap.ker_eq_bot.mpr hρ)
end Formalism.HN.PlaceLattice
