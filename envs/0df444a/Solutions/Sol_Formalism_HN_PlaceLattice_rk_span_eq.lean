-- Prove2me | solution 1 for Formalism.HN.PlaceLattice.rk_span_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:22.962737+00:00
-- url     : https://prove2.me/submissions/19a8a68d-b59b-4f51-943f-25bea07854a5

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Theorems.Thm_Formalism_HN_PlaceLattice_zl_span_eq
import Theorems.Thm_Formalism_HN_PlaceLattice_linIndep_int

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
    rk ρ (Submodule.span (𝓞 K) (Set.range e)) = Module.finrank ℚ K * Fintype.card ι' := by
  unfold rk Formalism.F.rk
  rw [zl_span_eq, finrank_span_eq_card (linIndep_int ρ hρ e he), Fintype.card_prod,
    ← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank]
end Formalism.HN.PlaceLattice
