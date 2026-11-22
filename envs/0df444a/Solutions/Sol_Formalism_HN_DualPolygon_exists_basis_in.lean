-- Prove2me | solution 1 for Formalism.HN.DualPolygon.exists_basis_in
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:29:58.303803+00:00
-- url     : https://prove2.me/submissions/28520902-d327-4192-a943-55a428776a29

import Definitions.Def_Formalism_HarderNarasimhan_QuotRealize
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Duality
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl

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
open Formalism Formalism.HN Formalism.HN.DualPolygon
open Formalism.HN
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
omit [Fintype ι] [DecidableEq ι]
namespace Formalism.HN.DualPolygon
theorem _root_.solution (A : Submodule (𝓞 K) V) [FiniteDimensional K V]
    (hsp : Submodule.span K (A : Set V) = ⊤) :
    ∃ (n : ℕ) (e : Basis (Fin n) K V), ∀ i, e i ∈ A := by
  obtain ⟨s, hsA, hspan, hli⟩ := exists_linearIndependent K (A : Set V)
  have hfin : s.Finite := hli.setFinite
  haveI : Fintype s := hfin.fintype
  let e0 : Basis s K V := Basis.mk hli (by rw [Subtype.range_coe, hspan, hsp])
  refine ⟨Fintype.card s, e0.reindex (Fintype.equivFin s), fun i => ?_⟩
  rw [Basis.reindex_apply, Basis.mk_apply]
  exact hsA (Subtype.mem _)
end Formalism.HN.DualPolygon
