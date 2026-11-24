-- Prove2me | solution 1 for Formalism.HN.DualPolygon.dualLat_le_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:13.017639+00:00
-- url     : https://prove2.me/submissions/11615461-79e1-4f02-9a5e-91bd3dd9809e

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
theorem _root_.solution {n : ℕ} (A : Submodule (𝓞 K) V) (e : Basis (Fin n) K V)
    (he : ∀ i, e i ∈ A) : dualLat A ≤ Submodule.span (𝓞 K) (Set.range e.dualBasis) := by
  intro f hf
  have h : ∀ i, ∃ a : 𝓞 K, algebraMap (𝓞 K) K a = f (e i) := fun i => hf (e i) (he i)
  choose a ha using h
  have hf' : f = ∑ i, a i • e.dualBasis i := by
    conv_lhs => rw [← e.dualBasis.sum_repr f]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Basis.dualBasis_repr, ← ha i, algebraMap_smul]
  rw [hf']
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
end Formalism.HN.DualPolygon
