-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.LatticeDescentAlt.span_inf_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:35:25.245337+00:00
-- url     : https://prove2.me/submissions/10355233-c89e-4b35-ae79-c23f17334977

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_BetaSesquilinearity
import Definitions.Def_Formalism_LogFactorialIndices_LogProductFormula
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LatticeDescent
import Theorems.Thm_Formalism_LatticeIndexTer_LatticeIndexLength_exists_smul_mem_of_span


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeBaseChangeAlt
open Module
open Formalism.LatticeBaseChangeAlt.LatticeDescentAlt
variable {O K V : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
  [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
namespace Formalism.LatticeBaseChangeAlt.LatticeDescentAlt
theorem _root_.solution (M : Submodule O V) (hM : Formalism.LatticeIndexTer.IsLat O K V M) (V' : Submodule K V) :
    Submodule.span K ((M ⊓ V'.restrictScalars O : Submodule O V) : Set V) = V' := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    exact hx.2
  · intro v hv
    obtain ⟨d, hd, hdv⟩ := Formalism.LatticeIndexTer.LatticeIndexLength.exists_smul_mem_of_span (K := K) M hM.2 v
    have hd' : (algebraMap O K d) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 hd
    have hmem : d • v ∈ (M ⊓ V'.restrictScalars O : Submodule O V) := by
      refine ⟨hdv, ?_⟩
      show d • v ∈ V'
      rw [← algebraMap_smul K d v]
      exact V'.smul_mem _ hv
    have hsp := Submodule.subset_span (R := K) hmem
    have : v = (algebraMap O K d)⁻¹ • (d • v) := by
      rw [← algebraMap_smul K d v, smul_smul, inv_mul_cancel₀ hd', one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ hsp
end Formalism.LatticeBaseChangeAlt.LatticeDescentAlt
