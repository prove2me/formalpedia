-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.SplitA.conjO_mem_hcompl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:41:15.359991+00:00
-- url     : https://prove2.me/submissions/8afed447-5686-4715-afa6-72354832d88b

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteDimensionalOfOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjOMemHcompl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.SplitA
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.HermitianLattices.Ext.L3.SplitA
theorem _root_.solution (p : Ideal (𝓞 K)) {s : 𝓞 K} (hs : s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p) :
    conjO K s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p := by
  have hle : Formalism.HermitianLatticesTheory.hcompl (K := K) p ≤
      (Formalism.HermitianLatticesTheory.hcompl (K := K) p).comap (conjO K).toMonoidHom := by
    unfold Formalism.HermitianLatticesTheory.hcompl
    rw [Submonoid.closure_le]
    rintro s ⟨hs1, hs2⟩
    rw [SetLike.mem_coe, Submonoid.mem_comap]
    apply Submonoid.subset_closure
    refine ⟨hs2 _ rfl, fun t ht => ?_⟩
    have hts : t = s := by
      apply FaithfulSMul.algebraMap_injective (𝓞 K) K
      rw [ht]
      exact star_star _
    rw [hts]; exact hs1
  exact hle hs
end Formalism.HermitianLattices.Ext.L3.SplitA
