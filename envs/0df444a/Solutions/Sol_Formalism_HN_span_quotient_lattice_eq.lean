-- Prove2me | solution 1 for Formalism.HN.span_quotient_lattice_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:02.150654+00:00
-- url     : https://prove2.me/submissions/f5296866-8fca-4551-a110-d580cc1bb708

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_HarderNarasimhan_DefsPl
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_GramBlock
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtImage

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
namespace Formalism.HN
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (L N : Submodule ℤ E) (h : N ≤ L) :
    Submodule.span ℝ (Formalism.F.quot L N : Set E) =
      Submodule.span ℝ (L : Set E) ⊓ (Submodule.span ℝ (N : Set E))ᗮ := by
  set K := Submodule.span ℝ (N : Set E) with hK
  have hKU : K ≤ Submodule.span ℝ (L : Set E) := Submodule.span_mono (by exact_mod_cast h)
  have hcoe : (Formalism.F.quot L N : Set E) =
      (Kᗮ.starProjection : E →ₗ[ℝ] E) '' (L : Set E) := by
    simp only [Formalism.F.quot, Submodule.map_coe]
    rfl
  rw [hcoe, Submodule.span_image]
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    simp only [ContinuousLinearMap.coe_coe]
    refine Submodule.mem_inf.2 ⟨?_, ?_⟩
    · have h1 : x - Kᗮ.starProjection x ∈ K := by
        have h3 := Kᗮ.sub_starProjection_mem_orthogonal x
        rwa [Submodule.orthogonal_orthogonal] at h3
      have h2 : Kᗮ.starProjection x = x - (x - Kᗮ.starProjection x) := by abel
      rw [h2]
      exact Submodule.sub_mem _ hx (hKU h1)
    · exact (Kᗮ.orthogonalProjection x).2
  · intro y hy
    obtain ⟨hyU, hyK⟩ := Submodule.mem_inf.1 hy
    exact ⟨y, hyU, Submodule.starProjection_eq_self_iff.2 hyK⟩
end Formalism.HN
