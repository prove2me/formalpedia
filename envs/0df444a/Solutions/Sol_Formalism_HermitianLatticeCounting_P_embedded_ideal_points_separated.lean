-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.embedded_ideal_points_separated
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:16:49.223468+00:00
-- url     : https://prove2.me/submissions/4f5e1755-8653-4a34-9dca-c197e4a9db69

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_norm_placeEmbedding_sub
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_radius_pow_card_places

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Finset Real MeasureTheory NumberField Formalism.HermitianLatticeCounting.ExpansionTerms
open Classical
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (hn : IdealNormProductLowerBound) (E : Type) [Field E] [NumberField E] [NumberField.IsTotallyComplex E]
    (aa : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (haa : aa ≠ 0) (S : Finset E)
    (hS : ∀ D ∈ S, D ∈ aa) : IsNormSeparated (idealRadius E aa) (S.image (infinitePlaceEmbedding E)) := by
  intro D hD D' hD' hne
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hD
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hD'
  have hxy : x - y ≠ 0 := fun h => hne (by rw [sub_eq_zero.1 h])
  have hmem : x - y ∈ aa := by
    have := Submodule.sub_mem (aa : Submodule (𝓞 E) E) (hS x hx) (hS y hy)
    exact this
  rw [radius_pow_card_places E aa haa]
  simp_rw [norm_placeEmbedding_sub]
  exact hn E aa haa (x - y) hmem hxy
end Formalism.HermitianLatticeCounting.P
