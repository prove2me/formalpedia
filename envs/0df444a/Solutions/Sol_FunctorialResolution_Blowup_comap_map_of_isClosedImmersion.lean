-- Prove2me | solution 1 for FunctorialResolution.Blowup.comap_map_of_isClosedImmersion
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:16:24.099919+00:00
-- url     : https://prove2.me/submissions/072262c6-460d-4fc1-b5e3-6f6c7dd6586a

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
namespace FunctorialResolution.Blowup
private theorem le_comap_map_of_isClosedImmersion {S X : Scheme.{u}} (ι : S ⟶ X)
    [IsClosedImmersion ι] (Z : S.IdealSheafData) : Z ≤ (Z.map ι).comap ι := by
  have hmapdef : Z.map ι = Scheme.Hom.ker (Z.subschemeι ≫ ι) := rfl
  have hcomapdef : (Z.map ι).comap ι
      = Scheme.Hom.ker (pullback.fst ι (Z.map ι).subschemeι) := rfl
  have hle : Scheme.Hom.ker (Z.subschemeι ≫ ι)
      ≤ Scheme.Hom.ker (Z.map ι).subschemeι := by
    rw [Scheme.IdealSheafData.ker_subschemeι, ← hmapdef]
  have hu : IsClosedImmersion.lift (Z.subschemeι ≫ ι) (Z.map ι).subschemeι hle
      ≫ (Z.subschemeι ≫ ι) = (Z.map ι).subschemeι :=
    IsClosedImmersion.lift_fac _ _ hle
  set u := IsClosedImmersion.lift (Z.subschemeι ≫ ι) (Z.map ι).subschemeι hle with hudef
  have hk : (pullback.snd ι (Z.map ι).subschemeι ≫ u) ≫ Z.subschemeι
      = pullback.fst ι (Z.map ι).subschemeι := by
    have h2 : ((pullback.snd ι (Z.map ι).subschemeι ≫ u) ≫ Z.subschemeι) ≫ ι
        = pullback.fst ι (Z.map ι).subschemeι ≫ ι := by
      rw [Category.assoc, Category.assoc, hu]
      exact pullback.condition.symm
    exact (cancel_mono ι).mp h2
  rw [hcomapdef, ← hk, Scheme.Hom.ker_comp]
  calc Z = (⊥ : Z.subscheme.IdealSheafData).map Z.subschemeι := by
        rw [Scheme.IdealSheafData.map_bot, Scheme.IdealSheafData.ker_subschemeι]
    _ ≤ _ := Scheme.IdealSheafData.map_mono Z.subschemeι bot_le
end FunctorialResolution.Blowup
namespace TopologicalSpace.NoetherianSpace
end TopologicalSpace.NoetherianSpace
namespace AlgebraicGeometry
namespace Scheme
namespace Hom
end Hom
end Scheme
end AlgebraicGeometry
end

set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open FunctorialResolution FunctorialResolution.Blowup
namespace FunctorialResolution.Blowup
theorem _root_.solution {S X : Scheme.{u}} (ι : S ⟶ X)
    [IsClosedImmersion ι] (Z : S.IdealSheafData) :
    (Z.map ι).comap ι = Z :=
  le_antisymm (Scheme.IdealSheafData.comap_map_le Z ι) (le_comap_map_of_isClosedImmersion ι Z)
end FunctorialResolution.Blowup
