-- Prove2me | solution 1 for DeletionCode.BubbleContextGeometry.insertion_geometry
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:22:40.98618+00:00
-- url     : https://prove2.me/submissions/5515811a-e38b-4644-be3a-04498623ef18

import Definitions.Def_DeletionCode_BubbleEndpoints
import Definitions.Def_DeletionCode_BubblePathSimplicity
import Definitions.Def_DeletionCode_BubbleLocalSpectrum
import Definitions.Def_DeletionCode_BubbleContextGeometry
import Theorems.Thm_DeletionCode_BubbleContextGeometry_cut_bounds
import Theorems.Thm_DeletionCode_BubbleContextGeometry_lengths
import Theorems.Thm_DeletionCode_BubbleContextGeometry_middle_agree
import Theorems.Thm_DeletionCode_BubbleContextGeometry_insert_context
import Theorems.Thm_DeletionCode_BubbleEndpoints_insertion_endpoints
import Theorems.Thm_DeletionCode_BubblePathSimplicity_insertion_vertices_injective


set_option autoImplicit true
open DeletionCode DeletionCode.BubbleContextGeometry
open Windows HeaderRecovery CatalogueWords SpectrumLocalization
namespace DeletionCode.BubbleContextGeometry
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) (bubble : BubbleWord k)
    (hleft : bubble.left.getLast? = some (!bubble.bit))
    (hright : bubble.right.head? = some (!bubble.bit)) (x y : List Bool)
    (hx : KUnique (listLetters (x ++ (bubble.shortWord ++ y)))
      (x ++ (bubble.shortWord ++ y)).length k) : Geometry bubble := by
  have hlength := lengths bubble
  have hcut := (cut_bounds bubble).2
  have hpos : x.length + editOffset k ≤ (x ++ (bubble.shortWord ++ y)).length := by
    simp only [List.length_append]
    omega
  have hl : x.length + bubble.longWord.length ≤ (x ++ (bubble.shortWord ++ y)).length + 1 := by
    simp only [List.length_append]
    omega
  have hs : x.length + bubble.shortWord.length ≤ (x ++ (bubble.shortWord ++ y)).length := by
    simp only [List.length_append]
    omega
  have hlong : Agree (listLetters bubble.longWord) 0
      (insertAt (listLetters (x ++ (bubble.shortWord ++ y)))
        (x.length + editOffset k) bubble.bit) x.length bubble.longWord.length := by
    rw [insert_context]
    exact middle_agree x bubble.longWord y
  have hsimple := BubblePathSimplicity.insertion_vertices_injective hk bubble _ hx
    (x.length + editOffset k) bubble.bit hpos x.length hl hs hlong
    (middle_agree x bubble.shortWord y)
  exact ⟨hsimple.1, hsimple.2, fun a b ha hb hag =>
    BubbleEndpoints.insertion_endpoints hk bubble hleft hright _ hx
      (x.length + editOffset k) bubble.bit hpos x.length hl hs hlong
      (middle_agree x bubble.shortWord y) a b ha hb hag⟩
end DeletionCode.BubbleContextGeometry
