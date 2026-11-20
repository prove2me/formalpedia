-- Prove2me | solution 1 for DeletionCode.BubbleContextGeometry.deletion_geometry
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:22:34.905207+00:00
-- url     : https://prove2.me/submissions/06eb7293-08ff-4e47-984c-1915564a1953

import Definitions.Def_DeletionCode_BubbleEndpoints
import Definitions.Def_DeletionCode_BubblePathSimplicity
import Definitions.Def_DeletionCode_BubbleLocalSpectrum
import Definitions.Def_DeletionCode_BubbleContextGeometry
import Theorems.Thm_DeletionCode_BubbleContextGeometry_cut_bounds
import Theorems.Thm_DeletionCode_BubbleContextGeometry_lengths
import Theorems.Thm_DeletionCode_BubbleContextGeometry_middle_agree
import Theorems.Thm_DeletionCode_BubbleContextGeometry_delete_context
import Theorems.Thm_DeletionCode_BubbleEndpoints_deletion_endpoints
import Theorems.Thm_DeletionCode_BubblePathSimplicity_deletion_vertices_injective


set_option autoImplicit true
open DeletionCode DeletionCode.BubbleContextGeometry
open Windows HeaderRecovery CatalogueWords SpectrumLocalization
namespace DeletionCode.BubbleContextGeometry
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) (bubble : BubbleWord k)
    (hleft : bubble.left.getLast? = some (!bubble.bit))
    (hright : bubble.right.head? = some (!bubble.bit)) (x y : List Bool)
    (hx : KUnique (listLetters (x ++ (bubble.longWord ++ y)))
      (x ++ (bubble.longWord ++ y)).length k) : Geometry bubble := by
  have hlength := lengths bubble
  have hcut := (cut_bounds bubble).1
  have hpos : x.length + editOffset k < (x ++ (bubble.longWord ++ y)).length := by
    simp only [List.length_append]
    omega
  have hl : x.length + bubble.longWord.length ≤ (x ++ (bubble.longWord ++ y)).length := by
    simp only [List.length_append]
    omega
  have hs : x.length + bubble.shortWord.length ≤ (x ++ (bubble.longWord ++ y)).length - 1 := by
    simp only [List.length_append]
    omega
  have hshort : Agree (listLetters bubble.shortWord) 0
      (deleteAt (listLetters (x ++ (bubble.longWord ++ y))) (x.length + editOffset k))
      x.length bubble.shortWord.length := by
    rw [delete_context]
    exact middle_agree x bubble.shortWord y
  have hsimple := BubblePathSimplicity.deletion_vertices_injective hk bubble _ hx
    (x.length + editOffset k) hpos x.length hl hs (middle_agree x bubble.longWord y) hshort
  exact ⟨hsimple.1, hsimple.2, fun a b ha hb hag =>
    BubbleEndpoints.deletion_endpoints hk bubble hleft hright _ hx
      (x.length + editOffset k) hpos x.length hl hs
      (middle_agree x bubble.longWord y) hshort a b ha hb hag⟩
end DeletionCode.BubbleContextGeometry
