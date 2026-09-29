-- Prove2me | solution 1 for Freiman.late_fork_endpoints_unswapped
-- status  : ACCEPTED   (prove)
-- author  : @Koki Yamada
-- created : 2026-09-16T10:56:04.187215+00:00
-- url     : https://prove2.me/submissions/0674434a-8235-4c6e-afa5-f619e7eb27f0

import Definitions.Def_Freiman_lateGeometry
import Mathlib.Tactic

open Freiman
attribute [local instance] Classical.propDecidable
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem child_digit (q : LowerPair) (d : ℕ+) :
    lowerChild q ([d], []) =
      ((lowerNormalize q).1 ++ [d], (lowerNormalize q).2) := by
  unfold lowerChild
  simp [List.reverse_cons, List.reverse_nil]

private theorem fork_words_false (n : LateNormalization) (d : ℕ+)
    (hw : n.wide = false) :
    lateForkWords n d = (n.label.1.reverse ++ [d], n.label.2) := by
  unfold lateForkWords lateWords lowerHistorySet lowerHistoryPick
  simp [hw]

theorem solution (p : LowerPair) (path : LatePath)
    (hm : lateMatches p path.right3)
    (hv : latePathValid lateCatalog path)
    (hn : ∀ n ∈ path.normalizations, lateNormalizationHolds p n)
    (n : LateNormalization) (hmem : n ∈ path.normalizations)
    (d : ℕ+) (hd : d ∈ ([1, 2] : List ℕ+)) (upper : Bool)
    (hw : n.wide = false) :
    lowerEndpoint (lowerChild (lowerChild p n.label) ([d], [])) upper =
      lowerEndpoint (lowerHistoryAppend (lowerNormalize p) (lateForkWords n d))
        upper := by
  have := hm
  have := hv
  have := hd
  have := upper
  have hnorm := hn n hmem
  set N := lowerNormalize p
  set child := lowerChild p n.label
  have hchild : child = (N.1 ++ n.label.1.reverse, N.2 ++ n.label.2) := by
    unfold child N lowerChild
    rfl
  have hNchild : lowerNormalize child = child := by
    simpa [lateNormalizationHolds, child, hw] using hnorm
  have hL : lowerChild child ([d], []) = (child.1 ++ [d], child.2) := by
    rw [child_digit, hNchild]
  have hR : lowerHistoryAppend N (lateForkWords n d) =
      (child.1 ++ [d], child.2) := by
    rw [fork_words_false n d hw, hchild]
    simp [lowerHistoryAppend, N, List.append_assoc]
  rw [hL, hR]
