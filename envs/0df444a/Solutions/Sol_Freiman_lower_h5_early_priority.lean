-- Prove2me | solution 1 for Freiman.lower_h5_early_priority
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-13T08:37:05.800664+00:00
-- url     : https://prove2.me/submissions/63381444-9f0e-49ea-9b52-545201fadeb8

import Definitions.Def_Freiman_lowerH5Verification
import Definitions.Def_Freiman_lowerInitialEntry
import Mathlib.Tactic

open Freiman

theorem solution
    (ho : ∀ p : LowerPair, lowerEndpoint p false ≤ lowerEndpoint p true)
    (p : LowerPair) (t : ℝ) (hs : lowerState t p) (hd : lowerEarlyDomain p)
    (hg : lowerEarlyGeometry p)
    (ha : lowerLocalLower p ([3],[2]) ≤ lowerH5ParentLower p)
    (hp : ∀ l ∈ lowerEarlyList p, t ∉ lowerCover (lowerChild p l)) :
    lowerH5LocalUpper p ([2],[2]) < lowerLocalCoordinate p t := by
  let U : Set ℝ := {x | ∃ l ∈ lowerEarlyList p, x ∈ lowerCover (lowerChild p l)}
  have htU : t ∉ U := by
    rintro ⟨l, hl, htl⟩
    exact hp l hl htl
  have hconn : IsPreconnected U := hg.2.1
  have h32sub : lowerCover (lowerChild p ([3],[2])) ⊆ U := hg.2.2.1
  have h22sub : lowerCover (lowerChild p ([2],[2])) ⊆ U := hg.2.2.2
  have hparent := hs.2.2.1
  unfold lowerCover at hparent
  simp only [Set.mem_Icc] at hparent
  by_cases he : (lowerNormalize p).1.length % 2 = 0
  · have hxmem : lowerEndpoint (lowerChild p ([3],[2])) false ∈
        lowerCover (lowerChild p ([3],[2])) := by
      unfold lowerCover
      exact ⟨le_rfl, ho _⟩
    have hzmem : lowerEndpoint (lowerChild p ([2],[2])) true ∈
        lowerCover (lowerChild p ([2],[2])) := by
      unfold lowerCover
      exact ⟨ho _, le_rfl⟩
    have hxU := h32sub hxmem
    have hzU := h22sub hzmem
    have hxt : lowerEndpoint (lowerChild p ([3],[2])) false ≤ t := by
      unfold lowerLocalLower lowerH5ParentLower at ha
      simp only [if_pos he] at ha
      exact ha.trans hparent.1
    unfold lowerH5LocalUpper lowerLocalCoordinate
    simp only [if_pos he]
    by_contra hzt
    have htz : t ≤ lowerEndpoint (lowerChild p ([2],[2])) true := le_of_not_gt hzt
    exact htU (hconn.ordConnected.out hxU hzU ⟨hxt, htz⟩)
  · have hxmem : lowerEndpoint (lowerChild p ([3],[2])) true ∈
        lowerCover (lowerChild p ([3],[2])) := by
      unfold lowerCover
      exact ⟨ho _, le_rfl⟩
    have hzmem : lowerEndpoint (lowerChild p ([2],[2])) false ∈
        lowerCover (lowerChild p ([2],[2])) := by
      unfold lowerCover
      exact ⟨le_rfl, ho _⟩
    have hxU := h32sub hxmem
    have hzU := h22sub hzmem
    have htx : t ≤ lowerEndpoint (lowerChild p ([3],[2])) true := by
      unfold lowerLocalLower lowerH5ParentLower at ha
      simp only [if_neg he] at ha
      linarith [hparent.2]
    unfold lowerH5LocalUpper lowerLocalCoordinate
    simp only [if_neg he]
    by_contra htz
    have hzt : lowerEndpoint (lowerChild p ([2],[2])) false ≤ t := by linarith
    exact htU (hconn.ordConnected.out hzU hxU ⟨hzt, htx⟩)

#print axioms solution
