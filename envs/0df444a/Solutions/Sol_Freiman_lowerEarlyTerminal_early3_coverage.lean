-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_early3_coverage
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T13:01:21.030108+00:00
-- url     : https://prove2.me/submissions/95c18b34-09f3-48ca-9679-e4a3396092aa

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry
import Mathlib.Tactic.IntervalCases
open Freiman
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
private def earlyCompareFlags (C : LowerEarlyTerminalCatalog) (u : LowerPair) (a : Bool)
    (v : LowerPair) (b strict : Bool) : List Bool :=
  ((section14EndpointCases (lowerEarlyTerminalContext C) u a).map Prod.fst).flatMap fun x =>
    ((section14EndpointCases (lowerEarlyTerminalContext C) v b).map Prod.fst).map fun y =>
      decide (lowerEarlyTerminalGreater x y strict = LowerHistoryComparison.automatic)
private theorem earlyCompareFlags_eq (C : LowerEarlyTerminalCatalog) (u : LowerPair) (a : Bool)
    (v : LowerPair) (b strict : Bool) :
    earlyCompareFlags C u a v b strict =
      (lowerEarlyTerminalCompare C u a v b strict).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) := by
  simp [earlyCompareFlags,lowerEarlyTerminalCompare,List.map_flatMap,List.flatMap_map,List.map_map,Function.comp_def]
private def earlyRecordKeys (C : LowerEarlyTerminalCatalog) : List (ℕ × ℕ) := C.records.map fun r => (r.goal,r.branch)
private theorem earlyBucket_recorded (C : LowerEarlyTerminalCatalog) (g j : ℕ)
    (h : j ∈ (earlyRecordKeys C).filterMap (fun r => if r.1=g then some r.2 else none)) :
    ∃ r ∈ C.records, r.goal=g ∧ r.branch=j := by
  obtain ⟨key,hkey,hj⟩ := List.mem_filterMap.mp h
  by_cases hk : key.1=g
  · have hbr : key.2=j := by simpa only [if_pos hk,Option.some.injEq] using hj
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hkey
    exact ⟨r,hr,hk,hbr⟩
  · simp [hk] at hj
private theorem earlyCoverageTables_sound (C : LowerEarlyTerminalCatalog) (N : ℕ)
    (flags : Array (List Bool)) (buckets : Array (List ℕ))
    (hlen : C.goals.length=N)
    (hf : ∀ g, g<N → (lowerEarlyTerminalBranches C (lowerEarlyTerminalGoal C g).kind).map
      (fun z => decide (z.2=LowerHistoryComparison.automatic)) = flags[g]?.getD [])
    (hb : ∀ g, g<N → (earlyRecordKeys C).filterMap (fun r => if r.1=g then some r.2 else none) = buckets[g]?.getD [])
    (hc : ∀ g ∈ List.range N, ∀ bj ∈ (flags[g]?.getD []).zipIdx,
      bj.1=true ∨ bj.2 ∈ buckets[g]?.getD []) : lowerEarlyTerminalCoverage C := by
  intro g hg j hj
  have hgN : g<N := by simpa only [List.mem_range,hlen] using hg
  let bs := lowerEarlyTerminalBranches C (lowerEarlyTerminalGoal C g).kind
  have hjB : j<bs.length := List.mem_range.mp hj
  have hget : bs[j]?=some (bs[j]'hjB) := List.getElem?_eq_getElem hjB
  have hfget : (flags[g]?.getD [])[j]?=some (decide ((bs[j]'hjB).2=LowerHistoryComparison.automatic)) := by
    rw [←hf g hgN,List.getElem?_map]
    change Option.map (fun z => decide (z.2=LowerHistoryComparison.automatic)) bs[j]? = _
    rw [hget]
    rfl
  have hmem := List.mk_mem_zipIdx_iff_getElem?.mpr hfget
  rcases hc g (List.mem_range.mpr hgN) _ hmem with ha | hr
  · left
    change ((bs[j]?).getD ([],.impossible)).2 = _
    rw [hget]
    exact of_decide_eq_true ha
  · right
    apply earlyBucket_recorded C g j
    rw [hb g hgN]
    exact hr
private def earlyFields : Array CertField := #[⟨(553/1429),(1/1429),(0/1),(0/1)⟩,⟨(3289/10753),(1/10753),(0/1),(0/1)⟩,⟨(278/709),(-1/709),(0/1),(0/1)⟩,⟨(71/229),(-1/229),(0/1),(0/1)⟩,⟨(1413/4654),(-1/4654),(0/1),(0/1)⟩,⟨(1929/4946),(-1/14838),(0/1),(0/1)⟩,⟨(15/37),(-1/37),(0/1),(0/1)⟩,⟨(66/179),(-1/537),(0/1),(0/1)⟩,⟨(247/649),(1/649),(0/1),(0/1)⟩,⟨(16/59),(1/177),(0/1),(0/1)⟩,⟨(767/2749),(1/2749),(0/1),(0/1)⟩,⟨(3734/9757),(1/9757),(0/1),(0/1)⟩,⟨(89/214),(1/214),(0/1),(0/1)⟩,⟨(1272/3013),(1/3013),(0/1),(0/1)⟩,⟨(10/23),(-1/69),(0/1),(0/1)⟩,⟨(133/478),(-1/478),(0/1),(0/1)⟩,⟨(1950/7081),(-1/7081),(0/1),(0/1)⟩,⟨(517/1249),(-1/1249),(0/1),(0/1)⟩,⟨(7298/17677),(-1/17677),(0/1),(0/1)⟩,⟨(168/409),(1/409),(0/1),(0/1)⟩,⟨(1005/2426),(1/7278),(0/1),(0/1)⟩,⟨(223/529),(-1/529),(0/1),(0/1)⟩,⟨(1137/2714),(-1/8142),(0/1),(0/1)⟩,⟨(341/1237),(1/1237),(0/1),(0/1)⟩,⟨(1721/6218),(1/18654),(0/1),(0/1)⟩,⟨(246/877),(-1/877),(0/1),(0/1)⟩,⟨(1493/5354),(-1/16062),(0/1),(0/1)⟩,⟨(10780/38569),(1/38569),(0/1),(0/1)⟩,⟨(42/143),(1/429),(0/1),(0/1)⟩,⟨(1809/6094),(1/6094),(0/1),(0/1)⟩,⟨(43/142),(-1/142),(0/1),(0/1)⟩,⟨(731/2497),(-1/2497),(0/1),(0/1)⟩,⟨(3437/11762),(-1/35286),(0/1),(0/1)⟩,⟨(237/814),(1/814),(0/1),(0/1)⟩,⟨(4264/14557),(1/14557),(0/1),(0/1)⟩,⟨(317/1069),(-1/1069),(0/1),(0/1)⟩,⟨(4840/16393),(-1/16393),(0/1),(0/1)⟩,⟨(5/22),(1/22),(0/1),(0/1)⟩,⟨(4/13),(1/13),(0/1),(0/1)⟩,⟨(271/1006),(-1/1006),(0/1),(0/1)⟩,⟨(35/94),(1/94),(0/1),(0/1)⟩,⟨(32/83),(-1/249),(0/1),(0/1)⟩,⟨(1413/3718),(-1/3718),(0/1),(0/1)⟩,⟨(177/454),(-1/454),(0/1),(0/1)⟩,⟨(3230/8353),(-1/8353),(0/1),(0/1)⟩,⟨(2589/6674),(1/20022),(0/1),(0/1)⟩,⟨(45733/118318),(-1/118318),(0/1),(0/1)⟩,⟨(353/914),(1/2742),(0/1),(0/1)⟩,⟨(1364/3517),(-1/3517),(0/1),(0/1)⟩,⟨(21015/54241),(-1/54241),(0/1),(0/1)⟩,⟨(6697/22079),(-1/66237),(0/1),(0/1)⟩,⟨(469/1549),(1/1549),(0/1),(0/1)⟩,⟨(8222/27073),(1/27073),(0/1),(0/1)⟩,⟨(579/1894),(-1/1894),(0/1),(0/1)⟩,⟨(9014/29557),(-1/29557),(0/1),(0/1)⟩,⟨(13260/33937),(1/33937),(0/1),(0/1)⟩,⟨(82450/211453),(-1/211453),(0/1),(0/1)⟩,⟨(1932/4957),(1/4957),(0/1),(0/1)⟩,⟨(779/1994),(-1/5982),(0/1),(0/1)⟩,⟨(36569/93661),(-1/93661),(0/1),(0/1)⟩]
private abbrev earlyInput0 : LowerPair × Bool := (([2, 1, 1, 2], [3, 3]), true)
private def earlyCodes0 : List (ℕ × ℕ) := [(0, 1)]
private abbrev earlyInput1 : LowerPair × Bool := (([2, 1, 1, 3], [3, 3]), false)
private def earlyCodes1 : List (ℕ × ℕ) := [(2, 3), (2, 4), (2, 3), (5, 3)]
private abbrev earlyInput2 : LowerPair × Bool := (([2], [2]), false)
private def earlyCodes2 : List (ℕ × ℕ) := [(6, 6), (6, 7), (6, 6), (7, 6)]
private abbrev earlyInput3 : LowerPair × Bool := (([2, 1, 1, 1], [3, 1, 1]), true)
private def earlyCodes3 : List (ℕ × ℕ) := [(8, 9), (8, 10), (8, 9), (11, 9), (8, 9)]
private abbrev earlyInput4 : LowerPair × Bool := (([2, 2], [3, 1, 1]), true)
private def earlyCodes4 : List (ℕ × ℕ) := [(12, 9), (12, 10), (12, 9), (13, 9), (12, 9)]
private abbrev earlyInput5 : LowerPair × Bool := (([2, 2], [3, 1, 1]), false)
private def earlyCodes5 : List (ℕ × ℕ) := [(14, 15), (14, 15), (14, 16), (14, 15), (17, 15)]
private abbrev earlyInput6 : LowerPair × Bool := (([2, 2, 1], [3, 1, 1]), true)
private def earlyCodes6 : List (ℕ × ℕ) := [(12, 9), (12, 10), (12, 9), (13, 9)]
private abbrev earlyInput7 : LowerPair × Bool := (([2, 2, 2], [3, 1, 1]), false)
private def earlyCodes7 : List (ℕ × ℕ) := [(17, 15), (17, 16), (17, 15), (18, 15)]
private abbrev earlyInput8 : LowerPair × Bool := (([2, 2, 2], [3, 1, 1]), true)
private def earlyCodes8 : List (ℕ × ℕ) := [(19, 9), (19, 10), (19, 9), (20, 9)]
private abbrev earlyInput9 : LowerPair × Bool := (([2, 2, 1], [3, 1, 1]), false)
private def earlyCodes9 : List (ℕ × ℕ) := [(21, 15), (21, 16), (21, 15), (22, 15)]
private abbrev earlyInput10 : LowerPair × Bool := (([2, 2], [3, 1, 1, 1]), true)
private def earlyCodes10 : List (ℕ × ℕ) := [(12, 23), (12, 24), (12, 23), (13, 23)]
private abbrev earlyInput11 : LowerPair × Bool := (([2, 2], [3, 1, 1, 2]), false)
private def earlyCodes11 : List (ℕ × ℕ) := [(14, 25), (14, 26), (14, 25), (17, 25)]
private abbrev earlyInput12 : LowerPair × Bool := (([2, 2], [3, 1, 1, 2]), true)
private def earlyCodes12 : List (ℕ × ℕ) := [(12, 10), (12, 27), (12, 10), (13, 10)]
private abbrev earlyInput13 : LowerPair × Bool := (([2, 2], [3, 1, 1, 1]), false)
private def earlyCodes13 : List (ℕ × ℕ) := [(14, 15), (14, 16), (14, 15), (17, 15)]
private abbrev earlyInput14 : LowerPair × Bool := (([2, 2], [3, 2]), true)
private def earlyCodes14 : List (ℕ × ℕ) := [(12, 28), (12, 29), (12, 28), (13, 28)]
private abbrev earlyInput15 : LowerPair × Bool := (([2, 2], [3, 2]), false)
private def earlyCodes15 : List (ℕ × ℕ) := [(14, 30), (14, 31), (14, 30), (17, 30)]
private abbrev earlyInput16 : LowerPair × Bool := (([2, 2, 1], [3, 2]), true)
private def earlyCodes16 : List (ℕ × ℕ) := [(12, 28), (12, 28), (12, 29), (12, 28), (13, 28)]
private abbrev earlyInput17 : LowerPair × Bool := (([2, 2, 2], [3, 2]), false)
private def earlyCodes17 : List (ℕ × ℕ) := [(17, 30), (17, 31), (17, 30), (18, 30), (17, 30)]
private abbrev earlyInput18 : LowerPair × Bool := (([2, 2, 2], [3, 2]), true)
private def earlyCodes18 : List (ℕ × ℕ) := [(19, 28), (19, 28), (19, 29), (19, 28), (20, 28)]
private abbrev earlyInput19 : LowerPair × Bool := (([2, 2, 1], [3, 2]), false)
private def earlyCodes19 : List (ℕ × ℕ) := [(21, 30), (21, 31), (21, 30), (22, 30), (21, 30)]
private abbrev earlyInput20 : LowerPair × Bool := (([2, 2], [3, 2, 1]), true)
private def earlyCodes20 : List (ℕ × ℕ) := [(12, 28), (12, 29), (12, 28), (13, 28), (12, 28)]
private abbrev earlyInput21 : LowerPair × Bool := (([2, 2], [3, 2, 2]), false)
private def earlyCodes21 : List (ℕ × ℕ) := [(14, 31), (14, 31), (14, 32), (14, 31), (17, 31)]
private abbrev earlyInput22 : LowerPair × Bool := (([2, 2], [3, 2, 2]), true)
private def earlyCodes22 : List (ℕ × ℕ) := [(12, 33), (12, 34), (12, 33), (13, 33), (12, 33)]
private abbrev earlyInput23 : LowerPair × Bool := (([2, 2], [3, 2, 1]), false)
private def earlyCodes23 : List (ℕ × ℕ) := [(14, 35), (14, 35), (14, 36), (14, 35), (17, 35)]
private abbrev earlyInput24 : LowerPair × Bool := (([3], [2]), true)
private def earlyCodes24 : List (ℕ × ℕ) := [(37, 38), (37, 12), (37, 38), (28, 38)]
private abbrev earlyInput25 : LowerPair × Bool := (([3], [2]), false)
private def earlyCodes25 : List (ℕ × ℕ) := [(39, 6)]
private abbrev earlyInput26 : LowerPair × Bool := (([2], [2]), true)
private def earlyCodes26 : List (ℕ × ℕ) := [(38, 38), (38, 12), (38, 38), (12, 38)]
private abbrev earlyInput27 : LowerPair × Bool := (([2, 1, 1], [3, 1, 1]), true)
private def earlyCodes27 : List (ℕ × ℕ) := [(40, 9), (40, 10), (40, 9), (0, 9)]
private abbrev earlyInput28 : LowerPair × Bool := (([2, 1, 1], [3, 1, 1]), false)
private def earlyCodes28 : List (ℕ × ℕ) := [(41, 15), (41, 16), (41, 15), (42, 15)]
private abbrev earlyInput29 : LowerPair × Bool := (([2, 1, 1, 2], [3, 1, 1]), false)
private def earlyCodes29 : List (ℕ × ℕ) := [(43, 15), (43, 15), (43, 16), (43, 15), (44, 15)]
private abbrev earlyInput30 : LowerPair × Bool := (([2, 1, 1, 2], [3, 1, 1]), true)
private def earlyCodes30 : List (ℕ × ℕ) := [(0, 9), (0, 10), (0, 9), (45, 9), (0, 9)]
private abbrev earlyInput31 : LowerPair × Bool := (([2, 1, 1, 1], [3, 1, 1]), false)
private def earlyCodes31 : List (ℕ × ℕ) := [(41, 15), (41, 15), (41, 16), (41, 15), (42, 15)]
private abbrev earlyInput32 : LowerPair × Bool := (([2, 1, 1], [3, 1, 1, 1]), true)
private def earlyCodes32 : List (ℕ × ℕ) := [(40, 23), (40, 23), (40, 24), (40, 23), (0, 23)]
private abbrev earlyInput33 : LowerPair × Bool := (([2, 1, 1], [3, 1, 1, 2]), false)
private def earlyCodes33 : List (ℕ × ℕ) := [(41, 25), (41, 26), (41, 25), (42, 25), (41, 25)]
private abbrev earlyInput34 : LowerPair × Bool := (([2, 1, 1], [3, 1, 1, 2]), true)
private def earlyCodes34 : List (ℕ × ℕ) := [(40, 10), (40, 10), (40, 27), (40, 10), (0, 10)]
private abbrev earlyInput35 : LowerPair × Bool := (([2, 1, 1], [3, 1, 1, 1]), false)
private def earlyCodes35 : List (ℕ × ℕ) := [(41, 15), (41, 16), (41, 15), (42, 15), (41, 15)]
private abbrev earlyInput36 : LowerPair × Bool := (([2, 1, 1], [3, 2]), true)
private def earlyCodes36 : List (ℕ × ℕ) := [(40, 28), (40, 28), (40, 29), (40, 28), (0, 28)]
private abbrev earlyInput37 : LowerPair × Bool := (([2, 1, 1], [3, 2]), false)
private def earlyCodes37 : List (ℕ × ℕ) := [(41, 30), (41, 31), (41, 30), (42, 30), (41, 30)]
private abbrev earlyInput38 : LowerPair × Bool := (([2, 1, 1, 1], [3, 2]), true)
private def earlyCodes38 : List (ℕ × ℕ) := [(8, 28), (8, 29), (8, 28), (11, 28)]
private abbrev earlyInput39 : LowerPair × Bool := (([2, 1, 1, 2], [3, 2]), false)
private def earlyCodes39 : List (ℕ × ℕ) := [(43, 30), (43, 31), (43, 30), (44, 30)]
private abbrev earlyInput40 : LowerPair × Bool := (([2, 1, 1, 2], [3, 2]), true)
private def earlyCodes40 : List (ℕ × ℕ) := [(0, 28), (0, 29), (0, 28), (45, 28)]
private abbrev earlyInput41 : LowerPair × Bool := (([2, 1, 1, 1], [3, 2]), false)
private def earlyCodes41 : List (ℕ × ℕ) := [(41, 30), (41, 31), (41, 30), (42, 30)]
private abbrev earlyInput42 : LowerPair × Bool := (([2, 1, 1], [3, 2, 1]), true)
private def earlyCodes42 : List (ℕ × ℕ) := [(40, 28), (40, 29), (40, 28), (0, 28)]
private abbrev earlyInput43 : LowerPair × Bool := (([2, 1, 1], [3, 2, 2]), false)
private def earlyCodes43 : List (ℕ × ℕ) := [(41, 31), (41, 32), (41, 31), (42, 31)]
private abbrev earlyInput44 : LowerPair × Bool := (([2, 1, 1], [3, 2, 2]), true)
private def earlyCodes44 : List (ℕ × ℕ) := [(40, 33), (40, 34), (40, 33), (0, 33)]
private abbrev earlyInput45 : LowerPair × Bool := (([2, 1, 1], [3, 2, 1]), false)
private def earlyCodes45 : List (ℕ × ℕ) := [(41, 35), (41, 36), (41, 35), (42, 35)]
private abbrev earlyInput46 : LowerPair × Bool := (([2, 1, 1, 2], [3, 3]), false)
private def earlyCodes46 : List (ℕ × ℕ) := [(43, 3), (43, 4), (43, 3), (44, 3)]
private abbrev earlyInput47 : LowerPair × Bool := (([2, 1, 1, 2, 1], [3, 3]), true)
private def earlyCodes47 : List (ℕ × ℕ) := [(0, 1), (0, 1)]
private abbrev earlyInput48 : LowerPair × Bool := (([2, 1, 1, 2, 2], [3, 3]), false)
private def earlyCodes48 : List (ℕ × ℕ) := [(44, 3), (44, 4), (44, 3), (46, 3), (44, 3)]
private abbrev earlyInput49 : LowerPair × Bool := (([2, 1, 1, 2, 2], [3, 3]), true)
private def earlyCodes49 : List (ℕ × ℕ) := [(47, 1), (47, 1)]
private abbrev earlyInput50 : LowerPair × Bool := (([2, 1, 1, 2, 1], [3, 3]), false)
private def earlyCodes50 : List (ℕ × ℕ) := [(48, 3), (48, 4), (48, 3), (49, 3), (48, 3)]
private abbrev earlyInput51 : LowerPair × Bool := (([2, 1, 1, 2], [3, 3, 1]), true)
private def earlyCodes51 : List (ℕ × ℕ) := [(0, 1), (0, 1)]
private abbrev earlyInput52 : LowerPair × Bool := (([2, 1, 1, 2], [3, 3, 2]), false)
private def earlyCodes52 : List (ℕ × ℕ) := [(43, 4), (43, 4), (43, 50), (43, 4), (44, 4)]
private abbrev earlyInput53 : LowerPair × Bool := (([2, 1, 1, 2], [3, 3, 2]), true)
private def earlyCodes53 : List (ℕ × ℕ) := [(0, 51), (0, 52), (0, 51), (45, 51), (0, 51)]
private abbrev earlyInput54 : LowerPair × Bool := (([2, 1, 1, 2], [3, 3, 1]), false)
private def earlyCodes54 : List (ℕ × ℕ) := [(43, 53), (43, 53), (43, 54), (43, 53), (44, 53)]
private abbrev earlyInput55 : LowerPair × Bool := (([2, 1, 1, 3], [3, 3]), true)
private def earlyCodes55 : List (ℕ × ℕ) := [(55, 1)]
private abbrev earlyInput56 : LowerPair × Bool := (([2, 1, 1, 3, 1], [3, 3]), true)
private def earlyCodes56 : List (ℕ × ℕ) := [(55, 1), (55, 1)]
private abbrev earlyInput57 : LowerPair × Bool := (([2, 1, 1, 3, 2], [3, 3]), false)
private def earlyCodes57 : List (ℕ × ℕ) := [(5, 3), (5, 4), (5, 3), (56, 3), (5, 3)]
private abbrev earlyInput58 : LowerPair × Bool := (([2, 1, 1, 3, 2], [3, 3]), true)
private def earlyCodes58 : List (ℕ × ℕ) := [(57, 1), (57, 1)]
private abbrev earlyInput59 : LowerPair × Bool := (([2, 1, 1, 3, 1], [3, 3]), false)
private def earlyCodes59 : List (ℕ × ℕ) := [(58, 3), (58, 4), (58, 3), (59, 3), (58, 3)]
private abbrev earlyInput60 : LowerPair × Bool := (([2, 1, 1, 3], [3, 3, 1]), true)
private def earlyCodes60 : List (ℕ × ℕ) := [(55, 1), (55, 1)]
private abbrev earlyInput61 : LowerPair × Bool := (([2, 1, 1, 3], [3, 3, 2]), false)
private def earlyCodes61 : List (ℕ × ℕ) := [(2, 4), (2, 4), (2, 50), (2, 4), (5, 4)]
private abbrev earlyInput62 : LowerPair × Bool := (([2, 1, 1, 3], [3, 3, 2]), true)
private def earlyCodes62 : List (ℕ × ℕ) := [(55, 51), (55, 51)]
private abbrev earlyInput63 : LowerPair × Bool := (([2, 1, 1, 3], [3, 3, 1]), false)
private def earlyCodes63 : List (ℕ × ℕ) := [(2, 53), (2, 53), (2, 54), (2, 53), (5, 53)]
private def earlyDecode (x : ℕ × ℕ) : CertField × CertField := (earlyFields[x.1]?.getD ⟨0,0,0,0⟩,earlyFields[x.2]?.getD ⟨0,0,0,0⟩)
private theorem hEC0 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput0.1 earlyInput0.2).map Prod.fst = earlyCodes0.map earlyDecode := by decide +kernel
private theorem hEC1 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput1.1 earlyInput1.2).map Prod.fst = earlyCodes1.map earlyDecode := by decide +kernel
private theorem hEC2 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput2.1 earlyInput2.2).map Prod.fst = earlyCodes2.map earlyDecode := by decide +kernel
private theorem hEC3 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput3.1 earlyInput3.2).map Prod.fst = earlyCodes3.map earlyDecode := by decide +kernel
private theorem hEC4 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput4.1 earlyInput4.2).map Prod.fst = earlyCodes4.map earlyDecode := by decide +kernel
private theorem hEC5 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput5.1 earlyInput5.2).map Prod.fst = earlyCodes5.map earlyDecode := by decide +kernel
private theorem hEC6 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput6.1 earlyInput6.2).map Prod.fst = earlyCodes6.map earlyDecode := by decide +kernel
private theorem hEC7 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput7.1 earlyInput7.2).map Prod.fst = earlyCodes7.map earlyDecode := by decide +kernel
private theorem hEC8 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput8.1 earlyInput8.2).map Prod.fst = earlyCodes8.map earlyDecode := by decide +kernel
private theorem hEC9 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput9.1 earlyInput9.2).map Prod.fst = earlyCodes9.map earlyDecode := by decide +kernel
private theorem hEC10 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput10.1 earlyInput10.2).map Prod.fst = earlyCodes10.map earlyDecode := by decide +kernel
private theorem hEC11 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput11.1 earlyInput11.2).map Prod.fst = earlyCodes11.map earlyDecode := by decide +kernel
private theorem hEC12 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput12.1 earlyInput12.2).map Prod.fst = earlyCodes12.map earlyDecode := by decide +kernel
private theorem hEC13 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput13.1 earlyInput13.2).map Prod.fst = earlyCodes13.map earlyDecode := by decide +kernel
private theorem hEC14 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput14.1 earlyInput14.2).map Prod.fst = earlyCodes14.map earlyDecode := by decide +kernel
private theorem hEC15 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput15.1 earlyInput15.2).map Prod.fst = earlyCodes15.map earlyDecode := by decide +kernel
private theorem hEC16 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput16.1 earlyInput16.2).map Prod.fst = earlyCodes16.map earlyDecode := by decide +kernel
private theorem hEC17 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput17.1 earlyInput17.2).map Prod.fst = earlyCodes17.map earlyDecode := by decide +kernel
private theorem hEC18 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput18.1 earlyInput18.2).map Prod.fst = earlyCodes18.map earlyDecode := by decide +kernel
private theorem hEC19 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput19.1 earlyInput19.2).map Prod.fst = earlyCodes19.map earlyDecode := by decide +kernel
private theorem hEC20 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput20.1 earlyInput20.2).map Prod.fst = earlyCodes20.map earlyDecode := by decide +kernel
private theorem hEC21 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput21.1 earlyInput21.2).map Prod.fst = earlyCodes21.map earlyDecode := by decide +kernel
private theorem hEC22 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput22.1 earlyInput22.2).map Prod.fst = earlyCodes22.map earlyDecode := by decide +kernel
private theorem hEC23 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput23.1 earlyInput23.2).map Prod.fst = earlyCodes23.map earlyDecode := by decide +kernel
private theorem hEC24 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput24.1 earlyInput24.2).map Prod.fst = earlyCodes24.map earlyDecode := by decide +kernel
private theorem hEC25 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput25.1 earlyInput25.2).map Prod.fst = earlyCodes25.map earlyDecode := by decide +kernel
private theorem hEC26 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput26.1 earlyInput26.2).map Prod.fst = earlyCodes26.map earlyDecode := by decide +kernel
private theorem hEC27 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput27.1 earlyInput27.2).map Prod.fst = earlyCodes27.map earlyDecode := by decide +kernel
private theorem hEC28 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput28.1 earlyInput28.2).map Prod.fst = earlyCodes28.map earlyDecode := by decide +kernel
private theorem hEC29 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput29.1 earlyInput29.2).map Prod.fst = earlyCodes29.map earlyDecode := by decide +kernel
private theorem hEC30 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput30.1 earlyInput30.2).map Prod.fst = earlyCodes30.map earlyDecode := by decide +kernel
private theorem hEC31 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput31.1 earlyInput31.2).map Prod.fst = earlyCodes31.map earlyDecode := by decide +kernel
private theorem hEC32 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput32.1 earlyInput32.2).map Prod.fst = earlyCodes32.map earlyDecode := by decide +kernel
private theorem hEC33 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput33.1 earlyInput33.2).map Prod.fst = earlyCodes33.map earlyDecode := by decide +kernel
private theorem hEC34 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput34.1 earlyInput34.2).map Prod.fst = earlyCodes34.map earlyDecode := by decide +kernel
private theorem hEC35 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput35.1 earlyInput35.2).map Prod.fst = earlyCodes35.map earlyDecode := by decide +kernel
private theorem hEC36 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput36.1 earlyInput36.2).map Prod.fst = earlyCodes36.map earlyDecode := by decide +kernel
private theorem hEC37 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput37.1 earlyInput37.2).map Prod.fst = earlyCodes37.map earlyDecode := by decide +kernel
private theorem hEC38 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput38.1 earlyInput38.2).map Prod.fst = earlyCodes38.map earlyDecode := by decide +kernel
private theorem hEC39 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput39.1 earlyInput39.2).map Prod.fst = earlyCodes39.map earlyDecode := by decide +kernel
private theorem hEC40 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput40.1 earlyInput40.2).map Prod.fst = earlyCodes40.map earlyDecode := by decide +kernel
private theorem hEC41 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput41.1 earlyInput41.2).map Prod.fst = earlyCodes41.map earlyDecode := by decide +kernel
private theorem hEC42 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput42.1 earlyInput42.2).map Prod.fst = earlyCodes42.map earlyDecode := by decide +kernel
private theorem hEC43 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput43.1 earlyInput43.2).map Prod.fst = earlyCodes43.map earlyDecode := by decide +kernel
private theorem hEC44 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput44.1 earlyInput44.2).map Prod.fst = earlyCodes44.map earlyDecode := by decide +kernel
private theorem hEC45 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput45.1 earlyInput45.2).map Prod.fst = earlyCodes45.map earlyDecode := by decide +kernel
private theorem hEC46 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput46.1 earlyInput46.2).map Prod.fst = earlyCodes46.map earlyDecode := by decide +kernel
private theorem hEC47 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput47.1 earlyInput47.2).map Prod.fst = earlyCodes47.map earlyDecode := by decide +kernel
private theorem hEC48 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput48.1 earlyInput48.2).map Prod.fst = earlyCodes48.map earlyDecode := by decide +kernel
private theorem hEC49 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput49.1 earlyInput49.2).map Prod.fst = earlyCodes49.map earlyDecode := by decide +kernel
private theorem hEC50 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput50.1 earlyInput50.2).map Prod.fst = earlyCodes50.map earlyDecode := by decide +kernel
private theorem hEC51 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput51.1 earlyInput51.2).map Prod.fst = earlyCodes51.map earlyDecode := by decide +kernel
private theorem hEC52 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput52.1 earlyInput52.2).map Prod.fst = earlyCodes52.map earlyDecode := by decide +kernel
private theorem hEC53 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput53.1 earlyInput53.2).map Prod.fst = earlyCodes53.map earlyDecode := by decide +kernel
private theorem hEC54 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput54.1 earlyInput54.2).map Prod.fst = earlyCodes54.map earlyDecode := by decide +kernel
private theorem hEC55 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput55.1 earlyInput55.2).map Prod.fst = earlyCodes55.map earlyDecode := by decide +kernel
private theorem hEC56 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput56.1 earlyInput56.2).map Prod.fst = earlyCodes56.map earlyDecode := by decide +kernel
private theorem hEC57 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput57.1 earlyInput57.2).map Prod.fst = earlyCodes57.map earlyDecode := by decide +kernel
private theorem hEC58 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput58.1 earlyInput58.2).map Prod.fst = earlyCodes58.map earlyDecode := by decide +kernel
private theorem hEC59 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput59.1 earlyInput59.2).map Prod.fst = earlyCodes59.map earlyDecode := by decide +kernel
private theorem hEC60 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput60.1 earlyInput60.2).map Prod.fst = earlyCodes60.map earlyDecode := by decide +kernel
private theorem hEC61 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput61.1 earlyInput61.2).map Prod.fst = earlyCodes61.map earlyDecode := by decide +kernel
private theorem hEC62 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput62.1 earlyInput62.2).map Prod.fst = earlyCodes62.map earlyDecode := by decide +kernel
private theorem hEC63 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalEarly3) earlyInput63.1 earlyInput63.2).map Prod.fst = earlyCodes63.map earlyDecode := by decide +kernel
private theorem pairFlags_4_5_0 : earlyCompareFlags lowerEarlyTerminalEarly3 earlyInput4.1 earlyInput4.2 earlyInput5.1 earlyInput5.2 false = (List.replicate 25 true) := by
  unfold earlyCompareFlags
  rw [hEC4,hEC5]
  decide +kernel
private theorem pairFlags_6_7_1 : earlyCompareFlags lowerEarlyTerminalEarly3 earlyInput6.1 earlyInput6.2 earlyInput7.1 earlyInput7.2 true = (List.replicate 16 true) := by
  unfold earlyCompareFlags
  rw [hEC6,hEC7]
  decide +kernel
private theorem pairFlags_8_9_1 : earlyCompareFlags lowerEarlyTerminalEarly3 earlyInput8.1 earlyInput8.2 earlyInput9.1 earlyInput9.2 true = (List.replicate 16 false) := by
  unfold earlyCompareFlags
  rw [hEC8,hEC9]
  decide +kernel
private theorem pairFlags_10_11_1 : earlyCompareFlags lowerEarlyTerminalEarly3 earlyInput10.1 earlyInput10.2 earlyInput11.1 earlyInput11.2 true = (List.replicate 16 false) := by
  unfold earlyCompareFlags
  rw [hEC10,hEC11]
  decide +kernel
private theorem pairFlags_12_13_1 : earlyCompareFlags lowerEarlyTerminalEarly3 earlyInput12.1 earlyInput12.2 earlyInput13.1 earlyInput13.2 true = (List.replicate 16 true) := by
  unfold earlyCompareFlags
  rw [hEC12,hEC13]
  decide +kernel
private theorem pairFlags_14_15_0 : earlyCompareFlags lowerEarlyTerminalEarly3 earlyInput14.1 earlyInput14.2 earlyInput15.1 earlyInput15.2 false = (List.replicate 16 true) := by
  unfold earlyCompareFlags
  rw [hEC14,hEC15]
  decide +kernel
private theorem pairFlags_16_17_1 : earlyCompareFlags lowerEarlyTerminalEarly3 earlyInput16.1 earlyInput16.2 earlyInput17.1 earlyInput17.2 true = (List.replicate 25 true) := by
  unfold earlyCompareFlags
  rw [hEC16,hEC17]
  decide +kernel
private theorem pairFlags_18_19_1 : earlyCompareFlags lowerEarlyTerminalEarly3 earlyInput18.1 earlyInput18.2 earlyInput19.1 earlyInput19.2 true = (List.replicate 25 false) := by
  unfold earlyCompareFlags
  rw [hEC18,hEC19]
  decide +kernel
private theorem pairFlags_20_21_1 : earlyCompareFlags lowerEarlyTerminalEarly3 earlyInput20.1 earlyInput20.2 earlyInput21.1 earlyInput21.2 true = (List.replicate 25 true) := by
  unfold earlyCompareFlags
  rw [hEC20,hEC21]
  decide +kernel
private theorem pairFlags_22_23_1 : earlyCompareFlags lowerEarlyTerminalEarly3 earlyInput22.1 earlyInput22.2 earlyInput23.1 earlyInput23.2 true = (List.replicate 25 false) := by
  unfold earlyCompareFlags
  rw [hEC22,hEC23]
  decide +kernel
private theorem pairFlags_24_5_0 : earlyCompareFlags lowerEarlyTerminalEarly3 earlyInput24.1 earlyInput24.2 earlyInput5.1 earlyInput5.2 false = (List.replicate 20 false) := by
  unfold earlyCompareFlags
  rw [hEC24,hEC5]
  decide +kernel
private theorem pairFlags_4_25_0 : earlyCompareFlags lowerEarlyTerminalEarly3 earlyInput4.1 earlyInput4.2 earlyInput25.1 earlyInput25.2 false = (List.replicate 5 false) := by
  unfold earlyCompareFlags
  rw [hEC4,hEC25]
  decide +kernel
private theorem pairFlags_4_15_0 : earlyCompareFlags lowerEarlyTerminalEarly3 earlyInput4.1 earlyInput4.2 earlyInput15.1 earlyInput15.2 false = (List.replicate 20 false) := by
  unfold earlyCompareFlags
  rw [hEC4,hEC15]
  decide +kernel
private theorem pairFlags_14_5_0 : earlyCompareFlags lowerEarlyTerminalEarly3 earlyInput14.1 earlyInput14.2 earlyInput5.1 earlyInput5.2 false = (List.replicate 20 true) := by
  unfold earlyCompareFlags
  rw [hEC14,hEC5]
  decide +kernel
private theorem pairFlags_14_2_0 : earlyCompareFlags lowerEarlyTerminalEarly3 earlyInput14.1 earlyInput14.2 earlyInput2.1 earlyInput2.2 false = (List.replicate 16 false) := by
  unfold earlyCompareFlags
  rw [hEC14,hEC2]
  decide +kernel
private theorem pairFlags_26_15_0 : earlyCompareFlags lowerEarlyTerminalEarly3 earlyInput26.1 earlyInput26.2 earlyInput15.1 earlyInput15.2 false = (List.replicate 16 true) := by
  unfold earlyCompareFlags
  rw [hEC26,hEC15]
  decide +kernel
private theorem pairFlags_27_28_0 : earlyCompareFlags lowerEarlyTerminalEarly3 earlyInput27.1 earlyInput27.2 earlyInput28.1 earlyInput28.2 false = (List.replicate 16 true) := by
  unfold earlyCompareFlags
  rw [hEC27,hEC28]
  decide +kernel
private theorem pairFlags_3_29_1 : earlyCompareFlags lowerEarlyTerminalEarly3 earlyInput3.1 earlyInput3.2 earlyInput29.1 earlyInput29.2 true = (List.replicate 25 false) := by
  unfold earlyCompareFlags
  rw [hEC3,hEC29]
  decide +kernel
private theorem pairFlags_30_31_1 : earlyCompareFlags lowerEarlyTerminalEarly3 earlyInput30.1 earlyInput30.2 earlyInput31.1 earlyInput31.2 true = (List.replicate 25 true) := by
  unfold earlyCompareFlags
  rw [hEC30,hEC31]
  decide +kernel
private theorem pairFlags_32_33_1 : earlyCompareFlags lowerEarlyTerminalEarly3 earlyInput32.1 earlyInput32.2 earlyInput33.1 earlyInput33.2 true = (List.replicate 25 false) := by
  unfold earlyCompareFlags
  rw [hEC32,hEC33]
  decide +kernel
private theorem pairFlags_34_35_1 : earlyCompareFlags lowerEarlyTerminalEarly3 earlyInput34.1 earlyInput34.2 earlyInput35.1 earlyInput35.2 true = (List.replicate 25 true) := by
  unfold earlyCompareFlags
  rw [hEC34,hEC35]
  decide +kernel
private theorem pairFlags_36_37_0 : earlyCompareFlags lowerEarlyTerminalEarly3 earlyInput36.1 earlyInput36.2 earlyInput37.1 earlyInput37.2 false = (List.replicate 25 true) := by
  unfold earlyCompareFlags
  rw [hEC36,hEC37]
  decide +kernel
private theorem pairFlags_38_39_1 : earlyCompareFlags lowerEarlyTerminalEarly3 earlyInput38.1 earlyInput38.2 earlyInput39.1 earlyInput39.2 true = (List.replicate 16 false) := by
  unfold earlyCompareFlags
  rw [hEC38,hEC39]
  decide +kernel
private theorem pairFlags_40_41_1 : earlyCompareFlags lowerEarlyTerminalEarly3 earlyInput40.1 earlyInput40.2 earlyInput41.1 earlyInput41.2 true = (List.replicate 16 true) := by
  unfold earlyCompareFlags
  rw [hEC40,hEC41]
  decide +kernel
private theorem pairFlags_42_43_1 : earlyCompareFlags lowerEarlyTerminalEarly3 earlyInput42.1 earlyInput42.2 earlyInput43.1 earlyInput43.2 true = (List.replicate 16 true) := by
  unfold earlyCompareFlags
  rw [hEC42,hEC43]
  decide +kernel
private theorem pairFlags_44_45_1 : earlyCompareFlags lowerEarlyTerminalEarly3 earlyInput44.1 earlyInput44.2 earlyInput45.1 earlyInput45.2 true = (List.replicate 16 false) := by
  unfold earlyCompareFlags
  rw [hEC44,hEC45]
  decide +kernel
private theorem pairFlags_0_46_0 : earlyCompareFlags lowerEarlyTerminalEarly3 earlyInput0.1 earlyInput0.2 earlyInput46.1 earlyInput46.2 false = (List.replicate 4 true) := by
  unfold earlyCompareFlags
  rw [hEC0,hEC46]
  decide +kernel
private theorem pairFlags_47_48_1 : earlyCompareFlags lowerEarlyTerminalEarly3 earlyInput47.1 earlyInput47.2 earlyInput48.1 earlyInput48.2 true = (List.replicate 10 true) := by
  unfold earlyCompareFlags
  rw [hEC47,hEC48]
  decide +kernel
private theorem pairFlags_49_50_1 : earlyCompareFlags lowerEarlyTerminalEarly3 earlyInput49.1 earlyInput49.2 earlyInput50.1 earlyInput50.2 true = (List.replicate 10 false) := by
  unfold earlyCompareFlags
  rw [hEC49,hEC50]
  decide +kernel
private theorem pairFlags_51_52_1 : earlyCompareFlags lowerEarlyTerminalEarly3 earlyInput51.1 earlyInput51.2 earlyInput52.1 earlyInput52.2 true = (List.replicate 10 true) := by
  unfold earlyCompareFlags
  rw [hEC51,hEC52]
  decide +kernel
private theorem pairFlags_53_54_1 : earlyCompareFlags lowerEarlyTerminalEarly3 earlyInput53.1 earlyInput53.2 earlyInput54.1 earlyInput54.2 true = (List.replicate 25 false) := by
  unfold earlyCompareFlags
  rw [hEC53,hEC54]
  decide +kernel
private theorem pairFlags_55_1_0 : earlyCompareFlags lowerEarlyTerminalEarly3 earlyInput55.1 earlyInput55.2 earlyInput1.1 earlyInput1.2 false = (List.replicate 4 true) := by
  unfold earlyCompareFlags
  rw [hEC55,hEC1]
  decide +kernel
private theorem pairFlags_56_57_1 : earlyCompareFlags lowerEarlyTerminalEarly3 earlyInput56.1 earlyInput56.2 earlyInput57.1 earlyInput57.2 true = (List.replicate 10 true) := by
  unfold earlyCompareFlags
  rw [hEC56,hEC57]
  decide +kernel
private theorem pairFlags_58_59_1 : earlyCompareFlags lowerEarlyTerminalEarly3 earlyInput58.1 earlyInput58.2 earlyInput59.1 earlyInput59.2 true = (List.replicate 10 false) := by
  unfold earlyCompareFlags
  rw [hEC58,hEC59]
  decide +kernel
private theorem pairFlags_60_61_1 : earlyCompareFlags lowerEarlyTerminalEarly3 earlyInput60.1 earlyInput60.2 earlyInput61.1 earlyInput61.2 true = (List.replicate 10 true) := by
  unfold earlyCompareFlags
  rw [hEC60,hEC61]
  decide +kernel
private theorem pairFlags_62_63_1 : earlyCompareFlags lowerEarlyTerminalEarly3 earlyInput62.1 earlyInput62.2 earlyInput63.1 earlyInput63.2 true = (List.replicate 10 false) := by
  unfold earlyCompareFlags
  rw [hEC62,hEC63]
  decide +kernel
private theorem pairFlags_24_28_0 : earlyCompareFlags lowerEarlyTerminalEarly3 earlyInput24.1 earlyInput24.2 earlyInput28.1 earlyInput28.2 false = (List.replicate 16 false) := by
  unfold earlyCompareFlags
  rw [hEC24,hEC28]
  decide +kernel
private theorem pairFlags_27_25_0 : earlyCompareFlags lowerEarlyTerminalEarly3 earlyInput27.1 earlyInput27.2 earlyInput25.1 earlyInput25.2 false = (List.replicate 4 false) := by
  unfold earlyCompareFlags
  rw [hEC27,hEC25]
  decide +kernel
private theorem pairFlags_27_37_0 : earlyCompareFlags lowerEarlyTerminalEarly3 earlyInput27.1 earlyInput27.2 earlyInput37.1 earlyInput37.2 false = (List.replicate 20 false) := by
  unfold earlyCompareFlags
  rw [hEC27,hEC37]
  decide +kernel
private theorem pairFlags_36_28_0 : earlyCompareFlags lowerEarlyTerminalEarly3 earlyInput36.1 earlyInput36.2 earlyInput28.1 earlyInput28.2 false = (List.replicate 20 true) := by
  unfold earlyCompareFlags
  rw [hEC36,hEC28]
  decide +kernel
private theorem pairFlags_36_46_0 : earlyCompareFlags lowerEarlyTerminalEarly3 earlyInput36.1 earlyInput36.2 earlyInput46.1 earlyInput46.2 false = (List.replicate 20 false) := by
  unfold earlyCompareFlags
  rw [hEC36,hEC46]
  decide +kernel
private theorem pairFlags_0_37_0 : earlyCompareFlags lowerEarlyTerminalEarly3 earlyInput0.1 earlyInput0.2 earlyInput37.1 earlyInput37.2 false = (List.replicate 5 true) := by
  unfold earlyCompareFlags
  rw [hEC0,hEC37]
  decide +kernel
private theorem pairFlags_0_1_0 : earlyCompareFlags lowerEarlyTerminalEarly3 earlyInput0.1 earlyInput0.2 earlyInput1.1 earlyInput1.2 false = (List.replicate 4 false) := by
  unfold earlyCompareFlags
  rw [hEC0,hEC1]
  decide +kernel
private theorem pairFlags_55_46_0 : earlyCompareFlags lowerEarlyTerminalEarly3 earlyInput55.1 earlyInput55.2 earlyInput46.1 earlyInput46.2 false = (List.replicate 4 true) := by
  unfold earlyCompareFlags
  rw [hEC55,hEC46]
  decide +kernel
private theorem pairFlags_55_5_0 : earlyCompareFlags lowerEarlyTerminalEarly3 earlyInput55.1 earlyInput55.2 earlyInput5.1 earlyInput5.2 false = (List.replicate 5 false) := by
  unfold earlyCompareFlags
  rw [hEC55,hEC5]
  decide +kernel
private theorem pairFlags_4_1_0 : earlyCompareFlags lowerEarlyTerminalEarly3 earlyInput4.1 earlyInput4.2 earlyInput1.1 earlyInput1.2 false = (List.replicate 20 false) := by
  unfold earlyCompareFlags
  rw [hEC4,hEC1]
  decide +kernel
private def earlyFlags : Array (List Bool) := #[(List.replicate 25 true),(List.replicate 16 true),(List.replicate 16 false),(List.replicate 16 false),(List.replicate 16 true),(List.replicate 16 true),(List.replicate 25 true),(List.replicate 25 false),(List.replicate 25 true),(List.replicate 25 false),(List.replicate 20 false),(List.replicate 5 false),(List.replicate 20 false),(List.replicate 20 true),(List.replicate 16 false),(List.replicate 16 true),(List.replicate 16 true),(List.replicate 25 false),(List.replicate 25 true),(List.replicate 25 false),(List.replicate 25 true),(List.replicate 25 true),(List.replicate 16 false),(List.replicate 16 true),(List.replicate 16 true),(List.replicate 16 false),(List.replicate 4 true),(List.replicate 10 true),(List.replicate 10 false),(List.replicate 10 true),(List.replicate 25 false),(List.replicate 4 true),(List.replicate 10 true),(List.replicate 10 false),(List.replicate 10 true),(List.replicate 10 false),(List.replicate 25 true),(List.replicate 16 true),(List.replicate 16 false),(List.replicate 16 false),(List.replicate 16 true),(List.replicate 16 true),(List.replicate 25 true),(List.replicate 25 false),(List.replicate 25 true),(List.replicate 25 false),(List.replicate 16 false),(List.replicate 4 false),(List.replicate 20 false),(List.replicate 20 true),(List.replicate 20 false),(List.replicate 5 true),(List.replicate 4 false),(List.replicate 4 true),(List.replicate 5 false),(List.replicate 20 false),(List.replicate 20 false),(List.replicate 20 true),(List.replicate 16 false),(List.replicate 16 true)]
private def earlyBuckets : Array (List ℕ) := #[[],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[],[],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19],[0,1,2,3,4],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24],[],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[],[],[0,1,2,3,4,5,6,7,8,9],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24],[],[],[0,1,2,3,4,5,6,7,8,9],[],[0,1,2,3,4,5,6,7,8,9],[],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[],[],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[0,1,2,3],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19],[],[0,1,2,3],[],[0,1,2,3,4],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[]]
private theorem hEF0 : (lowerEarlyTerminalBranches lowerEarlyTerminalEarly3 (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 0).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[0]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 0).kind = .compare earlyInput4.1 earlyInput4.2 earlyInput5.1 earlyInput5.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_4_5_0
private theorem hEF1 : (lowerEarlyTerminalBranches lowerEarlyTerminalEarly3 (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 1).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[1]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 1).kind = .compare earlyInput6.1 earlyInput6.2 earlyInput7.1 earlyInput7.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_6_7_1
private theorem hEF2 : (lowerEarlyTerminalBranches lowerEarlyTerminalEarly3 (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 2).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[2]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 2).kind = .compare earlyInput8.1 earlyInput8.2 earlyInput9.1 earlyInput9.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_8_9_1
private theorem hEF3 : (lowerEarlyTerminalBranches lowerEarlyTerminalEarly3 (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 3).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[3]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 3).kind = .compare earlyInput10.1 earlyInput10.2 earlyInput11.1 earlyInput11.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_10_11_1
private theorem hEF4 : (lowerEarlyTerminalBranches lowerEarlyTerminalEarly3 (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 4).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[4]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 4).kind = .compare earlyInput12.1 earlyInput12.2 earlyInput13.1 earlyInput13.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_12_13_1
private theorem hEF5 : (lowerEarlyTerminalBranches lowerEarlyTerminalEarly3 (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 5).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[5]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 5).kind = .compare earlyInput14.1 earlyInput14.2 earlyInput15.1 earlyInput15.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_14_15_0
private theorem hEF6 : (lowerEarlyTerminalBranches lowerEarlyTerminalEarly3 (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 6).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[6]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 6).kind = .compare earlyInput16.1 earlyInput16.2 earlyInput17.1 earlyInput17.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_16_17_1
private theorem hEF7 : (lowerEarlyTerminalBranches lowerEarlyTerminalEarly3 (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 7).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[7]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 7).kind = .compare earlyInput18.1 earlyInput18.2 earlyInput19.1 earlyInput19.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_18_19_1
private theorem hEF8 : (lowerEarlyTerminalBranches lowerEarlyTerminalEarly3 (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 8).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[8]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 8).kind = .compare earlyInput20.1 earlyInput20.2 earlyInput21.1 earlyInput21.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_20_21_1
private theorem hEF9 : (lowerEarlyTerminalBranches lowerEarlyTerminalEarly3 (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 9).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[9]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 9).kind = .compare earlyInput22.1 earlyInput22.2 earlyInput23.1 earlyInput23.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_22_23_1
private theorem hEF10 : (lowerEarlyTerminalBranches lowerEarlyTerminalEarly3 (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 10).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[10]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 10).kind = .compare earlyInput24.1 earlyInput24.2 earlyInput5.1 earlyInput5.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_24_5_0
private theorem hEF11 : (lowerEarlyTerminalBranches lowerEarlyTerminalEarly3 (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 11).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[11]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 11).kind = .compare earlyInput4.1 earlyInput4.2 earlyInput25.1 earlyInput25.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_4_25_0
private theorem hEF12 : (lowerEarlyTerminalBranches lowerEarlyTerminalEarly3 (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 12).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[12]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 12).kind = .compare earlyInput4.1 earlyInput4.2 earlyInput15.1 earlyInput15.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_4_15_0
private theorem hEF13 : (lowerEarlyTerminalBranches lowerEarlyTerminalEarly3 (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 13).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[13]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 13).kind = .compare earlyInput14.1 earlyInput14.2 earlyInput5.1 earlyInput5.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_14_5_0
private theorem hEF14 : (lowerEarlyTerminalBranches lowerEarlyTerminalEarly3 (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 14).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[14]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 14).kind = .compare earlyInput14.1 earlyInput14.2 earlyInput2.1 earlyInput2.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_14_2_0
private theorem hEF15 : (lowerEarlyTerminalBranches lowerEarlyTerminalEarly3 (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 15).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[15]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 15).kind = .compare earlyInput26.1 earlyInput26.2 earlyInput15.1 earlyInput15.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_26_15_0
private theorem hEF16 : (lowerEarlyTerminalBranches lowerEarlyTerminalEarly3 (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 16).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[16]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 16).kind = .compare earlyInput27.1 earlyInput27.2 earlyInput28.1 earlyInput28.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_27_28_0
private theorem hEF17 : (lowerEarlyTerminalBranches lowerEarlyTerminalEarly3 (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 17).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[17]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 17).kind = .compare earlyInput3.1 earlyInput3.2 earlyInput29.1 earlyInput29.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_3_29_1
private theorem hEF18 : (lowerEarlyTerminalBranches lowerEarlyTerminalEarly3 (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 18).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[18]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 18).kind = .compare earlyInput30.1 earlyInput30.2 earlyInput31.1 earlyInput31.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_30_31_1
private theorem hEF19 : (lowerEarlyTerminalBranches lowerEarlyTerminalEarly3 (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 19).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[19]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 19).kind = .compare earlyInput32.1 earlyInput32.2 earlyInput33.1 earlyInput33.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_32_33_1
private theorem hEF20 : (lowerEarlyTerminalBranches lowerEarlyTerminalEarly3 (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 20).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[20]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 20).kind = .compare earlyInput34.1 earlyInput34.2 earlyInput35.1 earlyInput35.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_34_35_1
private theorem hEF21 : (lowerEarlyTerminalBranches lowerEarlyTerminalEarly3 (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 21).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[21]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 21).kind = .compare earlyInput36.1 earlyInput36.2 earlyInput37.1 earlyInput37.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_36_37_0
private theorem hEF22 : (lowerEarlyTerminalBranches lowerEarlyTerminalEarly3 (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 22).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[22]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 22).kind = .compare earlyInput38.1 earlyInput38.2 earlyInput39.1 earlyInput39.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_38_39_1
private theorem hEF23 : (lowerEarlyTerminalBranches lowerEarlyTerminalEarly3 (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 23).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[23]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 23).kind = .compare earlyInput40.1 earlyInput40.2 earlyInput41.1 earlyInput41.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_40_41_1
private theorem hEF24 : (lowerEarlyTerminalBranches lowerEarlyTerminalEarly3 (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 24).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[24]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 24).kind = .compare earlyInput42.1 earlyInput42.2 earlyInput43.1 earlyInput43.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_42_43_1
private theorem hEF25 : (lowerEarlyTerminalBranches lowerEarlyTerminalEarly3 (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 25).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[25]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 25).kind = .compare earlyInput44.1 earlyInput44.2 earlyInput45.1 earlyInput45.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_44_45_1
private theorem hEF26 : (lowerEarlyTerminalBranches lowerEarlyTerminalEarly3 (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 26).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[26]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 26).kind = .compare earlyInput0.1 earlyInput0.2 earlyInput46.1 earlyInput46.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_0_46_0
private theorem hEF27 : (lowerEarlyTerminalBranches lowerEarlyTerminalEarly3 (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 27).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[27]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 27).kind = .compare earlyInput47.1 earlyInput47.2 earlyInput48.1 earlyInput48.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_47_48_1
private theorem hEF28 : (lowerEarlyTerminalBranches lowerEarlyTerminalEarly3 (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 28).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[28]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 28).kind = .compare earlyInput49.1 earlyInput49.2 earlyInput50.1 earlyInput50.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_49_50_1
private theorem hEF29 : (lowerEarlyTerminalBranches lowerEarlyTerminalEarly3 (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 29).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[29]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 29).kind = .compare earlyInput51.1 earlyInput51.2 earlyInput52.1 earlyInput52.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_51_52_1
private theorem hEF30 : (lowerEarlyTerminalBranches lowerEarlyTerminalEarly3 (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 30).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[30]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 30).kind = .compare earlyInput53.1 earlyInput53.2 earlyInput54.1 earlyInput54.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_53_54_1
private theorem hEF31 : (lowerEarlyTerminalBranches lowerEarlyTerminalEarly3 (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 31).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[31]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 31).kind = .compare earlyInput55.1 earlyInput55.2 earlyInput1.1 earlyInput1.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_55_1_0
private theorem hEF32 : (lowerEarlyTerminalBranches lowerEarlyTerminalEarly3 (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 32).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[32]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 32).kind = .compare earlyInput56.1 earlyInput56.2 earlyInput57.1 earlyInput57.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_56_57_1
private theorem hEF33 : (lowerEarlyTerminalBranches lowerEarlyTerminalEarly3 (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 33).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[33]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 33).kind = .compare earlyInput58.1 earlyInput58.2 earlyInput59.1 earlyInput59.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_58_59_1
private theorem hEF34 : (lowerEarlyTerminalBranches lowerEarlyTerminalEarly3 (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 34).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[34]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 34).kind = .compare earlyInput60.1 earlyInput60.2 earlyInput61.1 earlyInput61.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_60_61_1
private theorem hEF35 : (lowerEarlyTerminalBranches lowerEarlyTerminalEarly3 (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 35).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[35]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 35).kind = .compare earlyInput62.1 earlyInput62.2 earlyInput63.1 earlyInput63.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_62_63_1
private theorem hEF36 : (lowerEarlyTerminalBranches lowerEarlyTerminalEarly3 (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 36).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[36]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 36).kind = .compare earlyInput4.1 earlyInput4.2 earlyInput5.1 earlyInput5.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_4_5_0
private theorem hEF37 : (lowerEarlyTerminalBranches lowerEarlyTerminalEarly3 (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 37).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[37]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 37).kind = .compare earlyInput6.1 earlyInput6.2 earlyInput7.1 earlyInput7.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_6_7_1
private theorem hEF38 : (lowerEarlyTerminalBranches lowerEarlyTerminalEarly3 (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 38).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[38]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 38).kind = .compare earlyInput8.1 earlyInput8.2 earlyInput9.1 earlyInput9.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_8_9_1
private theorem hEF39 : (lowerEarlyTerminalBranches lowerEarlyTerminalEarly3 (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 39).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[39]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 39).kind = .compare earlyInput10.1 earlyInput10.2 earlyInput11.1 earlyInput11.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_10_11_1
private theorem hEF40 : (lowerEarlyTerminalBranches lowerEarlyTerminalEarly3 (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 40).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[40]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 40).kind = .compare earlyInput12.1 earlyInput12.2 earlyInput13.1 earlyInput13.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_12_13_1
private theorem hEF41 : (lowerEarlyTerminalBranches lowerEarlyTerminalEarly3 (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 41).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[41]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 41).kind = .compare earlyInput14.1 earlyInput14.2 earlyInput15.1 earlyInput15.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_14_15_0
private theorem hEF42 : (lowerEarlyTerminalBranches lowerEarlyTerminalEarly3 (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 42).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[42]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 42).kind = .compare earlyInput16.1 earlyInput16.2 earlyInput17.1 earlyInput17.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_16_17_1
private theorem hEF43 : (lowerEarlyTerminalBranches lowerEarlyTerminalEarly3 (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 43).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[43]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 43).kind = .compare earlyInput18.1 earlyInput18.2 earlyInput19.1 earlyInput19.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_18_19_1
private theorem hEF44 : (lowerEarlyTerminalBranches lowerEarlyTerminalEarly3 (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 44).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[44]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 44).kind = .compare earlyInput20.1 earlyInput20.2 earlyInput21.1 earlyInput21.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_20_21_1
private theorem hEF45 : (lowerEarlyTerminalBranches lowerEarlyTerminalEarly3 (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 45).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[45]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 45).kind = .compare earlyInput22.1 earlyInput22.2 earlyInput23.1 earlyInput23.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_22_23_1
private theorem hEF46 : (lowerEarlyTerminalBranches lowerEarlyTerminalEarly3 (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 46).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[46]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 46).kind = .compare earlyInput24.1 earlyInput24.2 earlyInput28.1 earlyInput28.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_24_28_0
private theorem hEF47 : (lowerEarlyTerminalBranches lowerEarlyTerminalEarly3 (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 47).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[47]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 47).kind = .compare earlyInput27.1 earlyInput27.2 earlyInput25.1 earlyInput25.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_27_25_0
private theorem hEF48 : (lowerEarlyTerminalBranches lowerEarlyTerminalEarly3 (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 48).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[48]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 48).kind = .compare earlyInput27.1 earlyInput27.2 earlyInput37.1 earlyInput37.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_27_37_0
private theorem hEF49 : (lowerEarlyTerminalBranches lowerEarlyTerminalEarly3 (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 49).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[49]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 49).kind = .compare earlyInput36.1 earlyInput36.2 earlyInput28.1 earlyInput28.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_36_28_0
private theorem hEF50 : (lowerEarlyTerminalBranches lowerEarlyTerminalEarly3 (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 50).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[50]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 50).kind = .compare earlyInput36.1 earlyInput36.2 earlyInput46.1 earlyInput46.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_36_46_0
private theorem hEF51 : (lowerEarlyTerminalBranches lowerEarlyTerminalEarly3 (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 51).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[51]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 51).kind = .compare earlyInput0.1 earlyInput0.2 earlyInput37.1 earlyInput37.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_0_37_0
private theorem hEF52 : (lowerEarlyTerminalBranches lowerEarlyTerminalEarly3 (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 52).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[52]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 52).kind = .compare earlyInput0.1 earlyInput0.2 earlyInput1.1 earlyInput1.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_0_1_0
private theorem hEF53 : (lowerEarlyTerminalBranches lowerEarlyTerminalEarly3 (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 53).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[53]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 53).kind = .compare earlyInput55.1 earlyInput55.2 earlyInput46.1 earlyInput46.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_55_46_0
private theorem hEF54 : (lowerEarlyTerminalBranches lowerEarlyTerminalEarly3 (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 54).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[54]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 54).kind = .compare earlyInput55.1 earlyInput55.2 earlyInput5.1 earlyInput5.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_55_5_0
private theorem hEF55 : (lowerEarlyTerminalBranches lowerEarlyTerminalEarly3 (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 55).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[55]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 55).kind = .compare earlyInput4.1 earlyInput4.2 earlyInput1.1 earlyInput1.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_4_1_0
private theorem hEF56 : (lowerEarlyTerminalBranches lowerEarlyTerminalEarly3 (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 56).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[56]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 56).kind = .compare earlyInput4.1 earlyInput4.2 earlyInput15.1 earlyInput15.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_4_15_0
private theorem hEF57 : (lowerEarlyTerminalBranches lowerEarlyTerminalEarly3 (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 57).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[57]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 57).kind = .compare earlyInput14.1 earlyInput14.2 earlyInput5.1 earlyInput5.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_14_5_0
private theorem hEF58 : (lowerEarlyTerminalBranches lowerEarlyTerminalEarly3 (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 58).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[58]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 58).kind = .compare earlyInput14.1 earlyInput14.2 earlyInput2.1 earlyInput2.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_14_2_0
private theorem hEF59 : (lowerEarlyTerminalBranches lowerEarlyTerminalEarly3 (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 59).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[59]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 59).kind = .compare earlyInput26.1 earlyInput26.2 earlyInput15.1 earlyInput15.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_26_15_0
private theorem earlyLength : lowerEarlyTerminalEarly3.goals.length = 60 := by decide +kernel
private theorem hEFlags (g : ℕ) (hg : g<60) : (lowerEarlyTerminalBranches lowerEarlyTerminalEarly3 (lowerEarlyTerminalGoal lowerEarlyTerminalEarly3 g).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[g]?.getD [] := by
  interval_cases g
  · exact hEF0
  · exact hEF1
  · exact hEF2
  · exact hEF3
  · exact hEF4
  · exact hEF5
  · exact hEF6
  · exact hEF7
  · exact hEF8
  · exact hEF9
  · exact hEF10
  · exact hEF11
  · exact hEF12
  · exact hEF13
  · exact hEF14
  · exact hEF15
  · exact hEF16
  · exact hEF17
  · exact hEF18
  · exact hEF19
  · exact hEF20
  · exact hEF21
  · exact hEF22
  · exact hEF23
  · exact hEF24
  · exact hEF25
  · exact hEF26
  · exact hEF27
  · exact hEF28
  · exact hEF29
  · exact hEF30
  · exact hEF31
  · exact hEF32
  · exact hEF33
  · exact hEF34
  · exact hEF35
  · exact hEF36
  · exact hEF37
  · exact hEF38
  · exact hEF39
  · exact hEF40
  · exact hEF41
  · exact hEF42
  · exact hEF43
  · exact hEF44
  · exact hEF45
  · exact hEF46
  · exact hEF47
  · exact hEF48
  · exact hEF49
  · exact hEF50
  · exact hEF51
  · exact hEF52
  · exact hEF53
  · exact hEF54
  · exact hEF55
  · exact hEF56
  · exact hEF57
  · exact hEF58
  · exact hEF59
private theorem hEBuckets : ∀ g ∈ List.range 60, (earlyRecordKeys lowerEarlyTerminalEarly3).filterMap (fun r => if r.1=g then some r.2 else none) = earlyBuckets[g]?.getD [] := by decide +kernel
private theorem hECovered : ∀ g ∈ List.range 60, ∀ bj ∈ (earlyFlags[g]?.getD []).zipIdx, bj.1=true ∨ bj.2 ∈ earlyBuckets[g]?.getD [] := by decide +kernel

theorem solution : lowerEarlyTerminalCoverage lowerEarlyTerminalEarly3 :=
  earlyCoverageTables_sound _ 60 earlyFlags earlyBuckets earlyLength hEFlags (fun g hg => hEBuckets g (List.mem_range.mpr hg)) hECovered
#print axioms solution
