-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_terminal3_coverage
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:05:26.203417+00:00
-- url     : https://prove2.me/submissions/cfcbb1ba-b396-48fe-add6-7eb1a0d35b1f

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
private def earlyBucketKeys (N : ℕ) (buckets : Array (List ℕ)) : List (ℕ × ℕ) :=
  (List.range N).flatMap fun g => (buckets[g]?.getD []).map fun j => (g,j)
private theorem earlyCoverageGrouped_sound (C : LowerEarlyTerminalCatalog) (N : ℕ)
    (flags : Array (List Bool)) (buckets : Array (List ℕ))
    (hlen : C.goals.length=N)
    (hf : ∀ g, g<N → (lowerEarlyTerminalBranches C (lowerEarlyTerminalGoal C g).kind).map
      (fun z => decide (z.2=LowerHistoryComparison.automatic)) = flags[g]?.getD [])
    (hb : earlyRecordKeys C = earlyBucketKeys N buckets)
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
    have hk : (g,j) ∈ earlyRecordKeys C := by
      rw [hb]
      exact List.mem_flatMap.mpr ⟨g,List.mem_range.mpr hgN,List.mem_map.mpr ⟨j,hr,rfl⟩⟩
    obtain ⟨r,hr,hpair⟩ := List.mem_map.mp hk
    exact ⟨r,hr,congrArg Prod.fst hpair,congrArg Prod.snd hpair⟩
private def earlyFields : Array CertField := #[⟨(553/1429),(1/1429),(0/1),(0/1)⟩,⟨(3289/10753),(1/10753),(0/1),(0/1)⟩,⟨(278/709),(-1/709),(0/1),(0/1)⟩,⟨(71/229),(-1/229),(0/1),(0/1)⟩,⟨(1413/4654),(-1/4654),(0/1),(0/1)⟩,⟨(1929/4946),(-1/14838),(0/1),(0/1)⟩,⟨(15/37),(-1/37),(0/1),(0/1)⟩,⟨(66/179),(-1/537),(0/1),(0/1)⟩,⟨(247/649),(1/649),(0/1),(0/1)⟩,⟨(16/59),(1/177),(0/1),(0/1)⟩,⟨(767/2749),(1/2749),(0/1),(0/1)⟩,⟨(3734/9757),(1/9757),(0/1),(0/1)⟩,⟨(93/262),(1/262),(0/1),(0/1)⟩,⟨(83/313),(1/313),(0/1),(0/1)⟩,⟨(1590/5893),(1/5893),(0/1),(0/1)⟩,⟨(1991/5521),(1/5521),(0/1),(0/1)⟩,⟨(4519/12598),(-1/12598),(0/1),(0/1)⟩,⟨(271/1006),(-1/1006),(0/1),(0/1)⟩,⟨(133/478),(-1/478),(0/1),(0/1)⟩,⟨(61/169),(1/169),(0/1),(0/1)⟩,⟨(1161/3142),(1/3142),(0/1),(0/1)⟩,⟨(1950/7081),(-1/7081),(0/1),(0/1)⟩,⟨(2747/7501),(-1/7501),(0/1),(0/1)⟩,⟨(42/143),(1/429),(0/1),(0/1)⟩,⟨(1809/6094),(1/6094),(0/1),(0/1)⟩,⟨(43/142),(-1/142),(0/1),(0/1)⟩,⟨(731/2497),(-1/2497),(0/1),(0/1)⟩,⟨(32/83),(-1/249),(0/1),(0/1)⟩,⟨(1413/3718),(-1/3718),(0/1),(0/1)⟩,⟨(2589/6674),(1/20022),(0/1),(0/1)⟩,⟨(177/454),(-1/454),(0/1),(0/1)⟩,⟨(3230/8353),(-1/8353),(0/1),(0/1)⟩,⟨(13260/33937),(1/33937),(0/1),(0/1)⟩,⟨(5/22),(1/22),(0/1),(0/1)⟩,⟨(4/13),(1/13),(0/1),(0/1)⟩,⟨(89/214),(1/214),(0/1),(0/1)⟩,⟨(1251/4667),(-1/14001),(0/1),(0/1)⟩,⟨(483/1318),(1/1318),(0/1),(0/1)⟩,⟨(7480/20353),(1/20353),(0/1),(0/1)⟩,⟨(797/2221),(1/2221),(0/1),(0/1)⟩,⟨(12510/34801),(1/34801),(0/1),(0/1)⟩,⟨(667/1846),(-1/1846),(0/1),(0/1)⟩,⟨(11574/32101),(-1/32101),(0/1),(0/1)⟩,⟨(9467/26234),(1/78702),(0/1),(0/1)⟩,⟨(660/2461),(1/2461),(0/1),(0/1)⟩,⟨(10229/38062),(1/38062),(0/1),(0/1)⟩,⟨(175/647),(-1/1941),(0/1),(0/1)⟩,⟨(22567/83569),(1/83569),(0/1),(0/1)⟩,⟨(341/1237),(1/1237),(0/1),(0/1)⟩,⟨(1721/6218),(1/18654),(0/1),(0/1)⟩,⟨(246/877),(-1/877),(0/1),(0/1)⟩,⟨(10780/38569),(1/38569),(0/1),(0/1)⟩,⟨(383/1033),(-1/1033),(0/1),(0/1)⟩,⟨(6760/18301),(-1/18301),(0/1),(0/1)⟩,⟨(5491/14843),(1/44529),(0/1),(0/1)⟩,⟨(1493/5354),(-1/16062),(0/1),(0/1)⟩,⟨(237/814),(1/814),(0/1),(0/1)⟩,⟨(4264/14557),(1/14557),(0/1),(0/1)⟩,⟨(317/1069),(-1/1069),(0/1),(0/1)⟩,⟨(469/1549),(1/1549),(0/1),(0/1)⟩,⟨(8222/27073),(1/27073),(0/1),(0/1)⟩,⟨(579/1894),(-1/1894),(0/1),(0/1)⟩,⟨(4840/16393),(-1/16393),(0/1),(0/1)⟩,⟨(3437/11762),(-1/35286),(0/1),(0/1)⟩,⟨(446/1177),(1/1177),(0/1),(0/1)⟩,⟨(2755/7247),(1/21741),(0/1),(0/1)⟩,⟨(651/1702),(-1/1702),(0/1),(0/1)⟩,⟨(3247/8507),(-1/25521),(0/1),(0/1)⟩,⟨(19756/52033),(-1/52033),(0/1),(0/1)⟩,⟨(353/914),(1/2742),(0/1),(0/1)⟩,⟨(18819/48661),(1/48661),(0/1),(0/1)⟩,⟨(1364/3517),(-1/3517),(0/1),(0/1)⟩,⟨(21015/54241),(-1/54241),(0/1),(0/1)⟩,⟨(45733/118318),(-1/118318),(0/1),(0/1)⟩,⟨(9014/29557),(-1/29557),(0/1),(0/1)⟩,⟨(6697/22079),(-1/66237),(0/1),(0/1)⟩,⟨(1932/4957),(1/4957),(0/1),(0/1)⟩,⟨(33653/86281),(1/86281),(0/1),(0/1)⟩,⟨(779/1994),(-1/5982),(0/1),(0/1)⟩,⟨(36569/93661),(-1/93661),(0/1),(0/1)⟩,⟨(82450/211453),(-1/211453),(0/1),(0/1)⟩,⟨(9257/34318),(-1/34318),(0/1),(0/1)⟩,⟨(856/2341),(1/2341),(0/1),(0/1)⟩,⟨(5363/14642),(1/43926),(0/1),(0/1)⟩,⟨(1301/3541),(-1/3541),(0/1),(0/1)⟩,⟨(6431/17522),(-1/52566),(0/1),(0/1)⟩,⟨(38250/104497),(-1/104497),(0/1),(0/1)⟩]
private abbrev earlyInput0 : LowerPair × Bool := (([2, 1, 1, 2], [3, 3]), true)
private def earlyCodes0 : List (ℕ × ℕ) := [(0, 1)]
private abbrev earlyInput1 : LowerPair × Bool := (([2, 1, 1, 3], [3, 3]), false)
private def earlyCodes1 : List (ℕ × ℕ) := [(2, 3), (2, 4), (2, 3), (5, 3)]
private abbrev earlyInput2 : LowerPair × Bool := (([2], [2]), false)
private def earlyCodes2 : List (ℕ × ℕ) := [(6, 6), (6, 7), (6, 6), (7, 6)]
private abbrev earlyInput3 : LowerPair × Bool := (([2, 1, 1, 1], [3, 1, 1]), true)
private def earlyCodes3 : List (ℕ × ℕ) := [(8, 9), (8, 10), (8, 9), (11, 9), (8, 9)]
private abbrev earlyInput4 : LowerPair × Bool := (([2, 1, 3], [3, 1, 2]), true)
private def earlyCodes4 : List (ℕ × ℕ) := [(12, 13), (12, 14), (12, 13), (15, 13)]
private abbrev earlyInput5 : LowerPair × Bool := (([2, 1, 3], [3, 1, 2]), false)
private def earlyCodes5 : List (ℕ × ℕ) := [(16, 17)]
private abbrev earlyInput6 : LowerPair × Bool := (([2, 1, 3], [3, 1, 1]), true)
private def earlyCodes6 : List (ℕ × ℕ) := [(12, 9), (12, 10), (12, 9), (15, 9)]
private abbrev earlyInput7 : LowerPair × Bool := (([2, 1, 3], [3, 1, 1]), false)
private def earlyCodes7 : List (ℕ × ℕ) := [(16, 18)]
private abbrev earlyInput8 : LowerPair × Bool := (([2, 1, 2], [3, 1, 1]), true)
private def earlyCodes8 : List (ℕ × ℕ) := [(19, 9), (19, 10), (19, 9), (20, 9)]
private abbrev earlyInput9 : LowerPair × Bool := (([2, 1, 2], [3, 1, 1]), false)
private def earlyCodes9 : List (ℕ × ℕ) := [(7, 18), (7, 21), (7, 18), (22, 18)]
private abbrev earlyInput10 : LowerPair × Bool := (([2, 1, 3], [3, 2]), true)
private def earlyCodes10 : List (ℕ × ℕ) := [(12, 23), (12, 23), (12, 24), (12, 23), (15, 23)]
private abbrev earlyInput11 : LowerPair × Bool := (([2, 1, 3], [3, 2]), false)
private def earlyCodes11 : List (ℕ × ℕ) := [(16, 25), (16, 25)]
private abbrev earlyInput12 : LowerPair × Bool := (([2, 1, 3], [3, 3]), true)
private def earlyCodes12 : List (ℕ × ℕ) := [(12, 1), (12, 1)]
private abbrev earlyInput13 : LowerPair × Bool := (([2, 1, 3], [3, 3]), false)
private def earlyCodes13 : List (ℕ × ℕ) := [(16, 3), (16, 3)]
private abbrev earlyInput14 : LowerPair × Bool := (([2, 1, 2], [3, 2]), true)
private def earlyCodes14 : List (ℕ × ℕ) := [(19, 23), (19, 23), (19, 24), (19, 23), (20, 23)]
private abbrev earlyInput15 : LowerPair × Bool := (([2, 1, 2], [3, 2]), false)
private def earlyCodes15 : List (ℕ × ℕ) := [(7, 25), (7, 26), (7, 25), (22, 25), (7, 25)]
private abbrev earlyInput16 : LowerPair × Bool := (([2, 1, 1, 1], [3, 1, 1]), false)
private def earlyCodes16 : List (ℕ × ℕ) := [(27, 18), (27, 18), (27, 21), (27, 18), (28, 18)]
private abbrev earlyInput17 : LowerPair × Bool := (([2, 1, 1, 2], [3, 1, 1]), true)
private def earlyCodes17 : List (ℕ × ℕ) := [(0, 9), (0, 10), (0, 9), (29, 9), (0, 9)]
private abbrev earlyInput18 : LowerPair × Bool := (([2, 1, 1, 2], [3, 1, 1]), false)
private def earlyCodes18 : List (ℕ × ℕ) := [(30, 18), (30, 18), (30, 21), (30, 18), (31, 18)]
private abbrev earlyInput19 : LowerPair × Bool := (([2, 1, 1, 1], [3, 2]), true)
private def earlyCodes19 : List (ℕ × ℕ) := [(8, 23), (8, 24), (8, 23), (11, 23)]
private abbrev earlyInput20 : LowerPair × Bool := (([2, 1, 1, 1], [3, 2]), false)
private def earlyCodes20 : List (ℕ × ℕ) := [(27, 25), (27, 26), (27, 25), (28, 25)]
private abbrev earlyInput21 : LowerPair × Bool := (([2, 1, 1, 1], [3, 3]), true)
private def earlyCodes21 : List (ℕ × ℕ) := [(8, 1)]
private abbrev earlyInput22 : LowerPair × Bool := (([2, 1, 1, 1], [3, 3]), false)
private def earlyCodes22 : List (ℕ × ℕ) := [(27, 3), (27, 4), (27, 3), (28, 3)]
private abbrev earlyInput23 : LowerPair × Bool := (([2, 1, 1, 2], [3, 2]), true)
private def earlyCodes23 : List (ℕ × ℕ) := [(0, 23), (0, 24), (0, 23), (29, 23)]
private abbrev earlyInput24 : LowerPair × Bool := (([2, 1, 1, 2], [3, 2]), false)
private def earlyCodes24 : List (ℕ × ℕ) := [(30, 25), (30, 26), (30, 25), (31, 25)]
private abbrev earlyInput25 : LowerPair × Bool := (([2, 1, 1, 3], [3, 2]), true)
private def earlyCodes25 : List (ℕ × ℕ) := [(32, 23)]
private abbrev earlyInput26 : LowerPair × Bool := (([2, 1, 1, 3], [3, 2]), false)
private def earlyCodes26 : List (ℕ × ℕ) := [(2, 25), (2, 26), (2, 25), (5, 25)]
private abbrev earlyInput27 : LowerPair × Bool := (([2, 1, 1, 2], [3, 3]), false)
private def earlyCodes27 : List (ℕ × ℕ) := [(30, 3), (30, 4), (30, 3), (31, 3)]
private abbrev earlyInput28 : LowerPair × Bool := (([3], [2]), true)
private def earlyCodes28 : List (ℕ × ℕ) := [(33, 34), (33, 35), (33, 34), (23, 34)]
private abbrev earlyInput29 : LowerPair × Bool := (([3], [2]), false)
private def earlyCodes29 : List (ℕ × ℕ) := [(17, 6)]
private abbrev earlyInput30 : LowerPair × Bool := (([2, 1, 2, 1], [3, 1, 2]), false)
private def earlyCodes30 : List (ℕ × ℕ) := [(7, 17), (7, 17), (7, 36), (7, 17), (22, 17)]
private abbrev earlyInput31 : LowerPair × Bool := (([2, 1, 2, 1], [3, 1, 2]), true)
private def earlyCodes31 : List (ℕ × ℕ) := [(37, 13), (37, 14), (37, 13), (38, 13), (37, 13)]
private abbrev earlyInput32 : LowerPair × Bool := (([2, 1, 2], [3, 1, 2]), false)
private def earlyCodes32 : List (ℕ × ℕ) := [(7, 17), (7, 36), (7, 17), (22, 17)]
private abbrev earlyInput33 : LowerPair × Bool := (([2, 1, 2], [3, 1, 2]), true)
private def earlyCodes33 : List (ℕ × ℕ) := [(19, 13), (19, 14), (19, 13), (20, 13)]
private abbrev earlyInput34 : LowerPair × Bool := (([2, 1, 1, 3], [3, 3]), true)
private def earlyCodes34 : List (ℕ × ℕ) := [(32, 1)]
private abbrev earlyInput35 : LowerPair × Bool := (([2], [2]), true)
private def earlyCodes35 : List (ℕ × ℕ) := [(34, 34), (34, 35), (34, 34), (35, 34)]
private abbrev earlyInput36 : LowerPair × Bool := (([2, 1, 3, 1], [3, 1, 2]), true)
private def earlyCodes36 : List (ℕ × ℕ) := [(39, 13), (39, 14), (39, 13), (40, 13), (39, 13)]
private abbrev earlyInput37 : LowerPair × Bool := (([2, 1, 3, 2], [3, 1, 2]), false)
private def earlyCodes37 : List (ℕ × ℕ) := [(41, 17), (41, 17), (41, 36), (41, 17), (42, 17)]
private abbrev earlyInput38 : LowerPair × Bool := (([2, 1, 3, 2], [3, 1, 2]), true)
private def earlyCodes38 : List (ℕ × ℕ) := [(15, 13), (15, 14), (15, 13), (43, 13), (15, 13)]
private abbrev earlyInput39 : LowerPair × Bool := (([2, 1, 3, 1], [3, 1, 2]), false)
private def earlyCodes39 : List (ℕ × ℕ) := [(16, 17), (16, 17)]
private abbrev earlyInput40 : LowerPair × Bool := (([2, 1, 3], [3, 1, 2, 1]), true)
private def earlyCodes40 : List (ℕ × ℕ) := [(12, 44), (12, 44), (12, 45), (12, 44), (15, 44)]
private abbrev earlyInput41 : LowerPair × Bool := (([2, 1, 3], [3, 1, 2, 2]), false)
private def earlyCodes41 : List (ℕ × ℕ) := [(16, 46), (16, 46)]
private abbrev earlyInput42 : LowerPair × Bool := (([2, 1, 3], [3, 1, 2, 2]), true)
private def earlyCodes42 : List (ℕ × ℕ) := [(12, 14), (12, 14), (12, 47), (12, 14), (15, 14)]
private abbrev earlyInput43 : LowerPair × Bool := (([2, 1, 3], [3, 1, 2, 1]), false)
private def earlyCodes43 : List (ℕ × ℕ) := [(16, 17), (16, 17)]
private abbrev earlyInput44 : LowerPair × Bool := (([2, 1, 3, 1], [3, 1, 1]), true)
private def earlyCodes44 : List (ℕ × ℕ) := [(39, 9), (39, 10), (39, 9), (40, 9), (39, 9)]
private abbrev earlyInput45 : LowerPair × Bool := (([2, 1, 3, 2], [3, 1, 1]), false)
private def earlyCodes45 : List (ℕ × ℕ) := [(41, 18), (41, 18), (41, 21), (41, 18), (42, 18)]
private abbrev earlyInput46 : LowerPair × Bool := (([2, 1, 3, 2], [3, 1, 1]), true)
private def earlyCodes46 : List (ℕ × ℕ) := [(15, 9), (15, 10), (15, 9), (43, 9), (15, 9)]
private abbrev earlyInput47 : LowerPair × Bool := (([2, 1, 3, 1], [3, 1, 1]), false)
private def earlyCodes47 : List (ℕ × ℕ) := [(16, 18), (16, 18)]
private abbrev earlyInput48 : LowerPair × Bool := (([2, 1, 3], [3, 1, 1, 1]), true)
private def earlyCodes48 : List (ℕ × ℕ) := [(12, 48), (12, 48), (12, 49), (12, 48), (15, 48)]
private abbrev earlyInput49 : LowerPair × Bool := (([2, 1, 3], [3, 1, 1, 2]), false)
private def earlyCodes49 : List (ℕ × ℕ) := [(16, 50), (16, 50)]
private abbrev earlyInput50 : LowerPair × Bool := (([2, 1, 3], [3, 1, 1, 2]), true)
private def earlyCodes50 : List (ℕ × ℕ) := [(12, 10), (12, 10), (12, 51), (12, 10), (15, 10)]
private abbrev earlyInput51 : LowerPair × Bool := (([2, 1, 3], [3, 1, 1, 1]), false)
private def earlyCodes51 : List (ℕ × ℕ) := [(16, 18), (16, 18)]
private abbrev earlyInput52 : LowerPair × Bool := (([2, 1, 2, 1], [3, 1, 1]), true)
private def earlyCodes52 : List (ℕ × ℕ) := [(37, 9), (37, 10), (37, 9), (38, 9), (37, 9)]
private abbrev earlyInput53 : LowerPair × Bool := (([2, 1, 2, 2], [3, 1, 1]), false)
private def earlyCodes53 : List (ℕ × ℕ) := [(52, 18), (52, 18), (52, 21), (52, 18), (53, 18)]
private abbrev earlyInput54 : LowerPair × Bool := (([2, 1, 2, 2], [3, 1, 1]), true)
private def earlyCodes54 : List (ℕ × ℕ) := [(20, 9), (20, 10), (20, 9), (54, 9), (20, 9)]
private abbrev earlyInput55 : LowerPair × Bool := (([2, 1, 2, 1], [3, 1, 1]), false)
private def earlyCodes55 : List (ℕ × ℕ) := [(7, 18), (7, 18), (7, 21), (7, 18), (22, 18)]
private abbrev earlyInput56 : LowerPair × Bool := (([2, 1, 2], [3, 1, 1, 1]), true)
private def earlyCodes56 : List (ℕ × ℕ) := [(19, 48), (19, 48), (19, 49), (19, 48), (20, 48)]
private abbrev earlyInput57 : LowerPair × Bool := (([2, 1, 2], [3, 1, 1, 2]), false)
private def earlyCodes57 : List (ℕ × ℕ) := [(7, 50), (7, 55), (7, 50), (22, 50), (7, 50)]
private abbrev earlyInput58 : LowerPair × Bool := (([2, 1, 2], [3, 1, 1, 2]), true)
private def earlyCodes58 : List (ℕ × ℕ) := [(19, 10), (19, 10), (19, 51), (19, 10), (20, 10)]
private abbrev earlyInput59 : LowerPair × Bool := (([2, 1, 2], [3, 1, 1, 1]), false)
private def earlyCodes59 : List (ℕ × ℕ) := [(7, 18), (7, 21), (7, 18), (22, 18), (7, 18)]
private abbrev earlyInput60 : LowerPair × Bool := (([2, 1, 3, 1], [3, 2]), true)
private def earlyCodes60 : List (ℕ × ℕ) := [(39, 23), (39, 24), (39, 23), (40, 23)]
private abbrev earlyInput61 : LowerPair × Bool := (([2, 1, 3, 2], [3, 2]), false)
private def earlyCodes61 : List (ℕ × ℕ) := [(41, 25), (41, 26), (41, 25), (42, 25)]
private abbrev earlyInput62 : LowerPair × Bool := (([2, 1, 3, 2], [3, 2]), true)
private def earlyCodes62 : List (ℕ × ℕ) := [(15, 23), (15, 24), (15, 23), (43, 23)]
private abbrev earlyInput63 : LowerPair × Bool := (([2, 1, 3, 1], [3, 2]), false)
private def earlyCodes63 : List (ℕ × ℕ) := [(16, 25)]
private abbrev earlyInput64 : LowerPair × Bool := (([2, 1, 3], [3, 2, 2]), true)
private def earlyCodes64 : List (ℕ × ℕ) := [(12, 56), (12, 57), (12, 56), (15, 56)]
private abbrev earlyInput65 : LowerPair × Bool := (([2, 1, 3], [3, 2, 1]), false)
private def earlyCodes65 : List (ℕ × ℕ) := [(16, 58)]
private abbrev earlyInput66 : LowerPair × Bool := (([2, 1, 3], [3, 2, 1]), true)
private def earlyCodes66 : List (ℕ × ℕ) := [(12, 23), (12, 24), (12, 23), (15, 23)]
private abbrev earlyInput67 : LowerPair × Bool := (([2, 1, 3], [3, 2, 2]), false)
private def earlyCodes67 : List (ℕ × ℕ) := [(16, 26)]
private abbrev earlyInput68 : LowerPair × Bool := (([2, 1, 3, 1], [3, 3]), true)
private def earlyCodes68 : List (ℕ × ℕ) := [(39, 1)]
private abbrev earlyInput69 : LowerPair × Bool := (([2, 1, 3, 2], [3, 3]), false)
private def earlyCodes69 : List (ℕ × ℕ) := [(41, 3), (41, 4), (41, 3), (42, 3)]
private abbrev earlyInput70 : LowerPair × Bool := (([2, 1, 3, 2], [3, 3]), true)
private def earlyCodes70 : List (ℕ × ℕ) := [(15, 1)]
private abbrev earlyInput71 : LowerPair × Bool := (([2, 1, 3, 1], [3, 3]), false)
private def earlyCodes71 : List (ℕ × ℕ) := [(16, 3)]
private abbrev earlyInput72 : LowerPair × Bool := (([2, 1, 3], [3, 3, 2]), true)
private def earlyCodes72 : List (ℕ × ℕ) := [(12, 59), (12, 60), (12, 59), (15, 59)]
private abbrev earlyInput73 : LowerPair × Bool := (([2, 1, 3], [3, 3, 1]), false)
private def earlyCodes73 : List (ℕ × ℕ) := [(16, 61)]
private abbrev earlyInput74 : LowerPair × Bool := (([2, 1, 3], [3, 3, 1]), true)
private def earlyCodes74 : List (ℕ × ℕ) := [(12, 1)]
private abbrev earlyInput75 : LowerPair × Bool := (([2, 1, 3], [3, 3, 2]), false)
private def earlyCodes75 : List (ℕ × ℕ) := [(16, 4)]
private abbrev earlyInput76 : LowerPair × Bool := (([2, 1, 2, 1], [3, 2]), true)
private def earlyCodes76 : List (ℕ × ℕ) := [(37, 23), (37, 24), (37, 23), (38, 23)]
private abbrev earlyInput77 : LowerPair × Bool := (([2, 1, 2, 2], [3, 2]), false)
private def earlyCodes77 : List (ℕ × ℕ) := [(52, 25), (52, 26), (52, 25), (53, 25)]
private abbrev earlyInput78 : LowerPair × Bool := (([2, 1, 2, 2], [3, 2]), true)
private def earlyCodes78 : List (ℕ × ℕ) := [(20, 23), (20, 24), (20, 23), (54, 23)]
private abbrev earlyInput79 : LowerPair × Bool := (([2, 1, 2, 1], [3, 2]), false)
private def earlyCodes79 : List (ℕ × ℕ) := [(7, 25), (7, 26), (7, 25), (22, 25)]
private abbrev earlyInput80 : LowerPair × Bool := (([2, 1, 2], [3, 2, 2]), true)
private def earlyCodes80 : List (ℕ × ℕ) := [(19, 56), (19, 57), (19, 56), (20, 56)]
private abbrev earlyInput81 : LowerPair × Bool := (([2, 1, 2], [3, 2, 1]), false)
private def earlyCodes81 : List (ℕ × ℕ) := [(7, 58), (7, 62), (7, 58), (22, 58)]
private abbrev earlyInput82 : LowerPair × Bool := (([2, 1, 2], [3, 2, 1]), true)
private def earlyCodes82 : List (ℕ × ℕ) := [(19, 23), (19, 24), (19, 23), (20, 23)]
private abbrev earlyInput83 : LowerPair × Bool := (([2, 1, 2], [3, 2, 2]), false)
private def earlyCodes83 : List (ℕ × ℕ) := [(7, 26), (7, 63), (7, 26), (22, 26)]
private abbrev earlyInput84 : LowerPair × Bool := (([2, 1, 1, 1, 2], [3, 1, 1]), true)
private def earlyCodes84 : List (ℕ × ℕ) := [(64, 9), (64, 10), (64, 9), (65, 9)]
private abbrev earlyInput85 : LowerPair × Bool := (([2, 1, 1, 1, 1], [3, 1, 1]), false)
private def earlyCodes85 : List (ℕ × ℕ) := [(66, 18), (66, 21), (66, 18), (67, 18)]
private abbrev earlyInput86 : LowerPair × Bool := (([2, 1, 1, 1, 1], [3, 1, 1]), true)
private def earlyCodes86 : List (ℕ × ℕ) := [(8, 9), (8, 10), (8, 9), (11, 9)]
private abbrev earlyInput87 : LowerPair × Bool := (([2, 1, 1, 1, 2], [3, 1, 1]), false)
private def earlyCodes87 : List (ℕ × ℕ) := [(28, 18), (28, 21), (28, 18), (68, 18)]
private abbrev earlyInput88 : LowerPair × Bool := (([2, 1, 1, 1], [3, 1, 1, 1]), true)
private def earlyCodes88 : List (ℕ × ℕ) := [(8, 48), (8, 49), (8, 48), (11, 48)]
private abbrev earlyInput89 : LowerPair × Bool := (([2, 1, 1, 1], [3, 1, 1, 2]), false)
private def earlyCodes89 : List (ℕ × ℕ) := [(27, 50), (27, 55), (27, 50), (28, 50)]
private abbrev earlyInput90 : LowerPair × Bool := (([2, 1, 1, 1], [3, 1, 1, 2]), true)
private def earlyCodes90 : List (ℕ × ℕ) := [(8, 10), (8, 51), (8, 10), (11, 10)]
private abbrev earlyInput91 : LowerPair × Bool := (([2, 1, 1, 1], [3, 1, 1, 1]), false)
private def earlyCodes91 : List (ℕ × ℕ) := [(27, 18), (27, 21), (27, 18), (28, 18)]
private abbrev earlyInput92 : LowerPair × Bool := (([2, 1, 1, 2, 2], [3, 1, 1]), true)
private def earlyCodes92 : List (ℕ × ℕ) := [(69, 9), (69, 10), (69, 9), (70, 9)]
private abbrev earlyInput93 : LowerPair × Bool := (([2, 1, 1, 2, 1], [3, 1, 1]), false)
private def earlyCodes93 : List (ℕ × ℕ) := [(71, 18), (71, 21), (71, 18), (72, 18)]
private abbrev earlyInput94 : LowerPair × Bool := (([2, 1, 1, 2, 1], [3, 1, 1]), true)
private def earlyCodes94 : List (ℕ × ℕ) := [(0, 9), (0, 10), (0, 9), (29, 9)]
private abbrev earlyInput95 : LowerPair × Bool := (([2, 1, 1, 2, 2], [3, 1, 1]), false)
private def earlyCodes95 : List (ℕ × ℕ) := [(31, 18), (31, 21), (31, 18), (73, 18)]
private abbrev earlyInput96 : LowerPair × Bool := (([2, 1, 1, 2], [3, 1, 1, 1]), true)
private def earlyCodes96 : List (ℕ × ℕ) := [(0, 48), (0, 49), (0, 48), (29, 48)]
private abbrev earlyInput97 : LowerPair × Bool := (([2, 1, 1, 2], [3, 1, 1, 2]), false)
private def earlyCodes97 : List (ℕ × ℕ) := [(30, 50), (30, 55), (30, 50), (31, 50)]
private abbrev earlyInput98 : LowerPair × Bool := (([2, 1, 1, 2], [3, 1, 1, 2]), true)
private def earlyCodes98 : List (ℕ × ℕ) := [(0, 10), (0, 51), (0, 10), (29, 10)]
private abbrev earlyInput99 : LowerPair × Bool := (([2, 1, 1, 2], [3, 1, 1, 1]), false)
private def earlyCodes99 : List (ℕ × ℕ) := [(30, 18), (30, 21), (30, 18), (31, 18)]
private abbrev earlyInput100 : LowerPair × Bool := (([2, 1, 1, 1, 2], [3, 2]), true)
private def earlyCodes100 : List (ℕ × ℕ) := [(64, 23), (64, 23), (64, 24), (64, 23), (65, 23)]
private abbrev earlyInput101 : LowerPair × Bool := (([2, 1, 1, 1, 1], [3, 2]), false)
private def earlyCodes101 : List (ℕ × ℕ) := [(66, 25), (66, 26), (66, 25), (67, 25), (66, 25)]
private abbrev earlyInput102 : LowerPair × Bool := (([2, 1, 1, 1, 1], [3, 2]), true)
private def earlyCodes102 : List (ℕ × ℕ) := [(8, 23), (8, 23), (8, 24), (8, 23), (11, 23)]
private abbrev earlyInput103 : LowerPair × Bool := (([2, 1, 1, 1, 2], [3, 2]), false)
private def earlyCodes103 : List (ℕ × ℕ) := [(28, 25), (28, 26), (28, 25), (68, 25), (28, 25)]
private abbrev earlyInput104 : LowerPair × Bool := (([2, 1, 1, 1], [3, 2, 2]), true)
private def earlyCodes104 : List (ℕ × ℕ) := [(8, 56), (8, 57), (8, 56), (11, 56), (8, 56)]
private abbrev earlyInput105 : LowerPair × Bool := (([2, 1, 1, 1], [3, 2, 1]), false)
private def earlyCodes105 : List (ℕ × ℕ) := [(27, 58), (27, 58), (27, 62), (27, 58), (28, 58)]
private abbrev earlyInput106 : LowerPair × Bool := (([2, 1, 1, 1], [3, 2, 1]), true)
private def earlyCodes106 : List (ℕ × ℕ) := [(8, 23), (8, 24), (8, 23), (11, 23), (8, 23)]
private abbrev earlyInput107 : LowerPair × Bool := (([2, 1, 1, 1], [3, 2, 2]), false)
private def earlyCodes107 : List (ℕ × ℕ) := [(27, 26), (27, 26), (27, 63), (27, 26), (28, 26)]
private abbrev earlyInput108 : LowerPair × Bool := (([2, 1, 1, 1, 2], [3, 3]), true)
private def earlyCodes108 : List (ℕ × ℕ) := [(64, 1), (64, 1)]
private abbrev earlyInput109 : LowerPair × Bool := (([2, 1, 1, 1, 1], [3, 3]), false)
private def earlyCodes109 : List (ℕ × ℕ) := [(66, 3), (66, 4), (66, 3), (67, 3), (66, 3)]
private abbrev earlyInput110 : LowerPair × Bool := (([2, 1, 1, 1, 1], [3, 3]), true)
private def earlyCodes110 : List (ℕ × ℕ) := [(8, 1), (8, 1)]
private abbrev earlyInput111 : LowerPair × Bool := (([2, 1, 1, 1, 2], [3, 3]), false)
private def earlyCodes111 : List (ℕ × ℕ) := [(28, 3), (28, 4), (28, 3), (68, 3), (28, 3)]
private abbrev earlyInput112 : LowerPair × Bool := (([2, 1, 1, 1], [3, 3, 2]), true)
private def earlyCodes112 : List (ℕ × ℕ) := [(8, 59), (8, 60), (8, 59), (11, 59), (8, 59)]
private abbrev earlyInput113 : LowerPair × Bool := (([2, 1, 1, 1], [3, 3, 1]), false)
private def earlyCodes113 : List (ℕ × ℕ) := [(27, 61), (27, 61), (27, 74), (27, 61), (28, 61)]
private abbrev earlyInput114 : LowerPair × Bool := (([2, 1, 1, 1], [3, 3, 1]), true)
private def earlyCodes114 : List (ℕ × ℕ) := [(8, 1), (8, 1)]
private abbrev earlyInput115 : LowerPair × Bool := (([2, 1, 1, 1], [3, 3, 2]), false)
private def earlyCodes115 : List (ℕ × ℕ) := [(27, 4), (27, 4), (27, 75), (27, 4), (28, 4)]
private abbrev earlyInput116 : LowerPair × Bool := (([2, 1, 1, 2, 2], [3, 2]), true)
private def earlyCodes116 : List (ℕ × ℕ) := [(69, 23), (69, 23), (69, 24), (69, 23), (70, 23)]
private abbrev earlyInput117 : LowerPair × Bool := (([2, 1, 1, 2, 1], [3, 2]), false)
private def earlyCodes117 : List (ℕ × ℕ) := [(71, 25), (71, 26), (71, 25), (72, 25), (71, 25)]
private abbrev earlyInput118 : LowerPair × Bool := (([2, 1, 1, 2, 1], [3, 2]), true)
private def earlyCodes118 : List (ℕ × ℕ) := [(0, 23), (0, 23), (0, 24), (0, 23), (29, 23)]
private abbrev earlyInput119 : LowerPair × Bool := (([2, 1, 1, 2, 2], [3, 2]), false)
private def earlyCodes119 : List (ℕ × ℕ) := [(31, 25), (31, 26), (31, 25), (73, 25), (31, 25)]
private abbrev earlyInput120 : LowerPair × Bool := (([2, 1, 1, 2], [3, 2, 2]), true)
private def earlyCodes120 : List (ℕ × ℕ) := [(0, 56), (0, 57), (0, 56), (29, 56), (0, 56)]
private abbrev earlyInput121 : LowerPair × Bool := (([2, 1, 1, 2], [3, 2, 1]), false)
private def earlyCodes121 : List (ℕ × ℕ) := [(30, 58), (30, 58), (30, 62), (30, 58), (31, 58)]
private abbrev earlyInput122 : LowerPair × Bool := (([2, 1, 1, 2], [3, 2, 1]), true)
private def earlyCodes122 : List (ℕ × ℕ) := [(0, 23), (0, 24), (0, 23), (29, 23), (0, 23)]
private abbrev earlyInput123 : LowerPair × Bool := (([2, 1, 1, 2], [3, 2, 2]), false)
private def earlyCodes123 : List (ℕ × ℕ) := [(30, 26), (30, 26), (30, 63), (30, 26), (31, 26)]
private abbrev earlyInput124 : LowerPair × Bool := (([2, 1, 1, 3, 2], [3, 2]), true)
private def earlyCodes124 : List (ℕ × ℕ) := [(76, 23), (76, 23), (76, 24), (76, 23), (77, 23)]
private abbrev earlyInput125 : LowerPair × Bool := (([2, 1, 1, 3, 1], [3, 2]), false)
private def earlyCodes125 : List (ℕ × ℕ) := [(78, 25), (78, 26), (78, 25), (79, 25), (78, 25)]
private abbrev earlyInput126 : LowerPair × Bool := (([2, 1, 1, 3, 1], [3, 2]), true)
private def earlyCodes126 : List (ℕ × ℕ) := [(32, 23), (32, 23)]
private abbrev earlyInput127 : LowerPair × Bool := (([2, 1, 1, 3, 2], [3, 2]), false)
private def earlyCodes127 : List (ℕ × ℕ) := [(5, 25), (5, 26), (5, 25), (80, 25), (5, 25)]
private abbrev earlyInput128 : LowerPair × Bool := (([2, 1, 1, 3], [3, 2, 2]), true)
private def earlyCodes128 : List (ℕ × ℕ) := [(32, 56), (32, 56)]
private abbrev earlyInput129 : LowerPair × Bool := (([2, 1, 1, 3], [3, 2, 1]), false)
private def earlyCodes129 : List (ℕ × ℕ) := [(2, 58), (2, 58), (2, 62), (2, 58), (5, 58)]
private abbrev earlyInput130 : LowerPair × Bool := (([2, 1, 1, 3], [3, 2, 1]), true)
private def earlyCodes130 : List (ℕ × ℕ) := [(32, 23), (32, 23)]
private abbrev earlyInput131 : LowerPair × Bool := (([2, 1, 1, 3], [3, 2, 2]), false)
private def earlyCodes131 : List (ℕ × ℕ) := [(2, 26), (2, 26), (2, 63), (2, 26), (5, 26)]
private abbrev earlyInput132 : LowerPair × Bool := (([2, 1, 1, 2, 2], [3, 3]), true)
private def earlyCodes132 : List (ℕ × ℕ) := [(69, 1), (69, 1)]
private abbrev earlyInput133 : LowerPair × Bool := (([2, 1, 1, 2, 1], [3, 3]), false)
private def earlyCodes133 : List (ℕ × ℕ) := [(71, 3), (71, 4), (71, 3), (72, 3), (71, 3)]
private abbrev earlyInput134 : LowerPair × Bool := (([2, 1, 1, 2, 1], [3, 3]), true)
private def earlyCodes134 : List (ℕ × ℕ) := [(0, 1), (0, 1)]
private abbrev earlyInput135 : LowerPair × Bool := (([2, 1, 1, 2, 2], [3, 3]), false)
private def earlyCodes135 : List (ℕ × ℕ) := [(31, 3), (31, 4), (31, 3), (73, 3), (31, 3)]
private abbrev earlyInput136 : LowerPair × Bool := (([2, 1, 1, 2], [3, 3, 2]), true)
private def earlyCodes136 : List (ℕ × ℕ) := [(0, 59), (0, 60), (0, 59), (29, 59), (0, 59)]
private abbrev earlyInput137 : LowerPair × Bool := (([2, 1, 1, 2], [3, 3, 1]), false)
private def earlyCodes137 : List (ℕ × ℕ) := [(30, 61), (30, 61), (30, 74), (30, 61), (31, 61)]
private abbrev earlyInput138 : LowerPair × Bool := (([2, 1, 1, 2], [3, 3, 1]), true)
private def earlyCodes138 : List (ℕ × ℕ) := [(0, 1), (0, 1)]
private abbrev earlyInput139 : LowerPair × Bool := (([2, 1, 1, 2], [3, 3, 2]), false)
private def earlyCodes139 : List (ℕ × ℕ) := [(30, 4), (30, 4), (30, 75), (30, 4), (31, 4)]
private abbrev earlyInput140 : LowerPair × Bool := (([2, 1, 1, 3, 2], [3, 3]), true)
private def earlyCodes140 : List (ℕ × ℕ) := [(76, 1), (76, 1)]
private abbrev earlyInput141 : LowerPair × Bool := (([2, 1, 1, 3, 1], [3, 3]), false)
private def earlyCodes141 : List (ℕ × ℕ) := [(78, 3), (78, 4), (78, 3), (79, 3), (78, 3)]
private abbrev earlyInput142 : LowerPair × Bool := (([2, 1, 1, 3, 1], [3, 3]), true)
private def earlyCodes142 : List (ℕ × ℕ) := [(32, 1), (32, 1)]
private abbrev earlyInput143 : LowerPair × Bool := (([2, 1, 1, 3, 2], [3, 3]), false)
private def earlyCodes143 : List (ℕ × ℕ) := [(5, 3), (5, 4), (5, 3), (80, 3), (5, 3)]
private abbrev earlyInput144 : LowerPair × Bool := (([2, 1, 1, 3], [3, 3, 2]), true)
private def earlyCodes144 : List (ℕ × ℕ) := [(32, 59), (32, 59)]
private abbrev earlyInput145 : LowerPair × Bool := (([2, 1, 1, 3], [3, 3, 1]), false)
private def earlyCodes145 : List (ℕ × ℕ) := [(2, 61), (2, 61), (2, 74), (2, 61), (5, 61)]
private abbrev earlyInput146 : LowerPair × Bool := (([2, 1, 1, 3], [3, 3, 1]), true)
private def earlyCodes146 : List (ℕ × ℕ) := [(32, 1), (32, 1)]
private abbrev earlyInput147 : LowerPair × Bool := (([2, 1, 1, 3], [3, 3, 2]), false)
private def earlyCodes147 : List (ℕ × ℕ) := [(2, 4), (2, 4), (2, 75), (2, 4), (5, 4)]
private abbrev earlyInput148 : LowerPair × Bool := (([2, 1, 2, 2], [3, 1, 2]), false)
private def earlyCodes148 : List (ℕ × ℕ) := [(52, 17), (52, 17), (52, 36), (52, 17), (53, 17)]
private abbrev earlyInput149 : LowerPair × Bool := (([2, 1, 2, 2], [3, 1, 2]), true)
private def earlyCodes149 : List (ℕ × ℕ) := [(20, 13), (20, 14), (20, 13), (54, 13), (20, 13)]
private abbrev earlyInput150 : LowerPair × Bool := (([2, 1, 2], [3, 1, 2, 1]), true)
private def earlyCodes150 : List (ℕ × ℕ) := [(19, 44), (19, 44), (19, 45), (19, 44), (20, 44)]
private abbrev earlyInput151 : LowerPair × Bool := (([2, 1, 2], [3, 1, 2, 2]), false)
private def earlyCodes151 : List (ℕ × ℕ) := [(7, 46), (7, 81), (7, 46), (22, 46), (7, 46)]
private abbrev earlyInput152 : LowerPair × Bool := (([2, 1, 2], [3, 1, 2, 2]), true)
private def earlyCodes152 : List (ℕ × ℕ) := [(19, 14), (19, 14), (19, 47), (19, 14), (20, 14)]
private abbrev earlyInput153 : LowerPair × Bool := (([2, 1, 2], [3, 1, 2, 1]), false)
private def earlyCodes153 : List (ℕ × ℕ) := [(7, 17), (7, 36), (7, 17), (22, 17), (7, 17)]
private abbrev earlyInput154 : LowerPair × Bool := (([2, 1, 2, 1, 2], [3, 1, 2]), true)
private def earlyCodes154 : List (ℕ × ℕ) := [(82, 13), (82, 14), (82, 13), (83, 13)]
private abbrev earlyInput155 : LowerPair × Bool := (([2, 1, 2, 1, 1], [3, 1, 2]), false)
private def earlyCodes155 : List (ℕ × ℕ) := [(84, 17), (84, 36), (84, 17), (85, 17)]
private abbrev earlyInput156 : LowerPair × Bool := (([2, 1, 2, 1, 1], [3, 1, 2]), true)
private def earlyCodes156 : List (ℕ × ℕ) := [(37, 13), (37, 14), (37, 13), (38, 13)]
private abbrev earlyInput157 : LowerPair × Bool := (([2, 1, 2, 1, 2], [3, 1, 2]), false)
private def earlyCodes157 : List (ℕ × ℕ) := [(22, 17), (22, 36), (22, 17), (86, 17)]
private abbrev earlyInput158 : LowerPair × Bool := (([2, 1, 2, 1], [3, 1, 2, 1]), true)
private def earlyCodes158 : List (ℕ × ℕ) := [(37, 44), (37, 45), (37, 44), (38, 44)]
private abbrev earlyInput159 : LowerPair × Bool := (([2, 1, 2, 1], [3, 1, 2, 2]), false)
private def earlyCodes159 : List (ℕ × ℕ) := [(7, 46), (7, 81), (7, 46), (22, 46)]
private abbrev earlyInput160 : LowerPair × Bool := (([2, 1, 2, 1], [3, 1, 2, 2]), true)
private def earlyCodes160 : List (ℕ × ℕ) := [(37, 14), (37, 47), (37, 14), (38, 14)]
private abbrev earlyInput161 : LowerPair × Bool := (([2, 1, 2, 1], [3, 1, 2, 1]), false)
private def earlyCodes161 : List (ℕ × ℕ) := [(7, 17), (7, 36), (7, 17), (22, 17)]
private def earlyDecode (x : ℕ × ℕ) : CertField × CertField := (earlyFields[x.1]?.getD ⟨0,0,0,0⟩,earlyFields[x.2]?.getD ⟨0,0,0,0⟩)
private theorem hEC0 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput0.1 earlyInput0.2).map Prod.fst = earlyCodes0.map earlyDecode := by decide +kernel
private theorem hEC1 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput1.1 earlyInput1.2).map Prod.fst = earlyCodes1.map earlyDecode := by decide +kernel
private theorem hEC2 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput2.1 earlyInput2.2).map Prod.fst = earlyCodes2.map earlyDecode := by decide +kernel
private theorem hEC3 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput3.1 earlyInput3.2).map Prod.fst = earlyCodes3.map earlyDecode := by decide +kernel
private theorem hEC4 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput4.1 earlyInput4.2).map Prod.fst = earlyCodes4.map earlyDecode := by decide +kernel
private theorem hEC5 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput5.1 earlyInput5.2).map Prod.fst = earlyCodes5.map earlyDecode := by decide +kernel
private theorem hEC6 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput6.1 earlyInput6.2).map Prod.fst = earlyCodes6.map earlyDecode := by decide +kernel
private theorem hEC7 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput7.1 earlyInput7.2).map Prod.fst = earlyCodes7.map earlyDecode := by decide +kernel
private theorem hEC8 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput8.1 earlyInput8.2).map Prod.fst = earlyCodes8.map earlyDecode := by decide +kernel
private theorem hEC9 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput9.1 earlyInput9.2).map Prod.fst = earlyCodes9.map earlyDecode := by decide +kernel
private theorem hEC10 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput10.1 earlyInput10.2).map Prod.fst = earlyCodes10.map earlyDecode := by decide +kernel
private theorem hEC11 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput11.1 earlyInput11.2).map Prod.fst = earlyCodes11.map earlyDecode := by decide +kernel
private theorem hEC12 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput12.1 earlyInput12.2).map Prod.fst = earlyCodes12.map earlyDecode := by decide +kernel
private theorem hEC13 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput13.1 earlyInput13.2).map Prod.fst = earlyCodes13.map earlyDecode := by decide +kernel
private theorem hEC14 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput14.1 earlyInput14.2).map Prod.fst = earlyCodes14.map earlyDecode := by decide +kernel
private theorem hEC15 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput15.1 earlyInput15.2).map Prod.fst = earlyCodes15.map earlyDecode := by decide +kernel
private theorem hEC16 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput16.1 earlyInput16.2).map Prod.fst = earlyCodes16.map earlyDecode := by decide +kernel
private theorem hEC17 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput17.1 earlyInput17.2).map Prod.fst = earlyCodes17.map earlyDecode := by decide +kernel
private theorem hEC18 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput18.1 earlyInput18.2).map Prod.fst = earlyCodes18.map earlyDecode := by decide +kernel
private theorem hEC19 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput19.1 earlyInput19.2).map Prod.fst = earlyCodes19.map earlyDecode := by decide +kernel
private theorem hEC20 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput20.1 earlyInput20.2).map Prod.fst = earlyCodes20.map earlyDecode := by decide +kernel
private theorem hEC21 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput21.1 earlyInput21.2).map Prod.fst = earlyCodes21.map earlyDecode := by decide +kernel
private theorem hEC22 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput22.1 earlyInput22.2).map Prod.fst = earlyCodes22.map earlyDecode := by decide +kernel
private theorem hEC23 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput23.1 earlyInput23.2).map Prod.fst = earlyCodes23.map earlyDecode := by decide +kernel
private theorem hEC24 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput24.1 earlyInput24.2).map Prod.fst = earlyCodes24.map earlyDecode := by decide +kernel
private theorem hEC25 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput25.1 earlyInput25.2).map Prod.fst = earlyCodes25.map earlyDecode := by decide +kernel
private theorem hEC26 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput26.1 earlyInput26.2).map Prod.fst = earlyCodes26.map earlyDecode := by decide +kernel
private theorem hEC27 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput27.1 earlyInput27.2).map Prod.fst = earlyCodes27.map earlyDecode := by decide +kernel
private theorem hEC28 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput28.1 earlyInput28.2).map Prod.fst = earlyCodes28.map earlyDecode := by decide +kernel
private theorem hEC29 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput29.1 earlyInput29.2).map Prod.fst = earlyCodes29.map earlyDecode := by decide +kernel
private theorem hEC30 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput30.1 earlyInput30.2).map Prod.fst = earlyCodes30.map earlyDecode := by decide +kernel
private theorem hEC31 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput31.1 earlyInput31.2).map Prod.fst = earlyCodes31.map earlyDecode := by decide +kernel
private theorem hEC32 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput32.1 earlyInput32.2).map Prod.fst = earlyCodes32.map earlyDecode := by decide +kernel
private theorem hEC33 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput33.1 earlyInput33.2).map Prod.fst = earlyCodes33.map earlyDecode := by decide +kernel
private theorem hEC34 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput34.1 earlyInput34.2).map Prod.fst = earlyCodes34.map earlyDecode := by decide +kernel
private theorem hEC35 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput35.1 earlyInput35.2).map Prod.fst = earlyCodes35.map earlyDecode := by decide +kernel
private theorem hEC36 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput36.1 earlyInput36.2).map Prod.fst = earlyCodes36.map earlyDecode := by decide +kernel
private theorem hEC37 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput37.1 earlyInput37.2).map Prod.fst = earlyCodes37.map earlyDecode := by decide +kernel
private theorem hEC38 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput38.1 earlyInput38.2).map Prod.fst = earlyCodes38.map earlyDecode := by decide +kernel
private theorem hEC39 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput39.1 earlyInput39.2).map Prod.fst = earlyCodes39.map earlyDecode := by decide +kernel
private theorem hEC40 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput40.1 earlyInput40.2).map Prod.fst = earlyCodes40.map earlyDecode := by decide +kernel
private theorem hEC41 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput41.1 earlyInput41.2).map Prod.fst = earlyCodes41.map earlyDecode := by decide +kernel
private theorem hEC42 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput42.1 earlyInput42.2).map Prod.fst = earlyCodes42.map earlyDecode := by decide +kernel
private theorem hEC43 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput43.1 earlyInput43.2).map Prod.fst = earlyCodes43.map earlyDecode := by decide +kernel
private theorem hEC44 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput44.1 earlyInput44.2).map Prod.fst = earlyCodes44.map earlyDecode := by decide +kernel
private theorem hEC45 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput45.1 earlyInput45.2).map Prod.fst = earlyCodes45.map earlyDecode := by decide +kernel
private theorem hEC46 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput46.1 earlyInput46.2).map Prod.fst = earlyCodes46.map earlyDecode := by decide +kernel
private theorem hEC47 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput47.1 earlyInput47.2).map Prod.fst = earlyCodes47.map earlyDecode := by decide +kernel
private theorem hEC48 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput48.1 earlyInput48.2).map Prod.fst = earlyCodes48.map earlyDecode := by decide +kernel
private theorem hEC49 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput49.1 earlyInput49.2).map Prod.fst = earlyCodes49.map earlyDecode := by decide +kernel
private theorem hEC50 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput50.1 earlyInput50.2).map Prod.fst = earlyCodes50.map earlyDecode := by decide +kernel
private theorem hEC51 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput51.1 earlyInput51.2).map Prod.fst = earlyCodes51.map earlyDecode := by decide +kernel
private theorem hEC52 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput52.1 earlyInput52.2).map Prod.fst = earlyCodes52.map earlyDecode := by decide +kernel
private theorem hEC53 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput53.1 earlyInput53.2).map Prod.fst = earlyCodes53.map earlyDecode := by decide +kernel
private theorem hEC54 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput54.1 earlyInput54.2).map Prod.fst = earlyCodes54.map earlyDecode := by decide +kernel
private theorem hEC55 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput55.1 earlyInput55.2).map Prod.fst = earlyCodes55.map earlyDecode := by decide +kernel
private theorem hEC56 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput56.1 earlyInput56.2).map Prod.fst = earlyCodes56.map earlyDecode := by decide +kernel
private theorem hEC57 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput57.1 earlyInput57.2).map Prod.fst = earlyCodes57.map earlyDecode := by decide +kernel
private theorem hEC58 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput58.1 earlyInput58.2).map Prod.fst = earlyCodes58.map earlyDecode := by decide +kernel
private theorem hEC59 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput59.1 earlyInput59.2).map Prod.fst = earlyCodes59.map earlyDecode := by decide +kernel
private theorem hEC60 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput60.1 earlyInput60.2).map Prod.fst = earlyCodes60.map earlyDecode := by decide +kernel
private theorem hEC61 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput61.1 earlyInput61.2).map Prod.fst = earlyCodes61.map earlyDecode := by decide +kernel
private theorem hEC62 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput62.1 earlyInput62.2).map Prod.fst = earlyCodes62.map earlyDecode := by decide +kernel
private theorem hEC63 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput63.1 earlyInput63.2).map Prod.fst = earlyCodes63.map earlyDecode := by decide +kernel
private theorem hEC64 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput64.1 earlyInput64.2).map Prod.fst = earlyCodes64.map earlyDecode := by decide +kernel
private theorem hEC65 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput65.1 earlyInput65.2).map Prod.fst = earlyCodes65.map earlyDecode := by decide +kernel
private theorem hEC66 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput66.1 earlyInput66.2).map Prod.fst = earlyCodes66.map earlyDecode := by decide +kernel
private theorem hEC67 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput67.1 earlyInput67.2).map Prod.fst = earlyCodes67.map earlyDecode := by decide +kernel
private theorem hEC68 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput68.1 earlyInput68.2).map Prod.fst = earlyCodes68.map earlyDecode := by decide +kernel
private theorem hEC69 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput69.1 earlyInput69.2).map Prod.fst = earlyCodes69.map earlyDecode := by decide +kernel
private theorem hEC70 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput70.1 earlyInput70.2).map Prod.fst = earlyCodes70.map earlyDecode := by decide +kernel
private theorem hEC71 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput71.1 earlyInput71.2).map Prod.fst = earlyCodes71.map earlyDecode := by decide +kernel
private theorem hEC72 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput72.1 earlyInput72.2).map Prod.fst = earlyCodes72.map earlyDecode := by decide +kernel
private theorem hEC73 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput73.1 earlyInput73.2).map Prod.fst = earlyCodes73.map earlyDecode := by decide +kernel
private theorem hEC74 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput74.1 earlyInput74.2).map Prod.fst = earlyCodes74.map earlyDecode := by decide +kernel
private theorem hEC75 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput75.1 earlyInput75.2).map Prod.fst = earlyCodes75.map earlyDecode := by decide +kernel
private theorem hEC76 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput76.1 earlyInput76.2).map Prod.fst = earlyCodes76.map earlyDecode := by decide +kernel
private theorem hEC77 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput77.1 earlyInput77.2).map Prod.fst = earlyCodes77.map earlyDecode := by decide +kernel
private theorem hEC78 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput78.1 earlyInput78.2).map Prod.fst = earlyCodes78.map earlyDecode := by decide +kernel
private theorem hEC79 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput79.1 earlyInput79.2).map Prod.fst = earlyCodes79.map earlyDecode := by decide +kernel
private theorem hEC80 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput80.1 earlyInput80.2).map Prod.fst = earlyCodes80.map earlyDecode := by decide +kernel
private theorem hEC81 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput81.1 earlyInput81.2).map Prod.fst = earlyCodes81.map earlyDecode := by decide +kernel
private theorem hEC82 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput82.1 earlyInput82.2).map Prod.fst = earlyCodes82.map earlyDecode := by decide +kernel
private theorem hEC83 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput83.1 earlyInput83.2).map Prod.fst = earlyCodes83.map earlyDecode := by decide +kernel
private theorem hEC84 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput84.1 earlyInput84.2).map Prod.fst = earlyCodes84.map earlyDecode := by decide +kernel
private theorem hEC85 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput85.1 earlyInput85.2).map Prod.fst = earlyCodes85.map earlyDecode := by decide +kernel
private theorem hEC86 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput86.1 earlyInput86.2).map Prod.fst = earlyCodes86.map earlyDecode := by decide +kernel
private theorem hEC87 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput87.1 earlyInput87.2).map Prod.fst = earlyCodes87.map earlyDecode := by decide +kernel
private theorem hEC88 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput88.1 earlyInput88.2).map Prod.fst = earlyCodes88.map earlyDecode := by decide +kernel
private theorem hEC89 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput89.1 earlyInput89.2).map Prod.fst = earlyCodes89.map earlyDecode := by decide +kernel
private theorem hEC90 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput90.1 earlyInput90.2).map Prod.fst = earlyCodes90.map earlyDecode := by decide +kernel
private theorem hEC91 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput91.1 earlyInput91.2).map Prod.fst = earlyCodes91.map earlyDecode := by decide +kernel
private theorem hEC92 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput92.1 earlyInput92.2).map Prod.fst = earlyCodes92.map earlyDecode := by decide +kernel
private theorem hEC93 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput93.1 earlyInput93.2).map Prod.fst = earlyCodes93.map earlyDecode := by decide +kernel
private theorem hEC94 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput94.1 earlyInput94.2).map Prod.fst = earlyCodes94.map earlyDecode := by decide +kernel
private theorem hEC95 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput95.1 earlyInput95.2).map Prod.fst = earlyCodes95.map earlyDecode := by decide +kernel
private theorem hEC96 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput96.1 earlyInput96.2).map Prod.fst = earlyCodes96.map earlyDecode := by decide +kernel
private theorem hEC97 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput97.1 earlyInput97.2).map Prod.fst = earlyCodes97.map earlyDecode := by decide +kernel
private theorem hEC98 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput98.1 earlyInput98.2).map Prod.fst = earlyCodes98.map earlyDecode := by decide +kernel
private theorem hEC99 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput99.1 earlyInput99.2).map Prod.fst = earlyCodes99.map earlyDecode := by decide +kernel
private theorem hEC100 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput100.1 earlyInput100.2).map Prod.fst = earlyCodes100.map earlyDecode := by decide +kernel
private theorem hEC101 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput101.1 earlyInput101.2).map Prod.fst = earlyCodes101.map earlyDecode := by decide +kernel
private theorem hEC102 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput102.1 earlyInput102.2).map Prod.fst = earlyCodes102.map earlyDecode := by decide +kernel
private theorem hEC103 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput103.1 earlyInput103.2).map Prod.fst = earlyCodes103.map earlyDecode := by decide +kernel
private theorem hEC104 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput104.1 earlyInput104.2).map Prod.fst = earlyCodes104.map earlyDecode := by decide +kernel
private theorem hEC105 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput105.1 earlyInput105.2).map Prod.fst = earlyCodes105.map earlyDecode := by decide +kernel
private theorem hEC106 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput106.1 earlyInput106.2).map Prod.fst = earlyCodes106.map earlyDecode := by decide +kernel
private theorem hEC107 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput107.1 earlyInput107.2).map Prod.fst = earlyCodes107.map earlyDecode := by decide +kernel
private theorem hEC108 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput108.1 earlyInput108.2).map Prod.fst = earlyCodes108.map earlyDecode := by decide +kernel
private theorem hEC109 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput109.1 earlyInput109.2).map Prod.fst = earlyCodes109.map earlyDecode := by decide +kernel
private theorem hEC110 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput110.1 earlyInput110.2).map Prod.fst = earlyCodes110.map earlyDecode := by decide +kernel
private theorem hEC111 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput111.1 earlyInput111.2).map Prod.fst = earlyCodes111.map earlyDecode := by decide +kernel
private theorem hEC112 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput112.1 earlyInput112.2).map Prod.fst = earlyCodes112.map earlyDecode := by decide +kernel
private theorem hEC113 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput113.1 earlyInput113.2).map Prod.fst = earlyCodes113.map earlyDecode := by decide +kernel
private theorem hEC114 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput114.1 earlyInput114.2).map Prod.fst = earlyCodes114.map earlyDecode := by decide +kernel
private theorem hEC115 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput115.1 earlyInput115.2).map Prod.fst = earlyCodes115.map earlyDecode := by decide +kernel
private theorem hEC116 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput116.1 earlyInput116.2).map Prod.fst = earlyCodes116.map earlyDecode := by decide +kernel
private theorem hEC117 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput117.1 earlyInput117.2).map Prod.fst = earlyCodes117.map earlyDecode := by decide +kernel
private theorem hEC118 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput118.1 earlyInput118.2).map Prod.fst = earlyCodes118.map earlyDecode := by decide +kernel
private theorem hEC119 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput119.1 earlyInput119.2).map Prod.fst = earlyCodes119.map earlyDecode := by decide +kernel
private theorem hEC120 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput120.1 earlyInput120.2).map Prod.fst = earlyCodes120.map earlyDecode := by decide +kernel
private theorem hEC121 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput121.1 earlyInput121.2).map Prod.fst = earlyCodes121.map earlyDecode := by decide +kernel
private theorem hEC122 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput122.1 earlyInput122.2).map Prod.fst = earlyCodes122.map earlyDecode := by decide +kernel
private theorem hEC123 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput123.1 earlyInput123.2).map Prod.fst = earlyCodes123.map earlyDecode := by decide +kernel
private theorem hEC124 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput124.1 earlyInput124.2).map Prod.fst = earlyCodes124.map earlyDecode := by decide +kernel
private theorem hEC125 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput125.1 earlyInput125.2).map Prod.fst = earlyCodes125.map earlyDecode := by decide +kernel
private theorem hEC126 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput126.1 earlyInput126.2).map Prod.fst = earlyCodes126.map earlyDecode := by decide +kernel
private theorem hEC127 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput127.1 earlyInput127.2).map Prod.fst = earlyCodes127.map earlyDecode := by decide +kernel
private theorem hEC128 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput128.1 earlyInput128.2).map Prod.fst = earlyCodes128.map earlyDecode := by decide +kernel
private theorem hEC129 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput129.1 earlyInput129.2).map Prod.fst = earlyCodes129.map earlyDecode := by decide +kernel
private theorem hEC130 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput130.1 earlyInput130.2).map Prod.fst = earlyCodes130.map earlyDecode := by decide +kernel
private theorem hEC131 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput131.1 earlyInput131.2).map Prod.fst = earlyCodes131.map earlyDecode := by decide +kernel
private theorem hEC132 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput132.1 earlyInput132.2).map Prod.fst = earlyCodes132.map earlyDecode := by decide +kernel
private theorem hEC133 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput133.1 earlyInput133.2).map Prod.fst = earlyCodes133.map earlyDecode := by decide +kernel
private theorem hEC134 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput134.1 earlyInput134.2).map Prod.fst = earlyCodes134.map earlyDecode := by decide +kernel
private theorem hEC135 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput135.1 earlyInput135.2).map Prod.fst = earlyCodes135.map earlyDecode := by decide +kernel
private theorem hEC136 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput136.1 earlyInput136.2).map Prod.fst = earlyCodes136.map earlyDecode := by decide +kernel
private theorem hEC137 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput137.1 earlyInput137.2).map Prod.fst = earlyCodes137.map earlyDecode := by decide +kernel
private theorem hEC138 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput138.1 earlyInput138.2).map Prod.fst = earlyCodes138.map earlyDecode := by decide +kernel
private theorem hEC139 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput139.1 earlyInput139.2).map Prod.fst = earlyCodes139.map earlyDecode := by decide +kernel
private theorem hEC140 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput140.1 earlyInput140.2).map Prod.fst = earlyCodes140.map earlyDecode := by decide +kernel
private theorem hEC141 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput141.1 earlyInput141.2).map Prod.fst = earlyCodes141.map earlyDecode := by decide +kernel
private theorem hEC142 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput142.1 earlyInput142.2).map Prod.fst = earlyCodes142.map earlyDecode := by decide +kernel
private theorem hEC143 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput143.1 earlyInput143.2).map Prod.fst = earlyCodes143.map earlyDecode := by decide +kernel
private theorem hEC144 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput144.1 earlyInput144.2).map Prod.fst = earlyCodes144.map earlyDecode := by decide +kernel
private theorem hEC145 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput145.1 earlyInput145.2).map Prod.fst = earlyCodes145.map earlyDecode := by decide +kernel
private theorem hEC146 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput146.1 earlyInput146.2).map Prod.fst = earlyCodes146.map earlyDecode := by decide +kernel
private theorem hEC147 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput147.1 earlyInput147.2).map Prod.fst = earlyCodes147.map earlyDecode := by decide +kernel
private theorem hEC148 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput148.1 earlyInput148.2).map Prod.fst = earlyCodes148.map earlyDecode := by decide +kernel
private theorem hEC149 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput149.1 earlyInput149.2).map Prod.fst = earlyCodes149.map earlyDecode := by decide +kernel
private theorem hEC150 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput150.1 earlyInput150.2).map Prod.fst = earlyCodes150.map earlyDecode := by decide +kernel
private theorem hEC151 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput151.1 earlyInput151.2).map Prod.fst = earlyCodes151.map earlyDecode := by decide +kernel
private theorem hEC152 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput152.1 earlyInput152.2).map Prod.fst = earlyCodes152.map earlyDecode := by decide +kernel
private theorem hEC153 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput153.1 earlyInput153.2).map Prod.fst = earlyCodes153.map earlyDecode := by decide +kernel
private theorem hEC154 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput154.1 earlyInput154.2).map Prod.fst = earlyCodes154.map earlyDecode := by decide +kernel
private theorem hEC155 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput155.1 earlyInput155.2).map Prod.fst = earlyCodes155.map earlyDecode := by decide +kernel
private theorem hEC156 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput156.1 earlyInput156.2).map Prod.fst = earlyCodes156.map earlyDecode := by decide +kernel
private theorem hEC157 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput157.1 earlyInput157.2).map Prod.fst = earlyCodes157.map earlyDecode := by decide +kernel
private theorem hEC158 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput158.1 earlyInput158.2).map Prod.fst = earlyCodes158.map earlyDecode := by decide +kernel
private theorem hEC159 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput159.1 earlyInput159.2).map Prod.fst = earlyCodes159.map earlyDecode := by decide +kernel
private theorem hEC160 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput160.1 earlyInput160.2).map Prod.fst = earlyCodes160.map earlyDecode := by decide +kernel
private theorem hEC161 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalTerminal3) earlyInput161.1 earlyInput161.2).map Prod.fst = earlyCodes161.map earlyDecode := by decide +kernel
private theorem pairFlags_4_5_0 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput4.1 earlyInput4.2 earlyInput5.1 earlyInput5.2 false = (List.replicate 4 true) := by
  unfold earlyCompareFlags
  rw [hEC4,hEC5]
  decide +kernel
private theorem pairFlags_6_7_0 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput6.1 earlyInput6.2 earlyInput7.1 earlyInput7.2 false = (List.replicate 4 true) := by
  unfold earlyCompareFlags
  rw [hEC6,hEC7]
  decide +kernel
private theorem pairFlags_8_9_0 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput8.1 earlyInput8.2 earlyInput9.1 earlyInput9.2 false = (List.replicate 16 true) := by
  unfold earlyCompareFlags
  rw [hEC8,hEC9]
  decide +kernel
private theorem pairFlags_10_11_0 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput10.1 earlyInput10.2 earlyInput11.1 earlyInput11.2 false = (List.replicate 10 true) := by
  unfold earlyCompareFlags
  rw [hEC10,hEC11]
  decide +kernel
private theorem pairFlags_12_13_0 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput12.1 earlyInput12.2 earlyInput13.1 earlyInput13.2 false = (List.replicate 4 true) := by
  unfold earlyCompareFlags
  rw [hEC12,hEC13]
  decide +kernel
private theorem pairFlags_14_15_0 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput14.1 earlyInput14.2 earlyInput15.1 earlyInput15.2 false = (List.replicate 25 true) := by
  unfold earlyCompareFlags
  rw [hEC14,hEC15]
  decide +kernel
private theorem pairFlags_3_16_0 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput3.1 earlyInput3.2 earlyInput16.1 earlyInput16.2 false = (List.replicate 25 true) := by
  unfold earlyCompareFlags
  rw [hEC3,hEC16]
  decide +kernel
private theorem pairFlags_17_18_0 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput17.1 earlyInput17.2 earlyInput18.1 earlyInput18.2 false = (List.replicate 25 true) := by
  unfold earlyCompareFlags
  rw [hEC17,hEC18]
  decide +kernel
private theorem pairFlags_19_20_0 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput19.1 earlyInput19.2 earlyInput20.1 earlyInput20.2 false = (List.replicate 16 true) := by
  unfold earlyCompareFlags
  rw [hEC19,hEC20]
  decide +kernel
private theorem pairFlags_21_22_0 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput21.1 earlyInput21.2 earlyInput22.1 earlyInput22.2 false = (List.replicate 4 true) := by
  unfold earlyCompareFlags
  rw [hEC21,hEC22]
  decide +kernel
private theorem pairFlags_23_24_0 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput23.1 earlyInput23.2 earlyInput24.1 earlyInput24.2 false = (List.replicate 16 true) := by
  unfold earlyCompareFlags
  rw [hEC23,hEC24]
  decide +kernel
private theorem pairFlags_25_26_0 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput25.1 earlyInput25.2 earlyInput26.1 earlyInput26.2 false = (List.replicate 4 true) := by
  unfold earlyCompareFlags
  rw [hEC25,hEC26]
  decide +kernel
private theorem pairFlags_0_27_0 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput0.1 earlyInput0.2 earlyInput27.1 earlyInput27.2 false = (List.replicate 4 true) := by
  unfold earlyCompareFlags
  rw [hEC0,hEC27]
  decide +kernel
private theorem pairFlags_28_5_0 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput28.1 earlyInput28.2 earlyInput5.1 earlyInput5.2 false = (List.replicate 4 false) := by
  unfold earlyCompareFlags
  rw [hEC28,hEC5]
  decide +kernel
private theorem pairFlags_4_29_0 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput4.1 earlyInput4.2 earlyInput29.1 earlyInput29.2 false = (List.replicate 4 false) := by
  unfold earlyCompareFlags
  rw [hEC4,hEC29]
  decide +kernel
private theorem pairFlags_4_7_0 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput4.1 earlyInput4.2 earlyInput7.1 earlyInput7.2 false = (List.replicate 4 false) := by
  unfold earlyCompareFlags
  rw [hEC4,hEC7]
  decide +kernel
private theorem pairFlags_6_5_0 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput6.1 earlyInput6.2 earlyInput5.1 earlyInput5.2 false = (List.replicate 4 true) := by
  unfold earlyCompareFlags
  rw [hEC6,hEC5]
  decide +kernel
private theorem pairFlags_8_11_0 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput8.1 earlyInput8.2 earlyInput11.1 earlyInput11.2 false = (List.replicate 8 false) := by
  unfold earlyCompareFlags
  rw [hEC8,hEC11]
  decide +kernel
private theorem pairFlags_10_9_0 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput10.1 earlyInput10.2 earlyInput9.1 earlyInput9.2 false = (List.replicate 20 false) := by
  unfold earlyCompareFlags
  rw [hEC10,hEC9]
  decide +kernel
private theorem pairFlags_10_13_0 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput10.1 earlyInput10.2 earlyInput13.1 earlyInput13.2 false = (List.replicate 10 false) := by
  unfold earlyCompareFlags
  rw [hEC10,hEC13]
  decide +kernel
private theorem pairFlags_12_11_0 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput12.1 earlyInput12.2 earlyInput11.1 earlyInput11.2 false = (List.replicate 4 true) := by
  unfold earlyCompareFlags
  rw [hEC12,hEC11]
  decide +kernel
private theorem pairFlags_12_15_0 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput12.1 earlyInput12.2 earlyInput15.1 earlyInput15.2 false = (List.replicate 10 false) := by
  unfold earlyCompareFlags
  rw [hEC12,hEC15]
  decide +kernel
private theorem pairFlags_14_13_0 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput14.1 earlyInput14.2 earlyInput13.1 earlyInput13.2 false = (List.replicate 10 false) := by
  unfold earlyCompareFlags
  rw [hEC14,hEC13]
  decide +kernel
private theorem pairFlags_14_16_0 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput14.1 earlyInput14.2 earlyInput16.1 earlyInput16.2 false = (List.replicate 25 false) := by
  unfold earlyCompareFlags
  rw [hEC14,hEC16]
  decide +kernel
private theorem pairFlags_3_15_0 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput3.1 earlyInput3.2 earlyInput15.1 earlyInput15.2 false = (List.replicate 25 false) := by
  unfold earlyCompareFlags
  rw [hEC3,hEC15]
  decide +kernel
private theorem pairFlags_17_20_0 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput17.1 earlyInput17.2 earlyInput20.1 earlyInput20.2 false = (List.replicate 20 false) := by
  unfold earlyCompareFlags
  rw [hEC17,hEC20]
  decide +kernel
private theorem pairFlags_19_18_0 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput19.1 earlyInput19.2 earlyInput18.1 earlyInput18.2 false = (List.replicate 20 false) := by
  unfold earlyCompareFlags
  rw [hEC19,hEC18]
  decide +kernel
private theorem pairFlags_19_22_0 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput19.1 earlyInput19.2 earlyInput22.1 earlyInput22.2 false = (List.replicate 16 false) := by
  unfold earlyCompareFlags
  rw [hEC19,hEC22]
  decide +kernel
private theorem pairFlags_21_20_0 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput21.1 earlyInput21.2 earlyInput20.1 earlyInput20.2 false = (List.replicate 4 true) := by
  unfold earlyCompareFlags
  rw [hEC21,hEC20]
  decide +kernel
private theorem pairFlags_21_24_0 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput21.1 earlyInput21.2 earlyInput24.1 earlyInput24.2 false = (List.replicate 4 false) := by
  unfold earlyCompareFlags
  rw [hEC21,hEC24]
  decide +kernel
private theorem pairFlags_23_22_0 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput23.1 earlyInput23.2 earlyInput22.1 earlyInput22.2 false = (List.replicate 16 false) := by
  unfold earlyCompareFlags
  rw [hEC23,hEC22]
  decide +kernel
private theorem pairFlags_23_26_0 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput23.1 earlyInput23.2 earlyInput26.1 earlyInput26.2 false = (List.replicate 16 false) := by
  unfold earlyCompareFlags
  rw [hEC23,hEC26]
  decide +kernel
private theorem pairFlags_25_24_0 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput25.1 earlyInput25.2 earlyInput24.1 earlyInput24.2 false = (List.replicate 4 true) := by
  unfold earlyCompareFlags
  rw [hEC25,hEC24]
  decide +kernel
private theorem pairFlags_25_27_0 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput25.1 earlyInput25.2 earlyInput27.1 earlyInput27.2 false = (List.replicate 4 false) := by
  unfold earlyCompareFlags
  rw [hEC25,hEC27]
  decide +kernel
private theorem pairFlags_0_26_0 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput0.1 earlyInput0.2 earlyInput26.1 earlyInput26.2 false = (List.replicate 4 false) := by
  unfold earlyCompareFlags
  rw [hEC0,hEC26]
  decide +kernel
private theorem pairFlags_6_30_0 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput6.1 earlyInput6.2 earlyInput30.1 earlyInput30.2 false = (List.replicate 20 false) := by
  unfold earlyCompareFlags
  rw [hEC6,hEC30]
  decide +kernel
private theorem pairFlags_31_7_0 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput31.1 earlyInput31.2 earlyInput7.1 earlyInput7.2 false = (List.replicate 5 false) := by
  unfold earlyCompareFlags
  rw [hEC31,hEC7]
  decide +kernel
private theorem pairFlags_31_9_0 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput31.1 earlyInput31.2 earlyInput9.1 earlyInput9.2 false = (List.replicate 20 false) := by
  unfold earlyCompareFlags
  rw [hEC31,hEC9]
  decide +kernel
private theorem pairFlags_8_30_0 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput8.1 earlyInput8.2 earlyInput30.1 earlyInput30.2 false = (List.replicate 20 true) := by
  unfold earlyCompareFlags
  rw [hEC8,hEC30]
  decide +kernel
private theorem pairFlags_6_32_0 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput6.1 earlyInput6.2 earlyInput32.1 earlyInput32.2 false = (List.replicate 16 false) := by
  unfold earlyCompareFlags
  rw [hEC6,hEC32]
  decide +kernel
private theorem pairFlags_33_7_0 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput33.1 earlyInput33.2 earlyInput7.1 earlyInput7.2 false = (List.replicate 4 false) := by
  unfold earlyCompareFlags
  rw [hEC33,hEC7]
  decide +kernel
private theorem pairFlags_33_9_0 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput33.1 earlyInput33.2 earlyInput9.1 earlyInput9.2 false = (List.replicate 16 false) := by
  unfold earlyCompareFlags
  rw [hEC33,hEC9]
  decide +kernel
private theorem pairFlags_8_32_0 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput8.1 earlyInput8.2 earlyInput32.1 earlyInput32.2 false = (List.replicate 16 true) := by
  unfold earlyCompareFlags
  rw [hEC8,hEC32]
  decide +kernel
private theorem pairFlags_3_20_0 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput3.1 earlyInput3.2 earlyInput20.1 earlyInput20.2 false = (List.replicate 20 false) := by
  unfold earlyCompareFlags
  rw [hEC3,hEC20]
  decide +kernel
private theorem pairFlags_19_16_0 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput19.1 earlyInput19.2 earlyInput16.1 earlyInput16.2 false = (List.replicate 20 true) := by
  unfold earlyCompareFlags
  rw [hEC19,hEC16]
  decide +kernel
private theorem pairFlags_3_18_0 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput3.1 earlyInput3.2 earlyInput18.1 earlyInput18.2 false = (List.replicate 25 false) := by
  unfold earlyCompareFlags
  rw [hEC3,hEC18]
  decide +kernel
private theorem pairFlags_17_16_0 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput17.1 earlyInput17.2 earlyInput16.1 earlyInput16.2 false = (List.replicate 25 true) := by
  unfold earlyCompareFlags
  rw [hEC17,hEC16]
  decide +kernel
private theorem pairFlags_34_2_0 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput34.1 earlyInput34.2 earlyInput2.1 earlyInput2.2 false = (List.replicate 4 false) := by
  unfold earlyCompareFlags
  rw [hEC34,hEC2]
  decide +kernel
private theorem pairFlags_35_1_0 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput35.1 earlyInput35.2 earlyInput1.1 earlyInput1.2 false = (List.replicate 16 true) := by
  unfold earlyCompareFlags
  rw [hEC35,hEC1]
  decide +kernel
private theorem pairFlags_36_37_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput36.1 earlyInput36.2 earlyInput37.1 earlyInput37.2 true = (List.replicate 25 false) := by
  unfold earlyCompareFlags
  rw [hEC36,hEC37]
  decide +kernel
private theorem pairFlags_38_39_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput38.1 earlyInput38.2 earlyInput39.1 earlyInput39.2 true = (List.replicate 10 true) := by
  unfold earlyCompareFlags
  rw [hEC38,hEC39]
  decide +kernel
private theorem pairFlags_40_41_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput40.1 earlyInput40.2 earlyInput41.1 earlyInput41.2 true = (List.replicate 10 false) := by
  unfold earlyCompareFlags
  rw [hEC40,hEC41]
  decide +kernel
private theorem pairFlags_42_43_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput42.1 earlyInput42.2 earlyInput43.1 earlyInput43.2 true = (List.replicate 10 true) := by
  unfold earlyCompareFlags
  rw [hEC42,hEC43]
  decide +kernel
private theorem pairFlags_44_45_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput44.1 earlyInput44.2 earlyInput45.1 earlyInput45.2 true = (List.replicate 25 false) := by
  unfold earlyCompareFlags
  rw [hEC44,hEC45]
  decide +kernel
private theorem pairFlags_46_47_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput46.1 earlyInput46.2 earlyInput47.1 earlyInput47.2 true = (List.replicate 10 true) := by
  unfold earlyCompareFlags
  rw [hEC46,hEC47]
  decide +kernel
private theorem pairFlags_48_49_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput48.1 earlyInput48.2 earlyInput49.1 earlyInput49.2 true = (List.replicate 10 false) := by
  unfold earlyCompareFlags
  rw [hEC48,hEC49]
  decide +kernel
private theorem pairFlags_50_51_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput50.1 earlyInput50.2 earlyInput51.1 earlyInput51.2 true = (List.replicate 10 true) := by
  unfold earlyCompareFlags
  rw [hEC50,hEC51]
  decide +kernel
private theorem pairFlags_52_53_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput52.1 earlyInput52.2 earlyInput53.1 earlyInput53.2 true = (List.replicate 25 false) := by
  unfold earlyCompareFlags
  rw [hEC52,hEC53]
  decide +kernel
private theorem pairFlags_54_55_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput54.1 earlyInput54.2 earlyInput55.1 earlyInput55.2 true = (List.replicate 25 true) := by
  unfold earlyCompareFlags
  rw [hEC54,hEC55]
  decide +kernel
private theorem pairFlags_56_57_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput56.1 earlyInput56.2 earlyInput57.1 earlyInput57.2 true = (List.replicate 25 false) := by
  unfold earlyCompareFlags
  rw [hEC56,hEC57]
  decide +kernel
private theorem pairFlags_58_59_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput58.1 earlyInput58.2 earlyInput59.1 earlyInput59.2 true = (List.replicate 25 true) := by
  unfold earlyCompareFlags
  rw [hEC58,hEC59]
  decide +kernel
private theorem pairFlags_60_61_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput60.1 earlyInput60.2 earlyInput61.1 earlyInput61.2 true = (List.replicate 16 false) := by
  unfold earlyCompareFlags
  rw [hEC60,hEC61]
  decide +kernel
private theorem pairFlags_62_63_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput62.1 earlyInput62.2 earlyInput63.1 earlyInput63.2 true = (List.replicate 4 true) := by
  unfold earlyCompareFlags
  rw [hEC62,hEC63]
  decide +kernel
private theorem pairFlags_64_65_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput64.1 earlyInput64.2 earlyInput65.1 earlyInput65.2 true = (List.replicate 4 false) := by
  unfold earlyCompareFlags
  rw [hEC64,hEC65]
  decide +kernel
private theorem pairFlags_66_67_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput66.1 earlyInput66.2 earlyInput67.1 earlyInput67.2 true = (List.replicate 4 true) := by
  unfold earlyCompareFlags
  rw [hEC66,hEC67]
  decide +kernel
private theorem pairFlags_68_69_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput68.1 earlyInput68.2 earlyInput69.1 earlyInput69.2 true = (List.replicate 4 false) := by
  unfold earlyCompareFlags
  rw [hEC68,hEC69]
  decide +kernel
private theorem pairFlags_70_71_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput70.1 earlyInput70.2 earlyInput71.1 earlyInput71.2 true = (List.replicate 1 true) := by
  unfold earlyCompareFlags
  rw [hEC70,hEC71]
  decide +kernel
private theorem pairFlags_72_73_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput72.1 earlyInput72.2 earlyInput73.1 earlyInput73.2 true = (List.replicate 4 false) := by
  unfold earlyCompareFlags
  rw [hEC72,hEC73]
  decide +kernel
private theorem pairFlags_74_75_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput74.1 earlyInput74.2 earlyInput75.1 earlyInput75.2 true = (List.replicate 1 true) := by
  unfold earlyCompareFlags
  rw [hEC74,hEC75]
  decide +kernel
private theorem pairFlags_76_77_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput76.1 earlyInput76.2 earlyInput77.1 earlyInput77.2 true = (List.replicate 16 false) := by
  unfold earlyCompareFlags
  rw [hEC76,hEC77]
  decide +kernel
private theorem pairFlags_78_79_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput78.1 earlyInput78.2 earlyInput79.1 earlyInput79.2 true = (List.replicate 16 true) := by
  unfold earlyCompareFlags
  rw [hEC78,hEC79]
  decide +kernel
private theorem pairFlags_80_81_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput80.1 earlyInput80.2 earlyInput81.1 earlyInput81.2 true = (List.replicate 16 false) := by
  unfold earlyCompareFlags
  rw [hEC80,hEC81]
  decide +kernel
private theorem pairFlags_82_83_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput82.1 earlyInput82.2 earlyInput83.1 earlyInput83.2 true = (List.replicate 16 true) := by
  unfold earlyCompareFlags
  rw [hEC82,hEC83]
  decide +kernel
private theorem pairFlags_84_85_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput84.1 earlyInput84.2 earlyInput85.1 earlyInput85.2 true = (List.replicate 16 false) := by
  unfold earlyCompareFlags
  rw [hEC84,hEC85]
  decide +kernel
private theorem pairFlags_86_87_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput86.1 earlyInput86.2 earlyInput87.1 earlyInput87.2 true = (List.replicate 16 true) := by
  unfold earlyCompareFlags
  rw [hEC86,hEC87]
  decide +kernel
private theorem pairFlags_88_89_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput88.1 earlyInput88.2 earlyInput89.1 earlyInput89.2 true = (List.replicate 16 false) := by
  unfold earlyCompareFlags
  rw [hEC88,hEC89]
  decide +kernel
private theorem pairFlags_90_91_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput90.1 earlyInput90.2 earlyInput91.1 earlyInput91.2 true = (List.replicate 16 true) := by
  unfold earlyCompareFlags
  rw [hEC90,hEC91]
  decide +kernel
private theorem pairFlags_92_93_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput92.1 earlyInput92.2 earlyInput93.1 earlyInput93.2 true = (List.replicate 16 false) := by
  unfold earlyCompareFlags
  rw [hEC92,hEC93]
  decide +kernel
private theorem pairFlags_94_95_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput94.1 earlyInput94.2 earlyInput95.1 earlyInput95.2 true = (List.replicate 16 true) := by
  unfold earlyCompareFlags
  rw [hEC94,hEC95]
  decide +kernel
private theorem pairFlags_96_97_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput96.1 earlyInput96.2 earlyInput97.1 earlyInput97.2 true = (List.replicate 16 false) := by
  unfold earlyCompareFlags
  rw [hEC96,hEC97]
  decide +kernel
private theorem pairFlags_98_99_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput98.1 earlyInput98.2 earlyInput99.1 earlyInput99.2 true = (List.replicate 16 true) := by
  unfold earlyCompareFlags
  rw [hEC98,hEC99]
  decide +kernel
private theorem pairFlags_100_101_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput100.1 earlyInput100.2 earlyInput101.1 earlyInput101.2 true = (List.replicate 25 false) := by
  unfold earlyCompareFlags
  rw [hEC100,hEC101]
  decide +kernel
private theorem pairFlags_102_103_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput102.1 earlyInput102.2 earlyInput103.1 earlyInput103.2 true = (List.replicate 25 true) := by
  unfold earlyCompareFlags
  rw [hEC102,hEC103]
  decide +kernel
private theorem pairFlags_104_105_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput104.1 earlyInput104.2 earlyInput105.1 earlyInput105.2 true = (List.replicate 25 false) := by
  unfold earlyCompareFlags
  rw [hEC104,hEC105]
  decide +kernel
private theorem pairFlags_106_107_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput106.1 earlyInput106.2 earlyInput107.1 earlyInput107.2 true = (List.replicate 25 true) := by
  unfold earlyCompareFlags
  rw [hEC106,hEC107]
  decide +kernel
private theorem pairFlags_108_109_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput108.1 earlyInput108.2 earlyInput109.1 earlyInput109.2 true = (List.replicate 10 false) := by
  unfold earlyCompareFlags
  rw [hEC108,hEC109]
  decide +kernel
private theorem pairFlags_110_111_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput110.1 earlyInput110.2 earlyInput111.1 earlyInput111.2 true = (List.replicate 10 true) := by
  unfold earlyCompareFlags
  rw [hEC110,hEC111]
  decide +kernel
private theorem pairFlags_112_113_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput112.1 earlyInput112.2 earlyInput113.1 earlyInput113.2 true = (List.replicate 25 false) := by
  unfold earlyCompareFlags
  rw [hEC112,hEC113]
  decide +kernel
private theorem pairFlags_114_115_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput114.1 earlyInput114.2 earlyInput115.1 earlyInput115.2 true = (List.replicate 10 true) := by
  unfold earlyCompareFlags
  rw [hEC114,hEC115]
  decide +kernel
private theorem pairFlags_116_117_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput116.1 earlyInput116.2 earlyInput117.1 earlyInput117.2 true = (List.replicate 25 false) := by
  unfold earlyCompareFlags
  rw [hEC116,hEC117]
  decide +kernel
private theorem pairFlags_118_119_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput118.1 earlyInput118.2 earlyInput119.1 earlyInput119.2 true = (List.replicate 25 true) := by
  unfold earlyCompareFlags
  rw [hEC118,hEC119]
  decide +kernel
private theorem pairFlags_120_121_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput120.1 earlyInput120.2 earlyInput121.1 earlyInput121.2 true = (List.replicate 25 false) := by
  unfold earlyCompareFlags
  rw [hEC120,hEC121]
  decide +kernel
private theorem pairFlags_122_123_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput122.1 earlyInput122.2 earlyInput123.1 earlyInput123.2 true = (List.replicate 25 true) := by
  unfold earlyCompareFlags
  rw [hEC122,hEC123]
  decide +kernel
private theorem pairFlags_124_125_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput124.1 earlyInput124.2 earlyInput125.1 earlyInput125.2 true = (List.replicate 25 false) := by
  unfold earlyCompareFlags
  rw [hEC124,hEC125]
  decide +kernel
private theorem pairFlags_126_127_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput126.1 earlyInput126.2 earlyInput127.1 earlyInput127.2 true = (List.replicate 10 true) := by
  unfold earlyCompareFlags
  rw [hEC126,hEC127]
  decide +kernel
private theorem pairFlags_128_129_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput128.1 earlyInput128.2 earlyInput129.1 earlyInput129.2 true = (List.replicate 10 false) := by
  unfold earlyCompareFlags
  rw [hEC128,hEC129]
  decide +kernel
private theorem pairFlags_130_131_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput130.1 earlyInput130.2 earlyInput131.1 earlyInput131.2 true = (List.replicate 10 true) := by
  unfold earlyCompareFlags
  rw [hEC130,hEC131]
  decide +kernel
private theorem pairFlags_132_133_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput132.1 earlyInput132.2 earlyInput133.1 earlyInput133.2 true = (List.replicate 10 false) := by
  unfold earlyCompareFlags
  rw [hEC132,hEC133]
  decide +kernel
private theorem pairFlags_134_135_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput134.1 earlyInput134.2 earlyInput135.1 earlyInput135.2 true = (List.replicate 10 true) := by
  unfold earlyCompareFlags
  rw [hEC134,hEC135]
  decide +kernel
private theorem pairFlags_136_137_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput136.1 earlyInput136.2 earlyInput137.1 earlyInput137.2 true = (List.replicate 25 false) := by
  unfold earlyCompareFlags
  rw [hEC136,hEC137]
  decide +kernel
private theorem pairFlags_138_139_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput138.1 earlyInput138.2 earlyInput139.1 earlyInput139.2 true = (List.replicate 10 true) := by
  unfold earlyCompareFlags
  rw [hEC138,hEC139]
  decide +kernel
private theorem pairFlags_140_141_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput140.1 earlyInput140.2 earlyInput141.1 earlyInput141.2 true = (List.replicate 10 false) := by
  unfold earlyCompareFlags
  rw [hEC140,hEC141]
  decide +kernel
private theorem pairFlags_142_143_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput142.1 earlyInput142.2 earlyInput143.1 earlyInput143.2 true = (List.replicate 10 true) := by
  unfold earlyCompareFlags
  rw [hEC142,hEC143]
  decide +kernel
private theorem pairFlags_144_145_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput144.1 earlyInput144.2 earlyInput145.1 earlyInput145.2 true = (List.replicate 10 false) := by
  unfold earlyCompareFlags
  rw [hEC144,hEC145]
  decide +kernel
private theorem pairFlags_146_147_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput146.1 earlyInput146.2 earlyInput147.1 earlyInput147.2 true = (List.replicate 10 true) := by
  unfold earlyCompareFlags
  rw [hEC146,hEC147]
  decide +kernel
private theorem pairFlags_31_148_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput31.1 earlyInput31.2 earlyInput148.1 earlyInput148.2 true = (List.replicate 25 false) := by
  unfold earlyCompareFlags
  rw [hEC31,hEC148]
  decide +kernel
private theorem pairFlags_149_30_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput149.1 earlyInput149.2 earlyInput30.1 earlyInput30.2 true = (List.replicate 25 true) := by
  unfold earlyCompareFlags
  rw [hEC149,hEC30]
  decide +kernel
private theorem pairFlags_150_151_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput150.1 earlyInput150.2 earlyInput151.1 earlyInput151.2 true = (List.replicate 25 false) := by
  unfold earlyCompareFlags
  rw [hEC150,hEC151]
  decide +kernel
private theorem pairFlags_152_153_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput152.1 earlyInput152.2 earlyInput153.1 earlyInput153.2 true = (List.replicate 25 true) := by
  unfold earlyCompareFlags
  rw [hEC152,hEC153]
  decide +kernel
private theorem pairFlags_154_155_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput154.1 earlyInput154.2 earlyInput155.1 earlyInput155.2 true = (List.replicate 16 false) := by
  unfold earlyCompareFlags
  rw [hEC154,hEC155]
  decide +kernel
private theorem pairFlags_156_157_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput156.1 earlyInput156.2 earlyInput157.1 earlyInput157.2 true = (List.replicate 16 true) := by
  unfold earlyCompareFlags
  rw [hEC156,hEC157]
  decide +kernel
private theorem pairFlags_158_159_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput158.1 earlyInput158.2 earlyInput159.1 earlyInput159.2 true = (List.replicate 16 false) := by
  unfold earlyCompareFlags
  rw [hEC158,hEC159]
  decide +kernel
private theorem pairFlags_160_161_1 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput160.1 earlyInput160.2 earlyInput161.1 earlyInput161.2 true = (List.replicate 16 true) := by
  unfold earlyCompareFlags
  rw [hEC160,hEC161]
  decide +kernel
private theorem pairFlags_33_32_0 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput33.1 earlyInput33.2 earlyInput32.1 earlyInput32.2 false = (List.replicate 16 true) := by
  unfold earlyCompareFlags
  rw [hEC33,hEC32]
  decide +kernel
private theorem pairFlags_31_30_0 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput31.1 earlyInput31.2 earlyInput30.1 earlyInput30.2 false = (List.replicate 25 true) := by
  unfold earlyCompareFlags
  rw [hEC31,hEC30]
  decide +kernel
private theorem pairFlags_34_1_0 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput34.1 earlyInput34.2 earlyInput1.1 earlyInput1.2 false = (List.replicate 4 true) := by
  unfold earlyCompareFlags
  rw [hEC34,hEC1]
  decide +kernel
private theorem pairFlags_35_27_0 : earlyCompareFlags lowerEarlyTerminalTerminal3 earlyInput35.1 earlyInput35.2 earlyInput27.1 earlyInput27.2 false = (List.replicate 16 true) := by
  unfold earlyCompareFlags
  rw [hEC35,hEC27]
  decide +kernel
private def earlyFlags : Array (List Bool) := #[(List.replicate 1 false),(List.replicate 1 false),(List.replicate 4 true),(List.replicate 1 false),(List.replicate 1 false),(List.replicate 4 true),(List.replicate 1 false),(List.replicate 1 false),(List.replicate 16 true),(List.replicate 1 false),(List.replicate 1 false),(List.replicate 10 true),(List.replicate 1 false),(List.replicate 1 false),(List.replicate 4 true),(List.replicate 1 false),(List.replicate 1 false),(List.replicate 25 true),(List.replicate 1 false),(List.replicate 1 false),(List.replicate 25 true),(List.replicate 1 false),(List.replicate 1 false),(List.replicate 25 true),(List.replicate 1 false),(List.replicate 1 false),(List.replicate 16 true),(List.replicate 1 false),(List.replicate 1 false),(List.replicate 4 true),(List.replicate 1 false),(List.replicate 1 false),(List.replicate 16 true),(List.replicate 1 false),(List.replicate 1 false),(List.replicate 4 true),(List.replicate 1 false),(List.replicate 1 false),(List.replicate 4 true),(List.replicate 4 false),(List.replicate 4 false),(List.replicate 4 false),(List.replicate 4 true),(List.replicate 8 false),(List.replicate 20 false),(List.replicate 10 false),(List.replicate 4 true),(List.replicate 10 false),(List.replicate 10 false),(List.replicate 25 false),(List.replicate 25 false),(List.replicate 20 false),(List.replicate 20 false),(List.replicate 16 false),(List.replicate 4 true),(List.replicate 4 false),(List.replicate 16 false),(List.replicate 16 false),(List.replicate 4 true),(List.replicate 4 false),(List.replicate 4 false),(List.replicate 1 false),(List.replicate 1 false),(List.replicate 20 false),(List.replicate 5 false),(List.replicate 20 false),(List.replicate 20 true),(List.replicate 1 false),(List.replicate 1 false),(List.replicate 16 false),(List.replicate 4 false),(List.replicate 16 false),(List.replicate 16 true),(List.replicate 20 false),(List.replicate 20 true),(List.replicate 25 false),(List.replicate 25 true),(List.replicate 1 false),(List.replicate 1 false),(List.replicate 4 false),(List.replicate 16 true),(List.replicate 1 false),(List.replicate 1 false),(List.replicate 1 false),(List.replicate 1 false),(List.replicate 1 false),(List.replicate 1 false),(List.replicate 1 false),(List.replicate 1 false),(List.replicate 1 false),(List.replicate 1 false),(List.replicate 1 false),(List.replicate 1 false),(List.replicate 1 false),(List.replicate 1 false),(List.replicate 1 false),(List.replicate 1 false),(List.replicate 25 false),(List.replicate 10 true),(List.replicate 10 false),(List.replicate 10 true),(List.replicate 25 false),(List.replicate 10 true),(List.replicate 10 false),(List.replicate 10 true),(List.replicate 25 false),(List.replicate 25 true),(List.replicate 25 false),(List.replicate 25 true),(List.replicate 16 false),(List.replicate 4 true),(List.replicate 4 false),(List.replicate 4 true),(List.replicate 4 false),(List.replicate 1 true),(List.replicate 4 false),(List.replicate 1 true),(List.replicate 16 false),(List.replicate 16 true),(List.replicate 16 false),(List.replicate 16 true),(List.replicate 16 false),(List.replicate 16 true),(List.replicate 16 false),(List.replicate 16 true),(List.replicate 16 false),(List.replicate 16 true),(List.replicate 16 false),(List.replicate 16 true),(List.replicate 25 false),(List.replicate 25 true),(List.replicate 25 false),(List.replicate 25 true),(List.replicate 10 false),(List.replicate 10 true),(List.replicate 25 false),(List.replicate 10 true),(List.replicate 25 false),(List.replicate 25 true),(List.replicate 25 false),(List.replicate 25 true),(List.replicate 25 false),(List.replicate 10 true),(List.replicate 10 false),(List.replicate 10 true),(List.replicate 10 false),(List.replicate 10 true),(List.replicate 25 false),(List.replicate 10 true),(List.replicate 10 false),(List.replicate 10 true),(List.replicate 10 false),(List.replicate 10 true),(List.replicate 25 false),(List.replicate 25 true),(List.replicate 25 false),(List.replicate 25 true),(List.replicate 16 false),(List.replicate 16 true),(List.replicate 16 false),(List.replicate 16 true),(List.replicate 1 false),(List.replicate 1 false),(List.replicate 1 false),(List.replicate 16 true),(List.replicate 25 true),(List.replicate 4 true),(List.replicate 16 true)]
private def earlyBuckets : Array (List ℕ) := #[[0],[0],[],[0],[0],[],[0],[0],[],[0],[0],[],[0],[0],[],[0],[0],[],[0],[0],[],[0],[0],[],[0],[0],[],[0],[0],[],[0],[0],[],[0],[0],[],[0],[0],[],[0,1,2,3],[0,1,2,3],[0,1,2,3],[],[0,1,2,3,4,5,6,7],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19],[0,1,2,3,4,5,6,7,8,9],[],[0,1,2,3,4,5,6,7,8,9],[0,1,2,3,4,5,6,7,8,9],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[],[0,1,2,3],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[],[0,1,2,3],[0,1,2,3],[0],[0],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19],[0,1,2,3,4],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19],[],[0],[0],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[0,1,2,3],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24],[],[0],[0],[0,1,2,3],[],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24],[],[0,1,2,3,4,5,6,7,8,9],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24],[],[0,1,2,3,4,5,6,7,8,9],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[],[0,1,2,3],[],[0,1,2,3],[],[0,1,2,3],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24],[],[0,1,2,3,4,5,6,7,8,9],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24],[],[0,1,2,3,4,5,6,7,8,9],[],[0,1,2,3,4,5,6,7,8,9],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24],[],[0,1,2,3,4,5,6,7,8,9],[],[0,1,2,3,4,5,6,7,8,9],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[],[0],[0],[0],[],[],[],[]]
private theorem hEF0 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 0).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[0]?.getD [] := by
  decide +kernel
private theorem hEF1 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 1).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[1]?.getD [] := by
  decide +kernel
private theorem hEF2 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 2).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[2]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 2).kind = .compare earlyInput4.1 earlyInput4.2 earlyInput5.1 earlyInput5.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_4_5_0
private theorem hEF3 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 3).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[3]?.getD [] := by
  decide +kernel
private theorem hEF4 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 4).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[4]?.getD [] := by
  decide +kernel
private theorem hEF5 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 5).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[5]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 5).kind = .compare earlyInput6.1 earlyInput6.2 earlyInput7.1 earlyInput7.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_6_7_0
private theorem hEF6 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 6).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[6]?.getD [] := by
  decide +kernel
private theorem hEF7 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 7).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[7]?.getD [] := by
  decide +kernel
private theorem hEF8 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 8).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[8]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 8).kind = .compare earlyInput8.1 earlyInput8.2 earlyInput9.1 earlyInput9.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_8_9_0
private theorem hEF9 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 9).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[9]?.getD [] := by
  decide +kernel
private theorem hEF10 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 10).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[10]?.getD [] := by
  decide +kernel
private theorem hEF11 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 11).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[11]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 11).kind = .compare earlyInput10.1 earlyInput10.2 earlyInput11.1 earlyInput11.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_10_11_0
private theorem hEF12 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 12).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[12]?.getD [] := by
  decide +kernel
private theorem hEF13 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 13).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[13]?.getD [] := by
  decide +kernel
private theorem hEF14 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 14).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[14]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 14).kind = .compare earlyInput12.1 earlyInput12.2 earlyInput13.1 earlyInput13.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_12_13_0
private theorem hEF15 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 15).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[15]?.getD [] := by
  decide +kernel
private theorem hEF16 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 16).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[16]?.getD [] := by
  decide +kernel
private theorem hEF17 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 17).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[17]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 17).kind = .compare earlyInput14.1 earlyInput14.2 earlyInput15.1 earlyInput15.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_14_15_0
private theorem hEF18 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 18).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[18]?.getD [] := by
  decide +kernel
private theorem hEF19 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 19).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[19]?.getD [] := by
  decide +kernel
private theorem hEF20 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 20).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[20]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 20).kind = .compare earlyInput3.1 earlyInput3.2 earlyInput16.1 earlyInput16.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_3_16_0
private theorem hEF21 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 21).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[21]?.getD [] := by
  decide +kernel
private theorem hEF22 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 22).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[22]?.getD [] := by
  decide +kernel
private theorem hEF23 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 23).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[23]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 23).kind = .compare earlyInput17.1 earlyInput17.2 earlyInput18.1 earlyInput18.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_17_18_0
private theorem hEF24 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 24).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[24]?.getD [] := by
  decide +kernel
private theorem hEF25 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 25).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[25]?.getD [] := by
  decide +kernel
private theorem hEF26 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 26).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[26]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 26).kind = .compare earlyInput19.1 earlyInput19.2 earlyInput20.1 earlyInput20.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_19_20_0
private theorem hEF27 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 27).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[27]?.getD [] := by
  decide +kernel
private theorem hEF28 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 28).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[28]?.getD [] := by
  decide +kernel
private theorem hEF29 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 29).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[29]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 29).kind = .compare earlyInput21.1 earlyInput21.2 earlyInput22.1 earlyInput22.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_21_22_0
private theorem hEF30 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 30).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[30]?.getD [] := by
  decide +kernel
private theorem hEF31 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 31).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[31]?.getD [] := by
  decide +kernel
private theorem hEF32 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 32).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[32]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 32).kind = .compare earlyInput23.1 earlyInput23.2 earlyInput24.1 earlyInput24.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_23_24_0
private theorem hEF33 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 33).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[33]?.getD [] := by
  decide +kernel
private theorem hEF34 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 34).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[34]?.getD [] := by
  decide +kernel
private theorem hEF35 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 35).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[35]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 35).kind = .compare earlyInput25.1 earlyInput25.2 earlyInput26.1 earlyInput26.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_25_26_0
private theorem hEF36 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 36).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[36]?.getD [] := by
  decide +kernel
private theorem hEF37 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 37).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[37]?.getD [] := by
  decide +kernel
private theorem hEF38 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 38).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[38]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 38).kind = .compare earlyInput0.1 earlyInput0.2 earlyInput27.1 earlyInput27.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_0_27_0
private theorem hEF39 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 39).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[39]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 39).kind = .compare earlyInput28.1 earlyInput28.2 earlyInput5.1 earlyInput5.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_28_5_0
private theorem hEF40 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 40).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[40]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 40).kind = .compare earlyInput4.1 earlyInput4.2 earlyInput29.1 earlyInput29.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_4_29_0
private theorem hEF41 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 41).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[41]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 41).kind = .compare earlyInput4.1 earlyInput4.2 earlyInput7.1 earlyInput7.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_4_7_0
private theorem hEF42 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 42).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[42]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 42).kind = .compare earlyInput6.1 earlyInput6.2 earlyInput5.1 earlyInput5.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_6_5_0
private theorem hEF43 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 43).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[43]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 43).kind = .compare earlyInput8.1 earlyInput8.2 earlyInput11.1 earlyInput11.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_8_11_0
private theorem hEF44 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 44).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[44]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 44).kind = .compare earlyInput10.1 earlyInput10.2 earlyInput9.1 earlyInput9.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_10_9_0
private theorem hEF45 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 45).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[45]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 45).kind = .compare earlyInput10.1 earlyInput10.2 earlyInput13.1 earlyInput13.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_10_13_0
private theorem hEF46 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 46).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[46]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 46).kind = .compare earlyInput12.1 earlyInput12.2 earlyInput11.1 earlyInput11.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_12_11_0
private theorem hEF47 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 47).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[47]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 47).kind = .compare earlyInput12.1 earlyInput12.2 earlyInput15.1 earlyInput15.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_12_15_0
private theorem hEF48 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 48).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[48]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 48).kind = .compare earlyInput14.1 earlyInput14.2 earlyInput13.1 earlyInput13.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_14_13_0
private theorem hEF49 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 49).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[49]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 49).kind = .compare earlyInput14.1 earlyInput14.2 earlyInput16.1 earlyInput16.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_14_16_0
private theorem hEF50 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 50).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[50]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 50).kind = .compare earlyInput3.1 earlyInput3.2 earlyInput15.1 earlyInput15.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_3_15_0
private theorem hEF51 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 51).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[51]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 51).kind = .compare earlyInput17.1 earlyInput17.2 earlyInput20.1 earlyInput20.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_17_20_0
private theorem hEF52 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 52).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[52]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 52).kind = .compare earlyInput19.1 earlyInput19.2 earlyInput18.1 earlyInput18.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_19_18_0
private theorem hEF53 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 53).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[53]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 53).kind = .compare earlyInput19.1 earlyInput19.2 earlyInput22.1 earlyInput22.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_19_22_0
private theorem hEF54 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 54).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[54]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 54).kind = .compare earlyInput21.1 earlyInput21.2 earlyInput20.1 earlyInput20.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_21_20_0
private theorem hEF55 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 55).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[55]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 55).kind = .compare earlyInput21.1 earlyInput21.2 earlyInput24.1 earlyInput24.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_21_24_0
private theorem hEF56 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 56).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[56]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 56).kind = .compare earlyInput23.1 earlyInput23.2 earlyInput22.1 earlyInput22.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_23_22_0
private theorem hEF57 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 57).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[57]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 57).kind = .compare earlyInput23.1 earlyInput23.2 earlyInput26.1 earlyInput26.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_23_26_0
private theorem hEF58 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 58).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[58]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 58).kind = .compare earlyInput25.1 earlyInput25.2 earlyInput24.1 earlyInput24.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_25_24_0
private theorem hEF59 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 59).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[59]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 59).kind = .compare earlyInput25.1 earlyInput25.2 earlyInput27.1 earlyInput27.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_25_27_0
private theorem hEF60 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 60).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[60]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 60).kind = .compare earlyInput0.1 earlyInput0.2 earlyInput26.1 earlyInput26.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_0_26_0
private theorem hEF61 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 61).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[61]?.getD [] := by
  decide +kernel
private theorem hEF62 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 62).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[62]?.getD [] := by
  decide +kernel
private theorem hEF63 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 63).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[63]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 63).kind = .compare earlyInput6.1 earlyInput6.2 earlyInput30.1 earlyInput30.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_6_30_0
private theorem hEF64 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 64).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[64]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 64).kind = .compare earlyInput31.1 earlyInput31.2 earlyInput7.1 earlyInput7.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_31_7_0
private theorem hEF65 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 65).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[65]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 65).kind = .compare earlyInput31.1 earlyInput31.2 earlyInput9.1 earlyInput9.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_31_9_0
private theorem hEF66 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 66).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[66]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 66).kind = .compare earlyInput8.1 earlyInput8.2 earlyInput30.1 earlyInput30.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_8_30_0
private theorem hEF67 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 67).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[67]?.getD [] := by
  decide +kernel
private theorem hEF68 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 68).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[68]?.getD [] := by
  decide +kernel
private theorem hEF69 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 69).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[69]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 69).kind = .compare earlyInput6.1 earlyInput6.2 earlyInput32.1 earlyInput32.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_6_32_0
private theorem hEF70 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 70).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[70]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 70).kind = .compare earlyInput33.1 earlyInput33.2 earlyInput7.1 earlyInput7.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_33_7_0
private theorem hEF71 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 71).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[71]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 71).kind = .compare earlyInput33.1 earlyInput33.2 earlyInput9.1 earlyInput9.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_33_9_0
private theorem hEF72 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 72).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[72]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 72).kind = .compare earlyInput8.1 earlyInput8.2 earlyInput32.1 earlyInput32.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_8_32_0
private theorem hEF73 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 73).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[73]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 73).kind = .compare earlyInput3.1 earlyInput3.2 earlyInput20.1 earlyInput20.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_3_20_0
private theorem hEF74 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 74).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[74]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 74).kind = .compare earlyInput19.1 earlyInput19.2 earlyInput16.1 earlyInput16.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_19_16_0
private theorem hEF75 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 75).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[75]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 75).kind = .compare earlyInput3.1 earlyInput3.2 earlyInput18.1 earlyInput18.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_3_18_0
private theorem hEF76 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 76).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[76]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 76).kind = .compare earlyInput17.1 earlyInput17.2 earlyInput16.1 earlyInput16.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_17_16_0
private theorem hEF77 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 77).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[77]?.getD [] := by
  decide +kernel
private theorem hEF78 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 78).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[78]?.getD [] := by
  decide +kernel
private theorem hEF79 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 79).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[79]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 79).kind = .compare earlyInput34.1 earlyInput34.2 earlyInput2.1 earlyInput2.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_34_2_0
private theorem hEF80 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 80).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[80]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 80).kind = .compare earlyInput35.1 earlyInput35.2 earlyInput1.1 earlyInput1.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_35_1_0
private theorem hEF81 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 81).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[81]?.getD [] := by
  decide +kernel
private theorem hEF82 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 82).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[82]?.getD [] := by
  decide +kernel
private theorem hEF83 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 83).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[83]?.getD [] := by
  decide +kernel
private theorem hEF84 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 84).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[84]?.getD [] := by
  decide +kernel
private theorem hEF85 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 85).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[85]?.getD [] := by
  decide +kernel
private theorem hEF86 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 86).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[86]?.getD [] := by
  decide +kernel
private theorem hEF87 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 87).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[87]?.getD [] := by
  decide +kernel
private theorem hEF88 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 88).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[88]?.getD [] := by
  decide +kernel
private theorem hEF89 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 89).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[89]?.getD [] := by
  decide +kernel
private theorem hEF90 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 90).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[90]?.getD [] := by
  decide +kernel
private theorem hEF91 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 91).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[91]?.getD [] := by
  decide +kernel
private theorem hEF92 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 92).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[92]?.getD [] := by
  decide +kernel
private theorem hEF93 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 93).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[93]?.getD [] := by
  decide +kernel
private theorem hEF94 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 94).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[94]?.getD [] := by
  decide +kernel
private theorem hEF95 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 95).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[95]?.getD [] := by
  decide +kernel
private theorem hEF96 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 96).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[96]?.getD [] := by
  decide +kernel
private theorem hEF97 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 97).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[97]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 97).kind = .compare earlyInput36.1 earlyInput36.2 earlyInput37.1 earlyInput37.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_36_37_1
private theorem hEF98 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 98).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[98]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 98).kind = .compare earlyInput38.1 earlyInput38.2 earlyInput39.1 earlyInput39.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_38_39_1
private theorem hEF99 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 99).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[99]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 99).kind = .compare earlyInput40.1 earlyInput40.2 earlyInput41.1 earlyInput41.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_40_41_1
private theorem hEF100 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 100).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[100]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 100).kind = .compare earlyInput42.1 earlyInput42.2 earlyInput43.1 earlyInput43.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_42_43_1
private theorem hEF101 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 101).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[101]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 101).kind = .compare earlyInput44.1 earlyInput44.2 earlyInput45.1 earlyInput45.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_44_45_1
private theorem hEF102 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 102).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[102]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 102).kind = .compare earlyInput46.1 earlyInput46.2 earlyInput47.1 earlyInput47.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_46_47_1
private theorem hEF103 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 103).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[103]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 103).kind = .compare earlyInput48.1 earlyInput48.2 earlyInput49.1 earlyInput49.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_48_49_1
private theorem hEF104 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 104).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[104]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 104).kind = .compare earlyInput50.1 earlyInput50.2 earlyInput51.1 earlyInput51.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_50_51_1
private theorem hEF105 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 105).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[105]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 105).kind = .compare earlyInput52.1 earlyInput52.2 earlyInput53.1 earlyInput53.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_52_53_1
private theorem hEF106 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 106).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[106]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 106).kind = .compare earlyInput54.1 earlyInput54.2 earlyInput55.1 earlyInput55.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_54_55_1
private theorem hEF107 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 107).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[107]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 107).kind = .compare earlyInput56.1 earlyInput56.2 earlyInput57.1 earlyInput57.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_56_57_1
private theorem hEF108 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 108).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[108]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 108).kind = .compare earlyInput58.1 earlyInput58.2 earlyInput59.1 earlyInput59.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_58_59_1
private theorem hEF109 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 109).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[109]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 109).kind = .compare earlyInput60.1 earlyInput60.2 earlyInput61.1 earlyInput61.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_60_61_1
private theorem hEF110 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 110).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[110]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 110).kind = .compare earlyInput62.1 earlyInput62.2 earlyInput63.1 earlyInput63.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_62_63_1
private theorem hEF111 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 111).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[111]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 111).kind = .compare earlyInput64.1 earlyInput64.2 earlyInput65.1 earlyInput65.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_64_65_1
private theorem hEF112 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 112).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[112]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 112).kind = .compare earlyInput66.1 earlyInput66.2 earlyInput67.1 earlyInput67.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_66_67_1
private theorem hEF113 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 113).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[113]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 113).kind = .compare earlyInput68.1 earlyInput68.2 earlyInput69.1 earlyInput69.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_68_69_1
private theorem hEF114 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 114).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[114]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 114).kind = .compare earlyInput70.1 earlyInput70.2 earlyInput71.1 earlyInput71.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_70_71_1
private theorem hEF115 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 115).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[115]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 115).kind = .compare earlyInput72.1 earlyInput72.2 earlyInput73.1 earlyInput73.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_72_73_1
private theorem hEF116 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 116).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[116]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 116).kind = .compare earlyInput74.1 earlyInput74.2 earlyInput75.1 earlyInput75.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_74_75_1
private theorem hEF117 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 117).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[117]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 117).kind = .compare earlyInput76.1 earlyInput76.2 earlyInput77.1 earlyInput77.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_76_77_1
private theorem hEF118 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 118).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[118]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 118).kind = .compare earlyInput78.1 earlyInput78.2 earlyInput79.1 earlyInput79.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_78_79_1
private theorem hEF119 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 119).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[119]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 119).kind = .compare earlyInput80.1 earlyInput80.2 earlyInput81.1 earlyInput81.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_80_81_1
private theorem hEF120 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 120).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[120]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 120).kind = .compare earlyInput82.1 earlyInput82.2 earlyInput83.1 earlyInput83.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_82_83_1
private theorem hEF121 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 121).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[121]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 121).kind = .compare earlyInput84.1 earlyInput84.2 earlyInput85.1 earlyInput85.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_84_85_1
private theorem hEF122 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 122).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[122]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 122).kind = .compare earlyInput86.1 earlyInput86.2 earlyInput87.1 earlyInput87.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_86_87_1
private theorem hEF123 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 123).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[123]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 123).kind = .compare earlyInput88.1 earlyInput88.2 earlyInput89.1 earlyInput89.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_88_89_1
private theorem hEF124 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 124).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[124]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 124).kind = .compare earlyInput90.1 earlyInput90.2 earlyInput91.1 earlyInput91.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_90_91_1
private theorem hEF125 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 125).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[125]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 125).kind = .compare earlyInput92.1 earlyInput92.2 earlyInput93.1 earlyInput93.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_92_93_1
private theorem hEF126 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 126).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[126]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 126).kind = .compare earlyInput94.1 earlyInput94.2 earlyInput95.1 earlyInput95.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_94_95_1
private theorem hEF127 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 127).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[127]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 127).kind = .compare earlyInput96.1 earlyInput96.2 earlyInput97.1 earlyInput97.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_96_97_1
private theorem hEF128 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 128).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[128]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 128).kind = .compare earlyInput98.1 earlyInput98.2 earlyInput99.1 earlyInput99.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_98_99_1
private theorem hEF129 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 129).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[129]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 129).kind = .compare earlyInput100.1 earlyInput100.2 earlyInput101.1 earlyInput101.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_100_101_1
private theorem hEF130 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 130).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[130]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 130).kind = .compare earlyInput102.1 earlyInput102.2 earlyInput103.1 earlyInput103.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_102_103_1
private theorem hEF131 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 131).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[131]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 131).kind = .compare earlyInput104.1 earlyInput104.2 earlyInput105.1 earlyInput105.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_104_105_1
private theorem hEF132 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 132).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[132]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 132).kind = .compare earlyInput106.1 earlyInput106.2 earlyInput107.1 earlyInput107.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_106_107_1
private theorem hEF133 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 133).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[133]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 133).kind = .compare earlyInput108.1 earlyInput108.2 earlyInput109.1 earlyInput109.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_108_109_1
private theorem hEF134 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 134).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[134]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 134).kind = .compare earlyInput110.1 earlyInput110.2 earlyInput111.1 earlyInput111.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_110_111_1
private theorem hEF135 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 135).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[135]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 135).kind = .compare earlyInput112.1 earlyInput112.2 earlyInput113.1 earlyInput113.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_112_113_1
private theorem hEF136 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 136).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[136]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 136).kind = .compare earlyInput114.1 earlyInput114.2 earlyInput115.1 earlyInput115.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_114_115_1
private theorem hEF137 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 137).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[137]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 137).kind = .compare earlyInput116.1 earlyInput116.2 earlyInput117.1 earlyInput117.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_116_117_1
private theorem hEF138 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 138).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[138]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 138).kind = .compare earlyInput118.1 earlyInput118.2 earlyInput119.1 earlyInput119.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_118_119_1
private theorem hEF139 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 139).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[139]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 139).kind = .compare earlyInput120.1 earlyInput120.2 earlyInput121.1 earlyInput121.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_120_121_1
private theorem hEF140 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 140).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[140]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 140).kind = .compare earlyInput122.1 earlyInput122.2 earlyInput123.1 earlyInput123.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_122_123_1
private theorem hEF141 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 141).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[141]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 141).kind = .compare earlyInput124.1 earlyInput124.2 earlyInput125.1 earlyInput125.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_124_125_1
private theorem hEF142 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 142).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[142]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 142).kind = .compare earlyInput126.1 earlyInput126.2 earlyInput127.1 earlyInput127.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_126_127_1
private theorem hEF143 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 143).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[143]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 143).kind = .compare earlyInput128.1 earlyInput128.2 earlyInput129.1 earlyInput129.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_128_129_1
private theorem hEF144 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 144).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[144]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 144).kind = .compare earlyInput130.1 earlyInput130.2 earlyInput131.1 earlyInput131.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_130_131_1
private theorem hEF145 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 145).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[145]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 145).kind = .compare earlyInput132.1 earlyInput132.2 earlyInput133.1 earlyInput133.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_132_133_1
private theorem hEF146 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 146).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[146]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 146).kind = .compare earlyInput134.1 earlyInput134.2 earlyInput135.1 earlyInput135.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_134_135_1
private theorem hEF147 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 147).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[147]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 147).kind = .compare earlyInput136.1 earlyInput136.2 earlyInput137.1 earlyInput137.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_136_137_1
private theorem hEF148 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 148).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[148]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 148).kind = .compare earlyInput138.1 earlyInput138.2 earlyInput139.1 earlyInput139.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_138_139_1
private theorem hEF149 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 149).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[149]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 149).kind = .compare earlyInput140.1 earlyInput140.2 earlyInput141.1 earlyInput141.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_140_141_1
private theorem hEF150 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 150).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[150]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 150).kind = .compare earlyInput142.1 earlyInput142.2 earlyInput143.1 earlyInput143.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_142_143_1
private theorem hEF151 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 151).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[151]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 151).kind = .compare earlyInput144.1 earlyInput144.2 earlyInput145.1 earlyInput145.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_144_145_1
private theorem hEF152 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 152).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[152]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 152).kind = .compare earlyInput146.1 earlyInput146.2 earlyInput147.1 earlyInput147.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_146_147_1
private theorem hEF153 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 153).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[153]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 153).kind = .compare earlyInput31.1 earlyInput31.2 earlyInput148.1 earlyInput148.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_31_148_1
private theorem hEF154 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 154).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[154]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 154).kind = .compare earlyInput149.1 earlyInput149.2 earlyInput30.1 earlyInput30.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_149_30_1
private theorem hEF155 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 155).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[155]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 155).kind = .compare earlyInput150.1 earlyInput150.2 earlyInput151.1 earlyInput151.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_150_151_1
private theorem hEF156 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 156).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[156]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 156).kind = .compare earlyInput152.1 earlyInput152.2 earlyInput153.1 earlyInput153.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_152_153_1
private theorem hEF157 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 157).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[157]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 157).kind = .compare earlyInput154.1 earlyInput154.2 earlyInput155.1 earlyInput155.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_154_155_1
private theorem hEF158 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 158).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[158]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 158).kind = .compare earlyInput156.1 earlyInput156.2 earlyInput157.1 earlyInput157.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_156_157_1
private theorem hEF159 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 159).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[159]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 159).kind = .compare earlyInput158.1 earlyInput158.2 earlyInput159.1 earlyInput159.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_158_159_1
private theorem hEF160 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 160).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[160]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 160).kind = .compare earlyInput160.1 earlyInput160.2 earlyInput161.1 earlyInput161.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_160_161_1
private theorem hEF161 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 161).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[161]?.getD [] := by
  decide +kernel
private theorem hEF162 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 162).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[162]?.getD [] := by
  decide +kernel
private theorem hEF163 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 163).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[163]?.getD [] := by
  decide +kernel
private theorem hEF164 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 164).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[164]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 164).kind = .compare earlyInput33.1 earlyInput33.2 earlyInput32.1 earlyInput32.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_33_32_0
private theorem hEF165 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 165).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[165]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 165).kind = .compare earlyInput31.1 earlyInput31.2 earlyInput30.1 earlyInput30.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_31_30_0
private theorem hEF166 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 166).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[166]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 166).kind = .compare earlyInput34.1 earlyInput34.2 earlyInput1.1 earlyInput1.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_34_1_0
private theorem hEF167 : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 167).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[167]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 167).kind = .compare earlyInput35.1 earlyInput35.2 earlyInput27.1 earlyInput27.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_35_27_0
private theorem earlyLength : lowerEarlyTerminalTerminal3.goals.length = 168 := by decide +kernel
private theorem hEFlags (g : ℕ) (hg : g<168) : (lowerEarlyTerminalBranches lowerEarlyTerminalTerminal3 (lowerEarlyTerminalGoal lowerEarlyTerminalTerminal3 g).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[g]?.getD [] := by
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
  · exact hEF60
  · exact hEF61
  · exact hEF62
  · exact hEF63
  · exact hEF64
  · exact hEF65
  · exact hEF66
  · exact hEF67
  · exact hEF68
  · exact hEF69
  · exact hEF70
  · exact hEF71
  · exact hEF72
  · exact hEF73
  · exact hEF74
  · exact hEF75
  · exact hEF76
  · exact hEF77
  · exact hEF78
  · exact hEF79
  · exact hEF80
  · exact hEF81
  · exact hEF82
  · exact hEF83
  · exact hEF84
  · exact hEF85
  · exact hEF86
  · exact hEF87
  · exact hEF88
  · exact hEF89
  · exact hEF90
  · exact hEF91
  · exact hEF92
  · exact hEF93
  · exact hEF94
  · exact hEF95
  · exact hEF96
  · exact hEF97
  · exact hEF98
  · exact hEF99
  · exact hEF100
  · exact hEF101
  · exact hEF102
  · exact hEF103
  · exact hEF104
  · exact hEF105
  · exact hEF106
  · exact hEF107
  · exact hEF108
  · exact hEF109
  · exact hEF110
  · exact hEF111
  · exact hEF112
  · exact hEF113
  · exact hEF114
  · exact hEF115
  · exact hEF116
  · exact hEF117
  · exact hEF118
  · exact hEF119
  · exact hEF120
  · exact hEF121
  · exact hEF122
  · exact hEF123
  · exact hEF124
  · exact hEF125
  · exact hEF126
  · exact hEF127
  · exact hEF128
  · exact hEF129
  · exact hEF130
  · exact hEF131
  · exact hEF132
  · exact hEF133
  · exact hEF134
  · exact hEF135
  · exact hEF136
  · exact hEF137
  · exact hEF138
  · exact hEF139
  · exact hEF140
  · exact hEF141
  · exact hEF142
  · exact hEF143
  · exact hEF144
  · exact hEF145
  · exact hEF146
  · exact hEF147
  · exact hEF148
  · exact hEF149
  · exact hEF150
  · exact hEF151
  · exact hEF152
  · exact hEF153
  · exact hEF154
  · exact hEF155
  · exact hEF156
  · exact hEF157
  · exact hEF158
  · exact hEF159
  · exact hEF160
  · exact hEF161
  · exact hEF162
  · exact hEF163
  · exact hEF164
  · exact hEF165
  · exact hEF166
  · exact hEF167
private theorem hEBuckets : earlyRecordKeys lowerEarlyTerminalTerminal3 = earlyBucketKeys 168 earlyBuckets := by decide +kernel
private theorem hECovered : ∀ g ∈ List.range 168, ∀ bj ∈ (earlyFlags[g]?.getD []).zipIdx, bj.1=true ∨ bj.2 ∈ earlyBuckets[g]?.getD [] := by decide +kernel

theorem solution : lowerEarlyTerminalCoverage lowerEarlyTerminalTerminal3 :=
  earlyCoverageGrouped_sound _ 168 earlyFlags earlyBuckets earlyLength hEFlags hEBuckets hECovered
#print axioms solution
