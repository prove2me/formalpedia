-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_state2_coverage
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T13:19:55.704689+00:00
-- url     : https://prove2.me/submissions/00c24a30-845e-4f79-a268-0b17f2134521

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
private def earlyFields : Array CertField := #[⟨(553/1429),(1/1429),(0/1),(0/1)⟩,⟨(3289/10753),(1/10753),(0/1),(0/1)⟩,⟨(278/709),(-1/709),(0/1),(0/1)⟩,⟨(71/229),(-1/229),(0/1),(0/1)⟩,⟨(1413/4654),(-1/4654),(0/1),(0/1)⟩,⟨(1929/4946),(-1/14838),(0/1),(0/1)⟩,⟨(15/37),(-1/37),(0/1),(0/1)⟩,⟨(66/179),(-1/537),(0/1),(0/1)⟩,⟨(247/649),(1/649),(0/1),(0/1)⟩,⟨(16/59),(1/177),(0/1),(0/1)⟩,⟨(767/2749),(1/2749),(0/1),(0/1)⟩,⟨(3734/9757),(1/9757),(0/1),(0/1)⟩,⟨(89/214),(1/214),(0/1),(0/1)⟩,⟨(1272/3013),(1/3013),(0/1),(0/1)⟩,⟨(10/23),(-1/69),(0/1),(0/1)⟩,⟨(133/478),(-1/478),(0/1),(0/1)⟩,⟨(1950/7081),(-1/7081),(0/1),(0/1)⟩,⟨(517/1249),(-1/1249),(0/1),(0/1)⟩,⟨(7298/17677),(-1/17677),(0/1),(0/1)⟩,⟨(168/409),(1/409),(0/1),(0/1)⟩,⟨(1005/2426),(1/7278),(0/1),(0/1)⟩,⟨(223/529),(-1/529),(0/1),(0/1)⟩,⟨(1137/2714),(-1/8142),(0/1),(0/1)⟩,⟨(341/1237),(1/1237),(0/1),(0/1)⟩,⟨(1721/6218),(1/18654),(0/1),(0/1)⟩,⟨(246/877),(-1/877),(0/1),(0/1)⟩,⟨(1493/5354),(-1/16062),(0/1),(0/1)⟩,⟨(10780/38569),(1/38569),(0/1),(0/1)⟩,⟨(42/143),(1/429),(0/1),(0/1)⟩,⟨(1809/6094),(1/6094),(0/1),(0/1)⟩,⟨(43/142),(-1/142),(0/1),(0/1)⟩,⟨(731/2497),(-1/2497),(0/1),(0/1)⟩,⟨(3437/11762),(-1/35286),(0/1),(0/1)⟩,⟨(237/814),(1/814),(0/1),(0/1)⟩,⟨(4264/14557),(1/14557),(0/1),(0/1)⟩,⟨(317/1069),(-1/1069),(0/1),(0/1)⟩,⟨(4840/16393),(-1/16393),(0/1),(0/1)⟩,⟨(5/22),(1/22),(0/1),(0/1)⟩,⟨(4/13),(1/13),(0/1),(0/1)⟩,⟨(271/1006),(-1/1006),(0/1),(0/1)⟩,⟨(35/94),(1/94),(0/1),(0/1)⟩,⟨(32/83),(-1/249),(0/1),(0/1)⟩,⟨(1413/3718),(-1/3718),(0/1),(0/1)⟩,⟨(177/454),(-1/454),(0/1),(0/1)⟩,⟨(3230/8353),(-1/8353),(0/1),(0/1)⟩,⟨(2589/6674),(1/20022),(0/1),(0/1)⟩,⟨(45733/118318),(-1/118318),(0/1),(0/1)⟩,⟨(353/914),(1/2742),(0/1),(0/1)⟩,⟨(1364/3517),(-1/3517),(0/1),(0/1)⟩,⟨(21015/54241),(-1/54241),(0/1),(0/1)⟩,⟨(6697/22079),(-1/66237),(0/1),(0/1)⟩,⟨(469/1549),(1/1549),(0/1),(0/1)⟩,⟨(8222/27073),(1/27073),(0/1),(0/1)⟩,⟨(579/1894),(-1/1894),(0/1),(0/1)⟩,⟨(9014/29557),(-1/29557),(0/1),(0/1)⟩,⟨(13260/33937),(1/33937),(0/1),(0/1)⟩,⟨(82450/211453),(-1/211453),(0/1),(0/1)⟩,⟨(1932/4957),(1/4957),(0/1),(0/1)⟩,⟨(779/1994),(-1/5982),(0/1),(0/1)⟩,⟨(36569/93661),(-1/93661),(0/1),(0/1)⟩,⟨(93/262),(1/262),(0/1),(0/1)⟩,⟨(83/313),(1/313),(0/1),(0/1)⟩,⟨(1590/5893),(1/5893),(0/1),(0/1)⟩,⟨(1991/5521),(1/5521),(0/1),(0/1)⟩,⟨(4519/12598),(-1/12598),(0/1),(0/1)⟩,⟨(61/169),(1/169),(0/1),(0/1)⟩,⟨(1161/3142),(1/3142),(0/1),(0/1)⟩,⟨(2747/7501),(-1/7501),(0/1),(0/1)⟩,⟨(1251/4667),(-1/14001),(0/1),(0/1)⟩,⟨(483/1318),(1/1318),(0/1),(0/1)⟩,⟨(7480/20353),(1/20353),(0/1),(0/1)⟩,⟨(797/2221),(1/2221),(0/1),(0/1)⟩,⟨(12510/34801),(1/34801),(0/1),(0/1)⟩,⟨(667/1846),(-1/1846),(0/1),(0/1)⟩,⟨(11574/32101),(-1/32101),(0/1),(0/1)⟩,⟨(9467/26234),(1/78702),(0/1),(0/1)⟩,⟨(660/2461),(1/2461),(0/1),(0/1)⟩,⟨(10229/38062),(1/38062),(0/1),(0/1)⟩,⟨(175/647),(-1/1941),(0/1),(0/1)⟩,⟨(22567/83569),(1/83569),(0/1),(0/1)⟩,⟨(383/1033),(-1/1033),(0/1),(0/1)⟩,⟨(6760/18301),(-1/18301),(0/1),(0/1)⟩,⟨(5491/14843),(1/44529),(0/1),(0/1)⟩,⟨(446/1177),(1/1177),(0/1),(0/1)⟩,⟨(2755/7247),(1/21741),(0/1),(0/1)⟩,⟨(651/1702),(-1/1702),(0/1),(0/1)⟩,⟨(3247/8507),(-1/25521),(0/1),(0/1)⟩,⟨(19756/52033),(-1/52033),(0/1),(0/1)⟩,⟨(18819/48661),(1/48661),(0/1),(0/1)⟩,⟨(33653/86281),(1/86281),(0/1),(0/1)⟩,⟨(9257/34318),(-1/34318),(0/1),(0/1)⟩,⟨(856/2341),(1/2341),(0/1),(0/1)⟩,⟨(5363/14642),(1/43926),(0/1),(0/1)⟩,⟨(1301/3541),(-1/3541),(0/1),(0/1)⟩,⟨(6431/17522),(-1/52566),(0/1),(0/1)⟩,⟨(38250/104497),(-1/104497),(0/1),(0/1)⟩]
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
private abbrev earlyInput64 : LowerPair × Bool := (([2, 1, 3], [3, 1, 2]), true)
private def earlyCodes64 : List (ℕ × ℕ) := [(60, 61), (60, 62), (60, 61), (63, 61)]
private abbrev earlyInput65 : LowerPair × Bool := (([2, 1, 3], [3, 1, 2]), false)
private def earlyCodes65 : List (ℕ × ℕ) := [(64, 39)]
private abbrev earlyInput66 : LowerPair × Bool := (([2, 1, 3], [3, 1, 1]), true)
private def earlyCodes66 : List (ℕ × ℕ) := [(60, 9), (60, 10), (60, 9), (63, 9)]
private abbrev earlyInput67 : LowerPair × Bool := (([2, 1, 3], [3, 1, 1]), false)
private def earlyCodes67 : List (ℕ × ℕ) := [(64, 15)]
private abbrev earlyInput68 : LowerPair × Bool := (([2, 1, 2], [3, 1, 1]), true)
private def earlyCodes68 : List (ℕ × ℕ) := [(65, 9), (65, 10), (65, 9), (66, 9)]
private abbrev earlyInput69 : LowerPair × Bool := (([2, 1, 2], [3, 1, 1]), false)
private def earlyCodes69 : List (ℕ × ℕ) := [(7, 15), (7, 16), (7, 15), (67, 15)]
private abbrev earlyInput70 : LowerPair × Bool := (([2, 1, 3], [3, 2]), true)
private def earlyCodes70 : List (ℕ × ℕ) := [(60, 28), (60, 28), (60, 29), (60, 28), (63, 28)]
private abbrev earlyInput71 : LowerPair × Bool := (([2, 1, 3], [3, 2]), false)
private def earlyCodes71 : List (ℕ × ℕ) := [(64, 30), (64, 30)]
private abbrev earlyInput72 : LowerPair × Bool := (([2, 1, 3], [3, 3]), true)
private def earlyCodes72 : List (ℕ × ℕ) := [(60, 1), (60, 1)]
private abbrev earlyInput73 : LowerPair × Bool := (([2, 1, 3], [3, 3]), false)
private def earlyCodes73 : List (ℕ × ℕ) := [(64, 3), (64, 3)]
private abbrev earlyInput74 : LowerPair × Bool := (([2, 1, 2], [3, 2]), true)
private def earlyCodes74 : List (ℕ × ℕ) := [(65, 28), (65, 28), (65, 29), (65, 28), (66, 28)]
private abbrev earlyInput75 : LowerPair × Bool := (([2, 1, 2], [3, 2]), false)
private def earlyCodes75 : List (ℕ × ℕ) := [(7, 30), (7, 31), (7, 30), (67, 30), (7, 30)]
private abbrev earlyInput76 : LowerPair × Bool := (([2, 1, 1, 1], [3, 3]), true)
private def earlyCodes76 : List (ℕ × ℕ) := [(8, 1)]
private abbrev earlyInput77 : LowerPair × Bool := (([2, 1, 1, 1], [3, 3]), false)
private def earlyCodes77 : List (ℕ × ℕ) := [(41, 3), (41, 4), (41, 3), (42, 3)]
private abbrev earlyInput78 : LowerPair × Bool := (([2, 1, 1, 3], [3, 2]), true)
private def earlyCodes78 : List (ℕ × ℕ) := [(55, 28)]
private abbrev earlyInput79 : LowerPair × Bool := (([2, 1, 1, 3], [3, 2]), false)
private def earlyCodes79 : List (ℕ × ℕ) := [(2, 30), (2, 31), (2, 30), (5, 30)]
private abbrev earlyInput80 : LowerPair × Bool := (([2, 1, 2, 1], [3, 1, 2]), false)
private def earlyCodes80 : List (ℕ × ℕ) := [(7, 39), (7, 39), (7, 68), (7, 39), (67, 39)]
private abbrev earlyInput81 : LowerPair × Bool := (([2, 1, 2, 1], [3, 1, 2]), true)
private def earlyCodes81 : List (ℕ × ℕ) := [(69, 61), (69, 62), (69, 61), (70, 61), (69, 61)]
private abbrev earlyInput82 : LowerPair × Bool := (([2, 1, 2], [3, 1, 2]), false)
private def earlyCodes82 : List (ℕ × ℕ) := [(7, 39), (7, 68), (7, 39), (67, 39)]
private abbrev earlyInput83 : LowerPair × Bool := (([2, 1, 2], [3, 1, 2]), true)
private def earlyCodes83 : List (ℕ × ℕ) := [(65, 61), (65, 62), (65, 61), (66, 61)]
private abbrev earlyInput84 : LowerPair × Bool := (([2, 1, 3, 1], [3, 1, 2]), true)
private def earlyCodes84 : List (ℕ × ℕ) := [(71, 61), (71, 62), (71, 61), (72, 61), (71, 61)]
private abbrev earlyInput85 : LowerPair × Bool := (([2, 1, 3, 2], [3, 1, 2]), false)
private def earlyCodes85 : List (ℕ × ℕ) := [(73, 39), (73, 39), (73, 68), (73, 39), (74, 39)]
private abbrev earlyInput86 : LowerPair × Bool := (([2, 1, 3, 2], [3, 1, 2]), true)
private def earlyCodes86 : List (ℕ × ℕ) := [(63, 61), (63, 62), (63, 61), (75, 61), (63, 61)]
private abbrev earlyInput87 : LowerPair × Bool := (([2, 1, 3, 1], [3, 1, 2]), false)
private def earlyCodes87 : List (ℕ × ℕ) := [(64, 39), (64, 39)]
private abbrev earlyInput88 : LowerPair × Bool := (([2, 1, 3], [3, 1, 2, 1]), true)
private def earlyCodes88 : List (ℕ × ℕ) := [(60, 76), (60, 76), (60, 77), (60, 76), (63, 76)]
private abbrev earlyInput89 : LowerPair × Bool := (([2, 1, 3], [3, 1, 2, 2]), false)
private def earlyCodes89 : List (ℕ × ℕ) := [(64, 78), (64, 78)]
private abbrev earlyInput90 : LowerPair × Bool := (([2, 1, 3], [3, 1, 2, 2]), true)
private def earlyCodes90 : List (ℕ × ℕ) := [(60, 62), (60, 62), (60, 79), (60, 62), (63, 62)]
private abbrev earlyInput91 : LowerPair × Bool := (([2, 1, 3], [3, 1, 2, 1]), false)
private def earlyCodes91 : List (ℕ × ℕ) := [(64, 39), (64, 39)]
private abbrev earlyInput92 : LowerPair × Bool := (([2, 1, 3, 1], [3, 1, 1]), true)
private def earlyCodes92 : List (ℕ × ℕ) := [(71, 9), (71, 10), (71, 9), (72, 9), (71, 9)]
private abbrev earlyInput93 : LowerPair × Bool := (([2, 1, 3, 2], [3, 1, 1]), false)
private def earlyCodes93 : List (ℕ × ℕ) := [(73, 15), (73, 15), (73, 16), (73, 15), (74, 15)]
private abbrev earlyInput94 : LowerPair × Bool := (([2, 1, 3, 2], [3, 1, 1]), true)
private def earlyCodes94 : List (ℕ × ℕ) := [(63, 9), (63, 10), (63, 9), (75, 9), (63, 9)]
private abbrev earlyInput95 : LowerPair × Bool := (([2, 1, 3, 1], [3, 1, 1]), false)
private def earlyCodes95 : List (ℕ × ℕ) := [(64, 15), (64, 15)]
private abbrev earlyInput96 : LowerPair × Bool := (([2, 1, 3], [3, 1, 1, 1]), true)
private def earlyCodes96 : List (ℕ × ℕ) := [(60, 23), (60, 23), (60, 24), (60, 23), (63, 23)]
private abbrev earlyInput97 : LowerPair × Bool := (([2, 1, 3], [3, 1, 1, 2]), false)
private def earlyCodes97 : List (ℕ × ℕ) := [(64, 25), (64, 25)]
private abbrev earlyInput98 : LowerPair × Bool := (([2, 1, 3], [3, 1, 1, 2]), true)
private def earlyCodes98 : List (ℕ × ℕ) := [(60, 10), (60, 10), (60, 27), (60, 10), (63, 10)]
private abbrev earlyInput99 : LowerPair × Bool := (([2, 1, 3], [3, 1, 1, 1]), false)
private def earlyCodes99 : List (ℕ × ℕ) := [(64, 15), (64, 15)]
private abbrev earlyInput100 : LowerPair × Bool := (([2, 1, 2, 1], [3, 1, 1]), true)
private def earlyCodes100 : List (ℕ × ℕ) := [(69, 9), (69, 10), (69, 9), (70, 9), (69, 9)]
private abbrev earlyInput101 : LowerPair × Bool := (([2, 1, 2, 2], [3, 1, 1]), false)
private def earlyCodes101 : List (ℕ × ℕ) := [(80, 15), (80, 15), (80, 16), (80, 15), (81, 15)]
private abbrev earlyInput102 : LowerPair × Bool := (([2, 1, 2, 2], [3, 1, 1]), true)
private def earlyCodes102 : List (ℕ × ℕ) := [(66, 9), (66, 10), (66, 9), (82, 9), (66, 9)]
private abbrev earlyInput103 : LowerPair × Bool := (([2, 1, 2, 1], [3, 1, 1]), false)
private def earlyCodes103 : List (ℕ × ℕ) := [(7, 15), (7, 15), (7, 16), (7, 15), (67, 15)]
private abbrev earlyInput104 : LowerPair × Bool := (([2, 1, 2], [3, 1, 1, 1]), true)
private def earlyCodes104 : List (ℕ × ℕ) := [(65, 23), (65, 23), (65, 24), (65, 23), (66, 23)]
private abbrev earlyInput105 : LowerPair × Bool := (([2, 1, 2], [3, 1, 1, 2]), false)
private def earlyCodes105 : List (ℕ × ℕ) := [(7, 25), (7, 26), (7, 25), (67, 25), (7, 25)]
private abbrev earlyInput106 : LowerPair × Bool := (([2, 1, 2], [3, 1, 1, 2]), true)
private def earlyCodes106 : List (ℕ × ℕ) := [(65, 10), (65, 10), (65, 27), (65, 10), (66, 10)]
private abbrev earlyInput107 : LowerPair × Bool := (([2, 1, 2], [3, 1, 1, 1]), false)
private def earlyCodes107 : List (ℕ × ℕ) := [(7, 15), (7, 16), (7, 15), (67, 15), (7, 15)]
private abbrev earlyInput108 : LowerPair × Bool := (([2, 1, 3, 1], [3, 2]), true)
private def earlyCodes108 : List (ℕ × ℕ) := [(71, 28), (71, 29), (71, 28), (72, 28)]
private abbrev earlyInput109 : LowerPair × Bool := (([2, 1, 3, 2], [3, 2]), false)
private def earlyCodes109 : List (ℕ × ℕ) := [(73, 30), (73, 31), (73, 30), (74, 30)]
private abbrev earlyInput110 : LowerPair × Bool := (([2, 1, 3, 2], [3, 2]), true)
private def earlyCodes110 : List (ℕ × ℕ) := [(63, 28), (63, 29), (63, 28), (75, 28)]
private abbrev earlyInput111 : LowerPair × Bool := (([2, 1, 3, 1], [3, 2]), false)
private def earlyCodes111 : List (ℕ × ℕ) := [(64, 30)]
private abbrev earlyInput112 : LowerPair × Bool := (([2, 1, 3], [3, 2, 2]), true)
private def earlyCodes112 : List (ℕ × ℕ) := [(60, 33), (60, 34), (60, 33), (63, 33)]
private abbrev earlyInput113 : LowerPair × Bool := (([2, 1, 3], [3, 2, 1]), false)
private def earlyCodes113 : List (ℕ × ℕ) := [(64, 35)]
private abbrev earlyInput114 : LowerPair × Bool := (([2, 1, 3], [3, 2, 1]), true)
private def earlyCodes114 : List (ℕ × ℕ) := [(60, 28), (60, 29), (60, 28), (63, 28)]
private abbrev earlyInput115 : LowerPair × Bool := (([2, 1, 3], [3, 2, 2]), false)
private def earlyCodes115 : List (ℕ × ℕ) := [(64, 31)]
private abbrev earlyInput116 : LowerPair × Bool := (([2, 1, 3, 1], [3, 3]), true)
private def earlyCodes116 : List (ℕ × ℕ) := [(71, 1)]
private abbrev earlyInput117 : LowerPair × Bool := (([2, 1, 3, 2], [3, 3]), false)
private def earlyCodes117 : List (ℕ × ℕ) := [(73, 3), (73, 4), (73, 3), (74, 3)]
private abbrev earlyInput118 : LowerPair × Bool := (([2, 1, 3, 2], [3, 3]), true)
private def earlyCodes118 : List (ℕ × ℕ) := [(63, 1)]
private abbrev earlyInput119 : LowerPair × Bool := (([2, 1, 3, 1], [3, 3]), false)
private def earlyCodes119 : List (ℕ × ℕ) := [(64, 3)]
private abbrev earlyInput120 : LowerPair × Bool := (([2, 1, 3], [3, 3, 2]), true)
private def earlyCodes120 : List (ℕ × ℕ) := [(60, 51), (60, 52), (60, 51), (63, 51)]
private abbrev earlyInput121 : LowerPair × Bool := (([2, 1, 3], [3, 3, 1]), false)
private def earlyCodes121 : List (ℕ × ℕ) := [(64, 53)]
private abbrev earlyInput122 : LowerPair × Bool := (([2, 1, 3], [3, 3, 1]), true)
private def earlyCodes122 : List (ℕ × ℕ) := [(60, 1)]
private abbrev earlyInput123 : LowerPair × Bool := (([2, 1, 3], [3, 3, 2]), false)
private def earlyCodes123 : List (ℕ × ℕ) := [(64, 4)]
private abbrev earlyInput124 : LowerPair × Bool := (([2, 1, 2, 1], [3, 2]), true)
private def earlyCodes124 : List (ℕ × ℕ) := [(69, 28), (69, 29), (69, 28), (70, 28)]
private abbrev earlyInput125 : LowerPair × Bool := (([2, 1, 2, 2], [3, 2]), false)
private def earlyCodes125 : List (ℕ × ℕ) := [(80, 30), (80, 31), (80, 30), (81, 30)]
private abbrev earlyInput126 : LowerPair × Bool := (([2, 1, 2, 2], [3, 2]), true)
private def earlyCodes126 : List (ℕ × ℕ) := [(66, 28), (66, 29), (66, 28), (82, 28)]
private abbrev earlyInput127 : LowerPair × Bool := (([2, 1, 2, 1], [3, 2]), false)
private def earlyCodes127 : List (ℕ × ℕ) := [(7, 30), (7, 31), (7, 30), (67, 30)]
private abbrev earlyInput128 : LowerPair × Bool := (([2, 1, 2], [3, 2, 2]), true)
private def earlyCodes128 : List (ℕ × ℕ) := [(65, 33), (65, 34), (65, 33), (66, 33)]
private abbrev earlyInput129 : LowerPair × Bool := (([2, 1, 2], [3, 2, 1]), false)
private def earlyCodes129 : List (ℕ × ℕ) := [(7, 35), (7, 36), (7, 35), (67, 35)]
private abbrev earlyInput130 : LowerPair × Bool := (([2, 1, 2], [3, 2, 1]), true)
private def earlyCodes130 : List (ℕ × ℕ) := [(65, 28), (65, 29), (65, 28), (66, 28)]
private abbrev earlyInput131 : LowerPair × Bool := (([2, 1, 2], [3, 2, 2]), false)
private def earlyCodes131 : List (ℕ × ℕ) := [(7, 31), (7, 32), (7, 31), (67, 31)]
private abbrev earlyInput132 : LowerPair × Bool := (([2, 1, 1, 1, 2], [3, 1, 1]), true)
private def earlyCodes132 : List (ℕ × ℕ) := [(83, 9), (83, 10), (83, 9), (84, 9)]
private abbrev earlyInput133 : LowerPair × Bool := (([2, 1, 1, 1, 1], [3, 1, 1]), false)
private def earlyCodes133 : List (ℕ × ℕ) := [(85, 15), (85, 16), (85, 15), (86, 15)]
private abbrev earlyInput134 : LowerPair × Bool := (([2, 1, 1, 1, 1], [3, 1, 1]), true)
private def earlyCodes134 : List (ℕ × ℕ) := [(8, 9), (8, 10), (8, 9), (11, 9)]
private abbrev earlyInput135 : LowerPair × Bool := (([2, 1, 1, 1, 2], [3, 1, 1]), false)
private def earlyCodes135 : List (ℕ × ℕ) := [(42, 15), (42, 16), (42, 15), (87, 15)]
private abbrev earlyInput136 : LowerPair × Bool := (([2, 1, 1, 1], [3, 1, 1, 1]), true)
private def earlyCodes136 : List (ℕ × ℕ) := [(8, 23), (8, 24), (8, 23), (11, 23)]
private abbrev earlyInput137 : LowerPair × Bool := (([2, 1, 1, 1], [3, 1, 1, 2]), false)
private def earlyCodes137 : List (ℕ × ℕ) := [(41, 25), (41, 26), (41, 25), (42, 25)]
private abbrev earlyInput138 : LowerPair × Bool := (([2, 1, 1, 1], [3, 1, 1, 2]), true)
private def earlyCodes138 : List (ℕ × ℕ) := [(8, 10), (8, 27), (8, 10), (11, 10)]
private abbrev earlyInput139 : LowerPair × Bool := (([2, 1, 1, 1], [3, 1, 1, 1]), false)
private def earlyCodes139 : List (ℕ × ℕ) := [(41, 15), (41, 16), (41, 15), (42, 15)]
private abbrev earlyInput140 : LowerPair × Bool := (([2, 1, 1, 2, 2], [3, 1, 1]), true)
private def earlyCodes140 : List (ℕ × ℕ) := [(47, 9), (47, 10), (47, 9), (88, 9)]
private abbrev earlyInput141 : LowerPair × Bool := (([2, 1, 1, 2, 1], [3, 1, 1]), false)
private def earlyCodes141 : List (ℕ × ℕ) := [(48, 15), (48, 16), (48, 15), (49, 15)]
private abbrev earlyInput142 : LowerPair × Bool := (([2, 1, 1, 2, 1], [3, 1, 1]), true)
private def earlyCodes142 : List (ℕ × ℕ) := [(0, 9), (0, 10), (0, 9), (45, 9)]
private abbrev earlyInput143 : LowerPair × Bool := (([2, 1, 1, 2, 2], [3, 1, 1]), false)
private def earlyCodes143 : List (ℕ × ℕ) := [(44, 15), (44, 16), (44, 15), (46, 15)]
private abbrev earlyInput144 : LowerPair × Bool := (([2, 1, 1, 2], [3, 1, 1, 1]), true)
private def earlyCodes144 : List (ℕ × ℕ) := [(0, 23), (0, 24), (0, 23), (45, 23)]
private abbrev earlyInput145 : LowerPair × Bool := (([2, 1, 1, 2], [3, 1, 1, 2]), false)
private def earlyCodes145 : List (ℕ × ℕ) := [(43, 25), (43, 26), (43, 25), (44, 25)]
private abbrev earlyInput146 : LowerPair × Bool := (([2, 1, 1, 2], [3, 1, 1, 2]), true)
private def earlyCodes146 : List (ℕ × ℕ) := [(0, 10), (0, 27), (0, 10), (45, 10)]
private abbrev earlyInput147 : LowerPair × Bool := (([2, 1, 1, 2], [3, 1, 1, 1]), false)
private def earlyCodes147 : List (ℕ × ℕ) := [(43, 15), (43, 16), (43, 15), (44, 15)]
private abbrev earlyInput148 : LowerPair × Bool := (([2, 1, 1, 1, 2], [3, 2]), true)
private def earlyCodes148 : List (ℕ × ℕ) := [(83, 28), (83, 28), (83, 29), (83, 28), (84, 28)]
private abbrev earlyInput149 : LowerPair × Bool := (([2, 1, 1, 1, 1], [3, 2]), false)
private def earlyCodes149 : List (ℕ × ℕ) := [(85, 30), (85, 31), (85, 30), (86, 30), (85, 30)]
private abbrev earlyInput150 : LowerPair × Bool := (([2, 1, 1, 1, 1], [3, 2]), true)
private def earlyCodes150 : List (ℕ × ℕ) := [(8, 28), (8, 28), (8, 29), (8, 28), (11, 28)]
private abbrev earlyInput151 : LowerPair × Bool := (([2, 1, 1, 1, 2], [3, 2]), false)
private def earlyCodes151 : List (ℕ × ℕ) := [(42, 30), (42, 31), (42, 30), (87, 30), (42, 30)]
private abbrev earlyInput152 : LowerPair × Bool := (([2, 1, 1, 1], [3, 2, 2]), true)
private def earlyCodes152 : List (ℕ × ℕ) := [(8, 33), (8, 34), (8, 33), (11, 33), (8, 33)]
private abbrev earlyInput153 : LowerPair × Bool := (([2, 1, 1, 1], [3, 2, 1]), false)
private def earlyCodes153 : List (ℕ × ℕ) := [(41, 35), (41, 35), (41, 36), (41, 35), (42, 35)]
private abbrev earlyInput154 : LowerPair × Bool := (([2, 1, 1, 1], [3, 2, 1]), true)
private def earlyCodes154 : List (ℕ × ℕ) := [(8, 28), (8, 29), (8, 28), (11, 28), (8, 28)]
private abbrev earlyInput155 : LowerPair × Bool := (([2, 1, 1, 1], [3, 2, 2]), false)
private def earlyCodes155 : List (ℕ × ℕ) := [(41, 31), (41, 31), (41, 32), (41, 31), (42, 31)]
private abbrev earlyInput156 : LowerPair × Bool := (([2, 1, 1, 1, 2], [3, 3]), true)
private def earlyCodes156 : List (ℕ × ℕ) := [(83, 1), (83, 1)]
private abbrev earlyInput157 : LowerPair × Bool := (([2, 1, 1, 1, 1], [3, 3]), false)
private def earlyCodes157 : List (ℕ × ℕ) := [(85, 3), (85, 4), (85, 3), (86, 3), (85, 3)]
private abbrev earlyInput158 : LowerPair × Bool := (([2, 1, 1, 1, 1], [3, 3]), true)
private def earlyCodes158 : List (ℕ × ℕ) := [(8, 1), (8, 1)]
private abbrev earlyInput159 : LowerPair × Bool := (([2, 1, 1, 1, 2], [3, 3]), false)
private def earlyCodes159 : List (ℕ × ℕ) := [(42, 3), (42, 4), (42, 3), (87, 3), (42, 3)]
private abbrev earlyInput160 : LowerPair × Bool := (([2, 1, 1, 1], [3, 3, 2]), true)
private def earlyCodes160 : List (ℕ × ℕ) := [(8, 51), (8, 52), (8, 51), (11, 51), (8, 51)]
private abbrev earlyInput161 : LowerPair × Bool := (([2, 1, 1, 1], [3, 3, 1]), false)
private def earlyCodes161 : List (ℕ × ℕ) := [(41, 53), (41, 53), (41, 54), (41, 53), (42, 53)]
private abbrev earlyInput162 : LowerPair × Bool := (([2, 1, 1, 1], [3, 3, 1]), true)
private def earlyCodes162 : List (ℕ × ℕ) := [(8, 1), (8, 1)]
private abbrev earlyInput163 : LowerPair × Bool := (([2, 1, 1, 1], [3, 3, 2]), false)
private def earlyCodes163 : List (ℕ × ℕ) := [(41, 4), (41, 4), (41, 50), (41, 4), (42, 4)]
private abbrev earlyInput164 : LowerPair × Bool := (([2, 1, 1, 2, 2], [3, 2]), true)
private def earlyCodes164 : List (ℕ × ℕ) := [(47, 28), (47, 28), (47, 29), (47, 28), (88, 28)]
private abbrev earlyInput165 : LowerPair × Bool := (([2, 1, 1, 2, 1], [3, 2]), false)
private def earlyCodes165 : List (ℕ × ℕ) := [(48, 30), (48, 31), (48, 30), (49, 30), (48, 30)]
private abbrev earlyInput166 : LowerPair × Bool := (([2, 1, 1, 2, 1], [3, 2]), true)
private def earlyCodes166 : List (ℕ × ℕ) := [(0, 28), (0, 28), (0, 29), (0, 28), (45, 28)]
private abbrev earlyInput167 : LowerPair × Bool := (([2, 1, 1, 2, 2], [3, 2]), false)
private def earlyCodes167 : List (ℕ × ℕ) := [(44, 30), (44, 31), (44, 30), (46, 30), (44, 30)]
private abbrev earlyInput168 : LowerPair × Bool := (([2, 1, 1, 2], [3, 2, 2]), true)
private def earlyCodes168 : List (ℕ × ℕ) := [(0, 33), (0, 34), (0, 33), (45, 33), (0, 33)]
private abbrev earlyInput169 : LowerPair × Bool := (([2, 1, 1, 2], [3, 2, 1]), false)
private def earlyCodes169 : List (ℕ × ℕ) := [(43, 35), (43, 35), (43, 36), (43, 35), (44, 35)]
private abbrev earlyInput170 : LowerPair × Bool := (([2, 1, 1, 2], [3, 2, 1]), true)
private def earlyCodes170 : List (ℕ × ℕ) := [(0, 28), (0, 29), (0, 28), (45, 28), (0, 28)]
private abbrev earlyInput171 : LowerPair × Bool := (([2, 1, 1, 2], [3, 2, 2]), false)
private def earlyCodes171 : List (ℕ × ℕ) := [(43, 31), (43, 31), (43, 32), (43, 31), (44, 31)]
private abbrev earlyInput172 : LowerPair × Bool := (([2, 1, 1, 3, 2], [3, 2]), true)
private def earlyCodes172 : List (ℕ × ℕ) := [(57, 28), (57, 28), (57, 29), (57, 28), (89, 28)]
private abbrev earlyInput173 : LowerPair × Bool := (([2, 1, 1, 3, 1], [3, 2]), false)
private def earlyCodes173 : List (ℕ × ℕ) := [(58, 30), (58, 31), (58, 30), (59, 30), (58, 30)]
private abbrev earlyInput174 : LowerPair × Bool := (([2, 1, 1, 3, 1], [3, 2]), true)
private def earlyCodes174 : List (ℕ × ℕ) := [(55, 28), (55, 28)]
private abbrev earlyInput175 : LowerPair × Bool := (([2, 1, 1, 3, 2], [3, 2]), false)
private def earlyCodes175 : List (ℕ × ℕ) := [(5, 30), (5, 31), (5, 30), (56, 30), (5, 30)]
private abbrev earlyInput176 : LowerPair × Bool := (([2, 1, 1, 3], [3, 2, 2]), true)
private def earlyCodes176 : List (ℕ × ℕ) := [(55, 33), (55, 33)]
private abbrev earlyInput177 : LowerPair × Bool := (([2, 1, 1, 3], [3, 2, 1]), false)
private def earlyCodes177 : List (ℕ × ℕ) := [(2, 35), (2, 35), (2, 36), (2, 35), (5, 35)]
private abbrev earlyInput178 : LowerPair × Bool := (([2, 1, 1, 3], [3, 2, 1]), true)
private def earlyCodes178 : List (ℕ × ℕ) := [(55, 28), (55, 28)]
private abbrev earlyInput179 : LowerPair × Bool := (([2, 1, 1, 3], [3, 2, 2]), false)
private def earlyCodes179 : List (ℕ × ℕ) := [(2, 31), (2, 31), (2, 32), (2, 31), (5, 31)]
private abbrev earlyInput180 : LowerPair × Bool := (([2, 1, 2, 2], [3, 1, 2]), false)
private def earlyCodes180 : List (ℕ × ℕ) := [(80, 39), (80, 39), (80, 68), (80, 39), (81, 39)]
private abbrev earlyInput181 : LowerPair × Bool := (([2, 1, 2, 2], [3, 1, 2]), true)
private def earlyCodes181 : List (ℕ × ℕ) := [(66, 61), (66, 62), (66, 61), (82, 61), (66, 61)]
private abbrev earlyInput182 : LowerPair × Bool := (([2, 1, 2], [3, 1, 2, 1]), true)
private def earlyCodes182 : List (ℕ × ℕ) := [(65, 76), (65, 76), (65, 77), (65, 76), (66, 76)]
private abbrev earlyInput183 : LowerPair × Bool := (([2, 1, 2], [3, 1, 2, 2]), false)
private def earlyCodes183 : List (ℕ × ℕ) := [(7, 78), (7, 90), (7, 78), (67, 78), (7, 78)]
private abbrev earlyInput184 : LowerPair × Bool := (([2, 1, 2], [3, 1, 2, 2]), true)
private def earlyCodes184 : List (ℕ × ℕ) := [(65, 62), (65, 62), (65, 79), (65, 62), (66, 62)]
private abbrev earlyInput185 : LowerPair × Bool := (([2, 1, 2], [3, 1, 2, 1]), false)
private def earlyCodes185 : List (ℕ × ℕ) := [(7, 39), (7, 68), (7, 39), (67, 39), (7, 39)]
private abbrev earlyInput186 : LowerPair × Bool := (([2, 1, 2, 1, 2], [3, 1, 2]), true)
private def earlyCodes186 : List (ℕ × ℕ) := [(91, 61), (91, 62), (91, 61), (92, 61)]
private abbrev earlyInput187 : LowerPair × Bool := (([2, 1, 2, 1, 1], [3, 1, 2]), false)
private def earlyCodes187 : List (ℕ × ℕ) := [(93, 39), (93, 68), (93, 39), (94, 39)]
private abbrev earlyInput188 : LowerPair × Bool := (([2, 1, 2, 1, 1], [3, 1, 2]), true)
private def earlyCodes188 : List (ℕ × ℕ) := [(69, 61), (69, 62), (69, 61), (70, 61)]
private abbrev earlyInput189 : LowerPair × Bool := (([2, 1, 2, 1, 2], [3, 1, 2]), false)
private def earlyCodes189 : List (ℕ × ℕ) := [(67, 39), (67, 68), (67, 39), (95, 39)]
private abbrev earlyInput190 : LowerPair × Bool := (([2, 1, 2, 1], [3, 1, 2, 1]), true)
private def earlyCodes190 : List (ℕ × ℕ) := [(69, 76), (69, 77), (69, 76), (70, 76)]
private abbrev earlyInput191 : LowerPair × Bool := (([2, 1, 2, 1], [3, 1, 2, 2]), false)
private def earlyCodes191 : List (ℕ × ℕ) := [(7, 78), (7, 90), (7, 78), (67, 78)]
private abbrev earlyInput192 : LowerPair × Bool := (([2, 1, 2, 1], [3, 1, 2, 2]), true)
private def earlyCodes192 : List (ℕ × ℕ) := [(69, 62), (69, 79), (69, 62), (70, 62)]
private abbrev earlyInput193 : LowerPair × Bool := (([2, 1, 2, 1], [3, 1, 2, 1]), false)
private def earlyCodes193 : List (ℕ × ℕ) := [(7, 39), (7, 68), (7, 39), (67, 39)]
private def earlyDecode (x : ℕ × ℕ) : CertField × CertField := (earlyFields[x.1]?.getD ⟨0,0,0,0⟩,earlyFields[x.2]?.getD ⟨0,0,0,0⟩)
private theorem hEC0 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput0.1 earlyInput0.2).map Prod.fst = earlyCodes0.map earlyDecode := by decide +kernel
private theorem hEC1 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput1.1 earlyInput1.2).map Prod.fst = earlyCodes1.map earlyDecode := by decide +kernel
private theorem hEC2 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput2.1 earlyInput2.2).map Prod.fst = earlyCodes2.map earlyDecode := by decide +kernel
private theorem hEC3 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput3.1 earlyInput3.2).map Prod.fst = earlyCodes3.map earlyDecode := by decide +kernel
private theorem hEC4 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput4.1 earlyInput4.2).map Prod.fst = earlyCodes4.map earlyDecode := by decide +kernel
private theorem hEC5 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput5.1 earlyInput5.2).map Prod.fst = earlyCodes5.map earlyDecode := by decide +kernel
private theorem hEC6 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput6.1 earlyInput6.2).map Prod.fst = earlyCodes6.map earlyDecode := by decide +kernel
private theorem hEC7 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput7.1 earlyInput7.2).map Prod.fst = earlyCodes7.map earlyDecode := by decide +kernel
private theorem hEC8 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput8.1 earlyInput8.2).map Prod.fst = earlyCodes8.map earlyDecode := by decide +kernel
private theorem hEC9 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput9.1 earlyInput9.2).map Prod.fst = earlyCodes9.map earlyDecode := by decide +kernel
private theorem hEC10 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput10.1 earlyInput10.2).map Prod.fst = earlyCodes10.map earlyDecode := by decide +kernel
private theorem hEC11 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput11.1 earlyInput11.2).map Prod.fst = earlyCodes11.map earlyDecode := by decide +kernel
private theorem hEC12 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput12.1 earlyInput12.2).map Prod.fst = earlyCodes12.map earlyDecode := by decide +kernel
private theorem hEC13 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput13.1 earlyInput13.2).map Prod.fst = earlyCodes13.map earlyDecode := by decide +kernel
private theorem hEC14 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput14.1 earlyInput14.2).map Prod.fst = earlyCodes14.map earlyDecode := by decide +kernel
private theorem hEC15 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput15.1 earlyInput15.2).map Prod.fst = earlyCodes15.map earlyDecode := by decide +kernel
private theorem hEC16 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput16.1 earlyInput16.2).map Prod.fst = earlyCodes16.map earlyDecode := by decide +kernel
private theorem hEC17 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput17.1 earlyInput17.2).map Prod.fst = earlyCodes17.map earlyDecode := by decide +kernel
private theorem hEC18 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput18.1 earlyInput18.2).map Prod.fst = earlyCodes18.map earlyDecode := by decide +kernel
private theorem hEC19 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput19.1 earlyInput19.2).map Prod.fst = earlyCodes19.map earlyDecode := by decide +kernel
private theorem hEC20 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput20.1 earlyInput20.2).map Prod.fst = earlyCodes20.map earlyDecode := by decide +kernel
private theorem hEC21 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput21.1 earlyInput21.2).map Prod.fst = earlyCodes21.map earlyDecode := by decide +kernel
private theorem hEC22 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput22.1 earlyInput22.2).map Prod.fst = earlyCodes22.map earlyDecode := by decide +kernel
private theorem hEC23 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput23.1 earlyInput23.2).map Prod.fst = earlyCodes23.map earlyDecode := by decide +kernel
private theorem hEC24 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput24.1 earlyInput24.2).map Prod.fst = earlyCodes24.map earlyDecode := by decide +kernel
private theorem hEC25 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput25.1 earlyInput25.2).map Prod.fst = earlyCodes25.map earlyDecode := by decide +kernel
private theorem hEC26 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput26.1 earlyInput26.2).map Prod.fst = earlyCodes26.map earlyDecode := by decide +kernel
private theorem hEC27 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput27.1 earlyInput27.2).map Prod.fst = earlyCodes27.map earlyDecode := by decide +kernel
private theorem hEC28 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput28.1 earlyInput28.2).map Prod.fst = earlyCodes28.map earlyDecode := by decide +kernel
private theorem hEC29 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput29.1 earlyInput29.2).map Prod.fst = earlyCodes29.map earlyDecode := by decide +kernel
private theorem hEC30 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput30.1 earlyInput30.2).map Prod.fst = earlyCodes30.map earlyDecode := by decide +kernel
private theorem hEC31 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput31.1 earlyInput31.2).map Prod.fst = earlyCodes31.map earlyDecode := by decide +kernel
private theorem hEC32 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput32.1 earlyInput32.2).map Prod.fst = earlyCodes32.map earlyDecode := by decide +kernel
private theorem hEC33 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput33.1 earlyInput33.2).map Prod.fst = earlyCodes33.map earlyDecode := by decide +kernel
private theorem hEC34 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput34.1 earlyInput34.2).map Prod.fst = earlyCodes34.map earlyDecode := by decide +kernel
private theorem hEC35 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput35.1 earlyInput35.2).map Prod.fst = earlyCodes35.map earlyDecode := by decide +kernel
private theorem hEC36 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput36.1 earlyInput36.2).map Prod.fst = earlyCodes36.map earlyDecode := by decide +kernel
private theorem hEC37 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput37.1 earlyInput37.2).map Prod.fst = earlyCodes37.map earlyDecode := by decide +kernel
private theorem hEC38 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput38.1 earlyInput38.2).map Prod.fst = earlyCodes38.map earlyDecode := by decide +kernel
private theorem hEC39 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput39.1 earlyInput39.2).map Prod.fst = earlyCodes39.map earlyDecode := by decide +kernel
private theorem hEC40 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput40.1 earlyInput40.2).map Prod.fst = earlyCodes40.map earlyDecode := by decide +kernel
private theorem hEC41 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput41.1 earlyInput41.2).map Prod.fst = earlyCodes41.map earlyDecode := by decide +kernel
private theorem hEC42 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput42.1 earlyInput42.2).map Prod.fst = earlyCodes42.map earlyDecode := by decide +kernel
private theorem hEC43 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput43.1 earlyInput43.2).map Prod.fst = earlyCodes43.map earlyDecode := by decide +kernel
private theorem hEC44 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput44.1 earlyInput44.2).map Prod.fst = earlyCodes44.map earlyDecode := by decide +kernel
private theorem hEC45 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput45.1 earlyInput45.2).map Prod.fst = earlyCodes45.map earlyDecode := by decide +kernel
private theorem hEC46 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput46.1 earlyInput46.2).map Prod.fst = earlyCodes46.map earlyDecode := by decide +kernel
private theorem hEC47 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput47.1 earlyInput47.2).map Prod.fst = earlyCodes47.map earlyDecode := by decide +kernel
private theorem hEC48 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput48.1 earlyInput48.2).map Prod.fst = earlyCodes48.map earlyDecode := by decide +kernel
private theorem hEC49 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput49.1 earlyInput49.2).map Prod.fst = earlyCodes49.map earlyDecode := by decide +kernel
private theorem hEC50 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput50.1 earlyInput50.2).map Prod.fst = earlyCodes50.map earlyDecode := by decide +kernel
private theorem hEC51 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput51.1 earlyInput51.2).map Prod.fst = earlyCodes51.map earlyDecode := by decide +kernel
private theorem hEC52 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput52.1 earlyInput52.2).map Prod.fst = earlyCodes52.map earlyDecode := by decide +kernel
private theorem hEC53 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput53.1 earlyInput53.2).map Prod.fst = earlyCodes53.map earlyDecode := by decide +kernel
private theorem hEC54 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput54.1 earlyInput54.2).map Prod.fst = earlyCodes54.map earlyDecode := by decide +kernel
private theorem hEC55 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput55.1 earlyInput55.2).map Prod.fst = earlyCodes55.map earlyDecode := by decide +kernel
private theorem hEC56 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput56.1 earlyInput56.2).map Prod.fst = earlyCodes56.map earlyDecode := by decide +kernel
private theorem hEC57 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput57.1 earlyInput57.2).map Prod.fst = earlyCodes57.map earlyDecode := by decide +kernel
private theorem hEC58 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput58.1 earlyInput58.2).map Prod.fst = earlyCodes58.map earlyDecode := by decide +kernel
private theorem hEC59 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput59.1 earlyInput59.2).map Prod.fst = earlyCodes59.map earlyDecode := by decide +kernel
private theorem hEC60 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput60.1 earlyInput60.2).map Prod.fst = earlyCodes60.map earlyDecode := by decide +kernel
private theorem hEC61 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput61.1 earlyInput61.2).map Prod.fst = earlyCodes61.map earlyDecode := by decide +kernel
private theorem hEC62 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput62.1 earlyInput62.2).map Prod.fst = earlyCodes62.map earlyDecode := by decide +kernel
private theorem hEC63 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput63.1 earlyInput63.2).map Prod.fst = earlyCodes63.map earlyDecode := by decide +kernel
private theorem hEC64 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput64.1 earlyInput64.2).map Prod.fst = earlyCodes64.map earlyDecode := by decide +kernel
private theorem hEC65 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput65.1 earlyInput65.2).map Prod.fst = earlyCodes65.map earlyDecode := by decide +kernel
private theorem hEC66 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput66.1 earlyInput66.2).map Prod.fst = earlyCodes66.map earlyDecode := by decide +kernel
private theorem hEC67 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput67.1 earlyInput67.2).map Prod.fst = earlyCodes67.map earlyDecode := by decide +kernel
private theorem hEC68 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput68.1 earlyInput68.2).map Prod.fst = earlyCodes68.map earlyDecode := by decide +kernel
private theorem hEC69 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput69.1 earlyInput69.2).map Prod.fst = earlyCodes69.map earlyDecode := by decide +kernel
private theorem hEC70 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput70.1 earlyInput70.2).map Prod.fst = earlyCodes70.map earlyDecode := by decide +kernel
private theorem hEC71 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput71.1 earlyInput71.2).map Prod.fst = earlyCodes71.map earlyDecode := by decide +kernel
private theorem hEC72 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput72.1 earlyInput72.2).map Prod.fst = earlyCodes72.map earlyDecode := by decide +kernel
private theorem hEC73 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput73.1 earlyInput73.2).map Prod.fst = earlyCodes73.map earlyDecode := by decide +kernel
private theorem hEC74 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput74.1 earlyInput74.2).map Prod.fst = earlyCodes74.map earlyDecode := by decide +kernel
private theorem hEC75 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput75.1 earlyInput75.2).map Prod.fst = earlyCodes75.map earlyDecode := by decide +kernel
private theorem hEC76 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput76.1 earlyInput76.2).map Prod.fst = earlyCodes76.map earlyDecode := by decide +kernel
private theorem hEC77 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput77.1 earlyInput77.2).map Prod.fst = earlyCodes77.map earlyDecode := by decide +kernel
private theorem hEC78 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput78.1 earlyInput78.2).map Prod.fst = earlyCodes78.map earlyDecode := by decide +kernel
private theorem hEC79 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput79.1 earlyInput79.2).map Prod.fst = earlyCodes79.map earlyDecode := by decide +kernel
private theorem hEC80 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput80.1 earlyInput80.2).map Prod.fst = earlyCodes80.map earlyDecode := by decide +kernel
private theorem hEC81 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput81.1 earlyInput81.2).map Prod.fst = earlyCodes81.map earlyDecode := by decide +kernel
private theorem hEC82 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput82.1 earlyInput82.2).map Prod.fst = earlyCodes82.map earlyDecode := by decide +kernel
private theorem hEC83 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput83.1 earlyInput83.2).map Prod.fst = earlyCodes83.map earlyDecode := by decide +kernel
private theorem hEC84 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput84.1 earlyInput84.2).map Prod.fst = earlyCodes84.map earlyDecode := by decide +kernel
private theorem hEC85 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput85.1 earlyInput85.2).map Prod.fst = earlyCodes85.map earlyDecode := by decide +kernel
private theorem hEC86 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput86.1 earlyInput86.2).map Prod.fst = earlyCodes86.map earlyDecode := by decide +kernel
private theorem hEC87 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput87.1 earlyInput87.2).map Prod.fst = earlyCodes87.map earlyDecode := by decide +kernel
private theorem hEC88 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput88.1 earlyInput88.2).map Prod.fst = earlyCodes88.map earlyDecode := by decide +kernel
private theorem hEC89 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput89.1 earlyInput89.2).map Prod.fst = earlyCodes89.map earlyDecode := by decide +kernel
private theorem hEC90 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput90.1 earlyInput90.2).map Prod.fst = earlyCodes90.map earlyDecode := by decide +kernel
private theorem hEC91 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput91.1 earlyInput91.2).map Prod.fst = earlyCodes91.map earlyDecode := by decide +kernel
private theorem hEC92 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput92.1 earlyInput92.2).map Prod.fst = earlyCodes92.map earlyDecode := by decide +kernel
private theorem hEC93 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput93.1 earlyInput93.2).map Prod.fst = earlyCodes93.map earlyDecode := by decide +kernel
private theorem hEC94 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput94.1 earlyInput94.2).map Prod.fst = earlyCodes94.map earlyDecode := by decide +kernel
private theorem hEC95 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput95.1 earlyInput95.2).map Prod.fst = earlyCodes95.map earlyDecode := by decide +kernel
private theorem hEC96 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput96.1 earlyInput96.2).map Prod.fst = earlyCodes96.map earlyDecode := by decide +kernel
private theorem hEC97 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput97.1 earlyInput97.2).map Prod.fst = earlyCodes97.map earlyDecode := by decide +kernel
private theorem hEC98 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput98.1 earlyInput98.2).map Prod.fst = earlyCodes98.map earlyDecode := by decide +kernel
private theorem hEC99 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput99.1 earlyInput99.2).map Prod.fst = earlyCodes99.map earlyDecode := by decide +kernel
private theorem hEC100 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput100.1 earlyInput100.2).map Prod.fst = earlyCodes100.map earlyDecode := by decide +kernel
private theorem hEC101 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput101.1 earlyInput101.2).map Prod.fst = earlyCodes101.map earlyDecode := by decide +kernel
private theorem hEC102 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput102.1 earlyInput102.2).map Prod.fst = earlyCodes102.map earlyDecode := by decide +kernel
private theorem hEC103 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput103.1 earlyInput103.2).map Prod.fst = earlyCodes103.map earlyDecode := by decide +kernel
private theorem hEC104 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput104.1 earlyInput104.2).map Prod.fst = earlyCodes104.map earlyDecode := by decide +kernel
private theorem hEC105 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput105.1 earlyInput105.2).map Prod.fst = earlyCodes105.map earlyDecode := by decide +kernel
private theorem hEC106 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput106.1 earlyInput106.2).map Prod.fst = earlyCodes106.map earlyDecode := by decide +kernel
private theorem hEC107 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput107.1 earlyInput107.2).map Prod.fst = earlyCodes107.map earlyDecode := by decide +kernel
private theorem hEC108 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput108.1 earlyInput108.2).map Prod.fst = earlyCodes108.map earlyDecode := by decide +kernel
private theorem hEC109 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput109.1 earlyInput109.2).map Prod.fst = earlyCodes109.map earlyDecode := by decide +kernel
private theorem hEC110 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput110.1 earlyInput110.2).map Prod.fst = earlyCodes110.map earlyDecode := by decide +kernel
private theorem hEC111 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput111.1 earlyInput111.2).map Prod.fst = earlyCodes111.map earlyDecode := by decide +kernel
private theorem hEC112 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput112.1 earlyInput112.2).map Prod.fst = earlyCodes112.map earlyDecode := by decide +kernel
private theorem hEC113 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput113.1 earlyInput113.2).map Prod.fst = earlyCodes113.map earlyDecode := by decide +kernel
private theorem hEC114 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput114.1 earlyInput114.2).map Prod.fst = earlyCodes114.map earlyDecode := by decide +kernel
private theorem hEC115 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput115.1 earlyInput115.2).map Prod.fst = earlyCodes115.map earlyDecode := by decide +kernel
private theorem hEC116 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput116.1 earlyInput116.2).map Prod.fst = earlyCodes116.map earlyDecode := by decide +kernel
private theorem hEC117 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput117.1 earlyInput117.2).map Prod.fst = earlyCodes117.map earlyDecode := by decide +kernel
private theorem hEC118 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput118.1 earlyInput118.2).map Prod.fst = earlyCodes118.map earlyDecode := by decide +kernel
private theorem hEC119 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput119.1 earlyInput119.2).map Prod.fst = earlyCodes119.map earlyDecode := by decide +kernel
private theorem hEC120 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput120.1 earlyInput120.2).map Prod.fst = earlyCodes120.map earlyDecode := by decide +kernel
private theorem hEC121 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput121.1 earlyInput121.2).map Prod.fst = earlyCodes121.map earlyDecode := by decide +kernel
private theorem hEC122 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput122.1 earlyInput122.2).map Prod.fst = earlyCodes122.map earlyDecode := by decide +kernel
private theorem hEC123 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput123.1 earlyInput123.2).map Prod.fst = earlyCodes123.map earlyDecode := by decide +kernel
private theorem hEC124 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput124.1 earlyInput124.2).map Prod.fst = earlyCodes124.map earlyDecode := by decide +kernel
private theorem hEC125 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput125.1 earlyInput125.2).map Prod.fst = earlyCodes125.map earlyDecode := by decide +kernel
private theorem hEC126 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput126.1 earlyInput126.2).map Prod.fst = earlyCodes126.map earlyDecode := by decide +kernel
private theorem hEC127 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput127.1 earlyInput127.2).map Prod.fst = earlyCodes127.map earlyDecode := by decide +kernel
private theorem hEC128 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput128.1 earlyInput128.2).map Prod.fst = earlyCodes128.map earlyDecode := by decide +kernel
private theorem hEC129 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput129.1 earlyInput129.2).map Prod.fst = earlyCodes129.map earlyDecode := by decide +kernel
private theorem hEC130 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput130.1 earlyInput130.2).map Prod.fst = earlyCodes130.map earlyDecode := by decide +kernel
private theorem hEC131 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput131.1 earlyInput131.2).map Prod.fst = earlyCodes131.map earlyDecode := by decide +kernel
private theorem hEC132 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput132.1 earlyInput132.2).map Prod.fst = earlyCodes132.map earlyDecode := by decide +kernel
private theorem hEC133 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput133.1 earlyInput133.2).map Prod.fst = earlyCodes133.map earlyDecode := by decide +kernel
private theorem hEC134 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput134.1 earlyInput134.2).map Prod.fst = earlyCodes134.map earlyDecode := by decide +kernel
private theorem hEC135 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput135.1 earlyInput135.2).map Prod.fst = earlyCodes135.map earlyDecode := by decide +kernel
private theorem hEC136 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput136.1 earlyInput136.2).map Prod.fst = earlyCodes136.map earlyDecode := by decide +kernel
private theorem hEC137 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput137.1 earlyInput137.2).map Prod.fst = earlyCodes137.map earlyDecode := by decide +kernel
private theorem hEC138 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput138.1 earlyInput138.2).map Prod.fst = earlyCodes138.map earlyDecode := by decide +kernel
private theorem hEC139 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput139.1 earlyInput139.2).map Prod.fst = earlyCodes139.map earlyDecode := by decide +kernel
private theorem hEC140 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput140.1 earlyInput140.2).map Prod.fst = earlyCodes140.map earlyDecode := by decide +kernel
private theorem hEC141 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput141.1 earlyInput141.2).map Prod.fst = earlyCodes141.map earlyDecode := by decide +kernel
private theorem hEC142 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput142.1 earlyInput142.2).map Prod.fst = earlyCodes142.map earlyDecode := by decide +kernel
private theorem hEC143 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput143.1 earlyInput143.2).map Prod.fst = earlyCodes143.map earlyDecode := by decide +kernel
private theorem hEC144 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput144.1 earlyInput144.2).map Prod.fst = earlyCodes144.map earlyDecode := by decide +kernel
private theorem hEC145 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput145.1 earlyInput145.2).map Prod.fst = earlyCodes145.map earlyDecode := by decide +kernel
private theorem hEC146 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput146.1 earlyInput146.2).map Prod.fst = earlyCodes146.map earlyDecode := by decide +kernel
private theorem hEC147 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput147.1 earlyInput147.2).map Prod.fst = earlyCodes147.map earlyDecode := by decide +kernel
private theorem hEC148 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput148.1 earlyInput148.2).map Prod.fst = earlyCodes148.map earlyDecode := by decide +kernel
private theorem hEC149 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput149.1 earlyInput149.2).map Prod.fst = earlyCodes149.map earlyDecode := by decide +kernel
private theorem hEC150 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput150.1 earlyInput150.2).map Prod.fst = earlyCodes150.map earlyDecode := by decide +kernel
private theorem hEC151 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput151.1 earlyInput151.2).map Prod.fst = earlyCodes151.map earlyDecode := by decide +kernel
private theorem hEC152 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput152.1 earlyInput152.2).map Prod.fst = earlyCodes152.map earlyDecode := by decide +kernel
private theorem hEC153 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput153.1 earlyInput153.2).map Prod.fst = earlyCodes153.map earlyDecode := by decide +kernel
private theorem hEC154 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput154.1 earlyInput154.2).map Prod.fst = earlyCodes154.map earlyDecode := by decide +kernel
private theorem hEC155 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput155.1 earlyInput155.2).map Prod.fst = earlyCodes155.map earlyDecode := by decide +kernel
private theorem hEC156 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput156.1 earlyInput156.2).map Prod.fst = earlyCodes156.map earlyDecode := by decide +kernel
private theorem hEC157 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput157.1 earlyInput157.2).map Prod.fst = earlyCodes157.map earlyDecode := by decide +kernel
private theorem hEC158 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput158.1 earlyInput158.2).map Prod.fst = earlyCodes158.map earlyDecode := by decide +kernel
private theorem hEC159 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput159.1 earlyInput159.2).map Prod.fst = earlyCodes159.map earlyDecode := by decide +kernel
private theorem hEC160 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput160.1 earlyInput160.2).map Prod.fst = earlyCodes160.map earlyDecode := by decide +kernel
private theorem hEC161 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput161.1 earlyInput161.2).map Prod.fst = earlyCodes161.map earlyDecode := by decide +kernel
private theorem hEC162 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput162.1 earlyInput162.2).map Prod.fst = earlyCodes162.map earlyDecode := by decide +kernel
private theorem hEC163 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput163.1 earlyInput163.2).map Prod.fst = earlyCodes163.map earlyDecode := by decide +kernel
private theorem hEC164 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput164.1 earlyInput164.2).map Prod.fst = earlyCodes164.map earlyDecode := by decide +kernel
private theorem hEC165 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput165.1 earlyInput165.2).map Prod.fst = earlyCodes165.map earlyDecode := by decide +kernel
private theorem hEC166 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput166.1 earlyInput166.2).map Prod.fst = earlyCodes166.map earlyDecode := by decide +kernel
private theorem hEC167 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput167.1 earlyInput167.2).map Prod.fst = earlyCodes167.map earlyDecode := by decide +kernel
private theorem hEC168 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput168.1 earlyInput168.2).map Prod.fst = earlyCodes168.map earlyDecode := by decide +kernel
private theorem hEC169 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput169.1 earlyInput169.2).map Prod.fst = earlyCodes169.map earlyDecode := by decide +kernel
private theorem hEC170 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput170.1 earlyInput170.2).map Prod.fst = earlyCodes170.map earlyDecode := by decide +kernel
private theorem hEC171 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput171.1 earlyInput171.2).map Prod.fst = earlyCodes171.map earlyDecode := by decide +kernel
private theorem hEC172 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput172.1 earlyInput172.2).map Prod.fst = earlyCodes172.map earlyDecode := by decide +kernel
private theorem hEC173 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput173.1 earlyInput173.2).map Prod.fst = earlyCodes173.map earlyDecode := by decide +kernel
private theorem hEC174 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput174.1 earlyInput174.2).map Prod.fst = earlyCodes174.map earlyDecode := by decide +kernel
private theorem hEC175 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput175.1 earlyInput175.2).map Prod.fst = earlyCodes175.map earlyDecode := by decide +kernel
private theorem hEC176 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput176.1 earlyInput176.2).map Prod.fst = earlyCodes176.map earlyDecode := by decide +kernel
private theorem hEC177 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput177.1 earlyInput177.2).map Prod.fst = earlyCodes177.map earlyDecode := by decide +kernel
private theorem hEC178 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput178.1 earlyInput178.2).map Prod.fst = earlyCodes178.map earlyDecode := by decide +kernel
private theorem hEC179 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput179.1 earlyInput179.2).map Prod.fst = earlyCodes179.map earlyDecode := by decide +kernel
private theorem hEC180 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput180.1 earlyInput180.2).map Prod.fst = earlyCodes180.map earlyDecode := by decide +kernel
private theorem hEC181 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput181.1 earlyInput181.2).map Prod.fst = earlyCodes181.map earlyDecode := by decide +kernel
private theorem hEC182 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput182.1 earlyInput182.2).map Prod.fst = earlyCodes182.map earlyDecode := by decide +kernel
private theorem hEC183 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput183.1 earlyInput183.2).map Prod.fst = earlyCodes183.map earlyDecode := by decide +kernel
private theorem hEC184 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput184.1 earlyInput184.2).map Prod.fst = earlyCodes184.map earlyDecode := by decide +kernel
private theorem hEC185 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput185.1 earlyInput185.2).map Prod.fst = earlyCodes185.map earlyDecode := by decide +kernel
private theorem hEC186 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput186.1 earlyInput186.2).map Prod.fst = earlyCodes186.map earlyDecode := by decide +kernel
private theorem hEC187 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput187.1 earlyInput187.2).map Prod.fst = earlyCodes187.map earlyDecode := by decide +kernel
private theorem hEC188 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput188.1 earlyInput188.2).map Prod.fst = earlyCodes188.map earlyDecode := by decide +kernel
private theorem hEC189 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput189.1 earlyInput189.2).map Prod.fst = earlyCodes189.map earlyDecode := by decide +kernel
private theorem hEC190 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput190.1 earlyInput190.2).map Prod.fst = earlyCodes190.map earlyDecode := by decide +kernel
private theorem hEC191 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput191.1 earlyInput191.2).map Prod.fst = earlyCodes191.map earlyDecode := by decide +kernel
private theorem hEC192 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput192.1 earlyInput192.2).map Prod.fst = earlyCodes192.map earlyDecode := by decide +kernel
private theorem hEC193 : (section14EndpointCases (lowerEarlyTerminalContext lowerEarlyTerminalState2) earlyInput193.1 earlyInput193.2).map Prod.fst = earlyCodes193.map earlyDecode := by decide +kernel
private theorem pairFlags_4_5_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput4.1 earlyInput4.2 earlyInput5.1 earlyInput5.2 false = (List.replicate 25 true) := by
  unfold earlyCompareFlags
  rw [hEC4,hEC5]
  decide +kernel
private theorem pairFlags_6_7_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput6.1 earlyInput6.2 earlyInput7.1 earlyInput7.2 true = (List.replicate 16 true) := by
  unfold earlyCompareFlags
  rw [hEC6,hEC7]
  decide +kernel
private theorem pairFlags_8_9_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput8.1 earlyInput8.2 earlyInput9.1 earlyInput9.2 true = (List.replicate 16 false) := by
  unfold earlyCompareFlags
  rw [hEC8,hEC9]
  decide +kernel
private theorem pairFlags_10_11_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput10.1 earlyInput10.2 earlyInput11.1 earlyInput11.2 true = (List.replicate 16 false) := by
  unfold earlyCompareFlags
  rw [hEC10,hEC11]
  decide +kernel
private theorem pairFlags_12_13_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput12.1 earlyInput12.2 earlyInput13.1 earlyInput13.2 true = (List.replicate 16 true) := by
  unfold earlyCompareFlags
  rw [hEC12,hEC13]
  decide +kernel
private theorem pairFlags_14_15_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput14.1 earlyInput14.2 earlyInput15.1 earlyInput15.2 false = (List.replicate 16 true) := by
  unfold earlyCompareFlags
  rw [hEC14,hEC15]
  decide +kernel
private theorem pairFlags_16_17_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput16.1 earlyInput16.2 earlyInput17.1 earlyInput17.2 true = (List.replicate 25 true) := by
  unfold earlyCompareFlags
  rw [hEC16,hEC17]
  decide +kernel
private theorem pairFlags_18_19_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput18.1 earlyInput18.2 earlyInput19.1 earlyInput19.2 true = (List.replicate 25 false) := by
  unfold earlyCompareFlags
  rw [hEC18,hEC19]
  decide +kernel
private theorem pairFlags_20_21_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput20.1 earlyInput20.2 earlyInput21.1 earlyInput21.2 true = (List.replicate 25 true) := by
  unfold earlyCompareFlags
  rw [hEC20,hEC21]
  decide +kernel
private theorem pairFlags_22_23_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput22.1 earlyInput22.2 earlyInput23.1 earlyInput23.2 true = (List.replicate 25 false) := by
  unfold earlyCompareFlags
  rw [hEC22,hEC23]
  decide +kernel
private theorem pairFlags_24_5_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput24.1 earlyInput24.2 earlyInput5.1 earlyInput5.2 false = (List.replicate 20 false) := by
  unfold earlyCompareFlags
  rw [hEC24,hEC5]
  decide +kernel
private theorem pairFlags_4_25_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput4.1 earlyInput4.2 earlyInput25.1 earlyInput25.2 false = (List.replicate 5 false) := by
  unfold earlyCompareFlags
  rw [hEC4,hEC25]
  decide +kernel
private theorem pairFlags_4_15_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput4.1 earlyInput4.2 earlyInput15.1 earlyInput15.2 false = (List.replicate 20 false) := by
  unfold earlyCompareFlags
  rw [hEC4,hEC15]
  decide +kernel
private theorem pairFlags_14_5_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput14.1 earlyInput14.2 earlyInput5.1 earlyInput5.2 false = (List.replicate 20 true) := by
  unfold earlyCompareFlags
  rw [hEC14,hEC5]
  decide +kernel
private theorem pairFlags_14_2_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput14.1 earlyInput14.2 earlyInput2.1 earlyInput2.2 false = (List.replicate 16 false) := by
  unfold earlyCompareFlags
  rw [hEC14,hEC2]
  decide +kernel
private theorem pairFlags_26_15_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput26.1 earlyInput26.2 earlyInput15.1 earlyInput15.2 false = (List.replicate 16 true) := by
  unfold earlyCompareFlags
  rw [hEC26,hEC15]
  decide +kernel
private theorem pairFlags_27_28_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput27.1 earlyInput27.2 earlyInput28.1 earlyInput28.2 false = (List.replicate 16 true) := by
  unfold earlyCompareFlags
  rw [hEC27,hEC28]
  decide +kernel
private theorem pairFlags_3_29_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput3.1 earlyInput3.2 earlyInput29.1 earlyInput29.2 true = (List.replicate 25 false) := by
  unfold earlyCompareFlags
  rw [hEC3,hEC29]
  decide +kernel
private theorem pairFlags_30_31_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput30.1 earlyInput30.2 earlyInput31.1 earlyInput31.2 true = (List.replicate 25 true) := by
  unfold earlyCompareFlags
  rw [hEC30,hEC31]
  decide +kernel
private theorem pairFlags_32_33_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput32.1 earlyInput32.2 earlyInput33.1 earlyInput33.2 true = (List.replicate 25 false) := by
  unfold earlyCompareFlags
  rw [hEC32,hEC33]
  decide +kernel
private theorem pairFlags_34_35_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput34.1 earlyInput34.2 earlyInput35.1 earlyInput35.2 true = (List.replicate 25 true) := by
  unfold earlyCompareFlags
  rw [hEC34,hEC35]
  decide +kernel
private theorem pairFlags_36_37_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput36.1 earlyInput36.2 earlyInput37.1 earlyInput37.2 false = (List.replicate 25 true) := by
  unfold earlyCompareFlags
  rw [hEC36,hEC37]
  decide +kernel
private theorem pairFlags_38_39_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput38.1 earlyInput38.2 earlyInput39.1 earlyInput39.2 true = (List.replicate 16 false) := by
  unfold earlyCompareFlags
  rw [hEC38,hEC39]
  decide +kernel
private theorem pairFlags_40_41_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput40.1 earlyInput40.2 earlyInput41.1 earlyInput41.2 true = (List.replicate 16 true) := by
  unfold earlyCompareFlags
  rw [hEC40,hEC41]
  decide +kernel
private theorem pairFlags_42_43_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput42.1 earlyInput42.2 earlyInput43.1 earlyInput43.2 true = (List.replicate 16 true) := by
  unfold earlyCompareFlags
  rw [hEC42,hEC43]
  decide +kernel
private theorem pairFlags_44_45_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput44.1 earlyInput44.2 earlyInput45.1 earlyInput45.2 true = (List.replicate 16 false) := by
  unfold earlyCompareFlags
  rw [hEC44,hEC45]
  decide +kernel
private theorem pairFlags_0_46_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput0.1 earlyInput0.2 earlyInput46.1 earlyInput46.2 false = (List.replicate 4 true) := by
  unfold earlyCompareFlags
  rw [hEC0,hEC46]
  decide +kernel
private theorem pairFlags_47_48_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput47.1 earlyInput47.2 earlyInput48.1 earlyInput48.2 true = (List.replicate 10 true) := by
  unfold earlyCompareFlags
  rw [hEC47,hEC48]
  decide +kernel
private theorem pairFlags_49_50_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput49.1 earlyInput49.2 earlyInput50.1 earlyInput50.2 true = (List.replicate 10 false) := by
  unfold earlyCompareFlags
  rw [hEC49,hEC50]
  decide +kernel
private theorem pairFlags_51_52_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput51.1 earlyInput51.2 earlyInput52.1 earlyInput52.2 true = (List.replicate 10 true) := by
  unfold earlyCompareFlags
  rw [hEC51,hEC52]
  decide +kernel
private theorem pairFlags_53_54_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput53.1 earlyInput53.2 earlyInput54.1 earlyInput54.2 true = (List.replicate 25 false) := by
  unfold earlyCompareFlags
  rw [hEC53,hEC54]
  decide +kernel
private theorem pairFlags_55_1_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput55.1 earlyInput55.2 earlyInput1.1 earlyInput1.2 false = (List.replicate 4 true) := by
  unfold earlyCompareFlags
  rw [hEC55,hEC1]
  decide +kernel
private theorem pairFlags_56_57_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput56.1 earlyInput56.2 earlyInput57.1 earlyInput57.2 true = (List.replicate 10 true) := by
  unfold earlyCompareFlags
  rw [hEC56,hEC57]
  decide +kernel
private theorem pairFlags_58_59_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput58.1 earlyInput58.2 earlyInput59.1 earlyInput59.2 true = (List.replicate 10 false) := by
  unfold earlyCompareFlags
  rw [hEC58,hEC59]
  decide +kernel
private theorem pairFlags_60_61_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput60.1 earlyInput60.2 earlyInput61.1 earlyInput61.2 true = (List.replicate 10 true) := by
  unfold earlyCompareFlags
  rw [hEC60,hEC61]
  decide +kernel
private theorem pairFlags_62_63_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput62.1 earlyInput62.2 earlyInput63.1 earlyInput63.2 true = (List.replicate 10 false) := by
  unfold earlyCompareFlags
  rw [hEC62,hEC63]
  decide +kernel
private theorem pairFlags_24_28_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput24.1 earlyInput24.2 earlyInput28.1 earlyInput28.2 false = (List.replicate 16 false) := by
  unfold earlyCompareFlags
  rw [hEC24,hEC28]
  decide +kernel
private theorem pairFlags_27_25_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput27.1 earlyInput27.2 earlyInput25.1 earlyInput25.2 false = (List.replicate 4 false) := by
  unfold earlyCompareFlags
  rw [hEC27,hEC25]
  decide +kernel
private theorem pairFlags_27_37_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput27.1 earlyInput27.2 earlyInput37.1 earlyInput37.2 false = (List.replicate 20 false) := by
  unfold earlyCompareFlags
  rw [hEC27,hEC37]
  decide +kernel
private theorem pairFlags_36_28_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput36.1 earlyInput36.2 earlyInput28.1 earlyInput28.2 false = (List.replicate 20 true) := by
  unfold earlyCompareFlags
  rw [hEC36,hEC28]
  decide +kernel
private theorem pairFlags_36_46_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput36.1 earlyInput36.2 earlyInput46.1 earlyInput46.2 false = (List.replicate 20 false) := by
  unfold earlyCompareFlags
  rw [hEC36,hEC46]
  decide +kernel
private theorem pairFlags_0_37_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput0.1 earlyInput0.2 earlyInput37.1 earlyInput37.2 false = (List.replicate 5 true) := by
  unfold earlyCompareFlags
  rw [hEC0,hEC37]
  decide +kernel
private theorem pairFlags_0_1_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput0.1 earlyInput0.2 earlyInput1.1 earlyInput1.2 false = (List.replicate 4 false) := by
  unfold earlyCompareFlags
  rw [hEC0,hEC1]
  decide +kernel
private theorem pairFlags_55_46_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput55.1 earlyInput55.2 earlyInput46.1 earlyInput46.2 false = (List.replicate 4 true) := by
  unfold earlyCompareFlags
  rw [hEC55,hEC46]
  decide +kernel
private theorem pairFlags_55_5_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput55.1 earlyInput55.2 earlyInput5.1 earlyInput5.2 false = (List.replicate 5 false) := by
  unfold earlyCompareFlags
  rw [hEC55,hEC5]
  decide +kernel
private theorem pairFlags_4_1_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput4.1 earlyInput4.2 earlyInput1.1 earlyInput1.2 false = (List.replicate 20 false) := by
  unfold earlyCompareFlags
  rw [hEC4,hEC1]
  decide +kernel
private theorem pairFlags_64_65_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput64.1 earlyInput64.2 earlyInput65.1 earlyInput65.2 false = (List.replicate 4 true) := by
  unfold earlyCompareFlags
  rw [hEC64,hEC65]
  decide +kernel
private theorem pairFlags_66_67_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput66.1 earlyInput66.2 earlyInput67.1 earlyInput67.2 false = (List.replicate 4 true) := by
  unfold earlyCompareFlags
  rw [hEC66,hEC67]
  decide +kernel
private theorem pairFlags_68_69_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput68.1 earlyInput68.2 earlyInput69.1 earlyInput69.2 false = (List.replicate 16 true) := by
  unfold earlyCompareFlags
  rw [hEC68,hEC69]
  decide +kernel
private theorem pairFlags_70_71_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput70.1 earlyInput70.2 earlyInput71.1 earlyInput71.2 false = (List.replicate 10 true) := by
  unfold earlyCompareFlags
  rw [hEC70,hEC71]
  decide +kernel
private theorem pairFlags_72_73_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput72.1 earlyInput72.2 earlyInput73.1 earlyInput73.2 false = (List.replicate 4 true) := by
  unfold earlyCompareFlags
  rw [hEC72,hEC73]
  decide +kernel
private theorem pairFlags_74_75_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput74.1 earlyInput74.2 earlyInput75.1 earlyInput75.2 false = (List.replicate 25 true) := by
  unfold earlyCompareFlags
  rw [hEC74,hEC75]
  decide +kernel
private theorem pairFlags_3_31_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput3.1 earlyInput3.2 earlyInput31.1 earlyInput31.2 false = (List.replicate 25 true) := by
  unfold earlyCompareFlags
  rw [hEC3,hEC31]
  decide +kernel
private theorem pairFlags_30_29_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput30.1 earlyInput30.2 earlyInput29.1 earlyInput29.2 false = (List.replicate 25 true) := by
  unfold earlyCompareFlags
  rw [hEC30,hEC29]
  decide +kernel
private theorem pairFlags_38_41_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput38.1 earlyInput38.2 earlyInput41.1 earlyInput41.2 false = (List.replicate 16 true) := by
  unfold earlyCompareFlags
  rw [hEC38,hEC41]
  decide +kernel
private theorem pairFlags_76_77_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput76.1 earlyInput76.2 earlyInput77.1 earlyInput77.2 false = (List.replicate 4 true) := by
  unfold earlyCompareFlags
  rw [hEC76,hEC77]
  decide +kernel
private theorem pairFlags_40_39_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput40.1 earlyInput40.2 earlyInput39.1 earlyInput39.2 false = (List.replicate 16 true) := by
  unfold earlyCompareFlags
  rw [hEC40,hEC39]
  decide +kernel
private theorem pairFlags_78_79_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput78.1 earlyInput78.2 earlyInput79.1 earlyInput79.2 false = (List.replicate 4 true) := by
  unfold earlyCompareFlags
  rw [hEC78,hEC79]
  decide +kernel
private theorem pairFlags_24_65_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput24.1 earlyInput24.2 earlyInput65.1 earlyInput65.2 false = (List.replicate 4 false) := by
  unfold earlyCompareFlags
  rw [hEC24,hEC65]
  decide +kernel
private theorem pairFlags_64_25_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput64.1 earlyInput64.2 earlyInput25.1 earlyInput25.2 false = (List.replicate 4 false) := by
  unfold earlyCompareFlags
  rw [hEC64,hEC25]
  decide +kernel
private theorem pairFlags_64_67_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput64.1 earlyInput64.2 earlyInput67.1 earlyInput67.2 false = (List.replicate 4 false) := by
  unfold earlyCompareFlags
  rw [hEC64,hEC67]
  decide +kernel
private theorem pairFlags_66_65_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput66.1 earlyInput66.2 earlyInput65.1 earlyInput65.2 false = (List.replicate 4 true) := by
  unfold earlyCompareFlags
  rw [hEC66,hEC65]
  decide +kernel
private theorem pairFlags_68_71_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput68.1 earlyInput68.2 earlyInput71.1 earlyInput71.2 false = (List.replicate 8 false) := by
  unfold earlyCompareFlags
  rw [hEC68,hEC71]
  decide +kernel
private theorem pairFlags_70_69_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput70.1 earlyInput70.2 earlyInput69.1 earlyInput69.2 false = (List.replicate 20 false) := by
  unfold earlyCompareFlags
  rw [hEC70,hEC69]
  decide +kernel
private theorem pairFlags_70_73_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput70.1 earlyInput70.2 earlyInput73.1 earlyInput73.2 false = (List.replicate 10 false) := by
  unfold earlyCompareFlags
  rw [hEC70,hEC73]
  decide +kernel
private theorem pairFlags_72_71_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput72.1 earlyInput72.2 earlyInput71.1 earlyInput71.2 false = (List.replicate 4 true) := by
  unfold earlyCompareFlags
  rw [hEC72,hEC71]
  decide +kernel
private theorem pairFlags_72_75_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput72.1 earlyInput72.2 earlyInput75.1 earlyInput75.2 false = (List.replicate 10 false) := by
  unfold earlyCompareFlags
  rw [hEC72,hEC75]
  decide +kernel
private theorem pairFlags_74_73_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput74.1 earlyInput74.2 earlyInput73.1 earlyInput73.2 false = (List.replicate 10 false) := by
  unfold earlyCompareFlags
  rw [hEC74,hEC73]
  decide +kernel
private theorem pairFlags_74_31_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput74.1 earlyInput74.2 earlyInput31.1 earlyInput31.2 false = (List.replicate 25 false) := by
  unfold earlyCompareFlags
  rw [hEC74,hEC31]
  decide +kernel
private theorem pairFlags_3_75_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput3.1 earlyInput3.2 earlyInput75.1 earlyInput75.2 false = (List.replicate 25 false) := by
  unfold earlyCompareFlags
  rw [hEC3,hEC75]
  decide +kernel
private theorem pairFlags_30_41_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput30.1 earlyInput30.2 earlyInput41.1 earlyInput41.2 false = (List.replicate 20 false) := by
  unfold earlyCompareFlags
  rw [hEC30,hEC41]
  decide +kernel
private theorem pairFlags_38_29_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput38.1 earlyInput38.2 earlyInput29.1 earlyInput29.2 false = (List.replicate 20 false) := by
  unfold earlyCompareFlags
  rw [hEC38,hEC29]
  decide +kernel
private theorem pairFlags_38_77_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput38.1 earlyInput38.2 earlyInput77.1 earlyInput77.2 false = (List.replicate 16 false) := by
  unfold earlyCompareFlags
  rw [hEC38,hEC77]
  decide +kernel
private theorem pairFlags_76_41_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput76.1 earlyInput76.2 earlyInput41.1 earlyInput41.2 false = (List.replicate 4 true) := by
  unfold earlyCompareFlags
  rw [hEC76,hEC41]
  decide +kernel
private theorem pairFlags_76_39_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput76.1 earlyInput76.2 earlyInput39.1 earlyInput39.2 false = (List.replicate 4 false) := by
  unfold earlyCompareFlags
  rw [hEC76,hEC39]
  decide +kernel
private theorem pairFlags_40_77_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput40.1 earlyInput40.2 earlyInput77.1 earlyInput77.2 false = (List.replicate 16 false) := by
  unfold earlyCompareFlags
  rw [hEC40,hEC77]
  decide +kernel
private theorem pairFlags_40_79_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput40.1 earlyInput40.2 earlyInput79.1 earlyInput79.2 false = (List.replicate 16 false) := by
  unfold earlyCompareFlags
  rw [hEC40,hEC79]
  decide +kernel
private theorem pairFlags_78_39_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput78.1 earlyInput78.2 earlyInput39.1 earlyInput39.2 false = (List.replicate 4 true) := by
  unfold earlyCompareFlags
  rw [hEC78,hEC39]
  decide +kernel
private theorem pairFlags_78_46_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput78.1 earlyInput78.2 earlyInput46.1 earlyInput46.2 false = (List.replicate 4 false) := by
  unfold earlyCompareFlags
  rw [hEC78,hEC46]
  decide +kernel
private theorem pairFlags_0_79_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput0.1 earlyInput0.2 earlyInput79.1 earlyInput79.2 false = (List.replicate 4 false) := by
  unfold earlyCompareFlags
  rw [hEC0,hEC79]
  decide +kernel
private theorem pairFlags_66_80_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput66.1 earlyInput66.2 earlyInput80.1 earlyInput80.2 false = (List.replicate 20 false) := by
  unfold earlyCompareFlags
  rw [hEC66,hEC80]
  decide +kernel
private theorem pairFlags_81_67_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput81.1 earlyInput81.2 earlyInput67.1 earlyInput67.2 false = (List.replicate 5 false) := by
  unfold earlyCompareFlags
  rw [hEC81,hEC67]
  decide +kernel
private theorem pairFlags_81_69_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput81.1 earlyInput81.2 earlyInput69.1 earlyInput69.2 false = (List.replicate 20 false) := by
  unfold earlyCompareFlags
  rw [hEC81,hEC69]
  decide +kernel
private theorem pairFlags_68_80_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput68.1 earlyInput68.2 earlyInput80.1 earlyInput80.2 false = (List.replicate 20 true) := by
  unfold earlyCompareFlags
  rw [hEC68,hEC80]
  decide +kernel
private theorem pairFlags_66_82_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput66.1 earlyInput66.2 earlyInput82.1 earlyInput82.2 false = (List.replicate 16 false) := by
  unfold earlyCompareFlags
  rw [hEC66,hEC82]
  decide +kernel
private theorem pairFlags_83_67_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput83.1 earlyInput83.2 earlyInput67.1 earlyInput67.2 false = (List.replicate 4 false) := by
  unfold earlyCompareFlags
  rw [hEC83,hEC67]
  decide +kernel
private theorem pairFlags_83_69_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput83.1 earlyInput83.2 earlyInput69.1 earlyInput69.2 false = (List.replicate 16 false) := by
  unfold earlyCompareFlags
  rw [hEC83,hEC69]
  decide +kernel
private theorem pairFlags_68_82_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput68.1 earlyInput68.2 earlyInput82.1 earlyInput82.2 false = (List.replicate 16 true) := by
  unfold earlyCompareFlags
  rw [hEC68,hEC82]
  decide +kernel
private theorem pairFlags_3_41_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput3.1 earlyInput3.2 earlyInput41.1 earlyInput41.2 false = (List.replicate 20 false) := by
  unfold earlyCompareFlags
  rw [hEC3,hEC41]
  decide +kernel
private theorem pairFlags_38_31_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput38.1 earlyInput38.2 earlyInput31.1 earlyInput31.2 false = (List.replicate 20 true) := by
  unfold earlyCompareFlags
  rw [hEC38,hEC31]
  decide +kernel
private theorem pairFlags_3_29_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput3.1 earlyInput3.2 earlyInput29.1 earlyInput29.2 false = (List.replicate 25 false) := by
  unfold earlyCompareFlags
  rw [hEC3,hEC29]
  decide +kernel
private theorem pairFlags_30_31_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput30.1 earlyInput30.2 earlyInput31.1 earlyInput31.2 false = (List.replicate 25 true) := by
  unfold earlyCompareFlags
  rw [hEC30,hEC31]
  decide +kernel
private theorem pairFlags_55_2_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput55.1 earlyInput55.2 earlyInput2.1 earlyInput2.2 false = (List.replicate 4 false) := by
  unfold earlyCompareFlags
  rw [hEC55,hEC2]
  decide +kernel
private theorem pairFlags_26_1_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput26.1 earlyInput26.2 earlyInput1.1 earlyInput1.2 false = (List.replicate 16 true) := by
  unfold earlyCompareFlags
  rw [hEC26,hEC1]
  decide +kernel
private theorem pairFlags_84_85_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput84.1 earlyInput84.2 earlyInput85.1 earlyInput85.2 true = (List.replicate 25 false) := by
  unfold earlyCompareFlags
  rw [hEC84,hEC85]
  decide +kernel
private theorem pairFlags_86_87_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput86.1 earlyInput86.2 earlyInput87.1 earlyInput87.2 true = (List.replicate 10 true) := by
  unfold earlyCompareFlags
  rw [hEC86,hEC87]
  decide +kernel
private theorem pairFlags_88_89_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput88.1 earlyInput88.2 earlyInput89.1 earlyInput89.2 true = (List.replicate 10 false) := by
  unfold earlyCompareFlags
  rw [hEC88,hEC89]
  decide +kernel
private theorem pairFlags_90_91_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput90.1 earlyInput90.2 earlyInput91.1 earlyInput91.2 true = (List.replicate 10 true) := by
  unfold earlyCompareFlags
  rw [hEC90,hEC91]
  decide +kernel
private theorem pairFlags_92_93_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput92.1 earlyInput92.2 earlyInput93.1 earlyInput93.2 true = (List.replicate 25 false) := by
  unfold earlyCompareFlags
  rw [hEC92,hEC93]
  decide +kernel
private theorem pairFlags_94_95_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput94.1 earlyInput94.2 earlyInput95.1 earlyInput95.2 true = (List.replicate 10 true) := by
  unfold earlyCompareFlags
  rw [hEC94,hEC95]
  decide +kernel
private theorem pairFlags_96_97_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput96.1 earlyInput96.2 earlyInput97.1 earlyInput97.2 true = (List.replicate 10 false) := by
  unfold earlyCompareFlags
  rw [hEC96,hEC97]
  decide +kernel
private theorem pairFlags_98_99_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput98.1 earlyInput98.2 earlyInput99.1 earlyInput99.2 true = (List.replicate 10 true) := by
  unfold earlyCompareFlags
  rw [hEC98,hEC99]
  decide +kernel
private theorem pairFlags_100_101_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput100.1 earlyInput100.2 earlyInput101.1 earlyInput101.2 true = (List.replicate 25 false) := by
  unfold earlyCompareFlags
  rw [hEC100,hEC101]
  decide +kernel
private theorem pairFlags_102_103_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput102.1 earlyInput102.2 earlyInput103.1 earlyInput103.2 true = (List.replicate 25 true) := by
  unfold earlyCompareFlags
  rw [hEC102,hEC103]
  decide +kernel
private theorem pairFlags_104_105_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput104.1 earlyInput104.2 earlyInput105.1 earlyInput105.2 true = (List.replicate 25 false) := by
  unfold earlyCompareFlags
  rw [hEC104,hEC105]
  decide +kernel
private theorem pairFlags_106_107_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput106.1 earlyInput106.2 earlyInput107.1 earlyInput107.2 true = (List.replicate 25 true) := by
  unfold earlyCompareFlags
  rw [hEC106,hEC107]
  decide +kernel
private theorem pairFlags_108_109_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput108.1 earlyInput108.2 earlyInput109.1 earlyInput109.2 true = (List.replicate 16 false) := by
  unfold earlyCompareFlags
  rw [hEC108,hEC109]
  decide +kernel
private theorem pairFlags_110_111_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput110.1 earlyInput110.2 earlyInput111.1 earlyInput111.2 true = (List.replicate 4 true) := by
  unfold earlyCompareFlags
  rw [hEC110,hEC111]
  decide +kernel
private theorem pairFlags_112_113_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput112.1 earlyInput112.2 earlyInput113.1 earlyInput113.2 true = (List.replicate 4 false) := by
  unfold earlyCompareFlags
  rw [hEC112,hEC113]
  decide +kernel
private theorem pairFlags_114_115_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput114.1 earlyInput114.2 earlyInput115.1 earlyInput115.2 true = (List.replicate 4 true) := by
  unfold earlyCompareFlags
  rw [hEC114,hEC115]
  decide +kernel
private theorem pairFlags_116_117_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput116.1 earlyInput116.2 earlyInput117.1 earlyInput117.2 true = (List.replicate 4 false) := by
  unfold earlyCompareFlags
  rw [hEC116,hEC117]
  decide +kernel
private theorem pairFlags_118_119_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput118.1 earlyInput118.2 earlyInput119.1 earlyInput119.2 true = (List.replicate 1 true) := by
  unfold earlyCompareFlags
  rw [hEC118,hEC119]
  decide +kernel
private theorem pairFlags_120_121_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput120.1 earlyInput120.2 earlyInput121.1 earlyInput121.2 true = (List.replicate 4 false) := by
  unfold earlyCompareFlags
  rw [hEC120,hEC121]
  decide +kernel
private theorem pairFlags_122_123_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput122.1 earlyInput122.2 earlyInput123.1 earlyInput123.2 true = (List.replicate 1 true) := by
  unfold earlyCompareFlags
  rw [hEC122,hEC123]
  decide +kernel
private theorem pairFlags_124_125_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput124.1 earlyInput124.2 earlyInput125.1 earlyInput125.2 true = (List.replicate 16 false) := by
  unfold earlyCompareFlags
  rw [hEC124,hEC125]
  decide +kernel
private theorem pairFlags_126_127_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput126.1 earlyInput126.2 earlyInput127.1 earlyInput127.2 true = (List.replicate 16 true) := by
  unfold earlyCompareFlags
  rw [hEC126,hEC127]
  decide +kernel
private theorem pairFlags_128_129_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput128.1 earlyInput128.2 earlyInput129.1 earlyInput129.2 true = (List.replicate 16 false) := by
  unfold earlyCompareFlags
  rw [hEC128,hEC129]
  decide +kernel
private theorem pairFlags_130_131_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput130.1 earlyInput130.2 earlyInput131.1 earlyInput131.2 true = (List.replicate 16 true) := by
  unfold earlyCompareFlags
  rw [hEC130,hEC131]
  decide +kernel
private theorem pairFlags_132_133_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput132.1 earlyInput132.2 earlyInput133.1 earlyInput133.2 true = (List.replicate 16 false) := by
  unfold earlyCompareFlags
  rw [hEC132,hEC133]
  decide +kernel
private theorem pairFlags_134_135_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput134.1 earlyInput134.2 earlyInput135.1 earlyInput135.2 true = (List.replicate 16 true) := by
  unfold earlyCompareFlags
  rw [hEC134,hEC135]
  decide +kernel
private theorem pairFlags_136_137_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput136.1 earlyInput136.2 earlyInput137.1 earlyInput137.2 true = (List.replicate 16 false) := by
  unfold earlyCompareFlags
  rw [hEC136,hEC137]
  decide +kernel
private theorem pairFlags_138_139_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput138.1 earlyInput138.2 earlyInput139.1 earlyInput139.2 true = (List.replicate 16 true) := by
  unfold earlyCompareFlags
  rw [hEC138,hEC139]
  decide +kernel
private theorem pairFlags_140_141_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput140.1 earlyInput140.2 earlyInput141.1 earlyInput141.2 true = (List.replicate 16 false) := by
  unfold earlyCompareFlags
  rw [hEC140,hEC141]
  decide +kernel
private theorem pairFlags_142_143_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput142.1 earlyInput142.2 earlyInput143.1 earlyInput143.2 true = (List.replicate 16 true) := by
  unfold earlyCompareFlags
  rw [hEC142,hEC143]
  decide +kernel
private theorem pairFlags_144_145_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput144.1 earlyInput144.2 earlyInput145.1 earlyInput145.2 true = (List.replicate 16 false) := by
  unfold earlyCompareFlags
  rw [hEC144,hEC145]
  decide +kernel
private theorem pairFlags_146_147_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput146.1 earlyInput146.2 earlyInput147.1 earlyInput147.2 true = (List.replicate 16 true) := by
  unfold earlyCompareFlags
  rw [hEC146,hEC147]
  decide +kernel
private theorem pairFlags_148_149_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput148.1 earlyInput148.2 earlyInput149.1 earlyInput149.2 true = (List.replicate 25 false) := by
  unfold earlyCompareFlags
  rw [hEC148,hEC149]
  decide +kernel
private theorem pairFlags_150_151_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput150.1 earlyInput150.2 earlyInput151.1 earlyInput151.2 true = (List.replicate 25 true) := by
  unfold earlyCompareFlags
  rw [hEC150,hEC151]
  decide +kernel
private theorem pairFlags_152_153_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput152.1 earlyInput152.2 earlyInput153.1 earlyInput153.2 true = (List.replicate 25 false) := by
  unfold earlyCompareFlags
  rw [hEC152,hEC153]
  decide +kernel
private theorem pairFlags_154_155_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput154.1 earlyInput154.2 earlyInput155.1 earlyInput155.2 true = (List.replicate 25 true) := by
  unfold earlyCompareFlags
  rw [hEC154,hEC155]
  decide +kernel
private theorem pairFlags_156_157_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput156.1 earlyInput156.2 earlyInput157.1 earlyInput157.2 true = (List.replicate 10 false) := by
  unfold earlyCompareFlags
  rw [hEC156,hEC157]
  decide +kernel
private theorem pairFlags_158_159_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput158.1 earlyInput158.2 earlyInput159.1 earlyInput159.2 true = (List.replicate 10 true) := by
  unfold earlyCompareFlags
  rw [hEC158,hEC159]
  decide +kernel
private theorem pairFlags_160_161_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput160.1 earlyInput160.2 earlyInput161.1 earlyInput161.2 true = (List.replicate 25 false) := by
  unfold earlyCompareFlags
  rw [hEC160,hEC161]
  decide +kernel
private theorem pairFlags_162_163_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput162.1 earlyInput162.2 earlyInput163.1 earlyInput163.2 true = (List.replicate 10 true) := by
  unfold earlyCompareFlags
  rw [hEC162,hEC163]
  decide +kernel
private theorem pairFlags_164_165_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput164.1 earlyInput164.2 earlyInput165.1 earlyInput165.2 true = (List.replicate 25 false) := by
  unfold earlyCompareFlags
  rw [hEC164,hEC165]
  decide +kernel
private theorem pairFlags_166_167_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput166.1 earlyInput166.2 earlyInput167.1 earlyInput167.2 true = (List.replicate 25 true) := by
  unfold earlyCompareFlags
  rw [hEC166,hEC167]
  decide +kernel
private theorem pairFlags_168_169_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput168.1 earlyInput168.2 earlyInput169.1 earlyInput169.2 true = (List.replicate 25 false) := by
  unfold earlyCompareFlags
  rw [hEC168,hEC169]
  decide +kernel
private theorem pairFlags_170_171_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput170.1 earlyInput170.2 earlyInput171.1 earlyInput171.2 true = (List.replicate 25 true) := by
  unfold earlyCompareFlags
  rw [hEC170,hEC171]
  decide +kernel
private theorem pairFlags_172_173_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput172.1 earlyInput172.2 earlyInput173.1 earlyInput173.2 true = (List.replicate 25 false) := by
  unfold earlyCompareFlags
  rw [hEC172,hEC173]
  decide +kernel
private theorem pairFlags_174_175_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput174.1 earlyInput174.2 earlyInput175.1 earlyInput175.2 true = (List.replicate 10 true) := by
  unfold earlyCompareFlags
  rw [hEC174,hEC175]
  decide +kernel
private theorem pairFlags_176_177_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput176.1 earlyInput176.2 earlyInput177.1 earlyInput177.2 true = (List.replicate 10 false) := by
  unfold earlyCompareFlags
  rw [hEC176,hEC177]
  decide +kernel
private theorem pairFlags_178_179_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput178.1 earlyInput178.2 earlyInput179.1 earlyInput179.2 true = (List.replicate 10 true) := by
  unfold earlyCompareFlags
  rw [hEC178,hEC179]
  decide +kernel
private theorem pairFlags_81_180_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput81.1 earlyInput81.2 earlyInput180.1 earlyInput180.2 true = (List.replicate 25 false) := by
  unfold earlyCompareFlags
  rw [hEC81,hEC180]
  decide +kernel
private theorem pairFlags_181_80_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput181.1 earlyInput181.2 earlyInput80.1 earlyInput80.2 true = (List.replicate 25 true) := by
  unfold earlyCompareFlags
  rw [hEC181,hEC80]
  decide +kernel
private theorem pairFlags_182_183_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput182.1 earlyInput182.2 earlyInput183.1 earlyInput183.2 true = (List.replicate 25 false) := by
  unfold earlyCompareFlags
  rw [hEC182,hEC183]
  decide +kernel
private theorem pairFlags_184_185_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput184.1 earlyInput184.2 earlyInput185.1 earlyInput185.2 true = (List.replicate 25 true) := by
  unfold earlyCompareFlags
  rw [hEC184,hEC185]
  decide +kernel
private theorem pairFlags_186_187_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput186.1 earlyInput186.2 earlyInput187.1 earlyInput187.2 true = (List.replicate 16 false) := by
  unfold earlyCompareFlags
  rw [hEC186,hEC187]
  decide +kernel
private theorem pairFlags_188_189_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput188.1 earlyInput188.2 earlyInput189.1 earlyInput189.2 true = (List.replicate 16 true) := by
  unfold earlyCompareFlags
  rw [hEC188,hEC189]
  decide +kernel
private theorem pairFlags_190_191_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput190.1 earlyInput190.2 earlyInput191.1 earlyInput191.2 true = (List.replicate 16 false) := by
  unfold earlyCompareFlags
  rw [hEC190,hEC191]
  decide +kernel
private theorem pairFlags_192_193_1 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput192.1 earlyInput192.2 earlyInput193.1 earlyInput193.2 true = (List.replicate 16 true) := by
  unfold earlyCompareFlags
  rw [hEC192,hEC193]
  decide +kernel
private theorem pairFlags_83_82_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput83.1 earlyInput83.2 earlyInput82.1 earlyInput82.2 false = (List.replicate 16 true) := by
  unfold earlyCompareFlags
  rw [hEC83,hEC82]
  decide +kernel
private theorem pairFlags_81_80_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput81.1 earlyInput81.2 earlyInput80.1 earlyInput80.2 false = (List.replicate 25 true) := by
  unfold earlyCompareFlags
  rw [hEC81,hEC80]
  decide +kernel
private theorem pairFlags_26_46_0 : earlyCompareFlags lowerEarlyTerminalState2 earlyInput26.1 earlyInput26.2 earlyInput46.1 earlyInput46.2 false = (List.replicate 16 true) := by
  unfold earlyCompareFlags
  rw [hEC26,hEC46]
  decide +kernel
private def earlyFlags : Array (List Bool) := #[(List.replicate 25 true),(List.replicate 16 true),(List.replicate 16 false),(List.replicate 16 false),(List.replicate 16 true),(List.replicate 16 true),(List.replicate 25 true),(List.replicate 25 false),(List.replicate 25 true),(List.replicate 25 false),(List.replicate 20 false),(List.replicate 5 false),(List.replicate 20 false),(List.replicate 20 true),(List.replicate 16 false),(List.replicate 16 true),(List.replicate 16 true),(List.replicate 25 false),(List.replicate 25 true),(List.replicate 25 false),(List.replicate 25 true),(List.replicate 25 true),(List.replicate 16 false),(List.replicate 16 true),(List.replicate 16 true),(List.replicate 16 false),(List.replicate 4 true),(List.replicate 10 true),(List.replicate 10 false),(List.replicate 10 true),(List.replicate 25 false),(List.replicate 4 true),(List.replicate 10 true),(List.replicate 10 false),(List.replicate 10 true),(List.replicate 10 false),(List.replicate 25 true),(List.replicate 16 true),(List.replicate 16 false),(List.replicate 16 false),(List.replicate 16 true),(List.replicate 16 true),(List.replicate 25 true),(List.replicate 25 false),(List.replicate 25 true),(List.replicate 25 false),(List.replicate 16 false),(List.replicate 4 false),(List.replicate 20 false),(List.replicate 20 true),(List.replicate 20 false),(List.replicate 5 true),(List.replicate 4 false),(List.replicate 4 true),(List.replicate 5 false),(List.replicate 20 false),(List.replicate 20 false),(List.replicate 20 true),(List.replicate 16 false),(List.replicate 16 true),(List.replicate 4 true),(List.replicate 4 true),(List.replicate 16 true),(List.replicate 10 true),(List.replicate 4 true),(List.replicate 25 true),(List.replicate 25 true),(List.replicate 25 true),(List.replicate 16 true),(List.replicate 4 true),(List.replicate 16 true),(List.replicate 4 true),(List.replicate 4 true),(List.replicate 4 false),(List.replicate 4 false),(List.replicate 4 false),(List.replicate 4 true),(List.replicate 8 false),(List.replicate 20 false),(List.replicate 10 false),(List.replicate 4 true),(List.replicate 10 false),(List.replicate 10 false),(List.replicate 25 false),(List.replicate 25 false),(List.replicate 20 false),(List.replicate 20 false),(List.replicate 16 false),(List.replicate 4 true),(List.replicate 4 false),(List.replicate 16 false),(List.replicate 16 false),(List.replicate 4 true),(List.replicate 4 false),(List.replicate 4 false),(List.replicate 20 false),(List.replicate 5 false),(List.replicate 20 false),(List.replicate 20 true),(List.replicate 16 false),(List.replicate 4 false),(List.replicate 16 false),(List.replicate 16 true),(List.replicate 20 false),(List.replicate 20 true),(List.replicate 25 false),(List.replicate 25 true),(List.replicate 4 false),(List.replicate 16 true),(List.replicate 1 false),(List.replicate 1 false),(List.replicate 1 false),(List.replicate 1 false),(List.replicate 1 false),(List.replicate 1 false),(List.replicate 1 false),(List.replicate 1 false),(List.replicate 1 false),(List.replicate 1 false),(List.replicate 1 false),(List.replicate 1 false),(List.replicate 1 false),(List.replicate 1 false),(List.replicate 1 false),(List.replicate 1 false),(List.replicate 25 false),(List.replicate 10 true),(List.replicate 10 false),(List.replicate 10 true),(List.replicate 25 false),(List.replicate 10 true),(List.replicate 10 false),(List.replicate 10 true),(List.replicate 25 false),(List.replicate 25 true),(List.replicate 25 false),(List.replicate 25 true),(List.replicate 16 false),(List.replicate 4 true),(List.replicate 4 false),(List.replicate 4 true),(List.replicate 4 false),(List.replicate 1 true),(List.replicate 4 false),(List.replicate 1 true),(List.replicate 16 false),(List.replicate 16 true),(List.replicate 16 false),(List.replicate 16 true),(List.replicate 16 false),(List.replicate 16 true),(List.replicate 16 false),(List.replicate 16 true),(List.replicate 16 false),(List.replicate 16 true),(List.replicate 16 false),(List.replicate 16 true),(List.replicate 25 false),(List.replicate 25 true),(List.replicate 25 false),(List.replicate 25 true),(List.replicate 10 false),(List.replicate 10 true),(List.replicate 25 false),(List.replicate 10 true),(List.replicate 25 false),(List.replicate 25 true),(List.replicate 25 false),(List.replicate 25 true),(List.replicate 25 false),(List.replicate 10 true),(List.replicate 10 false),(List.replicate 10 true),(List.replicate 10 false),(List.replicate 10 true),(List.replicate 25 false),(List.replicate 10 true),(List.replicate 10 false),(List.replicate 10 true),(List.replicate 10 false),(List.replicate 10 true),(List.replicate 25 false),(List.replicate 25 true),(List.replicate 25 false),(List.replicate 25 true),(List.replicate 16 false),(List.replicate 16 true),(List.replicate 16 false),(List.replicate 16 true),(List.replicate 1 false),(List.replicate 1 false),(List.replicate 1 false),(List.replicate 16 true),(List.replicate 25 true),(List.replicate 4 true),(List.replicate 16 true)]
private def earlyBuckets : Array (List ℕ) := #[[],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[],[],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19],[0,1,2,3,4],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24],[],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[],[],[0,1,2,3,4,5,6,7,8,9],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24],[],[],[0,1,2,3,4,5,6,7,8,9],[],[0,1,2,3,4,5,6,7,8,9],[],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[],[],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[0,1,2,3],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19],[],[0,1,2,3],[],[0,1,2,3,4],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[0,1,2,3],[0,1,2,3],[0,1,2,3],[],[0,1,2,3,4,5,6,7],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19],[0,1,2,3,4,5,6,7,8,9],[],[0,1,2,3,4,5,6,7,8,9],[0,1,2,3,4,5,6,7,8,9],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[],[0,1,2,3],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[],[0,1,2,3],[0,1,2,3],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19],[0,1,2,3,4],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[0,1,2,3],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24],[],[0,1,2,3],[],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24],[],[0,1,2,3,4,5,6,7,8,9],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24],[],[0,1,2,3,4,5,6,7,8,9],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[],[0,1,2,3],[],[0,1,2,3],[],[0,1,2,3],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24],[],[0,1,2,3,4,5,6,7,8,9],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24],[],[0,1,2,3,4,5,6,7,8,9],[],[0,1,2,3,4,5,6,7,8,9],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24],[],[0,1,2,3,4,5,6,7,8,9],[],[0,1,2,3,4,5,6,7,8,9],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[],[0],[0],[0],[],[],[],[]]
private theorem hEF0 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 0).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[0]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 0).kind = .compare earlyInput4.1 earlyInput4.2 earlyInput5.1 earlyInput5.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_4_5_0
private theorem hEF1 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 1).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[1]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 1).kind = .compare earlyInput6.1 earlyInput6.2 earlyInput7.1 earlyInput7.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_6_7_1
private theorem hEF2 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 2).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[2]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 2).kind = .compare earlyInput8.1 earlyInput8.2 earlyInput9.1 earlyInput9.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_8_9_1
private theorem hEF3 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 3).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[3]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 3).kind = .compare earlyInput10.1 earlyInput10.2 earlyInput11.1 earlyInput11.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_10_11_1
private theorem hEF4 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 4).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[4]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 4).kind = .compare earlyInput12.1 earlyInput12.2 earlyInput13.1 earlyInput13.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_12_13_1
private theorem hEF5 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 5).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[5]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 5).kind = .compare earlyInput14.1 earlyInput14.2 earlyInput15.1 earlyInput15.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_14_15_0
private theorem hEF6 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 6).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[6]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 6).kind = .compare earlyInput16.1 earlyInput16.2 earlyInput17.1 earlyInput17.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_16_17_1
private theorem hEF7 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 7).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[7]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 7).kind = .compare earlyInput18.1 earlyInput18.2 earlyInput19.1 earlyInput19.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_18_19_1
private theorem hEF8 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 8).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[8]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 8).kind = .compare earlyInput20.1 earlyInput20.2 earlyInput21.1 earlyInput21.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_20_21_1
private theorem hEF9 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 9).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[9]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 9).kind = .compare earlyInput22.1 earlyInput22.2 earlyInput23.1 earlyInput23.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_22_23_1
private theorem hEF10 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 10).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[10]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 10).kind = .compare earlyInput24.1 earlyInput24.2 earlyInput5.1 earlyInput5.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_24_5_0
private theorem hEF11 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 11).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[11]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 11).kind = .compare earlyInput4.1 earlyInput4.2 earlyInput25.1 earlyInput25.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_4_25_0
private theorem hEF12 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 12).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[12]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 12).kind = .compare earlyInput4.1 earlyInput4.2 earlyInput15.1 earlyInput15.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_4_15_0
private theorem hEF13 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 13).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[13]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 13).kind = .compare earlyInput14.1 earlyInput14.2 earlyInput5.1 earlyInput5.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_14_5_0
private theorem hEF14 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 14).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[14]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 14).kind = .compare earlyInput14.1 earlyInput14.2 earlyInput2.1 earlyInput2.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_14_2_0
private theorem hEF15 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 15).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[15]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 15).kind = .compare earlyInput26.1 earlyInput26.2 earlyInput15.1 earlyInput15.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_26_15_0
private theorem hEF16 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 16).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[16]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 16).kind = .compare earlyInput27.1 earlyInput27.2 earlyInput28.1 earlyInput28.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_27_28_0
private theorem hEF17 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 17).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[17]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 17).kind = .compare earlyInput3.1 earlyInput3.2 earlyInput29.1 earlyInput29.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_3_29_1
private theorem hEF18 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 18).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[18]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 18).kind = .compare earlyInput30.1 earlyInput30.2 earlyInput31.1 earlyInput31.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_30_31_1
private theorem hEF19 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 19).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[19]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 19).kind = .compare earlyInput32.1 earlyInput32.2 earlyInput33.1 earlyInput33.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_32_33_1
private theorem hEF20 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 20).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[20]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 20).kind = .compare earlyInput34.1 earlyInput34.2 earlyInput35.1 earlyInput35.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_34_35_1
private theorem hEF21 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 21).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[21]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 21).kind = .compare earlyInput36.1 earlyInput36.2 earlyInput37.1 earlyInput37.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_36_37_0
private theorem hEF22 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 22).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[22]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 22).kind = .compare earlyInput38.1 earlyInput38.2 earlyInput39.1 earlyInput39.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_38_39_1
private theorem hEF23 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 23).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[23]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 23).kind = .compare earlyInput40.1 earlyInput40.2 earlyInput41.1 earlyInput41.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_40_41_1
private theorem hEF24 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 24).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[24]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 24).kind = .compare earlyInput42.1 earlyInput42.2 earlyInput43.1 earlyInput43.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_42_43_1
private theorem hEF25 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 25).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[25]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 25).kind = .compare earlyInput44.1 earlyInput44.2 earlyInput45.1 earlyInput45.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_44_45_1
private theorem hEF26 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 26).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[26]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 26).kind = .compare earlyInput0.1 earlyInput0.2 earlyInput46.1 earlyInput46.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_0_46_0
private theorem hEF27 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 27).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[27]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 27).kind = .compare earlyInput47.1 earlyInput47.2 earlyInput48.1 earlyInput48.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_47_48_1
private theorem hEF28 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 28).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[28]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 28).kind = .compare earlyInput49.1 earlyInput49.2 earlyInput50.1 earlyInput50.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_49_50_1
private theorem hEF29 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 29).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[29]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 29).kind = .compare earlyInput51.1 earlyInput51.2 earlyInput52.1 earlyInput52.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_51_52_1
private theorem hEF30 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 30).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[30]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 30).kind = .compare earlyInput53.1 earlyInput53.2 earlyInput54.1 earlyInput54.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_53_54_1
private theorem hEF31 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 31).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[31]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 31).kind = .compare earlyInput55.1 earlyInput55.2 earlyInput1.1 earlyInput1.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_55_1_0
private theorem hEF32 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 32).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[32]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 32).kind = .compare earlyInput56.1 earlyInput56.2 earlyInput57.1 earlyInput57.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_56_57_1
private theorem hEF33 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 33).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[33]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 33).kind = .compare earlyInput58.1 earlyInput58.2 earlyInput59.1 earlyInput59.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_58_59_1
private theorem hEF34 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 34).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[34]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 34).kind = .compare earlyInput60.1 earlyInput60.2 earlyInput61.1 earlyInput61.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_60_61_1
private theorem hEF35 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 35).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[35]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 35).kind = .compare earlyInput62.1 earlyInput62.2 earlyInput63.1 earlyInput63.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_62_63_1
private theorem hEF36 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 36).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[36]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 36).kind = .compare earlyInput4.1 earlyInput4.2 earlyInput5.1 earlyInput5.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_4_5_0
private theorem hEF37 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 37).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[37]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 37).kind = .compare earlyInput6.1 earlyInput6.2 earlyInput7.1 earlyInput7.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_6_7_1
private theorem hEF38 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 38).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[38]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 38).kind = .compare earlyInput8.1 earlyInput8.2 earlyInput9.1 earlyInput9.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_8_9_1
private theorem hEF39 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 39).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[39]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 39).kind = .compare earlyInput10.1 earlyInput10.2 earlyInput11.1 earlyInput11.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_10_11_1
private theorem hEF40 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 40).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[40]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 40).kind = .compare earlyInput12.1 earlyInput12.2 earlyInput13.1 earlyInput13.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_12_13_1
private theorem hEF41 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 41).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[41]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 41).kind = .compare earlyInput14.1 earlyInput14.2 earlyInput15.1 earlyInput15.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_14_15_0
private theorem hEF42 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 42).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[42]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 42).kind = .compare earlyInput16.1 earlyInput16.2 earlyInput17.1 earlyInput17.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_16_17_1
private theorem hEF43 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 43).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[43]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 43).kind = .compare earlyInput18.1 earlyInput18.2 earlyInput19.1 earlyInput19.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_18_19_1
private theorem hEF44 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 44).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[44]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 44).kind = .compare earlyInput20.1 earlyInput20.2 earlyInput21.1 earlyInput21.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_20_21_1
private theorem hEF45 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 45).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[45]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 45).kind = .compare earlyInput22.1 earlyInput22.2 earlyInput23.1 earlyInput23.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_22_23_1
private theorem hEF46 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 46).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[46]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 46).kind = .compare earlyInput24.1 earlyInput24.2 earlyInput28.1 earlyInput28.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_24_28_0
private theorem hEF47 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 47).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[47]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 47).kind = .compare earlyInput27.1 earlyInput27.2 earlyInput25.1 earlyInput25.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_27_25_0
private theorem hEF48 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 48).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[48]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 48).kind = .compare earlyInput27.1 earlyInput27.2 earlyInput37.1 earlyInput37.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_27_37_0
private theorem hEF49 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 49).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[49]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 49).kind = .compare earlyInput36.1 earlyInput36.2 earlyInput28.1 earlyInput28.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_36_28_0
private theorem hEF50 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 50).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[50]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 50).kind = .compare earlyInput36.1 earlyInput36.2 earlyInput46.1 earlyInput46.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_36_46_0
private theorem hEF51 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 51).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[51]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 51).kind = .compare earlyInput0.1 earlyInput0.2 earlyInput37.1 earlyInput37.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_0_37_0
private theorem hEF52 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 52).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[52]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 52).kind = .compare earlyInput0.1 earlyInput0.2 earlyInput1.1 earlyInput1.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_0_1_0
private theorem hEF53 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 53).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[53]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 53).kind = .compare earlyInput55.1 earlyInput55.2 earlyInput46.1 earlyInput46.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_55_46_0
private theorem hEF54 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 54).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[54]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 54).kind = .compare earlyInput55.1 earlyInput55.2 earlyInput5.1 earlyInput5.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_55_5_0
private theorem hEF55 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 55).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[55]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 55).kind = .compare earlyInput4.1 earlyInput4.2 earlyInput1.1 earlyInput1.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_4_1_0
private theorem hEF56 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 56).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[56]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 56).kind = .compare earlyInput4.1 earlyInput4.2 earlyInput15.1 earlyInput15.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_4_15_0
private theorem hEF57 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 57).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[57]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 57).kind = .compare earlyInput14.1 earlyInput14.2 earlyInput5.1 earlyInput5.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_14_5_0
private theorem hEF58 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 58).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[58]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 58).kind = .compare earlyInput14.1 earlyInput14.2 earlyInput2.1 earlyInput2.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_14_2_0
private theorem hEF59 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 59).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[59]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 59).kind = .compare earlyInput26.1 earlyInput26.2 earlyInput15.1 earlyInput15.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_26_15_0
private theorem hEF60 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 60).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[60]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 60).kind = .compare earlyInput64.1 earlyInput64.2 earlyInput65.1 earlyInput65.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_64_65_0
private theorem hEF61 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 61).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[61]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 61).kind = .compare earlyInput66.1 earlyInput66.2 earlyInput67.1 earlyInput67.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_66_67_0
private theorem hEF62 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 62).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[62]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 62).kind = .compare earlyInput68.1 earlyInput68.2 earlyInput69.1 earlyInput69.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_68_69_0
private theorem hEF63 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 63).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[63]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 63).kind = .compare earlyInput70.1 earlyInput70.2 earlyInput71.1 earlyInput71.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_70_71_0
private theorem hEF64 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 64).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[64]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 64).kind = .compare earlyInput72.1 earlyInput72.2 earlyInput73.1 earlyInput73.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_72_73_0
private theorem hEF65 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 65).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[65]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 65).kind = .compare earlyInput74.1 earlyInput74.2 earlyInput75.1 earlyInput75.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_74_75_0
private theorem hEF66 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 66).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[66]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 66).kind = .compare earlyInput3.1 earlyInput3.2 earlyInput31.1 earlyInput31.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_3_31_0
private theorem hEF67 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 67).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[67]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 67).kind = .compare earlyInput30.1 earlyInput30.2 earlyInput29.1 earlyInput29.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_30_29_0
private theorem hEF68 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 68).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[68]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 68).kind = .compare earlyInput38.1 earlyInput38.2 earlyInput41.1 earlyInput41.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_38_41_0
private theorem hEF69 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 69).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[69]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 69).kind = .compare earlyInput76.1 earlyInput76.2 earlyInput77.1 earlyInput77.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_76_77_0
private theorem hEF70 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 70).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[70]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 70).kind = .compare earlyInput40.1 earlyInput40.2 earlyInput39.1 earlyInput39.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_40_39_0
private theorem hEF71 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 71).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[71]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 71).kind = .compare earlyInput78.1 earlyInput78.2 earlyInput79.1 earlyInput79.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_78_79_0
private theorem hEF72 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 72).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[72]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 72).kind = .compare earlyInput0.1 earlyInput0.2 earlyInput46.1 earlyInput46.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_0_46_0
private theorem hEF73 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 73).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[73]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 73).kind = .compare earlyInput24.1 earlyInput24.2 earlyInput65.1 earlyInput65.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_24_65_0
private theorem hEF74 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 74).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[74]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 74).kind = .compare earlyInput64.1 earlyInput64.2 earlyInput25.1 earlyInput25.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_64_25_0
private theorem hEF75 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 75).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[75]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 75).kind = .compare earlyInput64.1 earlyInput64.2 earlyInput67.1 earlyInput67.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_64_67_0
private theorem hEF76 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 76).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[76]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 76).kind = .compare earlyInput66.1 earlyInput66.2 earlyInput65.1 earlyInput65.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_66_65_0
private theorem hEF77 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 77).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[77]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 77).kind = .compare earlyInput68.1 earlyInput68.2 earlyInput71.1 earlyInput71.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_68_71_0
private theorem hEF78 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 78).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[78]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 78).kind = .compare earlyInput70.1 earlyInput70.2 earlyInput69.1 earlyInput69.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_70_69_0
private theorem hEF79 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 79).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[79]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 79).kind = .compare earlyInput70.1 earlyInput70.2 earlyInput73.1 earlyInput73.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_70_73_0
private theorem hEF80 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 80).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[80]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 80).kind = .compare earlyInput72.1 earlyInput72.2 earlyInput71.1 earlyInput71.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_72_71_0
private theorem hEF81 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 81).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[81]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 81).kind = .compare earlyInput72.1 earlyInput72.2 earlyInput75.1 earlyInput75.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_72_75_0
private theorem hEF82 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 82).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[82]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 82).kind = .compare earlyInput74.1 earlyInput74.2 earlyInput73.1 earlyInput73.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_74_73_0
private theorem hEF83 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 83).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[83]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 83).kind = .compare earlyInput74.1 earlyInput74.2 earlyInput31.1 earlyInput31.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_74_31_0
private theorem hEF84 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 84).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[84]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 84).kind = .compare earlyInput3.1 earlyInput3.2 earlyInput75.1 earlyInput75.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_3_75_0
private theorem hEF85 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 85).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[85]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 85).kind = .compare earlyInput30.1 earlyInput30.2 earlyInput41.1 earlyInput41.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_30_41_0
private theorem hEF86 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 86).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[86]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 86).kind = .compare earlyInput38.1 earlyInput38.2 earlyInput29.1 earlyInput29.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_38_29_0
private theorem hEF87 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 87).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[87]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 87).kind = .compare earlyInput38.1 earlyInput38.2 earlyInput77.1 earlyInput77.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_38_77_0
private theorem hEF88 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 88).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[88]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 88).kind = .compare earlyInput76.1 earlyInput76.2 earlyInput41.1 earlyInput41.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_76_41_0
private theorem hEF89 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 89).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[89]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 89).kind = .compare earlyInput76.1 earlyInput76.2 earlyInput39.1 earlyInput39.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_76_39_0
private theorem hEF90 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 90).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[90]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 90).kind = .compare earlyInput40.1 earlyInput40.2 earlyInput77.1 earlyInput77.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_40_77_0
private theorem hEF91 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 91).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[91]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 91).kind = .compare earlyInput40.1 earlyInput40.2 earlyInput79.1 earlyInput79.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_40_79_0
private theorem hEF92 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 92).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[92]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 92).kind = .compare earlyInput78.1 earlyInput78.2 earlyInput39.1 earlyInput39.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_78_39_0
private theorem hEF93 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 93).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[93]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 93).kind = .compare earlyInput78.1 earlyInput78.2 earlyInput46.1 earlyInput46.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_78_46_0
private theorem hEF94 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 94).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[94]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 94).kind = .compare earlyInput0.1 earlyInput0.2 earlyInput79.1 earlyInput79.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_0_79_0
private theorem hEF95 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 95).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[95]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 95).kind = .compare earlyInput66.1 earlyInput66.2 earlyInput80.1 earlyInput80.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_66_80_0
private theorem hEF96 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 96).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[96]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 96).kind = .compare earlyInput81.1 earlyInput81.2 earlyInput67.1 earlyInput67.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_81_67_0
private theorem hEF97 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 97).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[97]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 97).kind = .compare earlyInput81.1 earlyInput81.2 earlyInput69.1 earlyInput69.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_81_69_0
private theorem hEF98 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 98).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[98]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 98).kind = .compare earlyInput68.1 earlyInput68.2 earlyInput80.1 earlyInput80.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_68_80_0
private theorem hEF99 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 99).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[99]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 99).kind = .compare earlyInput66.1 earlyInput66.2 earlyInput82.1 earlyInput82.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_66_82_0
private theorem hEF100 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 100).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[100]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 100).kind = .compare earlyInput83.1 earlyInput83.2 earlyInput67.1 earlyInput67.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_83_67_0
private theorem hEF101 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 101).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[101]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 101).kind = .compare earlyInput83.1 earlyInput83.2 earlyInput69.1 earlyInput69.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_83_69_0
private theorem hEF102 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 102).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[102]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 102).kind = .compare earlyInput68.1 earlyInput68.2 earlyInput82.1 earlyInput82.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_68_82_0
private theorem hEF103 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 103).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[103]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 103).kind = .compare earlyInput3.1 earlyInput3.2 earlyInput41.1 earlyInput41.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_3_41_0
private theorem hEF104 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 104).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[104]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 104).kind = .compare earlyInput38.1 earlyInput38.2 earlyInput31.1 earlyInput31.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_38_31_0
private theorem hEF105 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 105).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[105]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 105).kind = .compare earlyInput3.1 earlyInput3.2 earlyInput29.1 earlyInput29.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_3_29_0
private theorem hEF106 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 106).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[106]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 106).kind = .compare earlyInput30.1 earlyInput30.2 earlyInput31.1 earlyInput31.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_30_31_0
private theorem hEF107 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 107).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[107]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 107).kind = .compare earlyInput55.1 earlyInput55.2 earlyInput2.1 earlyInput2.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_55_2_0
private theorem hEF108 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 108).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[108]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 108).kind = .compare earlyInput26.1 earlyInput26.2 earlyInput1.1 earlyInput1.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_26_1_0
private theorem hEF109 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 109).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[109]?.getD [] := by
  decide +kernel
private theorem hEF110 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 110).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[110]?.getD [] := by
  decide +kernel
private theorem hEF111 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 111).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[111]?.getD [] := by
  decide +kernel
private theorem hEF112 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 112).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[112]?.getD [] := by
  decide +kernel
private theorem hEF113 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 113).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[113]?.getD [] := by
  decide +kernel
private theorem hEF114 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 114).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[114]?.getD [] := by
  decide +kernel
private theorem hEF115 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 115).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[115]?.getD [] := by
  decide +kernel
private theorem hEF116 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 116).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[116]?.getD [] := by
  decide +kernel
private theorem hEF117 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 117).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[117]?.getD [] := by
  decide +kernel
private theorem hEF118 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 118).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[118]?.getD [] := by
  decide +kernel
private theorem hEF119 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 119).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[119]?.getD [] := by
  decide +kernel
private theorem hEF120 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 120).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[120]?.getD [] := by
  decide +kernel
private theorem hEF121 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 121).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[121]?.getD [] := by
  decide +kernel
private theorem hEF122 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 122).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[122]?.getD [] := by
  decide +kernel
private theorem hEF123 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 123).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[123]?.getD [] := by
  decide +kernel
private theorem hEF124 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 124).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[124]?.getD [] := by
  decide +kernel
private theorem hEF125 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 125).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[125]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 125).kind = .compare earlyInput84.1 earlyInput84.2 earlyInput85.1 earlyInput85.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_84_85_1
private theorem hEF126 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 126).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[126]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 126).kind = .compare earlyInput86.1 earlyInput86.2 earlyInput87.1 earlyInput87.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_86_87_1
private theorem hEF127 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 127).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[127]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 127).kind = .compare earlyInput88.1 earlyInput88.2 earlyInput89.1 earlyInput89.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_88_89_1
private theorem hEF128 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 128).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[128]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 128).kind = .compare earlyInput90.1 earlyInput90.2 earlyInput91.1 earlyInput91.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_90_91_1
private theorem hEF129 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 129).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[129]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 129).kind = .compare earlyInput92.1 earlyInput92.2 earlyInput93.1 earlyInput93.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_92_93_1
private theorem hEF130 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 130).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[130]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 130).kind = .compare earlyInput94.1 earlyInput94.2 earlyInput95.1 earlyInput95.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_94_95_1
private theorem hEF131 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 131).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[131]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 131).kind = .compare earlyInput96.1 earlyInput96.2 earlyInput97.1 earlyInput97.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_96_97_1
private theorem hEF132 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 132).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[132]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 132).kind = .compare earlyInput98.1 earlyInput98.2 earlyInput99.1 earlyInput99.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_98_99_1
private theorem hEF133 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 133).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[133]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 133).kind = .compare earlyInput100.1 earlyInput100.2 earlyInput101.1 earlyInput101.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_100_101_1
private theorem hEF134 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 134).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[134]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 134).kind = .compare earlyInput102.1 earlyInput102.2 earlyInput103.1 earlyInput103.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_102_103_1
private theorem hEF135 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 135).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[135]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 135).kind = .compare earlyInput104.1 earlyInput104.2 earlyInput105.1 earlyInput105.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_104_105_1
private theorem hEF136 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 136).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[136]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 136).kind = .compare earlyInput106.1 earlyInput106.2 earlyInput107.1 earlyInput107.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_106_107_1
private theorem hEF137 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 137).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[137]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 137).kind = .compare earlyInput108.1 earlyInput108.2 earlyInput109.1 earlyInput109.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_108_109_1
private theorem hEF138 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 138).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[138]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 138).kind = .compare earlyInput110.1 earlyInput110.2 earlyInput111.1 earlyInput111.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_110_111_1
private theorem hEF139 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 139).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[139]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 139).kind = .compare earlyInput112.1 earlyInput112.2 earlyInput113.1 earlyInput113.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_112_113_1
private theorem hEF140 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 140).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[140]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 140).kind = .compare earlyInput114.1 earlyInput114.2 earlyInput115.1 earlyInput115.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_114_115_1
private theorem hEF141 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 141).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[141]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 141).kind = .compare earlyInput116.1 earlyInput116.2 earlyInput117.1 earlyInput117.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_116_117_1
private theorem hEF142 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 142).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[142]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 142).kind = .compare earlyInput118.1 earlyInput118.2 earlyInput119.1 earlyInput119.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_118_119_1
private theorem hEF143 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 143).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[143]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 143).kind = .compare earlyInput120.1 earlyInput120.2 earlyInput121.1 earlyInput121.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_120_121_1
private theorem hEF144 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 144).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[144]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 144).kind = .compare earlyInput122.1 earlyInput122.2 earlyInput123.1 earlyInput123.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_122_123_1
private theorem hEF145 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 145).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[145]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 145).kind = .compare earlyInput124.1 earlyInput124.2 earlyInput125.1 earlyInput125.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_124_125_1
private theorem hEF146 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 146).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[146]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 146).kind = .compare earlyInput126.1 earlyInput126.2 earlyInput127.1 earlyInput127.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_126_127_1
private theorem hEF147 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 147).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[147]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 147).kind = .compare earlyInput128.1 earlyInput128.2 earlyInput129.1 earlyInput129.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_128_129_1
private theorem hEF148 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 148).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[148]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 148).kind = .compare earlyInput130.1 earlyInput130.2 earlyInput131.1 earlyInput131.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_130_131_1
private theorem hEF149 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 149).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[149]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 149).kind = .compare earlyInput132.1 earlyInput132.2 earlyInput133.1 earlyInput133.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_132_133_1
private theorem hEF150 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 150).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[150]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 150).kind = .compare earlyInput134.1 earlyInput134.2 earlyInput135.1 earlyInput135.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_134_135_1
private theorem hEF151 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 151).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[151]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 151).kind = .compare earlyInput136.1 earlyInput136.2 earlyInput137.1 earlyInput137.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_136_137_1
private theorem hEF152 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 152).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[152]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 152).kind = .compare earlyInput138.1 earlyInput138.2 earlyInput139.1 earlyInput139.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_138_139_1
private theorem hEF153 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 153).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[153]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 153).kind = .compare earlyInput140.1 earlyInput140.2 earlyInput141.1 earlyInput141.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_140_141_1
private theorem hEF154 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 154).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[154]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 154).kind = .compare earlyInput142.1 earlyInput142.2 earlyInput143.1 earlyInput143.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_142_143_1
private theorem hEF155 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 155).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[155]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 155).kind = .compare earlyInput144.1 earlyInput144.2 earlyInput145.1 earlyInput145.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_144_145_1
private theorem hEF156 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 156).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[156]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 156).kind = .compare earlyInput146.1 earlyInput146.2 earlyInput147.1 earlyInput147.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_146_147_1
private theorem hEF157 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 157).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[157]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 157).kind = .compare earlyInput148.1 earlyInput148.2 earlyInput149.1 earlyInput149.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_148_149_1
private theorem hEF158 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 158).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[158]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 158).kind = .compare earlyInput150.1 earlyInput150.2 earlyInput151.1 earlyInput151.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_150_151_1
private theorem hEF159 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 159).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[159]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 159).kind = .compare earlyInput152.1 earlyInput152.2 earlyInput153.1 earlyInput153.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_152_153_1
private theorem hEF160 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 160).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[160]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 160).kind = .compare earlyInput154.1 earlyInput154.2 earlyInput155.1 earlyInput155.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_154_155_1
private theorem hEF161 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 161).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[161]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 161).kind = .compare earlyInput156.1 earlyInput156.2 earlyInput157.1 earlyInput157.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_156_157_1
private theorem hEF162 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 162).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[162]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 162).kind = .compare earlyInput158.1 earlyInput158.2 earlyInput159.1 earlyInput159.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_158_159_1
private theorem hEF163 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 163).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[163]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 163).kind = .compare earlyInput160.1 earlyInput160.2 earlyInput161.1 earlyInput161.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_160_161_1
private theorem hEF164 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 164).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[164]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 164).kind = .compare earlyInput162.1 earlyInput162.2 earlyInput163.1 earlyInput163.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_162_163_1
private theorem hEF165 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 165).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[165]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 165).kind = .compare earlyInput164.1 earlyInput164.2 earlyInput165.1 earlyInput165.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_164_165_1
private theorem hEF166 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 166).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[166]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 166).kind = .compare earlyInput166.1 earlyInput166.2 earlyInput167.1 earlyInput167.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_166_167_1
private theorem hEF167 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 167).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[167]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 167).kind = .compare earlyInput168.1 earlyInput168.2 earlyInput169.1 earlyInput169.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_168_169_1
private theorem hEF168 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 168).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[168]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 168).kind = .compare earlyInput170.1 earlyInput170.2 earlyInput171.1 earlyInput171.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_170_171_1
private theorem hEF169 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 169).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[169]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 169).kind = .compare earlyInput172.1 earlyInput172.2 earlyInput173.1 earlyInput173.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_172_173_1
private theorem hEF170 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 170).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[170]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 170).kind = .compare earlyInput174.1 earlyInput174.2 earlyInput175.1 earlyInput175.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_174_175_1
private theorem hEF171 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 171).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[171]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 171).kind = .compare earlyInput176.1 earlyInput176.2 earlyInput177.1 earlyInput177.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_176_177_1
private theorem hEF172 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 172).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[172]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 172).kind = .compare earlyInput178.1 earlyInput178.2 earlyInput179.1 earlyInput179.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_178_179_1
private theorem hEF173 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 173).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[173]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 173).kind = .compare earlyInput49.1 earlyInput49.2 earlyInput50.1 earlyInput50.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_49_50_1
private theorem hEF174 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 174).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[174]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 174).kind = .compare earlyInput47.1 earlyInput47.2 earlyInput48.1 earlyInput48.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_47_48_1
private theorem hEF175 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 175).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[175]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 175).kind = .compare earlyInput53.1 earlyInput53.2 earlyInput54.1 earlyInput54.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_53_54_1
private theorem hEF176 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 176).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[176]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 176).kind = .compare earlyInput51.1 earlyInput51.2 earlyInput52.1 earlyInput52.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_51_52_1
private theorem hEF177 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 177).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[177]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 177).kind = .compare earlyInput58.1 earlyInput58.2 earlyInput59.1 earlyInput59.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_58_59_1
private theorem hEF178 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 178).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[178]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 178).kind = .compare earlyInput56.1 earlyInput56.2 earlyInput57.1 earlyInput57.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_56_57_1
private theorem hEF179 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 179).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[179]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 179).kind = .compare earlyInput62.1 earlyInput62.2 earlyInput63.1 earlyInput63.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_62_63_1
private theorem hEF180 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 180).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[180]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 180).kind = .compare earlyInput60.1 earlyInput60.2 earlyInput61.1 earlyInput61.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_60_61_1
private theorem hEF181 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 181).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[181]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 181).kind = .compare earlyInput81.1 earlyInput81.2 earlyInput180.1 earlyInput180.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_81_180_1
private theorem hEF182 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 182).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[182]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 182).kind = .compare earlyInput181.1 earlyInput181.2 earlyInput80.1 earlyInput80.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_181_80_1
private theorem hEF183 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 183).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[183]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 183).kind = .compare earlyInput182.1 earlyInput182.2 earlyInput183.1 earlyInput183.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_182_183_1
private theorem hEF184 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 184).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[184]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 184).kind = .compare earlyInput184.1 earlyInput184.2 earlyInput185.1 earlyInput185.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_184_185_1
private theorem hEF185 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 185).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[185]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 185).kind = .compare earlyInput186.1 earlyInput186.2 earlyInput187.1 earlyInput187.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_186_187_1
private theorem hEF186 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 186).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[186]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 186).kind = .compare earlyInput188.1 earlyInput188.2 earlyInput189.1 earlyInput189.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_188_189_1
private theorem hEF187 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 187).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[187]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 187).kind = .compare earlyInput190.1 earlyInput190.2 earlyInput191.1 earlyInput191.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_190_191_1
private theorem hEF188 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 188).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[188]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 188).kind = .compare earlyInput192.1 earlyInput192.2 earlyInput193.1 earlyInput193.2 true := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_192_193_1
private theorem hEF189 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 189).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[189]?.getD [] := by
  decide +kernel
private theorem hEF190 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 190).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[190]?.getD [] := by
  decide +kernel
private theorem hEF191 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 191).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[191]?.getD [] := by
  decide +kernel
private theorem hEF192 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 192).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[192]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 192).kind = .compare earlyInput83.1 earlyInput83.2 earlyInput82.1 earlyInput82.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_83_82_0
private theorem hEF193 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 193).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[193]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 193).kind = .compare earlyInput81.1 earlyInput81.2 earlyInput80.1 earlyInput80.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_81_80_0
private theorem hEF194 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 194).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[194]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 194).kind = .compare earlyInput55.1 earlyInput55.2 earlyInput1.1 earlyInput1.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_55_1_0
private theorem hEF195 : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 195).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[195]?.getD [] := by
  have hk : (lowerEarlyTerminalGoal lowerEarlyTerminalState2 195).kind = .compare earlyInput26.1 earlyInput26.2 earlyInput46.1 earlyInput46.2 false := by decide +kernel
  rw [hk]
  exact (earlyCompareFlags_eq _ _ _ _ _ _).symm.trans pairFlags_26_46_0
private theorem earlyLength : lowerEarlyTerminalState2.goals.length = 196 := by decide +kernel
private theorem hEFlags (g : ℕ) (hg : g<196) : (lowerEarlyTerminalBranches lowerEarlyTerminalState2 (lowerEarlyTerminalGoal lowerEarlyTerminalState2 g).kind).map (fun z => decide (z.2=LowerHistoryComparison.automatic)) = earlyFlags[g]?.getD [] := by
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
  · exact hEF168
  · exact hEF169
  · exact hEF170
  · exact hEF171
  · exact hEF172
  · exact hEF173
  · exact hEF174
  · exact hEF175
  · exact hEF176
  · exact hEF177
  · exact hEF178
  · exact hEF179
  · exact hEF180
  · exact hEF181
  · exact hEF182
  · exact hEF183
  · exact hEF184
  · exact hEF185
  · exact hEF186
  · exact hEF187
  · exact hEF188
  · exact hEF189
  · exact hEF190
  · exact hEF191
  · exact hEF192
  · exact hEF193
  · exact hEF194
  · exact hEF195
private theorem hEBuckets : earlyRecordKeys lowerEarlyTerminalState2 = earlyBucketKeys 196 earlyBuckets := by decide +kernel
private theorem hECovered : ∀ g ∈ List.range 196, ∀ bj ∈ (earlyFlags[g]?.getD []).zipIdx, bj.1=true ∨ bj.2 ∈ earlyBuckets[g]?.getD [] := by decide +kernel

theorem solution : lowerEarlyTerminalCoverage lowerEarlyTerminalState2 :=
  earlyCoverageGrouped_sound _ 196 earlyFlags earlyBuckets earlyLength hEFlags hEBuckets hECovered
#print axioms solution
