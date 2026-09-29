-- Prove2me | solution 1 for Freiman.trunk_bindings_09_000_100
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:23:12.648118+00:00
-- url     : https://prove2.me/submissions/0cb7f5ec-c093-4329-8f33-b95b370fadbd

import Definitions.Def_Freiman_trunkFast
import Theorems.Thm_Freiman_trunkFast_correctness
set_option Elab.async false
open Freiman Freiman.TrunkFast
private abbrev bc0 : ℕ × Bool × Bool := (3, false, false)
private abbrev bc1 : ℕ × Bool × Bool := (3, true, true)
private abbrev bc2 : ℕ × Bool × Bool := (30, false, false)
private abbrev bc3 : ℕ × Bool × Bool := (29, false, true)
private abbrev bc4 : ℕ × Bool × Bool := (29, true, false)
private abbrev bc5 : ℕ × Bool × Bool := (30, true, true)
private abbrev bc6 : ℕ × Bool × Bool := (147, true, true)
private abbrev bc7 : ℕ × Bool × Bool := (147, false, false)
private abbrev bc8 : ℕ × Bool × Bool := (10, false, false)
private abbrev bc9 : ℕ × Bool × Bool := (4, false, false)
private abbrev bc10 : ℕ × Bool × Bool := (9, false, true)
private abbrev bc11 : ℕ × Bool × Bool := (9, true, false)
private abbrev bc12 : ℕ × Bool × Bool := (4, true, true)
private abbrev bc13 : ℕ × Bool × Bool := (26, true, true)
private abbrev bc14 : ℕ × Bool × Bool := (26, false, false)
private abbrev bc15 : ℕ × Bool × Bool := (10, true, true)
private abbrev bc16 : ℕ × Bool × Bool := (6, false, false)
private abbrev bc17 : ℕ × Bool × Bool := (2, false, true)
private abbrev bc18 : ℕ × Bool × Bool := (2, true, false)
private abbrev bc19 : ℕ × Bool × Bool := (6, true, true)
private abbrev bc20 : ℕ × Bool × Bool := (13, true, true)
private abbrev bc21 : ℕ × Bool × Bool := (13, false, false)
private abbrev bc22 : ℕ × Bool × Bool := (33, false, true)
private abbrev bc23 : ℕ × Bool × Bool := (33, true, false)
private abbrev bc24 : ℕ × Bool × Bool := (45, true, true)
private abbrev bc25 : ℕ × Bool × Bool := (45, false, false)
private abbrev bc26 : ℕ × Bool × Bool := (32, false, false)
private abbrev bc27 : ℕ × Bool × Bool := (31, false, true)
private abbrev bc28 : ℕ × Bool × Bool := (31, true, false)
private abbrev bc29 : ℕ × Bool × Bool := (32, true, true)
private abbrev bc30 : ℕ × Bool × Bool := (37, true, true)
private abbrev bc31 : ℕ × Bool × Bool := (37, false, false)
private abbrev bc32 : ℕ × Bool × Bool := (18, false, true)
private abbrev bc33 : ℕ × Bool × Bool := (18, true, false)
private abbrev bc34 : ℕ × Bool × Bool := (69, false, true)
private abbrev bc35 : ℕ × Bool × Bool := (69, true, false)
private abbrev bc36 : ℕ × Bool × Bool := (83, true, true)
private abbrev bc37 : ℕ × Bool × Bool := (83, false, false)
private abbrev bc38 : ℕ × Bool × Bool := (72, false, false)
private abbrev bc39 : ℕ × Bool × Bool := (70, false, true)
private abbrev bc40 : ℕ × Bool × Bool := (70, true, false)
private abbrev bc41 : ℕ × Bool × Bool := (72, true, true)
private abbrev bc42 : ℕ × Bool × Bool := (75, true, true)
private abbrev bc43 : ℕ × Bool × Bool := (75, false, false)
private abbrev bc44 : ℕ × Bool × Bool := (89, false, true)
private abbrev bc45 : ℕ × Bool × Bool := (91, false, true)
private abbrev bc46 : ℕ × Bool × Bool := (91, true, false)
private abbrev bc47 : ℕ × Bool × Bool := (89, true, false)
private abbrev bc48 : ℕ × Bool × Bool := (102, true, true)
private abbrev bc49 : ℕ × Bool × Bool := (102, false, false)
private abbrev bc50 : ℕ × Bool × Bool := (30, false, true)
private abbrev bc51 : ℕ × Bool × Bool := (90, false, true)
private abbrev bc52 : ℕ × Bool × Bool := (90, true, false)
private abbrev bc53 : ℕ × Bool × Bool := (30, true, false)
private abbrev bc54 : ℕ × Bool × Bool := (95, true, true)
private abbrev bc55 : ℕ × Bool × Bool := (95, false, false)
private abbrev bc56 : ℕ × Bool × Bool := (109, false, false)
private abbrev bc57 : ℕ × Bool × Bool := (113, false, true)
private abbrev bc58 : ℕ × Bool × Bool := (113, true, false)
private abbrev bc59 : ℕ × Bool × Bool := (109, true, true)
private abbrev bc60 : ℕ × Bool × Bool := (125, true, true)
private abbrev bc61 : ℕ × Bool × Bool := (125, false, false)
private abbrev bc62 : ℕ × Bool × Bool := (112, false, false)
private abbrev bc63 : ℕ × Bool × Bool := (108, false, true)
private abbrev bc64 : ℕ × Bool × Bool := (108, true, false)
private abbrev bc65 : ℕ × Bool × Bool := (112, true, true)
private abbrev bc66 : ℕ × Bool × Bool := (117, true, true)
private abbrev bc67 : ℕ × Bool × Bool := (117, false, false)
private abbrev bc68 : ℕ × Bool × Bool := (132, false, true)
private abbrev bc69 : ℕ × Bool × Bool := (133, false, true)
private abbrev bc70 : ℕ × Bool × Bool := (133, true, false)
private abbrev bc71 : ℕ × Bool × Bool := (132, true, false)
private abbrev bc72 : ℕ × Bool × Bool := (136, true, true)
private abbrev bc73 : ℕ × Bool × Bool := (136, false, false)
private abbrev bc74 : ℕ × Bool × Bool := (110, false, false)
private abbrev bc75 : ℕ × Bool × Bool := (110, true, true)
private abbrev bc76 : ℕ × Bool × Bool := (156, false, false)
private abbrev bc77 : ℕ × Bool × Bool := (155, false, true)
private abbrev bc78 : ℕ × Bool × Bool := (155, true, false)
private abbrev bc79 : ℕ × Bool × Bool := (156, true, true)
private abbrev bc80 : ℕ × Bool × Bool := (162, true, true)
private abbrev bc81 : ℕ × Bool × Bool := (162, false, false)
private abbrev bc82 : ℕ × Bool × Bool := (183, false, false)
private abbrev bc83 : ℕ × Bool × Bool := (182, false, false)
private abbrev bc84 : ℕ × Bool × Bool := (179, false, true)
private abbrev bc85 : ℕ × Bool × Bool := (179, true, false)
private abbrev bc86 : ℕ × Bool × Bool := (182, true, true)
private abbrev bc87 : ℕ × Bool × Bool := (197, true, true)
private abbrev bc88 : ℕ × Bool × Bool := (197, false, false)
private abbrev bc89 : ℕ × Bool × Bool := (183, true, true)
private abbrev bc90 : ℕ × Bool × Bool := (181, false, false)
private abbrev bc91 : ℕ × Bool × Bool := (181, true, true)
private abbrev bc92 : ℕ × Bool × Bool := (184, false, false)
private abbrev bc93 : ℕ × Bool × Bool := (186, false, true)
private abbrev bc94 : ℕ × Bool × Bool := (186, true, false)
private abbrev bc95 : ℕ × Bool × Bool := (184, true, true)
private abbrev bc96 : ℕ × Bool × Bool := (189, true, true)
private abbrev bc97 : ℕ × Bool × Bool := (189, false, false)
private abbrev bc98 : ℕ × Bool × Bool := (206, true, false)
private abbrev bc99 : ℕ × Bool × Bool := (210, false, true)
private abbrev bc100 : ℕ × Bool × Bool := (210, true, false)
private abbrev bc101 : ℕ × Bool × Bool := (205, false, true)
private abbrev bc102 : ℕ × Bool × Bool := (205, true, false)
private abbrev bc103 : ℕ × Bool × Bool := (132, false, false)
private abbrev bc104 : ℕ × Bool × Bool := (132, true, true)
private abbrev bc105 : ℕ × Bool × Bool := (8, false, false)
private abbrev bc106 : ℕ × Bool × Bool := (8, true, true)
private abbrev bc107 : ℕ × Bool × Bool := (233, false, false)
private abbrev bc108 : ℕ × Bool × Bool := (233, true, true)
private abbrev bc109 : ℕ × Bool × Bool := (234, false, false)
private abbrev bc110 : ℕ × Bool × Bool := (236, false, false)
private abbrev bc111 : ℕ × Bool × Bool := (236, true, true)
private abbrev bc112 : ℕ × Bool × Bool := (246, false, true)
private abbrev bc113 : ℕ × Bool × Bool := (246, true, false)
private abbrev bc114 : ℕ × Bool × Bool := (248, true, false)
private abbrev bc115 : ℕ × Bool × Bool := (251, false, true)
private abbrev bc116 : ℕ × Bool × Bool := (251, true, false)
private abbrev bc117 : ℕ × Bool × Bool := (260, false, false)
private abbrev bc118 : ℕ × Bool × Bool := (261, false, false)
private abbrev bc119 : ℕ × Bool × Bool := (261, true, true)
private abbrev bc120 : ℕ × Bool × Bool := (263, false, false)
private abbrev bc121 : ℕ × Bool × Bool := (263, true, true)
private abbrev bc122 : ℕ × Bool × Bool := (275, true, false)
private abbrev bc123 : ℕ × Bool × Bool := (279, false, true)
private abbrev bc124 : ℕ × Bool × Bool := (279, true, false)
private abbrev bc125 : ℕ × Bool × Bool := (274, false, true)
private abbrev bc126 : ℕ × Bool × Bool := (274, true, false)
private abbrev bc127 : ℕ × Bool × Bool := (235, false, false)
private abbrev bc128 : ℕ × Bool × Bool := (288, false, true)
private abbrev bc129 : ℕ × Bool × Bool := (288, true, false)
private abbrev bc130 : ℕ × Bool × Bool := (235, true, true)
private abbrev bc131 : ℕ × Bool × Bool := (291, true, true)
private abbrev bc132 : ℕ × Bool × Bool := (291, false, false)
private abbrev bc133 : ℕ × Bool × Bool := (1, true, false)
private abbrev bc134 : ℕ × Bool × Bool := (23, true, false)
private abbrev bc135 : ℕ × Bool × Bool := (27, true, false)
private abbrev bc136 : ℕ × Bool × Bool := (143, true, false)
private abbrev bc137 : ℕ × Bool × Bool := (148, true, false)
private abbrev bc138 : ℕ × Bool × Bool := (34, true, true)
private abbrev bc139 : ℕ × Bool × Bool := (71, true, true)
private abbrev bc140 : ℕ × Bool × Bool := (88, false, true)
private abbrev bc141 : ℕ × Bool × Bool := (111, true, true)
private abbrev bc142 : ℕ × Bool × Bool := (152, true, false)
private abbrev bc143 : ℕ × Bool × Bool := (180, true, true)
private abbrev bc144 : ℕ × Bool × Bool := (204, false, true)
private abbrev bc145 : ℕ × Bool × Bool := (217, true, false)
private abbrev bc146 : ℕ × Bool × Bool := (232, true, true)
private abbrev bc147 : ℕ × Bool × Bool := (245, false, true)
private abbrev bc148 : ℕ × Bool × Bool := (262, false, false)
private abbrev bc149 : ℕ × Bool × Bool := (264, true, true)
private abbrev bc150 : ℕ × Bool × Bool := (262, true, true)
private abbrev bc151 : ℕ × Bool × Bool := (273, false, true)

private def intCode (z : ℤ) : ℕ := if z < 0 then 2*z.natAbs+1 else 2*z.natAbs
private def proj (b : CertBound) : ℕ :=
  [b.lower.toNat,b.strict.toNat,intCode b.threshold.c.a.num,b.threshold.c.a.den,
   intCode b.threshold.x0.a.num,b.threshold.x0.a.den,intCode b.threshold.c.b.num,
   b.threshold.c.b.den,intCode b.threshold.x0.b.num,b.threshold.x0.b.den].foldl
    (fun acc n => ((acc+n+17)*(acc+n+17)+3*acc) % 1000000007) 7
private def fingerprint (bs : List CertBound) : ℕ := ((bs.map proj).toFinset.sum id)

private theorem fingerprint_congr {cs bs : List CertBound} (heq : cs.toFinset = bs.toFinset) :
    fingerprint cs = fingerprint bs := by
  have hm : ∀ b, b ∈ cs ↔ b ∈ bs := by
    intro b
    have h := congrArg (fun s : Finset CertBound => b ∈ s) heq
    simpa using Iff.of_eq h
  have hi : (cs.map proj).toFinset = (bs.map proj).toFinset := by
    ext z
    simp only [List.mem_toFinset,List.mem_map,hm]
  exact congrArg (fun s : Finset ℕ => s.sum id) hi
private theorem parents_of_fingerprints (raw : List (List CertBound))
    (h : (raw.map fingerprint).Nodup) : raw.Pairwise (fun cs bs => cs.toFinset ≠ bs.toFinset) := by
  have h' : raw.Pairwise (fun cs bs => fingerprint cs ≠ fingerprint bs) := List.pairwise_map.mp h
  exact h'.imp fun hne heq => hne (fingerprint_congr heq)
private def rawParent (a b : List CertBound × LowerHistoryComparison) : Option (List CertBound) :=
  let base := a.1 ++ b.1 ++ [lowerHistoryHN,lowerHistoryZero]
  match a.2,b.2 with
  | .impossible,_ | _,.impossible => none
  | .automatic,.automatic => some base
  | .bound g,.automatic | .automatic,.bound g => some (g::base)
  | .bound g,.bound h => some (g::h::base)
private def branchCode (a : List CertBound × LowerHistoryComparison) : List ℕ × Option (Option ℕ) :=
  (a.1.map proj, match a.2 with
    | .impossible => none
    | .automatic => some none
    | .bound b => some (some (proj b)))
private def parentCode (hn zero : ℕ) (a b : List ℕ × Option (Option ℕ)) : Option (List ℕ) :=
  match a.2,b.2 with
  | none,_ | _,none => none
  | some ga,some gb => some (ga.toList ++ gb.toList ++ a.1 ++ b.1 ++ [hn,zero])
private theorem parentCode_map (a b : List CertBound × LowerHistoryComparison) :
    (rawParent a b).map (List.map proj) = parentCode (proj lowerHistoryHN) (proj lowerHistoryZero) (branchCode a) (branchCode b) := by
  rcases a with ⟨ca,ga⟩
  rcases b with ⟨cb,gb⟩
  cases ga <;> cases gb <;> simp [rawParent,parentCode,branchCode,List.map_append,List.append_assoc]
private theorem rawCodes_map (A B : List (List CertBound × LowerHistoryComparison)) :
    (A.flatMap (fun a => B.filterMap (rawParent a))).map (List.map proj) =
    (A.map branchCode).flatMap (fun a => (B.map branchCode).filterMap (parentCode (proj lowerHistoryHN) (proj lowerHistoryZero) a)) := by
  simp only [List.map_flatMap,List.map_filterMap,List.flatMap_map,List.filterMap_map,Function.comp_apply]
  apply congrArg (fun f => A.flatMap f)
  funext a
  apply congrArg (fun f => B.filterMap f)
  funext b
  exact parentCode_map a b
private theorem trunkCodes_map (C : LowerHistoryContext) :
    (trunkRawParents C).map (List.map proj) =
    ((trunkBranches C ⟨([2],[]),true,([1],[]),false,false,[]⟩).map branchCode).flatMap (fun a =>
    ((trunkBranches C ⟨([1],[]),true,([2],[]),false,false,[]⟩).map branchCode).filterMap (parentCode (proj lowerHistoryHN) (proj lowerHistoryZero) a)) := by
  exact rawCodes_map _ _

private def codesA9 : List (List ℕ × Option (Option ℕ)) := [([112911326, 882722351, 131368818, 335455726], some (some 948335893)),
 ([112911326, 882722351, 131368818, 46223616], some (some 626279719)),
 ([112911326, 882722351, 624295141, 16305415], some (some 948335893)),
 ([112911326, 882722351, 624295141, 58036967], some (some 102443919)),
 ([112911326, 991976176], some (some 948335893)),
 ([728891584, 60072750, 649066977, 882722351, 131368818, 335455726], some (some 948335893)),
 ([728891584, 60072750, 649066977, 882722351, 131368818, 46223616], some (some 626279719)),
 ([728891584, 60072750, 649066977, 882722351, 624295141, 16305415], some (some 948335893)),
 ([728891584, 60072750, 649066977, 882722351, 624295141, 58036967], some (some 102443919)),
 ([728891584, 60072750, 649066977, 991976176], some (some 948335893)),
 ([728891584, 60072750, 595767334, 882722351, 131368818, 335455726], some (some 690199589)),
 ([728891584, 60072750, 595767334, 882722351, 131368818, 46223616], some (some 416338889)),
 ([728891584, 60072750, 595767334, 882722351, 624295141, 16305415], some (some 690199589)),
 ([728891584, 60072750, 595767334, 882722351, 624295141, 58036967], some (some 609086174)),
 ([728891584, 60072750, 595767334, 991976176], some (some 690199589)),
 ([728891584, 476573349, 881768834, 882722351, 131368818, 335455726], some (some 948335893)),
 ([728891584, 476573349, 881768834, 882722351, 131368818, 46223616], some (some 626279719)),
 ([728891584, 476573349, 881768834, 882722351, 624295141, 16305415], some (some 948335893)),
 ([728891584, 476573349, 881768834, 882722351, 624295141, 58036967], some (some 102443919)),
 ([728891584, 476573349, 881768834, 991976176], some (some 948335893)),
 ([728891584, 476573349, 159503643, 882722351, 131368818, 335455726], some (some 507666506)),
 ([728891584, 476573349, 159503643, 882722351, 131368818, 46223616], some (some 753260783)),
 ([728891584, 476573349, 159503643, 882722351, 624295141, 16305415], some (some 507666506)),
 ([728891584, 476573349, 159503643, 882722351, 624295141, 58036967], some (some 21298099)),
 ([728891584, 476573349, 159503643, 991976176], some (some 507666506))]
private def codesB9 : List (List ℕ × Option (Option ℕ)) := [([882722351, 112911326, 475598846, 413245293], some none),
 ([882722351, 112911326, 475598846, 250783862], some none),
 ([882722351, 112911326, 18672300, 970110223], some none),
 ([882722351, 112911326, 18672300, 961625388], some none),
 ([882722351, 728891584], some none),
 ([991976176, 112911326, 475598846, 413245293], some none),
 ([991976176, 112911326, 475598846, 250783862], some none),
 ([991976176, 112911326, 18672300, 970110223], some none),
 ([991976176, 112911326, 18672300, 961625388], some none),
 ([991976176, 728891584], some none)]

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
private def decodeThresholdBound (b : ℕ × Bool × Bool) : CertBound :=
  ⟨b.2.1,b.2.2,(fastBound b.1).threshold⟩
private def decodeGoalBranch (a : List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) : List CertBound × LowerHistoryComparison :=
  (a.1.map decodeThresholdBound, match a.2 with
    | none => .impossible
    | some none => .automatic
    | some (some b) => .bound (decodeThresholdBound b))
private def endpointFields9 : Array CertField := #[⟨(4/13),(1/13),(0/1),(0/1)⟩,⟨(1/2),(1/6),(0/1),(0/1)⟩,⟨(52/73),(1/73),(0/1),(0/1)⟩,⟨(89/214),(1/214),(0/1),(0/1)⟩,⟨(9/13),(-1/13),(0/1),(0/1)⟩,⟨(2/1),(-1/1),(0/1),(0/1)⟩,⟨(15/37),(-1/37),(0/1),(0/1)⟩,⟨(125/214),(-1/214),(0/1),(0/1)⟩,⟨(66/179),(-1/537),(0/1),(0/1)⟩,⟨(22/37),(1/37),(0/1),(0/1)⟩,⟨(113/179),(1/537),(0/1),(0/1)⟩,⟨(17/22),(-1/22),(0/1),(0/1)⟩,⟨(101/143),(-1/429),(0/1),(0/1)⟩,⟨(35/94),(1/94),(0/1),(0/1)⟩,⟨(553/1429),(1/1429),(0/1),(0/1)⟩,⟨(10/23),(-1/69),(0/1),(0/1)⟩,⟨(517/1249),(-1/1249),(0/1),(0/1)⟩,⟨(16/59),(1/177),(0/1),(0/1)⟩,⟨(767/2749),(1/2749),(0/1),(0/1)⟩,⟨(43/142),(-1/142),(0/1),(0/1)⟩,⟨(731/2497),(-1/2497),(0/1),(0/1)⟩,⟨(5/22),(1/22),(0/1),(0/1)⟩,⟨(42/143),(1/429),(0/1),(0/1)⟩,⟨(271/1006),(-1/1006),(0/1),(0/1)⟩,⟨(469/1549),(1/1549),(0/1),(0/1)⟩,⟨(3289/10753),(1/10753),(0/1),(0/1)⟩,⟨(579/1894),(-1/1894),(0/1),(0/1)⟩,⟨(71/229),(-1/229),(0/1),(0/1)⟩,⟨(1413/4654),(-1/4654),(0/1),(0/1)⟩,⟨(9014/29557),(-1/29557),(0/1),(0/1)⟩,⟨(13/23),(1/69),(0/1),(0/1)⟩,⟨(732/1249),(1/1249),(0/1),(0/1)⟩,⟨(59/94),(-1/94),(0/1),(0/1)⟩]
private abbrev endpointInput9_0 : LowerPair × Bool × Bool := (([2], []), true, false)
private def endpointCodes9_0 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((0, 1), [bc0]),
 ((0, 1), [bc1, bc2, bc3]),
 ((0, 2), [bc1, bc2, bc4]),
 ((0, 1), [bc1, bc5, bc6]),
 ((3, 1), [bc1, bc5, bc7])]
private abbrev endpointInput9_1 : LowerPair × Bool × Bool := (([1], []), false, false)
private def endpointCodes9_1 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((4, 5), [bc8, bc9, bc10]),
 ((4, 6), [bc8, bc9, bc11]),
 ((4, 5), [bc8, bc12, bc13]),
 ((7, 5), [bc8, bc12, bc14]),
 ((4, 5), [bc15])]
private abbrev endpointInput9_2 : LowerPair × Bool × Bool := (([1], []), true, false)
private def endpointCodes9_2 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((2, 1), [bc8]), ((2, 1), [bc15])]
private abbrev endpointInput9_3 : LowerPair × Bool × Bool := (([2], []), false, false)
private def endpointCodes9_3 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((6, 5), [bc0, bc16, bc17]),
 ((6, 6), [bc0, bc16, bc18]),
 ((6, 5), [bc0, bc19, bc20]),
 ((8, 5), [bc0, bc19, bc21]),
 ((6, 5), [bc1])]
private abbrev endpointInput9_4 : LowerPair × Bool × Bool := (([1, 1], []), true, false)
private def endpointCodes9_4 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((9, 1), [bc9, bc22]),
 ((9, 2), [bc9, bc23]),
 ((9, 1), [bc12, bc24]),
 ((10, 1), [bc12, bc25])]
private abbrev endpointInput9_5 : LowerPair × Bool × Bool := (([1, 2], []), false, false)
private def endpointCodes9_5 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((11, 5), [bc26, bc27]),
 ((11, 6), [bc26, bc28]),
 ((11, 5), [bc29, bc30]),
 ((12, 5), [bc29, bc31])]
private abbrev endpointInput9_6 : LowerPair × Bool × Bool := (([1], [2]), true, true)
private def endpointCodes9_6 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((2, 0), [])]
private abbrev endpointInput9_7 : LowerPair × Bool × Bool := (([1], [1]), false, true)
private def endpointCodes9_7 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((4, 4), [bc32, (52, false, true)]),
 ((4, 7), [bc32, (52, true, false)]),
 ((4, 4), [bc33, (56, true, true)]),
 ((7, 4), [bc33, (56, false, false)])]
private abbrev endpointInput9_8 : LowerPair × Bool × Bool := (([2, 1], []), true, false)
private def endpointCodes9_8 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((13, 1), [bc16, bc34]),
 ((13, 2), [bc16, bc35]),
 ((13, 1), [bc19, bc36]),
 ((14, 1), [bc19, bc37])]
private abbrev endpointInput9_9 : LowerPair × Bool × Bool := (([2, 2], []), false, false)
private def endpointCodes9_9 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((15, 5), [bc38, bc39]),
 ((15, 6), [bc38, bc40]),
 ((15, 5), [bc41, bc42]),
 ((16, 5), [bc41, bc43])]
private abbrev endpointInput9_10 : LowerPair × Bool × Bool := (([2], [2]), true, true)
private def endpointCodes9_10 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((0, 0), [bc44, bc45]),
 ((0, 3), [bc44, bc46]),
 ((0, 0), [bc47, bc48]),
 ((3, 0), [bc47, bc49])]
private abbrev endpointInput9_11 : LowerPair × Bool × Bool := (([2], [1]), false, true)
private def endpointCodes9_11 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((6, 4), [bc50, bc51]),
 ((6, 7), [bc50, bc52]),
 ((6, 4), [bc53, bc54]),
 ((8, 4), [bc53, bc55])]
private abbrev endpointInput9_12 : LowerPair × Bool × Bool := (([3, 1], []), true, false)
private def endpointCodes9_12 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((17, 1), [bc56, bc57]),
 ((17, 2), [bc56, bc58]),
 ((17, 1), [bc59, bc60]),
 ((18, 1), [bc59, bc61])]
private abbrev endpointInput9_13 : LowerPair × Bool × Bool := (([3, 2], []), false, false)
private def endpointCodes9_13 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((19, 5), [bc62, bc63]),
 ((19, 6), [bc62, bc64]),
 ((19, 5), [bc65, bc66]),
 ((20, 5), [bc65, bc67])]
private abbrev endpointInput9_14 : LowerPair × Bool × Bool := (([3], [2]), true, true)
private def endpointCodes9_14 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((21, 0), [bc68, bc69]),
 ((21, 3), [bc68, bc70]),
 ((21, 0), [bc71, bc72]),
 ((22, 0), [bc71, bc73])]
private abbrev endpointInput9_15 : LowerPair × Bool × Bool := (([3], [1]), false, true)
private def endpointCodes9_15 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((23, 4), [])]
private abbrev endpointInput9_16 : LowerPair × Bool × Bool := (([3], []), true, false)
private def endpointCodes9_16 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((21, 1), [bc74]),
 ((21, 1), [bc75, bc76, bc77]),
 ((21, 2), [bc75, bc76, bc78]),
 ((21, 1), [bc75, bc79, bc80]),
 ((22, 1), [bc75, bc79, bc81])]
private abbrev endpointInput9_17 : LowerPair × Bool × Bool := (([3, 1], [2]), true, false)
private def endpointCodes9_17 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((17, 0), [bc82, bc83, bc84]),
 ((17, 3), [bc82, bc83, bc85]),
 ((17, 0), [bc82, bc86, bc87]),
 ((18, 0), [bc82, bc86, bc88]),
 ((17, 0), [bc89])]
private abbrev endpointInput9_18 : LowerPair × Bool × Bool := (([3, 2], [2]), false, false)
private def endpointCodes9_18 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((19, 6), [bc90]),
 ((19, 6), [bc91, bc92, bc93]),
 ((19, 8), [bc91, bc92, bc94]),
 ((19, 6), [bc91, bc95, bc96]),
 ((20, 6), [bc91, bc95, bc97])]
private abbrev endpointInput9_19 : LowerPair × Bool × Bool := (([3], [2, 1]), true, true)
private def endpointCodes9_19 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((21, 13), [(206, false, true)]),
 ((21, 13), [bc98, bc99, (208, false, true)]),
 ((21, 14), [bc98, bc99, (208, true, false)]),
 ((21, 13), [bc98, bc100, (213, true, true)]),
 ((22, 13), [bc98, bc100, (213, false, false)])]
private abbrev endpointInput9_20 : LowerPair × Bool × Bool := (([3], [2, 2]), false, true)
private def endpointCodes9_20 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((23, 15), [bc101]), ((23, 15), [bc102])]
private abbrev endpointInput9_21 : LowerPair × Bool × Bool := (([3], [2]), true, false)
private def endpointCodes9_21 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((21, 0), [bc103, bc69]),
 ((21, 3), [bc103, bc70]),
 ((21, 0), [bc104, bc72]),
 ((22, 0), [bc104, bc73])]
private abbrev endpointInput9_22 : LowerPair × Bool × Bool := (([], []), false, false)
private def endpointCodes9_22 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((5, 5), [bc105, (176, false, true)]),
 ((5, 6), [bc105, (176, true, false)]),
 ((5, 5), [bc106, (228, true, true)]),
 ((6, 5), [bc106, (228, false, false)])]
private abbrev endpointInput9_23 : LowerPair × Bool × Bool := (([3], [2]), false, false)
private def endpointCodes9_23 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((23, 6), [])]
private abbrev endpointInput9_24 : LowerPair × Bool × Bool := (([3, 3, 2], [3, 3]), true, false)
private def endpointCodes9_24 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((24, 25), [bc107]), ((24, 25), [bc108])]
private abbrev endpointInput9_25 : LowerPair × Bool × Bool := (([3, 3, 1], [3, 3]), false, false)
private def endpointCodes9_25 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((26, 27), [bc109, bc110, (231, false, true)]),
 ((26, 28), [bc109, bc110, (231, true, false)]),
 ((26, 27), [bc109, bc111, (239, true, true)]),
 ((29, 27), [bc109, bc111, (239, false, false)]),
 ((26, 27), [(234, true, true)])]
private abbrev endpointInput9_26 : LowerPair × Bool × Bool := (([3, 3], [3, 3, 2]), true, true)
private def endpointCodes9_26 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((25, 24), [bc112]), ((25, 24), [bc113])]
private abbrev endpointInput9_27 : LowerPair × Bool × Bool := (([3, 3], [3, 3, 1]), false, true)
private def endpointCodes9_27 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((27, 26), [(248, false, true)]),
 ((27, 26), [bc114, bc115, (249, false, true)]),
 ((27, 29), [bc114, bc115, (249, true, false)]),
 ((27, 26), [bc114, bc116, (254, true, true)]),
 ((28, 26), [bc114, bc116, (254, false, false)])]
private abbrev endpointInput9_28 : LowerPair × Bool × Bool := (([3, 1], [3]), true, false)
private def endpointCodes9_28 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((17, 21), [bc117, bc118, (259, false, true)]),
 ((17, 22), [bc117, bc118, (259, true, false)]),
 ((17, 21), [bc117, bc119, (269, true, true)]),
 ((18, 21), [bc117, bc119, (269, false, false)]),
 ((17, 21), [(260, true, true)])]
private abbrev endpointInput9_29 : LowerPair × Bool × Bool := (([3, 2], [3]), false, false)
private def endpointCodes9_29 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((19, 23), [bc120]), ((19, 23), [bc121])]
private abbrev endpointInput9_30 : LowerPair × Bool × Bool := (([3], [3, 1]), true, true)
private def endpointCodes9_30 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((21, 17), [(275, false, true)]),
 ((21, 17), [bc122, bc123, (280, false, true)]),
 ((21, 18), [bc122, bc123, (280, true, false)]),
 ((21, 17), [bc122, bc124, (283, true, true)]),
 ((22, 17), [bc122, bc124, (283, false, false)])]
private abbrev endpointInput9_31 : LowerPair × Bool × Bool := (([3], [3, 2]), false, true)
private def endpointCodes9_31 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((23, 19), [bc125]), ((23, 19), [bc126])]
private abbrev endpointInput9_32 : LowerPair × Bool × Bool := (([3, 3], [3, 3]), false, false)
private def endpointCodes9_32 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((27, 27), [bc127, bc128]),
 ((27, 28), [bc127, bc129]),
 ((27, 27), [bc130, bc131]),
 ((28, 27), [bc130, bc132])]
private abbrev endpointInput9_33 : LowerPair × Bool × Bool := (([3, 3], [3, 3]), true, false)
private def endpointCodes9_33 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((25, 25), [])]

private def decodeEndpoint9 (x : (ℕ × ℕ) × List (ℕ × Bool × Bool)) : LowerHistoryEndCase :=
  ((endpointFields9[x.1.1]?.getD ⟨0,0,0,0⟩,endpointFields9[x.1.2]?.getD ⟨0,0,0,0⟩),x.2.map decodeThresholdBound)

private theorem hEndpoint9_0 :
    trunkEndpointCases (trunkCatalog.states 9).context endpointInput9_0.1 endpointInput9_0.2.1 endpointInput9_0.2.2 = endpointCodes9_0.map decodeEndpoint9 := by decide +kernel

private theorem hEndpoint9_1 :
    trunkEndpointCases (trunkCatalog.states 9).context endpointInput9_1.1 endpointInput9_1.2.1 endpointInput9_1.2.2 = endpointCodes9_1.map decodeEndpoint9 := by decide +kernel

private theorem hEndpoint9_2 :
    trunkEndpointCases (trunkCatalog.states 9).context endpointInput9_2.1 endpointInput9_2.2.1 endpointInput9_2.2.2 = endpointCodes9_2.map decodeEndpoint9 := by decide +kernel

private theorem hEndpoint9_3 :
    trunkEndpointCases (trunkCatalog.states 9).context endpointInput9_3.1 endpointInput9_3.2.1 endpointInput9_3.2.2 = endpointCodes9_3.map decodeEndpoint9 := by decide +kernel

private theorem hEndpoint9_4 :
    trunkEndpointCases (trunkCatalog.states 9).context endpointInput9_4.1 endpointInput9_4.2.1 endpointInput9_4.2.2 = endpointCodes9_4.map decodeEndpoint9 := by decide +kernel

private theorem hEndpoint9_5 :
    trunkEndpointCases (trunkCatalog.states 9).context endpointInput9_5.1 endpointInput9_5.2.1 endpointInput9_5.2.2 = endpointCodes9_5.map decodeEndpoint9 := by decide +kernel

private theorem hEndpoint9_6 :
    trunkEndpointCases (trunkCatalog.states 9).context endpointInput9_6.1 endpointInput9_6.2.1 endpointInput9_6.2.2 = endpointCodes9_6.map decodeEndpoint9 := by decide +kernel

private theorem hEndpoint9_7 :
    trunkEndpointCases (trunkCatalog.states 9).context endpointInput9_7.1 endpointInput9_7.2.1 endpointInput9_7.2.2 = endpointCodes9_7.map decodeEndpoint9 := by decide +kernel

private theorem hEndpoint9_8 :
    trunkEndpointCases (trunkCatalog.states 9).context endpointInput9_8.1 endpointInput9_8.2.1 endpointInput9_8.2.2 = endpointCodes9_8.map decodeEndpoint9 := by decide +kernel

private theorem hEndpoint9_9 :
    trunkEndpointCases (trunkCatalog.states 9).context endpointInput9_9.1 endpointInput9_9.2.1 endpointInput9_9.2.2 = endpointCodes9_9.map decodeEndpoint9 := by decide +kernel

private theorem hEndpoint9_10 :
    trunkEndpointCases (trunkCatalog.states 9).context endpointInput9_10.1 endpointInput9_10.2.1 endpointInput9_10.2.2 = endpointCodes9_10.map decodeEndpoint9 := by decide +kernel

private theorem hEndpoint9_11 :
    trunkEndpointCases (trunkCatalog.states 9).context endpointInput9_11.1 endpointInput9_11.2.1 endpointInput9_11.2.2 = endpointCodes9_11.map decodeEndpoint9 := by decide +kernel

private theorem hEndpoint9_12 :
    trunkEndpointCases (trunkCatalog.states 9).context endpointInput9_12.1 endpointInput9_12.2.1 endpointInput9_12.2.2 = endpointCodes9_12.map decodeEndpoint9 := by decide +kernel

private theorem hEndpoint9_13 :
    trunkEndpointCases (trunkCatalog.states 9).context endpointInput9_13.1 endpointInput9_13.2.1 endpointInput9_13.2.2 = endpointCodes9_13.map decodeEndpoint9 := by decide +kernel

private theorem hEndpoint9_14 :
    trunkEndpointCases (trunkCatalog.states 9).context endpointInput9_14.1 endpointInput9_14.2.1 endpointInput9_14.2.2 = endpointCodes9_14.map decodeEndpoint9 := by decide +kernel

private theorem hEndpoint9_15 :
    trunkEndpointCases (trunkCatalog.states 9).context endpointInput9_15.1 endpointInput9_15.2.1 endpointInput9_15.2.2 = endpointCodes9_15.map decodeEndpoint9 := by decide +kernel

private theorem hEndpoint9_16 :
    trunkEndpointCases (trunkCatalog.states 9).context endpointInput9_16.1 endpointInput9_16.2.1 endpointInput9_16.2.2 = endpointCodes9_16.map decodeEndpoint9 := by decide +kernel

private theorem hEndpoint9_17 :
    trunkEndpointCases (trunkCatalog.states 9).context endpointInput9_17.1 endpointInput9_17.2.1 endpointInput9_17.2.2 = endpointCodes9_17.map decodeEndpoint9 := by decide +kernel

private theorem hEndpoint9_18 :
    trunkEndpointCases (trunkCatalog.states 9).context endpointInput9_18.1 endpointInput9_18.2.1 endpointInput9_18.2.2 = endpointCodes9_18.map decodeEndpoint9 := by decide +kernel

private theorem hEndpoint9_19 :
    trunkEndpointCases (trunkCatalog.states 9).context endpointInput9_19.1 endpointInput9_19.2.1 endpointInput9_19.2.2 = endpointCodes9_19.map decodeEndpoint9 := by decide +kernel

private theorem hEndpoint9_20 :
    trunkEndpointCases (trunkCatalog.states 9).context endpointInput9_20.1 endpointInput9_20.2.1 endpointInput9_20.2.2 = endpointCodes9_20.map decodeEndpoint9 := by decide +kernel

private theorem hEndpoint9_21 :
    trunkEndpointCases (trunkCatalog.states 9).context endpointInput9_21.1 endpointInput9_21.2.1 endpointInput9_21.2.2 = endpointCodes9_21.map decodeEndpoint9 := by decide +kernel

private theorem hEndpoint9_22 :
    trunkEndpointCases (trunkCatalog.states 9).context endpointInput9_22.1 endpointInput9_22.2.1 endpointInput9_22.2.2 = endpointCodes9_22.map decodeEndpoint9 := by decide +kernel

private theorem hEndpoint9_23 :
    trunkEndpointCases (trunkCatalog.states 9).context endpointInput9_23.1 endpointInput9_23.2.1 endpointInput9_23.2.2 = endpointCodes9_23.map decodeEndpoint9 := by decide +kernel

private theorem hEndpoint9_24 :
    trunkEndpointCases (trunkCatalog.states 9).context endpointInput9_24.1 endpointInput9_24.2.1 endpointInput9_24.2.2 = endpointCodes9_24.map decodeEndpoint9 := by decide +kernel

private theorem hEndpoint9_25 :
    trunkEndpointCases (trunkCatalog.states 9).context endpointInput9_25.1 endpointInput9_25.2.1 endpointInput9_25.2.2 = endpointCodes9_25.map decodeEndpoint9 := by decide +kernel

private theorem hEndpoint9_26 :
    trunkEndpointCases (trunkCatalog.states 9).context endpointInput9_26.1 endpointInput9_26.2.1 endpointInput9_26.2.2 = endpointCodes9_26.map decodeEndpoint9 := by decide +kernel

private theorem hEndpoint9_27 :
    trunkEndpointCases (trunkCatalog.states 9).context endpointInput9_27.1 endpointInput9_27.2.1 endpointInput9_27.2.2 = endpointCodes9_27.map decodeEndpoint9 := by decide +kernel

private theorem hEndpoint9_28 :
    trunkEndpointCases (trunkCatalog.states 9).context endpointInput9_28.1 endpointInput9_28.2.1 endpointInput9_28.2.2 = endpointCodes9_28.map decodeEndpoint9 := by decide +kernel

private theorem hEndpoint9_29 :
    trunkEndpointCases (trunkCatalog.states 9).context endpointInput9_29.1 endpointInput9_29.2.1 endpointInput9_29.2.2 = endpointCodes9_29.map decodeEndpoint9 := by decide +kernel

private theorem hEndpoint9_30 :
    trunkEndpointCases (trunkCatalog.states 9).context endpointInput9_30.1 endpointInput9_30.2.1 endpointInput9_30.2.2 = endpointCodes9_30.map decodeEndpoint9 := by decide +kernel

private theorem hEndpoint9_31 :
    trunkEndpointCases (trunkCatalog.states 9).context endpointInput9_31.1 endpointInput9_31.2.1 endpointInput9_31.2.2 = endpointCodes9_31.map decodeEndpoint9 := by decide +kernel

private theorem hEndpoint9_32 :
    trunkEndpointCases (trunkCatalog.states 9).context endpointInput9_32.1 endpointInput9_32.2.1 endpointInput9_32.2.2 = endpointCodes9_32.map decodeEndpoint9 := by decide +kernel

private theorem hEndpoint9_33 :
    trunkEndpointCases (trunkCatalog.states 9).context endpointInput9_33.1 endpointInput9_33.2.1 endpointInput9_33.2.2 = endpointCodes9_33.map decodeEndpoint9 := by decide +kernel

private def cachedBranches (C : LowerHistoryContext) (strict : Bool) (extra : List CertBound)
    (left right : List LowerHistoryEndCase) : List (List CertBound × LowerHistoryComparison) :=
  left.flatMap fun (x,cx) => right.map fun (y,cy) =>
    (extra ++ cx ++ cy,trunkGreater C x y strict)
private theorem cachedBranches_eq (C : LowerHistoryContext) (s : Section14Spec)
    (i j : LowerPair × Bool × Bool) (extra : List CertBound) (left right : List LowerHistoryEndCase)
    (hi : (s.first,s.firstUpper,trunkSpecIncoming s) = i)
    (hj : (s.second,s.secondUpper,trunkSpecIncoming s) = j)
    (he : s.extra = extra)
    (hl : trunkEndpointCases C i.1 i.2.1 i.2.2 = left)
    (hr : trunkEndpointCases C j.1 j.2.1 j.2.2 = right) :
    trunkBranches C s = cachedBranches C s.strict extra left right := by
  have hL : trunkEndpointCases C s.first s.firstUpper (trunkSpecIncoming s) = left :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases C z.1 z.2.1 z.2.2) hi).trans hl
  have hR : trunkEndpointCases C s.second s.secondUpper (trunkSpecIncoming s) = right :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases C z.1 z.2.1 z.2.2) hj).trans hr
  unfold trunkBranches cachedBranches
  rw [hL,hR,he]
private def thresholdClasses : Array ℕ := #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 2, 6, 13, 13, 3, 10, 17, 18, 17, 20, 18, 20, 23, 9, 4, 26, 27, 26, 29, 30, 31, 32, 33,
 34, 31, 36, 37, 32, 39, 37, 41, 33, 43, 44, 45, 46, 45, 48, 49, 50, 51, 52, 53, 52, 55, 56, 57, 56, 59, 51, 61, 62, 50,
 64, 65, 64, 67, 68, 69, 70, 71, 72, 73, 70, 75, 72, 77, 75, 69, 80, 81, 82, 83, 83, 85, 86, 87, 88, 89, 90, 91, 92, 90,
 30, 95, 95, 97, 91, 99, 100, 101, 102, 89, 104, 102, 106, 107, 108, 109, 110, 111, 112, 113, 114, 108, 112, 117, 117,
 119, 113, 121, 122, 123, 109, 125, 126, 125, 128, 129, 130, 110, 132, 133, 133, 135, 136, 132, 136, 139, 1, 23, 27,
 143, 29, 145, 146, 147, 148, 147, 150, 151, 152, 153, 154, 155, 156, 157, 155, 159, 160, 156, 162, 162, 164, 165, 166,
 8, 168, 168, 143, 145, 146, 148, 150, 151, 176, 177, 7, 179, 180, 181, 182, 183, 184, 181, 186, 187, 186, 189, 184,
 191, 189, 179, 194, 195, 196, 197, 182, 199, 197, 201, 202, 183, 204, 205, 206, 205, 208, 206, 210, 208, 212, 213, 210,
 215, 213, 217, 218, 219, 220, 221, 222, 223, 224, 225, 176, 227, 228, 228, 230, 231, 232, 233, 234, 235, 236, 231, 238,
 239, 236, 239, 242, 234, 233, 245, 246, 235, 248, 249, 248, 251, 249, 253, 254, 251, 254, 257, 246, 259, 260, 261, 262,
 263, 264, 263, 266, 259, 261, 269, 269, 271, 260, 273, 274, 275, 262, 274, 275, 279, 280, 280, 282, 283, 279, 285, 283,
 287, 288, 288, 290, 291, 292, 291, 294, 177, 296, 297, 298, 299, 300, 301, 299, 303, 304, 303, 301, 307, 307, 309, 310,
 311, 312, 298, 314, 315, 316, 297, 318, 319, 320, 321, 322, 323, 321, 325, 322, 327, 325, 320, 319, 331, 332, 332, 334,
 335, 336, 337, 331, 337, 340, 341, 342, 343, 344, 345, 346, 347, 346, 349, 350, 349, 352, 347, 354, 352, 356, 357, 358,
 343, 360, 361, 362, 344, 364, 365, 366, 366, 365, 369, 370, 370, 372, 373, 369, 375, 373, 377, 378, 379, 380, 381, 381,
 383, 384, 385, 383, 384, 388, 388, 390, 391, 377, 393, 394, 395, 379, 395, 398, 399, 400, 380, 402, 403, 404, 405, 406,
 407, 403, 409, 406, 411, 409, 404, 414, 415, 405, 414, 418, 419, 420, 421, 415, 421, 424, 425, 426, 427, 428, 429, 430,
 431, 432, 428, 434, 427, 436, 430, 436, 439, 432, 441, 431, 443, 444, 445, 446, 447, 444, 449, 445, 451, 449, 446, 443,
 455, 456, 456, 458, 459, 460, 461, 455, 461, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 476,
 479, 479, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 490, 494, 495, 496, 497, 497, 499, 500, 501, 502,
 503, 504, 505, 506, 507, 296, 509, 510, 511, 512, 513, 510, 515, 516, 517, 511, 519, 520, 519, 522, 523, 524, 525, 526,
 526, 528, 529, 525, 531, 529, 533, 534, 535, 536, 537, 538, 539, 540, 541, 542, 543, 544, 545, 546, 547, 548, 549, 550,
 551, 551]
private def thresholdClass (id : ℕ) : ℕ := thresholdClasses[id-1]?.getD 0

private def classValidIds : List ℕ := [1, 2, 6, 9, 14, 15, 3, 16, 10, 23, 4, 27, 25, 31, 32, 34, 40, 46, 88, 29, 92, 94, 7, 98, 102, 103, 108, 112, 111, 118, 121, 126, 130, 134, 136, 137, 140, 26, 28, 144, 30, 110, 152, 157, 162, 164, 171, 90, 170, 143, 172, 147, 176, 65, 177, 67, 56, 68, 97, 96, 179, 182, 181, 180, 187, 191, 200, 204, 207, 211, 213, 214, 149, 217, 220, 223, 226, 167, 8, 178, 231, 236, 233, 243, 232, 241, 245, 252, 254, 255, 258, 259, 261, 263, 264, 270, 272, 273, 277, 281, 283, 284, 287, 289, 290, 291, 247, 292, 294]
private theorem thresholdClass_key : ∀ i ∈ classValidIds,
    i = thresholdClass i ∨ (fastBound i).threshold = (fastBound (thresholdClass i)).threshold := by decide +kernel
private theorem threshold_class_of_range (i : ℕ) (hi : i ∈ classValidIds) :
    (fastBound i).threshold = (fastBound (thresholdClass i)).threshold := by
  rcases thresholdClass_key i hi with he | he
  · rw [← he]
  · exact he
private def codeUseBounds (w : TrunkWitness) (l u : ℕ × Bool × Bool) : Prop :=
  l.2.1 = true ∧ u.2.1 = false ∧
  w.lowerId ∈ classValidIds ∧ w.upperId ∈ classValidIds ∧
  l.1 = thresholdClass w.lowerId ∧ u.1 = thresholdClass w.upperId ∧
  ((w.diagonal = 0 ∧ 0 < w.margin) ∨ l.2.2 = true ∨ u.2.2 = true)
private theorem codeUseBounds_sound (w : TrunkWitness) (l u : ℕ × Bool × Bool)
    (h : codeUseBounds w l u) : trunkUseBoundsFast w (decodeThresholdBound l) (decodeThresholdBound u) := by
  rcases h with ⟨hl,hu,hll,hul,hle,hue,hs⟩
  refine ⟨hl,hu,?_,?_,hs⟩
  · change (fastBound l.1).threshold = (fastBound w.lowerId).threshold
    rw [hle,← threshold_class_of_range w.lowerId hll]
  · change (fastBound u.1).threshold = (fastBound w.upperId).threshold
    rw [hue,← threshold_class_of_range w.upperId hul]
private def codeLeafBound (R : CertRectangle) (bs : List (ℕ × Bool × Bool)) (id : ℕ) (sign : ℤ) : Prop :=
  0 < id ∧ id ≤ 8656 ∧
  (fastWitness id).diagonal = sign ∧
  section14RectangleContains (fastWitness id).rectangle R ∧
  (fastWitness id).lowerId ∈ classValidIds ∧ (fastWitness id).upperId ∈ classValidIds ∧
  ∃ l ∈ bs, l.2.1 = true ∧ l.1 = thresholdClass (fastWitness id).lowerId ∧
    ∃ u ∈ bs, u.2.1 = false ∧ u.1 = thresholdClass (fastWitness id).upperId ∧
      (((fastWitness id).diagonal = 0 ∧ 0 < (fastWitness id).margin) ∨ l.2.2 = true ∨ u.2.2 = true)
private theorem codeLeafBound_sound (R : CertRectangle) (bs : List (ℕ × Bool × Bool)) (id : ℕ) (sign : ℤ)
    (h : codeLeafBound R bs id sign) : trunkLeafBoundFast R (bs.map decodeThresholdBound) id sign := by
  rcases h with ⟨hlo,hhi,hdiag,hrect,hll,hul,l,hl,hloflag,hloid,u,hu,hupflag,hupid,hstrict⟩
  refine ⟨hlo,hhi,hdiag,hrect,decodeThresholdBound l,List.mem_map.mpr ⟨l,hl,rfl⟩,
    decodeThresholdBound u,List.mem_map.mpr ⟨u,hu,rfl⟩,?_⟩
  exact codeUseBounds_sound _ _ _ ⟨hloflag,hupflag,hll,hul,hloid,hupid,hstrict⟩
private def codeTreeBound (R : CertRectangle) (bs : List (ℕ × Bool × Bool)) : TrunkTree → Prop
  | .pair id => codeLeafBound R bs id 0
  | .split axis left right =>
    codeTreeBound (trunkRectangleHalf R axis false) bs left ∧
    codeTreeBound (trunkRectangleHalf R axis true) bs right
  | .diagonal negative positive => codeLeafBound R bs negative (-1) ∧ codeLeafBound R bs positive 1
  | .boundary => trunkBoundaryBound R (bs.map decodeThresholdBound)
private instance decCodeTreeBound (R : CertRectangle) (bs : List (ℕ × Bool × Bool)) :
    ∀ t : TrunkTree, Decidable (codeTreeBound R bs t)
  | .pair id => by unfold codeTreeBound codeLeafBound section14RectangleContains; infer_instance
  | .split axis left right => by
      unfold codeTreeBound
      have := decCodeTreeBound (trunkRectangleHalf R axis false) bs left
      have := decCodeTreeBound (trunkRectangleHalf R axis true) bs right
      infer_instance
  | .diagonal negative positive => by
      unfold codeTreeBound codeLeafBound section14RectangleContains
      infer_instance
  | .boundary => by unfold codeTreeBound trunkBoundaryBound certThresholdDataValid; infer_instance
private theorem codeTreeBound_sound (t : TrunkTree) (R : CertRectangle) (bs : List (ℕ × Bool × Bool))
    (h : codeTreeBound R bs t) : trunkTreeBoundFast R (bs.map decodeThresholdBound) t := by
  induction t generalizing R with
  | pair id => exact codeLeafBound_sound _ _ _ _ h
  | split axis left right ihl ihr => exact ⟨ihl _ h.1,ihr _ h.2⟩
  | diagonal negative positive => exact ⟨codeLeafBound_sound _ _ _ _ h.1,codeLeafBound_sound _ _ _ _ h.2⟩
  | boundary => exact h
private def codeComplement (b : ℕ × Bool × Bool) : ℕ × Bool × Bool := (b.1,!b.2.1,!b.2.2)
private theorem decodeComplement (b : ℕ × Bool × Bool) :
    decodeThresholdBound (codeComplement b) = lowerHistoryComplement (decodeThresholdBound b) := rfl
private def codeResidual (parents : ℕ → List (ℕ × Bool × Bool)) (cuts : List (ℕ × Bool × Bool))
    (goals : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))))
    (parent : ℕ) (branch : ℤ) : List (ℕ × Bool × Bool) :=
  let b := goals[branch.toNat]?.getD ([],none)
  cuts ++ parents parent ++ b.1 ++
    match b.2 with | some (some a) => [codeComplement a] | _ => []
private theorem codedBranch_eq (S : TrunkState) (pi goal : ℕ) (branch : ℤ)
    (codes : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))))
    (he : trunkGoalBranches S pi goal = codes.map decodeGoalBranch) :
    trunkBranch S pi goal branch = decodeGoalBranch (codes[branch.toNat]?.getD ([],none)) := by
  unfold trunkBranch
  rw [he,List.getElem?_map]
  exact Option.getD_map decodeGoalBranch ([],none) codes[branch.toNat]?
private theorem codeResidual_eq (S : TrunkState) (pi parent goal : ℕ) (branch : ℤ)
    (parents : ℕ → List (ℕ × Bool × Bool)) (cuts : List (ℕ × Bool × Bool))
    (goals : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))))
    (hpar : ∀ i, (trunkRawParents S.context)[i]?.getD [] = (parents i).map decodeThresholdBound)
    (hcut : (trunkPlanAt S pi).cuts = cuts.map decodeThresholdBound)
    (hgoal : trunkGoalBranches S pi goal = goals.map decodeGoalBranch) :
    trunkResidualFast S pi parent goal branch = (codeResidual parents cuts goals parent branch).map decodeThresholdBound := by
  unfold trunkResidualFast codeResidual
  rw [hcut,hpar parent,codedBranch_eq S pi goal branch goals hgoal]
  generalize goals[branch.toNat]?.getD ([],none) = b
  rcases b with ⟨bs,cmp⟩
  cases cmp with
  | none => simp [decodeGoalBranch,List.map_append]
  | some cmp =>
    cases cmp <;> simp [decodeGoalBranch,List.map_append,decodeComplement]
private def codeGroupValid (S : TrunkState) (parents : ℕ → List (ℕ × Bool × Bool)) (parentCount : ℕ)
    (cuts : ℕ → List (ℕ × Bool × Bool))
    (goals : ℕ → ℕ → List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))))
    (g : TrunkGroup) : Prop :=
  g.plan < (trunkSourcePlans S.context).length ∧ g.goal ≤ (trunkSpecs (trunkPlanAt S g.plan)).length ∧
  (∀ p ∈ g.parents, p < parentCount) ∧
  ∀ bt ∈ g.branches,
    ((g.goal = 0 ∧ bt.1 = -1) ∨ (0 < g.goal ∧ 0 ≤ bt.1 ∧ bt.1.toNat < (goals g.plan g.goal).length)) ∧
    ((goals g.plan g.goal)[bt.1.toNat]?.getD ([],none)).2 ≠ some none ∧
    ∀ p ∈ g.parents, codeTreeBound S.rectangle (codeResidual parents (cuts g.plan) (goals g.plan g.goal) p bt.1) bt.2
private theorem codeGroupValid_sound (k : Fin 16) (parents : ℕ → List (ℕ × Bool × Bool)) (parentCount : ℕ)
    (cuts : ℕ → List (ℕ × Bool × Bool))
    (goals : ℕ → ℕ → List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))))
    (g : TrunkGroup)
    (hpar : ∀ i, (trunkRawParents (trunkCatalog.states k).context)[i]?.getD [] = (parents i).map decodeThresholdBound)
    (hlen : (trunkRawParents (trunkCatalog.states k).context).length = parentCount)
    (hcut : (trunkPlanAt (trunkCatalog.states k) g.plan).cuts = (cuts g.plan).map decodeThresholdBound)
    (hgoal : trunkGoalBranches (trunkCatalog.states k) g.plan g.goal = (goals g.plan g.goal).map decodeGoalBranch)
    (h : codeGroupValid (trunkCatalog.states k) parents parentCount cuts goals g) : trunkGroupValidFast k g := by
  rcases h with ⟨hp,hg,hparents,hb⟩
  refine ⟨hp,hg,?_,?_⟩
  · simpa only [hlen] using hparents
  · intro bt hbt
    obtain ⟨hr,ha,ht⟩ := hb bt hbt
    refine ⟨?_,?_,?_⟩
    · simpa only [hgoal,List.length_map] using hr
    · rw [codedBranch_eq _ _ _ _ _ hgoal]
      generalize he : (goals g.plan g.goal)[bt.1.toNat]?.getD ([],none) = b at *
      rcases b with ⟨bs,cmp⟩
      cases cmp with
      | none => simp [decodeGoalBranch]
      | some cmp =>
        cases cmp <;> simp_all [decodeGoalBranch]
    · intro p hpg
      rw [codeResidual_eq _ _ _ _ _ parents (cuts g.plan) (goals g.plan g.goal) hpar hcut hgoal]
      exact codeTreeBound_sound _ _ _ (ht p hpg)
private def codeHN : ℕ × Bool × Bool := bc105
private def codeZero : ℕ × Bool × Bool := (5, true, true)

private theorem hDecodeHN : decodeThresholdBound codeHN = lowerHistoryHN := by decide +kernel
private theorem hDecodeZero : decodeThresholdBound codeZero = lowerHistoryZero := by decide +kernel
private def codeRawParent (a b : List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) : Option (List (ℕ × Bool × Bool)) :=
  match a.2,b.2 with
  | none,_ | _,none => none
  | some ga,some gb => some (ga.toList ++ gb.toList ++ a.1 ++ b.1 ++ [codeHN,codeZero])
private theorem codeRawParent_map (a b : List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) :
    (codeRawParent a b).map (List.map decodeThresholdBound) = rawParent (decodeGoalBranch a) (decodeGoalBranch b) := by
  rcases a with ⟨ca,ga⟩
  rcases b with ⟨cb,gb⟩
  cases ga with
  | none => simp [codeRawParent,decodeGoalBranch,rawParent]
  | some ga =>
    cases gb with
    | none => cases ga <;> simp [codeRawParent,decodeGoalBranch,rawParent]
    | some gb =>
      cases ga <;> cases gb <;>
        simp [codeRawParent,decodeGoalBranch,rawParent,List.map_append,List.append_assoc,hDecodeHN,hDecodeZero]
private theorem codeParents_map (A B : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool)))) :
    (A.flatMap (fun a => B.filterMap (codeRawParent a))).map (List.map decodeThresholdBound) =
    (A.map decodeGoalBranch).flatMap (fun a => (B.map decodeGoalBranch).filterMap (rawParent a)) := by
  simp only [List.map_flatMap,List.map_filterMap,List.flatMap_map,List.filterMap_map,Function.comp_apply]
  apply congrArg (fun f => A.flatMap f)
  funext a
  apply congrArg (fun f => B.filterMap f)
  funext b
  exact codeRawParent_map a b
private def thresholdParentA9 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc0, bc8, bc9, bc10], some (some bc133)),
 ([bc0, bc8, bc9, bc11], some (some bc134)),
 ([bc0, bc8, bc12, bc13], some (some bc133)),
 ([bc0, bc8, bc12, bc14], some (some bc135)),
 ([bc0, bc15], some (some bc133)),
 ([bc1, bc2, bc3, bc8, bc9, bc10],
  some (some bc133)),
 ([bc1, bc2, bc3, bc8, bc9, bc11],
  some (some bc134)),
 ([bc1, bc2, bc3, bc8, bc12, bc13],
  some (some bc133)),
 ([bc1, bc2, bc3, bc8, bc12, bc14],
  some (some bc135)),
 ([bc1, bc2, bc3, bc15], some (some bc133)),
 ([bc1, bc2, bc4, bc8, bc9, bc10],
  some (some bc136)),
 ([bc1, bc2, bc4, bc8, bc9, bc11],
  some (some (145, true, false))),
 ([bc1, bc2, bc4, bc8, bc12, bc13],
  some (some bc136)),
 ([bc1, bc2, bc4, bc8, bc12, bc14],
  some (some (146, true, false))),
 ([bc1, bc2, bc4, bc15], some (some bc136)),
 ([bc1, bc5, bc6, bc8, bc9, bc10],
  some (some bc133)),
 ([bc1, bc5, bc6, bc8, bc9, bc11],
  some (some bc134)),
 ([bc1, bc5, bc6, bc8, bc12, bc13],
  some (some bc133)),
 ([bc1, bc5, bc6, bc8, bc12, bc14],
  some (some bc135)),
 ([bc1, bc5, bc6, bc15], some (some bc133)),
 ([bc1, bc5, bc7, bc8, bc9, bc10],
  some (some bc137)),
 ([bc1, bc5, bc7, bc8, bc9, bc11],
  some (some (150, true, false))),
 ([bc1, bc5, bc7, bc8, bc12, bc13],
  some (some bc137)),
 ([bc1, bc5, bc7, bc8, bc12, bc14],
  some (some (151, true, false))),
 ([bc1, bc5, bc7, bc15], some (some bc137))]
private def thresholdParentB9 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc8, bc0, bc16, bc17], some none),
 ([bc8, bc0, bc16, bc18], some none),
 ([bc8, bc0, bc19, bc20], some none),
 ([bc8, bc0, bc19, bc21], some none),
 ([bc8, bc1], some none),
 ([bc15, bc0, bc16, bc17], some none),
 ([bc15, bc0, bc16, bc18], some none),
 ([bc15, bc0, bc19, bc20], some none),
 ([bc15, bc0, bc19, bc21], some none),
 ([bc15, bc1], some none)]

private def parentSourceA9 : Array (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := #[([bc0, bc8, bc9, bc10], some (some bc133)),
 ([bc0, bc8, bc9, bc11], some (some bc134)),
 ([bc0, bc8, bc12, bc13], some (some bc133)),
 ([bc0, bc8, bc12, bc14], some (some bc135)),
 ([bc0, bc15], some (some bc133)),
 ([bc1, bc2, bc3, bc8, bc9, bc10],
  some (some bc133)),
 ([bc1, bc2, bc3, bc8, bc9, bc11],
  some (some bc134)),
 ([bc1, bc2, bc3, bc8, bc12, bc13],
  some (some bc133)),
 ([bc1, bc2, bc3, bc8, bc12, bc14],
  some (some bc135)),
 ([bc1, bc2, bc3, bc15], some (some bc133)),
 ([bc1, bc2, bc4, bc8, bc9, bc10],
  some (some bc136)),
 ([bc1, bc2, bc4, bc8, bc9, bc11],
  some (some (145, true, false))),
 ([bc1, bc2, bc4, bc8, bc12, bc13],
  some (some bc136)),
 ([bc1, bc2, bc4, bc8, bc12, bc14],
  some (some (146, true, false))),
 ([bc1, bc2, bc4, bc15], some (some bc136)),
 ([bc1, bc5, bc6, bc8, bc9, bc10],
  some (some bc133)),
 ([bc1, bc5, bc6, bc8, bc9, bc11],
  some (some bc134)),
 ([bc1, bc5, bc6, bc8, bc12, bc13],
  some (some bc133)),
 ([bc1, bc5, bc6, bc8, bc12, bc14],
  some (some bc135)),
 ([bc1, bc5, bc6, bc15], some (some bc133)),
 ([bc1, bc5, bc7, bc8, bc9, bc10],
  some (some bc137)),
 ([bc1, bc5, bc7, bc8, bc9, bc11],
  some (some (150, true, false))),
 ([bc1, bc5, bc7, bc8, bc12, bc13],
  some (some bc137)),
 ([bc1, bc5, bc7, bc8, bc12, bc14],
  some (some (151, true, false))),
 ([bc1, bc5, bc7, bc15], some (some bc137))]

private def parentSourceB9 : Array (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := #[([bc8, bc0, bc16, bc17], some none),
 ([bc8, bc0, bc16, bc18], some none),
 ([bc8, bc0, bc19, bc20], some none),
 ([bc8, bc0, bc19, bc21], some none),
 ([bc8, bc1], some none),
 ([bc15, bc0, bc16, bc17], some none),
 ([bc15, bc0, bc16, bc18], some none),
 ([bc15, bc0, bc19, bc20], some none),
 ([bc15, bc0, bc19, bc21], some none),
 ([bc15, bc1], some none)]

private def codedParents9 (i : ℕ) : List (ℕ × Bool × Bool) :=
  if i < 250 then
    (codeRawParent (parentSourceA9[i / 10]?.getD ([],none)) (parentSourceB9[i % 10]?.getD ([],none))).getD []
  else []

private theorem hThresholdParentA9 : trunkBranches (trunkCatalog.states 9).context ⟨([2],[]),true,([1],[]),false,false,[]⟩ = thresholdParentA9.map decodeGoalBranch := by
  have hi : ((⟨([2],[]),true,([1],[]),false,false,[]⟩ : Section14Spec).first,(⟨([2],[]),true,([1],[]),false,false,[]⟩ : Section14Spec).firstUpper,trunkSpecIncoming (⟨([2],[]),true,([1],[]),false,false,[]⟩ : Section14Spec)) = endpointInput9_0 := by decide +kernel
  have hj : ((⟨([2],[]),true,([1],[]),false,false,[]⟩ : Section14Spec).second,(⟨([2],[]),true,([1],[]),false,false,[]⟩ : Section14Spec).secondUpper,trunkSpecIncoming (⟨([2],[]),true,([1],[]),false,false,[]⟩ : Section14Spec)) = endpointInput9_1 := by decide +kernel
  have heL : trunkEndpointCases (trunkCatalog.states 9).context (⟨([2],[]),true,([1],[]),false,false,[]⟩ : Section14Spec).first (⟨([2],[]),true,([1],[]),false,false,[]⟩ : Section14Spec).firstUpper (trunkSpecIncoming (⟨([2],[]),true,([1],[]),false,false,[]⟩ : Section14Spec)) = endpointCodes9_0.map decodeEndpoint9 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 9).context z.1 z.2.1 z.2.2) hi).trans hEndpoint9_0
  have heR : trunkEndpointCases (trunkCatalog.states 9).context (⟨([2],[]),true,([1],[]),false,false,[]⟩ : Section14Spec).second (⟨([2],[]),true,([1],[]),false,false,[]⟩ : Section14Spec).secondUpper (trunkSpecIncoming (⟨([2],[]),true,([1],[]),false,false,[]⟩ : Section14Spec)) = endpointCodes9_1.map decodeEndpoint9 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 9).context z.1 z.2.1 z.2.2) hj).trans hEndpoint9_1
  unfold trunkBranches
  rw [heL,heR]
  decide +kernel
private theorem hThresholdParentB9 : trunkBranches (trunkCatalog.states 9).context ⟨([1],[]),true,([2],[]),false,false,[]⟩ = thresholdParentB9.map decodeGoalBranch := by
  have hi : ((⟨([1],[]),true,([2],[]),false,false,[]⟩ : Section14Spec).first,(⟨([1],[]),true,([2],[]),false,false,[]⟩ : Section14Spec).firstUpper,trunkSpecIncoming (⟨([1],[]),true,([2],[]),false,false,[]⟩ : Section14Spec)) = endpointInput9_2 := by decide +kernel
  have hj : ((⟨([1],[]),true,([2],[]),false,false,[]⟩ : Section14Spec).second,(⟨([1],[]),true,([2],[]),false,false,[]⟩ : Section14Spec).secondUpper,trunkSpecIncoming (⟨([1],[]),true,([2],[]),false,false,[]⟩ : Section14Spec)) = endpointInput9_3 := by decide +kernel
  have heL : trunkEndpointCases (trunkCatalog.states 9).context (⟨([1],[]),true,([2],[]),false,false,[]⟩ : Section14Spec).first (⟨([1],[]),true,([2],[]),false,false,[]⟩ : Section14Spec).firstUpper (trunkSpecIncoming (⟨([1],[]),true,([2],[]),false,false,[]⟩ : Section14Spec)) = endpointCodes9_2.map decodeEndpoint9 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 9).context z.1 z.2.1 z.2.2) hi).trans hEndpoint9_2
  have heR : trunkEndpointCases (trunkCatalog.states 9).context (⟨([1],[]),true,([2],[]),false,false,[]⟩ : Section14Spec).second (⟨([1],[]),true,([2],[]),false,false,[]⟩ : Section14Spec).secondUpper (trunkSpecIncoming (⟨([1],[]),true,([2],[]),false,false,[]⟩ : Section14Spec)) = endpointCodes9_3.map decodeEndpoint9 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 9).context z.1 z.2.1 z.2.2) hj).trans hEndpoint9_3
  unfold trunkBranches
  rw [heL,heR]
  decide +kernel
private theorem hCodedParentTable9 : (List.range 250).map codedParents9 = thresholdParentA9.flatMap (fun a => thresholdParentB9.filterMap (codeRawParent a)) := by decide +kernel
private theorem hCodedParentList9 : trunkRawParents (trunkCatalog.states 9).context = ((List.range 250).map codedParents9).map (List.map decodeThresholdBound) := by
  unfold trunkRawParents
  rw [hThresholdParentA9,hThresholdParentB9]
  change (thresholdParentA9.map decodeGoalBranch).flatMap (fun a => (thresholdParentB9.map decodeGoalBranch).filterMap (rawParent a)) = ((List.range 250).map codedParents9).map (List.map decodeThresholdBound)
  rw [←codeParents_map,←hCodedParentTable9]
private theorem hCodedParentLength9 : (trunkRawParents (trunkCatalog.states 9).context).length = 250 := by
  rw [hCodedParentList9]; simp only [List.length_map,List.length_range]
private theorem hCodedParents9 (i : ℕ) : (trunkRawParents (trunkCatalog.states 9).context)[i]?.getD [] = (codedParents9 i).map decodeThresholdBound := by
  rw [hCodedParentList9,List.getElem?_map,List.getElem?_map]
  by_cases hi : i < 250
  · rw [List.getElem?_range hi]; rfl
  · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hi)]
    simp only [Option.map_none,Option.getD_none,codedParents9,if_neg hi,List.map_nil]

private theorem hHN : proj lowerHistoryHN = 466397207 := by decide +kernel
private theorem hZero : proj lowerHistoryZero = 559802771 := by decide +kernel

private theorem hA9 : (trunkBranches (trunkCatalog.states 9).context ⟨([2],[]),true,([1],[]),false,false,[]⟩).map branchCode = codesA9 := by
  rw [hThresholdParentA9]
  decide +kernel
private theorem hB9 : (trunkBranches (trunkCatalog.states 9).context ⟨([1],[]),true,([2],[]),false,false,[]⟩).map branchCode = codesB9 := by
  rw [hThresholdParentB9]
  decide +kernel
private def fprints9 : List ℕ := [4325838231, 4163376800, 4425776615, 4417291780, 4165885676, 5317814407, 5155352976, 5417752791, 5409267956, 5157861852, 3714549947, 3552088516, 3814488331, 3806003496, 3554597392, 4706526123, 4544064692, 4806464507, 4797979672, 4546573568, 4499614243, 4337152812, 4599552627, 4591067792, 4339661688, 5491590419, 5329128988, 5591528803, 5583043968, 5331637864, 3695453821, 3532992390, 3795392205, 3786907370, 3535501266, 4687429997, 4524968566, 4787368381, 4778883546, 4527477442, 4850989863, 4688528432, 4950928247, 4942443412, 4691037308, 3968267512, 3805806081, 4068205896, 4059721061, 3808314957, 5763869542, 5601408111, 5863807926, 5855323091, 4762114077, 6755845718, 6593384287, 6855784102, 6847299267, 5754090253, 5152581258, 4990119827, 5252519642, 5244034807, 4150825793, 6144557434, 5982096003, 6244495818, 6236010983, 5142801969, 5937645554, 5775184123, 6037583938, 6029099103, 4935890089, 6929621730, 6767160299, 7029560114, 7021075279, 5927866265, 5133485132, 4971023701, 5233423516, 5224938681, 4131729667, 6125461308, 5962999877, 6225399692, 6216914857, 5123705843, 6289021174, 6126559743, 6388959558, 6380474723, 5287265709, 5406298823, 5243837392, 5506237207, 5497752372, 4404543358, 5452433595, 5289972164, 5552371979, 5543887144, 4450678130, 6444409771, 6281948340, 6544348155, 6535863320, 5442654306, 4889340785, 4726879354, 4989279169, 4980794334, 3887585320, 5881316961, 5718855530, 5981255345, 5972770510, 4879561496, 5626209607, 5463748176, 5726147991, 5717663156, 4624454142, 6618185783, 6455724352, 6718124167, 6709639332, 5616430318, 5586827744, 5424366313, 5686766128, 5678281293, 4585072279, 6578803920, 6416342489, 6678742304, 6670257469, 5577048455, 5977585227, 5815123796, 6077523611, 6069038776, 4975829762, 5094862876, 4932401445, 5194801260, 5186316425, 4093107411, 6413071998, 6250610567, 6513010382, 6504525547, 5411316533, 7405048174, 7242586743, 7504986558, 7496501723, 6403292709, 5801783714, 5639322283, 5901722098, 5893237263, 4800028249, 6793759890, 6631298459, 6893698274, 6885213439, 5792004425, 6586848010, 6424386579, 6686786394, 6678301559, 5585092545, 7578824186, 7416362755, 7678762570, 7670277735, 6577068721, 5782687588, 5620226157, 5882625972, 5874141137, 4780932123, 6774663764, 6612202333, 6874602148, 6866117313, 5772908299, 6938223630, 6775762199, 7038162014, 7029677179, 5936468165, 6055501279, 5893039848, 6155439663, 6146954828, 5053745814, 5250137420, 5087675989, 5350075804, 5341590969, 4248381955, 6242113596, 6079652165, 6342051980, 6333567145, 5240358131, 5206499587, 5044038156, 5306437971, 5297953136, 4204744122, 6198475763, 6036014332, 6298414147, 6289929312, 5196720298, 5423913432, 5261452001, 5523851816, 5515366981, 4422157967, 6415889608, 6253428177, 6515827992, 6507343157, 5414134143, 4979276577, 4816815146, 5079214961, 5070730126, 3977521112, 5971252753, 5808791322, 6071191137, 6062706302, 4969497288, 5775289052, 5612827621, 5875227436, 5866742601, 4773533587, 4892566701, 4730105270, 4992505085, 4984020250, 3890811236]
private theorem hprints9 : (trunkRawParents (trunkCatalog.states 9).context).map fingerprint = fprints9 := by
  have hm (L : List (List CertBound)) :
      L.map fingerprint = (L.map (List.map proj)).map (fun cs => cs.toFinset.sum id) := by
    rw [List.map_map]; rfl
  rw [hm,trunkCodes_map,hA9,hB9,hHN,hZero]
  decide +kernel
private theorem hPar9 : trunkParents (trunkCatalog.states 9).context = trunkRawParents (trunkCatalog.states 9).context := by
  apply Freiman.trunkFast_correctness.1
  apply parents_of_fingerprints
  rw [hprints9]
  apply (List.perm_insertionSort (fun a b : ℕ => a ≤ b) fprints9).nodup_iff.mp
  have hs : (List.insertionSort (fun a b : ℕ => a ≤ b) fprints9).IsChain (fun a b => a < b) := by
    decide +kernel
  exact (List.isChain_iff_pairwise.mp hs).imp (fun h => Nat.ne_of_lt h)


private def goalCodes9_0_0 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([], none)]
private def goalCodes9_0_2 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc8, bc9, bc22, bc26, bc27],
  some (some bc138)),
 ([bc8, bc9, bc22, bc26, bc28],
  some (some (36, true, true))),
 ([bc8, bc9, bc22, bc29, bc30],
  some (some bc138)),
 ([bc8, bc9, bc22, bc29, bc31],
  some (some (39, true, true))),
 ([bc8, bc9, bc23, bc26, bc27],
  some (some (41, true, true))),
 ([bc8, bc9, bc23, bc26, bc28],
  some (some (43, true, true))),
 ([bc8, bc9, bc23, bc29, bc30],
  some (some (41, true, true))),
 ([bc8, bc9, bc23, bc29, bc31],
  some (some (44, true, true))),
 ([bc8, bc12, bc24, bc26, bc27],
  some (some bc138)),
 ([bc8, bc12, bc24, bc26, bc28],
  some (some (36, true, true))),
 ([bc8, bc12, bc24, bc29, bc30],
  some (some bc138)),
 ([bc8, bc12, bc24, bc29, bc31],
  some (some (39, true, true))),
 ([bc8, bc12, bc25, bc26, bc27],
  some (some (46, true, true))),
 ([bc8, bc12, bc25, bc26, bc28],
  some (some (48, true, true))),
 ([bc8, bc12, bc25, bc29, bc30],
  some (some (46, true, true))),
 ([bc8, bc12, bc25, bc29, bc31],
  some (some (49, true, true)))]
private def goalCodes9_0_5 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc15, bc32, (52, false, true)], some (some (65, false, true))),
 ([bc15, bc32, (52, true, false)], some (some (67, false, true))),
 ([bc15, bc33, (56, true, true)], some (some (65, false, true))),
 ([bc15, bc33, (56, false, false)], some (some (68, false, true)))]
private def goalCodes9_0_7 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc0, bc16, bc34, bc38, bc39],
  some (some bc139)),
 ([bc0, bc16, bc34, bc38, bc40],
  some (some (73, true, true))),
 ([bc0, bc16, bc34, bc41, bc42],
  some (some bc139)),
 ([bc0, bc16, bc34, bc41, bc43],
  some (some (77, true, true))),
 ([bc0, bc16, bc35, bc38, bc39],
  some (some (80, true, true))),
 ([bc0, bc16, bc35, bc38, bc40],
  some (some (81, true, true))),
 ([bc0, bc16, bc35, bc41, bc42],
  some (some (80, true, true))),
 ([bc0, bc16, bc35, bc41, bc43],
  some (some (82, true, true))),
 ([bc0, bc19, bc36, bc38, bc39],
  some (some bc139)),
 ([bc0, bc19, bc36, bc38, bc40],
  some (some (73, true, true))),
 ([bc0, bc19, bc36, bc41, bc42],
  some (some bc139)),
 ([bc0, bc19, bc36, bc41, bc43],
  some (some (77, true, true))),
 ([bc0, bc19, bc37, bc38, bc39],
  some (some (85, true, true))),
 ([bc0, bc19, bc37, bc38, bc40],
  some (some (86, true, true))),
 ([bc0, bc19, bc37, bc41, bc42],
  some (some (85, true, true))),
 ([bc0, bc19, bc37, bc41, bc43],
  some (some (87, true, true)))]
private def goalCodes9_0_10 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc1, bc44, bc45, bc50, bc51],
  some (some bc140)),
 ([bc1, bc44, bc45, bc50, bc52],
  some (some (92, false, true))),
 ([bc1, bc44, bc45, bc53, bc54],
  some (some bc140)),
 ([bc1, bc44, bc45, bc53, bc55],
  some (some (97, false, true))),
 ([bc1, bc44, bc46, bc50, bc51],
  some (some (99, false, true))),
 ([bc1, bc44, bc46, bc50, bc52],
  some (some (100, false, true))),
 ([bc1, bc44, bc46, bc53, bc54],
  some (some (99, false, true))),
 ([bc1, bc44, bc46, bc53, bc55],
  some (some (101, false, true))),
 ([bc1, bc47, bc48, bc50, bc51],
  some (some bc140)),
 ([bc1, bc47, bc48, bc50, bc52],
  some (some (92, false, true))),
 ([bc1, bc47, bc48, bc53, bc54],
  some (some bc140)),
 ([bc1, bc47, bc48, bc53, bc55],
  some (some (97, false, true))),
 ([bc1, bc47, bc49, bc50, bc51],
  some (some (104, false, true))),
 ([bc1, bc47, bc49, bc50, bc52],
  some (some (106, false, true))),
 ([bc1, bc47, bc49, bc53, bc54],
  some (some (104, false, true))),
 ([bc1, bc47, bc49, bc53, bc55],
  some (some (107, false, true)))]
private def goalCodes9_0_12 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc74, bc56, bc57, bc62, bc63],
  some (some bc141)),
 ([bc74, bc56, bc57, bc62, bc64],
  some (some (114, true, true))),
 ([bc74, bc56, bc57, bc65, bc66],
  some (some bc141)),
 ([bc74, bc56, bc57, bc65, bc67],
  some (some (119, true, true))),
 ([bc74, bc56, bc58, bc62, bc63],
  some (some (121, true, true))),
 ([bc74, bc56, bc58, bc62, bc64],
  some (some (122, true, true))),
 ([bc74, bc56, bc58, bc65, bc66],
  some (some (121, true, true))),
 ([bc74, bc56, bc58, bc65, bc67],
  some (some (123, true, true))),
 ([bc74, bc59, bc60, bc62, bc63],
  some (some bc141)),
 ([bc74, bc59, bc60, bc62, bc64],
  some (some (114, true, true))),
 ([bc74, bc59, bc60, bc65, bc66],
  some (some bc141)),
 ([bc74, bc59, bc60, bc65, bc67],
  some (some (119, true, true))),
 ([bc74, bc59, bc61, bc62, bc63],
  some (some (126, true, true))),
 ([bc74, bc59, bc61, bc62, bc64],
  some (some (128, true, true))),
 ([bc74, bc59, bc61, bc65, bc66],
  some (some (126, true, true))),
 ([bc74, bc59, bc61, bc65, bc67],
  some (some (129, true, true)))]
private def goalCodes9_0_15 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc75, bc68, bc69], some (some (130, false, true))),
 ([bc75, bc68, bc70], some (some (135, false, true))),
 ([bc75, bc71, bc72], some (some (130, false, true))),
 ([bc75, bc71, bc73], some (some (139, false, true)))]
private def goalCodes9_0_17 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc0, bc8, bc9, bc10], some (some bc133)),
 ([bc0, bc8, bc9, bc11], some (some bc134)),
 ([bc0, bc8, bc12, bc13], some (some bc133)),
 ([bc0, bc8, bc12, bc14], some (some bc135)),
 ([bc0, bc15], some (some bc133)),
 ([bc1, bc2, bc3, bc8, bc9, bc10],
  some (some bc133)),
 ([bc1, bc2, bc3, bc8, bc9, bc11],
  some (some bc134)),
 ([bc1, bc2, bc3, bc8, bc12, bc13],
  some (some bc133)),
 ([bc1, bc2, bc3, bc8, bc12, bc14],
  some (some bc135)),
 ([bc1, bc2, bc3, bc15], some (some bc133)),
 ([bc1, bc2, bc4, bc8, bc9, bc10],
  some (some bc136)),
 ([bc1, bc2, bc4, bc8, bc9, bc11],
  some (some (145, true, false))),
 ([bc1, bc2, bc4, bc8, bc12, bc13],
  some (some bc136)),
 ([bc1, bc2, bc4, bc8, bc12, bc14],
  some (some (146, true, false))),
 ([bc1, bc2, bc4, bc15], some (some bc136)),
 ([bc1, bc5, bc6, bc8, bc9, bc10],
  some (some bc133)),
 ([bc1, bc5, bc6, bc8, bc9, bc11],
  some (some bc134)),
 ([bc1, bc5, bc6, bc8, bc12, bc13],
  some (some bc133)),
 ([bc1, bc5, bc6, bc8, bc12, bc14],
  some (some bc135)),
 ([bc1, bc5, bc6, bc15], some (some bc133)),
 ([bc1, bc5, bc7, bc8, bc9, bc10],
  some (some bc137)),
 ([bc1, bc5, bc7, bc8, bc9, bc11],
  some (some (150, true, false))),
 ([bc1, bc5, bc7, bc8, bc12, bc13],
  some (some bc137)),
 ([bc1, bc5, bc7, bc8, bc12, bc14],
  some (some (151, true, false))),
 ([bc1, bc5, bc7, bc15], some (some bc137))]
private def goalCodes9_0_19 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc74, bc0, bc16, bc17], some (some bc142)),
 ([bc74, bc0, bc16, bc18], some (some (153, true, false))),
 ([bc74, bc0, bc19, bc20], some (some bc142)),
 ([bc74, bc0, bc19, bc21], some (some (154, true, false))),
 ([bc74, bc1], some (some bc142)),
 ([bc75, bc76, bc77, bc0, bc16, bc17],
  some (some bc142)),
 ([bc75, bc76, bc77, bc0, bc16, bc18],
  some (some (153, true, false))),
 ([bc75, bc76, bc77, bc0, bc19, bc20],
  some (some bc142)),
 ([bc75, bc76, bc77, bc0, bc19, bc21],
  some (some (154, true, false))),
 ([bc75, bc76, bc77, bc1], some (some bc142)),
 ([bc75, bc76, bc78, bc0, bc16, bc17],
  some (some (157, true, false))),
 ([bc75, bc76, bc78, bc0, bc16, bc18],
  some (some (159, true, false))),
 ([bc75, bc76, bc78, bc0, bc19, bc20],
  some (some (157, true, false))),
 ([bc75, bc76, bc78, bc0, bc19, bc21],
  some (some (160, true, false))),
 ([bc75, bc76, bc78, bc1], some (some (157, true, false))),
 ([bc75, bc79, bc80, bc0, bc16, bc17],
  some (some bc142)),
 ([bc75, bc79, bc80, bc0, bc16, bc18],
  some (some (153, true, false))),
 ([bc75, bc79, bc80, bc0, bc19, bc20],
  some (some bc142)),
 ([bc75, bc79, bc80, bc0, bc19, bc21],
  some (some (154, true, false))),
 ([bc75, bc79, bc80, bc1], some (some bc142)),
 ([bc75, bc79, bc81, bc0, bc16, bc17],
  some (some (164, true, false))),
 ([bc75, bc79, bc81, bc0, bc16, bc18],
  some (some (165, true, false))),
 ([bc75, bc79, bc81, bc0, bc19, bc20],
  some (some (164, true, false))),
 ([bc75, bc79, bc81, bc0, bc19, bc21],
  some (some (166, true, false))),
 ([bc75, bc79, bc81, bc1], some (some (164, true, false)))]
private def goalCodes9_1_0 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes9_0_0
private def goalCodes9_1_2 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes9_0_2
private def goalCodes9_1_5 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes9_0_5
private def goalCodes9_1_7 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes9_0_7
private def goalCodes9_1_10 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes9_0_10
private def goalCodes9_1_12 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc103, bc82, bc83, bc84, bc90],
  some (some bc143)),
 ([bc103,
   bc82,
   bc83,
   bc84,
   bc91,
   bc92,
   bc93],
  some (some bc143)),
 ([bc103,
   bc82,
   bc83,
   bc84,
   bc91,
   bc92,
   bc94],
  some (some (187, true, true))),
 ([bc103,
   bc82,
   bc83,
   bc84,
   bc91,
   bc95,
   bc96],
  some (some bc143)),
 ([bc103,
   bc82,
   bc83,
   bc84,
   bc91,
   bc95,
   bc97],
  some (some (191, true, true))),
 ([bc103, bc82, bc83, bc85, bc90],
  some (some (194, true, true))),
 ([bc103,
   bc82,
   bc83,
   bc85,
   bc91,
   bc92,
   bc93],
  some (some (194, true, true))),
 ([bc103,
   bc82,
   bc83,
   bc85,
   bc91,
   bc92,
   bc94],
  some (some (195, true, true))),
 ([bc103,
   bc82,
   bc83,
   bc85,
   bc91,
   bc95,
   bc96],
  some (some (194, true, true))),
 ([bc103,
   bc82,
   bc83,
   bc85,
   bc91,
   bc95,
   bc97],
  some (some (196, true, true))),
 ([bc103, bc82, bc86, bc87, bc90],
  some (some bc143)),
 ([bc103,
   bc82,
   bc86,
   bc87,
   bc91,
   bc92,
   bc93],
  some (some bc143)),
 ([bc103,
   bc82,
   bc86,
   bc87,
   bc91,
   bc92,
   bc94],
  some (some (187, true, true))),
 ([bc103,
   bc82,
   bc86,
   bc87,
   bc91,
   bc95,
   bc96],
  some (some bc143)),
 ([bc103,
   bc82,
   bc86,
   bc87,
   bc91,
   bc95,
   bc97],
  some (some (191, true, true))),
 ([bc103, bc82, bc86, bc88, bc90],
  some (some (199, true, true))),
 ([bc103,
   bc82,
   bc86,
   bc88,
   bc91,
   bc92,
   bc93],
  some (some (199, true, true))),
 ([bc103,
   bc82,
   bc86,
   bc88,
   bc91,
   bc92,
   bc94],
  some (some (201, true, true))),
 ([bc103,
   bc82,
   bc86,
   bc88,
   bc91,
   bc95,
   bc96],
  some (some (199, true, true))),
 ([bc103,
   bc82,
   bc86,
   bc88,
   bc91,
   bc95,
   bc97],
  some (some (202, true, true))),
 ([bc103, bc89, bc90], some (some bc143)),
 ([bc103, bc89, bc91, bc92, bc93],
  some (some bc143)),
 ([bc103, bc89, bc91, bc92, bc94],
  some (some (187, true, true))),
 ([bc103, bc89, bc91, bc95, bc96],
  some (some bc143)),
 ([bc103, bc89, bc91, bc95, bc97],
  some (some (191, true, true)))]
private def goalCodes9_1_14 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc104, (206, false, true), bc101], some (some bc144)),
 ([bc104, (206, false, true), bc102], some (some bc144)),
 ([bc104, bc98, bc99, (208, false, true), bc101],
  some (some bc144)),
 ([bc104, bc98, bc99, (208, false, true), bc102],
  some (some bc144)),
 ([bc104, bc98, bc99, (208, true, false), bc101],
  some (some (212, false, true))),
 ([bc104, bc98, bc99, (208, true, false), bc102],
  some (some (212, false, true))),
 ([bc104, bc98, bc100, (213, true, true), bc101],
  some (some bc144)),
 ([bc104, bc98, bc100, (213, true, true), bc102],
  some (some bc144)),
 ([bc104, bc98, bc100, (213, false, false), bc101],
  some (some (215, false, true))),
 ([bc104, bc98, bc100, (213, false, false), bc102],
  some (some (215, false, true)))]
private def goalCodes9_1_17 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes9_0_17
private def goalCodes9_1_19 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc103, bc69, bc0, bc16, bc17],
  some (some bc145)),
 ([bc103, bc69, bc0, bc16, bc18],
  some (some (218, true, false))),
 ([bc103, bc69, bc0, bc19, bc20],
  some (some bc145)),
 ([bc103, bc69, bc0, bc19, bc21],
  some (some (219, true, false))),
 ([bc103, bc69, bc1], some (some bc145)),
 ([bc103, bc70, bc0, bc16, bc17],
  some (some (220, true, false))),
 ([bc103, bc70, bc0, bc16, bc18],
  some (some (221, true, false))),
 ([bc103, bc70, bc0, bc19, bc20],
  some (some (220, true, false))),
 ([bc103, bc70, bc0, bc19, bc21],
  some (some (222, true, false))),
 ([bc103, bc70, bc1], some (some (220, true, false))),
 ([bc104, bc72, bc0, bc16, bc17],
  some (some bc145)),
 ([bc104, bc72, bc0, bc16, bc18],
  some (some (218, true, false))),
 ([bc104, bc72, bc0, bc19, bc20],
  some (some bc145)),
 ([bc104, bc72, bc0, bc19, bc21],
  some (some (219, true, false))),
 ([bc104, bc72, bc1], some (some bc145)),
 ([bc104, bc73, bc0, bc16, bc17],
  some (some (223, true, false))),
 ([bc104, bc73, bc0, bc16, bc18],
  some (some (224, true, false))),
 ([bc104, bc73, bc0, bc19, bc20],
  some (some (223, true, false))),
 ([bc104, bc73, bc0, bc19, bc21],
  some (some (225, true, false))),
 ([bc104, bc73, bc1], some (some (223, true, false)))]
private def goalCodes9_1_21 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc105, (176, false, true)], some (some (227, false, false))),
 ([bc105, (176, true, false)], some none),
 ([bc106, (228, true, true)], some (some (227, false, false))),
 ([bc106, (228, false, false)], some (some (230, false, false)))]
private def goalCodes9_2_0 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes9_0_0
private def goalCodes9_2_2 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes9_0_2
private def goalCodes9_2_5 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes9_0_5
private def goalCodes9_2_7 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes9_0_7
private def goalCodes9_2_10 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes9_0_10
private def goalCodes9_2_12 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes9_1_12
private def goalCodes9_2_14 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes9_1_14
private def goalCodes9_2_18 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc127, bc107, bc109, bc110, (231, false, true)],
  some (some bc146)),
 ([bc127, bc107, bc109, bc110, (231, true, false)],
  some (some (238, true, true))),
 ([bc127, bc107, bc109, bc111, (239, true, true)],
  some (some bc146)),
 ([bc127, bc107, bc109, bc111, (239, false, false)],
  some (some (242, true, true))),
 ([bc127, bc107, (234, true, true)], some (some bc146)),
 ([bc127, bc108, bc109, bc110, (231, false, true)],
  some (some bc146)),
 ([bc127, bc108, bc109, bc110, (231, true, false)],
  some (some (238, true, true))),
 ([bc127, bc108, bc109, bc111, (239, true, true)],
  some (some bc146)),
 ([bc127, bc108, bc109, bc111, (239, false, false)],
  some (some (242, true, true))),
 ([bc127, bc108, (234, true, true)], some (some bc146))]
private def goalCodes9_2_20 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc130, bc112, (248, false, true)], some (some bc147)),
 ([bc130, bc112, bc114, bc115, (249, false, true)],
  some (some bc147)),
 ([bc130, bc112, bc114, bc115, (249, true, false)],
  some (some (253, false, true))),
 ([bc130, bc112, bc114, bc116, (254, true, true)],
  some (some bc147)),
 ([bc130, bc112, bc114, bc116, (254, false, false)],
  some (some (257, false, true))),
 ([bc130, bc113, (248, false, true)], some (some bc147)),
 ([bc130, bc113, bc114, bc115, (249, false, true)],
  some (some bc147)),
 ([bc130, bc113, bc114, bc115, (249, true, false)],
  some (some (253, false, true))),
 ([bc130, bc113, bc114, bc116, (254, true, true)],
  some (some bc147)),
 ([bc130, bc113, bc114, bc116, (254, false, false)],
  some (some (257, false, true)))]
private def goalCodes9_2_22 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc148, bc117, bc118, (259, false, true), bc120],
  some (some bc149)),
 ([bc148, bc117, bc118, (259, false, true), bc121],
  some (some bc149)),
 ([bc148, bc117, bc118, (259, true, false), bc120],
  some (some (266, true, true))),
 ([bc148, bc117, bc118, (259, true, false), bc121],
  some (some (266, true, true))),
 ([bc148, bc117, bc119, (269, true, true), bc120],
  some (some bc149)),
 ([bc148, bc117, bc119, (269, true, true), bc121],
  some (some bc149)),
 ([bc148, bc117, bc119, (269, false, false), bc120],
  some (some (271, true, true))),
 ([bc148, bc117, bc119, (269, false, false), bc121],
  some (some (271, true, true))),
 ([bc148, (260, true, true), bc120], some (some bc149)),
 ([bc148, (260, true, true), bc121], some (some bc149))]
private def goalCodes9_2_24 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc150, (275, false, true), bc125], some (some bc151)),
 ([bc150, (275, false, true), bc126], some (some bc151)),
 ([bc150, bc122, bc123, (280, false, true), bc125],
  some (some bc151)),
 ([bc150, bc122, bc123, (280, false, true), bc126],
  some (some bc151)),
 ([bc150, bc122, bc123, (280, true, false), bc125],
  some (some (282, false, true))),
 ([bc150, bc122, bc123, (280, true, false), bc126],
  some (some (282, false, true))),
 ([bc150, bc122, bc124, (283, true, true), bc125],
  some (some bc151)),
 ([bc150, bc122, bc124, (283, true, true), bc126],
  some (some bc151)),
 ([bc150, bc122, bc124, (283, false, false), bc125],
  some (some (285, false, true))),
 ([bc150, bc122, bc124, (283, false, false), bc126],
  some (some (285, false, true)))]
private def goalCodes9_2_27 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes9_0_17
private def goalCodes9_2_29 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes9_1_19
private def goalCodes9_2_30 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc103, bc69, bc127, bc128], some none),
 ([bc103, bc69, bc127, bc129], some none),
 ([bc103, bc69, bc130, bc131], some none),
 ([bc103, bc69, bc130, bc132], some none),
 ([bc103, bc70, bc127, bc128], some none),
 ([bc103, bc70, bc127, bc129], some none),
 ([bc103, bc70, bc130, bc131], some none),
 ([bc103, bc70, bc130, bc132], some none),
 ([bc104, bc72, bc127, bc128], some none),
 ([bc104, bc72, bc127, bc129], some none),
 ([bc104, bc72, bc130, bc131], some none),
 ([bc104, bc72, bc130, bc132], some none),
 ([bc104, bc73, bc127, bc128], some (some (287, true, false))),
 ([bc104, bc73, bc127, bc129], some (some (290, true, false))),
 ([bc104, bc73, bc130, bc131], some (some (287, true, false))),
 ([bc104, bc73, bc130, bc132], some (some (292, true, false)))]
private def goalCodes9_2_31 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([], some (some (294, false, false)))]
private def cutCodes9_0 : List (ℕ × Bool × Bool) := [(7, false, true)]
private def cutCodes9_1 : List (ℕ × Bool × Bool) := [(7, true, false), (177, false, false), (176, true, false)]
private def cutCodes9_2 : List (ℕ × Bool × Bool) := [(7, true, false), (177, false, false), (176, false, true)]

private theorem hGoal9_0_0 : trunkGoalBranches (trunkCatalog.states 9) 0 0 = goalCodes9_0_0.map decodeGoalBranch := by
  decide +kernel

private abbrev goalSpec9_0_2 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 0))[2-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_0_2 : trunkGoalBranches (trunkCatalog.states 9) 0 2 = goalCodes9_0_2.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 9).context goalSpec9_0_2 = _
  exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_0_2
    endpointInput9_4 endpointInput9_5 (([bc8] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes9_4.map decodeEndpoint9) (endpointCodes9_5.map decodeEndpoint9)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_4 hEndpoint9_5).trans
    (by decide +kernel)

private abbrev goalSpec9_0_5 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 0))[5-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_0_5 : trunkGoalBranches (trunkCatalog.states 9) 0 5 = goalCodes9_0_5.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 9).context goalSpec9_0_5 = _
  exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_0_5
    endpointInput9_6 endpointInput9_7 (([bc15] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes9_6.map decodeEndpoint9) (endpointCodes9_7.map decodeEndpoint9)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_6 hEndpoint9_7).trans
    (by decide +kernel)

private abbrev goalSpec9_0_7 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 0))[7-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_0_7 : trunkGoalBranches (trunkCatalog.states 9) 0 7 = goalCodes9_0_7.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 9).context goalSpec9_0_7 = _
  exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_0_7
    endpointInput9_8 endpointInput9_9 (([bc0] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes9_8.map decodeEndpoint9) (endpointCodes9_9.map decodeEndpoint9)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_8 hEndpoint9_9).trans
    (by decide +kernel)

private abbrev goalSpec9_0_10 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 0))[10-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_0_10 : trunkGoalBranches (trunkCatalog.states 9) 0 10 = goalCodes9_0_10.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 9).context goalSpec9_0_10 = _
  exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_0_10
    endpointInput9_10 endpointInput9_11 (([bc1] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes9_10.map decodeEndpoint9) (endpointCodes9_11.map decodeEndpoint9)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_10 hEndpoint9_11).trans
    (by decide +kernel)

private abbrev goalSpec9_0_12 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 0))[12-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_0_12 : trunkGoalBranches (trunkCatalog.states 9) 0 12 = goalCodes9_0_12.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 9).context goalSpec9_0_12 = _
  exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_0_12
    endpointInput9_12 endpointInput9_13 (([bc74] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes9_12.map decodeEndpoint9) (endpointCodes9_13.map decodeEndpoint9)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_12 hEndpoint9_13).trans
    (by decide +kernel)

private abbrev goalSpec9_0_15 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 0))[15-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_0_15 : trunkGoalBranches (trunkCatalog.states 9) 0 15 = goalCodes9_0_15.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 9).context goalSpec9_0_15 = _
  exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_0_15
    endpointInput9_14 endpointInput9_15 (([bc75] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes9_14.map decodeEndpoint9) (endpointCodes9_15.map decodeEndpoint9)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_14 hEndpoint9_15).trans
    (by decide +kernel)

private abbrev goalSpec9_0_17 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 0))[17-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_0_17 : trunkGoalBranches (trunkCatalog.states 9) 0 17 = goalCodes9_0_17.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 9).context goalSpec9_0_17 = _
  exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_0_17
    endpointInput9_0 endpointInput9_1 (([] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes9_0.map decodeEndpoint9) (endpointCodes9_1.map decodeEndpoint9)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_0 hEndpoint9_1).trans
    (by decide +kernel)

private abbrev goalSpec9_0_19 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 0))[19-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_0_19 : trunkGoalBranches (trunkCatalog.states 9) 0 19 = goalCodes9_0_19.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 9).context goalSpec9_0_19 = _
  exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_0_19
    endpointInput9_16 endpointInput9_3 (([] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes9_16.map decodeEndpoint9) (endpointCodes9_3.map decodeEndpoint9)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_16 hEndpoint9_3).trans
    (by decide +kernel)

private theorem hGoal9_1_0 : trunkGoalBranches (trunkCatalog.states 9) 1 0 = goalCodes9_1_0.map decodeGoalBranch := by
  exact hGoal9_0_0

private abbrev goalSpec9_1_2 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 1))[2-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_1_2 : trunkGoalBranches (trunkCatalog.states 9) 1 2 = goalCodes9_1_2.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 9) 1 2 = trunkGoalBranches (trunkCatalog.states 9) 0 2 := by
      apply congrArg (trunkBranches (trunkCatalog.states 9).context)
      decide +kernel
    exact he.trans hGoal9_0_2
  | change trunkBranches (trunkCatalog.states 9).context goalSpec9_1_2 = _
    exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_1_2
      endpointInput9_4 endpointInput9_5 (([bc8] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
      (endpointCodes9_4.map decodeEndpoint9) (endpointCodes9_5.map decodeEndpoint9)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_4 hEndpoint9_5).trans
      (by decide +kernel)

private abbrev goalSpec9_1_5 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 1))[5-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_1_5 : trunkGoalBranches (trunkCatalog.states 9) 1 5 = goalCodes9_1_5.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 9) 1 5 = trunkGoalBranches (trunkCatalog.states 9) 0 5 := by
      apply congrArg (trunkBranches (trunkCatalog.states 9).context)
      decide +kernel
    exact he.trans hGoal9_0_5
  | change trunkBranches (trunkCatalog.states 9).context goalSpec9_1_5 = _
    exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_1_5
      endpointInput9_6 endpointInput9_7 (([bc15] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
      (endpointCodes9_6.map decodeEndpoint9) (endpointCodes9_7.map decodeEndpoint9)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_6 hEndpoint9_7).trans
      (by decide +kernel)

private abbrev goalSpec9_1_7 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 1))[7-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_1_7 : trunkGoalBranches (trunkCatalog.states 9) 1 7 = goalCodes9_1_7.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 9) 1 7 = trunkGoalBranches (trunkCatalog.states 9) 0 7 := by
      apply congrArg (trunkBranches (trunkCatalog.states 9).context)
      decide +kernel
    exact he.trans hGoal9_0_7
  | change trunkBranches (trunkCatalog.states 9).context goalSpec9_1_7 = _
    exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_1_7
      endpointInput9_8 endpointInput9_9 (([bc0] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
      (endpointCodes9_8.map decodeEndpoint9) (endpointCodes9_9.map decodeEndpoint9)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_8 hEndpoint9_9).trans
      (by decide +kernel)

private abbrev goalSpec9_1_10 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 1))[10-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_1_10 : trunkGoalBranches (trunkCatalog.states 9) 1 10 = goalCodes9_1_10.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 9) 1 10 = trunkGoalBranches (trunkCatalog.states 9) 0 10 := by
      apply congrArg (trunkBranches (trunkCatalog.states 9).context)
      decide +kernel
    exact he.trans hGoal9_0_10
  | change trunkBranches (trunkCatalog.states 9).context goalSpec9_1_10 = _
    exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_1_10
      endpointInput9_10 endpointInput9_11 (([bc1] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
      (endpointCodes9_10.map decodeEndpoint9) (endpointCodes9_11.map decodeEndpoint9)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_10 hEndpoint9_11).trans
      (by decide +kernel)

private abbrev goalSpec9_1_12 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 1))[12-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_1_12 : trunkGoalBranches (trunkCatalog.states 9) 1 12 = goalCodes9_1_12.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 9).context goalSpec9_1_12 = _
  exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_1_12
    endpointInput9_17 endpointInput9_18 (([bc103] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes9_17.map decodeEndpoint9) (endpointCodes9_18.map decodeEndpoint9)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_17 hEndpoint9_18).trans
    (by decide +kernel)

private abbrev goalSpec9_1_14 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 1))[14-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_1_14 : trunkGoalBranches (trunkCatalog.states 9) 1 14 = goalCodes9_1_14.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 9).context goalSpec9_1_14 = _
  exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_1_14
    endpointInput9_19 endpointInput9_20 (([bc104] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes9_19.map decodeEndpoint9) (endpointCodes9_20.map decodeEndpoint9)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_19 hEndpoint9_20).trans
    (by decide +kernel)

private abbrev goalSpec9_1_17 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 1))[17-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_1_17 : trunkGoalBranches (trunkCatalog.states 9) 1 17 = goalCodes9_1_17.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 9) 1 17 = trunkGoalBranches (trunkCatalog.states 9) 0 17 := by
      apply congrArg (trunkBranches (trunkCatalog.states 9).context)
      decide +kernel
    exact he.trans hGoal9_0_17
  | change trunkBranches (trunkCatalog.states 9).context goalSpec9_1_17 = _
    exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_1_17
      endpointInput9_0 endpointInput9_1 (([] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
      (endpointCodes9_0.map decodeEndpoint9) (endpointCodes9_1.map decodeEndpoint9)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_0 hEndpoint9_1).trans
      (by decide +kernel)

private abbrev goalSpec9_1_19 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 1))[19-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_1_19 : trunkGoalBranches (trunkCatalog.states 9) 1 19 = goalCodes9_1_19.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 9).context goalSpec9_1_19 = _
  exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_1_19
    endpointInput9_21 endpointInput9_3 (([] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes9_21.map decodeEndpoint9) (endpointCodes9_3.map decodeEndpoint9)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_21 hEndpoint9_3).trans
    (by decide +kernel)

private abbrev goalSpec9_1_21 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 1))[21-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_1_21 : trunkGoalBranches (trunkCatalog.states 9) 1 21 = goalCodes9_1_21.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 9).context goalSpec9_1_21 = _
  exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_1_21
    endpointInput9_22 endpointInput9_23 (([] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes9_22.map decodeEndpoint9) (endpointCodes9_23.map decodeEndpoint9)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_22 hEndpoint9_23).trans
    (by decide +kernel)

private theorem hGoal9_2_0 : trunkGoalBranches (trunkCatalog.states 9) 2 0 = goalCodes9_2_0.map decodeGoalBranch := by
  exact hGoal9_0_0

private abbrev goalSpec9_2_2 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 2))[2-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_2_2 : trunkGoalBranches (trunkCatalog.states 9) 2 2 = goalCodes9_2_2.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 9) 2 2 = trunkGoalBranches (trunkCatalog.states 9) 0 2 := by
      apply congrArg (trunkBranches (trunkCatalog.states 9).context)
      decide +kernel
    exact he.trans hGoal9_0_2
  | change trunkBranches (trunkCatalog.states 9).context goalSpec9_2_2 = _
    exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_2_2
      endpointInput9_4 endpointInput9_5 (([bc8] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
      (endpointCodes9_4.map decodeEndpoint9) (endpointCodes9_5.map decodeEndpoint9)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_4 hEndpoint9_5).trans
      (by decide +kernel)

private abbrev goalSpec9_2_5 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 2))[5-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_2_5 : trunkGoalBranches (trunkCatalog.states 9) 2 5 = goalCodes9_2_5.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 9) 2 5 = trunkGoalBranches (trunkCatalog.states 9) 0 5 := by
      apply congrArg (trunkBranches (trunkCatalog.states 9).context)
      decide +kernel
    exact he.trans hGoal9_0_5
  | change trunkBranches (trunkCatalog.states 9).context goalSpec9_2_5 = _
    exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_2_5
      endpointInput9_6 endpointInput9_7 (([bc15] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
      (endpointCodes9_6.map decodeEndpoint9) (endpointCodes9_7.map decodeEndpoint9)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_6 hEndpoint9_7).trans
      (by decide +kernel)

private abbrev goalSpec9_2_7 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 2))[7-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_2_7 : trunkGoalBranches (trunkCatalog.states 9) 2 7 = goalCodes9_2_7.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 9) 2 7 = trunkGoalBranches (trunkCatalog.states 9) 0 7 := by
      apply congrArg (trunkBranches (trunkCatalog.states 9).context)
      decide +kernel
    exact he.trans hGoal9_0_7
  | change trunkBranches (trunkCatalog.states 9).context goalSpec9_2_7 = _
    exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_2_7
      endpointInput9_8 endpointInput9_9 (([bc0] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
      (endpointCodes9_8.map decodeEndpoint9) (endpointCodes9_9.map decodeEndpoint9)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_8 hEndpoint9_9).trans
      (by decide +kernel)

private abbrev goalSpec9_2_10 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 2))[10-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_2_10 : trunkGoalBranches (trunkCatalog.states 9) 2 10 = goalCodes9_2_10.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 9) 2 10 = trunkGoalBranches (trunkCatalog.states 9) 0 10 := by
      apply congrArg (trunkBranches (trunkCatalog.states 9).context)
      decide +kernel
    exact he.trans hGoal9_0_10
  | change trunkBranches (trunkCatalog.states 9).context goalSpec9_2_10 = _
    exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_2_10
      endpointInput9_10 endpointInput9_11 (([bc1] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
      (endpointCodes9_10.map decodeEndpoint9) (endpointCodes9_11.map decodeEndpoint9)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_10 hEndpoint9_11).trans
      (by decide +kernel)

private abbrev goalSpec9_2_12 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 2))[12-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_2_12 : trunkGoalBranches (trunkCatalog.states 9) 2 12 = goalCodes9_2_12.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 9) 2 12 = trunkGoalBranches (trunkCatalog.states 9) 1 12 := by
      apply congrArg (trunkBranches (trunkCatalog.states 9).context)
      decide +kernel
    exact he.trans hGoal9_1_12
  | change trunkBranches (trunkCatalog.states 9).context goalSpec9_2_12 = _
    exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_2_12
      endpointInput9_17 endpointInput9_18 (([bc103] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
      (endpointCodes9_17.map decodeEndpoint9) (endpointCodes9_18.map decodeEndpoint9)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_17 hEndpoint9_18).trans
      (by decide +kernel)

private abbrev goalSpec9_2_14 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 2))[14-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_2_14 : trunkGoalBranches (trunkCatalog.states 9) 2 14 = goalCodes9_2_14.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 9) 2 14 = trunkGoalBranches (trunkCatalog.states 9) 1 14 := by
      apply congrArg (trunkBranches (trunkCatalog.states 9).context)
      decide +kernel
    exact he.trans hGoal9_1_14
  | change trunkBranches (trunkCatalog.states 9).context goalSpec9_2_14 = _
    exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_2_14
      endpointInput9_19 endpointInput9_20 (([bc104] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
      (endpointCodes9_19.map decodeEndpoint9) (endpointCodes9_20.map decodeEndpoint9)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_19 hEndpoint9_20).trans
      (by decide +kernel)

private abbrev goalSpec9_2_18 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 2))[18-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_2_18 : trunkGoalBranches (trunkCatalog.states 9) 2 18 = goalCodes9_2_18.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 9).context goalSpec9_2_18 = _
  exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_2_18
    endpointInput9_24 endpointInput9_25 (([bc127] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes9_24.map decodeEndpoint9) (endpointCodes9_25.map decodeEndpoint9)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_24 hEndpoint9_25).trans
    (by decide +kernel)

private abbrev goalSpec9_2_20 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 2))[20-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_2_20 : trunkGoalBranches (trunkCatalog.states 9) 2 20 = goalCodes9_2_20.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 9).context goalSpec9_2_20 = _
  exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_2_20
    endpointInput9_26 endpointInput9_27 (([bc130] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes9_26.map decodeEndpoint9) (endpointCodes9_27.map decodeEndpoint9)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_26 hEndpoint9_27).trans
    (by decide +kernel)

private abbrev goalSpec9_2_22 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 2))[22-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_2_22 : trunkGoalBranches (trunkCatalog.states 9) 2 22 = goalCodes9_2_22.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 9).context goalSpec9_2_22 = _
  exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_2_22
    endpointInput9_28 endpointInput9_29 (([bc148] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes9_28.map decodeEndpoint9) (endpointCodes9_29.map decodeEndpoint9)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_28 hEndpoint9_29).trans
    (by decide +kernel)

private abbrev goalSpec9_2_24 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 2))[24-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_2_24 : trunkGoalBranches (trunkCatalog.states 9) 2 24 = goalCodes9_2_24.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 9).context goalSpec9_2_24 = _
  exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_2_24
    endpointInput9_30 endpointInput9_31 (([bc150] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes9_30.map decodeEndpoint9) (endpointCodes9_31.map decodeEndpoint9)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_30 hEndpoint9_31).trans
    (by decide +kernel)

private abbrev goalSpec9_2_27 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 2))[27-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_2_27 : trunkGoalBranches (trunkCatalog.states 9) 2 27 = goalCodes9_2_27.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 9) 2 27 = trunkGoalBranches (trunkCatalog.states 9) 0 17 := by
      apply congrArg (trunkBranches (trunkCatalog.states 9).context)
      decide +kernel
    exact he.trans hGoal9_0_17
  | change trunkBranches (trunkCatalog.states 9).context goalSpec9_2_27 = _
    exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_2_27
      endpointInput9_0 endpointInput9_1 (([] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
      (endpointCodes9_0.map decodeEndpoint9) (endpointCodes9_1.map decodeEndpoint9)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_0 hEndpoint9_1).trans
      (by decide +kernel)

private abbrev goalSpec9_2_29 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 2))[29-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_2_29 : trunkGoalBranches (trunkCatalog.states 9) 2 29 = goalCodes9_2_29.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 9) 2 29 = trunkGoalBranches (trunkCatalog.states 9) 1 19 := by
      apply congrArg (trunkBranches (trunkCatalog.states 9).context)
      decide +kernel
    exact he.trans hGoal9_1_19
  | change trunkBranches (trunkCatalog.states 9).context goalSpec9_2_29 = _
    exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_2_29
      endpointInput9_21 endpointInput9_3 (([] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
      (endpointCodes9_21.map decodeEndpoint9) (endpointCodes9_3.map decodeEndpoint9)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_21 hEndpoint9_3).trans
      (by decide +kernel)

private abbrev goalSpec9_2_30 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 2))[30-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_2_30 : trunkGoalBranches (trunkCatalog.states 9) 2 30 = goalCodes9_2_30.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 9).context goalSpec9_2_30 = _
  exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_2_30
    endpointInput9_21 endpointInput9_32 (([] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes9_21.map decodeEndpoint9) (endpointCodes9_32.map decodeEndpoint9)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_21 hEndpoint9_32).trans
    (by decide +kernel)

private abbrev goalSpec9_2_31 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 2))[31-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_2_31 : trunkGoalBranches (trunkCatalog.states 9) 2 31 = goalCodes9_2_31.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 9).context goalSpec9_2_31 = _
  exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_2_31
    endpointInput9_33 endpointInput9_23 (([] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes9_33.map decodeEndpoint9) (endpointCodes9_23.map decodeEndpoint9)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_33 hEndpoint9_23).trans
    (by decide +kernel)

private theorem hCut9_0 : (trunkPlanAt (trunkCatalog.states 9) 0).cuts = cutCodes9_0.map decodeThresholdBound := by decide +kernel

private theorem hCut9_1 : (trunkPlanAt (trunkCatalog.states 9) 1).cuts = cutCodes9_1.map decodeThresholdBound := by decide +kernel

private theorem hCut9_2 : (trunkPlanAt (trunkCatalog.states 9) 2).cuts = cutCodes9_2.map decodeThresholdBound := by decide +kernel

private def codedGoals9 (pi goal : ℕ) : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) :=
  if pi = 0 ∧ goal = 0 then goalCodes9_0_0 else
  if pi = 0 ∧ goal = 2 then goalCodes9_0_2 else
  if pi = 0 ∧ goal = 5 then goalCodes9_0_5 else
  if pi = 0 ∧ goal = 7 then goalCodes9_0_7 else
  if pi = 0 ∧ goal = 10 then goalCodes9_0_10 else
  if pi = 0 ∧ goal = 12 then goalCodes9_0_12 else
  if pi = 0 ∧ goal = 15 then goalCodes9_0_15 else
  if pi = 0 ∧ goal = 17 then goalCodes9_0_17 else
  if pi = 0 ∧ goal = 19 then goalCodes9_0_19 else
  if pi = 1 ∧ goal = 0 then goalCodes9_1_0 else
  if pi = 1 ∧ goal = 2 then goalCodes9_1_2 else
  if pi = 1 ∧ goal = 5 then goalCodes9_1_5 else
  if pi = 1 ∧ goal = 7 then goalCodes9_1_7 else
  if pi = 1 ∧ goal = 10 then goalCodes9_1_10 else
  if pi = 1 ∧ goal = 12 then goalCodes9_1_12 else
  if pi = 1 ∧ goal = 14 then goalCodes9_1_14 else
  if pi = 1 ∧ goal = 17 then goalCodes9_1_17 else
  if pi = 1 ∧ goal = 19 then goalCodes9_1_19 else
  if pi = 1 ∧ goal = 21 then goalCodes9_1_21 else
  if pi = 2 ∧ goal = 0 then goalCodes9_2_0 else
  if pi = 2 ∧ goal = 2 then goalCodes9_2_2 else
  if pi = 2 ∧ goal = 5 then goalCodes9_2_5 else
  if pi = 2 ∧ goal = 7 then goalCodes9_2_7 else
  if pi = 2 ∧ goal = 10 then goalCodes9_2_10 else
  if pi = 2 ∧ goal = 12 then goalCodes9_2_12 else
  if pi = 2 ∧ goal = 14 then goalCodes9_2_14 else
  if pi = 2 ∧ goal = 18 then goalCodes9_2_18 else
  if pi = 2 ∧ goal = 20 then goalCodes9_2_20 else
  if pi = 2 ∧ goal = 22 then goalCodes9_2_22 else
  if pi = 2 ∧ goal = 24 then goalCodes9_2_24 else
  if pi = 2 ∧ goal = 27 then goalCodes9_2_27 else
  if pi = 2 ∧ goal = 29 then goalCodes9_2_29 else
  if pi = 2 ∧ goal = 30 then goalCodes9_2_30 else
  if pi = 2 ∧ goal = 31 then goalCodes9_2_31 else
  []

private def codedKeys9 : List (ℕ × ℕ) := [(0, 0), (0, 2), (0, 5), (0, 7), (0, 10), (0, 12), (0, 15), (0, 17), (0, 19), (1, 0), (1, 2), (1, 5), (1, 7), (1, 10), (1, 12), (1, 14), (1, 17), (1, 19), (1, 21), (2, 0), (2, 2), (2, 5), (2, 7), (2, 10), (2, 12), (2, 14), (2, 18), (2, 20), (2, 22), (2, 24), (2, 27), (2, 29), (2, 30), (2, 31)]

private theorem hCodedGoals9 (pi goal : ℕ) (hm : (pi,goal) ∈ codedKeys9) : trunkGoalBranches (trunkCatalog.states 9) pi goal = (codedGoals9 pi goal).map decodeGoalBranch := by
  unfold codedGoals9
  by_cases h0 : pi = 0 ∧ goal = 0
  · rw [if_pos h0]
    rcases h0 with ⟨rfl,rfl⟩
    exact hGoal9_0_0
  rw [if_neg h0]
  by_cases h1 : pi = 0 ∧ goal = 2
  · rw [if_pos h1]
    rcases h1 with ⟨rfl,rfl⟩
    exact hGoal9_0_2
  rw [if_neg h1]
  by_cases h2 : pi = 0 ∧ goal = 5
  · rw [if_pos h2]
    rcases h2 with ⟨rfl,rfl⟩
    exact hGoal9_0_5
  rw [if_neg h2]
  by_cases h3 : pi = 0 ∧ goal = 7
  · rw [if_pos h3]
    rcases h3 with ⟨rfl,rfl⟩
    exact hGoal9_0_7
  rw [if_neg h3]
  by_cases h4 : pi = 0 ∧ goal = 10
  · rw [if_pos h4]
    rcases h4 with ⟨rfl,rfl⟩
    exact hGoal9_0_10
  rw [if_neg h4]
  by_cases h5 : pi = 0 ∧ goal = 12
  · rw [if_pos h5]
    rcases h5 with ⟨rfl,rfl⟩
    exact hGoal9_0_12
  rw [if_neg h5]
  by_cases h6 : pi = 0 ∧ goal = 15
  · rw [if_pos h6]
    rcases h6 with ⟨rfl,rfl⟩
    exact hGoal9_0_15
  rw [if_neg h6]
  by_cases h7 : pi = 0 ∧ goal = 17
  · rw [if_pos h7]
    rcases h7 with ⟨rfl,rfl⟩
    exact hGoal9_0_17
  rw [if_neg h7]
  by_cases h8 : pi = 0 ∧ goal = 19
  · rw [if_pos h8]
    rcases h8 with ⟨rfl,rfl⟩
    exact hGoal9_0_19
  rw [if_neg h8]
  by_cases h9 : pi = 1 ∧ goal = 0
  · rw [if_pos h9]
    rcases h9 with ⟨rfl,rfl⟩
    exact hGoal9_1_0
  rw [if_neg h9]
  by_cases h10 : pi = 1 ∧ goal = 2
  · rw [if_pos h10]
    rcases h10 with ⟨rfl,rfl⟩
    exact hGoal9_1_2
  rw [if_neg h10]
  by_cases h11 : pi = 1 ∧ goal = 5
  · rw [if_pos h11]
    rcases h11 with ⟨rfl,rfl⟩
    exact hGoal9_1_5
  rw [if_neg h11]
  by_cases h12 : pi = 1 ∧ goal = 7
  · rw [if_pos h12]
    rcases h12 with ⟨rfl,rfl⟩
    exact hGoal9_1_7
  rw [if_neg h12]
  by_cases h13 : pi = 1 ∧ goal = 10
  · rw [if_pos h13]
    rcases h13 with ⟨rfl,rfl⟩
    exact hGoal9_1_10
  rw [if_neg h13]
  by_cases h14 : pi = 1 ∧ goal = 12
  · rw [if_pos h14]
    rcases h14 with ⟨rfl,rfl⟩
    exact hGoal9_1_12
  rw [if_neg h14]
  by_cases h15 : pi = 1 ∧ goal = 14
  · rw [if_pos h15]
    rcases h15 with ⟨rfl,rfl⟩
    exact hGoal9_1_14
  rw [if_neg h15]
  by_cases h16 : pi = 1 ∧ goal = 17
  · rw [if_pos h16]
    rcases h16 with ⟨rfl,rfl⟩
    exact hGoal9_1_17
  rw [if_neg h16]
  by_cases h17 : pi = 1 ∧ goal = 19
  · rw [if_pos h17]
    rcases h17 with ⟨rfl,rfl⟩
    exact hGoal9_1_19
  rw [if_neg h17]
  by_cases h18 : pi = 1 ∧ goal = 21
  · rw [if_pos h18]
    rcases h18 with ⟨rfl,rfl⟩
    exact hGoal9_1_21
  rw [if_neg h18]
  by_cases h19 : pi = 2 ∧ goal = 0
  · rw [if_pos h19]
    rcases h19 with ⟨rfl,rfl⟩
    exact hGoal9_2_0
  rw [if_neg h19]
  by_cases h20 : pi = 2 ∧ goal = 2
  · rw [if_pos h20]
    rcases h20 with ⟨rfl,rfl⟩
    exact hGoal9_2_2
  rw [if_neg h20]
  by_cases h21 : pi = 2 ∧ goal = 5
  · rw [if_pos h21]
    rcases h21 with ⟨rfl,rfl⟩
    exact hGoal9_2_5
  rw [if_neg h21]
  by_cases h22 : pi = 2 ∧ goal = 7
  · rw [if_pos h22]
    rcases h22 with ⟨rfl,rfl⟩
    exact hGoal9_2_7
  rw [if_neg h22]
  by_cases h23 : pi = 2 ∧ goal = 10
  · rw [if_pos h23]
    rcases h23 with ⟨rfl,rfl⟩
    exact hGoal9_2_10
  rw [if_neg h23]
  by_cases h24 : pi = 2 ∧ goal = 12
  · rw [if_pos h24]
    rcases h24 with ⟨rfl,rfl⟩
    exact hGoal9_2_12
  rw [if_neg h24]
  by_cases h25 : pi = 2 ∧ goal = 14
  · rw [if_pos h25]
    rcases h25 with ⟨rfl,rfl⟩
    exact hGoal9_2_14
  rw [if_neg h25]
  by_cases h26 : pi = 2 ∧ goal = 18
  · rw [if_pos h26]
    rcases h26 with ⟨rfl,rfl⟩
    exact hGoal9_2_18
  rw [if_neg h26]
  by_cases h27 : pi = 2 ∧ goal = 20
  · rw [if_pos h27]
    rcases h27 with ⟨rfl,rfl⟩
    exact hGoal9_2_20
  rw [if_neg h27]
  by_cases h28 : pi = 2 ∧ goal = 22
  · rw [if_pos h28]
    rcases h28 with ⟨rfl,rfl⟩
    exact hGoal9_2_22
  rw [if_neg h28]
  by_cases h29 : pi = 2 ∧ goal = 24
  · rw [if_pos h29]
    rcases h29 with ⟨rfl,rfl⟩
    exact hGoal9_2_24
  rw [if_neg h29]
  by_cases h30 : pi = 2 ∧ goal = 27
  · rw [if_pos h30]
    rcases h30 with ⟨rfl,rfl⟩
    exact hGoal9_2_27
  rw [if_neg h30]
  by_cases h31 : pi = 2 ∧ goal = 29
  · rw [if_pos h31]
    rcases h31 with ⟨rfl,rfl⟩
    exact hGoal9_2_29
  rw [if_neg h31]
  by_cases h32 : pi = 2 ∧ goal = 30
  · rw [if_pos h32]
    rcases h32 with ⟨rfl,rfl⟩
    exact hGoal9_2_30
  rw [if_neg h32]
  by_cases h33 : pi = 2 ∧ goal = 31
  · rw [if_pos h33]
    rcases h33 with ⟨rfl,rfl⟩
    exact hGoal9_2_31
  rw [if_neg h33]
  simp_all only [codedKeys9,List.mem_cons,List.mem_nil_iff,or_false,Prod.mk.injEq]

private def codedCuts9 (pi : ℕ) : List (ℕ × Bool × Bool) :=
  if pi = 0 then cutCodes9_0 else
  if pi = 1 then cutCodes9_1 else
  if pi = 2 then cutCodes9_2 else
  []

private theorem hCodedCuts9 (pi goal : ℕ) (hm : (pi,goal) ∈ codedKeys9) : (trunkPlanAt (trunkCatalog.states 9) pi).cuts = (codedCuts9 pi).map decodeThresholdBound := by
  unfold codedCuts9
  by_cases h0 : pi = 0
  · rw [if_pos h0]
    subst pi
    exact hCut9_0
  rw [if_neg h0]
  by_cases h1 : pi = 1
  · rw [if_pos h1]
    subst pi
    exact hCut9_1
  rw [if_neg h1]
  by_cases h2 : pi = 2
  · rw [if_pos h2]
    subst pi
    exact hCut9_2
  rw [if_neg h2]
  simp_all only [codedKeys9,List.mem_cons,List.mem_nil_iff,or_false,Prod.mk.injEq,false_and]

private def codedValid9 (g : TrunkGroup) : Prop := (g.plan,g.goal) ∈ codedKeys9 ∧ codeGroupValid (trunkCatalog.states 9) codedParents9 250 codedCuts9 codedGoals9 g

private theorem codedValid9_sound (g : TrunkGroup) (h : codedValid9 g) : trunkGroupValidFast 9 g :=
  codeGroupValid_sound 9 codedParents9 250 codedCuts9 codedGoals9 g hCodedParents9 hCodedParentLength9 (hCodedCuts9 g.plan g.goal h.1) (hCodedGoals9 g.plan g.goal h.1) h.2



set_option Elab.async false
theorem batch_chunk_0 : ∀ j ∈ List.range 20, codedValid9 (trunkStateData09Part01.getD j ⟨0,[],0,[]⟩) := by
  unfold codedValid9 codeGroupValid
  decide +kernel

theorem batch_chunk_20 : ∀ j ∈ List.range' 20 20, codedValid9 (trunkStateData09Part01.getD j ⟨0,[],0,[]⟩) := by
  unfold codedValid9 codeGroupValid
  decide +kernel

theorem batch_chunk_40 : ∀ j ∈ List.range' 40 20, codedValid9 (trunkStateData09Part01.getD j ⟨0,[],0,[]⟩) := by
  unfold codedValid9 codeGroupValid
  decide +kernel

theorem batch_chunk_60 : ∀ j ∈ List.range' 60 20, codedValid9 (trunkStateData09Part01.getD j ⟨0,[],0,[]⟩) := by
  unfold codedValid9 codeGroupValid
  decide +kernel

theorem batch_chunk_80 : ∀ j ∈ List.range' 80 20, codedValid9 (trunkStateData09Part01.getD j ⟨0,[],0,[]⟩) := by
  unfold codedValid9 codeGroupValid
  decide +kernel

theorem batch_key (j : ℕ) (hj : j < 100) : codedValid9 (trunkStateData09Part01.getD j ⟨0,[],0,[]⟩) := by
  rcases lt_or_ge j 20 with h0 | h0
  · exact batch_chunk_0 j (List.mem_range.2 (by omega))
  rcases lt_or_ge j 40 with h1 | h1
  · exact batch_chunk_20 j (List.mem_range'.2 ⟨j - 20, by omega, by omega⟩)
  rcases lt_or_ge j 60 with h2 | h2
  · exact batch_chunk_40 j (List.mem_range'.2 ⟨j - 40, by omega, by omega⟩)
  rcases lt_or_ge j 80 with h3 | h3
  · exact batch_chunk_60 j (List.mem_range'.2 ⟨j - 60, by omega, by omega⟩)
  · exact batch_chunk_80 j (List.mem_range'.2 ⟨j - 80, by omega, by omega⟩)

theorem part_length_1 : trunkStateData09Part01.length = 100 := by decide +kernel

theorem part_length_2 : trunkStateData09Part02.length = 100 := by decide +kernel

theorem solution : trunkBindingBatch 9 0 100 := by
  intro i hlo hhi g hg
  change (trunkStateData09Part01 ++ trunkStateData09Part02 ++ trunkStateData09Part03)[i]? = some g at hg
  rw [List.getElem?_append_left (show i < (trunkStateData09Part01 ++ trunkStateData09Part02).length by simp only [List.length_append, part_length_1, part_length_2, Nat.reduceAdd]; omega)] at hg
  rw [List.getElem?_append_left (show i < (trunkStateData09Part01).length by simp only [List.length_append, part_length_1, part_length_2, Nat.reduceAdd]; omega)] at hg
  have hgi := batch_key (i - 0) (by omega)
  have hgv : trunkStateData09Part01.getD (i - 0) ⟨0,[],0,[]⟩ = g := by
    try simp only [Nat.sub_zero]
    rw [List.getD_eq_getElem?_getD, hg]; rfl
  rw [hgv] at hgi
  exact Freiman.trunkFast_correctness.2 9 hPar9 g (codedValid9_sound g hgi)

#print axioms solution
