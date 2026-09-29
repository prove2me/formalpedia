-- Prove2me | solution 1 for Freiman.trunk_bindings_11_000_100
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:34:03.873985+00:00
-- url     : https://prove2.me/submissions/6f7a36b6-b0b7-4272-aff4-5f46aae97d81

import Definitions.Def_Freiman_trunkFast
open Freiman Freiman.TrunkFast
set_option Elab.async false
private abbrev bc0 : ℕ × Bool × Bool := (3, false, false)
private abbrev bc1 : ℕ × Bool × Bool := (3, true, true)
private abbrev bc2 : ℕ × Bool × Bool := (30, false, false)
private abbrev bc3 : ℕ × Bool × Bool := (29, false, true)
private abbrev bc4 : ℕ × Bool × Bool := (29, true, false)
private abbrev bc5 : ℕ × Bool × Bool := (30, true, true)
private abbrev bc6 : ℕ × Bool × Bool := (147, true, true)
private abbrev bc7 : ℕ × Bool × Bool := (147, false, false)
private abbrev bc8 : ℕ × Bool × Bool := (10, false, false)
private abbrev bc9 : ℕ × Bool × Bool := (10, true, true)
private abbrev bc10 : ℕ × Bool × Bool := (4, false, false)
private abbrev bc11 : ℕ × Bool × Bool := (4, true, true)
private abbrev bc12 : ℕ × Bool × Bool := (18, false, true)
private abbrev bc13 : ℕ × Bool × Bool := (18, true, false)
private abbrev bc14 : ℕ × Bool × Bool := (6, false, false)
private abbrev bc15 : ℕ × Bool × Bool := (69, false, true)
private abbrev bc16 : ℕ × Bool × Bool := (69, true, false)
private abbrev bc17 : ℕ × Bool × Bool := (6, true, true)
private abbrev bc18 : ℕ × Bool × Bool := (83, true, true)
private abbrev bc19 : ℕ × Bool × Bool := (83, false, false)
private abbrev bc20 : ℕ × Bool × Bool := (89, false, true)
private abbrev bc21 : ℕ × Bool × Bool := (91, false, true)
private abbrev bc22 : ℕ × Bool × Bool := (91, true, false)
private abbrev bc23 : ℕ × Bool × Bool := (89, true, false)
private abbrev bc24 : ℕ × Bool × Bool := (102, true, true)
private abbrev bc25 : ℕ × Bool × Bool := (102, false, false)
private abbrev bc26 : ℕ × Bool × Bool := (30, false, true)
private abbrev bc27 : ℕ × Bool × Bool := (90, false, true)
private abbrev bc28 : ℕ × Bool × Bool := (90, true, false)
private abbrev bc29 : ℕ × Bool × Bool := (30, true, false)
private abbrev bc30 : ℕ × Bool × Bool := (95, true, true)
private abbrev bc31 : ℕ × Bool × Bool := (95, false, false)
private abbrev bc32 : ℕ × Bool × Bool := (109, false, false)
private abbrev bc33 : ℕ × Bool × Bool := (113, false, true)
private abbrev bc34 : ℕ × Bool × Bool := (113, true, false)
private abbrev bc35 : ℕ × Bool × Bool := (109, true, true)
private abbrev bc36 : ℕ × Bool × Bool := (125, true, true)
private abbrev bc37 : ℕ × Bool × Bool := (125, false, false)
private abbrev bc38 : ℕ × Bool × Bool := (132, false, true)
private abbrev bc39 : ℕ × Bool × Bool := (133, false, true)
private abbrev bc40 : ℕ × Bool × Bool := (133, true, false)
private abbrev bc41 : ℕ × Bool × Bool := (132, true, false)
private abbrev bc42 : ℕ × Bool × Bool := (136, true, true)
private abbrev bc43 : ℕ × Bool × Bool := (136, false, false)
private abbrev bc44 : ℕ × Bool × Bool := (110, false, false)
private abbrev bc45 : ℕ × Bool × Bool := (110, true, true)
private abbrev bc46 : ℕ × Bool × Bool := (156, false, false)
private abbrev bc47 : ℕ × Bool × Bool := (155, false, true)
private abbrev bc48 : ℕ × Bool × Bool := (155, true, false)
private abbrev bc49 : ℕ × Bool × Bool := (156, true, true)
private abbrev bc50 : ℕ × Bool × Bool := (162, true, true)
private abbrev bc51 : ℕ × Bool × Bool := (162, false, false)
private abbrev bc52 : ℕ × Bool × Bool := (380, false, false)
private abbrev bc53 : ℕ × Bool × Bool := (379, false, false)
private abbrev bc54 : ℕ × Bool × Bool := (377, false, true)
private abbrev bc55 : ℕ × Bool × Bool := (377, true, false)
private abbrev bc56 : ℕ × Bool × Bool := (379, true, true)
private abbrev bc57 : ℕ × Bool × Bool := (395, true, true)
private abbrev bc58 : ℕ × Bool × Bool := (395, false, false)
private abbrev bc59 : ℕ × Bool × Bool := (380, true, true)
private abbrev bc60 : ℕ × Bool × Bool := (381, false, false)
private abbrev bc61 : ℕ × Bool × Bool := (381, true, true)
private abbrev bc62 : ℕ × Bool × Bool := (384, false, false)
private abbrev bc63 : ℕ × Bool × Bool := (383, false, true)
private abbrev bc64 : ℕ × Bool × Bool := (383, true, false)
private abbrev bc65 : ℕ × Bool × Bool := (384, true, true)
private abbrev bc66 : ℕ × Bool × Bool := (388, true, true)
private abbrev bc67 : ℕ × Bool × Bool := (388, false, false)
private abbrev bc68 : ℕ × Bool × Bool := (405, false, true)
private abbrev bc69 : ℕ × Bool × Bool := (405, true, false)
private abbrev bc70 : ℕ × Bool × Bool := (415, false, true)
private abbrev bc71 : ℕ × Bool × Bool := (414, false, true)
private abbrev bc72 : ℕ × Bool × Bool := (414, true, false)
private abbrev bc73 : ℕ × Bool × Bool := (415, true, false)
private abbrev bc74 : ℕ × Bool × Bool := (421, true, true)
private abbrev bc75 : ℕ × Bool × Bool := (421, false, false)
private abbrev bc76 : ℕ × Bool × Bool := (404, false, true)
private abbrev bc77 : ℕ × Bool × Bool := (406, false, true)
private abbrev bc78 : ℕ × Bool × Bool := (403, false, true)
private abbrev bc79 : ℕ × Bool × Bool := (403, true, false)
private abbrev bc80 : ℕ × Bool × Bool := (406, true, false)
private abbrev bc81 : ℕ × Bool × Bool := (409, true, true)
private abbrev bc82 : ℕ × Bool × Bool := (409, false, false)
private abbrev bc83 : ℕ × Bool × Bool := (404, true, false)
private abbrev bc84 : ℕ × Bool × Bool := (183, false, false)
private abbrev bc85 : ℕ × Bool × Bool := (182, false, false)
private abbrev bc86 : ℕ × Bool × Bool := (179, false, true)
private abbrev bc87 : ℕ × Bool × Bool := (179, true, false)
private abbrev bc88 : ℕ × Bool × Bool := (182, true, true)
private abbrev bc89 : ℕ × Bool × Bool := (197, true, true)
private abbrev bc90 : ℕ × Bool × Bool := (197, false, false)
private abbrev bc91 : ℕ × Bool × Bool := (183, true, true)
private abbrev bc92 : ℕ × Bool × Bool := (181, false, false)
private abbrev bc93 : ℕ × Bool × Bool := (181, true, true)
private abbrev bc94 : ℕ × Bool × Bool := (184, false, false)
private abbrev bc95 : ℕ × Bool × Bool := (186, false, true)
private abbrev bc96 : ℕ × Bool × Bool := (186, true, false)
private abbrev bc97 : ℕ × Bool × Bool := (184, true, true)
private abbrev bc98 : ℕ × Bool × Bool := (189, true, true)
private abbrev bc99 : ℕ × Bool × Bool := (189, false, false)
private abbrev bc100 : ℕ × Bool × Bool := (206, true, false)
private abbrev bc101 : ℕ × Bool × Bool := (210, false, true)
private abbrev bc102 : ℕ × Bool × Bool := (210, true, false)
private abbrev bc103 : ℕ × Bool × Bool := (205, false, true)
private abbrev bc104 : ℕ × Bool × Bool := (205, true, false)
private abbrev bc105 : ℕ × Bool × Bool := (297, false, false)
private abbrev bc106 : ℕ × Bool × Bool := (298, false, false)
private abbrev bc107 : ℕ × Bool × Bool := (298, true, true)
private abbrev bc108 : ℕ × Bool × Bool := (297, true, true)
private abbrev bc109 : ℕ × Bool × Bool := (299, false, false)
private abbrev bc110 : ℕ × Bool × Bool := (299, true, true)
private abbrev bc111 : ℕ × Bool × Bool := (301, false, false)
private abbrev bc112 : ℕ × Bool × Bool := (303, false, true)
private abbrev bc113 : ℕ × Bool × Bool := (303, true, false)
private abbrev bc114 : ℕ × Bool × Bool := (301, true, true)
private abbrev bc115 : ℕ × Bool × Bool := (307, true, true)
private abbrev bc116 : ℕ × Bool × Bool := (307, false, false)
private abbrev bc117 : ℕ × Bool × Bool := (319, false, true)
private abbrev bc118 : ℕ × Bool × Bool := (319, true, false)
private abbrev bc119 : ℕ × Bool × Bool := (331, false, true)
private abbrev bc120 : ℕ × Bool × Bool := (332, false, true)
private abbrev bc121 : ℕ × Bool × Bool := (332, true, false)
private abbrev bc122 : ℕ × Bool × Bool := (331, true, false)
private abbrev bc123 : ℕ × Bool × Bool := (337, true, true)
private abbrev bc124 : ℕ × Bool × Bool := (337, false, false)
private abbrev bc125 : ℕ × Bool × Bool := (320, false, true)
private abbrev bc126 : ℕ × Bool × Bool := (322, false, true)
private abbrev bc127 : ℕ × Bool × Bool := (321, false, true)
private abbrev bc128 : ℕ × Bool × Bool := (321, true, false)
private abbrev bc129 : ℕ × Bool × Bool := (322, true, false)
private abbrev bc130 : ℕ × Bool × Bool := (325, true, true)
private abbrev bc131 : ℕ × Bool × Bool := (325, false, false)
private abbrev bc132 : ℕ × Bool × Bool := (320, true, false)
private abbrev bc133 : ℕ × Bool × Bool := (344, false, false)
private abbrev bc134 : ℕ × Bool × Bool := (343, false, false)
private abbrev bc135 : ℕ × Bool × Bool := (343, true, true)
private abbrev bc136 : ℕ × Bool × Bool := (344, true, true)
private abbrev bc137 : ℕ × Bool × Bool := (346, false, false)
private abbrev bc138 : ℕ × Bool × Bool := (346, true, true)
private abbrev bc139 : ℕ × Bool × Bool := (347, false, false)
private abbrev bc140 : ℕ × Bool × Bool := (349, false, true)
private abbrev bc141 : ℕ × Bool × Bool := (349, true, false)
private abbrev bc142 : ℕ × Bool × Bool := (347, true, true)
private abbrev bc143 : ℕ × Bool × Bool := (352, true, true)
private abbrev bc144 : ℕ × Bool × Bool := (352, false, false)
private abbrev bc145 : ℕ × Bool × Bool := (365, true, false)
private abbrev bc146 : ℕ × Bool × Bool := (369, false, true)
private abbrev bc147 : ℕ × Bool × Bool := (369, true, false)
private abbrev bc148 : ℕ × Bool × Bool := (366, false, true)
private abbrev bc149 : ℕ × Bool × Bool := (366, true, false)
private abbrev bc150 : ℕ × Bool × Bool := (432, false, false)
private abbrev bc151 : ℕ × Bool × Bool := (430, false, false)
private abbrev bc152 : ℕ × Bool × Bool := (430, true, true)
private abbrev bc153 : ℕ × Bool × Bool := (428, false, false)
private abbrev bc154 : ℕ × Bool × Bool := (428, true, true)
private abbrev bc155 : ℕ × Bool × Bool := (443, false, true)
private abbrev bc156 : ℕ × Bool × Bool := (443, true, false)
private abbrev bc157 : ℕ × Bool × Bool := (455, false, true)
private abbrev bc158 : ℕ × Bool × Bool := (456, false, true)
private abbrev bc159 : ℕ × Bool × Bool := (456, true, false)
private abbrev bc160 : ℕ × Bool × Bool := (455, true, false)
private abbrev bc161 : ℕ × Bool × Bool := (461, true, true)
private abbrev bc162 : ℕ × Bool × Bool := (461, false, false)
private abbrev bc163 : ℕ × Bool × Bool := (446, false, true)
private abbrev bc164 : ℕ × Bool × Bool := (445, false, true)
private abbrev bc165 : ℕ × Bool × Bool := (444, false, true)
private abbrev bc166 : ℕ × Bool × Bool := (444, true, false)
private abbrev bc167 : ℕ × Bool × Bool := (445, true, false)
private abbrev bc168 : ℕ × Bool × Bool := (449, true, true)
private abbrev bc169 : ℕ × Bool × Bool := (449, false, false)
private abbrev bc170 : ℕ × Bool × Bool := (446, true, false)
private abbrev bc171 : ℕ × Bool × Bool := (89, false, false)
private abbrev bc172 : ℕ × Bool × Bool := (476, false, true)
private abbrev bc173 : ℕ × Bool × Bool := (476, true, false)
private abbrev bc174 : ℕ × Bool × Bool := (89, true, true)
private abbrev bc175 : ℕ × Bool × Bool := (479, true, true)
private abbrev bc176 : ℕ × Bool × Bool := (479, false, false)
private abbrev bc177 : ℕ × Bool × Bool := (431, false, false)
private abbrev bc178 : ℕ × Bool × Bool := (490, false, true)
private abbrev bc179 : ℕ × Bool × Bool := (490, true, false)
private abbrev bc180 : ℕ × Bool × Bool := (431, true, true)
private abbrev bc181 : ℕ × Bool × Bool := (497, true, true)
private abbrev bc182 : ℕ × Bool × Bool := (497, false, false)
private abbrev bc183 : ℕ × Bool × Bool := (132, false, false)
private abbrev bc184 : ℕ × Bool × Bool := (132, true, true)
private abbrev bc185 : ℕ × Bool × Bool := (8, false, false)
private abbrev bc186 : ℕ × Bool × Bool := (5, true, true)
private abbrev bc187 : ℕ × Bool × Bool := (23, true, false)
private abbrev bc188 : ℕ × Bool × Bool := (145, true, false)
private abbrev bc189 : ℕ × Bool × Bool := (150, true, false)
private abbrev bc190 : ℕ × Bool × Bool := (88, false, true)
private abbrev bc191 : ℕ × Bool × Bool := (153, true, false)
private abbrev bc192 : ℕ × Bool × Bool := (159, true, false)
private abbrev bc193 : ℕ × Bool × Bool := (165, true, false)
private abbrev bc194 : ℕ × Bool × Bool := (378, true, true)
private abbrev bc195 : ℕ × Bool × Bool := (402, false, true)
private abbrev bc196 : ℕ × Bool × Bool := (180, true, true)
private abbrev bc197 : ℕ × Bool × Bool := (204, false, true)
private abbrev bc198 : ℕ × Bool × Bool := (300, true, true)
private abbrev bc199 : ℕ × Bool × Bool := (318, false, true)
private abbrev bc200 : ℕ × Bool × Bool := (345, true, true)
private abbrev bc201 : ℕ × Bool × Bool := (364, false, true)
private abbrev bc202 : ℕ × Bool × Bool := (429, true, true)
private abbrev bc203 : ℕ × Bool × Bool := (441, false, true)
private abbrev bc204 : ℕ × Bool × Bool := (467, true, false)
private abbrev bc205 : ℕ × Bool × Bool := (489, false, false)
private abbrev bc206 : ℕ × Bool × Bool := (7, true, false)

private def rawParent (a b : List CertBound × LowerHistoryComparison) : Option (List CertBound) :=
  let base := a.1 ++ b.1 ++ [lowerHistoryHN,lowerHistoryZero]
  match a.2,b.2 with
  | .impossible,_ | _,.impossible => none
  | .automatic,.automatic => some base
  | .bound g,.automatic | .automatic,.bound g => some (g::base)
  | .bound g,.bound h => some (g::h::base)

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
private def decodeThresholdBound (b : ℕ × Bool × Bool) : CertBound :=
  ⟨b.2.1,b.2.2,(fastBound b.1).threshold⟩
private def decodeGoalBranch (a : List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) : List CertBound × LowerHistoryComparison :=
  (a.1.map decodeThresholdBound, match a.2 with
    | none => .impossible
    | some none => .automatic
    | some (some b) => .bound (decodeThresholdBound b))
private def endpointFields11 : Array CertField := #[⟨(4/13),(1/13),(0/1),(0/1)⟩,⟨(1/2),(1/6),(0/1),(0/1)⟩,⟨(52/73),(1/73),(0/1),(0/1)⟩,⟨(89/214),(1/214),(0/1),(0/1)⟩,⟨(9/13),(-1/13),(0/1),(0/1)⟩,⟨(15/37),(-1/37),(0/1),(0/1)⟩,⟨(22/37),(1/37),(0/1),(0/1)⟩,⟨(113/179),(1/537),(0/1),(0/1)⟩,⟨(17/22),(-1/22),(0/1),(0/1)⟩,⟨(125/214),(-1/214),(0/1),(0/1)⟩,⟨(35/94),(1/94),(0/1),(0/1)⟩,⟨(553/1429),(1/1429),(0/1),(0/1)⟩,⟨(10/23),(-1/69),(0/1),(0/1)⟩,⟨(66/179),(-1/537),(0/1),(0/1)⟩,⟨(16/59),(1/177),(0/1),(0/1)⟩,⟨(767/2749),(1/2749),(0/1),(0/1)⟩,⟨(43/142),(-1/142),(0/1),(0/1)⟩,⟨(5/22),(1/22),(0/1),(0/1)⟩,⟨(42/143),(1/429),(0/1),(0/1)⟩,⟨(271/1006),(-1/1006),(0/1),(0/1)⟩,⟨(517/1249),(-1/1249),(0/1),(0/1)⟩,⟨(731/2497),(-1/2497),(0/1),(0/1)⟩,⟨(101/143),(-1/429),(0/1),(0/1)⟩,⟨(13/23),(1/69),(0/1),(0/1)⟩,⟨(732/1249),(1/1249),(0/1),(0/1)⟩,⟨(59/94),(-1/94),(0/1),(0/1)⟩]
private abbrev endpointInput11_0 : LowerPair × Bool × Bool := (([2], []), true, false)
private def endpointCodes11_0 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((0, 1), [bc0]),
 ((0, 1), [bc1, bc2, bc3]),
 ((0, 2), [bc1, bc2, bc4]),
 ((0, 1), [bc1, bc5, bc6]),
 ((3, 1), [bc1, bc5, bc7])]
private abbrev endpointInput11_1 : LowerPair × Bool × Bool := (([1], []), false, false)
private def endpointCodes11_1 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((4, 5), [bc8]), ((4, 5), [bc9])]
private abbrev endpointInput11_2 : LowerPair × Bool × Bool := (([1], []), true, false)
private def endpointCodes11_2 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((2, 1), [bc8]), ((2, 1), [bc9])]
private abbrev endpointInput11_3 : LowerPair × Bool × Bool := (([2], []), false, false)
private def endpointCodes11_3 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((5, 5), [bc0]), ((5, 5), [bc1])]
private abbrev endpointInput11_4 : LowerPair × Bool × Bool := (([1, 1], []), true, false)
private def endpointCodes11_4 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((6, 1), [bc10, (33, false, true)]),
 ((6, 2), [bc10, (33, true, false)]),
 ((6, 1), [bc11, (45, true, true)]),
 ((7, 1), [bc11, (45, false, false)])]
private abbrev endpointInput11_5 : LowerPair × Bool × Bool := (([1, 2], []), false, false)
private def endpointCodes11_5 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((8, 5), [])]
private abbrev endpointInput11_6 : LowerPair × Bool × Bool := (([1], [2]), true, true)
private def endpointCodes11_6 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((2, 0), [])]
private abbrev endpointInput11_7 : LowerPair × Bool × Bool := (([1], [1]), false, true)
private def endpointCodes11_7 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((4, 4), [bc12, (52, false, true)]),
 ((4, 9), [bc12, (52, true, false)]),
 ((4, 4), [bc13, (56, true, true)]),
 ((9, 4), [bc13, (56, false, false)])]
private abbrev endpointInput11_8 : LowerPair × Bool × Bool := (([2, 1], []), true, false)
private def endpointCodes11_8 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((10, 1), [bc14, bc15]),
 ((10, 2), [bc14, bc16]),
 ((10, 1), [bc17, bc18]),
 ((11, 1), [bc17, bc19])]
private abbrev endpointInput11_9 : LowerPair × Bool × Bool := (([2, 2], []), false, false)
private def endpointCodes11_9 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((12, 5), [])]
private abbrev endpointInput11_10 : LowerPair × Bool × Bool := (([2], [2]), true, true)
private def endpointCodes11_10 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((0, 0), [bc20, bc21]),
 ((0, 3), [bc20, bc22]),
 ((0, 0), [bc23, bc24]),
 ((3, 0), [bc23, bc25])]
private abbrev endpointInput11_11 : LowerPair × Bool × Bool := (([2], [1]), false, true)
private def endpointCodes11_11 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((5, 4), [bc26, bc27]),
 ((5, 9), [bc26, bc28]),
 ((5, 4), [bc29, bc30]),
 ((13, 4), [bc29, bc31])]
private abbrev endpointInput11_12 : LowerPair × Bool × Bool := (([3, 1], []), true, false)
private def endpointCodes11_12 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((14, 1), [bc32, bc33]),
 ((14, 2), [bc32, bc34]),
 ((14, 1), [bc35, bc36]),
 ((15, 1), [bc35, bc37])]
private abbrev endpointInput11_13 : LowerPair × Bool × Bool := (([3, 2], []), false, false)
private def endpointCodes11_13 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((16, 5), [])]
private abbrev endpointInput11_14 : LowerPair × Bool × Bool := (([3], [2]), true, true)
private def endpointCodes11_14 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((17, 0), [bc38, bc39]),
 ((17, 3), [bc38, bc40]),
 ((17, 0), [bc41, bc42]),
 ((18, 0), [bc41, bc43])]
private abbrev endpointInput11_15 : LowerPair × Bool × Bool := (([3], [1]), false, true)
private def endpointCodes11_15 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((19, 4), [])]
private abbrev endpointInput11_16 : LowerPair × Bool × Bool := (([3], []), true, false)
private def endpointCodes11_16 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((17, 1), [bc44]),
 ((17, 1), [bc45, bc46, bc47]),
 ((17, 2), [bc45, bc46, bc48]),
 ((17, 1), [bc45, bc49, bc50]),
 ((18, 1), [bc45, bc49, bc51])]
private abbrev endpointInput11_17 : LowerPair × Bool × Bool := (([2, 1], [2]), true, false)
private def endpointCodes11_17 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((10, 0), [bc52, bc53, bc54]),
 ((10, 3), [bc52, bc53, bc55]),
 ((10, 0), [bc52, bc56, bc57]),
 ((11, 0), [bc52, bc56, bc58]),
 ((10, 0), [bc59])]
private abbrev endpointInput11_18 : LowerPair × Bool × Bool := (([2, 2], [2]), false, false)
private def endpointCodes11_18 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((12, 5), [bc60]),
 ((12, 5), [bc61, bc62, bc63]),
 ((12, 13), [bc61, bc62, bc64]),
 ((12, 5), [bc61, bc65, bc66]),
 ((20, 5), [bc61, bc65, bc67])]
private abbrev endpointInput11_19 : LowerPair × Bool × Bool := (([2], [2, 1]), true, true)
private def endpointCodes11_19 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((0, 10), [bc68]),
 ((0, 10), [bc69, bc70, bc71]),
 ((0, 11), [bc69, bc70, bc72]),
 ((0, 10), [bc69, bc73, bc74]),
 ((3, 10), [bc69, bc73, bc75])]
private abbrev endpointInput11_20 : LowerPair × Bool × Bool := (([2], [2, 2]), false, true)
private def endpointCodes11_20 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((5, 12), [bc76, bc77, bc78]),
 ((5, 20), [bc76, bc77, bc79]),
 ((5, 12), [bc76, bc80, bc81]),
 ((13, 12), [bc76, bc80, bc82]),
 ((5, 12), [bc83])]
private abbrev endpointInput11_21 : LowerPair × Bool × Bool := (([3, 1], [2]), true, false)
private def endpointCodes11_21 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((14, 0), [bc84, bc85, bc86]),
 ((14, 3), [bc84, bc85, bc87]),
 ((14, 0), [bc84, bc88, bc89]),
 ((15, 0), [bc84, bc88, bc90]),
 ((14, 0), [bc91])]
private abbrev endpointInput11_22 : LowerPair × Bool × Bool := (([3, 2], [2]), false, false)
private def endpointCodes11_22 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((16, 5), [bc92]),
 ((16, 5), [bc93, bc94, bc95]),
 ((16, 13), [bc93, bc94, bc96]),
 ((16, 5), [bc93, bc97, bc98]),
 ((21, 5), [bc93, bc97, bc99])]
private abbrev endpointInput11_23 : LowerPair × Bool × Bool := (([3], [2, 1]), true, true)
private def endpointCodes11_23 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((17, 10), [(206, false, true)]),
 ((17, 10), [bc100, bc101, (208, false, true)]),
 ((17, 11), [bc100, bc101, (208, true, false)]),
 ((17, 10), [bc100, bc102, (213, true, true)]),
 ((18, 10), [bc100, bc102, (213, false, false)])]
private abbrev endpointInput11_24 : LowerPair × Bool × Bool := (([3], [2, 2]), false, true)
private def endpointCodes11_24 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((19, 12), [bc103]), ((19, 12), [bc104])]
private abbrev endpointInput11_25 : LowerPair × Bool × Bool := (([2, 1], [1]), true, false)
private def endpointCodes11_25 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((10, 1), [bc105, bc106, bc15]),
 ((10, 2), [bc105, bc106, bc16]),
 ((10, 1), [bc105, bc107, bc18]),
 ((11, 1), [bc105, bc107, bc19]),
 ((10, 1), [bc108])]
private abbrev endpointInput11_26 : LowerPair × Bool × Bool := (([2, 2], [1]), false, false)
private def endpointCodes11_26 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((12, 4), [bc109]),
 ((12, 4), [bc110, bc111, bc112]),
 ((12, 9), [bc110, bc111, bc113]),
 ((12, 4), [bc110, bc114, bc115]),
 ((20, 4), [bc110, bc114, bc116])]
private abbrev endpointInput11_27 : LowerPair × Bool × Bool := (([2], [1, 1]), true, true)
private def endpointCodes11_27 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((0, 6), [bc117]),
 ((0, 6), [bc118, bc119, bc120]),
 ((0, 7), [bc118, bc119, bc121]),
 ((0, 6), [bc118, bc122, bc123]),
 ((3, 6), [bc118, bc122, bc124])]
private abbrev endpointInput11_28 : LowerPair × Bool × Bool := (([2], [1, 2]), false, true)
private def endpointCodes11_28 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((5, 8), [bc125, bc126, bc127]),
 ((5, 22), [bc125, bc126, bc128]),
 ((5, 8), [bc125, bc129, bc130]),
 ((13, 8), [bc125, bc129, bc131]),
 ((5, 8), [bc132])]
private abbrev endpointInput11_29 : LowerPair × Bool × Bool := (([3, 1], [1]), true, false)
private def endpointCodes11_29 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((14, 1), [bc133, bc134, bc33]),
 ((14, 2), [bc133, bc134, bc34]),
 ((14, 1), [bc133, bc135, bc36]),
 ((15, 1), [bc133, bc135, bc37]),
 ((14, 1), [bc136])]
private abbrev endpointInput11_30 : LowerPair × Bool × Bool := (([3, 2], [1]), false, false)
private def endpointCodes11_30 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((16, 4), [bc137]),
 ((16, 4), [bc138, bc139, bc140]),
 ((16, 9), [bc138, bc139, bc141]),
 ((16, 4), [bc138, bc142, bc143]),
 ((21, 4), [bc138, bc142, bc144])]
private abbrev endpointInput11_31 : LowerPair × Bool × Bool := (([3], [1, 1]), true, true)
private def endpointCodes11_31 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((17, 6), [(365, false, true)]),
 ((17, 6), [bc145, bc146, (370, false, true)]),
 ((17, 7), [bc145, bc146, (370, true, false)]),
 ((17, 6), [bc145, bc147, (373, true, true)]),
 ((18, 6), [bc145, bc147, (373, false, false)])]
private abbrev endpointInput11_32 : LowerPair × Bool × Bool := (([3], [1, 2]), false, true)
private def endpointCodes11_32 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((19, 8), [bc148]), ((19, 8), [bc149])]
private abbrev endpointInput11_33 : LowerPair × Bool × Bool := (([2, 1], [3]), true, false)
private def endpointCodes11_33 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((10, 17), [bc150, bc151, (427, false, true)]),
 ((10, 18), [bc150, bc151, (427, true, false)]),
 ((10, 17), [bc150, bc152, (436, true, true)]),
 ((11, 17), [bc150, bc152, (436, false, false)]),
 ((10, 17), [(432, true, true)])]
private abbrev endpointInput11_34 : LowerPair × Bool × Bool := (([2, 2], [3]), false, false)
private def endpointCodes11_34 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((12, 19), [bc153]), ((12, 19), [bc154])]
private abbrev endpointInput11_35 : LowerPair × Bool × Bool := (([2], [3, 1]), true, true)
private def endpointCodes11_35 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((0, 14), [bc155]),
 ((0, 14), [bc156, bc157, bc158]),
 ((0, 15), [bc156, bc157, bc159]),
 ((0, 14), [bc156, bc160, bc161]),
 ((3, 14), [bc156, bc160, bc162])]
private abbrev endpointInput11_36 : LowerPair × Bool × Bool := (([2], [3, 2]), false, true)
private def endpointCodes11_36 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((5, 16), [bc163, bc164, bc165]),
 ((5, 21), [bc163, bc164, bc166]),
 ((5, 16), [bc163, bc167, bc168]),
 ((13, 16), [bc163, bc167, bc169]),
 ((5, 16), [bc170])]
private abbrev endpointInput11_37 : LowerPair × Bool × Bool := (([2], [1]), true, false)
private def endpointCodes11_37 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((0, 1), [bc2, bc3]),
 ((0, 2), [bc2, bc4]),
 ((0, 1), [bc5, bc6]),
 ((3, 1), [bc5, bc7])]
private abbrev endpointInput11_38 : LowerPair × Bool × Bool := (([3], [1]), true, false)
private def endpointCodes11_38 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((17, 1), [bc46, bc47]),
 ((17, 2), [bc46, bc48]),
 ((17, 1), [bc49, bc50]),
 ((18, 1), [bc49, bc51])]
private abbrev endpointInput11_39 : LowerPair × Bool × Bool := (([2], [1]), false, false)
private def endpointCodes11_39 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((5, 4), [bc2, bc27]),
 ((5, 9), [bc2, bc28]),
 ((5, 4), [bc5, bc30]),
 ((13, 4), [bc5, bc31])]
private abbrev endpointInput11_40 : LowerPair × Bool × Bool := (([2], [2]), false, false)
private def endpointCodes11_40 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((5, 5), [bc171, bc172]),
 ((5, 13), [bc171, bc173]),
 ((5, 5), [bc174, bc175]),
 ((13, 5), [bc174, bc176])]
private abbrev endpointInput11_41 : LowerPair × Bool × Bool := (([2], [2]), true, false)
private def endpointCodes11_41 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((0, 0), [bc171, bc21]),
 ((0, 3), [bc171, bc22]),
 ((0, 0), [bc174, bc24]),
 ((3, 0), [bc174, bc25])]
private abbrev endpointInput11_42 : LowerPair × Bool × Bool := (([3], [1]), false, false)
private def endpointCodes11_42 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((19, 4), [])]
private abbrev endpointInput11_43 : LowerPair × Bool × Bool := (([2], [3]), true, false)
private def endpointCodes11_43 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((0, 17), [bc177, bc178]),
 ((0, 18), [bc177, bc179]),
 ((0, 17), [bc180, bc181]),
 ((3, 17), [bc180, bc182])]
private abbrev endpointInput11_44 : LowerPair × Bool × Bool := (([3], [2]), false, false)
private def endpointCodes11_44 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((19, 5), [])]
private abbrev endpointInput11_45 : LowerPair × Bool × Bool := (([3], [2]), true, false)
private def endpointCodes11_45 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((17, 0), [bc183, bc39]),
 ((17, 3), [bc183, bc40]),
 ((17, 0), [bc184, bc42]),
 ((18, 0), [bc184, bc43])]
private abbrev endpointInput11_46 : LowerPair × Bool × Bool := (([2], [3]), false, false)
private def endpointCodes11_46 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((5, 19), [])]

private def decodeEndpoint11 (x : (ℕ × ℕ) × List (ℕ × Bool × Bool)) : LowerHistoryEndCase :=
  ((endpointFields11[x.1.1]?.getD ⟨0,0,0,0⟩,endpointFields11[x.1.2]?.getD ⟨0,0,0,0⟩),x.2.map decodeThresholdBound)

private theorem hEndpoint11_0 :
    trunkEndpointCases (trunkCatalog.states 11).context endpointInput11_0.1 endpointInput11_0.2.1 endpointInput11_0.2.2 = endpointCodes11_0.map decodeEndpoint11 := by decide +kernel

private theorem hEndpoint11_1 :
    trunkEndpointCases (trunkCatalog.states 11).context endpointInput11_1.1 endpointInput11_1.2.1 endpointInput11_1.2.2 = endpointCodes11_1.map decodeEndpoint11 := by decide +kernel

private theorem hEndpoint11_2 :
    trunkEndpointCases (trunkCatalog.states 11).context endpointInput11_2.1 endpointInput11_2.2.1 endpointInput11_2.2.2 = endpointCodes11_2.map decodeEndpoint11 := by decide +kernel

private theorem hEndpoint11_3 :
    trunkEndpointCases (trunkCatalog.states 11).context endpointInput11_3.1 endpointInput11_3.2.1 endpointInput11_3.2.2 = endpointCodes11_3.map decodeEndpoint11 := by decide +kernel

private theorem hEndpoint11_4 :
    trunkEndpointCases (trunkCatalog.states 11).context endpointInput11_4.1 endpointInput11_4.2.1 endpointInput11_4.2.2 = endpointCodes11_4.map decodeEndpoint11 := by decide +kernel

private theorem hEndpoint11_5 :
    trunkEndpointCases (trunkCatalog.states 11).context endpointInput11_5.1 endpointInput11_5.2.1 endpointInput11_5.2.2 = endpointCodes11_5.map decodeEndpoint11 := by decide +kernel

private theorem hEndpoint11_6 :
    trunkEndpointCases (trunkCatalog.states 11).context endpointInput11_6.1 endpointInput11_6.2.1 endpointInput11_6.2.2 = endpointCodes11_6.map decodeEndpoint11 := by decide +kernel

private theorem hEndpoint11_7 :
    trunkEndpointCases (trunkCatalog.states 11).context endpointInput11_7.1 endpointInput11_7.2.1 endpointInput11_7.2.2 = endpointCodes11_7.map decodeEndpoint11 := by decide +kernel

private theorem hEndpoint11_8 :
    trunkEndpointCases (trunkCatalog.states 11).context endpointInput11_8.1 endpointInput11_8.2.1 endpointInput11_8.2.2 = endpointCodes11_8.map decodeEndpoint11 := by decide +kernel

private theorem hEndpoint11_9 :
    trunkEndpointCases (trunkCatalog.states 11).context endpointInput11_9.1 endpointInput11_9.2.1 endpointInput11_9.2.2 = endpointCodes11_9.map decodeEndpoint11 := by decide +kernel

private theorem hEndpoint11_10 :
    trunkEndpointCases (trunkCatalog.states 11).context endpointInput11_10.1 endpointInput11_10.2.1 endpointInput11_10.2.2 = endpointCodes11_10.map decodeEndpoint11 := by decide +kernel

private theorem hEndpoint11_11 :
    trunkEndpointCases (trunkCatalog.states 11).context endpointInput11_11.1 endpointInput11_11.2.1 endpointInput11_11.2.2 = endpointCodes11_11.map decodeEndpoint11 := by decide +kernel

private theorem hEndpoint11_12 :
    trunkEndpointCases (trunkCatalog.states 11).context endpointInput11_12.1 endpointInput11_12.2.1 endpointInput11_12.2.2 = endpointCodes11_12.map decodeEndpoint11 := by decide +kernel

private theorem hEndpoint11_13 :
    trunkEndpointCases (trunkCatalog.states 11).context endpointInput11_13.1 endpointInput11_13.2.1 endpointInput11_13.2.2 = endpointCodes11_13.map decodeEndpoint11 := by decide +kernel

private theorem hEndpoint11_14 :
    trunkEndpointCases (trunkCatalog.states 11).context endpointInput11_14.1 endpointInput11_14.2.1 endpointInput11_14.2.2 = endpointCodes11_14.map decodeEndpoint11 := by decide +kernel

private theorem hEndpoint11_15 :
    trunkEndpointCases (trunkCatalog.states 11).context endpointInput11_15.1 endpointInput11_15.2.1 endpointInput11_15.2.2 = endpointCodes11_15.map decodeEndpoint11 := by decide +kernel

private theorem hEndpoint11_16 :
    trunkEndpointCases (trunkCatalog.states 11).context endpointInput11_16.1 endpointInput11_16.2.1 endpointInput11_16.2.2 = endpointCodes11_16.map decodeEndpoint11 := by decide +kernel

private theorem hEndpoint11_17 :
    trunkEndpointCases (trunkCatalog.states 11).context endpointInput11_17.1 endpointInput11_17.2.1 endpointInput11_17.2.2 = endpointCodes11_17.map decodeEndpoint11 := by decide +kernel

private theorem hEndpoint11_18 :
    trunkEndpointCases (trunkCatalog.states 11).context endpointInput11_18.1 endpointInput11_18.2.1 endpointInput11_18.2.2 = endpointCodes11_18.map decodeEndpoint11 := by decide +kernel

private theorem hEndpoint11_19 :
    trunkEndpointCases (trunkCatalog.states 11).context endpointInput11_19.1 endpointInput11_19.2.1 endpointInput11_19.2.2 = endpointCodes11_19.map decodeEndpoint11 := by decide +kernel

private theorem hEndpoint11_20 :
    trunkEndpointCases (trunkCatalog.states 11).context endpointInput11_20.1 endpointInput11_20.2.1 endpointInput11_20.2.2 = endpointCodes11_20.map decodeEndpoint11 := by decide +kernel

private theorem hEndpoint11_21 :
    trunkEndpointCases (trunkCatalog.states 11).context endpointInput11_21.1 endpointInput11_21.2.1 endpointInput11_21.2.2 = endpointCodes11_21.map decodeEndpoint11 := by decide +kernel

private theorem hEndpoint11_22 :
    trunkEndpointCases (trunkCatalog.states 11).context endpointInput11_22.1 endpointInput11_22.2.1 endpointInput11_22.2.2 = endpointCodes11_22.map decodeEndpoint11 := by decide +kernel

private theorem hEndpoint11_23 :
    trunkEndpointCases (trunkCatalog.states 11).context endpointInput11_23.1 endpointInput11_23.2.1 endpointInput11_23.2.2 = endpointCodes11_23.map decodeEndpoint11 := by decide +kernel

private theorem hEndpoint11_24 :
    trunkEndpointCases (trunkCatalog.states 11).context endpointInput11_24.1 endpointInput11_24.2.1 endpointInput11_24.2.2 = endpointCodes11_24.map decodeEndpoint11 := by decide +kernel

private theorem hEndpoint11_25 :
    trunkEndpointCases (trunkCatalog.states 11).context endpointInput11_25.1 endpointInput11_25.2.1 endpointInput11_25.2.2 = endpointCodes11_25.map decodeEndpoint11 := by decide +kernel

private theorem hEndpoint11_26 :
    trunkEndpointCases (trunkCatalog.states 11).context endpointInput11_26.1 endpointInput11_26.2.1 endpointInput11_26.2.2 = endpointCodes11_26.map decodeEndpoint11 := by decide +kernel

private theorem hEndpoint11_27 :
    trunkEndpointCases (trunkCatalog.states 11).context endpointInput11_27.1 endpointInput11_27.2.1 endpointInput11_27.2.2 = endpointCodes11_27.map decodeEndpoint11 := by decide +kernel

private theorem hEndpoint11_28 :
    trunkEndpointCases (trunkCatalog.states 11).context endpointInput11_28.1 endpointInput11_28.2.1 endpointInput11_28.2.2 = endpointCodes11_28.map decodeEndpoint11 := by decide +kernel

private theorem hEndpoint11_29 :
    trunkEndpointCases (trunkCatalog.states 11).context endpointInput11_29.1 endpointInput11_29.2.1 endpointInput11_29.2.2 = endpointCodes11_29.map decodeEndpoint11 := by decide +kernel

private theorem hEndpoint11_30 :
    trunkEndpointCases (trunkCatalog.states 11).context endpointInput11_30.1 endpointInput11_30.2.1 endpointInput11_30.2.2 = endpointCodes11_30.map decodeEndpoint11 := by decide +kernel

private theorem hEndpoint11_31 :
    trunkEndpointCases (trunkCatalog.states 11).context endpointInput11_31.1 endpointInput11_31.2.1 endpointInput11_31.2.2 = endpointCodes11_31.map decodeEndpoint11 := by decide +kernel

private theorem hEndpoint11_32 :
    trunkEndpointCases (trunkCatalog.states 11).context endpointInput11_32.1 endpointInput11_32.2.1 endpointInput11_32.2.2 = endpointCodes11_32.map decodeEndpoint11 := by decide +kernel

private theorem hEndpoint11_33 :
    trunkEndpointCases (trunkCatalog.states 11).context endpointInput11_33.1 endpointInput11_33.2.1 endpointInput11_33.2.2 = endpointCodes11_33.map decodeEndpoint11 := by decide +kernel

private theorem hEndpoint11_34 :
    trunkEndpointCases (trunkCatalog.states 11).context endpointInput11_34.1 endpointInput11_34.2.1 endpointInput11_34.2.2 = endpointCodes11_34.map decodeEndpoint11 := by decide +kernel

private theorem hEndpoint11_35 :
    trunkEndpointCases (trunkCatalog.states 11).context endpointInput11_35.1 endpointInput11_35.2.1 endpointInput11_35.2.2 = endpointCodes11_35.map decodeEndpoint11 := by decide +kernel

private theorem hEndpoint11_36 :
    trunkEndpointCases (trunkCatalog.states 11).context endpointInput11_36.1 endpointInput11_36.2.1 endpointInput11_36.2.2 = endpointCodes11_36.map decodeEndpoint11 := by decide +kernel

private theorem hEndpoint11_37 :
    trunkEndpointCases (trunkCatalog.states 11).context endpointInput11_37.1 endpointInput11_37.2.1 endpointInput11_37.2.2 = endpointCodes11_37.map decodeEndpoint11 := by decide +kernel

private theorem hEndpoint11_38 :
    trunkEndpointCases (trunkCatalog.states 11).context endpointInput11_38.1 endpointInput11_38.2.1 endpointInput11_38.2.2 = endpointCodes11_38.map decodeEndpoint11 := by decide +kernel

private theorem hEndpoint11_39 :
    trunkEndpointCases (trunkCatalog.states 11).context endpointInput11_39.1 endpointInput11_39.2.1 endpointInput11_39.2.2 = endpointCodes11_39.map decodeEndpoint11 := by decide +kernel

private theorem hEndpoint11_40 :
    trunkEndpointCases (trunkCatalog.states 11).context endpointInput11_40.1 endpointInput11_40.2.1 endpointInput11_40.2.2 = endpointCodes11_40.map decodeEndpoint11 := by decide +kernel

private theorem hEndpoint11_41 :
    trunkEndpointCases (trunkCatalog.states 11).context endpointInput11_41.1 endpointInput11_41.2.1 endpointInput11_41.2.2 = endpointCodes11_41.map decodeEndpoint11 := by decide +kernel

private theorem hEndpoint11_42 :
    trunkEndpointCases (trunkCatalog.states 11).context endpointInput11_42.1 endpointInput11_42.2.1 endpointInput11_42.2.2 = endpointCodes11_42.map decodeEndpoint11 := by decide +kernel

private theorem hEndpoint11_43 :
    trunkEndpointCases (trunkCatalog.states 11).context endpointInput11_43.1 endpointInput11_43.2.1 endpointInput11_43.2.2 = endpointCodes11_43.map decodeEndpoint11 := by decide +kernel

private theorem hEndpoint11_44 :
    trunkEndpointCases (trunkCatalog.states 11).context endpointInput11_44.1 endpointInput11_44.2.1 endpointInput11_44.2.2 = endpointCodes11_44.map decodeEndpoint11 := by decide +kernel

private theorem hEndpoint11_45 :
    trunkEndpointCases (trunkCatalog.states 11).context endpointInput11_45.1 endpointInput11_45.2.1 endpointInput11_45.2.2 = endpointCodes11_45.map decodeEndpoint11 := by decide +kernel

private theorem hEndpoint11_46 :
    trunkEndpointCases (trunkCatalog.states 11).context endpointInput11_46.1 endpointInput11_46.2.1 endpointInput11_46.2.2 = endpointCodes11_46.map decodeEndpoint11 := by decide +kernel

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

private def classValidIds : List ℕ := [23, 3, 15, 16, 10, 33, 43, 36, 48, 88, 29, 92, 94, 98, 102, 103, 113, 122, 114, 128, 130, 134, 136, 137, 141, 144, 30, 110, 153, 159, 162, 165, 171, 90, 7, 145, 147, 551, 177, 149, 178, 377, 388, 387, 379, 381, 378, 385, 390, 397, 401, 402, 407, 411, 413, 417, 421, 422, 179, 182, 181, 180, 187, 191, 200, 204, 207, 211, 213, 214, 65, 67, 56, 68, 97, 96, 174, 150, 295, 52, 296, 318, 321, 323, 327, 329, 333, 337, 338, 343, 346, 345, 350, 354, 127, 364, 365, 367, 371, 373, 374, 427, 430, 428, 429, 438, 441, 447, 451, 453, 457, 461, 462, 155, 156, 467, 469, 163, 477, 479, 482, 483, 481, 484, 485, 486, 91, 487, 488, 489, 476, 491, 89, 492, 493, 497, 442, 502, 503, 504, 505, 506, 507, 508]
private theorem thresholdClass_key : ∀ i ∈ classValidIds,
    i = thresholdClass i ∨ (fastBound i).threshold = (fastBound (thresholdClass i)).threshold := by decide +kernel
private theorem threshold_class_of_range (i : ℕ) (hi : i ∈ classValidIds) :
    (fastBound i).threshold = (fastBound (thresholdClass i)).threshold := by
  rcases thresholdClass_key i hi with he | he
  · rw [← he]
  · exact he
private theorem foldl_append_getElem? {α : Type} :
    ∀ (arrs : List (Array α)) (init : Array α) (i : ℕ),
      (arrs.foldl (·++·) init)[i]? =
        if i < init.size then init[i]? else chainGet? arrs (i - init.size)
  | [], init, i => by
      by_cases h : i < init.size
      · simp [h]
      · simp [h, chainGet?]
  | A::As, init, i => by
      rw [List.foldl_cons, foldl_append_getElem? As (init++A) i, Array.size_append]
      by_cases h1 : i < init.size
      · rw [if_pos h1, if_pos (by omega : i < init.size + A.size),
          Array.getElem?_append_left h1]
      · rw [if_neg h1]
        rw [show chainGet? (A::As) (i-init.size) =
              if i - init.size < A.size then A[i-init.size]? else chainGet? As (i - init.size - A.size)
            from rfl]
        by_cases h2 : i < init.size + A.size
        · rw [if_pos h2, Array.getElem?_append_right (by omega),
            if_pos (by omega : i - init.size < A.size)]
        · rw [if_neg h2, if_neg (show ¬ i - init.size < A.size by omega),
            show i - (init.size + A.size) = i - init.size - A.size by omega]

private theorem foldl_append_size {α : Type} :
    ∀ (arrs : List (Array α)) (init : Array α),
      (arrs.foldl (·++·) init).size = arrs.foldl (fun n A => n + A.size) init.size
  | [], init => rfl
  | A::As, init => by
      rw [List.foldl_cons, foldl_append_size As (init++A), Array.size_append, List.foldl_cons]

private theorem trunkDataWitnesses_eq_foldl :
    trunkDataWitnesses = List.foldl (·++·) trunkWitnessData01
      [trunkWitnessData02,trunkWitnessData03,trunkWitnessData04,trunkWitnessData05,trunkWitnessData06,
       trunkWitnessData07,trunkWitnessData08,trunkWitnessData09,trunkWitnessData10,trunkWitnessData11,
       trunkWitnessData12,trunkWitnessData13,trunkWitnessData14,trunkWitnessData15,trunkWitnessData16,
       trunkWitnessData17,trunkWitnessData18,trunkWitnessData19,trunkWitnessData20,trunkWitnessData21,
       trunkWitnessData22,trunkWitnessData23,trunkWitnessData24,trunkWitnessData25,trunkWitnessData26,
       trunkWitnessData27,trunkWitnessData28,trunkWitnessData29,trunkWitnessData30,trunkWitnessData31,
       trunkWitnessData32,trunkWitnessData33,trunkWitnessData34,trunkWitnessData35] := rfl

private theorem trunkWitnesses_size : trunkCatalog.witnesses.size = 8656 := by
  rw [show trunkCatalog.witnesses = trunkDataWitnesses from rfl,
    trunkDataWitnesses_eq_foldl, foldl_append_size]
  decide +kernel

private theorem witness_eq? (n : ℕ) : trunkDataWitnesses[n-1]? = fastWitness? n := by
  rw [trunkDataWitnesses_eq_foldl, foldl_append_getElem?]; rfl

private theorem witness_eq (n : ℕ) : trunkWitness trunkCatalog n = fastWitness n := by
  unfold trunkWitness fastWitness
  rw [show trunkCatalog.witnesses = trunkDataWitnesses from rfl, witness_eq?]

private theorem trunkDataBounds_eq_foldl :
    trunkDataBounds = List.foldl (·++·) trunkBoundData01
      [trunkBoundData02,trunkBoundData03,trunkBoundData04] := rfl

private theorem bound_eq? (n : ℕ) : trunkDataBounds[n-1]? = fastBound? n := by
  rw [trunkDataBounds_eq_foldl, foldl_append_getElem?]; rfl

private theorem bound_eq (n : ℕ) : trunkBound trunkCatalog n = fastBound n := by
  unfold trunkBound fastBound
  rw [show trunkCatalog.bounds = trunkDataBounds from rfl, bound_eq?]

/-! ## Mirror predicates: same shape as trunkLeafBound/trunkTreeBound, but
built directly from fastWitness/fastBound/literal sizes, hence PLAINLY
decidable (no rewriting needed at decide-time). Soundness (Fast -> real) is
proved ONCE, ordinarily (not inside a reusable Decidable instance), so
`decide +kernel` on the Fast predicate never has to reduce the
witness_eq/bound_eq/foldl-induction proofs. -/

private theorem trunkUseBoundsFast_iff (w : TrunkWitness) (l u : CertBound) :
    trunkUseBoundsFast w l u ↔ trunkUseBounds trunkCatalog w l u := by
  unfold trunkUseBoundsFast trunkUseBounds
  rw [bound_eq, bound_eq]

private theorem trunkLeafBoundFast_iff (R : CertRectangle) (bs : List CertBound) (id : ℕ) (sign : ℤ) :
    trunkLeafBoundFast R bs id sign ↔ trunkLeafBound trunkCatalog R bs id sign := by
  unfold trunkLeafBoundFast trunkLeafBound
  rw [← witness_eq, ← trunkWitnesses_size]
  constructor
  · rintro ⟨h1,h2,h3,h4,l,hl,u,hu,h5⟩
    exact ⟨h1,h2,h3,h4,l,hl,u,hu,(trunkUseBoundsFast_iff _ l u).1 h5⟩
  · rintro ⟨h1,h2,h3,h4,l,hl,u,hu,h5⟩
    exact ⟨h1,h2,h3,h4,l,hl,u,hu,(trunkUseBoundsFast_iff _ l u).2 h5⟩

private theorem trunkTreeBoundFast_iff (R : CertRectangle) (bs : List CertBound) :
    ∀ t, trunkTreeBoundFast R bs t ↔ trunkTreeBound trunkCatalog R bs t
  | .pair id => trunkLeafBoundFast_iff R bs id 0
  | .split axis left right => by
      unfold trunkTreeBoundFast trunkTreeBound
      rw [trunkTreeBoundFast_iff (trunkRectangleHalf R axis false) bs left,
          trunkTreeBoundFast_iff (trunkRectangleHalf R axis true) bs right]
  | .diagonal negative positive => by
      unfold trunkTreeBoundFast trunkTreeBound
      rw [trunkLeafBoundFast_iff R bs negative (-1), trunkLeafBoundFast_iff R bs positive 1]
  | .boundary => by unfold trunkTreeBoundFast trunkTreeBound; rfl

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
private def codeResidual (parents : List (List (ℕ × Bool × Bool))) (cuts : List (ℕ × Bool × Bool))
    (goals : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))))
    (parent : ℕ) (branch : ℤ) : List (ℕ × Bool × Bool) :=
  let b := goals[branch.toNat]?.getD ([],none)
  cuts ++ parents[parent]?.getD [] ++ b.1 ++
    match b.2 with | some (some a) => [codeComplement a] | _ => []
private theorem codedBranch_eq (S : TrunkState) (pi goal : ℕ) (branch : ℤ)
    (codes : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))))
    (he : trunkGoalBranches S pi goal = codes.map decodeGoalBranch) :
    trunkBranch S pi goal branch = decodeGoalBranch (codes[branch.toNat]?.getD ([],none)) := by
  unfold trunkBranch
  rw [he,List.getElem?_map]
  exact Option.getD_map decodeGoalBranch ([],none) codes[branch.toNat]?
private theorem codedParent_eq (codes : List (List (ℕ × Bool × Bool))) (i : ℕ) :
    (codes.map (List.map decodeThresholdBound))[i]?.getD [] =
      (codes[i]?.getD []).map decodeThresholdBound := by
  rw [List.getElem?_map]
  exact Option.getD_map (List.map decodeThresholdBound) [] codes[i]?
private theorem codeResidual_eq (S : TrunkState) (pi parent goal : ℕ) (branch : ℤ)
    (parents : List (List (ℕ × Bool × Bool))) (cuts : List (ℕ × Bool × Bool))
    (goals : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))))
    (hpar : trunkParents S.context = parents.map (List.map decodeThresholdBound))
    (hcut : (trunkPlanAt S pi).cuts = cuts.map decodeThresholdBound)
    (hgoal : trunkGoalBranches S pi goal = goals.map decodeGoalBranch) :
    trunkResidual S pi parent goal branch = (codeResidual parents cuts goals parent branch).map decodeThresholdBound := by
  unfold trunkResidual trunkBaseConditions codeResidual
  rw [hcut,hpar,codedParent_eq,codedBranch_eq S pi goal branch goals hgoal]
  generalize goals[branch.toNat]?.getD ([],none) = b
  rcases b with ⟨bs,cmp⟩
  cases cmp with
  | none => simp [decodeGoalBranch,List.map_append]
  | some cmp =>
    cases cmp <;> simp [decodeGoalBranch,List.map_append,decodeComplement]
private def codeGroupValid (S : TrunkState) (parents : List (List (ℕ × Bool × Bool)))
    (cuts : ℕ → List (ℕ × Bool × Bool))
    (goals : ℕ → ℕ → List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))))
    (g : TrunkGroup) : Prop :=
  g.plan < (trunkSourcePlans S.context).length ∧ g.goal ≤ (trunkSpecs (trunkPlanAt S g.plan)).length ∧
  (∀ p ∈ g.parents, p < parents.length) ∧
  ∀ bt ∈ g.branches,
    ((g.goal = 0 ∧ bt.1 = -1) ∨ (0 < g.goal ∧ 0 ≤ bt.1 ∧ bt.1.toNat < (goals g.plan g.goal).length)) ∧
    ((goals g.plan g.goal)[bt.1.toNat]?.getD ([],none)).2 ≠ some none ∧
    ∀ p ∈ g.parents, codeTreeBound S.rectangle (codeResidual parents (cuts g.plan) (goals g.plan g.goal) p bt.1) bt.2
private theorem codeGroupValid_sound (k : Fin 16) (parents : List (List (ℕ × Bool × Bool)))
    (cuts : ℕ → List (ℕ × Bool × Bool))
    (goals : ℕ → ℕ → List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))))
    (g : TrunkGroup)
    (hpar : trunkParents (trunkCatalog.states k).context = parents.map (List.map decodeThresholdBound))
    (hcut : (trunkPlanAt (trunkCatalog.states k) g.plan).cuts = (cuts g.plan).map decodeThresholdBound)
    (hgoal : trunkGoalBranches (trunkCatalog.states k) g.plan g.goal = (goals g.plan g.goal).map decodeGoalBranch)
    (h : codeGroupValid (trunkCatalog.states k) parents cuts goals g) : trunkGroupValid trunkCatalog k g := by
  rcases h with ⟨hp,hg,hparents,hb⟩
  refine ⟨hp,hg,?_,?_⟩
  · simpa only [hpar,List.length_map] using hparents
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
      exact (trunkTreeBoundFast_iff _ _ _).1 (codeTreeBound_sound _ _ _ (ht p hpg))
private def codeHN : ℕ × Bool × Bool := bc185
private def codeZero : ℕ × Bool × Bool := bc186

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
private def thresholdParentA11 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc0, bc8], some (some bc187)),
 ([bc0, bc9], some (some bc187)),
 ([bc1, bc2, bc3, bc8], some (some bc187)),
 ([bc1, bc2, bc3, bc9], some (some bc187)),
 ([bc1, bc2, bc4, bc8], some (some bc188)),
 ([bc1, bc2, bc4, bc9], some (some bc188)),
 ([bc1, bc5, bc6, bc8], some (some bc187)),
 ([bc1, bc5, bc6, bc9], some (some bc187)),
 ([bc1, bc5, bc7, bc8], some (some bc189)),
 ([bc1, bc5, bc7, bc9], some (some bc189))]
private def thresholdParentB11 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc8, bc0], some none),
 ([bc8, bc1], some none),
 ([bc9, bc0], some none),
 ([bc9, bc1], some none)]
private def codedParents11 : List (List (ℕ × Bool × Bool)) := [[bc187, bc0, bc8, bc8, bc0, bc185, bc186], [bc187, bc0, bc8, bc8, bc1, bc185, bc186], [bc187, bc0, bc8, bc9, bc0, bc185, bc186], [bc187, bc0, bc8, bc9, bc1, bc185, bc186], [bc187, bc0, bc9, bc9, bc0, bc185, bc186], [bc187, bc0, bc9, bc9, bc1, bc185, bc186], [bc187, bc1, bc2, bc3, bc8, bc8, bc0, bc185, bc186], [bc187, bc1, bc2, bc3, bc8, bc8, bc1, bc185, bc186], [bc187, bc1, bc2, bc3, bc8, bc9, bc0, bc185, bc186], [bc187, bc1, bc2, bc3, bc8, bc9, bc1, bc185, bc186], [bc187, bc1, bc2, bc3, bc9, bc9, bc0, bc185, bc186], [bc187, bc1, bc2, bc3, bc9, bc9, bc1, bc185, bc186], [bc188, bc1, bc2, bc4, bc8, bc8, bc0, bc185, bc186], [bc188, bc1, bc2, bc4, bc8, bc8, bc1, bc185, bc186], [bc188, bc1, bc2, bc4, bc8, bc9, bc0, bc185, bc186], [bc188, bc1, bc2, bc4, bc8, bc9, bc1, bc185, bc186], [bc188, bc1, bc2, bc4, bc9, bc9, bc0, bc185, bc186], [bc188, bc1, bc2, bc4, bc9, bc9, bc1, bc185, bc186], [bc187, bc1, bc5, bc6, bc8, bc8, bc0, bc185, bc186], [bc187, bc1, bc5, bc6, bc8, bc8, bc1, bc185, bc186], [bc187, bc1, bc5, bc6, bc8, bc9, bc0, bc185, bc186], [bc187, bc1, bc5, bc6, bc8, bc9, bc1, bc185, bc186], [bc187, bc1, bc5, bc6, bc9, bc9, bc0, bc185, bc186], [bc187, bc1, bc5, bc6, bc9, bc9, bc1, bc185, bc186], [bc189, bc1, bc5, bc7, bc8, bc8, bc0, bc185, bc186], [bc189, bc1, bc5, bc7, bc8, bc8, bc1, bc185, bc186], [bc189, bc1, bc5, bc7, bc8, bc9, bc0, bc185, bc186], [bc189, bc1, bc5, bc7, bc8, bc9, bc1, bc185, bc186], [bc189, bc1, bc5, bc7, bc9, bc9, bc0, bc185, bc186], [bc189, bc1, bc5, bc7, bc9, bc9, bc1, bc185, bc186]]

private theorem hThresholdParentA11 : trunkBranches (trunkCatalog.states 11).context ⟨([2],[]),true,([1],[]),false,false,[]⟩ = thresholdParentA11.map decodeGoalBranch := by decide +kernel
private theorem hThresholdParentB11 : trunkBranches (trunkCatalog.states 11).context ⟨([1],[]),true,([2],[]),false,false,[]⟩ = thresholdParentB11.map decodeGoalBranch := by decide +kernel
private theorem hCodedParents11 : trunkParents (trunkCatalog.states 11).context = codedParents11.map (List.map decodeThresholdBound) := by
  unfold trunkParents
  rw [hThresholdParentA11,hThresholdParentB11]
  decide +kernel


private def goalCodes11_0_0 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([], none)]
private def goalCodes11_0_2 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc8, bc10, (33, false, true)], some (some (36, true, true))),
 ([bc8, bc10, (33, true, false)], some (some (43, true, true))),
 ([bc8, bc11, (45, true, true)], some (some (36, true, true))),
 ([bc8, bc11, (45, false, false)], some (some (48, true, true)))]
private def goalCodes11_0_5 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc9, bc12, (52, false, true)], some (some (65, false, true))),
 ([bc9, bc12, (52, true, false)], some (some (67, false, true))),
 ([bc9, bc13, (56, true, true)], some (some (65, false, true))),
 ([bc9, bc13, (56, false, false)], some (some (68, false, true)))]
private def goalCodes11_0_7 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc0, bc14, bc15], some (some (73, true, true))),
 ([bc0, bc14, bc16], some (some (81, true, true))),
 ([bc0, bc17, bc18], some (some (73, true, true))),
 ([bc0, bc17, bc19], some (some (86, true, true)))]
private def goalCodes11_0_10 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc1, bc20, bc21, bc26, bc27],
  some (some bc190)),
 ([bc1, bc20, bc21, bc26, bc28],
  some (some (92, false, true))),
 ([bc1, bc20, bc21, bc29, bc30],
  some (some bc190)),
 ([bc1, bc20, bc21, bc29, bc31],
  some (some (97, false, true))),
 ([bc1, bc20, bc22, bc26, bc27],
  some (some (99, false, true))),
 ([bc1, bc20, bc22, bc26, bc28],
  some (some (100, false, true))),
 ([bc1, bc20, bc22, bc29, bc30],
  some (some (99, false, true))),
 ([bc1, bc20, bc22, bc29, bc31],
  some (some (101, false, true))),
 ([bc1, bc23, bc24, bc26, bc27],
  some (some bc190)),
 ([bc1, bc23, bc24, bc26, bc28],
  some (some (92, false, true))),
 ([bc1, bc23, bc24, bc29, bc30],
  some (some bc190)),
 ([bc1, bc23, bc24, bc29, bc31],
  some (some (97, false, true))),
 ([bc1, bc23, bc25, bc26, bc27],
  some (some (104, false, true))),
 ([bc1, bc23, bc25, bc26, bc28],
  some (some (106, false, true))),
 ([bc1, bc23, bc25, bc29, bc30],
  some (some (104, false, true))),
 ([bc1, bc23, bc25, bc29, bc31],
  some (some (107, false, true)))]
private def goalCodes11_0_12 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc44, bc32, bc33], some (some (114, true, true))),
 ([bc44, bc32, bc34], some (some (122, true, true))),
 ([bc44, bc35, bc36], some (some (114, true, true))),
 ([bc44, bc35, bc37], some (some (128, true, true)))]
private def goalCodes11_0_15 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc45, bc38, bc39], some (some (130, false, true))),
 ([bc45, bc38, bc40], some (some (135, false, true))),
 ([bc45, bc41, bc42], some (some (130, false, true))),
 ([bc45, bc41, bc43], some (some (139, false, true)))]
private def goalCodes11_0_17 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc0, bc8], some (some bc187)),
 ([bc0, bc9], some (some bc187)),
 ([bc1, bc2, bc3, bc8], some (some bc187)),
 ([bc1, bc2, bc3, bc9], some (some bc187)),
 ([bc1, bc2, bc4, bc8], some (some bc188)),
 ([bc1, bc2, bc4, bc9], some (some bc188)),
 ([bc1, bc5, bc6, bc8], some (some bc187)),
 ([bc1, bc5, bc6, bc9], some (some bc187)),
 ([bc1, bc5, bc7, bc8], some (some bc189)),
 ([bc1, bc5, bc7, bc9], some (some bc189))]
private def goalCodes11_0_19 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc44, bc0], some (some bc191)),
 ([bc44, bc1], some (some bc191)),
 ([bc45, bc46, bc47, bc0], some (some bc191)),
 ([bc45, bc46, bc47, bc1], some (some bc191)),
 ([bc45, bc46, bc48, bc0], some (some bc192)),
 ([bc45, bc46, bc48, bc1], some (some bc192)),
 ([bc45, bc49, bc50, bc0], some (some bc191)),
 ([bc45, bc49, bc50, bc1], some (some bc191)),
 ([bc45, bc49, bc51, bc0], some (some bc193)),
 ([bc45, bc49, bc51, bc1], some (some bc193))]
private def goalCodes11_1_0 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes11_0_0
private def goalCodes11_2_0 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes11_0_0
private def goalCodes11_2_2 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes11_0_2
private def goalCodes11_2_5 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes11_0_5
private def goalCodes11_2_7 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes11_0_7
private def goalCodes11_2_10 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes11_0_10
private def goalCodes11_2_12 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc171, bc52, bc53, bc54, bc60],
  some (some bc194)),
 ([bc171,
   bc52,
   bc53,
   bc54,
   bc61,
   bc62,
   bc63],
  some (some bc194)),
 ([bc171,
   bc52,
   bc53,
   bc54,
   bc61,
   bc62,
   bc64],
  some (some (385, true, true))),
 ([bc171,
   bc52,
   bc53,
   bc54,
   bc61,
   bc65,
   bc66],
  some (some bc194)),
 ([bc171,
   bc52,
   bc53,
   bc54,
   bc61,
   bc65,
   bc67],
  some (some (390, true, true))),
 ([bc171, bc52, bc53, bc55, bc60],
  some (some (391, true, true))),
 ([bc171,
   bc52,
   bc53,
   bc55,
   bc61,
   bc62,
   bc63],
  some (some (391, true, true))),
 ([bc171,
   bc52,
   bc53,
   bc55,
   bc61,
   bc62,
   bc64],
  some (some (393, true, true))),
 ([bc171,
   bc52,
   bc53,
   bc55,
   bc61,
   bc65,
   bc66],
  some (some (391, true, true))),
 ([bc171,
   bc52,
   bc53,
   bc55,
   bc61,
   bc65,
   bc67],
  some (some (394, true, true))),
 ([bc171, bc52, bc56, bc57, bc60],
  some (some bc194)),
 ([bc171,
   bc52,
   bc56,
   bc57,
   bc61,
   bc62,
   bc63],
  some (some bc194)),
 ([bc171,
   bc52,
   bc56,
   bc57,
   bc61,
   bc62,
   bc64],
  some (some (385, true, true))),
 ([bc171,
   bc52,
   bc56,
   bc57,
   bc61,
   bc65,
   bc66],
  some (some bc194)),
 ([bc171,
   bc52,
   bc56,
   bc57,
   bc61,
   bc65,
   bc67],
  some (some (390, true, true))),
 ([bc171, bc52, bc56, bc58, bc60],
  some (some (398, true, true))),
 ([bc171,
   bc52,
   bc56,
   bc58,
   bc61,
   bc62,
   bc63],
  some (some (398, true, true))),
 ([bc171,
   bc52,
   bc56,
   bc58,
   bc61,
   bc62,
   bc64],
  some (some (399, true, true))),
 ([bc171,
   bc52,
   bc56,
   bc58,
   bc61,
   bc65,
   bc66],
  some (some (398, true, true))),
 ([bc171,
   bc52,
   bc56,
   bc58,
   bc61,
   bc65,
   bc67],
  some (some (400, true, true))),
 ([bc171, bc59, bc60], some (some bc194)),
 ([bc171, bc59, bc61, bc62, bc63],
  some (some bc194)),
 ([bc171, bc59, bc61, bc62, bc64],
  some (some (385, true, true))),
 ([bc171, bc59, bc61, bc65, bc66],
  some (some bc194)),
 ([bc171, bc59, bc61, bc65, bc67],
  some (some (390, true, true)))]
private def goalCodes11_2_14 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc174, bc68, bc76, bc77, bc78],
  some (some bc195)),
 ([bc174, bc68, bc76, bc77, bc79],
  some (some (407, false, true))),
 ([bc174, bc68, bc76, bc80, bc81],
  some (some bc195)),
 ([bc174, bc68, bc76, bc80, bc82],
  some (some (411, false, true))),
 ([bc174, bc68, bc83], some (some bc195)),
 ([bc174,
   bc69,
   bc70,
   bc71,
   bc76,
   bc77,
   bc78],
  some (some bc195)),
 ([bc174,
   bc69,
   bc70,
   bc71,
   bc76,
   bc77,
   bc79],
  some (some (407, false, true))),
 ([bc174,
   bc69,
   bc70,
   bc71,
   bc76,
   bc80,
   bc81],
  some (some bc195)),
 ([bc174,
   bc69,
   bc70,
   bc71,
   bc76,
   bc80,
   bc82],
  some (some (411, false, true))),
 ([bc174, bc69, bc70, bc71, bc83],
  some (some bc195)),
 ([bc174,
   bc69,
   bc70,
   bc72,
   bc76,
   bc77,
   bc78],
  some (some (418, false, true))),
 ([bc174,
   bc69,
   bc70,
   bc72,
   bc76,
   bc77,
   bc79],
  some (some (419, false, true))),
 ([bc174,
   bc69,
   bc70,
   bc72,
   bc76,
   bc80,
   bc81],
  some (some (418, false, true))),
 ([bc174,
   bc69,
   bc70,
   bc72,
   bc76,
   bc80,
   bc82],
  some (some (420, false, true))),
 ([bc174, bc69, bc70, bc72, bc83],
  some (some (418, false, true))),
 ([bc174,
   bc69,
   bc73,
   bc74,
   bc76,
   bc77,
   bc78],
  some (some bc195)),
 ([bc174,
   bc69,
   bc73,
   bc74,
   bc76,
   bc77,
   bc79],
  some (some (407, false, true))),
 ([bc174,
   bc69,
   bc73,
   bc74,
   bc76,
   bc80,
   bc81],
  some (some bc195)),
 ([bc174,
   bc69,
   bc73,
   bc74,
   bc76,
   bc80,
   bc82],
  some (some (411, false, true))),
 ([bc174, bc69, bc73, bc74, bc83],
  some (some bc195)),
 ([bc174,
   bc69,
   bc73,
   bc75,
   bc76,
   bc77,
   bc78],
  some (some (424, false, true))),
 ([bc174,
   bc69,
   bc73,
   bc75,
   bc76,
   bc77,
   bc79],
  some (some (425, false, true))),
 ([bc174,
   bc69,
   bc73,
   bc75,
   bc76,
   bc80,
   bc81],
  some (some (424, false, true))),
 ([bc174,
   bc69,
   bc73,
   bc75,
   bc76,
   bc80,
   bc82],
  some (some (426, false, true))),
 ([bc174, bc69, bc73, bc75, bc83],
  some (some (424, false, true)))]
private def goalCodes11_2_17 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc183, bc84, bc85, bc86, bc92],
  some (some bc196)),
 ([bc183,
   bc84,
   bc85,
   bc86,
   bc93,
   bc94,
   bc95],
  some (some bc196)),
 ([bc183,
   bc84,
   bc85,
   bc86,
   bc93,
   bc94,
   bc96],
  some (some (187, true, true))),
 ([bc183,
   bc84,
   bc85,
   bc86,
   bc93,
   bc97,
   bc98],
  some (some bc196)),
 ([bc183,
   bc84,
   bc85,
   bc86,
   bc93,
   bc97,
   bc99],
  some (some (191, true, true))),
 ([bc183, bc84, bc85, bc87, bc92],
  some (some (194, true, true))),
 ([bc183,
   bc84,
   bc85,
   bc87,
   bc93,
   bc94,
   bc95],
  some (some (194, true, true))),
 ([bc183,
   bc84,
   bc85,
   bc87,
   bc93,
   bc94,
   bc96],
  some (some (195, true, true))),
 ([bc183,
   bc84,
   bc85,
   bc87,
   bc93,
   bc97,
   bc98],
  some (some (194, true, true))),
 ([bc183,
   bc84,
   bc85,
   bc87,
   bc93,
   bc97,
   bc99],
  some (some (196, true, true))),
 ([bc183, bc84, bc88, bc89, bc92],
  some (some bc196)),
 ([bc183,
   bc84,
   bc88,
   bc89,
   bc93,
   bc94,
   bc95],
  some (some bc196)),
 ([bc183,
   bc84,
   bc88,
   bc89,
   bc93,
   bc94,
   bc96],
  some (some (187, true, true))),
 ([bc183,
   bc84,
   bc88,
   bc89,
   bc93,
   bc97,
   bc98],
  some (some bc196)),
 ([bc183,
   bc84,
   bc88,
   bc89,
   bc93,
   bc97,
   bc99],
  some (some (191, true, true))),
 ([bc183, bc84, bc88, bc90, bc92],
  some (some (199, true, true))),
 ([bc183,
   bc84,
   bc88,
   bc90,
   bc93,
   bc94,
   bc95],
  some (some (199, true, true))),
 ([bc183,
   bc84,
   bc88,
   bc90,
   bc93,
   bc94,
   bc96],
  some (some (201, true, true))),
 ([bc183,
   bc84,
   bc88,
   bc90,
   bc93,
   bc97,
   bc98],
  some (some (199, true, true))),
 ([bc183,
   bc84,
   bc88,
   bc90,
   bc93,
   bc97,
   bc99],
  some (some (202, true, true))),
 ([bc183, bc91, bc92], some (some bc196)),
 ([bc183, bc91, bc93, bc94, bc95],
  some (some bc196)),
 ([bc183, bc91, bc93, bc94, bc96],
  some (some (187, true, true))),
 ([bc183, bc91, bc93, bc97, bc98],
  some (some bc196)),
 ([bc183, bc91, bc93, bc97, bc99],
  some (some (191, true, true)))]
private def goalCodes11_2_19 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc184, (206, false, true), bc103], some (some bc197)),
 ([bc184, (206, false, true), bc104], some (some bc197)),
 ([bc184, bc100, bc101, (208, false, true), bc103],
  some (some bc197)),
 ([bc184, bc100, bc101, (208, false, true), bc104],
  some (some bc197)),
 ([bc184, bc100, bc101, (208, true, false), bc103],
  some (some (212, false, true))),
 ([bc184, bc100, bc101, (208, true, false), bc104],
  some (some (212, false, true))),
 ([bc184, bc100, bc102, (213, true, true), bc103],
  some (some bc197)),
 ([bc184, bc100, bc102, (213, true, true), bc104],
  some (some bc197)),
 ([bc184, bc100, bc102, (213, false, false), bc103],
  some (some (215, false, true))),
 ([bc184, bc100, bc102, (213, false, false), bc104],
  some (some (215, false, true)))]
private def goalCodes11_2_22 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes11_0_17
private def goalCodes11_3_0 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes11_0_0
private def goalCodes11_3_2 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes11_0_2
private def goalCodes11_3_5 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes11_0_5
private def goalCodes11_3_7 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc2, bc105, bc106, bc15, bc109],
  some (some bc198)),
 ([bc2,
   bc105,
   bc106,
   bc15,
   bc110,
   bc111,
   bc112],
  some (some bc198)),
 ([bc2,
   bc105,
   bc106,
   bc15,
   bc110,
   bc111,
   bc113],
  some (some (304, true, true))),
 ([bc2,
   bc105,
   bc106,
   bc15,
   bc110,
   bc114,
   bc115],
  some (some bc198)),
 ([bc2,
   bc105,
   bc106,
   bc15,
   bc110,
   bc114,
   bc116],
  some (some (309, true, true))),
 ([bc2, bc105, bc106, bc16, bc109],
  some (some (310, true, true))),
 ([bc2,
   bc105,
   bc106,
   bc16,
   bc110,
   bc111,
   bc112],
  some (some (310, true, true))),
 ([bc2,
   bc105,
   bc106,
   bc16,
   bc110,
   bc111,
   bc113],
  some (some (311, true, true))),
 ([bc2,
   bc105,
   bc106,
   bc16,
   bc110,
   bc114,
   bc115],
  some (some (310, true, true))),
 ([bc2,
   bc105,
   bc106,
   bc16,
   bc110,
   bc114,
   bc116],
  some (some (312, true, true))),
 ([bc2, bc105, bc107, bc18, bc109],
  some (some bc198)),
 ([bc2,
   bc105,
   bc107,
   bc18,
   bc110,
   bc111,
   bc112],
  some (some bc198)),
 ([bc2,
   bc105,
   bc107,
   bc18,
   bc110,
   bc111,
   bc113],
  some (some (304, true, true))),
 ([bc2,
   bc105,
   bc107,
   bc18,
   bc110,
   bc114,
   bc115],
  some (some bc198)),
 ([bc2,
   bc105,
   bc107,
   bc18,
   bc110,
   bc114,
   bc116],
  some (some (309, true, true))),
 ([bc2, bc105, bc107, bc19, bc109],
  some (some (314, true, true))),
 ([bc2,
   bc105,
   bc107,
   bc19,
   bc110,
   bc111,
   bc112],
  some (some (314, true, true))),
 ([bc2,
   bc105,
   bc107,
   bc19,
   bc110,
   bc111,
   bc113],
  some (some (315, true, true))),
 ([bc2,
   bc105,
   bc107,
   bc19,
   bc110,
   bc114,
   bc115],
  some (some (314, true, true))),
 ([bc2,
   bc105,
   bc107,
   bc19,
   bc110,
   bc114,
   bc116],
  some (some (316, true, true))),
 ([bc2, bc108, bc109], some (some bc198)),
 ([bc2, bc108, bc110, bc111, bc112],
  some (some bc198)),
 ([bc2, bc108, bc110, bc111, bc113],
  some (some (304, true, true))),
 ([bc2, bc108, bc110, bc114, bc115],
  some (some bc198)),
 ([bc2, bc108, bc110, bc114, bc116],
  some (some (309, true, true)))]
private def goalCodes11_3_9 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc5, bc117, bc125, bc126, bc127],
  some (some bc199)),
 ([bc5, bc117, bc125, bc126, bc128],
  some (some (323, false, true))),
 ([bc5, bc117, bc125, bc129, bc130],
  some (some bc199)),
 ([bc5, bc117, bc125, bc129, bc131],
  some (some (327, false, true))),
 ([bc5, bc117, bc132], some (some bc199)),
 ([bc5,
   bc118,
   bc119,
   bc120,
   bc125,
   bc126,
   bc127],
  some (some bc199)),
 ([bc5,
   bc118,
   bc119,
   bc120,
   bc125,
   bc126,
   bc128],
  some (some (323, false, true))),
 ([bc5,
   bc118,
   bc119,
   bc120,
   bc125,
   bc129,
   bc130],
  some (some bc199)),
 ([bc5,
   bc118,
   bc119,
   bc120,
   bc125,
   bc129,
   bc131],
  some (some (327, false, true))),
 ([bc5, bc118, bc119, bc120, bc132],
  some (some bc199)),
 ([bc5,
   bc118,
   bc119,
   bc121,
   bc125,
   bc126,
   bc127],
  some (some (334, false, true))),
 ([bc5,
   bc118,
   bc119,
   bc121,
   bc125,
   bc126,
   bc128],
  some (some (335, false, true))),
 ([bc5,
   bc118,
   bc119,
   bc121,
   bc125,
   bc129,
   bc130],
  some (some (334, false, true))),
 ([bc5,
   bc118,
   bc119,
   bc121,
   bc125,
   bc129,
   bc131],
  some (some (336, false, true))),
 ([bc5, bc118, bc119, bc121, bc132],
  some (some (334, false, true))),
 ([bc5,
   bc118,
   bc122,
   bc123,
   bc125,
   bc126,
   bc127],
  some (some bc199)),
 ([bc5,
   bc118,
   bc122,
   bc123,
   bc125,
   bc126,
   bc128],
  some (some (323, false, true))),
 ([bc5,
   bc118,
   bc122,
   bc123,
   bc125,
   bc129,
   bc130],
  some (some bc199)),
 ([bc5,
   bc118,
   bc122,
   bc123,
   bc125,
   bc129,
   bc131],
  some (some (327, false, true))),
 ([bc5, bc118, bc122, bc123, bc132],
  some (some bc199)),
 ([bc5,
   bc118,
   bc122,
   bc124,
   bc125,
   bc126,
   bc127],
  some (some (340, false, true))),
 ([bc5,
   bc118,
   bc122,
   bc124,
   bc125,
   bc126,
   bc128],
  some (some (341, false, true))),
 ([bc5,
   bc118,
   bc122,
   bc124,
   bc125,
   bc129,
   bc130],
  some (some (340, false, true))),
 ([bc5,
   bc118,
   bc122,
   bc124,
   bc125,
   bc129,
   bc131],
  some (some (342, false, true))),
 ([bc5, bc118, bc122, bc124, bc132],
  some (some (340, false, true)))]
private def goalCodes11_3_12 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc46, bc133, bc134, bc33, bc137],
  some (some bc200)),
 ([bc46,
   bc133,
   bc134,
   bc33,
   bc138,
   bc139,
   bc140],
  some (some bc200)),
 ([bc46,
   bc133,
   bc134,
   bc33,
   bc138,
   bc139,
   bc141],
  some (some (350, true, true))),
 ([bc46,
   bc133,
   bc134,
   bc33,
   bc138,
   bc142,
   bc143],
  some (some bc200)),
 ([bc46,
   bc133,
   bc134,
   bc33,
   bc138,
   bc142,
   bc144],
  some (some (354, true, true))),
 ([bc46, bc133, bc134, bc34, bc137],
  some (some (356, true, true))),
 ([bc46,
   bc133,
   bc134,
   bc34,
   bc138,
   bc139,
   bc140],
  some (some (356, true, true))),
 ([bc46,
   bc133,
   bc134,
   bc34,
   bc138,
   bc139,
   bc141],
  some (some (357, true, true))),
 ([bc46,
   bc133,
   bc134,
   bc34,
   bc138,
   bc142,
   bc143],
  some (some (356, true, true))),
 ([bc46,
   bc133,
   bc134,
   bc34,
   bc138,
   bc142,
   bc144],
  some (some (358, true, true))),
 ([bc46, bc133, bc135, bc36, bc137],
  some (some bc200)),
 ([bc46,
   bc133,
   bc135,
   bc36,
   bc138,
   bc139,
   bc140],
  some (some bc200)),
 ([bc46,
   bc133,
   bc135,
   bc36,
   bc138,
   bc139,
   bc141],
  some (some (350, true, true))),
 ([bc46,
   bc133,
   bc135,
   bc36,
   bc138,
   bc142,
   bc143],
  some (some bc200)),
 ([bc46,
   bc133,
   bc135,
   bc36,
   bc138,
   bc142,
   bc144],
  some (some (354, true, true))),
 ([bc46, bc133, bc135, bc37, bc137],
  some (some (360, true, true))),
 ([bc46,
   bc133,
   bc135,
   bc37,
   bc138,
   bc139,
   bc140],
  some (some (360, true, true))),
 ([bc46,
   bc133,
   bc135,
   bc37,
   bc138,
   bc139,
   bc141],
  some (some (361, true, true))),
 ([bc46,
   bc133,
   bc135,
   bc37,
   bc138,
   bc142,
   bc143],
  some (some (360, true, true))),
 ([bc46,
   bc133,
   bc135,
   bc37,
   bc138,
   bc142,
   bc144],
  some (some (362, true, true))),
 ([bc46, bc136, bc137], some (some bc200)),
 ([bc46, bc136, bc138, bc139, bc140],
  some (some bc200)),
 ([bc46, bc136, bc138, bc139, bc141],
  some (some (350, true, true))),
 ([bc46, bc136, bc138, bc142, bc143],
  some (some bc200)),
 ([bc46, bc136, bc138, bc142, bc144],
  some (some (354, true, true)))]
private def goalCodes11_3_14 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc49, (365, false, true), bc148], some (some bc201)),
 ([bc49, (365, false, true), bc149], some (some bc201)),
 ([bc49, bc145, bc146, (370, false, true), bc148],
  some (some bc201)),
 ([bc49, bc145, bc146, (370, false, true), bc149],
  some (some bc201)),
 ([bc49, bc145, bc146, (370, true, false), bc148],
  some (some (372, false, true))),
 ([bc49, bc145, bc146, (370, true, false), bc149],
  some (some (372, false, true))),
 ([bc49, bc145, bc147, (373, true, true), bc148],
  some (some bc201)),
 ([bc49, bc145, bc147, (373, true, true), bc149],
  some (some bc201)),
 ([bc49, bc145, bc147, (373, false, false), bc148],
  some (some (375, false, true))),
 ([bc49, bc145, bc147, (373, false, false), bc149],
  some (some (375, false, true)))]
private def goalCodes11_3_17 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes11_2_12
private def goalCodes11_3_19 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes11_2_14
private def goalCodes11_3_22 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc177, bc150, bc151, (427, false, true), bc153],
  some (some bc202)),
 ([bc177, bc150, bc151, (427, false, true), bc154],
  some (some bc202)),
 ([bc177, bc150, bc151, (427, true, false), bc153],
  some (some (434, true, true))),
 ([bc177, bc150, bc151, (427, true, false), bc154],
  some (some (434, true, true))),
 ([bc177, bc150, bc152, (436, true, true), bc153],
  some (some bc202)),
 ([bc177, bc150, bc152, (436, true, true), bc154],
  some (some bc202)),
 ([bc177, bc150, bc152, (436, false, false), bc153],
  some (some (439, true, true))),
 ([bc177, bc150, bc152, (436, false, false), bc154],
  some (some (439, true, true))),
 ([bc177, (432, true, true), bc153], some (some bc202)),
 ([bc177, (432, true, true), bc154], some (some bc202))]
private def goalCodes11_3_24 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc180, bc155, bc163, bc164, bc165],
  some (some bc203)),
 ([bc180, bc155, bc163, bc164, bc166],
  some (some (447, false, true))),
 ([bc180, bc155, bc163, bc167, bc168],
  some (some bc203)),
 ([bc180, bc155, bc163, bc167, bc169],
  some (some (451, false, true))),
 ([bc180, bc155, bc170], some (some bc203)),
 ([bc180,
   bc156,
   bc157,
   bc158,
   bc163,
   bc164,
   bc165],
  some (some bc203)),
 ([bc180,
   bc156,
   bc157,
   bc158,
   bc163,
   bc164,
   bc166],
  some (some (447, false, true))),
 ([bc180,
   bc156,
   bc157,
   bc158,
   bc163,
   bc167,
   bc168],
  some (some bc203)),
 ([bc180,
   bc156,
   bc157,
   bc158,
   bc163,
   bc167,
   bc169],
  some (some (451, false, true))),
 ([bc180, bc156, bc157, bc158, bc170],
  some (some bc203)),
 ([bc180,
   bc156,
   bc157,
   bc159,
   bc163,
   bc164,
   bc165],
  some (some (458, false, true))),
 ([bc180,
   bc156,
   bc157,
   bc159,
   bc163,
   bc164,
   bc166],
  some (some (459, false, true))),
 ([bc180,
   bc156,
   bc157,
   bc159,
   bc163,
   bc167,
   bc168],
  some (some (458, false, true))),
 ([bc180,
   bc156,
   bc157,
   bc159,
   bc163,
   bc167,
   bc169],
  some (some (460, false, true))),
 ([bc180, bc156, bc157, bc159, bc170],
  some (some (458, false, true))),
 ([bc180,
   bc156,
   bc160,
   bc161,
   bc163,
   bc164,
   bc165],
  some (some bc203)),
 ([bc180,
   bc156,
   bc160,
   bc161,
   bc163,
   bc164,
   bc166],
  some (some (447, false, true))),
 ([bc180,
   bc156,
   bc160,
   bc161,
   bc163,
   bc167,
   bc168],
  some (some bc203)),
 ([bc180,
   bc156,
   bc160,
   bc161,
   bc163,
   bc167,
   bc169],
  some (some (451, false, true))),
 ([bc180, bc156, bc160, bc161, bc170],
  some (some bc203)),
 ([bc180,
   bc156,
   bc160,
   bc162,
   bc163,
   bc164,
   bc165],
  some (some (464, false, true))),
 ([bc180,
   bc156,
   bc160,
   bc162,
   bc163,
   bc164,
   bc166],
  some (some (465, false, true))),
 ([bc180,
   bc156,
   bc160,
   bc162,
   bc163,
   bc167,
   bc168],
  some (some (464, false, true))),
 ([bc180,
   bc156,
   bc160,
   bc162,
   bc163,
   bc167,
   bc169],
  some (some (466, false, true))),
 ([bc180, bc156, bc160, bc162, bc170],
  some (some (464, false, true)))]
private def goalCodes11_3_27 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes11_2_17
private def goalCodes11_3_29 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes11_2_19
private def goalCodes11_3_32 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc2, bc3, bc8], some (some bc187)),
 ([bc2, bc3, bc9], some (some bc187)),
 ([bc2, bc4, bc8], some (some bc188)),
 ([bc2, bc4, bc9], some (some bc188)),
 ([bc5, bc6, bc8], some (some bc187)),
 ([bc5, bc6, bc9], some (some bc187)),
 ([bc5, bc7, bc8], some (some bc189)),
 ([bc5, bc7, bc9], some (some bc189))]
private def goalCodes11_3_34 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc46, bc47, bc2, bc27], some (some bc204)),
 ([bc46, bc47, bc2, bc28], some (some (468, true, false))),
 ([bc46, bc47, bc5, bc30], some (some bc204)),
 ([bc46, bc47, bc5, bc31], some (some (469, true, false))),
 ([bc46, bc48, bc2, bc27], some (some (470, true, false))),
 ([bc46, bc48, bc2, bc28], some (some (471, true, false))),
 ([bc46, bc48, bc5, bc30], some (some (470, true, false))),
 ([bc46, bc48, bc5, bc31], some (some (472, true, false))),
 ([bc49, bc50, bc2, bc27], some (some bc204)),
 ([bc49, bc50, bc2, bc28], some (some (468, true, false))),
 ([bc49, bc50, bc5, bc30], some (some bc204)),
 ([bc49, bc50, bc5, bc31], some (some (469, true, false))),
 ([bc49, bc51, bc2, bc27], some (some (473, true, false))),
 ([bc49, bc51, bc2, bc28], some (some (474, true, false))),
 ([bc49, bc51, bc5, bc30], some (some (473, true, false))),
 ([bc49, bc51, bc5, bc31], some (some (475, true, false)))]
private def goalCodes11_3_35 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc46, bc47, bc171, bc172], some (some bc191)),
 ([bc46, bc47, bc171, bc173], some (some (477, true, false))),
 ([bc46, bc47, bc174, bc175], some (some bc191)),
 ([bc46, bc47, bc174, bc176], some (some (481, true, false))),
 ([bc46, bc48, bc171, bc172], some (some bc192)),
 ([bc46, bc48, bc171, bc173], some (some (482, true, false))),
 ([bc46, bc48, bc174, bc175], some (some bc192)),
 ([bc46, bc48, bc174, bc176], some (some (483, true, false))),
 ([bc49, bc50, bc171, bc172], some (some bc191)),
 ([bc49, bc50, bc171, bc173], some (some (477, true, false))),
 ([bc49, bc50, bc174, bc175], some (some bc191)),
 ([bc49, bc50, bc174, bc176], some (some (481, true, false))),
 ([bc49, bc51, bc171, bc172], some (some bc193)),
 ([bc49, bc51, bc171, bc173], some (some (484, true, false))),
 ([bc49, bc51, bc174, bc175], some (some bc193)),
 ([bc49, bc51, bc174, bc176], some (some (485, true, false)))]
private def goalCodes11_3_36 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc171, bc21], some (some (486, false, false))),
 ([bc171, bc22], some (some (487, false, false))),
 ([bc174, bc24], some (some (486, false, false))),
 ([bc174, bc25], some (some (488, false, false)))]
private def goalCodes11_3_38 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc177, bc178, bc171, bc172], some (some bc205)),
 ([bc177, bc178, bc171, bc173], some (some (491, false, false))),
 ([bc177, bc178, bc174, bc175], some (some bc205)),
 ([bc177, bc178, bc174, bc176], some (some (492, false, false))),
 ([bc177, bc179, bc171, bc172], some (some (494, false, false))),
 ([bc177, bc179, bc171, bc173], some (some (495, false, false))),
 ([bc177, bc179, bc174, bc175], some (some (494, false, false))),
 ([bc177, bc179, bc174, bc176], some (some (496, false, false))),
 ([bc180, bc181, bc171, bc172], some (some bc205)),
 ([bc180, bc181, bc171, bc173], some (some (491, false, false))),
 ([bc180, bc181, bc174, bc175], some (some bc205)),
 ([bc180, bc181, bc174, bc176], some (some (492, false, false))),
 ([bc180, bc182, bc171, bc172], some (some (499, false, false))),
 ([bc180, bc182, bc171, bc173], some (some (500, false, false))),
 ([bc180, bc182, bc174, bc175], some (some (499, false, false))),
 ([bc180, bc182, bc174, bc176], some (some (501, false, false)))]
private def goalCodes11_3_39 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc177, bc178], some (some (502, false, false))),
 ([bc177, bc179], some (some (503, false, false))),
 ([bc180, bc181], some (some (502, false, false))),
 ([bc180, bc182], some (some (504, false, false)))]
private def goalCodes11_3_40 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc183, bc39], some (some (505, true, false))),
 ([bc183, bc40], some (some (506, true, false))),
 ([bc184, bc42], some (some (505, true, false))),
 ([bc184, bc43], some (some (507, true, false)))]
private def goalCodes11_4_0 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes11_0_0
private def cutCodes11_0 : List (ℕ × Bool × Bool) := [(7, false, true)]
private def cutCodes11_1 : List (ℕ × Bool × Bool) := [bc206, (177, false, false), (551, true, true)]
private def cutCodes11_2 : List (ℕ × Bool × Bool) := [bc206, (177, false, false), (551, false, false)]
private def cutCodes11_3 : List (ℕ × Bool × Bool) := [bc206, (177, true, true), (296, false, true)]
private def cutCodes11_4 : List (ℕ × Bool × Bool) := [bc206, (177, true, true), (296, true, false)]

private theorem hGoal11_0_0 : trunkGoalBranches (trunkCatalog.states 11) 0 0 = goalCodes11_0_0.map decodeGoalBranch := by
  decide +kernel

private abbrev goalSpec11_0_2 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 11) 0))[2-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal11_0_2 : trunkGoalBranches (trunkCatalog.states 11) 0 2 = goalCodes11_0_2.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 11).context goalSpec11_0_2 = _
  exact (cachedBranches_eq (trunkCatalog.states 11).context goalSpec11_0_2
    endpointInput11_4 endpointInput11_5 (([bc8] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes11_4.map decodeEndpoint11) (endpointCodes11_5.map decodeEndpoint11)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint11_4 hEndpoint11_5).trans
    (by decide +kernel)

private abbrev goalSpec11_0_5 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 11) 0))[5-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal11_0_5 : trunkGoalBranches (trunkCatalog.states 11) 0 5 = goalCodes11_0_5.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 11).context goalSpec11_0_5 = _
  exact (cachedBranches_eq (trunkCatalog.states 11).context goalSpec11_0_5
    endpointInput11_6 endpointInput11_7 (([bc9] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes11_6.map decodeEndpoint11) (endpointCodes11_7.map decodeEndpoint11)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint11_6 hEndpoint11_7).trans
    (by decide +kernel)

private abbrev goalSpec11_0_7 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 11) 0))[7-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal11_0_7 : trunkGoalBranches (trunkCatalog.states 11) 0 7 = goalCodes11_0_7.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 11).context goalSpec11_0_7 = _
  exact (cachedBranches_eq (trunkCatalog.states 11).context goalSpec11_0_7
    endpointInput11_8 endpointInput11_9 (([bc0] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes11_8.map decodeEndpoint11) (endpointCodes11_9.map decodeEndpoint11)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint11_8 hEndpoint11_9).trans
    (by decide +kernel)

private abbrev goalSpec11_0_10 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 11) 0))[10-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal11_0_10 : trunkGoalBranches (trunkCatalog.states 11) 0 10 = goalCodes11_0_10.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 11).context goalSpec11_0_10 = _
  exact (cachedBranches_eq (trunkCatalog.states 11).context goalSpec11_0_10
    endpointInput11_10 endpointInput11_11 (([bc1] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes11_10.map decodeEndpoint11) (endpointCodes11_11.map decodeEndpoint11)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint11_10 hEndpoint11_11).trans
    (by decide +kernel)

private abbrev goalSpec11_0_12 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 11) 0))[12-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal11_0_12 : trunkGoalBranches (trunkCatalog.states 11) 0 12 = goalCodes11_0_12.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 11).context goalSpec11_0_12 = _
  exact (cachedBranches_eq (trunkCatalog.states 11).context goalSpec11_0_12
    endpointInput11_12 endpointInput11_13 (([bc44] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes11_12.map decodeEndpoint11) (endpointCodes11_13.map decodeEndpoint11)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint11_12 hEndpoint11_13).trans
    (by decide +kernel)

private abbrev goalSpec11_0_15 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 11) 0))[15-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal11_0_15 : trunkGoalBranches (trunkCatalog.states 11) 0 15 = goalCodes11_0_15.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 11).context goalSpec11_0_15 = _
  exact (cachedBranches_eq (trunkCatalog.states 11).context goalSpec11_0_15
    endpointInput11_14 endpointInput11_15 (([bc45] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes11_14.map decodeEndpoint11) (endpointCodes11_15.map decodeEndpoint11)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint11_14 hEndpoint11_15).trans
    (by decide +kernel)

private abbrev goalSpec11_0_17 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 11) 0))[17-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal11_0_17 : trunkGoalBranches (trunkCatalog.states 11) 0 17 = goalCodes11_0_17.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 11).context goalSpec11_0_17 = _
  exact (cachedBranches_eq (trunkCatalog.states 11).context goalSpec11_0_17
    endpointInput11_0 endpointInput11_1 (([] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes11_0.map decodeEndpoint11) (endpointCodes11_1.map decodeEndpoint11)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint11_0 hEndpoint11_1).trans
    (by decide +kernel)

private abbrev goalSpec11_0_19 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 11) 0))[19-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal11_0_19 : trunkGoalBranches (trunkCatalog.states 11) 0 19 = goalCodes11_0_19.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 11).context goalSpec11_0_19 = _
  exact (cachedBranches_eq (trunkCatalog.states 11).context goalSpec11_0_19
    endpointInput11_16 endpointInput11_3 (([] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes11_16.map decodeEndpoint11) (endpointCodes11_3.map decodeEndpoint11)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint11_16 hEndpoint11_3).trans
    (by decide +kernel)

private theorem hGoal11_1_0 : trunkGoalBranches (trunkCatalog.states 11) 1 0 = goalCodes11_1_0.map decodeGoalBranch := by
  exact hGoal11_0_0

private theorem hGoal11_2_0 : trunkGoalBranches (trunkCatalog.states 11) 2 0 = goalCodes11_2_0.map decodeGoalBranch := by
  exact hGoal11_0_0

private abbrev goalSpec11_2_2 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 11) 2))[2-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal11_2_2 : trunkGoalBranches (trunkCatalog.states 11) 2 2 = goalCodes11_2_2.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 11) 2 2 = trunkGoalBranches (trunkCatalog.states 11) 0 2 := by
      apply congrArg (trunkBranches (trunkCatalog.states 11).context)
      decide +kernel
    exact he.trans hGoal11_0_2
  | change trunkBranches (trunkCatalog.states 11).context goalSpec11_2_2 = _
    exact (cachedBranches_eq (trunkCatalog.states 11).context goalSpec11_2_2
      endpointInput11_4 endpointInput11_5 (([bc8] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
      (endpointCodes11_4.map decodeEndpoint11) (endpointCodes11_5.map decodeEndpoint11)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint11_4 hEndpoint11_5).trans
      (by decide +kernel)

private abbrev goalSpec11_2_5 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 11) 2))[5-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal11_2_5 : trunkGoalBranches (trunkCatalog.states 11) 2 5 = goalCodes11_2_5.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 11) 2 5 = trunkGoalBranches (trunkCatalog.states 11) 0 5 := by
      apply congrArg (trunkBranches (trunkCatalog.states 11).context)
      decide +kernel
    exact he.trans hGoal11_0_5
  | change trunkBranches (trunkCatalog.states 11).context goalSpec11_2_5 = _
    exact (cachedBranches_eq (trunkCatalog.states 11).context goalSpec11_2_5
      endpointInput11_6 endpointInput11_7 (([bc9] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
      (endpointCodes11_6.map decodeEndpoint11) (endpointCodes11_7.map decodeEndpoint11)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint11_6 hEndpoint11_7).trans
      (by decide +kernel)

private abbrev goalSpec11_2_7 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 11) 2))[7-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal11_2_7 : trunkGoalBranches (trunkCatalog.states 11) 2 7 = goalCodes11_2_7.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 11) 2 7 = trunkGoalBranches (trunkCatalog.states 11) 0 7 := by
      apply congrArg (trunkBranches (trunkCatalog.states 11).context)
      decide +kernel
    exact he.trans hGoal11_0_7
  | change trunkBranches (trunkCatalog.states 11).context goalSpec11_2_7 = _
    exact (cachedBranches_eq (trunkCatalog.states 11).context goalSpec11_2_7
      endpointInput11_8 endpointInput11_9 (([bc0] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
      (endpointCodes11_8.map decodeEndpoint11) (endpointCodes11_9.map decodeEndpoint11)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint11_8 hEndpoint11_9).trans
      (by decide +kernel)

private abbrev goalSpec11_2_10 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 11) 2))[10-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal11_2_10 : trunkGoalBranches (trunkCatalog.states 11) 2 10 = goalCodes11_2_10.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 11) 2 10 = trunkGoalBranches (trunkCatalog.states 11) 0 10 := by
      apply congrArg (trunkBranches (trunkCatalog.states 11).context)
      decide +kernel
    exact he.trans hGoal11_0_10
  | change trunkBranches (trunkCatalog.states 11).context goalSpec11_2_10 = _
    exact (cachedBranches_eq (trunkCatalog.states 11).context goalSpec11_2_10
      endpointInput11_10 endpointInput11_11 (([bc1] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
      (endpointCodes11_10.map decodeEndpoint11) (endpointCodes11_11.map decodeEndpoint11)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint11_10 hEndpoint11_11).trans
      (by decide +kernel)

private abbrev goalSpec11_2_12 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 11) 2))[12-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal11_2_12 : trunkGoalBranches (trunkCatalog.states 11) 2 12 = goalCodes11_2_12.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 11).context goalSpec11_2_12 = _
  exact (cachedBranches_eq (trunkCatalog.states 11).context goalSpec11_2_12
    endpointInput11_17 endpointInput11_18 (([bc171] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes11_17.map decodeEndpoint11) (endpointCodes11_18.map decodeEndpoint11)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint11_17 hEndpoint11_18).trans
    (by decide +kernel)

private abbrev goalSpec11_2_14 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 11) 2))[14-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal11_2_14 : trunkGoalBranches (trunkCatalog.states 11) 2 14 = goalCodes11_2_14.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 11).context goalSpec11_2_14 = _
  exact (cachedBranches_eq (trunkCatalog.states 11).context goalSpec11_2_14
    endpointInput11_19 endpointInput11_20 (([bc174] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes11_19.map decodeEndpoint11) (endpointCodes11_20.map decodeEndpoint11)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint11_19 hEndpoint11_20).trans
    (by decide +kernel)

private abbrev goalSpec11_2_17 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 11) 2))[17-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal11_2_17 : trunkGoalBranches (trunkCatalog.states 11) 2 17 = goalCodes11_2_17.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 11).context goalSpec11_2_17 = _
  exact (cachedBranches_eq (trunkCatalog.states 11).context goalSpec11_2_17
    endpointInput11_21 endpointInput11_22 (([bc183] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes11_21.map decodeEndpoint11) (endpointCodes11_22.map decodeEndpoint11)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint11_21 hEndpoint11_22).trans
    (by decide +kernel)

private abbrev goalSpec11_2_19 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 11) 2))[19-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal11_2_19 : trunkGoalBranches (trunkCatalog.states 11) 2 19 = goalCodes11_2_19.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 11).context goalSpec11_2_19 = _
  exact (cachedBranches_eq (trunkCatalog.states 11).context goalSpec11_2_19
    endpointInput11_23 endpointInput11_24 (([bc184] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes11_23.map decodeEndpoint11) (endpointCodes11_24.map decodeEndpoint11)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint11_23 hEndpoint11_24).trans
    (by decide +kernel)

private abbrev goalSpec11_2_22 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 11) 2))[22-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal11_2_22 : trunkGoalBranches (trunkCatalog.states 11) 2 22 = goalCodes11_2_22.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 11) 2 22 = trunkGoalBranches (trunkCatalog.states 11) 0 17 := by
      apply congrArg (trunkBranches (trunkCatalog.states 11).context)
      decide +kernel
    exact he.trans hGoal11_0_17
  | change trunkBranches (trunkCatalog.states 11).context goalSpec11_2_22 = _
    exact (cachedBranches_eq (trunkCatalog.states 11).context goalSpec11_2_22
      endpointInput11_0 endpointInput11_1 (([] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
      (endpointCodes11_0.map decodeEndpoint11) (endpointCodes11_1.map decodeEndpoint11)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint11_0 hEndpoint11_1).trans
      (by decide +kernel)

private theorem hGoal11_3_0 : trunkGoalBranches (trunkCatalog.states 11) 3 0 = goalCodes11_3_0.map decodeGoalBranch := by
  exact hGoal11_0_0

private abbrev goalSpec11_3_2 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 11) 3))[2-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal11_3_2 : trunkGoalBranches (trunkCatalog.states 11) 3 2 = goalCodes11_3_2.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 11) 3 2 = trunkGoalBranches (trunkCatalog.states 11) 0 2 := by
      apply congrArg (trunkBranches (trunkCatalog.states 11).context)
      decide +kernel
    exact he.trans hGoal11_0_2
  | change trunkBranches (trunkCatalog.states 11).context goalSpec11_3_2 = _
    exact (cachedBranches_eq (trunkCatalog.states 11).context goalSpec11_3_2
      endpointInput11_4 endpointInput11_5 (([bc8] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
      (endpointCodes11_4.map decodeEndpoint11) (endpointCodes11_5.map decodeEndpoint11)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint11_4 hEndpoint11_5).trans
      (by decide +kernel)

private abbrev goalSpec11_3_5 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 11) 3))[5-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal11_3_5 : trunkGoalBranches (trunkCatalog.states 11) 3 5 = goalCodes11_3_5.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 11) 3 5 = trunkGoalBranches (trunkCatalog.states 11) 0 5 := by
      apply congrArg (trunkBranches (trunkCatalog.states 11).context)
      decide +kernel
    exact he.trans hGoal11_0_5
  | change trunkBranches (trunkCatalog.states 11).context goalSpec11_3_5 = _
    exact (cachedBranches_eq (trunkCatalog.states 11).context goalSpec11_3_5
      endpointInput11_6 endpointInput11_7 (([bc9] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
      (endpointCodes11_6.map decodeEndpoint11) (endpointCodes11_7.map decodeEndpoint11)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint11_6 hEndpoint11_7).trans
      (by decide +kernel)

private abbrev goalSpec11_3_7 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 11) 3))[7-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal11_3_7 : trunkGoalBranches (trunkCatalog.states 11) 3 7 = goalCodes11_3_7.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 11).context goalSpec11_3_7 = _
  exact (cachedBranches_eq (trunkCatalog.states 11).context goalSpec11_3_7
    endpointInput11_25 endpointInput11_26 (([bc2] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes11_25.map decodeEndpoint11) (endpointCodes11_26.map decodeEndpoint11)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint11_25 hEndpoint11_26).trans
    (by decide +kernel)

private abbrev goalSpec11_3_9 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 11) 3))[9-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal11_3_9 : trunkGoalBranches (trunkCatalog.states 11) 3 9 = goalCodes11_3_9.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 11).context goalSpec11_3_9 = _
  exact (cachedBranches_eq (trunkCatalog.states 11).context goalSpec11_3_9
    endpointInput11_27 endpointInput11_28 (([bc5] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes11_27.map decodeEndpoint11) (endpointCodes11_28.map decodeEndpoint11)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint11_27 hEndpoint11_28).trans
    (by decide +kernel)

private abbrev goalSpec11_3_12 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 11) 3))[12-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal11_3_12 : trunkGoalBranches (trunkCatalog.states 11) 3 12 = goalCodes11_3_12.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 11).context goalSpec11_3_12 = _
  exact (cachedBranches_eq (trunkCatalog.states 11).context goalSpec11_3_12
    endpointInput11_29 endpointInput11_30 (([bc46] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes11_29.map decodeEndpoint11) (endpointCodes11_30.map decodeEndpoint11)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint11_29 hEndpoint11_30).trans
    (by decide +kernel)

private abbrev goalSpec11_3_14 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 11) 3))[14-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal11_3_14 : trunkGoalBranches (trunkCatalog.states 11) 3 14 = goalCodes11_3_14.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 11).context goalSpec11_3_14 = _
  exact (cachedBranches_eq (trunkCatalog.states 11).context goalSpec11_3_14
    endpointInput11_31 endpointInput11_32 (([bc49] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes11_31.map decodeEndpoint11) (endpointCodes11_32.map decodeEndpoint11)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint11_31 hEndpoint11_32).trans
    (by decide +kernel)

private abbrev goalSpec11_3_17 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 11) 3))[17-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal11_3_17 : trunkGoalBranches (trunkCatalog.states 11) 3 17 = goalCodes11_3_17.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 11) 3 17 = trunkGoalBranches (trunkCatalog.states 11) 2 12 := by
      apply congrArg (trunkBranches (trunkCatalog.states 11).context)
      decide +kernel
    exact he.trans hGoal11_2_12
  | change trunkBranches (trunkCatalog.states 11).context goalSpec11_3_17 = _
    exact (cachedBranches_eq (trunkCatalog.states 11).context goalSpec11_3_17
      endpointInput11_17 endpointInput11_18 (([bc171] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
      (endpointCodes11_17.map decodeEndpoint11) (endpointCodes11_18.map decodeEndpoint11)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint11_17 hEndpoint11_18).trans
      (by decide +kernel)

private abbrev goalSpec11_3_19 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 11) 3))[19-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal11_3_19 : trunkGoalBranches (trunkCatalog.states 11) 3 19 = goalCodes11_3_19.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 11) 3 19 = trunkGoalBranches (trunkCatalog.states 11) 2 14 := by
      apply congrArg (trunkBranches (trunkCatalog.states 11).context)
      decide +kernel
    exact he.trans hGoal11_2_14
  | change trunkBranches (trunkCatalog.states 11).context goalSpec11_3_19 = _
    exact (cachedBranches_eq (trunkCatalog.states 11).context goalSpec11_3_19
      endpointInput11_19 endpointInput11_20 (([bc174] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
      (endpointCodes11_19.map decodeEndpoint11) (endpointCodes11_20.map decodeEndpoint11)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint11_19 hEndpoint11_20).trans
      (by decide +kernel)

private abbrev goalSpec11_3_22 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 11) 3))[22-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal11_3_22 : trunkGoalBranches (trunkCatalog.states 11) 3 22 = goalCodes11_3_22.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 11).context goalSpec11_3_22 = _
  exact (cachedBranches_eq (trunkCatalog.states 11).context goalSpec11_3_22
    endpointInput11_33 endpointInput11_34 (([bc177] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes11_33.map decodeEndpoint11) (endpointCodes11_34.map decodeEndpoint11)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint11_33 hEndpoint11_34).trans
    (by decide +kernel)

private abbrev goalSpec11_3_24 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 11) 3))[24-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal11_3_24 : trunkGoalBranches (trunkCatalog.states 11) 3 24 = goalCodes11_3_24.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 11).context goalSpec11_3_24 = _
  exact (cachedBranches_eq (trunkCatalog.states 11).context goalSpec11_3_24
    endpointInput11_35 endpointInput11_36 (([bc180] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes11_35.map decodeEndpoint11) (endpointCodes11_36.map decodeEndpoint11)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint11_35 hEndpoint11_36).trans
    (by decide +kernel)

private abbrev goalSpec11_3_27 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 11) 3))[27-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal11_3_27 : trunkGoalBranches (trunkCatalog.states 11) 3 27 = goalCodes11_3_27.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 11) 3 27 = trunkGoalBranches (trunkCatalog.states 11) 2 17 := by
      apply congrArg (trunkBranches (trunkCatalog.states 11).context)
      decide +kernel
    exact he.trans hGoal11_2_17
  | change trunkBranches (trunkCatalog.states 11).context goalSpec11_3_27 = _
    exact (cachedBranches_eq (trunkCatalog.states 11).context goalSpec11_3_27
      endpointInput11_21 endpointInput11_22 (([bc183] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
      (endpointCodes11_21.map decodeEndpoint11) (endpointCodes11_22.map decodeEndpoint11)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint11_21 hEndpoint11_22).trans
      (by decide +kernel)

private abbrev goalSpec11_3_29 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 11) 3))[29-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal11_3_29 : trunkGoalBranches (trunkCatalog.states 11) 3 29 = goalCodes11_3_29.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 11) 3 29 = trunkGoalBranches (trunkCatalog.states 11) 2 19 := by
      apply congrArg (trunkBranches (trunkCatalog.states 11).context)
      decide +kernel
    exact he.trans hGoal11_2_19
  | change trunkBranches (trunkCatalog.states 11).context goalSpec11_3_29 = _
    exact (cachedBranches_eq (trunkCatalog.states 11).context goalSpec11_3_29
      endpointInput11_23 endpointInput11_24 (([bc184] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
      (endpointCodes11_23.map decodeEndpoint11) (endpointCodes11_24.map decodeEndpoint11)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint11_23 hEndpoint11_24).trans
      (by decide +kernel)

private abbrev goalSpec11_3_32 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 11) 3))[32-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal11_3_32 : trunkGoalBranches (trunkCatalog.states 11) 3 32 = goalCodes11_3_32.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 11).context goalSpec11_3_32 = _
  exact (cachedBranches_eq (trunkCatalog.states 11).context goalSpec11_3_32
    endpointInput11_37 endpointInput11_1 (([] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes11_37.map decodeEndpoint11) (endpointCodes11_1.map decodeEndpoint11)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint11_37 hEndpoint11_1).trans
    (by decide +kernel)

private abbrev goalSpec11_3_34 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 11) 3))[34-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal11_3_34 : trunkGoalBranches (trunkCatalog.states 11) 3 34 = goalCodes11_3_34.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 11).context goalSpec11_3_34 = _
  exact (cachedBranches_eq (trunkCatalog.states 11).context goalSpec11_3_34
    endpointInput11_38 endpointInput11_39 (([] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes11_38.map decodeEndpoint11) (endpointCodes11_39.map decodeEndpoint11)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint11_38 hEndpoint11_39).trans
    (by decide +kernel)

private abbrev goalSpec11_3_35 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 11) 3))[35-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal11_3_35 : trunkGoalBranches (trunkCatalog.states 11) 3 35 = goalCodes11_3_35.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 11).context goalSpec11_3_35 = _
  exact (cachedBranches_eq (trunkCatalog.states 11).context goalSpec11_3_35
    endpointInput11_38 endpointInput11_40 (([] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes11_38.map decodeEndpoint11) (endpointCodes11_40.map decodeEndpoint11)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint11_38 hEndpoint11_40).trans
    (by decide +kernel)

private abbrev goalSpec11_3_36 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 11) 3))[36-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal11_3_36 : trunkGoalBranches (trunkCatalog.states 11) 3 36 = goalCodes11_3_36.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 11).context goalSpec11_3_36 = _
  exact (cachedBranches_eq (trunkCatalog.states 11).context goalSpec11_3_36
    endpointInput11_41 endpointInput11_42 (([] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes11_41.map decodeEndpoint11) (endpointCodes11_42.map decodeEndpoint11)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint11_41 hEndpoint11_42).trans
    (by decide +kernel)

private abbrev goalSpec11_3_38 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 11) 3))[38-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal11_3_38 : trunkGoalBranches (trunkCatalog.states 11) 3 38 = goalCodes11_3_38.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 11).context goalSpec11_3_38 = _
  exact (cachedBranches_eq (trunkCatalog.states 11).context goalSpec11_3_38
    endpointInput11_43 endpointInput11_40 (([] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes11_43.map decodeEndpoint11) (endpointCodes11_40.map decodeEndpoint11)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint11_43 hEndpoint11_40).trans
    (by decide +kernel)

private abbrev goalSpec11_3_39 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 11) 3))[39-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal11_3_39 : trunkGoalBranches (trunkCatalog.states 11) 3 39 = goalCodes11_3_39.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 11).context goalSpec11_3_39 = _
  exact (cachedBranches_eq (trunkCatalog.states 11).context goalSpec11_3_39
    endpointInput11_43 endpointInput11_44 (([] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes11_43.map decodeEndpoint11) (endpointCodes11_44.map decodeEndpoint11)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint11_43 hEndpoint11_44).trans
    (by decide +kernel)

private abbrev goalSpec11_3_40 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 11) 3))[40-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal11_3_40 : trunkGoalBranches (trunkCatalog.states 11) 3 40 = goalCodes11_3_40.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 11).context goalSpec11_3_40 = _
  exact (cachedBranches_eq (trunkCatalog.states 11).context goalSpec11_3_40
    endpointInput11_45 endpointInput11_46 (([] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes11_45.map decodeEndpoint11) (endpointCodes11_46.map decodeEndpoint11)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint11_45 hEndpoint11_46).trans
    (by decide +kernel)

private theorem hGoal11_4_0 : trunkGoalBranches (trunkCatalog.states 11) 4 0 = goalCodes11_4_0.map decodeGoalBranch := by
  exact hGoal11_0_0

private theorem hCut11_0 : (trunkPlanAt (trunkCatalog.states 11) 0).cuts = cutCodes11_0.map decodeThresholdBound := by decide +kernel

private theorem hCut11_1 : (trunkPlanAt (trunkCatalog.states 11) 1).cuts = cutCodes11_1.map decodeThresholdBound := by decide +kernel

private theorem hCut11_2 : (trunkPlanAt (trunkCatalog.states 11) 2).cuts = cutCodes11_2.map decodeThresholdBound := by decide +kernel

private theorem hCut11_3 : (trunkPlanAt (trunkCatalog.states 11) 3).cuts = cutCodes11_3.map decodeThresholdBound := by decide +kernel

private theorem hCut11_4 : (trunkPlanAt (trunkCatalog.states 11) 4).cuts = cutCodes11_4.map decodeThresholdBound := by decide +kernel

private def codedGoals11 (pi goal : ℕ) : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) :=
  if pi = 0 ∧ goal = 0 then goalCodes11_0_0 else
  if pi = 0 ∧ goal = 2 then goalCodes11_0_2 else
  if pi = 0 ∧ goal = 5 then goalCodes11_0_5 else
  if pi = 0 ∧ goal = 7 then goalCodes11_0_7 else
  if pi = 0 ∧ goal = 10 then goalCodes11_0_10 else
  if pi = 0 ∧ goal = 12 then goalCodes11_0_12 else
  if pi = 0 ∧ goal = 15 then goalCodes11_0_15 else
  if pi = 0 ∧ goal = 17 then goalCodes11_0_17 else
  if pi = 0 ∧ goal = 19 then goalCodes11_0_19 else
  if pi = 1 ∧ goal = 0 then goalCodes11_1_0 else
  if pi = 2 ∧ goal = 0 then goalCodes11_2_0 else
  if pi = 2 ∧ goal = 2 then goalCodes11_2_2 else
  if pi = 2 ∧ goal = 5 then goalCodes11_2_5 else
  if pi = 2 ∧ goal = 7 then goalCodes11_2_7 else
  if pi = 2 ∧ goal = 10 then goalCodes11_2_10 else
  if pi = 2 ∧ goal = 12 then goalCodes11_2_12 else
  if pi = 2 ∧ goal = 14 then goalCodes11_2_14 else
  if pi = 2 ∧ goal = 17 then goalCodes11_2_17 else
  if pi = 2 ∧ goal = 19 then goalCodes11_2_19 else
  if pi = 2 ∧ goal = 22 then goalCodes11_2_22 else
  if pi = 3 ∧ goal = 0 then goalCodes11_3_0 else
  if pi = 3 ∧ goal = 2 then goalCodes11_3_2 else
  if pi = 3 ∧ goal = 5 then goalCodes11_3_5 else
  if pi = 3 ∧ goal = 7 then goalCodes11_3_7 else
  if pi = 3 ∧ goal = 9 then goalCodes11_3_9 else
  if pi = 3 ∧ goal = 12 then goalCodes11_3_12 else
  if pi = 3 ∧ goal = 14 then goalCodes11_3_14 else
  if pi = 3 ∧ goal = 17 then goalCodes11_3_17 else
  if pi = 3 ∧ goal = 19 then goalCodes11_3_19 else
  if pi = 3 ∧ goal = 22 then goalCodes11_3_22 else
  if pi = 3 ∧ goal = 24 then goalCodes11_3_24 else
  if pi = 3 ∧ goal = 27 then goalCodes11_3_27 else
  if pi = 3 ∧ goal = 29 then goalCodes11_3_29 else
  if pi = 3 ∧ goal = 32 then goalCodes11_3_32 else
  if pi = 3 ∧ goal = 34 then goalCodes11_3_34 else
  if pi = 3 ∧ goal = 35 then goalCodes11_3_35 else
  if pi = 3 ∧ goal = 36 then goalCodes11_3_36 else
  if pi = 3 ∧ goal = 38 then goalCodes11_3_38 else
  if pi = 3 ∧ goal = 39 then goalCodes11_3_39 else
  if pi = 3 ∧ goal = 40 then goalCodes11_3_40 else
  if pi = 4 ∧ goal = 0 then goalCodes11_4_0 else
  []

private def codedKeys11 : List (ℕ × ℕ) := [(0, 0), (0, 2), (0, 5), (0, 7), (0, 10), (0, 12), (0, 15), (0, 17), (0, 19), (1, 0), (2, 0), (2, 2), (2, 5), (2, 7), (2, 10), (2, 12), (2, 14), (2, 17), (2, 19), (2, 22), (3, 0), (3, 2), (3, 5), (3, 7), (3, 9), (3, 12), (3, 14), (3, 17), (3, 19), (3, 22), (3, 24), (3, 27), (3, 29), (3, 32), (3, 34), (3, 35), (3, 36), (3, 38), (3, 39), (3, 40), (4, 0)]

private theorem hCodedGoals11 (pi goal : ℕ) (hm : (pi,goal) ∈ codedKeys11) : trunkGoalBranches (trunkCatalog.states 11) pi goal = (codedGoals11 pi goal).map decodeGoalBranch := by
  unfold codedGoals11
  by_cases h0 : pi = 0 ∧ goal = 0
  · rw [if_pos h0]
    rcases h0 with ⟨rfl,rfl⟩
    exact hGoal11_0_0
  rw [if_neg h0]
  by_cases h1 : pi = 0 ∧ goal = 2
  · rw [if_pos h1]
    rcases h1 with ⟨rfl,rfl⟩
    exact hGoal11_0_2
  rw [if_neg h1]
  by_cases h2 : pi = 0 ∧ goal = 5
  · rw [if_pos h2]
    rcases h2 with ⟨rfl,rfl⟩
    exact hGoal11_0_5
  rw [if_neg h2]
  by_cases h3 : pi = 0 ∧ goal = 7
  · rw [if_pos h3]
    rcases h3 with ⟨rfl,rfl⟩
    exact hGoal11_0_7
  rw [if_neg h3]
  by_cases h4 : pi = 0 ∧ goal = 10
  · rw [if_pos h4]
    rcases h4 with ⟨rfl,rfl⟩
    exact hGoal11_0_10
  rw [if_neg h4]
  by_cases h5 : pi = 0 ∧ goal = 12
  · rw [if_pos h5]
    rcases h5 with ⟨rfl,rfl⟩
    exact hGoal11_0_12
  rw [if_neg h5]
  by_cases h6 : pi = 0 ∧ goal = 15
  · rw [if_pos h6]
    rcases h6 with ⟨rfl,rfl⟩
    exact hGoal11_0_15
  rw [if_neg h6]
  by_cases h7 : pi = 0 ∧ goal = 17
  · rw [if_pos h7]
    rcases h7 with ⟨rfl,rfl⟩
    exact hGoal11_0_17
  rw [if_neg h7]
  by_cases h8 : pi = 0 ∧ goal = 19
  · rw [if_pos h8]
    rcases h8 with ⟨rfl,rfl⟩
    exact hGoal11_0_19
  rw [if_neg h8]
  by_cases h9 : pi = 1 ∧ goal = 0
  · rw [if_pos h9]
    rcases h9 with ⟨rfl,rfl⟩
    exact hGoal11_1_0
  rw [if_neg h9]
  by_cases h10 : pi = 2 ∧ goal = 0
  · rw [if_pos h10]
    rcases h10 with ⟨rfl,rfl⟩
    exact hGoal11_2_0
  rw [if_neg h10]
  by_cases h11 : pi = 2 ∧ goal = 2
  · rw [if_pos h11]
    rcases h11 with ⟨rfl,rfl⟩
    exact hGoal11_2_2
  rw [if_neg h11]
  by_cases h12 : pi = 2 ∧ goal = 5
  · rw [if_pos h12]
    rcases h12 with ⟨rfl,rfl⟩
    exact hGoal11_2_5
  rw [if_neg h12]
  by_cases h13 : pi = 2 ∧ goal = 7
  · rw [if_pos h13]
    rcases h13 with ⟨rfl,rfl⟩
    exact hGoal11_2_7
  rw [if_neg h13]
  by_cases h14 : pi = 2 ∧ goal = 10
  · rw [if_pos h14]
    rcases h14 with ⟨rfl,rfl⟩
    exact hGoal11_2_10
  rw [if_neg h14]
  by_cases h15 : pi = 2 ∧ goal = 12
  · rw [if_pos h15]
    rcases h15 with ⟨rfl,rfl⟩
    exact hGoal11_2_12
  rw [if_neg h15]
  by_cases h16 : pi = 2 ∧ goal = 14
  · rw [if_pos h16]
    rcases h16 with ⟨rfl,rfl⟩
    exact hGoal11_2_14
  rw [if_neg h16]
  by_cases h17 : pi = 2 ∧ goal = 17
  · rw [if_pos h17]
    rcases h17 with ⟨rfl,rfl⟩
    exact hGoal11_2_17
  rw [if_neg h17]
  by_cases h18 : pi = 2 ∧ goal = 19
  · rw [if_pos h18]
    rcases h18 with ⟨rfl,rfl⟩
    exact hGoal11_2_19
  rw [if_neg h18]
  by_cases h19 : pi = 2 ∧ goal = 22
  · rw [if_pos h19]
    rcases h19 with ⟨rfl,rfl⟩
    exact hGoal11_2_22
  rw [if_neg h19]
  by_cases h20 : pi = 3 ∧ goal = 0
  · rw [if_pos h20]
    rcases h20 with ⟨rfl,rfl⟩
    exact hGoal11_3_0
  rw [if_neg h20]
  by_cases h21 : pi = 3 ∧ goal = 2
  · rw [if_pos h21]
    rcases h21 with ⟨rfl,rfl⟩
    exact hGoal11_3_2
  rw [if_neg h21]
  by_cases h22 : pi = 3 ∧ goal = 5
  · rw [if_pos h22]
    rcases h22 with ⟨rfl,rfl⟩
    exact hGoal11_3_5
  rw [if_neg h22]
  by_cases h23 : pi = 3 ∧ goal = 7
  · rw [if_pos h23]
    rcases h23 with ⟨rfl,rfl⟩
    exact hGoal11_3_7
  rw [if_neg h23]
  by_cases h24 : pi = 3 ∧ goal = 9
  · rw [if_pos h24]
    rcases h24 with ⟨rfl,rfl⟩
    exact hGoal11_3_9
  rw [if_neg h24]
  by_cases h25 : pi = 3 ∧ goal = 12
  · rw [if_pos h25]
    rcases h25 with ⟨rfl,rfl⟩
    exact hGoal11_3_12
  rw [if_neg h25]
  by_cases h26 : pi = 3 ∧ goal = 14
  · rw [if_pos h26]
    rcases h26 with ⟨rfl,rfl⟩
    exact hGoal11_3_14
  rw [if_neg h26]
  by_cases h27 : pi = 3 ∧ goal = 17
  · rw [if_pos h27]
    rcases h27 with ⟨rfl,rfl⟩
    exact hGoal11_3_17
  rw [if_neg h27]
  by_cases h28 : pi = 3 ∧ goal = 19
  · rw [if_pos h28]
    rcases h28 with ⟨rfl,rfl⟩
    exact hGoal11_3_19
  rw [if_neg h28]
  by_cases h29 : pi = 3 ∧ goal = 22
  · rw [if_pos h29]
    rcases h29 with ⟨rfl,rfl⟩
    exact hGoal11_3_22
  rw [if_neg h29]
  by_cases h30 : pi = 3 ∧ goal = 24
  · rw [if_pos h30]
    rcases h30 with ⟨rfl,rfl⟩
    exact hGoal11_3_24
  rw [if_neg h30]
  by_cases h31 : pi = 3 ∧ goal = 27
  · rw [if_pos h31]
    rcases h31 with ⟨rfl,rfl⟩
    exact hGoal11_3_27
  rw [if_neg h31]
  by_cases h32 : pi = 3 ∧ goal = 29
  · rw [if_pos h32]
    rcases h32 with ⟨rfl,rfl⟩
    exact hGoal11_3_29
  rw [if_neg h32]
  by_cases h33 : pi = 3 ∧ goal = 32
  · rw [if_pos h33]
    rcases h33 with ⟨rfl,rfl⟩
    exact hGoal11_3_32
  rw [if_neg h33]
  by_cases h34 : pi = 3 ∧ goal = 34
  · rw [if_pos h34]
    rcases h34 with ⟨rfl,rfl⟩
    exact hGoal11_3_34
  rw [if_neg h34]
  by_cases h35 : pi = 3 ∧ goal = 35
  · rw [if_pos h35]
    rcases h35 with ⟨rfl,rfl⟩
    exact hGoal11_3_35
  rw [if_neg h35]
  by_cases h36 : pi = 3 ∧ goal = 36
  · rw [if_pos h36]
    rcases h36 with ⟨rfl,rfl⟩
    exact hGoal11_3_36
  rw [if_neg h36]
  by_cases h37 : pi = 3 ∧ goal = 38
  · rw [if_pos h37]
    rcases h37 with ⟨rfl,rfl⟩
    exact hGoal11_3_38
  rw [if_neg h37]
  by_cases h38 : pi = 3 ∧ goal = 39
  · rw [if_pos h38]
    rcases h38 with ⟨rfl,rfl⟩
    exact hGoal11_3_39
  rw [if_neg h38]
  by_cases h39 : pi = 3 ∧ goal = 40
  · rw [if_pos h39]
    rcases h39 with ⟨rfl,rfl⟩
    exact hGoal11_3_40
  rw [if_neg h39]
  by_cases h40 : pi = 4 ∧ goal = 0
  · rw [if_pos h40]
    rcases h40 with ⟨rfl,rfl⟩
    exact hGoal11_4_0
  rw [if_neg h40]
  simp_all only [codedKeys11,List.mem_cons,List.mem_nil_iff,or_false,Prod.mk.injEq]

private def codedCuts11 (pi : ℕ) : List (ℕ × Bool × Bool) :=
  if pi = 0 then cutCodes11_0 else
  if pi = 1 then cutCodes11_1 else
  if pi = 2 then cutCodes11_2 else
  if pi = 3 then cutCodes11_3 else
  if pi = 4 then cutCodes11_4 else
  []

private theorem hCodedCuts11 (pi goal : ℕ) (hm : (pi,goal) ∈ codedKeys11) : (trunkPlanAt (trunkCatalog.states 11) pi).cuts = (codedCuts11 pi).map decodeThresholdBound := by
  unfold codedCuts11
  by_cases h0 : pi = 0
  · rw [if_pos h0]
    subst pi
    exact hCut11_0
  rw [if_neg h0]
  by_cases h1 : pi = 1
  · rw [if_pos h1]
    subst pi
    exact hCut11_1
  rw [if_neg h1]
  by_cases h2 : pi = 2
  · rw [if_pos h2]
    subst pi
    exact hCut11_2
  rw [if_neg h2]
  by_cases h3 : pi = 3
  · rw [if_pos h3]
    subst pi
    exact hCut11_3
  rw [if_neg h3]
  by_cases h4 : pi = 4
  · rw [if_pos h4]
    subst pi
    exact hCut11_4
  rw [if_neg h4]
  simp_all only [codedKeys11,List.mem_cons,List.mem_nil_iff,or_false,Prod.mk.injEq,false_and]

private def codedValid11 (g : TrunkGroup) : Prop := (g.plan,g.goal) ∈ codedKeys11 ∧ codeGroupValid (trunkCatalog.states 11) codedParents11 codedCuts11 codedGoals11 g

private theorem codedValid11_sound (g : TrunkGroup) (h : codedValid11 g) : trunkGroupValid trunkCatalog 11 g :=
  codeGroupValid_sound 11 codedParents11 codedCuts11 codedGoals11 g hCodedParents11 (hCodedCuts11 g.plan g.goal h.1) (hCodedGoals11 g.plan g.goal h.1) h.2



set_option Elab.async false
theorem batch_chunk_0 : ∀ j ∈ List.range 20, codedValid11 (trunkStateData11Part01.getD j ⟨0,[],0,[]⟩) := by
  unfold codedValid11 codeGroupValid
  decide +kernel

theorem batch_chunk_20 : ∀ j ∈ List.range' 20 20, codedValid11 (trunkStateData11Part01.getD j ⟨0,[],0,[]⟩) := by
  unfold codedValid11 codeGroupValid
  decide +kernel

theorem batch_chunk_40 : ∀ j ∈ List.range' 40 20, codedValid11 (trunkStateData11Part01.getD j ⟨0,[],0,[]⟩) := by
  unfold codedValid11 codeGroupValid
  decide +kernel

theorem batch_chunk_60 : ∀ j ∈ List.range' 60 20, codedValid11 (trunkStateData11Part01.getD j ⟨0,[],0,[]⟩) := by
  unfold codedValid11 codeGroupValid
  decide +kernel

theorem batch_chunk_80 : ∀ j ∈ List.range' 80 20, codedValid11 (trunkStateData11Part01.getD j ⟨0,[],0,[]⟩) := by
  unfold codedValid11 codeGroupValid
  decide +kernel

theorem batch_key (j : ℕ) (hj : j < 100) : codedValid11 (trunkStateData11Part01.getD j ⟨0,[],0,[]⟩) := by
  rcases lt_or_ge j 20 with h0 | h0
  · exact batch_chunk_0 j (List.mem_range.2 (by omega))
  rcases lt_or_ge j 40 with h1 | h1
  · exact batch_chunk_20 j (List.mem_range'.2 ⟨j - 20, by omega, by omega⟩)
  rcases lt_or_ge j 60 with h2 | h2
  · exact batch_chunk_40 j (List.mem_range'.2 ⟨j - 40, by omega, by omega⟩)
  rcases lt_or_ge j 80 with h3 | h3
  · exact batch_chunk_60 j (List.mem_range'.2 ⟨j - 60, by omega, by omega⟩)
  · exact batch_chunk_80 j (List.mem_range'.2 ⟨j - 80, by omega, by omega⟩)

theorem part_length_1 : trunkStateData11Part01.length = 100 := by decide +kernel

theorem solution : trunkBindingBatch 11 0 100 := by
  intro i hlo hhi g hg
  change (trunkStateData11Part01 ++ trunkStateData11Part02)[i]? = some g at hg
  rw [List.getElem?_append_left (show i < (trunkStateData11Part01).length by simp only [List.length_append, part_length_1, Nat.reduceAdd]; omega)] at hg
  have hgi := batch_key (i - 0) (by omega)
  have hgv : trunkStateData11Part01.getD (i - 0) ⟨0,[],0,[]⟩ = g := by
    try simp only [Nat.sub_zero]
    rw [List.getD_eq_getElem?_getD, hg]; rfl
  rw [hgv] at hgi
  exact codedValid11_sound g hgi

#print axioms solution
