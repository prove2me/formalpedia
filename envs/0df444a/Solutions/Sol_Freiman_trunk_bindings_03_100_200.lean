-- Prove2me | solution 1 for Freiman.trunk_bindings_03_100_200
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:23:07.743238+00:00
-- url     : https://prove2.me/submissions/619b0f87-ca8a-46db-8010-9c2c6674a770

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
private abbrev bc9 : ℕ × Bool × Bool := (10, true, true)
private abbrev bc10 : ℕ × Bool × Bool := (18, false, false)
private abbrev bc11 : ℕ × Bool × Bool := (17, false, true)
private abbrev bc12 : ℕ × Bool × Bool := (17, true, false)
private abbrev bc13 : ℕ × Bool × Bool := (18, true, true)
private abbrev bc14 : ℕ × Bool × Bool := (20, true, true)
private abbrev bc15 : ℕ × Bool × Bool := (20, false, false)
private abbrev bc16 : ℕ × Bool × Bool := (4, false, false)
private abbrev bc17 : ℕ × Bool × Bool := (4, true, true)
private abbrev bc18 : ℕ × Bool × Bool := (50, false, true)
private abbrev bc19 : ℕ × Bool × Bool := (51, false, true)
private abbrev bc20 : ℕ × Bool × Bool := (51, true, false)
private abbrev bc21 : ℕ × Bool × Bool := (50, true, false)
private abbrev bc22 : ℕ × Bool × Bool := (64, true, true)
private abbrev bc23 : ℕ × Bool × Bool := (64, false, false)
private abbrev bc24 : ℕ × Bool × Bool := (18, false, true)
private abbrev bc25 : ℕ × Bool × Bool := (52, false, true)
private abbrev bc26 : ℕ × Bool × Bool := (52, true, false)
private abbrev bc27 : ℕ × Bool × Bool := (18, true, false)
private abbrev bc28 : ℕ × Bool × Bool := (56, true, true)
private abbrev bc29 : ℕ × Bool × Bool := (56, false, false)
private abbrev bc30 : ℕ × Bool × Bool := (89, false, true)
private abbrev bc31 : ℕ × Bool × Bool := (91, false, true)
private abbrev bc32 : ℕ × Bool × Bool := (91, true, false)
private abbrev bc33 : ℕ × Bool × Bool := (89, true, false)
private abbrev bc34 : ℕ × Bool × Bool := (102, true, true)
private abbrev bc35 : ℕ × Bool × Bool := (102, false, false)
private abbrev bc36 : ℕ × Bool × Bool := (30, false, true)
private abbrev bc37 : ℕ × Bool × Bool := (90, false, true)
private abbrev bc38 : ℕ × Bool × Bool := (90, true, false)
private abbrev bc39 : ℕ × Bool × Bool := (30, true, false)
private abbrev bc40 : ℕ × Bool × Bool := (95, true, true)
private abbrev bc41 : ℕ × Bool × Bool := (95, false, false)
private abbrev bc42 : ℕ × Bool × Bool := (8, false, false)
private abbrev bc43 : ℕ × Bool × Bool := (8, true, true)
private abbrev bc44 : ℕ × Bool × Bool := (380, false, false)
private abbrev bc45 : ℕ × Bool × Bool := (379, false, false)
private abbrev bc46 : ℕ × Bool × Bool := (377, false, true)
private abbrev bc47 : ℕ × Bool × Bool := (377, true, false)
private abbrev bc48 : ℕ × Bool × Bool := (379, true, true)
private abbrev bc49 : ℕ × Bool × Bool := (395, true, true)
private abbrev bc50 : ℕ × Bool × Bool := (395, false, false)
private abbrev bc51 : ℕ × Bool × Bool := (380, true, true)
private abbrev bc52 : ℕ × Bool × Bool := (381, false, false)
private abbrev bc53 : ℕ × Bool × Bool := (381, true, true)
private abbrev bc54 : ℕ × Bool × Bool := (384, false, false)
private abbrev bc55 : ℕ × Bool × Bool := (383, false, true)
private abbrev bc56 : ℕ × Bool × Bool := (383, true, false)
private abbrev bc57 : ℕ × Bool × Bool := (384, true, true)
private abbrev bc58 : ℕ × Bool × Bool := (388, true, true)
private abbrev bc59 : ℕ × Bool × Bool := (388, false, false)
private abbrev bc60 : ℕ × Bool × Bool := (405, false, true)
private abbrev bc61 : ℕ × Bool × Bool := (405, true, false)
private abbrev bc62 : ℕ × Bool × Bool := (415, false, true)
private abbrev bc63 : ℕ × Bool × Bool := (414, false, true)
private abbrev bc64 : ℕ × Bool × Bool := (414, true, false)
private abbrev bc65 : ℕ × Bool × Bool := (415, true, false)
private abbrev bc66 : ℕ × Bool × Bool := (421, true, true)
private abbrev bc67 : ℕ × Bool × Bool := (421, false, false)
private abbrev bc68 : ℕ × Bool × Bool := (404, false, true)
private abbrev bc69 : ℕ × Bool × Bool := (406, false, true)
private abbrev bc70 : ℕ × Bool × Bool := (403, false, true)
private abbrev bc71 : ℕ × Bool × Bool := (403, true, false)
private abbrev bc72 : ℕ × Bool × Bool := (406, true, false)
private abbrev bc73 : ℕ × Bool × Bool := (409, true, true)
private abbrev bc74 : ℕ × Bool × Bool := (409, false, false)
private abbrev bc75 : ℕ × Bool × Bool := (404, true, false)
private abbrev bc76 : ℕ × Bool × Bool := (183, false, false)
private abbrev bc77 : ℕ × Bool × Bool := (182, false, false)
private abbrev bc78 : ℕ × Bool × Bool := (179, false, true)
private abbrev bc79 : ℕ × Bool × Bool := (179, true, false)
private abbrev bc80 : ℕ × Bool × Bool := (182, true, true)
private abbrev bc81 : ℕ × Bool × Bool := (197, true, true)
private abbrev bc82 : ℕ × Bool × Bool := (197, false, false)
private abbrev bc83 : ℕ × Bool × Bool := (183, true, true)
private abbrev bc84 : ℕ × Bool × Bool := (181, false, false)
private abbrev bc85 : ℕ × Bool × Bool := (181, true, true)
private abbrev bc86 : ℕ × Bool × Bool := (184, false, false)
private abbrev bc87 : ℕ × Bool × Bool := (186, false, true)
private abbrev bc88 : ℕ × Bool × Bool := (186, true, false)
private abbrev bc89 : ℕ × Bool × Bool := (184, true, true)
private abbrev bc90 : ℕ × Bool × Bool := (189, true, true)
private abbrev bc91 : ℕ × Bool × Bool := (189, false, false)
private abbrev bc92 : ℕ × Bool × Bool := (206, true, false)
private abbrev bc93 : ℕ × Bool × Bool := (210, false, true)
private abbrev bc94 : ℕ × Bool × Bool := (210, true, false)
private abbrev bc95 : ℕ × Bool × Bool := (205, false, true)
private abbrev bc96 : ℕ × Bool × Bool := (205, true, false)
private abbrev bc97 : ℕ × Bool × Bool := (297, false, false)
private abbrev bc98 : ℕ × Bool × Bool := (298, false, false)
private abbrev bc99 : ℕ × Bool × Bool := (69, false, true)
private abbrev bc100 : ℕ × Bool × Bool := (69, true, false)
private abbrev bc101 : ℕ × Bool × Bool := (298, true, true)
private abbrev bc102 : ℕ × Bool × Bool := (83, true, true)
private abbrev bc103 : ℕ × Bool × Bool := (83, false, false)
private abbrev bc104 : ℕ × Bool × Bool := (297, true, true)
private abbrev bc105 : ℕ × Bool × Bool := (299, false, false)
private abbrev bc106 : ℕ × Bool × Bool := (299, true, true)
private abbrev bc107 : ℕ × Bool × Bool := (301, false, false)
private abbrev bc108 : ℕ × Bool × Bool := (303, false, true)
private abbrev bc109 : ℕ × Bool × Bool := (303, true, false)
private abbrev bc110 : ℕ × Bool × Bool := (301, true, true)
private abbrev bc111 : ℕ × Bool × Bool := (307, true, true)
private abbrev bc112 : ℕ × Bool × Bool := (307, false, false)
private abbrev bc113 : ℕ × Bool × Bool := (319, false, true)
private abbrev bc114 : ℕ × Bool × Bool := (319, true, false)
private abbrev bc115 : ℕ × Bool × Bool := (331, false, true)
private abbrev bc116 : ℕ × Bool × Bool := (332, false, true)
private abbrev bc117 : ℕ × Bool × Bool := (332, true, false)
private abbrev bc118 : ℕ × Bool × Bool := (331, true, false)
private abbrev bc119 : ℕ × Bool × Bool := (337, true, true)
private abbrev bc120 : ℕ × Bool × Bool := (337, false, false)
private abbrev bc121 : ℕ × Bool × Bool := (320, false, true)
private abbrev bc122 : ℕ × Bool × Bool := (322, false, true)
private abbrev bc123 : ℕ × Bool × Bool := (321, false, true)
private abbrev bc124 : ℕ × Bool × Bool := (321, true, false)
private abbrev bc125 : ℕ × Bool × Bool := (322, true, false)
private abbrev bc126 : ℕ × Bool × Bool := (325, true, true)
private abbrev bc127 : ℕ × Bool × Bool := (325, false, false)
private abbrev bc128 : ℕ × Bool × Bool := (320, true, false)
private abbrev bc129 : ℕ × Bool × Bool := (344, false, false)
private abbrev bc130 : ℕ × Bool × Bool := (343, false, false)
private abbrev bc131 : ℕ × Bool × Bool := (113, false, true)
private abbrev bc132 : ℕ × Bool × Bool := (113, true, false)
private abbrev bc133 : ℕ × Bool × Bool := (343, true, true)
private abbrev bc134 : ℕ × Bool × Bool := (125, true, true)
private abbrev bc135 : ℕ × Bool × Bool := (125, false, false)
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
private abbrev bc171 : ℕ × Bool × Bool := (156, false, false)
private abbrev bc172 : ℕ × Bool × Bool := (155, false, true)
private abbrev bc173 : ℕ × Bool × Bool := (155, true, false)
private abbrev bc174 : ℕ × Bool × Bool := (156, true, true)
private abbrev bc175 : ℕ × Bool × Bool := (162, true, true)
private abbrev bc176 : ℕ × Bool × Bool := (162, false, false)
private abbrev bc177 : ℕ × Bool × Bool := (89, false, false)
private abbrev bc178 : ℕ × Bool × Bool := (476, false, true)
private abbrev bc179 : ℕ × Bool × Bool := (476, true, false)
private abbrev bc180 : ℕ × Bool × Bool := (89, true, true)
private abbrev bc181 : ℕ × Bool × Bool := (479, true, true)
private abbrev bc182 : ℕ × Bool × Bool := (479, false, false)
private abbrev bc183 : ℕ × Bool × Bool := (431, false, false)
private abbrev bc184 : ℕ × Bool × Bool := (490, false, true)
private abbrev bc185 : ℕ × Bool × Bool := (490, true, false)
private abbrev bc186 : ℕ × Bool × Bool := (431, true, true)
private abbrev bc187 : ℕ × Bool × Bool := (497, true, true)
private abbrev bc188 : ℕ × Bool × Bool := (497, false, false)
private abbrev bc189 : ℕ × Bool × Bool := (132, false, false)
private abbrev bc190 : ℕ × Bool × Bool := (132, true, true)
private abbrev bc191 : ℕ × Bool × Bool := (511, false, false)
private abbrev bc192 : ℕ × Bool × Bool := (510, false, true)
private abbrev bc193 : ℕ × Bool × Bool := (510, true, false)
private abbrev bc194 : ℕ × Bool × Bool := (511, true, true)
private abbrev bc195 : ℕ × Bool × Bool := (519, true, true)
private abbrev bc196 : ℕ × Bool × Bool := (519, false, false)
private abbrev bc197 : ℕ × Bool × Bool := (525, false, true)
private abbrev bc198 : ℕ × Bool × Bool := (525, true, false)
private abbrev bc199 : ℕ × Bool × Bool := (23, true, false)
private abbrev bc200 : ℕ × Bool × Bool := (145, true, false)
private abbrev bc201 : ℕ × Bool × Bool := (150, true, false)
private abbrev bc202 : ℕ × Bool × Bool := (53, false, true)
private abbrev bc203 : ℕ × Bool × Bool := (88, false, true)
private abbrev bc204 : ℕ × Bool × Bool := (378, true, true)
private abbrev bc205 : ℕ × Bool × Bool := (402, false, true)
private abbrev bc206 : ℕ × Bool × Bool := (180, true, true)
private abbrev bc207 : ℕ × Bool × Bool := (204, false, true)
private abbrev bc208 : ℕ × Bool × Bool := (300, true, true)
private abbrev bc209 : ℕ × Bool × Bool := (318, false, true)
private abbrev bc210 : ℕ × Bool × Bool := (345, true, true)
private abbrev bc211 : ℕ × Bool × Bool := (364, false, true)
private abbrev bc212 : ℕ × Bool × Bool := (429, true, true)
private abbrev bc213 : ℕ × Bool × Bool := (441, false, true)
private abbrev bc214 : ℕ × Bool × Bool := (467, true, false)
private abbrev bc215 : ℕ × Bool × Bool := (153, true, false)
private abbrev bc216 : ℕ × Bool × Bool := (489, false, false)
private abbrev bc217 : ℕ × Bool × Bool := (365, false, false)
private abbrev bc218 : ℕ × Bool × Bool := (509, true, true)
private abbrev bc219 : ℕ × Bool × Bool := (365, true, true)

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

private def codesA3 : List (List ℕ × Option (Option ℕ)) := [([112911326, 882722351], some (some 626279719)),
 ([112911326, 991976176], some (some 626279719)),
 ([728891584, 60072750, 649066977, 882722351], some (some 626279719)),
 ([728891584, 60072750, 649066977, 991976176], some (some 626279719)),
 ([728891584, 60072750, 595767334, 882722351], some (some 416338889)),
 ([728891584, 60072750, 595767334, 991976176], some (some 416338889)),
 ([728891584, 476573349, 881768834, 882722351], some (some 626279719)),
 ([728891584, 476573349, 881768834, 991976176], some (some 626279719)),
 ([728891584, 476573349, 159503643, 882722351], some (some 753260783)),
 ([728891584, 476573349, 159503643, 991976176], some (some 753260783))]
private def codesB3 : List (List ℕ × Option (Option ℕ)) := [([882722351, 112911326], some none),
 ([882722351, 728891584], some none),
 ([991976176, 466397207, 55717250, 112911326], some none),
 ([991976176, 466397207, 55717250, 728891584], some none),
 ([991976176, 466397207, 649614909, 112911326], some none),
 ([991976176, 466397207, 649614909, 728891584], some none),
 ([991976176, 827878947, 143171926, 112911326], some none),
 ([991976176, 827878947, 143171926, 728891584], some none),
 ([991976176, 827878947, 222803470, 112911326], some none),
 ([991976176, 827878947, 222803470, 728891584], some none)]

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
private def decodeThresholdBound (b : ℕ × Bool × Bool) : CertBound :=
  ⟨b.2.1,b.2.2,(fastBound b.1).threshold⟩
private def decodeGoalBranch (a : List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) : List CertBound × LowerHistoryComparison :=
  (a.1.map decodeThresholdBound, match a.2 with
    | none => .impossible
    | some none => .automatic
    | some (some b) => .bound (decodeThresholdBound b))
private def endpointFields3 : Array CertField := #[⟨(4/13),(1/13),(0/1),(0/1)⟩,⟨(1/2),(1/6),(0/1),(0/1)⟩,⟨(52/73),(1/73),(0/1),(0/1)⟩,⟨(89/214),(1/214),(0/1),(0/1)⟩,⟨(9/13),(-1/13),(0/1),(0/1)⟩,⟨(15/37),(-1/37),(0/1),(0/1)⟩,⟨(22/37),(1/37),(0/1),(0/1)⟩,⟨(113/179),(1/537),(0/1),(0/1)⟩,⟨(17/22),(-1/22),(0/1),(0/1)⟩,⟨(125/214),(-1/214),(0/1),(0/1)⟩,⟨(35/94),(1/94),(0/1),(0/1)⟩,⟨(553/1429),(1/1429),(0/1),(0/1)⟩,⟨(10/23),(-1/69),(0/1),(0/1)⟩,⟨(66/179),(-1/537),(0/1),(0/1)⟩,⟨(16/59),(1/177),(0/1),(0/1)⟩,⟨(767/2749),(1/2749),(0/1),(0/1)⟩,⟨(43/142),(-1/142),(0/1),(0/1)⟩,⟨(5/22),(1/22),(0/1),(0/1)⟩,⟨(42/143),(1/429),(0/1),(0/1)⟩,⟨(271/1006),(-1/1006),(0/1),(0/1)⟩,⟨(517/1249),(-1/1249),(0/1),(0/1)⟩,⟨(731/2497),(-1/2497),(0/1),(0/1)⟩,⟨(101/143),(-1/429),(0/1),(0/1)⟩,⟨(13/23),(1/69),(0/1),(0/1)⟩,⟨(732/1249),(1/1249),(0/1),(0/1)⟩,⟨(59/94),(-1/94),(0/1),(0/1)⟩]
private abbrev endpointInput3_0 : LowerPair × Bool × Bool := (([2], []), true, false)
private def endpointCodes3_0 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((0, 1), [bc0]),
 ((0, 1), [bc1, bc2, bc3]),
 ((0, 2), [bc1, bc2, bc4]),
 ((0, 1), [bc1, bc5, bc6]),
 ((3, 1), [bc1, bc5, bc7])]
private abbrev endpointInput3_1 : LowerPair × Bool × Bool := (([1], []), false, false)
private def endpointCodes3_1 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((4, 5), [bc8]), ((4, 5), [bc9])]
private abbrev endpointInput3_2 : LowerPair × Bool × Bool := (([1], []), true, false)
private def endpointCodes3_2 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((1, 1), [bc8]),
 ((1, 1), [bc9, bc10, bc11]),
 ((1, 2), [bc9, bc10, bc12]),
 ((1, 1), [bc9, bc13, bc14]),
 ((2, 1), [bc9, bc13, bc15])]
private abbrev endpointInput3_3 : LowerPair × Bool × Bool := (([2], []), false, false)
private def endpointCodes3_3 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((5, 5), [bc0]), ((5, 5), [bc1])]
private abbrev endpointInput3_4 : LowerPair × Bool × Bool := (([1, 1], []), true, false)
private def endpointCodes3_4 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((6, 1), [bc16, (33, false, true)]),
 ((6, 2), [bc16, (33, true, false)]),
 ((6, 1), [bc17, (45, true, true)]),
 ((7, 1), [bc17, (45, false, false)])]
private abbrev endpointInput3_5 : LowerPair × Bool × Bool := (([1, 2], []), false, false)
private def endpointCodes3_5 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((8, 5), [])]
private abbrev endpointInput3_6 : LowerPair × Bool × Bool := (([1], [2]), true, true)
private def endpointCodes3_6 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((1, 0), [bc18, bc19]),
 ((1, 3), [bc18, bc20]),
 ((1, 0), [bc21, bc22]),
 ((2, 0), [bc21, bc23])]
private abbrev endpointInput3_7 : LowerPair × Bool × Bool := (([1], [1]), false, true)
private def endpointCodes3_7 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((4, 4), [bc24, bc25]),
 ((4, 9), [bc24, bc26]),
 ((4, 4), [bc27, bc28]),
 ((9, 4), [bc27, bc29])]
private abbrev endpointInput3_10 : LowerPair × Bool × Bool := (([2], [2]), true, true)
private def endpointCodes3_10 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((0, 0), [bc30, bc31]),
 ((0, 3), [bc30, bc32]),
 ((0, 0), [bc33, bc34]),
 ((3, 0), [bc33, bc35])]
private abbrev endpointInput3_11 : LowerPair × Bool × Bool := (([2], [1]), false, true)
private def endpointCodes3_11 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((5, 4), [bc36, bc37]),
 ((5, 9), [bc36, bc38]),
 ((5, 4), [bc39, bc40]),
 ((13, 4), [bc39, bc41])]
private abbrev endpointInput3_17 : LowerPair × Bool × Bool := (([], []), true, false)
private def endpointCodes3_17 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((1, 1), [bc42, bc11]),
 ((1, 2), [bc42, bc12]),
 ((1, 1), [bc43, bc14]),
 ((2, 1), [bc43, bc15])]
private abbrev endpointInput3_18 : LowerPair × Bool × Bool := (([2, 1], [2]), true, false)
private def endpointCodes3_18 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((10, 0), [bc44, bc45, bc46]),
 ((10, 3), [bc44, bc45, bc47]),
 ((10, 0), [bc44, bc48, bc49]),
 ((11, 0), [bc44, bc48, bc50]),
 ((10, 0), [bc51])]
private abbrev endpointInput3_19 : LowerPair × Bool × Bool := (([2, 2], [2]), false, false)
private def endpointCodes3_19 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((12, 5), [bc52]),
 ((12, 5), [bc53, bc54, bc55]),
 ((12, 13), [bc53, bc54, bc56]),
 ((12, 5), [bc53, bc57, bc58]),
 ((20, 5), [bc53, bc57, bc59])]
private abbrev endpointInput3_20 : LowerPair × Bool × Bool := (([2], [2, 1]), true, true)
private def endpointCodes3_20 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((0, 10), [bc60]),
 ((0, 10), [bc61, bc62, bc63]),
 ((0, 11), [bc61, bc62, bc64]),
 ((0, 10), [bc61, bc65, bc66]),
 ((3, 10), [bc61, bc65, bc67])]
private abbrev endpointInput3_21 : LowerPair × Bool × Bool := (([2], [2, 2]), false, true)
private def endpointCodes3_21 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((5, 12), [bc68, bc69, bc70]),
 ((5, 20), [bc68, bc69, bc71]),
 ((5, 12), [bc68, bc72, bc73]),
 ((13, 12), [bc68, bc72, bc74]),
 ((5, 12), [bc75])]
private abbrev endpointInput3_22 : LowerPair × Bool × Bool := (([3, 1], [2]), true, false)
private def endpointCodes3_22 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((14, 0), [bc76, bc77, bc78]),
 ((14, 3), [bc76, bc77, bc79]),
 ((14, 0), [bc76, bc80, bc81]),
 ((15, 0), [bc76, bc80, bc82]),
 ((14, 0), [bc83])]
private abbrev endpointInput3_23 : LowerPair × Bool × Bool := (([3, 2], [2]), false, false)
private def endpointCodes3_23 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((16, 5), [bc84]),
 ((16, 5), [bc85, bc86, bc87]),
 ((16, 13), [bc85, bc86, bc88]),
 ((16, 5), [bc85, bc89, bc90]),
 ((21, 5), [bc85, bc89, bc91])]
private abbrev endpointInput3_24 : LowerPair × Bool × Bool := (([3], [2, 1]), true, true)
private def endpointCodes3_24 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((17, 10), [(206, false, true)]),
 ((17, 10), [bc92, bc93, (208, false, true)]),
 ((17, 11), [bc92, bc93, (208, true, false)]),
 ((17, 10), [bc92, bc94, (213, true, true)]),
 ((18, 10), [bc92, bc94, (213, false, false)])]
private abbrev endpointInput3_25 : LowerPair × Bool × Bool := (([3], [2, 2]), false, true)
private def endpointCodes3_25 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((19, 12), [bc95]), ((19, 12), [bc96])]
private abbrev endpointInput3_26 : LowerPair × Bool × Bool := (([2, 1], [1]), true, false)
private def endpointCodes3_26 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((10, 1), [bc97, bc98, bc99]),
 ((10, 2), [bc97, bc98, bc100]),
 ((10, 1), [bc97, bc101, bc102]),
 ((11, 1), [bc97, bc101, bc103]),
 ((10, 1), [bc104])]
private abbrev endpointInput3_27 : LowerPair × Bool × Bool := (([2, 2], [1]), false, false)
private def endpointCodes3_27 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((12, 4), [bc105]),
 ((12, 4), [bc106, bc107, bc108]),
 ((12, 9), [bc106, bc107, bc109]),
 ((12, 4), [bc106, bc110, bc111]),
 ((20, 4), [bc106, bc110, bc112])]
private abbrev endpointInput3_28 : LowerPair × Bool × Bool := (([2], [1, 1]), true, true)
private def endpointCodes3_28 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((0, 6), [bc113]),
 ((0, 6), [bc114, bc115, bc116]),
 ((0, 7), [bc114, bc115, bc117]),
 ((0, 6), [bc114, bc118, bc119]),
 ((3, 6), [bc114, bc118, bc120])]
private abbrev endpointInput3_29 : LowerPair × Bool × Bool := (([2], [1, 2]), false, true)
private def endpointCodes3_29 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((5, 8), [bc121, bc122, bc123]),
 ((5, 22), [bc121, bc122, bc124]),
 ((5, 8), [bc121, bc125, bc126]),
 ((13, 8), [bc121, bc125, bc127]),
 ((5, 8), [bc128])]
private abbrev endpointInput3_30 : LowerPair × Bool × Bool := (([3, 1], [1]), true, false)
private def endpointCodes3_30 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((14, 1), [bc129, bc130, bc131]),
 ((14, 2), [bc129, bc130, bc132]),
 ((14, 1), [bc129, bc133, bc134]),
 ((15, 1), [bc129, bc133, bc135]),
 ((14, 1), [bc136])]
private abbrev endpointInput3_31 : LowerPair × Bool × Bool := (([3, 2], [1]), false, false)
private def endpointCodes3_31 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((16, 4), [bc137]),
 ((16, 4), [bc138, bc139, bc140]),
 ((16, 9), [bc138, bc139, bc141]),
 ((16, 4), [bc138, bc142, bc143]),
 ((21, 4), [bc138, bc142, bc144])]
private abbrev endpointInput3_32 : LowerPair × Bool × Bool := (([3], [1, 1]), true, true)
private def endpointCodes3_32 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((17, 6), [(365, false, true)]),
 ((17, 6), [bc145, bc146, (370, false, true)]),
 ((17, 7), [bc145, bc146, (370, true, false)]),
 ((17, 6), [bc145, bc147, (373, true, true)]),
 ((18, 6), [bc145, bc147, (373, false, false)])]
private abbrev endpointInput3_33 : LowerPair × Bool × Bool := (([3], [1, 2]), false, true)
private def endpointCodes3_33 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((19, 8), [bc148]), ((19, 8), [bc149])]
private abbrev endpointInput3_34 : LowerPair × Bool × Bool := (([2, 1], [3]), true, false)
private def endpointCodes3_34 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((10, 17), [bc150, bc151, (427, false, true)]),
 ((10, 18), [bc150, bc151, (427, true, false)]),
 ((10, 17), [bc150, bc152, (436, true, true)]),
 ((11, 17), [bc150, bc152, (436, false, false)]),
 ((10, 17), [(432, true, true)])]
private abbrev endpointInput3_35 : LowerPair × Bool × Bool := (([2, 2], [3]), false, false)
private def endpointCodes3_35 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((12, 19), [bc153]), ((12, 19), [bc154])]
private abbrev endpointInput3_36 : LowerPair × Bool × Bool := (([2], [3, 1]), true, true)
private def endpointCodes3_36 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((0, 14), [bc155]),
 ((0, 14), [bc156, bc157, bc158]),
 ((0, 15), [bc156, bc157, bc159]),
 ((0, 14), [bc156, bc160, bc161]),
 ((3, 14), [bc156, bc160, bc162])]
private abbrev endpointInput3_37 : LowerPair × Bool × Bool := (([2], [3, 2]), false, true)
private def endpointCodes3_37 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((5, 16), [bc163, bc164, bc165]),
 ((5, 21), [bc163, bc164, bc166]),
 ((5, 16), [bc163, bc167, bc168]),
 ((13, 16), [bc163, bc167, bc169]),
 ((5, 16), [bc170])]
private abbrev endpointInput3_38 : LowerPair × Bool × Bool := (([2], [1]), true, false)
private def endpointCodes3_38 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((0, 1), [bc2, bc3]),
 ((0, 2), [bc2, bc4]),
 ((0, 1), [bc5, bc6]),
 ((3, 1), [bc5, bc7])]
private abbrev endpointInput3_39 : LowerPair × Bool × Bool := (([3], [1]), true, false)
private def endpointCodes3_39 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((17, 1), [bc171, bc172]),
 ((17, 2), [bc171, bc173]),
 ((17, 1), [bc174, bc175]),
 ((18, 1), [bc174, bc176])]
private abbrev endpointInput3_40 : LowerPair × Bool × Bool := (([2], [1]), false, false)
private def endpointCodes3_40 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((5, 4), [bc2, bc37]),
 ((5, 9), [bc2, bc38]),
 ((5, 4), [bc5, bc40]),
 ((13, 4), [bc5, bc41])]
private abbrev endpointInput3_41 : LowerPair × Bool × Bool := (([2], [2]), false, false)
private def endpointCodes3_41 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((5, 5), [bc177, bc178]),
 ((5, 13), [bc177, bc179]),
 ((5, 5), [bc180, bc181]),
 ((13, 5), [bc180, bc182])]
private abbrev endpointInput3_42 : LowerPair × Bool × Bool := (([2], [2]), true, false)
private def endpointCodes3_42 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((0, 0), [bc177, bc31]),
 ((0, 3), [bc177, bc32]),
 ((0, 0), [bc180, bc34]),
 ((3, 0), [bc180, bc35])]
private abbrev endpointInput3_43 : LowerPair × Bool × Bool := (([3], [1]), false, false)
private def endpointCodes3_43 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((19, 4), [])]
private abbrev endpointInput3_44 : LowerPair × Bool × Bool := (([2], [3]), true, false)
private def endpointCodes3_44 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((0, 17), [bc183, bc184]),
 ((0, 18), [bc183, bc185]),
 ((0, 17), [bc186, bc187]),
 ((3, 17), [bc186, bc188])]
private abbrev endpointInput3_45 : LowerPair × Bool × Bool := (([3], [2]), false, false)
private def endpointCodes3_45 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((19, 5), [])]
private abbrev endpointInput3_46 : LowerPair × Bool × Bool := (([3], [2]), true, false)
private def endpointCodes3_46 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((17, 0), [bc189, (133, false, true)]),
 ((17, 3), [bc189, (133, true, false)]),
 ((17, 0), [bc190, (136, true, true)]),
 ((18, 0), [bc190, (136, false, false)])]
private abbrev endpointInput3_47 : LowerPair × Bool × Bool := (([2], [3]), false, false)
private def endpointCodes3_47 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((5, 19), [])]
private abbrev endpointInput3_48 : LowerPair × Bool × Bool := (([3, 1], [1, 1]), true, false)
private def endpointCodes3_48 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((14, 6), [bc191, bc192]),
 ((14, 7), [bc191, bc193]),
 ((14, 6), [bc194, bc195]),
 ((15, 6), [bc194, bc196])]
private abbrev endpointInput3_49 : LowerPair × Bool × Bool := (([3, 2], [1, 1]), false, false)
private def endpointCodes3_49 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((16, 4), [bc139, bc140]),
 ((16, 9), [bc139, bc141]),
 ((16, 4), [bc142, bc143]),
 ((21, 4), [bc142, bc144])]
private abbrev endpointInput3_50 : LowerPair × Bool × Bool := (([3], [1, 1, 2]), true, true)
private def endpointCodes3_50 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((17, 23), [bc197, (526, false, true)]),
 ((17, 24), [bc197, (526, true, false)]),
 ((17, 23), [bc198, (529, true, true)]),
 ((18, 23), [bc198, (529, false, false)])]
private abbrev endpointInput3_51 : LowerPair × Bool × Bool := (([3], [1, 1, 1]), false, true)
private def endpointCodes3_51 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((19, 25), [])]

private def decodeEndpoint3 (x : (ℕ × ℕ) × List (ℕ × Bool × Bool)) : LowerHistoryEndCase :=
  ((endpointFields3[x.1.1]?.getD ⟨0,0,0,0⟩,endpointFields3[x.1.2]?.getD ⟨0,0,0,0⟩),x.2.map decodeThresholdBound)

private theorem hEndpoint3_0 :
    trunkEndpointCases (trunkCatalog.states 3).context endpointInput3_0.1 endpointInput3_0.2.1 endpointInput3_0.2.2 = endpointCodes3_0.map decodeEndpoint3 := by decide +kernel

private theorem hEndpoint3_1 :
    trunkEndpointCases (trunkCatalog.states 3).context endpointInput3_1.1 endpointInput3_1.2.1 endpointInput3_1.2.2 = endpointCodes3_1.map decodeEndpoint3 := by decide +kernel

private theorem hEndpoint3_2 :
    trunkEndpointCases (trunkCatalog.states 3).context endpointInput3_2.1 endpointInput3_2.2.1 endpointInput3_2.2.2 = endpointCodes3_2.map decodeEndpoint3 := by decide +kernel

private theorem hEndpoint3_3 :
    trunkEndpointCases (trunkCatalog.states 3).context endpointInput3_3.1 endpointInput3_3.2.1 endpointInput3_3.2.2 = endpointCodes3_3.map decodeEndpoint3 := by decide +kernel

private theorem hEndpoint3_4 :
    trunkEndpointCases (trunkCatalog.states 3).context endpointInput3_4.1 endpointInput3_4.2.1 endpointInput3_4.2.2 = endpointCodes3_4.map decodeEndpoint3 := by decide +kernel

private theorem hEndpoint3_5 :
    trunkEndpointCases (trunkCatalog.states 3).context endpointInput3_5.1 endpointInput3_5.2.1 endpointInput3_5.2.2 = endpointCodes3_5.map decodeEndpoint3 := by decide +kernel

private theorem hEndpoint3_6 :
    trunkEndpointCases (trunkCatalog.states 3).context endpointInput3_6.1 endpointInput3_6.2.1 endpointInput3_6.2.2 = endpointCodes3_6.map decodeEndpoint3 := by decide +kernel

private theorem hEndpoint3_7 :
    trunkEndpointCases (trunkCatalog.states 3).context endpointInput3_7.1 endpointInput3_7.2.1 endpointInput3_7.2.2 = endpointCodes3_7.map decodeEndpoint3 := by decide +kernel

private theorem hEndpoint3_10 :
    trunkEndpointCases (trunkCatalog.states 3).context endpointInput3_10.1 endpointInput3_10.2.1 endpointInput3_10.2.2 = endpointCodes3_10.map decodeEndpoint3 := by decide +kernel

private theorem hEndpoint3_11 :
    trunkEndpointCases (trunkCatalog.states 3).context endpointInput3_11.1 endpointInput3_11.2.1 endpointInput3_11.2.2 = endpointCodes3_11.map decodeEndpoint3 := by decide +kernel

private theorem hEndpoint3_17 :
    trunkEndpointCases (trunkCatalog.states 3).context endpointInput3_17.1 endpointInput3_17.2.1 endpointInput3_17.2.2 = endpointCodes3_17.map decodeEndpoint3 := by decide +kernel

private theorem hEndpoint3_18 :
    trunkEndpointCases (trunkCatalog.states 3).context endpointInput3_18.1 endpointInput3_18.2.1 endpointInput3_18.2.2 = endpointCodes3_18.map decodeEndpoint3 := by decide +kernel

private theorem hEndpoint3_19 :
    trunkEndpointCases (trunkCatalog.states 3).context endpointInput3_19.1 endpointInput3_19.2.1 endpointInput3_19.2.2 = endpointCodes3_19.map decodeEndpoint3 := by decide +kernel

private theorem hEndpoint3_20 :
    trunkEndpointCases (trunkCatalog.states 3).context endpointInput3_20.1 endpointInput3_20.2.1 endpointInput3_20.2.2 = endpointCodes3_20.map decodeEndpoint3 := by decide +kernel

private theorem hEndpoint3_21 :
    trunkEndpointCases (trunkCatalog.states 3).context endpointInput3_21.1 endpointInput3_21.2.1 endpointInput3_21.2.2 = endpointCodes3_21.map decodeEndpoint3 := by decide +kernel

private theorem hEndpoint3_22 :
    trunkEndpointCases (trunkCatalog.states 3).context endpointInput3_22.1 endpointInput3_22.2.1 endpointInput3_22.2.2 = endpointCodes3_22.map decodeEndpoint3 := by decide +kernel

private theorem hEndpoint3_23 :
    trunkEndpointCases (trunkCatalog.states 3).context endpointInput3_23.1 endpointInput3_23.2.1 endpointInput3_23.2.2 = endpointCodes3_23.map decodeEndpoint3 := by decide +kernel

private theorem hEndpoint3_24 :
    trunkEndpointCases (trunkCatalog.states 3).context endpointInput3_24.1 endpointInput3_24.2.1 endpointInput3_24.2.2 = endpointCodes3_24.map decodeEndpoint3 := by decide +kernel

private theorem hEndpoint3_25 :
    trunkEndpointCases (trunkCatalog.states 3).context endpointInput3_25.1 endpointInput3_25.2.1 endpointInput3_25.2.2 = endpointCodes3_25.map decodeEndpoint3 := by decide +kernel

private theorem hEndpoint3_26 :
    trunkEndpointCases (trunkCatalog.states 3).context endpointInput3_26.1 endpointInput3_26.2.1 endpointInput3_26.2.2 = endpointCodes3_26.map decodeEndpoint3 := by decide +kernel

private theorem hEndpoint3_27 :
    trunkEndpointCases (trunkCatalog.states 3).context endpointInput3_27.1 endpointInput3_27.2.1 endpointInput3_27.2.2 = endpointCodes3_27.map decodeEndpoint3 := by decide +kernel

private theorem hEndpoint3_28 :
    trunkEndpointCases (trunkCatalog.states 3).context endpointInput3_28.1 endpointInput3_28.2.1 endpointInput3_28.2.2 = endpointCodes3_28.map decodeEndpoint3 := by decide +kernel

private theorem hEndpoint3_29 :
    trunkEndpointCases (trunkCatalog.states 3).context endpointInput3_29.1 endpointInput3_29.2.1 endpointInput3_29.2.2 = endpointCodes3_29.map decodeEndpoint3 := by decide +kernel

private theorem hEndpoint3_30 :
    trunkEndpointCases (trunkCatalog.states 3).context endpointInput3_30.1 endpointInput3_30.2.1 endpointInput3_30.2.2 = endpointCodes3_30.map decodeEndpoint3 := by decide +kernel

private theorem hEndpoint3_31 :
    trunkEndpointCases (trunkCatalog.states 3).context endpointInput3_31.1 endpointInput3_31.2.1 endpointInput3_31.2.2 = endpointCodes3_31.map decodeEndpoint3 := by decide +kernel

private theorem hEndpoint3_32 :
    trunkEndpointCases (trunkCatalog.states 3).context endpointInput3_32.1 endpointInput3_32.2.1 endpointInput3_32.2.2 = endpointCodes3_32.map decodeEndpoint3 := by decide +kernel

private theorem hEndpoint3_33 :
    trunkEndpointCases (trunkCatalog.states 3).context endpointInput3_33.1 endpointInput3_33.2.1 endpointInput3_33.2.2 = endpointCodes3_33.map decodeEndpoint3 := by decide +kernel

private theorem hEndpoint3_34 :
    trunkEndpointCases (trunkCatalog.states 3).context endpointInput3_34.1 endpointInput3_34.2.1 endpointInput3_34.2.2 = endpointCodes3_34.map decodeEndpoint3 := by decide +kernel

private theorem hEndpoint3_35 :
    trunkEndpointCases (trunkCatalog.states 3).context endpointInput3_35.1 endpointInput3_35.2.1 endpointInput3_35.2.2 = endpointCodes3_35.map decodeEndpoint3 := by decide +kernel

private theorem hEndpoint3_36 :
    trunkEndpointCases (trunkCatalog.states 3).context endpointInput3_36.1 endpointInput3_36.2.1 endpointInput3_36.2.2 = endpointCodes3_36.map decodeEndpoint3 := by decide +kernel

private theorem hEndpoint3_37 :
    trunkEndpointCases (trunkCatalog.states 3).context endpointInput3_37.1 endpointInput3_37.2.1 endpointInput3_37.2.2 = endpointCodes3_37.map decodeEndpoint3 := by decide +kernel

private theorem hEndpoint3_38 :
    trunkEndpointCases (trunkCatalog.states 3).context endpointInput3_38.1 endpointInput3_38.2.1 endpointInput3_38.2.2 = endpointCodes3_38.map decodeEndpoint3 := by decide +kernel

private theorem hEndpoint3_39 :
    trunkEndpointCases (trunkCatalog.states 3).context endpointInput3_39.1 endpointInput3_39.2.1 endpointInput3_39.2.2 = endpointCodes3_39.map decodeEndpoint3 := by decide +kernel

private theorem hEndpoint3_40 :
    trunkEndpointCases (trunkCatalog.states 3).context endpointInput3_40.1 endpointInput3_40.2.1 endpointInput3_40.2.2 = endpointCodes3_40.map decodeEndpoint3 := by decide +kernel

private theorem hEndpoint3_41 :
    trunkEndpointCases (trunkCatalog.states 3).context endpointInput3_41.1 endpointInput3_41.2.1 endpointInput3_41.2.2 = endpointCodes3_41.map decodeEndpoint3 := by decide +kernel

private theorem hEndpoint3_42 :
    trunkEndpointCases (trunkCatalog.states 3).context endpointInput3_42.1 endpointInput3_42.2.1 endpointInput3_42.2.2 = endpointCodes3_42.map decodeEndpoint3 := by decide +kernel

private theorem hEndpoint3_43 :
    trunkEndpointCases (trunkCatalog.states 3).context endpointInput3_43.1 endpointInput3_43.2.1 endpointInput3_43.2.2 = endpointCodes3_43.map decodeEndpoint3 := by decide +kernel

private theorem hEndpoint3_44 :
    trunkEndpointCases (trunkCatalog.states 3).context endpointInput3_44.1 endpointInput3_44.2.1 endpointInput3_44.2.2 = endpointCodes3_44.map decodeEndpoint3 := by decide +kernel

private theorem hEndpoint3_45 :
    trunkEndpointCases (trunkCatalog.states 3).context endpointInput3_45.1 endpointInput3_45.2.1 endpointInput3_45.2.2 = endpointCodes3_45.map decodeEndpoint3 := by decide +kernel

private theorem hEndpoint3_46 :
    trunkEndpointCases (trunkCatalog.states 3).context endpointInput3_46.1 endpointInput3_46.2.1 endpointInput3_46.2.2 = endpointCodes3_46.map decodeEndpoint3 := by decide +kernel

private theorem hEndpoint3_47 :
    trunkEndpointCases (trunkCatalog.states 3).context endpointInput3_47.1 endpointInput3_47.2.1 endpointInput3_47.2.2 = endpointCodes3_47.map decodeEndpoint3 := by decide +kernel

private theorem hEndpoint3_48 :
    trunkEndpointCases (trunkCatalog.states 3).context endpointInput3_48.1 endpointInput3_48.2.1 endpointInput3_48.2.2 = endpointCodes3_48.map decodeEndpoint3 := by decide +kernel

private theorem hEndpoint3_49 :
    trunkEndpointCases (trunkCatalog.states 3).context endpointInput3_49.1 endpointInput3_49.2.1 endpointInput3_49.2.2 = endpointCodes3_49.map decodeEndpoint3 := by decide +kernel

private theorem hEndpoint3_50 :
    trunkEndpointCases (trunkCatalog.states 3).context endpointInput3_50.1 endpointInput3_50.2.1 endpointInput3_50.2.2 = endpointCodes3_50.map decodeEndpoint3 := by decide +kernel

private theorem hEndpoint3_51 :
    trunkEndpointCases (trunkCatalog.states 3).context endpointInput3_51.1 endpointInput3_51.2.1 endpointInput3_51.2.2 = endpointCodes3_51.map decodeEndpoint3 := by decide +kernel

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

private def classValidIds : List ℕ := [402, 177, 407, 411, 413, 417, 421, 422, 19, 179, 182, 181, 180, 187, 191, 200, 204, 207, 211, 213, 214, 20, 21, 94, 10, 53, 149, 55, 60, 8, 64, 63, 30, 88, 97, 95, 98, 102, 103, 377, 388, 379, 381, 378, 385, 390, 397, 16, 15, 3, 147, 174, 150, 295, 29, 17, 318, 323, 327, 329, 333, 337, 338, 113, 343, 346, 345, 350, 354, 127, 364, 365, 367, 371, 373, 374, 427, 430, 428, 429, 438, 441, 447, 451, 453, 457, 461, 462, 23, 141, 155, 156, 467, 469, 163, 153, 478, 477, 479, 481, 159, 482, 483, 165, 484, 485, 486, 487, 488, 489, 491, 492, 493, 497, 442, 502, 503, 504, 505, 506, 136, 507, 167, 18, 52, 57, 321, 91, 476, 169, 508, 349, 347, 509, 355, 515, 520, 524, 527, 529, 530]
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
private def codeHN : ℕ × Bool × Bool := bc42
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
private def thresholdParentA3 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc0, bc8], some (some bc199)),
 ([bc0, bc9], some (some bc199)),
 ([bc1, bc2, bc3, bc8], some (some bc199)),
 ([bc1, bc2, bc3, bc9], some (some bc199)),
 ([bc1, bc2, bc4, bc8], some (some bc200)),
 ([bc1, bc2, bc4, bc9], some (some bc200)),
 ([bc1, bc5, bc6, bc8], some (some bc199)),
 ([bc1, bc5, bc6, bc9], some (some bc199)),
 ([bc1, bc5, bc7, bc8], some (some bc201)),
 ([bc1, bc5, bc7, bc9], some (some bc201))]
private def thresholdParentB3 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc8, bc0], some none),
 ([bc8, bc1], some none),
 ([bc9, bc10, bc11, bc0], some none),
 ([bc9, bc10, bc11, bc1], some none),
 ([bc9, bc10, bc12, bc0], some none),
 ([bc9, bc10, bc12, bc1], some none),
 ([bc9, bc13, bc14, bc0], some none),
 ([bc9, bc13, bc14, bc1], some none),
 ([bc9, bc13, bc15, bc0], some none),
 ([bc9, bc13, bc15, bc1], some none)]

private def parentSourceA3 : Array (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := #[([bc0, bc8], some (some bc199)),
 ([bc0, bc9], some (some bc199)),
 ([bc1, bc2, bc3, bc8], some (some bc199)),
 ([bc1, bc2, bc3, bc9], some (some bc199)),
 ([bc1, bc2, bc4, bc8], some (some bc200)),
 ([bc1, bc2, bc4, bc9], some (some bc200)),
 ([bc1, bc5, bc6, bc8], some (some bc199)),
 ([bc1, bc5, bc6, bc9], some (some bc199)),
 ([bc1, bc5, bc7, bc8], some (some bc201)),
 ([bc1, bc5, bc7, bc9], some (some bc201))]

private def parentSourceB3 : Array (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := #[([bc8, bc0], some none),
 ([bc8, bc1], some none),
 ([bc9, bc10, bc11, bc0], some none),
 ([bc9, bc10, bc11, bc1], some none),
 ([bc9, bc10, bc12, bc0], some none),
 ([bc9, bc10, bc12, bc1], some none),
 ([bc9, bc13, bc14, bc0], some none),
 ([bc9, bc13, bc14, bc1], some none),
 ([bc9, bc13, bc15, bc0], some none),
 ([bc9, bc13, bc15, bc1], some none)]

private def codedParents3 (i : ℕ) : List (ℕ × Bool × Bool) :=
  if i < 100 then
    (codeRawParent (parentSourceA3[i / 10]?.getD ([],none)) (parentSourceB3[i % 10]?.getD ([],none))).getD []
  else []

private theorem hThresholdParentA3 : trunkBranches (trunkCatalog.states 3).context ⟨([2],[]),true,([1],[]),false,false,[]⟩ = thresholdParentA3.map decodeGoalBranch := by
  have hi : ((⟨([2],[]),true,([1],[]),false,false,[]⟩ : Section14Spec).first,(⟨([2],[]),true,([1],[]),false,false,[]⟩ : Section14Spec).firstUpper,trunkSpecIncoming (⟨([2],[]),true,([1],[]),false,false,[]⟩ : Section14Spec)) = endpointInput3_0 := by decide +kernel
  have hj : ((⟨([2],[]),true,([1],[]),false,false,[]⟩ : Section14Spec).second,(⟨([2],[]),true,([1],[]),false,false,[]⟩ : Section14Spec).secondUpper,trunkSpecIncoming (⟨([2],[]),true,([1],[]),false,false,[]⟩ : Section14Spec)) = endpointInput3_1 := by decide +kernel
  have heL : trunkEndpointCases (trunkCatalog.states 3).context (⟨([2],[]),true,([1],[]),false,false,[]⟩ : Section14Spec).first (⟨([2],[]),true,([1],[]),false,false,[]⟩ : Section14Spec).firstUpper (trunkSpecIncoming (⟨([2],[]),true,([1],[]),false,false,[]⟩ : Section14Spec)) = endpointCodes3_0.map decodeEndpoint3 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 3).context z.1 z.2.1 z.2.2) hi).trans hEndpoint3_0
  have heR : trunkEndpointCases (trunkCatalog.states 3).context (⟨([2],[]),true,([1],[]),false,false,[]⟩ : Section14Spec).second (⟨([2],[]),true,([1],[]),false,false,[]⟩ : Section14Spec).secondUpper (trunkSpecIncoming (⟨([2],[]),true,([1],[]),false,false,[]⟩ : Section14Spec)) = endpointCodes3_1.map decodeEndpoint3 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 3).context z.1 z.2.1 z.2.2) hj).trans hEndpoint3_1
  unfold trunkBranches
  rw [heL,heR]
  decide +kernel
private theorem hThresholdParentB3 : trunkBranches (trunkCatalog.states 3).context ⟨([1],[]),true,([2],[]),false,false,[]⟩ = thresholdParentB3.map decodeGoalBranch := by
  have hi : ((⟨([1],[]),true,([2],[]),false,false,[]⟩ : Section14Spec).first,(⟨([1],[]),true,([2],[]),false,false,[]⟩ : Section14Spec).firstUpper,trunkSpecIncoming (⟨([1],[]),true,([2],[]),false,false,[]⟩ : Section14Spec)) = endpointInput3_2 := by decide +kernel
  have hj : ((⟨([1],[]),true,([2],[]),false,false,[]⟩ : Section14Spec).second,(⟨([1],[]),true,([2],[]),false,false,[]⟩ : Section14Spec).secondUpper,trunkSpecIncoming (⟨([1],[]),true,([2],[]),false,false,[]⟩ : Section14Spec)) = endpointInput3_3 := by decide +kernel
  have heL : trunkEndpointCases (trunkCatalog.states 3).context (⟨([1],[]),true,([2],[]),false,false,[]⟩ : Section14Spec).first (⟨([1],[]),true,([2],[]),false,false,[]⟩ : Section14Spec).firstUpper (trunkSpecIncoming (⟨([1],[]),true,([2],[]),false,false,[]⟩ : Section14Spec)) = endpointCodes3_2.map decodeEndpoint3 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 3).context z.1 z.2.1 z.2.2) hi).trans hEndpoint3_2
  have heR : trunkEndpointCases (trunkCatalog.states 3).context (⟨([1],[]),true,([2],[]),false,false,[]⟩ : Section14Spec).second (⟨([1],[]),true,([2],[]),false,false,[]⟩ : Section14Spec).secondUpper (trunkSpecIncoming (⟨([1],[]),true,([2],[]),false,false,[]⟩ : Section14Spec)) = endpointCodes3_3.map decodeEndpoint3 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 3).context z.1 z.2.1 z.2.2) hj).trans hEndpoint3_3
  unfold trunkBranches
  rw [heL,heR]
  decide +kernel
private theorem hCodedParentTable3 : (List.range 100).map codedParents3 = thresholdParentA3.flatMap (fun a => thresholdParentB3.filterMap (codeRawParent a)) := by decide +kernel
private theorem hCodedParentList3 : trunkRawParents (trunkCatalog.states 3).context = ((List.range 100).map codedParents3).map (List.map decodeThresholdBound) := by
  unfold trunkRawParents
  rw [hThresholdParentA3,hThresholdParentB3]
  change (thresholdParentA3.map decodeGoalBranch).flatMap (fun a => (thresholdParentB3.map decodeGoalBranch).filterMap (rawParent a)) = ((List.range 100).map codedParents3).map (List.map decodeThresholdBound)
  rw [←codeParents_map,←hCodedParentTable3]
private theorem hCodedParentLength3 : (trunkRawParents (trunkCatalog.states 3).context).length = 100 := by
  rw [hCodedParentList3]; simp only [List.length_map,List.length_range]
private theorem hCodedParents3 (i : ℕ) : (trunkRawParents (trunkCatalog.states 3).context)[i]?.getD [] = (codedParents3 i).map decodeThresholdBound := by
  rw [hCodedParentList3,List.getElem?_map,List.getElem?_map]
  by_cases hi : i < 100
  · rw [List.getElem?_range hi]; rfl
  · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hi)]
    simp only [Option.map_none,Option.getD_none,codedParents3,if_neg hi,List.map_nil]

private theorem hHN : proj lowerHistoryHN = 466397207 := by decide +kernel
private theorem hZero : proj lowerHistoryZero = 559802771 := by decide +kernel

private theorem hA3 : (trunkBranches (trunkCatalog.states 3).context ⟨([2],[]),true,([1],[]),false,false,[]⟩).map branchCode = codesA3 := by
  rw [hThresholdParentA3]
  decide +kernel
private theorem hB3 : (trunkBranches (trunkCatalog.states 3).context ⟨([1],[]),true,([2],[]),false,false,[]⟩).map branchCode = codesB3 := by
  rw [hThresholdParentB3]
  decide +kernel
private def fprints3 : List ℕ := [2648113374, 3377004958, 3695806800, 4424698384, 4289704459, 5018596043, 4611140423, 5340032007, 4690771967, 5419663551, 3640089550, 4368981134, 2813084449, 3541976033, 3406982108, 4135873692, 3728418072, 4457309656, 3808049616, 4536941200, 4086144685, 3973233359, 5133838111, 5020926785, 5727735770, 5614824444, 6049171734, 5936260408, 6128803278, 6015891952, 5078120861, 4965209535, 4251115760, 4138204434, 4845013419, 4732102093, 5166449383, 5053538057, 5246080927, 5133169601, 3822904212, 3709992886, 4870597638, 4757686312, 5464495297, 5351583971, 5785931261, 5673019935, 5865562805, 5752651479, 4814880388, 4701969062, 3987875287, 3874963961, 4581772946, 4468861620, 4903208910, 4790297584, 4982840454, 4869929128, 4735347141, 4622435815, 5783040567, 5670129241, 6376938226, 6264026900, 6698374190, 6585462864, 6778005734, 6665094408, 5727323317, 5614411991, 4900318216, 4787406890, 5494215875, 5381304549, 5815651839, 5702740513, 5895283383, 5782372057, 4140063014, 4027151688, 5187756440, 5074845114, 5781654099, 5668742773, 6103090063, 5990178737, 6182721607, 6069810281, 5132039190, 5019127864, 4305034089, 4192122763, 4898931748, 4786020422, 5220367712, 5107456386, 5299999256, 5187087930]
private theorem hprints3 : (trunkRawParents (trunkCatalog.states 3).context).map fingerprint = fprints3 := by
  have hm (L : List (List CertBound)) :
      L.map fingerprint = (L.map (List.map proj)).map (fun cs => cs.toFinset.sum id) := by
    rw [List.map_map]; rfl
  rw [hm,trunkCodes_map,hA3,hB3,hHN,hZero]
  decide +kernel
private theorem hPar3 : trunkParents (trunkCatalog.states 3).context = trunkRawParents (trunkCatalog.states 3).context := by
  apply Freiman.trunkFast_correctness.1
  apply parents_of_fingerprints
  rw [hprints3]
  apply (List.perm_insertionSort (fun a b : ℕ => a ≤ b) fprints3).nodup_iff.mp
  have hs : (List.insertionSort (fun a b : ℕ => a ≤ b) fprints3).IsChain (fun a b => a < b) := by
    decide +kernel
  exact (List.isChain_iff_pairwise.mp hs).imp (fun h => Nat.ne_of_lt h)


private def goalCodes3_2_0 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([], none)]
private def goalCodes3_2_5 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc9, bc18, bc19, bc24, bc25],
  some (some bc202)),
 ([bc9, bc18, bc19, bc24, bc26],
  some (some (55, false, true))),
 ([bc9, bc18, bc19, bc27, bc28],
  some (some bc202)),
 ([bc9, bc18, bc19, bc27, bc29],
  some (some (57, false, true))),
 ([bc9, bc18, bc20, bc24, bc25],
  some (some (59, false, true))),
 ([bc9, bc18, bc20, bc24, bc26],
  some (some (61, false, true))),
 ([bc9, bc18, bc20, bc27, bc28],
  some (some (59, false, true))),
 ([bc9, bc18, bc20, bc27, bc29],
  some (some (62, false, true))),
 ([bc9, bc21, bc22, bc24, bc25],
  some (some bc202)),
 ([bc9, bc21, bc22, bc24, bc26],
  some (some (55, false, true))),
 ([bc9, bc21, bc22, bc27, bc28],
  some (some bc202)),
 ([bc9, bc21, bc22, bc27, bc29],
  some (some (57, false, true))),
 ([bc9, bc21, bc23, bc24, bc25],
  some (some (65, false, true))),
 ([bc9, bc21, bc23, bc24, bc26],
  some (some (67, false, true))),
 ([bc9, bc21, bc23, bc27, bc28],
  some (some (65, false, true))),
 ([bc9, bc21, bc23, bc27, bc29],
  some (some (68, false, true)))]
private def goalCodes3_2_10 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc1, bc30, bc31, bc36, bc37],
  some (some bc203)),
 ([bc1, bc30, bc31, bc36, bc38],
  some (some (92, false, true))),
 ([bc1, bc30, bc31, bc39, bc40],
  some (some bc203)),
 ([bc1, bc30, bc31, bc39, bc41],
  some (some (97, false, true))),
 ([bc1, bc30, bc32, bc36, bc37],
  some (some (99, false, true))),
 ([bc1, bc30, bc32, bc36, bc38],
  some (some (100, false, true))),
 ([bc1, bc30, bc32, bc39, bc40],
  some (some (99, false, true))),
 ([bc1, bc30, bc32, bc39, bc41],
  some (some (101, false, true))),
 ([bc1, bc33, bc34, bc36, bc37],
  some (some bc203)),
 ([bc1, bc33, bc34, bc36, bc38],
  some (some (92, false, true))),
 ([bc1, bc33, bc34, bc39, bc40],
  some (some bc203)),
 ([bc1, bc33, bc34, bc39, bc41],
  some (some (97, false, true))),
 ([bc1, bc33, bc35, bc36, bc37],
  some (some (104, false, true))),
 ([bc1, bc33, bc35, bc36, bc38],
  some (some (106, false, true))),
 ([bc1, bc33, bc35, bc39, bc40],
  some (some (104, false, true))),
 ([bc1, bc33, bc35, bc39, bc41],
  some (some (107, false, true)))]
private def goalCodes3_2_12 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc177, bc44, bc45, bc46, bc52],
  some (some bc204)),
 ([bc177,
   bc44,
   bc45,
   bc46,
   bc53,
   bc54,
   bc55],
  some (some bc204)),
 ([bc177,
   bc44,
   bc45,
   bc46,
   bc53,
   bc54,
   bc56],
  some (some (385, true, true))),
 ([bc177,
   bc44,
   bc45,
   bc46,
   bc53,
   bc57,
   bc58],
  some (some bc204)),
 ([bc177,
   bc44,
   bc45,
   bc46,
   bc53,
   bc57,
   bc59],
  some (some (390, true, true))),
 ([bc177, bc44, bc45, bc47, bc52],
  some (some (391, true, true))),
 ([bc177,
   bc44,
   bc45,
   bc47,
   bc53,
   bc54,
   bc55],
  some (some (391, true, true))),
 ([bc177,
   bc44,
   bc45,
   bc47,
   bc53,
   bc54,
   bc56],
  some (some (393, true, true))),
 ([bc177,
   bc44,
   bc45,
   bc47,
   bc53,
   bc57,
   bc58],
  some (some (391, true, true))),
 ([bc177,
   bc44,
   bc45,
   bc47,
   bc53,
   bc57,
   bc59],
  some (some (394, true, true))),
 ([bc177, bc44, bc48, bc49, bc52],
  some (some bc204)),
 ([bc177,
   bc44,
   bc48,
   bc49,
   bc53,
   bc54,
   bc55],
  some (some bc204)),
 ([bc177,
   bc44,
   bc48,
   bc49,
   bc53,
   bc54,
   bc56],
  some (some (385, true, true))),
 ([bc177,
   bc44,
   bc48,
   bc49,
   bc53,
   bc57,
   bc58],
  some (some bc204)),
 ([bc177,
   bc44,
   bc48,
   bc49,
   bc53,
   bc57,
   bc59],
  some (some (390, true, true))),
 ([bc177, bc44, bc48, bc50, bc52],
  some (some (398, true, true))),
 ([bc177,
   bc44,
   bc48,
   bc50,
   bc53,
   bc54,
   bc55],
  some (some (398, true, true))),
 ([bc177,
   bc44,
   bc48,
   bc50,
   bc53,
   bc54,
   bc56],
  some (some (399, true, true))),
 ([bc177,
   bc44,
   bc48,
   bc50,
   bc53,
   bc57,
   bc58],
  some (some (398, true, true))),
 ([bc177,
   bc44,
   bc48,
   bc50,
   bc53,
   bc57,
   bc59],
  some (some (400, true, true))),
 ([bc177, bc51, bc52], some (some bc204)),
 ([bc177, bc51, bc53, bc54, bc55],
  some (some bc204)),
 ([bc177, bc51, bc53, bc54, bc56],
  some (some (385, true, true))),
 ([bc177, bc51, bc53, bc57, bc58],
  some (some bc204)),
 ([bc177, bc51, bc53, bc57, bc59],
  some (some (390, true, true)))]
private def goalCodes3_2_14 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc180, bc60, bc68, bc69, bc70],
  some (some bc205)),
 ([bc180, bc60, bc68, bc69, bc71],
  some (some (407, false, true))),
 ([bc180, bc60, bc68, bc72, bc73],
  some (some bc205)),
 ([bc180, bc60, bc68, bc72, bc74],
  some (some (411, false, true))),
 ([bc180, bc60, bc75], some (some bc205)),
 ([bc180,
   bc61,
   bc62,
   bc63,
   bc68,
   bc69,
   bc70],
  some (some bc205)),
 ([bc180,
   bc61,
   bc62,
   bc63,
   bc68,
   bc69,
   bc71],
  some (some (407, false, true))),
 ([bc180,
   bc61,
   bc62,
   bc63,
   bc68,
   bc72,
   bc73],
  some (some bc205)),
 ([bc180,
   bc61,
   bc62,
   bc63,
   bc68,
   bc72,
   bc74],
  some (some (411, false, true))),
 ([bc180, bc61, bc62, bc63, bc75],
  some (some bc205)),
 ([bc180,
   bc61,
   bc62,
   bc64,
   bc68,
   bc69,
   bc70],
  some (some (418, false, true))),
 ([bc180,
   bc61,
   bc62,
   bc64,
   bc68,
   bc69,
   bc71],
  some (some (419, false, true))),
 ([bc180,
   bc61,
   bc62,
   bc64,
   bc68,
   bc72,
   bc73],
  some (some (418, false, true))),
 ([bc180,
   bc61,
   bc62,
   bc64,
   bc68,
   bc72,
   bc74],
  some (some (420, false, true))),
 ([bc180, bc61, bc62, bc64, bc75],
  some (some (418, false, true))),
 ([bc180,
   bc61,
   bc65,
   bc66,
   bc68,
   bc69,
   bc70],
  some (some bc205)),
 ([bc180,
   bc61,
   bc65,
   bc66,
   bc68,
   bc69,
   bc71],
  some (some (407, false, true))),
 ([bc180,
   bc61,
   bc65,
   bc66,
   bc68,
   bc72,
   bc73],
  some (some bc205)),
 ([bc180,
   bc61,
   bc65,
   bc66,
   bc68,
   bc72,
   bc74],
  some (some (411, false, true))),
 ([bc180, bc61, bc65, bc66, bc75],
  some (some bc205)),
 ([bc180,
   bc61,
   bc65,
   bc67,
   bc68,
   bc69,
   bc70],
  some (some (424, false, true))),
 ([bc180,
   bc61,
   bc65,
   bc67,
   bc68,
   bc69,
   bc71],
  some (some (425, false, true))),
 ([bc180,
   bc61,
   bc65,
   bc67,
   bc68,
   bc72,
   bc73],
  some (some (424, false, true))),
 ([bc180,
   bc61,
   bc65,
   bc67,
   bc68,
   bc72,
   bc74],
  some (some (426, false, true))),
 ([bc180, bc61, bc65, bc67, bc75],
  some (some (424, false, true)))]
private def goalCodes3_2_17 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc189, bc76, bc77, bc78, bc84],
  some (some bc206)),
 ([bc189,
   bc76,
   bc77,
   bc78,
   bc85,
   bc86,
   bc87],
  some (some bc206)),
 ([bc189,
   bc76,
   bc77,
   bc78,
   bc85,
   bc86,
   bc88],
  some (some (187, true, true))),
 ([bc189,
   bc76,
   bc77,
   bc78,
   bc85,
   bc89,
   bc90],
  some (some bc206)),
 ([bc189,
   bc76,
   bc77,
   bc78,
   bc85,
   bc89,
   bc91],
  some (some (191, true, true))),
 ([bc189, bc76, bc77, bc79, bc84],
  some (some (194, true, true))),
 ([bc189,
   bc76,
   bc77,
   bc79,
   bc85,
   bc86,
   bc87],
  some (some (194, true, true))),
 ([bc189,
   bc76,
   bc77,
   bc79,
   bc85,
   bc86,
   bc88],
  some (some (195, true, true))),
 ([bc189,
   bc76,
   bc77,
   bc79,
   bc85,
   bc89,
   bc90],
  some (some (194, true, true))),
 ([bc189,
   bc76,
   bc77,
   bc79,
   bc85,
   bc89,
   bc91],
  some (some (196, true, true))),
 ([bc189, bc76, bc80, bc81, bc84],
  some (some bc206)),
 ([bc189,
   bc76,
   bc80,
   bc81,
   bc85,
   bc86,
   bc87],
  some (some bc206)),
 ([bc189,
   bc76,
   bc80,
   bc81,
   bc85,
   bc86,
   bc88],
  some (some (187, true, true))),
 ([bc189,
   bc76,
   bc80,
   bc81,
   bc85,
   bc89,
   bc90],
  some (some bc206)),
 ([bc189,
   bc76,
   bc80,
   bc81,
   bc85,
   bc89,
   bc91],
  some (some (191, true, true))),
 ([bc189, bc76, bc80, bc82, bc84],
  some (some (199, true, true))),
 ([bc189,
   bc76,
   bc80,
   bc82,
   bc85,
   bc86,
   bc87],
  some (some (199, true, true))),
 ([bc189,
   bc76,
   bc80,
   bc82,
   bc85,
   bc86,
   bc88],
  some (some (201, true, true))),
 ([bc189,
   bc76,
   bc80,
   bc82,
   bc85,
   bc89,
   bc90],
  some (some (199, true, true))),
 ([bc189,
   bc76,
   bc80,
   bc82,
   bc85,
   bc89,
   bc91],
  some (some (202, true, true))),
 ([bc189, bc83, bc84], some (some bc206)),
 ([bc189, bc83, bc85, bc86, bc87],
  some (some bc206)),
 ([bc189, bc83, bc85, bc86, bc88],
  some (some (187, true, true))),
 ([bc189, bc83, bc85, bc89, bc90],
  some (some bc206)),
 ([bc189, bc83, bc85, bc89, bc91],
  some (some (191, true, true)))]
private def goalCodes3_2_19 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc190, (206, false, true), bc95], some (some bc207)),
 ([bc190, (206, false, true), bc96], some (some bc207)),
 ([bc190, bc92, bc93, (208, false, true), bc95],
  some (some bc207)),
 ([bc190, bc92, bc93, (208, false, true), bc96],
  some (some bc207)),
 ([bc190, bc92, bc93, (208, true, false), bc95],
  some (some (212, false, true))),
 ([bc190, bc92, bc93, (208, true, false), bc96],
  some (some (212, false, true))),
 ([bc190, bc92, bc94, (213, true, true), bc95],
  some (some bc207)),
 ([bc190, bc92, bc94, (213, true, true), bc96],
  some (some bc207)),
 ([bc190, bc92, bc94, (213, false, false), bc95],
  some (some (215, false, true))),
 ([bc190, bc92, bc94, (213, false, false), bc96],
  some (some (215, false, true)))]
private def goalCodes3_2_22 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc0, bc8], some (some bc199)),
 ([bc0, bc9], some (some bc199)),
 ([bc1, bc2, bc3, bc8], some (some bc199)),
 ([bc1, bc2, bc3, bc9], some (some bc199)),
 ([bc1, bc2, bc4, bc8], some (some bc200)),
 ([bc1, bc2, bc4, bc9], some (some bc200)),
 ([bc1, bc5, bc6, bc8], some (some bc199)),
 ([bc1, bc5, bc6, bc9], some (some bc199)),
 ([bc1, bc5, bc7, bc8], some (some bc201)),
 ([bc1, bc5, bc7, bc9], some (some bc201))]
private def goalCodes3_3_0 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes3_2_0
private def goalCodes3_3_2 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc8, bc16, (33, false, true)], some (some (36, true, true))),
 ([bc8, bc16, (33, true, false)], some (some (43, true, true))),
 ([bc8, bc17, (45, true, true)], some (some (36, true, true))),
 ([bc8, bc17, (45, false, false)], some (some (48, true, true)))]
private def goalCodes3_3_5 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes3_2_5
private def goalCodes3_3_7 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc2, bc97, bc98, bc99, bc105],
  some (some bc208)),
 ([bc2,
   bc97,
   bc98,
   bc99,
   bc106,
   bc107,
   bc108],
  some (some bc208)),
 ([bc2,
   bc97,
   bc98,
   bc99,
   bc106,
   bc107,
   bc109],
  some (some (304, true, true))),
 ([bc2,
   bc97,
   bc98,
   bc99,
   bc106,
   bc110,
   bc111],
  some (some bc208)),
 ([bc2,
   bc97,
   bc98,
   bc99,
   bc106,
   bc110,
   bc112],
  some (some (309, true, true))),
 ([bc2, bc97, bc98, bc100, bc105],
  some (some (310, true, true))),
 ([bc2,
   bc97,
   bc98,
   bc100,
   bc106,
   bc107,
   bc108],
  some (some (310, true, true))),
 ([bc2,
   bc97,
   bc98,
   bc100,
   bc106,
   bc107,
   bc109],
  some (some (311, true, true))),
 ([bc2,
   bc97,
   bc98,
   bc100,
   bc106,
   bc110,
   bc111],
  some (some (310, true, true))),
 ([bc2,
   bc97,
   bc98,
   bc100,
   bc106,
   bc110,
   bc112],
  some (some (312, true, true))),
 ([bc2, bc97, bc101, bc102, bc105],
  some (some bc208)),
 ([bc2,
   bc97,
   bc101,
   bc102,
   bc106,
   bc107,
   bc108],
  some (some bc208)),
 ([bc2,
   bc97,
   bc101,
   bc102,
   bc106,
   bc107,
   bc109],
  some (some (304, true, true))),
 ([bc2,
   bc97,
   bc101,
   bc102,
   bc106,
   bc110,
   bc111],
  some (some bc208)),
 ([bc2,
   bc97,
   bc101,
   bc102,
   bc106,
   bc110,
   bc112],
  some (some (309, true, true))),
 ([bc2, bc97, bc101, bc103, bc105],
  some (some (314, true, true))),
 ([bc2,
   bc97,
   bc101,
   bc103,
   bc106,
   bc107,
   bc108],
  some (some (314, true, true))),
 ([bc2,
   bc97,
   bc101,
   bc103,
   bc106,
   bc107,
   bc109],
  some (some (315, true, true))),
 ([bc2,
   bc97,
   bc101,
   bc103,
   bc106,
   bc110,
   bc111],
  some (some (314, true, true))),
 ([bc2,
   bc97,
   bc101,
   bc103,
   bc106,
   bc110,
   bc112],
  some (some (316, true, true))),
 ([bc2, bc104, bc105], some (some bc208)),
 ([bc2, bc104, bc106, bc107, bc108],
  some (some bc208)),
 ([bc2, bc104, bc106, bc107, bc109],
  some (some (304, true, true))),
 ([bc2, bc104, bc106, bc110, bc111],
  some (some bc208)),
 ([bc2, bc104, bc106, bc110, bc112],
  some (some (309, true, true)))]
private def goalCodes3_3_9 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc5, bc113, bc121, bc122, bc123],
  some (some bc209)),
 ([bc5, bc113, bc121, bc122, bc124],
  some (some (323, false, true))),
 ([bc5, bc113, bc121, bc125, bc126],
  some (some bc209)),
 ([bc5, bc113, bc121, bc125, bc127],
  some (some (327, false, true))),
 ([bc5, bc113, bc128], some (some bc209)),
 ([bc5,
   bc114,
   bc115,
   bc116,
   bc121,
   bc122,
   bc123],
  some (some bc209)),
 ([bc5,
   bc114,
   bc115,
   bc116,
   bc121,
   bc122,
   bc124],
  some (some (323, false, true))),
 ([bc5,
   bc114,
   bc115,
   bc116,
   bc121,
   bc125,
   bc126],
  some (some bc209)),
 ([bc5,
   bc114,
   bc115,
   bc116,
   bc121,
   bc125,
   bc127],
  some (some (327, false, true))),
 ([bc5, bc114, bc115, bc116, bc128],
  some (some bc209)),
 ([bc5,
   bc114,
   bc115,
   bc117,
   bc121,
   bc122,
   bc123],
  some (some (334, false, true))),
 ([bc5,
   bc114,
   bc115,
   bc117,
   bc121,
   bc122,
   bc124],
  some (some (335, false, true))),
 ([bc5,
   bc114,
   bc115,
   bc117,
   bc121,
   bc125,
   bc126],
  some (some (334, false, true))),
 ([bc5,
   bc114,
   bc115,
   bc117,
   bc121,
   bc125,
   bc127],
  some (some (336, false, true))),
 ([bc5, bc114, bc115, bc117, bc128],
  some (some (334, false, true))),
 ([bc5,
   bc114,
   bc118,
   bc119,
   bc121,
   bc122,
   bc123],
  some (some bc209)),
 ([bc5,
   bc114,
   bc118,
   bc119,
   bc121,
   bc122,
   bc124],
  some (some (323, false, true))),
 ([bc5,
   bc114,
   bc118,
   bc119,
   bc121,
   bc125,
   bc126],
  some (some bc209)),
 ([bc5,
   bc114,
   bc118,
   bc119,
   bc121,
   bc125,
   bc127],
  some (some (327, false, true))),
 ([bc5, bc114, bc118, bc119, bc128],
  some (some bc209)),
 ([bc5,
   bc114,
   bc118,
   bc120,
   bc121,
   bc122,
   bc123],
  some (some (340, false, true))),
 ([bc5,
   bc114,
   bc118,
   bc120,
   bc121,
   bc122,
   bc124],
  some (some (341, false, true))),
 ([bc5,
   bc114,
   bc118,
   bc120,
   bc121,
   bc125,
   bc126],
  some (some (340, false, true))),
 ([bc5,
   bc114,
   bc118,
   bc120,
   bc121,
   bc125,
   bc127],
  some (some (342, false, true))),
 ([bc5, bc114, bc118, bc120, bc128],
  some (some (340, false, true)))]
private def goalCodes3_3_12 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc171, bc129, bc130, bc131, bc137],
  some (some bc210)),
 ([bc171,
   bc129,
   bc130,
   bc131,
   bc138,
   bc139,
   bc140],
  some (some bc210)),
 ([bc171,
   bc129,
   bc130,
   bc131,
   bc138,
   bc139,
   bc141],
  some (some (350, true, true))),
 ([bc171,
   bc129,
   bc130,
   bc131,
   bc138,
   bc142,
   bc143],
  some (some bc210)),
 ([bc171,
   bc129,
   bc130,
   bc131,
   bc138,
   bc142,
   bc144],
  some (some (354, true, true))),
 ([bc171, bc129, bc130, bc132, bc137],
  some (some (356, true, true))),
 ([bc171,
   bc129,
   bc130,
   bc132,
   bc138,
   bc139,
   bc140],
  some (some (356, true, true))),
 ([bc171,
   bc129,
   bc130,
   bc132,
   bc138,
   bc139,
   bc141],
  some (some (357, true, true))),
 ([bc171,
   bc129,
   bc130,
   bc132,
   bc138,
   bc142,
   bc143],
  some (some (356, true, true))),
 ([bc171,
   bc129,
   bc130,
   bc132,
   bc138,
   bc142,
   bc144],
  some (some (358, true, true))),
 ([bc171, bc129, bc133, bc134, bc137],
  some (some bc210)),
 ([bc171,
   bc129,
   bc133,
   bc134,
   bc138,
   bc139,
   bc140],
  some (some bc210)),
 ([bc171,
   bc129,
   bc133,
   bc134,
   bc138,
   bc139,
   bc141],
  some (some (350, true, true))),
 ([bc171,
   bc129,
   bc133,
   bc134,
   bc138,
   bc142,
   bc143],
  some (some bc210)),
 ([bc171,
   bc129,
   bc133,
   bc134,
   bc138,
   bc142,
   bc144],
  some (some (354, true, true))),
 ([bc171, bc129, bc133, bc135, bc137],
  some (some (360, true, true))),
 ([bc171,
   bc129,
   bc133,
   bc135,
   bc138,
   bc139,
   bc140],
  some (some (360, true, true))),
 ([bc171,
   bc129,
   bc133,
   bc135,
   bc138,
   bc139,
   bc141],
  some (some (361, true, true))),
 ([bc171,
   bc129,
   bc133,
   bc135,
   bc138,
   bc142,
   bc143],
  some (some (360, true, true))),
 ([bc171,
   bc129,
   bc133,
   bc135,
   bc138,
   bc142,
   bc144],
  some (some (362, true, true))),
 ([bc171, bc136, bc137], some (some bc210)),
 ([bc171, bc136, bc138, bc139, bc140],
  some (some bc210)),
 ([bc171, bc136, bc138, bc139, bc141],
  some (some (350, true, true))),
 ([bc171, bc136, bc138, bc142, bc143],
  some (some bc210)),
 ([bc171, bc136, bc138, bc142, bc144],
  some (some (354, true, true)))]
private def goalCodes3_3_14 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc174, (365, false, true), bc148], some (some bc211)),
 ([bc174, (365, false, true), bc149], some (some bc211)),
 ([bc174, bc145, bc146, (370, false, true), bc148],
  some (some bc211)),
 ([bc174, bc145, bc146, (370, false, true), bc149],
  some (some bc211)),
 ([bc174, bc145, bc146, (370, true, false), bc148],
  some (some (372, false, true))),
 ([bc174, bc145, bc146, (370, true, false), bc149],
  some (some (372, false, true))),
 ([bc174, bc145, bc147, (373, true, true), bc148],
  some (some bc211)),
 ([bc174, bc145, bc147, (373, true, true), bc149],
  some (some bc211)),
 ([bc174, bc145, bc147, (373, false, false), bc148],
  some (some (375, false, true))),
 ([bc174, bc145, bc147, (373, false, false), bc149],
  some (some (375, false, true)))]
private def goalCodes3_3_17 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes3_2_12
private def goalCodes3_3_19 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes3_2_14
private def goalCodes3_3_22 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc183, bc150, bc151, (427, false, true), bc153],
  some (some bc212)),
 ([bc183, bc150, bc151, (427, false, true), bc154],
  some (some bc212)),
 ([bc183, bc150, bc151, (427, true, false), bc153],
  some (some (434, true, true))),
 ([bc183, bc150, bc151, (427, true, false), bc154],
  some (some (434, true, true))),
 ([bc183, bc150, bc152, (436, true, true), bc153],
  some (some bc212)),
 ([bc183, bc150, bc152, (436, true, true), bc154],
  some (some bc212)),
 ([bc183, bc150, bc152, (436, false, false), bc153],
  some (some (439, true, true))),
 ([bc183, bc150, bc152, (436, false, false), bc154],
  some (some (439, true, true))),
 ([bc183, (432, true, true), bc153], some (some bc212)),
 ([bc183, (432, true, true), bc154], some (some bc212))]
private def goalCodes3_3_24 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc186, bc155, bc163, bc164, bc165],
  some (some bc213)),
 ([bc186, bc155, bc163, bc164, bc166],
  some (some (447, false, true))),
 ([bc186, bc155, bc163, bc167, bc168],
  some (some bc213)),
 ([bc186, bc155, bc163, bc167, bc169],
  some (some (451, false, true))),
 ([bc186, bc155, bc170], some (some bc213)),
 ([bc186,
   bc156,
   bc157,
   bc158,
   bc163,
   bc164,
   bc165],
  some (some bc213)),
 ([bc186,
   bc156,
   bc157,
   bc158,
   bc163,
   bc164,
   bc166],
  some (some (447, false, true))),
 ([bc186,
   bc156,
   bc157,
   bc158,
   bc163,
   bc167,
   bc168],
  some (some bc213)),
 ([bc186,
   bc156,
   bc157,
   bc158,
   bc163,
   bc167,
   bc169],
  some (some (451, false, true))),
 ([bc186, bc156, bc157, bc158, bc170],
  some (some bc213)),
 ([bc186,
   bc156,
   bc157,
   bc159,
   bc163,
   bc164,
   bc165],
  some (some (458, false, true))),
 ([bc186,
   bc156,
   bc157,
   bc159,
   bc163,
   bc164,
   bc166],
  some (some (459, false, true))),
 ([bc186,
   bc156,
   bc157,
   bc159,
   bc163,
   bc167,
   bc168],
  some (some (458, false, true))),
 ([bc186,
   bc156,
   bc157,
   bc159,
   bc163,
   bc167,
   bc169],
  some (some (460, false, true))),
 ([bc186, bc156, bc157, bc159, bc170],
  some (some (458, false, true))),
 ([bc186,
   bc156,
   bc160,
   bc161,
   bc163,
   bc164,
   bc165],
  some (some bc213)),
 ([bc186,
   bc156,
   bc160,
   bc161,
   bc163,
   bc164,
   bc166],
  some (some (447, false, true))),
 ([bc186,
   bc156,
   bc160,
   bc161,
   bc163,
   bc167,
   bc168],
  some (some bc213)),
 ([bc186,
   bc156,
   bc160,
   bc161,
   bc163,
   bc167,
   bc169],
  some (some (451, false, true))),
 ([bc186, bc156, bc160, bc161, bc170],
  some (some bc213)),
 ([bc186,
   bc156,
   bc160,
   bc162,
   bc163,
   bc164,
   bc165],
  some (some (464, false, true))),
 ([bc186,
   bc156,
   bc160,
   bc162,
   bc163,
   bc164,
   bc166],
  some (some (465, false, true))),
 ([bc186,
   bc156,
   bc160,
   bc162,
   bc163,
   bc167,
   bc168],
  some (some (464, false, true))),
 ([bc186,
   bc156,
   bc160,
   bc162,
   bc163,
   bc167,
   bc169],
  some (some (466, false, true))),
 ([bc186, bc156, bc160, bc162, bc170],
  some (some (464, false, true)))]
private def goalCodes3_3_27 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes3_2_17
private def goalCodes3_3_29 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes3_2_19
private def goalCodes3_3_32 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc2, bc3, bc8], some (some bc199)),
 ([bc2, bc3, bc9], some (some bc199)),
 ([bc2, bc4, bc8], some (some bc200)),
 ([bc2, bc4, bc9], some (some bc200)),
 ([bc5, bc6, bc8], some (some bc199)),
 ([bc5, bc6, bc9], some (some bc199)),
 ([bc5, bc7, bc8], some (some bc201)),
 ([bc5, bc7, bc9], some (some bc201))]
private def goalCodes3_3_34 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc171, bc172, bc2, bc37], some (some bc214)),
 ([bc171, bc172, bc2, bc38], some (some (468, true, false))),
 ([bc171, bc172, bc5, bc40], some (some bc214)),
 ([bc171, bc172, bc5, bc41], some (some (469, true, false))),
 ([bc171, bc173, bc2, bc37], some (some (470, true, false))),
 ([bc171, bc173, bc2, bc38], some (some (471, true, false))),
 ([bc171, bc173, bc5, bc40], some (some (470, true, false))),
 ([bc171, bc173, bc5, bc41], some (some (472, true, false))),
 ([bc174, bc175, bc2, bc37], some (some bc214)),
 ([bc174, bc175, bc2, bc38], some (some (468, true, false))),
 ([bc174, bc175, bc5, bc40], some (some bc214)),
 ([bc174, bc175, bc5, bc41], some (some (469, true, false))),
 ([bc174, bc176, bc2, bc37], some (some (473, true, false))),
 ([bc174, bc176, bc2, bc38], some (some (474, true, false))),
 ([bc174, bc176, bc5, bc40], some (some (473, true, false))),
 ([bc174, bc176, bc5, bc41], some (some (475, true, false)))]
private def goalCodes3_3_35 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc171, bc172, bc177, bc178], some (some bc215)),
 ([bc171, bc172, bc177, bc179], some (some (477, true, false))),
 ([bc171, bc172, bc180, bc181], some (some bc215)),
 ([bc171, bc172, bc180, bc182], some (some (481, true, false))),
 ([bc171, bc173, bc177, bc178], some (some (159, true, false))),
 ([bc171, bc173, bc177, bc179], some (some (482, true, false))),
 ([bc171, bc173, bc180, bc181], some (some (159, true, false))),
 ([bc171, bc173, bc180, bc182], some (some (483, true, false))),
 ([bc174, bc175, bc177, bc178], some (some bc215)),
 ([bc174, bc175, bc177, bc179], some (some (477, true, false))),
 ([bc174, bc175, bc180, bc181], some (some bc215)),
 ([bc174, bc175, bc180, bc182], some (some (481, true, false))),
 ([bc174, bc176, bc177, bc178], some (some (165, true, false))),
 ([bc174, bc176, bc177, bc179], some (some (484, true, false))),
 ([bc174, bc176, bc180, bc181], some (some (165, true, false))),
 ([bc174, bc176, bc180, bc182], some (some (485, true, false)))]
private def goalCodes3_3_36 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc177, bc31], some (some (486, false, false))),
 ([bc177, bc32], some (some (487, false, false))),
 ([bc180, bc34], some (some (486, false, false))),
 ([bc180, bc35], some (some (488, false, false)))]
private def goalCodes3_3_38 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc183, bc184, bc177, bc178], some (some bc216)),
 ([bc183, bc184, bc177, bc179], some (some (491, false, false))),
 ([bc183, bc184, bc180, bc181], some (some bc216)),
 ([bc183, bc184, bc180, bc182], some (some (492, false, false))),
 ([bc183, bc185, bc177, bc178], some (some (494, false, false))),
 ([bc183, bc185, bc177, bc179], some (some (495, false, false))),
 ([bc183, bc185, bc180, bc181], some (some (494, false, false))),
 ([bc183, bc185, bc180, bc182], some (some (496, false, false))),
 ([bc186, bc187, bc177, bc178], some (some bc216)),
 ([bc186, bc187, bc177, bc179], some (some (491, false, false))),
 ([bc186, bc187, bc180, bc181], some (some bc216)),
 ([bc186, bc187, bc180, bc182], some (some (492, false, false))),
 ([bc186, bc188, bc177, bc178], some (some (499, false, false))),
 ([bc186, bc188, bc177, bc179], some (some (500, false, false))),
 ([bc186, bc188, bc180, bc181], some (some (499, false, false))),
 ([bc186, bc188, bc180, bc182], some (some (501, false, false)))]
private def goalCodes3_3_39 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc183, bc184], some (some (502, false, false))),
 ([bc183, bc185], some (some (503, false, false))),
 ([bc186, bc187], some (some (502, false, false))),
 ([bc186, bc188], some (some (504, false, false)))]
private def goalCodes3_3_40 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc189, (133, false, true)], some (some (505, true, false))),
 ([bc189, (133, true, false)], some (some (506, true, false))),
 ([bc190, (136, true, true)], some (some (505, true, false))),
 ([bc190, (136, false, false)], some (some (507, true, false)))]
private def goalCodes3_3_41 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc8, bc42, bc11], some none),
 ([bc8, bc42, bc12], some none),
 ([bc8, bc43, bc14], some none),
 ([bc8, bc43, bc15], some none),
 ([bc9, bc10, bc11, bc42, bc11], some none),
 ([bc9, bc10, bc11, bc42, bc12], some none),
 ([bc9, bc10, bc11, bc43, bc14], some none),
 ([bc9, bc10, bc11, bc43, bc15], some none),
 ([bc9, bc10, bc12, bc42, bc11], none),
 ([bc9, bc10, bc12, bc42, bc12], some none),
 ([bc9, bc10, bc12, bc43, bc14], none),
 ([bc9, bc10, bc12, bc43, bc15],
  some (some (168, false, false))),
 ([bc9, bc13, bc14, bc42, bc11], some none),
 ([bc9, bc13, bc14, bc42, bc12], some none),
 ([bc9, bc13, bc14, bc43, bc14], some none),
 ([bc9, bc13, bc14, bc43, bc15], some none),
 ([bc9, bc13, bc15, bc42, bc11], none),
 ([bc9, bc13, bc15, bc42, bc12],
  some (some (168, true, false))),
 ([bc9, bc13, bc15, bc43, bc14], none),
 ([bc9, bc13, bc15, bc43, bc15], some none)]
private def goalCodes3_4_0 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes3_2_0
private def goalCodes3_4_2 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes3_3_2
private def goalCodes3_4_5 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes3_2_5
private def goalCodes3_4_7 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes3_3_7
private def goalCodes3_4_9 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes3_3_9
private def goalCodes3_4_12 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc217, bc191, bc192, bc139, bc140],
  some (some bc218)),
 ([bc217, bc191, bc192, bc139, bc141],
  some (some (512, true, true))),
 ([bc217, bc191, bc192, bc142, bc143],
  some (some bc218)),
 ([bc217, bc191, bc192, bc142, bc144],
  some (some (513, true, true))),
 ([bc217, bc191, bc193, bc139, bc140],
  some (some (515, true, true))),
 ([bc217, bc191, bc193, bc139, bc141],
  some (some (516, true, true))),
 ([bc217, bc191, bc193, bc142, bc143],
  some (some (515, true, true))),
 ([bc217, bc191, bc193, bc142, bc144],
  some (some (517, true, true))),
 ([bc217, bc194, bc195, bc139, bc140],
  some (some bc218)),
 ([bc217, bc194, bc195, bc139, bc141],
  some (some (512, true, true))),
 ([bc217, bc194, bc195, bc142, bc143],
  some (some bc218)),
 ([bc217, bc194, bc195, bc142, bc144],
  some (some (513, true, true))),
 ([bc217, bc194, bc196, bc139, bc140],
  some (some (520, true, true))),
 ([bc217, bc194, bc196, bc139, bc141],
  some (some (522, true, true))),
 ([bc217, bc194, bc196, bc142, bc143],
  some (some (520, true, true))),
 ([bc217, bc194, bc196, bc142, bc144],
  some (some (523, true, true)))]
private def goalCodes3_4_15 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc219, bc197, (526, false, true)], some (some (524, false, true))),
 ([bc219, bc197, (526, true, false)], some (some (528, false, true))),
 ([bc219, bc198, (529, true, true)], some (some (524, false, true))),
 ([bc219, bc198, (529, false, false)], some (some (531, false, true)))]
private def goalCodes3_4_17 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes3_2_12
private def goalCodes3_4_19 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes3_2_14
private def goalCodes3_4_22 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes3_3_22
private def goalCodes3_4_24 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes3_3_24
private def goalCodes3_4_27 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes3_2_17
private def cutCodes3_2 : List (ℕ × Bool × Bool) := [(7, true, false), (177, false, false), (551, false, false)]
private def cutCodes3_3 : List (ℕ × Bool × Bool) := [(7, true, false), (177, true, true), (296, false, true)]
private def cutCodes3_4 : List (ℕ × Bool × Bool) := [(7, true, false), (177, true, true), (296, true, false)]

private abbrev goalSpec3_2_14 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 3) 2))[14-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal3_2_14 : trunkGoalBranches (trunkCatalog.states 3) 2 14 = goalCodes3_2_14.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 3).context goalSpec3_2_14 = _
  exact (cachedBranches_eq (trunkCatalog.states 3).context goalSpec3_2_14
    endpointInput3_20 endpointInput3_21 (([bc180] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes3_20.map decodeEndpoint3) (endpointCodes3_21.map decodeEndpoint3)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint3_20 hEndpoint3_21).trans
    (by decide +kernel)

private abbrev goalSpec3_2_17 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 3) 2))[17-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal3_2_17 : trunkGoalBranches (trunkCatalog.states 3) 2 17 = goalCodes3_2_17.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 3).context goalSpec3_2_17 = _
  exact (cachedBranches_eq (trunkCatalog.states 3).context goalSpec3_2_17
    endpointInput3_22 endpointInput3_23 (([bc189] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes3_22.map decodeEndpoint3) (endpointCodes3_23.map decodeEndpoint3)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint3_22 hEndpoint3_23).trans
    (by decide +kernel)

private abbrev goalSpec3_2_19 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 3) 2))[19-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal3_2_19 : trunkGoalBranches (trunkCatalog.states 3) 2 19 = goalCodes3_2_19.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 3).context goalSpec3_2_19 = _
  exact (cachedBranches_eq (trunkCatalog.states 3).context goalSpec3_2_19
    endpointInput3_24 endpointInput3_25 (([bc190] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes3_24.map decodeEndpoint3) (endpointCodes3_25.map decodeEndpoint3)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint3_24 hEndpoint3_25).trans
    (by decide +kernel)

private theorem hGoal3_2_0 : trunkGoalBranches (trunkCatalog.states 3) 2 0 = goalCodes3_2_0.map decodeGoalBranch := by
  decide +kernel

private abbrev goalSpec3_2_5 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 3) 2))[5-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal3_2_5 : trunkGoalBranches (trunkCatalog.states 3) 2 5 = goalCodes3_2_5.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 3).context goalSpec3_2_5 = _
  exact (cachedBranches_eq (trunkCatalog.states 3).context goalSpec3_2_5
    endpointInput3_6 endpointInput3_7 (([bc9] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes3_6.map decodeEndpoint3) (endpointCodes3_7.map decodeEndpoint3)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint3_6 hEndpoint3_7).trans
    (by decide +kernel)

private abbrev goalSpec3_2_10 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 3) 2))[10-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal3_2_10 : trunkGoalBranches (trunkCatalog.states 3) 2 10 = goalCodes3_2_10.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 3).context goalSpec3_2_10 = _
  exact (cachedBranches_eq (trunkCatalog.states 3).context goalSpec3_2_10
    endpointInput3_10 endpointInput3_11 (([bc1] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes3_10.map decodeEndpoint3) (endpointCodes3_11.map decodeEndpoint3)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint3_10 hEndpoint3_11).trans
    (by decide +kernel)

private abbrev goalSpec3_2_12 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 3) 2))[12-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal3_2_12 : trunkGoalBranches (trunkCatalog.states 3) 2 12 = goalCodes3_2_12.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 3).context goalSpec3_2_12 = _
  exact (cachedBranches_eq (trunkCatalog.states 3).context goalSpec3_2_12
    endpointInput3_18 endpointInput3_19 (([bc177] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes3_18.map decodeEndpoint3) (endpointCodes3_19.map decodeEndpoint3)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint3_18 hEndpoint3_19).trans
    (by decide +kernel)

private abbrev goalSpec3_2_22 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 3) 2))[22-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal3_2_22 : trunkGoalBranches (trunkCatalog.states 3) 2 22 = goalCodes3_2_22.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 3).context goalSpec3_2_22 = _
  exact (cachedBranches_eq (trunkCatalog.states 3).context goalSpec3_2_22
    endpointInput3_0 endpointInput3_1 (([] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes3_0.map decodeEndpoint3) (endpointCodes3_1.map decodeEndpoint3)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint3_0 hEndpoint3_1).trans
    (by decide +kernel)

private theorem hGoal3_3_0 : trunkGoalBranches (trunkCatalog.states 3) 3 0 = goalCodes3_3_0.map decodeGoalBranch := by
  exact hGoal3_2_0

private abbrev goalSpec3_3_2 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 3) 3))[2-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal3_3_2 : trunkGoalBranches (trunkCatalog.states 3) 3 2 = goalCodes3_3_2.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 3).context goalSpec3_3_2 = _
  exact (cachedBranches_eq (trunkCatalog.states 3).context goalSpec3_3_2
    endpointInput3_4 endpointInput3_5 (([bc8] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes3_4.map decodeEndpoint3) (endpointCodes3_5.map decodeEndpoint3)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint3_4 hEndpoint3_5).trans
    (by decide +kernel)

private abbrev goalSpec3_3_5 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 3) 3))[5-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal3_3_5 : trunkGoalBranches (trunkCatalog.states 3) 3 5 = goalCodes3_3_5.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 3) 3 5 = trunkGoalBranches (trunkCatalog.states 3) 2 5 := by
      apply congrArg (trunkBranches (trunkCatalog.states 3).context)
      decide +kernel
    exact he.trans hGoal3_2_5
  | change trunkBranches (trunkCatalog.states 3).context goalSpec3_3_5 = _
    exact (cachedBranches_eq (trunkCatalog.states 3).context goalSpec3_3_5
      endpointInput3_6 endpointInput3_7 (([bc9] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
      (endpointCodes3_6.map decodeEndpoint3) (endpointCodes3_7.map decodeEndpoint3)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint3_6 hEndpoint3_7).trans
      (by decide +kernel)

private abbrev goalSpec3_3_7 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 3) 3))[7-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal3_3_7 : trunkGoalBranches (trunkCatalog.states 3) 3 7 = goalCodes3_3_7.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 3).context goalSpec3_3_7 = _
  exact (cachedBranches_eq (trunkCatalog.states 3).context goalSpec3_3_7
    endpointInput3_26 endpointInput3_27 (([bc2] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes3_26.map decodeEndpoint3) (endpointCodes3_27.map decodeEndpoint3)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint3_26 hEndpoint3_27).trans
    (by decide +kernel)

private abbrev goalSpec3_3_9 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 3) 3))[9-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal3_3_9 : trunkGoalBranches (trunkCatalog.states 3) 3 9 = goalCodes3_3_9.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 3).context goalSpec3_3_9 = _
  exact (cachedBranches_eq (trunkCatalog.states 3).context goalSpec3_3_9
    endpointInput3_28 endpointInput3_29 (([bc5] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes3_28.map decodeEndpoint3) (endpointCodes3_29.map decodeEndpoint3)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint3_28 hEndpoint3_29).trans
    (by decide +kernel)

private abbrev goalSpec3_3_12 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 3) 3))[12-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal3_3_12 : trunkGoalBranches (trunkCatalog.states 3) 3 12 = goalCodes3_3_12.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 3).context goalSpec3_3_12 = _
  exact (cachedBranches_eq (trunkCatalog.states 3).context goalSpec3_3_12
    endpointInput3_30 endpointInput3_31 (([bc171] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes3_30.map decodeEndpoint3) (endpointCodes3_31.map decodeEndpoint3)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint3_30 hEndpoint3_31).trans
    (by decide +kernel)

private abbrev goalSpec3_3_14 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 3) 3))[14-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal3_3_14 : trunkGoalBranches (trunkCatalog.states 3) 3 14 = goalCodes3_3_14.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 3).context goalSpec3_3_14 = _
  exact (cachedBranches_eq (trunkCatalog.states 3).context goalSpec3_3_14
    endpointInput3_32 endpointInput3_33 (([bc174] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes3_32.map decodeEndpoint3) (endpointCodes3_33.map decodeEndpoint3)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint3_32 hEndpoint3_33).trans
    (by decide +kernel)

private abbrev goalSpec3_3_17 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 3) 3))[17-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal3_3_17 : trunkGoalBranches (trunkCatalog.states 3) 3 17 = goalCodes3_3_17.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 3) 3 17 = trunkGoalBranches (trunkCatalog.states 3) 2 12 := by
      apply congrArg (trunkBranches (trunkCatalog.states 3).context)
      decide +kernel
    exact he.trans hGoal3_2_12
  | change trunkBranches (trunkCatalog.states 3).context goalSpec3_3_17 = _
    exact (cachedBranches_eq (trunkCatalog.states 3).context goalSpec3_3_17
      endpointInput3_18 endpointInput3_19 (([bc177] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
      (endpointCodes3_18.map decodeEndpoint3) (endpointCodes3_19.map decodeEndpoint3)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint3_18 hEndpoint3_19).trans
      (by decide +kernel)

private abbrev goalSpec3_3_19 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 3) 3))[19-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal3_3_19 : trunkGoalBranches (trunkCatalog.states 3) 3 19 = goalCodes3_3_19.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 3) 3 19 = trunkGoalBranches (trunkCatalog.states 3) 2 14 := by
      apply congrArg (trunkBranches (trunkCatalog.states 3).context)
      decide +kernel
    exact he.trans hGoal3_2_14
  | change trunkBranches (trunkCatalog.states 3).context goalSpec3_3_19 = _
    exact (cachedBranches_eq (trunkCatalog.states 3).context goalSpec3_3_19
      endpointInput3_20 endpointInput3_21 (([bc180] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
      (endpointCodes3_20.map decodeEndpoint3) (endpointCodes3_21.map decodeEndpoint3)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint3_20 hEndpoint3_21).trans
      (by decide +kernel)

private abbrev goalSpec3_3_22 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 3) 3))[22-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal3_3_22 : trunkGoalBranches (trunkCatalog.states 3) 3 22 = goalCodes3_3_22.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 3).context goalSpec3_3_22 = _
  exact (cachedBranches_eq (trunkCatalog.states 3).context goalSpec3_3_22
    endpointInput3_34 endpointInput3_35 (([bc183] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes3_34.map decodeEndpoint3) (endpointCodes3_35.map decodeEndpoint3)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint3_34 hEndpoint3_35).trans
    (by decide +kernel)

private abbrev goalSpec3_3_24 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 3) 3))[24-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal3_3_24 : trunkGoalBranches (trunkCatalog.states 3) 3 24 = goalCodes3_3_24.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 3).context goalSpec3_3_24 = _
  exact (cachedBranches_eq (trunkCatalog.states 3).context goalSpec3_3_24
    endpointInput3_36 endpointInput3_37 (([bc186] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes3_36.map decodeEndpoint3) (endpointCodes3_37.map decodeEndpoint3)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint3_36 hEndpoint3_37).trans
    (by decide +kernel)

private abbrev goalSpec3_3_27 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 3) 3))[27-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal3_3_27 : trunkGoalBranches (trunkCatalog.states 3) 3 27 = goalCodes3_3_27.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 3) 3 27 = trunkGoalBranches (trunkCatalog.states 3) 2 17 := by
      apply congrArg (trunkBranches (trunkCatalog.states 3).context)
      decide +kernel
    exact he.trans hGoal3_2_17
  | change trunkBranches (trunkCatalog.states 3).context goalSpec3_3_27 = _
    exact (cachedBranches_eq (trunkCatalog.states 3).context goalSpec3_3_27
      endpointInput3_22 endpointInput3_23 (([bc189] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
      (endpointCodes3_22.map decodeEndpoint3) (endpointCodes3_23.map decodeEndpoint3)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint3_22 hEndpoint3_23).trans
      (by decide +kernel)

private abbrev goalSpec3_3_29 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 3) 3))[29-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal3_3_29 : trunkGoalBranches (trunkCatalog.states 3) 3 29 = goalCodes3_3_29.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 3) 3 29 = trunkGoalBranches (trunkCatalog.states 3) 2 19 := by
      apply congrArg (trunkBranches (trunkCatalog.states 3).context)
      decide +kernel
    exact he.trans hGoal3_2_19
  | change trunkBranches (trunkCatalog.states 3).context goalSpec3_3_29 = _
    exact (cachedBranches_eq (trunkCatalog.states 3).context goalSpec3_3_29
      endpointInput3_24 endpointInput3_25 (([bc190] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
      (endpointCodes3_24.map decodeEndpoint3) (endpointCodes3_25.map decodeEndpoint3)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint3_24 hEndpoint3_25).trans
      (by decide +kernel)

private abbrev goalSpec3_3_32 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 3) 3))[32-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal3_3_32 : trunkGoalBranches (trunkCatalog.states 3) 3 32 = goalCodes3_3_32.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 3).context goalSpec3_3_32 = _
  exact (cachedBranches_eq (trunkCatalog.states 3).context goalSpec3_3_32
    endpointInput3_38 endpointInput3_1 (([] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes3_38.map decodeEndpoint3) (endpointCodes3_1.map decodeEndpoint3)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint3_38 hEndpoint3_1).trans
    (by decide +kernel)

private abbrev goalSpec3_3_34 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 3) 3))[34-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal3_3_34 : trunkGoalBranches (trunkCatalog.states 3) 3 34 = goalCodes3_3_34.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 3).context goalSpec3_3_34 = _
  exact (cachedBranches_eq (trunkCatalog.states 3).context goalSpec3_3_34
    endpointInput3_39 endpointInput3_40 (([] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes3_39.map decodeEndpoint3) (endpointCodes3_40.map decodeEndpoint3)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint3_39 hEndpoint3_40).trans
    (by decide +kernel)

private abbrev goalSpec3_3_35 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 3) 3))[35-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal3_3_35 : trunkGoalBranches (trunkCatalog.states 3) 3 35 = goalCodes3_3_35.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 3).context goalSpec3_3_35 = _
  exact (cachedBranches_eq (trunkCatalog.states 3).context goalSpec3_3_35
    endpointInput3_39 endpointInput3_41 (([] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes3_39.map decodeEndpoint3) (endpointCodes3_41.map decodeEndpoint3)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint3_39 hEndpoint3_41).trans
    (by decide +kernel)

private abbrev goalSpec3_3_36 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 3) 3))[36-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal3_3_36 : trunkGoalBranches (trunkCatalog.states 3) 3 36 = goalCodes3_3_36.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 3).context goalSpec3_3_36 = _
  exact (cachedBranches_eq (trunkCatalog.states 3).context goalSpec3_3_36
    endpointInput3_42 endpointInput3_43 (([] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes3_42.map decodeEndpoint3) (endpointCodes3_43.map decodeEndpoint3)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint3_42 hEndpoint3_43).trans
    (by decide +kernel)

private abbrev goalSpec3_3_38 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 3) 3))[38-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal3_3_38 : trunkGoalBranches (trunkCatalog.states 3) 3 38 = goalCodes3_3_38.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 3).context goalSpec3_3_38 = _
  exact (cachedBranches_eq (trunkCatalog.states 3).context goalSpec3_3_38
    endpointInput3_44 endpointInput3_41 (([] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes3_44.map decodeEndpoint3) (endpointCodes3_41.map decodeEndpoint3)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint3_44 hEndpoint3_41).trans
    (by decide +kernel)

private abbrev goalSpec3_3_39 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 3) 3))[39-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal3_3_39 : trunkGoalBranches (trunkCatalog.states 3) 3 39 = goalCodes3_3_39.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 3).context goalSpec3_3_39 = _
  exact (cachedBranches_eq (trunkCatalog.states 3).context goalSpec3_3_39
    endpointInput3_44 endpointInput3_45 (([] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes3_44.map decodeEndpoint3) (endpointCodes3_45.map decodeEndpoint3)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint3_44 hEndpoint3_45).trans
    (by decide +kernel)

private abbrev goalSpec3_3_40 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 3) 3))[40-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal3_3_40 : trunkGoalBranches (trunkCatalog.states 3) 3 40 = goalCodes3_3_40.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 3).context goalSpec3_3_40 = _
  exact (cachedBranches_eq (trunkCatalog.states 3).context goalSpec3_3_40
    endpointInput3_46 endpointInput3_47 (([] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes3_46.map decodeEndpoint3) (endpointCodes3_47.map decodeEndpoint3)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint3_46 hEndpoint3_47).trans
    (by decide +kernel)

private abbrev goalSpec3_3_41 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 3) 3))[41-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal3_3_41 : trunkGoalBranches (trunkCatalog.states 3) 3 41 = goalCodes3_3_41.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 3).context goalSpec3_3_41 = _
  exact (cachedBranches_eq (trunkCatalog.states 3).context goalSpec3_3_41
    endpointInput3_2 endpointInput3_17 (([] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes3_2.map decodeEndpoint3) (endpointCodes3_17.map decodeEndpoint3)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint3_2 hEndpoint3_17).trans
    (by decide +kernel)

private theorem hGoal3_4_0 : trunkGoalBranches (trunkCatalog.states 3) 4 0 = goalCodes3_4_0.map decodeGoalBranch := by
  exact hGoal3_2_0

private abbrev goalSpec3_4_2 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 3) 4))[2-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal3_4_2 : trunkGoalBranches (trunkCatalog.states 3) 4 2 = goalCodes3_4_2.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 3) 4 2 = trunkGoalBranches (trunkCatalog.states 3) 3 2 := by
      apply congrArg (trunkBranches (trunkCatalog.states 3).context)
      decide +kernel
    exact he.trans hGoal3_3_2
  | change trunkBranches (trunkCatalog.states 3).context goalSpec3_4_2 = _
    exact (cachedBranches_eq (trunkCatalog.states 3).context goalSpec3_4_2
      endpointInput3_4 endpointInput3_5 (([bc8] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
      (endpointCodes3_4.map decodeEndpoint3) (endpointCodes3_5.map decodeEndpoint3)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint3_4 hEndpoint3_5).trans
      (by decide +kernel)

private abbrev goalSpec3_4_5 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 3) 4))[5-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal3_4_5 : trunkGoalBranches (trunkCatalog.states 3) 4 5 = goalCodes3_4_5.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 3) 4 5 = trunkGoalBranches (trunkCatalog.states 3) 2 5 := by
      apply congrArg (trunkBranches (trunkCatalog.states 3).context)
      decide +kernel
    exact he.trans hGoal3_2_5
  | change trunkBranches (trunkCatalog.states 3).context goalSpec3_4_5 = _
    exact (cachedBranches_eq (trunkCatalog.states 3).context goalSpec3_4_5
      endpointInput3_6 endpointInput3_7 (([bc9] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
      (endpointCodes3_6.map decodeEndpoint3) (endpointCodes3_7.map decodeEndpoint3)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint3_6 hEndpoint3_7).trans
      (by decide +kernel)

private abbrev goalSpec3_4_7 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 3) 4))[7-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal3_4_7 : trunkGoalBranches (trunkCatalog.states 3) 4 7 = goalCodes3_4_7.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 3) 4 7 = trunkGoalBranches (trunkCatalog.states 3) 3 7 := by
      apply congrArg (trunkBranches (trunkCatalog.states 3).context)
      decide +kernel
    exact he.trans hGoal3_3_7
  | change trunkBranches (trunkCatalog.states 3).context goalSpec3_4_7 = _
    exact (cachedBranches_eq (trunkCatalog.states 3).context goalSpec3_4_7
      endpointInput3_26 endpointInput3_27 (([bc2] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
      (endpointCodes3_26.map decodeEndpoint3) (endpointCodes3_27.map decodeEndpoint3)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint3_26 hEndpoint3_27).trans
      (by decide +kernel)

private abbrev goalSpec3_4_9 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 3) 4))[9-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal3_4_9 : trunkGoalBranches (trunkCatalog.states 3) 4 9 = goalCodes3_4_9.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 3) 4 9 = trunkGoalBranches (trunkCatalog.states 3) 3 9 := by
      apply congrArg (trunkBranches (trunkCatalog.states 3).context)
      decide +kernel
    exact he.trans hGoal3_3_9
  | change trunkBranches (trunkCatalog.states 3).context goalSpec3_4_9 = _
    exact (cachedBranches_eq (trunkCatalog.states 3).context goalSpec3_4_9
      endpointInput3_28 endpointInput3_29 (([bc5] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
      (endpointCodes3_28.map decodeEndpoint3) (endpointCodes3_29.map decodeEndpoint3)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint3_28 hEndpoint3_29).trans
      (by decide +kernel)

private abbrev goalSpec3_4_12 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 3) 4))[12-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal3_4_12 : trunkGoalBranches (trunkCatalog.states 3) 4 12 = goalCodes3_4_12.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 3).context goalSpec3_4_12 = _
  exact (cachedBranches_eq (trunkCatalog.states 3).context goalSpec3_4_12
    endpointInput3_48 endpointInput3_49 (([bc217] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes3_48.map decodeEndpoint3) (endpointCodes3_49.map decodeEndpoint3)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint3_48 hEndpoint3_49).trans
    (by decide +kernel)

private abbrev goalSpec3_4_15 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 3) 4))[15-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal3_4_15 : trunkGoalBranches (trunkCatalog.states 3) 4 15 = goalCodes3_4_15.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 3).context goalSpec3_4_15 = _
  exact (cachedBranches_eq (trunkCatalog.states 3).context goalSpec3_4_15
    endpointInput3_50 endpointInput3_51 (([bc219] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes3_50.map decodeEndpoint3) (endpointCodes3_51.map decodeEndpoint3)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint3_50 hEndpoint3_51).trans
    (by decide +kernel)

private abbrev goalSpec3_4_17 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 3) 4))[17-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal3_4_17 : trunkGoalBranches (trunkCatalog.states 3) 4 17 = goalCodes3_4_17.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 3) 4 17 = trunkGoalBranches (trunkCatalog.states 3) 2 12 := by
      apply congrArg (trunkBranches (trunkCatalog.states 3).context)
      decide +kernel
    exact he.trans hGoal3_2_12
  | change trunkBranches (trunkCatalog.states 3).context goalSpec3_4_17 = _
    exact (cachedBranches_eq (trunkCatalog.states 3).context goalSpec3_4_17
      endpointInput3_18 endpointInput3_19 (([bc177] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
      (endpointCodes3_18.map decodeEndpoint3) (endpointCodes3_19.map decodeEndpoint3)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint3_18 hEndpoint3_19).trans
      (by decide +kernel)

private abbrev goalSpec3_4_19 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 3) 4))[19-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal3_4_19 : trunkGoalBranches (trunkCatalog.states 3) 4 19 = goalCodes3_4_19.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 3) 4 19 = trunkGoalBranches (trunkCatalog.states 3) 2 14 := by
      apply congrArg (trunkBranches (trunkCatalog.states 3).context)
      decide +kernel
    exact he.trans hGoal3_2_14
  | change trunkBranches (trunkCatalog.states 3).context goalSpec3_4_19 = _
    exact (cachedBranches_eq (trunkCatalog.states 3).context goalSpec3_4_19
      endpointInput3_20 endpointInput3_21 (([bc180] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
      (endpointCodes3_20.map decodeEndpoint3) (endpointCodes3_21.map decodeEndpoint3)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint3_20 hEndpoint3_21).trans
      (by decide +kernel)

private abbrev goalSpec3_4_22 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 3) 4))[22-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal3_4_22 : trunkGoalBranches (trunkCatalog.states 3) 4 22 = goalCodes3_4_22.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 3) 4 22 = trunkGoalBranches (trunkCatalog.states 3) 3 22 := by
      apply congrArg (trunkBranches (trunkCatalog.states 3).context)
      decide +kernel
    exact he.trans hGoal3_3_22
  | change trunkBranches (trunkCatalog.states 3).context goalSpec3_4_22 = _
    exact (cachedBranches_eq (trunkCatalog.states 3).context goalSpec3_4_22
      endpointInput3_34 endpointInput3_35 (([bc183] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
      (endpointCodes3_34.map decodeEndpoint3) (endpointCodes3_35.map decodeEndpoint3)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint3_34 hEndpoint3_35).trans
      (by decide +kernel)

private abbrev goalSpec3_4_24 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 3) 4))[24-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal3_4_24 : trunkGoalBranches (trunkCatalog.states 3) 4 24 = goalCodes3_4_24.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 3) 4 24 = trunkGoalBranches (trunkCatalog.states 3) 3 24 := by
      apply congrArg (trunkBranches (trunkCatalog.states 3).context)
      decide +kernel
    exact he.trans hGoal3_3_24
  | change trunkBranches (trunkCatalog.states 3).context goalSpec3_4_24 = _
    exact (cachedBranches_eq (trunkCatalog.states 3).context goalSpec3_4_24
      endpointInput3_36 endpointInput3_37 (([bc186] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
      (endpointCodes3_36.map decodeEndpoint3) (endpointCodes3_37.map decodeEndpoint3)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint3_36 hEndpoint3_37).trans
      (by decide +kernel)

private abbrev goalSpec3_4_27 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 3) 4))[27-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal3_4_27 : trunkGoalBranches (trunkCatalog.states 3) 4 27 = goalCodes3_4_27.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 3) 4 27 = trunkGoalBranches (trunkCatalog.states 3) 2 17 := by
      apply congrArg (trunkBranches (trunkCatalog.states 3).context)
      decide +kernel
    exact he.trans hGoal3_2_17
  | change trunkBranches (trunkCatalog.states 3).context goalSpec3_4_27 = _
    exact (cachedBranches_eq (trunkCatalog.states 3).context goalSpec3_4_27
      endpointInput3_22 endpointInput3_23 (([bc189] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
      (endpointCodes3_22.map decodeEndpoint3) (endpointCodes3_23.map decodeEndpoint3)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint3_22 hEndpoint3_23).trans
      (by decide +kernel)

private theorem hCut3_2 : (trunkPlanAt (trunkCatalog.states 3) 2).cuts = cutCodes3_2.map decodeThresholdBound := by decide +kernel

private theorem hCut3_3 : (trunkPlanAt (trunkCatalog.states 3) 3).cuts = cutCodes3_3.map decodeThresholdBound := by decide +kernel

private theorem hCut3_4 : (trunkPlanAt (trunkCatalog.states 3) 4).cuts = cutCodes3_4.map decodeThresholdBound := by decide +kernel

private def codedGoals3 (pi goal : ℕ) : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) :=
  if pi = 2 ∧ goal = 14 then goalCodes3_2_14 else
  if pi = 2 ∧ goal = 17 then goalCodes3_2_17 else
  if pi = 2 ∧ goal = 19 then goalCodes3_2_19 else
  if pi = 2 ∧ goal = 0 then goalCodes3_2_0 else
  if pi = 2 ∧ goal = 5 then goalCodes3_2_5 else
  if pi = 2 ∧ goal = 10 then goalCodes3_2_10 else
  if pi = 2 ∧ goal = 12 then goalCodes3_2_12 else
  if pi = 2 ∧ goal = 22 then goalCodes3_2_22 else
  if pi = 3 ∧ goal = 0 then goalCodes3_3_0 else
  if pi = 3 ∧ goal = 2 then goalCodes3_3_2 else
  if pi = 3 ∧ goal = 5 then goalCodes3_3_5 else
  if pi = 3 ∧ goal = 7 then goalCodes3_3_7 else
  if pi = 3 ∧ goal = 9 then goalCodes3_3_9 else
  if pi = 3 ∧ goal = 12 then goalCodes3_3_12 else
  if pi = 3 ∧ goal = 14 then goalCodes3_3_14 else
  if pi = 3 ∧ goal = 17 then goalCodes3_3_17 else
  if pi = 3 ∧ goal = 19 then goalCodes3_3_19 else
  if pi = 3 ∧ goal = 22 then goalCodes3_3_22 else
  if pi = 3 ∧ goal = 24 then goalCodes3_3_24 else
  if pi = 3 ∧ goal = 27 then goalCodes3_3_27 else
  if pi = 3 ∧ goal = 29 then goalCodes3_3_29 else
  if pi = 3 ∧ goal = 32 then goalCodes3_3_32 else
  if pi = 3 ∧ goal = 34 then goalCodes3_3_34 else
  if pi = 3 ∧ goal = 35 then goalCodes3_3_35 else
  if pi = 3 ∧ goal = 36 then goalCodes3_3_36 else
  if pi = 3 ∧ goal = 38 then goalCodes3_3_38 else
  if pi = 3 ∧ goal = 39 then goalCodes3_3_39 else
  if pi = 3 ∧ goal = 40 then goalCodes3_3_40 else
  if pi = 3 ∧ goal = 41 then goalCodes3_3_41 else
  if pi = 4 ∧ goal = 0 then goalCodes3_4_0 else
  if pi = 4 ∧ goal = 2 then goalCodes3_4_2 else
  if pi = 4 ∧ goal = 5 then goalCodes3_4_5 else
  if pi = 4 ∧ goal = 7 then goalCodes3_4_7 else
  if pi = 4 ∧ goal = 9 then goalCodes3_4_9 else
  if pi = 4 ∧ goal = 12 then goalCodes3_4_12 else
  if pi = 4 ∧ goal = 15 then goalCodes3_4_15 else
  if pi = 4 ∧ goal = 17 then goalCodes3_4_17 else
  if pi = 4 ∧ goal = 19 then goalCodes3_4_19 else
  if pi = 4 ∧ goal = 22 then goalCodes3_4_22 else
  if pi = 4 ∧ goal = 24 then goalCodes3_4_24 else
  if pi = 4 ∧ goal = 27 then goalCodes3_4_27 else
  []

private def codedKeys3 : List (ℕ × ℕ) := [(2, 14), (2, 17), (2, 19), (2, 0), (2, 5), (2, 10), (2, 12), (2, 22), (3, 0), (3, 2), (3, 5), (3, 7), (3, 9), (3, 12), (3, 14), (3, 17), (3, 19), (3, 22), (3, 24), (3, 27), (3, 29), (3, 32), (3, 34), (3, 35), (3, 36), (3, 38), (3, 39), (3, 40), (3, 41), (4, 0), (4, 2), (4, 5), (4, 7), (4, 9), (4, 12), (4, 15), (4, 17), (4, 19), (4, 22), (4, 24), (4, 27)]

private theorem hCodedGoals3 (pi goal : ℕ) (hm : (pi,goal) ∈ codedKeys3) : trunkGoalBranches (trunkCatalog.states 3) pi goal = (codedGoals3 pi goal).map decodeGoalBranch := by
  unfold codedGoals3
  by_cases h0 : pi = 2 ∧ goal = 14
  · rw [if_pos h0]
    rcases h0 with ⟨rfl,rfl⟩
    exact hGoal3_2_14
  rw [if_neg h0]
  by_cases h1 : pi = 2 ∧ goal = 17
  · rw [if_pos h1]
    rcases h1 with ⟨rfl,rfl⟩
    exact hGoal3_2_17
  rw [if_neg h1]
  by_cases h2 : pi = 2 ∧ goal = 19
  · rw [if_pos h2]
    rcases h2 with ⟨rfl,rfl⟩
    exact hGoal3_2_19
  rw [if_neg h2]
  by_cases h3 : pi = 2 ∧ goal = 0
  · rw [if_pos h3]
    rcases h3 with ⟨rfl,rfl⟩
    exact hGoal3_2_0
  rw [if_neg h3]
  by_cases h4 : pi = 2 ∧ goal = 5
  · rw [if_pos h4]
    rcases h4 with ⟨rfl,rfl⟩
    exact hGoal3_2_5
  rw [if_neg h4]
  by_cases h5 : pi = 2 ∧ goal = 10
  · rw [if_pos h5]
    rcases h5 with ⟨rfl,rfl⟩
    exact hGoal3_2_10
  rw [if_neg h5]
  by_cases h6 : pi = 2 ∧ goal = 12
  · rw [if_pos h6]
    rcases h6 with ⟨rfl,rfl⟩
    exact hGoal3_2_12
  rw [if_neg h6]
  by_cases h7 : pi = 2 ∧ goal = 22
  · rw [if_pos h7]
    rcases h7 with ⟨rfl,rfl⟩
    exact hGoal3_2_22
  rw [if_neg h7]
  by_cases h8 : pi = 3 ∧ goal = 0
  · rw [if_pos h8]
    rcases h8 with ⟨rfl,rfl⟩
    exact hGoal3_3_0
  rw [if_neg h8]
  by_cases h9 : pi = 3 ∧ goal = 2
  · rw [if_pos h9]
    rcases h9 with ⟨rfl,rfl⟩
    exact hGoal3_3_2
  rw [if_neg h9]
  by_cases h10 : pi = 3 ∧ goal = 5
  · rw [if_pos h10]
    rcases h10 with ⟨rfl,rfl⟩
    exact hGoal3_3_5
  rw [if_neg h10]
  by_cases h11 : pi = 3 ∧ goal = 7
  · rw [if_pos h11]
    rcases h11 with ⟨rfl,rfl⟩
    exact hGoal3_3_7
  rw [if_neg h11]
  by_cases h12 : pi = 3 ∧ goal = 9
  · rw [if_pos h12]
    rcases h12 with ⟨rfl,rfl⟩
    exact hGoal3_3_9
  rw [if_neg h12]
  by_cases h13 : pi = 3 ∧ goal = 12
  · rw [if_pos h13]
    rcases h13 with ⟨rfl,rfl⟩
    exact hGoal3_3_12
  rw [if_neg h13]
  by_cases h14 : pi = 3 ∧ goal = 14
  · rw [if_pos h14]
    rcases h14 with ⟨rfl,rfl⟩
    exact hGoal3_3_14
  rw [if_neg h14]
  by_cases h15 : pi = 3 ∧ goal = 17
  · rw [if_pos h15]
    rcases h15 with ⟨rfl,rfl⟩
    exact hGoal3_3_17
  rw [if_neg h15]
  by_cases h16 : pi = 3 ∧ goal = 19
  · rw [if_pos h16]
    rcases h16 with ⟨rfl,rfl⟩
    exact hGoal3_3_19
  rw [if_neg h16]
  by_cases h17 : pi = 3 ∧ goal = 22
  · rw [if_pos h17]
    rcases h17 with ⟨rfl,rfl⟩
    exact hGoal3_3_22
  rw [if_neg h17]
  by_cases h18 : pi = 3 ∧ goal = 24
  · rw [if_pos h18]
    rcases h18 with ⟨rfl,rfl⟩
    exact hGoal3_3_24
  rw [if_neg h18]
  by_cases h19 : pi = 3 ∧ goal = 27
  · rw [if_pos h19]
    rcases h19 with ⟨rfl,rfl⟩
    exact hGoal3_3_27
  rw [if_neg h19]
  by_cases h20 : pi = 3 ∧ goal = 29
  · rw [if_pos h20]
    rcases h20 with ⟨rfl,rfl⟩
    exact hGoal3_3_29
  rw [if_neg h20]
  by_cases h21 : pi = 3 ∧ goal = 32
  · rw [if_pos h21]
    rcases h21 with ⟨rfl,rfl⟩
    exact hGoal3_3_32
  rw [if_neg h21]
  by_cases h22 : pi = 3 ∧ goal = 34
  · rw [if_pos h22]
    rcases h22 with ⟨rfl,rfl⟩
    exact hGoal3_3_34
  rw [if_neg h22]
  by_cases h23 : pi = 3 ∧ goal = 35
  · rw [if_pos h23]
    rcases h23 with ⟨rfl,rfl⟩
    exact hGoal3_3_35
  rw [if_neg h23]
  by_cases h24 : pi = 3 ∧ goal = 36
  · rw [if_pos h24]
    rcases h24 with ⟨rfl,rfl⟩
    exact hGoal3_3_36
  rw [if_neg h24]
  by_cases h25 : pi = 3 ∧ goal = 38
  · rw [if_pos h25]
    rcases h25 with ⟨rfl,rfl⟩
    exact hGoal3_3_38
  rw [if_neg h25]
  by_cases h26 : pi = 3 ∧ goal = 39
  · rw [if_pos h26]
    rcases h26 with ⟨rfl,rfl⟩
    exact hGoal3_3_39
  rw [if_neg h26]
  by_cases h27 : pi = 3 ∧ goal = 40
  · rw [if_pos h27]
    rcases h27 with ⟨rfl,rfl⟩
    exact hGoal3_3_40
  rw [if_neg h27]
  by_cases h28 : pi = 3 ∧ goal = 41
  · rw [if_pos h28]
    rcases h28 with ⟨rfl,rfl⟩
    exact hGoal3_3_41
  rw [if_neg h28]
  by_cases h29 : pi = 4 ∧ goal = 0
  · rw [if_pos h29]
    rcases h29 with ⟨rfl,rfl⟩
    exact hGoal3_4_0
  rw [if_neg h29]
  by_cases h30 : pi = 4 ∧ goal = 2
  · rw [if_pos h30]
    rcases h30 with ⟨rfl,rfl⟩
    exact hGoal3_4_2
  rw [if_neg h30]
  by_cases h31 : pi = 4 ∧ goal = 5
  · rw [if_pos h31]
    rcases h31 with ⟨rfl,rfl⟩
    exact hGoal3_4_5
  rw [if_neg h31]
  by_cases h32 : pi = 4 ∧ goal = 7
  · rw [if_pos h32]
    rcases h32 with ⟨rfl,rfl⟩
    exact hGoal3_4_7
  rw [if_neg h32]
  by_cases h33 : pi = 4 ∧ goal = 9
  · rw [if_pos h33]
    rcases h33 with ⟨rfl,rfl⟩
    exact hGoal3_4_9
  rw [if_neg h33]
  by_cases h34 : pi = 4 ∧ goal = 12
  · rw [if_pos h34]
    rcases h34 with ⟨rfl,rfl⟩
    exact hGoal3_4_12
  rw [if_neg h34]
  by_cases h35 : pi = 4 ∧ goal = 15
  · rw [if_pos h35]
    rcases h35 with ⟨rfl,rfl⟩
    exact hGoal3_4_15
  rw [if_neg h35]
  by_cases h36 : pi = 4 ∧ goal = 17
  · rw [if_pos h36]
    rcases h36 with ⟨rfl,rfl⟩
    exact hGoal3_4_17
  rw [if_neg h36]
  by_cases h37 : pi = 4 ∧ goal = 19
  · rw [if_pos h37]
    rcases h37 with ⟨rfl,rfl⟩
    exact hGoal3_4_19
  rw [if_neg h37]
  by_cases h38 : pi = 4 ∧ goal = 22
  · rw [if_pos h38]
    rcases h38 with ⟨rfl,rfl⟩
    exact hGoal3_4_22
  rw [if_neg h38]
  by_cases h39 : pi = 4 ∧ goal = 24
  · rw [if_pos h39]
    rcases h39 with ⟨rfl,rfl⟩
    exact hGoal3_4_24
  rw [if_neg h39]
  by_cases h40 : pi = 4 ∧ goal = 27
  · rw [if_pos h40]
    rcases h40 with ⟨rfl,rfl⟩
    exact hGoal3_4_27
  rw [if_neg h40]
  simp_all only [codedKeys3,List.mem_cons,List.mem_nil_iff,or_false,Prod.mk.injEq]

private def codedCuts3 (pi : ℕ) : List (ℕ × Bool × Bool) :=
  if pi = 2 then cutCodes3_2 else
  if pi = 3 then cutCodes3_3 else
  if pi = 4 then cutCodes3_4 else
  []

private theorem hCodedCuts3 (pi goal : ℕ) (hm : (pi,goal) ∈ codedKeys3) : (trunkPlanAt (trunkCatalog.states 3) pi).cuts = (codedCuts3 pi).map decodeThresholdBound := by
  unfold codedCuts3
  by_cases h0 : pi = 2
  · rw [if_pos h0]
    subst pi
    exact hCut3_2
  rw [if_neg h0]
  by_cases h1 : pi = 3
  · rw [if_pos h1]
    subst pi
    exact hCut3_3
  rw [if_neg h1]
  by_cases h2 : pi = 4
  · rw [if_pos h2]
    subst pi
    exact hCut3_4
  rw [if_neg h2]
  simp_all only [codedKeys3,List.mem_cons,List.mem_nil_iff,or_false,Prod.mk.injEq,false_and]

private def codedValid3 (g : TrunkGroup) : Prop := (g.plan,g.goal) ∈ codedKeys3 ∧ codeGroupValid (trunkCatalog.states 3) codedParents3 100 codedCuts3 codedGoals3 g

private theorem codedValid3_sound (g : TrunkGroup) (h : codedValid3 g) : trunkGroupValidFast 3 g :=
  codeGroupValid_sound 3 codedParents3 100 codedCuts3 codedGoals3 g hCodedParents3 hCodedParentLength3 (hCodedCuts3 g.plan g.goal h.1) (hCodedGoals3 g.plan g.goal h.1) h.2



set_option Elab.async false
theorem batch_chunk_0 : ∀ j ∈ List.range 20, codedValid3 (trunkStateData03Part02.getD j ⟨0,[],0,[]⟩) := by
  unfold codedValid3 codeGroupValid
  decide +kernel

theorem batch_chunk_20 : ∀ j ∈ List.range' 20 20, codedValid3 (trunkStateData03Part02.getD j ⟨0,[],0,[]⟩) := by
  unfold codedValid3 codeGroupValid
  decide +kernel

theorem batch_chunk_40 : ∀ j ∈ List.range' 40 20, codedValid3 (trunkStateData03Part02.getD j ⟨0,[],0,[]⟩) := by
  unfold codedValid3 codeGroupValid
  decide +kernel

theorem batch_chunk_60 : ∀ j ∈ List.range' 60 20, codedValid3 (trunkStateData03Part02.getD j ⟨0,[],0,[]⟩) := by
  unfold codedValid3 codeGroupValid
  decide +kernel

theorem batch_chunk_80 : ∀ j ∈ List.range' 80 20, codedValid3 (trunkStateData03Part02.getD j ⟨0,[],0,[]⟩) := by
  unfold codedValid3 codeGroupValid
  decide +kernel

theorem batch_key (j : ℕ) (hj : j < 100) : codedValid3 (trunkStateData03Part02.getD j ⟨0,[],0,[]⟩) := by
  rcases lt_or_ge j 20 with h0 | h0
  · exact batch_chunk_0 j (List.mem_range.2 (by omega))
  rcases lt_or_ge j 40 with h1 | h1
  · exact batch_chunk_20 j (List.mem_range'.2 ⟨j - 20, by omega, by omega⟩)
  rcases lt_or_ge j 60 with h2 | h2
  · exact batch_chunk_40 j (List.mem_range'.2 ⟨j - 40, by omega, by omega⟩)
  rcases lt_or_ge j 80 with h3 | h3
  · exact batch_chunk_60 j (List.mem_range'.2 ⟨j - 60, by omega, by omega⟩)
  · exact batch_chunk_80 j (List.mem_range'.2 ⟨j - 80, by omega, by omega⟩)

theorem part_length_1 : trunkStateData03Part01.length = 100 := by decide +kernel

theorem part_length_2 : trunkStateData03Part02.length = 100 := by decide +kernel

theorem solution : trunkBindingBatch 3 100 200 := by
  intro i hlo hhi g hg
  change (trunkStateData03Part01 ++ trunkStateData03Part02 ++ trunkStateData03Part03)[i]? = some g at hg
  rw [List.getElem?_append_left (show i < (trunkStateData03Part01 ++ trunkStateData03Part02).length by simp only [List.length_append, part_length_1, part_length_2, Nat.reduceAdd]; omega)] at hg
  rw [List.getElem?_append_right (show (trunkStateData03Part01).length ≤ i by simp only [List.length_append, part_length_1, part_length_2, Nat.reduceAdd]; omega)] at hg
  simp only [List.length_append, part_length_1, part_length_2, Nat.reduceAdd] at hg
  have hgi := batch_key (i - 100) (by omega)
  have hgv : trunkStateData03Part02.getD (i - 100) ⟨0,[],0,[]⟩ = g := by
    try simp only [Nat.sub_zero]
    rw [List.getD_eq_getElem?_getD, hg]; rfl
  rw [hgv] at hgi
  exact Freiman.trunkFast_correctness.2 3 hPar3 g (codedValid3_sound g hgi)

#print axioms solution
