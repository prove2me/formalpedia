-- Prove2me | solution 1 for Freiman.trunk_bindings_08_100_200
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:23:11.34547+00:00
-- url     : https://prove2.me/submissions/97f123a0-ba65-4438-ba08-639b3a5de3f6

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
private abbrev bc34 : ℕ × Bool × Bool := (89, false, true)
private abbrev bc35 : ℕ × Bool × Bool := (91, false, true)
private abbrev bc36 : ℕ × Bool × Bool := (91, true, false)
private abbrev bc37 : ℕ × Bool × Bool := (89, true, false)
private abbrev bc38 : ℕ × Bool × Bool := (102, true, true)
private abbrev bc39 : ℕ × Bool × Bool := (102, false, false)
private abbrev bc40 : ℕ × Bool × Bool := (30, false, true)
private abbrev bc41 : ℕ × Bool × Bool := (90, false, true)
private abbrev bc42 : ℕ × Bool × Bool := (90, true, false)
private abbrev bc43 : ℕ × Bool × Bool := (30, true, false)
private abbrev bc44 : ℕ × Bool × Bool := (95, true, true)
private abbrev bc45 : ℕ × Bool × Bool := (95, false, false)
private abbrev bc46 : ℕ × Bool × Bool := (183, false, false)
private abbrev bc47 : ℕ × Bool × Bool := (182, false, false)
private abbrev bc48 : ℕ × Bool × Bool := (179, false, true)
private abbrev bc49 : ℕ × Bool × Bool := (179, true, false)
private abbrev bc50 : ℕ × Bool × Bool := (182, true, true)
private abbrev bc51 : ℕ × Bool × Bool := (197, true, true)
private abbrev bc52 : ℕ × Bool × Bool := (197, false, false)
private abbrev bc53 : ℕ × Bool × Bool := (183, true, true)
private abbrev bc54 : ℕ × Bool × Bool := (181, false, false)
private abbrev bc55 : ℕ × Bool × Bool := (181, true, true)
private abbrev bc56 : ℕ × Bool × Bool := (184, false, false)
private abbrev bc57 : ℕ × Bool × Bool := (186, false, true)
private abbrev bc58 : ℕ × Bool × Bool := (186, true, false)
private abbrev bc59 : ℕ × Bool × Bool := (184, true, true)
private abbrev bc60 : ℕ × Bool × Bool := (189, true, true)
private abbrev bc61 : ℕ × Bool × Bool := (189, false, false)
private abbrev bc62 : ℕ × Bool × Bool := (206, true, false)
private abbrev bc63 : ℕ × Bool × Bool := (210, false, true)
private abbrev bc64 : ℕ × Bool × Bool := (210, true, false)
private abbrev bc65 : ℕ × Bool × Bool := (205, false, true)
private abbrev bc66 : ℕ × Bool × Bool := (205, true, false)
private abbrev bc67 : ℕ × Bool × Bool := (132, false, false)
private abbrev bc68 : ℕ × Bool × Bool := (133, false, true)
private abbrev bc69 : ℕ × Bool × Bool := (133, true, false)
private abbrev bc70 : ℕ × Bool × Bool := (132, true, true)
private abbrev bc71 : ℕ × Bool × Bool := (136, true, true)
private abbrev bc72 : ℕ × Bool × Bool := (136, false, false)
private abbrev bc73 : ℕ × Bool × Bool := (8, false, false)
private abbrev bc74 : ℕ × Bool × Bool := (176, false, true)
private abbrev bc75 : ℕ × Bool × Bool := (8, true, true)
private abbrev bc76 : ℕ × Bool × Bool := (233, false, false)
private abbrev bc77 : ℕ × Bool × Bool := (233, true, true)
private abbrev bc78 : ℕ × Bool × Bool := (234, false, false)
private abbrev bc79 : ℕ × Bool × Bool := (236, false, false)
private abbrev bc80 : ℕ × Bool × Bool := (236, true, true)
private abbrev bc81 : ℕ × Bool × Bool := (246, false, true)
private abbrev bc82 : ℕ × Bool × Bool := (246, true, false)
private abbrev bc83 : ℕ × Bool × Bool := (248, true, false)
private abbrev bc84 : ℕ × Bool × Bool := (251, false, true)
private abbrev bc85 : ℕ × Bool × Bool := (251, true, false)
private abbrev bc86 : ℕ × Bool × Bool := (260, false, false)
private abbrev bc87 : ℕ × Bool × Bool := (261, false, false)
private abbrev bc88 : ℕ × Bool × Bool := (261, true, true)
private abbrev bc89 : ℕ × Bool × Bool := (263, false, false)
private abbrev bc90 : ℕ × Bool × Bool := (263, true, true)
private abbrev bc91 : ℕ × Bool × Bool := (275, true, false)
private abbrev bc92 : ℕ × Bool × Bool := (279, false, true)
private abbrev bc93 : ℕ × Bool × Bool := (279, true, false)
private abbrev bc94 : ℕ × Bool × Bool := (274, false, true)
private abbrev bc95 : ℕ × Bool × Bool := (274, true, false)
private abbrev bc96 : ℕ × Bool × Bool := (235, false, false)
private abbrev bc97 : ℕ × Bool × Bool := (288, false, true)
private abbrev bc98 : ℕ × Bool × Bool := (288, true, false)
private abbrev bc99 : ℕ × Bool × Bool := (235, true, true)
private abbrev bc100 : ℕ × Bool × Bool := (291, true, true)
private abbrev bc101 : ℕ × Bool × Bool := (291, false, false)
private abbrev bc102 : ℕ × Bool × Bool := (297, false, false)
private abbrev bc103 : ℕ × Bool × Bool := (298, false, false)
private abbrev bc104 : ℕ × Bool × Bool := (69, false, true)
private abbrev bc105 : ℕ × Bool × Bool := (69, true, false)
private abbrev bc106 : ℕ × Bool × Bool := (298, true, true)
private abbrev bc107 : ℕ × Bool × Bool := (83, true, true)
private abbrev bc108 : ℕ × Bool × Bool := (83, false, false)
private abbrev bc109 : ℕ × Bool × Bool := (297, true, true)
private abbrev bc110 : ℕ × Bool × Bool := (299, false, false)
private abbrev bc111 : ℕ × Bool × Bool := (299, true, true)
private abbrev bc112 : ℕ × Bool × Bool := (301, false, false)
private abbrev bc113 : ℕ × Bool × Bool := (303, false, true)
private abbrev bc114 : ℕ × Bool × Bool := (303, true, false)
private abbrev bc115 : ℕ × Bool × Bool := (301, true, true)
private abbrev bc116 : ℕ × Bool × Bool := (307, true, true)
private abbrev bc117 : ℕ × Bool × Bool := (307, false, false)
private abbrev bc118 : ℕ × Bool × Bool := (319, false, true)
private abbrev bc119 : ℕ × Bool × Bool := (319, true, false)
private abbrev bc120 : ℕ × Bool × Bool := (331, false, true)
private abbrev bc121 : ℕ × Bool × Bool := (332, false, true)
private abbrev bc122 : ℕ × Bool × Bool := (332, true, false)
private abbrev bc123 : ℕ × Bool × Bool := (331, true, false)
private abbrev bc124 : ℕ × Bool × Bool := (337, true, true)
private abbrev bc125 : ℕ × Bool × Bool := (337, false, false)
private abbrev bc126 : ℕ × Bool × Bool := (320, false, true)
private abbrev bc127 : ℕ × Bool × Bool := (322, false, true)
private abbrev bc128 : ℕ × Bool × Bool := (321, false, true)
private abbrev bc129 : ℕ × Bool × Bool := (321, true, false)
private abbrev bc130 : ℕ × Bool × Bool := (322, true, false)
private abbrev bc131 : ℕ × Bool × Bool := (325, true, true)
private abbrev bc132 : ℕ × Bool × Bool := (325, false, false)
private abbrev bc133 : ℕ × Bool × Bool := (320, true, false)
private abbrev bc134 : ℕ × Bool × Bool := (344, false, false)
private abbrev bc135 : ℕ × Bool × Bool := (343, false, false)
private abbrev bc136 : ℕ × Bool × Bool := (113, false, true)
private abbrev bc137 : ℕ × Bool × Bool := (113, true, false)
private abbrev bc138 : ℕ × Bool × Bool := (343, true, true)
private abbrev bc139 : ℕ × Bool × Bool := (125, true, true)
private abbrev bc140 : ℕ × Bool × Bool := (125, false, false)
private abbrev bc141 : ℕ × Bool × Bool := (344, true, true)
private abbrev bc142 : ℕ × Bool × Bool := (346, false, false)
private abbrev bc143 : ℕ × Bool × Bool := (346, true, true)
private abbrev bc144 : ℕ × Bool × Bool := (347, false, false)
private abbrev bc145 : ℕ × Bool × Bool := (349, false, true)
private abbrev bc146 : ℕ × Bool × Bool := (349, true, false)
private abbrev bc147 : ℕ × Bool × Bool := (347, true, true)
private abbrev bc148 : ℕ × Bool × Bool := (352, true, true)
private abbrev bc149 : ℕ × Bool × Bool := (352, false, false)
private abbrev bc150 : ℕ × Bool × Bool := (365, true, false)
private abbrev bc151 : ℕ × Bool × Bool := (369, false, true)
private abbrev bc152 : ℕ × Bool × Bool := (369, true, false)
private abbrev bc153 : ℕ × Bool × Bool := (366, false, true)
private abbrev bc154 : ℕ × Bool × Bool := (366, true, false)
private abbrev bc155 : ℕ × Bool × Bool := (380, false, false)
private abbrev bc156 : ℕ × Bool × Bool := (379, false, false)
private abbrev bc157 : ℕ × Bool × Bool := (377, false, true)
private abbrev bc158 : ℕ × Bool × Bool := (377, true, false)
private abbrev bc159 : ℕ × Bool × Bool := (379, true, true)
private abbrev bc160 : ℕ × Bool × Bool := (395, true, true)
private abbrev bc161 : ℕ × Bool × Bool := (395, false, false)
private abbrev bc162 : ℕ × Bool × Bool := (380, true, true)
private abbrev bc163 : ℕ × Bool × Bool := (381, false, false)
private abbrev bc164 : ℕ × Bool × Bool := (381, true, true)
private abbrev bc165 : ℕ × Bool × Bool := (384, false, false)
private abbrev bc166 : ℕ × Bool × Bool := (383, false, true)
private abbrev bc167 : ℕ × Bool × Bool := (383, true, false)
private abbrev bc168 : ℕ × Bool × Bool := (384, true, true)
private abbrev bc169 : ℕ × Bool × Bool := (388, true, true)
private abbrev bc170 : ℕ × Bool × Bool := (388, false, false)
private abbrev bc171 : ℕ × Bool × Bool := (405, false, true)
private abbrev bc172 : ℕ × Bool × Bool := (405, true, false)
private abbrev bc173 : ℕ × Bool × Bool := (415, false, true)
private abbrev bc174 : ℕ × Bool × Bool := (414, false, true)
private abbrev bc175 : ℕ × Bool × Bool := (414, true, false)
private abbrev bc176 : ℕ × Bool × Bool := (415, true, false)
private abbrev bc177 : ℕ × Bool × Bool := (421, true, true)
private abbrev bc178 : ℕ × Bool × Bool := (421, false, false)
private abbrev bc179 : ℕ × Bool × Bool := (404, false, true)
private abbrev bc180 : ℕ × Bool × Bool := (406, false, true)
private abbrev bc181 : ℕ × Bool × Bool := (403, false, true)
private abbrev bc182 : ℕ × Bool × Bool := (403, true, false)
private abbrev bc183 : ℕ × Bool × Bool := (406, true, false)
private abbrev bc184 : ℕ × Bool × Bool := (409, true, true)
private abbrev bc185 : ℕ × Bool × Bool := (409, false, false)
private abbrev bc186 : ℕ × Bool × Bool := (404, true, false)
private abbrev bc187 : ℕ × Bool × Bool := (432, false, false)
private abbrev bc188 : ℕ × Bool × Bool := (430, false, false)
private abbrev bc189 : ℕ × Bool × Bool := (430, true, true)
private abbrev bc190 : ℕ × Bool × Bool := (428, false, false)
private abbrev bc191 : ℕ × Bool × Bool := (428, true, true)
private abbrev bc192 : ℕ × Bool × Bool := (443, false, true)
private abbrev bc193 : ℕ × Bool × Bool := (443, true, false)
private abbrev bc194 : ℕ × Bool × Bool := (455, false, true)
private abbrev bc195 : ℕ × Bool × Bool := (456, false, true)
private abbrev bc196 : ℕ × Bool × Bool := (456, true, false)
private abbrev bc197 : ℕ × Bool × Bool := (455, true, false)
private abbrev bc198 : ℕ × Bool × Bool := (461, true, true)
private abbrev bc199 : ℕ × Bool × Bool := (461, false, false)
private abbrev bc200 : ℕ × Bool × Bool := (446, false, true)
private abbrev bc201 : ℕ × Bool × Bool := (445, false, true)
private abbrev bc202 : ℕ × Bool × Bool := (444, false, true)
private abbrev bc203 : ℕ × Bool × Bool := (444, true, false)
private abbrev bc204 : ℕ × Bool × Bool := (445, true, false)
private abbrev bc205 : ℕ × Bool × Bool := (449, true, true)
private abbrev bc206 : ℕ × Bool × Bool := (449, false, false)
private abbrev bc207 : ℕ × Bool × Bool := (446, true, false)
private abbrev bc208 : ℕ × Bool × Bool := (156, false, false)
private abbrev bc209 : ℕ × Bool × Bool := (155, false, true)
private abbrev bc210 : ℕ × Bool × Bool := (155, true, false)
private abbrev bc211 : ℕ × Bool × Bool := (156, true, true)
private abbrev bc212 : ℕ × Bool × Bool := (162, true, true)
private abbrev bc213 : ℕ × Bool × Bool := (162, false, false)
private abbrev bc214 : ℕ × Bool × Bool := (89, false, false)
private abbrev bc215 : ℕ × Bool × Bool := (476, false, true)
private abbrev bc216 : ℕ × Bool × Bool := (476, true, false)
private abbrev bc217 : ℕ × Bool × Bool := (89, true, true)
private abbrev bc218 : ℕ × Bool × Bool := (479, true, true)
private abbrev bc219 : ℕ × Bool × Bool := (479, false, false)
private abbrev bc220 : ℕ × Bool × Bool := (431, false, false)
private abbrev bc221 : ℕ × Bool × Bool := (490, false, true)
private abbrev bc222 : ℕ × Bool × Bool := (490, true, false)
private abbrev bc223 : ℕ × Bool × Bool := (431, true, true)
private abbrev bc224 : ℕ × Bool × Bool := (497, true, true)
private abbrev bc225 : ℕ × Bool × Bool := (497, false, false)
private abbrev bc226 : ℕ × Bool × Bool := (1, true, false)
private abbrev bc227 : ℕ × Bool × Bool := (23, true, false)
private abbrev bc228 : ℕ × Bool × Bool := (27, true, false)
private abbrev bc229 : ℕ × Bool × Bool := (143, true, false)
private abbrev bc230 : ℕ × Bool × Bool := (145, true, false)
private abbrev bc231 : ℕ × Bool × Bool := (146, true, false)
private abbrev bc232 : ℕ × Bool × Bool := (148, true, false)
private abbrev bc233 : ℕ × Bool × Bool := (150, true, false)
private abbrev bc234 : ℕ × Bool × Bool := (151, true, false)
private abbrev bc235 : ℕ × Bool × Bool := (34, true, true)
private abbrev bc236 : ℕ × Bool × Bool := (88, false, true)
private abbrev bc237 : ℕ × Bool × Bool := (180, true, true)
private abbrev bc238 : ℕ × Bool × Bool := (204, false, true)
private abbrev bc239 : ℕ × Bool × Bool := (232, true, true)
private abbrev bc240 : ℕ × Bool × Bool := (245, false, true)
private abbrev bc241 : ℕ × Bool × Bool := (262, false, false)
private abbrev bc242 : ℕ × Bool × Bool := (264, true, true)
private abbrev bc243 : ℕ × Bool × Bool := (262, true, true)
private abbrev bc244 : ℕ × Bool × Bool := (273, false, true)
private abbrev bc245 : ℕ × Bool × Bool := (217, true, false)
private abbrev bc246 : ℕ × Bool × Bool := (300, true, true)
private abbrev bc247 : ℕ × Bool × Bool := (318, false, true)
private abbrev bc248 : ℕ × Bool × Bool := (345, true, true)
private abbrev bc249 : ℕ × Bool × Bool := (364, false, true)
private abbrev bc250 : ℕ × Bool × Bool := (378, true, true)
private abbrev bc251 : ℕ × Bool × Bool := (402, false, true)
private abbrev bc252 : ℕ × Bool × Bool := (429, true, true)
private abbrev bc253 : ℕ × Bool × Bool := (441, false, true)
private abbrev bc254 : ℕ × Bool × Bool := (467, true, false)
private abbrev bc255 : ℕ × Bool × Bool := (153, true, false)
private abbrev bc256 : ℕ × Bool × Bool := (489, false, false)

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

private def codesA8 : List (List ℕ × Option (Option ℕ)) := [([112911326, 882722351, 131368818, 335455726], some (some 948335893)),
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
private def codesB8 : List (List ℕ × Option (Option ℕ)) := [([882722351, 112911326, 475598846, 413245293], some none),
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
private def endpointFields8 : Array CertField := #[⟨(4/13),(1/13),(0/1),(0/1)⟩,⟨(1/2),(1/6),(0/1),(0/1)⟩,⟨(52/73),(1/73),(0/1),(0/1)⟩,⟨(89/214),(1/214),(0/1),(0/1)⟩,⟨(9/13),(-1/13),(0/1),(0/1)⟩,⟨(2/1),(-1/1),(0/1),(0/1)⟩,⟨(15/37),(-1/37),(0/1),(0/1)⟩,⟨(125/214),(-1/214),(0/1),(0/1)⟩,⟨(66/179),(-1/537),(0/1),(0/1)⟩,⟨(22/37),(1/37),(0/1),(0/1)⟩,⟨(113/179),(1/537),(0/1),(0/1)⟩,⟨(17/22),(-1/22),(0/1),(0/1)⟩,⟨(101/143),(-1/429),(0/1),(0/1)⟩,⟨(35/94),(1/94),(0/1),(0/1)⟩,⟨(553/1429),(1/1429),(0/1),(0/1)⟩,⟨(10/23),(-1/69),(0/1),(0/1)⟩,⟨(517/1249),(-1/1249),(0/1),(0/1)⟩,⟨(16/59),(1/177),(0/1),(0/1)⟩,⟨(767/2749),(1/2749),(0/1),(0/1)⟩,⟨(43/142),(-1/142),(0/1),(0/1)⟩,⟨(731/2497),(-1/2497),(0/1),(0/1)⟩,⟨(5/22),(1/22),(0/1),(0/1)⟩,⟨(42/143),(1/429),(0/1),(0/1)⟩,⟨(271/1006),(-1/1006),(0/1),(0/1)⟩,⟨(469/1549),(1/1549),(0/1),(0/1)⟩,⟨(3289/10753),(1/10753),(0/1),(0/1)⟩,⟨(579/1894),(-1/1894),(0/1),(0/1)⟩,⟨(71/229),(-1/229),(0/1),(0/1)⟩,⟨(1413/4654),(-1/4654),(0/1),(0/1)⟩,⟨(9014/29557),(-1/29557),(0/1),(0/1)⟩,⟨(13/23),(1/69),(0/1),(0/1)⟩,⟨(732/1249),(1/1249),(0/1),(0/1)⟩,⟨(59/94),(-1/94),(0/1),(0/1)⟩]
private abbrev endpointInput8_0 : LowerPair × Bool × Bool := (([2], []), true, false)
private def endpointCodes8_0 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((0, 1), [bc0]),
 ((0, 1), [bc1, bc2, bc3]),
 ((0, 2), [bc1, bc2, bc4]),
 ((0, 1), [bc1, bc5, bc6]),
 ((3, 1), [bc1, bc5, bc7])]
private abbrev endpointInput8_1 : LowerPair × Bool × Bool := (([1], []), false, false)
private def endpointCodes8_1 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((4, 5), [bc8, bc9, bc10]),
 ((4, 6), [bc8, bc9, bc11]),
 ((4, 5), [bc8, bc12, bc13]),
 ((7, 5), [bc8, bc12, bc14]),
 ((4, 5), [bc15])]
private abbrev endpointInput8_2 : LowerPair × Bool × Bool := (([1], []), true, false)
private def endpointCodes8_2 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((2, 1), [bc8]), ((2, 1), [bc15])]
private abbrev endpointInput8_3 : LowerPair × Bool × Bool := (([2], []), false, false)
private def endpointCodes8_3 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((6, 5), [bc0, bc16, bc17]),
 ((6, 6), [bc0, bc16, bc18]),
 ((6, 5), [bc0, bc19, bc20]),
 ((8, 5), [bc0, bc19, bc21]),
 ((6, 5), [bc1])]
private abbrev endpointInput8_4 : LowerPair × Bool × Bool := (([1, 1], []), true, false)
private def endpointCodes8_4 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((9, 1), [bc9, bc22]),
 ((9, 2), [bc9, bc23]),
 ((9, 1), [bc12, bc24]),
 ((10, 1), [bc12, bc25])]
private abbrev endpointInput8_5 : LowerPair × Bool × Bool := (([1, 2], []), false, false)
private def endpointCodes8_5 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((11, 5), [bc26, bc27]),
 ((11, 6), [bc26, bc28]),
 ((11, 5), [bc29, bc30]),
 ((12, 5), [bc29, bc31])]
private abbrev endpointInput8_6 : LowerPair × Bool × Bool := (([1], [2]), true, true)
private def endpointCodes8_6 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((2, 0), [])]
private abbrev endpointInput8_7 : LowerPair × Bool × Bool := (([1], [1]), false, true)
private def endpointCodes8_7 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((4, 4), [bc32, (52, false, true)]),
 ((4, 7), [bc32, (52, true, false)]),
 ((4, 4), [bc33, (56, true, true)]),
 ((7, 4), [bc33, (56, false, false)])]
private abbrev endpointInput8_10 : LowerPair × Bool × Bool := (([2], [2]), true, true)
private def endpointCodes8_10 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((0, 0), [bc34, bc35]),
 ((0, 3), [bc34, bc36]),
 ((0, 0), [bc37, bc38]),
 ((3, 0), [bc37, bc39])]
private abbrev endpointInput8_11 : LowerPair × Bool × Bool := (([2], [1]), false, true)
private def endpointCodes8_11 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((6, 4), [bc40, bc41]),
 ((6, 7), [bc40, bc42]),
 ((6, 4), [bc43, bc44]),
 ((8, 4), [bc43, bc45])]
private abbrev endpointInput8_17 : LowerPair × Bool × Bool := (([3, 1], [2]), true, false)
private def endpointCodes8_17 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((17, 0), [bc46, bc47, bc48]),
 ((17, 3), [bc46, bc47, bc49]),
 ((17, 0), [bc46, bc50, bc51]),
 ((18, 0), [bc46, bc50, bc52]),
 ((17, 0), [bc53])]
private abbrev endpointInput8_18 : LowerPair × Bool × Bool := (([3, 2], [2]), false, false)
private def endpointCodes8_18 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((19, 6), [bc54]),
 ((19, 6), [bc55, bc56, bc57]),
 ((19, 8), [bc55, bc56, bc58]),
 ((19, 6), [bc55, bc59, bc60]),
 ((20, 6), [bc55, bc59, bc61])]
private abbrev endpointInput8_19 : LowerPair × Bool × Bool := (([3], [2, 1]), true, true)
private def endpointCodes8_19 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((21, 13), [(206, false, true)]),
 ((21, 13), [bc62, bc63, (208, false, true)]),
 ((21, 14), [bc62, bc63, (208, true, false)]),
 ((21, 13), [bc62, bc64, (213, true, true)]),
 ((22, 13), [bc62, bc64, (213, false, false)])]
private abbrev endpointInput8_20 : LowerPair × Bool × Bool := (([3], [2, 2]), false, true)
private def endpointCodes8_20 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((23, 15), [bc65]), ((23, 15), [bc66])]
private abbrev endpointInput8_21 : LowerPair × Bool × Bool := (([3], [2]), true, false)
private def endpointCodes8_21 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((21, 0), [bc67, bc68]),
 ((21, 3), [bc67, bc69]),
 ((21, 0), [bc70, bc71]),
 ((22, 0), [bc70, bc72])]
private abbrev endpointInput8_22 : LowerPair × Bool × Bool := (([], []), false, false)
private def endpointCodes8_22 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((5, 5), [bc73, bc74]),
 ((5, 6), [bc73, (176, true, false)]),
 ((5, 5), [bc75, (228, true, true)]),
 ((6, 5), [bc75, (228, false, false)])]
private abbrev endpointInput8_23 : LowerPair × Bool × Bool := (([3], [2]), false, false)
private def endpointCodes8_23 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((23, 6), [])]
private abbrev endpointInput8_24 : LowerPair × Bool × Bool := (([3, 3, 2], [3, 3]), true, false)
private def endpointCodes8_24 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((24, 25), [bc76]), ((24, 25), [bc77])]
private abbrev endpointInput8_25 : LowerPair × Bool × Bool := (([3, 3, 1], [3, 3]), false, false)
private def endpointCodes8_25 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((26, 27), [bc78, bc79, (231, false, true)]),
 ((26, 28), [bc78, bc79, (231, true, false)]),
 ((26, 27), [bc78, bc80, (239, true, true)]),
 ((29, 27), [bc78, bc80, (239, false, false)]),
 ((26, 27), [(234, true, true)])]
private abbrev endpointInput8_26 : LowerPair × Bool × Bool := (([3, 3], [3, 3, 2]), true, true)
private def endpointCodes8_26 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((25, 24), [bc81]), ((25, 24), [bc82])]
private abbrev endpointInput8_27 : LowerPair × Bool × Bool := (([3, 3], [3, 3, 1]), false, true)
private def endpointCodes8_27 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((27, 26), [(248, false, true)]),
 ((27, 26), [bc83, bc84, (249, false, true)]),
 ((27, 29), [bc83, bc84, (249, true, false)]),
 ((27, 26), [bc83, bc85, (254, true, true)]),
 ((28, 26), [bc83, bc85, (254, false, false)])]
private abbrev endpointInput8_28 : LowerPair × Bool × Bool := (([3, 1], [3]), true, false)
private def endpointCodes8_28 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((17, 21), [bc86, bc87, (259, false, true)]),
 ((17, 22), [bc86, bc87, (259, true, false)]),
 ((17, 21), [bc86, bc88, (269, true, true)]),
 ((18, 21), [bc86, bc88, (269, false, false)]),
 ((17, 21), [(260, true, true)])]
private abbrev endpointInput8_29 : LowerPair × Bool × Bool := (([3, 2], [3]), false, false)
private def endpointCodes8_29 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((19, 23), [bc89]), ((19, 23), [bc90])]
private abbrev endpointInput8_30 : LowerPair × Bool × Bool := (([3], [3, 1]), true, true)
private def endpointCodes8_30 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((21, 17), [(275, false, true)]),
 ((21, 17), [bc91, bc92, (280, false, true)]),
 ((21, 18), [bc91, bc92, (280, true, false)]),
 ((21, 17), [bc91, bc93, (283, true, true)]),
 ((22, 17), [bc91, bc93, (283, false, false)])]
private abbrev endpointInput8_31 : LowerPair × Bool × Bool := (([3], [3, 2]), false, true)
private def endpointCodes8_31 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((23, 19), [bc94]), ((23, 19), [bc95])]
private abbrev endpointInput8_32 : LowerPair × Bool × Bool := (([3, 3], [3, 3]), false, false)
private def endpointCodes8_32 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((27, 27), [bc96, bc97]),
 ((27, 28), [bc96, bc98]),
 ((27, 27), [bc99, bc100]),
 ((28, 27), [bc99, bc101])]
private abbrev endpointInput8_33 : LowerPair × Bool × Bool := (([3, 3], [3, 3]), true, false)
private def endpointCodes8_33 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((25, 25), [])]
private abbrev endpointInput8_34 : LowerPair × Bool × Bool := (([2, 1], [1]), true, false)
private def endpointCodes8_34 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((13, 1), [bc102, bc103, bc104]),
 ((13, 2), [bc102, bc103, bc105]),
 ((13, 1), [bc102, bc106, bc107]),
 ((14, 1), [bc102, bc106, bc108]),
 ((13, 1), [bc109])]
private abbrev endpointInput8_35 : LowerPair × Bool × Bool := (([2, 2], [1]), false, false)
private def endpointCodes8_35 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((15, 4), [bc110]),
 ((15, 4), [bc111, bc112, bc113]),
 ((15, 7), [bc111, bc112, bc114]),
 ((15, 4), [bc111, bc115, bc116]),
 ((16, 4), [bc111, bc115, bc117])]
private abbrev endpointInput8_36 : LowerPair × Bool × Bool := (([2], [1, 1]), true, true)
private def endpointCodes8_36 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((0, 9), [bc118]),
 ((0, 9), [bc119, bc120, bc121]),
 ((0, 10), [bc119, bc120, bc122]),
 ((0, 9), [bc119, bc123, bc124]),
 ((3, 9), [bc119, bc123, bc125])]
private abbrev endpointInput8_37 : LowerPair × Bool × Bool := (([2], [1, 2]), false, true)
private def endpointCodes8_37 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((6, 11), [bc126, bc127, bc128]),
 ((6, 12), [bc126, bc127, bc129]),
 ((6, 11), [bc126, bc130, bc131]),
 ((8, 11), [bc126, bc130, bc132]),
 ((6, 11), [bc133])]
private abbrev endpointInput8_38 : LowerPair × Bool × Bool := (([3, 1], [1]), true, false)
private def endpointCodes8_38 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((17, 1), [bc134, bc135, bc136]),
 ((17, 2), [bc134, bc135, bc137]),
 ((17, 1), [bc134, bc138, bc139]),
 ((18, 1), [bc134, bc138, bc140]),
 ((17, 1), [bc141])]
private abbrev endpointInput8_39 : LowerPair × Bool × Bool := (([3, 2], [1]), false, false)
private def endpointCodes8_39 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((19, 4), [bc142]),
 ((19, 4), [bc143, bc144, bc145]),
 ((19, 7), [bc143, bc144, bc146]),
 ((19, 4), [bc143, bc147, bc148]),
 ((20, 4), [bc143, bc147, bc149])]
private abbrev endpointInput8_40 : LowerPair × Bool × Bool := (([3], [1, 1]), true, true)
private def endpointCodes8_40 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((21, 9), [(365, false, true)]),
 ((21, 9), [bc150, bc151, (370, false, true)]),
 ((21, 10), [bc150, bc151, (370, true, false)]),
 ((21, 9), [bc150, bc152, (373, true, true)]),
 ((22, 9), [bc150, bc152, (373, false, false)])]
private abbrev endpointInput8_41 : LowerPair × Bool × Bool := (([3], [1, 2]), false, true)
private def endpointCodes8_41 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((23, 11), [bc153]), ((23, 11), [bc154])]
private abbrev endpointInput8_42 : LowerPair × Bool × Bool := (([2, 1], [2]), true, false)
private def endpointCodes8_42 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((13, 0), [bc155, bc156, bc157]),
 ((13, 3), [bc155, bc156, bc158]),
 ((13, 0), [bc155, bc159, bc160]),
 ((14, 0), [bc155, bc159, bc161]),
 ((13, 0), [bc162])]
private abbrev endpointInput8_43 : LowerPair × Bool × Bool := (([2, 2], [2]), false, false)
private def endpointCodes8_43 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((15, 6), [bc163]),
 ((15, 6), [bc164, bc165, bc166]),
 ((15, 8), [bc164, bc165, bc167]),
 ((15, 6), [bc164, bc168, bc169]),
 ((16, 6), [bc164, bc168, bc170])]
private abbrev endpointInput8_44 : LowerPair × Bool × Bool := (([2], [2, 1]), true, true)
private def endpointCodes8_44 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((0, 13), [bc171]),
 ((0, 13), [bc172, bc173, bc174]),
 ((0, 14), [bc172, bc173, bc175]),
 ((0, 13), [bc172, bc176, bc177]),
 ((3, 13), [bc172, bc176, bc178])]
private abbrev endpointInput8_45 : LowerPair × Bool × Bool := (([2], [2, 2]), false, true)
private def endpointCodes8_45 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((6, 15), [bc179, bc180, bc181]),
 ((6, 16), [bc179, bc180, bc182]),
 ((6, 15), [bc179, bc183, bc184]),
 ((8, 15), [bc179, bc183, bc185]),
 ((6, 15), [bc186])]
private abbrev endpointInput8_46 : LowerPair × Bool × Bool := (([2, 1], [3]), true, false)
private def endpointCodes8_46 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((13, 21), [bc187, bc188, (427, false, true)]),
 ((13, 22), [bc187, bc188, (427, true, false)]),
 ((13, 21), [bc187, bc189, (436, true, true)]),
 ((14, 21), [bc187, bc189, (436, false, false)]),
 ((13, 21), [(432, true, true)])]
private abbrev endpointInput8_47 : LowerPair × Bool × Bool := (([2, 2], [3]), false, false)
private def endpointCodes8_47 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((15, 23), [bc190]), ((15, 23), [bc191])]
private abbrev endpointInput8_48 : LowerPair × Bool × Bool := (([2], [3, 1]), true, true)
private def endpointCodes8_48 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((0, 17), [bc192]),
 ((0, 17), [bc193, bc194, bc195]),
 ((0, 18), [bc193, bc194, bc196]),
 ((0, 17), [bc193, bc197, bc198]),
 ((3, 17), [bc193, bc197, bc199])]
private abbrev endpointInput8_49 : LowerPair × Bool × Bool := (([2], [3, 2]), false, true)
private def endpointCodes8_49 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((6, 19), [bc200, bc201, bc202]),
 ((6, 20), [bc200, bc201, bc203]),
 ((6, 19), [bc200, bc204, bc205]),
 ((8, 19), [bc200, bc204, bc206]),
 ((6, 19), [bc207])]
private abbrev endpointInput8_50 : LowerPair × Bool × Bool := (([2], [1]), true, false)
private def endpointCodes8_50 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((0, 1), [bc2, bc3]),
 ((0, 2), [bc2, bc4]),
 ((0, 1), [bc5, bc6]),
 ((3, 1), [bc5, bc7])]
private abbrev endpointInput8_51 : LowerPair × Bool × Bool := (([3], [1]), true, false)
private def endpointCodes8_51 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((21, 1), [bc208, bc209]),
 ((21, 2), [bc208, bc210]),
 ((21, 1), [bc211, bc212]),
 ((22, 1), [bc211, bc213])]
private abbrev endpointInput8_52 : LowerPair × Bool × Bool := (([2], [1]), false, false)
private def endpointCodes8_52 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((6, 4), [bc2, bc41]),
 ((6, 7), [bc2, bc42]),
 ((6, 4), [bc5, bc44]),
 ((8, 4), [bc5, bc45])]
private abbrev endpointInput8_53 : LowerPair × Bool × Bool := (([2], [2]), false, false)
private def endpointCodes8_53 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((6, 6), [bc214, bc215]),
 ((6, 8), [bc214, bc216]),
 ((6, 6), [bc217, bc218]),
 ((8, 6), [bc217, bc219])]
private abbrev endpointInput8_54 : LowerPair × Bool × Bool := (([2], [2]), true, false)
private def endpointCodes8_54 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((0, 0), [bc214, bc35]),
 ((0, 3), [bc214, bc36]),
 ((0, 0), [bc217, bc38]),
 ((3, 0), [bc217, bc39])]
private abbrev endpointInput8_55 : LowerPair × Bool × Bool := (([3], [1]), false, false)
private def endpointCodes8_55 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((23, 4), [])]
private abbrev endpointInput8_56 : LowerPair × Bool × Bool := (([2], [3]), true, false)
private def endpointCodes8_56 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((0, 21), [bc220, bc221]),
 ((0, 22), [bc220, bc222]),
 ((0, 21), [bc223, bc224]),
 ((3, 21), [bc223, bc225])]
private abbrev endpointInput8_57 : LowerPair × Bool × Bool := (([2], [3]), false, false)
private def endpointCodes8_57 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((6, 23), [])]

private def decodeEndpoint8 (x : (ℕ × ℕ) × List (ℕ × Bool × Bool)) : LowerHistoryEndCase :=
  ((endpointFields8[x.1.1]?.getD ⟨0,0,0,0⟩,endpointFields8[x.1.2]?.getD ⟨0,0,0,0⟩),x.2.map decodeThresholdBound)

private theorem hEndpoint8_0 :
    trunkEndpointCases (trunkCatalog.states 8).context endpointInput8_0.1 endpointInput8_0.2.1 endpointInput8_0.2.2 = endpointCodes8_0.map decodeEndpoint8 := by decide +kernel

private theorem hEndpoint8_1 :
    trunkEndpointCases (trunkCatalog.states 8).context endpointInput8_1.1 endpointInput8_1.2.1 endpointInput8_1.2.2 = endpointCodes8_1.map decodeEndpoint8 := by decide +kernel

private theorem hEndpoint8_2 :
    trunkEndpointCases (trunkCatalog.states 8).context endpointInput8_2.1 endpointInput8_2.2.1 endpointInput8_2.2.2 = endpointCodes8_2.map decodeEndpoint8 := by decide +kernel

private theorem hEndpoint8_3 :
    trunkEndpointCases (trunkCatalog.states 8).context endpointInput8_3.1 endpointInput8_3.2.1 endpointInput8_3.2.2 = endpointCodes8_3.map decodeEndpoint8 := by decide +kernel

private theorem hEndpoint8_4 :
    trunkEndpointCases (trunkCatalog.states 8).context endpointInput8_4.1 endpointInput8_4.2.1 endpointInput8_4.2.2 = endpointCodes8_4.map decodeEndpoint8 := by decide +kernel

private theorem hEndpoint8_5 :
    trunkEndpointCases (trunkCatalog.states 8).context endpointInput8_5.1 endpointInput8_5.2.1 endpointInput8_5.2.2 = endpointCodes8_5.map decodeEndpoint8 := by decide +kernel

private theorem hEndpoint8_6 :
    trunkEndpointCases (trunkCatalog.states 8).context endpointInput8_6.1 endpointInput8_6.2.1 endpointInput8_6.2.2 = endpointCodes8_6.map decodeEndpoint8 := by decide +kernel

private theorem hEndpoint8_7 :
    trunkEndpointCases (trunkCatalog.states 8).context endpointInput8_7.1 endpointInput8_7.2.1 endpointInput8_7.2.2 = endpointCodes8_7.map decodeEndpoint8 := by decide +kernel

private theorem hEndpoint8_10 :
    trunkEndpointCases (trunkCatalog.states 8).context endpointInput8_10.1 endpointInput8_10.2.1 endpointInput8_10.2.2 = endpointCodes8_10.map decodeEndpoint8 := by decide +kernel

private theorem hEndpoint8_11 :
    trunkEndpointCases (trunkCatalog.states 8).context endpointInput8_11.1 endpointInput8_11.2.1 endpointInput8_11.2.2 = endpointCodes8_11.map decodeEndpoint8 := by decide +kernel

private theorem hEndpoint8_17 :
    trunkEndpointCases (trunkCatalog.states 8).context endpointInput8_17.1 endpointInput8_17.2.1 endpointInput8_17.2.2 = endpointCodes8_17.map decodeEndpoint8 := by decide +kernel

private theorem hEndpoint8_18 :
    trunkEndpointCases (trunkCatalog.states 8).context endpointInput8_18.1 endpointInput8_18.2.1 endpointInput8_18.2.2 = endpointCodes8_18.map decodeEndpoint8 := by decide +kernel

private theorem hEndpoint8_19 :
    trunkEndpointCases (trunkCatalog.states 8).context endpointInput8_19.1 endpointInput8_19.2.1 endpointInput8_19.2.2 = endpointCodes8_19.map decodeEndpoint8 := by decide +kernel

private theorem hEndpoint8_20 :
    trunkEndpointCases (trunkCatalog.states 8).context endpointInput8_20.1 endpointInput8_20.2.1 endpointInput8_20.2.2 = endpointCodes8_20.map decodeEndpoint8 := by decide +kernel

private theorem hEndpoint8_21 :
    trunkEndpointCases (trunkCatalog.states 8).context endpointInput8_21.1 endpointInput8_21.2.1 endpointInput8_21.2.2 = endpointCodes8_21.map decodeEndpoint8 := by decide +kernel

private theorem hEndpoint8_22 :
    trunkEndpointCases (trunkCatalog.states 8).context endpointInput8_22.1 endpointInput8_22.2.1 endpointInput8_22.2.2 = endpointCodes8_22.map decodeEndpoint8 := by decide +kernel

private theorem hEndpoint8_23 :
    trunkEndpointCases (trunkCatalog.states 8).context endpointInput8_23.1 endpointInput8_23.2.1 endpointInput8_23.2.2 = endpointCodes8_23.map decodeEndpoint8 := by decide +kernel

private theorem hEndpoint8_24 :
    trunkEndpointCases (trunkCatalog.states 8).context endpointInput8_24.1 endpointInput8_24.2.1 endpointInput8_24.2.2 = endpointCodes8_24.map decodeEndpoint8 := by decide +kernel

private theorem hEndpoint8_25 :
    trunkEndpointCases (trunkCatalog.states 8).context endpointInput8_25.1 endpointInput8_25.2.1 endpointInput8_25.2.2 = endpointCodes8_25.map decodeEndpoint8 := by decide +kernel

private theorem hEndpoint8_26 :
    trunkEndpointCases (trunkCatalog.states 8).context endpointInput8_26.1 endpointInput8_26.2.1 endpointInput8_26.2.2 = endpointCodes8_26.map decodeEndpoint8 := by decide +kernel

private theorem hEndpoint8_27 :
    trunkEndpointCases (trunkCatalog.states 8).context endpointInput8_27.1 endpointInput8_27.2.1 endpointInput8_27.2.2 = endpointCodes8_27.map decodeEndpoint8 := by decide +kernel

private theorem hEndpoint8_28 :
    trunkEndpointCases (trunkCatalog.states 8).context endpointInput8_28.1 endpointInput8_28.2.1 endpointInput8_28.2.2 = endpointCodes8_28.map decodeEndpoint8 := by decide +kernel

private theorem hEndpoint8_29 :
    trunkEndpointCases (trunkCatalog.states 8).context endpointInput8_29.1 endpointInput8_29.2.1 endpointInput8_29.2.2 = endpointCodes8_29.map decodeEndpoint8 := by decide +kernel

private theorem hEndpoint8_30 :
    trunkEndpointCases (trunkCatalog.states 8).context endpointInput8_30.1 endpointInput8_30.2.1 endpointInput8_30.2.2 = endpointCodes8_30.map decodeEndpoint8 := by decide +kernel

private theorem hEndpoint8_31 :
    trunkEndpointCases (trunkCatalog.states 8).context endpointInput8_31.1 endpointInput8_31.2.1 endpointInput8_31.2.2 = endpointCodes8_31.map decodeEndpoint8 := by decide +kernel

private theorem hEndpoint8_32 :
    trunkEndpointCases (trunkCatalog.states 8).context endpointInput8_32.1 endpointInput8_32.2.1 endpointInput8_32.2.2 = endpointCodes8_32.map decodeEndpoint8 := by decide +kernel

private theorem hEndpoint8_33 :
    trunkEndpointCases (trunkCatalog.states 8).context endpointInput8_33.1 endpointInput8_33.2.1 endpointInput8_33.2.2 = endpointCodes8_33.map decodeEndpoint8 := by decide +kernel

private theorem hEndpoint8_34 :
    trunkEndpointCases (trunkCatalog.states 8).context endpointInput8_34.1 endpointInput8_34.2.1 endpointInput8_34.2.2 = endpointCodes8_34.map decodeEndpoint8 := by decide +kernel

private theorem hEndpoint8_35 :
    trunkEndpointCases (trunkCatalog.states 8).context endpointInput8_35.1 endpointInput8_35.2.1 endpointInput8_35.2.2 = endpointCodes8_35.map decodeEndpoint8 := by decide +kernel

private theorem hEndpoint8_36 :
    trunkEndpointCases (trunkCatalog.states 8).context endpointInput8_36.1 endpointInput8_36.2.1 endpointInput8_36.2.2 = endpointCodes8_36.map decodeEndpoint8 := by decide +kernel

private theorem hEndpoint8_37 :
    trunkEndpointCases (trunkCatalog.states 8).context endpointInput8_37.1 endpointInput8_37.2.1 endpointInput8_37.2.2 = endpointCodes8_37.map decodeEndpoint8 := by decide +kernel

private theorem hEndpoint8_38 :
    trunkEndpointCases (trunkCatalog.states 8).context endpointInput8_38.1 endpointInput8_38.2.1 endpointInput8_38.2.2 = endpointCodes8_38.map decodeEndpoint8 := by decide +kernel

private theorem hEndpoint8_39 :
    trunkEndpointCases (trunkCatalog.states 8).context endpointInput8_39.1 endpointInput8_39.2.1 endpointInput8_39.2.2 = endpointCodes8_39.map decodeEndpoint8 := by decide +kernel

private theorem hEndpoint8_40 :
    trunkEndpointCases (trunkCatalog.states 8).context endpointInput8_40.1 endpointInput8_40.2.1 endpointInput8_40.2.2 = endpointCodes8_40.map decodeEndpoint8 := by decide +kernel

private theorem hEndpoint8_41 :
    trunkEndpointCases (trunkCatalog.states 8).context endpointInput8_41.1 endpointInput8_41.2.1 endpointInput8_41.2.2 = endpointCodes8_41.map decodeEndpoint8 := by decide +kernel

private theorem hEndpoint8_42 :
    trunkEndpointCases (trunkCatalog.states 8).context endpointInput8_42.1 endpointInput8_42.2.1 endpointInput8_42.2.2 = endpointCodes8_42.map decodeEndpoint8 := by decide +kernel

private theorem hEndpoint8_43 :
    trunkEndpointCases (trunkCatalog.states 8).context endpointInput8_43.1 endpointInput8_43.2.1 endpointInput8_43.2.2 = endpointCodes8_43.map decodeEndpoint8 := by decide +kernel

private theorem hEndpoint8_44 :
    trunkEndpointCases (trunkCatalog.states 8).context endpointInput8_44.1 endpointInput8_44.2.1 endpointInput8_44.2.2 = endpointCodes8_44.map decodeEndpoint8 := by decide +kernel

private theorem hEndpoint8_45 :
    trunkEndpointCases (trunkCatalog.states 8).context endpointInput8_45.1 endpointInput8_45.2.1 endpointInput8_45.2.2 = endpointCodes8_45.map decodeEndpoint8 := by decide +kernel

private theorem hEndpoint8_46 :
    trunkEndpointCases (trunkCatalog.states 8).context endpointInput8_46.1 endpointInput8_46.2.1 endpointInput8_46.2.2 = endpointCodes8_46.map decodeEndpoint8 := by decide +kernel

private theorem hEndpoint8_47 :
    trunkEndpointCases (trunkCatalog.states 8).context endpointInput8_47.1 endpointInput8_47.2.1 endpointInput8_47.2.2 = endpointCodes8_47.map decodeEndpoint8 := by decide +kernel

private theorem hEndpoint8_48 :
    trunkEndpointCases (trunkCatalog.states 8).context endpointInput8_48.1 endpointInput8_48.2.1 endpointInput8_48.2.2 = endpointCodes8_48.map decodeEndpoint8 := by decide +kernel

private theorem hEndpoint8_49 :
    trunkEndpointCases (trunkCatalog.states 8).context endpointInput8_49.1 endpointInput8_49.2.1 endpointInput8_49.2.2 = endpointCodes8_49.map decodeEndpoint8 := by decide +kernel

private theorem hEndpoint8_50 :
    trunkEndpointCases (trunkCatalog.states 8).context endpointInput8_50.1 endpointInput8_50.2.1 endpointInput8_50.2.2 = endpointCodes8_50.map decodeEndpoint8 := by decide +kernel

private theorem hEndpoint8_51 :
    trunkEndpointCases (trunkCatalog.states 8).context endpointInput8_51.1 endpointInput8_51.2.1 endpointInput8_51.2.2 = endpointCodes8_51.map decodeEndpoint8 := by decide +kernel

private theorem hEndpoint8_52 :
    trunkEndpointCases (trunkCatalog.states 8).context endpointInput8_52.1 endpointInput8_52.2.1 endpointInput8_52.2.2 = endpointCodes8_52.map decodeEndpoint8 := by decide +kernel

private theorem hEndpoint8_53 :
    trunkEndpointCases (trunkCatalog.states 8).context endpointInput8_53.1 endpointInput8_53.2.1 endpointInput8_53.2.2 = endpointCodes8_53.map decodeEndpoint8 := by decide +kernel

private theorem hEndpoint8_54 :
    trunkEndpointCases (trunkCatalog.states 8).context endpointInput8_54.1 endpointInput8_54.2.1 endpointInput8_54.2.2 = endpointCodes8_54.map decodeEndpoint8 := by decide +kernel

private theorem hEndpoint8_55 :
    trunkEndpointCases (trunkCatalog.states 8).context endpointInput8_55.1 endpointInput8_55.2.1 endpointInput8_55.2.2 = endpointCodes8_55.map decodeEndpoint8 := by decide +kernel

private theorem hEndpoint8_56 :
    trunkEndpointCases (trunkCatalog.states 8).context endpointInput8_56.1 endpointInput8_56.2.1 endpointInput8_56.2.2 = endpointCodes8_56.map decodeEndpoint8 := by decide +kernel

private theorem hEndpoint8_57 :
    trunkEndpointCases (trunkCatalog.states 8).context endpointInput8_57.1 endpointInput8_57.2.1 endpointInput8_57.2.2 = endpointCodes8_57.map decodeEndpoint8 := by decide +kernel

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

private def classValidIds : List ℕ := [294, 10, 16, 65, 30, 67, 56, 68, 88, 90, 92, 177, 97, 96, 98, 102, 103, 179, 182, 181, 180, 187, 191, 200, 204, 207, 211, 213, 214, 231, 236, 233, 232, 241, 245, 252, 254, 255, 258, 259, 261, 263, 264, 270, 273, 277, 281, 283, 284, 15, 3, 144, 29, 170, 143, 94, 217, 220, 136, 137, 223, 147, 9, 4, 28, 226, 1, 140, 149, 287, 289, 290, 291, 247, 292, 173, 148, 176, 2, 6, 14, 295, 52, 296, 318, 321, 323, 327, 329, 333, 337, 338, 113, 343, 346, 345, 350, 354, 127, 364, 365, 367, 371, 373, 374, 377, 379, 381, 378, 385, 390, 397, 402, 407, 411, 413, 417, 421, 422, 427, 430, 428, 429, 438, 440, 441, 447, 451, 453, 457, 461, 462, 155, 156, 467, 469, 163, 153, 478, 477, 479, 159, 482, 483, 481, 165, 484, 485, 486, 91, 487, 488, 489, 476, 491, 492, 493, 89, 497, 442, 502, 503, 504, 505, 506, 507, 167, 8]
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
private def codeHN : ℕ × Bool × Bool := bc73
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
private def thresholdParentA8 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc0, bc8, bc9, bc10], some (some bc226)),
 ([bc0, bc8, bc9, bc11], some (some bc227)),
 ([bc0, bc8, bc12, bc13], some (some bc226)),
 ([bc0, bc8, bc12, bc14], some (some bc228)),
 ([bc0, bc15], some (some bc226)),
 ([bc1, bc2, bc3, bc8, bc9, bc10],
  some (some bc226)),
 ([bc1, bc2, bc3, bc8, bc9, bc11],
  some (some bc227)),
 ([bc1, bc2, bc3, bc8, bc12, bc13],
  some (some bc226)),
 ([bc1, bc2, bc3, bc8, bc12, bc14],
  some (some bc228)),
 ([bc1, bc2, bc3, bc15], some (some bc226)),
 ([bc1, bc2, bc4, bc8, bc9, bc10],
  some (some bc229)),
 ([bc1, bc2, bc4, bc8, bc9, bc11],
  some (some bc230)),
 ([bc1, bc2, bc4, bc8, bc12, bc13],
  some (some bc229)),
 ([bc1, bc2, bc4, bc8, bc12, bc14],
  some (some bc231)),
 ([bc1, bc2, bc4, bc15], some (some bc229)),
 ([bc1, bc5, bc6, bc8, bc9, bc10],
  some (some bc226)),
 ([bc1, bc5, bc6, bc8, bc9, bc11],
  some (some bc227)),
 ([bc1, bc5, bc6, bc8, bc12, bc13],
  some (some bc226)),
 ([bc1, bc5, bc6, bc8, bc12, bc14],
  some (some bc228)),
 ([bc1, bc5, bc6, bc15], some (some bc226)),
 ([bc1, bc5, bc7, bc8, bc9, bc10],
  some (some bc232)),
 ([bc1, bc5, bc7, bc8, bc9, bc11],
  some (some bc233)),
 ([bc1, bc5, bc7, bc8, bc12, bc13],
  some (some bc232)),
 ([bc1, bc5, bc7, bc8, bc12, bc14],
  some (some bc234)),
 ([bc1, bc5, bc7, bc15], some (some bc232))]
private def thresholdParentB8 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc8, bc0, bc16, bc17], some none),
 ([bc8, bc0, bc16, bc18], some none),
 ([bc8, bc0, bc19, bc20], some none),
 ([bc8, bc0, bc19, bc21], some none),
 ([bc8, bc1], some none),
 ([bc15, bc0, bc16, bc17], some none),
 ([bc15, bc0, bc16, bc18], some none),
 ([bc15, bc0, bc19, bc20], some none),
 ([bc15, bc0, bc19, bc21], some none),
 ([bc15, bc1], some none)]

private def parentSourceA8 : Array (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := #[([bc0, bc8, bc9, bc10], some (some bc226)),
 ([bc0, bc8, bc9, bc11], some (some bc227)),
 ([bc0, bc8, bc12, bc13], some (some bc226)),
 ([bc0, bc8, bc12, bc14], some (some bc228)),
 ([bc0, bc15], some (some bc226)),
 ([bc1, bc2, bc3, bc8, bc9, bc10],
  some (some bc226)),
 ([bc1, bc2, bc3, bc8, bc9, bc11],
  some (some bc227)),
 ([bc1, bc2, bc3, bc8, bc12, bc13],
  some (some bc226)),
 ([bc1, bc2, bc3, bc8, bc12, bc14],
  some (some bc228)),
 ([bc1, bc2, bc3, bc15], some (some bc226)),
 ([bc1, bc2, bc4, bc8, bc9, bc10],
  some (some bc229)),
 ([bc1, bc2, bc4, bc8, bc9, bc11],
  some (some bc230)),
 ([bc1, bc2, bc4, bc8, bc12, bc13],
  some (some bc229)),
 ([bc1, bc2, bc4, bc8, bc12, bc14],
  some (some bc231)),
 ([bc1, bc2, bc4, bc15], some (some bc229)),
 ([bc1, bc5, bc6, bc8, bc9, bc10],
  some (some bc226)),
 ([bc1, bc5, bc6, bc8, bc9, bc11],
  some (some bc227)),
 ([bc1, bc5, bc6, bc8, bc12, bc13],
  some (some bc226)),
 ([bc1, bc5, bc6, bc8, bc12, bc14],
  some (some bc228)),
 ([bc1, bc5, bc6, bc15], some (some bc226)),
 ([bc1, bc5, bc7, bc8, bc9, bc10],
  some (some bc232)),
 ([bc1, bc5, bc7, bc8, bc9, bc11],
  some (some bc233)),
 ([bc1, bc5, bc7, bc8, bc12, bc13],
  some (some bc232)),
 ([bc1, bc5, bc7, bc8, bc12, bc14],
  some (some bc234)),
 ([bc1, bc5, bc7, bc15], some (some bc232))]

private def parentSourceB8 : Array (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := #[([bc8, bc0, bc16, bc17], some none),
 ([bc8, bc0, bc16, bc18], some none),
 ([bc8, bc0, bc19, bc20], some none),
 ([bc8, bc0, bc19, bc21], some none),
 ([bc8, bc1], some none),
 ([bc15, bc0, bc16, bc17], some none),
 ([bc15, bc0, bc16, bc18], some none),
 ([bc15, bc0, bc19, bc20], some none),
 ([bc15, bc0, bc19, bc21], some none),
 ([bc15, bc1], some none)]

private def codedParents8 (i : ℕ) : List (ℕ × Bool × Bool) :=
  if i < 250 then
    (codeRawParent (parentSourceA8[i / 10]?.getD ([],none)) (parentSourceB8[i % 10]?.getD ([],none))).getD []
  else []

private theorem hThresholdParentA8 : trunkBranches (trunkCatalog.states 8).context ⟨([2],[]),true,([1],[]),false,false,[]⟩ = thresholdParentA8.map decodeGoalBranch := by
  have hi : ((⟨([2],[]),true,([1],[]),false,false,[]⟩ : Section14Spec).first,(⟨([2],[]),true,([1],[]),false,false,[]⟩ : Section14Spec).firstUpper,trunkSpecIncoming (⟨([2],[]),true,([1],[]),false,false,[]⟩ : Section14Spec)) = endpointInput8_0 := by decide +kernel
  have hj : ((⟨([2],[]),true,([1],[]),false,false,[]⟩ : Section14Spec).second,(⟨([2],[]),true,([1],[]),false,false,[]⟩ : Section14Spec).secondUpper,trunkSpecIncoming (⟨([2],[]),true,([1],[]),false,false,[]⟩ : Section14Spec)) = endpointInput8_1 := by decide +kernel
  have heL : trunkEndpointCases (trunkCatalog.states 8).context (⟨([2],[]),true,([1],[]),false,false,[]⟩ : Section14Spec).first (⟨([2],[]),true,([1],[]),false,false,[]⟩ : Section14Spec).firstUpper (trunkSpecIncoming (⟨([2],[]),true,([1],[]),false,false,[]⟩ : Section14Spec)) = endpointCodes8_0.map decodeEndpoint8 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 8).context z.1 z.2.1 z.2.2) hi).trans hEndpoint8_0
  have heR : trunkEndpointCases (trunkCatalog.states 8).context (⟨([2],[]),true,([1],[]),false,false,[]⟩ : Section14Spec).second (⟨([2],[]),true,([1],[]),false,false,[]⟩ : Section14Spec).secondUpper (trunkSpecIncoming (⟨([2],[]),true,([1],[]),false,false,[]⟩ : Section14Spec)) = endpointCodes8_1.map decodeEndpoint8 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 8).context z.1 z.2.1 z.2.2) hj).trans hEndpoint8_1
  unfold trunkBranches
  rw [heL,heR]
  decide +kernel
private theorem hThresholdParentB8 : trunkBranches (trunkCatalog.states 8).context ⟨([1],[]),true,([2],[]),false,false,[]⟩ = thresholdParentB8.map decodeGoalBranch := by
  have hi : ((⟨([1],[]),true,([2],[]),false,false,[]⟩ : Section14Spec).first,(⟨([1],[]),true,([2],[]),false,false,[]⟩ : Section14Spec).firstUpper,trunkSpecIncoming (⟨([1],[]),true,([2],[]),false,false,[]⟩ : Section14Spec)) = endpointInput8_2 := by decide +kernel
  have hj : ((⟨([1],[]),true,([2],[]),false,false,[]⟩ : Section14Spec).second,(⟨([1],[]),true,([2],[]),false,false,[]⟩ : Section14Spec).secondUpper,trunkSpecIncoming (⟨([1],[]),true,([2],[]),false,false,[]⟩ : Section14Spec)) = endpointInput8_3 := by decide +kernel
  have heL : trunkEndpointCases (trunkCatalog.states 8).context (⟨([1],[]),true,([2],[]),false,false,[]⟩ : Section14Spec).first (⟨([1],[]),true,([2],[]),false,false,[]⟩ : Section14Spec).firstUpper (trunkSpecIncoming (⟨([1],[]),true,([2],[]),false,false,[]⟩ : Section14Spec)) = endpointCodes8_2.map decodeEndpoint8 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 8).context z.1 z.2.1 z.2.2) hi).trans hEndpoint8_2
  have heR : trunkEndpointCases (trunkCatalog.states 8).context (⟨([1],[]),true,([2],[]),false,false,[]⟩ : Section14Spec).second (⟨([1],[]),true,([2],[]),false,false,[]⟩ : Section14Spec).secondUpper (trunkSpecIncoming (⟨([1],[]),true,([2],[]),false,false,[]⟩ : Section14Spec)) = endpointCodes8_3.map decodeEndpoint8 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 8).context z.1 z.2.1 z.2.2) hj).trans hEndpoint8_3
  unfold trunkBranches
  rw [heL,heR]
  decide +kernel
private theorem hCodedParentTable8 : (List.range 250).map codedParents8 = thresholdParentA8.flatMap (fun a => thresholdParentB8.filterMap (codeRawParent a)) := by decide +kernel
private theorem hCodedParentList8 : trunkRawParents (trunkCatalog.states 8).context = ((List.range 250).map codedParents8).map (List.map decodeThresholdBound) := by
  unfold trunkRawParents
  rw [hThresholdParentA8,hThresholdParentB8]
  change (thresholdParentA8.map decodeGoalBranch).flatMap (fun a => (thresholdParentB8.map decodeGoalBranch).filterMap (rawParent a)) = ((List.range 250).map codedParents8).map (List.map decodeThresholdBound)
  rw [←codeParents_map,←hCodedParentTable8]
private theorem hCodedParentLength8 : (trunkRawParents (trunkCatalog.states 8).context).length = 250 := by
  rw [hCodedParentList8]; simp only [List.length_map,List.length_range]
private theorem hCodedParents8 (i : ℕ) : (trunkRawParents (trunkCatalog.states 8).context)[i]?.getD [] = (codedParents8 i).map decodeThresholdBound := by
  rw [hCodedParentList8,List.getElem?_map,List.getElem?_map]
  by_cases hi : i < 250
  · rw [List.getElem?_range hi]; rfl
  · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hi)]
    simp only [Option.map_none,Option.getD_none,codedParents8,if_neg hi,List.map_nil]

private theorem hHN : proj lowerHistoryHN = 466397207 := by decide +kernel
private theorem hZero : proj lowerHistoryZero = 559802771 := by decide +kernel

private theorem hA8 : (trunkBranches (trunkCatalog.states 8).context ⟨([2],[]),true,([1],[]),false,false,[]⟩).map branchCode = codesA8 := by
  rw [hThresholdParentA8]
  decide +kernel
private theorem hB8 : (trunkBranches (trunkCatalog.states 8).context ⟨([1],[]),true,([2],[]),false,false,[]⟩).map branchCode = codesB8 := by
  rw [hThresholdParentB8]
  decide +kernel
private def fprints8 : List ℕ := [4325838231, 4163376800, 4425776615, 4417291780, 4165885676, 5317814407, 5155352976, 5417752791, 5409267956, 5157861852, 3714549947, 3552088516, 3814488331, 3806003496, 3554597392, 4706526123, 4544064692, 4806464507, 4797979672, 4546573568, 4499614243, 4337152812, 4599552627, 4591067792, 4339661688, 5491590419, 5329128988, 5591528803, 5583043968, 5331637864, 3695453821, 3532992390, 3795392205, 3786907370, 3535501266, 4687429997, 4524968566, 4787368381, 4778883546, 4527477442, 4850989863, 4688528432, 4950928247, 4942443412, 4691037308, 3968267512, 3805806081, 4068205896, 4059721061, 3808314957, 5763869542, 5601408111, 5863807926, 5855323091, 4762114077, 6755845718, 6593384287, 6855784102, 6847299267, 5754090253, 5152581258, 4990119827, 5252519642, 5244034807, 4150825793, 6144557434, 5982096003, 6244495818, 6236010983, 5142801969, 5937645554, 5775184123, 6037583938, 6029099103, 4935890089, 6929621730, 6767160299, 7029560114, 7021075279, 5927866265, 5133485132, 4971023701, 5233423516, 5224938681, 4131729667, 6125461308, 5962999877, 6225399692, 6216914857, 5123705843, 6289021174, 6126559743, 6388959558, 6380474723, 5287265709, 5406298823, 5243837392, 5506237207, 5497752372, 4404543358, 5452433595, 5289972164, 5552371979, 5543887144, 4450678130, 6444409771, 6281948340, 6544348155, 6535863320, 5442654306, 4889340785, 4726879354, 4989279169, 4980794334, 3887585320, 5881316961, 5718855530, 5981255345, 5972770510, 4879561496, 5626209607, 5463748176, 5726147991, 5717663156, 4624454142, 6618185783, 6455724352, 6718124167, 6709639332, 5616430318, 5586827744, 5424366313, 5686766128, 5678281293, 4585072279, 6578803920, 6416342489, 6678742304, 6670257469, 5577048455, 5977585227, 5815123796, 6077523611, 6069038776, 4975829762, 5094862876, 4932401445, 5194801260, 5186316425, 4093107411, 6413071998, 6250610567, 6513010382, 6504525547, 5411316533, 7405048174, 7242586743, 7504986558, 7496501723, 6403292709, 5801783714, 5639322283, 5901722098, 5893237263, 4800028249, 6793759890, 6631298459, 6893698274, 6885213439, 5792004425, 6586848010, 6424386579, 6686786394, 6678301559, 5585092545, 7578824186, 7416362755, 7678762570, 7670277735, 6577068721, 5782687588, 5620226157, 5882625972, 5874141137, 4780932123, 6774663764, 6612202333, 6874602148, 6866117313, 5772908299, 6938223630, 6775762199, 7038162014, 7029677179, 5936468165, 6055501279, 5893039848, 6155439663, 6146954828, 5053745814, 5250137420, 5087675989, 5350075804, 5341590969, 4248381955, 6242113596, 6079652165, 6342051980, 6333567145, 5240358131, 5206499587, 5044038156, 5306437971, 5297953136, 4204744122, 6198475763, 6036014332, 6298414147, 6289929312, 5196720298, 5423913432, 5261452001, 5523851816, 5515366981, 4422157967, 6415889608, 6253428177, 6515827992, 6507343157, 5414134143, 4979276577, 4816815146, 5079214961, 5070730126, 3977521112, 5971252753, 5808791322, 6071191137, 6062706302, 4969497288, 5775289052, 5612827621, 5875227436, 5866742601, 4773533587, 4892566701, 4730105270, 4992505085, 4984020250, 3890811236]
private theorem hprints8 : (trunkRawParents (trunkCatalog.states 8).context).map fingerprint = fprints8 := by
  have hm (L : List (List CertBound)) :
      L.map fingerprint = (L.map (List.map proj)).map (fun cs => cs.toFinset.sum id) := by
    rw [List.map_map]; rfl
  rw [hm,trunkCodes_map,hA8,hB8,hHN,hZero]
  decide +kernel
private theorem hPar8 : trunkParents (trunkCatalog.states 8).context = trunkRawParents (trunkCatalog.states 8).context := by
  apply Freiman.trunkFast_correctness.1
  apply parents_of_fingerprints
  rw [hprints8]
  apply (List.perm_insertionSort (fun a b : ℕ => a ≤ b) fprints8).nodup_iff.mp
  have hs : (List.insertionSort (fun a b : ℕ => a ≤ b) fprints8).IsChain (fun a b => a < b) := by
    decide +kernel
  exact (List.isChain_iff_pairwise.mp hs).imp (fun h => Nat.ne_of_lt h)


private def goalCodes8_2_0 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([], none)]
private def goalCodes8_2_2 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc8, bc9, bc22, bc26, bc27],
  some (some bc235)),
 ([bc8, bc9, bc22, bc26, bc28],
  some (some (36, true, true))),
 ([bc8, bc9, bc22, bc29, bc30],
  some (some bc235)),
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
  some (some bc235)),
 ([bc8, bc12, bc24, bc26, bc28],
  some (some (36, true, true))),
 ([bc8, bc12, bc24, bc29, bc30],
  some (some bc235)),
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
private def goalCodes8_2_5 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc15, bc32, (52, false, true)], some (some (65, false, true))),
 ([bc15, bc32, (52, true, false)], some (some (67, false, true))),
 ([bc15, bc33, (56, true, true)], some (some (65, false, true))),
 ([bc15, bc33, (56, false, false)], some (some (68, false, true)))]
private def goalCodes8_2_10 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc1, bc34, bc35, bc40, bc41],
  some (some bc236)),
 ([bc1, bc34, bc35, bc40, bc42],
  some (some (92, false, true))),
 ([bc1, bc34, bc35, bc43, bc44],
  some (some bc236)),
 ([bc1, bc34, bc35, bc43, bc45],
  some (some (97, false, true))),
 ([bc1, bc34, bc36, bc40, bc41],
  some (some (99, false, true))),
 ([bc1, bc34, bc36, bc40, bc42],
  some (some (100, false, true))),
 ([bc1, bc34, bc36, bc43, bc44],
  some (some (99, false, true))),
 ([bc1, bc34, bc36, bc43, bc45],
  some (some (101, false, true))),
 ([bc1, bc37, bc38, bc40, bc41],
  some (some bc236)),
 ([bc1, bc37, bc38, bc40, bc42],
  some (some (92, false, true))),
 ([bc1, bc37, bc38, bc43, bc44],
  some (some bc236)),
 ([bc1, bc37, bc38, bc43, bc45],
  some (some (97, false, true))),
 ([bc1, bc37, bc39, bc40, bc41],
  some (some (104, false, true))),
 ([bc1, bc37, bc39, bc40, bc42],
  some (some (106, false, true))),
 ([bc1, bc37, bc39, bc43, bc44],
  some (some (104, false, true))),
 ([bc1, bc37, bc39, bc43, bc45],
  some (some (107, false, true)))]
private def goalCodes8_2_12 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc67, bc46, bc47, bc48, bc54],
  some (some bc237)),
 ([bc67,
   bc46,
   bc47,
   bc48,
   bc55,
   bc56,
   bc57],
  some (some bc237)),
 ([bc67,
   bc46,
   bc47,
   bc48,
   bc55,
   bc56,
   bc58],
  some (some (187, true, true))),
 ([bc67,
   bc46,
   bc47,
   bc48,
   bc55,
   bc59,
   bc60],
  some (some bc237)),
 ([bc67,
   bc46,
   bc47,
   bc48,
   bc55,
   bc59,
   bc61],
  some (some (191, true, true))),
 ([bc67, bc46, bc47, bc49, bc54],
  some (some (194, true, true))),
 ([bc67,
   bc46,
   bc47,
   bc49,
   bc55,
   bc56,
   bc57],
  some (some (194, true, true))),
 ([bc67,
   bc46,
   bc47,
   bc49,
   bc55,
   bc56,
   bc58],
  some (some (195, true, true))),
 ([bc67,
   bc46,
   bc47,
   bc49,
   bc55,
   bc59,
   bc60],
  some (some (194, true, true))),
 ([bc67,
   bc46,
   bc47,
   bc49,
   bc55,
   bc59,
   bc61],
  some (some (196, true, true))),
 ([bc67, bc46, bc50, bc51, bc54],
  some (some bc237)),
 ([bc67,
   bc46,
   bc50,
   bc51,
   bc55,
   bc56,
   bc57],
  some (some bc237)),
 ([bc67,
   bc46,
   bc50,
   bc51,
   bc55,
   bc56,
   bc58],
  some (some (187, true, true))),
 ([bc67,
   bc46,
   bc50,
   bc51,
   bc55,
   bc59,
   bc60],
  some (some bc237)),
 ([bc67,
   bc46,
   bc50,
   bc51,
   bc55,
   bc59,
   bc61],
  some (some (191, true, true))),
 ([bc67, bc46, bc50, bc52, bc54],
  some (some (199, true, true))),
 ([bc67,
   bc46,
   bc50,
   bc52,
   bc55,
   bc56,
   bc57],
  some (some (199, true, true))),
 ([bc67,
   bc46,
   bc50,
   bc52,
   bc55,
   bc56,
   bc58],
  some (some (201, true, true))),
 ([bc67,
   bc46,
   bc50,
   bc52,
   bc55,
   bc59,
   bc60],
  some (some (199, true, true))),
 ([bc67,
   bc46,
   bc50,
   bc52,
   bc55,
   bc59,
   bc61],
  some (some (202, true, true))),
 ([bc67, bc53, bc54], some (some bc237)),
 ([bc67, bc53, bc55, bc56, bc57],
  some (some bc237)),
 ([bc67, bc53, bc55, bc56, bc58],
  some (some (187, true, true))),
 ([bc67, bc53, bc55, bc59, bc60],
  some (some bc237)),
 ([bc67, bc53, bc55, bc59, bc61],
  some (some (191, true, true)))]
private def goalCodes8_2_14 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc70, (206, false, true), bc65], some (some bc238)),
 ([bc70, (206, false, true), bc66], some (some bc238)),
 ([bc70, bc62, bc63, (208, false, true), bc65],
  some (some bc238)),
 ([bc70, bc62, bc63, (208, false, true), bc66],
  some (some bc238)),
 ([bc70, bc62, bc63, (208, true, false), bc65],
  some (some (212, false, true))),
 ([bc70, bc62, bc63, (208, true, false), bc66],
  some (some (212, false, true))),
 ([bc70, bc62, bc64, (213, true, true), bc65],
  some (some bc238)),
 ([bc70, bc62, bc64, (213, true, true), bc66],
  some (some bc238)),
 ([bc70, bc62, bc64, (213, false, false), bc65],
  some (some (215, false, true))),
 ([bc70, bc62, bc64, (213, false, false), bc66],
  some (some (215, false, true)))]
private def goalCodes8_2_18 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc96, bc76, bc78, bc79, (231, false, true)],
  some (some bc239)),
 ([bc96, bc76, bc78, bc79, (231, true, false)],
  some (some (238, true, true))),
 ([bc96, bc76, bc78, bc80, (239, true, true)],
  some (some bc239)),
 ([bc96, bc76, bc78, bc80, (239, false, false)],
  some (some (242, true, true))),
 ([bc96, bc76, (234, true, true)], some (some bc239)),
 ([bc96, bc77, bc78, bc79, (231, false, true)],
  some (some bc239)),
 ([bc96, bc77, bc78, bc79, (231, true, false)],
  some (some (238, true, true))),
 ([bc96, bc77, bc78, bc80, (239, true, true)],
  some (some bc239)),
 ([bc96, bc77, bc78, bc80, (239, false, false)],
  some (some (242, true, true))),
 ([bc96, bc77, (234, true, true)], some (some bc239))]
private def goalCodes8_2_20 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc99, bc81, (248, false, true)], some (some bc240)),
 ([bc99, bc81, bc83, bc84, (249, false, true)],
  some (some bc240)),
 ([bc99, bc81, bc83, bc84, (249, true, false)],
  some (some (253, false, true))),
 ([bc99, bc81, bc83, bc85, (254, true, true)],
  some (some bc240)),
 ([bc99, bc81, bc83, bc85, (254, false, false)],
  some (some (257, false, true))),
 ([bc99, bc82, (248, false, true)], some (some bc240)),
 ([bc99, bc82, bc83, bc84, (249, false, true)],
  some (some bc240)),
 ([bc99, bc82, bc83, bc84, (249, true, false)],
  some (some (253, false, true))),
 ([bc99, bc82, bc83, bc85, (254, true, true)],
  some (some bc240)),
 ([bc99, bc82, bc83, bc85, (254, false, false)],
  some (some (257, false, true)))]
private def goalCodes8_2_22 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc241, bc86, bc87, (259, false, true), bc89],
  some (some bc242)),
 ([bc241, bc86, bc87, (259, false, true), bc90],
  some (some bc242)),
 ([bc241, bc86, bc87, (259, true, false), bc89],
  some (some (266, true, true))),
 ([bc241, bc86, bc87, (259, true, false), bc90],
  some (some (266, true, true))),
 ([bc241, bc86, bc88, (269, true, true), bc89],
  some (some bc242)),
 ([bc241, bc86, bc88, (269, true, true), bc90],
  some (some bc242)),
 ([bc241, bc86, bc88, (269, false, false), bc89],
  some (some (271, true, true))),
 ([bc241, bc86, bc88, (269, false, false), bc90],
  some (some (271, true, true))),
 ([bc241, (260, true, true), bc89], some (some bc242)),
 ([bc241, (260, true, true), bc90], some (some bc242))]
private def goalCodes8_2_24 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc243, (275, false, true), bc94], some (some bc244)),
 ([bc243, (275, false, true), bc95], some (some bc244)),
 ([bc243, bc91, bc92, (280, false, true), bc94],
  some (some bc244)),
 ([bc243, bc91, bc92, (280, false, true), bc95],
  some (some bc244)),
 ([bc243, bc91, bc92, (280, true, false), bc94],
  some (some (282, false, true))),
 ([bc243, bc91, bc92, (280, true, false), bc95],
  some (some (282, false, true))),
 ([bc243, bc91, bc93, (283, true, true), bc94],
  some (some bc244)),
 ([bc243, bc91, bc93, (283, true, true), bc95],
  some (some bc244)),
 ([bc243, bc91, bc93, (283, false, false), bc94],
  some (some (285, false, true))),
 ([bc243, bc91, bc93, (283, false, false), bc95],
  some (some (285, false, true)))]
private def goalCodes8_2_27 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc0, bc8, bc9, bc10], some (some bc226)),
 ([bc0, bc8, bc9, bc11], some (some bc227)),
 ([bc0, bc8, bc12, bc13], some (some bc226)),
 ([bc0, bc8, bc12, bc14], some (some bc228)),
 ([bc0, bc15], some (some bc226)),
 ([bc1, bc2, bc3, bc8, bc9, bc10],
  some (some bc226)),
 ([bc1, bc2, bc3, bc8, bc9, bc11],
  some (some bc227)),
 ([bc1, bc2, bc3, bc8, bc12, bc13],
  some (some bc226)),
 ([bc1, bc2, bc3, bc8, bc12, bc14],
  some (some bc228)),
 ([bc1, bc2, bc3, bc15], some (some bc226)),
 ([bc1, bc2, bc4, bc8, bc9, bc10],
  some (some bc229)),
 ([bc1, bc2, bc4, bc8, bc9, bc11],
  some (some bc230)),
 ([bc1, bc2, bc4, bc8, bc12, bc13],
  some (some bc229)),
 ([bc1, bc2, bc4, bc8, bc12, bc14],
  some (some bc231)),
 ([bc1, bc2, bc4, bc15], some (some bc229)),
 ([bc1, bc5, bc6, bc8, bc9, bc10],
  some (some bc226)),
 ([bc1, bc5, bc6, bc8, bc9, bc11],
  some (some bc227)),
 ([bc1, bc5, bc6, bc8, bc12, bc13],
  some (some bc226)),
 ([bc1, bc5, bc6, bc8, bc12, bc14],
  some (some bc228)),
 ([bc1, bc5, bc6, bc15], some (some bc226)),
 ([bc1, bc5, bc7, bc8, bc9, bc10],
  some (some bc232)),
 ([bc1, bc5, bc7, bc8, bc9, bc11],
  some (some bc233)),
 ([bc1, bc5, bc7, bc8, bc12, bc13],
  some (some bc232)),
 ([bc1, bc5, bc7, bc8, bc12, bc14],
  some (some bc234)),
 ([bc1, bc5, bc7, bc15], some (some bc232))]
private def goalCodes8_2_29 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc67, bc68, bc0, bc16, bc17],
  some (some bc245)),
 ([bc67, bc68, bc0, bc16, bc18],
  some (some (218, true, false))),
 ([bc67, bc68, bc0, bc19, bc20],
  some (some bc245)),
 ([bc67, bc68, bc0, bc19, bc21],
  some (some (219, true, false))),
 ([bc67, bc68, bc1], some (some bc245)),
 ([bc67, bc69, bc0, bc16, bc17],
  some (some (220, true, false))),
 ([bc67, bc69, bc0, bc16, bc18],
  some (some (221, true, false))),
 ([bc67, bc69, bc0, bc19, bc20],
  some (some (220, true, false))),
 ([bc67, bc69, bc0, bc19, bc21],
  some (some (222, true, false))),
 ([bc67, bc69, bc1], some (some (220, true, false))),
 ([bc70, bc71, bc0, bc16, bc17],
  some (some bc245)),
 ([bc70, bc71, bc0, bc16, bc18],
  some (some (218, true, false))),
 ([bc70, bc71, bc0, bc19, bc20],
  some (some bc245)),
 ([bc70, bc71, bc0, bc19, bc21],
  some (some (219, true, false))),
 ([bc70, bc71, bc1], some (some bc245)),
 ([bc70, bc72, bc0, bc16, bc17],
  some (some (223, true, false))),
 ([bc70, bc72, bc0, bc16, bc18],
  some (some (224, true, false))),
 ([bc70, bc72, bc0, bc19, bc20],
  some (some (223, true, false))),
 ([bc70, bc72, bc0, bc19, bc21],
  some (some (225, true, false))),
 ([bc70, bc72, bc1], some (some (223, true, false)))]
private def goalCodes8_2_30 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc67, bc68, bc96, bc97], some none),
 ([bc67, bc68, bc96, bc98], some none),
 ([bc67, bc68, bc99, bc100], some none),
 ([bc67, bc68, bc99, bc101], some none),
 ([bc67, bc69, bc96, bc97], some none),
 ([bc67, bc69, bc96, bc98], some none),
 ([bc67, bc69, bc99, bc100], some none),
 ([bc67, bc69, bc99, bc101], some none),
 ([bc70, bc71, bc96, bc97], some none),
 ([bc70, bc71, bc96, bc98], some none),
 ([bc70, bc71, bc99, bc100], some none),
 ([bc70, bc71, bc99, bc101], some none),
 ([bc70, bc72, bc96, bc97], some (some (287, true, false))),
 ([bc70, bc72, bc96, bc98], some (some (290, true, false))),
 ([bc70, bc72, bc99, bc100], some (some (287, true, false))),
 ([bc70, bc72, bc99, bc101], some (some (292, true, false)))]
private def goalCodes8_2_31 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([], some (some (294, false, false)))]
private def goalCodes8_3_0 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes8_2_0
private def goalCodes8_3_2 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes8_2_2
private def goalCodes8_3_5 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes8_2_5
private def goalCodes8_3_7 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc2, bc102, bc103, bc104, bc110],
  some (some bc246)),
 ([bc2,
   bc102,
   bc103,
   bc104,
   bc111,
   bc112,
   bc113],
  some (some bc246)),
 ([bc2,
   bc102,
   bc103,
   bc104,
   bc111,
   bc112,
   bc114],
  some (some (304, true, true))),
 ([bc2,
   bc102,
   bc103,
   bc104,
   bc111,
   bc115,
   bc116],
  some (some bc246)),
 ([bc2,
   bc102,
   bc103,
   bc104,
   bc111,
   bc115,
   bc117],
  some (some (309, true, true))),
 ([bc2, bc102, bc103, bc105, bc110],
  some (some (310, true, true))),
 ([bc2,
   bc102,
   bc103,
   bc105,
   bc111,
   bc112,
   bc113],
  some (some (310, true, true))),
 ([bc2,
   bc102,
   bc103,
   bc105,
   bc111,
   bc112,
   bc114],
  some (some (311, true, true))),
 ([bc2,
   bc102,
   bc103,
   bc105,
   bc111,
   bc115,
   bc116],
  some (some (310, true, true))),
 ([bc2,
   bc102,
   bc103,
   bc105,
   bc111,
   bc115,
   bc117],
  some (some (312, true, true))),
 ([bc2, bc102, bc106, bc107, bc110],
  some (some bc246)),
 ([bc2,
   bc102,
   bc106,
   bc107,
   bc111,
   bc112,
   bc113],
  some (some bc246)),
 ([bc2,
   bc102,
   bc106,
   bc107,
   bc111,
   bc112,
   bc114],
  some (some (304, true, true))),
 ([bc2,
   bc102,
   bc106,
   bc107,
   bc111,
   bc115,
   bc116],
  some (some bc246)),
 ([bc2,
   bc102,
   bc106,
   bc107,
   bc111,
   bc115,
   bc117],
  some (some (309, true, true))),
 ([bc2, bc102, bc106, bc108, bc110],
  some (some (314, true, true))),
 ([bc2,
   bc102,
   bc106,
   bc108,
   bc111,
   bc112,
   bc113],
  some (some (314, true, true))),
 ([bc2,
   bc102,
   bc106,
   bc108,
   bc111,
   bc112,
   bc114],
  some (some (315, true, true))),
 ([bc2,
   bc102,
   bc106,
   bc108,
   bc111,
   bc115,
   bc116],
  some (some (314, true, true))),
 ([bc2,
   bc102,
   bc106,
   bc108,
   bc111,
   bc115,
   bc117],
  some (some (316, true, true))),
 ([bc2, bc109, bc110], some (some bc246)),
 ([bc2, bc109, bc111, bc112, bc113],
  some (some bc246)),
 ([bc2, bc109, bc111, bc112, bc114],
  some (some (304, true, true))),
 ([bc2, bc109, bc111, bc115, bc116],
  some (some bc246)),
 ([bc2, bc109, bc111, bc115, bc117],
  some (some (309, true, true)))]
private def goalCodes8_3_9 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc5, bc118, bc126, bc127, bc128],
  some (some bc247)),
 ([bc5, bc118, bc126, bc127, bc129],
  some (some (323, false, true))),
 ([bc5, bc118, bc126, bc130, bc131],
  some (some bc247)),
 ([bc5, bc118, bc126, bc130, bc132],
  some (some (327, false, true))),
 ([bc5, bc118, bc133], some (some bc247)),
 ([bc5,
   bc119,
   bc120,
   bc121,
   bc126,
   bc127,
   bc128],
  some (some bc247)),
 ([bc5,
   bc119,
   bc120,
   bc121,
   bc126,
   bc127,
   bc129],
  some (some (323, false, true))),
 ([bc5,
   bc119,
   bc120,
   bc121,
   bc126,
   bc130,
   bc131],
  some (some bc247)),
 ([bc5,
   bc119,
   bc120,
   bc121,
   bc126,
   bc130,
   bc132],
  some (some (327, false, true))),
 ([bc5, bc119, bc120, bc121, bc133],
  some (some bc247)),
 ([bc5,
   bc119,
   bc120,
   bc122,
   bc126,
   bc127,
   bc128],
  some (some (334, false, true))),
 ([bc5,
   bc119,
   bc120,
   bc122,
   bc126,
   bc127,
   bc129],
  some (some (335, false, true))),
 ([bc5,
   bc119,
   bc120,
   bc122,
   bc126,
   bc130,
   bc131],
  some (some (334, false, true))),
 ([bc5,
   bc119,
   bc120,
   bc122,
   bc126,
   bc130,
   bc132],
  some (some (336, false, true))),
 ([bc5, bc119, bc120, bc122, bc133],
  some (some (334, false, true))),
 ([bc5,
   bc119,
   bc123,
   bc124,
   bc126,
   bc127,
   bc128],
  some (some bc247)),
 ([bc5,
   bc119,
   bc123,
   bc124,
   bc126,
   bc127,
   bc129],
  some (some (323, false, true))),
 ([bc5,
   bc119,
   bc123,
   bc124,
   bc126,
   bc130,
   bc131],
  some (some bc247)),
 ([bc5,
   bc119,
   bc123,
   bc124,
   bc126,
   bc130,
   bc132],
  some (some (327, false, true))),
 ([bc5, bc119, bc123, bc124, bc133],
  some (some bc247)),
 ([bc5,
   bc119,
   bc123,
   bc125,
   bc126,
   bc127,
   bc128],
  some (some (340, false, true))),
 ([bc5,
   bc119,
   bc123,
   bc125,
   bc126,
   bc127,
   bc129],
  some (some (341, false, true))),
 ([bc5,
   bc119,
   bc123,
   bc125,
   bc126,
   bc130,
   bc131],
  some (some (340, false, true))),
 ([bc5,
   bc119,
   bc123,
   bc125,
   bc126,
   bc130,
   bc132],
  some (some (342, false, true))),
 ([bc5, bc119, bc123, bc125, bc133],
  some (some (340, false, true)))]
private def goalCodes8_3_12 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc208, bc134, bc135, bc136, bc142],
  some (some bc248)),
 ([bc208,
   bc134,
   bc135,
   bc136,
   bc143,
   bc144,
   bc145],
  some (some bc248)),
 ([bc208,
   bc134,
   bc135,
   bc136,
   bc143,
   bc144,
   bc146],
  some (some (350, true, true))),
 ([bc208,
   bc134,
   bc135,
   bc136,
   bc143,
   bc147,
   bc148],
  some (some bc248)),
 ([bc208,
   bc134,
   bc135,
   bc136,
   bc143,
   bc147,
   bc149],
  some (some (354, true, true))),
 ([bc208, bc134, bc135, bc137, bc142],
  some (some (356, true, true))),
 ([bc208,
   bc134,
   bc135,
   bc137,
   bc143,
   bc144,
   bc145],
  some (some (356, true, true))),
 ([bc208,
   bc134,
   bc135,
   bc137,
   bc143,
   bc144,
   bc146],
  some (some (357, true, true))),
 ([bc208,
   bc134,
   bc135,
   bc137,
   bc143,
   bc147,
   bc148],
  some (some (356, true, true))),
 ([bc208,
   bc134,
   bc135,
   bc137,
   bc143,
   bc147,
   bc149],
  some (some (358, true, true))),
 ([bc208, bc134, bc138, bc139, bc142],
  some (some bc248)),
 ([bc208,
   bc134,
   bc138,
   bc139,
   bc143,
   bc144,
   bc145],
  some (some bc248)),
 ([bc208,
   bc134,
   bc138,
   bc139,
   bc143,
   bc144,
   bc146],
  some (some (350, true, true))),
 ([bc208,
   bc134,
   bc138,
   bc139,
   bc143,
   bc147,
   bc148],
  some (some bc248)),
 ([bc208,
   bc134,
   bc138,
   bc139,
   bc143,
   bc147,
   bc149],
  some (some (354, true, true))),
 ([bc208, bc134, bc138, bc140, bc142],
  some (some (360, true, true))),
 ([bc208,
   bc134,
   bc138,
   bc140,
   bc143,
   bc144,
   bc145],
  some (some (360, true, true))),
 ([bc208,
   bc134,
   bc138,
   bc140,
   bc143,
   bc144,
   bc146],
  some (some (361, true, true))),
 ([bc208,
   bc134,
   bc138,
   bc140,
   bc143,
   bc147,
   bc148],
  some (some (360, true, true))),
 ([bc208,
   bc134,
   bc138,
   bc140,
   bc143,
   bc147,
   bc149],
  some (some (362, true, true))),
 ([bc208, bc141, bc142], some (some bc248)),
 ([bc208, bc141, bc143, bc144, bc145],
  some (some bc248)),
 ([bc208, bc141, bc143, bc144, bc146],
  some (some (350, true, true))),
 ([bc208, bc141, bc143, bc147, bc148],
  some (some bc248)),
 ([bc208, bc141, bc143, bc147, bc149],
  some (some (354, true, true)))]
private def goalCodes8_3_14 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc211, (365, false, true), bc153], some (some bc249)),
 ([bc211, (365, false, true), bc154], some (some bc249)),
 ([bc211, bc150, bc151, (370, false, true), bc153],
  some (some bc249)),
 ([bc211, bc150, bc151, (370, false, true), bc154],
  some (some bc249)),
 ([bc211, bc150, bc151, (370, true, false), bc153],
  some (some (372, false, true))),
 ([bc211, bc150, bc151, (370, true, false), bc154],
  some (some (372, false, true))),
 ([bc211, bc150, bc152, (373, true, true), bc153],
  some (some bc249)),
 ([bc211, bc150, bc152, (373, true, true), bc154],
  some (some bc249)),
 ([bc211, bc150, bc152, (373, false, false), bc153],
  some (some (375, false, true))),
 ([bc211, bc150, bc152, (373, false, false), bc154],
  some (some (375, false, true)))]
private def goalCodes8_3_17 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc214, bc155, bc156, bc157, bc163],
  some (some bc250)),
 ([bc214,
   bc155,
   bc156,
   bc157,
   bc164,
   bc165,
   bc166],
  some (some bc250)),
 ([bc214,
   bc155,
   bc156,
   bc157,
   bc164,
   bc165,
   bc167],
  some (some (385, true, true))),
 ([bc214,
   bc155,
   bc156,
   bc157,
   bc164,
   bc168,
   bc169],
  some (some bc250)),
 ([bc214,
   bc155,
   bc156,
   bc157,
   bc164,
   bc168,
   bc170],
  some (some (390, true, true))),
 ([bc214, bc155, bc156, bc158, bc163],
  some (some (391, true, true))),
 ([bc214,
   bc155,
   bc156,
   bc158,
   bc164,
   bc165,
   bc166],
  some (some (391, true, true))),
 ([bc214,
   bc155,
   bc156,
   bc158,
   bc164,
   bc165,
   bc167],
  some (some (393, true, true))),
 ([bc214,
   bc155,
   bc156,
   bc158,
   bc164,
   bc168,
   bc169],
  some (some (391, true, true))),
 ([bc214,
   bc155,
   bc156,
   bc158,
   bc164,
   bc168,
   bc170],
  some (some (394, true, true))),
 ([bc214, bc155, bc159, bc160, bc163],
  some (some bc250)),
 ([bc214,
   bc155,
   bc159,
   bc160,
   bc164,
   bc165,
   bc166],
  some (some bc250)),
 ([bc214,
   bc155,
   bc159,
   bc160,
   bc164,
   bc165,
   bc167],
  some (some (385, true, true))),
 ([bc214,
   bc155,
   bc159,
   bc160,
   bc164,
   bc168,
   bc169],
  some (some bc250)),
 ([bc214,
   bc155,
   bc159,
   bc160,
   bc164,
   bc168,
   bc170],
  some (some (390, true, true))),
 ([bc214, bc155, bc159, bc161, bc163],
  some (some (398, true, true))),
 ([bc214,
   bc155,
   bc159,
   bc161,
   bc164,
   bc165,
   bc166],
  some (some (398, true, true))),
 ([bc214,
   bc155,
   bc159,
   bc161,
   bc164,
   bc165,
   bc167],
  some (some (399, true, true))),
 ([bc214,
   bc155,
   bc159,
   bc161,
   bc164,
   bc168,
   bc169],
  some (some (398, true, true))),
 ([bc214,
   bc155,
   bc159,
   bc161,
   bc164,
   bc168,
   bc170],
  some (some (400, true, true))),
 ([bc214, bc162, bc163], some (some bc250)),
 ([bc214, bc162, bc164, bc165, bc166],
  some (some bc250)),
 ([bc214, bc162, bc164, bc165, bc167],
  some (some (385, true, true))),
 ([bc214, bc162, bc164, bc168, bc169],
  some (some bc250)),
 ([bc214, bc162, bc164, bc168, bc170],
  some (some (390, true, true)))]
private def goalCodes8_3_19 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc217, bc171, bc179, bc180, bc181],
  some (some bc251)),
 ([bc217, bc171, bc179, bc180, bc182],
  some (some (407, false, true))),
 ([bc217, bc171, bc179, bc183, bc184],
  some (some bc251)),
 ([bc217, bc171, bc179, bc183, bc185],
  some (some (411, false, true))),
 ([bc217, bc171, bc186], some (some bc251)),
 ([bc217,
   bc172,
   bc173,
   bc174,
   bc179,
   bc180,
   bc181],
  some (some bc251)),
 ([bc217,
   bc172,
   bc173,
   bc174,
   bc179,
   bc180,
   bc182],
  some (some (407, false, true))),
 ([bc217,
   bc172,
   bc173,
   bc174,
   bc179,
   bc183,
   bc184],
  some (some bc251)),
 ([bc217,
   bc172,
   bc173,
   bc174,
   bc179,
   bc183,
   bc185],
  some (some (411, false, true))),
 ([bc217, bc172, bc173, bc174, bc186],
  some (some bc251)),
 ([bc217,
   bc172,
   bc173,
   bc175,
   bc179,
   bc180,
   bc181],
  some (some (418, false, true))),
 ([bc217,
   bc172,
   bc173,
   bc175,
   bc179,
   bc180,
   bc182],
  some (some (419, false, true))),
 ([bc217,
   bc172,
   bc173,
   bc175,
   bc179,
   bc183,
   bc184],
  some (some (418, false, true))),
 ([bc217,
   bc172,
   bc173,
   bc175,
   bc179,
   bc183,
   bc185],
  some (some (420, false, true))),
 ([bc217, bc172, bc173, bc175, bc186],
  some (some (418, false, true))),
 ([bc217,
   bc172,
   bc176,
   bc177,
   bc179,
   bc180,
   bc181],
  some (some bc251)),
 ([bc217,
   bc172,
   bc176,
   bc177,
   bc179,
   bc180,
   bc182],
  some (some (407, false, true))),
 ([bc217,
   bc172,
   bc176,
   bc177,
   bc179,
   bc183,
   bc184],
  some (some bc251)),
 ([bc217,
   bc172,
   bc176,
   bc177,
   bc179,
   bc183,
   bc185],
  some (some (411, false, true))),
 ([bc217, bc172, bc176, bc177, bc186],
  some (some bc251)),
 ([bc217,
   bc172,
   bc176,
   bc178,
   bc179,
   bc180,
   bc181],
  some (some (424, false, true))),
 ([bc217,
   bc172,
   bc176,
   bc178,
   bc179,
   bc180,
   bc182],
  some (some (425, false, true))),
 ([bc217,
   bc172,
   bc176,
   bc178,
   bc179,
   bc183,
   bc184],
  some (some (424, false, true))),
 ([bc217,
   bc172,
   bc176,
   bc178,
   bc179,
   bc183,
   bc185],
  some (some (426, false, true))),
 ([bc217, bc172, bc176, bc178, bc186],
  some (some (424, false, true)))]
private def goalCodes8_3_22 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc220, bc187, bc188, (427, false, true), bc190],
  some (some bc252)),
 ([bc220, bc187, bc188, (427, false, true), bc191],
  some (some bc252)),
 ([bc220, bc187, bc188, (427, true, false), bc190],
  some (some (434, true, true))),
 ([bc220, bc187, bc188, (427, true, false), bc191],
  some (some (434, true, true))),
 ([bc220, bc187, bc189, (436, true, true), bc190],
  some (some bc252)),
 ([bc220, bc187, bc189, (436, true, true), bc191],
  some (some bc252)),
 ([bc220, bc187, bc189, (436, false, false), bc190],
  some (some (439, true, true))),
 ([bc220, bc187, bc189, (436, false, false), bc191],
  some (some (439, true, true))),
 ([bc220, (432, true, true), bc190], some (some bc252)),
 ([bc220, (432, true, true), bc191], some (some bc252))]
private def goalCodes8_3_24 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc223, bc192, bc200, bc201, bc202],
  some (some bc253)),
 ([bc223, bc192, bc200, bc201, bc203],
  some (some (447, false, true))),
 ([bc223, bc192, bc200, bc204, bc205],
  some (some bc253)),
 ([bc223, bc192, bc200, bc204, bc206],
  some (some (451, false, true))),
 ([bc223, bc192, bc207], some (some bc253)),
 ([bc223,
   bc193,
   bc194,
   bc195,
   bc200,
   bc201,
   bc202],
  some (some bc253)),
 ([bc223,
   bc193,
   bc194,
   bc195,
   bc200,
   bc201,
   bc203],
  some (some (447, false, true))),
 ([bc223,
   bc193,
   bc194,
   bc195,
   bc200,
   bc204,
   bc205],
  some (some bc253)),
 ([bc223,
   bc193,
   bc194,
   bc195,
   bc200,
   bc204,
   bc206],
  some (some (451, false, true))),
 ([bc223, bc193, bc194, bc195, bc207],
  some (some bc253)),
 ([bc223,
   bc193,
   bc194,
   bc196,
   bc200,
   bc201,
   bc202],
  some (some (458, false, true))),
 ([bc223,
   bc193,
   bc194,
   bc196,
   bc200,
   bc201,
   bc203],
  some (some (459, false, true))),
 ([bc223,
   bc193,
   bc194,
   bc196,
   bc200,
   bc204,
   bc205],
  some (some (458, false, true))),
 ([bc223,
   bc193,
   bc194,
   bc196,
   bc200,
   bc204,
   bc206],
  some (some (460, false, true))),
 ([bc223, bc193, bc194, bc196, bc207],
  some (some (458, false, true))),
 ([bc223,
   bc193,
   bc197,
   bc198,
   bc200,
   bc201,
   bc202],
  some (some bc253)),
 ([bc223,
   bc193,
   bc197,
   bc198,
   bc200,
   bc201,
   bc203],
  some (some (447, false, true))),
 ([bc223,
   bc193,
   bc197,
   bc198,
   bc200,
   bc204,
   bc205],
  some (some bc253)),
 ([bc223,
   bc193,
   bc197,
   bc198,
   bc200,
   bc204,
   bc206],
  some (some (451, false, true))),
 ([bc223, bc193, bc197, bc198, bc207],
  some (some bc253)),
 ([bc223,
   bc193,
   bc197,
   bc199,
   bc200,
   bc201,
   bc202],
  some (some (464, false, true))),
 ([bc223,
   bc193,
   bc197,
   bc199,
   bc200,
   bc201,
   bc203],
  some (some (465, false, true))),
 ([bc223,
   bc193,
   bc197,
   bc199,
   bc200,
   bc204,
   bc205],
  some (some (464, false, true))),
 ([bc223,
   bc193,
   bc197,
   bc199,
   bc200,
   bc204,
   bc206],
  some (some (466, false, true))),
 ([bc223, bc193, bc197, bc199, bc207],
  some (some (464, false, true)))]
private def goalCodes8_3_27 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes8_2_12
private def goalCodes8_3_29 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes8_2_14
private def goalCodes8_3_32 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc2, bc3, bc8, bc9, bc10],
  some (some bc226)),
 ([bc2, bc3, bc8, bc9, bc11],
  some (some bc227)),
 ([bc2, bc3, bc8, bc12, bc13],
  some (some bc226)),
 ([bc2, bc3, bc8, bc12, bc14],
  some (some bc228)),
 ([bc2, bc3, bc15], some (some bc226)),
 ([bc2, bc4, bc8, bc9, bc10],
  some (some bc229)),
 ([bc2, bc4, bc8, bc9, bc11],
  some (some bc230)),
 ([bc2, bc4, bc8, bc12, bc13],
  some (some bc229)),
 ([bc2, bc4, bc8, bc12, bc14],
  some (some bc231)),
 ([bc2, bc4, bc15], some (some bc229)),
 ([bc5, bc6, bc8, bc9, bc10],
  some (some bc226)),
 ([bc5, bc6, bc8, bc9, bc11],
  some (some bc227)),
 ([bc5, bc6, bc8, bc12, bc13],
  some (some bc226)),
 ([bc5, bc6, bc8, bc12, bc14],
  some (some bc228)),
 ([bc5, bc6, bc15], some (some bc226)),
 ([bc5, bc7, bc8, bc9, bc10],
  some (some bc232)),
 ([bc5, bc7, bc8, bc9, bc11],
  some (some bc233)),
 ([bc5, bc7, bc8, bc12, bc13],
  some (some bc232)),
 ([bc5, bc7, bc8, bc12, bc14],
  some (some bc234)),
 ([bc5, bc7, bc15], some (some bc232))]
private def goalCodes8_3_34 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc208, bc209, bc2, bc41], some (some bc254)),
 ([bc208, bc209, bc2, bc42], some (some (468, true, false))),
 ([bc208, bc209, bc5, bc44], some (some bc254)),
 ([bc208, bc209, bc5, bc45], some (some (469, true, false))),
 ([bc208, bc210, bc2, bc41], some (some (470, true, false))),
 ([bc208, bc210, bc2, bc42], some (some (471, true, false))),
 ([bc208, bc210, bc5, bc44], some (some (470, true, false))),
 ([bc208, bc210, bc5, bc45], some (some (472, true, false))),
 ([bc211, bc212, bc2, bc41], some (some bc254)),
 ([bc211, bc212, bc2, bc42], some (some (468, true, false))),
 ([bc211, bc212, bc5, bc44], some (some bc254)),
 ([bc211, bc212, bc5, bc45], some (some (469, true, false))),
 ([bc211, bc213, bc2, bc41], some (some (473, true, false))),
 ([bc211, bc213, bc2, bc42], some (some (474, true, false))),
 ([bc211, bc213, bc5, bc44], some (some (473, true, false))),
 ([bc211, bc213, bc5, bc45], some (some (475, true, false)))]
private def goalCodes8_3_35 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc208, bc209, bc214, bc215], some (some bc255)),
 ([bc208, bc209, bc214, bc216], some (some (477, true, false))),
 ([bc208, bc209, bc217, bc218], some (some bc255)),
 ([bc208, bc209, bc217, bc219], some (some (481, true, false))),
 ([bc208, bc210, bc214, bc215], some (some (159, true, false))),
 ([bc208, bc210, bc214, bc216], some (some (482, true, false))),
 ([bc208, bc210, bc217, bc218], some (some (159, true, false))),
 ([bc208, bc210, bc217, bc219], some (some (483, true, false))),
 ([bc211, bc212, bc214, bc215], some (some bc255)),
 ([bc211, bc212, bc214, bc216], some (some (477, true, false))),
 ([bc211, bc212, bc217, bc218], some (some bc255)),
 ([bc211, bc212, bc217, bc219], some (some (481, true, false))),
 ([bc211, bc213, bc214, bc215], some (some (165, true, false))),
 ([bc211, bc213, bc214, bc216], some (some (484, true, false))),
 ([bc211, bc213, bc217, bc218], some (some (165, true, false))),
 ([bc211, bc213, bc217, bc219], some (some (485, true, false)))]
private def goalCodes8_3_36 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc214, bc35], some (some (486, false, false))),
 ([bc214, bc36], some (some (487, false, false))),
 ([bc217, bc38], some (some (486, false, false))),
 ([bc217, bc39], some (some (488, false, false)))]
private def goalCodes8_3_38 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc220, bc221, bc214, bc215], some (some bc256)),
 ([bc220, bc221, bc214, bc216], some (some (491, false, false))),
 ([bc220, bc221, bc217, bc218], some (some bc256)),
 ([bc220, bc221, bc217, bc219], some (some (492, false, false))),
 ([bc220, bc222, bc214, bc215], some (some (494, false, false))),
 ([bc220, bc222, bc214, bc216], some (some (495, false, false))),
 ([bc220, bc222, bc217, bc218], some (some (494, false, false))),
 ([bc220, bc222, bc217, bc219], some (some (496, false, false))),
 ([bc223, bc224, bc214, bc215], some (some bc256)),
 ([bc223, bc224, bc214, bc216], some (some (491, false, false))),
 ([bc223, bc224, bc217, bc218], some (some bc256)),
 ([bc223, bc224, bc217, bc219], some (some (492, false, false))),
 ([bc223, bc225, bc214, bc215], some (some (499, false, false))),
 ([bc223, bc225, bc214, bc216], some (some (500, false, false))),
 ([bc223, bc225, bc217, bc218], some (some (499, false, false))),
 ([bc223, bc225, bc217, bc219], some (some (501, false, false)))]
private def goalCodes8_3_39 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc220, bc221], some (some (502, false, false))),
 ([bc220, bc222], some (some (503, false, false))),
 ([bc223, bc224], some (some (502, false, false))),
 ([bc223, bc225], some (some (504, false, false)))]
private def goalCodes8_3_40 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc67, bc68], some (some (505, true, false))),
 ([bc67, bc69], some (some (506, true, false))),
 ([bc70, bc71], some (some (505, true, false))),
 ([bc70, bc72], some (some (507, true, false)))]
private def goalCodes8_3_42 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc73, bc74], some (some (227, false, false))),
 ([bc73, (176, true, false)], some none),
 ([bc75, (228, true, true)], some (some (227, false, false))),
 ([bc75, (228, false, false)], some (some (230, false, false)))]
private def goalCodes8_4_0 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes8_2_0
private def goalCodes8_4_2 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes8_2_2
private def goalCodes8_4_5 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes8_2_5
private def goalCodes8_4_7 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes8_3_7
private def goalCodes8_4_9 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes8_3_9
private def goalCodes8_4_12 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes8_3_12
private def goalCodes8_4_14 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes8_3_14
private def goalCodes8_4_17 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes8_3_17
private def goalCodes8_4_19 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes8_3_19
private def goalCodes8_4_22 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes8_3_22
private def goalCodes8_4_24 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes8_3_24
private def goalCodes8_4_27 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes8_2_12
private def cutCodes8_2 : List (ℕ × Bool × Bool) := [(7, true, false), (177, false, false), bc74]
private def cutCodes8_3 : List (ℕ × Bool × Bool) := [(7, true, false), (177, true, true), (296, false, true), (176, true, false)]
private def cutCodes8_4 : List (ℕ × Bool × Bool) := [(7, true, false), (177, true, true), (296, false, true), bc74]

private abbrev goalSpec8_2_31 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 8) 2))[31-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal8_2_31 : trunkGoalBranches (trunkCatalog.states 8) 2 31 = goalCodes8_2_31.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 8).context goalSpec8_2_31 = _
  exact (cachedBranches_eq (trunkCatalog.states 8).context goalSpec8_2_31
    endpointInput8_33 endpointInput8_23 (([] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes8_33.map decodeEndpoint8) (endpointCodes8_23.map decodeEndpoint8)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint8_33 hEndpoint8_23).trans
    (by decide +kernel)

private abbrev goalSpec8_2_2 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 8) 2))[2-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal8_2_2 : trunkGoalBranches (trunkCatalog.states 8) 2 2 = goalCodes8_2_2.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 8).context goalSpec8_2_2 = _
  exact (cachedBranches_eq (trunkCatalog.states 8).context goalSpec8_2_2
    endpointInput8_4 endpointInput8_5 (([bc8] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes8_4.map decodeEndpoint8) (endpointCodes8_5.map decodeEndpoint8)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint8_4 hEndpoint8_5).trans
    (by decide +kernel)

private abbrev goalSpec8_2_5 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 8) 2))[5-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal8_2_5 : trunkGoalBranches (trunkCatalog.states 8) 2 5 = goalCodes8_2_5.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 8).context goalSpec8_2_5 = _
  exact (cachedBranches_eq (trunkCatalog.states 8).context goalSpec8_2_5
    endpointInput8_6 endpointInput8_7 (([bc15] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes8_6.map decodeEndpoint8) (endpointCodes8_7.map decodeEndpoint8)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint8_6 hEndpoint8_7).trans
    (by decide +kernel)

private abbrev goalSpec8_2_10 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 8) 2))[10-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal8_2_10 : trunkGoalBranches (trunkCatalog.states 8) 2 10 = goalCodes8_2_10.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 8).context goalSpec8_2_10 = _
  exact (cachedBranches_eq (trunkCatalog.states 8).context goalSpec8_2_10
    endpointInput8_10 endpointInput8_11 (([bc1] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes8_10.map decodeEndpoint8) (endpointCodes8_11.map decodeEndpoint8)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint8_10 hEndpoint8_11).trans
    (by decide +kernel)

private abbrev goalSpec8_2_12 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 8) 2))[12-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal8_2_12 : trunkGoalBranches (trunkCatalog.states 8) 2 12 = goalCodes8_2_12.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 8).context goalSpec8_2_12 = _
  exact (cachedBranches_eq (trunkCatalog.states 8).context goalSpec8_2_12
    endpointInput8_17 endpointInput8_18 (([bc67] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes8_17.map decodeEndpoint8) (endpointCodes8_18.map decodeEndpoint8)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint8_17 hEndpoint8_18).trans
    (by decide +kernel)

private abbrev goalSpec8_2_14 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 8) 2))[14-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal8_2_14 : trunkGoalBranches (trunkCatalog.states 8) 2 14 = goalCodes8_2_14.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 8).context goalSpec8_2_14 = _
  exact (cachedBranches_eq (trunkCatalog.states 8).context goalSpec8_2_14
    endpointInput8_19 endpointInput8_20 (([bc70] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes8_19.map decodeEndpoint8) (endpointCodes8_20.map decodeEndpoint8)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint8_19 hEndpoint8_20).trans
    (by decide +kernel)

private abbrev goalSpec8_2_18 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 8) 2))[18-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal8_2_18 : trunkGoalBranches (trunkCatalog.states 8) 2 18 = goalCodes8_2_18.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 8).context goalSpec8_2_18 = _
  exact (cachedBranches_eq (trunkCatalog.states 8).context goalSpec8_2_18
    endpointInput8_24 endpointInput8_25 (([bc96] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes8_24.map decodeEndpoint8) (endpointCodes8_25.map decodeEndpoint8)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint8_24 hEndpoint8_25).trans
    (by decide +kernel)

private abbrev goalSpec8_2_20 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 8) 2))[20-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal8_2_20 : trunkGoalBranches (trunkCatalog.states 8) 2 20 = goalCodes8_2_20.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 8).context goalSpec8_2_20 = _
  exact (cachedBranches_eq (trunkCatalog.states 8).context goalSpec8_2_20
    endpointInput8_26 endpointInput8_27 (([bc99] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes8_26.map decodeEndpoint8) (endpointCodes8_27.map decodeEndpoint8)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint8_26 hEndpoint8_27).trans
    (by decide +kernel)

private abbrev goalSpec8_2_22 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 8) 2))[22-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal8_2_22 : trunkGoalBranches (trunkCatalog.states 8) 2 22 = goalCodes8_2_22.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 8).context goalSpec8_2_22 = _
  exact (cachedBranches_eq (trunkCatalog.states 8).context goalSpec8_2_22
    endpointInput8_28 endpointInput8_29 (([bc241] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes8_28.map decodeEndpoint8) (endpointCodes8_29.map decodeEndpoint8)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint8_28 hEndpoint8_29).trans
    (by decide +kernel)

private abbrev goalSpec8_2_24 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 8) 2))[24-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal8_2_24 : trunkGoalBranches (trunkCatalog.states 8) 2 24 = goalCodes8_2_24.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 8).context goalSpec8_2_24 = _
  exact (cachedBranches_eq (trunkCatalog.states 8).context goalSpec8_2_24
    endpointInput8_30 endpointInput8_31 (([bc243] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes8_30.map decodeEndpoint8) (endpointCodes8_31.map decodeEndpoint8)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint8_30 hEndpoint8_31).trans
    (by decide +kernel)

private abbrev goalSpec8_2_27 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 8) 2))[27-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal8_2_27 : trunkGoalBranches (trunkCatalog.states 8) 2 27 = goalCodes8_2_27.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 8).context goalSpec8_2_27 = _
  exact (cachedBranches_eq (trunkCatalog.states 8).context goalSpec8_2_27
    endpointInput8_0 endpointInput8_1 (([] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes8_0.map decodeEndpoint8) (endpointCodes8_1.map decodeEndpoint8)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint8_0 hEndpoint8_1).trans
    (by decide +kernel)

private abbrev goalSpec8_2_29 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 8) 2))[29-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal8_2_29 : trunkGoalBranches (trunkCatalog.states 8) 2 29 = goalCodes8_2_29.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 8).context goalSpec8_2_29 = _
  exact (cachedBranches_eq (trunkCatalog.states 8).context goalSpec8_2_29
    endpointInput8_21 endpointInput8_3 (([] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes8_21.map decodeEndpoint8) (endpointCodes8_3.map decodeEndpoint8)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint8_21 hEndpoint8_3).trans
    (by decide +kernel)

private theorem hGoal8_2_0 : trunkGoalBranches (trunkCatalog.states 8) 2 0 = goalCodes8_2_0.map decodeGoalBranch := by
  decide +kernel

private abbrev goalSpec8_2_30 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 8) 2))[30-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal8_2_30 : trunkGoalBranches (trunkCatalog.states 8) 2 30 = goalCodes8_2_30.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 8).context goalSpec8_2_30 = _
  exact (cachedBranches_eq (trunkCatalog.states 8).context goalSpec8_2_30
    endpointInput8_21 endpointInput8_32 (([] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes8_21.map decodeEndpoint8) (endpointCodes8_32.map decodeEndpoint8)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint8_21 hEndpoint8_32).trans
    (by decide +kernel)

private theorem hGoal8_3_0 : trunkGoalBranches (trunkCatalog.states 8) 3 0 = goalCodes8_3_0.map decodeGoalBranch := by
  exact hGoal8_2_0

private abbrev goalSpec8_3_2 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 8) 3))[2-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal8_3_2 : trunkGoalBranches (trunkCatalog.states 8) 3 2 = goalCodes8_3_2.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 8) 3 2 = trunkGoalBranches (trunkCatalog.states 8) 2 2 := by
      apply congrArg (trunkBranches (trunkCatalog.states 8).context)
      decide +kernel
    exact he.trans hGoal8_2_2
  | change trunkBranches (trunkCatalog.states 8).context goalSpec8_3_2 = _
    exact (cachedBranches_eq (trunkCatalog.states 8).context goalSpec8_3_2
      endpointInput8_4 endpointInput8_5 (([bc8] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
      (endpointCodes8_4.map decodeEndpoint8) (endpointCodes8_5.map decodeEndpoint8)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint8_4 hEndpoint8_5).trans
      (by decide +kernel)

private abbrev goalSpec8_3_5 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 8) 3))[5-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal8_3_5 : trunkGoalBranches (trunkCatalog.states 8) 3 5 = goalCodes8_3_5.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 8) 3 5 = trunkGoalBranches (trunkCatalog.states 8) 2 5 := by
      apply congrArg (trunkBranches (trunkCatalog.states 8).context)
      decide +kernel
    exact he.trans hGoal8_2_5
  | change trunkBranches (trunkCatalog.states 8).context goalSpec8_3_5 = _
    exact (cachedBranches_eq (trunkCatalog.states 8).context goalSpec8_3_5
      endpointInput8_6 endpointInput8_7 (([bc15] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
      (endpointCodes8_6.map decodeEndpoint8) (endpointCodes8_7.map decodeEndpoint8)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint8_6 hEndpoint8_7).trans
      (by decide +kernel)

private abbrev goalSpec8_3_7 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 8) 3))[7-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal8_3_7 : trunkGoalBranches (trunkCatalog.states 8) 3 7 = goalCodes8_3_7.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 8).context goalSpec8_3_7 = _
  exact (cachedBranches_eq (trunkCatalog.states 8).context goalSpec8_3_7
    endpointInput8_34 endpointInput8_35 (([bc2] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes8_34.map decodeEndpoint8) (endpointCodes8_35.map decodeEndpoint8)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint8_34 hEndpoint8_35).trans
    (by decide +kernel)

private abbrev goalSpec8_3_9 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 8) 3))[9-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal8_3_9 : trunkGoalBranches (trunkCatalog.states 8) 3 9 = goalCodes8_3_9.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 8).context goalSpec8_3_9 = _
  exact (cachedBranches_eq (trunkCatalog.states 8).context goalSpec8_3_9
    endpointInput8_36 endpointInput8_37 (([bc5] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes8_36.map decodeEndpoint8) (endpointCodes8_37.map decodeEndpoint8)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint8_36 hEndpoint8_37).trans
    (by decide +kernel)

private abbrev goalSpec8_3_12 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 8) 3))[12-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal8_3_12 : trunkGoalBranches (trunkCatalog.states 8) 3 12 = goalCodes8_3_12.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 8).context goalSpec8_3_12 = _
  exact (cachedBranches_eq (trunkCatalog.states 8).context goalSpec8_3_12
    endpointInput8_38 endpointInput8_39 (([bc208] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes8_38.map decodeEndpoint8) (endpointCodes8_39.map decodeEndpoint8)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint8_38 hEndpoint8_39).trans
    (by decide +kernel)

private abbrev goalSpec8_3_14 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 8) 3))[14-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal8_3_14 : trunkGoalBranches (trunkCatalog.states 8) 3 14 = goalCodes8_3_14.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 8).context goalSpec8_3_14 = _
  exact (cachedBranches_eq (trunkCatalog.states 8).context goalSpec8_3_14
    endpointInput8_40 endpointInput8_41 (([bc211] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes8_40.map decodeEndpoint8) (endpointCodes8_41.map decodeEndpoint8)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint8_40 hEndpoint8_41).trans
    (by decide +kernel)

private abbrev goalSpec8_3_17 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 8) 3))[17-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal8_3_17 : trunkGoalBranches (trunkCatalog.states 8) 3 17 = goalCodes8_3_17.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 8).context goalSpec8_3_17 = _
  exact (cachedBranches_eq (trunkCatalog.states 8).context goalSpec8_3_17
    endpointInput8_42 endpointInput8_43 (([bc214] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes8_42.map decodeEndpoint8) (endpointCodes8_43.map decodeEndpoint8)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint8_42 hEndpoint8_43).trans
    (by decide +kernel)

private abbrev goalSpec8_3_19 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 8) 3))[19-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal8_3_19 : trunkGoalBranches (trunkCatalog.states 8) 3 19 = goalCodes8_3_19.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 8).context goalSpec8_3_19 = _
  exact (cachedBranches_eq (trunkCatalog.states 8).context goalSpec8_3_19
    endpointInput8_44 endpointInput8_45 (([bc217] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes8_44.map decodeEndpoint8) (endpointCodes8_45.map decodeEndpoint8)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint8_44 hEndpoint8_45).trans
    (by decide +kernel)

private abbrev goalSpec8_3_22 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 8) 3))[22-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal8_3_22 : trunkGoalBranches (trunkCatalog.states 8) 3 22 = goalCodes8_3_22.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 8).context goalSpec8_3_22 = _
  exact (cachedBranches_eq (trunkCatalog.states 8).context goalSpec8_3_22
    endpointInput8_46 endpointInput8_47 (([bc220] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes8_46.map decodeEndpoint8) (endpointCodes8_47.map decodeEndpoint8)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint8_46 hEndpoint8_47).trans
    (by decide +kernel)

private abbrev goalSpec8_3_24 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 8) 3))[24-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal8_3_24 : trunkGoalBranches (trunkCatalog.states 8) 3 24 = goalCodes8_3_24.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 8).context goalSpec8_3_24 = _
  exact (cachedBranches_eq (trunkCatalog.states 8).context goalSpec8_3_24
    endpointInput8_48 endpointInput8_49 (([bc223] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes8_48.map decodeEndpoint8) (endpointCodes8_49.map decodeEndpoint8)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint8_48 hEndpoint8_49).trans
    (by decide +kernel)

private abbrev goalSpec8_3_27 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 8) 3))[27-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal8_3_27 : trunkGoalBranches (trunkCatalog.states 8) 3 27 = goalCodes8_3_27.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 8) 3 27 = trunkGoalBranches (trunkCatalog.states 8) 2 12 := by
      apply congrArg (trunkBranches (trunkCatalog.states 8).context)
      decide +kernel
    exact he.trans hGoal8_2_12
  | change trunkBranches (trunkCatalog.states 8).context goalSpec8_3_27 = _
    exact (cachedBranches_eq (trunkCatalog.states 8).context goalSpec8_3_27
      endpointInput8_17 endpointInput8_18 (([bc67] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
      (endpointCodes8_17.map decodeEndpoint8) (endpointCodes8_18.map decodeEndpoint8)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint8_17 hEndpoint8_18).trans
      (by decide +kernel)

private abbrev goalSpec8_3_29 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 8) 3))[29-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal8_3_29 : trunkGoalBranches (trunkCatalog.states 8) 3 29 = goalCodes8_3_29.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 8) 3 29 = trunkGoalBranches (trunkCatalog.states 8) 2 14 := by
      apply congrArg (trunkBranches (trunkCatalog.states 8).context)
      decide +kernel
    exact he.trans hGoal8_2_14
  | change trunkBranches (trunkCatalog.states 8).context goalSpec8_3_29 = _
    exact (cachedBranches_eq (trunkCatalog.states 8).context goalSpec8_3_29
      endpointInput8_19 endpointInput8_20 (([bc70] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
      (endpointCodes8_19.map decodeEndpoint8) (endpointCodes8_20.map decodeEndpoint8)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint8_19 hEndpoint8_20).trans
      (by decide +kernel)

private abbrev goalSpec8_3_32 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 8) 3))[32-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal8_3_32 : trunkGoalBranches (trunkCatalog.states 8) 3 32 = goalCodes8_3_32.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 8).context goalSpec8_3_32 = _
  exact (cachedBranches_eq (trunkCatalog.states 8).context goalSpec8_3_32
    endpointInput8_50 endpointInput8_1 (([] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes8_50.map decodeEndpoint8) (endpointCodes8_1.map decodeEndpoint8)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint8_50 hEndpoint8_1).trans
    (by decide +kernel)

private abbrev goalSpec8_3_34 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 8) 3))[34-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal8_3_34 : trunkGoalBranches (trunkCatalog.states 8) 3 34 = goalCodes8_3_34.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 8).context goalSpec8_3_34 = _
  exact (cachedBranches_eq (trunkCatalog.states 8).context goalSpec8_3_34
    endpointInput8_51 endpointInput8_52 (([] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes8_51.map decodeEndpoint8) (endpointCodes8_52.map decodeEndpoint8)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint8_51 hEndpoint8_52).trans
    (by decide +kernel)

private abbrev goalSpec8_3_35 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 8) 3))[35-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal8_3_35 : trunkGoalBranches (trunkCatalog.states 8) 3 35 = goalCodes8_3_35.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 8).context goalSpec8_3_35 = _
  exact (cachedBranches_eq (trunkCatalog.states 8).context goalSpec8_3_35
    endpointInput8_51 endpointInput8_53 (([] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes8_51.map decodeEndpoint8) (endpointCodes8_53.map decodeEndpoint8)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint8_51 hEndpoint8_53).trans
    (by decide +kernel)

private abbrev goalSpec8_3_36 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 8) 3))[36-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal8_3_36 : trunkGoalBranches (trunkCatalog.states 8) 3 36 = goalCodes8_3_36.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 8).context goalSpec8_3_36 = _
  exact (cachedBranches_eq (trunkCatalog.states 8).context goalSpec8_3_36
    endpointInput8_54 endpointInput8_55 (([] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes8_54.map decodeEndpoint8) (endpointCodes8_55.map decodeEndpoint8)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint8_54 hEndpoint8_55).trans
    (by decide +kernel)

private abbrev goalSpec8_3_38 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 8) 3))[38-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal8_3_38 : trunkGoalBranches (trunkCatalog.states 8) 3 38 = goalCodes8_3_38.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 8).context goalSpec8_3_38 = _
  exact (cachedBranches_eq (trunkCatalog.states 8).context goalSpec8_3_38
    endpointInput8_56 endpointInput8_53 (([] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes8_56.map decodeEndpoint8) (endpointCodes8_53.map decodeEndpoint8)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint8_56 hEndpoint8_53).trans
    (by decide +kernel)

private abbrev goalSpec8_3_39 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 8) 3))[39-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal8_3_39 : trunkGoalBranches (trunkCatalog.states 8) 3 39 = goalCodes8_3_39.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 8).context goalSpec8_3_39 = _
  exact (cachedBranches_eq (trunkCatalog.states 8).context goalSpec8_3_39
    endpointInput8_56 endpointInput8_23 (([] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes8_56.map decodeEndpoint8) (endpointCodes8_23.map decodeEndpoint8)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint8_56 hEndpoint8_23).trans
    (by decide +kernel)

private abbrev goalSpec8_3_40 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 8) 3))[40-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal8_3_40 : trunkGoalBranches (trunkCatalog.states 8) 3 40 = goalCodes8_3_40.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 8).context goalSpec8_3_40 = _
  exact (cachedBranches_eq (trunkCatalog.states 8).context goalSpec8_3_40
    endpointInput8_21 endpointInput8_57 (([] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes8_21.map decodeEndpoint8) (endpointCodes8_57.map decodeEndpoint8)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint8_21 hEndpoint8_57).trans
    (by decide +kernel)

private abbrev goalSpec8_3_42 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 8) 3))[42-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal8_3_42 : trunkGoalBranches (trunkCatalog.states 8) 3 42 = goalCodes8_3_42.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 8).context goalSpec8_3_42 = _
  exact (cachedBranches_eq (trunkCatalog.states 8).context goalSpec8_3_42
    endpointInput8_22 endpointInput8_23 (([] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes8_22.map decodeEndpoint8) (endpointCodes8_23.map decodeEndpoint8)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint8_22 hEndpoint8_23).trans
    (by decide +kernel)

private theorem hGoal8_4_0 : trunkGoalBranches (trunkCatalog.states 8) 4 0 = goalCodes8_4_0.map decodeGoalBranch := by
  exact hGoal8_2_0

private abbrev goalSpec8_4_2 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 8) 4))[2-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal8_4_2 : trunkGoalBranches (trunkCatalog.states 8) 4 2 = goalCodes8_4_2.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 8) 4 2 = trunkGoalBranches (trunkCatalog.states 8) 2 2 := by
      apply congrArg (trunkBranches (trunkCatalog.states 8).context)
      decide +kernel
    exact he.trans hGoal8_2_2
  | change trunkBranches (trunkCatalog.states 8).context goalSpec8_4_2 = _
    exact (cachedBranches_eq (trunkCatalog.states 8).context goalSpec8_4_2
      endpointInput8_4 endpointInput8_5 (([bc8] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
      (endpointCodes8_4.map decodeEndpoint8) (endpointCodes8_5.map decodeEndpoint8)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint8_4 hEndpoint8_5).trans
      (by decide +kernel)

private abbrev goalSpec8_4_5 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 8) 4))[5-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal8_4_5 : trunkGoalBranches (trunkCatalog.states 8) 4 5 = goalCodes8_4_5.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 8) 4 5 = trunkGoalBranches (trunkCatalog.states 8) 2 5 := by
      apply congrArg (trunkBranches (trunkCatalog.states 8).context)
      decide +kernel
    exact he.trans hGoal8_2_5
  | change trunkBranches (trunkCatalog.states 8).context goalSpec8_4_5 = _
    exact (cachedBranches_eq (trunkCatalog.states 8).context goalSpec8_4_5
      endpointInput8_6 endpointInput8_7 (([bc15] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
      (endpointCodes8_6.map decodeEndpoint8) (endpointCodes8_7.map decodeEndpoint8)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint8_6 hEndpoint8_7).trans
      (by decide +kernel)

private abbrev goalSpec8_4_7 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 8) 4))[7-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal8_4_7 : trunkGoalBranches (trunkCatalog.states 8) 4 7 = goalCodes8_4_7.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 8) 4 7 = trunkGoalBranches (trunkCatalog.states 8) 3 7 := by
      apply congrArg (trunkBranches (trunkCatalog.states 8).context)
      decide +kernel
    exact he.trans hGoal8_3_7
  | change trunkBranches (trunkCatalog.states 8).context goalSpec8_4_7 = _
    exact (cachedBranches_eq (trunkCatalog.states 8).context goalSpec8_4_7
      endpointInput8_34 endpointInput8_35 (([bc2] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
      (endpointCodes8_34.map decodeEndpoint8) (endpointCodes8_35.map decodeEndpoint8)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint8_34 hEndpoint8_35).trans
      (by decide +kernel)

private abbrev goalSpec8_4_9 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 8) 4))[9-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal8_4_9 : trunkGoalBranches (trunkCatalog.states 8) 4 9 = goalCodes8_4_9.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 8) 4 9 = trunkGoalBranches (trunkCatalog.states 8) 3 9 := by
      apply congrArg (trunkBranches (trunkCatalog.states 8).context)
      decide +kernel
    exact he.trans hGoal8_3_9
  | change trunkBranches (trunkCatalog.states 8).context goalSpec8_4_9 = _
    exact (cachedBranches_eq (trunkCatalog.states 8).context goalSpec8_4_9
      endpointInput8_36 endpointInput8_37 (([bc5] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
      (endpointCodes8_36.map decodeEndpoint8) (endpointCodes8_37.map decodeEndpoint8)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint8_36 hEndpoint8_37).trans
      (by decide +kernel)

private abbrev goalSpec8_4_12 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 8) 4))[12-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal8_4_12 : trunkGoalBranches (trunkCatalog.states 8) 4 12 = goalCodes8_4_12.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 8) 4 12 = trunkGoalBranches (trunkCatalog.states 8) 3 12 := by
      apply congrArg (trunkBranches (trunkCatalog.states 8).context)
      decide +kernel
    exact he.trans hGoal8_3_12
  | change trunkBranches (trunkCatalog.states 8).context goalSpec8_4_12 = _
    exact (cachedBranches_eq (trunkCatalog.states 8).context goalSpec8_4_12
      endpointInput8_38 endpointInput8_39 (([bc208] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
      (endpointCodes8_38.map decodeEndpoint8) (endpointCodes8_39.map decodeEndpoint8)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint8_38 hEndpoint8_39).trans
      (by decide +kernel)

private abbrev goalSpec8_4_14 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 8) 4))[14-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal8_4_14 : trunkGoalBranches (trunkCatalog.states 8) 4 14 = goalCodes8_4_14.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 8) 4 14 = trunkGoalBranches (trunkCatalog.states 8) 3 14 := by
      apply congrArg (trunkBranches (trunkCatalog.states 8).context)
      decide +kernel
    exact he.trans hGoal8_3_14
  | change trunkBranches (trunkCatalog.states 8).context goalSpec8_4_14 = _
    exact (cachedBranches_eq (trunkCatalog.states 8).context goalSpec8_4_14
      endpointInput8_40 endpointInput8_41 (([bc211] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
      (endpointCodes8_40.map decodeEndpoint8) (endpointCodes8_41.map decodeEndpoint8)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint8_40 hEndpoint8_41).trans
      (by decide +kernel)

private abbrev goalSpec8_4_17 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 8) 4))[17-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal8_4_17 : trunkGoalBranches (trunkCatalog.states 8) 4 17 = goalCodes8_4_17.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 8) 4 17 = trunkGoalBranches (trunkCatalog.states 8) 3 17 := by
      apply congrArg (trunkBranches (trunkCatalog.states 8).context)
      decide +kernel
    exact he.trans hGoal8_3_17
  | change trunkBranches (trunkCatalog.states 8).context goalSpec8_4_17 = _
    exact (cachedBranches_eq (trunkCatalog.states 8).context goalSpec8_4_17
      endpointInput8_42 endpointInput8_43 (([bc214] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
      (endpointCodes8_42.map decodeEndpoint8) (endpointCodes8_43.map decodeEndpoint8)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint8_42 hEndpoint8_43).trans
      (by decide +kernel)

private abbrev goalSpec8_4_19 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 8) 4))[19-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal8_4_19 : trunkGoalBranches (trunkCatalog.states 8) 4 19 = goalCodes8_4_19.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 8) 4 19 = trunkGoalBranches (trunkCatalog.states 8) 3 19 := by
      apply congrArg (trunkBranches (trunkCatalog.states 8).context)
      decide +kernel
    exact he.trans hGoal8_3_19
  | change trunkBranches (trunkCatalog.states 8).context goalSpec8_4_19 = _
    exact (cachedBranches_eq (trunkCatalog.states 8).context goalSpec8_4_19
      endpointInput8_44 endpointInput8_45 (([bc217] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
      (endpointCodes8_44.map decodeEndpoint8) (endpointCodes8_45.map decodeEndpoint8)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint8_44 hEndpoint8_45).trans
      (by decide +kernel)

private abbrev goalSpec8_4_22 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 8) 4))[22-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal8_4_22 : trunkGoalBranches (trunkCatalog.states 8) 4 22 = goalCodes8_4_22.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 8) 4 22 = trunkGoalBranches (trunkCatalog.states 8) 3 22 := by
      apply congrArg (trunkBranches (trunkCatalog.states 8).context)
      decide +kernel
    exact he.trans hGoal8_3_22
  | change trunkBranches (trunkCatalog.states 8).context goalSpec8_4_22 = _
    exact (cachedBranches_eq (trunkCatalog.states 8).context goalSpec8_4_22
      endpointInput8_46 endpointInput8_47 (([bc220] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
      (endpointCodes8_46.map decodeEndpoint8) (endpointCodes8_47.map decodeEndpoint8)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint8_46 hEndpoint8_47).trans
      (by decide +kernel)

private abbrev goalSpec8_4_24 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 8) 4))[24-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal8_4_24 : trunkGoalBranches (trunkCatalog.states 8) 4 24 = goalCodes8_4_24.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 8) 4 24 = trunkGoalBranches (trunkCatalog.states 8) 3 24 := by
      apply congrArg (trunkBranches (trunkCatalog.states 8).context)
      decide +kernel
    exact he.trans hGoal8_3_24
  | change trunkBranches (trunkCatalog.states 8).context goalSpec8_4_24 = _
    exact (cachedBranches_eq (trunkCatalog.states 8).context goalSpec8_4_24
      endpointInput8_48 endpointInput8_49 (([bc223] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
      (endpointCodes8_48.map decodeEndpoint8) (endpointCodes8_49.map decodeEndpoint8)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint8_48 hEndpoint8_49).trans
      (by decide +kernel)

private abbrev goalSpec8_4_27 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 8) 4))[27-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal8_4_27 : trunkGoalBranches (trunkCatalog.states 8) 4 27 = goalCodes8_4_27.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 8) 4 27 = trunkGoalBranches (trunkCatalog.states 8) 2 12 := by
      apply congrArg (trunkBranches (trunkCatalog.states 8).context)
      decide +kernel
    exact he.trans hGoal8_2_12
  | change trunkBranches (trunkCatalog.states 8).context goalSpec8_4_27 = _
    exact (cachedBranches_eq (trunkCatalog.states 8).context goalSpec8_4_27
      endpointInput8_17 endpointInput8_18 (([bc67] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
      (endpointCodes8_17.map decodeEndpoint8) (endpointCodes8_18.map decodeEndpoint8)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint8_17 hEndpoint8_18).trans
      (by decide +kernel)

private theorem hCut8_2 : (trunkPlanAt (trunkCatalog.states 8) 2).cuts = cutCodes8_2.map decodeThresholdBound := by decide +kernel

private theorem hCut8_3 : (trunkPlanAt (trunkCatalog.states 8) 3).cuts = cutCodes8_3.map decodeThresholdBound := by decide +kernel

private theorem hCut8_4 : (trunkPlanAt (trunkCatalog.states 8) 4).cuts = cutCodes8_4.map decodeThresholdBound := by decide +kernel

private def codedGoals8 (pi goal : ℕ) : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) :=
  if pi = 2 ∧ goal = 31 then goalCodes8_2_31 else
  if pi = 2 ∧ goal = 2 then goalCodes8_2_2 else
  if pi = 2 ∧ goal = 5 then goalCodes8_2_5 else
  if pi = 2 ∧ goal = 10 then goalCodes8_2_10 else
  if pi = 2 ∧ goal = 12 then goalCodes8_2_12 else
  if pi = 2 ∧ goal = 14 then goalCodes8_2_14 else
  if pi = 2 ∧ goal = 18 then goalCodes8_2_18 else
  if pi = 2 ∧ goal = 20 then goalCodes8_2_20 else
  if pi = 2 ∧ goal = 22 then goalCodes8_2_22 else
  if pi = 2 ∧ goal = 24 then goalCodes8_2_24 else
  if pi = 2 ∧ goal = 27 then goalCodes8_2_27 else
  if pi = 2 ∧ goal = 29 then goalCodes8_2_29 else
  if pi = 2 ∧ goal = 0 then goalCodes8_2_0 else
  if pi = 2 ∧ goal = 30 then goalCodes8_2_30 else
  if pi = 3 ∧ goal = 0 then goalCodes8_3_0 else
  if pi = 3 ∧ goal = 2 then goalCodes8_3_2 else
  if pi = 3 ∧ goal = 5 then goalCodes8_3_5 else
  if pi = 3 ∧ goal = 7 then goalCodes8_3_7 else
  if pi = 3 ∧ goal = 9 then goalCodes8_3_9 else
  if pi = 3 ∧ goal = 12 then goalCodes8_3_12 else
  if pi = 3 ∧ goal = 14 then goalCodes8_3_14 else
  if pi = 3 ∧ goal = 17 then goalCodes8_3_17 else
  if pi = 3 ∧ goal = 19 then goalCodes8_3_19 else
  if pi = 3 ∧ goal = 22 then goalCodes8_3_22 else
  if pi = 3 ∧ goal = 24 then goalCodes8_3_24 else
  if pi = 3 ∧ goal = 27 then goalCodes8_3_27 else
  if pi = 3 ∧ goal = 29 then goalCodes8_3_29 else
  if pi = 3 ∧ goal = 32 then goalCodes8_3_32 else
  if pi = 3 ∧ goal = 34 then goalCodes8_3_34 else
  if pi = 3 ∧ goal = 35 then goalCodes8_3_35 else
  if pi = 3 ∧ goal = 36 then goalCodes8_3_36 else
  if pi = 3 ∧ goal = 38 then goalCodes8_3_38 else
  if pi = 3 ∧ goal = 39 then goalCodes8_3_39 else
  if pi = 3 ∧ goal = 40 then goalCodes8_3_40 else
  if pi = 3 ∧ goal = 42 then goalCodes8_3_42 else
  if pi = 4 ∧ goal = 0 then goalCodes8_4_0 else
  if pi = 4 ∧ goal = 2 then goalCodes8_4_2 else
  if pi = 4 ∧ goal = 5 then goalCodes8_4_5 else
  if pi = 4 ∧ goal = 7 then goalCodes8_4_7 else
  if pi = 4 ∧ goal = 9 then goalCodes8_4_9 else
  if pi = 4 ∧ goal = 12 then goalCodes8_4_12 else
  if pi = 4 ∧ goal = 14 then goalCodes8_4_14 else
  if pi = 4 ∧ goal = 17 then goalCodes8_4_17 else
  if pi = 4 ∧ goal = 19 then goalCodes8_4_19 else
  if pi = 4 ∧ goal = 22 then goalCodes8_4_22 else
  if pi = 4 ∧ goal = 24 then goalCodes8_4_24 else
  if pi = 4 ∧ goal = 27 then goalCodes8_4_27 else
  []

private def codedKeys8 : List (ℕ × ℕ) := [(2, 31), (2, 2), (2, 5), (2, 10), (2, 12), (2, 14), (2, 18), (2, 20), (2, 22), (2, 24), (2, 27), (2, 29), (2, 0), (2, 30), (3, 0), (3, 2), (3, 5), (3, 7), (3, 9), (3, 12), (3, 14), (3, 17), (3, 19), (3, 22), (3, 24), (3, 27), (3, 29), (3, 32), (3, 34), (3, 35), (3, 36), (3, 38), (3, 39), (3, 40), (3, 42), (4, 0), (4, 2), (4, 5), (4, 7), (4, 9), (4, 12), (4, 14), (4, 17), (4, 19), (4, 22), (4, 24), (4, 27)]

private theorem hCodedGoals8 (pi goal : ℕ) (hm : (pi,goal) ∈ codedKeys8) : trunkGoalBranches (trunkCatalog.states 8) pi goal = (codedGoals8 pi goal).map decodeGoalBranch := by
  unfold codedGoals8
  by_cases h0 : pi = 2 ∧ goal = 31
  · rw [if_pos h0]
    rcases h0 with ⟨rfl,rfl⟩
    exact hGoal8_2_31
  rw [if_neg h0]
  by_cases h1 : pi = 2 ∧ goal = 2
  · rw [if_pos h1]
    rcases h1 with ⟨rfl,rfl⟩
    exact hGoal8_2_2
  rw [if_neg h1]
  by_cases h2 : pi = 2 ∧ goal = 5
  · rw [if_pos h2]
    rcases h2 with ⟨rfl,rfl⟩
    exact hGoal8_2_5
  rw [if_neg h2]
  by_cases h3 : pi = 2 ∧ goal = 10
  · rw [if_pos h3]
    rcases h3 with ⟨rfl,rfl⟩
    exact hGoal8_2_10
  rw [if_neg h3]
  by_cases h4 : pi = 2 ∧ goal = 12
  · rw [if_pos h4]
    rcases h4 with ⟨rfl,rfl⟩
    exact hGoal8_2_12
  rw [if_neg h4]
  by_cases h5 : pi = 2 ∧ goal = 14
  · rw [if_pos h5]
    rcases h5 with ⟨rfl,rfl⟩
    exact hGoal8_2_14
  rw [if_neg h5]
  by_cases h6 : pi = 2 ∧ goal = 18
  · rw [if_pos h6]
    rcases h6 with ⟨rfl,rfl⟩
    exact hGoal8_2_18
  rw [if_neg h6]
  by_cases h7 : pi = 2 ∧ goal = 20
  · rw [if_pos h7]
    rcases h7 with ⟨rfl,rfl⟩
    exact hGoal8_2_20
  rw [if_neg h7]
  by_cases h8 : pi = 2 ∧ goal = 22
  · rw [if_pos h8]
    rcases h8 with ⟨rfl,rfl⟩
    exact hGoal8_2_22
  rw [if_neg h8]
  by_cases h9 : pi = 2 ∧ goal = 24
  · rw [if_pos h9]
    rcases h9 with ⟨rfl,rfl⟩
    exact hGoal8_2_24
  rw [if_neg h9]
  by_cases h10 : pi = 2 ∧ goal = 27
  · rw [if_pos h10]
    rcases h10 with ⟨rfl,rfl⟩
    exact hGoal8_2_27
  rw [if_neg h10]
  by_cases h11 : pi = 2 ∧ goal = 29
  · rw [if_pos h11]
    rcases h11 with ⟨rfl,rfl⟩
    exact hGoal8_2_29
  rw [if_neg h11]
  by_cases h12 : pi = 2 ∧ goal = 0
  · rw [if_pos h12]
    rcases h12 with ⟨rfl,rfl⟩
    exact hGoal8_2_0
  rw [if_neg h12]
  by_cases h13 : pi = 2 ∧ goal = 30
  · rw [if_pos h13]
    rcases h13 with ⟨rfl,rfl⟩
    exact hGoal8_2_30
  rw [if_neg h13]
  by_cases h14 : pi = 3 ∧ goal = 0
  · rw [if_pos h14]
    rcases h14 with ⟨rfl,rfl⟩
    exact hGoal8_3_0
  rw [if_neg h14]
  by_cases h15 : pi = 3 ∧ goal = 2
  · rw [if_pos h15]
    rcases h15 with ⟨rfl,rfl⟩
    exact hGoal8_3_2
  rw [if_neg h15]
  by_cases h16 : pi = 3 ∧ goal = 5
  · rw [if_pos h16]
    rcases h16 with ⟨rfl,rfl⟩
    exact hGoal8_3_5
  rw [if_neg h16]
  by_cases h17 : pi = 3 ∧ goal = 7
  · rw [if_pos h17]
    rcases h17 with ⟨rfl,rfl⟩
    exact hGoal8_3_7
  rw [if_neg h17]
  by_cases h18 : pi = 3 ∧ goal = 9
  · rw [if_pos h18]
    rcases h18 with ⟨rfl,rfl⟩
    exact hGoal8_3_9
  rw [if_neg h18]
  by_cases h19 : pi = 3 ∧ goal = 12
  · rw [if_pos h19]
    rcases h19 with ⟨rfl,rfl⟩
    exact hGoal8_3_12
  rw [if_neg h19]
  by_cases h20 : pi = 3 ∧ goal = 14
  · rw [if_pos h20]
    rcases h20 with ⟨rfl,rfl⟩
    exact hGoal8_3_14
  rw [if_neg h20]
  by_cases h21 : pi = 3 ∧ goal = 17
  · rw [if_pos h21]
    rcases h21 with ⟨rfl,rfl⟩
    exact hGoal8_3_17
  rw [if_neg h21]
  by_cases h22 : pi = 3 ∧ goal = 19
  · rw [if_pos h22]
    rcases h22 with ⟨rfl,rfl⟩
    exact hGoal8_3_19
  rw [if_neg h22]
  by_cases h23 : pi = 3 ∧ goal = 22
  · rw [if_pos h23]
    rcases h23 with ⟨rfl,rfl⟩
    exact hGoal8_3_22
  rw [if_neg h23]
  by_cases h24 : pi = 3 ∧ goal = 24
  · rw [if_pos h24]
    rcases h24 with ⟨rfl,rfl⟩
    exact hGoal8_3_24
  rw [if_neg h24]
  by_cases h25 : pi = 3 ∧ goal = 27
  · rw [if_pos h25]
    rcases h25 with ⟨rfl,rfl⟩
    exact hGoal8_3_27
  rw [if_neg h25]
  by_cases h26 : pi = 3 ∧ goal = 29
  · rw [if_pos h26]
    rcases h26 with ⟨rfl,rfl⟩
    exact hGoal8_3_29
  rw [if_neg h26]
  by_cases h27 : pi = 3 ∧ goal = 32
  · rw [if_pos h27]
    rcases h27 with ⟨rfl,rfl⟩
    exact hGoal8_3_32
  rw [if_neg h27]
  by_cases h28 : pi = 3 ∧ goal = 34
  · rw [if_pos h28]
    rcases h28 with ⟨rfl,rfl⟩
    exact hGoal8_3_34
  rw [if_neg h28]
  by_cases h29 : pi = 3 ∧ goal = 35
  · rw [if_pos h29]
    rcases h29 with ⟨rfl,rfl⟩
    exact hGoal8_3_35
  rw [if_neg h29]
  by_cases h30 : pi = 3 ∧ goal = 36
  · rw [if_pos h30]
    rcases h30 with ⟨rfl,rfl⟩
    exact hGoal8_3_36
  rw [if_neg h30]
  by_cases h31 : pi = 3 ∧ goal = 38
  · rw [if_pos h31]
    rcases h31 with ⟨rfl,rfl⟩
    exact hGoal8_3_38
  rw [if_neg h31]
  by_cases h32 : pi = 3 ∧ goal = 39
  · rw [if_pos h32]
    rcases h32 with ⟨rfl,rfl⟩
    exact hGoal8_3_39
  rw [if_neg h32]
  by_cases h33 : pi = 3 ∧ goal = 40
  · rw [if_pos h33]
    rcases h33 with ⟨rfl,rfl⟩
    exact hGoal8_3_40
  rw [if_neg h33]
  by_cases h34 : pi = 3 ∧ goal = 42
  · rw [if_pos h34]
    rcases h34 with ⟨rfl,rfl⟩
    exact hGoal8_3_42
  rw [if_neg h34]
  by_cases h35 : pi = 4 ∧ goal = 0
  · rw [if_pos h35]
    rcases h35 with ⟨rfl,rfl⟩
    exact hGoal8_4_0
  rw [if_neg h35]
  by_cases h36 : pi = 4 ∧ goal = 2
  · rw [if_pos h36]
    rcases h36 with ⟨rfl,rfl⟩
    exact hGoal8_4_2
  rw [if_neg h36]
  by_cases h37 : pi = 4 ∧ goal = 5
  · rw [if_pos h37]
    rcases h37 with ⟨rfl,rfl⟩
    exact hGoal8_4_5
  rw [if_neg h37]
  by_cases h38 : pi = 4 ∧ goal = 7
  · rw [if_pos h38]
    rcases h38 with ⟨rfl,rfl⟩
    exact hGoal8_4_7
  rw [if_neg h38]
  by_cases h39 : pi = 4 ∧ goal = 9
  · rw [if_pos h39]
    rcases h39 with ⟨rfl,rfl⟩
    exact hGoal8_4_9
  rw [if_neg h39]
  by_cases h40 : pi = 4 ∧ goal = 12
  · rw [if_pos h40]
    rcases h40 with ⟨rfl,rfl⟩
    exact hGoal8_4_12
  rw [if_neg h40]
  by_cases h41 : pi = 4 ∧ goal = 14
  · rw [if_pos h41]
    rcases h41 with ⟨rfl,rfl⟩
    exact hGoal8_4_14
  rw [if_neg h41]
  by_cases h42 : pi = 4 ∧ goal = 17
  · rw [if_pos h42]
    rcases h42 with ⟨rfl,rfl⟩
    exact hGoal8_4_17
  rw [if_neg h42]
  by_cases h43 : pi = 4 ∧ goal = 19
  · rw [if_pos h43]
    rcases h43 with ⟨rfl,rfl⟩
    exact hGoal8_4_19
  rw [if_neg h43]
  by_cases h44 : pi = 4 ∧ goal = 22
  · rw [if_pos h44]
    rcases h44 with ⟨rfl,rfl⟩
    exact hGoal8_4_22
  rw [if_neg h44]
  by_cases h45 : pi = 4 ∧ goal = 24
  · rw [if_pos h45]
    rcases h45 with ⟨rfl,rfl⟩
    exact hGoal8_4_24
  rw [if_neg h45]
  by_cases h46 : pi = 4 ∧ goal = 27
  · rw [if_pos h46]
    rcases h46 with ⟨rfl,rfl⟩
    exact hGoal8_4_27
  rw [if_neg h46]
  simp_all only [codedKeys8,List.mem_cons,List.mem_nil_iff,or_false,Prod.mk.injEq]

private def codedCuts8 (pi : ℕ) : List (ℕ × Bool × Bool) :=
  if pi = 2 then cutCodes8_2 else
  if pi = 3 then cutCodes8_3 else
  if pi = 4 then cutCodes8_4 else
  []

private theorem hCodedCuts8 (pi goal : ℕ) (hm : (pi,goal) ∈ codedKeys8) : (trunkPlanAt (trunkCatalog.states 8) pi).cuts = (codedCuts8 pi).map decodeThresholdBound := by
  unfold codedCuts8
  by_cases h0 : pi = 2
  · rw [if_pos h0]
    subst pi
    exact hCut8_2
  rw [if_neg h0]
  by_cases h1 : pi = 3
  · rw [if_pos h1]
    subst pi
    exact hCut8_3
  rw [if_neg h1]
  by_cases h2 : pi = 4
  · rw [if_pos h2]
    subst pi
    exact hCut8_4
  rw [if_neg h2]
  simp_all only [codedKeys8,List.mem_cons,List.mem_nil_iff,or_false,Prod.mk.injEq,false_and]

private def codedValid8 (g : TrunkGroup) : Prop := (g.plan,g.goal) ∈ codedKeys8 ∧ codeGroupValid (trunkCatalog.states 8) codedParents8 250 codedCuts8 codedGoals8 g

private theorem codedValid8_sound (g : TrunkGroup) (h : codedValid8 g) : trunkGroupValidFast 8 g :=
  codeGroupValid_sound 8 codedParents8 250 codedCuts8 codedGoals8 g hCodedParents8 hCodedParentLength8 (hCodedCuts8 g.plan g.goal h.1) (hCodedGoals8 g.plan g.goal h.1) h.2



set_option Elab.async false
theorem batch_chunk_0 : ∀ j ∈ List.range 20, codedValid8 (trunkStateData08Part02.getD j ⟨0,[],0,[]⟩) := by
  unfold codedValid8 codeGroupValid
  decide +kernel

theorem batch_chunk_20 : ∀ j ∈ List.range' 20 20, codedValid8 (trunkStateData08Part02.getD j ⟨0,[],0,[]⟩) := by
  unfold codedValid8 codeGroupValid
  decide +kernel

theorem batch_chunk_40 : ∀ j ∈ List.range' 40 20, codedValid8 (trunkStateData08Part02.getD j ⟨0,[],0,[]⟩) := by
  unfold codedValid8 codeGroupValid
  decide +kernel

theorem batch_chunk_60 : ∀ j ∈ List.range' 60 20, codedValid8 (trunkStateData08Part02.getD j ⟨0,[],0,[]⟩) := by
  unfold codedValid8 codeGroupValid
  decide +kernel

theorem batch_chunk_80 : ∀ j ∈ List.range' 80 20, codedValid8 (trunkStateData08Part02.getD j ⟨0,[],0,[]⟩) := by
  unfold codedValid8 codeGroupValid
  decide +kernel

theorem batch_key (j : ℕ) (hj : j < 100) : codedValid8 (trunkStateData08Part02.getD j ⟨0,[],0,[]⟩) := by
  rcases lt_or_ge j 20 with h0 | h0
  · exact batch_chunk_0 j (List.mem_range.2 (by omega))
  rcases lt_or_ge j 40 with h1 | h1
  · exact batch_chunk_20 j (List.mem_range'.2 ⟨j - 20, by omega, by omega⟩)
  rcases lt_or_ge j 60 with h2 | h2
  · exact batch_chunk_40 j (List.mem_range'.2 ⟨j - 40, by omega, by omega⟩)
  rcases lt_or_ge j 80 with h3 | h3
  · exact batch_chunk_60 j (List.mem_range'.2 ⟨j - 60, by omega, by omega⟩)
  · exact batch_chunk_80 j (List.mem_range'.2 ⟨j - 80, by omega, by omega⟩)

theorem part_length_1 : trunkStateData08Part01.length = 100 := by decide +kernel

theorem part_length_2 : trunkStateData08Part02.length = 100 := by decide +kernel

theorem solution : trunkBindingBatch 8 100 200 := by
  intro i hlo hhi g hg
  change (trunkStateData08Part01 ++ trunkStateData08Part02 ++ trunkStateData08Part03)[i]? = some g at hg
  rw [List.getElem?_append_left (show i < (trunkStateData08Part01 ++ trunkStateData08Part02).length by simp only [List.length_append, part_length_1, part_length_2, Nat.reduceAdd]; omega)] at hg
  rw [List.getElem?_append_right (show (trunkStateData08Part01).length ≤ i by simp only [List.length_append, part_length_1, part_length_2, Nat.reduceAdd]; omega)] at hg
  simp only [List.length_append, part_length_1, part_length_2, Nat.reduceAdd] at hg
  have hgi := batch_key (i - 100) (by omega)
  have hgv : trunkStateData08Part02.getD (i - 100) ⟨0,[],0,[]⟩ = g := by
    try simp only [Nat.sub_zero]
    rw [List.getD_eq_getElem?_getD, hg]; rfl
  rw [hgv] at hgi
  exact Freiman.trunkFast_correctness.2 8 hPar8 g (codedValid8_sound g hgi)

#print axioms solution
