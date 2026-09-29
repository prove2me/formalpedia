-- Prove2me | solution 1 for Freiman.trunk_bindings_00_200_300
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:23:03.133438+00:00
-- url     : https://prove2.me/submissions/bd6e784c-a180-4c4f-baee-3239b8a4660a

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
private abbrev bc16 : ℕ × Bool × Bool := (18, false, false)
private abbrev bc17 : ℕ × Bool × Bool := (17, false, true)
private abbrev bc18 : ℕ × Bool × Bool := (17, true, false)
private abbrev bc19 : ℕ × Bool × Bool := (18, true, true)
private abbrev bc20 : ℕ × Bool × Bool := (20, true, true)
private abbrev bc21 : ℕ × Bool × Bool := (20, false, false)
private abbrev bc22 : ℕ × Bool × Bool := (6, false, false)
private abbrev bc23 : ℕ × Bool × Bool := (2, false, true)
private abbrev bc24 : ℕ × Bool × Bool := (2, true, false)
private abbrev bc25 : ℕ × Bool × Bool := (6, true, true)
private abbrev bc26 : ℕ × Bool × Bool := (13, true, true)
private abbrev bc27 : ℕ × Bool × Bool := (13, false, false)
private abbrev bc28 : ℕ × Bool × Bool := (33, false, true)
private abbrev bc29 : ℕ × Bool × Bool := (33, true, false)
private abbrev bc30 : ℕ × Bool × Bool := (45, true, true)
private abbrev bc31 : ℕ × Bool × Bool := (45, false, false)
private abbrev bc32 : ℕ × Bool × Bool := (32, false, false)
private abbrev bc33 : ℕ × Bool × Bool := (31, false, true)
private abbrev bc34 : ℕ × Bool × Bool := (31, true, false)
private abbrev bc35 : ℕ × Bool × Bool := (32, true, true)
private abbrev bc36 : ℕ × Bool × Bool := (37, true, true)
private abbrev bc37 : ℕ × Bool × Bool := (37, false, false)
private abbrev bc38 : ℕ × Bool × Bool := (50, false, true)
private abbrev bc39 : ℕ × Bool × Bool := (51, false, true)
private abbrev bc40 : ℕ × Bool × Bool := (51, true, false)
private abbrev bc41 : ℕ × Bool × Bool := (50, true, false)
private abbrev bc42 : ℕ × Bool × Bool := (64, true, true)
private abbrev bc43 : ℕ × Bool × Bool := (64, false, false)
private abbrev bc44 : ℕ × Bool × Bool := (18, false, true)
private abbrev bc45 : ℕ × Bool × Bool := (52, false, true)
private abbrev bc46 : ℕ × Bool × Bool := (52, true, false)
private abbrev bc47 : ℕ × Bool × Bool := (18, true, false)
private abbrev bc48 : ℕ × Bool × Bool := (56, true, true)
private abbrev bc49 : ℕ × Bool × Bool := (56, false, false)
private abbrev bc50 : ℕ × Bool × Bool := (89, false, true)
private abbrev bc51 : ℕ × Bool × Bool := (91, false, true)
private abbrev bc52 : ℕ × Bool × Bool := (91, true, false)
private abbrev bc53 : ℕ × Bool × Bool := (89, true, false)
private abbrev bc54 : ℕ × Bool × Bool := (102, true, true)
private abbrev bc55 : ℕ × Bool × Bool := (102, false, false)
private abbrev bc56 : ℕ × Bool × Bool := (30, false, true)
private abbrev bc57 : ℕ × Bool × Bool := (90, false, true)
private abbrev bc58 : ℕ × Bool × Bool := (90, true, false)
private abbrev bc59 : ℕ × Bool × Bool := (30, true, false)
private abbrev bc60 : ℕ × Bool × Bool := (95, true, true)
private abbrev bc61 : ℕ × Bool × Bool := (95, false, false)
private abbrev bc62 : ℕ × Bool × Bool := (8, false, false)
private abbrev bc63 : ℕ × Bool × Bool := (8, true, true)
private abbrev bc64 : ℕ × Bool × Bool := (183, false, false)
private abbrev bc65 : ℕ × Bool × Bool := (182, false, false)
private abbrev bc66 : ℕ × Bool × Bool := (179, false, true)
private abbrev bc67 : ℕ × Bool × Bool := (179, true, false)
private abbrev bc68 : ℕ × Bool × Bool := (182, true, true)
private abbrev bc69 : ℕ × Bool × Bool := (197, true, true)
private abbrev bc70 : ℕ × Bool × Bool := (197, false, false)
private abbrev bc71 : ℕ × Bool × Bool := (183, true, true)
private abbrev bc72 : ℕ × Bool × Bool := (181, false, false)
private abbrev bc73 : ℕ × Bool × Bool := (181, true, true)
private abbrev bc74 : ℕ × Bool × Bool := (184, false, false)
private abbrev bc75 : ℕ × Bool × Bool := (186, false, true)
private abbrev bc76 : ℕ × Bool × Bool := (186, true, false)
private abbrev bc77 : ℕ × Bool × Bool := (184, true, true)
private abbrev bc78 : ℕ × Bool × Bool := (189, true, true)
private abbrev bc79 : ℕ × Bool × Bool := (189, false, false)
private abbrev bc80 : ℕ × Bool × Bool := (206, true, false)
private abbrev bc81 : ℕ × Bool × Bool := (210, false, true)
private abbrev bc82 : ℕ × Bool × Bool := (210, true, false)
private abbrev bc83 : ℕ × Bool × Bool := (205, false, true)
private abbrev bc84 : ℕ × Bool × Bool := (205, true, false)
private abbrev bc85 : ℕ × Bool × Bool := (132, false, false)
private abbrev bc86 : ℕ × Bool × Bool := (133, false, true)
private abbrev bc87 : ℕ × Bool × Bool := (133, true, false)
private abbrev bc88 : ℕ × Bool × Bool := (132, true, true)
private abbrev bc89 : ℕ × Bool × Bool := (136, true, true)
private abbrev bc90 : ℕ × Bool × Bool := (136, false, false)
private abbrev bc91 : ℕ × Bool × Bool := (176, false, true)
private abbrev bc92 : ℕ × Bool × Bool := (233, false, false)
private abbrev bc93 : ℕ × Bool × Bool := (233, true, true)
private abbrev bc94 : ℕ × Bool × Bool := (234, false, false)
private abbrev bc95 : ℕ × Bool × Bool := (236, false, false)
private abbrev bc96 : ℕ × Bool × Bool := (236, true, true)
private abbrev bc97 : ℕ × Bool × Bool := (246, false, true)
private abbrev bc98 : ℕ × Bool × Bool := (246, true, false)
private abbrev bc99 : ℕ × Bool × Bool := (248, true, false)
private abbrev bc100 : ℕ × Bool × Bool := (251, false, true)
private abbrev bc101 : ℕ × Bool × Bool := (251, true, false)
private abbrev bc102 : ℕ × Bool × Bool := (260, false, false)
private abbrev bc103 : ℕ × Bool × Bool := (261, false, false)
private abbrev bc104 : ℕ × Bool × Bool := (261, true, true)
private abbrev bc105 : ℕ × Bool × Bool := (263, false, false)
private abbrev bc106 : ℕ × Bool × Bool := (263, true, true)
private abbrev bc107 : ℕ × Bool × Bool := (275, true, false)
private abbrev bc108 : ℕ × Bool × Bool := (279, false, true)
private abbrev bc109 : ℕ × Bool × Bool := (279, true, false)
private abbrev bc110 : ℕ × Bool × Bool := (274, false, true)
private abbrev bc111 : ℕ × Bool × Bool := (274, true, false)
private abbrev bc112 : ℕ × Bool × Bool := (297, false, false)
private abbrev bc113 : ℕ × Bool × Bool := (298, false, false)
private abbrev bc114 : ℕ × Bool × Bool := (69, false, true)
private abbrev bc115 : ℕ × Bool × Bool := (69, true, false)
private abbrev bc116 : ℕ × Bool × Bool := (298, true, true)
private abbrev bc117 : ℕ × Bool × Bool := (83, true, true)
private abbrev bc118 : ℕ × Bool × Bool := (83, false, false)
private abbrev bc119 : ℕ × Bool × Bool := (297, true, true)
private abbrev bc120 : ℕ × Bool × Bool := (299, false, false)
private abbrev bc121 : ℕ × Bool × Bool := (299, true, true)
private abbrev bc122 : ℕ × Bool × Bool := (301, false, false)
private abbrev bc123 : ℕ × Bool × Bool := (303, false, true)
private abbrev bc124 : ℕ × Bool × Bool := (303, true, false)
private abbrev bc125 : ℕ × Bool × Bool := (301, true, true)
private abbrev bc126 : ℕ × Bool × Bool := (307, true, true)
private abbrev bc127 : ℕ × Bool × Bool := (307, false, false)
private abbrev bc128 : ℕ × Bool × Bool := (319, false, true)
private abbrev bc129 : ℕ × Bool × Bool := (319, true, false)
private abbrev bc130 : ℕ × Bool × Bool := (331, false, true)
private abbrev bc131 : ℕ × Bool × Bool := (332, false, true)
private abbrev bc132 : ℕ × Bool × Bool := (332, true, false)
private abbrev bc133 : ℕ × Bool × Bool := (331, true, false)
private abbrev bc134 : ℕ × Bool × Bool := (337, true, true)
private abbrev bc135 : ℕ × Bool × Bool := (337, false, false)
private abbrev bc136 : ℕ × Bool × Bool := (320, false, true)
private abbrev bc137 : ℕ × Bool × Bool := (322, false, true)
private abbrev bc138 : ℕ × Bool × Bool := (321, false, true)
private abbrev bc139 : ℕ × Bool × Bool := (321, true, false)
private abbrev bc140 : ℕ × Bool × Bool := (322, true, false)
private abbrev bc141 : ℕ × Bool × Bool := (325, true, true)
private abbrev bc142 : ℕ × Bool × Bool := (325, false, false)
private abbrev bc143 : ℕ × Bool × Bool := (320, true, false)
private abbrev bc144 : ℕ × Bool × Bool := (344, false, false)
private abbrev bc145 : ℕ × Bool × Bool := (343, false, false)
private abbrev bc146 : ℕ × Bool × Bool := (113, false, true)
private abbrev bc147 : ℕ × Bool × Bool := (113, true, false)
private abbrev bc148 : ℕ × Bool × Bool := (343, true, true)
private abbrev bc149 : ℕ × Bool × Bool := (125, true, true)
private abbrev bc150 : ℕ × Bool × Bool := (125, false, false)
private abbrev bc151 : ℕ × Bool × Bool := (344, true, true)
private abbrev bc152 : ℕ × Bool × Bool := (346, false, false)
private abbrev bc153 : ℕ × Bool × Bool := (346, true, true)
private abbrev bc154 : ℕ × Bool × Bool := (347, false, false)
private abbrev bc155 : ℕ × Bool × Bool := (349, false, true)
private abbrev bc156 : ℕ × Bool × Bool := (349, true, false)
private abbrev bc157 : ℕ × Bool × Bool := (347, true, true)
private abbrev bc158 : ℕ × Bool × Bool := (352, true, true)
private abbrev bc159 : ℕ × Bool × Bool := (352, false, false)
private abbrev bc160 : ℕ × Bool × Bool := (365, true, false)
private abbrev bc161 : ℕ × Bool × Bool := (369, false, true)
private abbrev bc162 : ℕ × Bool × Bool := (369, true, false)
private abbrev bc163 : ℕ × Bool × Bool := (366, false, true)
private abbrev bc164 : ℕ × Bool × Bool := (366, true, false)
private abbrev bc165 : ℕ × Bool × Bool := (380, false, false)
private abbrev bc166 : ℕ × Bool × Bool := (379, false, false)
private abbrev bc167 : ℕ × Bool × Bool := (377, false, true)
private abbrev bc168 : ℕ × Bool × Bool := (377, true, false)
private abbrev bc169 : ℕ × Bool × Bool := (379, true, true)
private abbrev bc170 : ℕ × Bool × Bool := (395, true, true)
private abbrev bc171 : ℕ × Bool × Bool := (395, false, false)
private abbrev bc172 : ℕ × Bool × Bool := (380, true, true)
private abbrev bc173 : ℕ × Bool × Bool := (381, false, false)
private abbrev bc174 : ℕ × Bool × Bool := (381, true, true)
private abbrev bc175 : ℕ × Bool × Bool := (384, false, false)
private abbrev bc176 : ℕ × Bool × Bool := (383, false, true)
private abbrev bc177 : ℕ × Bool × Bool := (383, true, false)
private abbrev bc178 : ℕ × Bool × Bool := (384, true, true)
private abbrev bc179 : ℕ × Bool × Bool := (388, true, true)
private abbrev bc180 : ℕ × Bool × Bool := (388, false, false)
private abbrev bc181 : ℕ × Bool × Bool := (405, false, true)
private abbrev bc182 : ℕ × Bool × Bool := (405, true, false)
private abbrev bc183 : ℕ × Bool × Bool := (415, false, true)
private abbrev bc184 : ℕ × Bool × Bool := (414, false, true)
private abbrev bc185 : ℕ × Bool × Bool := (414, true, false)
private abbrev bc186 : ℕ × Bool × Bool := (415, true, false)
private abbrev bc187 : ℕ × Bool × Bool := (421, true, true)
private abbrev bc188 : ℕ × Bool × Bool := (421, false, false)
private abbrev bc189 : ℕ × Bool × Bool := (404, false, true)
private abbrev bc190 : ℕ × Bool × Bool := (406, false, true)
private abbrev bc191 : ℕ × Bool × Bool := (403, false, true)
private abbrev bc192 : ℕ × Bool × Bool := (403, true, false)
private abbrev bc193 : ℕ × Bool × Bool := (406, true, false)
private abbrev bc194 : ℕ × Bool × Bool := (409, true, true)
private abbrev bc195 : ℕ × Bool × Bool := (409, false, false)
private abbrev bc196 : ℕ × Bool × Bool := (404, true, false)
private abbrev bc197 : ℕ × Bool × Bool := (432, false, false)
private abbrev bc198 : ℕ × Bool × Bool := (430, false, false)
private abbrev bc199 : ℕ × Bool × Bool := (430, true, true)
private abbrev bc200 : ℕ × Bool × Bool := (428, false, false)
private abbrev bc201 : ℕ × Bool × Bool := (428, true, true)
private abbrev bc202 : ℕ × Bool × Bool := (443, false, true)
private abbrev bc203 : ℕ × Bool × Bool := (443, true, false)
private abbrev bc204 : ℕ × Bool × Bool := (455, false, true)
private abbrev bc205 : ℕ × Bool × Bool := (456, false, true)
private abbrev bc206 : ℕ × Bool × Bool := (456, true, false)
private abbrev bc207 : ℕ × Bool × Bool := (455, true, false)
private abbrev bc208 : ℕ × Bool × Bool := (461, true, true)
private abbrev bc209 : ℕ × Bool × Bool := (461, false, false)
private abbrev bc210 : ℕ × Bool × Bool := (446, false, true)
private abbrev bc211 : ℕ × Bool × Bool := (445, false, true)
private abbrev bc212 : ℕ × Bool × Bool := (444, false, true)
private abbrev bc213 : ℕ × Bool × Bool := (444, true, false)
private abbrev bc214 : ℕ × Bool × Bool := (445, true, false)
private abbrev bc215 : ℕ × Bool × Bool := (449, true, true)
private abbrev bc216 : ℕ × Bool × Bool := (449, false, false)
private abbrev bc217 : ℕ × Bool × Bool := (446, true, false)
private abbrev bc218 : ℕ × Bool × Bool := (156, false, false)
private abbrev bc219 : ℕ × Bool × Bool := (155, false, true)
private abbrev bc220 : ℕ × Bool × Bool := (155, true, false)
private abbrev bc221 : ℕ × Bool × Bool := (156, true, true)
private abbrev bc222 : ℕ × Bool × Bool := (162, true, true)
private abbrev bc223 : ℕ × Bool × Bool := (162, false, false)
private abbrev bc224 : ℕ × Bool × Bool := (89, false, false)
private abbrev bc225 : ℕ × Bool × Bool := (476, false, true)
private abbrev bc226 : ℕ × Bool × Bool := (476, true, false)
private abbrev bc227 : ℕ × Bool × Bool := (89, true, true)
private abbrev bc228 : ℕ × Bool × Bool := (479, true, true)
private abbrev bc229 : ℕ × Bool × Bool := (479, false, false)
private abbrev bc230 : ℕ × Bool × Bool := (431, false, false)
private abbrev bc231 : ℕ × Bool × Bool := (490, false, true)
private abbrev bc232 : ℕ × Bool × Bool := (490, true, false)
private abbrev bc233 : ℕ × Bool × Bool := (431, true, true)
private abbrev bc234 : ℕ × Bool × Bool := (497, true, true)
private abbrev bc235 : ℕ × Bool × Bool := (497, false, false)
private abbrev bc236 : ℕ × Bool × Bool := (1, true, false)
private abbrev bc237 : ℕ × Bool × Bool := (23, true, false)
private abbrev bc238 : ℕ × Bool × Bool := (27, true, false)
private abbrev bc239 : ℕ × Bool × Bool := (143, true, false)
private abbrev bc240 : ℕ × Bool × Bool := (145, true, false)
private abbrev bc241 : ℕ × Bool × Bool := (146, true, false)
private abbrev bc242 : ℕ × Bool × Bool := (148, true, false)
private abbrev bc243 : ℕ × Bool × Bool := (150, true, false)
private abbrev bc244 : ℕ × Bool × Bool := (151, true, false)
private abbrev bc245 : ℕ × Bool × Bool := (53, false, true)
private abbrev bc246 : ℕ × Bool × Bool := (88, false, true)
private abbrev bc247 : ℕ × Bool × Bool := (180, true, true)
private abbrev bc248 : ℕ × Bool × Bool := (204, false, true)
private abbrev bc249 : ℕ × Bool × Bool := (235, false, false)
private abbrev bc250 : ℕ × Bool × Bool := (232, true, true)
private abbrev bc251 : ℕ × Bool × Bool := (235, true, true)
private abbrev bc252 : ℕ × Bool × Bool := (245, false, true)
private abbrev bc253 : ℕ × Bool × Bool := (262, false, false)
private abbrev bc254 : ℕ × Bool × Bool := (264, true, true)
private abbrev bc255 : ℕ × Bool × Bool := (262, true, true)
private abbrev bc256 : ℕ × Bool × Bool := (273, false, true)
private abbrev bc257 : ℕ × Bool × Bool := (217, true, false)
private abbrev bc258 : ℕ × Bool × Bool := (34, true, true)
private abbrev bc259 : ℕ × Bool × Bool := (300, true, true)
private abbrev bc260 : ℕ × Bool × Bool := (318, false, true)
private abbrev bc261 : ℕ × Bool × Bool := (345, true, true)
private abbrev bc262 : ℕ × Bool × Bool := (364, false, true)
private abbrev bc263 : ℕ × Bool × Bool := (378, true, true)
private abbrev bc264 : ℕ × Bool × Bool := (402, false, true)
private abbrev bc265 : ℕ × Bool × Bool := (429, true, true)
private abbrev bc266 : ℕ × Bool × Bool := (441, false, true)
private abbrev bc267 : ℕ × Bool × Bool := (467, true, false)
private abbrev bc268 : ℕ × Bool × Bool := (153, true, false)
private abbrev bc269 : ℕ × Bool × Bool := (489, false, false)
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

private def codesA0 : List (List ℕ × Option (Option ℕ)) := [([112911326, 882722351, 131368818, 335455726], some (some 948335893)),
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
private def codesB0 : List (List ℕ × Option (Option ℕ)) := [([882722351, 112911326, 475598846, 413245293], some none),
 ([882722351, 112911326, 475598846, 250783862], some none),
 ([882722351, 112911326, 18672300, 970110223], some none),
 ([882722351, 112911326, 18672300, 961625388], some none),
 ([882722351, 728891584], some none),
 ([991976176, 466397207, 55717250, 112911326, 475598846, 413245293], some none),
 ([991976176, 466397207, 55717250, 112911326, 475598846, 250783862], some none),
 ([991976176, 466397207, 55717250, 112911326, 18672300, 970110223], some none),
 ([991976176, 466397207, 55717250, 112911326, 18672300, 961625388], some none),
 ([991976176, 466397207, 55717250, 728891584], some none),
 ([991976176, 466397207, 649614909, 112911326, 475598846, 413245293], some none),
 ([991976176, 466397207, 649614909, 112911326, 475598846, 250783862], some none),
 ([991976176, 466397207, 649614909, 112911326, 18672300, 970110223], some none),
 ([991976176, 466397207, 649614909, 112911326, 18672300, 961625388], some none),
 ([991976176, 466397207, 649614909, 728891584], some none),
 ([991976176, 827878947, 143171926, 112911326, 475598846, 413245293], some none),
 ([991976176, 827878947, 143171926, 112911326, 475598846, 250783862], some none),
 ([991976176, 827878947, 143171926, 112911326, 18672300, 970110223], some none),
 ([991976176, 827878947, 143171926, 112911326, 18672300, 961625388], some none),
 ([991976176, 827878947, 143171926, 728891584], some none),
 ([991976176, 827878947, 222803470, 112911326, 475598846, 413245293], some none),
 ([991976176, 827878947, 222803470, 112911326, 475598846, 250783862], some none),
 ([991976176, 827878947, 222803470, 112911326, 18672300, 970110223], some none),
 ([991976176, 827878947, 222803470, 112911326, 18672300, 961625388], some none),
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
private def endpointFields0 : Array CertField := #[⟨(4/13),(1/13),(0/1),(0/1)⟩,⟨(1/2),(1/6),(0/1),(0/1)⟩,⟨(52/73),(1/73),(0/1),(0/1)⟩,⟨(89/214),(1/214),(0/1),(0/1)⟩,⟨(9/13),(-1/13),(0/1),(0/1)⟩,⟨(2/1),(-1/1),(0/1),(0/1)⟩,⟨(15/37),(-1/37),(0/1),(0/1)⟩,⟨(125/214),(-1/214),(0/1),(0/1)⟩,⟨(66/179),(-1/537),(0/1),(0/1)⟩,⟨(22/37),(1/37),(0/1),(0/1)⟩,⟨(113/179),(1/537),(0/1),(0/1)⟩,⟨(17/22),(-1/22),(0/1),(0/1)⟩,⟨(101/143),(-1/429),(0/1),(0/1)⟩,⟨(35/94),(1/94),(0/1),(0/1)⟩,⟨(553/1429),(1/1429),(0/1),(0/1)⟩,⟨(10/23),(-1/69),(0/1),(0/1)⟩,⟨(517/1249),(-1/1249),(0/1),(0/1)⟩,⟨(16/59),(1/177),(0/1),(0/1)⟩,⟨(767/2749),(1/2749),(0/1),(0/1)⟩,⟨(43/142),(-1/142),(0/1),(0/1)⟩,⟨(731/2497),(-1/2497),(0/1),(0/1)⟩,⟨(5/22),(1/22),(0/1),(0/1)⟩,⟨(42/143),(1/429),(0/1),(0/1)⟩,⟨(271/1006),(-1/1006),(0/1),(0/1)⟩,⟨(469/1549),(1/1549),(0/1),(0/1)⟩,⟨(3289/10753),(1/10753),(0/1),(0/1)⟩,⟨(579/1894),(-1/1894),(0/1),(0/1)⟩,⟨(71/229),(-1/229),(0/1),(0/1)⟩,⟨(1413/4654),(-1/4654),(0/1),(0/1)⟩,⟨(9014/29557),(-1/29557),(0/1),(0/1)⟩,⟨(13/23),(1/69),(0/1),(0/1)⟩,⟨(732/1249),(1/1249),(0/1),(0/1)⟩,⟨(59/94),(-1/94),(0/1),(0/1)⟩]
private abbrev endpointInput0_0 : LowerPair × Bool × Bool := (([2], []), true, false)
private def endpointCodes0_0 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((0, 1), [bc0]),
 ((0, 1), [bc1, bc2, bc3]),
 ((0, 2), [bc1, bc2, bc4]),
 ((0, 1), [bc1, bc5, bc6]),
 ((3, 1), [bc1, bc5, bc7])]
private abbrev endpointInput0_1 : LowerPair × Bool × Bool := (([1], []), false, false)
private def endpointCodes0_1 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((4, 5), [bc8, bc9, bc10]),
 ((4, 6), [bc8, bc9, bc11]),
 ((4, 5), [bc8, bc12, bc13]),
 ((7, 5), [bc8, bc12, bc14]),
 ((4, 5), [bc15])]
private abbrev endpointInput0_2 : LowerPair × Bool × Bool := (([1], []), true, false)
private def endpointCodes0_2 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((1, 1), [bc8]),
 ((1, 1), [bc15, bc16, bc17]),
 ((1, 2), [bc15, bc16, bc18]),
 ((1, 1), [bc15, bc19, bc20]),
 ((2, 1), [bc15, bc19, bc21])]
private abbrev endpointInput0_3 : LowerPair × Bool × Bool := (([2], []), false, false)
private def endpointCodes0_3 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((6, 5), [bc0, bc22, bc23]),
 ((6, 6), [bc0, bc22, bc24]),
 ((6, 5), [bc0, bc25, bc26]),
 ((8, 5), [bc0, bc25, bc27]),
 ((6, 5), [bc1])]
private abbrev endpointInput0_4 : LowerPair × Bool × Bool := (([1, 1], []), true, false)
private def endpointCodes0_4 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((9, 1), [bc9, bc28]),
 ((9, 2), [bc9, bc29]),
 ((9, 1), [bc12, bc30]),
 ((10, 1), [bc12, bc31])]
private abbrev endpointInput0_5 : LowerPair × Bool × Bool := (([1, 2], []), false, false)
private def endpointCodes0_5 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((11, 5), [bc32, bc33]),
 ((11, 6), [bc32, bc34]),
 ((11, 5), [bc35, bc36]),
 ((12, 5), [bc35, bc37])]
private abbrev endpointInput0_6 : LowerPair × Bool × Bool := (([1], [2]), true, true)
private def endpointCodes0_6 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((1, 0), [bc38, bc39]),
 ((1, 3), [bc38, bc40]),
 ((1, 0), [bc41, bc42]),
 ((2, 0), [bc41, bc43])]
private abbrev endpointInput0_7 : LowerPair × Bool × Bool := (([1], [1]), false, true)
private def endpointCodes0_7 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((4, 4), [bc44, bc45]),
 ((4, 7), [bc44, bc46]),
 ((4, 4), [bc47, bc48]),
 ((7, 4), [bc47, bc49])]
private abbrev endpointInput0_10 : LowerPair × Bool × Bool := (([2], [2]), true, true)
private def endpointCodes0_10 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((0, 0), [bc50, bc51]),
 ((0, 3), [bc50, bc52]),
 ((0, 0), [bc53, bc54]),
 ((3, 0), [bc53, bc55])]
private abbrev endpointInput0_11 : LowerPair × Bool × Bool := (([2], [1]), false, true)
private def endpointCodes0_11 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((6, 4), [bc56, bc57]),
 ((6, 7), [bc56, bc58]),
 ((6, 4), [bc59, bc60]),
 ((8, 4), [bc59, bc61])]
private abbrev endpointInput0_17 : LowerPair × Bool × Bool := (([], []), true, false)
private def endpointCodes0_17 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((1, 1), [bc62, bc17]),
 ((1, 2), [bc62, bc18]),
 ((1, 1), [bc63, bc20]),
 ((2, 1), [bc63, bc21])]
private abbrev endpointInput0_18 : LowerPair × Bool × Bool := (([3, 1], [2]), true, false)
private def endpointCodes0_18 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((17, 0), [bc64, bc65, bc66]),
 ((17, 3), [bc64, bc65, bc67]),
 ((17, 0), [bc64, bc68, bc69]),
 ((18, 0), [bc64, bc68, bc70]),
 ((17, 0), [bc71])]
private abbrev endpointInput0_19 : LowerPair × Bool × Bool := (([3, 2], [2]), false, false)
private def endpointCodes0_19 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((19, 6), [bc72]),
 ((19, 6), [bc73, bc74, bc75]),
 ((19, 8), [bc73, bc74, bc76]),
 ((19, 6), [bc73, bc77, bc78]),
 ((20, 6), [bc73, bc77, bc79])]
private abbrev endpointInput0_20 : LowerPair × Bool × Bool := (([3], [2, 1]), true, true)
private def endpointCodes0_20 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((21, 13), [(206, false, true)]),
 ((21, 13), [bc80, bc81, (208, false, true)]),
 ((21, 14), [bc80, bc81, (208, true, false)]),
 ((21, 13), [bc80, bc82, (213, true, true)]),
 ((22, 13), [bc80, bc82, (213, false, false)])]
private abbrev endpointInput0_21 : LowerPair × Bool × Bool := (([3], [2, 2]), false, true)
private def endpointCodes0_21 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((23, 15), [bc83]), ((23, 15), [bc84])]
private abbrev endpointInput0_22 : LowerPair × Bool × Bool := (([3], [2]), true, false)
private def endpointCodes0_22 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((21, 0), [bc85, bc86]),
 ((21, 3), [bc85, bc87]),
 ((21, 0), [bc88, bc89]),
 ((22, 0), [bc88, bc90])]
private abbrev endpointInput0_23 : LowerPair × Bool × Bool := (([], []), false, false)
private def endpointCodes0_23 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((5, 5), [bc62, bc91]),
 ((5, 6), [bc62, (176, true, false)]),
 ((5, 5), [bc63, (228, true, true)]),
 ((6, 5), [bc63, (228, false, false)])]
private abbrev endpointInput0_24 : LowerPair × Bool × Bool := (([3], [2]), false, false)
private def endpointCodes0_24 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((23, 6), [])]
private abbrev endpointInput0_25 : LowerPair × Bool × Bool := (([3, 3, 2], [3, 3]), true, false)
private def endpointCodes0_25 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((24, 25), [bc92]), ((24, 25), [bc93])]
private abbrev endpointInput0_26 : LowerPair × Bool × Bool := (([3, 3, 1], [3, 3]), false, false)
private def endpointCodes0_26 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((26, 27), [bc94, bc95, (231, false, true)]),
 ((26, 28), [bc94, bc95, (231, true, false)]),
 ((26, 27), [bc94, bc96, (239, true, true)]),
 ((29, 27), [bc94, bc96, (239, false, false)]),
 ((26, 27), [(234, true, true)])]
private abbrev endpointInput0_27 : LowerPair × Bool × Bool := (([3, 3], [3, 3, 2]), true, true)
private def endpointCodes0_27 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((25, 24), [bc97]), ((25, 24), [bc98])]
private abbrev endpointInput0_28 : LowerPair × Bool × Bool := (([3, 3], [3, 3, 1]), false, true)
private def endpointCodes0_28 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((27, 26), [(248, false, true)]),
 ((27, 26), [bc99, bc100, (249, false, true)]),
 ((27, 29), [bc99, bc100, (249, true, false)]),
 ((27, 26), [bc99, bc101, (254, true, true)]),
 ((28, 26), [bc99, bc101, (254, false, false)])]
private abbrev endpointInput0_29 : LowerPair × Bool × Bool := (([3, 1], [3]), true, false)
private def endpointCodes0_29 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((17, 21), [bc102, bc103, (259, false, true)]),
 ((17, 22), [bc102, bc103, (259, true, false)]),
 ((17, 21), [bc102, bc104, (269, true, true)]),
 ((18, 21), [bc102, bc104, (269, false, false)]),
 ((17, 21), [(260, true, true)])]
private abbrev endpointInput0_30 : LowerPair × Bool × Bool := (([3, 2], [3]), false, false)
private def endpointCodes0_30 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((19, 23), [bc105]), ((19, 23), [bc106])]
private abbrev endpointInput0_31 : LowerPair × Bool × Bool := (([3], [3, 1]), true, true)
private def endpointCodes0_31 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((21, 17), [(275, false, true)]),
 ((21, 17), [bc107, bc108, (280, false, true)]),
 ((21, 18), [bc107, bc108, (280, true, false)]),
 ((21, 17), [bc107, bc109, (283, true, true)]),
 ((22, 17), [bc107, bc109, (283, false, false)])]
private abbrev endpointInput0_32 : LowerPair × Bool × Bool := (([3], [3, 2]), false, true)
private def endpointCodes0_32 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((23, 19), [bc110]), ((23, 19), [bc111])]
private abbrev endpointInput0_34 : LowerPair × Bool × Bool := (([3, 3], [3, 3]), true, false)
private def endpointCodes0_34 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((25, 25), [])]
private abbrev endpointInput0_35 : LowerPair × Bool × Bool := (([2, 1], [1]), true, false)
private def endpointCodes0_35 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((13, 1), [bc112, bc113, bc114]),
 ((13, 2), [bc112, bc113, bc115]),
 ((13, 1), [bc112, bc116, bc117]),
 ((14, 1), [bc112, bc116, bc118]),
 ((13, 1), [bc119])]
private abbrev endpointInput0_36 : LowerPair × Bool × Bool := (([2, 2], [1]), false, false)
private def endpointCodes0_36 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((15, 4), [bc120]),
 ((15, 4), [bc121, bc122, bc123]),
 ((15, 7), [bc121, bc122, bc124]),
 ((15, 4), [bc121, bc125, bc126]),
 ((16, 4), [bc121, bc125, bc127])]
private abbrev endpointInput0_37 : LowerPair × Bool × Bool := (([2], [1, 1]), true, true)
private def endpointCodes0_37 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((0, 9), [bc128]),
 ((0, 9), [bc129, bc130, bc131]),
 ((0, 10), [bc129, bc130, bc132]),
 ((0, 9), [bc129, bc133, bc134]),
 ((3, 9), [bc129, bc133, bc135])]
private abbrev endpointInput0_38 : LowerPair × Bool × Bool := (([2], [1, 2]), false, true)
private def endpointCodes0_38 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((6, 11), [bc136, bc137, bc138]),
 ((6, 12), [bc136, bc137, bc139]),
 ((6, 11), [bc136, bc140, bc141]),
 ((8, 11), [bc136, bc140, bc142]),
 ((6, 11), [bc143])]
private abbrev endpointInput0_39 : LowerPair × Bool × Bool := (([3, 1], [1]), true, false)
private def endpointCodes0_39 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((17, 1), [bc144, bc145, bc146]),
 ((17, 2), [bc144, bc145, bc147]),
 ((17, 1), [bc144, bc148, bc149]),
 ((18, 1), [bc144, bc148, bc150]),
 ((17, 1), [bc151])]
private abbrev endpointInput0_40 : LowerPair × Bool × Bool := (([3, 2], [1]), false, false)
private def endpointCodes0_40 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((19, 4), [bc152]),
 ((19, 4), [bc153, bc154, bc155]),
 ((19, 7), [bc153, bc154, bc156]),
 ((19, 4), [bc153, bc157, bc158]),
 ((20, 4), [bc153, bc157, bc159])]
private abbrev endpointInput0_41 : LowerPair × Bool × Bool := (([3], [1, 1]), true, true)
private def endpointCodes0_41 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((21, 9), [(365, false, true)]),
 ((21, 9), [bc160, bc161, (370, false, true)]),
 ((21, 10), [bc160, bc161, (370, true, false)]),
 ((21, 9), [bc160, bc162, (373, true, true)]),
 ((22, 9), [bc160, bc162, (373, false, false)])]
private abbrev endpointInput0_42 : LowerPair × Bool × Bool := (([3], [1, 2]), false, true)
private def endpointCodes0_42 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((23, 11), [bc163]), ((23, 11), [bc164])]
private abbrev endpointInput0_43 : LowerPair × Bool × Bool := (([2, 1], [2]), true, false)
private def endpointCodes0_43 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((13, 0), [bc165, bc166, bc167]),
 ((13, 3), [bc165, bc166, bc168]),
 ((13, 0), [bc165, bc169, bc170]),
 ((14, 0), [bc165, bc169, bc171]),
 ((13, 0), [bc172])]
private abbrev endpointInput0_44 : LowerPair × Bool × Bool := (([2, 2], [2]), false, false)
private def endpointCodes0_44 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((15, 6), [bc173]),
 ((15, 6), [bc174, bc175, bc176]),
 ((15, 8), [bc174, bc175, bc177]),
 ((15, 6), [bc174, bc178, bc179]),
 ((16, 6), [bc174, bc178, bc180])]
private abbrev endpointInput0_45 : LowerPair × Bool × Bool := (([2], [2, 1]), true, true)
private def endpointCodes0_45 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((0, 13), [bc181]),
 ((0, 13), [bc182, bc183, bc184]),
 ((0, 14), [bc182, bc183, bc185]),
 ((0, 13), [bc182, bc186, bc187]),
 ((3, 13), [bc182, bc186, bc188])]
private abbrev endpointInput0_46 : LowerPair × Bool × Bool := (([2], [2, 2]), false, true)
private def endpointCodes0_46 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((6, 15), [bc189, bc190, bc191]),
 ((6, 16), [bc189, bc190, bc192]),
 ((6, 15), [bc189, bc193, bc194]),
 ((8, 15), [bc189, bc193, bc195]),
 ((6, 15), [bc196])]
private abbrev endpointInput0_47 : LowerPair × Bool × Bool := (([2, 1], [3]), true, false)
private def endpointCodes0_47 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((13, 21), [bc197, bc198, (427, false, true)]),
 ((13, 22), [bc197, bc198, (427, true, false)]),
 ((13, 21), [bc197, bc199, (436, true, true)]),
 ((14, 21), [bc197, bc199, (436, false, false)]),
 ((13, 21), [(432, true, true)])]
private abbrev endpointInput0_48 : LowerPair × Bool × Bool := (([2, 2], [3]), false, false)
private def endpointCodes0_48 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((15, 23), [bc200]), ((15, 23), [bc201])]
private abbrev endpointInput0_49 : LowerPair × Bool × Bool := (([2], [3, 1]), true, true)
private def endpointCodes0_49 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((0, 17), [bc202]),
 ((0, 17), [bc203, bc204, bc205]),
 ((0, 18), [bc203, bc204, bc206]),
 ((0, 17), [bc203, bc207, bc208]),
 ((3, 17), [bc203, bc207, bc209])]
private abbrev endpointInput0_50 : LowerPair × Bool × Bool := (([2], [3, 2]), false, true)
private def endpointCodes0_50 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((6, 19), [bc210, bc211, bc212]),
 ((6, 20), [bc210, bc211, bc213]),
 ((6, 19), [bc210, bc214, bc215]),
 ((8, 19), [bc210, bc214, bc216]),
 ((6, 19), [bc217])]
private abbrev endpointInput0_51 : LowerPair × Bool × Bool := (([2], [1]), true, false)
private def endpointCodes0_51 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((0, 1), [bc2, bc3]),
 ((0, 2), [bc2, bc4]),
 ((0, 1), [bc5, bc6]),
 ((3, 1), [bc5, bc7])]
private abbrev endpointInput0_52 : LowerPair × Bool × Bool := (([3], [1]), true, false)
private def endpointCodes0_52 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((21, 1), [bc218, bc219]),
 ((21, 2), [bc218, bc220]),
 ((21, 1), [bc221, bc222]),
 ((22, 1), [bc221, bc223])]
private abbrev endpointInput0_53 : LowerPair × Bool × Bool := (([2], [1]), false, false)
private def endpointCodes0_53 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((6, 4), [bc2, bc57]),
 ((6, 7), [bc2, bc58]),
 ((6, 4), [bc5, bc60]),
 ((8, 4), [bc5, bc61])]
private abbrev endpointInput0_54 : LowerPair × Bool × Bool := (([2], [2]), false, false)
private def endpointCodes0_54 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((6, 6), [bc224, bc225]),
 ((6, 8), [bc224, bc226]),
 ((6, 6), [bc227, bc228]),
 ((8, 6), [bc227, bc229])]
private abbrev endpointInput0_55 : LowerPair × Bool × Bool := (([2], [2]), true, false)
private def endpointCodes0_55 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((0, 0), [bc224, bc51]),
 ((0, 3), [bc224, bc52]),
 ((0, 0), [bc227, bc54]),
 ((3, 0), [bc227, bc55])]
private abbrev endpointInput0_56 : LowerPair × Bool × Bool := (([3], [1]), false, false)
private def endpointCodes0_56 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((23, 4), [])]
private abbrev endpointInput0_57 : LowerPair × Bool × Bool := (([2], [3]), true, false)
private def endpointCodes0_57 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((0, 21), [bc230, bc231]),
 ((0, 22), [bc230, bc232]),
 ((0, 21), [bc233, bc234]),
 ((3, 21), [bc233, bc235])]
private abbrev endpointInput0_58 : LowerPair × Bool × Bool := (([2], [3]), false, false)
private def endpointCodes0_58 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((6, 23), [])]

private def decodeEndpoint0 (x : (ℕ × ℕ) × List (ℕ × Bool × Bool)) : LowerHistoryEndCase :=
  ((endpointFields0[x.1.1]?.getD ⟨0,0,0,0⟩,endpointFields0[x.1.2]?.getD ⟨0,0,0,0⟩),x.2.map decodeThresholdBound)

private theorem hEndpoint0_0 :
    trunkEndpointCases (trunkCatalog.states 0).context endpointInput0_0.1 endpointInput0_0.2.1 endpointInput0_0.2.2 = endpointCodes0_0.map decodeEndpoint0 := by decide +kernel

private theorem hEndpoint0_1 :
    trunkEndpointCases (trunkCatalog.states 0).context endpointInput0_1.1 endpointInput0_1.2.1 endpointInput0_1.2.2 = endpointCodes0_1.map decodeEndpoint0 := by decide +kernel

private theorem hEndpoint0_2 :
    trunkEndpointCases (trunkCatalog.states 0).context endpointInput0_2.1 endpointInput0_2.2.1 endpointInput0_2.2.2 = endpointCodes0_2.map decodeEndpoint0 := by decide +kernel

private theorem hEndpoint0_3 :
    trunkEndpointCases (trunkCatalog.states 0).context endpointInput0_3.1 endpointInput0_3.2.1 endpointInput0_3.2.2 = endpointCodes0_3.map decodeEndpoint0 := by decide +kernel

private theorem hEndpoint0_4 :
    trunkEndpointCases (trunkCatalog.states 0).context endpointInput0_4.1 endpointInput0_4.2.1 endpointInput0_4.2.2 = endpointCodes0_4.map decodeEndpoint0 := by decide +kernel

private theorem hEndpoint0_5 :
    trunkEndpointCases (trunkCatalog.states 0).context endpointInput0_5.1 endpointInput0_5.2.1 endpointInput0_5.2.2 = endpointCodes0_5.map decodeEndpoint0 := by decide +kernel

private theorem hEndpoint0_6 :
    trunkEndpointCases (trunkCatalog.states 0).context endpointInput0_6.1 endpointInput0_6.2.1 endpointInput0_6.2.2 = endpointCodes0_6.map decodeEndpoint0 := by decide +kernel

private theorem hEndpoint0_7 :
    trunkEndpointCases (trunkCatalog.states 0).context endpointInput0_7.1 endpointInput0_7.2.1 endpointInput0_7.2.2 = endpointCodes0_7.map decodeEndpoint0 := by decide +kernel

private theorem hEndpoint0_10 :
    trunkEndpointCases (trunkCatalog.states 0).context endpointInput0_10.1 endpointInput0_10.2.1 endpointInput0_10.2.2 = endpointCodes0_10.map decodeEndpoint0 := by decide +kernel

private theorem hEndpoint0_11 :
    trunkEndpointCases (trunkCatalog.states 0).context endpointInput0_11.1 endpointInput0_11.2.1 endpointInput0_11.2.2 = endpointCodes0_11.map decodeEndpoint0 := by decide +kernel

private theorem hEndpoint0_17 :
    trunkEndpointCases (trunkCatalog.states 0).context endpointInput0_17.1 endpointInput0_17.2.1 endpointInput0_17.2.2 = endpointCodes0_17.map decodeEndpoint0 := by decide +kernel

private theorem hEndpoint0_18 :
    trunkEndpointCases (trunkCatalog.states 0).context endpointInput0_18.1 endpointInput0_18.2.1 endpointInput0_18.2.2 = endpointCodes0_18.map decodeEndpoint0 := by decide +kernel

private theorem hEndpoint0_19 :
    trunkEndpointCases (trunkCatalog.states 0).context endpointInput0_19.1 endpointInput0_19.2.1 endpointInput0_19.2.2 = endpointCodes0_19.map decodeEndpoint0 := by decide +kernel

private theorem hEndpoint0_20 :
    trunkEndpointCases (trunkCatalog.states 0).context endpointInput0_20.1 endpointInput0_20.2.1 endpointInput0_20.2.2 = endpointCodes0_20.map decodeEndpoint0 := by decide +kernel

private theorem hEndpoint0_21 :
    trunkEndpointCases (trunkCatalog.states 0).context endpointInput0_21.1 endpointInput0_21.2.1 endpointInput0_21.2.2 = endpointCodes0_21.map decodeEndpoint0 := by decide +kernel

private theorem hEndpoint0_22 :
    trunkEndpointCases (trunkCatalog.states 0).context endpointInput0_22.1 endpointInput0_22.2.1 endpointInput0_22.2.2 = endpointCodes0_22.map decodeEndpoint0 := by decide +kernel

private theorem hEndpoint0_23 :
    trunkEndpointCases (trunkCatalog.states 0).context endpointInput0_23.1 endpointInput0_23.2.1 endpointInput0_23.2.2 = endpointCodes0_23.map decodeEndpoint0 := by decide +kernel

private theorem hEndpoint0_24 :
    trunkEndpointCases (trunkCatalog.states 0).context endpointInput0_24.1 endpointInput0_24.2.1 endpointInput0_24.2.2 = endpointCodes0_24.map decodeEndpoint0 := by decide +kernel

private theorem hEndpoint0_25 :
    trunkEndpointCases (trunkCatalog.states 0).context endpointInput0_25.1 endpointInput0_25.2.1 endpointInput0_25.2.2 = endpointCodes0_25.map decodeEndpoint0 := by decide +kernel

private theorem hEndpoint0_26 :
    trunkEndpointCases (trunkCatalog.states 0).context endpointInput0_26.1 endpointInput0_26.2.1 endpointInput0_26.2.2 = endpointCodes0_26.map decodeEndpoint0 := by decide +kernel

private theorem hEndpoint0_27 :
    trunkEndpointCases (trunkCatalog.states 0).context endpointInput0_27.1 endpointInput0_27.2.1 endpointInput0_27.2.2 = endpointCodes0_27.map decodeEndpoint0 := by decide +kernel

private theorem hEndpoint0_28 :
    trunkEndpointCases (trunkCatalog.states 0).context endpointInput0_28.1 endpointInput0_28.2.1 endpointInput0_28.2.2 = endpointCodes0_28.map decodeEndpoint0 := by decide +kernel

private theorem hEndpoint0_29 :
    trunkEndpointCases (trunkCatalog.states 0).context endpointInput0_29.1 endpointInput0_29.2.1 endpointInput0_29.2.2 = endpointCodes0_29.map decodeEndpoint0 := by decide +kernel

private theorem hEndpoint0_30 :
    trunkEndpointCases (trunkCatalog.states 0).context endpointInput0_30.1 endpointInput0_30.2.1 endpointInput0_30.2.2 = endpointCodes0_30.map decodeEndpoint0 := by decide +kernel

private theorem hEndpoint0_31 :
    trunkEndpointCases (trunkCatalog.states 0).context endpointInput0_31.1 endpointInput0_31.2.1 endpointInput0_31.2.2 = endpointCodes0_31.map decodeEndpoint0 := by decide +kernel

private theorem hEndpoint0_32 :
    trunkEndpointCases (trunkCatalog.states 0).context endpointInput0_32.1 endpointInput0_32.2.1 endpointInput0_32.2.2 = endpointCodes0_32.map decodeEndpoint0 := by decide +kernel

private theorem hEndpoint0_34 :
    trunkEndpointCases (trunkCatalog.states 0).context endpointInput0_34.1 endpointInput0_34.2.1 endpointInput0_34.2.2 = endpointCodes0_34.map decodeEndpoint0 := by decide +kernel

private theorem hEndpoint0_35 :
    trunkEndpointCases (trunkCatalog.states 0).context endpointInput0_35.1 endpointInput0_35.2.1 endpointInput0_35.2.2 = endpointCodes0_35.map decodeEndpoint0 := by decide +kernel

private theorem hEndpoint0_36 :
    trunkEndpointCases (trunkCatalog.states 0).context endpointInput0_36.1 endpointInput0_36.2.1 endpointInput0_36.2.2 = endpointCodes0_36.map decodeEndpoint0 := by decide +kernel

private theorem hEndpoint0_37 :
    trunkEndpointCases (trunkCatalog.states 0).context endpointInput0_37.1 endpointInput0_37.2.1 endpointInput0_37.2.2 = endpointCodes0_37.map decodeEndpoint0 := by decide +kernel

private theorem hEndpoint0_38 :
    trunkEndpointCases (trunkCatalog.states 0).context endpointInput0_38.1 endpointInput0_38.2.1 endpointInput0_38.2.2 = endpointCodes0_38.map decodeEndpoint0 := by decide +kernel

private theorem hEndpoint0_39 :
    trunkEndpointCases (trunkCatalog.states 0).context endpointInput0_39.1 endpointInput0_39.2.1 endpointInput0_39.2.2 = endpointCodes0_39.map decodeEndpoint0 := by decide +kernel

private theorem hEndpoint0_40 :
    trunkEndpointCases (trunkCatalog.states 0).context endpointInput0_40.1 endpointInput0_40.2.1 endpointInput0_40.2.2 = endpointCodes0_40.map decodeEndpoint0 := by decide +kernel

private theorem hEndpoint0_41 :
    trunkEndpointCases (trunkCatalog.states 0).context endpointInput0_41.1 endpointInput0_41.2.1 endpointInput0_41.2.2 = endpointCodes0_41.map decodeEndpoint0 := by decide +kernel

private theorem hEndpoint0_42 :
    trunkEndpointCases (trunkCatalog.states 0).context endpointInput0_42.1 endpointInput0_42.2.1 endpointInput0_42.2.2 = endpointCodes0_42.map decodeEndpoint0 := by decide +kernel

private theorem hEndpoint0_43 :
    trunkEndpointCases (trunkCatalog.states 0).context endpointInput0_43.1 endpointInput0_43.2.1 endpointInput0_43.2.2 = endpointCodes0_43.map decodeEndpoint0 := by decide +kernel

private theorem hEndpoint0_44 :
    trunkEndpointCases (trunkCatalog.states 0).context endpointInput0_44.1 endpointInput0_44.2.1 endpointInput0_44.2.2 = endpointCodes0_44.map decodeEndpoint0 := by decide +kernel

private theorem hEndpoint0_45 :
    trunkEndpointCases (trunkCatalog.states 0).context endpointInput0_45.1 endpointInput0_45.2.1 endpointInput0_45.2.2 = endpointCodes0_45.map decodeEndpoint0 := by decide +kernel

private theorem hEndpoint0_46 :
    trunkEndpointCases (trunkCatalog.states 0).context endpointInput0_46.1 endpointInput0_46.2.1 endpointInput0_46.2.2 = endpointCodes0_46.map decodeEndpoint0 := by decide +kernel

private theorem hEndpoint0_47 :
    trunkEndpointCases (trunkCatalog.states 0).context endpointInput0_47.1 endpointInput0_47.2.1 endpointInput0_47.2.2 = endpointCodes0_47.map decodeEndpoint0 := by decide +kernel

private theorem hEndpoint0_48 :
    trunkEndpointCases (trunkCatalog.states 0).context endpointInput0_48.1 endpointInput0_48.2.1 endpointInput0_48.2.2 = endpointCodes0_48.map decodeEndpoint0 := by decide +kernel

private theorem hEndpoint0_49 :
    trunkEndpointCases (trunkCatalog.states 0).context endpointInput0_49.1 endpointInput0_49.2.1 endpointInput0_49.2.2 = endpointCodes0_49.map decodeEndpoint0 := by decide +kernel

private theorem hEndpoint0_50 :
    trunkEndpointCases (trunkCatalog.states 0).context endpointInput0_50.1 endpointInput0_50.2.1 endpointInput0_50.2.2 = endpointCodes0_50.map decodeEndpoint0 := by decide +kernel

private theorem hEndpoint0_51 :
    trunkEndpointCases (trunkCatalog.states 0).context endpointInput0_51.1 endpointInput0_51.2.1 endpointInput0_51.2.2 = endpointCodes0_51.map decodeEndpoint0 := by decide +kernel

private theorem hEndpoint0_52 :
    trunkEndpointCases (trunkCatalog.states 0).context endpointInput0_52.1 endpointInput0_52.2.1 endpointInput0_52.2.2 = endpointCodes0_52.map decodeEndpoint0 := by decide +kernel

private theorem hEndpoint0_53 :
    trunkEndpointCases (trunkCatalog.states 0).context endpointInput0_53.1 endpointInput0_53.2.1 endpointInput0_53.2.2 = endpointCodes0_53.map decodeEndpoint0 := by decide +kernel

private theorem hEndpoint0_54 :
    trunkEndpointCases (trunkCatalog.states 0).context endpointInput0_54.1 endpointInput0_54.2.1 endpointInput0_54.2.2 = endpointCodes0_54.map decodeEndpoint0 := by decide +kernel

private theorem hEndpoint0_55 :
    trunkEndpointCases (trunkCatalog.states 0).context endpointInput0_55.1 endpointInput0_55.2.1 endpointInput0_55.2.2 = endpointCodes0_55.map decodeEndpoint0 := by decide +kernel

private theorem hEndpoint0_56 :
    trunkEndpointCases (trunkCatalog.states 0).context endpointInput0_56.1 endpointInput0_56.2.1 endpointInput0_56.2.2 = endpointCodes0_56.map decodeEndpoint0 := by decide +kernel

private theorem hEndpoint0_57 :
    trunkEndpointCases (trunkCatalog.states 0).context endpointInput0_57.1 endpointInput0_57.2.1 endpointInput0_57.2.2 = endpointCodes0_57.map decodeEndpoint0 := by decide +kernel

private theorem hEndpoint0_58 :
    trunkEndpointCases (trunkCatalog.states 0).context endpointInput0_58.1 endpointInput0_58.2.1 endpointInput0_58.2.2 = endpointCodes0_58.map decodeEndpoint0 := by decide +kernel

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

private def classValidIds : List ℕ := [94, 9, 4, 10, 28, 53, 149, 55, 21, 177, 60, 8, 64, 63, 30, 88, 97, 95, 98, 102, 103, 179, 182, 181, 180, 187, 191, 200, 204, 207, 211, 213, 214, 231, 236, 233, 232, 241, 245, 252, 254, 255, 258, 259, 261, 263, 264, 270, 273, 277, 281, 283, 284, 16, 15, 3, 147, 173, 148, 217, 220, 136, 137, 223, 294, 19, 20, 176, 2, 6, 14, 29, 17, 318, 323, 327, 329, 333, 337, 338, 113, 343, 346, 345, 350, 354, 127, 364, 365, 367, 371, 373, 374, 377, 379, 381, 378, 385, 390, 397, 402, 407, 411, 413, 417, 421, 422, 427, 430, 428, 429, 438, 441, 447, 451, 453, 457, 461, 462, 1, 140, 155, 156, 467, 469, 163, 153, 477, 479, 159, 482, 483, 481, 165, 484, 485, 486, 487, 488, 489, 491, 492, 493, 497, 442, 502, 503, 504, 505, 506, 507, 167, 18, 22, 226, 52, 57, 321, 296, 91, 476, 169, 295]
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
private def codeHN : ℕ × Bool × Bool := bc62
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
private def thresholdParentA0 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc0, bc8, bc9, bc10], some (some bc236)),
 ([bc0, bc8, bc9, bc11], some (some bc237)),
 ([bc0, bc8, bc12, bc13], some (some bc236)),
 ([bc0, bc8, bc12, bc14], some (some bc238)),
 ([bc0, bc15], some (some bc236)),
 ([bc1, bc2, bc3, bc8, bc9, bc10],
  some (some bc236)),
 ([bc1, bc2, bc3, bc8, bc9, bc11],
  some (some bc237)),
 ([bc1, bc2, bc3, bc8, bc12, bc13],
  some (some bc236)),
 ([bc1, bc2, bc3, bc8, bc12, bc14],
  some (some bc238)),
 ([bc1, bc2, bc3, bc15], some (some bc236)),
 ([bc1, bc2, bc4, bc8, bc9, bc10],
  some (some bc239)),
 ([bc1, bc2, bc4, bc8, bc9, bc11],
  some (some bc240)),
 ([bc1, bc2, bc4, bc8, bc12, bc13],
  some (some bc239)),
 ([bc1, bc2, bc4, bc8, bc12, bc14],
  some (some bc241)),
 ([bc1, bc2, bc4, bc15], some (some bc239)),
 ([bc1, bc5, bc6, bc8, bc9, bc10],
  some (some bc236)),
 ([bc1, bc5, bc6, bc8, bc9, bc11],
  some (some bc237)),
 ([bc1, bc5, bc6, bc8, bc12, bc13],
  some (some bc236)),
 ([bc1, bc5, bc6, bc8, bc12, bc14],
  some (some bc238)),
 ([bc1, bc5, bc6, bc15], some (some bc236)),
 ([bc1, bc5, bc7, bc8, bc9, bc10],
  some (some bc242)),
 ([bc1, bc5, bc7, bc8, bc9, bc11],
  some (some bc243)),
 ([bc1, bc5, bc7, bc8, bc12, bc13],
  some (some bc242)),
 ([bc1, bc5, bc7, bc8, bc12, bc14],
  some (some bc244)),
 ([bc1, bc5, bc7, bc15], some (some bc242))]
private def thresholdParentB0 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc8, bc0, bc22, bc23], some none),
 ([bc8, bc0, bc22, bc24], some none),
 ([bc8, bc0, bc25, bc26], some none),
 ([bc8, bc0, bc25, bc27], some none),
 ([bc8, bc1], some none),
 ([bc15, bc16, bc17, bc0, bc22, bc23],
  some none),
 ([bc15, bc16, bc17, bc0, bc22, bc24],
  some none),
 ([bc15, bc16, bc17, bc0, bc25, bc26],
  some none),
 ([bc15, bc16, bc17, bc0, bc25, bc27],
  some none),
 ([bc15, bc16, bc17, bc1], some none),
 ([bc15, bc16, bc18, bc0, bc22, bc23],
  some none),
 ([bc15, bc16, bc18, bc0, bc22, bc24],
  some none),
 ([bc15, bc16, bc18, bc0, bc25, bc26],
  some none),
 ([bc15, bc16, bc18, bc0, bc25, bc27],
  some none),
 ([bc15, bc16, bc18, bc1], some none),
 ([bc15, bc19, bc20, bc0, bc22, bc23],
  some none),
 ([bc15, bc19, bc20, bc0, bc22, bc24],
  some none),
 ([bc15, bc19, bc20, bc0, bc25, bc26],
  some none),
 ([bc15, bc19, bc20, bc0, bc25, bc27],
  some none),
 ([bc15, bc19, bc20, bc1], some none),
 ([bc15, bc19, bc21, bc0, bc22, bc23],
  some none),
 ([bc15, bc19, bc21, bc0, bc22, bc24],
  some none),
 ([bc15, bc19, bc21, bc0, bc25, bc26],
  some none),
 ([bc15, bc19, bc21, bc0, bc25, bc27],
  some none),
 ([bc15, bc19, bc21, bc1], some none)]

private def parentSourceA0 : Array (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := #[([bc0, bc8, bc9, bc10], some (some bc236)),
 ([bc0, bc8, bc9, bc11], some (some bc237)),
 ([bc0, bc8, bc12, bc13], some (some bc236)),
 ([bc0, bc8, bc12, bc14], some (some bc238)),
 ([bc0, bc15], some (some bc236)),
 ([bc1, bc2, bc3, bc8, bc9, bc10],
  some (some bc236)),
 ([bc1, bc2, bc3, bc8, bc9, bc11],
  some (some bc237)),
 ([bc1, bc2, bc3, bc8, bc12, bc13],
  some (some bc236)),
 ([bc1, bc2, bc3, bc8, bc12, bc14],
  some (some bc238)),
 ([bc1, bc2, bc3, bc15], some (some bc236)),
 ([bc1, bc2, bc4, bc8, bc9, bc10],
  some (some bc239)),
 ([bc1, bc2, bc4, bc8, bc9, bc11],
  some (some bc240)),
 ([bc1, bc2, bc4, bc8, bc12, bc13],
  some (some bc239)),
 ([bc1, bc2, bc4, bc8, bc12, bc14],
  some (some bc241)),
 ([bc1, bc2, bc4, bc15], some (some bc239)),
 ([bc1, bc5, bc6, bc8, bc9, bc10],
  some (some bc236)),
 ([bc1, bc5, bc6, bc8, bc9, bc11],
  some (some bc237)),
 ([bc1, bc5, bc6, bc8, bc12, bc13],
  some (some bc236)),
 ([bc1, bc5, bc6, bc8, bc12, bc14],
  some (some bc238)),
 ([bc1, bc5, bc6, bc15], some (some bc236)),
 ([bc1, bc5, bc7, bc8, bc9, bc10],
  some (some bc242)),
 ([bc1, bc5, bc7, bc8, bc9, bc11],
  some (some bc243)),
 ([bc1, bc5, bc7, bc8, bc12, bc13],
  some (some bc242)),
 ([bc1, bc5, bc7, bc8, bc12, bc14],
  some (some bc244)),
 ([bc1, bc5, bc7, bc15], some (some bc242))]

private def parentSourceB0 : Array (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := #[([bc8, bc0, bc22, bc23], some none),
 ([bc8, bc0, bc22, bc24], some none),
 ([bc8, bc0, bc25, bc26], some none),
 ([bc8, bc0, bc25, bc27], some none),
 ([bc8, bc1], some none),
 ([bc15, bc16, bc17, bc0, bc22, bc23],
  some none),
 ([bc15, bc16, bc17, bc0, bc22, bc24],
  some none),
 ([bc15, bc16, bc17, bc0, bc25, bc26],
  some none),
 ([bc15, bc16, bc17, bc0, bc25, bc27],
  some none),
 ([bc15, bc16, bc17, bc1], some none),
 ([bc15, bc16, bc18, bc0, bc22, bc23],
  some none),
 ([bc15, bc16, bc18, bc0, bc22, bc24],
  some none),
 ([bc15, bc16, bc18, bc0, bc25, bc26],
  some none),
 ([bc15, bc16, bc18, bc0, bc25, bc27],
  some none),
 ([bc15, bc16, bc18, bc1], some none),
 ([bc15, bc19, bc20, bc0, bc22, bc23],
  some none),
 ([bc15, bc19, bc20, bc0, bc22, bc24],
  some none),
 ([bc15, bc19, bc20, bc0, bc25, bc26],
  some none),
 ([bc15, bc19, bc20, bc0, bc25, bc27],
  some none),
 ([bc15, bc19, bc20, bc1], some none),
 ([bc15, bc19, bc21, bc0, bc22, bc23],
  some none),
 ([bc15, bc19, bc21, bc0, bc22, bc24],
  some none),
 ([bc15, bc19, bc21, bc0, bc25, bc26],
  some none),
 ([bc15, bc19, bc21, bc0, bc25, bc27],
  some none),
 ([bc15, bc19, bc21, bc1], some none)]

private def codedParents0 (i : ℕ) : List (ℕ × Bool × Bool) :=
  if i < 625 then
    (codeRawParent (parentSourceA0[i / 25]?.getD ([],none)) (parentSourceB0[i % 25]?.getD ([],none))).getD []
  else []

private theorem hThresholdParentA0 : trunkBranches (trunkCatalog.states 0).context ⟨([2],[]),true,([1],[]),false,false,[]⟩ = thresholdParentA0.map decodeGoalBranch := by
  have hi : ((⟨([2],[]),true,([1],[]),false,false,[]⟩ : Section14Spec).first,(⟨([2],[]),true,([1],[]),false,false,[]⟩ : Section14Spec).firstUpper,trunkSpecIncoming (⟨([2],[]),true,([1],[]),false,false,[]⟩ : Section14Spec)) = endpointInput0_0 := by decide +kernel
  have hj : ((⟨([2],[]),true,([1],[]),false,false,[]⟩ : Section14Spec).second,(⟨([2],[]),true,([1],[]),false,false,[]⟩ : Section14Spec).secondUpper,trunkSpecIncoming (⟨([2],[]),true,([1],[]),false,false,[]⟩ : Section14Spec)) = endpointInput0_1 := by decide +kernel
  have heL : trunkEndpointCases (trunkCatalog.states 0).context (⟨([2],[]),true,([1],[]),false,false,[]⟩ : Section14Spec).first (⟨([2],[]),true,([1],[]),false,false,[]⟩ : Section14Spec).firstUpper (trunkSpecIncoming (⟨([2],[]),true,([1],[]),false,false,[]⟩ : Section14Spec)) = endpointCodes0_0.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hi).trans hEndpoint0_0
  have heR : trunkEndpointCases (trunkCatalog.states 0).context (⟨([2],[]),true,([1],[]),false,false,[]⟩ : Section14Spec).second (⟨([2],[]),true,([1],[]),false,false,[]⟩ : Section14Spec).secondUpper (trunkSpecIncoming (⟨([2],[]),true,([1],[]),false,false,[]⟩ : Section14Spec)) = endpointCodes0_1.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hj).trans hEndpoint0_1
  unfold trunkBranches
  rw [heL,heR]
  decide +kernel
private theorem hThresholdParentB0 : trunkBranches (trunkCatalog.states 0).context ⟨([1],[]),true,([2],[]),false,false,[]⟩ = thresholdParentB0.map decodeGoalBranch := by
  have hi : ((⟨([1],[]),true,([2],[]),false,false,[]⟩ : Section14Spec).first,(⟨([1],[]),true,([2],[]),false,false,[]⟩ : Section14Spec).firstUpper,trunkSpecIncoming (⟨([1],[]),true,([2],[]),false,false,[]⟩ : Section14Spec)) = endpointInput0_2 := by decide +kernel
  have hj : ((⟨([1],[]),true,([2],[]),false,false,[]⟩ : Section14Spec).second,(⟨([1],[]),true,([2],[]),false,false,[]⟩ : Section14Spec).secondUpper,trunkSpecIncoming (⟨([1],[]),true,([2],[]),false,false,[]⟩ : Section14Spec)) = endpointInput0_3 := by decide +kernel
  have heL : trunkEndpointCases (trunkCatalog.states 0).context (⟨([1],[]),true,([2],[]),false,false,[]⟩ : Section14Spec).first (⟨([1],[]),true,([2],[]),false,false,[]⟩ : Section14Spec).firstUpper (trunkSpecIncoming (⟨([1],[]),true,([2],[]),false,false,[]⟩ : Section14Spec)) = endpointCodes0_2.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hi).trans hEndpoint0_2
  have heR : trunkEndpointCases (trunkCatalog.states 0).context (⟨([1],[]),true,([2],[]),false,false,[]⟩ : Section14Spec).second (⟨([1],[]),true,([2],[]),false,false,[]⟩ : Section14Spec).secondUpper (trunkSpecIncoming (⟨([1],[]),true,([2],[]),false,false,[]⟩ : Section14Spec)) = endpointCodes0_3.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hj).trans hEndpoint0_3
  unfold trunkBranches
  rw [heL,heR]
  decide +kernel
private theorem hCodedParentTable0 : (List.range 625).map codedParents0 = thresholdParentA0.flatMap (fun a => thresholdParentB0.filterMap (codeRawParent a)) := by decide +kernel
private theorem hCodedParentList0 : trunkRawParents (trunkCatalog.states 0).context = ((List.range 625).map codedParents0).map (List.map decodeThresholdBound) := by
  unfold trunkRawParents
  rw [hThresholdParentA0,hThresholdParentB0]
  change (thresholdParentA0.map decodeGoalBranch).flatMap (fun a => (thresholdParentB0.map decodeGoalBranch).filterMap (rawParent a)) = ((List.range 625).map codedParents0).map (List.map decodeThresholdBound)
  rw [←codeParents_map,←hCodedParentTable0]
private theorem hCodedParentLength0 : (trunkRawParents (trunkCatalog.states 0).context).length = 625 := by
  rw [hCodedParentList0]; simp only [List.length_map,List.length_range]
private theorem hCodedParents0 (i : ℕ) : (trunkRawParents (trunkCatalog.states 0).context)[i]?.getD [] = (codedParents0 i).map decodeThresholdBound := by
  rw [hCodedParentList0,List.getElem?_map,List.getElem?_map]
  by_cases hi : i < 625
  · rw [List.getElem?_range hi]; rfl
  · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hi)]
    simp only [Option.map_none,Option.getD_none,codedParents0,if_neg hi,List.map_nil]

private theorem hHN : proj lowerHistoryHN = 466397207 := by decide +kernel
private theorem hZero : proj lowerHistoryZero = 559802771 := by decide +kernel

private theorem hA0 : (trunkBranches (trunkCatalog.states 0).context ⟨([2],[]),true,([1],[]),false,false,[]⟩).map branchCode = codesA0 := by
  rw [hThresholdParentA0]
  decide +kernel
private theorem hB0 : (trunkBranches (trunkCatalog.states 0).context ⟨([1],[]),true,([2],[]),false,false,[]⟩).map branchCode = codesB0 := by
  rw [hThresholdParentB0]
  decide +kernel
private def fprints0 : List ℕ := [4325838231, 4163376800, 4425776615, 4417291780, 4165885676, 5373531657, 5211070226, 5473470041, 5464985206, 5213579102, 5967429316, 5804967885, 6067367700, 6058882865, 5807476761, 6288865280, 6126403849, 6388803664, 6380318829, 6128912725, 6368496824, 6206035393, 6468435208, 6459950373, 6208544269, 3714549947, 3552088516, 3814488331, 3806003496, 3554597392, 4762243373, 4599781942, 4862181757, 4853696922, 4602290818, 5356141032, 5193679601, 5456079416, 5447594581, 5196188477, 5677576996, 5515115565, 5777515380, 5769030545, 5517624441, 5757208540, 5594747109, 5857146924, 5848662089, 5597255985, 4499614243, 4337152812, 4599552627, 4591067792, 4339661688, 5547307669, 5384846238, 5647246053, 5638761218, 5387355114, 6141205328, 5978743897, 6241143712, 6232658877, 5981252773, 6462641292, 6300179861, 6562579676, 6554094841, 6302688737, 6542272836, 6379811405, 6642211220, 6633726385, 6382320281, 3695453821, 3532992390, 3795392205, 3786907370, 3535501266, 4743147247, 4580685816, 4843085631, 4834600796, 4583194692, 5337044906, 5174583475, 5436983290, 5428498455, 5177092351, 5658480870, 5496019439, 5758419254, 5749934419, 5498528315, 5738112414, 5575650983, 5838050798, 5829565963, 5578159859, 4850989863, 4688528432, 4950928247, 4942443412, 4691037308, 4023984762, 3861523331, 4123923146, 4115438311, 3864032207, 4617882421, 4455420990, 4717820805, 4709335970, 4457929866, 4939318385, 4776856954, 5039256769, 5030771934, 4779365830, 5018949929, 4856488498, 5118888313, 5110403478, 4858997374, 5763869542, 5601408111, 5863807926, 5855323091, 4762114077, 6811562968, 6649101537, 6911501352, 6903016517, 5809807503, 7405460627, 7242999196, 7505399011, 7496914176, 6403705162, 7726896591, 7564435160, 7826834975, 7818350140, 6725141126, 7806528135, 7644066704, 7906466519, 7897981684, 6804772670, 5152581258, 4990119827, 5252519642, 5244034807, 4150825793, 6200274684, 6037813253, 6300213068, 6291728233, 5198519219, 6794172343, 6631710912, 6894110727, 6885625892, 5792416878, 7115608307, 6953146876, 7215546691, 7207061856, 6113852842, 7195239851, 7032778420, 7295178235, 7286693400, 6193484386, 5937645554, 5775184123, 6037583938, 6029099103, 4935890089, 6985338980, 6822877549, 7085277364, 7076792529, 5983583515, 7579236639, 7416775208, 7679175023, 7670690188, 6577481174, 7900672603, 7738211172, 8000610987, 7992126152, 6898917138, 7980304147, 7817842716, 8080242531, 8071757696, 6978548682, 5133485132, 4971023701, 5233423516, 5224938681, 4131729667, 6181178558, 6018717127, 6281116942, 6272632107, 5179423093, 6775076217, 6612614786, 6875014601, 6866529766, 5773320752, 7096512181, 6934050750, 7196450565, 7187965730, 6094756716, 7176143725, 7013682294, 7276082109, 7267597274, 6174388260, 6289021174, 6126559743, 6388959558, 6380474723, 5287265709, 5462016073, 5299554642, 5561954457, 5553469622, 4460260608, 6055913732, 5893452301, 6155852116, 6147367281, 5054158267, 6377349696, 6214888265, 6477288080, 6468803245, 5375594231, 6456981240, 6294519809, 6556919624, 6548434789, 5455225775, 5452433595, 5289972164, 5552371979, 5543887144, 4450678130, 6500127021, 6337665590, 6600065405, 6591580570, 5498371556, 7094024680, 6931563249, 7193963064, 7185478229, 6092269215, 7415460644, 7252999213, 7515399028, 7506914193, 6413705179, 7495092188, 7332630757, 7595030572, 7586545737, 6493336723, 4889340785, 4726879354, 4989279169, 4980794334, 3887585320, 5937034211, 5774572780, 6036972595, 6028487760, 4935278746, 6530931870, 6368470439, 6630870254, 6622385419, 5529176405, 6852367834, 6689906403, 6952306218, 6943821383, 5850612369, 6931999378, 6769537947, 7031937762, 7023452927, 5930243913, 5626209607, 5463748176, 5726147991, 5717663156, 4624454142, 6673903033, 6511441602, 6773841417, 6765356582, 5672147568, 7267800692, 7105339261, 7367739076, 7359254241, 6266045227, 7589236656, 7426775225, 7689175040, 7680690205, 6587481191, 7668868200, 7506406769, 7768806584, 7760321749, 6667112735, 5586827744, 5424366313, 5686766128, 5678281293, 4585072279, 6634521170, 6472059739, 6734459554, 6725974719, 5632765705, 7228418829, 7065957398, 7328357213, 7319872378, 6226663364, 7549854793, 7387393362, 7649793177, 7641308342, 6548099328, 7629486337, 7467024906, 7729424721, 7720939886, 6627730872, 5977585227, 5815123796, 6077523611, 6069038776, 4975829762, 5150580126, 4988118695, 5250518510, 5242033675, 4148824661, 5744477785, 5582016354, 5844416169, 5835931334, 4742722320, 6065913749, 5903452318, 6165852133, 6157367298, 5064158284, 6145545293, 5983083862, 6245483677, 6236998842, 5143789828, 6413071998, 6250610567, 6513010382, 6504525547, 5411316533, 7460765424, 7298303993, 7560703808, 7552218973, 6459009959, 8054663083, 7892201652, 8154601467, 8146116632, 7052907618, 8376099047, 8213637616, 8476037431, 8467552596, 7374343582, 8455730591, 8293269160, 8555668975, 8547184140, 7453975126, 5801783714, 5639322283, 5901722098, 5893237263, 4800028249, 6849477140, 6687015709, 6949415524, 6940930689, 5847721675, 7443374799, 7280913368, 7543313183, 7534828348, 6441619334, 7764810763, 7602349332, 7864749147, 7856264312, 6763055298, 7844442307, 7681980876, 7944380691, 7935895856, 6842686842, 6586848010, 6424386579, 6686786394, 6678301559, 5585092545, 7634541436, 7472080005, 7734479820, 7725994985, 6632785971, 8228439095, 8065977664, 8328377479, 8319892644, 7226683630, 8549875059, 8387413628, 8649813443, 8641328608, 7548119594, 8629506603, 8467045172, 8729444987, 8720960152, 7627751138, 5782687588, 5620226157, 5882625972, 5874141137, 4780932123, 6830381014, 6667919583, 6930319398, 6921834563, 5828625549, 7424278673, 7261817242, 7524217057, 7515732222, 6422523208, 7745714637, 7583253206, 7845653021, 7837168186, 6743959172, 7825346181, 7662884750, 7925284565, 7916799730, 6823590716, 6938223630, 6775762199, 7038162014, 7029677179, 5936468165, 6111218529, 5948757098, 6211156913, 6202672078, 5109463064, 6705116188, 6542654757, 6805054572, 6796569737, 5703360723, 7026552152, 6864090721, 7126490536, 7118005701, 6024796687, 7106183696, 6943722265, 7206122080, 7197637245, 6104428231, 5250137420, 5087675989, 5350075804, 5341590969, 4248381955, 6297830846, 6135369415, 6397769230, 6389284395, 5296075381, 6891728505, 6729267074, 6991666889, 6983182054, 5889973040, 7213164469, 7050703038, 7313102853, 7304618018, 6211409004, 7292796013, 7130334582, 7392734397, 7384249562, 6291040548, 5206499587, 5044038156, 5306437971, 5297953136, 4204744122, 6254193013, 6091731582, 6354131397, 6345646562, 5252437548, 6848090672, 6685629241, 6948029056, 6939544221, 5846335207, 7169526636, 7007065205, 7269465020, 7260980185, 6167771171, 7249158180, 7086696749, 7349096564, 7340611729, 6247402715, 5423913432, 5261452001, 5523851816, 5515366981, 4422157967, 6471606858, 6309145427, 6571545242, 6563060407, 5469851393, 7065504517, 6903043086, 7165442901, 7156958066, 6063749052, 7386940481, 7224479050, 7486878865, 7478394030, 6385185016, 7466572025, 7304110594, 7566510409, 7558025574, 6464816560, 4979276577, 4816815146, 5079214961, 5070730126, 3977521112, 6026970003, 5864508572, 6126908387, 6118423552, 5025214538, 6620867662, 6458406231, 6720806046, 6712321211, 5619112197, 6942303626, 6779842195, 7042242010, 7033757175, 5940548161, 7021935170, 6859473739, 7121873554, 7113388719, 6020179705, 5775289052, 5612827621, 5875227436, 5866742601, 4773533587, 4948283951, 4785822520, 5048222335, 5039737500, 3946528486, 5542181610, 5379720179, 5642119994, 5633635159, 4540426145, 5863617574, 5701156143, 5963555958, 5955071123, 4861862109, 5943249118, 5780787687, 6043187502, 6034702667, 4941493653]
private theorem hprints0 : (trunkRawParents (trunkCatalog.states 0).context).map fingerprint = fprints0 := by
  have hm (L : List (List CertBound)) :
      L.map fingerprint = (L.map (List.map proj)).map (fun cs => cs.toFinset.sum id) := by
    rw [List.map_map]; rfl
  rw [hm,trunkCodes_map,hA0,hB0,hHN,hZero]
  decide +kernel
private theorem hPar0 : trunkParents (trunkCatalog.states 0).context = trunkRawParents (trunkCatalog.states 0).context := by
  apply Freiman.trunkFast_correctness.1
  apply parents_of_fingerprints
  rw [hprints0]
  apply (List.perm_insertionSort (fun a b : ℕ => a ≤ b) fprints0).nodup_iff.mp
  have hs : (List.insertionSort (fun a b : ℕ => a ≤ b) fprints0).IsChain (fun a b => a < b) := by
    decide +kernel
  exact (List.isChain_iff_pairwise.mp hs).imp (fun h => Nat.ne_of_lt h)


private def goalCodes0_2_0 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([], none)]
private def goalCodes0_2_5 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc15, bc38, bc39, bc44, bc45],
  some (some bc245)),
 ([bc15, bc38, bc39, bc44, bc46],
  some (some (55, false, true))),
 ([bc15, bc38, bc39, bc47, bc48],
  some (some bc245)),
 ([bc15, bc38, bc39, bc47, bc49],
  some (some (57, false, true))),
 ([bc15, bc38, bc40, bc44, bc45],
  some (some (59, false, true))),
 ([bc15, bc38, bc40, bc44, bc46],
  some (some (61, false, true))),
 ([bc15, bc38, bc40, bc47, bc48],
  some (some (59, false, true))),
 ([bc15, bc38, bc40, bc47, bc49],
  some (some (62, false, true))),
 ([bc15, bc41, bc42, bc44, bc45],
  some (some bc245)),
 ([bc15, bc41, bc42, bc44, bc46],
  some (some (55, false, true))),
 ([bc15, bc41, bc42, bc47, bc48],
  some (some bc245)),
 ([bc15, bc41, bc42, bc47, bc49],
  some (some (57, false, true))),
 ([bc15, bc41, bc43, bc44, bc45],
  some (some (65, false, true))),
 ([bc15, bc41, bc43, bc44, bc46],
  some (some (67, false, true))),
 ([bc15, bc41, bc43, bc47, bc48],
  some (some (65, false, true))),
 ([bc15, bc41, bc43, bc47, bc49],
  some (some (68, false, true)))]
private def goalCodes0_2_10 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc1, bc50, bc51, bc56, bc57],
  some (some bc246)),
 ([bc1, bc50, bc51, bc56, bc58],
  some (some (92, false, true))),
 ([bc1, bc50, bc51, bc59, bc60],
  some (some bc246)),
 ([bc1, bc50, bc51, bc59, bc61],
  some (some (97, false, true))),
 ([bc1, bc50, bc52, bc56, bc57],
  some (some (99, false, true))),
 ([bc1, bc50, bc52, bc56, bc58],
  some (some (100, false, true))),
 ([bc1, bc50, bc52, bc59, bc60],
  some (some (99, false, true))),
 ([bc1, bc50, bc52, bc59, bc61],
  some (some (101, false, true))),
 ([bc1, bc53, bc54, bc56, bc57],
  some (some bc246)),
 ([bc1, bc53, bc54, bc56, bc58],
  some (some (92, false, true))),
 ([bc1, bc53, bc54, bc59, bc60],
  some (some bc246)),
 ([bc1, bc53, bc54, bc59, bc61],
  some (some (97, false, true))),
 ([bc1, bc53, bc55, bc56, bc57],
  some (some (104, false, true))),
 ([bc1, bc53, bc55, bc56, bc58],
  some (some (106, false, true))),
 ([bc1, bc53, bc55, bc59, bc60],
  some (some (104, false, true))),
 ([bc1, bc53, bc55, bc59, bc61],
  some (some (107, false, true)))]
private def goalCodes0_2_12 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc85, bc64, bc65, bc66, bc72],
  some (some bc247)),
 ([bc85,
   bc64,
   bc65,
   bc66,
   bc73,
   bc74,
   bc75],
  some (some bc247)),
 ([bc85,
   bc64,
   bc65,
   bc66,
   bc73,
   bc74,
   bc76],
  some (some (187, true, true))),
 ([bc85,
   bc64,
   bc65,
   bc66,
   bc73,
   bc77,
   bc78],
  some (some bc247)),
 ([bc85,
   bc64,
   bc65,
   bc66,
   bc73,
   bc77,
   bc79],
  some (some (191, true, true))),
 ([bc85, bc64, bc65, bc67, bc72],
  some (some (194, true, true))),
 ([bc85,
   bc64,
   bc65,
   bc67,
   bc73,
   bc74,
   bc75],
  some (some (194, true, true))),
 ([bc85,
   bc64,
   bc65,
   bc67,
   bc73,
   bc74,
   bc76],
  some (some (195, true, true))),
 ([bc85,
   bc64,
   bc65,
   bc67,
   bc73,
   bc77,
   bc78],
  some (some (194, true, true))),
 ([bc85,
   bc64,
   bc65,
   bc67,
   bc73,
   bc77,
   bc79],
  some (some (196, true, true))),
 ([bc85, bc64, bc68, bc69, bc72],
  some (some bc247)),
 ([bc85,
   bc64,
   bc68,
   bc69,
   bc73,
   bc74,
   bc75],
  some (some bc247)),
 ([bc85,
   bc64,
   bc68,
   bc69,
   bc73,
   bc74,
   bc76],
  some (some (187, true, true))),
 ([bc85,
   bc64,
   bc68,
   bc69,
   bc73,
   bc77,
   bc78],
  some (some bc247)),
 ([bc85,
   bc64,
   bc68,
   bc69,
   bc73,
   bc77,
   bc79],
  some (some (191, true, true))),
 ([bc85, bc64, bc68, bc70, bc72],
  some (some (199, true, true))),
 ([bc85,
   bc64,
   bc68,
   bc70,
   bc73,
   bc74,
   bc75],
  some (some (199, true, true))),
 ([bc85,
   bc64,
   bc68,
   bc70,
   bc73,
   bc74,
   bc76],
  some (some (201, true, true))),
 ([bc85,
   bc64,
   bc68,
   bc70,
   bc73,
   bc77,
   bc78],
  some (some (199, true, true))),
 ([bc85,
   bc64,
   bc68,
   bc70,
   bc73,
   bc77,
   bc79],
  some (some (202, true, true))),
 ([bc85, bc71, bc72], some (some bc247)),
 ([bc85, bc71, bc73, bc74, bc75],
  some (some bc247)),
 ([bc85, bc71, bc73, bc74, bc76],
  some (some (187, true, true))),
 ([bc85, bc71, bc73, bc77, bc78],
  some (some bc247)),
 ([bc85, bc71, bc73, bc77, bc79],
  some (some (191, true, true)))]
private def goalCodes0_2_14 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc88, (206, false, true), bc83], some (some bc248)),
 ([bc88, (206, false, true), bc84], some (some bc248)),
 ([bc88, bc80, bc81, (208, false, true), bc83],
  some (some bc248)),
 ([bc88, bc80, bc81, (208, false, true), bc84],
  some (some bc248)),
 ([bc88, bc80, bc81, (208, true, false), bc83],
  some (some (212, false, true))),
 ([bc88, bc80, bc81, (208, true, false), bc84],
  some (some (212, false, true))),
 ([bc88, bc80, bc82, (213, true, true), bc83],
  some (some bc248)),
 ([bc88, bc80, bc82, (213, true, true), bc84],
  some (some bc248)),
 ([bc88, bc80, bc82, (213, false, false), bc83],
  some (some (215, false, true))),
 ([bc88, bc80, bc82, (213, false, false), bc84],
  some (some (215, false, true)))]
private def goalCodes0_2_18 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc249, bc92, bc94, bc95, (231, false, true)],
  some (some bc250)),
 ([bc249, bc92, bc94, bc95, (231, true, false)],
  some (some (238, true, true))),
 ([bc249, bc92, bc94, bc96, (239, true, true)],
  some (some bc250)),
 ([bc249, bc92, bc94, bc96, (239, false, false)],
  some (some (242, true, true))),
 ([bc249, bc92, (234, true, true)], some (some bc250)),
 ([bc249, bc93, bc94, bc95, (231, false, true)],
  some (some bc250)),
 ([bc249, bc93, bc94, bc95, (231, true, false)],
  some (some (238, true, true))),
 ([bc249, bc93, bc94, bc96, (239, true, true)],
  some (some bc250)),
 ([bc249, bc93, bc94, bc96, (239, false, false)],
  some (some (242, true, true))),
 ([bc249, bc93, (234, true, true)], some (some bc250))]
private def goalCodes0_2_20 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc251, bc97, (248, false, true)], some (some bc252)),
 ([bc251, bc97, bc99, bc100, (249, false, true)],
  some (some bc252)),
 ([bc251, bc97, bc99, bc100, (249, true, false)],
  some (some (253, false, true))),
 ([bc251, bc97, bc99, bc101, (254, true, true)],
  some (some bc252)),
 ([bc251, bc97, bc99, bc101, (254, false, false)],
  some (some (257, false, true))),
 ([bc251, bc98, (248, false, true)], some (some bc252)),
 ([bc251, bc98, bc99, bc100, (249, false, true)],
  some (some bc252)),
 ([bc251, bc98, bc99, bc100, (249, true, false)],
  some (some (253, false, true))),
 ([bc251, bc98, bc99, bc101, (254, true, true)],
  some (some bc252)),
 ([bc251, bc98, bc99, bc101, (254, false, false)],
  some (some (257, false, true)))]
private def goalCodes0_2_22 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc253, bc102, bc103, (259, false, true), bc105],
  some (some bc254)),
 ([bc253, bc102, bc103, (259, false, true), bc106],
  some (some bc254)),
 ([bc253, bc102, bc103, (259, true, false), bc105],
  some (some (266, true, true))),
 ([bc253, bc102, bc103, (259, true, false), bc106],
  some (some (266, true, true))),
 ([bc253, bc102, bc104, (269, true, true), bc105],
  some (some bc254)),
 ([bc253, bc102, bc104, (269, true, true), bc106],
  some (some bc254)),
 ([bc253, bc102, bc104, (269, false, false), bc105],
  some (some (271, true, true))),
 ([bc253, bc102, bc104, (269, false, false), bc106],
  some (some (271, true, true))),
 ([bc253, (260, true, true), bc105], some (some bc254)),
 ([bc253, (260, true, true), bc106], some (some bc254))]
private def goalCodes0_2_24 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc255, (275, false, true), bc110], some (some bc256)),
 ([bc255, (275, false, true), bc111], some (some bc256)),
 ([bc255, bc107, bc108, (280, false, true), bc110],
  some (some bc256)),
 ([bc255, bc107, bc108, (280, false, true), bc111],
  some (some bc256)),
 ([bc255, bc107, bc108, (280, true, false), bc110],
  some (some (282, false, true))),
 ([bc255, bc107, bc108, (280, true, false), bc111],
  some (some (282, false, true))),
 ([bc255, bc107, bc109, (283, true, true), bc110],
  some (some bc256)),
 ([bc255, bc107, bc109, (283, true, true), bc111],
  some (some bc256)),
 ([bc255, bc107, bc109, (283, false, false), bc110],
  some (some (285, false, true))),
 ([bc255, bc107, bc109, (283, false, false), bc111],
  some (some (285, false, true)))]
private def goalCodes0_2_27 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc0, bc8, bc9, bc10], some (some bc236)),
 ([bc0, bc8, bc9, bc11], some (some bc237)),
 ([bc0, bc8, bc12, bc13], some (some bc236)),
 ([bc0, bc8, bc12, bc14], some (some bc238)),
 ([bc0, bc15], some (some bc236)),
 ([bc1, bc2, bc3, bc8, bc9, bc10],
  some (some bc236)),
 ([bc1, bc2, bc3, bc8, bc9, bc11],
  some (some bc237)),
 ([bc1, bc2, bc3, bc8, bc12, bc13],
  some (some bc236)),
 ([bc1, bc2, bc3, bc8, bc12, bc14],
  some (some bc238)),
 ([bc1, bc2, bc3, bc15], some (some bc236)),
 ([bc1, bc2, bc4, bc8, bc9, bc10],
  some (some bc239)),
 ([bc1, bc2, bc4, bc8, bc9, bc11],
  some (some bc240)),
 ([bc1, bc2, bc4, bc8, bc12, bc13],
  some (some bc239)),
 ([bc1, bc2, bc4, bc8, bc12, bc14],
  some (some bc241)),
 ([bc1, bc2, bc4, bc15], some (some bc239)),
 ([bc1, bc5, bc6, bc8, bc9, bc10],
  some (some bc236)),
 ([bc1, bc5, bc6, bc8, bc9, bc11],
  some (some bc237)),
 ([bc1, bc5, bc6, bc8, bc12, bc13],
  some (some bc236)),
 ([bc1, bc5, bc6, bc8, bc12, bc14],
  some (some bc238)),
 ([bc1, bc5, bc6, bc15], some (some bc236)),
 ([bc1, bc5, bc7, bc8, bc9, bc10],
  some (some bc242)),
 ([bc1, bc5, bc7, bc8, bc9, bc11],
  some (some bc243)),
 ([bc1, bc5, bc7, bc8, bc12, bc13],
  some (some bc242)),
 ([bc1, bc5, bc7, bc8, bc12, bc14],
  some (some bc244)),
 ([bc1, bc5, bc7, bc15], some (some bc242))]
private def goalCodes0_2_29 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc85, bc86, bc0, bc22, bc23],
  some (some bc257)),
 ([bc85, bc86, bc0, bc22, bc24],
  some (some (218, true, false))),
 ([bc85, bc86, bc0, bc25, bc26],
  some (some bc257)),
 ([bc85, bc86, bc0, bc25, bc27],
  some (some (219, true, false))),
 ([bc85, bc86, bc1], some (some bc257)),
 ([bc85, bc87, bc0, bc22, bc23],
  some (some (220, true, false))),
 ([bc85, bc87, bc0, bc22, bc24],
  some (some (221, true, false))),
 ([bc85, bc87, bc0, bc25, bc26],
  some (some (220, true, false))),
 ([bc85, bc87, bc0, bc25, bc27],
  some (some (222, true, false))),
 ([bc85, bc87, bc1], some (some (220, true, false))),
 ([bc88, bc89, bc0, bc22, bc23],
  some (some bc257)),
 ([bc88, bc89, bc0, bc22, bc24],
  some (some (218, true, false))),
 ([bc88, bc89, bc0, bc25, bc26],
  some (some bc257)),
 ([bc88, bc89, bc0, bc25, bc27],
  some (some (219, true, false))),
 ([bc88, bc89, bc1], some (some bc257)),
 ([bc88, bc90, bc0, bc22, bc23],
  some (some (223, true, false))),
 ([bc88, bc90, bc0, bc22, bc24],
  some (some (224, true, false))),
 ([bc88, bc90, bc0, bc25, bc26],
  some (some (223, true, false))),
 ([bc88, bc90, bc0, bc25, bc27],
  some (some (225, true, false))),
 ([bc88, bc90, bc1], some (some (223, true, false)))]
private def goalCodes0_2_31 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([], some (some (294, false, false)))]
private def goalCodes0_3_0 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes0_2_0
private def goalCodes0_3_2 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc8, bc9, bc28, bc32, bc33],
  some (some bc258)),
 ([bc8, bc9, bc28, bc32, bc34],
  some (some (36, true, true))),
 ([bc8, bc9, bc28, bc35, bc36],
  some (some bc258)),
 ([bc8, bc9, bc28, bc35, bc37],
  some (some (39, true, true))),
 ([bc8, bc9, bc29, bc32, bc33],
  some (some (41, true, true))),
 ([bc8, bc9, bc29, bc32, bc34],
  some (some (43, true, true))),
 ([bc8, bc9, bc29, bc35, bc36],
  some (some (41, true, true))),
 ([bc8, bc9, bc29, bc35, bc37],
  some (some (44, true, true))),
 ([bc8, bc12, bc30, bc32, bc33],
  some (some bc258)),
 ([bc8, bc12, bc30, bc32, bc34],
  some (some (36, true, true))),
 ([bc8, bc12, bc30, bc35, bc36],
  some (some bc258)),
 ([bc8, bc12, bc30, bc35, bc37],
  some (some (39, true, true))),
 ([bc8, bc12, bc31, bc32, bc33],
  some (some (46, true, true))),
 ([bc8, bc12, bc31, bc32, bc34],
  some (some (48, true, true))),
 ([bc8, bc12, bc31, bc35, bc36],
  some (some (46, true, true))),
 ([bc8, bc12, bc31, bc35, bc37],
  some (some (49, true, true)))]
private def goalCodes0_3_5 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes0_2_5
private def goalCodes0_3_7 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc2, bc112, bc113, bc114, bc120],
  some (some bc259)),
 ([bc2,
   bc112,
   bc113,
   bc114,
   bc121,
   bc122,
   bc123],
  some (some bc259)),
 ([bc2,
   bc112,
   bc113,
   bc114,
   bc121,
   bc122,
   bc124],
  some (some (304, true, true))),
 ([bc2,
   bc112,
   bc113,
   bc114,
   bc121,
   bc125,
   bc126],
  some (some bc259)),
 ([bc2,
   bc112,
   bc113,
   bc114,
   bc121,
   bc125,
   bc127],
  some (some (309, true, true))),
 ([bc2, bc112, bc113, bc115, bc120],
  some (some (310, true, true))),
 ([bc2,
   bc112,
   bc113,
   bc115,
   bc121,
   bc122,
   bc123],
  some (some (310, true, true))),
 ([bc2,
   bc112,
   bc113,
   bc115,
   bc121,
   bc122,
   bc124],
  some (some (311, true, true))),
 ([bc2,
   bc112,
   bc113,
   bc115,
   bc121,
   bc125,
   bc126],
  some (some (310, true, true))),
 ([bc2,
   bc112,
   bc113,
   bc115,
   bc121,
   bc125,
   bc127],
  some (some (312, true, true))),
 ([bc2, bc112, bc116, bc117, bc120],
  some (some bc259)),
 ([bc2,
   bc112,
   bc116,
   bc117,
   bc121,
   bc122,
   bc123],
  some (some bc259)),
 ([bc2,
   bc112,
   bc116,
   bc117,
   bc121,
   bc122,
   bc124],
  some (some (304, true, true))),
 ([bc2,
   bc112,
   bc116,
   bc117,
   bc121,
   bc125,
   bc126],
  some (some bc259)),
 ([bc2,
   bc112,
   bc116,
   bc117,
   bc121,
   bc125,
   bc127],
  some (some (309, true, true))),
 ([bc2, bc112, bc116, bc118, bc120],
  some (some (314, true, true))),
 ([bc2,
   bc112,
   bc116,
   bc118,
   bc121,
   bc122,
   bc123],
  some (some (314, true, true))),
 ([bc2,
   bc112,
   bc116,
   bc118,
   bc121,
   bc122,
   bc124],
  some (some (315, true, true))),
 ([bc2,
   bc112,
   bc116,
   bc118,
   bc121,
   bc125,
   bc126],
  some (some (314, true, true))),
 ([bc2,
   bc112,
   bc116,
   bc118,
   bc121,
   bc125,
   bc127],
  some (some (316, true, true))),
 ([bc2, bc119, bc120], some (some bc259)),
 ([bc2, bc119, bc121, bc122, bc123],
  some (some bc259)),
 ([bc2, bc119, bc121, bc122, bc124],
  some (some (304, true, true))),
 ([bc2, bc119, bc121, bc125, bc126],
  some (some bc259)),
 ([bc2, bc119, bc121, bc125, bc127],
  some (some (309, true, true)))]
private def goalCodes0_3_9 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc5, bc128, bc136, bc137, bc138],
  some (some bc260)),
 ([bc5, bc128, bc136, bc137, bc139],
  some (some (323, false, true))),
 ([bc5, bc128, bc136, bc140, bc141],
  some (some bc260)),
 ([bc5, bc128, bc136, bc140, bc142],
  some (some (327, false, true))),
 ([bc5, bc128, bc143], some (some bc260)),
 ([bc5,
   bc129,
   bc130,
   bc131,
   bc136,
   bc137,
   bc138],
  some (some bc260)),
 ([bc5,
   bc129,
   bc130,
   bc131,
   bc136,
   bc137,
   bc139],
  some (some (323, false, true))),
 ([bc5,
   bc129,
   bc130,
   bc131,
   bc136,
   bc140,
   bc141],
  some (some bc260)),
 ([bc5,
   bc129,
   bc130,
   bc131,
   bc136,
   bc140,
   bc142],
  some (some (327, false, true))),
 ([bc5, bc129, bc130, bc131, bc143],
  some (some bc260)),
 ([bc5,
   bc129,
   bc130,
   bc132,
   bc136,
   bc137,
   bc138],
  some (some (334, false, true))),
 ([bc5,
   bc129,
   bc130,
   bc132,
   bc136,
   bc137,
   bc139],
  some (some (335, false, true))),
 ([bc5,
   bc129,
   bc130,
   bc132,
   bc136,
   bc140,
   bc141],
  some (some (334, false, true))),
 ([bc5,
   bc129,
   bc130,
   bc132,
   bc136,
   bc140,
   bc142],
  some (some (336, false, true))),
 ([bc5, bc129, bc130, bc132, bc143],
  some (some (334, false, true))),
 ([bc5,
   bc129,
   bc133,
   bc134,
   bc136,
   bc137,
   bc138],
  some (some bc260)),
 ([bc5,
   bc129,
   bc133,
   bc134,
   bc136,
   bc137,
   bc139],
  some (some (323, false, true))),
 ([bc5,
   bc129,
   bc133,
   bc134,
   bc136,
   bc140,
   bc141],
  some (some bc260)),
 ([bc5,
   bc129,
   bc133,
   bc134,
   bc136,
   bc140,
   bc142],
  some (some (327, false, true))),
 ([bc5, bc129, bc133, bc134, bc143],
  some (some bc260)),
 ([bc5,
   bc129,
   bc133,
   bc135,
   bc136,
   bc137,
   bc138],
  some (some (340, false, true))),
 ([bc5,
   bc129,
   bc133,
   bc135,
   bc136,
   bc137,
   bc139],
  some (some (341, false, true))),
 ([bc5,
   bc129,
   bc133,
   bc135,
   bc136,
   bc140,
   bc141],
  some (some (340, false, true))),
 ([bc5,
   bc129,
   bc133,
   bc135,
   bc136,
   bc140,
   bc142],
  some (some (342, false, true))),
 ([bc5, bc129, bc133, bc135, bc143],
  some (some (340, false, true)))]
private def goalCodes0_3_12 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc218, bc144, bc145, bc146, bc152],
  some (some bc261)),
 ([bc218,
   bc144,
   bc145,
   bc146,
   bc153,
   bc154,
   bc155],
  some (some bc261)),
 ([bc218,
   bc144,
   bc145,
   bc146,
   bc153,
   bc154,
   bc156],
  some (some (350, true, true))),
 ([bc218,
   bc144,
   bc145,
   bc146,
   bc153,
   bc157,
   bc158],
  some (some bc261)),
 ([bc218,
   bc144,
   bc145,
   bc146,
   bc153,
   bc157,
   bc159],
  some (some (354, true, true))),
 ([bc218, bc144, bc145, bc147, bc152],
  some (some (356, true, true))),
 ([bc218,
   bc144,
   bc145,
   bc147,
   bc153,
   bc154,
   bc155],
  some (some (356, true, true))),
 ([bc218,
   bc144,
   bc145,
   bc147,
   bc153,
   bc154,
   bc156],
  some (some (357, true, true))),
 ([bc218,
   bc144,
   bc145,
   bc147,
   bc153,
   bc157,
   bc158],
  some (some (356, true, true))),
 ([bc218,
   bc144,
   bc145,
   bc147,
   bc153,
   bc157,
   bc159],
  some (some (358, true, true))),
 ([bc218, bc144, bc148, bc149, bc152],
  some (some bc261)),
 ([bc218,
   bc144,
   bc148,
   bc149,
   bc153,
   bc154,
   bc155],
  some (some bc261)),
 ([bc218,
   bc144,
   bc148,
   bc149,
   bc153,
   bc154,
   bc156],
  some (some (350, true, true))),
 ([bc218,
   bc144,
   bc148,
   bc149,
   bc153,
   bc157,
   bc158],
  some (some bc261)),
 ([bc218,
   bc144,
   bc148,
   bc149,
   bc153,
   bc157,
   bc159],
  some (some (354, true, true))),
 ([bc218, bc144, bc148, bc150, bc152],
  some (some (360, true, true))),
 ([bc218,
   bc144,
   bc148,
   bc150,
   bc153,
   bc154,
   bc155],
  some (some (360, true, true))),
 ([bc218,
   bc144,
   bc148,
   bc150,
   bc153,
   bc154,
   bc156],
  some (some (361, true, true))),
 ([bc218,
   bc144,
   bc148,
   bc150,
   bc153,
   bc157,
   bc158],
  some (some (360, true, true))),
 ([bc218,
   bc144,
   bc148,
   bc150,
   bc153,
   bc157,
   bc159],
  some (some (362, true, true))),
 ([bc218, bc151, bc152], some (some bc261)),
 ([bc218, bc151, bc153, bc154, bc155],
  some (some bc261)),
 ([bc218, bc151, bc153, bc154, bc156],
  some (some (350, true, true))),
 ([bc218, bc151, bc153, bc157, bc158],
  some (some bc261)),
 ([bc218, bc151, bc153, bc157, bc159],
  some (some (354, true, true)))]
private def goalCodes0_3_14 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc221, (365, false, true), bc163], some (some bc262)),
 ([bc221, (365, false, true), bc164], some (some bc262)),
 ([bc221, bc160, bc161, (370, false, true), bc163],
  some (some bc262)),
 ([bc221, bc160, bc161, (370, false, true), bc164],
  some (some bc262)),
 ([bc221, bc160, bc161, (370, true, false), bc163],
  some (some (372, false, true))),
 ([bc221, bc160, bc161, (370, true, false), bc164],
  some (some (372, false, true))),
 ([bc221, bc160, bc162, (373, true, true), bc163],
  some (some bc262)),
 ([bc221, bc160, bc162, (373, true, true), bc164],
  some (some bc262)),
 ([bc221, bc160, bc162, (373, false, false), bc163],
  some (some (375, false, true))),
 ([bc221, bc160, bc162, (373, false, false), bc164],
  some (some (375, false, true)))]
private def goalCodes0_3_17 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc224, bc165, bc166, bc167, bc173],
  some (some bc263)),
 ([bc224,
   bc165,
   bc166,
   bc167,
   bc174,
   bc175,
   bc176],
  some (some bc263)),
 ([bc224,
   bc165,
   bc166,
   bc167,
   bc174,
   bc175,
   bc177],
  some (some (385, true, true))),
 ([bc224,
   bc165,
   bc166,
   bc167,
   bc174,
   bc178,
   bc179],
  some (some bc263)),
 ([bc224,
   bc165,
   bc166,
   bc167,
   bc174,
   bc178,
   bc180],
  some (some (390, true, true))),
 ([bc224, bc165, bc166, bc168, bc173],
  some (some (391, true, true))),
 ([bc224,
   bc165,
   bc166,
   bc168,
   bc174,
   bc175,
   bc176],
  some (some (391, true, true))),
 ([bc224,
   bc165,
   bc166,
   bc168,
   bc174,
   bc175,
   bc177],
  some (some (393, true, true))),
 ([bc224,
   bc165,
   bc166,
   bc168,
   bc174,
   bc178,
   bc179],
  some (some (391, true, true))),
 ([bc224,
   bc165,
   bc166,
   bc168,
   bc174,
   bc178,
   bc180],
  some (some (394, true, true))),
 ([bc224, bc165, bc169, bc170, bc173],
  some (some bc263)),
 ([bc224,
   bc165,
   bc169,
   bc170,
   bc174,
   bc175,
   bc176],
  some (some bc263)),
 ([bc224,
   bc165,
   bc169,
   bc170,
   bc174,
   bc175,
   bc177],
  some (some (385, true, true))),
 ([bc224,
   bc165,
   bc169,
   bc170,
   bc174,
   bc178,
   bc179],
  some (some bc263)),
 ([bc224,
   bc165,
   bc169,
   bc170,
   bc174,
   bc178,
   bc180],
  some (some (390, true, true))),
 ([bc224, bc165, bc169, bc171, bc173],
  some (some (398, true, true))),
 ([bc224,
   bc165,
   bc169,
   bc171,
   bc174,
   bc175,
   bc176],
  some (some (398, true, true))),
 ([bc224,
   bc165,
   bc169,
   bc171,
   bc174,
   bc175,
   bc177],
  some (some (399, true, true))),
 ([bc224,
   bc165,
   bc169,
   bc171,
   bc174,
   bc178,
   bc179],
  some (some (398, true, true))),
 ([bc224,
   bc165,
   bc169,
   bc171,
   bc174,
   bc178,
   bc180],
  some (some (400, true, true))),
 ([bc224, bc172, bc173], some (some bc263)),
 ([bc224, bc172, bc174, bc175, bc176],
  some (some bc263)),
 ([bc224, bc172, bc174, bc175, bc177],
  some (some (385, true, true))),
 ([bc224, bc172, bc174, bc178, bc179],
  some (some bc263)),
 ([bc224, bc172, bc174, bc178, bc180],
  some (some (390, true, true)))]
private def goalCodes0_3_19 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc227, bc181, bc189, bc190, bc191],
  some (some bc264)),
 ([bc227, bc181, bc189, bc190, bc192],
  some (some (407, false, true))),
 ([bc227, bc181, bc189, bc193, bc194],
  some (some bc264)),
 ([bc227, bc181, bc189, bc193, bc195],
  some (some (411, false, true))),
 ([bc227, bc181, bc196], some (some bc264)),
 ([bc227,
   bc182,
   bc183,
   bc184,
   bc189,
   bc190,
   bc191],
  some (some bc264)),
 ([bc227,
   bc182,
   bc183,
   bc184,
   bc189,
   bc190,
   bc192],
  some (some (407, false, true))),
 ([bc227,
   bc182,
   bc183,
   bc184,
   bc189,
   bc193,
   bc194],
  some (some bc264)),
 ([bc227,
   bc182,
   bc183,
   bc184,
   bc189,
   bc193,
   bc195],
  some (some (411, false, true))),
 ([bc227, bc182, bc183, bc184, bc196],
  some (some bc264)),
 ([bc227,
   bc182,
   bc183,
   bc185,
   bc189,
   bc190,
   bc191],
  some (some (418, false, true))),
 ([bc227,
   bc182,
   bc183,
   bc185,
   bc189,
   bc190,
   bc192],
  some (some (419, false, true))),
 ([bc227,
   bc182,
   bc183,
   bc185,
   bc189,
   bc193,
   bc194],
  some (some (418, false, true))),
 ([bc227,
   bc182,
   bc183,
   bc185,
   bc189,
   bc193,
   bc195],
  some (some (420, false, true))),
 ([bc227, bc182, bc183, bc185, bc196],
  some (some (418, false, true))),
 ([bc227,
   bc182,
   bc186,
   bc187,
   bc189,
   bc190,
   bc191],
  some (some bc264)),
 ([bc227,
   bc182,
   bc186,
   bc187,
   bc189,
   bc190,
   bc192],
  some (some (407, false, true))),
 ([bc227,
   bc182,
   bc186,
   bc187,
   bc189,
   bc193,
   bc194],
  some (some bc264)),
 ([bc227,
   bc182,
   bc186,
   bc187,
   bc189,
   bc193,
   bc195],
  some (some (411, false, true))),
 ([bc227, bc182, bc186, bc187, bc196],
  some (some bc264)),
 ([bc227,
   bc182,
   bc186,
   bc188,
   bc189,
   bc190,
   bc191],
  some (some (424, false, true))),
 ([bc227,
   bc182,
   bc186,
   bc188,
   bc189,
   bc190,
   bc192],
  some (some (425, false, true))),
 ([bc227,
   bc182,
   bc186,
   bc188,
   bc189,
   bc193,
   bc194],
  some (some (424, false, true))),
 ([bc227,
   bc182,
   bc186,
   bc188,
   bc189,
   bc193,
   bc195],
  some (some (426, false, true))),
 ([bc227, bc182, bc186, bc188, bc196],
  some (some (424, false, true)))]
private def goalCodes0_3_22 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc230, bc197, bc198, (427, false, true), bc200],
  some (some bc265)),
 ([bc230, bc197, bc198, (427, false, true), bc201],
  some (some bc265)),
 ([bc230, bc197, bc198, (427, true, false), bc200],
  some (some (434, true, true))),
 ([bc230, bc197, bc198, (427, true, false), bc201],
  some (some (434, true, true))),
 ([bc230, bc197, bc199, (436, true, true), bc200],
  some (some bc265)),
 ([bc230, bc197, bc199, (436, true, true), bc201],
  some (some bc265)),
 ([bc230, bc197, bc199, (436, false, false), bc200],
  some (some (439, true, true))),
 ([bc230, bc197, bc199, (436, false, false), bc201],
  some (some (439, true, true))),
 ([bc230, (432, true, true), bc200], some (some bc265)),
 ([bc230, (432, true, true), bc201], some (some bc265))]
private def goalCodes0_3_24 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc233, bc202, bc210, bc211, bc212],
  some (some bc266)),
 ([bc233, bc202, bc210, bc211, bc213],
  some (some (447, false, true))),
 ([bc233, bc202, bc210, bc214, bc215],
  some (some bc266)),
 ([bc233, bc202, bc210, bc214, bc216],
  some (some (451, false, true))),
 ([bc233, bc202, bc217], some (some bc266)),
 ([bc233,
   bc203,
   bc204,
   bc205,
   bc210,
   bc211,
   bc212],
  some (some bc266)),
 ([bc233,
   bc203,
   bc204,
   bc205,
   bc210,
   bc211,
   bc213],
  some (some (447, false, true))),
 ([bc233,
   bc203,
   bc204,
   bc205,
   bc210,
   bc214,
   bc215],
  some (some bc266)),
 ([bc233,
   bc203,
   bc204,
   bc205,
   bc210,
   bc214,
   bc216],
  some (some (451, false, true))),
 ([bc233, bc203, bc204, bc205, bc217],
  some (some bc266)),
 ([bc233,
   bc203,
   bc204,
   bc206,
   bc210,
   bc211,
   bc212],
  some (some (458, false, true))),
 ([bc233,
   bc203,
   bc204,
   bc206,
   bc210,
   bc211,
   bc213],
  some (some (459, false, true))),
 ([bc233,
   bc203,
   bc204,
   bc206,
   bc210,
   bc214,
   bc215],
  some (some (458, false, true))),
 ([bc233,
   bc203,
   bc204,
   bc206,
   bc210,
   bc214,
   bc216],
  some (some (460, false, true))),
 ([bc233, bc203, bc204, bc206, bc217],
  some (some (458, false, true))),
 ([bc233,
   bc203,
   bc207,
   bc208,
   bc210,
   bc211,
   bc212],
  some (some bc266)),
 ([bc233,
   bc203,
   bc207,
   bc208,
   bc210,
   bc211,
   bc213],
  some (some (447, false, true))),
 ([bc233,
   bc203,
   bc207,
   bc208,
   bc210,
   bc214,
   bc215],
  some (some bc266)),
 ([bc233,
   bc203,
   bc207,
   bc208,
   bc210,
   bc214,
   bc216],
  some (some (451, false, true))),
 ([bc233, bc203, bc207, bc208, bc217],
  some (some bc266)),
 ([bc233,
   bc203,
   bc207,
   bc209,
   bc210,
   bc211,
   bc212],
  some (some (464, false, true))),
 ([bc233,
   bc203,
   bc207,
   bc209,
   bc210,
   bc211,
   bc213],
  some (some (465, false, true))),
 ([bc233,
   bc203,
   bc207,
   bc209,
   bc210,
   bc214,
   bc215],
  some (some (464, false, true))),
 ([bc233,
   bc203,
   bc207,
   bc209,
   bc210,
   bc214,
   bc216],
  some (some (466, false, true))),
 ([bc233, bc203, bc207, bc209, bc217],
  some (some (464, false, true)))]
private def goalCodes0_3_27 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes0_2_12
private def goalCodes0_3_29 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes0_2_14
private def goalCodes0_3_32 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc2, bc3, bc8, bc9, bc10],
  some (some bc236)),
 ([bc2, bc3, bc8, bc9, bc11],
  some (some bc237)),
 ([bc2, bc3, bc8, bc12, bc13],
  some (some bc236)),
 ([bc2, bc3, bc8, bc12, bc14],
  some (some bc238)),
 ([bc2, bc3, bc15], some (some bc236)),
 ([bc2, bc4, bc8, bc9, bc10],
  some (some bc239)),
 ([bc2, bc4, bc8, bc9, bc11],
  some (some bc240)),
 ([bc2, bc4, bc8, bc12, bc13],
  some (some bc239)),
 ([bc2, bc4, bc8, bc12, bc14],
  some (some bc241)),
 ([bc2, bc4, bc15], some (some bc239)),
 ([bc5, bc6, bc8, bc9, bc10],
  some (some bc236)),
 ([bc5, bc6, bc8, bc9, bc11],
  some (some bc237)),
 ([bc5, bc6, bc8, bc12, bc13],
  some (some bc236)),
 ([bc5, bc6, bc8, bc12, bc14],
  some (some bc238)),
 ([bc5, bc6, bc15], some (some bc236)),
 ([bc5, bc7, bc8, bc9, bc10],
  some (some bc242)),
 ([bc5, bc7, bc8, bc9, bc11],
  some (some bc243)),
 ([bc5, bc7, bc8, bc12, bc13],
  some (some bc242)),
 ([bc5, bc7, bc8, bc12, bc14],
  some (some bc244)),
 ([bc5, bc7, bc15], some (some bc242))]
private def goalCodes0_3_34 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc218, bc219, bc2, bc57], some (some bc267)),
 ([bc218, bc219, bc2, bc58], some (some (468, true, false))),
 ([bc218, bc219, bc5, bc60], some (some bc267)),
 ([bc218, bc219, bc5, bc61], some (some (469, true, false))),
 ([bc218, bc220, bc2, bc57], some (some (470, true, false))),
 ([bc218, bc220, bc2, bc58], some (some (471, true, false))),
 ([bc218, bc220, bc5, bc60], some (some (470, true, false))),
 ([bc218, bc220, bc5, bc61], some (some (472, true, false))),
 ([bc221, bc222, bc2, bc57], some (some bc267)),
 ([bc221, bc222, bc2, bc58], some (some (468, true, false))),
 ([bc221, bc222, bc5, bc60], some (some bc267)),
 ([bc221, bc222, bc5, bc61], some (some (469, true, false))),
 ([bc221, bc223, bc2, bc57], some (some (473, true, false))),
 ([bc221, bc223, bc2, bc58], some (some (474, true, false))),
 ([bc221, bc223, bc5, bc60], some (some (473, true, false))),
 ([bc221, bc223, bc5, bc61], some (some (475, true, false)))]
private def goalCodes0_3_35 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc218, bc219, bc224, bc225], some (some bc268)),
 ([bc218, bc219, bc224, bc226], some (some (477, true, false))),
 ([bc218, bc219, bc227, bc228], some (some bc268)),
 ([bc218, bc219, bc227, bc229], some (some (481, true, false))),
 ([bc218, bc220, bc224, bc225], some (some (159, true, false))),
 ([bc218, bc220, bc224, bc226], some (some (482, true, false))),
 ([bc218, bc220, bc227, bc228], some (some (159, true, false))),
 ([bc218, bc220, bc227, bc229], some (some (483, true, false))),
 ([bc221, bc222, bc224, bc225], some (some bc268)),
 ([bc221, bc222, bc224, bc226], some (some (477, true, false))),
 ([bc221, bc222, bc227, bc228], some (some bc268)),
 ([bc221, bc222, bc227, bc229], some (some (481, true, false))),
 ([bc221, bc223, bc224, bc225], some (some (165, true, false))),
 ([bc221, bc223, bc224, bc226], some (some (484, true, false))),
 ([bc221, bc223, bc227, bc228], some (some (165, true, false))),
 ([bc221, bc223, bc227, bc229], some (some (485, true, false)))]
private def goalCodes0_3_36 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc224, bc51], some (some (486, false, false))),
 ([bc224, bc52], some (some (487, false, false))),
 ([bc227, bc54], some (some (486, false, false))),
 ([bc227, bc55], some (some (488, false, false)))]
private def goalCodes0_3_38 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc230, bc231, bc224, bc225], some (some bc269)),
 ([bc230, bc231, bc224, bc226], some (some (491, false, false))),
 ([bc230, bc231, bc227, bc228], some (some bc269)),
 ([bc230, bc231, bc227, bc229], some (some (492, false, false))),
 ([bc230, bc232, bc224, bc225], some (some (494, false, false))),
 ([bc230, bc232, bc224, bc226], some (some (495, false, false))),
 ([bc230, bc232, bc227, bc228], some (some (494, false, false))),
 ([bc230, bc232, bc227, bc229], some (some (496, false, false))),
 ([bc233, bc234, bc224, bc225], some (some bc269)),
 ([bc233, bc234, bc224, bc226], some (some (491, false, false))),
 ([bc233, bc234, bc227, bc228], some (some bc269)),
 ([bc233, bc234, bc227, bc229], some (some (492, false, false))),
 ([bc233, bc235, bc224, bc225], some (some (499, false, false))),
 ([bc233, bc235, bc224, bc226], some (some (500, false, false))),
 ([bc233, bc235, bc227, bc228], some (some (499, false, false))),
 ([bc233, bc235, bc227, bc229], some (some (501, false, false)))]
private def goalCodes0_3_39 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc230, bc231], some (some (502, false, false))),
 ([bc230, bc232], some (some (503, false, false))),
 ([bc233, bc234], some (some (502, false, false))),
 ([bc233, bc235], some (some (504, false, false)))]
private def goalCodes0_3_40 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc85, bc86], some (some (505, true, false))),
 ([bc85, bc87], some (some (506, true, false))),
 ([bc88, bc89], some (some (505, true, false))),
 ([bc88, bc90], some (some (507, true, false)))]
private def goalCodes0_3_41 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc8, bc62, bc17], some none),
 ([bc8, bc62, bc18], some none),
 ([bc8, bc63, bc20], some none),
 ([bc8, bc63, bc21], some none),
 ([bc15, bc16, bc17, bc62, bc17], some none),
 ([bc15, bc16, bc17, bc62, bc18], some none),
 ([bc15, bc16, bc17, bc63, bc20], some none),
 ([bc15, bc16, bc17, bc63, bc21], some none),
 ([bc15, bc16, bc18, bc62, bc17], none),
 ([bc15, bc16, bc18, bc62, bc18], some none),
 ([bc15, bc16, bc18, bc63, bc20], none),
 ([bc15, bc16, bc18, bc63, bc21],
  some (some (168, false, false))),
 ([bc15, bc19, bc20, bc62, bc17], some none),
 ([bc15, bc19, bc20, bc62, bc18], some none),
 ([bc15, bc19, bc20, bc63, bc20], some none),
 ([bc15, bc19, bc20, bc63, bc21], some none),
 ([bc15, bc19, bc21, bc62, bc17], none),
 ([bc15, bc19, bc21, bc62, bc18],
  some (some (168, true, false))),
 ([bc15, bc19, bc21, bc63, bc20], none),
 ([bc15, bc19, bc21, bc63, bc21], some none)]
private def goalCodes0_3_42 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc62, bc91], some (some (227, false, false))),
 ([bc62, (176, true, false)], some none),
 ([bc63, (228, true, true)], some (some (227, false, false))),
 ([bc63, (228, false, false)], some (some (230, false, false)))]
private def goalCodes0_4_0 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes0_2_0
private def cutCodes0_2 : List (ℕ × Bool × Bool) := [(7, true, false), (177, false, false), bc91]
private def cutCodes0_3 : List (ℕ × Bool × Bool) := [(7, true, false), (177, true, true), (296, false, true), (176, true, false)]
private def cutCodes0_4 : List (ℕ × Bool × Bool) := [(7, true, false), (177, true, true), (296, false, true), bc91]

private theorem hGoal0_2_0 : trunkGoalBranches (trunkCatalog.states 0) 2 0 = goalCodes0_2_0.map decodeGoalBranch := by
  decide +kernel

private abbrev goalSpec0_2_5 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 0) 2))[5-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal0_2_5 : trunkGoalBranches (trunkCatalog.states 0) 2 5 = goalCodes0_2_5.map decodeGoalBranch := by
  have hi : (goalSpec0_2_5.first,goalSpec0_2_5.firstUpper,trunkSpecIncoming goalSpec0_2_5) = endpointInput0_6 := by decide +kernel
  have hj : (goalSpec0_2_5.second,goalSpec0_2_5.secondUpper,trunkSpecIncoming goalSpec0_2_5) = endpointInput0_7 := by decide +kernel
  have heL : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_2_5.first goalSpec0_2_5.firstUpper (trunkSpecIncoming goalSpec0_2_5) = endpointCodes0_6.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hi).trans hEndpoint0_6
  have heR : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_2_5.second goalSpec0_2_5.secondUpper (trunkSpecIncoming goalSpec0_2_5) = endpointCodes0_7.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hj).trans hEndpoint0_7
  have he : goalSpec0_2_5.extra = ([bc15] : List (ℕ × Bool × Bool)).map decodeThresholdBound := by decide +kernel
  unfold trunkGoalBranches
  rw [if_neg (by decide)]
  unfold trunkBranches
  rw [heL,heR,he]
  decide +kernel

private abbrev goalSpec0_2_10 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 0) 2))[10-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal0_2_10 : trunkGoalBranches (trunkCatalog.states 0) 2 10 = goalCodes0_2_10.map decodeGoalBranch := by
  have hi : (goalSpec0_2_10.first,goalSpec0_2_10.firstUpper,trunkSpecIncoming goalSpec0_2_10) = endpointInput0_10 := by decide +kernel
  have hj : (goalSpec0_2_10.second,goalSpec0_2_10.secondUpper,trunkSpecIncoming goalSpec0_2_10) = endpointInput0_11 := by decide +kernel
  have heL : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_2_10.first goalSpec0_2_10.firstUpper (trunkSpecIncoming goalSpec0_2_10) = endpointCodes0_10.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hi).trans hEndpoint0_10
  have heR : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_2_10.second goalSpec0_2_10.secondUpper (trunkSpecIncoming goalSpec0_2_10) = endpointCodes0_11.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hj).trans hEndpoint0_11
  have he : goalSpec0_2_10.extra = ([bc1] : List (ℕ × Bool × Bool)).map decodeThresholdBound := by decide +kernel
  unfold trunkGoalBranches
  rw [if_neg (by decide)]
  unfold trunkBranches
  rw [heL,heR,he]
  decide +kernel

private abbrev goalSpec0_2_12 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 0) 2))[12-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal0_2_12 : trunkGoalBranches (trunkCatalog.states 0) 2 12 = goalCodes0_2_12.map decodeGoalBranch := by
  have hi : (goalSpec0_2_12.first,goalSpec0_2_12.firstUpper,trunkSpecIncoming goalSpec0_2_12) = endpointInput0_18 := by decide +kernel
  have hj : (goalSpec0_2_12.second,goalSpec0_2_12.secondUpper,trunkSpecIncoming goalSpec0_2_12) = endpointInput0_19 := by decide +kernel
  have heL : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_2_12.first goalSpec0_2_12.firstUpper (trunkSpecIncoming goalSpec0_2_12) = endpointCodes0_18.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hi).trans hEndpoint0_18
  have heR : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_2_12.second goalSpec0_2_12.secondUpper (trunkSpecIncoming goalSpec0_2_12) = endpointCodes0_19.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hj).trans hEndpoint0_19
  have he : goalSpec0_2_12.extra = ([bc85] : List (ℕ × Bool × Bool)).map decodeThresholdBound := by decide +kernel
  unfold trunkGoalBranches
  rw [if_neg (by decide)]
  unfold trunkBranches
  rw [heL,heR,he]
  decide +kernel

private abbrev goalSpec0_2_14 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 0) 2))[14-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal0_2_14 : trunkGoalBranches (trunkCatalog.states 0) 2 14 = goalCodes0_2_14.map decodeGoalBranch := by
  have hi : (goalSpec0_2_14.first,goalSpec0_2_14.firstUpper,trunkSpecIncoming goalSpec0_2_14) = endpointInput0_20 := by decide +kernel
  have hj : (goalSpec0_2_14.second,goalSpec0_2_14.secondUpper,trunkSpecIncoming goalSpec0_2_14) = endpointInput0_21 := by decide +kernel
  have heL : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_2_14.first goalSpec0_2_14.firstUpper (trunkSpecIncoming goalSpec0_2_14) = endpointCodes0_20.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hi).trans hEndpoint0_20
  have heR : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_2_14.second goalSpec0_2_14.secondUpper (trunkSpecIncoming goalSpec0_2_14) = endpointCodes0_21.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hj).trans hEndpoint0_21
  have he : goalSpec0_2_14.extra = ([bc88] : List (ℕ × Bool × Bool)).map decodeThresholdBound := by decide +kernel
  unfold trunkGoalBranches
  rw [if_neg (by decide)]
  unfold trunkBranches
  rw [heL,heR,he]
  decide +kernel

private abbrev goalSpec0_2_18 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 0) 2))[18-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal0_2_18 : trunkGoalBranches (trunkCatalog.states 0) 2 18 = goalCodes0_2_18.map decodeGoalBranch := by
  have hi : (goalSpec0_2_18.first,goalSpec0_2_18.firstUpper,trunkSpecIncoming goalSpec0_2_18) = endpointInput0_25 := by decide +kernel
  have hj : (goalSpec0_2_18.second,goalSpec0_2_18.secondUpper,trunkSpecIncoming goalSpec0_2_18) = endpointInput0_26 := by decide +kernel
  have heL : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_2_18.first goalSpec0_2_18.firstUpper (trunkSpecIncoming goalSpec0_2_18) = endpointCodes0_25.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hi).trans hEndpoint0_25
  have heR : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_2_18.second goalSpec0_2_18.secondUpper (trunkSpecIncoming goalSpec0_2_18) = endpointCodes0_26.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hj).trans hEndpoint0_26
  have he : goalSpec0_2_18.extra = ([bc249] : List (ℕ × Bool × Bool)).map decodeThresholdBound := by decide +kernel
  unfold trunkGoalBranches
  rw [if_neg (by decide)]
  unfold trunkBranches
  rw [heL,heR,he]
  decide +kernel

private abbrev goalSpec0_2_20 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 0) 2))[20-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal0_2_20 : trunkGoalBranches (trunkCatalog.states 0) 2 20 = goalCodes0_2_20.map decodeGoalBranch := by
  have hi : (goalSpec0_2_20.first,goalSpec0_2_20.firstUpper,trunkSpecIncoming goalSpec0_2_20) = endpointInput0_27 := by decide +kernel
  have hj : (goalSpec0_2_20.second,goalSpec0_2_20.secondUpper,trunkSpecIncoming goalSpec0_2_20) = endpointInput0_28 := by decide +kernel
  have heL : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_2_20.first goalSpec0_2_20.firstUpper (trunkSpecIncoming goalSpec0_2_20) = endpointCodes0_27.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hi).trans hEndpoint0_27
  have heR : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_2_20.second goalSpec0_2_20.secondUpper (trunkSpecIncoming goalSpec0_2_20) = endpointCodes0_28.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hj).trans hEndpoint0_28
  have he : goalSpec0_2_20.extra = ([bc251] : List (ℕ × Bool × Bool)).map decodeThresholdBound := by decide +kernel
  unfold trunkGoalBranches
  rw [if_neg (by decide)]
  unfold trunkBranches
  rw [heL,heR,he]
  decide +kernel

private abbrev goalSpec0_2_22 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 0) 2))[22-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal0_2_22 : trunkGoalBranches (trunkCatalog.states 0) 2 22 = goalCodes0_2_22.map decodeGoalBranch := by
  have hi : (goalSpec0_2_22.first,goalSpec0_2_22.firstUpper,trunkSpecIncoming goalSpec0_2_22) = endpointInput0_29 := by decide +kernel
  have hj : (goalSpec0_2_22.second,goalSpec0_2_22.secondUpper,trunkSpecIncoming goalSpec0_2_22) = endpointInput0_30 := by decide +kernel
  have heL : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_2_22.first goalSpec0_2_22.firstUpper (trunkSpecIncoming goalSpec0_2_22) = endpointCodes0_29.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hi).trans hEndpoint0_29
  have heR : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_2_22.second goalSpec0_2_22.secondUpper (trunkSpecIncoming goalSpec0_2_22) = endpointCodes0_30.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hj).trans hEndpoint0_30
  have he : goalSpec0_2_22.extra = ([bc253] : List (ℕ × Bool × Bool)).map decodeThresholdBound := by decide +kernel
  unfold trunkGoalBranches
  rw [if_neg (by decide)]
  unfold trunkBranches
  rw [heL,heR,he]
  decide +kernel

private abbrev goalSpec0_2_24 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 0) 2))[24-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal0_2_24 : trunkGoalBranches (trunkCatalog.states 0) 2 24 = goalCodes0_2_24.map decodeGoalBranch := by
  have hi : (goalSpec0_2_24.first,goalSpec0_2_24.firstUpper,trunkSpecIncoming goalSpec0_2_24) = endpointInput0_31 := by decide +kernel
  have hj : (goalSpec0_2_24.second,goalSpec0_2_24.secondUpper,trunkSpecIncoming goalSpec0_2_24) = endpointInput0_32 := by decide +kernel
  have heL : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_2_24.first goalSpec0_2_24.firstUpper (trunkSpecIncoming goalSpec0_2_24) = endpointCodes0_31.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hi).trans hEndpoint0_31
  have heR : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_2_24.second goalSpec0_2_24.secondUpper (trunkSpecIncoming goalSpec0_2_24) = endpointCodes0_32.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hj).trans hEndpoint0_32
  have he : goalSpec0_2_24.extra = ([bc255] : List (ℕ × Bool × Bool)).map decodeThresholdBound := by decide +kernel
  unfold trunkGoalBranches
  rw [if_neg (by decide)]
  unfold trunkBranches
  rw [heL,heR,he]
  decide +kernel

private abbrev goalSpec0_2_27 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 0) 2))[27-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal0_2_27 : trunkGoalBranches (trunkCatalog.states 0) 2 27 = goalCodes0_2_27.map decodeGoalBranch := by
  have hi : (goalSpec0_2_27.first,goalSpec0_2_27.firstUpper,trunkSpecIncoming goalSpec0_2_27) = endpointInput0_0 := by decide +kernel
  have hj : (goalSpec0_2_27.second,goalSpec0_2_27.secondUpper,trunkSpecIncoming goalSpec0_2_27) = endpointInput0_1 := by decide +kernel
  have heL : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_2_27.first goalSpec0_2_27.firstUpper (trunkSpecIncoming goalSpec0_2_27) = endpointCodes0_0.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hi).trans hEndpoint0_0
  have heR : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_2_27.second goalSpec0_2_27.secondUpper (trunkSpecIncoming goalSpec0_2_27) = endpointCodes0_1.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hj).trans hEndpoint0_1
  have he : goalSpec0_2_27.extra = ([] : List (ℕ × Bool × Bool)).map decodeThresholdBound := by decide +kernel
  unfold trunkGoalBranches
  rw [if_neg (by decide)]
  unfold trunkBranches
  rw [heL,heR,he]
  decide +kernel

private abbrev goalSpec0_2_29 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 0) 2))[29-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal0_2_29 : trunkGoalBranches (trunkCatalog.states 0) 2 29 = goalCodes0_2_29.map decodeGoalBranch := by
  have hi : (goalSpec0_2_29.first,goalSpec0_2_29.firstUpper,trunkSpecIncoming goalSpec0_2_29) = endpointInput0_22 := by decide +kernel
  have hj : (goalSpec0_2_29.second,goalSpec0_2_29.secondUpper,trunkSpecIncoming goalSpec0_2_29) = endpointInput0_3 := by decide +kernel
  have heL : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_2_29.first goalSpec0_2_29.firstUpper (trunkSpecIncoming goalSpec0_2_29) = endpointCodes0_22.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hi).trans hEndpoint0_22
  have heR : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_2_29.second goalSpec0_2_29.secondUpper (trunkSpecIncoming goalSpec0_2_29) = endpointCodes0_3.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hj).trans hEndpoint0_3
  have he : goalSpec0_2_29.extra = ([] : List (ℕ × Bool × Bool)).map decodeThresholdBound := by decide +kernel
  unfold trunkGoalBranches
  rw [if_neg (by decide)]
  unfold trunkBranches
  rw [heL,heR,he]
  decide +kernel

private abbrev goalSpec0_2_31 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 0) 2))[31-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal0_2_31 : trunkGoalBranches (trunkCatalog.states 0) 2 31 = goalCodes0_2_31.map decodeGoalBranch := by
  have hi : (goalSpec0_2_31.first,goalSpec0_2_31.firstUpper,trunkSpecIncoming goalSpec0_2_31) = endpointInput0_34 := by decide +kernel
  have hj : (goalSpec0_2_31.second,goalSpec0_2_31.secondUpper,trunkSpecIncoming goalSpec0_2_31) = endpointInput0_24 := by decide +kernel
  have heL : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_2_31.first goalSpec0_2_31.firstUpper (trunkSpecIncoming goalSpec0_2_31) = endpointCodes0_34.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hi).trans hEndpoint0_34
  have heR : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_2_31.second goalSpec0_2_31.secondUpper (trunkSpecIncoming goalSpec0_2_31) = endpointCodes0_24.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hj).trans hEndpoint0_24
  have he : goalSpec0_2_31.extra = ([] : List (ℕ × Bool × Bool)).map decodeThresholdBound := by decide +kernel
  unfold trunkGoalBranches
  rw [if_neg (by decide)]
  unfold trunkBranches
  rw [heL,heR,he]
  decide +kernel

private theorem hGoal0_3_0 : trunkGoalBranches (trunkCatalog.states 0) 3 0 = goalCodes0_3_0.map decodeGoalBranch := by
  exact hGoal0_2_0

private abbrev goalSpec0_3_2 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 0) 3))[2-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal0_3_2 : trunkGoalBranches (trunkCatalog.states 0) 3 2 = goalCodes0_3_2.map decodeGoalBranch := by
  have hi : (goalSpec0_3_2.first,goalSpec0_3_2.firstUpper,trunkSpecIncoming goalSpec0_3_2) = endpointInput0_4 := by decide +kernel
  have hj : (goalSpec0_3_2.second,goalSpec0_3_2.secondUpper,trunkSpecIncoming goalSpec0_3_2) = endpointInput0_5 := by decide +kernel
  have heL : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_3_2.first goalSpec0_3_2.firstUpper (trunkSpecIncoming goalSpec0_3_2) = endpointCodes0_4.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hi).trans hEndpoint0_4
  have heR : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_3_2.second goalSpec0_3_2.secondUpper (trunkSpecIncoming goalSpec0_3_2) = endpointCodes0_5.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hj).trans hEndpoint0_5
  have he : goalSpec0_3_2.extra = ([bc8] : List (ℕ × Bool × Bool)).map decodeThresholdBound := by decide +kernel
  unfold trunkGoalBranches
  rw [if_neg (by decide)]
  unfold trunkBranches
  rw [heL,heR,he]
  decide +kernel

private abbrev goalSpec0_3_5 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 0) 3))[5-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal0_3_5 : trunkGoalBranches (trunkCatalog.states 0) 3 5 = goalCodes0_3_5.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 0) 3 5 = trunkGoalBranches (trunkCatalog.states 0) 2 5 := by
      apply congrArg (trunkBranches (trunkCatalog.states 0).context)
      decide +kernel
    exact he.trans hGoal0_2_5
  | have hi : (goalSpec0_3_5.first,goalSpec0_3_5.firstUpper,trunkSpecIncoming goalSpec0_3_5) = endpointInput0_6 := by decide +kernel
    have hj : (goalSpec0_3_5.second,goalSpec0_3_5.secondUpper,trunkSpecIncoming goalSpec0_3_5) = endpointInput0_7 := by decide +kernel
    have heL : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_3_5.first goalSpec0_3_5.firstUpper (trunkSpecIncoming goalSpec0_3_5) = endpointCodes0_6.map decodeEndpoint0 :=
      (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hi).trans hEndpoint0_6
    have heR : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_3_5.second goalSpec0_3_5.secondUpper (trunkSpecIncoming goalSpec0_3_5) = endpointCodes0_7.map decodeEndpoint0 :=
      (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hj).trans hEndpoint0_7
    have he : goalSpec0_3_5.extra = ([bc15] : List (ℕ × Bool × Bool)).map decodeThresholdBound := by decide +kernel
    unfold trunkGoalBranches
    rw [if_neg (by decide)]
    unfold trunkBranches
    rw [heL,heR,he]
    decide +kernel

private abbrev goalSpec0_3_7 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 0) 3))[7-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal0_3_7 : trunkGoalBranches (trunkCatalog.states 0) 3 7 = goalCodes0_3_7.map decodeGoalBranch := by
  have hi : (goalSpec0_3_7.first,goalSpec0_3_7.firstUpper,trunkSpecIncoming goalSpec0_3_7) = endpointInput0_35 := by decide +kernel
  have hj : (goalSpec0_3_7.second,goalSpec0_3_7.secondUpper,trunkSpecIncoming goalSpec0_3_7) = endpointInput0_36 := by decide +kernel
  have heL : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_3_7.first goalSpec0_3_7.firstUpper (trunkSpecIncoming goalSpec0_3_7) = endpointCodes0_35.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hi).trans hEndpoint0_35
  have heR : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_3_7.second goalSpec0_3_7.secondUpper (trunkSpecIncoming goalSpec0_3_7) = endpointCodes0_36.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hj).trans hEndpoint0_36
  have he : goalSpec0_3_7.extra = ([bc2] : List (ℕ × Bool × Bool)).map decodeThresholdBound := by decide +kernel
  unfold trunkGoalBranches
  rw [if_neg (by decide)]
  unfold trunkBranches
  rw [heL,heR,he]
  decide +kernel

private abbrev goalSpec0_3_9 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 0) 3))[9-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal0_3_9 : trunkGoalBranches (trunkCatalog.states 0) 3 9 = goalCodes0_3_9.map decodeGoalBranch := by
  have hi : (goalSpec0_3_9.first,goalSpec0_3_9.firstUpper,trunkSpecIncoming goalSpec0_3_9) = endpointInput0_37 := by decide +kernel
  have hj : (goalSpec0_3_9.second,goalSpec0_3_9.secondUpper,trunkSpecIncoming goalSpec0_3_9) = endpointInput0_38 := by decide +kernel
  have heL : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_3_9.first goalSpec0_3_9.firstUpper (trunkSpecIncoming goalSpec0_3_9) = endpointCodes0_37.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hi).trans hEndpoint0_37
  have heR : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_3_9.second goalSpec0_3_9.secondUpper (trunkSpecIncoming goalSpec0_3_9) = endpointCodes0_38.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hj).trans hEndpoint0_38
  have he : goalSpec0_3_9.extra = ([bc5] : List (ℕ × Bool × Bool)).map decodeThresholdBound := by decide +kernel
  unfold trunkGoalBranches
  rw [if_neg (by decide)]
  unfold trunkBranches
  rw [heL,heR,he]
  decide +kernel

private abbrev goalSpec0_3_12 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 0) 3))[12-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal0_3_12 : trunkGoalBranches (trunkCatalog.states 0) 3 12 = goalCodes0_3_12.map decodeGoalBranch := by
  have hi : (goalSpec0_3_12.first,goalSpec0_3_12.firstUpper,trunkSpecIncoming goalSpec0_3_12) = endpointInput0_39 := by decide +kernel
  have hj : (goalSpec0_3_12.second,goalSpec0_3_12.secondUpper,trunkSpecIncoming goalSpec0_3_12) = endpointInput0_40 := by decide +kernel
  have heL : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_3_12.first goalSpec0_3_12.firstUpper (trunkSpecIncoming goalSpec0_3_12) = endpointCodes0_39.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hi).trans hEndpoint0_39
  have heR : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_3_12.second goalSpec0_3_12.secondUpper (trunkSpecIncoming goalSpec0_3_12) = endpointCodes0_40.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hj).trans hEndpoint0_40
  have he : goalSpec0_3_12.extra = ([bc218] : List (ℕ × Bool × Bool)).map decodeThresholdBound := by decide +kernel
  unfold trunkGoalBranches
  rw [if_neg (by decide)]
  unfold trunkBranches
  rw [heL,heR,he]
  decide +kernel

private abbrev goalSpec0_3_14 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 0) 3))[14-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal0_3_14 : trunkGoalBranches (trunkCatalog.states 0) 3 14 = goalCodes0_3_14.map decodeGoalBranch := by
  have hi : (goalSpec0_3_14.first,goalSpec0_3_14.firstUpper,trunkSpecIncoming goalSpec0_3_14) = endpointInput0_41 := by decide +kernel
  have hj : (goalSpec0_3_14.second,goalSpec0_3_14.secondUpper,trunkSpecIncoming goalSpec0_3_14) = endpointInput0_42 := by decide +kernel
  have heL : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_3_14.first goalSpec0_3_14.firstUpper (trunkSpecIncoming goalSpec0_3_14) = endpointCodes0_41.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hi).trans hEndpoint0_41
  have heR : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_3_14.second goalSpec0_3_14.secondUpper (trunkSpecIncoming goalSpec0_3_14) = endpointCodes0_42.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hj).trans hEndpoint0_42
  have he : goalSpec0_3_14.extra = ([bc221] : List (ℕ × Bool × Bool)).map decodeThresholdBound := by decide +kernel
  unfold trunkGoalBranches
  rw [if_neg (by decide)]
  unfold trunkBranches
  rw [heL,heR,he]
  decide +kernel

private abbrev goalSpec0_3_17 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 0) 3))[17-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal0_3_17 : trunkGoalBranches (trunkCatalog.states 0) 3 17 = goalCodes0_3_17.map decodeGoalBranch := by
  have hi : (goalSpec0_3_17.first,goalSpec0_3_17.firstUpper,trunkSpecIncoming goalSpec0_3_17) = endpointInput0_43 := by decide +kernel
  have hj : (goalSpec0_3_17.second,goalSpec0_3_17.secondUpper,trunkSpecIncoming goalSpec0_3_17) = endpointInput0_44 := by decide +kernel
  have heL : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_3_17.first goalSpec0_3_17.firstUpper (trunkSpecIncoming goalSpec0_3_17) = endpointCodes0_43.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hi).trans hEndpoint0_43
  have heR : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_3_17.second goalSpec0_3_17.secondUpper (trunkSpecIncoming goalSpec0_3_17) = endpointCodes0_44.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hj).trans hEndpoint0_44
  have he : goalSpec0_3_17.extra = ([bc224] : List (ℕ × Bool × Bool)).map decodeThresholdBound := by decide +kernel
  unfold trunkGoalBranches
  rw [if_neg (by decide)]
  unfold trunkBranches
  rw [heL,heR,he]
  decide +kernel

private abbrev goalSpec0_3_19 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 0) 3))[19-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal0_3_19 : trunkGoalBranches (trunkCatalog.states 0) 3 19 = goalCodes0_3_19.map decodeGoalBranch := by
  have hi : (goalSpec0_3_19.first,goalSpec0_3_19.firstUpper,trunkSpecIncoming goalSpec0_3_19) = endpointInput0_45 := by decide +kernel
  have hj : (goalSpec0_3_19.second,goalSpec0_3_19.secondUpper,trunkSpecIncoming goalSpec0_3_19) = endpointInput0_46 := by decide +kernel
  have heL : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_3_19.first goalSpec0_3_19.firstUpper (trunkSpecIncoming goalSpec0_3_19) = endpointCodes0_45.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hi).trans hEndpoint0_45
  have heR : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_3_19.second goalSpec0_3_19.secondUpper (trunkSpecIncoming goalSpec0_3_19) = endpointCodes0_46.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hj).trans hEndpoint0_46
  have he : goalSpec0_3_19.extra = ([bc227] : List (ℕ × Bool × Bool)).map decodeThresholdBound := by decide +kernel
  unfold trunkGoalBranches
  rw [if_neg (by decide)]
  unfold trunkBranches
  rw [heL,heR,he]
  decide +kernel

private abbrev goalSpec0_3_22 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 0) 3))[22-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal0_3_22 : trunkGoalBranches (trunkCatalog.states 0) 3 22 = goalCodes0_3_22.map decodeGoalBranch := by
  have hi : (goalSpec0_3_22.first,goalSpec0_3_22.firstUpper,trunkSpecIncoming goalSpec0_3_22) = endpointInput0_47 := by decide +kernel
  have hj : (goalSpec0_3_22.second,goalSpec0_3_22.secondUpper,trunkSpecIncoming goalSpec0_3_22) = endpointInput0_48 := by decide +kernel
  have heL : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_3_22.first goalSpec0_3_22.firstUpper (trunkSpecIncoming goalSpec0_3_22) = endpointCodes0_47.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hi).trans hEndpoint0_47
  have heR : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_3_22.second goalSpec0_3_22.secondUpper (trunkSpecIncoming goalSpec0_3_22) = endpointCodes0_48.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hj).trans hEndpoint0_48
  have he : goalSpec0_3_22.extra = ([bc230] : List (ℕ × Bool × Bool)).map decodeThresholdBound := by decide +kernel
  unfold trunkGoalBranches
  rw [if_neg (by decide)]
  unfold trunkBranches
  rw [heL,heR,he]
  decide +kernel

private abbrev goalSpec0_3_24 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 0) 3))[24-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal0_3_24 : trunkGoalBranches (trunkCatalog.states 0) 3 24 = goalCodes0_3_24.map decodeGoalBranch := by
  have hi : (goalSpec0_3_24.first,goalSpec0_3_24.firstUpper,trunkSpecIncoming goalSpec0_3_24) = endpointInput0_49 := by decide +kernel
  have hj : (goalSpec0_3_24.second,goalSpec0_3_24.secondUpper,trunkSpecIncoming goalSpec0_3_24) = endpointInput0_50 := by decide +kernel
  have heL : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_3_24.first goalSpec0_3_24.firstUpper (trunkSpecIncoming goalSpec0_3_24) = endpointCodes0_49.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hi).trans hEndpoint0_49
  have heR : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_3_24.second goalSpec0_3_24.secondUpper (trunkSpecIncoming goalSpec0_3_24) = endpointCodes0_50.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hj).trans hEndpoint0_50
  have he : goalSpec0_3_24.extra = ([bc233] : List (ℕ × Bool × Bool)).map decodeThresholdBound := by decide +kernel
  unfold trunkGoalBranches
  rw [if_neg (by decide)]
  unfold trunkBranches
  rw [heL,heR,he]
  decide +kernel

private abbrev goalSpec0_3_27 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 0) 3))[27-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal0_3_27 : trunkGoalBranches (trunkCatalog.states 0) 3 27 = goalCodes0_3_27.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 0) 3 27 = trunkGoalBranches (trunkCatalog.states 0) 2 12 := by
      apply congrArg (trunkBranches (trunkCatalog.states 0).context)
      decide +kernel
    exact he.trans hGoal0_2_12
  | have hi : (goalSpec0_3_27.first,goalSpec0_3_27.firstUpper,trunkSpecIncoming goalSpec0_3_27) = endpointInput0_18 := by decide +kernel
    have hj : (goalSpec0_3_27.second,goalSpec0_3_27.secondUpper,trunkSpecIncoming goalSpec0_3_27) = endpointInput0_19 := by decide +kernel
    have heL : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_3_27.first goalSpec0_3_27.firstUpper (trunkSpecIncoming goalSpec0_3_27) = endpointCodes0_18.map decodeEndpoint0 :=
      (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hi).trans hEndpoint0_18
    have heR : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_3_27.second goalSpec0_3_27.secondUpper (trunkSpecIncoming goalSpec0_3_27) = endpointCodes0_19.map decodeEndpoint0 :=
      (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hj).trans hEndpoint0_19
    have he : goalSpec0_3_27.extra = ([bc85] : List (ℕ × Bool × Bool)).map decodeThresholdBound := by decide +kernel
    unfold trunkGoalBranches
    rw [if_neg (by decide)]
    unfold trunkBranches
    rw [heL,heR,he]
    decide +kernel

private abbrev goalSpec0_3_29 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 0) 3))[29-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal0_3_29 : trunkGoalBranches (trunkCatalog.states 0) 3 29 = goalCodes0_3_29.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 0) 3 29 = trunkGoalBranches (trunkCatalog.states 0) 2 14 := by
      apply congrArg (trunkBranches (trunkCatalog.states 0).context)
      decide +kernel
    exact he.trans hGoal0_2_14
  | have hi : (goalSpec0_3_29.first,goalSpec0_3_29.firstUpper,trunkSpecIncoming goalSpec0_3_29) = endpointInput0_20 := by decide +kernel
    have hj : (goalSpec0_3_29.second,goalSpec0_3_29.secondUpper,trunkSpecIncoming goalSpec0_3_29) = endpointInput0_21 := by decide +kernel
    have heL : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_3_29.first goalSpec0_3_29.firstUpper (trunkSpecIncoming goalSpec0_3_29) = endpointCodes0_20.map decodeEndpoint0 :=
      (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hi).trans hEndpoint0_20
    have heR : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_3_29.second goalSpec0_3_29.secondUpper (trunkSpecIncoming goalSpec0_3_29) = endpointCodes0_21.map decodeEndpoint0 :=
      (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hj).trans hEndpoint0_21
    have he : goalSpec0_3_29.extra = ([bc88] : List (ℕ × Bool × Bool)).map decodeThresholdBound := by decide +kernel
    unfold trunkGoalBranches
    rw [if_neg (by decide)]
    unfold trunkBranches
    rw [heL,heR,he]
    decide +kernel

private abbrev goalSpec0_3_32 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 0) 3))[32-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal0_3_32 : trunkGoalBranches (trunkCatalog.states 0) 3 32 = goalCodes0_3_32.map decodeGoalBranch := by
  have hi : (goalSpec0_3_32.first,goalSpec0_3_32.firstUpper,trunkSpecIncoming goalSpec0_3_32) = endpointInput0_51 := by decide +kernel
  have hj : (goalSpec0_3_32.second,goalSpec0_3_32.secondUpper,trunkSpecIncoming goalSpec0_3_32) = endpointInput0_1 := by decide +kernel
  have heL : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_3_32.first goalSpec0_3_32.firstUpper (trunkSpecIncoming goalSpec0_3_32) = endpointCodes0_51.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hi).trans hEndpoint0_51
  have heR : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_3_32.second goalSpec0_3_32.secondUpper (trunkSpecIncoming goalSpec0_3_32) = endpointCodes0_1.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hj).trans hEndpoint0_1
  have he : goalSpec0_3_32.extra = ([] : List (ℕ × Bool × Bool)).map decodeThresholdBound := by decide +kernel
  unfold trunkGoalBranches
  rw [if_neg (by decide)]
  unfold trunkBranches
  rw [heL,heR,he]
  decide +kernel

private abbrev goalSpec0_3_34 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 0) 3))[34-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal0_3_34 : trunkGoalBranches (trunkCatalog.states 0) 3 34 = goalCodes0_3_34.map decodeGoalBranch := by
  have hi : (goalSpec0_3_34.first,goalSpec0_3_34.firstUpper,trunkSpecIncoming goalSpec0_3_34) = endpointInput0_52 := by decide +kernel
  have hj : (goalSpec0_3_34.second,goalSpec0_3_34.secondUpper,trunkSpecIncoming goalSpec0_3_34) = endpointInput0_53 := by decide +kernel
  have heL : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_3_34.first goalSpec0_3_34.firstUpper (trunkSpecIncoming goalSpec0_3_34) = endpointCodes0_52.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hi).trans hEndpoint0_52
  have heR : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_3_34.second goalSpec0_3_34.secondUpper (trunkSpecIncoming goalSpec0_3_34) = endpointCodes0_53.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hj).trans hEndpoint0_53
  have he : goalSpec0_3_34.extra = ([] : List (ℕ × Bool × Bool)).map decodeThresholdBound := by decide +kernel
  unfold trunkGoalBranches
  rw [if_neg (by decide)]
  unfold trunkBranches
  rw [heL,heR,he]
  decide +kernel

private abbrev goalSpec0_3_35 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 0) 3))[35-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal0_3_35 : trunkGoalBranches (trunkCatalog.states 0) 3 35 = goalCodes0_3_35.map decodeGoalBranch := by
  have hi : (goalSpec0_3_35.first,goalSpec0_3_35.firstUpper,trunkSpecIncoming goalSpec0_3_35) = endpointInput0_52 := by decide +kernel
  have hj : (goalSpec0_3_35.second,goalSpec0_3_35.secondUpper,trunkSpecIncoming goalSpec0_3_35) = endpointInput0_54 := by decide +kernel
  have heL : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_3_35.first goalSpec0_3_35.firstUpper (trunkSpecIncoming goalSpec0_3_35) = endpointCodes0_52.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hi).trans hEndpoint0_52
  have heR : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_3_35.second goalSpec0_3_35.secondUpper (trunkSpecIncoming goalSpec0_3_35) = endpointCodes0_54.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hj).trans hEndpoint0_54
  have he : goalSpec0_3_35.extra = ([] : List (ℕ × Bool × Bool)).map decodeThresholdBound := by decide +kernel
  unfold trunkGoalBranches
  rw [if_neg (by decide)]
  unfold trunkBranches
  rw [heL,heR,he]
  decide +kernel

private abbrev goalSpec0_3_36 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 0) 3))[36-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal0_3_36 : trunkGoalBranches (trunkCatalog.states 0) 3 36 = goalCodes0_3_36.map decodeGoalBranch := by
  have hi : (goalSpec0_3_36.first,goalSpec0_3_36.firstUpper,trunkSpecIncoming goalSpec0_3_36) = endpointInput0_55 := by decide +kernel
  have hj : (goalSpec0_3_36.second,goalSpec0_3_36.secondUpper,trunkSpecIncoming goalSpec0_3_36) = endpointInput0_56 := by decide +kernel
  have heL : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_3_36.first goalSpec0_3_36.firstUpper (trunkSpecIncoming goalSpec0_3_36) = endpointCodes0_55.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hi).trans hEndpoint0_55
  have heR : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_3_36.second goalSpec0_3_36.secondUpper (trunkSpecIncoming goalSpec0_3_36) = endpointCodes0_56.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hj).trans hEndpoint0_56
  have he : goalSpec0_3_36.extra = ([] : List (ℕ × Bool × Bool)).map decodeThresholdBound := by decide +kernel
  unfold trunkGoalBranches
  rw [if_neg (by decide)]
  unfold trunkBranches
  rw [heL,heR,he]
  decide +kernel

private abbrev goalSpec0_3_38 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 0) 3))[38-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal0_3_38 : trunkGoalBranches (trunkCatalog.states 0) 3 38 = goalCodes0_3_38.map decodeGoalBranch := by
  have hi : (goalSpec0_3_38.first,goalSpec0_3_38.firstUpper,trunkSpecIncoming goalSpec0_3_38) = endpointInput0_57 := by decide +kernel
  have hj : (goalSpec0_3_38.second,goalSpec0_3_38.secondUpper,trunkSpecIncoming goalSpec0_3_38) = endpointInput0_54 := by decide +kernel
  have heL : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_3_38.first goalSpec0_3_38.firstUpper (trunkSpecIncoming goalSpec0_3_38) = endpointCodes0_57.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hi).trans hEndpoint0_57
  have heR : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_3_38.second goalSpec0_3_38.secondUpper (trunkSpecIncoming goalSpec0_3_38) = endpointCodes0_54.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hj).trans hEndpoint0_54
  have he : goalSpec0_3_38.extra = ([] : List (ℕ × Bool × Bool)).map decodeThresholdBound := by decide +kernel
  unfold trunkGoalBranches
  rw [if_neg (by decide)]
  unfold trunkBranches
  rw [heL,heR,he]
  decide +kernel

private abbrev goalSpec0_3_39 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 0) 3))[39-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal0_3_39 : trunkGoalBranches (trunkCatalog.states 0) 3 39 = goalCodes0_3_39.map decodeGoalBranch := by
  have hi : (goalSpec0_3_39.first,goalSpec0_3_39.firstUpper,trunkSpecIncoming goalSpec0_3_39) = endpointInput0_57 := by decide +kernel
  have hj : (goalSpec0_3_39.second,goalSpec0_3_39.secondUpper,trunkSpecIncoming goalSpec0_3_39) = endpointInput0_24 := by decide +kernel
  have heL : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_3_39.first goalSpec0_3_39.firstUpper (trunkSpecIncoming goalSpec0_3_39) = endpointCodes0_57.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hi).trans hEndpoint0_57
  have heR : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_3_39.second goalSpec0_3_39.secondUpper (trunkSpecIncoming goalSpec0_3_39) = endpointCodes0_24.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hj).trans hEndpoint0_24
  have he : goalSpec0_3_39.extra = ([] : List (ℕ × Bool × Bool)).map decodeThresholdBound := by decide +kernel
  unfold trunkGoalBranches
  rw [if_neg (by decide)]
  unfold trunkBranches
  rw [heL,heR,he]
  decide +kernel

private abbrev goalSpec0_3_40 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 0) 3))[40-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal0_3_40 : trunkGoalBranches (trunkCatalog.states 0) 3 40 = goalCodes0_3_40.map decodeGoalBranch := by
  have hi : (goalSpec0_3_40.first,goalSpec0_3_40.firstUpper,trunkSpecIncoming goalSpec0_3_40) = endpointInput0_22 := by decide +kernel
  have hj : (goalSpec0_3_40.second,goalSpec0_3_40.secondUpper,trunkSpecIncoming goalSpec0_3_40) = endpointInput0_58 := by decide +kernel
  have heL : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_3_40.first goalSpec0_3_40.firstUpper (trunkSpecIncoming goalSpec0_3_40) = endpointCodes0_22.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hi).trans hEndpoint0_22
  have heR : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_3_40.second goalSpec0_3_40.secondUpper (trunkSpecIncoming goalSpec0_3_40) = endpointCodes0_58.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hj).trans hEndpoint0_58
  have he : goalSpec0_3_40.extra = ([] : List (ℕ × Bool × Bool)).map decodeThresholdBound := by decide +kernel
  unfold trunkGoalBranches
  rw [if_neg (by decide)]
  unfold trunkBranches
  rw [heL,heR,he]
  decide +kernel

private abbrev goalSpec0_3_41 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 0) 3))[41-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal0_3_41 : trunkGoalBranches (trunkCatalog.states 0) 3 41 = goalCodes0_3_41.map decodeGoalBranch := by
  have hi : (goalSpec0_3_41.first,goalSpec0_3_41.firstUpper,trunkSpecIncoming goalSpec0_3_41) = endpointInput0_2 := by decide +kernel
  have hj : (goalSpec0_3_41.second,goalSpec0_3_41.secondUpper,trunkSpecIncoming goalSpec0_3_41) = endpointInput0_17 := by decide +kernel
  have heL : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_3_41.first goalSpec0_3_41.firstUpper (trunkSpecIncoming goalSpec0_3_41) = endpointCodes0_2.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hi).trans hEndpoint0_2
  have heR : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_3_41.second goalSpec0_3_41.secondUpper (trunkSpecIncoming goalSpec0_3_41) = endpointCodes0_17.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hj).trans hEndpoint0_17
  have he : goalSpec0_3_41.extra = ([] : List (ℕ × Bool × Bool)).map decodeThresholdBound := by decide +kernel
  unfold trunkGoalBranches
  rw [if_neg (by decide)]
  unfold trunkBranches
  rw [heL,heR,he]
  decide +kernel

private abbrev goalSpec0_3_42 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 0) 3))[42-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal0_3_42 : trunkGoalBranches (trunkCatalog.states 0) 3 42 = goalCodes0_3_42.map decodeGoalBranch := by
  have hi : (goalSpec0_3_42.first,goalSpec0_3_42.firstUpper,trunkSpecIncoming goalSpec0_3_42) = endpointInput0_23 := by decide +kernel
  have hj : (goalSpec0_3_42.second,goalSpec0_3_42.secondUpper,trunkSpecIncoming goalSpec0_3_42) = endpointInput0_24 := by decide +kernel
  have heL : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_3_42.first goalSpec0_3_42.firstUpper (trunkSpecIncoming goalSpec0_3_42) = endpointCodes0_23.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hi).trans hEndpoint0_23
  have heR : trunkEndpointCases (trunkCatalog.states 0).context goalSpec0_3_42.second goalSpec0_3_42.secondUpper (trunkSpecIncoming goalSpec0_3_42) = endpointCodes0_24.map decodeEndpoint0 :=
    (congrArg (fun z : LowerPair × Bool × Bool => trunkEndpointCases (trunkCatalog.states 0).context z.1 z.2.1 z.2.2) hj).trans hEndpoint0_24
  have he : goalSpec0_3_42.extra = ([] : List (ℕ × Bool × Bool)).map decodeThresholdBound := by decide +kernel
  unfold trunkGoalBranches
  rw [if_neg (by decide)]
  unfold trunkBranches
  rw [heL,heR,he]
  decide +kernel

private theorem hGoal0_4_0 : trunkGoalBranches (trunkCatalog.states 0) 4 0 = goalCodes0_4_0.map decodeGoalBranch := by
  exact hGoal0_2_0

private theorem hCut0_2 : (trunkPlanAt (trunkCatalog.states 0) 2).cuts = cutCodes0_2.map decodeThresholdBound := by decide +kernel

private theorem hCut0_3 : (trunkPlanAt (trunkCatalog.states 0) 3).cuts = cutCodes0_3.map decodeThresholdBound := by decide +kernel

private theorem hCut0_4 : (trunkPlanAt (trunkCatalog.states 0) 4).cuts = cutCodes0_4.map decodeThresholdBound := by decide +kernel

private def codedGoals0 (pi goal : ℕ) : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) :=
  if pi = 2 ∧ goal = 0 then goalCodes0_2_0 else
  if pi = 2 ∧ goal = 5 then goalCodes0_2_5 else
  if pi = 2 ∧ goal = 10 then goalCodes0_2_10 else
  if pi = 2 ∧ goal = 12 then goalCodes0_2_12 else
  if pi = 2 ∧ goal = 14 then goalCodes0_2_14 else
  if pi = 2 ∧ goal = 18 then goalCodes0_2_18 else
  if pi = 2 ∧ goal = 20 then goalCodes0_2_20 else
  if pi = 2 ∧ goal = 22 then goalCodes0_2_22 else
  if pi = 2 ∧ goal = 24 then goalCodes0_2_24 else
  if pi = 2 ∧ goal = 27 then goalCodes0_2_27 else
  if pi = 2 ∧ goal = 29 then goalCodes0_2_29 else
  if pi = 2 ∧ goal = 31 then goalCodes0_2_31 else
  if pi = 3 ∧ goal = 0 then goalCodes0_3_0 else
  if pi = 3 ∧ goal = 2 then goalCodes0_3_2 else
  if pi = 3 ∧ goal = 5 then goalCodes0_3_5 else
  if pi = 3 ∧ goal = 7 then goalCodes0_3_7 else
  if pi = 3 ∧ goal = 9 then goalCodes0_3_9 else
  if pi = 3 ∧ goal = 12 then goalCodes0_3_12 else
  if pi = 3 ∧ goal = 14 then goalCodes0_3_14 else
  if pi = 3 ∧ goal = 17 then goalCodes0_3_17 else
  if pi = 3 ∧ goal = 19 then goalCodes0_3_19 else
  if pi = 3 ∧ goal = 22 then goalCodes0_3_22 else
  if pi = 3 ∧ goal = 24 then goalCodes0_3_24 else
  if pi = 3 ∧ goal = 27 then goalCodes0_3_27 else
  if pi = 3 ∧ goal = 29 then goalCodes0_3_29 else
  if pi = 3 ∧ goal = 32 then goalCodes0_3_32 else
  if pi = 3 ∧ goal = 34 then goalCodes0_3_34 else
  if pi = 3 ∧ goal = 35 then goalCodes0_3_35 else
  if pi = 3 ∧ goal = 36 then goalCodes0_3_36 else
  if pi = 3 ∧ goal = 38 then goalCodes0_3_38 else
  if pi = 3 ∧ goal = 39 then goalCodes0_3_39 else
  if pi = 3 ∧ goal = 40 then goalCodes0_3_40 else
  if pi = 3 ∧ goal = 41 then goalCodes0_3_41 else
  if pi = 3 ∧ goal = 42 then goalCodes0_3_42 else
  if pi = 4 ∧ goal = 0 then goalCodes0_4_0 else
  []

private def codedKeys0 : List (ℕ × ℕ) := [(2, 0), (2, 5), (2, 10), (2, 12), (2, 14), (2, 18), (2, 20), (2, 22), (2, 24), (2, 27), (2, 29), (2, 31), (3, 0), (3, 2), (3, 5), (3, 7), (3, 9), (3, 12), (3, 14), (3, 17), (3, 19), (3, 22), (3, 24), (3, 27), (3, 29), (3, 32), (3, 34), (3, 35), (3, 36), (3, 38), (3, 39), (3, 40), (3, 41), (3, 42), (4, 0)]

private theorem hCodedGoals0 (pi goal : ℕ) (hm : (pi,goal) ∈ codedKeys0) : trunkGoalBranches (trunkCatalog.states 0) pi goal = (codedGoals0 pi goal).map decodeGoalBranch := by
  unfold codedGoals0
  by_cases h0 : pi = 2 ∧ goal = 0
  · rw [if_pos h0]
    rcases h0 with ⟨rfl,rfl⟩
    exact hGoal0_2_0
  rw [if_neg h0]
  by_cases h1 : pi = 2 ∧ goal = 5
  · rw [if_pos h1]
    rcases h1 with ⟨rfl,rfl⟩
    exact hGoal0_2_5
  rw [if_neg h1]
  by_cases h2 : pi = 2 ∧ goal = 10
  · rw [if_pos h2]
    rcases h2 with ⟨rfl,rfl⟩
    exact hGoal0_2_10
  rw [if_neg h2]
  by_cases h3 : pi = 2 ∧ goal = 12
  · rw [if_pos h3]
    rcases h3 with ⟨rfl,rfl⟩
    exact hGoal0_2_12
  rw [if_neg h3]
  by_cases h4 : pi = 2 ∧ goal = 14
  · rw [if_pos h4]
    rcases h4 with ⟨rfl,rfl⟩
    exact hGoal0_2_14
  rw [if_neg h4]
  by_cases h5 : pi = 2 ∧ goal = 18
  · rw [if_pos h5]
    rcases h5 with ⟨rfl,rfl⟩
    exact hGoal0_2_18
  rw [if_neg h5]
  by_cases h6 : pi = 2 ∧ goal = 20
  · rw [if_pos h6]
    rcases h6 with ⟨rfl,rfl⟩
    exact hGoal0_2_20
  rw [if_neg h6]
  by_cases h7 : pi = 2 ∧ goal = 22
  · rw [if_pos h7]
    rcases h7 with ⟨rfl,rfl⟩
    exact hGoal0_2_22
  rw [if_neg h7]
  by_cases h8 : pi = 2 ∧ goal = 24
  · rw [if_pos h8]
    rcases h8 with ⟨rfl,rfl⟩
    exact hGoal0_2_24
  rw [if_neg h8]
  by_cases h9 : pi = 2 ∧ goal = 27
  · rw [if_pos h9]
    rcases h9 with ⟨rfl,rfl⟩
    exact hGoal0_2_27
  rw [if_neg h9]
  by_cases h10 : pi = 2 ∧ goal = 29
  · rw [if_pos h10]
    rcases h10 with ⟨rfl,rfl⟩
    exact hGoal0_2_29
  rw [if_neg h10]
  by_cases h11 : pi = 2 ∧ goal = 31
  · rw [if_pos h11]
    rcases h11 with ⟨rfl,rfl⟩
    exact hGoal0_2_31
  rw [if_neg h11]
  by_cases h12 : pi = 3 ∧ goal = 0
  · rw [if_pos h12]
    rcases h12 with ⟨rfl,rfl⟩
    exact hGoal0_3_0
  rw [if_neg h12]
  by_cases h13 : pi = 3 ∧ goal = 2
  · rw [if_pos h13]
    rcases h13 with ⟨rfl,rfl⟩
    exact hGoal0_3_2
  rw [if_neg h13]
  by_cases h14 : pi = 3 ∧ goal = 5
  · rw [if_pos h14]
    rcases h14 with ⟨rfl,rfl⟩
    exact hGoal0_3_5
  rw [if_neg h14]
  by_cases h15 : pi = 3 ∧ goal = 7
  · rw [if_pos h15]
    rcases h15 with ⟨rfl,rfl⟩
    exact hGoal0_3_7
  rw [if_neg h15]
  by_cases h16 : pi = 3 ∧ goal = 9
  · rw [if_pos h16]
    rcases h16 with ⟨rfl,rfl⟩
    exact hGoal0_3_9
  rw [if_neg h16]
  by_cases h17 : pi = 3 ∧ goal = 12
  · rw [if_pos h17]
    rcases h17 with ⟨rfl,rfl⟩
    exact hGoal0_3_12
  rw [if_neg h17]
  by_cases h18 : pi = 3 ∧ goal = 14
  · rw [if_pos h18]
    rcases h18 with ⟨rfl,rfl⟩
    exact hGoal0_3_14
  rw [if_neg h18]
  by_cases h19 : pi = 3 ∧ goal = 17
  · rw [if_pos h19]
    rcases h19 with ⟨rfl,rfl⟩
    exact hGoal0_3_17
  rw [if_neg h19]
  by_cases h20 : pi = 3 ∧ goal = 19
  · rw [if_pos h20]
    rcases h20 with ⟨rfl,rfl⟩
    exact hGoal0_3_19
  rw [if_neg h20]
  by_cases h21 : pi = 3 ∧ goal = 22
  · rw [if_pos h21]
    rcases h21 with ⟨rfl,rfl⟩
    exact hGoal0_3_22
  rw [if_neg h21]
  by_cases h22 : pi = 3 ∧ goal = 24
  · rw [if_pos h22]
    rcases h22 with ⟨rfl,rfl⟩
    exact hGoal0_3_24
  rw [if_neg h22]
  by_cases h23 : pi = 3 ∧ goal = 27
  · rw [if_pos h23]
    rcases h23 with ⟨rfl,rfl⟩
    exact hGoal0_3_27
  rw [if_neg h23]
  by_cases h24 : pi = 3 ∧ goal = 29
  · rw [if_pos h24]
    rcases h24 with ⟨rfl,rfl⟩
    exact hGoal0_3_29
  rw [if_neg h24]
  by_cases h25 : pi = 3 ∧ goal = 32
  · rw [if_pos h25]
    rcases h25 with ⟨rfl,rfl⟩
    exact hGoal0_3_32
  rw [if_neg h25]
  by_cases h26 : pi = 3 ∧ goal = 34
  · rw [if_pos h26]
    rcases h26 with ⟨rfl,rfl⟩
    exact hGoal0_3_34
  rw [if_neg h26]
  by_cases h27 : pi = 3 ∧ goal = 35
  · rw [if_pos h27]
    rcases h27 with ⟨rfl,rfl⟩
    exact hGoal0_3_35
  rw [if_neg h27]
  by_cases h28 : pi = 3 ∧ goal = 36
  · rw [if_pos h28]
    rcases h28 with ⟨rfl,rfl⟩
    exact hGoal0_3_36
  rw [if_neg h28]
  by_cases h29 : pi = 3 ∧ goal = 38
  · rw [if_pos h29]
    rcases h29 with ⟨rfl,rfl⟩
    exact hGoal0_3_38
  rw [if_neg h29]
  by_cases h30 : pi = 3 ∧ goal = 39
  · rw [if_pos h30]
    rcases h30 with ⟨rfl,rfl⟩
    exact hGoal0_3_39
  rw [if_neg h30]
  by_cases h31 : pi = 3 ∧ goal = 40
  · rw [if_pos h31]
    rcases h31 with ⟨rfl,rfl⟩
    exact hGoal0_3_40
  rw [if_neg h31]
  by_cases h32 : pi = 3 ∧ goal = 41
  · rw [if_pos h32]
    rcases h32 with ⟨rfl,rfl⟩
    exact hGoal0_3_41
  rw [if_neg h32]
  by_cases h33 : pi = 3 ∧ goal = 42
  · rw [if_pos h33]
    rcases h33 with ⟨rfl,rfl⟩
    exact hGoal0_3_42
  rw [if_neg h33]
  by_cases h34 : pi = 4 ∧ goal = 0
  · rw [if_pos h34]
    rcases h34 with ⟨rfl,rfl⟩
    exact hGoal0_4_0
  rw [if_neg h34]
  simp_all only [codedKeys0,List.mem_cons,List.mem_nil_iff,or_false,Prod.mk.injEq]

private def codedCuts0 (pi : ℕ) : List (ℕ × Bool × Bool) :=
  if pi = 2 then cutCodes0_2 else
  if pi = 3 then cutCodes0_3 else
  if pi = 4 then cutCodes0_4 else
  []

private theorem hCodedCuts0 (pi goal : ℕ) (hm : (pi,goal) ∈ codedKeys0) : (trunkPlanAt (trunkCatalog.states 0) pi).cuts = (codedCuts0 pi).map decodeThresholdBound := by
  unfold codedCuts0
  by_cases h0 : pi = 2
  · rw [if_pos h0]
    subst pi
    exact hCut0_2
  rw [if_neg h0]
  by_cases h1 : pi = 3
  · rw [if_pos h1]
    subst pi
    exact hCut0_3
  rw [if_neg h1]
  by_cases h2 : pi = 4
  · rw [if_pos h2]
    subst pi
    exact hCut0_4
  rw [if_neg h2]
  simp_all only [codedKeys0,List.mem_cons,List.mem_nil_iff,or_false,Prod.mk.injEq,false_and]

private def codedValid0 (g : TrunkGroup) : Prop := (g.plan,g.goal) ∈ codedKeys0 ∧ codeGroupValid (trunkCatalog.states 0) codedParents0 625 codedCuts0 codedGoals0 g

private theorem codedValid0_sound (g : TrunkGroup) (h : codedValid0 g) : trunkGroupValidFast 0 g :=
  codeGroupValid_sound 0 codedParents0 625 codedCuts0 codedGoals0 g hCodedParents0 hCodedParentLength0 (hCodedCuts0 g.plan g.goal h.1) (hCodedGoals0 g.plan g.goal h.1) h.2



set_option Elab.async false
theorem batch_chunk_0 : ∀ j ∈ List.range 20, codedValid0 (trunkStateData00Part03.getD j ⟨0,[],0,[]⟩) := by
  unfold codedValid0 codeGroupValid
  decide +kernel

theorem batch_chunk_20 : ∀ j ∈ List.range' 20 20, codedValid0 (trunkStateData00Part03.getD j ⟨0,[],0,[]⟩) := by
  unfold codedValid0 codeGroupValid
  decide +kernel

theorem batch_chunk_40 : ∀ j ∈ List.range' 40 20, codedValid0 (trunkStateData00Part03.getD j ⟨0,[],0,[]⟩) := by
  unfold codedValid0 codeGroupValid
  decide +kernel

theorem batch_chunk_60 : ∀ j ∈ List.range' 60 20, codedValid0 (trunkStateData00Part03.getD j ⟨0,[],0,[]⟩) := by
  unfold codedValid0 codeGroupValid
  decide +kernel

theorem batch_chunk_80 : ∀ j ∈ List.range' 80 20, codedValid0 (trunkStateData00Part03.getD j ⟨0,[],0,[]⟩) := by
  unfold codedValid0 codeGroupValid
  decide +kernel

theorem batch_key (j : ℕ) (hj : j < 100) : codedValid0 (trunkStateData00Part03.getD j ⟨0,[],0,[]⟩) := by
  rcases lt_or_ge j 20 with h0 | h0
  · exact batch_chunk_0 j (List.mem_range.2 (by omega))
  rcases lt_or_ge j 40 with h1 | h1
  · exact batch_chunk_20 j (List.mem_range'.2 ⟨j - 20, by omega, by omega⟩)
  rcases lt_or_ge j 60 with h2 | h2
  · exact batch_chunk_40 j (List.mem_range'.2 ⟨j - 40, by omega, by omega⟩)
  rcases lt_or_ge j 80 with h3 | h3
  · exact batch_chunk_60 j (List.mem_range'.2 ⟨j - 60, by omega, by omega⟩)
  · exact batch_chunk_80 j (List.mem_range'.2 ⟨j - 80, by omega, by omega⟩)

theorem part_length_1 : trunkStateData00Part01.length = 100 := by decide +kernel

theorem part_length_2 : trunkStateData00Part02.length = 100 := by decide +kernel

theorem part_length_3 : trunkStateData00Part03.length = 100 := by decide +kernel

theorem part_length_4 : trunkStateData00Part04.length = 100 := by decide +kernel

theorem solution : trunkBindingBatch 0 200 300 := by
  intro i hlo hhi g hg
  change (trunkStateData00Part01 ++ trunkStateData00Part02 ++ trunkStateData00Part03 ++ trunkStateData00Part04 ++ trunkStateData00Part05)[i]? = some g at hg
  rw [List.getElem?_append_left (show i < (trunkStateData00Part01 ++ trunkStateData00Part02 ++ trunkStateData00Part03 ++ trunkStateData00Part04).length by simp only [List.length_append, part_length_1, part_length_2, part_length_3, part_length_4, Nat.reduceAdd]; omega)] at hg
  rw [List.getElem?_append_left (show i < (trunkStateData00Part01 ++ trunkStateData00Part02 ++ trunkStateData00Part03).length by simp only [List.length_append, part_length_1, part_length_2, part_length_3, part_length_4, Nat.reduceAdd]; omega)] at hg
  rw [List.getElem?_append_right (show (trunkStateData00Part01 ++ trunkStateData00Part02).length ≤ i by simp only [List.length_append, part_length_1, part_length_2, part_length_3, part_length_4, Nat.reduceAdd]; omega)] at hg
  simp only [List.length_append, part_length_1, part_length_2, part_length_3, part_length_4, Nat.reduceAdd] at hg
  have hgi := batch_key (i - 200) (by omega)
  have hgv : trunkStateData00Part03.getD (i - 200) ⟨0,[],0,[]⟩ = g := by
    try simp only [Nat.sub_zero]
    rw [List.getD_eq_getElem?_getD, hg]; rfl
  rw [hgv] at hgi
  exact Freiman.trunkFast_correctness.2 0 hPar0 g (codedValid0_sound g hgi)

#print axioms solution
