-- Prove2me | solution 1 for Freiman.trunk_bindings_09_200_260
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:34:01.4514+00:00
-- url     : https://prove2.me/submissions/5d5a3278-39d3-4580-a4a3-1a66009498f5

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
private abbrev bc34 : ℕ × Bool × Bool := (183, false, false)
private abbrev bc35 : ℕ × Bool × Bool := (182, false, false)
private abbrev bc36 : ℕ × Bool × Bool := (179, false, true)
private abbrev bc37 : ℕ × Bool × Bool := (179, true, false)
private abbrev bc38 : ℕ × Bool × Bool := (182, true, true)
private abbrev bc39 : ℕ × Bool × Bool := (197, true, true)
private abbrev bc40 : ℕ × Bool × Bool := (197, false, false)
private abbrev bc41 : ℕ × Bool × Bool := (183, true, true)
private abbrev bc42 : ℕ × Bool × Bool := (181, false, false)
private abbrev bc43 : ℕ × Bool × Bool := (181, true, true)
private abbrev bc44 : ℕ × Bool × Bool := (184, false, false)
private abbrev bc45 : ℕ × Bool × Bool := (186, false, true)
private abbrev bc46 : ℕ × Bool × Bool := (186, true, false)
private abbrev bc47 : ℕ × Bool × Bool := (184, true, true)
private abbrev bc48 : ℕ × Bool × Bool := (189, true, true)
private abbrev bc49 : ℕ × Bool × Bool := (189, false, false)
private abbrev bc50 : ℕ × Bool × Bool := (206, true, false)
private abbrev bc51 : ℕ × Bool × Bool := (210, false, true)
private abbrev bc52 : ℕ × Bool × Bool := (210, true, false)
private abbrev bc53 : ℕ × Bool × Bool := (205, false, true)
private abbrev bc54 : ℕ × Bool × Bool := (205, true, false)
private abbrev bc55 : ℕ × Bool × Bool := (132, false, false)
private abbrev bc56 : ℕ × Bool × Bool := (133, false, true)
private abbrev bc57 : ℕ × Bool × Bool := (133, true, false)
private abbrev bc58 : ℕ × Bool × Bool := (132, true, true)
private abbrev bc59 : ℕ × Bool × Bool := (136, true, true)
private abbrev bc60 : ℕ × Bool × Bool := (136, false, false)
private abbrev bc61 : ℕ × Bool × Bool := (8, false, false)
private abbrev bc62 : ℕ × Bool × Bool := (176, false, true)
private abbrev bc63 : ℕ × Bool × Bool := (8, true, true)
private abbrev bc64 : ℕ × Bool × Bool := (246, false, true)
private abbrev bc65 : ℕ × Bool × Bool := (246, true, false)
private abbrev bc66 : ℕ × Bool × Bool := (248, true, false)
private abbrev bc67 : ℕ × Bool × Bool := (251, false, true)
private abbrev bc68 : ℕ × Bool × Bool := (251, true, false)
private abbrev bc69 : ℕ × Bool × Bool := (260, false, false)
private abbrev bc70 : ℕ × Bool × Bool := (261, false, false)
private abbrev bc71 : ℕ × Bool × Bool := (261, true, true)
private abbrev bc72 : ℕ × Bool × Bool := (263, false, false)
private abbrev bc73 : ℕ × Bool × Bool := (263, true, true)
private abbrev bc74 : ℕ × Bool × Bool := (275, true, false)
private abbrev bc75 : ℕ × Bool × Bool := (279, false, true)
private abbrev bc76 : ℕ × Bool × Bool := (279, true, false)
private abbrev bc77 : ℕ × Bool × Bool := (274, false, true)
private abbrev bc78 : ℕ × Bool × Bool := (274, true, false)
private abbrev bc79 : ℕ × Bool × Bool := (235, false, false)
private abbrev bc80 : ℕ × Bool × Bool := (288, false, true)
private abbrev bc81 : ℕ × Bool × Bool := (288, true, false)
private abbrev bc82 : ℕ × Bool × Bool := (235, true, true)
private abbrev bc83 : ℕ × Bool × Bool := (291, true, true)
private abbrev bc84 : ℕ × Bool × Bool := (291, false, false)
private abbrev bc85 : ℕ × Bool × Bool := (297, false, false)
private abbrev bc86 : ℕ × Bool × Bool := (298, false, false)
private abbrev bc87 : ℕ × Bool × Bool := (69, false, true)
private abbrev bc88 : ℕ × Bool × Bool := (69, true, false)
private abbrev bc89 : ℕ × Bool × Bool := (298, true, true)
private abbrev bc90 : ℕ × Bool × Bool := (83, true, true)
private abbrev bc91 : ℕ × Bool × Bool := (83, false, false)
private abbrev bc92 : ℕ × Bool × Bool := (297, true, true)
private abbrev bc93 : ℕ × Bool × Bool := (299, false, false)
private abbrev bc94 : ℕ × Bool × Bool := (299, true, true)
private abbrev bc95 : ℕ × Bool × Bool := (301, false, false)
private abbrev bc96 : ℕ × Bool × Bool := (303, false, true)
private abbrev bc97 : ℕ × Bool × Bool := (303, true, false)
private abbrev bc98 : ℕ × Bool × Bool := (301, true, true)
private abbrev bc99 : ℕ × Bool × Bool := (307, true, true)
private abbrev bc100 : ℕ × Bool × Bool := (307, false, false)
private abbrev bc101 : ℕ × Bool × Bool := (319, false, true)
private abbrev bc102 : ℕ × Bool × Bool := (319, true, false)
private abbrev bc103 : ℕ × Bool × Bool := (331, false, true)
private abbrev bc104 : ℕ × Bool × Bool := (332, false, true)
private abbrev bc105 : ℕ × Bool × Bool := (332, true, false)
private abbrev bc106 : ℕ × Bool × Bool := (331, true, false)
private abbrev bc107 : ℕ × Bool × Bool := (337, true, true)
private abbrev bc108 : ℕ × Bool × Bool := (337, false, false)
private abbrev bc109 : ℕ × Bool × Bool := (320, false, true)
private abbrev bc110 : ℕ × Bool × Bool := (322, false, true)
private abbrev bc111 : ℕ × Bool × Bool := (321, false, true)
private abbrev bc112 : ℕ × Bool × Bool := (321, true, false)
private abbrev bc113 : ℕ × Bool × Bool := (322, true, false)
private abbrev bc114 : ℕ × Bool × Bool := (325, true, true)
private abbrev bc115 : ℕ × Bool × Bool := (325, false, false)
private abbrev bc116 : ℕ × Bool × Bool := (320, true, false)
private abbrev bc117 : ℕ × Bool × Bool := (380, false, false)
private abbrev bc118 : ℕ × Bool × Bool := (379, false, false)
private abbrev bc119 : ℕ × Bool × Bool := (377, false, true)
private abbrev bc120 : ℕ × Bool × Bool := (377, true, false)
private abbrev bc121 : ℕ × Bool × Bool := (379, true, true)
private abbrev bc122 : ℕ × Bool × Bool := (395, true, true)
private abbrev bc123 : ℕ × Bool × Bool := (395, false, false)
private abbrev bc124 : ℕ × Bool × Bool := (380, true, true)
private abbrev bc125 : ℕ × Bool × Bool := (381, false, false)
private abbrev bc126 : ℕ × Bool × Bool := (381, true, true)
private abbrev bc127 : ℕ × Bool × Bool := (384, false, false)
private abbrev bc128 : ℕ × Bool × Bool := (383, false, true)
private abbrev bc129 : ℕ × Bool × Bool := (383, true, false)
private abbrev bc130 : ℕ × Bool × Bool := (384, true, true)
private abbrev bc131 : ℕ × Bool × Bool := (388, true, true)
private abbrev bc132 : ℕ × Bool × Bool := (388, false, false)
private abbrev bc133 : ℕ × Bool × Bool := (405, false, true)
private abbrev bc134 : ℕ × Bool × Bool := (405, true, false)
private abbrev bc135 : ℕ × Bool × Bool := (415, false, true)
private abbrev bc136 : ℕ × Bool × Bool := (414, false, true)
private abbrev bc137 : ℕ × Bool × Bool := (414, true, false)
private abbrev bc138 : ℕ × Bool × Bool := (415, true, false)
private abbrev bc139 : ℕ × Bool × Bool := (421, true, true)
private abbrev bc140 : ℕ × Bool × Bool := (421, false, false)
private abbrev bc141 : ℕ × Bool × Bool := (404, false, true)
private abbrev bc142 : ℕ × Bool × Bool := (406, false, true)
private abbrev bc143 : ℕ × Bool × Bool := (403, false, true)
private abbrev bc144 : ℕ × Bool × Bool := (403, true, false)
private abbrev bc145 : ℕ × Bool × Bool := (406, true, false)
private abbrev bc146 : ℕ × Bool × Bool := (409, true, true)
private abbrev bc147 : ℕ × Bool × Bool := (409, false, false)
private abbrev bc148 : ℕ × Bool × Bool := (404, true, false)
private abbrev bc149 : ℕ × Bool × Bool := (432, false, false)
private abbrev bc150 : ℕ × Bool × Bool := (430, false, false)
private abbrev bc151 : ℕ × Bool × Bool := (430, true, true)
private abbrev bc152 : ℕ × Bool × Bool := (428, false, false)
private abbrev bc153 : ℕ × Bool × Bool := (428, true, true)
private abbrev bc154 : ℕ × Bool × Bool := (443, false, true)
private abbrev bc155 : ℕ × Bool × Bool := (443, true, false)
private abbrev bc156 : ℕ × Bool × Bool := (455, false, true)
private abbrev bc157 : ℕ × Bool × Bool := (456, false, true)
private abbrev bc158 : ℕ × Bool × Bool := (456, true, false)
private abbrev bc159 : ℕ × Bool × Bool := (455, true, false)
private abbrev bc160 : ℕ × Bool × Bool := (461, true, true)
private abbrev bc161 : ℕ × Bool × Bool := (461, false, false)
private abbrev bc162 : ℕ × Bool × Bool := (446, false, true)
private abbrev bc163 : ℕ × Bool × Bool := (445, false, true)
private abbrev bc164 : ℕ × Bool × Bool := (444, false, true)
private abbrev bc165 : ℕ × Bool × Bool := (444, true, false)
private abbrev bc166 : ℕ × Bool × Bool := (445, true, false)
private abbrev bc167 : ℕ × Bool × Bool := (449, true, true)
private abbrev bc168 : ℕ × Bool × Bool := (449, false, false)
private abbrev bc169 : ℕ × Bool × Bool := (446, true, false)
private abbrev bc170 : ℕ × Bool × Bool := (156, false, false)
private abbrev bc171 : ℕ × Bool × Bool := (155, false, true)
private abbrev bc172 : ℕ × Bool × Bool := (155, true, false)
private abbrev bc173 : ℕ × Bool × Bool := (156, true, true)
private abbrev bc174 : ℕ × Bool × Bool := (162, true, true)
private abbrev bc175 : ℕ × Bool × Bool := (162, false, false)
private abbrev bc176 : ℕ × Bool × Bool := (90, false, true)
private abbrev bc177 : ℕ × Bool × Bool := (90, true, false)
private abbrev bc178 : ℕ × Bool × Bool := (95, true, true)
private abbrev bc179 : ℕ × Bool × Bool := (95, false, false)
private abbrev bc180 : ℕ × Bool × Bool := (89, false, false)
private abbrev bc181 : ℕ × Bool × Bool := (476, false, true)
private abbrev bc182 : ℕ × Bool × Bool := (476, true, false)
private abbrev bc183 : ℕ × Bool × Bool := (89, true, true)
private abbrev bc184 : ℕ × Bool × Bool := (479, true, true)
private abbrev bc185 : ℕ × Bool × Bool := (479, false, false)
private abbrev bc186 : ℕ × Bool × Bool := (91, false, true)
private abbrev bc187 : ℕ × Bool × Bool := (91, true, false)
private abbrev bc188 : ℕ × Bool × Bool := (102, true, true)
private abbrev bc189 : ℕ × Bool × Bool := (102, false, false)
private abbrev bc190 : ℕ × Bool × Bool := (431, false, false)
private abbrev bc191 : ℕ × Bool × Bool := (490, false, true)
private abbrev bc192 : ℕ × Bool × Bool := (490, true, false)
private abbrev bc193 : ℕ × Bool × Bool := (431, true, true)
private abbrev bc194 : ℕ × Bool × Bool := (497, true, true)
private abbrev bc195 : ℕ × Bool × Bool := (497, false, false)
private abbrev bc196 : ℕ × Bool × Bool := (511, false, false)
private abbrev bc197 : ℕ × Bool × Bool := (510, false, true)
private abbrev bc198 : ℕ × Bool × Bool := (510, true, false)
private abbrev bc199 : ℕ × Bool × Bool := (511, true, true)
private abbrev bc200 : ℕ × Bool × Bool := (519, true, true)
private abbrev bc201 : ℕ × Bool × Bool := (519, false, false)
private abbrev bc202 : ℕ × Bool × Bool := (347, false, false)
private abbrev bc203 : ℕ × Bool × Bool := (349, false, true)
private abbrev bc204 : ℕ × Bool × Bool := (349, true, false)
private abbrev bc205 : ℕ × Bool × Bool := (347, true, true)
private abbrev bc206 : ℕ × Bool × Bool := (352, true, true)
private abbrev bc207 : ℕ × Bool × Bool := (352, false, false)
private abbrev bc208 : ℕ × Bool × Bool := (525, false, true)
private abbrev bc209 : ℕ × Bool × Bool := (525, true, false)
private abbrev bc210 : ℕ × Bool × Bool := (365, false, false)
private abbrev bc211 : ℕ × Bool × Bool := (365, true, true)
private abbrev bc212 : ℕ × Bool × Bool := (369, false, false)
private abbrev bc213 : ℕ × Bool × Bool := (370, false, true)
private abbrev bc214 : ℕ × Bool × Bool := (370, true, false)
private abbrev bc215 : ℕ × Bool × Bool := (369, true, true)
private abbrev bc216 : ℕ × Bool × Bool := (373, true, true)
private abbrev bc217 : ℕ × Bool × Bool := (373, false, false)
private abbrev bc218 : ℕ × Bool × Bool := (1, true, false)
private abbrev bc219 : ℕ × Bool × Bool := (23, true, false)
private abbrev bc220 : ℕ × Bool × Bool := (27, true, false)
private abbrev bc221 : ℕ × Bool × Bool := (143, true, false)
private abbrev bc222 : ℕ × Bool × Bool := (148, true, false)
private abbrev bc223 : ℕ × Bool × Bool := (245, false, true)
private abbrev bc224 : ℕ × Bool × Bool := (262, false, false)
private abbrev bc225 : ℕ × Bool × Bool := (264, true, true)
private abbrev bc226 : ℕ × Bool × Bool := (262, true, true)
private abbrev bc227 : ℕ × Bool × Bool := (273, false, true)
private abbrev bc228 : ℕ × Bool × Bool := (467, true, false)
private abbrev bc229 : ℕ × Bool × Bool := (153, true, false)
private abbrev bc230 : ℕ × Bool × Bool := (486, false, false)
private abbrev bc231 : ℕ × Bool × Bool := (489, false, false)
private abbrev bc232 : ℕ × Bool × Bool := (34, true, true)
private abbrev bc233 : ℕ × Bool × Bool := (300, true, true)
private abbrev bc234 : ℕ × Bool × Bool := (318, false, true)
private abbrev bc235 : ℕ × Bool × Bool := (509, true, true)
private abbrev bc236 : ℕ × Bool × Bool := (378, true, true)
private abbrev bc237 : ℕ × Bool × Bool := (402, false, true)
private abbrev bc238 : ℕ × Bool × Bool := (429, true, true)
private abbrev bc239 : ℕ × Bool × Bool := (441, false, true)
private abbrev bc240 : ℕ × Bool × Bool := (180, true, true)
private abbrev bc241 : ℕ × Bool × Bool := (204, false, true)
private abbrev bc242 : ℕ × Bool × Bool := (533, true, false)
private abbrev bc243 : ℕ × Bool × Bool := (542, true, false)

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
private abbrev endpointInput9_17 : LowerPair × Bool × Bool := (([3, 1], [2]), true, false)
private def endpointCodes9_17 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((17, 0), [bc34, bc35, bc36]),
 ((17, 3), [bc34, bc35, bc37]),
 ((17, 0), [bc34, bc38, bc39]),
 ((18, 0), [bc34, bc38, bc40]),
 ((17, 0), [bc41])]
private abbrev endpointInput9_18 : LowerPair × Bool × Bool := (([3, 2], [2]), false, false)
private def endpointCodes9_18 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((19, 6), [bc42]),
 ((19, 6), [bc43, bc44, bc45]),
 ((19, 8), [bc43, bc44, bc46]),
 ((19, 6), [bc43, bc47, bc48]),
 ((20, 6), [bc43, bc47, bc49])]
private abbrev endpointInput9_19 : LowerPair × Bool × Bool := (([3], [2, 1]), true, true)
private def endpointCodes9_19 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((21, 13), [(206, false, true)]),
 ((21, 13), [bc50, bc51, (208, false, true)]),
 ((21, 14), [bc50, bc51, (208, true, false)]),
 ((21, 13), [bc50, bc52, (213, true, true)]),
 ((22, 13), [bc50, bc52, (213, false, false)])]
private abbrev endpointInput9_20 : LowerPair × Bool × Bool := (([3], [2, 2]), false, true)
private def endpointCodes9_20 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((23, 15), [bc53]), ((23, 15), [bc54])]
private abbrev endpointInput9_21 : LowerPair × Bool × Bool := (([3], [2]), true, false)
private def endpointCodes9_21 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((21, 0), [bc55, bc56]),
 ((21, 3), [bc55, bc57]),
 ((21, 0), [bc58, bc59]),
 ((22, 0), [bc58, bc60])]
private abbrev endpointInput9_22 : LowerPair × Bool × Bool := (([], []), false, false)
private def endpointCodes9_22 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((5, 5), [bc61, bc62]),
 ((5, 6), [bc61, (176, true, false)]),
 ((5, 5), [bc63, (228, true, true)]),
 ((6, 5), [bc63, (228, false, false)])]
private abbrev endpointInput9_23 : LowerPair × Bool × Bool := (([3], [2]), false, false)
private def endpointCodes9_23 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((23, 6), [])]
private abbrev endpointInput9_26 : LowerPair × Bool × Bool := (([3, 3], [3, 3, 2]), true, true)
private def endpointCodes9_26 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((25, 24), [bc64]), ((25, 24), [bc65])]
private abbrev endpointInput9_27 : LowerPair × Bool × Bool := (([3, 3], [3, 3, 1]), false, true)
private def endpointCodes9_27 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((27, 26), [(248, false, true)]),
 ((27, 26), [bc66, bc67, (249, false, true)]),
 ((27, 29), [bc66, bc67, (249, true, false)]),
 ((27, 26), [bc66, bc68, (254, true, true)]),
 ((28, 26), [bc66, bc68, (254, false, false)])]
private abbrev endpointInput9_28 : LowerPair × Bool × Bool := (([3, 1], [3]), true, false)
private def endpointCodes9_28 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((17, 21), [bc69, bc70, (259, false, true)]),
 ((17, 22), [bc69, bc70, (259, true, false)]),
 ((17, 21), [bc69, bc71, (269, true, true)]),
 ((18, 21), [bc69, bc71, (269, false, false)]),
 ((17, 21), [(260, true, true)])]
private abbrev endpointInput9_29 : LowerPair × Bool × Bool := (([3, 2], [3]), false, false)
private def endpointCodes9_29 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((19, 23), [bc72]), ((19, 23), [bc73])]
private abbrev endpointInput9_30 : LowerPair × Bool × Bool := (([3], [3, 1]), true, true)
private def endpointCodes9_30 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((21, 17), [(275, false, true)]),
 ((21, 17), [bc74, bc75, (280, false, true)]),
 ((21, 18), [bc74, bc75, (280, true, false)]),
 ((21, 17), [bc74, bc76, (283, true, true)]),
 ((22, 17), [bc74, bc76, (283, false, false)])]
private abbrev endpointInput9_31 : LowerPair × Bool × Bool := (([3], [3, 2]), false, true)
private def endpointCodes9_31 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((23, 19), [bc77]), ((23, 19), [bc78])]
private abbrev endpointInput9_32 : LowerPair × Bool × Bool := (([3, 3], [3, 3]), false, false)
private def endpointCodes9_32 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((27, 27), [bc79, bc80]),
 ((27, 28), [bc79, bc81]),
 ((27, 27), [bc82, bc83]),
 ((28, 27), [bc82, bc84])]
private abbrev endpointInput9_33 : LowerPair × Bool × Bool := (([3, 3], [3, 3]), true, false)
private def endpointCodes9_33 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((25, 25), [])]
private abbrev endpointInput9_34 : LowerPair × Bool × Bool := (([2, 1], [1]), true, false)
private def endpointCodes9_34 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((13, 1), [bc85, bc86, bc87]),
 ((13, 2), [bc85, bc86, bc88]),
 ((13, 1), [bc85, bc89, bc90]),
 ((14, 1), [bc85, bc89, bc91]),
 ((13, 1), [bc92])]
private abbrev endpointInput9_35 : LowerPair × Bool × Bool := (([2, 2], [1]), false, false)
private def endpointCodes9_35 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((15, 4), [bc93]),
 ((15, 4), [bc94, bc95, bc96]),
 ((15, 7), [bc94, bc95, bc97]),
 ((15, 4), [bc94, bc98, bc99]),
 ((16, 4), [bc94, bc98, bc100])]
private abbrev endpointInput9_36 : LowerPair × Bool × Bool := (([2], [1, 1]), true, true)
private def endpointCodes9_36 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((0, 9), [bc101]),
 ((0, 9), [bc102, bc103, bc104]),
 ((0, 10), [bc102, bc103, bc105]),
 ((0, 9), [bc102, bc106, bc107]),
 ((3, 9), [bc102, bc106, bc108])]
private abbrev endpointInput9_37 : LowerPair × Bool × Bool := (([2], [1, 2]), false, true)
private def endpointCodes9_37 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((6, 11), [bc109, bc110, bc111]),
 ((6, 12), [bc109, bc110, bc112]),
 ((6, 11), [bc109, bc113, bc114]),
 ((8, 11), [bc109, bc113, bc115]),
 ((6, 11), [bc116])]
private abbrev endpointInput9_42 : LowerPair × Bool × Bool := (([2, 1], [2]), true, false)
private def endpointCodes9_42 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((13, 0), [bc117, bc118, bc119]),
 ((13, 3), [bc117, bc118, bc120]),
 ((13, 0), [bc117, bc121, bc122]),
 ((14, 0), [bc117, bc121, bc123]),
 ((13, 0), [bc124])]
private abbrev endpointInput9_43 : LowerPair × Bool × Bool := (([2, 2], [2]), false, false)
private def endpointCodes9_43 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((15, 6), [bc125]),
 ((15, 6), [bc126, bc127, bc128]),
 ((15, 8), [bc126, bc127, bc129]),
 ((15, 6), [bc126, bc130, bc131]),
 ((16, 6), [bc126, bc130, bc132])]
private abbrev endpointInput9_44 : LowerPair × Bool × Bool := (([2], [2, 1]), true, true)
private def endpointCodes9_44 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((0, 13), [bc133]),
 ((0, 13), [bc134, bc135, bc136]),
 ((0, 14), [bc134, bc135, bc137]),
 ((0, 13), [bc134, bc138, bc139]),
 ((3, 13), [bc134, bc138, bc140])]
private abbrev endpointInput9_45 : LowerPair × Bool × Bool := (([2], [2, 2]), false, true)
private def endpointCodes9_45 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((6, 15), [bc141, bc142, bc143]),
 ((6, 16), [bc141, bc142, bc144]),
 ((6, 15), [bc141, bc145, bc146]),
 ((8, 15), [bc141, bc145, bc147]),
 ((6, 15), [bc148])]
private abbrev endpointInput9_46 : LowerPair × Bool × Bool := (([2, 1], [3]), true, false)
private def endpointCodes9_46 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((13, 21), [bc149, bc150, (427, false, true)]),
 ((13, 22), [bc149, bc150, (427, true, false)]),
 ((13, 21), [bc149, bc151, (436, true, true)]),
 ((14, 21), [bc149, bc151, (436, false, false)]),
 ((13, 21), [(432, true, true)])]
private abbrev endpointInput9_47 : LowerPair × Bool × Bool := (([2, 2], [3]), false, false)
private def endpointCodes9_47 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((15, 23), [bc152]), ((15, 23), [bc153])]
private abbrev endpointInput9_48 : LowerPair × Bool × Bool := (([2], [3, 1]), true, true)
private def endpointCodes9_48 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((0, 17), [bc154]),
 ((0, 17), [bc155, bc156, bc157]),
 ((0, 18), [bc155, bc156, bc158]),
 ((0, 17), [bc155, bc159, bc160]),
 ((3, 17), [bc155, bc159, bc161])]
private abbrev endpointInput9_49 : LowerPair × Bool × Bool := (([2], [3, 2]), false, true)
private def endpointCodes9_49 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((6, 19), [bc162, bc163, bc164]),
 ((6, 20), [bc162, bc163, bc165]),
 ((6, 19), [bc162, bc166, bc167]),
 ((8, 19), [bc162, bc166, bc168]),
 ((6, 19), [bc169])]
private abbrev endpointInput9_50 : LowerPair × Bool × Bool := (([2], [1]), true, false)
private def endpointCodes9_50 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((0, 1), [bc2, bc3]),
 ((0, 2), [bc2, bc4]),
 ((0, 1), [bc5, bc6]),
 ((3, 1), [bc5, bc7])]
private abbrev endpointInput9_51 : LowerPair × Bool × Bool := (([3], [1]), true, false)
private def endpointCodes9_51 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((21, 1), [bc170, bc171]),
 ((21, 2), [bc170, bc172]),
 ((21, 1), [bc173, bc174]),
 ((22, 1), [bc173, bc175])]
private abbrev endpointInput9_52 : LowerPair × Bool × Bool := (([2], [1]), false, false)
private def endpointCodes9_52 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((6, 4), [bc2, bc176]),
 ((6, 7), [bc2, bc177]),
 ((6, 4), [bc5, bc178]),
 ((8, 4), [bc5, bc179])]
private abbrev endpointInput9_53 : LowerPair × Bool × Bool := (([2], [2]), false, false)
private def endpointCodes9_53 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((6, 6), [bc180, bc181]),
 ((6, 8), [bc180, bc182]),
 ((6, 6), [bc183, bc184]),
 ((8, 6), [bc183, bc185])]
private abbrev endpointInput9_54 : LowerPair × Bool × Bool := (([2], [2]), true, false)
private def endpointCodes9_54 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((0, 0), [bc180, bc186]),
 ((0, 3), [bc180, bc187]),
 ((0, 0), [bc183, bc188]),
 ((3, 0), [bc183, bc189])]
private abbrev endpointInput9_55 : LowerPair × Bool × Bool := (([3], [1]), false, false)
private def endpointCodes9_55 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((23, 4), [])]
private abbrev endpointInput9_56 : LowerPair × Bool × Bool := (([2], [3]), true, false)
private def endpointCodes9_56 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((0, 21), [bc190, bc191]),
 ((0, 22), [bc190, bc192]),
 ((0, 21), [bc193, bc194]),
 ((3, 21), [bc193, bc195])]
private abbrev endpointInput9_57 : LowerPair × Bool × Bool := (([2], [3]), false, false)
private def endpointCodes9_57 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((6, 23), [])]
private abbrev endpointInput9_58 : LowerPair × Bool × Bool := (([3, 1], [1, 1]), true, false)
private def endpointCodes9_58 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((17, 9), [bc196, bc197]),
 ((17, 10), [bc196, bc198]),
 ((17, 9), [bc199, bc200]),
 ((18, 9), [bc199, bc201])]
private abbrev endpointInput9_59 : LowerPair × Bool × Bool := (([3, 2], [1, 1]), false, false)
private def endpointCodes9_59 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((19, 4), [bc202, bc203]),
 ((19, 7), [bc202, bc204]),
 ((19, 4), [bc205, bc206]),
 ((20, 4), [bc205, bc207])]
private abbrev endpointInput9_60 : LowerPair × Bool × Bool := (([3], [1, 1, 2]), true, true)
private def endpointCodes9_60 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((21, 30), [bc208, (526, false, true)]),
 ((21, 31), [bc208, (526, true, false)]),
 ((21, 30), [bc209, (529, true, true)]),
 ((22, 30), [bc209, (529, false, false)])]
private abbrev endpointInput9_61 : LowerPair × Bool × Bool := (([3], [1, 1, 1]), false, true)
private def endpointCodes9_61 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((23, 32), [])]
private abbrev endpointInput9_62 : LowerPair × Bool × Bool := (([3], [1, 1]), true, false)
private def endpointCodes9_62 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((21, 9), [bc210]),
 ((21, 9), [bc211, bc212, bc213]),
 ((21, 10), [bc211, bc212, bc214]),
 ((21, 9), [bc211, bc215, bc216]),
 ((22, 9), [bc211, bc215, bc217])]
private abbrev endpointInput9_63 : LowerPair × Bool × Bool := (([3], [1, 1]), false, false)
private def endpointCodes9_63 : List ((ℕ × ℕ) × List (ℕ × Bool × Bool)) := [((23, 4), [bc210]), ((23, 4), [bc211])]

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

private theorem hEndpoint9_34 :
    trunkEndpointCases (trunkCatalog.states 9).context endpointInput9_34.1 endpointInput9_34.2.1 endpointInput9_34.2.2 = endpointCodes9_34.map decodeEndpoint9 := by decide +kernel

private theorem hEndpoint9_35 :
    trunkEndpointCases (trunkCatalog.states 9).context endpointInput9_35.1 endpointInput9_35.2.1 endpointInput9_35.2.2 = endpointCodes9_35.map decodeEndpoint9 := by decide +kernel

private theorem hEndpoint9_36 :
    trunkEndpointCases (trunkCatalog.states 9).context endpointInput9_36.1 endpointInput9_36.2.1 endpointInput9_36.2.2 = endpointCodes9_36.map decodeEndpoint9 := by decide +kernel

private theorem hEndpoint9_37 :
    trunkEndpointCases (trunkCatalog.states 9).context endpointInput9_37.1 endpointInput9_37.2.1 endpointInput9_37.2.2 = endpointCodes9_37.map decodeEndpoint9 := by decide +kernel

private theorem hEndpoint9_42 :
    trunkEndpointCases (trunkCatalog.states 9).context endpointInput9_42.1 endpointInput9_42.2.1 endpointInput9_42.2.2 = endpointCodes9_42.map decodeEndpoint9 := by decide +kernel

private theorem hEndpoint9_43 :
    trunkEndpointCases (trunkCatalog.states 9).context endpointInput9_43.1 endpointInput9_43.2.1 endpointInput9_43.2.2 = endpointCodes9_43.map decodeEndpoint9 := by decide +kernel

private theorem hEndpoint9_44 :
    trunkEndpointCases (trunkCatalog.states 9).context endpointInput9_44.1 endpointInput9_44.2.1 endpointInput9_44.2.2 = endpointCodes9_44.map decodeEndpoint9 := by decide +kernel

private theorem hEndpoint9_45 :
    trunkEndpointCases (trunkCatalog.states 9).context endpointInput9_45.1 endpointInput9_45.2.1 endpointInput9_45.2.2 = endpointCodes9_45.map decodeEndpoint9 := by decide +kernel

private theorem hEndpoint9_46 :
    trunkEndpointCases (trunkCatalog.states 9).context endpointInput9_46.1 endpointInput9_46.2.1 endpointInput9_46.2.2 = endpointCodes9_46.map decodeEndpoint9 := by decide +kernel

private theorem hEndpoint9_47 :
    trunkEndpointCases (trunkCatalog.states 9).context endpointInput9_47.1 endpointInput9_47.2.1 endpointInput9_47.2.2 = endpointCodes9_47.map decodeEndpoint9 := by decide +kernel

private theorem hEndpoint9_48 :
    trunkEndpointCases (trunkCatalog.states 9).context endpointInput9_48.1 endpointInput9_48.2.1 endpointInput9_48.2.2 = endpointCodes9_48.map decodeEndpoint9 := by decide +kernel

private theorem hEndpoint9_49 :
    trunkEndpointCases (trunkCatalog.states 9).context endpointInput9_49.1 endpointInput9_49.2.1 endpointInput9_49.2.2 = endpointCodes9_49.map decodeEndpoint9 := by decide +kernel

private theorem hEndpoint9_50 :
    trunkEndpointCases (trunkCatalog.states 9).context endpointInput9_50.1 endpointInput9_50.2.1 endpointInput9_50.2.2 = endpointCodes9_50.map decodeEndpoint9 := by decide +kernel

private theorem hEndpoint9_51 :
    trunkEndpointCases (trunkCatalog.states 9).context endpointInput9_51.1 endpointInput9_51.2.1 endpointInput9_51.2.2 = endpointCodes9_51.map decodeEndpoint9 := by decide +kernel

private theorem hEndpoint9_52 :
    trunkEndpointCases (trunkCatalog.states 9).context endpointInput9_52.1 endpointInput9_52.2.1 endpointInput9_52.2.2 = endpointCodes9_52.map decodeEndpoint9 := by decide +kernel

private theorem hEndpoint9_53 :
    trunkEndpointCases (trunkCatalog.states 9).context endpointInput9_53.1 endpointInput9_53.2.1 endpointInput9_53.2.2 = endpointCodes9_53.map decodeEndpoint9 := by decide +kernel

private theorem hEndpoint9_54 :
    trunkEndpointCases (trunkCatalog.states 9).context endpointInput9_54.1 endpointInput9_54.2.1 endpointInput9_54.2.2 = endpointCodes9_54.map decodeEndpoint9 := by decide +kernel

private theorem hEndpoint9_55 :
    trunkEndpointCases (trunkCatalog.states 9).context endpointInput9_55.1 endpointInput9_55.2.1 endpointInput9_55.2.2 = endpointCodes9_55.map decodeEndpoint9 := by decide +kernel

private theorem hEndpoint9_56 :
    trunkEndpointCases (trunkCatalog.states 9).context endpointInput9_56.1 endpointInput9_56.2.1 endpointInput9_56.2.2 = endpointCodes9_56.map decodeEndpoint9 := by decide +kernel

private theorem hEndpoint9_57 :
    trunkEndpointCases (trunkCatalog.states 9).context endpointInput9_57.1 endpointInput9_57.2.1 endpointInput9_57.2.2 = endpointCodes9_57.map decodeEndpoint9 := by decide +kernel

private theorem hEndpoint9_58 :
    trunkEndpointCases (trunkCatalog.states 9).context endpointInput9_58.1 endpointInput9_58.2.1 endpointInput9_58.2.2 = endpointCodes9_58.map decodeEndpoint9 := by decide +kernel

private theorem hEndpoint9_59 :
    trunkEndpointCases (trunkCatalog.states 9).context endpointInput9_59.1 endpointInput9_59.2.1 endpointInput9_59.2.2 = endpointCodes9_59.map decodeEndpoint9 := by decide +kernel

private theorem hEndpoint9_60 :
    trunkEndpointCases (trunkCatalog.states 9).context endpointInput9_60.1 endpointInput9_60.2.1 endpointInput9_60.2.2 = endpointCodes9_60.map decodeEndpoint9 := by decide +kernel

private theorem hEndpoint9_61 :
    trunkEndpointCases (trunkCatalog.states 9).context endpointInput9_61.1 endpointInput9_61.2.1 endpointInput9_61.2.2 = endpointCodes9_61.map decodeEndpoint9 := by decide +kernel

private theorem hEndpoint9_62 :
    trunkEndpointCases (trunkCatalog.states 9).context endpointInput9_62.1 endpointInput9_62.2.1 endpointInput9_62.2.2 = endpointCodes9_62.map decodeEndpoint9 := by decide +kernel

private theorem hEndpoint9_63 :
    trunkEndpointCases (trunkCatalog.states 9).context endpointInput9_63.1 endpointInput9_63.2.1 endpointInput9_63.2.2 = endpointCodes9_63.map decodeEndpoint9 := by decide +kernel

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

private def classValidIds : List ℕ := [245, 226, 252, 254, 255, 258, 295, 259, 261, 263, 264, 270, 273, 277, 281, 283, 284, 1, 140, 94, 30, 16, 10, 147, 149, 155, 156, 467, 469, 163, 153, 478, 477, 479, 103, 159, 482, 483, 481, 165, 484, 485, 486, 91, 487, 488, 489, 476, 491, 492, 493, 497, 442, 502, 503, 504, 505, 506, 136, 507, 287, 289, 290, 291, 247, 292, 294, 508, 2, 6, 9, 14, 15, 3, 4, 29, 28, 65, 52, 67, 8, 56, 68, 318, 321, 323, 322, 327, 329, 333, 337, 338, 349, 347, 509, 355, 515, 520, 524, 527, 529, 530, 377, 379, 381, 378, 385, 390, 397, 402, 407, 411, 413, 417, 421, 422, 427, 430, 428, 429, 438, 441, 447, 451, 453, 457, 461, 462, 179, 182, 181, 180, 187, 191, 200, 204, 207, 211, 213, 214, 365, 533, 96, 371, 536, 373, 374, 539, 542, 543, 544, 545, 546, 547, 548, 549, 550, 89, 176, 167]
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
private def codeHN : ℕ × Bool × Bool := bc61
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
private def thresholdParentA9 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc0, bc8, bc9, bc10], some (some bc218)),
 ([bc0, bc8, bc9, bc11], some (some bc219)),
 ([bc0, bc8, bc12, bc13], some (some bc218)),
 ([bc0, bc8, bc12, bc14], some (some bc220)),
 ([bc0, bc15], some (some bc218)),
 ([bc1, bc2, bc3, bc8, bc9, bc10],
  some (some bc218)),
 ([bc1, bc2, bc3, bc8, bc9, bc11],
  some (some bc219)),
 ([bc1, bc2, bc3, bc8, bc12, bc13],
  some (some bc218)),
 ([bc1, bc2, bc3, bc8, bc12, bc14],
  some (some bc220)),
 ([bc1, bc2, bc3, bc15], some (some bc218)),
 ([bc1, bc2, bc4, bc8, bc9, bc10],
  some (some bc221)),
 ([bc1, bc2, bc4, bc8, bc9, bc11],
  some (some (145, true, false))),
 ([bc1, bc2, bc4, bc8, bc12, bc13],
  some (some bc221)),
 ([bc1, bc2, bc4, bc8, bc12, bc14],
  some (some (146, true, false))),
 ([bc1, bc2, bc4, bc15], some (some bc221)),
 ([bc1, bc5, bc6, bc8, bc9, bc10],
  some (some bc218)),
 ([bc1, bc5, bc6, bc8, bc9, bc11],
  some (some bc219)),
 ([bc1, bc5, bc6, bc8, bc12, bc13],
  some (some bc218)),
 ([bc1, bc5, bc6, bc8, bc12, bc14],
  some (some bc220)),
 ([bc1, bc5, bc6, bc15], some (some bc218)),
 ([bc1, bc5, bc7, bc8, bc9, bc10],
  some (some bc222)),
 ([bc1, bc5, bc7, bc8, bc9, bc11],
  some (some (150, true, false))),
 ([bc1, bc5, bc7, bc8, bc12, bc13],
  some (some bc222)),
 ([bc1, bc5, bc7, bc8, bc12, bc14],
  some (some (151, true, false))),
 ([bc1, bc5, bc7, bc15], some (some bc222))]
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

private def parentSourceA9 : Array (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := #[([bc0, bc8, bc9, bc10], some (some bc218)),
 ([bc0, bc8, bc9, bc11], some (some bc219)),
 ([bc0, bc8, bc12, bc13], some (some bc218)),
 ([bc0, bc8, bc12, bc14], some (some bc220)),
 ([bc0, bc15], some (some bc218)),
 ([bc1, bc2, bc3, bc8, bc9, bc10],
  some (some bc218)),
 ([bc1, bc2, bc3, bc8, bc9, bc11],
  some (some bc219)),
 ([bc1, bc2, bc3, bc8, bc12, bc13],
  some (some bc218)),
 ([bc1, bc2, bc3, bc8, bc12, bc14],
  some (some bc220)),
 ([bc1, bc2, bc3, bc15], some (some bc218)),
 ([bc1, bc2, bc4, bc8, bc9, bc10],
  some (some bc221)),
 ([bc1, bc2, bc4, bc8, bc9, bc11],
  some (some (145, true, false))),
 ([bc1, bc2, bc4, bc8, bc12, bc13],
  some (some bc221)),
 ([bc1, bc2, bc4, bc8, bc12, bc14],
  some (some (146, true, false))),
 ([bc1, bc2, bc4, bc15], some (some bc221)),
 ([bc1, bc5, bc6, bc8, bc9, bc10],
  some (some bc218)),
 ([bc1, bc5, bc6, bc8, bc9, bc11],
  some (some bc219)),
 ([bc1, bc5, bc6, bc8, bc12, bc13],
  some (some bc218)),
 ([bc1, bc5, bc6, bc8, bc12, bc14],
  some (some bc220)),
 ([bc1, bc5, bc6, bc15], some (some bc218)),
 ([bc1, bc5, bc7, bc8, bc9, bc10],
  some (some bc222)),
 ([bc1, bc5, bc7, bc8, bc9, bc11],
  some (some (150, true, false))),
 ([bc1, bc5, bc7, bc8, bc12, bc13],
  some (some bc222)),
 ([bc1, bc5, bc7, bc8, bc12, bc14],
  some (some (151, true, false))),
 ([bc1, bc5, bc7, bc15], some (some bc222))]

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


private def goalCodes9_4_0 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([], none)]
private def goalCodes9_4_35 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc82, bc64, (248, false, true)], some (some bc223)),
 ([bc82, bc64, bc66, bc67, (249, false, true)],
  some (some bc223)),
 ([bc82, bc64, bc66, bc67, (249, true, false)],
  some (some (253, false, true))),
 ([bc82, bc64, bc66, bc68, (254, true, true)],
  some (some bc223)),
 ([bc82, bc64, bc66, bc68, (254, false, false)],
  some (some (257, false, true))),
 ([bc82, bc65, (248, false, true)], some (some bc223)),
 ([bc82, bc65, bc66, bc67, (249, false, true)],
  some (some bc223)),
 ([bc82, bc65, bc66, bc67, (249, true, false)],
  some (some (253, false, true))),
 ([bc82, bc65, bc66, bc68, (254, true, true)],
  some (some bc223)),
 ([bc82, bc65, bc66, bc68, (254, false, false)],
  some (some (257, false, true)))]
private def goalCodes9_4_37 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc224, bc69, bc70, (259, false, true), bc72],
  some (some bc225)),
 ([bc224, bc69, bc70, (259, false, true), bc73],
  some (some bc225)),
 ([bc224, bc69, bc70, (259, true, false), bc72],
  some (some (266, true, true))),
 ([bc224, bc69, bc70, (259, true, false), bc73],
  some (some (266, true, true))),
 ([bc224, bc69, bc71, (269, true, true), bc72],
  some (some bc225)),
 ([bc224, bc69, bc71, (269, true, true), bc73],
  some (some bc225)),
 ([bc224, bc69, bc71, (269, false, false), bc72],
  some (some (271, true, true))),
 ([bc224, bc69, bc71, (269, false, false), bc73],
  some (some (271, true, true))),
 ([bc224, (260, true, true), bc72], some (some bc225)),
 ([bc224, (260, true, true), bc73], some (some bc225))]
private def goalCodes9_4_39 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc226, (275, false, true), bc77], some (some bc227)),
 ([bc226, (275, false, true), bc78], some (some bc227)),
 ([bc226, bc74, bc75, (280, false, true), bc77],
  some (some bc227)),
 ([bc226, bc74, bc75, (280, false, true), bc78],
  some (some bc227)),
 ([bc226, bc74, bc75, (280, true, false), bc77],
  some (some (282, false, true))),
 ([bc226, bc74, bc75, (280, true, false), bc78],
  some (some (282, false, true))),
 ([bc226, bc74, bc76, (283, true, true), bc77],
  some (some bc227)),
 ([bc226, bc74, bc76, (283, true, true), bc78],
  some (some bc227)),
 ([bc226, bc74, bc76, (283, false, false), bc77],
  some (some (285, false, true))),
 ([bc226, bc74, bc76, (283, false, false), bc78],
  some (some (285, false, true)))]
private def goalCodes9_4_42 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc2, bc3, bc8, bc9, bc10],
  some (some bc218)),
 ([bc2, bc3, bc8, bc9, bc11],
  some (some bc219)),
 ([bc2, bc3, bc8, bc12, bc13],
  some (some bc218)),
 ([bc2, bc3, bc8, bc12, bc14],
  some (some bc220)),
 ([bc2, bc3, bc15], some (some bc218)),
 ([bc2, bc4, bc8, bc9, bc10],
  some (some bc221)),
 ([bc2, bc4, bc8, bc9, bc11],
  some (some (145, true, false))),
 ([bc2, bc4, bc8, bc12, bc13],
  some (some bc221)),
 ([bc2, bc4, bc8, bc12, bc14],
  some (some (146, true, false))),
 ([bc2, bc4, bc15], some (some bc221)),
 ([bc5, bc6, bc8, bc9, bc10],
  some (some bc218)),
 ([bc5, bc6, bc8, bc9, bc11],
  some (some bc219)),
 ([bc5, bc6, bc8, bc12, bc13],
  some (some bc218)),
 ([bc5, bc6, bc8, bc12, bc14],
  some (some bc220)),
 ([bc5, bc6, bc15], some (some bc218)),
 ([bc5, bc7, bc8, bc9, bc10],
  some (some bc222)),
 ([bc5, bc7, bc8, bc9, bc11],
  some (some (150, true, false))),
 ([bc5, bc7, bc8, bc12, bc13],
  some (some bc222)),
 ([bc5, bc7, bc8, bc12, bc14],
  some (some (151, true, false))),
 ([bc5, bc7, bc15], some (some bc222))]
private def goalCodes9_4_44 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc170, bc171, bc2, bc176], some (some bc228)),
 ([bc170, bc171, bc2, bc177], some (some (468, true, false))),
 ([bc170, bc171, bc5, bc178], some (some bc228)),
 ([bc170, bc171, bc5, bc179], some (some (469, true, false))),
 ([bc170, bc172, bc2, bc176], some (some (470, true, false))),
 ([bc170, bc172, bc2, bc177], some (some (471, true, false))),
 ([bc170, bc172, bc5, bc178], some (some (470, true, false))),
 ([bc170, bc172, bc5, bc179], some (some (472, true, false))),
 ([bc173, bc174, bc2, bc176], some (some bc228)),
 ([bc173, bc174, bc2, bc177], some (some (468, true, false))),
 ([bc173, bc174, bc5, bc178], some (some bc228)),
 ([bc173, bc174, bc5, bc179], some (some (469, true, false))),
 ([bc173, bc175, bc2, bc176], some (some (473, true, false))),
 ([bc173, bc175, bc2, bc177], some (some (474, true, false))),
 ([bc173, bc175, bc5, bc178], some (some (473, true, false))),
 ([bc173, bc175, bc5, bc179], some (some (475, true, false)))]
private def goalCodes9_4_45 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc170, bc171, bc180, bc181], some (some bc229)),
 ([bc170, bc171, bc180, bc182], some (some (477, true, false))),
 ([bc170, bc171, bc183, bc184], some (some bc229)),
 ([bc170, bc171, bc183, bc185], some (some (481, true, false))),
 ([bc170, bc172, bc180, bc181], some (some (159, true, false))),
 ([bc170, bc172, bc180, bc182], some (some (482, true, false))),
 ([bc170, bc172, bc183, bc184], some (some (159, true, false))),
 ([bc170, bc172, bc183, bc185], some (some (483, true, false))),
 ([bc173, bc174, bc180, bc181], some (some bc229)),
 ([bc173, bc174, bc180, bc182], some (some (477, true, false))),
 ([bc173, bc174, bc183, bc184], some (some bc229)),
 ([bc173, bc174, bc183, bc185], some (some (481, true, false))),
 ([bc173, bc175, bc180, bc181], some (some (165, true, false))),
 ([bc173, bc175, bc180, bc182], some (some (484, true, false))),
 ([bc173, bc175, bc183, bc184], some (some (165, true, false))),
 ([bc173, bc175, bc183, bc185], some (some (485, true, false)))]
private def goalCodes9_4_46 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc180, bc186], some (some bc230)),
 ([bc180, bc187], some (some (487, false, false))),
 ([bc183, bc188], some (some bc230)),
 ([bc183, bc189], some (some (488, false, false)))]
private def goalCodes9_4_48 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc190, bc191, bc180, bc181], some (some bc231)),
 ([bc190, bc191, bc180, bc182], some (some (491, false, false))),
 ([bc190, bc191, bc183, bc184], some (some bc231)),
 ([bc190, bc191, bc183, bc185], some (some (492, false, false))),
 ([bc190, bc192, bc180, bc181], some (some (494, false, false))),
 ([bc190, bc192, bc180, bc182], some (some (495, false, false))),
 ([bc190, bc192, bc183, bc184], some (some (494, false, false))),
 ([bc190, bc192, bc183, bc185], some (some (496, false, false))),
 ([bc193, bc194, bc180, bc181], some (some bc231)),
 ([bc193, bc194, bc180, bc182], some (some (491, false, false))),
 ([bc193, bc194, bc183, bc184], some (some bc231)),
 ([bc193, bc194, bc183, bc185], some (some (492, false, false))),
 ([bc193, bc195, bc180, bc181], some (some (499, false, false))),
 ([bc193, bc195, bc180, bc182], some (some (500, false, false))),
 ([bc193, bc195, bc183, bc184], some (some (499, false, false))),
 ([bc193, bc195, bc183, bc185], some (some (501, false, false)))]
private def goalCodes9_4_49 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc190, bc191], some (some (502, false, false))),
 ([bc190, bc192], some (some (503, false, false))),
 ([bc193, bc194], some (some (502, false, false))),
 ([bc193, bc195], some (some (504, false, false)))]
private def goalCodes9_4_50 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc55, bc56], some (some (505, true, false))),
 ([bc55, bc57], some (some (506, true, false))),
 ([bc58, bc59], some (some (505, true, false))),
 ([bc58, bc60], some (some (507, true, false)))]
private def goalCodes9_4_51 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc55, bc56, bc79, bc80], some none),
 ([bc55, bc56, bc79, bc81], some none),
 ([bc55, bc56, bc82, bc83], some none),
 ([bc55, bc56, bc82, bc84], some none),
 ([bc55, bc57, bc79, bc80], some none),
 ([bc55, bc57, bc79, bc81], some none),
 ([bc55, bc57, bc82, bc83], some none),
 ([bc55, bc57, bc82, bc84], some none),
 ([bc58, bc59, bc79, bc80], some none),
 ([bc58, bc59, bc79, bc81], some none),
 ([bc58, bc59, bc82, bc83], some none),
 ([bc58, bc59, bc82, bc84], some none),
 ([bc58, bc60, bc79, bc80], some (some (287, true, false))),
 ([bc58, bc60, bc79, bc81], some (some (290, true, false))),
 ([bc58, bc60, bc82, bc83], some (some (287, true, false))),
 ([bc58, bc60, bc82, bc84], some (some (292, true, false)))]
private def goalCodes9_4_52 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([], some (some (294, false, false)))]
private def goalCodes9_5_0 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes9_4_0
private def goalCodes9_5_2 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc8, bc9, bc22, bc26, bc27],
  some (some bc232)),
 ([bc8, bc9, bc22, bc26, bc28],
  some (some (36, true, true))),
 ([bc8, bc9, bc22, bc29, bc30],
  some (some bc232)),
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
  some (some bc232)),
 ([bc8, bc12, bc24, bc26, bc28],
  some (some (36, true, true))),
 ([bc8, bc12, bc24, bc29, bc30],
  some (some bc232)),
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
private def goalCodes9_5_5 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc15, bc32, (52, false, true)], some (some (65, false, true))),
 ([bc15, bc32, (52, true, false)], some (some (67, false, true))),
 ([bc15, bc33, (56, true, true)], some (some (65, false, true))),
 ([bc15, bc33, (56, false, false)], some (some (68, false, true)))]
private def goalCodes9_5_7 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc2, bc85, bc86, bc87, bc93],
  some (some bc233)),
 ([bc2,
   bc85,
   bc86,
   bc87,
   bc94,
   bc95,
   bc96],
  some (some bc233)),
 ([bc2,
   bc85,
   bc86,
   bc87,
   bc94,
   bc95,
   bc97],
  some (some (304, true, true))),
 ([bc2,
   bc85,
   bc86,
   bc87,
   bc94,
   bc98,
   bc99],
  some (some bc233)),
 ([bc2,
   bc85,
   bc86,
   bc87,
   bc94,
   bc98,
   bc100],
  some (some (309, true, true))),
 ([bc2, bc85, bc86, bc88, bc93],
  some (some (310, true, true))),
 ([bc2,
   bc85,
   bc86,
   bc88,
   bc94,
   bc95,
   bc96],
  some (some (310, true, true))),
 ([bc2,
   bc85,
   bc86,
   bc88,
   bc94,
   bc95,
   bc97],
  some (some (311, true, true))),
 ([bc2,
   bc85,
   bc86,
   bc88,
   bc94,
   bc98,
   bc99],
  some (some (310, true, true))),
 ([bc2,
   bc85,
   bc86,
   bc88,
   bc94,
   bc98,
   bc100],
  some (some (312, true, true))),
 ([bc2, bc85, bc89, bc90, bc93],
  some (some bc233)),
 ([bc2,
   bc85,
   bc89,
   bc90,
   bc94,
   bc95,
   bc96],
  some (some bc233)),
 ([bc2,
   bc85,
   bc89,
   bc90,
   bc94,
   bc95,
   bc97],
  some (some (304, true, true))),
 ([bc2,
   bc85,
   bc89,
   bc90,
   bc94,
   bc98,
   bc99],
  some (some bc233)),
 ([bc2,
   bc85,
   bc89,
   bc90,
   bc94,
   bc98,
   bc100],
  some (some (309, true, true))),
 ([bc2, bc85, bc89, bc91, bc93],
  some (some (314, true, true))),
 ([bc2,
   bc85,
   bc89,
   bc91,
   bc94,
   bc95,
   bc96],
  some (some (314, true, true))),
 ([bc2,
   bc85,
   bc89,
   bc91,
   bc94,
   bc95,
   bc97],
  some (some (315, true, true))),
 ([bc2,
   bc85,
   bc89,
   bc91,
   bc94,
   bc98,
   bc99],
  some (some (314, true, true))),
 ([bc2,
   bc85,
   bc89,
   bc91,
   bc94,
   bc98,
   bc100],
  some (some (316, true, true))),
 ([bc2, bc92, bc93], some (some bc233)),
 ([bc2, bc92, bc94, bc95, bc96],
  some (some bc233)),
 ([bc2, bc92, bc94, bc95, bc97],
  some (some (304, true, true))),
 ([bc2, bc92, bc94, bc98, bc99],
  some (some bc233)),
 ([bc2, bc92, bc94, bc98, bc100],
  some (some (309, true, true)))]
private def goalCodes9_5_9 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc5, bc101, bc109, bc110, bc111],
  some (some bc234)),
 ([bc5, bc101, bc109, bc110, bc112],
  some (some (323, false, true))),
 ([bc5, bc101, bc109, bc113, bc114],
  some (some bc234)),
 ([bc5, bc101, bc109, bc113, bc115],
  some (some (327, false, true))),
 ([bc5, bc101, bc116], some (some bc234)),
 ([bc5,
   bc102,
   bc103,
   bc104,
   bc109,
   bc110,
   bc111],
  some (some bc234)),
 ([bc5,
   bc102,
   bc103,
   bc104,
   bc109,
   bc110,
   bc112],
  some (some (323, false, true))),
 ([bc5,
   bc102,
   bc103,
   bc104,
   bc109,
   bc113,
   bc114],
  some (some bc234)),
 ([bc5,
   bc102,
   bc103,
   bc104,
   bc109,
   bc113,
   bc115],
  some (some (327, false, true))),
 ([bc5, bc102, bc103, bc104, bc116],
  some (some bc234)),
 ([bc5,
   bc102,
   bc103,
   bc105,
   bc109,
   bc110,
   bc111],
  some (some (334, false, true))),
 ([bc5,
   bc102,
   bc103,
   bc105,
   bc109,
   bc110,
   bc112],
  some (some (335, false, true))),
 ([bc5,
   bc102,
   bc103,
   bc105,
   bc109,
   bc113,
   bc114],
  some (some (334, false, true))),
 ([bc5,
   bc102,
   bc103,
   bc105,
   bc109,
   bc113,
   bc115],
  some (some (336, false, true))),
 ([bc5, bc102, bc103, bc105, bc116],
  some (some (334, false, true))),
 ([bc5,
   bc102,
   bc106,
   bc107,
   bc109,
   bc110,
   bc111],
  some (some bc234)),
 ([bc5,
   bc102,
   bc106,
   bc107,
   bc109,
   bc110,
   bc112],
  some (some (323, false, true))),
 ([bc5,
   bc102,
   bc106,
   bc107,
   bc109,
   bc113,
   bc114],
  some (some bc234)),
 ([bc5,
   bc102,
   bc106,
   bc107,
   bc109,
   bc113,
   bc115],
  some (some (327, false, true))),
 ([bc5, bc102, bc106, bc107, bc116],
  some (some bc234)),
 ([bc5,
   bc102,
   bc106,
   bc108,
   bc109,
   bc110,
   bc111],
  some (some (340, false, true))),
 ([bc5,
   bc102,
   bc106,
   bc108,
   bc109,
   bc110,
   bc112],
  some (some (341, false, true))),
 ([bc5,
   bc102,
   bc106,
   bc108,
   bc109,
   bc113,
   bc114],
  some (some (340, false, true))),
 ([bc5,
   bc102,
   bc106,
   bc108,
   bc109,
   bc113,
   bc115],
  some (some (342, false, true))),
 ([bc5, bc102, bc106, bc108, bc116],
  some (some (340, false, true)))]
private def goalCodes9_5_12 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc210, bc196, bc197, bc202, bc203],
  some (some bc235)),
 ([bc210, bc196, bc197, bc202, bc204],
  some (some (512, true, true))),
 ([bc210, bc196, bc197, bc205, bc206],
  some (some bc235)),
 ([bc210, bc196, bc197, bc205, bc207],
  some (some (513, true, true))),
 ([bc210, bc196, bc198, bc202, bc203],
  some (some (515, true, true))),
 ([bc210, bc196, bc198, bc202, bc204],
  some (some (516, true, true))),
 ([bc210, bc196, bc198, bc205, bc206],
  some (some (515, true, true))),
 ([bc210, bc196, bc198, bc205, bc207],
  some (some (517, true, true))),
 ([bc210, bc199, bc200, bc202, bc203],
  some (some bc235)),
 ([bc210, bc199, bc200, bc202, bc204],
  some (some (512, true, true))),
 ([bc210, bc199, bc200, bc205, bc206],
  some (some bc235)),
 ([bc210, bc199, bc200, bc205, bc207],
  some (some (513, true, true))),
 ([bc210, bc199, bc201, bc202, bc203],
  some (some (520, true, true))),
 ([bc210, bc199, bc201, bc202, bc204],
  some (some (522, true, true))),
 ([bc210, bc199, bc201, bc205, bc206],
  some (some (520, true, true))),
 ([bc210, bc199, bc201, bc205, bc207],
  some (some (523, true, true)))]
private def goalCodes9_5_15 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc211, bc208, (526, false, true)], some (some (524, false, true))),
 ([bc211, bc208, (526, true, false)], some (some (528, false, true))),
 ([bc211, bc209, (529, true, true)], some (some (524, false, true))),
 ([bc211, bc209, (529, false, false)], some (some (531, false, true)))]
private def goalCodes9_5_17 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc180, bc117, bc118, bc119, bc125],
  some (some bc236)),
 ([bc180,
   bc117,
   bc118,
   bc119,
   bc126,
   bc127,
   bc128],
  some (some bc236)),
 ([bc180,
   bc117,
   bc118,
   bc119,
   bc126,
   bc127,
   bc129],
  some (some (385, true, true))),
 ([bc180,
   bc117,
   bc118,
   bc119,
   bc126,
   bc130,
   bc131],
  some (some bc236)),
 ([bc180,
   bc117,
   bc118,
   bc119,
   bc126,
   bc130,
   bc132],
  some (some (390, true, true))),
 ([bc180, bc117, bc118, bc120, bc125],
  some (some (391, true, true))),
 ([bc180,
   bc117,
   bc118,
   bc120,
   bc126,
   bc127,
   bc128],
  some (some (391, true, true))),
 ([bc180,
   bc117,
   bc118,
   bc120,
   bc126,
   bc127,
   bc129],
  some (some (393, true, true))),
 ([bc180,
   bc117,
   bc118,
   bc120,
   bc126,
   bc130,
   bc131],
  some (some (391, true, true))),
 ([bc180,
   bc117,
   bc118,
   bc120,
   bc126,
   bc130,
   bc132],
  some (some (394, true, true))),
 ([bc180, bc117, bc121, bc122, bc125],
  some (some bc236)),
 ([bc180,
   bc117,
   bc121,
   bc122,
   bc126,
   bc127,
   bc128],
  some (some bc236)),
 ([bc180,
   bc117,
   bc121,
   bc122,
   bc126,
   bc127,
   bc129],
  some (some (385, true, true))),
 ([bc180,
   bc117,
   bc121,
   bc122,
   bc126,
   bc130,
   bc131],
  some (some bc236)),
 ([bc180,
   bc117,
   bc121,
   bc122,
   bc126,
   bc130,
   bc132],
  some (some (390, true, true))),
 ([bc180, bc117, bc121, bc123, bc125],
  some (some (398, true, true))),
 ([bc180,
   bc117,
   bc121,
   bc123,
   bc126,
   bc127,
   bc128],
  some (some (398, true, true))),
 ([bc180,
   bc117,
   bc121,
   bc123,
   bc126,
   bc127,
   bc129],
  some (some (399, true, true))),
 ([bc180,
   bc117,
   bc121,
   bc123,
   bc126,
   bc130,
   bc131],
  some (some (398, true, true))),
 ([bc180,
   bc117,
   bc121,
   bc123,
   bc126,
   bc130,
   bc132],
  some (some (400, true, true))),
 ([bc180, bc124, bc125], some (some bc236)),
 ([bc180, bc124, bc126, bc127, bc128],
  some (some bc236)),
 ([bc180, bc124, bc126, bc127, bc129],
  some (some (385, true, true))),
 ([bc180, bc124, bc126, bc130, bc131],
  some (some bc236)),
 ([bc180, bc124, bc126, bc130, bc132],
  some (some (390, true, true)))]
private def goalCodes9_5_19 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc183, bc133, bc141, bc142, bc143],
  some (some bc237)),
 ([bc183, bc133, bc141, bc142, bc144],
  some (some (407, false, true))),
 ([bc183, bc133, bc141, bc145, bc146],
  some (some bc237)),
 ([bc183, bc133, bc141, bc145, bc147],
  some (some (411, false, true))),
 ([bc183, bc133, bc148], some (some bc237)),
 ([bc183,
   bc134,
   bc135,
   bc136,
   bc141,
   bc142,
   bc143],
  some (some bc237)),
 ([bc183,
   bc134,
   bc135,
   bc136,
   bc141,
   bc142,
   bc144],
  some (some (407, false, true))),
 ([bc183,
   bc134,
   bc135,
   bc136,
   bc141,
   bc145,
   bc146],
  some (some bc237)),
 ([bc183,
   bc134,
   bc135,
   bc136,
   bc141,
   bc145,
   bc147],
  some (some (411, false, true))),
 ([bc183, bc134, bc135, bc136, bc148],
  some (some bc237)),
 ([bc183,
   bc134,
   bc135,
   bc137,
   bc141,
   bc142,
   bc143],
  some (some (418, false, true))),
 ([bc183,
   bc134,
   bc135,
   bc137,
   bc141,
   bc142,
   bc144],
  some (some (419, false, true))),
 ([bc183,
   bc134,
   bc135,
   bc137,
   bc141,
   bc145,
   bc146],
  some (some (418, false, true))),
 ([bc183,
   bc134,
   bc135,
   bc137,
   bc141,
   bc145,
   bc147],
  some (some (420, false, true))),
 ([bc183, bc134, bc135, bc137, bc148],
  some (some (418, false, true))),
 ([bc183,
   bc134,
   bc138,
   bc139,
   bc141,
   bc142,
   bc143],
  some (some bc237)),
 ([bc183,
   bc134,
   bc138,
   bc139,
   bc141,
   bc142,
   bc144],
  some (some (407, false, true))),
 ([bc183,
   bc134,
   bc138,
   bc139,
   bc141,
   bc145,
   bc146],
  some (some bc237)),
 ([bc183,
   bc134,
   bc138,
   bc139,
   bc141,
   bc145,
   bc147],
  some (some (411, false, true))),
 ([bc183, bc134, bc138, bc139, bc148],
  some (some bc237)),
 ([bc183,
   bc134,
   bc138,
   bc140,
   bc141,
   bc142,
   bc143],
  some (some (424, false, true))),
 ([bc183,
   bc134,
   bc138,
   bc140,
   bc141,
   bc142,
   bc144],
  some (some (425, false, true))),
 ([bc183,
   bc134,
   bc138,
   bc140,
   bc141,
   bc145,
   bc146],
  some (some (424, false, true))),
 ([bc183,
   bc134,
   bc138,
   bc140,
   bc141,
   bc145,
   bc147],
  some (some (426, false, true))),
 ([bc183, bc134, bc138, bc140, bc148],
  some (some (424, false, true)))]
private def goalCodes9_5_22 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc190, bc149, bc150, (427, false, true), bc152],
  some (some bc238)),
 ([bc190, bc149, bc150, (427, false, true), bc153],
  some (some bc238)),
 ([bc190, bc149, bc150, (427, true, false), bc152],
  some (some (434, true, true))),
 ([bc190, bc149, bc150, (427, true, false), bc153],
  some (some (434, true, true))),
 ([bc190, bc149, bc151, (436, true, true), bc152],
  some (some bc238)),
 ([bc190, bc149, bc151, (436, true, true), bc153],
  some (some bc238)),
 ([bc190, bc149, bc151, (436, false, false), bc152],
  some (some (439, true, true))),
 ([bc190, bc149, bc151, (436, false, false), bc153],
  some (some (439, true, true))),
 ([bc190, (432, true, true), bc152], some (some bc238)),
 ([bc190, (432, true, true), bc153], some (some bc238))]
private def goalCodes9_5_24 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc193, bc154, bc162, bc163, bc164],
  some (some bc239)),
 ([bc193, bc154, bc162, bc163, bc165],
  some (some (447, false, true))),
 ([bc193, bc154, bc162, bc166, bc167],
  some (some bc239)),
 ([bc193, bc154, bc162, bc166, bc168],
  some (some (451, false, true))),
 ([bc193, bc154, bc169], some (some bc239)),
 ([bc193,
   bc155,
   bc156,
   bc157,
   bc162,
   bc163,
   bc164],
  some (some bc239)),
 ([bc193,
   bc155,
   bc156,
   bc157,
   bc162,
   bc163,
   bc165],
  some (some (447, false, true))),
 ([bc193,
   bc155,
   bc156,
   bc157,
   bc162,
   bc166,
   bc167],
  some (some bc239)),
 ([bc193,
   bc155,
   bc156,
   bc157,
   bc162,
   bc166,
   bc168],
  some (some (451, false, true))),
 ([bc193, bc155, bc156, bc157, bc169],
  some (some bc239)),
 ([bc193,
   bc155,
   bc156,
   bc158,
   bc162,
   bc163,
   bc164],
  some (some (458, false, true))),
 ([bc193,
   bc155,
   bc156,
   bc158,
   bc162,
   bc163,
   bc165],
  some (some (459, false, true))),
 ([bc193,
   bc155,
   bc156,
   bc158,
   bc162,
   bc166,
   bc167],
  some (some (458, false, true))),
 ([bc193,
   bc155,
   bc156,
   bc158,
   bc162,
   bc166,
   bc168],
  some (some (460, false, true))),
 ([bc193, bc155, bc156, bc158, bc169],
  some (some (458, false, true))),
 ([bc193,
   bc155,
   bc159,
   bc160,
   bc162,
   bc163,
   bc164],
  some (some bc239)),
 ([bc193,
   bc155,
   bc159,
   bc160,
   bc162,
   bc163,
   bc165],
  some (some (447, false, true))),
 ([bc193,
   bc155,
   bc159,
   bc160,
   bc162,
   bc166,
   bc167],
  some (some bc239)),
 ([bc193,
   bc155,
   bc159,
   bc160,
   bc162,
   bc166,
   bc168],
  some (some (451, false, true))),
 ([bc193, bc155, bc159, bc160, bc169],
  some (some bc239)),
 ([bc193,
   bc155,
   bc159,
   bc161,
   bc162,
   bc163,
   bc164],
  some (some (464, false, true))),
 ([bc193,
   bc155,
   bc159,
   bc161,
   bc162,
   bc163,
   bc165],
  some (some (465, false, true))),
 ([bc193,
   bc155,
   bc159,
   bc161,
   bc162,
   bc166,
   bc167],
  some (some (464, false, true))),
 ([bc193,
   bc155,
   bc159,
   bc161,
   bc162,
   bc166,
   bc168],
  some (some (466, false, true))),
 ([bc193, bc155, bc159, bc161, bc169],
  some (some (464, false, true)))]
private def goalCodes9_5_27 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc55, bc34, bc35, bc36, bc42],
  some (some bc240)),
 ([bc55,
   bc34,
   bc35,
   bc36,
   bc43,
   bc44,
   bc45],
  some (some bc240)),
 ([bc55,
   bc34,
   bc35,
   bc36,
   bc43,
   bc44,
   bc46],
  some (some (187, true, true))),
 ([bc55,
   bc34,
   bc35,
   bc36,
   bc43,
   bc47,
   bc48],
  some (some bc240)),
 ([bc55,
   bc34,
   bc35,
   bc36,
   bc43,
   bc47,
   bc49],
  some (some (191, true, true))),
 ([bc55, bc34, bc35, bc37, bc42],
  some (some (194, true, true))),
 ([bc55,
   bc34,
   bc35,
   bc37,
   bc43,
   bc44,
   bc45],
  some (some (194, true, true))),
 ([bc55,
   bc34,
   bc35,
   bc37,
   bc43,
   bc44,
   bc46],
  some (some (195, true, true))),
 ([bc55,
   bc34,
   bc35,
   bc37,
   bc43,
   bc47,
   bc48],
  some (some (194, true, true))),
 ([bc55,
   bc34,
   bc35,
   bc37,
   bc43,
   bc47,
   bc49],
  some (some (196, true, true))),
 ([bc55, bc34, bc38, bc39, bc42],
  some (some bc240)),
 ([bc55,
   bc34,
   bc38,
   bc39,
   bc43,
   bc44,
   bc45],
  some (some bc240)),
 ([bc55,
   bc34,
   bc38,
   bc39,
   bc43,
   bc44,
   bc46],
  some (some (187, true, true))),
 ([bc55,
   bc34,
   bc38,
   bc39,
   bc43,
   bc47,
   bc48],
  some (some bc240)),
 ([bc55,
   bc34,
   bc38,
   bc39,
   bc43,
   bc47,
   bc49],
  some (some (191, true, true))),
 ([bc55, bc34, bc38, bc40, bc42],
  some (some (199, true, true))),
 ([bc55,
   bc34,
   bc38,
   bc40,
   bc43,
   bc44,
   bc45],
  some (some (199, true, true))),
 ([bc55,
   bc34,
   bc38,
   bc40,
   bc43,
   bc44,
   bc46],
  some (some (201, true, true))),
 ([bc55,
   bc34,
   bc38,
   bc40,
   bc43,
   bc47,
   bc48],
  some (some (199, true, true))),
 ([bc55,
   bc34,
   bc38,
   bc40,
   bc43,
   bc47,
   bc49],
  some (some (202, true, true))),
 ([bc55, bc41, bc42], some (some bc240)),
 ([bc55, bc41, bc43, bc44, bc45],
  some (some bc240)),
 ([bc55, bc41, bc43, bc44, bc46],
  some (some (187, true, true))),
 ([bc55, bc41, bc43, bc47, bc48],
  some (some bc240)),
 ([bc55, bc41, bc43, bc47, bc49],
  some (some (191, true, true)))]
private def goalCodes9_5_29 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc58, (206, false, true), bc53], some (some bc241)),
 ([bc58, (206, false, true), bc54], some (some bc241)),
 ([bc58, bc50, bc51, (208, false, true), bc53],
  some (some bc241)),
 ([bc58, bc50, bc51, (208, false, true), bc54],
  some (some bc241)),
 ([bc58, bc50, bc51, (208, true, false), bc53],
  some (some (212, false, true))),
 ([bc58, bc50, bc51, (208, true, false), bc54],
  some (some (212, false, true))),
 ([bc58, bc50, bc52, (213, true, true), bc53],
  some (some bc241)),
 ([bc58, bc50, bc52, (213, true, true), bc54],
  some (some bc241)),
 ([bc58, bc50, bc52, (213, false, false), bc53],
  some (some (215, false, true))),
 ([bc58, bc50, bc52, (213, false, false), bc54],
  some (some (215, false, true)))]
private def goalCodes9_5_32 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes9_4_42
private def goalCodes9_5_34 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc210, bc2, bc176], some (some bc242)),
 ([bc210, bc2, bc177], some (some (534, true, false))),
 ([bc210, bc5, bc178], some (some bc242)),
 ([bc210, bc5, bc179], some (some (535, true, false))),
 ([bc211, bc212, bc213, bc2, bc176],
  some (some bc242)),
 ([bc211, bc212, bc213, bc2, bc177],
  some (some (534, true, false))),
 ([bc211, bc212, bc213, bc5, bc178],
  some (some bc242)),
 ([bc211, bc212, bc213, bc5, bc179],
  some (some (535, true, false))),
 ([bc211, bc212, bc214, bc2, bc176],
  some (some (536, true, false))),
 ([bc211, bc212, bc214, bc2, bc177],
  some (some (537, true, false))),
 ([bc211, bc212, bc214, bc5, bc178],
  some (some (536, true, false))),
 ([bc211, bc212, bc214, bc5, bc179],
  some (some (538, true, false))),
 ([bc211, bc215, bc216, bc2, bc176],
  some (some bc242)),
 ([bc211, bc215, bc216, bc2, bc177],
  some (some (534, true, false))),
 ([bc211, bc215, bc216, bc5, bc178],
  some (some bc242)),
 ([bc211, bc215, bc216, bc5, bc179],
  some (some (535, true, false))),
 ([bc211, bc215, bc217, bc2, bc176],
  some (some (539, true, false))),
 ([bc211, bc215, bc217, bc2, bc177],
  some (some (540, true, false))),
 ([bc211, bc215, bc217, bc5, bc178],
  some (some (539, true, false))),
 ([bc211, bc215, bc217, bc5, bc179],
  some (some (541, true, false)))]
private def goalCodes9_5_35 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc210, bc180, bc181], some (some bc243)),
 ([bc210, bc180, bc182], some (some (543, true, false))),
 ([bc210, bc183, bc184], some (some bc243)),
 ([bc210, bc183, bc185], some (some (544, true, false))),
 ([bc211, bc212, bc213, bc180, bc181],
  some (some bc243)),
 ([bc211, bc212, bc213, bc180, bc182],
  some (some (543, true, false))),
 ([bc211, bc212, bc213, bc183, bc184],
  some (some bc243)),
 ([bc211, bc212, bc213, bc183, bc185],
  some (some (544, true, false))),
 ([bc211, bc212, bc214, bc180, bc181],
  some (some (545, true, false))),
 ([bc211, bc212, bc214, bc180, bc182],
  some (some (546, true, false))),
 ([bc211, bc212, bc214, bc183, bc184],
  some (some (545, true, false))),
 ([bc211, bc212, bc214, bc183, bc185],
  some (some (547, true, false))),
 ([bc211, bc215, bc216, bc180, bc181],
  some (some bc243)),
 ([bc211, bc215, bc216, bc180, bc182],
  some (some (543, true, false))),
 ([bc211, bc215, bc216, bc183, bc184],
  some (some bc243)),
 ([bc211, bc215, bc216, bc183, bc185],
  some (some (544, true, false))),
 ([bc211, bc215, bc217, bc180, bc181],
  some (some (548, true, false))),
 ([bc211, bc215, bc217, bc180, bc182],
  some (some (549, true, false))),
 ([bc211, bc215, bc217, bc183, bc184],
  some (some (548, true, false))),
 ([bc211, bc215, bc217, bc183, bc185],
  some (some (550, true, false)))]
private def goalCodes9_5_36 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc180, bc186, bc210], some (some bc230)),
 ([bc180, bc186, bc211], some (some bc230)),
 ([bc180, bc187, bc210], some (some (487, false, false))),
 ([bc180, bc187, bc211], some (some (487, false, false))),
 ([bc183, bc188, bc210], some (some bc230)),
 ([bc183, bc188, bc211], some (some bc230)),
 ([bc183, bc189, bc210], some (some (488, false, false))),
 ([bc183, bc189, bc211], some (some (488, false, false)))]
private def goalCodes9_5_38 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes9_4_48
private def goalCodes9_5_39 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes9_4_49
private def goalCodes9_5_40 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes9_4_50
private def goalCodes9_5_42 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([bc61, bc62], some (some (227, false, false))),
 ([bc61, (176, true, false)], some none),
 ([bc63, (228, true, true)], some (some (227, false, false))),
 ([bc63, (228, false, false)], some (some (230, false, false)))]
private def goalCodes9_6_0 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := goalCodes9_4_0
private def cutCodes9_4 : List (ℕ × Bool × Bool) := [(7, true, false), (177, true, true), (296, false, true), bc62]
private def cutCodes9_5 : List (ℕ × Bool × Bool) := [(7, true, false), (177, true, true), (296, true, false), (176, true, false)]
private def cutCodes9_6 : List (ℕ × Bool × Bool) := [(7, true, false), (177, true, true), (296, true, false), bc62]

private abbrev goalSpec9_4_35 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 4))[35-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_4_35 : trunkGoalBranches (trunkCatalog.states 9) 4 35 = goalCodes9_4_35.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 9).context goalSpec9_4_35 = _
  exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_4_35
    endpointInput9_26 endpointInput9_27 (([bc82] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes9_26.map decodeEndpoint9) (endpointCodes9_27.map decodeEndpoint9)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_26 hEndpoint9_27).trans
    (by decide +kernel)

private abbrev goalSpec9_4_37 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 4))[37-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_4_37 : trunkGoalBranches (trunkCatalog.states 9) 4 37 = goalCodes9_4_37.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 9).context goalSpec9_4_37 = _
  exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_4_37
    endpointInput9_28 endpointInput9_29 (([bc224] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes9_28.map decodeEndpoint9) (endpointCodes9_29.map decodeEndpoint9)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_28 hEndpoint9_29).trans
    (by decide +kernel)

private abbrev goalSpec9_4_39 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 4))[39-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_4_39 : trunkGoalBranches (trunkCatalog.states 9) 4 39 = goalCodes9_4_39.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 9).context goalSpec9_4_39 = _
  exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_4_39
    endpointInput9_30 endpointInput9_31 (([bc226] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes9_30.map decodeEndpoint9) (endpointCodes9_31.map decodeEndpoint9)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_30 hEndpoint9_31).trans
    (by decide +kernel)

private abbrev goalSpec9_4_42 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 4))[42-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_4_42 : trunkGoalBranches (trunkCatalog.states 9) 4 42 = goalCodes9_4_42.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 9).context goalSpec9_4_42 = _
  exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_4_42
    endpointInput9_50 endpointInput9_1 (([] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes9_50.map decodeEndpoint9) (endpointCodes9_1.map decodeEndpoint9)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_50 hEndpoint9_1).trans
    (by decide +kernel)

private abbrev goalSpec9_4_44 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 4))[44-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_4_44 : trunkGoalBranches (trunkCatalog.states 9) 4 44 = goalCodes9_4_44.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 9).context goalSpec9_4_44 = _
  exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_4_44
    endpointInput9_51 endpointInput9_52 (([] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes9_51.map decodeEndpoint9) (endpointCodes9_52.map decodeEndpoint9)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_51 hEndpoint9_52).trans
    (by decide +kernel)

private abbrev goalSpec9_4_45 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 4))[45-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_4_45 : trunkGoalBranches (trunkCatalog.states 9) 4 45 = goalCodes9_4_45.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 9).context goalSpec9_4_45 = _
  exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_4_45
    endpointInput9_51 endpointInput9_53 (([] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes9_51.map decodeEndpoint9) (endpointCodes9_53.map decodeEndpoint9)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_51 hEndpoint9_53).trans
    (by decide +kernel)

private abbrev goalSpec9_4_46 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 4))[46-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_4_46 : trunkGoalBranches (trunkCatalog.states 9) 4 46 = goalCodes9_4_46.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 9).context goalSpec9_4_46 = _
  exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_4_46
    endpointInput9_54 endpointInput9_55 (([] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes9_54.map decodeEndpoint9) (endpointCodes9_55.map decodeEndpoint9)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_54 hEndpoint9_55).trans
    (by decide +kernel)

private abbrev goalSpec9_4_48 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 4))[48-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_4_48 : trunkGoalBranches (trunkCatalog.states 9) 4 48 = goalCodes9_4_48.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 9).context goalSpec9_4_48 = _
  exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_4_48
    endpointInput9_56 endpointInput9_53 (([] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes9_56.map decodeEndpoint9) (endpointCodes9_53.map decodeEndpoint9)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_56 hEndpoint9_53).trans
    (by decide +kernel)

private abbrev goalSpec9_4_49 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 4))[49-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_4_49 : trunkGoalBranches (trunkCatalog.states 9) 4 49 = goalCodes9_4_49.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 9).context goalSpec9_4_49 = _
  exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_4_49
    endpointInput9_56 endpointInput9_23 (([] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes9_56.map decodeEndpoint9) (endpointCodes9_23.map decodeEndpoint9)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_56 hEndpoint9_23).trans
    (by decide +kernel)

private abbrev goalSpec9_4_50 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 4))[50-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_4_50 : trunkGoalBranches (trunkCatalog.states 9) 4 50 = goalCodes9_4_50.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 9).context goalSpec9_4_50 = _
  exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_4_50
    endpointInput9_21 endpointInput9_57 (([] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes9_21.map decodeEndpoint9) (endpointCodes9_57.map decodeEndpoint9)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_21 hEndpoint9_57).trans
    (by decide +kernel)

private abbrev goalSpec9_4_51 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 4))[51-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_4_51 : trunkGoalBranches (trunkCatalog.states 9) 4 51 = goalCodes9_4_51.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 9).context goalSpec9_4_51 = _
  exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_4_51
    endpointInput9_21 endpointInput9_32 (([] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes9_21.map decodeEndpoint9) (endpointCodes9_32.map decodeEndpoint9)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_21 hEndpoint9_32).trans
    (by decide +kernel)

private abbrev goalSpec9_4_52 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 4))[52-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_4_52 : trunkGoalBranches (trunkCatalog.states 9) 4 52 = goalCodes9_4_52.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 9).context goalSpec9_4_52 = _
  exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_4_52
    endpointInput9_33 endpointInput9_23 (([] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes9_33.map decodeEndpoint9) (endpointCodes9_23.map decodeEndpoint9)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_33 hEndpoint9_23).trans
    (by decide +kernel)

private theorem hGoal9_4_0 : trunkGoalBranches (trunkCatalog.states 9) 4 0 = goalCodes9_4_0.map decodeGoalBranch := by
  decide +kernel

private theorem hGoal9_5_0 : trunkGoalBranches (trunkCatalog.states 9) 5 0 = goalCodes9_5_0.map decodeGoalBranch := by
  exact hGoal9_4_0

private abbrev goalSpec9_5_2 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 5))[2-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_5_2 : trunkGoalBranches (trunkCatalog.states 9) 5 2 = goalCodes9_5_2.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 9).context goalSpec9_5_2 = _
  exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_5_2
    endpointInput9_4 endpointInput9_5 (([bc8] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes9_4.map decodeEndpoint9) (endpointCodes9_5.map decodeEndpoint9)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_4 hEndpoint9_5).trans
    (by decide +kernel)

private abbrev goalSpec9_5_5 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 5))[5-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_5_5 : trunkGoalBranches (trunkCatalog.states 9) 5 5 = goalCodes9_5_5.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 9).context goalSpec9_5_5 = _
  exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_5_5
    endpointInput9_6 endpointInput9_7 (([bc15] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes9_6.map decodeEndpoint9) (endpointCodes9_7.map decodeEndpoint9)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_6 hEndpoint9_7).trans
    (by decide +kernel)

private abbrev goalSpec9_5_7 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 5))[7-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_5_7 : trunkGoalBranches (trunkCatalog.states 9) 5 7 = goalCodes9_5_7.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 9).context goalSpec9_5_7 = _
  exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_5_7
    endpointInput9_34 endpointInput9_35 (([bc2] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes9_34.map decodeEndpoint9) (endpointCodes9_35.map decodeEndpoint9)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_34 hEndpoint9_35).trans
    (by decide +kernel)

private abbrev goalSpec9_5_9 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 5))[9-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_5_9 : trunkGoalBranches (trunkCatalog.states 9) 5 9 = goalCodes9_5_9.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 9).context goalSpec9_5_9 = _
  exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_5_9
    endpointInput9_36 endpointInput9_37 (([bc5] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes9_36.map decodeEndpoint9) (endpointCodes9_37.map decodeEndpoint9)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_36 hEndpoint9_37).trans
    (by decide +kernel)

private abbrev goalSpec9_5_12 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 5))[12-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_5_12 : trunkGoalBranches (trunkCatalog.states 9) 5 12 = goalCodes9_5_12.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 9).context goalSpec9_5_12 = _
  exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_5_12
    endpointInput9_58 endpointInput9_59 (([bc210] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes9_58.map decodeEndpoint9) (endpointCodes9_59.map decodeEndpoint9)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_58 hEndpoint9_59).trans
    (by decide +kernel)

private abbrev goalSpec9_5_15 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 5))[15-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_5_15 : trunkGoalBranches (trunkCatalog.states 9) 5 15 = goalCodes9_5_15.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 9).context goalSpec9_5_15 = _
  exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_5_15
    endpointInput9_60 endpointInput9_61 (([bc211] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes9_60.map decodeEndpoint9) (endpointCodes9_61.map decodeEndpoint9)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_60 hEndpoint9_61).trans
    (by decide +kernel)

private abbrev goalSpec9_5_17 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 5))[17-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_5_17 : trunkGoalBranches (trunkCatalog.states 9) 5 17 = goalCodes9_5_17.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 9).context goalSpec9_5_17 = _
  exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_5_17
    endpointInput9_42 endpointInput9_43 (([bc180] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes9_42.map decodeEndpoint9) (endpointCodes9_43.map decodeEndpoint9)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_42 hEndpoint9_43).trans
    (by decide +kernel)

private abbrev goalSpec9_5_19 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 5))[19-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_5_19 : trunkGoalBranches (trunkCatalog.states 9) 5 19 = goalCodes9_5_19.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 9).context goalSpec9_5_19 = _
  exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_5_19
    endpointInput9_44 endpointInput9_45 (([bc183] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes9_44.map decodeEndpoint9) (endpointCodes9_45.map decodeEndpoint9)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_44 hEndpoint9_45).trans
    (by decide +kernel)

private abbrev goalSpec9_5_22 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 5))[22-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_5_22 : trunkGoalBranches (trunkCatalog.states 9) 5 22 = goalCodes9_5_22.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 9).context goalSpec9_5_22 = _
  exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_5_22
    endpointInput9_46 endpointInput9_47 (([bc190] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes9_46.map decodeEndpoint9) (endpointCodes9_47.map decodeEndpoint9)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_46 hEndpoint9_47).trans
    (by decide +kernel)

private abbrev goalSpec9_5_24 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 5))[24-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_5_24 : trunkGoalBranches (trunkCatalog.states 9) 5 24 = goalCodes9_5_24.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 9).context goalSpec9_5_24 = _
  exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_5_24
    endpointInput9_48 endpointInput9_49 (([bc193] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes9_48.map decodeEndpoint9) (endpointCodes9_49.map decodeEndpoint9)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_48 hEndpoint9_49).trans
    (by decide +kernel)

private abbrev goalSpec9_5_27 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 5))[27-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_5_27 : trunkGoalBranches (trunkCatalog.states 9) 5 27 = goalCodes9_5_27.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 9).context goalSpec9_5_27 = _
  exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_5_27
    endpointInput9_17 endpointInput9_18 (([bc55] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes9_17.map decodeEndpoint9) (endpointCodes9_18.map decodeEndpoint9)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_17 hEndpoint9_18).trans
    (by decide +kernel)

private abbrev goalSpec9_5_29 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 5))[29-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_5_29 : trunkGoalBranches (trunkCatalog.states 9) 5 29 = goalCodes9_5_29.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 9).context goalSpec9_5_29 = _
  exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_5_29
    endpointInput9_19 endpointInput9_20 (([bc58] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes9_19.map decodeEndpoint9) (endpointCodes9_20.map decodeEndpoint9)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_19 hEndpoint9_20).trans
    (by decide +kernel)

private abbrev goalSpec9_5_32 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 5))[32-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_5_32 : trunkGoalBranches (trunkCatalog.states 9) 5 32 = goalCodes9_5_32.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 9) 5 32 = trunkGoalBranches (trunkCatalog.states 9) 4 42 := by
      apply congrArg (trunkBranches (trunkCatalog.states 9).context)
      decide +kernel
    exact he.trans hGoal9_4_42
  | change trunkBranches (trunkCatalog.states 9).context goalSpec9_5_32 = _
    exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_5_32
      endpointInput9_50 endpointInput9_1 (([] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
      (endpointCodes9_50.map decodeEndpoint9) (endpointCodes9_1.map decodeEndpoint9)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_50 hEndpoint9_1).trans
      (by decide +kernel)

private abbrev goalSpec9_5_34 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 5))[34-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_5_34 : trunkGoalBranches (trunkCatalog.states 9) 5 34 = goalCodes9_5_34.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 9).context goalSpec9_5_34 = _
  exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_5_34
    endpointInput9_62 endpointInput9_52 (([] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes9_62.map decodeEndpoint9) (endpointCodes9_52.map decodeEndpoint9)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_62 hEndpoint9_52).trans
    (by decide +kernel)

private abbrev goalSpec9_5_35 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 5))[35-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_5_35 : trunkGoalBranches (trunkCatalog.states 9) 5 35 = goalCodes9_5_35.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 9).context goalSpec9_5_35 = _
  exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_5_35
    endpointInput9_62 endpointInput9_53 (([] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes9_62.map decodeEndpoint9) (endpointCodes9_53.map decodeEndpoint9)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_62 hEndpoint9_53).trans
    (by decide +kernel)

private abbrev goalSpec9_5_36 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 5))[36-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_5_36 : trunkGoalBranches (trunkCatalog.states 9) 5 36 = goalCodes9_5_36.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 9).context goalSpec9_5_36 = _
  exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_5_36
    endpointInput9_54 endpointInput9_63 (([] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes9_54.map decodeEndpoint9) (endpointCodes9_63.map decodeEndpoint9)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_54 hEndpoint9_63).trans
    (by decide +kernel)

private abbrev goalSpec9_5_38 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 5))[38-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_5_38 : trunkGoalBranches (trunkCatalog.states 9) 5 38 = goalCodes9_5_38.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 9) 5 38 = trunkGoalBranches (trunkCatalog.states 9) 4 48 := by
      apply congrArg (trunkBranches (trunkCatalog.states 9).context)
      decide +kernel
    exact he.trans hGoal9_4_48
  | change trunkBranches (trunkCatalog.states 9).context goalSpec9_5_38 = _
    exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_5_38
      endpointInput9_56 endpointInput9_53 (([] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
      (endpointCodes9_56.map decodeEndpoint9) (endpointCodes9_53.map decodeEndpoint9)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_56 hEndpoint9_53).trans
      (by decide +kernel)

private abbrev goalSpec9_5_39 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 5))[39-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_5_39 : trunkGoalBranches (trunkCatalog.states 9) 5 39 = goalCodes9_5_39.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 9) 5 39 = trunkGoalBranches (trunkCatalog.states 9) 4 49 := by
      apply congrArg (trunkBranches (trunkCatalog.states 9).context)
      decide +kernel
    exact he.trans hGoal9_4_49
  | change trunkBranches (trunkCatalog.states 9).context goalSpec9_5_39 = _
    exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_5_39
      endpointInput9_56 endpointInput9_23 (([] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
      (endpointCodes9_56.map decodeEndpoint9) (endpointCodes9_23.map decodeEndpoint9)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_56 hEndpoint9_23).trans
      (by decide +kernel)

private abbrev goalSpec9_5_40 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 5))[40-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_5_40 : trunkGoalBranches (trunkCatalog.states 9) 5 40 = goalCodes9_5_40.map decodeGoalBranch := by
  first
  | have he : trunkGoalBranches (trunkCatalog.states 9) 5 40 = trunkGoalBranches (trunkCatalog.states 9) 4 50 := by
      apply congrArg (trunkBranches (trunkCatalog.states 9).context)
      decide +kernel
    exact he.trans hGoal9_4_50
  | change trunkBranches (trunkCatalog.states 9).context goalSpec9_5_40 = _
    exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_5_40
      endpointInput9_21 endpointInput9_57 (([] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
      (endpointCodes9_21.map decodeEndpoint9) (endpointCodes9_57.map decodeEndpoint9)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_21 hEndpoint9_57).trans
      (by decide +kernel)

private abbrev goalSpec9_5_42 : Section14Spec := ((trunkSpecs (trunkPlanAt (trunkCatalog.states 9) 5))[42-1]?.getD (⟨([],[]),false,([],[]),false,false,[]⟩ : Section14Spec))

private theorem hGoal9_5_42 : trunkGoalBranches (trunkCatalog.states 9) 5 42 = goalCodes9_5_42.map decodeGoalBranch := by
  change trunkBranches (trunkCatalog.states 9).context goalSpec9_5_42 = _
  exact (cachedBranches_eq (trunkCatalog.states 9).context goalSpec9_5_42
    endpointInput9_22 endpointInput9_23 (([] : List (ℕ × Bool × Bool)).map decodeThresholdBound)
    (endpointCodes9_22.map decodeEndpoint9) (endpointCodes9_23.map decodeEndpoint9)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hEndpoint9_22 hEndpoint9_23).trans
    (by decide +kernel)

private theorem hGoal9_6_0 : trunkGoalBranches (trunkCatalog.states 9) 6 0 = goalCodes9_6_0.map decodeGoalBranch := by
  exact hGoal9_4_0

private theorem hCut9_4 : (trunkPlanAt (trunkCatalog.states 9) 4).cuts = cutCodes9_4.map decodeThresholdBound := by decide +kernel

private theorem hCut9_5 : (trunkPlanAt (trunkCatalog.states 9) 5).cuts = cutCodes9_5.map decodeThresholdBound := by decide +kernel

private theorem hCut9_6 : (trunkPlanAt (trunkCatalog.states 9) 6).cuts = cutCodes9_6.map decodeThresholdBound := by decide +kernel

private def codedGoals9 (pi goal : ℕ) : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) :=
  if pi = 4 ∧ goal = 35 then goalCodes9_4_35 else
  if pi = 4 ∧ goal = 37 then goalCodes9_4_37 else
  if pi = 4 ∧ goal = 39 then goalCodes9_4_39 else
  if pi = 4 ∧ goal = 42 then goalCodes9_4_42 else
  if pi = 4 ∧ goal = 44 then goalCodes9_4_44 else
  if pi = 4 ∧ goal = 45 then goalCodes9_4_45 else
  if pi = 4 ∧ goal = 46 then goalCodes9_4_46 else
  if pi = 4 ∧ goal = 48 then goalCodes9_4_48 else
  if pi = 4 ∧ goal = 49 then goalCodes9_4_49 else
  if pi = 4 ∧ goal = 50 then goalCodes9_4_50 else
  if pi = 4 ∧ goal = 51 then goalCodes9_4_51 else
  if pi = 4 ∧ goal = 52 then goalCodes9_4_52 else
  if pi = 4 ∧ goal = 0 then goalCodes9_4_0 else
  if pi = 5 ∧ goal = 0 then goalCodes9_5_0 else
  if pi = 5 ∧ goal = 2 then goalCodes9_5_2 else
  if pi = 5 ∧ goal = 5 then goalCodes9_5_5 else
  if pi = 5 ∧ goal = 7 then goalCodes9_5_7 else
  if pi = 5 ∧ goal = 9 then goalCodes9_5_9 else
  if pi = 5 ∧ goal = 12 then goalCodes9_5_12 else
  if pi = 5 ∧ goal = 15 then goalCodes9_5_15 else
  if pi = 5 ∧ goal = 17 then goalCodes9_5_17 else
  if pi = 5 ∧ goal = 19 then goalCodes9_5_19 else
  if pi = 5 ∧ goal = 22 then goalCodes9_5_22 else
  if pi = 5 ∧ goal = 24 then goalCodes9_5_24 else
  if pi = 5 ∧ goal = 27 then goalCodes9_5_27 else
  if pi = 5 ∧ goal = 29 then goalCodes9_5_29 else
  if pi = 5 ∧ goal = 32 then goalCodes9_5_32 else
  if pi = 5 ∧ goal = 34 then goalCodes9_5_34 else
  if pi = 5 ∧ goal = 35 then goalCodes9_5_35 else
  if pi = 5 ∧ goal = 36 then goalCodes9_5_36 else
  if pi = 5 ∧ goal = 38 then goalCodes9_5_38 else
  if pi = 5 ∧ goal = 39 then goalCodes9_5_39 else
  if pi = 5 ∧ goal = 40 then goalCodes9_5_40 else
  if pi = 5 ∧ goal = 42 then goalCodes9_5_42 else
  if pi = 6 ∧ goal = 0 then goalCodes9_6_0 else
  []

private def codedKeys9 : List (ℕ × ℕ) := [(4, 35), (4, 37), (4, 39), (4, 42), (4, 44), (4, 45), (4, 46), (4, 48), (4, 49), (4, 50), (4, 51), (4, 52), (4, 0), (5, 0), (5, 2), (5, 5), (5, 7), (5, 9), (5, 12), (5, 15), (5, 17), (5, 19), (5, 22), (5, 24), (5, 27), (5, 29), (5, 32), (5, 34), (5, 35), (5, 36), (5, 38), (5, 39), (5, 40), (5, 42), (6, 0)]

private theorem hCodedGoals9 (pi goal : ℕ) (hm : (pi,goal) ∈ codedKeys9) : trunkGoalBranches (trunkCatalog.states 9) pi goal = (codedGoals9 pi goal).map decodeGoalBranch := by
  unfold codedGoals9
  by_cases h0 : pi = 4 ∧ goal = 35
  · rw [if_pos h0]
    rcases h0 with ⟨rfl,rfl⟩
    exact hGoal9_4_35
  rw [if_neg h0]
  by_cases h1 : pi = 4 ∧ goal = 37
  · rw [if_pos h1]
    rcases h1 with ⟨rfl,rfl⟩
    exact hGoal9_4_37
  rw [if_neg h1]
  by_cases h2 : pi = 4 ∧ goal = 39
  · rw [if_pos h2]
    rcases h2 with ⟨rfl,rfl⟩
    exact hGoal9_4_39
  rw [if_neg h2]
  by_cases h3 : pi = 4 ∧ goal = 42
  · rw [if_pos h3]
    rcases h3 with ⟨rfl,rfl⟩
    exact hGoal9_4_42
  rw [if_neg h3]
  by_cases h4 : pi = 4 ∧ goal = 44
  · rw [if_pos h4]
    rcases h4 with ⟨rfl,rfl⟩
    exact hGoal9_4_44
  rw [if_neg h4]
  by_cases h5 : pi = 4 ∧ goal = 45
  · rw [if_pos h5]
    rcases h5 with ⟨rfl,rfl⟩
    exact hGoal9_4_45
  rw [if_neg h5]
  by_cases h6 : pi = 4 ∧ goal = 46
  · rw [if_pos h6]
    rcases h6 with ⟨rfl,rfl⟩
    exact hGoal9_4_46
  rw [if_neg h6]
  by_cases h7 : pi = 4 ∧ goal = 48
  · rw [if_pos h7]
    rcases h7 with ⟨rfl,rfl⟩
    exact hGoal9_4_48
  rw [if_neg h7]
  by_cases h8 : pi = 4 ∧ goal = 49
  · rw [if_pos h8]
    rcases h8 with ⟨rfl,rfl⟩
    exact hGoal9_4_49
  rw [if_neg h8]
  by_cases h9 : pi = 4 ∧ goal = 50
  · rw [if_pos h9]
    rcases h9 with ⟨rfl,rfl⟩
    exact hGoal9_4_50
  rw [if_neg h9]
  by_cases h10 : pi = 4 ∧ goal = 51
  · rw [if_pos h10]
    rcases h10 with ⟨rfl,rfl⟩
    exact hGoal9_4_51
  rw [if_neg h10]
  by_cases h11 : pi = 4 ∧ goal = 52
  · rw [if_pos h11]
    rcases h11 with ⟨rfl,rfl⟩
    exact hGoal9_4_52
  rw [if_neg h11]
  by_cases h12 : pi = 4 ∧ goal = 0
  · rw [if_pos h12]
    rcases h12 with ⟨rfl,rfl⟩
    exact hGoal9_4_0
  rw [if_neg h12]
  by_cases h13 : pi = 5 ∧ goal = 0
  · rw [if_pos h13]
    rcases h13 with ⟨rfl,rfl⟩
    exact hGoal9_5_0
  rw [if_neg h13]
  by_cases h14 : pi = 5 ∧ goal = 2
  · rw [if_pos h14]
    rcases h14 with ⟨rfl,rfl⟩
    exact hGoal9_5_2
  rw [if_neg h14]
  by_cases h15 : pi = 5 ∧ goal = 5
  · rw [if_pos h15]
    rcases h15 with ⟨rfl,rfl⟩
    exact hGoal9_5_5
  rw [if_neg h15]
  by_cases h16 : pi = 5 ∧ goal = 7
  · rw [if_pos h16]
    rcases h16 with ⟨rfl,rfl⟩
    exact hGoal9_5_7
  rw [if_neg h16]
  by_cases h17 : pi = 5 ∧ goal = 9
  · rw [if_pos h17]
    rcases h17 with ⟨rfl,rfl⟩
    exact hGoal9_5_9
  rw [if_neg h17]
  by_cases h18 : pi = 5 ∧ goal = 12
  · rw [if_pos h18]
    rcases h18 with ⟨rfl,rfl⟩
    exact hGoal9_5_12
  rw [if_neg h18]
  by_cases h19 : pi = 5 ∧ goal = 15
  · rw [if_pos h19]
    rcases h19 with ⟨rfl,rfl⟩
    exact hGoal9_5_15
  rw [if_neg h19]
  by_cases h20 : pi = 5 ∧ goal = 17
  · rw [if_pos h20]
    rcases h20 with ⟨rfl,rfl⟩
    exact hGoal9_5_17
  rw [if_neg h20]
  by_cases h21 : pi = 5 ∧ goal = 19
  · rw [if_pos h21]
    rcases h21 with ⟨rfl,rfl⟩
    exact hGoal9_5_19
  rw [if_neg h21]
  by_cases h22 : pi = 5 ∧ goal = 22
  · rw [if_pos h22]
    rcases h22 with ⟨rfl,rfl⟩
    exact hGoal9_5_22
  rw [if_neg h22]
  by_cases h23 : pi = 5 ∧ goal = 24
  · rw [if_pos h23]
    rcases h23 with ⟨rfl,rfl⟩
    exact hGoal9_5_24
  rw [if_neg h23]
  by_cases h24 : pi = 5 ∧ goal = 27
  · rw [if_pos h24]
    rcases h24 with ⟨rfl,rfl⟩
    exact hGoal9_5_27
  rw [if_neg h24]
  by_cases h25 : pi = 5 ∧ goal = 29
  · rw [if_pos h25]
    rcases h25 with ⟨rfl,rfl⟩
    exact hGoal9_5_29
  rw [if_neg h25]
  by_cases h26 : pi = 5 ∧ goal = 32
  · rw [if_pos h26]
    rcases h26 with ⟨rfl,rfl⟩
    exact hGoal9_5_32
  rw [if_neg h26]
  by_cases h27 : pi = 5 ∧ goal = 34
  · rw [if_pos h27]
    rcases h27 with ⟨rfl,rfl⟩
    exact hGoal9_5_34
  rw [if_neg h27]
  by_cases h28 : pi = 5 ∧ goal = 35
  · rw [if_pos h28]
    rcases h28 with ⟨rfl,rfl⟩
    exact hGoal9_5_35
  rw [if_neg h28]
  by_cases h29 : pi = 5 ∧ goal = 36
  · rw [if_pos h29]
    rcases h29 with ⟨rfl,rfl⟩
    exact hGoal9_5_36
  rw [if_neg h29]
  by_cases h30 : pi = 5 ∧ goal = 38
  · rw [if_pos h30]
    rcases h30 with ⟨rfl,rfl⟩
    exact hGoal9_5_38
  rw [if_neg h30]
  by_cases h31 : pi = 5 ∧ goal = 39
  · rw [if_pos h31]
    rcases h31 with ⟨rfl,rfl⟩
    exact hGoal9_5_39
  rw [if_neg h31]
  by_cases h32 : pi = 5 ∧ goal = 40
  · rw [if_pos h32]
    rcases h32 with ⟨rfl,rfl⟩
    exact hGoal9_5_40
  rw [if_neg h32]
  by_cases h33 : pi = 5 ∧ goal = 42
  · rw [if_pos h33]
    rcases h33 with ⟨rfl,rfl⟩
    exact hGoal9_5_42
  rw [if_neg h33]
  by_cases h34 : pi = 6 ∧ goal = 0
  · rw [if_pos h34]
    rcases h34 with ⟨rfl,rfl⟩
    exact hGoal9_6_0
  rw [if_neg h34]
  simp_all only [codedKeys9,List.mem_cons,List.mem_nil_iff,or_false,Prod.mk.injEq]

private def codedCuts9 (pi : ℕ) : List (ℕ × Bool × Bool) :=
  if pi = 4 then cutCodes9_4 else
  if pi = 5 then cutCodes9_5 else
  if pi = 6 then cutCodes9_6 else
  []

private theorem hCodedCuts9 (pi goal : ℕ) (hm : (pi,goal) ∈ codedKeys9) : (trunkPlanAt (trunkCatalog.states 9) pi).cuts = (codedCuts9 pi).map decodeThresholdBound := by
  unfold codedCuts9
  by_cases h0 : pi = 4
  · rw [if_pos h0]
    subst pi
    exact hCut9_4
  rw [if_neg h0]
  by_cases h1 : pi = 5
  · rw [if_pos h1]
    subst pi
    exact hCut9_5
  rw [if_neg h1]
  by_cases h2 : pi = 6
  · rw [if_pos h2]
    subst pi
    exact hCut9_6
  rw [if_neg h2]
  simp_all only [codedKeys9,List.mem_cons,List.mem_nil_iff,or_false,Prod.mk.injEq,false_and]

private def codedValid9 (g : TrunkGroup) : Prop := (g.plan,g.goal) ∈ codedKeys9 ∧ codeGroupValid (trunkCatalog.states 9) codedParents9 250 codedCuts9 codedGoals9 g

private theorem codedValid9_sound (g : TrunkGroup) (h : codedValid9 g) : trunkGroupValidFast 9 g :=
  codeGroupValid_sound 9 codedParents9 250 codedCuts9 codedGoals9 g hCodedParents9 hCodedParentLength9 (hCodedCuts9 g.plan g.goal h.1) (hCodedGoals9 g.plan g.goal h.1) h.2



set_option Elab.async false
theorem batch_chunk_0 : ∀ j ∈ List.range 20, codedValid9 (trunkStateData09Part03.getD j ⟨0,[],0,[]⟩) := by
  unfold codedValid9 codeGroupValid
  decide +kernel

theorem batch_chunk_20 : ∀ j ∈ List.range' 20 20, codedValid9 (trunkStateData09Part03.getD j ⟨0,[],0,[]⟩) := by
  unfold codedValid9 codeGroupValid
  decide +kernel

theorem batch_chunk_40 : ∀ j ∈ List.range' 40 20, codedValid9 (trunkStateData09Part03.getD j ⟨0,[],0,[]⟩) := by
  unfold codedValid9 codeGroupValid
  decide +kernel

theorem batch_key (j : ℕ) (hj : j < 60) : codedValid9 (trunkStateData09Part03.getD j ⟨0,[],0,[]⟩) := by
  rcases lt_or_ge j 20 with h0 | h0
  · exact batch_chunk_0 j (List.mem_range.2 (by omega))
  rcases lt_or_ge j 40 with h1 | h1
  · exact batch_chunk_20 j (List.mem_range'.2 ⟨j - 20, by omega, by omega⟩)
  · exact batch_chunk_40 j (List.mem_range'.2 ⟨j - 40, by omega, by omega⟩)

theorem part_length_1 : trunkStateData09Part01.length = 100 := by decide +kernel

theorem part_length_2 : trunkStateData09Part02.length = 100 := by decide +kernel

theorem solution : trunkBindingBatch 9 200 260 := by
  intro i hlo hhi g hg
  change (trunkStateData09Part01 ++ trunkStateData09Part02 ++ trunkStateData09Part03)[i]? = some g at hg
  rw [List.getElem?_append_right (show (trunkStateData09Part01 ++ trunkStateData09Part02).length ≤ i by simp only [List.length_append, part_length_1, part_length_2, Nat.reduceAdd]; omega)] at hg
  simp only [List.length_append, part_length_1, part_length_2, Nat.reduceAdd] at hg
  have hgi := batch_key (i - 200) (by omega)
  have hgv : trunkStateData09Part03.getD (i - 200) ⟨0,[],0,[]⟩ = g := by
    try simp only [Nat.sub_zero]
    rw [List.getD_eq_getElem?_getD, hg]; rfl
  rw [hgv] at hgi
  exact Freiman.trunkFast_correctness.2 9 hPar9 g (codedValid9_sound g hgi)

#print axioms solution
