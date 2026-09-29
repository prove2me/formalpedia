-- Prove2me | solution 1 for Freiman.lowerHistory_row2_catalog_partition
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-14T09:49:11.655485+00:00
-- url     : https://prove2.me/submissions/ca1a7eb6-66d1-46d1-a551-40b4966c8809

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic.NormNum
open Freiman
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
private theorem sizeL : lowerHistoryPathsL.size = 594 := by rfl
private def rowsL : List ℕ := [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
private theorem row_valuesL : lowerHistoryPathsL.toList.map (fun p => p.row) = rowsL := by rfl
private theorem sizeR : lowerHistoryPathsR.size = 90 := by rfl
private def rowsR : List ℕ := [2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2]
private theorem row_valuesR : lowerHistoryPathsR.toList.map (fun p => p.row) = rowsR := by rfl
private theorem sizeM : lowerHistoryPathsM.size = 312 := by rfl
private def rowsM : List ℕ := [3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3]
private theorem row_valuesM : lowerHistoryPathsM.toList.map (fun p => p.row) = rowsM := by rfl
private theorem sizeX : lowerHistoryPathsX.size = 90 := by rfl
private def rowsX : List ℕ := [4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4]
private theorem row_valuesX : lowerHistoryPathsX.toList.map (fun p => p.row) = rowsX := by rfl
private theorem sizeH : lowerHistoryPathsH.size = 406 := by rfl
private def rowsH : List ℕ := [3,1,4,1,1,1,2,3,1,3,1,3,1,4,1,1,1,2,3,1,3,1,3,1,2,3,1,3,1,3,1,4,1,1,1,4,1,1,1,2,3,1,3,1,3,1,4,1,1,1,2,3,1,3,1,3,1,3,1,4,1,1,1,2,3,1,3,1,3,1,3,1,1,2,3,1,3,1,3,1,4,1,1,1,2,3,1,3,1,3,1,4,1,1,1,4,1,1,2,3,1,3,1,3,1,3,1,2,3,1,3,1,3,1,4,1,1,1,4,1,1,1,2,3,1,3,1,3,1,3,1,2,3,1,3,1,3,1,4,1,1,1,1,4,1,1,1,2,3,1,3,1,3,1,3,1,2,3,1,3,1,3,1,4,1,1,1,1,4,1,1,1,2,3,1,3,1,3,1,3,1,2,3,1,3,1,3,1,4,1,1,1,1,2,3,1,3,1,3,1,4,1,1,1,1,2,3,1,3,1,3,1,4,1,1,1,3,1,4,1,1,1,2,3,1,3,1,3,1,2,3,1,3,1,4,1,1,1,4,1,1,1,2,3,1,3,1,3,1,3,1,4,1,1,1,2,3,1,3,1,3,1,3,1,1,2,3,1,3,1,3,1,4,1,1,1,2,3,1,3,1,3,1,4,1,1,1,4,1,1,2,3,1,3,1,3,1,3,1,2,3,1,3,1,3,1,4,1,1,1,4,1,1,1,2,3,1,3,1,3,1,3,1,2,3,1,3,1,3,1,4,1,1,1,1,4,1,1,1,2,3,1,3,1,3,1,3,1,2,3,1,3,1,3,1,4,1,1,1,1,4,1,1,1,2,3,1,3,1,3,1,3,1,2,3,1,3,1,4,1,1,1,1,2,3,1,3,1,3,1,4,1,1,1,1,2,3,1,3,1,3,1,4,1,1,1]
private theorem row_valuesH : lowerHistoryPathsH.toList.map (fun p => p.row) = rowsH := by rfl
private def rowValues : List ℕ := rowsL ++ rowsR ++ rowsM ++ rowsX ++ rowsH
private theorem row_values : lowerHistoryPaths.toList.map (fun p => p.row) = rowValues := by
  simp only [lowerHistoryPaths,Array.toList_append,List.map_append,
    row_valuesL,row_valuesR,row_valuesM,row_valuesX,row_valuesH,rowValues]
private def row2Indices : List ℕ := [594,595,596,597,598,599,600,601,602,603,604,605,606,607,608,609,610,611,612,613,614,615,616,617,618,619,620,621,622,623,624,625,626,627,628,629,630,631,632,633,634,635,636,637,638,639,640,641,642,643,644,645,646,647,648,649,650,651,652,653,654,655,656,657,658,659,660,661,662,663,664,665,666,667,668,669,670,671,672,673,674,675,676,677,678,679,680,681,682,683,1092,1103,1110,1125,1136,1149,1159,1170,1184,1193,1208,1217,1233,1242,1258,1267,1279,1291,1308,1315,1328,1341,1351,1362,1376,1385,1400,1409,1425,1434,1450,1459,1469,1481]
private theorem row_indices :
    (rowValues.zipIdx.filter (fun z => decide (z.1=2))).map Prod.snd = row2Indices := by rfl

private theorem selected_index {α : Type} (xs : List α) (f : α → ℕ)
    (rows : List ℕ) (hm : xs.map f = rows) (p : α) (hp : p ∈ xs) (hrow : f p=2) :
    ∃ i, xs[i]? = some p ∧ i ∈ (rows.zipIdx.filter (fun z => decide (z.1=2))).map Prod.snd := by
  obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp hp
  have hc := congrArg (fun l : List ℕ => l[i]?) hm
  rw [List.getElem?_map,hi,Option.map_some,hrow] at hc
  have hz : (2,i) ∈ rows.zipIdx := List.mk_mem_zipIdx_iff_getElem?.mpr hc.symm
  exact ⟨i,hi,List.mem_map.mpr ⟨(2,i),List.mem_filter.mpr ⟨hz,rfl⟩,rfl⟩⟩
private theorem lookup594 : lowerHistoryPaths[594]? = some lowerHistoryPathsR[0] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup595 : lowerHistoryPaths[595]? = some lowerHistoryPathsR[1] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup596 : lowerHistoryPaths[596]? = some lowerHistoryPathsR[2] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup597 : lowerHistoryPaths[597]? = some lowerHistoryPathsR[3] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup598 : lowerHistoryPaths[598]? = some lowerHistoryPathsR[4] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup599 : lowerHistoryPaths[599]? = some lowerHistoryPathsR[5] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup600 : lowerHistoryPaths[600]? = some lowerHistoryPathsR[6] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup601 : lowerHistoryPaths[601]? = some lowerHistoryPathsR[7] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup602 : lowerHistoryPaths[602]? = some lowerHistoryPathsR[8] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup603 : lowerHistoryPaths[603]? = some lowerHistoryPathsR[9] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup604 : lowerHistoryPaths[604]? = some lowerHistoryPathsR[10] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup605 : lowerHistoryPaths[605]? = some lowerHistoryPathsR[11] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup606 : lowerHistoryPaths[606]? = some lowerHistoryPathsR[12] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup607 : lowerHistoryPaths[607]? = some lowerHistoryPathsR[13] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup608 : lowerHistoryPaths[608]? = some lowerHistoryPathsR[14] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup609 : lowerHistoryPaths[609]? = some lowerHistoryPathsR[15] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup610 : lowerHistoryPaths[610]? = some lowerHistoryPathsR[16] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup611 : lowerHistoryPaths[611]? = some lowerHistoryPathsR[17] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup612 : lowerHistoryPaths[612]? = some lowerHistoryPathsR[18] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup613 : lowerHistoryPaths[613]? = some lowerHistoryPathsR[19] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup614 : lowerHistoryPaths[614]? = some lowerHistoryPathsR[20] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup615 : lowerHistoryPaths[615]? = some lowerHistoryPathsR[21] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup616 : lowerHistoryPaths[616]? = some lowerHistoryPathsR[22] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup617 : lowerHistoryPaths[617]? = some lowerHistoryPathsR[23] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup618 : lowerHistoryPaths[618]? = some lowerHistoryPathsR[24] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup619 : lowerHistoryPaths[619]? = some lowerHistoryPathsR[25] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup620 : lowerHistoryPaths[620]? = some lowerHistoryPathsR[26] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup621 : lowerHistoryPaths[621]? = some lowerHistoryPathsR[27] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup622 : lowerHistoryPaths[622]? = some lowerHistoryPathsR[28] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup623 : lowerHistoryPaths[623]? = some lowerHistoryPathsR[29] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup624 : lowerHistoryPaths[624]? = some lowerHistoryPathsR[30] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup625 : lowerHistoryPaths[625]? = some lowerHistoryPathsR[31] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup626 : lowerHistoryPaths[626]? = some lowerHistoryPathsR[32] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup627 : lowerHistoryPaths[627]? = some lowerHistoryPathsR[33] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup628 : lowerHistoryPaths[628]? = some lowerHistoryPathsR[34] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup629 : lowerHistoryPaths[629]? = some lowerHistoryPathsR[35] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup630 : lowerHistoryPaths[630]? = some lowerHistoryPathsR[36] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup631 : lowerHistoryPaths[631]? = some lowerHistoryPathsR[37] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup632 : lowerHistoryPaths[632]? = some lowerHistoryPathsR[38] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup633 : lowerHistoryPaths[633]? = some lowerHistoryPathsR[39] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup634 : lowerHistoryPaths[634]? = some lowerHistoryPathsR[40] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup635 : lowerHistoryPaths[635]? = some lowerHistoryPathsR[41] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup636 : lowerHistoryPaths[636]? = some lowerHistoryPathsR[42] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup637 : lowerHistoryPaths[637]? = some lowerHistoryPathsR[43] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup638 : lowerHistoryPaths[638]? = some lowerHistoryPathsR[44] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup639 : lowerHistoryPaths[639]? = some lowerHistoryPathsR[45] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup640 : lowerHistoryPaths[640]? = some lowerHistoryPathsR[46] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup641 : lowerHistoryPaths[641]? = some lowerHistoryPathsR[47] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup642 : lowerHistoryPaths[642]? = some lowerHistoryPathsR[48] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup643 : lowerHistoryPaths[643]? = some lowerHistoryPathsR[49] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup644 : lowerHistoryPaths[644]? = some lowerHistoryPathsR[50] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup645 : lowerHistoryPaths[645]? = some lowerHistoryPathsR[51] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup646 : lowerHistoryPaths[646]? = some lowerHistoryPathsR[52] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup647 : lowerHistoryPaths[647]? = some lowerHistoryPathsR[53] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup648 : lowerHistoryPaths[648]? = some lowerHistoryPathsR[54] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup649 : lowerHistoryPaths[649]? = some lowerHistoryPathsR[55] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup650 : lowerHistoryPaths[650]? = some lowerHistoryPathsR[56] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup651 : lowerHistoryPaths[651]? = some lowerHistoryPathsR[57] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup652 : lowerHistoryPaths[652]? = some lowerHistoryPathsR[58] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup653 : lowerHistoryPaths[653]? = some lowerHistoryPathsR[59] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup654 : lowerHistoryPaths[654]? = some lowerHistoryPathsR[60] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup655 : lowerHistoryPaths[655]? = some lowerHistoryPathsR[61] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup656 : lowerHistoryPaths[656]? = some lowerHistoryPathsR[62] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup657 : lowerHistoryPaths[657]? = some lowerHistoryPathsR[63] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup658 : lowerHistoryPaths[658]? = some lowerHistoryPathsR[64] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup659 : lowerHistoryPaths[659]? = some lowerHistoryPathsR[65] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup660 : lowerHistoryPaths[660]? = some lowerHistoryPathsR[66] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup661 : lowerHistoryPaths[661]? = some lowerHistoryPathsR[67] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup662 : lowerHistoryPaths[662]? = some lowerHistoryPathsR[68] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup663 : lowerHistoryPaths[663]? = some lowerHistoryPathsR[69] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup664 : lowerHistoryPaths[664]? = some lowerHistoryPathsR[70] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup665 : lowerHistoryPaths[665]? = some lowerHistoryPathsR[71] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup666 : lowerHistoryPaths[666]? = some lowerHistoryPathsR[72] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup667 : lowerHistoryPaths[667]? = some lowerHistoryPathsR[73] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup668 : lowerHistoryPaths[668]? = some lowerHistoryPathsR[74] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup669 : lowerHistoryPaths[669]? = some lowerHistoryPathsR[75] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup670 : lowerHistoryPaths[670]? = some lowerHistoryPathsR[76] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup671 : lowerHistoryPaths[671]? = some lowerHistoryPathsR[77] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup672 : lowerHistoryPaths[672]? = some lowerHistoryPathsR[78] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup673 : lowerHistoryPaths[673]? = some lowerHistoryPathsR[79] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup674 : lowerHistoryPaths[674]? = some lowerHistoryPathsR[80] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup675 : lowerHistoryPaths[675]? = some lowerHistoryPathsR[81] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup676 : lowerHistoryPaths[676]? = some lowerHistoryPathsR[82] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup677 : lowerHistoryPaths[677]? = some lowerHistoryPathsR[83] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup678 : lowerHistoryPaths[678]? = some lowerHistoryPathsR[84] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup679 : lowerHistoryPaths[679]? = some lowerHistoryPathsR[85] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup680 : lowerHistoryPaths[680]? = some lowerHistoryPathsR[86] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup681 : lowerHistoryPaths[681]? = some lowerHistoryPathsR[87] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup682 : lowerHistoryPaths[682]? = some lowerHistoryPathsR[88] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup683 : lowerHistoryPaths[683]? = some lowerHistoryPathsR[89] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeR]; decide)
private theorem lookup1092 : lowerHistoryPaths[1092]? = some lowerHistoryPathsH[6] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeH]; decide)
private theorem lookup1103 : lowerHistoryPaths[1103]? = some lowerHistoryPathsH[17] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeH]; decide)
private theorem lookup1110 : lowerHistoryPaths[1110]? = some lowerHistoryPathsH[24] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeH]; decide)
private theorem lookup1125 : lowerHistoryPaths[1125]? = some lowerHistoryPathsH[39] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeH]; decide)
private theorem lookup1136 : lowerHistoryPaths[1136]? = some lowerHistoryPathsH[50] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeH]; decide)
private theorem lookup1149 : lowerHistoryPaths[1149]? = some lowerHistoryPathsH[63] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeH]; decide)
private theorem lookup1159 : lowerHistoryPaths[1159]? = some lowerHistoryPathsH[73] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeH]; decide)
private theorem lookup1170 : lowerHistoryPaths[1170]? = some lowerHistoryPathsH[84] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeH]; decide)
private theorem lookup1184 : lowerHistoryPaths[1184]? = some lowerHistoryPathsH[98] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeH]; decide)
private theorem lookup1193 : lowerHistoryPaths[1193]? = some lowerHistoryPathsH[107] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeH]; decide)
private theorem lookup1208 : lowerHistoryPaths[1208]? = some lowerHistoryPathsH[122] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeH]; decide)
private theorem lookup1217 : lowerHistoryPaths[1217]? = some lowerHistoryPathsH[131] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeH]; decide)
private theorem lookup1233 : lowerHistoryPaths[1233]? = some lowerHistoryPathsH[147] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeH]; decide)
private theorem lookup1242 : lowerHistoryPaths[1242]? = some lowerHistoryPathsH[156] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeH]; decide)
private theorem lookup1258 : lowerHistoryPaths[1258]? = some lowerHistoryPathsH[172] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeH]; decide)
private theorem lookup1267 : lowerHistoryPaths[1267]? = some lowerHistoryPathsH[181] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeH]; decide)
private theorem lookup1279 : lowerHistoryPaths[1279]? = some lowerHistoryPathsH[193] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeH]; decide)
private theorem lookup1291 : lowerHistoryPaths[1291]? = some lowerHistoryPathsH[205] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeH]; decide)
private theorem lookup1308 : lowerHistoryPaths[1308]? = some lowerHistoryPathsH[222] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeH]; decide)
private theorem lookup1315 : lowerHistoryPaths[1315]? = some lowerHistoryPathsH[229] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeH]; decide)
private theorem lookup1328 : lowerHistoryPaths[1328]? = some lowerHistoryPathsH[242] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeH]; decide)
private theorem lookup1341 : lowerHistoryPaths[1341]? = some lowerHistoryPathsH[255] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeH]; decide)
private theorem lookup1351 : lowerHistoryPaths[1351]? = some lowerHistoryPathsH[265] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeH]; decide)
private theorem lookup1362 : lowerHistoryPaths[1362]? = some lowerHistoryPathsH[276] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeH]; decide)
private theorem lookup1376 : lowerHistoryPaths[1376]? = some lowerHistoryPathsH[290] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeH]; decide)
private theorem lookup1385 : lowerHistoryPaths[1385]? = some lowerHistoryPathsH[299] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeH]; decide)
private theorem lookup1400 : lowerHistoryPaths[1400]? = some lowerHistoryPathsH[314] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeH]; decide)
private theorem lookup1409 : lowerHistoryPaths[1409]? = some lowerHistoryPathsH[323] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeH]; decide)
private theorem lookup1425 : lowerHistoryPaths[1425]? = some lowerHistoryPathsH[339] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeH]; decide)
private theorem lookup1434 : lowerHistoryPaths[1434]? = some lowerHistoryPathsH[348] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeH]; decide)
private theorem lookup1450 : lowerHistoryPaths[1450]? = some lowerHistoryPathsH[364] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeH]; decide)
private theorem lookup1459 : lowerHistoryPaths[1459]? = some lowerHistoryPathsH[373] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeH]; decide)
private theorem lookup1469 : lowerHistoryPaths[1469]? = some lowerHistoryPathsH[383] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeH]; decide)
private theorem lookup1481 : lowerHistoryPaths[1481]? = some lowerHistoryPathsH[395] := by
  norm_num only [lowerHistoryPaths,Array.getElem?_append,Array.size_append,sizeL,sizeR,sizeM,sizeX,sizeH]
  exact Array.getElem?_eq_getElem (by rw [sizeH]; decide)
theorem solution : ∀ p ∈ lowerHistoryPaths.toList, p.row = 2 →
  lowerHistorySurvivor p ∨
  p ∈ [lowerHistoryPathsR[0],lowerHistoryPathsR[15],lowerHistoryPathsR[30],lowerHistoryPathsR[45],lowerHistoryPathsR[60],lowerHistoryPathsR[75]] ∨
  p ∈ [lowerHistoryPathsR[1],lowerHistoryPathsR[16],lowerHistoryPathsR[31],lowerHistoryPathsR[46],lowerHistoryPathsR[61],lowerHistoryPathsR[76]] ∨
  p ∈ [lowerHistoryPathsR[2],lowerHistoryPathsR[17],lowerHistoryPathsR[32],lowerHistoryPathsR[47],lowerHistoryPathsR[62],lowerHistoryPathsR[77]] ∨
  p ∈ [lowerHistoryPathsR[3],lowerHistoryPathsR[18],lowerHistoryPathsR[33],lowerHistoryPathsR[48],lowerHistoryPathsR[63],lowerHistoryPathsR[78]] ∨
  p ∈ [lowerHistoryPathsR[4],lowerHistoryPathsR[19],lowerHistoryPathsR[34],lowerHistoryPathsR[49],lowerHistoryPathsR[64],lowerHistoryPathsR[79]] ∨
  p ∈ [lowerHistoryPathsR[5],lowerHistoryPathsR[20],lowerHistoryPathsR[35],lowerHistoryPathsR[50],lowerHistoryPathsR[65],lowerHistoryPathsR[80]] ∨
  p ∈ [lowerHistoryPathsR[6],lowerHistoryPathsR[21],lowerHistoryPathsR[36],lowerHistoryPathsR[51],lowerHistoryPathsR[66],lowerHistoryPathsR[81]] ∨
  p ∈ [lowerHistoryPathsR[7],lowerHistoryPathsR[22],lowerHistoryPathsR[37],lowerHistoryPathsR[52],lowerHistoryPathsR[67],lowerHistoryPathsR[82]] ∨
  p ∈ [lowerHistoryPathsR[8],lowerHistoryPathsR[23],lowerHistoryPathsR[38],lowerHistoryPathsR[53],lowerHistoryPathsR[68],lowerHistoryPathsR[83]] ∨
  p ∈ [lowerHistoryPathsR[9],lowerHistoryPathsR[24],lowerHistoryPathsR[39],lowerHistoryPathsR[54],lowerHistoryPathsR[69],lowerHistoryPathsR[84]] ∨
  p ∈ [lowerHistoryPathsR[10],lowerHistoryPathsR[25],lowerHistoryPathsR[40],lowerHistoryPathsR[55],lowerHistoryPathsR[70],lowerHistoryPathsR[85]] ∨
  p ∈ [lowerHistoryPathsR[11],lowerHistoryPathsR[26],lowerHistoryPathsR[41],lowerHistoryPathsR[56],lowerHistoryPathsR[71],lowerHistoryPathsR[86]] ∨
  p ∈ [lowerHistoryPathsR[12],lowerHistoryPathsR[27],lowerHistoryPathsR[42],lowerHistoryPathsR[57],lowerHistoryPathsR[72],lowerHistoryPathsR[87]] ∨
  p ∈ [lowerHistoryPathsR[13],lowerHistoryPathsR[28],lowerHistoryPathsR[43],lowerHistoryPathsR[58],lowerHistoryPathsR[73],lowerHistoryPathsR[88]] ∨
  p ∈ [lowerHistoryPathsR[14],lowerHistoryPathsR[29],lowerHistoryPathsR[44],lowerHistoryPathsR[59],lowerHistoryPathsR[74],lowerHistoryPathsR[89]] ∨
  p ∈ [lowerHistoryPathsH[6]] ∨
  p ∈ [lowerHistoryPathsH[17],lowerHistoryPathsH[222]] ∨
  p ∈ [lowerHistoryPathsH[24],lowerHistoryPathsH[229]] ∨
  p ∈ [lowerHistoryPathsH[39]] ∨
  p ∈ [lowerHistoryPathsH[50],lowerHistoryPathsH[242]] ∨
  p ∈ [lowerHistoryPathsH[63],lowerHistoryPathsH[255]] ∨
  p ∈ [lowerHistoryPathsH[73],lowerHistoryPathsH[265]] ∨
  p ∈ [lowerHistoryPathsH[84],lowerHistoryPathsH[276]] ∨
  p ∈ [lowerHistoryPathsH[98],lowerHistoryPathsH[290]] ∨
  p ∈ [lowerHistoryPathsH[107],lowerHistoryPathsH[299]] ∨
  p ∈ [lowerHistoryPathsH[122],lowerHistoryPathsH[314]] ∨
  p ∈ [lowerHistoryPathsH[131],lowerHistoryPathsH[323]] ∨
  p ∈ [lowerHistoryPathsH[147],lowerHistoryPathsH[339]] ∨
  p ∈ [lowerHistoryPathsH[156],lowerHistoryPathsH[348]] ∨
  p ∈ [lowerHistoryPathsH[172],lowerHistoryPathsH[364]] ∨
  p ∈ [lowerHistoryPathsH[193],lowerHistoryPathsH[383]] ∨
  p ∈ [lowerHistoryPathsH[205],lowerHistoryPathsH[395]] := by
  intro p hp hrow
  obtain ⟨i,hi,hm⟩ := selected_index lowerHistoryPaths.toList (fun p => p.row) rowValues row_values p hp hrow
  rw [row_indices] at hm
  rw [Array.getElem?_toList] at hi
  simp only [row2Indices,List.mem_cons,List.mem_nil_iff,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [lookup594] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inl (List.mem_cons_self))
  · rw [lookup595] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inl (List.mem_cons_self)))
  · rw [lookup596] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_self))))
  · rw [lookup597] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_self)))))
  · rw [lookup598] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_self))))))
  · rw [lookup599] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_self)))))))
  · rw [lookup600] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_self))))))))
  · rw [lookup601] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_self)))))))))
  · rw [lookup602] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_self))))))))))
  · rw [lookup603] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_self)))))))))))
  · rw [lookup604] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_self))))))))))))
  · rw [lookup605] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_self)))))))))))))
  · rw [lookup606] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_self))))))))))))))
  · rw [lookup607] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_self)))))))))))))))
  · rw [lookup608] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_self))))))))))))))))
  · rw [lookup609] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_self)))
  · rw [lookup610] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_self))))
  · rw [lookup611] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_self)))))
  · rw [lookup612] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_self))))))
  · rw [lookup613] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_self)))))))
  · rw [lookup614] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_self))))))))
  · rw [lookup615] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))
  · rw [lookup616] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))
  · rw [lookup617] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))
  · rw [lookup618] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))
  · rw [lookup619] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))
  · rw [lookup620] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))
  · rw [lookup621] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))
  · rw [lookup622] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))
  · rw [lookup623] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))
  · rw [lookup624] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))
  · rw [lookup625] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))
  · rw [lookup626] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))
  · rw [lookup627] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))
  · rw [lookup628] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))
  · rw [lookup629] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))
  · rw [lookup630] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))
  · rw [lookup631] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))
  · rw [lookup632] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))
  · rw [lookup633] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))
  · rw [lookup634] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))
  · rw [lookup635] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))
  · rw [lookup636] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))
  · rw [lookup637] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))
  · rw [lookup638] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))
  · rw [lookup639] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))
  · rw [lookup640] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))
  · rw [lookup641] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))
  · rw [lookup642] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))
  · rw [lookup643] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))
  · rw [lookup644] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))
  · rw [lookup645] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))
  · rw [lookup646] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))
  · rw [lookup647] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))
  · rw [lookup648] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))
  · rw [lookup649] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))
  · rw [lookup650] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))
  · rw [lookup651] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))
  · rw [lookup652] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))
  · rw [lookup653] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))
  · rw [lookup654] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))
  · rw [lookup655] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))
  · rw [lookup656] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))
  · rw [lookup657] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))
  · rw [lookup658] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))
  · rw [lookup659] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))
  · rw [lookup660] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))
  · rw [lookup661] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))
  · rw [lookup662] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))
  · rw [lookup663] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))
  · rw [lookup664] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))
  · rw [lookup665] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))
  · rw [lookup666] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))
  · rw [lookup667] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))
  · rw [lookup668] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))))
  · rw [lookup669] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))
  · rw [lookup670] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))
  · rw [lookup671] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))
  · rw [lookup672] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))
  · rw [lookup673] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))
  · rw [lookup674] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))
  · rw [lookup675] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))
  · rw [lookup676] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))
  · rw [lookup677] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))
  · rw [lookup678] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))
  · rw [lookup679] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))
  · rw [lookup680] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))
  · rw [lookup681] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))
  · rw [lookup682] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))))
  · rw [lookup683] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))))
  · rw [lookup1092] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_self)))))))))))))))))
  · rw [lookup1103] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_self))))))))))))))))))
  · rw [lookup1110] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_self)))))))))))))))))))
  · rw [lookup1125] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_self))))))))))))))))))))
  · rw [lookup1136] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_self)))))))))))))))))))))
  · rw [lookup1149] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_self))))))))))))))))))))))
  · rw [lookup1159] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_self)))))))))))))))))))))))
  · rw [lookup1170] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_self))))))))))))))))))))))))
  · rw [lookup1184] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_self)))))))))))))))))))))))))
  · rw [lookup1193] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_self))))))))))))))))))))))))))
  · rw [lookup1208] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_self)))))))))))))))))))))))))))
  · rw [lookup1217] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_self))))))))))))))))))))))))))))
  · rw [lookup1233] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_self)))))))))))))))))))))))))))))
  · rw [lookup1242] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_self))))))))))))))))))))))))))))))
  · rw [lookup1258] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_self)))))))))))))))))))))))))))))))
  · rw [lookup1267] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inl (by unfold lowerHistorySurvivor; decide)
  · rw [lookup1279] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_self))))))))))))))))))))))))))))))))
  · rw [lookup1291] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (List.mem_cons_self))))))))))))))))))))))))))))))))
  · rw [lookup1308] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))
  · rw [lookup1315] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))))
  · rw [lookup1328] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))))))
  · rw [lookup1341] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))))))
  · rw [lookup1351] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))))))))
  · rw [lookup1362] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))))))))
  · rw [lookup1376] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))))))))))
  · rw [lookup1385] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))))))))))
  · rw [lookup1400] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))))))))))))
  · rw [lookup1409] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))))))))))))
  · rw [lookup1425] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))))))))))))))
  · rw [lookup1434] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))))))))))))))
  · rw [lookup1450] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))))))))))))))))
  · rw [lookup1459] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inl (by unfold lowerHistorySurvivor; decide)
  · rw [lookup1469] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))))))))))))))))
  · rw [lookup1481] at hi
    have heq := Option.some.inj hi
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))))))))))))))))
#print axioms solution
