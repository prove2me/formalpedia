-- Prove2me | solution 1 for Freiman.lowerHistory_catalog_M
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T10:29:19.249639+00:00
-- url     : https://prove2.me/submissions/b4f86c31-873b-4e6e-8a65-06397ffdd9e2

-- Exact finite catalog equivalence, with symbolic array-to-list distribution before kernel evaluation.
import Definitions.Def_Freiman_lowerHistoryVerification
open Freiman
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option profiler true
set_option Elab.async false
private theorem range_lookup {α : Type} (xs : List α) (d : α) :
    (List.range xs.length).map (fun i => xs[i]?.getD d) = xs := by
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  simp [h₂]
private def key (i : ℕ) : LowerHistoryKey := ((lowerHistoryPathsM[i]?).map lowerHistoryPathKey).getD
  (.mixed,[],([],[]),false,[])
private def indices : List ℕ := [47, 46, 45, 44, 43, 42, 41, 40, 39, 38, 37, 36, 35, 34, 33, 32, 31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 51, 50, 49, 48, 99, 98, 97, 96, 95, 94, 93, 92, 91, 90, 89, 88, 87, 86, 85, 84, 83, 82, 81, 80, 79, 78, 77, 76, 75, 74, 73, 72, 71, 70, 69, 68, 67, 66, 65, 64, 63, 62, 61, 60, 59, 58, 57, 56, 55, 54, 53, 52, 103, 102, 101, 100, 151, 150, 149, 148, 147, 146, 145, 144, 143, 142, 141, 140, 139, 138, 137, 136, 135, 134, 133, 132, 131, 130, 129, 128, 127, 126, 125, 124, 123, 122, 121, 120, 119, 118, 117, 116, 115, 114, 113, 112, 111, 110, 109, 108, 107, 106, 105, 104, 155, 154, 153, 152, 203, 202, 201, 200, 199, 198, 197, 196, 195, 194, 193, 192, 191, 190, 189, 188, 187, 186, 185, 184, 183, 182, 181, 180, 179, 178, 177, 176, 175, 174, 173, 172, 171, 170, 169, 168, 167, 166, 165, 164, 163, 162, 161, 160, 159, 158, 157, 156, 207, 206, 205, 204, 255, 254, 253, 252, 251, 250, 249, 248, 247, 246, 245, 244, 243, 242, 241, 240, 239, 238, 237, 236, 235, 234, 233, 232, 231, 230, 229, 228, 227, 226, 225, 224, 223, 222, 221, 220, 219, 218, 217, 216, 215, 214, 213, 212, 211, 210, 209, 208, 259, 258, 257, 256, 307, 306, 305, 304, 303, 302, 301, 300, 299, 298, 297, 296, 295, 294, 293, 292, 291, 290, 289, 288, 287, 286, 285, 284, 283, 282, 281, 280, 279, 278, 277, 276, 275, 274, 273, 272, 271, 270, 269, 268, 267, 266, 265, 264, 263, 262, 261, 260, 311, 310, 309, 308]
private theorem catalog_eq : lowerHistoryCatalogKeys .mixed = lowerHistoryPathsM.toList.map lowerHistoryPathKey := by
  unfold lowerHistoryCatalogKeys lowerHistoryPaths
  simp only [Array.toList_append,List.filter_append,List.map_append]
  decide +kernel
private theorem generated_eq : lowerHistoryGeneratedKeys .mixed = indices.map key := by
  decide +kernel
private theorem index_perm : indices.Perm (List.range 312) := by
  decide +kernel
private theorem recorded_eq : (List.range 312).map key = lowerHistoryPathsM.toList.map lowerHistoryPathKey := by
  have h := range_lookup (lowerHistoryPathsM.toList.map lowerHistoryPathKey) ((.mixed,[],([],[]),false,[]) : LowerHistoryKey)
  unfold key
  have hs : lowerHistoryPathsM.size = 312 := rfl
  simpa only [List.length_map,Array.length_toList,List.getElem?_map,Array.getElem?_toList,hs] using h
 theorem solution :
    (lowerHistoryGeneratedKeys .mixed).toFinset = (lowerHistoryCatalogKeys .mixed).toFinset := by
  calc
    (lowerHistoryGeneratedKeys .mixed).toFinset = (indices.map key).toFinset := congrArg List.toFinset generated_eq
    _ = ((List.range 312).map key).toFinset := List.toFinset_eq_of_perm _ _ (index_perm.map key)
    _ = (lowerHistoryPathsM.toList.map lowerHistoryPathKey).toFinset := congrArg List.toFinset recorded_eq
    _ = (lowerHistoryCatalogKeys .mixed).toFinset := congrArg List.toFinset catalog_eq.symm
#print axioms solution
