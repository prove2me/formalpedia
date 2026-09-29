-- Prove2me | solution 1 for Freiman.lowerHistory_catalog_H
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T10:29:20.081661+00:00
-- url     : https://prove2.me/submissions/4039e451-cc4c-48de-a497-ad19014f68c7

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
private def key (i : ℕ) : LowerHistoryKey := ((lowerHistoryPathsH[i]?).map lowerHistoryPathKey).getD
  (.initial,[],([],[]),false,[])
private def indices : List ℕ := [167, 156, 163, 166, 165, 164, 161, 162, 159, 160, 157, 158, 154, 155, 143, 147, 152, 153, 150, 151, 148, 149, 146, 145, 144, 142, 131, 138, 141, 140, 139, 136, 137, 134, 135, 132, 133, 129, 130, 118, 122, 127, 128, 125, 126, 123, 124, 121, 120, 119, 117, 107, 114, 116, 115, 112, 113, 110, 111, 108, 109, 105, 106, 95, 98, 103, 104, 101, 102, 99, 100, 97, 96, 84, 91, 94, 93, 92, 89, 90, 87, 88, 85, 86, 83, 73, 80, 82, 81, 78, 79, 76, 77, 74, 75, 72, 70, 71, 59, 63, 68, 69, 66, 67, 64, 65, 62, 61, 60, 57, 58, 46, 50, 55, 56, 53, 54, 51, 52, 49, 48, 47, 44, 45, 35, 39, 42, 43, 40, 41, 38, 37, 36, 24, 31, 34, 33, 32, 29, 30, 27, 28, 25, 26, 13, 17, 22, 23, 20, 21, 18, 19, 16, 15, 14, 11, 12, 2, 6, 9, 10, 7, 8, 5, 4, 3, 0, 1, 192, 181, 188, 191, 190, 189, 186, 187, 184, 185, 182, 183, 179, 180, 168, 172, 177, 178, 175, 176, 173, 174, 171, 170, 169, 193, 200, 203, 202, 201, 198, 199, 196, 197, 194, 195, 204, 205, 212, 214, 213, 210, 211, 208, 209, 206, 207, 215, 359, 348, 355, 358, 357, 356, 353, 354, 351, 352, 349, 350, 346, 347, 335, 339, 344, 345, 342, 343, 340, 341, 338, 337, 336, 334, 323, 330, 333, 332, 331, 328, 329, 326, 327, 324, 325, 321, 322, 310, 314, 319, 320, 317, 318, 315, 316, 313, 312, 311, 309, 299, 306, 308, 307, 304, 305, 302, 303, 300, 301, 297, 298, 287, 290, 295, 296, 293, 294, 291, 292, 289, 288, 276, 283, 286, 285, 284, 281, 282, 279, 280, 277, 278, 275, 265, 272, 274, 273, 270, 271, 268, 269, 266, 267, 264, 262, 263, 251, 255, 260, 261, 258, 259, 256, 257, 254, 253, 252, 249, 250, 238, 242, 247, 248, 245, 246, 243, 244, 241, 240, 239, 229, 234, 237, 236, 235, 232, 233, 230, 231, 218, 222, 227, 228, 225, 226, 223, 224, 221, 220, 219, 216, 217, 382, 373, 378, 381, 380, 379, 376, 377, 374, 375, 371, 372, 360, 364, 369, 370, 367, 368, 365, 366, 363, 362, 361, 383, 390, 393, 392, 391, 388, 389, 386, 387, 384, 385, 394, 395, 402, 404, 403, 400, 401, 398, 399, 396, 397, 405]
private theorem catalog_eq : lowerHistoryCatalogKeys .initial = lowerHistoryPathsH.toList.map lowerHistoryPathKey := by
  unfold lowerHistoryCatalogKeys lowerHistoryPaths
  simp only [Array.toList_append,List.filter_append,List.map_append]
  decide +kernel
private theorem generated_eq : lowerHistoryGeneratedKeys .initial = indices.map key := by
  decide +kernel
private theorem index_perm : indices.Perm (List.range 406) := by
  decide +kernel
private theorem recorded_eq : (List.range 406).map key = lowerHistoryPathsH.toList.map lowerHistoryPathKey := by
  have h := range_lookup (lowerHistoryPathsH.toList.map lowerHistoryPathKey) ((.initial,[],([],[]),false,[]) : LowerHistoryKey)
  unfold key
  have hs : lowerHistoryPathsH.size = 406 := rfl
  simpa only [List.length_map,Array.length_toList,List.getElem?_map,Array.getElem?_toList,hs] using h
 theorem solution :
    (lowerHistoryGeneratedKeys .initial).toFinset = (lowerHistoryCatalogKeys .initial).toFinset := by
  calc
    (lowerHistoryGeneratedKeys .initial).toFinset = (indices.map key).toFinset := congrArg List.toFinset generated_eq
    _ = ((List.range 406).map key).toFinset := List.toFinset_eq_of_perm _ _ (index_perm.map key)
    _ = (lowerHistoryPathsH.toList.map lowerHistoryPathKey).toFinset := congrArg List.toFinset recorded_eq
    _ = (lowerHistoryCatalogKeys .initial).toFinset := congrArg List.toFinset catalog_eq.symm
#print axioms solution
