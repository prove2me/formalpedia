-- Prove2me | solution 1 for Freiman.lowerHistory_inventory_sizes
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-11T02:24:24.28571+00:00
-- url     : https://prove2.me/submissions/3a8e2eac-b4f5-4513-b296-da574268915a

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic

open Freiman

set_option autoImplicit false
set_option maxRecDepth 8192

private theorem ao_paths_L : lowerHistoryPathsL.size = 594 := by
  change lowerHistoryPathsL.toList.length = 594
  rw [List.length_eq_lengthTR]
  rfl
private theorem ao_paths_R : lowerHistoryPathsR.size = 90 := by
  change lowerHistoryPathsR.toList.length = 90
  rw [List.length_eq_lengthTR]
  rfl
private theorem ao_paths_M : lowerHistoryPathsM.size = 312 := by
  change lowerHistoryPathsM.toList.length = 312
  rw [List.length_eq_lengthTR]
  rfl
private theorem ao_paths_X : lowerHistoryPathsX.size = 90 := by
  change lowerHistoryPathsX.toList.length = 90
  rw [List.length_eq_lengthTR]
  rfl
private theorem ao_paths_H : lowerHistoryPathsH.size = 406 := by
  change lowerHistoryPathsH.toList.length = 406
  rw [List.length_eq_lengthTR]
  rfl

private theorem ao_witnesses_01 : lowerHistoryWitnesses01.size = 200 := by
  change lowerHistoryWitnesses01.toList.length = 200
  rw [List.length_eq_lengthTR]
  rfl
private theorem ao_witnesses_02 : lowerHistoryWitnesses02.size = 200 := by
  change lowerHistoryWitnesses02.toList.length = 200
  rw [List.length_eq_lengthTR]
  rfl
private theorem ao_witnesses_03 : lowerHistoryWitnesses03.size = 200 := by
  change lowerHistoryWitnesses03.toList.length = 200
  rw [List.length_eq_lengthTR]
  rfl
private theorem ao_witnesses_04 : lowerHistoryWitnesses04.size = 200 := by
  change lowerHistoryWitnesses04.toList.length = 200
  rw [List.length_eq_lengthTR]
  rfl
private theorem ao_witnesses_05 : lowerHistoryWitnesses05.size = 200 := by
  change lowerHistoryWitnesses05.toList.length = 200
  rw [List.length_eq_lengthTR]
  rfl
private theorem ao_witnesses_06 : lowerHistoryWitnesses06.size = 194 := by
  change lowerHistoryWitnesses06.toList.length = 194
  rw [List.length_eq_lengthTR]
  rfl

private theorem ao_records_L : lowerHistoryRecordsL.size = 1536 := by
  change lowerHistoryRecordsL.toList.length = 1536
  rw [List.length_eq_lengthTR]
  rfl
private theorem ao_records_R : lowerHistoryRecordsR.size = 264 := by
  change lowerHistoryRecordsR.toList.length = 264
  rw [List.length_eq_lengthTR]
  rfl
private theorem ao_records_M : lowerHistoryRecordsM.size = 846 := by
  change lowerHistoryRecordsM.toList.length = 846
  rw [List.length_eq_lengthTR]
  rfl
private theorem ao_records_X : lowerHistoryRecordsX.size = 132 := by
  change lowerHistoryRecordsX.toList.length = 132
  rw [List.length_eq_lengthTR]
  rfl
private theorem ao_records_H : lowerHistoryRecordsH.size = 846 := by
  change lowerHistoryRecordsH.toList.length = 846
  rw [List.length_eq_lengthTR]
  rfl

theorem solution :
    lowerHistoryPaths.size = 1492 ∧ lowerHistoryWitnesses.size = 1194 ∧ lowerHistoryRecords.size = 3624 := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num only [lowerHistoryPaths, Array.size_append,
      ao_paths_L, ao_paths_R, ao_paths_M, ao_paths_X, ao_paths_H]
  · norm_num only [lowerHistoryWitnesses, Array.size_append,
      ao_witnesses_01, ao_witnesses_02, ao_witnesses_03,
      ao_witnesses_04, ao_witnesses_05, ao_witnesses_06]
  · norm_num only [lowerHistoryRecords, Array.size_append,
      ao_records_L, ao_records_R, ao_records_M, ao_records_X, ao_records_H]

#print axioms solution
