-- Prove2me | solution 1 for BS2_b3ba934b_RI_checked_length6
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T19:52:42.028084+00:00
-- url     : https://prove2.me/submissions/79bd9130-a4c4-44eb-a6fa-2939c94348d7

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
import Theorems.Thm_BS2_b3ba934b_RI_Batch_0997866a336d
import Theorems.Thm_BS2_b3ba934b_RI_Batch_618c58463e44
import Theorems.Thm_BS2_b3ba934b_RI_Batch_75d723d2897e
import Theorems.Thm_BS2_b3ba934b_RI_Batch_83689d4e5d10
import Theorems.Thm_BS2_b3ba934b_RI_Batch_8b120256d811
import Theorems.Thm_BS2_b3ba934b_RI_Batch_8e2ebec860a5
import Theorems.Thm_BS2_b3ba934b_RI_Batch_cc30a0ee5240
import Theorems.Thm_BS2_b3ba934b_RI_checked_type6_27
import Theorems.Thm_BS2_b3ba934b_RI_checked_type6_28
import Theorems.Thm_BS2_b3ba934b_RI_checked_type6_29
import Theorems.Thm_BS2_b3ba934b_RI_checked_type6_30
import Theorems.Thm_BS2_b3ba934b_RI_checked_type6_31
import Theorems.Thm_BS2_b3ba934b_RI_checked_type6_32
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup
attribute [local irreducible] ThreeBoundRecordLookup.checkCasesFrom ThreeBoundRecordLookup.checkCasesChunk ThreeBoundRecordLookup.checkTypes ThreeBoundRecordLookup.checkLength ThreeBoundEndpoint40Records.tree

theorem solution : ThreeBoundRecordLookup.checkLength ThreeBoundEndpoint40Records.tree 6=true := by
  have ri_inline_checked_length6_coverage_tail029 : (([[5,5,5,5,5,7],[5,5,5,5,6,7],[5,5,5,5,7,7],[5,5,5,7,7,7]] : List (List ThreeBoundQ2.Kind)).all (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree))=true := by
    exact ThreeBoundRecordLookup.all_cons_of _ _ _ BS2_b3ba934b_RI_checked_type6_29 (ThreeBoundRecordLookup.all_cons_of _ _ _ BS2_b3ba934b_RI_checked_type6_30 (ThreeBoundRecordLookup.all_cons_of _ _ _ BS2_b3ba934b_RI_checked_type6_31 (ThreeBoundRecordLookup.all_cons_of _ _ _ BS2_b3ba934b_RI_checked_type6_32 (rfl))))
  have ri_inline_checked_length6_coverage_tail025 : (([[4,5,5,5,5,7],[4,5,5,5,7,7],[5,5,5,5,5,5],[5,5,5,5,5,6],[5,5,5,5,5,7],[5,5,5,5,6,7],[5,5,5,5,7,7],[5,5,5,7,7,7]] : List (List ThreeBoundQ2.Kind)).all (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree))=true := by
    exact ThreeBoundRecordLookup.all_cons_of _ _ _ (BS2_b3ba934b_RI_Batch_8e2ebec860a5.2.2.2.2.2.2.2.1) (ThreeBoundRecordLookup.all_cons_of _ _ _ (BS2_b3ba934b_RI_Batch_75d723d2897e.1) (ThreeBoundRecordLookup.all_cons_of _ _ _ BS2_b3ba934b_RI_checked_type6_27 (ThreeBoundRecordLookup.all_cons_of _ _ _ BS2_b3ba934b_RI_checked_type6_28 (ri_inline_checked_length6_coverage_tail029))))
  have ri_inline_checked_length6_coverage_tail021 : (([[4,4,5,5,5,5],[4,4,5,5,5,7],[4,5,5,5,5,5],[4,5,5,5,5,6],[4,5,5,5,5,7],[4,5,5,5,7,7],[5,5,5,5,5,5],[5,5,5,5,5,6],[5,5,5,5,5,7],[5,5,5,5,6,7],[5,5,5,5,7,7],[5,5,5,7,7,7]] : List (List ThreeBoundQ2.Kind)).all (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree))=true := by
    exact ThreeBoundRecordLookup.all_cons_of _ _ _ (BS2_b3ba934b_RI_Batch_8e2ebec860a5.2.2.2.1) (ThreeBoundRecordLookup.all_cons_of _ _ _ (BS2_b3ba934b_RI_Batch_8e2ebec860a5.2.2.2.2.1) (ThreeBoundRecordLookup.all_cons_of _ _ _ (BS2_b3ba934b_RI_Batch_8e2ebec860a5.2.2.2.2.2.1) (ThreeBoundRecordLookup.all_cons_of _ _ _ (BS2_b3ba934b_RI_Batch_8e2ebec860a5.2.2.2.2.2.2.1) (ri_inline_checked_length6_coverage_tail025))))
  have ri_inline_checked_length6_coverage_tail017 : (([[3,4,5,5,5,5],[3,5,5,5,5,5],[3,5,5,5,5,7],[4,4,4,5,5,5],[4,4,5,5,5,5],[4,4,5,5,5,7],[4,5,5,5,5,5],[4,5,5,5,5,6],[4,5,5,5,5,7],[4,5,5,5,7,7],[5,5,5,5,5,5],[5,5,5,5,5,6],[5,5,5,5,5,7],[5,5,5,5,6,7],[5,5,5,5,7,7],[5,5,5,7,7,7]] : List (List ThreeBoundQ2.Kind)).all (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree))=true := by
    exact ThreeBoundRecordLookup.all_cons_of _ _ _ (BS2_b3ba934b_RI_Batch_0997866a336d.2.2.2.2.2.2.2.1) (ThreeBoundRecordLookup.all_cons_of _ _ _ (BS2_b3ba934b_RI_Batch_8e2ebec860a5.1) (ThreeBoundRecordLookup.all_cons_of _ _ _ (BS2_b3ba934b_RI_Batch_8e2ebec860a5.2.1) (ThreeBoundRecordLookup.all_cons_of _ _ _ (BS2_b3ba934b_RI_Batch_8e2ebec860a5.2.2.1) (ri_inline_checked_length6_coverage_tail021))))
  have ri_inline_checked_length6_coverage_tail013 : (([[2,5,5,5,5,5],[2,5,5,5,5,6],[2,5,5,5,5,7],[2,5,5,5,7,7],[3,4,5,5,5,5],[3,5,5,5,5,5],[3,5,5,5,5,7],[4,4,4,5,5,5],[4,4,5,5,5,5],[4,4,5,5,5,7],[4,5,5,5,5,5],[4,5,5,5,5,6],[4,5,5,5,5,7],[4,5,5,5,7,7],[5,5,5,5,5,5],[5,5,5,5,5,6],[5,5,5,5,5,7],[5,5,5,5,6,7],[5,5,5,5,7,7],[5,5,5,7,7,7]] : List (List ThreeBoundQ2.Kind)).all (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree))=true := by
    exact ThreeBoundRecordLookup.all_cons_of _ _ _ (BS2_b3ba934b_RI_Batch_0997866a336d.2.2.2.1) (ThreeBoundRecordLookup.all_cons_of _ _ _ (BS2_b3ba934b_RI_Batch_0997866a336d.2.2.2.2.1) (ThreeBoundRecordLookup.all_cons_of _ _ _ (BS2_b3ba934b_RI_Batch_0997866a336d.2.2.2.2.2.1) (ThreeBoundRecordLookup.all_cons_of _ _ _ (BS2_b3ba934b_RI_Batch_0997866a336d.2.2.2.2.2.2.1) (ri_inline_checked_length6_coverage_tail017))))
  have ri_inline_checked_length6_coverage_tail009 : (([[2,3,5,5,5,5],[2,4,4,5,5,5],[2,4,5,5,5,5],[2,4,5,5,5,7],[2,5,5,5,5,5],[2,5,5,5,5,6],[2,5,5,5,5,7],[2,5,5,5,7,7],[3,4,5,5,5,5],[3,5,5,5,5,5],[3,5,5,5,5,7],[4,4,4,5,5,5],[4,4,5,5,5,5],[4,4,5,5,5,7],[4,5,5,5,5,5],[4,5,5,5,5,6],[4,5,5,5,5,7],[4,5,5,5,7,7],[5,5,5,5,5,5],[5,5,5,5,5,6],[5,5,5,5,5,7],[5,5,5,5,6,7],[5,5,5,5,7,7],[5,5,5,7,7,7]] : List (List ThreeBoundQ2.Kind)).all (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree))=true := by
    exact ThreeBoundRecordLookup.all_cons_of _ _ _ (BS2_b3ba934b_RI_Batch_cc30a0ee5240.2.2.2.2.2.2.2.1) (ThreeBoundRecordLookup.all_cons_of _ _ _ (BS2_b3ba934b_RI_Batch_0997866a336d.1) (ThreeBoundRecordLookup.all_cons_of _ _ _ (BS2_b3ba934b_RI_Batch_0997866a336d.2.1) (ThreeBoundRecordLookup.all_cons_of _ _ _ (BS2_b3ba934b_RI_Batch_0997866a336d.2.2.1) (ri_inline_checked_length6_coverage_tail013))))
  have ri_inline_checked_length6_coverage_tail005 : (([[2,2,2,5,5,5],[2,2,4,5,5,5],[2,2,5,5,5,5],[2,2,5,5,5,7],[2,3,5,5,5,5],[2,4,4,5,5,5],[2,4,5,5,5,5],[2,4,5,5,5,7],[2,5,5,5,5,5],[2,5,5,5,5,6],[2,5,5,5,5,7],[2,5,5,5,7,7],[3,4,5,5,5,5],[3,5,5,5,5,5],[3,5,5,5,5,7],[4,4,4,5,5,5],[4,4,5,5,5,5],[4,4,5,5,5,7],[4,5,5,5,5,5],[4,5,5,5,5,6],[4,5,5,5,5,7],[4,5,5,5,7,7],[5,5,5,5,5,5],[5,5,5,5,5,6],[5,5,5,5,5,7],[5,5,5,5,6,7],[5,5,5,5,7,7],[5,5,5,7,7,7]] : List (List ThreeBoundQ2.Kind)).all (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree))=true := by
    exact ThreeBoundRecordLookup.all_cons_of _ _ _ (BS2_b3ba934b_RI_Batch_cc30a0ee5240.2.2.2.1) (ThreeBoundRecordLookup.all_cons_of _ _ _ (BS2_b3ba934b_RI_Batch_cc30a0ee5240.2.2.2.2.1) (ThreeBoundRecordLookup.all_cons_of _ _ _ (BS2_b3ba934b_RI_Batch_cc30a0ee5240.2.2.2.2.2.1) (ThreeBoundRecordLookup.all_cons_of _ _ _ (BS2_b3ba934b_RI_Batch_cc30a0ee5240.2.2.2.2.2.2.1) (ri_inline_checked_length6_coverage_tail009))))
  have ri_inline_checked_length6_coverage_tail001 : (([[1,2,5,5,5,5],[1,4,5,5,5,5],[1,5,5,5,5,5],[1,5,5,5,5,7],[2,2,2,5,5,5],[2,2,4,5,5,5],[2,2,5,5,5,5],[2,2,5,5,5,7],[2,3,5,5,5,5],[2,4,4,5,5,5],[2,4,5,5,5,5],[2,4,5,5,5,7],[2,5,5,5,5,5],[2,5,5,5,5,6],[2,5,5,5,5,7],[2,5,5,5,7,7],[3,4,5,5,5,5],[3,5,5,5,5,5],[3,5,5,5,5,7],[4,4,4,5,5,5],[4,4,5,5,5,5],[4,4,5,5,5,7],[4,5,5,5,5,5],[4,5,5,5,5,6],[4,5,5,5,5,7],[4,5,5,5,7,7],[5,5,5,5,5,5],[5,5,5,5,5,6],[5,5,5,5,5,7],[5,5,5,5,6,7],[5,5,5,5,7,7],[5,5,5,7,7,7]] : List (List ThreeBoundQ2.Kind)).all (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree))=true := by
    exact ThreeBoundRecordLookup.all_cons_of _ _ _ (BS2_b3ba934b_RI_Batch_83689d4e5d10.2.2.2.2.2.2.2.1) (ThreeBoundRecordLookup.all_cons_of _ _ _ (BS2_b3ba934b_RI_Batch_cc30a0ee5240.1) (ThreeBoundRecordLookup.all_cons_of _ _ _ (BS2_b3ba934b_RI_Batch_cc30a0ee5240.2.1) (ThreeBoundRecordLookup.all_cons_of _ _ _ (BS2_b3ba934b_RI_Batch_cc30a0ee5240.2.2.1) (ri_inline_checked_length6_coverage_tail005))))
  have ri_inline_checked_length6_coverage_tail000 : (([[0,5,5,5,5,5],[1,2,5,5,5,5],[1,4,5,5,5,5],[1,5,5,5,5,5],[1,5,5,5,5,7],[2,2,2,5,5,5],[2,2,4,5,5,5],[2,2,5,5,5,5],[2,2,5,5,5,7],[2,3,5,5,5,5],[2,4,4,5,5,5],[2,4,5,5,5,5],[2,4,5,5,5,7],[2,5,5,5,5,5],[2,5,5,5,5,6],[2,5,5,5,5,7],[2,5,5,5,7,7],[3,4,5,5,5,5],[3,5,5,5,5,5],[3,5,5,5,5,7],[4,4,4,5,5,5],[4,4,5,5,5,5],[4,4,5,5,5,7],[4,5,5,5,5,5],[4,5,5,5,5,6],[4,5,5,5,5,7],[4,5,5,5,7,7],[5,5,5,5,5,5],[5,5,5,5,5,6],[5,5,5,5,5,7],[5,5,5,5,6,7],[5,5,5,5,7,7],[5,5,5,7,7,7]] : List (List ThreeBoundQ2.Kind)).all (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree))=true := by
    exact ThreeBoundRecordLookup.all_cons_of _ _ _ (BS2_b3ba934b_RI_Batch_618c58463e44.2.2.2.2.1) (ri_inline_checked_length6_coverage_tail001)
  apply ThreeBoundRecordLookup.checkLength_of_active
  rw [(BS2_b3ba934b_RI_Batch_8b120256d811.1)]
  exact ri_inline_checked_length6_coverage_tail000
