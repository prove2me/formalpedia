-- Prove2me | solution 2 for DetDLP.d4_partial_unroll_rank_enumerator_v2
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-25T07:59:29.511798+00:00
-- url     : https://prove2.me/submissions/678069b4-b6b5-46f9-903b-0da8c242ee59

import Definitions.Def_DetDLP_D4Plan
import Definitions.Def_DetDLP_D4SoloPlanDefs
import Theorems.Thm_DetDLP_d4_balanced_node_rank_machine
import Theorems.Thm_DetDLP_d4_active_node_preconditions
import Theorems.Thm_DetDLP_d4_unroll_tree_bit_budget
import Theorems.Thm_DetDLP_d4_unroll_guard_and_residual_bounds
import Theorems.Thm_DetDLP_d4_core_cut_poly_and_spec
import Theorems.Thm_DetDLP_m14_sync
import Theorems.Thm_DetDLP_m14_base_fuel
import Theorems.Thm_DetDLP_m14_plan_obligations
import Theorems.Thm_DetDLP_m14_bounds
import Theorems.Thm_DetDLP_m14_sources
import Theorems.Thm_DetDLP_m14_enum

set_option autoImplicit false
set_option maxHeartbeats 600000

open DetDLP DetDLP.D4Plan DetDLP.D4GuardTree
open DetDLP.D4SoloNode DetDLP.D4SoloRoot DetDLP.D4SoloStep DetDLP.D4SoloTree
open DetDLP.D4SoloForest DetDLP.D4SoloPlanDefs
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation

theorem solution (one : AppendixD4.OneStep) (C c : ℕ) (hC : 0 < C) (hc : 0 < c) (E : PrimitiveMachine) (o : Fin E.tapeCount) :
    ∃ (A : PrimitiveMachine) (oa : Fin A.tapeCount) (K L₀ : ℕ) (P : (x : Input C c) → L₀ ≤ Nat.clog 2 x.S → entry x E o → Plan x),
      (∀ x hl he, ∀ i < (P x hl he).f.natDegree, (P x hl he).f.coeff i = 0 ∨ (P x hl he).f.coeff i = 1) ∧
      (∀ x hl he, Enumerates A oa K (P x hl he)) ∧
      (AppendixD4.Closed → ∃ (B : PrimitiveMachine) (ob : Fin B.tapeCount) (k : ℕ), ∀ x hl he, Sources B ob k (P x hl he)) := by
  obtain ⟨M_node, E_pkt, o_node, o_pkt, K_loc, H_loc, c_loc, hLocal⟩ :=
    DetDLP.d4_balanced_node_rank_machine one
  obtain ⟨A_enum, oa_enum, K_enum, hEnum⟩ :=
    DetDLP.m14_enum hC hc M_node E_pkt o_node o_pkt K_loc H_loc c_loc
  obtain ⟨L_src, hSources⟩ :=
    DetDLP.m14_sources hC hc E o M_node E_pkt o_node o_pkt K_loc H_loc c_loc
  choose B_src ob_src k_src hSrc using hSources
  obtain ⟨_, _, hRootPins, hHitDeg, _, hPlan⟩ := DetDLP.m14_plan_obligations
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hRootPorts, _, hUnrollPorts⟩ :=
    DetDLP.m14_bounds

  let L_act := (DetDLP.d4_active_node_preconditions C hC).choose
  let L_bud := (DetDLP.d4_unroll_tree_bit_budget C (8 * K_loc) hC).choose
  let L_grd := (DetDLP.d4_unroll_guard_and_residual_bounds C hC).choose
  let L₀ := max (max L_bud L_grd) (max (max 6 L_act) (max (C + 6) L_src))

  let build (x : Input C c) (hl : L₀ ≤ Nat.clog 2 x.S) :
      {p : Plan x // (∀ i < p.f.natDegree, p.f.coeff i = 0 ∨ p.f.coeff i = 1) ∧
        Enumerates A_enum oa_enum K_enum p ∧
        ∀ hClosed : AppendixD4.Closed, entry x E o →
          Sources (B_src hClosed) (ob_src hClosed) (k_src hClosed) p} := by
    obtain ⟨hbg, has⟩ := max_le_iff.mp hl
    obtain ⟨hbud, hgrd⟩ := max_le_iff.mp hbg
    obtain ⟨hact6, hsrc⟩ := max_le_iff.mp has
    obtain ⟨h6, hact⟩ := max_le_iff.mp hact6
    have hlevel : 1 ≤ D3Stopped.level x.S := le_trans (by decide : 1 ≤ 6) h6
    let f := soloPoly x.S
    obtain ⟨hf, hdeg_f, hRing⟩ := DetDLP.m14_base_fuel.1 hlevel
    have hpos : 0 < (soloPoly x.S).natDegree := by
      rw [hdeg_f]
      exact Nat.mul_pos (by decide) hlevel

    let D := Nat.clog 32 (4 * x.m)
    let guard := totalGuard x.S D
    let budget := D4UnrollBudget.budget x.S D (8 * K_loc)
    let pkt := pktOKOf E_pkt o_pkt K_loc x f hf
    let root := rootSoloNode x f pkt
    have hdepth : root.d + D = D := by rw [show root.d = 0 from rootSoloNode_d x f pkt, Nat.zero_add]
    have hactive := (DetDLP.d4_active_node_preconditions C hC).choose_spec x
    let rootUnroll := buildSoloUnroll x hf hRing hdeg_f M_node E_pkt o_node o_pkt K_loc H_loc c_loc
      hLocal L_act hactive hact D root hdepth
    let todo : List (WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc) :=
      [⟨D, root, rootUnroll⟩]
    let certTree := unrollCertFuel x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc
      guard (64 ^ D) todo [] 1 0
    have hslots : remSlots todo ≤ 64 ^ D := slots_bound_64 D
    have hvalid : treeAll SoloLeafData.Valid certTree := by
      refine (DetDLP.m14_sync x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc).2.1
        (64 ^ D) todo [] 1 0 hslots ?_ ?_ ?_ (List.Perm.of_eq (hRootPins x f pkt))
      · simpa only [Nat.zero_add, totalGuard] using Nat.mul_le_mul_left (localAllowance x.S D) hslots
      · simp [todo, remLeaves, D]
      · simp

    have hbLen : (D4CoreCut.boundaryEdges x.G x.spec.lookupVerts).length = 4 * x.m * x.k :=
      (DetDLP.d4_core_cut_poly_and_spec.2 x).2.2.2.2.1
    have hdeg_all := hHitDeg (PktOK := pkt) x hbLen
    let br := mkPlanBranchAux x hf E_pkt o_pkt K_loc guard budget certTree hvalid hbLen hdeg_all
    obtain ⟨hverts, hdegree, hcorrect⟩ :=
      hPlan hC x hlevel hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc
        hbud hgrd rootUnroll hvalid hbLen hdeg_all hpos
    let p := mkSoloPlanFromBr x f hf hdeg_f hpos guard budget br hverts hdegree hcorrect
    refine ⟨p, ?_, ?_, ?_⟩
    · intro i _hi
      exact DetDLP.m14_base_fuel.2.1 x.S i
    · have hports := hUnrollPorts x hf hRing hdeg_f M_node E_pkt o_node o_pkt K_loc H_loc c_loc
        hLocal L_act hactive hact D root hdepth (hRootPorts x f pkt)
      exact hEnum x hlevel hbud hgrd hf hdeg_f hpos rootUnroll hports hvalid hbLen hdeg_all
        hverts hdegree hcorrect
    · intro hClosed he
      exact hSrc hClosed x hlevel hbud hgrd hact6 hsrc he hf hdeg_f hpos rootUnroll hvalid
        hbLen hdeg_all hverts hdegree hcorrect

  let P : (x : Input C c) → L₀ ≤ Nat.clog 2 x.S → entry x E o → Plan x :=
    fun x hl _he => (build x hl).1
  refine ⟨A_enum, oa_enum, K_enum, L₀, P, ?_, ?_, ?_⟩
  · exact fun x hl _he => (build x hl).2.1
  · exact fun x hl _he => (build x hl).2.2.1
  · intro hClosed
    exact ⟨B_src hClosed, ob_src hClosed, k_src hClosed, fun x hl he => (build x hl).2.2.2 hClosed he⟩
