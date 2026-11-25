-- Prove2me | solution 1 for DetDLP.m14_enum
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-25T07:46:39.760407+00:00
-- url     : https://prove2.me/submissions/303339a2-fc53-49ac-9e76-603eaaea5d0b

import Definitions.Def_DetDLP_D4SoloPlanDefs
import Theorems.Thm_DetDLP_d4_unroll_tree_bit_budget
import Theorems.Thm_DetDLP_d4_unroll_guard_and_residual_bounds
import Theorems.Thm_DetDLP_d4_padded_tree_rank_walker_v2_machine
import Theorems.Thm_DetDLP_m14_sync
import Theorems.Thm_DetDLP_m14_base_fuel
import Theorems.Thm_DetDLP_m14_bounds
import Theorems.Thm_DetDLP_m14_enum_wire
import Theorems.Thm_DetDLP_m14_enum_bounds

set_option autoImplicit false
set_option maxHeartbeats 1200000

open Groundwork Polynomial Finset DetDLP DetDLP.AppendixD4 DetDLP.ResidualScalarOracle
open DetDLP.D4Plan DetDLP.D4StoppedNode DetDLP.D4RankWalker DetDLP.D4GuardTree
open DetDLP.D4SoloRaw DetDLP.D4SoloNode DetDLP.D4SoloRoot DetDLP.D4SoloStep
open DetDLP.D4SoloStepEq DetDLP.D4SoloTree DetDLP.D4SoloForest DetDLP.D4SoloPlanDefs
open DetDLP_W1_Queries OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

namespace DetDLP.M14EnumInternal

private theorem polyBound_nonneg (K n : ℕ) : 0 ≤ polyBound K n := by
  unfold polyBound; positivity

private theorem polyBound_const_mul_succ (c K n : ℕ) :
    (c : ℝ) * (polyBound K n + 1) ≤ polyBound (c * (K + 1)) n := by
  by_cases hc0 : c = 0
  · subst hc0; simp [polyBound]
  · unfold polyBound
    have h1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ (K + 1) := one_le_pow₀ (by exact_mod_cast Nat.succ_pos n)
    have h2 : ((n : ℝ) + 1) ^ K ≤ ((n : ℝ) + 1) ^ (K + 1) :=
      pow_le_pow_right₀ (by exact_mod_cast Nat.succ_pos n) (Nat.le_succ K)
    have hK_step : (K : ℝ) * ((n : ℝ) + 1) ^ K + 1 ≤ ((K + 1 : ℕ) : ℝ) * ((n : ℝ) + 1) ^ (K + 1) := by
      push_cast; nlinarith only [h1, h2, Nat.cast_nonneg (α := ℝ) K]
    have h3 : (c : ℝ) * ((K : ℝ) * ((n : ℝ) + 1) ^ K + 1) ≤
        ((c * (K + 1) : ℕ) : ℝ) * ((n : ℝ) + 1) ^ (K + 1) := by
      have hm := mul_le_mul_of_nonneg_left hK_step (Nat.cast_nonneg c)
      push_cast at hm ⊢
      linarith [hm]
    exact h3.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by exact_mod_cast Nat.succ_pos n) (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hc0)))
      (by positivity))

private theorem two_mul_polyBound_le (K n : ℕ) :
    2 * polyBound K n ≤ polyBound (2 * K) n := by
  unfold polyBound
  push_cast
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by exact_mod_cast Nat.succ_pos n) (by omega))
      (Nat.cast_nonneg K))
    (by norm_num)

end DetDLP.M14EnumInternal

-- Keep the target's names for hypotheses used only in the proof.
open DetDLP.M14EnumInternal in
set_option linter.unusedVariables false in
theorem solution :
    ∀ {C c : ℕ} (hC : 0 < C) (hc : 0 < c)
        (M_node E_pkt : PrimitiveMachine) (o_node : Fin M_node.tapeCount) (o_pkt : Fin E_pkt.tapeCount)
        (K_loc H_loc c_loc : ℕ),
    ∃ (A_enum : PrimitiveMachine) (oa_enum : Fin A_enum.tapeCount) (K_enum : ℕ),
      ∀ (x : Input C c) (hL_level : 1 ≤ D3Stopped.level x.S)
          (hL_bud : (DetDLP.d4_unroll_tree_bit_budget C (8 * K_loc) hC).choose ≤ D3Stopped.level x.S)
        (hL_grd : (DetDLP.d4_unroll_guard_and_residual_bounds C hC).choose ≤ D3Stopped.level x.S)
          (hf : (soloPoly x.S).Monic)
        (hdeg_f : (soloPoly x.S).natDegree = 4 * Nat.clog 2 x.S)
        (hpos : 0 < (soloPoly x.S).natDegree),
      let f := soloPoly x.S
      let D := Nat.clog 32 (4 * x.m)
      let guard := totalGuard x.S D
      let B_bud := D4UnrollBudget.budget x.S D (8 * K_loc)
      let rootNode := rootSoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)
      ∀ (rootUnroll : SoloUnroll x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc D rootNode),
      SoloUnrollAllPortsBounded D rootNode rootUnroll →
      let certTree := unrollCertFuel x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc guard (64 ^ D)
        [⟨D, rootNode, rootUnroll⟩] [] 1 0
      ∀ (hvalid : treeAll SoloLeafData.Valid certTree)
          (hbLen : (D4CoreCut.boundaryEdges x.G x.spec.lookupVerts).length = 4 * x.m * x.k)
          (hdeg_all : ∀ (doneNodes : List (SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)))
            (hperm : List.Perm (pinFirsts doneNodes) (List.finRange (4 * x.m * x.k))),
            HitDegProp x hbLen doneNodes hperm),
      let br := mkPlanBranchAux x hf E_pkt o_pkt K_loc guard B_bud certTree hvalid hbLen hdeg_all
      ∀ (hverts : ∀ u : Fin (2 ^ B_bud),
            (D4CoreCut.reattach x.G x.spec.lookupVerts (br u).n (br u).leafFn).nV ≤
              4 * x.m + 64 ^ Nat.clog 32 (4 * x.m))
          (hdegree : ∀ u : Fin (2 ^ B_bud),
            (D4CoreCut.reattach x.G x.spec.lookupVerts (br u).n (br u).leafFn).maxDeg * x.m ≤
              1217 * (C + 1) ^ 3 * x.b)
          (hcorrect :
            answer x = encodeNatListBin (List.ofFn fun j : Fin x.l =>
              word f x.l (guard + x.p) hf
                (∑ u : Fin (2 ^ B_bud), (br u).wVal *
                  BTNContract (D4CoreCut.reattach x.G x.spec.lookupVerts (br u).n (br u).leafFn)
                    (planVOfBr x f guard B_bud br u))
                j ⟨0, hpos⟩ / 2 ^ guard)),
      let P := mkSoloPlanFromBr x f hf hdeg_f hpos guard B_bud br hverts hdegree hcorrect
      Enumerates A_enum oa_enum K_enum P := by
  intro C c hC hc M_node E_pkt o_node o_pkt K_loc H_loc c_loc
  obtain ⟨poly_spec, _, _, _, _, clog2_le_self, pow2_clog2_le, pow64_clog32_le, _⟩ :=
    DetDLP.m14_base_fuel
  obtain ⟨countWord_len_le_succ, countWord_len_of_le_pow, _, pack_len_le, graph_encode_len_le, _,
    polyBound_eq_natCast, _, input_params_le, input_len_le_poly, _, unrollCertFuel_done_depth_le,
    _, _, rootSoloNode_portsBounded, soloNode_table_and_work_len, _⟩ := DetDLP.m14_bounds
  obtain ⟨soloOneCall, _, _, preWalkGen_eq_startV2, postWalk_spec⟩ := DetDLP.m14_enum_wire
  obtain ⟨polyBound_mono_K, _, polyBound_const_le, polyBound_add_le, polyBound_mul_le,
    polyBound_comp_le, unrollCertFuel_done_portsBounded, callsV2_workItems_bounded,
    width_le_level_solo, active_nBranches_le_pow2, residue_len_X2, contextV2_len_X2,
    active_req_and_step_len_X2, phaseStateV2_len_X2, branch_and_digit_len_X3⟩ :=
    DetDLP.m14_enum_bounds
  obtain ⟨W_mach, o_walk, K_walk, hWalk⟩ := (DetDLP.d4_padded_tree_rank_walker_v2_machine M_node o_node).2
  let A_fl := A_fuel C K_loc
  let K_mode := 8 * K_loc
  let preFn := preWalkGen D4CoreCut.cutCoreRaw A_fl K_mode
  let postFn := postWalkGen D4CoreCut.reattachRaw A_fl K_mode
  obtain ⟨A_enum, oa_enum, K_one, _, hOneCall⟩ :=
    soloOneCall W_mach o_walk preFn postFn
      (preWalkGen_poly DetDLP.d4_core_cut_poly_and_spec.1 A_fl K_mode)
      (postWalkGen_poly DetDLP.d4_reattach_poly_and_spec.1 A_fl K_mode)
  obtain ⟨K_bud, hKbud_def⟩ : ∃ K, K = (DetDLP.d4_unroll_tree_bit_budget C (8 * K_loc) hC).choose_spec.choose := ⟨_, rfl⟩
  obtain ⟨K_grd, hKgrd_def⟩ : ∃ K, K = (DetDLP.d4_unroll_guard_and_residual_bounds C hC).choose_spec.choose := ⟨_, rfl⟩
  obtain ⟨K_in, _, hIn_len⟩ := input_len_le_poly (C := C) hc
  obtain ⟨K_wi, _, hNode_len⟩ := soloNode_table_and_work_len (C := C) (c := c) K_loc
  -- Opaque polynomial degree & coefficient constants
  obtain ⟨E_base, hEb_def⟩ : ∃ E, E = max (K_in + 4) (max (K_grd + 4) (max (K_wi + 4) (2 * c + 8))) := ⟨_, rfl⟩
  obtain ⟨C_big, hCbig_def⟩ : ∃ M, M = (C + 2) * (K_loc + 2) * (K_grd + 2) * (K_wi + 2) * (K_in + 2) := ⟨_, rfl⟩
  obtain ⟨K_word, hKw_def⟩ : ∃ K, K = 2199023255552 * C_big + 3 * E_base + 8 := ⟨_, rfl⟩
  obtain ⟨K_bnd, hKbnd_def⟩ : ∃ K, K = compExp H_loc K_word + compExp K_loc K_word + c_loc + 4 := ⟨_, rfl⟩
  obtain ⟨K_len, hKlen_def⟩ : ∃ K, K = 32 * K_word + 16 * K_bnd + 8192 := ⟨_, rfl⟩
  obtain ⟨K_W, hKW_def⟩ : ∃ K, K = compExp K_walk K_len * (K_bnd + 1) + compExp K_walk K_len + (K_walk + 1) * (K_bnd + 1) + 4 := ⟨_, rfl⟩
  obtain ⟨K_A, hKA_def⟩ : ∃ K, K = 2 * (compExp K_one K_len + K_one * (2 * K_W + 1)) + 4 := ⟨_, rfl⟩
  obtain ⟨K_enum, hKenum_def⟩ : ∃ K, K = max 1 (max K_A (max K_bud (max K_grd K_len))) := ⟨_, rfl⟩
  -- Pure ℕ inequalities between constants
  have hEb_ge8 : 8 ≤ E_base := by rw [hEb_def]; omega
  have hEb_Kin : K_in ≤ E_base := by rw [hEb_def]; omega
  have hEb_Kgrd : K_grd ≤ E_base := by rw [hEb_def]; omega
  have hEb_Kwi : K_wi ≤ E_base := by rw [hEb_def]; omega
  have hEb_2c4 : 2 * c + 4 ≤ E_base := by rw [hEb_def]; omega
  have hCbig_ge1 : 1 ≤ C_big := by
    rw [hCbig_def]
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _))
      (Nat.succ_pos _)) (Nat.succ_pos _)) (Nat.succ_pos _)
  have hC_Cbig : C + 2 ≤ C_big := by
    rw [hCbig_def]
    exact (((Nat.le_mul_of_pos_right _ (Nat.succ_pos _)).trans
      (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))).trans
      (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))).trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
  have hKL_Cbig : K_loc + 2 ≤ C_big := by
    rw [hCbig_def]
    exact (((Nat.le_mul_of_pos_left _ (Nat.succ_pos _)).trans
      (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))).trans
      (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))).trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
  have hKG_Cbig : K_grd + 2 ≤ C_big := by
    rw [hCbig_def]
    exact ((Nat.le_mul_of_pos_left _ (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _))).trans
      (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))).trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
  have hKW_Cbig : K_wi + 2 ≤ C_big := by
    rw [hCbig_def]
    exact (Nat.le_mul_of_pos_left _ (Nat.mul_pos (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _))
      (Nat.succ_pos _))).trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
  have hKI_Cbig : K_in + 2 ≤ C_big := by
    rw [hCbig_def]
    exact Nat.le_mul_of_pos_left _ (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _))
      (Nat.succ_pos _)) (Nat.succ_pos _))
  have hCG_Cbig : (C + 2) * (K_grd + 2) ≤ C_big := by
    rw [hCbig_def]
    calc (C + 2) * (K_grd + 2)
        ≤ ((C + 2) * (K_loc + 2)) * (K_grd + 2) :=
          Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
      _ ≤ ((C + 2) * (K_loc + 2) * (K_grd + 2) * (K_wi + 2)) * (K_in + 2) :=
          (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)).trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
  have hCL_Cbig : (C + 2) * (K_loc + 2) ≤ C_big := by
    rw [hCbig_def]
    exact ((Nat.le_mul_of_pos_right _ (Nat.succ_pos _)).trans
      (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))).trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
  have hLG_Cbig : (K_loc + 2) * (K_grd + 2) ≤ C_big := by
    rw [hCbig_def]
    calc (K_loc + 2) * (K_grd + 2)
        ≤ ((C + 2) * (K_loc + 2)) * (K_grd + 2) :=
          Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
      _ ≤ ((C + 2) * (K_loc + 2) * (K_grd + 2) * (K_wi + 2)) * (K_in + 2) :=
          (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)).trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
  have hKw_coef : 2199023255552 * C_big ≤ K_word := by
    rw [hKw_def]; exact (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
  have hKw_exp : 3 * E_base ≤ K_word := by
    rw [hKw_def]; exact (Nat.le_add_left _ _).trans (Nat.le_add_right _ _)
  have hKbnd_1 : compExp H_loc K_word + compExp K_loc K_word + c_loc ≤ K_bnd := by
    rw [hKbnd_def]; exact Nat.le_add_right _ _
  have hKlen_sum : 16 * K_word + 8 * K_bnd + 4120 ≤ K_len := by rw [hKlen_def]; omega
  have hKlen_exp_w : K_word ≤ K_len := by rw [hKlen_def]; omega
  have hKlen_exp_b : K_bnd ≤ K_len := by rw [hKlen_def]; omega
  have hKlen_ge2 : 2 ≤ K_len := by rw [hKlen_def]; omega
  have hKW_tm : compExp K_walk K_len * (K_bnd + 1) + compExp K_walk K_len + (K_bnd + 1) ≤ K_W := by
    rw [hKW_def]
    have h1 : 1 * (K_bnd + 1) ≤ (K_walk + 1) * (K_bnd + 1) := Nat.mul_le_mul_right _ (Nat.succ_pos _)
    rw [one_mul] at h1
    exact (Nat.add_le_add_left h1 _).trans (Nat.le_add_right _ _)
  have hKW_sp : compExp K_walk K_len + K_walk * (K_bnd + 1) ≤ K_W := by
    rw [hKW_def]
    have h1 : K_walk * (K_bnd + 1) ≤ (K_walk + 1) * (K_bnd + 1) := Nat.mul_le_mul_right _ (Nat.le_succ _)
    exact (Nat.add_le_add (Nat.le_add_left _ _) h1).trans (Nat.le_add_right _ _)
  have hKA_tm : 2 * (compExp K_one K_len + K_one * (2 * K_W + 1)) ≤ K_A := by
    rw [hKA_def]; exact Nat.le_add_right _ _
  have hKA_sp : compExp K_one K_len + K_one * (K_W + 1) ≤ K_A := by
    rw [hKA_def]
    have h1 : K_one * (K_W + 1) ≤ K_one * (2 * K_W + 1) := Nat.mul_le_mul_left _ (by omega)
    exact (Nat.add_le_add_left h1 _).trans ((Nat.le_mul_of_pos_left _ (by decide : 0 < 2)).trans (Nat.le_add_right _ _))
  have hKA_enum : K_A ≤ K_enum := by rw [hKenum_def]; exact (le_max_left _ _).trans (le_max_right _ _)
  have hKbud_enum : K_bud ≤ K_enum := by
    rw [hKenum_def]; exact ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hKgrd_enum : K_grd ≤ K_enum := by
    rw [hKenum_def]
    exact (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hKlen_enum : K_len ≤ K_enum := by
    rw [hKenum_def]
    exact (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)
  clear hEb_def hCbig_def hKw_def hKbnd_def hKlen_def hKW_def hKA_def hKenum_def
  refine ⟨A_enum, oa_enum, K_enum, ?_⟩
  intro x hL_level hL_bud hL_grd hf hdeg_f hpos f D guard B_bud rootNode rootUnroll hRoot_pb
    certTree hvalid hbLen hdeg_all br hverts hdegree hcorrect P
  let N := D4Plan.size x
  let N₁ := N + 1
  obtain ⟨hmk, _, _, _, _, hl_x, hp_x, hS_sz, hdesc_sz⟩ := input_params_le x
  have hS_pos : 1 ≤ x.S := x.hp.trans x.pS
  have hN1_ge2 : 2 ≤ N₁ := Nat.succ_le_succ (hS_pos.trans hS_sz)
  have hN1_pos : 1 ≤ N₁ := by omega
  have hRing : RingOK f := (poly_spec hL_level).2.2
  let qPrec := guard + x.p
  let ctx := contextV2 x.S x.m x.p guard x.l (polynomialBits f)
  let PktOK := pktOKOf E_pkt o_pkt K_loc x f hf
  let F := soloStepFn M_node o_node ctx
  have hbud_spec := (DetDLP.d4_unroll_tree_bit_budget C (8 * K_loc) hC).choose_spec.choose_spec x hL_bud
  have hgrd_spec := (DetDLP.d4_unroll_guard_and_residual_bounds C hC).choose_spec.choose_spec x hL_grd
  rw [← hKbud_def] at hbud_spec
  rw [← hKgrd_def] at hgrd_spec
  clear hKbud_def hKgrd_def
  obtain ⟨X, hX_def⟩ : ∃ M, M = N₁ ^ E_base := ⟨_, rfl⟩
  have hX1 : 1 ≤ X := hX_def ▸ Nat.one_le_pow _ _ hN1_pos
  have hN1_pow_le_X : ∀ e ≤ E_base, N₁ ^ e ≤ X := fun e he => hX_def ▸ Nat.pow_le_pow_right hN1_pos he
  have hN1_X : N₁ ≤ X := (pow_one N₁).symm.le.trans (hN1_pow_le_X 1 (by omega))
  have hN2_X : N₁ ^ 2 ≤ X := hN1_pow_le_X 2 (by omega)
  have hN3_X : N₁ ^ 3 ≤ X := hN1_pow_le_X 3 (by omega)
  have hN6_X : N₁ ^ 6 ≤ X := hN1_pow_le_X 6 (by omega)
  have hX_X2 : X ≤ X ^ 2 := by nlinarith only [hX1]
  have hX2_X3 : X ^ 2 ≤ X ^ 3 := by
    calc X ^ 2 = X ^ 2 * 1 := (mul_one _).symm
      _ ≤ X ^ 2 * X := Nat.mul_le_mul_left _ hX1
      _ = X ^ 3 := (pow_succ X 2).symm
  have hX_X3 : X ≤ X ^ 3 := hX_X2.trans hX2_X3
  have hWord_master : ∀ m : ℕ, m ≤ 2199023255552 * C_big * X ^ 3 → m ≤ K_word * N₁ ^ K_word := by
    intro m hm
    have hX3 : X ^ 3 = N₁ ^ (3 * E_base) := by rw [hX_def, ← pow_mul, mul_comm]
    calc m ≤ 2199023255552 * C_big * N₁ ^ (3 * E_base) := by rw [← hX3]; exact hm
      _ ≤ K_word * N₁ ^ K_word := Nat.mul_le_mul hKw_coef (Nat.pow_le_pow_right hN1_pos hKw_exp)
  clear hX_def
  -- Basic parameter bounds
  have hxS_N1 : x.S ≤ N₁ := hS_sz.trans (Nat.le_succ N)
  have hdesc_N1 : x.desc.length ≤ N₁ := hdesc_sz.trans (Nat.le_succ N)
  have hp_N1 : x.p ≤ N₁ := hp_x.trans hxS_N1
  have hl_N1 : x.l ≤ 2 * C * N₁ := hl_x.trans (Nat.mul_le_mul_left _ hxS_N1)
  have hmk_N1 : 4 * x.m * x.k ≤ 2 * N₁ := hmk.trans (Nat.mul_le_mul_left 2 hxS_N1)
  have h4m_N1 : 4 * x.m ≤ 2 * N₁ :=
    (Nat.le_mul_of_pos_right _ x.hk).trans hmk_N1
  have hlev_N1 : D3Stopped.level x.S ≤ N₁ := (clog2_le_self x.S).trans hxS_N1
  have hdeg_f_N1 : f.natDegree ≤ 4 * N₁ := hdeg_f.le.trans (Nat.mul_le_mul_left 4 hlev_N1)
  have hpf_N1 : (polynomialBits f).length ≤ 4 * N₁ := by
    unfold polynomialBits; simp only [List.length_ofFn]; exact hdeg_f_N1
  have hD_N1 : D ≤ 8 * N₁ := by
    have hcl : D ≤ Nat.clog 2 (4 * x.m) := by dsimp [D]; rw [Nat.clog_pow_left 2 5 (4 * x.m)]; omega
    exact (hcl.trans (clog2_le_self _)).trans (by omega)
  have h64D_N2 : 64 ^ D ≤ 4096 * N₁ ^ 2 := by
    have h1 := pow64_clog32_le (n := 4 * x.m) (by have := x.hm; omega)
    refine h1.trans ?_
    calc (32 * (4 * x.m)) ^ 2 ≤ (32 * (2 * N₁)) ^ 2 := Nat.pow_le_pow_left (Nat.mul_le_mul_left 32 h4m_N1) 2
      _ = 4096 * N₁ ^ 2 := by ring
  have h64D_X : 64 ^ D ≤ 4096 * X := h64D_N2.trans (Nat.mul_le_mul_left 4096 hN2_X)
  have h2sh_N1 : ∀ d, 2 ^ D3Stopped.shift x.S d ≤ 2 * N₁ := fun d =>
    ((Nat.pow_le_pow_right (by decide) (shift_le_level_solo x.S d)).trans (pow2_clog2_le hS_pos)).trans
      (Nat.mul_le_mul_left 2 hxS_N1)
  have h64sh_X : ∀ d, 64 ^ D3Stopped.shift x.S d ≤ 64 * X := by
    intro d
    have h64_eq : 64 ^ D3Stopped.shift x.S d = (2 ^ D3Stopped.shift x.S d) ^ 6 := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [h64_eq]
    calc (2 ^ D3Stopped.shift x.S d) ^ 6 ≤ (2 * N₁) ^ 6 := Nat.pow_le_pow_left (h2sh_N1 d) 6
      _ = 64 * N₁ ^ 6 := by ring
      _ ≤ 64 * X := Nat.mul_le_mul_left 64 hN6_X
  have hBbud_X : B_bud ≤ 131072 * (K_loc + 1) * X := by
    dsimp [B_bud]; unfold D4UnrollBudget.budget
    have h2D : 2 ^ D - 1 ≤ 64 ^ D := (Nat.sub_le _ _).trans (Nat.pow_le_pow_left (by decide) D)
    have hdiv : (2 * (8 * K_loc) * (2 ^ D - 1) * x.S) / max 1 (D3Stopped.width x.S D).sqrt ≤
        16 * K_loc * (4096 * N₁ ^ 2) * N₁ := by
      refine (Nat.div_le_self _ _).trans ?_
      calc 2 * (8 * K_loc) * (2 ^ D - 1) * x.S
          = 16 * K_loc * (2 ^ D - 1) * x.S := by ring
        _ ≤ 16 * K_loc * (4096 * N₁ ^ 2) * N₁ :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (h2D.trans h64D_N2)) hxS_N1
    have ht1 : 8 * (D3Stopped.level x.S + 1) * 64 ^ D ≤ 16 * N₁ * (4096 * N₁ ^ 2) :=
      Nat.mul_le_mul (by omega) h64D_N2
    have hsum : 16 * N₁ * (4096 * N₁ ^ 2) + 16 * K_loc * (4096 * N₁ ^ 2) * N₁ ≤
        131072 * (K_loc + 1) * N₁ ^ 3 := by
      have : 65536 * (K_loc + 1) * N₁ ^ 3 ≤ 131072 * (K_loc + 1) * N₁ ^ 3 :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num))
      calc 16 * N₁ * (4096 * N₁ ^ 2) + 16 * K_loc * (4096 * N₁ ^ 2) * N₁
          = 65536 * (K_loc + 1) * N₁ ^ 3 := by ring
        _ ≤ 131072 * (K_loc + 1) * N₁ ^ 3 := this
    exact ((Nat.add_le_add ht1 hdiv).trans hsum).trans (Nat.mul_le_mul_left _ hN3_X)
  have hguard_X : guard ≤ K_grd * X := by
    have hg1 : guard ≤ K_grd * N₁ ^ K_grd := by
      have hr := hgrd_spec.1; rw [polyBound_eq_natCast] at hr; exact (Nat.cast_le (α := ℝ)).mp hr
    exact hg1.trans (Nat.mul_le_mul_left K_grd (hN1_pow_le_X K_grd hEb_Kgrd))
  have hq_X : qPrec ≤ (K_grd + 1) * X := by dsimp [qPrec]; nlinarith only [hguard_X, hp_N1, hN1_X]
  have hin_CX : (D4Plan.input x).length ≤ C_big * X :=
    ((hIn_len x).trans (Nat.mul_le_mul_left K_in (hN1_pow_le_X K_in hEb_Kin))).trans
      (Nat.mul_le_mul_right X ((Nat.le_add_right K_in 2).trans hKI_Cbig))
  have hwi_X : ∀ nd : SoloNode x f PktOK, nd.d ≤ D →
      nd.toStoppedSpec.tableBits.length ≤ K_wi * X ∧
      (NodePortsBounded x.S nd → nd.toWorkItem.bits.length ≤ K_wi * X) := by
    intro nd hnd
    have hb := hNode_len x hf E_pkt o_pkt nd hnd
    have hpow := hN1_pow_le_X K_wi hEb_Kwi
    exact ⟨hb.1.trans (Nat.mul_le_mul_left K_wi hpow), fun hp => (hb.2 hp).trans (Nat.mul_le_mul_left K_wi hpow)⟩
  have hlf_X : x.l * f.natDegree ≤ 8 * (C + 1) * X := by
    calc x.l * f.natDegree ≤ (2 * C * N₁) * (4 * N₁) := Nat.mul_le_mul hl_N1 hdeg_f_N1
      _ = 8 * C * N₁ ^ 2 := by ring
      _ ≤ 8 * (C + 1) * X := Nat.mul_le_mul (Nat.mul_le_mul_left 8 (Nat.le_succ C)) hN2_X
  have hres_C : ∀ z : B f x.l qPrec, (residue f x.l qPrec hf z).length ≤ 64 * C_big * X ^ 2 := by
    intro z
    have hcg : (C + 1) * (K_grd + 2) ≤ C_big :=
      (Nat.mul_le_mul_right _ (Nat.succ_le_succ (Nat.le_succ C))).trans hCG_Cbig
    calc (residue f x.l qPrec hf z).length
        ≤ 64 * (C + 1) * (K_grd + 2) * X ^ 2 := residue_len_X2 hf z hX1 hq_X hlf_X
      _ = 64 * ((C + 1) * (K_grd + 2)) * X ^ 2 := by ring
      _ ≤ 64 * C_big * X ^ 2 := Nat.mul_le_mul_right (X ^ 2) (Nat.mul_le_mul_left 64 hcg)
  have hctx_C : ctx.length ≤ 131072 * C_big * X ^ 2 := by
    have hc0 := contextV2_len_X2 x.S x.m x.p guard x.l C K_grd X (polynomialBits f)
      hX1 (hxS_N1.trans hN1_X) (hlev_N1.trans hN1_X)
      (hD_N1.trans (Nat.mul_le_mul_left 8 hN1_X)) h64sh_X hguard_X hq_X
      (hl_N1.trans (Nat.mul_le_mul_left (2 * C) hN1_X))
      (hpf_N1.trans (Nat.mul_le_mul_left 4 hN1_X))
    rw [Nat.mul_assoc 131072 (C + 2) (K_grd + 2)] at hc0
    exact hc0.trans (Nat.mul_le_mul_right (X ^ 2) (Nat.mul_le_mul_left 131072 hCG_Cbig))
  have hhdr_X3 : (header P).length ≤ 1048576 * C_big * X ^ 3 := by
    let cap_h := 131072 * (K_loc + 1) * X + K_grd * X + 4 * X + 2
    have hh1 : (header P).length ≤ (2 * cap_h + 2) * 3 + 1 := by
      apply pack_len_le _ cap_h
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · change (countWord (2 ^ B_bud)).length ≤ cap_h
        rw [countWord_two_pow]; simp only [List.length_append, List.length_replicate, List.length_singleton]
        dsimp [cap_h]; omega
      · exact (countWord_len_le_succ guard).trans (by dsimp [cap_h]; omega)
      · change (polynomialBits f).length ≤ cap_h
        have := hpf_N1.trans (Nat.mul_le_mul_left 4 hN1_X); dsimp [cap_h]; omega
    dsimp [cap_h] at hh1
    have hsum_LG : (2 * K_loc + K_grd + 4) * X ≤ C_big * X :=
      Nat.mul_le_mul_right X ((by nlinarith only [Nat.zero_le K_loc, Nat.zero_le K_grd] :
        2 * K_loc + K_grd + 4 ≤ (K_loc + 2) * (K_grd + 2)).trans hLG_Cbig)
    have hh2 : (header P).length ≤ 1048576 * C_big * X := by nlinarith only [hh1, hX1, hsum_LG]
    exact hh2.trans (Nat.mul_le_mul_left _ hX_X3)
  have hnd_graph_X : ∀ nd : SoloNode x f PktOK, nd.d ≤ D →
      nd.G.nV ≤ 25 * N₁ ^ (c + 2) ∧ nd.G.encode.length ≤ 25088 * X ∧ nd.pCurr ≤ 161 * X ∧
      nd.pins.length ≤ 100 * N₁ := by
    intro nd hnd
    have hxV : x.G.nV ≤ N₁ ^ (c + 2) := x.nV.trans (Nat.pow_le_pow_right hN1_pos (by omega))
    have hdS : nd.d * (3 * x.S) ≤ 24 * N₁ ^ 2 := by
      calc nd.d * (3 * x.S) ≤ (8 * N₁) * (3 * N₁) :=
            Nat.mul_le_mul (hnd.trans hD_N1) (Nat.mul_le_mul_left 3 hxS_N1)
        _ = 24 * N₁ ^ 2 := by ring
    have hN2_c2 : N₁ ^ 2 ≤ N₁ ^ (c + 2) := Nat.pow_le_pow_right hN1_pos (by omega)
    have hnV_nd : nd.G.nV ≤ 25 * N₁ ^ (c + 2) := by have h1 := nd.verts_le; omega
    have hnE_nd : nd.G.nE ≤ N₁ := (nd.edges_le.trans (Nat.div_le_self _ _)).trans hxS_N1
    have hG_enc : nd.G.encode.length ≤ 25088 * X := by
      have h1 : nd.G.encode.length ≤ 32 * (28 * N₁ ^ (c + 2)) ^ 2 := by
        refine (graph_encode_len_le nd.G).trans (Nat.mul_le_mul_left 32 (Nat.pow_le_pow_left ?_ 2))
        have hN_c2 : N₁ ≤ N₁ ^ (c + 2) := (pow_one N₁).symm.le.trans (Nat.pow_le_pow_right hN1_pos (by omega))
        have h1_c2 : 1 ≤ N₁ ^ (c + 2) := Nat.one_le_pow _ _ hN1_pos
        omega
      have h2 : 32 * (28 * N₁ ^ (c + 2)) ^ 2 = 25088 * N₁ ^ (2 * c + 4) := by
        rw [mul_pow, ← pow_mul]; ring
      rw [h2] at h1
      exact h1.trans (Nat.mul_le_mul_left 25088 (hN1_pow_le_X (2 * c + 4) hEb_2c4))
    have hpCurr_X : nd.pCurr ≤ 161 * X := by
      have hif : (if nd.d = 0 then 0 else 80 * x.S * 2 ^ D3Stopped.shift x.S (nd.d - 1)) ≤ 160 * N₁ ^ 2 := by
        split_ifs
        · exact Nat.zero_le _
        · calc 80 * x.S * 2 ^ D3Stopped.shift x.S (nd.d - 1)
              ≤ 80 * N₁ * (2 * N₁) := Nat.mul_le_mul (Nat.mul_le_mul_left 80 hxS_N1) (h2sh_N1 _)
            _ = 160 * N₁ ^ 2 := by ring
      have hxp_N2 : x.p ≤ N₁ ^ 2 := hp_N1.trans (by nlinarith only [hN1_pos])
      exact (nd.hp_le.trans ((Nat.add_le_add hxp_N2 hif).trans_eq (by ring))).trans
        (Nat.mul_le_mul_left 161 hN2_X)
    have hpins_N1 : nd.pins.length ≤ 100 * N₁ := by
      have hdiv : (4 * x.m * x.k) / 32 ^ nd.d ≤ 2 * N₁ := (Nat.div_le_self _ _).trans hmk_N1
      have h1 := nd.pins_len_le; omega
    exact ⟨hnV_nd, hG_enc, hpCurr_X, hpins_N1⟩
  obtain ⟨hbranch_X3, hdigit_X3⟩ := branch_and_digit_len_X3 hC x hL_level M_node E_pkt o_node o_pkt
    K_loc H_loc c_loc hL_bud hL_grd hf hdeg_f hpos rootUnroll hvalid hbLen hdeg_all
    hverts hdegree hcorrect K_grd K_wi C_big X
    hX1 hCbig_ge1 hC_Cbig hKG_Cbig hKW_Cbig hCG_Cbig
    (hxS_N1.trans hN1_X) (hdesc_N1.trans hN1_X) (hp_N1.trans hN1_X)
    (hl_N1.trans (Nat.mul_le_mul_left (2 * C) hN1_X)) h4m_N1 hmk_N1
    hN1_X hN2_X h64D_N2 (hD_N1.trans (Nat.mul_le_mul_left 8 hN1_X))
    (x.nV.trans (hN1_pow_le_X c (by omega))) hdeg_f_N1 hq_X
    hhdr_X3 (hin_CX.trans (Nat.mul_le_mul_left _ hX_X3))
    (fun nd hnd => ⟨(hnd_graph_X nd hnd).2.1, (hnd_graph_X nd hnd).2.2.1, (hwi_X nd hnd).1⟩)
  -- Tree invariants for `certTree`
  have hslots : D4GuardTree.slots D ≤ 64 ^ D := slots_bound_64 D
  have hsync := DetDLP.m14_sync x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc
  have hd_tree : treeAll (fun lf => ∀ m ∈ lf.doneNodes, m.d ≤ D) certTree :=
    unrollCertFuel_done_depth_le x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc guard
      (64 ^ D) [⟨D, rootNode, rootUnroll⟩] [] 1 0
      (fun it hit => by rw [List.mem_singleton] at hit; subst hit; dsimp [rootNode]; rw [rootSoloNode_d]; omega)
      (fun _ hm => by cases hm)
  have hpb_tree : treeAll (fun lf => ∀ m ∈ lf.doneNodes, NodePortsBounded x.S m) certTree :=
    unrollCertFuel_done_portsBounded x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc guard
      (64 ^ D) [⟨D, rootNode, rootUnroll⟩] [] 1 0
      (fun it hit => by rw [List.mem_singleton] at hit; subst hit; exact hRoot_pb)
      (fun _ hm => by cases hm)
  -- Core machine run bound for any `j ≤ 2 ^ B_bud`
  have hRun_query : ∀ j : ℕ, j ≤ 2 ^ B_bud →
      let uRank := if j = 0 then 0 else j - 1
      let ansW := tag ((unrollRankTreeV2 ctx rootNode.toWorkItem F).read B_bud uRank)
      (postFn (pack [rankQuery x j, ansW])).length ≤ K_word * N₁ ^ K_word →
      RunsWithin A_enum oa_enum (rankQuery x j) (postFn (pack [rankQuery x j, ansW]))
        (polyBound K_enum N * (2 : ℝ) ^ ((K_enum : ℝ) * ((x.b : ℝ) / (x.m : ℝ))))
        (polyBound K_enum N) := by
    intro j hj_le uRank ansW hpost_len
    have hu_lt : uRank < 2 ^ B_bud := by
      dsimp [uRank]; split_ifs with hj0; exact Nat.pow_pos (by decide); omega
    let cs := runCallsV2 ctx rootNode.toWorkItem F B_bud uRank
    let startW := startV2 ctx rootNode.toWorkItem B_bud uRank
    have hnum_ctx0 : num ctx 0 = D := by dsimp [ctx, D]; simp [contextV2, num, fld_pack]
    have hone_ctx : oneWord ctx = residue f x.l (guard + x.p) hf 1 :=
      oneWord_eq_residue_one x.S x.m x.p guard x.l f hf x.hl hpos (Nat.add_pos_right _ x.hp)
    have hcs_eq : cs = callsV2 ctx F (64 ^ D)
        ((todoNodes [⟨D, rootNode, rootUnroll⟩]).map (·.toWorkItem.bits))
        (([] : List (SoloNode x f PktOK)).map (·.toWorkItem.bits))
        B_bud uRank (residue f x.l (guard + x.p) hf 1) 0 := by
      dsimp only [cs]; unfold runCallsV2; rw [hnum_ctx0, hone_ctx]; rfl
    have hcall_cov : ∀ e ∈ cs, CallCovered x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc guard B_bud e := by
      intro e he; rw [hcs_eq] at he
      exact hsync.2.2.2 hRing B_bud
        (64 ^ D) [⟨D, rootNode, rootUnroll⟩] [] B_bud uRank 1 0
        (fun it hit => by rw [List.mem_singleton] at hit; subst hit; dsimp [rootNode]; rw [rootSoloNode_d]; omega)
        (fun _ hm => by cases hm)
        (by simp only [remSlots, List.map_singleton, List.sum_singleton, zero_add]; exact Nat.mul_le_mul_left _ hslots)
        (by simp [remLeaves, D]) le_rfl hu_lt e he
    have hcall_wi : ∀ e ∈ cs,
        (∀ w ∈ unpack (fld e.1 2), w.length ≤ K_wi * X) ∧
        (∀ w ∈ unpack (fld e.1 3), w.length ≤ K_wi * X) := by
      intro e he; rw [hcs_eq] at he
      exact callsV2_workItems_bounded x hf hRing M_node E_pkt o_node o_pkt K_loc H_loc c_loc (K_wi * X)
        (fun nd hnd hp => (hwi_X nd hnd).2 hp)
        (64 ^ D) [⟨D, rootNode, rootUnroll⟩] [] B_bud uRank 1 0
        (fun it hit => by rw [List.mem_singleton] at hit; subst hit; dsimp [rootNode]; rw [rootSoloNode_d]; omega)
        (fun it hit => by rw [List.mem_singleton] at hit; subst hit; exact hRoot_pb)
        (fun _ hm => by cases hm) e he
    have hcw_B : ∀ m ≤ B_bud, (countWord m).length ≤ 131072 * C_big * X + 1 := fun m hm =>
      (countWord_len_le_succ m).trans (Nat.add_le_add_right
        ((hm.trans hBbud_X).trans (Nat.mul_le_mul_right X
          (Nat.mul_le_mul_left 131072 ((Nat.succ_le_succ (Nat.le_succ K_loc)).trans hKL_Cbig)))) 1)
    have hcw_powB : ∀ m ≤ 2 ^ B_bud, (countWord m).length ≤ 131072 * C_big * X + 1 := fun m hm =>
      (countWord_len_of_le_pow hm).trans (Nat.add_le_add_right
        (hBbud_X.trans (Nat.mul_le_mul_right X
          (Nat.mul_le_mul_left 131072 ((Nat.succ_le_succ (Nat.le_succ K_loc)).trans hKL_Cbig)))) 1)
    have hcall_all : ∀ e ∈ cs,
        RunsWithin M_node o_node e.2.1 e.2.2 (polyBound K_bnd N) (polyBound K_bnd N) ∧
        e.1.length ≤ K_word * N₁ ^ K_word ∧
        e.2.1.length ≤ K_word * N₁ ^ K_word ∧
        e.2.2.length ≤ K_bnd * N₁ ^ K_bnd := by
      intro e he
      obtain ⟨nd, cert, j_q, pendN, doneN, tagB, b', u', loss', accVal,
        hd_lt, hj_q, hb'_le, hu'_lt, hloss'_le, htot_N, _, _, he1_eq, he21_eq, hrun_e⟩ := hcall_cov e he
      obtain ⟨hwi_p, hwi_d⟩ := hcall_wi e he
      obtain ⟨hnV_nd, hG_X, hpCurr_X, hpins_N1⟩ := hnd_graph_X nd hd_lt.le
      let a_nd := D3Stopped.shift x.S nd.d
      let u_nd := D3Stopped.width x.S nd.d
      have hj_cw : (countWord j_q).length ≤ 24 * (K_loc + 1) * X + 1 :=
        (countWord_len_of_le_pow (hj_q.trans (active_nBranches_le_pow2 cert))).trans
          (Nat.add_le_add_right (Nat.mul_le_mul_left _ hN1_X) 1)
      have ha_nd_N1 : a_nd ≤ N₁ := (shift_le_level_solo x.S nd.d).trans hlev_N1
      have ha_nV : a_nd * nd.G.nV ≤ 25 * X := by
        calc a_nd * nd.G.nV ≤ N₁ * (25 * N₁ ^ (c + 2)) := Nat.mul_le_mul ha_nd_N1 hnV_nd
          _ = 25 * N₁ ^ (c + 3) := by rw [mul_left_comm, ← pow_succ']
          _ ≤ 25 * X := Nat.mul_le_mul_left 25 (hN1_pow_le_X (c + 3) (by omega))
      obtain ⟨hreq_X2, hstep_X2⟩ := active_req_and_step_len_X2 nd.G nd.host a_nd u_nd nd.pCurr x.l j_q C K_loc X f cert.lbl
        hX1 (((nd.edges_le.trans (Nat.div_le_self _ _)).trans hxS_N1).trans hN1_X)
        ha_nV (hnV_nd.trans (Nat.mul_le_mul_left 25 (hN1_pow_le_X (c + 2) (by omega))))
        hG_X (hpins_N1.trans (Nat.mul_le_mul_left 100 hN1_X))
        (ha_nd_N1.trans hN1_X) (((width_le_level_solo x.S nd.d).trans hlev_N1).trans hN1_X)
        (h64sh_X nd.d) hpCurr_X (hl_N1.trans (Nat.mul_le_mul_left (2 * C) hN1_X))
        (hdeg_f_N1.trans (Nat.mul_le_mul_left 4 hN1_X)) hj_cw
      rw [Nat.mul_assoc 4194304 (C + 2) (K_loc + 2)] at hreq_X2 hstep_X2
      have he21_Kw : (D4NodeQuery.request nd.G nd.host a_nd u_nd nd.pCurr x.l f j_q).length ≤ K_word * N₁ ^ K_word := by
        apply hWord_master
        exact ((hreq_X2.trans (Nat.mul_le_mul_right (X ^ 2) (Nat.mul_le_mul_left 4194304 hCL_Cbig))).trans
          (Nat.mul_le_mul_left _ hX2_X3)).trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num)))
      have hstep_Kw : (nd.G.nE + nd.pCurr + f.natDegree + x.l + 2) +
          (stepInput nd.G a_nd u_nd nd.pCurr x.l f cert.lbl).length ≤ K_word * N₁ ^ K_word := by
        apply hWord_master
        exact ((hstep_X2.trans (Nat.mul_le_mul_right (X ^ 2) (Nat.mul_le_mul_left 4194304 hCL_Cbig))).trans
          (Nat.mul_le_mul_left _ hX2_X3)).trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num)))
      have hbnd_le : polyBound H_loc (D4NodeQuery.request nd.G nd.host a_nd u_nd nd.pCurr x.l f j_q).length +
          polyBound K_loc ((nd.G.nE + nd.pCurr + f.natDegree + x.l + 2) + (stepInput nd.G a_nd u_nd nd.pCurr x.l f cert.lbl).length) + c_loc ≤
          polyBound K_bnd N := by
        have ht1 := polyBound_comp_le H_loc K_word _ N he21_Kw
        have ht2 := polyBound_comp_le K_loc K_word _ N hstep_Kw
        have ht3 := polyBound_const_le c_loc N
        have hadd1 := polyBound_add_le (compExp H_loc K_word) (compExp K_loc K_word) N
        have hadd2 := polyBound_add_le (compExp H_loc K_word + compExp K_loc K_word) c_loc N
        have hm := polyBound_mono_K hKbnd_1 N
        linarith [ht1, ht2, ht3, hadd1, hadd2, hm]
      have hrun_bnd : RunsWithin M_node o_node e.2.1 e.2.2 (polyBound K_bnd N) (polyBound K_bnd N) :=
        DetDLP.PolyTBridge.runsWithin_mono_local hrun_e hbnd_le hbnd_le
      have he22_Kb : e.2.2.length ≤ K_bnd * N₁ ^ K_bnd := by
        have hr := runsWithin_output_len_le hrun_bnd
        rw [polyBound_eq_natCast] at hr; exact (Nat.cast_le (α := ℝ)).mp hr
      have he1_Kw : e.1.length ≤ K_word * N₁ ^ K_word := by
        have hp_unp : unpack (fld e.1 2) = pendN.map (·.toWorkItem.bits) := by
          rw [he1_eq]; simp [phaseStateV2, fld_pack, unpack_pack]
        have hd_unp : unpack (fld e.1 3) = doneN.map (·.toWorkItem.bits) := by
          rw [he1_eq]; simp [phaseStateV2, fld_pack, unpack_pack]
        rw [hp_unp] at hwi_p
        rw [hd_unp] at hwi_d
        have hloss_cw : (countWord loss').length ≤ C_big * X + 1 :=
          (countWord_len_le_succ loss').trans (Nat.add_le_add_right
            ((hloss'_le.trans hguard_X).trans (Nat.mul_le_mul_right X ((Nat.le_add_right K_grd 2).trans hKG_Cbig))) 1)
        have hps := phaseStateV2_len_X2 [tagB] ctx (residue f x.l (guard + x.p) hf accVal)
          (pendN.map (·.toWorkItem.bits)) (doneN.map (·.toWorkItem.bits)) b' u' loss' K_wi C_big X
          hX1 hCbig_ge1 hKW_Cbig (by simp) hctx_C (hres_C accVal)
          (by simp only [List.length_map]; exact (Nat.le_add_right _ doneN.length).trans (htot_N.trans h64D_X)) hwi_p
          (by simp only [List.length_map]; exact (Nat.le_add_left _ pendN.length).trans (htot_N.trans h64D_X)) hwi_d
          (hcw_B b' hb'_le) (hcw_powB u' hu'_lt.le) hloss_cw
        rw [he1_eq]
        apply hWord_master
        exact (hps.trans (Nat.mul_le_mul_left _ hX2_X3)).trans
          (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num)))
      exact ⟨hrun_bnd, he1_Kw, he21_eq ▸ he21_Kw, he22_Kb⟩
    -- Bound `startW.length`, `ansW.length`, `(rankQuery x j).length`
    have hstart_Kw : startW.length ≤ K_word * N₁ ^ K_word := by
      have hroot_wi : rootNode.toWorkItem.bits.length ≤ K_wi * X :=
        (hwi_X rootNode (by dsimp [rootNode]; rw [rootSoloNode_d]; exact Nat.zero_le D)).2
          (rootSoloNode_portsBounded x f PktOK)
      have hsw_eq : startW = phaseStateV2 [] ctx [rootNode.toWorkItem.bits] [] B_bud uRank (oneWord ctx) 0 := rfl
      have hps := phaseStateV2_len_X2 [] ctx (oneWord ctx) [rootNode.toWorkItem.bits] [] B_bud uRank 0 K_wi C_big X
        hX1 hCbig_ge1 hKW_Cbig (by simp) hctx_C (by rw [hone_ctx]; exact hres_C 1)
        (by simp only [List.length_singleton]; exact Nat.mul_pos (by norm_num) hX1)
        (fun w hw => by rw [List.mem_singleton] at hw; subst hw; exact hroot_wi)
        (by simp) (fun _ hw => by cases hw)
        (hcw_B B_bud le_rfl) (hcw_powB uRank hu_lt.le)
        (by change 1 ≤ C_big * X + 1; omega)
      rw [hsw_eq]
      apply hWord_master
      exact (hps.trans (Nat.mul_le_mul_left _ hX2_X3)).trans
        (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num)))
    have hans_Kw : ansW.length ≤ K_word * N₁ ^ K_word := by
      have htree_eq : unrollRankTreeV2 ctx rootNode.toWorkItem F = treeMap (SoloLeafData.toBits ctx) certTree := by
        unfold unrollRankTreeV2
        rw [hnum_ctx0, hone_ctx]
        exact (hsync.1 hRing
          (64 ^ D) [⟨D, rootNode, rootUnroll⟩] [] 1 0 (by simpa [remSlots] using hslots)).symm
      have hans_eq : ansW = tag ((certTree.read B_bud uRank).map (SoloLeafData.toBits ctx)) := by
        dsimp only [ansW]; rw [htree_eq, treeMap_read]
      rw [hans_eq]
      cases hread : certTree.read B_bud uRank with
      | none =>
        change [false].length ≤ K_word * N₁ ^ K_word
        apply hWord_master
        simp only [List.length_singleton]
        have : 1 ≤ C_big * X ^ 3 := Nat.mul_pos hCbig_ge1 (hX1.trans hX_X3)
        nlinarith only [this]
      | some lf =>
        change (true :: SoloLeafData.toBits ctx lf).length ≤ K_word * N₁ ^ K_word
        have hlf : lf.Valid := treeAll_read hvalid B_bud uRank hread
        have hlf_d : ∀ m ∈ lf.doneNodes, m.d ≤ D := treeAll_read hd_tree B_bud uRank hread
        have hlf_pb : ∀ m ∈ lf.doneNodes, NodePortsBounded x.S m := treeAll_read hpb_tree B_bud uRank hread
        have hwt_eq : finishWt ctx (residue f x.l (guard + x.p) hf lf.accVal) lf.lossSum =
            residue f x.l qPrec hf lf.weight :=
          finishWt_eq_residue_shift x.S x.m x.p guard x.l lf.lossSum f hf hlf.1 _ lf.accVal rfl
        have hdone_pack : (pack (lf.doneNodes.map (·.toWorkItem.bits))).length ≤ 16384 * C_big * X ^ 2 := by
          have hd1 : (pack (lf.doneNodes.map (·.toWorkItem.bits))).length ≤
              (2 * (K_wi * X) + 2) * lf.doneNodes.length + 1 := by
            refine (pack_len_le _ (K_wi * X) ?_).trans_eq (by simp)
            intro w hw; obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hw
            exact (hwi_X m (hlf_d m hm)).2 (hlf_pb m hm)
          have hd_len : lf.doneNodes.length ≤ 4096 * X := hlf.2.1.trans h64D_X
          have hm := Nat.mul_le_mul (le_rfl : 2 * (K_wi * X) + 2 ≤ 2 * (K_wi * X) + 2) hd_len
          have h2 : (2 * (K_wi * X) + 2) * lf.doneNodes.length + 1 ≤ 16384 * (K_wi + 2) * X ^ 2 := by
            nlinarith only [hm, hX1, hX_X2]
          exact (hd1.trans h2).trans (Nat.mul_le_mul_right (X ^ 2) (Nat.mul_le_mul_left 16384 hKW_Cbig))
        have hwt_len := hres_C lf.weight
        unfold SoloLeafData.toBits
        rw [hwt_eq, List.length_cons]
        have htb : (pack [residue f x.l qPrec hf lf.weight, pack (lf.doneNodes.map (·.toWorkItem.bits))]).length ≤
            (2 * (16384 * C_big * X ^ 2) + 2) * 2 + 1 := by
          apply pack_len_le _ (16384 * C_big * X ^ 2)
          intro w hw
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
          rcases hw with rfl | rfl
          · exact hwt_len.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num)))
          · exact hdone_pack
        apply hWord_master
        have hCX2_3 : C_big * X ^ 2 ≤ C_big * X ^ 3 := Nat.mul_le_mul_left C_big hX2_X3
        have h1_c : 1 ≤ C_big * X ^ 3 := Nat.mul_pos hCbig_ge1 (hX1.trans hX_X3)
        nlinarith only [htb, hCX2_3, h1_c]
    have hrq_Kw : (rankQuery x j).length ≤ K_word * N₁ ^ K_word := by
      have hj_cw := hcw_powB j hj_le
      let cap_rq := C_big * X + 131072 * C_big * X + 2
      have hrq1 : (rankQuery x j).length ≤ (2 * cap_rq + 2) * 2 + 1 := by
        apply pack_len_le _ cap_rq
        intro w hw
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl <;> (dsimp [cap_rq]; omega)
      apply hWord_master
      dsimp [cap_rq] at hrq1
      have hCX_3 : C_big * X ≤ C_big * X ^ 3 := Nat.mul_le_mul_left C_big hX_X3
      have h1_c : 1 ≤ C_big * X ^ 3 := Nat.mul_pos hCbig_ge1 (hX1.trans hX_X3)
      nlinarith only [hrq1, hCX_3, h1_c]
    -- Bound `maxLen startW ansW cs + 64 ^ D ≤ M_len`
    let M_len := K_len * N₁ ^ K_len
    have hpair_len : ∀ s a : Wd, (callPair s a).length = 2 * s.length + 1 + a.length := by
      intro s a; unfold callPair DetDLP_W1_Queries.frame; simp [List.length_flatMap]; omega
    have hw_pair_len : ∀ s a : Wd, (D4RankWalker.pair s a).length = 2 * s.length + 1 + a.length := hpair_len
    have hWL_bound : ∀ a b : ℕ, a ≤ K_word * N₁ ^ K_word → b ≤ K_bnd * N₁ ^ K_bnd →
        8 * a + 4 * b + 4104 * N₁ ^ 2 ≤ M_len := by
      intro a b ha hb
      obtain ⟨Pw, hPw⟩ : ∃ P_w, P_w = N₁ ^ K_word := ⟨_, rfl⟩
      obtain ⟨Pb, hPb⟩ : ∃ P_b, P_b = N₁ ^ K_bnd := ⟨_, rfl⟩
      obtain ⟨Pl, hPl⟩ : ∃ P_l, P_l = N₁ ^ K_len := ⟨_, rfl⟩
      have hPw_Pl : Pw ≤ Pl := by rw [hPw, hPl]; exact Nat.pow_le_pow_right hN1_pos hKlen_exp_w
      have hPb_Pl : Pb ≤ Pl := by rw [hPb, hPl]; exact Nat.pow_le_pow_right hN1_pos hKlen_exp_b
      have hN2_Pl : N₁ ^ 2 ≤ Pl := by rw [hPl]; exact Nat.pow_le_pow_right hN1_pos hKlen_ge2
      rw [← hPw] at ha
      rw [← hPb] at hb
      dsimp [M_len]; rw [← hPl]
      have ha' : a ≤ K_word * Pl := ha.trans (Nat.mul_le_mul_left K_word hPw_Pl)
      have hb' : b ≤ K_bnd * Pl := hb.trans (Nat.mul_le_mul_left K_bnd hPb_Pl)
      have hm := Nat.mul_le_mul_right Pl hKlen_sum
      nlinarith only [ha', hb', hN2_Pl, hm]
    have hmaxLen_le : maxLen startW ansW cs + 64 ^ D ≤ M_len := by
      have hfold_le : ∀ xs : List Call, (∀ e ∈ xs, span e ≤ 3 * (K_word * N₁ ^ K_word) + K_bnd * N₁ ^ K_bnd + 2) →
          (xs.map span).foldr max 0 ≤ 3 * (K_word * N₁ ^ K_word) + K_bnd * N₁ ^ K_bnd + 2 := by
        intro xs hxs
        induction xs with
        | nil => simp
        | cons e rest ihr =>
          simp only [List.map_cons, List.foldr_cons]
          exact max_le (hxs e List.mem_cons_self) (ihr fun e' he' => hxs e' (List.mem_cons_of_mem _ he'))
      have hspan_cs : ∀ e ∈ cs, span e ≤ 3 * (K_word * N₁ ^ K_word) + K_bnd * N₁ ^ K_bnd + 2 := by
        intro e he
        obtain ⟨_, he1, he21, he22⟩ := hcall_all e he
        unfold span; rw [hw_pair_len, hw_pair_len]
        exact max_le (by omega) (by omega)
      have hf_cs := hfold_le cs hspan_cs
      have hinit_p : (D4RankWalker.pair startW []).length ≤ 3 * (K_word * N₁ ^ K_word) + K_bnd * N₁ ^ K_bnd + 2 := by
        rw [hw_pair_len, List.length_nil]; omega
      have hans_p : ansW.length ≤ 3 * (K_word * N₁ ^ K_word) + K_bnd * N₁ ^ K_bnd + 2 := by omega
      have hml : maxLen startW ansW cs ≤ 3 * (K_word * N₁ ^ K_word) + K_bnd * N₁ ^ K_bnd + 2 :=
        max_le (max_le hinit_p hans_p) hf_cs
      have hsum_m : maxLen startW ansW cs + 64 ^ D ≤
          8 * (K_word * N₁ ^ K_word) + 4 * (K_bnd * N₁ ^ K_bnd) + 4104 * N₁ ^ 2 := by
        have h1_N2 : 1 ≤ N₁ ^ 2 := Nat.one_le_pow _ _ hN1_pos
        omega
      exact hsum_m.trans (hWL_bound _ _ le_rfl le_rfl)
    -- Execute walker `hWalk`
    have hpre_eq : preFn (rankQuery x j) = startW :=
      preWalkGen_eq_startV2 x hL_level E_pkt o_pkt K_loc j hf
    have hwalk_run := (hWalk x.S x.m x.p guard x.l f rootNode.toWorkItem F B_bud uRank
      (polyBound K_bnd N) (polyBound K_bnd N)
      (polyBound_nonneg K_bnd N) (polyBound_nonneg K_bnd N)
      (fun e he => (hcall_all e he).1)).2
    have hwalk_KW : RunsWithin W_mach o_walk (preFn (rankQuery x j)) ansW
        (polyBound K_W N) (polyBound K_W N) := by
      rw [hpre_eq]
      refine DetDLP.PolyTBridge.runsWithin_mono_local hwalk_run ?_ ?_
      · have hc1 := polyBound_comp_le K_walk K_len (maxLen startW ansW cs + 64 ^ D) N hmaxLen_le
        have hb1 : polyBound K_bnd N + 1 ≤ polyBound (K_bnd + 1) N := by
          have h1_pb : (1 : ℝ) ≤ polyBound 1 N := by simpa using polyBound_const_le 1 N
          have ha := polyBound_add_le K_bnd 1 N
          linarith [h1_pb, ha]
        have hm1 : polyBound K_walk (maxLen startW ansW cs + 64 ^ D) * (polyBound K_bnd N + 1) ≤
            polyBound (compExp K_walk K_len) N * polyBound (K_bnd + 1) N :=
          mul_le_mul hc1 hb1 (by linarith [polyBound_nonneg K_bnd N]) (polyBound_nonneg _ _)
        exact (hm1.trans (polyBound_mul_le _ _ N)).trans (polyBound_mono_K hKW_tm N)
      · have hc1 := polyBound_comp_le K_walk K_len (maxLen startW ansW cs + 64 ^ D) N hmaxLen_le
        have hb1 := polyBound_const_mul_succ K_walk K_bnd N
        exact ((add_le_add hc1 hb1).trans (polyBound_add_le _ _ N)).trans (polyBound_mono_K hKW_sp N)
    -- Execute `soloOneCall`
    have hans_ne : ansW ≠ [] := by
      dsimp only [ansW]
      cases (unrollRankTreeV2 ctx rootNode.toWorkItem F).read B_bud uRank <;> intro h <;> cases h
    have h1_N2 : 1 ≤ N₁ ^ 2 := Nat.one_le_pow _ _ hN1_pos
    have h1_oc : (callPair (rankQuery x j) []).length ≤ M_len := by
      rw [hpair_len, List.length_nil]
      exact (by omega : 2 * (rankQuery x j).length + 1 ≤ 8 * (K_word * N₁ ^ K_word) + 4 * 0 + 4104 * N₁ ^ 2).trans
        (hWL_bound _ 0 le_rfl (Nat.zero_le _))
    have h2_oc : (callPair (rankQuery x j) (preFn (rankQuery x j))).length ≤ M_len := by
      rw [hpair_len, hpre_eq]
      exact (by omega : 2 * (rankQuery x j).length + 1 + startW.length ≤
        8 * (K_word * N₁ ^ K_word) + 4 * 0 + 4104 * N₁ ^ 2).trans (hWL_bound _ 0 le_rfl (Nat.zero_le _))
    have h3_oc : (callPair (rankQuery x j) ansW).length ≤ M_len := by
      rw [hpair_len]
      exact (by omega : 2 * (rankQuery x j).length + 1 + ansW.length ≤
        8 * (K_word * N₁ ^ K_word) + 4 * 0 + 4104 * N₁ ^ 2).trans (hWL_bound _ 0 le_rfl (Nat.zero_le _))
    have h4_oc : ansW.length ≤ M_len :=
      (by omega : ansW.length ≤ 8 * (K_word * N₁ ^ K_word) + 4 * 0 + 4104 * N₁ ^ 2).trans
        (hWL_bound _ 0 le_rfl (Nat.zero_le _))
    have h5_oc : (postFn (pack [rankQuery x j, ansW])).length ≤ M_len :=
      (by omega : (postFn (pack [rankQuery x j, ansW])).length ≤
        8 * (K_word * N₁ ^ K_word) + 4 * 0 + 4104 * N₁ ^ 2).trans (hWL_bound _ 0 le_rfl (Nat.zero_le _))
    have hoc_run := hOneCall (rankQuery x j) ansW (polyBound K_W N) (polyBound K_W N) M_len
      (polyBound_nonneg K_W N) (polyBound_nonneg K_W N) hans_ne hwalk_KW h1_oc h2_oc h3_oc h4_oc h5_oc
    have hoc_KA : RunsWithin A_enum oa_enum (rankQuery x j) (postFn (pack [rankQuery x j, ansW]))
        (polyBound K_A N) (polyBound K_A N) := by
      refine DetDLP.PolyTBridge.runsWithin_mono_local hoc_run ?_ ?_
      · have hc1 := polyBound_comp_le K_one K_len M_len N le_rfl
        have hadd_W : polyBound K_W N + polyBound K_W N + 1 ≤ polyBound (2 * K_W) N + 1 := by
          have hw := polyBound_add_le K_W K_W N
          rw [show K_W + K_W = 2 * K_W from (two_mul K_W).symm] at hw
          linarith [hw]
        have htw : (K_one : ℝ) * (polyBound K_W N + polyBound K_W N + 1) ≤
            polyBound (K_one * (2 * K_W + 1)) N :=
          (mul_le_mul_of_nonneg_left hadd_W (Nat.cast_nonneg _)).trans
            (polyBound_const_mul_succ K_one (2 * K_W) N)
        have hsum := (add_le_add hc1 htw).trans (polyBound_add_le _ _ N)
        have h2mul := two_mul_polyBound_le (compExp K_one K_len + K_one * (2 * K_W + 1)) N
        exact ((mul_le_mul_of_nonneg_left hsum (by positivity)).trans h2mul).trans
          (polyBound_mono_K hKA_tm N)
      · have hc1 := polyBound_comp_le K_one K_len M_len N le_rfl
        have hsw := polyBound_const_mul_succ K_one K_W N
        exact ((add_le_add hc1 hsw).trans (polyBound_add_le _ _ N)).trans (polyBound_mono_K hKA_sp N)
    have hpow_ge1 : (1 : ℝ) ≤ (2 : ℝ) ^ ((K_enum : ℝ) * ((x.b : ℝ) / (x.m : ℝ))) :=
      Real.one_le_rpow (by norm_num) (by positivity)
    have hKA_Kenum := polyBound_mono_K hKA_enum N
    exact DetDLP.PolyTBridge.runsWithin_mono_local hoc_KA
      (hKA_Kenum.trans (le_mul_of_one_le_right (polyBound_nonneg K_enum N) hpow_ge1))
      hKA_Kenum
  obtain ⟨post_header, post_branch⟩ := postWalk_spec x hL_level M_node E_pkt o_node o_pkt
    K_loc H_loc c_loc hf hdeg_f hpos rootUnroll hvalid hbLen hdeg_all hverts hdegree hcorrect
  -- Assemble all 8 conjuncts of `Enumerates`
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (1) Header run (`j = 0`)
    let ans0 := tag ((unrollRankTreeV2 ctx rootNode.toWorkItem F).read B_bud 0)
    have hpost0 : postFn (pack [rankQuery x 0, ans0]) = header P :=
      post_header ans0
    have hhdr_Kw : (header P).length ≤ K_word * N₁ ^ K_word :=
      hWord_master _ (hhdr_X3.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num))))
    have hr0 := hRun_query 0 (Nat.zero_le _) (by
      rw [if_pos rfl]
      change (postFn (pack [rankQuery x 0, ans0])).length ≤ _
      rw [hpost0]
      exact hhdr_Kw)
    rw [if_pos rfl] at hr0
    change RunsWithin A_enum oa_enum (rankQuery x 0) (postFn (pack [rankQuery x 0, ans0])) _ _ at hr0
    rwa [hpost0] at hr0
  · -- (2) Branch run (`j = u.val + 1`)
    intro u
    let ansU := tag ((unrollRankTreeV2 ctx rootNode.toWorkItem F).read B_bud u.val)
    have hpostU : postFn (pack [rankQuery x (u.val + 1), ansU]) = branch P u :=
      post_branch u
    have hbr_Kw : (branch P u).length ≤ K_word * N₁ ^ K_word :=
      hWord_master _ ((hbranch_X3 u).trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num))))
    have hrU := hRun_query (u.val + 1) u.isLt (by
      rw [if_neg (Nat.succ_ne_zero u.val), Nat.add_sub_cancel]
      change (postFn (pack [rankQuery x (u.val + 1), ansU])).length ≤ _
      rw [hpostU]
      exact hbr_Kw)
    rw [if_neg (Nat.succ_ne_zero u.val), Nat.add_sub_cancel] at hrU
    change RunsWithin A_enum oa_enum (rankQuery x (u.val + 1)) (postFn (pack [rankQuery x (u.val + 1), ansU])) _ _ at hrU
    rwa [hpostU] at hrU
  · -- (3) Branch count bound
    have hN_eq : (P.N : ℝ) = (2 : ℝ) ^ B_bud := by change ((2 ^ B_bud : ℕ) : ℝ) = _; push_cast; rfl
    rw [hN_eq]
    refine hbud_spec.2.1.trans (Real.exp_le_exp.mpr ?_)
    have hnn : (0 : ℝ) ≤ (x.b : ℝ) / (Nat.clog 2 x.S : ℝ) ^ ((7 : ℝ) / 40) +
        (Nat.clog 2 x.S : ℝ) ^ ((13 : ℝ) / 10) := by positivity
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hKbud_enum) hnn
  · -- (4) Residual digit grid bound
    intro u
    refine (hgrd_spec.2.1 (P.R u).nV (P.vertices u)).trans (Real.exp_le_exp.mpr ?_)
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hKgrd_enum) (by positivity)
  · -- (5) `P.guard ≤ scale`
    exact hgrd_spec.1.trans (polyBound_mono_K hKgrd_enum N)
  · -- (6) `(header P).length ≤ scale`
    have hhdr_Kw : (header P).length ≤ K_word * N₁ ^ K_word :=
      hWord_master _ (hhdr_X3.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num))))
    have hhdr_Kl : (header P).length ≤ K_len * N₁ ^ K_len :=
      hhdr_Kw.trans (Nat.mul_le_mul hKlen_exp_w (Nat.pow_le_pow_right hN1_pos hKlen_exp_w))
    have hr : ((header P).length : ℝ) ≤ polyBound K_len N := by
      rw [polyBound_eq_natCast]; exact_mod_cast hhdr_Kl
    exact hr.trans (polyBound_mono_K hKlen_enum N)
  · -- (7) `(digitDesc P u a).length ≤ scale`
    intro u a
    have hdd_Kw : (digitDesc P u a).length ≤ K_word * N₁ ^ K_word :=
      hWord_master _ (hdigit_X3 u a)
    have hdd_Kl : (digitDesc P u a).length ≤ K_len * N₁ ^ K_len :=
      hdd_Kw.trans (Nat.mul_le_mul hKlen_exp_w (Nat.pow_le_pow_right hN1_pos hKlen_exp_w))
    have hr : ((digitDesc P u a).length : ℝ) ≤ polyBound K_len N := by
      rw [polyBound_eq_natCast]; exact_mod_cast hdd_Kl
    exact hr.trans (polyBound_mono_K hKlen_enum N)
  · -- (8) `precision` and `spacing` bounds
    intro u
    obtain ⟨hp_b, hs_b⟩ := hgrd_spec.2.2.1 P.f (P.R u) P.deg (P.vertices u)
    exact ⟨hp_b.trans (Nat.mul_le_mul_right x.b hKgrd_enum),
      hs_b.trans (Nat.mul_le_mul_right x.b hKgrd_enum)⟩
