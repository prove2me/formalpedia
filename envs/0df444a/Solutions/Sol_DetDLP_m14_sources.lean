-- Prove2me | solution 1 for DetDLP.m14_sources
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-25T07:59:26.010466+00:00
-- url     : https://prove2.me/submissions/7004bc8a-c275-4de3-b2fc-75e893137f83

import Definitions.Def_DetDLP_D4SoloPlanDefs
import Definitions.Def_DetDLP_W1_Pipeline
import Theorems.Thm_DetDLP_d4_concrete_source_evaluator_machine
import Theorems.Thm_DetDLP_d4_unroll_tree_bit_budget
import Theorems.Thm_DetDLP_d4_unroll_guard_and_residual_bounds
import Theorems.Thm_DetDLP_d4_active_node_preconditions
import Theorems.Thm_DetDLP_d4_reattach_poly_and_spec
import Theorems.Thm_DetDLP_m14_base_fuel
import Theorems.Thm_DetDLP_m14_plan_obligations
import Theorems.Thm_DetDLP_m14_bounds
import Theorems.Thm_DetDLP_m14_pkt

set_option autoImplicit false
set_option maxHeartbeats 800000

open Groundwork Polynomial Finset DetDLP DetDLP.AppendixD4 DetDLP.ResidualScalarOracle
open DetDLP.D4Plan DetDLP.D4StoppedNode DetDLP.D4RankWalker DetDLP.D4GuardTree
open DetDLP.D4SoloRaw DetDLP.D4SoloNode DetDLP.D4SoloRoot DetDLP.D4SoloStep
open DetDLP.D4SoloStepEq DetDLP.D4SoloTree DetDLP.D4SoloForest DetDLP.D4SoloPlanDefs
open DetDLP_W1_Queries OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open DetDLP.w5_SplitArithmetic

namespace DetDLP.M14SourcesInternal

private theorem deg_le_nE (G : BipartiteMultigraph) (v : Fin G.nV) : G.deg v ≤ G.nE := by
  unfold BipartiteMultigraph.deg BipartiteMultigraph.ports
  exact (List.length_filter_le _ _).trans (by simp)

private theorem descOf_len_ge_payload (d₀ : ℕ) (f : ℤ[X]) (payload : Bits) :
    payload.length ≤ (D3Stopped.descOf d₀ f payload).length := by
  unfold D3Stopped.descOf
  exact DetDLP.m14_base_fuel.2.2.2.2.1 (by simp)

private theorem descOf_len_le (d₀ : ℕ) (f : ℤ[X]) (payload : Bits) :
    (D3Stopped.descOf d₀ f payload).length ≤ 16 * (d₀ + f.natDegree + payload.length + 2) := by
  unfold D3Stopped.descOf
  let cap := d₀ + f.natDegree + payload.length + 1
  have h1 : (Encoding.encodeList id [countWord d₀, polynomialBits f, payload]).length ≤
      (2 * cap + 2) * 3 + 1 := by
    apply length_encodeList_le id _ cap
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact (DetDLP.m14_bounds.1 d₀).trans (by dsimp [cap]; omega)
    · simp only [id_eq, polynomialBits, List.length_ofFn]; dsimp [cap]; omega
    · simp only [id_eq]; dsimp [cap]; omega
  dsimp [cap] at h1
  omega

private theorem stopped_prec_le_guard (S D p d pCurr : ℕ)
    (hD1 : 1 ≤ D) (hd_le : d ≤ D)
    (hp_le : pCurr ≤ p + (if d = 0 then 0 else 80 * S * 2 ^ D3Stopped.shift S (d - 1))) :
    pCurr ≤ totalGuard S D + p := by
  have h64 : 64 ≤ 64 ^ D := by
    calc 64 = 64 ^ 1 := by ring
      _ ≤ 64 ^ D := Nat.pow_le_pow_right (by decide) hD1
  have hif : (if d = 0 then 0 else 80 * S * 2 ^ D3Stopped.shift S (d - 1)) ≤ totalGuard S D := by
    split_ifs with hd0
    · exact Nat.zero_le _
    · have hsh : D3Stopped.shift S (d - 1) ≤ D3Stopped.shift S D :=
        shift_mono_solo S ((Nat.sub_le d 1).trans hd_le)
      have hpow : 2 ^ D3Stopped.shift S (d - 1) ≤ 2 ^ D3Stopped.shift S D :=
        Nat.pow_le_pow_right (by decide) hsh
      unfold totalGuard localAllowance
      have h1 : 80 * S * 2 ^ D3Stopped.shift S (d - 1) ≤ 2 * (40 * (S + 1) * (D3Stopped.shift S D + 1) * 2 ^ D3Stopped.shift S D) := by
        have hsh1 : 1 ≤ D3Stopped.shift S D + 1 := Nat.succ_pos _
        calc 80 * S * 2 ^ D3Stopped.shift S (d - 1)
            ≤ 80 * (S + 1) * 1 * 2 ^ D3Stopped.shift S D := by
              rw [mul_one]; exact Nat.mul_le_mul (Nat.mul_le_mul_left 80 (Nat.le_succ S)) hpow
          _ ≤ 80 * (S + 1) * (D3Stopped.shift S D + 1) * 2 ^ D3Stopped.shift S D := by gcongr
          _ = 2 * (40 * (S + 1) * (D3Stopped.shift S D + 1) * 2 ^ D3Stopped.shift S D) := by ring
      have h2 : 2 * (40 * (S + 1) * (D3Stopped.shift S D + 1) * 2 ^ D3Stopped.shift S D) ≤
          (40 * (S + 1) * (D3Stopped.shift S D + 1) * 2 ^ D3Stopped.shift S D) * 64 ^ D := by
        calc 2 * (40 * (S + 1) * (D3Stopped.shift S D + 1) * 2 ^ D3Stopped.shift S D)
            ≤ 64 * (40 * (S + 1) * (D3Stopped.shift S D + 1) * 2 ^ D3Stopped.shift S D) :=
              Nat.mul_le_mul_right _ (by decide)
          _ ≤ 64 ^ D * (40 * (S + 1) * (D3Stopped.shift S D + 1) * 2 ^ D3Stopped.shift S D) :=
              Nat.mul_le_mul_right _ h64
          _ = (40 * (S + 1) * (D3Stopped.shift S D + 1) * 2 ^ D3Stopped.shift S D) * 64 ^ D :=
              Nat.mul_comm _ _
      exact h1.trans h2
  omega

/-- A single source evaluator serves every plan assembled from a valid unrolling. -/
theorem solo_sources_complete :
    ∀ {C c : ℕ} (hC : 0 < C) (_hc : 0 < c)
        (E : PrimitiveMachine) (o : Fin E.tapeCount)
        (M_node E_pkt : PrimitiveMachine) (o_node : Fin M_node.tapeCount) (o_pkt : Fin E_pkt.tapeCount)
        (K_loc H_loc c_loc : ℕ),
    ∃ L₀_src_opt : ℕ, AppendixD4.Closed →
      ∃ (B_src : PrimitiveMachine) (ob_src : Fin B_src.tapeCount) (k_src : ℕ),
        ∀ (x : Input C c) (_hL_level : 1 ≤ D3Stopped.level x.S)
            (_hL_bud : (DetDLP.d4_unroll_tree_bit_budget C (8 * K_loc) hC).choose ≤ D3Stopped.level x.S)
        (_hL_grd : (DetDLP.d4_unroll_guard_and_residual_bounds C hC).choose ≤ D3Stopped.level x.S)
            (_hL_act : max 6 (DetDLP.d4_active_node_preconditions C hC).choose ≤ D3Stopped.level x.S)
            (_hL_src : max (C + 6) L₀_src_opt ≤ D3Stopped.level x.S) (_he : entry x E o)
            (hf : (soloPoly x.S).Monic)
        (hdeg_f : (soloPoly x.S).natDegree = 4 * Nat.clog 2 x.S)
        (hpos : 0 < (soloPoly x.S).natDegree),
        let f := soloPoly x.S
        let D := Nat.clog 32 (4 * x.m)
        let guard := totalGuard x.S D
        let B_bud := D4UnrollBudget.budget x.S D (8 * K_loc)
        let rootNode := rootSoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)
        ∀ (rootUnroll : SoloUnroll x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc D rootNode),
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
        Sources B_src ob_src k_src P := by
  classical
  intro C c hC hc E o M_node E_pkt o_node o_pkt K_loc H_loc c_loc
  obtain ⟨kappa_le_lookupQuery_len, solo_packet_adapter_machine,
    source_lengths_from_bounds, stopped_lengths_from_bounds⟩ := DetDLP.m14_pkt
  obtain ⟨countWord_len_le_succ, countWord_len_of_le_pow, encodeNatListBin_len_le, _,
    graph_encode_len_le, residue_len_le, polyBound_eq_natCast, shift_le_level_div_32768,
    input_params_le, _, source_rate_le_plan_rate, unrollCertFuel_done_depth_le,
    cap_bound_of_active_pre, _, _, soloNode_table_and_work_len, _⟩ := DetDLP.m14_bounds
  obtain ⟨hpoly, _, _, _, encodeList_mem_len_le, clog2_le_self,
    pow2_clog2_le, pow64_clog32_le, _⟩ := DetDLP.m14_base_fuel
  obtain ⟨F_pkt, oF_pkt, K_pkt, _, hF_pkt⟩ := solo_packet_adapter_machine E_pkt o_pkt K_loc
  let K_grd := (DetDLP.d4_unroll_guard_and_residual_bounds C hC).choose_spec.choose
  obtain ⟨K_wi, hK_wi1, hNode_len⟩ := soloNode_table_and_work_len (C := C) (c := c) K_loc
  let C_src := 2 * C + 2
  have hC_src : 0 < C_src := by dsimp [C_src]; omega
  let c_pkt := 2 * C + 12
  obtain ⟨c_s1, hc_s1, _, hlen_lk⟩ := source_lengths_from_bounds C c K_grd K_wi K_pkt c_pkt
  obtain ⟨c_s2, hc_s2, _, hlen_st⟩ := stopped_lengths_from_bounds C c K_grd K_wi K_pkt c_pkt
  let c_src := max c_s1 c_s2
  have hc_le_src : c ≤ c_src := hc_s1.trans (le_max_left _ _)
  let L₀_src_opt : ℕ :=
    if hCl : AppendixD4.Closed then
      (DetDLP.d4_concrete_source_evaluator_machine hCl C_src c_src K_pkt c_pkt hC_src E F_pkt o oF_pkt).choose_spec.choose_spec.choose_spec.choose
    else 0
  refine ⟨L₀_src_opt, fun hClosed => ?_⟩
  let hex := DetDLP.d4_concrete_source_evaluator_machine hClosed C_src c_src K_pkt c_pkt hC_src E F_pkt o oF_pkt
  let B_src := hex.choose
  let ob_src := hex.choose_spec.choose
  let K_B := hex.choose_spec.choose_spec.choose
  let L₀_B := hex.choose_spec.choose_spec.choose_spec.choose
  have hB_spec := hex.choose_spec.choose_spec.choose_spec.choose_spec
  have hL0_eq : L₀_src_opt = L₀_B := dif_pos hClosed
  let k_src := max 1 (max K_B (9 * (C + 1) ^ 3 * K_B))
  refine ⟨B_src, ob_src, k_src, ?_⟩
  intro x hL_level _hL_bud hL_grd hL_act hL_src he hf hdeg_f hpos
    f D guard B_bud rootNode rootUnroll certTree hvalid hbLen hdeg_all branches hverts hdegree hcorrect P
  change f.natDegree = 4 * D3Stopped.level x.S at hdeg_f
  have hLC6 : C + 6 ≤ D3Stopped.level x.S := (le_max_left _ _).trans hL_src
  have hLB : L₀_B ≤ D3Stopped.level x.S := hL0_eq ▸ (le_max_right _ _).trans hL_src
  change ∀ (u : Fin P.N) (v : Fin (P.R u).nV) (t_bits : Fin ((P.R u).deg v) → Bool),
    RunsWithin B_src ob_src (encodePortQuery (P.source u v) v.val (List.ofFn t_bits))
      (residue P.f x.l (P.guard + x.p) P.hf (P.V u v t_bits))
      (polyBound k_src (size x) * (2 : ℝ) ^ ((k_src : ℝ) * ((x.b : ℝ) / x.m)))
      (polyBound k_src (size x))
  -- Common instance bounds
  obtain ⟨hmk, hne_x, hm_x, _, _, hl_x, hp_x, hS_sz, hdesc_sz⟩ := input_params_le x
  let N := size x
  let N₁ := N + 1
  have hS_pos : 1 ≤ x.S := x.hp.trans x.pS
  have hN1_ge2 : 2 ≤ N₁ := Nat.succ_le_succ (hS_pos.trans hS_sz)
  have hN1_pos : 1 ≤ N₁ := by omega
  have hRing_f : RingOK f := (hpoly hL_level).2.2
  have hD1 : 1 ≤ D := Nat.clog_pos (by decide) (by have := x.hm; omega)
  let q := guard + x.p
  have hgrd_spec := (DetDLP.d4_unroll_guard_and_residual_bounds C hC).choose_spec.choose_spec x hL_grd
  have hguard_nat : guard ≤ K_grd * N₁ ^ K_grd := by
    have hr : (guard : ℝ) ≤ polyBound K_grd N := hgrd_spec.1
    rw [polyBound_eq_natCast K_grd N] at hr
    exact (Nat.cast_le (α := ℝ)).mp hr
  have hq_bound : q ≤ (K_grd + 1) * N₁ ^ (K_grd + 1) := by
    have hp1 : 1 ≤ N₁ ^ K_grd := Nat.one_le_pow _ _ hN1_pos
    have hxN : x.p ≤ N₁ := (hp_x.trans hS_sz).trans (Nat.le_succ N)
    calc q = guard + x.p := rfl
      _ ≤ K_grd * N₁ ^ K_grd + N₁ * N₁ ^ K_grd :=
          Nat.add_le_add hguard_nat (by nlinarith only [hxN, hp1])
      _ ≤ K_grd * N₁ ^ (K_grd + 1) + 1 * N₁ ^ (K_grd + 1) := by
          apply Nat.add_le_add
          · exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hN1_pos (Nat.le_succ _))
          · rw [one_mul, pow_succ']
      _ = (K_grd + 1) * N₁ ^ (K_grd + 1) := by ring
  -- Time/space majorant from `(K_B, level x.S)` to `(k_src, x.b / x.m)`
  have hmono_out : ∀ {inp_w out_w : List Bool},
      RunsWithin B_src ob_src inp_w out_w
        (polyBound K_B N * (2 : ℝ) ^ ((K_B : ℝ) * x.S / Real.sqrt (D3Stopped.level x.S : ℝ)))
        (polyBound K_B N) →
      RunsWithin B_src ob_src inp_w out_w
        (polyBound k_src N * (2 : ℝ) ^ ((k_src : ℝ) * ((x.b : ℝ) / x.m)))
        (polyBound k_src N) := by
    intro inp_w out_w hrun
    have hK_le : K_B ≤ k_src := (le_max_left _ _).trans (le_max_right _ _)
    have hsp_m : polyBound K_B N ≤ polyBound k_src N := by
      unfold polyBound
      apply mul_le_mul
      · exact_mod_cast hK_le
      · exact pow_le_pow_right₀ (by linarith only [Nat.cast_nonneg (α := ℝ) N]) hK_le
      · positivity
      · positivity
    have hrate := source_rate_le_plan_rate x K_B hLC6
    have hk_rate : (9 * (C + 1) ^ 3 * K_B : ℕ) ≤ k_src :=
      (le_max_right _ _).trans (le_max_right _ _)
    have hexp_m : (K_B : ℝ) * x.S / Real.sqrt (D3Stopped.level x.S : ℝ) ≤
        (k_src : ℝ) * ((x.b : ℝ) / x.m) := by
      refine hrate.trans ?_
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hk_rate)
        (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    have h2_m : (2 : ℝ) ^ ((K_B : ℝ) * x.S / Real.sqrt (D3Stopped.level x.S : ℝ)) ≤
        (2 : ℝ) ^ ((k_src : ℝ) * ((x.b : ℝ) / x.m)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp_m
    have htm_m : polyBound K_B N * (2 : ℝ) ^ ((K_B : ℝ) * x.S / Real.sqrt (D3Stopped.level x.S : ℝ)) ≤
        polyBound k_src N * (2 : ℝ) ^ ((k_src : ℝ) * ((x.b : ℝ) / x.m)) :=
      mul_le_mul hsp_m h2_m (by positivity) (by unfold polyBound; positivity)
    exact DetDLP.PolyTBridge.runsWithin_mono_local hrun htm_m hsp_m
  -- Original entry oracle bounds for arbitrary `n_any ≥ N`
  have horig_entry : ∀ (n_any : ℕ), N ≤ n_any → ∀ v₀ t₀,
      let inp₀ := encodePortQuery x.desc v₀.val (List.ofFn t₀)
      let ans₀ := encodeNatListBin (List.ofFn (x.A v₀ t₀))
      inp₀.length ≤ c_src * (n_any + 1) ^ c_src ∧
      ans₀.length ≤ c_src * (n_any + 1) ^ c_src ∧
      RunsWithin E o inp₀ ans₀ (polyBound c_src n_any) (polyBound c_src n_any) := by
    intro n_any hn_ge v₀ t₀ inp₀ ans₀
    have hrun₀ := he v₀ t₀
    have hpb_e : polyBound c N ≤ polyBound c_src n_any := by
      unfold polyBound
      apply mul_le_mul
      · exact_mod_cast hc_le_src
      · exact (pow_le_pow_left₀ (by positivity) (add_le_add (Nat.cast_le.mpr hn_ge) le_rfl) c).trans
          (pow_le_pow_right₀ (by linarith only [Nat.cast_nonneg (α := ℝ) n_any]) hc_le_src)
      · positivity
      · positivity
    have hrun_mono := DetDLP.PolyTBridge.runsWithin_mono_local hrun₀ hpb_e hpb_e
    let n₁ := n_any + 1
    have hN1_n1 : N₁ ≤ n₁ := Nat.add_le_add_right hn_ge 1
    have hinp_len : inp₀.length ≤ 16 * (x.desc.length + v₀.val + (List.ofFn t₀).length + 4) := by
      let cap_x := x.desc.length + v₀.val + (List.ofFn t₀).length + 1
      have hx1 : inp₀.length ≤ (2 * cap_x + 2) * 3 + 1 := by
        apply length_encodeList_le id _ cap_x
        intro u_w hu_w
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu_w
        rcases hu_w with rfl | rfl | rfl
        · simp only [id_eq]; dsimp [cap_x]; omega
        · exact (countWord_len_le_succ v₀.val).trans (by dsimp [cap_x]; omega)
        · simp only [id_eq]; dsimp [cap_x]; omega
      dsimp [cap_x] at hx1; omega
    have hans_len : ans₀.length ≤ (2 * N₁ + 4) * x.l + 1 := by
      have h1 : ans₀.length ≤ (2 * N₁ + 2) * (List.ofFn (x.A v₀ t₀)).length + 1 := by
        apply encodeNatListBin_len_le _ N₁
        intro m_a hma
        obtain ⟨j_a, rfl⟩ := List.mem_ofFn.mp hma
        apply (countWord_len_of_le_pow (m := x.p) (x.bounded v₀ t₀ j_a).le).trans
        have : x.p ≤ N := hp_x.trans hS_sz
        dsimp [N₁]; omega
      rw [List.length_ofFn] at h1
      exact h1.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ (by omega)) 1)
    have hv0_n1 : v₀.val ≤ n₁ ^ c :=
      (v₀.isLt.le.trans x.nV).trans (Nat.pow_le_pow_left hN1_n1 c)
    have ht0_n1 : (List.ofFn t₀).length ≤ 3 * n₁ := by
      simp only [List.length_ofFn]
      exact (deg_le_nE x.G v₀).trans (hne_x.trans (by have := hS_sz; dsimp [n₁, N] at hn_ge ⊢; omega))
    have hdesc_n1 : x.desc.length ≤ n₁ := (hdesc_sz.trans (Nat.le_succ N)).trans hN1_n1
    have hl_n1 : x.l ≤ 2 * C * n₁ := hl_x.trans (Nat.mul_le_mul_left _ ((hS_sz.trans (Nat.le_succ N)).trans hN1_n1))
    have hans_len' : ans₀.length ≤ (2 * n₁ + 4) * x.l + 1 :=
      hans_len.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ (by omega)) 1)
    have hlk := hlen_lk n₁ (hN1_pos.trans hN1_n1) x.desc.length v₀.val 0 x.l 0 0 (List.ofFn t₀).length
      ans₀.length inp₀.length 0 hdesc_n1 hv0_n1 (Nat.zero_le _) hl_n1 (Nat.zero_le _) (Nat.zero_le _) ht0_n1
      (Nat.zero_le _) hinp_len hans_len'
    have hc1_src : c_s1 * n₁ ^ c_s1 ≤ c_src * n₁ ^ c_src :=
      Nat.mul_le_mul (le_max_left _ _) (Nat.pow_le_pow_right (hN1_pos.trans hN1_n1) (le_max_left _ _))
    exact ⟨hlk.2.1.trans hc1_src, hlk.2.2.trans hc1_src, hrun_mono⟩
  -- Helper for any `StoppedSpec` case (covers both `emptyStoppedSpec` on miss and `nd.toStoppedSpec` on hit!)
  have hstopped_case : ∀ (P_st d₀ deg_st v_idx : ℕ) (G_st : Graph)
      (s_st : StoppedSpec x.G G_st f x.l P_st deg_st)
      (α_st : Fin deg_st → Bool),
      v_idx ≤ 4 * x.m + 64 ^ D →
      d₀ ≤ D →
      deg_st ≤ 2 * N₁ →
      s_st.tableBits.length ≤ K_wi * N₁ ^ K_wi →
      G_st.nE ≤ x.S / 8 ^ d₀ →
      G_st.maxDeg ≤ D3Stopped.cap x.S →
      G_st.nV ≤ 25 * N₁ ^ (c + 2) →
      x.p ≤ P_st →
      P_st ≤ x.p + (if d₀ = 0 then 0 else 80 * x.S * 2 ^ D3Stopped.shift x.S (d₀ - 1)) →
      (∀ w_p pkt_p (hp : s_st.vTable w_p = .pkt pkt_p) β_p,
        let p_p := s_st.packet w_p pkt_p hp
        let n_pkt := G_st.nE + p_p.creation + 4 * D3Stopped.level x.S + x.l + 2
        let inp_p := Encoding.encodeList id [pkt_p, List.ofFn β_p]
        p_p.creation ≤ P_st ∧
        inp_p.length ≤ K_pkt * (n_pkt + 1) ^ K_pkt ∧
        RunsWithin F_pkt oF_pkt inp_p (residue f x.l p_p.creation hf (p_p.entry β_p))
          (Real.exp ((K_pkt : ℝ) * (2 ^ D3Stopped.shift x.S (d₀ - 1) : ℕ) * Real.log n_pkt))
          (polyBound K_pkt n_pkt)) →
      RunsWithin B_src ob_src
        (encodePortQuery (stoppedDesc x.desc x.S x.l P_st d₀ f G_st s_st.tableBits) v_idx (List.ofFn α_st))
        (residue f x.l q hf (s_st.value hf x.A q α_st))
        (polyBound K_B N * (2 : ℝ) ^ ((K_B : ℝ) * x.S / Real.sqrt (D3Stopped.level x.S : ℝ)))
        (polyBound K_B N) := by
    intro P_st d₀ deg_st v_idx G_st s_st α_st hv_idx hd0_D hdeg_st htbl_st
      hnE_st hcap_st hnV_st hp_ge_st hp_le_st hpkt_st
    let pay := s_st.payload x.desc α_st
    let n_st := x.S + pay.length
    let desc_st := D3Stopped.descOf d₀ f pay
    let m_st := x.S + desc_st.length
    have hdesc_le_pay : x.desc.length ≤ pay.length :=
      encodeList_mem_len_le (by simp)
    have hN_le_n : N ≤ n_st := Nat.add_le_add_left hdesc_le_pay x.S
    have hn_le_m : n_st ≤ m_st := Nat.add_le_add_left (descOf_len_ge_payload d₀ f pay) x.S
    let n₁ := n_st + 1
    let m₁ := m_st + 1
    have hN1_n1 : N₁ ≤ n₁ := Nat.add_le_add_right hN_le_n 1
    have hn1_m1 : n₁ ≤ m₁ := Nat.add_le_add_right hn_le_m 1
    obtain ⟨hm_nV, hpkt_in_c2, hfour_c2⟩ := hlen_st N₁ n₁ m₁ hN1_ge2 hN1_n1 hn1_m1
    have hc2_src_N : c_s2 * N₁ ^ c_s2 ≤ c_src * N₁ ^ c_src :=
      Nat.mul_le_mul (le_max_right _ _) (Nat.pow_le_pow_right hN1_pos (le_max_right _ _))
    have hc2_src_n : c_s2 * n₁ ^ c_s2 ≤ c_src * n₁ ^ c_src :=
      Nat.mul_le_mul (le_max_right _ _) (Nat.pow_le_pow_right (hN1_pos.trans hN1_n1) (le_max_right _ _))
    -- Verify scalar bounds of `hB_spec.2`
    have hsh_div : D3Stopped.shift x.S (d₀ - 1) ≤ D3Stopped.level x.S / 32768 :=
      shift_le_level_div_32768 x.S (d₀ - 1)
    have hnE_Csrc : G_st.nE ≤ C_src * x.S / 8 ^ d₀ :=
      hnE_st.trans (Nat.div_le_div_right (Nat.le_mul_of_pos_left x.S hC_src))
    have hnV_msrc : G_st.nV ≤ m₁ ^ c_src := by
      have h1 : G_st.nV ≤ 25 * m₁ ^ (c + 2) :=
        hnV_st.trans (Nat.mul_le_mul_left 25 (Nat.pow_le_pow_left (hN1_n1.trans hn1_m1) _))
      exact (h1.trans hm_nV).trans (Nat.pow_le_pow_right (by omega) (le_max_right _ _))
    have hP_pos : 1 ≤ P_st := x.hp.trans hp_ge_st
    have hP_upper : P_st ≤ x.S + 80 * C_src * x.S * (if d₀ = 0 then 1 else 2 ^ D3Stopped.shift x.S (d₀ - 1)) := by
      have h1 : x.p ≤ x.S := x.pS
      have h2 : (if d₀ = 0 then 0 else 80 * x.S * 2 ^ D3Stopped.shift x.S (d₀ - 1)) ≤
          80 * C_src * x.S * (if d₀ = 0 then 1 else 2 ^ D3Stopped.shift x.S (d₀ - 1)) := by
        split_ifs with hz
        · exact Nat.zero_le _
        · calc 80 * x.S * 2 ^ D3Stopped.shift x.S (d₀ - 1)
              = 80 * 1 * x.S * 2 ^ D3Stopped.shift x.S (d₀ - 1) := by ring
            _ ≤ 80 * C_src * x.S * 2 ^ D3Stopped.shift x.S (d₀ - 1) :=
                Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hC_src))
      exact hp_le_st.trans (Nat.add_le_add h1 h2)
    have hl_Csrc : x.l ≤ C_src * x.S :=
      hl_x.trans (Nat.mul_le_mul_right x.S (by dsimp [C_src]; omega))
    have hP_le_q : P_st ≤ q := stopped_prec_le_guard x.S D x.p d₀ P_st hD1 hd0_D hp_le_st
    have hA_lt_P : ∀ v₀ t₀ j₀, x.A v₀ t₀ j₀ < 2 ^ P_st := fun v₀ t₀ j₀ =>
      (x.bounded v₀ t₀ j₀).trans_le (Nat.pow_le_pow_right (by decide) hp_ge_st)
    have h2L : 2 ^ D3Stopped.level x.S ≤ 2 * x.S := pow2_clog2_le hS_pos
    have hP_N2 : P_st ≤ 161 * N₁ ^ 2 := by
      have hif : (if d₀ = 0 then 0 else 80 * x.S * 2 ^ D3Stopped.shift x.S (d₀ - 1)) ≤ 160 * N₁ ^ 2 := by
        split_ifs
        · exact Nat.zero_le _
        · have hsh : 2 ^ D3Stopped.shift x.S (d₀ - 1) ≤ 2 * N₁ :=
            ((Nat.pow_le_pow_right (by decide) (shift_le_level_solo x.S _)).trans h2L).trans
              (Nat.mul_le_mul_left 2 (hS_sz.trans (Nat.le_succ N)))
          have hxN : x.S ≤ N₁ := hS_sz.trans (Nat.le_succ N)
          calc 80 * x.S * 2 ^ D3Stopped.shift x.S (d₀ - 1)
              ≤ 80 * N₁ * (2 * N₁) := Nat.mul_le_mul (Nat.mul_le_mul_left 80 hxN) hsh
            _ = 160 * N₁ ^ 2 := by ring
      have hxp : x.p ≤ N₁ ^ 2 := by
        have hsq : N₁ ≤ N₁ ^ 2 := by nlinarith only [hN1_pos]
        exact ((hp_x.trans hS_sz).trans (Nat.le_succ N)).trans hsq
      exact hp_le_st.trans ((Nat.add_le_add hxp hif).trans_eq (by ring))
    have hd0_N : d₀ ≤ 8 * N₁ := by
      have hcl : D ≤ 8 * N₁ := by
        have h1 : D ≤ Nat.clog 2 (4 * x.m) := by dsimp [D]; rw [Nat.clog_pow_left 2 5]; omega
        exact h1.trans ((clog2_le_self _).trans (by have := hm_x; have := hS_sz; dsimp [N₁, N]; omega))
      exact hd0_D.trans hcl
    have hdeg_f_N : f.natDegree ≤ 4 * N₁ := by
      rw [hdeg_f]
      exact Nat.mul_le_mul_left 4 ((clog2_le_self x.S).trans (hS_sz.trans (Nat.le_succ N)))
    have hG_st_len : G_st.encode.length ≤ 32 * (27 * N₁ ^ (c + 2)) ^ 2 := by
      refine (graph_encode_len_le G_st).trans (Nat.mul_le_mul_left 32 (Nat.pow_le_pow_left ?_ 2))
      have hN_c2 : N₁ ≤ N₁ ^ (c + 2) := by
        calc N₁ = N₁ ^ 1 := (pow_one N₁).symm
          _ ≤ N₁ ^ (c + 2) := Nat.pow_le_pow_right hN1_pos (by omega)
      have hnE_N : G_st.nE ≤ N₁ := (hnE_st.trans (Nat.div_le_self _ _)).trans (hS_sz.trans (Nat.le_succ N))
      omega
    have hv_idx_N2 : v_idx ≤ 65544 * N₁ ^ 2 := by
      have h64 : 64 ^ D ≤ (256 * N₁) ^ 2 := by
        have h1 := pow64_clog32_le (n := 4 * x.m) (by have := x.hm; omega)
        refine h1.trans (Nat.pow_le_pow_left ?_ 2)
        have : x.m ≤ 2 * N₁ := hm_x.trans (Nat.mul_le_mul_left 2 (hS_sz.trans (Nat.le_succ N)))
        omega
      have hm_N2 : 4 * x.m ≤ 8 * N₁ ^ 2 := by
        have : x.m ≤ 2 * N₁ := hm_x.trans (Nat.mul_le_mul_left 2 (hS_sz.trans (Nat.le_succ N)))
        nlinarith only [this, hN1_pos]
      nlinarith only [hv_idx, h64, hm_N2]
    let u_st := encodePortQuery (stoppedDesc x.desc x.S x.l P_st d₀ f G_st s_st.tableBits) v_idx (List.ofFn α_st)
    let x_st := encodeBTNInstance desc_st G_st x.S P_st x.l
    let y_st := residue f x.l P_st hf (BTNContract G_st (s_st.entry hf x.A α_st))
    let E_exp := max (2 * c + 6) (K_wi + 4)
    let X_big := N₁ ^ E_exp
    have hX1 : 1 ≤ X_big := Nat.one_le_pow _ _ hN1_pos
    have hN1_X : N₁ ≤ X_big := by
      calc N₁ = N₁ ^ 1 := (pow_one N₁).symm
        _ ≤ N₁ ^ E_exp := Nat.pow_le_pow_right hN1_pos (by dsimp [E_exp]; omega)
    have hN2_X : N₁ ^ 2 ≤ X_big := Nat.pow_le_pow_right hN1_pos (by dsimp [E_exp]; omega)
    have hG_X : G_st.encode.length ≤ 23328 * X_big := by
      have hpow_c : N₁ ^ (2 * c + 4) ≤ X_big := Nat.pow_le_pow_right hN1_pos (by dsimp [E_exp]; omega)
      have hsq : 32 * (27 * N₁ ^ (c + 2)) ^ 2 = 23328 * N₁ ^ (2 * c + 4) := by
        rw [mul_pow, ← pow_mul]; ring_nf
      exact hG_st_len.trans (hsq ▸ Nat.mul_le_mul_left _ hpow_c)
    have htbl_X : s_st.tableBits.length ≤ K_wi * X_big :=
      htbl_st.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hN1_pos (by dsimp [E_exp]; omega)))
    have hxN : x.S ≤ N₁ := hS_sz.trans (Nat.le_succ N)
    have hdescN : x.desc.length ≤ N₁ := hdesc_sz.trans (Nat.le_succ N)
    have hl_CX : x.l ≤ 2 * C * X_big := (hl_x.trans (Nat.mul_le_mul_left _ hxN)).trans (Nat.mul_le_mul_left _ hN1_X)
    have hpay_len : pay.length ≤ 16 * (N₁ + K_wi * X_big + 2 * N₁ + 2) := by
      let cap_py := N₁ + K_wi * X_big + 2 * N₁ + 1
      have h1 : pay.length ≤ (2 * cap_py + 2) * 3 + 1 := by
        apply length_encodeList_le id _ cap_py
        intro u_w hu_w
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu_w
        rcases hu_w with rfl | rfl | rfl
        · simp only [id_eq]; dsimp [cap_py]; omega
        · simp only [id_eq]; dsimp [cap_py]; omega
        · simp only [id_eq, List.length_ofFn]; dsimp [cap_py]; omega
      dsimp [cap_py] at h1; omega
    have hdesc_st_len : desc_st.length ≤ 2048 * (K_wi + 2) * X_big := by
      have hd1 := descOf_len_le d₀ f pay
      dsimp only [desc_st]
      nlinarith only [hd1, hd0_N, hdeg_f_N, hpay_len, hN1_X, hX1, Nat.zero_le K_wi]
    have hstopDesc_len : (stoppedDesc x.desc x.S x.l P_st d₀ f G_st s_st.tableBits).length ≤
        65536 * (C + 2) * (K_wi + 2) * X_big := by
      unfold stoppedDesc
      simp only [List.length_cons]
      have hin_pair : (Encoding.encodeList id [x.desc, s_st.tableBits]).length ≤
          (2 * (N₁ + K_wi * X_big + 1) + 2) * 2 + 1 := by
        apply length_encodeList_le id _ (N₁ + K_wi * X_big + 1)
        intro u_w hu_w
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu_w
        rcases hu_w with rfl | rfl <;> simp only [id_eq] <;> omega
      have hdo := descOf_len_le d₀ f (Encoding.encodeList id [x.desc, s_st.tableBits])
      let cap_sd := 23328 * X_big + 2 * C * X_big + 161 * X_big +
        16 * (8 * N₁ + 4 * N₁ + ((2 * (N₁ + K_wi * X_big + 1) + 2) * 2 + 1) + 2) + 4
      have hpk : (Encoding.encodeList id [countWord x.S, countWord x.l, countWord P_st, G_st.encode,
          D3Stopped.descOf d₀ f (Encoding.encodeList id [x.desc, s_st.tableBits])]).length ≤
          (2 * cap_sd + 2) * 5 + 1 := by
        apply length_encodeList_le id _ cap_sd
        intro u_w hu_w
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu_w
        rcases hu_w with rfl | rfl | rfl | rfl | rfl
        · exact (countWord_len_le_succ x.S).trans (by dsimp [cap_sd]; omega)
        · exact (countWord_len_le_succ x.l).trans (by dsimp [cap_sd]; omega)
        · exact (countWord_len_le_succ P_st).trans (by dsimp [cap_sd]; nlinarith only [hP_N2, hN2_X, hX1])
        · simp only [id_eq]; dsimp [cap_sd]; omega
        · simp only [id_eq]; dsimp [cap_sd]; omega
      dsimp [cap_sd] at hpk
      have h4X : 4 * X_big ≤ (C + 2) * (K_wi + 2) * X_big :=
        Nat.mul_le_mul_right X_big (by nlinarith only [Nat.zero_le C, Nat.zero_le K_wi])
      have h2CX : 2 * C * X_big ≤ (C + 2) * (K_wi + 2) * X_big :=
        Nat.mul_le_mul_right X_big (by nlinarith only [Nat.zero_le C, Nat.zero_le K_wi])
      have h2KX : 2 * K_wi * X_big ≤ (C + 2) * (K_wi + 2) * X_big :=
        Nat.mul_le_mul_right X_big (by nlinarith only [Nat.zero_le C, Nat.zero_le K_wi])
      nlinarith only [hpk, hN1_X, hX1, h4X, h2CX, h2KX]
    have hu_st_len : u_st.length ≤ 1048576 * (C + 2) * (K_wi + 2) * X_big := by
      let cap_u := 65536 * (C + 2) * (K_wi + 2) * X_big + 65545 * X_big + 2
      have h1 : u_st.length ≤ (2 * cap_u + 2) * 3 + 1 := by
        apply length_encodeList_le id _ cap_u
        intro u_w hu_w
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu_w
        rcases hu_w with rfl | rfl | rfl
        · simp only [id_eq]; dsimp [cap_u]; omega
        · refine (countWord_len_le_succ v_idx).trans ?_
          have hvX : v_idx + 1 ≤ 65545 * X_big := by nlinarith only [hv_idx_N2, hN2_X, hX1]
          dsimp [cap_u]; omega
        · simp only [id_eq, List.length_ofFn]; dsimp [cap_u]; omega
      dsimp [cap_u] at h1
      have h4X : 4 * X_big ≤ (C + 2) * (K_wi + 2) * X_big :=
        Nat.mul_le_mul_right X_big (by nlinarith only [Nat.zero_le C, Nat.zero_le K_wi])
      nlinarith only [h1, hX1, h4X]
    have hx_st_len : x_st.length ≤ 1048576 * (C + 2) * (K_wi + 2) * X_big := by
      let cap_x := 2048 * (K_wi + 2) * X_big + 23328 * X_big + 2 * C * X_big + 161 * X_big + 4
      have h1 : x_st.length ≤ (2 * cap_x + 2) * 5 + 1 := by
        apply length_encodeList_le id _ cap_x
        intro u_w hu_w
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu_w
        rcases hu_w with rfl | rfl | rfl | rfl | rfl
        · simp only [id_eq]; dsimp [cap_x]; omega
        · simp only [id_eq]; dsimp [cap_x]; omega
        · exact (countWord_len_le_succ x.S).trans (by dsimp [cap_x]; omega)
        · exact (countWord_len_le_succ P_st).trans (by dsimp [cap_x]; nlinarith only [hP_N2, hN2_X, hX1])
        · exact (countWord_len_le_succ x.l).trans (by dsimp [cap_x]; omega)
      dsimp [cap_x] at h1
      have hC2_X : X_big ≤ (C + 2) * (K_wi + 2) * X_big := by
        have h1' : 1 ≤ (C + 2) * (K_wi + 2) := by nlinarith only [Nat.zero_le C, Nat.zero_le K_wi]
        nlinarith only [h1', hX1]
      have hCX : C * X_big ≤ (C + 2) * (K_wi + 2) * X_big :=
        Nat.mul_le_mul_right X_big (by nlinarith only [Nat.zero_le C, Nat.zero_le K_wi])
      have hK2X : (K_wi + 2) * X_big ≤ (C + 2) * (K_wi + 2) * X_big :=
        Nat.mul_le_mul_right X_big (by nlinarith only [Nat.zero_le C, Nat.zero_le K_wi])
      nlinarith only [h1, hX1, hC2_X, hCX, hK2X]
    have hy_st_len : y_st.length ≤ 1048576 * (C + 2) * N₁ ^ 6 := by
      have hr := residue_len_le f x.l P_st hf (BTNContract G_st (s_st.entry hf x.A α_st))
      have hl_N : x.l ≤ 2 * C * N₁ := hl_x.trans (Nat.mul_le_mul_left _ hxN)
      have hprod_ld : x.l * f.natDegree ≤ 8 * (C + 1) * N₁ ^ 2 := by
        calc x.l * f.natDegree ≤ (2 * C * N₁) * (4 * N₁) := Nat.mul_le_mul hl_N hdeg_f_N
          _ = 8 * C * N₁ ^ 2 := by ring
          _ ≤ 8 * (C + 1) * N₁ ^ 2 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 8 (Nat.le_succ C))
      have h2P : 2 * (P_st + 1) + 2 ≤ 326 * N₁ ^ 2 := by nlinarith only [hP_N2, hN1_pos]
      have hmul := Nat.add_le_add_right (Nat.mul_le_mul h2P hprod_ld) 1
      have hN4_6 : N₁ ^ 4 ≤ N₁ ^ 6 := Nat.pow_le_pow_right hN1_pos (by decide)
      have h326 : (326 * N₁ ^ 2) * (8 * (C + 1) * N₁ ^ 2) = 2608 * (C + 1) * N₁ ^ 4 := by ring
      rw [h326] at hmul
      have h4_6 := Nat.mul_le_mul_left (2608 * (C + 1)) hN4_6
      have h1_6 : 1 ≤ N₁ ^ 6 := Nat.one_le_pow _ _ hN1_pos
      nlinarith only [hr, hmul, h4_6, h1_6]
    have huxy := hfour_c2 u_st.length x_st.length y_st.length 0 hu_st_len hx_st_len hy_st_len (Nat.zero_le _)
    apply hB_spec.2 x.S P_st q x.l d₀ deg_st v_idx x.desc x.G G_st f hf s_st x.A α_st
      hLB hsh_div hnE_Csrc hcap_st hnV_msrc hP_pos hP_upper x.hl hl_Csrc hRing_f hdeg_f hP_le_q hA_lt_P
      (huxy.1.trans hc2_src_N) (huxy.2.1.trans hc2_src_N) (huxy.2.2.1.trans hc2_src_N)
    · intro w_g β_g
      let E_n := max (c + 4) (K_wi + 4)
      let X_n := n₁ ^ E_n
      have hXn1 : 1 ≤ X_n := Nat.one_le_pow _ _ (hN1_pos.trans hN1_n1)
      have hn1_Xn : n₁ ≤ X_n := by
        calc n₁ = n₁ ^ 1 := (pow_one n₁).symm
          _ ≤ n₁ ^ E_n := Nat.pow_le_pow_right (hN1_pos.trans hN1_n1) (by dsimp [E_n]; omega)
      have hpay_n : pay.length ≤ n₁ := by dsimp [n₁, n_st]; omega
      have hdesc_n : desc_st.length ≤ 512 * X_n := by
        have hd1 := descOf_len_le d₀ f pay
        have hd_n : d₀ ≤ 8 * n₁ := hd0_N.trans (Nat.mul_le_mul_left 8 hN1_n1)
        have hdf_n : f.natDegree ≤ 4 * n₁ := hdeg_f_N.trans (Nat.mul_le_mul_left 4 hN1_n1)
        dsimp only [desc_st]
        omega
      have hw_n : w_g.val ≤ 25 * X_n := by
        have h1 : w_g.val < 25 * n₁ ^ (c + 2) :=
          w_g.isLt.trans_le (hnV_st.trans (Nat.mul_le_mul_left 25 (Nat.pow_le_pow_left hN1_n1 _)))
        exact h1.le.trans (Nat.mul_le_mul_left 25 (Nat.pow_le_pow_right (hN1_pos.trans hN1_n1) (by dsimp [E_n]; omega)))
      have hβ_n : (List.ofFn β_g).length ≤ X_n := by
        simp only [List.length_ofFn]
        exact ((deg_le_nE G_st w_g).trans ((hnE_st.trans (Nat.div_le_self _ _)).trans hxN)).trans (hN1_n1.trans hn1_Xn)
      let cap_q := 512 * X_n + 25 * X_n + 2
      have hq_len : (encodePortQuery desc_st w_g.val (List.ofFn β_g)).length ≤ (2 * cap_q + 2) * 3 + 1 := by
        apply length_encodeList_le id _ cap_q
        intro u_w hu_w
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu_w
        rcases hu_w with rfl | rfl | rfl
        · simp only [id_eq]; dsimp [cap_q]; omega
        · exact (countWord_len_le_succ w_g.val).trans (by dsimp [cap_q]; omega)
        · simp only [id_eq]; dsimp [cap_q]; omega
      have hq_top : (encodePortQuery desc_st w_g.val (List.ofFn β_g)).length ≤
          1048576 * (C + 2) * (K_wi + 2) * X_n := by
        dsimp [cap_q] at hq_len
        have h4Xn : 4 * X_n ≤ (C + 2) * (K_wi + 2) * X_n :=
          Nat.mul_le_mul_right X_n (by nlinarith only [Nat.zero_le C, Nat.zero_le K_wi])
        nlinarith only [hq_len, hXn1, h4Xn]
      exact ((hfour_c2 0 0 0 _ (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) hq_top).2.2.2).trans hc2_src_n
    · exact horig_entry n_st hN_le_n
    · intro w_p pkt_p hp β_p
      obtain ⟨hp_cr_le, hinp_p, hrun_p⟩ := hpkt_st w_p pkt_p hp β_p
      let p_p := s_st.packet w_p pkt_p hp
      let n_pkt := G_st.nE + p_p.creation + 4 * D3Stopped.level x.S + x.l + 2
      have hnpkt_pow : n_pkt ≤ (x.S + 2) ^ c_pkt := by
        let S2 := x.S + 2
        have hS2_ge2 : 2 ≤ S2 := by dsimp [S2]; omega
        have hnE_S : G_st.nE ≤ S2 := (hnE_st.trans (Nat.div_le_self _ _)).trans (by dsimp [S2]; omega)
        have hp_cr_S2 : p_p.creation ≤ 161 * S2 ^ 2 := by
          have hp_st_S2 : P_st ≤ 161 * S2 ^ 2 := by
            have hif : (if d₀ = 0 then 0 else 80 * x.S * 2 ^ D3Stopped.shift x.S (d₀ - 1)) ≤ 160 * S2 ^ 2 := by
              split_ifs
              · exact Nat.zero_le _
              · have hsh : 2 ^ D3Stopped.shift x.S (d₀ - 1) ≤ 2 * S2 :=
                  ((Nat.pow_le_pow_right (by decide) (shift_le_level_solo x.S _)).trans h2L).trans (by dsimp [S2]; omega)
                have hxs2 : x.S ≤ S2 := by dsimp [S2]; omega
                calc 80 * x.S * 2 ^ D3Stopped.shift x.S (d₀ - 1)
                    ≤ 80 * S2 * (2 * S2) := Nat.mul_le_mul (Nat.mul_le_mul_left 80 hxs2) hsh
                  _ = 160 * S2 ^ 2 := by ring
            have hxp_s2 : x.p ≤ S2 ^ 2 := by
              have hp1 : x.p ≤ S2 := x.pS.trans (by dsimp [S2]; omega)
              have hs2 : S2 ≤ S2 ^ 2 := by nlinarith only [hS2_ge2]
              exact hp1.trans hs2
            exact hp_le_st.trans ((Nat.add_le_add hxp_s2 hif).trans_eq (by ring))
          exact hp_cr_le.trans hp_st_S2
        have h4L_S : 4 * D3Stopped.level x.S ≤ 4 * S2 :=
          Nat.mul_le_mul_left 4 ((clog2_le_self x.S).trans (by dsimp [S2]; omega))
        have hl_S : x.l ≤ 2 * C * S2 := hl_x.trans (Nat.mul_le_mul_left _ (by dsimp [S2]; omega))
        have hlin : n_pkt ≤ (200 + 2 * C) * S2 ^ 2 := by
          dsimp [n_pkt]
          nlinarith only [hnE_S, hp_cr_S2, h4L_S, hl_S, hS2_ge2]
        have hcoef : 200 + 2 * C ≤ S2 ^ (2 * C + 10) := by
          calc 200 + 2 * C ≤ 2 ^ 8 * 2 ^ (2 * C + 2) := by
                have hc2 : 2 * C + 2 ≤ 2 ^ (2 * C + 2) := (Nat.lt_pow_self (by decide : 1 < 2)).le
                norm_num; omega
            _ = 2 ^ (2 * C + 10) := by rw [← pow_add]; congr 1; omega
            _ ≤ S2 ^ (2 * C + 10) := Nat.pow_le_pow_left hS2_ge2 _
        calc n_pkt ≤ S2 ^ (2 * C + 10) * S2 ^ 2 := hlin.trans (Nat.mul_le_mul_right _ hcoef)
          _ = S2 ^ c_pkt := by rw [← pow_add]
      have hS2_2N1 : x.S + 2 ≤ 2 * N₁ := by have := hS_sz; dsimp [N₁, N]; omega
      have hinp_csrc : (Encoding.encodeList id [pkt_p, List.ofFn β_p]).length ≤ c_src * n₁ ^ c_src := by
        have h1 : n_pkt + 1 ≤ (2 * N₁) ^ c_pkt + 1 :=
          Nat.add_le_add_right (hnpkt_pow.trans (Nat.pow_le_pow_left hS2_2N1 c_pkt)) 1
        exact (hinp_p.trans (Nat.mul_le_mul_left K_pkt (Nat.pow_le_pow_left h1 K_pkt))).trans
          (hpkt_in_c2.trans hc2_src_n)
      have hans_csrc : (residue f x.l p_p.creation hf (p_p.entry β_p)).length ≤ c_src * n₁ ^ c_src := by
        have hr := residue_len_le f x.l p_p.creation hf (p_p.entry β_p)
        have hpcr_N2 : p_p.creation ≤ 161 * N₁ ^ 2 := hp_cr_le.trans hP_N2
        have hl_N : x.l ≤ 2 * C * N₁ := hl_x.trans (Nat.mul_le_mul_left _ hxN)
        have hprod_ld : x.l * f.natDegree ≤ 8 * (C + 1) * N₁ ^ 2 := by
          calc x.l * f.natDegree ≤ (2 * C * N₁) * (4 * N₁) := Nat.mul_le_mul hl_N hdeg_f_N
            _ = 8 * C * N₁ ^ 2 := by ring
            _ ≤ 8 * (C + 1) * N₁ ^ 2 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 8 (Nat.le_succ C))
        have h2P : 2 * (p_p.creation + 1) + 2 ≤ 326 * N₁ ^ 2 := by nlinarith only [hpcr_N2, hN1_pos]
        have hmul := Nat.add_le_add_right (Nat.mul_le_mul h2P hprod_ld) 1
        have h326 : (326 * N₁ ^ 2) * (8 * (C + 1) * N₁ ^ 2) = 2608 * (C + 1) * N₁ ^ 4 := by ring
        rw [h326] at hmul
        have hN4_6 : N₁ ^ 4 ≤ N₁ ^ 6 := Nat.pow_le_pow_right hN1_pos (by decide)
        have h4_6 := Nat.mul_le_mul_left (2608 * (C + 1)) hN4_6
        have h1_6 : 1 ≤ N₁ ^ 6 := Nat.one_le_pow _ _ hN1_pos
        have hans_N6 : (residue f x.l p_p.creation hf (p_p.entry β_p)).length ≤ 1048576 * (C + 2) * N₁ ^ 6 := by
          nlinarith only [hr, hmul, h4_6, h1_6]
        have hcN_cn : c_src * N₁ ^ c_src ≤ c_src * n₁ ^ c_src :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hN1_n1 _)
        exact ((hfour_c2 0 0 _ 0 (Nat.zero_le _) (Nat.zero_le _) hans_N6 (Nat.zero_le _)).2.2.1.trans hc2_src_N).trans hcN_cn
      exact ⟨hnpkt_pow, hinp_csrc, hans_csrc, hrun_p⟩
  -- Prove `Sources` for every `(u, v, t_bits)`
  intro u v t_bits
  apply hmono_out
  let PktOK := pktOKOf E_pkt o_pkt K_loc x f hf
  have hd_tree : treeAll (fun lf => ∀ m ∈ lf.doneNodes, m.d ≤ D) certTree :=
    unrollCertFuel_done_depth_le x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc guard
      (64 ^ D) [⟨D, rootNode, rootUnroll⟩] [] 1 0
      (fun it hit => by rw [List.mem_singleton] at hit; subst hit; dsimp [rootNode]; rw [rootSoloNode_d]; omega)
      (fun _ hm => by cases hm)
  let br := branches u
  let L := x.spec.lookupVerts
  let w_re := getReattachWit x br.n br.leafFn
  have hv_le_max : v.val ≤ 4 * x.m + 64 ^ D := v.isLt.le.trans (P.vertices u)
  revert hv_le_max t_bits v
  change ∀ (v : Fin (L.card + br.n))
    (t_bits : Fin ((D4CoreCut.reattach x.G L br.n br.leafFn).deg v) → Bool),
    v.val ≤ 4 * x.m + 64 ^ D →
    RunsWithin B_src ob_src
      (encodePortQuery (Fin.addCases (fun v₀ => lookupDesc x.desc (w_re.old v₀).val.val f.natDegree x.l q) br.rightSrc v)
        v.val (List.ofFn t_bits))
      (residue f x.l q hf
        (Fin.addCases (motive := fun z => (Fin ((D4CoreCut.reattach x.G L br.n br.leafFn).deg z) → Bool) → B f x.l q)
          (fun v₀ β => liftBase f x.l q (x.A (w_re.old v₀).val (fun i => β (w_re.lp v₀ i))))
          br.rightV v t_bits))
      _ _
  intro v t_bits hv_le_max
  cases v using Fin.addCases with
  | left v₀ =>
    rw [Fin.addCases_left, Fin.addCases_left]
    let j_orig : Fin x.G.nV := (w_re.old v₀).val
    let α_orig : Fin (x.G.deg j_orig) → Bool := fun i => t_bits (w_re.lp v₀ i)
    have hbits_eq : List.ofFn t_bits = List.ofFn α_orig := by
      have hlp_val := (DetDLP.m14_plan_obligations.1 x br.n br.leafFn).2 v₀
      have hdeg_eq : (D4CoreCut.reattach x.G L br.n br.leafFn).deg (v₀.castAdd br.n) = x.G.deg j_orig :=
        (Fintype.card_fin _).symm.trans ((Fintype.card_congr (w_re.lp v₀).symm).trans (Fintype.card_fin _))
      apply List.ext_getElem
      · simp [hdeg_eq]
      · intro idx h1 h2
        simp only [List.length_ofFn] at h1 h2
        simp only [List.getElem_ofFn, α_orig]
        congr 1; apply Fin.ext
        exact (hlp_val ⟨idx, h2⟩).symm
    rw [hbits_eq]
    have h2L_q : 2 ^ (f.natDegree / 4) ≤ q := by
      have hdiv4 : f.natDegree / 4 = D3Stopped.level x.S := by rw [hdeg_f]; omega
      rw [hdiv4]
      have h2_mul : 2 ^ D3Stopped.level x.S ≤ 2 * x.S := pow2_clog2_le hS_pos
      have hg_ge : 40 * x.S ≤ guard := by
        dsimp [guard]; unfold totalGuard localAllowance
        have h64 : 1 ≤ 64 ^ D := Nat.one_le_pow _ _ (by decide)
        have h2s : 1 ≤ 2 ^ D3Stopped.shift x.S D := Nat.one_le_pow _ _ (by decide)
        have hsh1 : 1 ≤ D3Stopped.shift x.S D + 1 := Nat.succ_pos _
        calc 40 * x.S ≤ 40 * (x.S + 1) * 1 * 1 * 1 := by omega
          _ ≤ 40 * (x.S + 1) * (D3Stopped.shift x.S D + 1) * 2 ^ D3Stopped.shift x.S D * 64 ^ D := by gcongr
      dsimp [q]; omega
    have hκ_le_u := kappa_le_lookupQuery_len x.desc j_orig.val f.natDegree x.l q (v₀.castAdd br.n).val
      (List.ofFn α_orig) h2L_q (by rw [hdeg_f]; omega)
    have ha_lt_q : ∀ t_i, x.A j_orig α_orig t_i < 2 ^ q := fun t_i =>
      (x.bounded j_orig α_orig t_i).trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_add_left x.p guard))
    obtain ⟨hx_len, hy_len, hrun_e⟩ := horig_entry N le_rfl j_orig α_orig
    let u_lk := encodePortQuery (lookupDesc x.desc j_orig.val f.natDegree x.l q) (v₀.castAdd br.n).val (List.ofFn α_orig)
    have hu_lk_len : u_lk.length ≤ c_src * N₁ ^ c_src := by
      have hv_n2 : (v₀.castAdd br.n).val ≤ 65544 * N₁ ^ 2 := by
        have h64 : 64 ^ D ≤ (256 * N₁) ^ 2 := by
          refine (pow64_clog32_le (n := 4 * x.m) (by have := x.hm; omega)).trans (Nat.pow_le_pow_left ?_ 2)
          have : x.m ≤ 2 * N₁ := hm_x.trans (Nat.mul_le_mul_left 2 (hS_sz.trans (Nat.le_succ N)))
          omega
        have hm_N2 : 4 * x.m ≤ 8 * N₁ ^ 2 := by
          have : x.m ≤ 2 * N₁ := hm_x.trans (Nat.mul_le_mul_left 2 (hS_sz.trans (Nat.le_succ N)))
          nlinarith only [this, hN1_pos]
        nlinarith only [hv_le_max, h64, hm_N2]
      have hα_len : (List.ofFn α_orig).length ≤ 3 * N₁ := by
        simp only [List.length_ofFn]
        exact (deg_le_nE x.G j_orig).trans (hne_x.trans (Nat.mul_le_mul_left 3 (hS_sz.trans (Nat.le_succ N))))
      have hdeg_f_N : f.natDegree ≤ 4 * N₁ := by
        rw [hdeg_f]; exact Nat.mul_le_mul_left 4 ((clog2_le_self x.S).trans (hS_sz.trans (Nat.le_succ N)))
      let cap_in := x.desc.length + j_orig.val + f.natDegree + x.l + q + 1
      have hld_l : (lookupDesc x.desc j_orig.val f.natDegree x.l q).length ≤ (2 * cap_in + 2) * 5 + 2 := by
        unfold lookupDesc
        simp only [List.length_cons]
        refine Nat.add_le_add_right (length_encodeList_le id _ cap_in ?_) 1
        intro u_w hu_w
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu_w
        rcases hu_w with rfl | rfl | rfl | rfl | rfl
        · simp only [id_eq]; dsimp [cap_in]; omega
        · exact (countWord_len_le_succ _).trans (by dsimp [cap_in]; omega)
        · exact (countWord_len_le_succ _).trans (by dsimp [cap_in]; omega)
        · exact (countWord_len_le_succ _).trans (by dsimp [cap_in]; omega)
        · exact (countWord_len_le_succ _).trans (by dsimp [cap_in]; omega)
      let cap_out := (2 * cap_in + 2) * 5 + 2 + (v₀.castAdd br.n).val + (List.ofFn α_orig).length + 1
      have hu1 : u_lk.length ≤ (2 * cap_out + 2) * 3 + 1 := by
        apply length_encodeList_le id _ cap_out
        intro u_w hu_w
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu_w
        rcases hu_w with rfl | rfl | rfl
        · simp only [id_eq]; dsimp [cap_out]; omega
        · exact (countWord_len_le_succ _).trans (by dsimp [cap_out]; omega)
        · simp only [id_eq]; dsimp [cap_out]; omega
      have hu64 : u_lk.length ≤ 64 * (x.desc.length + j_orig.val + f.natDegree + x.l + q + (v₀.castAdd br.n).val + (List.ofFn α_orig).length + 4) := by
        dsimp [cap_out, cap_in] at hu1
        simp only [Fin.val_castAdd] at hu1 ⊢
        omega
      have hj_Nc : j_orig.val ≤ N₁ ^ c := j_orig.isLt.le.trans x.nV
      have hdesc_N1 : x.desc.length ≤ N₁ := hdesc_sz.trans (Nat.le_succ N)
      have hl_N1 : x.l ≤ 2 * C * N₁ := hl_x.trans (Nat.mul_le_mul_left _ (hS_sz.trans (Nat.le_succ N)))
      have hc1_src : c_s1 * N₁ ^ c_s1 ≤ c_src * N₁ ^ c_src :=
        Nat.mul_le_mul (le_max_left _ _) (Nat.pow_le_pow_right hN1_pos (le_max_left _ _))
      exact (hlen_lk N₁ hN1_pos x.desc.length j_orig.val f.natDegree x.l q (v₀.castAdd br.n).val (List.ofFn α_orig).length
        0 0 u_lk.length hdesc_N1 hj_Nc hdeg_f_N hl_N1 hq_bound hv_n2 hα_len hu64 (Nat.zero_le _) (Nat.zero_le _)).1.trans hc1_src
    exact hB_spec.1 x.S f.natDegree x.l q x.desc (P.R u) x.G (v₀.castAdd br.n) j_orig α_orig x.A f hf
      rfl hκ_le_u ha_lt_q hu_lk_len hx_len hy_len hrun_e
  | right j =>
    rw [Fin.addCases_right, Fin.addCases_right]
    let rightGoal (b : PlanBranchData x f PktOK q) : Prop :=
      ∀ (j' : Fin b.n)
        (t' : Fin ((D4CoreCut.reattach x.G L b.n b.leafFn).deg (Fin.natAdd L.card j')) → Bool),
        (Fin.natAdd L.card j').val ≤ 4 * x.m + 64 ^ D →
        RunsWithin B_src ob_src
          (encodePortQuery (b.rightSrc j') (Fin.natAdd L.card j').val (List.ofFn t'))
          (residue f x.l q hf (b.rightV j' t'))
          (polyBound K_B N * (2 : ℝ) ^ ((K_B : ℝ) * x.S / Real.sqrt (D3Stopped.level x.S : ℝ)))
          (polyBound K_B N)
    suffices hrg : rightGoal br from hrg j t_bits hv_le_max
    dsimp only [br, branches]
    have hbranch := DetDLP.m14_plan_obligations.2.2.2.2.1 x hf E_pkt o_pkt K_loc guard
      B_bud certTree hvalid hbLen hdeg_all u
    cases hread : certTree.read B_bud u.val with
    | none =>
      rw [hbranch.1 hread]
      intro j' t' hv'
      dsimp only
      let H_m := D4CoreCut.reattach x.G L (4 * x.m) (missLeafFn x hbLen)
      let deg_m := H_m.deg (Fin.natAdd L.card j')
      rw [← (DetDLP.m14_plan_obligations.2.1 x f deg_m).2]
      have hdeg_m : deg_m ≤ 2 * N₁ := by
        have h1 : deg_m ≤ H_m.nE := deg_le_nE H_m (Fin.natAdd L.card j')
        have h2 : H_m.nE = 4 * x.m * x.k := (DetDLP.d4_reattach_poly_and_spec.2 x (4 * x.m) (missLeafFn x hbLen)).2.1
        rw [h2] at h1
        exact h1.trans (hmk.trans (Nat.mul_le_mul_left 2 (hS_sz.trans (Nat.le_succ N))))
      have htbl_m : (emptyStoppedSpec x f deg_m).tableBits.length ≤ K_wi * N₁ ^ K_wi := by
        rw [(DetDLP.m14_plan_obligations.2.1 x f deg_m).1]
        have h1 : (pack []).length = 1 := rfl
        rw [h1]
        exact Nat.mul_pos hK_wi1 (Nat.pow_pos hN1_pos)
      exact hstopped_case x.p 0 deg_m (Fin.natAdd L.card j').val emptyGraphConst
        (emptyStoppedSpec x f deg_m) t' hv' (Nat.zero_le D) hdeg_m htbl_m
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) le_rfl (by simp)
        (fun w_p => Fin.elim0 w_p)
    | some lf =>
      rw [hbranch.2 lf hread]
      intro j' t' hv'
      dsimp only
      have hlf : lf.Valid := treeAll_read hvalid B_bud u.val hread
      let nd := lf.doneNodes.get j'
      have hnd_d : nd.d ≤ D := treeAll_read hd_tree B_bud u.val hread nd (List.get_mem _ j')
      have hdeg_eq := hdeg_all lf.doneNodes hlf.2.2.2 j'
      let α_nd : Fin nd.pins.length → Bool := fun kp => t' (kp.cast hdeg_eq.symm)
      have hofFn_eq : List.ofFn t' = List.ofFn α_nd := by
        apply List.ext_getElem
        · simp only [List.length_ofFn]; exact hdeg_eq
        · intro idx h1 h2
          simp only [List.getElem_ofFn, α_nd]
          rfl
      rw [hofFn_eq]
      have hpins_2N1 : nd.pins.length ≤ 2 * N₁ := by
        let H_h := D4CoreCut.reattach x.G L lf.doneNodes.length (hitLeafFn x hbLen lf.doneNodes hlf.2.2.2)
        have h1 : nd.pins.length = H_h.deg (Fin.natAdd L.card j') := hdeg_eq.symm
        have h2 : H_h.deg (Fin.natAdd L.card j') ≤ H_h.nE := deg_le_nE H_h _
        have h3 : H_h.nE = 4 * x.m * x.k := (DetDLP.d4_reattach_poly_and_spec.2 x _ _).2.1
        exact h1.le.trans ((h2.trans_eq h3).trans (hmk.trans (Nat.mul_le_mul_left 2 (hS_sz.trans (Nat.le_succ N)))))
      have hnV_25 : nd.G.nV ≤ 25 * N₁ ^ (c + 2) := by
        have hcl : D ≤ 8 * N₁ := by
          have h1 : D ≤ Nat.clog 2 (4 * x.m) := by dsimp [D]; rw [Nat.clog_pow_left 2 5]; omega
          exact h1.trans ((clog2_le_self _).trans (by have := hm_x; have := hS_sz; dsimp [N₁, N]; omega))
        have hxV : x.G.nV ≤ N₁ ^ (c + 2) := x.nV.trans (Nat.pow_le_pow_right hN1_pos (by omega))
        have hdS : nd.d * (3 * x.S) ≤ 24 * N₁ ^ 2 := by
          calc nd.d * (3 * x.S) ≤ (8 * N₁) * (3 * N₁) :=
                Nat.mul_le_mul (hnd_d.trans hcl) (Nat.mul_le_mul_left 3 (hS_sz.trans (Nat.le_succ N)))
            _ = 24 * N₁ ^ 2 := by ring
        have hN2 : N₁ ^ 2 ≤ N₁ ^ (c + 2) := Nat.pow_le_pow_right hN1_pos (by omega)
        have h1 := nd.verts_le
        omega
      exact hstopped_case nd.pCurr nd.d nd.pins.length (Fin.natAdd L.card j').val nd.G
        nd.toStoppedSpec α_nd hv' hnd_d hpins_2N1 (hNode_len x hf E_pkt o_pkt nd hnd_d).1
        nd.edges_le (cap_bound_of_active_pre hC x nd hL_act) hnV_25 nd.hp_ge nd.hp_le
        (fun w_p pkt_p hp β_p =>
          let hrun_f := hF_pkt x hf nd w_p pkt_p hp β_p
          ⟨(nd.toStoppedSpec.packet w_p pkt_p hp).le_precision, hrun_f.1, hrun_f.2⟩)

end DetDLP.M14SourcesInternal

-- Preserve the hypothesis names of the published statement.
set_option linter.unusedVariables false in
theorem solution :
    ∀ {C c : ℕ} (hC : 0 < C) (hc : 0 < c)
        (E : PrimitiveMachine) (o : Fin E.tapeCount)
        (M_node E_pkt : PrimitiveMachine) (o_node : Fin M_node.tapeCount) (o_pkt : Fin E_pkt.tapeCount)
        (K_loc H_loc c_loc : ℕ),
    ∃ L₀_src_opt : ℕ, AppendixD4.Closed →
      ∃ (B_src : PrimitiveMachine) (ob_src : Fin B_src.tapeCount) (k_src : ℕ),
        ∀ (x : Input C c) (hL_level : 1 ≤ D3Stopped.level x.S)
            (hL_bud : (DetDLP.d4_unroll_tree_bit_budget C (8 * K_loc) hC).choose ≤ D3Stopped.level x.S)
        (hL_grd : (DetDLP.d4_unroll_guard_and_residual_bounds C hC).choose ≤ D3Stopped.level x.S)
            (hL_act : max 6 (DetDLP.d4_active_node_preconditions C hC).choose ≤ D3Stopped.level x.S)
            (hL_src : max (C + 6) L₀_src_opt ≤ D3Stopped.level x.S) (he : entry x E o)
            (hf : (soloPoly x.S).Monic)
        (hdeg_f : (soloPoly x.S).natDegree = 4 * Nat.clog 2 x.S)
        (hpos : 0 < (soloPoly x.S).natDegree),
        let f := soloPoly x.S
        let D := Nat.clog 32 (4 * x.m)
        let guard := totalGuard x.S D
        let B_bud := D4UnrollBudget.budget x.S D (8 * K_loc)
        let rootNode := rootSoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)
        ∀ (rootUnroll : SoloUnroll x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc D rootNode),
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
        Sources B_src ob_src k_src P :=
  @DetDLP.M14SourcesInternal.solo_sources_complete
