-- Prove2me | solution 1 for DetDLP.m14_pkt
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-25T07:23:11.073888+00:00
-- url     : https://prove2.me/submissions/a25a2561-83b6-4b40-a234-05f15c75bfa3

import Definitions.Def_DetDLP_D4SoloPlanDefs
import Definitions.Def_DetDLP_W1_Pipeline
import Theorems.Thm_DetDLP_m14_base_fuel
import Theorems.Thm_DetDLP_m14_bounds

set_option autoImplicit false
set_option maxHeartbeats 800000

open Polynomial Finset DetDLP DetDLP.AppendixD4 DetDLP.ResidualScalarOracle
open DetDLP.D4Plan DetDLP.D4StoppedNode DetDLP.D4RankWalker DetDLP.D4GuardTree
open DetDLP.D4SoloRaw DetDLP.D4SoloNode DetDLP.D4SoloRoot DetDLP.D4SoloStep
open DetDLP.D4SoloTree DetDLP.D4SoloForest DetDLP.D4SoloPlanDefs DetDLP.w5_SplitArithmetic
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

namespace DetDLP.M14PktInternal

noncomputable section

private theorem pb_nonneg (K n : ℕ) : 0 ≤ polyBound K n := by
  unfold polyBound; positivity

private theorem encodeNatListBin_isEmpty_false (ns : List ℕ) :
    (encodeNatListBin ns).isEmpty = false := by
  cases ns with
  | nil => rfl
  | cons _ _ => rfl

private theorem frame_mem_two_mul_le {w : List Bool} {xs : List (List Bool)} (hw : w ∈ xs) :
    2 * w.length + 2 ≤ (Encoding.encodeList id xs).length := by
  induction xs with
  | nil => cases hw
  | cons x xs ih =>
    simp only [Encoding.encodeList, id_eq, List.length_cons, List.length_append, length_frame]
    rcases List.mem_cons.mp hw with rfl | hmem
    · omega
    · have := ih hmem; omega

theorem kappa_le_lookupQuery_len (origDesc : Bits) (j κ l q v : ℕ) (α : List Bool)
    (hq : 2 ^ (κ / 4) ≤ q) (hκ4 : κ = 4 * (κ / 4)) :
    κ ≤ (encodePortQuery (lookupDesc origDesc j κ l q) v α).length := by
  let L := κ / 4
  have hq_pos : 0 < q := lt_of_lt_of_le (Nat.two_pow_pos L) hq
  have hcw_q : L + 1 ≤ (countWord q).length := by
    rw [countWord_length_eq_bitLen q hq_pos]
    change L + 1 ≤ Nat.clog 2 (q + 1)
    by_contra! hlt
    have hpow := (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mp (Nat.le_of_lt_succ hlt)
    dsimp [L] at hpow
    omega
  have hld_len : 2 * L + 5 ≤ (lookupDesc origDesc j κ l q).length := by
    unfold lookupDesc
    simp only [List.length_cons]
    have hm : countWord q ∈ [origDesc, countWord j, countWord κ, countWord l, countWord q] := by simp
    have hf := frame_mem_two_mul_le hm
    omega
  unfold encodePortQuery
  have hm2 : lookupDesc origDesc j κ l q ∈ [lookupDesc origDesc j κ l q, countWord v, α] := by simp
  have hf2 := frame_mem_two_mul_le hm2
  omega

/-- Uniform packet adapter machine `F_pkt` prepending `permutePktQuery` to `(E_pkt, o_pkt)`. -/
theorem solo_packet_adapter_machine (E_pkt : PrimitiveMachine) (o_pkt : Fin E_pkt.tapeCount)
    (K_loc : ℕ) :
    ∃ (F_pkt : PrimitiveMachine) (oF_pkt : Fin F_pkt.tapeCount) (K_pkt : ℕ),
      1 ≤ K_pkt ∧
      ∀ {C c : ℕ} (x : Input C c) {f : ℤ[X]} (hf : f.Monic)
        (nd : SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf))
        (w : Fin nd.G.nV) (pkt : Bits) (h : nd.toStoppedSpec.vTable w = .pkt pkt)
        (β : Fin (nd.G.deg w) → Bool),
        let p := nd.toStoppedSpec.packet w pkt h
        let n_pkt := nd.G.nE + p.creation + 4 * D3Stopped.level x.S + x.l + 2
        let inp := Encoding.encodeList id [pkt, List.ofFn β]
        let ans := residue f x.l p.creation hf (p.entry β)
        inp.length ≤ K_pkt * (n_pkt + 1) ^ K_pkt ∧
        RunsWithin F_pkt oF_pkt inp ans
          (Real.exp ((K_pkt : ℝ) * (2 ^ D3Stopped.shift x.S (nd.d - 1) : ℕ) * Real.log n_pkt))
          (polyBound K_pkt n_pkt) := by
  obtain ⟨countWord_len_le_succ, _, encodeNatListBin_len_le, pack_len_le, _, _,
    polyBound_eq_natCast, _, _, _, _, _, _, pkt_origDeg_le, _⟩ := DetDLP.m14_bounds
  obtain ⟨M_perm, o_perm, k_perm, hM_perm⟩ :=
    PolyTBridge.polyT_listBool_runsWithin permutePktQuery permutePktQuery_poly
  let F_pkt := DetDLP_W1_Pipeline.WordPipeline.machine M_perm o_perm E_pkt
  let oF_pkt := DetDLP_W1_Pipeline.WordPipeline.resultPort M_perm o_perm E_pkt o_pkt
  obtain ⟨K_in, hKin_def⟩ : ∃ K, K = 128 * (K_loc + 2) := ⟨_, rfl⟩
  obtain ⟨K_a, hKa_def⟩ : ∃ K, K = k_perm * (K_in + 1) ^ k_perm + k_perm * K_in := ⟨_, rfl⟩
  obtain ⟨K_perm_sp, hKsp_def⟩ : ∃ K, K = K_a + E_pkt.tapeCount + M_perm.tapeCount + K_loc + 4 := ⟨_, rfl⟩
  obtain ⟨K_pkt, hKpkt_def⟩ : ∃ K, K = 4 * K_perm_sp + K_loc + K_in + 4 := ⟨_, rfl⟩
  have hKpkt_pos : 1 ≤ K_pkt := by rw [hKpkt_def]; omega
  have hKin_ge : K_loc + 1 ≤ K_in := by rw [hKin_def]; omega
  have hKa_exp : k_perm * (K_loc + 1) ≤ K_a :=
    (Nat.mul_le_mul_left k_perm hKin_ge).trans (by rw [hKa_def]; exact Nat.le_add_left _ _)
  have hKa_coef : k_perm * (K_in + 1) ^ k_perm ≤ K_a := by
    rw [hKa_def]; exact Nat.le_add_right _ _
  have hKa_sp : K_a ≤ K_perm_sp := by rw [hKsp_def]; omega
  have hKloc_sp : K_loc ≤ K_perm_sp := by rw [hKsp_def]; omega
  have hKsum_sp : K_a + E_pkt.tapeCount + K_loc + M_perm.tapeCount ≤ K_perm_sp := by
    rw [hKsp_def]; omega
  have hKsp_pkt : K_perm_sp ≤ K_pkt := by rw [hKpkt_def]; omega
  have hKin_pkt : K_in ≤ K_pkt := by rw [hKpkt_def]; omega
  have hKloc1_pkt : K_loc + 1 ≤ K_pkt := by rw [hKpkt_def]; omega
  have hKtop_pkt : 3 * K_perm_sp + K_loc + 1 ≤ K_pkt := by rw [hKpkt_def]; omega
  refine ⟨F_pkt, oF_pkt, K_pkt, hKpkt_pos, ?_⟩
  intro C c x f hf nd w pkt h β p n_pkt inp ans
  have hgen : ∀ (pinPos : ℕ) (sv : SoloVert x nd.G f (pktOKOf E_pkt o_pkt K_loc x f hf) nd.pCurr nd.d w)
      (hv : sv.toVertexSpec pinPos = .pkt pkt),
      let p' := sv.toPacket pinPos pkt hv
      let n_pkt' := nd.G.nE + p'.creation + 4 * D3Stopped.level x.S + x.l + 2
      let ans' := residue f x.l p'.creation hf (p'.entry β)
      inp.length ≤ K_pkt * (n_pkt' + 1) ^ K_pkt ∧
      RunsWithin F_pkt oF_pkt inp ans'
        (Real.exp ((K_pkt : ℝ) * (2 ^ D3Stopped.shift x.S (nd.d - 1) : ℕ) * Real.log n_pkt'))
        (polyBound K_pkt n_pkt') := by
    intro pinPos sv hv
    cases sv with
    | orig _ _ _ _ _ _ => cases hv
    | pkt dCreate pCreate origDeg rawDesc hdLt hpLe entry₀ hpkt permOpt hperm =>
      intro p' n_pkt' ans'
      have hn0_le : pCreate + 4 * D3Stopped.level x.S + x.l + 2 ≤ n_pkt' := by
        have hp_cr : p'.creation = pCreate := by cases permOpt <;> rfl
        dsimp only [n_pkt']; rw [hp_cr]; omega
      have hnpkt_ge3 : 3 ≤ n_pkt' := by
        have hp_cr : p'.creation = pCreate := by cases permOpt <;> rfl
        have h1 := hpkt.1; have h2 := x.hl
        dsimp only [n_pkt']; rw [hp_cr]; omega
      obtain ⟨n₀, hn0_def⟩ : ∃ m, m = pCreate + 4 * D3Stopped.level x.S + x.l + 2 := ⟨_, rfl⟩
      have hn0_pos_nat : 1 ≤ n₀ := by rw [hn0_def]; have := x.hl; omega
      have hn0_npkt : n₀ ≤ n_pkt' := hn0_def ▸ hn0_le
      obtain ⟨PB₀, hPB₀_def⟩ : ∃ M, M = K_loc * (n_pkt' + 1) ^ K_loc := ⟨_, rfl⟩
      have hpb0 : polyBound K_loc n₀ ≤ ((PB₀ : ℕ) : ℝ) := by
        rw [hPB₀_def, ← polyBound_eq_natCast K_loc n_pkt']
        unfold polyBound
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) (add_le_add (Nat.cast_le.mpr hn0_npkt) le_rfl) K_loc)
          (Nat.cast_nonneg _)
      have hpb0_raw : polyBound K_loc (pCreate + 4 * D3Stopped.level x.S + x.l + 2) ≤ ((PB₀ : ℕ) : ℝ) :=
        hn0_def ▸ hpb0
      have hraw_le : rawDesc.length ≤ PB₀ :=
        (Nat.cast_le (α := ℝ)).mp (hpkt.2.2.2.1.trans hpb0_raw)
      have horig_le : origDeg ≤ PB₀ :=
        (Nat.cast_le (α := ℝ)).mp ((pkt_origDeg_le hpkt).trans hpb0_raw)
      have hdeg_w : nd.G.deg w ≤ n_pkt' := by
        have hdeg : nd.G.deg w ≤ nd.G.nE := by
          unfold BipartiteMultigraph.deg BipartiteMultigraph.ports
          exact (List.length_filter_le _ _).trans (by simp)
        dsimp [n_pkt']
        omega
      have hpkt_case : pkt.length ≤ 32 * (n_pkt' + 1) * (PB₀ + 1) ∧
          ∃ α₀ : Fin origDeg → Bool,
            permutePktQuery inp = Encoding.encodeList id [rawDesc, List.ofFn α₀] ∧
            ans' = residue f x.l pCreate hf (entry₀ α₀) := by
        cases permOpt with
        | none =>
          simp only [SoloVert.toVertexSpec, VertexSpec.pkt.injEq] at hv
          subst hv
          refine ⟨?_, fun i => β (i.cast hperm), ?_, rfl⟩
          · have hp_l : (pack [rawDesc, []]).length ≤ (2 * PB₀ + 2) * 2 + 1 := by
              apply pack_len_le _ PB₀
              intro u hu
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
              rcases hu with rfl | rfl
              · exact hraw_le
              · simp
            have h1 : (2 * PB₀ + 2) * 2 + 1 ≤ 32 * 1 * (PB₀ + 1) := by omega
            exact (hp_l.trans h1).trans (Nat.mul_le_mul_right (PB₀ + 1) (Nat.mul_le_mul_left 32 (Nat.succ_pos n_pkt')))
          · unfold permutePktQuery
            simp only [inp, fld_encodeList_id, fld_pack, List.getD_cons_zero, List.getD_cons_succ,
              List.isEmpty_nil, ↓reduceIte]
            congr 2; congr 1
            apply List.ext_getElem
            · simp [hperm]
            · intro idx h1 h2; simp
        | some pm =>
          simp only [SoloVert.toVertexSpec, VertexSpec.pkt.injEq] at hv
          subst hv
          refine ⟨?_, fun i => β ⟨pm.getD i.val 0, hperm.2 i⟩, ?_, rfl⟩
          · have hpm_l : (encodeNatListBin pm).length ≤ (2 * (n_pkt' + 1) + 2) * PB₀ + 1 := by
              refine (encodeNatListBin_len_le pm (n_pkt' + 1) ?_).trans ?_
              · intro m hm
                obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.mp hm
                have hi : idx < origDeg := hperm.1 ▸ hidx
                have hlt : pm[idx]'hidx < nd.G.deg w := by
                  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx] using hperm.2 ⟨idx, hi⟩
                exact (countWord_len_le_succ _).trans (by omega)
              · exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (hperm.1.le.trans horig_le)) 1
            let cap_m := (2 * (n_pkt' + 1) + 2) * PB₀ + PB₀ + 1
            have hp_l : (pack [rawDesc, encodeNatListBin pm]).length ≤ (2 * cap_m + 2) * 2 + 1 := by
              apply pack_len_le _ cap_m
              intro u hu
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
              rcases hu with rfl | rfl <;> (dsimp [cap_m]; omega)
            have hcm : (2 * cap_m + 2) * 2 + 1 ≤ 32 * (n_pkt' + 1) * (PB₀ + 1) := by
              dsimp [cap_m]
              nlinarith only [Nat.zero_le n_pkt', Nat.zero_le PB₀]
            exact hp_l.trans hcm
          · unfold permutePktQuery
            simp only [inp, fld_encodeList_id, fld_pack, List.getD_cons_zero, List.getD_cons_succ,
              encodeNatListBin_isEmpty_false, Bool.false_eq_true, ↓reduceIte, ints_encodeNatListBin]
            congr 2; congr 1
            apply List.ext_getElem
            · simp [hperm.1]
            · intro idx h1 h2
              simp only [List.length_map] at h1
              have hi : idx < origDeg := hperm.1 ▸ h1
              have hlt : pm[idx]'h1 < nd.G.deg w := by
                simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1] using hperm.2 ⟨idx, hi⟩
              simp only [List.getElem_map, List.getElem_ofFn]
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [hlt]),
                  List.getElem_ofFn, Option.getD_some]
              congr 1; apply Fin.ext
              simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]
      obtain ⟨hpkt_len, α₀, hperm_eq, hans_eq⟩ := hpkt_case
      have hinp_len : inp.length ≤ K_in * (n_pkt' + 1) ^ (K_loc + 1) := by
        let cap_i := 32 * (n_pkt' + 1) * (PB₀ + 1) + n_pkt'
        have hi1 : inp.length ≤ (2 * cap_i + 2) * 2 + 1 := by
          apply length_encodeList_le id _ cap_i
          intro u hu
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
          rcases hu with rfl | rfl
          · dsimp [cap_i]; omega
          · simp only [id_eq, List.length_ofFn]; dsimp [cap_i]; omega
        obtain ⟨P_pow, hPpow_def⟩ : ∃ P, P = (n_pkt' + 1) ^ K_loc := ⟨_, rfl⟩
        have h1_pow : 1 ≤ P_pow := hPpow_def ▸ Nat.one_le_pow _ _ (Nat.succ_pos _)
        have hPB_bound : PB₀ + 1 ≤ (K_loc + 1) * P_pow := by
          have hpb_eq : PB₀ = K_loc * P_pow := by rw [hPB₀_def, hPpow_def]
          nlinarith only [hpb_eq, h1_pow]
        have hi2 : (2 * cap_i + 2) * 2 + 1 ≤ 128 * (K_loc + 2) * (n_pkt' + 1) * P_pow := by
          dsimp [cap_i]
          have hmul := Nat.mul_le_mul_left (32 * (n_pkt' + 1)) hPB_bound
          nlinarith only [hmul, h1_pow, Nat.zero_le n_pkt', Nat.zero_le K_loc]
        calc inp.length ≤ (2 * cap_i + 2) * 2 + 1 := hi1
          _ ≤ 128 * (K_loc + 2) * (n_pkt' + 1) * P_pow := hi2
          _ = K_in * (n_pkt' + 1) ^ (K_loc + 1) := by
            rw [hKin_def, hPpow_def, pow_succ']; ring
      have hinp_Kpkt : inp.length ≤ K_pkt * (n_pkt' + 1) ^ K_pkt :=
        hinp_len.trans (Nat.mul_le_mul hKin_pkt (Nat.pow_le_pow_right (Nat.succ_pos _) hKloc1_pkt))
      refine ⟨hinp_Kpkt, ?_⟩
      have hrun_perm := hM_perm inp
      rw [hperm_eq] at hrun_perm
      have hrun_epkt := hpkt.2.2.2.2 α₀
      rw [← hans_eq, ← hn0_def] at hrun_epkt
      have hpipe := DetDLP_W1_Pipeline.WordPipeline.run M_perm o_perm E_pkt o_pkt hrun_perm hrun_epkt
      obtain ⟨np, hnp_def⟩ : ∃ m, m = n_pkt' := ⟨_, rfl⟩
      rw [← hnp_def] at hn0_npkt hnpkt_ge3 ⊢
      have hnp1_ge1 : (1 : ℝ) ≤ (np : ℝ) + 1 := by exact_mod_cast Nat.succ_pos np
      have hperm_pb : polyBound k_perm inp.length ≤ polyBound K_a np := by
        unfold polyBound
        have hinp_r : (inp.length : ℝ) + 1 ≤ ((K_in + 1 : ℕ) : ℝ) * ((np : ℝ) + 1) ^ (K_loc + 1) := by
          have hnat : inp.length + 1 ≤ (K_in + 1) * (np + 1) ^ (K_loc + 1) := by
            have hp1 : 1 ≤ (np + 1) ^ (K_loc + 1) := Nat.one_le_pow _ _ (Nat.succ_pos _)
            have hinp_np : inp.length ≤ K_in * (np + 1) ^ (K_loc + 1) := hnp_def ▸ hinp_len
            nlinarith only [hinp_np, hp1]
          have hr := (Nat.cast_le (α := ℝ)).mpr hnat
          push_cast at hr ⊢
          exact hr
        have hpow_le : ((inp.length : ℝ) + 1) ^ k_perm ≤
            (((K_in + 1) ^ k_perm : ℕ) : ℝ) * ((np : ℝ) + 1) ^ (k_perm * (K_loc + 1)) := by
          calc ((inp.length : ℝ) + 1) ^ k_perm
              ≤ (((K_in + 1 : ℕ) : ℝ) * ((np : ℝ) + 1) ^ (K_loc + 1)) ^ k_perm :=
                pow_le_pow_left₀ (by positivity) hinp_r k_perm
            _ = (((K_in + 1) ^ k_perm : ℕ) : ℝ) * ((np : ℝ) + 1) ^ (k_perm * (K_loc + 1)) := by
                rw [mul_pow, ← pow_mul, mul_comm (K_loc + 1) k_perm]; push_cast; rfl
        calc (k_perm : ℝ) * ((inp.length : ℝ) + 1) ^ k_perm
            ≤ (k_perm : ℝ) * ((((K_in + 1) ^ k_perm : ℕ) : ℝ) * ((np : ℝ) + 1) ^ (k_perm * (K_loc + 1))) :=
              mul_le_mul_of_nonneg_left hpow_le (Nat.cast_nonneg _)
          _ = ((k_perm * (K_in + 1) ^ k_perm : ℕ) : ℝ) * ((np : ℝ) + 1) ^ (k_perm * (K_loc + 1)) := by
              push_cast; ring
          _ ≤ (K_a : ℝ) * ((np : ℝ) + 1) ^ K_a := by
              apply mul_le_mul
              · exact_mod_cast hKa_coef
              · exact pow_le_pow_right₀ hnp1_ge1 hKa_exp
              · positivity
              · positivity
      have hsp_le : polyBound k_perm inp.length + (E_pkt.tapeCount : ℝ) +
          (polyBound K_loc n₀ + (M_perm.tapeCount : ℝ)) ≤ polyBound K_perm_sp np := by
        have h1 : polyBound K_a np ≤ (K_a : ℝ) * ((np : ℝ) + 1) ^ K_perm_sp := by
          unfold polyBound
          exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hnp1_ge1 hKa_sp) (Nat.cast_nonneg _)
        have h2 : polyBound K_loc n₀ ≤ (K_loc : ℝ) * ((np : ℝ) + 1) ^ K_perm_sp := by
          unfold polyBound
          exact mul_le_mul_of_nonneg_left
            ((pow_le_pow_left₀ (by positivity) (add_le_add (Nat.cast_le.mpr hn0_npkt) le_rfl) K_loc).trans
              (pow_le_pow_right₀ hnp1_ge1 hKloc_sp))
            (Nat.cast_nonneg _)
        have hpow1 : (1 : ℝ) ≤ ((np : ℝ) + 1) ^ K_perm_sp := one_le_pow₀ hnp1_ge1
        have hsum_K : (K_a : ℝ) + (E_pkt.tapeCount : ℝ) + (K_loc : ℝ) + (M_perm.tapeCount : ℝ) ≤ (K_perm_sp : ℝ) := by
          have hr := (Nat.cast_le (α := ℝ)).mpr hKsum_sp
          push_cast at hr
          exact hr
        change polyBound k_perm inp.length + (E_pkt.tapeCount : ℝ) +
          (polyBound K_loc n₀ + (M_perm.tapeCount : ℝ)) ≤ (K_perm_sp : ℝ) * ((np : ℝ) + 1) ^ K_perm_sp
        have hmul_K : ((K_a : ℝ) + (E_pkt.tapeCount : ℝ) + (K_loc : ℝ) + (M_perm.tapeCount : ℝ)) *
            ((np : ℝ) + 1) ^ K_perm_sp ≤ (K_perm_sp : ℝ) * ((np : ℝ) + 1) ^ K_perm_sp :=
          mul_le_mul_of_nonneg_right hsum_K (by positivity)
        have he1 : (E_pkt.tapeCount : ℝ) ≤ (E_pkt.tapeCount : ℝ) * ((np : ℝ) + 1) ^ K_perm_sp :=
          le_mul_of_one_le_right (Nat.cast_nonneg _) hpow1
        have hm1 : (M_perm.tapeCount : ℝ) ≤ (M_perm.tapeCount : ℝ) * ((np : ℝ) + 1) ^ K_perm_sp :=
          le_mul_of_one_le_right (Nat.cast_nonneg _) hpow1
        linarith [hperm_pb, h1, h2, hmul_K, he1, hm1]
      have hsp_final : polyBound K_perm_sp np ≤ polyBound K_pkt np := by
        unfold polyBound
        exact mul_le_mul (Nat.cast_le.mpr hKsp_pkt) (pow_le_pow_right₀ hnp1_ge1 hKsp_pkt) (by positivity) (by positivity)
      have htm_final : polyBound k_perm inp.length +
          Real.exp ((K_loc : ℝ) * (2 ^ D3Stopped.shift x.S dCreate : ℕ) * Real.log n₀) ≤
          Real.exp ((K_pkt : ℝ) * (2 ^ D3Stopped.shift x.S (nd.d - 1) : ℕ) * Real.log np) := by
        have hn_pos : (0 : ℝ) < (np : ℝ) := by exact_mod_cast (by omega : 0 < np)
        have hn0_pos : (0 : ℝ) < (n₀ : ℝ) := by exact_mod_cast (by omega : 0 < n₀)
        have hlog_ge : Real.log 3 ≤ Real.log (np : ℝ) :=
          Real.log_le_log (by positivity) (by exact_mod_cast hnpkt_ge3)
        have hlog_pos : 0 < Real.log (np : ℝ) :=
          lt_of_lt_of_le (Real.log_pos (by norm_num)) hlog_ge
        have hpb_exp : polyBound K_perm_sp np ≤ Real.exp ((3 * K_perm_sp : ℝ) * Real.log (np : ℝ)) := by
          have hnp1 : (np : ℝ) + 1 ≤ (np : ℝ) ^ 2 := by
            have : np + 1 ≤ np ^ 2 := by nlinarith only [hnpkt_ge3]
            exact_mod_cast this
          have hK_pow : (K_perm_sp : ℝ) ≤ (np : ℝ) ^ K_perm_sp := by
            have h2K : K_perm_sp ≤ 2 ^ K_perm_sp :=
              (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mp
                (DetDLP.m14_base_fuel.2.2.2.2.2.1 K_perm_sp)
            have h2n : 2 ^ K_perm_sp ≤ np ^ K_perm_sp := Nat.pow_le_pow_left (by omega) _
            exact_mod_cast h2K.trans h2n
          calc polyBound K_perm_sp np
              = (K_perm_sp : ℝ) * ((np : ℝ) + 1) ^ K_perm_sp := rfl
            _ ≤ (np : ℝ) ^ K_perm_sp * ((np : ℝ) ^ 2) ^ K_perm_sp :=
                mul_le_mul hK_pow (pow_le_pow_left₀ (by positivity) hnp1 K_perm_sp) (by positivity) (by positivity)
            _ = (np : ℝ) ^ (3 * K_perm_sp) := by rw [← pow_mul, ← pow_add]; ring_nf
            _ = Real.exp ((3 * K_perm_sp : ℝ) * Real.log (np : ℝ)) := by
                rw [← Real.rpow_natCast, Real.rpow_def_of_pos hn_pos]
                push_cast
                rw [mul_comm]
        have hd_prev : dCreate ≤ nd.d - 1 := by omega
        obtain ⟨Sh_d, hShd_def⟩ : ∃ m, m = 2 ^ D3Stopped.shift x.S (nd.d - 1) := ⟨_, rfl⟩
        rw [← hShd_def]
        have h2_sh : (1 : ℝ) ≤ (Sh_d : ℝ) := by
          have : 1 ≤ Sh_d := hShd_def ▸ Nat.one_le_pow _ _ (by decide)
          exact_mod_cast this
        have h2_mono : ((2 ^ D3Stopped.shift x.S dCreate : ℕ) : ℝ) ≤ (Sh_d : ℝ) := by
          have : 2 ^ D3Stopped.shift x.S dCreate ≤ Sh_d :=
            hShd_def ▸ Nat.pow_le_pow_right (by decide) (shift_mono_solo x.S hd_prev)
          exact_mod_cast this
        have hlog_mono : Real.log (n₀ : ℝ) ≤ Real.log (np : ℝ) :=
          Real.log_le_log hn0_pos (Nat.cast_le.mpr hn0_npkt)
        have hexp_t1 : polyBound k_perm inp.length ≤
            Real.exp (((3 * K_perm_sp : ℕ) : ℝ) * (Sh_d : ℝ) * Real.log (np : ℝ)) := by
          have hp_le : polyBound k_perm inp.length ≤ polyBound K_perm_sp np := by
            nlinarith only [hsp_le, pb_nonneg K_loc n₀,
              Nat.cast_nonneg (α := ℝ) E_pkt.tapeCount, Nat.cast_nonneg (α := ℝ) M_perm.tapeCount]
          refine hp_le.trans (hpb_exp.trans (Real.exp_le_exp.mpr ?_))
          push_cast
          have h1 : (3 : ℝ) * K_perm_sp * 1 ≤ (3 : ℝ) * K_perm_sp * Sh_d :=
            mul_le_mul_of_nonneg_left h2_sh (by positivity)
          have h2 := mul_le_mul_of_nonneg_right h1 hlog_pos.le
          linarith only [h2]
        have hexp_t2 : Real.exp ((K_loc : ℝ) * (2 ^ D3Stopped.shift x.S dCreate : ℕ) * Real.log n₀) ≤
            Real.exp ((K_loc : ℝ) * (Sh_d : ℝ) * Real.log (np : ℝ)) := by
          apply Real.exp_le_exp.mpr
          have hlog0_nn : 0 ≤ Real.log (n₀ : ℝ) := Real.log_nonneg (by exact_mod_cast hn0_pos_nat)
          exact mul_le_mul (mul_le_mul_of_nonneg_left h2_mono (Nat.cast_nonneg _)) hlog_mono hlog0_nn (by positivity)
        have hlog3_gt1 : (1 : ℝ) ≤ Real.log (np : ℝ) := by
          have hexp1_lt3 : Real.exp 1 ≤ 3 := by
            have := Real.exp_one_lt_d9.le
            linarith
          exact ((Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 3)).mpr hexp1_lt3).trans hlog_ge
        let E_top := ((3 * K_perm_sp + K_loc : ℕ) : ℝ) * (Sh_d : ℝ) * Real.log (np : ℝ)
        have ht1' : polyBound k_perm inp.length ≤ Real.exp E_top := by
          refine hexp_t1.trans (Real.exp_le_exp.mpr ?_)
          dsimp [E_top]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.le_add_right _ _)) (by positivity))
            hlog_pos.le
        have ht2' : Real.exp ((K_loc : ℝ) * (2 ^ D3Stopped.shift x.S dCreate : ℕ) * Real.log n₀) ≤ Real.exp E_top := by
          refine hexp_t2.trans (Real.exp_le_exp.mpr ?_)
          dsimp [E_top]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.le_add_left _ _)) (by positivity))
            hlog_pos.le
        have h2_le_exp1 : (2 : ℝ) ≤ Real.exp 1 := by
          have := Real.add_one_le_exp (1 : ℝ)
          linarith
        have hmul_e1 : 2 * Real.exp E_top ≤ Real.exp (1 + E_top) := by
          rw [Real.exp_add]
          exact mul_le_mul_of_nonneg_right h2_le_exp1 (Real.exp_pos E_top).le
        have hfinal_exp : Real.exp (1 + E_top) ≤
            Real.exp ((K_pkt : ℝ) * (Sh_d : ℝ) * Real.log (np : ℝ)) := by
          apply Real.exp_le_exp.mpr
          dsimp [E_top]
          have h1_le : (1 : ℝ) ≤ 1 * (Sh_d : ℝ) * Real.log (np : ℝ) := by
            nlinarith only [h2_sh, hlog3_gt1]
          have hcoef_r : ((3 * K_perm_sp + K_loc : ℕ) : ℝ) + 1 ≤ (K_pkt : ℝ) := by
            exact_mod_cast hKtop_pkt
          calc 1 + ((3 * K_perm_sp + K_loc : ℕ) : ℝ) * (Sh_d : ℝ) * Real.log (np : ℝ)
              ≤ 1 * (Sh_d : ℝ) * Real.log (np : ℝ) +
                ((3 * K_perm_sp + K_loc : ℕ) : ℝ) * (Sh_d : ℝ) * Real.log (np : ℝ) := by
                linarith only [h1_le]
            _ = (((3 * K_perm_sp + K_loc : ℕ) : ℝ) + 1) * ((Sh_d : ℝ) * Real.log (np : ℝ)) := by ring
            _ ≤ (K_pkt : ℝ) * ((Sh_d : ℝ) * Real.log (np : ℝ)) :=
                mul_le_mul_of_nonneg_right hcoef_r (mul_nonneg (by positivity) hlog_pos.le)
            _ = (K_pkt : ℝ) * (Sh_d : ℝ) * Real.log (np : ℝ) := by ring
        have hsum_e : polyBound k_perm inp.length +
            Real.exp ((K_loc : ℝ) * (2 ^ D3Stopped.shift x.S dCreate : ℕ) * Real.log n₀) ≤
            2 * Real.exp E_top := by
          linarith only [ht1', ht2']
        exact hsum_e.trans (hmul_e1.trans hfinal_exp)
      exact DetDLP.PolyTBridge.runsWithin_mono_local hpipe htm_final (hsp_le.trans hsp_final)
  exact hgen (nd.pinPosOf w) (nd.verts w) h


private theorem source_lengths_from_bounds (C c K_grd K_wi K_pkt c_pkt : ℕ) :
    ∃ c_src : ℕ, c ≤ c_src ∧ 1 ≤ c_src ∧
      ∀ (N₁ : ℕ), 1 ≤ N₁ →
        -- (1) lookup branch bounds:
        ∀ (descLen jVal κ l q vVal αLen yLen xLen uLen : ℕ),
          descLen ≤ N₁ → jVal ≤ N₁ ^ c → κ ≤ 4 * N₁ → l ≤ 2 * C * N₁ →
          q ≤ (K_grd + 1) * N₁ ^ (K_grd + 1) → vVal ≤ 65544 * N₁ ^ 2 → αLen ≤ 3 * N₁ →
          uLen ≤ 64 * (descLen + jVal + κ + l + q + vVal + αLen + 4) →
          xLen ≤ 16 * (descLen + jVal + αLen + 4) →
          yLen ≤ (2 * N₁ + 4) * l + 1 →
          uLen ≤ c_src * N₁ ^ c_src ∧
          xLen ≤ c_src * N₁ ^ c_src ∧
          yLen ≤ c_src * N₁ ^ c_src := by
  let e_max := max (c + 2) (K_grd + 2)
  let c_src := 16777216 * (C + 2) * (K_grd + 2) + c + e_max + 8 + K_wi + K_pkt + c_pkt
  refine ⟨c_src, by dsimp [c_src]; omega, by dsimp [c_src]; omega, ?_⟩
  intro N₁ hN1 descLen jVal κ l q vVal αLen yLen xLen uLen
    hdesc hj hκ hl hq hv hα hu hx hy
  let M := N₁ ^ e_max
  have hM1 : 1 ≤ M := Nat.one_le_pow _ _ hN1
  have hN_M : N₁ ≤ M := by
    calc N₁ = N₁ ^ 1 := (pow_one N₁).symm
      _ ≤ N₁ ^ e_max := Nat.pow_le_pow_right hN1 (by dsimp [e_max]; omega)
  have hN2_M : N₁ ^ 2 ≤ M := Nat.pow_le_pow_right hN1 (by dsimp [e_max]; omega)
  have hj_M : jVal ≤ M := hj.trans (Nat.pow_le_pow_right hN1 (by dsimp [e_max]; omega))
  have hq_M : q ≤ (K_grd + 1) * M :=
    hq.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hN1 (by dsimp [e_max]; omega)))
  have hv_M : vVal ≤ 65544 * M := hv.trans (Nat.mul_le_mul_left _ hN2_M)
  have hl_M : l ≤ 2 * C * M := hl.trans (Nat.mul_le_mul_left _ hN_M)
  have hM_csrc : M ≤ N₁ ^ c_src :=
    Nat.pow_le_pow_right hN1 (by dsimp [c_src]; omega)
  have h1_csrc : 16777216 * (C + 2) * (K_grd + 2) ≤ c_src := by dsimp [c_src]; omega
  have hu_M : uLen ≤ 16777216 * (C + 2) * (K_grd + 2) * M := by
    nlinarith [hu, hdesc, hj_M, hκ, hl_M, hq_M, hv_M, hα, hN_M, hM1]
  have hx_M : xLen ≤ 16777216 * (C + 2) * (K_grd + 2) * M := by
    nlinarith [hx, hdesc, hj_M, hα, hN_M, hM1]
  have hy_M : yLen ≤ 16777216 * (C + 2) * (K_grd + 2) * M := by
    have hmul : (2 * N₁ + 4) * l + 1 ≤ (6 * N₁) * (2 * C * N₁) + 1 := by
      have : 2 * N₁ + 4 ≤ 6 * N₁ := by omega
      nlinarith [Nat.mul_le_mul this hl]
    have h12 : (6 * N₁) * (2 * C * N₁) = 12 * C * N₁ ^ 2 := by ring
    rw [h12] at hmul
    have h12_M : 12 * C * N₁ ^ 2 ≤ 12 * C * M := Nat.mul_le_mul_left _ hN2_M
    nlinarith [hy, hmul, h12_M, hM1]
  exact ⟨hu_M.trans (Nat.mul_le_mul h1_csrc hM_csrc),
    hx_M.trans (Nat.mul_le_mul h1_csrc hM_csrc),
    hy_M.trans (Nat.mul_le_mul h1_csrc hM_csrc)⟩

private theorem stopped_lengths_from_bounds (C c K_grd K_wi K_pkt c_pkt : ℕ) :
    ∃ c_s2 : ℕ, c ≤ c_s2 ∧ 1 ≤ c_s2 ∧
      ∀ (N₁ n₁ m₁ : ℕ), 2 ≤ N₁ → N₁ ≤ n₁ → n₁ ≤ m₁ →
        (25 * m₁ ^ (c + 2) ≤ m₁ ^ c_s2) ∧
        (K_pkt * ((2 * N₁) ^ c_pkt + 1) ^ K_pkt ≤ c_s2 * n₁ ^ c_s2) ∧
        ∀ (uLen xStopLen yStopLen qStopLen : ℕ),
          uLen ≤ 1048576 * (C + 2) * (K_wi + 2) * N₁ ^ (max (2 * c + 6) (K_wi + 4)) →
          xStopLen ≤ 1048576 * (C + 2) * (K_wi + 2) * N₁ ^ (max (2 * c + 6) (K_wi + 4)) →
          yStopLen ≤ 1048576 * (C + 2) * N₁ ^ 6 →
          qStopLen ≤ 1048576 * (C + 2) * (K_wi + 2) * n₁ ^ (max (c + 4) (K_wi + 4)) →
          uLen ≤ c_s2 * N₁ ^ c_s2 ∧
          xStopLen ≤ c_s2 * N₁ ^ c_s2 ∧
          yStopLen ≤ c_s2 * N₁ ^ c_s2 ∧
          qStopLen ≤ c_s2 * n₁ ^ c_s2 := by
  let e2 := max (max (2 * c + 8) (K_wi + 6)) (2 * c_pkt * K_pkt + K_pkt + K_grd + 8)
  let c_s2 := 2097152 * (C + 2) * (K_wi + 2) + K_pkt * 2 ^ K_pkt + e2 + 16
  have hc_pos : 1 ≤ c_s2 := Nat.le_trans (by decide : 1 ≤ 16) (Nat.le_add_left 16 _)
  refine ⟨c_s2, by dsimp [c_s2, e2]; omega, hc_pos, ?_⟩
  intro N₁ n₁ m₁ hN2 hNn hnm
  have hN1 : 1 ≤ N₁ := by omega
  have hn2 : 2 ≤ n₁ := hN2.trans hNn
  have hm2 : 2 ≤ m₁ := hn2.trans hnm
  refine ⟨?_, ?_, ?_⟩
  · have h25 : 25 ≤ m₁ ^ 5 := by
      calc 25 ≤ 32 := by decide
        _ = 2 ^ 5 := by ring
        _ ≤ m₁ ^ 5 := Nat.pow_le_pow_left hm2 5
    calc 25 * m₁ ^ (c + 2)
        ≤ m₁ ^ 5 * m₁ ^ (c + 2) := Nat.mul_le_mul_right _ h25
      _ = m₁ ^ (c + 7) := (pow_add m₁ 5 (c + 2)).symm.trans (by congr 1; omega)
      _ ≤ m₁ ^ c_s2 := Nat.pow_le_pow_right (by omega) (by dsimp [c_s2, e2]; omega)
  · have h2N_sq : 2 * N₁ ≤ N₁ ^ 2 := by nlinarith [hN2]
    have hp1 : (2 * N₁) ^ c_pkt + 1 ≤ 2 * N₁ ^ (2 * c_pkt) := by
      have hp_a : (2 * N₁) ^ c_pkt ≤ N₁ ^ (2 * c_pkt) := by
        calc (2 * N₁) ^ c_pkt ≤ (N₁ ^ 2) ^ c_pkt := Nat.pow_le_pow_left h2N_sq c_pkt
          _ = N₁ ^ (2 * c_pkt) := (pow_mul N₁ 2 c_pkt).symm
      have hp_1 : 1 ≤ N₁ ^ (2 * c_pkt) := Nat.one_le_pow _ _ hN1
      omega
    have hp2 : ((2 * N₁) ^ c_pkt + 1) ^ K_pkt ≤ 2 ^ K_pkt * n₁ ^ (2 * c_pkt * K_pkt) := by
      calc ((2 * N₁) ^ c_pkt + 1) ^ K_pkt
          ≤ (2 * N₁ ^ (2 * c_pkt)) ^ K_pkt := Nat.pow_le_pow_left hp1 K_pkt
        _ = 2 ^ K_pkt * N₁ ^ (2 * c_pkt * K_pkt) := by rw [mul_pow, ← pow_mul]
        _ ≤ 2 ^ K_pkt * n₁ ^ (2 * c_pkt * K_pkt) :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hNn _)
    have hK_c : K_pkt * 2 ^ K_pkt ≤ c_s2 :=
      (Nat.le_add_left _ _).trans ((Nat.le_add_right _ e2).trans (Nat.le_add_right _ 16))
    have he_c : 2 * c_pkt * K_pkt ≤ c_s2 := by dsimp [c_s2, e2]; omega
    calc K_pkt * ((2 * N₁) ^ c_pkt + 1) ^ K_pkt
        ≤ K_pkt * (2 ^ K_pkt * n₁ ^ (2 * c_pkt * K_pkt)) := Nat.mul_le_mul_left _ hp2
      _ = (K_pkt * 2 ^ K_pkt) * n₁ ^ (2 * c_pkt * K_pkt) := (Nat.mul_assoc _ _ _).symm
      _ ≤ c_s2 * n₁ ^ c_s2 := Nat.mul_le_mul hK_c (Nat.pow_le_pow_right (by omega) he_c)
  · intro uLen xStopLen yStopLen qStopLen hu hx hy hq
    have hC_c : 1048576 * (C + 2) * (K_wi + 2) ≤ c_s2 := by
      have h1 : 1048576 * (C + 2) * (K_wi + 2) ≤ 2097152 * (C + 2) * (K_wi + 2) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide))
      exact h1.trans ((Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)))
    have hC_c2 : 1048576 * (C + 2) ≤ c_s2 := by
      have : 1048576 * (C + 2) * 1 ≤ 1048576 * (C + 2) * (K_wi + 2) :=
        Nat.mul_le_mul_left _ (by omega)
      rw [mul_one] at this; exact this.trans hC_c
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact hu.trans (Nat.mul_le_mul hC_c (Nat.pow_le_pow_right hN1 (by dsimp [c_s2, e2]; omega)))
    · exact hx.trans (Nat.mul_le_mul hC_c (Nat.pow_le_pow_right hN1 (by dsimp [c_s2, e2]; omega)))
    · exact hy.trans (Nat.mul_le_mul hC_c2 (Nat.pow_le_pow_right hN1 (by dsimp [c_s2, e2]; omega)))
    · exact hq.trans (Nat.mul_le_mul hC_c (Nat.pow_le_pow_right (by omega) (by dsimp [c_s2, e2]; omega)))

end
end DetDLP.M14PktInternal

open DetDLP.M14PktInternal in
theorem solution :
    (∀ (origDesc : Bits) (j κ l q v : ℕ) (α : List Bool),
      2 ^ (κ / 4) ≤ q → κ = 4 * (κ / 4) →
      κ ≤ (encodePortQuery (lookupDesc origDesc j κ l q) v α).length) ∧
    (∀ (E_pkt : PrimitiveMachine) (o_pkt : Fin E_pkt.tapeCount) (K_loc : ℕ),
      ∃ (F_pkt : PrimitiveMachine) (oF_pkt : Fin F_pkt.tapeCount) (K_pkt : ℕ),
        1 ≤ K_pkt ∧
        ∀ {C c : ℕ} (x : Input C c) {f : ℤ[X]} (hf : f.Monic)
          (nd : SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf))
          (w : Fin nd.G.nV) (pkt : Bits) (h : nd.toStoppedSpec.vTable w = .pkt pkt)
          (β : Fin (nd.G.deg w) → Bool),
          let p := nd.toStoppedSpec.packet w pkt h
          let n_pkt := nd.G.nE + p.creation + 4 * D3Stopped.level x.S + x.l + 2
          let inp := Encoding.encodeList id [pkt, List.ofFn β]
          let ans := residue f x.l p.creation hf (p.entry β)
          inp.length ≤ K_pkt * (n_pkt + 1) ^ K_pkt ∧
          RunsWithin F_pkt oF_pkt inp ans
            (Real.exp ((K_pkt : ℝ) * (2 ^ D3Stopped.shift x.S (nd.d - 1) : ℕ) * Real.log n_pkt))
            (polyBound K_pkt n_pkt)) ∧
    ((C c K_grd K_wi K_pkt c_pkt : ℕ) →
      ∃ c_src : ℕ, c ≤ c_src ∧ 1 ≤ c_src ∧
        ∀ (N₁ : ℕ), 1 ≤ N₁ →
          ∀ (descLen jVal κ l q vVal αLen yLen xLen uLen : ℕ),
            descLen ≤ N₁ → jVal ≤ N₁ ^ c → κ ≤ 4 * N₁ → l ≤ 2 * C * N₁ →
            q ≤ (K_grd + 1) * N₁ ^ (K_grd + 1) → vVal ≤ 65544 * N₁ ^ 2 → αLen ≤ 3 * N₁ →
            uLen ≤ 64 * (descLen + jVal + κ + l + q + vVal + αLen + 4) →
            xLen ≤ 16 * (descLen + jVal + αLen + 4) →
            yLen ≤ (2 * N₁ + 4) * l + 1 →
            uLen ≤ c_src * N₁ ^ c_src ∧
            xLen ≤ c_src * N₁ ^ c_src ∧
            yLen ≤ c_src * N₁ ^ c_src) ∧
    ((C c K_grd K_wi K_pkt c_pkt : ℕ) →
      ∃ c_s2 : ℕ, c ≤ c_s2 ∧ 1 ≤ c_s2 ∧
        ∀ (N₁ n₁ m₁ : ℕ), 2 ≤ N₁ → N₁ ≤ n₁ → n₁ ≤ m₁ →
          (25 * m₁ ^ (c + 2) ≤ m₁ ^ c_s2) ∧
          (K_pkt * ((2 * N₁) ^ c_pkt + 1) ^ K_pkt ≤ c_s2 * n₁ ^ c_s2) ∧
          ∀ (uLen xStopLen yStopLen qStopLen : ℕ),
            uLen ≤ 1048576 * (C + 2) * (K_wi + 2) * N₁ ^ (max (2 * c + 6) (K_wi + 4)) →
            xStopLen ≤ 1048576 * (C + 2) * (K_wi + 2) * N₁ ^ (max (2 * c + 6) (K_wi + 4)) →
            yStopLen ≤ 1048576 * (C + 2) * N₁ ^ 6 →
            qStopLen ≤ 1048576 * (C + 2) * (K_wi + 2) * n₁ ^ (max (c + 4) (K_wi + 4)) →
            uLen ≤ c_s2 * N₁ ^ c_s2 ∧
            xStopLen ≤ c_s2 * N₁ ^ c_s2 ∧
            yStopLen ≤ c_s2 * N₁ ^ c_s2 ∧
            qStopLen ≤ c_s2 * n₁ ^ c_s2) :=
  ⟨@kappa_le_lookupQuery_len,
   @solo_packet_adapter_machine,
   @source_lengths_from_bounds,
   @stopped_lengths_from_bounds⟩
