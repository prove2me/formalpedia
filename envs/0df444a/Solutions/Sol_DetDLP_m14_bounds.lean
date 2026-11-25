-- Prove2me | solution 1 for DetDLP.m14_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-25T07:02:25.274937+00:00
-- url     : https://prove2.me/submissions/a4747fc9-81c2-4bbd-82bc-5f4034dafff4

import Definitions.Def_DetDLP_D4SoloPlanDefs
import Definitions.Def_DetDLP_W5_M6DriverFrames
import Theorems.Thm_DetDLP_m14_base_fuel
import Theorems.Thm_DetDLP_m14a_separator_edge_budget
import Theorems.Thm_DetDLP_d4_active_node_preconditions

set_option autoImplicit false
set_option maxHeartbeats 800000

open Polynomial Finset DetDLP DetDLP.AppendixD4 DetDLP.ResidualScalarOracle
open DetDLP.D4Plan DetDLP.D4StoppedNode DetDLP.D4RankWalker DetDLP.D4GuardTree
open DetDLP.D4SoloRaw DetDLP.D4SoloNode DetDLP.D4SoloRoot DetDLP.D4SoloStep
open DetDLP.D4SoloTree DetDLP.D4SoloForest DetDLP.D4SoloPlanDefs DetDLP.w5_SplitArithmetic
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

namespace DetDLP.M14BoundsInternal

noncomputable section

abbrev encodeList_mem_len_le {w : List Bool} {xs : List (List Bool)} (hw : w ∈ xs) :=
  DetDLP.m14_base_fuel.2.2.2.2.1 hw

abbrev clog2_le_self := DetDLP.m14_base_fuel.2.2.2.2.2.1

abbrev pow2_clog2_le {n : ℕ} (hn : 1 ≤ n) := DetDLP.m14_base_fuel.2.2.2.2.2.2.1 hn

private theorem deg_le_nE (G : BipartiteMultigraph) (v : Fin G.nV) : G.deg v ≤ G.nE := by
  unfold BipartiteMultigraph.deg BipartiteMultigraph.ports
  exact (List.length_filter_le _ _).trans (by simp)

theorem countWord_len_le_succ (n : ℕ) : (countWord n).length ≤ n + 1 := by
  cases n with
  | zero => decide
  | succ n =>
    rw [countWord_length_eq_bitLen (n + 1) (Nat.succ_pos n)]
    change Nat.clog 2 (n + 2) ≤ n + 2
    exact clog2_le_self (n + 2)

theorem countWord_len_of_le_pow {a m : ℕ} (ha : a ≤ 2 ^ m) :
    (countWord a).length ≤ m + 1 := by
  by_cases h0 : a = 0
  · subst h0; simp [countWord]
  · rw [countWord_length_eq_bitLen a (Nat.pos_of_ne_zero h0)]
    change Nat.clog 2 (a + 1) ≤ m + 1
    apply Nat.clog_le_of_le_pow
    have hpos : 1 ≤ 2 ^ m := Nat.one_le_pow _ _ (by decide)
    rw [pow_succ]
    omega

theorem encodeNatListBin_len_le (ns : List ℕ) (b : ℕ) (hb : ∀ n ∈ ns, (countWord n).length ≤ b) :
    (encodeNatListBin ns).length ≤ (2 * b + 2) * ns.length + 1 :=
  length_encodeList_le countWord ns b hb

theorem pack_len_le (ws : List Wd) (b : ℕ) (hb : ∀ w ∈ ws, w.length ≤ b) :
    (pack ws).length ≤ (2 * b + 2) * ws.length + 1 :=
  length_encodeList_le id ws b hb

theorem graph_encode_len_le (G : BipartiteMultigraph) :
    G.encode.length ≤ 32 * (G.nV + G.nE + 2) ^ 2 := by
  let b := G.nV + G.nE + 1
  let es := (List.finRange G.nE).flatMap fun e => [(G.endpoints e).1.val, (G.endpoints e).2.val]
  have hes_len : es.length = 2 * G.nE := by simp [es, List.length_flatMap]; omega
  have hes_enc : (encodeNatListBin es).length ≤ (2 * b + 2) * (2 * G.nE) + 1 := by
    refine (encodeNatListBin_len_le es b ?_).trans_eq (by rw [hes_len])
    intro a ha
    simp only [es, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at ha
    obtain ⟨e, _, rfl | rfl⟩ := ha
    · exact (countWord_len_le_succ _).trans (by have := (G.endpoints e).1.isLt; dsimp [b]; omega)
    · exact (countWord_len_le_succ _).trans (by have := (G.endpoints e).2.isLt; dsimp [b]; omega)
  let cap := (2 * b + 2) * (2 * G.nE) + b + 1
  have hG : G.encode.length ≤ (2 * cap + 2) * 4 + 1 := by
    apply length_encodeList_le id _ cap
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact (countWord_len_le_succ G.nV).trans (by dsimp [cap, b]; omega)
    · exact (countWord_len_le_succ G.nE).trans (by dsimp [cap, b]; omega)
    · simp only [id_eq, List.length_ofFn]; dsimp [cap, b]; omega
    · change (encodeNatListBin es).length ≤ cap
      dsimp [cap]; omega
  refine hG.trans ?_
  dsimp only [cap, b]
  nlinarith

theorem residue_len_le (f : ℤ[X]) (l q : ℕ) (hf : f.Monic) (z : B f l q) :
    (residue f l q hf z).length ≤ (2 * (q + 1) + 2) * (l * f.natDegree) + 1 := by
  unfold residue
  refine (encodeNatListBin_len_le _ (q + 1) ?_).trans_eq (by simp)
  intro v hv
  obtain ⟨idx, rfl⟩ := List.mem_ofFn.mp hv
  apply countWord_len_of_le_pow
  exact (ZMod.val_lt _).le

theorem polyBound_eq_natCast (K u : ℕ) :
    polyBound K u = ((K * (u + 1) ^ K : ℕ) : ℝ) := by
  unfold polyBound
  push_cast
  rfl

theorem shift_le_level_div_32768 (S j : ℕ) :
    D3Stopped.shift S j ≤ D3Stopped.level S / 32768 := by
  have hsum : ∀ k : ℕ, (∑ t ∈ Finset.range (k + 1), (D3Stopped.level S / 131072) / 2 ^ t) +
      (D3Stopped.level S / 131072) / 2 ^ k ≤ 2 * (D3Stopped.level S / 131072) := by
    intro k
    induction k with
    | zero => simp; omega
    | succ k ih =>
      rw [Finset.sum_range_succ]
      have hdiv : (D3Stopped.level S / 131072) / 2 ^ (k + 1) +
          (D3Stopped.level S / 131072) / 2 ^ (k + 1) ≤ (D3Stopped.level S / 131072) / 2 ^ k := by
        rw [pow_succ, ← Nat.div_div_eq_div_mul]
        omega
      omega
  have hb_le : ∑ t ∈ Finset.range (j + 1), (D3Stopped.level S / 131072) / 2 ^ t ≤
      2 * (D3Stopped.level S / 131072) :=
    (Nat.le_add_right _ _).trans (hsum j)
  have h4 : 4 * (D3Stopped.level S / 131072) ≤ D3Stopped.level S / 32768 := by omega
  unfold D3Stopped.shift
  simp only [D3Stopped.width]
  omega

theorem input_params_le {C c : ℕ} (x : Input C c) :
    4 * x.m * x.k ≤ 2 * x.S ∧
    x.G.nE ≤ 3 * x.S ∧
    x.m ≤ 2 * x.S ∧
    x.k ≤ 2 * x.S ∧
    x.b ≤ 2 * C * x.S ∧
    x.l ≤ 2 * C * x.S ∧
    x.p ≤ x.S ∧
    x.S ≤ size x ∧
    x.desc.length ≤ size x := by
  obtain ⟨hmk, hne⟩ := DetDLP.m14a_separator_edge_budget x.spec
  have hm1 : x.m ≤ 4 * x.m * x.k := by
    calc x.m = 1 * x.m * 1 := by ring
      _ ≤ 4 * x.m * x.k := Nat.mul_le_mul (Nat.mul_le_mul_right _ (by decide)) x.hk
  have hk1 : x.k ≤ 4 * x.m * x.k := by
    have h4m : 1 ≤ 4 * x.m := by have := x.hm; omega
    calc x.k = 1 * x.k := (one_mul x.k).symm
      _ ≤ (4 * x.m) * x.k := Nat.mul_le_mul_right _ h4m
  have hb : x.b ≤ 2 * C * x.S := by
    calc x.b ≤ C * (4 * x.m * x.k) := x.lower
      _ ≤ C * (2 * x.S) := Nat.mul_le_mul_left C hmk
      _ = 2 * C * x.S := by ring
  have hl : x.l ≤ 2 * C * x.S := by
    calc x.l ≤ C * x.m := x.lm
      _ ≤ C * (2 * x.S) := Nat.mul_le_mul_left C (hm1.trans hmk)
      _ = 2 * C * x.S := by ring
  exact ⟨hmk, hne, hm1.trans hmk, hk1.trans hmk, hb, hl, x.pS,
    Nat.le_add_right _ _, Nat.le_add_left _ _⟩

/-- Uniform polynomial bound on `(D4Plan.input x).length` in terms of `size x`, valid for ALL `x`. -/
theorem input_len_le_poly {C c : ℕ} (_hc : 0 < c) :
    ∃ K_in : ℕ, 1 ≤ K_in ∧ ∀ x : Input C c,
      (D4Plan.input x).length ≤ K_in * (size x + 1) ^ K_in := by
  let K_in := 16384 * (C + 2) ^ 2 + 2 * c + 4
  refine ⟨K_in, by dsimp [K_in]; omega, fun x => ?_⟩
  obtain ⟨_, hne, hm, hk, hb, hl, hp, hS_sz, hdesc_sz⟩ := input_params_le x
  let N := size x + 1
  have hN1 : 1 ≤ N := Nat.succ_pos _
  let Y := (C + 2) * N ^ (c + 1)
  have hN_le_Nc : N ≤ N ^ (c + 1) := by
    calc N = N ^ 1 := (pow_one N).symm
      _ ≤ N ^ (c + 1) := Nat.pow_le_pow_right hN1 (Nat.succ_pos c)
  have hY_ge_N : N ≤ Y := by
    calc N ≤ 1 * N ^ (c + 1) := by rw [one_mul]; exact hN_le_Nc
      _ ≤ (C + 2) * N ^ (c + 1) := Nat.mul_le_mul_right _ (by omega)
  have hdesc_Y : x.desc.length ≤ Y := (hdesc_sz.trans (Nat.le_succ _)).trans hY_ge_N
  have hS_Y : x.S + 1 ≤ Y := (Nat.succ_le_succ hS_sz).trans hY_ge_N
  have hp_Y : x.p + 1 ≤ Y := (Nat.succ_le_succ (hp.trans hS_sz)).trans hY_ge_N
  have hm_Y : x.m + 1 ≤ 2 * Y := by
    have : x.m + 1 ≤ 2 * N := hm.trans_lt (by dsimp [N]; omega)
    exact this.trans (Nat.mul_le_mul_left 2 hY_ge_N)
  have hk_Y : x.k + 1 ≤ 2 * Y := by
    have : x.k + 1 ≤ 2 * N := hk.trans_lt (by dsimp [N]; omega)
    exact this.trans (Nat.mul_le_mul_left 2 hY_ge_N)
  have h2CN : 2 * C * x.S + 1 ≤ 2 * Y := by
    have : 2 * C * x.S + 1 ≤ 2 * (C + 2) * N := by dsimp [N]; nlinarith
    calc 2 * C * x.S + 1 ≤ 2 * (C + 2) * N := this
      _ ≤ 2 * ((C + 2) * N ^ (c + 1)) := by
        have := Nat.mul_le_mul_left (2 * (C + 2)) hN_le_Nc
        nlinarith
  have hnV : x.G.nV ≤ N ^ (c + 1) :=
    x.nV.trans (Nat.pow_le_pow_right hN1 (Nat.le_succ c))
  have hnV_Y : x.G.nV ≤ Y := hnV.trans (Nat.le_mul_of_pos_left _ (by omega))
  have hnE : x.G.nE ≤ 3 * N := hne.trans (by dsimp [N]; omega)
  have hG_enc : x.G.encode.length ≤ 32 * (5 * Y) ^ 2 := by
    refine (graph_encode_len_le x.G).trans ?_
    apply Nat.mul_le_mul_left 32
    apply Nat.pow_le_pow_left
    omega
  let cap := 32 * (5 * Y) ^ 2 + 2 * Y + 2
  have hterm : (D4Plan.input x).length ≤ (2 * cap + 2) * 9 + 1 := by
    apply length_encodeList_le id _ cap
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [id_eq]; dsimp [cap]; omega
    · simp only [id_eq]; dsimp [cap]; omega
    · exact (countWord_len_le_succ x.b).trans (by dsimp [cap]; omega)
    · exact (countWord_len_le_succ x.m).trans (by dsimp [cap]; omega)
    · exact (countWord_len_le_succ x.k).trans (by dsimp [cap]; omega)
    · exact (countWord_len_le_succ x.S).trans (by dsimp [cap]; omega)
    · exact (countWord_len_le_succ x.p).trans (by dsimp [cap]; omega)
    · exact (countWord_len_le_succ x.l).trans (by dsimp [cap]; omega)
    · simp only [id_eq, List.length_ofFn]; dsimp [cap]; omega
  refine hterm.trans ?_
  have hY1 : 1 ≤ Y := hN1.trans hY_ge_N
  have hY_le_Y2 : Y ≤ Y ^ 2 := by nlinarith
  have h1 : (2 * cap + 2) * 9 + 1 ≤ 16000 * Y ^ 2 := by
    dsimp [cap]
    nlinarith [hY1, hY_le_Y2]
  have hY_sq : 16000 * Y ^ 2 = (16000 * (C + 2) ^ 2) * N ^ (2 * c + 2) := by
    dsimp [Y]; ring
  rw [hY_sq] at h1
  refine h1.trans (Nat.mul_le_mul ?_ (Nat.pow_le_pow_right hN1 ?_))
  · dsimp [K_in]; omega
  · dsimp [K_in]; omega

/-- Rate majorization: `x.S / √(level x.S) ≤ 9 * (C + 1)^3 * (x.b / x.m)` for `C + 6 ≤ level x.S`. -/
theorem source_rate_le_plan_rate {C c : ℕ} (x : Input C c) (K_B : ℕ)
    (hL : C + 6 ≤ D3Stopped.level x.S) :
    (K_B : ℝ) * (x.S : ℝ) / Real.sqrt (D3Stopped.level x.S : ℝ) ≤
      ((9 * (C + 1) ^ 3 * K_B : ℕ) : ℝ) * ((x.b : ℝ) / (x.m : ℝ)) := by
  let L := D3Stopped.level x.S
  have hL1 : 1 ≤ L := by dsimp [L]; omega
  have hLr_pos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL1
  have hsqrtL_pos : (0 : ℝ) < Real.sqrt (L : ℝ) := Real.sqrt_pos.mpr hLr_pos
  have hssqrtL_ge1 : (1 : ℝ) ≤ Real.sqrt (Real.sqrt (L : ℝ)) := by
    have h1 : (1 : ℝ) ≤ Real.sqrt (L : ℝ) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hL1)
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt h1
  obtain ⟨_, _, _, _, hb_S, _, _, _, _⟩ := input_params_le x
  have hS_pow : x.S ≤ 2 ^ L := Nat.le_pow_clog (by decide : 1 < 2) x.S
  have hC_pow : C + 1 ≤ 2 ^ (C + 1) := (Nat.lt_pow_self (by decide : 1 < 2)).le
  have hb2_pow : x.b + 2 ≤ 2 ^ (16 * L) := by
    have hexp_le : (C + 1) + 2 + L ≤ 16 * L := by dsimp [L] at *; omega
    have h1 : x.b + 2 ≤ 2 * (C + 1) * 2 ^ L + 2 := by
      have : x.b ≤ 2 * (C + 1) * x.S := by nlinarith [hb_S]
      exact Nat.add_le_add_right (this.trans (Nat.mul_le_mul_left _ hS_pow)) 2
    have h2 : 2 * (C + 1) * 2 ^ L + 2 ≤ 2 ^ ((C + 1) + 2 + L) := by
      have hpL : 1 ≤ 2 ^ L := Nat.one_le_pow _ _ (by decide)
      have hpC := Nat.mul_le_mul_right (2 ^ L) (Nat.mul_le_mul_left 2 hC_pow)
      calc 2 * (C + 1) * 2 ^ L + 2
          ≤ 2 * 2 ^ (C + 1) * 2 ^ L + 2 * 2 ^ (C + 1) * 2 ^ L := by nlinarith
        _ = 2 ^ ((C + 1) + 2 + L) := by rw [pow_add, pow_add]; ring
    exact h1.trans (h2.trans (Nat.pow_le_pow_right (by decide) hexp_le))
  have hclog_b : Nat.clog 2 (x.b + 2) ≤ 16 * L := Nat.clog_le_of_le_pow hb2_pow
  let t : ℝ := (Nat.clog 2 (x.b + 2) : ℝ)
  have ht_nonneg : 0 ≤ t := Nat.cast_nonneg _
  have ht_le : t ≤ 16 * (L : ℝ) := by
    have h1 : (Nat.clog 2 (x.b + 2) : ℝ) ≤ ((16 * L : ℕ) : ℝ) := Nat.cast_le.mpr hclog_b
    push_cast at h1
    exact h1
  have ht_qtr : t ^ ((1 : ℝ) / 4) = Real.sqrt (Real.sqrt t) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul ht_nonneg]
    norm_num
  have hss_le : Real.sqrt (Real.sqrt t) ≤ 2 * Real.sqrt (Real.sqrt (L : ℝ)) := by
    have hs1 : Real.sqrt t ≤ 4 * Real.sqrt (L : ℝ) := by
      calc Real.sqrt t ≤ Real.sqrt (16 * (L : ℝ)) := Real.sqrt_le_sqrt ht_le
        _ = Real.sqrt ((4 : ℝ) ^ 2) * Real.sqrt (L : ℝ) := by
          rw [← Real.sqrt_mul (by positivity)]; norm_num
        _ = 4 * Real.sqrt (L : ℝ) := by rw [Real.sqrt_sq (by positivity)]
    calc Real.sqrt (Real.sqrt t) ≤ Real.sqrt (4 * Real.sqrt (L : ℝ)) := Real.sqrt_le_sqrt hs1
      _ = Real.sqrt ((2 : ℝ) ^ 2) * Real.sqrt (Real.sqrt (L : ℝ)) := by
        rw [← Real.sqrt_mul (by positivity)]; norm_num
      _ = 2 * Real.sqrt (Real.sqrt (L : ℝ)) := by rw [Real.sqrt_sq (by positivity)]
  have hblk_le : (blockCount x.b : ℝ) ≤ 3 * Real.sqrt (Real.sqrt (L : ℝ)) := by
    unfold blockCount
    rw [Nat.cast_max]
    apply max_le
    · push_cast; linarith
    · have hceil : (⌈t ^ ((1 : ℝ) / 4)⌉₊ : ℝ) ≤ t ^ ((1 : ℝ) / 4) + 1 :=
        (Nat.ceil_lt_add_one (Real.rpow_nonneg ht_nonneg _)).le
      have hceil' : (⌈t ^ ((1 : ℝ) / 4)⌉₊ : ℝ) ≤ Real.sqrt (Real.sqrt t) + 1 := by
        calc (⌈t ^ ((1 : ℝ) / 4)⌉₊ : ℝ) ≤ t ^ ((1 : ℝ) / 4) + 1 := hceil
          _ = Real.sqrt (Real.sqrt t) + 1 := by rw [ht_qtr]
      linarith
  have hm_r : (x.m : ℝ) ≤ 3 * ((C : ℝ) + 1) * Real.sqrt (Real.sqrt (L : ℝ)) := by
    have hm_nat : (x.m : ℝ) ≤ (C : ℝ) * (blockCount x.b : ℝ) := by exact_mod_cast x.mb
    have hC1 : (C : ℝ) * (blockCount x.b : ℝ) ≤ ((C : ℝ) + 1) * (blockCount x.b : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
    calc (x.m : ℝ) ≤ ((C : ℝ) + 1) * (blockCount x.b : ℝ) := hm_nat.trans hC1
      _ ≤ ((C : ℝ) + 1) * (3 * Real.sqrt (Real.sqrt (L : ℝ))) :=
        mul_le_mul_of_nonneg_left hblk_le (by positivity)
      _ = 3 * ((C : ℝ) + 1) * Real.sqrt (Real.sqrt (L : ℝ)) := by ring
  have hm_sq : (x.m : ℝ) ^ 2 ≤ 9 * ((C : ℝ) + 1) ^ 2 * Real.sqrt (L : ℝ) := by
    calc (x.m : ℝ) ^ 2
        ≤ (3 * ((C : ℝ) + 1) * Real.sqrt (Real.sqrt (L : ℝ))) ^ 2 :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) hm_r 2
      _ = 9 * ((C : ℝ) + 1) ^ 2 * (Real.sqrt (Real.sqrt (L : ℝ))) ^ 2 := by ring
      _ = 9 * ((C : ℝ) + 1) ^ 2 * Real.sqrt (L : ℝ) := by
          rw [Real.sq_sqrt (Real.sqrt_nonneg _)]
  have hm_pos : (0 : ℝ) < (x.m : ℝ) := by exact_mod_cast x.hm
  have hS_r : (x.S : ℝ) ≤ ((C : ℝ) + 1) * (x.m : ℝ) * (x.b : ℝ) := by
    have h1 : (x.S : ℝ) ≤ ((C * x.m * x.b : ℕ) : ℝ) := Nat.cast_le.mpr x.hS
    push_cast at h1
    nlinarith [Nat.cast_nonneg (α := ℝ) x.m, Nat.cast_nonneg (α := ℝ) x.b]
  have hmain : (x.S : ℝ) / Real.sqrt (L : ℝ) ≤ 9 * ((C : ℝ) + 1) ^ 3 * ((x.b : ℝ) / (x.m : ℝ)) := by
    rw [div_le_iff₀ hsqrtL_pos]
    have h1 : ((C : ℝ) + 1) * (x.m : ℝ) * (x.b : ℝ) =
        (((C : ℝ) + 1) * (x.m : ℝ) ^ 2) * ((x.b : ℝ) / (x.m : ℝ)) := by
      field_simp [hm_pos.ne']
    calc (x.S : ℝ) ≤ ((C : ℝ) + 1) * (x.m : ℝ) * (x.b : ℝ) := hS_r
      _ = (((C : ℝ) + 1) * (x.m : ℝ) ^ 2) * ((x.b : ℝ) / (x.m : ℝ)) := h1
      _ ≤ (((C : ℝ) + 1) * (9 * ((C : ℝ) + 1) ^ 2 * Real.sqrt (L : ℝ))) * ((x.b : ℝ) / (x.m : ℝ)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hm_sq (add_nonneg (Nat.cast_nonneg C) zero_le_one))
            (div_nonneg (Nat.cast_nonneg x.b) (Nat.cast_nonneg x.m))
      _ = 9 * ((C : ℝ) + 1) ^ 3 * ((x.b : ℝ) / (x.m : ℝ)) * Real.sqrt (L : ℝ) := by ring
  calc (K_B : ℝ) * (x.S : ℝ) / Real.sqrt (L : ℝ)
      = (K_B : ℝ) * ((x.S : ℝ) / Real.sqrt (L : ℝ)) := by ring
    _ ≤ (K_B : ℝ) * (9 * ((C : ℝ) + 1) ^ 3 * ((x.b : ℝ) / (x.m : ℝ))) :=
        mul_le_mul_of_nonneg_left hmain (Nat.cast_nonneg _)
    _ = ((9 * (C + 1) ^ 3 * K_B : ℕ) : ℝ) * ((x.b : ℝ) / (x.m : ℝ)) := by push_cast; ring

theorem unrollCertFuel_done_depth_le {C c : ℕ} (x : Input C c) {f : ℤ[X]} (hf : f.Monic)
    (M_node E_pkt : PrimitiveMachine) (o_node : Fin M_node.tapeCount) (o_pkt : Fin E_pkt.tapeCount)
    (K_loc H_loc c_loc guard : ℕ) :
    let D := Nat.clog 32 (4 * x.m)
    ∀ (fuel : ℕ)
      (todo : List (WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc))
      (done : List (SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)))
      (accVal : B f x.l (guard + x.p)) (lossSum : ℕ),
      (∀ it ∈ todo, it.2.1.d + it.1 = D) →
      (∀ m ∈ done, m.d ≤ D) →
      treeAll (fun lf => ∀ m ∈ lf.doneNodes, m.d ≤ D)
        (unrollCertFuel x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc guard fuel todo done accVal lossSum) := by
  intro D fuel
  have hpeel_sub : ∀ xs : List (WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc),
      (∀ m ∈ (peelCert xs).1, m ∈ todoNodes xs) ∧
      (∀ y ∈ (peelCert xs).2, y ∈ xs) := by
    intro xs
    induction xs with
    | nil => exact And.intro (fun _ h => by cases h) (fun _ h => by cases h)
    | cons z zs ihz =>
      rcases z with ⟨kz, ndz, uz⟩
      cases kz with
      | zero =>
        refine ⟨fun m hm => ?_, fun y hy => List.mem_cons_of_mem _ (ihz.2 y hy)⟩
        rcases List.mem_cons.mp hm with rfl | hrest
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ihz.1 m hrest)
      | succ kz =>
        cases uz with
        | inl _ =>
          refine ⟨fun m hm => ?_, fun y hy => List.mem_cons_of_mem _ (ihz.2 y hy)⟩
          rcases List.mem_cons.mp hm with rfl | hrest
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (ihz.1 m hrest)
        | inr _ =>
          exact And.intro (fun _ h => by cases h) (fun _ h => h)
  induction fuel with
  | zero =>
    intro todo done accVal lossSum hdepth hdone
    simp only [unrollCertFuel, treeAll]
    intro m hm
    rcases List.mem_append.mp hm with h1 | h2
    · exact hdone m h1
    · obtain ⟨it, hit, rfl⟩ := List.mem_map.mp ((hpeel_sub todo).1 m h2)
      have := hdepth it hit; omega
  | succ fuel ih =>
    intro todo done accVal lossSum hdepth hdone
    have hdone' : ∀ m ∈ done ++ (peelCert todo).1, m.d ≤ D := by
      intro m hm
      rcases List.mem_append.mp hm with h1 | h2
      · exact hdone m h1
      · obtain ⟨it, hit, rfl⟩ := List.mem_map.mp ((hpeel_sub todo).1 m h2)
        have := hdepth it hit; omega
    rcases peelCert_rem_shape todo with hrem0 | ⟨k, nd, cert, sub, tail, hrem⟩
    · simp only [unrollCertFuel, hrem0, treeAll]
      exact hdone'
    · simp only [unrollCertFuel, hrem, treeAll]
      intro d
      apply ih
      · intro it hit
        rcases List.mem_append.mp hit with hch | htl
        · obtain ⟨g, rfl⟩ := List.mem_ofFn.mp hch
          have hd_nd := hdepth ⟨k + 1, nd, PSum.inr ⟨cert, sub⟩⟩
            ((hpeel_sub todo).2 _ (by rw [hrem]; exact List.mem_cons_self))
          change (nd.d + 1) + k = D
          dsimp only at hd_nd; omega
        · exact hdepth it ((hpeel_sub todo).2 it (by rw [hrem]; exact List.mem_cons_of_mem _ htl))
      · exact hdone'

theorem cap_bound_of_active_pre {C c : ℕ} (hC : 0 < C) (x : Input C c)
    {f : ℤ[X]} {PktOK : PktPred f x.l} (nd : SoloNode x f PktOK)
    (hL_act : max 6 (DetDLP.d4_active_node_preconditions C hC).choose ≤ D3Stopped.level x.S) :
    nd.G.maxDeg ≤ D3Stopped.cap x.S := by
  let L := D3Stopped.level x.S
  have hL6 : 6 ≤ L := (le_max_left _ _).trans hL_act
  have hLact : (DetDLP.d4_active_node_preconditions C hC).choose ≤ L :=
    (le_max_right _ _).trans hL_act
  have hS_gt16 : 32 < x.S := by
    have hlt : 5 < Nat.clog 2 x.S := by change 5 < L; omega
    have hp := (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).mp hlt
    norm_num at hp
    exact hp
  have hsqrt_ge2 : 2 ≤ max 1 L.sqrt := by
    have h4 : 2 ^ 2 ≤ L := by omega
    exact (Nat.le_sqrt.mpr h4).trans (le_max_right 1 L.sqrt)
  have hthresh_lt_S : D3Stopped.threshold x.S < x.S := by
    unfold D3Stopped.threshold
    have hs_le : L.sqrt ≤ x.S := (Nat.sqrt_le_self L).trans (clog2_le_self x.S)
    have h1 : x.S + L.sqrt - 1 < x.S * max 1 L.sqrt := by
      have hm : x.S * 2 ≤ x.S * max 1 L.sqrt := Nat.mul_le_mul_left _ hsqrt_ge2
      omega
    exact (Nat.div_lt_iff_lt_mul (by positivity)).mpr h1
  let Δ₀ := C * Nat.ceil ((x.b : ℝ) ^ ((3 : ℝ) / 4))
  have hpre := (DetDLP.d4_active_node_preconditions C hC).choose_spec x 0 x.S Δ₀ x.p
    hLact hthresh_lt_S (by simp) (le_max_left _ _) (Nat.le_add_right _ _)
  have hΔ_cap : Δ₀ ≤ D3Stopped.cap x.S :=
    (le_max_left _ _).trans hpre.2.2.2.2.2.2.2.1
  have h2_cap : (if nd.d = 0 then 0 else 2 * 2 ^ D3Stopped.shift x.S (nd.d - 1)) ≤ D3Stopped.cap x.S := by
    split_ifs with hd0
    · exact Nat.zero_le _
    · unfold D3Stopped.cap
      have hsh := shift_le_level_div_32768 x.S (nd.d - 1)
      have hexp : D3Stopped.shift x.S (nd.d - 1) + 1 ≤ (9 * L + 9) / 10 := by
        change D3Stopped.shift x.S (nd.d - 1) ≤ L / 32768 at hsh
        omega
      calc 2 * 2 ^ D3Stopped.shift x.S (nd.d - 1)
          = 2 ^ (D3Stopped.shift x.S (nd.d - 1) + 1) := (pow_succ' 2 _).symm
        _ ≤ 2 ^ ((9 * L + 9) / 10) := Nat.pow_le_pow_right (by decide) hexp
  exact nd.deg_le.trans (max_le hΔ_cap h2_cap)

theorem pkt_origDeg_le {E_pkt : PrimitiveMachine} {oe : Fin E_pkt.tapeCount} {K_loc : ℕ}
    {C c : ℕ} {x : Input C c} {f : ℤ[X]} {hf : f.Monic}
    {dCreate pCreate origDeg : ℕ} {rawDesc : Bits} {entry₀ : (Fin origDeg → Bool) → B f x.l pCreate}
    (hpkt : pktOKOf E_pkt oe K_loc x f hf dCreate pCreate origDeg rawDesc entry₀) :
    (origDeg : ℝ) ≤ polyBound K_loc (pCreate + 4 * D3Stopped.level x.S + x.l + 2) := by
  have hrun := hpkt.2.2.2.2 (fun _ => false)
  have hin_le := runsWithin_input_len_le hrun
  have hlen : origDeg ≤ (Encoding.encodeList id [rawDesc, List.ofFn (fun _ : Fin origDeg => false)]).length := by
    have hmem : List.ofFn (fun _ : Fin origDeg => false) ∈
        [rawDesc, List.ofFn (fun _ : Fin origDeg => false)] := by simp
    simpa using encodeList_mem_len_le hmem
  exact (by exact_mod_cast hlen : (origDeg : ℝ) ≤ _).trans hin_le

theorem rootSoloNode_portsBounded {C c : ℕ} (x : Input C c) (f : ℤ[X]) (PktOK : PktPred f x.l) :
    NodePortsBounded x.S (rootSoloNode x f PktOK) := by
  let rootNode := rootSoloNode x f PktOK
  let L := x.spec.lookupVerts
  let t := rootCut x
  have hSpec := DetDLP.d4_core_cut_poly_and_spec.2 x
  have hcut : D4CoreCut.cutCoreRaw (D4Plan.input x) = t.encode x.G L := hSpec.1
  have hnE_le : t.H₀.nE ≤ x.S := hSpec.2.1
  have hbits := rootSoloNode_bits_eq x f PktOK
  intro w
  have hlhs : (unpack (fld rootNode.toWorkItem.bits 4)).getD w.val [] = (rootNode.verts w).specBits := by
    unfold SoloNode.toWorkItem WorkItem.bits
    simp only [fld_pack, List.getD_cons_succ, List.getD_cons_zero, unpack_pack]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [List.length_ofFn]; exact w.isLt),
        List.getElem_ofFn, Option.getD_some]
  have hrhs : ∀ m ∈ ints (fld ((unpack (fld (rootRaw (D4CoreCut.cutCoreRaw (D4Plan.input x)) x.p) 4)).getD w.val []) 2),
      m ≤ x.S := by
    rw [hcut]
    unfold rootRaw D4CoreCut.Cut.encode rootVSpecAt
    simp only [fld_pack, fld_encodeList_id, unpack_encodeList_id, List.getD_cons_succ,
      List.getD_cons_zero, unpack_pack, ints_encodeNatListBin, List.length_ofFn]
    have hw_t : w.val < t.H₀.nV := w.isLt
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [hw_t]),
        List.getElem_map, List.getElem_range, Option.getD_some]
    simp only [fld_pack, List.getD_cons_succ, List.getD_cons_zero, ints_encodeNatListBin]
    intro m hm
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp hm
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [hw_t]),
        List.getElem_ofFn, Option.getD_some, ints_encodeNatListBin]
    have hidx_le : List.idxOf r (List.ofFn fun j : Fin (t.H₀.deg ⟨w.val, hw_t⟩) => (t.incl ⟨w.val, hw_t⟩ j).val) ≤
        (List.ofFn fun j : Fin (t.H₀.deg ⟨w.val, hw_t⟩) => (t.incl ⟨w.val, hw_t⟩ j).val).length :=
      List.idxOf_le_length
    rw [List.length_ofFn] at hidx_le
    exact hidx_le.trans ((deg_le_nE t.H₀ ⟨w.val, hw_t⟩).trans hnE_le)
  have hspec_eq : (rootNode.verts w).specBits =
      (unpack (fld (rootRaw (D4CoreCut.cutCoreRaw (D4Plan.input x)) x.p) 4)).getD w.val [] := by
    rw [← hlhs, hbits]
  have htag_false : fld (rootNode.verts w).specBits 0 = [false] := by
    rw [hspec_eq, hcut]
    unfold rootRaw D4CoreCut.Cut.encode rootVSpecAt
    have hw_t : w.val < t.H₀.nV := w.isLt
    simp only [fld_pack, fld_encodeList_id, unpack_pack, List.getD_cons_succ,
      List.getD_cons_zero, ints_encodeNatListBin, List.length_ofFn]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [hw_t]),
        List.getElem_map, List.getElem_range, Option.getD_some]
    simp [fld_pack]
  cases hsv : rootNode.verts w with
  | orig v₀ hv₀ pinPort portMap hlen hports =>
    dsimp only [VertPortBounded]
    intro m hm
    apply hrhs m
    rw [← hspec_eq, hsv]
    simp [SoloVert.specBits, fld_pack, hm]
  | pkt _ _ _ _ _ _ _ _ permOpt _ =>
    rw [hsv] at htag_false
    cases permOpt <;> simp [SoloVert.specBits, fld_pack] at htag_false

theorem pushChild_portBounded {C c : ℕ} {x : Input C c} {G G' : BipartiteMultigraph}
    {f : ℤ[X]} {PktOK : PktPred f x.l} {pCurr dNode : ℕ} {w : Fin G.nV} {w' : Fin G'.nV}
    (p' : ℕ) (hp' : pCurr ≤ p') (pe : Fin (G.deg w) ≃ Fin (G'.deg w'))
    (sv : SoloVert x G f PktOK pCurr dNode w) (B_port : ℕ) (hG'_nE : G'.nE ≤ B_port) :
    VertPortBounded B_port (sv.pushChild p' hp' pe) := by
  have hget_le : ∀ j : ℕ, ((List.ofFn fun i : Fin (G.deg w) => (pe i).val).getD j 0) ≤ B_port := by
    intro j
    by_cases hj : j < G.deg w
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [hj]),
          List.getElem_ofFn, Option.getD_some]
      exact (pe ⟨j, hj⟩).isLt.le.trans ((deg_le_nE G' w').trans hG'_nE)
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
      exact Nat.zero_le _
  cases sv with
  | orig _ _ _ portMap _ _ =>
    dsimp only [SoloVert.pushChild, VertPortBounded]
    intro m hm
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hm
    exact hget_le j
  | pkt _ _ _ _ _ _ _ _ permOpt _ =>
    cases permOpt with
    | none =>
      dsimp only [SoloVert.pushChild, VertPortBounded]
      intro m hm
      rw [List.mem_ofFn] at hm
      obtain ⟨i, rfl⟩ := hm
      exact (pe i).isLt.le.trans ((deg_le_nE G' w').trans hG'_nE)
    | some pm =>
      dsimp only [SoloVert.pushChild, VertPortBounded]
      intro m hm
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hm
      exact hget_le j

theorem childSoloNode_portsBounded {C c : ℕ} {x : Input C c} {f : ℤ[X]} {hf : f.Monic}
    {M_node E_pkt : PrimitiveMachine} {o_node : Fin M_node.tapeCount} {o_pkt : Fin E_pkt.tapeCount}
    {K_loc H_loc c_loc : ℕ}
    {nd : SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)}
    (cert : ActiveNodeCert x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc nd)
    (ν : Branch cert.s) (g : Fin 64) :
    NodePortsBounded x.S (cert.childNode ν g) := by
  intro w
  let cnd := cert.childNode ν g
  have hc_nE : cnd.G.nE ≤ x.S := cnd.edges_le.trans (Nat.div_le_self _ _)
  let ch := cert.s.child ν.1 ν.2.1 ν.2.2 g
  cases hcw : ch.oldOrPacket w with
  | inl v =>
    have hv := childVert_inl x hf E_pkt o_pkt K_loc nd cert.s rfl cert.hinc_le
      cert.hpkt_eval cert.hdeg_f ν g w v hcw
    dsimp only [ActiveNodeCert.childNode, childSoloNode]
    rw [hv]
    exact pushChild_portBounded _ _ _ _ x.S hc_nE
  | inr r =>
    obtain ⟨_, hr⟩ := childVert_inr x hf E_pkt o_pkt K_loc nd cert.s rfl cert.hinc_le
      cert.hpkt_eval cert.hdeg_f ν g w r hcw
    dsimp only [ActiveNodeCert.childNode, childSoloNode]
    rw [hr]
    trivial

private theorem node_len_from_M {C c : ℕ} {x : Input C c} {f : ℤ[X]} {hf : f.Monic}
    {E_pkt : PrimitiveMachine} {o_pkt : Fin E_pkt.tapeCount} {K_loc : ℕ}
    (nd : SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf))
    (N M_elt : ℕ) (hM1 : 1 ≤ M_elt) (hN_M : N ≤ M_elt)
    (hxS_N : x.S ≤ N) (hmk_N : 4 * x.m * x.k ≤ 2 * N) (hne_N : x.G.nE ≤ 3 * N)
    (hxV_M : x.G.nV ≤ M_elt)
    (hd_N : nd.d ≤ 8 * N) (hnE_nd : nd.G.nE ≤ N) (hnV_M : nd.G.nV ≤ M_elt)
    (hpCurr_M2 : nd.pCurr ≤ 161 * M_elt ^ 2) (hpins_len : nd.pins.length ≤ 100 * N)
    (hpkt_bounds : ∀ {dCr pCr oDeg : ℕ} {rDesc : Bits} {ent₀ : (Fin oDeg → Bool) → B f x.l pCr},
      pCr ≤ nd.pCurr →
      pktOKOf E_pkt o_pkt K_loc x f hf dCr pCr oDeg rDesc ent₀ →
      rDesc.length ≤ M_elt ∧ oDeg ≤ M_elt) :
    nd.toStoppedSpec.tableBits.length ≤ 262144 * M_elt ^ 3 ∧
    (NodePortsBounded x.S nd → nd.toWorkItem.bits.length ≤ 262144 * M_elt ^ 3) := by
  have hvs_len : ∀ w : Fin nd.G.nV,
      (VertexSpec.bits ((nd.verts w).toVertexSpec (nd.pinPosOf w))).length ≤ 4096 * M_elt ^ 2 := by
    intro w
    have hpinPos : nd.pinPosOf w ≤ 100 * N := by
      unfold SoloNode.pinPosOf findPinPos
      by_cases hne_l : ((List.range (nd.pins.map fun pv => encodeNatListBin [pv.1.val, pv.2.val]).length).filter
          (fun idx => decide ((ints ((nd.pins.map fun pv => encodeNatListBin [pv.1.val, pv.2.val]).getD idx [])).getD 1 0 = w.val))) = []
      · rw [hne_l, List.headD_nil, List.length_map]; exact hpins_len
      · obtain ⟨hd_el, tl, hcons⟩ := List.exists_cons_of_ne_nil hne_l
        rw [hcons, List.headD_cons]
        have hmem : hd_el ∈ List.range nd.pins.length := by
          have hm := (List.mem_filter.mp (hcons ▸ List.mem_cons_self)).1
          simpa using hm
        exact (List.mem_range.mp hmem).le.trans hpins_len
    cases hsv : nd.verts w with
    | orig v₀ hv₀ pinPort portMap hlen hports =>
      dsimp only [SoloVert.toVertexSpec, VertexSpec.bits]
      simp only [List.length_cons]
      have hv0_M : v₀.val ≤ M_elt := v₀.isLt.le.trans hxV_M
      have hdeg0 : x.G.deg v₀ ≤ 3 * N := (deg_le_nE x.G v₀).trans hne_N
      let routedL := (List.range (x.G.deg v₀)).map fun r =>
        if SoloVert.pinCode pinPort = r + 1 then (true, nd.pinPosOf w)
        else (false, portMap.getD r 0)
      have hrouted_len : (Encoding.encodeList (fun r : Bool × ℕ => r.1 :: countWord r.2) routedL).length ≤
          (2 * (100 * N + 2) + 2) * (3 * N) + 1 := by
        refine (length_encodeList_le _ _ (100 * N + 2) ?_).trans ?_
        · intro rt hrt
          obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hrt
          have hr_lt : r < x.G.deg v₀ := List.mem_range.mp hr
          split_ifs with hpc
          · simp only [List.length_cons]
            exact Nat.add_le_add_right ((countWord_len_le_succ _).trans (by omega)) 1
          · simp only [List.length_cons]
            have hne_pr : pinPort ≠ some ⟨r, hr_lt⟩ := by
              intro heq; subst heq; simp [SoloVert.pinCode] at hpc
            have hlt_deg : portMap.getD r 0 ≤ N := by
              have h1 := hports ⟨r, hr_lt⟩ hne_pr
              dsimp only at h1
              exact h1.le.trans ((deg_le_nE nd.G w).trans hnE_nd)
            exact Nat.add_le_add_right ((countWord_len_le_succ _).trans (by omega)) 1
        · simp only [routedL, List.length_map, List.length_range]
          exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hdeg0) 1
      let cap0 := (2 * (100 * N + 2) + 2) * (3 * N) + M_elt + 2
      have henc : (Encoding.encodeList id [countWord v₀.val,
          Encoding.encodeList (fun r : Bool × ℕ => r.1 :: countWord r.2) routedL]).length ≤ (2 * cap0 + 2) * 2 + 1 := by
        apply length_encodeList_le id _ cap0
        intro u hu
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with rfl | rfl
        · exact (countWord_len_le_succ v₀.val).trans (by dsimp [cap0]; omega)
        · dsimp [cap0]; omega
      dsimp [cap0, routedL] at henc
      nlinarith [henc, hN_M, hM1]
    | pkt dCreate pCreate origDeg rawDesc hdLt hpLe entry₀ hpkt permOpt hperm =>
      obtain ⟨hraw_le, horig_le⟩ := hpkt_bounds hpLe hpkt
      cases permOpt with
      | none =>
        dsimp only [SoloVert.toVertexSpec, VertexSpec.bits]
        simp only [List.length_cons]
        have hp_len : (pack [rawDesc, []]).length ≤ (2 * M_elt + 2) * 2 + 1 := by
          apply pack_len_le _ M_elt
          intro u hu
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
          rcases hu with rfl | rfl
          · exact hraw_le
          · simp
        nlinarith [hp_len, hM1]
      | some pm =>
        dsimp only [SoloVert.toVertexSpec, VertexSpec.bits]
        simp only [List.length_cons]
        have hpm_enc : (encodeNatListBin pm).length ≤ (2 * (N + 1) + 2) * M_elt + 1 := by
          refine (encodeNatListBin_len_le pm (N + 1) ?_).trans ?_
          · intro m hm
            obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.mp hm
            have hi : idx < origDeg := hperm.1 ▸ hidx
            have hlt : pm[idx]'hidx < nd.G.deg w := by
              simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx] using hperm.2 ⟨idx, hi⟩
            exact (countWord_len_le_succ _).trans (Nat.add_le_add_right (hlt.le.trans ((deg_le_nE nd.G w).trans hnE_nd)) 1)
          · exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (hperm.1.le.trans horig_le)) 1
        let cap_p := (2 * (N + 1) + 2) * M_elt + M_elt + 1
        have hp_len : (pack [rawDesc, encodeNatListBin pm]).length ≤ (2 * cap_p + 2) * 2 + 1 := by
          apply pack_len_le _ cap_p
          intro u hu
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
          rcases hu with rfl | rfl <;> (dsimp [cap_p]; omega)
        dsimp [cap_p] at hp_len
        nlinarith [hp_len, hN_M, hM1]
  have hspec_len : NodePortsBounded x.S nd → ∀ w : Fin nd.G.nV,
      (nd.verts w).specBits.length ≤ 4096 * M_elt ^ 2 := by
    intro hpb w
    have hpb_w := hpb w
    cases hsv : nd.verts w with
    | orig v₀ hv₀ pinPort portMap hlen hports =>
      rw [hsv] at hpb_w
      dsimp only [SoloVert.specBits]
      have hv0_M : v₀.val ≤ M_elt := v₀.isLt.le.trans hxV_M
      have hdeg0 : x.G.deg v₀ ≤ 3 * N := (deg_le_nE x.G v₀).trans hne_N
      have hpc : SoloVert.pinCode pinPort ≤ 3 * N + 1 := by
        cases pinPort with
        | none => simp [SoloVert.pinCode]
        | some r => simp only [SoloVert.pinCode, Option.elim_some]; have := r.isLt; omega
      have hmeta : (encodeNatListBin [v₀.val, x.G.deg v₀, SoloVert.pinCode pinPort]).length ≤
          (2 * (M_elt + 3 * N + 2) + 2) * 3 + 1 := by
        apply encodeNatListBin_len_le _ (M_elt + 3 * N + 2)
        intro m hm
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl | rfl <;> exact (countWord_len_le_succ _).trans (by omega)
      have hpm : (encodeNatListBin portMap).length ≤ (2 * (N + 1) + 2) * (3 * N) + 1 := by
        refine (encodeNatListBin_len_le portMap (N + 1) ?_).trans ?_
        · intro m hm
          have hmS := (hpb_w m hm).trans hxS_N
          exact (countWord_len_le_succ m).trans (by omega)
        · rw [hlen]; exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hdeg0) 1
      let cap_s := (2 * (M_elt + 3 * N + 2) + 2) * 3 + (2 * (N + 1) + 2) * (3 * N) + 2
      have hpk : (pack [[false], encodeNatListBin [v₀.val, x.G.deg v₀, SoloVert.pinCode pinPort],
          encodeNatListBin portMap]).length ≤ (2 * cap_s + 2) * 3 + 1 := by
        apply pack_len_le _ cap_s
        intro u hu
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with rfl | rfl | rfl
        · simp [cap_s]
        · dsimp [cap_s]; omega
        · dsimp [cap_s]; omega
      dsimp [cap_s] at hpk
      nlinarith [hpk, hN_M, hM1]
    | pkt dCreate pCreate origDeg rawDesc hdLt hpLe entry₀ hpkt permOpt hperm =>
      rw [hsv] at hpb_w
      obtain ⟨hraw_le, horig_le⟩ := hpkt_bounds hpLe hpkt
      cases permOpt with
      | none =>
        dsimp only [SoloVert.specBits]
        have hpk : (pack [[true], rawDesc]).length ≤ (2 * M_elt + 2) * 2 + 1 := by
          apply pack_len_le _ M_elt
          intro u hu
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
          rcases hu with rfl | rfl
          · simp; exact hM1
          · exact hraw_le
        nlinarith [hpk, hM1]
      | some pm =>
        dsimp only [SoloVert.specBits]
        have hpm_enc : (encodeNatListBin pm).length ≤ (2 * (N + 1) + 2) * M_elt + 1 := by
          refine (encodeNatListBin_len_le pm (N + 1) ?_).trans ?_
          · intro m hm
            have hmS := (hpb_w m hm).trans hxS_N
            exact (countWord_len_le_succ m).trans (by omega)
          · exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (hperm.1.le.trans horig_le)) 1
        let cap_p := (2 * (N + 1) + 2) * M_elt + M_elt + 1
        have hpk : (pack [[true], rawDesc, encodeNatListBin pm]).length ≤ (2 * cap_p + 2) * 3 + 1 := by
          apply pack_len_le _ cap_p
          intro u hu
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
          rcases hu with rfl | rfl | rfl
          · simp [cap_p]
          · dsimp [cap_p]; omega
          · dsimp [cap_p]; omega
        dsimp [cap_p] at hpk
        nlinarith [hpk, hN_M, hM1]
  have htbl_len : nd.toStoppedSpec.tableBits.length ≤ 262144 * M_elt ^ 3 := by
    unfold StoppedSpec.tableBits
    have hlen1 : (Encoding.encodeList VertexSpec.bits (List.ofFn nd.toStoppedSpec.vTable)).length ≤
        (2 * (4096 * M_elt ^ 2) + 2) * nd.G.nV + 1 := by
      refine (length_encodeList_le VertexSpec.bits _ (4096 * M_elt ^ 2) ?_).trans_eq (by simp)
      intro vs hvs
      obtain ⟨w, rfl⟩ := List.mem_ofFn.mp hvs
      exact hvs_len w
    nlinarith [hlen1, hnV_M, hM1]
  refine ⟨htbl_len, fun hpb => ?_⟩
  have hG_len : nd.G.encode.length ≤ 512 * M_elt ^ 2 := by
    have hb : nd.G.nV + nd.G.nE + 2 ≤ 4 * M_elt := by omega
    calc nd.G.encode.length ≤ 32 * (nd.G.nV + nd.G.nE + 2) ^ 2 := graph_encode_len_le nd.G
      _ ≤ 32 * (4 * M_elt) ^ 2 := Nat.mul_le_mul_left 32 (Nat.pow_le_pow_left hb 2)
      _ = 512 * M_elt ^ 2 := by ring
  have hpins_bits_len : (pack (nd.pins.map fun pv => encodeNatListBin [pv.1.val, pv.2.val])).length ≤
      8192 * M_elt ^ 2 := by
    have hel : ∀ w_p ∈ nd.pins.map (fun pv => encodeNatListBin [pv.1.val, pv.2.val]),
        w_p.length ≤ (2 * (2 * M_elt + 2) + 2) * 2 + 1 := by
      intro w_p hwp
      obtain ⟨pv, _, rfl⟩ := List.mem_map.mp hwp
      apply encodeNatListBin_len_le _ (2 * M_elt + 2)
      intro m hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl
      · have hbi : pv.1.val < 2 * N := pv.1.isLt.trans_le hmk_N
        exact (countWord_len_le_succ _).trans (by omega)
      · have hwv : pv.2.val < M_elt := pv.2.isLt.trans_le hnV_M
        exact (countWord_len_le_succ _).trans (by omega)
    have hpk := pack_len_le _ ((2 * (2 * M_elt + 2) + 2) * 2 + 1) hel
    rw [List.length_map] at hpk
    have hpl : nd.pins.length ≤ 100 * M_elt := hpins_len.trans (Nat.mul_le_mul_left _ hN_M)
    have hpk' := hpk.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hpl) 1)
    nlinarith [hpk', hM1]
  have hvSpecs_len : (pack (List.ofFn fun w => (nd.verts w).specBits)).length ≤ 16384 * M_elt ^ 3 := by
    have hpk : (pack (List.ofFn fun w => (nd.verts w).specBits)).length ≤
        (2 * (4096 * M_elt ^ 2) + 2) * nd.G.nV + 1 := by
      refine (pack_len_le _ (4096 * M_elt ^ 2) ?_).trans_eq (by simp)
      intro sp hsp
      obtain ⟨w, rfl⟩ := List.mem_ofFn.mp hsp
      exact hspec_len hpb w
    nlinarith [hpk, hnV_M, hM1]
  let cap_wi := 16384 * M_elt ^ 3
  have hwi_len : nd.toWorkItem.bits.length ≤ (2 * cap_wi + 2) * 5 + 1 := by
    unfold SoloNode.toWorkItem WorkItem.bits
    simp only [List.map_map, Function.comp_def]
    apply length_encodeList_le id _ cap_wi
    intro w_f hwf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hwf
    rcases hwf with rfl | rfl | rfl | rfl | rfl
    · exact (countWord_len_le_succ nd.d).trans (by dsimp [cap_wi]; nlinarith [hd_N, hN_M, hM1])
    · dsimp [cap_wi]; nlinarith [hG_len, hM1]
    · exact (countWord_len_le_succ nd.pCurr).trans (by dsimp [cap_wi]; nlinarith [hpCurr_M2, hM1])
    · change (pack (nd.pins.map fun pv => encodeNatListBin [pv.1.val, pv.2.val])).length ≤ cap_wi
      dsimp [cap_wi]; nlinarith [hpins_bits_len, hM1]
    · change (pack (List.ofFn fun w => (nd.verts w).specBits)).length ≤ cap_wi
      dsimp [cap_wi]; nlinarith [hvSpecs_len, hM1]
  dsimp [cap_wi] at hwi_len
  nlinarith [hwi_len, hM1]

/-- Every `SoloNode` with `nd.d ≤ D` has `toStoppedSpec.tableBits.length` polynomially bounded in `size x`,
    and if `NodePortsBounded x.S nd`, also `nd.toWorkItem.bits.length` polynomially bounded in `size x`. -/
theorem soloNode_table_and_work_len {C c : ℕ} (K_loc : ℕ) :
    ∃ K_wi : ℕ, 1 ≤ K_wi ∧
      ∀ (x : Input C c) {f : ℤ[X]} (hf : f.Monic)
        (E_pkt : PrimitiveMachine) (o_pkt : Fin E_pkt.tapeCount)
        (nd : SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)),
        nd.d ≤ Nat.clog 32 (4 * x.m) →
        nd.toStoppedSpec.tableBits.length ≤ K_wi * (size x + 1) ^ K_wi ∧
        (NodePortsBounded x.S nd → nd.toWorkItem.bits.length ≤ K_wi * (size x + 1) ^ K_wi) := by
  let e_v := (c + 2) * (K_loc + 2)
  let C0 := 8 * (K_loc + 2) * (700 * (C + 2)) ^ (K_loc + 1)
  let K_wi := 262144 * C0 ^ 3 + 3 * e_v + 16
  have hK_pos : 1 ≤ K_wi :=
    Nat.le_trans (by decide : 1 ≤ 16) (Nat.le_add_left 16 _)
  refine ⟨K_wi, hK_pos, ?_⟩
  intro x f hf E_pkt o_pkt nd hd_le
  obtain ⟨hmk, hne_x, _, _, _, hl_x, hp_x, hS_sz, _⟩ := input_params_le x
  let N := size x + 1
  have hN1 : 1 ≤ N := Nat.succ_pos _
  have hS_pos : 1 ≤ x.S := x.hp.trans x.pS
  have h2L : 2 ^ D3Stopped.level x.S ≤ 2 * x.S := pow2_clog2_le hS_pos
  have h2sh : ∀ j, 2 ^ D3Stopped.shift x.S j ≤ 2 * x.S := fun j =>
    (Nat.pow_le_pow_right (by decide) (shift_le_level_solo x.S j)).trans h2L
  have hD_le : Nat.clog 32 (4 * x.m) ≤ 8 * N := by
    have hcl : Nat.clog 32 (4 * x.m) ≤ Nat.clog 2 (4 * x.m) := by
      rw [Nat.clog_pow_left 2 5 (4 * x.m)]; omega
    exact hcl.trans ((clog2_le_self (4 * x.m)).trans (by dsimp [N]; omega))
  have hd_N : nd.d ≤ 8 * N := hd_le.trans hD_le
  have hnE_nd : nd.G.nE ≤ N := (nd.edges_le.trans (Nat.div_le_self _ _)).trans (by dsimp [N]; omega)
  have hnV_nd : nd.G.nV ≤ 25 * N ^ (c + 2) := by
    have hxV : x.G.nV ≤ N ^ (c + 2) := x.nV.trans (Nat.pow_le_pow_right hN1 (by omega))
    have hdS : nd.d * (3 * x.S) ≤ 24 * N ^ 2 := by
      calc nd.d * (3 * x.S) ≤ (8 * N) * (3 * N) := Nat.mul_le_mul hd_N (by dsimp [N]; omega)
        _ = 24 * N ^ 2 := by ring
    have hN2 : N ^ 2 ≤ N ^ (c + 2) := Nat.pow_le_pow_right hN1 (by omega)
    have h1 := nd.verts_le
    nlinarith
  have hpCurr_le : nd.pCurr ≤ 161 * N ^ 2 := by
    have hif : (if nd.d = 0 then 0 else 80 * x.S * 2 ^ D3Stopped.shift x.S (nd.d - 1)) ≤ 160 * N ^ 2 := by
      split_ifs
      · exact Nat.zero_le _
      · have hsh := h2sh (nd.d - 1)
        calc 80 * x.S * 2 ^ D3Stopped.shift x.S (nd.d - 1)
            ≤ 80 * N * (2 * N) := Nat.mul_le_mul (by dsimp [N]; omega) (hsh.trans (by dsimp [N]; omega))
          _ = 160 * N ^ 2 := by ring
    have hxp_N2 : x.p ≤ N ^ 2 := by
      have hN2 : N ≤ N ^ 2 := by nlinarith
      exact (hp_x.trans (hS_sz.trans (Nat.le_succ _))).trans hN2
    exact nd.hp_le.trans ((Nat.add_le_add hxp_N2 hif).trans_eq (by ring))
  have hpins_len : nd.pins.length ≤ 100 * N := by
    have hdiv : (4 * x.m * x.k) / 32 ^ nd.d ≤ 2 * N :=
      (Nat.div_le_self _ _).trans (hmk.trans (by dsimp [N]; omega))
    have hlev : D3Stopped.level x.S ≤ N := (clog2_le_self x.S).trans (by dsimp [N]; omega)
    have h1 := nd.pins_len_le
    dsimp [N] at hN1; omega
  let V_bnd := 350 * (C + 2) * N ^ (c + 2)
  have hN_le_Nc2 : N ≤ N ^ (c + 2) := by
    calc N = N ^ 1 := (pow_one N).symm
      _ ≤ N ^ (c + 2) := Nat.pow_le_pow_right hN1 (by omega)
  have hN2_le_Nc2 : N ^ 2 ≤ N ^ (c + 2) := Nat.pow_le_pow_right hN1 (by omega)
  have hV_ge_N : N ≤ V_bnd := by
    calc N ≤ 1 * N ^ (c + 2) := by rw [one_mul]; exact hN_le_Nc2
      _ ≤ 350 * (C + 2) * N ^ (c + 2) := Nat.mul_le_mul_right _ (by omega)
  have hn0_le : ∀ pCreate ≤ nd.pCurr, pCreate + 4 * D3Stopped.level x.S + x.l + 2 ≤ V_bnd := by
    intro pCreate hpCr
    have hlev : D3Stopped.level x.S ≤ N := (clog2_le_self x.S).trans (by dsimp [N]; omega)
    have hl_N : x.l ≤ 2 * C * N := hl_x.trans (Nat.mul_le_mul_left _ (by dsimp [N]; omega))
    have : pCreate + 4 * D3Stopped.level x.S + x.l + 2 ≤ 170 * (C + 2) * N ^ 2 := by
      nlinarith [hpCr, hpCurr_le, hN1]
    exact this.trans (by
      calc 170 * (C + 2) * N ^ 2 ≤ 350 * (C + 2) * N ^ 2 := Nat.mul_le_mul_right _ (by omega)
        _ ≤ 350 * (C + 2) * N ^ (c + 2) := Nat.mul_le_mul_left _ hN2_le_Nc2)
  let PB := K_loc * (V_bnd + 1) ^ K_loc
  let M_elt := 8 * (K_loc + 1) * (2 * V_bnd) ^ (K_loc + 1)
  have hPB_le_M : PB ≤ M_elt ∧ V_bnd ≤ M_elt := by
    have hV1 : 1 ≤ V_bnd := hN1.trans hV_ge_N
    have h2V : V_bnd + 1 ≤ 2 * V_bnd := by omega
    have hp1 : (V_bnd + 1) ^ K_loc ≤ (2 * V_bnd) ^ (K_loc + 1) :=
      (Nat.pow_le_pow_left h2V K_loc).trans (Nat.pow_le_pow_right (by omega) (Nat.le_succ K_loc))
    have h1 : PB ≤ M_elt := by
      dsimp [PB, M_elt]
      calc K_loc * (V_bnd + 1) ^ K_loc
          ≤ 8 * (K_loc + 1) * (V_bnd + 1) ^ K_loc := Nat.mul_le_mul_right _ (by omega)
        _ ≤ 8 * (K_loc + 1) * (2 * V_bnd) ^ (K_loc + 1) := Nat.mul_le_mul_left _ hp1
    have h2 : V_bnd ≤ M_elt := by
      have : 2 * V_bnd ≤ (2 * V_bnd) ^ (K_loc + 1) := by
        calc 2 * V_bnd = (2 * V_bnd) ^ 1 := (pow_one _).symm
          _ ≤ (2 * V_bnd) ^ (K_loc + 1) := Nat.pow_le_pow_right (by omega) (Nat.succ_pos _)
      dsimp [M_elt]
      calc V_bnd ≤ 2 * V_bnd := by omega
        _ ≤ 1 * (2 * V_bnd) ^ (K_loc + 1) := by rw [one_mul]; exact this
        _ ≤ 8 * (K_loc + 1) * (2 * V_bnd) ^ (K_loc + 1) := Nat.mul_le_mul_right _ (by omega)
    exact ⟨h1, h2⟩
  have hM1 : 1 ≤ M_elt := (hN1.trans hV_ge_N).trans hPB_le_M.2
  have hN_M : N ≤ M_elt := hV_ge_N.trans hPB_le_M.2
  have hnV_M : nd.G.nV ≤ M_elt :=
    (hnV_nd.trans (Nat.mul_le_mul_right _ (by omega : 25 ≤ 350 * (C + 2)))).trans hPB_le_M.2
  have hM_bound : 262144 * M_elt ^ 3 ≤ K_wi * N ^ K_wi := by
    have h2V_pow : (2 * V_bnd) ^ (K_loc + 1) = (700 * (C + 2)) ^ (K_loc + 1) * N ^ ((c + 2) * (K_loc + 1)) := by
      dsimp [V_bnd]
      rw [show 2 * (350 * (C + 2) * N ^ (c + 2)) = (700 * (C + 2)) * N ^ (c + 2) from by ring,
          mul_pow, ← pow_mul]
    have hM_le : M_elt ≤ C0 * N ^ e_v := by
      dsimp [M_elt, C0, e_v]
      rw [h2V_pow, ← Nat.mul_assoc]
      refine Nat.mul_le_mul (Nat.mul_le_mul_right _ (by omega))
        (Nat.pow_le_pow_right hN1 (Nat.mul_le_mul_left _ (by omega)))
    have hK_coeff : 262144 * C0 ^ 3 ≤ K_wi :=
      (Nat.le_add_right _ (3 * e_v)).trans (Nat.le_add_right _ 16)
    have hK_exp : 3 * e_v ≤ K_wi :=
      (Nat.le_add_left (3 * e_v) (262144 * C0 ^ 3)).trans (Nat.le_add_right _ 16)
    calc 262144 * M_elt ^ 3
        ≤ 262144 * (C0 * N ^ e_v) ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hM_le 3)
      _ = (262144 * C0 ^ 3) * N ^ (3 * e_v) := by
          rw [mul_pow, ← pow_mul, ← Nat.mul_assoc, Nat.mul_comm e_v 3]
      _ ≤ K_wi * N ^ K_wi := Nat.mul_le_mul hK_coeff (Nat.pow_le_pow_right hN1 hK_exp)
  have hpb_le_PB : ∀ pCreate ≤ nd.pCurr,
      polyBound K_loc (pCreate + 4 * D3Stopped.level x.S + x.l + 2) ≤ ((PB : ℕ) : ℝ) := by
    have hpb_mono : ∀ (a b : ℕ), a ≤ b → polyBound K_loc a ≤ ((K_loc * (b + 1) ^ K_loc : ℕ) : ℝ) := by
      intro a b hab
      rw [← polyBound_eq_natCast K_loc b]
      unfold polyBound
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (add_nonneg (Nat.cast_nonneg a) zero_le_one)
          (add_le_add (Nat.cast_le.mpr hab) le_rfl) K_loc)
        (Nat.cast_nonneg K_loc)
    intro pCreate hpCr
    exact hpb_mono _ V_bnd (hn0_le pCreate hpCr)
  have hpkt_bounds : ∀ {dCr pCr oDeg : ℕ} {rDesc : Bits} {ent₀ : (Fin oDeg → Bool) → B f x.l pCr},
      pCr ≤ nd.pCurr →
      pktOKOf E_pkt o_pkt K_loc x f hf dCr pCr oDeg rDesc ent₀ →
      rDesc.length ≤ M_elt ∧ oDeg ≤ M_elt := by
    intro dCr pCr oDeg rDesc ent₀ hpCr hpkt
    have hpb_m := hpb_le_PB pCr hpCr
    have hr : rDesc.length ≤ PB := (Nat.cast_le (α := ℝ)).mp (hpkt.2.2.2.1.trans hpb_m)
    have ho : oDeg ≤ PB := (Nat.cast_le (α := ℝ)).mp ((pkt_origDeg_le hpkt).trans hpb_m)
    exact ⟨hr.trans hPB_le_M.1, ho.trans hPB_le_M.1⟩
  have hxV_M : x.G.nV ≤ M_elt := by
    have : x.G.nV ≤ N ^ (c + 2) := x.nV.trans (Nat.pow_le_pow_right hN1 (by omega))
    exact (this.trans (Nat.le_mul_of_pos_left _ (by omega : 0 < 350 * (C + 2)))).trans hPB_le_M.2
  have hpCurr_M2 : nd.pCurr ≤ 161 * M_elt ^ 2 :=
    hpCurr_le.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hN_M 2))
  have hxS_N : x.S ≤ N := hS_sz.trans (Nat.le_succ _)
  have hmk_N : 4 * x.m * x.k ≤ 2 * N := hmk.trans (Nat.mul_le_mul_left 2 hxS_N)
  have hne_N : x.G.nE ≤ 3 * N := hne_x.trans (Nat.mul_le_mul_left 3 hxS_N)
  have hboth := node_len_from_M nd N M_elt hM1 hN_M hxS_N hmk_N hne_N hxV_M hd_N hnE_nd hnV_M hpCurr_M2 hpins_len hpkt_bounds
  exact ⟨hboth.1.trans hM_bound, fun hpb => (hboth.2 hpb).trans hM_bound⟩

private theorem allPortsBounded_dite {C c : ℕ} {x : Input C c} {f : ℤ[X]} {hf : f.Monic}
    {M_node E_pkt : PrimitiveMachine} {o_node : Fin M_node.tapeCount} {o_pkt : Fin E_pkt.tapeCount}
    {K_loc H_loc c_loc k : ℕ} {nd : SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)}
    {P : Prop} [Decidable P]
    (t : P → SoloUnroll x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc (k + 1) nd)
    (e : ¬P → SoloUnroll x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc (k + 1) nd)
    (ht : ∀ h, SoloUnrollAllPortsBounded (k + 1) nd (t h))
    (he : ∀ h, SoloUnrollAllPortsBounded (k + 1) nd (e h)) :
    SoloUnrollAllPortsBounded (k + 1) nd (if h : P then t h else e h) := by
  split_ifs with h
  · exact ht h
  · exact he h

theorem buildSoloUnroll_portsBounded {C c : ℕ} (x : Input C c) {f : ℤ[X]} (hf : f.Monic) (hRing : RingOK f)
    (hdeg_f : f.natDegree = 4 * D3Stopped.level x.S)
    (M_node E_pkt : PrimitiveMachine) (o_node : Fin M_node.tapeCount) (o_pkt : Fin E_pkt.tapeCount)
    (K_loc H_loc c_loc : ℕ)
    (hLocal : ∀ (G : Graph) (a u p l b τ : ℕ) (host : Fin b → Fin G.nV) (f' : ℤ[X]) (hf' : f'.Monic),
      1 ≤ u → (hu : u ≤ a) → u ≤ G.nE → 1 ≤ l → 1 ≤ p → RingOK f' → points G.nE a ≤ 2 ^ f'.natDegree →
      2 ^ a * 64 ^ (2 * a) ≤ G.nE → (a + 2) * 64 ^ (4 * a) * max 1 G.maxDeg ≤ G.nE → 1 ≤ τ →
      (∀ z, (Finset.univ.filter fun y => host z = host y).card ≤ τ) →
      ∃ (lbl : Label a G) (s : Step lbl hu f' l p) (order : Fin (Fintype.card (Branch s)) ≃ Branch s),
        let n := G.nE + p + f'.natDegree + l + 2
        let bound (j : ℕ) := polyBound H_loc (D4NodeQuery.request G host a u p l f' j).length +
          polyBound K_loc (n + (stepInput G a u p l f' lbl).length) + c_loc
        D2.Balanced host τ lbl ∧ Padded lbl ∧ s.sound hf' ∧
        (∀ t, ((s.modes t).count : ℝ) ≤ Real.exp ((K_loc : ℝ) * Real.sqrt
          ((G.nE : ℝ) * (p + increase G.nE a u (AppendixD4.level t.val)) / tileScale a (AppendixD4.level t.val)))) ∧
        RunsWithin M_node o_node (D4NodeQuery.request G host a u p l f' 0)
          (countWord (Fintype.card (Branch s))) (bound 0) (bound 0) ∧
        (∀ j, RunsWithin M_node o_node (D4NodeQuery.request G host a u p l f' (j.val + 1))
          (s.bits hf' (order j)) (bound (j.val + 1)) (bound (j.val + 1))) ∧
        ∀ t k β g r α, let z := s.child t k β g
          RunsWithin E_pkt o_pkt (Encoding.encodeList id [z.descriptor r, List.ofFn α])
            (residue f' l _ hf' (z.entry r α))
            (Real.exp ((K_loc : ℝ) * (2 ^ a : ℕ) * Real.log n)) (polyBound K_loc n))
    (L₀_act : ℕ)
    (hact_all : ∀ (d M Δ p : ℕ),
      L₀_act ≤ D3Stopped.level x.S → D3Stopped.threshold x.S < M → M ≤ x.S / 8 ^ d →
      let a := D3Stopped.shift x.S d; let u := D3Stopped.width x.S d
      let last := if d = 0 then 0 else D3Stopped.shift x.S (d - 1)
      Δ ≤ max (C * Nat.ceil ((x.b : ℝ) ^ ((3 : ℝ) / 4))) (2 * 2 ^ last) →
      p ≤ x.p + 80 * x.S * 2 ^ last →
      1 ≤ u ∧ u ≤ a ∧ u ≤ M ∧ 1 ≤ x.l ∧ points M a ≤ 2 ^ (4 * D3Stopped.level x.S) ∧
      2 ^ a * 64 ^ (2 * a) ≤ M ∧ (a + 2) * 64 ^ (4 * a) * max 1 Δ ≤ M ∧
      max Δ (2 * 2 ^ a) ≤ D3Stopped.cap x.S ∧
      (∀ i < u, p + increase M a u i ≤ 64 * M * tileScale a i / u) ∧
      ∀ i, p + increase M a u i ≤ x.p + 80 * x.S * 2 ^ a)
    (hL : L₀_act ≤ D3Stopped.level x.S) :
    ∀ (k : ℕ) (nd : SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf))
      (hk : nd.d + k = Nat.clog 32 (4 * x.m)), NodePortsBounded x.S nd →
      SoloUnrollAllPortsBounded k nd
        (buildSoloUnroll x hf hRing hdeg_f M_node E_pkt o_node o_pkt K_loc H_loc c_loc hLocal L₀_act hact_all hL k nd hk)
  | 0, _, _, hpb => hpb
  | k + 1, nd, hk, hpb => by
    unfold buildSoloUnroll
    refine allPortsBounded_dite _ _ (fun hM => ?_) (fun _ => hpb)
    exact ⟨hpb, fun ν g => buildSoloUnroll_portsBounded x hf hRing hdeg_f M_node E_pkt o_node o_pkt K_loc H_loc c_loc
      hLocal L₀_act hact_all hL k _ _ (childSoloNode_portsBounded _ ν g)⟩

end
end DetDLP.M14BoundsInternal

open DetDLP.M14BoundsInternal in
theorem solution :
    (∀ n : ℕ, (countWord n).length ≤ n + 1) ∧
    (∀ {a m : ℕ}, a ≤ 2 ^ m → (countWord a).length ≤ m + 1) ∧
    (∀ (ns : List ℕ) (b : ℕ), (∀ n ∈ ns, (countWord n).length ≤ b) →
      (encodeNatListBin ns).length ≤ (2 * b + 2) * ns.length + 1) ∧
    (∀ (ws : List Wd) (b : ℕ), (∀ w ∈ ws, w.length ≤ b) →
      (pack ws).length ≤ (2 * b + 2) * ws.length + 1) ∧
    (∀ G : BipartiteMultigraph, G.encode.length ≤ 32 * (G.nV + G.nE + 2) ^ 2) ∧
    (∀ (f : ℤ[X]) (l q : ℕ) (hf : f.Monic) (z : B f l q),
      (residue f l q hf z).length ≤ (2 * (q + 1) + 2) * (l * f.natDegree) + 1) ∧
    (∀ K u : ℕ, polyBound K u = ((K * (u + 1) ^ K : ℕ) : ℝ)) ∧
    (∀ S j : ℕ, D3Stopped.shift S j ≤ D3Stopped.level S / 32768) ∧
    (∀ {C c : ℕ} (x : Input C c),
      4 * x.m * x.k ≤ 2 * x.S ∧ x.G.nE ≤ 3 * x.S ∧ x.m ≤ 2 * x.S ∧ x.k ≤ 2 * x.S ∧
      x.b ≤ 2 * C * x.S ∧ x.l ≤ 2 * C * x.S ∧ x.p ≤ x.S ∧ x.S ≤ size x ∧ x.desc.length ≤ size x) ∧
    (∀ {C c : ℕ}, 0 < c → ∃ K_in : ℕ, 1 ≤ K_in ∧ ∀ x : Input C c,
      (D4Plan.input x).length ≤ K_in * (size x + 1) ^ K_in) ∧
    (∀ {C c : ℕ} (x : Input C c) (K_B : ℕ), C + 6 ≤ D3Stopped.level x.S →
      (K_B : ℝ) * (x.S : ℝ) / Real.sqrt (D3Stopped.level x.S : ℝ) ≤
        ((9 * (C + 1) ^ 3 * K_B : ℕ) : ℝ) * ((x.b : ℝ) / (x.m : ℝ))) ∧
    (∀ {C c : ℕ} (x : Input C c) {f : ℤ[X]} (hf : f.Monic)
      (M_node E_pkt : PrimitiveMachine) (o_node : Fin M_node.tapeCount) (o_pkt : Fin E_pkt.tapeCount)
      (K_loc H_loc c_loc guard : ℕ),
      let D := Nat.clog 32 (4 * x.m)
      ∀ (fuel : ℕ)
        (todo : List (WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc))
        (done : List (SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)))
        (accVal : B f x.l (guard + x.p)) (lossSum : ℕ),
        (∀ it ∈ todo, it.2.1.d + it.1 = D) →
        (∀ m ∈ done, m.d ≤ D) →
        treeAll (fun lf => ∀ m ∈ lf.doneNodes, m.d ≤ D)
          (unrollCertFuel x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc guard fuel todo done accVal lossSum)) ∧
    (∀ {C c : ℕ} (hC : 0 < C) (x : Input C c) {f : ℤ[X]} {PktOK : PktPred f x.l}
      (nd : SoloNode x f PktOK),
      max 6 (DetDLP.d4_active_node_preconditions C hC).choose ≤ D3Stopped.level x.S →
      nd.G.maxDeg ≤ D3Stopped.cap x.S) ∧
    (∀ {E_pkt : PrimitiveMachine} {oe : Fin E_pkt.tapeCount} {K_loc C c : ℕ}
      {x : Input C c} {f : ℤ[X]} {hf : f.Monic}
      {dCreate pCreate origDeg : ℕ} {rawDesc : Bits} {entry₀ : (Fin origDeg → Bool) → B f x.l pCreate},
      pktOKOf E_pkt oe K_loc x f hf dCreate pCreate origDeg rawDesc entry₀ →
      (origDeg : ℝ) ≤ polyBound K_loc (pCreate + 4 * D3Stopped.level x.S + x.l + 2)) ∧
    (∀ {C c : ℕ} (x : Input C c) (f : ℤ[X]) (PktOK : PktPred f x.l),
      NodePortsBounded x.S (rootSoloNode x f PktOK)) ∧
    (∀ {C c : ℕ} (K_loc : ℕ), ∃ K_wi : ℕ, 1 ≤ K_wi ∧
      ∀ (x : Input C c) {f : ℤ[X]} (hf : f.Monic)
        (E_pkt : PrimitiveMachine) (o_pkt : Fin E_pkt.tapeCount)
        (nd : SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)),
        nd.d ≤ Nat.clog 32 (4 * x.m) →
        nd.toStoppedSpec.tableBits.length ≤ K_wi * (size x + 1) ^ K_wi ∧
        (NodePortsBounded x.S nd → nd.toWorkItem.bits.length ≤ K_wi * (size x + 1) ^ K_wi)) ∧
    (∀ {C c : ℕ} (x : Input C c) {f : ℤ[X]} (hf : f.Monic) (hRing : RingOK f)
      (hdeg_f : f.natDegree = 4 * D3Stopped.level x.S)
      (M_node E_pkt : PrimitiveMachine) (o_node : Fin M_node.tapeCount) (o_pkt : Fin E_pkt.tapeCount)
      (K_loc H_loc c_loc : ℕ)
      (hLocal : ∀ (G : Graph) (a u p l b τ : ℕ) (host : Fin b → Fin G.nV) (f' : ℤ[X]) (hf' : f'.Monic),
        1 ≤ u → (hu : u ≤ a) → u ≤ G.nE → 1 ≤ l → 1 ≤ p → RingOK f' → points G.nE a ≤ 2 ^ f'.natDegree →
        2 ^ a * 64 ^ (2 * a) ≤ G.nE → (a + 2) * 64 ^ (4 * a) * max 1 G.maxDeg ≤ G.nE → 1 ≤ τ →
        (∀ z, (Finset.univ.filter fun y => host z = host y).card ≤ τ) →
        ∃ (lbl : Label a G) (s : Step lbl hu f' l p) (order : Fin (Fintype.card (Branch s)) ≃ Branch s),
          let n := G.nE + p + f'.natDegree + l + 2
          let bound (j : ℕ) := polyBound H_loc (D4NodeQuery.request G host a u p l f' j).length +
            polyBound K_loc (n + (stepInput G a u p l f' lbl).length) + c_loc
          D2.Balanced host τ lbl ∧ Padded lbl ∧ s.sound hf' ∧
          (∀ t, ((s.modes t).count : ℝ) ≤ Real.exp ((K_loc : ℝ) * Real.sqrt
            ((G.nE : ℝ) * (p + increase G.nE a u (AppendixD4.level t.val)) / tileScale a (AppendixD4.level t.val)))) ∧
          RunsWithin M_node o_node (D4NodeQuery.request G host a u p l f' 0)
            (countWord (Fintype.card (Branch s))) (bound 0) (bound 0) ∧
          (∀ j, RunsWithin M_node o_node (D4NodeQuery.request G host a u p l f' (j.val + 1))
            (s.bits hf' (order j)) (bound (j.val + 1)) (bound (j.val + 1))) ∧
          ∀ t k β g r α, let z := s.child t k β g
            RunsWithin E_pkt o_pkt (Encoding.encodeList id [z.descriptor r, List.ofFn α])
              (residue f' l _ hf' (z.entry r α))
              (Real.exp ((K_loc : ℝ) * (2 ^ a : ℕ) * Real.log n)) (polyBound K_loc n))
      (L₀_act : ℕ)
      (hact_all : ∀ (d M Δ p : ℕ),
        L₀_act ≤ D3Stopped.level x.S → D3Stopped.threshold x.S < M → M ≤ x.S / 8 ^ d →
        let a := D3Stopped.shift x.S d; let u := D3Stopped.width x.S d
        let last := if d = 0 then 0 else D3Stopped.shift x.S (d - 1)
        Δ ≤ max (C * Nat.ceil ((x.b : ℝ) ^ ((3 : ℝ) / 4))) (2 * 2 ^ last) →
        p ≤ x.p + 80 * x.S * 2 ^ last →
        1 ≤ u ∧ u ≤ a ∧ u ≤ M ∧ 1 ≤ x.l ∧ points M a ≤ 2 ^ (4 * D3Stopped.level x.S) ∧
        2 ^ a * 64 ^ (2 * a) ≤ M ∧ (a + 2) * 64 ^ (4 * a) * max 1 Δ ≤ M ∧
        max Δ (2 * 2 ^ a) ≤ D3Stopped.cap x.S ∧
        (∀ i < u, p + increase M a u i ≤ 64 * M * tileScale a i / u) ∧
        ∀ i, p + increase M a u i ≤ x.p + 80 * x.S * 2 ^ a)
      (hL : L₀_act ≤ D3Stopped.level x.S)
      (k : ℕ) (nd : SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf))
      (hk : nd.d + k = Nat.clog 32 (4 * x.m)),
      NodePortsBounded x.S nd →
      SoloUnrollAllPortsBounded k nd
        (buildSoloUnroll x hf hRing hdeg_f M_node E_pkt o_node o_pkt K_loc H_loc c_loc hLocal L₀_act hact_all hL k nd hk)) :=
  ⟨@countWord_len_le_succ,
   @countWord_len_of_le_pow,
   @encodeNatListBin_len_le,
   @pack_len_le,
   @graph_encode_len_le,
   @residue_len_le,
   @polyBound_eq_natCast,
   @shift_le_level_div_32768,
   @input_params_le,
   @input_len_le_poly,
   @source_rate_le_plan_rate,
   @unrollCertFuel_done_depth_le,
   @cap_bound_of_active_pre,
   @pkt_origDeg_le,
   @rootSoloNode_portsBounded,
   @soloNode_table_and_work_len,
   @buildSoloUnroll_portsBounded⟩
