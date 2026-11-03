-- Prove2me | solution 1 for FlowJobHardness.FlowShopGap.lemma_2_4
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T22:24:31.030971+00:00
-- url     : https://prove2.me/submissions/a09df8c9-2adc-49ff-8118-219e8f2c5368

import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_FlowJobHardness_FlowShopGap_Construction
import Definitions.Def_FlowJobHardness_FlowShopGap_GoodOps

open JobShopLTAS.Core
open FlowJobHardness.FlowShopGap

namespace Lemma24Proof

private lemma mul_add_inj {d a b r1 r2 : ℕ} (hr1 : r1 < d) (hr2 : r2 < d)
    (h : a * d + r1 = b * d + r2) : a = b ∧ r1 = r2 := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · have h1 : (a + 1) * d ≤ b * d := Nat.mul_le_mul_right d hab
    rw [Nat.add_mul, Nat.one_mul] at h1
    omega
  · exact ⟨rfl, by omega⟩
  · have h1 : (b + 1) * d ≤ a * d := Nat.mul_le_mul_right d hba
    rw [Nat.add_mul, Nat.one_mul] at h1
    omega

private lemma div_mod_of_eq_mul_add {d p m rem : ℕ} (hrem : rem < d) (hp : p = m * d + rem) :
    p / d = m ∧ p % d = rem := by
  have hd_pos : 0 < d := by omega
  have h1 : (p / d) * d + p % d = m * d + rem := by
    rw [Nat.mul_comm (p / d) d, Nat.div_add_mod, hp]
  exact mul_add_inj (Nat.mod_lt p hd_pos) hrem h1

private lemma div_lt_of_lt_mul_right {p M d : ℕ} (hp : p < M * d) : p / d < M := by
  rcases Nat.eq_zero_or_pos d with rfl | hd_pos
  · simp at hp
  · by_contra hge
    have hle : M ≤ p / d := le_of_not_gt hge
    have h1 : M * d ≤ (p / d) * d := Nat.mul_le_mul_right d hle
    have h2 : (p / d) * d + p % d = p := by rw [Nat.mul_comm, Nat.div_add_mod]
    omega

private lemma pos_of_fin_size {r d : ℕ} (x : Fin (size r d)) :
    0 < d ∧ 0 < r ^ (2 * d) ∧ 0 < r := by
  have h_size : 0 < size r d := by have := x.isLt; omega
  have hd_pos : 0 < d := by
    unfold size at h_size
    exact Nat.pos_of_mul_pos_left h_size
  have hR_pos : 0 < r ^ (2 * d) := by
    unfold size at h_size
    exact Nat.pos_of_mul_pos_right h_size
  have hr_pos : 0 < r := by
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · have h2d : 2 * d ≠ 0 := by omega
      rw [zero_pow h2d] at hR_pos
      omega
    · exact hr
  exact ⟨hd_pos, hR_pos, hr_pos⟩

private lemma jobFreq_bounds {r d : ℕ} (q : Fin (size r d)) :
    1 ≤ jobFreq r d q.val ∧ jobFreq r d q.val ≤ d := by
  have hq : q.val < d * r ^ (2 * d) := by
    rw [Nat.mul_comm]
    exact q.isLt
  have hdiv : q.val / r ^ (2 * d) < d := div_lt_of_lt_mul_right hq
  unfold jobFreq
  exact ⟨Nat.le_add_left 1 _, hdiv⟩

private lemma isLongOp_iff_isLongPair {r d : ℕ} (hr : 1 ≤ r) (q i : Fin (size r d)) :
    IsLongOp r d ⟨q, i⟩ ↔ IsLongPair r d q.val i.val := by
  unfold IsLongOp Instance.proc inst procTime
  dsimp
  split_ifs with h
  · refine ⟨fun _ => h, fun _ => ?_⟩
    have hr_pos : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
    exact pow_pos hr_pos _
  · exact ⟨fun h0 => (lt_irrefl (0 : ℝ) h0).elim, fun h' => (h h').elim⟩

private lemma schedule_step_aux {r d : ℕ} {s : (inst r d).Op → ℝ}
    (hs : (inst r d).IsFeasibleSchedule Finset.univ s)
    (q : Fin (size r d)) (m : ℕ) :
    ∀ (i i' : Fin (size r d)), i.val + 1 + m = i'.val →
      s ⟨q, i⟩ + (inst r d).proc ⟨q, i⟩ ≤ s ⟨q, i'⟩ := by
  induction m with
  | zero =>
    intro i i' h
    rw [Nat.add_zero] at h
    exact hs.precedence q (Finset.mem_univ q) i i' h
  | succ m ih =>
    intro i i' h
    let mid : Fin (size r d) := ⟨i.val + 1 + m, by have := i'.isLt; omega⟩
    have h1 : s ⟨q, i⟩ + (inst r d).proc ⟨q, i⟩ ≤ s ⟨q, mid⟩ := ih i mid rfl
    have h2 : s ⟨q, mid⟩ + (inst r d).p q mid ≤ s ⟨q, i'⟩ :=
      hs.precedence q (Finset.mem_univ q) mid i' h
    have h3 : 0 ≤ (inst r d).p q mid := (inst r d).p_nonneg q mid
    linarith

private lemma schedule_lt_le {r d : ℕ} {s : (inst r d).Op → ℝ}
    (hs : (inst r d).IsFeasibleSchedule Finset.univ s)
    (q : Fin (size r d)) (i i' : Fin (size r d)) (h : i < i') :
    s ⟨q, i⟩ + (inst r d).proc ⟨q, i⟩ ≤ s ⟨q, i'⟩ := by
  change i.val < i'.val at h
  exact schedule_step_aux hs q (i'.val - (i.val + 1)) i i' (by omega)

private lemma completion_le_makespan {r d : ℕ} {s : (inst r d).Op → ℝ}
    (o : (inst r d).Op) :
    s o + (inst r d).proc o ≤ (inst r d).makespan Finset.univ s := by
  unfold Instance.makespan
  let idx : {x : (inst r d).Op // x.1 ∈ (Finset.univ : Finset (Fin (size r d)))} :=
    ⟨o, Finset.mem_univ o.1⟩
  have hbdd : BddAbove (Set.range (fun x : {x : (inst r d).Op // x.1 ∈ (Finset.univ : Finset (Fin (size r d)))} =>
      s x.1 + (inst r d).proc x.1)) := Set.Finite.bddAbove (Set.toFinite _)
  exact le_ciSup hbdd idx

private lemma goodCount_lower_bound (r d : ℕ) (hr : 8 ≤ r) (s : (inst r d).Op → ℝ)
    (hs : (inst r d).IsFeasibleSchedule Finset.univ s)
    (hmk : (inst r d).makespan Finset.univ s < (r : ℝ) * (r : ℝ) ^ (2 * d))
    (q : Fin (size r d)) :
    (r : ℝ) ^ (2 * jobFreq r d q.val) / 2 ≤ (goodCount r d s q : ℝ) := by
  classical
  have hr1 : 1 ≤ r := by omega
  obtain ⟨hd_pos, hR_pos, hr_pos⟩ := pos_of_fin_size q
  obtain ⟨hf1, hf2⟩ := jobFreq_bounds q
  let f := jobFreq r d q.val
  let N := r ^ (2 * f)
  have hR_split : r ^ (2 * d) = r ^ (2 * (d - f)) * N := by
    dsimp [N]
    rw [← pow_add]
    congr 1
    omega
  have hN_pos : 0 < N := pow_pos hr_pos _
  have hg_lt : jobGroup r d q.val - 1 < r ^ (2 * (d - f)) := by
    have hmod : q.val % r ^ (2 * d) < r ^ (2 * (d - f)) * N := by
      rw [← hR_split]
      exact Nat.mod_lt q.val hR_pos
    have hdiv := div_lt_of_lt_mul_right hmod
    unfold jobGroup
    dsimp [f, N] at hdiv ⊢
    omega
  let c := (jobGroup r d q.val - 1) * N
  have hc_le : c + N ≤ r ^ (2 * d) := by
    have h1 : (jobGroup r d q.val - 1 + 1) * N ≤ r ^ (2 * (d - f)) * N :=
      Nat.mul_le_mul_right _ hg_lt
    rw [Nat.add_mul, Nat.one_mul, ← hR_split] at h1
    exact h1
  let φ : Fin N → Fin (size r d) := fun k =>
    ⟨(c + k.val) * d + (d - f), by
      have hk_lt : c + k.val < r ^ (2 * d) := lt_of_lt_of_le (Nat.add_lt_add_left k.isLt c) hc_le
      have h1 : (c + k.val + 1) * d ≤ r ^ (2 * d) * d := Nat.mul_le_mul_right d hk_lt
      rw [Nat.add_mul, Nat.one_mul] at h1
      unfold size
      omega⟩
  have hφ_div_mod : ∀ k : Fin N,
      (φ k).val / d = c + k.val ∧ (φ k).val % d = d - f := by
    intro k
    exact div_mod_of_eq_mul_add (by omega) rfl
  have hφ_strictMono : StrictMono φ := by
    intro k1 k2 hk
    change (c + k1.val) * d + (d - f) < (c + k2.val) * d + (d - f)
    have hk' : c + k1.val + 1 ≤ c + k2.val := by change k1.val < k2.val at hk; omega
    have h1 : (c + k1.val + 1) * d ≤ (c + k2.val) * d := Nat.mul_le_mul_right d hk'
    rw [Nat.add_mul, Nat.one_mul] at h1
    omega
  have hφ_inj : Function.Injective φ := hφ_strictMono.injective
  have hfilter_long :
      Finset.univ.filter (fun i : Fin (size r d) => IsLongOp r d ⟨q, i⟩) =
        Finset.univ.image φ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      isLongOp_iff_isLongPair hr1]
    constructor
    · rintro ⟨hfreq, hgrp1, hgrp2⟩
      unfold machFreq at hfreq
      unfold machGroup at hgrp1 hgrp2
      have himod : i.val % d < d := Nat.mod_lt i.val hd_pos
      have himod_eq : i.val % d = d - f := by dsimp [f]; omega
      have hidiv_ge : c ≤ i.val / d := by dsimp [c, f, N]; omega
      have hidiv_lt : i.val / d - c < N := by dsimp [c, f, N]; omega
      refine ⟨⟨i.val / d - c, hidiv_lt⟩, ?_⟩
      ext
      dsimp [φ]
      have h_add : c + (i.val / d - c) = i.val / d := by omega
      rw [h_add, ← himod_eq, Nat.mul_comm (i.val / d) d, Nat.div_add_mod]
    · rintro ⟨k, rfl⟩
      obtain ⟨hdiv, hmod⟩ := hφ_div_mod k
      have hk_lt := k.isLt
      refine ⟨?_, ?_, ?_⟩
      · unfold machFreq; rw [hmod]; dsimp [f]; omega
      · unfold machGroup; rw [hdiv]; dsimp [c, f, N]; omega
      · unfold machGroup; rw [hdiv]; dsimp [c, f, N] at hk_lt ⊢; omega
  have hφ_longOp : ∀ k : Fin N, IsLongOp r d ⟨q, φ k⟩ := by
    intro k
    have hk_mem : φ k ∈ Finset.univ.filter (fun i : Fin (size r d) => IsLongOp r d ⟨q, i⟩) := by
      rw [hfilter_long]
      exact Finset.mem_image_of_mem φ (Finset.mem_univ k)
    exact (Finset.mem_filter.mp hk_mem).2
  let D : ℝ := (r : ℝ) ^ 2 / 4 * (r : ℝ) ^ (2 * (d - f))
  have hD_pos : 0 < D := by
    dsimp [D]
    have hr_real : (0 : ℝ) < r := by exact_mod_cast hr_pos
    positivity
  let tSeq : ℕ → ℝ := fun k => if hk : k < N then s ⟨q, φ ⟨k, hk⟩⟩ else 0
  have htSeq_diff_nonneg : ∀ k ∈ Finset.range (N - 1), 0 ≤ tSeq (k + 1) - tSeq k := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hk1 : k < N := by omega
    have hk2 : k + 1 < N := by omega
    dsimp [tSeq]
    rw [dif_pos hk1, dif_pos hk2]
    have hlt : φ ⟨k, hk1⟩ < φ ⟨k + 1, hk2⟩ := hφ_strictMono (show (⟨k, hk1⟩ : Fin N) < ⟨k + 1, hk2⟩ by change k < k + 1; omega)
    have hprec := schedule_lt_le hs q (φ ⟨k, hk1⟩) (φ ⟨k + 1, hk2⟩) hlt
    have hproc_nn : 0 ≤ (inst r d).proc ⟨q, φ ⟨k, hk1⟩⟩ := (inst r d).p_nonneg q (φ ⟨k, hk1⟩)
    linarith
  let isGoodIdx : ℕ → Prop := fun k => if hk : k < N then IsGood r d s ⟨q, φ ⟨k, hk⟩⟩ else False
  have hbad_diff_ge : ∀ k ∈ Finset.range (N - 1), ¬ isGoodIdx k → D ≤ tSeq (k + 1) - tSeq k := by
    intro k hk hnot_good
    rw [Finset.mem_range] at hk
    have hk1 : k < N := by omega
    have hk2 : k + 1 < N := by omega
    dsimp [isGoodIdx] at hnot_good
    rw [dif_pos hk1] at hnot_good
    dsimp [tSeq]
    rw [dif_pos hk1, dif_pos hk2]
    by_contra hlt_D
    apply hnot_good
    refine ⟨hφ_longOp ⟨k, hk1⟩, φ ⟨k + 1, hk2⟩, ?_, hφ_longOp ⟨k + 1, hk2⟩, ?_, ?_⟩
    · exact hφ_strictMono (show (⟨k, hk1⟩ : Fin N) < ⟨k + 1, hk2⟩ by change k < k + 1; omega)
    · intro i'' hi1 hi2 hlong''
      have hi''_mem : i'' ∈ Finset.univ.image φ := by
        rw [← hfilter_long]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ i'', hlong''⟩
      obtain ⟨m, _, rfl⟩ := Finset.mem_image.mp hi''_mem
      have hm1 : (⟨k, hk1⟩ : Fin N) < m := hφ_strictMono.lt_iff_lt.mp hi1
      have hm2 : m < (⟨k + 1, hk2⟩ : Fin N) := hφ_strictMono.lt_iff_lt.mp hi2
      change k < m.val at hm1
      change m.val < k + 1 at hm2
      omega
    · have hproc_nn : 0 ≤ (inst r d).proc ⟨q, φ ⟨k, hk1⟩⟩ := (inst r d).p_nonneg q (φ ⟨k, hk1⟩)
      change s ⟨q, φ ⟨k + 1, hk2⟩⟩ - (s ⟨q, φ ⟨k, hk1⟩⟩ + (inst r d).proc ⟨q, φ ⟨k, hk1⟩⟩) ≤ D
      linarith
  let B := (Finset.range (N - 1)).filter (fun k => ¬ isGoodIdx k)
  have hB_sum : (B.card : ℝ) * D ≤ ∑ k ∈ Finset.range (N - 1), (tSeq (k + 1) - tSeq k) := by
    calc (B.card : ℝ) * D = ∑ _k ∈ B, D := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ k ∈ B, (tSeq (k + 1) - tSeq k) := by
          refine Finset.sum_le_sum ?_
          intro k hkB
          obtain ⟨hk_range, hk_bad⟩ := Finset.mem_filter.mp hkB
          exact hbad_diff_ge k hk_range hk_bad
      _ ≤ ∑ k ∈ Finset.range (N - 1), (tSeq (k + 1) - tSeq k) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
          intro k hk_range _
          exact htSeq_diff_nonneg k hk_range
  have htele : ∑ k ∈ Finset.range (N - 1), (tSeq (k + 1) - tSeq k) = tSeq (N - 1) - tSeq 0 :=
    Finset.sum_range_sub tSeq (N - 1)
  have htSeq_bound : tSeq (N - 1) - tSeq 0 < (r : ℝ) * (r : ℝ) ^ (2 * d) := by
    have hN1 : N - 1 < N := by omega
    dsimp [tSeq]
    rw [dif_pos hN1, dif_pos hN_pos]
    have hstart : 0 ≤ s ⟨q, φ ⟨0, hN_pos⟩⟩ := hs.start_nonneg ⟨q, φ ⟨0, hN_pos⟩⟩ (Finset.mem_univ q)
    have hcomp := completion_le_makespan (s := s) ⟨q, φ ⟨N - 1, hN1⟩⟩
    have hproc_nn : 0 ≤ (inst r d).proc ⟨q, φ ⟨N - 1, hN1⟩⟩ := (inst r d).p_nonneg q (φ ⟨N - 1, hN1⟩)
    linarith
  let M_bad : ℕ := 4 * r ^ (2 * f - 1)
  have hN_mul : r * r ^ (2 * f - 1) = N := by
    dsimp [N]
    rw [← pow_succ', Nat.sub_add_cancel (by omega)]
  have hM_bad_D : (M_bad : ℝ) * D = (r : ℝ) * (r : ℝ) ^ (2 * d) := by
    have h1 : (r : ℝ) * (r : ℝ) ^ (2 * f - 1) = (N : ℝ) := by exact_mod_cast hN_mul
    have h2 : (r : ℝ) ^ (2 * d) = (r : ℝ) ^ (2 * (d - f)) * (N : ℝ) := by exact_mod_cast hR_split
    dsimp [M_bad, D]
    push_cast
    rw [h2, ← h1]
    ring
  have hB_lt_M : B.card < M_bad := by
    have h1 : (B.card : ℝ) * D < (M_bad : ℝ) * D := by linarith
    have h2 : (B.card : ℝ) < (M_bad : ℝ) := lt_of_mul_lt_mul_right h1 hD_pos.le
    exact_mod_cast h2
  let G_idx := (Finset.range (N - 1)).filter isGoodIdx
  have hGB_sub : Finset.range (N - 1) ⊆ G_idx ∪ B := by
    intro k hk
    by_cases h : isGoodIdx k
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hk, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hk, h⟩)
  have hGB_card : N - 1 ≤ G_idx.card + B.card := by
    calc N - 1 = (Finset.range (N - 1)).card := (Finset.card_range _).symm
      _ ≤ (G_idx ∪ B).card := Finset.card_le_card hGB_sub
      _ ≤ G_idx.card + B.card := Finset.card_union_le _ _
  let ψ_good : ℕ → Fin (size r d) := fun k => if hk : k < N then φ ⟨k, hk⟩ else q
  have hG_image_sub :
      G_idx.image ψ_good ⊆ Finset.univ.filter (fun i : Fin (size r d) => IsGood r d s ⟨q, i⟩) := by
    intro i hi
    obtain ⟨k, hkG, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨hk_range, hk_good⟩ := Finset.mem_filter.mp hkG
    rw [Finset.mem_range] at hk_range
    have hkN : k < N := by omega
    dsimp [ψ_good, isGoodIdx] at hk_good ⊢
    rw [dif_pos hkN] at hk_good ⊢
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk_good⟩
  have hψ_good_inj : Set.InjOn ψ_good G_idx := by
    intro k1 hk1 k2 hk2 heq
    have hk1_range := (Finset.mem_filter.mp hk1).1
    have hk2_range := (Finset.mem_filter.mp hk2).1
    rw [Finset.mem_range] at hk1_range hk2_range
    have hk1N : k1 < N := by omega
    have hk2N : k2 < N := by omega
    dsimp [ψ_good] at heq
    rw [dif_pos hk1N, dif_pos hk2N] at heq
    have hfin := hφ_inj heq
    exact congrArg Fin.val hfin
  have hG_le_good : G_idx.card ≤ goodCount r d s q := by
    unfold goodCount
    change G_idx.card ≤ (Finset.univ.filter (fun i : Fin (size r d) => IsGood r d s ⟨q, i⟩)).card
    rw [← Finset.card_image_of_injOn hψ_good_inj]
    exact Finset.card_le_card hG_image_sub
  have hN_le_good_M : N ≤ goodCount r d s q + M_bad := by omega
  have hcast_le : (N : ℝ) - (M_bad : ℝ) ≤ (goodCount r d s q : ℝ) := by
    have : (N : ℝ) ≤ (goodCount r d s q : ℝ) + (M_bad : ℝ) := by exact_mod_cast hN_le_good_M
    linarith
  have h_lhs_eq : (1 - 4 / (r : ℝ)) * (N : ℝ) = (N : ℝ) - (M_bad : ℝ) := by
    have hr_ne : (r : ℝ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
    have h1 : (r : ℝ) * (r : ℝ) ^ (2 * f - 1) = (N : ℝ) := by exact_mod_cast hN_mul
    dsimp [M_bad]
    push_cast
    rw [← h1]
    field_simp [hr_ne]
  have hr8 : (8 : ℝ) ≤ r := by exact_mod_cast hr
  have hr_pos_real : (0 : ℝ) < r := by linarith
  have hdiv_le : 4 / (r : ℝ) ≤ 1 / 2 := by
    rw [div_le_iff₀ hr_pos_real]
    linarith
  have hN_nonneg : 0 ≤ (N : ℝ) := by positivity
  have h_half_le : (N : ℝ) / 2 ≤ (1 - 4 / (r : ℝ)) * (N : ℝ) := by
    have : (1 / 2 : ℝ) * (N : ℝ) ≤ (1 - 4 / (r : ℝ)) * (N : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith) hN_nonneg
    linarith
  have hN_eq : (N : ℝ) = (r : ℝ) ^ (2 * jobFreq r d q.val) := by
    dsimp [N, f]
    push_cast
    rfl
  linarith

private lemma L_eq_card_mul {r d : ℕ} (hr : 1 ≤ r) (hd : 1 ≤ d)
    (s : (inst r d).Op → ℝ) (hs : (inst r d).IsFeasibleSchedule Finset.univ s)
    (g f : ℕ) (hg1 : 1 ≤ g) (_hg2 : g ≤ r ^ (2 * d)) (_hf1 : 1 ≤ f) (hf2 : f ≤ d) :
    L r d s g f = ((goodOpsOn r d s g f).card : ℝ) * ((r : ℝ) ^ (2 * (d - f)) / 2) := by
  classical
  have hd_pos : 0 < d := by omega
  have hmach_val : ∀ o ∈ goodOpsOn r d s g f, o.2.val = (g - 1) * d + (d - f) := by
    intro o ho
    simp only [goodOpsOn, Finset.mem_filter, Finset.mem_univ, true_and] at ho
    rcases ho with ⟨_, hgrp, hfreq⟩
    change machGroup d o.2.val = g at hgrp
    change machFreq d o.2.val = f at hfreq
    have hmod_lt : o.2.val % d < d := Nat.mod_lt o.2.val hd_pos
    unfold machGroup at hgrp
    unfold machFreq at hfreq
    have hdiv : o.2.val / d = g - 1 := by omega
    have hmod : o.2.val % d = d - f := by omega
    rw [← hdiv, ← hmod, Nat.mul_comm (o.2.val / d) d, Nat.div_add_mod]
  have hproc_val : ∀ o ∈ goodOpsOn r d s g f, (inst r d).proc o = (r : ℝ) ^ (2 * (d - f)) := by
    intro o ho
    simp only [goodOpsOn, Finset.mem_filter, Finset.mem_univ, true_and] at ho
    rcases ho with ⟨ho_good, _, hfreq⟩
    change machFreq d o.2.val = f at hfreq
    have hpair : IsLongPair r d o.1.val o.2.val :=
      (isLongOp_iff_isLongPair hr o.1 o.2).mp ho_good.1
    have hqf : jobFreq r d o.1.val = f := hpair.1.symm.trans hfreq
    change procTime r d o.1.val o.2.val = _
    unfold procTime
    rw [if_pos hpair, hqf]
  have hdisj : (goodOpsOn r d s g f : Set (inst r d).Op).PairwiseDisjoint (firstHalf r d s) := by
    intro o1 ho1 o2 ho2 hne
    have hm1 := hmach_val o1 ho1
    have hm2 := hmach_val o2 ho2
    have hmach_eq : (inst r d).mach o1 = (inst r d).mach o2 := Fin.ext (hm1.trans hm2.symm)
    have hmd := hs.machine_disjoint o1 o2 (Finset.mem_univ _) (Finset.mem_univ _) hne hmach_eq
    have hp1 : 0 ≤ (inst r d).proc o1 := (inst r d).p_nonneg o1.1 o1.2
    have hp2 : 0 ≤ (inst r d).proc o2 := (inst r d).p_nonneg o2.1 o2.2
    change Disjoint (firstHalf r d s o1) (firstHalf r d s o2)
    rw [Set.disjoint_iff]
    rintro x ⟨hx1, hx2⟩
    unfold firstHalf at hx1 hx2
    simp only [Set.mem_Ico] at hx1 hx2
    rcases hmd with h12 | h21 <;> linarith
  have hsUnion_eq : ⋃₀ T r d s g f = ⋃ o ∈ goodOpsOn r d s g f, firstHalf r d s o := by
    ext x
    simp [T]
  have hmeas : ∀ o ∈ goodOpsOn r d s g f, MeasurableSet (firstHalf r d s o) :=
    fun _ _ => measurableSet_Ico
  have hvol_union :
      MeasureTheory.volume (⋃₀ T r d s g f) =
        ∑ o ∈ goodOpsOn r d s g f, ENNReal.ofReal ((r : ℝ) ^ (2 * (d - f)) / 2) := by
    rw [hsUnion_eq, MeasureTheory.measure_biUnion_finset hdisj hmeas]
    refine Finset.sum_congr rfl ?_
    intro o ho
    unfold firstHalf
    rw [Real.volume_Ico, hproc_val o ho]
    ring_nf
  unfold L
  rw [hvol_union, ENNReal.toReal_sum (fun _ _ => ENNReal.ofReal_ne_top)]
  have h_ofReal : (ENNReal.ofReal ((r : ℝ) ^ (2 * (d - f)) / 2)).toReal = (r : ℝ) ^ (2 * (d - f)) / 2 :=
    ENNReal.toReal_ofReal (by positivity)
  simp_rw [h_ofReal]
  rw [Finset.sum_const, nsmul_eq_mul]

private lemma sum_goodOpsOn_card_eq_sum_goodCount {r d : ℕ} (hr : 1 ≤ r)
    (s : (inst r d).Op → ℝ) (f : ℕ) :
    ∑ g ∈ Finset.Icc 1 (r ^ (2 * d)), (goodOpsOn r d s g f).card =
      ∑ q ∈ Finset.univ.filter (fun q : Fin (size r d) => jobFreq r d q.val = f),
        goodCount r d s q := by
  classical
  let R := r ^ (2 * d)
  let S_f : Finset (inst r d).Op :=
    Finset.univ.filter (fun o : (inst r d).Op => IsGood r d s o ∧ machFreq d ((inst r d).mach o) = f)
  have h_lhs : S_f.card = ∑ g ∈ Finset.Icc 1 R, (goodOpsOn r d s g f).card := by
    have hbiUnion : (Finset.Icc 1 R).biUnion (fun g => goodOpsOn r d s g f) = S_f := by
      ext o
      simp only [Finset.mem_biUnion, Finset.mem_Icc, goodOpsOn, S_f, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · rintro ⟨g, _, ho_good, _, ho_freq⟩
        exact ⟨ho_good, ho_freq⟩
      · rintro ⟨ho_good, ho_freq⟩
        refine ⟨machGroup d o.2.val, ?_, ho_good, rfl, ho_freq⟩
        have hdiv : o.2.val / d < R := div_lt_of_lt_mul_right o.2.isLt
        unfold machGroup
        exact ⟨Nat.le_add_left 1 _, hdiv⟩
    have hdisj : (Finset.Icc 1 R : Set ℕ).PairwiseDisjoint (fun g => goodOpsOn r d s g f) := by
      intro g1 _ g2 _ hne
      change Disjoint (goodOpsOn r d s g1 f) (goodOpsOn r d s g2 f)
      rw [Finset.disjoint_left]
      intro o ho1 ho2
      simp only [goodOpsOn, Finset.mem_filter, Finset.mem_univ, true_and] at ho1 ho2
      exact hne (ho1.2.1.symm.trans ho2.2.1)
    rw [← hbiUnion, Finset.card_biUnion hdisj]
  let Q_f := Finset.univ.filter (fun q : Fin (size r d) => jobFreq r d q.val = f)
  let opsOfJob : Fin (size r d) → Finset (inst r d).Op := fun q =>
    (Finset.univ.filter (fun i : Fin (size r d) => IsGood r d s ⟨q, i⟩)).image (fun i => ⟨q, i⟩)
  have h_rhs : S_f.card = ∑ q ∈ Q_f, goodCount r d s q := by
    have hbiUnion : Q_f.biUnion opsOfJob = S_f := by
      ext o
      rw [Finset.mem_biUnion]
      constructor
      · rintro ⟨q', hq', hmem⟩
        have hq'_freq : jobFreq r d q'.val = f := (Finset.mem_filter.mp hq').2
        obtain ⟨i', hi', rfl⟩ := Finset.mem_image.mp hmem
        have hi'_good : IsGood r d s ⟨q', i'⟩ := (Finset.mem_filter.mp hi').2
        have hpair : IsLongPair r d q'.val i'.val :=
          (isLongOp_iff_isLongPair hr q' i').mp hi'_good.1
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi'_good, hpair.1.trans hq'_freq⟩
      · intro hmem
        rcases o with ⟨q, i⟩
        obtain ⟨_, hi_good, hi_freq⟩ := Finset.mem_filter.mp hmem
        have hpair : IsLongPair r d q.val i.val :=
          (isLongOp_iff_isLongPair hr q i).mp hi_good.1
        refine ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpair.1.symm.trans hi_freq⟩, ?_⟩
        exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi_good⟩, rfl⟩
    have hdisj : (Q_f : Set (Fin (size r d))).PairwiseDisjoint opsOfJob := by
      intro q1 _ q2 _ hne
      change Disjoint (opsOfJob q1) (opsOfJob q2)
      rw [Finset.disjoint_left]
      intro o ho1 ho2
      obtain ⟨i1, _, rfl⟩ := Finset.mem_image.mp ho1
      obtain ⟨i2, _, heq⟩ := Finset.mem_image.mp ho2
      exact hne (congrArg Sigma.fst heq).symm
    rw [← hbiUnion, Finset.card_biUnion hdisj]
    refine Finset.sum_congr rfl ?_
    intro q _
    unfold opsOfJob goodCount
    have hinj : Function.Injective (fun i : Fin (size r d) => (⟨q, i⟩ : (inst r d).Op)) := by
      intro i1 i2 h
      injection h
    exact Finset.card_image_of_injective _ hinj
  exact h_lhs.symm.trans h_rhs

private lemma card_jobs_of_freq {r d : ℕ} (hr : 1 ≤ r) (_hd : 1 ≤ d)
    (f : ℕ) (hf1 : 1 ≤ f) (hf2 : f ≤ d) :
    (Finset.univ.filter (fun q : Fin (size r d) => jobFreq r d q.val = f)).card = r ^ (2 * d) := by
  classical
  let R := r ^ (2 * d)
  have hR_pos : 0 < R := pow_pos (by omega) _
  let ξ : Fin R → Fin (size r d) := fun rem =>
    ⟨(f - 1) * R + rem.val, by
      have hf_lt : f - 1 < d := by omega
      have h1 : (f - 1) * R + R ≤ R * d := by
        calc (f - 1) * R + R = (f - 1 + 1) * R := by rw [Nat.add_mul, Nat.one_mul]
          _ ≤ d * R := Nat.mul_le_mul_right R hf_lt
          _ = R * d := Nat.mul_comm d R
      change (f - 1) * R + rem.val < R * d
      exact lt_of_lt_of_le (Nat.add_lt_add_left rem.isLt _) h1⟩
  have hξ_div_mod : ∀ rem : Fin R, (ξ rem).val / R = f - 1 ∧ (ξ rem).val % R = rem.val := by
    intro rem
    exact div_mod_of_eq_mul_add rem.isLt rfl
  have hξ_inj : Function.Injective ξ := by
    intro r1 r2 h
    have h1 := (hξ_div_mod r1).2
    have h2 := (hξ_div_mod r2).2
    rw [h] at h1
    ext
    exact h1.symm.trans h2
  have hfilter_eq :
      Finset.univ.filter (fun q : Fin (size r d) => jobFreq r d q.val = f) =
        Finset.univ.image ξ := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hqf
      unfold jobFreq at hqf
      have hdiv : q.val / R = f - 1 := by dsimp [R]; omega
      refine ⟨⟨q.val % R, Nat.mod_lt q.val hR_pos⟩, ?_⟩
      ext
      dsimp [ξ]
      rw [← hdiv, Nat.mul_comm (q.val / R) R, Nat.div_add_mod]
    · rintro ⟨rem, rfl⟩
      obtain ⟨hdiv, _⟩ := hξ_div_mod rem
      unfold jobFreq
      change (ξ rem).val / R + 1 = f
      omega
  rw [hfilter_eq, Finset.card_image_of_injective _ hξ_inj, Finset.card_univ, Fintype.card_fin]

end Lemma24Proof

open Lemma24Proof in
theorem solution (r d : ℕ) (hr : 8 ≤ r) (s : (inst r d).Op → ℝ)
    (hs : (inst r d).IsFeasibleSchedule Finset.univ s)
    (hmk : (inst r d).makespan Finset.univ s < (r : ℝ) * (r : ℝ) ^ (2 * d)) :
    ∃ g : ℕ, 1 ≤ g ∧ g ≤ r ^ (2 * d) ∧
      (r : ℝ) ^ (2 * d) / 4 * (d : ℝ) ≤ ∑ f ∈ Finset.Icc 1 d, L r d s g f := by
  classical
  rcases Nat.eq_zero_or_pos d with rfl | hd_pos
  · refine ⟨1, le_rfl, by simp, ?_⟩
    simp
  · have hr1 : 1 ≤ r := by omega
    have hd1 : 1 ≤ d := by omega
    let R := r ^ (2 * d)
    have hR_pos : 0 < R := pow_pos (by omega) _
    have h_sum_f : ∀ f ∈ Finset.Icc 1 d,
        (R : ℝ) * ((R : ℝ) / 4) ≤ ∑ g ∈ Finset.Icc 1 R, L r d s g f := by
      intro f hf
      rw [Finset.mem_Icc] at hf
      rcases hf with ⟨hf1, hf2⟩
      have hL_congr : ∑ g ∈ Finset.Icc 1 R, L r d s g f =
          (∑ g ∈ Finset.Icc 1 R, ((goodOpsOn r d s g f).card : ℝ)) *
            ((r : ℝ) ^ (2 * (d - f)) / 2) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl ?_
        intro g hg
        rw [Finset.mem_Icc] at hg
        exact L_eq_card_mul hr1 hd1 s hs g f hg.1 hg.2 hf1 hf2
      rw [hL_congr, ← Nat.cast_sum, sum_goodOpsOn_card_eq_sum_goodCount hr1 s f, Nat.cast_sum]
      let Q_f := Finset.univ.filter (fun q : Fin (size r d) => jobFreq r d q.val = f)
      have hQ_sum_ge :
          (R : ℝ) * ((r : ℝ) ^ (2 * f) / 2) ≤ ∑ q ∈ Q_f, (goodCount r d s q : ℝ) := by
        calc (R : ℝ) * ((r : ℝ) ^ (2 * f) / 2)
            = (Q_f.card : ℝ) * ((r : ℝ) ^ (2 * f) / 2) := by
                rw [card_jobs_of_freq hr1 hd1 f hf1 hf2]
          _ = ∑ _q ∈ Q_f, ((r : ℝ) ^ (2 * f) / 2) := by
                rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ ∑ q ∈ Q_f, (goodCount r d s q : ℝ) := by
                refine Finset.sum_le_sum ?_
                intro q hq
                have hqf : jobFreq r d q.val = f := (Finset.mem_filter.mp hq).2
                have hgood := goodCount_lower_bound r d hr s hs hmk q
                rwa [hqf] at hgood
      have h_nonneg : 0 ≤ (r : ℝ) ^ (2 * (d - f)) / 2 := by positivity
      have h_mul := mul_le_mul_of_nonneg_right hQ_sum_ge h_nonneg
      have hR_split : (R : ℝ) = (r : ℝ) ^ (2 * f) * (r : ℝ) ^ (2 * (d - f)) := by
        have hnat : R = r ^ (2 * f) * r ^ (2 * (d - f)) := by
          dsimp [R]
          rw [← pow_add]
          congr 1
          omega
        exact_mod_cast hnat
      linarith [show (R : ℝ) * ((r : ℝ) ^ (2 * f) / 2) * ((r : ℝ) ^ (2 * (d - f)) / 2) =
        (R : ℝ) * ((R : ℝ) / 4) by rw [hR_split]; ring]
    have h_total_sum :
        (R : ℝ) * ((R : ℝ) / 4 * (d : ℝ)) ≤
          ∑ g ∈ Finset.Icc 1 R, ∑ f ∈ Finset.Icc 1 d, L r d s g f := by
      rw [Finset.sum_comm]
      have hcard_d_nat : (Finset.Icc 1 d).card = d := by
        rw [Nat.card_Icc]
        omega
      have hcard_d : ((Finset.Icc 1 d).card : ℝ) = (d : ℝ) := by exact_mod_cast hcard_d_nat
      calc (R : ℝ) * ((R : ℝ) / 4 * (d : ℝ))
          = ((Finset.Icc 1 d).card : ℝ) * ((R : ℝ) * ((R : ℝ) / 4)) := by
              rw [hcard_d]; ring
        _ = ∑ _f ∈ Finset.Icc 1 d, (R : ℝ) * ((R : ℝ) / 4) := by
              rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ f ∈ Finset.Icc 1 d, ∑ g ∈ Finset.Icc 1 R, L r d s g f :=
              Finset.sum_le_sum h_sum_f
    by_contra h_none
    have hR_cast : (R : ℝ) = (r : ℝ) ^ (2 * d) := by dsimp [R]; push_cast; rfl
    have h_all_lt : ∀ g ∈ Finset.Icc 1 R,
        ∑ f ∈ Finset.Icc 1 d, L r d s g f < (R : ℝ) / 4 * (d : ℝ) := by
      intro g hg
      rw [Finset.mem_Icc] at hg
      by_contra hge
      have hle : (r : ℝ) ^ (2 * d) / 4 * (d : ℝ) ≤ ∑ f ∈ Finset.Icc 1 d, L r d s g f := by
        rw [← hR_cast]
        exact le_of_not_gt hge
      exact h_none ⟨g, hg.1, hg.2, hle⟩
    have hIcc_nonempty : (Finset.Icc 1 R).Nonempty := ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hR_pos⟩⟩
    have h_sum_lt := Finset.sum_lt_sum_of_nonempty hIcc_nonempty h_all_lt
    have hcard_R_nat : (Finset.Icc 1 R).card = R := by
      rw [Nat.card_Icc]
      omega
    have hcard_R : ((Finset.Icc 1 R).card : ℝ) = (R : ℝ) := by exact_mod_cast hcard_R_nat
    rw [Finset.sum_const, nsmul_eq_mul, hcard_R] at h_sum_lt
    linarith
