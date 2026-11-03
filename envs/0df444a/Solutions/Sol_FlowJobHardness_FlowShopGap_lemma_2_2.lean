-- Prove2me | solution 1 for FlowJobHardness.FlowShopGap.lemma_2_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T22:24:18.99343+00:00
-- url     : https://prove2.me/submissions/b6f04314-964e-45a2-9909-ed67fa166948

import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_FlowJobHardness_FlowShopGap_Construction
import Definitions.Def_FlowJobHardness_FlowShopGap_GoodOps

open JobShopLTAS.Core
open FlowJobHardness.FlowShopGap

namespace Lemma22Proof

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

end Lemma22Proof

open Lemma22Proof in
theorem solution (r d : ℕ) (hr : 1 ≤ r) (s : (inst r d).Op → ℝ)
    (hs : (inst r d).IsFeasibleSchedule Finset.univ s)
    (hmk : (inst r d).makespan Finset.univ s < (r : ℝ) * (r : ℝ) ^ (2 * d))
    (q : Fin (size r d)) :
    (1 - 4 / (r : ℝ)) * (longCount r d q : ℝ) ≤ (goodCount r d s q : ℝ) := by
  classical
  by_cases hr4 : r ≤ 4
  · have hr_pos : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
    have hr_le : (r : ℝ) ≤ 4 := by exact_mod_cast hr4
    have hdiv : 1 ≤ 4 / (r : ℝ) := by
      rw [le_div_iff₀ hr_pos]
      linarith
    have hnonpos : (1 - 4 / (r : ℝ)) * (longCount r d q : ℝ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (Nat.cast_nonneg _)
    exact le_trans hnonpos (Nat.cast_nonneg _)
  · obtain ⟨hd_pos, hR_pos, hr_pos⟩ := pos_of_fin_size q
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
        isLongOp_iff_isLongPair hr]
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
    have hlongCount : longCount r d q = N := by
      unfold longCount
      change (Finset.univ.filter (fun i : Fin (size r d) => IsLongOp r d ⟨q, i⟩)).card = N
      rw [hfilter_long, Finset.card_image_of_injective _ hφ_inj, Finset.card_univ, Fintype.card_fin]
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
    have h_lhs_eq : (1 - 4 / (r : ℝ)) * (longCount r d q : ℝ) = (N : ℝ) - (M_bad : ℝ) := by
      rw [hlongCount]
      have hr_ne : (r : ℝ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
      have h1 : (r : ℝ) * (r : ℝ) ^ (2 * f - 1) = (N : ℝ) := by exact_mod_cast hN_mul
      dsimp [M_bad]
      push_cast
      rw [← h1]
      field_simp [hr_ne]
    linarith
