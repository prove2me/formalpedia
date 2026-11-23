-- Prove2me | solution 1 for BLTCounting.AccuracySpace.claim_3_14
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:28:14.038049+00:00
-- url     : https://prove2.me/submissions/2cb2341e-ce53-4249-9f49-f7984f0d0dc9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BLTCounting_AccuracySpace_FourierKernel
import Theorems.Thm_BLTCounting_AccuracySpace_lemma_3_13

open Matrix BLTCounting.AccuracySpace

namespace AuxClaim314

lemma bandCoeff_neg (θ : ℝ) (p : ℤ) : bandCoeff θ (-p) = bandCoeff θ p := by
  unfold bandCoeff
  by_cases hp : p = 0
  · simp [hp]
  · have hnp : -p ≠ 0 := neg_ne_zero.mpr hp
    simp only [hp, hnp, ↓reduceIte, Int.cast_neg]
    have h1 : (-(p : ℝ)) * θ = -((p : ℝ) * θ) := by ring
    rw [h1, Real.sin_neg]
    ring

lemma bandCoeff_sq_le_inv_sq (θ : ℝ) {p : ℕ} (hp : 1 ≤ p) :
    |bandCoeff θ (p : ℤ)| ^ 2 ≤ 1 / (p : ℝ) ^ 2 := by
  have hp0 : (p : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (by omega)
  have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr (by omega)
  have hpi1 : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  unfold bandCoeff
  simp only [hp0, ↓reduceIte, Int.cast_natCast, abs_div]
  rw [abs_of_pos (mul_pos Real.pi_pos hp_pos), div_pow]
  have hsin : |Real.sin ((p : ℝ) * θ)| ^ 2 ≤ 1 := by
    have h1 := Real.abs_sin_le_one ((p : ℝ) * θ)
    nlinarith [abs_nonneg (Real.sin ((p : ℝ) * θ))]
  have hden : (p : ℝ) ^ 2 ≤ (Real.pi * (p : ℝ)) ^ 2 :=
    pow_le_pow_left₀ hp_pos.le (by nlinarith) 2
  calc
    |Real.sin ((p : ℝ) * θ)| ^ 2 / (Real.pi * (p : ℝ)) ^ 2
        ≤ 1 / (Real.pi * (p : ℝ)) ^ 2 :=
      div_le_div_of_nonneg_right hsin (by positivity)
    _ ≤ 1 / (p : ℝ) ^ 2 :=
      one_div_le_one_div_of_le (by positivity) hden

lemma bandCoeff_sq_le_theta_sq {θ : ℝ} (hθ0 : 0 < θ) {p : ℕ} (hp : 1 ≤ p) :
    |bandCoeff θ (p : ℤ)| ^ 2 ≤ θ ^ 2 := by
  have hp0 : (p : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (by omega)
  have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr (by omega)
  have hpi1 : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  unfold bandCoeff
  simp only [hp0, ↓reduceIte, Int.cast_natCast, abs_div]
  rw [abs_of_pos (mul_pos Real.pi_pos hp_pos)]
  have hle : |Real.sin ((p : ℝ) * θ)| / (Real.pi * (p : ℝ)) ≤ θ := by
    rw [div_le_iff₀ (mul_pos Real.pi_pos hp_pos)]
    have hsin : |Real.sin ((p : ℝ) * θ)| ≤ (p : ℝ) * θ := by
      simpa [abs_of_pos (mul_pos hp_pos hθ0)] using (Real.abs_sin_le_abs (x := (p : ℝ) * θ))
    have hmul : 1 * ((p : ℝ) * θ) ≤ Real.pi * ((p : ℝ) * θ) :=
      mul_le_mul_of_nonneg_right hpi1 (by positivity)
    linarith
  have hnn : 0 ≤ |Real.sin ((p : ℝ) * θ)| / (Real.pi * (p : ℝ)) := by positivity
  nlinarith

lemma inv_le_log_sub {p : ℕ} (hp : 2 ≤ p) :
    1 / (p : ℝ) ≤ Real.log (p : ℝ) - Real.log (((p - 1 : ℕ) : ℝ)) := by
  have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr (by omega)
  have hp1_pos : (0 : ℝ) < (((p - 1 : ℕ) : ℝ)) := Nat.cast_pos.mpr (by omega)
  have hcast : (((p - 1 : ℕ) : ℝ)) = (p : ℝ) - 1 := by simp [Nat.cast_sub (by omega : 1 ≤ p)]
  have hlog := Real.log_le_sub_one_of_pos (div_pos hp1_pos hp_pos)
  rw [Real.log_div (ne_of_gt hp1_pos) (ne_of_gt hp_pos)] at hlog
  have hrhs : (((p - 1 : ℕ) : ℝ)) / (p : ℝ) - 1 = -(1 / (p : ℝ)) := by
    rw [hcast]
    field_simp [ne_of_gt hp_pos]
    ring
  linarith

lemma sum_inv_Ico_le_log {a b : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) :
    ∑ p ∈ Finset.Ico a b, (1 / (p : ℝ)) ≤
      Real.log (((b - 1 : ℕ) : ℝ)) - Real.log (((a - 1 : ℕ) : ℝ)) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Nat.add_succ, Finset.sum_Ico_succ_top (by omega)]
    have hstep := inv_le_log_sub (p := a + d) (by omega)
    have h1 : a + d + 1 - 1 = a + d := by omega
    rw [h1]
    have ih' := ih (by omega)
    linarith

lemma sum_inv_sq_tail_le (K N : ℕ) (hK : 2 ≤ K) :
    ∑ m ∈ Finset.range N, (1 / ((m + K : ℕ) : ℝ) ^ 2) ≤ 1 / (((K - 1 : ℕ) : ℝ)) := by
  have htele : ∑ m ∈ Finset.range N, (1 / ((m + K : ℕ) : ℝ) ^ 2) ≤
      1 / (((K - 1 : ℕ) : ℝ)) - 1 / (((N + K - 1 : ℕ) : ℝ)) := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have hpos1 : (0 : ℝ) < (((N + K - 1 : ℕ) : ℝ)) := Nat.cast_pos.mpr (by omega)
      have hpos2 : (0 : ℝ) < (((N + K : ℕ) : ℝ)) := Nat.cast_pos.mpr (by omega)
      have hcast1 : (((N + K - 1 : ℕ) : ℝ)) = ((N + K : ℕ) : ℝ) - 1 := by
        simp [Nat.cast_sub (by omega : 1 ≤ N + K)]
      have hcast2 : (((N + 1 + K - 1 : ℕ) : ℝ)) = ((N + K : ℕ) : ℝ) := by
        congr 1; omega
      rw [hcast2]
      have hterm : 1 / (((N + K : ℕ) : ℝ)) ^ 2 ≤
          1 / (((N + K - 1 : ℕ) : ℝ)) - 1 / (((N + K : ℕ) : ℝ)) := by
        have hdiff : 1 / (((N + K - 1 : ℕ) : ℝ)) - 1 / (((N + K : ℕ) : ℝ)) =
            1 / ((((N + K - 1 : ℕ) : ℝ)) * (((N + K : ℕ) : ℝ))) := by
          field_simp [ne_of_gt hpos1, ne_of_gt hpos2]
          rw [hcast1]
          ring
        rw [hdiff]
        refine one_div_le_one_div_of_le (mul_pos hpos1 hpos2) ?_
        rw [hcast1, sq]
        nlinarith
      linarith
  have hnn : 0 ≤ 1 / (((N + K - 1 : ℕ) : ℝ)) := by positivity
  linarith

lemma mid_sum_eq (θ : ℝ) {K : ℕ} (hK : 2 ≤ K) :
    ∑ p ∈ Finset.Icc (-((K : ℤ) - 1)) ((K : ℤ) - 1), |bandCoeff θ p| ^ 2 =
      |bandCoeff θ 0| ^ 2 + 2 * ∑ p ∈ Finset.Ico 1 K, |bandCoeff θ (p : ℤ)| ^ 2 := by
  let S_mid : Finset ℤ := Finset.Icc (-((K : ℤ) - 1)) ((K : ℤ) - 1)
  change ∑ p ∈ S_mid, |bandCoeff θ p| ^ 2 = _
  have h0_mem : (0 : ℤ) ∈ S_mid := by
    simp only [S_mid, Finset.mem_Icc]
    omega
  rw [← Finset.add_sum_erase S_mid _ h0_mem]
  congr 1
  let pos_set : Finset ℤ := (Finset.Ico 1 K).image (fun n : ℕ => (n : ℤ))
  let neg_set : Finset ℤ := (Finset.Ico 1 K).image (fun n : ℕ => -(n : ℤ))
  have hpart : S_mid.erase 0 = pos_set ∪ neg_set := by
    ext z
    simp only [S_mid, pos_set, neg_set, Finset.mem_erase, Finset.mem_Icc, Finset.mem_union,
      Finset.mem_image, Finset.mem_Ico]
    constructor
    · rintro ⟨hz0, hz1, hz2⟩
      rcases lt_trichotomy z 0 with hneg | rfl | hpos
      · exact Or.inr ⟨(-z).toNat, ⟨by omega, by omega⟩, by omega⟩
      · exact absurd rfl hz0
      · exact Or.inl ⟨z.toNat, ⟨by omega, by omega⟩, by omega⟩
    · rintro (⟨n, ⟨hn1, hn2⟩, rfl⟩ | ⟨n, ⟨hn1, hn2⟩, rfl⟩) <;> omega
  have hdisj : Disjoint pos_set neg_set := by
    rw [Finset.disjoint_left]
    rintro z hz1 hz2
    simp only [pos_set, neg_set, Finset.mem_image, Finset.mem_Ico] at hz1 hz2
    rcases hz1 with ⟨n1, ⟨h1, _⟩, rfl⟩
    rcases hz2 with ⟨n2, ⟨h2, _⟩, heq⟩
    omega
  rw [hpart, Finset.sum_union hdisj,
    Finset.sum_image (fun a _ b _ h => Nat.cast_injective h),
    Finset.sum_image (fun a _ b _ h => Nat.cast_injective (neg_inj.mp h))]
  simp only [bandCoeff_neg]
  ring

lemma tail_bound {θ : ℝ} {K : ℕ} (hK : 2 ≤ K)
    (hsum : HasSum (fun p : ℤ => |bandCoeff θ p| ^ 2) (bandCoeff θ 0)) :
    (bandCoeff θ 0 - |bandCoeff θ 0| ^ 2 -
      2 * ∑ p ∈ Finset.Ico 1 K, |bandCoeff θ (p : ℤ)| ^ 2) ≤ 4 / (K : ℝ) := by
  by_contra hgt
  have hgt' : 4 / (K : ℝ) <
      bandCoeff θ 0 - |bandCoeff θ 0| ^ 2 -
        2 * ∑ p ∈ Finset.Ico 1 K, |bandCoeff θ (p : ℤ)| ^ 2 := not_le.mp hgt
  let S_mid : Finset ℤ := Finset.Icc (-((K : ℤ) - 1)) ((K : ℤ) - 1)
  have hmid_sum : ∑ p ∈ S_mid, |bandCoeff θ p| ^ 2 =
      |bandCoeff θ 0| ^ 2 + 2 * ∑ p ∈ Finset.Ico 1 K, |bandCoeff θ (p : ℤ)| ^ 2 :=
    mid_sum_eq θ hK
  let gap : ℝ := (bandCoeff θ 0 - |bandCoeff θ 0| ^ 2 -
    2 * ∑ p ∈ Finset.Ico 1 K, |bandCoeff θ (p : ℤ)| ^ 2) - 4 / (K : ℝ)
  have hgap_pos : 0 < gap := sub_pos.mpr hgt'
  have hnhds : Metric.ball (bandCoeff θ 0) (gap / 2) ∈ nhds (bandCoeff θ 0) :=
    Metric.ball_mem_nhds _ (half_pos hgap_pos)
  rcases (Filter.mem_atTop_sets.mp (hsum hnhds)) with ⟨T₀, hT₀⟩
  let N : ℕ := T₀.sup (fun z : ℤ => z.natAbs) + 1
  let S_big : Finset ℤ := Finset.Icc (-(((N + K : ℕ) : ℤ) - 1)) (((N + K : ℕ) : ℤ) - 1)
  have hsub_T₀ : T₀ ⊆ S_big := by
    intro z hz
    have hle_sup : z.natAbs ≤ T₀.sup (fun w : ℤ => w.natAbs) := Finset.le_sup hz
    simp only [S_big, Finset.mem_Icc]
    omega
  have hball : (∑ p ∈ S_big, |bandCoeff θ p| ^ 2) ∈ Metric.ball (bandCoeff θ 0) (gap / 2) :=
    hT₀ S_big hsub_T₀
  rw [Metric.mem_ball, Real.dist_eq] at hball
  have hbig_gt : bandCoeff θ 0 - gap / 2 < ∑ p ∈ S_big, |bandCoeff θ p| ^ 2 := by
    linarith [(abs_lt.mp hball).1]
  have hbig_le : ∑ p ∈ S_big, |bandCoeff θ p| ^ 2 ≤
      (∑ p ∈ S_mid, |bandCoeff θ p| ^ 2) +
        2 * ∑ m ∈ Finset.range N, |bandCoeff θ ((m + K : ℕ) : ℤ)| ^ 2 := by
    let pos_tail : Finset ℤ := (Finset.range N).image (fun m : ℕ => ((m + K : ℕ) : ℤ))
    let neg_tail : Finset ℤ := (Finset.range N).image (fun m : ℕ => -(((m + K : ℕ) : ℤ)))
    have hcov : S_big ⊆ S_mid ∪ (pos_tail ∪ neg_tail) := by
      intro z hz
      simp only [S_big, S_mid, pos_tail, neg_tail, Finset.mem_Icc, Finset.mem_union,
        Finset.mem_image, Finset.mem_range] at hz ⊢
      by_cases hmid : -((K : ℤ) - 1) ≤ z ∧ z ≤ (K : ℤ) - 1
      · exact Or.inl hmid
      · right
        rcases lt_or_ge z (-((K : ℤ) - 1)) with hlt | hge
        · exact Or.inr ⟨((-z).toNat - K), by omega, by omega⟩
        · exact Or.inl ⟨(z.toNat - K), by omega, by omega⟩
    calc
      ∑ p ∈ S_big, |bandCoeff θ p| ^ 2
          ≤ ∑ p ∈ S_mid ∪ (pos_tail ∪ neg_tail), |bandCoeff θ p| ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hcov fun _ _ _ => sq_nonneg _
      _ ≤ (∑ p ∈ S_mid, |bandCoeff θ p| ^ 2) +
          ((∑ p ∈ pos_tail, |bandCoeff θ p| ^ 2) + (∑ p ∈ neg_tail, |bandCoeff θ p| ^ 2)) := by
        have hu1 : ∀ A B : Finset ℤ,
            ∑ p ∈ A ∪ B, |bandCoeff θ p| ^ 2 ≤
              (∑ p ∈ A, |bandCoeff θ p| ^ 2) + (∑ p ∈ B, |bandCoeff θ p| ^ 2) := by
          intro A B
          have h := Finset.sum_union_inter (s₁ := A) (s₂ := B) (f := fun p => |bandCoeff θ p| ^ 2)
          have hnn : 0 ≤ ∑ p ∈ A ∩ B, |bandCoeff θ p| ^ 2 :=
            Finset.sum_nonneg fun _ _ => sq_nonneg _
          linarith
        linarith [hu1 S_mid (pos_tail ∪ neg_tail), hu1 pos_tail neg_tail]
      _ = (∑ p ∈ S_mid, |bandCoeff θ p| ^ 2) +
          2 * ∑ m ∈ Finset.range N, |bandCoeff θ ((m + K : ℕ) : ℤ)| ^ 2 := by
        rw [Finset.sum_image (fun a _ b _ h => by omega),
          Finset.sum_image (fun a _ b _ h => by omega)]
        simp only [bandCoeff_neg]
        ring
  have htail_num : 2 * ∑ m ∈ Finset.range N, |bandCoeff θ ((m + K : ℕ) : ℤ)| ^ 2 ≤
      4 / (K : ℝ) := by
    calc
      2 * ∑ m ∈ Finset.range N, |bandCoeff θ ((m + K : ℕ) : ℤ)| ^ 2
          ≤ 2 * ∑ m ∈ Finset.range N, (1 / ((m + K : ℕ) : ℝ) ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        refine Finset.sum_le_sum fun m _ => ?_
        exact bandCoeff_sq_le_inv_sq θ (by omega)
      _ ≤ 2 * (1 / (((K - 1 : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left (sum_inv_sq_tail_le K N hK) (by norm_num)
      _ ≤ 4 / (K : ℝ) := by
        have hK_pos : (0 : ℝ) < (K : ℝ) := Nat.cast_pos.mpr (by omega)
        have hKm1_pos : (0 : ℝ) < (((K - 1 : ℕ) : ℝ)) := Nat.cast_pos.mpr (by omega)
        have hKm1 : (K : ℝ) ≤ 2 * (((K - 1 : ℕ) : ℝ)) := by
          have hc : (((K - 1 : ℕ) : ℝ)) = (K : ℝ) - 1 := by simp [Nat.cast_sub (by omega : 1 ≤ K)]
          have hK2 : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
          linarith
        rw [mul_one_div, div_le_div_iff₀ hKm1_pos hK_pos]
        linarith
  linarith [hmid_sum]

lemma weighted_mid_bound {θ : ℝ} (hθ0 : 0 < θ) (hθπ : θ ≤ Real.pi) {K : ℕ} (hK : 2 ≤ K)
    (hX : 4 ≤ (K : ℝ) * θ) :
    2 * ∑ p ∈ Finset.Ico 1 K, (p : ℝ) * |bandCoeff θ (p : ℤ)| ^ 2 ≤
      12 * Real.log ((K : ℝ) * θ) := by
  let M : ℕ := max 1 ⌊1 / θ⌋₊
  have hM1 : 1 ≤ M := le_max_left _ _
  have hsplit : ∑ p ∈ Finset.Ico 1 K, (p : ℝ) * |bandCoeff θ (p : ℤ)| ^ 2 ≤
      (∑ p ∈ Finset.Ico 1 (M + 1), (p : ℝ) * |bandCoeff θ (p : ℤ)| ^ 2) +
      (∑ p ∈ Finset.Ico (M + 1) K, (p : ℝ) * |bandCoeff θ (p : ℤ)| ^ 2) := by
    by_cases hMK : M + 1 ≤ K
    · have hu : Finset.Ico 1 K = Finset.Ico 1 (M + 1) ∪ Finset.Ico (M + 1) K :=
        (Finset.Ico_union_Ico_eq_Ico (by omega) hMK).symm
      rw [hu, Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive 1 (M + 1) K)]
    · have hemp : Finset.Ico (M + 1) K = ∅ := Finset.Ico_eq_empty_iff.mpr (by omega)
      rw [hemp, Finset.sum_empty, add_zero]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun p _ _ => by positivity
      intro p hp
      rw [Finset.mem_Ico] at hp ⊢
      omega
  have h_small : ∑ p ∈ Finset.Ico 1 (M + 1), (p : ℝ) * |bandCoeff θ (p : ℤ)| ^ 2 ≤ 4 := by
    by_cases hM_eq1 : ⌊1 / θ⌋₊ ≤ 1
    · have hMeq : M = 1 := by omega
      rw [hMeq]
      have hset : Finset.Ico 1 2 = {1} := by decide
      rw [hset, Finset.sum_singleton]
      have hb := bandCoeff_sq_le_inv_sq θ (p := 1) le_rfl
      have hb' : |bandCoeff θ (1 : ℤ)| ^ 2 ≤ 1 := by simpa using hb
      simpa using le_trans hb' (by norm_num : (1 : ℝ) ≤ 4)
    · have hgt1 : 1 < ⌊1 / θ⌋₊ := not_le.mp hM_eq1
      have hMeq : M = ⌊1 / θ⌋₊ := max_eq_right hgt1.le
      have hMθ : (M : ℝ) * θ ≤ 1 := by
        rw [hMeq]
        have hle : (⌊1 / θ⌋₊ : ℝ) ≤ 1 / θ := Nat.floor_le (by positivity)
        exact (le_div_iff₀ hθ0).mp hle
      have hsum_nat : ∑ p ∈ Finset.Ico 1 (M + 1), (p : ℝ) ≤ (M : ℝ) * ((M : ℝ) + 1) / 2 := by
        clear hsplit hMeq hMθ hgt1 hM_eq1
        induction M with
        | zero => simp
        | succ m ih =>
          rw [Finset.sum_Ico_succ_top (by omega)]
          push_cast
          linarith
      calc
        ∑ p ∈ Finset.Ico 1 (M + 1), (p : ℝ) * |bandCoeff θ (p : ℤ)| ^ 2
            ≤ ∑ p ∈ Finset.Ico 1 (M + 1), (p : ℝ) * θ ^ 2 := by
          refine Finset.sum_le_sum fun p hp => ?_
          exact mul_le_mul_of_nonneg_left
            (bandCoeff_sq_le_theta_sq hθ0 (Finset.mem_Ico.mp hp).1) (Nat.cast_nonneg p)
        _ = (∑ p ∈ Finset.Ico 1 (M + 1), (p : ℝ)) * θ ^ 2 := by rw [← Finset.sum_mul]
        _ ≤ ((M : ℝ) * ((M : ℝ) + 1) / 2) * θ ^ 2 :=
          mul_le_mul_of_nonneg_right hsum_nat (sq_nonneg θ)
        _ = ((M : ℝ) * θ) * ((M : ℝ) * θ + θ) / 2 := by ring
        _ ≤ 1 * (1 + Real.pi) / 2 := by
          have h1 : (M : ℝ) * θ + θ ≤ 1 + Real.pi := by linarith
          have h2 : 0 ≤ (M : ℝ) * θ := by positivity
          have h3 : 0 ≤ (M : ℝ) * θ + θ := by positivity
          nlinarith [mul_le_mul hMθ h1 h3 zero_le_one]
        _ ≤ 4 := by linarith [Real.pi_lt_four]
  have h_large : ∑ p ∈ Finset.Ico (M + 1) K, (p : ℝ) * |bandCoeff θ (p : ℤ)| ^ 2 ≤
      Real.log 2 + Real.log ((K : ℝ) * θ) := by
    by_cases hMK : M + 1 < K
    · calc
        ∑ p ∈ Finset.Ico (M + 1) K, (p : ℝ) * |bandCoeff θ (p : ℤ)| ^ 2
            ≤ ∑ p ∈ Finset.Ico (M + 1) K, (1 / (p : ℝ)) := by
          refine Finset.sum_le_sum fun p hp => ?_
          have hp1 : 1 ≤ p := by
            have := (Finset.mem_Ico.mp hp).1; omega
          have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr (by omega)
          calc
            (p : ℝ) * |bandCoeff θ (p : ℤ)| ^ 2 ≤ (p : ℝ) * (1 / (p : ℝ) ^ 2) :=
              mul_le_mul_of_nonneg_left (bandCoeff_sq_le_inv_sq θ hp1) hp_pos.le
            _ = 1 / (p : ℝ) := by field_simp [ne_of_gt hp_pos]
        _ ≤ Real.log (((K - 1 : ℕ) : ℝ)) - Real.log (((M + 1 - 1 : ℕ) : ℝ)) :=
          sum_inv_Ico_le_log (by omega) hMK.le
        _ = Real.log (((K - 1 : ℕ) : ℝ) / (M : ℝ)) := by
          have hsub : M + 1 - 1 = M := by omega
          rw [hsub]
          have hKm1_pos : (0 : ℝ) < (((K - 1 : ℕ) : ℝ)) := Nat.cast_pos.mpr (by omega)
          have hM_pos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr (by omega)
          exact (Real.log_div (ne_of_gt hKm1_pos) (ne_of_gt hM_pos)).symm
        _ ≤ Real.log (2 * ((K : ℝ) * θ)) := by
          have hKm1_pos : (0 : ℝ) < (((K - 1 : ℕ) : ℝ)) := Nat.cast_pos.mpr (by omega)
          have hM_pos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr (by omega)
          refine Real.log_le_log (div_pos hKm1_pos hM_pos) ?_
          rw [div_le_iff₀ hM_pos]
          have hKm1_le : (((K - 1 : ℕ) : ℝ)) ≤ (K : ℝ) := by exact_mod_cast Nat.sub_le K 1
          have h2Mθ : 1 ≤ 2 * θ * (M : ℝ) := by
            by_cases h1θ : 1 / θ < 2
            · have hθ_gt : (1 / 2 : ℝ) < θ := by
                have h := (div_lt_iff₀ hθ0).mp h1θ
                linarith
              have hM_ge1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
              nlinarith
            · have h1θ_ge : 2 ≤ 1 / θ := not_lt.mp h1θ
              have hfl : 1 / θ - 1 < (⌊1 / θ⌋₊ : ℝ) := Nat.sub_one_lt_floor _
              have hhalf : (1 / (2 * θ)) ≤ 1 / θ - 1 := by
                have h : 1 / (2 * θ) = (1 / θ) / 2 := by ring
                linarith
              have hM_ge : (⌊1 / θ⌋₊ : ℝ) ≤ (M : ℝ) := by exact_mod_cast (le_max_right 1 ⌊1 / θ⌋₊)
              have hM_gt : 1 / (2 * θ) < (M : ℝ) := lt_of_le_of_lt hhalf (lt_of_lt_of_le hfl hM_ge)
              have hmul := mul_lt_mul_of_pos_left hM_gt (by positivity : 0 < 2 * θ)
              have hsimp : (2 * θ) * (1 / (2 * θ)) = 1 := by field_simp [ne_of_gt hθ0]
              linarith
          calc
            (((K - 1 : ℕ) : ℝ)) ≤ (K : ℝ) * 1 := by linarith
            _ ≤ (K : ℝ) * (2 * θ * (M : ℝ)) :=
              mul_le_mul_of_nonneg_left h2Mθ (Nat.cast_nonneg K)
            _ = 2 * ((K : ℝ) * θ) * (M : ℝ) := by ring
        _ = Real.log 2 + Real.log ((K : ℝ) * θ) :=
          Real.log_mul (by norm_num) (by linarith)
    · have hemp : Finset.Ico (M + 1) K = ∅ := Finset.Ico_eq_empty_iff.mpr hMK
      rw [hemp, Finset.sum_empty]
      have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      have hlogX : 0 ≤ Real.log ((K : ℝ) * θ) := Real.log_nonneg (by linarith)
      linarith
  have hlog4_gt1 : 1 < Real.log 4 := by
    have he : Real.exp 1 < 4 := by linarith [Real.exp_one_lt_d9]
    exact (Real.lt_log_iff_exp_lt (by norm_num)).mpr he
  have hlogX_gt1 : 1 < Real.log ((K : ℝ) * θ) :=
    lt_of_lt_of_le hlog4_gt1 (Real.log_le_log (by norm_num) hX)
  have hlog2_lt1 : Real.log 2 < 1 := by
    have he : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    exact (Real.log_lt_iff_lt_exp (by norm_num)).mpr he
  linarith

end AuxClaim314

theorem solution :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ (K : ℕ) (θ : ℝ), 0 < θ → θ ≤ Real.pi → X₀ ≤ (K : ℝ) * θ →
      ‖(bandMatrix K θ - bandMatrix K θ * bandMatrix K θ).trace‖ ≤
        C * Real.log ((K : ℝ) * θ) := by
  refine ⟨16, 4, by norm_num, fun K θ hθ0 hθπ hX => ?_⟩
  have hK2 : 2 ≤ K := by
    by_contra hlt
    have hKle1 : (K : ℝ) ≤ 1 := by
      have : K ≤ 1 := by omega
      exact_mod_cast this
    have hpi4 : Real.pi < 4 := Real.pi_lt_four
    nlinarith
  have h13 := lemma_3_13 K θ hθ0 hθπ
  have htrB := h13.2.1.2.1
  have hsum := h13.2.1.2.2
  have htrB2 := h13.2.2
  let D : ℝ := (K : ℝ) * bandCoeff θ 0 -
    ((K : ℝ) * |bandCoeff θ 0| ^ 2 +
      2 * ∑ p ∈ Finset.Ico 1 K, ((K : ℝ) - p) * |bandCoeff θ (p : ℤ)| ^ 2)
  have htr_eq : (bandMatrix K θ - bandMatrix K θ * bandMatrix K θ).trace = ((D : ℝ) : ℂ) := by
    rw [Matrix.trace_sub, htrB, htrB2]
    dsimp [D]
    push_cast
    ring
  have hD_decomp : D = (K : ℝ) * (bandCoeff θ 0 - |bandCoeff θ 0| ^ 2 -
      2 * ∑ p ∈ Finset.Ico 1 K, |bandCoeff θ (p : ℤ)| ^ 2) +
      2 * ∑ p ∈ Finset.Ico 1 K, (p : ℝ) * |bandCoeff θ (p : ℤ)| ^ 2 := by
    dsimp [D]
    have h1 : (∑ p ∈ Finset.Ico 1 K, ((K : ℝ) - p) * |bandCoeff θ (p : ℤ)| ^ 2) =
        (K : ℝ) * (∑ p ∈ Finset.Ico 1 K, |bandCoeff θ (p : ℤ)| ^ 2) -
        (∑ p ∈ Finset.Ico 1 K, (p : ℝ) * |bandCoeff θ (p : ℤ)| ^ 2) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun p _ => by ring
    linarith
  have hD_nn : 0 ≤ D := by
    let S_mid : Finset ℤ := Finset.Icc (-((K : ℤ) - 1)) ((K : ℤ) - 1)
    have hmid_le : ∑ p ∈ S_mid, |bandCoeff θ p| ^ 2 ≤ bandCoeff θ 0 :=
      sum_le_hasSum S_mid (fun _ _ => sq_nonneg _) hsum
    have hmid_eq : ∑ p ∈ S_mid, |bandCoeff θ p| ^ 2 =
        |bandCoeff θ 0| ^ 2 + 2 * ∑ p ∈ Finset.Ico 1 K, |bandCoeff θ (p : ℤ)| ^ 2 :=
      AuxClaim314.mid_sum_eq θ hK2
    have hrem_nn : 0 ≤ bandCoeff θ 0 - |bandCoeff θ 0| ^ 2 -
        2 * ∑ p ∈ Finset.Ico 1 K, |bandCoeff θ (p : ℤ)| ^ 2 := by linarith
    have hsum_nn : 0 ≤ 2 * ∑ p ∈ Finset.Ico 1 K, (p : ℝ) * |bandCoeff θ (p : ℤ)| ^ 2 :=
      mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => by positivity)
    rw [hD_decomp]
    exact add_nonneg (mul_nonneg (Nat.cast_nonneg K) hrem_nn) hsum_nn
  have hK_pos : (0 : ℝ) < (K : ℝ) := Nat.cast_pos.mpr (by omega)
  have hpart1 : (K : ℝ) * (bandCoeff θ 0 - |bandCoeff θ 0| ^ 2 -
      2 * ∑ p ∈ Finset.Ico 1 K, |bandCoeff θ (p : ℤ)| ^ 2) ≤ 4 := by
    calc
      (K : ℝ) * (bandCoeff θ 0 - |bandCoeff θ 0| ^ 2 -
          2 * ∑ p ∈ Finset.Ico 1 K, |bandCoeff θ (p : ℤ)| ^ 2)
          ≤ (K : ℝ) * (4 / (K : ℝ)) :=
        mul_le_mul_of_nonneg_left (AuxClaim314.tail_bound hK2 hsum) hK_pos.le
      _ = 4 := mul_div_cancel₀ 4 (ne_of_gt hK_pos)
  have hpart2 := AuxClaim314.weighted_mid_bound hθ0 hθπ hK2 hX
  have hlogX_gt1 : 1 < Real.log ((K : ℝ) * θ) := by
    have hlog4 : 1 < Real.log 4 := by
      have he : Real.exp 1 < 4 := by linarith [Real.exp_one_lt_d9]
      exact (Real.lt_log_iff_exp_lt (by norm_num)).mpr he
    exact lt_of_lt_of_le hlog4 (Real.log_le_log (by norm_num) hX)
  rw [htr_eq, Complex.norm_real, Real.norm_of_nonneg hD_nn, hD_decomp]
  linarith
