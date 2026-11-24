-- Prove2me | solution 1 for FairShareAlmostAll.Slack.bucket_supply
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T17:15:08.181496+00:00
-- url     : https://prove2.me/submissions/904d0802-444e-4756-8f73-43c0fd1d8efa

import Mathlib
import Definitions.Def_AnyPriceShare_Bidding_Basic
import Definitions.Def_FairShareAlmostAll_Slack_FiniteAllocation
import Definitions.Def_FairShareAlmostAll_Slack_Instance
import Definitions.Def_FairShareAlmostAll_Slack_Buckets

open FairShareAlmostAll.Slack

namespace BucketSupplyAux

theorem rank_card {m : ℕ} (s : Finset (Fin m)) (k : ℕ) (hk : k ≤ s.card) :
    (s.filter (fun g => (s.filter (fun r => r < g)).card < k)).card = k := by
  classical
  have hmono : ∀ a ∈ s, ∀ b ∈ s, a < b →
      (s.filter (fun r => r < a)).card < (s.filter (fun r => r < b)).card := by
    intro a ha b hb hab
    apply Finset.card_lt_card
    refine (Finset.ssubset_iff_of_subset ?_).mpr ⟨a, ?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, hx.2.trans hab⟩
    · simp [ha, hab]
    · simp
  have hinj : Set.InjOn (fun g => (s.filter (fun r => r < g)).card) s := by
    intro a ha b hb hab
    rcases lt_trichotomy a b with h | h | h
    · exact absurd hab (hmono a ha b hb h).ne
    · exact h
    · exact absurd hab (hmono b hb a ha h).ne'
  have hsub : s.image (fun g => (s.filter (fun r => r < g)).card) ⊆ Finset.range s.card := by
    intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨g, hg, rfl⟩ := hx
    simp only [Finset.mem_range]
    apply Finset.card_lt_card
    exact (Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)).mpr ⟨g, hg, by simp⟩
  have himg : s.image (fun g => (s.filter (fun r => r < g)).card) = Finset.range s.card :=
    Finset.eq_of_subset_of_card_le hsub
      (by rw [Finset.card_range, Finset.card_image_of_injOn hinj])
  have hfin : (s.filter (fun g => (s.filter (fun r => r < g)).card < k)).image
      (fun g => (s.filter (fun r => r < g)).card) = Finset.range k := by
    ext x
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨g, ⟨_, hg⟩, rfl⟩
      exact hg
    · intro hx
      have hx' : x ∈ s.image (fun g => (s.filter (fun r => r < g)).card) := by
        rw [himg, Finset.mem_range]; omega
      simp only [Finset.mem_image] at hx'
      obtain ⟨g, hg, hgx⟩ := hx'
      exact ⟨g, ⟨hg, hgx ▸ hx⟩, hgx⟩
  rw [← Finset.card_image_of_injOn (hinj.mono (by
    intro x hx; exact (Finset.mem_filter.mp hx).1)), hfin, Finset.card_range]

theorem mem_bucket {q m h : ℕ} (g : Fin m) :
    g ∈ bucket q m h ↔ prefixSize q (h - 1) ≤ g.val ∧ g.val < prefixSize q h := by
  unfold bucket
  simp

theorem mem_reserve {q m : ℕ} (g : Fin m) : g ∈ reserve q m ↔ g.val % q = 0 := by
  unfold reserve
  simp

theorem available_card {q m h : ℕ} (hq : 2 ≤ q) :
    (bucket q m h).card / q ≤ (bucket q m h \ reserve q m).card := by
  classical
  set a := prefixSize q (h - 1)
  set L := (bucket q m h).card
  have hL : L ≤ min (prefixSize q h) m - a := by
    have hsub : (bucket q m h).map Fin.valEmbedding ⊆ Finset.Ico a (min (prefixSize q h) m) := by
      intro x hx
      simp only [Finset.mem_map, Fin.valEmbedding_apply] at hx
      obtain ⟨g, hg, rfl⟩ := hx
      rw [mem_bucket] at hg
      simp only [Finset.mem_Ico]
      have := g.isLt
      omega
    have := Finset.card_le_card hsub
    rw [Finset.card_map, Nat.card_Ico] at this
    exact this
  set c : ℕ := if a % q = 0 then 1 else 0 with hc
  have hc1 : c ≤ 1 := by rw [hc]; split_ifs <;> omega
  have hqpos : 0 < q := by omega
  have himage : (Finset.range (L / q)).image (fun t => a + c + t * q) ⊆
      (bucket q m h \ reserve q m).map Fin.valEmbedding := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_range] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    have ht' : (t + 1) * q ≤ L := (Nat.le_div_iff_mul_le hqpos).mp ht
    have hmod : (a + c + t * q) % q ≠ 0 := by
      rw [Nat.add_mul_mod_self_right]
      rw [hc]
      split_ifs with h0
      · rw [Nat.add_mod, h0]
        simp
        omega
      · simpa using h0
    have hlt : a + c + t * q < min (prefixSize q h) m := by
      have : t * q + q ≤ L := by rw [Nat.add_mul, one_mul] at ht'; exact ht'
      generalize t * q = u at *
      omega
    simp only [Finset.mem_map, Fin.valEmbedding_apply]
    refine ⟨⟨a + c + t * q, by omega⟩, ?_, rfl⟩
    rw [Finset.mem_sdiff, mem_bucket, mem_reserve]
    refine ⟨⟨?_, ?_⟩, hmod⟩
    · show a ≤ a + c + t * q
      omega
    · show a + c + t * q < prefixSize q h
      omega
  have hinj : Set.InjOn (fun t => a + c + t * q) (Finset.range (L / q) : Set ℕ) := by
    intro x _ y _ hxy
    simp only at hxy
    have : x * q = y * q := by omega
    exact Nat.eq_of_mul_eq_mul_right hqpos this
  have := Finset.card_le_card himage
  rw [Finset.card_image_of_injOn hinj, Finset.card_range, Finset.card_map] at this
  exact this

theorem buffer_card {q m h : ℕ} (hq : 2 ≤ q) :
    (bucket q m h).card / q = (buffer q m h).card := by
  classical
  have hbuf : buffer q m h = (bucket q m h \ reserve q m).filter (fun g =>
      ((bucket q m h \ reserve q m).filter (fun r => r < g)).card < (bucket q m h).card / q) := by
    unfold buffer
    rfl
  rw [hbuf, rank_card _ _ (available_card hq)]

theorem presc_bounds (q k : ℕ) :
    (q : ℝ) * (1 + 1 / (q : ℝ)) ^ k ≤ prescribedSize q (k + 1) ∧
      (prescribedSize q (k + 1) : ℝ) < (q : ℝ) * (1 + 1 / (q : ℝ)) ^ k + 1 := by
  unfold prescribedSize
  simp only [Nat.add_sub_cancel]
  exact ⟨Nat.le_ceil _, Nat.ceil_lt_add_one (by positivity)⟩

theorem presc_ge (q k : ℕ) : q ≤ prescribedSize q k := by
  unfold prescribedSize
  have h0 : (0 : ℝ) ≤ 1 / (q : ℝ) := by positivity
  have h1 : (1 : ℝ) ≤ (1 + 1 / (q : ℝ)) ^ (k - 1) := one_le_pow₀ (by linarith)
  have h2 : (q : ℝ) ≤ (q : ℝ) * (1 + 1 / (q : ℝ)) ^ (k - 1) :=
    le_mul_of_one_le_right (Nat.cast_nonneg _) h1
  exact_mod_cast h2.trans (Nat.le_ceil _)

theorem presc_one (q : ℕ) : prescribedSize q 1 = q := by
  unfold prescribedSize
  simp

theorem prefix_succ (q k : ℕ) :
    prefixSize q (k + 1) = prefixSize q k + prescribedSize q (k + 1) := by
  unfold prefixSize
  rw [Finset.sum_range_succ]

theorem prefix_zero (q : ℕ) : prefixSize q 0 = 0 := by
  unfold prefixSize
  simp

theorem prefix_mono (q : ℕ) {a b : ℕ} (h : a ≤ b) : prefixSize q a ≤ prefixSize q b := by
  unfold prefixSize
  exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr h)

theorem prefix_ge (q h : ℕ) : h * q ≤ prefixSize q h := by
  induction h with
  | zero => simp [prefix_zero]
  | succ k ih =>
    rw [prefix_succ, add_mul, one_mul]
    have := presc_ge q (k + 1)
    omega

theorem prefix_diff (q j : ℕ) (hj : 1 ≤ j) :
    prefixSize q j - prefixSize q (j - 1) = prescribedSize q j := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  rw [Nat.add_sub_cancel, prefix_succ]
  omega

theorem bucket_card_le (q m h : ℕ) :
    (bucket q m h).card ≤ prefixSize q h - prefixSize q (h - 1) := by
  have hsub : (bucket q m h).map Fin.valEmbedding ⊆
      Finset.Ico (prefixSize q (h - 1)) (prefixSize q h) := by
    intro x hx
    simp only [Finset.mem_map, Fin.valEmbedding_apply] at hx
    obtain ⟨g, hg, rfl⟩ := hx
    rw [mem_bucket] at hg
    simp only [Finset.mem_Ico]
    exact hg
  have := Finset.card_le_card hsub
  rw [Finset.card_map, Nat.card_Ico] at this
  exact this

theorem bucket_card_full (q m h : ℕ) (hm : prefixSize q h ≤ m) :
    prefixSize q h - prefixSize q (h - 1) ≤ (bucket q m h).card := by
  have hsub : Finset.Ico (prefixSize q (h - 1)) (prefixSize q h) ⊆
      (bucket q m h).map Fin.valEmbedding := by
    intro x hx
    simp only [Finset.mem_Ico] at hx
    simp only [Finset.mem_map, Fin.valEmbedding_apply]
    exact ⟨⟨x, by omega⟩, (mem_bucket _).mpr hx, rfl⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_map, Nat.card_Ico] at this
  exact this

theorem bucket_disj {q m h₁ h₂ : ℕ} (g : Fin m) (g₁ : g ∈ bucket q m h₁)
    (g₂ : g ∈ bucket q m h₂) : h₁ = h₂ := by
  rw [mem_bucket] at g₁ g₂
  rcases lt_trichotomy h₁ h₂ with h | h | h
  · have := prefix_mono q (show h₁ ≤ h₂ - 1 by omega)
    omega
  · exact h
  · have := prefix_mono q (show h₂ ≤ h₁ - 1 by omega)
    omega

theorem mult_gap {q x y : ℕ} (hq : 0 < q) (hx : x % q = 0) (hy : y % q = 0) (hxy : x < y) :
    x + q ≤ y := by
  obtain ⟨s, rfl⟩ := Nat.dvd_of_mod_eq_zero hx
  obtain ⟨t, rfl⟩ := Nat.dvd_of_mod_eq_zero hy
  have hst : s < t := Nat.lt_of_mul_lt_mul_left hxy
  have : q * (s + 1) ≤ q * t := Nat.mul_le_mul_left q hst
  rw [mul_add, mul_one] at this
  exact this

theorem div_gap {q a x y : ℕ} (hq : 0 < q) (hx : a ≤ x) (hxy : x + q ≤ y) :
    (x - a) / q < (y - a) / q := by
  have h1 : (x - a) + q ≤ y - a := by omega
  calc (x - a) / q < (x - a) / q + 1 := Nat.lt_succ_self _
    _ = ((x - a) + q) / q := (Nat.add_div_right _ hq).symm
    _ ≤ (y - a) / q := Nat.div_le_div_right h1

theorem reserve_count (q m h : ℕ) (hq : 0 < q) :
    (reserve q m ∩ bucket q m h).card ≤
      (prefixSize q h - prefixSize q (h - 1) - 1) / q + 1 := by
  set a := prefixSize q (h - 1)
  set L := prefixSize q h - prefixSize q (h - 1)
  have hmaps : ∀ g ∈ reserve q m ∩ bucket q m h, (g.val - a) / q ∈ Finset.range ((L - 1) / q + 1) := by
    intro g hg
    rw [Finset.mem_inter, mem_bucket] at hg
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact Nat.div_le_div_right (by omega)
  have hinj : Set.InjOn (fun g : Fin m => (g.val - a) / q) ((reserve q m ∩ bucket q m h : Finset (Fin m)) : Set (Fin m)) := by
    intro g₁ hg₁ g₂ hg₂ heq
    simp only [Finset.coe_inter, Set.mem_inter_iff, Finset.mem_coe, mem_bucket, mem_reserve] at hg₁ hg₂
    simp only at heq
    rcases lt_trichotomy g₁.val g₂.val with hlt | heq' | hlt
    · exact absurd heq (div_gap hq hg₁.2.1 (mult_gap hq hg₁.1 hg₂.1 hlt)).ne
    · exact Fin.ext heq'
    · exact absurd heq (div_gap hq hg₂.2.1 (mult_gap hq hg₂.1 hg₁.1 hlt)).ne'
  have := Finset.card_le_card_of_injOn _ hmaps hinj
  rwa [Finset.card_range] at this

theorem mem_ordinaryBucket {q m h : ℕ} (g : Fin m) :
    g ∈ ordinaryBucket q m h ↔
      (g ∉ reserve q m ∧ ∀ k ∈ Finset.Icc 1 (bucketCount q m), g ∉ buffer q m k) ∧
        g ∈ bucket q m h := by
  unfold ordinaryBucket ordinary allBuffers
  simp

theorem buffer_sub {q m h : ℕ} : buffer q m h ⊆ bucket q m h \ reserve q m := by
  intro g hg
  unfold buffer at hg
  exact (Finset.mem_filter.mp hg).1

theorem anyPrice_nonpos {m : ℕ} (b : ℝ) (v : Fin m → ℝ) (hv : ∀ g, 0 ≤ v g)
    (hmb : (m : ℝ) * b < 1) :
    AnyPriceShare.Bidding.anyPrice b (AnyPriceShare.Bidding.addVal v) Finset.univ ≤ 0 := by
  unfold AnyPriceShare.Bidding.anyPrice
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    haveI : IsEmpty {p : Fin 0 → ℝ // (∀ j ∈ (Finset.univ : Finset (Fin 0)), 0 ≤ p j) ∧
        ∑ j ∈ (Finset.univ : Finset (Fin 0)), p j = 1} :=
      ⟨fun p => by have := p.2.2; simp at this⟩
    rw [Real.iInf_of_isEmpty]
  · have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    refine ciInf_le_of_le ⟨0, ?_⟩ ⟨fun _ => 1 / (m : ℝ), fun _ _ => by positivity, ?_⟩ ?_
    · rintro _ ⟨p, rfl⟩
      exact Real.iSup_nonneg (fun T => Finset.sum_nonneg (fun g _ => hv g))
    · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    · apply Real.iSup_nonpos
      intro T
      have hT := T.2.2
      dsimp only at hT
      rw [Finset.sum_const, nsmul_eq_mul] at hT
      have hcard : T.1.card = 0 := by
        by_contra hc
        have h1 : (1 : ℝ) ≤ T.1.card := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hc
        have h2 : (T.1.card : ℝ) ≤ b * m := by
          rwa [mul_one_div, div_le_iff₀ hmR] at hT
        nlinarith
      rw [Finset.card_eq_zero.mp hcard]
      simp [AnyPriceShare.Bidding.addVal]

end BucketSupplyAux

open BucketSupplyAux in
theorem solution {n m : ℕ} (X : Instance n m) (q : ℕ) (h : ConstructionAssumptions X q) :
    q^2 ≤ m ∧ 2 ≤ bucketCount q m ∧
    m ≤ prefixSize q (bucketCount q m) ∧
    (∀ k, 0 < k → k < bucketCount q m → prefixSize q k < m) ∧
    ((Finset.Icc 1 (bucketCount q m)).biUnion (bucket q m) = Finset.univ) ∧
    (∀ j ∈ Finset.Icc 1 (bucketCount q m),
      0 < (bucket q m j).card ∧
      (buffer q m j).card = (bucket q m j).card / q) ∧
    (∀ j ∈ Finset.Icc 2 (bucketCount q m),
      ((bucket q m j).card : ℝ) ≤ (1 + 2 / (q : ℝ)) * (bucket q m (j - 1)).card) ∧
    (∀ j ∈ Finset.Ico 1 (bucketCount q m),
      (1 - 3 / (q : ℝ)) * (bucket q m j).card ≤ (ordinaryBucket q m j).card) := by
  classical
  obtain ⟨_, hq16, _, hb, hact, _⟩ := h
  have hq2 : 2 ≤ q := by omega
  have hqpos : 0 < q := by omega
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqpos
  -- q² ≤ m
  have hm : q ^ 2 ≤ m := by
    obtain ⟨i, hi⟩ := hact
    have hti : 0 < target X i := by
      unfold active at hi
      exact (Finset.mem_filter.mp hi).2
    by_contra hlt
    push_neg at hlt
    have hltR : (m : ℝ) < (q : ℝ) ^ 2 := by exact_mod_cast hlt
    have hq2R : (0 : ℝ) < (q : ℝ) ^ 2 := by positivity
    have hmb : (m : ℝ) * X.entitlement i < 1 := by
      calc (m : ℝ) * X.entitlement i ≤ (m : ℝ) * (1 / (q : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left (hb i) (Nat.cast_nonneg _)
        _ = (m : ℝ) / (q : ℝ) ^ 2 := by ring
        _ < 1 := by rw [div_lt_one hq2R]; exact hltR
    have := anyPrice_nonpos (X.entitlement i) (X.value i) (X.value_nonneg i) hmb
    unfold target at hti
    linarith
  have hqq : q < q ^ 2 := by nlinarith
  have hmpos : 0 < m := by omega
  -- bucket count
  have hne : {h : ℕ | 0 < h ∧ m ≤ prefixSize q h}.Nonempty :=
    ⟨m, hmpos, le_trans (by nlinarith) (prefix_ge q m)⟩
  have hbcdef : bucketCount q m = sInf {h : ℕ | 0 < h ∧ m ≤ prefixSize q h} := rfl
  have hbcmem : 0 < bucketCount q m ∧ m ≤ prefixSize q (bucketCount q m) := by
    rw [hbcdef]; exact Nat.sInf_mem hne
  have hmin : ∀ k, 0 < k → k < bucketCount q m → prefixSize q k < m := by
    intro k hk hkb
    by_contra hc
    push_neg at hc
    have : bucketCount q m ≤ k := by rw [hbcdef]; exact Nat.sInf_le ⟨hk, hc⟩
    omega
  have hP1 : prefixSize q 1 = q := by
    rw [prefix_succ, prefix_zero, presc_one]; simp
  have hbc2 : 2 ≤ bucketCount q m := by
    by_contra hc
    have h1 : bucketCount q m = 1 := by omega
    have := hbcmem.2
    rw [h1, hP1] at this
    omega
  set bc := bucketCount q m with hbc
  -- full buckets
  have hfull : ∀ j, 1 ≤ j → j < bc → (bucket q m j).card = prescribedSize q j := by
    intro j hj1 hjb
    have hle := bucket_card_le q m j
    have hge := bucket_card_full q m j (hmin j hj1 hjb).le
    rw [prefix_diff q j hj1] at hle hge
    omega
  refine ⟨hm, hbc2, hbcmem.2, hmin, ?_, ?_, ?_, ?_⟩
  · -- union
    apply Finset.eq_univ_iff_forall.mpr
    intro g
    have hex : ∃ h, g.val < prefixSize q h := ⟨bc, lt_of_lt_of_le g.isLt hbcmem.2⟩
    have hspec := Nat.find_spec hex
    have hmin' := Nat.find_min' hex (lt_of_lt_of_le g.isLt hbcmem.2)
    have hpos : Nat.find hex ≠ 0 := by
      intro h0
      rw [h0, prefix_zero] at hspec
      omega
    have hprev : ¬ g.val < prefixSize q (Nat.find hex - 1) := Nat.find_min hex (by omega)
    refine Finset.mem_biUnion.mpr ⟨Nat.find hex, Finset.mem_Icc.mpr ⟨by omega, hmin'⟩, ?_⟩
    exact (mem_bucket g).mpr ⟨by omega, hspec⟩
  · intro j hj
    rw [Finset.mem_Icc] at hj
    refine ⟨?_, (buffer_card hq2).symm⟩
    have hprev : prefixSize q (j - 1) < m := by
      rcases Nat.eq_or_lt_of_le hj.1 with h1 | h1
      · rw [← h1, Nat.sub_self, prefix_zero]; exact hmpos
      · exact hmin (j - 1) (by omega) (by omega)
    have hstep : prefixSize q (j - 1) < prefixSize q j := by
      have := prefix_diff q j hj.1
      have := presc_ge q j
      have := prefix_mono q (show j - 1 ≤ j by omega)
      omega
    exact Finset.card_pos.mpr ⟨⟨prefixSize q (j - 1), hprev⟩, (mem_bucket _).mpr ⟨le_refl _, hstep⟩⟩
  · intro j hj
    rw [Finset.mem_Icc] at hj
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
    have hk1 : k + 2 - 1 = k + 1 := by omega
    rw [hk1]
    have hc1 : (bucket q m (k + 1)).card = prescribedSize q (k + 1) :=
      hfull (k + 1) (by omega) (by omega)
    have hc2 : (bucket q m (k + 2)).card ≤ prescribedSize q (k + 2) := by
      have := bucket_card_le q m (k + 2)
      rw [prefix_diff q (k + 2) (by omega)] at this
      exact this
    have hc2R : ((bucket q m (k + 2)).card : ℝ) ≤ prescribedSize q (k + 2) := by
      exact_mod_cast hc2
    rw [hc1]
    obtain ⟨hlo, _⟩ := presc_bounds q k
    obtain ⟨_, hhi⟩ := presc_bounds q (k + 1)
    set R := (1 + 1 / (q : ℝ)) ^ k with hR
    have hq0 : (0 : ℝ) ≤ 1 / (q : ℝ) := by positivity
    have hR1 : (1 : ℝ) ≤ R := one_le_pow₀ (by linarith)
    have e1 : (q : ℝ) * (1 + 1 / (q : ℝ)) ^ (k + 1) = q * R + R := by
      rw [pow_succ, ← hR]; field_simp
    have e2 : (1 + 2 / (q : ℝ)) * (q * R) = q * R + 2 * R := by field_simp
    have hpos2 : (0 : ℝ) ≤ 1 + 2 / (q : ℝ) := by positivity
    have := mul_le_mul_of_nonneg_left hlo hpos2
    have hk2 : (k + 1 + 1) = k + 2 := rfl
    rw [hk2] at hhi
    linarith
  · intro j hj
    rw [Finset.mem_Ico] at hj
    have hL := hfull j hj.1 hj.2
    set L := (bucket q m j).card with hLdef
    have hLq : q ≤ L := by rw [hL]; exact presc_ge q j
    set u := L / q with hu
    have hbuf := buffer_card (q := q) (m := m) (h := j) hq2
    -- reserve count
    have hres := reserve_count q m j hqpos
    rw [prefix_diff q j hj.1, ← hL] at hres
    have hres' : (reserve q m ∩ bucket q m j).card ≤ u + 1 := by
      have : (L - 1) / q ≤ L / q := Nat.div_le_div_right (by omega)
      omega
    -- available
    have havail : (bucket q m j \ reserve q m).card = L - (reserve q m ∩ bucket q m j).card :=
      Finset.card_sdiff
    -- ordinary ⊇ available \ buffer
    have hsub : (bucket q m j \ reserve q m) \ buffer q m j ⊆ ordinaryBucket q m j := by
      intro g hg
      rw [Finset.mem_sdiff, Finset.mem_sdiff] at hg
      rw [mem_ordinaryBucket]
      refine ⟨⟨hg.1.2, ?_⟩, hg.1.1⟩
      intro k _ hk
      have hgk : g ∈ bucket q m k := (Finset.mem_sdiff.mp (buffer_sub hk)).1
      have := bucket_disj g hgk hg.1.1
      subst this
      exact hg.2 hk
    have hord := Finset.card_le_card hsub
    rw [Finset.card_sdiff_of_subset buffer_sub, havail, ← hbuf] at hord
    have huL : u * q ≤ L := Nat.div_mul_le_self L q
    have hu1 : 1 ≤ u := (Nat.le_div_iff_mul_le hqpos).mpr (by omega)
    have hLc : (bucket q m j).card = L := rfl
    have hu' : u = L / q := rfl
    clear_value u L
    rw [hLc, ← hu'] at hord
    have hordN : L ≤ (ordinaryBucket q m j).card + 2 * u + 1 := by omega
    have hordR : (L : ℝ) ≤ (ordinaryBucket q m j).card + 2 * u + 1 := by exact_mod_cast hordN
    have huLR : (u : ℝ) * q ≤ L := by exact_mod_cast huL
    have hu1R : (1 : ℝ) ≤ u := by exact_mod_cast hu1
    have key : (2 * u + 1 : ℝ) ≤ 3 * L / q := by
      rw [le_div_iff₀ hqR]
      nlinarith
    have e : (1 - 3 / (q : ℝ)) * L = L - 3 * L / q := by ring
    rw [e]
    linarith
