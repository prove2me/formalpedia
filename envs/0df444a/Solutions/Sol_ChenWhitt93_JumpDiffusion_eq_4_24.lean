-- Prove2me | solution 1 for ChenWhitt93.JumpDiffusion.eq_4_24
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T20:51:19.501189+00:00
-- url     : https://prove2.me/submissions/b60d5844-912f-4bb7-8c74-0ece59eb7ec2

import Mathlib
import Definitions.Def_ChenWhitt93_JumpDiffusion_HeavyTraffic

open Filter Topology MeasureTheory Matrix

namespace Aux_CW42
open ChenWhitt93.JumpDiffusion

lemma cycleStart_succ {J : ℕ} (I : Interruptions J) (j : Fin J) (l : ℕ) :
    I.cycleStart j (l + 1) = I.cycleStart j l + (I.up j l + I.down j l) := by
  unfold Interruptions.cycleStart
  rw [Finset.sum_range_succ]

lemma cycleStart_zero {J : ℕ} (I : Interruptions J) (j : Fin J) : I.cycleStart j 0 = 0 := by
  unfold Interruptions.cycleStart
  simp

lemma cycleStart_mono {J : ℕ} (I : Interruptions J) (hI : I.IsValid) (j : Fin J) :
    Monotone (I.cycleStart j) := by
  apply monotone_nat_of_le_succ
  intro l
  rw [cycleStart_succ]
  linarith [(hI.1 j l).1, (hI.1 j l).2]

lemma up_of_not_down {J : ℕ} (I : Interruptions J) (hI : I.IsValid) (j : Fin J) (v : ℝ)
    (hv : 0 ≤ v) (hd : ¬ I.IsDown j v) : I.IsUp j v := by
  classical
  have hex : ∃ l, v < I.cycleStart j l :=
    ((hI.2 j).eventually (eventually_gt_atTop v)).exists
  have hspec := Nat.find_spec hex
  have hmin : ∀ m, m < Nat.find hex → ¬ v < I.cycleStart j m := fun m hm => Nat.find_min hex hm
  generalize Nat.find hex = l0 at hspec hmin
  cases l0 with
  | zero =>
    rw [cycleStart_zero] at hspec
    linarith
  | succ l =>
    have hle : I.cycleStart j l ≤ v := not_lt.mp (hmin l (Nat.lt_succ_self l))
    by_cases hup : v < I.cycleStart j l + I.up j l
    · exact ⟨l, hle, hup⟩
    · exact absurd ⟨l, not_lt.mp hup, hspec⟩ hd

lemma downTime_mono {J : ℕ} (I : Interruptions J) (j : Fin J) {a b : ℝ} (hab : a ≤ b) :
    I.downTime j a ≤ I.downTime j b := by
  unfold Interruptions.downTime
  exact measureReal_mono (fun x hx => ⟨Set.Icc_subset_Icc_right hab hx.1, hx.2⟩)
    (measure_ne_top_of_subset Set.inter_subset_left measure_Icc_lt_top.ne)

lemma downTime_nonneg {J : ℕ} (I : Interruptions J) (j : Fin J) (a : ℝ) :
    0 ≤ I.downTime j a := measureReal_nonneg

lemma downTime_le_sum {J : ℕ} (I : Interruptions J) (hI : I.IsValid) (j : Fin J) (τ : ℝ)
    (m : ℕ) (hm : τ < ∑ l ∈ Finset.range m, I.up j l) :
    I.downTime j τ ≤ ∑ l ∈ Finset.range m, I.down j l := by
  unfold Interruptions.downTime
  have hsub : Set.Icc 0 τ ∩ {s | I.IsDown j s} ⊆
      ⋃ l ∈ Finset.range m, Set.Ico (I.cycleStart j l + I.up j l) (I.cycleStart j (l + 1)) := by
    rintro v ⟨hv, l, hl1, hl2⟩
    simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_Ico]
    refine ⟨l, ?_, hl1, hl2⟩
    by_contra hlm
    push_neg at hlm
    have h1 : I.cycleStart j m ≤ I.cycleStart j l := cycleStart_mono I hI j hlm
    have h2 : ∑ l ∈ Finset.range m, I.up j l ≤ I.cycleStart j m := by
      unfold Interruptions.cycleStart
      apply Finset.sum_le_sum
      intro i _
      linarith [(hI.1 j i).2]
    have h3 : 0 ≤ I.up j l := (hI.1 j l).1
    linarith [hv.2]
  have hfin : volume (⋃ l ∈ Finset.range m,
      Set.Ico (I.cycleStart j l + I.up j l) (I.cycleStart j (l + 1))) ≠ ⊤ :=
    ((measure_biUnion_finset_le _ _).trans_lt
      (ENNReal.sum_lt_top.2 fun l _ => measure_Ico_lt_top)).ne
  calc volume.real (Set.Icc 0 τ ∩ {s | I.IsDown j s})
      ≤ volume.real (⋃ l ∈ Finset.range m,
          Set.Ico (I.cycleStart j l + I.up j l) (I.cycleStart j (l + 1))) :=
        measureReal_mono hsub hfin
    _ ≤ ∑ l ∈ Finset.range m,
          volume.real (Set.Ico (I.cycleStart j l + I.up j l) (I.cycleStart j (l + 1))) :=
        measureReal_biUnion_finset_le _ _
    _ = ∑ l ∈ Finset.range m, I.down j l := by
        apply Finset.sum_congr rfl
        intro l _
        have hle : I.cycleStart j l + I.up j l ≤ I.cycleStart j (l + 1) := by
          rw [cycleStart_succ]; linarith [(hI.1 j l).2]
        rw [Real.volume_real_Ico_of_le hle, cycleStart_succ]
        ring

lemma B_bounds {J : ℕ} (χ : Fin J → Fin J → ℕ → Bool) (N : NetworkData J)
    (Z : ℝ → Fin J → ℤ) (B : ℝ → Fin J → ℝ) (hsol : IsQueueSolution χ N Z B)
    (τ : ℝ) (hτ : 0 ≤ τ) (i : Fin J) : 0 ≤ B τ i ∧ B τ i ≤ τ := by
  rw [(hsol τ hτ i).2.2]
  refine ⟨measureReal_nonneg, ?_⟩
  calc _ ≤ volume.real (Set.Icc 0 τ) :=
        measureReal_mono (fun s hs => hs.1) measure_Icc_lt_top.ne
    _ = τ := by rw [Real.volume_real_Icc_of_le hτ, sub_zero]

lemma key_last_zero {J : ℕ} (χ : Fin J → Fin J → ℕ → Bool) (N : NetworkData J)
    (hN : N.IsValid χ) (Z : ℝ → Fin J → ℤ) (B : ℝ → Fin J → ℝ)
    (hsol : IsQueueSolution χ N Z B) (j : Fin J) (τ : ℝ) (hτ : 0 ≤ τ) :
    (τ - B τ j ≤ N.downTime j τ) ∨
    (∀ δ > 0, ∃ u ∈ Set.Icc 0 τ, Z u j = 0 ∧
      τ - B τ j ≤ u - B u j + δ + N.downTime j τ) := by
  have hBτ := (hsol τ hτ j).2.2
  have hfinG : ∀ a, volume ({s | s ∈ Set.Icc 0 τ ∧ 0 < Z s j ∧ N.IsUp j s} \ Set.Iic a) ≠ ⊤ :=
    fun a => measure_ne_top_of_subset (fun s hs => hs.1.1) measure_Icc_lt_top.ne
  have F1 : ∀ a, 0 ≤ a → a ≤ τ → (∀ v ∈ Set.Ioc a τ, 0 < Z v j) →
      τ - a - N.downTime j τ ≤
        volume.real ({s | s ∈ Set.Icc 0 τ ∧ 0 < Z s j ∧ N.IsUp j s} \ Set.Iic a) := by
    intro a ha0 haτ hpos
    have hsub1 : Set.Ioc a τ \ {s | N.IsDown j s} ⊆
        {s | s ∈ Set.Icc 0 τ ∧ 0 < Z s j ∧ N.IsUp j s} \ Set.Iic a := by
      rintro v ⟨⟨hv1, hv2⟩, hvD⟩
      refine ⟨⟨⟨by linarith, hv2⟩, hpos v ⟨hv1, hv2⟩,
        up_of_not_down N.toInterruptions hN.1 j v (by linarith) hvD⟩, ?_⟩
      simp only [Set.mem_Iic, not_le]
      exact hv1
    have hsub2 : Set.Ioc a τ ∩ {s | N.IsDown j s} ⊆ Set.Icc 0 τ ∩ {s | N.IsDown j s} :=
      fun v hv => ⟨⟨by linarith [hv.1.1], hv.1.2⟩, hv.2⟩
    have hcov : Set.Ioc a τ ⊆
        (Set.Ioc a τ \ {s | N.IsDown j s}) ∪ (Set.Ioc a τ ∩ {s | N.IsDown j s}) := by
      intro v hv
      by_cases h : v ∈ {s | N.IsDown j s}
      · exact Or.inr ⟨hv, h⟩
      · exact Or.inl ⟨hv, h⟩
    have e1 : volume.real (Set.Ioc a τ) = τ - a := Real.volume_real_Ioc_of_le haτ
    have e2 : volume.real (Set.Ioc a τ) ≤ volume.real
        ((Set.Ioc a τ \ {s | N.IsDown j s}) ∪ (Set.Ioc a τ ∩ {s | N.IsDown j s})) :=
      measureReal_mono hcov (measure_ne_top_of_subset (by
        rintro v (hv | hv)
        · exact hv.1
        · exact hv.1) measure_Ioc_lt_top.ne)
    have e3 := measureReal_union_le (μ := volume) (Set.Ioc a τ \ {s | N.IsDown j s})
      (Set.Ioc a τ ∩ {s | N.IsDown j s})
    have e4 := measureReal_mono (μ := volume) hsub1 (hfinG a)
    have e5 : volume.real (Set.Ioc a τ ∩ {s | N.IsDown j s}) ≤ N.downTime j τ :=
      measureReal_mono hsub2 (measure_ne_top_of_subset Set.inter_subset_left measure_Icc_lt_top.ne)
    linarith
  by_cases hU : ∃ u ∈ Set.Icc 0 τ, Z u j = 0
  · right
    intro δ hδ
    let U : Set ℝ := {u | u ∈ Set.Icc 0 τ ∧ Z u j = 0}
    have hmemU : ∀ v, v ∈ U ↔ (v ∈ Set.Icc 0 τ ∧ Z v j = 0) := fun v => Iff.rfl
    have hUne : U.Nonempty := by
      obtain ⟨u, hu, hz⟩ := hU
      exact ⟨u, (hmemU u).2 ⟨hu, hz⟩⟩
    have hUbdd : BddAbove U := ⟨τ, fun u hu => ((hmemU u).1 hu).1.2⟩
    have hsle : sSup U ≤ τ := csSup_le hUne (fun u hu => ((hmemU u).1 hu).1.2)
    obtain ⟨u, huU, hlt⟩ := exists_lt_of_lt_csSup hUne (show sSup U - δ < sSup U by linarith)
    have hus : u ≤ sSup U := le_csSup hUbdd huU
    have huU' := (hmemU u).1 huU
    have hs0 : 0 ≤ sSup U := le_trans huU'.1.1 hus
    refine ⟨u, huU'.1, huU'.2, ?_⟩
    have hpos : ∀ v ∈ Set.Ioc (sSup U) τ, 0 < Z v j := by
      intro v hv
      have hv0 : 0 ≤ v := by linarith [hv.1]
      rcases (hsol v hv0 j).1.lt_or_eq with h | h
      · exact h
      · exfalso
        have hvU : v ∈ U := (hmemU v).2 ⟨⟨hv0, hv.2⟩, h.symm⟩
        have := le_csSup hUbdd hvU
        linarith [hv.1]
    have hF := F1 (sSup U) hs0 hsle hpos
    have hBu := (hsol u huU'.1.1 j).2.2
    have hsplit := measureReal_inter_add_sdiff (μ := volume)
      (s := {s | s ∈ Set.Icc 0 τ ∧ 0 < Z s j ∧ N.IsUp j s}) (t := Set.Iic u) measurableSet_Iic
      (measure_ne_top_of_subset (fun s hs => hs.1) measure_Icc_lt_top.ne)
    have hinter : {s | s ∈ Set.Icc 0 τ ∧ 0 < Z s j ∧ N.IsUp j s} ∩ Set.Iic u =
        {s | s ∈ Set.Icc 0 u ∧ 0 < Z s j ∧ N.IsUp j s} := by
      ext v
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Icc, Set.mem_Iic]
      constructor
      · rintro ⟨⟨⟨h1, _⟩, h3, h4⟩, h5⟩
        exact ⟨⟨h1, h5⟩, h3, h4⟩
      · rintro ⟨⟨h1, h2⟩, h3, h4⟩
        exact ⟨⟨⟨h1, h2.trans huU'.1.2⟩, h3, h4⟩, h2⟩
    have hmono : volume.real ({s | s ∈ Set.Icc 0 τ ∧ 0 < Z s j ∧ N.IsUp j s} \ Set.Iic (sSup U))
        ≤ volume.real ({s | s ∈ Set.Icc 0 τ ∧ 0 < Z s j ∧ N.IsUp j s} \ Set.Iic u) :=
      measureReal_mono (Set.diff_subset_diff_right (Set.Iic_subset_Iic.2 hus)) (hfinG u)
    rw [hinter, ← hBu, ← hBτ] at hsplit
    linarith
  · left
    push_neg at hU
    have hpos : ∀ v ∈ Set.Ioc 0 τ, 0 < Z v j := by
      intro v hv
      exact lt_of_le_of_ne (hsol v hv.1.le j).1 (fun h => hU v ⟨hv.1.le, hv.2⟩ h.symm)
    have hF := F1 0 le_rfl hτ hpos
    have hmono : volume.real ({s | s ∈ Set.Icc 0 τ ∧ 0 < Z s j ∧ N.IsUp j s} \ Set.Iic 0)
        ≤ B τ j := by
      rw [hBτ]
      exact measureReal_mono Set.diff_subset
        (measure_ne_top_of_subset (fun s hs => hs.1) measure_Icc_lt_top.ne)
    linarith

def Cst (J : ℕ) : ℕ → ℝ
  | 0 => 0
  | m + 1 => (J : ℝ) * Cst J m + 1

lemma Cst_nonneg (J m : ℕ) : 0 ≤ Cst J m := by
  induction m with
  | zero => simp [Cst]
  | succ m ih =>
    simp only [Cst]
    exact add_nonneg (mul_nonneg (Nat.cast_nonneg J) ih) zero_le_one

lemma tmul_apply {J : ℕ} (P : Matrix (Fin J) (Fin J) ℝ) (w : Fin J → ℝ) (k : Fin J) :
    (P.transpose *ᵥ w) k = ∑ i, P i k * w i := rfl

lemma pow_succ_mulVec {J : ℕ} (P : Matrix (Fin J) (Fin J) ℝ) (v : Fin J → ℝ) (m : ℕ) :
    (P.transpose ^ (m + 1)) *ᵥ v = P.transpose *ᵥ ((P.transpose ^ m) *ᵥ v) := by
  rw [pow_succ', Matrix.mulVec_mulVec]

lemma powvec_nonneg {J : ℕ} (P : Matrix (Fin J) (Fin J) ℝ) (hP0 : ∀ i j, 0 ≤ P i j)
    (v : Fin J → ℝ) (hv : ∀ k, 0 ≤ v k) (m : ℕ) : ∀ k, 0 ≤ ((P.transpose ^ m) *ᵥ v) k := by
  induction m with
  | zero =>
    intro k
    simpa using hv k
  | succ m ih =>
    intro k
    rw [pow_succ_mulVec, tmul_apply]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hP0 i k) (ih i)

lemma Z_identity {J : ℕ} (χ : Fin J → Fin J → ℕ → Bool) (N : NetworkData J)
    (Z : ℝ → Fin J → ℤ) (B : ℝ → Fin J → ℝ) (hsol : IsQueueSolution χ N Z B)
    (lamv muv : Fin J → ℝ) (P : Matrix (Fin J) (Fin J) ℝ) (τ : ℝ) (hτ : 0 ≤ τ) (k : Fin J) :
    (Z τ k : ℝ) = ((N.Z0 k : ℝ) + xi χ N lamv muv P B τ k
        + (lamv k - muv k + ∑ i, P i k * muv i) * τ)
      + muv k * (τ - B τ k) - ∑ i, P i k * (muv i * (τ - B τ i)) := by
  have h := (hsol τ hτ k).2.1
  have h' : (Z τ k : ℝ) = (N.Z0 k : ℝ) + (N.A τ k : ℝ)
      + ∑ i, (routingCount χ i k (N.S (B τ i) i) : ℝ) - (N.S (B τ k) k : ℝ) := by
    rw [h]
    push_cast
    try ring
  rw [h']
  simp only [xi, Finset.sum_sub_distrib, Finset.sum_add_distrib, mul_sub, Finset.sum_mul,
    add_mul, sub_mul, mul_assoc]
  ring

lemma reflection_bound {J : ℕ} (χ : Fin J → Fin J → ℕ → Bool) (N : NetworkData J)
    (hN : N.IsValid χ) (Z : ℝ → Fin J → ℤ) (B : ℝ → Fin J → ℝ)
    (hsol : IsQueueSolution χ N Z B)
    (P : Matrix (Fin J) (Fin J) ℝ) (hP0 : ∀ i j, 0 ≤ P i j) (hPsum : ∀ k, ∑ i, P i k ≤ (J : ℝ))
    (μ : Fin J → ℝ) (hμ0 : ∀ k, 0 ≤ μ k) (μmax : ℝ) (hμmax0 : 0 ≤ μmax)
    (hμmax : ∀ k, μ k ≤ μmax)
    (x : ℝ → Fin J → ℝ)
    (hx : ∀ τ, 0 ≤ τ → ∀ k, (Z τ k : ℝ) =
      x τ k + μ k * (τ - B τ k) - ∑ i, P i k * (μ i * (τ - B τ i)))
    (τ0 E Dn : ℝ) (hE0 : 0 ≤ E) (hDn0 : 0 ≤ Dn)
    (hE : ∀ τ ∈ Set.Icc 0 τ0, ∀ k, |x τ k| ≤ E)
    (hD : ∀ k, N.downTime k τ0 ≤ Dn) :
    ∀ m : ℕ, ∀ τ ∈ Set.Icc 0 τ0, ∀ k, μ k * (τ - B τ k) ≤
      ((P.transpose ^ m) *ᵥ (fun _ : Fin J => μmax * τ0)) k + Cst J m * (E + μmax * Dn) := by
  have hF0 : 0 ≤ E + μmax * Dn := add_nonneg hE0 (mul_nonneg hμmax0 hDn0)
  intro m
  induction m with
  | zero =>
    intro τ hτ k
    obtain ⟨hB0, _⟩ := B_bounds χ N Z B hsol τ hτ.1 k
    simp only [pow_zero, Matrix.one_mulVec, Cst, zero_mul, add_zero]
    nlinarith [mul_nonneg (hμ0 k) hB0, mul_nonneg (sub_nonneg.2 (hμmax k)) hτ.1,
      mul_nonneg hμmax0 (sub_nonneg.2 hτ.2)]
  | succ m ih =>
    intro τ hτ k
    have hnn := powvec_nonneg P hP0 (fun _ : Fin J => μmax * τ0)
      (fun _ => mul_nonneg hμmax0 (hτ.1.trans hτ.2)) (m + 1) k
    have hdτ : N.downTime k τ ≤ Dn := (downTime_mono N.toInterruptions k hτ.2).trans (hD k)
    have hCs : Cst J (m + 1) = J * Cst J m + 1 := rfl
    have hC0 := Cst_nonneg J m
    have hJC : 0 ≤ (J : ℝ) * Cst J m * (E + μmax * Dn) :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg J) hC0) hF0
    rcases key_last_zero χ N hN Z B hsol k τ hτ.1 with h1 | h1
    · have h2 : μ k * (τ - B τ k) ≤ μmax * Dn := by
        calc μ k * (τ - B τ k) ≤ μ k * N.downTime k τ := mul_le_mul_of_nonneg_left h1 (hμ0 k)
          _ ≤ μmax * Dn := mul_le_mul (hμmax k) hdτ (downTime_nonneg _ _ _) hμmax0
      rw [hCs]
      nlinarith
    · by_contra hcon
      push_neg at hcon
      obtain ⟨g, hg⟩ : ∃ g, g = μ k * (τ - B τ k) -
          (((P.transpose ^ (m + 1)) *ᵥ (fun _ : Fin J => μmax * τ0)) k
            + Cst J (m + 1) * (E + μmax * Dn)) := ⟨_, rfl⟩
      have hgpos : 0 < g := by rw [hg]; linarith
      have hne : μmax + 1 ≠ 0 := by linarith
      obtain ⟨u, hu, hZu, hτu⟩ := h1 ((g / 2) / (μmax + 1)) (div_pos (by linarith) (by linarith))
      have hδ : (μmax + 1) * ((g / 2) / (μmax + 1)) = g / 2 := mul_div_cancel₀ _ hne
      have hδ0 : 0 ≤ (g / 2) / (μmax + 1) := (div_pos (by linarith) (by linarith)).le
      have hu0 : u ∈ Set.Icc 0 τ0 := ⟨hu.1, hu.2.trans hτ.2⟩
      have hid := hx u hu0.1 k
      rw [hZu, Int.cast_zero] at hid
      have hxu := abs_le.mp (hE u hu0 k)
      have hIH : ∀ i, μ i * (u - B u i) ≤
          ((P.transpose ^ m) *ᵥ (fun _ : Fin J => μmax * τ0)) i + Cst J m * (E + μmax * Dn) :=
        fun i => ih u hu0 i
      have hwm : ((P.transpose ^ (m + 1)) *ᵥ (fun _ : Fin J => μmax * τ0)) k =
          ∑ i, P i k * ((P.transpose ^ m) *ᵥ (fun _ : Fin J => μmax * τ0)) i := by
        rw [pow_succ_mulVec, tmul_apply]
      have hsumP : ∑ i, P i k * (μ i * (u - B u i)) ≤
          ((P.transpose ^ (m + 1)) *ᵥ (fun _ : Fin J => μmax * τ0)) k
            + J * (Cst J m * (E + μmax * Dn)) := by
        calc ∑ i, P i k * (μ i * (u - B u i))
            ≤ ∑ i, P i k * (((P.transpose ^ m) *ᵥ (fun _ : Fin J => μmax * τ0)) i
                + Cst J m * (E + μmax * Dn)) :=
              Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hIH i) (hP0 i k)
          _ = ∑ i, P i k * ((P.transpose ^ m) *ᵥ (fun _ : Fin J => μmax * τ0)) i
                + (∑ i, P i k) * (Cst J m * (E + μmax * Dn)) := by
              simp only [mul_add, Finset.sum_add_distrib, Finset.sum_mul]
          _ ≤ _ := by
              rw [hwm]
              have := mul_le_mul_of_nonneg_right (hPsum k) (mul_nonneg hC0 hF0)
              linarith
      have ha : μ k * (τ - B τ k) ≤ μ k * (u - B u k) + μ k * ((g / 2) / (μmax + 1))
          + μ k * N.downTime k τ := by
        have := mul_le_mul_of_nonneg_left hτu (hμ0 k)
        calc _ ≤ μ k * (u - B u k + (g / 2) / (μmax + 1) + N.downTime k τ) := this
          _ = _ := by ring
      have hb : μ k * ((g / 2) / (μmax + 1)) ≤ g / 2 := by
        have h1 : μ k * ((g / 2) / (μmax + 1)) ≤ (μmax + 1) * ((g / 2) / (μmax + 1)) :=
          mul_le_mul_of_nonneg_right (by linarith [hμmax k]) hδ0
        linarith [hδ]
      have hc : μ k * N.downTime k τ ≤ μmax * Dn :=
        mul_le_mul (hμmax k) hdτ (downTime_nonneg _ _ _) hμmax0
      rw [hCs] at hg
      have hJ : (J : ℝ) * (Cst J m * (E + μmax * Dn)) = J * Cst J m * (E + μmax * Dn) := by ring
      linarith

lemma xi_bound {J : ℕ} (χ : Fin J → Fin J → ℕ → Bool) (N : NetworkData J)
    (lamv muv : Fin J → ℝ)
    (P : Matrix (Fin J) (Fin J) ℝ) (hP0 : ∀ i j, 0 ≤ P i j) (hP1 : ∀ i j, P i j ≤ 1)
    (B : ℝ → Fin J → ℝ) (τ : ℝ) (k : Fin J) (KA KR KS : ℝ)
    (hA : |(N.A τ k : ℝ) - lamv k * τ| ≤ KA)
    (hR : ∀ i, |(routingCount χ i k (N.S (B τ i) i) : ℝ) - P i k * (N.S (B τ i) i : ℝ)| ≤ KR)
    (hS : ∀ i, |(N.S (B τ i) i : ℝ) - muv i * B τ i| ≤ KS) :
    |xi χ N lamv muv P B τ k| ≤ KA + J * KR + J * KS + KS := by
  have h1 : |∑ i, ((routingCount χ i k (N.S (B τ i) i) : ℝ) - P i k * (N.S (B τ i) i : ℝ))|
      ≤ J * KR := by
    calc _ ≤ ∑ i, |(routingCount χ i k (N.S (B τ i) i) : ℝ) - P i k * (N.S (B τ i) i : ℝ)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin J, KR := Finset.sum_le_sum fun i _ => hR i
      _ = J * KR := by simp
  have h2 : |∑ i, P i k * ((N.S (B τ i) i : ℝ) - muv i * B τ i)| ≤ J * KS := by
    calc _ ≤ ∑ i, |P i k * ((N.S (B τ i) i : ℝ) - muv i * B τ i)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin J, KS := Finset.sum_le_sum fun i _ => by
          rw [abs_mul, abs_of_nonneg (hP0 i k)]
          calc P i k * |(N.S (B τ i) i : ℝ) - muv i * B τ i| ≤ 1 * KS :=
                mul_le_mul (hP1 i k) (hS i) (abs_nonneg _) zero_le_one
            _ = KS := one_mul _
      _ = J * KS := by simp
  have h3 := abs_le.mp (hS k)
  have h1' := abs_le.mp h1
  have h2' := abs_le.mp h2
  have hA' := abs_le.mp hA
  show |(N.A τ k : ℝ) - lamv k * τ
      + ∑ i, ((routingCount χ i k (N.S (B τ i) i) : ℝ) - P i k * (N.S (B τ i) i : ℝ))
      + ∑ i, P i k * ((N.S (B τ i) i : ℝ) - muv i * B τ i)
      - ((N.S (B τ k) k : ℝ) - muv k * B τ k)| ≤ _
  rw [abs_le]
  constructor <;> linarith

lemma uoc_bound {E : Type*} [NormedAddCommGroup E] {f : ℕ → ℝ → E} {g : ℝ → E}
    (h : UocTendsto f g) (T : ℝ) (hg : ContinuousOn g (Set.Icc 0 T)) :
    ∃ K, 0 ≤ K ∧ ∀ᶠ n in atTop, ∀ t ∈ Set.Icc 0 T, ‖f n t‖ ≤ K := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  refine ⟨|C| + 1, by positivity, ?_⟩
  filter_upwards [h T 1 one_pos] with n hn t ht
  have h1 := hn t ht
  have h2 := hC t ht
  have h3 := norm_sub_norm_le (f n t) (g t)
  linarith [le_abs_self C]

lemma div_sqrt_bound {X K : ℝ} {n : ℕ} (hn : 1 ≤ n) (h : |X / Real.sqrt n| ≤ K) :
    |X| ≤ K * Real.sqrt n := by
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 (Nat.cast_pos.2 (by omega))
  rw [abs_div, abs_of_pos hs, div_le_iff₀ hs] at h
  exact h

lemma rate_conv {J : ℕ} (a : ℕ → Fin J → ℝ) (a0 c : Fin J → ℝ)
    (h : Tendsto (fun n : ℕ => Real.sqrt n • (a n - a0)) atTop (𝓝 c)) :
    Tendsto a atTop (𝓝 a0) := by
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hsqrt
  have h2 : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹ • (Real.sqrt n • (a n - a0))) atTop
      (𝓝 ((0 : ℝ) • c)) := hinv.smul h
  rw [zero_smul] at h2
  have h3 : Tendsto (fun n : ℕ => a0 + (Real.sqrt n)⁻¹ • (Real.sqrt n • (a n - a0))) atTop
      (𝓝 (a0 + 0)) := tendsto_const_nhds.add h2
  rw [add_zero] at h3
  apply h3.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hs : Real.sqrt n ≠ 0 := (Real.sqrt_pos.2 (Nat.cast_pos.2 (by omega))).ne'
  rw [smul_smul, inv_mul_cancel₀ hs, one_smul]
  abel


theorem lemma42 {J : ℕ} (χ : Fin J → Fin J → ℕ → Bool) (net : ℕ → NetworkData J)
    (lamn mun : ℕ → Fin J → ℝ) (lam mu clam cmu : Fin J → ℝ) (P : Matrix (Fin J) (Fin J) ℝ)
    (L : LimitData J) (Z : ℕ → ℝ → Fin J → ℤ) (B : ℕ → ℝ → Fin J → ℝ)
    (hH : PathwiseHyp χ net lamn mun lam mu clam cmu P L)
    (hsol : ∀ n, IsQueueSolution χ (net n) (Z n) (B n)) :
    ∀ j : Fin J, UocTendsto (fun (n : ℕ) (t : ℝ) => B n (n * t) j / n) (fun t => t) := by
  unfold PathwiseHyp at hH
  obtain ⟨hvalid, hpar, hprim, hreg⟩ := hH
  unfold ParamHyp at hpar
  obtain ⟨hlam, -, hmu, hmu0, hlamEq, hPT⟩ := hpar
  unfold IsTransientSubstochastic at hPT
  obtain ⟨hP0, hP1row, hPk⟩ := hPT
  unfold PrimConv at hprim
  obtain ⟨hZ0, hA, hS, hR, hUD⟩ := hprim
  unfold LimitRegular at hreg
  obtain ⟨hAc, hSc, hRc, hsum, -⟩ := hreg
  have hP1 : ∀ i j, P i j ≤ 1 := fun i j =>
    (Finset.single_le_sum (f := fun j' => P i j') (fun j' _ => hP0 i j')
      (Finset.mem_univ j)).trans (hP1row i)
  have hPsum : ∀ k, ∑ i, P i k ≤ (J : ℝ) := by
    intro k
    calc ∑ i, P i k ≤ ∑ _i : Fin J, (1 : ℝ) := Finset.sum_le_sum fun i _ => hP1 i k
      _ = J := by simp
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hlamc := rate_conv lamn lam clam hlam
  have hmuc := rate_conv mun mu cmu hmu
  have hc : ∀ k, Tendsto (fun n => lamn n k - mun n k + ∑ i, P i k * mun n i) atTop (𝓝 0) := by
    intro k
    have e : lam k - mu k + ∑ i, P i k * mu i = 0 := by
      have h := congrFun hlamEq k
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, tmul_apply] at h
      rw [h]
      ring
    rw [← e]
    exact ((tendsto_pi_nhds.1 hlamc k).sub (tendsto_pi_nhds.1 hmuc k)).add
      (tendsto_finset_sum _ fun i _ => (tendsto_pi_nhds.1 hmuc i).const_mul (P i k))
  have hupc : ∀ k l, Tendsto (fun n : ℕ => (net n).up k l / (n : ℝ)) atTop (𝓝 (L.up k l)) := by
    intro k l
    have h1 := tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hUD k) l
    exact (continuous_fst.tendsto _).comp h1
  have hdnc : ∀ k l, Tendsto (fun n : ℕ => (net n).down k l / Real.sqrt n) atTop
      (𝓝 (L.down k l)) := by
    intro k l
    have h1 := tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hUD k) l
    exact (continuous_snd.tendsto _).comp h1
  intro j0 T ε hε
  obtain ⟨T1, hT1⟩ : ∃ T1, T1 = max T 0 := ⟨_, rfl⟩
  have hT10 : 0 ≤ T1 := by rw [hT1]; exact le_max_right T 0
  have hTT1 : T ≤ T1 := by rw [hT1]; exact le_max_left T 0
  obtain ⟨μmax, hμmaxdef⟩ : ∃ μmax : ℝ, μmax = ∑ k, (mu k + 1) := ⟨_, rfl⟩
  have hμmaxk : ∀ k, mu k + 1 ≤ μmax := fun k => by
    rw [hμmaxdef]
    exact Finset.single_le_sum (f := fun k => mu k + 1) (fun i _ => by linarith [hmu0 i])
      (Finset.mem_univ k)
  have hμmax0 : 0 ≤ μmax := by
    rw [hμmaxdef]
    exact Finset.sum_nonneg fun i _ => by linarith [hmu0 i]
  have hmuev : ∀ᶠ n in atTop, ∀ k, mu k / 2 < mun n k ∧ mun n k < mu k + 1 := by
    rw [eventually_all]
    intro k
    have h := tendsto_pi_nhds.1 hmuc k
    exact (h.eventually (lt_mem_nhds (by linarith [hmu0 k]))).and
      (h.eventually (gt_mem_nhds (by linarith)))
  obtain ⟨γ, hγdef⟩ : ∃ γ, γ = mu j0 / 2 * ε := ⟨_, rfl⟩
  have hγ : 0 < γ := by rw [hγdef]; exact mul_pos (half_pos (hmu0 j0)) hε
  -- choice of m
  have hPm : Tendsto (fun m : ℕ => ((P ^ m).transpose *ᵥ (fun _ : Fin J => μmax * T1)) j0)
      atTop (𝓝 0) := by
    have hcont : Continuous (fun M : Matrix (Fin J) (Fin J) ℝ =>
        (M.transpose *ᵥ (fun _ : Fin J => μmax * T1)) j0) :=
      (continuous_apply j0).comp
        (Continuous.matrix_mulVec (Continuous.matrix_transpose continuous_id) continuous_const)
    have h : Tendsto (fun m : ℕ => ((P ^ m).transpose *ᵥ (fun _ : Fin J => μmax * T1)) j0)
        atTop (𝓝 (((0 : Matrix (Fin J) (Fin J) ℝ).transpose *ᵥ
          (fun _ : Fin J => μmax * T1)) j0)) := (hcont.tendsto 0).comp hPk
    have e : ((0 : Matrix (Fin J) (Fin J) ℝ).transpose *ᵥ (fun _ : Fin J => μmax * T1)) j0 = 0 := by
      simp
    rwa [e] at h
  obtain ⟨m, hm⟩ := (hPm.eventually (gt_mem_nhds (half_pos hγ))).exists
  rw [Matrix.transpose_pow] at hm
  -- choice of η
  have hC0 := Cst_nonneg J m
  have hD : 0 < (Cst J m + 1) * (1 + μmax) := mul_pos (by linarith) (by linarith)
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = γ / (4 * ((Cst J m + 1) * (1 + μmax))) := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hηdef]; exact div_pos hγ (by linarith)
  have hCη : Cst J m * (η + μmax * η) < γ / 2 := by
    have h1 : Cst J m * (η + μmax * η) ≤ ((Cst J m + 1) * (1 + μmax)) * η := by
      nlinarith [mul_nonneg hμmax0 hη.le]
    have h2 : ((Cst J m + 1) * (1 + μmax)) * η = γ / 4 := by
      rw [hηdef, mul_div_assoc', div_eq_div_iff (mul_pos (by norm_num : (0:ℝ) < 4) hD).ne'
        (by norm_num : (4:ℝ) ≠ 0)]
      ring
    linarith
  -- uniform bounds on the primitives
  have hAg : ContinuousOn L.toPrim.2.1 (Set.Icc 0 T1) :=
    (hAc.mono Set.Icc_subset_Ici_self).congr (fun t ht => by
      show (if t < 0 then (0 : Fin J → ℝ) else L.A t) = L.A t
      rw [if_neg (not_lt.mpr ht.1)])
  have hSg : ContinuousOn L.toPrim.2.2.1 (Set.Icc 0 T1) :=
    (hSc.mono Set.Icc_subset_Ici_self).congr (fun t ht => by
      show (if t < 0 then (0 : Fin J → ℝ) else L.S t) = L.S t
      rw [if_neg (not_lt.mpr ht.1)])
  obtain ⟨KA, hKA0, hKA⟩ := uoc_bound hA T1 hAg
  obtain ⟨KS, hKS0, hKS⟩ := uoc_bound hS T1 hSg
  obtain ⟨T', hT'⟩ : ∃ T' : ℝ, T' = μmax * T1 + KS := ⟨_, rfl⟩
  have hRg : ContinuousOn L.toPrim.2.2.2.1 (Set.Icc 0 T') :=
    (hRc.mono Set.Icc_subset_Ici_self).congr (fun t ht => by
      show (if t < 0 then (0 : Fin J → Fin J → ℝ) else L.R t) = L.R t
      rw [if_neg (not_lt.mpr ht.1)])
  obtain ⟨KR, hKR0, hKR⟩ := uoc_bound hR T' hRg
  have hAn : ∀ᶠ n in atTop, ∀ t ∈ Set.Icc 0 T1, ∀ k,
      |((net n).A ((n : ℝ) * t) k : ℝ) - lamn n k * n * t| ≤ KA * Real.sqrt n := by
    filter_upwards [hKA, eventually_ge_atTop 1] with n hn hn1 t ht k
    have h1 : ‖(if t < 0 then (0 : ℝ) else
        (((net n).A ((n : ℝ) * t) k : ℝ) - lamn n k * n * t) / Real.sqrt n)‖ ≤ KA :=
      (norm_le_pi_norm ((scaledPrimitives χ (net n) (lamn n) (mun n) P n).2.1 t) k).trans
        (hn t ht)
    rw [if_neg (not_lt.mpr ht.1), Real.norm_eq_abs] at h1
    exact div_sqrt_bound hn1 h1
  have hSn : ∀ᶠ n in atTop, ∀ t ∈ Set.Icc 0 T1, ∀ k,
      |((net n).S ((n : ℝ) * t) k : ℝ) - mun n k * n * t| ≤ KS * Real.sqrt n := by
    filter_upwards [hKS, eventually_ge_atTop 1] with n hn hn1 t ht k
    have h1 : ‖(if t < 0 then (0 : ℝ) else
        (((net n).S ((n : ℝ) * t) k : ℝ) - mun n k * n * t) / Real.sqrt n)‖ ≤ KS :=
      (norm_le_pi_norm ((scaledPrimitives χ (net n) (lamn n) (mun n) P n).2.2.1 t) k).trans
        (hn t ht)
    rw [if_neg (not_lt.mpr ht.1), Real.norm_eq_abs] at h1
    exact div_sqrt_bound hn1 h1
  have hRn : ∀ᶠ n : ℕ in atTop, ∀ t ∈ Set.Icc 0 T', ∀ i k,
      |(routingCount χ i k ⌊(n : ℝ) * t⌋₊ : ℝ) - P i k * n * t| ≤ KR * Real.sqrt n := by
    filter_upwards [hKR, eventually_ge_atTop 1] with n hn hn1 t ht i k
    have h1 : ‖(if t < 0 then (0 : ℝ) else
        ((routingCount χ i k ⌊(n : ℝ) * t⌋₊ : ℝ) - P i k * n * t) / Real.sqrt n)‖ ≤ KR :=
      (norm_le_pi_norm ((scaledPrimitives χ (net n) (lamn n) (mun n) P n).2.2.2.1 t i) k).trans
        ((norm_le_pi_norm ((scaledPrimitives χ (net n) (lamn n) (mun n) P n).2.2.2.1 t) i).trans
          (hn t ht))
    rw [if_neg (not_lt.mpr ht.1), Real.norm_eq_abs] at h1
    exact div_sqrt_bound hn1 h1
  obtain ⟨K0, hK0⟩ : ∃ K0 : ℝ, K0 = ‖L.toPrim.1‖ + 1 := ⟨_, rfl⟩
  have hZ0n : ∀ᶠ n in atTop, ∀ k, |((net n).Z0 k : ℝ)| ≤ K0 * Real.sqrt n := by
    filter_upwards [hZ0.norm.eventually (gt_mem_nhds (lt_add_one ‖L.toPrim.1‖)),
      eventually_ge_atTop 1] with n hn hn1 k
    have h1 : ‖((net n).Z0 k : ℝ) / Real.sqrt n‖ ≤ K0 := by
      rw [hK0]
      exact (norm_le_pi_norm (scaledPrimitives χ (net n) (lamn n) (mun n) P n).1 k).trans hn.le
    rw [Real.norm_eq_abs] at h1
    exact div_sqrt_bound hn1 h1
  have hK0nn : 0 ≤ K0 := by rw [hK0]; positivity
  obtain ⟨Kxi, hKxi⟩ : ∃ Kxi : ℝ, Kxi = KA + J * KR + J * KS + KS := ⟨_, rfl⟩
  have hsq : ∀ᶠ n : ℕ in atTop, 2 * (K0 + Kxi) ≤ Real.sqrt n * η := by
    filter_upwards [hsqrt.eventually (eventually_ge_atTop (2 * (K0 + Kxi) / η))] with n hn
    rwa [div_le_iff₀ hη] at hn
  have hcn : ∀ᶠ n in atTop, ∀ k, |lamn n k - mun n k + ∑ i, P i k * mun n i| * T1 ≤ η / 2 := by
    rw [eventually_all]
    intro k
    have hr : 0 < η / (2 * (T1 + 1)) := div_pos hη (by linarith)
    filter_upwards [(hc k).eventually (Ioo_mem_nhds (show -(η / (2 * (T1 + 1))) < 0 by linarith) hr)]
      with n hn
    have h1 : |lamn n k - mun n k + ∑ i, P i k * mun n i| < η / (2 * (T1 + 1)) :=
      abs_lt.mpr ⟨hn.1, hn.2⟩
    rw [lt_div_iff₀ (show (0:ℝ) < 2 * (T1 + 1) by linarith)] at h1
    nlinarith [abs_nonneg (lamn n k - mun n k + ∑ i, P i k * mun n i)]
  have hdown : ∀ᶠ n in atTop, ∀ k, (net n).downTime k (n * T1) ≤ n * η := by
    rw [eventually_all]
    intro k
    obtain ⟨M, hM⟩ := ((hsum k).eventually (eventually_gt_atTop (T1 + 1))).exists
    have hup_sum : Tendsto (fun n : ℕ => ∑ l ∈ Finset.range M, (net n).up k l / (n : ℝ)) atTop
        (𝓝 (∑ l ∈ Finset.range M, L.up k l)) := tendsto_finset_sum _ fun l _ => hupc k l
    have hdn_sum : Tendsto (fun n : ℕ => ∑ l ∈ Finset.range M, (net n).down k l / Real.sqrt n)
        atTop (𝓝 (∑ l ∈ Finset.range M, L.down k l)) := tendsto_finset_sum _ fun l _ => hdnc k l
    filter_upwards [hup_sum.eventually (lt_mem_nhds (show T1 < ∑ l ∈ Finset.range M, L.up k l by
        linarith)),
      hdn_sum.eventually (gt_mem_nhds (lt_add_one (∑ l ∈ Finset.range M, L.down k l))),
      hsqrt.eventually (eventually_ge_atTop ((∑ l ∈ Finset.range M, L.down k l + 1) / η)),
      eventually_ge_atTop 1] with n h1 h2 h3 hn
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
    have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
    rw [← Finset.sum_div, lt_div_iff₀ hnpos] at h1
    rw [← Finset.sum_div, div_lt_iff₀ hs] at h2
    rw [div_le_iff₀ hη] at h3
    have hss : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hnpos.le
    calc (net n).downTime k (n * T1) ≤ ∑ l ∈ Finset.range M, (net n).down k l :=
          downTime_le_sum _ (hvalid n).1 k _ M (by linarith)
      _ ≤ (∑ l ∈ Finset.range M, L.down k l + 1) * Real.sqrt n := h2.le
      _ ≤ (Real.sqrt n * η) * Real.sqrt n := mul_le_mul_of_nonneg_right h3 hs.le
      _ = n * η := by
          rw [show Real.sqrt n * η * Real.sqrt n = (Real.sqrt n * Real.sqrt n) * η by ring, hss]
  filter_upwards [eventually_ge_atTop 1, hmuev, hcn, hZ0n, hAn, hSn, hRn, hdown, hsq]
    with n hn1 hmun hcn' hZ0' hA' hS' hR' hdown' hsq'
  intro t ht
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
  have hn0 : (n : ℝ) ≠ 0 := hnpos.ne'
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
  have hss : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hnpos.le
  have hs1 : 1 ≤ Real.sqrt n := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hn1)
  have hsn : Real.sqrt n ≤ n := by nlinarith [mul_le_mul_of_nonneg_left hs1 hs.le]
  have hmun0 : ∀ k, 0 ≤ mun n k := fun k => by linarith [(hmun k).1, hmu0 k]
  have hmunmax : ∀ k, mun n k ≤ μmax := fun k => by linarith [(hmun k).2, hμmaxk k]
  -- the bound on the free part
  have hE : ∀ τ ∈ Set.Icc 0 ((n : ℝ) * T1), ∀ k,
      |((net n).Z0 k : ℝ) + xi χ (net n) (lamn n) (mun n) P (B n) τ k
        + (lamn n k - mun n k + ∑ i, P i k * mun n i) * τ| ≤ n * η := by
    intro τ hτ k
    have hτn : τ / n ∈ Set.Icc 0 T1 :=
      ⟨div_nonneg hτ.1 hnpos.le, (div_le_iff₀ hnpos).2 (by linarith [hτ.2])⟩
    have hA1 := hA' (τ / n) hτn k
    have e1 : lamn n k * n * (τ / n) = lamn n k * τ := by rw [mul_assoc, mul_div_cancel₀ τ hn0]
    rw [e1, mul_div_cancel₀ τ hn0] at hA1
    have hSi : ∀ i, |((net n).S (B n τ i) i : ℝ) - mun n i * B n τ i| ≤ KS * Real.sqrt n := by
      intro i
      obtain ⟨hB0, hB1⟩ := B_bounds χ (net n) (Z n) (B n) (hsol n) τ hτ.1 i
      have hBn : B n τ i / n ∈ Set.Icc 0 T1 :=
        ⟨div_nonneg hB0 hnpos.le, (div_le_iff₀ hnpos).2 (by linarith [hτ.2])⟩
      have h1 := hS' (B n τ i / n) hBn i
      have e2 : mun n i * n * (B n τ i / n) = mun n i * B n τ i := by
        rw [mul_assoc, mul_div_cancel₀ _ hn0]
      rw [e2, mul_div_cancel₀ _ hn0] at h1
      exact h1
    have hRi : ∀ i, |(routingCount χ i k ((net n).S (B n τ i) i) : ℝ)
        - P i k * ((net n).S (B n τ i) i : ℝ)| ≤ KR * Real.sqrt n := by
      intro i
      obtain ⟨hB0, hB1⟩ := B_bounds χ (net n) (Z n) (B n) (hsol n) τ hτ.1 i
      have hSb := abs_le.mp (hSi i)
      have hmB : mun n i * B n τ i ≤ μmax * (n * T1) :=
        mul_le_mul (hmunmax i) (by linarith [hτ.2]) hB0 hμmax0
      have hKS : KS * Real.sqrt n ≤ KS * n := mul_le_mul_of_nonneg_left hsn hKS0
      have hmem : ((net n).S (B n τ i) i : ℝ) / n ∈ Set.Icc 0 T' := by
        refine ⟨div_nonneg (Nat.cast_nonneg _) hnpos.le, (div_le_iff₀ hnpos).2 ?_⟩
        rw [hT']
        linarith [hSb.2]
      have h1 := hR' _ hmem i k
      have e3 : P i k * n * (((net n).S (B n τ i) i : ℝ) / n) = P i k * ((net n).S (B n τ i) i : ℝ) := by
        rw [mul_assoc, mul_div_cancel₀ _ hn0]
      rw [e3, mul_div_cancel₀ _ hn0, Nat.floor_natCast] at h1
      exact h1
    have hxi := xi_bound χ (net n) (lamn n) (mun n) P hP0 hP1 (B n) τ k
      (KA * Real.sqrt n) (KR * Real.sqrt n) (KS * Real.sqrt n) hA1 hRi hSi
    have hxi' : |xi χ (net n) (lamn n) (mun n) P (B n) τ k| ≤ Kxi * Real.sqrt n := by
      rw [hKxi]
      calc _ ≤ KA * Real.sqrt n + J * (KR * Real.sqrt n) + J * (KS * Real.sqrt n)
            + KS * Real.sqrt n := hxi
        _ = _ := by ring
    have hcτ : |(lamn n k - mun n k + ∑ i, P i k * mun n i) * τ| ≤ n * (η / 2) := by
      rw [abs_mul, abs_of_nonneg hτ.1]
      have h1 := mul_le_mul_of_nonneg_left (hcn' k) hnpos.le
      have h2 : |lamn n k - mun n k + ∑ i, P i k * mun n i| * τ
          ≤ |lamn n k - mun n k + ∑ i, P i k * mun n i| * (n * T1) :=
        mul_le_mul_of_nonneg_left hτ.2 (abs_nonneg _)
      linarith
    have hZk := abs_le.mp (hZ0' k)
    have hxi2 := abs_le.mp hxi'
    have hc2 := abs_le.mp hcτ
    have hsq2 : 2 * (K0 + Kxi) * Real.sqrt n ≤ Real.sqrt n * η * Real.sqrt n :=
      mul_le_mul_of_nonneg_right hsq' hs.le
    have hsq3 : Real.sqrt n * η * Real.sqrt n = n * η := by
      rw [show Real.sqrt n * η * Real.sqrt n = (Real.sqrt n * Real.sqrt n) * η by ring, hss]
    rw [abs_le]
    constructor <;> linarith
  have hbound := reflection_bound χ (net n) (hvalid n) (Z n) (B n) (hsol n) P hP0 hPsum
    (mun n) hmun0 μmax hμmax0 hmunmax
    (fun τ k => ((net n).Z0 k : ℝ) + xi χ (net n) (lamn n) (mun n) P (B n) τ k
        + (lamn n k - mun n k + ∑ i, P i k * mun n i) * τ)
    (fun τ hτ k => Z_identity χ (net n) (Z n) (B n) (hsol n) (lamn n) (mun n) P τ hτ k)
    ((n : ℝ) * T1) (n * η) (n * η) (mul_nonneg hnpos.le hη.le) (mul_nonneg hnpos.le hη.le)
    hE hdown' m
  have htT : (n : ℝ) * t ∈ Set.Icc 0 ((n : ℝ) * T1) :=
    ⟨mul_nonneg hnpos.le ht.1, mul_le_mul_of_nonneg_left (ht.2.trans hTT1) hnpos.le⟩
  have hb := hbound ((n : ℝ) * t) htT j0
  have hfun : (fun _ : Fin J => μmax * ((n : ℝ) * T1)) = (n : ℝ) • (fun _ : Fin J => μmax * T1) := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hfun, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul] at hb
  obtain ⟨hB0, hB1⟩ := B_bounds χ (net n) (Z n) (B n) (hsol n) ((n : ℝ) * t) htT.1 j0
  have hmunj : mu j0 / 2 < mun n j0 := (hmun j0).1
  have hγle : γ ≤ mun n j0 * ε := by
    rw [hγdef]; nlinarith [mul_lt_mul_of_pos_right hmunj hε]
  have hb2 : mun n j0 * ((n : ℝ) * t - B n ((n : ℝ) * t) j0) < n * γ := by
    have h1 : Cst J m * (n * η + μmax * (n * η)) = n * (Cst J m * (η + μmax * η)) := by ring
    rw [h1] at hb
    have h2 := mul_lt_mul_of_pos_left hm hnpos
    have h3 := mul_lt_mul_of_pos_left hCη hnpos
    linarith
  have hkey : (n : ℝ) * t - B n ((n : ℝ) * t) j0 < n * ε := by
    have hmpos : 0 < mun n j0 := by linarith [hmu0 j0]
    by_contra hcon
    push_neg at hcon
    have h1 := mul_le_mul_of_nonneg_left hcon hmpos.le
    have h2 := mul_le_mul_of_nonneg_left hγle hnpos.le
    linarith
  show ‖B n ((n : ℝ) * t) j0 / n - t‖ < ε
  rw [Real.norm_eq_abs, show B n ((n : ℝ) * t) j0 / n - t = (B n ((n : ℝ) * t) j0 - n * t) / n by
    rw [sub_div, mul_div_cancel_left₀ t hn0], abs_div, abs_of_pos hnpos, div_lt_iff₀ hnpos,
    abs_lt]
  have hεn : 0 < ε * n := mul_pos hε hnpos
  constructor <;> linarith


end Aux_CW42

open ChenWhitt93.JumpDiffusion Aux_CW42 in
theorem solution {J : ℕ} (χ : Fin J → Fin J → ℕ → Bool) (net : ℕ → NetworkData J)
    (lamn mun : ℕ → Fin J → ℝ) (lam mu clam cmu : Fin J → ℝ) (P : Matrix (Fin J) (Fin J) ℝ)
    (L : LimitData J) (Z : ℕ → ℝ → Fin J → ℤ) (B : ℕ → ℝ → Fin J → ℝ)
    (hH : PathwiseHyp χ net lamn mun lam mu clam cmu P L)
    (hsol : ∀ n, IsQueueSolution χ (net n) (Z n) (B n)) :
    UocTendsto (fun (n : ℕ) (t : ℝ) => (Real.sqrt n)⁻¹ • xi χ (net n) (lamn n) (mun n) P (B n) (n * t))
      (xiHat L mu P) ∧
    ContinuousOn (xiHat L mu P) (Set.Ici 0) := by
  have h42 := lemma42 χ net lamn mun lam mu clam cmu P L Z B hH hsol
  unfold PathwiseHyp at hH
  obtain ⟨hvalid, hpar, hprim, hreg⟩ := hH
  unfold ParamHyp at hpar
  obtain ⟨hlam, -, hmu, hmu0, hlamEq, hPT⟩ := hpar
  unfold IsTransientSubstochastic at hPT
  obtain ⟨hP0, hP1row, hPk⟩ := hPT
  unfold PrimConv at hprim
  obtain ⟨hZ0, hA, hS, hR, hUD⟩ := hprim
  unfold LimitRegular at hreg
  obtain ⟨hAc, hSc, hRc, hsum, -⟩ := hreg
  have hP1 : ∀ i j, P i j ≤ 1 := fun i j =>
    (Finset.single_le_sum (f := fun j' => P i j') (fun j' _ => hP0 i j')
      (Finset.mem_univ j)).trans (hP1row i)
  have hmuc := rate_conv mun mu cmu hmu
  have hRmu : ∀ k, ContinuousOn (fun t => L.R (mu k * t)) (Set.Ici 0) := fun k =>
    hRc.comp (continuous_mul_left (mu k)).continuousOn
      (fun t ht => mul_nonneg (hmu0 k).le ht)
  refine ⟨?_, ?_⟩
  swap
  · apply continuousOn_pi.2
    intro j
    show ContinuousOn
      (fun t => L.A t j + ∑ k, (L.R (mu k * t) k j + P k j * L.S t k) - L.S t j) (Set.Ici 0)
    have cA : ContinuousOn (fun t => L.A t j) (Set.Ici 0) :=
      (continuous_apply j).comp_continuousOn hAc
    have cS : ∀ k, ContinuousOn (fun t => L.S t k) (Set.Ici 0) := fun k =>
      (continuous_apply k).comp_continuousOn hSc
    have cR : ∀ k, ContinuousOn (fun t => L.R (mu k * t) k j) (Set.Ici 0) := fun k => by
      have hc : Continuous (fun f : Fin J → Fin J → ℝ => f k j) :=
        continuous_apply_apply k j
      exact hc.comp_continuousOn (hRmu k)
    have cSum : ContinuousOn (fun t => ∑ k, (L.R (mu k * t) k j + P k j * L.S t k)) (Set.Ici 0) :=
      continuousOn_finset_sum _ fun k _ => (cR k).add (continuousOn_const.mul (cS k))
    exact (cA.add cSum).sub (cS j)
  intro T ε hε
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨T1, hT1⟩ : ∃ T1, T1 = max T 0 := ⟨_, rfl⟩
  have hT10 : 0 ≤ T1 := by rw [hT1]; exact le_max_right T 0
  have hTT1 : T ≤ T1 := by rw [hT1]; exact le_max_left T 0
  obtain ⟨μmax, hμmaxdef⟩ : ∃ μmax : ℝ, μmax = ∑ k, (mu k + 1) := ⟨_, rfl⟩
  have hμmaxk : ∀ k, mu k + 1 ≤ μmax := fun k => by
    rw [hμmaxdef]
    exact Finset.single_le_sum (f := fun k => mu k + 1) (fun i _ => by linarith [hmu0 i])
      (Finset.mem_univ k)
  have hμmax0 : 0 ≤ μmax := by
    rw [hμmaxdef]
    exact Finset.sum_nonneg fun i _ => by linarith [hmu0 i]
  have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  obtain ⟨ε', hε'def⟩ : ∃ ε' : ℝ, ε' = ε / (2 * J + 3) := ⟨_, rfl⟩
  have hε' : 0 < ε' := by rw [hε'def]; exact div_pos hε (by linarith)
  have hεε : (2 * J + 2) * ε' < ε := by
    rw [hε'def, mul_div_assoc', div_lt_iff₀ (by linarith : (0 : ℝ) < 2 * J + 3)]
    nlinarith
  have hSg : ContinuousOn L.toPrim.2.2.1 (Set.Icc 0 T1) :=
    (hSc.mono Set.Icc_subset_Ici_self).congr (fun t ht => by
      show (if t < 0 then (0 : Fin J → ℝ) else L.S t) = L.S t
      rw [if_neg (not_lt.mpr ht.1)])
  obtain ⟨KS, hKS0, hKS⟩ := uoc_bound hS T1 hSg
  obtain ⟨T', hT'⟩ : ∃ T' : ℝ, T' = μmax * T1 + KS := ⟨_, rfl⟩
  obtain ⟨δS, hδS, hδSc⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous
      (hSc.mono (Set.Icc_subset_Ici_self : Set.Icc (0 : ℝ) T1 ⊆ Set.Ici 0))) (ε' / 2) (half_pos hε')
  obtain ⟨δR, hδR, hδRc⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous
      (hRc.mono (Set.Icc_subset_Ici_self : Set.Icc (0 : ℝ) T' ⊆ Set.Ici 0))) (ε' / 2) (half_pos hε')
  obtain ⟨η1, hη1def⟩ : ∃ η1 : ℝ, η1 = min δS (δR / 3 / (μmax + 1)) := ⟨_, rfl⟩
  have hη1 : 0 < η1 := by
    rw [hη1def]
    exact lt_min hδS (div_pos (by linarith) (by linarith))
  have hη1S : η1 ≤ δS := by rw [hη1def]; exact min_le_left _ _
  have hη1R : (μmax + 1) * η1 ≤ δR / 3 := by
    have h1 : η1 ≤ δR / 3 / (μmax + 1) := by rw [hη1def]; exact min_le_right _ _
    calc (μmax + 1) * η1 ≤ (μmax + 1) * (δR / 3 / (μmax + 1)) :=
          mul_le_mul_of_nonneg_left h1 (by linarith)
      _ = δR / 3 := mul_div_cancel₀ _ (show (0 : ℝ) < μmax + 1 by linarith).ne'
  have hAu : ∀ᶠ n : ℕ in atTop, ∀ s ∈ Set.Icc 0 T1, ∀ k,
      |(((net n).A ((n : ℝ) * s) k : ℝ) - lamn n k * n * s) / Real.sqrt n - L.A s k| < ε' := by
    filter_upwards [hA T1 ε' hε'] with n hn s hs k
    have hs' : ¬ s < 0 := not_lt.mpr hs.1
    have h1 : ‖(if s < 0 then (0 : ℝ) else
        (((net n).A ((n : ℝ) * s) k : ℝ) - lamn n k * n * s) / Real.sqrt n)
          - (if s < 0 then (0 : Fin J → ℝ) else L.A s) k‖ < ε' :=
      lt_of_le_of_lt (norm_le_pi_norm ((scaledPrimitives χ (net n) (lamn n) (mun n) P n).2.1 s
        - L.toPrim.2.1 s) k) (hn s hs)
    rw [if_neg hs', if_neg hs', Real.norm_eq_abs] at h1
    exact h1
  have hSu : ∀ᶠ n : ℕ in atTop, ∀ s ∈ Set.Icc 0 T1, ∀ k,
      |(((net n).S ((n : ℝ) * s) k : ℝ) - mun n k * n * s) / Real.sqrt n - L.S s k| < ε' / 2 := by
    filter_upwards [hS T1 (ε' / 2) (half_pos hε')] with n hn s hs k
    have hs' : ¬ s < 0 := not_lt.mpr hs.1
    have h1 : ‖(if s < 0 then (0 : ℝ) else
        (((net n).S ((n : ℝ) * s) k : ℝ) - mun n k * n * s) / Real.sqrt n)
          - (if s < 0 then (0 : Fin J → ℝ) else L.S s) k‖ < ε' / 2 :=
      lt_of_le_of_lt (norm_le_pi_norm ((scaledPrimitives χ (net n) (lamn n) (mun n) P n).2.2.1 s
        - L.toPrim.2.2.1 s) k) (hn s hs)
    rw [if_neg hs', if_neg hs', Real.norm_eq_abs] at h1
    exact h1
  have hRu : ∀ᶠ n : ℕ in atTop, ∀ s ∈ Set.Icc 0 T', ∀ i k,
      |((routingCount χ i k ⌊(n : ℝ) * s⌋₊ : ℝ) - P i k * n * s) / Real.sqrt n - L.R s i k|
        < ε' / 2 := by
    filter_upwards [hR T' (ε' / 2) (half_pos hε')] with n hn s hs i k
    have hs' : ¬ s < 0 := not_lt.mpr hs.1
    have h1 : ‖(if s < 0 then (0 : ℝ) else
        ((routingCount χ i k ⌊(n : ℝ) * s⌋₊ : ℝ) - P i k * n * s) / Real.sqrt n)
          - (if s < 0 then (0 : Fin J → Fin J → ℝ) else L.R s) i k‖ < ε' / 2 :=
      lt_of_le_of_lt ((norm_le_pi_norm (((scaledPrimitives χ (net n) (lamn n) (mun n) P n).2.2.2.1 s
        - L.toPrim.2.2.2.1 s) i) k).trans
          (norm_le_pi_norm ((scaledPrimitives χ (net n) (lamn n) (mun n) P n).2.2.2.1 s
            - L.toPrim.2.2.2.1 s) i)) (hn s hs)
    rw [if_neg hs', if_neg hs', Real.norm_eq_abs] at h1
    exact h1
  have hSn : ∀ᶠ n : ℕ in atTop, ∀ t ∈ Set.Icc 0 T1, ∀ k,
      |((net n).S ((n : ℝ) * t) k : ℝ) - mun n k * n * t| ≤ KS * Real.sqrt n := by
    filter_upwards [hKS, eventually_ge_atTop 1] with n hn hn1 t ht k
    have h1 : ‖(if t < 0 then (0 : ℝ) else
        (((net n).S ((n : ℝ) * t) k : ℝ) - mun n k * n * t) / Real.sqrt n)‖ ≤ KS :=
      (norm_le_pi_norm ((scaledPrimitives χ (net n) (lamn n) (mun n) P n).2.2.1 t) k).trans
        (hn t ht)
    rw [if_neg (not_lt.mpr ht.1), Real.norm_eq_abs] at h1
    exact div_sqrt_bound hn1 h1
  have hBu : ∀ᶠ n : ℕ in atTop, ∀ k, ∀ t ∈ Set.Icc 0 T1, |B n (n * t) k / n - t| < η1 := by
    rw [eventually_all]
    intro k
    filter_upwards [h42 k T1 η1 hη1] with n hn t ht
    have h1 := hn t ht
    rw [Real.norm_eq_abs] at h1
    exact h1
  have hmuev : ∀ᶠ n : ℕ in atTop, ∀ k, mu k / 2 < mun n k ∧ mun n k < mu k + 1 := by
    rw [eventually_all]
    intro k
    have h := tendsto_pi_nhds.1 hmuc k
    exact (h.eventually (lt_mem_nhds (by linarith [hmu0 k]))).and
      (h.eventually (gt_mem_nhds (by linarith)))
  have hmud : ∀ᶠ n : ℕ in atTop, ∀ k, |mun n k - mu k| * T1 ≤ δR / 3 := by
    rw [eventually_all]
    intro k
    have hr : 0 < δR / (3 * (T1 + 1)) := div_pos hδR (by linarith)
    filter_upwards [(tendsto_pi_nhds.1 hmuc k).eventually
      (Ioo_mem_nhds (show mu k - δR / (3 * (T1 + 1)) < mu k by linarith)
        (show mu k < mu k + δR / (3 * (T1 + 1)) by linarith))] with n hn
    have h1 : |mun n k - mu k| < δR / (3 * (T1 + 1)) :=
      abs_sub_lt_iff.2 ⟨by linarith [hn.2], by linarith [hn.1]⟩
    rw [lt_div_iff₀ (show (0 : ℝ) < 3 * (T1 + 1) by linarith)] at h1
    nlinarith [abs_nonneg (mun n k - mu k)]
  have hsq : ∀ᶠ n : ℕ in atTop, 3 * KS < Real.sqrt n * δR := by
    filter_upwards [hsqrt.eventually (eventually_gt_atTop (3 * KS / δR))] with n hn
    rwa [div_lt_iff₀ hδR] at hn
  filter_upwards [eventually_ge_atTop 1, hAu, hSu, hRu, hSn, hBu, hmuev, hmud, hsq]
    with n hn1 hAu' hSu' hRu' hSn' hBu' hmuev' hmud' hsq'
  intro t ht
  have htT1 : t ∈ Set.Icc 0 T1 := ⟨ht.1, ht.2.trans hTT1⟩
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
  have hn0 : (n : ℝ) ≠ 0 := hnpos.ne'
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
  have hss : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hnpos.le
  have hnt : 0 ≤ (n : ℝ) * t := mul_nonneg hnpos.le htT1.1
  have hBk : ∀ k, 0 ≤ B n (n * t) k ∧ B n (n * t) k ≤ n * t := fun k =>
    B_bounds χ (net n) (Z n) (B n) (hsol n) (n * t) hnt k
  have hntT : (n : ℝ) * t ≤ n * T1 := mul_le_mul_of_nonneg_left htT1.2 hnpos.le
  have hsk : ∀ k, B n (n * t) k / n ∈ Set.Icc 0 T1 := fun k =>
    ⟨div_nonneg (hBk k).1 hnpos.le, (div_le_iff₀ hnpos).2 (by linarith [(hBk k).2])⟩
  have hmunmax : ∀ k, mun n k ≤ μmax := fun k => by linarith [(hmuev' k).2, hμmaxk k]
  have hSb : ∀ k, |((net n).S (B n (n * t) k) k : ℝ) - mun n k * B n (n * t) k|
      ≤ KS * Real.sqrt n := by
    intro k
    have h1 := hSn' (B n (n * t) k / n) (hsk k) k
    have e2 : mun n k * n * (B n (n * t) k / n) = mun n k * B n (n * t) k := by
      rw [mul_assoc, mul_div_cancel₀ _ hn0]
    rw [e2, mul_div_cancel₀ _ hn0] at h1
    exact h1
  have hSp : ∀ k, |(((net n).S (B n (n * t) k) k : ℝ) - mun n k * B n (n * t) k) / Real.sqrt n
      - L.S t k| < ε' := by
    intro k
    have h1 := hSu' (B n (n * t) k / n) (hsk k) k
    have e2 : mun n k * n * (B n (n * t) k / n) = mun n k * B n (n * t) k := by
      rw [mul_assoc, mul_div_cancel₀ _ hn0]
    rw [e2, mul_div_cancel₀ _ hn0] at h1
    have h2 : |L.S (B n (n * t) k / n) k - L.S t k| < ε' / 2 := by
      have hd := hδSc (B n (n * t) k / n) (hsk k) t htT1
        (by rw [Real.dist_eq]; exact lt_of_lt_of_le (hBu' k t htT1) hη1S)
      refine lt_of_le_of_lt ?_ hd
      rw [← Real.dist_eq]
      exact dist_le_pi_dist _ _ k
    have h3 := abs_sub_le ((((net n).S (B n (n * t) k) k : ℝ) - mun n k * B n (n * t) k)
      / Real.sqrt n) (L.S (B n (n * t) k / n) k) (L.S t k)
    linarith
  show ‖(Real.sqrt n)⁻¹ • xi χ (net n) (lamn n) (mun n) P (B n) (n * t) - xiHat L mu P t‖ < ε
  rw [pi_norm_lt_iff hε]
  intro j
  rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs]
  have hRr : ∀ k, |((routingCount χ k j ((net n).S (B n (n * t) k) k) : ℝ)
      - P k j * ((net n).S (B n (n * t) k) k : ℝ)) / Real.sqrt n - L.R (mu k * t) k j| < ε' := by
    intro k
    have hB1 : |B n (n * t) k - n * t| < η1 * n := by
      have h := hBu' k t htT1
      rw [show B n (n * t) k / n - t = (B n (n * t) k - n * t) / n by
        rw [sub_div, mul_div_cancel_left₀ t hn0], abs_div, abs_of_pos hnpos,
        div_lt_iff₀ hnpos] at h
      exact h
    have hSbk := abs_le.mp (hSb k)
    have hsn : Real.sqrt n ≤ n := by
      have hs1 : 1 ≤ Real.sqrt n := by
        rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
        exact Real.sqrt_le_sqrt (by exact_mod_cast hn1)
      nlinarith [mul_le_mul_of_nonneg_left hs1 hs.le]
    have hq : ((net n).S (B n (n * t) k) k : ℝ) / n ∈ Set.Icc 0 T' := by
      have hmB : mun n k * B n (n * t) k ≤ μmax * (n * T1) :=
        mul_le_mul (hmunmax k) (by linarith [(hBk k).2]) (hBk k).1 hμmax0
      have hKSn : KS * Real.sqrt n ≤ KS * n := mul_le_mul_of_nonneg_left hsn hKS0
      refine ⟨div_nonneg (Nat.cast_nonneg _) hnpos.le, (div_le_iff₀ hnpos).2 ?_⟩
      rw [hT']
      linarith [hSbk.2]
    have hmt : mu k * t ∈ Set.Icc 0 T' := by
      refine ⟨mul_nonneg (hmu0 k).le htT1.1, ?_⟩
      have : mu k * t ≤ μmax * T1 :=
        mul_le_mul (by linarith [hμmaxk k]) htT1.2 htT1.1 hμmax0
      rw [hT']
      linarith
    have hclose : |((net n).S (B n (n * t) k) k : ℝ) / n - mu k * t| < δR := by
      have ha : 3 * KS * Real.sqrt n < δR * n := by
        have h1 := mul_lt_mul_of_pos_right hsq' hs
        have e : Real.sqrt n * δR * Real.sqrt n = δR * n := by
          rw [show Real.sqrt n * δR * Real.sqrt n = δR * (Real.sqrt n * Real.sqrt n) by ring, hss]
        linarith
      have hb : |(mun n k - mu k) * B n (n * t) k| ≤ n * (δR / 3) := by
        rw [abs_mul, abs_of_nonneg (hBk k).1]
        have h1 : |mun n k - mu k| * B n (n * t) k ≤ |mun n k - mu k| * (n * T1) :=
          mul_le_mul_of_nonneg_left (by linarith [(hBk k).2]) (abs_nonneg _)
        have h2 := mul_le_mul_of_nonneg_left (hmud' k) hnpos.le
        linarith
      have hc : |mu k * (B n (n * t) k - n * t)| ≤ n * (δR / 3) := by
        rw [abs_mul, abs_of_nonneg (hmu0 k).le]
        have h1 : mu k * |B n (n * t) k - n * t| ≤ mu k * (η1 * n) :=
          mul_le_mul_of_nonneg_left hB1.le (hmu0 k).le
        have h2 : mu k * η1 ≤ δR / 3 := by
          have := mul_le_mul_of_nonneg_right (show mu k ≤ μmax + 1 by linarith [hμmaxk k]) hη1.le
          linarith
        have h3 := mul_le_mul_of_nonneg_left h2 hnpos.le
        linarith
      have hb' := abs_le.mp hb
      have hc' := abs_le.mp hc
      have htot : |((net n).S (B n (n * t) k) k : ℝ) - mu k * (n * t)| < δR * n := by
        rw [abs_lt]
        constructor <;> linarith
      rw [show ((net n).S (B n (n * t) k) k : ℝ) / n - mu k * t
          = (((net n).S (B n (n * t) k) k : ℝ) - mu k * (n * t)) / n by
        rw [sub_div, mul_comm (n : ℝ) t, ← mul_assoc, mul_div_cancel_right₀ _ hn0],
        abs_div, abs_of_pos hnpos, div_lt_iff₀ hnpos]
      exact htot
    have h1 := hRu' _ hq k j
    have e3 : P k j * n * (((net n).S (B n (n * t) k) k : ℝ) / n)
        = P k j * ((net n).S (B n (n * t) k) k : ℝ) := by
      rw [mul_assoc, mul_div_cancel₀ _ hn0]
    rw [e3, mul_div_cancel₀ _ hn0, Nat.floor_natCast] at h1
    have h2 : |L.R (((net n).S (B n (n * t) k) k : ℝ) / n) k j - L.R (mu k * t) k j|
        < ε' / 2 := by
      have hd := hδRc _ hq _ hmt (by rw [Real.dist_eq]; exact hclose)
      refine lt_of_le_of_lt ?_ hd
      rw [← Real.dist_eq]
      exact (dist_le_pi_dist _ _ j).trans (dist_le_pi_dist _ _ k)
    have h3 := abs_sub_le (((routingCount χ k j ((net n).S (B n (n * t) k) k) : ℝ)
      - P k j * ((net n).S (B n (n * t) k) k : ℝ)) / Real.sqrt n)
      (L.R (((net n).S (B n (n * t) k) k : ℝ) / n) k j) (L.R (mu k * t) k j)
    linarith
  have hxi : (Real.sqrt n)⁻¹ * xi χ (net n) (lamn n) (mun n) P (B n) (n * t) j
      = (((net n).A ((n : ℝ) * t) j : ℝ) - lamn n j * n * t) / Real.sqrt n
        + (∑ k, ((routingCount χ k j ((net n).S (B n (n * t) k) k) : ℝ)
            - P k j * ((net n).S (B n (n * t) k) k : ℝ))) / Real.sqrt n
        + (∑ k, P k j * (((net n).S (B n (n * t) k) k : ℝ) - mun n k * B n (n * t) k))
            / Real.sqrt n
        - (((net n).S (B n (n * t) j) j : ℝ) - mun n j * B n (n * t) j) / Real.sqrt n := by
    show (Real.sqrt n)⁻¹ * ((((net n).A ((n : ℝ) * t) j : ℝ) - lamn n j * (n * t)
      + ∑ k, ((routingCount χ k j ((net n).S (B n (n * t) k) k) : ℝ)
            - P k j * ((net n).S (B n (n * t) k) k : ℝ))
      + ∑ k, P k j * (((net n).S (B n (n * t) k) k : ℝ) - mun n k * B n (n * t) k)
      - (((net n).S (B n (n * t) j) j : ℝ) - mun n j * B n (n * t) j))) = _
    ring
  have hxh : xiHat L mu P t j = L.A t j + ∑ k, L.R (mu k * t) k j
      + ∑ k, P k j * L.S t k - L.S t j := by
    show L.A t j + ∑ k, (L.R (mu k * t) k j + P k j * L.S t k) - L.S t j = _
    rw [Finset.sum_add_distrib]
    ring
  have hsumR : |(∑ k, ((routingCount χ k j ((net n).S (B n (n * t) k) k) : ℝ)
            - P k j * ((net n).S (B n (n * t) k) k : ℝ))) / Real.sqrt n
        - ∑ k, L.R (mu k * t) k j| ≤ J * ε' := by
    rw [Finset.sum_div, ← Finset.sum_sub_distrib]
    calc _ ≤ ∑ k, |((routingCount χ k j ((net n).S (B n (n * t) k) k) : ℝ)
            - P k j * ((net n).S (B n (n * t) k) k : ℝ)) / Real.sqrt n - L.R (mu k * t) k j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin J, ε' := Finset.sum_le_sum fun k _ => (hRr k).le
      _ = J * ε' := by simp
  have hsumS : |(∑ k, P k j * (((net n).S (B n (n * t) k) k : ℝ) - mun n k * B n (n * t) k))
        / Real.sqrt n - ∑ k, P k j * L.S t k| ≤ J * ε' := by
    rw [Finset.sum_div, ← Finset.sum_sub_distrib]
    calc _ ≤ ∑ k, |P k j * (((net n).S (B n (n * t) k) k : ℝ) - mun n k * B n (n * t) k)
            / Real.sqrt n - P k j * L.S t k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin J, ε' := Finset.sum_le_sum fun k _ => by
          rw [mul_div_assoc, ← mul_sub, abs_mul, abs_of_nonneg (hP0 k j)]
          exact (mul_le_of_le_one_left (abs_nonneg _) (hP1 k j)).trans (hSp k).le
      _ = J * ε' := by simp
  rw [hxi, hxh]
  have hAa := abs_lt.mp (hAu' t htT1 j)
  have hR' := abs_le.mp hsumR
  have hS' := abs_le.mp hsumS
  have hSj := abs_lt.mp (hSp j)
  rw [abs_lt]
  constructor <;> linarith
