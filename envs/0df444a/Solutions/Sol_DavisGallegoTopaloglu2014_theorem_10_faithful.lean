-- Prove2me | solution 1 for DavisGallegoTopaloglu2014.theorem_10_faithful
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T04:14:28.558003+00:00
-- url     : https://prove2.me/submissions/7b594639-5a40-4e7a-9d2d-952b431e7620

import Mathlib
import Definitions.Def_NestedLogitVariants_PartialCompetitive_Model
import Definitions.Def_NestedLogitVariants_PartialCompetitive_Knapsack

open NestedLogitVariants.PartialCompetitive

theorem dg86_x_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (I : NestedLogitVariants.PartialCompetitive.Instance ι n)
    (hv0 : 0 ≤ I.v0) (hvnp : ∀ i, 0 ≤ I.vnp i) (hv : ∀ i j, 0 ≤ I.v i j)
    (hr : ∀ i j, 0 ≤ I.r i j)
    (A : ι → Set (Finset (Fin n))) (hA : ∀ i, ∅ ∈ A i)
    (xh : ℝ) (yh : ι → ℝ) (hopt : LP4Optimal I A xh yh) : 0 ≤ xh := by
  have hV : ∀ i S, 0 ≤ V I i S := fun i S =>
    add_nonneg (hvnp i) (Finset.sum_nonneg fun j _ => hv i j)
  have hnw : ∀ i S, 0 ≤ nestWeight I i S := fun i S => Real.rpow_nonneg (hV i S) _
  have hR : ∀ i S, 0 ≤ R I i S := fun i S =>
    div_nonneg (Finset.sum_nonneg fun j _ => mul_nonneg (hr i j) (hv i j)) (hV i S)
  obtain ⟨⟨hf1, hf2⟩, hmin⟩ := hopt
  by_contra hx
  push Not at hx
  have hy0 : ∀ i, 0 ≤ yh i := fun i =>
    le_trans (mul_nonneg (hnw i ∅) (by linarith [hR i ∅])) (hf2 i ∅ (hA i))
  have hsum0 : 0 ≤ ∑ i, yh i := Finset.sum_nonneg fun i _ => hy0 i
  have hv0x : I.v0 * xh ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hv0 hx.le
  have hsum : ∑ i, yh i = 0 := by linarith
  have hyz : ∀ i, yh i = 0 := fun i =>
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hy0 i)).1 hsum i (Finset.mem_univ i)
  have hv0z : I.v0 = 0 := by
    by_contra h
    have : 0 < I.v0 := lt_of_le_of_ne hv0 (Ne.symm h)
    nlinarith
  have hnw0 : ∀ i, ∀ S ∈ A i, nestWeight I i S = 0 := by
    intro i S hS
    have h := hf2 i S hS
    rw [hyz i] at h
    have h1 := hnw i S
    have h2 := hR i S
    by_contra hne
    have : 0 < nestWeight I i S := lt_of_le_of_ne h1 (Ne.symm hne)
    nlinarith
  have hfeas : LP4Feasible I A (xh - 1) yh := by
    refine ⟨by rw [hsum, hv0z]; simp, ?_⟩
    intro i S hS
    rw [hnw0 i S hS, hyz i]; simp
  have := hmin _ _ hfeas
  linarith


theorem dg86_mem_Shat {ι : Type*} {n : ℕ} (I : NestedLogitVariants.PartialCompetitive.Instance ι n)
    (i : ι) (ε : ℝ) (hv : ∀ j, 0 ≤ I.v i j) (j : Fin n) :
    j ∈ Shat I i ε ↔ I.v i j ≤ ε ∧ 0 < I.v i j ∧ prefixLoad I i ε j + I.v i j ≤ ε := by
  unfold Shat; rw [Finset.mem_filter]; simp only [Finset.mem_univ, true_and, zhat]
  split_ifs with h
  · constructor
    · intro h1
      have hm : min 1 ((ε - prefixLoad I i ε j) / I.v i j) = 1 := by
        have := min_le_left 1 ((ε - prefixLoad I i ε j) / I.v i j)
        rcases le_total 0 (min 1 ((ε - prefixLoad I i ε j) / I.v i j)) with h2 | h2
        · rw [max_eq_right h2] at h1; exact h1
        · rw [max_eq_left h2] at h1; norm_num at h1
      have hq : 1 ≤ (ε - prefixLoad I i ε j) / I.v i j := by
        rw [← hm]; exact min_le_right _ _
      have hvp : 0 < I.v i j := by
        rcases (hv j).lt_or_eq with h3 | h3
        · exact h3
        · rw [← h3] at hq; simp at hq; linarith
      refine ⟨h, hvp, ?_⟩
      rw [le_div_iff₀ hvp] at hq; linarith
    · rintro ⟨-, hvp, hP⟩
      have hq : 1 ≤ (ε - prefixLoad I i ε j) / I.v i j := by
        rw [le_div_iff₀ hvp]; linarith
      rw [min_eq_left hq, max_eq_right zero_le_one]
  · simp only [zero_ne_one, false_iff]
    rintro ⟨h1, -⟩; exact h h1

theorem dg86_Shat_zero {ι : Type*} {n : ℕ} (I : NestedLogitVariants.PartialCompetitive.Instance ι n)
    (i : ι) (hv : ∀ j, 0 ≤ I.v i j) : Shat I i 0 = ∅ := by
  ext j
  rw [dg86_mem_Shat I i 0 hv]
  simp only [Finset.notMem_empty, iff_false, not_and]
  intro h1 h2; linarith

/-- exchange inequality -/
theorem dg86_exch {n : ℕ} (r w : Fin n → ℝ) (S H : Finset (Fin n)) (ρ : ℝ)
    (h1 : ∀ j ∈ H, j ∉ S → ρ * w j ≤ r j * w j) (h2 : ∀ j ∈ S, j ∉ H → r j * w j ≤ ρ * w j) :
    ∑ j ∈ S, r j * w j ≤ ∑ j ∈ H, r j * w j + ρ * (∑ j ∈ S, w j - ∑ j ∈ H, w j) := by
  have eS := Finset.sum_filter_add_sum_filter_not S (fun j => j ∈ H) (fun j => r j * w j)
  have eH := Finset.sum_filter_add_sum_filter_not H (fun j => j ∈ S) (fun j => r j * w j)
  have fS := Finset.sum_filter_add_sum_filter_not S (fun j => j ∈ H) w
  have fH := Finset.sum_filter_add_sum_filter_not H (fun j => j ∈ S) w
  have hc : S.filter (fun j => j ∈ H) = H.filter (fun j => j ∈ S) := by
    ext j; simp [and_comm]
  rw [hc] at eS fS
  have k1 : ∑ j ∈ S.filter (fun j => j ∉ H), r j * w j ≤
      ρ * ∑ j ∈ S.filter (fun j => j ∉ H), w j := by
    rw [Finset.mul_sum]; apply Finset.sum_le_sum; intro j hj
    rw [Finset.mem_filter] at hj; exact h2 j hj.1 hj.2
  have k2 : ρ * ∑ j ∈ H.filter (fun j => j ∉ S), w j ≤
      ∑ j ∈ H.filter (fun j => j ∉ S), r j * w j := by
    rw [Finset.mul_sum]; apply Finset.sum_le_sum; intro j hj
    rw [Finset.mem_filter] at hj; exact h1 j hj.1 hj.2
  rw [← eS, ← eH, ← fS, ← fH]
  nlinarith

/-- the greedy/knapsack bound -/
theorem dg86_knap {ι : Type*} {n : ℕ} (I : NestedLogitVariants.PartialCompetitive.Instance ι n)
    (i : ι) (hv : ∀ j, 0 ≤ I.v i j) (hr : ∀ j, 0 ≤ I.r i j) (hanti : Antitone (I.r i))
    (S : Finset (Fin n)) :
    ∃ A ∈ candidates I i, ∃ T ∈ candidates I i,
      ∑ j ∈ S, I.r i j * I.v i j ≤ ∑ j ∈ A, I.r i j * I.v i j + ∑ j ∈ T, I.r i j * I.v i j ∧
      ∑ j ∈ A, I.v i j ≤ ∑ j ∈ S, I.v i j ∧ ∑ j ∈ T, I.v i j ≤ ∑ j ∈ S, I.v i j := by
  set ε := ∑ j ∈ S, I.v i j with hε
  have hε0 : 0 ≤ ε := Finset.sum_nonneg fun j _ => hv j
  have hSE : ∀ j ∈ S, I.v i j ≤ ε := fun j hj =>
    Finset.single_le_sum (f := fun j => I.v i j) (fun j _ => hv j) hj
  set H := Shat I i ε with hH
  have hmem := dg86_mem_Shat I i ε hv
  have hHc : H ∈ candidates I i := Or.inl ⟨ε, hε0, rfl⟩
  have hempty : (∅ : Finset (Fin n)) ∈ candidates I i := Or.inl ⟨0, le_rfl, (dg86_Shat_zero I i hv).symm⟩
  -- (a) total weight of H ≤ ε
  have hHw : ∑ j ∈ H, I.v i j ≤ ε := by
    rcases H.eq_empty_or_nonempty with he | hne
    · rw [he]; simpa using hε0
    · set m := H.max' hne
      have hm : m ∈ H := H.max'_mem hne
      have hsub : H ⊆ insert m (Finset.univ.filter (fun k => k < m ∧ I.v i k ≤ ε)) := by
        intro j hj
        rcases (H.le_max' j hj).lt_or_eq with h | h
        · exact Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨Finset.mem_univ _, h, ((hmem j).1 hj).1⟩)
        · rw [h]; exact Finset.mem_insert_self _ _
      have hnot : m ∉ Finset.univ.filter (fun k => k < m ∧ I.v i k ≤ ε) := by simp
      calc ∑ j ∈ H, I.v i j
          ≤ ∑ j ∈ insert m (Finset.univ.filter (fun k => k < m ∧ I.v i k ≤ ε)), I.v i j :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hv j)
        _ = I.v i m + prefixLoad I i ε m := by rw [Finset.sum_insert hnot]; rfl
        _ ≤ ε := by linarith [((hmem m).1 hm).2.2]
  refine ⟨H, hHc, ?_⟩
  set B := Finset.univ.filter (fun j => I.v i j ≤ ε ∧ 0 < I.v i j ∧ j ∉ H) with hB
  rcases B.eq_empty_or_nonempty with hBe | hBne
  · refine ⟨∅, hempty, ?_, hHw, by simpa using hε0⟩
    have := dg86_exch (I.r i) (I.v i) S H 0
      (fun j _ _ => by rw [zero_mul]; exact mul_nonneg (hr j) (hv j))
      (fun j hj hjH => by
        have : I.v i j = 0 := by
          by_contra hne
          have hp : 0 < I.v i j := lt_of_le_of_ne (hv j) (Ne.symm hne)
          have : j ∈ B := by simp [hB, hSE j hj, hp, hjH]
          rw [hBe] at this; simp at this
        rw [this]; simp)
    simpa using this
  · set k := B.min' hBne
    have hk : k ∈ B := B.min'_mem hBne
    have hk' : I.v i k ≤ ε ∧ 0 < I.v i k ∧ k ∉ H := by simpa [hB] using hk
    have hkP : ε < prefixLoad I i ε k + I.v i k := by
      by_contra h; push Not at h
      exact hk'.2.2 ((hmem k).2 ⟨hk'.1, hk'.2.1, h⟩)
    have hkc : ({k} : Finset (Fin n)) ∈ candidates I i := Or.inr ⟨k, rfl⟩
    refine ⟨{k}, hkc, ?_, hHw, by simpa using hk'.1⟩
    have hex := dg86_exch (I.r i) (I.v i) S H (I.r i k)
      (fun j hj _ => by
        apply mul_le_mul_of_nonneg_right _ (hv j)
        apply hanti
        by_contra hlt; push Not at hlt
        have hjm := (hmem j).1 hj
        have hsub : insert k (Finset.univ.filter (fun l => l < k ∧ I.v i l ≤ ε)) ⊆
            Finset.univ.filter (fun l => l < j ∧ I.v i l ≤ ε) := by
          intro l hl
          rcases Finset.mem_insert.1 hl with h | h
          · rw [h]; simp [hlt, hk'.1]
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
            exact ⟨h.1.trans hlt, h.2⟩
        have hnot : k ∉ Finset.univ.filter (fun l => l < k ∧ I.v i l ≤ ε) := by simp
        have := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun l _ _ => hv l)
        rw [Finset.sum_insert hnot] at this
        have e1 : prefixLoad I i ε j = ∑ l ∈ Finset.univ.filter (fun l => l < j ∧ I.v i l ≤ ε), I.v i l := rfl
        have e2 : prefixLoad I i ε k = ∑ l ∈ Finset.univ.filter (fun l => l < k ∧ I.v i l ≤ ε), I.v i l := rfl
        linarith [hjm.2.2, hv j])
      (fun j hj hjH => by
        rcases (hv j).lt_or_eq with hp | h0
        · apply mul_le_mul_of_nonneg_right _ (hv j)
          apply hanti
          apply B.min'_le
          simp [hB, hSE j hj, hp, hjH]
        · rw [← h0]; simp)
    -- prefixLoad k ≤ weight of H
    have hPH : prefixLoad I i ε k ≤ ∑ j ∈ H, I.v i j := by
      unfold prefixLoad
      rw [← Finset.sum_filter_ne_zero]
      apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun j _ _ => hv j)
      intro l hl
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
      obtain ⟨⟨hlk, hlE⟩, hl0⟩ := hl
      by_contra hlH
      have hp : 0 < I.v i l := lt_of_le_of_ne (hv l) (Ne.symm hl0)
      have : l ∈ B := by simp [hB, hlE, hp, hlH]
      have := B.min'_le l this
      exact absurd hlk (not_lt.2 this)
    simp only [Finset.sum_singleton]
    have hrk := hr k
    have : I.r i k * (ε - ∑ j ∈ H, I.v i j) ≤ I.r i k * I.v i k :=
      mul_le_mul_of_nonneg_left (by linarith) hrk
    linarith

theorem dg86_one {γ x c a NA : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hx : 0 ≤ x) (hNA : 0 ≤ NA)
    (hc : 0 < c) (ha0 : 0 ≤ a) (hac : a ≤ c) (hNA0 : a = 0 → NA = 0) (hγa : a = 0 → γ ≠ 0) :
    NA * c ^ (γ - 1) - x * c ^ γ ≤ a ^ γ * (NA / a - x) := by
  rcases ha0.lt_or_eq with hapos | ha
  · have e : a ^ γ * (NA / a - x) = NA * a ^ (γ - 1) - x * a ^ γ := by
      rw [Real.rpow_sub_one hapos.ne']; field_simp
    rw [e]
    have h1 : c ^ (γ - 1) ≤ a ^ (γ - 1) := Real.rpow_le_rpow_of_nonpos hapos hac (by linarith)
    have h2 : a ^ γ ≤ c ^ γ := Real.rpow_le_rpow ha0 hac hγ0
    nlinarith
  · subst ha
    rw [hNA0 rfl, Real.zero_rpow (hγa rfl)]
    have := Real.rpow_nonneg hc.le γ
    simp; nlinarith

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (I : NestedLogitVariants.PartialCompetitive.Instance ι n)
    (hv0 : 0 ≤ I.v0) (hvnp : ∀ i, 0 ≤ I.vnp i) (hv : ∀ i j, 0 ≤ I.v i j)
    (hr : ∀ i j, 0 ≤ I.r i j) (hγ0 : ∀ i, 0 ≤ I.γ i) (hγv : ∀ i, I.γ i = 0 → 0 < I.vnp i)
    (hanti : ∀ i, Antitone (I.r i))
    (hγ : ∀ i, I.γ i ≤ 1)
    (xh : ℝ) (yh : ι → ℝ) (hopt : LP4Optimal I (candidates I) xh yh) :
    LP3Feasible I (2 * xh) (2 • yh) := by
  have hA : ∀ i, (∅ : Finset (Fin n)) ∈ candidates I i := fun i =>
    Or.inl ⟨0, le_rfl, (dg86_Shat_zero I i (hv i)).symm⟩
  have hx := dg86_x_nonneg I hv0 hvnp hv hr _ hA xh yh hopt
  obtain ⟨⟨hf1, hf2⟩, _⟩ := hopt
  have hN : ∀ i (S : Finset (Fin n)), 0 ≤ ∑ j ∈ S, I.r i j * I.v i j := fun i S =>
    Finset.sum_nonneg fun j _ => mul_nonneg (hr i j) (hv i j)
  have hW : ∀ i (S : Finset (Fin n)), 0 ≤ ∑ j ∈ S, I.v i j := fun i S =>
    Finset.sum_nonneg fun j _ => hv i j
  refine ⟨?_, ?_⟩
  · simp only [Pi.smul_apply, nsmul_eq_mul, ← Finset.mul_sum]
    push_cast
    nlinarith
  intro i S
  simp only [Pi.smul_apply, nsmul_eq_mul]
  push_cast
  -- zero-weight sets have zero numerator
  have hNz : ∀ T : Finset (Fin n), V I i T = 0 → ∑ j ∈ T, I.r i j * I.v i j = 0 := by
    intro T hT
    have h1 : ∑ j ∈ T, I.v i j = 0 := by
      unfold V at hT; linarith [hvnp i, hW i T]
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hv i j)).1 h1
    exact Finset.sum_eq_zero fun j hj => by rw [h2 j hj, mul_zero]
  have hγz : ∀ T : Finset (Fin n), V I i T = 0 → I.γ i ≠ 0 := by
    intro T hT h0
    have := hγv i h0
    unfold V at hT; linarith [hW i T]
  rcases (add_nonneg (hvnp i) (hW i S)).lt_or_eq with hc | hc
  · obtain ⟨A, hAc, T, hTc, hNS, hAw, hTw⟩ := dg86_knap I i (hv i) (hr i) (hanti i) S
    have hyA := hf2 i A hAc
    have hyT := hf2 i T hTc
    have hc' : 0 < V I i S := hc
    have k1 := dg86_one (hγ0 i) (hγ i) hx (hN i A) hc'
      (show 0 ≤ V I i A from add_nonneg (hvnp i) (hW i A))
      (show V I i A ≤ V I i S by simp only [V]; linarith) (hNz A) (hγz A)
    have k2 := dg86_one (hγ0 i) (hγ i) hx (hN i T) hc'
      (show 0 ≤ V I i T from add_nonneg (hvnp i) (hW i T))
      (show V I i T ≤ V I i S by simp only [V]; linarith) (hNz T) (hγz T)
    have e : nestWeight I i S * (R I i S - 2 * xh) =
        (∑ j ∈ S, I.r i j * I.v i j) * (V I i S) ^ (I.γ i - 1) - 2 * xh * (V I i S) ^ I.γ i := by
      unfold nestWeight R
      rw [Real.rpow_sub_one hc'.ne']; field_simp
    unfold nestWeight R at hyA hyT
    rw [e]
    have hpow : 0 ≤ (V I i S) ^ (I.γ i - 1) := Real.rpow_nonneg hc.le _
    have := mul_le_mul_of_nonneg_right hNS hpow
    nlinarith
  · have hS0 : V I i S = 0 := hc.symm
    have hy := hf2 i ∅ (hA i)
    have hE0 : V I i ∅ = 0 := by
      unfold V at hS0 ⊢; simp; linarith [hW i S, hvnp i]
    unfold nestWeight at hy ⊢
    rw [hS0, Real.zero_rpow (hγz S hS0)]
    rw [hE0, Real.zero_rpow (hγz S hS0)] at hy
    linarith
