-- Prove2me | solution 1 for DavisGallegoTopaloglu2014.theorem_7_faithful
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T04:31:51.552656+00:00
-- url     : https://prove2.me/submissions/13be290e-c22b-4e19-953f-bbc4abfef0c0

import Mathlib
import Definitions.Def_NestedLogitVariants_Synergistic_Model
import Definitions.Def_NestedLogitVariants_Synergistic_Factor

open NestedLogitVariants.Synergistic

theorem dg86_x_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (I : NestedLogitVariants.Synergistic.Instance ι n)
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
theorem dg86_prefix {n : ℕ} (r : Fin n → ℝ) (hr : Antitone r) (t : ℝ) :
    ∃ m ≤ n, Finset.univ.filter (fun k => t ≤ r k) = nbr n m := by
  by_cases hall : ∀ k, t ≤ r k
  · refine ⟨n, le_rfl, ?_⟩
    ext k; simp [nbr, hall k, k.isLt]
  · push Not at hall
    have hne : (Finset.univ.filter (fun k => r k < t)).Nonempty := by
      obtain ⟨k, hk⟩ := hall; exact ⟨k, by simp [hk]⟩
    refine ⟨((Finset.univ.filter (fun k => r k < t)).min' hne).val, by omega, ?_⟩
    have hk0 := (Finset.univ.filter (fun k => r k < t)).min'_mem hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk0
    ext k
    simp only [nbr, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hk
      by_contra hle
      push Not at hle
      have : r k ≤ r ((Finset.univ.filter (fun k => r k < t)).min' hne) := hr (Fin.le_def.2 hle)
      linarith
    · intro hk
      by_contra hlt
      push Not at hlt
      have := (Finset.univ.filter (fun k => r k < t)).min'_le k (by simp [hlt])
      exact absurd hk (not_lt.2 (Fin.le_def.1 this))

theorem dg86_tangent {p u W : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hu : 0 < u) (hW : 0 ≤ W) :
    W ^ p ≤ u ^ p + p * u ^ p / u * (W - u) := by
  have hs : -1 ≤ W / u - 1 := by have := div_nonneg hW hu.le; linarith
  have h1 := rpow_one_add_le_one_add_mul_self hs hp0 hp1
  have e : W = u * (1 + (W / u - 1)) := by field_simp; ring
  have hup : 0 ≤ u ^ p := Real.rpow_nonneg hu.le _
  calc W ^ p = u ^ p * (1 + (W / u - 1)) ^ p := by
        conv_lhs => rw [e]
        exact Real.mul_rpow hu.le (by linarith)
    _ ≤ u ^ p * (1 + p * (W / u - 1)) := mul_le_mul_of_nonneg_left h1 hup
    _ = u ^ p + p * u ^ p / u * (W - u) := by field_simp

theorem dg86_nest {ι : Type*} {n : ℕ} (I : NestedLogitVariants.Synergistic.Instance ι n) (i : ι)
    (z : ℝ) (hv : ∀ j, 0 ≤ I.v i j) (hγpos : 0 < I.γ i) (hγ1 : I.γ i ≤ 1)
    (hfc : I.vnp i = 0) (hanti : Antitone (I.r i)) (S0 : Finset (Fin n))
    (hmax : ∀ S, nestWeight I i S * (R I i S - z) ≤ nestWeight I i S0 * (R I i S0 - z))
    (hu : 0 < V I i S0) :
    ∃ m ≤ n, nestWeight I i S0 * (R I i S0 - z) ≤ nestWeight I i (nbr n m) * (R I i (nbr n m) - z)
      ∧ 0 < V I i (nbr n m) := by
  obtain ⟨hs, hhs⟩ : ∃ h, h = nestWeight I i S0 * (R I i S0 - z) := ⟨_, rfl⟩
  rw [← hhs] at hmax ⊢
  obtain ⟨p, hp⟩ : ∃ p, p = 1 - I.γ i := ⟨_, rfl⟩
  have hp0 : 0 ≤ p := by linarith
  have hp1 : p ≤ 1 := by linarith
  have hVe : ∀ S, V I i S = ∑ j ∈ S, I.v i j := fun S => by simp [V, hfc]
  have hV0 : ∀ S, 0 ≤ V I i S := fun S => by rw [hVe]; exact Finset.sum_nonneg fun j _ => hv j
  have hK : ∀ S, 0 < V I i S → V I i S ^ p * (nestWeight I i S * (R I i S - z)) =
      ∑ j ∈ S, I.r i j * I.v i j - z * V I i S := by
    intro S hS
    unfold nestWeight R
    rw [← mul_assoc, ← Real.rpow_add hS, hp, sub_add_cancel, Real.rpow_one]
    field_simp
  have hNz : ∀ S, V I i S = 0 → ∑ j ∈ S, I.r i j * I.v i j = 0 := by
    intro S hS
    rw [hVe] at hS
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hv j)).1 hS
    exact Finset.sum_eq_zero fun j hj => by rw [h2 j hj, mul_zero]
  have hE : V I i ∅ = 0 := by rw [hVe]; simp
  have h0 : 0 ≤ hs := by
    have := hmax ∅
    unfold nestWeight at this
    rwa [hE, Real.zero_rpow hγpos.ne', zero_mul] at this
  have hup : ∀ S, ∑ j ∈ S, I.r i j * I.v i j - z * V I i S ≤ hs * V I i S ^ p := by
    intro S
    rcases (hV0 S).lt_or_eq with h | h
    · rw [← hK S h, mul_comm hs]
      exact mul_le_mul_of_nonneg_left (hmax S) (Real.rpow_nonneg (hV0 S) _)
    · rw [hNz S h.symm, ← h]; simp
      exact mul_nonneg h0 (Real.rpow_nonneg le_rfl _)
  obtain ⟨u, hu'⟩ : ∃ u, u = V I i S0 := ⟨_, rfl⟩
  rw [← hu'] at hu
  obtain ⟨c, hc⟩ : ∃ c, c = hs * (p * u ^ p / u) := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by
    rw [hc]; exact mul_nonneg h0 (div_nonneg (mul_nonneg hp0 (Real.rpow_nonneg hu.le _)) hu.le)
  have htan : ∀ S, hs * V I i S ^ p ≤ hs * u ^ p + c * (V I i S - u) := by
    intro S
    have := mul_le_mul_of_nonneg_left (dg86_tangent hp0 hp1 hu (hV0 S)) h0
    rw [hc]; nlinarith
  have hLs : ∀ S, ∑ j ∈ S, I.r i j * I.v i j - (z + c) * V I i S =
      ∑ j ∈ S, I.v i j * (I.r i j - (z + c)) := by
    intro S
    rw [hVe, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _; ring
  have hS0K := hK S0 (hu'.symm ▸ hu)
  rw [← hu', ← hhs] at hS0K
  have hL : ∀ S, ∑ j ∈ S, I.v i j * (I.r i j - (z + c)) ≤
      ∑ j ∈ S0, I.v i j * (I.r i j - (z + c)) := by
    intro S
    rw [← hLs, ← hLs, ← hu']
    have := hup S
    have := htan S
    nlinarith
  obtain ⟨m, hm, hT⟩ := dg86_prefix (I.r i) hanti (z + c)
  refine ⟨m, hm, ?_⟩
  rw [← hT]
  set T := Finset.univ.filter (fun k => z + c ≤ I.r i k) with hTdef
  have hLT : ∑ j ∈ S0, I.v i j * (I.r i j - (z + c)) ≤ ∑ j ∈ T, I.v i j * (I.r i j - (z + c)) := by
    rw [hTdef, Finset.sum_filter]
    rw [← Finset.sum_filter_add_sum_filter_not S0 (fun j => z + c ≤ I.r i j)]
    have k1 : ∑ j ∈ S0.filter (fun j => ¬ z + c ≤ I.r i j), I.v i j * (I.r i j - (z + c)) ≤ 0 :=
      Finset.sum_nonpos fun j hj => by
        rw [Finset.mem_filter] at hj
        exact mul_nonpos_of_nonneg_of_nonpos (hv j) (by linarith [not_le.1 hj.2])
    have k2 : ∑ j ∈ S0.filter (fun j => z + c ≤ I.r i j), I.v i j * (I.r i j - (z + c)) ≤
        ∑ j, if z + c ≤ I.r i j then I.v i j * (I.r i j - (z + c)) else 0 := by
      rw [← Finset.sum_filter]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj; simp only [Finset.mem_filter] at hj ⊢; exact ⟨Finset.mem_univ _, hj.2⟩
      · intro j hj _
        simp only [Finset.mem_filter] at hj
        exact mul_nonneg (hv j) (by linarith [hj.2])
    linarith
  have hLeq := le_antisymm (hL T) hLT
  have hVT : u ≤ V I i T := by
    rw [hu', hVe, hVe, ← Finset.sum_filter_ne_zero]
    apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun j _ _ => hv j)
    intro j hj
    simp only [Finset.mem_filter] at hj
    obtain ⟨hjS, hj0⟩ := hj
    rw [hTdef, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    by_contra hlt
    push Not at hlt
    have hp' : 0 < I.v i j := lt_of_le_of_ne (hv j) (Ne.symm hj0)
    have h1 := Finset.add_sum_erase S0 (fun j => I.v i j * (I.r i j - (z + c))) hjS
    have h2 := hL (S0.erase j)
    have h3 : I.v i j * (I.r i j - (z + c)) < 0 := mul_neg_of_pos_of_neg hp' (by linarith)
    linarith
  have hVTp : 0 < V I i T := lt_of_lt_of_le hu hVT
  refine ⟨?_, hVTp⟩
  have hKT := hK T hVTp
  have hpos : 0 < V I i T ^ p := Real.rpow_pos_of_pos hVTp _
  have e1 := hLs T
  have e2 := hLs S0
  rw [← hu'] at e2
  have ht := htan T
  have : V I i T ^ p * hs ≤ V I i T ^ p * (nestWeight I i T * (R I i T - z)) := by
    rw [hKT]; nlinarith
  exact le_of_mul_le_mul_left this hpos

theorem dg86_nbr_succ {n m : ℕ} (h : m < n) :
    nbr n (m + 1) = insert ⟨m, h⟩ (nbr n m) ∧ (⟨m, h⟩ : Fin n) ∉ nbr n m := by
  constructor
  · ext k; simp only [nbr, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Fin.ext_iff]; omega
  · simp [nbr]

theorem dg86_rN {ι : Type*} {n : ℕ} (I : NestedLogitVariants.Synergistic.Instance ι n) (i : ι)
    (hv : ∀ j, 0 ≤ I.v i j) (hanti : Antitone (I.r i)) (hfc : I.vnp i = 0) {m : ℕ} (h : m < n) :
    I.r i ⟨m, h⟩ * V I i (nbr n m) ≤ ∑ j ∈ nbr n m, I.r i j * I.v i j := by
  simp only [V, hfc, zero_add, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  simp only [nbr, Finset.mem_filter, Finset.mem_univ, true_and] at hk
  exact mul_le_mul_of_nonneg_right (hanti (Fin.le_def.2 (by simp; omega))) (hv k)

/-- the nested sets with `j ≥ 1` have positive weight and revenue -/
theorem dg86_pos {ι : Type*} {n : ℕ} (I : NestedLogitVariants.Synergistic.Instance ι n) (i : ι)
    (hv : ∀ j, 0 ≤ I.v i j) (hr : ∀ j, 0 ≤ I.r i j) (hfc : I.vnp i = 0) (h0 : 0 < n)
    (hv1 : 0 < I.v i ⟨0, h0⟩) (hr1 : 0 < I.r i ⟨0, h0⟩) {m : ℕ} (hm : 1 ≤ m) :
    0 < V I i (nbr n m) ∧ 0 < ∑ j ∈ nbr n m, I.r i j * I.v i j := by
  have hmem : (⟨0, h0⟩ : Fin n) ∈ nbr n m := by simp [nbr]; omega
  constructor
  · simp only [V, hfc, zero_add]
    exact lt_of_lt_of_le hv1 (Finset.single_le_sum (f := fun j => I.v i j) (fun j _ => hv j) hmem)
  · exact lt_of_lt_of_le (mul_pos hr1 hv1)
      (Finset.single_le_sum (f := fun j => I.r i j * I.v i j)
        (fun j _ => mul_nonneg (hr j) (hv j)) hmem)

theorem dg86_RW {ι : Type*} {n : ℕ} (I : NestedLogitVariants.Synergistic.Instance ι n) (i : ι)
    (T : Finset (Fin n)) (hT : 0 < V I i T) (c : ℝ) :
    nestWeight I i T * (R I i T - c) =
      (∑ j ∈ T, I.r i j * I.v i j) * V I i T ^ (I.γ i - 1) - c * V I i T ^ I.γ i := by
  unfold nestWeight R
  rw [Real.rpow_sub_one hT.ne']; field_simp

theorem dg86_syn {ι : Type*} {n : ℕ} (I : NestedLogitVariants.Synergistic.Instance ι n) (i : ι)
    (z α y : ℝ) (hz : 0 ≤ z) (hα : 1 ≤ α)
    (hαt : ∀ j ∈ Finset.Icc 2 n, alphaTerm I i j ≤ α)
    (hv : ∀ j, 0 ≤ I.v i j) (hr : ∀ j, 0 ≤ I.r i j) (hanti : Antitone (I.r i))
    (hfc : I.vnp i = 0) (hγ1 : 1 ≤ I.γ i) (h0 : 0 < n) (hv1 : 0 < I.v i ⟨0, h0⟩)
    (hr1 : 0 < I.r i ⟨0, h0⟩)
    (hy : ∀ m ≤ n, nestWeight I i (nbr n m) * (R I i (nbr n m) - z) ≤ y) (S : Finset (Fin n)) :
    nestWeight I i S * (R I i S - α * z) ≤ α * y := by
  have hγ0 : I.γ i ≠ 0 := by linarith
  have hVe : ∀ T, V I i T = ∑ j ∈ T, I.v i j := fun T => by simp [V, hfc]
  have hV0 : ∀ T, 0 ≤ V I i T := fun T => by rw [hVe]; exact Finset.sum_nonneg fun j _ => hv j
  have hN0 : ∀ T : Finset (Fin n), 0 ≤ ∑ j ∈ T, I.r i j * I.v i j := fun T =>
    Finset.sum_nonneg fun j _ => mul_nonneg (hr j) (hv j)
  have hnb0 : nbr n 0 = ∅ := by ext k; simp [nbr]
  have hy0 : 0 ≤ y := by
    have := hy 0 (Nat.zero_le _)
    rw [hnb0] at this
    unfold nestWeight at this
    rwa [show V I i ∅ = 0 by simp [V, hfc], Real.zero_rpow hγ0, zero_mul] at this
  have hαy : 0 ≤ α * y := mul_nonneg (by linarith) hy0
  rcases (hV0 S).lt_or_eq with hVS | hVS
  swap
  · unfold nestWeight; rw [← hVS, Real.zero_rpow hγ0, zero_mul]; exact hαy
  -- locate the segment
  have hex : ∃ j, j ≤ n ∧ V I i S ≤ V I i (nbr n j) := by
    refine ⟨n, le_rfl, ?_⟩
    rw [hVe, hVe]
    exact Finset.sum_le_sum_of_subset_of_nonneg (fun k _ => by simp [nbr])
      (fun j _ _ => hv j)
  classical
  obtain ⟨hjn, hjV⟩ := Nat.find_spec hex
  have hjmin := fun k (hk : k < Nat.find hex) => Nat.find_min hex hk
  obtain ⟨j, hj⟩ : ∃ j, j = Nat.find hex := ⟨_, rfl⟩
  rw [← hj] at hjn hjV hjmin
  have hj1 : 1 ≤ j := by
    by_contra h
    have : j = 0 := by omega
    rw [this, hnb0, show V I i ∅ = 0 by simp [V, hfc]] at hjV
    linarith
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  have hmn : m < n := by omega
  have hlow : V I i (nbr n m) < V I i S := by
    have := hjmin m (by omega)
    push Not at this
    exact this (by omega)
  obtain ⟨hins, hnot⟩ := dg86_nbr_succ hmn
  set pm : Fin n := ⟨m, hmn⟩ with hpm
  have eN : ∑ j ∈ nbr n (m + 1), I.r i j * I.v i j =
      I.r i pm * I.v i pm + ∑ j ∈ nbr n m, I.r i j * I.v i j := by
    rw [hins, Finset.sum_insert hnot]
  have eV : V I i (nbr n (m + 1)) = I.v i pm + V I i (nbr n m) := by
    rw [hVe, hVe, hins, Finset.sum_insert hnot]
  -- exchange bound F1
  have hF1 : ∑ j ∈ S, I.r i j * I.v i j ≤
      ∑ j ∈ nbr n m, I.r i j * I.v i j + I.r i pm * (V I i S - V I i (nbr n m)) := by
    rw [hVe, hVe]
    apply dg86_exch (I.r i) (I.v i) S (nbr n m) (I.r i pm)
    · intro k hk _
      simp only [nbr, Finset.mem_filter, Finset.mem_univ, true_and] at hk
      exact mul_le_mul_of_nonneg_right (hanti (Fin.le_def.2 (by simp [hpm]; omega))) (hv k)
    · intro k _ hk
      simp only [nbr, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hk
      exact mul_le_mul_of_nonneg_right (hanti (Fin.le_def.2 (by simp [hpm]; omega))) (hv k)
  have hrpm := hr pm
  have hvpm := hv pm
  obtain ⟨hVj, hNj⟩ := dg86_pos I i hv hr hfc h0 hv1 hr1 (m := m + 1) (by omega)
  -- Case A
  have caseA : ∀ ρ, ∑ j ∈ S, I.r i j * I.v i j ≤ ρ * V I i S →
      ρ ≤ α * R I i (nbr n (m + 1)) → nestWeight I i S * (R I i S - α * z) ≤ α * y := by
    intro ρ h1 h2
    have hRS : R I i S ≤ ρ := by unfold R; rw [div_le_iff₀ hVS]; linarith
    have hw : 0 ≤ nestWeight I i S := Real.rpow_nonneg (hV0 S) _
    have k1 : nestWeight I i S * (R I i S - α * z) ≤
        nestWeight I i S * (α * (R I i (nbr n (m + 1)) - z)) :=
      mul_le_mul_of_nonneg_left (by nlinarith) hw
    rcases le_or_gt z (R I i (nbr n (m + 1))) with h3 | h3
    · have hWle : nestWeight I i S ≤ nestWeight I i (nbr n (m + 1)) :=
        Real.rpow_le_rpow (hV0 S) hjV (by linarith)
      have k2 : nestWeight I i S * (α * (R I i (nbr n (m + 1)) - z)) ≤
          nestWeight I i (nbr n (m + 1)) * (α * (R I i (nbr n (m + 1)) - z)) :=
        mul_le_mul_of_nonneg_right hWle (mul_nonneg (by linarith) (by linarith))
      have k3 := hy (m + 1) hjn
      nlinarith
    · have : nestWeight I i S * (α * (R I i (nbr n (m + 1)) - z)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hw (mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith))
      linarith
  have hRpos : 0 ≤ R I i (nbr n (m + 1)) := div_nonneg (hN0 _) (hV0 _)
  rcases Nat.eq_zero_or_pos m with hm0 | hm0
  · -- first segment
    subst hm0
    apply caseA (I.r i pm)
    · rw [hnb0] at hF1; simpa [show V I i ∅ = 0 by simp [V, hfc]] using hF1
    · have : R I i (nbr n (0 + 1)) = I.r i pm := by
        have hpv : I.v i pm ≠ 0 := hv1.ne'
        unfold R; rw [eN, eV, hnb0]; simp [show V I i ∅ = 0 by simp [V, hfc]]
        exact mul_div_cancel_right₀ _ hpv
      rw [this]; nlinarith
  · obtain ⟨hVm, hNm⟩ := dg86_pos I i hv hr hfc h0 hv1 hr1 (m := m) hm0
    have hterm := hαt (m + 1) (Finset.mem_Icc.2 ⟨by omega, hjn⟩)
    unfold alphaTerm at hterm
    simp only [Nat.add_sub_cancel] at hterm
    have hRm : 0 < R I i (nbr n m) := div_pos hNm hVm
    have hRj : 0 < R I i (nbr n (m + 1)) := div_pos hNj hVj
    have hWm : 0 < nestWeight I i (nbr n m) := Real.rpow_pos_of_pos hVm _
    have hWj : 0 < nestWeight I i (nbr n (m + 1)) := Real.rpow_pos_of_pos hVj _
    rcases min_le_iff.1 hterm with ha | hb
    · -- Case A with ρ = R_m
      apply caseA (R I i (nbr n m))
      · have hrN := dg86_rN I i hv hanti hfc hmn
        rw [← hpm] at hrN
        have : I.r i pm ≤ R I i (nbr n m) := by unfold R; rw [le_div_iff₀ hVm]; linarith
        have e : R I i (nbr n m) * V I i (nbr n m) = ∑ j ∈ nbr n m, I.r i j * I.v i j := by
          unfold R; field_simp
        nlinarith
      · rwa [div_le_iff₀ hRj] at ha
    · -- Case B
      have hb' : R I i (nbr n (m + 1)) * nestWeight I i (nbr n (m + 1)) ≤
          α * (R I i (nbr n m) * nestWeight I i (nbr n m)) := by
        rw [div_mul_div_comm, div_le_iff₀ (mul_pos hRm hWm)] at hb; linarith
      have eRW : ∀ T, 0 < V I i T → R I i T * nestWeight I i T =
          (∑ j ∈ T, I.r i j * I.v i j) * V I i T ^ (I.γ i - 1) := by
        intro T hT
        have := dg86_RW I i T hT 0
        simp only [sub_zero, zero_mul] at this
        rw [mul_comm]; exact this
      rw [dg86_RW I i S hVS]
      have hNS : ∑ j ∈ S, I.r i j * I.v i j ≤ ∑ j ∈ nbr n (m + 1), I.r i j * I.v i j := by
        rw [eN]
        have : I.r i pm * (V I i S - V I i (nbr n m)) ≤ I.r i pm * I.v i pm :=
          mul_le_mul_of_nonneg_left (by linarith) hrpm
        linarith
      have hp1 : V I i S ^ (I.γ i - 1) ≤ V I i (nbr n (m + 1)) ^ (I.γ i - 1) :=
        Real.rpow_le_rpow (hV0 S) hjV (by linarith)
      have k1 : (∑ j ∈ S, I.r i j * I.v i j) * V I i S ^ (I.γ i - 1) ≤
          (∑ j ∈ nbr n (m + 1), I.r i j * I.v i j) * V I i (nbr n (m + 1)) ^ (I.γ i - 1) :=
        mul_le_mul hNS hp1 (Real.rpow_nonneg (hV0 S) _) (hN0 _)
      rw [← eRW _ hVj] at k1
      have hWle : nestWeight I i (nbr n m) ≤ V I i S ^ I.γ i :=
        Real.rpow_le_rpow (hV0 _) hlow.le (by linarith)
      have k2 : α * z * nestWeight I i (nbr n m) ≤ α * z * V I i S ^ I.γ i :=
        mul_le_mul_of_nonneg_left hWle (mul_nonneg (by linarith) hz)
      have k3 := hy m hmn.le
      have k4 : α * (nestWeight I i (nbr n m) * (R I i (nbr n m) - z)) ≤ α * y :=
        mul_le_mul_of_nonneg_left k3 (by linarith)
      nlinarith

theorem dg86_alpha_ge {ι : Type*} {n : ℕ} (I : NestedLogitVariants.Synergistic.Instance ι n) (i : ι)
    (hv : ∀ j, 0 ≤ I.v i j) (hr : ∀ j, 0 ≤ I.r i j) (hanti : Antitone (I.r i))
    (hfc : I.vnp i = 0) (hγ1 : 1 < I.γ i) (hn : 2 ≤ n) (hv1 : 0 < I.v i ⟨0, by omega⟩)
    (hr1 : 0 < I.r i ⟨0, by omega⟩) : 1 ≤ alphaTerm I i 2 := by
  have h0 : 0 < n := by omega
  have hmn : 1 < n := by omega
  obtain ⟨hins, hnot⟩ := dg86_nbr_succ hmn
  have hVe : ∀ T, V I i T = ∑ j ∈ T, I.v i j := fun T => by simp [V, hfc]
  set p1 : Fin n := ⟨1, hmn⟩ with hp1
  have eN : ∑ j ∈ nbr n (1 + 1), I.r i j * I.v i j =
      I.r i p1 * I.v i p1 + ∑ j ∈ nbr n 1, I.r i j * I.v i j := by
    rw [hins, Finset.sum_insert hnot]
  have eV : V I i (nbr n (1 + 1)) = I.v i p1 + V I i (nbr n 1) := by
    rw [hVe, hVe, hins, Finset.sum_insert hnot]
  obtain ⟨hV1, hN1⟩ := dg86_pos I i hv hr hfc h0 hv1 hr1 (m := 1) le_rfl
  obtain ⟨hV2, hN2⟩ := dg86_pos I i hv hr hfc h0 hv1 hr1 (m := 2) (by norm_num)
  have hrN := dg86_rN I i hv hanti hfc hmn
  rw [← hp1] at hrN
  have hv1' := hv p1
  have hr1' := hr p1
  unfold alphaTerm
  simp only [show (2 : ℕ) - 1 = 1 from rfl]
  rw [show (2 : ℕ) = 1 + 1 from rfl]
  have hR1 : 0 < R I i (nbr n 1) := div_pos hN1 hV1
  have hR2 : 0 < R I i (nbr n (1 + 1)) := div_pos hN2 hV2
  apply le_min
  · rw [one_le_div hR2]
    unfold R
    rw [div_le_div_iff₀ hV2 hV1, eN, eV]
    nlinarith
  · have hW1 : 0 < nestWeight I i (nbr n 1) := Real.rpow_pos_of_pos hV1 _
    rw [div_mul_div_comm, one_le_div (mul_pos hR1 hW1)]
    have e : ∀ T, 0 < V I i T → R I i T * nestWeight I i T =
        (∑ j ∈ T, I.r i j * I.v i j) * V I i T ^ (I.γ i - 1) := by
      intro T hT
      have := dg86_RW I i T hT 0
      simp only [sub_zero, zero_mul] at this
      rw [mul_comm]; exact this
    rw [e _ hV1, e _ hV2]
    apply mul_le_mul
    · rw [eN]; linarith [mul_nonneg hr1' hv1']
    · exact Real.rpow_le_rpow hV1.le (by rw [eV]; linarith) (by linarith)
    · exact Real.rpow_nonneg hV1.le _
    · exact hN2.le

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (I : NestedLogitVariants.Synergistic.Instance ι n)
    (hv0 : 0 ≤ I.v0) (hv : ∀ i j, 0 ≤ I.v i j) (hrnn : ∀ i j, 0 ≤ I.r i j)
    (hγpos : ∀ i, 0 < I.γ i) (hanti : ∀ i, Antitone (I.r i))
    (hfc : ∀ i, I.vnp i = 0) (hsyn : ∃ i, 1 < I.γ i) (hn : 2 ≤ n)
    (hv1 : ∀ i, 0 < I.v i ⟨0, by omega⟩) (hr1 : ∀ i, 0 < I.r i ⟨0, by omega⟩)
    (α : ℝ) (hα : IsGreatest (alphaTerms I) α)
    (xh : ℝ) (yh : ι → ℝ) (hopt : LP4Optimal I (fun _ => {S | ∃ j ≤ n, S = nbr n j}) xh yh) :
    LP3Feasible I (α * xh) (α • yh) := by
  have hnb0 : nbr n 0 = ∅ := by ext k; simp [nbr]
  have hA : ∀ i : ι, (∅ : Finset (Fin n)) ∈ {S : Finset (Fin n) | ∃ j ≤ n, S = nbr n j} :=
    fun i => ⟨0, Nat.zero_le _, hnb0.symm⟩
  have hvnp : ∀ i, 0 ≤ I.vnp i := fun i => by rw [hfc i]
  have hx := dg86_x_nonneg I hv0 hvnp hv hrnn (fun _ => {S : Finset (Fin n) | ∃ j ≤ n, S = nbr n j}) hA xh yh hopt
  obtain ⟨⟨hf1, hf2⟩, _⟩ := hopt
  have h0 : 0 < n := by omega
  have hαge : 1 ≤ α := by
    obtain ⟨i0, hi0⟩ := hsyn
    have h1 := dg86_alpha_ge I i0 (hv i0) (hrnn i0) (hanti i0) (hfc i0) hi0 hn (hv1 i0) (hr1 i0)
    exact h1.trans (hα.2 ⟨i0, 2, Finset.mem_Icc.2 ⟨le_rfl, hn⟩, rfl⟩)
  have hy0 : ∀ i, 0 ≤ yh i := by
    intro i
    have := hf2 i ∅ (hA i)
    unfold nestWeight at this
    rwa [show V I i ∅ = 0 by simp [V, hfc], Real.zero_rpow (hγpos i).ne', zero_mul] at this
  refine ⟨?_, ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    calc α * ∑ i, yh i ≤ α * (I.v0 * xh) := mul_le_mul_of_nonneg_left hf1 (by linarith)
      _ = I.v0 * (α * xh) := by ring
  intro i S
  simp only [Pi.smul_apply, smul_eq_mul]
  have hyc : ∀ m ≤ n, nestWeight I i (nbr n m) * (R I i (nbr n m) - xh) ≤ yh i :=
    fun m hm => hf2 i (nbr n m) ⟨m, hm, rfl⟩
  rcases le_or_gt 1 (I.γ i) with hγ1 | hγ1
  · exact dg86_syn I i xh α (yh i) hx hαge
      (fun j hj => hα.2 ⟨i, j, hj, rfl⟩) (hv i) (hrnn i) (hanti i) (hfc i) hγ1 h0 (hv1 i) (hr1 i)
      hyc S
  · -- γ < 1: nested sets are optimal for the nest subproblem
    have hV0 : ∀ T, 0 ≤ V I i T := fun T => by
      simp only [V, hfc, zero_add]; exact Finset.sum_nonneg fun j _ => hv i j
    obtain ⟨S0, -, hS0⟩ := Finset.exists_max_image (Finset.univ : Finset (Finset (Fin n)))
      (fun T => nestWeight I i T * (R I i T - α * xh)) Finset.univ_nonempty
    have hmax : ∀ T, nestWeight I i T * (R I i T - α * xh) ≤
        nestWeight I i S0 * (R I i S0 - α * xh) := fun T => hS0 T (Finset.mem_univ _)
    have hαy : 0 ≤ α * yh i := mul_nonneg (by linarith) (hy0 i)
    rcases (hV0 S0).lt_or_eq with hu | hu
    · obtain ⟨m, hm, hg, -⟩ := dg86_nest I i (α * xh) (hv i) (hγpos i) hγ1.le (hfc i) (hanti i)
        S0 hmax hu
      have hw := Real.rpow_nonneg (hV0 (nbr n m)) (I.γ i)
      have hRn : 0 ≤ R I i (nbr n m) :=
        div_nonneg (Finset.sum_nonneg fun j _ => mul_nonneg (hrnn i j) (hv i j)) (hV0 _)
      have k1 : nestWeight I i (nbr n m) * (R I i (nbr n m) - α * xh) ≤
          α * (nestWeight I i (nbr n m) * (R I i (nbr n m) - xh)) := by
        unfold nestWeight at hw ⊢
        have := mul_nonneg hw hRn
        nlinarith
      have k2 := mul_le_mul_of_nonneg_left (hyc m hm) (by linarith : (0 : ℝ) ≤ α)
      linarith [hmax S]
    · have : nestWeight I i S0 * (R I i S0 - α * xh) = 0 := by
        unfold nestWeight; rw [← hu, Real.zero_rpow (hγpos i).ne', zero_mul]
      linarith [hmax S]
