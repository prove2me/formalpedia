-- Prove2me | solution 1 for DavisGallegoTopaloglu2014.theorem_4_faithful
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T04:19:42.764466+00:00
-- url     : https://prove2.me/submissions/55bf322a-1e2d-44c9-993d-7d0de3829e39

import Mathlib
import Definitions.Def_NestedLogitVariants_Competitive_Model

open NestedLogitVariants.Competitive

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

theorem dg86_nest {ι : Type*} {n : ℕ} (I : NestedLogitVariants.Competitive.Instance ι n) (i : ι)
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

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (I : NestedLogitVariants.Competitive.Instance ι n)
    (hv0 : 0 ≤ I.v0) (hv : ∀ i j, 0 ≤ I.v i j) (hr : ∀ i j, 0 ≤ I.r i j)
    (hγpos : ∀ i, 0 < I.γ i) (hanti : ∀ i, Antitone (I.r i))
    (hγ : ∀ i, I.γ i ≤ 1) (hfc : ∀ i, I.vnp i = 0) :
    ∃ S : ι → Finset (Fin n), IsOptimal I S ∧ ∀ i, ∃ j ≤ n, S i = nbr n j := by
  have hV : ∀ i S, 0 ≤ V I i S := fun i S => by
    simp only [V, hfc, zero_add]; exact Finset.sum_nonneg fun j _ => hv i j
  have hnw : ∀ i S, 0 ≤ nestWeight I i S := fun i S => Real.rpow_nonneg (hV i S) _
  have hR : ∀ i S, 0 ≤ R I i S := fun i S =>
    div_nonneg (Finset.sum_nonneg fun j _ => mul_nonneg (hr i j) (hv i j)) (hV i S)
  have hD0 : ∀ S : ι → Finset (Fin n), 0 ≤ I.v0 + ∑ i, nestWeight I i (S i) := fun S =>
    add_nonneg hv0 (Finset.sum_nonneg fun i _ => hnw i (S i))
  have hrev0 : ∀ S, 0 ≤ revenue I S := fun S =>
    div_nonneg (Finset.sum_nonneg fun i _ => mul_nonneg (hnw i _) (hR i _)) (hD0 S)
  have hsplit : ∀ (S : ι → Finset (Fin n)) (z : ℝ), ∑ i, nestWeight I i (S i) * (R I i (S i) - z) =
      ∑ i, nestWeight I i (S i) * R I i (S i) - z * ∑ i, nestWeight I i (S i) := by
    intro S z
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro i _; ring
  obtain ⟨Ss, -, hSs⟩ := Finset.exists_max_image (Finset.univ : Finset (ι → Finset (Fin n)))
    (revenue I) Finset.univ_nonempty
  have hSopt : ∀ S', revenue I S' ≤ revenue I Ss := fun S' => hSs S' (Finset.mem_univ _)
  obtain ⟨z, hz⟩ : ∃ z, z = revenue I Ss := ⟨_, rfl⟩
  rcases (hz ▸ hrev0 Ss : 0 ≤ z).lt_or_eq with hzpos | hz0
  swap
  · refine ⟨fun _ => nbr n 0, fun S' => ?_, fun i => ⟨0, Nat.zero_le _, rfl⟩⟩
    have := hSopt S'
    rw [← hz, ← hz0] at this
    exact this.trans (hrev0 _)
  -- z > 0
  have hDpos : 0 < I.v0 + ∑ i, nestWeight I i (Ss i) := by
    rcases (hD0 Ss).lt_or_eq with h | h
    · exact h
    · exfalso; rw [hz, revenue, ← h, div_zero] at hzpos; exact lt_irrefl _ hzpos
  have hident : ∑ i, nestWeight I i (Ss i) * (R I i (Ss i) - z) = I.v0 * z := by
    rw [hsplit]
    have : ∑ i, nestWeight I i (Ss i) * R I i (Ss i) = z * (I.v0 + ∑ i, nestWeight I i (Ss i)) := by
      rw [hz, revenue, div_mul_cancel₀ _ hDpos.ne']
    rw [this]; ring
  -- each nest of Ss maximizes g_i
  have hmax : ∀ i S, nestWeight I i S * (R I i S - z) ≤
      nestWeight I i (Ss i) * (R I i (Ss i) - z) := by
    intro i S
    by_contra hlt
    push Not at hlt
    set S2 := Function.update Ss i S with hS2
    have hsum : ∑ k, nestWeight I k (S2 k) * (R I k (S2 k) - z) =
        ∑ k, nestWeight I k (Ss k) * (R I k (Ss k) - z) +
          (nestWeight I i S * (R I i S - z) - nestWeight I i (Ss i) * (R I i (Ss i) - z)) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
        ← Finset.add_sum_erase _ (fun k => nestWeight I k (Ss k) * (R I k (Ss k) - z))
          (Finset.mem_univ i)]
      have : ∑ k ∈ Finset.univ.erase i, nestWeight I k (S2 k) * (R I k (S2 k) - z) =
          ∑ k ∈ Finset.univ.erase i, nestWeight I k (Ss k) * (R I k (Ss k) - z) := by
        apply Finset.sum_congr rfl; intro k hk
        rw [hS2, Function.update_of_ne (Finset.ne_of_mem_erase hk)]
      rw [this, hS2, Function.update_self]; ring
    have hgt : I.v0 * z < ∑ k, nestWeight I k (S2 k) * (R I k (S2 k) - z) := by
      rw [hsum, hident]; linarith
    have hD2 : 0 < I.v0 + ∑ k, nestWeight I k (S2 k) := by
      rcases (hD0 S2).lt_or_eq with h | h
      · exact h
      · exfalso
        have hv00 : I.v0 = 0 := by linarith [Finset.sum_nonneg fun k (_ : k ∈ Finset.univ) => hnw k (S2 k)]
        have hall : ∀ k, nestWeight I k (S2 k) = 0 := fun k =>
          (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hnw k (S2 k))).1 (by linarith) k
            (Finset.mem_univ k)
        simp [hall, hv00] at hgt
    have : z < revenue I S2 := by
      unfold revenue
      rw [lt_div_iff₀ hD2]
      rw [hsplit] at hgt; nlinarith
    have := hSopt S2
    linarith
  -- choose nested sets
  have hch : ∀ i, ∃ m ≤ n, nestWeight I i (Ss i) * (R I i (Ss i) - z) ≤
      nestWeight I i (nbr n m) * (R I i (nbr n m) - z) ∧
      (0 < V I i (Ss i) → 0 < V I i (nbr n m)) := by
    intro i
    rcases (hV i (Ss i)).lt_or_eq with h | h
    · obtain ⟨m, hm, h1, h2⟩ := dg86_nest I i z (hv i) (hγpos i) (hγ i) (hfc i) (hanti i) (Ss i)
        (hmax i) h
      exact ⟨m, hm, h1, fun _ => h2⟩
    · refine ⟨0, Nat.zero_le _, ?_, fun h' => absurd h (ne_of_lt h')⟩
      have hnb : nbr n 0 = ∅ := by ext k; simp [nbr]
      have hE : V I i ∅ = 0 := by simp [V, hfc]
      unfold nestWeight
      rw [← h, hnb, hE, Real.zero_rpow (hγpos i).ne']; simp
  choose m hm hg hpos using hch
  refine ⟨fun i => nbr n (m i), ?_, fun i => ⟨m i, hm i, rfl⟩⟩
  intro S'
  have hT : I.v0 * z ≤ ∑ i, nestWeight I i (nbr n (m i)) * (R I i (nbr n (m i)) - z) := by
    rw [← hident]; exact Finset.sum_le_sum fun i _ => hg i
  have hDT : 0 < I.v0 + ∑ i, nestWeight I i (nbr n (m i)) := by
    rcases hv0.lt_or_eq with h | h
    · exact add_pos_of_pos_of_nonneg h (Finset.sum_nonneg fun i _ => hnw i _)
    · rw [← h, zero_add] at hDpos ⊢
      obtain ⟨i, -, hi⟩ := Finset.exists_lt_of_sum_lt (s := Finset.univ)
        (f := fun _ => (0 : ℝ)) (by simpa using hDpos)
      have hVi : 0 < V I i (Ss i) := by
        rcases (hV i (Ss i)).lt_or_eq with h' | h'
        · exact h'
        · exfalso; unfold nestWeight at hi; rw [← h', Real.zero_rpow (hγpos i).ne'] at hi
          exact lt_irrefl _ hi
      have := Real.rpow_pos_of_pos (hpos i hVi) (I.γ i)
      exact lt_of_lt_of_le this (Finset.single_le_sum (f := fun i => nestWeight I i (nbr n (m i)))
        (fun i _ => hnw i _) (Finset.mem_univ i))
  have hzT : z ≤ revenue I (fun i => nbr n (m i)) := by
    unfold revenue
    rw [le_div_iff₀ hDT]
    rw [hsplit] at hT; nlinarith
  have := hSopt S'
  linarith
