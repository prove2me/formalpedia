-- Prove2me | solution 1 for FuzzyGames.NTUCore.piV_closed_convex
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T19:50:39.034046+00:00
-- url     : https://prove2.me/submissions/40eaa13e-85a6-412a-93e6-ef019be0e29b

import Mathlib
import Definitions.Def_FuzzyGames_NTUCore_Basic

open Set Finset Pointwise

namespace FuzzyGames.NTUCore.Aux
open FuzzyGames.NTUCore

theorem mem_piV {n : ℕ} (𝒞 : CoalFamily n) (V : Finset (Fin n) → Set (Fin n → ℝ))
    (τ x : Fin n → ℝ) :
    x ∈ piV 𝒞 V τ ↔ ∃ m ∈ balances 𝒞 τ, ∃ w : Finset (Fin n) → Fin n → ℝ,
      (∀ A ∈ 𝒞.C, w A ∈ V A) ∧ ∑ A ∈ 𝒞.C, m A • w A = x := by
  classical
  unfold piV
  simp only [Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨m, hm, hx⟩
    rw [Set.mem_finsetSum] at hx
    obtain ⟨g, hg, rfl⟩ := hx
    have : ∀ A ∈ 𝒞.C, ∃ w ∈ V A, m A • w = g A := fun A hA => by
      simpa [Set.mem_smul_set] using hg hA
    choose! w hw hw' using this
    exact ⟨m, hm, w, hw, Finset.sum_congr rfl (fun A hA => hw' A hA)⟩
  · rintro ⟨m, hm, w, hw, rfl⟩
    exact ⟨m, hm, Set.finsetSum_mem_finsetSum _ _ _ (fun A hA =>
      Set.smul_mem_smul_set (hw A hA))⟩


theorem bal_smul {n : ℕ} (𝒞 : CoalFamily n) {τ : Fin n → ℝ} {m : Finset (Fin n) → ℝ}
    (hm : m ∈ balances 𝒞 τ) {s : ℝ} (hs : 0 ≤ s) : s • m ∈ balances 𝒞 (s • τ) := by
  obtain ⟨h0, h1, h2⟩ := hm
  refine ⟨fun A => by simpa using mul_nonneg hs (h0 A), fun A hA => by simp [h1 A hA], fun i => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, h2 i]

theorem bal_add {n : ℕ} (𝒞 : CoalFamily n) {τ σ : Fin n → ℝ} {m m' : Finset (Fin n) → ℝ}
    (hm : m ∈ balances 𝒞 τ) (hm' : m' ∈ balances 𝒞 σ) : m + m' ∈ balances 𝒞 (τ + σ) := by
  obtain ⟨h0, h1, h2⟩ := hm
  obtain ⟨h0', h1', h2'⟩ := hm'
  refine ⟨fun A => by simpa using add_nonneg (h0 A) (h0' A),
    fun A hA => by simp [h1 A hA, h1' A hA], fun i => ?_⟩
  simp only [Pi.add_apply, Finset.sum_add_distrib, h2 i, h2' i]


theorem piV_hom {n : ℕ} (𝒞 : CoalFamily n) {V : Finset (Fin n) → Set (Fin n → ℝ)}
    (t : ℝ) (ht : 0 < t) (τ : Fin n → ℝ) : piV 𝒞 V (t • τ) = t • piV 𝒞 V τ := by
  classical
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ ht.ne', mem_piV, mem_piV]
  constructor
  · rintro ⟨m, hm, w, hw, rfl⟩
    refine ⟨t⁻¹ • m, ?_, w, hw, ?_⟩
    · have := bal_smul 𝒞 hm (inv_nonneg.2 ht.le)
      rwa [smul_smul, inv_mul_cancel₀ ht.ne', one_smul] at this
    · rw [Finset.smul_sum]
      apply Finset.sum_congr rfl; intro A _
      simp [smul_smul]
  · rintro ⟨m, hm, w, hw, hx⟩
    refine ⟨t • m, bal_smul 𝒞 hm ht.le, w, hw, ?_⟩
    have : x = t • (t⁻¹ • x) := by rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
    rw [this, ← hx, Finset.smul_sum]
    apply Finset.sum_congr rfl; intro A _
    simp [smul_smul]

theorem piV_sup {n : ℕ} (𝒞 : CoalFamily n) {V : Finset (Fin n) → Set (Fin n → ℝ)}
    (hV : IsNTUGame 𝒞 V) (τ σ : Fin n → ℝ) :
    piV 𝒞 V τ + piV 𝒞 V σ ⊆ piV 𝒞 V (τ + σ) := by
  classical
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_add.1 hz
  simp only [piV, Set.mem_iUnion, exists_prop] at hx hy ⊢
  obtain ⟨m, hm, hx⟩ := hx
  obtain ⟨m', hm', hy⟩ := hy
  refine ⟨m + m', bal_add 𝒞 hm hm', ?_⟩
  have hset : ∑ A ∈ 𝒞.C, m A • V A + ∑ A ∈ 𝒞.C, m' A • V A =
      ∑ A ∈ 𝒞.C, (m + m') A • V A := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro A hA
    rw [Pi.add_apply, (hV.convex A hA).add_smul (hm.1 A) (hm'.1 A)]
  rw [← hset]
  exact Set.add_mem_add hx hy

theorem bal_zero_of {n : ℕ} (𝒞 : CoalFamily n) {τ : Fin n → ℝ} {m : Finset (Fin n) → ℝ}
    (hm : m ∈ balances 𝒞 τ) {A : Finset (Fin n)} (hA : A ∈ 𝒞.C) {i : Fin n} (hi : i ∈ A)
    (hτ : τ i = 0) : m A = 0 := by
  have h := hm.2.2 i
  rw [hτ, Finset.sum_eq_zero_iff_of_nonneg (fun B _ => hm.1 B)] at h
  exact h A (Finset.mem_filter.2 ⟨hA, hi⟩)

theorem bal_le {n : ℕ} (𝒞 : CoalFamily n) {τ : Fin n → ℝ} {m : Finset (Fin n) → ℝ}
    (hm : m ∈ balances 𝒞 τ) {A : Finset (Fin n)} (hA : A ∈ 𝒞.C) {i : Fin n} (hi : i ∈ A) :
    m A ≤ τ i := by
  rw [← hm.2.2 i]
  exact Finset.single_le_sum (f := m) (fun B _ => hm.1 B) (Finset.mem_filter.2 ⟨hA, hi⟩)

theorem piV_subset_Rtau {n : ℕ} (𝒞 : CoalFamily n) {V : Finset (Fin n) → Set (Fin n → ℝ)}
    (hV : IsNTUGame 𝒞 V) (τ : Fin n → ℝ) : piV 𝒞 V τ ⊆ Rtau τ := by
  classical
  intro x hx i hτ
  obtain ⟨m, hm, w, hw, rfl⟩ := (mem_piV 𝒞 V τ x).1 hx
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro A hA
  by_cases hi : i ∈ A
  · rw [bal_zero_of 𝒞 hm hA hi hτ, zero_mul]
  · rw [hV.subset_Rtau A hA (hw A hA) i (by simp [coal, hi]), mul_zero]

theorem piV_comp {n : ℕ} (𝒞 : CoalFamily n) {V : Finset (Fin n) → Set (Fin n → ℝ)}
    (hV : IsNTUGame 𝒞 V) (τ : Fin n → ℝ) (hτ0 : τ ∈ orthant n) :
    piV 𝒞 V τ - RtauNonneg τ = piV 𝒞 V τ := by
  classical
  apply Set.Subset.antisymm
  · intro z hz
    obtain ⟨x, hx, p, hp, rfl⟩ := Set.mem_sub.1 hz
    obtain ⟨m, hm, w, hw, rfl⟩ := (mem_piV 𝒞 V τ x).1 hx
    rw [mem_piV]
    let r : Finset (Fin n) → Fin n → ℝ := fun A i => if i ∈ A then p i / τ i else 0
    refine ⟨m, hm, fun A => w A - r A, fun A hA => ?_, ?_⟩
    · rw [← hV.comprehensive A hA]
      refine Set.sub_mem_sub (hw A hA) ⟨fun i hi => ?_, fun i => ?_⟩
      · have : i ∉ A := by intro h; simp [coal, h] at hi
        simp [r, this]
      · simp only [r]; split_ifs
        · exact div_nonneg (hp.2 i) (hτ0 i)
        · exact le_rfl
    · ext i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, mul_sub,
        Finset.sum_sub_distrib]
      congr 1
      have : ∑ A ∈ 𝒞.C, m A * r A i = (p i / τ i) * ∑ A ∈ 𝒞.C.filter (fun A => i ∈ A), m A := by
        rw [Finset.mul_sum, Finset.sum_filter]
        apply Finset.sum_congr rfl; intro A _
        simp only [r]; split_ifs <;> ring
      rw [this, hm.2.2 i]
      by_cases hτ : τ i = 0
      · rw [hp.1 i hτ, hτ]; simp
      · field_simp
  · intro x hx
    exact ⟨x, hx, 0, ⟨fun i _ => rfl, fun i => le_rfl⟩, sub_zero x⟩


theorem piV_nonempty {n : ℕ} (𝒞 : CoalFamily n) {V : Finset (Fin n) → Set (Fin n → ℝ)}
    (hV : IsNTUGame 𝒞 V) (τ : Fin n → ℝ) (hτ0 : τ ∈ orthant n) : (piV 𝒞 V τ).Nonempty := by
  classical
  let m : Finset (Fin n) → ℝ := fun A => ∑ j, if A = {j} then τ j else 0
  have hm : m ∈ balances 𝒞 τ := by
    refine ⟨fun A => Finset.sum_nonneg fun j _ => ?_, fun A hA => ?_, fun i => ?_⟩
    · split_ifs
      · exact hτ0 j
      · exact le_rfl
    · apply Finset.sum_eq_zero; intro j _
      rw [if_neg]; rintro rfl; exact hA (𝒞.singleton_mem j)
    · simp only [m]
      rw [Finset.sum_comm]
      have : ∀ j : Fin n, (∑ A ∈ 𝒞.C.filter (fun A => i ∈ A), if A = {j} then τ j else 0)
          = if i = j then τ j else 0 := by
        intro j
        rw [Finset.sum_ite_eq']
        simp [Finset.mem_filter, 𝒞.singleton_mem j]
      rw [Finset.sum_congr rfl (fun j _ => this j)]
      simp
  let w : Finset (Fin n) → Fin n → ℝ := fun A =>
    if h : A ∈ 𝒞.C then (hV.nonempty A h).some else 0
  refine ⟨∑ A ∈ 𝒞.C, m A • w A, (mem_piV 𝒞 V τ _).2 ⟨m, hm, w, fun A hA => ?_, rfl⟩⟩
  simp only [w, dif_pos hA]
  exact (hV.nonempty A hA).some_mem

/-- a uniform coordinatewise bound for the sets `V A` -/
theorem exists_K {n : ℕ} (𝒞 : CoalFamily n) {V : Finset (Fin n) → Set (Fin n → ℝ)}
    (hV : IsNTUGame 𝒞 V) : ∃ K : Fin n → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ A ∈ 𝒞.C, ∀ w ∈ V A, ∀ i, ∀ t : ℝ, 0 ≤ t → t * w i ≤ t * K i := by
  classical
  have : ∀ A ∈ 𝒞.C, ∃ C ∈ Rtau (coal A), V A ⊆ {C} - RtauNonneg (coal A) := hV.bddAbove
  choose! Cv hCv hsub using this
  refine ⟨fun i => ∑ A ∈ 𝒞.C, |Cv A i|, fun i => Finset.sum_nonneg fun _ _ => abs_nonneg _, ?_⟩
  intro A hA w hw i t ht
  apply mul_le_mul_of_nonneg_left _ ht
  obtain ⟨c, hc, p, hp, hcp⟩ := Set.mem_sub.1 (hsub A hA hw)
  rw [Set.mem_singleton_iff] at hc
  subst hc
  have h1 : w i ≤ Cv A i := by rw [← hcp]; simp only [Pi.sub_apply]; linarith [hp.2 i]
  exact h1.trans ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun B => |Cv B i|) (fun _ _ => abs_nonneg _) hA))

theorem piV_bdd {n : ℕ} (𝒞 : CoalFamily n) {V : Finset (Fin n) → Set (Fin n → ℝ)}
    (hV : IsNTUGame 𝒞 V) (τ : Fin n → ℝ) :
    ∃ C ∈ Rtau τ, piV 𝒞 V τ ⊆ {C} - RtauNonneg τ := by
  classical
  obtain ⟨K, hK0, hK⟩ := exists_K 𝒞 hV
  refine ⟨fun i => τ i * K i, fun i hi => by simp [hi], fun x hx => ?_⟩
  refine ⟨fun i => τ i * K i, rfl, fun i => τ i * K i - x i, ⟨fun i hi => ?_, fun i => ?_⟩, ?_⟩
  · simp [hi, piV_subset_Rtau 𝒞 hV τ hx i hi]
  · obtain ⟨m, hm, w, hw, rfl⟩ := (mem_piV 𝒞 V τ x).1 hx
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sub_nonneg]
    rw [← hm.2.2 i, Finset.sum_mul, Finset.sum_filter]
    apply Finset.sum_le_sum; intro A hA
    split_ifs with hi
    · exact hK A hA (w A) (hw A hA) i (m A) (hm.1 A)
    · rw [hV.subset_Rtau A hA (hw A hA) i (by simp [coal, hi]), mul_zero]
  · ext i; simp

theorem piV_convex {n : ℕ} (𝒞 : CoalFamily n) {V : Finset (Fin n) → Set (Fin n → ℝ)}
    (hV : IsNTUGame 𝒞 V) (τ : Fin n → ℝ) : Convex ℝ (piV 𝒞 V τ) := by
  intro x hx y hy a b ha hb hab
  rcases ha.lt_or_eq with ha | ha
  · rcases hb.lt_or_eq with hb | hb
    · have h1 : a • x ∈ piV 𝒞 V (a • τ) := by
        rw [piV_hom 𝒞 a ha]; exact Set.smul_mem_smul_set hx
      have h2 : b • y ∈ piV 𝒞 V (b • τ) := by
        rw [piV_hom 𝒞 b hb]; exact Set.smul_mem_smul_set hy
      have := piV_sup 𝒞 hV (a • τ) (b • τ) (Set.add_mem_add h1 h2)
      rwa [← add_smul, hab, one_smul] at this
    · subst hb; rw [add_zero] at hab; subst hab; simpa using hx
  · subst ha; rw [zero_add] at hab; subst hab; simpa using hy


open Filter Topology in
theorem piV_closed {n : ℕ} (𝒞 : CoalFamily n) {V : Finset (Fin n) → Set (Fin n → ℝ)}
    (hV : IsNTUGame 𝒞 V) (τ : Fin n → ℝ) (hτ0 : τ ∈ orthant n) : IsClosed (piV 𝒞 V τ) := by
  classical
  obtain ⟨K, hK0, hK⟩ := exists_K 𝒞 hV
  apply isClosed_of_closure_subset
  intro x hx
  rw [mem_closure_iff_seq_limit] at hx
  obtain ⟨xs, hxs, hlim⟩ := hx
  have hrep : ∀ k, ∃ m ∈ balances 𝒞 τ, ∃ w : Finset (Fin n) → Fin n → ℝ,
      (∀ A ∈ 𝒞.C, w A ∈ V A) ∧ ∑ A ∈ 𝒞.C, m A • w A = xs k :=
    fun k => (mem_piV 𝒞 V τ _).1 (hxs k)
  choose ms hms ws hws hsum using hrep
  set ys : ℕ → Finset (Fin n) → Fin n → ℝ := fun k A => ms k A • ws k A with hys_def
  have hys : ∀ k A i, ys k A i = ms k A * ws k A i := fun k A i => rfl
  obtain ⟨X, hX⟩ : ∃ X, ∀ k i, |xs k i| ≤ X := by
    obtain ⟨X, hX⟩ := isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto xs hlim)
    exact ⟨X, fun k i => by
      rw [← Real.norm_eq_abs]; exact (norm_le_pi_norm (xs k) i).trans (hX _ ⟨k, rfl⟩)⟩
  set T : ℝ := ∑ i, τ i with hT_def
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun i _ => hτ0 i
  have hT : ∀ k A, 0 ≤ ms k A ∧ ms k A ≤ T := by
    intro k A
    refine ⟨(hms k).1 A, ?_⟩
    by_cases hA : A ∈ 𝒞.C
    · have hAne : A.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]; rintro rfl; exact 𝒞.empty_not_mem hA
      obtain ⟨i, hi⟩ := hAne
      exact (bal_le 𝒞 (hms k) hA hi).trans
        (Finset.single_le_sum (f := τ) (fun j _ => hτ0 j) (Finset.mem_univ i))
    · rw [(hms k).2.1 A hA]; exact hT0
  have hy0 : ∀ k A, A ∉ 𝒞.C → ys k A = 0 := by
    intro k A hA; ext i; rw [hys, (hms k).2.1 A hA, zero_mul]; rfl
  have hyU : ∀ k A i, ys k A i ≤ ms k A * K i := by
    intro k A i
    by_cases hA : A ∈ 𝒞.C
    · rw [hys]; exact hK A hA (ws k A) (hws k A hA) i (ms k A) (hT k A).1
    · rw [hy0 k A hA, (hms k).2.1 A hA, zero_mul]; rfl
  set U : Fin n → ℝ := fun i => T * K i with hU_def
  have hU0 : ∀ i, 0 ≤ U i := fun i => mul_nonneg hT0 (hK0 i)
  have hyU' : ∀ k A i, ys k A i ≤ U i := fun k A i =>
    (hyU k A i).trans (mul_le_mul_of_nonneg_right (hT k A).2 (hK0 i))
  set L : Fin n → ℝ := fun i => -X - (𝒞.C.card : ℝ) * U i with hL_def
  have hsumi : ∀ k i, ∑ A ∈ 𝒞.C, ys k A i = xs k i := by
    intro k i
    rw [← hsum k]; simp [ys, Finset.sum_apply]
  have hyL : ∀ k A i, L i ≤ ys k A i := by
    intro k A i
    have hX0 : 0 ≤ X := (abs_nonneg _).trans (hX k i)
    have hxl : -X ≤ xs k i := by have := hX k i; rw [abs_le] at this; exact this.1
    by_cases hA : A ∈ 𝒞.C
    · have h1 := Finset.add_sum_erase 𝒞.C (fun B => ys k B i) hA
      rw [hsumi k i] at h1
      have h2 : ∑ B ∈ 𝒞.C.erase A, ys k B i ≤ (𝒞.C.card : ℝ) * U i := by
        calc ∑ B ∈ 𝒞.C.erase A, ys k B i ≤ ∑ B ∈ 𝒞.C.erase A, U i :=
              Finset.sum_le_sum fun B _ => hyU' k B i
          _ = ((𝒞.C.erase A).card : ℝ) * U i := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (𝒞.C.card : ℝ) * U i := by
              apply mul_le_mul_of_nonneg_right _ (hU0 i)
              exact_mod_cast Finset.card_le_card (Finset.erase_subset A 𝒞.C)
      simp only [L]; linarith
    · rw [hy0 k A hA]
      simp only [L, Pi.zero_apply]
      nlinarith [hU0 i, (Nat.cast_nonneg 𝒞.C.card : (0:ℝ) ≤ 𝒞.C.card)]
  set S : Set ((Finset (Fin n) → ℝ) × (Finset (Fin n) → Fin n → ℝ)) :=
    (Set.pi Set.univ fun _ => Set.Icc 0 T) ×ˢ
      (Set.pi Set.univ fun _ => Set.pi Set.univ fun i => Set.Icc (L i) (U i)) with hS_def
  have hS : IsCompact S :=
    (isCompact_univ_pi fun _ => isCompact_Icc).prod
      (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc)
  obtain ⟨⟨m, y⟩, -, φ, hφ, hconv⟩ := hS.tendsto_subseq (x := fun k => (ms k, ys k))
    (fun k => ⟨fun A _ => hT k A, fun A _ i _ => ⟨hyL k A i, hyU' k A i⟩⟩)
  have hm_t : Tendsto (fun k => ms (φ k)) atTop (𝓝 m) := hconv.fst_nhds
  have hy_t : Tendsto (fun k => ys (φ k)) atTop (𝓝 y) := hconv.snd_nhds
  have hmA : ∀ A, Tendsto (fun k => ms (φ k) A) atTop (𝓝 (m A)) := fun A =>
    ((continuous_apply A).tendsto m).comp hm_t
  have hyA' : ∀ A, Tendsto (fun k => ys (φ k) A) atTop (𝓝 (y A)) := fun A =>
    ((continuous_apply A).tendsto y).comp hy_t
  have hyA : ∀ A i, Tendsto (fun k => ys (φ k) A i) atTop (𝓝 (y A i)) := fun A i =>
    ((continuous_apply i).tendsto (y A)).comp (hyA' A)
  have hm : m ∈ balances 𝒞 τ := by
    refine ⟨fun A => ge_of_tendsto' (hmA A) (fun k => (hms _).1 A), fun A hA => ?_, fun i => ?_⟩
    · have h1 := hmA A
      have : (fun k => ms (φ k) A) = fun _ => 0 := funext fun k => (hms _).2.1 A hA
      rw [this] at h1
      exact tendsto_nhds_unique h1 tendsto_const_nhds
    · have h1 : Tendsto (fun k => ∑ A ∈ 𝒞.C.filter (fun A => i ∈ A), ms (φ k) A) atTop
          (𝓝 (∑ A ∈ 𝒞.C.filter (fun A => i ∈ A), m A)) :=
        tendsto_finsetSum _ fun A _ => hmA A
      have : (fun k => ∑ A ∈ 𝒞.C.filter (fun A => i ∈ A), ms (φ k) A) = fun _ => τ i :=
        funext fun k => (hms _).2.2 i
      rw [this] at h1
      exact tendsto_nhds_unique h1 tendsto_const_nhds
  have hxy : ∑ A ∈ 𝒞.C, y A = x := by
    ext i
    have h1 : Tendsto (fun k => ∑ A ∈ 𝒞.C, ys (φ k) A i) atTop (𝓝 (∑ A ∈ 𝒞.C, y A i)) :=
      tendsto_finsetSum _ fun A _ => hyA A i
    have h2 : Tendsto (fun k => xs (φ k) i) atTop (𝓝 (x i)) :=
      ((continuous_apply i).tendsto x).comp (hlim.comp hφ.tendsto_atTop)
    have : (fun k => ∑ A ∈ 𝒞.C, ys (φ k) A i) = fun k => xs (φ k) i :=
      funext fun k => hsumi (φ k) i
    rw [this] at h1
    rw [Finset.sum_apply]
    exact tendsto_nhds_unique h1 h2
  set v : Finset (Fin n) → Fin n → ℝ := fun A =>
    if h : A ∈ 𝒞.C then (hV.nonempty A h).some else 0 with hv_def
  set w : Finset (Fin n) → Fin n → ℝ := fun A =>
    if 0 < m A then (m A)⁻¹ • y A else v A with hw_def
  have hw : ∀ A ∈ 𝒞.C, w A ∈ V A := by
    intro A hA
    by_cases hpos : 0 < m A
    · simp only [w, if_pos hpos]
      have ht : Tendsto (fun k => (ms (φ k) A)⁻¹ • ys (φ k) A) atTop (𝓝 ((m A)⁻¹ • y A)) :=
        ((hmA A).inv₀ hpos.ne').smul (hyA' A)
      apply (hV.isClosed A hA).mem_of_tendsto ht
      filter_upwards [(hmA A).eventually (lt_mem_nhds hpos)] with k hk
      have : (ms (φ k) A)⁻¹ • ys (φ k) A = ws (φ k) A := by
        simp only [ys, smul_smul, inv_mul_cancel₀ hk.ne', one_smul]
      rw [this]; exact hws _ A hA
    · simp only [w, if_neg hpos, v, dif_pos hA]
      exact (hV.nonempty A hA).some_mem
  set p : Fin n → ℝ := ∑ A ∈ 𝒞.C, (if 0 < m A then 0 else -y A) with hp_def
  have hp : p ∈ RtauNonneg τ := by
    refine ⟨fun i hi => ?_, fun i => ?_⟩
    · simp only [p, Finset.sum_apply]
      apply Finset.sum_eq_zero; intro A hA
      split_ifs
      · rfl
      · have hz : ∀ k, ys (φ k) A i = 0 := by
          intro k
          rw [hys]
          by_cases hiA : i ∈ A
          · rw [bal_zero_of 𝒞 (hms _) hA hiA hi, zero_mul]
          · rw [hV.subset_Rtau A hA (hws _ A hA) i (by simp [coal, hiA]), mul_zero]
        have : (fun k => ys (φ k) A i) = fun _ => 0 := funext hz
        have h1 := hyA A i
        rw [this] at h1
        simp [tendsto_nhds_unique h1 tendsto_const_nhds]
    · simp only [p, Finset.sum_apply]
      apply Finset.sum_nonneg; intro A _
      split_ifs with hpos
      · exact le_rfl
      · have hm0 : m A = 0 := le_antisymm (not_lt.1 hpos) (hm.1 A)
        have h1 : y A i ≤ m A * K i :=
          le_of_tendsto_of_tendsto' (hyA A i) ((hmA A).mul_const (K i))
            (fun k => hyU _ A i)
        rw [hm0, zero_mul] at h1
        simp only [Pi.neg_apply]; linarith
  have hx_eq : x = ∑ A ∈ 𝒞.C, m A • w A - p := by
    rw [← hxy, hp_def, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro A _
    by_cases hpos : 0 < m A
    · simp only [w, if_pos hpos, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul, sub_zero]
    · have hm0 : m A = 0 := le_antisymm (not_lt.1 hpos) (hm.1 A)
      simp only [w, if_neg hpos, hm0, zero_smul, zero_sub, lt_irrefl, if_false, neg_neg]
  rw [hx_eq, ← piV_comp 𝒞 hV τ hτ0]
  exact Set.sub_mem_sub ((mem_piV 𝒞 V τ _).2 ⟨m, hm, w, hw, rfl⟩) hp

end FuzzyGames.NTUCore.Aux

open FuzzyGames.NTUCore FuzzyGames.NTUCore.Aux in
theorem solution {n : ℕ} (𝒞 : CoalFamily n) {V : Finset (Fin n) → Set (Fin n → ℝ)}
    (hV : IsNTUGame 𝒞 V) :
    ∀ τ ∈ orthant n,
      IsClosed (piV 𝒞 V τ) ∧ Convex ℝ (piV 𝒞 V τ) ∧
      piV 𝒞 V τ - RtauNonneg τ = piV 𝒞 V τ ∧
      (∃ C ∈ Rtau τ, piV 𝒞 V τ ⊆ {C} - RtauNonneg τ) ∧
      (piV 𝒞 V τ).Nonempty ∧ piV 𝒞 V τ ⊆ Rtau τ := fun τ hτ =>
  ⟨piV_closed 𝒞 hV τ hτ, piV_convex 𝒞 hV τ, piV_comp 𝒞 hV τ hτ, piV_bdd 𝒞 hV τ,
    piV_nonempty 𝒞 hV τ hτ, piV_subset_Rtau 𝒞 hV τ⟩
