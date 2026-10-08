-- Prove2me | solution 1 for DiscountedDP.Stationary.theorem5_contraction
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T21:01:03.00805+00:00
-- url     : https://prove2.me/submissions/031522a3-f596-4ed4-a99c-c3a388a387df

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Operators



namespace DiscountedDP.Stationary

open MeasureTheory ProbabilityTheory

lemma t5_le_supNorm {S : Type*} {u : S → ℝ} (h : ∃ C : ℝ, ∀ s, |u s| ≤ C) (s : S) :
    |u s| ≤ supNorm u := by
  obtain ⟨C, hC⟩ := h
  exact le_ciSup (f := fun s => |u s|) ⟨C, by rintro _ ⟨t, rfl⟩; exact hC t⟩ s

lemma t5_supNorm_le {S : Type*} [Nonempty S] {u : S → ℝ} {c : ℝ} (h : ∀ s, |u s| ≤ c) :
    supNorm u ≤ c := ciSup_le h

lemma t5_supNorm_nonneg {S : Type*} [Nonempty S] {u : S → ℝ} (h : ∃ C : ℝ, ∀ s, |u s| ≤ C) :
    0 ≤ supNorm u :=
  le_trans (abs_nonneg _) (t5_le_supNorm h (Classical.arbitrary S))

lemma t5_bdd_sub {S : Type*} [MeasurableSpace S] {u v : S → ℝ} (hu : IsBM u) (hv : IsBM v) :
    ∃ C : ℝ, ∀ s, |u s - v s| ≤ C := by
  obtain ⟨C, hC⟩ := hu.2
  obtain ⟨D, hD⟩ := hv.2
  exact ⟨C + D, fun s => (abs_sub _ _).trans (add_le_add (hC s) (hD s))⟩

lemma t5_BM_add {S : Type*} [MeasurableSpace S] {u : S → ℝ} (hu : IsBM u) (c : ℝ) :
    IsBM (fun t => u t + c) := by
  obtain ⟨C, hC⟩ := hu.2
  exact ⟨hu.1.add_const c, C + |c|, fun s => (abs_add_le _ _).trans (add_le_add (hC s) le_rfl)⟩

lemma t5_zero_of_le {x K β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (h : ∀ n : ℕ, |x| ≤ K * β ^ n) :
    x = 0 := by
  have ht : Filter.Tendsto (fun n : ℕ => K * β ^ n) Filter.atTop (nhds (K * 0)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).const_mul K
  rw [mul_zero] at ht
  have : |x| ≤ 0 := ge_of_tendsto' ht h
  exact abs_nonpos_iff.mp this

theorem theorem5_core
    {S : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (V : (S → ℝ) → S → ℝ)
    (hmap : ∀ u, IsBM u → IsBM (V u))
    (hmono : ∀ u v, IsBM u → IsBM v →
      (∀ s, u s ≤ v s) → ∀ s, V u s ≤ V v s)
    (hshift : ∀ u, IsBM u → ∀ c : ℝ, ∀ s,
      V (fun t => u t + c) s = V u s + β * c) :
    (∀ u v, IsBM u → IsBM v →
      supNorm (fun s => V u s - V v s) ≤
        β * supNorm (fun s => u s - v s)) ∧
    ∃ ustar : S → ℝ, IsBM ustar ∧ (∀ s, V ustar s = ustar s) ∧
      (∀ v, IsBM v → (∀ s, V v s = v s) → v = ustar) ∧
      ∀ u, IsBM u → ∀ n : ℕ,
        supNorm (fun s => (V^[n] u) s - ustar s) ≤
          β ^ n * supNorm (fun s => u s - ustar s) := by
  have hcon : ∀ u v, IsBM u → IsBM v →
      supNorm (fun s => V u s - V v s) ≤ β * supNorm (fun s => u s - v s) := by
    intro u v hu hv
    set c := supNorm (fun s => u s - v s) with hc
    have h1 : ∀ s, |u s - v s| ≤ c := fun s => t5_le_supNorm (u := fun s => u s - v s) (t5_bdd_sub hu hv) s
    have hA : ∀ s, V u s ≤ V v s + β * c := by
      intro s
      rw [← hshift v hv c s]
      exact hmono u _ hu (t5_BM_add hv c) (fun t => by have := h1 t; rw [abs_le] at this; linarith) s
    have hB : ∀ s, V v s ≤ V u s + β * c := by
      intro s
      rw [← hshift u hu c s]
      exact hmono v _ hv (t5_BM_add hu c) (fun t => by have := h1 t; rw [abs_le] at this; linarith) s
    apply t5_supNorm_le
    intro s
    rw [abs_le]
    constructor
    · linarith [hB s]
    · linarith [hA s]
  refine ⟨hcon, ?_⟩
  -- iterates
  set u : ℕ → S → ℝ := fun n => V^[n] (fun _ => 0) with hu_def
  have hBM0 : IsBM (fun _ : S => (0:ℝ)) := ⟨measurable_const, 0, fun s => by simp⟩
  have hiter : ∀ w, IsBM w → ∀ n, IsBM (V^[n] w) := by
    intro w hw n
    induction n with
    | zero => simpa using hw
    | succ n ih => rw [Function.iterate_succ_apply']; exact hmap _ ih
  have huBM : ∀ n, IsBM (u n) := fun n => hiter _ hBM0 n
  have usucc : ∀ n, u (n + 1) = V (u n) := fun n => by
    simp only [hu_def]; rw [Function.iterate_succ_apply']
  set D := supNorm (fun s => u 1 s - u 0 s) with hD
  have hdiff : ∀ n, supNorm (fun s => u (n+1) s - u n s) ≤ D * β ^ n := by
    intro n
    induction n with
    | zero => rw [pow_zero, mul_one]
    | succ n ih =>
      have e : supNorm (fun s => u (n+1+1) s - u (n+1) s) = supNorm (fun s => V (u (n+1)) s - V (u n) s) := by
        rw [usucc (n+1), usucc n]
      rw [e]
      calc supNorm (fun s => V (u (n+1)) s - V (u n) s)
          ≤ β * supNorm (fun s => u (n+1) s - u n s) := hcon _ _ (huBM _) (huBM _)
        _ ≤ β * (D * β ^ n) := mul_le_mul_of_nonneg_left ih hβ0
        _ = D * β ^ (n+1) := by ring
  have hpt : ∀ s n, dist (u n s) (u (n+1) s) ≤ D * β ^ n := by
    intro s n
    rw [Real.dist_eq, abs_sub_comm]
    exact (t5_le_supNorm (u := fun s => u (n+1) s - u n s) (t5_bdd_sub (huBM _) (huBM _)) s).trans (hdiff n)
  have hcs : ∀ s, CauchySeq (fun n => u n s) := fun s => cauchySeq_of_le_geometric β D hβ1 (hpt s)
  choose L hL using fun s => cauchySeq_tendsto_of_complete (hcs s)
  have hdistL : ∀ s n, |u n s - L s| ≤ D * β ^ n / (1 - β) := by
    intro s n
    rw [← Real.dist_eq]
    exact dist_le_of_le_geometric_of_tendsto β D hβ1 (hpt s) (hL s) n
  have hLBM : IsBM L := by
    refine ⟨measurable_of_tendsto_metrizable (fun n => (huBM n).1) (tendsto_pi_nhds.mpr hL), D * β ^ 0 / (1 - β), ?_⟩
    intro s
    have := hdistL s 0
    simp only [hu_def, Function.iterate_zero, id] at this
    simpa using this
  have hsupL : ∀ n, supNorm (fun s => u n s - L s) ≤ D * β ^ n / (1 - β) :=
    fun n => t5_supNorm_le (fun s => hdistL s n)
  have hfix : ∀ s, V L s = L s := by
    intro s
    have : V L s - L s = 0 := by
      apply t5_zero_of_le (K := 2 * D / (1 - β)) hβ0 hβ1
      intro n
      have h1 : |V L s - V (u n) s| ≤ β * (D * β ^ n / (1 - β)) := by
        have := t5_le_supNorm (u := fun s => V L s - V (u n) s) (t5_bdd_sub (hmap _ hLBM) (hmap _ (huBM n))) s
        refine this.trans ((hcon _ _ hLBM (huBM n)).trans (mul_le_mul_of_nonneg_left ?_ hβ0))
        have := hsupL n
        refine le_trans (le_of_eq ?_) this
        unfold supNorm; congr 1; funext t; exact abs_sub_comm _ _
      have h2 : |u (n+1) s - L s| ≤ D * β ^ (n+1) / (1 - β) := hdistL s (n+1)
      rw [usucc n] at h2
      have hD0 : 0 ≤ D := t5_supNorm_nonneg (t5_bdd_sub (huBM 1) (huBM 0))
      have hb : β * (D * β ^ n / (1 - β)) ≤ D * β ^ n / (1 - β) := by
        have : 0 ≤ D * β ^ n / (1 - β) := div_nonneg (mul_nonneg hD0 (pow_nonneg hβ0 n)) (by linarith)
        nlinarith
      have hb2 : D * β ^ (n+1) / (1 - β) ≤ D * β ^ n / (1 - β) := by
        rw [pow_succ, ← mul_assoc]
        have : 0 ≤ D * β ^ n / (1 - β) := div_nonneg (mul_nonneg hD0 (pow_nonneg hβ0 n)) (by linarith)
        rw [mul_div_right_comm]; nlinarith
      calc |V L s - L s| ≤ |V L s - V (u n) s| + |V (u n) s - L s| := abs_sub_le _ _ _
        _ ≤ D * β ^ n / (1 - β) + D * β ^ n / (1 - β) := add_le_add (h1.trans hb) (h2.trans hb2)
        _ = 2 * D / (1 - β) * β ^ n := by ring
    linarith
  refine ⟨L, hLBM, hfix, ?_, ?_⟩
  · intro v hv hvfix
    have hVv : V v = v := funext hvfix
    have hVL : V L = L := funext hfix
    have h := hcon v L hv hLBM
    rw [hVv, hVL] at h
    have h0 : 0 ≤ supNorm (fun s => v s - L s) := t5_supNorm_nonneg (t5_bdd_sub hv hLBM)
    have hz : supNorm (fun s => v s - L s) ≤ 0 := by nlinarith
    funext s
    have := (t5_le_supNorm (u := fun s => v s - L s) (t5_bdd_sub hv hLBM) s).trans hz
    have := abs_nonpos_iff.mp this
    linarith
  · intro w hw n
    induction n with
    | zero => simp
    | succ n ih =>
      have hVL : V L = L := funext hfix
      have e : (fun s => (V^[n+1] w) s - L s) = (fun s => V (V^[n] w) s - V L s) := by
        funext s; rw [Function.iterate_succ_apply', hVL]
      rw [e]
      calc _ ≤ β * supNorm (fun s => (V^[n] w) s - L s) := hcon _ _ (hiter w hw n) hLBM
        _ ≤ β * (β ^ n * supNorm (fun s => w s - L s)) := mul_le_mul_of_nonneg_left ih hβ0
        _ = _ := by ring

end DiscountedDP.Stationary

open DiscountedDP.Stationary


theorem solution
    {S : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (V : (S → ℝ) → S → ℝ)
    (hmap : ∀ u, IsBM u → IsBM (V u))
    (hmono : ∀ u v, IsBM u → IsBM v →
      (∀ s, u s ≤ v s) → ∀ s, V u s ≤ V v s)
    (hshift : ∀ u, IsBM u → ∀ c : ℝ, ∀ s,
      V (fun t => u t + c) s = V u s + β * c) :
    (∀ u v, IsBM u → IsBM v →
      supNorm (fun s => V u s - V v s) ≤
        β * supNorm (fun s => u s - v s)) ∧
    ∃ ustar : S → ℝ, IsBM ustar ∧ (∀ s, V ustar s = ustar s) ∧
      (∀ v, IsBM v → (∀ s, V v s = v s) → v = ustar) ∧
      ∀ u, IsBM u → ∀ n : ℕ,
        supNorm (fun s => (V^[n] u) s - ustar s) ≤
          β ^ n * supNorm (fun s => u s - ustar s) := by
  exact theorem5_core β hβ0 hβ1 V hmap hmono hshift
