-- Prove2me | solution 1 for ContJRP.Align.theorem_1_3_approximation
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T21:59:53.616535+00:00
-- url     : https://prove2.me/submissions/10c5126f-fdf2-41f9-9a2d-ad39fedf55f9

import Mathlib
import Definitions.Def_ContJRP_Align_Model
import Definitions.Def_ContJRP_Align_Alignment
import Definitions.Def_ContJRP_Align_Policy
import Theorems.Thm_ContJRP_Align_lemma_1_2_density
import Theorems.Thm_ContJRP_Align_lemma_2_1_easy_regime
import Theorems.Thm_ContJRP_Align_observation_2_3_first_segment_active
import Theorems.Thm_ContJRP_Align_lemma_2_5_misaligned_solution
import Theorems.Thm_ContJRP_Align_eq_3_density
import Theorems.Thm_ContJRP_Align_lemma_3_6_assignability

open ContJRP.Align

/-- The density of a positive family exists (Lemma 1.2), so `orderDensity` is its limit. -/
theorem jrp13_density_tendsto {ι : Type*} (s : Finset ι) (T : ι → ℝ) (hT : ∀ i ∈ s, 0 < T i) :
    Filter.Tendsto (fun Δ : ℝ => (numOrders s T Δ : ℝ) / Δ) Filter.atTop
      (nhds (orderDensity s T)) := by
  have h := lemma_1_2_density s T hT
  unfold orderDensity
  rw [h.limUnder_eq]
  exact h

theorem jrp13_card_multiples (t Δ : ℝ) (ht : 0 < t) :
    (multiplesUpTo t Δ).card = ⌊Δ / t⌋₊ + 1 := by
  unfold multiplesUpTo
  rw [Finset.card_image_of_injective, Finset.card_range]
  intro a b hab
  have : (a : ℝ) = b := by
    have := mul_right_cancel₀ (ne_of_gt ht) hab
    exact this
  exact_mod_cast this

theorem jrp13_mult_subset (r Δ : ℝ) (hr : 0 < r) (m : ℕ) (hm : 1 ≤ m) :
    multiplesUpTo ((m : ℝ) * r) Δ ⊆ multiplesUpTo r Δ := by
  intro x hx
  unfold multiplesUpTo at hx ⊢
  simp only [Finset.mem_image, Finset.mem_range] at hx ⊢
  obtain ⟨k, hk, rfl⟩ := hx
  have hmr : 0 < (m : ℝ) * r := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    positivity
  refine ⟨k * m, ?_, by push_cast; ring⟩
  have hk' : k ≤ ⌊Δ / ((m : ℝ) * r)⌋₊ := by omega
  rcases lt_or_ge Δ 0 with hΔ | hΔ
  · have : ⌊Δ / ((m : ℝ) * r)⌋₊ = 0 := by
      apply Nat.floor_eq_zero.mpr
      have : Δ / ((m : ℝ) * r) < 0 := div_neg_of_neg_of_pos hΔ hmr
      linarith
    have hk0 : k = 0 := by omega
    subst hk0
    simp
  · have h1 : (k : ℝ) ≤ Δ / ((m : ℝ) * r) :=
      le_trans (by exact_mod_cast hk') (Nat.floor_le (div_nonneg hΔ hmr.le))
    have h2 : ((k * m : ℕ) : ℝ) ≤ Δ / r := by
      rw [le_div_iff₀ hmr] at h1
      rw [le_div_iff₀ hr]
      push_cast
      linarith
    have := Nat.le_floor h2
    omega

theorem solution {n : ℕ} [NeZero n] (K0 : ℝ) (K H : Fin n → ℝ)
    (hK0 : 0 < K0) (hK : ∀ i, 0 < K i) (hH : ∀ i, 0 < H i)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    (Tstar : Fin n → ℝ) (hTstar : ∀ i, 0 < Tstar i)
    (OPT : ℝ) (hOPT1 : totalCost K0 K H Tstar ≤ OPT) (hOPT2 : OPT ≤ 2 * totalCost K0 K H Tstar) :
    -- (a) the easy regime (Lemma 2.1)
    ((n : ℝ) / ε * (K0 / OPT) ≤ tmin Tstar →
      totalCost K0 K H (easyPolicy K0 K H) ≤ (1 + 2 * ε) * totalCost K0 K H Tstar) ∧
    -- (b) the difficult regime
    (tmin Tstar < (n : ℝ) / ε * (K0 / OPT) →
      -- the grid of powers of 1 + ε/2 in [K₀/OPT~, (n/ε)·K₀/OPT~) contains a guess satisfying (2)
      (∃ j : ℕ, (1 + ε / 2) ^ j * (K0 / OPT) < (n : ℝ) / ε * (K0 / OPT) ∧
        (1 - ε / 2) * tmin Tstar ≤ (1 + ε / 2) ^ j * (K0 / OPT) ∧
        (1 + ε / 2) ^ j * (K0 / OPT) ≤ tmin Tstar) ∧
      -- for every guess satisfying (2) and every choice of representatives:
      ∀ Tt : ℝ, (1 - ε / 2) * tmin Tstar ≤ Tt → Tt ≤ tmin Tstar →
        ∀ Rstar : ℕ → ℝ, IsRepChoice ε Tt Tstar Rstar →
          -- a cross-component misaligned feasible solution of (LP) exists (Lemma 2.5), and
          (∃ R : ℕ → ℝ, IsLPFeasible ε Tt Tstar Rstar R ∧ CrossMisaligned ε Tt Tstar Rstar R) ∧
          -- the final policy of every such solution is within 1 + 5ε of Tstar
          ∀ R : ℕ → ℝ, IsLPFeasible ε Tt Tstar Rstar R → CrossMisaligned ε Tt Tstar Rstar R →
            ∀ That : Fin n → ℝ, IsFinalPolicy K H ε Tt Tstar R That →
              totalCost K0 K H That ≤ (1 + 5 * ε) * totalCost K0 K H Tstar ∧
              K0 * orderDensity (active ε Tt Tstar) R + ∑ i, eoqCost (K i) (H i) (That i) ≤
                (1 + 5 * ε) * totalCost K0 K H Tstar) := by
  -- basic facts
  have heoq_pos : ∀ i (T : ℝ), 0 < T → 0 < eoqCost (K i) (H i) T := by
    intro i T hT
    unfold eoqCost
    have := hK i; have := hH i
    positivity
  have htmin_pos : 0 < tmin Tstar := by
    unfold tmin
    rw [Finset.lt_inf'_iff]
    intro i _; exact hTstar i
  obtain ⟨i0, -, hi0⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := Fin n)) Tstar
  have htmin_eq : tmin Tstar = Tstar i0 := hi0
  have hdT := jrp13_density_tendsto Finset.univ Tstar (fun i _ => hTstar i)
  -- the density of Tstar is at least 1 / tmin
  have hdens_lb : 1 / tmin Tstar ≤ orderDensity Finset.univ Tstar := by
    apply ge_of_tendsto hdT
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with Δ hΔ
    rw [div_le_div_iff₀ htmin_pos hΔ]
    have h1 : (multiplesUpTo (Tstar i0) Δ).card ≤ numOrders Finset.univ Tstar Δ := by
      unfold numOrders
      apply Finset.card_le_card
      exact Finset.subset_biUnion_of_mem (fun i => multiplesUpTo (Tstar i) Δ)
        (Finset.mem_univ i0)
    rw [jrp13_card_multiples _ _ (hTstar i0)] at h1
    have h2 : Δ / Tstar i0 ≤ ((⌊Δ / Tstar i0⌋₊ + 1 : ℕ) : ℝ) := by
      push_cast
      exact (Nat.lt_floor_add_one _).le
    have h3 : Δ / Tstar i0 ≤ (numOrders Finset.univ Tstar Δ : ℝ) :=
      le_trans h2 (by exact_mod_cast h1)
    rw [htmin_eq]
    rw [div_le_iff₀ (hTstar i0)] at h3
    linarith
  have hsum_pos : 0 < ∑ i, eoqCost (K i) (H i) (Tstar i) := by
    apply Finset.sum_pos
    · intro i _; exact heoq_pos i _ (hTstar i)
    · exact Finset.univ_nonempty
  have hF_lb : K0 / tmin Tstar ≤ totalCost K0 K H Tstar := by
    unfold totalCost jointCost
    have : K0 * (1 / tmin Tstar) ≤ K0 * orderDensity Finset.univ Tstar :=
      mul_le_mul_of_nonneg_left hdens_lb hK0.le
    rw [mul_one_div] at this
    linarith
  have hF_pos : 0 < totalCost K0 K H Tstar :=
    lt_of_lt_of_le (div_pos hK0 htmin_pos) hF_lb
  have hOPT_pos : 0 < OPT := lt_of_lt_of_le hF_pos hOPT1
  have hc_le : K0 / OPT ≤ tmin Tstar := by
    rw [div_le_iff₀ hOPT_pos]
    have := le_trans hF_lb hOPT1
    rw [div_le_iff₀ htmin_pos] at this
    linarith
  have hc_pos : 0 < K0 / OPT := div_pos hK0 hOPT_pos
  refine ⟨?_, ?_⟩
  · -- (a)
    intro heasy
    obtain ⟨h1, h2⟩ := lemma_2_1_easy_regime K0 K H hK0 hK hH ε hε0 hε1 Tstar hTstar OPT
      hOPT1 hOPT2 heasy
    exact le_trans h1 h2
  · intro hdiff
    refine ⟨?_, ?_⟩
    · -- the grid
      set q : ℝ := 1 + ε / 2 with hq
      set c : ℝ := K0 / OPT with hc
      have hq1 : 1 < q := by rw [hq]; linarith
      have hex : ∃ j : ℕ, tmin Tstar < q ^ (j + 1) * c := by
        obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (tmin Tstar / c) hq1
        refine ⟨j, ?_⟩
        rw [div_lt_iff₀ hc_pos] at hj
        have : q ^ j ≤ q ^ (j + 1) := pow_le_pow_right₀ hq1.le (Nat.le_succ j)
        nlinarith
      classical
      let j := Nat.find hex
      have hj : tmin Tstar < q ^ (j + 1) * c := Nat.find_spec hex
      have hj' : q ^ j * c ≤ tmin Tstar := by
        rcases Nat.eq_zero_or_eq_succ_pred j with h0 | hs
        · rw [h0]; simpa using hc_le
        · have hlt : j - 1 < j := by omega
          have := Nat.find_min hex hlt
          rw [not_lt] at this
          rw [hs]
          simpa using this
      refine ⟨j, lt_of_le_of_lt hj' hdiff, ?_, hj'⟩
      have hpos : 0 < q ^ j * c := by positivity
      have e : q ^ (j + 1) * c = q * (q ^ j * c) := by ring
      rw [e] at hj
      have hm : (1 - ε / 2) * q ≤ 1 := by rw [hq]; nlinarith
      have h1ε : 0 < 1 - ε / 2 := by linarith
      calc (1 - ε / 2) * tmin Tstar ≤ (1 - ε / 2) * (q * (q ^ j * c)) :=
            mul_le_mul_of_nonneg_left hj.le h1ε.le
        _ = ((1 - ε / 2) * q) * (q ^ j * c) := by ring
        _ ≤ 1 * (q ^ j * c) := mul_le_mul_of_nonneg_right hm hpos.le
        _ = q ^ j * c := one_mul _
    · intro Tt hTt1 hTt2 Rstar hR
      refine ⟨lemma_2_5_misaligned_solution ε hε0 hε1 Tstar hTstar Tt hTt1 hTt2 Rstar hR, ?_⟩
      intro R hfeas hmis That hThat
      have hTt_pos : 0 < Tt := by
        have : 0 < (1 - ε / 2) * tmin Tstar := mul_pos (by linarith) htmin_pos
        linarith
      obtain ⟨dR, dT, hdR, hdT', hle⟩ :=
        eq_3_density ε hε0 hε1 Tstar hTstar Tt hTt1 hTt2 Rstar hR R hfeas hmis
      have hodR : orderDensity (active ε Tt Tstar) R = dR := by
        unfold orderDensity; exact hdR.limUnder_eq
      have hodT : orderDensity Finset.univ Tstar = dT := by
        unfold orderDensity; exact hdT'.limUnder_eq
      have h36 := lemma_3_6_assignability ε hε0 hε1 Tstar hTstar Tt hTt1 hTt2 Rstar hR K H hK hH
        R hfeas That hThat
      have hsumC : ∑ i, eoqCost (K i) (H i) (That i) ≤
          (1 + 2 * ε) * ∑ i, eoqCost (K i) (H i) (Tstar i) := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum (fun i _ => h36 i)
      have hF : totalCost K0 K H Tstar = K0 * dT + ∑ i, eoqCost (K i) (H i) (Tstar i) := by
        unfold totalCost jointCost; rw [hodT]
      have hkey : K0 * dR + ∑ i, eoqCost (K i) (H i) (That i) ≤
          (1 + 5 * ε) * totalCost K0 K H Tstar := by
        rw [hF]
        have : K0 * dR ≤ K0 * ((1 + 5 * ε) * dT) := mul_le_mul_of_nonneg_left hle hK0.le
        nlinarith
      refine ⟨?_, by rw [hodR]; exact hkey⟩
      -- positivity of the representatives and of the final policy
      have h0act : 0 ∈ active ε Tt Tstar :=
        observation_2_3_first_segment_active ε hε0 hε1 Tstar hTstar Tt hTt1 hTt2
      have hRpos : ∀ ℓ ∈ active ε Tt Tstar, 0 < R ℓ := by
        intro ℓ hℓ
        have := (hfeas.1 ℓ hℓ).1
        have : 0 < (1 + ε) ^ ℓ * Tt := by
          have : 0 < 1 + ε := by linarith
          positivity
        linarith
      have hR0 := hRpos 0 h0act
      -- each That i is a representative, or a positive multiple of R 0
      have hshape : ∀ i, (∃ ℓ ∈ active ε Tt Tstar, That i = R ℓ) ∨
          ∃ m : ℕ, 1 ≤ m ∧ That i = (m : ℝ) * R 0 := by
        intro i
        have hmem := (hThat i).1
        unfold options at hmem
        rcases Finset.mem_union.mp hmem with h | h
        · left
          obtain ⟨ℓ, hℓ, e⟩ := Finset.mem_image.mp h
          exact ⟨ℓ, hℓ, e.symm⟩
        · right
          rw [Finset.mem_singleton] at h
          refine ⟨⌈tMax K H ε Tt i / R 0⌉₊, ?_, h⟩
          have : 0 < tMax K H ε Tt i / R 0 := by
            apply div_pos _ hR0
            unfold tMax
            exact lt_of_lt_of_le (div_pos hTt_pos hε0) (le_max_left _ _)
          have := Nat.ceil_pos.mpr this
          omega
      have hThat_pos : ∀ i, 0 < That i := by
        intro i
        rcases hshape i with ⟨ℓ, hℓ, e⟩ | ⟨m, hm, e⟩
        · rw [e]; exact hRpos ℓ hℓ
        · rw [e]
          have : (1 : ℝ) ≤ m := by exact_mod_cast hm
          positivity
      have hdH := jrp13_density_tendsto Finset.univ That (fun i _ => hThat_pos i)
      have hcount : ∀ Δ, numOrders Finset.univ That Δ ≤ numOrders (active ε Tt Tstar) R Δ := by
        intro Δ
        unfold numOrders
        apply Finset.card_le_card
        intro x hx
        rw [Finset.mem_biUnion] at hx ⊢
        obtain ⟨i, -, hx⟩ := hx
        rcases hshape i with ⟨ℓ, hℓ, e⟩ | ⟨m, hm, e⟩
        · exact ⟨ℓ, hℓ, by rw [← e]; exact hx⟩
        · refine ⟨0, h0act, ?_⟩
          rw [e] at hx
          exact jrp13_mult_subset (R 0) Δ hR0 m hm hx
      have hJ : orderDensity Finset.univ That ≤ dR := by
        apply le_of_tendsto_of_tendsto hdH hdR
        filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with Δ hΔ
        apply div_le_div_of_nonneg_right _ hΔ.le
        exact_mod_cast hcount Δ
      have : totalCost K0 K H That ≤ K0 * dR + ∑ i, eoqCost (K i) (H i) (That i) := by
        unfold totalCost jointCost
        have := mul_le_mul_of_nonneg_left hJ hK0.le
        linarith
      linarith
