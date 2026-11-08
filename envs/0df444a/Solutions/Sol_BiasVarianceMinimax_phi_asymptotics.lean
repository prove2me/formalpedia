-- Prove2me | solution 1 for BiasVarianceMinimax.phi_asymptotics
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T01:32:17.329173+00:00
-- url     : https://prove2.me/submissions/e766e386-1d23-44b8-ad42-9bc76e91232f

import Mathlib
import Definitions.Def_BiasVarianceMinimax_xi

open Filter Asymptotics Topology

namespace BiasVarianceMinimax.Aux_BV

open BiasVarianceMinimax

theorem equiv_of_bounds {u v L U : ℕ → ℝ} (hv : ∀ᶠ n in atTop, 0 < v n)
    (hL : ∀ᶠ n in atTop, L n ≤ u n) (hU : ∀ᶠ n in atTop, u n ≤ U n)
    (hL1 : Tendsto (fun n => L n / v n) atTop (𝓝 1))
    (hU1 : Tendsto (fun n => U n / v n) atTop (𝓝 1)) : u ~[atTop] v := by
  apply isEquivalent_of_tendsto_one
  show Tendsto (fun n => u n / v n) atTop (𝓝 1)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hL1 hU1
  · filter_upwards [hv, hL] with n hvn hLn
    exact div_le_div_of_nonneg_right hLn hvn.le
  · filter_upwards [hv, hU] with n hvn hUn
    exact div_le_div_of_nonneg_right hUn hvn.le

theorem phi_eq (n₀ n : ℕ) (κ : ℝ) :
    phi n₀ n κ = ∑ i ∈ Finset.range n, ((n₀ : ℝ) + 1 + i) ^ (-κ) := by
  unfold phi
  rw [Fin.sum_univ_eq_sum_range (fun i => 1 / runPoint n₀ i ^ κ) n]
  apply Finset.sum_congr rfl
  intro i _
  unfold runPoint
  rw [Real.rpow_neg (by positivity), one_div]
  congr 2
  ring

theorem ratio_tendsto (x₀ : ℝ) :
    Tendsto (fun n : ℕ => (x₀ + n) / (n : ℝ)) atTop (𝓝 1) := by
  have h := (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) x₀).const_add 1
  rw [add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have : (n : ℝ) ≠ 0 := by positivity
  field_simp <;> ring

end BiasVarianceMinimax.Aux_BV

open BiasVarianceMinimax BiasVarianceMinimax.Aux_BV in
theorem solution (n₀ : ℕ) :
    (fun n : ℕ => phi n₀ n 1) ~[atTop] (fun n : ℕ => Real.log (n : ℝ)) ∧
    ∀ κ : ℝ, κ < 1 →
      (fun n : ℕ => phi n₀ n κ) ~[atTop] (fun n : ℕ => 1 / (1 - κ) * (n : ℝ) ^ (1 - κ)) := by
  set x₀ : ℝ := (n₀ : ℝ) + 1 with hx₀
  have hx₀pos : 0 < x₀ := by positivity
  have hx₀1 : 1 ≤ x₀ := by have : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg _; linarith
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  -- sum–integral bounds
  have hanti : ∀ κ : ℝ, 0 ≤ κ → ∀ n : ℕ,
      (∫ y in x₀..x₀ + n, y ^ (-κ)) ≤ phi n₀ n κ ∧
        phi n₀ n κ ≤ (∫ y in x₀..x₀ + n, y ^ (-κ)) + x₀ ^ (-κ) := by
    intro κ hκ n
    have hf : AntitoneOn (fun y : ℝ => y ^ (-κ)) (Set.Icc x₀ (x₀ + n)) := by
      intro a ha b hb hab
      exact Real.rpow_le_rpow_of_nonpos (by linarith [ha.1]) hab (by linarith)
    have h1 := hf.integral_le_sum
    have h2 := hf.sum_le_integral
    rw [phi_eq]
    refine ⟨h1, ?_⟩
    have e : ∑ i ∈ Finset.range n, (x₀ + i) ^ (-κ) + (x₀ + n) ^ (-κ) =
        x₀ ^ (-κ) + ∑ i ∈ Finset.range n, (x₀ + ((i + 1 : ℕ) : ℝ)) ^ (-κ) := by
      rw [← Finset.sum_range_succ (fun i : ℕ => (x₀ + i) ^ (-κ)), Finset.sum_range_succ']
      simp only [Nat.cast_zero, add_zero]
      ring
    have hpos : 0 ≤ (x₀ + n) ^ (-κ) := Real.rpow_nonneg (by positivity) _
    have hsum : ∑ i ∈ Finset.range n, ((n₀ : ℝ) + 1 + i) ^ (-κ) =
        ∑ i ∈ Finset.range n, (x₀ + i) ^ (-κ) := rfl
    rw [hsum]
    linarith
  have hmono : ∀ κ : ℝ, κ ≤ 0 → ∀ n : ℕ,
      (∫ y in x₀..x₀ + n, y ^ (-κ)) - (x₀ + n) ^ (-κ) ≤ phi n₀ n κ ∧
        phi n₀ n κ ≤ ∫ y in x₀..x₀ + n, y ^ (-κ) := by
    intro κ hκ n
    have hf : MonotoneOn (fun y : ℝ => y ^ (-κ)) (Set.Icc x₀ (x₀ + n)) := by
      intro a ha b hb hab
      exact Real.rpow_le_rpow (by linarith [ha.1]) hab (by linarith)
    have h1 := hf.sum_le_integral
    have h2 := hf.integral_le_sum
    rw [phi_eq]
    refine ⟨?_, h1⟩
    have e : ∑ i ∈ Finset.range n, (x₀ + i) ^ (-κ) + (x₀ + n) ^ (-κ) =
        x₀ ^ (-κ) + ∑ i ∈ Finset.range n, (x₀ + ((i + 1 : ℕ) : ℝ)) ^ (-κ) := by
      rw [← Finset.sum_range_succ (fun i : ℕ => (x₀ + i) ^ (-κ)), Finset.sum_range_succ']
      simp only [Nat.cast_zero, add_zero]
      ring
    have hpos : 0 ≤ x₀ ^ (-κ) := Real.rpow_nonneg hx₀pos.le _
    have hsum : ∑ i ∈ Finset.range n, ((n₀ : ℝ) + 1 + i) ^ (-κ) =
        ∑ i ∈ Finset.range n, (x₀ + i) ^ (-κ) := rfl
    rw [hsum]
    linarith
  constructor
  · -- logarithmic case
    have hI : ∀ n : ℕ, (∫ y in x₀..x₀ + n, y ^ (-(1 : ℝ))) = Real.log (x₀ + n) - Real.log x₀ := by
      intro n
      have : (∫ y in x₀..x₀ + n, y ^ (-(1 : ℝ))) = ∫ y in x₀..x₀ + n, y⁻¹ := by
        apply intervalIntegral.integral_congr
        intro y _
        simp only [Real.rpow_neg_one]
      rw [this, integral_inv_of_pos hx₀pos (by positivity), Real.log_div (by positivity)
        hx₀pos.ne']
    have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp hnat
    have hnum : Tendsto (fun n : ℕ => Real.log ((x₀ + n) / n) - Real.log x₀) atTop
        (𝓝 (Real.log 1 - Real.log x₀)) :=
      ((Real.continuousAt_log one_ne_zero).tendsto.comp (ratio_tendsto x₀)).sub tendsto_const_nhds
    have hmain : Tendsto (fun n : ℕ => (Real.log (x₀ + n) - Real.log x₀) / Real.log n) atTop
        (𝓝 1) := by
      have h := (hnum.div_atTop hlog).const_add 1
      rw [add_zero] at h
      apply h.congr'
      filter_upwards [eventually_ge_atTop 2] with n hn
      have hn' : (1 : ℝ) < n := by exact_mod_cast hn
      have hlogpos : 0 < Real.log n := Real.log_pos hn'
      have hnpos : (0 : ℝ) < n := by linarith
      rw [Real.log_div (by positivity) hnpos.ne']
      field_simp <;> ring
    apply equiv_of_bounds (L := fun n => Real.log (x₀ + n) - Real.log x₀)
      (U := fun n => Real.log (x₀ + n) - Real.log x₀ + x₀ ^ (-(1 : ℝ)))
    · filter_upwards [eventually_ge_atTop 2] with n hn
      have hn' : (1 : ℝ) < n := by exact_mod_cast hn
      exact Real.log_pos hn'
    · exact Eventually.of_forall fun n => by
        have := (hanti 1 zero_le_one n).1
        rw [hI] at this; exact this
    · exact Eventually.of_forall fun n => by
        have := (hanti 1 zero_le_one n).2
        rw [hI] at this; exact this
    · exact hmain
    · have h2 : Tendsto (fun n : ℕ => x₀ ^ (-(1 : ℝ)) / Real.log n) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop hlog
      have h3 := hmain.add h2
      rw [add_zero] at h3
      apply h3.congr'
      filter_upwards with n
      ring
  · intro κ hκ
    set e := 1 - κ with he
    have hepos : 0 < e := by rw [he]; linarith
    have hI : ∀ n : ℕ, (∫ y in x₀..x₀ + n, y ^ (-κ)) = ((x₀ + n) ^ e - x₀ ^ e) / e := by
      intro n
      rw [integral_rpow (Or.inl (by linarith))]
      rw [show -κ + 1 = e by rw [he]; ring]
    have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ e) atTop atTop :=
      (tendsto_rpow_atTop hepos).comp hnat
    have hratio_e : Tendsto (fun n : ℕ => ((x₀ + n) / (n : ℝ)) ^ e) atTop (𝓝 1) := by
      have := (ratio_tendsto x₀).rpow_const (Or.inl one_ne_zero) (p := e)
      rwa [Real.one_rpow] at this
    -- I / target → 1
    have hIT : Tendsto (fun n : ℕ => (((x₀ + n) ^ e - x₀ ^ e) / e) / (1 / (1 - κ) * (n : ℝ) ^ e))
        atTop (𝓝 1) := by
      have h := hratio_e.sub ((tendsto_const_nhds (x := x₀ ^ e)).div_atTop hpow)
      rw [sub_zero] at h
      apply h.congr'
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      have hne : (n : ℝ) ^ e ≠ 0 := (Real.rpow_pos_of_pos hnpos e).ne'
      rw [Real.div_rpow (by positivity) hnpos.le, ← he]
      field_simp
    have htarget : ∀ᶠ n : ℕ in atTop, 0 < 1 / (1 - κ) * (n : ℝ) ^ (1 - κ) := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      have : 0 < 1 - κ := by linarith
      positivity
    rcases le_or_gt 0 κ with hκ0 | hκ0
    · -- antitone case
      apply equiv_of_bounds htarget (L := fun n => ((x₀ + n) ^ e - x₀ ^ e) / e)
        (U := fun n => ((x₀ + n) ^ e - x₀ ^ e) / e + x₀ ^ (-κ))
      · exact Eventually.of_forall fun n => by
          have := (hanti κ hκ0 n).1; rw [hI] at this; exact this
      · exact Eventually.of_forall fun n => by
          have := (hanti κ hκ0 n).2; rw [hI] at this; exact this
      · rw [← he]; exact hIT
      · have h2 : Tendsto (fun n : ℕ => x₀ ^ (-κ) * e / (n : ℝ) ^ e) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop hpow
        have h3 := hIT.add h2
        rw [add_zero] at h3
        rw [← he]
        apply h3.congr'
        filter_upwards [eventually_ge_atTop 1] with n hn
        have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
        have hne : (n : ℝ) ^ e ≠ 0 := (Real.rpow_pos_of_pos hnpos e).ne'
        rw [← he]
        field_simp <;> ring
    · -- monotone case
      apply equiv_of_bounds htarget
        (L := fun n => ((x₀ + n) ^ e - x₀ ^ e) / e - (x₀ + n) ^ (-κ))
        (U := fun n => ((x₀ + n) ^ e - x₀ ^ e) / e)
      · exact Eventually.of_forall fun n => by
          have := (hmono κ hκ0.le n).1; rw [hI] at this; exact this
      · exact Eventually.of_forall fun n => by
          have := (hmono κ hκ0.le n).2; rw [hI] at this; exact this
      · have hr2 : Tendsto (fun n : ℕ => ((x₀ + n) / (n : ℝ)) ^ (-κ)) atTop (𝓝 1) := by
          have := (ratio_tendsto x₀).rpow_const (Or.inl one_ne_zero) (p := -κ)
          rwa [Real.one_rpow] at this
        have h2 : Tendsto (fun n : ℕ => e * ((x₀ + n) / (n : ℝ)) ^ (-κ) * (1 / (n : ℝ)))
            atTop (𝓝 0) := by
          have := (hr2.const_mul e).mul (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) 1)
          rwa [mul_zero] at this
        have h3 := hIT.sub h2
        rw [sub_zero] at h3
        rw [← he]
        apply h3.congr'
        filter_upwards [eventually_ge_atTop 1] with n hn
        have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
        have hne : (n : ℝ) ^ e ≠ 0 := (Real.rpow_pos_of_pos hnpos e).ne'
        have hsplit : (x₀ + n) ^ (-κ) = ((x₀ + n) / (n : ℝ)) ^ (-κ) * (n : ℝ) ^ (-κ) := by
          rw [← Real.mul_rpow (by positivity) hnpos.le, div_mul_cancel₀ _ hnpos.ne']
        have hnn : (n : ℝ) ^ (-κ) = (n : ℝ) ^ e / n := by
          rw [he, show (1 : ℝ) - κ = -κ + 1 by ring, Real.rpow_add_one hnpos.ne']
          field_simp
        rw [hsplit, hnn, ← he]
        field_simp <;> ring
      · rw [← he]; exact hIT
