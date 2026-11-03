-- Prove2me | solution 1 for FracRiccati.Radius.riemann_sum_B_52
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T05:12:24.403968+00:00
-- url     : https://prove2.me/submissions/a3d360bb-09ad-4fb6-ab82-628ee0c5fed8

import Mathlib
import Definitions.Def_FracRiccati_Radius_Constants

namespace Aux_FRR_B52

lemma beta_real (α : ℝ) (hα : 0 < α) :
    ∫ x in (0 : ℝ)..1, (x * (1 - x)) ^ (α - 1) =
      Real.Gamma α * Real.Gamma α / Real.Gamma (α + α) := by
  have h := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := (α : ℂ)) (t := (α : ℂ))
    (by simp [hα]) (by simp [hα])
  have hI : Complex.betaIntegral (α : ℂ) (α : ℂ) =
      ((∫ x in (0 : ℝ)..1, (x * (1 - x)) ^ (α - 1) : ℝ) : ℂ) := by
    unfold Complex.betaIntegral
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
    obtain ⟨hx0, hx1⟩ := hx
    simp only
    rw [Real.mul_rpow hx0 (by linarith), Complex.ofReal_mul, Complex.ofReal_cpow hx0,
      Complex.ofReal_cpow (by linarith)]
    push_cast
    ring_nf
  have hadd : ((α : ℂ) + (α : ℂ)) = ((α + α : ℝ) : ℂ) := by push_cast; ring
  rw [hI, hadd, Complex.Gamma_ofReal, Complex.Gamma_ofReal] at h
  have h' : Real.Gamma α * Real.Gamma α =
      Real.Gamma (α + α) * ∫ x in (0 : ℝ)..1, (x * (1 - x)) ^ (α - 1) := by
    exact_mod_cast h
  have hG : 0 < Real.Gamma (α + α) := Real.Gamma_pos_of_pos (by linarith)
  rw [h']; field_simp

end Aux_FRR_B52

open FracRiccati.Radius Aux_FRR_B52 in
theorem solution (α : ℝ) (hα1 : 1 < α) (hα2 : α ≤ 2) :
    let f : ℝ → ℝ := fun x => (x * (1 - x)) ^ (α - 1)
    (∀ k : ℕ, 2 ≤ k → BTilde α ≤ (1 / (k : ℝ)) * ∑ ℓ ∈ Finset.Ico 1 k, f ((ℓ : ℝ) / k)) ∧
    (∫ u in (0 : ℝ)..1, f u) - 1 / 2 * f (1 / 2) = BTilde α ∧
    0 < BTilde α := by
  intro f
  have hα0 : 0 < α := by linarith
  have hfd : ∀ x, f x = (x * (1 - x)) ^ (α - 1) := fun x => rfl
  have hcont : Continuous f := by
    rw [show f = fun x => (x * (1 - x)) ^ (α - 1) from rfl]
    exact (continuous_id.mul (continuous_const.sub continuous_id)).rpow_const
      (fun x => Or.inr (by linarith))
  have hint : ∀ a b : ℝ, IntervalIntegrable f MeasureTheory.volume a b :=
    fun a b => hcont.intervalIntegrable a b
  have hhalf : f (1 / 2) = (2 : ℝ) ^ (2 - 2 * α) := by
    rw [hfd, show (1 / 2 : ℝ) * (1 - 1 / 2) = (2 : ℝ) ^ (-2 : ℝ) by norm_num,
      ← Real.rpow_mul (by norm_num)]
    congr 1; ring
  -- part 2
  have hpart2 : (∫ u in (0 : ℝ)..1, f u) - 1 / 2 * f (1 / 2) = BTilde α := by
    have hb := beta_real α hα0
    unfold BTilde betaFn
    rw [show (∫ u in (0 : ℝ)..1, f u) = ∫ x in (0 : ℝ)..1, (x * (1 - x)) ^ (α - 1) from rfl, hb,
      hhalf]
    have : (2 : ℝ) ^ (1 - 2 * α) = 1 / 2 * (2 : ℝ) ^ (2 - 2 * α) := by
      rw [show (2 - 2 * α) = (1 - 2 * α) + 1 by ring, Real.rpow_add_one (by norm_num)]; ring
    rw [this]
  -- basic properties of f
  have hf0 : ∀ x, 0 ≤ x → x ≤ 1 → 0 ≤ f x := fun x h0 h1 => by
    rw [hfd]; exact Real.rpow_nonneg (mul_nonneg h0 (by linarith)) _
  have hfmax : ∀ x, 0 ≤ x → x ≤ 1 → f x ≤ f (1 / 2) := by
    intro x h0 h1
    rw [hfd, hfd]
    apply Real.rpow_le_rpow (mul_nonneg h0 (by linarith)) (by nlinarith [sq_nonneg (x - 1/2)])
      (by linarith)
  have hfmono : ∀ x y, 0 ≤ x → x ≤ y → y ≤ 1 / 2 → f x ≤ f y := by
    intro x y h0 hxy hy
    rw [hfd, hfd]
    apply Real.rpow_le_rpow (mul_nonneg h0 (by linarith)) (by nlinarith) (by linarith)
  have hfsymm : ∀ x, f (1 - x) = f x := by
    intro x; rw [hfd, hfd]; ring_nf
  have hfanti : ∀ x y, 1 / 2 ≤ x → x ≤ y → y ≤ 1 → f y ≤ f x := by
    intro x y hx hxy hy
    rw [← hfsymm x, ← hfsymm y]
    exact hfmono (1 - y) (1 - x) (by linarith) (by linarith) (by linarith)
  -- part 1: the Riemann sum bound
  have hpart1 : ∀ k : ℕ, 2 ≤ k →
      (∫ u in (0 : ℝ)..1, f u) ≤ (1 / (k : ℝ)) * (∑ ℓ ∈ Finset.Ico 1 k, f ((ℓ : ℝ) / k) + f (1 / 2)) := by
    intro k hk
    have hkR : (0 : ℝ) < k := by positivity
    set h := k / 2 with hh
    have hhk : h + 1 ≤ k := by omega
    let b : ℕ → ℝ := fun i => if i < h then f (((i + 1 : ℕ) : ℝ) / k) else if i = h then f (1 / 2)
      else f ((i : ℝ) / k)
    have hpiece : ∀ i < k, (∫ u in ((i : ℕ) : ℝ) / k..((i + 1 : ℕ) : ℝ) / k, f u) ≤ (1 / (k : ℝ)) * b i := by
      intro i hi
      have hle : ((i : ℕ) : ℝ) / k ≤ ((i + 1 : ℕ) : ℝ) / k := by
        apply div_le_div_of_nonneg_right _ hkR.le; push_cast; linarith
      have hlen : ((i + 1 : ℕ) : ℝ) / k - ((i : ℕ) : ℝ) / k = 1 / k := by push_cast; ring
      have hup : ((i + 1 : ℕ) : ℝ) / k ≤ 1 := by
        rw [div_le_one hkR]; exact_mod_cast hi
      have hlo : 0 ≤ ((i : ℕ) : ℝ) / k := by positivity
      have hbound : ∀ x ∈ Set.Icc (((i : ℕ) : ℝ) / k) (((i + 1 : ℕ) : ℝ) / k), f x ≤ b i := by
        intro x hx
        obtain ⟨hx1, hx2⟩ := hx
        simp only [b]
        split_ifs with h1 h2
        · apply hfmono x _ (hlo.trans hx1) hx2
          rw [div_le_iff₀ hkR]; push_cast
          have : (i : ℝ) + 1 ≤ h := by exact_mod_cast h1
          have : (2 : ℝ) * h ≤ k := by exact_mod_cast (by omega : 2 * h ≤ k)
          linarith
        · exact hfmax x (hlo.trans hx1) (hx2.trans hup)
        · apply hfanti _ x _ hx1 (hx2.trans hup)
          rw [le_div_iff₀ hkR]
          have : h + 1 ≤ i := by omega
          have h3 : ((h + 1 : ℕ) : ℝ) ≤ i := by exact_mod_cast this
          have : k < 2 * (h + 1) := by omega
          have h4 : (k : ℝ) < 2 * ((h + 1 : ℕ) : ℝ) := by exact_mod_cast this
          linarith
      calc (∫ u in ((i : ℕ) : ℝ) / k..((i + 1 : ℕ) : ℝ) / k, f u)
          ≤ ∫ u in ((i : ℕ) : ℝ) / k..((i + 1 : ℕ) : ℝ) / k, b i :=
            intervalIntegral.integral_mono_on hle (hint _ _) intervalIntegrable_const hbound
        _ = (1 / (k : ℝ)) * b i := by
            rw [intervalIntegral.integral_const, hlen, smul_eq_mul]
    have hsplit := intervalIntegral.sum_integral_adjacent_intervals (μ := MeasureTheory.volume)
      (f := f) (a := fun i : ℕ => ((i : ℕ) : ℝ) / k) (n := k) (fun i _ => hint _ _)
    simp only [Nat.cast_zero, zero_div] at hsplit
    rw [div_self hkR.ne'] at hsplit
    rw [← hsplit]
    calc ∑ i ∈ Finset.range k, (∫ u in ((i : ℕ) : ℝ) / k..((i + 1 : ℕ) : ℝ) / k, f u)
        ≤ ∑ i ∈ Finset.range k, (1 / (k : ℝ)) * b i := by
          apply Finset.sum_le_sum; intro i hi; exact hpiece i (Finset.mem_range.mp hi)
      _ = (1 / (k : ℝ)) * (∑ ℓ ∈ Finset.Ico 1 k, f ((ℓ : ℝ) / k) + f (1 / 2)) := by
          rw [← Finset.mul_sum]
          congr 1
          rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le h) (by omega : h ≤ k),
            Finset.sum_eq_sum_Ico_succ_bot (by omega : h < k),
            ← Finset.sum_Ico_consecutive _ (by omega : 1 ≤ h + 1) hhk]
          have e1 : ∑ i ∈ Finset.Ico 0 h, b i = ∑ ℓ ∈ Finset.Ico 1 (h + 1), f ((ℓ : ℝ) / k) := by
            rw [show (1 : ℕ) = 0 + 1 from rfl, ← Finset.sum_Ico_add']
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mem_Ico] at hi
            simp only [b, if_pos hi.2]
          have e2 : b h = f (1 / 2) := by simp [b]
          have e3 : ∑ i ∈ Finset.Ico (h + 1) k, b i = ∑ ℓ ∈ Finset.Ico (h + 1) k, f ((ℓ : ℝ) / k) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mem_Ico] at hi
            simp only [b, if_neg (by omega : ¬ i < h), if_neg (by omega : ¬ i = h)]
          rw [e1, e2, e3]; ring
  refine ⟨?_, hpart2, ?_⟩
  · intro k hk
    have h1 := hpart1 k hk
    have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
    have hf2 : 0 ≤ f (1 / 2) := hf0 _ (by norm_num) (by norm_num)
    have : (1 / (k : ℝ)) * f (1 / 2) ≤ 1 / 2 * f (1 / 2) := by
      apply mul_le_mul_of_nonneg_right _ hf2
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    rw [← hpart2]
    rw [mul_add] at h1
    linarith
  · -- positivity: f ≥ f(1/2) * 4x(1-x) on [0,1]
    rw [← hpart2]
    set c := f (1 / 2) with hc
    have hcpos : 0 < c := by rw [hhalf]; positivity
    have hlow : ∀ x ∈ Set.Icc (0 : ℝ) 1, c * (4 * (x * (1 - x))) ≤ f x := by
      intro x hx
      obtain ⟨h0, h1⟩ := hx
      have ht0 : 0 ≤ 4 * (x * (1 - x)) := by nlinarith
      have ht1 : 4 * (x * (1 - x)) ≤ 1 := by nlinarith [sq_nonneg (2 * x - 1)]
      have hpow : 4 * (x * (1 - x)) ≤ (4 * (x * (1 - x))) ^ (α - 1) := by
        rcases eq_or_lt_of_le ht0 with h | h
        · rw [← h]; exact Real.rpow_nonneg le_rfl _
        · calc 4 * (x * (1 - x)) = (4 * (x * (1 - x))) ^ (1 : ℝ) := (Real.rpow_one _).symm
            _ ≤ (4 * (x * (1 - x))) ^ (α - 1) :=
              Real.rpow_le_rpow_of_exponent_ge h ht1 (by linarith)
      have hfx : f x = c * (4 * (x * (1 - x))) ^ (α - 1) := by
        rw [hc, hfd, hfd, ← Real.mul_rpow (by norm_num) ht0]
        congr 1; ring
      rw [hfx]
      exact mul_le_mul_of_nonneg_left hpow hcpos.le
    have hI : c * (2 / 3) ≤ ∫ u in (0 : ℝ)..1, f u := by
      have := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
        ((by fun_prop : Continuous fun x : ℝ => c * (4 * (x * (1 - x)))).intervalIntegrable 0 1)
        (hint 0 1) hlow
      refine le_trans (le_of_eq ?_) this
      have : (fun x : ℝ => c * (4 * (x * (1 - x)))) = fun x => (4 * c) * x - (4 * c) * x ^ 2 := by
        funext x; ring
      rw [this, intervalIntegral.integral_sub
        ((by fun_prop : Continuous fun x : ℝ => (4 * c) * x).intervalIntegrable 0 1)
        ((by fun_prop : Continuous fun x : ℝ => (4 * c) * x ^ 2).intervalIntegrable 0 1),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_id,
        integral_pow]
      norm_num; ring
    linarith
