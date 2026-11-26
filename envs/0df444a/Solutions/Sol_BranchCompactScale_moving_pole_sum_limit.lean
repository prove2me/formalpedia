-- Prove2me | solution 1 for BranchCompactScale.moving_pole_sum_limit
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-18T09:01:23.25159+00:00
-- url     : https://prove2.me/submissions/07f0b2d5-7b22-4700-b558-f2d7512e45e3

import Mathlib
open Set Filter Topology
namespace CompactPoleLimit

theorem moving_pole_limit (B : ℂ) (hB : 0 < B.re)
    (k : ℕ → ℕ) (hk : Tendsto k atTop atTop)
    (lam : ℕ → ℝ) (L : ℝ) (hL : 0 < L) (hlam : Tendsto lam atTop (𝓝 L)) :
    Tendsto (fun j => ((1+(lam j : ℂ)*B/(k j : ℂ))⁻¹)^(k j)) atTop
      (𝓝 (Complex.exp (-(L : ℂ)*B))) := by
  let g : ℕ → ℂ := fun j => (lam j : ℂ)*B/(k j : ℂ)
  have hkR : Tendsto (fun j => (k j : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hk
  have hg0 : Tendsto g atTop (𝓝 0) := by
    have hh := ((Complex.continuous_ofReal.tendsto 0).comp (hlam.div_atTop hkR)).mul_const B
    simpa [g, Complex.ofReal_div, Complex.ofReal_natCast, div_mul_eq_mul_div] using hh
  have hkpos : ∀ᶠ j : ℕ in atTop, 0 < k j := hk.eventually (eventually_gt_atTop 0)
  have hlpos : ∀ᶠ j : ℕ in atTop, 0 < lam j := hlam.eventually (Ioi_mem_nhds hL)
  have hBn : B ≠ 0 := by intro hh; simpa [hh] using hB
  have hgn : ∀ᶠ j : ℕ in atTop, g j ≠ 0 := by
    filter_upwards [hkpos, hlpos] with j hj hl
    exact div_ne_zero (mul_ne_zero (by exact_mod_cast ne_of_gt hl) hBn)
      (by exact_mod_cast Nat.ne_of_gt hj)
  have hgp : Tendsto g atTop (𝓝[≠] 0) := tendsto_nhdsWithin_iff.mpr ⟨hg0,hgn⟩
  have hratio : Tendsto (fun j => Complex.log (1+g j)/g j) atTop (𝓝 1) := by
    have hd := (Complex.hasDerivAt_log (z := 1) (by simp)).tendsto_slope_zero.comp hgp
    simpa [Function.comp_def, smul_eq_mul, div_eq_mul_inv, mul_comm] using hd
  have hw : Tendsto (fun j => (lam j : ℂ)*B) atTop (𝓝 ((L : ℂ)*B)) :=
    ((Complex.continuous_ofReal.tendsto L).comp hlam).mul_const B
  have hlog : Tendsto (fun j => (k j : ℂ)*Complex.log (1+g j)) atTop (𝓝 ((L : ℂ)*B)) := by
    have hh := hratio.mul hw
    simp only [one_mul] at hh
    apply hh.congr'
    filter_upwards [hkpos,hlpos] with j hj hl
    have hn : (k j : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hj
    have hl' : (lam j : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hl
    dsimp [g]
    field_simp
  have hplus : ∀ᶠ j : ℕ in atTop, 1+g j ≠ 0 := by
    exact (tendsto_const_nhds.add hg0).eventually_ne (by norm_num : (1 : ℂ)+0 ≠ 0)
  have hpow : Tendsto (fun j => (1+g j)^(k j)) atTop (𝓝 (Complex.exp ((L : ℂ)*B))) := by
    apply ((Complex.continuous_exp.tendsto _).comp hlog).congr'
    filter_upwards [hplus] with j hj
    change Complex.exp ((k j : ℂ)*Complex.log (1+g j)) = (1+g j)^(k j)
    rw [Complex.exp_nat_mul, Complex.exp_log hj]
  have hi := hpow.inv₀ (Complex.exp_ne_zero _)
  simpa [g, inv_pow, Complex.exp_neg, neg_mul] using hi
end CompactPoleLimit
namespace CompactPoleLimit

theorem pole_majorant (B : ℂ) (hB : 0 < B.re) (k : ℕ) (hk : 1 ≤ k)
    (lam c : ℝ) (hc : 0 < c) (hcl : c ≤ lam) :
    ‖((1+(lam : ℂ)*B/(k : ℂ))⁻¹)^k‖ ≤ c⁻¹*B.re⁻¹ := by
  have hl : 0 < lam := hc.trans_le hcl
  have hn : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have ha : 0 < lam*B.re := mul_pos hl hB
  have ht : 0 < 1+lam*B.re/(k : ℝ) := by positivity
  have he : (1+(lam : ℂ)*B/(k : ℂ)).re = 1+lam*B.re/(k : ℝ) := by
    have he' : (lam : ℂ)*B/(k : ℂ) = ((lam/(k : ℝ) : ℝ) : ℂ)*B := by
      push_cast
      ring
    rw [he']
    simp [Complex.mul_re,div_mul_eq_mul_div]
  have hr : 1+lam*B.re/(k : ℝ) ≤ ‖1+(lam : ℂ)*B/(k : ℂ)‖ := by
    rw [← he]
    exact Complex.re_le_norm _
  have hb := one_add_mul_le_pow
    (show (-2 : ℝ) ≤ lam*B.re/(k : ℝ) by linarith [div_nonneg ha.le hn.le]) k
  have hcan : (k : ℝ)*(lam*B.re/(k : ℝ)) = lam*B.re := by field_simp
  rw [hcan] at hb
  rw [norm_pow,norm_inv]
  calc
    _ ≤ ((1+lam*B.re/(k : ℝ))⁻¹)^k :=
      pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg _)) (inv_anti₀ ht hr) k
    _ = ((1+lam*B.re/(k : ℝ))^k)⁻¹ := inv_pow _ _
    _ ≤ (1+lam*B.re)⁻¹ := inv_anti₀ (by positivity) hb
    _ ≤ (lam*B.re)⁻¹ := inv_anti₀ ha (by linarith)
    _ ≤ (c*B.re)⁻¹ := inv_anti₀ (mul_pos hc hB) (mul_le_mul_of_nonneg_right hcl hB.le)
    _ = c⁻¹*B.re⁻¹ := by rw [mul_inv_rev]; ring

theorem moving_pole_sum_limit {ι : Type*} (B : ι → ℂ)
    (hB : ∀ i, 0 < (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (k : ℕ → ℕ) (hk : Tendsto k atTop atTop)
    (lam : ℕ → ℝ) (L : ℝ) (hL : 0 < L) (hlam : Tendsto lam atTop (𝓝 L)) :
    Tendsto (fun j => ∑' i, ((1+(lam j : ℂ)*B i/(k j : ℂ))⁻¹)^(k j)) atTop
      (𝓝 (∑' i, Complex.exp (-(L : ℂ)*B i))) := by
  have hc : 0 < L/2 := by linarith
  have hb : ∀ᶠ j : ℕ in atTop, ∀ i,
      ‖((1+(lam j : ℂ)*B i/(k j : ℂ))⁻¹)^(k j)‖ ≤ (L/2)⁻¹*(B i).re⁻¹ := by
    filter_upwards [hk.eventually (eventually_ge_atTop 1),
      hlam.eventually (Ioi_mem_nhds (show L/2 < L by linarith))] with j hj hl i
    exact pole_majorant (B i) (hB i) (k j) hj (lam j) (L/2) hc (le_of_lt hl)
  exact tendsto_tsum_of_dominated_convergence (hs.mul_left ((L/2)⁻¹))
    (fun i => moving_pole_limit (B i) (hB i) k hk lam L hL hlam) hb
end CompactPoleLimit

theorem solution {ι : Type*} (B : ι → ℂ)
    (hB : ∀ i, 0 < (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (k : ℕ → ℕ) (hk : Tendsto k atTop atTop)
    (lam : ℕ → ℝ) (L : ℝ) (hL : 0 < L) (hlam : Tendsto lam atTop (𝓝 L)) :
    Tendsto (fun j => ∑' i, ((1+(lam j : ℂ)*B i/(k j : ℂ))⁻¹)^(k j)) atTop
      (𝓝 (∑' i, Complex.exp (-(L : ℂ)*B i))) := by
  exact CompactPoleLimit.moving_pole_sum_limit B hB hs k hk lam L hL hlam
