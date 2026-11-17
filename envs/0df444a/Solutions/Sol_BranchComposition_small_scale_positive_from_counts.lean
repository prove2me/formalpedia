-- Prove2me | solution 1 for BranchComposition.small_scale_positive_from_counts
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-16T16:43:31.006489+00:00
-- url     : https://prove2.me/submissions/a9d6a9d6-861c-4f3c-969d-388cbb86ca6a

import Mathlib

namespace BranchEscapeRepair

lemma quadratic_binomial (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    1 + (n : ℝ)*t + ((n : ℝ)*((n : ℝ)-1)/2)*t^2 ≤ (1+t)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hnn : 0 ≤ (n : ℝ)*((n : ℝ)-1) := by
      cases n with
      | zero => norm_num
      | succ k => simp only [Nat.cast_add, Nat.cast_one]; nlinarith [Nat.cast_nonneg (α := ℝ) k]
    have hc : 0 ≤ ((n : ℝ)*((n : ℝ)-1)/2)*t^3 := mul_nonneg (by positivity) (by positivity)
    have hh := mul_le_mul_of_nonneg_right ih (by linarith : 0 ≤ 1+t)
    simp only [Nat.cast_add, Nat.cast_one]
    rw [pow_succ (1+t) n]
    nlinarith

theorem uniform_ratio_majorant (n : ℕ) (hn : 2 ≤ n) (x d : ℝ)
    (hx : 0 < x) (hxn : x ≤ n) (hd : 0 < d) :
    (x / (x+d))^n ≤ 4 / d^2 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have ht : 0 ≤ d/x := le_of_lt (div_pos hd hx)
  have hbin := quadratic_binomial n (d/x) ht
  have hxx : 0 < x^2 := sq_pos_of_pos hx
  have hnx : x^2 ≤ (n : ℝ)^2 := sq_le_sq₀ (le_of_lt hx) (by positivity) |>.2 hxn
  have hcoef : (n : ℝ)^2 ≤ 2*((n : ℝ)*((n : ℝ)-1)) := by nlinarith
  have hmain : d^2/4 ≤ ((n : ℝ)*((n : ℝ)-1)/2)*(d/x)^2 := by
    rw [div_pow, ← mul_div_assoc]
    apply (le_div_iff₀ hxx).2
    nlinarith [sq_nonneg d]
  have hpow : d^2/4 ≤ (1+d/x)^n := by
    have : 0 ≤ (n : ℝ)*(d/x) := mul_nonneg (by positivity) ht
    linarith
  have hd2 : 0 < d^2 := sq_pos_of_pos hd
  have hid : x/(x+d) = (1+d/x)⁻¹ := by field_simp
  rw [hid, inv_pow]
  calc
    ((1+d/x)^n)⁻¹ ≤ (d^2/4)⁻¹ := inv_anti₀ (by positivity) hpow
    _ = 4/d^2 := by field_simp

end BranchEscapeRepair
#print axioms BranchEscapeRepair.uniform_ratio_majorant

open MeasureTheory Set
namespace BranchTailRepair
lemma kernel_bound (n : ℕ) (hn : 2 ≤ n) (l y : ℝ)
    (hl : l ≤ 1) (hy : 1 ≤ y) :
    ((1+(y^2-l/4)/(n : ℝ))^n)⁻¹ ≤ 16/y^4 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0<n by omega)
  have hy0 : 0<y := by linarith
  have hd : 0<y^2/2 := by positivity
  have h := BranchEscapeRepair.uniform_ratio_majorant n hn (n : ℝ) (y^2/2) hn0 le_rfl hd
  have hh : 1+(y^2/2)/(n : ℝ) ≤ 1+(y^2-l/4)/(n : ℝ) := by
    apply add_le_add_right
    apply (div_le_div_iff_of_pos_right hn0).2
    nlinarith [sq_nonneg (y-1)]
  have hp : (1+(y^2/2)/(n : ℝ))^n ≤ (1+(y^2-l/4)/(n : ℝ))^n :=
    pow_le_pow_left₀ (by positivity) hh n
  have hid : ((n : ℝ)/((n : ℝ)+y^2/2))^n = ((1+(y^2/2)/(n : ℝ))^n)⁻¹ := by
    rw [← inv_pow]
    congr 1
    field_simp
  rw [hid] at h
  have hh2 := (inv_anti₀ (by positivity : 0 < (1+(y^2/2)/(n : ℝ))^n) hp).trans h
  have heq : 4 / (y^2/2)^2 = 16/y^4 := by field_simp; ring
  rwa [heq] at hh2

lemma weighted_bound (n : ℕ) (hn : 2 ≤ n) (l L y : ℝ)
    (hl : l ≤ 1) (hL : 1 ≤ L) (hy : 1 ≤ y) :
    0 ≤ (L+Real.log (y+3))*((1+(y^2-l/4)/(n : ℝ))^n)⁻¹ ∧
    (L+Real.log (y+3))*((1+(y^2-l/4)/(n : ℝ))^n)⁻¹ ≤ 64*L/y^3 := by
  have hn0 : (0 : ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hy0 : 0<y := by linarith
  have hlog0 : 0 ≤ Real.log (y+3) := Real.log_nonneg (by linarith)
  have hlog := Real.log_le_sub_one_of_pos (by linarith : 0<y+3)
  have hweight : L+Real.log (y+3) ≤ 4*L*y := by
    nlinarith [mul_nonneg (show 0≤L-1 by linarith) (show 0≤y-1 by linarith)]
  have hbase : 0 < 1+(y^2-l/4)/(n : ℝ) := by
    have : 0 ≤ y^2-l/4 := by nlinarith [sq_nonneg (y-1)]
    positivity
  constructor
  · positivity
  · calc
      _ ≤ (4*L*y)*(16/y^4) := mul_le_mul hweight (kernel_bound n hn l y hl hy)
        (by positivity) (by positivity)
      _ = 64*L/y^3 := by field_simp; ring

theorem integrated_tail (n : ℕ) (hn : 2 ≤ n) (l L M : ℝ)
    (hl : l ≤ 1) (hL : 1 ≤ L) (hM : 1 ≤ M) :
    IntegrableOn (fun y : ℝ => (L+Real.log (y+3))*((1+(y^2-l/4)/(n : ℝ))^n)⁻¹) (Ioi M) ∧
    (∫ y : ℝ in Ioi M, (L+Real.log (y+3))*((1+(y^2-l/4)/(n : ℝ))^n)⁻¹) ≤ 32*L/M^2 := by
  have hM0 : 0<M := by linarith
  have hpow : ∀ y : ℝ, y^(-3 : ℝ) = 1/y^3 := by
    intro y
    convert Real.rpow_intCast y (-3) using 1 <;> norm_num
  have hg : IntegrableOn (fun y : ℝ => 64*L/y^3) (Ioi M) := by
    have h := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ)< -1) hM0).const_mul (64*L)
    change Integrable (fun y : ℝ => 64*L/y^3) (volume.restrict (Ioi M))
    convert h using 1 <;> funext y <;> rw [hpow] <;> ring
  have hbound : ∀ᵐ y : ℝ ∂volume.restrict (Ioi M),
      ‖(L+Real.log (y+3))*((1+(y^2-l/4)/(n : ℝ))^n)⁻¹‖ ≤ 64*L/y^3 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have h := weighted_bound n hn l L y hl hL (le_trans hM (le_of_lt hy))
    simpa only [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2
  have hf : IntegrableOn (fun y : ℝ => (L+Real.log (y+3))*((1+(y^2-l/4)/(n : ℝ))^n)⁻¹) (Ioi M) :=
    hg.mono' (by fun_prop) hbound
  refine ⟨hf, ?_⟩
  have hle := integral_mono_ae hf hg (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact (weighted_bound n hn l L y hl hL (le_trans hM (le_of_lt hy))).2)
  have heq : (∫ y : ℝ in Ioi M, 64*L/y^3) = 32*L/M^2 := by
    have hfun : (fun y : ℝ => 64*L/y^3) = (fun y : ℝ => 64*L*y^(-3 : ℝ)) := by
      funext y
      rw [hpow]
      ring
    rw [hfun, integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hM0]
    have hp2 : M^(-2 : ℝ) = 1/M^2 := by
      convert Real.rpow_intCast M (-2) using 1 <;> norm_num
    norm_num only at *
    rw [hp2]
    ring
  rwa [heq] at hle
end BranchTailRepair

open Filter Topology
namespace BranchTailRepair
lemma cube_step (B h : ℝ) (hB : 0<B) (hh : 0<h) :
    1/(B+h)^3 ≤ (1/B^2-1/(B+h)^2)/(2*h) := by
  have he : (1/B^2-1/(B+h)^2)/(2*h)-1/(B+h)^3 =
      h*(3*B+h)/(2*B^2*(B+h)^3) := by field_simp; ring
  have hp : 0 ≤ h*(3*B+h)/(2*B^2*(B+h)^3) := by positivity
  linarith

lemma cube_partial (M h : ℝ) (hM : 0<M) (hh : 0<h) (N : ℕ) :
    ∑ j ∈ Finset.range N, 1/(M+((j+1 : ℕ) : ℝ)*h)^3 ≤
      (1/M^2-1/(M+(N : ℝ)*h)^2)/(2*h) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hp : 0<M+(N : ℝ)*h := by positivity
    have hs := cube_step (M+(N : ℝ)*h) h hp hh
    simp only [Nat.cast_add, Nat.cast_one] at *
    have he : M+((N : ℝ)+1)*h = M+(N : ℝ)*h+h := by ring
    rw [he]
    simp only [sub_div] at *
    linarith

lemma cube_sum_bound (M h : ℝ) (hM : 0<M) (hh : 0<h) :
    Summable (fun j : ℕ => 1/(M+(j : ℝ)*h)^3) ∧
    (∑' j : ℕ, 1/(M+(j : ℝ)*h)^3) ≤ 1/M^3+1/(2*h*M^2) := by
  have hpart : ∀ N : ℕ, ∑ j ∈ Finset.range N, 1/(M+(j : ℝ)*h)^3 ≤ 1/M^3+1/(2*h*M^2) := by
    intro N
    cases N with
    | zero => simp; positivity
    | succ N =>
      rw [Finset.sum_range_succ']
      simp only [Nat.cast_zero, zero_mul, add_zero]
      have hs := cube_partial M h hM hh N
      have hp : 0 ≤ 1/(M+(N : ℝ)*h)^2/(2*h) := by positivity
      have he : (1/M^2-1/(M+(N : ℝ)*h)^2)/(2*h) =
        1/(2*h*M^2)-1/(M+(N : ℝ)*h)^2/(2*h) := by ring
      rw [he] at hs
      linarith
  have hs := summable_of_sum_range_le (fun j => by positivity) hpart
  refine ⟨hs, ?_⟩
  exact le_of_tendsto' hs.hasSum.tendsto_sum_nat hpart

theorem discrete_tail (n : ℕ) (hn : 2≤n) (l L M h : ℝ)
    (hl : l≤1) (hL : 1≤L) (hM : 1≤M) (hh : 0<h) :
    Summable (fun j : ℕ => (L+Real.log (M+(j : ℝ)*h+3))*
      ((1+((M+(j : ℝ)*h)^2-l/4)/(n : ℝ))^n)⁻¹) ∧
    (∑' j : ℕ, (L+Real.log (M+(j : ℝ)*h+3))*
      ((1+((M+(j : ℝ)*h)^2-l/4)/(n : ℝ))^n)⁻¹) ≤
      64*L/M^3+32*L/(h*M^2) := by
  have hM0 : 0<M := by linarith
  have hcube := cube_sum_bound M h hM0 hh
  have hb : ∀ j : ℕ, 1≤M+(j : ℝ)*h := by
    intro j
    have hp : 0≤(j : ℝ)*h := by positivity
    linarith
  have hw := fun (j : ℕ) => weighted_bound n hn l L (M+(j : ℝ)*h) hl hL (hb j)
  have hg := hcube.1.mul_left (64*L)
  have hf := Summable.of_nonneg_of_le (fun j => (hw j).1)
    (fun j => by simpa only [mul_one_div] using (hw j).2) hg
  refine ⟨hf, ?_⟩
  have hs := hf.tsum_le_tsum (fun j => by simpa only [mul_one_div] using (hw j).2) hg
  rw [tsum_mul_left] at hs
  have ht := mul_le_mul_of_nonneg_left hcube.2 (by positivity : 0≤64*L)
  have he : 64*L*(1/M^3+1/(2*h*M^2)) = 64*L/M^3+32*L/(h*M^2) := by ring
  rw [he] at ht
  exact hs.trans ht
end BranchTailRepair

namespace BranchTailRepair
theorem normalized_tail (n : ℕ) (hn : 2≤n) (l L M h : ℝ)
    (hl : l≤1) (hL : 1≤L) (hM : 1≤M) (hh : 0<h) (hh1 : h≤1) :
    0 ≤ h/L * (∑' j : ℕ, (L+Real.log (M+(j : ℝ)*h+3))*
      ((1+((M+(j : ℝ)*h)^2-l/4)/(n : ℝ))^n)⁻¹) ∧
    h/L * (∑' j : ℕ, (L+Real.log (M+(j : ℝ)*h+3))*
      ((1+((M+(j : ℝ)*h)^2-l/4)/(n : ℝ))^n)⁻¹) ≤ 96/M^2 := by
  have hL0 : 0<L := by linarith
  have hM0 : 0<M := by linarith
  have ht := discrete_tail n hn l L M h hl hL hM hh
  constructor
  · apply mul_nonneg (by positivity)
    apply tsum_nonneg
    intro j
    have hy : 1≤M+(j : ℝ)*h := by
      have hp : 0≤(j : ℝ)*h := by positivity
      linarith
    exact (weighted_bound n hn l L (M+(j : ℝ)*h) hl hL hy).1
  · have hle := mul_le_mul_of_nonneg_left ht.2 (by positivity : 0≤h/L)
    have he : h/L*(64*L/M^3+32*L/(h*M^2)) = 64*(h/M)/M^2+32/M^2 := by
      field_simp
    rw [he] at hle
    have hm : h/M ≤ 1 := (div_le_iff₀ hM0).2 (by linarith)
    have hp : 64*(h/M)/M^2 ≤ 64/M^2 :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    have he2 : 64/M^2+32/M^2=96/M^2 := by ring
    linarith

theorem normalized_tail_limit (k : ℕ → ℕ) (hk : ∀ n, 2≤k n)
    (l L M h : ℕ → ℝ) (hl : ∀ n, l n≤1) (hL : ∀ n, 1≤L n)
    (hM : ∀ n, 1≤M n) (hh : ∀ n, 0<h n) (hh1 : ∀ n, h n≤1)
    (hMt : Tendsto M atTop atTop) :
    Tendsto (fun n => h n/L n * (∑' j : ℕ, (L n+Real.log (M n+(j : ℝ)*h n+3))*
      ((1+((M n+(j : ℝ)*h n)^2-l n/4)/(k n : ℝ))^(k n))⁻¹)) atTop (𝓝 0) := by
  have hi : Tendsto (fun n => (M n)⁻¹) atTop (𝓝 (0 : ℝ)) := tendsto_inv_atTop_zero.comp hMt
  have hb : Tendsto (fun n => 96/(M n)^2) atTop (𝓝 (0 : ℝ)) := by
    have ht := (hi.pow 2).const_mul 96
    simpa only [zero_pow (by norm_num : (2 : ℕ)≠0), mul_zero, inv_pow, div_eq_mul_inv] using ht
  apply squeeze_zero (fun n => (normalized_tail (k n) (hk n) (l n) (L n) (M n) (h n) (hl n) (hL n) (hM n) (hh n) (hh1 n)).1)
    (fun n => (normalized_tail (k n) (hk n) (l n) (L n) (M n) (h n) (hl n) (hL n) (hM n) (hh n) (hh1 n)).2) hb
end BranchTailRepair



namespace BranchShellRepair

theorem fiber_norm_bound {ι : Type*} (f : ι → ℂ) (bin : ι → ℕ) (N K : ℕ → ℝ)
    (hK : ∀ j, 0≤K j) (hN : ∀ j, 0≤N j)
    (hc : ∀ (F : Finset ι) (j : ℕ), ((F.filter (fun i => bin i=j)).card : ℝ)≤N j)
    (hf : ∀ i, ‖f i‖≤K (bin i)) (hs : Summable (fun j => N j*K j)) :
    Summable f ∧ (∑' i, ‖f i‖)≤∑' j, N j*K j := by
  classical
  have hfinite : ∀ F : Finset ι, ∑ i ∈ F, ‖f i‖≤∑' j, N j*K j := by
    intro F
    have hid := Finset.sum_fiberwise_of_maps_to (s:=F) (t:=F.image bin)
      (g:=bin) (fun i hi => Finset.mem_image.mpr ⟨i,hi,rfl⟩) (fun i => ‖f i‖)
    rw [← hid]
    calc
      _ ≤ ∑ j ∈ F.image bin, N j*K j := by
        apply Finset.sum_le_sum
        intro j hj
        have hsum : ∑ i ∈ F.filter (fun i => bin i=j), ‖f i‖ ≤
            ((F.filter (fun i => bin i=j)).card : ℝ)*K j := by
          calc
            _ ≤ ∑ i ∈ F.filter (fun i => bin i=j), K j := by
              apply Finset.sum_le_sum
              intro i hi
              have he := (Finset.mem_filter.mp hi).2
              simpa only [he] using hf i
            _ = _ := by simp
        exact hsum.trans (mul_le_mul_of_nonneg_right (hc F j) (hK j))
      _ ≤ ∑' j, N j*K j := hs.sum_le_tsum _ (fun j _ => mul_nonneg (hN j) (hK j))
  have hn := summable_of_sum_le (fun i => norm_nonneg (f i)) hfinite
  refine ⟨hn.of_norm_bounded (fun i => le_rfl), ?_⟩
  exact tsum_le_of_sum_le' (tsum_nonneg (fun j => mul_nonneg (hN j) (hK j))) hfinite
end BranchShellRepair
#print axioms BranchShellRepair.fiber_norm_bound


namespace BranchShellRepair

theorem pole_kernel_bound (n : ℕ) (hn : 2≤n) (h y e g : ℝ)
    (hh : 0<h) (hh1 : h≤1) (hy : 1≤y) (he : |e|≤1/2)
    (hg : 0≤g) (hgy : y≤g*h) :
    ‖(((((n : ℝ)/h^2 : ℝ) : ℂ)/
      (((n : ℝ)/h^2+g^2-e^2 : ℝ)-(2*e*g : ℝ)*Complex.I))^n)‖ ≤
    ((1+(y^2-h^2/4)/(n : ℝ))^n)⁻¹ := by
  have hn0 : (0 : ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hne : h≠0 := ne_of_gt hh
  have hnne : (n : ℝ)≠0 := ne_of_gt hn0
  have he2 : e^2≤1/4 := by have := abs_le.mp he; nlinarith
  have hsq : y^2≤g^2*h^2 := by nlinarith [sq_nonneg (g*h-y)]
  have hshift : 0≤y^2-h^2/4 := by nlinarith [sq_nonneg (y-1), sq_nonneg (h-1)]
  have hb0 : 0<1+(y^2-h^2/4)/(n : ℝ) := by positivity
  have hden : (n : ℝ)/h^2+(y^2-h^2/4)/h^2 ≤ (n : ℝ)/h^2+g^2-e^2 := by
    have hs : (y^2-h^2/4)/h^2 ≤ g^2-e^2 := by
      apply (div_le_iff₀ (sq_pos_of_pos hh)).2
      nlinarith [mul_le_mul_of_nonneg_right he2 (sq_nonneg h)]
    linarith
  have hd0 : 0<(n : ℝ)/h^2+(y^2-h^2/4)/h^2 := by positivity
  have hre : (n : ℝ)/h^2+g^2-e^2 ≤
      ‖((n : ℝ)/h^2+g^2-e^2 : ℝ)-(2*e*g : ℝ)*Complex.I‖ := by
    simpa only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero] using
      Complex.re_le_norm (((n : ℝ)/h^2+g^2-e^2 : ℝ)-(2*e*g : ℝ)*Complex.I)
  have hnorm := hden.trans hre
  have hquot : (n : ℝ)/h^2 / ‖((n : ℝ)/h^2+g^2-e^2 : ℝ)-(2*e*g : ℝ)*Complex.I‖ ≤
      (1+(y^2-h^2/4)/(n : ℝ))⁻¹ := by
    calc
      _ ≤ (n : ℝ)/h^2 / ((n : ℝ)/h^2+(y^2-h^2/4)/h^2) :=
        div_le_div_of_nonneg_left (by positivity) hd0 hnorm
      _ = _ := by field_simp
  rw [norm_pow, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0<(n : ℝ)/h^2)]
  rw [← inv_pow]
  exact pow_le_pow_left₀ (by positivity) hquot n
end BranchShellRepair
#print axioms BranchShellRepair.pole_kernel_bound


namespace BranchShellRepair

theorem indexed_tail {ι : Type*} (n : ℕ) (hn : 2≤n) (h L A C : ℝ)
    (hh : 0<h) (hh1 : h≤1) (hL : 1≤L) (hA : 1≤A) (hC : 0≤C)
    (e g : ι → ℝ) (bin : ι → ℕ) (he : ∀ i, |e i|≤1/2) (hg : ∀ i, 0≤g i)
    (hbin : ∀ i, A+(bin i : ℝ)*h≤g i*h)
    (hcount : ∀ (F : Finset ι) (j : ℕ), ((F.filter (fun i => bin i=j)).card : ℝ)≤
      C*(L+Real.log (A+(j : ℝ)*h+3))) :
    Summable (fun i => (((((n : ℝ)/h^2 : ℝ) : ℂ)/
      (((n : ℝ)/h^2+(g i)^2-(e i)^2 : ℝ)-(2*e i*g i : ℝ)*Complex.I))^n)) ∧
    h/L * (∑' i, ‖(((((n : ℝ)/h^2 : ℝ) : ℂ)/
      (((n : ℝ)/h^2+(g i)^2-(e i)^2 : ℝ)-(2*e i*g i : ℝ)*Complex.I))^n)‖) ≤96*C/A^2 := by
  let K : ℕ → ℝ := fun j => ((1+((A+(j : ℝ)*h)^2-h^2/4)/(n : ℝ))^n)⁻¹
  let W : ℕ → ℝ := fun j => L+Real.log (A+(j : ℝ)*h+3)
  have hn0 : (0 : ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hhy : h^2≤1 := by nlinarith [sq_nonneg (h-1)]
  have hy (j : ℕ) : 1≤A+(j : ℝ)*h := by
    have := mul_nonneg (Nat.cast_nonneg (α:=ℝ) j) hh.le
    linarith
  have hK (j : ℕ) : 0≤K j := by
    have hz : 0≤(A+(j : ℝ)*h)^2-h^2/4 := by nlinarith [sq_nonneg (A+(j : ℝ)*h-1), hy j]
    dsimp [K]
    positivity
  have hW (j : ℕ) : 0≤W j := by
    have hl := Real.log_nonneg (show 1≤A+(j : ℝ)*h+3 by linarith [hy j])
    dsimp [W]
    linarith
  have hdisc := BranchTailRepair.discrete_tail n hn (h^2) L A h hhy hL hA hh
  have hs : Summable (fun j => (C*W j)*K j) := by
    simpa only [W,K,mul_assoc] using hdisc.1.mul_left C
  have hf := fiber_norm_bound
    (fun i => (((((n : ℝ)/h^2 : ℝ) : ℂ)/
      (((n : ℝ)/h^2+(g i)^2-(e i)^2 : ℝ)-(2*e i*g i : ℝ)*Complex.I))^n))
    bin (fun j => C*W j) K hK (fun j => mul_nonneg hC (hW j)) hcount
    (fun i => pole_kernel_bound n hn h (A+(bin i : ℝ)*h) (e i) (g i)
      hh hh1 (hy _) (he i) (hg i) (hbin i)) hs
  refine ⟨hf.1, ?_⟩
  have ht := mul_le_mul_of_nonneg_left hf.2 (by positivity : 0≤h/L)
  have hid : (∑' j, (C*W j)*K j) = C*(∑' j, W j*K j) := by
    simp only [mul_assoc, tsum_mul_left]
  rw [hid] at ht
  have hnorm := (BranchTailRepair.normalized_tail n hn (h^2) L A h hhy hL hA hh hh1).2
  have hmul := mul_le_mul_of_nonneg_left hnorm hC
  change C*(h/L*(∑' j, W j*K j)) ≤ C*(96/A^2) at hmul
  calc
    _ ≤ h/L*(C*(∑' j, W j*K j)) := ht
    _ = C*(h/L*(∑' j, W j*K j)) := by ring
    _ ≤ C*(96/A^2) := hmul
    _ = 96*C/A^2 := by ring
end BranchShellRepair
#print axioms BranchShellRepair.indexed_tail

namespace BranchShellRepair
lemma log_window_weight (h A L : ℝ) (j : ℕ) (hh : 0<h) (hh1 : h≤1)
    (hA : 1≤A) (hlog : -Real.log h≤L) :
    Real.log (A/h+(j : ℝ)+3) ≤ L+Real.log (A+(j : ℝ)*h+3) := by
  have hA0 : 0<A := by linarith
  have hhne : h≠0 := ne_of_gt hh
  have hm : (A/h+(j : ℝ)+3)*h≤A+(j : ℝ)*h+3 := by
    have hid : A/h*h=A := div_mul_cancel₀ A hhne
    nlinarith
  have hle := Real.log_le_log (show 0<A/h+(j : ℝ)+3 by positivity)
    ((le_div_iff₀ hh).2 hm)
  rw [Real.log_div (by positivity : A+(j : ℝ)*h+3≠0) hhne] at hle
  linarith

theorem tail_from_unit_count {ι : Type*} (n : ℕ) (hn : 2≤n) (h L A C : ℝ)
    (hh : 0<h) (hh1 : h≤1) (hL : 1≤L) (hA : 1≤A) (hC : 0≤C)
    (hlog : -Real.log h≤L) (e g : ι → ℝ)
    (he : ∀ i, |e i|≤1/2) (hg : ∀ i, 0≤g i) (hhigh : ∀ i, A<g i*h)
    (hcount : ∀ T ≥ (1 : ℝ), ∀ F : Finset ι,
      (∀ i ∈ F, T≤g i ∧ g i<T+1) → (F.card : ℝ)≤C*Real.log (T+3)) :
    Summable (fun i => (((((n : ℝ)/h^2 : ℝ) : ℂ)/
      (((n : ℝ)/h^2+(g i)^2-(e i)^2 : ℝ)-(2*e i*g i : ℝ)*Complex.I))^n)) ∧
    h/L * (∑' i, ‖(((((n : ℝ)/h^2 : ℝ) : ℂ)/
      (((n : ℝ)/h^2+(g i)^2-(e i)^2 : ℝ)-(2*e i*g i : ℝ)*Complex.I))^n)‖) ≤96*C/A^2 := by
  classical
  let bin : ι → ℕ := fun i => ⌊g i-A/h⌋₊
  have hdiff (i : ι) : 0≤g i-A/h := by
    have ht : A/h<g i := (div_lt_iff₀ hh).2 (hhigh i)
    linarith
  have hb (i : ι) : A/h+(bin i : ℝ)≤g i ∧ g i<A/h+(bin i : ℝ)+1 := by
    have hlo := Nat.floor_le (hdiff i)
    have hhi := Nat.lt_floor_add_one (g i-A/h)
    change A/h+(⌊g i-A/h⌋₊ : ℝ)≤g i ∧ g i<A/h+(⌊g i-A/h⌋₊ : ℝ)+1
    constructor <;> linarith
  have hbin (i : ι) : A+(bin i : ℝ)*h≤g i*h := by
    have hm := mul_le_mul_of_nonneg_right (hb i).1 hh.le
    have heq : (A/h+(bin i : ℝ))*h=A+(bin i : ℝ)*h := by field_simp
    rwa [heq] at hm
  apply indexed_tail n hn h L A C hh hh1 hL hA hC e g bin he hg hbin
  intro F j
  have hT : 1≤A/h+(j : ℝ) := by
    have hx : 1≤A/h := (le_div_iff₀ hh).2 (by linarith)
    have hj := Nat.cast_nonneg (α:=ℝ) j
    linarith
  have hc := hcount (A/h+(j : ℝ)) hT (F.filter (fun i => bin i=j)) (by
    intro i hi
    have hij := (Finset.mem_filter.mp hi).2
    simpa only [hij] using hb i)
  exact hc.trans (mul_le_mul_of_nonneg_left (log_window_weight h A L j hh hh1 hA hlog) hC)
end BranchShellRepair
#print axioms BranchShellRepair.tail_from_unit_count



namespace BranchNearRepair
lemma pow_distance (z : ℂ) (r : ℝ) (hr : 0≤r) (hz : ‖z-1‖≤r) (n : ℕ) :
    ‖z^n-1‖ ≤ (1+r)^n-1 := by
  have hnz : ‖z‖≤1+r := by
    have h := norm_add_le (z-1) (1 : ℂ)
    simp only [sub_add_cancel, norm_one] at h
    linarith
  induction n with
  | zero => simp
  | succ n ih =>
    have he : z^(n+1)-1 = (z^n-1)*z+(z-1) := by ring
    rw [he]
    calc
      _ ≤ ‖(z^n-1)*z‖+‖z-1‖ := norm_add_le _ _
      _ = ‖z^n-1‖*‖z‖+‖z-1‖ := by rw [norm_mul]
      _ ≤ ((1+r)^n-1)*(1+r)+r := by
        exact add_le_add (mul_le_mul ih hnz (norm_nonneg _) (by nlinarith [norm_nonneg (z^n-1)])) hz
      _ = (1+r)^(n+1)-1 := by ring

lemma power_bound (n : ℕ) (r : ℝ) (hr : 0≤r) (hr1 : r≤1) (hnr : (n : ℝ)*r≤1/4) :
    (1+r)^n ≤ 4/3 := by
  have hb := one_add_mul_le_pow (show (-2 : ℝ)≤ -r by linarith) n
  have hq : (3/4 : ℝ) ≤ (1-r)^n := by
    simp only [mul_neg, ← sub_eq_add_neg] at hb
    linarith
  have hp : (1+r)^n*(1-r)^n ≤ 1 := by
    rw [← mul_pow]
    have ht : (1+r)*(1-r) ≤ 1 := by nlinarith [sq_nonneg r]
    simpa using pow_le_pow_left₀ (by nlinarith) ht n
  have hm := mul_le_mul_of_nonneg_left hq (by positivity : 0≤(1+r)^n)
  nlinarith

theorem inverse_power_positive (n : ℕ) (hn : 1≤n) (w : ℂ)
    (hw : (n : ℝ)*‖w‖ ≤ 1/8) :
    ‖((1-w)⁻¹)^n-1‖≤1/2 ∧ 1/2≤(((1-w)⁻¹)^n).re := by
  have hnR : (1 : ℝ)≤n := by exact_mod_cast hn
  have hr : ‖w‖≤1/8 := by nlinarith [norm_nonneg w]
  have hnorm : 1-‖w‖≤‖(1 : ℂ)-w‖ := by
    have h := norm_add_le ((1 : ℂ)-w) w
    simp only [sub_add_cancel, norm_one] at h
    linarith
  have hne : (1 : ℂ)-w ≠ 0 := by
    intro he
    rw [he, norm_zero] at hnorm
    linarith
  have he : ((1-w)⁻¹ : ℂ)-1 = w/(1-w) := by field_simp; ring
  have hd : ‖((1-w)⁻¹ : ℂ)-1‖≤2*‖w‖ := by
    rw [he, norm_div]
    apply (div_le_iff₀ (norm_pos_iff.mpr hne)).2
    nlinarith [norm_nonneg w]
  have hp := pow_distance ((1-w)⁻¹) (2*‖w‖) (by positivity) hd n
  have hbound := power_bound n (2*‖w‖) (by positivity) (by linarith) (by linarith)
  have hdist : ‖((1-w)⁻¹)^n-1‖≤1/2 := by linarith
  refine ⟨hdist, ?_⟩
  have hreal := Complex.re_le_norm (1-((1-w)⁻¹)^n)
  rw [norm_sub_rev] at hreal
  simp only [Complex.sub_re, Complex.one_re] at hreal
  linarith
end BranchNearRepair
#print axioms BranchNearRepair.inverse_power_positive

namespace BranchNearRepair
lemma perturbation_bound (x e g : ℝ) (hx : 0<x) (he : |e|≤1/2) (hg : 0≤g) :
    ‖(((e^2 : ℝ) : ℂ)+(2*e*g : ℝ)*Complex.I)/(x+g^2 : ℝ)‖ ≤ (1/4+g)/x := by
  have he2 : e^2≤1/4 := by
    have := abs_le.mp he
    nlinarith
  have hp : |2*e*g|≤g := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ)≤2), abs_of_nonneg hg]
    nlinarith
  have hn := norm_add_le ((e^2 : ℝ) : ℂ) ((2*e*g : ℝ)*Complex.I)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg e), Complex.norm_I, mul_one, abs_of_nonneg hg, abs_of_nonneg (by norm_num : (0 : ℝ)≤2)] at hn
  rw [abs_mul, abs_mul, abs_of_nonneg hg, abs_of_nonneg (by norm_num : (0 : ℝ)≤2)] at hp
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0<x+g^2)]
  calc
    _ ≤ (1/4+g)/(x+g^2) := div_le_div_of_nonneg_right (by linarith) (by positivity)
    _ ≤ (1/4+g)/x := div_le_div_of_nonneg_left (by positivity) hx (by nlinarith [sq_nonneg g])

theorem near_window_positive (n : ℕ) (hn : 1≤n) (h A e g : ℝ)
    (hh : 0<h) (he : |e|≤1/2) (hg : 0≤g) (hAg : g*h≤A)
    (hsmall : h^2/4+A*h≤1/8) :
    1/2 ≤ (((1-(((e^2 : ℝ) : ℂ)+(2*e*g : ℝ)*Complex.I)/
       ((n : ℝ)/h^2+g^2 : ℝ))⁻¹)^n).re := by
  have hn0 : (0 : ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hnne : (n : ℝ)≠0 := ne_of_gt hn0
  have hne : h≠0 := ne_of_gt hh
  have hb := perturbation_bound ((n : ℝ)/h^2) e g (by positivity) he hg
  have hm := mul_le_mul_of_nonneg_left hb (le_of_lt hn0)
  have heq : (n : ℝ)*((1/4+g)/((n : ℝ)/h^2)) = h^2/4+(g*h)*h  := by field_simp
  rw [heq] at hm
  have hw : (n : ℝ)*‖(((e^2 : ℝ) : ℂ)+(2*e*g : ℝ)*Complex.I)/((n : ℝ)/h^2+g^2 : ℝ)‖ ≤ 1/8 := by
    nlinarith [mul_le_mul_of_nonneg_right hAg (le_of_lt hh)]
  exact (inverse_power_positive n hn _ hw).2

open Filter Topology

theorem near_window_eventually (k : ℕ → ℕ) (hk : ∀ n, 1≤k n)
    (h : ℕ → ℝ) (hh : ∀ n, 0<h n) (ht : Tendsto h atTop (𝓝 0)) (A : ℝ) :
    ∀ᶠ n in atTop, ∀ e g : ℝ, |e|≤1/2 → 0≤g → g*h n≤A →
    1/2 ≤ (((1-(((e^2 : ℝ) : ℂ)+(2*e*g : ℝ)*Complex.I)/
       ((k n : ℝ)/(h n)^2+g^2 : ℝ))⁻¹)^(k n)).re := by
  have hs : Tendsto (fun n => (h n)^2/4+A*h n) atTop (𝓝 (0 : ℝ)) := by
    convert ((ht.pow 2).div_const 4).add (ht.const_mul A) using 1 <;> norm_num
  filter_upwards [hs.eventually_le_const (by norm_num : (0 : ℝ)<1/8)] with n hn
  intro e g he hg hAg
  exact near_window_positive (k n) (hk n) (h n) A e g (hh n) he hg hAg hn
end BranchNearRepair
#print axioms BranchNearRepair.near_window_eventually

namespace BranchNearRepair
lemma ratio_factorization (x e g : ℝ) (hx : 0<x) :
    (x : ℂ)/((x+g^2-e^2 : ℝ)-(2*e*g : ℝ)*Complex.I) =
    (x/(x+g^2) : ℝ)*(1-(((e^2 : ℝ) : ℂ)+(2*e*g : ℝ)*Complex.I)/(x+g^2 : ℝ))⁻¹ := by
  have hd : (x+g^2 : ℝ)≠0 := ne_of_gt (by positivity)
  have hdC : ((x+g^2 : ℝ) : ℂ)≠0 := by exact_mod_cast hd
  have heq : (1-(((e^2 : ℝ) : ℂ)+(2*e*g : ℝ)*Complex.I)/(x+g^2 : ℝ)) =
      ((x+g^2-e^2 : ℝ)-(2*e*g : ℝ)*Complex.I)/(x+g^2 : ℝ) := by
    rw [one_sub_div hdC]
    congr 1
    push_cast
    ring
  rw [heq, inv_div, Complex.ofReal_div]
  field_simp

theorem near_ratio_lower (n : ℕ) (hn : 1≤n) (h A e g : ℝ)
    (hh : 0<h) (he : |e|≤1/2) (hg : 0≤g) (hAg : g*h≤A)
    (hsmall : h^2/4+A*h≤1/8) :
    (1/2)*(((n : ℝ)/h^2)/((n : ℝ)/h^2+g^2))^n ≤
    (((((n : ℝ)/h^2 : ℝ) : ℂ)/
      (((n : ℝ)/h^2+g^2-e^2 : ℝ)-(2*e*g : ℝ)*Complex.I))^n).re := by
  have hn0 : (0 : ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hp := near_window_positive n hn h A e g hh he hg hAg hsmall
  rw [ratio_factorization _ e g (by positivity), mul_pow]
  simp only [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hp (by positivity : 0≤(((n : ℝ)/h^2)/((n : ℝ)/h^2+g^2))^n)

lemma core_real_lower (n : ℕ) (hn : 1≤n) (h g : ℝ)
    (hh : 0<h) (hg : 0≤g) (hgh : g*h≤1) :
    Real.exp (-1) ≤ (((n : ℝ)/h^2)/((n : ℝ)/h^2+g^2))^n := by
  have hn0 : (0 : ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hne : h≠0 := ne_of_gt hh
  have hnne : (n : ℝ)≠0 := ne_of_gt hn0
  have ht : 0≤g^2*h^2/(n : ℝ) := by positivity
  have hpow := pow_le_pow_left₀ (by positivity : 0≤1+g^2*h^2/(n : ℝ))
    (by simpa [add_comm] using Real.add_one_le_exp (g^2*h^2/(n : ℝ))) n
  rw [← Real.exp_nat_mul] at hpow
  have he : (n : ℝ)*(g^2*h^2/(n : ℝ)) = (g*h)^2 := by field_simp
  rw [he] at hpow
  have hs : (g*h)^2≤1 := by nlinarith [mul_nonneg hg hh.le]
  have hle := hpow.trans (Real.exp_le_exp.mpr hs)
  have hdiv : ((n : ℝ)/h^2)/((n : ℝ)/h^2+g^2) = (1+g^2*h^2/(n : ℝ))⁻¹ := by field_simp
  rw [hdiv, inv_pow, Real.exp_neg]
  exact inv_anti₀ (by positivity) hle
end BranchNearRepair
#print axioms BranchNearRepair.near_ratio_lower
#print axioms BranchNearRepair.core_real_lower

namespace BranchNearRepair
open Filter Topology

theorem uniform_window_and_core (k : ℕ → ℕ) (hk : ∀ n, 1≤k n)
    (h : ℕ → ℝ) (hh : ∀ n, 0<h n) (ht : Tendsto h atTop (𝓝 0))
    (A : ℝ) (hA : 1≤A) :
    ∀ᶠ n in atTop, ∀ e g : ℝ, |e|≤1/2 → 0≤g → g*h n≤A →
    0 < (((((k n : ℝ)/(h n)^2 : ℝ) : ℂ)/
      (((k n : ℝ)/(h n)^2+g^2-e^2 : ℝ)-(2*e*g : ℝ)*Complex.I))^(k n)).re ∧
    (g*h n≤1 → Real.exp (-1)/2 ≤ (((((k n : ℝ)/(h n)^2 : ℝ) : ℂ)/
      (((k n : ℝ)/(h n)^2+g^2-e^2 : ℝ)-(2*e*g : ℝ)*Complex.I))^(k n)).re) := by
  have hs : Tendsto (fun n => (h n)^2/4+A*h n) atTop (𝓝 (0 : ℝ)) := by
    convert ((ht.pow 2).div_const 4).add (ht.const_mul A) using 1 <;> norm_num
  filter_upwards [hs.eventually_le_const (by norm_num : (0 : ℝ)<1/8)] with n hsmall
  intro e g he hg hAg
  have hn0 : (0 : ℝ)<k n := by exact_mod_cast (show 0<k n by have := hk n; omega)
  have hl := near_ratio_lower (k n) (hk n) (h n) A e g (hh n) he hg hAg hsmall
  constructor
  · apply lt_of_lt_of_le _ hl
    have hh0 := hh n
    positivity
  · intro hcore
    have hc := core_real_lower (k n) (hk n) (h n) g (hh n) hg hcore
    linarith
end BranchNearRepair



namespace BranchComposition
open Filter Topology
noncomputable def term (k : ℕ) (h e g : ℝ) : ℂ :=
  ((((k : ℝ)/h^2 : ℝ) : ℂ)/(((k : ℝ)/h^2+g^2-e^2 : ℝ)-(2*e*g : ℝ)*Complex.I))^k

theorem two_cutoff_exclusion {ι : Type*} [DecidableEq ι]
    (e g : ι → ℝ) (he : ∀ i, |e i|≤1/2) (hg : ∀ i, 0≤g i)
    (cut : ℝ → Finset ι) (hpref : ∀ T i, i∈cut T ↔ g i≤T)
    (C : ℝ) (hC : 0≤C)
    (hcount : ∀ T ≥ (1 : ℝ), ∀ F : Finset ι,
      (∀ i ∈ F, T≤g i ∧ g i<T+1) → (F.card : ℝ)≤C*Real.log (T+3))
    (k : ℕ → ℕ) (hk : ∀ n, 2≤k n)
    (h L : ℕ → ℝ) (hh : ∀ n, 0<h n) (hh1 : ∀ n, h n≤1)
    (hL : ∀ n, 1≤L n) (hlog : ∀ n, -Real.log (h n)≤L n)
    (ht : Tendsto h atTop (𝓝 0))
    (c : ℝ) (hc : 0<c)
    (hlower : ∀ᶠ n in atTop, c≤h n/L n*((cut (1/h n)).card : ℝ)) :
    ∀ᶠ n in atTop, Summable (fun i => term (k n) (h n) (e i) (g i)) ∧
      0<(∑' i, term (k n) (h n) (e i) (g i)).re := by
  classical
  let d : ℝ := c*Real.exp (-1)/4
  have hd : 0<d := by dsimp [d]; positivity
  let A : ℝ := 1+96*C/d
  have hA : 1≤A := by
    have hp : 0≤96*C/d := by positivity
    dsimp [A]
    linarith
  have hAd : 96*C/A^2<d := by
    have hid : d*A=d+96*C := by dsimp [A]; field_simp
    apply (div_lt_iff₀ (by positivity : 0<A^2)).2
    nlinarith [sq_nonneg (A-1)]
  have hw := BranchNearRepair.uniform_window_and_core k (fun n => by have := hk n; omega) h hh ht A hA
  filter_upwards [hw,hlower] with n hwin hlowcount
  let F := cut (A/h n)
  let G := cut (1/h n)
  let f : ι → ℂ := fun i => term (k n) (h n) (e i) (g i)
  have hF (i : ι) : i∈F ↔ g i≤A/h n := hpref _ _
  have hG (i : ι) : i∈G ↔ g i≤1/h n := hpref _ _
  have hsub : G⊆F := by
    intro i hi
    apply (hF i).2
    exact ((hG i).1 hi).trans (div_le_div_of_nonneg_right hA (hh n).le)
  have hhigh (i : {i // i∉F}) : A<g i*h n := by
    have hnot : ¬g i≤A/h n := by simpa only [← hF] using i.property
    exact (div_lt_iff₀ (hh n)).1 (lt_of_not_ge hnot)
  have hcountsub : ∀ T ≥ (1 : ℝ), ∀ S : Finset {i // i∉F},
      (∀ i ∈ S, T≤g i ∧ g i<T+1) → (S.card : ℝ)≤C*Real.log (T+3) := by
    intro T hT S hS
    have hb := hcount T hT (S.image Subtype.val) (by
      intro i hi
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
      exact hS j hj)
    simpa only [Finset.card_image_of_injective _ Subtype.val_injective] using hb
  have htail := BranchShellRepair.tail_from_unit_count (k n) (hk n) (h n) (L n) A C
    (hh n) (hh1 n) (hL n) hA hC (hlog n)
    (fun i : {i // i∉F} => e i) (fun i : {i // i∉F} => g i)
    (fun i => he i) (fun i => hg i) hhigh hcountsub
  change Summable (fun i : {i // i∉F} => f i) ∧
    h n/L n*(∑' i : {i // i∉F}, ‖f i‖)≤96*C/A^2 at htail
  have hsum : Summable f := F.summable_compl_iff.mp htail.1
  refine ⟨hsum, ?_⟩
  have hFn (i : ι) (hi : i∈F) : 0<(f i).re := by
    exact (hwin (e i) (g i) (he i) (hg i) ((le_div_iff₀ (hh n)).1 ((hF i).1 hi))).1
  have hGc (i : ι) (hi : i∈G) : Real.exp (-1)/2≤(f i).re := by
    exact (hwin (e i) (g i) (he i) (hg i)
      ((le_div_iff₀ (hh n)).1 ((hF i).1 (hsub hi)))).2
      ((le_div_iff₀ (hh n)).1 ((hG i).1 hi))
  have hcore : (G.card : ℝ)*(Real.exp (-1)/2)≤∑ i ∈ F, (f i).re := by
    calc
      _ = ∑ i ∈ G, Real.exp (-1)/2 := by simp
      _ ≤ ∑ i ∈ G, (f i).re := Finset.sum_le_sum hGc
      _ ≤ ∑ i ∈ F, (f i).re := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i hi _ => (hFn i hi).le)
  have hscale : 0<h n/L n := div_pos (hh n) (by linarith [hL n])
  have hmain := mul_le_mul_of_nonneg_left hcore hscale.le
  have hcscale := mul_le_mul_of_nonneg_right hlowcount (by positivity : 0≤Real.exp (-1)/2)
  change c≤h n/L n*(G.card : ℝ) at hlowcount
  have hmain' : 2*d≤h n/L n*(∑ i ∈ F, (f i).re) := by
    dsimp [d]
    change c*(Real.exp (-1)/2)≤(h n/L n*(G.card : ℝ))*(Real.exp (-1)/2) at hcscale
    nlinarith
  have htailnorm := norm_tsum_le_tsum_norm htail.1.norm
  have hre := Complex.re_le_norm (-(∑' i : {i // i∉F}, f i))
  simp only [Complex.neg_re, norm_neg] at hre
  have hneg : -(∑' i : {i // i∉F}, f i).re≤∑' i : {i // i∉F}, ‖f i‖ := hre.trans htailnorm
  have hnegscale := mul_le_mul_of_nonneg_left hneg hscale.le
  have htotal := congrArg Complex.re (hsum.sum_add_tsum_compl (s:=F))
  simp only [Complex.add_re, Complex.re_sum] at htotal
  change (∑ i ∈ F, (f i).re)+(∑' i : {i // i∉F}, f i).re = (∑' i, f i).re at htotal
  have htotscale := congrArg (fun t : ℝ => h n/L n*t) htotal
  rw [mul_add] at htotscale
  have hpositive : 0<h n/L n*(∑' i, f i).re := by linarith [htail.2]
  exact (mul_pos_iff_of_pos_left hscale).1 hpositive
end BranchComposition
#print axioms BranchComposition.two_cutoff_exclusion

theorem solution {ι : Type*} [DecidableEq ι]
    (e g : ι → ℝ) (he : ∀ i, |e i|≤1/2) (hg : ∀ i, 0≤g i)
    (cut : ℝ → Finset ι) (hpref : ∀ T i, i∈cut T ↔ g i≤T)
    (C : ℝ) (hC : 0≤C)
    (hcount : ∀ T ≥ (1 : ℝ), ∀ F : Finset ι,
      (∀ i ∈ F, T≤g i ∧ g i<T+1) → (F.card : ℝ)≤C*Real.log (T+3))
    (k : ℕ → ℕ) (hk : ∀ n, 2≤k n)
    (h L : ℕ → ℝ) (hh : ∀ n, 0<h n) (hh1 : ∀ n, h n≤1)
    (hL : ∀ n, 1≤L n) (hlog : ∀ n, -Real.log (h n)≤L n)
    (ht : Filter.Tendsto h Filter.atTop (nhds 0))
    (c : ℝ) (hc : 0<c)
    (hlower : ∀ᶠ n in Filter.atTop, c≤h n/L n*((cut (1/h n)).card : ℝ)) :
    ∀ᶠ n in Filter.atTop, Summable (fun i => (((((k n : ℝ)/(h n)^2 : ℝ) : ℂ)/(((k n : ℝ)/(h n)^2+(g i)^2-(e i)^2 : ℝ)-(2*e i*g i : ℝ)*Complex.I))^(k n))) ∧
      0<(∑' i, (((((k n : ℝ)/(h n)^2 : ℝ) : ℂ)/(((k n : ℝ)/(h n)^2+(g i)^2-(e i)^2 : ℝ)-(2*e i*g i : ℝ)*Complex.I))^(k n))).re := by
  simpa only [BranchComposition.term] using
    BranchComposition.two_cutoff_exclusion e g he hg cut hpref C hC hcount k hk h L hh hh1 hL hlog ht c hc hlower
#print axioms solution
