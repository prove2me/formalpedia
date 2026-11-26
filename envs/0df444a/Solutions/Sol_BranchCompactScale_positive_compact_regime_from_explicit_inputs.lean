-- Prove2me | solution 1 for BranchCompactScale.positive_compact_regime_from_explicit_inputs
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-18T09:13:14.95136+00:00
-- url     : https://prove2.me/submissions/436b3dbd-c99e-43b9-81a3-5d9f033e12ce

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

open Set Filter Topology
namespace CompactHeatPositivity
/-- A negative oscillatory contribution is dominated by the anchor divided by a squared pole. -/
theorem negative_atom_bound (a b a₀ lam : ℝ)
    (ha : 900000 ≤ a) (ha₀ : a₀ ≤ 10000) (hb : b^2 ≤ 2*a) (hl : 0 < lam) :
    -(Real.exp (-a₀*lam)/a^2) ≤ Real.exp (-a*lam)*Real.cos (b*lam) := by
  have ha0 : 0 < a := by linarith
  by_cases hcos : 0 ≤ Real.cos (b*lam)
  · exact le_trans (neg_nonpos.mpr (by positivity))
      (mul_nonneg (Real.exp_pos _).le hcos)
  have hc : Real.cos (b*lam) < 0 := lt_of_not_ge hcos
  have hphase : 2 < b^2*lam^2 := by
    have hh := Real.one_sub_sq_div_two_le_cos (x := b*lam)
    rw [mul_pow] at hh
    linarith
  have hlam2 : 1 < a*lam^2 := by
    have hh := mul_le_mul_of_nonneg_right hb (sq_nonneg lam)
    nlinarith
  let t := (a-a₀)*lam
  have hgap : a/2 ≤ a-a₀ := by linarith
  have ht : 0 ≤ t := mul_nonneg (by linarith : 0 ≤ a-a₀) hl.le
  have htlow : a*lam/2 ≤ t := by
    have hh := mul_le_mul_of_nonneg_right hgap hl.le
    dsimp [t]
    linarith
  have ht2 : a/4 ≤ t^2 := by
    have hh := sq_le_sq₀ (by positivity : 0 ≤ a*lam/2) ht |>.2 htlow
    have hh' := mul_le_mul_of_nonneg_left hlam2.le ha0.le
    nlinarith
  have hp4 : (a/4)^4 ≤ (t^2)^4 := pow_le_pow_left₀ (by positivity) ht2 4
  have hp8 : a^4/256 ≤ t^8 := by nlinarith [hp4]
  have hex := Real.pow_div_factorial_le_exp t ht 8
  norm_num at hex
  have hsq : (10321920 : ℝ) ≤ a^2 := by nlinarith
  have hexlower : a^2 ≤ Real.exp t := by
    have hh := mul_le_mul_of_nonneg_right hsq (sq_nonneg a)
    nlinarith [sq_nonneg a]
  have hsmall : Real.exp (-t) ≤ 1/a^2 := by
    rw [Real.exp_neg,one_div]
    exact inv_anti₀ (sq_pos_of_pos ha0) hexlower
  have hfact : Real.exp (-a*lam) = Real.exp (-a₀*lam)*Real.exp (-t) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [t]
    ring
  have hbound : Real.exp (-a*lam) ≤ Real.exp (-a₀*lam)/a^2 := by
    rw [hfact]
    simpa only [div_eq_mul_inv, mul_one, one_mul] using
      mul_le_mul_of_nonneg_left hsmall (Real.exp_pos (-a₀*lam)).le
  have hcoslow : -1 ≤ Real.cos (b*lam) := Real.neg_one_le_cos _
  nlinarith [mul_le_mul_of_nonneg_left hcoslow (Real.exp_pos (-a*lam)).le]
end CompactHeatPositivity

open Set Filter Topology
namespace CompactHeatCounting
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

theorem fiber_norm_bound {ι : Type*} (f : ι → ℝ) (bin : ι → ℕ) (N K : ℕ → ℝ)
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
end CompactHeatCounting
namespace CompactHeatCounting

theorem offline_inverse_square_bound {ι : Type*} (g e : ι → ℝ)
    (hg : ∀ i, 1000 < g i) (he : ∀ i, |e i| ≤ 1/2)
    (hcount : ∀ T ≥ (1000 : ℝ), ∀ F : Finset ι,
      (∀ i ∈ F, T ≤ g i ∧ g i < T+1) → (F.card : ℝ) ≤ 50*Real.log (T+3)) :
    Summable (fun i => 1/((g i)^2-(e i)^2)^2) ∧
      (∑' i, 1/((g i)^2-(e i)^2)^2) ≤ 1/2 := by
  classical
  let bin : ι → ℕ := fun i => ⌊g i-1000⌋₊
  have hb (i : ι) : 1000+(bin i : ℝ) ≤ g i ∧ g i < 1000+(bin i : ℝ)+1 := by
    have hlo := Nat.floor_le (show 0 ≤ g i-1000 by linarith [hg i])
    have hhi := Nat.lt_floor_add_one (g i-1000)
    change 1000+(⌊g i-1000⌋₊ : ℝ) ≤ g i ∧ g i < 1000+(⌊g i-1000⌋₊ : ℝ)+1
    constructor <;> linarith
  have ht (j : ℕ) : 1000 ≤ 1000+(j : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) j]
  have hc (F : Finset ι) (j : ℕ) : ((F.filter (fun i => bin i=j)).card : ℝ) ≤
      100*(1000+(j : ℝ)) := by
    have hh := hcount (1000+(j : ℝ)) (ht j) (F.filter (fun i => bin i=j)) (by
      intro i hi
      simpa only [(Finset.mem_filter.mp hi).2] using hb i)
    have hlog := Real.log_le_sub_one_of_pos (by positivity : 0 < 1000+(j : ℝ)+3)
    linarith [Nat.cast_nonneg (α := ℝ) j]
  have hden (i : ι) : (1000+(bin i : ℝ))^2/2 ≤ (g i)^2-(e i)^2 := by
    have he2 : (e i)^2 ≤ 1/4 := by have := abs_le.mp (he i); nlinarith
    have hg2 : (1000+(bin i : ℝ))^2 ≤ (g i)^2 :=
      sq_le_sq₀ (by positivity) (by linarith [hg i]) |>.2 (hb i).1
    nlinarith [sq_nonneg (1000+(bin i : ℝ)-1), ht (bin i)]
  have hden0 (i : ι) : 0 < (g i)^2-(e i)^2 :=
    lt_of_lt_of_le (by positivity) (hden i)
  have hf (i : ι) : ‖1/((g i)^2-(e i)^2)^2‖ ≤ 4/(1000+(bin i : ℝ))^4 := by
    rw [Real.norm_of_nonneg (by positivity)]
    have hh := one_div_le_one_div_of_le
      (by positivity : 0 < ((1000+(bin i : ℝ))^2/2)^2)
      (sq_le_sq₀ (by positivity) (hden0 i).le |>.2 (hden i))
    calc
      _ ≤ 1/((1000+(bin i : ℝ))^2/2)^2 := hh
      _ = _ := by field_simp; ring
  have hcube := cube_sum_bound 1000 1 (by norm_num) (by norm_num)
  have heq : (fun j : ℕ => (100*(1000+(j : ℝ)))*(4/(1000+(j : ℝ))^4)) =
      (fun j : ℕ => 400*(1/(1000+(j : ℝ)*1)^3)) := by
    funext j
    field_simp
    ring
  have hseries : Summable (fun j : ℕ => (100*(1000+(j : ℝ)))*(4/(1000+(j : ℝ))^4)) := by
    rw [heq]
    exact hcube.1.mul_left 400
  have hh := fiber_norm_bound (fun i => 1/((g i)^2-(e i)^2)^2) bin
    (fun j => 100*(1000+(j : ℝ))) (fun j => 4/(1000+(j : ℝ))^4)
    (fun j => by positivity) (fun j => by positivity) hc hf hseries
  refine ⟨hh.1,?_⟩
  have hnorm : (fun i => ‖1/((g i)^2-(e i)^2)^2‖) = (fun i => 1/((g i)^2-(e i)^2)^2) := by
    funext i
    exact Real.norm_of_nonneg (by positivity)
  rw [hnorm] at hh
  rw [heq,tsum_mul_left] at hh
  have hm := mul_le_mul_of_nonneg_left hcube.2 (by norm_num : (0 : ℝ) ≤ 400)
  norm_num at hm
  linarith [hh.2]
end CompactHeatCounting

namespace CompactHeatPositivity

theorem heat_sum_positive {ι : Type*} (g e : ι → ℝ)
    (hg : ∀ i, 2 ≤ g i) (he : ∀ i, |e i| ≤ 1/2)
    (verified : ∀ i, g i ≤ 1000 → e i = 0)
    (anchor : ∃ i, g i ≤ 100)
    (hs : Summable (fun i => ((g i)^2-(e i)^2)⁻¹))
    (hcount : ∀ T ≥ (1000 : ℝ), ∀ F : Finset ι,
      (∀ i ∈ F, T ≤ g i ∧ g i < T+1) → (F.card : ℝ) ≤ 50*Real.log (T+3))
    (lam : ℝ) (hl : 0 < lam) :
    0 < ∑' i, Real.exp (-((g i)^2-(e i)^2)*lam)*Real.cos ((2*e i*g i)*lam) := by
  classical
  let a : ι → ℝ := fun i => (g i)^2-(e i)^2
  let H : ι → ℝ := fun i => Real.exp (-a i*lam)*Real.cos ((2*e i*g i)*lam)
  let O : Set ι := {i | e i ≠ 0}
  have he2 (i : ι) : (e i)^2 ≤ 1/4 := by have := abs_le.mp (he i); nlinarith
  have ha (i : ι) : 1 ≤ a i := by dsimp [a]; nlinarith [hg i, he2 i]
  have ha0 (i : ι) : 0 < a i := lt_of_lt_of_le (by norm_num) (ha i)
  have hheat : Summable H := by
    apply (hs.mul_left lam⁻¹).of_norm_bounded
    intro i
    have hx : 0 < a i*lam := mul_pos (ha0 i) hl
    have hex : a i*lam ≤ Real.exp (a i*lam) := by linarith [Real.add_one_le_exp (a i*lam)]
    have hb : Real.exp (-a i*lam) ≤ lam⁻¹*(a i)⁻¹ := by
      rw [neg_mul, Real.exp_neg]
      have hh := inv_anti₀ hx hex
      simpa only [mul_inv_rev] using hh
    dsimp [H]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (Real.exp_pos _).le).trans
      (by simpa only [mul_one] using hb)
  have hoffhigh (i : O) : 1000 < g i := by
    by_contra hh
    exact i.property (verified i (le_of_not_gt hh))
  have hoffcount : ∀ T ≥ (1000 : ℝ), ∀ F : Finset O,
      (∀ i ∈ F, T ≤ g i ∧ g i < T+1) → (F.card : ℝ) ≤ 50*Real.log (T+3) := by
    intro T hT F hF
    have hh := hcount T hT (F.map (Function.Embedding.subtype _)) (by
      intro i hi
      obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hi
      exact hF v hv)
    simpa using hh
  have hw := CompactHeatCounting.offline_inverse_square_bound (fun i : O => g i)
    (fun i : O => e i) hoffhigh (fun i => he i) hoffcount
  obtain ⟨i₀,hi₀⟩ := anchor
  have he₀ : e i₀ = 0 := verified i₀ (by linarith)
  have hi₀' : i₀ ∈ Oᶜ := by simpa [O] using he₀
  let A : ℝ := Real.exp (-(g i₀)^2*lam)
  have hA : 0 < A := Real.exp_pos _
  have hofflower (i : O) : -A/(a i)^2 ≤ H i := by
    have haoff : 900000 ≤ a i := by dsimp [a]; nlinarith [hoffhigh i,he2 i]
    have haanchor : (g i₀)^2 ≤ 10000 := by nlinarith [hg i₀]
    have hb : (2*e i*g i)^2 ≤ 2*a i := by
      have hh := mul_le_mul_of_nonneg_right (he2 i) (sq_nonneg (g i))
      dsimp [a]
      nlinarith [hg i,he2 i]
    simpa only [A,H,neg_div] using negative_atom_bound (a i) (2*e i*g i) ((g i₀)^2) lam haoff haanchor hb hl
  have hwoff : Summable (fun i : O => -A/(a i)^2) := by
    simpa only [a,mul_one_div] using hw.1.mul_left (-A)
  have hoff := hwoff.tsum_le_tsum hofflower (hheat.subtype (fun i => i ∈ O))
  have heq : (∑' i : O, -A/(a i)^2) = -A*(∑' i : O, 1/(a i)^2) := by
    simp only [div_eq_mul_inv,mul_one,one_mul,tsum_mul_left]
  rw [heq] at hoff
  have hwA : -A/2 ≤ -A*(∑' i : O, 1/(a i)^2) := by
    have hh := mul_le_mul_of_nonpos_left hw.2 (by linarith : -A ≤ 0)
    simpa only [a,mul_one_div] using hh
  have hcritical : A ≤ ∑' i : ↥(Oᶜ), H i := by
    have hh := (hheat.subtype (fun i => i ∈ Oᶜ)).sum_le_tsum {⟨i₀,hi₀'⟩} (by
      intro i hi
      have hei : e i = 0 := Classical.not_not.mp i.property
      dsimp [H]
      simp only [hei,mul_zero,zero_mul,Real.cos_zero,mul_one]
      exact (Real.exp_pos _).le)
    simpa [H,a,he₀,A] using hh
  have hsplit := hheat.tsum_subtype_add_tsum_subtype_compl O
  change (∑' i : O, H i)+(∑' i : ↥(Oᶜ), H i) = ∑' i, H i at hsplit
  change 0 < ∑' i, H i
  linarith
end CompactHeatPositivity

namespace BranchCompactScale
open Set Filter Topology

theorem exp_family_summable {ι : Type*} (B : ι → ℂ)
    (hB : ∀ i, 0 < (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (L : ℝ) (hL : 0 < L) : Summable (fun i => Complex.exp (-(L : ℂ)*B i)) := by
  apply (hs.mul_left L⁻¹).of_norm_bounded
  intro i
  rw [Complex.norm_exp]
  have hre : (-(L : ℂ)*B i).re = -(L*(B i).re) := by simp [Complex.mul_re]
  rw [hre,Real.exp_neg]
  have hh : L*(B i).re ≤ Real.exp (L*(B i).re) := by
    linarith [Real.add_one_le_exp (L*(B i).re)]
  have hi := inv_anti₀ (mul_pos hL (hB i)) hh
  simpa only [mul_inv_rev,mul_comm] using hi

theorem compact_scale_eventually_positive {ι : Type*} (g e : ι → ℝ)
    (hg : ∀ i, 2 ≤ g i) (he : ∀ i, |e i| ≤ 1/2)
    (verified : ∀ i, g i ≤ 1000 → e i = 0)
    (anchor : ∃ i, g i ≤ 100)
    (hs : Summable (fun i => ((g i)^2-(e i)^2)⁻¹))
    (hcount : ∀ T ≥ (1000 : ℝ), ∀ F : Finset ι,
      (∀ i ∈ F, T ≤ g i ∧ g i < T+1) → (F.card : ℝ) ≤ 50*Real.log (T+3))
    (k : ℕ → ℕ) (hk : Tendsto k atTop atTop)
    (lam : ℕ → ℝ) (L : ℝ) (hL : 0 < L) (hlam : Tendsto lam atTop (𝓝 L)) :
    ∀ᶠ j : ℕ in atTop, 0 <
      (∑' i, ((1+(lam j : ℂ)*
        ((((g i)^2-(e i)^2 : ℝ) : ℂ)-(2*e i*g i : ℝ)*Complex.I)/(k j : ℂ))⁻¹)^(k j)).re := by
  let B : ι → ℂ := fun i => (((g i)^2-(e i)^2 : ℝ) : ℂ)-(2*e i*g i : ℝ)*Complex.I
  have hre (i : ι) : (B i).re = (g i)^2-(e i)^2 := by simp [B,Complex.mul_re,pow_two]
  have hb : ∀ i, 0 < (B i).re := by
    intro i
    rw [hre]
    have he2 : (e i)^2 ≤ 1/4 := by have := abs_le.mp (he i); nlinarith
    nlinarith [hg i]
  have hs' : Summable (fun i => (B i).re⁻¹) := by simpa only [hre] using hs
  have hl := CompactPoleLimit.moving_pole_sum_limit B hb hs' k hk lam L hL hlam
  have hreal := (Complex.continuous_re.tendsto _).comp hl
  have hex := exp_family_summable B hb hs' L hL
  have hsum := Complex.reCLM.map_tsum hex
  change (∑' i, Complex.exp (-(L : ℂ)*B i)).re = ∑' i, (Complex.exp (-(L : ℂ)*B i)).re at hsum
  have hterm (i : ι) : (Complex.exp (-(L : ℂ)*B i)).re =
      Real.exp (-((g i)^2-(e i)^2)*L)*Real.cos ((2*e i*g i)*L) := by
    rw [Complex.exp_re]
    have hr : (-(L : ℂ)*B i).re = -((g i)^2-(e i)^2)*L := by
      simp [B,Complex.mul_re,pow_two]
      ring
    have hi : (-(L : ℂ)*B i).im = (2*e i*g i)*L := by
      simp [B,Complex.mul_im,pow_two,Complex.mul_re]
      ring
    rw [hr,hi]
  simp only [hterm] at hsum
  have hpos : 0 < (∑' i, Complex.exp (-(L : ℂ)*B i)).re := by
    rw [hsum]
    exact CompactHeatPositivity.heat_sum_positive g e hg he verified anchor hs hcount L hL
  exact hreal.eventually (Ioi_mem_nhds hpos)
end BranchCompactScale

theorem solution {ι : Type*} (g e : ι → ℝ)
    (hg : ∀ i, 2 ≤ g i) (he : ∀ i, |e i| ≤ 1/2)
    (verified : ∀ i, g i ≤ 1000 → e i = 0)
    (anchor : ∃ i, g i ≤ 100)
    (hs : Summable (fun i => ((g i)^2-(e i)^2)⁻¹))
    (hcount : ∀ T ≥ (1000 : ℝ), ∀ F : Finset ι,
      (∀ i ∈ F, T ≤ g i ∧ g i < T+1) → (F.card : ℝ) ≤ 50*Real.log (T+3))
    (k : ℕ → ℕ) (hk : Tendsto k atTop atTop)
    (lam : ℕ → ℝ) (L : ℝ) (hL : 0 < L) (hlam : Tendsto lam atTop (𝓝 L)) :
    ∀ᶠ j : ℕ in atTop, 0 <
      (∑' i, ((1+(lam j : ℂ)*
        ((((g i)^2-(e i)^2 : ℝ) : ℂ)-(2*e i*g i : ℝ)*Complex.I)/(k j : ℂ))⁻¹)^(k j)).re := by
  exact BranchCompactScale.compact_scale_eventually_positive g e hg he verified anchor hs hcount k hk lam L hL hlam
