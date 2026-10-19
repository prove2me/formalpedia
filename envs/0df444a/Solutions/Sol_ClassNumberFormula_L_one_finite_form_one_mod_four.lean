-- Prove2me | solution 1 for ClassNumberFormula.L_one_finite_form_one_mod_four
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T00:50:15.909604+00:00
-- url     : https://prove2.me/submissions/a253d57a-fd9e-4449-b862-f737bfd8e7e7

import Mathlib

section
open Complex Filter Topology Finset Real

namespace LOA

/-- Summation by parts identity. -/
lemma parts (f : ℕ → ℝ) (z : ℕ → ℂ) (N : ℕ) : ∀ K, N ≤ K →
    ∑ i ∈ Ico N K, (f i : ℂ) * z i =
      (f K : ℂ) * (∑ i ∈ range K, z i) - (f N : ℂ) * (∑ i ∈ range N, z i) +
        ∑ i ∈ Ico N K, ((f i - f (i + 1) : ℝ) : ℂ) * (∑ j ∈ range (i + 1), z j) := by
  intro K hK
  induction K, hK using Nat.le_induction with
  | base => simp
  | succ K hK ih =>
    rw [sum_Ico_succ_top hK, ih, sum_Ico_succ_top hK, sum_range_succ]
    push_cast
    ring

lemma tail_fin {z : ℕ → ℂ} {b : ℝ} (hz : ∀ n, ‖∑ i ∈ range n, z i‖ ≤ b) {f : ℕ → ℝ}
    (hf : Antitone f) (hf0 : ∀ n, 0 ≤ f n) (N K : ℕ) (hNK : N ≤ K) :
    ‖∑ i ∈ Ico N K, (f i : ℂ) * z i‖ ≤ 2 * b * f N := by
  have hb : 0 ≤ b := le_trans (norm_nonneg _) (hz 0)
  rw [parts f z N K hNK]
  have h1 : ‖(f K : ℂ) * (∑ i ∈ range K, z i)‖ ≤ f K * b := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hf0 K)]
    exact mul_le_mul_of_nonneg_left (hz K) (hf0 K)
  have h2 : ‖(f N : ℂ) * (∑ i ∈ range N, z i)‖ ≤ f N * b := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hf0 N)]
    exact mul_le_mul_of_nonneg_left (hz N) (hf0 N)
  have h3 : ‖∑ i ∈ Ico N K, ((f i - f (i + 1) : ℝ) : ℂ) * (∑ j ∈ range (i + 1), z j)‖ ≤
      ∑ i ∈ Ico N K, (f i - f (i + 1)) * b := by
    refine (norm_sum_le _ _).trans (sum_le_sum fun i _ => ?_)
    have hi : 0 ≤ f i - f (i + 1) := sub_nonneg.2 (hf (Nat.le_succ i))
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hi]
    exact mul_le_mul_of_nonneg_left (hz _) hi
  have h4 : ∑ i ∈ Ico N K, (f i - f (i + 1)) * b = (f N - f K) * b := by
    rw [← sum_mul, sum_Ico_eq_sum_range]
    congr 1
    have h := sum_range_sub' (fun i => f (N + i)) (K - N)
    simp only [Nat.add_zero, Nat.add_sub_cancel' hNK] at h
    exact h
  have hKN : f K ≤ f N := hf hNK
  calc _ ≤ ‖(f K : ℂ) * (∑ i ∈ range K, z i) - (f N : ℂ) * (∑ i ∈ range N, z i)‖ +
        ‖∑ i ∈ Ico N K, ((f i - f (i + 1) : ℝ) : ℂ) * (∑ j ∈ range (i + 1), z j)‖ := norm_add_le _ _
    _ ≤ (f K * b + f N * b) + (f N - f K) * b := by
        gcongr
        · exact (norm_sub_le _ _).trans (add_le_add h1 h2)
        · exact h3.trans h4.le
    _ = 2 * b * f N := by ring

lemma tail_lim {z : ℕ → ℂ} {b : ℝ} (hz : ∀ n, ‖∑ i ∈ range n, z i‖ ≤ b) {f : ℕ → ℝ}
    (hf : Antitone f) (hf0 : ∀ n, 0 ≤ f n) {T : ℂ}
    (hT : Tendsto (fun K => ∑ i ∈ range K, (f i : ℂ) * z i) atTop (𝓝 T)) (N : ℕ) :
    ‖T - ∑ i ∈ range N, (f i : ℂ) * z i‖ ≤ 2 * b * f N := by
  have h : Tendsto (fun K => ‖∑ i ∈ range K, (f i : ℂ) * z i - ∑ i ∈ range N, (f i : ℂ) * z i‖)
      atTop (𝓝 ‖T - ∑ i ∈ range N, (f i : ℂ) * z i‖) :=
    (hT.sub_const _).norm
  refine le_of_tendsto h ?_
  filter_upwards [eventually_ge_atTop N] with K hK
  rw [← sum_range_add_sum_Ico _ hK, add_sub_cancel_left]
  exact tail_fin hz hf hf0 N K hK

/-- Continuity of a Dirichlet series with bounded partial sums at `s = 1` (from the right). -/
lemma ds_tendsto {z : ℕ → ℂ} {b : ℝ} (hz : ∀ n, ‖∑ i ∈ range n, z i‖ ≤ b) {l : ℂ}
    (hl : Tendsto (fun K => ∑ i ∈ range K, ((((i:ℝ) + 1) ^ (-(1 : ℝ)) : ℝ) : ℂ) * z i) atTop (𝓝 l))
    (F : ℝ → ℂ)
    (hF : ∀ σ : ℝ, 1 < σ → HasSum (fun i : ℕ => ((((i:ℝ) + 1) ^ (-σ) : ℝ) : ℂ) * z i) (F σ)) :
    Tendsto F (𝓝[>] 1) (𝓝 l) := by
  have hb : 0 ≤ b := le_trans (norm_nonneg _) (hz 0)
  have anti : ∀ σ : ℝ, 0 ≤ σ → Antitone fun i : ℕ => (i + 1 : ℝ) ^ (-σ) := by
    intro σ hσ i j hij
    apply Real.rpow_le_rpow_of_nonpos (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1)
      (by linarith)
  have nn : ∀ σ : ℝ, ∀ i : ℕ, 0 ≤ (i + 1 : ℝ) ^ (-σ) := fun σ i => by positivity
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 4 * b / (N + 1) < ε / 2 := by
    obtain ⟨N, hN⟩ := exists_nat_gt (8 * b / ε)
    refine ⟨N, ?_⟩
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hε] at hN
    nlinarith
  -- continuity of the finite sum
  have hc : Continuous fun σ : ℝ => ∑ i ∈ range N, ((((i:ℝ) + 1) ^ (-σ) : ℝ) : ℂ) * z i := by
    refine continuous_finsetSum _ fun i _ => ?_
    refine (Complex.continuous_ofReal.comp ?_).mul continuous_const
    exact (Real.continuous_const_rpow (by positivity)).comp continuous_neg |>.congr (fun _ => rfl)
  have hcl := (hc.tendsto 1)
  rw [Metric.tendsto_nhds_nhds] at hcl
  obtain ⟨δ, hδ, hδ'⟩ := hcl (ε / 2) (by linarith)
  refine ⟨δ, hδ, fun σ hσ hd => ?_⟩
  have hσ1 : (1 : ℝ) < σ := hσ
  have t1 := tail_lim hz (anti σ (by linarith)) (nn σ) (hF σ hσ1).tendsto_sum_nat N
  have t2 := tail_lim hz (anti 1 zero_le_one) (nn 1) hl N
  have hNσ : (N + 1 : ℝ) ^ (-σ) ≤ (N + 1 : ℝ) ^ (-(1 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have h1 : (N + 1 : ℝ) ^ (-(1 : ℝ)) = 1 / (N + 1) := by
    rw [Real.rpow_neg_one]; ring
  have hfin := hδ' hd
  rw [dist_eq_norm] at hfin ⊢
  have key : F σ - l = (F σ - ∑ i ∈ range N, ((((i:ℝ) + 1) ^ (-σ) : ℝ) : ℂ) * z i) +
      (∑ i ∈ range N, ((((i:ℝ) + 1) ^ (-σ) : ℝ) : ℂ) * z i -
        ∑ i ∈ range N, ((((i:ℝ) + 1) ^ (-(1:ℝ)) : ℝ) : ℂ) * z i) -
      (l - ∑ i ∈ range N, ((((i:ℝ) + 1) ^ (-(1:ℝ)) : ℝ) : ℂ) * z i) := by ring
  rw [key]
  have e1 : 2 * b * (N + 1 : ℝ) ^ (-σ) ≤ 2 * b * (1 / (N + 1)) := by
    rw [← h1]; exact mul_le_mul_of_nonneg_left hNσ (by linarith)
  have e2 : 2 * b * (N + 1 : ℝ) ^ (-(1:ℝ)) = 2 * b * (1 / (N + 1)) := by rw [h1]
  have e3 : 2 * b * (1 / (N + 1 : ℝ)) + 2 * b * (1 / (N + 1)) = 4 * b / (N + 1) := by ring
  calc _ ≤ ‖(F σ - ∑ i ∈ range N, ((((i:ℝ) + 1) ^ (-σ) : ℝ) : ℂ) * z i) +
      (∑ i ∈ range N, ((((i:ℝ) + 1) ^ (-σ) : ℝ) : ℂ) * z i -
        ∑ i ∈ range N, ((((i:ℝ) + 1) ^ (-(1:ℝ)) : ℝ) : ℂ) * z i)‖ +
      ‖l - ∑ i ∈ range N, ((((i:ℝ) + 1) ^ (-(1:ℝ)) : ℝ) : ℂ) * z i‖ := norm_sub_le _ _
    _ ≤ (2 * b * (N + 1 : ℝ) ^ (-σ) + ε / 2) + 2 * b * (N + 1 : ℝ) ^ (-(1:ℝ)) := by
      gcongr
      · exact (norm_add_le _ _).trans (add_le_add t1 hfin.le)
    _ < ε := by linarith


lemma geom_bound {e : ℂ} (he : ‖e‖ = 1) (he1 : e ≠ 1) (n : ℕ) :
    ‖∑ i ∈ range n, e ^ (i + 1)‖ ≤ 2 / ‖e - 1‖ := by
  have hne : e - 1 ≠ 0 := sub_ne_zero.2 he1
  have : ∑ i ∈ range n, e ^ (i + 1) = e * ((e ^ n - 1) / (e - 1)) := by
    rw [← geom_sum_eq he1 n, mul_sum]; simp [pow_succ, mul_comm]
  rw [this, norm_mul, he, one_mul, norm_div]
  gcongr
  calc ‖e ^ n - 1‖ ≤ ‖e ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_pow, he]; norm_num

lemma re_lt_one {e : ℂ} (he : ‖e‖ = 1) (he1 : e ≠ 1) : e.re < 1 := by
  by_contra h
  push Not at h
  have h2 : e.re ^ 2 + e.im ^ 2 = 1 := by
    have := Complex.sq_norm e
    rw [he, Complex.normSq_apply] at this; nlinarith
  have hre : e.re ≤ 1 := by
    have := Complex.re_le_norm e; rw [he] at this; exact this
  have h1 : e.re = 1 := le_antisymm hre h
  have him : e.im = 0 := by rw [h1] at h2; nlinarith
  exact he1 (Complex.ext (by simp [h1]) (by simp [him]))

lemma log_series {e : ℂ} (he : ‖e‖ = 1) (he1 : e ≠ 1) :
    Tendsto (fun K => ∑ i ∈ range K, ((((i:ℝ) + 1) ^ (-(1 : ℝ)) : ℝ) : ℂ) * e ^ (i + 1)) atTop
      (𝓝 (-log (1 - e))) := by
  set f : ℕ → ℝ := fun i => ((i:ℝ) + 1) ^ (-(1 : ℝ)) with hf
  have anti : Antitone f := by
    intro i j hij
    apply Real.rpow_le_rpow_of_nonpos (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1)
      (by norm_num)
  have f0 : Tendsto f atTop (𝓝 0) := by
    have : f = fun i : ℕ => 1 / ((i : ℝ) + 1) := by
      funext i; simp [hf, Real.rpow_neg_one]
    rw [this]; exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hc := anti.cauchySeq_series_mul_of_tendsto_zero_of_bounded f0 (geom_bound he he1)
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hc
  simp_rw [Complex.real_smul] at hl
  have habel := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt hl
  -- identify the power series
  have hid : ∀ r : ℝ, 0 < r → r < 1 →
      ∑' n, (f n : ℂ) * e ^ (n + 1) * (r : ℂ) ^ n = -log (1 - (r : ℂ) * e) / r := by
    intro r hr0 hr1
    have hz : ‖(r : ℂ) * e‖ < 1 := by
      rw [norm_mul, he, mul_one, Complex.norm_real, Real.norm_of_nonneg hr0.le]; exact hr1
    have hs := (hasSum_taylorSeries_neg_log' hz).div_const (r : ℂ)
    refine (HasSum.tsum_eq ?_)
    have hr : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
    have heq : (fun n : ℕ => (f n : ℂ) * e ^ (n + 1) * (r : ℂ) ^ n) =
        (fun n : ℕ => ((r : ℂ) * e) ^ (n + 1) / ((n : ℂ) + 1) / (r : ℂ)) := by
      funext n
      simp only [hf]
      rw [Complex.ofReal_cpow (by positivity)]
      push_cast
      rw [cpow_neg_one]
      field_simp
      ring
    rw [heq]; exact hs
  have hlim : Tendsto (fun z : ℂ => -log (1 - z * e) / z) ((𝓝[<] (1 : ℝ)).map ofReal)
      (𝓝 (-log (1 - e))) := by
    have hslit : 1 - e ∈ slitPlane := by
      left; simp only [sub_re, one_re]; linarith [re_lt_one he he1]
    have hca : ContinuousAt (fun z : ℂ => -log (1 - z * e) / z) 1 := by
      refine ContinuousAt.div ?_ continuousAt_id one_ne_zero
      refine ContinuousAt.neg ?_
      refine ContinuousAt.comp (g := Complex.log) ?_ (by fun_prop)
      simpa using continuousAt_clog hslit
    have := hca.tendsto
    simp only [one_mul, div_one] at this
    refine this.mono_left ?_
    refine (Filter.map_mono nhdsWithin_le_nhds).trans ?_
    rw [← Complex.ofReal_one]; exact Complex.continuous_ofReal.continuousAt
  have hev : (fun z : ℂ => ∑' n, (f n : ℂ) * e ^ (n + 1) * z ^ n) =ᶠ[(𝓝[<] (1 : ℝ)).map ofReal]
      (fun z : ℂ => -log (1 - z * e) / z) := by
    rw [Filter.EventuallyEq, Filter.eventually_map]
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
    exact hid r hr.1 hr.2
  have := tendsto_nhds_unique habel (hlim.congr' hev.symm)
  rw [← this]; exact hl

/-- Value of the exponential zeta function at `s = 1`. -/
theorem expZeta_one (x : ℝ) (hx : cexp (2 * π * I * x) ≠ 1) :
    HurwitzZeta.expZeta x 1 = -log (1 - cexp (2 * π * I * x)) := by
  set e := cexp (2 * π * I * x) with he_def
  have he : ‖e‖ = 1 := by
    rw [he_def, show 2 * π * I * x = ((2 * π * x : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hF : ∀ σ : ℝ, 1 < σ → HasSum (fun i : ℕ => ((((i:ℝ) + 1) ^ (-σ) : ℝ) : ℂ) * e ^ (i + 1))
      (HurwitzZeta.expZeta x σ) := by
    intro σ hσ
    have h := HurwitzZeta.hasSum_expZeta_of_one_lt_re x (s := (σ : ℂ)) (by simpa using hσ)
    rw [← hasSum_nat_add_iff' 1] at h
    have h0 : (0 : ℂ) ^ (σ : ℂ) = 0 := Complex.zero_cpow (by exact_mod_cast (by linarith : σ ≠ 0))
    simp only [range_one, sum_singleton, Nat.cast_zero, mul_zero, Complex.exp_zero, h0,
      div_zero, sub_zero] at h
    have heq : (fun i : ℕ => ((((i:ℝ) + 1) ^ (-σ) : ℝ) : ℂ) * e ^ (i + 1)) =
        (fun n : ℕ => cexp (2 * π * I * x * ((n + 1 : ℕ) : ℂ)) / ((n + 1 : ℕ) : ℂ) ^ (σ : ℂ)) := by
      funext i
      rw [Complex.ofReal_cpow (by positivity), he_def, ← Complex.exp_nat_mul]
      push_cast
      rw [cpow_neg, div_eq_inv_mul]
      congr 2
      ring
    rw [heq]; exact h
  have h1 := ds_tendsto (geom_bound he (by simpa [he_def] using hx)) (log_series he hx)
    (fun σ => HurwitzZeta.expZeta x σ) hF
  have hx0 : ((x : ℝ) : UnitAddCircle) ≠ 0 := by
    intro h0
    rw [AddCircle.coe_eq_zero_iff] at h0
    obtain ⟨n, hn⟩ := h0
    apply hx
    rw [he_def, ← hn]
    simp only [zsmul_eq_mul, mul_one]
    rw [show 2 * π * I * (n : ℝ) = n * (2 * π * I) by push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I n
  have h2 : Tendsto (fun σ : ℝ => HurwitzZeta.expZeta x σ) (𝓝[>] 1) (𝓝 (HurwitzZeta.expZeta x 1)) := by
    have hc := (HurwitzZeta.differentiableAt_expZeta (x : UnitAddCircle) 1 (Or.inr hx0)).continuousAt
    refine (hc.tendsto.comp ?_)
    refine (Complex.continuous_ofReal.tendsto' 1 1 (by simp)).mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique h2 h1

end LOA

end

section
open Complex Filter Topology Finset Real

namespace LOB

lemma exp_even (N : ℤ) : cexp (π * I * (2 * N)) = 1 := by
  rw [show π * I * (2 * (N : ℂ)) = N * (2 * π * I) by ring]
  exact Complex.exp_int_mul_two_pi_mul_I N

/-- One residue class of the theta series, via the functional equation. -/
lemma class_hasSum (c : ℕ) (hc : 0 < c) (a : ℤ) (ha : Even ((c : ℤ) * a)) (w : ℂ) (hw : 0 < w.im)
    (k : ℕ) :
    HasSum (fun m : ℤ => jacobiTheta₂_term ((c : ℤ) * m + k) 0 ((a : ℂ) / c + w))
      (cexp (π * I * (k : ℂ) ^ 2 * a / c) *
        (1 / (-I * ((c : ℂ) ^ 2 * w)) ^ (1 / 2 : ℂ) * jacobiTheta₂ ((k : ℂ) / c) (-1 / ((c : ℂ) ^ 2 * w)))) := by
  obtain ⟨j, hj⟩ := ha
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  set T : ℂ := (c : ℂ) ^ 2 * w with hT
  set β : ℂ := (k : ℂ) / c with hβ
  have hTim : 0 < T.im := by
    have : T.im = (c : ℝ) ^ 2 * w.im := by rw [hT]; simp [pow_two, Complex.mul_im]
    rw [this]; exact mul_pos (by positivity) hw
  have hT0 : T ≠ 0 := fun h => by rw [h] at hTim; simp at hTim
  have h1 := hasSum_jacobiTheta₂_term (T * β) hTim
  have hFE := jacobiTheta₂_functional_equation (T * β) T
  have hTβ : T * β / T = β := by field_simp
  have hTβ2 : -π * I * (T * β) ^ 2 / T = -(π * I * T * β ^ 2) := by field_simp
  rw [hTβ, hTβ2] at hFE
  have h2 := h1.mul_left (cexp (π * I * (k : ℂ) ^ 2 * a / c) * cexp (π * I * T * β ^ 2))
  have e1 : (fun m : ℤ => jacobiTheta₂_term ((c : ℤ) * m + k) 0 ((a : ℂ) / c + w)) =
      (fun i => cexp (π * I * (k : ℂ) ^ 2 * a / c) * cexp (π * I * T * β ^ 2) *
        jacobiTheta₂_term i (T * β) T) := by
    funext m
    simp only [jacobiTheta₂_term]
    rw [← Complex.exp_add, ← Complex.exp_add]
    have : (2 : ℂ) * π * I * ((c : ℤ) * m + k : ℤ) * 0 + π * I * (((c : ℤ) * m + k : ℤ) : ℂ) ^ 2 *
        ((a : ℂ) / c + w) =
        (π * I * (k : ℂ) ^ 2 * a / c + π * I * T * β ^ 2 +
          (2 * π * I * m * (T * β) + π * I * m ^ 2 * T)) + π * I * (2 * (j * m ^ 2 + m * k * a : ℤ)) := by
      have hj' : ((c : ℤ) : ℂ) * a = j + j := by exact_mod_cast hj
      push_cast at hj' ⊢
      rw [hT, hβ]
      field_simp
      linear_combination ((m : ℂ) ^ 2 * c) * hj'
    rw [this, Complex.exp_add, exp_even, mul_one]
  have e2 : cexp (π * I * (k : ℂ) ^ 2 * a / c) * cexp (π * I * T * β ^ 2) * jacobiTheta₂ (T * β) T =
      cexp (π * I * (k : ℂ) ^ 2 * a / c) *
        (1 / (-I * T) ^ (1 / 2 : ℂ) * jacobiTheta₂ β (-1 / T)) := by
    rw [hFE]
    have : cexp (π * I * T * β ^ 2) * cexp (-(π * I * T * β ^ 2)) = 1 := by
      rw [← Complex.exp_add]; simp
    linear_combination (cexp (π * I * ↑k ^ 2 * ↑a / ↑c) * (1 / (-I * T) ^ (1 / 2 : ℂ)) *
      jacobiTheta₂ β (-1 / T)) * this
  rw [e1]; rw [e2] at h2; exact h2


/-- Splitting the theta series at `a/c + w` into residue classes mod `c`. -/
lemma split (c : ℕ) (hc : 0 < c) (a : ℤ) (ha : Even ((c : ℤ) * a)) (w : ℂ) (hw : 0 < w.im) :
    jacobiTheta₂ 0 ((a : ℂ) / c + w) = ∑ k ∈ range c, cexp (π * I * (k : ℂ) ^ 2 * a / c) *
        (1 / (-I * ((c : ℂ) ^ 2 * w)) ^ (1 / 2 : ℂ) * jacobiTheta₂ ((k : ℂ) / c) (-1 / ((c : ℂ) ^ 2 * w))) := by
  set τ := (a : ℂ) / c + w with hτ
  have hτim : 0 < τ.im := by
    have : ((a : ℂ) / c).im = 0 := by
      rw [show (a : ℂ) / c = ((a / c : ℝ) : ℂ) by push_cast; rfl]; exact Complex.ofReal_im _
    rw [hτ, Complex.add_im, this, zero_add]; exact hw
  set f : ℤ → ℂ := fun n => jacobiTheta₂_term n 0 τ with hf
  have hcz : (0 : ℤ) < c := by exact_mod_cast hc
  have hind : ∀ k ∈ range c, HasSum (fun n : ℤ => if n % (c : ℤ) = k then f n else 0)
      (cexp (π * I * (k : ℂ) ^ 2 * a / c) *
        (1 / (-I * ((c : ℂ) ^ 2 * w)) ^ (1 / 2 : ℂ) * jacobiTheta₂ ((k : ℂ) / c) (-1 / ((c : ℂ) ^ 2 * w)))) := by
    intro k hk
    have hk' : (k : ℤ) < c := by exact_mod_cast mem_range.1 hk
    have hinj : Function.Injective (fun m : ℤ => (c : ℤ) * m + k) := by
      intro x y hxy
      simp only [add_left_inj] at hxy
      exact mul_left_cancel₀ hcz.ne' hxy
    rw [← hinj.hasSum_iff]
    · convert class_hasSum c hc a ha w hw k using 1
      funext m
      simp only [Function.comp_apply, hf]
      rw [if_pos]
      rw [add_comm, Int.add_mul_emod_self_left]
      exact Int.emod_eq_of_lt (by positivity) hk'
    · intro n hn
      rw [if_neg]
      intro h
      apply hn
      refine ⟨n / c, ?_⟩
      simp only
      rw [← h]; have := Int.ediv_mul_add_emod n c; linarith [mul_comm (c : ℤ) (n / c)]
  have hsum := hasSum_sum hind
  have hfun : (fun n : ℤ => ∑ k ∈ range c, if n % (c : ℤ) = k then f n else 0) = f := by
    funext n
    have h0 : 0 ≤ n % (c : ℤ) := Int.emod_nonneg _ hcz.ne'
    have h1 : n % (c : ℤ) < c := Int.emod_lt_of_pos _ hcz
    rw [sum_eq_single (n % (c : ℤ)).toNat]
    · rw [if_pos (Int.toNat_of_nonneg h0).symm]
    · intro b _ hb
      rw [if_neg]
      intro h; apply hb; rw [h]; simp
    · intro h
      exfalso; apply h
      rw [mem_range]; omega
  rw [hfun] at hsum
  exact (hasSum_jacobiTheta₂_term 0 hτim).unique hsum


lemma theta_sub_one_le (β : ℝ) {τ : ℂ} (hτ : 0 < τ.im) :
    ‖jacobiTheta₂ β τ - 1‖ ≤ 2 / (1 - rexp (-π * τ.im)) * rexp (-π * τ.im) := by
  set y := τ.im with hy
  set G : ℤ → ℝ := fun n => rexp (-π * n ^ 2 * y) - if n = 0 then 1 else 0 with hG
  set g : ℤ → ℂ := fun n => jacobiTheta₂_term n β τ - if n = 0 then 1 else 0 with hg
  have hgs : HasSum g (jacobiTheta₂ β τ - 1) :=
    (hasSum_jacobiTheta₂_term (β : ℂ) hτ).sub (hasSum_ite_eq (0 : ℤ) (1 : ℂ))
  have hyτ : 0 < (I * (y : ℂ)).im := by simpa using hτ
  have hg's : HasSum (fun n : ℤ => ((G n : ℝ) : ℂ)) (jacobiTheta (I * y) - 1) := by
    rw [jacobiTheta_eq_jacobiTheta₂]
    have := (hasSum_jacobiTheta₂_term 0 hyτ).sub (hasSum_ite_eq (0 : ℤ) (1 : ℂ))
    have e : (fun n : ℤ => ((G n : ℝ) : ℂ)) =
        (fun b : ℤ => jacobiTheta₂_term b 0 (I * y) - if b = 0 then 1 else 0) := by
      funext n
      simp only [hG, jacobiTheta₂_term]
      push_cast
      congr 1
      · congr 1; ring_nf; rw [I_sq]; ring
      · split_ifs <;> simp
    rw [e]; exact this
  have hnorm : ∀ n, ‖g n‖ = G n := by
    intro n
    simp only [hg, hG]
    by_cases hn : n = 0
    · subst hn; simp [jacobiTheta₂_term]
    · rw [if_neg hn, if_neg hn, sub_zero, sub_zero, norm_jacobiTheta₂_term]
      simp [hy]
  have hGnn : ∀ n, 0 ≤ G n := fun n => by rw [← hnorm]; exact norm_nonneg _
  have hGs : Summable G := Complex.summable_ofReal.1 hg's.summable
  have h1 : ‖jacobiTheta₂ β τ - 1‖ ≤ ∑' n, G n := by
    rw [← hgs.tsum_eq]
    refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq (tsum_congr hnorm))
    exact (summable_congr hnorm).2 hGs
  have h2 : ∑' n, G n = ‖jacobiTheta (I * y) - 1‖ := by
    rw [← hg's.tsum_eq, ← Complex.ofReal_tsum, Complex.norm_real, Real.norm_of_nonneg (tsum_nonneg hGnn)]
  have h3 := norm_jacobiTheta_sub_one_le hyτ
  have h4 : (I * (y : ℂ)).im = y := by simp
  rw [h4] at h3
  linarith

lemma theta_near_one {ε : ℝ} (hε : 0 < ε) :
    ∃ Y : ℝ, 0 < Y ∧ ∀ β : ℝ, ∀ τ : ℂ, Y ≤ τ.im → ‖jacobiTheta₂ β τ - 1‖ ≤ ε := by
  have ht : Tendsto (fun y : ℝ => rexp (-π * y)) atTop (𝓝 0) := by
    have := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop Real.pi_pos)
    refine this.congr fun y => ?_
    simp [neg_mul]
  have hev := (ht.eventually (gt_mem_nhds (show (0 : ℝ) < min (1 / 2) (ε / 4) by positivity))).and
    (eventually_gt_atTop 0)
  obtain ⟨Y, hY⟩ := hev.exists_forall_of_atTop
  refine ⟨Y, (hY Y le_rfl).2, fun β τ hτ => ?_⟩
  have hτ0 : 0 < τ.im := lt_of_lt_of_le (hY Y le_rfl).2 hτ
  refine (theta_sub_one_le β hτ0).trans ?_
  have hE := (hY τ.im hτ).1
  set E := rexp (-π * τ.im)
  have hE0 : 0 < E := Real.exp_pos _
  have hE1 : E < 1 / 2 := lt_of_lt_of_le hE (min_le_left _ _)
  have hE2 : E < ε / 4 := lt_of_lt_of_le hE (min_le_right _ _)
  rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
  nlinarith


lemma cpow_ofReal_mul' {t : ℝ} (ht : 0 < t) {X : ℂ} (hX : X ≠ 0) (y : ℂ) :
    ((t : ℂ) * X) ^ y = (t : ℂ) ^ y * X ^ y := by
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  rw [cpow_def_of_ne_zero (mul_ne_zero ht' hX), cpow_def_of_ne_zero ht', cpow_def_of_ne_zero hX,
    Complex.log_ofReal_mul ht hX, ← Complex.exp_add, Complex.ofReal_log ht.le]
  ring_nf

lemma im_formula (c : ℕ) (hc : 0 < c) {t : ℝ} (ht : 0 < t) {h : ℂ} (hh : h ≠ 0) :
    (-1 / ((c : ℂ) ^ 2 * (I * t * h))).im = h.re / ((c : ℝ) ^ 2 * Complex.normSq h) * t⁻¹ := by
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have e : -1 / ((c : ℂ) ^ 2 * (I * t * h)) = I * ((((c : ℝ) ^ 2 * t : ℝ) : ℂ) * h)⁻¹ := by
    push_cast
    field_simp
    ring_nf
    rw [I_sq]
  rw [e, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add, Complex.inv_re,
    Complex.normSq_mul, Complex.normSq_ofReal, Complex.re_ofReal_mul]
  have hn : Complex.normSq h ≠ 0 := by rwa [Ne, Complex.normSq_eq_zero]
  have hc2 : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  field_simp

/-- Asymptotics of the theta function near the cusp `a / c`. -/
theorem cusp (c : ℕ) (hc : 0 < c) (a : ℤ) (ha : Even ((c : ℤ) * a)) (h : ℝ → ℂ) (h0 : ℂ)
    (hh : Tendsto h (𝓝[>] 0) (𝓝 h0)) (hre : 0 < h0.re) :
    Tendsto (fun t : ℝ => (t : ℂ) ^ (1 / 2 : ℂ) * jacobiTheta₂ 0 ((a : ℂ) / c + I * t * h t)) (𝓝[>] 0)
      (𝓝 (∑ k ∈ range c, cexp (π * I * (k : ℂ) ^ 2 * a / c) * (1 / ((c : ℂ) ^ 2 * h0) ^ (1 / 2 : ℂ)))) := by
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hcr : (0 : ℝ) < (c : ℝ) ^ 2 := by positivity
  have hre_ev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < (h t).re :=
    (Complex.continuous_re.tendsto h0).comp hh |>.eventually (lt_mem_nhds hre)
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ 0 < (h t).re := (eventually_mem_nhdsWithin (s := Set.Ioi (0:ℝ)) (a := 0)).and hre_ev
  set F : ℝ → ℂ := fun t => ∑ k ∈ range c, cexp (π * I * (k : ℂ) ^ 2 * a / c) *
    (1 / ((c : ℂ) ^ 2 * h t) ^ (1 / 2 : ℂ) * jacobiTheta₂ ((k : ℂ) / c) (-1 / ((c : ℂ) ^ 2 * (I * t * h t))))
  have heq : (fun t : ℝ => (t : ℂ) ^ (1 / 2 : ℂ) * jacobiTheta₂ 0 ((a : ℂ) / c + I * t * h t)) =ᶠ[𝓝[>] 0] F := by
    filter_upwards [hev] with t ⟨ht, hht⟩
    have hw : 0 < (I * t * h t).im := by
      simp [Complex.mul_im, Complex.mul_re]; exact mul_pos ht hht
    have hh0 : h t ≠ 0 := fun h' => by rw [h'] at hht; simp at hht
    rw [split c hc a ha _ hw, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    have e1 : -I * ((c : ℂ) ^ 2 * (I * t * h t)) = (t : ℂ) * ((c : ℂ) ^ 2 * h t) := by
      ring_nf; rw [I_sq]; ring
    have hX : (c : ℂ) ^ 2 * h t ≠ 0 := mul_ne_zero (pow_ne_zero _ hc') hh0
    have htp : (t : ℂ) ^ (1 / 2 : ℂ) ≠ 0 := by
      rw [Ne, cpow_eq_zero_iff]; push Not; intro h; exact absurd h (by exact_mod_cast ht.ne')
    rw [e1, cpow_ofReal_mul' ht hX]
    field_simp
  refine Tendsto.congr' heq.symm ?_
  refine tendsto_finsetSum _ fun k _ => ?_
  refine Tendsto.const_mul _ ?_
  rw [show 1 / ((c : ℂ) ^ 2 * h0) ^ (1 / 2 : ℂ) = 1 / ((c : ℂ) ^ 2 * h0) ^ (1 / 2 : ℂ) * 1 by ring]
  refine Tendsto.mul ?_ ?_
  · -- continuity of z ↦ 1 / z ^ (1/2)
    have hslit : (c : ℂ) ^ 2 * h0 ∈ slitPlane := by
      left
      rw [show (c : ℂ) ^ 2 = (((c : ℝ) ^ 2 : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul]
      exact mul_pos hcr hre
    have hne : ((c : ℂ) ^ 2 * h0) ^ (1 / 2 : ℂ) ≠ 0 := by
      rw [Ne, cpow_eq_zero_iff]; push Not; intro h; exact absurd h (slitPlane_ne_zero hslit)
    have hca : ContinuousAt (fun z : ℂ => 1 / z ^ (1 / 2 : ℂ)) ((c : ℂ) ^ 2 * h0) :=
      continuousAt_const.div (continuousAt_cpow_const hslit) hne
    exact hca.tendsto.comp (hh.const_mul _)
  · -- theta tends to 1
    have him : Tendsto (fun t : ℝ => (-1 / ((c : ℂ) ^ 2 * (I * t * h t))).im) (𝓝[>] 0) atTop := by
      have hn0 : 0 < Complex.normSq h0 := by
        rw [Complex.normSq_pos]; intro h'; rw [h'] at hre; simp at hre
      have hcoef : Tendsto (fun t => (h t).re / ((c : ℝ) ^ 2 * Complex.normSq (h t))) (𝓝[>] 0)
          (𝓝 (h0.re / ((c : ℝ) ^ 2 * Complex.normSq h0))) := by
        refine Tendsto.div ((Complex.continuous_re.tendsto h0).comp hh)
          (((Complex.continuous_normSq.tendsto h0).comp hh).const_mul _) (by positivity)
      have := hcoef.pos_mul_atTop (by positivity) tendsto_inv_nhdsGT_zero
      refine this.congr' ?_
      filter_upwards [hev] with t ⟨ht, hht⟩
      have hh0 : h t ≠ 0 := fun h' => by rw [h'] at hht; simp at hht
      exact (im_formula c hc ht hh0).symm
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨Y, -, hY⟩ := theta_near_one (half_pos hε)
    filter_upwards [him.eventually (eventually_ge_atTop Y)] with t ht
    rw [dist_eq_norm]
    have := hY ((k : ℝ) / c) _ ht
    push_cast at this
    linarith


lemma sq_cpow_half (q : ℕ) (hq : 0 < q) : (((q : ℂ) ^ 2) ^ (1 / 2 : ℂ)) = q := by
  rw [show ((q : ℂ) ^ 2) = (((q : ℝ) ^ 2 : ℝ) : ℂ) by push_cast; rfl,
    show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_cpow (by positivity)]
  rw [← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity)]
  norm_cast

lemma theta_FE0 {τ : ℂ} : jacobiTheta₂ 0 τ = 1 / (-I * τ) ^ (1 / 2 : ℂ) * jacobiTheta₂ 0 (-1 / τ) := by
  rw [jacobiTheta₂_functional_equation 0 τ]; simp

/-- Quadratic Gauss sum, unnormalised form. -/
theorem gauss_eval (q : ℕ) (hq : Odd q) :
    (∑ k ∈ range q, cexp (2 * π * I * (k : ℂ) ^ 2 / q)) =
      (1 + (-I) ^ q) / ((-I * (2 / q : ℂ)) ^ (1 / 2 : ℂ)) := by
  have hq0 : 0 < q := hq.pos
  have hqc : (q : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
  -- path 1
  have P1 := cusp q hq0 2 (by rw [even_iff_two_dvd]; exact Dvd.intro_left _ rfl) (fun _ => 1) 1
    tendsto_const_nhds (by norm_num)
  simp only [mul_one] at P1
  rw [sq_cpow_half q hq0] at P1
  -- path 2
  set h' : ℝ → ℂ := fun t => (q : ℂ) ^ 2 / (2 * (2 + I * q * t)) with hh'
  have hh'0 : Tendsto h' (𝓝[>] 0) (𝓝 ((q : ℂ) ^ 2 / 4)) := by
    have : Tendsto (fun t : ℝ => (q : ℂ) ^ 2 / (2 * (2 + I * q * t))) (𝓝 0)
        (𝓝 ((q : ℂ) ^ 2 / (2 * (2 + I * q * ((0 : ℝ) : ℂ))))) := by
      refine Tendsto.div tendsto_const_nhds (Tendsto.const_mul _ (Tendsto.const_add _
        (Tendsto.const_mul _ (Complex.continuous_ofReal.tendsto 0)))) (by simp)
    convert this.mono_left nhdsWithin_le_nhds using 2
    simp; ring
  have hre : 0 < ((q : ℂ) ^ 2 / 4).re := by
    rw [show (q : ℂ) ^ 2 / 4 = (((q : ℝ) ^ 2 / 4 : ℝ) : ℂ) by push_cast; rfl, Complex.ofReal_re]
    positivity
  have P2 := cusp 2 two_pos (-(q : ℤ)) (by rw [even_iff_two_dvd]; exact Dvd.intro _ rfl) h' _ hh'0 hre
  have e4 : ((2 : ℕ) : ℂ) ^ 2 * ((q : ℂ) ^ 2 / 4) = (q : ℂ) ^ 2 := by push_cast; ring
  rw [e4, sq_cpow_half q hq0] at P2
  simp only [sum_range_succ, range_zero, sum_empty, zero_add] at P2
  -- functional equation along path 1
  have hfe : ∀ t : ℝ, 0 < t → (t : ℂ) ^ (1 / 2 : ℂ) * jacobiTheta₂ 0 (((2 : ℤ) : ℂ) / q + I * t) =
      1 / (-I * (((2 : ℤ) : ℂ) / q + I * t)) ^ (1 / 2 : ℂ) *
        ((t : ℂ) ^ (1 / 2 : ℂ) * jacobiTheta₂ 0 (((-(q : ℤ) : ℤ) : ℂ) / ((2 : ℕ) : ℂ) + I * t * h' t)) := by
    intro t ht
    rw [theta_FE0]
    have hden : (2 : ℂ) + I * q * t ≠ 0 := by
      intro h0; have := congrArg Complex.re h0; simp at this
    have hτ : (((2 : ℤ) : ℂ) / q + I * t) ≠ 0 := by
      intro h0; have := congrArg Complex.re h0
      simp at this
      exact absurd this (by positivity)
    have : -1 / (((2 : ℤ) : ℂ) / q + I * t) = (((-(q : ℤ) : ℤ) : ℂ) / ((2 : ℕ) : ℂ) + I * t * h' t) := by
      have hden' : (2 : ℂ) + q * I * t ≠ 0 := by rw [mul_comm (q : ℂ) I]; exact hden
      simp only [hh']
      push_cast
      field_simp
      ring_nf
    rw [this]; ring
  have hlim : Tendsto (fun t : ℝ => 1 / (-I * (((2 : ℤ) : ℂ) / q + I * t)) ^ (1 / 2 : ℂ)) (𝓝[>] 0)
      (𝓝 (1 / (-I * (2 / q : ℂ)) ^ (1 / 2 : ℂ))) := by
    have hslit : -I * (2 / q : ℂ) ∈ slitPlane := by
      right; simp; positivity
    have hne : (-I * (2 / q : ℂ)) ^ (1 / 2 : ℂ) ≠ 0 := by
      rw [Ne, cpow_eq_zero_iff]; push Not; intro h; exact absurd h (slitPlane_ne_zero hslit)
    have hca : ContinuousAt (fun z : ℂ => 1 / (-I * z) ^ (1 / 2 : ℂ)) (2 / q : ℂ) :=
      continuousAt_const.div ((continuousAt_cpow_const hslit).comp (by fun_prop)) hne
    have ht : Tendsto (fun t : ℝ => (((2 : ℤ) : ℂ) / q + I * t)) (𝓝[>] 0) (𝓝 (2 / q : ℂ)) := by
      have : Tendsto (fun t : ℝ => (((2 : ℤ) : ℂ) / q + I * t)) (𝓝 0) (𝓝 (((2 : ℤ) : ℂ) / q + I * ((0:ℝ):ℂ))) :=
        tendsto_const_nhds.add (tendsto_const_nhds.mul (Complex.continuous_ofReal.tendsto 0))
      convert this.mono_left nhdsWithin_le_nhds using 2; simp
    exact hca.tendsto.comp ht
  have P1' := (hlim.mul P2).congr' (by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hfe t ht).symm)
  have := tendsto_nhds_unique P1 (by simpa using P1')
  -- now solve
  have hS : (-I * (2 / q : ℂ)) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; push Not; intro h; simp [hqc] at h
  have hE : cexp (-(π * I * q) / 2) = (-I) ^ q := by
    rw [show -(π * I * q) / 2 = q * (-(π / 2 * I)) by ring, Complex.exp_nat_mul, Complex.exp_neg,
      Complex.exp_pi_div_two_mul_I, Complex.inv_I]
  rw [hE] at this
  have e2 : ∀ k : ℕ, cexp (π * I * (k : ℂ) ^ 2 * ((2 : ℤ) : ℂ) / q) = cexp (2 * π * I * (k : ℂ) ^ 2 / q) := by
    intro k; congr 1; push_cast; ring
  simp only [e2, ← sum_mul] at this
  field_simp at this ⊢
  linear_combination this


lemma S_val (q : ℕ) (hq : 0 < q) : (-I * (2 / q : ℂ)) ^ (1 / 2 : ℂ) = (1 - I) / Real.sqrt q := by
  have h2q : (0 : ℝ) < 2 / q := by positivity
  rw [show -I * (2 / q : ℂ) = ((2 / q : ℝ) : ℂ) * (-I) by push_cast; ring,
    cpow_ofReal_mul' h2q (by simp), show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_cpow h2q.le, ← Real.sqrt_eq_rpow]
  rw [cpow_def_of_ne_zero (by simp), Complex.log_neg_I]
  have : -(↑π / 2) * I * ((1 / 2 : ℝ) : ℂ) = ((-(π / 4)) : ℝ) * I := by push_cast; ring
  rw [this, Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four,
    Real.sin_pi_div_four]
  have hs : Real.sqrt (2 / q) * (Real.sqrt 2 / 2) = 1 / Real.sqrt q := by
    rw [Real.sqrt_div (by norm_num)]
    have h1 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have h2 : 0 < Real.sqrt q := Real.sqrt_pos.2 (by exact_mod_cast hq)
    field_simp
    linarith
  have hsq : (Real.sqrt q : ℂ) ≠ 0 := by
    have h2 : 0 < Real.sqrt q := Real.sqrt_pos.2 (by exact_mod_cast hq)
    exact_mod_cast h2.ne'
  have hs' : (Real.sqrt (2 / q) : ℂ) * ((Real.sqrt 2 / 2 : ℝ) : ℂ) = 1 / (Real.sqrt q : ℂ) := by
    rw [← Complex.ofReal_mul, hs]; push_cast; ring
  push_cast at hs' ⊢
  field_simp at hs' ⊢
  linear_combination (1 - I) * hs'

theorem gauss_three (q : ℕ) (hq : q % 4 = 3) :
    (∑ k ∈ range q, cexp (2 * π * I * (k : ℂ) ^ 2 / q)) = I * Real.sqrt q := by
  have hodd : Odd q := Nat.odd_iff.2 (by omega)
  have hq0 : 0 < q := hodd.pos
  rw [gauss_eval q hodd, S_val q hq0]
  have hp : (-I) ^ q = I := by
    obtain ⟨m, rfl⟩ : ∃ m, q = 4 * m + 3 := ⟨q / 4, by omega⟩
    rw [pow_add, pow_mul]; norm_num
    ring_nf; rw [show I ^ 3 = I ^ 2 * I by ring, I_sq]; ring
  rw [hp]
  have hsq : (Real.sqrt q : ℂ) ≠ 0 := by
    have h2 : 0 < Real.sqrt q := Real.sqrt_pos.2 (by exact_mod_cast hq0)
    exact_mod_cast h2.ne'
  have h1I : (1 : ℂ) - I ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this
  field_simp
  ring_nf
  rw [I_sq]; ring

theorem gauss_one (q : ℕ) (hq : q % 4 = 1) :
    (∑ k ∈ range q, cexp (2 * π * I * (k : ℂ) ^ 2 / q)) = Real.sqrt q := by
  have hodd : Odd q := Nat.odd_iff.2 (by omega)
  have hq0 : 0 < q := hodd.pos
  rw [gauss_eval q hodd, S_val q hq0]
  have hp : (-I) ^ q = -I := by
    obtain ⟨m, rfl⟩ : ∃ m, q = 4 * m + 1 := ⟨q / 4, by omega⟩
    rw [pow_add, pow_mul]; norm_num
  rw [hp]
  have hsq : (Real.sqrt q : ℂ) ≠ 0 := by
    have h2 : 0 < Real.sqrt q := Real.sqrt_pos.2 (by exact_mod_cast hq0)
    exact_mod_cast h2.ne'
  have h1I : (1 : ℂ) - I ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this
  field_simp
  ring

end LOB

end

section
open Complex Filter Topology Finset Real ZMod

namespace LOC

lemma zsum (q : ℕ) [NeZero q] (f : ZMod q → ℂ) :
    ∑ x : ZMod q, f x = ∑ m ∈ range q, f (m : ZMod q) := by
  symm
  refine Finset.sum_nbij' (fun m => (m : ZMod q)) ZMod.val (by simp) (fun x _ => ?_) (fun m hm => ?_)
    (fun x _ => ?_) (fun m _ => rfl)
  · exact mem_range.2 (ZMod.val_lt x)
  · exact ZMod.val_cast_of_lt (by simpa using hm)
  · simp

variable {q : ℕ} [hqp : Fact q.Prime]

lemma ringChar_ne_two (hq2 : q ≠ 2) : ringChar (ZMod q) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]; exact hq2

lemma chi_eq (χ : DirichletCharacter ℂ q) (hχ : ∀ m : ℕ, χ m = (legendreSym q m : ℂ)) (a : ZMod q) :
    χ a = (quadraticChar (ZMod q) a : ℂ) := by
  rw [← ZMod.natCast_zmod_val a, hχ, legendreSym]
  simp

/-- The Gauss sum of the quadratic character is the quadratic exponential sum. -/
lemma gauss_eq (hq2 : q ≠ 2) (χ : DirichletCharacter ℂ q) (hχ : ∀ m : ℕ, χ m = (legendreSym q m : ℂ)) :
    gaussSum χ ZMod.stdAddChar = ∑ k ∈ range q, cexp (2 * π * I * (k : ℂ) ^ 2 / q) := by
  have hq1 : 1 < q := hqp.out.one_lt
  set ψ := (ZMod.stdAddChar : AddChar (ZMod q) ℂ)
  have hψ1 : ψ 1 = cexp (2 * π * I / q) := by
    simp only [ψ, ZMod.stdAddChar_apply, ZMod.toCircle_apply, ZMod.val_one'' (by omega : q ≠ 1)]
    push_cast; ring_nf
  have h1 : ∀ k : ℕ, cexp (2 * π * I * (k : ℂ) ^ 2 / q) = ψ (((k : ZMod q)) ^ 2) := by
    intro k
    rw [show ((k : ZMod q)) ^ 2 = (k ^ 2) • (1 : ZMod q) by simp, AddChar.map_nsmul_eq_pow, hψ1,
      ← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  simp_rw [h1]
  rw [← zsum q (fun x => ψ (x ^ 2))]
  -- fibre count
  have h2 : ∑ x : ZMod q, ψ (x ^ 2) = ∑ a : ZMod q, ((quadraticChar (ZMod q) a : ℂ) + 1) * ψ a := by
    have : ∀ a : ZMod q, ((quadraticChar (ZMod q) a : ℂ) + 1) =
        ((#{x : ZMod q | x ^ 2 = a}.toFinset : ℕ) : ℂ) := by
      intro a
      have := quadraticChar_card_sqrts (ringChar_ne_two hq2) a
      exact_mod_cast this.symm
    simp_rw [this]
    rw [← Finset.sum_fiberwise (s := univ) (g := fun x : ZMod q => x ^ 2) (f := fun x => ψ (x ^ 2))]
    refine sum_congr rfl fun a _ => ?_
    rw [sum_congr rfl (g := fun _ => ψ a), sum_const, nsmul_eq_mul]
    · simp
    · intro x hx; simp only [mem_filter] at hx; rw [hx.2]
  rw [h2]
  simp_rw [add_mul, one_mul, sum_add_distrib]
  have hψ : ψ ≠ 1 := by
    intro h
    have := congrArg (fun φ : AddChar (ZMod q) ℂ => φ 1) h
    simp only [AddChar.one_apply] at this
    rw [hψ1] at this
    have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hqp.out.ne_zero
    rw [Complex.exp_eq_one_iff] at this
    obtain ⟨n, hn⟩ := this
    field_simp at hn
    have h3 : (1 : ℤ) = n * q := by rw [mul_comm]; exact_mod_cast hn
    have : (q : ℤ) ∣ 1 := ⟨n, by rw [h3]; ring⟩
    have := Int.eq_one_of_dvd_one (by positivity) this
    omega
  rw [AddChar.sum_eq_zero_of_ne_one hψ, add_zero, gaussSum]
  refine sum_congr rfl fun a _ => ?_
  rw [chi_eq χ hχ]


lemma chi_sum (hq2 : q ≠ 2) (χ : DirichletCharacter ℂ q) (hχ : ∀ m : ℕ, χ m = (legendreSym q m : ℂ)) :
    ∑ a : ZMod q, χ a = 0 := by
  simp_rw [chi_eq χ hχ]
  exact_mod_cast quadraticChar_sum_zero (ringChar_ne_two hq2)

lemma chi_sq (χ : DirichletCharacter ℂ q) (hχ : ∀ m : ℕ, χ m = (legendreSym q m : ℂ)) {a : ZMod q}
    (ha : a ≠ 0) : χ a * χ a = 1 := by
  rw [chi_eq χ hχ, ← sq]
  exact_mod_cast quadraticChar_sq_one ha

lemma dft_chi (hq2 : q ≠ 2) (χ : DirichletCharacter ℂ q) (hχ : ∀ m : ℕ, χ m = (legendreSym q m : ℂ))
    (k : ZMod q) : 𝓕 (χ : ZMod q → ℂ) k = χ (-k) * gaussSum χ ZMod.stdAddChar := by
  rw [DirichletCharacter.fourierTransform_eq_gaussSum_mulShift]
  by_cases hk : k = 0
  · subst hk
    simp only [neg_zero, AddChar.mulShift_zero, MulChar.map_zero, zero_mul]
    rw [gaussSum]
    simp only [AddChar.one_apply, mul_one]
    exact chi_sum hq2 χ hχ
  · have hk' : -k ≠ 0 := neg_ne_zero.2 hk
    set u := Units.mk0 (-k) hk'
    have h := gaussSum_mulShift (χ : MulChar (ZMod q) ℂ) ZMod.stdAddChar u
    have hu : (u : ZMod q) = -k := rfl
    rw [hu] at h
    have hsq := chi_sq χ hχ hk'
    have : gaussSum χ (ZMod.stdAddChar.mulShift (-k)) =
        χ (-k) * (χ (-k) * gaussSum χ (ZMod.stdAddChar.mulShift (-k))) := by
      rw [← mul_assoc, hsq, one_mul]
    rw [this]
    have h' : χ (-k) * gaussSum χ (ZMod.stdAddChar.mulShift (-k)) = gaussSum χ ZMod.stdAddChar := by
      have := h; simpa using this
    rw [h']

lemma LFun_const_mul (c : ℂ) (Φ : ZMod q → ℂ) (s : ℂ) :
    ZMod.LFunction (fun k => c * Φ k) s = c * ZMod.LFunction Φ s := by
  simp only [ZMod.LFunction, mul_sum]
  refine sum_congr rfl fun j _ => by ring

lemma exp_ne_one {m : ℕ} (hm0 : 0 < m) (hmq : m < q) :
    cexp (2 * π * I * (((m : ℝ) / q : ℝ) : ℂ)) ≠ 1 := by
  intro h
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hqp.out.ne_zero
  have hpi : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  have h1 : ((m : ℝ) / q : ℂ) = n := by
    push_cast at hn
    have := hn
    field_simp at this ⊢
    linear_combination this
  have h2 : (m : ℝ) / q = n := by exact_mod_cast h1
  have hq0' : (0 : ℝ) < q := by exact_mod_cast hqp.out.pos
  have h3 : (0 : ℝ) < n := by rw [← h2]; positivity
  have h4 : (n : ℝ) < 1 := by rw [← h2, div_lt_one hq0']; exact_mod_cast hmq
  have h5 : (0 : ℤ) < n := by exact_mod_cast h3
  have h6 : n < (1 : ℤ) := by exact_mod_cast h4
  omega

/-- `L(1, χ)` as a finite sum of logarithms. -/
lemma L_formula (hq2 : q ≠ 2) (χ : DirichletCharacter ℂ q) (hχ : ∀ m : ℕ, χ m = (legendreSym q m : ℂ)) :
    χ.LFunction 1 = (1 / gaussSum χ ZMod.stdAddChar) *
      ∑ m ∈ range q, χ m * (-Complex.log (1 - cexp (2 * π * I * (((m : ℝ) / q : ℝ) : ℂ)))) := by
  set τ := gaussSum χ ZMod.stdAddChar with hτ
  have hfun : (χ : ZMod q → ℂ) = fun k => (1 / τ) * 𝓕 (fun j => χ (-j)) k := by
    funext k
    rw [ZMod.dft_comp_neg]
    simp only
    rw [dft_chi hq2 χ hχ, neg_neg]
    have hτ0 : τ ≠ 0 := by
      rw [hτ, gauss_eq hq2 χ hχ]
      rcases Nat.Prime.eq_two_or_odd hqp.out with h | h
      · exact absurd h hq2
      · have h4 : q % 4 = 1 ∨ q % 4 = 3 := by omega
        have hsq : (Real.sqrt q : ℂ) ≠ 0 := by
          have : 0 < Real.sqrt q := Real.sqrt_pos.2 (by exact_mod_cast hqp.out.pos)
          exact_mod_cast this.ne'
        rcases h4 with h4 | h4
        · rw [LOB.gauss_one q h4]; exact hsq
        · rw [LOB.gauss_three q h4]; exact mul_ne_zero I_ne_zero hsq
    field_simp
    rfl
  have hχ0 : χ 0 = 0 := MulChar.map_nonunit _ not_isUnit_zero
  have hL := congrArg (fun Φ => ZMod.LFunction Φ 1) hfun
  rw [DirichletCharacter.LFunction, hL, LFun_const_mul]
  congr 1
  rw [ZMod.LFunction_dft _ (Or.inl (by simpa using hχ0))]
  rw [show ∑ j : ZMod q, χ (-j) * HurwitzZeta.expZeta (ZMod.toAddCircle (-j)) 1 =
      ∑ j : ZMod q, χ j * HurwitzZeta.expZeta (ZMod.toAddCircle j) 1 from
    Fintype.sum_equiv (Equiv.neg _) _ _ (fun j => by simp)]
  rw [zsum q]
  refine sum_congr rfl fun m hm => ?_
  rcases Nat.eq_zero_or_pos m with h0 | h0
  · subst h0; simp [hχ0]
  · have hmq : m < q := mem_range.1 hm
    rw [ZMod.toAddCircle_apply, ZMod.val_cast_of_lt hmq, LOA.expZeta_one _ (exp_ne_one h0 hmq)]

end LOC

end

section
open Complex Filter Topology Finset Real ZMod

namespace LOD

lemma logform {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1) :
    -Complex.log (1 - cexp (2 * π * I * (θ : ℂ))) =
      -((Real.log (2 * Real.sin (π * θ)) : ℝ) : ℂ) - I * ((π * θ - π / 2 : ℝ) : ℂ) := by
  have hs : 0 < Real.sin (π * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  have key : 1 - cexp (2 * π * I * (θ : ℂ)) =
      ((2 * Real.sin (π * θ) : ℝ) : ℂ) * cexp (((π * θ - π / 2 : ℝ) : ℂ) * I) := by
    rw [show 2 * π * I * (θ : ℂ) = ((2 * (π * θ) : ℝ) : ℂ) * I by push_cast; ring,
      Complex.exp_mul_I, Complex.exp_mul_I, ← ofReal_cos, ← ofReal_sin, ← ofReal_cos, ← ofReal_sin,
      Real.cos_sub_pi_div_two, Real.sin_sub_pi_div_two, Real.cos_two_mul, Real.sin_two_mul]
    have := Real.sin_sq_add_cos_sq (π * θ)
    have hc : ((Real.sin (π * θ) : ℝ) : ℂ) ^ 2 + ((Real.cos (π * θ) : ℝ) : ℂ) ^ 2 = 1 := by
      exact_mod_cast this
    push_cast at hc ⊢
    linear_combination (-2 : ℂ) * hc
  rw [key, Complex.log_ofReal_mul (by positivity) (Complex.exp_ne_zero _), Complex.log_exp]
  · ring
  · simp; nlinarith [Real.pi_pos]
  · simp; nlinarith [Real.pi_pos]

variable {q : ℕ} [hqp : Fact q.Prime]

/-- Common evaluation of the finite sum. -/
lemma sum_form (hq2 : q ≠ 2) (χ : DirichletCharacter ℂ q) (hχ : ∀ m : ℕ, χ m = (legendreSym q m : ℂ)) :
    ∑ m ∈ range q, χ m * (-Complex.log (1 - cexp (2 * π * I * (((m : ℝ) / q : ℝ) : ℂ)))) =
      -((∑ m ∈ Ico 1 q, (legendreSym q m : ℝ) * Real.log (2 * Real.sin (π * (m / q))) : ℝ) : ℂ) -
        I * ((π / q * ∑ m ∈ Ico 1 q, (m : ℝ) * (legendreSym q m : ℝ) -
          π / 2 * ∑ m ∈ Ico 1 q, (legendreSym q m : ℝ) : ℝ) : ℂ) := by
  have hq1 : 1 ≤ q := hqp.out.one_lt.le
  have hχ0 : χ 0 = 0 := MulChar.map_nonunit _ not_isUnit_zero
  rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega)]
  simp only [Nat.cast_zero, hχ0, zero_mul, zero_add]
  have hq0' : (0 : ℝ) < q := by exact_mod_cast hqp.out.pos
  have hterm : ∀ m ∈ Ico 1 q, χ m * (-Complex.log (1 - cexp (2 * π * I * (((m : ℝ) / q : ℝ) : ℂ)))) =
      ((legendreSym q m : ℝ) : ℂ) *
        (-((Real.log (2 * Real.sin (π * (m / q))) : ℝ) : ℂ) - I * ((π * (m / q) - π / 2 : ℝ) : ℂ)) := by
    intro m hm
    have hm' := mem_Ico.1 hm
    have hpos : (0 : ℝ) < (m : ℝ) / q := div_pos (by exact_mod_cast hm'.1) hq0'
    rw [hχ m, LOD.logform hpos (by rw [div_lt_one hq0']; exact_mod_cast hm'.2)]
    push_cast; ring
  have hs := Finset.sum_congr (rfl : Ico 1 q = Ico 1 q) hterm
  rw [hs]
  push_cast
  rw [mul_sum, mul_sum, ← sum_sub_distrib, mul_sum, ← sum_neg_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun m _ => ?_
  ring

lemma chi_neg_one (hq2 : q ≠ 2) (χ : DirichletCharacter ℂ q) (hχ : ∀ m : ℕ, χ m = (legendreSym q m : ℂ)) :
    χ (-1) = (ZMod.χ₄ q : ℂ) := by
  rw [LOC.chi_eq χ hχ, quadraticChar_neg_one (LOC.ringChar_ne_two hq2), ZMod.card]

lemma leg_reflect (hq2 : q ≠ 2) (χ : DirichletCharacter ℂ q) (hχ : ∀ m : ℕ, χ m = (legendreSym q m : ℂ))
    {m : ℕ} (hm : m ≤ q) :
    (legendreSym q (q - m : ℕ) : ℝ) = (ZMod.χ₄ q : ℝ) * (legendreSym q m : ℝ) := by
  have h : χ ((q - m : ℕ) : ZMod q) = χ (-1) * χ m := by
    rw [← map_mul, Nat.cast_sub hm, ZMod.natCast_self, zero_sub, neg_one_mul]
  rw [hχ, hχ, chi_neg_one hq2 χ hχ] at h
  exact_mod_cast h

lemma sum_zero (hq2 : q ≠ 2) (χ : DirichletCharacter ℂ q) (hχ : ∀ m : ℕ, χ m = (legendreSym q m : ℂ)) :
    ∑ m ∈ Ico 1 q, (legendreSym q m : ℝ) = 0 := by
  have h := LOC.chi_sum hq2 χ hχ
  rw [LOC.zsum q, range_eq_Ico, sum_eq_sum_Ico_succ_bot hqp.out.pos] at h
  have hχ0 : χ 0 = 0 := MulChar.map_nonunit _ not_isUnit_zero
  simp only [Nat.cast_zero, hχ0, zero_add] at h
  simp_rw [hχ] at h
  exact_mod_cast h

lemma reflect_sum (f : ℕ → ℝ) : ∑ m ∈ Ico 1 q, f (q - m) = ∑ m ∈ Ico 1 q, f m := by
  have := Finset.sum_Ico_reflect f 1 (show q ≤ q + 1 by omega)
  rw [this]
  congr 1
  rcases Nat.eq_zero_or_pos q with h | h
  · subst h; simp
  · congr 1 <;> omega

lemma sin_reflect {m : ℕ} (hm : m ≤ q) :
    Real.sin (π * (((q - m : ℕ) : ℝ) / q)) = Real.sin (π * (m / q)) := by
  have hq0' : (q : ℝ) ≠ 0 := by exact_mod_cast hqp.out.ne_zero
  rw [Nat.cast_sub hm, show π * ((q - m : ℝ) / q) = π - π * (m / q) by field_simp, Real.sin_pi_sub]

end LOD

end

section
open Finset

namespace LOE
open Complex Real

variable {q : ℕ} [hqp : Fact q.Prime]

lemma A_zero (hq : q % 4 = 3) (χ : DirichletCharacter ℂ q) (hχ : ∀ m : ℕ, χ m = (legendreSym q m : ℂ)) :
    ∑ m ∈ Ico 1 q, (legendreSym q m : ℝ) * Real.log (2 * Real.sin (π * (m / q))) = 0 := by
  have hq2 : q ≠ 2 := by omega
  set f : ℕ → ℝ := fun m => (legendreSym q m : ℝ) * Real.log (2 * Real.sin (π * (m / q)))
  have h4 : (ZMod.χ₄ (q : ZMod 4) : ℝ) = -1 := by
    rw [ZMod.χ₄_nat_three_mod_four hq]; norm_num
  have h := LOD.reflect_sum (q := q) f
  have h' : ∑ m ∈ Ico 1 q, f (q - m) = -∑ m ∈ Ico 1 q, f m := by
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun m hm => ?_
    have hmq : m ≤ q := (mem_Ico.1 hm).2.le
    simp only [f]
    rw [LOD.leg_reflect hq2 χ hχ hmq, LOD.sin_reflect hmq, h4]; ring
  change ∑ m ∈ Ico 1 q, f m = 0
  linarith

lemma S_zero (hq : q % 4 = 1) (χ : DirichletCharacter ℂ q) (hχ : ∀ m : ℕ, χ m = (legendreSym q m : ℂ)) :
    ∑ m ∈ Ico 1 q, (m : ℝ) * (legendreSym q m : ℝ) = 0 := by
  have hq2 : q ≠ 2 := by omega
  set f : ℕ → ℝ := fun m => (m : ℝ) * (legendreSym q m : ℝ)
  have h4 : (ZMod.χ₄ (q : ZMod 4) : ℝ) = 1 := by
    rw [ZMod.χ₄_nat_one_mod_four hq]; norm_num
  have h := LOD.reflect_sum (q := q) f
  have hZ := LOD.sum_zero hq2 χ hχ
  have h' : ∑ m ∈ Ico 1 q, f (q - m) = q * ∑ m ∈ Ico 1 q, (legendreSym q m : ℝ) - ∑ m ∈ Ico 1 q, f m := by
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun m hm => ?_
    have hmq : m ≤ q := (mem_Ico.1 hm).2.le
    simp only [f]
    rw [LOD.leg_reflect hq2 χ hχ hmq, h4, Nat.cast_sub hmq]; ring
  rw [hZ, mul_zero, zero_sub] at h'
  change ∑ m ∈ Ico 1 q, f m = 0
  linarith

theorem three (q : ℕ) [Fact q.Prime] (hq : q % 4 = 3)
    (χ : DirichletCharacter ℂ q) (hχ : ∀ m : ℕ, χ m = (legendreSym q m : ℂ)) :
    χ.LFunction 1 = ((-(π / (q : ℝ) ^ ((3 : ℝ) / 2)) *
      ∑ m ∈ Finset.Ico 1 q, (m : ℝ) * (legendreSym q m : ℝ) : ℝ) : ℂ) := by
  have hq2 : q ≠ 2 := by omega
  rw [LOC.L_formula hq2 χ hχ, LOD.sum_form hq2 χ hχ, LOC.gauss_eq hq2 χ hχ, LOB.gauss_three q hq,
    A_zero hq χ hχ, LOD.sum_zero hq2 χ hχ]
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (Fact.out : q.Prime).pos
  have hpow : (q : ℝ) ^ ((3 : ℝ) / 2) = q * Real.sqrt q := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hq0, Real.rpow_one, Real.sqrt_eq_rpow]
  rw [hpow]
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.2 hq0
  have hs' : (Real.sqrt q : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
  push_cast
  field_simp
  ring_nf

theorem one (q : ℕ) [Fact q.Prime] (hq : q % 4 = 1)
    (χ : DirichletCharacter ℂ q) (hχ : ∀ m : ℕ, χ m = (legendreSym q m : ℂ)) :
    χ.LFunction 1 = ((-(1 / Real.sqrt q) * ∑ m ∈ Finset.Ico 1 q,
      (legendreSym q m : ℝ) * Real.log (Real.sin (m * π / q)) : ℝ) : ℂ) := by
  have hq2 : q ≠ 2 := by omega
  rw [LOC.L_formula hq2 χ hχ, LOD.sum_form hq2 χ hχ, LOC.gauss_eq hq2 χ hχ, LOB.gauss_one q hq,
    S_zero hq χ hχ, LOD.sum_zero hq2 χ hχ]
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (Fact.out : q.Prime).pos
  have hA : ∑ m ∈ Ico 1 q, (legendreSym q m : ℝ) * Real.log (2 * Real.sin (π * (m / q))) =
      ∑ m ∈ Ico 1 q, (legendreSym q m : ℝ) * Real.log (Real.sin (m * π / q)) := by
    have hZ := LOD.sum_zero hq2 χ hχ
    have : ∀ m ∈ Ico 1 q, (legendreSym q m : ℝ) * Real.log (2 * Real.sin (π * (m / q))) =
        Real.log 2 * (legendreSym q m : ℝ) + (legendreSym q m : ℝ) * Real.log (Real.sin (m * π / q)) := by
      intro m hm
      have hm' := mem_Ico.1 hm
      have hpos : 0 < Real.sin (π * (m / q)) := by
        apply Real.sin_pos_of_pos_of_lt_pi
        · exact mul_pos Real.pi_pos (div_pos (by exact_mod_cast hm'.1) hq0)
        · have : (m : ℝ) / q < 1 := by rw [div_lt_one hq0]; exact_mod_cast hm'.2
          nlinarith [Real.pi_pos]
      rw [Real.log_mul (by norm_num) hpos.ne', show π * (m / q) = m * π / q by ring]
      ring
    rw [sum_congr rfl this, sum_add_distrib, ← mul_sum, hZ, mul_zero, zero_add]
  rw [hA]
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.2 hq0
  have hs' : (Real.sqrt q : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  generalize (∑ m ∈ Ico 1 q, (legendreSym q m : ℝ) * Real.log (Real.sin (m * π / q))) = A'
  push_cast
  field_simp
  ring

end LOE

end

open NumberField NumberField.InfinitePlace NumberField.Units Filter Topology Real

theorem solution (q : ℕ) [Fact q.Prime] (hq : q % 4 = 1)
    (χ : DirichletCharacter ℂ q) (hχ : ∀ m : ℕ, χ m = (legendreSym q m : ℂ)) :
    χ.LFunction 1 = ((-(1 / Real.sqrt q) * ∑ m ∈ Finset.Ico 1 q,
      (legendreSym q m : ℝ) * Real.log (Real.sin (m * π / q)) : ℝ) : ℂ) :=
  LOE.one q hq χ hχ
