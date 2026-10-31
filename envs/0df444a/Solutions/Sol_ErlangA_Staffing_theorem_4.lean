-- Prove2me | solution 1 for ErlangA.Staffing.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-30T18:23:13.393013+00:00
-- url     : https://prove2.me/submissions/606ff4e9-1f8f-48fb-b0da-c72805295c9d

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Erlang
import Definitions.Def_DimCallCenters_Rationalized_delayFn
import Definitions.Def_ErlangA_Staffing_Model

set_option autoImplicit false

open Filter Topology MeasureTheory

namespace ErlA4

theorem fac_upper (u v : ℝ) (_hu1 : u ≤ 1) (hv1 : v < 1) :
    (1 - u) / (1 - v) ≤ Real.exp (-u + v / (1 - v)) := by
  have hp : 0 < 1 - v := by linarith
  have h1 : 1 - u ≤ Real.exp (-u) := by linarith [Real.add_one_le_exp (-u)]
  have h2 : 1 / (1 - v) ≤ Real.exp (v / (1 - v)) := by
    have := Real.add_one_le_exp (v / (1 - v))
    have e : v / (1 - v) + 1 = 1 / (1 - v) := by field_simp; ring
    linarith
  calc (1 - u) / (1 - v) = (1 - u) * (1 / (1 - v)) := by ring
    _ ≤ Real.exp (-u) * Real.exp (v / (1 - v)) :=
        mul_le_mul h1 h2 (by positivity) (Real.exp_pos _).le
    _ = Real.exp (-u + v / (1 - v)) := (Real.exp_add _ _).symm

theorem fac_lower (u v : ℝ) (hu1 : u < 1) (hv1 : v < 1) :
    Real.exp (-(u / (1 - u)) + v) ≤ (1 - u) / (1 - v) := by
  have hp : 0 < 1 - v := by linarith
  have hq : 0 < 1 - u := by linarith
  have h1 : Real.exp (-(u / (1 - u))) ≤ 1 - u := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) hq]
    have := Real.add_one_le_exp (u / (1 - u))
    have e : u / (1 - u) + 1 = (1 - u)⁻¹ := by field_simp; ring
    linarith
  have h2 : Real.exp v ≤ 1 / (1 - v) := by
    rw [le_div_iff₀ hp]
    have h3 := Real.add_one_le_exp (-v)
    have e : Real.exp v * Real.exp (-v) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos v]
  calc Real.exp (-(u / (1 - u)) + v) = Real.exp (-(u / (1 - u))) * Real.exp v := Real.exp_add _ _
    _ ≤ (1 - u) * (1 / (1 - v)) := mul_le_mul h1 h2 (Real.exp_pos _).le hq.le
    _ = (1 - u) / (1 - v) := by ring

theorem sum_range_id_real (k : ℕ) : ∑ j ∈ Finset.range k, (j : ℝ) = k * (k - 1) / 2 := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
theorem tendsto_sqrt_nat : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
  Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop

theorem tendsto_floor_div (x : ℝ) (hx : 0 ≤ x) :
    Tendsto (fun n : ℕ => (⌊x * Real.sqrt n⌋₊ : ℝ) / Real.sqrt n) atTop (𝓝 x) := by
  have hs : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (𝓝 0) :=
    tendsto_sqrt_nat.inv_tendsto_atTop
  have hlow : Tendsto (fun n : ℕ => x - (Real.sqrt n)⁻¹) atTop (𝓝 x) := by
    simpa using (tendsto_const_nhds (x := x)).sub hs
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [tendsto_sqrt_nat.eventually_gt_atTop 0] with n hq
    rw [le_div_iff₀ hq]
    have := Nat.lt_floor_add_one (x * Real.sqrt n)
    have e : (x - (Real.sqrt n)⁻¹) * Real.sqrt n = x * Real.sqrt n - 1 := by field_simp
    rw [e]; linarith
  · filter_upwards [tendsto_sqrt_nat.eventually_gt_atTop 0] with n hq
    rw [div_le_iff₀ hq]
    exact Nat.floor_le (by positivity)

theorem exp_neg_div_le (v : ℝ) (hv1 : v < 1) : Real.exp (-(v / (1 - v))) ≤ 1 - v := by
  have hq : 0 < 1 - v := by linarith
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) hq]
  have := Real.add_one_le_exp (v / (1 - v))
  have e : v / (1 - v) + 1 = (1 - v)⁻¹ := by field_simp; ring
  linarith

theorem one_sub_le_exp_neg (v : ℝ) : 1 - v ≤ Real.exp (-v) := by
  linarith [Real.add_one_le_exp (-v)]

theorem v_tendsto (v : ℕ → ℝ) (β : ℝ)
    (hc : Tendsto (fun n : ℕ => v n * Real.sqrt n) atTop (𝓝 β)) :
    Tendsto v atTop (𝓝 0) := by
  have h := hc.mul (tendsto_sqrt_nat.inv_tendsto_atTop)
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [tendsto_sqrt_nat.eventually_gt_atTop 0] with n hq
  change v n * Real.sqrt n * (Real.sqrt n)⁻¹ = v n
  field_simp

theorem ind_integral (q : ℝ) (hq : 0 < q) (m : ℕ) (c : ℝ) :
    ∫ x in Set.Ici (0 : ℝ), (Set.Ico ((m : ℝ) / q) (((m : ℝ) + 1) / q)).indicator (fun _ => c) x
      = q⁻¹ * c := by
  have hsub : Set.Ico ((m : ℝ) / q) (((m : ℝ) + 1) / q) ⊆ Set.Ici 0 := by
    intro y hy
    exact le_trans (by positivity) hy.1
  have hle : (m : ℝ) / q ≤ ((m : ℝ) + 1) / q :=
    div_le_div_of_nonneg_right (by linarith) hq.le
  rw [integral_indicator_const _ measurableSet_Ico, measureReal_restrict_apply measurableSet_Ico,
    Set.inter_eq_left.2 hsub, Real.volume_real_Ico_of_le hle, smul_eq_mul]
  have : ((m : ℝ) + 1) / q - (m : ℝ) / q = q⁻¹ := by ring
  rw [this]

theorem ind_integrable (q : ℝ) (m : ℕ) (c : ℝ) :
    Integrable (fun x : ℝ => (Set.Ico ((m : ℝ) / q) (((m : ℝ) + 1) / q)).indicator (fun _ => c) x)
      (volume.restrict (Set.Ici (0 : ℝ))) := by
  refine Integrable.restrict ?_
  exact (integrable_indicator_iff measurableSet_Ico).2
    (integrableOn_const (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top))

theorem H_eq (q : ℝ) (hq : 0 < q) (c : ℕ → ℝ) (x : ℝ) (hx : 0 ≤ x) :
    ∑' m : ℕ, (Set.Ico ((m : ℝ) / q) (((m : ℝ) + 1) / q)).indicator (fun _ => c m) x
      = c ⌊x * q⌋₊ := by
  have hxq : 0 ≤ x * q := by positivity
  rw [tsum_eq_single ⌊x * q⌋₊]
  · rw [Set.indicator_of_mem]
    rw [Set.mem_Ico, div_le_iff₀ hq, lt_div_iff₀ hq]
    exact ⟨Nat.floor_le hxq, Nat.lt_floor_add_one _⟩
  · intro m hm
    rw [Set.indicator_of_notMem]
    intro hmem
    rw [Set.mem_Ico, div_le_iff₀ hq, lt_div_iff₀ hq] at hmem
    exact hm ((Nat.floor_eq_iff hxq).2 ⟨hmem.1, hmem.2⟩).symm

theorem step_integral (q : ℝ) (hq : 0 < q) (c : ℕ → ℝ) (hs : Summable fun m => |c m|) :
    ∫ x in Set.Ici (0 : ℝ),
      (∑' m : ℕ, (Set.Ico ((m : ℝ) / q) (((m : ℝ) + 1) / q)).indicator (fun _ => c m) x)
      = q⁻¹ * ∑' m, c m := by
  have hsum : Summable fun m : ℕ => ∫ x in Set.Ici (0 : ℝ),
      ‖(Set.Ico ((m : ℝ) / q) (((m : ℝ) + 1) / q)).indicator (fun _ => c m) x‖ := by
    have : ∀ m : ℕ, ∫ x in Set.Ici (0 : ℝ),
        ‖(Set.Ico ((m : ℝ) / q) (((m : ℝ) + 1) / q)).indicator (fun _ => c m) x‖ =
          q⁻¹ * |c m| := by
      intro m
      simp_rw [norm_indicator_eq_indicator_norm, Real.norm_eq_abs]
      exact ind_integral q hq m |c m|
    simp_rw [this]
    exact hs.mul_left q⁻¹
  rw [← integral_tsum_of_summable_integral_norm (fun m => ind_integrable q m (c m)) hsum]
  simp_rw [ind_integral q hq]
  rw [tsum_mul_left]

/-- left products `∏_{i<j} (1 - i/n)/(1 - v)`. -/
noncomputable def uL (n : ℕ) (v : ℝ) (j : ℕ) : ℝ :=
  ∏ i ∈ Finset.range j, (1 - (i : ℝ) / n) / (1 - v)

theorem uL_nonneg (n : ℕ) (v : ℝ) (j : ℕ) (hn : 0 < n) (hj : j ≤ n) (hv : v < 1) :
    0 ≤ uL n v j := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  unfold uL
  refine Finset.prod_nonneg fun i hi => ?_
  have h1 : i < n := lt_of_lt_of_le (Finset.mem_range.1 hi) hj
  have h2 : (i : ℝ) < n := by exact_mod_cast h1
  have h3 : (i : ℝ) / n ≤ 1 := by rw [div_le_one hnr]; linarith
  apply div_nonneg <;> linarith


theorem uL_upper (n : ℕ) (q : ℝ) (hq : (n : ℝ) = q ^ 2) (v : ℝ) (j : ℕ) (hn : 0 < n)
    (hj : j ≤ n) (hv : v < 1) :
    uL n v j ≤ Real.exp (-((j : ℝ) * (j - 1) / 2) / q ^ 2 + j * (v / (1 - v))) := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← hq]
  unfold uL
  calc ∏ i ∈ Finset.range j, (1 - (i : ℝ) / n) / (1 - v)
      ≤ ∏ i ∈ Finset.range j, Real.exp (-((i : ℝ) / n) + v / (1 - v)) := by
        refine Finset.prod_le_prod (fun i hi => ?_) (fun i hi => ?_)
        · have h1 : i < n := lt_of_lt_of_le (Finset.mem_range.1 hi) hj
          have h2 : (i : ℝ) < n := by exact_mod_cast h1
          have h3 : (i : ℝ) / n ≤ 1 := by rw [div_le_one hnr]; linarith
          apply div_nonneg <;> linarith
        · have h1 : i < n := lt_of_lt_of_le (Finset.mem_range.1 hi) hj
          have h2 : (i : ℝ) < n := by exact_mod_cast h1
          exact fac_upper _ _ (by rw [div_le_one hnr]; linarith) hv
    _ = _ := by
        rw [← Real.exp_sum]
        congr 1
        rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.sum_div,
          sum_range_id_real, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

theorem uL_lower (n : ℕ) (q : ℝ) (hq : (n : ℝ) = q ^ 2) (v : ℝ) (j : ℕ) (hn : 0 < n)
    (hj : j < n) (hv : v < 1) :
    Real.exp (-((j : ℝ) * (j - 1) / 2) / (q ^ 2 - j) + j * v) ≤ uL n v j := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hjr : (j : ℝ) < n := by exact_mod_cast hj
  rw [← hq]
  unfold uL
  calc Real.exp (-((j : ℝ) * (j - 1) / 2) / ((n : ℝ) - j) + j * v)
      = ∏ i ∈ Finset.range j, Real.exp (-((i : ℝ) / ((n : ℝ) - j)) + v) := by
        rw [← Real.exp_sum]
        congr 1
        rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.sum_div,
          sum_range_id_real, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
    _ ≤ ∏ i ∈ Finset.range j, (1 - (i : ℝ) / n) / (1 - v) := by
        refine Finset.prod_le_prod (fun i _ => (Real.exp_pos _).le) fun i hi => ?_
        have hij : i < j := Finset.mem_range.1 hi
        have hi0 : (0 : ℝ) ≤ i := by positivity
        have hijr : (i : ℝ) < j := by exact_mod_cast hij
        have hu : (i : ℝ) / n < 1 := by rw [div_lt_one hnr]; linarith
        refine le_trans ?_ (fac_lower _ _ hu hv)
        apply Real.exp_le_exp.2
        have e : (i : ℝ) / n / (1 - (i : ℝ) / n) = (i : ℝ) / ((n : ℝ) - i) := by
          field_simp
        rw [e]
        have : (i : ℝ) / ((n : ℝ) - i) ≤ (i : ℝ) / ((n : ℝ) - j) :=
          div_le_div_of_nonneg_left hi0 (by linarith) (by linarith)
        linarith

theorem expo_upper_eq (q v j : ℝ) (hq : 0 < q) (hv : v < 1) :
    -(j * (j - 1) / 2) / q ^ 2 + j * (v / (1 - v)) =
      -((j / q) * (j / q - q⁻¹)) / 2 + (j / q) * ((v * q) / (1 - v)) := by
  have h1 : 1 - v ≠ 0 := by intro h; linarith
  field_simp
  try ring

theorem expo_lower_eq (q v j : ℝ) (hq : 0 < q) (hj : j < q ^ 2) :
    -(j * (j - 1) / 2) / (q ^ 2 - j) + j * v =
      -((j / q) * (j / q - q⁻¹) / 2) / (1 - (j / q) * q⁻¹) + (j / q) * (v * q) := by
  have h1 : q ^ 2 - j ≠ 0 := by intro h; linarith
  have h2 : 1 - (j / q) * q⁻¹ = (q ^ 2 - j) / q ^ 2 := by field_simp
  rw [h2]
  field_simp
  try ring
theorem bound_integrable' (β : ℝ) :
    Integrable (fun x : ℝ => Real.exp (-x ^ 2 / 2 + x / 2 + 2 * β * (x + 1)))
      (volume.restrict (Set.Ici 0)) := by
  set b : ℝ := 2 * β + 1 / 2
  have hg := ((integrable_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num)).comp_sub_right b).const_mul
    (Real.exp (2 * β + b ^ 2 / 2))
  refine (hg.congr (ae_of_all _ fun x => ?_)).restrict
  simp only
  rw [← Real.exp_add]
  congr 1
  simp only [b]
  ring

theorem uL_pt (v : ℕ → ℝ) (β : ℝ)
    (hc : Tendsto (fun n : ℕ => v n * Real.sqrt n) atTop (𝓝 β))
    (j : ℕ → ℕ) (y : ℝ) (ht : Tendsto (fun n : ℕ => (j n : ℝ) / Real.sqrt n) atTop (𝓝 y)) :
    Tendsto (fun n : ℕ => uL n (v n) (j n)) atTop
      (𝓝 (Real.exp (β * y - y ^ 2 / 2))) := by
  have hv := v_tendsto v β hc
  have hs : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (𝓝 0) :=
    tendsto_sqrt_nat.inv_tendsto_atTop
  have hU : Tendsto (fun n : ℕ =>
      -(((j n : ℝ) / Real.sqrt n) * ((j n : ℝ) / Real.sqrt n
        - (Real.sqrt n)⁻¹)) / 2 + ((j n : ℝ) / Real.sqrt n) *
        ((v n * Real.sqrt n) / (1 - v n))) atTop (𝓝 (β * y - y ^ 2 / 2)) := by
    have := ((ht.mul (ht.sub hs)).neg.div_const 2).add
      (ht.mul (hc.div (tendsto_const_nhds.sub hv) (show (1 : ℝ) - 0 ≠ 0 by norm_num)))
    have e : β * y - y ^ 2 / 2 = -(y * (y - 0)) / 2 + y * (β / (1 - 0)) := by ring
    rw [e]; exact this
  have hL : Tendsto (fun n : ℕ =>
      -(((j n : ℝ) / Real.sqrt n) * ((j n : ℝ) / Real.sqrt n
        - (Real.sqrt n)⁻¹) / 2) / (1 - ((j n : ℝ) / Real.sqrt n) *
        (Real.sqrt n)⁻¹) + ((j n : ℝ) / Real.sqrt n) * (v n * Real.sqrt n))
      atTop (𝓝 (β * y - y ^ 2 / 2)) := by
    have := (((ht.mul (ht.sub hs)).div_const 2).neg.div
      ((tendsto_const_nhds (x := (1 : ℝ))).sub (ht.mul hs))
      (show (1 : ℝ) - y * 0 ≠ 0 by norm_num)).add (ht.mul hc)
    have e : β * y - y ^ 2 / 2 = -(y * (y - 0) / 2) / (1 - y * 0) + y * β := by ring
    rw [e]; exact this
  have hUe := hU.rexp
  have hLe := hL.rexp
  have hev : ∀ᶠ n : ℕ in atTop, v n < 1 ∧ (j n : ℝ) / Real.sqrt n < |y| + 1 ∧
      |y| + 1 < Real.sqrt n :=
    (hv.eventually (gt_mem_nhds (by norm_num))).and
      ((ht.eventually (gt_mem_nhds (by linarith [le_abs_self y]))).and
        (tendsto_sqrt_nat.eventually_gt_atTop _))
  have key : ∀ n : ℕ, v n < 1 → (j n : ℝ) / Real.sqrt n < |y| + 1 → |y| + 1 < Real.sqrt n →
      0 < Real.sqrt n ∧ 0 < n ∧ (n : ℝ) = Real.sqrt n ^ 2 ∧ j n < n := by
    intro n _ h2 h3
    have hq0 : 0 < Real.sqrt n := lt_of_le_of_lt (by positivity) h3
    have hn : 0 < n := by
      have : (0 : ℝ) < n := Real.sqrt_pos.1 hq0
      exact_mod_cast this
    have hn2 : (n : ℝ) = Real.sqrt n ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg n)).symm
    have hj : (j n : ℝ) < n := by
      rw [div_lt_iff₀ hq0] at h2
      have : (|y| + 1) * Real.sqrt n ≤ Real.sqrt n * Real.sqrt n := by nlinarith
      calc (j n : ℝ) < (|y| + 1) * Real.sqrt n := h2
        _ ≤ Real.sqrt n * Real.sqrt n := this
        _ = n := Real.mul_self_sqrt (Nat.cast_nonneg _)
    exact ⟨hq0, hn, hn2, by exact_mod_cast hj⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hLe hUe ?_ ?_
  · filter_upwards [hev] with n ⟨h1, h2, h3⟩
    obtain ⟨hq0, hn, hn2, hjn⟩ := key n h1 h2 h3
    have hj : (j n : ℝ) < n := by exact_mod_cast hjn
    have := uL_lower n (Real.sqrt n) hn2 (v n) _ hn hjn h1
    rw [expo_lower_eq _ _ _ hq0 (by rw [← hn2]; exact hj)] at this
    exact this
  · filter_upwards [hev] with n ⟨h1, h2, h3⟩
    obtain ⟨hq0, hn, hn2, hjn⟩ := key n h1 h2 h3
    have := uL_upper n (Real.sqrt n) hn2 (v n) _ hn hjn.le h1
    rw [expo_upper_eq _ _ _ hq0 h1] at this
    exact this

theorem floor_succ_div (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun n : ℕ => ((⌊t * Real.sqrt n⌋₊ + 1 : ℕ) : ℝ) / Real.sqrt n) atTop (𝓝 t) := by
  have h1 := tendsto_floor_div t ht
  have hs : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (𝓝 0) :=
    tendsto_sqrt_nat.inv_tendsto_atTop
  have := h1.add hs
  rw [add_zero] at this
  refine this.congr' ?_
  filter_upwards with n
  push_cast
  rw [add_div, div_eq_mul_inv 1, one_mul]

/-- generic dominated convergence for scaled sums `(√N)⁻¹ Σ' c N m`. -/
theorem step_dct (c : ℕ → ℕ → ℝ) (f g : ℝ → ℝ)
    (hsum : ∀ᶠ N : ℕ in atTop, Summable fun m => |c N m|)
    (hpt : ∀ t : ℝ, 0 ≤ t →
      Tendsto (fun N : ℕ => c N ⌊t * Real.sqrt N⌋₊) atTop (𝓝 (f t)))
    (hg : Integrable g (volume.restrict (Set.Ici (0 : ℝ))))
    (hdom : ∀ᶠ N : ℕ in atTop, ∀ t : ℝ, 0 ≤ t → |c N ⌊t * Real.sqrt N⌋₊| ≤ g t) :
    Tendsto (fun N : ℕ => (Real.sqrt N)⁻¹ * ∑' m, c N m) atTop
      (𝓝 (∫ t in Set.Ici (0 : ℝ), f t)) := by
  have hlim := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict (Set.Ici (0 : ℝ)))
    (F := fun (N : ℕ) (t : ℝ) => c N ⌊t * Real.sqrt N⌋₊) (f := f) (l := atTop) g
    (Eventually.of_forall fun N => (measurable_from_nat.comp
      (Nat.measurable_floor.comp (measurable_id.mul_const _))).aestronglyMeasurable)
    (hdom.mono fun N hN => (ae_restrict_iff' measurableSet_Ici).2
      (Eventually.of_forall fun t ht => by rw [Real.norm_eq_abs]; exact hN t ht))
    hg ((ae_restrict_iff' measurableSet_Ici).2 (Eventually.of_forall fun t ht => hpt t ht))
  refine hlim.congr' ?_
  filter_upwards [hsum, tendsto_sqrt_nat.eventually_gt_atTop 0] with N hN hq
  rw [← step_integral _ hq _ hN]
  refine setIntegral_congr_fun measurableSet_Ici fun t ht => ?_
  exact (H_eq _ hq _ t ht).symm

theorem vdiv_le (v : ℝ) (hv : |v| ≤ 1 / 2) : v / (1 - v) ≤ 2 * |v| := by
  have hv1 : v ≤ 1 / 2 := le_trans (le_abs_self v) hv
  rw [div_le_iff₀ (by linarith)]
  rcases abs_cases v with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> nlinarith [abs_nonneg v]

/-- left sum `SB = Σ_{m<N} uL N v (m+1)`. -/
noncomputable def SB (N : ℕ) (v : ℝ) : ℝ := ∑ m ∈ Finset.range N, uL N v (m + 1)

theorem left_lim (v : ℕ → ℝ) (β : ℝ)
    (hc : Tendsto (fun n : ℕ => v n * Real.sqrt n) atTop (𝓝 β)) :
    Tendsto (fun N : ℕ => (Real.sqrt N)⁻¹ * SB N (v N)) atTop
      (𝓝 (∫ t in Set.Ici (0 : ℝ), Real.exp (β * t - t ^ 2 / 2))) := by
  set K : ℝ := |β| + 1 with hK
  have hK0 : 0 < K := by positivity
  set c : ℕ → ℕ → ℝ := fun N m => if m < N then uL N (v N) (m + 1) else 0 with hcdef
  have hv := v_tendsto v β hc
  have hsumeq : ∀ N, ∑' m, c N m = SB N (v N) := by
    intro N
    rw [tsum_eq_sum (s := Finset.range N)]
    · refine Finset.sum_congr rfl fun m hm => ?_
      simp only [hcdef, if_pos (Finset.mem_range.1 hm)]
    · intro m hm
      simp only [hcdef, if_neg (fun h => hm (Finset.mem_range.2 h))]
  have hmain := step_dct c (fun t => Real.exp (β * t - t ^ 2 / 2))
    (fun x : ℝ => Real.exp (-x ^ 2 / 2 + x / 2 + 2 * K * (x + 1)))
    (Eventually.of_forall fun N => by
      refine summable_of_ne_finset_zero (s := Finset.range N) fun m hm => ?_
      simp only [hcdef, if_neg (fun h => hm (Finset.mem_range.2 h)), abs_zero])
    (fun t ht => by
      have h1 := uL_pt v β hc (fun n => ⌊t * Real.sqrt n⌋₊ + 1) t (floor_succ_div t ht)
      refine h1.congr' ?_
      have h2 : ∀ᶠ n : ℕ in atTop, ((⌊t * Real.sqrt n⌋₊ + 1 : ℕ) : ℝ) / Real.sqrt n < t + 1 ∧
          t + 1 < Real.sqrt n :=
        ((floor_succ_div t ht).eventually (gt_mem_nhds (by linarith))).and
          (tendsto_sqrt_nat.eventually_gt_atTop _)
      filter_upwards [h2] with n ⟨h3, h4⟩
      have hq0 : 0 < Real.sqrt n := lt_of_le_of_lt (by linarith) h4
      have hlt : ((⌊t * Real.sqrt n⌋₊ : ℕ) : ℝ) < n := by
        rw [div_lt_iff₀ hq0] at h3
        have : (t + 1) * Real.sqrt n ≤ Real.sqrt n * Real.sqrt n := by nlinarith
        push_cast at h3
        nlinarith [Real.mul_self_sqrt (Nat.cast_nonneg (α := ℝ) n)]
      have hlt' : ⌊t * Real.sqrt n⌋₊ < n := by exact_mod_cast hlt
      simp only [hcdef, if_pos hlt'])
    (bound_integrable' K)
    (by
      have h1 : ∀ᶠ n : ℕ in atTop, |v n * Real.sqrt n| < K ∧ 2 * K ≤ Real.sqrt n ∧ 1 ≤ n :=
        (hc.abs.eventually (gt_mem_nhds (show |β| < K by rw [hK]; linarith))).and
          ((tendsto_sqrt_nat.eventually_ge_atTop (2 * K)).and (eventually_ge_atTop 1))
      filter_upwards [h1] with N ⟨hvK, hNK, hN1⟩ t ht
      have hq0 : 0 < Real.sqrt N := by linarith
      have hq1 : 1 ≤ Real.sqrt N := by
        rw [show (1 : ℝ) = Real.sqrt 1 by simp]
        exact Real.sqrt_le_sqrt (by exact_mod_cast hN1)
      have hn2 : (N : ℝ) = Real.sqrt N ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg N)).symm
      have habsv : |v N| * Real.sqrt N < K := by rw [← abs_of_pos hq0, ← abs_mul]; exact hvK
      have hvh : |v N| ≤ 1 / 2 := by
        rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
        nlinarith [abs_nonneg (v N)]
      have hv1 : v N < 1 := by linarith [le_abs_self (v N)]
      simp only [hcdef]
      split_ifs with hm
      · set m := ⌊t * Real.sqrt N⌋₊ with hmdef
        have hmle : (m : ℝ) ≤ t * Real.sqrt N := Nat.floor_le (by positivity)
        have hmgt : t * Real.sqrt N < (m : ℝ) + 1 := Nat.lt_floor_add_one _
        have hpos : 0 ≤ uL N (v N) (m + 1) := uL_nonneg N (v N) (m + 1) (by omega) (by omega) hv1
        rw [abs_of_nonneg hpos]
        refine le_trans (uL_upper N (Real.sqrt N) hn2 (v N) (m + 1) (by omega) (by omega) hv1) ?_
        apply Real.exp_le_exp.2
        push_cast
        have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        have e1 : ((m : ℝ) + 1) * ((m : ℝ) + 1 - 1) = (m : ℝ) * (m + 1) := by ring
        rw [e1]
        have hA : t ^ 2 / 2 - t / 2 ≤ ((m : ℝ) * (m + 1) / 2) / Real.sqrt N ^ 2 := by
          rw [le_div_iff₀ (by positivity)]
          have : (t * Real.sqrt N - 1) * (t * Real.sqrt N) ≤ (m : ℝ) * (m + 1) := by
            rcases le_or_gt 1 (t * Real.sqrt N) with h | h
            · have : t * Real.sqrt N - 1 ≤ m := by linarith
              nlinarith
            · nlinarith [mul_nonneg ht hq0.le]
          nlinarith [mul_nonneg ht hq0.le]
        have hB : ((m : ℝ) + 1) * (v N / (1 - v N)) ≤ 2 * K * (t + 1) := by
          have h1 := vdiv_le (v N) hvh
          have h2 : ((m : ℝ) + 1) * (v N / (1 - v N)) ≤ ((m : ℝ) + 1) * (2 * |v N|) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
          have h3 : ((m : ℝ) + 1) * |v N| ≤ (t + 1) * K := by
            have : ((m : ℝ) + 1) ≤ (t + 1) * Real.sqrt N := by nlinarith
            have h4 : ((m : ℝ) + 1) * |v N| ≤ (t + 1) * Real.sqrt N * |v N| :=
              mul_le_mul_of_nonneg_right this (abs_nonneg _)
            nlinarith [abs_nonneg (v N)]
          nlinarith
        have : -((m : ℝ) * (m + 1) / 2) / Real.sqrt N ^ 2 =
            -(((m : ℝ) * (m + 1) / 2) / Real.sqrt N ^ 2) := by ring
        rw [this]
        nlinarith
      · rw [abs_zero]; exact (Real.exp_pos _).le)
  refine hmain.congr' (Eventually.of_forall fun N => ?_)
  simp only [hsumeq]


/-! ## Right side (abandonment products) -/

/-- right products `∏_{j<n} (1 - v)/(1 + c (j+1)/N)` = weight (N+n) / weight N. -/
noncomputable def uR (N : ℕ) (v c : ℝ) (n : ℕ) : ℝ :=
  ∏ j ∈ Finset.range n, (1 - v) / (1 + c * ((j : ℝ) + 1) / N)

theorem sum_range_succ_real (k : ℕ) :
    ∑ j ∈ Finset.range k, ((j : ℝ) + 1) = k * (k + 1) / 2 := by
  rw [Finset.sum_add_distrib, sum_range_id_real, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
  ring

theorem uR_nonneg (N : ℕ) (v c : ℝ) (hv : v < 1) (hc : 0 ≤ c) (n : ℕ) : 0 ≤ uR N v c n := by
  unfold uR
  refine Finset.prod_nonneg fun j _ => div_nonneg (by linarith) (by positivity)

theorem uR_upper (N : ℕ) (hN : 0 < N) (v c : ℝ) (hv : v < 1) (hc : 0 ≤ c) (n : ℕ) :
    uR N v c n ≤ Real.exp (-(n * v) - c * ((n : ℝ) * (n + 1) / 2) / (N + c * n)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hD : 0 < (N : ℝ) + c * n := by positivity
  unfold uR
  calc ∏ j ∈ Finset.range n, (1 - v) / (1 + c * ((j : ℝ) + 1) / N)
      ≤ ∏ j ∈ Finset.range n, Real.exp (-v - c * ((j : ℝ) + 1) / (N + c * n)) := by
        refine Finset.prod_le_prod (fun j _ => div_nonneg (by linarith) (by positivity))
          (fun j hj => ?_)
        have hjn : (j : ℝ) + 1 ≤ n := by
          have := Finset.mem_range.1 hj
          exact_mod_cast this
        have hu0 : 0 ≤ c * ((j : ℝ) + 1) / N := by positivity
        have e1 : 1 - v ≤ Real.exp (-v) := one_sub_le_exp_neg v
        have hx : c * ((j : ℝ) + 1) / (N + c * n) ≤ c * ((j : ℝ) + 1) / (N + c * ((j : ℝ) + 1)) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity)
            (by nlinarith)
        have e3 : 1 / (1 + c * ((j : ℝ) + 1) / N) =
            1 - c * ((j : ℝ) + 1) / (N + c * ((j : ℝ) + 1)) := by
          field_simp
          ring
        have e2 : 1 / (1 + c * ((j : ℝ) + 1) / N) ≤
            Real.exp (-(c * ((j : ℝ) + 1) / (N + c * n))) := by
          rw [e3]
          linarith [one_sub_le_exp_neg (c * ((j : ℝ) + 1) / (N + c * n))]
        calc (1 - v) / (1 + c * ((j : ℝ) + 1) / N)
            = (1 - v) * (1 / (1 + c * ((j : ℝ) + 1) / N)) := by ring
          _ ≤ Real.exp (-v) * Real.exp (-(c * ((j : ℝ) + 1) / (N + c * n))) :=
              mul_le_mul e1 e2 (by positivity) (Real.exp_pos _).le
          _ = Real.exp (-v - c * ((j : ℝ) + 1) / (N + c * n)) := by
              rw [← Real.exp_add]; ring_nf
    _ = _ := by
        rw [← Real.exp_sum]
        congr 1
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        have : ∑ j ∈ Finset.range n, c * ((j : ℝ) + 1) / (N + c * n) =
            c * (∑ j ∈ Finset.range n, ((j : ℝ) + 1)) / (N + c * n) := by
          rw [Finset.mul_sum, Finset.sum_div]
        rw [this, sum_range_succ_real]
        ring

theorem uR_lower (N : ℕ) (hN : 0 < N) (v c : ℝ) (hv : v < 1) (hc : 0 ≤ c) (n : ℕ) :
    Real.exp (-(n * (v / (1 - v))) - c * ((n : ℝ) * (n + 1) / 2) / N) ≤ uR N v c n := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  unfold uR
  calc Real.exp (-(n * (v / (1 - v))) - c * ((n : ℝ) * (n + 1) / 2) / N)
      = ∏ j ∈ Finset.range n, Real.exp (-(v / (1 - v)) - c * ((j : ℝ) + 1) / N) := by
        rw [← Real.exp_sum]
        congr 1
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        have : ∑ j ∈ Finset.range n, c * ((j : ℝ) + 1) / N =
            c * (∑ j ∈ Finset.range n, ((j : ℝ) + 1)) / N := by
          rw [Finset.mul_sum, Finset.sum_div]
        rw [this, sum_range_succ_real]
        ring
    _ ≤ ∏ j ∈ Finset.range n, (1 - v) / (1 + c * ((j : ℝ) + 1) / N) := by
        refine Finset.prod_le_prod (fun j _ => (Real.exp_pos _).le) (fun j _ => ?_)
        have hu0 : 0 ≤ c * ((j : ℝ) + 1) / N := by positivity
        have e1 := exp_neg_div_le v hv
        have e2 : Real.exp (-(c * ((j : ℝ) + 1) / N)) ≤ 1 / (1 + c * ((j : ℝ) + 1) / N) := by
          rw [le_div_iff₀ (by positivity)]
          have h1 := Real.add_one_le_exp (c * ((j : ℝ) + 1) / N)
          have h2 : Real.exp (-(c * ((j : ℝ) + 1) / N)) * Real.exp (c * ((j : ℝ) + 1) / N) = 1 := by
            rw [← Real.exp_add]; simp
          nlinarith [Real.exp_pos (-(c * ((j : ℝ) + 1) / N))]
        calc Real.exp (-(v / (1 - v)) - c * ((j : ℝ) + 1) / N)
            = Real.exp (-(v / (1 - v))) * Real.exp (-(c * ((j : ℝ) + 1) / N)) := by
              rw [← Real.exp_add]; ring_nf
          _ ≤ (1 - v) * (1 / (1 + c * ((j : ℝ) + 1) / N)) :=
              mul_le_mul e1 e2 (Real.exp_pos _).le (by linarith)
          _ = (1 - v) / (1 + c * ((j : ℝ) + 1) / N) := by ring

theorem uR_pt (v : ℕ → ℝ) (β c : ℝ) (hc0 : 0 ≤ c)
    (hc : Tendsto (fun n : ℕ => v n * Real.sqrt n) atTop (𝓝 β))
    (j : ℕ → ℕ) (y : ℝ) (ht : Tendsto (fun n : ℕ => (j n : ℝ) / Real.sqrt n) atTop (𝓝 y)) :
    Tendsto (fun n : ℕ => uR n (v n) c (j n)) atTop
      (𝓝 (Real.exp (-(β * y) - c * y ^ 2 / 2))) := by
  have hv := v_tendsto v β hc
  have hs : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (𝓝 0) :=
    tendsto_sqrt_nat.inv_tendsto_atTop
  have hU : Tendsto (fun n : ℕ =>
      -(((j n : ℝ) / Real.sqrt n) * (v n * Real.sqrt n)) -
        c * (((j n : ℝ) / Real.sqrt n) * ((j n : ℝ) / Real.sqrt n + (Real.sqrt n)⁻¹) / 2) /
          (1 + c * ((j n : ℝ) / Real.sqrt n) * (Real.sqrt n)⁻¹)) atTop
      (𝓝 (-(β * y) - c * y ^ 2 / 2)) := by
    have := (ht.mul hc).neg.sub ((((ht.mul (ht.add hs)).div_const 2).const_mul c).div
      ((tendsto_const_nhds (x := (1 : ℝ))).add ((ht.const_mul c).mul hs))
      (show (1 : ℝ) + c * y * 0 ≠ 0 by norm_num))
    have e : -(β * y) - c * y ^ 2 / 2 = -(y * β) - c * (y * (y + 0) / 2) / (1 + c * y * 0) := by
      ring
    rw [e]; exact this
  have hL : Tendsto (fun n : ℕ =>
      -(((j n : ℝ) / Real.sqrt n) * ((v n * Real.sqrt n) / (1 - v n))) -
        c * (((j n : ℝ) / Real.sqrt n) * ((j n : ℝ) / Real.sqrt n + (Real.sqrt n)⁻¹) / 2))
      atTop (𝓝 (-(β * y) - c * y ^ 2 / 2)) := by
    have := (ht.mul (hc.div (tendsto_const_nhds.sub hv) (show (1 : ℝ) - 0 ≠ 0 by norm_num))).neg.sub
      (((ht.mul (ht.add hs)).div_const 2).const_mul c)
    have e : -(β * y) - c * y ^ 2 / 2 = -(y * (β / (1 - 0))) - c * (y * (y + 0) / 2) := by ring
    rw [e]; exact this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hL.rexp hU.rexp ?_ ?_
  · filter_upwards [hv.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1)),
      tendsto_sqrt_nat.eventually_gt_atTop 0] with n h1 hq
    have hn : 0 < n := by
      have : (0 : ℝ) < n := Real.sqrt_pos.1 hq
      exact_mod_cast this
    have hn2 : (n : ℝ) = Real.sqrt n ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg n)).symm
    refine le_trans (le_of_eq ?_) (uR_lower n hn (v n) c h1 hc0 (j n))
    congr 1
    have h1' : 1 - v n ≠ 0 := by intro h; linarith
    generalize Real.sqrt (n : ℝ) = q at hq hn2 ⊢
    rw [hn2]
    field_simp
  · filter_upwards [hv.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1)),
      tendsto_sqrt_nat.eventually_gt_atTop 0] with n h1 hq
    have hn : 0 < n := by
      have : (0 : ℝ) < n := Real.sqrt_pos.1 hq
      exact_mod_cast this
    have hn2 : (n : ℝ) = Real.sqrt n ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg n)).symm
    refine le_trans (uR_upper n hn (v n) c h1 hc0 (j n)) (le_of_eq ?_)
    congr 1
    have hD : 0 < Real.sqrt n ^ 2 + c * (j n : ℝ) := by positivity
    have hD2 : 0 < 1 + c * ((j n : ℝ) / Real.sqrt n) * (Real.sqrt n)⁻¹ := by positivity
    generalize Real.sqrt (n : ℝ) = q at hq hn2 hD hD2 ⊢
    rw [hn2]
    field_simp


theorem gauss_gen (a b : ℝ) (ha : 0 < a) :
    Integrable (fun x : ℝ => Real.exp (-a * x ^ 2 + b * x)) := by
  have hg := ((integrable_exp_neg_mul_sq ha).comp_sub_right (b / (2 * a))).const_mul
    (Real.exp (b ^ 2 / (4 * a)))
  refine hg.congr (ae_of_all _ fun x => ?_)
  simp only
  rw [← Real.exp_add]
  congr 1
  field_simp
  ring

theorem expdecay_int (b d : ℝ) (hb : 0 < b) :
    Integrable (fun x : ℝ => Real.exp (d - b * x)) (volume.restrict (Set.Ici (0 : ℝ))) := by
  have h1 : IntegrableOn (fun x : ℝ => Real.exp (-b * x)) (Set.Ici 0) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact exp_neg_integrableOn_Ioi 0 hb
  have h2 := h1.integrable.const_mul (Real.exp d)
  refine h2.congr (ae_of_all _ fun x => ?_)
  simp only
  rw [← Real.exp_add]
  ring_nf

theorem uR_le_fact (N : ℕ) (hN : 0 < N) (v c : ℝ) (hv : v < 1) (hc : 0 < c) (n : ℕ) :
    uR N v c n ≤ ((1 - v) * N / c) ^ n / (Nat.factorial n : ℝ) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  induction n with
  | zero => simp [uR]
  | succ n ih =>
    have e : uR N v c (n + 1) = uR N v c n * ((1 - v) / (1 + c * ((n : ℝ) + 1) / N)) := by
      unfold uR; rw [Finset.prod_range_succ]
    rw [e, pow_succ, Nat.factorial_succ]
    push_cast
    have hf : (1 - v) / (1 + c * ((n : ℝ) + 1) / N) ≤ (1 - v) * N / c / ((n : ℝ) + 1) := by
      rw [div_div]
      have : (1 - v) * N / (c * ((n : ℝ) + 1)) = (1 - v) / (c * ((n : ℝ) + 1) / N) := by
        field_simp
      rw [this]
      exact div_le_div_of_nonneg_left (by linarith) (by positivity) (by linarith [show 0 ≤ (1:ℝ) by norm_num])
    calc uR N v c n * ((1 - v) / (1 + c * ((n : ℝ) + 1) / N))
        ≤ ((1 - v) * N / c) ^ n / (Nat.factorial n : ℝ) * ((1 - v) * N / c / ((n : ℝ) + 1)) :=
          mul_le_mul ih hf (div_nonneg (by linarith) (by positivity)) (by positivity)
      _ = _ := by field_simp

theorem uR_summable (N : ℕ) (hN : 0 < N) (v c : ℝ) (hv : v < 1) (hc : 0 < c) :
    Summable fun n => uR N v c n :=
  Summable.of_nonneg_of_le (fun n => uR_nonneg N v c hv hc.le n) (uR_le_fact N hN v c hv hc)
    (Real.summable_pow_div_factorial _)

theorem uR_dom (N : ℕ) (hN : 0 < N) (v c K : ℝ) (hc : 0 < c) (hK : 0 ≤ K)
    (hvK : |v| * Real.sqrt N ≤ K) (hv1 : v < 1) (hq : 4 * (K + 1) ≤ Real.sqrt N)
    (t : ℝ) (ht : 0 ≤ t) :
    uR N v c ⌊t * Real.sqrt N⌋₊ ≤
      Real.exp (-(c / 4) * t ^ 2 + (K + c / 4) * t) + Real.exp (1 / 4 - 1 * t) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hn2 : (N : ℝ) = Real.sqrt N ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg N)).symm
  have hq1 : 1 ≤ Real.sqrt N := by linarith
  generalize Real.sqrt (N : ℝ) = q at hvK hq hn2 hq1 ⊢
  have hq0 : 0 < q := by linarith
  set n := ⌊t * q⌋₊ with hndef
  have htq : 0 ≤ t * q := by positivity
  have hnle : (n : ℝ) ≤ t * q := Nat.floor_le htq
  have hngt : t * q < (n : ℝ) + 1 := Nat.lt_floor_add_one _
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  refine le_trans (uR_upper N hN v c hv1 hc.le n) ?_
  have hA : -((n : ℝ) * v) ≤ K * t := by
    have h1 : -((n : ℝ) * v) ≤ (n : ℝ) * |v| := by
      have := neg_abs_le v
      nlinarith
    have h2 : (n : ℝ) * |v| ≤ t * q * |v| := mul_le_mul_of_nonneg_right hnle (abs_nonneg v)
    have h3 : t * q * |v| ≤ t * K := by
      have : t * (|v| * q) ≤ t * K := mul_le_mul_of_nonneg_left hvK ht
      nlinarith
    linarith
  have hD : 0 < (N : ℝ) + c * n := by positivity
  rcases le_or_gt (c * ((n : ℝ) + 1)) N with hcase | hcase
  · have hm : (t * q) ^ 2 - t * q ≤ (n : ℝ) * (n + 1) := by
      rcases le_or_gt (1 / 2) (t * q) with h | h
      · nlinarith
      · nlinarith
    have hQ : c * t ^ 2 / 4 - c * t / 4 ≤ c * ((n : ℝ) * (n + 1) / 2) / (N + c * n) := by
      rw [le_div_iff₀ hD]
      rcases le_or_gt (c * t ^ 2 / 4 - c * t / 4) 0 with h | h
      · have : 0 ≤ c * ((n : ℝ) * (n + 1) / 2) := by positivity
        nlinarith
      · have h1 : (c * t ^ 2 / 4 - c * t / 4) * (N + c * n) ≤ (c * t ^ 2 / 4 - c * t / 4) * (2 * N) :=
          mul_le_mul_of_nonneg_left (by nlinarith) h.le
        have h2 : (c * t ^ 2 / 4 - c * t / 4) * (2 * N) ≤ c * (((t * q) ^ 2 - t * q) / 2) := by
          rw [hn2]
          have : t * q ≤ t * q ^ 2 := by nlinarith
          nlinarith
        have h3 : c * (((t * q) ^ 2 - t * q) / 2) ≤ c * ((n : ℝ) * (n + 1) / 2) := by
          apply mul_le_mul_of_nonneg_left _ hc.le; linarith
        linarith
    have : -((n : ℝ) * v) - c * ((n : ℝ) * (n + 1) / 2) / (N + c * n) ≤
        -(c / 4) * t ^ 2 + (K + c / 4) * t := by nlinarith
    exact le_trans (Real.exp_le_exp.2 this) (le_add_of_nonneg_right (Real.exp_pos _).le)
  · have hQ : (n : ℝ) / 4 ≤ c * ((n : ℝ) * (n + 1) / 2) / (N + c * n) := by
      rw [le_div_iff₀ hD]
      have : (n : ℝ) * N ≤ (n : ℝ) * (c * ((n : ℝ) + 1)) := mul_le_mul_of_nonneg_left hcase.le hn0
      nlinarith
    have h4 : (K + 1) * t - 1 / 4 ≤ (n : ℝ) / 4 := by
      have : 4 * (K + 1) * t ≤ q * t := mul_le_mul_of_nonneg_right hq ht
      nlinarith
    have : -((n : ℝ) * v) - c * ((n : ℝ) * (n + 1) / 2) / (N + c * n) ≤ 1 / 4 - 1 * t := by
      nlinarith
    exact le_trans (Real.exp_le_exp.2 this) (le_add_of_nonneg_left (Real.exp_pos _).le)

/-- `SA = Σ' uR` (= Σ_{k ≥ N} weight k / weight N). -/
noncomputable def SA (N : ℕ) (v c : ℝ) : ℝ := ∑' n, uR N v c n

/-- `SC = Σ' uR · u/(1+u)`, `u = c (n+1)/N` (abandonment-weighted). -/
noncomputable def SC (N : ℕ) (v c : ℝ) : ℝ :=
  ∑' n, uR N v c n * (c * ((n : ℝ) + 1) / N / (1 + c * ((n : ℝ) + 1) / N))

theorem dom_events (v : ℕ → ℝ) (β : ℝ)
    (hc : Tendsto (fun n : ℕ => v n * Real.sqrt n) atTop (𝓝 β)) :
    ∀ᶠ N : ℕ in atTop, 0 < N ∧ |v N| * Real.sqrt N ≤ |β| + 1 ∧ v N < 1 ∧
      4 * ((|β| + 1) + 1) ≤ Real.sqrt N := by
  have h1 := (hc.abs.eventually (gt_mem_nhds (show |β| < |β| + 1 by linarith))).and
    ((tendsto_sqrt_nat.eventually_ge_atTop (4 * ((|β| + 1) + 1))).and (eventually_ge_atTop 1))
  filter_upwards [h1] with N ⟨h2, h3, h4⟩
  have hq0 : 0 < Real.sqrt N := lt_of_lt_of_le (by positivity) h3
  have h5 : |v N| * Real.sqrt N < |β| + 1 := by
    rw [← abs_of_pos hq0, ← abs_mul]; exact h2
  refine ⟨h4, h5.le, ?_, h3⟩
  have : |v N| < 1 := by
    by_contra hh
    push Not at hh
    nlinarith [abs_nonneg β]
  linarith [le_abs_self (v N)]

theorem right_lim (v : ℕ → ℝ) (β c : ℝ) (hc0 : 0 < c)
    (hc : Tendsto (fun n : ℕ => v n * Real.sqrt n) atTop (𝓝 β)) :
    Tendsto (fun N : ℕ => (Real.sqrt N)⁻¹ * SA N (v N) c) atTop
      (𝓝 (∫ t in Set.Ici (0 : ℝ), Real.exp (-(β * t) - c * t ^ 2 / 2))) := by
  set K : ℝ := |β| + 1
  exact step_dct (fun N n => uR N (v N) c n) (fun t => Real.exp (-(β * t) - c * t ^ 2 / 2))
    (fun t => Real.exp (-(c / 4) * t ^ 2 + (K + c / 4) * t) + Real.exp (1 / 4 - 1 * t))
    ((dom_events v β hc).mono fun N ⟨hN, _, hv1, _⟩ => by
      simp_rw [abs_of_nonneg (uR_nonneg N (v N) c hv1 hc0.le _)]
      exact uR_summable N hN (v N) c hv1 hc0)
    (fun t ht => uR_pt v β c hc0.le hc (fun n => ⌊t * Real.sqrt n⌋₊) t (tendsto_floor_div t ht))
    (((gauss_gen _ _ (by positivity)).restrict).add (expdecay_int _ _ one_pos))
    ((dom_events v β hc).mono fun N ⟨hN, hvK, hv1, hq⟩ t ht => by
      rw [abs_of_nonneg (uR_nonneg N (v N) c hv1 hc0.le _)]
      exact uR_dom N hN (v N) c K hc0 (by positivity) hvK hv1 hq t ht)

theorem rightC_lim (v : ℕ → ℝ) (β c : ℝ) (hc0 : 0 < c)
    (hc : Tendsto (fun n : ℕ => v n * Real.sqrt n) atTop (𝓝 β)) :
    Tendsto (fun N : ℕ => SC N (v N) c) atTop
      (𝓝 (∫ t in Set.Ici (0 : ℝ), Real.exp (-(β * t) - c * t ^ 2 / 2) * (c * t))) := by
  set K : ℝ := |β| + 1
  have hfac : ∀ (N : ℕ) (x : ℝ), 0 ≤ x → 0 ≤ x / (1 + x) ∧ x / (1 + x) ≤ x := by
    intro N x hx
    refine ⟨by positivity, ?_⟩
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hmain := step_dct
    (fun N n => Real.sqrt N * (uR N (v N) c n * (c * ((n : ℝ) + 1) / N / (1 + c * ((n : ℝ) + 1) / N))))
    (fun t => Real.exp (-(β * t) - c * t ^ 2 / 2) * (c * t))
    (fun t => 2 * c * (Real.exp (-(c / 4) * t ^ 2 + (K + c / 4 + 1 / 2) * t) +
      Real.exp (1 / 4 - (1 / 2) * t)))
    ((dom_events v β hc).mono fun N ⟨hN, _, hv1, _⟩ => by
      have hNr : (0 : ℝ) < N := by exact_mod_cast hN
      refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_)
        ((uR_summable N hN (v N) c hv1 hc0).mul_left (Real.sqrt N))
      have h0 := uR_nonneg N (v N) c hv1 hc0.le n
      have hx := hfac N (c * ((n : ℝ) + 1) / N) (by positivity)
      rw [abs_of_nonneg (by have := hx.1; positivity)]
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      calc uR N (v N) c n * (c * ((n : ℝ) + 1) / N / (1 + c * ((n : ℝ) + 1) / N))
          ≤ uR N (v N) c n * 1 := by
            apply mul_le_mul_of_nonneg_left _ h0
            rw [div_le_one (by positivity)]; linarith
        _ = uR N (v N) c n := mul_one _)
    (fun t ht => by
      have h1 := uR_pt v β c hc0.le hc (fun n => ⌊t * Real.sqrt n⌋₊) t (tendsto_floor_div t ht)
      have hs : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (𝓝 0) :=
        tendsto_sqrt_nat.inv_tendsto_atTop
      have hJ := tendsto_floor_div t ht
      have h2 : Tendsto (fun n : ℕ => c * ((⌊t * Real.sqrt n⌋₊ : ℝ) / Real.sqrt n + (Real.sqrt n)⁻¹) /
          (1 + c * ((⌊t * Real.sqrt n⌋₊ : ℝ) / Real.sqrt n + (Real.sqrt n)⁻¹) * (Real.sqrt n)⁻¹))
          atTop (𝓝 (c * t)) := by
        have := ((hJ.add hs).const_mul c).div
          ((tendsto_const_nhds (x := (1 : ℝ))).add (((hJ.add hs).const_mul c).mul hs))
          (show (1 : ℝ) + c * (t + 0) * 0 ≠ 0 by norm_num)
        have e : c * (t + 0) / (1 + c * (t + 0) * 0) = c * t := by simp
        rw [e] at this
        exact this
      refine (h1.mul h2).congr' ?_
      filter_upwards [tendsto_sqrt_nat.eventually_gt_atTop 0] with n hq
      have hn2 : (n : ℝ) = Real.sqrt n ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg n)).symm
      generalize Real.sqrt (n : ℝ) = q at hq hn2 ⊢
      rw [hn2]
      have : 0 < q ^ 2 + c * ((⌊t * q⌋₊ : ℝ) + 1) := by positivity
      field_simp)
    (by
      refine Integrable.const_mul ?_ _
      exact ((gauss_gen _ _ (by positivity)).restrict).add (expdecay_int _ _ (by norm_num)))
    ((dom_events v β hc).mono fun N ⟨hN, hvK, hv1, hq⟩ t ht => by
      have hNr : (0 : ℝ) < N := by exact_mod_cast hN
      have hd := uR_dom N hN (v N) c K hc0 (by positivity) hvK hv1 hq t ht
      have hn2 : (N : ℝ) = Real.sqrt N ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg N)).symm
      have hq1 : 1 ≤ Real.sqrt N := by linarith [abs_nonneg β]
      set n := ⌊t * Real.sqrt N⌋₊ with hndef
      have h0 := uR_nonneg N (v N) c hv1 hc0.le n
      have hx := hfac N (c * ((n : ℝ) + 1) / N) (by positivity)
      have hnle : (n : ℝ) ≤ t * Real.sqrt N := Nat.floor_le (by positivity)
      rw [abs_of_nonneg (by have := hx.1; positivity)]
      have hE : t + 1 ≤ 2 * Real.exp (t / 2) := by linarith [Real.add_one_le_exp (t / 2)]
      have hst : Real.sqrt N * (c * ((n : ℝ) + 1) / N) ≤ c * (t + 1) := by
        have hq0 : 0 < Real.sqrt N := by linarith
        have hnle' := hnle
        generalize Real.sqrt (N : ℝ) = q at hn2 hq0 hq1 hnle' ⊢
        rw [hn2]
        rw [show q * (c * ((n : ℝ) + 1) / q ^ 2) = c * (((n : ℝ) + 1) / q) by
          field_simp]
        apply mul_le_mul_of_nonneg_left _ hc0.le
        rw [div_le_iff₀ hq0]; nlinarith
      calc Real.sqrt N * (uR N (v N) c n * (c * ((n : ℝ) + 1) / N / (1 + c * ((n : ℝ) + 1) / N)))
          ≤ Real.sqrt N * (uR N (v N) c n * (c * ((n : ℝ) + 1) / N)) := by
            apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
            exact mul_le_mul_of_nonneg_left hx.2 h0
        _ = uR N (v N) c n * (Real.sqrt N * (c * ((n : ℝ) + 1) / N)) := by ring
        _ ≤ (Real.exp (-(c / 4) * t ^ 2 + (K + c / 4) * t) + Real.exp (1 / 4 - 1 * t)) *
              (c * (2 * Real.exp (t / 2))) := by
            apply mul_le_mul hd (le_trans hst (mul_le_mul_of_nonneg_left hE hc0.le))
              (by positivity) (by positivity)
        _ = _ := by
            rw [add_mul, mul_add]
            simp only [mul_comm, mul_left_comm, mul_assoc]
            rw [← Real.exp_add, ← Real.exp_add]
            ring_nf)
  refine hmain.congr' ?_
  filter_upwards [tendsto_sqrt_nat.eventually_gt_atTop 0] with N hN
  rw [tsum_mul_left, ← mul_assoc, inv_mul_cancel₀ hN.ne', one_mul]
  rfl


/-! ## C1: exact structure of probWait / probAbandon -/

open ErlangA.Abandonment in
theorem w_right (N : ℕ) (lam μ θ : ℝ) (n : ℕ) :
    weight N lam μ θ (N + n) =
      (∏ j ∈ Finset.Icc (N + 1) (N + n), lam / ((N : ℝ) * μ + ((j - N : ℕ) : ℝ) * θ)) *
        ((lam / μ) ^ N / (Nat.factorial N : ℝ)) := by
  unfold weight
  split_ifs with h
  · have hn : n = 0 := by omega
    subst hn
    simp
  · rfl

theorem prod_eq_uR (N : ℕ) (hN : 0 < N) (lam μ θ : ℝ) (hμ : 0 < μ) (n : ℕ) :
    (∏ j ∈ Finset.Icc (N + 1) (N + n), lam / ((N : ℝ) * μ + ((j - N : ℕ) : ℝ) * θ)) =
      uR N (1 - lam / (N * μ)) (θ / μ) n := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  induction n with
  | zero =>
    rw [Finset.Icc_eq_empty (by omega)]
    simp [uR]
  | succ n ih =>
    rw [show N + (n + 1) = (N + n) + 1 by ring, Finset.prod_Icc_succ_top (by omega), ih]
    unfold uR
    rw [Finset.prod_range_succ]
    congr 1
    have e : (N + n + 1 - N : ℕ) = n + 1 := by omega
    rw [e]
    push_cast
    field_simp
    ring

open ErlangA.Abandonment in
theorem w_left (N : ℕ) (hN : 0 < N) (lam μ θ : ℝ) (hl : 0 < lam) (hμ : 0 < μ) (j : ℕ)
    (hj : j ≤ N) :
    weight N lam μ θ (N - j) = uL N (1 - lam / (N * μ)) j *
      ((lam / μ) ^ N / (Nat.factorial N : ℝ)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  induction j with
  | zero => simp [weight, uL]
  | succ j ih =>
    have ih' := ih (by omega)
    obtain ⟨m, hm⟩ : ∃ m, N = m + (j + 1) := ⟨N - (j + 1), by omega⟩
    have e1 : N - (j + 1) = m := by omega
    have e2 : N - j = m + 1 := by omega
    rw [e2] at ih'
    rw [e1]
    have hmr : (N : ℝ) = m + j + 1 := by rw [hm]; push_cast; ring
    unfold weight at ih' ⊢
    rw [if_pos (by omega)] at ih'
    rw [if_pos (by omega)]
    have hu : uL N (1 - lam / (N * μ)) (j + 1) =
        uL N (1 - lam / (N * μ)) j * ((1 - (j : ℝ) / N) / (1 - (1 - lam / (N * μ)))) := by
      unfold uL; rw [Finset.prod_range_succ]
    rw [hu, mul_assoc, mul_comm ((1 - (j : ℝ) / N) / (1 - (1 - lam / (N * μ)))), ← mul_assoc, ← ih']
    rw [pow_succ, Nat.factorial_succ]
    push_cast
    rw [hmr]
    have hl0 : lam ≠ 0 := hl.ne'
    have hμ0 : μ ≠ 0 := hμ.ne'
    have hmj : (m : ℝ) + j + 1 ≠ 0 := by positivity
    have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
    rw [sub_sub_cancel]
    field_simp
    ring

open ErlangA.Abandonment in
theorem weight_summable (N : ℕ) (hN : 0 < N) (lam μ θ : ℝ) (hl : 0 < lam) (hμ : 0 < μ)
    (hθ : 0 < θ) : Summable (weight N lam μ θ) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hv : 1 - lam / (N * μ) < 1 := by
    have : 0 < lam / (N * μ) := by positivity
    linarith
  rw [← summable_nat_add_iff N]
  have h := (uR_summable N hN _ (θ / μ) hv (by positivity)).mul_right
    ((lam / μ) ^ N / (Nat.factorial N : ℝ))
  refine h.congr fun n => ?_
  rw [add_comm n N, w_right, prod_eq_uR N hN lam μ θ hμ]

open ErlangA.Abandonment in
theorem struct (N : ℕ) (hN : 0 < N) (lam μ θ : ℝ) (hl : 0 < lam) (hμ : 0 < μ) (hθ : 0 < θ) :
    ErlangA.Staffing.probWait N lam μ θ =
        SA N (1 - lam / (N * μ)) (θ / μ) /
          (SA N (1 - lam / (N * μ)) (θ / μ) + SB N (1 - lam / (N * μ))) ∧
      probAbandon N lam μ θ =
        SC N (1 - lam / (N * μ)) (θ / μ) /
          (SA N (1 - lam / (N * μ)) (θ / μ) + SB N (1 - lam / (N * μ))) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set v := 1 - lam / (N * μ) with hvdef
  set c := θ / μ with hcdef
  have hv : v < 1 := by
    have : 0 < lam / (N * μ) := by positivity
    linarith
  set wN := (lam / μ) ^ N / (Nat.factorial N : ℝ) with hwN
  have hwN0 : 0 < wN := by positivity
  have hR : ∀ n, weight N lam μ θ (N + n) = uR N v c n * wN := by
    intro n; rw [w_right, prod_eq_uR N hN lam μ θ hμ]
  have hsum := weight_summable N hN lam μ θ hl hμ hθ
  have hT : ∑' j, weight N lam μ θ j = wN * (SA N v c + SB N v) := by
    rw [← hsum.sum_add_tsum_nat_add N]
    have h1 : ∑' i, weight N lam μ θ (i + N) = wN * SA N v c := by
      unfold SA
      rw [← tsum_mul_left]
      congr 1; funext n; rw [add_comm, hR]; ring
    have h2 : ∑ i ∈ Finset.range N, weight N lam μ θ i = wN * SB N v := by
      unfold SB
      rw [Finset.mul_sum, ← Finset.sum_range_reflect]
      refine Finset.sum_congr rfl fun m hm => ?_
      have hm' := Finset.mem_range.1 hm
      rw [show N - 1 - m = N - (m + 1) by omega, w_left N hN lam μ θ hl hμ (m + 1) (by omega)]
      ring
    rw [h1, h2]; ring
  have hSA0 : 0 ≤ SA N v c := tsum_nonneg fun n => uR_nonneg N v c hv (by positivity) n
  constructor
  · unfold ErlangA.Staffing.probWait stationaryDist
    rw [hT]
    simp_rw [hR]
    rw [tsum_div_const, tsum_mul_right]
    unfold SA
    field_simp
  · unfold probAbandon stationaryDist
    rw [hT]
    simp_rw [hR]
    unfold SC
    rw [div_eq_mul_inv (∑' n, _), ← tsum_mul_right]
    congr 1; funext n
    have hD : 0 < (N : ℝ) * μ + ((n : ℝ) + 1) * θ := by positivity
    rw [hcdef]
    field_simp


open DimCallCenters.Rationalized

/-! ## Gaussian helpers (from DimCC1e7h) -/

theorem stdPdf_pos (x : ℝ) : 0 < stdPdf x := by unfold stdPdf; positivity

theorem stdPdf_int : Integrable stdPdf := by
  have : stdPdf = fun x => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1/2) * x ^ 2) := by
    funext x; unfold stdPdf; congr 2; ring
  rw [this]
  exact (integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/2)).const_mul _

theorem stdPdf_total : ∫ x, stdPdf x = 1 := by
  have : stdPdf = fun x => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1/2) * x ^ 2) := by
    funext x; unfold stdPdf; congr 2; ring
  rw [this, integral_const_mul, integral_gaussian]
  have h1 : Real.pi / (1/2) = 2 * Real.pi := by ring
  rw [h1]
  have : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  field_simp

theorem one_sub_cdf' (x : ℝ) : 1 - stdCdf x = ∫ t in Set.Ioi x, stdPdf t := by
  unfold stdCdf
  rw [← stdPdf_total, ← integral_add_compl (measurableSet_Iic (a := x)) stdPdf_int,
    Set.compl_Iic]
  ring

theorem pos_Ioi (f : ℝ → ℝ) (hf : ∀ t, 0 < t → 0 < f t) (hi : IntegrableOn f (Set.Ioi 0)) :
    0 < ∫ t in Set.Ioi (0:ℝ), f t := by
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => (hf t ht).le)) hi]
  have : Function.support f ∩ Set.Ioi 0 = Set.Ioi 0 :=
    Set.inter_eq_right.2 (fun t ht => (hf t ht).ne')
  rw [this, Real.volume_Ioi]; exact ENNReal.zero_lt_top

theorem Q_pos (x : ℝ) : 0 < ∫ t in Set.Ioi x, stdPdf t := by
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    (Eventually.of_forall (fun t => (stdPdf_pos t).le)) stdPdf_int.integrableOn]
  have : Function.support stdPdf = Set.univ :=
    Set.eq_univ_of_forall (fun t => (stdPdf_pos t).ne')
  rw [this, Set.univ_inter, Real.volume_Ioi]
  exact ENNReal.zero_lt_top

theorem hazard_pos (x : ℝ) : 0 < hazard x := by
  unfold hazard; rw [one_sub_cdf']; exact div_pos (stdPdf_pos x) (Q_pos x)

/-! ## The integrals IA y c = ∫_0^∞ e^{-yt-ct²/2}, IC = ∫ e^{..}·ct -/

noncomputable def EE (y c t : ℝ) : ℝ := Real.exp (-(y * t) - c * t ^ 2 / 2)
noncomputable def IA (y c : ℝ) : ℝ := ∫ t in Set.Ioi (0:ℝ), EE y c t
noncomputable def IC (y c : ℝ) : ℝ := ∫ t in Set.Ioi (0:ℝ), EE y c t * (c * t)

theorem EE_pos (y c t : ℝ) : 0 < EE y c t := Real.exp_pos _

theorem EE_le (y c t : ℝ) (hc : 0 < c) :
    EE y c t ≤ Real.exp (y ^ 2 / c) * Real.exp (-(c / 4) * t ^ 2) := by
  unfold EE; rw [← Real.exp_add]; apply Real.exp_le_exp.2
  have h0 : 0 ≤ (c * t / 2 + y) ^ 2 / c := by positivity
  have e : (c * t / 2 + y) ^ 2 / c = y ^ 2 / c + c * t ^ 2 / 4 + y * t := by
    field_simp; ring
  nlinarith

theorem EE_int (y c : ℝ) (hc : 0 < c) : Integrable (fun t => EE y c t) := by
  refine Integrable.mono' ((integrable_exp_neg_mul_sq (b := c / 4) (by positivity)).const_mul
    (Real.exp (y ^ 2 / c))) (by unfold EE; fun_prop : Continuous _).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (EE_pos y c t)]; exact EE_le y c t hc

theorem tEE_int (y c : ℝ) (hc : 0 < c) : Integrable (fun t => t * EE y c t) := by
  refine Integrable.mono' (((integrable_mul_exp_neg_mul_sq (b := c / 4) (by positivity)).norm).const_mul
    (Real.exp (y ^ 2 / c))) (by unfold EE; fun_prop : Continuous _).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (EE_pos y c t),
    abs_of_pos (Real.exp_pos (-(c / 4) * t ^ 2))]
  have := EE_le y c t hc
  calc |t| * EE y c t ≤ |t| * (Real.exp (y ^ 2 / c) * Real.exp (-(c / 4) * t ^ 2)) :=
        mul_le_mul_of_nonneg_left this (abs_nonneg t)
    _ = _ := by ring

theorem ICi_int (y c : ℝ) (hc : 0 < c) : Integrable (fun t => EE y c t * (c * t)) :=
  ((tEE_int y c hc).const_mul c).congr (ae_of_all _ fun t => by simp only; ring)

theorem IA_pos (y c : ℝ) (hc : 0 < c) : 0 < IA y c :=
  pos_Ioi _ (fun t _ => Real.exp_pos _) (EE_int y c hc).integrableOn

theorem IC_pos (y c : ℝ) (hc : 0 < c) : 0 < IC y c :=
  pos_Ioi _ (fun t ht => mul_pos (Real.exp_pos _) (mul_pos hc ht)) (ICi_int y c hc).integrableOn

/-- IBP: `IC = 1 - y IA`. -/
theorem IC_eq (y c : ℝ) (hc : 0 < c) : IC y c = 1 - y * IA y c := by
  have hlim : Tendsto (fun t : ℝ => -EE y c t) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => -(c / 4) * t ^ 2) atTop atBot := by
      have := (tendsto_pow_atTop (two_ne_zero)).const_mul_atTop (show (0:ℝ) < c / 4 by positivity)
      have h2 := tendsto_neg_atTop_atBot.comp this
      refine h2.congr (fun t => ?_)
      simp [neg_mul]
    have h2 := (Real.tendsto_exp_atBot.comp h1).const_mul (Real.exp (y ^ 2 / c))
    rw [mul_zero] at h2
    have h3 : Tendsto (fun t : ℝ => EE y c t) atTop (𝓝 0) :=
      squeeze_zero (fun t => (Real.exp_pos _).le) (fun t => EE_le y c t hc) h2
    simpa using h3.neg
  have hint : Integrable (fun t => (y + c * t) * EE y c t) :=
    (((EE_int y c hc).const_mul y).add ((tEE_int y c hc).const_mul c)).congr
      (ae_of_all _ fun t => by simp only [Pi.add_apply]; ring)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto (f := fun t => -EE y c t)
    (f' := fun t => (y + c * t) * EE y c t) (a := 0) (m := 0)
    (by unfold EE; fun_prop : Continuous fun t : ℝ => -EE y c t).continuousWithinAt
    (fun t _ => by
      have hp : HasDerivAt (fun t : ℝ => t ^ 2) (2 * t) t := by simpa using hasDerivAt_pow 2 t
      have hd : HasDerivAt (fun t : ℝ => -(y * t) - c * t ^ 2 / 2) (-(y + c * t)) t := by
        have := ((hasDerivAt_id' t).const_mul y).neg.sub ((hp.const_mul c).div_const 2)
        exact this.congr_deriv (by ring)
      have h2 : HasDerivAt (fun t => -EE y c t)
          (-(Real.exp (-(y * t) - c * t ^ 2 / 2) * (-(y + c * t)))) t := hd.exp.neg
      show HasDerivAt _ ((y + c * t) * EE y c t) t
      exact h2.congr_deriv (by unfold EE; ring))
    hint.integrableOn hlim
  have hsplit : ∫ t in Set.Ioi (0:ℝ), (y + c * t) * EE y c t = y * IA y c + IC y c := by
    unfold IA IC
    rw [← integral_const_mul, ← integral_add ((EE_int y c hc).const_mul y).integrableOn
      (ICi_int y c hc).integrableOn]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    ring
  have h0 : EE y c 0 = 1 := by unfold EE; simp
  rw [hsplit, h0] at h
  linarith

/-- `IA x 1 = 1 / h(x)`. -/
theorem IA_one (x : ℝ) : IA x 1 = 1 / hazard x := by
  unfold IA hazard
  rw [one_sub_cdf', one_div_div, eq_div_iff (stdPdf_pos x).ne', ← integral_mul_const]
  have hs : ∫ w in Set.Ioi (0:ℝ), stdPdf (w + x) = ∫ u in Set.Ioi x, stdPdf u := by
    rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
    refine Eq.trans ?_ (integral_add_right_eq_self (μ := volume)
      (fun u => (Set.Ioi x).indicator stdPdf u) x)
    congr 1
    ext w
    simp only [Set.indicator, Set.mem_Ioi]
    by_cases h : 0 < w
    · rw [if_pos h, if_pos (by linarith)]
    · rw [if_neg h, if_neg (by linarith)]
  rw [← hs]
  refine setIntegral_congr_fun measurableSet_Ioi (fun w _ => ?_)
  unfold EE stdPdf
  rw [show -(w + x) ^ 2 / 2 = (-(x * w) - 1 * w ^ 2 / 2) + (-x ^ 2 / 2) by ring, Real.exp_add]
  ring

/-- scaling: `IA y c = 1 / (√c · h(y/√c))`. -/
theorem IA_closed (y c : ℝ) (hc : 0 < c) :
    IA y c = 1 / (Real.sqrt c * hazard (y / Real.sqrt c)) := by
  have ha : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hsq : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc.le
  have h := integral_comp_mul_left_Ioi (fun s => EE (y / Real.sqrt c) 1 s) 0 ha
  rw [mul_zero] at h
  have h2 : IA y c = (Real.sqrt c)⁻¹ * IA (y / Real.sqrt c) 1 := by
    unfold IA
    rw [← smul_eq_mul, ← h]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    unfold EE
    congr 1
    field_simp
    rw [hsq]
  rw [h2, IA_one]
  field_simp

/-! ## Monotonicity -/

theorem IA_strictAnti (c : ℝ) (hc : 0 < c) : StrictAnti (fun y => IA y c) := by
  intro y1 y2 h
  show IA y2 c < IA y1 c
  have hpos : 0 < ∫ t in Set.Ioi (0:ℝ), (EE y1 c t - EE y2 c t) :=
    pos_Ioi _ (fun t ht => by
      unfold EE
      have : -(y2 * t) - c * t ^ 2 / 2 < -(y1 * t) - c * t ^ 2 / 2 := by nlinarith
      linarith [Real.exp_lt_exp.2 this])
      ((EE_int y1 c hc).sub (EE_int y2 c hc)).integrableOn
  rw [integral_sub (EE_int y1 c hc).integrableOn (EE_int y2 c hc).integrableOn] at hpos
  unfold IA; linarith

noncomputable def FF (y c : ℝ) : ℝ := IA y c / (IA y c + IA (-y) 1)
noncomputable def GG (y c : ℝ) : ℝ := IC y c / (IA y c + IA (-y) 1)

theorem FF_strictAnti (c : ℝ) (hc : 0 < c) : StrictAnti (fun y => FF y c) := by
  intro y1 y2 h
  show FF y2 c < FF y1 c
  have ha := IA_strictAnti c hc h
  have hb := IA_strictAnti 1 one_pos (show -y2 < -y1 by linarith)
  simp only at ha hb
  have p1 := IA_pos y1 c hc
  have p2 := IA_pos y2 c hc
  have q1 := IA_pos (-y1) 1 one_pos
  have q2 := IA_pos (-y2) 1 one_pos
  unfold FF
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_lt_mul_of_pos_left ha q1, mul_lt_mul_of_pos_left hb p1]

theorem lin4 {μ' : Measure ℝ} (f1 g1 f2 g2 : ℝ → ℝ) (K m : ℝ) (h1 : Integrable f1 μ')
    (h2 : Integrable g1 μ') (h3 : Integrable f2 μ') (h4 : Integrable g2 μ') :
    ∫ t, (K * f1 t - K * m * g1 t - (f2 t - m * g2 t)) ∂μ' =
      K * ∫ t, f1 t ∂μ' - K * m * ∫ t, g1 t ∂μ' - (∫ t, f2 t ∂μ' - m * ∫ t, g2 t ∂μ') := by
  rw [integral_sub, integral_sub, integral_sub, integral_const_mul, integral_const_mul,
    integral_const_mul]
  all_goals first
    | exact h1.const_mul _ | exact h2.const_mul _ | exact h3 | exact h4.const_mul _
    | exact (h1.const_mul _).sub (h2.const_mul _) | exact h3.sub (h4.const_mul _)

/-- the tilted mean `IC/IA` is nonincreasing in `y` (pointwise covariance trick). -/
theorem ratio_anti (c : ℝ) (hc : 0 < c) (y1 y2 : ℝ) (h : y1 ≤ y2) :
    IC y2 c * IA y1 c ≤ IC y1 c * IA y2 c := by
  set m := IC y1 c / IA y1 c with hm
  set d := y2 - y1 with hd
  set K := Real.exp (-(d * (m / c))) with hK
  have hA1 := IA_pos y1 c hc
  have hd0 : 0 ≤ d := by rw [hd]; linarith
  have hEE : ∀ t, EE y2 c t = EE y1 c t * Real.exp (-(d * t)) := by
    intro t; unfold EE; rw [← Real.exp_add]; congr 1; rw [hd]; ring
  have hpt : ∀ t, 0 ≤ K * (EE y1 c t * (c * t)) - K * m * EE y1 c t -
      (EE y2 c t * (c * t) - m * EE y2 c t) := by
    intro t
    have hE := EE_pos y1 c t
    have key : 0 ≤ (m - c * t) * (Real.exp (-(d * t)) - K) := by
      rcases le_total (c * t) m with h1 | h1
      · have ht : t ≤ m / c := by rw [le_div_iff₀ hc]; linarith
        have : -(d * (m / c)) ≤ -(d * t) := by nlinarith
        have := Real.exp_le_exp.2 this
        exact mul_nonneg (by linarith) (by rw [hK]; linarith)
      · have ht : m / c ≤ t := by rw [div_le_iff₀ hc]; linarith
        have : -(d * t) ≤ -(d * (m / c)) := by nlinarith
        have := Real.exp_le_exp.2 this
        exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by rw [hK]; linarith)
    rw [hEE]
    nlinarith [mul_nonneg hE.le key]
  have hge := setIntegral_nonneg (μ := volume) measurableSet_Ioi (fun t (_ : t ∈ Set.Ioi (0:ℝ)) => hpt t)
  rw [lin4 (fun t => EE y1 c t * (c * t)) (fun t => EE y1 c t) (fun t => EE y2 c t * (c * t))
    (fun t => EE y2 c t) K m (ICi_int y1 c hc).integrableOn (EE_int y1 c hc).integrableOn
    (ICi_int y2 c hc).integrableOn (EE_int y2 c hc).integrableOn] at hge
  change 0 ≤ K * IC y1 c - K * m * IA y1 c - (IC y2 c - m * IA y2 c) at hge
  have hmA : m * IA y1 c = IC y1 c := by rw [hm]; field_simp
  have hKm : K * m * IA y1 c = K * IC y1 c := by rw [mul_assoc, hmA]
  have : IC y2 c ≤ m * IA y2 c := by linarith
  calc IC y2 c * IA y1 c ≤ m * IA y2 c * IA y1 c := mul_le_mul_of_nonneg_right this hA1.le
    _ = IC y1 c * IA y2 c := by rw [← hmA]; ring

theorem GG_strictAnti (c : ℝ) (hc : 0 < c) : StrictAnti (fun y => GG y c) := by
  intro y1 y2 h
  show GG y2 c < GG y1 c
  have hF := FF_strictAnti c hc h
  simp only at hF
  have hr := ratio_anti c hc y1 y2 h.le
  have p1 := IA_pos y1 c hc
  have p2 := IA_pos y2 c hc
  have q1 := IA_pos (-y1) 1 one_pos
  have q2 := IA_pos (-y2) 1 one_pos
  have c1 := IC_pos y1 c hc
  have c2 := IC_pos y2 c hc
  unfold FF at hF
  rw [div_lt_div_iff₀ (by positivity) (by positivity)] at hF
  unfold GG
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have key : IC y2 c * (IA y1 c + IA (-y1) 1) * IA y1 c <
      IC y1 c * (IA y2 c + IA (-y2) 1) * IA y1 c := by
    nlinarith [mul_le_mul_of_nonneg_right hr (show 0 ≤ IA y1 c + IA (-y1) 1 by positivity),
      mul_lt_mul_of_pos_left hF c1]
  exact lt_of_mul_lt_mul_right key p1.le

/-! ## Range bounds -/

theorem expI (b : ℝ) (hb : 0 < b) : ∫ t in Set.Ioi (0:ℝ), Real.exp (-b * t) = 1 / b := by
  rw [integral_exp_mul_Ioi (by linarith : -b < 0) 0, mul_zero, Real.exp_zero, neg_div_neg_eq]

theorem IA_le (y c : ℝ) (hy : 0 < y) (hc : 0 < c) : IA y c ≤ 1 / y := by
  rw [← expI y hy]; unfold IA
  refine setIntegral_mono_on (EE_int y c hc).integrableOn (exp_neg_integrableOn_Ioi 0 hy)
    measurableSet_Ioi (fun t _ => ?_)
  unfold EE; apply Real.exp_le_exp.2; nlinarith [sq_nonneg t]

theorem IC_le (y c : ℝ) (hy : 0 < y) (hc : 0 < c) : IC y c ≤ 4 * c / y ^ 2 := by
  have hy2 : 0 < y / 2 := half_pos hy
  calc IC y c ≤ ∫ t in Set.Ioi (0:ℝ), 2 * c / y * Real.exp (-(y / 2) * t) := by
        unfold IC
        refine setIntegral_mono_on (ICi_int y c hc).integrableOn
          ((exp_neg_integrableOn_Ioi 0 hy2).const_mul (2 * c / y)) measurableSet_Ioi (fun t ht => ?_)
        have ht0 : 0 < t := ht
        have h1 : EE y c t ≤ Real.exp (-y * t) := by
          unfold EE; apply Real.exp_le_exp.2; nlinarith [sq_nonneg t]
        have h2 : t ≤ 2 / y * Real.exp (y * t / 2) := by
          have := Real.add_one_le_exp (y * t / 2)
          rw [div_mul_eq_mul_div, le_div_iff₀ hy]; nlinarith
        have h3 : Real.exp (-y * t) * Real.exp (y * t / 2) = Real.exp (-(y / 2) * t) := by
          rw [← Real.exp_add]; congr 1; ring
        calc EE y c t * (c * t) ≤ Real.exp (-y * t) * (c * (2 / y * Real.exp (y * t / 2))) :=
              mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 hc.le) (by positivity) (Real.exp_pos _).le
          _ = 2 * c / y * Real.exp (-(y / 2) * t) := by rw [← h3]; ring
    _ = 4 * c / y ^ 2 := by
        rw [integral_const_mul, expI _ hy2]; field_simp; ring

theorem FF_lt (c : ℝ) (hc : 0 < c) (α : ℝ) (hα : 0 < α) : ∃ y, FF y c < α := by
  set b0 := IA 0 1
  have hb0 : 0 < b0 := IA_pos 0 1 one_pos
  refine ⟨2 / (α * b0), ?_⟩
  set y := 2 / (α * b0) with hy
  have hy0 : 0 < y := by positivity
  have hA := IA_le y c hy0 hc
  have hApos := IA_pos y c hc
  have hB : b0 < IA (-y) 1 := IA_strictAnti 1 one_pos (show -y < 0 by linarith)
  have h1y : 1 / y = α * b0 / 2 := by rw [hy]; field_simp
  unfold FF
  rw [div_lt_iff₀ (by linarith)]
  nlinarith

theorem FF_gt (c : ℝ) (hc : 0 < c) (α : ℝ) (hα : α < 1) (hα0 : 0 < α) : ∃ y, α < FF y c := by
  set a0 := IA 0 c
  have ha0 : 0 < a0 := IA_pos 0 c hc
  have h1α : 0 < 1 - α := by linarith
  refine ⟨-(2 / ((1 - α) * a0)), ?_⟩
  set s := 2 / ((1 - α) * a0) with hs
  have hs0 : 0 < s := by positivity
  have hB := IA_le s 1 hs0 one_pos
  have hBpos := IA_pos s 1 one_pos
  have hA : a0 < IA (-s) c := IA_strictAnti c hc (show -s < 0 by linarith)
  have h1s : 1 / s = (1 - α) * a0 / 2 := by rw [hs]; field_simp
  unfold FF
  rw [neg_neg, lt_div_iff₀ (by linarith)]
  nlinarith [mul_le_mul_of_nonneg_left hB hα0.le]

theorem GG_gt (c : ℝ) (hc : 0 < c) (Δ : ℝ) (hΔ : 0 < Δ) : ∃ y, Δ < GG y c := by
  set a0 := IA 0 c
  have ha0 : 0 < a0 := IA_pos 0 c hc
  refine ⟨-(2 / a0 + 2 * Δ + 2), ?_⟩
  set s := 2 / a0 + 2 * Δ + 2 with hs
  have hs0 : 0 < s := by positivity
  have hB := IA_le s 1 hs0 one_pos
  have hBpos := IA_pos s 1 one_pos
  have hA : a0 < IA (-s) c := IA_strictAnti c hc (show -s < 0 by linarith)
  have h1s : 1 / s ≤ a0 / 2 := by
    rw [div_le_iff₀ hs0]
    have : 2 / a0 * a0 = 2 := by field_simp
    nlinarith
  have hB2 : IA s 1 ≤ IA (-s) c / 2 := by linarith
  have hIC := IC_eq (-s) c hc
  unfold GG
  rw [neg_neg, lt_div_iff₀ (by linarith), hIC]
  have hsA : 2 * Δ * IA (-s) c ≤ s * IA (-s) c :=
    mul_le_mul_of_nonneg_right (by rw [hs]; have : 0 < 2 / a0 := by positivity
                                   linarith) (IA_pos (-s) c hc).le
  nlinarith [mul_le_mul_of_nonneg_left hB2 hΔ.le]

theorem GG_lt (c : ℝ) (hc : 0 < c) (Δ : ℝ) (hΔ : 0 < Δ) : ∃ y, GG y c < Δ := by
  set b0 := IA 0 1
  have hb0 : 0 < b0 := IA_pos 0 1 one_pos
  refine ⟨4 * c / (b0 * Δ) + 1, ?_⟩
  set y := 4 * c / (b0 * Δ) + 1 with hy
  have hy1 : 1 ≤ y := by have : 0 < 4 * c / (b0 * Δ) := by positivity
                         linarith
  have hy0 : 0 < y := by linarith
  have hC := IC_le y c hy0 hc
  have hApos := IA_pos y c hc
  have hB : b0 < IA (-y) 1 := IA_strictAnti 1 one_pos (show -y < 0 by linarith)
  have e : y * (b0 * Δ) = 4 * c + b0 * Δ := by rw [hy]; field_simp
  have h4 : 4 * c / y ^ 2 < Δ * b0 := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hy1 (show 0 ≤ y * (b0 * Δ) by positivity)]
  unfold GG
  rw [div_lt_iff₀ (by linarith)]
  nlinarith [mul_lt_mul_of_pos_left hB hΔ]

/-! ## Closed forms -/

theorem FF_closed (β μ θ : ℝ) (hμ : 0 < μ) (hθ : 0 < θ) :
    FF β (θ / μ) = ErlangA.Staffing.w (-β) (Real.sqrt (μ / θ)) := by
  have hc : 0 < θ / μ := by positivity
  have ha : 0 < Real.sqrt (θ / μ) := Real.sqrt_pos.2 hc
  have hs : Real.sqrt (μ / θ) = (Real.sqrt (θ / μ))⁻¹ := by rw [← Real.sqrt_inv, inv_div]
  have hb := hazard_pos (β / Real.sqrt (θ / μ))
  have hm := hazard_pos (-β)
  unfold FF ErlangA.Staffing.w
  have e : -(-β * Real.sqrt (μ / θ)) = β / Real.sqrt (θ / μ) := by rw [hs]; ring
  rw [IA_closed β _ hc, IA_one, e, hs]
  field_simp

theorem GG_closed (β μ θ : ℝ) (hμ : 0 < μ) (hθ : 0 < θ) :
    GG β (θ / μ) = (Real.sqrt (θ / μ) * hazard (β * Real.sqrt (μ / θ)) - β) *
      ErlangA.Staffing.w (-β) (Real.sqrt (μ / θ)) := by
  have hc : 0 < θ / μ := by positivity
  rw [← FF_closed β μ θ hμ hθ]
  have hs : Real.sqrt (μ / θ) = (Real.sqrt (θ / μ))⁻¹ := by rw [← Real.sqrt_inv, inv_div]
  have hA := IA_closed β _ hc
  have hApos := IA_pos β _ hc
  have hBpos := IA_pos (-β) 1 one_pos
  have hb := hazard_pos (β / Real.sqrt (θ / μ))
  have ha : 0 < Real.sqrt (θ / μ) := Real.sqrt_pos.2 hc
  have e1 : Real.sqrt (θ / μ) * hazard (β * Real.sqrt (μ / θ)) = 1 / IA β (θ / μ) := by
    rw [hA, hs, ← div_eq_mul_inv]; field_simp
  rw [e1]
  unfold GG FF
  rw [IC_eq β _ hc]
  field_simp

/-! ## Finite-N monotonicity in v = 1 - lam/(Nμ) -/


noncomputable def gA (N : ℕ) (c : ℝ) (n : ℕ) : ℝ :=
  c * ((n : ℝ) + 1) / N / (1 + c * ((n : ℝ) + 1) / N)

theorem gA_nonneg (N : ℕ) (c : ℝ) (hc : 0 ≤ c) (n : ℕ) : 0 ≤ gA N c n := by
  unfold gA; positivity

theorem gA_le_one (N : ℕ) (c : ℝ) (hc : 0 ≤ c) (n : ℕ) : gA N c n ≤ 1 := by
  unfold gA
  have : 0 ≤ c * ((n : ℝ) + 1) / N := by positivity
  rw [div_le_one (by linarith)]; linarith

theorem gA_mono (N : ℕ) (c : ℝ) (hc : 0 ≤ c) : Monotone (gA N c) := by
  refine monotone_nat_of_le_succ fun n => ?_
  have key : ∀ x x' : ℝ, 0 ≤ x → x ≤ x' → x / (1 + x) ≤ x' / (1 + x') := by
    intro x x' hx hxx
    rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith
  unfold gA
  apply key _ _ (by positivity)
  have : ((n : ℝ) + 1) ≤ ((n + 1 : ℕ) : ℝ) + 1 := by push_cast; linarith
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left this hc) (Nat.cast_nonneg N)

theorem uR_nonneg' (N : ℕ) (v c : ℝ) (n : ℕ) (hv : v < 1) (hc : 0 ≤ c) : 0 ≤ uR N v c n :=
  Finset.prod_nonneg fun j _ => div_nonneg (by linarith) (by positivity)

theorem uR_anti_v (N : ℕ) (v v' c : ℝ) (h : v ≤ v') (hv' : v' < 1) (hc : 0 ≤ c) (n : ℕ) :
    uR N v' c n ≤ uR N v c n := by
  unfold uR
  exact Finset.prod_le_prod (fun j _ => div_nonneg (by linarith) (by positivity))
    (fun j _ => div_le_div_of_nonneg_right (by linarith) (by positivity))

theorem uR_tilt (N : ℕ) (v v' c : ℝ) (hv' : v' < 1) (n : ℕ) :
    uR N v c n = uR N v' c n * ((1 - v) / (1 - v')) ^ n := by
  have h1 : (1 - v') ≠ 0 := by linarith
  unfold uR
  rw [show ((1 - v) / (1 - v')) ^ n = ∏ j ∈ Finset.range n, ((1 - v) / (1 - v')) by
      rw [Finset.prod_const, Finset.card_range],
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [div_mul_div_comm, mul_comm (1 - v') (1 - v), mul_div_mul_right _ _ h1]

theorem uL_mono_v (N : ℕ) (hN : 0 < N) (v v' : ℝ) (h : v ≤ v') (hv' : v' < 1) (j : ℕ)
    (hj : j ≤ N) : uL N v j ≤ uL N v' j := by
  unfold uL
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  refine Finset.prod_le_prod (fun i hi => ?_) (fun i hi => ?_)
  · have : (i : ℝ) / N < 1 := by
      rw [div_lt_one hNr]; exact_mod_cast (lt_of_lt_of_le (Finset.mem_range.1 hi) hj)
    exact div_nonneg (by linarith) (by linarith)
  · have : (i : ℝ) / N < 1 := by
      rw [div_lt_one hNr]; exact_mod_cast (lt_of_lt_of_le (Finset.mem_range.1 hi) hj)
    exact div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith)

theorem SB_mono (N : ℕ) (hN : 0 < N) (v v' : ℝ) (h : v ≤ v') (hv' : v' < 1) :
    SB N v ≤ SB N v' :=
  Finset.sum_le_sum fun m hm =>
    uL_mono_v N hN v v' h hv' (m + 1) (by have := Finset.mem_range.1 hm; omega)

theorem SB_nonneg (N : ℕ) (hN : 0 < N) (v : ℝ) (hv : v < 1) : 0 ≤ SB N v := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  refine Finset.sum_nonneg fun m hm => Finset.prod_nonneg fun i hi => ?_
  have : (i : ℝ) / N < 1 := by
    rw [div_lt_one hNr]
    have := Finset.mem_range.1 hi; have := Finset.mem_range.1 hm
    exact_mod_cast (show i < N by omega)
  exact div_nonneg (by linarith) (by linarith)

theorem SA_ge_one (N : ℕ) (v c : ℝ) (hv : v < 1) (hc : 0 ≤ c) (hs : Summable (uR N v c)) :
    1 ≤ SA N v c := by
  have := hs.le_tsum 0 (fun j _ => uR_nonneg' N v c j hv hc)
  have h0 : uR N v c 0 = 1 := by unfold uR; simp
  unfold SA; linarith

theorem SA_anti (N : ℕ) (v v' c : ℝ) (h : v ≤ v') (hv' : v' < 1) (hc : 0 ≤ c)
    (hs : Summable (uR N v c)) : SA N v' c ≤ SA N v c ∧ Summable (uR N v' c) := by
  have hs' : Summable (uR N v' c) := Summable.of_nonneg_of_le
    (fun n => uR_nonneg' N v' c n hv' hc) (fun n => uR_anti_v N v v' c h hv' hc n) hs
  exact ⟨Summable.tsum_le_tsum (fun n => uR_anti_v N v v' c h hv' hc n) hs' hs, hs'⟩

noncomputable def PW (N : ℕ) (v c : ℝ) : ℝ := SA N v c / (SA N v c + SB N v)
noncomputable def PA (N : ℕ) (v c : ℝ) : ℝ := SC N v c / (SA N v c + SB N v)

theorem PW_anti (N : ℕ) (hN : 0 < N) (v v' c : ℝ) (h : v ≤ v') (hv' : v' < 1) (hc : 0 ≤ c)
    (hs : Summable (uR N v c)) : PW N v' c ≤ PW N v c := by
  obtain ⟨hA, hs'⟩ := SA_anti N v v' c h hv' hc hs
  have a1 := SA_ge_one N v c (by linarith) hc hs
  have a2 := SA_ge_one N v' c hv' hc hs'
  have b1 := SB_nonneg N hN v (by linarith)
  have b2 := SB_nonneg N hN v' hv'
  have hB := SB_mono N hN v v' h hv'
  unfold PW
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith [mul_le_mul hA hB b1 (by linarith)]

/-- likelihood-ratio (tilting) inequality: tilting by an increasing weight raises the mean of an
increasing bounded function. -/
theorem tilt (p g : ℕ → ℝ) (r : ℝ) (hr : 1 ≤ r) (hp : ∀ n, 0 ≤ p n) (hg : Monotone g)
    (hg0 : ∀ n, 0 ≤ g n) (hg1 : ∀ n, g n ≤ 1) (hps : Summable p)
    (hqs : Summable fun n => p n * r ^ n) (hpos : 0 < ∑' n, p n) :
    (∑' n, p n * g n) * (∑' n, p n * r ^ n) ≤ (∑' n, p n * r ^ n * g n) * ∑' n, p n := by
  classical
  have hr0 : 0 < r := by linarith
  have hpg : Summable fun n => p n * g n := Summable.of_nonneg_of_le
    (fun n => mul_nonneg (hp n) (hg0 n)) (fun n => mul_le_of_le_one_right (hp n) (hg1 n)) hps
  have hqg : Summable fun n => p n * r ^ n * g n := Summable.of_nonneg_of_le
    (fun n => mul_nonneg (mul_nonneg (hp n) (by positivity)) (hg0 n))
    (fun n => mul_le_of_le_one_right (mul_nonneg (hp n) (by positivity)) (hg1 n)) hqs
  set m := (∑' n, p n * g n) / ∑' n, p n with hm
  have hmS : m * ∑' n, p n = ∑' n, p n * g n := by rw [hm]; field_simp
  have hpgm : Summable fun n => p n * (g n - m) :=
    (hpg.sub (hps.mul_left m)).congr (fun n => by ring)
  have hz : ∑' n, p n * (g n - m) = 0 := by
    have : (fun n => p n * (g n - m)) = fun n => p n * g n - m * p n := by funext n; ring
    rw [this, Summable.tsum_sub hpg (hps.mul_left m), tsum_mul_left]; linarith
  by_cases hex : ∃ n, m ≤ g n
  · have hn0 : m ≤ g (Nat.find hex) := Nat.find_spec hex
    set K := r ^ (Nat.find hex) with hK
    have hpt : ∀ n, 0 ≤ p n * (r ^ n - K) * (g n - m) := by
      intro n
      rcases le_or_gt (Nat.find hex) n with h | h
      · have h1 : K ≤ r ^ n := pow_le_pow_right₀ hr h
        have h2 : m ≤ g n := le_trans hn0 (hg h)
        exact mul_nonneg (mul_nonneg (hp n) (by linarith)) (by linarith)
      · have h1 : r ^ n ≤ K := pow_le_pow_right₀ hr h.le
        have h2 : g n < m := by have := Nat.find_min hex h; push Not at this; exact this
        exact mul_nonneg_of_nonpos_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (hp n) (by linarith))
          (by linarith)
    have hsum : 0 ≤ ∑' n, p n * (r ^ n - K) * (g n - m) := tsum_nonneg hpt
    have e : (fun n => p n * (r ^ n - K) * (g n - m)) =
        fun n => (p n * r ^ n * g n - m * (p n * r ^ n)) - K * (p n * (g n - m)) := by
      funext n; ring
    rw [e, Summable.tsum_sub (hqg.sub (hqs.mul_left m)) (hpgm.mul_left K),
      Summable.tsum_sub hqg (hqs.mul_left m), tsum_mul_left, tsum_mul_left, hz] at hsum
    have h3 : m * (∑' n, p n * r ^ n) ≤ ∑' n, p n * r ^ n * g n := by linarith
    rw [← hmS]
    calc m * (∑' n, p n) * (∑' n, p n * r ^ n) = (m * (∑' n, p n * r ^ n)) * ∑' n, p n := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h3 hpos.le
  · push Not at hex
    exfalso
    obtain ⟨i, hi⟩ : ∃ i, 0 < p i := by
      by_contra hne
      push Not at hne
      have : (fun n => p n) = fun _ => (0:ℝ) := funext fun n => le_antisymm (hne n) (hp n)
      rw [show (∑' n, p n) = ∑' _ : ℕ, (0:ℝ) by rw [this]] at hpos
      simp at hpos
    have hpos2 : 0 < ∑' n, p n * (m - g n) :=
      Summable.tsum_pos (((hps.mul_right m).sub hpg).congr (fun n => by ring))
        (fun n => mul_nonneg (hp n) (by linarith [hex n])) i (mul_pos hi (by linarith [hex i]))
    have : ∑' n, p n * (m - g n) = -∑' n, p n * (g n - m) := by
      rw [← tsum_neg]; congr 1; funext n; ring
    linarith

theorem PA_anti (N : ℕ) (hN : 0 < N) (v v' c : ℝ) (h : v ≤ v') (hv' : v' < 1) (hc : 0 ≤ c)
    (hs : Summable (uR N v c)) : PA N v' c ≤ PA N v c := by
  obtain ⟨hA, hs'⟩ := SA_anti N v v' c h hv' hc hs
  have a1 := SA_ge_one N v c (by linarith) hc hs
  have a2 := SA_ge_one N v' c hv' hc hs'
  have b1 := SB_nonneg N hN v (by linarith)
  have b2 := SB_nonneg N hN v' hv'
  have hPW := PW_anti N hN v v' c h hv' hc hs
  unfold PW at hPW
  rw [div_le_div_iff₀ (by linarith) (by linarith)] at hPW
  have hr : 1 ≤ (1 - v) / (1 - v') := by rw [one_le_div (by linarith)]; linarith
  have hq : ∀ n, uR N v' c n * ((1 - v) / (1 - v')) ^ n = uR N v c n :=
    fun n => (uR_tilt N v v' c hv' n).symm
  have ht := tilt (uR N v' c) (gA N c) _ hr (fun n => uR_nonneg' N v' c n hv' hc) (gA_mono N c hc)
    (gA_nonneg N c hc) (gA_le_one N c hc) hs' (by simp_rw [hq]; exact hs) (by unfold SA at a2; linarith)
  simp_rw [hq] at ht
  change SC N v' c * SA N v c ≤ SC N v c * SA N v' c at ht
  have c1 : 0 ≤ SC N v' c := tsum_nonneg fun n =>
    mul_nonneg (uR_nonneg' N v' c n hv' hc) (gA_nonneg N c hc n)
  unfold PA
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  have key : SC N v' c * (SA N v c + SB N v) * SA N v' c ≤
      SC N v c * (SA N v' c + SB N v') * SA N v' c := by
    nlinarith [mul_le_mul_of_nonneg_left hPW c1,
      mul_le_mul_of_nonneg_right ht (show 0 ≤ SA N v' c + SB N v' by linarith)]
  exact le_of_mul_le_mul_right key (by linarith)

/-! ## Inversion -/

theorem invert (P : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (α : ℝ)
    (hmono : ∀ N : ℕ, 0 < N → ∀ v v' : ℝ, v ≤ v' → v' < 1 → P N v' ≤ P N v)
    (hlim : ∀ y : ℝ, Tendsto (fun N : ℕ => P N (y / Real.sqrt N)) atTop (𝓝 (F y)))
    (hF : StrictAnti F) (h1 : ∃ y, α < F y) (h2 : ∃ y, F y < α)
    (v : ℕ → ℝ) (hv : ∀ N : ℕ, 0 < N → v N < 1)
    (hP : Tendsto (fun N => P N (v N)) atTop (𝓝 α)) :
    ∃ β, Tendsto (fun N : ℕ => v N * Real.sqrt N) atTop (𝓝 β) := by
  set S := {y | α < F y} with hS
  obtain ⟨y1, hy1⟩ := h1
  obtain ⟨y2, hy2⟩ := h2
  have hne : S.Nonempty := ⟨y1, hy1⟩
  have hbdd : BddAbove S := by
    refine ⟨y2, fun y hy => ?_⟩
    by_contra hc
    push Not at hc
    have := hF hc
    simp only [hS, Set.mem_setOf_eq] at hy
    linarith
  have hsq : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨sSup S, tendsto_order.2 ⟨fun y hy => ?_, fun y hy => ?_⟩⟩
  · obtain ⟨y', hy'S, hyy'⟩ := exists_lt_of_lt_csSup hne hy
    have hFy : α < F y := lt_of_lt_of_le hy'S (hF.antitone hyy'.le)
    have e1 := (hlim y).eventually (lt_mem_nhds (show (α + F y) / 2 < F y by linarith))
    have e2 := hP.eventually (gt_mem_nhds (show α < (α + F y) / 2 by linarith))
    have e3 : ∀ᶠ N : ℕ in atTop, y / Real.sqrt N < 1 := by
      have := (tendsto_const_nhds (x := y)).div_atTop hsq
      exact this.eventually (gt_mem_nhds one_pos)
    filter_upwards [e1, e2, e3, eventually_ge_atTop 1] with N h1 h2 h3 hN
    by_contra hc
    push Not at hc
    have hq : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN)
    have h4 : v N ≤ y / Real.sqrt N := by rw [le_div_iff₀ hq]; exact hc
    have := hmono N hN (v N) (y / Real.sqrt N) h4 h3
    linarith
  · obtain ⟨y'', h1', h2'⟩ := exists_between hy
    have hy''S : y'' ∉ S := fun hm => (not_le.2 h1') (le_csSup hbdd hm)
    have hFy'' : F y'' ≤ α := by
      simp only [hS, Set.mem_setOf_eq, not_lt] at hy''S; exact hy''S
    have hFy : F y < α := lt_of_lt_of_le (hF h2') hFy''
    have e1 := (hlim y).eventually (gt_mem_nhds (show F y < (α + F y) / 2 by linarith))
    have e2 := hP.eventually (lt_mem_nhds (show (α + F y) / 2 < α by linarith))
    filter_upwards [e1, e2, eventually_ge_atTop 1] with N h1 h2 hN
    by_contra hc
    push Not at hc
    have hq : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN)
    have h4 : y / Real.sqrt N ≤ v N := by rw [div_le_iff₀ hq]; exact hc
    have := hmono N hN (y / Real.sqrt N) (v N) h4 (hv N hN)
    linarith

/-! ## Assembly -/

theorem eA (β c : ℝ) :
    ∫ t in Set.Ici (0:ℝ), Real.exp (-(β * t) - c * t ^ 2 / 2) = IA β c := by
  rw [integral_Ici_eq_integral_Ioi]; rfl

theorem eB (β : ℝ) : ∫ t in Set.Ici (0:ℝ), Real.exp (β * t - t ^ 2 / 2) = IA (-β) 1 := by
  rw [integral_Ici_eq_integral_Ioi]; unfold IA EE
  refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
  congr 1; ring

theorem eC (β c : ℝ) :
    ∫ t in Set.Ici (0:ℝ), Real.exp (-(β * t) - c * t ^ 2 / 2) * (c * t) = IC β c := by
  rw [integral_Ici_eq_integral_Ioi]; rfl

theorem PW_lim (v : ℕ → ℝ) (β c : ℝ) (hc : 0 < c)
    (hconv : Tendsto (fun n : ℕ => v n * Real.sqrt n) atTop (𝓝 β)) :
    Tendsto (fun N : ℕ => PW N (v N) c) atTop (𝓝 (FF β c)) := by
  have hA := right_lim v β c hc hconv
  have hB := left_lim v β hconv
  rw [eA] at hA
  rw [eB] at hB
  have hlim := hA.div (hA.add hB) (add_pos (IA_pos β c hc) (IA_pos (-β) 1 one_pos)).ne'
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hq : (Real.sqrt N)⁻¹ ≠ 0 :=
    inv_ne_zero (Real.sqrt_pos.2 (by exact_mod_cast hN)).ne'
  simp only [Pi.div_apply]
  unfold PW
  rw [← mul_add, mul_div_mul_left _ _ hq]

theorem PA_lim (v : ℕ → ℝ) (β c : ℝ) (hc : 0 < c)
    (hconv : Tendsto (fun n : ℕ => v n * Real.sqrt n) atTop (𝓝 β)) :
    Tendsto (fun N : ℕ => Real.sqrt N * PA N (v N) c) atTop (𝓝 (GG β c)) := by
  have hA := right_lim v β c hc hconv
  have hB := left_lim v β hconv
  have hC := rightC_lim v β c hc hconv
  rw [eA] at hA
  rw [eB] at hB
  rw [eC] at hC
  have hlim := hC.div (hA.add hB) (add_pos (IA_pos β c hc) (IA_pos (-β) 1 one_pos)).ne'
  refine hlim.congr' (Eventually.of_forall fun N => ?_)
  simp only [Pi.div_apply]
  unfold PA
  rw [← mul_add, div_eq_mul_inv, mul_inv, inv_inv, div_eq_mul_inv]; ring

theorem main (μ θ : ℝ) (lam : ℕ → ℝ) (hμ : 0 < μ) (hθ : 0 < θ)
    (hlam : ∀ N : ℕ, 1 ≤ N → 0 < lam N) :
    List.TFAE
        [∃ β : ℝ,
            Tendsto (fun N : ℕ => Real.sqrt N * (1 - lam N / ((N : ℝ) * μ))) atTop (𝓝 β),
         ∃ α ∈ Set.Ioo (0 : ℝ) 1,
            Tendsto (fun N : ℕ => ErlangA.Staffing.probWait N (lam N) μ θ) atTop (𝓝 α),
         ∃ Δ ∈ Set.Ioi (0 : ℝ),
            Tendsto (fun N : ℕ => Real.sqrt N * ErlangA.Abandonment.probAbandon N (lam N) μ θ) atTop (𝓝 Δ)] ∧
      ∀ β : ℝ,
        Tendsto (fun N : ℕ => Real.sqrt N * (1 - lam N / ((N : ℝ) * μ))) atTop (𝓝 β) →
          Tendsto (fun N : ℕ => ErlangA.Staffing.probWait N (lam N) μ θ) atTop
              (𝓝 (ErlangA.Staffing.w (-β) (Real.sqrt (μ / θ)))) ∧
            Tendsto (fun N : ℕ => Real.sqrt N * ErlangA.Abandonment.probAbandon N (lam N) μ θ) atTop
              (𝓝 ((Real.sqrt (θ / μ) * hazard (β * Real.sqrt (μ / θ)) - β) *
                ErlangA.Staffing.w (-β) (Real.sqrt (μ / θ)))) := by
  have hc : 0 < θ / μ := by positivity
  obtain ⟨v, hvN⟩ : ∃ v : ℕ → ℝ, ∀ N, v N = 1 - lam N / ((N : ℝ) * μ) :=
    ⟨fun N => 1 - lam N / ((N : ℝ) * μ), fun N => rfl⟩
  have hv1 : ∀ N : ℕ, 0 < N → v N < 1 := by
    intro N hN
    have : 0 < lam N / ((N : ℝ) * μ) := div_pos (hlam N hN) (by positivity)
    rw [hvN]; linarith
  have hW : ∀ᶠ N : ℕ in atTop,
      PW N (v N) (θ / μ) = ErlangA.Staffing.probWait N (lam N) μ θ := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [(struct N hN (lam N) μ θ (hlam N hN) hμ hθ).1, hvN]; rfl
  have hAb : ∀ᶠ N : ℕ in atTop, Real.sqrt N * PA N (v N) (θ / μ) =
      Real.sqrt N * ErlangA.Abandonment.probAbandon N (lam N) μ θ := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [(struct N hN (lam N) μ θ (hlam N hN) hμ hθ).2, hvN]; rfl
  have hswap : ∀ β, Tendsto (fun N : ℕ => Real.sqrt N * (1 - lam N / ((N : ℝ) * μ))) atTop (𝓝 β) ↔
      Tendsto (fun N : ℕ => v N * Real.sqrt N) atTop (𝓝 β) := by
    intro β
    constructor
    · intro h; refine h.congr (fun N => ?_); rw [hvN]; ring
    · intro h; refine h.congr (fun N => ?_); rw [hvN]; ring
  have K1 : ∀ β, Tendsto (fun N : ℕ => Real.sqrt N * (1 - lam N / ((N : ℝ) * μ))) atTop (𝓝 β) →
      Tendsto (fun N => ErlangA.Staffing.probWait N (lam N) μ θ) atTop (𝓝 (FF β (θ / μ))) ∧
      Tendsto (fun N : ℕ => Real.sqrt N * ErlangA.Abandonment.probAbandon N (lam N) μ θ) atTop
        (𝓝 (GG β (θ / μ))) := by
    intro β hβ
    have h' := (hswap β).1 hβ
    exact ⟨(PW_lim v β _ hc h').congr' hW, (PA_lim v β _ hc h').congr' hAb⟩
  have hconst : ∀ y : ℝ, Tendsto (fun N : ℕ => y / Real.sqrt N * Real.sqrt N) atTop (𝓝 y) := by
    intro y
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hq : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN)
    field_simp
  refine ⟨?_, fun β hβ => ?_⟩
  · tfae_have 1 → 2 := by
      rintro ⟨β, hβ⟩
      have hp := add_pos (IA_pos β _ hc) (IA_pos (-β) 1 one_pos)
      refine ⟨FF β (θ / μ), ⟨div_pos (IA_pos β _ hc) hp, ?_⟩, (K1 β hβ).1⟩
      rw [FF, div_lt_one hp]
      linarith [IA_pos (-β) 1 one_pos]
    tfae_have 1 → 3 := by
      rintro ⟨β, hβ⟩
      exact ⟨GG β (θ / μ),
        div_pos (IC_pos β _ hc) (add_pos (IA_pos β _ hc) (IA_pos (-β) 1 one_pos)), (K1 β hβ).2⟩
    tfae_have 2 → 1 := by
      rintro ⟨α, ⟨hα0, hα1⟩, hα⟩
      obtain ⟨β, hβ⟩ := invert (fun N v => PW N v (θ / μ)) (fun y => FF y (θ / μ)) α
        (fun N hN v v' h hv' => PW_anti N hN v v' _ h hv' hc.le
          (uR_summable N hN v _ (lt_of_le_of_lt h hv') hc))
        (fun y => PW_lim (fun N => y / Real.sqrt N) y _ hc (hconst y))
        (FF_strictAnti _ hc) (FF_gt _ hc α hα1 hα0) (FF_lt _ hc α hα0) v hv1
        (hα.congr' (hW.mono fun N h => h.symm))
      exact ⟨β, (hswap β).2 hβ⟩
    tfae_have 3 → 1 := by
      rintro ⟨Δ, hΔ, hΔt⟩
      have hΔ0 : 0 < Δ := hΔ
      obtain ⟨β, hβ⟩ := invert (fun N v => Real.sqrt N * PA N v (θ / μ)) (fun y => GG y (θ / μ)) Δ
        (fun N hN v v' h hv' => mul_le_mul_of_nonneg_left (PA_anti N hN v v' _ h hv' hc.le
          (uR_summable N hN v _ (lt_of_le_of_lt h hv') hc)) (Real.sqrt_nonneg _))
        (fun y => PA_lim (fun N => y / Real.sqrt N) y _ hc (hconst y))
        (GG_strictAnti _ hc) (GG_gt _ hc Δ hΔ0) (GG_lt _ hc Δ hΔ0) v hv1
        (hΔt.congr' (hAb.mono fun N h => h.symm))
      exact ⟨β, (hswap β).2 hβ⟩
    tfae_finish
  · obtain ⟨h1, h2⟩ := K1 β hβ
    rw [FF_closed β μ θ hμ hθ] at h1
    rw [GG_closed β μ θ hμ hθ] at h2
    exact ⟨h1, h2⟩

end ErlA4

open Filter Topology DimCallCenters.Rationalized ErlangA.Staffing in
theorem solution (μ θ : ℝ) (lam : ℕ → ℝ) (hμ : 0 < μ) (hθ : 0 < θ)
    (hlam : ∀ N : ℕ, 1 ≤ N → 0 < lam N) :
    List.TFAE
        [∃ β : ℝ,
            Tendsto (fun N : ℕ => Real.sqrt N * (1 - lam N / ((N : ℝ) * μ))) atTop (𝓝 β),
         ∃ α ∈ Set.Ioo (0 : ℝ) 1,
            Tendsto (fun N : ℕ => probWait N (lam N) μ θ) atTop (𝓝 α),
         ∃ Δ ∈ Set.Ioi (0 : ℝ),
            Tendsto (fun N : ℕ => Real.sqrt N * ErlangA.Abandonment.probAbandon N (lam N) μ θ) atTop (𝓝 Δ)] ∧
      ∀ β : ℝ,
        Tendsto (fun N : ℕ => Real.sqrt N * (1 - lam N / ((N : ℝ) * μ))) atTop (𝓝 β) →
          Tendsto (fun N : ℕ => probWait N (lam N) μ θ) atTop
              (𝓝 (w (-β) (Real.sqrt (μ / θ)))) ∧
            Tendsto (fun N : ℕ => Real.sqrt N * ErlangA.Abandonment.probAbandon N (lam N) μ θ) atTop
              (𝓝 ((Real.sqrt (θ / μ) * hazard (β * Real.sqrt (μ / θ)) - β) *
                w (-β) (Real.sqrt (μ / θ)))) := by
  exact ErlA4.main μ θ lam hμ hθ hlam
