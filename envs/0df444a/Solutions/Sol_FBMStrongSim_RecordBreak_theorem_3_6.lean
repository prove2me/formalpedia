-- Prove2me | solution 1 for FBMStrongSim.RecordBreak.theorem_3_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T20:31:45.71986+00:00
-- url     : https://prove2.me/submissions/01f8a1e9-3f65-478a-8c0f-610a22076744

import Mathlib
import Definitions.Def_FBMStrongSim_RecordBreak_Model
import Theorems.Thm_FBMStrongSim_RecordBreak_sup_norm_eq_max_disp
import Theorems.Thm_FBMStrongSim_RecordBreak_theorem_3_1

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace FBM36Aux
open FBMStrongSim.RecordBreak

/-- Pointwise convergence of the dyadic interpolations of a path continuous on `[0,1]`. -/
theorem interp_tendsto (x : ℝ → ℝ) (hx : ContinuousOn x (Set.Icc 0 1)) (s : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun m : ℕ => interp x m s) atTop (𝓝 (x s)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨η, hη, hηx⟩ := Metric.continuousWithinAt_iff.1 (hx s hs) (ε / 2) (by linarith)
  obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one hη (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨M, fun m hm => ?_⟩
  have h2m : (0 : ℝ) < 2 ^ m := by positivity
  have h2m1 : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
  have hpowle : ((1 : ℝ) / 2) ^ m ≤ (1 / 2) ^ M :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
  have hinv : 1 / (2 : ℝ) ^ m = (1 / 2) ^ m := by rw [one_div_pow]
  set F : ℕ := ⌊(2 : ℝ) ^ m * s⌋₊ with hF
  set i : ℕ := min F (2 ^ m - 1) with hi
  have hs0 : 0 ≤ (2 : ℝ) ^ m * s := mul_nonneg h2m.le hs.1
  have hFle : (F : ℝ) ≤ 2 ^ m * s := Nat.floor_le hs0
  have hFlt : 2 ^ m * s < (F : ℝ) + 1 := Nat.lt_floor_add_one _
  have hcast : ((2 ^ m - 1 : ℕ) : ℝ) = 2 ^ m - 1 := by
    rw [Nat.cast_sub (Nat.one_le_two_pow)]; push_cast; ring
  have hi1 : (i : ℝ) ≤ 2 ^ m * s := by
    have : i ≤ F := min_le_left _ _
    exact le_trans (by exact_mod_cast this) hFle
  have hi2 : (i : ℝ) + 1 ≤ 2 ^ m := by
    have : i ≤ 2 ^ m - 1 := min_le_right _ _
    have h' : (i : ℝ) ≤ ((2 ^ m - 1 : ℕ) : ℝ) := by exact_mod_cast this
    rw [hcast] at h'; linarith
  have hi3 : 2 ^ m * s - i ≤ 1 := by
    rcases le_total F (2 ^ m - 1) with h | h
    · have : i = F := min_eq_left h
      rw [this]; linarith
    · have : i = 2 ^ m - 1 := min_eq_right h
      rw [this, hcast]
      have : s ≤ 1 := hs.2
      nlinarith
  set lam : ℝ := 2 ^ m * s - i with hlam
  have hl0 : 0 ≤ lam := by rw [hlam]; linarith
  have hp : dyadic m i = s - lam / 2 ^ m := by
    unfold dyadic; rw [hlam]; field_simp; ring
  have hq : dyadic m (i + 1) = s + (1 - lam) / 2 ^ m := by
    unfold dyadic; rw [hlam]; push_cast; field_simp; ring
  have hpI : dyadic m i ∈ Set.Icc (0 : ℝ) 1 := by
    unfold dyadic
    constructor
    · positivity
    · rw [div_le_one h2m]; linarith
  have hqI : dyadic m (i + 1) ∈ Set.Icc (0 : ℝ) 1 := by
    unfold dyadic
    constructor
    · positivity
    · rw [div_le_one h2m]; push_cast; linarith
  have hd : 1 / (2 : ℝ) ^ m < η := by rw [hinv]; linarith
  have hlam_div : lam / 2 ^ m ≤ 1 / 2 ^ m := by
    apply div_le_div_of_nonneg_right _ h2m.le; linarith
  have hlam_div' : (1 - lam) / 2 ^ m ≤ 1 / 2 ^ m := by
    apply div_le_div_of_nonneg_right _ h2m.le; linarith
  have hlam_nn : 0 ≤ lam / 2 ^ m := div_nonneg hl0 h2m.le
  have hlam_nn' : 0 ≤ (1 - lam) / 2 ^ m := div_nonneg (by linarith) h2m.le
  have hxp : |x (dyadic m i) - x s| < ε / 2 := by
    have := hηx hpI (by rw [Real.dist_eq, hp, abs_lt]; constructor <;> linarith)
    rwa [Real.dist_eq] at this
  have hxq : |x (dyadic m (i + 1)) - x s| < ε / 2 := by
    have := hηx hqI (by rw [Real.dist_eq, hq, abs_lt]; constructor <;> linarith)
    rwa [Real.dist_eq] at this
  have hint : interp x m s = x (dyadic m i) + lam * (x (dyadic m (i + 1)) - x (dyadic m i)) := by
    rfl
  rw [Real.dist_eq, hint]
  have key : x (dyadic m i) + lam * (x (dyadic m (i + 1)) - x (dyadic m i)) - x s
      = (1 - lam) * (x (dyadic m i) - x s) + lam * (x (dyadic m (i + 1)) - x s) := by ring
  rw [key]
  calc |(1 - lam) * (x (dyadic m i) - x s) + lam * (x (dyadic m (i + 1)) - x s)|
      ≤ |(1 - lam) * (x (dyadic m i) - x s)| + |lam * (x (dyadic m (i + 1)) - x s)| :=
        abs_add_le _ _
    _ = (1 - lam) * |x (dyadic m i) - x s| + lam * |x (dyadic m (i + 1)) - x s| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - lam),
          abs_of_nonneg hl0]
    _ ≤ (1 - lam) * (ε / 2) + lam * (ε / 2) := by
        gcongr
    _ < ε := by linarith

/-- `ℓ_k = r^k` with `r = 2^{-(H-δ)}`. -/
theorem ell_eq (H δ : ℝ) (k : ℕ) : ell H δ k = ((2 : ℝ) ^ (-(H - δ))) ^ k := by
  unfold ell
  rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]

/-- Deterministic part: if a path is continuous on `[0,1]` and no record is broken beyond
level `n`, then `|x s - x_n(s)| ≤ ρ r^{n+1} / (1 - r)`. -/
theorem det_bound (x : ℝ → ℝ) (hx : ContinuousOn x (Set.Icc 0 1)) (rho H δ : ℝ)
    (hHδ : 0 < H - δ) (n : ℕ)
    (hk : ∀ k : ℕ, n < k → maxDisp x k ≤ rho * ell H δ k) (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    |x s - interp x n s| ≤ rho * ((2 : ℝ) ^ (-(H - δ))) ^ (n + 1) / (1 - (2 : ℝ) ^ (-(H - δ))) := by
  set r : ℝ := (2 : ℝ) ^ (-(H - δ)) with hr
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hrho : 0 ≤ rho := by
    have h1 := hk (n + 1) (by omega)
    have h2 : 0 ≤ maxDisp x (n + 1) := by
      unfold maxDisp
      exact le_trans (abs_nonneg (disp x (n + 1) 0))
        (Finset.le_sup' (fun j => |disp x (n + 1) j|) (by simp))
    have h3 : 0 < ell H δ (n + 1) := by rw [ell_eq]; exact pow_pos (Real.rpow_pos_of_pos (by norm_num) _) _
    by_contra hneg
    push Not at hneg
    nlinarith
  have step : ∀ m : ℕ, n ≤ m →
      |interp x m s - interp x n s| ≤ rho * ∑ k ∈ Finset.Ico (n + 1) (m + 1), r ^ k := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => simp
    | succ m hm ih =>
      have hsup := (FBMStrongSim.RecordBreak.sup_norm_eq_max_disp x (m + 1) (by omega)).2
        ⟨s, hs, rfl⟩
      simp only [Nat.add_sub_cancel] at hsup
      have hmk := hk (m + 1) (by omega)
      rw [ell_eq] at hmk
      rw [Finset.sum_Ico_succ_top (by omega), mul_add]
      calc |interp x (m + 1) s - interp x n s|
          ≤ |interp x (m + 1) s - interp x m s| + |interp x m s - interp x n s| := by
            have := abs_add_le (interp x (m + 1) s - interp x m s) (interp x m s - interp x n s)
            rwa [sub_add_sub_cancel] at this
        _ ≤ rho * r ^ (m + 1) + rho * ∑ k ∈ Finset.Ico (n + 1) (m + 1), r ^ k := by
            linarith
        _ = _ := by ring
  have hbound : ∀ m : ℕ, n ≤ m → |interp x m s - interp x n s| ≤ rho * r ^ (n + 1) / (1 - r) := by
    intro m hm
    refine le_trans (step m hm) ?_
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one hr0 hr1) hrho
  have hlim : Tendsto (fun m : ℕ => |interp x m s - interp x n s|) atTop
      (𝓝 (|x s - interp x n s|)) :=
    ((interp_tendsto x hx s hs).sub_const _).abs
  exact le_of_tendsto hlim (eventually_atTop.2 ⟨n, fun m hm => hbound m hm⟩)

/-- Real tail estimate: `e^{tk} · 2e^{-X} ≤ 2 e^{(t+1)^2/(4a)} (e^{-1})^k` when `X ≥ a k^2`. -/
theorem tail_real (t a : ℝ) (ha : 0 < a) (k : ℕ) (X : ℝ) (hX : a * (k : ℝ) ^ 2 ≤ X) :
    Real.exp (t * k) * (2 * Real.exp (-X))
      ≤ 2 * Real.exp ((t + 1) ^ 2 / (4 * a)) * Real.exp (-1) ^ k := by
  have hq : (t + 1) * k - a * (k : ℝ) ^ 2 ≤ (t + 1) ^ 2 / (4 * a) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (2 * a * k - (t + 1))]
  have h1 : Real.exp (t * k) * (2 * Real.exp (-X)) = 2 * Real.exp (t * k - X) := by
    rw [Real.exp_sub, Real.exp_neg]; field_simp
  have h2 : Real.exp (-1) ^ k = Real.exp (-(k : ℝ)) := by
    rw [← Real.exp_nat_mul]; ring_nf
  rw [h1, h2, mul_assoc, ← Real.exp_add]
  gcongr
  nlinarith

/-- Lower bound `ν*² · 2^{2kδ-2} ≥ a k²` with `a = ν*² (2 log 2 · δ)² / 8`. -/
theorem quad_lower (c δ : ℝ) (hc : 0 ≤ c) (hδ : 0 < δ) (k : ℕ) :
    c * (2 * Real.log 2 * δ) ^ 2 / 8 * (k : ℝ) ^ 2 ≤ c * (2 : ℝ) ^ (2 * (k : ℝ) * δ - 2) := by
  have hsplit : (2 : ℝ) ^ (2 * (k : ℝ) * δ - 2) = (2 : ℝ) ^ (2 * (k : ℝ) * δ) / 4 := by
    rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]; norm_num
  rw [hsplit, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  set z : ℝ := Real.log 2 * (2 * (k : ℝ) * δ) with hz
  have hz0 : 0 ≤ z := by
    rw [hz]; apply mul_nonneg (Real.log_nonneg (by norm_num)); positivity
  have he := Real.quadratic_le_exp_of_nonneg hz0
  have hzz : z ^ 2 = (2 * Real.log 2 * δ) ^ 2 * (k : ℝ) ^ 2 := by rw [hz]; ring
  have : z ^ 2 / 8 ≤ Real.exp z / 4 := by nlinarith
  calc c * (2 * Real.log 2 * δ) ^ 2 / 8 * (k : ℝ) ^ 2 = c * (z ^ 2 / 8) := by rw [hzz]; ring
    _ ≤ c * (Real.exp z / 4) := mul_le_mul_of_nonneg_left this hc

open Classical in
/-- Pointwise bound on `exp(t N)` by a sum over record levels beyond `K0`. -/
theorem expMul_le (x : ℝ → ℝ) (rho H δ t : ℝ) (ht : 0 < t) (K0 : ℕ) :
    expMul t (lastRecord rho H δ x) ≤ ENNReal.ofReal (Real.exp (t * K0)) +
      ∑' k : ℕ, (if K0 < k ∧ IsRecord rho H δ x k then ENNReal.ofReal (Real.exp (t * k)) else 0) := by
  set N := lastRecord rho H δ x with hNdef
  by_cases hN : N = ⊤
  · have : expMul t N = ⊤ := by simp [expMul, hN]
    rw [this]
    refine le_trans (le_of_eq ?_) le_add_self
    symm
    apply ENNReal.eq_top_of_forall_nnreal_le
    intro r
    set M : ℕ := ⌈(r : ℝ) / t⌉₊ + K0 with hM
    have hMlt : ((M : ℕ) : ℕ∞) < N := by rw [hN]; exact ENat.coe_lt_top M
    rw [hNdef, lastRecord] at hMlt
    obtain ⟨k, hk⟩ := lt_iSup_iff.1 hMlt
    obtain ⟨hrec, hk2⟩ := lt_iSup_iff.1 hk
    have hMk : M < k := by exact_mod_cast hk2
    have hK0k : K0 < k := by omega
    refine le_trans ?_ (ENNReal.le_tsum k)
    rw [if_pos ⟨hK0k, hrec⟩, ← ENNReal.ofReal_coe_nnreal]
    apply ENNReal.ofReal_le_ofReal
    have h1 : (r : ℝ) / t ≤ ⌈(r : ℝ) / t⌉₊ := Nat.le_ceil _
    have h2 : (⌈(r : ℝ) / t⌉₊ : ℝ) ≤ k := by exact_mod_cast (by omega : ⌈(r : ℝ) / t⌉₊ ≤ k)
    have h3 : (r : ℝ) ≤ t * k := by
      rw [div_le_iff₀ ht] at h1; nlinarith
    have h4 := Real.add_one_le_exp (t * k)
    linarith
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hN
    have hval : expMul t N = ENNReal.ofReal (Real.exp (t * n)) := by
      simp [expMul, ← hn]
    rw [hval]
    by_cases hnK : n ≤ K0
    · refine le_trans ?_ le_self_add
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.2
      have : (n : ℝ) ≤ K0 := by exact_mod_cast hnK
      nlinarith
    · push Not at hnK
      have hlt : (((n - 1 : ℕ)) : ℕ∞) < N := by
        rw [← hn]; exact_mod_cast (by omega : n - 1 < n)
      rw [hNdef, lastRecord] at hlt
      obtain ⟨k, hk⟩ := lt_iSup_iff.1 hlt
      obtain ⟨hrec, hk2⟩ := lt_iSup_iff.1 hk
      have hkN : (k : ℕ∞) ≤ N := by
        rw [hNdef, lastRecord]
        exact le_iSup₂ (f := fun k (_ : IsRecord rho H δ x k) => (k : ℕ∞)) k hrec
      rw [← hn] at hkN
      have hkn : k ≤ n := by exact_mod_cast hkN
      have hk2' : n - 1 < k := by exact_mod_cast hk2
      have hkeq : k = n := by omega
      subst hkeq
      refine le_trans ?_ le_add_self
      refine le_trans ?_ (ENNReal.le_tsum k)
      rw [if_pos ⟨hnK, hrec⟩]

end FBM36Aux

open FBMStrongSim.RecordBreak FBM36Aux

theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {H delta rho : ℝ} (hH0 : 0 < H) (hH1 : H < 1) (hdelta0 : 0 < delta) (hdeltaH : delta < H)
    (hrho : 0 < rho) {B : ℝ → Ω → ℝ} (hB : IsFBM H B P)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun t => B t ω) (Set.Icc 0 1)) :
    (∀ t : ℝ, 0 < t → ∫⁻ ω, expMul t (lastRecord rho H delta (fun s => B s ω)) ∂P < ⊤) ∧
    (∀ᵐ ω ∂P, ∀ n : ℕ, lastRecord rho H delta (fun s => B s ω) < n →
      ∀ s ∈ Set.Icc (0 : ℝ) 1, |B s ω - interp (fun s => B s ω) n s|
        ≤ rho * (2 : ℝ) ^ (-(H - delta) * ((n : ℝ) + 1)) / (1 - (2 : ℝ) ^ (-(H - delta)))) := by
  constructor
  · intro t ht
    set nu : ℝ := rho / 4 with hnudef
    have hnu : 0 < nu := by rw [hnudef]; linarith
    set K0 : ℕ := Knu nu delta with hK0
    set c : ℝ := nu ^ 2 with hc
    set a : ℝ := c * (2 * Real.log 2 * delta) ^ 2 / 8 with ha
    have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
    have ha0 : 0 < a := by rw [ha, hc]; positivity
    set A : ℕ → Set Ω := fun k => {ω | rho * ell H delta k ≤ maxDisp (fun s => B s ω) k} with hAdef
    have hA : ∀ k : ℕ, K0 < k →
        P (A k) ≤ ENNReal.ofReal (2 * Real.exp (-c * (2 : ℝ) ^ (2 * (k : ℝ) * delta - 2))) := by
      intro k hk
      have h31 := FBMStrongSim.RecordBreak.theorem_3_1 hH0 hH1 hdelta0 hdeltaH hB hnu hnu hk
      have e : 2 * (nu + nu) = rho := by rw [hnudef]; ring
      rw [e] at h31
      exact h31
    set f : ℕ → ℝ := fun k => 2 * Real.exp ((t + 1) ^ 2 / (4 * a)) * Real.exp (-1) ^ k with hfdef
    have hf0 : ∀ k, 0 ≤ f k := fun k => by rw [hfdef]; positivity
    have hsum : Summable f :=
      (summable_geometric_of_lt_one (Real.exp_pos _).le
        (Real.exp_lt_one_iff.2 (by norm_num))).mul_left _
    set cf : ℕ → ℝ≥0∞ := fun k => if K0 < k then ENNReal.ofReal (Real.exp (t * k)) else 0
      with hcf
    have hle : ∀ ω, expMul t (lastRecord rho H delta (fun s => B s ω)) ≤
        ENNReal.ofReal (Real.exp (t * K0)) +
          ∑' k, (toMeasurable P (A k)).indicator (fun _ => cf k) ω := by
      intro ω
      classical
      refine le_trans (expMul_le _ rho H delta t ht K0)
        (add_le_add_right (ENNReal.tsum_le_tsum fun k => ?_) _)
      split_ifs with h
      · have hmem : ω ∈ toMeasurable P (A k) := subset_toMeasurable _ _ h.2.2
        rw [Set.indicator_of_mem hmem]
        simp [hcf, h.1]
      · exact zero_le
    have hterm : ∀ k, cf k * P (A k) ≤ ENNReal.ofReal (f k) := by
      intro k
      by_cases hk : K0 < k
      · simp only [hcf, if_pos hk]
        calc ENNReal.ofReal (Real.exp (t * k)) * P (A k)
            ≤ ENNReal.ofReal (Real.exp (t * k)) *
                ENNReal.ofReal (2 * Real.exp (-c * (2 : ℝ) ^ (2 * (k : ℝ) * delta - 2))) :=
              mul_le_mul_right (hA k hk) _
          _ = ENNReal.ofReal (Real.exp (t * k) *
                (2 * Real.exp (-(c * (2 : ℝ) ^ (2 * (k : ℝ) * delta - 2))))) := by
              rw [ENNReal.ofReal_mul (Real.exp_pos _).le, neg_mul]
          _ ≤ ENNReal.ofReal (f k) := by
              apply ENNReal.ofReal_le_ofReal
              have := tail_real t a ha0 k _ (quad_lower c delta (by rw [hc]; positivity) hdelta0 k)
              simpa [hfdef, ha] using this
      · simp [hcf, hk]
    calc ∫⁻ ω, expMul t (lastRecord rho H delta (fun s => B s ω)) ∂P
        ≤ ∫⁻ ω, (ENNReal.ofReal (Real.exp (t * K0)) +
            ∑' k, (toMeasurable P (A k)).indicator (fun _ => cf k) ω) ∂P := lintegral_mono hle
      _ = ENNReal.ofReal (Real.exp (t * K0)) + ∑' k, cf k * P (A k) := by
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
            lintegral_tsum (fun k => (measurable_const.indicator
              (measurableSet_toMeasurable _ _)).aemeasurable)]
          congr 1
          congr 1
          ext k
          rw [lintegral_indicator_const (measurableSet_toMeasurable _ _), measure_toMeasurable]
      _ ≤ ENNReal.ofReal (Real.exp (t * K0)) + ∑' k, ENNReal.ofReal (f k) :=
          add_le_add_right (ENNReal.tsum_le_tsum hterm) _
      _ < ⊤ := by
          rw [← ENNReal.ofReal_tsum_of_nonneg hf0 hsum]
          exact ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩
  · filter_upwards [hcont] with ω hω n hn s hs
    have hk : ∀ k : ℕ, n < k → maxDisp (fun s => B s ω) k ≤ rho * ell H delta k := by
      intro k hk
      by_contra hcon
      push Not at hcon
      have hrec : IsRecord rho H delta (fun s => B s ω) k := ⟨by omega, hcon.le⟩
      have h1 : (k : ℕ∞) ≤ lastRecord rho H delta (fun s => B s ω) := by
        rw [lastRecord]
        exact le_iSup₂ (f := fun k (_ : IsRecord rho H delta (fun s => B s ω) k) => (k : ℕ∞))
          k hrec
      have h2 : (k : ℕ∞) < n := lt_of_le_of_lt h1 hn
      have h3 : k < n := by exact_mod_cast h2
      omega
    have hdb := det_bound _ hω rho H delta (by linarith) n hk s hs
    have he : (2 : ℝ) ^ (-(H - delta) * ((n : ℝ) + 1)) = ((2 : ℝ) ^ (-(H - delta))) ^ (n + 1) := by
      have := ell_eq H delta (n + 1)
      unfold ell at this
      push_cast at this
      exact this
    rw [he]
    exact hdb
