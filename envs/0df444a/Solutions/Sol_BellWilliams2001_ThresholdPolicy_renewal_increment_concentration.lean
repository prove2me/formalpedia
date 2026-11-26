-- Prove2me | solution 1 for BellWilliams2001.ThresholdPolicy.renewal_increment_concentration
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T06:08:58.391831+00:00
-- url     : https://prove2.me/submissions/66dd7e46-4d7d-413d-b992-13ab01c302b1

import Theorems.Thm_BellWilliams2001_ThresholdPolicy_iid_block_concentration
import Theorems.Thm_BellWilliams2001_ThresholdPolicy_renewal_increments_from_epoch_blocks

open BellWilliams2001.ThresholdPolicy
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

set_option maxHeartbeats 1400000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℕ → Ω → ℝ) (hW : ∀ j, Measurable (W j)) (hPos : ∀ j ω, 0 < W j ω)
    (hi : iIndepFun W P) (hid : ∀ j, IdentDistrib (W j) (W 0) P P)
    (hInt : Integrable (W 0) P) (hMean : ∫ ω, W 0 ω ∂P = 1)
    (hmom : ∃ a > 0, ∀ u ∈ Set.Ioo (-a) a, Integrable (fun ω => Real.exp (u * W 0 ω)) P)
    (A η : ℝ) (hA : 0 < A) (hη : 0 < η) :
    ∃ K C : ℝ, 0 < K ∧ 0 ≤ C ∧ ∀ (r rate t : ℝ), 1 ≤ Real.log r → 1 ≤ r →
      0 < rate → rate ≤ A → 0 ≤ t →
      let e (ω : Ω) (m : ℕ) := ∑ j ∈ Finset.range m, W j ω
      let N (ω : Ω) (s : ℝ) : ℝ := ((renewalCount (e ω) (rate * s)).toNat : ℝ)
      P {ω | ∃ u v : ℝ, 0 ≤ u ∧ u ≤ v ∧ v ≤ r^2*t ∧
        η*(v-u) + K*Real.log r < |N ω v - N ω u - rate*(v-u)|} ≤
        ENNReal.ofReal (C*(1+t)/r^6) := by
  let X (j : ℕ) (ω : Ω) := W j ω - 1
  have hXm (j : ℕ) : Measurable (X j) := (hW j).sub_const 1
  have hXi : iIndepFun X P := hi.comp (fun _ (x : ℝ) => x-1) (fun _ => measurable_id.sub_const _)
  have hXd (j : ℕ) : IdentDistrib (X j) (X 0) P P := (hid j).comp (measurable_id.sub_const _)
  have hXzero : ∫ ω, X 0 ω ∂P = 0 := by
    simp only [X,integral_sub hInt (integrable_const _),hMean]
    simp
  have hXmom : ∃ a > 0, ∀ u ∈ Ioo (-a) a, Integrable (fun ω => Real.exp (u * X 0 ω)) P := by
    obtain ⟨a,ha,h⟩ := hmom
    refine ⟨a,ha,fun u hu => ?_⟩
    refine ((h u hu).mul_const (Real.exp (-u))).congr (ae_of_all _ fun ω => ?_)
    dsimp only [X]
    rw [← Real.exp_add]
    congr 1
    ring
  let δ := min (1/2:ℝ) (η/(2*A))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδh : δ ≤ 1/2 := min_le_left _ _
  have hδη : 2*δ*A ≤ η := by
    have hh := (le_div_iff₀ (show 0 < 2*A by positivity)).1 (min_le_right (1/2:ℝ) (η/(2*A)))
    dsimp [δ]
    linarith only [hh]
  obtain ⟨ρ,hρ,hρ1,hTail⟩ := iid_block_concentration P X hXm hXi hXd hXzero hXmom δ hδ
  have hln : 0 < -Real.log ρ := neg_pos.mpr (Real.log_neg hρ hρ1)
  let b := 8/(-Real.log ρ)
  have hb : 0 < b := by dsimp [b]; positivity
  let K := 2*(b+1)
  let C := 2*(2*A+2*(b+1)+1)
  refine ⟨K,C,by dsimp [K]; positivity,by dsimp [C]; positivity,?_⟩
  intro r rate t hrlog hr hrate hrateA ht
  let e (ω : Ω) (m : ℕ) := ∑ j ∈ Finset.range m, W j ω
  let count (ω : Ω) (s : ℝ) : ℝ := ((renewalCount (e ω) (rate*s)).toNat : ℝ)
  let m := ⌈b * Real.log r⌉₊
  have hml : b*Real.log r ≤ (m:ℝ) := Nat.le_ceil _
  have hm : 0 < m := by
    have hh := (mul_pos hb (zero_lt_one.trans_le hrlog)).trans_le hml
    exact_mod_cast hh
  have hm₀ : (0:ℝ) < m := by exact_mod_cast hm
  have hmu : (m:ℝ) ≤ (b+1)*Real.log r := by
    have h := (Nat.ceil_lt_add_one (show 0 ≤ b*Real.log r by positivity)).le
    linarith
  let H := rate*r^2*t
  have hH : 0 ≤ H := by dsimp [H]; positivity
  let z := ⌈2*H/(m:ℝ)⌉₊
  let N := m*(z+1)
  have hNl : 2*H < (N:ℝ) := by
    have h1 := Nat.le_ceil (2*H/(m:ℝ))
    have h2 := (div_le_iff₀ hm₀).1 h1
    dsimp [N,z] at *
    push_cast
    linarith only [h2,hm₀]
  have hNu : (N:ℝ) ≤ 2*H+2*(m:ℝ) := by
    have h1 := (Nat.ceil_lt_add_one (show 0 ≤ 2*H/(m:ℝ) by positivity)).le
    have h2 := mul_le_mul_of_nonneg_right h1 hm₀.le
    rw [add_mul, div_mul_cancel₀ _ hm₀.ne', one_mul] at h2
    dsimp [N,z]
    push_cast
    linarith only [h2]
  have hR : 0 < r := zero_lt_one.trans_le hr
  have hR2 : 1 ≤ r^2 := one_le_pow₀ hr
  have hLogR : Real.log r ≤ r^2 := by
    have h := Real.log_le_sub_one_of_pos hR
    nlinarith [mul_nonneg hR.le (sub_nonneg.mpr hr)]
  have hNu' : (N:ℝ)+1 ≤ (2*A+2*(b+1)+1)*r^2*(1+t) := by
    have h1 := mul_le_mul_of_nonneg_right hrateA (show 0 ≤ r^2*t by positivity)
    have h2 := mul_le_mul_of_nonneg_left hLogR (show 0 ≤ b+1 by positivity)
    have h3 : 0 ≤ (2*A+2*(b+1)+1)*r^2 := by positivity
    have h4 := mul_nonneg h3 ht
    have h5 := mul_nonneg (show 0 ≤ 2*(b+1)+1 by positivity) (show 0 ≤ r^2*t by positivity)
    dsimp [H] at hNu
    nlinarith
  have hρm : ρ^m ≤ (r^8)⁻¹ := by
    have hge := mul_le_mul_of_nonneg_right hml hln.le
    have he : b * (-Real.log ρ) = 8 := div_mul_cancel₀ _ hln.ne'
    have hm' : Real.log ρ * (m:ℝ) ≤ -((8:ℝ)*Real.log r) := by
      calc
        _ ≤ Real.log ρ * (b * Real.log r) := mul_le_mul_of_nonpos_left hml (by linarith)
        _ = _ := by
          have he' : Real.log ρ * b = -8 := by linarith only [he]
          rw [← mul_assoc,he']; ring
    have hx := Real.exp_le_exp.mpr hm'
    rw [mul_comm (Real.log ρ) (m:ℝ),Real.exp_nat_mul,Real.exp_log hρ,Real.exp_neg] at hx
    exact hx.trans_eq (by rw [show (8:ℝ) = ((8:ℕ):ℝ) by norm_num, Real.exp_nat_mul,Real.exp_log hR])
  let bad (j : ℕ) : Set Ω := {ω | δ*(m:ℝ) ≤ |∑ i ∈ Finset.range m, X (j+i) ω|}
  let E := ⋃ j ∈ Finset.range (N+1), bad j
  have hBadBound : P E ≤ ENNReal.ofReal (C*(1+t)/r^6) := by
    calc
      _ ≤ ∑ j ∈ Finset.range (N+1), P (bad j) := measure_biUnion_finset_le _ _
      _ ≤ ∑ _j ∈ Finset.range (N+1), ENNReal.ofReal (2*ρ^m) :=
        Finset.sum_le_sum (fun j _ => hTail j m)
      _ = ENNReal.ofReal (((N:ℝ)+1)*(2*ρ^m)) := by
        simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        norm_num
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by
        calc
          _ ≤ ((2*A+2*(b+1)+1)*r^2*(1+t))*(2*(r^8)⁻¹) := by
            exact mul_le_mul hNu' (mul_le_mul_of_nonneg_left hρm (by norm_num)) (by positivity) (by positivity)
          _ = _ := by dsimp [C]; field_simp <;> ring)
  refine (measure_mono ?_).trans hBadBound
  intro ω hω
  obtain ⟨u,v,hu,huv,hvt,hbad⟩ := hω
  by_contra hh
  have hB (j : ℕ) (hj : j ≤ N) : |e ω (j+m) - e ω j - (m:ℝ)| ≤ δ*m := by
    have hn : ω ∉ bad j := by
      intro hi
      exact hh (mem_iUnion.2 ⟨j,mem_iUnion.2 ⟨Finset.mem_range.2 (by omega),hi⟩⟩)
    have heq : e ω (j+m)-e ω j-(m:ℝ) = ∑ i ∈ Finset.range m, X (j+i) ω := by
      simp [e,X,Finset.sum_range_add,Finset.sum_sub_distrib,add_sub_cancel_left]
    rw [heq]
    exact (lt_of_not_ge hn).le
  have hE : StrictMono (e ω) := strictMono_nat_of_lt_succ fun j => by
    simpa [e,Finset.sum_range_succ] using hPos j ω
  have hCnt := renewal_increments_from_epoch_blocks (e ω) hE (by simp [e]) m hm N (dvd_mul_right _ _)
    H hH hNl δ hδ.le hδh hB (rate*u) (rate*v) (mul_nonneg hrate.le hu)
    (mul_le_mul_of_nonneg_left huv hrate.le) (by dsimp [H]; nlinarith [mul_le_mul_of_nonneg_left hvt hrate.le])
  have htime : rate * v - rate * u = rate*(v-u) := by ring
  rw [htime] at hCnt
  have he : 2*δ*rate ≤ η := (by gcongr : 2*δ*rate ≤ 2*δ*A).trans hδη
  have hbound : |count ω v-count ω u-rate*(v-u)| ≤ η*(v-u)+K*Real.log r := by
    refine hCnt.trans ?_
    dsimp [K]
    have h1 := mul_le_mul_of_nonneg_right he (sub_nonneg.mpr huv)
    linarith only [h1,hmu]
  exact hbad.not_ge hbound
