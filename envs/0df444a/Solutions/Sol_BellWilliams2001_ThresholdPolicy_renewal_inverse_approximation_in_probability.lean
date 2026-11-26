-- Prove2me | solution 1 for BellWilliams2001.ThresholdPolicy.renewal_inverse_approximation_in_probability
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T06:40:52.602075+00:00
-- url     : https://prove2.me/submissions/ce83686b-1e8e-4ccb-ab99-31b2f016dd8b

import Theorems.Thm_ManyServerQED_Scheduling_weak_continuous_path_laws_control_norm_and_modulus
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths

open MeasureTheory ProbabilityTheory Filter Topology Set DurrettProbability
open BellWilliams2001.ThresholdPolicy
open scoped ENNReal NNReal

private abbrev I := Icc (0:ℝ) 1

private theorem renewal_bracket {e : ℕ → ℝ} (he : StrictMono e) {s : ℝ} {m : ℕ}
    (h0 : e 0 ≤ s) (hm : s < e m) :
    ∃ j < m, e j ≤ s ∧ s < e (j + 1) ∧ renewalCount e s = j := by
  have hExists : ∃ i, s < e i := ⟨m, hm⟩
  let b := Nat.find hExists
  have hb : s < e b := Nat.find_spec hExists
  have hb_le : b ≤ m := Nat.find_min' hExists hm
  have hb_pos : 0 < b := by
    by_contra! hb0
    rw [Nat.eq_zero_of_le_zero hb0] at hb
    exact (not_lt_of_ge h0) hb
  let j := b - 1
  have hsucc : j + 1 = b := by dsimp [j]; omega
  have hj_lt : j < b := by omega
  have hj : e j ≤ s := le_of_not_gt (Nat.find_min hExists hj_lt)
  have hj_succ : s < e (j + 1) := by rwa [hsucc]
  refine ⟨j, hj_lt.trans_le hb_le, hj, hj_succ, le_antisymm ?_ ?_⟩
  · unfold renewalCount
    refine iSup_le fun r => iSup_le fun hr => ?_
    have h : r ≤ j := by
      by_contra! hjr
      exact (not_lt_of_ge hr) (hj_succ.trans_le (he.monotone hjr))
    exact_mod_cast h
  · unfold renewalCount
    exact le_iSup_of_le j (le_iSup_of_le hj le_rfl)

set_option maxHeartbeats 850000 in
private theorem local_renewal_sandwich (n : ℕ) (hn : 1 ≤ n) (e : ℕ → ℝ) (he : StrictMono e) (he0 : e 0 = 0)
    (u : ℝ → ℝ) (H : ℝ) (hgrid : ∀ j : ℕ, (j:ℝ)/n ≤ H → u ((j:ℝ)/n) = (e j-j)/Real.sqrt n)
    (a T D δ ε : ℝ) (ha : 0 ≤ a) (hT : 0 ≤ T) (hH : a*T+3 ≤ H)
    (hD : ∀ s ∈ Set.Icc (0:ℝ) H, |u s| ≤ D)
    (hDsmall : D/Real.sqrt n < min 1 (δ/4))
    (hNsmall : 1/(n:ℝ) < δ/4) (hRsmall : 1/Real.sqrt n < ε/4) (hε : 0 < ε)
    (hMod : ∀ s ∈ Set.Icc (0:ℝ) H, ∀ t ∈ Set.Icc (0:ℝ) H,
      |s-t| < δ → |u s-u t| < ε/2) :
    ∀ t ∈ Set.Icc (0:ℝ) T,
      |(((renewalCount e ((n:ℝ)*a*t)).toNat:ℝ) - (n:ℝ)*a*t)/Real.sqrt n + u (a*t)| < ε := by
  intro t ht
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith
  have hsqrt : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.2 hn0
  have hdiv1 : 1/(n:ℝ) ≤ 1 := by rwa [div_le_one hn0]
  have haT : a*t ≤ H-3 :=
    (mul_le_mul_of_nonneg_left ht.2 ha).trans (by linarith)
  have hvt : a*t ∈ Set.Icc 0 H := ⟨mul_nonneg ha ht.1,by linarith⟩
  let m : ℕ := ⌈(n:ℝ)*(H-1)⌉₊
  have hhm : H-1 ≤ (m:ℝ)/n := by
    apply (le_div_iff₀ hn0).2
    simpa [m,mul_comm] using (Nat.le_ceil ((n:ℝ)*(H-1)))
  have hmH : (m:ℝ)/n ≤ H := by
    have hH1 : 0 ≤ H-1 := by nlinarith [mul_nonneg ha hT]
    have hce := (Nat.ceil_lt_add_one (mul_nonneg hn0.le hH1)).le
    have he : (m:ℝ)/n ≤ (H-1)+1/(n:ℝ) := by
      apply (div_le_iff₀ hn0).2
      rw [add_mul, div_mul_cancel₀ _ hn0.ne']
      exact (by simpa only [m, mul_comm (H-1)] using hce)
    linarith
  have hDiv (j : ℕ) (hj : j ≤ m) : (j:ℝ)/n ∈ Set.Icc 0 H :=
    ⟨by positivity, (div_le_div_of_nonneg_right (by exact_mod_cast hj) hn0.le).trans hmH⟩
  have hDiff (j : ℕ) (hj : j ≤ m) : |(e j)/(n:ℝ) - (j:ℝ)/n| ≤ D / Real.sqrt n := by
    have huB := hD _ (hDiv j hj)
    have hcalc : e j/(n:ℝ) - (j:ℝ)/n = (e j - j) / Real.sqrt n / Real.sqrt n := by
      rw [← sub_div, div_div, ← pow_two, Real.sq_sqrt hn0.le]
    rw [hcalc, ← hgrid j (hDiv j hj).2, abs_div, abs_of_pos hsqrt]
    exact div_le_div_of_nonneg_right huB hsqrt.le
  have hStop : (n:ℝ) * a * t < e m := by
    calc
      _ = (a*t) * n := by ring
      _ < (e m / (n:ℝ)) * n := by
        apply mul_lt_mul_of_pos_right _ hn0
        have hdiff := (abs_le.mp (hDiff m le_rfl)).1
        linarith [(lt_min_iff.mp hDsmall).1]
      _ = _ := div_mul_cancel₀ _ hn0.ne'
  obtain ⟨j, hj, hjL, hjR, hCount⟩ := renewal_bracket (he)
    (by rw [he0]; exact mul_nonneg (mul_nonneg hn0.le (ha)) ht.1) hStop
  have hjm : j+1 ≤ m := Nat.succ_le_of_lt hj
  have hrot : (n:ℝ) * a * t = a * t * (n:ℝ) := by ring
  have hL : (e j)/(n:ℝ) ≤ a*t := by
    rw [div_le_iff₀ hn0]
    exact hrot ▸ hjL
  have hR : a*t < (e (j+1))/(n:ℝ) := by
    rw [lt_div_iff₀ hn0]
    exact hrot ▸ hjR
  have hNext : ((j+1:ℕ):ℝ)/(n:ℝ) = (j:ℝ)/n + 1/n := by
    simp [add_div]
  have hNear0 : |(j:ℝ)/n - a*t| < δ/2 := by
    have hdiff1 := abs_le.mp (hDiff j hj.le)
    have hdiff2 := abs_le.mp (hDiff (j+1) hjm)
    rw [hNext] at hdiff2
    exact abs_lt.mpr ⟨by linarith [(lt_min_iff.mp hDsmall).2], by linarith [(lt_min_iff.mp hDsmall).2]⟩
  have hNear1 : |((j+1:ℕ):ℝ)/(n:ℝ) - a*t| < δ/2 := by
    have hdiff1 := abs_le.mp (hDiff j hj.le)
    have hdiff2 := abs_le.mp (hDiff (j+1) hjm)
    rw [hNext] at hdiff2 ⊢
    exact abs_lt.mpr ⟨by linarith [(lt_min_iff.mp hDsmall).2], by linarith [(lt_min_iff.mp hDsmall).2]⟩
  have hLocal (k : ℕ) (hk : k ≤ m) (hh : |(k:ℝ)/n - a*t| < δ/2) :
      |u ((k:ℝ)/n) - u (a*t)| < ε/2 := by
    have hδ : 0 < δ := by linarith [show 0 ≤ 1/(n:ℝ) by positivity]
    exact hMod _ (hDiv k hk) _ hvt (hh.trans (by linarith))
  have hu0 := (abs_lt.mp (hLocal j hj.le hNear0)).1
  have hu1 := (abs_lt.mp (hLocal (j+1) hjm hNear1)).2
  have hupper : ((j:ℝ) - (n:ℝ)*a*t) / Real.sqrt n ≤ -u ((j:ℝ)/n) := by
    rw [hgrid j (hDiv j hj.le).2, ← neg_div]
    exact div_le_div_of_nonneg_right (by linarith) hsqrt.le
  have hlower : -u (((j+1:ℕ):ℝ)/n) - 1/Real.sqrt n <
      ((j:ℝ) - (n:ℝ)*a*t) / Real.sqrt n := by
    rw [hgrid (j+1) (hDiv (j+1) hjm).2, ← neg_div, ← sub_div]
    apply div_lt_div_of_pos_right _ hsqrt
    push_cast
    linarith
  rw [hCount, ENat.toNat_natCast]
  exact abs_lt.mpr ⟨by linarith, by linarith⟩


set_option maxHeartbeats 1300000 in
theorem solution {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (Y : ℕ → Ω → PathSpace) (Z : Ω' → PathSpace)
    (h : TendstoInDistribution Y atTop Z (fun _ => P) P')
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (q J : ℝ) (hq : 0 < q) (hJ : 0 < J)
    (e : ℕ → Ω → ℕ → ℝ) (he : ∀ n ω, StrictMono (e n ω)) (he0 : ∀ n ω, e n ω 0 = 0)
    (aN : ℕ → ℝ) (haN : ∀ n, 0 ≤ aN n) (T : ℝ) (hT : 0 ≤ T)
    (hH : ∀ᶠ n in atTop, aN n*T+3 ≤ J)
    (hg : ∀ (n : ℕ), 1 ≤ m n → ∀ ω (j : ℕ), (j:ℝ)/m n ≤ J →
      q*Y n ω (projIcc 0 1 zero_le_one (((j:ℝ)/m n)/J)) =
        (e n ω j-j)/Real.sqrt (m n)) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => P {ω | ∃ t ∈ Icc (0:ℝ) T,
        ε ≤ |(((renewalCount (e n ω) ((m n:ℝ)*aN n*t)).toNat:ℝ) - (m n:ℝ)*aN n*t)/Real.sqrt (m n) +
          q*Y n ω (projIcc 0 1 zero_le_one (aN n*t/J))|}) atTop (𝓝 0) := by
  intro ε hε
  apply (ENNReal.tendsto_nhds_zero.2)
  intro η hη
  obtain ⟨η',_,hη',hη'E⟩ := ENNReal.lt_iff_exists_real_btwn.1 hη
  have hη0 : 0 < η' := ENNReal.ofReal_pos.1 hη'
  obtain ⟨A,hA,δ,hδ,htight⟩ := ManyServerQED.Scheduling.weak_continuous_path_laws_control_norm_and_modulus Y Z h (ε/(2*q)) η'
    (by positivity) hη0
  have hsq : Tendsto (fun n : ℕ => Real.sqrt (m n)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hm)
  have hD0 : Tendsto (fun n : ℕ => (q*A)/Real.sqrt (m n)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hsq
  have hN0 : Tendsto (fun n : ℕ => 1/(m n:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hm)
  have hR0 : Tendsto (fun n : ℕ => 1/Real.sqrt (m n)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hsq
  filter_upwards [htight,hH,hm (eventually_ge_atTop (1:ℕ)),
    (tendsto_order.1 hD0).2 _ (show 0 < min 1 ((J*δ)/4) by positivity),
    (tendsto_order.1 hN0).2 _ (show 0 < J*δ/4 by positivity),
    (tendsto_order.1 hR0).2 _ (show 0 < ε/4 by positivity)]
    with n hn hnn hn0 hDsm hNsm hRsm
  refine (measure_mono ?_).trans (hn.trans hη'E.le)
  intro ω hω
  by_contra! hbad
  have hSup : ‖Y n ω‖ < A := lt_of_not_ge (fun h => hbad (Or.inl h))
  have hMod (s t : I) (hst : dist s t ≤ δ) : |Y n ω s-Y n ω t| < ε/(2*q) :=
    lt_of_not_ge (fun hh => hbad (Or.inr ⟨s,t,hst,hh⟩))
  let c (s : ℝ) : I := projIcc 0 1 zero_le_one (s/J)
  let u (s : ℝ) := q*Y n ω (c s)
  have hc (s : ℝ) (hs : s ∈ Icc 0 J) : (c s : ℝ) = s/J := by
    have h0 : 0 ≤ s/J := div_nonneg hs.1 hJ.le
    have h1 : s/J ≤ 1 := (div_le_one hJ).2 hs.2
    simp [c,Set.projIcc,max_eq_right h0,min_eq_right h1]
  have hUb (s : ℝ) (_ : s ∈ Icc (0:ℝ) J) : |u s| ≤ q*A := by
    dsimp only [u]
    rw [abs_mul,abs_of_pos hq]
    apply mul_le_mul_of_nonneg_left _ hq.le
    have hN := ContinuousMap.norm_coe_le_norm (Y n ω) (c s)
    rw [Real.norm_eq_abs] at hN
    exact hN.trans hSup.le
  have hUm (s : ℝ) (hs : s ∈ Icc (0:ℝ) J) (t : ℝ) (ht : t ∈ Icc (0:ℝ) J)
      (hh : |s-t| < J*δ) : |u s-u t| < ε/2 := by
    have hd : dist (c s) (c t) ≤ δ := by
      rw [Subtype.dist_eq,Real.dist_eq,hc s hs,hc t ht,← sub_div,abs_div,abs_of_pos hJ]
      exact (div_le_iff₀ hJ).2 (by simpa [mul_comm] using hh.le)
    have h := hMod (c s) (c t) hd
    dsimp only [u]
    rw [← mul_sub,abs_mul,abs_of_pos hq]
    have he : q*(ε/(2*q)) = ε/2 := by field_simp
    exact (mul_lt_mul_of_pos_left h hq).trans_eq he
  obtain ⟨t,ht,hh⟩ := hω
  have hClose := local_renewal_sandwich (m n) hn0 (e n ω) (he n ω) (he0 n ω) u J
    (hg n hn0 ω) (aN n) T (q*A) (J*δ) ε (haN n) hT hnn hUb hDsm hNsm hRsm hε hUm t ht
  exact (not_lt_of_ge hh) hClose

