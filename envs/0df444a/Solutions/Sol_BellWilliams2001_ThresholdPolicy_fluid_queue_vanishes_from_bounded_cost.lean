-- Prove2me | solution 1 for BellWilliams2001.ThresholdPolicy.fluid_queue_vanishes_from_bounded_cost
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T06:30:35.624724+00:00
-- url     : https://prove2.me/submissions/e0075980-1e3e-46dd-9371-3918ca67eb95

import Theorems.Thm_BellWilliams2001_ThresholdPolicy_admissible_discounted_cost_aemeasurable
import Theorems.Thm_BellWilliams2001_ThresholdPolicy_primitive_fluid_limits_in_prob

open BellWilliams2001.ThresholdPolicy
open MeasureTheory Filter Topology Set
open scoped ENNReal

private theorem alloc_range {Ω : Type*} [MeasurableSpace Ω]
    (M : SystemSequence Ω) (n : ℕ) (T : Allocation Ω) (hA : M.IsAdmissible n T)
    (ω : Ω) (j : Fin 3) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    0 ≤ T ω j a ∧ T ω j a ≤ T ω j b ∧ T ω j b ≤ b ∧
      T ω j b - T ω j a ≤ b-a := by
  have ha' : a ∈ Ici (0:ℝ) := ha
  have hb' : b ∈ Ici (0:ℝ) := ha.trans hab
  have hz : (0:ℝ) ∈ Ici (0:ℝ) := mem_Ici.mpr le_rfl
  have nonNeg (j : Fin 3) : 0 ≤ T ω j a := by
    have h := hA.alloc_mono ω j hz ha' ha
    rwa [hA.alloc_zero] at h
  have mono (j : Fin 3) : T ω j a ≤ T ω j b := hA.alloc_mono ω j ha' hb' hab
  have hi₀ := hA.idle_mono ω 0 ha' hb' hab
  have hi₁ := hA.idle_mono ω 1 ha' hb' hab
  simp only [SystemSequence.idle, if_true, show (1:Fin 2) ≠ 0 by decide, if_false] at hi₀ hi₁
  have hd (j : Fin 3) : T ω j b - T ω j a ≤ b-a := by
    fin_cases j <;> simp at *
    · linarith
    · linarith [mono 2]
    · linarith [mono 1]
  have hCap (j : Fin 3) : T ω j b ≤ b := by
    have h0 := hA.idle_mono ω 0 hz hb' (ha.trans hab)
    have h1 := hA.idle_mono ω 1 hz hb' (ha.trans hab)
    rw [hA.idle_zero] at h0 h1
    simp only [SystemSequence.idle, if_true, show (1:Fin 2) ≠ 0 by decide, if_false] at h0 h1
    fin_cases j <;> simp at *
    · linarith
    · linarith [nonNeg 2,mono 2]
    · linarith [nonNeg 1,mono 1]
  exact ⟨nonNeg j,mono j,hCap j,hd j⟩

private theorem point_of_supDist {m : ℕ} {f g : ℝ → Fin m → ℝ} {H e s : ℝ} (he : 0 < e)
    (hs : s ∈ Icc 0 H) (h : supDist f g H < ENNReal.ofReal e) (i : Fin m) :
    |f s i - g s i| ≤ e := by
  have hsum : |f s i - g s i| ≤ ∑ j, |f s j-g s j| :=
    Finset.single_le_sum (fun j _ => abs_nonneg (f s j-g s j)) (Finset.mem_univ i)
  have h₁ : ENNReal.ofReal (∑ j,|f s j-g s j|) ≤ supDist f g H :=
    le_iSup_of_le s (le_iSup_of_le hs le_rfl)
  exact ((ENNReal.ofReal_lt_ofReal_iff he).1 ((ENNReal.ofReal_le_ofReal hsum).trans_lt (h₁.trans_lt h))).le


private theorem fluid_queue_balance {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω)
    (n : ℕ) (T : Allocation Ω) (ω : Ω) (t : ℝ) :
    M.Qbar n T ω t 0 = M.Abar n ω t 0 - M.Sbar n ω (M.Tbar n T ω t 0) 0 - M.Sbar n ω (M.Tbar n T ω t 1) 1 ∧
    M.Qbar n T ω t 1 = M.Abar n ω t 1 - M.Sbar n ω (M.Tbar n T ω t 2) 2 := by
  let R := M.r n^2
  have hR : 0 < R := pow_pos (zero_lt_one.trans_le (M.r_ge n)) _
  have hComp j : R*(T ω j (R*t)/R) = T ω j (R*t) := mul_div_cancel₀ _ hR.ne'
  constructor
  · simp only [SystemSequence.Qbar,SystemSequence.Abar,SystemSequence.Sbar,SystemSequence.Tbar,
      SystemSequence.queue,if_true,sub_div,←show R=M.r n^2 from rfl,hComp]
  · simp only [SystemSequence.Qbar,SystemSequence.Abar,SystemSequence.Sbar,SystemSequence.Tbar,
      SystemSequence.queue,show (1:Fin 2) ≠ 0 by decide,if_false,sub_div,←show R=M.r n^2 from rfl,hComp]

private theorem qbar_lower_on_interval {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω)
    (n : ℕ) (T : Allocation Ω) (hT : M.IsAdmissible n T) (ω : Ω)
    (H e : ℝ) (he : 0 ≤ e) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ H)
    (hA : ∀ s ∈ Icc 0 H, ∀ k, |M.Abar n ω s k-M.lam k*s| ≤ e)
    (hS : ∀ s ∈ Icc 0 H, ∀ j, |M.Sbar n ω s j-M.mu j*s| ≤ e) (k : Fin 2) :
    M.Qbar n T ω a k - ((∑ j, M.mu j)*(b-a)+6*e) ≤ M.Qbar n T ω b k := by
  let R := M.r n^2
  have hR : 0 < R := pow_pos (zero_lt_one.trans_le (M.r_ge n)) _
  have hservice (j : Fin 3) :
      M.Sbar n ω (M.Tbar n T ω b j) j - M.Sbar n ω (M.Tbar n T ω a j) j ≤ M.mu j*(b-a)+2*e := by
    obtain ⟨hn,hm,hCap,hd⟩ := alloc_range M n T hT ω j
      (mul_nonneg hR.le ha) (mul_le_mul_of_nonneg_left hab hR.le)
    have hBal : M.Tbar n T ω b j - M.Tbar n T ω a j ≤ b-a := by
      change T ω j (R*b)/R-T ω j (R*a)/R ≤ b-a
      rw [←sub_div,div_le_iff₀ hR]
      linarith only [hd]
    have hUB : M.Tbar n T ω b j ∈ Icc 0 H := ⟨div_nonneg (hn.trans hm) hR.le,
      ((div_le_iff₀ hR).2 (by simpa only [mul_comm b] using hCap)).trans hb⟩
    have hUA : M.Tbar n T ω a j ∈ Icc 0 H := ⟨div_nonneg hn hR.le,
      (div_le_div_of_nonneg_right hm hR.le).trans hUB.2⟩
    have hp := mul_le_mul_of_nonneg_left hBal (M.mu_pos j).le
    linarith [(abs_le.1 (hS _ hUB j)).2,(abs_le.1 (hS _ hUA j)).1]
  have harr : -(2*e) ≤ M.Abar n ω b k-M.Abar n ω a k := by
    have hp := mul_nonneg (M.lam_pos k).le (sub_nonneg.mpr hab)
    linarith [(abs_le.1 (hA a ⟨ha,hab.trans hb⟩ k)).2,(abs_le.1 (hA b ⟨ha.trans hab,hb⟩ k)).1]
  have hqa := fluid_queue_balance M n T ω a
  have hqb := fluid_queue_balance M n T ω b
  have hp (j : Fin 3) := mul_nonneg (M.mu_pos j).le (sub_nonneg.mpr hab)
  fin_cases k
  · change -(2*e) ≤ M.Abar n ω b 0-M.Abar n ω a 0 at harr
    change M.Qbar n T ω a 0 - ((∑ j, M.mu j)*(b-a)+6*e) ≤ M.Qbar n T ω b 0
    rw [hqa.1,hqb.1,Fin.sum_univ_three]
    linarith [hservice 0,hservice 1,hp 2]
  · change -(2*e) ≤ M.Abar n ω b 1-M.Abar n ω a 1 at harr
    change M.Qbar n T ω a 1 - ((∑ j, M.mu j)*(b-a)+6*e) ≤ M.Qbar n T ω b 1
    rw [hqa.2,hqb.2,Fin.sum_univ_three]
    linarith [hservice 2,hp 0,hp 1]

set_option maxHeartbeats 1650000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω)
    (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop) (T : ℕ → Allocation Ω)
    (hT : ∀ᶠ n in atTop, M.IsAdmissible (φ n) (T n))
    (B : ℝ) (hB : 0 ≤ B) (hCost : ∀ᶠ n in atTop, M.cost (φ n) (T n) ≤ ENNReal.ofReal B) :
    UocInProb M.P (fun n ω t => M.Qbar (φ n) (T n) ω t) (fun _ => 0) := by
  obtain ⟨hA,hS⟩ := primitive_fluid_limits_in_prob M
  intro H hH ε hε
  let v := ε/4
  let e := v/24
  let U := ∑ j, M.mu j
  have hv : 0 < v := by dsimp [v]; positivity
  have he : 0 < e := by dsimp [e]; positivity
  have hU : 0 ≤ U := Finset.sum_nonneg (fun _ _ => (M.mu_pos _).le)
  let d := v/(4*(U+1))
  have hd : 0 < d := by dsimp [d]; positivity
  have hdv : U*d+6*e ≤ v/2 := by
    have hm : 4*(U+1)*d = v := by dsimp [d]; field_simp
    have hp := mul_nonneg hd.le hU
    dsimp only [e]
    linarith only [hm,hd.le]
  have hH' : 0 ≤ H+d := by positivity
  let m := min (M.h 0) (M.h 1)
  have hm : 0 < m := lt_min (M.h_pos _) (M.h_pos _)
  let β := Real.exp (-M.gamma*(H+d))*m*(v/2)*d
  have hβ : 0 < β := by dsimp [β]; positivity
  let a (n : ℕ) : Set Ω := {ω | ENNReal.ofReal e ≤
    supDist (M.Abar (φ n) ω) (fun t k => M.lam k*t) (H+d)}
  let b (n : ℕ) : Set Ω := {ω | ENNReal.ofReal e ≤
    supDist (M.Sbar (φ n) ω) (fun t j => M.mu j*t) (H+d)}
  have ha : Tendsto (fun n => M.P (a n)) atTop (𝓝 0) := (hA _ hH' e he).comp hφ
  have hb : Tendsto (fun n => M.P (b n)) atTop (𝓝 0) := (hS _ hH' e he).comp hφ
  have hRate : Tendsto (fun n => M.r (φ n)*β) atTop atTop :=
    (M.r_tendsto.comp hφ).atTop_mul_const hβ
  have hRational : Tendsto (fun n => ENNReal.ofReal (B/(M.r (φ n)*β))) atTop (𝓝 0) := by
    have hh : Tendsto (fun n => B/(M.r (φ n)*β)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hRate
    simpa only [Function.comp_def,ENNReal.ofReal_zero] using (ENNReal.continuous_ofReal.tendsto 0).comp hh
  have hg := (ha.add hb).add hRational
  have hSum : Tendsto (fun n => M.P (a n)+M.P (b n)+ENNReal.ofReal (B/(M.r (φ n)*β))) atTop (𝓝 0) :=
    by simpa only [add_zero] using hg
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hSum
    (Eventually.of_forall (fun _ => bot_le))
  filter_upwards [hT,hCost] with n hAdm hBound
  let i := φ n
  let r := M.r i
  have hr : 0 < r := zero_lt_one.trans_le (M.r_ge i)
  let F (ω : Ω) := ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal
    (Real.exp (-M.gamma*t)*∑ k,M.h k*M.Qhat i (T n) ω t k) ∂volume
  let E : Set Ω := {ω | ENNReal.ofReal (r*β) ≤ F ω}
  have hEm : M.P E ≤ ENNReal.ofReal (B/(r*β)) := by
    have hFm : AEMeasurable F M.P := (admissible_discounted_cost_aemeasurable M i (T n) hAdm).2
    have hPos : 0 < r*β := mul_pos hr hβ
    calc
      _ ≤ (∫⁻ ω, F ω ∂M.P) / ENNReal.ofReal (r*β) :=
        meas_ge_le_lintegral_div hFm (ENNReal.ofReal_ne_zero_iff.mpr hPos) ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal B / ENNReal.ofReal (r*β) := ENNReal.div_le_div_right hBound _
      _ = _ := (ENNReal.ofReal_div_of_pos hPos).symm
  refine (measure_mono ?_).trans (((measure_union_le (a n ∪ b n) E).trans
    (add_le_add (measure_union_le _ _) hEm)))
  intro ω hω
  by_contra hn
  have hAp : supDist (M.Abar i ω) (fun t k => M.lam k*t) (H+d) < ENNReal.ofReal e :=
    lt_of_not_ge (fun h => hn (Or.inl (Or.inl h)))
  have hSp : supDist (M.Sbar i ω) (fun t j => M.mu j*t) (H+d) < ENNReal.ofReal e :=
    lt_of_not_ge (fun h => hn (Or.inl (Or.inr h)))
  have hQ0 (s : ℝ) (hs : 0 ≤ s) (k : Fin 2) : 0 ≤ M.Qbar i (T n) ω s k :=
    div_nonneg (hAdm.queue_nonneg ω k _ (mul_nonneg (sq_nonneg _) hs)) (sq_nonneg _)
  have hx : ∃ s ∈ Icc 0 H, ∃ k, v ≤ M.Qbar i (T n) ω s k := by
    by_contra! h
    have hSup : supDist (M.Qbar i (T n) ω) (fun _ => 0) H ≤ ENNReal.ofReal (ε/2) := by
      refine iSup_le fun s => iSup_le fun hs => ENNReal.ofReal_le_ofReal ?_
      rw [Fin.sum_univ_two]
      simp only [Pi.zero_apply,sub_zero,abs_of_nonneg (hQ0 s hs.1 0),abs_of_nonneg (hQ0 s hs.1 1)]
      dsimp [v] at h
      linarith [h s hs 0,h s hs 1]
    exact ((ENNReal.ofReal_lt_ofReal_iff hε).2 (by linarith)).not_ge (hω.trans hSup)
  obtain ⟨s,hs,k,hk⟩ := hx
  have hQ (u : ℝ) (hu : u ∈ Ioc s (s+d)) : v/2 ≤ M.Qbar i (T n) ω u k := by
    have huH : u ≤ H+d := hu.2.trans (add_le_add_left hs.2 _)
    have hQ := qbar_lower_on_interval M i (T n) hAdm ω (H+d) e he.le s u hs.1 hu.1.le huH
      (fun q hq => point_of_supDist he hq hAp) (fun q hq => point_of_supDist he hq hSp) k
    have hm := mul_le_mul_of_nonneg_left (show u-s ≤ d by linarith [hu.2]) hU
    linarith
  have hIn (u : ℝ) (hu : u ∈ Ioc s (s+d)) :
      ENNReal.ofReal (Real.exp (-M.gamma*(H+d))*m*(r*(v/2))) ≤
      ENNReal.ofReal (Real.exp (-M.gamma*u)*∑ k, M.h k*M.Qhat i (T n) ω u k) := by
    apply ENNReal.ofReal_le_ofReal
    have huH : u ≤ H+d := hu.2.trans (add_le_add_left hs.2 _)
    have hExp := Real.exp_le_exp.2 (mul_le_mul_of_nonpos_left huH (neg_nonpos.mpr M.gamma_pos.le))
    have hScale (j : Fin 2) : M.Qhat i (T n) ω u j = r * M.Qbar i (T n) ω u j := by
      dsimp [r,SystemSequence.Qhat,SystemSequence.Qbar]
      field_simp
    have hQ' : r*(v/2) ≤ M.Qhat i (T n) ω u k := by
      rw [hScale k]
      exact mul_le_mul_of_nonneg_left (hQ u hu) hr.le
    have hh : m ≤ M.h k := by fin_cases k <;> first | exact min_le_left _ _ | exact min_le_right _ _
    have hHp : m*(r*(v/2)) ≤ ∑ j, M.h j*M.Qhat i (T n) ω u j :=
      (mul_le_mul hh hQ' (by positivity) (M.h_pos k).le).trans (Finset.single_le_sum
        (fun j _ => mul_nonneg (M.h_pos j).le (div_nonneg (hAdm.queue_nonneg ω j _
          (mul_nonneg (sq_nonneg _) (hs.1.trans hu.1.le))) hr.le)) (Finset.mem_univ k))
    rw [mul_assoc]
    exact mul_le_mul hExp hHp (by positivity) (Real.exp_nonneg _)
  have hE : ω ∈ E := by
    let c := ENNReal.ofReal (Real.exp (-M.gamma*(H+d))*m*(r*(v/2)))
    change ENNReal.ofReal (r*β) ≤ F ω
    calc
      _ = ∫⁻ u in Ioc s (s+d), c ∂volume := by
        rw [lintegral_const,Measure.restrict_apply_univ,Real.volume_Ioc,add_sub_cancel_left]
        dsimp [c,β]
        rw [←ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
      _ ≤ ∫⁻ u in Ioc s (s+d), ENNReal.ofReal (Real.exp (-M.gamma*u)*∑ k, M.h k*M.Qhat i (T n) ω u k) ∂volume :=
        setLIntegral_mono' measurableSet_Ioc hIn
      _ ≤ F ω := by
        exact lintegral_mono_set (fun u hu => hs.1.trans_lt hu.1)
  exact hn (Or.inr hE)
