-- Prove2me | solution 1 for BellWilliams2001.ThresholdPolicy.primitive_diffusion_second_moment_majorants
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T06:29:13.451978+00:00
-- url     : https://prove2.me/submissions/ed6ebe0a-5dd3-4485-a4f8-9b3674864ab1

import Definitions.Def_BellWilliams2001_ThresholdPolicy_Workload
import Theorems.Thm_BellWilliams2001_ThresholdPolicy_renewal_inverse_moment

open BellWilliams2001.ThresholdPolicy
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

private theorem partialSum_shift (f : ℕ → ℝ) (m : ℕ) :
    partialSum f m = ∑ j ∈ Finset.range m, f (j+1) := by
  have he : Finset.Icc 1 m = Finset.Ico 1 (m+1) := by
    ext j
    simp only [Finset.mem_Icc,Finset.mem_Ico]
    omega
  simp only [partialSum,he,Finset.sum_Ico_eq_sum_range,Nat.add_sub_cancel,Nat.add_comm 1]

private theorem scaled_count_second_moment {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U (i+1)))
    (hpos : ∀ i ω, 0 < U (i+1) ω) (hI : iIndepFun (fun i => U (i+1)) P)
    (hid : ∀ i, IdentDistrib (U (i+1)) (U 1) P P)
    (hfin : ∀ ω, Tendsto (partialSum (fun i => U i ω)) atTop atTop)
    (hLp : MemLp (U 1) 2 P) (hmean : ∫ ω, U 1 ω ∂P = 1)
    (rate : ℕ → ℝ) (hrate : ∀ n, 0 < rate n) (D : ℝ) (hD : 1 ≤ D)
    (hD' : ∀ n, rate n ≤ D) (r : ℕ → ℝ) (hr : ∀ n, 1 ≤ r n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n (t : ℝ), 0 ≤ t → ∃ J : Ω → ℝ≥0∞, Measurable J ∧
      (∫⁻ ω, J ω ∂P) ≤ ENNReal.ofReal (C*(1+t)) ∧
      ∀ ω s, 0 ≤ s → s ≤ t →
        let e := partialSum (fun i => U i ω / rate n)
        (ENNReal.ofReal |((renewalCount e (r n^2*s)).toNat:ℝ) / r n - rate n*(r n^2*s)/r n|)^2 ≤ J ω := by
  let W (i : ℕ) := U (i+1)
  have hsum (ω : Ω) (m : ℕ) : (∑ i ∈ Finset.range m,W i ω) = partialSum (fun i => U i ω) m :=
    (partialSum_shift (fun i => U i ω) m).symm
  have hfin' (ω : Ω) : Tendsto (fun m => ∑ i ∈ Finset.range m,W i ω) atTop atTop := by
    simpa only [hsum] using hfin ω
  have hInt (i : ℕ) : Integrable (W i) P := ((hid i).memLp_iff.2 hLp).integrable (by norm_num)
  have hMean (i : ℕ) : ∫ ω, W i ω ∂P = 1 := (hid i).integral_eq.trans hmean
  have h2 : MemLp (fun ω => W 0 ω - 1) 2 P := hLp.sub (memLp_const 1)
  have hFin2 : (∫⁻ ω, (ENNReal.ofReal |W 0 ω-1|)^(2:ℝ) ∂P) < ⊤ := by
    simp_rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
    exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => sq_nonneg (W 0 x - 1))).1
      h2.integrable_sq.hasFiniteIntegral
  obtain ⟨B,hB,hRen⟩ := renewal_inverse_moment P W hU hpos hI hid hfin' hInt hMean 2 le_rfl hFin2
  refine ⟨B*D,by positivity,fun n t ht => ?_⟩
  let H := rate n*r n^2*t
  have hH : 0 ≤ H := by dsimp [H]; positivity [hrate n,hr n]
  obtain ⟨J,hJ,hDom,hJint⟩ := hRen H hH
  have hr0 : 0 < r n := zero_lt_one.trans_le (hr n)
  have hr2 : 0 < r n^2 := pow_pos hr0 2
  let a := ENNReal.ofReal (1/(r n^2))
  refine ⟨fun ω => a*J ω,measurable_const.mul hJ,?_ ,?_⟩
  · rw [lintegral_const_mul' a _ ENNReal.ofReal_ne_top]
    refine (mul_le_mul_right hJint _).trans ?_
    have hq : (2:ℝ)/2 = 1 := by norm_num
    simp only [hq,Real.rpow_one,a,←ENNReal.ofReal_mul (by positivity : 0 ≤ 1/(r n^2))]
    apply ENNReal.ofReal_le_ofReal
    have hle : 1+H ≤ r n^2*(D*(1+t)) := by
      have hA := mul_le_mul_of_nonneg_right (hD' n) (show 0 ≤ r n^2*t by positivity)
      have hB := mul_le_mul_of_nonneg_left hD (sq_nonneg (r n))
      have hR : 1 ≤ r n^2 := one_le_pow₀ (hr n)
      dsimp [H]
      nlinarith
    calc
      _ = B*((1+H)/r n^2) := by ring
      _ ≤ B*(D*(1+t)) := mul_le_mul_of_nonneg_left
        ((div_le_iff₀ hr2).2 (by simpa only [mul_comm (D*(1+t))] using hle)) hB
      _ = _ := by ring
  · intro ω s hs hst
    let e := partialSum (fun i => U i ω / rate n)
    let u := rate n*(r n^2*s)
    have hu : 0 ≤ u := mul_nonneg (hrate n).le (mul_nonneg hr2.le hs)
    have huH : u ≤ H := by
      have h := mul_le_mul_of_nonneg_left hst (mul_nonneg (hrate n).le hr2.le)
      dsimp [H,u]
      simpa only [mul_assoc] using h
    have he (j : ℕ) : e j ≤ r n^2*s ↔ (∑ i ∈ Finset.range j,W i ω) ≤ u := by
      dsimp [e,u,W]
      rw [partialSum_shift,←Finset.sum_div,div_le_iff₀ (hrate n),mul_comm (r n^2*s)]
    have heq : renewalCount e (r n^2*s) = renewalCount (fun j => ∑ i ∈ Finset.range j,W i ω) u := by
      unfold renewalCount
      simp only [he]
    let g (v : ℝ) := (ENNReal.ofReal |((renewalCount (fun j => ∑ i ∈ Finset.range j,W i ω) v).toNat:ℝ)-v|)^(2:ℝ)
    have hsup : g u ≤ ⨆ v ∈ Icc 0 H, g v := by
      apply le_iSup_of_le u
      rw [iSup_pos (show u ∈ Icc 0 H from ⟨hu,huH⟩)]
    have hpt : g u ≤ J ω := hsup.trans (hDom ω)
    let d := |((renewalCount e (r n^2*s)).toNat:ℝ)-u|
    have hSame : ENNReal.ofReal (d^2) ≤ J ω := by
      simpa only [←heq,ENNReal.rpow_two,← ENNReal.ofReal_pow (abs_nonneg _) 2,d,g] using hpt
    change ENNReal.ofReal |((renewalCount e (r n^2*s)).toNat:ℝ)/r n-u/r n|^2 ≤ a*J ω
    rw [←sub_div,abs_div,abs_of_pos hr0,←ENNReal.ofReal_pow (div_nonneg (abs_nonneg _) hr0.le) 2]
    change ENNReal.ofReal ((d/r n)^2) ≤ a*J ω
    rw [div_pow,div_eq_inv_mul,ENNReal.ofReal_mul (inv_nonneg.mpr hr2.le)]
    simpa only [a,one_div] using mul_le_mul_right hSame (ENNReal.ofReal ((r n^2)⁻¹))

set_option maxHeartbeats 1500000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (t : ℝ), 0 ≤ t →
      ∃ (JA : Fin 2 → Ω → ℝ≥0∞) (JS : Fin 3 → Ω → ℝ≥0∞),
        (∀ k, Measurable (JA k) ∧ ∫⁻ ω, JA k ω ∂M.P ≤ ENNReal.ofReal (C*(1+t))) ∧
        (∀ j, Measurable (JS j) ∧ ∫⁻ ω, JS j ω ∂M.P ≤ ENNReal.ofReal (C*(1+t))) ∧
        ∀ ω s, 0 ≤ s → s ≤ t →
          (∀ k, (ENNReal.ofReal |M.Ahat n ω s k|)^2 ≤ JA k ω) ∧
          (∀ j, (ENNReal.ofReal |M.Shat n ω s j|)^2 ≤ JS j ω) := by
  letI : IsProbabilityMeasure M.P := M.isProb
  have hbA (k : Fin 2) : ∃ D : ℝ, 1 ≤ D ∧ ∀ n, M.lamR n k ≤ D := by
    obtain ⟨a,ha⟩ := (Metric.isBounded_range_of_tendsto _ (M.a31_iii k)).bddAbove
    exact ⟨max 1 a,le_max_left _ _,fun n => (ha ⟨n,rfl⟩).trans (le_max_right _ _)⟩
  have hbS (j : Fin 3) : ∃ D : ℝ, 1 ≤ D ∧ ∀ n, M.muR n j ≤ D := by
    obtain ⟨a,ha⟩ := (Metric.isBounded_range_of_tendsto _ (M.a31_iv j)).bddAbove
    exact ⟨max 1 a,le_max_left _ _,fun n => (ha ⟨n,rfl⟩).trans (le_max_right _ _)⟩
  choose Da hDa hDa' using hbA
  choose Ds hDs hDs' using hbS
  have ha (k : Fin 2) := scaled_count_second_moment M.P (M.uC k) (fun i => M.uC_meas k (i+1))
    (fun i ω => M.uC_pos k (i+1) ω (by omega))
    (M.indep.precomp (g := fun i => Sum.inl (k,i)) (by
      intro i j h; exact congrArg Prod.snd (Sum.inl.inj h)))
    (fun i => M.uC_ident k (i+1) (by omega)) (M.uC_finite k) (M.uC_memLp k) (M.uC_mean k)
    (fun n => M.lamR n k) (fun n => M.lamR_pos n k) (Da k) (hDa k) (hDa' k) M.r M.r_ge
  have hS (j : Fin 3) := scaled_count_second_moment M.P (M.vC j) (fun i => M.vC_meas j (i+1))
    (fun i ω => M.vC_pos j (i+1) ω (by omega))
    (M.indep.precomp (g := fun i => Sum.inr (j,i)) (by
      intro i k h; exact congrArg Prod.snd (Sum.inr.inj h)))
    (fun i => M.vC_ident j (i+1) (by omega)) (M.vC_finite j) (M.vC_memLp j) (M.vC_mean j)
    (fun n => M.muR n j) (fun n => M.muR_pos n j) (Ds j) (hDs j) (hDs' j) M.r M.r_ge
  choose Ca hCa ha using ha
  choose Cs hCs hs using hS
  let C := (∑ k, Ca k) + ∑ j, Cs j
  have hCa0 : 0 ≤ ∑ k, Ca k := Finset.sum_nonneg (fun k _ => hCa k)
  have hCs0 : 0 ≤ ∑ j, Cs j := Finset.sum_nonneg (fun j _ => hCs j)
  refine ⟨C,add_nonneg hCa0 hCs0,fun n t ht => ?_⟩
  choose JA hJAm hJAi hJAp using fun k => ha k n t ht
  choose JS hJSm hJSi hJSp using fun j => hs j n t ht
  have hA (i : Fin 2) : Ca i ≤ C :=
    (Finset.single_le_sum (fun k _ => hCa k) (Finset.mem_univ i)).trans (le_add_of_nonneg_right hCs0)
  have hB (i : Fin 3) : Cs i ≤ C :=
    (Finset.single_le_sum (fun j _ => hCs j) (Finset.mem_univ i)).trans (le_add_of_nonneg_left hCa0)
  refine ⟨JA,JS,fun k => ⟨hJAm k,(hJAi k).trans ?_⟩,fun j => ⟨hJSm j,(hJSi j).trans ?_⟩,?_⟩
  · exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hA k) (by positivity))
  · exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hB j) (by positivity))
  · intro ω s hs0 hst
    constructor
    · intro k
      rw [SystemSequence.Ahat,sub_div]
      exact hJAp k ω s hs0 hst
    · intro j
      rw [SystemSequence.Shat,sub_div]
      exact hJSp j ω s hs0 hst
