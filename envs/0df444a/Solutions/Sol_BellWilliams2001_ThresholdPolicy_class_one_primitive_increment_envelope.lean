-- Prove2me | solution 1 for BellWilliams2001.ThresholdPolicy.class_one_primitive_increment_envelope
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T06:09:12.814717+00:00
-- url     : https://prove2.me/submissions/1a884d18-01d9-4877-b28a-7dd54bcabd8f

import Definitions.Def_BellWilliams2001_ThresholdPolicy_Model
import Theorems.Thm_BellWilliams2001_ThresholdPolicy_renewal_increment_concentration

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

private theorem one_envelope {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℕ → Ω → ℝ) (hW : ∀ j, Measurable (W (j+1))) (hPos : ∀ j ω, 0 < W (j+1) ω)
    (hi : iIndepFun (fun j => W (j+1)) P)
    (hid : ∀ j, IdentDistrib (W (j+1)) (W 1) P P)
    (hint : Integrable (W 1) P) (hmean : ∫ ω, W 1 ω ∂P=1)
    (a : ℝ) (ha : 0 < a)
    (hmg : ∃ δ > 0, ∀ u ∈ Ioo (-δ) δ, Integrable (fun ω => Real.exp (u*(W 1 ω/a))) P)
    (A η : ℝ) (hA : 0 < A) (hη : 0 < η) :
    ∃ K C : ℝ, 0 < K ∧ 0 ≤ C ∧ ∀ (r rate t : ℝ), 1 ≤ Real.log r → 1 ≤ r →
      0 < rate → rate ≤ A → 0 ≤ t →
      let F (ω : Ω) (s : ℝ) : ℝ := ((renewalCount (partialSum (fun i => W i ω / rate)) s).toNat:ℝ)
      P {ω | ∃ u v : ℝ, 0 ≤ u ∧ u ≤ v ∧ v ≤ r^2*t ∧
        η*(v-u)+K*Real.log r < |F ω v - F ω u - rate*(v-u)|} ≤
          ENNReal.ofReal (C*(1+t)/r^6) := by
  have hmom : ∃ δ > 0, ∀ u ∈ Ioo (-δ) δ, Integrable (fun ω => Real.exp (u*W 1 ω)) P := by
    obtain ⟨δ,hδ,hδ'⟩ := hmg
    refine ⟨δ/a,div_pos hδ ha,fun u hu => ?_⟩
    have hIn : u*a ∈ Ioo (-δ) δ := ⟨by
        have h := (div_lt_iff₀ ha).1 (show -δ/a < u by simpa [neg_div] using hu.1)
        linarith,
      (lt_div_iff₀ ha).1 hu.2⟩
    have hh := hδ' (u*a) hIn
    convert hh using 1
    funext ω
    congr 1
    field_simp
  obtain ⟨K,C,hK,hC,hb⟩ := renewal_increment_concentration P (fun j => W (j+1))
    hW hPos hi hid hint hmean hmom A η hA hη
  refine ⟨K,C,hK,hC,fun r rate t hlog hr hrate hrateA ht => ?_⟩
  have he (ω : Ω) (s : ℝ) :
      renewalCount (partialSum (fun i => W i ω/rate)) s =
        renewalCount (fun m => ∑ j ∈ Finset.range m,W (j+1) ω) (rate*s) := by
    unfold renewalCount
    have hh (m : ℕ) : partialSum (fun i => W i ω/rate) m ≤ s ↔
        (∑ j ∈ Finset.range m,W (j+1) ω) ≤ rate*s := by
      rw [partialSum_shift, ← Finset.sum_div, div_le_iff₀ hrate, mul_comm s]
    simp only [hh]
  simpa only [he] using hb r rate t hlog hr hrate hrateA ht

set_option maxHeartbeats 1500000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω) :
    ∃ η α K C : ℝ, 0 < η ∧ 0 < α ∧ 0 < K ∧ 0 ≤ C ∧
      ∀ᶠ n in atTop,
        α+2*η ≤ M.lamR n 0-M.muR n 0 ∧
        α+3*η ≤ M.muR n 0+M.muR n 1-M.lamR n 0 ∧
        ∀ t : ℝ, 0 ≤ t → ∃ E : Set Ω, MeasurableSet E ∧
          M.P E ≤ ENNReal.ofReal (C*(1+t)/M.r n^6) ∧
          ∀ ω ∉ E,
            (∀ u v, 0 ≤ u → u ≤ v → v ≤ M.r n^2*t →
              |M.A n 0 ω v-M.A n 0 ω u-M.lamR n 0*(v-u)| ≤ η*(v-u)+K*Real.log (M.r n)) ∧
            (∀ j : Fin 3, j ≠ 2 → ∀ u v, 0 ≤ u → u ≤ v → v ≤ M.r n^2*t →
              |M.S n j ω v-M.S n j ω u-M.muR n j*(v-u)| ≤ η*(v-u)+K*Real.log (M.r n)) := by
  let D := max (max (M.lam 0) (M.mu 0)) (M.mu 1) + 1
  have hL0 : M.lam 0 ≤ max (max (M.lam 0) (M.mu 0)) (M.mu 1) :=
    (le_max_left (M.lam 0) (M.mu 0)).trans (le_max_left _ (M.mu 1))
  have hL1 : M.mu 0 ≤ max (max (M.lam 0) (M.mu 0)) (M.mu 1) :=
    (le_max_right (M.lam 0) (M.mu 0)).trans (le_max_left _ (M.mu 1))
  have hL2 : M.mu 1 ≤ max (max (M.lam 0) (M.mu 0)) (M.mu 1) := le_max_right _ _
  have hD0 : M.lam 0 < D := by dsimp [D]; linarith
  have hD1 : M.mu 0 < D := by dsimp [D]; linarith
  have hD2 : M.mu 1 < D := by dsimp [D]; linarith
  have hD : 0 < D := (M.lam_pos 0).trans hD0
  let d₁ := M.lam 0-M.mu 0
  let d₂ := M.mu 0+M.mu 1-M.lam 0
  have hd₁ : 0 < d₁ := sub_pos.mpr M.a31_i
  have hd₂ : 0 < d₂ := by
    have h := div_pos (M.lam_pos 1) (M.mu_pos 2)
    rw [← M.a31_ii, sub_pos, div_lt_one (M.mu_pos 1)] at h
    dsimp [d₂]
    linarith
  let η := min d₁ d₂ / 10
  have hη : 0 < η := by dsimp [η]; positivity
  have hlim1 : Tendsto (fun n => M.lamR n 0-M.muR n 0) atTop (𝓝 d₁) :=
    (M.a31_iii 0).sub (M.a31_iv 0)
  have hlim2 : Tendsto (fun n => M.muR n 0+M.muR n 1-M.lamR n 0) atTop (𝓝 d₂) :=
    ((M.a31_iv 0).add (M.a31_iv 1)).sub (M.a31_iii 0)
  have hDrift1 : η+2*η < d₁ := by
    have h := min_le_left d₁ d₂
    dsimp [η]; linarith
  have hDrift2 : η+3*η < d₂ := by
    have h := min_le_right d₁ d₂
    dsimp [η]; linarith
  have hex := M.a33
  letI : IsProbabilityMeasure M.P := M.isProb
  have ha := one_envelope M.P (M.uC 0) (fun j => M.uC_meas 0 (j+1))
    (fun j ω => M.uC_pos 0 (j+1) ω (by omega))
    (M.indep.precomp (g := fun j => Sum.inl (0,j)) (by
      intro i j h; exact congrArg Prod.snd (Sum.inl.inj h)))
    (fun j => M.uC_ident 0 (j+1) (by omega)) ((M.uC_memLp 0).integrable (by norm_num))
    (M.uC_mean 0) (M.lam 0) (M.lam_pos 0)
    (by obtain ⟨δ,hδ,h⟩ := hex; exact ⟨δ,hδ,fun u hu => (h u hu).1 0 1 le_rfl⟩) D η hD hη
  have hs (i : Fin 3) := one_envelope M.P (M.vC i) (fun j => M.vC_meas i (j+1))
    (fun j ω => M.vC_pos i (j+1) ω (by omega))
    (M.indep.precomp (g := fun j => Sum.inr (i,j)) (by
      intro k j h; exact congrArg Prod.snd (Sum.inr.inj h)))
    (fun j => M.vC_ident i (j+1) (by omega)) ((M.vC_memLp i).integrable (by norm_num))
    (M.vC_mean i) (M.mu i) (M.mu_pos i)
    (by obtain ⟨δ,hδ,h⟩ := hex; exact ⟨δ,hδ,fun u hu => (h u hu).2 i 1 le_rfl⟩) D η hD hη
  obtain ⟨Ka,Ca,hKa,hCa,hAa⟩ := ha
  obtain ⟨K0,C0,hK0,hC0,hS0⟩ := hs 0
  obtain ⟨K1,C1,hK1,hC1,hS1⟩ := hs 1
  let K := Ka+K0+K1
  let C := Ca+C0+C1
  refine ⟨η,η,K,C,hη,hη,by dsimp [K]; positivity,by dsimp [C]; positivity,?_⟩
  filter_upwards [(Real.tendsto_log_atTop.comp M.r_tendsto).eventually_ge_atTop 1,
    (M.a31_iii 0).eventually_lt_const hD0, (M.a31_iv 0).eventually_lt_const hD1,
    (M.a31_iv 1).eventually_lt_const hD2, hlim1.eventually_const_lt hDrift1,
    hlim2.eventually_const_lt hDrift2] with n hn hRa hR0 hR1 hDra hDrb
  refine ⟨hDra.le,hDrb.le,fun t ht => ?_⟩
  let bad (k : ℝ) (F : Ω → ℝ → ℝ) (a : ℝ) : Set Ω := {ω | ∃ u v : ℝ,
    0 ≤ u ∧ u ≤ v ∧ v ≤ M.r n^2*t ∧ η*(v-u)+k*Real.log (M.r n) < |F ω v-F ω u-a*(v-u)|}
  let Ea := bad Ka (M.A n 0) (M.lamR n 0)
  let E0 := bad K0 (M.S n 0) (M.muR n 0)
  let E1 := bad K1 (M.S n 1) (M.muR n 1)
  have hua : M.P Ea ≤ ENNReal.ofReal (Ca*(1+t)/M.r n^6) :=
    hAa _ _ _ hn (M.r_ge n) (M.lamR_pos n 0) hRa.le ht
  have hu0 : M.P E0 ≤ ENNReal.ofReal (C0*(1+t)/M.r n^6) :=
    hS0 _ _ _ hn (M.r_ge n) (M.muR_pos n 0) hR0.le ht
  have hu1 : M.P E1 ≤ ENNReal.ofReal (C1*(1+t)/M.r n^6) :=
    hS1 _ _ _ hn (M.r_ge n) (M.muR_pos n 1) hR1.le ht
  obtain ⟨E,hsub,hEm,hEmu⟩ := exists_measurable_superset M.P ((Ea ∪ E0) ∪ E1)
  refine ⟨E,hEm,?_,?_⟩
  · rw [hEmu]
    refine ((measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)).trans ?_
    refine (add_le_add (add_le_add hua hu0) hu1).trans_eq ?_
    have hr : 0 < M.r n := zero_lt_one.trans_le (M.r_ge n)
    rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    dsimp [C]
    ring
  · intro ω hω
    have hm (k : ℝ) (F : Ω → ℝ → ℝ) (a : ℝ) (hk : k ≤ K) (hF : bad k F a ⊆ E)
        (u v : ℝ) (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ M.r n^2*t) :
        |F ω v-F ω u-a*(v-u)| ≤ η*(v-u)+K*Real.log (M.r n) := by
      have hh : |F ω v-F ω u-a*(v-u)| ≤ η*(v-u)+k*Real.log (M.r n) :=
        le_of_not_gt (fun h => hω (hF ⟨u,v,hu,huv,hv,h⟩))
      exact hh.trans (add_le_add_right (mul_le_mul_of_nonneg_right hk (Real.log_nonneg (M.r_ge n))) _)
    refine ⟨hm Ka _ _ (by dsimp [K]; linarith) (fun ω h => hsub (Or.inl (Or.inl h))), ?_⟩
    intro j hj
    fin_cases j
    · exact hm K0 _ _ (by dsimp [K]; linarith) (fun ω h => hsub (Or.inl (Or.inr h)))
    · exact hm K1 _ _ (by dsimp [K]; linarith) (fun ω h => hsub (Or.inr h))
    · exact (hj rfl).elim
