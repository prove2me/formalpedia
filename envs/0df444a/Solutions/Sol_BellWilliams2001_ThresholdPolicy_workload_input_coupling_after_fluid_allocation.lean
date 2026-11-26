-- Prove2me | solution 1 for BellWilliams2001.ThresholdPolicy.workload_input_coupling_after_fluid_allocation
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T07:08:14.314654+00:00
-- url     : https://prove2.me/submissions/ac100eaf-fbc6-4fd1-96a6-c6adaf2e3989

import Theorems.Thm_BellWilliams2001_ThresholdPolicy_model_primitive_limits
import Theorems.Thm_BellWilliams2001_ThresholdPolicy_retimed_weighted_process_limits
import Theorems.Thm_BellWilliams2001_ThresholdPolicy_pooled_brownian_input_finite_laws
import Theorems.Thm_BellWilliams2001_ThresholdPolicy_coupling_from_ae_process_limits
import Theorems.Thm_BellWilliams2001_ThresholdPolicy_admissible_workload_and_idle_regularity
import Theorems.Thm_ManyServerQED_Scheduling_finite_family_independent_continuous_brownian

open MeasureTheory ProbabilityTheory Filter Topology Set
open BellWilliams2001.ThresholdPolicy ManyServerQED.Scheduling
open scoped ENNReal NNReal

private theorem clock_range {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω)
    (n : ℕ) (T : Allocation Ω) (hA : M.IsAdmissible n T) (ω : Ω) (j : Fin 3)
    (s : ℝ) (hs : 0 ≤ s) : 0 ≤ M.Tbar n T ω s j ∧ M.Tbar n T ω s j ≤ s := by
  let R := M.r n^2
  have hR : 0 < R := pow_pos (zero_lt_one.trans_le (M.r_ge n)) _
  have h0 : (0:ℝ) ∈ Ici (0:ℝ) := mem_Ici.mpr le_rfl
  have hu : R*s ∈ Ici (0:ℝ) := mul_nonneg hR.le hs
  have hNon (i : Fin 3) : 0 ≤ T ω i (R*s) := by
    have h := hA.alloc_mono ω i h0 hu hu
    rwa [hA.alloc_zero] at h
  refine ⟨div_nonneg (hNon j) hR.le, ?_⟩
  change T ω j (R*s) / R ≤ s
  rw [div_le_iff₀ hR, mul_comm s]
  have h0 := hA.idle_mono ω 0 h0 hu hu
  have h1 := hA.idle_mono ω 1 (show (0:ℝ) ∈ Ici 0 from mem_Ici.mpr le_rfl) hu hu
  rw [hA.idle_zero] at h0 h1
  simp only [SystemSequence.idle,if_true, show (1:Fin 2) ≠ 0 by decide,if_false] at h0 h1
  fin_cases j <;> simp at *
  · linarith
  · linarith [hNon 2]
  · linarith [hNon 1]

set_option maxHeartbeats 4300000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω)
    (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop)
    (T : ℕ → Allocation Ω) (hT : ∀ᶠ n in atTop, M.IsAdmissible (φ n) (T n))
    (hfluid : UocInProb M.P (fun n ω t => M.Tbar (φ n) (T n) ω t) M.fluidAllocation)
    (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (B : Fin 2 → ℝ≥0 → Ω' → ℝ)
    (hB : IsBrownianPair P' B) :
    CouplingConverges M.P P' (fun n ω t => ![M.workloadInput (φ n) (T n) ω t])
      (fun ω t => ![∑ i, M.yvec i * M.Xtilde B ω t i]) ∧
    (∀ (H : ℕ) (ε η : ℝ), 0 < ε → 0 < η → ∃ δ > 0, ∀ᶠ n in atTop,
      M.P {ω | ∃ s ∈ Icc (0:ℝ) (H:ℝ), ∃ t ∈ Icc (0:ℝ) (H:ℝ), |s-t| ≤ δ ∧
        ε ≤ |M.workloadInput (φ n) (T n) ω s-M.workloadInput (φ n) (T n) ω t|} ≤ ENNReal.ofReal η) := by
  classical
  letI : IsProbabilityMeasure M.P := M.isProb
  letI : IsProbabilityMeasure P' := hB.isProb
  obtain ⟨Λ,mΛ,Q,C,hQ,hC,hCc,hCm,hCI⟩ := finite_family_independent_continuous_brownian 5
  letI : IsProbabilityMeasure Q := hQ
  let X (n : ℕ) (ω : Ω) (t : ℝ) := Fin.append (M.Ahat (φ n) ω t) (M.Shat (φ n) ω t)
  let Z (ω : Λ) (t : ℝ) (i : Fin 5) :=
    (Fin.append (fun k => Real.sqrt (M.lam k*M.alphaSq k))
      (fun j => Real.sqrt (M.mu j*M.betaSq j))) i * C i t.toNNReal ω
  obtain ⟨hXF,hXM⟩ := model_primitive_limits M φ hφ C hC hCc hCI
  let y (n : ℕ) := M.poolingWeight (φ n)
  let ylim := M.yvec 1
  let α : Fin 5 → ℝ := ![1,ylim,-1,-1,-ylim]
  let a (n : ℕ) : Fin 5 → ℝ := ![1,y n,-1,-1,-y n]
  let b (n : ℕ) := M.driftR (φ n) 0+y n*M.driftR (φ n) 1
  let β := M.theta 0+ylim*M.theta 1
  let ρ : Fin 5 → ℝ := ![1,1,1,(M.lam 0-M.mu 0)/M.mu 1,M.lam 1/M.mu 2]
  let G (n : ℕ) (ω : Ω) (t : ℝ) := Fin.append (fun _ : Fin 2 => t) (M.Tbar (φ n) (T n) ω t)
  let g (t : ℝ) (i : Fin 5) := ρ i*t
  let Y (n : ℕ) (ω : Ω) (t : ℝ) : Fin 1 → ℝ :=
    if M.IsAdmissible (φ n) (T n) then ![M.workloadInput (φ n) (T n) ω t] else 0
  let W (ω : Ω') (t : ℝ) := ![∑ i,M.yvec i*M.Xtilde B ω t i]
  have hy : Tendsto y atTop (𝓝 ylim) := by
    simpa only [y,ylim,SystemSequence.yvec,SystemSequence.poolingWeight,show (1:Fin 2) ≠ 0 by decide,
      if_false,Function.comp_def,Pi.div_def] using
      ((M.a31_iv 1).div (M.a31_iv 2) (M.mu_pos 2).ne').comp hφ
  have ha : Tendsto a atTop (𝓝 α) := by
    apply tendsto_pi_nhds.2
    intro i
    fin_cases i
    · exact tendsto_const_nhds
    · exact hy
    · exact tendsto_const_nhds
    · exact tendsto_const_nhds
    · exact hy.neg
  have hD₀ : Tendsto (fun n => M.driftR (φ n) 0) atTop (𝓝 (M.theta 0)) :=
    M.a31_v.comp hφ
  have hD₁ : Tendsto (fun n => M.driftR (φ n) 1) atTop (𝓝 (M.theta 1)) := by
    simpa only [SystemSequence.driftR,show (1:Fin 2) ≠ 0 by decide,if_false,Function.comp_def]
      using M.a31_vi.comp hφ
  have hb : Tendsto b atTop (𝓝 β) := by
    simpa only [b, β,Pi.add_def,Pi.mul_def] using hD₀.add (hy.mul hD₁)
  have hρ (i : Fin 5) : 0 ≤ ρ i ∧ ρ i ≤ 1 := by
    have h0 := div_pos (sub_pos.2 M.a31_i) (M.mu_pos 1)
    have h1 := div_pos (M.lam_pos 1) (M.mu_pos 2)
    have h01 : (M.lam 0-M.mu 0)/M.mu 1 ≤ 1 := by linarith [M.a31_ii]
    have h11 : M.lam 1/M.mu 2 ≤ 1 := by linarith [M.a31_ii]
    fin_cases i <;> simp [ρ,h0.le,h1.le,h01,h11]
  have hg (t : ℝ) (ht : 0 ≤ t) (i : Fin 5) : g t i ∈ Icc 0 t :=
    ⟨mul_nonneg (hρ i).1 ht, by simpa using mul_le_mul_of_nonneg_right (hρ i).2 ht⟩
  have hgLip (s t : ℝ) (_ : 0 ≤ s) (_ : 0 ≤ t) (i : Fin 5) :
      |g s i-g t i| ≤ |s-t| := by
    rw [show g s i-g t i = ρ i*(s-t) by dsimp [g]; ring,abs_mul,abs_of_nonneg (hρ i).1]
    simpa using mul_le_mul_of_nonneg_right (hρ i).2 (abs_nonneg (s-t))
  have hg' (t : ℝ) : g t = Fin.append (fun _ : Fin 2 => t) (M.fluidAllocation t) := by
    funext i
    fin_cases i <;> first | rfl | exact one_mul t
  have hG : UocInProb M.P G g := by
    intro t ht ε hε
    have he (n : ℕ) (ω : Ω) : supDist (G n ω) g t =
        supDist (M.Tbar (φ n) (T n) ω) M.fluidAllocation t := by
      unfold supDist
      simp only [G,hg',Fin.sum_univ_add,Fin.append_left,Fin.append_right,sub_self,abs_zero,
        Finset.sum_const_zero,zero_add]
    simpa only [he] using hfluid t ht ε hε
  have hGt : ∀ᶠ n in atTop, ∀ ω t, 0 ≤ t → ∀ i, G n ω t i ∈ Icc 0 t := by
    filter_upwards [hT] with n hn ω t ht i
    obtain ⟨i,rfl⟩ := (finSumFinEquiv (m := 2) (n := 3)).surjective i
    rcases i with i | i
    · simpa only [G,finSumFinEquiv_apply_left,Fin.append_left] using (show t ∈ Icc 0 t from ⟨ht,le_rfl⟩)
    · simpa only [G,finSumFinEquiv_apply_right,Fin.append_right,mem_Icc] using
        clock_range M (φ n) (T n) hn ω i t ht
  have hYeq : ∀ᶠ n in atTop, ∀ ω t, 0 ≤ t →
      Y n ω t = ![(∑ i, a n i * X n ω (G n ω t i) i) + b n*t] := by
    filter_upwards [hT] with n hn ω t ht
    rw [show Y n ω t = ![M.workloadInput (φ n) (T n) ω t] by simp [Y,hn]]
    rw [Fin.sum_univ_add (a := 2) (b := 3),Fin.sum_univ_two,Fin.sum_univ_three]
    simp only [X,G,Fin.append_left,Fin.append_right]
    congr 1
    change M.workloadInput (φ n) (T n) ω t =
      (1*M.Ahat (φ n) ω t 0+y n*M.Ahat (φ n) ω t 1)+(
      (-1)*M.Shat (φ n) ω (M.Tbar (φ n) (T n) ω t 0) 0+
      (-1)*M.Shat (φ n) ω (M.Tbar (φ n) (T n) ω t 1) 1+
      (-y n)*M.Shat (φ n) ω (M.Tbar (φ n) (T n) ω t 2) 2)+b n*t
    simp only [SystemSequence.workloadInput,SystemSequence.Xhat,if_true,
      show (1:Fin 2) ≠ 0 by decide,if_false,←show y n = M.poolingWeight (φ n) from rfl,b]
    ring
  have hYm (n : ℕ) (t : ℝ) (ht : 0 ≤ t) : AEMeasurable (fun ω => Y n ω t) M.P := by
    by_cases hn : M.IsAdmissible (φ n) (T n)
    · have hm := (admissible_workload_and_idle_regularity M (φ n) (T n) hn).2.2.2 t ht
      refine aemeasurable_pi_lambda _ fun i => ?_
      have hi : i = 0 := Fin.eq_zero i
      subst i
      simpa only [Y,if_pos hn,Matrix.cons_val_zero] using hm
    · simpa only [Y,if_neg hn] using aemeasurable_const
  have hYc (n : ℕ) (ω : Ω) (i : Fin 1) : IsCadlag (fun t => Y n ω t i) := by
    have hi : i = 0 := Fin.eq_zero i
    subst i
    by_cases hn : M.IsAdmissible (φ n) (T n)
    · simpa only [Y,if_pos hn,Matrix.cons_val_zero] using
        (admissible_workload_and_idle_regularity M (φ n) (T n) hn).2.2.1 ω
    · simpa only [Y,if_neg hn,Pi.zero_apply] using
        (show IsCadlag (fun _ => (0:ℝ)) from
          ⟨fun _ _ => continuousWithinAt_const, fun _ _ => ⟨0,tendsto_const_nhds⟩⟩)
  obtain ⟨hYF,hYM⟩ := retimed_weighted_process_limits M.P Q X Z hXF hXM a b α β ha hb
    G g hG hg hgLip hGt Y hYm hYeq
  have hWc : ∀ᵐ ω ∂P', ContinuousOn (W ω) (Ici 0) := by
    filter_upwards [ae_all_iff.2 (fun i => (hB.brownian i).cont)] with ω hω
    apply Continuous.continuousOn
    apply continuous_pi
    intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    simp only [W,Matrix.cons_val_zero]
    apply continuous_finsetSum
    intro j _
    exact continuous_const.mul ((continuous_const.mul continuous_id).add
      (continuous_const.mul ((hω j).comp continuous_real_toNNReal)))
  have hWF (q : ℕ) (τ : Fin q → ℝ) (hτ : ∀ j, 0 ≤ τ j) :
      TendstoInDistribution (fun n ω j => Y n ω (τ j)) atTop
        (fun ω j => W ω (τ j)) (fun _ => M.P) P' := by
    have hL := pooled_brownian_input_finite_laws M Q C hC hCm hCI P' B hB q τ hτ
    let L (ω : Λ) (j : Fin q) := ![(∑ i, α i*Z ω (g (τ j) i) i)+β*τ j]
    have hF' : TendstoInDistribution (fun n ω j => Y n ω (τ j)) atTop L (fun _ => M.P) Q := hYF q τ hτ
    have hId : IdentDistrib L (fun ω j => W ω (τ j)) Q P' := by
      simpa only [L,Z,α,g,ρ,β,ylim,mul_assoc,W] using hL
    refine ⟨hF'.forall_aemeasurable,hId.aemeasurable_snd,?_⟩
    have he : (⟨Q.map L,Measure.isProbabilityMeasure_map hF'.aemeasurable_limit⟩ :
        ProbabilityMeasure (Fin q → Fin 1 → ℝ)) =
      ⟨P'.map (fun ω j => W ω (τ j)),Measure.isProbabilityMeasure_map hId.aemeasurable_snd⟩ :=
      Subtype.ext hId.map_eq
    exact he ▸ hF'.tendsto
  obtain ⟨Ωc,mΩc,Pc,U,V,hPc,hLaw,hLim,hCad,hConv⟩ :=
    coupling_from_ae_process_limits M.P P' Y W hYc hWc hWF hYM
  constructor
  · refine ⟨Ωc,mΩc,Pc,U,V,hPc,?_,hLim,hCad,hConv⟩
    filter_upwards [hT,hLaw] with n hn hL
    simpa only [Y,if_pos hn] using hL
  · intro H ε η hε hη
    obtain ⟨δ,hδ,h⟩ := hYM H ε η hε hη
    refine ⟨δ,hδ,?_⟩
    filter_upwards [hT,h] with n hn hh
    refine (measure_mono ?_).trans hh
    rintro ω ⟨s,hs,t,ht,hst,hb⟩
    refine ⟨s,hs,t,ht,hst,?_⟩
    have hnorm := norm_le_pi_norm (Y n ω s-Y n ω t) (0:Fin 1)
    exact hb.trans (by simpa only [Y,if_pos hn,Pi.sub_apply,Matrix.cons_val_zero,Real.norm_eq_abs] using hnorm)
