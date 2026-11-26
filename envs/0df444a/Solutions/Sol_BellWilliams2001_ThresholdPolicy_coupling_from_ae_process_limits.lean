-- Prove2me | solution 1 for BellWilliams2001.ThresholdPolicy.coupling_from_ae_process_limits
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T07:04:36.850784+00:00
-- url     : https://prove2.me/submissions/7f75066d-5a10-4596-b1b2-0dea3f499198

import Theorems.Thm_BellWilliams2001_ThresholdPolicy_measurable_path_version
import Theorems.Thm_ManyServerQED_Scheduling_functional_coupling_from_fdd_and_interval_modulus

open MeasureTheory ProbabilityTheory Filter Topology Set
open BellWilliams2001.ThresholdPolicy
open scoped ENNReal NNReal

set_option maxHeartbeats 1600000 in
theorem solution {Ω : Type*} {Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {k : ℕ} (X : ℕ → Ω → ℝ → Fin k → ℝ) (Z : Ω' → ℝ → Fin k → ℝ)
    (hX : ∀ n ω i, IsCadlag (fun t => X n ω t i))
    (hZ : ∀ᵐ ω ∂P', ContinuousOn (Z ω) (Ici (0:ℝ)))
    (hF : ∀ (q : ℕ) (τ : Fin q → ℝ), (∀ j, 0 ≤ τ j) →
      TendstoInDistribution (fun n ω j => X n ω (τ j)) atTop
        (fun ω j => Z ω (τ j)) (fun _ => P) P')
    (hM : ∀ (T : ℕ) (ε η : ℝ), 0 < ε → 0 < η → ∃ δ > 0, ∀ᶠ n in atTop,
      P {ω | ∃ s ∈ Icc (0:ℝ) (T:ℝ), ∃ t ∈ Icc (0:ℝ) (T:ℝ), |s-t| ≤ δ ∧
        ε ≤ ‖X n ω s-X n ω t‖} ≤ ENNReal.ofReal η) :
    CouplingConverges P P' X Z := by
  let G (f : ℝ → Fin k → ℝ) := ∀ i, IsCadlag (fun t => f t i)
  have h0 : G (fun _ => 0) := fun _ => ⟨fun _ _ => continuousWithinAt_const,
    fun _ _ => ⟨0,tendsto_const_nhds⟩⟩
  have hRight (f : ℝ → Fin k → ℝ) (hf : G f) (t : ℝ) (ht : 0 ≤ t) :
      ContinuousWithinAt f (Ici t) t :=
    tendsto_pi_nhds.2 (fun i => (hf i).1 t ht)
  have hXm (n : ℕ) (t : ℝ) (ht : 0 ≤ t) : AEMeasurable (fun ω => X n ω t) P :=
    (measurable_pi_apply (0:Fin 1)).comp_aemeasurable
      ((hF 1 (fun _ => t) (fun _ => ht)).forall_aemeasurable n)
  have hZm (t : ℝ) (ht : 0 ≤ t) : AEMeasurable (fun ω => Z ω t) P' :=
    (measurable_pi_apply (0:Fin 1)).comp_aemeasurable
      ((hF 1 (fun _ => t) (fun _ => ht)).aemeasurable_limit)
  choose X' hX' hEq hXm' using fun n => measurable_path_version P (X n) G h0
    (ae_of_all _ (hX n)) hRight (hXm n)
  obtain ⟨Z',hZ',hZeq,hZm'⟩ := measurable_path_version P' Z
    (fun f => ContinuousOn f (Ici 0)) continuousOn_const hZ
    (fun _ h t ht => (h t ht).mono (fun _ hs => ht.trans hs)) hZm
  have hF' (q : ℕ) (τ : Fin q → ℝ) (hτ : ∀ j, 0 ≤ τ j) :
      TendstoInDistribution (fun n ω j => X' n ω (τ j)) atTop
        (fun ω j => Z' ω (τ j)) (fun _ => P) P' :=
    (hF q τ hτ).congr (fun n => (hEq n).symm.mono fun ω hω => by rw [hω])
      (hZeq.symm.mono fun ω hω => by rw [hω])
  have hM' (T : ℕ) (ε η : ℝ) (he : 0 < ε) (hn : 0 < η) :
      ∃ δ > 0, ∀ᶠ n in atTop,
        P {ω | ∃ s ∈ Icc (0:ℝ) (T:ℝ), ∃ t ∈ Icc (0:ℝ) (T:ℝ), |s-t| ≤ δ ∧
          ε ≤ ‖X' n ω s-X' n ω t‖} ≤ ENNReal.ofReal η := by
    obtain ⟨δ,hδ,h⟩ := hM T ε η he hn
    refine ⟨δ,hδ,h.mono fun n hn => ?_⟩
    have hSame : {ω | ∃ s ∈ Icc (0:ℝ) (T:ℝ), ∃ t ∈ Icc (0:ℝ) (T:ℝ),
        |s-t| ≤ δ ∧ ε ≤ ‖X' n ω s-X' n ω t‖} =ᵐ[P]
        {ω | ∃ s ∈ Icc (0:ℝ) (T:ℝ), ∃ t ∈ Icc (0:ℝ) (T:ℝ),
        |s-t| ≤ δ ∧ ε ≤ ‖X n ω s-X n ω t‖} := by
      filter_upwards [hEq n] with ω hω
      change (∃ s ∈ Icc (0:ℝ) (T:ℝ), ∃ t ∈ Icc (0:ℝ) (T:ℝ),
        |s-t| ≤ δ ∧ ε ≤ ‖X' n ω s-X' n ω t‖) =
        (∃ s ∈ Icc (0:ℝ) (T:ℝ), ∃ t ∈ Icc (0:ℝ) (T:ℝ),
        |s-t| ≤ δ ∧ ε ≤ ‖X n ω s-X n ω t‖)
      rw [hω]
    rwa [measure_congr hSame]
  obtain ⟨Λ,mΛ,Q,U,V,hQ,hU,hV,hCad,hConv⟩ :=
    ManyServerQED.Scheduling.functional_coupling_from_fdd_and_interval_modulus X' Z'
      hX' hXm' hZ' hZm' hF' hM'
  refine ⟨Λ,mΛ,Q,U,V,hQ,?_,?_,hCad,hConv⟩
  · filter_upwards [hU] with n hn
    exact hn.trans (.of_ae_eq hn.aemeasurable_snd ((hEq n).mono fun ω hω => congrArg (fun f => fun t : ℝ≥0 => f t) hω))
  · exact hV.trans (.of_ae_eq hV.aemeasurable_snd (hZeq.mono fun ω hω => congrArg (fun f => fun t : ℝ≥0 => f t) hω))
