-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_original_budget_integrable_L1_joint_ito_transfer_signed
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T21:32:10.07804+00:00
-- url     : https://prove2.me/submissions/bcc86d72-4417-4116-914f-874466cd0693

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_transfer_stopped_pathwise_L1_positive_source
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A : Set Ω) (hA : MeasurableSet A)
    (F N Occ : Ω → ℝ) (M B : ℕ → Ω → ℝ) (x Γ c : ℝ)
    (hFI : Integrable F P) (hMI : ∀ m, Integrable (M m) P)
    (hOI : Integrable Occ (P.restrict A))
    (hNI : Integrable N P)
    (hBI : ∀ m, Integrable (B m) P)
    (hPath : ∀ᵐ ω ∂(P.restrict A),
      F ω - x ≤ N ω + Γ + c * Occ ω)
    (hNlim : Tendsto (fun m => ∫ ω in A, |N ω - M m ω| ∂P)
      atTop (𝓝 (0 : ℝ)))
    (hBlim : Tendsto (fun m => ∫ ω, |B m ω| ∂P)
      atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun m => ∫ ω in A,
      max ((F ω - x) - M m ω - (Γ + c * Occ ω) - B m ω)
        (0 : ℝ) ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  let G : Ω → ℝ := fun ω => F ω - x - Γ - c * Occ ω
  have hG : ∀ᵐ ω ∂(P.restrict A), G ω ≤ N ω := by
    filter_upwards [hPath] with ω hω
    dsimp only [G]
    linarith
  have hUpI (m : ℕ) :
      Integrable (fun ω => |N ω - M m ω| + |B m ω|)
        (P.restrict A) := by
    have hP := ((hNI.sub (hMI m)).abs.add (hBI m).abs)
    change Integrable (fun ω : Ω => |N ω - M m ω| + |B m ω|) P at hP
    exact hP.mono_measure Measure.restrict_le_self
  have hI (m : ℕ) :
      Integrable (fun ω => max (G ω - M m ω - B m ω) 0)
        (P.restrict A) := by
    have hf : AEStronglyMeasurable F (P.restrict A) :=
      (hFI.mono_measure Measure.restrict_le_self).aestronglyMeasurable
    have hm : AEStronglyMeasurable (M m) (P.restrict A) :=
      ((hMI m).mono_measure Measure.restrict_le_self).aestronglyMeasurable
    have hb : AEStronglyMeasurable (B m) (P.restrict A) :=
      ((hBI m).mono_measure Measure.restrict_le_self).aestronglyMeasurable
    have ho := hOI.aestronglyMeasurable
    have hc : AEStronglyMeasurable G (P.restrict A) := by
      have ht : AEStronglyMeasurable
          (((F - fun _ => x) - fun _ => Γ) - fun ω => c * Occ ω)
          (P.restrict A) :=
        ((hf.sub aestronglyMeasurable_const).sub
          aestronglyMeasurable_const).sub (ho.const_mul c)
      change AEStronglyMeasurable G (P.restrict A) at ht
      exact ht
    have hmeas : AEStronglyMeasurable
        (fun ω => max (G ω - M m ω - B m ω) (0 : ℝ)) (P.restrict A) := by
      have ht : AEStronglyMeasurable
          ((G - M m - B m) ⊔ fun _ => (0 : ℝ)) (P.restrict A) :=
        ((hc.sub hm).sub hb).sup
          (aestronglyMeasurable_const :
            AEStronglyMeasurable (fun _ : Ω => (0 : ℝ)) (P.restrict A))
      change AEStronglyMeasurable
        (fun ω => max (G ω - M m ω - B m ω) (0 : ℝ)) (P.restrict A) at ht
      exact ht
    refine (hUpI m).mono' hmeas ?_
    filter_upwards [hG] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    have hh : G ω - M m ω - B m ω ≤
        |N ω - M m ω| + |B m ω| := by
      linarith [le_abs_self (N ω - M m ω), neg_le_abs (B m ω)]
    exact max_le hh (add_nonneg (abs_nonneg _) (abs_nonneg _))
  have hBrestrict :
      Tendsto (fun m => ∫ ω in A, |B m ω| ∂P)
        atTop (𝓝 (0 : ℝ)) := by
    have hlo (m : ℕ) : 0 ≤ ∫ ω in A, |B m ω| ∂P :=
      integral_nonneg_of_ae (Filter.Eventually.of_forall (fun ω => abs_nonneg _))
    have hhi (m : ℕ) : (∫ ω in A, |B m ω| ∂P) ≤
        (∫ ω, |B m ω| ∂P) :=
      setIntegral_le_integral (hBI m).abs
        (Filter.Eventually.of_forall (fun ω => abs_nonneg _))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hBlim
      (Filter.Eventually.of_forall hlo)
      (Filter.Eventually.of_forall hhi)
  have hSumLimit : Tendsto
      (fun m => ∫ ω in A, |N ω - M m ω| + |B m ω| ∂P)
      atTop (𝓝 (0 : ℝ)) := by
    convert hNlim.add hBrestrict using 1
    · funext m
      simpa only [Pi.add_apply, Pi.sub_apply] using
        (integral_add ((hNI.sub (hMI m)).abs.integrableOn)
          ((hBI m).abs.integrableOn))
    · ring
  have hResult :=
    avram_ga_transfer_stopped_pathwise_L1_positive_source
      P A G N M B hG hI hUpI hSumLimit
  convert hResult using 1
  funext m
  apply integral_congr_ae
  filter_upwards [] with ω
  simp only [G]
  ring
