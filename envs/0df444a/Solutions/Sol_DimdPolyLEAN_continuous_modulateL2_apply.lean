-- Prove2me | solution 1 for DimdPolyLEAN.continuous_modulateL2_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:28:06.819915+00:00
-- url     : https://prove2.me/submissions/1534e8c3-8004-4efd-9927-053a4d320db4

module
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Basic
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Definitions
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_RotationalAveraging
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ImportedAnalyticInputs
section
@[expose] public section
noncomputable section
namespace DimdPolyLEAN
open MeasureTheory Filter
open scoped ENNReal Topology RealInnerProductSpace
private theorem tendsto_lintegral_filter_of_dominated_convergence_ae
    {α ι : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α} {l : Filter ι}
    [l.IsCountablyGenerated] {F : ι -> α -> ℝ≥0∞} {f : α -> ℝ≥0∞}
    (bound : α -> ℝ≥0∞)
    (hF_meas : ∀ᶠ n in l, AEMeasurable (F n) μ)
    (h_bound : ∀ᶠ n in l, ∀ᵐ a ∂μ, F n a ≤ bound a)
    (h_fin : ∫⁻ a, bound a ∂μ ≠ ∞)
    (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) l (𝓝 (f a))) :
    Tendsto (fun n => ∫⁻ a, F n a ∂μ) l (𝓝 <| ∫⁻ a, f a ∂μ) := by
  rw [tendsto_iff_seq_tendsto]
  intro x xl
  have h := inter_mem hF_meas h_bound
  replace h := (tendsto_atTop'.mp xl) _ h
  rcases h with ⟨k, h⟩
  rw [← tendsto_add_atTop_iff_nat k]
  refine tendsto_lintegral_of_dominated_convergence' bound ?_ ?_ h_fin ?_
  · intro n
    exact (h (n + k) (Nat.le_add_left _ _)).1
  · intro n
    exact (h (n + k) (Nat.le_add_left _ _)).2
  · refine h_lim.mono fun a h_lim => ?_
    apply @Tendsto.comp _ _ _ (fun n => x (n + k)) fun n => F n a
    · assumption
    rwa [tendsto_add_atTop_iff_nat]
private theorem modulation_eLpNorm_tendsto_zero {d : Nat} (f : L2Real d) (ω0 : RealVec d) :
    Tendsto
      (fun ω : RealVec d => MeasureTheory.eLpNorm
        (fun t : RealVec d =>
          modulationPhase ω t * (f : RealVec d -> ℂ) t -
            modulationPhase ω0 t * (f : RealVec d -> ℂ) t)
        2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
      (𝓝 ω0) (𝓝 (0 : ℝ≥0∞)) := by
  have hf := MeasureTheory.Lp.memLp f
  have hInt :
      Tendsto
        (fun ω : RealVec d => ∫⁻ t : RealVec d,
          ‖modulationPhase ω t * (f : RealVec d -> ℂ) t -
            modulationPhase ω0 t * (f : RealVec d -> ℂ) t‖ₑ ^ (2 : ℝ)
            ∂(MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
        (𝓝 ω0) (𝓝 (0 : ℝ≥0∞)) := by
    have hdc := tendsto_lintegral_filter_of_dominated_convergence_ae
      (μ := (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
      (l := 𝓝 ω0)
      (F := fun ω t =>
        ‖modulationPhase ω t * (f : RealVec d -> ℂ) t -
          modulationPhase ω0 t * (f : RealVec d -> ℂ) t‖ₑ ^ (2 : ℝ))
      (f := fun _ : RealVec d => (0 : ℝ≥0∞))
      (bound := fun t : RealVec d => ‖(2 : ℂ) * (f : RealVec d -> ℂ) t‖ₑ ^ (2 : ℝ))
      ?_ ?_ ?_ ?_
    · simpa only [ENNReal.rpow_ofNat, lintegral_const, zero_mul] using hdc
    · exact Filter.Eventually.of_forall fun ω => by
        exact (((Continuous.aestronglyMeasurable (by
          unfold modulationPhase
          fun_prop)).mul hf.aestronglyMeasurable).sub
            ((Continuous.aestronglyMeasurable (by
              unfold modulationPhase
              fun_prop)).mul hf.aestronglyMeasurable)).enorm.pow_const (2 : ℝ)
    · exact Filter.Eventually.of_forall fun ω => Filter.Eventually.of_forall fun t => by
        have hnorm :
            ‖modulationPhase ω t * (f : RealVec d -> ℂ) t -
                modulationPhase ω0 t * (f : RealVec d -> ℂ) t‖ ≤
              ‖(2 : ℂ) * (f : RealVec d -> ℂ) t‖ := by
          calc
            ‖modulationPhase ω t * (f : RealVec d -> ℂ) t -
                modulationPhase ω0 t * (f : RealVec d -> ℂ) t‖
                ≤ ‖modulationPhase ω t * (f : RealVec d -> ℂ) t‖ +
                    ‖modulationPhase ω0 t * (f : RealVec d -> ℂ) t‖ := norm_sub_le _ _
            _ = ‖(f : RealVec d -> ℂ) t‖ + ‖(f : RealVec d -> ℂ) t‖ := by
              rw [norm_mul, norm_mul, modulationPhase_norm, modulationPhase_norm]
              ac_rfl
            _ = ‖(2 : ℂ) * (f : RealVec d -> ℂ) t‖ := by
              rw [norm_mul]
              norm_num
              ring_nf
        have henorm :
            ‖modulationPhase ω t * (f : RealVec d -> ℂ) t -
                modulationPhase ω0 t * (f : RealVec d -> ℂ) t‖ₑ ≤
              ‖(2 : ℂ) * (f : RealVec d -> ℂ) t‖ₑ := by
          rw [← ofReal_norm, ← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal hnorm
        exact ENNReal.rpow_le_rpow henorm (by norm_num)
    · have hmul_mem : MeasureTheory.MemLp
          (fun t : RealVec d => (2 : ℂ) * (f : RealVec d -> ℂ) t)
          2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) := hf.const_mul (2 : ℂ)
      exact (MeasureTheory.lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
        (p := (2 : ℝ≥0∞))
        (μ := (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
        (f := fun t : RealVec d => (2 : ℂ) * (f : RealVec d -> ℂ) t)
        (by norm_num) (by norm_num) hmul_mem.eLpNorm_lt_top).ne
    · exact Filter.Eventually.of_forall fun t => by
        have hphase : Tendsto (fun ω : RealVec d => modulationPhase ω t) (𝓝 ω0)
            (𝓝 (modulationPhase ω0 t)) := by
          have hcont : Continuous fun ω : RealVec d => modulationPhase ω t := by
            unfold modulationPhase
            fun_prop
          exact hcont.tendsto ω0
        have hdiff : Tendsto
            (fun ω : RealVec d =>
              modulationPhase ω t * (f : RealVec d -> ℂ) t -
                modulationPhase ω0 t * (f : RealVec d -> ℂ) t)
            (𝓝 ω0) (𝓝 0) := by
          have hleft : Tendsto
              (fun ω : RealVec d => modulationPhase ω t * (f : RealVec d -> ℂ) t)
              (𝓝 ω0) (𝓝 (modulationPhase ω0 t * (f : RealVec d -> ℂ) t)) :=
            hphase.mul tendsto_const_nhds
          have hright : Tendsto
              (fun _ : RealVec d => modulationPhase ω0 t * (f : RealVec d -> ℂ) t)
              (𝓝 ω0) (𝓝 (modulationPhase ω0 t * (f : RealVec d -> ℂ) t)) :=
            tendsto_const_nhds
          simpa only [sub_self] using hleft.sub hright
        have hnorm : Tendsto
            (fun ω : RealVec d =>
              ‖modulationPhase ω t * (f : RealVec d -> ℂ) t -
                modulationPhase ω0 t * (f : RealVec d -> ℂ) t‖ₑ)
            (𝓝 ω0) (𝓝 (0 : ℝ≥0∞)) := by
          simpa only [Function.comp_def, enorm_zero] using (continuous_enorm.tendsto 0).comp hdiff
        have hpow_cont : Continuous fun x : ℝ≥0∞ => x ^ (2 : ℝ) :=
          ENNReal.continuous_rpow_const
        simpa only [ENNReal.rpow_ofNat, Function.comp_def, ENNReal.zero_rpow_of_pos (by norm_num : 0
          < (2 : ℝ))] using
          (hpow_cont.tendsto (0 : ℝ≥0∞)).comp hnorm
  have hpow : Tendsto
      (fun ω : RealVec d =>
        (∫⁻ t : RealVec d,
          ‖modulationPhase ω t * (f : RealVec d -> ℂ) t -
            modulationPhase ω0 t * (f : RealVec d -> ℂ) t‖ₑ ^ (2 : ℝ)
            ∂(MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) ^ (1 / (2 : ℝ)))
      (𝓝 ω0) (𝓝 (0 : ℝ≥0∞)) := by
    have hpow_cont : Continuous fun x : ℝ≥0∞ => x ^ (1 / (2 : ℝ)) :=
      ENNReal.continuous_rpow_const
    simpa only [ENNReal.rpow_ofNat, one_div, Function.comp_def, inv_pos, Nat.ofNat_pos,
      ENNReal.zero_rpow_of_pos, ENNReal.zero_rpow_of_pos (by norm_num : 0 < (1 / (2 : ℝ)))] using
      (hpow_cont.tendsto (0 : ℝ≥0∞)).comp hInt
  have hmeas : ∀ ω : RealVec d, MeasureTheory.AEStronglyMeasurable
      (fun t : RealVec d =>
        modulationPhase ω t * (f : RealVec d -> ℂ) t -
          modulationPhase ω0 t * (f : RealVec d -> ℂ) t)
      (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) := fun ω =>
    (modulateL2_mem ω f).aestronglyMeasurable.sub (modulateL2_mem ω0 f).aestronglyMeasurable
  refine hpow.congr fun ω => ?_
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
  norm_num
end DimdPolyLEAN
end
end
end

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN
open MeasureTheory Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace DimdPolyLEAN
theorem _root_.solution {d : Nat} (f : L2Real d) :
    Continuous fun ω : RealVec d => modulateL2 ω f := by
  rw [continuous_iff_continuousAt]
  intro ω0
  dsimp [ContinuousAt]
  simpa only [modulateL2] using
    (MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (f := fun ω t => modulationPhase ω t * (f : RealVec d -> ℂ) t)
      (f_ℒp := fun ω => modulateL2_mem ω f)
      (f_lim := fun t => modulationPhase ω0 t * (f : RealVec d -> ℂ) t)
      (f_lim_ℒp := modulateL2_mem ω0 f)).2 (modulation_eLpNorm_tendsto_zero f ω0)
end DimdPolyLEAN
