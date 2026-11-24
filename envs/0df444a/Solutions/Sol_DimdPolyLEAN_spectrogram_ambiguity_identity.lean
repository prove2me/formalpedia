-- Prove2me | solution 1 for DimdPolyLEAN.spectrogram_ambiguity_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:31:48.898319+00:00
-- url     : https://prove2.me/submissions/b5d47604-70a2-4c34-a4a9-3285ee8164e6

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
public import Theorems.Thm_DimdPolyLEAN_symplecticFourierPhase_norm
public import Theorems.Thm_DimdPolyLEAN_symplecticFourierRep_eq_of_lpNorm_one_approx
public import Theorems.Thm_DimdPolyLEAN_norm_translateL2
public import Theorems.Thm_DimdPolyLEAN_dist_translateL2
public import Theorems.Thm_DimdPolyLEAN_fourier_schwartzCompSubConstCLM_realVec
public import Theorems.Thm_DimdPolyLEAN_ambiguityRep_eq_integral_of_ae_eq
public import Theorems.Thm_DimdPolyLEAN_modulateL2_coeFn
public import Theorems.Thm_DimdPolyLEAN_norm_modulateL2
public import Theorems.Thm_DimdPolyLEAN_ambiguityRep_eq_lpPairing
public import Theorems.Thm_DimdPolyLEAN_dist_modulateL2
public import Theorems.Thm_DimdPolyLEAN_dist_star_L2
public import Theorems.Thm_DimdPolyLEAN_norm_star_L2
public import Theorems.Thm_DimdPolyLEAN_stftRep_eq_lpPairing
public import Theorems.Thm_DimdPolyLEAN_continuous_stftRep
section
@[expose] public section
noncomputable section
namespace DimdPolyLEAN
open MeasureTheory Filter
open scoped ENNReal Topology RealInnerProductSpace
private theorem schwartzApproxRealVec_lpNorm_sub_le {d : Nat}
    {f : RealVec d -> ℂ}
    (hf : MeasureTheory.MemLp f 2
      (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
    (n : Nat) :
    MeasureTheory.lpNorm (f - (schwartzApproxRealVec hf n : RealVec d -> ℂ)) 2
      (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) ≤ 1 / ((n : ℝ) + 1) :=
  Classical.choose_spec <|
    exists_schwartz_lpNorm_sub_le_realVec (f := f) hf
      (ε := 1 / ((n : ℝ) + 1)) (by positivity)
private theorem schwartzApproxRealVec_lpNorm_le {d : Nat}
    {f : RealVec d -> ℂ}
    (hf : MeasureTheory.MemLp f 2
      (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
    (n : Nat) :
    MeasureTheory.lpNorm (schwartzApproxRealVec hf n : RealVec d -> ℂ) 2
        (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) ≤
      MeasureTheory.lpNorm f 2
        (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) + 1 / ((n : ℝ) + 1) := by
  let μ : MeasureTheory.Measure (RealVec d) := MeasureTheory.volume
  have hs : MeasureTheory.MemLp (schwartzApproxRealVec hf n : RealVec d -> ℂ) 2 μ :=
    (schwartzApproxRealVec hf n).memLp 2 μ
  calc
    MeasureTheory.lpNorm (schwartzApproxRealVec hf n : RealVec d -> ℂ) 2 μ
        = MeasureTheory.lpNorm (f - (f - (schwartzApproxRealVec hf n : RealVec d -> ℂ)))
            2 μ := by
            congr 1
            funext t
            simp
    _ ≤ MeasureTheory.lpNorm f 2 μ +
        MeasureTheory.lpNorm (f - (schwartzApproxRealVec hf n : RealVec d -> ℂ)) 2 μ := by
          exact MeasureTheory.lpNorm_sub_le
            (f := f) (g := f - (schwartzApproxRealVec hf n : RealVec d -> ℂ)) hf
            (by norm_num)
    _ ≤ MeasureTheory.lpNorm f 2 μ + 1 / ((n : ℝ) + 1) := by
          gcongr
          exact schwartzApproxRealVec_lpNorm_sub_le hf n
private theorem schwartzApproxRealVec_tendsto_lpNorm_sub_zero {d : Nat}
    {f : RealVec d -> ℂ}
    (hf : MeasureTheory.MemLp f 2
      (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) :
    Tendsto
      (fun n : Nat =>
        MeasureTheory.lpNorm (f - (schwartzApproxRealVec hf n : RealVec d -> ℂ)) 2
          (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
      atTop (nhds 0) := by
  have hε :
      Tendsto (fun n : Nat => 1 / ((n : ℝ) + 1)) atTop (nhds 0) := by
    simpa only [one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : Nat => 1 / ((n : ℝ) + 1)) atTop (nhds 0))
  exact squeeze_zero (fun _ => MeasureTheory.lpNorm_nonneg)
    (schwartzApproxRealVec_lpNorm_sub_le hf) hε
private theorem schwartzApproxRealVec_tendsto_lpNorm {d : Nat}
    {f : RealVec d -> ℂ}
    (hf : MeasureTheory.MemLp f 2
      (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) :
    Tendsto
      (fun n : Nat =>
        MeasureTheory.lpNorm (schwartzApproxRealVec hf n : RealVec d -> ℂ) 2
          (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
      atTop
      (nhds (MeasureTheory.lpNorm f 2
        (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))) := by
  let μ : MeasureTheory.Measure (RealVec d) := MeasureTheory.volume
  rw [tendsto_iff_dist_tendsto_zero]
  have hε :
      Tendsto (fun n : Nat => 1 / ((n : ℝ) + 1)) atTop (nhds 0) := by
    simpa only [one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : Nat => 1 / ((n : ℝ) + 1)) atTop (nhds 0))
  have hbound :
      ∀ n : Nat,
        |MeasureTheory.lpNorm (schwartzApproxRealVec hf n : RealVec d -> ℂ) 2 μ -
            MeasureTheory.lpNorm f 2 μ| ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    have hs : MeasureTheory.MemLp (schwartzApproxRealVec hf n : RealVec d -> ℂ) 2 μ :=
      (schwartzApproxRealVec hf n).memLp 2 μ
    have h₁ :=
      schwartzApproxRealVec_lpNorm_le hf n
    have h₂ :
        MeasureTheory.lpNorm f 2 μ ≤
          MeasureTheory.lpNorm (schwartzApproxRealVec hf n : RealVec d -> ℂ) 2 μ +
            1 / ((n : ℝ) + 1) := by
      calc
        MeasureTheory.lpNorm f 2 μ
            = MeasureTheory.lpNorm
                ((schwartzApproxRealVec hf n : RealVec d -> ℂ) -
                  ((schwartzApproxRealVec hf n : RealVec d -> ℂ) - f)) 2 μ := by
                  congr 1
                  funext t
                  simp
        _ ≤ MeasureTheory.lpNorm (schwartzApproxRealVec hf n : RealVec d -> ℂ) 2 μ +
            MeasureTheory.lpNorm ((schwartzApproxRealVec hf n : RealVec d -> ℂ) - f) 2 μ := by
            exact MeasureTheory.lpNorm_sub_le
              (f := (schwartzApproxRealVec hf n : RealVec d -> ℂ))
              (g := (schwartzApproxRealVec hf n : RealVec d -> ℂ) - f) hs (by norm_num)
        _ ≤ MeasureTheory.lpNorm (schwartzApproxRealVec hf n : RealVec d -> ℂ) 2 μ +
            1 / ((n : ℝ) + 1) := by
            gcongr
            simpa only [lpNorm_sub_comm, one_div, MeasureTheory.lpNorm_sub_comm] using
              schwartzApproxRealVec_lpNorm_sub_le hf n
    rw [abs_sub_le_iff]
    constructor <;> linarith
  simpa only [Real.dist_eq, μ] using squeeze_zero (fun _ => abs_nonneg _) hbound hε
private theorem schwartzApproxRealVec_toLp_tendsto {d : Nat} (f : L2Real d) :
    Tendsto
      (fun n : Nat =>
        (schwartzApproxRealVec (MeasureTheory.Lp.memLp f) n).toLp 2
          (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
      atTop (nhds f) := by
  let μ : MeasureTheory.Measure (RealVec d) := MeasureTheory.volume
  let hf : MeasureTheory.MemLp (f : RealVec d -> ℂ) 2 μ := MeasureTheory.Lp.memLp f
  rw [tendsto_iff_dist_tendsto_zero]
  have hdist :
      ∀ n : Nat,
        dist ((schwartzApproxRealVec hf n).toLp 2 μ) f =
          MeasureTheory.lpNorm
            ((schwartzApproxRealVec hf n : RealVec d -> ℂ) - (f : RealVec d -> ℂ)) 2 μ := by
    intro n
    let s : SchwartzMap (RealVec d) ℂ := schwartzApproxRealVec hf n
    have hs : MeasureTheory.MemLp (s : RealVec d -> ℂ) 2 μ := s.memLp 2 μ
    have hsub : MeasureTheory.MemLp ((s : RealVec d -> ℂ) - (f : RealVec d -> ℂ)) 2 μ :=
      hs.sub hf
    calc
      dist (s.toLp 2 μ) f
          = (edist (s.toLp 2 μ) f).toReal := by rw [MeasureTheory.Lp.dist_edist]
      _ = (edist ((s.memLp 2 μ).toLp (s : RealVec d -> ℂ)) f).toReal := by rfl
      _ = (edist ((s.memLp 2 μ).toLp (s : RealVec d -> ℂ)) (hf.toLp f)).toReal := by
            rw [MeasureTheory.Lp.toLp_coeFn]
      _ = (MeasureTheory.eLpNorm
            ((s : RealVec d -> ℂ) - (f : RealVec d -> ℂ)) 2 μ).toReal := by
            rw [MeasureTheory.Lp.edist_toLp_toLp]
      _ = MeasureTheory.lpNorm
            ((s : RealVec d -> ℂ) - (f : RealVec d -> ℂ)) 2 μ := by
            rw [MeasureTheory.toReal_eLpNorm hsub.aestronglyMeasurable]
  have hraw :
      Tendsto
        (fun n : Nat =>
          MeasureTheory.lpNorm
            ((schwartzApproxRealVec hf n : RealVec d -> ℂ) - (f : RealVec d -> ℂ)) 2 μ)
        atTop (nhds 0) := by
    simpa only [lpNorm_sub_comm, MeasureTheory.lpNorm_sub_comm, hf, μ] using
      schwartzApproxRealVec_tendsto_lpNorm_sub_zero hf
  simpa only [hdist, hf, μ] using hraw
private theorem modulationPhase_add {d : Nat} (ω a b : RealVec d) :
    modulationPhase ω (a + b) = modulationPhase ω a * modulationPhase ω b := by
  unfold modulationPhase
  rw [inner_add_right, Complex.ofReal_add, mul_add, Complex.exp_add]
private theorem modulationPhase_neg_right {d : Nat} (ω y : RealVec d) :
    modulationPhase ω (-y) = modulationPhase (-ω) y := by
  unfold modulationPhase
  rw [inner_neg_right, inner_neg_left]
private theorem star_modulationPhase {d : Nat} (ω t : RealVec d) :
    star (modulationPhase ω t) = modulationPhase (-ω) t := by
  unfold modulationPhase
  rw [Complex.star_def, ← Complex.exp_conj]
  have htwo : (starRingEnd ℂ) (2 : ℂ) = 2 := by simpa only [Complex.ofReal_ofNat] using
    (Complex.conj_ofReal (2 : ℝ))
  simp [inner_neg_left, htwo, mul_assoc, mul_comm, mul_left_comm]
private theorem modulationPhase_neg_inv {d : Nat} (ω a : RealVec d) :
    modulationPhase ω a * modulationPhase (-ω) a = 1 := by
  unfold modulationPhase
  rw [inner_neg_left, ← Complex.exp_add]
  have hzero :
      -(2 * Real.pi : ℂ) * Complex.I * ↑⟪ω, a⟫ +
          (-(2 * Real.pi : ℂ) * Complex.I * ↑(-⟪ω, a⟫)) = 0 := by
    rw [Complex.ofReal_neg]
    ring
  rw [hzero, Complex.exp_zero]
private theorem modulationPhase_neg_split {d : Nat} (ω y a : RealVec d) :
    modulationPhase (-ω) y = modulationPhase ω a * modulationPhase (-ω) (y + a) := by
  rw [modulationPhase_add]
  calc
    modulationPhase (-ω) y = 1 * modulationPhase (-ω) y := by ring
    _ = (modulationPhase ω a * modulationPhase (-ω) a) * modulationPhase (-ω) y := by
      rw [modulationPhase_neg_inv]
    _ = modulationPhase ω a * (modulationPhase (-ω) y * modulationPhase (-ω) a) := by ring
private theorem symplecticFourier_phase_eq_modulationPhase {d : Nat}
    (x ω y η : RealVec d) :
    Complex.exp
        ((2 * Real.pi : ℂ) * Complex.I *
          (((inner ℝ η x : ℝ) - (inner ℝ y ω : ℝ) : ℝ) : ℂ)) =
      modulationPhase ω y * modulationPhase (-x) η := by
  unfold modulationPhase
  rw [← Complex.exp_add,
    inner_neg_left,
    real_inner_comm y ω,
    real_inner_comm η x,
    Complex.ofReal_sub, Complex.ofReal_neg]
  congr 1
  ring
private theorem stftRep_schwartz_eq_fourier_apply {d : Nat}
    (h f : SchwartzMap (RealVec d) ℂ) (x ω : RealVec d) :
    stftRep (h.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
      (f.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) (x, ω) =
      FourierTransform.fourier (stftSliceSchwartz h f x : RealVec d -> ℂ) ω := by
  unfold stftRep
  rw [Real.fourier_eq]
  apply integral_congr_ae
  have hf_ae :
      (f.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) : RealVec d -> ℂ)
        =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (RealVec d))] f :=
    f.coeFn_toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))
  have hh_ae :
      (fun t : RealVec d =>
        (h.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) : RealVec d -> ℂ)
          (t - x)) =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (RealVec d))]
        fun t : RealVec d => h (t - x) := by
    simpa only [Function.comp_def] using
      (MeasureTheory.measurePreserving_sub_right
          (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))
          x).quasiMeasurePreserving.ae_eq_comp
        (h.coeFn_toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
  filter_upwards [hf_ae, hh_ae] with t hft hht
  rw [hft, hht]
  simp only [Real.fourierChar_apply, Circle.smul_def, stftSliceSchwartz_apply,
    Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_ofNat, smul_eq_mul,
    real_inner_comm, mul_neg, neg_mul, mul_assoc, mul_comm]
private theorem integral_fourier_sq_phase_schwartz_realVec {d : Nat}
    (f : SchwartzMap (RealVec d) ℂ) (x : RealVec d) :
    ∫ η, ((‖(FourierTransform.fourier (f : RealVec d -> ℂ)) η‖ ^ 2 : ℝ) : ℂ) *
        modulationPhase (-x) η =
      ∫ t, star (f t) * f (t + x) := by
  have h :=
    SchwartzMap.integral_inner_fourier_fourier f (schwartzCompSubConstCLM (-x) f)
  simp_rw [SchwartzMap.fourier_coe] at h
  rw [fourier_schwartzCompSubConstCLM_realVec f (-x)] at h
  calc
    _ = ∫ η, inner ℂ (FourierTransform.fourier (f : RealVec d → ℂ) η)
        (modulationPhase (-x) η * FourierTransform.fourier (f : RealVec d → ℂ) η) := by
      symm
      apply integral_congr_ae
      filter_upwards with η
      rw [RCLike.inner_apply']
      calc
        _ = ((starRingEnd ℂ) (FourierTransform.fourier (f : RealVec d → ℂ) η) *
            FourierTransform.fourier (f : RealVec d → ℂ) η) * modulationPhase (-x) η := by
          ac_rfl
        _ = _ := by simp only [RCLike.conj_mul, Complex.ofReal_pow, Complex.coe_algebraMap]
    _ = ∫ t, inner ℂ (f t) (schwartzCompSubConstCLM (-x) f t) := h
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with t
      simp only [RCLike.inner_apply', schwartzCompSubConstCLM_apply, Function.comp_apply,
        sub_neg_eq_add, RCLike.star_def]
private theorem integral_stftRep_sq_phase_slice_schwartz {d : Nat}
    (h f : SchwartzMap (RealVec d) ℂ) (y x : RealVec d) :
    ∫ η,
        ((‖stftRep
          (h.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
          (f.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
          (y, η)‖ ^ 2 : ℝ) : ℂ) * modulationPhase (-x) η =
      ∫ t, star (stftSliceSchwartz h f y t) * stftSliceSchwartz h f y (t + x) := by
  simpa only [stftRep_schwartz_eq_fourier_apply, Complex.ofReal_pow, stftSliceSchwartz_apply,
    RCLike.star_def, star_mul', RingHomCompTriple.comp_apply, RingHom.id_apply] using
    integral_fourier_sq_phase_schwartz_realVec (stftSliceSchwartz h f y) x
private theorem integrable_norm_sq_schwartz_realVec {d : Nat}
    (f : SchwartzMap (RealVec d) ℂ) :
    Integrable (fun x : RealVec d => ‖f x‖ ^ 2)
      (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) := by
  exact
    (MeasureTheory.memLp_two_iff_integrable_sq_norm
      (μ := (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
      (f := (f : RealVec d -> ℂ)) f.continuous.aestronglyMeasurable).mp
      (f.memLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
private theorem reflected_memLp_schwartz_realVec {d : Nat}
    (h : SchwartzMap (RealVec d) ℂ) :
    MemLp (fun y : RealVec d => h (-y)) 2
      (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) := by
  let μ : MeasureTheory.Measure (RealVec d) := MeasureTheory.volume
  simpa only [Function.comp_def, μ] using
    (h.memLp 2 μ).comp_measurePreserving (Measure.measurePreserving_neg μ)
private theorem integrable_norm_sq_translate_sub_schwartz_realVec {d : Nat}
    (h : SchwartzMap (RealVec d) ℂ) (t : RealVec d) :
    Integrable (fun y : RealVec d => ‖h (t - y)‖ ^ 2)
      (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) := by
  let μ : MeasureTheory.Measure (RealVec d) := MeasureTheory.volume
  have hneg : MemLp (fun y : RealVec d => h (-y)) 2 μ := reflected_memLp_schwartz_realVec h
  have hcomp : MemLp (fun y : RealVec d => h (-(y - t))) 2 μ := by
    simpa only [neg_sub, Function.comp_def, μ] using
      hneg.comp_measurePreserving (MeasureTheory.measurePreserving_sub_right μ t)
  have hmem : MemLp (fun y : RealVec d => h (t - y)) 2 μ := by
    simpa only [sub_eq_add_neg, neg_add_rev, neg_neg, add_comm, add_left_comm, add_assoc, μ] using
      hcomp
  exact
    (MeasureTheory.memLp_two_iff_integrable_sq_norm
      (μ := μ) (f := fun y : RealVec d => h (t - y))
      hmem.aestronglyMeasurable).mp hmem
private theorem integral_norm_sq_translate_sub_schwartz_realVec {d : Nat}
    (h : SchwartzMap (RealVec d) ℂ) (t : RealVec d) :
    ∫ y : RealVec d, ‖h (t - y)‖ ^ 2 = ∫ y : RealVec d, ‖h y‖ ^ 2 := by
  let μ : MeasureTheory.Measure (RealVec d) := MeasureTheory.volume
  calc
    ∫ y : RealVec d, ‖h (t - y)‖ ^ 2
        = ∫ y : RealVec d, ‖h (-y)‖ ^ 2 := by
          simpa only [sub_eq_add_neg, neg_add_rev, neg_neg, μ] using
            (integral_sub_right_eq_self (μ := μ)
              (f := fun y : RealVec d => ‖h (-y)‖ ^ 2) t)
    _ = ∫ y : RealVec d, ‖h y‖ ^ 2 := by
      exact
        (integral_neg_eq_self (μ := μ) (f := fun y : RealVec d => ‖h y‖ ^ 2))
private theorem integral_stft_kernel_slice_schwartz_realVec {d : Nat}
    (h f : SchwartzMap (RealVec d) ℂ) (t : RealVec d) :
    ∫ y : RealVec d, ‖f t‖ ^ 2 * ‖h (t - y)‖ ^ 2 =
      ‖f t‖ ^ 2 * ∫ y : RealVec d, ‖h y‖ ^ 2 := by
  let μ : MeasureTheory.Measure (RealVec d) := MeasureTheory.volume
  calc
    ∫ y : RealVec d, ‖f t‖ ^ 2 * ‖h (t - y)‖ ^ 2
        = ‖f t‖ ^ 2 * ∫ y : RealVec d, ‖h (t - y)‖ ^ 2 := by
          simpa using
            (MeasureTheory.integral_const_mul
              (r := ‖f t‖ ^ 2) (f := fun y : RealVec d => ‖h (t - y)‖ ^ 2)
              (μ := μ))
    _ = ‖f t‖ ^ 2 * ∫ y : RealVec d, ‖h y‖ ^ 2 := by
      rw [integral_norm_sq_translate_sub_schwartz_realVec h t]
private theorem integrable_stft_kernel_schwartz_realVec {d : Nat}
    (h f : SchwartzMap (RealVec d) ℂ) :
    Integrable
      (fun p : RealVec d × RealVec d => ‖f p.1‖ ^ 2 * ‖h (p.1 - p.2)‖ ^ 2)
      ((MeasureTheory.volume : MeasureTheory.Measure (RealVec d)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) := by
  let μ : MeasureTheory.Measure (RealVec d) := MeasureTheory.volume
  let K : RealVec d × RealVec d → ℝ := fun p => ‖f p.1‖ ^ 2 * ‖h (p.1 - p.2)‖ ^ 2
  have hK_meas : AEStronglyMeasurable K (μ.prod μ) := by fun_prop
  refine (MeasureTheory.integrable_prod_iff hK_meas).2 ?_
  constructor
  · refine Filter.Eventually.of_forall ?_
    intro t
    have hslice := integrable_norm_sq_translate_sub_schwartz_realVec h t
    exact hslice.const_mul (‖f t‖ ^ 2)
  · have hf_sq : Integrable (fun t : RealVec d => ‖f t‖ ^ 2) μ := by
      exact integrable_norm_sq_schwartz_realVec f
    have h_outer :
        (fun t : RealVec d => ∫ y : RealVec d, ‖K (t, y)‖ ∂μ) =
          fun t : RealVec d => ‖f t‖ ^ 2 * ∫ y : RealVec d, ‖h y‖ ^ 2 ∂μ := by
      funext t
      calc
        ∫ y : RealVec d, ‖K (t, y)‖ ∂μ
            = ∫ y : RealVec d, ‖f t‖ ^ 2 * ‖h (t - y)‖ ^ 2 ∂μ := by
              refine integral_congr_ae ?_
              filter_upwards with y
              simp [K]
        _ = ‖f t‖ ^ 2 * ∫ y : RealVec d, ‖h y‖ ^ 2 ∂μ :=
          integral_stft_kernel_slice_schwartz_realVec h f t
    rw [h_outer]
    exact hf_sq.mul_const (∫ y : RealVec d, ‖h y‖ ^ 2 ∂μ)
private theorem integral_norm_sq_stft_slice_schwartz_realVec {d : Nat}
    (h f : SchwartzMap (RealVec d) ℂ) (x : RealVec d) :
    ∫ ω : RealVec d, ‖stftRep
      (h.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
      (f.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) (x, ω)‖ ^ 2 =
      ∫ t : RealVec d, ‖stftSliceSchwartz h f x t‖ ^ 2 := by
  calc
    ∫ ω : RealVec d, ‖stftRep
      (h.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
      (f.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) (x, ω)‖ ^ 2 =
        ∫ ω : RealVec d, ‖FourierTransform.fourier
          (stftSliceSchwartz h f x : RealVec d -> ℂ) ω‖ ^ 2 := by
          apply integral_congr_ae
          filter_upwards with ω
          rw [stftRep_schwartz_eq_fourier_apply h f x ω]
    _ = ∫ t : RealVec d, ‖stftSliceSchwartz h f x t‖ ^ 2 :=
      SchwartzMap.integral_norm_sq_fourier (stftSliceSchwartz h f x)
private theorem integrable_stftRep_sq_slice_schwartz_realVec {d : Nat}
    (h f : SchwartzMap (RealVec d) ℂ) (x : RealVec d) :
    Integrable (fun ω : RealVec d => ‖stftRep
      (h.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
      (f.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) (x, ω)‖ ^ 2)
      (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) := by
  have h_fourier :
      Integrable
        (fun ω : RealVec d =>
          ‖(FourierTransform.fourier (stftSliceSchwartz h f x)) ω‖ ^ 2)
        (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) := by
    exact integrable_norm_sq_schwartz_realVec
      (FourierTransform.fourier (stftSliceSchwartz h f x))
  simp_rw [stftRep_schwartz_eq_fourier_apply h f x]
  exact h_fourier
private theorem ambiguityRep_schwartz_eq_integral {d : ℕ}
    (f g : SchwartzMap (RealVec d) ℂ) (ξ : PhaseSpace d) :
    ambiguityRep (f.toLp 2 volume) (g.toLp 2 volume) ξ = ∫ t : RealVec d,
      f (t + (1 / 2 : ℝ) • ξ.1) * star (g (t - (1 / 2 : ℝ) • ξ.1)) *
        modulationPhase ξ.2 t :=
  ambiguityRep_eq_integral_of_ae_eq (f.coeFn_toLp 2 volume) (g.coeFn_toLp 2 volume) ξ
private theorem integral_signal_autocorr_phase_schwartz_realVec {d : Nat}
    (f : SchwartzMap (RealVec d) ℂ) (x ω : RealVec d) :
    ∫ t, star (f t) * f (t + x) * modulationPhase ω (t + (1 / 2 : ℝ) • x) =
      ambiguityRep
        (f.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
        (f.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) (x, ω) := by
  let μ : MeasureTheory.Measure (RealVec d) := MeasureTheory.volume
  let a : RealVec d := (1 / 2 : ℝ) • x
  have ha : a + a = x := by
    rw [← two_smul ℝ a]
    simp [a]
  have hshift :
      ∫ t, star (f t) * f (t + x) * modulationPhase ω (t + a) =
        ∫ t, f (t + a) * star (f (t - a)) * modulationPhase ω t := by
    calc
      _ = ∫ t, f (t + a + a) * star (f (t + a - a)) * modulationPhase ω (t + a) := by
        apply integral_congr_ae
        filter_upwards with t
        rw [add_assoc t a a, ha, add_sub_cancel_right]
        ac_rfl
      _ = _ := integral_add_right_eq_self (μ := μ)
        (f := fun t : RealVec d => f (t + a) * star (f (t - a)) * modulationPhase ω t) a
  rw [ambiguityRep_schwartz_eq_integral]
  exact hshift
private theorem signal_autocorr_integrable_schwartz_realVec {d : Nat}
    (f : SchwartzMap (RealVec d) ℂ) (x : RealVec d) :
    Integrable (fun t : RealVec d => star (f t) * f (t + x))
      (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) := by
  let μ : MeasureTheory.Measure (RealVec d) := MeasureTheory.volume
  have hshift : MemLp (fun t : RealVec d => f (t + x)) 2 μ := by
    simpa only [Function.comp_def, μ] using
      (f.memLp 2 μ).comp_measurePreserving
        (MeasureTheory.measurePreserving_add_right μ x)
  have hmul := (f.memLp 2 μ).star.integrable_mul hshift
  refine hmul.congr ?_
  filter_upwards with t
  simp only [Pi.mul_apply, Pi.star_apply]
private theorem window_autocorr_integrable_schwartz_realVec {d : Nat}
    (h : SchwartzMap (RealVec d) ℂ) (t x : RealVec d) :
    Integrable (fun y : RealVec d => h (t - y) * star (h (t + x - y)))
      (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) := by
  let μ : MeasureTheory.Measure (RealVec d) := MeasureTheory.volume
  have hneg : MemLp (fun y : RealVec d => h (-y)) 2 μ := by
    exact reflected_memLp_schwartz_realVec h
  have hleft' : MemLp (fun y : RealVec d => h (-(y - t))) 2 μ := by
    simpa only [neg_sub, Function.comp_def, μ] using
      hneg.comp_measurePreserving (MeasureTheory.measurePreserving_sub_right μ t)
  have hright' : MemLp (fun y : RealVec d => h (-(y - (t + x)))) 2 μ := by
    simpa only [neg_sub, Function.comp_def, μ] using
      hneg.comp_measurePreserving (MeasureTheory.measurePreserving_sub_right μ (t + x))
  have hleft : MemLp (fun y : RealVec d => h (t - y)) 2 μ := by
    simpa only [sub_eq_add_neg, neg_add_rev, neg_neg, add_comm, add_left_comm, add_assoc] using
      hleft'
  have hright : MemLp (fun y : RealVec d => h (t + x - y)) 2 μ := by
    simpa only [sub_eq_add_neg, add_assoc, neg_add_rev, add_comm, neg_neg, add_left_comm] using
      hright'
  have hmul := hleft.integrable_mul hright.star
  refine hmul.congr ?_
  filter_upwards with y
  simp only [Pi.mul_apply, Pi.star_apply]
private theorem integral_window_autocorr_norm_schwartz_realVec {d : Nat}
    (h : SchwartzMap (RealVec d) ℂ) (t x : RealVec d) :
    ∫ y : RealVec d, ‖h (t - y) * star (h (t + x - y))‖ =
      ∫ y : RealVec d, ‖h (-y) * star (h (x - y))‖ := by
  let μ : MeasureTheory.Measure (RealVec d) := MeasureTheory.volume
  simpa only [sub_eq_add_neg, add_assoc, RCLike.star_def, Complex.norm_mul, RCLike.norm_conj,
    neg_add_rev, neg_neg, add_left_comm, add_comm, μ] using
    (integral_sub_right_eq_self (μ := μ)
      (f := fun y : RealVec d => ‖h (-y) * star (h (x - y))‖) t)
private theorem autocorr_kernel_integrable_schwartz_realVec {d : Nat}
    (f h : SchwartzMap (RealVec d) ℂ) (x : RealVec d) :
    Integrable
      (fun p : RealVec d × RealVec d =>
        (star (f p.1) * f (p.1 + x)) *
          (h (p.1 - p.2) * star (h (p.1 + x - p.2))))
      ((MeasureTheory.volume : MeasureTheory.Measure (RealVec d)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) := by
  let μ : MeasureTheory.Measure (RealVec d) := MeasureTheory.volume
  let A : RealVec d → ℂ := fun t => star (f t) * f (t + x)
  let B : RealVec d × RealVec d → ℂ := fun p =>
    h (p.1 - p.2) * star (h (p.1 + x - p.2))
  have hA : Integrable A μ := signal_autocorr_integrable_schwartz_realVec f x
  have hB : ∀ᵐ t ∂μ, Integrable (fun y : RealVec d => A t * B (t, y)) μ :=
    Filter.Eventually.of_forall fun t =>
      (window_autocorr_integrable_schwartz_realVec h t x).const_mul (A t)
  have hmeas : AEStronglyMeasurable (fun p : RealVec d × RealVec d => A p.1 * B p)
      (μ.prod μ) := by fun_prop
  refine (MeasureTheory.integrable_prod_iff hmeas).2 ?_
  constructor
  · exact hB
  · have hA_norm : Integrable (fun t : RealVec d => ‖A t‖) μ := hA.norm
    let C : ℝ := ∫ y : RealVec d, ‖h (-y) * star (h (x - y))‖ ∂μ
    have hC : ∀ t : RealVec d, ∫ y : RealVec d, ‖B (t, y)‖ ∂μ = C := by
      intro t
      exact integral_window_autocorr_norm_schwartz_realVec h t x
    have houter : Integrable (fun t : RealVec d => ∫ y : RealVec d,
        ‖A t‖ * ‖B (t, y)‖ ∂μ) μ := by
      have hconst : ∀ t : RealVec d,
          ∫ y : RealVec d, ‖A t‖ * ‖B (t, y)‖ ∂μ = ‖A t‖ * C := by
        intro t
        calc
          ∫ y : RealVec d, ‖A t‖ * ‖B (t, y)‖ ∂μ
              = ‖A t‖ * ∫ y : RealVec d, ‖B (t, y)‖ ∂μ := integral_const_mul _ _
          _ = ‖A t‖ * C := by rw [hC t]
      simp_rw [hconst]
      exact hA_norm.mul_const C
    convert houter using 1
    ext t
    apply integral_congr_ae
    filter_upwards with y
    rw [norm_mul]
private theorem ambiguityRep_neg_neg_schwartz_realVec {d : Nat}
    (f : SchwartzMap (RealVec d) ℂ) (x ω : RealVec d) :
    ambiguityRep
        (f.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
        (f.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) (-x, -ω) =
      star (ambiguityRep
        (f.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
        (f.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) (x, ω)) := by
  rw [ambiguityRep_schwartz_eq_integral, ambiguityRep_schwartz_eq_integral]
  refine Eq.trans ?_ integral_conj
  apply integral_congr_ae
  filter_upwards with t
  simp only [← Complex.star_def, smul_neg, sub_eq_add_neg, neg_neg, star_mul, star_star,
    star_modulationPhase, mul_comm]
private theorem integral_window_autocorr_phase_schwartz_realVec {d : Nat}
    (h : SchwartzMap (RealVec d) ℂ) (t x ω : RealVec d) :
    ∫ y : RealVec d,
      h (t - y) * star (h (t + x - y)) * modulationPhase ω y =
        modulationPhase ω (t + (1 / 2 : ℝ) • x) *
          star (ambiguityRep
            (h.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
            (h.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) (x, ω)) := by
  let μ : MeasureTheory.Measure (RealVec d) := MeasureTheory.volume
  let a : RealVec d := (1 / 2 : ℝ) • x
  have ha : a + a = x := by
    rw [← two_smul ℝ a]
    simp [a]
  have hneg_half : (1 / 2 : ℝ) • (-x) = -a := by simp [a]
  have hphase_t : ∀ y : RealVec d,
      modulationPhase ω y = modulationPhase ω t * modulationPhase ω (y - t) := by
    intro y
    have hphase := modulationPhase_add ω t (y - t)
    simpa only [sub_eq_add_neg, add_neg_cancel_comm_assoc, add_comm, add_left_comm, add_assoc] using
      hphase
  have hshift_t :
      ∫ y : RealVec d, h (t - y) * star (h (t + x - y)) * modulationPhase ω y =
        modulationPhase ω t *
          ∫ y : RealVec d, h (-y) * star (h (x - y)) * modulationPhase ω y := by
    calc
      ∫ y : RealVec d, h (t - y) * star (h (t + x - y)) * modulationPhase ω y
          = ∫ y : RealVec d, modulationPhase ω t *
              (h (t - y) * star (h (t + x - y)) *
                modulationPhase ω (y - t)) := by
                refine integral_congr_ae ?_
                filter_upwards with y
                rw [hphase_t y]
                ac_rfl
      _ = modulationPhase ω t *
            ∫ y : RealVec d,
              h (t - y) * star (h (t + x - y)) * modulationPhase ω (y - t) := by
                simpa only [RCLike.star_def, mul_assoc] using
                  (MeasureTheory.integral_const_mul
                    (r := modulationPhase ω t)
                    (f := fun y : RealVec d =>
                      h (t - y) * star (h (t + x - y)) *
                        modulationPhase ω (y - t)))
      _ = modulationPhase ω t *
            ∫ y : RealVec d, h (-y) * star (h (x - y)) * modulationPhase ω y := by
                congr 1
                simpa only [sub_eq_add_neg, add_assoc, RCLike.star_def, neg_add_rev, neg_neg,
                  add_left_comm, add_comm] using
                  (integral_sub_right_eq_self (μ := μ)
                    (f := fun y : RealVec d =>
                      h (-y) * star (h (x - y)) * modulationPhase ω y) t)
  have hneg :
      ∫ y : RealVec d, h (-y) * star (h (x - y)) * modulationPhase ω y =
        ∫ y : RealVec d, h y * star (h (x + y)) * modulationPhase (-ω) y := by
    simpa only [sub_eq_add_neg, RCLike.star_def, mul_assoc, modulationPhase_neg_right, neg_neg,
      add_comm, add_left_comm, add_assoc] using
      (integral_neg_eq_self (μ := μ)
        (f := fun y : RealVec d => h y * star (h (x + y)) * modulationPhase (-ω) y))
  have hphase_x : ∀ y : RealVec d,
      modulationPhase (-ω) y = modulationPhase ω a * modulationPhase (-ω) (y + a) := by
    intro y
    exact modulationPhase_neg_split ω y a
  have hshift_x :
      ∫ y : RealVec d, h y * star (h (x + y)) * modulationPhase (-ω) y =
        modulationPhase ω a *
          ∫ y : RealVec d, h (y - a) * star (h (y + a)) *
            modulationPhase (-ω) y := by
    calc
      ∫ y : RealVec d, h y * star (h (x + y)) * modulationPhase (-ω) y
          = ∫ y : RealVec d, modulationPhase ω a *
              (h y * star (h (x + y)) * modulationPhase (-ω) (y + a)) := by
                refine integral_congr_ae ?_
                filter_upwards with y
                rw [hphase_x y]
                ac_rfl
      _ = modulationPhase ω a *
            ∫ y : RealVec d, h y * star (h (x + y)) *
              modulationPhase (-ω) (y + a) := by
              simpa only [RCLike.star_def, mul_assoc] using
                (MeasureTheory.integral_const_mul
                  (r := modulationPhase ω a)
                  (f := fun y : RealVec d =>
                    h y * star (h (x + y)) * modulationPhase (-ω) (y + a)))
      _ = modulationPhase ω a *
            ∫ y : RealVec d, h (y - a) * star (h (y + a)) *
              modulationPhase (-ω) y := by
              congr 1
              simpa only [RCLike.star_def, sub_eq_add_neg, add_assoc, add_neg_cancel, add_zero,
                add_comm, add_left_comm, ha] using
                (integral_add_right_eq_self (μ := μ)
                  (f := fun y : RealVec d =>
                    h (y - a) * star (h (y + a)) * modulationPhase (-ω) y) a)
  have hamb :
      ∫ y : RealVec d, h (y - a) * star (h (y + a)) * modulationPhase (-ω) y =
        ambiguityRep (h.toLp 2 μ) (h.toLp 2 μ) (-x, -ω) := by
    rw [ambiguityRep_schwartz_eq_integral]
    simp only [hneg_half, sub_eq_add_neg, neg_neg]
  calc
    ∫ y : RealVec d, h (t - y) * star (h (t + x - y)) * modulationPhase ω y
        = modulationPhase ω t *
            ∫ y : RealVec d, h (-y) * star (h (x - y)) *
              modulationPhase ω y := hshift_t
    _ = modulationPhase ω t *
          (modulationPhase ω a * ambiguityRep (h.toLp 2 μ) (h.toLp 2 μ) (-x, -ω)) := by
            rw [hneg, hshift_x, hamb]
    _ = modulationPhase ω (t + a) *
          star (ambiguityRep (h.toLp 2 μ) (h.toLp 2 μ) (x, ω)) := by
            rw [ambiguityRep_neg_neg_schwartz_realVec h x ω, modulationPhase_add]
            ac_rfl
private theorem lpPairing_mul_norm_le {d : Nat} (f g : L2Real d) :
    ‖((ContinuousLinearMap.mul ℂ ℂ).lpPairing
        (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) 2 2) f g‖ ≤ ‖f‖ * ‖g‖ := by
  let B := ContinuousLinearMap.mul ℂ ℂ
  have hleft : B.lpPairing (volume : Measure (RealVec d)) 2 2 f g =
      MeasureTheory.L1.integral (B.holder 1 f g) := by
    rw [MeasureTheory.L1.integral_eq' ℂ]
    rfl
  rw [hleft]
  calc
    _ ≤ ‖B.holder 1 f g‖ := MeasureTheory.L1.norm_integral_le _
    _ ≤ ‖B‖ * ‖f‖ * ‖g‖ := ContinuousLinearMap.norm_holder_apply_apply_le B f g
    _ ≤ 1 * ‖f‖ * ‖g‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_mul_le ℂ ℂ) (norm_nonneg f))
        (norm_nonneg g)
    _ = ‖f‖ * ‖g‖ := by rw [one_mul]
private theorem bilinear_sub
    {E F G : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
    [NormedSpace ℂ E] [NormedSpace ℂ F] [NormedSpace ℂ G]
    (B : E →L[ℂ] F →L[ℂ] G) (f₁ f₂ : E) (g₁ g₂ : F) :
    B f₁ g₁ - B f₂ g₂ = B (f₁ - f₂) g₁ + B f₂ (g₁ - g₂) := by
  simp only [map_sub, sub_apply]
  abel
private theorem norm_bilinear_sub_le
    {E F G : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
    [NormedSpace ℂ E] [NormedSpace ℂ F] [NormedSpace ℂ G]
    (B : E →L[ℂ] F →L[ℂ] G) (hB : ∀ f g, ‖B f g‖ ≤ ‖f‖ * ‖g‖)
    (f₁ f₂ : E) (g₁ g₂ : F) :
    ‖B f₁ g₁ - B f₂ g₂‖ ≤ ‖f₁ - f₂‖ * ‖g₁‖ + ‖f₂‖ * ‖g₁ - g₂‖ := by
  rw [bilinear_sub]
  exact (norm_add_le _ _).trans (add_le_add (hB _ _) (hB _ _))
private theorem norm_stftRep_sub_le {d : Nat}
    (h₁ h₂ f₁ f₂ : L2Real d) (ξ : PhaseSpace d) :
    ‖stftRep h₁ f₁ ξ - stftRep h₂ f₂ ξ‖ ≤
      ‖f₁ - f₂‖ * ‖h₁‖ + ‖f₂‖ * ‖h₁ - h₂‖ := by
  let P := ((ContinuousLinearMap.mul ℂ ℂ).lpPairing
    (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) 2 2)
  let T : L2Real d → L2Real d := fun h =>
    modulateL2 ξ.2 (star (translateL2 (-ξ.1) h))
  have hT_norm : ‖T h₁‖ = ‖h₁‖ :=
    (norm_modulateL2 ξ.2 _).trans ((norm_star_L2 _).trans (norm_translateL2 (-ξ.1) h₁))
  have hT_sub_norm : ‖T h₁ - T h₂‖ = ‖h₁ - h₂‖ := by
    calc
      ‖T h₁ - T h₂‖ = dist (T h₁) (T h₂) := by rw [dist_eq_norm]
      _ = dist (star (translateL2 (-ξ.1) h₁)) (star (translateL2 (-ξ.1) h₂)) := by
        exact dist_modulateL2 ξ.2 _ _
      _ = dist (translateL2 (-ξ.1) h₁) (translateL2 (-ξ.1) h₂) := by rw [dist_star_L2]
      _ = dist h₁ h₂ := by rw [dist_translateL2]
      _ = ‖h₁ - h₂‖ := by rw [dist_eq_norm]
  calc
    ‖stftRep h₁ f₁ ξ - stftRep h₂ f₂ ξ‖ = ‖P f₁ (T h₁) - P f₂ (T h₂)‖ :=
      congrArg norm (congrArg₂ (fun a b : ℂ => a - b)
        (stftRep_eq_lpPairing h₁ f₁ ξ) (stftRep_eq_lpPairing h₂ f₂ ξ))
    _ ≤ ‖f₁ - f₂‖ * ‖h₁‖ + ‖f₂‖ * ‖h₁ - h₂‖ := by
      simpa only [hT_norm, hT_sub_norm] using
        norm_bilinear_sub_le P (fun f g => lpPairing_mul_norm_le f g) f₁ f₂ (T h₁) (T h₂)
private theorem stftRep_aestronglyMeasurable {d : Nat} (h f : L2Real d) :
    AEStronglyMeasurable (stftRep h f)
      (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)) :=
  (continuous_stftRep h f).aestronglyMeasurable
private theorem stftRep_sq_integrable_schwartz_realVec {d : Nat}
    (h f : SchwartzMap (RealVec d) ℂ) :
    Integrable (fun p : PhaseSpace d => ‖stftRep
      (h.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
      (f.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) p‖ ^ 2)
      (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)) := by
  let μ : MeasureTheory.Measure (RealVec d) := MeasureTheory.volume
  let hLp : L2Real d := h.toLp 2 μ
  let fLp : L2Real d := f.toLp 2 μ
  let F : PhaseSpace d → ℝ := fun p => ‖stftRep hLp fLp p‖ ^ 2
  have hF_meas : AEStronglyMeasurable F (μ.prod μ) :=
    ((continuous_stftRep hLp fLp).norm.pow 2).aestronglyMeasurable
  change Integrable F (μ.prod μ)
  refine (MeasureTheory.integrable_prod_iff hF_meas).2 ?_
  constructor
  · refine Filter.Eventually.of_forall ?_
    intro x
    exact integrable_stftRep_sq_slice_schwartz_realVec h f x
  · have hkernel : Integrable
        (fun p : RealVec d × RealVec d => ‖f p.1‖ ^ 2 * ‖h (p.1 - p.2)‖ ^ 2)
        (μ.prod μ) := integrable_stft_kernel_schwartz_realVec h f
    have h_outer :
        (fun x : RealVec d => ∫ ω : RealVec d, ‖F (x, ω)‖ ∂μ) =
          fun x : RealVec d => ∫ t : RealVec d, ‖f t‖ ^ 2 * ‖h (t - x)‖ ^ 2 ∂μ := by
      funext x
      calc
        ∫ ω : RealVec d, ‖F (x, ω)‖ ∂μ
            = ∫ ω : RealVec d, ‖stftRep hLp fLp (x, ω)‖ ^ 2 ∂μ := by
              refine integral_congr_ae ?_
              filter_upwards with ω
              exact Real.norm_of_nonneg (sq_nonneg _)
        _ = ∫ t : RealVec d, ‖f t‖ ^ 2 * ‖h (t - x)‖ ^ 2 ∂μ := by
          rw [integral_norm_sq_stft_slice_schwartz_realVec h f x]
          refine integral_congr_ae ?_
          filter_upwards with t
          rw [stftSliceSchwartz_apply, norm_mul, norm_star, mul_pow]
    rw [h_outer]
    simpa only [norm_mul, norm_pow, norm_norm] using hkernel.integral_norm_prod_right
private theorem stftRep_sq_complex_integrable_schwartz_realVec {d : Nat}
    (h f : SchwartzMap (RealVec d) ℂ) :
    Integrable
      (fun p : PhaseSpace d => ((‖stftRep
        (h.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
        (f.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) p‖ ^ 2 : ℝ) : ℂ))
      (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)) := by
  simpa only [Complex.ofReal_pow, Complex.coe_algebraMap] using
    (stftRep_sq_integrable_schwartz_realVec h f).ofReal (𝕜 := ℂ)
private theorem integral_norm_sq_schwartz_eq_lpNorm_sq_realVec {d : Nat}
    (f : SchwartzMap (RealVec d) ℂ) :
    ∫ x : RealVec d, ‖f x‖ ^ 2 =
      MeasureTheory.lpNorm (f : RealVec d -> ℂ) 2
          (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) ^ 2 := by
  let μ : MeasureTheory.Measure (RealVec d) := MeasureTheory.volume
  have hf : MeasureTheory.MemLp (f : RealVec d -> ℂ) 2 μ := f.memLp 2 μ
  have hnorm :
      MeasureTheory.lpNorm (f : RealVec d -> ℂ) 2 μ =
        (∫ x : RealVec d, ‖f x‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
    rw [MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal
      (μ := μ) (p := (2 : ENNReal))
      (by norm_num : (2 : ENNReal) ≠ 0) (by norm_num : (2 : ENNReal) ≠ ⊤)
      hf.aestronglyMeasurable]
    norm_num
  rw [hnorm]
  have hpow :
      ∫ x : RealVec d, ‖f x‖ ^ (2 : ℝ) ∂μ =
        ∫ x : RealVec d, ‖f x‖ ^ 2 ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards with x
    norm_num
  rw [hpow]
  have hint_nonneg : 0 ≤ ∫ x : RealVec d, ‖f x‖ ^ 2 ∂μ := integral_nonneg fun _ => by positivity
  rw [← Real.sqrt_eq_rpow]
  exact (Real.sq_sqrt hint_nonneg).symm
private theorem integral_stftRep_sq_schwartz_realVec {d : Nat}
    (h f : SchwartzMap (RealVec d) ℂ) :
    ∫ p : PhaseSpace d,
        ‖stftRep
          (h.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
          (f.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) p‖ ^ 2 =
      MeasureTheory.lpNorm (f : RealVec d -> ℂ) 2
          (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) ^ 2 *
        MeasureTheory.lpNorm (h : RealVec d -> ℂ) 2
          (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) ^ 2 := by
  let μ : MeasureTheory.Measure (RealVec d) := MeasureTheory.volume
  let hLp : L2Real d := h.toLp 2 μ
  let fLp : L2Real d := f.toLp 2 μ
  let K : RealVec d → RealVec d → ℝ := fun x t => ‖f t‖ ^ 2 * ‖h (t - x)‖ ^ 2
  have hK : Integrable (Function.uncurry K) (μ.prod μ) :=
    (integrable_stft_kernel_schwartz_realVec h f).swap
  calc
    ∫ p : PhaseSpace d, ‖stftRep (h.toLp 2 μ) (f.toLp 2 μ) p‖ ^ 2
        = ∫ x : RealVec d, ∫ ω : RealVec d, ‖stftRep hLp fLp (x, ω)‖ ^ 2 := by
            change
              ∫ p : RealVec d × RealVec d, ‖stftRep hLp fLp p‖ ^ 2 ∂(μ.prod μ) =
                ∫ x : RealVec d, ∫ ω : RealVec d, ‖stftRep hLp fLp (x, ω)‖ ^ 2 ∂μ ∂μ
            rw [MeasureTheory.integral_prod
              (μ := μ) (ν := μ)
              (f := fun p : RealVec d × RealVec d => ‖stftRep hLp fLp p‖ ^ 2)]
            exact stftRep_sq_integrable_schwartz_realVec h f
    _ = ∫ x : RealVec d, ∫ t : RealVec d, K x t := by
          refine integral_congr_ae ?_
          filter_upwards with x
          rw [integral_norm_sq_stft_slice_schwartz_realVec h f x]
          refine integral_congr_ae ?_
          filter_upwards with t
          calc
            ‖stftSliceSchwartz h f x t‖ ^ 2
                = ‖f t * star (h (t - x))‖ ^ 2 := by rw [stftSliceSchwartz_apply]
            _ = (‖f t‖ * ‖h (t - x)‖) ^ 2 := by rw [norm_mul, norm_star]
            _ = K x t := mul_pow _ _ _
    _ = ∫ t : RealVec d, ∫ x : RealVec d, K x t := by exact MeasureTheory.integral_integral_swap hK
    _ = ∫ t : RealVec d, ‖f t‖ ^ 2 * ∫ x : RealVec d, ‖h x‖ ^ 2 := by
          refine integral_congr_ae ?_
          filter_upwards with t
          exact integral_stft_kernel_slice_schwartz_realVec h f t
    _ = (∫ t : RealVec d, ‖f t‖ ^ 2) * (∫ x : RealVec d, ‖h x‖ ^ 2) := by
          exact MeasureTheory.integral_mul_const
            (f := fun t : RealVec d => ‖f t‖ ^ 2)
            (r := ∫ x : RealVec d, ‖h x‖ ^ 2) (μ := μ)
    _ = MeasureTheory.lpNorm (f : RealVec d -> ℂ) 2 μ ^ 2 *
        MeasureTheory.lpNorm (h : RealVec d -> ℂ) 2 μ ^ 2 := by
          rw [integral_norm_sq_schwartz_eq_lpNorm_sq_realVec f,
            integral_norm_sq_schwartz_eq_lpNorm_sq_realVec h]
private theorem stftRep_memLp_schwartz_realVec {d : Nat}
    (h f : SchwartzMap (RealVec d) ℂ) :
    MeasureTheory.MemLp
      (fun p : PhaseSpace d =>
        stftRep
          (h.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
          (f.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) p)
      2 (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)) := by
  exact
    (MeasureTheory.memLp_two_iff_integrable_sq_norm
      (stftRep_aestronglyMeasurable
        (h.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
        (f.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))))).2
      (stftRep_sq_integrable_schwartz_realVec h f)
private theorem lpNorm_stftRep_schwartz_realVec {d : Nat}
    (h f : SchwartzMap (RealVec d) ℂ) :
    MeasureTheory.lpNorm
      (fun p : PhaseSpace d =>
        stftRep
          (h.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
          (f.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) p)
      2 (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)) =
      MeasureTheory.lpNorm (f : RealVec d -> ℂ) 2
          (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) *
        MeasureTheory.lpNorm (h : RealVec d -> ℂ) 2
          (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) := by
  let μ : MeasureTheory.Measure (RealVec d) := MeasureTheory.volume
  let hLp : L2Real d := h.toLp 2 μ
  let fLp : L2Real d := f.toLp 2 μ
  rw [MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal
      (μ := (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)))
      (p := (2 : ENNReal))
      (by norm_num : (2 : ENNReal) ≠ 0) (by norm_num : (2 : ENNReal) ≠ ⊤)
      (stftRep_aestronglyMeasurable hLp fLp)]
  norm_num
  rw [show
      ∫ p : PhaseSpace d, ‖stftRep hLp fLp p‖ ^ 2 =
        MeasureTheory.lpNorm (f : RealVec d -> ℂ) 2 μ ^ 2 *
          MeasureTheory.lpNorm (h : RealVec d -> ℂ) 2 μ ^ 2 by
        exact integral_stftRep_sq_schwartz_realVec h f]
  have hnonneg :
      0 ≤ MeasureTheory.lpNorm (f : RealVec d -> ℂ) 2 μ *
        MeasureTheory.lpNorm (h : RealVec d -> ℂ) 2 μ :=
    mul_nonneg MeasureTheory.lpNorm_nonneg MeasureTheory.lpNorm_nonneg
  rw [show
      MeasureTheory.lpNorm (f : RealVec d -> ℂ) 2 μ ^ 2 *
          MeasureTheory.lpNorm (h : RealVec d -> ℂ) 2 μ ^ 2 =
        (MeasureTheory.lpNorm (f : RealVec d -> ℂ) 2 μ *
          MeasureTheory.lpNorm (h : RealVec d -> ℂ) 2 μ) ^ 2 by ring]
  rw [← Real.sqrt_eq_rpow]
  simp [Real.sqrt_sq_eq_abs, abs_of_nonneg hnonneg, μ]
private theorem eLpNorm_stftRep_schwartz_eq {d : Nat}
    (h f : SchwartzMap (RealVec d) ℂ) :
    MeasureTheory.eLpNorm
      (fun p : PhaseSpace d =>
        stftRep
          (h.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
          (f.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) p)
      2 (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)) =
      ENNReal.ofReal
        (MeasureTheory.lpNorm (f : RealVec d -> ℂ) 2
            (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) *
          MeasureTheory.lpNorm (h : RealVec d -> ℂ) 2
            (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) := by
  calc
    MeasureTheory.eLpNorm
        (fun p : PhaseSpace d =>
          stftRep
            (h.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
            (f.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) p)
        2 (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d))
        = ENNReal.ofReal
            (MeasureTheory.lpNorm
              (fun p : PhaseSpace d =>
                stftRep
                  (h.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
                  (f.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) p)
              2 (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d))) := by
            symm
            exact MeasureTheory.ofReal_lpNorm (stftRep_memLp_schwartz_realVec h f)
    _ = ENNReal.ofReal
          (MeasureTheory.lpNorm (f : RealVec d -> ℂ) 2
              (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) *
            MeasureTheory.lpNorm (h : RealVec d -> ℂ) 2
              (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) := by
          rw [lpNorm_stftRep_schwartz_realVec]
private theorem cross_norm_bound_tendsto_zero
    {E : Type*} [NormedAddCommGroup E] {hN fN : Nat → E} {h f : E}
    (hhN : Tendsto hN atTop (nhds h)) (hfN : Tendsto fN atTop (nhds f)) :
    Tendsto (fun n : Nat => ‖fN n - f‖ * ‖hN n‖ + ‖f‖ * ‖hN n - h‖)
      atTop (nhds 0) := by
  have hf_err : Tendsto (fun n : Nat => ‖fN n - f‖) atTop (nhds 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hfN
  have hh_err : Tendsto (fun n : Nat => ‖hN n - h‖) atTop (nhds 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hhN
  simpa only [zero_mul, mul_zero, add_zero] using
    (hf_err.mul hhN.norm).add (tendsto_const_nhds.mul hh_err)
private theorem stftRep_tendsto_schwartzApprox_pointwise {d : Nat}
    (h f : L2Real d) (ξ : PhaseSpace d) :
    Tendsto
      (fun n : Nat =>
        stftRep
          ((schwartzApproxRealVec (MeasureTheory.Lp.memLp h) n).toLp 2
            (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
          ((schwartzApproxRealVec (MeasureTheory.Lp.memLp f) n).toLp 2
            (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) ξ)
      atTop (nhds (stftRep h f ξ)) := by
  let μ : MeasureTheory.Measure (RealVec d) := MeasureTheory.volume
  let hN : Nat → L2Real d := fun n =>
    (schwartzApproxRealVec (MeasureTheory.Lp.memLp h) n).toLp 2 μ
  let fN : Nat → L2Real d := fun n =>
    (schwartzApproxRealVec (MeasureTheory.Lp.memLp f) n).toLp 2 μ
  have hhN := schwartzApproxRealVec_toLp_tendsto h
  have hfN := schwartzApproxRealVec_toLp_tendsto f
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun _ => dist_nonneg) ?_ (cross_norm_bound_tendsto_zero hhN hfN)
  intro n
  rw [dist_eq_norm]
  exact norm_stftRep_sub_le (hN n) h (fN n) f ξ
private theorem eLpNorm_stftRep_le {d : Nat} (h f : L2Real d) :
    MeasureTheory.eLpNorm (stftRep h f) 2
        (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)) ≤
      ENNReal.ofReal
        (MeasureTheory.lpNorm (f : RealVec d -> ℂ) 2
            (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) *
          MeasureTheory.lpNorm (h : RealVec d -> ℂ) 2
            (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) := by
  let μ : MeasureTheory.Measure (RealVec d) := MeasureTheory.volume
  let μP : MeasureTheory.Measure (PhaseSpace d) := MeasureTheory.volume
  let hmem : MeasureTheory.MemLp (h : RealVec d -> ℂ) 2 μ := MeasureTheory.Lp.memLp h
  let fmem : MeasureTheory.MemLp (f : RealVec d -> ℂ) 2 μ := MeasureTheory.Lp.memLp f
  let hN : Nat → L2Real d := fun n => (schwartzApproxRealVec hmem n).toLp 2 μ
  let fN : Nat → L2Real d := fun n => (schwartzApproxRealVec fmem n).toLp 2 μ
  let F : PhaseSpace d → ℂ := stftRep h f
  let Fₙ : Nat → PhaseSpace d → ℂ := fun n => stftRep (hN n) (fN n)
  have hpoint : ∀ᵐ p : PhaseSpace d ∂μP, Tendsto (fun n : Nat => Fₙ n p) atTop (nhds (F p)) := by
    filter_upwards with p
    exact
      stftRep_tendsto_schwartzApprox_pointwise h f p
  have hmeas : ∀ n : Nat, AEStronglyMeasurable (Fₙ n) μP := by
    intro n
    exact stftRep_aestronglyMeasurable (hN n) (fN n)
  have hliminf :
      MeasureTheory.eLpNorm F 2 μP ≤
        atTop.liminf (fun n : Nat => MeasureTheory.eLpNorm (Fₙ n) 2 μP) :=
    MeasureTheory.Lp.eLpNorm_lim_le_liminf_eLpNorm hmeas F hpoint
  have hprod :
      Tendsto
        (fun n : Nat =>
          MeasureTheory.lpNorm (schwartzApproxRealVec fmem n : RealVec d -> ℂ) 2 μ *
            MeasureTheory.lpNorm (schwartzApproxRealVec hmem n : RealVec d -> ℂ) 2 μ)
        atTop
        (nhds (MeasureTheory.lpNorm (f : RealVec d -> ℂ) 2 μ *
          MeasureTheory.lpNorm (h : RealVec d -> ℂ) 2 μ)) := by
    exact (schwartzApproxRealVec_tendsto_lpNorm fmem).mul
      (schwartzApproxRealVec_tendsto_lpNorm hmem)
  have hnorms' :
      Tendsto
        (fun n : Nat =>
          ENNReal.ofReal
            (MeasureTheory.lpNorm (schwartzApproxRealVec fmem n : RealVec d -> ℂ) 2 μ *
              MeasureTheory.lpNorm (schwartzApproxRealVec hmem n : RealVec d -> ℂ) 2 μ))
        atTop
        (nhds (ENNReal.ofReal (MeasureTheory.lpNorm (f : RealVec d -> ℂ) 2 μ *
          MeasureTheory.lpNorm (h : RealVec d -> ℂ) 2 μ))) := by
    exact
      (ENNReal.continuous_ofReal.tendsto
        (MeasureTheory.lpNorm (f : RealVec d -> ℂ) 2 μ *
          MeasureTheory.lpNorm (h : RealVec d -> ℂ) 2 μ)).comp hprod
  have hnorms :
      Tendsto (fun n : Nat => MeasureTheory.eLpNorm (Fₙ n) 2 μP)
        atTop
        (nhds (ENNReal.ofReal (MeasureTheory.lpNorm (f : RealVec d -> ℂ) 2 μ *
          MeasureTheory.lpNorm (h : RealVec d -> ℂ) 2 μ))) := by
    have hnorms_aux :
        Tendsto
          (fun n : Nat =>
            MeasureTheory.eLpNorm
              (fun p : PhaseSpace d =>
                stftRep
                  ((schwartzApproxRealVec hmem n).toLp 2 μ)
                  ((schwartzApproxRealVec fmem n).toLp 2 μ) p)
              2 μP)
          atTop
          (nhds (ENNReal.ofReal (MeasureTheory.lpNorm (f : RealVec d -> ℂ) 2 μ *
            MeasureTheory.lpNorm (h : RealVec d -> ℂ) 2 μ))) := by
      simpa only [eLpNorm_stftRep_schwartz_eq, lpNorm_nonneg, ENNReal.ofReal_mul, μ, μP] using
        hnorms'
    simpa only [lpNorm_nonneg, ENNReal.ofReal_mul, Fₙ, hN, fN] using hnorms_aux
  calc
    MeasureTheory.eLpNorm (stftRep h f) 2 μP
        = MeasureTheory.eLpNorm F 2 μP := by rfl
    _ ≤ atTop.liminf (fun n : Nat => MeasureTheory.eLpNorm (Fₙ n) 2 μP) := hliminf
    _ = ENNReal.ofReal
          (MeasureTheory.lpNorm (f : RealVec d -> ℂ) 2 μ *
            MeasureTheory.lpNorm (h : RealVec d -> ℂ) 2 μ) := by rw [hnorms.liminf_eq]
private theorem stftRep_sq_integrable {d : Nat} (h f : L2Real d) :
    Integrable (fun p : PhaseSpace d => ‖stftRep h f p‖ ^ 2)
      (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)) := by
  let μ : MeasureTheory.Measure (RealVec d) := MeasureTheory.volume
  let μP : MeasureTheory.Measure (PhaseSpace d) := MeasureTheory.volume
  have hfinite_rhs :
      ENNReal.ofReal
        (MeasureTheory.lpNorm (f : RealVec d -> ℂ) 2 μ *
          MeasureTheory.lpNorm (h : RealVec d -> ℂ) 2 μ) < ⊤ :=
    ENNReal.ofReal_lt_top
  have hfin : MeasureTheory.eLpNorm (stftRep h f) 2 μP < ⊤ :=
    lt_of_le_of_lt (eLpNorm_stftRep_le h f) hfinite_rhs
  have hmem : MeasureTheory.MemLp (stftRep h f) 2 μP := ⟨stftRep_aestronglyMeasurable h f, hfin⟩
  exact (MeasureTheory.memLp_two_iff_integrable_sq_norm
    (stftRep_aestronglyMeasurable h f)).mp hmem
private theorem stftRep_sq_complex_integrable {d : Nat} (h f : L2Real d) :
    Integrable (fun p : PhaseSpace d => ((‖stftRep h f p‖ ^ 2 : ℝ) : ℂ))
      (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)) := by
  simpa only [Complex.ofReal_pow, Complex.coe_algebraMap] using
    (stftRep_sq_integrable h f).ofReal (𝕜 := ℂ)
private theorem stftRep_memLp {d : Nat} (h f : L2Real d) :
    MeasureTheory.MemLp (stftRep h f) 2
      (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)) := by
  exact (MeasureTheory.memLp_two_iff_integrable_sq_norm
    (stftRep_aestronglyMeasurable h f)).2 (stftRep_sq_integrable h f)
private theorem lpNorm_coeFn_L2Real_eq_norm {d : Nat} (f : L2Real d) :
    MeasureTheory.lpNorm (f : RealVec d -> ℂ) 2
      (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) = ‖f‖ := by
  rw [MeasureTheory.Lp.norm_def,
    MeasureTheory.toReal_eLpNorm (MeasureTheory.Lp.aestronglyMeasurable f)]
private theorem lpNorm_stftRep_le_lpNorm {d : Nat} (h f : L2Real d) :
    MeasureTheory.lpNorm (stftRep h f) 2
        (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)) ≤
      MeasureTheory.lpNorm (f : RealVec d -> ℂ) 2
          (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) *
        MeasureTheory.lpNorm (h : RealVec d -> ℂ) 2
          (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) := by
  let μP : MeasureTheory.Measure (PhaseSpace d) := MeasureTheory.volume
  have hmem : MeasureTheory.MemLp (stftRep h f) 2 μP := stftRep_memLp h f
  rw [← MeasureTheory.toReal_eLpNorm hmem.aestronglyMeasurable]
  simpa only [ge_iff_le, lpNorm_nonneg, ENNReal.ofReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal] using
    (ENNReal.toReal_le_toReal hmem.eLpNorm_ne_top ENNReal.ofReal_ne_top).mpr
      (eLpNorm_stftRep_le h f)
private theorem lpNorm_stftRep_le {d : Nat} (h f : L2Real d) :
    MeasureTheory.lpNorm (stftRep h f) 2
        (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)) ≤
      ‖f‖ * ‖h‖ := by simpa only [lpNorm_coeFn_L2Real_eq_norm] using lpNorm_stftRep_le_lpNorm h f
private theorem translateL2_sub {d : Nat} (a : RealVec d) (f g : L2Real d) :
    translateL2 a (f - g) = translateL2 a f - translateL2 a g := by
  simpa only [translateL2] using DomAddAct.vadd_Lp_sub (DomAddAct.mk a) f g
private theorem star_L2_sub {d : Nat} (f g : L2Real d) :
    star (f - g) = star f - star g := by
  apply MeasureTheory.Lp.ext
  filter_upwards [MeasureTheory.Lp.coeFn_star (f - g), MeasureTheory.Lp.coeFn_star f,
    MeasureTheory.Lp.coeFn_star g, MeasureTheory.Lp.coeFn_sub f g,
    MeasureTheory.Lp.coeFn_sub (star f) (star g)] with t hfg hf hg hsub hstarsub
  rw [hfg, hstarsub]
  simp only [Pi.star_apply, Pi.sub_apply] at *
  rw [hsub, hf, hg]
  simp
private theorem modulateL2_sub {d : Nat} (ω : RealVec d) (f g : L2Real d) :
    modulateL2 ω (f - g) = modulateL2 ω f - modulateL2 ω g := by
  apply MeasureTheory.Lp.ext
  filter_upwards [modulateL2_coeFn ω (f - g), modulateL2_coeFn ω f,
    modulateL2_coeFn ω g, MeasureTheory.Lp.coeFn_sub f g,
    MeasureTheory.Lp.coeFn_sub (modulateL2 ω f) (modulateL2 ω g)] with t hfg hf hg hsub hmodsub
  rw [hfg, hmodsub]
  simp only [Pi.sub_apply] at *
  rw [hf, hg, hsub]
  ring
private theorem stftRep_sub_eq_add {d : Nat}
    (h₁ h₂ f₁ f₂ : L2Real d) (ξ : PhaseSpace d) :
    stftRep h₁ f₁ ξ - stftRep h₂ f₂ ξ =
      stftRep h₁ (f₁ - f₂) ξ + stftRep (h₁ - h₂) f₂ ξ := by
  let P := ((ContinuousLinearMap.mul ℂ ℂ).lpPairing
    (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) 2 2)
  -- Generate the existing congruence theorem on a small application for import compatibility.
  have hpairing_zero : P 0 0 = 0 := by simp [P]
  let T : L2Real d → L2Real d := fun h =>
    modulateL2 ξ.2 (star (translateL2 (-ξ.1) h))
  have hT_sub : T (h₁ - h₂) = T h₁ - T h₂ := by
    simp [T, translateL2_sub, star_L2_sub, modulateL2_sub]
  calc
    stftRep h₁ f₁ ξ - stftRep h₂ f₂ ξ = P f₁ (T h₁) - P f₂ (T h₂) :=
      congrArg₂ (fun a b : ℂ => a - b)
        (stftRep_eq_lpPairing h₁ f₁ ξ) (stftRep_eq_lpPairing h₂ f₂ ξ)
    _ = P (f₁ - f₂) (T h₁) + P f₂ (T h₁ - T h₂) :=
      bilinear_sub P f₁ f₂ (T h₁) (T h₂)
    _ = stftRep h₁ (f₁ - f₂) ξ + stftRep (h₁ - h₂) f₂ ξ :=
      congrArg₂ (fun a b : ℂ => a + b)
        (stftRep_eq_lpPairing h₁ (f₁ - f₂) ξ).symm
        ((congrArg (P f₂) hT_sub.symm).trans
          (stftRep_eq_lpPairing (h₁ - h₂) f₂ ξ).symm)
private theorem lpNorm_stftRep_sub_le {d : Nat}
    (h₁ h₂ f₁ f₂ : L2Real d) :
    MeasureTheory.lpNorm
      (fun ξ : PhaseSpace d => stftRep h₁ f₁ ξ - stftRep h₂ f₂ ξ)
      2 (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)) ≤
      ‖f₁ - f₂‖ * ‖h₁‖ + ‖f₂‖ * ‖h₁ - h₂‖ := by
  let μP : MeasureTheory.Measure (PhaseSpace d) := MeasureTheory.volume
  have hmem₁ : MeasureTheory.MemLp (stftRep h₁ (f₁ - f₂)) 2 μP :=
    stftRep_memLp h₁ (f₁ - f₂)
  have hmem₂ : MeasureTheory.MemLp (stftRep (h₁ - h₂) f₂) 2 μP :=
    stftRep_memLp (h₁ - h₂) f₂
  calc
    MeasureTheory.lpNorm
        (fun ξ : PhaseSpace d => stftRep h₁ f₁ ξ - stftRep h₂ f₂ ξ) 2 μP
        = MeasureTheory.lpNorm
            ((stftRep h₁ (f₁ - f₂)) + stftRep (h₁ - h₂) f₂) 2 μP := by
            congr 1
            funext ξ
            exact stftRep_sub_eq_add h₁ h₂ f₁ f₂ ξ
    _ ≤ MeasureTheory.lpNorm (stftRep h₁ (f₁ - f₂)) 2 μP +
          MeasureTheory.lpNorm (stftRep (h₁ - h₂) f₂) 2 μP :=
          MeasureTheory.lpNorm_add_le hmem₁ (by norm_num)
    _ ≤ ‖f₁ - f₂‖ * ‖h₁‖ + ‖f₂‖ * ‖h₁ - h₂‖ :=
      add_le_add (lpNorm_stftRep_le h₁ (f₁ - f₂)) (lpNorm_stftRep_le (h₁ - h₂) f₂)
private theorem lpNorm_stftRep_tendsto_schwartzApprox {d : Nat}
    (h f : L2Real d) :
    Tendsto
      (fun n : Nat =>
        MeasureTheory.lpNorm
          (fun ξ : PhaseSpace d =>
            stftRep
              ((schwartzApproxRealVec (MeasureTheory.Lp.memLp h) n).toLp 2
                (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
              ((schwartzApproxRealVec (MeasureTheory.Lp.memLp f) n).toLp 2
                (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) ξ -
              stftRep h f ξ)
          2 (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)))
      atTop (nhds 0) := by
  let μ : MeasureTheory.Measure (RealVec d) := MeasureTheory.volume
  let hN : Nat → L2Real d := fun n =>
    (schwartzApproxRealVec (MeasureTheory.Lp.memLp h) n).toLp 2 μ
  let fN : Nat → L2Real d := fun n =>
    (schwartzApproxRealVec (MeasureTheory.Lp.memLp f) n).toLp 2 μ
  have hhN := schwartzApproxRealVec_toLp_tendsto h
  have hfN := schwartzApproxRealVec_toLp_tendsto f
  refine squeeze_zero (fun _ => MeasureTheory.lpNorm_nonneg) ?_
    (cross_norm_bound_tendsto_zero hhN hfN)
  intro n
  exact lpNorm_stftRep_sub_le (hN n) h (fN n) f
private theorem lpNorm_mul_le_real
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α} {f g : α → ℝ}
    (hf : MeasureTheory.MemLp f 2 μ) (hg : MeasureTheory.MemLp g 2 μ) :
    MeasureTheory.lpNorm (fun x => f x * g x) 1 μ ≤
      MeasureTheory.lpNorm f 2 μ * MeasureTheory.lpNorm g 2 μ := by
  have hfg_m : AEStronglyMeasurable (fun x => f x * g x) μ :=
    hf.aestronglyMeasurable.mul hg.aestronglyMeasurable
  rw [← MeasureTheory.toReal_eLpNorm (p := 1) hfg_m,
      ← MeasureTheory.toReal_eLpNorm (p := 2) hf.aestronglyMeasurable,
      ← MeasureTheory.toReal_eLpNorm (p := 2) hg.aestronglyMeasurable,
      ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono (ENNReal.mul_ne_top hf.eLpNorm_ne_top hg.eLpNorm_ne_top) ?_
  rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num),
      eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num),
      eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num)]
  simpa using eLpNorm'_le_eLpNorm'_mul_eLpNorm' hf.aestronglyMeasurable hg.aestronglyMeasurable
    (· * ·) 1 (Filter.Eventually.of_forall fun x => by simp)
    (by norm_num) (by norm_num) (by norm_num)
private theorem lpNorm_norm_sq_sub_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {F G : α → ℂ}
    (hF : MemLp F 2 μ) (hG : MemLp G 2 μ) :
    lpNorm (fun x => ((‖F x‖ ^ 2 : ℝ) : ℂ) - ((‖G x‖ ^ 2 : ℝ) : ℂ)) 1 μ ≤
      (lpNorm F 2 μ + lpNorm G 2 μ) * lpNorm (fun x => F x - G x) 2 μ := by
  let A : α → ℝ := fun x => ‖F x‖ + ‖G x‖
  let B : α → ℝ := fun x => ‖F x - G x‖
  have hA : MemLp A 2 μ := hF.norm.add hG.norm
  have hB : MemLp B 2 μ := (hF.sub hG).norm
  have hproduct : MemLp (fun x => A x * B x) 1 μ := hB.mul hA
  have hpoint : ∀ x,
      ‖((‖F x‖ ^ 2 : ℝ) : ℂ) - ((‖G x‖ ^ 2 : ℝ) : ℂ)‖ ≤ A x * B x := by
    intro x
    have hnonnegative : 0 ≤ ‖F x‖ + ‖G x‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_sub_sq,
      abs_mul, abs_of_nonneg hnonnegative]
    exact mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le _ _) hnonnegative
  have hsum : lpNorm A 2 μ ≤ lpNorm F 2 μ + lpNorm G 2 μ := by
    calc
      _ ≤ lpNorm (fun x => ‖F x‖) 2 μ + lpNorm (fun x => ‖G x‖) 2 μ :=
        lpNorm_add_le hF.norm (by norm_num)
      _ = _ := by rw [lpNorm_norm hF.aestronglyMeasurable, lpNorm_norm hG.aestronglyMeasurable]
  have hnorm : lpNorm B 2 μ = lpNorm (fun x => F x - G x) 2 μ :=
    lpNorm_norm (hF.sub hG).aestronglyMeasurable 2
  calc
    _ ≤ lpNorm (fun x => A x * B x) 1 μ := lpNorm_mono_real hproduct hpoint
    _ ≤ lpNorm A 2 μ * lpNorm B 2 μ := lpNorm_mul_le_real hA hB
    _ ≤ (lpNorm F 2 μ + lpNorm G 2 μ) * lpNorm (fun x => F x - G x) 2 μ := by
      rw [hnorm]
      exact mul_le_mul_of_nonneg_right hsum lpNorm_nonneg
private theorem lpNorm_stftRep_sq_sub_tendsto_zero {d : Nat}
    (h f : L2Real d) :
    Tendsto
      (fun n : Nat =>
        MeasureTheory.lpNorm
          (fun ξ : PhaseSpace d =>
            (((‖stftRep
              ((schwartzApproxRealVec (MeasureTheory.Lp.memLp h) n).toLp 2
                (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
              ((schwartzApproxRealVec (MeasureTheory.Lp.memLp f) n).toLp 2
                (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) ξ‖ ^ 2 : ℝ) : ℂ) -
              ((‖stftRep h f ξ‖ ^ 2 : ℝ) : ℂ)))
          1 (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)))
      atTop (nhds 0) := by
  let μ : MeasureTheory.Measure (RealVec d) := MeasureTheory.volume
  let μP : MeasureTheory.Measure (PhaseSpace d) := MeasureTheory.volume
  let hN : Nat → L2Real d := fun n =>
    (schwartzApproxRealVec (MeasureTheory.Lp.memLp h) n).toLp 2 μ
  let fN : Nat → L2Real d := fun n =>
    (schwartzApproxRealVec (MeasureTheory.Lp.memLp f) n).toLp 2 μ
  let F : PhaseSpace d → ℂ := stftRep h f
  let Fₙ : Nat → PhaseSpace d → ℂ := fun n => stftRep (hN n) (fN n)
  let Cₙ : Nat → ℝ := fun n => ‖fN n‖ * ‖hN n‖ + ‖f‖ * ‖h‖
  have hhN := schwartzApproxRealVec_toLp_tendsto h
  have hfN := schwartzApproxRealVec_toLp_tendsto f
  have hdiff :
      Tendsto
        (fun n : Nat => MeasureTheory.lpNorm (fun ξ : PhaseSpace d => Fₙ n ξ - F ξ) 2 μP)
        atTop (nhds 0) := by
    exact lpNorm_stftRep_tendsto_schwartzApprox h f
  have hC_tendsto :
      Tendsto Cₙ atTop (nhds (‖f‖ * ‖h‖ + ‖f‖ * ‖h‖)) := by
    have hprod : Tendsto (fun n : Nat => ‖fN n‖ * ‖hN n‖) atTop
        (nhds (‖f‖ * ‖h‖)) := hfN.norm.mul hhN.norm
    exact hprod.add tendsto_const_nhds
  have hCtendsto :
      Tendsto
        (fun n : Nat =>
          Cₙ n * MeasureTheory.lpNorm (fun ξ : PhaseSpace d => Fₙ n ξ - F ξ) 2 μP)
        atTop (nhds 0) := by simpa only [mul_zero] using hC_tendsto.mul hdiff
  refine squeeze_zero (fun _ => MeasureTheory.lpNorm_nonneg) ?_ hCtendsto
  intro n
  have hmemFn : MemLp (Fₙ n) 2 μP := stftRep_memLp (hN n) (fN n)
  have hmemF : MemLp F 2 μP := stftRep_memLp h f
  have hsum : lpNorm (Fₙ n) 2 μP + lpNorm F 2 μP ≤ Cₙ n :=
    add_le_add (lpNorm_stftRep_le (hN n) (fN n)) (lpNorm_stftRep_le h f)
  exact (lpNorm_norm_sq_sub_le hmemFn hmemF).trans
    (mul_le_mul_of_nonneg_right hsum lpNorm_nonneg)
private theorem norm_ambiguityRep_sub_le {d : Nat}
    (f₁ f₂ g₁ g₂ : L2Real d) (ξ : PhaseSpace d) :
    ‖ambiguityRep f₁ g₁ ξ - ambiguityRep f₂ g₂ ξ‖ ≤
      ‖f₁ - f₂‖ * ‖g₁‖ + ‖f₂‖ * ‖g₁ - g₂‖ := by
  let P := ((ContinuousLinearMap.mul ℂ ℂ).lpPairing
    (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) 2 2)
  let T₁ : L2Real d → L2Real d := fun f => translateL2 ((1 / 2 : ℝ) • ξ.1) f
  let T₂ : L2Real d → L2Real d := fun g =>
    modulateL2 ξ.2 (star (translateL2 (-((1 / 2 : ℝ) • ξ.1)) g))
  have hT₁_norm : ‖T₁ f₂‖ = ‖f₂‖ := norm_translateL2 _ f₂
  have hT₂_norm : ‖T₂ g₁‖ = ‖g₁‖ :=
    (norm_modulateL2 ξ.2 _).trans ((norm_star_L2 _).trans (norm_translateL2 _ g₁))
  have hT₁_sub_norm : ‖T₁ f₁ - T₁ f₂‖ = ‖f₁ - f₂‖ := by
    calc
      ‖T₁ f₁ - T₁ f₂‖ = dist (T₁ f₁) (T₁ f₂) := by rw [dist_eq_norm]
      _ = dist f₁ f₂ := dist_translateL2 _ f₁ f₂
      _ = ‖f₁ - f₂‖ := by rw [dist_eq_norm]
  have hT₂_sub_norm : ‖T₂ g₁ - T₂ g₂‖ = ‖g₁ - g₂‖ := by
    calc
      ‖T₂ g₁ - T₂ g₂‖ = dist (T₂ g₁) (T₂ g₂) := by rw [dist_eq_norm]
      _ = dist (star (translateL2 (-((1 / 2 : ℝ) • ξ.1)) g₁))
            (star (translateL2 (-((1 / 2 : ℝ) • ξ.1)) g₂)) := dist_modulateL2 ξ.2 _ _
      _ = dist (translateL2 (-((1 / 2 : ℝ) • ξ.1)) g₁)
            (translateL2 (-((1 / 2 : ℝ) • ξ.1)) g₂) := by rw [dist_star_L2]
      _ = dist g₁ g₂ := by rw [dist_translateL2]
      _ = ‖g₁ - g₂‖ := by rw [dist_eq_norm]
  calc
    ‖ambiguityRep f₁ g₁ ξ - ambiguityRep f₂ g₂ ξ‖ =
        ‖P (T₁ f₁) (T₂ g₁) - P (T₁ f₂) (T₂ g₂)‖ :=
      congrArg norm (congrArg₂ (fun a b : ℂ => a - b)
        (ambiguityRep_eq_lpPairing f₁ g₁ ξ) (ambiguityRep_eq_lpPairing f₂ g₂ ξ))
    _ ≤ ‖f₁ - f₂‖ * ‖g₁‖ + ‖f₂‖ * ‖g₁ - g₂‖ := by
      simpa only [hT₁_sub_norm, hT₂_norm, hT₁_norm, hT₂_sub_norm] using
        norm_bilinear_sub_le P (fun f g => lpPairing_mul_norm_le f g)
          (T₁ f₁) (T₁ f₂) (T₂ g₁) (T₂ g₂)
private theorem ambiguityRep_tendsto_schwartzApprox {d : Nat}
    (f : L2Real d) (ξ : PhaseSpace d) :
    Tendsto
      (fun n : Nat =>
        ambiguityRep
          ((schwartzApproxRealVec (MeasureTheory.Lp.memLp f) n).toLp 2
            (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
          ((schwartzApproxRealVec (MeasureTheory.Lp.memLp f) n).toLp 2
            (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) ξ)
      atTop (nhds (ambiguityRep f f ξ)) := by
  let μ : MeasureTheory.Measure (RealVec d) := MeasureTheory.volume
  let fN : Nat → L2Real d := fun n =>
    (schwartzApproxRealVec (MeasureTheory.Lp.memLp f) n).toLp 2 μ
  have hfN := schwartzApproxRealVec_toLp_tendsto f
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun _ => dist_nonneg) ?_ (cross_norm_bound_tendsto_zero hfN hfN)
  intro n
  rw [dist_eq_norm]
  exact norm_ambiguityRep_sub_le (fN n) f (fN n) f ξ
private lemma symplecticFourierRep_stft_sq_eq_iterated {d : Nat}
    (x ω : RealVec d)
    (hLp fLp : L2Real d)
    (hSphase :
      Integrable
        (fun η : PhaseSpace d =>
          ((‖stftRep hLp fLp η‖ ^ 2 : ℝ) : ℂ) *
            Complex.exp
              ((2 * Real.pi : ℂ) * Complex.I *
                (((inner ℝ η.2 x : ℝ) - (inner ℝ η.1 ω : ℝ) : ℝ) : ℂ)))
        ((MeasureTheory.volume : MeasureTheory.Measure (RealVec d)).prod
          (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))) :
    symplecticFourierRep
        (fun η : PhaseSpace d => ((‖stftRep hLp fLp η‖ ^ 2 : ℝ) : ℂ)) (x, ω) =
      ∫ y : RealVec d, ∫ η : RealVec d,
        ((‖stftRep hLp fLp (y, η)‖ ^ 2 : ℝ) : ℂ) *
          (modulationPhase ω y * modulationPhase (-x) η) := by
  simp only [symplecticFourierRep]
  rw [MeasureTheory.Measure.volume_eq_prod (RealVec d) (RealVec d),
    MeasureTheory.integral_prod _ hSphase]
  refine integral_congr_ae ?_
  filter_upwards with y
  refine integral_congr_ae ?_
  filter_upwards with η
  rw [symplecticFourier_phase_eq_modulationPhase x ω y η]
private lemma moyal_kernel_iterated_eq {d : Nat}
    (h f : SchwartzMap (RealVec d) ℂ) (x ω : RealVec d) (hLp fLp : L2Real d)
    (hhLp : hLp = h.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
    (hfLp : fLp = f.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
    (K : RealVec d → RealVec d → ℂ)
    (hKdef : K = fun y t =>
      (star (f t) * f (t + x)) *
        (h (t - y) * star (h (t + x - y))) * modulationPhase ω y)
    (hK : Integrable (Function.uncurry K)
      ((MeasureTheory.volume : MeasureTheory.Measure (RealVec d)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))) :
    ∫ y : RealVec d, ∫ t : RealVec d, K y t =
      ambiguityRep fLp fLp (x, ω) * star (ambiguityRep hLp hLp (x, ω)) := by
  subst hKdef hfLp
  calc
    ∫ y : RealVec d, ∫ t : RealVec d,
        (star (f t) * f (t + x)) *
          (h (t - y) * star (h (t + x - y))) * modulationPhase ω y
        = ∫ t : RealVec d, ∫ y : RealVec d,
            (star (f t) * f (t + x)) *
              (h (t - y) * star (h (t + x - y))) * modulationPhase ω y :=
          MeasureTheory.integral_integral_swap hK
    _ = ∫ t : RealVec d, (star (f t) * f (t + x)) *
          (modulationPhase ω (t + (1 / 2 : ℝ) • x) *
            star (ambiguityRep hLp hLp (x, ω))) := by
          refine integral_congr_ae ?_
          filter_upwards with t
          calc
            ∫ y : RealVec d,
                (star (f t) * f (t + x)) *
                  (h (t - y) * star (h (t + x - y))) * modulationPhase ω y
                = ∫ y : RealVec d, (star (f t) * f (t + x)) *
                    (h (t - y) * star (h (t + x - y)) * modulationPhase ω y) := by
                    refine integral_congr_ae ?_
                    filter_upwards with y
                    ac_rfl
            _ = (star (f t) * f (t + x)) *
                ∫ y : RealVec d,
                  h (t - y) * star (h (t + x - y)) * modulationPhase ω y := by
                simpa only [RCLike.star_def, mul_assoc] using
                  (MeasureTheory.integral_const_mul
                    (r := star (f t) * f (t + x))
                    (f := fun y : RealVec d =>
                      h (t - y) * star (h (t + x - y)) * modulationPhase ω y))
            _ = (star (f t) * f (t + x)) *
                (modulationPhase ω (t + (1 / 2 : ℝ) • x) *
                  star (ambiguityRep hLp hLp (x, ω))) := by
                rw [integral_window_autocorr_phase_schwartz_realVec h t x ω, ← hhLp]
    _ = star (ambiguityRep hLp hLp (x, ω)) *
          ∫ t : RealVec d,
            (star (f t) * f (t + x)) * modulationPhase ω (t + (1 / 2 : ℝ) • x) := by
          calc
            ∫ t : RealVec d, (star (f t) * f (t + x)) *
                (modulationPhase ω (t + (1 / 2 : ℝ) • x) *
                  star (ambiguityRep hLp hLp (x, ω)))
                = ∫ t : RealVec d, star (ambiguityRep hLp hLp (x, ω)) *
                    ((star (f t) * f (t + x)) *
                      modulationPhase ω (t + (1 / 2 : ℝ) • x) ) := by
                    refine integral_congr_ae ?_
                    filter_upwards with t
                    ac_rfl
            _ = star (ambiguityRep hLp hLp (x, ω)) *
                ∫ t : RealVec d,
                  (star (f t) * f (t + x)) *
                    modulationPhase ω (t + (1 / 2 : ℝ) • x) := by
                simpa only [RCLike.star_def, one_div, mul_assoc] using
                  (MeasureTheory.integral_const_mul
                    (r := star (ambiguityRep hLp hLp (x, ω)))
                    (f := fun t : RealVec d =>
                      (star (f t) * f (t + x)) *
                        modulationPhase ω (t + (1 / 2 : ℝ) • x)))
    _ = star (ambiguityRep hLp hLp (x, ω)) *
          ambiguityRep (f.toLp 2 MeasureTheory.volume)
            (f.toLp 2 MeasureTheory.volume) (x, ω) := by
          rw [integral_signal_autocorr_phase_schwartz_realVec f x ω]
    _ = ambiguityRep (f.toLp 2 MeasureTheory.volume)
          (f.toLp 2 MeasureTheory.volume) (x, ω) *
          star (ambiguityRep hLp hLp (x, ω)) := by ring
private lemma moyal_slice_collapse {d : Nat}
    (h f : SchwartzMap (RealVec d) ℂ) (x ω : RealVec d)
    (hLp fLp : L2Real d)
    (hhLp : hLp = h.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
    (hfLp : fLp = f.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
    (K : RealVec d → RealVec d → ℂ)
    (hKdef : K = fun y t =>
      (star (f t) * f (t + x)) *
        (h (t - y) * star (h (t + x - y))) * modulationPhase ω y) :
    ∫ y : RealVec d, ∫ η : RealVec d,
        ((‖stftRep hLp fLp (y, η)‖ ^ 2 : ℝ) : ℂ) *
          (modulationPhase ω y * modulationPhase (-x) η) =
      ∫ y : RealVec d, ∫ t : RealVec d, K y t := by
  subst hhLp hfLp hKdef
  refine integral_congr_ae ?_
  filter_upwards with y
  calc
    ∫ η : RealVec d,
        ((‖stftRep (h.toLp 2 MeasureTheory.volume) (f.toLp 2 MeasureTheory.volume)
          (y, η)‖ ^ 2 : ℝ) : ℂ) *
          (modulationPhase ω y * modulationPhase (-x) η)
        = ∫ η : RealVec d, modulationPhase ω y *
            (((‖stftRep (h.toLp 2 MeasureTheory.volume)
              (f.toLp 2 MeasureTheory.volume) (y, η)‖ ^ 2 : ℝ) : ℂ) *
              modulationPhase (-x) η) := by
              refine integral_congr_ae ?_
              filter_upwards with η
              ac_rfl
    _ = modulationPhase ω y *
        ∫ η : RealVec d,
          ((‖stftRep (h.toLp 2 MeasureTheory.volume)
            (f.toLp 2 MeasureTheory.volume) (y, η)‖ ^ 2 : ℝ) : ℂ) *
            modulationPhase (-x) η :=
          MeasureTheory.integral_const_mul _ _
    _ = modulationPhase ω y *
        ∫ t : RealVec d, star (stftSliceSchwartz h f y t) *
          stftSliceSchwartz h f y (t + x) := by
          rw [integral_stftRep_sq_phase_slice_schwartz h f y x]
    _ = ∫ t : RealVec d, modulationPhase ω y *
          (star (stftSliceSchwartz h f y t) *
            stftSliceSchwartz h f y (t + x)) := by
          simpa only [stftSliceSchwartz_apply, RCLike.star_def, star_mul',
            RingHomCompTriple.comp_apply, RingHom.id_apply, mul_assoc] using
            (MeasureTheory.integral_const_mul
              (r := modulationPhase ω y)
              (f := fun t : RealVec d =>
                star (stftSliceSchwartz h f y t) *
                  stftSliceSchwartz h f y (t + x))).symm
    _ = ∫ t : RealVec d,
          (star (f t) * f (t + x)) *
            (h (t - y) * star (h (t + x - y))) * modulationPhase ω y := by
          refine integral_congr_ae ?_
          filter_upwards with t
          simp only [stftSliceSchwartz_apply, star_mul, star_star]
          ac_rfl
private theorem symplecticFourier_stft_sq_schwartz_realVec {d : Nat}
    (h f : SchwartzMap (RealVec d) ℂ) (x ω : RealVec d) :
    symplecticFourierRep
        (fun η : PhaseSpace d =>
          ((‖stftRep
            (h.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
            (f.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) η‖ ^ 2 : ℝ) :
            ℂ))
        (x, ω) =
      ambiguityRep
        (f.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
        (f.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) (x, ω) *
        star (ambiguityRep
          (h.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
          (h.toLp 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) (x, ω)) := by
  let μ : MeasureTheory.Measure (RealVec d) := MeasureTheory.volume
  let hLp : L2Real d := h.toLp 2 μ
  let fLp : L2Real d := f.toLp 2 μ
  change
    symplecticFourierRep
        (fun η : PhaseSpace d => ((‖stftRep hLp fLp η‖ ^ 2 : ℝ) : ℂ)) (x, ω) =
      ambiguityRep fLp fLp (x, ω) * star (ambiguityRep hLp hLp (x, ω))
  let S : PhaseSpace d → ℂ := fun η => ((‖stftRep hLp fLp η‖ ^ 2 : ℝ) : ℂ)
  let phase : PhaseSpace d → ℂ := fun η =>
    Complex.exp
      ((2 * Real.pi : ℂ) * Complex.I *
        (((inner ℝ η.2 x : ℝ) - (inner ℝ η.1 ω : ℝ) : ℝ) : ℂ))
  let K : RealVec d → RealVec d → ℂ := fun y t =>
    (star (f t) * f (t + x)) *
      (h (t - y) * star (h (t + x - y))) *
      modulationPhase ω y
  let G : RealVec d × RealVec d → ℂ := fun p =>
    ((star (f p.1) * f (p.1 + x)) *
      (h (p.1 - p.2) * star (h (p.1 + x - p.2)))) *
      modulationPhase ω p.2
  have hS : Integrable S (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)) := by
    simpa only [Complex.ofReal_pow, S, hLp, fLp, μ] using
      stftRep_sq_complex_integrable_schwartz_realVec h f
  have hphase_meas :
      AEStronglyMeasurable phase
        (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)) :=
    (by fun_prop : Measurable phase).aestronglyMeasurable
  have hphase_bound :
      ∀ᵐ η : PhaseSpace d ∂(MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)),
        ‖phase η‖ ≤ (1 : ℝ) := by
    filter_upwards with η
    simpa only [Complex.ofReal_sub, phase] using le_of_eq (symplecticFourierPhase_norm η (x, ω))
  have hSphase :=
    hS.mul_bdd hphase_meas hphase_bound
  have hmod_meas :
      AEStronglyMeasurable (fun p : RealVec d × RealVec d => modulationPhase ω p.2)
        (μ.prod μ) := by
    exact
      (by
        unfold modulationPhase
        fun_prop :
        Measurable fun p : RealVec d × RealVec d => modulationPhase ω p.2).aestronglyMeasurable
  have hmod_bound :
      ∀ᵐ p : RealVec d × RealVec d ∂(μ.prod μ), ‖modulationPhase ω p.2‖ ≤ (1 : ℝ) := by
    filter_upwards with p
    simpa using le_of_eq (modulationPhase_norm ω p.2)
  have hG : Integrable G (μ.prod μ) := by
    have hbase :
        Integrable
          (fun p : RealVec d × RealVec d =>
            (star (f p.1) * f (p.1 + x)) *
              (h (p.1 - p.2) * star (h (p.1 + x - p.2))))
          (μ.prod μ) := by simpa only [RCLike.star_def, μ] using
            autocorr_kernel_integrable_schwartz_realVec f h x
    simpa only [RCLike.star_def, mul_assoc, G] using hbase.mul_bdd hmod_meas hmod_bound
  have hK : Integrable (Function.uncurry K) (μ.prod μ) := by
    refine hG.swap.congr ?_
    filter_upwards with p
    simp only [K, G, Function.uncurry, Function.comp_apply, Prod.fst_swap, Prod.snd_swap, mul_assoc]
  have hSphase_prod := hSphase
  calc
    symplecticFourierRep
        (fun η : PhaseSpace d => ((‖stftRep hLp fLp η‖ ^ 2 : ℝ) : ℂ)) (x, ω)
        = ∫ y : RealVec d, ∫ η : RealVec d,
            ((‖stftRep hLp fLp (y, η)‖ ^ 2 : ℝ) : ℂ) *
              (modulationPhase ω y * modulationPhase (-x) η) :=
          symplecticFourierRep_stft_sq_eq_iterated x ω hLp fLp hSphase_prod
    _ = ∫ y : RealVec d, ∫ t : RealVec d, K y t :=
          moyal_slice_collapse h f x ω hLp fLp rfl rfl K rfl
    _ = ambiguityRep fLp fLp (x, ω) * star (ambiguityRep hLp hLp (x, ω)) :=
          moyal_kernel_iterated_eq h f x ω hLp fLp rfl rfl K rfl hK
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
theorem _root_.solution
    {d : Nat} (h f : L2Real d) (ξ : PhaseSpace d) :
    symplecticFourierRep
        (fun η : PhaseSpace d => ((‖stftRep h f η‖ ^ 2 : ℝ) : ℂ)) ξ =
      ambiguityRep f f ξ * star (ambiguityRep h h ξ) := by
  let μ : MeasureTheory.Measure (RealVec d) := MeasureTheory.volume
  let μP : MeasureTheory.Measure (PhaseSpace d) := MeasureTheory.volume
  let hN : Nat → L2Real d := fun n =>
    (schwartzApproxRealVec (MeasureTheory.Lp.memLp h) n).toLp 2 μ
  let fN : Nat → L2Real d := fun n =>
    (schwartzApproxRealVec (MeasureTheory.Lp.memLp f) n).toLp 2 μ
  let G : PhaseSpace d → ℂ := fun η => ((‖stftRep h f η‖ ^ 2 : ℝ) : ℂ)
  let Gₙ : Nat → PhaseSpace d → ℂ := fun n η => ((‖stftRep (hN n) (fN n) η‖ ^ 2 : ℝ) : ℂ)
  let A : ℂ := ambiguityRep f f ξ * star (ambiguityRep h h ξ)
  let Aₙ : Nat → ℂ := fun n => ambiguityRep (fN n) (fN n) ξ *
    star (ambiguityRep (hN n) (hN n) ξ)
  have hG : Integrable G μP := by exact stftRep_sq_complex_integrable h f
  have hGₙ : ∀ n : Nat, Integrable (Gₙ n) μP := by
    intro n
    exact
      stftRep_sq_complex_integrable_schwartz_realVec
        (schwartzApproxRealVec (MeasureTheory.Lp.memLp h) n)
        (schwartzApproxRealVec (MeasureTheory.Lp.memLp f) n)
  have hLp :
      Tendsto
        (fun n : Nat => MeasureTheory.lpNorm (fun η : PhaseSpace d => Gₙ n η - G η) 1 μP)
        atTop (nhds 0) := by
    exact lpNorm_stftRep_sq_sub_tendsto_zero h f
  have hfAmb :
      Tendsto (fun n : Nat => ambiguityRep (fN n) (fN n) ξ) atTop
        (nhds (ambiguityRep f f ξ)) := by
    exact ambiguityRep_tendsto_schwartzApprox f ξ
  have hhAmb :
      Tendsto (fun n : Nat => ambiguityRep (hN n) (hN n) ξ) atTop
        (nhds (ambiguityRep h h ξ)) := by
    exact ambiguityRep_tendsto_schwartzApprox h ξ
  have hA : Tendsto Aₙ atTop (nhds A) := by
    have hhAmbStar :
        Tendsto (fun n : Nat => star (ambiguityRep (hN n) (hN n) ξ)) atTop
          (nhds (star (ambiguityRep h h ξ))) := hhAmb.star
    exact hfAmb.mul hhAmbStar
  have hEq : ∀ n : Nat, symplecticFourierRep (Gₙ n) ξ = Aₙ n := by
    intro n
    exact
      symplecticFourier_stft_sq_schwartz_realVec
        (schwartzApproxRealVec (MeasureTheory.Lp.memLp h) n)
        (schwartzApproxRealVec (MeasureTheory.Lp.memLp f) n) ξ.1 ξ.2
  exact
    symplecticFourierRep_eq_of_lpNorm_one_approx
      (G := G) (Gₙ := Gₙ) (A := A) (Aₙ := Aₙ) hG hGₙ hLp hA ξ hEq
end DimdPolyLEAN
