-- Prove2me | solution 1 for DKFAsymptotics.C4
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-15T20:58:58.975951+00:00
-- url     : https://prove2.me/submissions/19e782d6-3afb-494c-b843-f1067256c895

/- Standalone direct proof of DKFAsymptotics.C4.
All helper proofs are included; no mission theorem is imported. -/
import Definitions.Def_DKFAsymptotics_Assumptions
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Analysis.Matrix.Order
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

set_option autoImplicit false
noncomputable section

-- Solutions.DensityTools
section
open MeasureTheory Filter Matrix
open scoped Topology ENNReal

namespace DKFAsymptotics.Proof

variable {d : ℕ}

theorem isPDF_congr {f g : Density d} (h : f =ᵐ[volume] g) :
    IsPDF f ↔ IsPDF g := by
  unfold IsPDF
  constructor
  · rintro ⟨hp, hi, hn⟩
    exact ⟨by filter_upwards [hp, h] with z hz he; exact he ▸ hz, hi.congr h, (integral_congr_ae h).symm.trans hn⟩
  · rintro ⟨hp, hi, hn⟩
    exact ⟨by filter_upwards [hp, h] with z hz he; exact he.symm ▸ hz, hi.congr h.symm, (integral_congr_ae h).trans hn⟩

theorem densityMeasure_congr {f g : Density d} (h : f =ᵐ[volume] g) :
    densityMeasure f = densityMeasure g := by
  apply withDensity_congr_ae
  filter_upwards [h] with z hz using congrArg ENNReal.ofReal hz

theorem l1Norm_congr {f g : Density d} (h : f =ᵐ[volume] g) :
    l1Norm f = l1Norm g := by
  apply lintegral_congr_ae
  filter_upwards [h] with z hz using congrArg (fun r => ENNReal.ofReal |r|) hz

theorem weakly_congr {f g : ℕ+ → Density d} {P : Measure (State d)}
    (h : ∀ n, f n =ᵐ[volume] g n) : Weakly f P ↔ Weakly g P := by
  have he : ∀ n, densityMeasure (f n) = densityMeasure (g n) :=
    fun n => densityMeasure_congr (h n)
  simp only [Weakly, he]

theorem predictDensity_congr (M : Model d) {s s' : Density d}
    (hs : s =ᵐ[volume] s') : predictDensity M s = predictDensity M s' := by
  funext z
  apply integral_congr_ae
  filter_upwards [hs] with y hy using congrArg (transition M y z * ·) hy

theorem updateWeight_congr (M : Model d) {s s' u u' : Density d}
    (hs : s =ᵐ[volume] s') (hu : u =ᵐ[volume] u') :
    updateWeight M s u =ᵐ[volume] updateWeight M s' u' := by
  have hp := predictDensity_congr M hs
  filter_upwards [hu] with z hz
  simp only [updateWeight, hz, hp]

theorem updateDefined_congr (M : Model d) {s s' u u' : Density d}
    (hs : s =ᵐ[volume] s') (hu : u =ᵐ[volume] u') :
    UpdateDefined M s u ↔ UpdateDefined M s' u' := by
  have he := updateWeight_congr M hs hu
  have hn := l1Norm_congr he
  unfold UpdateDefined
  rw [hn]
  exact and_congr_left (fun _ => ⟨fun h => h.congr he, fun h => h.congr he.symm⟩)

theorem updateDensity_congr (M : Model d) {s s' u u' : Density d}
    (hs : s =ᵐ[volume] s') (hu : u =ᵐ[volume] u') :
    updateDensity M s u =ᵐ[volume] updateDensity M s' u' := by
  have he := updateWeight_congr M hs hu
  have hn := l1Norm_congr he
  filter_upwards [he] with z hz
  simp only [updateDensity, hz, hn]

theorem isGaussianPDF_congr {f g : Density d} (h : f =ᵐ[volume] g) :
    IsGaussianPDF f ↔ IsGaussianPDF g := by
  constructor
  · rintro ⟨hf, m, C, hC, he⟩
    exact ⟨(isPDF_congr h).mp hf, m, C, hC, h.symm.trans he⟩
  · rintro ⟨hg, m, C, hC, he⟩
    exact ⟨(isPDF_congr h).mpr hg, m, C, hC, h.trans he⟩

theorem isProbabilityMeasure_densityMeasure {f : Density d} (hf : IsPDF f) :
    IsProbabilityMeasure (densityMeasure f) := by
  constructor
  rw [densityMeasure, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal hf.2.1 hf.1, hf.2.2, ENNReal.ofReal_one]

def densityProbabilityMeasure {f : Density d} (hf : IsPDF f) :
    ProbabilityMeasure (State d) := ⟨densityMeasure f, isProbabilityMeasure_densityMeasure hf⟩

theorem weakly_iff_tendsto {f : ℕ+ → Density d} (hf : ∀ n, IsPDF (f n))
    (P : ProbabilityMeasure (State d)) :
    Weakly f P ↔ Tendsto (fun n => densityProbabilityMeasure (hf n)) atTop (𝓝 P) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  rfl

theorem integral_densityMeasure {f : Density d} (hf : IsPDF f)
    (g : State d → ℝ) :
    (∫ z, g z ∂densityMeasure f) = ∫ z, f z * g z ∂volume := by
  rw [densityMeasure, integral_withDensity_eq_integral_toReal_smul₀
    hf.2.1.aemeasurable.ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [hf.1] with z hz
  simp [ENNReal.toReal_ofReal hz]

theorem l1Norm_toReal {f : Density d} (hf : AEStronglyMeasurable f volume) :
    (l1Norm f).toReal = ∫ z, ‖f z‖ ∂volume := by
  rw [integral_norm_eq_lintegral_enorm hf]
  simp only [l1Norm, ← ofReal_norm, Real.norm_eq_abs]

theorem bounded_test_integrable {f : Density d} (hf : Integrable f volume)
    (g : BoundedContinuousFunction (State d) ℝ) :
    Integrable (fun z => f z * g z) volume :=
  hf.mul_bdd g.continuous.aestronglyMeasurable (ae_of_all _ g.norm_coe_le_norm)

/-- The estimate used in the first two sentences of the proof of Theorem 2. -/
theorem integral_density_difference_le {f f' : Density d}
    (hf : IsPDF f) (hf' : IsPDF f')
    (g : BoundedContinuousFunction (State d) ℝ) :
    ‖(∫ z, g z ∂densityMeasure f) - (∫ z, g z ∂densityMeasure f')‖ ≤
      ‖g‖ * (l1Distance f f').toReal := by
  rw [integral_densityMeasure hf, integral_densityMeasure hf',
    ← integral_sub (bounded_test_integrable hf.2.1 g)
      (bounded_test_integrable hf'.2.1 g)]
  calc
    _ ≤ ∫ z, ‖g‖ * ‖f z - f' z‖ ∂volume := by
      apply norm_integral_le_of_norm_le ((hf.2.1.sub hf'.2.1).norm.const_mul ‖g‖)
      filter_upwards [] with z
      rw [← sub_mul, norm_mul]
      exact (mul_le_mul_of_nonneg_left (g.norm_coe_le_norm z) (norm_nonneg _)).trans_eq
        (mul_comm _ _)
    _ = ‖g‖ * (l1Distance f f').toReal := by
      rw [integral_const_mul, l1Distance, l1Norm_toReal (hf.2.1.sub hf'.2.1).1]
      rfl

theorem weakly_of_l1Distance {f f' : ℕ+ → Density d} {P : Measure (State d)}
    (hf : ∀ n, IsPDF (f n)) (hf' : ∀ n, IsPDF (f' n))
    (hw : Weakly f P)
    (hl1 : Tendsto (fun n => l1Distance (f n) (f' n)) atTop (𝓝 0)) :
    Weakly f' P := by
  intro g
  have hreal : Tendsto (fun n => (l1Distance (f n) (f' n)).toReal) atTop (𝓝 0) := by
    simpa only [ENNReal.toReal_zero, Function.comp_def] using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hl1
  have hdiff : Tendsto (fun n => (∫ z, g z ∂densityMeasure (f n)) -
      (∫ z, g z ∂densityMeasure (f' n))) atTop (𝓝 0) :=
    squeeze_zero_norm (fun n => integral_density_difference_le (hf n) (hf' n) g)
      (by simpa using hreal.const_mul ‖g‖)
  simpa only [sub_sub_cancel, sub_zero] using (hw g).sub hdiff

end DKFAsymptotics.Proof
end

-- Solutions.C1C2
section
open MeasureTheory Filter Matrix
open scoped Topology ENNReal

namespace DKFAsymptotics.Proof

theorem C1 {d : ℕ} [NeZero d] (M : Model d) (D : Problem M)
    (h : Assumptions M D) : Weakly D.s' D.P :=
  weakly_of_l1Distance D.s_pdf (fun n => (D.s'_gaussian n).1) h.A1 h.A2

theorem C2 {d : ℕ} [NeZero d] (M : Model d) (D : Problem M)
    (h : Assumptions M D) : Weakly D.u' (Measure.dirac D.b) :=
  weakly_of_l1Distance D.u_pdf (fun n => (D.u'_gaussian n).1) h.A3 h.A4

end DKFAsymptotics.Proof
end

-- Solutions.GaussianBasics
section
open MeasureTheory Filter Matrix
open scoped Topology ENNReal

namespace DKFAsymptotics.Proof

variable {d : ℕ}

theorem gaussianPDF_pos (m : State d) {C : Covariance d} (hC : C.PosDef)
    (z : State d) : 0 < gaussianPDF m C z := by
  unfold gaussianPDF
  have : 0 < (2 * Real.pi) ^ d * C.det :=
    mul_pos (pow_pos (mul_pos (by norm_num) Real.pi_pos) _) hC.det_pos
  exact mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr this)) (Real.exp_pos _)

theorem gaussianPDF_continuous (m : State d) (C : Covariance d) :
    Continuous (gaussianPDF m C) := by
  unfold gaussianPDF dotProduct mulVec
  fun_prop

theorem gaussianPDF_le (m : State d) {C : Covariance d} (hC : C.PosDef)
    (z : State d) : gaussianPDF m C z ≤ gaussianPDF 0 C 0 := by
  have hq : 0 ≤ (z - m) ⬝ᵥ (C⁻¹ *ᵥ (z - m)) := by
    simpa using hC.posSemidef.inv.dotProduct_mulVec_nonneg (z - m)
  simp only [gaussianPDF, sub_self, mulVec_zero, dotProduct_zero, neg_zero, zero_div,
    Real.exp_zero, mul_one]
  apply mul_le_of_le_one_right (inv_nonneg.mpr (Real.sqrt_nonneg _))
  exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hq) (by norm_num))

def gaussianBCF (m : State d) {C : Covariance d} (hC : C.PosDef) :
    BoundedContinuousFunction (State d) ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (gaussianPDF m C)
    (gaussianPDF_continuous m C) (gaussianPDF 0 C 0) (fun z => by
      rw [Real.norm_eq_abs, abs_of_pos (gaussianPDF_pos m hC z)]
      exact gaussianPDF_le m hC z)

theorem transition_pos (M : Model d) (y z : State d) : 0 < transition M y z :=
  gaussianPDF_pos _ M.Γ_posDef z

theorem transition_le (M : Model d) (y z : State d) :
    transition M y z ≤ gaussianPDF 0 M.Γ 0 :=
  gaussianPDF_le _ M.Γ_posDef z

theorem transition_continuous (M : Model d) :
    Continuous (fun yz : State d × State d => transition M yz.1 yz.2) := by
  unfold transition gaussianPDF dotProduct mulVec
  fun_prop

theorem predictedCovariance_posDef (M : Model d) {V : Covariance d} (hV : V.PosSemidef) :
    (predictedCovariance M V).PosDef := by
  apply Matrix.PosDef.posSemidef_add _ M.Γ_posDef
  simpa only [conjTranspose_eq_transpose_of_trivial] using hV.mul_mul_conjTranspose_same M.A

end DKFAsymptotics.Proof
end

-- Solutions.KernelTools
section
open MeasureTheory Filter Matrix
open scoped Topology ENNReal

namespace DKFAsymptotics.Proof

variable {d : ℕ}

theorem predict_integrable (M : Model d) {s : Density d} (hs : Integrable s volume)
    (z : State d) : Integrable (fun y => transition M y z * s y) volume := by
  apply hs.bdd_mul
  · exact (transition_continuous M |>.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  · filter_upwards [] with y
    rw [Real.norm_eq_abs, abs_of_pos (transition_pos M y z)]
    exact transition_le M y z

theorem predict_nonneg (M : Model d) {s : Density d}
    (hs : ∀ᵐ y ∂volume, 0 ≤ s y) (z : State d) : 0 ≤ predictDensity M s z := by
  apply integral_nonneg_of_ae
  filter_upwards [hs] with y hy using mul_nonneg (transition_pos M y z).le hy

theorem predict_norm_le (M : Model d) {s : Density d} (hs : Integrable s volume)
    (z : State d) : ‖predictDensity M s z‖ ≤ gaussianPDF 0 M.Γ 0 * (l1Norm s).toReal := by
  calc
    _ ≤ ∫ y, gaussianPDF 0 M.Γ 0 * ‖s y‖ ∂volume := by
      apply norm_integral_le_of_norm_le (hs.norm.const_mul _)
      filter_upwards [] with y
      rw [norm_mul, Real.norm_eq_abs (transition M y z), abs_of_pos (transition_pos M y z)]
      exact mul_le_mul_of_nonneg_right (transition_le M y z) (norm_nonneg _)
    _ = _ := by rw [integral_const_mul, l1Norm_toReal hs.1]

theorem predict_sub (M : Model d) {s s' : Density d}
    (hs : Integrable s volume) (hs' : Integrable s' volume) :
    predictDensity M (s - s') = predictDensity M s - predictDensity M s' := by
  funext z
  simp only [predictDensity, Pi.sub_apply, mul_sub]
  exact integral_sub (predict_integrable M hs z) (predict_integrable M hs' z)

theorem predict_difference_le (M : Model d) {s s' : Density d}
    (hs : Integrable s volume) (hs' : Integrable s' volume) (z : State d) :
    ‖predictDensity M s z - predictDensity M s' z‖ ≤
      gaussianPDF 0 M.Γ 0 * (l1Distance s s').toReal := by
  simpa only [predict_sub M hs hs', Pi.sub_apply, l1Distance] using
    predict_norm_le M (hs.sub hs') z

theorem predict_continuous (M : Model d) {s : Density d} (hs : Integrable s volume) :
    Continuous (predictDensity M s) := by
  apply continuous_of_dominated
    (bound := fun y => gaussianPDF 0 M.Γ 0 * ‖s y‖)
  · intro z
    exact (predict_integrable M hs z).1
  · intro z
    filter_upwards [] with y
    rw [norm_mul, Real.norm_eq_abs (transition M y z), abs_of_pos (transition_pos M y z)]
    exact mul_le_mul_of_nonneg_right (transition_le M y z) (norm_nonneg _)
  · exact hs.norm.const_mul _
  · filter_upwards [] with y
    exact ((gaussianPDF_continuous (M.A *ᵥ y) M.Γ).mul continuous_const)

theorem l1Norm_toReal_pdf {s : Density d} (hs : IsPDF s) : (l1Norm s).toReal = 1 := by
  rw [l1Norm_toReal hs.2.1.1]
  calc
    (∫ y, ‖s y‖ ∂volume) = ∫ y, s y ∂volume := by
      apply integral_congr_ae
      filter_upwards [hs.1] with y hy using Real.norm_of_nonneg hy
    _ = 1 := hs.2.2

theorem updateWeight_nonneg (M : Model d) {s u : Density d}
    (hs : IsPDF s) (hu : IsPDF u) : ∀ᵐ z ∂volume, 0 ≤ updateWeight M s u z := by
  filter_upwards [hu.1] with z hz
  exact div_nonneg (mul_nonneg hz (predict_nonneg M hs.1 z))
    (gaussianPDF_pos 0 M.S_posDef z).le

theorem normalized_isPDF {f : Density d}
    (hf : AEStronglyMeasurable f volume) (hn : ∀ᵐ z ∂volume, 0 ≤ f z)
    (hp : 0 < l1Norm f) (hfin : l1Norm f < ⊤) :
    IsPDF (fun z => f z / (l1Norm f).toReal) := by
  have hreal : 0 < (l1Norm f).toReal := ENNReal.toReal_pos hp.ne' hfin.ne
  have hi : Integrable f volume := by
    refine ⟨hf, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    exact hfin
  have he : ∫ z, f z ∂volume = (l1Norm f).toReal := by
    rw [l1Norm_toReal hf]
    apply integral_congr_ae
    filter_upwards [hn] with z hz using (Real.norm_of_nonneg hz).symm
  refine ⟨?_, hi.div_const _, ?_⟩
  · filter_upwards [hn] with z hz using div_nonneg hz hreal.le
  · rw [integral_div, he, div_self hreal.ne']

theorem updateDensity_isPDF (M : Model d) {s u : Density d}
    (hs : IsPDF s) (hu : IsPDF u) (hd : UpdateDefined M s u) :
    IsPDF (updateDensity M s u) :=
  normalized_isPDF hd.1 (updateWeight_nonneg M hs hu) hd.2.1 hd.2.2

end DKFAsymptotics.Proof
end

-- Solutions.QuadraticIntegral
section
/-
Quadratic Gaussian integration helpers adapted from Harry_Xu’s accepted Prove2Me proof:
https://prove2.me/theorems/bea02c80-f5c4-4a04-8431-0ba9ac10fe54
Submission 166b3e3d-2ca5-4b2a-ade4-cdfad74ab4e7.
The copied helpers are proved locally here; no external theorem axiom is assumed.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped MatrixOrder ENNReal

namespace DKFAsymptotics.Proof

theorem dot_mulVec_comm_of_isHermitian
    {d : ℕ} {K : Matrix (Fin d) (Fin d) ℝ}
    (hK : K.IsHermitian) (x y : Fin d → ℝ) :
    x ⬝ᵥ K *ᵥ y = y ⬝ᵥ K *ᵥ x := by
  simp only [dotProduct, Matrix.mulVec]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hsym : K j i = K i j := by
    have heq := congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => M i j) hK.eq
    simpa using heq
  rw [hsym]
  ring

theorem quadratic_completion
    {d : ℕ} {K : Matrix (Fin d) (Fin d) ℝ}
    (hK : K.PosDef) (S x : Fin d → ℝ) :
    x ⬝ᵥ S - 1 / 2 * (x ⬝ᵥ K *ᵥ x) =
      1 / 2 * (S ⬝ᵥ K⁻¹ *ᵥ S) -
        1 / 2 * ((x - K⁻¹ *ᵥ S) ⬝ᵥ K *ᵥ (x - K⁻¹ *ᵥ S)) := by
  have hunit : IsUnit K := hK.isUnit
  have hdetunit : IsUnit K.det :=
    (Matrix.isUnit_iff_isUnit_det K).mp hunit
  have hKS : K *ᵥ (K⁻¹ *ᵥ S) = S := by
    rw [mulVec_mulVec, mul_nonsing_inv K hdetunit]
    exact one_mulVec S
  have hcomm (u v : Fin d → ℝ) :
      u ⬝ᵥ K *ᵥ v = v ⬝ᵥ K *ᵥ u :=
    dot_mulVec_comm_of_isHermitian hK.isHermitian u v
  simp only [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct]
  rw [hKS, hcomm (K⁻¹ *ᵥ S) x, hKS,
    dotProduct_comm (K⁻¹ *ᵥ S) S]
  ring

theorem sqrt_mulVec_sq
    {d : ℕ} {K : Matrix (Fin d) (Fin d) ℝ}
    (hK : K.PosDef) (x : Fin d → ℝ) :
    x ⬝ᵥ K *ᵥ x =
      (CFC.sqrt K *ᵥ x) ⬝ᵥ (CFC.sqrt K *ᵥ x) := by
  let B := CFC.sqrt K
  have hBps : B.PosSemidef :=
    nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg K)
  have hBB : B * B = K :=
    CFC.sqrt_mul_sqrt_self K hK.posSemidef.nonneg
  have hxvec : x ᵥ* B = B *ᵥ x := by
    have heq := vecMul_conjTranspose B x
    rw [hBps.isHermitian.eq] at heq
    simpa [B] using heq
  calc
    x ⬝ᵥ K *ᵥ x = x ⬝ᵥ (B * B) *ᵥ x := by rw [hBB]
    _ = x ⬝ᵥ B *ᵥ (B *ᵥ x) := by rw [mulVec_mulVec]
    _ = (B *ᵥ x) ⬝ᵥ (B *ᵥ x) := by rw [dotProduct_mulVec, hxvec]

theorem isotropic_b_integrable {d : ℕ} {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : Fin d → ℝ => Real.exp (-b * (x ⬝ᵥ x))) := by
  have hcoord : ∀ i : Fin d,
      Integrable (fun r : ℝ => Real.exp (-b * r ^ 2)) :=
    fun _ => integrable_exp_neg_mul_sq hb
  have hprod := Integrable.fintype_prod hcoord
  have heq : (fun x : Fin d → ℝ => Real.exp (-b * (x ⬝ᵥ x))) =
      fun x => ∏ i : Fin d, Real.exp (-b * (x i) ^ 2) := by
    funext x
    simp only [dotProduct, ← Real.exp_sum]
    congr 2
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [heq, volume_pi]
  exact hprod

theorem isotropic_b_integral (d : ℕ) (b : ℝ) :
    (∫ x : Fin d → ℝ, Real.exp (-b * (x ⬝ᵥ x))) =
      (Real.sqrt (Real.pi / b)) ^ d := by
  have heq : (fun x : Fin d → ℝ => Real.exp (-b * (x ⬝ᵥ x))) =
      fun x => ∏ i : Fin d, Real.exp (-b * (x i) ^ 2) := by
    funext x
    simp only [dotProduct, ← Real.exp_sum]
    congr 2
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [heq, integral_fintype_prod_volume_eq_prod
    (f := fun (_ : Fin d) (r : ℝ) => Real.exp (-b * r ^ 2))]
  rw [show (∫ r : ℝ, Real.exp (-b * r ^ 2)) =
      Real.sqrt (Real.pi / b) by exact integral_gaussian b,
    Finset.prod_const]
  simp

theorem isotropic_integrable (d : ℕ) :
    Integrable (fun x : Fin d → ℝ => Real.exp (-1 / 2 * (x ⬝ᵥ x))) := by
  have hcoord : ∀ i : Fin d,
      Integrable (fun r : ℝ => Real.exp (-1 / 2 * r ^ 2)) :=
    fun _ => by
      simpa only [neg_div] using
        integrable_exp_neg_mul_sq (show 0 < (1 / 2 : ℝ) by norm_num)
  have hprod := Integrable.fintype_prod hcoord
  have heq : (fun x : Fin d → ℝ => Real.exp (-1 / 2 * (x ⬝ᵥ x))) =
      fun x => ∏ i : Fin d, Real.exp (-1 / 2 * (x i) ^ 2) := by
    funext x
    simp only [dotProduct, ← Real.exp_sum]
    congr 2
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [heq, volume_pi]
  exact hprod

theorem isotropic_integral (d : ℕ) :
    (∫ x : Fin d → ℝ, Real.exp (-1 / 2 * (x ⬝ᵥ x))) =
      (Real.sqrt (Real.pi / (1 / 2 : ℝ))) ^ d := by
  have heq : (fun x : Fin d → ℝ => Real.exp (-1 / 2 * (x ⬝ᵥ x))) =
      fun x => ∏ i : Fin d, Real.exp (-1 / 2 * (x i) ^ 2) := by
    funext x
    simp only [dotProduct, ← Real.exp_sum]
    congr 2
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [heq, integral_fintype_prod_volume_eq_prod
    (f := fun (_ : Fin d) (r : ℝ) => Real.exp (-1 / 2 * r ^ 2))]
  have hscalar :
      (∫ r : ℝ, Real.exp (-1 / 2 * r ^ 2)) =
        Real.sqrt (Real.pi / (1 / 2 : ℝ)) := by
    simpa only [neg_div] using integral_gaussian (1 / 2 : ℝ)
  rw [hscalar, Finset.prod_const]
  simp

theorem centered_quadratic_integrable
    {d : ℕ} {K : Matrix (Fin d) (Fin d) ℝ} (hK : K.PosDef) :
    Integrable (fun x : Fin d → ℝ =>
      Real.exp (-1 / 2 * (x ⬝ᵥ K *ᵥ x))) := by
  let B := CFC.sqrt K
  have hBdet : B.det ≠ 0 := by
    rw [hK.posSemidef.det_sqrt]
    simpa using (Real.sqrt_pos.2 hK.det_pos).ne'
  have hBmeas : Measurable (toLin' B) :=
    (LinearMap.continuous_on_pi (toLin' B)).measurable
  have hmap :
      Measure.map (toLin' B) volume =
        ENNReal.ofReal (abs B.det⁻¹) • volume :=
    Real.map_matrix_volume_pi_eq_smul_volume_pi hBdet
  have hgsmul :
      Integrable (fun y : Fin d → ℝ => Real.exp (-1 / 2 * (y ⬝ᵥ y)))
        (Measure.map (toLin' B) volume) := by
    rw [hmap]
    exact (isotropic_integrable d).smul_measure (by finiteness)
  have hcomp := hgsmul.comp_measurable hBmeas
  have hfun : (fun x : Fin d → ℝ => Real.exp (-1 / 2 * (x ⬝ᵥ K *ᵥ x))) =
      (fun y : Fin d → ℝ => Real.exp (-1 / 2 * (y ⬝ᵥ y))) ∘ (toLin' B) := by
    funext x
    simp only [B, Function.comp_apply, toLin'_apply, sqrt_mulVec_sq hK]
  rw [hfun]
  exact hcomp

theorem centered_quadratic_integral
    {d : ℕ} {K : Matrix (Fin d) (Fin d) ℝ} (hK : K.PosDef) :
    (∫ x : Fin d → ℝ, Real.exp (-1 / 2 * (x ⬝ᵥ K *ᵥ x))) =
      (ENNReal.ofReal (abs (CFC.sqrt K).det⁻¹)).toReal *
      (Real.sqrt (Real.pi / (1 / 2 : ℝ))) ^ d := by
  let B := CFC.sqrt K
  have hBdet : B.det ≠ 0 := by
    rw [hK.posSemidef.det_sqrt]
    simpa using (Real.sqrt_pos.2 hK.det_pos).ne'
  have hBmeas : Measurable (toLin' B) :=
    (LinearMap.continuous_on_pi (toLin' B)).measurable
  have hgsm :
      AEStronglyMeasurable
        (fun y : Fin d → ℝ => Real.exp (-1 / 2 * (y ⬝ᵥ y)))
        (Measure.map (toLin' B) volume) := by
    have hm : Measurable
        (fun y : Fin d → ℝ => Real.exp (-1 / 2 * (y ⬝ᵥ y))) := by
      simp only [dotProduct]
      fun_prop
    exact hm.aestronglyMeasurable
  have hi := integral_map hBmeas.aemeasurable hgsm
  rw [Real.map_matrix_volume_pi_eq_smul_volume_pi hBdet,
    integral_smul_measure] at hi
  rw [isotropic_integral d] at hi
  simpa only [B, toLin'_apply, sqrt_mulVec_sq hK, smul_eq_mul] using hi.symm

theorem shifted_quadratic_integrable
    {d : ℕ} {K : Matrix (Fin d) (Fin d) ℝ}
    (hK : K.PosDef) (S : Fin d → ℝ) :
    Integrable (fun x : Fin d → ℝ =>
      Real.exp (x ⬝ᵥ S - 1 / 2 * (x ⬝ᵥ K *ᵥ x))) := by
  let c := K⁻¹ *ᵥ S
  have heq :
      (fun x : Fin d → ℝ =>
        Real.exp (x ⬝ᵥ S - 1 / 2 * (x ⬝ᵥ K *ᵥ x))) =
      fun x =>
        Real.exp (1 / 2 * (S ⬝ᵥ K⁻¹ *ᵥ S)) *
          Real.exp (-1 / 2 * ((x - c) ⬝ᵥ K *ᵥ (x - c))) := by
    funext x
    rw [← Real.exp_add]
    congr 1
    convert quadratic_completion hK S x using 1
    simp only [c]
    ring
  rw [heq]
  exact ((centered_quadratic_integrable hK).comp_sub_right c).const_mul _

theorem shifted_quadratic_integral
    {d : ℕ} {K : Matrix (Fin d) (Fin d) ℝ}
    (hK : K.PosDef) (S : Fin d → ℝ) :
    (∫ x : Fin d → ℝ,
      Real.exp (x ⬝ᵥ S - 1 / 2 * (x ⬝ᵥ K *ᵥ x))) =
      Real.exp (1 / 2 * (S ⬝ᵥ K⁻¹ *ᵥ S)) *
        (ENNReal.ofReal (abs (CFC.sqrt K).det⁻¹)).toReal *
          (Real.sqrt (Real.pi / (1 / 2 : ℝ))) ^ d := by
  let c := K⁻¹ *ᵥ S
  have heq :
      (fun x : Fin d → ℝ =>
        Real.exp (x ⬝ᵥ S - 1 / 2 * (x ⬝ᵥ K *ᵥ x))) =
      fun x =>
        Real.exp (1 / 2 * (S ⬝ᵥ K⁻¹ *ᵥ S)) *
          Real.exp (-1 / 2 * ((x - c) ⬝ᵥ K *ᵥ (x - c))) := by
    funext x
    rw [← Real.exp_add]
    congr 1
    convert quadratic_completion hK S x using 1
    simp only [c]
    ring
  have htrans :
      (∫ a : Fin d → ℝ,
        Real.exp (-1 / 2 * ((a - c) ⬝ᵥ K *ᵥ (a - c)))) =
      ∫ a : Fin d → ℝ, Real.exp (-1 / 2 * (a ⬝ᵥ K *ᵥ a)) :=
    integral_sub_right_eq_self
      (fun a : Fin d → ℝ => Real.exp (-1 / 2 * (a ⬝ᵥ K *ᵥ a))) c
  rw [heq, integral_const_mul, htrans, centered_quadratic_integral hK]
  ring


end DKFAsymptotics.Proof
end

-- Solutions.GaussianIntegral
section
open MeasureTheory Filter Matrix
open scoped Topology ENNReal MatrixOrder

namespace DKFAsymptotics.Proof

variable {d : ℕ}

theorem gaussianPDF_integrable (m : State d) {C : Covariance d} (hC : C.PosDef) :
    Integrable (gaussianPDF m C) volume := by
  have he : gaussianPDF m C = fun z =>
      (Real.sqrt ((2 * Real.pi) ^ d * C.det))⁻¹ *
        Real.exp (-1 / 2 * ((z - m) ⬝ᵥ C⁻¹ *ᵥ (z - m))) := by
    funext z
    unfold gaussianPDF
    congr 2
    ring
  rw [he]
  exact ((centered_quadratic_integrable hC.inv).comp_sub_right m).const_mul _

theorem gaussianPDF_integral (m : State d) {C : Covariance d} (hC : C.PosDef) :
    (∫ z, gaussianPDF m C z ∂volume) = 1 := by
  have he : gaussianPDF m C = fun z =>
      (Real.sqrt ((2 * Real.pi) ^ d * C.det))⁻¹ *
        Real.exp (-1 / 2 * ((z - m) ⬝ᵥ C⁻¹ *ᵥ (z - m))) := by
    funext z
    unfold gaussianPDF
    congr 2
    ring
  rw [he, integral_const_mul, integral_sub_right_eq_self
    (fun z : State d => Real.exp (-1 / 2 * (z ⬝ᵥ C⁻¹ *ᵥ z))) m,
    centered_quadratic_integral hC.inv]
  have hdet : (CFC.sqrt C⁻¹).det = Real.sqrt C.det⁻¹ := by
    simpa only [det_nonsing_inv, Ring.inverse_eq_inv,
      RCLike.sqrt_of_nonneg (inv_nonneg.mpr hC.det_pos.le), RCLike.ofReal_real_eq_id,
      RCLike.re_to_real, id_eq] using
      hC.inv.posSemidef.det_sqrt
  rw [hdet, ENNReal.toReal_ofReal (abs_nonneg _), abs_of_pos (inv_pos.mpr
    (Real.sqrt_pos.mpr (inv_pos.mpr hC.det_pos)))]
  rw [Real.sqrt_inv, inv_inv]
  have hs : 0 < Real.sqrt ((2 * Real.pi) ^ d * C.det) := by
    apply Real.sqrt_pos.mpr
    exact mul_pos (pow_pos (mul_pos (by norm_num) Real.pi_pos) _) hC.det_pos
  have hnorm : Real.sqrt ((2 * Real.pi) ^ d * C.det) =
      Real.sqrt C.det * (Real.sqrt (Real.pi / (1 / 2 : ℝ))) ^ d := by
    have hbase : Real.pi / (1 / 2 : ℝ) = 2 * Real.pi := by ring
    rw [hbase]
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    have hp : (Real.sqrt (2 * Real.pi) ^ d) ^ 2 = (2 * Real.pi) ^ d := by
      rw [← pow_mul, Nat.mul_comm d 2, pow_mul, Real.sq_sqrt (by positivity)]
    rw [Real.sq_sqrt (mul_nonneg (pow_nonneg (by positivity) _) hC.det_pos.le),
      mul_pow (Real.sqrt C.det) (Real.sqrt (2 * Real.pi) ^ d) 2,
      Real.sq_sqrt hC.det_pos.le, hp]
    ring
  rw [← hnorm, inv_mul_cancel₀ hs.ne']

theorem gaussianPDF_isPDF (m : State d) {C : Covariance d} (hC : C.PosDef) :
    IsPDF (gaussianPDF m C) :=
  ⟨ae_of_all _ (fun z => (gaussianPDF_pos m hC z).le), gaussianPDF_integrable m hC,
    gaussianPDF_integral m hC⟩

end DKFAsymptotics.Proof
end

-- Solutions.PredictionMass
section
open MeasureTheory Filter Matrix
open scoped Topology ENNReal

namespace DKFAsymptotics.Proof

variable {d : ℕ}

theorem predict_joint_integrable (M : Model d) {s : Density d} (hs : IsPDF s) :
    Integrable (fun yz : State d × State d => transition M yz.1 yz.2 * s yz.1)
      (volume.prod volume) := by
  have hm : AEStronglyMeasurable
      (fun yz : State d × State d => transition M yz.1 yz.2 * s yz.1)
      (volume.prod volume) :=
    (transition_continuous M).aestronglyMeasurable.mul hs.2.1.1.comp_fst
  apply (integrable_prod_iff hm).mpr
  refine ⟨ae_of_all _ (fun y => (gaussianPDF_integrable (M.A *ᵥ y) M.Γ_posDef).mul_const (s y)), ?_⟩
  have he : (fun y => ∫ z, ‖transition M y z * s y‖ ∂volume) = fun y => ‖s y‖ := by
    funext y
    simp only [norm_mul]
    rw [integral_mul_const]
    have hz : (fun z => ‖transition M y z‖) = gaussianPDF (M.A *ᵥ y) M.Γ := by
      funext z
      exact Real.norm_of_nonneg (transition_pos M y z).le
    rw [hz, gaussianPDF_integral _ M.Γ_posDef, one_mul]
  rw [he]
  exact hs.2.1.norm

theorem predict_isPDF (M : Model d) {s : Density d} (hs : IsPDF s) :
    IsPDF (predictDensity M s) := by
  have hj := predict_joint_integrable M hs
  refine ⟨ae_of_all _ (predict_nonneg M hs.1), hj.integral_prod_right, ?_⟩
  change (∫ z, ∫ y, transition M y z * s y ∂volume ∂volume) = 1
  rw [← integral_integral_swap hj]
  have he : (fun y => ∫ z, transition M y z * s y ∂volume) = s := by
    funext y
    rw [integral_mul_const]
    change (∫ z, gaussianPDF (M.A *ᵥ y) M.Γ z ∂volume) * s y = s y
    rw [gaussianPDF_integral _ M.Γ_posDef, one_mul]
  rw [he, hs.2.2]

end DKFAsymptotics.Proof
end

-- Solutions.GaussianConvolution
section
open MeasureTheory Filter Matrix
open scoped Topology ENNReal MatrixOrder

namespace DKFAsymptotics.Proof
variable {d : ℕ}

theorem dot_transpose_mulVec (A : Covariance d) (x y : State d) :
    x ⬝ᵥ A.transpose *ᵥ y = (A *ᵥ x) ⬝ᵥ y := by
  rw [dotProduct_mulVec, vecMul_transpose]

theorem convolution_quadratic (A B H : Covariance d) (hB : B.IsHermitian)
    (r x : State d) :
    ((r - A *ᵥ x) ⬝ᵥ B *ᵥ (r - A *ᵥ x)) + x ⬝ᵥ H *ᵥ x =
      r ⬝ᵥ B *ᵥ r - 2 * (x ⬝ᵥ (A.transpose * B) *ᵥ r) +
        x ⬝ᵥ (H + A.transpose * B * A) *ᵥ x := by
  simp only [mulVec_sub, dotProduct_sub, sub_dotProduct, add_mulVec, dotProduct_add,
    ← mulVec_mulVec, dot_transpose_mulVec]
  rw [dot_mulVec_comm_of_isHermitian hB r (A *ᵥ x)]
  ring

theorem convolution_precision_pos (M : Model d) {V : Covariance d} (hV : V.PosDef) :
    (V⁻¹ + M.A.transpose * M.Γ⁻¹ * M.A).PosDef := by
  apply hV.inv.add_posSemidef
  simpa only [conjTranspose_eq_transpose_of_trivial] using
    M.Γ_posDef.posSemidef.inv.conjTranspose_mul_mul_same M.A

theorem predicted_inverse (M : Model d) {V : Covariance d} (hV : V.PosDef) :
    (predictedCovariance M V)⁻¹ = M.Γ⁻¹ -
      M.Γ⁻¹ * M.A * (V⁻¹ + M.A.transpose * M.Γ⁻¹ * M.A)⁻¹ * M.A.transpose * M.Γ⁻¹ := by
  simpa only [predictedCovariance, add_comm] using
    Matrix.add_mul_mul_inv_eq_sub M.Γ M.A V M.A.transpose M.Γ_posDef.isUnit hV.isUnit
      (convolution_precision_pos M hV).isUnit

theorem convolution_exponent (M : Model d) {V : Covariance d} (hV : V.PosDef)
    (r : State d) :
    -(r ⬝ᵥ M.Γ⁻¹ *ᵥ r) / 2 +
      1 / 2 * (((M.A.transpose * M.Γ⁻¹) *ᵥ r) ⬝ᵥ
        (V⁻¹ + M.A.transpose * M.Γ⁻¹ * M.A)⁻¹ *ᵥ ((M.A.transpose * M.Γ⁻¹) *ᵥ r)) =
      -(r ⬝ᵥ (predictedCovariance M V)⁻¹ *ᵥ r) / 2 := by
  rw [predicted_inverse M hV, sub_mulVec, dotProduct_sub]
  have he : r ⬝ᵥ
      (M.Γ⁻¹ * M.A * (V⁻¹ + M.A.transpose * M.Γ⁻¹ * M.A)⁻¹ * M.A.transpose * M.Γ⁻¹) *ᵥ r =
      (((M.A.transpose * M.Γ⁻¹) *ᵥ r) ⬝ᵥ
        (V⁻¹ + M.A.transpose * M.Γ⁻¹ * M.A)⁻¹ *ᵥ ((M.A.transpose * M.Γ⁻¹) *ᵥ r)) := by
    simp only [← mulVec_mulVec]
    rw [dot_mulVec_comm_of_isHermitian M.Γ_posDef.inv.isHermitian]
    rw [← dot_transpose_mulVec M.A, dotProduct_comm]
  rw [he]
  ring

theorem predict_gaussian_shape (M : Model d) (a : State d) {V : Covariance d}
    (hV : V.PosDef) : ∃ c : ℝ, ∀ z,
    predictDensity M (gaussianPDF a V) z =
      c * Real.exp (-((z - M.A *ᵥ a) ⬝ᵥ (predictedCovariance M V)⁻¹ *ᵥ
        (z - M.A *ᵥ a)) / 2) := by
  let K := V⁻¹ + M.A.transpose * M.Γ⁻¹ * M.A
  let J := (ENNReal.ofReal |(CFC.sqrt K).det⁻¹|).toReal *
    (Real.sqrt (Real.pi / (1 / 2 : ℝ))) ^ d
  let cΓ := (Real.sqrt ((2 * Real.pi) ^ d * M.Γ.det))⁻¹
  let cV := (Real.sqrt ((2 * Real.pi) ^ d * V.det))⁻¹
  refine ⟨cΓ * cV * J, ?_⟩
  intro z
  let r := z - M.A *ᵥ a
  let L := (M.A.transpose * M.Γ⁻¹) *ᵥ r
  have hK : K.PosDef := convolution_precision_pos M hV
  have hex (x : State d) :
      -((r - M.A *ᵥ x) ⬝ᵥ M.Γ⁻¹ *ᵥ (r - M.A *ᵥ x)) / 2 +
        -(x ⬝ᵥ V⁻¹ *ᵥ x) / 2 =
      -(r ⬝ᵥ M.Γ⁻¹ *ᵥ r) / 2 + (x ⬝ᵥ L - 1 / 2 * (x ⬝ᵥ K *ᵥ x)) := by
    have hq := convolution_quadratic M.A M.Γ⁻¹ V⁻¹ M.Γ_posDef.inv.isHermitian r x
    dsimp [K, L]
    linarith
  have hf (x : State d) :
      transition M (x + a) z * gaussianPDF a V (x + a) =
      (cΓ * cV * Real.exp (-(r ⬝ᵥ M.Γ⁻¹ *ᵥ r) / 2)) *
        Real.exp (x ⬝ᵥ L - 1 / 2 * (x ⬝ᵥ K *ᵥ x)) := by
    have hshift : z - M.A *ᵥ (x + a) = r - M.A *ᵥ x := by
      dsimp [r]
      rw [mulVec_add]
      abel
    simp only [transition, gaussianPDF, hshift, add_sub_cancel_right]
    change (cΓ * Real.exp _) * (cV * Real.exp _) = _
    calc
      _ = (cΓ * cV) * Real.exp
          (-((r - M.A *ᵥ x) ⬝ᵥ M.Γ⁻¹ *ᵥ (r - M.A *ᵥ x)) / 2 +
            -(x ⬝ᵥ V⁻¹ *ᵥ x) / 2) := by rw [Real.exp_add]; ring
      _ = _ := by rw [hex, Real.exp_add]; ring
  unfold predictDensity
  rw [← integral_add_right_eq_self
    (fun y => transition M y z * gaussianPDF a V y) a]
  simp_rw [hf]
  rw [integral_const_mul, shifted_quadratic_integral hK L]
  have he := convolution_exponent M hV r
  change -(r ⬝ᵥ M.Γ⁻¹ *ᵥ r) / 2 + 1 / 2 * (L ⬝ᵥ K⁻¹ *ᵥ L) = _ at he
  calc
    _ = (cΓ * cV * J) * Real.exp
        (-(r ⬝ᵥ M.Γ⁻¹ *ᵥ r) / 2 + 1 / 2 * (L ⬝ᵥ K⁻¹ *ᵥ L)) := by
      rw [Real.exp_add]
      dsimp [J]
      ring
    _ = _ := by rw [he]

theorem predict_gaussian (M : Model d) (a : State d) {V : Covariance d}
    (hV : V.PosDef) :
    predictDensity M (gaussianPDF a V) =
      gaussianPDF (M.A *ᵥ a) (predictedCovariance M V) := by
  obtain ⟨c, hc⟩ := predict_gaussian_shape M a hV
  have hG := predictedCovariance_posDef M hV.posSemidef
  let k := Real.sqrt ((2 * Real.pi) ^ d * (predictedCovariance M V).det)
  have hk : k ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr
    (mul_pos (pow_pos (by positivity) _) hG.det_pos))
  have he : predictDensity M (gaussianPDF a V) =
      fun z => (c * k) * gaussianPDF (M.A *ᵥ a) (predictedCovariance M V) z := by
    funext z
    rw [hc, gaussianPDF]
    dsimp [k] at hk ⊢
    field_simp [hk]
  have hi := (predict_isPDF M (gaussianPDF_isPDF a hV)).2.2
  rw [he, integral_const_mul, gaussianPDF_integral _ hG, mul_one] at hi
  rw [he, hi]
  simp

end DKFAsymptotics.Proof
end

-- Solutions.Normalization
section
open MeasureTheory Filter Matrix
open scoped Topology ENNReal
namespace DKFAsymptotics.Proof
variable {d : ℕ}

theorem l1Norm_eq_integral {f : Density d} (hi : Integrable f volume)
    (hn : ∀ᵐ z ∂volume, 0 ≤ f z) :
    l1Norm f = ENNReal.ofReal (∫ z, f z ∂volume) := by
  rw [ofReal_integral_eq_lintegral_ofReal hi hn]
  apply lintegral_congr_ae
  filter_upwards [hn] with z hz
  rw [abs_of_nonneg hz]

theorem normalize_proportional_pdf {f g : Density d} (hg : IsPDF g)
    {c : ℝ} (hc : 0 < c) (he : f = fun z => c * g z) :
    (AEStronglyMeasurable f volume ∧ 0 < l1Norm f ∧ l1Norm f < ⊤) ∧
    (fun z => f z / (l1Norm f).toReal) = g := by
  have hi : Integrable f volume := he ▸ hg.2.1.const_mul c
  have hn : ∀ᵐ z ∂volume, 0 ≤ f z := by
    rw [he]
    filter_upwards [hg.1] with z hz using mul_nonneg hc.le hz
  have hl : l1Norm f = ENNReal.ofReal c := by
    rw [l1Norm_eq_integral hi hn, he, integral_const_mul, hg.2.2, mul_one]
  refine ⟨⟨hi.1, ?_, ?_⟩, ?_⟩
  · rw [hl]
    exact ENNReal.ofReal_pos.mpr hc
  · rw [hl]
    exact ENNReal.ofReal_lt_top
  · funext z
    rw [hl, he, ENNReal.toReal_ofReal hc.le]
    exact mul_div_cancel_left₀ (g z) hc.ne'

end DKFAsymptotics.Proof
end

-- Solutions.GaussianUpdate
section
open MeasureTheory Filter Matrix
open scoped Topology ENNReal

namespace DKFAsymptotics.Proof
variable {d : ℕ}

theorem shifted_quadratic_expand {B : Covariance d} (hB : B.IsHermitian)
    (z b : State d) :
    (z - b) ⬝ᵥ B *ᵥ (z - b) = z ⬝ᵥ B *ᵥ z - 2 * (z ⬝ᵥ B *ᵥ b) + b ⬝ᵥ B *ᵥ b := by
  simp only [mulVec_sub, dotProduct_sub, sub_dotProduct]
  rw [dot_mulVec_comm_of_isHermitian hB b z]
  ring

theorem update_quadratic (B H R : Covariance d) (hB : B.IsHermitian)
    (hH : H.IsHermitian) (z a b : State d) :
    -((z - b) ⬝ᵥ B *ᵥ (z - b)) / 2 - ((z - a) ⬝ᵥ H *ᵥ (z - a)) / 2 +
      (z ⬝ᵥ R *ᵥ z) / 2 =
    -(b ⬝ᵥ B *ᵥ b) / 2 - (a ⬝ᵥ H *ᵥ a) / 2 +
      (z ⬝ᵥ (B *ᵥ b + H *ᵥ a) - 1 / 2 * (z ⬝ᵥ (B + H - R) *ᵥ z)) := by
  rw [shifted_quadratic_expand hB, shifted_quadratic_expand hH]
  simp only [dotProduct_add, sub_mulVec, add_mulVec, dotProduct_sub]
  ring

theorem gaussian_update_proportional (M : Model d) (a b : State d)
    {V U : Covariance d} (hV : V.PosDef) (hU : U.PosDef)
    (hd : ValidStep M ⟨a, V⟩ ⟨b, U⟩) :
    ∃ c : ℝ, 0 < c ∧ updateWeight M (gaussianPDF a V) (gaussianPDF b U) =
      fun z => c * gaussianPDF (dkfStep M ⟨a, V⟩ ⟨b, U⟩).mean
        (dkfStep M ⟨a, V⟩ ⟨b, U⟩).covariance z := by
  let G := predictedCovariance M V
  let K := updatePrecision M V U
  let T := K⁻¹
  let l := U⁻¹ *ᵥ b + G⁻¹ *ᵥ (M.A *ᵥ a)
  have hG : G.PosDef := predictedCovariance_posDef M hV.posSemidef
  have hT : T.PosDef := hd.2
  have hTi : T⁻¹ = K := Matrix.nonsing_inv_nonsing_inv K hd.1
  have hK : K.PosDef := hTi ▸ hT.inv
  let q := -(b ⬝ᵥ U⁻¹ *ᵥ b) / 2 - ((M.A *ᵥ a) ⬝ᵥ G⁻¹ *ᵥ (M.A *ᵥ a)) / 2 +
    1 / 2 * (l ⬝ᵥ T *ᵥ l)
  let kU := Real.sqrt ((2 * Real.pi) ^ d * U.det)
  let kG := Real.sqrt ((2 * Real.pi) ^ d * G.det)
  let kS := Real.sqrt ((2 * Real.pi) ^ d * M.S.det)
  let kT := Real.sqrt ((2 * Real.pi) ^ d * T.det)
  have hkU : 0 < kU := Real.sqrt_pos.mpr (mul_pos (pow_pos (by positivity) _) hU.det_pos)
  have hkG : 0 < kG := Real.sqrt_pos.mpr (mul_pos (pow_pos (by positivity) _) hG.det_pos)
  have hkS : 0 < kS := Real.sqrt_pos.mpr (mul_pos (pow_pos (by positivity) _) M.S_posDef.det_pos)
  have hkT : 0 < kT := Real.sqrt_pos.mpr (mul_pos (pow_pos (by positivity) _) hT.det_pos)
  refine ⟨kU⁻¹ * kG⁻¹ / kS⁻¹ * Real.exp q * kT, by positivity, ?_⟩
  funext z
  have hex :
      -((z - b) ⬝ᵥ U⁻¹ *ᵥ (z - b)) / 2 -
      ((z - M.A *ᵥ a) ⬝ᵥ G⁻¹ *ᵥ (z - M.A *ᵥ a)) / 2 +
      (z ⬝ᵥ M.S⁻¹ *ᵥ z) / 2 =
      q - ((z - T *ᵥ l) ⬝ᵥ T⁻¹ *ᵥ (z - T *ᵥ l)) / 2 := by
    rw [update_quadratic U⁻¹ G⁻¹ M.S⁻¹ hU.inv.isHermitian hG.inv.isHermitian]
    change _ + (z ⬝ᵥ l - 1 / 2 * (z ⬝ᵥ K *ᵥ z)) = _
    rw [quadratic_completion hK l z, hTi]
    dsimp [q, T]
    ring
  unfold updateWeight
  rw [predict_gaussian M a hV]
  change gaussianPDF b U z * gaussianPDF (M.A *ᵥ a) G z / gaussianPDF 0 M.S z =
    (kU⁻¹ * kG⁻¹ / kS⁻¹ * Real.exp q * kT) * gaussianPDF (T *ᵥ l) T z
  simp only [gaussianPDF, sub_zero]
  change (kU⁻¹ * Real.exp _) * (kG⁻¹ * Real.exp _) / (kS⁻¹ * Real.exp _) =
    _ * (kT⁻¹ * Real.exp _)
  have hneg : - (z ⬝ᵥ M.S⁻¹ *ᵥ z) / 2 = - ((z ⬝ᵥ M.S⁻¹ *ᵥ z) / 2) := by ring
  rw [hneg, Real.exp_neg]
  have he : Real.exp (-((z - b) ⬝ᵥ U⁻¹ *ᵥ (z - b)) / 2) *
      Real.exp (-((z - M.A *ᵥ a) ⬝ᵥ G⁻¹ *ᵥ (z - M.A *ᵥ a)) / 2) *
      Real.exp ((z ⬝ᵥ M.S⁻¹ *ᵥ z) / 2) =
      Real.exp q * Real.exp (-((z - T *ᵥ l) ⬝ᵥ T⁻¹ *ᵥ (z - T *ᵥ l)) / 2) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    linarith [hex]
  calc
    _ = (kU⁻¹ * kG⁻¹ / kS⁻¹) *
        (Real.exp (-((z - b) ⬝ᵥ U⁻¹ *ᵥ (z - b)) / 2) *
        Real.exp (-((z - M.A *ᵥ a) ⬝ᵥ G⁻¹ *ᵥ (z - M.A *ᵥ a)) / 2) *
        Real.exp ((z ⬝ᵥ M.S⁻¹ *ᵥ z) / 2)) := by field_simp
    _ = _ := by rw [he]; field_simp [hkT.ne']

theorem gaussian_update_exact (M : Model d) (a b : State d)
    {V U : Covariance d} (hV : V.PosDef) (hU : U.PosDef)
    (hd : ValidStep M ⟨a, V⟩ ⟨b, U⟩) :
    UpdateDefined M (gaussianPDF a V) (gaussianPDF b U) ∧
    (∀ z, updateDensity M (gaussianPDF a V) (gaussianPDF b U) z =
      gaussianPDF (dkfStep M ⟨a, V⟩ ⟨b, U⟩).mean
        (dkfStep M ⟨a, V⟩ ⟨b, U⟩).covariance z) ∧
    IsPDF (updateDensity M (gaussianPDF a V) (gaussianPDF b U)) := by
  obtain ⟨c, hc, he⟩ := gaussian_update_proportional M a b hV hU hd
  have hg := gaussianPDF_isPDF (dkfStep M ⟨a, V⟩ ⟨b, U⟩).mean hd.2
  obtain ⟨hn, heq⟩ := normalize_proportional_pdf hg hc he
  change updateDensity M (gaussianPDF a V) (gaussianPDF b U) = _ at heq
  exact ⟨hn, fun z => congrFun heq z, heq ▸ hg⟩

end DKFAsymptotics.Proof
end

-- Solutions.MatrixLimits
section
open MeasureTheory Filter Matrix
open scoped Topology ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace DKFAsymptotics.Proof
variable {d : ℕ}

theorem posDef_one_add_of_norm_lt_one {B : Covariance d}
    (hB : B.IsHermitian) (hn : ‖B‖ < 1) : (1 + B).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (Matrix.isHermitian_one.add hB)
  intro x hx
  let v : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 x
  have hv : v ≠ 0 := by simpa [v] using hx
  have hinner : |⟪v, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) B v⟫| ≤ ‖B‖ * ‖v‖ ^ 2 := by
    calc
      _ ≤ ‖v‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) B v‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖v‖ * (‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) B‖ * ‖v‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ = _ := by rw [← Matrix.cstar_norm_def]; ring
  have he : x ⬝ᵥ x = ‖v‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [dotProduct, v, pow_two]
  have heB : x ⬝ᵥ B *ᵥ x = ⟪v, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) B v⟫ := by
    exact (Matrix.inner_toEuclideanCLM B v v).symm
  simp only [add_mulVec, one_mulVec, dotProduct_add, star_trivial, he, heB]
  have hsq : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
  have hl := (abs_le.mp hinner).1
  nlinarith

theorem tendsto_mulVec {ι : Type*} {L : Filter ι} {A : ι → Covariance d}
    {B : Covariance d} {x : ι → State d} {y : State d}
    (hA : Tendsto A L (𝓝 B)) (hx : Tendsto x L (𝓝 y)) :
    Tendsto (fun n => A n *ᵥ x n) L (𝓝 (B *ᵥ y)) := by
  have hc : Continuous (fun p : Covariance d × State d => p.1 *ᵥ p.2) := by fun_prop
  exact hc.continuousAt.tendsto.comp (hA.prodMk_nhds hx)

theorem matrix_inv_tendsto {ι : Type*} {L : Filter ι} {A : ι → Covariance d}
    {B : Covariance d} (hB : IsUnit B.det) (hA : Tendsto A L (𝓝 B)) :
    Tendsto (fun n => (A n)⁻¹) L (𝓝 B⁻¹) := by
  apply (continuousAt_matrix_inv B ?_).tendsto.comp hA
  simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ (isUnit_iff_ne_zero.mp hB)

theorem inverse_perturbation_identity {U D : Covariance d} (hU : U.PosDef) :
    (U⁻¹ + D)⁻¹ = (1 + U * D)⁻¹ * U := by
  have hdet := (Matrix.isUnit_iff_isUnit_det U).mp hU.isUnit
  have he : U⁻¹ + D = U⁻¹ * (1 + U * D) := by
    rw [mul_add, mul_one, nonsing_inv_mul_cancel_left U D hdet]
  rw [he, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv U hdet]

theorem inverse_perturbation_mul_identity {U D : Covariance d} (hU : U.PosDef) :
    (U⁻¹ + D)⁻¹ * U⁻¹ = (1 + U * D)⁻¹ := by
  rw [inverse_perturbation_identity hU, mul_assoc,
    mul_nonsing_inv U ((Matrix.isUnit_iff_isUnit_det U).mp hU.isUnit), mul_one]

theorem perturbation_posDef_eventually (U D : ℕ+ → Covariance d)
    (hU : ∀ n, (U n).PosDef) (hD : ∀ n, (D n).IsHermitian)
    {D₀ : Covariance d} (hU0 : Tendsto U atTop (𝓝 0)) (hD0 : Tendsto D atTop (𝓝 D₀)) :
    ∀ᶠ n in atTop, ((U n)⁻¹ + D n).PosDef := by
  have hsqrt : Tendsto (fun n => CFC.sqrt (U n)) atTop (𝓝 (0 : Covariance d)) := by
    have ht := CFC.continuousOn_sqrt.continuousWithinAt (x := (0 : Covariance d))
      (show 0 ≤ (0 : Covariance d) from le_rfl)
    have ht' := ht.tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨hU0, Eventually.of_forall (fun n => (hU n).posSemidef.nonneg)⟩)
    simpa [Function.comp_def] using ht'
  have hsmall : Tendsto (fun n => ‖CFC.sqrt (U n) * D n * CFC.sqrt (U n)‖)
      atTop (𝓝 0) := by simpa using ((hsqrt.mul hD0).mul hsqrt).norm
  have hevent : ∀ᶠ n in atTop, ‖CFC.sqrt (U n) * D n * CFC.sqrt (U n)‖ < 1 :=
    hsmall.eventually (gt_mem_nhds (by norm_num))
  filter_upwards [hevent] with n hn
  let C := CFC.sqrt (U n)
  have hC : C.PosDef := (hU n).isStrictlyPositive.sqrt.posDef
  have hCC : C * C = U n := CFC.sqrt_mul_sqrt_self _ (hU n).posSemidef.nonneg
  have hCh : Cᴴ = C := hC.isHermitian.eq
  have hsym : (C * D n * C).IsHermitian := by
    simpa only [hCh] using Matrix.isHermitian_conjTranspose_mul_mul C (hD n)
  have hpos : (1 + C * D n * C).PosDef := posDef_one_add_of_norm_lt_one hsym hn
  have he : Cᴴ * ((U n)⁻¹ + D n) * C = 1 + C * D n * C := by
    rw [hCh, mul_add, add_mul, ← hCC, Matrix.mul_inv_rev]
    have hdet := (Matrix.isUnit_iff_isUnit_det C).mp hC.isUnit
    simp only [← mul_assoc, mul_nonsing_inv C hdet, one_mul,
      nonsing_inv_mul C hdet]
  exact (hC.isUnit.posDef_star_left_conjugate_iff).mp (by
    simpa only [star_eq_conjTranspose, he] using hpos)

theorem perturbation_inverse_tendsto (U D : ℕ+ → Covariance d)
    (hU : ∀ n, (U n).PosDef) {D₀ : Covariance d}
    (hU0 : Tendsto U atTop (𝓝 0)) (hD0 : Tendsto D atTop (𝓝 D₀)) :
    Tendsto (fun n => ((U n)⁻¹ + D n)⁻¹) atTop (𝓝 0) ∧
    Tendsto (fun n => ((U n)⁻¹ + D n)⁻¹ * (U n)⁻¹) atTop (𝓝 1) := by
  have hJ : Tendsto (fun n => 1 + U n * D n) atTop (𝓝 (1 : Covariance d)) := by
    simpa using tendsto_const_nhds.add (hU0.mul hD0)
  have hJi : Tendsto (fun n => (1 + U n * D n)⁻¹) atTop (𝓝 (1 : Covariance d)) := by
    simpa using matrix_inv_tendsto (by simp : IsUnit (1 : Covariance d).det) hJ
  constructor
  · simpa only [inverse_perturbation_identity (hU _), mul_zero] using hJi.mul hU0
  · simpa only [inverse_perturbation_mul_identity (hU _)] using hJi

end DKFAsymptotics.Proof
end

-- Solutions.GaussianAffine
section
open MeasureTheory Filter Matrix
open scoped Topology ENNReal MatrixOrder Matrix.Norms.L2Operator
namespace DKFAsymptotics.Proof
variable {d : ℕ}

theorem integral_affine_matrix (B : Covariance d) (hB : B.det ≠ 0) (m : State d)
    (f : State d → ℝ) (hf : Continuous f) :
    (∫ x, f (m + B *ᵥ x) ∂volume) = |B.det⁻¹| * ∫ z, f z ∂volume := by
  have hb : Measurable (toLin' B) := (LinearMap.continuous_on_pi _).measurable
  have he := integral_map (μ := (volume : Measure (State d)))
    (f := fun z => f (m + z)) hb.aemeasurable
    ((hf.comp (continuous_const.add continuous_id)).aestronglyMeasurable)
  rw [Real.map_matrix_volume_pi_eq_smul_volume_pi hB, integral_smul_measure,
    ENNReal.toReal_ofReal (abs_nonneg _), integral_add_left_eq_self] at he
  exact he.symm

theorem gaussian_sqrt_quadratic {C : Covariance d} (hC : C.PosDef) (x : State d) :
    (CFC.sqrt C *ᵥ x) ⬝ᵥ C⁻¹ *ᵥ (CFC.sqrt C *ᵥ x) = x ⬝ᵥ x := by
  let B := CFC.sqrt C
  have hB : B.PosDef := hC.isStrictlyPositive.sqrt.posDef
  have hBB : B * B = C := CFC.sqrt_mul_sqrt_self _ hC.posSemidef.nonneg
  have hdet := (Matrix.isUnit_iff_isUnit_det B).mp hB.isUnit
  have hBi : B * C⁻¹ * B = 1 := by
    rw [← hBB, Matrix.mul_inv_rev]
    simp only [← mul_assoc, mul_nonsing_inv B hdet, one_mul, nonsing_inv_mul B hdet]
  change (B *ᵥ x) ⬝ᵥ C⁻¹ *ᵥ (B *ᵥ x) = _
  rw [← dot_transpose_mulVec B]
  have hBt : B.transpose = B := by simpa only [conjTranspose_eq_transpose_of_trivial] using hB.1.eq
  rw [hBt, mulVec_mulVec, mulVec_mulVec, hBi, one_mulVec]

theorem gaussianPDF_affine (m : State d) {C : Covariance d} (hC : C.PosDef)
    (x : State d) :
    gaussianPDF m C (m + CFC.sqrt C *ᵥ x) =
      |(CFC.sqrt C).det⁻¹| * gaussianPDF 0 (1 : Covariance d) x := by
  let kI := Real.sqrt ((2 * Real.pi) ^ d)
  let kC := Real.sqrt ((2 * Real.pi) ^ d * C.det)
  have hkI : kI ≠ 0 := (Real.sqrt_pos.mpr (pow_pos (by positivity) _)).ne'
  have hpoint y : gaussianPDF m C (m + CFC.sqrt C *ᵥ y) =
      (kI / kC) * gaussianPDF 0 (1 : Covariance d) y := by
    simp only [gaussianPDF, add_sub_cancel_left, gaussian_sqrt_quadratic hC,
      sub_zero, det_one, mul_one, inv_one, one_mulVec]
    change kC⁻¹ * _ = (kI / kC) * (kI⁻¹ * _)
    field_simp [hkI]
  have hB : (CFC.sqrt C).det ≠ 0 :=
    (hC.isStrictlyPositive.sqrt.posDef.det_pos).ne'
  have hint := integral_affine_matrix (CFC.sqrt C) hB m (gaussianPDF m C)
    (gaussianPDF_continuous m C)
  simp_rw [hpoint] at hint
  rw [integral_const_mul, gaussianPDF_integral _ Matrix.PosDef.one,
    gaussianPDF_integral m hC, mul_one, mul_one] at hint
  rw [hpoint, hint]

theorem gaussian_integral_affine (m : State d) {C : Covariance d} (hC : C.PosDef)
    (g : BoundedContinuousFunction (State d) ℝ) :
    (∫ z, g z ∂densityMeasure (gaussianPDF m C)) =
      ∫ x, g (m + CFC.sqrt C *ᵥ x) ∂densityMeasure (gaussianPDF 0 (1 : Covariance d)) := by
  rw [integral_densityMeasure (gaussianPDF_isPDF m hC),
    integral_densityMeasure (gaussianPDF_isPDF 0 Matrix.PosDef.one)]
  have hB : (CFC.sqrt C).det ≠ 0 :=
    (hC.isStrictlyPositive.sqrt.posDef.det_pos).ne'
  have hpos : |(CFC.sqrt C).det⁻¹| ≠ 0 := abs_ne_zero.mpr (inv_ne_zero hB)
  have he := integral_affine_matrix (CFC.sqrt C) hB m
    (fun z => gaussianPDF m C z * g z) ((gaussianPDF_continuous m C).mul g.continuous)
  simp only [gaussianPDF_affine m hC, mul_assoc] at he
  rw [integral_const_mul] at he
  exact (mul_left_cancel₀ hpos he).symm

theorem gaussian_weakly_dirac {m : ℕ+ → State d} {C : ℕ+ → Covariance d}
    (hC : ∀ n, (C n).PosDef) {b : State d}
    (hm : Tendsto m atTop (𝓝 b)) (hC0 : Tendsto C atTop (𝓝 0)) :
    Weakly (fun n => gaussianPDF (m n) (C n)) (Measure.dirac b) := by
  have hsqrt : Tendsto (fun n => CFC.sqrt (C n)) atTop (𝓝 (0 : Covariance d)) := by
    have hc := CFC.continuousOn_sqrt.continuousWithinAt (x := (0 : Covariance d)) le_rfl
    have ht := hc.tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨hC0, Eventually.of_forall (fun n => (hC n).posSemidef.nonneg)⟩)
    simpa [Function.comp_def] using ht
  intro g
  simp only [gaussian_integral_affine _ (hC _), integral_dirac]
  let μ := densityMeasure (gaussianPDF (0 : State d) (1 : Covariance d))
  let :=  isProbabilityMeasure_densityMeasure (gaussianPDF_isPDF (0 : State d) Matrix.PosDef.one)
  have ht : Tendsto (fun n => ∫ x, g (m n + CFC.sqrt (C n) *ᵥ x) ∂μ) atTop
      (𝓝 (∫ _x, g b ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => ‖g‖)
    · exact Eventually.of_forall (fun n => (g.continuous.comp
        (continuous_const.add (show Continuous (fun x : State d => CFC.sqrt (C n) *ᵥ x) by fun_prop))).aestronglyMeasurable)
    · exact Eventually.of_forall (fun n => ae_of_all _ (fun x => g.norm_coe_le_norm _))
    · exact integrable_const _
    · filter_upwards [] with x
      have hv := hm.add (tendsto_mulVec hsqrt (tendsto_const_nhds (x := x)))
      simpa only [zero_mulVec, add_zero, Function.comp_def] using g.continuous.tendsto _ |>.comp hv
  simpa [μ] using ht

end DKFAsymptotics.Proof
end

-- Solutions.GaussianLog
section
open MeasureTheory Filter Matrix
open scoped Topology ENNReal MatrixOrder Matrix.Norms.L2Operator
namespace DKFAsymptotics.Proof
variable {d : ℕ}

theorem gaussianPDF_log (m : State d) {C : Covariance d} (hC : C.PosDef) (z : State d) :
    Real.log (gaussianPDF m C z) =
      Real.log ((Real.sqrt ((2 * Real.pi) ^ d * C.det))⁻¹) -
        ((z - m) ⬝ᵥ C⁻¹ *ᵥ (z - m)) / 2 := by
  have hk : (Real.sqrt ((2 * Real.pi) ^ d * C.det))⁻¹ ≠ 0 := by
    apply inv_ne_zero
    exact (Real.sqrt_pos.mpr (mul_pos (pow_pos (by positivity) _) hC.det_pos)).ne'
  rw [gaussianPDF, Real.log_mul hk (Real.exp_ne_zero _), Real.log_exp]
  ring

theorem gaussian_log_second_difference (m : State d) {C : Covariance d}
    (hC : C.PosDef) (x y : State d) :
    Real.log (gaussianPDF m C x) + Real.log (gaussianPDF m C y) -
      Real.log (gaussianPDF m C (x + y)) - Real.log (gaussianPDF m C 0) =
        x ⬝ᵥ C⁻¹ *ᵥ y := by
  simp only [gaussianPDF_log m hC, shifted_quadratic_expand hC.inv.isHermitian,
    mulVec_add, dotProduct_add, add_dotProduct, zero_dotProduct, mulVec_zero,
    dotProduct_zero]
  rw [dot_mulVec_comm_of_isHermitian hC.inv.isHermitian y x]
  ring

theorem gaussian_log_first_difference (m : State d) {C : Covariance d}
    (hC : C.PosDef) (x : State d) :
    (Real.log (gaussianPDF m C x) - Real.log (gaussianPDF m C (-x))) / 2 =
        x ⬝ᵥ C⁻¹ *ᵥ m := by
  simp only [gaussianPDF_log m hC, shifted_quadratic_expand hC.inv.isHermitian,
    mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg]
  ring

theorem gaussian_log_precision_entry (m : State d) {C : Covariance d}
    (hC : C.PosDef) (i j : Fin d) :
    Real.log (gaussianPDF m C (Pi.single i 1)) + Real.log (gaussianPDF m C (Pi.single j 1)) -
      Real.log (gaussianPDF m C (Pi.single i 1 + Pi.single j 1)) -
        Real.log (gaussianPDF m C 0) = C⁻¹ i j := by
  rw [gaussian_log_second_difference m hC]
  simp [mulVec, dotProduct, Pi.single_apply]

theorem gaussian_log_weighted_mean (m : State d) {C : Covariance d}
    (hC : C.PosDef) (i : Fin d) :
    (Real.log (gaussianPDF m C (Pi.single i 1)) -
      Real.log (gaussianPDF m C (-Pi.single i 1))) / 2 = (C⁻¹ *ᵥ m) i := by
  rw [gaussian_log_first_difference m hC]
  simp [dotProduct, Pi.single_apply]

theorem gaussianPDF_injective {m m' : State d} {C C' : Covariance d}
    (hC : C.PosDef) (hC' : C'.PosDef) (he : gaussianPDF m C = gaussianPDF m' C') :
    m = m' ∧ C = C' := by
  have hI : C⁻¹ = C'⁻¹ := by
    ext i j
    rw [← gaussian_log_precision_entry m hC, ← gaussian_log_precision_entry m' hC', he]
  have hW : C⁻¹ *ᵥ m = C'⁻¹ *ᵥ m' := by
    ext i
    rw [← gaussian_log_weighted_mean m hC, ← gaussian_log_weighted_mean m' hC', he]
  have hCC : C = C' := by
    have := congrArg Inv.inv hI
    simpa only [Matrix.nonsing_inv_nonsing_inv C ((Matrix.isUnit_iff_isUnit_det C).mp hC.isUnit),
      Matrix.nonsing_inv_nonsing_inv C' ((Matrix.isUnit_iff_isUnit_det C').mp hC'.isUnit)] using this
  refine ⟨?_, hCC⟩
  rw [← hI] at hW
  exact Matrix.mulVec_injective_of_isUnit hC.inv.isUnit hW

theorem gaussian_density_sq_det_le (m : State d) {C : Covariance d}
    (hC : C.PosDef) : (gaussianPDF m C 0) ^ 2 * (2 * Real.pi) ^ d ≤ C⁻¹.det := by
  have hpos : 0 < (2 * Real.pi) ^ d := pow_pos (by positivity) _
  have hprod : 0 < (2 * Real.pi) ^ d * C.det := mul_pos hpos hC.det_pos
  have he : (gaussianPDF 0 C 0) ^ 2 * (2 * Real.pi) ^ d = C⁻¹.det := by
    simp only [gaussianPDF, sub_self, mulVec_zero, dotProduct_zero, neg_zero,
      zero_div, Real.exp_zero, mul_one, inv_pow, Real.sq_sqrt hprod.le,
      det_nonsing_inv, Ring.inverse_eq_inv]
    field_simp
  rw [← he]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (gaussianPDF_pos m hC 0).le (gaussianPDF_le m hC 0) _) hpos.le

end DKFAsymptotics.Proof
end

-- Solutions.L1Tools
section
open MeasureTheory Filter Matrix
open scoped Topology ENNReal
namespace DKFAsymptotics.Proof
variable {d : ℕ}

theorem l1Norm_finite {f : Density d} (hf : Integrable f volume) : l1Norm f < ⊤ := by
  have h := hf.2
  rw [hasFiniteIntegral_iff_norm] at h
  exact h

theorem l1Distance_finite {f g : Density d}
    (hf : Integrable f volume) (hg : Integrable g volume) : l1Distance f g < ⊤ :=
  l1Norm_finite (hf.sub hg)

theorem l1Distance_toReal {f g : Density d}
    (hf : Integrable f volume) (hg : Integrable g volume) :
    (l1Distance f g).toReal = ∫ z, ‖f z - g z‖ ∂volume :=
  l1Norm_toReal (hf.sub hg).1

theorem l1Distance_comm (f g : Density d) : l1Distance f g = l1Distance g f := by
  unfold l1Distance l1Norm
  apply lintegral_congr
  intro z
  simp only [Pi.sub_apply, abs_sub_comm]

theorem l1Distance_triangle {f g h : Density d}
    (hf : Integrable f volume) (hg : Integrable g volume) (hh : Integrable h volume) :
    (l1Distance f h).toReal ≤ (l1Distance f g).toReal + (l1Distance g h).toReal := by
  rw [l1Distance_toReal hf hh, l1Distance_toReal hf hg, l1Distance_toReal hg hh]
  have hadd := integral_add (hf.sub hg).norm (hg.sub hh).norm
  simp only [Pi.sub_apply] at hadd
  rw [← hadd]
  apply integral_mono (hf.sub hh).norm ((hf.sub hg).norm.add (hg.sub hh).norm)
  intro z
  exact norm_sub_le_norm_sub_add_norm_sub _ _ _

theorem l1Distance_zero_tendsto_iff {f g : ℕ+ → Density d}
    (hf : ∀ n, Integrable (f n) volume) (hg : ∀ n, Integrable (g n) volume) :
    Tendsto (fun n => l1Distance (f n) (g n)) atTop (𝓝 0) ↔
    Tendsto (fun n => (l1Distance (f n) (g n)).toReal) atTop (𝓝 0) := by
  exact (ENNReal.tendsto_toReal_zero_iff (fun n => (l1Distance_finite (hf n) (hg n)).ne)).symm

theorem integral_abs_density_difference_le {f g : Density d}
    (hf : Integrable f volume) (hg : Integrable g volume) :
    |(∫ z, f z ∂volume) - ∫ z, g z ∂volume| ≤ (l1Distance f g).toReal := by
  rw [← integral_sub hf hg, l1Distance_toReal hf hg]
  exact norm_integral_le_integral_norm (fun z : State d => f z - g z)

end DKFAsymptotics.Proof
end

-- Solutions.KernelMass
section
open MeasureTheory Filter Matrix
open scoped Topology ENNReal
namespace DKFAsymptotics.Proof
variable {d : ℕ}

def transitionBCF (M : Model d) : BoundedContinuousFunction (State d × State d) ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun yz => transition M yz.1 yz.2)
    (transition_continuous M) (gaussianPDF 0 M.Γ 0) (fun yz => by
      rw [Real.norm_eq_abs, abs_of_pos (transition_pos M yz.1 yz.2)]
      exact transition_le M yz.1 yz.2)

theorem kernelProduct_integrable (M : Model d) {s u : Density d}
    (hs : IsPDF s) (hu : IsPDF u) :
    Integrable (fun z => u z * predictDensity M s z) volume := by
  apply hu.2.1.mul_bdd (predict_continuous M hs.2.1).aestronglyMeasurable
  filter_upwards [] with z
  simpa only [l1Norm_toReal_pdf hs, mul_one] using predict_norm_le M hs.2.1 z

theorem kernelProduct_integral (M : Model d) {s u : Density d}
    (hs : IsPDF s) (hu : IsPDF u) :
    (∫ z, u z * predictDensity M s z ∂volume) =
      ∫ yz, transition M yz.1 yz.2 ∂(densityMeasure s).prod (densityMeasure u) := by
  let :=  isProbabilityMeasure_densityMeasure hs
  let :=  isProbabilityMeasure_densityMeasure hu
  have hj := (transitionBCF M).integrable ((densityMeasure s).prod (densityMeasure u))
  change Integrable (fun yz : State d × State d => transition M yz.1 yz.2)
    ((densityMeasure s).prod (densityMeasure u)) at hj
  rw [integral_prod _ hj, integral_integral_swap hj]
  rw [integral_densityMeasure hu]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [integral_densityMeasure hs]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with y using mul_comm _ _

theorem kernelProduct_mass_tendsto (M : Model d) {s u : ℕ+ → Density d}
    (hs : ∀ n, IsPDF (s n)) (hu : ∀ n, IsPDF (u n))
    (P : ProbabilityMeasure (State d)) (b : State d)
    (hws : Weakly s P) (hwu : Weakly u (Measure.dirac b)) :
    Tendsto (fun n => ∫ z, u n z * predictDensity M (s n) z ∂volume) atTop
      (𝓝 (∫ y, transition M y b ∂P)) := by
  let Q : ProbabilityMeasure (State d) := ⟨Measure.dirac b, inferInstance⟩
  have hS := (weakly_iff_tendsto hs P).mp hws
  have hU := (weakly_iff_tendsto hu Q).mp hwu
  have ht := ProbabilityMeasure.continuous_prod.tendsto (P, Q) |>.comp (hS.prodMk_nhds hU)
  have hw := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp ht (transitionBCF M)
  have hj := (transitionBCF M).integrable ((P : Measure (State d)).prod (Measure.dirac b))
  change Integrable (fun yz : State d × State d => transition M yz.1 yz.2)
    ((P : Measure (State d)).prod (Measure.dirac b)) at hj
  have hl : (∫ yz, transition M yz.1 yz.2 ∂(P : Measure (State d)).prod (Measure.dirac b)) =
      ∫ y, transition M y b ∂P := by
    rw [integral_prod _ hj]
    simp only [integral_dirac]
  change Tendsto (fun n => ∫ yz, transition M yz.1 yz.2 ∂
    (densityMeasure (s n)).prod (densityMeasure (u n))) atTop
    (𝓝 (∫ yz, transition M yz.1 yz.2 ∂(P : Measure (State d)).prod (Measure.dirac b))) at hw
  simpa only [← kernelProduct_integral M (hs _) (hu _), hl] using hw

theorem kernel_limit_pos (M : Model d) (P : ProbabilityMeasure (State d)) (b : State d) :
    0 < ∫ y, transition M y b ∂P := by
  let g := BoundedContinuousFunction.ofNormedAddCommGroup (fun y => transition M y b)
    ((transition_continuous M).comp (continuous_id.prodMk continuous_const))
    (gaussianPDF 0 M.Γ 0) (fun y => by
      rw [Real.norm_eq_abs, abs_of_pos (transition_pos M y b)]
      exact transition_le M y b)
  rw [integral_pos_iff_support_of_nonneg (fun y => (transition_pos M y b).le) (g.integrable P)]
  have he : Function.support (fun y => transition M y b) = Set.univ := by
    ext y
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (transition_pos M y b).ne'
  rw [he, measure_univ]
  exact zero_lt_one

end DKFAsymptotics.Proof
end

-- Solutions.GaussianParameterRecovery
section
open MeasureTheory Filter Matrix
open scoped Topology ENNReal MatrixOrder Matrix.Norms.L2Operator
namespace DKFAsymptotics.Proof
variable {d : ℕ}

theorem posSemidef_of_tendsto {ι : Type*} {L : Filter ι} [L.NeBot]
    {A : ι → Covariance d} {B : Covariance d}
    (hA : ∀ n, (A n).PosSemidef) (ht : Tendsto A L (𝓝 B)) : B.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · have hc : Continuous (fun C : Covariance d => Cᴴ) := by fun_prop
    have h1 := hc.tendsto B |>.comp ht
    have h2 : Tendsto (fun n => (A n)ᴴ) L (𝓝 B) :=
      ht.congr' (Eventually.of_forall (fun n => (hA n).isHermitian.eq.symm))
    exact tendsto_nhds_unique h1 h2
  · intro x
    have hc : Continuous (fun C : Covariance d => star x ⬝ᵥ C *ᵥ x) := by
      simp only [dotProduct, mulVec]
      fun_prop
    exact le_of_tendsto_of_tendsto tendsto_const_nhds (hc.tendsto B |>.comp ht)
      (Eventually.of_forall (fun n => (hA n).dotProduct_mulVec_nonneg x))

theorem gaussianPDF_tendsto {ι : Type*} {L : Filter ι}
    {m : ι → State d} {C : ι → Covariance d} {b : State d} {V : Covariance d}
    (hV : V.PosDef) (hm : Tendsto m L (𝓝 b)) (hC : Tendsto C L (𝓝 V)) (z : State d) :
    Tendsto (fun n => gaussianPDF (m n) (C n) z) L (𝓝 (gaussianPDF b V z)) := by
  have hinv := matrix_inv_tendsto ((Matrix.isUnit_iff_isUnit_det V).mp hV.isUnit) hC
  have hdet := (continuous_id.matrix_det).tendsto V |>.comp hC
  have hk := (hdet.const_mul ((2 * Real.pi) ^ d)).sqrt
  have hk0 : Real.sqrt ((2 * Real.pi) ^ d * V.det) ≠ 0 :=
    (Real.sqrt_pos.mpr (mul_pos (pow_pos (by positivity) _) hV.det_pos)).ne'
  have hsub := (tendsto_const_nhds (x := z)).sub hm
  have hmv := tendsto_mulVec hinv hsub
  have hdot : Continuous (fun p : State d × State d => p.1 ⬝ᵥ p.2) := by
    simp only [dotProduct]
    fun_prop
  have hq := hdot.continuousAt.tendsto.comp (hsub.prodMk_nhds hmv)
  have hex := Real.continuous_exp.continuousAt.tendsto.comp (hq.neg.div_const 2)
  simpa only [gaussianPDF, Function.comp_def, id_eq] using (hk.inv₀ hk0).mul hex

/-- A positive pointwise limit of nondegenerate Gaussian densities determines limits
of both parameters. Finite differences of the log densities avoid phase ambiguity. -/
theorem gaussian_parameters_of_positive_density_limit (m : ℕ+ → State d)
    (C : ℕ+ → Covariance d) (hC : ∀ n, (C n).PosDef)
    (F : State d → ℝ) (hF : ∀ z, 0 < F z)
    (hlim : ∀ z, Tendsto (fun n => gaussianPDF (m n) (C n) z) atTop (𝓝 (F z))) :
    ∃ b : State d, ∃ V : Covariance d, V.PosDef ∧
      Tendsto m atTop (𝓝 b) ∧ Tendsto C atTop (𝓝 V) ∧ F = gaussianPDF b V := by
  let H : Covariance d := fun i j =>
    Real.log (F (Pi.single i 1)) + Real.log (F (Pi.single j 1)) -
      Real.log (F (Pi.single i 1 + Pi.single j 1)) - Real.log (F 0)
  let w : State d := fun i =>
    (Real.log (F (Pi.single i 1)) - Real.log (F (-Pi.single i 1))) / 2
  have hlog z := (hlim z).log (hF z).ne'
  have hH : Tendsto (fun n => (C n)⁻¹) atTop (𝓝 H) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    have ht := ((hlog (Pi.single i 1)).add (hlog (Pi.single j 1))).sub
      (hlog (Pi.single i 1 + Pi.single j 1)) |>.sub (hlog 0)
    simpa only [gaussian_log_precision_entry _ (hC _)] using ht
  have hw : Tendsto (fun n => (C n)⁻¹ *ᵥ m n) atTop (𝓝 w) := by
    apply tendsto_pi_nhds.mpr
    intro i
    have ht := ((hlog (Pi.single i 1)).sub (hlog (-Pi.single i 1))).div_const 2
    simpa only [gaussian_log_weighted_mean _ (hC _)] using ht
  have hHps : H.PosSemidef := posSemidef_of_tendsto (fun n => (hC n).inv.posSemidef) hH
  have hdH := (continuous_id.matrix_det).tendsto H |>.comp hH
  have hbound : (F 0) ^ 2 * (2 * Real.pi) ^ d ≤ H.det :=
    le_of_tendsto_of_tendsto ((hlim 0).pow 2 |>.mul_const _) hdH
      (Eventually.of_forall (fun n => gaussian_density_sq_det_le (m n) (hC n)))
  have hHdet : 0 < H.det := lt_of_lt_of_le
    (mul_pos (sq_pos_of_pos (hF 0)) (pow_pos (by positivity) _)) hbound
  have hHp : H.PosDef := hHps.posDef_iff_det_ne_zero.mpr hHdet.ne'
  have hCs : Tendsto C atTop (𝓝 H⁻¹) := by
    have ht := matrix_inv_tendsto ((Matrix.isUnit_iff_isUnit_det H).mp hHp.isUnit) hH
    simpa only [Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (hC _).isUnit)] using ht
  have hm : Tendsto m atTop (𝓝 (H⁻¹ *ᵥ w)) := by
    have ht := tendsto_mulVec hCs hw
    simpa only [mulVec_mulVec, Matrix.mul_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det _).mp (hC _).isUnit), one_mulVec] using ht
  refine ⟨H⁻¹ *ᵥ w, H⁻¹, hHp.inv, hm, hCs, ?_⟩
  funext z
  exact tendsto_nhds_unique (hlim z) (gaussianPDF_tendsto hHp.inv hm hCs z)

end DKFAsymptotics.Proof
end

-- Solutions.GaussianWeakParameters
section
open MeasureTheory Filter Matrix
open scoped Topology ENNReal MatrixOrder Matrix.Norms.L2Operator
namespace DKFAsymptotics.Proof
variable {d : ℕ}

theorem predicted_gaussian_parameters (M : Model d) (a : ℕ+ → State d)
    (V : ℕ+ → Covariance d) (hV : ∀ n, (V n).PosDef)
    (P : ProbabilityMeasure (State d))
    (hw : Weakly (fun n => gaussianPDF (a n) (V n)) P) :
    ∃ c : State d, ∃ G : Covariance d, G.PosDef ∧
      Tendsto (fun n => M.A *ᵥ a n) atTop (𝓝 c) ∧
      Tendsto (fun n => predictedCovariance M (V n)) atTop (𝓝 G) ∧
      (fun z => ∫ y, transition M y z ∂P) = gaussianPDF c G := by
  apply gaussian_parameters_of_positive_density_limit
    (fun n => M.A *ᵥ a n) (fun n => predictedCovariance M (V n))
    (fun n => predictedCovariance_posDef M (hV n).posSemidef)
    (fun z => ∫ y, transition M y z ∂P) (kernel_limit_pos M P)
  intro z
  let g := BoundedContinuousFunction.ofNormedAddCommGroup (fun y => transition M y z)
    ((transition_continuous M).comp (continuous_id.prodMk continuous_const))
    (gaussianPDF 0 M.Γ 0) (fun y => by
      rw [Real.norm_eq_abs, abs_of_pos (transition_pos M y z)]
      exact transition_le M y z)
  have ht := hw g
  have he n : (∫ y, g y ∂densityMeasure (gaussianPDF (a n) (V n))) =
      gaussianPDF (M.A *ᵥ a n) (predictedCovariance M (V n)) z := by
    rw [integral_densityMeasure (gaussianPDF_isPDF _ (hV n))]
    have hpred := congrFun (predict_gaussian M (a n) (hV n)) z
    rw [← hpred]
    unfold predictDensity
    apply integral_congr_ae
    filter_upwards [] with y using mul_comm _ _
  simp only [he] at ht
  change Tendsto _ atTop (𝓝 (∫ y, transition M y z ∂P)) at ht
  exact ht

/-- A fixed smoothing model, used only inside the proof to recover Gaussian parameters. -/
def smoothingModel (d : ℕ) : Model d where
  A := (1 / 2 : ℝ) • 1
  Γ := (3 / 4 : ℝ) • 1
  S := 1
  Γ_posDef := Matrix.PosDef.one.smul (by norm_num)
  S_posDef := Matrix.PosDef.one
  stationary := by
    simp only [transpose_smul, transpose_one, mul_one, Matrix.mul_smul, smul_smul]
    module

theorem gaussian_parameters_of_weakly_dirac (a : ℕ+ → State d)
    (V : ℕ+ → Covariance d) (hV : ∀ n, (V n).PosDef) (b : State d)
    (hw : Weakly (fun n => gaussianPDF (a n) (V n)) (Measure.dirac b)) :
    Tendsto a atTop (𝓝 b) ∧ Tendsto V atTop (𝓝 0) := by
  let M := smoothingModel d
  let P : ProbabilityMeasure (State d) := ⟨Measure.dirac b, inferInstance⟩
  obtain ⟨c, G, hG, hc, hGs, he⟩ := predicted_gaussian_parameters M a V hV P hw
  have he' : gaussianPDF (M.A *ᵥ b) M.Γ = gaussianPDF c G := by
    change (fun z => ∫ y, transition M y z ∂Measure.dirac b) = _ at he
    simpa only [integral_dirac, transition] using he
  obtain ⟨hmean, hcov⟩ := gaussianPDF_injective M.Γ_posDef hG he'
  rw [← hmean] at hc
  rw [← hcov] at hGs
  have heMean (x : State d) : (2 : ℝ) • (M.A *ᵥ x) = x := by
    simp [M, smoothingModel, smul_mulVec, smul_smul]
  have heCov (C : Covariance d) : (4 : ℝ) • (predictedCovariance M C - M.Γ) = C := by
    simp only [predictedCovariance, add_sub_cancel_right, M, smoothingModel,
      transpose_smul, transpose_one, smul_mul, Matrix.mul_smul, one_mul, mul_one, smul_smul]
    norm_num
  constructor
  · simpa only [heMean] using hc.const_smul (2 : ℝ)
  · have ht := (hGs.sub (tendsto_const_nhds (x := M.Γ))).const_smul (4 : ℝ)
    simpa only [heCov, sub_self, smul_zero] using ht

end DKFAsymptotics.Proof
end

-- Solutions.DKFParameterLimits
section
open MeasureTheory Filter Matrix
open scoped Topology ENNReal MatrixOrder Matrix.Norms.L2Operator
namespace DKFAsymptotics.Proof

/-- The matrix part of the second half of Lemma 1. -/
theorem dkf_parameter_limits {d : ℕ} (M : Model d)
    (a b' : ℕ+ → State d) (V U : ℕ+ → Covariance d)
    (hV : ∀ n, (V n).PosDef) (hU : ∀ n, (U n).PosDef)
    {a₀ b : State d} {V₀ : Covariance d} (hV₀ : V₀.PosSemidef)
    (ha : Tendsto a atTop (𝓝 a₀)) (hb : Tendsto b' atTop (𝓝 b))
    (hVs : Tendsto V atTop (𝓝 V₀)) (hUs : Tendsto U atTop (𝓝 0)) :
    (∀ᶠ n in atTop, ValidStep M ⟨a n, V n⟩ ⟨b' n, U n⟩) ∧
    Tendsto (fun n => (dkfStep M ⟨a n, V n⟩ ⟨b' n, U n⟩).covariance)
      atTop (𝓝 0) ∧
    Tendsto (fun n => (dkfStep M ⟨a n, V n⟩ ⟨b' n, U n⟩).mean)
      atTop (𝓝 b) := by
  let G := fun n => predictedCovariance M (V n)
  let G₀ := predictedCovariance M V₀
  let D := fun n => (G n)⁻¹ - M.S⁻¹
  have hG₀ : G₀.PosDef := predictedCovariance_posDef M hV₀
  have hGs : Tendsto G atTop (𝓝 G₀) :=
    ((tendsto_const_nhds.mul hVs).mul tendsto_const_nhds).add tendsto_const_nhds
  have hGis : Tendsto (fun n => (G n)⁻¹) atTop (𝓝 G₀⁻¹) :=
    matrix_inv_tendsto ((Matrix.isUnit_iff_isUnit_det G₀).mp hG₀.isUnit) hGs
  have hDs : Tendsto D atTop (𝓝 (G₀⁻¹ - M.S⁻¹)) := hGis.sub tendsto_const_nhds
  have hDh n : (D n).IsHermitian :=
    (predictedCovariance_posDef M (hV n).posSemidef).inv.isHermitian.sub M.S_posDef.inv.isHermitian
  have hpos := perturbation_posDef_eventually U D hU hDh hUs hDs
  have ht := perturbation_inverse_tendsto U D hU hUs hDs
  have he n : (U n)⁻¹ + D n = updatePrecision M (V n) (U n) := by
    dsimp [D, G, updatePrecision]
    abel
  simp only [he] at hpos ht
  refine ⟨?_, ht.1, ?_⟩
  · filter_upwards [hpos] with n hn
    exact ⟨(Matrix.isUnit_iff_isUnit_det _).mp hn.isUnit, hn.inv⟩
  · have hm1 := tendsto_mulVec ht.2 hb
    have hm2 := tendsto_mulVec ht.1 (tendsto_mulVec hGis (tendsto_mulVec (tendsto_const_nhds (x := M.A)) ha))
    have hmean := hm1.add hm2
    simp only [one_mulVec, zero_mulVec, add_zero] at hmean
    convert hmean using 1
    ext n
    simp only [dkfStep, G, mulVec_add, mulVec_mulVec]

/-- The same limits expressed through the predictive Gaussian parameters. -/
theorem dkf_limits_of_prediction_limits {d : ℕ} (M : Model d)
    (a b' : ℕ+ → State d) (V U : ℕ+ → Covariance d)
    (hV : ∀ n, (V n).PosDef) (hU : ∀ n, (U n).PosDef)
    {c b : State d} {G₀ : Covariance d} (hG₀ : G₀.PosDef)
    (ha : Tendsto (fun n => M.A *ᵥ a n) atTop (𝓝 c))
    (hb : Tendsto b' atTop (𝓝 b))
    (hGs : Tendsto (fun n => predictedCovariance M (V n)) atTop (𝓝 G₀)) (hUs : Tendsto U atTop (𝓝 0)) :
    (∀ᶠ n in atTop, ValidStep M ⟨a n, V n⟩ ⟨b' n, U n⟩) ∧
    Tendsto (fun n => (dkfStep M ⟨a n, V n⟩ ⟨b' n, U n⟩).covariance)
      atTop (𝓝 0) ∧
    Tendsto (fun n => (dkfStep M ⟨a n, V n⟩ ⟨b' n, U n⟩).mean)
      atTop (𝓝 b) := by
  let G := fun n => predictedCovariance M (V n)
  let D := fun n => (G n)⁻¹ - M.S⁻¹
  have hGis : Tendsto (fun n => (G n)⁻¹) atTop (𝓝 G₀⁻¹) :=
    matrix_inv_tendsto ((Matrix.isUnit_iff_isUnit_det G₀).mp hG₀.isUnit) hGs
  have hDs : Tendsto D atTop (𝓝 (G₀⁻¹ - M.S⁻¹)) := hGis.sub tendsto_const_nhds
  have hDh n : (D n).IsHermitian :=
    (predictedCovariance_posDef M (hV n).posSemidef).inv.isHermitian.sub M.S_posDef.inv.isHermitian
  have hpos := perturbation_posDef_eventually U D hU hDh hUs hDs
  have ht := perturbation_inverse_tendsto U D hU hUs hDs
  have he n : (U n)⁻¹ + D n = updatePrecision M (V n) (U n) := by
    dsimp [D, G, updatePrecision]
    abel
  simp only [he] at hpos ht
  refine ⟨?_, ht.1, ?_⟩
  · filter_upwards [hpos] with n hn
    exact ⟨(Matrix.isUnit_iff_isUnit_det _).mp hn.isUnit, hn.inv⟩
  · have hm1 := tendsto_mulVec ht.2 hb
    have hm2 := tendsto_mulVec ht.1 (tendsto_mulVec hGis ha)
    have hmean := hm1.add hm2
    simp only [one_mulVec, zero_mulVec, add_zero] at hmean
    convert hmean using 1
    ext n
    simp only [dkfStep, G, mulVec_add, mulVec_mulVec]


end DKFAsymptotics.Proof
end

-- Solutions.NormalizeConvergence
section
open MeasureTheory Filter Matrix
open scoped Topology ENNReal
namespace DKFAsymptotics.Proof
variable {d : ℕ}

theorem normalized_distance_le {f g : Density d}
    (hf : Integrable f volume) (hg : Integrable g volume) (a b : ℝ) :
    (l1Distance (fun z => f z / a) (fun z => g z / b)).toReal ≤
      |a⁻¹| * (l1Distance f g).toReal + |a⁻¹ - b⁻¹| * (l1Norm g).toReal := by
  rw [l1Distance_toReal (hf.div_const _) (hg.div_const _), l1Distance_toReal hf hg,
    l1Norm_toReal hg.1, ← integral_const_mul, ← integral_const_mul]
  have h1 := (hf.sub hg).norm.const_mul |a⁻¹|
  have h2 := hg.norm.const_mul |a⁻¹ - b⁻¹|
  have ha := integral_add h1 h2
  simp only [Pi.sub_apply] at ha
  rw [← ha]
  apply integral_mono ((hf.div_const _).sub (hg.div_const _)).norm (h1.add h2)
  intro z
  simp only [Pi.sub_apply, Pi.add_apply]
  have he : f z / a - g z / b = a⁻¹ * (f z - g z) + (a⁻¹ - b⁻¹) * g z := by
    simp only [div_eq_mul_inv]
    ring
  rw [he]
  exact (norm_add_le _ _).trans_eq (by rw [norm_mul, norm_mul]; rfl)

theorem normalized_l1_tendsto {f g : ℕ+ → Density d}
    (hf : ∀ n, Integrable (f n) volume) (hg : ∀ n, Integrable (g n) volume)
    (hgn : ∀ n, ∀ᵐ z ∂volume, 0 ≤ g n z)
    {a : ℝ} (ha : 0 < a)
    (hmf : Tendsto (fun n => ∫ z, f n z ∂volume) atTop (𝓝 a))
    (hmg : Tendsto (fun n => ∫ z, g n z ∂volume) atTop (𝓝 a))
    (hd : Tendsto (fun n => (l1Distance (f n) (g n)).toReal) atTop (𝓝 0)) :
    Tendsto (fun n => (l1Distance
      (fun z => f n z / (∫ y, f n y ∂volume))
      (fun z => g n z / (∫ y, g n y ∂volume))).toReal) atTop (𝓝 0) := by
  have hnorm n : (l1Norm (g n)).toReal = ∫ z, g n z ∂volume := by
    rw [l1Norm_eq_integral (hg n) (hgn n), ENNReal.toReal_ofReal]
    exact integral_nonneg_of_ae (hgn n)
  have hb := ((hmf.inv₀ ha.ne').abs.mul hd).add
    (((hmf.inv₀ ha.ne').sub (hmg.inv₀ ha.ne')).abs.mul hmg)
  apply squeeze_zero (fun _ => ENNReal.toReal_nonneg)
    (fun n => (normalized_distance_le (hf n) (hg n) _ _).trans_eq ?_)
    (by simpa using hb)
  rw [hnorm]
  simp only [abs_inv]

end DKFAsymptotics.Proof
end

-- Solutions.KernelStability
section
open MeasureTheory Filter Matrix
open scoped Topology ENNReal
namespace DKFAsymptotics.Proof
variable {d : ℕ}

theorem kernelProduct_distance_le (M : Model d) {s s' u u' : Density d}
    (hs : IsPDF s) (hs' : IsPDF s') (hu : IsPDF u) (hu' : IsPDF u') :
    (l1Distance (fun z => u z * predictDensity M s z)
      (fun z => u' z * predictDensity M s' z)).toReal ≤
    gaussianPDF 0 M.Γ 0 * (l1Distance u u').toReal +
      gaussianPDF 0 M.Γ 0 * (l1Distance s s').toReal := by
  let β := gaussianPDF 0 M.Γ 0
  let δ := (l1Distance s s').toReal
  have hδ : 0 ≤ δ := ENNReal.toReal_nonneg
  have hβ : 0 ≤ β := (gaussianPDF_pos 0 M.Γ_posDef 0).le
  rw [l1Distance_toReal (kernelProduct_integrable M hs hu) (kernelProduct_integrable M hs' hu')]
  have hi1 := (hu.2.1.sub hu'.2.1).norm.const_mul β
  have hi2 := hu'.2.1.norm.const_mul (β * δ)
  calc
    _ ≤ ∫ z, β * ‖u z - u' z‖ + (β * δ) * ‖u' z‖ ∂volume := by
      apply integral_mono_ae
        ((kernelProduct_integrable M hs hu).sub (kernelProduct_integrable M hs' hu')).norm
        (hi1.add hi2)
      filter_upwards [] with z
      simp only [Pi.sub_apply]
      have he : u z * predictDensity M s z - u' z * predictDensity M s' z =
        (u z - u' z) * predictDensity M s z +
          u' z * (predictDensity M s z - predictDensity M s' z) := by ring
      rw [he]
      apply (norm_add_le _ _).trans
      rw [norm_mul, norm_mul]
      have hp : ‖predictDensity M s z‖ ≤ β := by
        simpa only [l1Norm_toReal_pdf hs, mul_one] using predict_norm_le M hs.2.1 z
      have hdiff := predict_difference_le M hs.2.1 hs'.2.1 z
      calc
        _ ≤ ‖u z - u' z‖ * β + ‖u' z‖ * (β * δ) := by gcongr
        _ = _ := by simp only [Pi.add_apply]; ring
    _ = β * (l1Distance u u').toReal + β * δ := by
      have hadd := integral_add hi1 hi2
      simp only [Pi.sub_apply] at hadd
      rw [hadd, integral_const_mul, integral_const_mul,
        ← l1Distance_toReal hu.2.1 hu'.2.1, ← l1Norm_toReal hu'.2.1.1,
        l1Norm_toReal_pdf hu', mul_one]

theorem kernelProduct_normalized_tendsto (M : Model d)
    {s s' u u' : ℕ+ → Density d}
    (hs : ∀ n, IsPDF (s n)) (hs' : ∀ n, IsPDF (s' n))
    (hu : ∀ n, IsPDF (u n)) (hu' : ∀ n, IsPDF (u' n))
    (P : ProbabilityMeasure (State d)) (b : State d)
    (hws : Weakly s P) (hws' : Weakly s' P)
    (hwu : Weakly u (Measure.dirac b)) (hwu' : Weakly u' (Measure.dirac b))
    (hds : Tendsto (fun n => l1Distance (s n) (s' n)) atTop (𝓝 0))
    (hdu : Tendsto (fun n => l1Distance (u n) (u' n)) atTop (𝓝 0)) :
    Tendsto (fun n => (l1Distance
      (fun z => u n z * predictDensity M (s n) z /
        (∫ y, u n y * predictDensity M (s n) y ∂volume))
      (fun z => u' n z * predictDensity M (s' n) z /
        (∫ y, u' n y * predictDensity M (s' n) y ∂volume))).toReal) atTop (𝓝 0) := by
  apply normalized_l1_tendsto
    (fun n => kernelProduct_integrable M (hs n) (hu n))
    (fun n => kernelProduct_integrable M (hs' n) (hu' n))
    (fun n => ?_) (kernel_limit_pos M P b)
    (kernelProduct_mass_tendsto M hs hu P b hws hwu)
    (kernelProduct_mass_tendsto M hs' hu' P b hws' hwu')
  · have hsr := (l1Distance_zero_tendsto_iff (fun n => (hs n).2.1) (fun n => (hs' n).2.1)).mp hds
    have hur := (l1Distance_zero_tendsto_iff (fun n => (hu n).2.1) (fun n => (hu' n).2.1)).mp hdu
    apply squeeze_zero (fun _ => ENNReal.toReal_nonneg)
      (fun n => kernelProduct_distance_le M (hs n) (hs' n) (hu n) (hu' n))
    simpa using (hur.const_mul (gaussianPDF 0 M.Γ 0)).add (hsr.const_mul (gaussianPDF 0 M.Γ 0))
  · filter_upwards [(hu' n).1] with z hz
    exact mul_nonneg hz (predict_nonneg M (hs' n).1 z)

end DKFAsymptotics.Proof
end

-- Solutions.Reweighting
section
open MeasureTheory Filter Matrix
open scoped Topology ENNReal
namespace DKFAsymptotics.Proof
variable {d : ℕ}

/-- The two outer terms in the five-term decomposition (B.2), on either side. -/
theorem weakly_dirac_reweight {f : ℕ+ → Density d} {b : State d}
    (hf : ∀ n, IsPDF (f n)) (hw : Weakly f (Measure.dirac b))
    (g : BoundedContinuousFunction (State d) ℝ) (hg : ∀ z, 0 ≤ g z)
    (hgb : 0 < g b) :
    Tendsto (fun n => (l1Distance (f n)
      (fun z => f n z * g z / (∫ y, f n y * g y ∂volume))).toReal) atTop (𝓝 0) := by
  let m := fun n => ∫ z, f n z * g z ∂volume
  have hi n := bounded_test_integrable (hf n).2.1 g
  have hm : Tendsto m atTop (𝓝 (g b)) := by
    have ht := hw g
    simp only [integral_dirac] at ht
    simpa only [m, integral_densityMeasure (hf _)] using ht
  let F : BoundedContinuousFunction (State d) ℝ :=
    BoundedContinuousFunction.ofNormedAddCommGroup (fun z => |1 - g z / g b|)
      (by fun_prop) (1 + ‖g‖ / |g b|) (fun z => by
        rw [Real.norm_eq_abs, abs_abs]
        calc
          _ ≤ |(1 : ℝ)| + |g z / g b| := abs_sub _ _
          _ ≤ 1 + ‖g‖ / |g b| := by
            rw [abs_one, abs_div]
            gcongr
            exact g.norm_coe_le_norm z)
  have hF : F b = 0 := by
    change |1 - g b / g b| = 0
    rw [div_self hgb.ne', sub_self, abs_zero]
  have hfirst : Tendsto (fun n => ∫ z, f n z * F z ∂volume) atTop (𝓝 0) := by
    have ht := hw F
    simp only [integral_dirac, hF] at ht
    simpa only [integral_densityMeasure (hf _)] using ht
  have hsecond : Tendsto (fun n => |1 / g b - 1 / m n| * m n) atTop (𝓝 0) := by
    have ht := ((tendsto_const_nhds (x := 1 / g b)).sub
      ((tendsto_const_nhds (x := (1 : ℝ))).div hm hgb.ne')).abs.mul hm
    simpa using ht
  apply squeeze_zero (fun _ => ENNReal.toReal_nonneg)
    (g := fun n => (∫ z, f n z * F z ∂volume) + |1 / g b - 1 / m n| * m n)
  · intro n
    rw [l1Distance_toReal (hf n).2.1 ((hi n).div_const _)]
    have hnorm : (∫ z, ‖f n z * g z‖ ∂volume) = m n := by
      apply integral_congr_ae
      filter_upwards [(hf n).1] with z hz using Real.norm_of_nonneg (mul_nonneg hz (hg z))
    rw [← hnorm, ← integral_const_mul, ← integral_add (bounded_test_integrable (hf n).2.1 F)
      ((hi n).norm.const_mul _)]
    apply integral_mono_ae ((hf n).2.1.sub ((hi n).div_const _)).norm
      ((bounded_test_integrable (hf n).2.1 F).add ((hi n).norm.const_mul _))
    filter_upwards [(hf n).1] with z hz
    have he : f n z - f n z * g z / m n =
        f n z * (1 - g z / g b) + (1 / g b - 1 / m n) * (f n z * g z) := by
      simp only [div_eq_mul_inv]
      ring
    simp only [Pi.sub_apply, Pi.add_apply, hnorm]
    change ‖f n z - f n z * g z / m n‖ ≤ _
    rw [he]
    calc
      _ ≤ ‖f n z * (1 - g z / g b)‖ + ‖(1 / g b - 1 / m n) * (f n z * g z)‖ := norm_add_le _ _
      _ = _ := by
        simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg hz]
        rfl
  · simpa using hfirst.add hsecond

end DKFAsymptotics.Proof
end

-- Solutions.UpdateCancellation
section
open MeasureTheory Filter Matrix
open scoped Topology ENNReal
namespace DKFAsymptotics.Proof
variable {d : ℕ}

theorem update_times_prior (M : Model d) (s u : Density d) (z : State d) :
    updateDensity M s u z * prior M z =
      (u z * predictDensity M s z) / (l1Norm (updateWeight M s u)).toReal := by
  have hp : prior M z ≠ 0 := (gaussianPDF_pos 0 M.S_posDef z).ne'
  unfold updateDensity updateWeight
  field_simp

theorem normalized_update_times_prior (M : Model d) {s u : Density d}
    (hd : UpdateDefined M s u) :
    (fun z => updateDensity M s u z * prior M z /
      (∫ y, updateDensity M s u y * prior M y ∂volume)) =
    fun z => (u z * predictDensity M s z) / (∫ y, u y * predictDensity M s y ∂volume) := by
  have hn : (l1Norm (updateWeight M s u)).toReal ≠ 0 :=
    (ENNReal.toReal_pos hd.2.1.ne' hd.2.2.ne).ne'
  funext z
  simp_rw [update_times_prior]
  rw [integral_div]
  exact div_div_div_cancel_right₀ hn _ _

theorem weakly_eventuallyEq {f g : ℕ+ → Density d} {P : Measure (State d)}
    (he : ∀ᶠ n in atTop, f n = g n) (hw : Weakly f P) : Weakly g P := by
  intro F
  apply (hw F).congr'
  filter_upwards [he] with n hn
  rw [hn]

end DKFAsymptotics.Proof
end

-- Solutions.Lemma1
section
open MeasureTheory Filter Matrix
open scoped Topology ENNReal

namespace DKFAsymptotics.Proof

theorem lemma1 {d : ℕ} [NeZero d] (M : Model d)
    (a b' : ℕ+ → State d) (V U : ℕ+ → Covariance d)
    (hV : ∀ n, (V n).PosDef) (hU : ∀ n, (U n).PosDef)
    (P : ProbabilityMeasure (State d)) (b : State d) :
    (∀ n, ValidStep M ⟨a n, V n⟩ ⟨b' n, U n⟩ →
      UpdateDefined M (gaussianPDF (a n) (V n)) (gaussianPDF (b' n) (U n)) ∧
      (∀ z, updateDensity M (gaussianPDF (a n) (V n)) (gaussianPDF (b' n) (U n)) z =
        gaussianPDF (dkfStep M ⟨a n, V n⟩ ⟨b' n, U n⟩).mean
          (dkfStep M ⟨a n, V n⟩ ⟨b' n, U n⟩).covariance z) ∧
      IsPDF (updateDensity M (gaussianPDF (a n) (V n)) (gaussianPDF (b' n) (U n)))) ∧
    (Weakly (fun n => gaussianPDF (a n) (V n)) P →
      Weakly (fun n => gaussianPDF (b' n) (U n)) (Measure.dirac b) →
      (∀ᶠ n in atTop,
        ValidStep M ⟨a n, V n⟩ ⟨b' n, U n⟩ ∧
        UpdateDefined M (gaussianPDF (a n) (V n)) (gaussianPDF (b' n) (U n)) ∧
        IsGaussianPDF (updateDensity M (gaussianPDF (a n) (V n))
          (gaussianPDF (b' n) (U n)))) ∧
      Weakly (fun n => updateDensity M (gaussianPDF (a n) (V n))
        (gaussianPDF (b' n) (U n))) (Measure.dirac b))  := by
  classical
  have hexact n := gaussian_update_exact M (a n) (b' n) (hV n) (hU n)
  refine ⟨fun n hn => hexact n hn, ?_⟩
  intro hs hu
  obtain ⟨c, G, hG, hc, hGs, _⟩ := predicted_gaussian_parameters M a V hV P hs
  obtain ⟨hb, hUs⟩ := gaussian_parameters_of_weakly_dirac b' U hU b hu
  obtain ⟨hvalid, hcov, hmean⟩ :=
    dkf_limits_of_prediction_limits M a b' V U hV hU hG hc hb hGs hUs
  have hevent : ∀ᶠ n in atTop,
      ValidStep M ⟨a n, V n⟩ ⟨b' n, U n⟩ ∧
      UpdateDefined M (gaussianPDF (a n) (V n)) (gaussianPDF (b' n) (U n)) ∧
      IsGaussianPDF (updateDensity M (gaussianPDF (a n) (V n))
        (gaussianPDF (b' n) (U n))) := by
    filter_upwards [hvalid] with n hn
    obtain ⟨hd, he, hp⟩ := hexact n hn
    exact ⟨hn, hd, hp, _, _, hn.2, ae_of_all _ he⟩
  refine ⟨hevent, ?_⟩
  let C : ℕ+ → Covariance d := fun n =>
    if ValidStep M ⟨a n, V n⟩ ⟨b' n, U n⟩ then
      (dkfStep M ⟨a n, V n⟩ ⟨b' n, U n⟩).covariance else 1
  have hC n : (C n).PosDef := by
    dsimp [C]
    split_ifs with hn
    · exact hn.2
    · exact Matrix.PosDef.one
  have hCe : ∀ᶠ n in atTop, C n =
      (dkfStep M ⟨a n, V n⟩ ⟨b' n, U n⟩).covariance := by
    filter_upwards [hvalid] with n hn
    simp only [C, if_pos hn]
  have hC0 : Tendsto C atTop (𝓝 0) := hcov.congr' (hCe.mono fun _ hn => hn.symm)
  have hw := gaussian_weakly_dirac hC hmean hC0
  apply weakly_eventuallyEq _ hw
  filter_upwards [hvalid, hCe] with n hn heC
  rw [heC]
  exact (funext (hexact n hn).2.1).symm

end DKFAsymptotics.Proof
end

-- Solutions.C3C4
section
open MeasureTheory Filter Matrix
open scoped Topology ENNReal

namespace DKFAsymptotics.Proof

/-- Proof of C3 and C4 to the Gaussian equation and convergence in Lemma 1. -/
theorem C3C4_of_lemma1 {d : ℕ} [NeZero d] (M : Model d) (D : Problem M)
    (h : Assumptions M D) :
    (∀ᶠ n in atTop, UpdateDefined M (D.s' n) (D.u' n) ∧
      IsGaussianPDF (D.p' M n)) ∧
    Weakly (D.p' M) (Measure.dirac D.b) := by
  choose a V hV hs using fun n => (D.s'_gaussian n).2
  choose b' U hU hu using fun n => (D.u'_gaussian n).2
  have hsweak := (weakly_congr hs).mp (C1 M D h)
  have huweak := (weakly_congr hu).mp (C2 M D h)
  obtain ⟨hevent, hweak⟩ :=
    (DKFAsymptotics.Proof.lemma1 M a b' V U hV hU D.P D.b).2 hsweak huweak
  have hp : ∀ n, D.p' M n =ᵐ[volume]
      updateDensity M (gaussianPDF (a n) (V n)) (gaussianPDF (b' n) (U n)) :=
    fun n => updateDensity_congr M (hs n) (hu n)
  refine ⟨?_, (weakly_congr hp).mpr hweak⟩
  filter_upwards [hevent] with n hn
  exact ⟨(updateDefined_congr M (hs n) (hu n)).mpr hn.2.1,
    (isGaussianPDF_congr (hp n)).mpr hn.2.2⟩

end DKFAsymptotics.Proof
end

open MeasureTheory Filter Matrix DKFAsymptotics
open scoped Topology ENNReal

theorem solution {d : ℕ} [NeZero d] (M : Model d) (D : Problem M)
    (h : Assumptions M D) :
    Weakly (D.p' M) (Measure.dirac D.b) := by
  exact (DKFAsymptotics.Proof.C3C4_of_lemma1 M D h).2
