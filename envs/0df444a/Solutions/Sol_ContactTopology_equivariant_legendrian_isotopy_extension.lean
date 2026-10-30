-- Prove2me | solution 1 for ContactTopology.equivariant_legendrian_isotopy_extension
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-29T23:54:48.975518+00:00
-- url     : https://prove2.me/submissions/a09dc38e-e5c2-4ea5-b999-55f4af927010

import Definitions.Def_BirkhoffGlobalSection_SphereContact
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Support
import Theorems.Thm_ContactCalculus_exterior_pairing_pullback
import Theorems.Thm_FlowCalculus_compact_supported_flow_preserves_regular_level
import Theorems.Thm_FlowCalculus_exists_unique_global_trajectory_of_compact_support
import Theorems.Thm_FlowCalculus_smooth_flow_spatial_derivative_injective
import Theorems.Thm_FlowCalculus_uniform_spatial_lipschitz_of_compact_support
import Theorems.Thm_GrayStability_pullback_family_hasDerivAt
import Theorems.Thm_ParameterizedCalculus_smooth_scalar_linear_transport
import Theorems.Thm_SmoothJetExtension_moving_circle_first_jet_extension


-- Reused from the accepted transverse contact-generator proof, submission 9a237cfc-145c-40c8-9d8c-9d9c0ca99ce5.






namespace BirkhoffGlobalSection.ContactGenerator
open BirkhoffGlobalSection
noncomputable section

def J (v : Phase) : Phase := ![v 2, v 3, -v 0, -v 1]

def contactField (h : ℝ) (g y : Phase) : Phase :=
  J g + (2 * h - phaseDot y g) • J y + phaseDot (J y) g • y

def contactFieldDerivative (h : ℝ) (g y v b : Phase) : Phase :=
  J b + (phaseDot g v - phaseDot y b) • J y +
    (2 * h - phaseDot y g) • J v +
    (phaseDot (J v) g + phaseDot (J y) b) • y + phaseDot (J y) g • v

lemma contact_eq_dot (y v : Phase) :
    phaseRadialContact y v = phaseDot (J y) v / 2 := by
  simp [phaseRadialContact, phaseSymplecticForm, phaseDot, J]; ring

lemma contactField_tangent (h : ℝ) (g y : Phase) (hy : phaseDot y y = 1) :
    phaseDot y (contactField h g y) = 0 := by
  simp only [phaseDot] at hy
  simp [contactField, phaseDot, J]
  linear_combination (y 2 * g 0 + y 3 * g 1 - y 0 * g 2 - y 1 * g 3) * hy

lemma contactField_value (h : ℝ) (g y : Phase) (hy : phaseDot y y = 1) :
    phaseRadialContact y (contactField h g y) = h := by
  rw [contact_eq_dot]
  simp only [phaseDot] at hy
  simp [contactField, phaseDot, J]
  linear_combination (h - (y 0 * g 0 + y 1 * g 1 + y 2 * g 2 + y 3 * g 3) / 2) * hy

/-- The differential contact identity is algebraic once the scalar Hamiltonian's
first derivative is represented by `g`. No Hessian symmetry assumption is needed. -/
lemma contactField_lie (h : ℝ) (g y v b : Phase)
    (hy : phaseDot y y = 1) (hv : phaseDot y v = 0) :
    phaseRadialContact (contactField h g y) v +
      phaseRadialContact y (contactFieldDerivative h g y v b) =
        (2 * phaseDot (J y) g) * phaseRadialContact y v := by
  simp only [contact_eq_dot]
  simp only [phaseDot] at hy hv
  simp [contactField, contactFieldDerivative, phaseDot, J, Matrix.vecHead, Matrix.vecTail, Pi.smul_apply]
  linear_combination
    ((g 0 * v 0 + g 1 * v 1 + g 2 * v 2 + g 3 * v 3 -
      (y 0 * b 0 + y 1 * b 1 + y 2 * b 2 + y 3 * b 3)) / 2) * hy

/-- A compatible first jet of the Hamiltonian reproduces the prescribed knot velocity. -/
lemma contactField_prescribed (y V : Phase) (m : ℝ)
    (hy : phaseDot y y = 1) (hV : phaseDot y V = 0) :
    contactField (phaseRadialContact y V) (-J V + (m / 2) • J y) y = V := by
  simp only [phaseDot] at hy hV
  ext i; fin_cases i <;>
    simp [contactField, contact_eq_dot, phaseDot, J] <;>
    linear_combination (m / 2) * (y _ * hy) - y _ * hV

end
end BirkhoffGlobalSection.ContactGenerator

namespace BirkhoffGlobalSection.ContactGenerator
open BirkhoffGlobalSection
open scoped ContDiff
noncomputable section

def dotCLM (g : Phase) : Phase →L[ℝ] ℝ := ∑ i, g i • ContinuousLinearMap.proj i

lemma dotCLM_apply (g v : Phase) : dotCLM g v = phaseDot g v := by
  simp [dotCLM, phaseDot, Fin.sum_univ_four]

lemma phaseDot_hasDerivAt {q g : ℝ → Phase} {v b : Phase} {t : ℝ}
    (hq : HasDerivAt q v t) (hg : HasDerivAt g b t) :
    HasDerivAt (fun s => phaseDot (q s) (g s))
      (phaseDot v (g t) + phaseDot (q t) b) t := by
  have h := fun i => hasDerivAt_pi.mp hq i
  have k := fun i => hasDerivAt_pi.mp hg i
  have hd := ((((h 0).mul (k 0)).add ((h 1).mul (k 1))).add ((h 2).mul (k 2))).add ((h 3).mul (k 3))
  apply hd.congr_deriv
  simp only [phaseDot]
  ring

lemma J_hasDerivAt {g : ℝ → Phase} {b : Phase} {t : ℝ} (hg : HasDerivAt g b t) :
    HasDerivAt (fun s => J (g s)) (J b) t := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hasDerivAt_pi.mp hg 2
  · exact hasDerivAt_pi.mp hg 3
  · exact (hasDerivAt_pi.mp hg 0).neg
  · exact (hasDerivAt_pi.mp hg 1).neg

lemma contactField_hasDerivAt {h : ℝ → ℝ} {g q : ℝ → Phase}
    {v b : Phase} {t : ℝ}
    (hh : HasDerivAt h (phaseDot (g t) v) t)
    (hg : HasDerivAt g b t) (hq : HasDerivAt q v t) :
    HasDerivAt (fun s => contactField (h s) (g s) (q s))
      (contactFieldDerivative (h t) (g t) (q t) v b) t := by
  have hc := (hh.const_mul 2).sub (phaseDot_hasDerivAt hq hg)
  have hd := (J_hasDerivAt hg).add (hc.smul (J_hasDerivAt hq))
  have hs := hd.add ((phaseDot_hasDerivAt (J_hasDerivAt hq) hg).smul hq)
  convert! hs using 1
  ext i
  fin_cases i <;> simp [contactFieldDerivative, phaseDot, J, Matrix.vecHead, Matrix.vecTail] <;> ring

lemma contactField_fderiv_apply (H : Phase → ℝ) (g : Phase → Phase) (y v : Phase)
    (hH : HasFDerivAt H (dotCLM (g y)) y)
    (hg : DifferentiableAt ℝ g y)
    (hF : DifferentiableAt ℝ (fun z => contactField (H z) (g z) z) y) :
    fderiv ℝ (fun z => contactField (H z) (g z) z) y v =
      contactFieldDerivative (H y) (g y) y v (fderiv ℝ g y v) := by
  let c : ℝ → Phase := fun s => y + s • v
  have hc : HasDerivAt c v 0 := by
    convert! (hasDerivAt_const (0 : ℝ) y).add ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1 <;> simp [c]
  have hH' : HasFDerivAt H (dotCLM (g y)) (c 0) := by simpa only [c, zero_smul, add_zero] using hH
  have hg' : DifferentiableAt ℝ g (c 0) := by simpa only [c, zero_smul, add_zero] using hg
  have hF' : DifferentiableAt ℝ (fun z => contactField (H z) (g z) z) (c 0) := by
    simpa only [c, zero_smul, add_zero] using hF
  have hdH : HasDerivAt (fun s => H (c s)) (phaseDot (g (c 0)) v) 0 := by
    simpa only [Function.comp_def, dotCLM_apply, c, zero_smul, add_zero] using hH'.comp_hasDerivAt 0 hc
  have hdg := hg'.hasFDerivAt.comp_hasDerivAt 0 hc
  have hd := contactField_hasDerivAt hdH hdg hc
  have hdf := hF'.hasFDerivAt.comp_hasDerivAt 0 hc
  have he := hdf.unique hd
  simpa only [Function.comp_def, c, zero_smul, add_zero] using he

lemma contactField_lie_at (H : Phase → ℝ) (g : Phase → Phase) (y v : Phase)
    (hH : HasFDerivAt H (dotCLM (g y)) y)
    (hg : DifferentiableAt ℝ g y)
    (hF : DifferentiableAt ℝ (fun z => contactField (H z) (g z) z) y)
    (hy : phaseDot y y = 1) (hv : phaseDot y v = 0) :
    phaseRadialContact (contactField (H y) (g y) y) v +
      phaseRadialContact y (fderiv ℝ (fun z => contactField (H z) (g z) z) y v) =
        (2 * phaseDot (J y) (g y)) * phaseRadialContact y v := by
  rw [contactField_fderiv_apply H g y v hH hg hF]
  exact contactField_lie _ _ _ _ _ hy hv

lemma prescribed_gradient_pairing (q V w : Phase) (m : ℝ) :
    phaseDot (-J V + (m / 2) • J q) w =
      -2 * phaseRadialContact V w + m * phaseRadialContact q w := by
  simp [contact_eq_dot, phaseDot, J]
  ring

lemma compatible_gradient_pairing (q V z : Phase) (hs : ℝ)
    (hden : phaseRadialContact q z ≠ 0) :
    phaseDot (-J V + ((hs + 2 * phaseRadialContact V z) / phaseRadialContact q z / 2) • J q) z = hs := by
  rw [prescribed_gradient_pairing]
  field_simp [hden]
  ring

end
end BirkhoffGlobalSection.ContactGenerator

namespace BirkhoffGlobalSection.ContactGenerator
open BirkhoffGlobalSection Set
open scoped ContDiff
noncomputable section

lemma phaseDot_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → Phase} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun p => phaseDot (f p) (g p)) := by
  have h := fun i => (contDiff_apply ℝ ℝ i).comp hf
  have k := fun i => (contDiff_apply ℝ ℝ i).comp hg
  exact ((((h 0).mul (k 0)).add ((h 1).mul (k 1))).add ((h 2).mul (k 2))).add ((h 3).mul (k 3))

lemma J_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → Phase} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (fun p => J (f p)) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact (contDiff_apply ℝ ℝ 2).comp hf
  · exact (contDiff_apply ℝ ℝ 3).comp hf
  · exact ((contDiff_apply ℝ ℝ 0).comp hf).neg
  · exact ((contDiff_apply ℝ ℝ 1).comp hf).neg

lemma contact_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → Phase} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun p => phaseRadialContact (f p) (g p)) := by
  simpa only [contact_eq_dot] using (phaseDot_contDiff (J_contDiff hf) hg).div_const 2

lemma dotCLM_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → Phase} (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (fun p => dotCLM (g p)) := by
  unfold dotCLM
  apply ContDiff.sum
  intro i hi
  exact ((contDiff_apply ℝ ℝ i).comp hg).smul contDiff_const

def spatialGradient (H : ℝ × Phase → ℝ) (p : ℝ × Phase) : Phase :=
  fun i => fderiv ℝ H p (0, Pi.single i 1)

lemma spatialGradient_contDiff {H : ℝ × Phase → ℝ} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (spatialGradient H) := by
  apply contDiff_pi.mpr
  intro i
  exact (hH.fderiv_right (by simp)).clm_apply contDiff_const

lemma clm_spatial_coordinates (L : (ℝ × Phase) →L[ℝ] ℝ) (v : Phase) :
    L (0, v) = phaseDot (fun i => L (0, Pi.single i 1)) v := by
  have he : (0, v) = ∑ i : Fin 4, v i • ((0 : ℝ), Pi.single i (1 : ℝ)) := by
    apply Prod.ext
    · simp [Fin.sum_univ_four]
    · ext j; fin_cases j <;> simp [Fin.sum_univ_four]
  rw [he, map_sum]
  simp only [map_smul]
  simp [phaseDot, Fin.sum_univ_four]
  ring

lemma slice_hasFDerivAt {H : ℝ × Phase → ℝ} (hH : ContDiff ℝ ∞ H) (t : ℝ) (y : Phase) :
    HasFDerivAt (fun z => H (t, z)) (dotCLM (spatialGradient H (t, y))) y := by
  have hd := ((hH.differentiable (by simp) (t,y)).hasFDerivAt).comp y
    ((hasFDerivAt_const t y).prodMk (hasFDerivAt_id y))
  apply hd.congr_fderiv
  ext v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.zero_apply, ContinuousLinearMap.id_apply, dotCLM_apply]
  exact clm_spatial_coordinates _ v

lemma hamiltonian_field_contDiff {H : ℝ × Phase → ℝ} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (fun p : ℝ × Phase => contactField (H p) (spatialGradient H p) p.2) := by
  have hg := spatialGradient_contDiff hH
  exact ((J_contDiff hg).add (((contDiff_const.mul hH).sub (phaseDot_contDiff contDiff_snd hg)).smul
    (J_contDiff contDiff_snd))).add ((phaseDot_contDiff (J_contDiff contDiff_snd) hg).smul contDiff_snd)

lemma hamiltonian_factor_contDiff {H : ℝ × Phase → ℝ} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (fun p : ℝ × Phase => 2 * phaseDot (J p.2) (spatialGradient H p)) :=
  contDiff_const.mul (phaseDot_contDiff (J_contDiff contDiff_snd) (spatialGradient_contDiff hH))

lemma hamiltonian_field_lie {H : ℝ × Phase → ℝ} (hH : ContDiff ℝ ∞ H)
    (t : ℝ) (y v : Phase) (hy : phaseDot y y = 1) (hv : phaseDot y v = 0) :
    phaseRadialContact (contactField (H (t,y)) (spatialGradient H (t,y)) y) v +
      phaseRadialContact y (fderiv ℝ
        (fun z => contactField (H (t,z)) (spatialGradient H (t,z)) z) y v) =
      (2 * phaseDot (J y) (spatialGradient H (t,y))) * phaseRadialContact y v := by
  exact contactField_lie_at (fun z => H (t,z)) (fun z => spatialGradient H (t,z)) y v
    (slice_hasFDerivAt hH t y)
    (((spatialGradient_contDiff hH).comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) y)
    (((hamiltonian_field_contDiff hH).comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) y)
    hy hv

lemma hamiltonian_field_compact_support {H : ℝ × Phase → ℝ} (hHc : HasCompactSupport H) :
    ∃ C : Set Phase, IsCompact C ∧ ∀ t y, y ∉ C →
      contactField (H (t,y)) (spatialGradient H (t,y)) y = 0 := by
  refine ⟨Prod.snd '' tsupport H, hHc.isCompact.image continuous_snd, ?_⟩
  intro t y hy
  have hp : (t,y) ∉ tsupport H := fun hp => hy ⟨(t,y), hp, rfl⟩
  have hz : H (t,y) = 0 := image_eq_zero_of_notMem_tsupport hp
  have hd := fderiv_of_notMem_tsupport (𝕜 := ℝ) hp
  have hg : spatialGradient H (t,y) = 0 := by ext i; simp [spatialGradient, hd]
  simp [contactField, hz, hg, J, phaseDot]

end
end BirkhoffGlobalSection.ContactGenerator

namespace ContactTopology.LegendrianExtension
open BirkhoffGlobalSection BirkhoffGlobalSection.ContactGenerator Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

def sphereRadialForm (y : Phase) : Phase →L[ℝ] ℝ :=
  (y 2/2) • ContinuousLinearMap.proj 0+(y 3/2) • ContinuousLinearMap.proj 1-
    (y 0/2) • ContinuousLinearMap.proj 2-(y 1/2) • ContinuousLinearMap.proj 3

lemma sphereRadialForm_apply (y v : Phase) : sphereRadialForm y v = phaseRadialContact y v := by
  simp [sphereRadialForm,phaseRadialContact,phaseSymplecticForm]
  ring

lemma sphereRadialForm_contDiff : ContDiff ℝ ∞ sphereRadialForm := by
  exact (((((contDiff_apply ℝ ℝ 2).div_const 2).smul contDiff_const).add
    (((contDiff_apply ℝ ℝ 3).div_const 2).smul contDiff_const)).sub
    (((contDiff_apply ℝ ℝ 0).div_const 2).smul contDiff_const)).sub
    (((contDiff_apply ℝ ℝ 1).div_const 2).smul contDiff_const)

def sphereRadialFormLinear : Phase →L[ℝ] (Phase →L[ℝ] ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := sphereRadialForm
      map_add' := by intro u v; ext w; simp [sphereRadialForm_apply,phaseRadialContact,phaseSymplecticForm]; ring
      map_smul' := by intro a v; ext w; simp [sphereRadialForm_apply,phaseRadialContact,phaseSymplecticForm]; ring }

lemma sphereRadialForm_fderiv (y u v : Phase) :
    fderiv ℝ sphereRadialForm y u v = phaseRadialContact u v := by
  have hlin : fderiv ℝ (sphereRadialFormLinear : Phase → (Phase →L[ℝ] ℝ)) y = sphereRadialFormLinear :=
    sphereRadialFormLinear.hasFDerivAt.fderiv
  have he := congrArg (fun L : Phase →L[ℝ] (Phase →L[ℝ] ℝ) => L u) hlin
  change fderiv ℝ sphereRadialForm y u = sphereRadialForm u at he
  rw [he,sphereRadialForm_apply]

lemma fderiv_clm_eval {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : E → V →L[ℝ] ℝ) (q u : E) (v : V) (hB : DifferentiableAt ℝ B q) :
    fderiv ℝ (fun z => B z v) q u = fderiv ℝ B q u v := by
  rw [fderiv_clm_apply hB (differentiableAt_const v)]
  simp


/-- Differentiating the Legendrian condition gives the compatibility of
Hamiltonian values and prescribed first derivatives along the moving circle. -/
lemma legendrian_hamiltonian_compatibility
    (k : ℝ × Plane → Phase) (hk : ContDiff ℝ ∞ k)
    (hleg : ∀ t : ℝ, ∀ u ∈ unitCircle,
      phaseRadialContact (k (t,u)) (fderiv ℝ k (t,u) (0,circleTangent u)) = 0)
    (t : ℝ) (u : Plane) (hu : u ∈ unitCircle) :
    fderiv ℝ (fun p : ℝ × Plane =>
      phaseRadialContact (k p) (fderiv ℝ k p (1,0))) (t,u) (0,circleTangent u) =
      -2*phaseRadialContact (fderiv ℝ k (t,u) (1,0))
        (fderiv ℝ k (t,u) (0,circleTangent u)) := by
  let B : (ℝ × Plane) → ((ℝ × Plane) →L[ℝ] ℝ) := fun q =>
    (sphereRadialForm (k q)).comp (fderiv ℝ k q)
  have hB : ContDiff ℝ ∞ B :=
    (sphereRadialForm_contDiff.comp hk).clm_comp (hk.fderiv_right (by simp))
  have heval : DifferentiableAt ℝ (fun q => B q (0,circleTangent u)) (t,u) :=
    ((hB.clm_apply contDiff_const).differentiable (by simp) _)
  have hc : HasDerivAt (fun s : ℝ => (s,u)) (1,0) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t u)
  have hd := heval.hasFDerivAt.comp_hasDerivAt t hc
  have heq : (fun s : ℝ => B (s,u) (0,circleTangent u)) = fun _ => 0 := by
    funext s
    exact (sphereRadialForm_apply _ _).trans (hleg s u hu)
  change HasDerivAt (fun s : ℝ => B (s,u) (0,circleTangent u)) _ t at hd
  rw [heq] at hd
  have htime : fderiv ℝ B (t,u) (1,0) (0,circleTangent u) = 0 := by
    have hh := hd.unique (hasDerivAt_const t (0:ℝ))
    rw [fderiv_clm_eval B (t,u) (1,0) (0,circleTangent u)
      (hB.differentiable (by simp) _)] at hh
    exact hh
  have hspace : fderiv ℝ B (t,u) (0,circleTangent u) (1,0) =
      fderiv ℝ (fun p : ℝ × Plane => phaseRadialContact (k p)
        (fderiv ℝ k p (1,0))) (t,u) (0,circleTangent u) := by
    rw [← fderiv_clm_eval B (t,u) (0,circleTangent u) (1,0)
      (hB.differentiable (by simp) _)]
    congr 2
    funext p
    exact sphereRadialForm_apply _ _
  have hp := ContactCalculus.exterior_pairing_pullback sphereRadialForm k (t,u)
    (1,0) (0,circleTangent u)
    (sphereRadialForm_contDiff.differentiable (by simp) _)
    (hk.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  change fderiv ℝ B (t,u) (1,0) (0,circleTangent u)-
    fderiv ℝ B (t,u) (0,circleTangent u) (1,0) = _ at hp
  rw [htime,hspace,sphereRadialForm_fderiv,sphereRadialForm_fderiv] at hp
  have hskew : phaseRadialContact (fderiv ℝ k (t,u) (0,circleTangent u))
      (fderiv ℝ k (t,u) (1,0)) =
      -phaseRadialContact (fderiv ℝ k (t,u) (1,0))
        (fderiv ℝ k (t,u) (0,circleTangent u)) := by
    simp [phaseRadialContact,phaseSymplecticForm]
    ring
  rw [hskew] at hp
  linarith

end
end ContactTopology.LegendrianExtension

namespace ContactTopology.LegendrianExtension
open BirkhoffGlobalSection BirkhoffGlobalSection.ContactGenerator Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma circleTangent_contDiff : ContDiff ℝ ∞ circleTangent := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact (contDiff_apply ℝ ℝ 1).neg
  · exact contDiff_apply ℝ ℝ 0

lemma sphere_dot_self {y : Phase} (hy : y ∈ unitThreeSphere) : phaseDot y y = 1 := by
  dsimp [unitThreeSphere, zNormSq, wNormSq] at hy
  dsimp [phaseDot]
  nlinarith

lemma clm_cylinder_decomposition {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D : (ℝ × Plane) →L[ℝ] F) (u : Plane) (a b : ℝ) :
    D (a, b • circleTangent u) = a • D (1,0) + b • D (0,circleTangent u) := by
  have he : (a, b • circleTangent u) = a • ((1 : ℝ),(0 : Plane)) + b • ((0 : ℝ),circleTangent u) := by
    ext i <;> simp
  rw [he, map_add, map_smul, map_smul]


lemma sphere_family_velocity_tangent (k : ℝ × Plane → Phase) (hk : ContDiff ℝ ∞ k)
    (hsphere : ∀ t : ℝ, ∀ u ∈ unitCircle, k (t,u) ∈ unitThreeSphere)
    (t : ℝ) (u : Plane) (hu : u ∈ unitCircle) :
    phaseDot (k (t,u)) (fderiv ℝ k (t,u) (1,0)) = 0 := by
  have hc : HasDerivAt (fun s : ℝ => (s,u)) (1,0) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t u)
  have hd := (hk.differentiable (by simp) (t,u)).hasFDerivAt.comp_hasDerivAt t hc
  have hdot := phaseDot_hasDerivAt hd hd
  have heq : (fun s : ℝ => phaseDot (k (s,u)) (k (s,u))) = fun _ => 1 :=
    funext (fun s => sphere_dot_self (hsphere s u hu))
  change HasDerivAt (fun s : ℝ => phaseDot (k (s,u)) (k (s,u))) _ t at hdot
  rw [heq] at hdot
  have hh := hdot.unique (hasDerivAt_const t (1:ℝ))
  change phaseDot (fderiv ℝ k (t,u) (1,0)) (k (t,u))+
    phaseDot (k (t,u)) (fderiv ℝ k (t,u) (1,0)) = 0 at hh
  have hsym : phaseDot (fderiv ℝ k (t,u) (1,0)) (k (t,u)) =
      phaseDot (k (t,u)) (fderiv ℝ k (t,u) (1,0)) := by simp [phaseDot]; ring
  rw [hsym] at hh
  linarith

lemma legendrian_exists_hamiltonian_prescribed_velocity
    (k : ℝ × Plane → Phase) (hk : ContDiff ℝ ∞ k)
    (hsphere : ∀ t : ℝ, ∀ u ∈ unitCircle, k (t,u) ∈ unitThreeSphere)
    (hinj : InjOn (fun p : ℝ × Plane => (p.1,k p)) (Icc (0:ℝ) 1 ×ˢ unitCircle))
    (hreg : ∀ p ∈ (Icc (0:ℝ) 1 ×ˢ unitCircle), fderiv ℝ k p (0,circleTangent p.2) ≠ 0)
    (hleg : ∀ t : ℝ, ∀ u ∈ unitCircle,
      phaseRadialContact (k (t,u)) (fderiv ℝ k (t,u) (0,circleTangent u)) = 0) :
    ∃ H : ℝ × Phase → ℝ, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧
      ∀ t ∈ Icc (0:ℝ) 1, ∀ u ∈ unitCircle,
        contactField (H (t,k (t,u))) (spatialGradient H (t,k (t,u)))
          (k (t,u)) = fderiv ℝ k (t,u) (1,0) := by
  let V : ℝ × Plane → Phase := fun p => fderiv ℝ k p (1,0)
  let z : ℝ × Plane → Phase := fun p => fderiv ℝ k p (0,circleTangent p.2)
  have hV : ContDiff ℝ ∞ V := (hk.fderiv_right (by simp)).clm_apply contDiff_const
  have hz : ContDiff ℝ ∞ z := (hk.fderiv_right (by simp)).clm_apply
    (contDiff_const.prodMk (circleTangent_contDiff.comp contDiff_snd))
  let h : ℝ × Plane → ℝ := fun p => phaseRadialContact (k p) (V p)
  have hh : ContDiff ℝ ∞ h := contact_contDiff hk hV
  let hs : ℝ × Plane → ℝ := fun p => fderiv ℝ h p (0,circleTangent p.2)
  let ht : ℝ × Plane → ℝ := fun p => fderiv ℝ h p (1,0)
  have hht : ContDiff ℝ ∞ ht := (hh.fderiv_right (by simp)).clm_apply contDiff_const
  let g : ℝ × Plane → Phase := fun p => -J (V p)
  have hg : ContDiff ℝ ∞ g := (J_contDiff hV).neg
  let a : ℝ × Plane → ℝ := fun p => ht p - phaseDot (g p) (V p)
  have ha : ContDiff ℝ ∞ a := hht.sub (phaseDot_contDiff hg hV)
  let L : ℝ × Plane → ((ℝ × Phase) →L[ℝ] ℝ) := fun p =>
    a p • ContinuousLinearMap.fst ℝ ℝ Phase +
      (dotCLM (g p)).comp (ContinuousLinearMap.snd ℝ ℝ Phase)
  have hL : ContDiff ℝ ∞ L :=
    (ha.smul contDiff_const).add ((dotCLM_contDiff hg).clm_comp contDiff_const)
  have hcomp : ∀ p ∈ (Icc (0:ℝ) 1 ×ˢ unitCircle), ∀ b c : ℝ,
      fderiv ℝ h p (b,c • circleTangent p.2) =
        L p (b,fderiv ℝ k p (b,c • circleTangent p.2)) := by
    intro p hp b c
    have hcompat := legendrian_hamiltonian_compatibility k hk hleg p.1 p.2 hp.2
    have hpair : phaseDot (g p) (z p) = hs p := by
      have hh := prescribed_gradient_pairing (k p) (V p) (z p) 0
      simp only [zero_div,zero_smul,add_zero,zero_mul] at hh
      simpa [g,hs,h,V,z] using hh.trans hcompat.symm
    have hpair' : dotCLM (g p) (z p) = hs p := by rw [dotCLM_apply]; exact hpair
    rw [clm_cylinder_decomposition (fderiv ℝ h p),clm_cylinder_decomposition (fderiv ℝ k p)]
    simp only [L,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.coe_fst',ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_snd',Prod.fst,Prod.snd,
      map_add,map_smul,smul_eq_mul]
    change b*ht p+c*hs p = a p*b+(b*dotCLM (g p) (V p)+c*dotCLM (g p) (z p))
    rw [hpair',dotCLM_apply]
    dsimp [a]
    ring
  obtain ⟨H,hH,hHc,hHjet⟩ := SmoothJetExtension.moving_circle_first_jet_extension
    k hk hinj hreg h hh L univ isOpen_univ (subset_univ _) hL.contDiffOn hcomp
  refine ⟨H,hH,hHc,?_⟩
  intro t htI u hu
  have hj := hHjet (t,u) ⟨htI,hu⟩
  have hgrad : spatialGradient H (t,k (t,u)) = g (t,u) := by
    ext i
    change fderiv ℝ H (t,k (t,u)) (0,Pi.single i 1) = g (t,u) i
    rw [hj.2]
    dsimp [L]
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.coe_fst',ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_snd',Prod.fst,Prod.snd,
      smul_eq_mul,mul_zero,zero_add,dotCLM_apply]
    fin_cases i <;> simp [phaseDot]
  have hv := contactField_prescribed (k (t,u)) (V (t,u)) 0
    (sphere_dot_self (hsphere t u hu)) (sphere_family_velocity_tangent k hk hsphere t u hu)
  simp only [zero_div,zero_smul,add_zero] at hv
  change contactField (h (t,u)) (g (t,u)) (k (t,u)) = V (t,u) at hv
  rw [← hj.1,← hgrad] at hv
  exact hv

end
end ContactTopology.LegendrianExtension


open BirkhoffGlobalSection GrayStability
open scoped ContDiff Topology

namespace BirkhoffGlobalSection.IsotopyExtension

/-- The round sphere as the zero level of `|y|² - 1`. -/
noncomputable def sphereEq : E 4 → (Fin 1 → ℝ) := fun y _ => zNormSq y + wNormSq y - 1

lemma mem_levelSet_sphereEq {y : Phase} : y ∈ levelSet sphereEq ↔ y ∈ unitThreeSphere := by
  change sphereEq y = 0 ↔ zNormSq y + wNormSq y = 1
  constructor
  · intro h
    have := congrFun h 0
    simp only [sphereEq, Pi.zero_apply] at this
    linarith
  · intro h
    funext i
    simp only [sphereEq, Pi.zero_apply, h, sub_self]

/-- The derivative of the squared norm. -/
noncomputable def normSqDeriv (y : Phase) : Phase →L[ℝ] ℝ :=
  (2 * y 0) • ContinuousLinearMap.proj 0 + (2 * y 1) • ContinuousLinearMap.proj 1 +
    (2 * y 2) • ContinuousLinearMap.proj 2 + (2 * y 3) • ContinuousLinearMap.proj 3

lemma normSqDeriv_apply (y v : Phase) : normSqDeriv y v = 2 * phaseDot y v := by
  simp [normSqDeriv, phaseDot]
  ring

lemma hasFDerivAt_normSq (y : Phase) :
    HasFDerivAt (fun x : Phase => zNormSq x + wNormSq x) (normSqDeriv y) y := by
  have hp := fun i : Fin 4 =>
    (hasFDerivAt_apply (𝕜 := ℝ) i y).mul (hasFDerivAt_apply (𝕜 := ℝ) i y)
  have hN := ((hp 0).add (hp 1)).add ((hp 2).add (hp 3))
  refine (hN.congr_fderiv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
  · refine ContinuousLinearMap.ext fun v => ?_
    simp [normSqDeriv]
    ring
  · simp [zNormSq, wNormSq]
    ring

lemma hasFDerivAt_sphereEq (y : Phase) :
    HasFDerivAt sphereEq (ContinuousLinearMap.pi fun _ : Fin 1 => normSqDeriv y) y :=
  hasFDerivAt_pi.2 fun _ => (hasFDerivAt_normSq y).sub_const 1

lemma mem_tangentSpace_sphereEq {y v : Phase} :
    v ∈ tangentSpace sphereEq y ↔ phaseDot y v = 0 := by
  change fderiv ℝ sphereEq y v = 0 ↔ phaseDot y v = 0
  rw [(hasFDerivAt_sphereEq y).fderiv]
  constructor
  · intro h
    have := congrFun h 0
    simp only [ContinuousLinearMap.pi_apply, normSqDeriv_apply, Pi.zero_apply] at this
    linarith
  · intro h
    funext i
    simp only [ContinuousLinearMap.pi_apply, normSqDeriv_apply, Pi.zero_apply, h, mul_zero]

lemma sphereEq_regular : IsCompactRegularLevel sphereEq := by
  refine ⟨?_, ?_, ?_⟩
  · refine contDiff_pi.2 fun _ => ?_
    show ContDiff ℝ ∞ (fun y : Phase => zNormSq y + wNormSq y - 1)
    unfold zNormSq wNormSq
    fun_prop
  · have hset : levelSet sphereEq = unitThreeSphere := Set.ext fun y => mem_levelSet_sphereEq
    rw [hset]
    apply Metric.isCompact_of_isClosed_isBounded
    · exact isClosed_eq (by unfold zNormSq wNormSq; fun_prop) continuous_const
    · refine (Metric.isBounded_closedBall (x := (0 : Phase)) (r := 1)).subset fun y hy => ?_
      have h : zNormSq y + wNormSq y = 1 := hy
      simp only [zNormSq, wNormSq] at h
      have h0 : y 0 ^ 2 ≤ 1 := by nlinarith [sq_nonneg (y 1), sq_nonneg (y 2), sq_nonneg (y 3)]
      have h1 : y 1 ^ 2 ≤ 1 := by nlinarith [sq_nonneg (y 0), sq_nonneg (y 2), sq_nonneg (y 3)]
      have h2 : y 2 ^ 2 ≤ 1 := by nlinarith [sq_nonneg (y 0), sq_nonneg (y 1), sq_nonneg (y 3)]
      have h3 : y 3 ^ 2 ≤ 1 := by nlinarith [sq_nonneg (y 0), sq_nonneg (y 1), sq_nonneg (y 2)]
      rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      rw [Real.norm_eq_abs]
      refine (sq_le_one_iff_abs_le_one _).1 ?_
      fin_cases i
      exacts [h0, h1, h2, h3]
  · intro y hy w
    have hy' : zNormSq y + wNormSq y = 1 := mem_levelSet_sphereEq.1 hy
    have hyy : phaseDot y y = 1 := by
      simp only [zNormSq, wNormSq] at hy'
      simp only [phaseDot]
      linarith [hy']
    refine ⟨(w 0 / 2) • y, ?_⟩
    rw [(hasFDerivAt_sphereEq y).fderiv]
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    simp only [ContinuousLinearMap.pi_apply, map_smul, normSqDeriv_apply, smul_eq_mul, hyy]
    ring

/-- The radial contact form `λ_y(v) = -ω(y,v)/2` as a linear family of covectors. -/
noncomputable def radialForm : Phase →L[ℝ] (Phase →L[ℝ] ℝ) :=
  (-(1 / 2 : ℝ)) •
    ((ContinuousLinearMap.proj 0 : Phase →L[ℝ] ℝ).smulRight
        (ContinuousLinearMap.proj 2 : Phase →L[ℝ] ℝ) -
      (ContinuousLinearMap.proj 2 : Phase →L[ℝ] ℝ).smulRight
        (ContinuousLinearMap.proj 0 : Phase →L[ℝ] ℝ) +
      (ContinuousLinearMap.proj 1 : Phase →L[ℝ] ℝ).smulRight
        (ContinuousLinearMap.proj 3 : Phase →L[ℝ] ℝ) -
      (ContinuousLinearMap.proj 3 : Phase →L[ℝ] ℝ).smulRight
        (ContinuousLinearMap.proj 1 : Phase →L[ℝ] ℝ))

lemma radialForm_apply (y v : Phase) : radialForm y v = phaseRadialContact y v := by
  simp [radialForm, phaseRadialContact, phaseSymplecticForm]
  ring


end BirkhoffGlobalSection.IsotopyExtension


open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

namespace BirkhoffGlobalSection.HopfTransport
noncomputable section

lemma smooth_inverse_of_bijective_derivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E → E) (hf : ContDiff ℝ ∞ f) (hb : Function.Bijective f)
    (hi : ∀ x, Function.Injective (fderiv ℝ f x)) :
    ∃ g : E → E, ContDiff ℝ ∞ g ∧ (∀ x, g (f x) = x) ∧ (∀ x, f (g x) = x) := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  let L : E → E ≃L[ℝ] E := fun x => (LinearEquiv.ofBijective (fderiv ℝ f x).toLinearMap
    ⟨hi x,LinearMap.injective_iff_surjective.mp (hi x)⟩).toContinuousLinearEquiv
  have hd : ∀ x, HasFDerivAt f (L x : E →L[ℝ] E) x := by
    intro x
    exact (hf.differentiable (by simp) x).hasFDerivAt
  have ho : IsOpenMap f := isOpenMap_of_hasStrictFDerivAt_equiv
    (fun x => hf.contDiffAt.hasStrictFDerivAt' (hd x) (by simp))
  let H : E ≃ₜ E := (Equiv.ofBijective f hb).toHomeomorphOfContinuousOpen hf.continuous ho
  have hH : ContDiff ℝ ∞ (H : E → E) := hf
  have hHd : ∀ x, HasFDerivAt (H : E → E) (L x : E →L[ℝ] E) x := hd
  exact ⟨H.symm,H.contDiff_symm hHd hH,H.symm_apply_apply,H.apply_symm_apply⟩

lemma smooth_joint_flow_inverse {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (X ψ : ℝ → V → V)
    (hX : ContDiff ℝ ∞ (fun p : ℝ × V => X p.1 p.2))
    (hψ : ContDiff ℝ ∞ (fun p : ℝ × V => ψ p.1 p.2))
    (h0 : ∀ y, ψ 0 y = y) (hb : ∀ t, Function.Bijective (ψ t))
    (hd : ∀ t y, HasDerivAt (fun s => ψ s y) (X t (ψ t y)) t) :
    ∃ ρ : ℝ → V → V, ContDiff ℝ ∞ (fun p : ℝ × V => ρ p.1 p.2) ∧
      (∀ t y, ρ t (ψ t y) = y) ∧ (∀ t y, ψ t (ρ t y) = y) := by
  letI : CompleteSpace V := FiniteDimensional.complete ℝ V
  let F : ℝ × V → ℝ × V := fun p => (p.1,ψ p.1 p.2)
  have hF : ContDiff ℝ ∞ F := contDiff_fst.prodMk hψ
  have hFb : Function.Bijective F := by
    constructor
    · intro p q he
      change (p.1,ψ p.1 p.2) = (q.1,ψ q.1 q.2) at he
      have ht := congrArg (fun z : ℝ × V => z.1) he
      have hy := congrArg (fun z : ℝ × V => z.2) he
      refine Prod.ext ht ?_
      apply (hb p.1).1
      change ψ p.1 p.2 = ψ q.1 q.2 at hy
      rw [← ht] at hy
      exact hy
    · rintro ⟨t,y⟩
      obtain ⟨x,hx⟩ := (hb t).2 y
      exact ⟨(t,x),Prod.ext rfl hx⟩
  have hFi : ∀ p, Function.Injective (fderiv ℝ F p) := by
    intro p
    have hfd := (hasFDerivAt_fst (𝕜 := ℝ) (p := p)).prodMk ((hψ.differentiable (by simp) p).hasFDerivAt)
    change HasFDerivAt F _ p at hfd
    have hslice := ((hψ.differentiable (by simp) p).hasFDerivAt).comp p.2
      ((hasFDerivAt_const (𝕜 := ℝ) p.1 p.2).prodMk (hasFDerivAt_id (𝕜 := ℝ) p.2))
    change HasFDerivAt (ψ p.1) _ p.2 at hslice
    have hsi := FlowCalculus.smooth_flow_spatial_derivative_injective X ψ hX hψ h0 hd p.1 p.2
    intro v w he
    rw [hfd.fderiv] at he
    change (v.1,(fderiv ℝ (fun q : ℝ × V => ψ q.1 q.2) p) v) =
      (w.1,(fderiv ℝ (fun q : ℝ × V => ψ q.1 q.2) p) w) at he
    have ht := congrArg (fun z : ℝ × V => z.1) he
    have hy := congrArg (fun z : ℝ × V => z.2) he
    have hz : (fderiv ℝ (fun q : ℝ × V => ψ q.1 q.2) p) (0,v.2-w.2) = 0 := by
      change (fderiv ℝ (fun q : ℝ × V => ψ q.1 q.2) p) v =
        (fderiv ℝ (fun q : ℝ × V => ψ q.1 q.2) p) w at hy
      have hsub := sub_eq_zero.mpr hy
      rw [← map_sub] at hsub
      have hvw : v-w = (0,v.2-w.2) := by
        apply Prod.ext
        · exact sub_eq_zero.mpr ht
        · rfl
      rw [hvw] at hsub
      exact hsub
    refine Prod.ext ht ?_
    have hsz : fderiv ℝ (ψ p.1) p.2 (v.2-w.2) = 0 := by
      change fderiv ℝ (ψ p.1) p.2 (v.2-w.2) = 0
      rw [hslice.fderiv]
      exact hz
    have hzv : v.2-w.2 = 0 := hsi (by simpa only [map_zero] using hsz)
    exact sub_eq_zero.mp hzv
  obtain ⟨G,hG,hGF,hFG⟩ := smooth_inverse_of_bijective_derivative F hF hFb hFi
  have hGt : ∀ t y, (G (t,y)).1 = t := by
    intro t y
    exact congrArg Prod.fst (hFG (t,y))
  refine ⟨fun t y => (G (t,y)).2,contDiff_snd.comp hG,?_,?_⟩
  · intro t y
    exact congrArg Prod.snd (hGF (t,y))
  · intro t y
    have he := congrArg Prod.snd (hFG (t,y))
    simpa only [F,hGt] using he

end
end BirkhoffGlobalSection.HopfTransport

namespace ContactTopology
open BirkhoffGlobalSection BirkhoffGlobalSection.HopfTransport BirkhoffGlobalSection.IsotopyExtension GrayStability Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Integrate a compact odd contact generator to a jointly smooth flow and
inverse, with positive contact pullback throughout the unit interval. -/
lemma integrate_equivariant_contact_generator (X : ℝ → Phase → Phase) (mu : ℝ → Phase → ℝ)
    (hX : ContDiff ℝ ∞ (fun p : ℝ × Phase => X p.1 p.2))
    (hmu : ContDiff ℝ ∞ (fun p : ℝ × Phase => mu p.1 p.2))
    (hsupp : ∃ C : Set Phase, IsCompact C ∧ ∀ t y, y ∉ C → X t y = 0)
    (hodd : ∀ t y, X t (-y) = -X t y)
    (htan : ∀ t ∈ Icc (0:ℝ) 1, ∀ y ∈ unitThreeSphere, phaseDot y (X t y) = 0)
    (hlie : ∀ t ∈ Icc (0:ℝ) 1, ∀ y ∈ unitThreeSphere, ∀ v : Phase, phaseDot y v = 0 →
      phaseRadialContact (X t y) v+phaseRadialContact y (fderiv ℝ (X t) y v) = mu t y*phaseRadialContact y v) :
    ∃ psi rho : ℝ → Phase → Phase, ∃ lam : ℝ → Phase → ℝ,
      ContDiff ℝ ∞ (fun p : ℝ × Phase => psi p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × Phase => rho p.1 p.2) ∧
      (∀ y, psi 0 y = y) ∧
      (∀ t y, rho t (psi t y) = y) ∧ (∀ t y, psi t (rho t y) = y) ∧
      (∀ t y, psi t (-y) = -psi t y) ∧
      (∀ t y, HasDerivAt (fun s => psi s y) (X t (psi t y)) t) ∧
      (∀ t ∈ Icc (0:ℝ) 1, MapsTo (psi t) unitThreeSphere unitThreeSphere) ∧
      (∀ t ∈ Icc (0:ℝ) 1, MapsTo (rho t) unitThreeSphere unitThreeSphere) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ y ∈ unitThreeSphere, 0 < lam t y) ∧
      ∀ t ∈ Icc (0:ℝ) 1, ∀ y ∈ unitThreeSphere, ∀ v : Phase, phaseDot y v = 0 →
        phaseRadialContact (psi t y) (fderiv ℝ (psi t) y v) = lam t y*phaseRadialContact y v := by
  obtain ⟨psi,hpsi,h0,hbij,hflow,hiso,hDpsi⟩ := FlowCalculus.compact_supported_flow_preserves_regular_level
    sphereEq sphereEq_regular X hX hsupp (by
      intro t ht y hy
      exact mem_tangentSpace_sphereEq.mpr (htan t ht y (mem_levelSet_sphereEq.mp hy)))
  obtain ⟨rho,hrho,hrp,hpr⟩ := smooth_joint_flow_inverse X psi hX hpsi h0 hbij hflow
  have hpsiodd : ∀ t y, psi t (-y) = -psi t y := by
    intro t y
    have hp : (fun s => psi s (-y)) 0 = -y ∧
        ∀ s, HasDerivAt (fun r => psi r (-y)) (X s (psi s (-y))) s := ⟨h0 (-y),fun s => hflow s (-y)⟩
    have hn : (fun s => -psi s y) 0 = -y ∧
        ∀ s, HasDerivAt (fun r => -psi r y) (X s (-psi s y)) s := by
      constructor
      · change -psi 0 y = -y
        rw [h0]
      · intro s
        rw [hodd]
        convert! (hflow s y).neg using 1
    have hh : (fun s => psi s (-y)) = fun s => -psi s y := by
      apply (FlowCalculus.exists_unique_global_trajectory_of_compact_support X hX hsupp 0 (-y)).unique
      · convert! hp using 1
      · convert! hn using 1
    exact congrFun hh t
  have hmaps : ∀ t ∈ Icc (0:ℝ) 1, MapsTo (psi t) unitThreeSphere unitThreeSphere := by
    intro t ht y hy
    exact mem_levelSet_sphereEq.mp ((hiso.2.2 t ht).1.mapsTo (mem_levelSet_sphereEq.mpr hy))
  have hrhomaps : ∀ t ∈ Icc (0:ℝ) 1, MapsTo (rho t) unitThreeSphere unitThreeSphere := by
    intro t ht y hy
    obtain ⟨z,hz,hzmap⟩ := (hiso.2.2 t ht).1.surjOn (mem_levelSet_sphereEq.mpr hy)
    rw [← hzmap,hrp]
    exact mem_levelSet_sphereEq.mp hz
  let rate : ℝ → Phase → ℝ := fun t y => mu t (psi t y)
  have hrate : ContDiff ℝ ∞ (fun p : ℝ × Phase => rate p.1 p.2) := hmu.comp (contDiff_fst.prodMk hpsi)
  obtain ⟨lam,hlam,hlam0,hpos,htransport⟩ := ParameterizedCalculus.smooth_scalar_linear_transport rate hrate
  refine ⟨psi,rho,lam,hpsi,hrho,h0,hrp,hpr,hpsiodd,hflow,hmaps,hrhomaps,fun t ht y hy => hpos t y,?_⟩
  intro t ht y hy v hv
  have hsmooth : IsSmoothFamily (fun _ : ℝ => (radialForm : OneForm 4)) :=
    radialForm.contDiff.comp contDiff_snd
  have hf : ∀ s ∈ Icc (0:ℝ) 1,
      HasDerivAt (fun r => phaseRadialContact (psi r y) (fderiv ℝ (psi r) y v))
        (rate s y*phaseRadialContact (psi s y) (fderiv ℝ (psi s) y v)) s := by
    intro s hs
    have hz := hmaps s hs hy
    have hw := mem_tangentSpace_sphereEq.mp
      (hDpsi s hs y (mem_levelSet_sphereEq.mpr hy) v (mem_tangentSpace_sphereEq.mpr hv))
    have hd := GrayStability.pullback_family_hasDerivAt (fun _ => (radialForm : OneForm 4)) hsmooth
      X hX psi hpsi h0 hbij hflow s y v
    have hval : formTimeDeriv (fun _ : ℝ => (radialForm : OneForm 4)) s (psi s y) (fderiv ℝ (psi s) y v)+
        lieDerivOneForm (X s) radialForm (psi s y) (fderiv ℝ (psi s) y v) =
        rate s y*phaseRadialContact (psi s y) (fderiv ℝ (psi s) y v) := by
      simp only [formTimeDeriv,lieDerivOneForm,deriv_const,ContinuousLinearMap.fderiv,
        radialForm_apply,zero_add,rate]
      exact hlie s hs _ hz _ hw
    rw [hval] at hd
    convert! hd using 1 <;> simp [pullback,radialForm_apply]
  have hinit : phaseRadialContact (psi 0 y) (fderiv ℝ (psi 0) y v) = phaseRadialContact y v := by
    have hid : psi 0 = id := funext h0
    simp [hid]
  simpa only [hinit] using htransport y
    (fun s => phaseRadialContact (psi s y) (fderiv ℝ (psi s) y v)) hf t ht

lemma contact_generator_flow_isotopy (X : ℝ → Phase → Phase) (mu : ℝ → Phase → ℝ)
    (hX : ContDiff ℝ ∞ (fun p : ℝ × Phase => X p.1 p.2))
    (hmu : ContDiff ℝ ∞ (fun p : ℝ × Phase => mu p.1 p.2))
    (hsupp : ∃ C : Set Phase, IsCompact C ∧ ∀ t y, y ∉ C → X t y = 0)
    (hodd : ∀ t y, X t (-y) = -X t y)
    (htan : ∀ t ∈ Icc (0:ℝ) 1, ∀ y ∈ unitThreeSphere, phaseDot y (X t y) = 0)
    (hlie : ∀ t ∈ Icc (0:ℝ) 1, ∀ y ∈ unitThreeSphere, ∀ v : Phase, phaseDot y v = 0 →
      phaseRadialContact (X t y) v+phaseRadialContact y (fderiv ℝ (X t) y v) = mu t y*phaseRadialContact y v) :
    ∃ F : EquivariantSphereContactomorphism, Nonempty (EquivariantSphereContactIsotopy F) ∧
      ∃ psi : ℝ → Phase → Phase, F.toFun = psi 1 ∧ (∀ y, psi 0 y = y) ∧
        ∀ t y, HasDerivAt (fun s => psi s y) (X t (psi t y)) t := by
  obtain ⟨psi,rho,lam,hpsi,hrho,h0,hrp,hpr,hoddpsi,hflow,hmaps,hrhomaps,hpos,hcontact⟩ :=
    integrate_equivariant_contact_generator X mu hX hmu hsupp hodd htan hlie
  let sig : ℝ → ℝ := fun t => Real.smoothTransition t
  have hsig : ContDiff ℝ ∞ sig := Real.smoothTransition.contDiff (n := (⊤:ℕ∞))
  have hsigmem : ∀ t, sig t ∈ Icc (0:ℝ) 1 := fun t => ⟨Real.smoothTransition.nonneg t,Real.smoothTransition.le_one t⟩
  let C : ℝ → EquivariantSphereContactomorphism := fun t =>
    { toFun := psi (sig t)
      invFun := rho (sig t)
      smooth := fun y hy => (hpsi.comp (contDiff_const.prodMk contDiff_id)).contDiffAt
      inv_smooth := fun y hy => (hrho.comp (contDiff_const.prodMk contDiff_id)).contDiffAt
      maps_sphere := hmaps _ (hsigmem t)
      inv_maps_sphere := hrhomaps _ (hsigmem t)
      left_inv := fun y hy => hrp _ y
      right_inv := fun y hy => hpr _ y
      antipodal := fun y hy => hoddpsi _ y
      contact := fun y hy => ⟨lam (sig t) y,hpos _ (hsigmem t) y hy,hcontact _ (hsigmem t) y hy⟩ }
  have hs0 : sig 0 = 0 := Real.smoothTransition.zero_of_nonpos (by norm_num)
  have hs1 : sig 1 = 1 := Real.smoothTransition.one_of_one_le (by norm_num)
  refine ⟨C 1,⟨{slice := C,smooth := ?_,start := ?_,finish := ?_}⟩,psi,?_,h0,hflow⟩
  · intro t ht y hy
    exact (hpsi.comp ((hsig.comp contDiff_fst).prodMk contDiff_snd)).contDiffAt
  · intro y hy
    change psi (sig 0) y = y
    rw [hs0,h0]
  · intro y hy
    rfl
  · change psi (sig 1) = psi 1
    rw [hs1]

end
end ContactTopology

-- Reused from accepted proof 9a237cfc-145c-40c8-9d8c-9d9c0ca99ce5.
namespace BirkhoffGlobalSection.ContactGenerator
open BirkhoffGlobalSection Set
open scoped ContDiff
noncomputable section

def oddAverage (X : ℝ → Phase → Phase) (t : ℝ) (y : Phase) : Phase :=
  (1 / 2 : ℝ) • (X t y - X t (-y))

lemma oddAverage_odd (X : ℝ → Phase → Phase) (t : ℝ) (y : Phase) :
    oddAverage X t (-y) = -oddAverage X t y := by
  ext i
  simp [oddAverage]
  ring

lemma oddAverage_contDiff {X : ℝ → Phase → Phase}
    (hX : ContDiff ℝ ∞ (fun p : ℝ × Phase => X p.1 p.2)) :
    ContDiff ℝ ∞ (fun p : ℝ × Phase => oddAverage X p.1 p.2) := by
  exact (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ × Phase => (1/2 : ℝ))).smul (hX.sub (hX.comp (contDiff_fst.prodMk contDiff_snd.neg)))

lemma oddAverage_fderiv_apply {X : ℝ → Phase → Phase}
    (hX : ContDiff ℝ ∞ (fun p : ℝ × Phase => X p.1 p.2)) (t : ℝ) (y v : Phase) :
    fderiv ℝ (oddAverage X t) y v =
      (1 / 2 : ℝ) • (fderiv ℝ (X t) y v + fderiv ℝ (X t) (-y) v) := by
  have hd : Differentiable ℝ (X t) :=
    (hX.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
  have hn : HasFDerivAt (fun z : Phase => -z) (-ContinuousLinearMap.id ℝ Phase) y :=
    (hasFDerivAt_id y).neg
  have hf := (((hd y).hasFDerivAt).sub (((hd (-y)).hasFDerivAt).comp y hn)).const_smul (1/2 : ℝ)
  change fderiv ℝ ((1/2 : ℝ) • (X t - X t ∘ Neg.neg)) y v = _
  rw [hf.fderiv]
  simp [ContinuousLinearMap.comp_apply]

lemma oddAverage_compact_support {X : ℝ → Phase → Phase}
    (hX : ∃ C : Set Phase, IsCompact C ∧ ∀ t y, y ∉ C → X t y = 0) :
    ∃ C : Set Phase, IsCompact C ∧ ∀ t y, y ∉ C → oddAverage X t y = 0 := by
  obtain ⟨C,hC,hs⟩ := hX
  refine ⟨C ∪ Neg.neg '' C, hC.union (hC.image continuous_neg), ?_⟩
  intro t y hy
  have hyC : y ∉ C := fun h => hy (Or.inl h)
  have hnyC : -y ∉ C := fun h => hy (Or.inr ⟨-y,h,neg_neg y⟩)
  simp [oddAverage, hs t y hyC, hs t (-y) hnyC]

lemma sphere_neg {y : Phase} (hy : y ∈ unitThreeSphere) : -y ∈ unitThreeSphere := by
  simpa [unitThreeSphere,zNormSq,wNormSq] using hy

lemma oddAverage_tangent {X : ℝ → Phase → Phase}
    (hX : ∀ t ∈ Icc (0 : ℝ) 1, ∀ y ∈ unitThreeSphere, phaseDot y (X t y) = 0) :
    ∀ t ∈ Icc (0 : ℝ) 1, ∀ y ∈ unitThreeSphere, phaseDot y (oddAverage X t y) = 0 := by
  intro t ht y hy
  have h1 := hX t ht y hy
  have h2 := hX t ht (-y) (sphere_neg hy)
  simp [phaseDot] at h1 h2
  simp [oddAverage, phaseDot]
  linear_combination (1/2 : ℝ) * h1 + (1/2 : ℝ) * h2

lemma oddAverage_lie {X : ℝ → Phase → Phase} {μ : ℝ → Phase → ℝ}
    (hX : ContDiff ℝ ∞ (fun p : ℝ × Phase => X p.1 p.2))
    (hc : ∀ t ∈ Icc (0 : ℝ) 1, ∀ y ∈ unitThreeSphere, ∀ v : Phase, phaseDot y v = 0 →
      phaseRadialContact (X t y) v + phaseRadialContact y (fderiv ℝ (X t) y v) = μ t y * phaseRadialContact y v) :
    ∀ t ∈ Icc (0 : ℝ) 1, ∀ y ∈ unitThreeSphere, ∀ v : Phase, phaseDot y v = 0 →
      phaseRadialContact (oddAverage X t y) v + phaseRadialContact y (fderiv ℝ (oddAverage X t) y v) =
        ((μ t y + μ t (-y))/2) * phaseRadialContact y v := by
  intro t ht y hy v hv
  have hnv : phaseDot (-y) v = 0 := by simp [phaseDot] at hv ⊢; linarith
  have h1 := hc t ht y hy v hv
  have h2 := hc t ht (-y) (sphere_neg hy) v hnv
  rw [oddAverage_fderiv_apply hX]
  simp [contact_eq_dot, phaseDot, J] at h1 h2
  simp [oddAverage, contact_eq_dot, phaseDot, J, Matrix.vecHead, Matrix.vecTail]
  linear_combination (1/2 : ℝ) * h1 - (1/2 : ℝ) * h2

end
end BirkhoffGlobalSection.ContactGenerator

namespace ContactTopology.LegendrianExtension
open BirkhoffGlobalSection BirkhoffGlobalSection.ContactGenerator Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma circle_neg {u : Plane} (hu : u ∈ unitCircle) : -u ∈ unitCircle := by
  simpa [unitCircle,planeNormSq] using hu

lemma family_velocity_odd (k : ℝ × Plane → Phase) (hk : ContDiff ℝ ∞ k)
    (hodd : ∀ t : ℝ, ∀ u ∈ unitCircle, k (t,-u) = -k (t,u))
    (t : ℝ) (u : Plane) (hu : u ∈ unitCircle) :
    fderiv ℝ k (t,-u) (1,0) = -fderiv ℝ k (t,u) (1,0) := by
  have hn := (hk.differentiable (by simp) (t,-u)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t (-u)))
  have hp := ((hk.differentiable (by simp) (t,u)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t u))).neg
  have heq : (fun s : ℝ => k (s,-u)) = fun s => -k (s,u) := funext (fun s => hodd s u hu)
  change HasDerivAt (fun s : ℝ => k (s,-u)) _ t at hn
  rw [heq] at hn
  exact hn.unique hp

lemma legendrian_contact_generator
    (k : ℝ × Plane → Phase) (hk : ContDiff ℝ ∞ k)
    (hsphere : ∀ t : ℝ, ∀ u ∈ unitCircle, k (t,u) ∈ unitThreeSphere)
    (hinj : InjOn (fun p : ℝ × Plane => (p.1,k p)) (Icc (0:ℝ) 1 ×ˢ unitCircle))
    (hreg : ∀ p ∈ (Icc (0:ℝ) 1 ×ˢ unitCircle), fderiv ℝ k p (0,circleTangent p.2) ≠ 0)
    (hleg : ∀ t : ℝ, ∀ u ∈ unitCircle,
      phaseRadialContact (k (t,u)) (fderiv ℝ k (t,u) (0,circleTangent u)) = 0)
    (hodd : ∀ t : ℝ, ∀ u ∈ unitCircle, k (t,-u) = -k (t,u)) :
    ∃ X : ℝ → Phase → Phase, ∃ mu : ℝ → Phase → ℝ,
      ContDiff ℝ ∞ (fun p : ℝ × Phase => X p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × Phase => mu p.1 p.2) ∧
      (∃ C : Set Phase, IsCompact C ∧ ∀ t y, y ∉ C → X t y = 0) ∧
      (∀ t y, X t (-y) = -X t y) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ y ∈ unitThreeSphere, phaseDot y (X t y) = 0) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ y ∈ unitThreeSphere, ∀ v : Phase, phaseDot y v = 0 →
        phaseRadialContact (X t y) v+phaseRadialContact y (fderiv ℝ (X t) y v) =
          mu t y*phaseRadialContact y v) ∧
      ∀ t ∈ Icc (0:ℝ) 1, ∀ u ∈ unitCircle, X t (k (t,u)) = fderiv ℝ k (t,u) (1,0) := by
  obtain ⟨H,hH,hHc,hv⟩ := legendrian_exists_hamiltonian_prescribed_velocity
    k hk hsphere hinj hreg hleg
  let X : ℝ → Phase → Phase := fun t y => contactField (H (t,y)) (spatialGradient H (t,y)) y
  let mu : ℝ → Phase → ℝ := fun t y => 2*phaseDot (J y) (spatialGradient H (t,y))
  have hX : ContDiff ℝ ∞ (fun p : ℝ × Phase => X p.1 p.2) := hamiltonian_field_contDiff hH
  have hmu : ContDiff ℝ ∞ (fun p : ℝ × Phase => mu p.1 p.2) := hamiltonian_factor_contDiff hH
  have htan : ∀ t ∈ Icc (0:ℝ) 1, ∀ y ∈ unitThreeSphere, phaseDot y (X t y) = 0 := by
    intro t ht y hy
    exact contactField_tangent _ _ _ (sphere_dot_self hy)
  have hlie : ∀ t ∈ Icc (0:ℝ) 1, ∀ y ∈ unitThreeSphere, ∀ v : Phase, phaseDot y v = 0 →
      phaseRadialContact (X t y) v+phaseRadialContact y (fderiv ℝ (X t) y v) =
        mu t y*phaseRadialContact y v := by
    intro t ht y hy v hvt
    exact hamiltonian_field_lie hH t y v (sphere_dot_self hy) hvt
  refine ⟨oddAverage X,(fun t y => (mu t y+mu t (-y))/2),oddAverage_contDiff hX,?_,
    oddAverage_compact_support (hamiltonian_field_compact_support hHc),oddAverage_odd X,
    oddAverage_tangent htan,oddAverage_lie hX hlie,?_⟩
  · exact (hmu.add (hmu.comp (contDiff_fst.prodMk contDiff_snd.neg))).div_const 2
  · intro t ht u hu
    have hn := hv t ht (-u) (circle_neg hu)
    rw [hodd t u hu,family_velocity_odd k hk hodd t u hu] at hn
    change (1/2:ℝ) • (X t (k (t,u))-X t (-k (t,u))) = _
    rw [show X t (k (t,u)) = fderiv ℝ k (t,u) (1,0) from hv t ht u hu,
      show X t (-k (t,u)) = -fderiv ℝ k (t,u) (1,0) from hn]
    ext i
    simp
    ring

/-- The endpoint form of equivariant Legendrian isotopy extension, retaining
pointwise parametrizations. -/
theorem equivariant_legendrian_isotopy_extension
    (k : ℝ × Plane → Phase) (hk : ContDiff ℝ ∞ k)
    (hsphere : ∀ t : ℝ, ∀ u ∈ unitCircle, k (t,u) ∈ unitThreeSphere)
    (hinj : InjOn (fun p : ℝ × Plane => (p.1,k p)) (Icc (0:ℝ) 1 ×ˢ unitCircle))
    (hreg : ∀ p ∈ (Icc (0:ℝ) 1 ×ˢ unitCircle), fderiv ℝ k p (0,circleTangent p.2) ≠ 0)
    (hleg : ∀ t : ℝ, ∀ u ∈ unitCircle,
      phaseRadialContact (k (t,u)) (fderiv ℝ k (t,u) (0,circleTangent u)) = 0)
    (hodd : ∀ t : ℝ, ∀ u ∈ unitCircle, k (t,-u) = -k (t,u)) :
    ∃ F : EquivariantSphereContactomorphism, Nonempty (EquivariantSphereContactIsotopy F) ∧
      ∀ u ∈ unitCircle, F.toFun (k (0,u)) = k (1,u) := by
  obtain ⟨X,mu,hX,hmu,hsupp,hXodd,htan,hlie,hvel⟩ :=
    legendrian_contact_generator k hk hsphere hinj hreg hleg hodd
  obtain ⟨F,hFiso,psi,hF,h0,hflow⟩ :=
    ContactTopology.contact_generator_flow_isotopy X mu hX hmu hsupp hXodd htan hlie
  obtain ⟨L,hL⟩ := FlowCalculus.uniform_spatial_lipschitz_of_compact_support X hX hsupp (0:ℝ) 1
  refine ⟨F,hFiso,?_⟩
  intro u hu
  have hb : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt (fun s => k (s,u)) (X t (k (t,u))) t := by
    intro t ht
    rw [hvel t ht u hu]
    exact (hk.differentiable (by simp) (t,u)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t u))
  have heq := ODE_solution_unique_of_mem_Icc_right (v := X) (s := fun _ => univ) (K := L)
    (f := fun t => psi t (k (0,u))) (g := fun t => k (t,u))
    (fun t ht => (hL t (Ico_subset_Icc_self ht)).lipschitzOnWith)
    (HasDerivAt.continuousOn fun t ht => hflow t _)
    (fun t ht => (hflow t _).hasDerivWithinAt) (fun t ht => trivial)
    (HasDerivAt.continuousOn fun t ht => hb t ht)
    (fun t ht => (hb t (Ico_subset_Icc_self ht)).hasDerivWithinAt) (fun t ht => trivial)
    (by simp [h0])
  rw [hF]
  exact heq ⟨zero_le_one,le_rfl⟩

end
end ContactTopology.LegendrianExtension
open BirkhoffGlobalSection Set Function
open scoped ContDiff
theorem solution
    (k : ℝ × Plane → Phase) (hk : ContDiff ℝ ∞ k)
    (hsphere : ∀ t : ℝ, ∀ u ∈ unitCircle, k (t,u) ∈ unitThreeSphere)
    (hinj : InjOn (fun p : ℝ × Plane => (p.1,k p)) (Icc (0:ℝ) 1 ×ˢ unitCircle))
    (hreg : ∀ p ∈ (Icc (0:ℝ) 1 ×ˢ unitCircle), fderiv ℝ k p (0,circleTangent p.2) ≠ 0)
    (hleg : ∀ t : ℝ, ∀ u ∈ unitCircle,
      phaseRadialContact (k (t,u)) (fderiv ℝ k (t,u) (0,circleTangent u)) = 0)
    (hodd : ∀ t : ℝ, ∀ u ∈ unitCircle, k (t,-u) = -k (t,u)) :
    ∃ F : EquivariantSphereContactomorphism, Nonempty (EquivariantSphereContactIsotopy F) ∧
      ∀ u ∈ unitCircle, F.toFun (k (0,u)) = k (1,u) := by
  exact ContactTopology.LegendrianExtension.equivariant_legendrian_isotopy_extension
    k hk hsphere hinj hreg hleg hodd
