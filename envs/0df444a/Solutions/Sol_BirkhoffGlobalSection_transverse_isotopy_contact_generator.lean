-- Prove2me | solution 1 for BirkhoffGlobalSection.transverse_isotopy_contact_generator
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-29T21:01:08.720799+00:00
-- url     : https://prove2.me/submissions/9a237cfc-145c-40c8-9d8c-9d9c0ca99ce5

import Definitions.Def_BirkhoffGlobalSection_SphereContact
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Support
import Theorems.Thm_SmoothJetExtension_contDiff_extension_closed_strip
import Theorems.Thm_SmoothJetExtension_moving_circle_first_jet_extension






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



namespace BirkhoffGlobalSection.ContactGenerator
open BirkhoffGlobalSection Set Filter
open scoped ContDiff Topology
noncomputable section

def circleNormalize (u : Plane) : Plane := (Real.sqrt (planeNormSq u))⁻¹ • u

def circleCutoff (u : Plane) : ℝ :=
  Real.smoothTransition (4 * planeNormSq u - 1) *
    Real.smoothTransition (4 - 2 * planeNormSq u)

lemma planeNormSq_pos {u : Plane} (hu : u ≠ 0) : 0 < planeNormSq u := by
  by_contra hn
  have h0 : u 0 = 0 := by dsimp [planeNormSq] at hn; nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
  have h1 : u 1 = 0 := by dsimp [planeNormSq] at hn; nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
  apply hu
  ext i; fin_cases i <;> assumption

lemma planeNormSq_contDiff : ContDiff ℝ ∞ planeNormSq := by unfold planeNormSq; fun_prop

lemma circleNormalize_mem {u : Plane} (hu : u ≠ 0) : circleNormalize u ∈ unitCircle := by
  have hr := planeNormSq_pos hu
  have he : planeNormSq (circleNormalize u) = (Real.sqrt (planeNormSq u))⁻¹ ^ 2 * planeNormSq u := by
    simp [circleNormalize, planeNormSq]
    ring
  change planeNormSq (circleNormalize u) = 1
  rw [he, inv_pow, Real.sq_sqrt hr.le, inv_mul_cancel₀ hr.ne']

lemma circleNormalize_eq {u : Plane} (hu : u ∈ unitCircle) : circleNormalize u = u := by
  have he : planeNormSq u = 1 := hu
  simp [circleNormalize, he]

lemma circleNormalize_contDiffAt {u : Plane} (hu : u ≠ 0) : ContDiffAt ℝ ∞ circleNormalize u := by
  have hr := planeNormSq_pos hu
  exact ((planeNormSq_contDiff.contDiffAt.sqrt hr.ne').inv (Real.sqrt_pos.mpr hr).ne').smul contDiffAt_id

lemma circleCutoff_contDiff : ContDiff ℝ ∞ circleCutoff := by
  unfold circleCutoff
  have hsq := planeNormSq_contDiff
  have hθ : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))
  fun_prop

lemma circleCutoff_one {u : Plane} (hu : u ∈ unitCircle) : circleCutoff u = 1 := by
  have he : planeNormSq u = 1 := hu
  simp only [circleCutoff, he]
  rw [Real.smoothTransition.one_of_one_le (by norm_num),
    Real.smoothTransition.one_of_one_le (by norm_num), one_mul]

lemma circleCutoff_zero_of_small {u : Plane} (hu : planeNormSq u ≤ 1 / 4) : circleCutoff u = 0 := by
  unfold circleCutoff
  rw [Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]

lemma circleCutoff_zero_of_large {u : Plane} (hu : 2 ≤ planeNormSq u) : circleCutoff u = 0 := by
  unfold circleCutoff
  rw [Real.smoothTransition.zero_of_nonpos (x := 4 - 2 * planeNormSq u) (by linarith), mul_zero]

lemma circleCutoff_zero_outside (u : Plane) (hu : u ∉ Metric.closedBall (0 : Plane) 2) : circleCutoff u = 0 := by
  apply circleCutoff_zero_of_large
  by_contra hn
  have hr : planeNormSq u < 2 := lt_of_not_ge hn
  have h0 : |u 0| ≤ 2 := by
    dsimp [planeNormSq] at hr
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
  have h1 : |u 1| ≤ 2 := by
    dsimp [planeNormSq] at hr
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
  have hc : ∀ i : Fin 2, ‖u i‖ ≤ 2 := by
    intro i
    fin_cases i
    · exact h0
    · exact h1
  have hnorm : ‖u‖ ≤ 2 := (pi_norm_le_iff_of_nonneg (by norm_num)).mpr hc
  exact hu (by simpa [Metric.mem_closedBall, dist_zero_right] using hnorm)

end
end BirkhoffGlobalSection.ContactGenerator


set_option backward.isDefEq.respectTransparency false

namespace BirkhoffGlobalSection.ContactGenerator
open BirkhoffGlobalSection Set
open scoped ContDiff
noncomputable section

lemma deriv_eq_of_eqOn_Icc {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : ℝ → F} {a b : F} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hf : HasDerivAt f a t) (hg : HasDerivAt g b t) (heq : EqOn f g (Icc 0 1)) : a = b := by
  apply (uniqueDiffOn_Icc_zero_one t ht).eq_deriv (Icc (0 : ℝ) 1)
    (hf.hasDerivWithinAt.congr heq.symm (heq ht).symm) hg.hasDerivWithinAt

noncomputable def circleCurve (u : Plane) (s : ℝ) : Plane :=
  Real.cos s • u + Real.sin s • circleTangent u

lemma circleCurve_zero (u : Plane) : circleCurve u 0 = u := by simp [circleCurve]

lemma circleCurve_mem (u : Plane) (hu : u ∈ unitCircle) (s : ℝ) : circleCurve u s ∈ unitCircle := by
  have he : planeNormSq (circleCurve u s) =
      (Real.cos s ^ 2 + Real.sin s ^ 2) * planeNormSq u := by
    simp only [circleCurve, circleTangent, planeNormSq, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  change planeNormSq (circleCurve u s) = 1
  rw [he, Real.cos_sq_add_sin_sq, one_mul]
  exact hu

lemma circleCurve_hasDerivAt (u : Plane) : HasDerivAt (circleCurve u) (circleTangent u) 0 := by
  apply hasDerivAt_pi.mpr
  intro i
  have h := ((Real.hasDerivAt_cos 0).mul_const (u i)).add
    ((Real.hasDerivAt_sin 0).mul_const (circleTangent u i))
  change HasDerivAt (fun s => Real.cos s * u i + Real.sin s * circleTangent u i)
    (circleTangent u i) 0
  convert! h using 1 <;>
    simp only [Real.sin_zero, Real.cos_zero, neg_zero, zero_mul, one_mul, zero_add]


lemma fderiv_circle_tangent_eq (f g : Plane → Phase) (u : Plane) (hu : u ∈ unitCircle)
    (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u)
    (he : EqOn f g unitCircle) :
    fderiv ℝ f u (circleTangent u) = fderiv ℝ g u (circleTangent u) := by
  have hf' : DifferentiableAt ℝ f (circleCurve u 0) := by rwa [circleCurve_zero]
  have hg' : DifferentiableAt ℝ g (circleCurve u 0) := by rwa [circleCurve_zero]
  have hff := hf'.hasFDerivAt.comp_hasDerivAt 0 (circleCurve_hasDerivAt u)
  have hgg := hg'.hasFDerivAt.comp_hasDerivAt 0 (circleCurve_hasDerivAt u)
  rw [circleCurve_zero] at hff hgg
  have heq : (fun s => f (circleCurve u s)) = (fun s => g (circleCurve u s)) := by
    funext s
    exact he (circleCurve_mem u hu s)
  change HasDerivAt (fun s => f (circleCurve u s)) (fderiv ℝ f u (circleTangent u)) 0 at hff
  rw [heq] at hff
  exact hff.unique hgg

lemma isotopy_time_hasDerivAt {K : Set Phase} (I : EquivariantTransverseHopfIsotopy K)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (u : Plane) (hu : u ∈ unitCircle) :
    HasDerivAt (fun s => I.isotopy (s, u)) (fderiv ℝ I.isotopy (t, u) (1, 0)) t := by
  have h := (I.smooth t ht u hu).differentiableAt (by simp) |>.hasFDerivAt
  exact h.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t u))

lemma phaseDot_self_hasDerivAt {q : ℝ → Phase} {V : Phase} {t : ℝ}
    (h : HasDerivAt q V t) :
    HasDerivAt (fun s => phaseDot (q s) (q s)) (2 * phaseDot (q t) V) t := by
  have hd := fun i => hasDerivAt_pi.mp h i
  have he := ((((hd 0).mul (hd 0)).add ((hd 1).mul (hd 1))).add
    ((hd 2).mul (hd 2))).add ((hd 3).mul (hd 3))
  apply he.congr_deriv
  simp only [phaseDot]
  ring

lemma isotopy_velocity_tangent {K : Set Phase} (I : EquivariantTransverseHopfIsotopy K)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (u : Plane) (hu : u ∈ unitCircle) :
    phaseDot (I.isotopy (t, u)) (fderiv ℝ I.isotopy (t, u) (1, 0)) = 0 := by
  have hd := phaseDot_self_hasDerivAt (isotopy_time_hasDerivAt I t ht u hu)
  have heq : EqOn (fun s => phaseDot (I.isotopy (s, u)) (I.isotopy (s, u)))
      (fun _ => (1 : ℝ)) (Icc (0 : ℝ) 1) := by
    intro s hs
    have he := I.sphere s hs u hu
    simpa [unitThreeSphere, zNormSq, wNormSq, phaseDot, pow_two, add_assoc] using he
  have hz := deriv_eq_of_eqOn_Icc ht hd (hasDerivAt_const t (1 : ℝ)) heq
  linarith

lemma isotopy_velocity_antipodal {K : Set Phase} (I : EquivariantTransverseHopfIsotopy K)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (u : Plane) (hu : u ∈ unitCircle) :
    fderiv ℝ I.isotopy (t, -u) (1, 0) = - fderiv ℝ I.isotopy (t, u) (1, 0) := by
  have hnu : -u ∈ unitCircle := by simpa [unitCircle, planeNormSq] using hu
  exact deriv_eq_of_eqOn_Icc ht (isotopy_time_hasDerivAt I t ht (-u) hnu)
    (isotopy_time_hasDerivAt I t ht u hu).neg (fun s hs => I.antipodal s hs u hu)

end
end BirkhoffGlobalSection.ContactGenerator

namespace BirkhoffGlobalSection.ContactGenerator
open BirkhoffGlobalSection Set Filter
open scoped ContDiff Topology
noncomputable section

lemma smooth_isotopy_representative {K : Set Phase} (I : EquivariantTransverseHopfIsotopy K) :
    ∃ k : ℝ × Plane → Phase, ContDiff ℝ ∞ k ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ unitCircle,
        k (t, u) = I.isotopy (t, u) ∧
        fderiv ℝ k (t, u) (1, 0) = fderiv ℝ I.isotopy (t, u) (1, 0) ∧
        fderiv ℝ (fun v => k (t, v)) u (circleTangent u) =
          fderiv ℝ (fun v => I.isotopy (t, v)) u (circleTangent u) := by
  let f : Plane × ℝ → Phase := fun p => circleCutoff p.1 • I.isotopy (p.2, circleNormalize p.1)
  have hf : ContDiffOn ℝ ∞ f {p : Plane × ℝ | p.2 ∈ Icc (0 : ℝ) 1} := by
    intro p hp
    by_cases hz : p.1 = 0
    · have hnear : ∀ᶠ q : Plane × ℝ in 𝓝 p, planeNormSq q.1 < 1 / 4 := by
        apply (isOpen_lt (planeNormSq_contDiff.continuous.comp continuous_fst) continuous_const).mem_nhds
        simp [hz, planeNormSq]
      have he : f =ᶠ[𝓝 p] (fun _ => (0 : Phase)) := by
        filter_upwards [hnear] with q hq
        dsimp [f]
        rw [circleCutoff_zero_of_small hq.le, zero_smul]
      exact (contDiffAt_const.congr_of_eventuallyEq he).contDiffWithinAt
    · have hmap : ContDiffAt ℝ ∞ (fun q : Plane × ℝ => (q.2, circleNormalize q.1)) p :=
        contDiffAt_snd.prodMk ((circleNormalize_contDiffAt hz).comp p contDiffAt_fst)
      have hI := I.smooth p.2 hp (circleNormalize p.1) (circleNormalize_mem hz)
      exact (((circleCutoff_contDiff.comp contDiff_fst).contDiffAt).smul (hI.comp p hmap)).contDiffWithinAt
  have hsupp : ∀ p : Plane × ℝ, p.1 ∉ Metric.closedBall (0 : Plane) 2 → f p = 0 := by
    intro p hp
    dsimp [f]
    rw [circleCutoff_zero_outside p.1 hp, zero_smul]
  obtain ⟨H, hH, hHeq⟩ := SmoothJetExtension.contDiff_extension_closed_strip f hf
    (Metric.closedBall (0 : Plane) 2) (isCompact_closedBall _ _) hsupp
  let k : ℝ × Plane → Phase := fun p => H (p.2, p.1)
  have hk : ContDiff ℝ ∞ k := hH.comp (contDiff_snd.prodMk contDiff_fst)
  have hkeq : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ unitCircle, k (t, u) = I.isotopy (t, u) := by
    intro t ht u hu
    have he := hHeq (x := (u, t)) ht
    simpa only [k, f, circleCutoff_one hu, circleNormalize_eq hu, one_smul] using he
  refine ⟨k, hk, ?_⟩
  intro t ht u hu
  refine ⟨hkeq t ht u hu, ?_, ?_⟩
  · have hkt : HasDerivAt (fun s => k (s, u)) (fderiv ℝ k (t, u) (1, 0)) t := by
      exact ((hk.differentiable (by simp) (t, u)).hasFDerivAt).comp_hasDerivAt t
        ((hasDerivAt_id t).prodMk (hasDerivAt_const t u))
    exact deriv_eq_of_eqOn_Icc ht hkt (isotopy_time_hasDerivAt I t ht u hu)
      (fun s hs => hkeq s hs u hu)
  · have hki : DifferentiableAt ℝ (fun v => k (t, v)) u :=
      (hk.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) u
    have hIi : DifferentiableAt ℝ (fun v => I.isotopy (t, v)) u :=
      ((I.smooth t ht u hu).comp u (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
    exact fderiv_circle_tangent_eq _ _ u hu hki hIi (fun v hv => hkeq t ht v hv)

end
end BirkhoffGlobalSection.ContactGenerator

namespace BirkhoffGlobalSection.ContactGenerator
open BirkhoffGlobalSection Set
open scoped ContDiff
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

lemma exists_hamiltonian_prescribed_velocity {K : Set Phase} (I : EquivariantTransverseHopfIsotopy K) :
    ∃ H : ℝ × Phase → ℝ, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ unitCircle,
        contactField (H (t,I.isotopy (t,u))) (spatialGradient H (t,I.isotopy (t,u)))
          (I.isotopy (t,u)) = fderiv ℝ I.isotopy (t,u) (1,0) := by
  obtain ⟨k, hk, hkeq⟩ := smooth_isotopy_representative I
  let V : ℝ × Plane → Phase := fun p => fderiv ℝ k p (1,0)
  let z : ℝ × Plane → Phase := fun p => fderiv ℝ k p (0,circleTangent p.2)
  have hV : ContDiff ℝ ∞ V := (hk.fderiv_right (by simp)).clm_apply contDiff_const
  have hz : ContDiff ℝ ∞ z := (hk.fderiv_right (by simp)).clm_apply
    (contDiff_const.prodMk (circleTangent_contDiff.comp contDiff_snd))
  have hzslice (t : ℝ) (u : Plane) : z (t,u) = fderiv ℝ (fun v => k (t,v)) u (circleTangent u) := by
    have hd := ((hk.differentiable (by simp) (t,u)).hasFDerivAt).comp u
      ((hasFDerivAt_const t u).prodMk (hasFDerivAt_id u))
    change z (t,u) = fderiv ℝ (k ∘ Prod.mk t) u (circleTangent u)
    rw [hd.fderiv]
    rfl
  let h : ℝ × Plane → ℝ := fun p => phaseRadialContact (k p) (V p)
  let d : ℝ × Plane → ℝ := fun p => phaseRadialContact (k p) (z p)
  have hh : ContDiff ℝ ∞ h := contact_contDiff hk hV
  have hd : ContDiff ℝ ∞ d := contact_contDiff hk hz
  have hdpos : ∀ p ∈ (Icc (0 : ℝ) 1 ×ˢ unitCircle), 0 < d p := by
    rintro ⟨t,u⟩ ⟨ht,hu⟩
    dsimp [d]
    rw [(hkeq t ht u hu).1, hzslice, (hkeq t ht u hu).2.2]
    exact I.positive t ht u hu
  let P : Set (ℝ × Plane) := {p | d p ≠ 0}
  have hPo : IsOpen P := isOpen_ne.preimage hd.continuous
  have hAP : (Icc (0 : ℝ) 1 ×ˢ unitCircle) ⊆ P := fun p hp => ne_of_gt (hdpos p hp)
  let hs : ℝ × Plane → ℝ := fun p => fderiv ℝ h p (0,circleTangent p.2)
  let ht : ℝ × Plane → ℝ := fun p => fderiv ℝ h p (1,0)
  have hhs : ContDiff ℝ ∞ hs := (hh.fderiv_right (by simp)).clm_apply
    (contDiff_const.prodMk (circleTangent_contDiff.comp contDiff_snd))
  have hht : ContDiff ℝ ∞ ht := (hh.fderiv_right (by simp)).clm_apply contDiff_const
  let m : ℝ × Plane → ℝ := fun p => (hs p + 2 * phaseRadialContact (V p) (z p)) / d p
  have hm : ContDiffOn ℝ ∞ m P :=
    ((hhs.add (contDiff_const.mul (contact_contDiff hV hz))).contDiffOn).div hd.contDiffOn (fun p hp => hp)
  let g : ℝ × Plane → Phase := fun p => -J (V p) + (m p / 2) • J (k p)
  have hg : ContDiffOn ℝ ∞ g P :=
    ((J_contDiff hV).neg.contDiffOn).add ((hm.div_const 2).smul (J_contDiff hk).contDiffOn)
  let a : ℝ × Plane → ℝ := fun p => ht p - phaseDot (g p) (V p)
  have hdot : ContDiffOn ℝ ∞ (fun p => phaseDot (g p) (V p)) P := by
    have hb : ContDiff ℝ ∞ (fun q : Phase × Phase => phaseDot q.1 q.2) :=
      phaseDot_contDiff contDiff_fst contDiff_snd
    exact hb.comp_contDiffOn (hg.prodMk hV.contDiffOn)
  have ha : ContDiffOn ℝ ∞ a P := hht.contDiffOn.sub hdot
  let L : ℝ × Plane → ((ℝ × Phase) →L[ℝ] ℝ) := fun p =>
    a p • ContinuousLinearMap.fst ℝ ℝ Phase +
      (dotCLM (g p)).comp (ContinuousLinearMap.snd ℝ ℝ Phase)
  have hL : ContDiffOn ℝ ∞ L P := by
    have hgc : ContDiffOn ℝ ∞ (fun p => dotCLM (g p)) P :=
      (dotCLM_contDiff contDiff_id).comp_contDiffOn hg
    exact (ha.smul contDiffOn_const).add (hgc.clm_comp contDiffOn_const)
  have hcomp : ∀ p ∈ (Icc (0 : ℝ) 1 ×ˢ unitCircle), ∀ b c : ℝ,
      fderiv ℝ h p (b,c • circleTangent p.2) =
        L p (b,fderiv ℝ k p (b,c • circleTangent p.2)) := by
    intro p hp b c
    have hpair : phaseDot (g p) (z p) = hs p :=
      compatible_gradient_pairing (k p) (V p) (z p) (hs p) (ne_of_gt (hdpos p hp))
    have hpair' : dotCLM (g p) (z p) = hs p := by rw [dotCLM_apply]; exact hpair
    rw [clm_cylinder_decomposition (fderiv ℝ h p), clm_cylinder_decomposition (fderiv ℝ k p)]
    simp only [L, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd', Prod.fst, Prod.snd,
      map_add, map_smul, smul_eq_mul]
    change b * ht p + c * hs p = a p * b + (b * dotCLM (g p) (V p) + c * dotCLM (g p) (z p))
    rw [hpair', dotCLM_apply]
    dsimp [a]
    ring
  have hinj : InjOn (fun p : ℝ × Plane => (p.1,k p)) (Icc (0 : ℝ) 1 ×ˢ unitCircle) := by
    rintro ⟨t,u⟩ ⟨ht,hu⟩ ⟨s,v⟩ ⟨hs,hv⟩ he
    have hts : t = s := congrArg Prod.fst he
    subst s
    refine Prod.ext (by rfl) ?_
    apply I.injective t ht hu hv
    have heq := congrArg Prod.snd he
    simpa only [(hkeq t ht u hu).1, (hkeq t ht v hv).1] using heq
  have hreg : ∀ p ∈ (Icc (0 : ℝ) 1 ×ˢ unitCircle), fderiv ℝ k p (0,circleTangent p.2) ≠ 0 := by
    intro p hp he
    have hzero : d p = 0 := by dsimp [d,z] at *; rw [he]; simp [phaseRadialContact,phaseSymplecticForm]
    exact (ne_of_gt (hdpos p hp)) hzero
  obtain ⟨H,hH,hHc,hHjet⟩ := SmoothJetExtension.moving_circle_first_jet_extension k hk hinj hreg
    h hh L P hPo hAP hL hcomp
  refine ⟨H,hH,hHc,?_⟩
  intro t htI u hu
  have hp : (t,u) ∈ (Icc (0 : ℝ) 1 ×ˢ unitCircle) := ⟨htI,hu⟩
  have hj := hHjet (t,u) hp
  have hgrad : spatialGradient H (t,k (t,u)) = g (t,u) := by
    ext i
    change fderiv ℝ H (t,k (t,u)) (0,Pi.single i 1) = g (t,u) i
    rw [hj.2]
    dsimp [L]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd', Prod.fst, Prod.snd,
      smul_eq_mul, mul_zero, zero_add, dotCLM_apply]
    fin_cases i <;> simp [phaseDot]
  have hks : phaseDot (k (t,u)) (k (t,u)) = 1 := by
    rw [(hkeq t htI u hu).1]
    exact sphere_dot_self (I.sphere t htI u hu)
  have hkt : phaseDot (k (t,u)) (V (t,u)) = 0 := by
    rw [(hkeq t htI u hu).1, show V (t,u) = fderiv ℝ I.isotopy (t,u) (1,0) from (hkeq t htI u hu).2.1]
    exact isotopy_velocity_tangent I t htI u hu
  have hv := contactField_prescribed (k (t,u)) (V (t,u)) (m (t,u)) hks hkt
  change contactField (h (t,u)) (g (t,u)) (k (t,u)) = V (t,u) at hv
  rw [← hj.1, ← hgrad] at hv
  simpa only [(hkeq t htI u hu).1, show V (t,u) = fderiv ℝ I.isotopy (t,u) (1,0) from (hkeq t htI u hu).2.1] using hv

end
end BirkhoffGlobalSection.ContactGenerator

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

lemma oddAverage_prescribed {K : Set Phase} (I : EquivariantTransverseHopfIsotopy K)
    {X : ℝ → Phase → Phase}
    (hX : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ unitCircle,
      X t (I.isotopy (t,u)) = fderiv ℝ I.isotopy (t,u) (1,0)) :
    ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ unitCircle,
      oddAverage X t (I.isotopy (t,u)) = fderiv ℝ I.isotopy (t,u) (1,0) := by
  intro t ht u hu
  have hnu : -u ∈ unitCircle := by simpa [unitCircle,planeNormSq] using hu
  have hn : X t (-I.isotopy (t,u)) = -fderiv ℝ I.isotopy (t,u) (1,0) := by
    rw [← I.antipodal t ht u hu, hX t ht (-u) hnu, isotopy_velocity_antipodal I t ht u hu]
  ext i
  simp [oddAverage,hX t ht u hu,hn]
  ring

end
end BirkhoffGlobalSection.ContactGenerator

open BirkhoffGlobalSection
open ContactGenerator Set
open scoped ContDiff

theorem solution (K : Set Phase)
    (I : EquivariantTransverseHopfIsotopy K) :
    ∃ X : ℝ → Phase → Phase, ∃ μ : ℝ → Phase → ℝ,
      ContDiff ℝ ∞ (fun p : ℝ × Phase => X p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × Phase => μ p.1 p.2) ∧
      (∃ C : Set Phase, IsCompact C ∧ ∀ t y, y ∉ C → X t y = 0) ∧
      (∀ t y, X t (-y) = -X t y) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ unitThreeSphere, phaseDot y (X t y) = 0) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ unitThreeSphere, ∀ v : Phase, phaseDot y v = 0 →
        phaseRadialContact (X t y) v + phaseRadialContact y (fderiv ℝ (X t) y v) =
          μ t y * phaseRadialContact y v) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ u ∈ unitCircle,
        X t (I.isotopy (t, u)) = fderiv ℝ I.isotopy (t, u) (1, 0)) := by
  obtain ⟨H,hH,hHc,hv⟩ := exists_hamiltonian_prescribed_velocity I
  let X : ℝ → Phase → Phase := fun t y => contactField (H (t,y)) (spatialGradient H (t,y)) y
  let μ : ℝ → Phase → ℝ := fun t y => 2 * phaseDot (J y) (spatialGradient H (t,y))
  have hX : ContDiff ℝ ∞ (fun p : ℝ × Phase => X p.1 p.2) := hamiltonian_field_contDiff hH
  have hμ : ContDiff ℝ ∞ (fun p : ℝ × Phase => μ p.1 p.2) := hamiltonian_factor_contDiff hH
  have htan : ∀ t ∈ Icc (0 : ℝ) 1, ∀ y ∈ unitThreeSphere, phaseDot y (X t y) = 0 := by
    intro t ht y hy
    exact contactField_tangent _ _ _ (sphere_dot_self hy)
  have hlie : ∀ t ∈ Icc (0 : ℝ) 1, ∀ y ∈ unitThreeSphere, ∀ v : Phase, phaseDot y v = 0 →
      phaseRadialContact (X t y) v + phaseRadialContact y (fderiv ℝ (X t) y v) = μ t y * phaseRadialContact y v := by
    intro t ht y hy v hvt
    exact hamiltonian_field_lie hH t y v (sphere_dot_self hy) hvt
  refine ⟨oddAverage X, (fun t y => (μ t y + μ t (-y))/2), oddAverage_contDiff hX, ?_,
    oddAverage_compact_support (hamiltonian_field_compact_support hHc), oddAverage_odd X,
    oddAverage_tangent htan, oddAverage_lie hX hlie, oddAverage_prescribed I hv⟩
  exact (hμ.add (hμ.comp (contDiff_fst.prodMk contDiff_snd.neg))).div_const 2
