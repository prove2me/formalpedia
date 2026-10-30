-- Prove2me | solution 1 for ContactTopology.equivariant_legendrian_neighborhood_fixing
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-29T23:40:34.209381+00:00
-- url     : https://prove2.me/submissions/7da7bad0-555d-4f45-bb4f-3895060fff99

import Definitions.Def_BirkhoffGlobalSection_SphereContact
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
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
import Theorems.Thm_BirkhoffGlobalSection_radial_normalization_contact_identity
import Theorems.Thm_ContactCalculus_exterior_pairing_pullback
import Theorems.Thm_ContactTopology_periodic_legendrian_family_contact_generator
import Theorems.Thm_ContactTopology_sphere_legendrian_core_coordinate_deformation
import Theorems.Thm_FlowCalculus_compact_supported_flow_preserves_regular_level
import Theorems.Thm_FlowCalculus_exists_unique_global_trajectory_of_compact_support
import Theorems.Thm_FlowCalculus_smooth_flow_spatial_derivative_injective
import Theorems.Thm_FlowCalculus_uniform_spatial_lipschitz_of_compact_support
import Theorems.Thm_GrayStability_pullback_family_hasDerivAt
import Theorems.Thm_ParameterizedCalculus_smooth_scalar_linear_transport


namespace ContactTopology
open BirkhoffGlobalSection Set Function Filter
open scoped ContDiff Topology
noncomputable section
abbrev Jet3 := Fin 3 → ℝ
def corePoint (x : ℝ) : Jet3 := ![x,0,0]
def jetContact (p v : Jet3) : ℝ := v 2-p 1*v 0
def normalStrip (e : ℝ) : Set Jet3 := {p | |p 1| < e ∧ |p 2| < e}
lemma normalStrip_isOpen (e : ℝ) : IsOpen (normalStrip e) :=
  (isOpen_lt ((continuous_apply 1).abs) continuous_const).inter
    (isOpen_lt ((continuous_apply 2).abs) continuous_const)
end
end ContactTopology


namespace ContactTopology
open Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

def jetOneForm (p : Jet3) : Jet3 →L[ℝ] ℝ :=
  ContinuousLinearMap.proj 2-p 1 • ContinuousLinearMap.proj 0

lemma jetOneForm_apply (p v : Jet3) : jetOneForm p v = jetContact p v := by
  rfl

lemma jetOneForm_contDiff : ContDiff ℝ ∞ jetOneForm :=
  contDiff_const.sub ((contDiff_apply ℝ ℝ 1).smul contDiff_const)

lemma jetOneForm_fderiv (p u v : Jet3) : fderiv ℝ jetOneForm p u v = -u 1*v 0 := by
  have hd := (hasFDerivAt_const (ContinuousLinearMap.proj 2 : Jet3 →L[ℝ] ℝ) p).sub
    ((ContinuousLinearMap.proj (1:Fin 3) : Jet3 →L[ℝ] ℝ).hasFDerivAt.smul_const
      (ContinuousLinearMap.proj 0 : Jet3 →L[ℝ] ℝ))
  change HasFDerivAt jetOneForm _ p at hd
  rw [hd.fderiv]
  simp

lemma weighted_jetOneForm_fderiv (lam : Jet3 → ℝ) (p u v : Jet3)
    (hlam : DifferentiableAt ℝ lam p) :
    fderiv ℝ (fun q => lam q • jetOneForm q) p u v =
      fderiv ℝ lam p u*jetContact p v-lam p*u 1*v 0 := by
  have hd := hlam.hasFDerivAt.smul (jetOneForm_contDiff.differentiable (by simp) p).hasFDerivAt
  change HasFDerivAt (fun q => lam q • jetOneForm q) _ p at hd
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smul_apply,smul_apply,smul_eq_mul,jetOneForm_apply,jetOneForm_fderiv]
  ring

end
end ContactTopology


namespace ContactTopology
open BirkhoffGlobalSection Set Function
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- A concrete contact coordinate cover about the real Legendrian circle.
Radial normalization gives a sphere map; x+1/2 is the antipodal action. -/
def legendrianChartRaw (p : Jet3) : Phase :=
  ![Real.cos (2*Real.pi*p 0),Real.sin (2*Real.pi*p 0),
    (-2*p 2)*Real.cos (2*Real.pi*p 0)+(p 1/(2*Real.pi))*Real.sin (2*Real.pi*p 0),
    (-2*p 2)*Real.sin (2*Real.pi*p 0)-(p 1/(2*Real.pi))*Real.cos (2*Real.pi*p 0)]

def legendrianSphereChart (p : Jet3) : Phase := radialNormalize (legendrianChartRaw p)

lemma legendrianChartRaw_contDiff : ContDiff ℝ ∞ legendrianChartRaw := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> change ContDiff ℝ ∞ _ <;> dsimp [legendrianChartRaw] <;> fun_prop

lemma legendrianChartRaw_radius_positive (p : Jet3) :
    0 < zNormSq (legendrianChartRaw p)+wNormSq (legendrianChartRaw p) := by
  have htrig := Real.cos_sq_add_sin_sq (2*Real.pi*p 0)
  have hsq₂ := sq_nonneg (legendrianChartRaw p 2)
  have hsq₃ := sq_nonneg (legendrianChartRaw p 3)
  change 0 < legendrianChartRaw p 0^2+legendrianChartRaw p 1^2+
    (legendrianChartRaw p 2^2+legendrianChartRaw p 3^2)
  change Real.cos (2*Real.pi*p 0)^2+Real.sin (2*Real.pi*p 0)^2=1 at htrig
  change legendrianChartRaw p 0^2+legendrianChartRaw p 1^2=1 at htrig
  linarith

lemma legendrianSphereChart_contDiff : ContDiff ℝ ∞ legendrianSphereChart := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  exact (radial_normalization_contact_identity _ (legendrianChartRaw_radius_positive p)).1.comp
    (f := legendrianChartRaw) p legendrianChartRaw_contDiff.contDiffAt

lemma legendrianSphereChart_mem (p : Jet3) : legendrianSphereChart p ∈ unitThreeSphere :=
  (radial_normalization_contact_identity _ (legendrianChartRaw_radius_positive p)).2.1

def legendrianChartRawDerivative (p v : Jet3) : Phase :=
  ![-(2*Real.pi)*Real.sin (2*Real.pi*p 0)*v 0,
    (2*Real.pi)*Real.cos (2*Real.pi*p 0)*v 0,
    (-2*v 2)*Real.cos (2*Real.pi*p 0)+(4*Real.pi*p 2)*Real.sin (2*Real.pi*p 0)*v 0+
      (v 1/(2*Real.pi))*Real.sin (2*Real.pi*p 0)+p 1*Real.cos (2*Real.pi*p 0)*v 0,
    (-2*v 2)*Real.sin (2*Real.pi*p 0)-(4*Real.pi*p 2)*Real.cos (2*Real.pi*p 0)*v 0-
      (v 1/(2*Real.pi))*Real.cos (2*Real.pi*p 0)+p 1*Real.sin (2*Real.pi*p 0)*v 0]

lemma legendrianChartRaw_fderiv (p v : Jet3) :
    fderiv ℝ legendrianChartRaw p v = legendrianChartRawDerivative p v := by
  let c : ℝ → Jet3 := fun s => p+s • v
  have hc : HasDerivAt c v 0 := by
    convert! (hasDerivAt_const (0:ℝ) p).add ((hasDerivAt_id (0:ℝ)).smul_const v) using 1 <;> simp [c]
  have hx := hasDerivAt_pi.mp hc 0
  have hy := hasDerivAt_pi.mp hc 1
  have hz := hasDerivAt_pi.mp hc 2
  have hθ := hx.const_mul (2*Real.pi)
  have hcos := hθ.cos
  have hsin := hθ.sin
  have hP : HasDerivAt (legendrianChartRaw ∘ c) (legendrianChartRawDerivative p v) 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · convert! hcos using 1 <;> simp [c,legendrianChartRaw,legendrianChartRawDerivative] <;> ring
    · convert! hsin using 1 <;> simp [c,legendrianChartRaw,legendrianChartRawDerivative] <;> ring
    · have hd := ((hz.const_mul (-2)).mul hcos).add ((hy.div_const (2*Real.pi)).mul hsin)
      convert! hd using 1 <;> simp [c,legendrianChartRaw,legendrianChartRawDerivative] <;>
        field_simp <;> ring
    · have hd := ((hz.const_mul (-2)).mul hsin).sub ((hy.div_const (2*Real.pi)).mul hcos)
      convert! hd using 1 <;> simp [c,legendrianChartRaw,legendrianChartRawDerivative] <;>
        field_simp <;> ring
  have hdiff : DifferentiableAt ℝ legendrianChartRaw (c 0) := by
    simp only [c,zero_smul,add_zero]
    exact legendrianChartRaw_contDiff.differentiable (by simp) p
  have hd := hdiff.hasFDerivAt.comp_hasDerivAt 0 hc
  simpa only [c,zero_smul,add_zero] using hd.unique hP

lemma legendrianChartRaw_contact (p v : Jet3) :
    phaseRadialContact (legendrianChartRaw p) (fderiv ℝ legendrianChartRaw p v) = jetContact p v := by
  rw [legendrianChartRaw_fderiv]
  have ht := Real.cos_sq_add_sin_sq (2*Real.pi*p 0)
  dsimp [phaseRadialContact,phaseSymplecticForm,legendrianChartRaw,legendrianChartRawDerivative,jetContact]
  field_simp [Real.pi_ne_zero]
  linear_combination (4*Real.pi*(v 2-p 1*v 0))*ht

lemma legendrianSphereChart_contact (p v : Jet3) :
    phaseRadialContact (legendrianSphereChart p) (fderiv ℝ legendrianSphereChart p v) =
      jetContact p v/(zNormSq (legendrianChartRaw p)+wNormSq (legendrianChartRaw p)) := by
  have hN := radial_normalization_contact_identity _ (legendrianChartRaw_radius_positive p)
  have hd := fderiv_comp p (hN.1.differentiableAt (by simp))
    (legendrianChartRaw_contDiff.differentiable (by simp) p)
  change phaseRadialContact (radialNormalize (legendrianChartRaw p))
    (fderiv ℝ (radialNormalize ∘ legendrianChartRaw) p v) = _
  rw [hd]
  change phaseRadialContact (radialNormalize (legendrianChartRaw p))
    (fderiv ℝ radialNormalize (legendrianChartRaw p) (fderiv ℝ legendrianChartRaw p v)) = _
  rw [hN.2.2.2,legendrianChartRaw_contact]

end
end ContactTopology


namespace ContactTopology
open BirkhoffGlobalSection Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma contact_pullback_jet_derivative_injective {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (A : W → W →L[ℝ] ℝ) (F : Jet3 → W) (hF : ContDiff ℝ ∞ F)
    (U : Set Jet3) (hU : IsOpen U) (lam : Jet3 → ℝ) (hlam : ContDiff ℝ ∞ lam)
    (hcontact : ∀ p ∈ U, ∀ v, A (F p) (fderiv ℝ F p v) = lam p*jetContact p v)
    (p : Jet3) (hp : p ∈ U) (hpos : 0 < lam p) (hA : DifferentiableAt ℝ A (F p)) :
    Injective (fderiv ℝ F p) := by
  have heq : (fun q => (A (F q)).comp (fderiv ℝ F q)) =ᶠ[𝓝 p] (fun q => lam q • jetOneForm q) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    ext v
    exact hcontact q hq v
  apply (injective_iff_map_eq_zero _).mpr
  intro u hu
  have hαu : jetContact p u = 0 := by
    have hm : lam p*jetContact p u = 0 := by rw [← hcontact p hp u,hu,map_zero]
    exact (mul_eq_zero.mp hm).resolve_left hpos.ne'
  have hz : ∀ v : Jet3, jetContact p v = 0 → lam p*(u 0*v 1-u 1*v 0) = 0 := by
    intro v hv
    have hpb := ContactCalculus.exterior_pairing_pullback A F p u v hA
      (hF.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    rw [heq.fderiv_eq,weighted_jetOneForm_fderiv lam p u v (hlam.differentiable (by simp) p),
      weighted_jetOneForm_fderiv lam p v u (hlam.differentiable (by simp) p),hu,hαu,hv] at hpb
    simp only [map_zero,mul_zero,zero_sub,sub_zero,ContinuousLinearMap.zero_apply] at hpb
    nlinarith [hpb]
  have hm₀ := hz (Pi.single 1 1) (by simp [jetContact])
  have hu₀ : u 0 = 0 := by
    have he : lam p*u 0 = 0 := by simpa using hm₀
    exact (mul_eq_zero.mp he).resolve_left hpos.ne'
  have hm₁ := hz (Pi.single 0 1+p 1 • Pi.single 2 1) (by simp [jetContact])
  have hu₁ : u 1 = 0 := by
    have hh : lam p * (-u 1) = 0 := by simpa [hu₀] using hm₁
    have hh' : lam p * u 1 = 0 := by nlinarith [hh]
    exact (mul_eq_zero.mp hh').resolve_left hpos.ne'
  have hu₂ : u 2 = 0 := by simpa [jetContact,hu₀] using hαu
  ext i
  fin_cases i
  · exact hu₀
  · exact hu₁
  · exact hu₂

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

def legendrianChartWeight (p : Jet3) : ℝ :=
  (zNormSq (legendrianChartRaw p)+wNormSq (legendrianChartRaw p))⁻¹

lemma legendrianChartWeight_contDiff : ContDiff ℝ ∞ legendrianChartWeight := by
  have hP := legendrianChartRaw_contDiff
  have hQ : ContDiff ℝ ∞ (fun p => zNormSq (legendrianChartRaw p)+wNormSq (legendrianChartRaw p)) := by
    dsimp [zNormSq,wNormSq]
    fun_prop
  exact hQ.inv (fun p => (legendrianChartRaw_radius_positive p).ne')

lemma legendrianSphereChart_derivative_injective (p : Jet3) :
    Injective (fderiv ℝ legendrianSphereChart p) := by
  apply contact_pullback_jet_derivative_injective sphereRadialForm legendrianSphereChart
    legendrianSphereChart_contDiff univ isOpen_univ legendrianChartWeight legendrianChartWeight_contDiff
    (fun p hp v => ?_) p (mem_univ p) (inv_pos.mpr (legendrianChartRaw_radius_positive p))
    (sphereRadialForm_contDiff.differentiable (by simp) _)
  simpa only [sphereRadialForm_apply,legendrianChartWeight,div_eq_mul_inv,mul_comm] using legendrianSphereChart_contact p v

lemma legendrianChartRaw_antipodal (p : Jet3) :
    legendrianChartRaw (p+corePoint (1/2)) = -legendrianChartRaw p := by
  have hθ : 2*Real.pi*(p 0+1/2) = 2*Real.pi*p 0+Real.pi := by ring
  ext i
  fin_cases i <;> dsimp [legendrianChartRaw,corePoint] <;>
    simp only [add_zero,hθ,Real.cos_add_pi,Real.sin_add_pi] <;> ring

lemma legendrianSphereChart_antipodal (p : Jet3) :
    legendrianSphereChart (p+corePoint (1/2)) = -legendrianSphereChart p := by
  change radialNormalize (legendrianChartRaw (p+corePoint (1/2))) = -radialNormalize (legendrianChartRaw p)
  rw [legendrianChartRaw_antipodal]
  exact (radial_normalization_contact_identity _ (legendrianChartRaw_radius_positive p)).2.2.1

lemma legendrianSphereChart_periodic (p : Jet3) :
    legendrianSphereChart (p+corePoint 1) = legendrianSphereChart p := by
  have ha : corePoint (1/2)+corePoint (1/2) = corePoint 1 := by
    ext i
    fin_cases i <;> norm_num [corePoint]
  have he : (p+corePoint (1/2))+corePoint (1/2) = p+corePoint 1 := by
    rw [add_assoc,ha]
  rw [← he,legendrianSphereChart_antipodal,legendrianSphereChart_antipodal,neg_neg]

lemma legendrianSphereChart_core (x : ℝ) :
    legendrianSphereChart (corePoint x) = ![Real.cos (2*Real.pi*x),Real.sin (2*Real.pi*x),0,0] := by
  have hraw : legendrianChartRaw (corePoint x) = ![Real.cos (2*Real.pi*x),Real.sin (2*Real.pi*x),0,0] := by
    simp [legendrianChartRaw,corePoint]
  have hQ : zNormSq (legendrianChartRaw (corePoint x))+wNormSq (legendrianChartRaw (corePoint x)) = 1 := by
    rw [hraw]
    simpa [zNormSq,wNormSq] using Real.cos_sq_add_sin_sq (2*Real.pi*x)
  change (Real.sqrt (zNormSq (legendrianChartRaw (corePoint x))+
    wNormSq (legendrianChartRaw (corePoint x))))⁻¹ • legendrianChartRaw (corePoint x) = _
  rw [hQ,Real.sqrt_one,inv_one,one_smul,hraw]

end
end ContactTopology


namespace BirkhoffGlobalSection.HopfTransport
open BirkhoffGlobalSection Set
open scoped ContDiff
noncomputable section

lemma sphere_dot_self {y : Phase} (hy : y ∈ unitThreeSphere) : phaseDot y y = 1 := by
  change zNormSq y + wNormSq y = 1 at hy
  simp [zNormSq,wNormSq,phaseDot] at hy ⊢
  nlinarith

lemma dot_hasDerivAt {q g : ℝ → Phase} {v b : Phase} {t : ℝ}
    (hq : HasDerivAt q v t) (hg : HasDerivAt g b t) :
    HasDerivAt (fun s => phaseDot (q s) (g s)) (phaseDot v (g t) + phaseDot (q t) b) t := by
  have h := fun i => hasDerivAt_pi.mp hq i
  have k := fun i => hasDerivAt_pi.mp hg i
  have hd := ((((h 0).mul (k 0)).add ((h 1).mul (k 1))).add ((h 2).mul (k 2))).add ((h 3).mul (k 3))
  apply hd.congr_deriv
  simp only [phaseDot]
  ring

lemma dot_self_hasDerivAt {q : ℝ → Phase} {v : Phase} {t : ℝ} (hq : HasDerivAt q v t) :
    HasDerivAt (fun s => phaseDot (q s) (q s)) (2 * phaseDot (q t) v) t := by
  apply (dot_hasDerivAt hq hq).congr_deriv
  simp [phaseDot]
  ring

end
end BirkhoffGlobalSection.HopfTransport


namespace ContactTopology
open BirkhoffGlobalSection BirkhoffGlobalSection.HopfTransport Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section
lemma legendrianSphereChart_fderiv_tangent (p v : Jet3) :
    phaseDot (legendrianSphereChart p) (fderiv ℝ legendrianSphereChart p v) = 0 := by
  let c : ℝ → Jet3 := fun t => p+t • v
  have hc : HasDerivAt c v 0 := by
    convert! (hasDerivAt_const (0:ℝ) p).add ((hasDerivAt_id (0:ℝ)).smul_const v) using 1 <;> simp [c]
  have hd := (legendrianSphereChart_contDiff.differentiable (by simp) (c 0)).hasFDerivAt.comp_hasDerivAt 0 hc
  have hsq := dot_self_hasDerivAt hd
  have heq : (fun t => phaseDot (legendrianSphereChart (c t)) (legendrianSphereChart (c t))) = fun _ => (1:ℝ) := by
    funext t
    exact sphere_dot_self (legendrianSphereChart_mem _)
  change HasDerivAt (fun t => phaseDot (legendrianSphereChart (c t)) (legendrianSphereChart (c t))) _ 0 at hsq
  rw [heq] at hsq
  have he := hsq.unique (hasDerivAt_const (0:ℝ) (1:ℝ))
  simp only [Function.comp_apply,c,zero_smul,add_zero] at he
  linarith

def legendrianChartRadialExtension (q : ℝ × Jet3) : Phase :=
  q.1 • legendrianSphereChart q.2

lemma legendrianChartRadialExtension_contDiff : ContDiff ℝ ∞ legendrianChartRadialExtension :=
  contDiff_fst.smul (legendrianSphereChart_contDiff.comp contDiff_snd)

end
end ContactTopology


namespace ContactTopology
open BirkhoffGlobalSection Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Global smoothness and invertibility throughout an open source set give
one genuine open target neighborhood with a smooth inverse on all of it. -/
lemma smooth_local_inverse_on_open {E V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (F : E → V) (hF : ContDiff ℝ ∞ F)
    (U : Set E) (hU : IsOpen U) (hinj : ∀ p ∈ U, Injective (fderiv ℝ F p))
    (p : E) (hp : p ∈ U) (hdim : Module.finrank ℝ E = Module.finrank ℝ V) :
    ∃ R : V → E, ∃ W : Set V, IsOpen W ∧ F p ∈ W ∧ ContDiffOn ℝ ∞ R W ∧
      R (F p) = p ∧ (∀ᶠ x in 𝓝 p, R (F x) = x) ∧
      ∀ y ∈ W, F (R y) = y ∧ R y ∈ U := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  let A : E ≃L[ℝ] V := (LinearEquiv.ofBijective (fderiv ℝ F p).toLinearMap
    ⟨hinj p hp,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp (hinj p hp)⟩).toContinuousLinearEquiv
  have hd : HasFDerivAt F (A : E →L[ℝ] V) p := (hF.differentiable (by simp) p).hasFDerivAt
  let e := hF.contDiffAt.toOpenPartialHomeomorph F hd (by simp)
  have he : (e : E → V) = F := hF.contDiffAt.toOpenPartialHomeomorph_coe hd (by simp)
  have hpe : p ∈ e.source := hF.contDiffAt.mem_toOpenPartialHomeomorph_source hd (by simp)
  have hFp : F p ∈ e.target := hF.contDiffAt.image_mem_toOpenPartialHomeomorph_target hd (by simp)
  have hbase : e.symm (F p) = p := by
    have hh := e.left_inv hpe
    rwa [he] at hh
  let W := e.target ∩ e.symm ⁻¹' U
  have hW : IsOpen W := e.isOpen_inter_preimage_symm hU
  refine ⟨e.symm,W,hW,⟨hFp,?_⟩,?_,hbase,?_,?_⟩
  · change e.symm (F p) ∈ U
    rwa [hbase]
  · intro y hy
    let B : E ≃L[ℝ] V := (LinearEquiv.ofBijective (fderiv ℝ F (e.symm y)).toLinearMap
      ⟨hinj _ hy.2,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp (hinj _ hy.2)⟩).toContinuousLinearEquiv
    have hdf : HasFDerivAt (e : E → V) (B : E →L[ℝ] V) (e.symm y) := by
      rw [he]
      exact (hF.differentiable (by simp) _).hasFDerivAt
    have hfe : ContDiffAt ℝ ∞ (e : E → V) (e.symm y) := by rw [he]; exact hF.contDiffAt
    exact (e.contDiffAt_symm hy.1 hdf hfe).contDiffWithinAt
  · filter_upwards [e.open_source.mem_nhds hpe] with x hx
    have hh := e.left_inv hx
    rwa [he] at hh
  · intro y hy
    refine ⟨?_,hy.2⟩
    have hh := e.right_inv hy.1
    rwa [he] at hh

end
end ContactTopology


namespace ContactTopology
open BirkhoffGlobalSection BirkhoffGlobalSection.HopfTransport Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma legendrianChartRadialExtension_derivative_injective_positive (r : ℝ) (hr : 0 < r) (p : Jet3) :
    Injective (fderiv ℝ legendrianChartRadialExtension (r,p)) := by
  have hd := (hasFDerivAt_fst (𝕜 := ℝ) (p := (r,p))).smul
    ((legendrianSphereChart_contDiff.differentiable (by simp) p).hasFDerivAt.comp (r,p) hasFDerivAt_snd)
  change HasFDerivAt legendrianChartRadialExtension _ (r,p) at hd
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  rw [hd.fderiv] at hv
  change r • fderiv ℝ legendrianSphereChart p v.2+v.1 • legendrianSphereChart p = 0 at hv
  have hdot := congrArg (phaseDot (legendrianSphereChart p)) hv
  have heq : phaseDot (legendrianSphereChart p)
      (r • fderiv ℝ legendrianSphereChart p v.2+v.1 • legendrianSphereChart p) =
      r*phaseDot (legendrianSphereChart p) (fderiv ℝ legendrianSphereChart p v.2)+
        v.1*phaseDot (legendrianSphereChart p) (legendrianSphereChart p) := by
    simp [phaseDot]
    ring
  rw [heq,sphere_dot_self (legendrianSphereChart_mem p),legendrianSphereChart_fderiv_tangent] at hdot
  have hv₁ : v.1 = 0 := by simpa [phaseDot] using hdot
  rw [hv₁,zero_smul,add_zero] at hv
  have hvd : fderiv ℝ legendrianSphereChart p v.2 = 0 := (smul_eq_zero.mp hv).resolve_left hr.ne'
  have hv₂ : v.2 = 0 := (legendrianSphereChart_derivative_injective p) (by simpa using hvd)
  exact Prod.ext hv₁ hv₂

lemma legendrianSphereChart_open_inverse (p : Jet3) :
    ∃ c : Phase → Jet3, ∃ V : Set Phase, IsOpen V ∧ legendrianSphereChart p ∈ V ∧
      ContDiffOn ℝ ∞ c V ∧ c (legendrianSphereChart p) = p ∧
      (∀ᶠ q in 𝓝 p, c (legendrianSphereChart q) = q) ∧
      ∀ y ∈ V, y ∈ unitThreeSphere → legendrianSphereChart (c y) = y := by
  let U : Set (ℝ × Jet3) := Ioi (0:ℝ) ×ˢ univ
  have hU : IsOpen U := isOpen_Ioi.prod isOpen_univ
  have hdim : Module.finrank ℝ (ℝ × Jet3) = Module.finrank ℝ Phase := by
    simp [Jet3,Phase,Module.finrank_prod]
  obtain ⟨R,V,hV,hVp,hR,hRp,hleft,hright⟩ := smooth_local_inverse_on_open
    legendrianChartRadialExtension legendrianChartRadialExtension_contDiff U hU
    (fun q hq => legendrianChartRadialExtension_derivative_injective_positive q.1 hq.1 q.2)
    (1,p) ⟨by norm_num,mem_univ p⟩ hdim
  have hval : legendrianChartRadialExtension (1,p) = legendrianSphereChart p := by
    simp [legendrianChartRadialExtension]
  rw [hval] at hVp hRp
  have hc : ContDiffOn ℝ ∞ (fun y => (R y).2) V := contDiff_snd.comp_contDiffOn hR
  refine ⟨fun y => (R y).2,V,hV,hVp,hc,congrArg Prod.snd hRp,?_,?_⟩
  · have hi : Tendsto (fun q : Jet3 => ((1:ℝ),q)) (𝓝 p) (𝓝 (1,p)) :=
      (continuous_const.prodMk continuous_id).continuousAt
    filter_upwards [hi.eventually hleft] with q hq
    have hh := congrArg Prod.snd hq
    simpa [legendrianChartRadialExtension] using hh
  · intro y hy hys
    have hh := hright y hy
    have hrpos : 0 < (R y).1 := hh.2.1
    have heq : (R y).1 • legendrianSphereChart (R y).2 = y := hh.1
    have hunit := sphere_dot_self hys
    have hchart := sphere_dot_self (legendrianSphereChart_mem (R y).2)
    have hscale : phaseDot ((R y).1 • legendrianSphereChart (R y).2)
        ((R y).1 • legendrianSphereChart (R y).2) =
        (R y).1^2*phaseDot (legendrianSphereChart (R y).2) (legendrianSphereChart (R y).2) := by
      simp [phaseDot]
      ring
    have hsq : (R y).1^2 = 1 := by rwa [← heq,hscale,hchart,mul_one] at hunit
    have hr : (R y).1 = 1 := by nlinarith
    simpa only [hr,one_smul] using heq

end
end ContactTopology



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

namespace ContactTopology
open BirkhoffGlobalSection Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

abbrev TubeCoord := Fin 3 → ℝ

def tubeRaw (p : TubeCoord) : Phase :=
  ![Real.cos (2*Real.pi*p 0),Real.sin (2*Real.pi*p 0),
    (-2*p 2)*Real.cos (2*Real.pi*p 0)+(p 1/(2*Real.pi))*Real.sin (2*Real.pi*p 0),
    (-2*p 2)*Real.sin (2*Real.pi*p 0)-(p 1/(2*Real.pi))*Real.cos (2*Real.pi*p 0)]

def tubeChart (p : TubeCoord) : Phase := radialNormalize (tubeRaw p)

lemma tubeRaw_contDiff : ContDiff ℝ ∞ tubeRaw := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [tubeRaw] <;> fun_prop

lemma tubeRaw_radius_positive (p : TubeCoord) : 0 < zNormSq (tubeRaw p)+wNormSq (tubeRaw p) := by
  have ht := Real.cos_sq_add_sin_sq (2*Real.pi*p 0)
  have hs₂ := sq_nonneg (tubeRaw p 2)
  have hs₃ := sq_nonneg (tubeRaw p 3)
  change 0 < tubeRaw p 0^2+tubeRaw p 1^2+(tubeRaw p 2^2+tubeRaw p 3^2)
  change Real.cos (2*Real.pi*p 0)^2+Real.sin (2*Real.pi*p 0)^2=1 at ht
  change tubeRaw p 0^2+tubeRaw p 1^2=1 at ht
  linarith

lemma tubeChart_contDiff : ContDiff ℝ ∞ tubeChart := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  exact (radial_normalization_contact_identity _ (tubeRaw_radius_positive p)).1.comp
    (f := tubeRaw) p tubeRaw_contDiff.contDiffAt

/-- A sphere contactomorphism fixing the real Legendrian circle can be
corrected, through an equivariant ambient contact isotopy from identity,
to the identity on a uniform Legendrian coordinate tube. -/
lemma equivariant_legendrian_neighborhood_correction (F : EquivariantSphereContactomorphism)
    (hcore : ∀ x : ℝ, F.toFun ![Real.cos (2*Real.pi*x),Real.sin (2*Real.pi*x),0,0] =
      ![Real.cos (2*Real.pi*x),Real.sin (2*Real.pi*x),0,0]) :
    ∃ C : EquivariantSphereContactomorphism, Nonempty (EquivariantSphereContactIsotopy C) ∧
      ∃ d : ℝ, 0 < d ∧ ∀ p : TubeCoord, |p 1| < d → |p 2| < d →
        C.toFun (F.toFun (tubeChart p)) = tubeChart p := by
  obtain ⟨e,he,H,hH,hH1,hHcore,hHhalf,hstart,hcontact⟩ :=
    ContactTopology.sphere_legendrian_core_coordinate_deformation F hcore
  let sig : ℝ → ℝ := fun t => Real.smoothTransition t
  have hsig : ContDiff ℝ ∞ sig := Real.smoothTransition.contDiff (n := (⊤:ℕ∞))
  have hsig0 : sig 0 = 0 := Real.smoothTransition.zero_of_nonpos (by norm_num)
  have hsig1 : sig 1 = 1 := Real.smoothTransition.one_of_one_le (by norm_num)
  have hsigmem : ∀ t, sig t ∈ Icc (0:ℝ) 1 := fun t =>
    ⟨Real.smoothTransition.nonneg t,Real.smoothTransition.le_one t⟩
  let K : ℝ → TubeCoord → TubeCoord := fun t => H (sig t)
  have hK : ContDiff ℝ ∞ (fun q : ℝ × TubeCoord => K q.1 q.2) :=
    hH.comp ((hsig.comp contDiff_fst).prodMk contDiff_snd)
  have hK1 : K 1 = id := by change H (sig 1) = id; rw [hsig1,hH1]
  have hKhalf : ∀ t p, K t (p+![1/2,0,0]) = K t p+![1/2,0,0] := fun t p => hHhalf _ p
  have hKinj : ∀ t, InjOn (K t) {p | |p 1| < e ∧ |p 2| < e} := fun t =>
    (hcontact _ (hsigmem t)).1
  have hKcontact : ∀ t p, |p 1| < e ∧ |p 2| < e → ∃ a : ℝ, 0 < a ∧ ∀ v : TubeCoord,
      (fderiv ℝ (K t) p v) 2-(K t p) 1*(fderiv ℝ (K t) p v) 0 = a*(v 2-p 1*v 0) := fun t =>
    (hcontact _ (hsigmem t)).2
  obtain ⟨d,hd,hde,X,mu,hX,hmu,hsupp,hodd,htan,hlie,hvel⟩ :=
    ContactTopology.periodic_legendrian_family_contact_generator e he K hK hKinj hKhalf hKcontact
  obtain ⟨C,hCiso,psi,hC,h0,hflow⟩ := contact_generator_flow_isotopy X mu hX hmu hsupp hodd htan hlie
  obtain ⟨L,hL⟩ := FlowCalculus.uniform_spatial_lipschitz_of_compact_support X hX hsupp 0 1
  have hfollow : ∀ p : TubeCoord, |p 1| ≤ d → |p 2| ≤ d →
      psi 1 (tubeChart (K 0 p)) = tubeChart (K 1 p) := by
    intro p hp₁ hp₂
    have hA : ContDiff ℝ ∞ (fun q : ℝ × TubeCoord => tubeChart (K q.1 q.2)) := tubeChart_contDiff.comp hK
    have hb : ∀ t ∈ Icc (0:ℝ) 1,
        HasDerivAt (fun t => tubeChart (K t p)) (X t (tubeChart (K t p))) t := by
      intro t ht
      have hh : X t (tubeChart (K t p)) =
          fderiv ℝ (fun q : ℝ × TubeCoord => tubeChart (K q.1 q.2)) (t,p) (1,0) := hvel t ht p hp₁ hp₂
      rw [hh]
      exact (hA.differentiable (by simp) (t,p)).hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_id t).prodMk (hasDerivAt_const t p))
    have heq := ODE_solution_unique_of_mem_Icc_right (v := X) (s := fun _ => univ) (K := L)
      (f := fun t => psi t (tubeChart (K 0 p))) (g := fun t => tubeChart (K t p))
      (fun t ht => (hL t (Ico_subset_Icc_self ht)).lipschitzOnWith)
      (HasDerivAt.continuousOn fun t ht => hflow t _)
      (fun t ht => (hflow t _).hasDerivWithinAt) (fun t ht => trivial)
      (HasDerivAt.continuousOn fun t ht => hb t ht)
      (fun t ht => (hb t (Ico_subset_Icc_self ht)).hasDerivWithinAt) (fun t ht => trivial)
      (by simp [h0])
    exact heq ⟨zero_le_one,le_rfl⟩
  refine ⟨C,hCiso,d,hd,?_⟩
  intro p hp₁ hp₂
  have hstartK : tubeChart (K 0 p) = F.toFun (tubeChart p) := by
    change tubeChart (H (sig 0) p) = _
    rw [hsig0]
    exact hstart p ⟨hp₁.trans hde,hp₂.trans hde⟩
  rw [hC,← hstartK,hfollow p hp₁.le hp₂.le,hK1]
  rfl

end
end ContactTopology

namespace ContactTopology
open BirkhoffGlobalSection BirkhoffGlobalSection.HopfTransport Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma legendrian_strip_contains_sphere_neighborhood (d : ℝ) (hd : 0 < d) :
    ∃ O : Set Phase, IsOpen O ∧
      (∀ x : ℝ, ![Real.cos (2*Real.pi*x),Real.sin (2*Real.pi*x),0,0] ∈ O) ∧
      O ∩ unitThreeSphere ⊆ legendrianSphereChart '' normalStrip d := by
  let T := legendrianSphereChart '' normalStrip d
  let O : Set Phase := {y | ∃ V : Set Phase, IsOpen V ∧ y ∈ V ∧ V ∩ unitThreeSphere ⊆ T}
  have hO : IsOpen O := by
    apply isOpen_iff_mem_nhds.mpr
    rintro y ⟨V,hV,hyV,hsub⟩
    apply mem_of_superset (hV.mem_nhds hyV)
    intro z hz
    exact ⟨V,hV,hz,hsub⟩
  have hTO : T ⊆ O := by
    rintro y ⟨p,hp,rfl⟩
    obtain ⟨c,V,hV,hVp,hc,hcp,hcleft,hcright⟩ := legendrianSphereChart_open_inverse p
    let P := V ∩ c ⁻¹' normalStrip d
    have hP : IsOpen P := hc.continuousOn.isOpen_inter_preimage hV (normalStrip_isOpen d)
    have hPp : legendrianSphereChart p ∈ P := ⟨hVp,by change c (legendrianSphereChart p) ∈ normalStrip d; rwa [hcp]⟩
    refine ⟨P,hP,hPp,?_⟩
    intro z hz
    exact ⟨c z,hz.1.2,hcright z hz.1.1 hz.2⟩
  refine ⟨O,hO,?_,?_⟩
  · intro x
    apply hTO
    refine ⟨corePoint x,?_,legendrianSphereChart_core x⟩
    change |(0:ℝ)| < d ∧ |(0:ℝ)| < d
    simpa using And.intro hd hd
  · rintro y ⟨⟨V,hV,hyV,hsub⟩,hyS⟩
    exact hsub ⟨hyV,hyS⟩

/-- Equivariant ambient Legendrian neighborhood fixing, with an actual open
sphere neighborhood rather than only a coordinate deformation. -/
lemma equivariant_legendrian_neighborhood_fixing (F : EquivariantSphereContactomorphism)
    (hcore : ∀ x : ℝ, F.toFun ![Real.cos (2*Real.pi*x),Real.sin (2*Real.pi*x),0,0] =
      ![Real.cos (2*Real.pi*x),Real.sin (2*Real.pi*x),0,0]) :
    ∃ C : EquivariantSphereContactomorphism, Nonempty (EquivariantSphereContactIsotopy C) ∧
      ∃ O : Set Phase, IsOpen O ∧
        (∀ x : ℝ, ![Real.cos (2*Real.pi*x),Real.sin (2*Real.pi*x),0,0] ∈ O) ∧
        ∀ y ∈ O ∩ unitThreeSphere, C.toFun (F.toFun y) = y := by
  obtain ⟨C,hC,d,hd,hfix⟩ := equivariant_legendrian_neighborhood_correction F hcore
  obtain ⟨O,hO,hcoreO,hsub⟩ := legendrian_strip_contains_sphere_neighborhood d hd
  refine ⟨C,hC,O,hO,hcoreO,?_⟩
  intro y hy
  obtain ⟨p,hp,hpy⟩ := hsub hy
  rw [← hpy]
  exact hfix p hp.1 hp.2

end
end ContactTopology

theorem solution (F : BirkhoffGlobalSection.EquivariantSphereContactomorphism)
    (hcore : ∀ x : ℝ,
      F.toFun ![Real.cos (2*Real.pi*x),Real.sin (2*Real.pi*x),0,0] =
        ![Real.cos (2*Real.pi*x),Real.sin (2*Real.pi*x),0,0]) :
    ∃ C : BirkhoffGlobalSection.EquivariantSphereContactomorphism,
      Nonempty (BirkhoffGlobalSection.EquivariantSphereContactIsotopy C) ∧
      ∃ O : Set BirkhoffGlobalSection.Phase, IsOpen O ∧
        (∀ x : ℝ, ![Real.cos (2*Real.pi*x),Real.sin (2*Real.pi*x),0,0] ∈ O) ∧
        ∀ y ∈ O ∩ BirkhoffGlobalSection.unitThreeSphere, C.toFun (F.toFun y) = y := by
  exact ContactTopology.equivariant_legendrian_neighborhood_fixing F hcore
