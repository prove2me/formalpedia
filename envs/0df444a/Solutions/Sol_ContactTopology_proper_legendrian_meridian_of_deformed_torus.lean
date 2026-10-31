-- Prove2me | solution 1 for ContactTopology.proper_legendrian_meridian_of_deformed_torus
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-31T02:52:00.345598+00:00
-- url     : https://prove2.me/submissions/6462c877-3fbf-4f83-8fa8-d893baf5bded

import Definitions.Def_ContactTopology_MeridianTorus
import Definitions.Def_BirkhoffGlobalSection_SphereContact
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Theorems.Thm_BirkhoffGlobalSection_radial_normalization_contact_identity
import Theorems.Thm_ContactCalculus_exterior_pairing_pullback
import Theorems.Thm_FlowCalculus_compact_supported_flow_preserves_regular_level
import Theorems.Thm_FlowCalculus_exists_unique_global_trajectory_of_compact_support
import Theorems.Thm_FlowCalculus_smooth_flow_spatial_derivative_injective
import Theorems.Thm_FlowCalculus_uniform_spatial_lipschitz_of_compact_support



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

namespace ContactTopology
open BirkhoffGlobalSection BirkhoffGlobalSection.HopfTransport Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

def legendrianNormalY (y : Phase) : ℝ :=
  -2*Real.pi*(y 0*y 3-y 1*y 2)/zNormSq y

def legendrianNormalZ (y : Phase) : ℝ :=
  -(y 0*y 2+y 1*y 3)/(2*zNormSq y)

lemma legendrianNormalY_contDiffAt (y : Phase) (hy : zNormSq y ≠ 0) :
    ContDiffAt ℝ ∞ legendrianNormalY y := by
  have hnum : ContDiffAt ℝ ∞ (fun q : Phase => -2*Real.pi*(q 0*q 3-q 1*q 2)) y := by fun_prop
  have hden : ContDiffAt ℝ ∞ zNormSq y :=
    (((contDiff_apply ℝ ℝ 0).pow 2).add ((contDiff_apply ℝ ℝ 1).pow 2)).contDiffAt
  exact hnum.div hden hy

lemma legendrianNormalZ_contDiffAt (y : Phase) (hy : zNormSq y ≠ 0) :
    ContDiffAt ℝ ∞ legendrianNormalZ y := by
  have hh : 2*zNormSq y ≠ 0 := mul_ne_zero (by norm_num) hy
  have hnum : ContDiffAt ℝ ∞ (fun q : Phase => -(q 0*q 2+q 1*q 3)) y := by fun_prop
  have hden : ContDiffAt ℝ ∞ (fun q : Phase => 2*zNormSq q) y := by dsimp [zNormSq]; fun_prop
  exact hnum.div hden hh

lemma zNormSq_smul (a : ℝ) (y : Phase) : zNormSq (a • y) = a^2*zNormSq y := by
  simp [zNormSq]
  ring

lemma legendrianNormalY_smul (a : ℝ) (ha : a ≠ 0) (y : Phase) (hy : zNormSq y ≠ 0) :
    legendrianNormalY (a • y) = legendrianNormalY y := by
  unfold legendrianNormalY
  rw [zNormSq_smul]
  simp only [Pi.smul_apply,smul_eq_mul]
  field_simp
  <;> ring

lemma legendrianNormalZ_smul (a : ℝ) (ha : a ≠ 0) (y : Phase) (hy : zNormSq y ≠ 0) :
    legendrianNormalZ (a • y) = legendrianNormalZ y := by
  unfold legendrianNormalZ
  rw [zNormSq_smul]
  simp only [Pi.smul_apply,smul_eq_mul]
  field_simp
  <;> ring

lemma legendrianChartRaw_zNormSq (p : Jet3) : zNormSq (legendrianChartRaw p) = 1 := by
  simpa [zNormSq,legendrianChartRaw] using Real.cos_sq_add_sin_sq (2*Real.pi*p 0)

lemma legendrianNormalY_raw (p : Jet3) : legendrianNormalY (legendrianChartRaw p) = p 1 := by
  unfold legendrianNormalY
  rw [legendrianChartRaw_zNormSq]
  dsimp [legendrianChartRaw]
  have ht := Real.cos_sq_add_sin_sq (2*Real.pi*p 0)
  field_simp [Real.pi_ne_zero]
  linear_combination (p 1)*ht

lemma legendrianNormalZ_raw (p : Jet3) : legendrianNormalZ (legendrianChartRaw p) = p 2 := by
  unfold legendrianNormalZ
  rw [legendrianChartRaw_zNormSq]
  dsimp [legendrianChartRaw]
  have ht := Real.cos_sq_add_sin_sq (2*Real.pi*p 0)
  field_simp [Real.pi_ne_zero]
  linear_combination (4*Real.pi*p 2)*ht

lemma legendrianNormalY_chart (p : Jet3) : legendrianNormalY (legendrianSphereChart p) = p 1 := by
  change legendrianNormalY ((Real.sqrt (zNormSq (legendrianChartRaw p)+wNormSq (legendrianChartRaw p)))⁻¹ • legendrianChartRaw p) = _
  rw [legendrianNormalY_smul _ (inv_ne_zero (Real.sqrt_pos.mpr (legendrianChartRaw_radius_positive p)).ne')
    _ (by rw [legendrianChartRaw_zNormSq]; norm_num),legendrianNormalY_raw]

lemma legendrianNormalZ_chart (p : Jet3) : legendrianNormalZ (legendrianSphereChart p) = p 2 := by
  change legendrianNormalZ ((Real.sqrt (zNormSq (legendrianChartRaw p)+wNormSq (legendrianChartRaw p)))⁻¹ • legendrianChartRaw p) = _
  rw [legendrianNormalZ_smul _ (inv_ne_zero (Real.sqrt_pos.mpr (legendrianChartRaw_radius_positive p)).ne')
    _ (by rw [legendrianChartRaw_zNormSq]; norm_num),legendrianNormalZ_raw]

lemma legendrianSphereChart_zNormSq_positive (p : Jet3) : 0 < zNormSq (legendrianSphereChart p) := by
  change 0 < zNormSq ((Real.sqrt (zNormSq (legendrianChartRaw p)+wNormSq (legendrianChartRaw p)))⁻¹ • legendrianChartRaw p)
  rw [zNormSq_smul,legendrianChartRaw_zNormSq,mul_one]
  have hp : 0 < 1+wNormSq (legendrianChartRaw p) := by
    simpa only [legendrianChartRaw_zNormSq] using legendrianChartRaw_radius_positive p
  exact sq_pos_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr hp))

lemma legendrianNormalY_neg (y : Phase) : legendrianNormalY (-y) = legendrianNormalY y := by
  simp [legendrianNormalY,zNormSq]

lemma legendrianNormalZ_neg (y : Phase) : legendrianNormalZ (-y) = legendrianNormalZ y := by
  simp [legendrianNormalZ,zNormSq]

end
end ContactTopology

namespace ContactTopology
open BirkhoffGlobalSection BirkhoffGlobalSection.HopfTransport Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section
lemma legendrianSphereChart_eq_angles (p q : Jet3) (hpq : legendrianSphereChart p = legendrianSphereChart q) :
    Real.cos (2*Real.pi*p 0) = Real.cos (2*Real.pi*q 0) ∧
      Real.sin (2*Real.pi*p 0) = Real.sin (2*Real.pi*q 0) := by
  let a := (Real.sqrt (zNormSq (legendrianChartRaw p)+wNormSq (legendrianChartRaw p)))⁻¹
  let b := (Real.sqrt (zNormSq (legendrianChartRaw q)+wNormSq (legendrianChartRaw q)))⁻¹
  have ha : 0 < a := inv_pos.mpr (Real.sqrt_pos.mpr (legendrianChartRaw_radius_positive p))
  have hb : 0 < b := inv_pos.mpr (Real.sqrt_pos.mpr (legendrianChartRaw_radius_positive q))
  have hza : zNormSq (legendrianSphereChart p) = a^2 := by
    change zNormSq (a • legendrianChartRaw p) = _
    rw [zNormSq_smul,legendrianChartRaw_zNormSq,mul_one]
  have hzb : zNormSq (legendrianSphereChart q) = b^2 := by
    change zNormSq (b • legendrianChartRaw q) = _
    rw [zNormSq_smul,legendrianChartRaw_zNormSq,mul_one]
  have hab : a = b := by rw [hpq,hzb] at hza; nlinarith
  have h₀ := congrFun hpq 0
  have h₁ := congrFun hpq 1
  change a*Real.cos (2*Real.pi*p 0) = b*Real.cos (2*Real.pi*q 0) at h₀
  change a*Real.sin (2*Real.pi*p 0) = b*Real.sin (2*Real.pi*q 0) at h₁
  rw [← hab] at h₀ h₁
  exact ⟨mul_left_cancel₀ ha.ne' h₀,mul_left_cancel₀ ha.ne' h₁⟩

lemma legendrianSphereChart_fiber (p q : Jet3) :
    legendrianSphereChart p = legendrianSphereChart q ↔ ∃ n : ℤ, p = q+corePoint n := by
  constructor
  · intro heq
    have htrig := legendrianSphereChart_eq_angles p q heq
    have hcos : Real.cos (2*Real.pi*(p 0-q 0)) = 1 := by
      have harg : 2*Real.pi*(p 0-q 0) = 2*Real.pi*p 0-2*Real.pi*q 0 := by ring
      rw [harg,Real.cos_sub,htrig.1,htrig.2]
      nlinarith [Real.cos_sq_add_sin_sq (2*Real.pi*q 0)]
    obtain ⟨n,hn⟩ := (Real.cos_eq_one_iff _).mp hcos
    have hx : p 0 = q 0+n := by nlinarith [Real.pi_pos]
    have hy : p 1 = q 1 := by rw [← legendrianNormalY_chart p,← legendrianNormalY_chart q,heq]
    have hz : p 2 = q 2 := by rw [← legendrianNormalZ_chart p,← legendrianNormalZ_chart q,heq]
    refine ⟨n,?_⟩
    ext i
    fin_cases i
    · exact hx
    · simpa [corePoint] using hy
    · simpa [corePoint] using hz
  · rintro ⟨n,rfl⟩
    have hper : Periodic legendrianSphereChart (corePoint 1) := legendrianSphereChart_periodic
    have he : n • corePoint 1 = corePoint n := by
      ext i
      fin_cases i <;> simp [corePoint,zsmul_eq_mul]
    rw [← he]
    exact hper.zsmul n q

end
end ContactTopology

namespace ContactTopology.ConvexCore
open BirkhoffGlobalSection BirkhoffGlobalSection.HopfTransport Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

def vertical (y : Phase) : Phase := ![0,0,y 2,y 3]

def verticalLinear : Phase →L[ℝ] Phase :=
  LinearMap.toContinuousLinearMap
    { toFun := vertical
      map_add' := by intro u v; ext i; fin_cases i <;> simp [vertical]
      map_smul' := by intro r v; ext i; fin_cases i <;> simp [vertical] }

lemma vertical_contDiff : ContDiff ℝ ∞ vertical := verticalLinear.contDiff

lemma vertical_fderiv (y v : Phase) : fderiv ℝ vertical y v = vertical v :=
  congrArg (fun L : Phase →L[ℝ] Phase => L v) (verticalLinear.hasFDerivAt (x := y)).fderiv

def fiberEuler (y : Phase) : Phase := vertical y-wNormSq y • y

lemma fiberEuler_contDiff : ContDiff ℝ ∞ fiberEuler := by
  exact vertical_contDiff.sub ((((contDiff_apply ℝ ℝ 2).pow 2).add
    ((contDiff_apply ℝ ℝ 3).pow 2)).smul contDiff_id)

lemma wNormSq_hasFDerivAt (y : Phase) :
    HasFDerivAt wNormSq
      ((2*y 2) • (ContinuousLinearMap.proj (2:Fin 4) : Phase →L[ℝ] ℝ)+
        (2*y 3) • ContinuousLinearMap.proj 3) y := by
  convert! ((ContinuousLinearMap.proj (2:Fin 4) : Phase →L[ℝ] ℝ).hasFDerivAt.pow 2).add
    ((ContinuousLinearMap.proj (3:Fin 4) : Phase →L[ℝ] ℝ).hasFDerivAt.pow 2) using 1
  ext v
  simp

def fiberEulerDerivative (y v : Phase) : Phase :=
  vertical v-(2*(y 2*v 2+y 3*v 3)) • y-wNormSq y • v

lemma fiberEuler_fderiv (y v : Phase) :
    fderiv ℝ fiberEuler y v = fiberEulerDerivative y v := by
  have hd := (verticalLinear.hasFDerivAt (x := y)).sub ((wNormSq_hasFDerivAt y).smul (hasFDerivAt_id y))
  change HasFDerivAt fiberEuler _ y at hd
  rw [hd.fderiv]
  ext i
  simp [fiberEulerDerivative,verticalLinear]
  ring

lemma fiberEuler_odd (y : Phase) : fiberEuler (-y) = -fiberEuler y := by
  ext i
  fin_cases i <;> simp [fiberEuler,vertical,wNormSq,Matrix.vecHead,Matrix.vecTail] <;> ring

lemma fiberEuler_tangent (y : Phase) (hy : y ∈ unitThreeSphere) :
    phaseDot y (fiberEuler y) = 0 := by
  have hs := sphere_dot_self hy
  have he : phaseDot y (fiberEuler y) = wNormSq y-wNormSq y*phaseDot y y := by
    simp [fiberEuler,vertical,phaseDot,wNormSq]
    ring
  rw [he,hs]
  ring

lemma fiberEuler_contact_value (y : Phase) :
    phaseRadialContact y (fiberEuler y) = -(y 0*y 2+y 1*y 3)/2 := by
  simp [fiberEuler,vertical,phaseRadialContact,phaseSymplecticForm,Matrix.vecHead,Matrix.vecTail]
  ring

lemma fiberEuler_lie (y v : Phase) :
    phaseRadialContact (fiberEuler y) v+
      phaseRadialContact y (fderiv ℝ fiberEuler y v) =
      (1-2*wNormSq y)*phaseRadialContact y v := by
  rw [fiberEuler_fderiv]
  simp [fiberEuler,fiberEulerDerivative,vertical,phaseRadialContact,phaseSymplecticForm,Matrix.vecHead,Matrix.vecTail]
  ring

def normalEuler (p : Jet3) : Jet3 := ![0,p 1,p 2]

def normalRadiusSq (p : Jet3) : ℝ := p 1^2+p 2^2

lemma normalRadiusSq_hasFDerivAt (p : Jet3) :
    HasFDerivAt normalRadiusSq
      ((2*p 1) • (ContinuousLinearMap.proj (1:Fin 3) : Jet3 →L[ℝ] ℝ)+
        (2*p 2) • ContinuousLinearMap.proj 2) p := by
  convert! ((ContinuousLinearMap.proj (1:Fin 3) : Jet3 →L[ℝ] ℝ).hasFDerivAt.pow 2).add
    ((ContinuousLinearMap.proj (2:Fin 3) : Jet3 →L[ℝ] ℝ).hasFDerivAt.pow 2) using 1
  ext v
  simp

lemma normalEuler_transverse (r : ℝ) (hr : 0 < r) (p : Jet3)
    (hp : normalRadiusSq p=r^2) :
    0 < fderiv ℝ normalRadiusSq p (normalEuler p) := by
  rw [(normalRadiusSq_hasFDerivAt p).fderiv]
  have he : ((2*p 1) • (ContinuousLinearMap.proj 1 : Jet3 →L[ℝ] ℝ)+
      (2*p 2) • (ContinuousLinearMap.proj 2 : Jet3 →L[ℝ] ℝ)) (normalEuler p) = 2*normalRadiusSq p := by
    simp [normalEuler,normalRadiusSq]
    ring
  rw [he,hp]
  positivity

lemma jetEuler_dividing (p : Jet3) : jetContact p (normalEuler p)=p 2 := by
  simp [jetContact,normalEuler]

lemma jetEuler_two_divides (r : ℝ) (p : Jet3) :
    normalRadiusSq p=r^2 ∧ jetContact p (normalEuler p)=0 ↔
      (p 1=r ∧ p 2=0) ∨ (p 1= -r ∧ p 2=0) := by
  rw [jetEuler_dividing]
  constructor
  · rintro ⟨hs,hz⟩
    have hsquare : p 1^2=r^2 := by simpa [normalRadiusSq,hz] using hs
    have hh : p 1=r ∨ p 1= -r := (sq_eq_sq_iff_eq_or_eq_neg).mp hsquare
    exact hh.elim (fun h => Or.inl ⟨h,hz⟩) (fun h => Or.inr ⟨h,hz⟩)
  · rintro (⟨hy,hz⟩|⟨hy,hz⟩) <;> simp [normalRadiusSq,hy,hz]

end
end ContactTopology.ConvexCore

namespace ContactTopology.ConvexCore
open BirkhoffGlobalSection BirkhoffGlobalSection.HopfTransport Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

def radiusSqDerivative (y : Phase) : Phase →L[ℝ] ℝ :=
  (2*y 0) • (ContinuousLinearMap.proj 0 : Phase →L[ℝ] ℝ)+
    (2*y 1) • ContinuousLinearMap.proj 1+
    (2*y 2) • ContinuousLinearMap.proj 2+(2*y 3) • ContinuousLinearMap.proj 3

lemma radiusSqDerivative_apply (y v : Phase) :
    radiusSqDerivative y v=2*phaseDot y v := by
  simp [radiusSqDerivative,phaseDot]
  ring

lemma radiusSq_hasFDerivAt (y : Phase) :
    HasFDerivAt (fun q : Phase => zNormSq q+wNormSq q) (radiusSqDerivative y) y := by
  have h0 := (ContinuousLinearMap.proj (0:Fin 4) : Phase →L[ℝ] ℝ).hasFDerivAt (x := y) |>.pow 2
  have h1 := (ContinuousLinearMap.proj (1:Fin 4) : Phase →L[ℝ] ℝ).hasFDerivAt (x := y) |>.pow 2
  have h2 := (ContinuousLinearMap.proj (2:Fin 4) : Phase →L[ℝ] ℝ).hasFDerivAt (x := y) |>.pow 2
  have h3 := (ContinuousLinearMap.proj (3:Fin 4) : Phase →L[ℝ] ℝ).hasFDerivAt (x := y) |>.pow 2
  convert! (h0.add h1).add (h2.add h3) using 1
  ext v
  simp [radiusSqDerivative]
  ring

lemma radialNormalize_fderiv (y v : Phase) (hy : 0 < zNormSq y+wNormSq y) :
    fderiv ℝ radialNormalize y v =
      (Real.sqrt (zNormSq y+wNormSq y))⁻¹ • v-
        (phaseDot y v/((zNormSq y+wNormSq y)*Real.sqrt (zNormSq y+wNormSq y))) • y := by
  let Q := zNormSq y+wNormSq y
  let r := Real.sqrt Q
  have hr : 0 < r := Real.sqrt_pos.mpr hy
  have hrsq : r^2=Q := Real.sq_sqrt hy.le
  have hd := ((hasFDerivAt_inv hr.ne').comp y ((radiusSq_hasFDerivAt y).sqrt hy.ne')).smul (hasFDerivAt_id y)
  change HasFDerivAt radialNormalize _ y at hd
  rw [hd.fderiv]
  ext i
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,Pi.smul_apply,
    Pi.sub_apply,Pi.add_apply,smul_eq_mul,radiusSqDerivative_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.toSpanSingleton_apply,
    Function.comp_apply,id_eq]
  change _ = r⁻¹*v i-phaseDot y v/(Q*r)*y i
  have he : zNormSq y+wNormSq y=r^2 := hrsq.symm
  simp only [he,Real.sqrt_sq hr.le]
  rw [← hrsq]
  field_simp [hr.ne']
  <;> ring

lemma chartRaw_normalEuler (p : Jet3) :
    fderiv ℝ legendrianChartRaw p (normalEuler p) = vertical (legendrianChartRaw p) := by
  rw [legendrianChartRaw_fderiv]
  ext i
  fin_cases i <;> simp [legendrianChartRawDerivative,normalEuler,vertical,legendrianChartRaw] <;> ring

lemma chart_normalEuler (p : Jet3) :
    fderiv ℝ legendrianSphereChart p (normalEuler p) = fiberEuler (legendrianSphereChart p) := by
  let y := legendrianChartRaw p
  let Q := zNormSq y+wNormSq y
  let a := (Real.sqrt Q)⁻¹
  have hy : 0 < Q := legendrianChartRaw_radius_positive p
  have ha : 0 < a := inv_pos.mpr (Real.sqrt_pos.mpr hy)
  have hroot : (Real.sqrt Q)^2=Q := Real.sq_sqrt hy.le
  have hdot : phaseDot y (vertical y)=wNormSq y := by simp [phaseDot,vertical,wNormSq]; ring
  have hV : vertical (a • y) = a • vertical y := by
    ext i
    fin_cases i <;> simp [vertical]
  have hW : wNormSq (a • y) = a^2*wNormSq y := by simp [wNormSq]; ring
  change fderiv ℝ (radialNormalize ∘ legendrianChartRaw) p (normalEuler p) = _
  rw [fderiv_comp p ((radial_normalization_contact_identity y hy).1.differentiableAt (by simp))
      (legendrianChartRaw_contDiff.differentiable (by simp) p)]
  change fderiv ℝ radialNormalize y (fderiv ℝ legendrianChartRaw p (normalEuler p)) = _
  rw [chartRaw_normalEuler,radialNormalize_fderiv y (vertical y) hy,hdot]
  change a • vertical y-(wNormSq y/(Q*Real.sqrt Q)) • y = fiberEuler (a • y)
  rw [fiberEuler,hV,hW]
  ext i
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  dsimp [a]
  field_simp [(Real.sqrt_pos.mpr hy).ne',hy.ne']
  rw [hroot]
  ring

lemma chart_fiberEuler_dividing (p : Jet3) :
    phaseRadialContact (legendrianSphereChart p) (fiberEuler (legendrianSphereChart p)) =
      p 2*legendrianChartWeight p := by
  rw [← chart_normalEuler,legendrianSphereChart_contact,jetEuler_dividing]
  rfl

lemma chart_fiberEuler_dividing_iff (p : Jet3) :
    phaseRadialContact (legendrianSphereChart p) (fiberEuler (legendrianSphereChart p))=0 ↔ p 2=0 := by
  rw [chart_fiberEuler_dividing]
  exact mul_eq_zero_iff_right (inv_pos.mpr (legendrianChartRaw_radius_positive p)).ne'

end
end ContactTopology.ConvexCore

namespace ContactTopology.ConvexCore
open BirkhoffGlobalSection BirkhoffGlobalSection.HopfTransport Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

def imageChart (F : EquivariantSphereContactomorphism) : Jet3 → Phase :=
  F.toFun ∘ legendrianSphereChart

lemma imageChart_contDiff (F : EquivariantSphereContactomorphism) : ContDiff ℝ ∞ (imageChart F) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  exact (F.smooth _ (legendrianSphereChart_mem p)).comp p legendrianSphereChart_contDiff.contDiffAt

lemma imageChart_mem (F : EquivariantSphereContactomorphism) (p : Jet3) :
    imageChart F p ∈ unitThreeSphere := F.maps_sphere (legendrianSphereChart_mem p)

lemma imageChart_fiber (F : EquivariantSphereContactomorphism) (p q : Jet3) :
    imageChart F p=imageChart F q ↔ ∃ n : ℤ, p=q+corePoint n := by
  constructor
  · intro he
    have hh := congrArg F.invFun he
    change F.invFun (F.toFun (legendrianSphereChart p)) = F.invFun (F.toFun (legendrianSphereChart q)) at hh
    rw [F.left_inv _ (legendrianSphereChart_mem p),F.left_inv _ (legendrianSphereChart_mem q)] at hh
    exact (legendrianSphereChart_fiber p q).mp hh
  · intro h
    exact congrArg F.toFun ((legendrianSphereChart_fiber p q).mpr h)

lemma imageChart_derivative_injective (F : EquivariantSphereContactomorphism) (p : Jet3) :
    Injective (fderiv ℝ (imageChart F) p) := by
  have heq : F.invFun ∘ imageChart F = legendrianSphereChart :=
    funext (fun q => F.left_inv _ (legendrianSphereChart_mem q))
  have hd := congrArg (fun f : Jet3 → Phase => fderiv ℝ f p) heq
  rw [fderiv_comp p ((F.inv_smooth _ (imageChart_mem F p)).differentiableAt (by simp))
    ((imageChart_contDiff F).differentiable (by simp) p)] at hd
  intro v w hvw
  apply legendrianSphereChart_derivative_injective p
  rw [← hd]
  change fderiv ℝ F.invFun (imageChart F p) (fderiv ℝ (imageChart F) p v) =
    fderiv ℝ F.invFun (imageChart F p) (fderiv ℝ (imageChart F) p w)
  rw [hvw]

lemma imageChart_fderiv_tangent (F : EquivariantSphereContactomorphism) (p v : Jet3) :
    phaseDot (imageChart F p) (fderiv ℝ (imageChart F) p v)=0 := by
  let c : ℝ → Jet3 := fun s => p+s • v
  have hc : HasDerivAt c v 0 := by
    convert! (hasDerivAt_const (0:ℝ) p).add ((hasDerivAt_id (0:ℝ)).smul_const v) using 1 <;> simp [c]
  have hd := ((imageChart_contDiff F).differentiable (by simp) (c 0)).hasFDerivAt.comp_hasDerivAt 0 hc
  have hsq := dot_self_hasDerivAt hd
  have heq : (fun s => phaseDot (imageChart F (c s)) (imageChart F (c s)))=fun _ => (1:ℝ) := by
    funext s
    exact sphere_dot_self (imageChart_mem F _)
  change HasDerivAt (fun s => phaseDot (imageChart F (c s)) (imageChart F (c s))) _ 0 at hsq
  rw [heq] at hsq
  have hh := hsq.unique (hasDerivAt_const (0:ℝ) (1:ℝ))
  simp only [Function.comp_apply,c,zero_smul,add_zero] at hh
  linarith

def imageChartFactor (F : EquivariantSphereContactomorphism) (p : Jet3) : ℝ :=
  phaseRadialContact (imageChart F p) (fderiv ℝ (imageChart F) p (Pi.single 2 1))

lemma imageChartFactor_contDiff (F : EquivariantSphereContactomorphism) :
    ContDiff ℝ ∞ (imageChartFactor F) := by
  have hG := imageChart_contDiff F
  have hD : ContDiff ℝ ∞ (fun p => fderiv ℝ (imageChart F) p (Pi.single 2 1)) :=
    (hG.fderiv_right (by simp)).clm_apply contDiff_const
  unfold imageChartFactor phaseRadialContact phaseSymplecticForm
  fun_prop

lemma imageChart_contact_factor (F : EquivariantSphereContactomorphism) (p : Jet3) :
    0 < imageChartFactor F p ∧ ∀ v : Jet3,
      phaseRadialContact (imageChart F p) (fderiv ℝ (imageChart F) p v) =
        imageChartFactor F p*jetContact p v := by
  obtain ⟨a,ha,hF⟩ := F.contact _ (legendrianSphereChart_mem p)
  have hpull (v : Jet3) :
      phaseRadialContact (imageChart F p) (fderiv ℝ (imageChart F) p v) =
        (a*legendrianChartWeight p)*jetContact p v := by
    change phaseRadialContact (F.toFun (legendrianSphereChart p))
      (fderiv ℝ (F.toFun ∘ legendrianSphereChart) p v) = _
    rw [fderiv_comp p ((F.smooth _ (legendrianSphereChart_mem p)).differentiableAt (by simp))
      (legendrianSphereChart_contDiff.differentiable (by simp) p)]
    change phaseRadialContact (F.toFun (legendrianSphereChart p))
      (fderiv ℝ F.toFun (legendrianSphereChart p) (fderiv ℝ legendrianSphereChart p v)) = _
    rw [hF _ (legendrianSphereChart_fderiv_tangent p v),legendrianSphereChart_contact]
    simp only [legendrianChartWeight,div_eq_mul_inv]
    ring
  have he : imageChartFactor F p=a*legendrianChartWeight p := by
    simpa [imageChartFactor,jetContact] using hpull (Pi.single 2 1)
  rw [he]
  exact ⟨mul_pos ha (inv_pos.mpr (legendrianChartRaw_radius_positive p)),hpull⟩

def transportedEuler (F : EquivariantSphereContactomorphism) (y : Phase) : Phase :=
  fderiv ℝ F.toFun (F.invFun y) (fiberEuler (F.invFun y))

lemma transportedEuler_smooth (F : EquivariantSphereContactomorphism) (y : Phase)
    (hy : y ∈ unitThreeSphere) : ContDiffAt ℝ ∞ (transportedEuler F) y := by
  have hi := F.inv_smooth y hy
  have hd : ContDiffAt ℝ ∞ (fun z => fderiv ℝ F.toFun z) (F.invFun y) :=
    (F.smooth _ (F.inv_maps_sphere hy)).fderiv_right (by simp)
  exact (hd.comp y hi).clm_apply (fiberEuler_contDiff.contDiffAt.comp y hi)

lemma transportedEuler_chart (F : EquivariantSphereContactomorphism) (p : Jet3) :
    transportedEuler F (imageChart F p)=fderiv ℝ (imageChart F) p (normalEuler p) := by
  change fderiv ℝ F.toFun (F.invFun (F.toFun (legendrianSphereChart p)))
    (fiberEuler (F.invFun (F.toFun (legendrianSphereChart p)))) = _
  rw [F.left_inv _ (legendrianSphereChart_mem p)]
  change _ = fderiv ℝ (F.toFun ∘ legendrianSphereChart) p (normalEuler p)
  rw [fderiv_comp p ((F.smooth _ (legendrianSphereChart_mem p)).differentiableAt (by simp))
    (legendrianSphereChart_contDiff.differentiable (by simp) p)]
  change _ = fderiv ℝ F.toFun (legendrianSphereChart p) (fderiv ℝ legendrianSphereChart p (normalEuler p))
  rw [chart_normalEuler]

lemma transportedEuler_contact_value (F : EquivariantSphereContactomorphism) (p : Jet3) :
    phaseRadialContact (imageChart F p) (transportedEuler F (imageChart F p)) =
      imageChartFactor F p*p 2 := by
  rw [transportedEuler_chart,(imageChart_contact_factor F p).2,jetEuler_dividing]

def sphereNormalRadiusSq (y : Phase) : ℝ := legendrianNormalY y^2+legendrianNormalZ y^2

def imageNormalRadiusSq (F : EquivariantSphereContactomorphism) (y : Phase) : ℝ :=
  sphereNormalRadiusSq (F.invFun y)

lemma imageNormalRadiusSq_chart (F : EquivariantSphereContactomorphism) (p : Jet3) :
    imageNormalRadiusSq F (imageChart F p)=normalRadiusSq p := by
  unfold imageNormalRadiusSq imageChart
  rw [Function.comp_apply,F.left_inv _ (legendrianSphereChart_mem p)]
  simp [sphereNormalRadiusSq,normalRadiusSq,legendrianNormalY_chart,legendrianNormalZ_chart]

lemma imageNormalRadiusSq_smooth (F : EquivariantSphereContactomorphism) (p : Jet3) :
    ContDiffAt ℝ ∞ (imageNormalRadiusSq F) (imageChart F p) := by
  have hY := (legendrianNormalY_contDiffAt _ (legendrianSphereChart_zNormSq_positive p).ne').pow 2
  have hZ := (legendrianNormalZ_contDiffAt _ (legendrianSphereChart_zNormSq_positive p).ne').pow 2
  have hR : ContDiffAt ℝ ∞ sphereNormalRadiusSq (legendrianSphereChart p) := hY.add hZ
  have hi := F.inv_smooth _ (imageChart_mem F p)
  have hFi : F.invFun (imageChart F p)=legendrianSphereChart p := F.left_inv _ (legendrianSphereChart_mem p)
  exact (hFi ▸ hR).comp _ hi

lemma transportedEuler_transverse (F : EquivariantSphereContactomorphism)
    (r : ℝ) (hr : 0 < r) (p : Jet3) (hp : normalRadiusSq p=r^2) :
    0 < fderiv ℝ (imageNormalRadiusSq F) (imageChart F p)
      (transportedEuler F (imageChart F p)) := by
  have heq : imageNormalRadiusSq F ∘ imageChart F=normalRadiusSq := funext (imageNormalRadiusSq_chart F)
  have hd := congrArg (fun f : Jet3 → ℝ => fderiv ℝ f p) heq
  rw [fderiv_comp p ((imageNormalRadiusSq_smooth F p).differentiableAt (by simp))
    ((imageChart_contDiff F).differentiable (by simp) p)] at hd
  rw [transportedEuler_chart]
  change 0 < ((fderiv ℝ (imageNormalRadiusSq F) (imageChart F p)).comp (fderiv ℝ (imageChart F) p)) (normalEuler p)
  rw [hd]
  exact normalEuler_transverse r hr p hp

end
end ContactTopology.ConvexCore

namespace ContactTopology.ConvexCore
open BirkhoffGlobalSection BirkhoffGlobalSection.HopfTransport Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

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


lemma contact_hasDerivAt {q w : ℝ → Phase} {v b : Phase} {s : ℝ}
    (hq : HasDerivAt q v s) (hw : HasDerivAt w b s) :
    HasDerivAt (fun t => phaseRadialContact (q t) (w t))
      (phaseRadialContact v (w s)+phaseRadialContact (q s) b) s := by
  have h := fun i => hasDerivAt_pi.mp hq i
  have k := fun i => hasDerivAt_pi.mp hw i
  have hd := (((((h 0).mul (k 2)).sub ((h 2).mul (k 0))).add
    (((h 1).mul (k 3)).sub ((h 3).mul (k 1)))).neg).div_const 2
  have heq : (fun t => phaseRadialContact (q t) (w t))=
      (fun t => -(q t 0*w t 2-q t 2*w t 0+(q t 1*w t 3-q t 3*w t 1))/2) := by
    funext t
    simp only [phaseRadialContact,phaseSymplecticForm]
    ring
  change HasDerivAt (fun t => -(q t 0*w t 2-q t 2*w t 0+(q t 1*w t 3-q t 3*w t 1))/2) _ s at hd
  rw [← heq] at hd
  apply hd.congr_deriv
  simp only [phaseRadialContact,phaseSymplecticForm]
  ring

lemma transportedEuler_lie_in_chart (F : EquivariantSphereContactomorphism) (p v : Jet3) :
    phaseRadialContact (transportedEuler F (imageChart F p)) (fderiv ℝ (imageChart F) p v)+
      phaseRadialContact (imageChart F p)
        (fderiv ℝ (transportedEuler F) (imageChart F p) (fderiv ℝ (imageChart F) p v)) =
      (fderiv ℝ (imageChartFactor F) p (normalEuler p)+imageChartFactor F p)*jetContact p v := by
  let G := imageChart F
  let Y := transportedEuler F
  let L := imageChartFactor F
  let E := normalEuler p
  let w := fderiv ℝ G p v
  have hG := imageChart_contDiff F
  have hL := imageChartFactor_contDiff F
  let B : Jet3 → (Jet3 →L[ℝ] ℝ) := fun q =>
    (sphereRadialForm (G q)).comp (fderiv ℝ G q)
  have hBeq : B=fun q => L q • jetOneForm q := by
    funext q
    ext z
    simpa only [B,L,G,ContinuousLinearMap.comp_apply,ContinuousLinearMap.smul_apply,
      sphereRadialForm_apply,jetOneForm_apply,smul_eq_mul] using (imageChart_contact_factor F q).2 z
  have hdB := congrArg (fun A : Jet3 → (Jet3 →L[ℝ] ℝ) => fderiv ℝ A p) hBeq
  have hp := ContactCalculus.exterior_pairing_pullback sphereRadialForm G p E v
    (sphereRadialForm_contDiff.differentiable (by simp) _)
    (hG.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  change fderiv ℝ B p E v-fderiv ℝ B p v E = _ at hp
  rw [hdB,weighted_jetOneForm_fderiv L p E v (hL.differentiable (by simp) p),
    weighted_jetOneForm_fderiv L p v E (hL.differentiable (by simp) p),
    sphereRadialForm_fderiv,sphereRadialForm_fderiv] at hp
  have hrel : fderiv ℝ G p E=Y (G p) := (transportedEuler_chart F p).symm
  rw [hrel] at hp
  have hskew : phaseRadialContact w (Y (G p)) = -phaseRadialContact (Y (G p)) w := by
    simp [phaseRadialContact,phaseSymplecticForm]
    ring
  change fderiv ℝ L p E*jetContact p v-L p*(E 1)*v 0-
    (fderiv ℝ L p v*jetContact p E-L p*v 1*(E 0)) =
      phaseRadialContact (Y (G p)) w-phaseRadialContact w (Y (G p)) at hp
  rw [hskew] at hp
  have hscalar : -phaseRadialContact (Y (G p)) w+
      phaseRadialContact (G p) (fderiv ℝ Y (G p) w) =
      fderiv ℝ L p v*p 2+L p*v 2 := by
    let c : ℝ → Jet3 := fun s => p+s • v
    have hc : HasDerivAt c v 0 := by
      convert! (hasDerivAt_const (0:ℝ) p).add ((hasDerivAt_id (0:ℝ)).smul_const v) using 1 <;> simp [c]
    have hGc : HasDerivAt (fun s => G (c s)) w 0 := by
      convert! (hG.differentiable (by simp) (c 0)).hasFDerivAt.comp_hasDerivAt 0 hc using 1 <;> simp [c,w,G]
    have hY0 : DifferentiableAt ℝ Y (G (c 0)) := by
      simpa [c,G,Y] using (transportedEuler_smooth F (imageChart F p) (imageChart_mem F p)).differentiableAt (by simp)
    have hYc := hY0.hasFDerivAt.comp_hasDerivAt 0 hGc
    have hh := contact_hasDerivAt hGc hYc
    have heq : (fun s => phaseRadialContact (G (c s)) (Y (G (c s))))=
        fun s => L (c s)*(c s) 2 := funext (fun s => transportedEuler_contact_value F (c s))
    change HasDerivAt (fun s => phaseRadialContact (G (c s)) (Y (G (c s)))) _ 0 at hh
    rw [heq] at hh
    have hLc := (hL.differentiable (by simp) (c 0)).hasFDerivAt.comp_hasDerivAt 0 hc
    have hcoord := (ContinuousLinearMap.proj (2:Fin 3) : Jet3 →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt 0 hc
    have he := hh.unique (hLc.mul hcoord)
    simp only [c,zero_smul,add_zero,Function.comp_apply] at he
    change phaseRadialContact w (Y (G p))+
      phaseRadialContact (G p) (fderiv ℝ Y (G p) w) =
      fderiv ℝ L p v*p 2+L p*v 2 at he
    rwa [hskew] at he
  change phaseRadialContact (Y (G p)) w+
    phaseRadialContact (G p) (fderiv ℝ Y (G p) w) =
      (fderiv ℝ L p E+L p)*jetContact p v
  dsimp [E,normalEuler,jetContact] at hp ⊢
  linear_combination -hp+hscalar

end
end ContactTopology.ConvexCore

namespace ContactTopology.ConvexCore
open BirkhoffGlobalSection BirkhoffGlobalSection.HopfTransport Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

def coreTorus (F : EquivariantSphereContactomorphism) (r : ℝ) : Set Phase :=
  imageChart F '' {p | normalRadiusSq p=r^2}

def dividingSet (F : EquivariantSphereContactomorphism) (r : ℝ) : Set Phase :=
  {y ∈ coreTorus F r | phaseRadialContact y (transportedEuler F y)=0}

def dividingCurve (F : EquivariantSphereContactomorphism) (r x : ℝ) : Phase :=
  imageChart F ![x,r,0]

lemma dividingCurve_contDiff (F : EquivariantSphereContactomorphism) (r : ℝ) :
    ContDiff ℝ ∞ (dividingCurve F r) := by
  have hparam : ContDiff ℝ ∞ (fun x : ℝ => (![x,r,0] : Jet3)) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> simp <;> fun_prop
  exact (imageChart_contDiff F).comp hparam

lemma dividingCurve_fiber (F : EquivariantSphereContactomorphism) (r s x y : ℝ) :
    dividingCurve F r x=dividingCurve F s y ↔ r=s ∧ ∃ n : ℤ, x=y+n := by
  rw [dividingCurve,dividingCurve,imageChart_fiber]
  constructor
  · rintro ⟨n,hn⟩
    have h0 := congrFun hn 0
    have h1 := congrFun hn 1
    exact ⟨by simpa [corePoint] using h1,⟨n,by simpa [corePoint] using h0⟩⟩
  · rintro ⟨rfl,n,hn⟩
    refine ⟨n,?_⟩
    ext i
    fin_cases i <;> simpa [corePoint] using hn

lemma dividingCurve_periodic (F : EquivariantSphereContactomorphism) (r : ℝ) :
    Periodic (dividingCurve F r) 1 := by
  intro x
  exact (dividingCurve_fiber F r r (x+1) x).mpr ⟨rfl,⟨1,by norm_num⟩⟩

lemma dividingCurve_antipodal (F : EquivariantSphereContactomorphism) (r x : ℝ) :
    dividingCurve F r (x+1/2)= -dividingCurve F r x := by
  have he : (![x+1/2,r,0] : Jet3)=![x,r,0]+corePoint (1/2) := by
    ext i
    fin_cases i <;> simp [corePoint]
  change F.toFun (legendrianSphereChart ![x+1/2,r,0]) = -F.toFun (legendrianSphereChart ![x,r,0])
  rw [he,legendrianSphereChart_antipodal,F.antipodal _ (legendrianSphereChart_mem _)]

lemma dividingCurve_hasDerivAt (F : EquivariantSphereContactomorphism) (r x : ℝ) :
    HasDerivAt (dividingCurve F r)
      (fderiv ℝ (imageChart F) ![x,r,0] (Pi.single 0 1)) x := by
  have hp : HasDerivAt (fun s : ℝ => (![s,r,0] : Jet3)) (Pi.single 0 1) x := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · convert! hasDerivAt_id x using 1
    · convert! hasDerivAt_const x r using 1
    · convert! hasDerivAt_const x (0:ℝ) using 1
  exact ((imageChart_contDiff F).differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt x hp

lemma dividingCurve_regular (F : EquivariantSphereContactomorphism) (r x : ℝ) :
    deriv (dividingCurve F r) x ≠ 0 := by
  rw [(dividingCurve_hasDerivAt F r x).deriv]
  intro hz
  have hh := (imageChart_derivative_injective F ![x,r,0])
    (show fderiv ℝ (imageChart F) ![x,r,0] (Pi.single 0 1)=fderiv ℝ (imageChart F) ![x,r,0] 0 by simpa using hz)
  have h0 := congrFun hh 0
  norm_num at h0

lemma dividingCurve_range_compact (F : EquivariantSphereContactomorphism) (r : ℝ) :
    IsCompact (range (dividingCurve F r)) := by
  have he : range (dividingCurve F r)=(dividingCurve F r) '' Icc (0:ℝ) 1 := by
    apply Subset.antisymm
    · rintro y ⟨x,rfl⟩
      refine ⟨Int.fract x,⟨Int.fract_nonneg _,(Int.fract_lt_one _).le⟩,?_⟩
      exact (dividingCurve_fiber F r r (Int.fract x) x).mpr ⟨rfl,⟨-⌊x⌋,by change x-(⌊x⌋:ℝ)=x+((-⌊x⌋:ℤ):ℝ); rw [Int.cast_neg]; ring⟩⟩
    · exact image_subset_range _ _
  rw [he]
  exact isCompact_Icc.image (dividingCurve_contDiff F r).continuous

lemma dividingCurve_range_connected (F : EquivariantSphereContactomorphism) (r : ℝ) :
    IsConnected (range (dividingCurve F r)) :=
  isConnected_range (dividingCurve_contDiff F r).continuous

lemma dividingSet_two_curves (F : EquivariantSphereContactomorphism) (r : ℝ) :
    dividingSet F r=range (dividingCurve F r) ∪ range (dividingCurve F (-r)) := by
  ext y
  constructor
  · rintro ⟨⟨p,hp,rfl⟩,hd⟩
    rw [transportedEuler_contact_value] at hd
    have hz : p 2=0 := (mul_eq_zero.mp hd).resolve_left (imageChart_contact_factor F p).1.ne'
    have hh := (jetEuler_two_divides r p).mp ⟨hp,by simpa [jetEuler_dividing] using hz⟩
    rcases hh with ⟨hy,hz⟩|⟨hy,hz⟩
    · left
      refine ⟨p 0,?_⟩
      change imageChart F ![p 0,r,0]=imageChart F p
      apply congrArg (imageChart F)
      ext i
      fin_cases i
      · rfl
      · exact hy.symm
      · exact hz.symm
    · right
      refine ⟨p 0,?_⟩
      change imageChart F ![p 0,-r,0]=imageChart F p
      apply congrArg (imageChart F)
      ext i
      fin_cases i
      · rfl
      · exact hy.symm
      · exact hz.symm
  · rintro (⟨x,rfl⟩|⟨x,rfl⟩)
    · refine ⟨⟨![x,r,0],by simp [normalRadiusSq],rfl⟩,?_⟩
      rw [dividingCurve,transportedEuler_contact_value]
      simp
    · refine ⟨⟨![x,-r,0],by simp [normalRadiusSq],rfl⟩,?_⟩
      rw [dividingCurve,transportedEuler_contact_value]
      simp

lemma dividingSet_curves_disjoint (F : EquivariantSphereContactomorphism) (r : ℝ) (hr : 0 < r) :
    Disjoint (range (dividingCurve F r)) (range (dividingCurve F (-r))) := by
  apply disjoint_left.mpr
  rintro y ⟨x,rfl⟩ ⟨s,hs⟩
  have hh := ((dividingCurve_fiber F r (-r) x s).mp hs.symm).1
  linarith

lemma coreTorus_transverse (F : EquivariantSphereContactomorphism) (r : ℝ) (hr : 0 < r)
    (y : Phase) (hy : y ∈ coreTorus F r) :
    ContDiffAt ℝ ∞ (imageNormalRadiusSq F) y ∧
      0 < fderiv ℝ (imageNormalRadiusSq F) y (transportedEuler F y) := by
  obtain ⟨p,hp,rfl⟩ := hy
  exact ⟨imageNormalRadiusSq_smooth F p,transportedEuler_transverse F r hr p hp⟩

end
end ContactTopology.ConvexCore

namespace ContactTopology.ConvexCore
open BirkhoffGlobalSection BirkhoffGlobalSection.HopfTransport Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma imageChart_tangent_surjective (F : EquivariantSphereContactomorphism) (p : Jet3)
    (w : Phase) (hw : phaseDot (imageChart F p) w=0) :
    ∃ v : Jet3, fderiv ℝ (imageChart F) p v=w := by
  let y := imageChart F p
  let D : Phase →ₗ[ℝ] ℝ := (radiusSqDerivative y).toLinearMap
  let A : Jet3 →ₗ[ℝ] Phase := (fderiv ℝ (imageChart F) p).toLinearMap
  have hDy : D y=2 := by
    change radiusSqDerivative y y=2
    rw [radiusSqDerivative_apply,sphere_dot_self (imageChart_mem F p)]
    ring
  have hDsurj : Surjective D := by
    intro s
    refine ⟨(s/2) • y,?_⟩
    rw [map_smul,hDy]
    simp
  have hDrange : Module.finrank ℝ (LinearMap.range D)=1 := by
    rw [LinearMap.range_eq_top.mpr hDsurj,finrank_top]
    simp
  have hDker : Module.finrank ℝ (LinearMap.ker D)=3 := by
    have hh := D.finrank_range_add_finrank_ker
    have hphase : Module.finrank ℝ Phase=4 := by simp [Phase]
    rw [hDrange,hphase] at hh
    exact Nat.add_left_cancel hh
  have hArange : Module.finrank ℝ (LinearMap.range A)=3 := by
    rw [LinearMap.finrank_range_of_inj (imageChart_derivative_injective F p)]
    simp [Jet3]
  have hle : LinearMap.range A ≤ LinearMap.ker D := by
    rintro z ⟨v,rfl⟩
    change radiusSqDerivative y (fderiv ℝ (imageChart F) p v)=0
    rw [radiusSqDerivative_apply,imageChart_fderiv_tangent]
    ring
  have heq : LinearMap.range A=LinearMap.ker D :=
    Submodule.eq_of_le_of_finrank_eq hle (hArange.trans hDker.symm)
  have hmem : w ∈ LinearMap.ker D := by
    change radiusSqDerivative y w=0
    rw [radiusSqDerivative_apply,hw]
    ring
  rw [← heq] at hmem
  exact hmem

lemma transportedEuler_tangent (F : EquivariantSphereContactomorphism) (p : Jet3) :
    phaseDot (imageChart F p) (transportedEuler F (imageChart F p))=0 := by
  rw [transportedEuler_chart]
  exact imageChart_fderiv_tangent F p _

lemma transportedEuler_is_contact (F : EquivariantSphereContactomorphism) (p : Jet3) :
    ∃ a : ℝ, ∀ w : Phase, phaseDot (imageChart F p) w=0 →
      phaseRadialContact (transportedEuler F (imageChart F p)) w+
        phaseRadialContact (imageChart F p) (fderiv ℝ (transportedEuler F) (imageChart F p) w) =
        a*phaseRadialContact (imageChart F p) w := by
  let L := imageChartFactor F
  refine ⟨(fderiv ℝ L p (normalEuler p)+L p)/L p,?_⟩
  intro w hw
  obtain ⟨v,rfl⟩ := imageChart_tangent_surjective F p w hw
  rw [transportedEuler_lie_in_chart,(imageChart_contact_factor F p).2]
  change _ = ((fderiv ℝ L p (normalEuler p)+L p)/L p)*(L p*jetContact p v)
  have hLne : L p ≠ 0 := (imageChart_contact_factor F p).1.ne'
  change (fderiv ℝ L p (normalEuler p)+L p)*jetContact p v = _
  field_simp [hLne]
  <;> ring

lemma imageChart_sphere_open (F : EquivariantSphereContactomorphism) (p : Jet3) :
    ∃ U : Set Phase, IsOpen U ∧ imageChart F p ∈ U ∧ U ∩ unitThreeSphere ⊆ range (imageChart F) := by
  obtain ⟨c,V,hV,hVp,hc,hcp,hl,hr⟩ := legendrianSphereChart_open_inverse p
  let U : Set Phase := interior (F.invFun ⁻¹' V)
  have hFy : F.invFun (imageChart F p)=legendrianSphereChart p := F.left_inv _ (legendrianSphereChart_mem p)
  have hUn : F.invFun ⁻¹' V ∈ 𝓝 (imageChart F p) :=
    (F.inv_smooth _ (imageChart_mem F p)).continuousAt.preimage_mem_nhds
      (by rw [hFy]; exact hV.mem_nhds hVp)
  refine ⟨U,isOpen_interior,mem_interior_iff_mem_nhds.mpr hUn,?_⟩
  intro y hy
  have hVinv : F.invFun y ∈ V := (show U ⊆ F.invFun ⁻¹' V from interior_subset) hy.1
  refine ⟨c (F.invFun y),?_⟩
  change F.toFun (legendrianSphereChart (c (F.invFun y)))=y
  rw [hr _ hVinv (F.inv_maps_sphere hy.2),F.right_inv y hy.2]

end
end ContactTopology.ConvexCore

namespace ContactTopology.ConvexCore
open BirkhoffGlobalSection BirkhoffGlobalSection.HopfTransport Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma unitCircle_compact : IsCompact unitCircle := by
  have hp : Continuous planeNormSq := by unfold planeNormSq; fun_prop
  have hc : IsClosed unitCircle := isClosed_eq hp continuous_const
  apply (isCompact_closedBall (0 : Plane) 1).of_isClosed_subset hc
  intro u hu
  have he : u 0^2+u 1^2=1 := hu
  have h0 : |u 0| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (u 0),sq_nonneg (u 1)]
  have h1 : |u 1| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (u 0),sq_nonneg (u 1)]
  have hi : ∀ i : Fin 2, ‖u i‖ ≤ 1 := by intro i; fin_cases i <;> assumption
  have hn : ‖u‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).mpr hi
  simpa [Metric.mem_closedBall,dist_zero_right] using hn

def torusParameter (F : EquivariantSphereContactomorphism) (r : ℝ) (q : ℝ × Plane) : Phase :=
  imageChart F ![q.1,r*q.2 0,r*q.2 1]

lemma torusParameter_contDiff (F : EquivariantSphereContactomorphism) (r : ℝ) :
    ContDiff ℝ ∞ (torusParameter F r) := by
  apply (imageChart_contDiff F).comp
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> simp <;> fun_prop

lemma coreTorus_parameter_image (F : EquivariantSphereContactomorphism) (r : ℝ) (hr : 0 < r) :
    coreTorus F r=torusParameter F r '' (Icc (0:ℝ) 1 ×ˢ unitCircle) := by
  ext y
  constructor
  · rintro ⟨p,hp,rfl⟩
    let u : Plane := ![p 1/r,p 2/r]
    have hu : u ∈ unitCircle := by
      change (p 1/r)^2+(p 2/r)^2=1
      have hn : p 1^2+p 2^2=r^2 := hp
      field_simp [hr.ne']
      exact hn
    refine ⟨(Int.fract (p 0),u),⟨⟨Int.fract_nonneg _,(Int.fract_lt_one _).le⟩,hu⟩,?_⟩
    change imageChart F ![Int.fract (p 0),r*(p 1/r),r*(p 2/r)]=imageChart F p
    apply (imageChart_fiber F _ _).mpr
    refine ⟨-⌊p 0⌋,?_⟩
    ext i
    fin_cases i
    · change Int.fract (p 0)=p 0+((-⌊p 0⌋:ℤ):ℝ)
      rw [Int.cast_neg]
      rfl
    · change r*(p 1/r)=p 1+0
      field_simp
      <;> ring
    · change r*(p 2/r)=p 2+0
      field_simp
      <;> ring
  · rintro ⟨⟨x,u⟩,⟨hx,hu⟩,rfl⟩
    refine ⟨![x,r*u 0,r*u 1],?_,rfl⟩
    have he : u 0^2+u 1^2=1 := hu
    change (r*u 0)^2+(r*u 1)^2=r^2
    linear_combination r^2*he

lemma coreTorus_compact (F : EquivariantSphereContactomorphism) (r : ℝ) (hr : 0 < r) :
    IsCompact (coreTorus F r) := by
  rw [coreTorus_parameter_image F r hr]
  exact (isCompact_Icc.prod unitCircle_compact).image (torusParameter_contDiff F r).continuous

lemma imageCore_Legendrian (F : EquivariantSphereContactomorphism) (x : ℝ) :
    dividingCurve F 0 x=F.toFun ![Real.cos (2*Real.pi*x),Real.sin (2*Real.pi*x),0,0] ∧
      phaseRadialContact (dividingCurve F 0 x) (deriv (dividingCurve F 0) x)=0 ∧
      deriv (dividingCurve F 0) x ≠ 0 := by
  refine ⟨?_,?_,dividingCurve_regular F 0 x⟩
  · change F.toFun (legendrianSphereChart (corePoint x))=_
    rw [legendrianSphereChart_core]
  · rw [(dividingCurve_hasDerivAt F 0 x).deriv]
    change phaseRadialContact (imageChart F ![x,0,0])
      (fderiv ℝ (imageChart F) ![x,0,0] (Pi.single 0 1))=0
    rw [(imageChart_contact_factor F _).2]
    simp [jetContact]

lemma convex_boundary_open_data (F : EquivariantSphereContactomorphism) (r : ℝ) (hr : 0 < r) :
    ∃ O : Set Phase, IsOpen O ∧ coreTorus F r ⊆ O ∧
      (O ∩ unitThreeSphere) ∩ {y | imageNormalRadiusSq F y=r^2}=coreTorus F r ∧
      (∀ y ∈ O ∩ unitThreeSphere, ContDiffAt ℝ ∞ (transportedEuler F) y ∧
        phaseDot y (transportedEuler F y)=0 ∧ ∃ a : ℝ, ∀ w : Phase, phaseDot y w=0 →
          phaseRadialContact (transportedEuler F y) w+
            phaseRadialContact y (fderiv ℝ (transportedEuler F) y w)=a*phaseRadialContact y w) ∧
      ∀ y ∈ coreTorus F r, ContDiffAt ℝ ∞ (imageNormalRadiusSq F) y ∧
        0 < fderiv ℝ (imageNormalRadiusSq F) y (transportedEuler F y) := by
  choose U hU hpoint hsub using imageChart_sphere_open F
  let O : Set Phase := ⋃ p : Jet3, U p
  have hO : IsOpen O := isOpen_iUnion hU
  have hGO : range (imageChart F) ⊆ O := by
    rintro y ⟨p,rfl⟩
    exact mem_iUnion.mpr ⟨p,hpoint p⟩
  have hOG : O ∩ unitThreeSphere ⊆ range (imageChart F) := by
    intro y hy
    obtain ⟨p,hp⟩ := mem_iUnion.mp hy.1
    exact hsub p ⟨hp,hy.2⟩
  have hTO : coreTorus F r ⊆ O := by
    rintro y ⟨p,hp,rfl⟩
    exact hGO ⟨p,rfl⟩
  refine ⟨O,hO,hTO,?_,?_,fun y hy => coreTorus_transverse F r hr y hy⟩
  · ext y
    constructor
    · rintro ⟨hy,hradius⟩
      obtain ⟨p,rfl⟩ := hOG hy
      refine ⟨p,?_,rfl⟩
      change imageNormalRadiusSq F (imageChart F p)=r^2 at hradius
      rwa [imageNormalRadiusSq_chart] at hradius
    · intro hy
      obtain ⟨p,hp,rfl⟩ := hy
      exact ⟨⟨hTO ⟨p,hp,rfl⟩,imageChart_mem F p⟩,by change imageNormalRadiusSq F (imageChart F p)=r^2; rw [imageNormalRadiusSq_chart]; exact hp⟩
  · intro y hy
    obtain ⟨p,rfl⟩ := hOG hy
    exact ⟨transportedEuler_smooth F _ (imageChart_mem F p),transportedEuler_tangent F p,
      transportedEuler_is_contact F p⟩

end
end ContactTopology.ConvexCore

namespace ContactTopology.MeridianTorus
open BirkhoffGlobalSection BirkhoffGlobalSection.HopfTransport ContactTopology.ConvexCore Set Function
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma raw_smooth (r k : ℝ) : ContDiff ℝ ∞ (raw r k) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [raw,dot2,cross2] <;> fun_prop
lemma raw_positive (r k : ℝ) (p : Plane × Plane) (hp : p.1 ∈ unitCircle) :
    0 < zNormSq (raw r k p)+wNormSq (raw r k p) := by
  change planeNormSq p.1=1 at hp
  have hq : zNormSq (raw r k p)=1 := hp
  rw [hq]
  unfold wNormSq
  positivity

lemma surface_smooth (r k : ℝ) (p : Plane × Plane) (hp : p.1 ∈ unitCircle) :
    ContDiffAt ℝ ∞ (surface r k) p :=
  ((radial_normalization_contact_identity _ (raw_positive r k p hp)).1).comp p (raw_smooth r k).contDiffAt
lemma surface_sphere (r k : ℝ) (p : Plane × Plane) (hp : p.1 ∈ unitCircle) :
    surface r k p ∈ unitThreeSphere :=
  (radial_normalization_contact_identity _ (raw_positive r k p hp)).2.1

lemma raw_meridian_derivative (r k : ℝ) (p : Plane × Plane) :
    fderiv ℝ (raw r k) p (circleTangent p.1,0)=
      ![-p.1 1,p.1 0,
        r*(-p.1 1*dot2 p.1 p.2+p.1 0*cross2 p.1 p.2-
          k*p.1 0*cross2 p.1 p.2+k*p.1 1*dot2 p.1 p.2),
        r*(p.1 0*dot2 p.1 p.2+p.1 1*cross2 p.1 p.2-
          k*p.1 1*cross2 p.1 p.2-k*p.1 0*dot2 p.1 p.2)] := by
  let c : ℝ → Plane × Plane := fun t => (p.1+t • circleTangent p.1,p.2)
  have hc : HasDerivAt c (circleTangent p.1,0) 0 := by
    convert! ((hasDerivAt_const (0:ℝ) p.1).add
      ((hasDerivAt_id (0:ℝ)).smul_const (circleTangent p.1))).prodMk
      (hasDerivAt_const (0:ℝ) p.2) using 1 <;> simp [c]
  have hd := ((raw_smooth r k).differentiable (by simp) (c 0)).hasFDerivAt.comp_hasDerivAt 0
    (show HasDerivAt c (circleTangent p.1,0) 0 from hc)
  have hd' : HasDerivAt (raw r k ∘ c) (fderiv ℝ (raw r k) p (circleTangent p.1,0)) 0 := by
    simpa [c] using hd
  have h0 (i : Fin 2) : HasDerivAt (fun t : ℝ => (c t).1 i) (circleTangent p.1 i) 0 := by
    convert! (hasDerivAt_const (0:ℝ) (p.1 i)).add
      ((hasDerivAt_id (0:ℝ)).mul_const (circleTangent p.1 i)) using 1 <;> simp [c]
  have h1 (i : Fin 2) : HasDerivAt (fun t : ℝ => (c t).2 i) 0 0 := by
    simpa [c] using hasDerivAt_const (0:ℝ) (p.2 i)
  have hdot := ((h0 0).mul (h1 0)).add ((h0 1).mul (h1 1))
  have hcross := ((h0 0).mul (h1 1)).sub ((h0 1).mul (h1 0))
  ext i
  fin_cases i
  · exact (hasDerivAt_pi.mp hd' 0).unique (h0 0)
  · exact (hasDerivAt_pi.mp hd' 1).unique (h0 1)
  · have hh := (((h0 0).mul hdot).sub (((h0 1).mul hcross).const_mul k)).const_mul r
    change HasDerivAt (fun t => raw r k (c t) 2) _ 0 at hh
    have he := (hasDerivAt_pi.mp hd' 2).unique hh
    dsimp [c,circleTangent,dot2,cross2] at he ⊢
    linear_combination he
  · have hh := (((h0 1).mul hdot).add (((h0 0).mul hcross).const_mul k)).const_mul r
    change HasDerivAt (fun t => raw r k (c t) 3) _ 0 at hh
    have he := (hasDerivAt_pi.mp hd' 3).unique hh
    dsimp [c,circleTangent,dot2,cross2] at he ⊢
    linear_combination he

lemma raw_meridian_contact (r k : ℝ) (p : Plane × Plane) :
    phaseRadialContact (raw r k p) (fderiv ℝ (raw r k) p (circleTangent p.1,0))=
      r*(2*k-1)*planeNormSq p.1*cross2 p.1 p.2/2 := by
  rw [raw_meridian_derivative]
  simp [raw,dot2,cross2,planeNormSq,phaseRadialContact,phaseSymplecticForm]
  ring
lemma surface_meridian_legendrian (r : ℝ) (p : Plane × Plane) (hp : p.1 ∈ unitCircle) :
    phaseRadialContact (surface r (1/2) p)
      (fderiv ℝ (surface r (1/2)) p (circleTangent p.1,0))=0 := by
  rw [surface,fderiv_comp p
    ((radial_normalization_contact_identity _ (raw_positive r (1/2) p hp)).1.differentiableAt (by simp))
    ((raw_smooth r (1/2)).differentiable (by simp) p)]
  change phaseRadialContact (radialNormalize (raw r (1/2) p))
    (fderiv ℝ radialNormalize (raw r (1/2) p) (fderiv ℝ (raw r (1/2)) p _))=0
  rw [(radial_normalization_contact_identity _ (raw_positive r (1/2) p hp)).2.2.2,
    raw_meridian_contact]
  norm_num

end
end ContactTopology.MeridianTorus


namespace ContactTopology.MeridianTorus
open BirkhoffGlobalSection BirkhoffGlobalSection.HopfTransport ContactTopology.ConvexCore Set Function
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
noncomputable section

def qDotP (y : Phase) : ℝ := y 0*y 2+y 1*y 3
def qCrossP (y : Phase) : ℝ := y 0*y 3-y 1*y 2
def level (r : ℝ) (y : Phase) : ℝ := qDotP y^2+4*qCrossP y^2-r^2*(zNormSq y)^2
lemma level_smooth (r : ℝ) : ContDiff ℝ ∞ (level r) := by
  unfold level qDotP qCrossP zNormSq
  fun_prop
lemma level_smul (r a : ℝ) (y : Phase) : level r (a • y)=a^4*level r y := by
  simp [level,qDotP,qCrossP,zNormSq]
  ring
lemma dot_cross_identity (u v : Plane) :
    dot2 u v^2+cross2 u v^2=planeNormSq u*planeNormSq v := by
  simp [dot2,cross2,planeNormSq]
  ring
lemma raw_level (r : ℝ) (p : Plane × Plane) (hu : p.1 ∈ unitCircle) (hv : p.2 ∈ unitCircle) :
    level r (raw r (1/2) p)=0 := by
  have hdot : qDotP (raw r (1/2) p)=r*planeNormSq p.1*dot2 p.1 p.2 := by
    simp [qDotP,raw,planeNormSq,dot2,cross2]
    ring
  have hcross : qCrossP (raw r (1/2) p)=r/2*planeNormSq p.1*cross2 p.1 p.2 := by
    simp [qCrossP,raw,planeNormSq,dot2,cross2]
    ring
  have hq : zNormSq (raw r (1/2) p)=planeNormSq p.1 := rfl
  change planeNormSq p.1=1 at hu
  change planeNormSq p.2=1 at hv
  unfold level
  rw [hdot,hcross,hq,hu]
  have hi := dot_cross_identity p.1 p.2
  rw [hu,hv] at hi
  nlinarith [sq_nonneg r]
lemma surface_level (r : ℝ) (p : Plane × Plane) (hu : p.1 ∈ unitCircle) (hv : p.2 ∈ unitCircle) :
    level r (surface r (1/2) p)=0 := by
  change level r (radialNormalize (raw r (1/2) p))=0
  rw [radialNormalize,level_smul,raw_level r p hu hv,mul_zero]
lemma level_fderiv (r : ℝ) (y v : Phase) :
    fderiv ℝ (level r) y v=
      2*qDotP y*(v 0*y 2+y 0*v 2+v 1*y 3+y 1*v 3)+
      8*qCrossP y*(v 0*y 3+y 0*v 3-v 1*y 2-y 1*v 2)-
      2*r^2*zNormSq y*(2*y 0*v 0+2*y 1*v 1) := by
  let c : ℝ → Phase := fun t => y+t • v
  have hc : HasDerivAt c v 0 := by
    convert! (hasDerivAt_const (0:ℝ) y).add ((hasDerivAt_id (0:ℝ)).smul_const v) using 1 <;> simp [c]
  have h (i : Fin 4) : HasDerivAt (fun t => c t i) (v i) 0 := hasDerivAt_pi.mp hc i
  have hdot := ((h 0).mul (h 2)).add ((h 1).mul (h 3))
  have hcross := ((h 0).mul (h 3)).sub ((h 1).mul (h 2))
  have hq := ((h 0).pow 2).add ((h 1).pow 2)
  have hd := ((hdot.pow 2).add ((hcross.pow 2).const_mul 4)).sub ((hq.pow 2).const_mul (r^2))
  have hf := ((level_smooth r).differentiable (by simp) (c 0)).hasFDerivAt.comp_hasDerivAt 0 hc
  change HasDerivAt (level r ∘ c) _ 0 at hd
  have he := hf.unique hd
  simp [c,qDotP,qCrossP,zNormSq] at he
  rw [he]
  simp only [qDotP,qCrossP,zNormSq]
  ring
lemma level_euler (r : ℝ) (y : Phase) :
    fderiv ℝ (level r) y (fiberEuler y)=
      2*(qDotP y^2+4*qCrossP y^2)-4*wNormSq y*level r y := by
  rw [level_fderiv]
  simp [fiberEuler,vertical,qDotP,qCrossP,zNormSq,wNormSq,level]
  ring
lemma level_euler_positive (r : ℝ) (hr : 0 < r) (y : Phase)
    (hy : level r y=0) (hq : 0 < zNormSq y) :
    0 < fderiv ℝ (level r) y (fiberEuler y) := by
  have he : qDotP y^2+4*qCrossP y^2=r^2*(zNormSq y)^2 := sub_eq_zero.mp hy
  rw [level_euler,hy,mul_zero,sub_zero,he]
  positivity

lemma surface_qnorm_positive (r k : ℝ) (p : Plane × Plane) (hu : p.1 ∈ unitCircle) :
    0 < zNormSq (surface r k p) := by
  have hq : zNormSq (raw r k p)=1 := hu
  have ha : 0 < (Real.sqrt (zNormSq (raw r k p)+wNormSq (raw r k p)))⁻¹ :=
    inv_pos.mpr (Real.sqrt_pos.mpr (raw_positive r k p hu))
  have he (a : ℝ) : zNormSq (a • raw r k p)=a^2*zNormSq (raw r k p) := by
    simp [zNormSq]
    ring
  change 0 < zNormSq ((Real.sqrt (zNormSq (raw r k p)+wNormSq (raw r k p)))⁻¹ • raw r k p)
  rw [he,hq,mul_one]
  simpa only [hq] using sq_pos_of_pos ha
lemma surface_euler_positive (r : ℝ) (hr : 0 < r) (p : Plane × Plane)
    (hu : p.1 ∈ unitCircle) (hv : p.2 ∈ unitCircle) :
    0 < fderiv ℝ (level r) (surface r (1/2) p) (fiberEuler (surface r (1/2) p)) :=
  level_euler_positive r hr _ (surface_level r p hu hv) (surface_qnorm_positive r (1/2) p hu)
lemma raw_standard (r : ℝ) (p : Plane × Plane) (hu : p.1 ∈ unitCircle) :
    raw r 1 p=![p.1 0,p.1 1,r*p.2 0,r*p.2 1] := by
  have hh : p.1 0^2+p.1 1^2=1 := hu
  ext i
  fin_cases i
  · rfl
  · rfl
  · dsimp [raw,dot2,cross2]
    linear_combination r*p.2 0*hh
  · dsimp [raw,dot2,cross2]
    linear_combination r*p.2 1*hh

end
end ContactTopology.MeridianTorus


namespace ContactTopology.MeridianTorus
open BirkhoffGlobalSection BirkhoffGlobalSection.HopfTransport ContactTopology.ConvexCore Set Function
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma qDotP_smul (a : ℝ) (y : Phase) : qDotP (a • y)=a^2*qDotP y := by
  simp [qDotP]
  ring
lemma qCrossP_smul (a : ℝ) (y : Phase) : qCrossP (a • y)=a^2*qCrossP y := by
  simp [qCrossP]
  ring
lemma zNormSq_smul (a : ℝ) (y : Phase) : zNormSq (a • y)=a^2*zNormSq y := by
  simp [zNormSq]
  ring
lemma raw_dot (r k : ℝ) (p : Plane × Plane) :
    qDotP (raw r k p)=r*planeNormSq p.1*dot2 p.1 p.2 := by
  simp [qDotP,raw,planeNormSq,dot2,cross2]
  ring
lemma raw_cross (r k : ℝ) (p : Plane × Plane) :
    qCrossP (raw r k p)=r*k*planeNormSq p.1*cross2 p.1 p.2 := by
  simp [qCrossP,raw,planeNormSq,dot2,cross2]
  ring
lemma raw_qnorm (r k : ℝ) (p : Plane × Plane) :
    zNormSq (raw r k p)=planeNormSq p.1 := rfl

def qDirection (y : Phase) : Plane := (Real.sqrt (zNormSq y))⁻¹ • ![y 0,y 1]
def recoverSecond (r k : ℝ) (y : Phase) : Plane :=
  (qDotP y/(r*zNormSq y)) • qDirection y+
    (qCrossP y/(r*k*zNormSq y)) • circleTangent (qDirection y)
def recovery (r k : ℝ) (y : Phase) : Plane × Plane := (qDirection y,recoverSecond r k y)
lemma qDirection_smooth (y : Phase) (hy : 0 < zNormSq y) : ContDiffAt ℝ ∞ qDirection y := by
  have hq : ContDiff ℝ ∞ zNormSq := by unfold zNormSq; fun_prop
  have hn : ContDiffAt ℝ ∞ (fun z => (Real.sqrt (zNormSq z))⁻¹) y :=
    (hq.contDiffAt.sqrt hy.ne').inv (Real.sqrt_pos.mpr hy).ne'
  exact hn.smul (by apply contDiffAt_pi.mpr; intro i; fin_cases i <;> dsimp <;> fun_prop)
lemma recovery_smooth (r k : ℝ) (hr : r ≠ 0) (hk : k ≠ 0) (y : Phase)
    (hy : 0 < zNormSq y) : ContDiffAt ℝ ∞ (recovery r k) y := by
  have hd : ContDiff ℝ ∞ qDotP := by unfold qDotP; fun_prop
  have hc : ContDiff ℝ ∞ qCrossP := by unfold qCrossP; fun_prop
  have hq : ContDiff ℝ ∞ zNormSq := by unfold zNormSq; fun_prop
  have hD := qDirection_smooth y hy
  have hJ : ContDiff ℝ ∞ circleTangent := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> dsimp [circleTangent] <;> fun_prop
  exact hD.prodMk (((hd.contDiffAt.div (contDiffAt_const.mul hq.contDiffAt)
    (mul_ne_zero hr hy.ne')).smul hD).add
      ((hc.contDiffAt.div ((contDiffAt_const.mul contDiffAt_const).mul hq.contDiffAt)
        (mul_ne_zero (mul_ne_zero hr hk) hy.ne')).smul (hJ.contDiffAt.comp y hD)))

lemma qDirection_surface (r k : ℝ) (p : Plane × Plane) (hu : p.1 ∈ unitCircle) :
    qDirection (surface r k p)=p.1 := by
  let a := (Real.sqrt (zNormSq (raw r k p)+wNormSq (raw r k p)))⁻¹
  have ha : 0 < a := inv_pos.mpr (Real.sqrt_pos.mpr (raw_positive r k p hu))
  have hq : zNormSq (a • raw r k p)=a^2 := by rw [zNormSq_smul,raw_qnorm,hu,mul_one]
  change (Real.sqrt (zNormSq (a • raw r k p)))⁻¹ •
    ![(a • raw r k p) 0,(a • raw r k p) 1]=p.1
  rw [hq,Real.sqrt_sq ha.le]
  ext i
  fin_cases i <;> dsimp [raw] <;> field_simp [ha.ne']
lemma recovery_surface (r k : ℝ) (hr : r ≠ 0) (hk : k ≠ 0) (p : Plane × Plane)
    (hu : p.1 ∈ unitCircle) : recovery r k (surface r k p)=p := by
  have hu' : planeNormSq p.1=1 := hu
  let a := (Real.sqrt (zNormSq (raw r k p)+wNormSq (raw r k p)))⁻¹
  have ha : a ≠ 0 := (inv_pos.mpr (Real.sqrt_pos.mpr (raw_positive r k p hu))).ne'
  have hq : zNormSq (surface r k p)=a^2 := by
    change zNormSq (a • raw r k p)=a^2
    rw [zNormSq_smul,raw_qnorm,hu',mul_one]
  have hd : qDotP (surface r k p)=a^2*r*dot2 p.1 p.2 := by
    change qDotP (a • raw r k p)=_
    rw [qDotP_smul,raw_dot,hu']
    ring
  have hc : qCrossP (surface r k p)=a^2*r*k*cross2 p.1 p.2 := by
    change qCrossP (a • raw r k p)=_
    rw [qCrossP_smul,raw_cross,hu']
    ring
  apply Prod.ext
  · exact qDirection_surface r k p hu
  · change recoverSecond r k (surface r k p)=p.2
    unfold recoverSecond
    rw [qDirection_surface r k p hu,hd,hc,hq]
    have h1 : a^2*r*dot2 p.1 p.2/(r*a^2)=dot2 p.1 p.2 := by field_simp
    have h2 : a^2*r*k*cross2 p.1 p.2/(r*k*a^2)=cross2 p.1 p.2 := by field_simp
    rw [h1,h2]
    ext i
    fin_cases i <;> dsimp [dot2,cross2,circleTangent,planeNormSq] at hu' ⊢
    · linear_combination p.2 0*hu'
    · linear_combination p.2 1*hu'

lemma torusMap_continuous (r k : ℝ) : Continuous (torusMap r k) := by
  rw [continuous_iff_continuousAt]
  intro p
  have hc : Continuous (fun q : UnitPlaneCircle × UnitPlaneCircle => (q.1.val,q.2.val)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)
  change ContinuousAt (surface r k ∘ (fun q : UnitPlaneCircle × UnitPlaneCircle => (q.1.val,q.2.val))) p
  exact ContinuousAt.comp (f := fun q : UnitPlaneCircle × UnitPlaneCircle => (q.1.val,q.2.val)) (x := p)
    (surface_smooth r k (p.1.val,p.2.val) p.1.property).continuousAt hc.continuousAt
lemma torusMap_injective (r k : ℝ) (hr : r ≠ 0) (hk : k ≠ 0) : Injective (torusMap r k) := by
  intro p q he
  have hh := congrArg (recovery r k) he
  change recovery r k (surface r k (p.1.val,p.2.val))=
    recovery r k (surface r k (q.1.val,q.2.val)) at hh
  rw [recovery_surface r k hr hk _ p.1.property,recovery_surface r k hr hk _ q.1.property] at hh
  exact Prod.ext (Subtype.ext (congrArg Prod.fst hh)) (Subtype.ext (congrArg Prod.snd hh))
lemma torusMap_embedding (r k : ℝ) (hr : r ≠ 0) (hk : k ≠ 0) : Topology.IsEmbedding (torusMap r k) := by
  letI : CompactSpace UnitPlaneCircle := isCompact_iff_compactSpace.mp unitCircle_compact
  exact ((torusMap_continuous r k).isClosedEmbedding (torusMap_injective r k hr hk)).isEmbedding

end
end ContactTopology.MeridianTorus


namespace ContactTopology.MeridianTorus
open BirkhoffGlobalSection BirkhoffGlobalSection.HopfTransport ContactTopology.ConvexCore Set Function
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

def rotate (t : ℝ) (u : Plane) : Plane := Real.cos t • u+Real.sin t • circleTangent u
lemma rotate_zero (u : Plane) : rotate 0 u=u := by simp [rotate]
lemma rotate_unit (t : ℝ) (u : Plane) (hu : u ∈ unitCircle) : rotate t u ∈ unitCircle := by
  change planeNormSq u=1 at hu
  change planeNormSq (rotate t u)=1
  have he : planeNormSq (rotate t u)=(Real.cos t^2+Real.sin t^2)*planeNormSq u := by
    dsimp [rotate,circleTangent,planeNormSq]
    ring
  rw [he,hu,mul_one]
  nlinarith [Real.sin_sq_add_cos_sq t]
lemma rotate_deriv (a : ℝ) (u : Plane) :
    HasDerivAt (fun t : ℝ => rotate (a*t) u) (a • circleTangent u) 0 := by
  convert! ((((hasDerivAt_id (0:ℝ)).const_mul a).cos).smul_const u).add
    ((((hasDerivAt_id (0:ℝ)).const_mul a).sin).smul_const (circleTangent u)) using 1 <;> simp [rotate]
lemma tangent_ne_zero (u : Plane) (hu : u ∈ unitCircle) : circleTangent u ≠ 0 := by
  intro he
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  change -u 1=0 at h0
  change u 0=0 at h1
  change u 0^2+u 1^2=1 at hu
  simp [h1,neg_eq_zero.mp h0] at hu

lemma recovery_tangent (r k : ℝ) (hr : r ≠ 0) (hk : k ≠ 0) (p : Plane × Plane)
    (hu : p.1 ∈ unitCircle) (a b : ℝ) :
    fderiv ℝ (recovery r k) (surface r k p)
      (fderiv ℝ (surface r k) p (a • circleTangent p.1,b • circleTangent p.2))=
        (a • circleTangent p.1,b • circleTangent p.2) := by
  let c : ℝ → Plane × Plane := fun t => (rotate (a*t) p.1,rotate (b*t) p.2)
  have hc : HasDerivAt c (a • circleTangent p.1,b • circleTangent p.2) 0 :=
    (rotate_deriv a p.1).prodMk (rotate_deriv b p.2)
  have hc0 : c 0=p := by simp [c,rotate_zero]
  have hcs : (c 0).1 ∈ unitCircle := by rw [hc0]; exact hu
  have hs := ((surface_smooth r k (c 0) hcs).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt 0 hc
  have hR := ((recovery_smooth r k hr hk (surface r k (c 0))
    (surface_qnorm_positive r k (c 0) hcs)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt 0 hs
  have he : (fun t => recovery r k (surface r k (c t)))=c := by
    funext t
    exact recovery_surface r k hr hk (c t) (rotate_unit _ _ hu)
  change HasDerivAt (fun t => recovery r k (surface r k (c t))) _ 0 at hR
  rw [he] at hR
  simpa only [hc0] using hR.unique hc
lemma surface_tangent_injective (r k : ℝ) (hr : r ≠ 0) (hk : k ≠ 0) (p : Plane × Plane)
    (hu : p.1 ∈ unitCircle) (hv : p.2 ∈ unitCircle) :
    Injective (fun w : ℝ × ℝ => fderiv ℝ (surface r k) p
      (w.1 • circleTangent p.1,w.2 • circleTangent p.2)) := by
  intro a b he
  have hh := congrArg (fderiv ℝ (recovery r k) (surface r k p)) he
  rw [recovery_tangent r k hr hk p hu,recovery_tangent r k hr hk p hu] at hh
  exact Prod.ext ((smul_left_injective ℝ (tangent_ne_zero p.1 hu)) (congrArg Prod.fst hh))
    ((smul_left_injective ℝ (tangent_ne_zero p.2 hv)) (congrArg Prod.snd hh))
lemma surface_level_tangent (r : ℝ) (p : Plane × Plane)
    (hu : p.1 ∈ unitCircle) (hv : p.2 ∈ unitCircle) (a b : ℝ) :
    fderiv ℝ (level r) (surface r (1/2) p)
      (fderiv ℝ (surface r (1/2)) p (a • circleTangent p.1,b • circleTangent p.2))=0 := by
  let c : ℝ → Plane × Plane := fun t => (rotate (a*t) p.1,rotate (b*t) p.2)
  have hc : HasDerivAt c (a • circleTangent p.1,b • circleTangent p.2) 0 :=
    (rotate_deriv a p.1).prodMk (rotate_deriv b p.2)
  have hc0 : c 0=p := by simp [c,rotate_zero]
  have hcs : (c 0).1 ∈ unitCircle := by rw [hc0]; exact hu
  have hs := ((surface_smooth r (1/2) (c 0) hcs).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt 0 hc
  have hG := ((level_smooth r).differentiable (by simp) (surface r (1/2) (c 0))).hasFDerivAt.comp_hasDerivAt 0 hs
  have he : (fun t => level r (surface r (1/2) (c t)))=fun _ => (0:ℝ) := by
    funext t
    exact surface_level r (c t) (rotate_unit _ _ hu) (rotate_unit _ _ hv)
  change HasDerivAt (fun t => level r (surface r (1/2) (c t))) _ 0 at hG
  rw [he] at hG
  simpa only [hc0] using hG.unique (hasDerivAt_const (0:ℝ) (0:ℝ))
lemma surface_euler_transverse (r : ℝ) (hr : 0 < r) (p : Plane × Plane)
    (hu : p.1 ∈ unitCircle) (hv : p.2 ∈ unitCircle) (a b : ℝ) :
    fiberEuler (surface r (1/2) p) ≠ fderiv ℝ (surface r (1/2)) p
      (a • circleTangent p.1,b • circleTangent p.2) := by
  intro he
  have h := congrArg (fderiv ℝ (level r) (surface r (1/2) p)) he
  rw [surface_level_tangent r p hu hv] at h
  exact (surface_euler_positive r hr p hu hv).ne' h

end
end ContactTopology.MeridianTorus


namespace ContactTopology.MeridianTorus
open BirkhoffGlobalSection BirkhoffGlobalSection.HopfTransport ContactTopology.ConvexCore Set Function
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

def qToP (y : Phase) : Phase := ![0,0,y 0,y 1]
def perp (y : Phase) : Phase := vertical y-(qDotP y/zNormSq y) • qToP y
def spherePerp (y : Phase) : Phase := perp y-phaseDot y (perp y) • y
lemma qToP_smooth : ContDiff ℝ ∞ qToP := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [qToP] <;> fun_prop
lemma perp_smooth (y : Phase) (hy : 0 < zNormSq y) : ContDiffAt ℝ ∞ perp y := by
  have hdot : ContDiff ℝ ∞ qDotP := by unfold qDotP; fun_prop
  have hq : ContDiff ℝ ∞ zNormSq := by unfold zNormSq; fun_prop
  exact vertical_contDiff.contDiffAt.sub
    ((hdot.contDiffAt.div hq.contDiffAt hy.ne').smul qToP_smooth.contDiffAt)
lemma spherePerp_smooth (y : Phase) (hy : 0 < zNormSq y) : ContDiffAt ℝ ∞ spherePerp y := by
  have hp := perp_smooth y hy
  have hc (i : Fin 4) : ContDiffAt ℝ ∞ (fun z => perp z i) y :=
    (contDiff_apply ℝ ℝ i).contDiffAt.comp y hp
  have hdot : ContDiffAt ℝ ∞ (fun z => phaseDot z (perp z)) y := by
    unfold phaseDot
    fun_prop
  exact hp.sub (hdot.smul contDiffAt_id)
lemma phaseDot_smul_right (y z : Phase) (a : ℝ) : phaseDot y (a • z)=a*phaseDot y z := by
  simp [phaseDot]
  ring
lemma phaseDot_smul_both (y z : Phase) (a : ℝ) : phaseDot (a • y) (a • z)=a^2*phaseDot y z := by
  simp [phaseDot]
  ring
lemma phaseDot_sub_right (y z w : Phase) : phaseDot y (z-w)=phaseDot y z-phaseDot y w := by
  simp [phaseDot]
  ring
lemma spherePerp_tangent (y : Phase) (hy : y ∈ unitThreeSphere) : phaseDot y (spherePerp y)=0 := by
  rw [spherePerp,phaseDot_sub_right,phaseDot_smul_right,sphere_dot_self hy]
  ring
lemma perp_smul (a : ℝ) (ha : a ≠ 0) (y : Phase) (hy : 0 < zNormSq y) :
    perp (a • y)=a • perp y := by
  have hrat : qDotP (a • y)/zNormSq (a • y)=qDotP y/zNormSq y := by
    rw [qDotP_smul,zNormSq_smul]
    field_simp [ha,hy.ne']
  have hv : vertical (a • y)=a • vertical y := (verticalLinear.map_smul a y)
  have hq : qToP (a • y)=a • qToP y := by
    ext i
    fin_cases i <;> simp [qToP]
  rw [perp,hrat,hv,hq]
  ext i
  simp [perp]
  ring
lemma perp_odd (y : Phase) : perp (-y)= -perp y := by
  have hd : qDotP (-y)=qDotP y := by simp [qDotP]
  have hq : zNormSq (-y)=zNormSq y := by simp [zNormSq]
  have hv : vertical (-y)= -vertical y := verticalLinear.map_neg y
  have hp : qToP (-y)= -qToP y := by ext i; fin_cases i <;> simp [qToP]
  rw [perp,hd,hq,hv,hp]
  simp only [perp,smul_neg,neg_sub_neg]
  abel
lemma spherePerp_odd (y : Phase) : spherePerp (-y)= -spherePerp y := by
  have hd : phaseDot (-y) (perp (-y))=phaseDot y (perp y) := by rw [perp_odd]; simp [phaseDot]
  rw [spherePerp,hd,perp_odd,smul_neg]
  simp only [spherePerp]
  abel
lemma normalize_perp_derivative (y : Phase) (hy : 0 < zNormSq y+wNormSq y) (hq : 0 < zNormSq y) :
    fderiv ℝ radialNormalize y (perp y)=spherePerp (radialNormalize y) := by
  let Q := zNormSq y+wNormSq y
  let a := (Real.sqrt Q)⁻¹
  have hr : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hy
  have hs : (Real.sqrt Q)^2=Q := Real.sq_sqrt hy.le
  have hp : perp (a • y)=a • perp y := perp_smul a (inv_ne_zero hr.ne') y hq
  rw [radialNormalize_fderiv y (perp y) hy]
  change a • perp y-(phaseDot y (perp y)/(Q*Real.sqrt Q)) • y=spherePerp (a • y)
  rw [spherePerp,hp,phaseDot_smul_both]
  ext i
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  dsimp [a]
  rw [← hs]
  simp only [Real.sqrt_sq hr.le]
  field_simp [hr.ne'] <;> ring

def rawKDerivative (r : ℝ) (p : Plane × Plane) : Phase :=
  ![0,0,-r*p.1 1*cross2 p.1 p.2,r*p.1 0*cross2 p.1 p.2]
lemma perp_raw (r k : ℝ) (p : Plane × Plane) (hu : p.1 ∈ unitCircle) :
    perp (raw r k p)=k • rawKDerivative r p := by
  rw [perp,raw_dot,raw_qnorm,hu]
  ext i
  fin_cases i <;> simp [raw,vertical,qToP,rawKDerivative] <;> ring
lemma raw_parameter_hasDerivAt (r : ℝ) (p : Plane × Plane) (k : ℝ → ℝ) (t d : ℝ)
    (hk : HasDerivAt k d t) : HasDerivAt (fun s => raw r (k s) p) (d • rawKDerivative r p) t := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [raw,rawKDerivative] using hasDerivAt_const t (p.1 0)
  · simpa [raw,rawKDerivative] using hasDerivAt_const t (p.1 1)
  · have hh := ((hasDerivAt_const t (p.1 0*dot2 p.1 p.2)).sub
      (hk.mul_const (p.1 1*cross2 p.1 p.2))).const_mul r
    convert! hh using 1 <;> dsimp [raw,rawKDerivative] <;> ring
  · have hh := ((hasDerivAt_const t (p.1 1*dot2 p.1 p.2)).add
      (hk.mul_const (p.1 0*cross2 p.1 p.2))).const_mul r
    convert! hh using 1 <;> dsimp [raw,rawKDerivative] <;> ring
lemma surface_parameter_hasDerivAt (r : ℝ) (p : Plane × Plane) (hu : p.1 ∈ unitCircle)
    (k : ℝ → ℝ) (t d : ℝ) (hk : HasDerivAt k d t) (hk0 : k t ≠ 0) :
    HasDerivAt (fun s => surface r (k s) p) ((d/k t) • spherePerp (surface r (k t) p)) t := by
  have hraw := raw_parameter_hasDerivAt r p k t d hk
  have hN := (radial_normalization_contact_identity _ (raw_positive r (k t) p hu)).1
  have hd := (hN.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t hraw
  change HasDerivAt (fun s => surface r (k s) p) _ t at hd
  apply hd.congr_deriv
  have he : d • rawKDerivative r p=(d/k t) • perp (raw r (k t) p) := by
    rw [perp_raw r (k t) p hu,smul_smul]
    congr 1
    field_simp [hk0]
  have hqraw : 0 < zNormSq (raw r (k t) p) := by rw [raw_qnorm,hu]; norm_num
  rw [he,map_smul,normalize_perp_derivative _ (raw_positive r (k t) p hu) hqraw]
  rfl

end
end ContactTopology.MeridianTorus



namespace ContactTopology.MeridianTorus
open BirkhoffGlobalSection BirkhoffGlobalSection.HopfTransport ContactTopology.ConvexCore Set Function
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

def clock (t : ℝ) : ℝ := 1-Real.smoothTransition t/2
@[fun_prop] lemma clock_smooth : ContDiff ℝ ∞ clock :=
  contDiff_const.sub (Real.smoothTransition.contDiff.div_const 2)
lemma clock_bounds (t : ℝ) : 1/2 ≤ clock t ∧ clock t ≤ 1 := by
  have h0 := Real.smoothTransition.nonneg t
  have h1 := Real.smoothTransition.le_one t
  dsimp [clock]
  constructor <;> linarith
lemma clock_positive (t : ℝ) : 0 < clock t := by linarith [(clock_bounds t).1]
lemma clock_zero : clock 0=1 := by simp [clock]
lemma clock_one : clock 1=1/2 := by simp [clock]; norm_num
lemma clock_deriv_smooth : ContDiff ℝ ∞ (deriv clock) := by
  apply ContDiff.deriv'
  simpa using clock_smooth
def rate (t : ℝ) : ℝ := deriv clock t/clock t
@[fun_prop] lemma rate_smooth : ContDiff ℝ ∞ rate :=
  clock_deriv_smooth.div clock_smooth (fun t => (clock_positive t).ne')
lemma timed_surface_derivative (r : ℝ) (p : Plane × Plane) (hu : p.1 ∈ unitCircle) (t : ℝ) :
    HasDerivAt (fun s => surface r (clock s) p) (rate t • spherePerp (surface r (clock t) p)) t :=
  surface_parameter_hasDerivAt r p hu clock t (deriv clock t)
    (clock_smooth.differentiable (by simp) t).hasDerivAt (clock_positive t).ne'
lemma timed_surface_smooth (r : ℝ) (p : ℝ × (Plane × Plane)) (hu : p.2.1 ∈ unitCircle) :
    ContDiffAt ℝ ∞ (fun q : ℝ × (Plane × Plane) => surface r (clock q.1) q.2) p := by
  have hraw : ContDiff ℝ ∞ (fun q : ℝ × (Plane × Plane) => raw r (clock q.1) q.2) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> dsimp [raw,dot2,cross2] <;> fun_prop
  exact ((radial_normalization_contact_identity _ (raw_positive r (clock p.1) p.2 hu)).1).comp p hraw.contDiffAt

def trackMap (r : ℝ) (p : ℝ × (UnitPlaneCircle × UnitPlaneCircle)) : Phase :=
  surface r (clock p.1) (p.2.1.val,p.2.2.val)
lemma trackMap_continuous (r : ℝ) : Continuous (trackMap r) := by
  rw [continuous_iff_continuousAt]
  intro p
  have hc : Continuous (fun q : ℝ × (UnitPlaneCircle × UnitPlaneCircle) =>
      (q.1,(q.2.1.val,q.2.2.val))) := continuous_fst.prodMk
        ((continuous_subtype_val.comp (continuous_fst.comp continuous_snd)).prodMk
          (continuous_subtype_val.comp (continuous_snd.comp continuous_snd)))
  exact ContinuousAt.comp (f := fun q : ℝ × (UnitPlaneCircle × UnitPlaneCircle) =>
    (q.1,(q.2.1.val,q.2.2.val))) (x := p)
    (timed_surface_smooth r _ p.2.1.property).continuousAt hc.continuousAt
def track (r : ℝ) : Set Phase :=
  range (fun p : Icc (0:ℝ) 1 × (UnitPlaneCircle × UnitPlaneCircle) => trackMap r (p.1.val,p.2))
lemma track_compact (r : ℝ) : IsCompact (track r) := by
  letI : CompactSpace UnitPlaneCircle := isCompact_iff_compactSpace.mp unitCircle_compact
  exact isCompact_range ((trackMap_continuous r).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd))
lemma surface_pnorm_positive (r k : ℝ) (hr : 0 < r) (hk : 0 < k)
    (p : Plane × Plane) (hu : p.1 ∈ unitCircle) (hv : p.2 ∈ unitCircle) :
    0 < wNormSq (surface r k p) := by
  have hi := dot_cross_identity p.1 p.2
  change planeNormSq p.1=1 at hu
  change planeNormSq p.2=1 at hv
  rw [hu,hv] at hi
  have hs : 0 < dot2 p.1 p.2^2+k^2*cross2 p.1 p.2^2 := by
    by_cases hd : dot2 p.1 p.2=0
    · rw [hd,zero_pow (by norm_num),zero_add] at hi ⊢
      have hc : cross2 p.1 p.2^2=1 := by linarith [hi]
      rw [hc,mul_one]
      exact sq_pos_of_pos hk
    · nlinarith [sq_pos_of_ne_zero hd,mul_nonneg (sq_nonneg k) (sq_nonneg (cross2 p.1 p.2))]
  have hraw : wNormSq (raw r k p)=r^2*planeNormSq p.1*(dot2 p.1 p.2^2+k^2*cross2 p.1 p.2^2) := by
    simp [wNormSq,raw,dot2,cross2,planeNormSq]
    ring
  have hp : 0 < wNormSq (raw r k p) := by rw [hraw,hu,mul_one]; exact mul_pos (sq_pos_of_pos hr) hs
  let a := (Real.sqrt (zNormSq (raw r k p)+wNormSq (raw r k p)))⁻¹
  have ha : 0 < a := inv_pos.mpr (Real.sqrt_pos.mpr (raw_positive r k p hu))
  have he : wNormSq (a • raw r k p)=a^2*wNormSq (raw r k p) := by simp [wNormSq]; ring
  change 0 < wNormSq (a • raw r k p)
  rw [he]
  exact mul_pos (sq_pos_of_pos ha) hp
lemma track_properties (r : ℝ) (hr : 0 < r) (y : Phase) (hy : y ∈ track r) :
    y ∈ unitThreeSphere ∧ 0 < zNormSq y ∧ 0 < wNormSq y := by
  obtain ⟨p,rfl⟩ := hy
  exact ⟨surface_sphere r _ _ p.2.1.property,surface_qnorm_positive r _ _ p.2.1.property,
    surface_pnorm_positive r _ hr (clock_positive _) _ p.2.1.property p.2.2.property⟩

end
end ContactTopology.MeridianTorus


namespace ContactTopology.MeridianTorus
open BirkhoffGlobalSection BirkhoffGlobalSection.HopfTransport ContactTopology.ConvexCore Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

def cutoff (ε : ℝ) (y : Phase) : ℝ :=
  Real.smoothTransition ((zNormSq y-ε)/ε)*Real.smoothTransition ((wNormSq y-ε)/ε)*
    Real.smoothTransition (4-(zNormSq y+wNormSq y))
lemma cutoff_smooth (ε : ℝ) : ContDiff ℝ ∞ (cutoff ε) := by
  unfold cutoff zNormSq wNormSq
  fun_prop
lemma cutoff_even (ε : ℝ) (y : Phase) : cutoff ε (-y)=cutoff ε y := by
  simp only [cutoff,zNormSq,wNormSq,Pi.neg_apply,neg_sq]
lemma cutoff_qsmall (ε : ℝ) (hε : 0 < ε) (y : Phase) (hy : zNormSq y ≤ ε) : cutoff ε y=0 := by
  have hz : Real.smoothTransition ((zNormSq y-ε)/ε)=0 :=
    Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hy) hε.le)
  simp [cutoff,hz]
lemma cutoff_psmall (ε : ℝ) (hε : 0 < ε) (y : Phase) (hy : wNormSq y ≤ ε) : cutoff ε y=0 := by
  have hz : Real.smoothTransition ((wNormSq y-ε)/ε)=0 :=
    Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hy) hε.le)
  simp [cutoff,hz]
lemma cutoff_large (ε : ℝ) (y : Phase) (hy : 4 ≤ zNormSq y+wNormSq y) : cutoff ε y=0 := by
  have hz : Real.smoothTransition (4-(zNormSq y+wNormSq y))=0 :=
    Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr hy)
  simp [cutoff,hz]
lemma cutoff_one (ε : ℝ) (hε : 0 < ε) (y : Phase) (hy : y ∈ unitThreeSphere)
    (hq : 2*ε ≤ zNormSq y) (hp : 2*ε ≤ wNormSq y) : cutoff ε y=1 := by
  have hq' : 1 ≤ (zNormSq y-ε)/ε := (le_div_iff₀ hε).mpr (by linarith)
  have hp' : 1 ≤ (wNormSq y-ε)/ε := (le_div_iff₀ hε).mpr (by linarith)
  have hrad : 1 ≤ 4-(zNormSq y+wNormSq y) := by
    change zNormSq y+wNormSq y=1 at hy
    linarith
  simp only [cutoff,Real.smoothTransition.one_of_one_le hq',Real.smoothTransition.one_of_one_le hp',
    Real.smoothTransition.one_of_one_le hrad,mul_one]
lemma exists_track_cutoff (r : ℝ) (hr : 0 < r) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y ∈ track r, cutoff ε y=1 := by
  have hqcont : Continuous zNormSq := by unfold zNormSq; fun_prop
  have hpcont : Continuous wNormSq := by unfold wNormSq; fun_prop
  have hc : Continuous (fun y : Phase => min (zNormSq y) (wNormSq y)) := hqcont.min hpcont
  obtain ⟨m,hm,hb⟩ := (track_compact r).exists_forall_le' hc.continuousOn
    (by intro y hy; exact lt_min (track_properties r hr y hy).2.1 (track_properties r hr y hy).2.2)
  refine ⟨m/3,by linarith,?_⟩
  intro y hy
  have hq : m ≤ zNormSq y := (hb y hy).trans (min_le_left _ _)
  have hp : m ≤ wNormSq y := (hb y hy).trans (min_le_right _ _)
  exact cutoff_one _ (by linarith) y (track_properties r hr y hy).1 (by linarith) (by linarith)

def generator (ε : ℝ) (t : ℝ) (y : Phase) : Phase := (rate t*cutoff ε y) • spherePerp y
lemma generator_smooth (ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ ∞ (fun p : ℝ × Phase => generator ε p.1 p.2) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hq : 0 < zNormSq p.2
  · exact ((rate_smooth.contDiffAt.comp p contDiffAt_fst).mul
      ((cutoff_smooth ε).contDiffAt.comp p contDiffAt_snd)).smul
        ((spherePerp_smooth p.2 hq).comp p contDiffAt_snd)
  · have hc : Continuous (fun q : ℝ × Phase => zNormSq q.2) := by unfold zNormSq; fun_prop
    have hpq : zNormSq p.2 < ε := lt_of_le_of_lt (le_of_not_gt hq) hε
    have hnear : ∀ᶠ q : ℝ × Phase in 𝓝 p, zNormSq q.2 < ε :=
      (isOpen_lt hc continuous_const).mem_nhds hpq
    have he : (fun q : ℝ × Phase => generator ε q.1 q.2)=ᶠ[𝓝 p] fun _ => (0:Phase) := by
      filter_upwards [hnear] with q hq
      rw [generator,cutoff_qsmall ε hε q.2 hq.le,mul_zero,zero_smul]
    exact contDiffAt_const.congr_of_eventuallyEq he
lemma generator_odd (ε t : ℝ) (y : Phase) : generator ε t (-y)= -generator ε t y := by
  rw [generator,cutoff_even,spherePerp_odd,smul_neg]
  rfl
lemma generator_tangent (ε t : ℝ) (y : Phase) (hy : y ∈ unitThreeSphere) :
    phaseDot y (generator ε t y)=0 := by
  rw [generator,phaseDot_smul_right,spherePerp_tangent y hy,mul_zero]
lemma radius_le_four (y : Phase) (hy : zNormSq y+wNormSq y ≤ 4) : y ∈ Metric.closedBall (0:Phase) 2 := by
  rw [Metric.mem_closedBall,dist_zero_right,pi_norm_le_iff_of_nonneg (by norm_num)]
  intro i
  rw [Real.norm_eq_abs]
  apply (sq_le_sq₀ (abs_nonneg _) (by norm_num)).mp
  rw [sq_abs]
  unfold zNormSq wNormSq at hy
  have h0 : y 0^2 ≤ 4 := by nlinarith [sq_nonneg (y 1),sq_nonneg (y 2),sq_nonneg (y 3)]
  have h1 : y 1^2 ≤ 4 := by nlinarith [sq_nonneg (y 0),sq_nonneg (y 2),sq_nonneg (y 3)]
  have h2 : y 2^2 ≤ 4 := by nlinarith [sq_nonneg (y 0),sq_nonneg (y 1),sq_nonneg (y 3)]
  have h3 : y 3^2 ≤ 4 := by nlinarith [sq_nonneg (y 0),sq_nonneg (y 1),sq_nonneg (y 2)]
  norm_num only [show (2:ℝ)^2=4 by norm_num]
  fin_cases i
  exacts [h0,h1,h2,h3]
lemma generator_compact (ε : ℝ) : ∃ C : Set Phase, IsCompact C ∧
    ∀ t y, y ∉ C → generator ε t y=0 := by
  refine ⟨Metric.closedBall (0:Phase) 2,isCompact_closedBall (0:Phase) 2,?_⟩
  intro t y hy
  have hq : 4 ≤ zNormSq y+wNormSq y := le_of_lt (lt_of_not_ge (fun h => hy (radius_le_four y h)))
  rw [generator,cutoff_large ε y hq,mul_zero,zero_smul]
lemma generator_zero_near_cores (ε : ℝ) (hε : 0 < ε) (t : ℝ) (y : Phase)
    (hy : zNormSq y ≤ ε ∨ wNormSq y ≤ ε) : generator ε t y=0 := by
  rcases hy with hq|hp
  · rw [generator,cutoff_qsmall ε hε y hq,mul_zero,zero_smul]
  · rw [generator,cutoff_psmall ε hε y hp,mul_zero,zero_smul]
lemma generator_matches (r ε : ℝ) (hε : ∀ y ∈ track r, cutoff ε y=1)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (p : UnitPlaneCircle × UnitPlaneCircle) :
    generator ε t (trackMap r (t,p))=rate t • spherePerp (trackMap r (t,p)) := by
  have hm : trackMap r (t,p) ∈ track r := ⟨(⟨t,ht⟩,p),rfl⟩
  rw [generator,hε _ hm,mul_one]

end
end ContactTopology.MeridianTorus


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



namespace ContactTopology.MeridianTorus
open BirkhoffGlobalSection BirkhoffGlobalSection.HopfTransport BirkhoffGlobalSection.IsotopyExtension
open Set Function Filter GrayStability
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma ambient_torus_isotopy (r : ℝ) (hr : 0 < r) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ Φ R : ℝ → Phase → Phase,
      ContDiff ℝ ∞ (fun p : ℝ × Phase => Φ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × Phase => R p.1 p.2) ∧
      (∀ y, Φ 0 y=y) ∧
      (∀ t y, R t (Φ t y)=y) ∧ (∀ t y, Φ t (R t y)=y) ∧
      (∀ t y, Φ t (-y)= -Φ t y) ∧
      (∀ t, MapsTo (Φ t) unitThreeSphere unitThreeSphere) ∧
      (∀ t, MapsTo (R t) unitThreeSphere unitThreeSphere) ∧
      (∀ t y, Injective (fderiv ℝ (Φ t) y)) ∧
      (∀ t y, zNormSq y ≤ ε ∨ wNormSq y ≤ ε → Φ t y=y) ∧
      ∀ t p, Φ t (torusMap r 1 p)=trackMap r (Real.smoothTransition t,p) := by
  obtain ⟨ε,hε,hcut⟩ := exists_track_cutoff r hr
  let X := generator ε
  have hX : ContDiff ℝ ∞ (fun p : ℝ × Phase => X p.1 p.2) := generator_smooth ε hε
  have hsupp := generator_compact ε
  obtain ⟨ψ,hψ,h0,hbij,hd,hiso,hD⟩ :=
    FlowCalculus.compact_supported_flow_preserves_regular_level sphereEq sphereEq_regular X hX hsupp (by
      intro t ht y hy
      exact mem_tangentSpace_sphereEq.mpr (generator_tangent ε t y (mem_levelSet_sphereEq.mp hy)))
  obtain ⟨ρ,hρ,hρψ,hψρ⟩ := smooth_joint_flow_inverse X ψ hX hψ h0 hbij hd
  have hodd : ∀ t y, ψ t (-y)= -ψ t y := by
    intro t y
    have hpos : (fun s => ψ s (-y)) 0= -y ∧
        ∀ s, HasDerivAt (fun q => ψ q (-y)) (X s (ψ s (-y))) s := ⟨h0 _,fun s => hd s _⟩
    have hneg : (fun s => -ψ s y) 0= -y ∧
        ∀ s, HasDerivAt (fun q => -ψ q y) (X s (-ψ s y)) s := by
      refine ⟨congrArg Neg.neg (h0 y),?_⟩
      intro s
      change HasDerivAt (fun q => -ψ q y) (generator ε s (-ψ s y)) s
      rw [generator_odd]
      exact (hd s y).neg
    have he : (fun s => ψ s (-y))=fun s => -ψ s y := by
      apply (FlowCalculus.exists_unique_global_trajectory_of_compact_support X hX hsupp 0 (-y)).unique
      · exact hpos
      · exact hneg
    exact congrFun he t
  have hmap : ∀ t ∈ Icc (0:ℝ) 1, MapsTo (ψ t) unitThreeSphere unitThreeSphere := by
    intro t ht y hy
    exact mem_levelSet_sphereEq.mp ((hiso.2.2 t ht).1.mapsTo (mem_levelSet_sphereEq.mpr hy))
  have hrmap : ∀ t ∈ Icc (0:ℝ) 1, MapsTo (ρ t) unitThreeSphere unitThreeSphere := by
    intro t ht y hy
    obtain ⟨z,hz,hzy⟩ := (hiso.2.2 t ht).1.surjOn (mem_levelSet_sphereEq.mpr hy)
    rw [← hzy,hρψ]
    exact mem_levelSet_sphereEq.mp hz
  have hfix : ∀ t y, zNormSq y ≤ ε ∨ wNormSq y ≤ ε → ψ t y=y := by
    intro t y hy
    have hconst : (fun _ : ℝ => y) 0=y ∧
        ∀ s, HasDerivAt (fun _ : ℝ => y) (X s y) s := by
      refine ⟨rfl,?_⟩
      intro s
      change HasDerivAt (fun _ : ℝ => y) (generator ε s y) s
      rw [generator_zero_near_cores ε hε s y hy]
      exact hasDerivAt_const s y
    have he : (fun s => ψ s y)=fun _ => y := by
      apply (FlowCalculus.exists_unique_global_trajectory_of_compact_support X hX hsupp 0 y).unique
      · exact ⟨h0 y,fun s => hd s y⟩
      · exact hconst
    exact congrFun he t
  obtain ⟨L,hL⟩ := FlowCalculus.uniform_spatial_lipschitz_of_compact_support X hX hsupp 0 1
  have hmatch : ∀ t ∈ Icc (0:ℝ) 1, ∀ p, ψ t (torusMap r 1 p)=trackMap r (t,p) := by
    intro t ht p
    have hψc : Continuous (fun s => ψ s (torusMap r 1 p)) :=
      hψ.continuous.comp (continuous_id.prodMk continuous_const)
    have htc : Continuous (fun s => trackMap r (s,p)) :=
      (trackMap_continuous r).comp (continuous_id.prodMk continuous_const)
    have he : EqOn (fun s => ψ s (torusMap r 1 p)) (fun s => trackMap r (s,p)) (Icc (0:ℝ) 1) := by
      apply ODE_solution_unique_of_mem_Icc_right (v := X) (s := fun _ => Set.univ)
        (fun s hs => (hL s (Ico_subset_Icc_self hs)).lipschitzOnWith) hψc.continuousOn
        (fun s hs => (hd s _).hasDerivWithinAt) (fun _ _ => mem_univ _) htc.continuousOn
      · intro s hs
        change HasDerivWithinAt (fun s => trackMap r (s,p))
          (generator ε s (trackMap r (s,p))) (Ici s) s
        rw [generator_matches r ε hcut s (Ico_subset_Icc_self hs) p]
        exact (timed_surface_derivative r (p.1.val,p.2.val) p.1.property s).hasDerivWithinAt
      · exact fun _ _ => mem_univ _
      · simp [h0,trackMap,clock_zero,torusMap]
    exact he ht
  let Φ : ℝ → Phase → Phase := fun t y => ψ (Real.smoothTransition t) y
  let R : ℝ → Phase → Phase := fun t y => ρ (Real.smoothTransition t) y
  have harg : ContDiff ℝ ∞ (fun p : ℝ × Phase => (Real.smoothTransition p.1,p.2)) :=
    (Real.smoothTransition.contDiff.comp contDiff_fst).prodMk contDiff_snd
  have hτ (t : ℝ) : Real.smoothTransition t ∈ Icc (0:ℝ) 1 :=
    ⟨Real.smoothTransition.nonneg t,Real.smoothTransition.le_one t⟩
  refine ⟨ε,hε,Φ,R,hψ.comp harg,hρ.comp harg,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro y
    simp [Φ,h0]
  · intro t y
    exact hρψ _ y
  · intro t y
    exact hψρ _ y
  · intro t y
    exact hodd _ y
  · intro t
    exact hmap _ (hτ t)
  · intro t
    exact hrmap _ (hτ t)
  · intro t y
    exact FlowCalculus.smooth_flow_spatial_derivative_injective X ψ hX hψ h0 hd _ y
  · intro t y hy
    exact hfix _ y hy
  · intro t p
    exact hmatch _ (hτ t) p

end
end ContactTopology.MeridianTorus


namespace ContactTopology.MeridianTorus
open BirkhoffGlobalSection BirkhoffGlobalSection.HopfTransport ContactTopology.ConvexCore Set Function
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma wNormSq_smul (a : ℝ) (y : Phase) : wNormSq (a • y)=a^2*wNormSq y := by simp [wNormSq]; ring
lemma normalize_scale (a : ℝ) (ha : 0 < a) (y : Phase) : radialNormalize (a • y)=radialNormalize y := by
  have hQ : zNormSq (a • y)+wNormSq (a • y)=a^2*(zNormSq y+wNormSq y) := by
    rw [zNormSq_smul,wNormSq_smul]
    ring
  simp [radialNormalize,hQ,Real.sqrt_mul (sq_nonneg a),Real.sqrt_sq ha.le,mul_inv_rev,smul_smul,ha.ne']
lemma normalize_sphere (y : Phase) (hy : y ∈ unitThreeSphere) : radialNormalize y=y := by
  change zNormSq y+wNormSq y=1 at hy
  simp [radialNormalize,hy]

def solidRecovery (r : ℝ) (y : Phase) : Plane × Plane :=
  ((r/Real.sqrt (wNormSq y)) • ![y 0,y 1],(Real.sqrt (wNormSq y))⁻¹ • ![y 2,y 3])
lemma solidRaw_smooth (r : ℝ) : ContDiff ℝ ∞ (solidRaw r) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [solidRaw] <;> fun_prop
lemma solidRaw_positive (r : ℝ) (p : Plane × Plane) (hv : p.2 ∈ unitCircle) :
    0 < zNormSq (solidRaw r p)+wNormSq (solidRaw r p) := by
  have hp : wNormSq (solidRaw r p)=1 := hv
  rw [hp]
  unfold zNormSq
  positivity
lemma solid_smooth (r : ℝ) (p : Plane × Plane) (hv : p.2 ∈ unitCircle) : ContDiffAt ℝ ∞ (solid r) p :=
  ((radial_normalization_contact_identity _ (solidRaw_positive r p hv)).1).comp p (solidRaw_smooth r).contDiffAt
lemma solid_sphere (r : ℝ) (p : Plane × Plane) (hv : p.2 ∈ unitCircle) : solid r p ∈ unitThreeSphere :=
  (radial_normalization_contact_identity _ (solidRaw_positive r p hv)).2.1
lemma solid_recovery (r : ℝ) (hr : r ≠ 0) (p : Plane × Plane) (hv : p.2 ∈ unitCircle) :
    solidRecovery r (solid r p)=p := by
  let a := (Real.sqrt (zNormSq (solidRaw r p)+wNormSq (solidRaw r p)))⁻¹
  have ha : 0 < a := inv_pos.mpr (Real.sqrt_pos.mpr (solidRaw_positive r p hv))
  have hp : wNormSq (solidRaw r p)=1 := hv
  have hN : wNormSq (a • solidRaw r p)=a^2 := by rw [wNormSq_smul,hp,mul_one]
  change solidRecovery r (a • solidRaw r p)=p
  unfold solidRecovery
  rw [hN,Real.sqrt_sq ha.le]
  apply Prod.ext <;> ext i
  all_goals fin_cases i <;> dsimp [solidRaw] <;> field_simp [hr,ha.ne'] <;> ring
lemma solid_recovery_smooth (r : ℝ) (y : Phase) (hy : 0 < wNormSq y) : ContDiffAt ℝ ∞ (solidRecovery r) y := by
  have hp : ContDiff ℝ ∞ wNormSq := by unfold wNormSq; fun_prop
  have hi : ContDiffAt ℝ ∞ (fun y => (Real.sqrt (wNormSq y))⁻¹) y :=
    (hp.contDiffAt.sqrt hy.ne').inv (Real.sqrt_pos.mpr hy).ne'
  have hq : ContDiff ℝ ∞ (fun y : Phase => ![y 0,y 1]) := by
    apply contDiff_pi.mpr; intro i; fin_cases i <;> dsimp <;> fun_prop
  have hw : ContDiff ℝ ∞ (fun y : Phase => ![y 2,y 3]) := by
    apply contDiff_pi.mpr; intro i; fin_cases i <;> dsimp <;> fun_prop
  exact ((contDiffAt_const.mul hi).smul hq.contDiffAt).prodMk (hi.smul hw.contDiffAt)
lemma solid_pnorm (r : ℝ) (p : Plane × Plane) (hv : p.2 ∈ unitCircle) : 0 < wNormSq (solid r p) := by
  have hp : wNormSq (solidRaw r p)=1 := hv
  change 0 < wNormSq ((Real.sqrt (zNormSq (solidRaw r p)+wNormSq (solidRaw r p)))⁻¹ • solidRaw r p)
  rw [wNormSq_smul,hp,mul_one]
  simpa only [hp] using sq_pos_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr (solidRaw_positive r p hv)))

lemma disk_compact : IsCompact {u : Plane | planeNormSq u ≤ 1} := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_le (by unfold planeNormSq; fun_prop) continuous_const
  · apply (Metric.isBounded_closedBall (x := (0:Plane)) (r := 1)).subset
    intro u hu
    change u 0^2+u 1^2 ≤ 1 at hu
    rw [Metric.mem_closedBall,dist_zero_right,pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    rw [Real.norm_eq_abs]
    apply (sq_le_one_iff_abs_le_one _).mp
    fin_cases i
    · change u 0^2 ≤ 1
      nlinarith [sq_nonneg (u 1)]
    · change u 1^2 ≤ 1
      nlinarith [sq_nonneg (u 0)]
lemma solidMap_continuous (r : ℝ) : Continuous (solidMap r) := by
  rw [continuous_iff_continuousAt]
  intro p
  have hc : Continuous (fun q : DiskPoint × UnitPlaneCircle => (q.1.val,q.2.val)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)
  exact ContinuousAt.comp (f := fun q : DiskPoint × UnitPlaneCircle => (q.1.val,q.2.val)) (x := p)
    (solid_smooth r _ p.2.property).continuousAt hc.continuousAt
lemma solidMap_injective (r : ℝ) (hr : r ≠ 0) : Injective (solidMap r) := by
  intro p q he
  have hh := congrArg (solidRecovery r) he
  change solidRecovery r (solid r (p.1.val,p.2.val))=solidRecovery r (solid r (q.1.val,q.2.val)) at hh
  rw [solid_recovery r hr _ p.2.property,solid_recovery r hr _ q.2.property] at hh
  exact Prod.ext (Subtype.ext (congrArg Prod.fst hh)) (Subtype.ext (congrArg Prod.snd hh))
lemma solidMap_embedding (r : ℝ) (hr : r ≠ 0) : Topology.IsEmbedding (solidMap r) := by
  letI : CompactSpace UnitPlaneCircle := isCompact_iff_compactSpace.mp unitCircle_compact
  letI : CompactSpace DiskPoint := isCompact_iff_compactSpace.mp disk_compact
  exact ((solidMap_continuous r).isClosedEmbedding (solidMap_injective r hr)).isEmbedding

lemma solid_region_iff (r : ℝ) (hr : r ≠ 0) (p : Plane × Plane) (hv : p.2 ∈ unitCircle) :
    solid r p ∈ solidRegion r ↔ planeNormSq p.1 ≤ 1 := by
  let a := (Real.sqrt (zNormSq (solidRaw r p)+wNormSq (solidRaw r p)))⁻¹
  have ha : 0 < a := inv_pos.mpr (Real.sqrt_pos.mpr (solidRaw_positive r p hv))
  have hp : wNormSq (solid r p)=a^2 := by
    change wNormSq (a • solidRaw r p)=a^2
    rw [wNormSq_smul,show wNormSq (solidRaw r p)=1 from hv,mul_one]
  have hq : r^2*zNormSq (solid r p)=a^2*planeNormSq p.1 := by
    change r^2*zNormSq (a • solidRaw r p)=_
    rw [zNormSq_smul]
    change r^2*(a^2*((p.1 0/r)^2+(p.1 1/r)^2))=a^2*(p.1 0^2+p.1 1^2)
    field_simp [hr] <;> ring
  change solid r p ∈ unitThreeSphere ∧ r^2*zNormSq (solid r p) ≤ wNormSq (solid r p) ↔ _
  rw [hq,hp]
  constructor
  · intro h
    exact (mul_le_mul_iff_right₀ (sq_pos_of_pos ha)).mp (by simpa [mul_comm] using h.2)
  · intro h
    exact ⟨solid_sphere r p hv,by nlinarith [mul_nonneg (sq_nonneg a) (sub_nonneg.mpr h)]⟩
lemma region_pnorm (r : ℝ) (hr : 0 < r) (y : Phase) (hy : y ∈ solidRegion r) : 0 < wNormSq y := by
  have hs : zNormSq y+wNormSq y=1 := hy.1
  have hq : 0 ≤ zNormSq y := by unfold zNormSq; positivity
  have hp : 0 ≤ wNormSq y := by unfold wNormSq; positivity
  have hi := hy.2
  nlinarith [sq_pos_of_pos hr]
lemma recovery_second_unit (r : ℝ) (y : Phase) (hy : 0 < wNormSq y) :
    (solidRecovery r y).2 ∈ unitCircle := by
  change planeNormSq ((Real.sqrt (wNormSq y))⁻¹ • ![y 2,y 3])=1
  have he : planeNormSq ((Real.sqrt (wNormSq y))⁻¹ • ![y 2,y 3])=
      ((Real.sqrt (wNormSq y))⁻¹)^2*wNormSq y := by simp [planeNormSq,wNormSq]; ring
  rw [he,inv_pow,Real.sq_sqrt hy.le,inv_mul_cancel₀ hy.ne']
lemma solid_of_recovery (r : ℝ) (hr : r ≠ 0) (y : Phase) (hy : y ∈ unitThreeSphere)
    (hp : 0 < wNormSq y) : solid r (solidRecovery r y)=y := by
  let a := (Real.sqrt (wNormSq y))⁻¹
  have ha : 0 < a := inv_pos.mpr (Real.sqrt_pos.mpr hp)
  have he : solidRaw r (solidRecovery r y)=a • y := by
    ext i
    fin_cases i <;> dsimp [solidRaw,solidRecovery,a] <;> field_simp [hr] <;> ring
  rw [solid,Function.comp_apply,he,normalize_scale a ha y,normalize_sphere y hy]
lemma solidMap_range (r : ℝ) (hr : 0 < r) : range (solidMap r)=solidRegion r := by
  ext y
  constructor
  · rintro ⟨p,rfl⟩
    exact (solid_region_iff r hr.ne' _ p.2.property).mpr p.1.property
  · intro hy
    have hp := region_pnorm r hr y hy
    have hv := recovery_second_unit r y hp
    have he := solid_of_recovery r hr.ne' y hy.1 hp
    have hu : planeNormSq (solidRecovery r y).1 ≤ 1 :=
      (solid_region_iff r hr.ne' _ hv).mp (by rw [he]; exact hy)
    exact ⟨(⟨(solidRecovery r y).1,hu⟩,⟨(solidRecovery r y).2,hv⟩),he⟩
lemma solid_boundary (r : ℝ) (hr : 0 < r) (p : Plane × Plane) (hu : p.1 ∈ unitCircle) :
    solid r p=surface r 1 p := by
  have he : raw r 1 p=r • solidRaw r p := by
    rw [raw_standard r p hu]
    ext i
    fin_cases i <;> simp [solidRaw] <;> field_simp [hr.ne'] <;> ring
  change radialNormalize (solidRaw r p)=radialNormalize (raw r 1 p)
  rw [he,normalize_scale r hr]

lemma solid_tangent_recovery (r : ℝ) (hr : r ≠ 0) (p : Plane × Plane)
    (hv : p.2 ∈ unitCircle) (a : Plane) (b : ℝ) :
    fderiv ℝ (solidRecovery r) (solid r p)
      (fderiv ℝ (solid r) p (a,b • circleTangent p.2))=(a,b • circleTangent p.2) := by
  let c : ℝ → Plane × Plane := fun t => (p.1+t • a,rotate (b*t) p.2)
  have hc : HasDerivAt c (a,b • circleTangent p.2) 0 := by
    convert! ((hasDerivAt_const (0:ℝ) p.1).add
      ((hasDerivAt_id (0:ℝ)).smul_const a)).prodMk (rotate_deriv b p.2) using 1 <;> simp [c]
  have hc0 : c 0=p := by simp [c,rotate_zero]
  have hcv : (c 0).2 ∈ unitCircle := by rw [hc0]; exact hv
  have hs := ((solid_smooth r (c 0) hcv).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt 0 hc
  have hR := ((solid_recovery_smooth r (solid r (c 0))
    (solid_pnorm r (c 0) hcv)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt 0 hs
  have he : (fun t => solidRecovery r (solid r (c t)))=c := by
    funext t
    exact solid_recovery r hr (c t) (rotate_unit _ _ hv)
  change HasDerivAt (fun t => solidRecovery r (solid r (c t))) _ 0 at hR
  rw [he] at hR
  simpa only [hc0] using hR.unique hc
lemma solid_tangent_injective (r : ℝ) (hr : r ≠ 0) (p : Plane × Plane)
    (hv : p.2 ∈ unitCircle) :
    Injective (fun w : Plane × ℝ => fderiv ℝ (solid r) p (w.1,w.2 • circleTangent p.2)) := by
  intro a b he
  have hh := congrArg (fderiv ℝ (solidRecovery r) (solid r p)) he
  rw [solid_tangent_recovery r hr p hv,solid_tangent_recovery r hr p hv] at hh
  exact Prod.ext (congrArg (fun q : Plane × Plane => q.1) hh)
    ((smul_left_injective ℝ (tangent_ne_zero p.2 hv)) (congrArg (fun q : Plane × Plane => q.2) hh))

end
end ContactTopology.MeridianTorus


namespace ContactTopology.MeridianTorus
open BirkhoffGlobalSection BirkhoffGlobalSection.HopfTransport ContactTopology.ConvexCore Set Function
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma standardDisk_smooth (r : ℝ) : ContDiff ℝ ∞ (standardDisk r) := by
  rw [contDiff_iff_contDiffAt]
  intro u
  exact (solid_smooth r (u,pole) pole_unit).comp u (contDiffAt_id.prodMk contDiffAt_const)
lemma standardDisk_sphere (r : ℝ) (u : Plane) : standardDisk r u ∈ unitThreeSphere :=
  solid_sphere r (u,pole) pole_unit
lemma standardDisk_recovery (r : ℝ) (hr : r ≠ 0) (u : Plane) :
    (solidRecovery r (standardDisk r u)).1=u :=
  congrArg Prod.fst (solid_recovery r hr (u,pole) pole_unit)
lemma standardDisk_injective (r : ℝ) (hr : r ≠ 0) : Injective (standardDisk r) := by
  intro u v he
  have hh := congrArg (fun y => (solidRecovery r y).1) he
  simpa only [standardDisk_recovery r hr] using hh
lemma standardDisk_immersed (r : ℝ) (hr : r ≠ 0) (u : Plane) :
    Injective (fderiv ℝ (standardDisk r) u) := by
  let Q : Phase → Plane := fun y => (solidRecovery r y).1
  have hQ : DifferentiableAt ℝ Q (standardDisk r u) :=
    (contDiffAt_fst.comp _ (solid_recovery_smooth r _ (solid_pnorm r (u,pole) pole_unit))).differentiableAt (by simp)
  have hM := (standardDisk_smooth r).differentiable (by simp) u
  have he : Q ∘ standardDisk r=id := by funext v; exact standardDisk_recovery r hr v
  have hd (w : Plane) : fderiv ℝ Q (standardDisk r u) (fderiv ℝ (standardDisk r) u w)=w := by
    rw [← ContinuousLinearMap.comp_apply,← fderiv_comp u hQ hM,he]
    simp
  intro a b hab
  have hh := congrArg (fderiv ℝ Q (standardDisk r u)) hab
  simpa only [hd] using hh
lemma standardDisk_boundary (r : ℝ) (hr : 0 < r) (u : Plane) (hu : u ∈ unitCircle) :
    standardDisk r u=surface r 1 (u,pole) := solid_boundary r hr (u,pole) hu
lemma standardDisk_qnorm_zero (r : ℝ) (hr : r ≠ 0) (u : Plane) :
    zNormSq (standardDisk r u)=0 ↔ u=0 := by
  constructor
  · intro h
    have h0 : standardDisk r u 0=0 := by
      change (standardDisk r u 0)^2+(standardDisk r u 1)^2=0 at h
      nlinarith [sq_nonneg (standardDisk r u 1),sq_nonneg (standardDisk r u 0)]
    have h1 : standardDisk r u 1=0 := by
      change (standardDisk r u 0)^2+(standardDisk r u 1)^2=0 at h
      nlinarith [sq_nonneg (standardDisk r u 1),sq_nonneg (standardDisk r u 0)]
    rw [← standardDisk_recovery r hr u]
    ext i
    fin_cases i <;> simp [solidRecovery,h0,h1]
  · rintro rfl
    simp [standardDisk,solid,Function.comp_apply,radialNormalize,zNormSq,solidRaw]
lemma standardDisk_meets_torus (r : ℝ) (hr : 0 < r) (u : Plane) :
    standardDisk r u ∈ range (torusMap r 1) ↔ u ∈ unitCircle := by
  constructor
  · rintro ⟨p,hp⟩
    have he : solid r (p.1.val,p.2.val)=solid r (u,pole) := by
      rw [solid_boundary r hr _ p.1.property]
      exact hp
    have hh := congrArg (solidRecovery r) he
    rw [solid_recovery r hr.ne' _ p.2.property,solid_recovery r hr.ne' _ pole_unit] at hh
    have hu := congrArg Prod.fst hh
    change p.1.val=u at hu
    rw [← hu]
    exact p.1.property
  · intro hu
    exact ⟨(⟨u,hu⟩,⟨pole,pole_unit⟩),(standardDisk_boundary r hr u hu).symm⟩

lemma time_slice_smooth (Φ : ℝ → Phase → Phase)
    (hΦ : ContDiff ℝ ∞ (fun p : ℝ × Phase => Φ p.1 p.2)) (t : ℝ) : ContDiff ℝ ∞ (Φ t) :=
  hΦ.comp (contDiff_const.prodMk contDiff_id)
lemma movedDisk_smooth (r : ℝ) (Φ : ℝ → Phase → Phase)
    (hΦ : ContDiff ℝ ∞ (fun p : ℝ × Phase => Φ p.1 p.2)) : ContDiff ℝ ∞ (movedDisk r Φ) :=
  (time_slice_smooth Φ hΦ 1).comp (standardDisk_smooth r)
lemma movedDisk_boundary (r : ℝ) (hr : 0 < r) (Φ : ℝ → Phase → Phase)
    (hm : ∀ t p, Φ t (torusMap r 1 p)=trackMap r (Real.smoothTransition t,p))
    (u : Plane) (hu : u ∈ unitCircle) : movedDisk r Φ u=surface r (1/2) (u,pole) := by
  have he := hm 1 (⟨u,hu⟩,⟨pole,pole_unit⟩)
  change Φ 1 (standardDisk r u)=_
  rw [standardDisk_boundary r hr u hu]
  simpa only [torusMap,trackMap,Real.smoothTransition.one,clock_one] using he
lemma movedDisk_boundary_tangent (r : ℝ) (hr : 0 < r) (Φ : ℝ → Phase → Phase)
    (hΦ : ContDiff ℝ ∞ (fun p : ℝ × Phase => Φ p.1 p.2))
    (hm : ∀ t p, Φ t (torusMap r 1 p)=trackMap r (Real.smoothTransition t,p))
    (u : Plane) (hu : u ∈ unitCircle) :
    fderiv ℝ (movedDisk r Φ) u (circleTangent u)=
      fderiv ℝ (surface r (1/2)) (u,pole) (circleTangent u,0) := by
  have hc : HasDerivAt (fun t => rotate t u) (circleTangent u) 0 := by
    simpa using rotate_deriv 1 u
  have hM := ((movedDisk_smooth r Φ hΦ).differentiable (by simp) (rotate 0 u)).hasFDerivAt.comp_hasDerivAt 0 hc
  have hc' := hc.prodMk (hasDerivAt_const (0:ℝ) pole)
  have hS := ((surface_smooth r (1/2) (rotate 0 u,pole) (rotate_unit 0 u hu)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt 0 hc'
  have he : (fun t => movedDisk r Φ (rotate t u))=fun t => surface r (1/2) (rotate t u,pole) := by
    funext t
    exact movedDisk_boundary r hr Φ hm _ (rotate_unit t u hu)
  change HasDerivAt (fun t => movedDisk r Φ (rotate t u)) _ 0 at hM
  rw [he] at hM
  simpa only [rotate_zero] using hM.unique hS
lemma movedDisk_legendrian_boundary (r : ℝ) (hr : 0 < r) (Φ : ℝ → Phase → Phase)
    (hΦ : ContDiff ℝ ∞ (fun p : ℝ × Phase => Φ p.1 p.2))
    (hm : ∀ t p, Φ t (torusMap r 1 p)=trackMap r (Real.smoothTransition t,p))
    (u : Plane) (hu : u ∈ unitCircle) :
    phaseRadialContact (movedDisk r Φ u) (fderiv ℝ (movedDisk r Φ) u (circleTangent u))=0 := by
  rw [movedDisk_boundary r hr Φ hm u hu,movedDisk_boundary_tangent r hr Φ hΦ hm u hu]
  exact surface_meridian_legendrian r (u,pole) hu

/-- An actual disk-times-circle embedding and its meridian slice, obtained by an
ambient sphere isotopy. The last equivalence is the proper-boundary condition.
This theorem does not assert convexity of the disk. -/
theorem exists_proper_legendrian_meridian (r : ℝ) (hr : 0 < r) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ Φ R : ℝ → Phase → Phase,
      ContDiff ℝ ∞ (fun p : ℝ × Phase => Φ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × Phase => R p.1 p.2) ∧
      (∀ y, Φ 0 y=y) ∧
      (∀ t y, R t (Φ t y)=y) ∧ (∀ t y, Φ t (R t y)=y) ∧
      (∀ t y, Φ t (-y)= -Φ t y) ∧
      (∀ t, MapsTo (Φ t) unitThreeSphere unitThreeSphere) ∧
      (∀ t, MapsTo (R t) unitThreeSphere unitThreeSphere) ∧
      (∀ t y, zNormSq y ≤ ε ∨ wNormSq y ≤ ε → Φ t y=y) ∧
      (∀ p, Φ 1 (torusMap r 1 p)=torusMap r (1/2) p) ∧
      Topology.IsEmbedding (torusMap r (1/2)) ∧
      (∀ p : Plane × Plane, p.1 ∈ unitCircle → p.2 ∈ unitCircle →
        Injective (fun w : ℝ × ℝ => fderiv ℝ (surface r (1/2)) p
          (w.1 • circleTangent p.1,w.2 • circleTangent p.2))) ∧
      Topology.IsEmbedding (movedSolid r Φ) ∧
      (∀ p : Plane × Plane, p.2 ∈ unitCircle → ContDiffAt ℝ ∞ (movedProduct r Φ) p) ∧
      (∀ p : Plane × Plane, p.2 ∈ unitCircle →
        Injective (fun w : Plane × ℝ => fderiv ℝ (movedProduct r Φ) p (w.1,w.2 • circleTangent p.2))) ∧
      (∀ p : Plane × Plane, p.1 ∈ unitCircle → p.2 ∈ unitCircle →
        movedProduct r Φ p=surface r (1/2) p) ∧
      range (movedSolid r Φ)=Φ 1 '' solidRegion r ∧
      (∀ p, movedSolid r Φ p ∈ unitThreeSphere) ∧
      ContDiff ℝ ∞ (movedDisk r Φ) ∧ Injective (movedDisk r Φ) ∧
      (∀ u, Injective (fderiv ℝ (movedDisk r Φ) u)) ∧
      Topology.IsEmbedding (fun u : DiskPoint => movedDisk r Φ u.val) ∧
      (∀ u, movedDisk r Φ u ∈ unitThreeSphere) ∧
      (∀ p : DiskPoint, movedDisk r Φ p.val=movedSolid r Φ (p,⟨pole,pole_unit⟩)) ∧
      (∀ u, planeNormSq u ≤ 1 → movedDisk r Φ u ∈ Φ 1 '' solidRegion r) ∧
      (∀ u, u ∈ unitCircle → movedDisk r Φ u=surface r (1/2) (u,pole)) ∧
      (∀ u, u ∈ unitCircle → phaseRadialContact (movedDisk r Φ u)
        (fderiv ℝ (movedDisk r Φ) u (circleTangent u))=0) ∧
      (∀ u, movedDisk r Φ u ∈ range (torusMap r (1/2)) ↔ u ∈ unitCircle) ∧
      (∀ u, zNormSq (movedDisk r Φ u)=0 ↔ u=0) ∧
      ∃ X : Phase → Phase, ContDiff ℝ ∞ X ∧
        (∀ y, X (-y)= -X y) ∧
        (∀ y ∈ unitThreeSphere, phaseDot y (X y)=0) ∧
        (∀ y, ∃ a : ℝ, ∀ v, phaseRadialContact (X y) v+
          phaseRadialContact y (fderiv ℝ X y v)=a*phaseRadialContact y v) ∧
        (∀ p : Plane × Plane, p.1 ∈ unitCircle → p.2 ∈ unitCircle → ∀ a b : ℝ,
          X (surface r (1/2) p) ≠ fderiv ℝ (surface r (1/2)) p
            (a • circleTangent p.1,b • circleTangent p.2)) := by
  obtain ⟨ε,hε,Φ,R,hΦ,hR,h0,hRΦ,hΦR,hodd,hsph,hRsph,hD,hfix,hm⟩ := ambient_torus_isotopy r hr
  have hi : Injective (Φ 1) := by
    intro a b hab
    have hh := congrArg (R 1) hab
    simpa only [hRΦ] using hh
  have htor (p : UnitPlaneCircle × UnitPlaneCircle) :
      Φ 1 (torusMap r 1 p)=torusMap r (1/2) p := by
    simpa only [Real.smoothTransition.one,trackMap,clock_one,torusMap] using hm 1 p
  have hΦ1 := time_slice_smooth Φ hΦ 1
  have hMs := movedDisk_smooth r Φ hΦ
  have hMi : Injective (movedDisk r Φ) := hi.comp (standardDisk_injective r hr.ne')
  have hKc : Continuous (movedSolid r Φ) := hΦ1.continuous.comp (solidMap_continuous r)
  have hKi : Injective (movedSolid r Φ) := hi.comp (solidMap_injective r hr.ne')
  letI : CompactSpace UnitPlaneCircle := isCompact_iff_compactSpace.mp unitCircle_compact
  letI : CompactSpace DiskPoint := isCompact_iff_compactSpace.mp disk_compact
  refine ⟨ε,hε,Φ,R,hΦ,hR,h0,hRΦ,hΦR,hodd,hsph,hRsph,hfix,htor,
    torusMap_embedding r (1/2) hr.ne' (by norm_num),
    (fun p hu hv => surface_tangent_injective r (1/2) hr.ne' (by norm_num) p hu hv),
    (hKc.isClosedEmbedding hKi).isEmbedding,?_,?_,?_,?_,?_,hMs,hMi,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro p hp
    exact hΦ1.contDiffAt.comp p (solid_smooth r p hp)
  · intro p hp a b hab
    apply solid_tangent_injective r hr.ne' p hp
    apply hD 1 (solid r p)
    change fderiv ℝ (Φ 1) (solid r p) (fderiv ℝ (solid r) p (a.1,a.2 • circleTangent p.2))=
      fderiv ℝ (Φ 1) (solid r p) (fderiv ℝ (solid r) p (b.1,b.2 • circleTangent p.2))
    simpa only [movedProduct,fderiv_comp p (hΦ1.differentiable (by simp) _)
      ((solid_smooth r p hp).differentiableAt (by simp)),ContinuousLinearMap.comp_apply] using hab
  · intro p hu hv
    change Φ 1 (solid r p)=_
    rw [solid_boundary r hr p hu]
    exact htor (⟨p.1,hu⟩,⟨p.2,hv⟩)
  · ext y
    constructor
    · rintro ⟨p,rfl⟩
      refine ⟨solidMap r p,?_,rfl⟩
      rw [← solidMap_range r hr]
      exact mem_range_self p
    · rintro ⟨z,hz,rfl⟩
      rw [← solidMap_range r hr] at hz
      obtain ⟨p,rfl⟩ := hz
      exact ⟨p,rfl⟩
  · intro p
    exact hsph 1 (solid_sphere r (p.1.val,p.2.val) p.2.property)
  · intro u
    change Injective (fderiv ℝ (Φ 1 ∘ standardDisk r) u)
    rw [fderiv_comp u (hΦ1.differentiable (by simp) _) ((standardDisk_smooth r).differentiable (by simp) u)]
    exact (hD 1 _).comp (standardDisk_immersed r hr.ne' u)
  · exact ((hMs.continuous.comp continuous_subtype_val).isClosedEmbedding
      (hMi.comp Subtype.val_injective)).isEmbedding
  · intro u
    exact hsph 1 (standardDisk_sphere r u)
  · intro p
    rfl
  · intro u hu
    exact ⟨standardDisk r u,(solid_region_iff r hr.ne' (u,pole) pole_unit).mpr hu,rfl⟩
  · intro u hu
    exact movedDisk_boundary r hr Φ hm u hu
  · intro u hu
    exact movedDisk_legendrian_boundary r hr Φ hΦ hm u hu
  · intro u
    constructor
    · rintro ⟨p,hp⟩
      have he : Φ 1 (torusMap r 1 p)=Φ 1 (standardDisk r u) := by
        rw [htor]
        exact hp
      exact (standardDisk_meets_torus r hr u).mp ⟨p,hi he⟩
    · intro hu
      exact ⟨(⟨u,hu⟩,⟨pole,pole_unit⟩),(movedDisk_boundary r hr Φ hm u hu).symm⟩
  · intro u
    constructor
    · intro hq
      have hf : Φ 1 (movedDisk r Φ u)=movedDisk r Φ u :=
        hfix 1 _ (Or.inl (by rw [hq]; exact hε.le))
      have he : standardDisk r u=movedDisk r Φ u := hi hf.symm
      exact (standardDisk_qnorm_zero r hr.ne' u).mp (by rw [he]; exact hq)
    · rintro rfl
      have hq := (standardDisk_qnorm_zero r hr.ne' (0:Plane)).mpr rfl
      change zNormSq (Φ 1 (standardDisk r 0))=0
      rw [hfix 1 _ (Or.inl (by rw [hq]; exact hε.le))]
      exact hq
  · refine ⟨fiberEuler,fiberEuler_contDiff,fiberEuler_odd,fiberEuler_tangent,?_,?_⟩
    · intro y
      exact ⟨1-2*wNormSq y,fiberEuler_lie y⟩
    · intro p hu hv a b
      exact surface_euler_transverse r hr p hu hv a b

end
end ContactTopology.MeridianTorus

open BirkhoffGlobalSection ContactTopology.MeridianTorus Set Function
open scoped ContDiff Topology

theorem solution (r : ℝ) (hr : 0 < r) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ Φ R : ℝ → Phase → Phase,
      ContDiff ℝ ∞ (fun p : ℝ × Phase => Φ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × Phase => R p.1 p.2) ∧
      (∀ y, Φ 0 y=y) ∧
      (∀ t y, R t (Φ t y)=y) ∧ (∀ t y, Φ t (R t y)=y) ∧
      (∀ t y, Φ t (-y)= -Φ t y) ∧
      (∀ t, MapsTo (Φ t) unitThreeSphere unitThreeSphere) ∧
      (∀ t, MapsTo (R t) unitThreeSphere unitThreeSphere) ∧
      (∀ t y, zNormSq y ≤ ε ∨ wNormSq y ≤ ε → Φ t y=y) ∧
      (∀ p, Φ 1 (torusMap r 1 p)=torusMap r (1/2) p) ∧
      Topology.IsEmbedding (torusMap r (1/2)) ∧
      (∀ p : Plane × Plane, p.1 ∈ unitCircle → p.2 ∈ unitCircle →
        Injective (fun w : ℝ × ℝ => fderiv ℝ (surface r (1/2)) p
          (w.1 • circleTangent p.1,w.2 • circleTangent p.2))) ∧
      Topology.IsEmbedding (movedSolid r Φ) ∧
      (∀ p : Plane × Plane, p.2 ∈ unitCircle → ContDiffAt ℝ ∞ (movedProduct r Φ) p) ∧
      (∀ p : Plane × Plane, p.2 ∈ unitCircle →
        Injective (fun w : Plane × ℝ => fderiv ℝ (movedProduct r Φ) p (w.1,w.2 • circleTangent p.2))) ∧
      (∀ p : Plane × Plane, p.1 ∈ unitCircle → p.2 ∈ unitCircle →
        movedProduct r Φ p=surface r (1/2) p) ∧
      range (movedSolid r Φ)=Φ 1 '' solidRegion r ∧
      (∀ p, movedSolid r Φ p ∈ unitThreeSphere) ∧
      ContDiff ℝ ∞ (movedDisk r Φ) ∧ Injective (movedDisk r Φ) ∧
      (∀ u, Injective (fderiv ℝ (movedDisk r Φ) u)) ∧
      Topology.IsEmbedding (fun u : DiskPoint => movedDisk r Φ u.val) ∧
      (∀ u, movedDisk r Φ u ∈ unitThreeSphere) ∧
      (∀ p : DiskPoint, movedDisk r Φ p.val=movedSolid r Φ (p,⟨pole,pole_unit⟩)) ∧
      (∀ u, planeNormSq u ≤ 1 → movedDisk r Φ u ∈ Φ 1 '' solidRegion r) ∧
      (∀ u, u ∈ unitCircle → movedDisk r Φ u=surface r (1/2) (u,pole)) ∧
      (∀ u, u ∈ unitCircle → phaseRadialContact (movedDisk r Φ u)
        (fderiv ℝ (movedDisk r Φ) u (circleTangent u))=0) ∧
      (∀ u, movedDisk r Φ u ∈ range (torusMap r (1/2)) ↔ u ∈ unitCircle) ∧
      (∀ u, zNormSq (movedDisk r Φ u)=0 ↔ u=0) ∧
      ∃ X : Phase → Phase, ContDiff ℝ ∞ X ∧
        (∀ y, X (-y)= -X y) ∧
        (∀ y ∈ unitThreeSphere, phaseDot y (X y)=0) ∧
        (∀ y, ∃ a : ℝ, ∀ v, phaseRadialContact (X y) v+
          phaseRadialContact y (fderiv ℝ X y v)=a*phaseRadialContact y v) ∧
        (∀ p : Plane × Plane, p.1 ∈ unitCircle → p.2 ∈ unitCircle → ∀ a b : ℝ,
          X (surface r (1/2) p) ≠ fderiv ℝ (surface r (1/2)) p
            (a • circleTangent p.1,b • circleTangent p.2)) := by
  exact ContactTopology.MeridianTorus.exists_proper_legendrian_meridian r hr
