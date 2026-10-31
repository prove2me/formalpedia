-- Prove2me | solution 1 for ContactTopology.contactomorphic_core_convex_rounded_annulus
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-31T01:48:50.353397+00:00
-- url     : https://prove2.me/submissions/14ee28c6-e5e6-4426-91d7-494f61509061

import Definitions.Def_BirkhoffGlobalSection_SphereContact
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Order.IntermediateValue
import Theorems.Thm_BirkhoffGlobalSection_radial_normalization_contact_identity
import Theorems.Thm_ContactCalculus_exterior_pairing_pullback






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


namespace ContactTopology.EdgeRounding
open Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section
abbrev V := Fin 3 → ℝ

def coeff (freq : ℝ) (y : V) : V := ![Real.sin (freq*y 2),Real.cos (freq*y 2),0]
def α (freq : ℝ) (y v : V) : ℝ := Real.sin (freq*y 2)*v 0+Real.cos (freq*y 2)*v 1
def field (r : ℝ) (y : V) : V := ![y 0-r,y 1-r,0]
def flow (r t : ℝ) (y : V) : V :=
  ![r+Real.exp t*(y 0-r),r+Real.exp t*(y 1-r),y 2]
def rounded (r : ℝ) (p : ℝ × ℝ) : V :=
  ![r*(1-Real.cos p.1),r*(1-Real.sin p.1),p.2]

def curve (freq r : ℝ) (k : ℤ) (θ : ℝ) : V := rounded r (θ,k*Real.pi/freq-θ/freq)

lemma coeff_smooth (freq : ℝ) : ContDiff ℝ ∞ (coeff freq) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [coeff] <;> fun_prop
lemma field_smooth (r : ℝ) : ContDiff ℝ ∞ (field r) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [field] <;> fun_prop
lemma flow_smooth (r : ℝ) : ContDiff ℝ ∞ (fun p : ℝ × V => flow r p.1 p.2) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [flow] <;> fun_prop
lemma rounded_smooth (r : ℝ) : ContDiff ℝ ∞ (rounded r) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [rounded] <;> fun_prop

lemma coeff_fderiv (freq : ℝ) (y v : V) :
    fderiv ℝ (coeff freq) y v=
      ![freq*Real.cos (freq*y 2)*v 2,-freq*Real.sin (freq*y 2)*v 2,0] := by
  let e : V →L[ℝ] ℝ := ContinuousLinearMap.proj 2
  have hsin := ((e.hasFDerivAt (x := y)).const_mul freq).sin
  have hcos := ((e.hasFDerivAt (x := y)).const_mul freq).cos
  have hD : HasFDerivAt (coeff freq) (ContinuousLinearMap.pi
      ![Real.cos (freq*y 2) • (freq • e),-Real.sin (freq*y 2) • (freq • e),0]) y := by
    apply hasFDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact hsin
    · exact hcos
    · exact hasFDerivAt_const (0:ℝ) y
  rw [hD.fderiv]
  ext i
  fin_cases i <;> simp [e] <;> ring

lemma field_fderiv (r : ℝ) (y v : V) : fderiv ℝ (field r) y v=![v 0,v 1,0] := by
  have hD : HasFDerivAt (field r) (ContinuousLinearMap.pi
      ![(ContinuousLinearMap.proj (0:Fin 3) : V →L[ℝ] ℝ),ContinuousLinearMap.proj (1:Fin 3),0]) y := by
    apply hasFDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact (ContinuousLinearMap.proj (0:Fin 3) : V →L[ℝ] ℝ).hasFDerivAt.sub_const r
    · exact (ContinuousLinearMap.proj (1:Fin 3) : V →L[ℝ] ℝ).hasFDerivAt.sub_const r
    · exact hasFDerivAt_const (0:ℝ) y
  rw [hD.fderiv]
  ext i
  fin_cases i <;> simp

lemma flow_fderiv (r t : ℝ) (y v : V) :
    fderiv ℝ (flow r t) y v=![Real.exp t*v 0,Real.exp t*v 1,v 2] := by
  have hD : HasFDerivAt (flow r t) (ContinuousLinearMap.pi
      ![Real.exp t • (ContinuousLinearMap.proj (0:Fin 3) : V →L[ℝ] ℝ),Real.exp t • ContinuousLinearMap.proj (1:Fin 3),
        ContinuousLinearMap.proj (2:Fin 3)]) y := by
    apply hasFDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact (((ContinuousLinearMap.proj (0:Fin 3) : V →L[ℝ] ℝ).hasFDerivAt.sub_const r).const_mul
        (Real.exp t)).const_add r
    · exact (((ContinuousLinearMap.proj (1:Fin 3) : V →L[ℝ] ℝ).hasFDerivAt.sub_const r).const_mul
        (Real.exp t)).const_add r
    · exact (ContinuousLinearMap.proj (2:Fin 3) : V →L[ℝ] ℝ).hasFDerivAt
  rw [hD.fderiv]
  ext i
  fin_cases i <;> simp

lemma rounded_fderiv (r : ℝ) (p v : ℝ × ℝ) :
    fderiv ℝ (rounded r) p v=![r*Real.sin p.1*v.1,-r*Real.cos p.1*v.1,v.2] := by
  have hD : HasFDerivAt (rounded r) (ContinuousLinearMap.pi
      ![(r*Real.sin p.1) • ContinuousLinearMap.fst ℝ ℝ ℝ,
        (-r*Real.cos p.1) • ContinuousLinearMap.fst ℝ ℝ ℝ,
        ContinuousLinearMap.snd ℝ ℝ ℝ]) p := by
    apply hasFDerivAt_pi.mpr
    intro i
    fin_cases i
    · have hh := ((hasFDerivAt_const (𝕜 := ℝ) (1:ℝ) p).sub
        (hasFDerivAt_fst (𝕜 := ℝ) (p := p)).cos).const_mul r
      convert! hh using 1 <;> ext w <;> simp <;> ring
    · have hh := ((hasFDerivAt_const (𝕜 := ℝ) (1:ℝ) p).sub
        (hasFDerivAt_fst (𝕜 := ℝ) (p := p)).sin).const_mul r
      convert! hh using 1 <;> ext w <;> simp <;> ring
    · exact hasFDerivAt_snd
  rw [hD.fderiv]
  ext i
  fin_cases i <;> simp

lemma contact_volume (freq : ℝ) (y : V) :
    coeff freq y 0*(fderiv ℝ (coeff freq) y (Pi.single 1 1) 2-fderiv ℝ (coeff freq) y (Pi.single 2 1) 1)+
      coeff freq y 1*(fderiv ℝ (coeff freq) y (Pi.single 2 1) 0-fderiv ℝ (coeff freq) y (Pi.single 0 1) 2)+
      coeff freq y 2*(fderiv ℝ (coeff freq) y (Pi.single 0 1) 1-fderiv ℝ (coeff freq) y (Pi.single 1 1) 0)=freq := by
  simp [coeff_fderiv,coeff]
  linear_combination freq * Real.sin_sq_add_cos_sq (freq*y 2)

lemma field_contact (freq r : ℝ) (y v : V) :
    (fderiv ℝ (coeff freq) y (field r y)) 0*v 0+
      (fderiv ℝ (coeff freq) y (field r y)) 1*v 1+
      (fderiv ℝ (coeff freq) y (field r y)) 2*v 2+
      α freq y (fderiv ℝ (field r) y v)=α freq y v := by
  simp [coeff_fderiv,field,field_fderiv,α]

lemma flow_contact (freq r t : ℝ) (y v : V) :
    α freq (flow r t y) (fderiv ℝ (flow r t) y v)=Real.exp t*α freq y v := by
  simp [flow,flow_fderiv,α]
  ring

lemma flow_zero (r : ℝ) (y : V) : flow r 0 y=y := by
  ext i
  fin_cases i <;> simp [flow]
lemma flow_inverse (r t : ℝ) (y : V) : flow r (-t) (flow r t y)=y := by
  ext i
  fin_cases i <;> simp [flow,Real.exp_neg]

lemma flow_velocity (r t : ℝ) (y : V) :
    HasDerivAt (fun s => flow r s y) (field r (flow r t y)) t := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · convert ((Real.hasDerivAt_exp t).mul_const (y 0-r)).const_add r using 1 <;> simp [flow,field]
  · convert ((Real.hasDerivAt_exp t).mul_const (y 1-r)).const_add r using 1 <;> simp [flow,field]
  · exact hasDerivAt_const t (y 2)

lemma rounded_immersion (r : ℝ) (hr : 0 < r) (p : ℝ × ℝ) :
    Injective (fderiv ℝ (rounded r) p) := by
  intro v w h
  rw [rounded_fderiv,rounded_fderiv] at h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 : v.2=w.2 := congrFun h 2
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one] at h0 h1
  have he : v.1=w.1 := by
    by_cases hs : Real.sin p.1=0
    · have hc : Real.cos p.1 ≠ 0 := by intro hc; have hi := Real.sin_sq_add_cos_sq p.1; simp [hs,hc] at hi
      exact mul_left_cancel₀ (mul_ne_zero (neg_ne_zero.mpr hr.ne') hc) h1
    · exact mul_left_cancel₀ (mul_ne_zero hr.ne' hs) h0
  exact Prod.ext he h2

lemma rounded_injOn (r : ℝ) (hr : 0 < r) :
    InjOn (rounded r) (Icc (0:ℝ) (Real.pi/2) ×ˢ (univ:Set ℝ)) := by
  rintro ⟨θ,z⟩ ⟨hθ,hz⟩ ⟨η,w⟩ ⟨hη,hw⟩ heq
  have hsin : Real.sin θ=Real.sin η := by
    have hh := congrFun heq 1
    simp [rounded] at hh
    exact hh.resolve_right hr.ne'
  have hθ' : θ ∈ Icc (-(Real.pi/2)) (Real.pi/2) := ⟨(show -(Real.pi/2) ≤ 0 by linarith [Real.pi_pos]).trans hθ.1,hθ.2⟩
  have hη' : η ∈ Icc (-(Real.pi/2)) (Real.pi/2) := ⟨(show -(Real.pi/2) ≤ 0 by linarith [Real.pi_pos]).trans hη.1,hη.2⟩
  exact Prod.ext (Real.strictMonoOn_sin.injOn hθ' hη' hsin) (congrFun heq 2)

lemma rounded_transverse (r : ℝ) (hr : 0 < r) (p v : ℝ × ℝ) :
    field r (rounded r p) ≠ fderiv ℝ (rounded r) p v := by
  intro heq
  rw [rounded_fderiv] at heq
  have h0 := congrFun heq 0
  have h1 := congrFun heq 1
  simp only [rounded,field,Matrix.cons_val_zero,Matrix.cons_val_one] at h0 h1
  have hs := Real.sin_sq_add_cos_sq p.1
  have hh : r=0 := by
    linear_combination -Real.cos p.1*h0-Real.sin p.1*h1-r*hs
  linarith

lemma rounded_contact_value (freq r : ℝ) (p : ℝ × ℝ) :
    α freq (rounded r p) (field r (rounded r p)) = -r*Real.sin (freq*p.2+p.1) := by
  simp [α,rounded,field,Real.sin_add]
  ring

lemma rounded_dividing_iff (freq r : ℝ) (hfreq : 0 < freq) (hr : 0 < r) (p : ℝ × ℝ) :
    α freq (rounded r p) (field r (rounded r p))=0 ↔
      ∃ k : ℤ, p.2=k*Real.pi/freq-p.1/freq := by
  rw [rounded_contact_value,mul_eq_zero]
  simp only [neg_eq_zero,hr.ne',false_or,Real.sin_eq_zero_iff]
  constructor
  · rintro ⟨k,hk⟩
    refine ⟨k,?_⟩
    rw [← sub_div]
    apply (eq_div_iff hfreq.ne').mpr
    linarith
  · rintro ⟨k,hk⟩
    refine ⟨k,?_⟩
    rw [hk]
    field_simp [hfreq.ne']
    ring

end
end ContactTopology.EdgeRounding


namespace ContactTopology.EdgeRoundingSphere
open BirkhoffGlobalSection ContactTopology.ConvexCore Set Function
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
noncomputable section
abbrev V := Fin 3 → ℝ

def rotateJet (freq : ℝ) (y : V) : Jet3 :=
  ![y 2,freq*(y 0*Real.cos (freq*y 2)-y 1*Real.sin (freq*y 2)),
    y 0*Real.sin (freq*y 2)+y 1*Real.cos (freq*y 2)]
def unrotateJet (freq : ℝ) (p : Jet3) : V :=
  ![Real.cos (freq*p 0)*(p 1/freq)+Real.sin (freq*p 0)*p 2,
    -Real.sin (freq*p 0)*(p 1/freq)+Real.cos (freq*p 0)*p 2,p 0]
lemma rotateJet_smooth (freq : ℝ) : ContDiff ℝ ∞ (rotateJet freq) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [rotateJet] <;> fun_prop
lemma unrotateJet_smooth (freq : ℝ) : ContDiff ℝ ∞ (unrotateJet freq) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [unrotateJet] <;> fun_prop
lemma unrotate_rotate (freq : ℝ) (hf : freq ≠ 0) (y : V) : unrotateJet freq (rotateJet freq y)=y := by
  ext i
  fin_cases i
  · simp only [unrotateJet,rotateJet,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
    simp
    field_simp [hf]
    linear_combination y 0*Real.sin_sq_add_cos_sq (freq*y 2)
  · simp only [unrotateJet,rotateJet,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
    simp
    field_simp [hf]
    linear_combination y 1*Real.sin_sq_add_cos_sq (freq*y 2)
  · rfl

lemma rotateJet_fderiv (freq : ℝ) (y v : V) : fderiv ℝ (rotateJet freq) y v=
    ![v 2,freq*(Real.cos (freq*y 2)*v 0-Real.sin (freq*y 2)*v 1-
        freq*(y 0*Real.sin (freq*y 2)+y 1*Real.cos (freq*y 2))*v 2),
      Real.sin (freq*y 2)*v 0+Real.cos (freq*y 2)*v 1+
        freq*(y 0*Real.cos (freq*y 2)-y 1*Real.sin (freq*y 2))*v 2] := by
  let e (i : Fin 3) : V →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have hd (i : Fin 3) : HasFDerivAt (fun y : V => y i) (e i) y := (e i).hasFDerivAt
  have hs := ((hd 2).const_mul freq).sin
  have hc := ((hd 2).const_mul freq).cos
  have h1 := (((hd 0).mul hc).sub ((hd 1).mul hs)).const_mul freq
  have h2 := ((hd 0).mul hs).add ((hd 1).mul hc)
  change HasFDerivAt (fun y : V => freq*(y 0*Real.cos (freq*y 2)-y 1*Real.sin (freq*y 2))) _ y at h1
  change HasFDerivAt (fun y : V => y 0*Real.sin (freq*y 2)+y 1*Real.cos (freq*y 2)) _ y at h2
  have hD : HasFDerivAt (rotateJet freq) (ContinuousLinearMap.pi ![e 2,
      fderiv ℝ (fun y : V => freq*(y 0*Real.cos (freq*y 2)-y 1*Real.sin (freq*y 2))) y,
      fderiv ℝ (fun y : V => y 0*Real.sin (freq*y 2)+y 1*Real.cos (freq*y 2)) y]) y := by
    apply hasFDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact hd 2
    · exact h1.differentiableAt.hasFDerivAt
    · exact h2.differentiableAt.hasFDerivAt
  rw [hD.fderiv]
  ext i
  fin_cases i
  · simp [e]
  · change (fderiv ℝ (fun y : V => freq*(y 0*Real.cos (freq*y 2)-y 1*Real.sin (freq*y 2))) y) v=_
    rw [h1.fderiv]
    simp [e] <;> ring_nf <;> simp
  · change (fderiv ℝ (fun y : V => y 0*Real.sin (freq*y 2)+y 1*Real.cos (freq*y 2)) y) v=_
    rw [h2.fderiv]
    simp [e] <;> ring_nf <;> simp

lemma rotateJet_contact (freq : ℝ) (y v : V) :
    jetContact (rotateJet freq y) (fderiv ℝ (rotateJet freq) y v)=ContactTopology.EdgeRounding.α freq y v := by
  rw [rotateJet_fderiv]
  simp [jetContact,rotateJet,ContactTopology.EdgeRounding.α]
lemma rotateJet_immersion (freq : ℝ) (hf : freq ≠ 0) (y : V) :
    Injective (fderiv ℝ (rotateJet freq) y) := by
  have heq : unrotateJet freq ∘ rotateJet freq=id := funext (unrotate_rotate freq hf)
  have hd := congrArg (fun f : V → V => fderiv ℝ f y) heq
  rw [fderiv_comp y ((unrotateJet_smooth freq).differentiable (by simp) _)
    ((rotateJet_smooth freq).differentiable (by simp) _),fderiv_id] at hd
  intro v w he
  have hh := congrArg (fderiv ℝ (unrotateJet freq) (rotateJet freq y)) he
  change ((fderiv ℝ (unrotateJet freq) (rotateJet freq y)).comp
      (fderiv ℝ (rotateJet freq) y)) v=
    ((fderiv ℝ (unrotateJet freq) (rotateJet freq y)).comp (fderiv ℝ (rotateJet freq) y)) w at hh
  simpa only [hd,ContinuousLinearMap.id_apply] using hh

def cover (F : EquivariantSphereContactomorphism) (freq : ℝ) : V → Phase := imageChart F ∘ rotateJet freq
def weight (F : EquivariantSphereContactomorphism) (freq : ℝ) : V → ℝ := imageChartFactor F ∘ rotateJet freq
lemma cover_smooth (F : EquivariantSphereContactomorphism) (freq : ℝ) : ContDiff ℝ ∞ (cover F freq) :=
  (imageChart_contDiff F).comp (rotateJet_smooth freq)
lemma weight_smooth (F : EquivariantSphereContactomorphism) (freq : ℝ) : ContDiff ℝ ∞ (weight F freq) :=
  (imageChartFactor_contDiff F).comp (rotateJet_smooth freq)
lemma cover_mem (F : EquivariantSphereContactomorphism) (freq : ℝ) (y : V) :
    cover F freq y ∈ unitThreeSphere := imageChart_mem F _
lemma weight_pos (F : EquivariantSphereContactomorphism) (freq : ℝ) (y : V) :
    0 < weight F freq y := (imageChart_contact_factor F _).1
lemma cover_contact (F : EquivariantSphereContactomorphism) (freq : ℝ) (y v : V) :
    phaseRadialContact (cover F freq y) (fderiv ℝ (cover F freq) y v)=
      weight F freq y*ContactTopology.EdgeRounding.α freq y v := by
  change phaseRadialContact (imageChart F (rotateJet freq y))
    (fderiv ℝ (imageChart F ∘ rotateJet freq) y v)=_
  rw [fderiv_comp y ((imageChart_contDiff F).differentiable (by simp) _)
    ((rotateJet_smooth freq).differentiable (by simp) _)]
  exact ((imageChart_contact_factor F (rotateJet freq y)).2 _).trans
    (congrArg (fun h => weight F freq y*h) (rotateJet_contact freq y v))
lemma cover_immersion (F : EquivariantSphereContactomorphism) (freq : ℝ) (hf : freq ≠ 0) (y : V) :
    Injective (fderiv ℝ (cover F freq) y) := by
  change Injective (fderiv ℝ (imageChart F ∘ rotateJet freq) y)
  rw [fderiv_comp y ((imageChart_contDiff F).differentiable (by simp) _)
    ((rotateJet_smooth freq).differentiable (by simp) _)]
  exact (imageChart_derivative_injective F _).comp (rotateJet_immersion freq hf y)

lemma rotateJet_injective (freq : ℝ) (hf : freq ≠ 0) : Injective (rotateJet freq) := by
  intro y z heq
  have hh := congrArg (unrotateJet freq) heq
  simpa only [unrotate_rotate freq hf] using hh

def shift (t : ℝ) (y : V) : V := ![y 0,y 1,y 2+t]
lemma rotateJet_shift (n : ℕ) (y : V) (k : ℤ) :
    rotateJet (2*Real.pi*n) (shift k y)=rotateJet (2*Real.pi*n) y+corePoint k := by
  let m : ℤ := (n:ℤ)*k
  have he : (2*Real.pi*n)*(y 2+k)=(2*Real.pi*n)*y 2+(m:ℝ)*(2*Real.pi) := by
    dsimp only [m]
    push_cast
    ring
  have hs : Real.sin ((2*Real.pi*n)*(y 2+k))=Real.sin ((2*Real.pi*n)*y 2) := by
    rw [he]; exact Real.sin_add_int_mul_two_pi _ m
  have hc : Real.cos ((2*Real.pi*n)*(y 2+k))=Real.cos ((2*Real.pi*n)*y 2) := by
    rw [he]; exact Real.cos_add_int_mul_two_pi _ m
  ext i
  fin_cases i <;> simp [rotateJet,shift,corePoint,hs,hc]

lemma cover_fiber (F : EquivariantSphereContactomorphism) (n : ℕ) (hn : 0 < n) (y z : V) :
    cover F (2*Real.pi*n) y=cover F (2*Real.pi*n) z ↔ ∃ k : ℤ, y=shift k z := by
  have hf : 2*Real.pi*n ≠ 0 := ne_of_gt (mul_pos (by positivity) (by exact_mod_cast hn))
  change imageChart F (rotateJet (2*Real.pi*n) y)=imageChart F (rotateJet (2*Real.pi*n) z) ↔ _
  rw [imageChart_fiber]
  constructor
  · rintro ⟨k,hk⟩
    refine ⟨k,rotateJet_injective _ hf ?_⟩
    rw [rotateJet_shift]
    exact hk
  · rintro ⟨k,rfl⟩
    exact ⟨k,rotateJet_shift n z k⟩

lemma cover_core (F : EquivariantSphereContactomorphism) (freq z : ℝ) :
    cover F freq ![0,0,z]=F.toFun ![Real.cos (2*Real.pi*z),Real.sin (2*Real.pi*z),0,0] := by
  have he : rotateJet freq (![0,0,z]:V)=corePoint z := by ext i; fin_cases i <;> simp [rotateJet,corePoint]
  change F.toFun (legendrianSphereChart (rotateJet freq ![0,0,z]))=_
  rw [he,legendrianSphereChart_core]

lemma cover_antipodal (F : EquivariantSphereContactomorphism) (y : V) :
    cover F (4*Real.pi) (shift (1/2) y)= -cover F (4*Real.pi) y := by
  have he : (4*Real.pi)*(y 2+1/2)=(4*Real.pi)*y 2+2*Real.pi := by ring
  have hs : Real.sin ((4*Real.pi)*(y 2+1/2))=Real.sin ((4*Real.pi)*y 2) := by
    rw [he,Real.sin_add_two_pi]
  have hc : Real.cos ((4*Real.pi)*(y 2+1/2))=Real.cos ((4*Real.pi)*y 2) := by
    rw [he,Real.cos_add_two_pi]
  simp only [one_div] at hs hc
  have hT : rotateJet (4*Real.pi) (shift (1/2) y)=rotateJet (4*Real.pi) y+corePoint (1/2) := by
    ext i
    fin_cases i <;> simp [rotateJet,shift,corePoint,hs,hc]
  change F.toFun (legendrianSphereChart (rotateJet (4*Real.pi) (shift (1/2) y)))=_
  rw [hT,legendrianSphereChart_antipodal,F.antipodal _ (legendrianSphereChart_mem _)]
  rfl

end
end ContactTopology.EdgeRoundingSphere


namespace ContactTopology.EdgeRoundingSphere
open BirkhoffGlobalSection ContactTopology.ConvexCore Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma rotate_unrotate (freq : ℝ) (hf : freq ≠ 0) (p : Jet3) : rotateJet freq (unrotateJet freq p)=p := by
  ext i
  fin_cases i
  · rfl
  · simp [rotateJet,unrotateJet]
    field_simp [hf]
    linear_combination p 1*Real.sin_sq_add_cos_sq (freq*p 0)
  · simp [rotateJet,unrotateJet]
    field_simp [hf]
    linear_combination (freq*p 2)*Real.sin_sq_add_cos_sq (freq*p 0)

lemma cover_local_inverse (F : EquivariantSphereContactomorphism) (freq : ℝ) (hf : freq ≠ 0) (y : V) :
    ∃ R : Phase → V, ContDiffAt ℝ ∞ R (cover F freq y) ∧ R (cover F freq y)=y ∧
      (∀ᶠ q in 𝓝 y, R (cover F freq q)=q) ∧
      ∀ᶠ z in 𝓝 (cover F freq y), z ∈ unitThreeSphere → cover F freq (R z)=z := by
  obtain ⟨R₀,O,hO,hpoint,hR₀on,hRpoint,hleft,hrr⟩ := legendrianSphereChart_open_inverse (rotateJet freq y)
  have hR₀ : ContDiffAt ℝ ∞ R₀ (legendrianSphereChart (rotateJet freq y)) :=
    (hR₀on _ hpoint).contDiffAt (hO.mem_nhds hpoint)
  have hright : ∀ᶠ z in 𝓝 (legendrianSphereChart (rotateJet freq y)),
      z ∈ unitThreeSphere → legendrianSphereChart (R₀ z)=z := by
    filter_upwards [hO.mem_nhds hpoint] with z hz
    exact hrr z hz
  have hFinv : F.invFun (cover F freq y)=legendrianSphereChart (rotateJet freq y) :=
    F.left_inv _ (legendrianSphereChart_mem _)
  let R : Phase → V := fun z => unrotateJet freq (R₀ (F.invFun z))
  have hR₀' : ContDiffAt ℝ ∞ R₀ (F.invFun (cover F freq y)) := by rw [hFinv]; exact hR₀
  have hRs : ContDiffAt ℝ ∞ R (cover F freq y) :=
    (unrotateJet_smooth freq).contDiffAt.comp _ (hR₀'.comp _ (F.inv_smooth _ (cover_mem F freq y)))
  refine ⟨R,hRs,?_,?_,?_⟩
  · change unrotateJet freq (R₀ (F.invFun (cover F freq y)))=y
    rw [hFinv,hRpoint,unrotate_rotate freq hf]
  · have hpre := (rotateJet_smooth freq).continuous.continuousAt.eventually hleft
    filter_upwards [hpre] with q hq
    change unrotateJet freq (R₀ (F.invFun (F.toFun (legendrianSphereChart (rotateJet freq q)))))=q
    rw [F.left_inv _ (legendrianSphereChart_mem _),hq,unrotate_rotate freq hf]
  · have hT : Tendsto F.invFun (𝓝 (cover F freq y))
        (𝓝 (legendrianSphereChart (rotateJet freq y))) := by
      simpa only [ContinuousAt,hFinv] using (F.inv_smooth _ (cover_mem F freq y)).continuousAt
    have hpre := hT.eventually hright
    filter_upwards [hpre] with z hz hzS
    change F.toFun (legendrianSphereChart
      (rotateJet freq (unrotateJet freq (R₀ (F.invFun z)))))=z
    rw [rotate_unrotate freq hf,hz (F.inv_maps_sphere hzS),F.right_inv z hzS]

end
end ContactTopology.EdgeRoundingSphere


namespace ContactTopology.EdgeRoundingSphere
open BirkhoffGlobalSection Set Function
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
noncomputable section

def shear (r : ℝ) (y : Phase) : Phase :=
  ![y 0,y 1,y 2-2*r*(y 0+y 1),y 3-2*r*(y 0-y 1)]
def shearLinear (r : ℝ) : Phase →L[ℝ] Phase :=
  LinearMap.toContinuousLinearMap
    { toFun := shear r
      map_add' := by intro y z; ext i; fin_cases i <;> simp [shear] <;> ring
      map_smul' := by intro a y; ext i; fin_cases i <;> simp [shear] <;> ring }
lemma shear_smooth (r : ℝ) : ContDiff ℝ ∞ (shear r) := (shearLinear r).contDiff
lemma shear_fderiv (r : ℝ) (y v : Phase) : fderiv ℝ (shear r) y v=shear r v :=
  congrArg (fun A : Phase →L[ℝ] Phase => A v) (shearLinear r).hasFDerivAt.fderiv
lemma shear_inverse (r : ℝ) (y : Phase) : shear (-r) (shear r y)=y := by
  ext i
  fin_cases i <;> simp [shear] <;> ring
lemma shear_contact (r : ℝ) (y v : Phase) :
    phaseRadialContact (shear r y) (shear r v)=phaseRadialContact y v := by
  simp [phaseRadialContact,phaseSymplecticForm,shear]
  ring

def rotatingRaw2 (y : V) : Phase :=
  ![Real.cos (2*Real.pi*y 2),Real.sin (2*Real.pi*y 2),
    -2*(y 0*Real.sin (2*Real.pi*y 2)+y 1*Real.cos (2*Real.pi*y 2)),
    -2*(y 0*Real.cos (2*Real.pi*y 2)-y 1*Real.sin (2*Real.pi*y 2))]
lemma rotatingRaw2_smooth : ContDiff ℝ ∞ rotatingRaw2 := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [rotatingRaw2] <;> fun_prop
lemma shear_rotatingRaw2 (r : ℝ) (y : V) :
    shear r (rotatingRaw2 y)=rotatingRaw2 ![y 0+r,y 1+r,y 2] := by
  ext i
  fin_cases i <;> simp [shear,rotatingRaw2] <;> ring
lemma raw_rotatingJet2 (y : V) : legendrianChartRaw (rotateJet (4*Real.pi) y)=rotatingRaw2 y := by
  have hangle : 4*Real.pi*y 2=2*(2*Real.pi*y 2) := by ring
  have hs := Real.sin_sq_add_cos_sq (2*Real.pi*y 2)
  ext i
  fin_cases i
  · rfl
  · rfl
  · simp [legendrianChartRaw,rotateJet,rotatingRaw2,hangle,Real.sin_two_mul,Real.cos_two_mul]
    field_simp [Real.pi_ne_zero]
    linear_combination -8*y 1*Real.cos (2*Real.pi*y 2)*hs
  · simp [legendrianChartRaw,rotateJet,rotatingRaw2,hangle,Real.sin_two_mul,Real.cos_two_mul]
    field_simp [Real.pi_ne_zero]
    linear_combination -8*y 0*Real.cos (2*Real.pi*y 2)*hs

end
end ContactTopology.EdgeRoundingSphere


namespace BirkhoffGlobalSection.HopfTransport
open BirkhoffGlobalSection Set Filter
open scoped ContDiff Topology
noncomputable section

lemma radiusSq_pos (y : Phase) (hy : y ≠ 0) : 0 < zNormSq y + wNormSq y := by
  by_contra hn
  have hle := le_of_not_gt hn
  unfold zNormSq wNormSq at hle
  apply hy
  ext i
  fin_cases i <;> dsimp <;>
    nlinarith [sq_nonneg (y 0),sq_nonneg (y 1),sq_nonneg (y 2),sq_nonneg (y 3)]

lemma sphere_ne_zero {u : Phase} (hu : u ∈ unitThreeSphere) : u ≠ 0 := by
  intro he
  simpa [he,unitThreeSphere,zNormSq,wNormSq] using hu

lemma normalize_unit {u : Phase} (hu : u ∈ unitThreeSphere) : radialNormalize u = u := by
  change zNormSq u + wNormSq u = 1 at hu
  simp [radialNormalize,hu]

lemma normalize_positive_smul {u : Phase} (hu : u ∈ unitThreeSphere) {r : ℝ} (hr : 0 < r) :
    radialNormalize (r • u) = u := by
  have he : zNormSq (r • u) + wNormSq (r • u) = r^2 := by
    change zNormSq u + wNormSq u = 1 at hu
    simp [zNormSq,wNormSq] at hu ⊢
    nlinarith [sq_nonneg (u 0),sq_nonneg (u 1),sq_nonneg (u 2),sq_nonneg (u 3)]
  simp [radialNormalize,he,Real.sqrt_sq hr.le,smul_smul,inv_mul_cancel₀ hr.ne']


end
end BirkhoffGlobalSection.HopfTransport


namespace BirkhoffGlobalSection.HopfTransport
open BirkhoffGlobalSection Set
open scoped ContDiff
noncomputable section

lemma sphere_dot_self_global {y : Phase} (hy : y ∈ unitThreeSphere) : phaseDot y y = 1 := by
  change zNormSq y + wNormSq y = 1 at hy
  simp [zNormSq,wNormSq,phaseDot] at hy ⊢
  nlinarith

lemma dot_hasDerivAt_global {q g : ℝ → Phase} {v b : Phase} {t : ℝ}
    (hq : HasDerivAt q v t) (hg : HasDerivAt g b t) :
    HasDerivAt (fun s => phaseDot (q s) (g s)) (phaseDot v (g t) + phaseDot (q t) b) t := by
  have h := fun i => hasDerivAt_pi.mp hq i
  have k := fun i => hasDerivAt_pi.mp hg i
  have hd := ((((h 0).mul (k 0)).add ((h 1).mul (k 1))).add ((h 2).mul (k 2))).add ((h 3).mul (k 3))
  apply hd.congr_deriv
  simp only [phaseDot]
  ring

lemma dot_self_hasDerivAt_global {q : ℝ → Phase} {v : Phase} {t : ℝ} (hq : HasDerivAt q v t) :
    HasDerivAt (fun s => phaseDot (q s) (q s)) (2 * phaseDot (q t) v) t := by
  apply (dot_hasDerivAt_global hq hq).congr_deriv
  simp [phaseDot]
  ring

lemma sphere_line_norm_positive (y v : Phase) (hy : y ∈ unitThreeSphere)
    (hv : phaseDot y v = 0) (s : ℝ) :
    0 < zNormSq (y+s•v) + wNormSq (y+s•v) := by
  have hy' := sphere_dot_self_global hy
  have hvv : 0 ≤ phaseDot v v := by
    simp only [phaseDot]
    nlinarith [sq_nonneg (v 0),sq_nonneg (v 1),sq_nonneg (v 2),sq_nonneg (v 3)]
  have he : zNormSq (y+s•v) + wNormSq (y+s•v) = 1 + s^2 * phaseDot v v := by
    simp [zNormSq,wNormSq,phaseDot] at hy' hv ⊢
    linear_combination hy' + (2*s)*hv
  rw [he]
  nlinarith [sq_nonneg s,mul_nonneg (sq_nonneg s) hvv]

lemma sphere_curve_hasDerivAt (y v : Phase) (hy : y ∈ unitThreeSphere)
    (hv : phaseDot y v = 0) :
    HasDerivAt (fun s : ℝ => radialNormalize (y+s•v)) v 0 := by
  have hc : HasDerivAt (fun s : ℝ => y+s•v) v 0 := by
    convert! (hasDerivAt_const (0 : ℝ) y).add ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1 <;> simp
  have hq : HasDerivAt (fun s : ℝ => zNormSq (y+s•v)+wNormSq (y+s•v)) 0 0 := by
    convert! dot_self_hasDerivAt_global hc using 1
    · ext s
      simp [zNormSq,wNormSq,phaseDot,pow_two,add_assoc]
    · simp [hv]
  have hQ : zNormSq y + wNormSq y = 1 := hy
  have hs := hq.sqrt (by simp [hQ])
  have hi := hs.inv (by simp [hQ])
  have hd := hi.smul hc
  convert! hd using 1 <;> simp [radialNormalize,hQ]

lemma sphere_tangent_fderiv_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f g : Phase → E) (y v : Phase)
    (hy : y ∈ unitThreeSphere) (hv : phaseDot y v = 0)
    (hf : DifferentiableAt ℝ f y) (hg : DifferentiableAt ℝ g y)
    (heq : EqOn f g unitThreeSphere) : fderiv ℝ f y v = fderiv ℝ g y v := by
  have hc := sphere_curve_hasDerivAt y v hy hv
  have hfy : DifferentiableAt ℝ f (radialNormalize (y+(0:ℝ)•v)) := by simpa [normalize_unit hy] using hf
  have hgy : DifferentiableAt ℝ g (radialNormalize (y+(0:ℝ)•v)) := by simpa [normalize_unit hy] using hg
  have hdf := hfy.hasFDerivAt.comp_hasDerivAt 0 hc
  have hdg := hgy.hasFDerivAt.comp_hasDerivAt 0 hc
  have hfun : f ∘ (fun s : ℝ => radialNormalize (y+s•v)) = g ∘ (fun s : ℝ => radialNormalize (y+s•v)) := by
    funext s
    exact heq (x := radialNormalize (y+s•v))
      (radial_normalization_contact_identity _ (sphere_line_norm_positive y v hy hv s)).2.1
  rw [hfun] at hdf
  have he := hdf.unique hdg
  simpa [normalize_unit hy] using he

lemma sphere_map_fderiv_tangent (f : Phase → Phase) (y v : Phase)
    (hy : y ∈ unitThreeSphere) (hv : phaseDot y v = 0)
    (hf : DifferentiableAt ℝ f y) (hmap : MapsTo f unitThreeSphere unitThreeSphere) :
    phaseDot (f y) (fderiv ℝ f y v) = 0 := by
  have hc := sphere_curve_hasDerivAt y v hy hv
  have hfy : DifferentiableAt ℝ f (radialNormalize (y+(0:ℝ)•v)) := by simpa [normalize_unit hy] using hf
  have hd := dot_self_hasDerivAt_global (hfy.hasFDerivAt.comp_hasDerivAt 0 hc)
  have heq : (fun s : ℝ => phaseDot (f (radialNormalize (y+s•v))) (f (radialNormalize (y+s•v)))) = fun _ => (1:ℝ) := by
    funext s
    exact sphere_dot_self_global (hmap (radial_normalization_contact_identity _
      (sphere_line_norm_positive y v hy hv s)).2.1)
  change HasDerivAt (fun s : ℝ => phaseDot (f (radialNormalize (y+s•v))) (f (radialNormalize (y+s•v)))) _ 0 at hd
  rw [heq] at hd
  have he := hd.unique (hasDerivAt_const (0:ℝ) (1:ℝ))
  simp [normalize_unit hy] at he
  linarith

end
end BirkhoffGlobalSection.HopfTransport


namespace ContactTopology.SphereContactAlgebra
open BirkhoffGlobalSection BirkhoffGlobalSection.HopfTransport Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma sphere_neg {y : Phase} (hy : y ∈ unitThreeSphere) : -y ∈ unitThreeSphere := by
  simpa [unitThreeSphere,zNormSq,wNormSq] using hy

def compose (F G : EquivariantSphereContactomorphism) : EquivariantSphereContactomorphism where
  toFun := F.toFun ∘ G.toFun
  invFun := G.invFun ∘ F.invFun
  smooth := fun y hy => (F.smooth _ (G.maps_sphere hy)).comp y (G.smooth y hy)
  inv_smooth := fun y hy => (G.inv_smooth _ (F.inv_maps_sphere hy)).comp y (F.inv_smooth y hy)
  maps_sphere := fun y hy => F.maps_sphere (G.maps_sphere hy)
  inv_maps_sphere := fun y hy => G.inv_maps_sphere (F.inv_maps_sphere hy)
  left_inv := by
    intro y hy
    change G.invFun (F.invFun (F.toFun (G.toFun y))) = y
    rw [F.left_inv _ (G.maps_sphere hy),G.left_inv y hy]
  right_inv := by
    intro y hy
    change F.toFun (G.toFun (G.invFun (F.invFun y))) = y
    rw [G.right_inv _ (F.inv_maps_sphere hy),F.right_inv y hy]
  antipodal := by
    intro y hy
    change F.toFun (G.toFun (-y)) = -F.toFun (G.toFun y)
    rw [G.antipodal y hy,F.antipodal _ (G.maps_sphere hy)]
  contact := by
    intro y hy
    obtain ⟨a,ha,hF⟩ := F.contact _ (G.maps_sphere hy)
    obtain ⟨b,hb,hG⟩ := G.contact y hy
    refine ⟨a*b,mul_pos ha hb,?_⟩
    intro v hv
    have htan := sphere_map_fderiv_tangent G.toFun y v hy hv
      ((G.smooth y hy).differentiableAt (by simp)) G.maps_sphere
    have hd := fderiv_comp y ((F.smooth _ (G.maps_sphere hy)).differentiableAt (by simp))
      ((G.smooth y hy).differentiableAt (by simp))
    change phaseRadialContact (F.toFun (G.toFun y)) (fderiv ℝ (F.toFun ∘ G.toFun) y v) = _
    rw [hd]
    change phaseRadialContact (F.toFun (G.toFun y)) (fderiv ℝ F.toFun (G.toFun y) (fderiv ℝ G.toFun y v)) = _
    rw [hF _ htan,hG v hv]
    ring

def inverse (F : EquivariantSphereContactomorphism) : EquivariantSphereContactomorphism where
  toFun := F.invFun
  invFun := F.toFun
  smooth := F.inv_smooth
  inv_smooth := F.smooth
  maps_sphere := F.inv_maps_sphere
  inv_maps_sphere := F.maps_sphere
  left_inv := F.right_inv
  right_inv := F.left_inv
  antipodal := by
    intro y hy
    have hx := F.inv_maps_sphere hy
    calc
      F.invFun (-y) = F.invFun (-F.toFun (F.invFun y)) := by rw [F.right_inv y hy]
      _ = F.invFun (F.toFun (-F.invFun y)) := by rw [F.antipodal _ hx]
      _ = -F.invFun y := F.left_inv _ (sphere_neg hx)
  contact := by
    intro y hy
    have hx := F.inv_maps_sphere hy
    obtain ⟨a,ha,hc⟩ := F.contact _ hx
    refine ⟨a⁻¹,inv_pos.mpr ha,?_⟩
    intro v hv
    have hw := sphere_map_fderiv_tangent F.invFun y v hy hv
      ((F.inv_smooth y hy).differentiableAt (by simp)) F.inv_maps_sphere
    have hdf := (F.smooth _ hx).differentiableAt (by simp)
    have hdi := (F.inv_smooth y hy).differentiableAt (by simp)
    have heq := sphere_tangent_fderiv_eq (F.toFun ∘ F.invFun) id y v hy hv
      (hdf.comp y hdi) differentiableAt_id F.right_inv
    rw [fderiv_comp y hdf hdi] at heq
    have hder : fderiv ℝ F.toFun (F.invFun y) (fderiv ℝ F.invFun y v) = v := by simpa using heq
    have hh := hc (fderiv ℝ F.invFun y v) hw
    rw [F.right_inv y hy,hder] at hh
    calc
      phaseRadialContact (F.invFun y) (fderiv ℝ F.invFun y v) = phaseRadialContact y v/a :=
        (eq_div_iff ha.ne').mpr (by nlinarith [hh])
      _ = _ := by ring

def isotopy_congr (F G : EquivariantSphereContactomorphism)
    (I : EquivariantSphereContactIsotopy F)
    (heq : ∀ y ∈ unitThreeSphere, F.toFun y = G.toFun y) :
    EquivariantSphereContactIsotopy G where
  slice := I.slice
  smooth := I.smooth
  start := I.start
  finish := fun y hy => (I.finish y hy).trans (heq y hy)

def isotopy_compose (F G : EquivariantSphereContactomorphism)
    (I : EquivariantSphereContactIsotopy F) (J : EquivariantSphereContactIsotopy G) :
    EquivariantSphereContactIsotopy (compose F G) where
  slice := fun t => compose (I.slice t) (J.slice t)
  smooth := by
    intro t ht y hy
    have hxy := (J.slice t).maps_sphere hy
    exact (I.smooth t ht _ hxy).comp (t,y) (contDiffAt_fst.prodMk (J.smooth t ht y hy))
  start := by
    intro y hy
    change (I.slice 0).toFun ((J.slice 0).toFun y) = y
    rw [J.start y hy,I.start y hy]
  finish := by
    intro y hy
    change (I.slice 1).toFun ((J.slice 1).toFun y) = F.toFun (G.toFun y)
    rw [I.finish _ ((J.slice 1).maps_sphere hy),J.finish y hy]

/-- Reversing the path and composing with the fixed endpoint inverse avoids
assuming joint smoothness of the inverses of an arbitrary isotopy. -/
def isotopy_inverse (F : EquivariantSphereContactomorphism)
    (I : EquivariantSphereContactIsotopy F) : EquivariantSphereContactIsotopy (inverse F) where
  slice := fun t => compose (inverse F) (I.slice (1-t))
  smooth := by
    intro t ht y hy
    have hs : 1-t ∈ Icc (0:ℝ) 1 := ⟨by linarith [ht.2],by linarith [ht.1]⟩
    have hclock : ContDiffAt ℝ ∞ (fun q : ℝ × Phase => (1-q.1,q.2)) (t,y) :=
      (contDiffAt_const.sub contDiffAt_fst).prodMk contDiffAt_snd
    have hI := (I.smooth (1-t) hs y hy).comp (t,y) hclock
    exact (F.inv_smooth _ ((I.slice (1-t)).maps_sphere hy)).comp (t,y) hI
  start := by
    intro y hy
    change F.invFun ((I.slice (1-0)).toFun y) = y
    rw [sub_zero,I.finish y hy,F.left_inv y hy]
  finish := by
    intro y hy
    change F.invFun ((I.slice (1-1)).toFun y) = F.invFun y
    rw [sub_self,I.start y hy]

end
end ContactTopology.SphereContactAlgebra


namespace ContactTopology.EdgeRoundingSphere
open BirkhoffGlobalSection BirkhoffGlobalSection.HopfTransport Set Function
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma normalize_scale (a : ℝ) (ha : 0 < a) (y : Phase) :
    radialNormalize (a • y)=radialNormalize y := by
  have hQ : zNormSq (a • y)+wNormSq (a • y)=a^2*(zNormSq y+wNormSq y) := by
    simp [zNormSq,wNormSq]
    ring
  simp [radialNormalize,hQ,Real.sqrt_mul (sq_nonneg a),Real.sqrt_sq ha.le,
    mul_inv_rev,smul_smul,ha.ne']

lemma shear_nonzero (r : ℝ) (y : Phase) (hy : y ≠ 0) : shear r y ≠ 0 := by
  intro h
  apply hy
  have hh := congrArg (shear (-r)) h
  rw [shear_inverse] at hh
  exact hh.trans (by ext i; fin_cases i <;> simp [shear])

lemma shear_normalize (r : ℝ) (y : Phase) :
    shear r (radialNormalize y)=
      (Real.sqrt (zNormSq y+wNormSq y))⁻¹ • shear r y :=
  (shearLinear r).map_smul _ _

def normalizedShear (r : ℝ) : Phase → Phase := radialNormalize ∘ shear r

lemma normalizedShear_smooth (r : ℝ) (y : Phase) (hy : y ≠ 0) :
    ContDiffAt ℝ ∞ (normalizedShear r) y :=
  ((radial_normalization_contact_identity _ (radiusSq_pos _ (shear_nonzero r y hy))).1).comp y
    (shear_smooth r).contDiffAt
lemma normalizedShear_mem (r : ℝ) (y : Phase) (hy : y ≠ 0) :
    normalizedShear r y ∈ unitThreeSphere :=
  (radial_normalization_contact_identity _ (radiusSq_pos _ (shear_nonzero r y hy))).2.1
lemma normalizedShear_inverse (r : ℝ) (y : Phase) (hy : y ∈ unitThreeSphere) :
    normalizedShear (-r) (normalizedShear r y)=y := by
  change radialNormalize (shear (-r) (radialNormalize (shear r y)))=y
  rw [shear_normalize,shear_inverse,normalize_scale _ (inv_pos.mpr (Real.sqrt_pos.mpr
    (radiusSq_pos _ (shear_nonzero r y (sphere_ne_zero hy))))),normalize_unit hy]
lemma normalizedShear_contact (r : ℝ) (y v : Phase) (hy : y ≠ 0) :
    phaseRadialContact (normalizedShear r y) (fderiv ℝ (normalizedShear r) y v)=
      (zNormSq (shear r y)+wNormSq (shear r y))⁻¹*phaseRadialContact y v := by
  have hN := radial_normalization_contact_identity (shear r y) (radiusSq_pos _ (shear_nonzero r y hy))
  change phaseRadialContact (radialNormalize (shear r y)) (fderiv ℝ (radialNormalize ∘ shear r) y v)=_
  rw [fderiv_comp y (hN.1.differentiableAt (by simp)) ((shear_smooth r).differentiable (by simp) y)]
  change phaseRadialContact (radialNormalize (shear r y))
    (fderiv ℝ radialNormalize (shear r y) (fderiv ℝ (shear r) y v))=_
  rw [hN.2.2.2,shear_fderiv,shear_contact]
  ring

def shearContactomorphism (r : ℝ) : EquivariantSphereContactomorphism where
  toFun := normalizedShear r
  invFun := normalizedShear (-r)
  smooth := fun y hy => normalizedShear_smooth r y (sphere_ne_zero hy)
  inv_smooth := fun y hy => normalizedShear_smooth (-r) y (sphere_ne_zero hy)
  maps_sphere := fun y hy => normalizedShear_mem r y (sphere_ne_zero hy)
  inv_maps_sphere := fun y hy => normalizedShear_mem (-r) y (sphere_ne_zero hy)
  left_inv := normalizedShear_inverse r
  right_inv := by simpa using normalizedShear_inverse (-r)
  antipodal := by
    intro y hy
    change radialNormalize (shear r (-y)) = -radialNormalize (shear r y)
    have he : shear r (-y) = -shear r y := (shearLinear r).map_neg y
    rw [he]
    exact (radial_normalization_contact_identity _ (radiusSq_pos _
      (shear_nonzero r y (sphere_ne_zero hy)))).2.2.1
  contact := by
    intro y hy
    refine ⟨_,inv_pos.mpr (radiusSq_pos _ (shear_nonzero r y (sphere_ne_zero hy))),?_⟩
    intro v hv
    exact normalizedShear_contact r y v (sphere_ne_zero hy)

lemma normalizedShear_rotating (r : ℝ) (y : V) :
    normalizedShear r (legendrianSphereChart (rotateJet (4*Real.pi) y))=
      legendrianSphereChart (rotateJet (4*Real.pi) ![y 0+r,y 1+r,y 2]) := by
  change radialNormalize (shear r (radialNormalize (legendrianChartRaw (rotateJet (4*Real.pi) y))))=_
  rw [shear_normalize,normalize_scale _ (inv_pos.mpr (Real.sqrt_pos.mpr
    (legendrianChartRaw_radius_positive _))),raw_rotatingJet2,shear_rotatingRaw2]
  change _=radialNormalize (legendrianChartRaw (rotateJet (4*Real.pi) _))
  rw [raw_rotatingJet2]

end
end ContactTopology.EdgeRoundingSphere


namespace ContactTopology.EdgeRoundingSphere
open BirkhoffGlobalSection ContactTopology.ConvexCore Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

def translateNormal (r : ℝ) (y : V) : V := ![y 0+r,y 1+r,y 2]
lemma translateNormal_smooth (r : ℝ) : ContDiff ℝ ∞ (translateNormal r) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [translateNormal] <;> fun_prop
lemma translateNormal_fderiv (r : ℝ) (y : V) :
    fderiv ℝ (translateNormal r) y=ContinuousLinearMap.id ℝ V := by
  have he : translateNormal r = fun z : V => z+![r,r,0] := by
    ext z i
    fin_cases i <;> simp [translateNormal]
  rw [he]
  simpa using ((hasFDerivAt_id y).add_const (![r,r,0]:V)).fderiv
lemma translateNormal_inverse (r : ℝ) (y : V) :
    translateNormal r (translateNormal (-r) y)=y := by
  ext i
  fin_cases i <;> simp [translateNormal]

lemma rotateJet_euler (freq : ℝ) (y : V) :
    fderiv ℝ (rotateJet freq) y ![y 0,y 1,0]=normalEuler (rotateJet freq y) := by
  rw [rotateJet_fderiv]
  ext i
  fin_cases i <;> dsimp [normalEuler,rotateJet] <;> ring
lemma cover_euler (F : EquivariantSphereContactomorphism) (freq : ℝ) (y : V) :
    transportedEuler F (cover F freq y)=fderiv ℝ (cover F freq) y ![y 0,y 1,0] := by
  rw [cover,Function.comp_apply,transportedEuler_chart]
  rw [fderiv_comp y ((imageChart_contDiff F).differentiable (by simp) _)
    ((rotateJet_smooth freq).differentiable (by simp) _)]
  change _=fderiv ℝ (imageChart F) (rotateJet freq y) (fderiv ℝ (rotateJet freq) y _)
  rw [rotateJet_euler]

def shiftedContact (F : EquivariantSphereContactomorphism) (r : ℝ) : EquivariantSphereContactomorphism :=
  SphereContactAlgebra.compose F (shearContactomorphism r)
lemma cover_shifted (F : EquivariantSphereContactomorphism) (r : ℝ) (y : V) :
    cover (shiftedContact F r) (4*Real.pi) y=cover F (4*Real.pi) (translateNormal r y) := by
  change F.toFun (normalizedShear r (legendrianSphereChart (rotateJet (4*Real.pi) y)))=_
  rw [normalizedShear_rotating]
  rfl

def centeredField (F : EquivariantSphereContactomorphism) (r : ℝ) : Phase → Phase :=
  transportedEuler (shiftedContact F r)
lemma centeredField_smooth (F : EquivariantSphereContactomorphism) (r : ℝ) (y : Phase)
    (hy : y ∈ unitThreeSphere) : ContDiffAt ℝ ∞ (centeredField F r) y :=
  transportedEuler_smooth _ y hy
lemma centeredField_cover (F : EquivariantSphereContactomorphism) (r : ℝ) (y : V) :
    centeredField F r (cover F (4*Real.pi) y)=
      fderiv ℝ (cover F (4*Real.pi)) y (ContactTopology.EdgeRounding.field r y) := by
  let z := translateNormal (-r) y
  have he : translateNormal r z=y := translateNormal_inverse r y
  have hcover : cover (shiftedContact F r) (4*Real.pi) = cover F (4*Real.pi) ∘ translateNormal r :=
    funext (cover_shifted F r)
  have hh := cover_euler (shiftedContact F r) (4*Real.pi) z
  rw [cover_shifted,he] at hh
  rw [hcover,fderiv_comp z ((cover_smooth F _).differentiable (by simp) _)
    ((translateNormal_smooth r).differentiable (by simp) _),translateNormal_fderiv] at hh
  change transportedEuler (shiftedContact F r) (cover F (4*Real.pi) y)=
    fderiv ℝ (cover F (4*Real.pi)) (translateNormal r z) ![z 0,z 1,0] at hh
  have hz : ![z 0,z 1,0]=ContactTopology.EdgeRounding.field r y := by
    ext i
    fin_cases i <;> simp [z,translateNormal,ContactTopology.EdgeRounding.field,sub_eq_add_neg]
  rw [he,hz] at hh
  exact hh
lemma centeredField_tangent (F : EquivariantSphereContactomorphism) (r : ℝ) (y : V) :
    phaseDot (cover F (4*Real.pi) y) (centeredField F r (cover F (4*Real.pi) y))=0 := by
  have he : cover F (4*Real.pi) y=cover (shiftedContact F r) (4*Real.pi) (translateNormal (-r) y) := by
    rw [cover_shifted,translateNormal_inverse]
  rw [he]
  exact transportedEuler_tangent _ _

lemma centeredField_is_contact (F : EquivariantSphereContactomorphism) (r : ℝ) (y : V) :
    ∃ a : ℝ, ∀ w : Phase, phaseDot (cover F (4*Real.pi) y) w=0 →
      phaseRadialContact (centeredField F r (cover F (4*Real.pi) y)) w+
        phaseRadialContact (cover F (4*Real.pi) y)
          (fderiv ℝ (centeredField F r) (cover F (4*Real.pi) y) w)=
            a*phaseRadialContact (cover F (4*Real.pi) y) w := by
  have he : cover F (4*Real.pi) y=cover (shiftedContact F r) (4*Real.pi) (translateNormal (-r) y) := by
    rw [cover_shifted,translateNormal_inverse]
  rw [he]
  exact transportedEuler_is_contact _ _

lemma shift_fderiv (t : ℝ) (y : V) : fderiv ℝ (shift t) y=ContinuousLinearMap.id ℝ V := by
  have he : shift t = fun z : V => z+![0,0,t] := by
    ext z i
    fin_cases i <;> simp [shift]
  rw [he]
  simpa using ((hasFDerivAt_id y).add_const (![0,0,t]:V)).fderiv
lemma shift_smooth (t : ℝ) : ContDiff ℝ ∞ (shift t) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [shift] <;> fun_prop
lemma cover_antipodal_derivative (F : EquivariantSphereContactomorphism) (y v : V) :
    fderiv ℝ (cover F (4*Real.pi)) (shift (1/2) y) v=
      -fderiv ℝ (cover F (4*Real.pi)) y v := by
  have he : cover F (4*Real.pi) ∘ shift (1/2) = fun z => -cover F (4*Real.pi) z :=
    funext (cover_antipodal F)
  have hh := congrArg (fun f : V → Phase => fderiv ℝ f y) he
  have hn : HasFDerivAt (fun z => -cover F (4*Real.pi) z)
      (-fderiv ℝ (cover F (4*Real.pi)) y) y :=
    ((cover_smooth F _).differentiable (by simp) y).hasFDerivAt.neg
  rw [fderiv_comp y ((cover_smooth F _).differentiable (by simp) _)
    ((shift_smooth _).differentiable (by simp) _),shift_fderiv,hn.fderiv] at hh
  have hv := congrArg (fun A : V →L[ℝ] Phase => A v) hh
  simpa using hv
lemma centeredField_odd_on_cover (F : EquivariantSphereContactomorphism) (r : ℝ) (y : V) :
    centeredField F r (-cover F (4*Real.pi) y)= -centeredField F r (cover F (4*Real.pi) y) := by
  rw [← cover_antipodal F y,centeredField_cover,centeredField_cover]
  change fderiv ℝ (cover F (4*Real.pi)) (shift (1/2) y) _=_
  rw [cover_antipodal_derivative]
  congr 1

end
end ContactTopology.EdgeRoundingSphere



namespace ContactTopology.EdgeRounding
open Set Function Filter
open scoped ContDiff Topology Interval
set_option backward.isDefEq.respectTransparency false
noncomputable section

def bendAngle (s : ℝ) : ℝ := Real.pi/2*Real.smoothTransition s
def speed (s : ℝ) : ℝ := Real.sin (bendAngle s)
def bendX (s : ℝ) : ℝ := ∫ t in (0:ℝ)..s, speed t
def bendC : ℝ := bendX 1

lemma bendAngle_smooth : ContDiff ℝ ∞ bendAngle :=
  contDiff_const.mul Real.smoothTransition.contDiff
lemma speed_smooth : ContDiff ℝ ∞ speed := bendAngle_smooth.sin
lemma transition_reflect (s : ℝ) : Real.smoothTransition (1-s)=1-Real.smoothTransition s := by
  unfold Real.smoothTransition
  rw [show 1-(1-s)=s by ring]
  field_simp [(Real.smoothTransition.pos_denom s).ne',
    show expNegInvGlue (1-s)+expNegInvGlue s ≠ 0 by
      simpa only [add_comm] using (Real.smoothTransition.pos_denom s).ne']
  ring
lemma bendAngle_reflect (s : ℝ) : bendAngle (1-s)=Real.pi/2-bendAngle s := by
  simp only [bendAngle,transition_reflect]
  ring
lemma speed_reflect (s : ℝ) : speed (1-s)=Real.cos (bendAngle s) := by
  rw [speed,bendAngle_reflect,Real.sin_pi_div_two_sub]
lemma speed_sq (s : ℝ) : speed s^2+speed (1-s)^2=1 := by
  rw [speed_reflect]
  exact Real.sin_sq_add_cos_sq _
lemma bendAngle_mem (s : ℝ) : bendAngle s ∈ Icc (0:ℝ) (Real.pi/2) := by
  constructor
  · exact mul_nonneg (by positivity) (Real.smoothTransition.nonneg s)
  · exact mul_le_of_le_one_right (by positivity) (Real.smoothTransition.le_one s)
lemma speed_nonneg (s : ℝ) : 0 ≤ speed s :=
  Real.sin_nonneg_of_nonneg_of_le_pi (bendAngle_mem s).1
    ((bendAngle_mem s).2.trans (by linarith [Real.pi_pos]))
lemma speed_pos (s : ℝ) (hs : 0 < s) : 0 < speed s := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · exact mul_pos (by positivity) (Real.smoothTransition.pos_of_pos hs)
  · exact lt_of_le_of_lt (bendAngle_mem s).2 (by linarith [Real.pi_pos])
lemma speed_zero (s : ℝ) (hs : s ≤ 0) : speed s=0 := by
  simp [speed,bendAngle,Real.smoothTransition.zero_of_nonpos hs]
lemma speed_one (s : ℝ) (hs : 1 ≤ s) : speed s=1 := by
  simp [speed,bendAngle,Real.smoothTransition.one_of_one_le hs]
lemma bendX_deriv (s : ℝ) : HasDerivAt bendX (speed s) s :=
  intervalIntegral.integral_hasDerivAt_right (speed_smooth.continuous.intervalIntegrable 0 s)
    speed_smooth.continuous.stronglyMeasurable.stronglyMeasurableAtFilter speed_smooth.continuous.continuousAt
@[fun_prop] lemma bendX_smooth : ContDiff ℝ ∞ bendX := by
  rw [contDiff_infty]
  intro n
  cases n with
  | zero => exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr (fun s => (bendX_deriv s).continuousAt))
  | succ n =>
    have hd : deriv bendX=speed := funext (fun s => (bendX_deriv s).deriv)
    apply (contDiff_succ_iff_deriv (𝕜 := ℝ) (f := bendX) (n := (n:ℕ∞ω))).mpr
    refine ⟨fun s => (bendX_deriv s).differentiableAt,by simp,?_⟩
    rw [hd]
    exact speed_smooth.of_le (by exact_mod_cast le_top)
lemma bendX_zero : bendX 0=0 := by simp [bendX]
lemma bendX_mono : Monotone bendX :=
  monotone_of_deriv_nonneg (fun s => (bendX_deriv s).differentiableAt)
    (fun s => by rw [(bendX_deriv s).deriv]; exact speed_nonneg s)
lemma bendX_strict : StrictMonoOn bendX (Ici (0:ℝ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0) bendX_smooth.continuous.continuousOn
  intro s hs
  rw [(bendX_deriv s).deriv]
  apply speed_pos
  simpa only [interior_Ici,mem_Ioi] using hs
lemma bendC_pos : 0 < bendC := by
  have hh := bendX_strict (show (0:ℝ) ∈ Ici 0 by simp) (show (1:ℝ) ∈ Ici 0 by norm_num) zero_lt_one
  simpa only [bendX_zero,bendC] using hh
lemma bendX_nonpos (s : ℝ) (hs : s ≤ 0) : bendX s=0 := by
  change (∫ t in (0:ℝ)..s, speed t)=0
  calc
    (∫ t in (0:ℝ)..s, speed t)=(∫ t in (0:ℝ)..s, (0:ℝ)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_ge hs] at ht
      exact speed_zero t ht.2
    _=0 := by simp

lemma bendX_one_le (s : ℝ) (hs : 1 ≤ s) : bendX s=bendC+s-1 := by
  have heq : (∫ t in (1:ℝ)..s, speed t)=s-1 := by
    calc
      (∫ t in (1:ℝ)..s, speed t)=(∫ t in (1:ℝ)..s, (1:ℝ)) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hs] at ht
        exact speed_one t ht.1
      _=s-1 := by simp
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (speed_smooth.continuous.intervalIntegrable (μ := MeasureTheory.volume) (0:ℝ) 1)
    (speed_smooth.continuous.intervalIntegrable (μ := MeasureTheory.volume) (1:ℝ) s)
  change bendC+(∫ t in (1:ℝ)..s, speed t)=bendX s at hadd
  rw [heq] at hadd
  linarith
lemma bendX_nonneg (s : ℝ) : 0 ≤ bendX s := by
  by_cases hs : s ≤ 0
  · rw [bendX_nonpos s hs]
  · simpa only [bendX_zero] using bendX_mono (le_of_not_ge hs)
lemma bendX_lt (s : ℝ) (hs : s < 1) : bendX s < bendC := by
  by_cases hz : s ≤ 0
  · rw [bendX_nonpos s hz]; exact bendC_pos
  · exact bendX_strict (le_of_not_ge hz) (show (1:ℝ) ∈ Ici 0 by norm_num) hs

def flatRounded (r : ℝ) (p : ℝ × ℝ) : V := ![r*bendX p.1,r*bendX (1-p.1),p.2]
lemma flatRounded_smooth (r : ℝ) : ContDiff ℝ ∞ (flatRounded r) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [flatRounded] <;> fun_prop

end
end ContactTopology.EdgeRounding


namespace ContactTopology.EdgeRounding
open Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma flatRounded_fderiv (r : ℝ) (p v : ℝ × ℝ) :
    fderiv ℝ (flatRounded r) p v=![r*speed p.1*v.1,-r*speed (1-p.1)*v.1,v.2] := by
  have hD : HasFDerivAt (flatRounded r) (ContinuousLinearMap.pi
      ![(r*speed p.1) • ContinuousLinearMap.fst ℝ ℝ ℝ,
        (-r*speed (1-p.1)) • ContinuousLinearMap.fst ℝ ℝ ℝ,
        ContinuousLinearMap.snd ℝ ℝ ℝ]) p := by
    apply hasFDerivAt_pi.mpr
    intro i
    fin_cases i
    · convert! ((bendX_deriv p.1).comp_hasFDerivAt p
        (hasFDerivAt_fst (𝕜 := ℝ) (p := p))).const_mul r using 1 <;> ext w <;> simp
    · convert! ((bendX_deriv (1-p.1)).comp_hasFDerivAt p
        ((hasFDerivAt_const (𝕜 := ℝ) (1:ℝ) p).sub hasFDerivAt_fst)).const_mul r using 1 <;>
        ext w <;> simp <;> ring
    · exact hasFDerivAt_snd
  rw [hD.fderiv]
  ext i
  fin_cases i <;> simp

lemma flatRounded_immersion (r : ℝ) (hr : 0 < r) (p : ℝ × ℝ) :
    Injective (fderiv ℝ (flatRounded r) p) := by
  intro v w h
  rw [flatRounded_fderiv,flatRounded_fderiv] at h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 : v.2=w.2 := congrFun h 2
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one] at h0 h1
  have he : v.1=w.1 := by
    by_cases hs : speed p.1=0
    · have hc : speed (1-p.1) ≠ 0 := by intro hc; have hi := speed_sq p.1; simp [hs,hc] at hi
      exact mul_left_cancel₀ (mul_ne_zero (neg_ne_zero.mpr hr.ne') hc) h1
    · exact mul_left_cancel₀ (mul_ne_zero hr.ne' hs) h0
  exact Prod.ext he h2

lemma bend_difference_deriv (s : ℝ) : HasDerivAt (fun t => bendX t-bendX (1-t))
    (speed s+speed (1-s)) s := by
  convert! (bendX_deriv s).sub ((bendX_deriv (1-s)).comp s
    ((hasDerivAt_const s (1:ℝ)).sub (hasDerivAt_id s))) using 1 <;> simp
lemma bend_difference_strict : StrictMono (fun s => bendX s-bendX (1-s)) := by
  apply strictMono_of_deriv_pos
  intro s
  rw [(bend_difference_deriv s).deriv]
  have hs := speed_sq s
  have ha := speed_nonneg s
  have hb := speed_nonneg (1-s)
  nlinarith
lemma flatRounded_injective (r : ℝ) (hr : 0 < r) : Injective (flatRounded r) := by
  rintro ⟨s,z⟩ ⟨t,w⟩ heq
  have h0 : r*bendX s=r*bendX t := congrFun heq 0
  have h1 : r*bendX (1-s)=r*bendX (1-t) := congrFun heq 1
  have h2 : z=w := congrFun heq 2
  have hst : s=t := bend_difference_strict.injective (by
    rw [mul_left_cancel₀ hr.ne' h0,mul_left_cancel₀ hr.ne' h1])
  exact Prod.ext hst h2

lemma flatRounded_left (r s z : ℝ) (hs : s ≤ 0) :
    flatRounded r (s,z)=![0,r*(bendC-s),z] := by
  have h1 : 1 ≤ 1-s := by linarith
  simp only [flatRounded,bendX_nonpos s hs,bendX_one_le (1-s) h1,mul_zero]
  congr 2
  ring
lemma flatRounded_right (r s z : ℝ) (hs : 1 ≤ s) :
    flatRounded r (s,z)=![r*(bendC+s-1),0,z] := by
  have h1 : 1-s ≤ 0 := by linarith
  simp only [flatRounded,bendX_nonpos (1-s) h1,bendX_one_le s hs,mul_zero]

def bendA (s : ℝ) : ℝ := bendC-bendX s
def bendB (s : ℝ) : ℝ := bendC-bendX (1-s)
lemma bendA_pos (s : ℝ) (hs : s < 1) : 0 < bendA s := sub_pos.mpr (bendX_lt s hs)
lemma bendB_pos (s : ℝ) (hs : 0 < s) : 0 < bendB s := bendA_pos (1-s) (by linarith)
lemma bendA_nonneg (s : ℝ) (hs : s ≤ 1) : 0 ≤ bendA s :=
  sub_nonneg.mpr (bendX_mono hs)
lemma bendB_nonneg (s : ℝ) (hs : 0 ≤ s) : 0 ≤ bendB s := bendA_nonneg (1-s) (by linarith)
lemma flat_weight_pos (s : ℝ) : 0 < bendA s*speed (1-s)+bendB s*speed s := by
  by_cases hs0 : s ≤ 0
  · have href : 1 ≤ 1-s := by linarith
    simp only [speed_zero s hs0,speed_one (1-s) href,mul_zero,add_zero,mul_one,bendA,bendX_nonpos s hs0,sub_zero]
    exact bendC_pos
  by_cases hs1 : 1 ≤ s
  · have href : 1-s ≤ 0 := by linarith
    simp only [speed_one s hs1,speed_zero (1-s) href,mul_zero,zero_add,mul_one,bendB,bendX_nonpos (1-s) href,sub_zero]
    exact bendC_pos
  have ha : 0 < bendA s*speed (1-s) :=
    mul_pos (bendA_pos s (lt_of_not_ge hs1)) (speed_pos _ (by linarith))
  have hb : 0 ≤ bendB s*speed s :=
    mul_nonneg (bendB_pos s (lt_of_not_ge hs0)).le (speed_nonneg s)
  exact add_pos_of_pos_of_nonneg ha hb

lemma flatRounded_transverse (r : ℝ) (hr : 0 < r) (p v : ℝ × ℝ) :
    field (r*bendC) (flatRounded r p) ≠ fderiv ℝ (flatRounded r) p v := by
  intro heq
  rw [flatRounded_fderiv] at heq
  have h0 := congrFun heq 0
  have h1 := congrFun heq 1
  simp only [flatRounded,field,Matrix.cons_val_zero,Matrix.cons_val_one] at h0 h1
  have hh : r*(bendA p.1*speed (1-p.1)+bendB p.1*speed p.1)=0 := by
    dsimp only [bendA,bendB]
    linear_combination -speed (1-p.1)*h0-speed p.1*h1
  have hp := mul_pos hr (flat_weight_pos p.1)
  linarith

lemma flatRounded_contact_value (freq r : ℝ) (p : ℝ × ℝ) :
    α freq (flatRounded r p) (field (r*bendC) (flatRounded r p)) =
      -r*(bendA p.1*Real.sin (freq*p.2)+bendB p.1*Real.cos (freq*p.2)) := by
  simp [α,flatRounded,field,bendA,bendB]
  ring

end
end ContactTopology.EdgeRounding


namespace ContactTopology.EdgeRounding
open Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

@[fun_prop] lemma bendA_smooth : ContDiff ℝ ∞ bendA := contDiff_const.sub bendX_smooth
@[fun_prop] lemma bendB_smooth : ContDiff ℝ ∞ bendB :=
  contDiff_const.sub (bendX_smooth.comp (contDiff_const.sub contDiff_id))

def bendPhase (s : ℝ) : ℝ := if s < 1/2 then Real.arctan (bendB s/bendA s)
  else Real.pi/2-Real.arctan (bendA s/bendB s)
lemma arctan_bend_complement (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    Real.arctan (bendA s/bendB s)=Real.pi/2-Real.arctan (bendB s/bendA s) := by
  have h := Real.arctan_inv_of_pos (div_pos (bendB_pos s hs0) (bendA_pos s hs1))
  simpa only [inv_div] using h
lemma bendPhase_left (s : ℝ) (hs : s < 1) :
    bendPhase s=Real.arctan (bendB s/bendA s) := by
  unfold bendPhase
  split_ifs with h
  · rfl
  · have hi := arctan_bend_complement s (by linarith) hs
    linarith
lemma bendPhase_right (s : ℝ) (hs : 0 < s) :
    bendPhase s=Real.pi/2-Real.arctan (bendA s/bendB s) := by
  unfold bendPhase
  split_ifs with h
  · have hi := arctan_bend_complement s hs (by linarith)
    linarith
  · rfl
lemma bendPhase_smooth : ContDiff ℝ ∞ bendPhase := by
  rw [contDiff_iff_contDiffAt]
  intro s
  by_cases hs : s < 1
  · have hf : ContDiffAt ℝ ∞ (fun t => Real.arctan (bendB t/bendA t)) s :=
      (bendB_smooth.contDiffAt.div bendA_smooth.contDiffAt (bendA_pos s hs).ne').arctan
    apply hf.congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hs] with t ht
    exact bendPhase_left t ht
  · have hpos : 0 < s := by linarith
    have hf : ContDiffAt ℝ ∞ (fun t => Real.pi/2-Real.arctan (bendA t/bendB t)) s :=
      contDiffAt_const.sub
        ((bendA_smooth.contDiffAt.div bendB_smooth.contDiffAt (bendB_pos s hpos).ne').arctan)
    apply hf.congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hpos] with t ht
    exact bendPhase_right t ht
lemma bendPhase_zero : bendPhase 0=0 := by
  rw [bendPhase_left 0 (by norm_num)]
  simp [bendB,bendC]
lemma bendPhase_one : bendPhase 1=Real.pi/2 := by
  rw [bendPhase_right 1 (by norm_num)]
  simp [bendA,bendC]

lemma bend_combination_zero (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) (x : ℝ) :
    bendA s*Real.sin x+bendB s*Real.cos x=0 ↔ Real.sin (x+bendPhase s)=0 := by
  by_cases hs1 : s < 1
  · have hA : bendA s ≠ 0 := (bendA_pos s hs1).ne'
    have hcos : Real.cos (bendPhase s) ≠ 0 := by
      rw [bendPhase_left s hs1]
      exact (Real.cos_arctan_pos _).ne'
    have htan : Real.sin (bendPhase s)=(bendB s/bendA s)*Real.cos (bendPhase s) := by
      rw [bendPhase_left s hs1]
      have ht := Real.tan_arctan (bendB s/bendA s)
      rw [Real.tan_eq_sin_div_cos] at ht
      exact (div_eq_iff (Real.cos_arctan_pos _).ne').mp ht
    have he : bendA s*Real.sin (x+bendPhase s)=
        Real.cos (bendPhase s)*(bendA s*Real.sin x+bendB s*Real.cos x) := by
      rw [Real.sin_add,htan]
      field_simp [hA]
    constructor
    · intro hz
      have hh : bendA s*Real.sin (x+bendPhase s)=0 := by rw [he,hz,mul_zero]
      exact (mul_eq_zero.mp hh).resolve_left hA
    · intro hz
      have hh : Real.cos (bendPhase s)*(bendA s*Real.sin x+bendB s*Real.cos x)=0 := by
        rw [← he,hz,mul_zero]
      exact (mul_eq_zero.mp hh).resolve_left hcos
  · have hs_eq : s=1 := le_antisymm hs.2 (le_of_not_gt hs1)
    subst s
    have hA : bendA 1=0 := by simp [bendA,bendC]
    have hB : bendB 1=bendC := by simp [bendB,bendX_zero]
    simp only [hA,hB,zero_mul,zero_add,bendPhase_one,Real.sin_add_pi_div_two,mul_eq_zero,bendC_pos.ne',false_or]

lemma flatRounded_dividing_iff (freq r : ℝ) (hfreq : 0 < freq) (hr : 0 < r)
    (s z : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
    α freq (flatRounded r (s,z)) (field (r*bendC) (flatRounded r (s,z)))=0 ↔
      ∃ k : ℤ, z=k*Real.pi/freq-bendPhase s/freq := by
  rw [flatRounded_contact_value,mul_eq_zero]
  simp only [neg_eq_zero,hr.ne',false_or]
  rw [bend_combination_zero s hs,Real.sin_eq_zero_iff]
  constructor
  · rintro ⟨k,hk⟩
    refine ⟨k,?_⟩
    rw [← sub_div]
    apply (eq_div_iff hfreq.ne').mpr
    linarith
  · rintro ⟨k,hk⟩
    refine ⟨k,?_⟩
    rw [hk]
    field_simp [hfreq.ne']
    ring

def flatCurve (freq r : ℝ) (k : ℤ) (s : ℝ) : V :=
  flatRounded r (s,k*Real.pi/freq-bendPhase s/freq)
lemma flatCurve_smooth (freq r : ℝ) (k : ℤ) : ContDiff ℝ ∞ (flatCurve freq r k) :=
  (flatRounded_smooth r).comp (contDiff_id.prodMk (contDiff_const.sub (bendPhase_smooth.div_const freq)))
lemma flatCurve_regular (freq r : ℝ) (hr : 0 < r) (k : ℤ) (s : ℝ) :
    deriv (flatCurve freq r k) s ≠ 0 := by
  let h : ℝ → ℝ × ℝ := fun t => (t,k*Real.pi/freq-bendPhase t/freq)
  have hd : HasDerivAt h (1,-(deriv bendPhase s/freq)) s := by
    convert! (hasDerivAt_id s).prodMk
      ((hasDerivAt_const s (k*Real.pi/freq)).sub
        ((bendPhase_smooth.differentiable (by simp) s).hasDerivAt.div_const freq)) using 1 <;> simp
  have hc := ((flatRounded_smooth r).differentiable (by simp) (h s)).hasFDerivAt.comp_hasDerivAt s hd
  change HasDerivAt (flatCurve freq r k) _ s at hc
  rw [hc.deriv]
  intro hz
  have heq : fderiv ℝ (flatRounded r) (h s) (1,-(deriv bendPhase s/freq))=
      fderiv ℝ (flatRounded r) (h s) (0 : ℝ × ℝ) := by simpa only [map_zero] using hz
  have hh := (flatRounded_immersion r hr (h s)) heq
  have hh0 := congrArg Prod.fst hh
  norm_num at hh0

lemma flatCurve_endpoints (n : ℕ) (hn : 0 < n) (r : ℝ) (k : ℤ) :
    flatCurve (2*Real.pi*n) r k 0=![0,r*bendC,(k:ℝ)/(2*n)] ∧
    flatCurve (2*Real.pi*n) r k 1=![r*bendC,0,(k:ℝ)/(2*n)-1/(4*n)] := by
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have h0 : (k:ℝ)*Real.pi/(2*Real.pi*n)=(k:ℝ)/(2*n) := by field_simp [Real.pi_ne_zero,hn0]
  have h1 : (Real.pi/2)/(2*Real.pi*n)=1/(4*n) := by field_simp [Real.pi_ne_zero,hn0]; ring
  constructor
  · simp only [flatCurve,bendPhase_zero,zero_div,sub_zero,flatRounded_left r 0 _ le_rfl,h0,sub_zero]
  · simp only [flatCurve,bendPhase_one,flatRounded_right r 1 _ le_rfl,h0,h1]
    congr 2
    ring

end
end ContactTopology.EdgeRounding



namespace ContactTopology.EdgeRounding
open Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma flatRounded_embedding (r : ℝ) (hr : 0 < r) : Topology.IsEmbedding (flatRounded r) := by
  let g : ℝ → ℝ := fun s => bendX s-bendX (1-s)
  have hgc : Continuous g := bendX_smooth.continuous.sub
    (bendX_smooth.continuous.comp (continuous_const.sub continuous_id))
  have hg : Topology.IsEmbedding g := bend_difference_strict.isEmbedding_of_ordConnected
    (isPreconnected_range hgc).ordConnected
  let L : V → ℝ × ℝ := fun y => ((y 0-y 1)/r,y 2)
  have hL : Continuous L := by fun_prop
  have hprod : Topology.IsEmbedding (Prod.map g (id : ℝ → ℝ)) := hg.prodMap Topology.IsEmbedding.id
  have heq : L ∘ flatRounded r=Prod.map g (id : ℝ → ℝ) := by
    funext p
    apply Prod.ext
    · dsimp [L,flatRounded,g]
      field_simp [hr.ne']
    · rfl
  apply Topology.IsEmbedding.of_comp (flatRounded_smooth r).continuous hL
  simpa only [heq] using hprod

lemma contact_periodic (n : ℕ) (y v : V) :
    α (2*Real.pi*n) (![y 0,y 1,y 2+1]) v=α (2*Real.pi*n) y v := by
  have he : (2*Real.pi*n)*(y 2+1)=(2*Real.pi*n)*y 2+n*(2*Real.pi) := by ring
  change Real.sin ((2*Real.pi*n)*(y 2+1))*v 0+Real.cos ((2*Real.pi*n)*(y 2+1))*v 1=
    Real.sin ((2*Real.pi*n)*y 2)*v 0+Real.cos ((2*Real.pi*n)*y 2)*v 1
  rw [he,Real.sin_add_nat_mul_two_pi,Real.cos_add_nat_mul_two_pi]

end
end ContactTopology.EdgeRounding


namespace ContactTopology.EdgeRoundingSphere
open BirkhoffGlobalSection ContactTopology.ConvexCore Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma four_pi_ne : (4*Real.pi:ℝ) ≠ 0 := by positivity
lemma cover_of_unrotate (F : EquivariantSphereContactomorphism) (p : Jet3) :
    cover F (4*Real.pi) (unrotateJet (4*Real.pi) p)=imageChart F p := by
  change imageChart F (rotateJet (4*Real.pi) (unrotateJet (4*Real.pi) p))=_
  rw [rotate_unrotate _ four_pi_ne]

lemma centeredField_open_data (F : EquivariantSphereContactomorphism) (r : ℝ) :
    ∃ O : Set Phase, IsOpen O ∧ range (cover F (4*Real.pi)) ⊆ O ∧
      ∀ y ∈ O ∩ unitThreeSphere, ContDiffAt ℝ ∞ (centeredField F r) y ∧
        phaseDot y (centeredField F r y)=0 ∧ centeredField F r (-y)= -centeredField F r y ∧
        ∃ a : ℝ, ∀ w : Phase, phaseDot y w=0 →
          phaseRadialContact (centeredField F r y) w+
            phaseRadialContact y (fderiv ℝ (centeredField F r) y w)=a*phaseRadialContact y w := by
  classical
  choose U hUopen hUmem hUsub using imageChart_sphere_open F
  refine ⟨⋃ p, U p,isOpen_iUnion hUopen,?_,?_⟩
  · rintro y ⟨z,rfl⟩
    exact mem_iUnion.mpr ⟨rotateJet (4*Real.pi) z,hUmem _⟩
  · intro y hy
    obtain ⟨p,hp⟩ := mem_iUnion.mp hy.1
    obtain ⟨q,hq⟩ := hUsub p ⟨hp,hy.2⟩
    have hrepr : cover F (4*Real.pi) (unrotateJet (4*Real.pi) q)=y :=
      (cover_of_unrotate F q).trans hq
    rw [← hrepr]
    exact ⟨centeredField_smooth F r _ (cover_mem F _ _),centeredField_tangent F r _,
      centeredField_odd_on_cover F r _,centeredField_is_contact F r _⟩

def sphereRounded (F : EquivariantSphereContactomorphism) (r : ℝ) : ℝ × ℝ → Phase :=
  cover F (4*Real.pi) ∘ EdgeRounding.flatRounded r
lemma sphereRounded_smooth (F : EquivariantSphereContactomorphism) (r : ℝ) :
    ContDiff ℝ ∞ (sphereRounded F r) := (cover_smooth F _).comp (EdgeRounding.flatRounded_smooth r)
lemma sphereRounded_mem (F : EquivariantSphereContactomorphism) (r : ℝ) (p : ℝ × ℝ) :
    sphereRounded F r p ∈ unitThreeSphere := cover_mem F _ _
lemma sphereRounded_immersion (F : EquivariantSphereContactomorphism) (r : ℝ) (hr : 0 < r) (p : ℝ × ℝ) :
    Injective (fderiv ℝ (sphereRounded F r) p) := by
  rw [sphereRounded,fderiv_comp p ((cover_smooth F _).differentiable (by simp) _)
    ((EdgeRounding.flatRounded_smooth r).differentiable (by simp) _)]
  exact (cover_immersion F _ four_pi_ne _).comp (EdgeRounding.flatRounded_immersion r hr p)
lemma sphereRounded_transverse (F : EquivariantSphereContactomorphism) (r : ℝ) (hr : 0 < r) (p v : ℝ × ℝ) :
    centeredField F (r*EdgeRounding.bendC) (sphereRounded F r p) ≠ fderiv ℝ (sphereRounded F r) p v := by
  change centeredField F _ (cover F (4*Real.pi) (EdgeRounding.flatRounded r p))≠_
  rw [centeredField_cover,sphereRounded,fderiv_comp p ((cover_smooth F _).differentiable (by simp) _)
    ((EdgeRounding.flatRounded_smooth r).differentiable (by simp) _)]
  intro he
  exact EdgeRounding.flatRounded_transverse r hr p v ((cover_immersion F _ four_pi_ne _) he)
lemma sphereRounded_fiber (F : EquivariantSphereContactomorphism) (r : ℝ) (hr : 0 < r) (p q : ℝ × ℝ) :
    sphereRounded F r p=sphereRounded F r q ↔ p.1=q.1 ∧ ∃ k : ℤ, p.2=q.2+k := by
  have hfreq : 2*Real.pi*(2:ℕ)=4*Real.pi := by norm_num; ring
  have hf := cover_fiber F 2 (by norm_num) (EdgeRounding.flatRounded r p) (EdgeRounding.flatRounded r q)
  rw [hfreq] at hf
  change cover F (4*Real.pi) (EdgeRounding.flatRounded r p)=cover F (4*Real.pi) (EdgeRounding.flatRounded r q) ↔ _
  rw [hf]
  constructor
  · rintro ⟨k,hk⟩
    have h0 : r*EdgeRounding.bendX p.1=r*EdgeRounding.bendX q.1 := congrFun hk 0
    have h1 : r*EdgeRounding.bendX (1-p.1)=r*EdgeRounding.bendX (1-q.1) := congrFun hk 1
    have hs : p.1=q.1 := EdgeRounding.bend_difference_strict.injective (by
      rw [mul_left_cancel₀ hr.ne' h0,mul_left_cancel₀ hr.ne' h1])
    exact ⟨hs,⟨k,congrFun hk 2⟩⟩
  · rintro ⟨hs,k,hk⟩
    refine ⟨k,?_⟩
    ext i
    fin_cases i <;> simp [EdgeRounding.flatRounded,shift,hs,hk]
lemma sphereRounded_antipodal (F : EquivariantSphereContactomorphism) (r s z : ℝ) :
    sphereRounded F r (s,z+1/2)= -sphereRounded F r (s,z) :=
  cover_antipodal F (EdgeRounding.flatRounded r (s,z))
lemma sphereRounded_legendrian (F : EquivariantSphereContactomorphism) (r : ℝ) (p : ℝ × ℝ) :
    phaseRadialContact (sphereRounded F r p) (fderiv ℝ (sphereRounded F r) p (0,1))=0 := by
  rw [sphereRounded,fderiv_comp p ((cover_smooth F _).differentiable (by simp) _)
    ((EdgeRounding.flatRounded_smooth r).differentiable (by simp) _)]
  change phaseRadialContact (cover F (4*Real.pi) _) (fderiv ℝ (cover F (4*Real.pi)) _ _)=0
  rw [cover_contact]
  have hz : EdgeRounding.α (4*Real.pi) (EdgeRounding.flatRounded r p)
      (fderiv ℝ (EdgeRounding.flatRounded r) p (0,1))=0 := by
    rw [EdgeRounding.flatRounded_fderiv]
    simp [EdgeRounding.α]
  exact mul_eq_zero.mpr (Or.inr hz)
lemma sphereRounded_dividing (F : EquivariantSphereContactomorphism) (r : ℝ) (hr : 0 < r)
    (s z : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
    phaseRadialContact (sphereRounded F r (s,z))
      (centeredField F (r*EdgeRounding.bendC) (sphereRounded F r (s,z)))=0 ↔
        ∃ k : ℤ, z=(k:ℝ)/4-EdgeRounding.bendPhase s/(4*Real.pi) := by
  change phaseRadialContact (cover F (4*Real.pi) _) (centeredField F _ (cover F (4*Real.pi) _))=0 ↔ _
  rw [centeredField_cover,cover_contact,mul_eq_zero]
  simp only [(weight_pos F (4*Real.pi) _).ne',false_or]
  rw [EdgeRounding.flatRounded_dividing_iff _ r (by positivity) hr s z hs]
  have he (k : ℤ) : (k:ℝ)*Real.pi/(4*Real.pi)=(k:ℝ)/4 := by field_simp [Real.pi_ne_zero]
  simp only [he]

def sphereDividingCurve (F : EquivariantSphereContactomorphism) (r : ℝ) (k : ℤ) : ℝ → Phase :=
  cover F (4*Real.pi) ∘ EdgeRounding.flatCurve (4*Real.pi) r k
lemma sphereDividingCurve_smooth (F : EquivariantSphereContactomorphism) (r : ℝ) (k : ℤ) :
    ContDiff ℝ ∞ (sphereDividingCurve F r k) :=
  (cover_smooth F _).comp (EdgeRounding.flatCurve_smooth _ r k)
lemma sphereDividingCurve_regular (F : EquivariantSphereContactomorphism) (r : ℝ) (hr : 0 < r) (k : ℤ) (s : ℝ) :
    deriv (sphereDividingCurve F r k) s ≠ 0 := by
  have hh := ((cover_smooth F (4*Real.pi)).differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt s
    ((EdgeRounding.flatCurve_smooth (4*Real.pi) r k).differentiable (by simp) s).hasDerivAt
  change HasDerivAt (sphereDividingCurve F r k) _ s at hh
  rw [hh.deriv]
  intro hz
  have he : fderiv ℝ (cover F (4*Real.pi)) (EdgeRounding.flatCurve (4*Real.pi) r k s) (deriv (EdgeRounding.flatCurve (4*Real.pi) r k) s)=
      fderiv ℝ (cover F (4*Real.pi)) (EdgeRounding.flatCurve (4*Real.pi) r k s) 0 := by simpa using hz
  exact EdgeRounding.flatCurve_regular _ r hr k s ((cover_immersion F _ four_pi_ne _) he)

def roundedAnnulus (F : EquivariantSphereContactomorphism) (r : ℝ) : Set Phase :=
  sphereRounded F r '' (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1)
lemma roundedAnnulus_compact (F : EquivariantSphereContactomorphism) (r : ℝ) :
    IsCompact (roundedAnnulus F r) :=
  (isCompact_Icc.prod isCompact_Icc).image (sphereRounded_smooth F r).continuous
lemma roundedAnnulus_mem (F : EquivariantSphereContactomorphism) (r : ℝ) (hr : 0 < r) (y : Phase) :
    y ∈ roundedAnnulus F r ↔ ∃ s ∈ Icc (0:ℝ) 1, ∃ z : ℝ, y=sphereRounded F r (s,z) := by
  constructor
  · rintro ⟨⟨s,z⟩,hp,hpEq⟩
    exact ⟨s,hp.1,z,hpEq.symm⟩
  · rintro ⟨s,hs,z,rfl⟩
    have he : sphereRounded F r (s,Int.fract z)=sphereRounded F r (s,z) := by
      apply (sphereRounded_fiber F r hr _ _).mpr
      refine ⟨rfl,⟨-⌊z⌋,?_⟩⟩
      simp only [Int.fract,Int.cast_neg]
      ring
    exact ⟨(s,Int.fract z),⟨hs,Int.fract_nonneg z,(Int.fract_lt_one z).le⟩,he⟩
lemma roundedAnnulus_antipodal (F : EquivariantSphereContactomorphism) (r : ℝ) (hr : 0 < r)
    (y : Phase) (hy : y ∈ roundedAnnulus F r) : -y ∈ roundedAnnulus F r := by
  obtain ⟨s,hs,z,rfl⟩ := (roundedAnnulus_mem F r hr y).mp hy
  apply (roundedAnnulus_mem F r hr _).mpr
  exact ⟨s,hs,z+1/2,(sphereRounded_antipodal F r s z).symm⟩
lemma sphereDividingCurve_formula (F : EquivariantSphereContactomorphism) (r : ℝ) (k : ℤ) (s : ℝ) :
    sphereDividingCurve F r k s=sphereRounded F r (s,(k:ℝ)/4-EdgeRounding.bendPhase s/(4*Real.pi)) := by
  have he : (k:ℝ)*Real.pi/(4*Real.pi)=(k:ℝ)/4 := by field_simp [Real.pi_ne_zero]
  simp only [sphereDividingCurve,Function.comp_apply,EdgeRounding.flatCurve,sphereRounded,he]
lemma sphereDividingCurve_endpoints (F : EquivariantSphereContactomorphism) (r : ℝ) (k : ℤ) :
    sphereDividingCurve F r k 0=cover F (4*Real.pi) ![0,r*EdgeRounding.bendC,(k:ℝ)/4] ∧
    sphereDividingCurve F r k 1=cover F (4*Real.pi) ![r*EdgeRounding.bendC,0,(k:ℝ)/4-1/8] := by
  have hp := EdgeRounding.flatCurve_endpoints 2 (by norm_num) r k
  norm_num at hp
  have he : 2*Real.pi*2=4*Real.pi := by ring
  rw [he] at hp
  exact ⟨congrArg (cover F (4*Real.pi)) hp.1,congrArg (cover F (4*Real.pi)) hp.2⟩

end
end ContactTopology.EdgeRoundingSphere


open BirkhoffGlobalSection Set Function Filter
open scoped ContDiff Topology

theorem solution
    (F : EquivariantSphereContactomorphism) (r : ℝ) (hr : 0 < r) :
    ∃ c : ℝ, ∃ C : (Fin 3 → ℝ) → Phase, ∃ L : (Fin 3 → ℝ) → ℝ,
    ∃ S : ℝ × ℝ → Phase, ∃ Y : Phase → Phase, ∃ O : Set Phase,
    ∃ phase : ℝ → ℝ, ∃ γ : ℤ → ℝ → Phase,
      0 < c ∧ ContDiff ℝ ∞ C ∧ ContDiff ℝ ∞ L ∧ (∀ y, 0 < L y) ∧
      (∀ y, C y ∈ unitThreeSphere) ∧ (∀ y, Injective (fderiv ℝ C y)) ∧
      (∀ z, C ![0,0,z]=F.toFun ![Real.cos (2*Real.pi*z),Real.sin (2*Real.pi*z),0,0]) ∧
      (∀ y v, phaseRadialContact (C y) (fderiv ℝ C y v)=
        L y*(Real.sin (4*Real.pi*y 2)*v 0+Real.cos (4*Real.pi*y 2)*v 1)) ∧
      ContDiff ℝ ∞ S ∧ (∀ p, S p ∈ unitThreeSphere) ∧
      (∀ p, Injective (fderiv ℝ S p)) ∧
      (∀ p q, S p=S q ↔ p.1=q.1 ∧ ∃ k : ℤ, p.2=q.2+k) ∧
      (∀ s z, S (s,z+1/2)= -S (s,z)) ∧
      (∀ s z, s ≤ 0 → S (s,z)=C ![0,r*(c-s),z]) ∧
      (∀ s z, 1 ≤ s → S (s,z)=C ![r*(c+s-1),0,z]) ∧
      IsCompact (S '' (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1)) ∧
      (∀ y, y ∈ S '' (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) ↔
        ∃ s ∈ Icc (0:ℝ) 1, ∃ z : ℝ, y=S (s,z)) ∧
      IsOpen O ∧ range S ⊆ O ∧
      (∀ y ∈ O ∩ unitThreeSphere, ContDiffAt ℝ ∞ Y y ∧ phaseDot y (Y y)=0 ∧
        Y (-y)= -Y y ∧ ∃ a : ℝ, ∀ w : Phase, phaseDot y w=0 →
          phaseRadialContact (Y y) w+phaseRadialContact y (fderiv ℝ Y y w)=a*phaseRadialContact y w) ∧
      (∀ p v : ℝ × ℝ, Y (S p) ≠ fderiv ℝ S p v) ∧
      (∀ p : ℝ × ℝ, phaseRadialContact (S p) (fderiv ℝ S p (0,1))=0) ∧
      ContDiff ℝ ∞ phase ∧ phase 0=0 ∧ phase 1=Real.pi/2 ∧
      (∀ k, ContDiff ℝ ∞ (γ k)) ∧
      (∀ k s, γ k s=S (s,(k:ℝ)/4-phase s/(4*Real.pi))) ∧
      (∀ k s, deriv (γ k) s ≠ 0) ∧
      (∀ k, γ k 0=C ![0,r*c,(k:ℝ)/4] ∧ γ k 1=C ![r*c,0,(k:ℝ)/4-1/8]) ∧
      ∀ s ∈ Icc (0:ℝ) 1, ∀ z : ℝ,
        (phaseRadialContact (S (s,z)) (Y (S (s,z)))=0 ↔
          ∃ k : ℤ, z=(k:ℝ)/4-phase s/(4*Real.pi)) := by

  obtain ⟨O,hO,hcover,hfield⟩ := ContactTopology.EdgeRoundingSphere.centeredField_open_data F
    (r*ContactTopology.EdgeRounding.bendC)
  refine ⟨ContactTopology.EdgeRounding.bendC,ContactTopology.EdgeRoundingSphere.cover F (4*Real.pi),
    ContactTopology.EdgeRoundingSphere.weight F (4*Real.pi),
    ContactTopology.EdgeRoundingSphere.sphereRounded F r,
    ContactTopology.EdgeRoundingSphere.centeredField F (r*ContactTopology.EdgeRounding.bendC),O,
    ContactTopology.EdgeRounding.bendPhase,ContactTopology.EdgeRoundingSphere.sphereDividingCurve F r,
    ContactTopology.EdgeRounding.bendC_pos,ContactTopology.EdgeRoundingSphere.cover_smooth F _,
    ContactTopology.EdgeRoundingSphere.weight_smooth F _,ContactTopology.EdgeRoundingSphere.weight_pos F _,
    ContactTopology.EdgeRoundingSphere.cover_mem F _,
    ContactTopology.EdgeRoundingSphere.cover_immersion F _ ContactTopology.EdgeRoundingSphere.four_pi_ne,
    ContactTopology.EdgeRoundingSphere.cover_core F _,ContactTopology.EdgeRoundingSphere.cover_contact F _,
    ContactTopology.EdgeRoundingSphere.sphereRounded_smooth F r,
    ContactTopology.EdgeRoundingSphere.sphereRounded_mem F r,
    ContactTopology.EdgeRoundingSphere.sphereRounded_immersion F r hr,
    ContactTopology.EdgeRoundingSphere.sphereRounded_fiber F r hr,
    ContactTopology.EdgeRoundingSphere.sphereRounded_antipodal F r,?_,?_,
    ContactTopology.EdgeRoundingSphere.roundedAnnulus_compact F r,
    ContactTopology.EdgeRoundingSphere.roundedAnnulus_mem F r hr,hO,?_,hfield,
    ContactTopology.EdgeRoundingSphere.sphereRounded_transverse F r hr,
    ContactTopology.EdgeRoundingSphere.sphereRounded_legendrian F r,
    ContactTopology.EdgeRounding.bendPhase_smooth,ContactTopology.EdgeRounding.bendPhase_zero,
    ContactTopology.EdgeRounding.bendPhase_one,ContactTopology.EdgeRoundingSphere.sphereDividingCurve_smooth F r,
    ContactTopology.EdgeRoundingSphere.sphereDividingCurve_formula F r,
    ContactTopology.EdgeRoundingSphere.sphereDividingCurve_regular F r hr,
    ContactTopology.EdgeRoundingSphere.sphereDividingCurve_endpoints F r,?_⟩
  · intro s z hs
    exact congrArg (ContactTopology.EdgeRoundingSphere.cover F (4*Real.pi))
      (ContactTopology.EdgeRounding.flatRounded_left r s z hs)
  · intro s z hs
    exact congrArg (ContactTopology.EdgeRoundingSphere.cover F (4*Real.pi))
      (ContactTopology.EdgeRounding.flatRounded_right r s z hs)
  · rintro y ⟨p,rfl⟩
    exact hcover ⟨ContactTopology.EdgeRounding.flatRounded r p,rfl⟩
  · intro s hs z
    exact ContactTopology.EdgeRoundingSphere.sphereRounded_dividing F r hr s z hs
