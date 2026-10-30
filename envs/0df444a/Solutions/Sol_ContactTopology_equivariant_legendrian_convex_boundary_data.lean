-- Prove2me | solution 1 for ContactTopology.equivariant_legendrian_convex_boundary_data
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-30T00:44:44.838431+00:00
-- url     : https://prove2.me/submissions/4b85ee91-d87c-48f9-aa51-e9fb9f415e12

import Definitions.Def_BirkhoffGlobalSection_SphereContact
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
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
open BirkhoffGlobalSection Set Function
open scoped ContDiff
theorem solution
    (F : EquivariantSphereContactomorphism) (r : ℝ) (hr : 0 < r) :
    let chart : (Fin 3 → ℝ) → Phase := fun p => radialNormalize
      ![Real.cos (2*Real.pi*p 0),Real.sin (2*Real.pi*p 0),
        (-2*p 2)*Real.cos (2*Real.pi*p 0)+(p 1/(2*Real.pi))*Real.sin (2*Real.pi*p 0),
        (-2*p 2)*Real.sin (2*Real.pi*p 0)-(p 1/(2*Real.pi))*Real.cos (2*Real.pi*p 0)]
    let G : (Fin 3 → ℝ) → Phase := fun p => F.toFun (chart p)
    let X : Phase → Phase := fun y => ![0,0,y 2,y 3]-wNormSq y • y
    let Y : Phase → Phase := fun y => fderiv ℝ F.toFun (F.invFun y) (X (F.invFun y))
    let N₁ : Phase → ℝ := fun y => -2*Real.pi*(y 0*y 3-y 1*y 2)/zNormSq y
    let N₂ : Phase → ℝ := fun y => -(y 0*y 2+y 1*y 3)/(2*zNormSq y)
    let R : Phase → ℝ := fun y => N₁ (F.invFun y)^2+N₂ (F.invFun y)^2
    let T : Set Phase := G '' {p | p 1^2+p 2^2=r^2}
    let C : ℝ → ℝ → Phase := fun s x => G ![x,s,0]
    ContDiff ℝ ∞ G ∧ (∀ p, G p ∈ unitThreeSphere) ∧
      (∀ p, Injective (fderiv ℝ G p)) ∧
      (∀ p q, G p=G q ↔ ∃ n : ℤ, p=q+![(n:ℝ),0,0]) ∧ IsCompact T ∧
      (∃ O : Set Phase, IsOpen O ∧ T ⊆ O ∧
        (O ∩ unitThreeSphere) ∩ {y | R y=r^2}=T ∧
        (∀ y ∈ O ∩ unitThreeSphere, ContDiffAt ℝ ∞ Y y ∧ phaseDot y (Y y)=0 ∧
          ∃ a : ℝ, ∀ w : Phase, phaseDot y w=0 →
            phaseRadialContact (Y y) w+phaseRadialContact y (fderiv ℝ Y y w)=a*phaseRadialContact y w) ∧
        ∀ y ∈ T, ContDiffAt ℝ ∞ R y ∧ 0 < fderiv ℝ R y (Y y)) ∧
      {y ∈ T | phaseRadialContact y (Y y)=0}=range (C r) ∪ range (C (-r)) ∧
      Disjoint (range (C r)) (range (C (-r))) ∧
      ∀ s : ℝ, ContDiff ℝ ∞ (C s) ∧ (∀ x, deriv (C s) x ≠ 0) ∧
        (∀ x y, C s x=C s y ↔ ∃ n : ℤ, x=y+n) ∧
        (∀ x, C s (x+1/2)= -C s x) ∧ IsCompact (range (C s)) ∧ IsConnected (range (C s)) := by
  refine ⟨ContactTopology.ConvexCore.imageChart_contDiff F,
    ContactTopology.ConvexCore.imageChart_mem F,
    ContactTopology.ConvexCore.imageChart_derivative_injective F,
    ContactTopology.ConvexCore.imageChart_fiber F,
    ContactTopology.ConvexCore.coreTorus_compact F r hr,
    ContactTopology.ConvexCore.convex_boundary_open_data F r hr,
    ContactTopology.ConvexCore.dividingSet_two_curves F r,
    ContactTopology.ConvexCore.dividingSet_curves_disjoint F r hr,?_⟩
  intro s
  refine ⟨ContactTopology.ConvexCore.dividingCurve_contDiff F s,
    ContactTopology.ConvexCore.dividingCurve_regular F s,?_,
    ContactTopology.ConvexCore.dividingCurve_antipodal F s,
    ContactTopology.ConvexCore.dividingCurve_range_compact F s,
    ContactTopology.ConvexCore.dividingCurve_range_connected F s⟩
  intro x y
  change (ContactTopology.ConvexCore.dividingCurve F s x=ContactTopology.ConvexCore.dividingCurve F s y) ↔ _
  constructor
  · intro h
    exact ((ContactTopology.ConvexCore.dividingCurve_fiber F s s x y).mp h).2
  · intro h
    exact (ContactTopology.ConvexCore.dividingCurve_fiber F s s x y).mpr ⟨rfl,h⟩
