-- Prove2me | solution 1 for ContactTopology.sphere_legendrian_core_coordinate_deformation
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-29T23:01:39.262596+00:00
-- url     : https://prove2.me/submissions/c6341842-450b-4d79-a0f6-3d90c0cd4984

import Definitions.Def_BirkhoffGlobalSection_SphereContact
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Separation.Hausdorff
import Theorems.Thm_BirkhoffGlobalSection_radial_normalization_contact_identity
import Theorems.Thm_ContactCalculus_exterior_pairing_pullback
import Theorems.Thm_ParameterizedCalculus_smooth_unit_interval_integral




















namespace ContactTopology
open MeasureTheory Set
open scoped ContDiff
noncomputable section

/-- Parameter-dependent smooth division by the normal scale. The integral
formula gives joint smoothness at scale zero, not merely a pointwise limit. -/
lemma smooth_normal_scale_division {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (f : P × ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hz : ∀ p, f (p,0) = 0) :
    ∃ Q : P × ℝ → ℝ, ContDiff ℝ ∞ Q ∧
      (∀ p s, f (p,s) = s * Q (p,s)) ∧
      (∀ p, Q (p,0) = fderiv ℝ f (p,0) (0,1)) := by
  let h : (P × ℝ) → ℝ → ℝ := fun p r => fderiv ℝ f (p.1,r*p.2) (0,1)
  let Q : P × ℝ → ℝ := fun p => ∫ r in (0:ℝ)..1, h p r
  have hd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hh : ContDiff ℝ ∞ (Function.uncurry h) := by
    exact (hd.comp ((contDiff_fst.fst).prodMk (contDiff_snd.mul contDiff_fst.snd))).clm_apply contDiff_const
  refine ⟨Q,ParameterizedCalculus.smooth_unit_interval_integral h hh,?_,?_⟩
  · intro p s
    let g : ℝ → ℝ := fun r => f (p,r*s)
    have hg : ∀ r, HasDerivAt g (s * h (p,s) r) r := by
      intro r
      have hi : HasDerivAt (fun t : ℝ => (p,t*s)) ((0:P),s) r := by
        convert! (hasDerivAt_const r p).prodMk ((hasDerivAt_id r).mul_const s) using 1 <;> simp
      have he := (hf.differentiable (by simp) (p,r*s)).hasFDerivAt.comp_hasDerivAt r hi
      apply he.congr_deriv
      change fderiv ℝ f (p,r*s) (0,s) = s * fderiv ℝ f (p,r*s) (0,1)
      have hv : ((0:P),s) = s • ((0:P),(1:ℝ)) := by simp
      rw [hv,map_smul,smul_eq_mul]
    have hc : Continuous (fun r => s * h (p,s) r) := by
      exact continuous_const.mul (hh.continuous.comp (continuous_const.prodMk continuous_id))
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hg r) (hc.intervalIntegrable 0 1)
    change (∫ r in (0:ℝ)..1, s * h (p,s) r) = g 1-g 0 at hFTC
    rw [intervalIntegral.integral_const_mul] at hFTC
    simpa only [Q,g,one_mul,zero_mul,hz,sub_zero] using hFTC.symm
  · intro p
    simp [Q,h]

end
end ContactTopology

namespace ContactTopology
open Set Function
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
noncomputable section

abbrev Jet3 := Fin 3 → ℝ

def corePoint (x : ℝ) : Jet3 := ![x,0,0]
def normalScale (s : ℝ) (p : Jet3) : Jet3 := ![p 0,s*p 1,s*p 2]
def normalVector (p : Jet3) : Jet3 := ![0,p 1,p 2]
def jetContact (p v : Jet3) : ℝ := v 2-p 1*v 0

lemma normalScale_zero (p : Jet3) : normalScale 0 p = corePoint (p 0) := by
  simp [normalScale,corePoint]

lemma normalScale_one (p : Jet3) : normalScale 1 p = p := by
  ext i
  fin_cases i <;> simp [normalScale]

lemma normalScale_contDiff : ContDiff ℝ ∞ (fun q : ℝ × Jet3 => normalScale q.1 q.2) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ ∞ (fun q : ℝ × Jet3 => q.2 0)
    fun_prop
  · change ContDiff ℝ ∞ (fun q : ℝ × Jet3 => q.1 * q.2 1)
    fun_prop
  · change ContDiff ℝ ∞ (fun q : ℝ × Jet3 => q.1 * q.2 2)
    fun_prop

lemma normalScale_hasDerivAt (p : Jet3) :
    HasDerivAt (fun s => normalScale s p) (normalVector p) 0 := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hasDerivAt_const 0 (p 0)
  · simpa [normalScale,normalVector] using (hasDerivAt_id (0:ℝ)).mul_const (p 1)
  · simpa [normalScale,normalVector] using (hasDerivAt_id (0:ℝ)).mul_const (p 2)

/-- The normal conjugation of a smooth map fixing the core extends jointly
smoothly across zero scale. This is the analytic limit in Min, Lemma2.7(2). -/
lemma smooth_normal_rescaling (F : Jet3 → Jet3) (hF : ContDiff ℝ ∞ F)
    (hcore : ∀ x, F (corePoint x) = corePoint x) :
    ∃ G : ℝ → Jet3 → Jet3,
      ContDiff ℝ ∞ (fun q : ℝ × Jet3 => G q.1 q.2) ∧
      (∀ s : ℝ, s ≠ 0 → ∀ p, G s p = normalScale s⁻¹ (F (normalScale s p))) ∧
      (∀ p, G 0 p = ![p 0,
        (fderiv ℝ F (corePoint (p 0)) (normalVector p)) 1,
        (fderiv ℝ F (corePoint (p 0)) (normalVector p)) 2]) ∧
      (∀ p, G 1 p = F p) := by
  let B : Fin 3 → Jet3 × ℝ → ℝ := fun i q => F (normalScale q.2 q.1) i
  have hB : ∀ i, ContDiff ℝ ∞ (B i) := by
    intro i
    exact ((contDiff_apply ℝ ℝ i).comp hF).comp (normalScale_contDiff.comp (contDiff_snd.prodMk contDiff_fst))
  have hz : ∀ i : Fin 3, i ≠ 0 → ∀ p, B i (p,0) = 0 := by
    intro i hi p
    change F (normalScale 0 p) i = 0
    rw [normalScale_zero,hcore]
    fin_cases i <;> simp_all [corePoint]
  obtain ⟨Q₁,hQ₁,he₁,hz₁⟩ := smooth_normal_scale_division (B 1) (hB 1) (hz 1 (by decide))
  obtain ⟨Q₂,hQ₂,he₂,hz₂⟩ := smooth_normal_scale_division (B 2) (hB 2) (hz 2 (by decide))
  let G : ℝ → Jet3 → Jet3 := fun s p => ![B 0 (p,s),Q₁ (p,s),Q₂ (p,s)]
  have hGsmooth : ContDiff ℝ ∞ (fun q : ℝ × Jet3 => G q.1 q.2) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · exact (hB 0).comp (contDiff_snd.prodMk contDiff_fst)
    · exact hQ₁.comp (contDiff_snd.prodMk contDiff_fst)
    · exact hQ₂.comp (contDiff_snd.prodMk contDiff_fst)
  have hGnz : ∀ s : ℝ, s ≠ 0 → ∀ p, G s p = normalScale s⁻¹ (F (normalScale s p)) := by
    intro s hs p
    ext i
    fin_cases i
    · rfl
    · change Q₁ (p,s) = s⁻¹ * B 1 (p,s)
      rw [he₁ p s]
      field_simp
    · change Q₂ (p,s) = s⁻¹ * B 2 (p,s)
      rw [he₂ p s]
      field_simp
  have hBnormal : ∀ i p, fderiv ℝ (B i) (p,0) (0,1) =
      (fderiv ℝ F (corePoint (p 0)) (normalVector p)) i := by
    intro i p
    have hδ := normalScale_hasDerivAt p
    have hFi : DifferentiableAt ℝ (fun y => F y i) (normalScale 0 p) :=
      (((contDiff_apply ℝ ℝ i).comp hF).differentiable (by simp) _)
    have hd := hFi.hasFDerivAt.comp_hasDerivAt 0 hδ
    have hb := ((hB i).differentiable (by simp) (p,0)).hasFDerivAt.comp_hasDerivAt 0
      ((hasDerivAt_const (0:ℝ) p).prodMk (hasDerivAt_id (0:ℝ)))
    have he := hb.unique hd
    have hcoord : fderiv ℝ (fun y => F y i) (normalScale 0 p) =
        (ContinuousLinearMap.proj i).comp (fderiv ℝ F (normalScale 0 p)) := by
      exact ((ContinuousLinearMap.proj i).hasFDerivAt.comp _ (hF.differentiable (by simp) _).hasFDerivAt).fderiv
    rw [normalScale_zero] at he hcoord
    rw [hcoord] at he
    simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply] using he
  refine ⟨G,hGsmooth,hGnz,?_,?_⟩
  · intro p
    ext i
    fin_cases i
    · change F (normalScale 0 p) 0 = p 0
      rw [normalScale_zero,hcore]
      rfl
    · change Q₁ (p,0) = (fderiv ℝ F (corePoint (p 0)) (normalVector p)) 1
      rw [hz₁ p,hBnormal]
    · change Q₂ (p,0) = (fderiv ℝ F (corePoint (p 0)) (normalVector p)) 2
      rw [hz₂ p,hBnormal]
  · intro p
    rw [hGnz 1 (by norm_num),inv_one,normalScale_one,normalScale_one]

end
end ContactTopology

namespace ContactTopology
open Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

def normalScaleLinear (s : ℝ) : Jet3 →L[ℝ] Jet3 :=
  LinearMap.toContinuousLinearMap {
    toFun := normalScale s
    map_add' := by intro p q; ext i; fin_cases i <;> simp [normalScale] <;> ring
    map_smul' := by intro c p; ext i; fin_cases i <;> simp [normalScale] <;> ring }

lemma normalScale_fderiv (s : ℝ) (p v : Jet3) :
    fderiv ℝ (normalScale s) p v = normalScale s v := by
  exact congrArg (fun L : Jet3 →L[ℝ] Jet3 => L v) (normalScaleLinear s).hasFDerivAt.fderiv

lemma normalScale_differentiable (s : ℝ) : Differentiable ℝ (normalScale s) :=
  (normalScaleLinear s).differentiable

lemma jetContact_normalScale (s : ℝ) (p v : Jet3) :
    jetContact (normalScale s p) (normalScale s v) = s * jetContact p v := by
  simp [normalScale,jetContact]
  ring

lemma normal_rescaling_contact_nonzero (F : Jet3 → Jet3) (hF : ContDiff ℝ ∞ F)
    (G : ℝ → Jet3 → Jet3)
    (hGnz : ∀ s : ℝ, s ≠ 0 → ∀ p, G s p = normalScale s⁻¹ (F (normalScale s p)))
    (U : Set Jet3) (lam : Jet3 → ℝ)
    (hcontact : ∀ p ∈ U, ∀ v, jetContact (F p) (fderiv ℝ F p v) = lam p * jetContact p v)
    (s : ℝ) (hs : s ≠ 0) (p : Jet3) (hp : normalScale s p ∈ U) (v : Jet3) :
    jetContact (G s p) (fderiv ℝ (G s) p v) = lam (normalScale s p) * jetContact p v := by
  have heq : G s = normalScale s⁻¹ ∘ F ∘ normalScale s := funext (hGnz s hs)
  rw [heq]
  rw [fderiv_comp p (normalScale_differentiable s⁻¹ _)
    ((hF.differentiable (by simp) _).comp p (normalScale_differentiable s p))]
  rw [fderiv_comp p (hF.differentiable (by simp) _) (normalScale_differentiable s p)]
  simp only [ContinuousLinearMap.comp_apply,normalScale_fderiv,Function.comp_apply]
  rw [jetContact_normalScale,hcontact _ hp,jetContact_normalScale]
  field_simp

lemma joint_fderiv_slice_apply (G : ℝ → Jet3 → Jet3)
    (hG : ContDiff ℝ ∞ (fun q : ℝ × Jet3 => G q.1 q.2)) (t : ℝ) (p v : Jet3) :
    fderiv ℝ (G t) p v = fderiv ℝ (fun q : ℝ × Jet3 => G q.1 q.2) (t,p) (0,v) := by
  have hd := (hG.differentiable (by simp) (t,p)).hasFDerivAt.comp p
    ((hasFDerivAt_const t p).prodMk (hasFDerivAt_id p))
  exact congrArg (fun L : Jet3 →L[ℝ] Jet3 => L v) hd.fderiv

lemma rescaled_contact_pairing_continuous (G : ℝ → Jet3 → Jet3)
    (hG : ContDiff ℝ ∞ (fun q : ℝ × Jet3 => G q.1 q.2)) (p v : Jet3) :
    Continuous (fun t => jetContact (G t p) (fderiv ℝ (G t) p v)) := by
  have hvalue : ContDiff ℝ ∞ (fun t => G t p) := hG.comp (contDiff_id.prodMk contDiff_const)
  have hd : ContDiff ℝ ∞ (fun q : ℝ × Jet3 =>
      fderiv ℝ (fun w : ℝ × Jet3 => G w.1 w.2) q (0,v)) :=
    (hG.fderiv_right (by simp)).clm_apply contDiff_const
  have hslice : ContDiff ℝ ∞ (fun t => fderiv ℝ (G t) p v) := by
    have heq : (fun t => fderiv ℝ (G t) p v) =
        (fun t => fderiv ℝ (fun q : ℝ × Jet3 => G q.1 q.2) (t,p) (0,v)) :=
      funext fun t => joint_fderiv_slice_apply G hG t p v
    rw [heq]
    exact hd.comp (contDiff_id.prodMk contDiff_const)
  unfold jetContact
  exact (((contDiff_apply ℝ ℝ 2).comp hslice).sub
    (((contDiff_apply ℝ ℝ 1).comp hvalue).mul ((contDiff_apply ℝ ℝ 0).comp hslice))).continuous

/-- The contact identity also holds at zero scale. Openness of the original
contact domain suffices: each fixed normal vector enters it at small scale. -/
lemma normal_rescaling_contact_zero (F : Jet3 → Jet3) (hF : ContDiff ℝ ∞ F)
    (G : ℝ → Jet3 → Jet3)
    (hG : ContDiff ℝ ∞ (fun q : ℝ × Jet3 => G q.1 q.2))
    (hGnz : ∀ s : ℝ, s ≠ 0 → ∀ p, G s p = normalScale s⁻¹ (F (normalScale s p)))
    (U : Set Jet3) (hU : IsOpen U) (hcoreU : ∀ x, corePoint x ∈ U)
    (lam : Jet3 → ℝ) (hlam : Continuous lam)
    (hcontact : ∀ p ∈ U, ∀ v, jetContact (F p) (fderiv ℝ F p v) = lam p * jetContact p v)
    (p v : Jet3) :
    jetContact (G 0 p) (fderiv ℝ (G 0) p v) = lam (corePoint (p 0)) * jetContact p v := by
  have hδ : Continuous (fun s => normalScale s p) :=
    normalScale_contDiff.continuous.comp (continuous_id.prodMk continuous_const)
  have hmem : ∀ᶠ s in 𝓝 (0:ℝ), normalScale s p ∈ U :=
    hδ.continuousAt.preimage_mem_nhds (hU.mem_nhds (by rw [normalScale_zero]; exact hcoreU _))
  have heq : (fun s => jetContact (G s p) (fderiv ℝ (G s) p v)) =ᶠ[𝓝[≠] (0:ℝ)]
      (fun s => lam (normalScale s p) * jetContact p v) := by
    filter_upwards [hmem.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with s hs hne
    exact normal_rescaling_contact_nonzero F hF G hGnz U lam hcontact s hne p hs v
  have hleft := rescaled_contact_pairing_continuous G hG p v
  have hright : Continuous (fun s => lam (normalScale s p)*jetContact p v) := (hlam.comp hδ).mul continuous_const
  have he := (hleft.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hright.continuousAt).mp heq
  simpa only [normalScale_zero] using he.eq_of_nhds

end
end ContactTopology

namespace ContactTopology
open Set Function
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma corePoint_contDiff : ContDiff ℝ ∞ corePoint := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_id
  · exact contDiff_const
  · exact contDiff_const

lemma fderiv_coordinate (F : Jet3 → Jet3) (p v : Jet3)
    (hF : DifferentiableAt ℝ F p) (i : Fin 3) :
    fderiv ℝ (fun q => F q i) p v = (fderiv ℝ F p v) i := by
  have hd := (ContinuousLinearMap.proj i).hasFDerivAt.comp p hF.hasFDerivAt
  exact congrArg (fun L : Jet3 →L[ℝ] ℝ => L v) hd.fderiv

def coreLinear (lam : ℝ → ℝ) (p : Jet3) : Jet3 :=
  ![p 0,lam (p 0)*p 1+deriv lam (p 0)*p 2,lam (p 0)*p 2]

/-- A fiber-linear contact map fixing the core is determined by its positive
conformal factor on that core. This identifies the zero-scale limit. -/
lemma normal_form_from_contact (F : Jet3 → Jet3) (hF : ContDiff ℝ ∞ F)
    (lam : ℝ → ℝ) (hlam : ContDiff ℝ ∞ lam)
    (hfirst : ∀ p, F p 0 = p 0)
    (hlast : ∀ p, F p 2 = lam (p 0)*p 2)
    (hcontact : ∀ p v, jetContact (F p) (fderiv ℝ F p v) = lam (p 0)*jetContact p v) :
    F = coreLinear lam := by
  have hfirstfun : (fun p => F p 0) = (fun p => p 0) := funext hfirst
  have hlastfun : (fun p => F p 2) = (fun p => lam (p 0)*p 2) := funext hlast
  funext p
  have hD0 : (fderiv ℝ F p (Pi.single 0 1)) 0 = 1 := by
    rw [← fderiv_coordinate F p (Pi.single 0 1) (hF.differentiable (by simp) p) 0,hfirstfun]
    have hd := (ContinuousLinearMap.proj (0:Fin 3) : Jet3 →L[ℝ] ℝ).hasFDerivAt (x := p)
    change HasFDerivAt (fun q : Jet3 => q 0) _ p at hd
    rw [hd.fderiv]
    simp
  have hD2 : (fderiv ℝ F p (Pi.single 0 1)) 2 = deriv lam (p 0)*p 2 := by
    rw [← fderiv_coordinate F p (Pi.single 0 1) (hF.differentiable (by simp) p) 2,hlastfun]
    have hl := (hlam.differentiable (by simp) (p 0)).hasDerivAt.comp_hasFDerivAt p
      (ContinuousLinearMap.proj (0:Fin 3) : Jet3 →L[ℝ] ℝ).hasFDerivAt
    have hd := hl.mul (ContinuousLinearMap.proj (2:Fin 3) : Jet3 →L[ℝ] ℝ).hasFDerivAt
    change HasFDerivAt (fun q : Jet3 => lam (q 0)*q 2) _ p at hd
    rw [hd.fderiv]
    simp
    ring
  have hc := hcontact p (Pi.single 0 1)
  simp only [jetContact,hD0,hD2,Pi.single_apply,ite_true,show (2:Fin 3) ≠ 0 by decide,
    ite_false,mul_one,zero_sub] at hc
  ext i
  fin_cases i
  · exact hfirst p
  · change F p 1 = lam (p 0)*p 1+deriv lam (p 0)*p 2
    linarith
  · exact hlast p

lemma contact_rescaling_zero_normal_form (F : Jet3 → Jet3) (hF : ContDiff ℝ ∞ F)
    (hcore : ∀ x, F (corePoint x) = corePoint x)
    (G : ℝ → Jet3 → Jet3) (hG : ContDiff ℝ ∞ (fun q : ℝ × Jet3 => G q.1 q.2))
    (hGnz : ∀ s : ℝ, s ≠ 0 → ∀ p, G s p = normalScale s⁻¹ (F (normalScale s p)))
    (hGzero : ∀ p, G 0 p = ![p 0,
      (fderiv ℝ F (corePoint (p 0)) (normalVector p)) 1,
      (fderiv ℝ F (corePoint (p 0)) (normalVector p)) 2])
    (U : Set Jet3) (hU : IsOpen U) (hcoreU : ∀ x, corePoint x ∈ U)
    (lam : Jet3 → ℝ) (hlam : ContDiff ℝ ∞ lam)
    (hcontact : ∀ p ∈ U, ∀ v, jetContact (F p) (fderiv ℝ F p v) = lam p * jetContact p v) :
    G 0 = coreLinear (lam ∘ corePoint) := by
  apply normal_form_from_contact (G 0) (hG.comp (contDiff_const.prodMk contDiff_id))
    (lam ∘ corePoint) (hlam.comp corePoint_contDiff)
  · intro p
    rw [hGzero]
    rfl
  · intro p
    have hc := hcontact (corePoint (p 0)) (hcoreU _) (normalVector p)
    rw [hcore] at hc
    have he := congrArg (fun v : Jet3 => v 2) (hGzero p)
    change G 0 p 2 = (fderiv ℝ F (corePoint (p 0)) (normalVector p)) 2 at he
    rw [he]
    simpa [jetContact,corePoint,normalVector] using hc
  · intro p v
    exact normal_rescaling_contact_zero F hF G hG hGnz U hU hcoreU lam hlam.continuous hcontact p v

end
end ContactTopology

namespace ContactTopology
open Set Function
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma coreLinear_contDiff (lam : ℝ → ℝ) (hlam : ContDiff ℝ ∞ lam) : ContDiff ℝ ∞ (coreLinear lam) := by
  have hd : ContDiff ℝ ∞ (deriv lam) := (contDiff_infty_iff_deriv.mp hlam).2
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_apply ℝ ℝ 0
  · change ContDiff ℝ ∞ (fun p : Jet3 => lam (p 0)*p 1+deriv lam (p 0)*p 2)
    fun_prop
  · change ContDiff ℝ ∞ (fun p : Jet3 => lam (p 0)*p 2)
    fun_prop

lemma coreLinear_contact (lam : ℝ → ℝ) (hlam : ContDiff ℝ ∞ lam) (p v : Jet3) :
    jetContact (coreLinear lam p) (fderiv ℝ (coreLinear lam) p v) = lam (p 0) * jetContact p v := by
  have hF := coreLinear_contDiff lam hlam
  have hD0 : (fderiv ℝ (coreLinear lam) p v) 0 = v 0 := by
    rw [← fderiv_coordinate (coreLinear lam) p v (hF.differentiable (by simp) p) 0]
    change fderiv ℝ (fun q : Jet3 => q 0) p v = v 0
    have hd := (ContinuousLinearMap.proj (0:Fin 3) : Jet3 →L[ℝ] ℝ).hasFDerivAt (x := p)
    change HasFDerivAt (fun q : Jet3 => q 0) _ p at hd
    rw [hd.fderiv]
    rfl
  have hD2 : (fderiv ℝ (coreLinear lam) p v) 2 = deriv lam (p 0)*v 0*p 2+lam (p 0)*v 2 := by
    rw [← fderiv_coordinate (coreLinear lam) p v (hF.differentiable (by simp) p) 2]
    change fderiv ℝ (fun q : Jet3 => lam (q 0)*q 2) p v = _
    have hl := (hlam.differentiable (by simp) (p 0)).hasDerivAt.comp_hasFDerivAt p
      (ContinuousLinearMap.proj (0:Fin 3) : Jet3 →L[ℝ] ℝ).hasFDerivAt
    have hd := hl.mul (ContinuousLinearMap.proj (2:Fin 3) : Jet3 →L[ℝ] ℝ).hasFDerivAt
    change HasFDerivAt (fun q : Jet3 => lam (q 0)*q 2) _ p at hd
    rw [hd.fderiv]
    simp
    ring
  simp only [jetContact,hD0,hD2]
  change deriv lam (p 0)*v 0*p 2+lam (p 0)*v 2-
    (lam (p 0)*p 1+deriv lam (p 0)*p 2)*v 0 = _
  ring

lemma coreLinear_injective (lam : ℝ → ℝ) (hlam : ∀ x, lam x ≠ 0) : Injective (coreLinear lam) := by
  intro p q he
  have hx := congrArg (fun v : Jet3 => v 0) he
  change p 0 = q 0 at hx
  have hz := congrArg (fun v : Jet3 => v 2) he
  change lam (p 0)*p 2 = lam (q 0)*q 2 at hz
  rw [← hx] at hz
  have hpq2 := (mul_left_cancel₀ (hlam (p 0))) hz
  have hy := congrArg (fun v : Jet3 => v 1) he
  change lam (p 0)*p 1+deriv lam (p 0)*p 2 = lam (q 0)*q 1+deriv lam (q 0)*q 2 at hy
  rw [← hx,← hpq2] at hy
  have hpq1 := (mul_left_cancel₀ (hlam (p 0))) (add_right_cancel hy)
  ext i
  fin_cases i
  · exact hx
  · exact hpq1
  · exact hpq2

def coreScaleFactor (lam : ℝ → ℝ) (s x : ℝ) : ℝ := s+(1-s)*lam x

def coreLinearPath (lam : ℝ → ℝ) (s : ℝ) (p : Jet3) : Jet3 :=
  ![p 0,coreScaleFactor lam s (p 0)*p 1+(1-s)*deriv lam (p 0)*p 2,
    coreScaleFactor lam s (p 0)*p 2]

lemma coreScaleFactor_contDiff (lam : ℝ → ℝ) (hlam : ContDiff ℝ ∞ lam) :
    ContDiff ℝ ∞ (fun q : ℝ × ℝ => coreScaleFactor lam q.1 q.2) := by
  unfold coreScaleFactor
  fun_prop

lemma coreScaleFactor_positive (lam : ℝ → ℝ) (hlam : ∀ x, 0 < lam x)
    (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) (x : ℝ) : 0 < coreScaleFactor lam s x := by
  unfold coreScaleFactor
  by_cases he : s = 1
  · simp [he]
  · have hlt : s < 1 := lt_of_le_of_ne hs.2 he
    exact add_pos_of_nonneg_of_pos hs.1 (mul_pos (sub_pos.mpr hlt) (hlam x))

lemma coreLinearPath_eq (lam : ℝ → ℝ) (hlam : ContDiff ℝ ∞ lam) (s : ℝ) :
    coreLinearPath lam s = coreLinear (coreScaleFactor lam s) := by
  have hd : ∀ x, deriv (coreScaleFactor lam s) x = (1-s)*deriv lam x := by
    intro x
    have hh := (hasDerivAt_const x s).add ((hlam.differentiable (by simp) x).hasDerivAt.const_mul (1-s))
    change HasDerivAt (coreScaleFactor lam s) _ x at hh
    simpa only [zero_add] using hh.deriv
  funext p
  simp only [coreLinearPath,coreLinear,hd]

lemma coreLinearPath_contDiff (lam : ℝ → ℝ) (hlam : ContDiff ℝ ∞ lam) :
    ContDiff ℝ ∞ (fun q : ℝ × Jet3 => coreLinearPath lam q.1 q.2) := by
  have hd : ContDiff ℝ ∞ (deriv lam) := (contDiff_infty_iff_deriv.mp hlam).2
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ ∞ (fun q : ℝ × Jet3 => q.2 0)
    exact (contDiff_apply ℝ ℝ 0).comp contDiff_snd
  · change ContDiff ℝ ∞ (fun q : ℝ × Jet3 =>
      coreScaleFactor lam q.1 (q.2 0)*q.2 1+(1-q.1)*deriv lam (q.2 0)*q.2 2)
    unfold coreScaleFactor
    fun_prop
  · change ContDiff ℝ ∞ (fun q : ℝ × Jet3 => coreScaleFactor lam q.1 (q.2 0)*q.2 2)
    unfold coreScaleFactor
    fun_prop

lemma coreLinearPath_contact (lam : ℝ → ℝ) (hlam : ContDiff ℝ ∞ lam) (s : ℝ) (p v : Jet3) :
    jetContact (coreLinearPath lam s p) (fderiv ℝ (coreLinearPath lam s) p v) =
      coreScaleFactor lam s (p 0)*jetContact p v := by
  rw [coreLinearPath_eq lam hlam s]
  exact coreLinear_contact _ ((coreScaleFactor_contDiff lam hlam).comp (contDiff_const.prodMk contDiff_id)) p v

lemma coreLinearPath_injective (lam : ℝ → ℝ) (hlam : ContDiff ℝ ∞ lam) (hpos : ∀ x, 0 < lam x)
    (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : Injective (coreLinearPath lam s) := by
  rw [coreLinearPath_eq lam hlam s]
  exact coreLinear_injective _ (fun x => (coreScaleFactor_positive lam hpos s hs x).ne')

lemma coreLinearPath_zero (lam : ℝ → ℝ) : coreLinearPath lam 0 = coreLinear lam := by
  funext p
  simp [coreLinearPath,coreLinear,coreScaleFactor]

lemma coreLinearPath_one (lam : ℝ → ℝ) : coreLinearPath lam 1 = id := by
  funext p
  ext i
  fin_cases i <;> simp [coreLinearPath,coreScaleFactor]

end
end ContactTopology

namespace ContactTopology
open Set Function
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
noncomputable section

def normalStrip (e : ℝ) : Set Jet3 := {p | |p 1| < e ∧ |p 2| < e}

lemma normalStrip_open (e : ℝ) : IsOpen (normalStrip e) :=
  (isOpen_lt ((continuous_apply 1).abs) continuous_const).inter
    (isOpen_lt ((continuous_apply 2).abs) continuous_const)

lemma normalStrip_core (e : ℝ) (he : 0 < e) (x : ℝ) : corePoint x ∈ normalStrip e := by
  simpa [normalStrip,corePoint] using And.intro he he

lemma normalScale_core (s x : ℝ) : normalScale s (corePoint x) = corePoint x := by
  simp [normalScale,corePoint]

lemma normalScale_inverse (s : ℝ) (hs : s ≠ 0) (p : Jet3) :
    normalScale s⁻¹ (normalScale s p) = p := by
  ext i
  fin_cases i <;> simp [normalScale,← mul_assoc,hs]

lemma normalScale_injective (s : ℝ) (hs : s ≠ 0) : Injective (normalScale s) :=
  (show LeftInverse (normalScale s⁻¹) (normalScale s) from normalScale_inverse s hs).injective

lemma normalScale_maps_strip (e s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
    MapsTo (normalScale s) (normalStrip e) (normalStrip e) := by
  intro p hp
  change |s*p 1| < e ∧ |s*p 2| < e
  rw [abs_mul,abs_mul,abs_of_nonneg hs.1]
  exact ⟨(mul_le_of_le_one_left (abs_nonneg _) hs.2).trans_lt hp.1,
    (mul_le_of_le_one_left (abs_nonneg _) hs.2).trans_lt hp.2⟩

lemma coreLinear_core (lam : ℝ → ℝ) (x : ℝ) : coreLinear lam (corePoint x) = corePoint x := by
  simp [coreLinear,corePoint]

lemma coreLinearPath_core (lam : ℝ → ℝ) (s x : ℝ) : coreLinearPath lam s (corePoint x) = corePoint x := by
  simp [coreLinearPath,corePoint]

/-- The two stages in the coordinate proof of the Legendrian neighborhood
fixing lemma: normal rescaling from F to its linear normal form, followed by
positive scalar interpolation to the identity. The input is contact only on
a normal strip; every slice is checked injective there and fixes the core. -/
lemma legendrian_core_two_stage_deformation (e : ℝ) (he : 0 < e)
    (F : Jet3 → Jet3) (hF : ContDiff ℝ ∞ F)
    (hcore : ∀ x, F (corePoint x) = corePoint x)
    (hinj : InjOn F (normalStrip e))
    (lam : Jet3 → ℝ) (hlam : ContDiff ℝ ∞ lam)
    (hpos : ∀ p ∈ normalStrip e, 0 < lam p)
    (hcontact : ∀ p ∈ normalStrip e, ∀ v,
      jetContact (F p) (fderiv ℝ F p v) = lam p*jetContact p v) :
    ∃ G L : ℝ → Jet3 → Jet3,
      ContDiff ℝ ∞ (fun q : ℝ × Jet3 => G q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × Jet3 => L q.1 q.2) ∧
      (∀ s : ℝ, s ≠ 0 → ∀ p, G s p = normalScale s⁻¹ (F (normalScale s p))) ∧
      L = coreLinearPath (lam ∘ corePoint) ∧
      G 1 = F ∧ G 0 = L 0 ∧ L 1 = id ∧
      (∀ s x, G s (corePoint x) = corePoint x ∧ L s (corePoint x) = corePoint x) ∧
      (∀ s ∈ Icc (0:ℝ) 1,
        InjOn (G s) (normalStrip e) ∧
        (∀ p ∈ normalStrip e, 0 < lam (normalScale s p)) ∧
        (∀ p ∈ normalStrip e, ∀ v,
          jetContact (G s p) (fderiv ℝ (G s) p v) = lam (normalScale s p)*jetContact p v)) ∧
      (∀ s ∈ Icc (0:ℝ) 1,
        Injective (L s) ∧
        (∀ x, 0 < coreScaleFactor (lam ∘ corePoint) s x) ∧
        (∀ p v, jetContact (L s p) (fderiv ℝ (L s) p v) =
          coreScaleFactor (lam ∘ corePoint) s (p 0)*jetContact p v)) := by
  obtain ⟨G,hG,hGnz,hGzero,hG1⟩ := smooth_normal_rescaling F hF hcore
  let l : ℝ → ℝ := lam ∘ corePoint
  have hl : ContDiff ℝ ∞ l := hlam.comp corePoint_contDiff
  have hlpos : ∀ x, 0 < l x := fun x => hpos _ (normalStrip_core e he x)
  have hzero : G 0 = coreLinear l := contact_rescaling_zero_normal_form F hF hcore G hG hGnz hGzero
    (normalStrip e) (normalStrip_open e) (normalStrip_core e he) lam hlam hcontact
  refine ⟨G,coreLinearPath l,hG,coreLinearPath_contDiff l hl,hGnz,rfl,funext hG1,?_,coreLinearPath_one l,?_,?_,?_⟩
  · rw [coreLinearPath_zero]
    exact hzero
  · intro s x
    refine ⟨?_,coreLinearPath_core l s x⟩
    by_cases hs : s = 0
    · rw [hs,hzero,coreLinear_core]
    · rw [hGnz s hs,normalScale_core,hcore,normalScale_core]
  · intro s hs
    refine ⟨?_,(fun p hp => hpos _ (normalScale_maps_strip e s hs hp)),?_⟩
    · intro p hp q hq hpq
      by_cases hsz : s = 0
      · rw [hsz,hzero] at hpq
        exact coreLinear_injective l (fun x => (hlpos x).ne') hpq
      · rw [hGnz s hsz p,hGnz s hsz q] at hpq
        have hFpFq := normalScale_injective s⁻¹ (inv_ne_zero hsz) hpq
        have hδ := hinj (normalScale_maps_strip e s hs hp) (normalScale_maps_strip e s hs hq) hFpFq
        exact normalScale_injective s hsz hδ
    · intro p hp v
      by_cases hsz : s = 0
      · rw [hsz,normalScale_zero]
        exact normal_rescaling_contact_zero F hF G hG hGnz (normalStrip e)
          (normalStrip_open e) (normalStrip_core e he) lam hlam.continuous hcontact p v
      · exact normal_rescaling_contact_nonzero F hF G hGnz (normalStrip e) lam hcontact s hsz p
          (normalScale_maps_strip e s hs hp) v
  · intro s hs
    exact ⟨coreLinearPath_injective l hl hlpos s hs,coreScaleFactor_positive l hlpos s hs,
      coreLinearPath_contact l hl s⟩

end
end ContactTopology

namespace ContactTopology
open Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma normalScale_translate (s : ℝ) (p : Jet3) :
    normalScale s (p+corePoint 1) = normalScale s p+corePoint 1 := by
  ext i
  fin_cases i <;> simp [normalScale,corePoint]

lemma normal_rescaling_periodic (F : Jet3 → Jet3)
    (hperiod : ∀ p, F (p+corePoint 1) = F p+corePoint 1)
    (G : ℝ → Jet3 → Jet3) (hG : ContDiff ℝ ∞ (fun q : ℝ × Jet3 => G q.1 q.2))
    (hGnz : ∀ s : ℝ, s ≠ 0 → ∀ p, G s p = normalScale s⁻¹ (F (normalScale s p))) :
    ∀ s p, G s (p+corePoint 1) = G s p+corePoint 1 := by
  have hnz : ∀ s : ℝ, s ≠ 0 → ∀ p, G s (p+corePoint 1) = G s p+corePoint 1 := by
    intro s hs p
    rw [hGnz s hs (p+corePoint 1),hGnz s hs p,normalScale_translate,hperiod,normalScale_translate]
  intro s p
  by_cases hs : s = 0
  · subst s
    have hl : Continuous (fun s => G s (p+corePoint 1)) :=
      hG.continuous.comp (continuous_id.prodMk continuous_const)
    have hr : Continuous (fun s => G s p+corePoint 1) :=
      (hG.continuous.comp (continuous_id.prodMk continuous_const)).add continuous_const
    have he : (fun s => G s (p+corePoint 1)) =ᶠ[𝓝[≠] (0:ℝ)] (fun s => G s p+corePoint 1) := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact hnz s hs p
    exact ((hl.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hr.continuousAt).mp he).eq_of_nhds
  · exact hnz s hs p

lemma core_factor_periodic (lam : ℝ → ℝ)
    (hperiod : ∀ p, coreLinear lam (p+corePoint 1) = coreLinear lam p+corePoint 1) :
    Periodic lam 1 := by
  intro x
  have he := congrArg (fun v : Jet3 => v 2) (hperiod ![x,0,1])
  simpa [coreLinear,corePoint] using he

lemma periodic_deriv (lam : ℝ → ℝ) (hlam : Differentiable ℝ lam) (hperiod : Periodic lam 1) :
    Periodic (deriv lam) 1 := by
  have heq : (fun x => lam (x+1)) = lam := funext hperiod
  intro x
  have hd := (hlam (x+1)).hasDerivAt.scomp (h := fun y : ℝ => y+1) x ((hasDerivAt_id x).add_const 1)
  change HasDerivAt (fun y => lam (y+1)) _ x at hd
  rw [heq] at hd
  simpa only [one_smul] using hd.deriv.symm

lemma coreLinearPath_periodic (lam : ℝ → ℝ) (hlam : ContDiff ℝ ∞ lam) (hperiod : Periodic lam 1) :
    ∀ s p, coreLinearPath lam s (p+corePoint 1) = coreLinearPath lam s p+corePoint 1 := by
  have hpder := periodic_deriv lam (hlam.differentiable (by simp)) hperiod
  intro s p
  ext i
  fin_cases i <;> simp [coreLinearPath,coreScaleFactor,corePoint,hperiod (p 0),hpder (p 0)]

end
end ContactTopology

namespace ContactTopology
open Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma concatenate_core_contact_deformations (U : Set Jet3) (F : Jet3 → Jet3)
    (G L : ℝ → Jet3 → Jet3)
    (hG : ContDiff ℝ ∞ (fun q : ℝ × Jet3 => G q.1 q.2))
    (hL : ContDiff ℝ ∞ (fun q : ℝ × Jet3 => L q.1 q.2))
    (hG1 : G 1 = F) (hmatch : G 0 = L 0) (hL1 : L 1 = id)
    (hcore : ∀ s x, G s (corePoint x) = corePoint x ∧ L s (corePoint x) = corePoint x)
    (hGper : ∀ s p, G s (p+corePoint 1) = G s p+corePoint 1)
    (hLper : ∀ s p, L s (p+corePoint 1) = L s p+corePoint 1)
    (hinjG : ∀ s ∈ Icc (0:ℝ) 1, InjOn (G s) U)
    (hinjL : ∀ s ∈ Icc (0:ℝ) 1, InjOn (L s) U)
    (hcG : ∀ s ∈ Icc (0:ℝ) 1, ∀ p ∈ U, ∃ a : ℝ, 0 < a ∧ ∀ v,
      jetContact (G s p) (fderiv ℝ (G s) p v) = a*jetContact p v)
    (hcL : ∀ s ∈ Icc (0:ℝ) 1, ∀ p ∈ U, ∃ a : ℝ, 0 < a ∧ ∀ v,
      jetContact (L s p) (fderiv ℝ (L s) p v) = a*jetContact p v) :
    ∃ H : ℝ → Jet3 → Jet3,
      ContDiff ℝ ∞ (fun q : ℝ × Jet3 => H q.1 q.2) ∧ H 0 = F ∧ H 1 = id ∧
      (∀ s x, H s (corePoint x) = corePoint x) ∧
      (∀ s p, H s (p+corePoint 1) = H s p+corePoint 1) ∧
      ∀ s ∈ Icc (0:ℝ) 1, InjOn (H s) U ∧ ∀ p ∈ U, ∃ a : ℝ, 0 < a ∧ ∀ v,
        jetContact (H s p) (fderiv ℝ (H s) p v) = a*jetContact p v := by
  let σ : ℝ → ℝ := fun t => Real.smoothTransition (4*t)
  let θ : ℝ → ℝ := fun t => Real.smoothTransition (4*t-3)
  have hσ : ContDiff ℝ ∞ σ := (Real.smoothTransition.contDiff (n := (⊤:ℕ∞))).comp (contDiff_const.mul contDiff_id)
  have hθ : ContDiff ℝ ∞ θ := (Real.smoothTransition.contDiff (n := (⊤:ℕ∞))).comp ((contDiff_const.mul contDiff_id).sub contDiff_const)
  have hσmem : ∀ t, 1-σ t ∈ Icc (0:ℝ) 1 := by
    intro t
    exact ⟨sub_nonneg.mpr (Real.smoothTransition.le_one _),sub_le_self _ (Real.smoothTransition.nonneg _)⟩
  have hθmem : ∀ t, θ t ∈ Icc (0:ℝ) 1 := fun t => ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩
  let H : ℝ → Jet3 → Jet3 := fun s p => if s ≤ 1/2 then G (1-σ s) p else L (θ s) p
  have hH : ContDiff ℝ ∞ (fun q : ℝ × Jet3 => H q.1 q.2) := by
    apply contDiff_iff_contDiffAt.mpr
    intro q
    rcases lt_trichotomy q.1 (1/2:ℝ) with hlo|hmid|hhi
    · have hn : ∀ᶠ z : ℝ × Jet3 in 𝓝 q, z.1 < 1/2 :=
        (isOpen_lt continuous_fst continuous_const).mem_nhds hlo
      have heq : (fun z : ℝ × Jet3 => H z.1 z.2) =ᶠ[𝓝 q] (fun z => G (1-σ z.1) z.2) := by
        filter_upwards [hn] with z hz
        simp only [H,if_pos hz.le]
      exact ((hG.comp (((contDiff_const.sub hσ).comp contDiff_fst).prodMk contDiff_snd)).contDiffAt).congr_of_eventuallyEq heq
    · have hn : ∀ᶠ z : ℝ × Jet3 in 𝓝 q, 1/4 < z.1 ∧ z.1 < 3/4 :=
        ((isOpen_lt continuous_const continuous_fst).inter (isOpen_lt continuous_fst continuous_const)).mem_nhds
          (show (1/4:ℝ) < q.1 ∧ q.1 < (3/4:ℝ) by rw [hmid]; constructor <;> norm_num)
      have heq : (fun z : ℝ × Jet3 => H z.1 z.2) =ᶠ[𝓝 q] (fun z => G 0 z.2) := by
        filter_upwards [hn] with z hz
        dsimp [H]
        split_ifs
        · have hσz : σ z.1 = 1 := Real.smoothTransition.one_of_one_le (by linarith)
          rw [hσz,sub_self]
        · have hθz : θ z.1 = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
          rw [hθz,← hmatch]
      exact ((hG.comp (contDiff_const.prodMk contDiff_snd)).contDiffAt).congr_of_eventuallyEq heq
    · have hn : ∀ᶠ z : ℝ × Jet3 in 𝓝 q, 1/2 < z.1 :=
        (isOpen_lt continuous_const continuous_fst).mem_nhds hhi
      have heq : (fun z : ℝ × Jet3 => H z.1 z.2) =ᶠ[𝓝 q] (fun z => L (θ z.1) z.2) := by
        filter_upwards [hn] with z hz
        simp only [H,if_neg (not_le.mpr hz)]
      exact ((hL.comp ((hθ.comp contDiff_fst).prodMk contDiff_snd)).contDiffAt).congr_of_eventuallyEq heq
  refine ⟨H,hH,?_,?_,?_,?_,?_⟩
  · have hσ0 : σ 0 = 0 := Real.smoothTransition.zero_of_nonpos (by norm_num)
    funext p
    simp only [H,show (0:ℝ) ≤ 1/2 by norm_num,if_true,hσ0,sub_zero,hG1]
  · have hθ1 : θ 1 = 1 := Real.smoothTransition.one_of_one_le (by norm_num)
    funext p
    simp only [H,show ¬(1:ℝ) ≤ 1/2 by norm_num,if_false,hθ1,hL1,Function.id_def]
  · intro s x
    dsimp [H]
    split_ifs
    · exact (hcore _ x).1
    · exact (hcore _ x).2
  · intro s p
    dsimp [H]
    split_ifs
    · exact hGper _ p
    · exact hLper _ p
  · intro s hs
    by_cases hlow : s ≤ 1/2
    · have heq : H s = G (1-σ s) := by funext p; simp only [H,if_pos hlow]
      rw [heq]
      exact ⟨hinjG _ (hσmem s),hcG _ (hσmem s)⟩
    · have heq : H s = L (θ s) := by funext p; simp only [H,if_neg hlow]
      rw [heq]
      exact ⟨hinjL _ (hθmem s),hcL _ (hθmem s)⟩

end
end ContactTopology

namespace ContactTopology
open Set Function
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Coordinate core-fixing contact deformation on the universal cover of a
standard Legendrian solid torus. Periodicity permits descent to the circle.
This is the local embedding step of Min's neighborhood-fixing Lemma2.7(2),
before the separate ambient contact-isotopy extension theorem is applied. -/
lemma periodic_legendrian_core_contact_deformation (e : ℝ) (he : 0 < e)
    (F : Jet3 → Jet3) (hF : ContDiff ℝ ∞ F)
    (hcore : ∀ x, F (corePoint x) = corePoint x)
    (hperiod : ∀ p, F (p+corePoint 1) = F p+corePoint 1)
    (hinj : InjOn F (normalStrip e))
    (lam : Jet3 → ℝ) (hlam : ContDiff ℝ ∞ lam)
    (hpos : ∀ p ∈ normalStrip e, 0 < lam p)
    (hcontact : ∀ p ∈ normalStrip e, ∀ v,
      jetContact (F p) (fderiv ℝ F p v) = lam p*jetContact p v) :
    ∃ H : ℝ → Jet3 → Jet3,
      ContDiff ℝ ∞ (fun q : ℝ × Jet3 => H q.1 q.2) ∧ H 0 = F ∧ H 1 = id ∧
      (∀ s x, H s (corePoint x) = corePoint x) ∧
      (∀ s p, H s (p+corePoint 1) = H s p+corePoint 1) ∧
      ∀ s ∈ Icc (0:ℝ) 1, InjOn (H s) (normalStrip e) ∧
        ∀ p ∈ normalStrip e, ∃ a : ℝ, 0 < a ∧ ∀ v,
          jetContact (H s p) (fderiv ℝ (H s) p v) = a*jetContact p v := by
  obtain ⟨G,L,hG,hL,hGnz,hLdef,hG1,hmatch,hL1,hcoreGL,hGc,hLc⟩ :=
    legendrian_core_two_stage_deformation e he F hF hcore hinj lam hlam hpos hcontact
  have hGper := normal_rescaling_periodic F hperiod G hG hGnz
  have hGzero : G 0 = coreLinear (lam ∘ corePoint) := by
    rw [hmatch,hLdef,coreLinearPath_zero]
  have hlper : Periodic (lam ∘ corePoint) 1 := by
    apply core_factor_periodic
    intro p
    rw [← hGzero]
    exact hGper 0 p
  have hLper : ∀ s p, L s (p+corePoint 1) = L s p+corePoint 1 := by
    rw [hLdef]
    exact coreLinearPath_periodic _ (hlam.comp corePoint_contDiff) hlper
  apply concatenate_core_contact_deformations (normalStrip e) F G L hG hL hG1 hmatch hL1 hcoreGL hGper hLper
  · intro s hs
    exact (hGc s hs).1
  · intro s hs
    exact (hLc s hs).1.injOn
  · intro s hs p hp
    exact ⟨lam (normalScale s p),(hGc s hs).2.1 p hp,(hGc s hs).2.2 p hp⟩
  · intro s hs p hp
    exact ⟨coreScaleFactor (lam ∘ corePoint) s (p 0),(hLc s hs).2.1 _,(hLc s hs).2.2 p⟩

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

lemma jet_contact_exterior_identity (F : Jet3 → Jet3) (hF : ContDiff ℝ ∞ F)
    (U : Set Jet3) (hU : IsOpen U) (lam : Jet3 → ℝ) (hlam : ContDiff ℝ ∞ lam)
    (hcontact : ∀ p ∈ U, ∀ v, jetContact (F p) (fderiv ℝ F p v) = lam p*jetContact p v)
    (p : Jet3) (hp : p ∈ U) (u v : Jet3) :
    (fderiv ℝ F p u) 0*(fderiv ℝ F p v) 1-(fderiv ℝ F p u) 1*(fderiv ℝ F p v) 0 =
      fderiv ℝ lam p u*jetContact p v-fderiv ℝ lam p v*jetContact p u+
        lam p*(u 0*v 1-u 1*v 0) := by
  have heq : (fun q => (jetOneForm (F q)).comp (fderiv ℝ F q)) =ᶠ[𝓝 p]
      (fun q => lam q • jetOneForm q) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    ext w
    exact hcontact q hq w
  have hpb := ContactCalculus.exterior_pairing_pullback jetOneForm F p u v
    (jetOneForm_contDiff.differentiable (by simp) _)
    (hF.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  rw [heq.fderiv_eq,weighted_jetOneForm_fderiv lam p u v (hlam.differentiable (by simp) p),
    weighted_jetOneForm_fderiv lam p v u (hlam.differentiable (by simp) p),
    jetOneForm_fderiv,jetOneForm_fderiv] at hpb
  nlinarith [hpb]

/-- A positive contact pullback identity forces full derivative rank. -/
lemma jet_contact_derivative_injective (F : Jet3 → Jet3) (hF : ContDiff ℝ ∞ F)
    (U : Set Jet3) (hU : IsOpen U) (lam : Jet3 → ℝ) (hlam : ContDiff ℝ ∞ lam)
    (hcontact : ∀ p ∈ U, ∀ v, jetContact (F p) (fderiv ℝ F p v) = lam p*jetContact p v)
    (p : Jet3) (hp : p ∈ U) (hpos : 0 < lam p) : Injective (fderiv ℝ F p) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro u hu
  have hαu : jetContact p u = 0 := by
    have hm : lam p*jetContact p u = 0 := by
      rw [← hcontact p hp u,hu]
      simp [jetContact]
    exact (mul_eq_zero.mp hm).resolve_left hpos.ne'
  have he₁ := jet_contact_exterior_identity F hF U hU lam hlam hcontact p hp u (Pi.single 1 1)
  rw [hαu] at he₁
  have hm₀ : lam p*u 0 = 0 := by
    simpa [hu,jetContact] using he₁.symm
  have hu₀ : u 0 = 0 := (mul_eq_zero.mp hm₀).resolve_left hpos.ne'
  let v : Jet3 := Pi.single 0 1+p 1 • Pi.single 2 1
  have hv : jetContact p v = 0 := by simp [v,jetContact]
  have he₂ := jet_contact_exterior_identity F hF U hU lam hlam hcontact p hp u v
  rw [hαu,hv] at he₂
  have hm₁ : lam p*u 1 = 0 := by
    simp [hu,v] at he₂
    exact mul_eq_zero.mpr he₂
  have hu₁ : u 1 = 0 := (mul_eq_zero.mp hm₁).resolve_left hpos.ne'
  have hu₂ : u 2 = 0 := by simpa [jetContact,hu₀] using hαu
  ext i
  fin_cases i
  · exact hu₀
  · exact hu₁
  · exact hu₂

def jetContactFactor (F : Jet3 → Jet3) (p : Jet3) : ℝ :=
  jetContact (F p) (fderiv ℝ F p (Pi.single 2 1))

lemma jetContactFactor_contDiff (F : Jet3 → Jet3) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (jetContactFactor F) := by
  have hd : ContDiff ℝ ∞ (fun p => fderiv ℝ F p (Pi.single 2 1)) :=
    (hF.fderiv_right (by simp)).clm_apply contDiff_const
  unfold jetContactFactor jetContact
  exact ((contDiff_apply ℝ ℝ 2).comp hd).sub
    (((contDiff_apply ℝ ℝ 1).comp hF).mul ((contDiff_apply ℝ ℝ 0).comp hd))

lemma jet_contact_derivative_injective_of_positive_factor
    (F : Jet3 → Jet3) (hF : ContDiff ℝ ∞ F) (U : Set Jet3) (hU : IsOpen U)
    (hcontact : ∀ p ∈ U, ∃ a : ℝ, 0 < a ∧ ∀ v,
      jetContact (F p) (fderiv ℝ F p v) = a*jetContact p v) :
    ∀ p ∈ U, Injective (fderiv ℝ F p) := by
  have hfactor : ∀ p ∈ U, 0 < jetContactFactor F p ∧ ∀ v,
      jetContact (F p) (fderiv ℝ F p v) = jetContactFactor F p*jetContact p v := by
    intro p hp
    obtain ⟨a,ha,hc⟩ := hcontact p hp
    have he : jetContactFactor F p = a := by
      simpa [jetContactFactor,jetContact] using hc (Pi.single 2 1)
    rw [he]
    exact ⟨ha,hc⟩
  intro p hp
  exact jet_contact_derivative_injective F hF U hU (jetContactFactor F)
    (jetContactFactor_contDiff F hF) (fun q hq => (hfactor q hq).2) p hp (hfactor p hp).1

end
end ContactTopology

namespace ContactTopology
open Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma smooth_local_inverse_of_injective_derivative {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : E → E) (hF : ContDiff ℝ ∞ F) (p : E) (hinj : Injective (fderiv ℝ F p)) :
    ∃ R : E → E, ContDiffAt ℝ ∞ R (F p) ∧ R (F p) = p ∧
      (∀ᶠ x in 𝓝 p, R (F x) = x) ∧ (∀ᶠ y in 𝓝 (F p), F (R y) = y) := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  let A : E ≃L[ℝ] E := (LinearEquiv.ofBijective (fderiv ℝ F p).toLinearMap
    ⟨hinj,LinearMap.injective_iff_surjective.mp hinj⟩).toContinuousLinearEquiv
  have hd : HasFDerivAt F (A : E →L[ℝ] E) p := (hF.differentiable (by simp) p).hasFDerivAt
  let e := hF.contDiffAt.toOpenPartialHomeomorph F hd (by simp)
  have he : (e : E → E) = F := hF.contDiffAt.toOpenPartialHomeomorph_coe hd (by simp)
  have hp : p ∈ e.source := hF.contDiffAt.mem_toOpenPartialHomeomorph_source hd (by simp)
  have hFp : F p ∈ e.target := hF.contDiffAt.image_mem_toOpenPartialHomeomorph_target hd (by simp)
  refine ⟨e.symm,?_,?_,?_,?_⟩
  · change ContDiffAt ℝ ∞ (hF.contDiffAt.localInverse hd (by simp)) (F p)
    exact hF.contDiffAt.to_localInverse hd (by simp)
  · have hh := e.left_inv hp
    rwa [he] at hh
  · filter_upwards [e.open_source.mem_nhds hp] with x hx
    have hh := e.left_inv hx
    rwa [he] at hh
  · filter_upwards [e.open_target.mem_nhds hFp] with y hy
    have hh := e.right_inv hy
    rwa [he] at hh

lemma family_world_derivative_injective (H : ℝ → Jet3 → Jet3)
    (hH : ContDiff ℝ ∞ (fun q : ℝ × Jet3 => H q.1 q.2)) (t : ℝ) (p : Jet3)
    (hinj : Injective (fderiv ℝ (H t) p)) :
    Injective (fderiv ℝ (fun q : ℝ × Jet3 => (q.1,H q.1 q.2)) (t,p)) := by
  have hd := (hasFDerivAt_fst (𝕜 := ℝ) (p := (t,p))).prodMk
    (hH.differentiable (by simp) (t,p)).hasFDerivAt
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  rw [hd.fderiv] at hv
  change (v.1,fderiv ℝ (fun q : ℝ × Jet3 => H q.1 q.2) (t,p) v) = (0,0) at hv
  have hv₁ : v.1 = 0 := congrArg (fun q : ℝ × Jet3 => q.1) hv
  have hv₂ := congrArg (fun q : ℝ × Jet3 => q.2) hv
  have hvrep : v = (0,v.2) := Prod.ext hv₁ rfl
  rw [hvrep,← joint_fderiv_slice_apply H hH t p v.2] at hv₂
  have hpv : v.2 = 0 := hinj (by simpa only [map_zero] using hv₂)
  exact Prod.ext hv₁ hpv

/-- A smooth contact family has a jointly smooth local inverse around every
point where the contact factor is positive, including endpoint parameters. -/
lemma contact_family_joint_local_inverse (H : ℝ → Jet3 → Jet3)
    (hH : ContDiff ℝ ∞ (fun q : ℝ × Jet3 => H q.1 q.2))
    (U : Set Jet3) (hU : IsOpen U) (t : ℝ)
    (hcontact : ∀ p ∈ U, ∃ a : ℝ, 0 < a ∧ ∀ v,
      jetContact (H t p) (fderiv ℝ (H t) p v) = a*jetContact p v)
    (p : Jet3) (hp : p ∈ U) :
    ∃ r : ℝ × Jet3 → Jet3,
      ContDiffAt ℝ ∞ r (t,H t p) ∧ r (t,H t p) = p ∧
      (∀ᶠ q : ℝ × Jet3 in 𝓝 (t,p), r (q.1,H q.1 q.2) = q.2) ∧
      (∀ᶠ q : ℝ × Jet3 in 𝓝 (t,H t p), H q.1 (r q) = q.2) ∧
      (∀ᶠ q : ℝ × Jet3 in 𝓝 (t,H t p), r q ∈ U) := by
  have hHt : ContDiff ℝ ∞ (H t) := hH.comp (contDiff_const.prodMk contDiff_id)
  have hinj := jet_contact_derivative_injective_of_positive_factor (H t) hHt U hU hcontact p hp
  let W : ℝ × Jet3 → ℝ × Jet3 := fun q => (q.1,H q.1 q.2)
  have hW : ContDiff ℝ ∞ W := contDiff_fst.prodMk hH
  obtain ⟨R,hR,hRa,hleft,hright⟩ := smooth_local_inverse_of_injective_derivative W hW (t,p)
    (family_world_derivative_injective H hH t p hinj)
  have hsmooth : ContDiffAt ℝ ∞ (fun q => (R q).2) (t,H t p) :=
    contDiffAt_snd.comp (t,H t p) hR
  have hpoint : (R (t,H t p)).2 = p := congrArg Prod.snd hRa
  refine ⟨fun q => (R q).2,hsmooth,hpoint,?_,?_,?_⟩
  · filter_upwards [hleft] with q hq
    exact congrArg Prod.snd hq
  · filter_upwards [hright] with q hq
    have htime := congrArg Prod.fst hq
    change (R q).1 = q.1 at htime
    have hspace := congrArg Prod.snd hq
    change H (R q).1 (R q).2 = q.2 at hspace
    rwa [htime] at hspace
  · apply hsmooth.continuousAt.preimage_mem_nhds
    apply hU.mem_nhds
    rwa [hpoint]

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

lemma smooth_local_inverse_of_equal_dimension_derivative {E V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (F : E → V) (hF : ContDiff ℝ ∞ F) (p : E) (hdim : Module.finrank ℝ E = Module.finrank ℝ V) (hinj : Injective (fderiv ℝ F p)) :
    ∃ R : V → E, ContDiffAt ℝ ∞ R (F p) ∧ R (F p) = p ∧
      (∀ᶠ x in 𝓝 p, R (F x) = x) ∧ (∀ᶠ y in 𝓝 (F p), F (R y) = y) := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  letI : CompleteSpace V := FiniteDimensional.complete ℝ V
  let A : E ≃L[ℝ] V := (LinearEquiv.ofBijective (fderiv ℝ F p).toLinearMap
    ⟨hinj,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj⟩).toContinuousLinearEquiv
  have hd : HasFDerivAt F (A : E →L[ℝ] V) p := (hF.differentiable (by simp) p).hasFDerivAt
  let e := hF.contDiffAt.toOpenPartialHomeomorph F hd (by simp)
  have he : (e : E → V) = F := hF.contDiffAt.toOpenPartialHomeomorph_coe hd (by simp)
  have hp : p ∈ e.source := hF.contDiffAt.mem_toOpenPartialHomeomorph_source hd (by simp)
  have hFp : F p ∈ e.target := hF.contDiffAt.image_mem_toOpenPartialHomeomorph_target hd (by simp)
  refine ⟨e.symm,?_,?_,?_,?_⟩
  · change ContDiffAt ℝ ∞ (hF.contDiffAt.localInverse hd (by simp)) (F p)
    exact hF.contDiffAt.to_localInverse hd (by simp)
  · have hh := e.left_inv hp
    rwa [he] at hh
  · filter_upwards [e.open_source.mem_nhds hp] with x hx
    have hh := e.left_inv hx
    rwa [he] at hh
  · filter_upwards [e.open_target.mem_nhds hFp] with y hy
    have hh := e.right_inv hy
    rwa [he] at hh


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

lemma legendrianChartRadialExtension_derivative_injective (p : Jet3) :
    Injective (fderiv ℝ legendrianChartRadialExtension (1,p)) := by
  have hd := (hasFDerivAt_fst (𝕜 := ℝ) (p := ((1:ℝ),p))).smul
    ((legendrianSphereChart_contDiff.differentiable (by simp) p).hasFDerivAt.comp (1,p) hasFDerivAt_snd)
  change HasFDerivAt legendrianChartRadialExtension _ (1,p) at hd
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  rw [hd.fderiv] at hv
  change (1:ℝ) • fderiv ℝ legendrianSphereChart p v.2+v.1 • legendrianSphereChart p = 0 at hv
  rw [one_smul,add_comm] at hv
  have hdot := congrArg (phaseDot (legendrianSphereChart p)) hv
  have heq : phaseDot (legendrianSphereChart p)
      (v.1 • legendrianSphereChart p+fderiv ℝ legendrianSphereChart p v.2) =
      v.1*phaseDot (legendrianSphereChart p) (legendrianSphereChart p)+
        phaseDot (legendrianSphereChart p) (fderiv ℝ legendrianSphereChart p v.2) := by
    simp [phaseDot]
    ring
  rw [heq,sphere_dot_self (legendrianSphereChart_mem p),legendrianSphereChart_fderiv_tangent] at hdot
  have hv₁ : v.1 = 0 := by simpa [phaseDot] using hdot
  rw [hv₁,zero_smul,zero_add] at hv
  have hv₂ : v.2 = 0 := (legendrianSphereChart_derivative_injective p) (by simpa using hv)
  exact Prod.ext hv₁ hv₂

/-- Genuine smooth local coordinates on the sphere, obtained from an ambient
four-dimensional radial extension and the inverse-function theorem. -/
lemma legendrianSphereChart_local_inverse (p : Jet3) :
    ∃ r : Phase → Jet3, ContDiffAt ℝ ∞ r (legendrianSphereChart p) ∧
      r (legendrianSphereChart p) = p ∧
      (∀ᶠ q in 𝓝 p, r (legendrianSphereChart q) = q) ∧
      (∀ᶠ y in 𝓝 (legendrianSphereChart p), y ∈ unitThreeSphere →
        legendrianSphereChart (r y) = y) := by
  have hdim : Module.finrank ℝ (ℝ × Jet3) = Module.finrank ℝ Phase := by
    simp [Jet3,Phase,Module.finrank_prod,Module.finrank_pi]
  obtain ⟨R,hR,hRp,hleft,hright⟩ := smooth_local_inverse_of_equal_dimension_derivative
    legendrianChartRadialExtension legendrianChartRadialExtension_contDiff (1,p) hdim
    (legendrianChartRadialExtension_derivative_injective p)
  have hval : legendrianChartRadialExtension (1,p) = legendrianSphereChart p := by
    simp [legendrianChartRadialExtension]
  rw [hval] at hR hRp hright
  have hsmooth : ContDiffAt ℝ ∞ (fun y => (R y).2) (legendrianSphereChart p) := contDiffAt_snd.comp _ hR
  refine ⟨fun y => (R y).2,hsmooth,congrArg Prod.snd hRp,?_,?_⟩
  · have hi : Tendsto (fun q : Jet3 => ((1:ℝ),q)) (𝓝 p) (𝓝 (1,p)) :=
      (continuous_const.prodMk continuous_id).continuousAt
    filter_upwards [hi.eventually hleft] with q hq
    have hh := congrArg Prod.snd hq
    simpa [legendrianChartRadialExtension] using hh
  · have hpos : ∀ᶠ y in 𝓝 (legendrianSphereChart p), 0 < (R y).1 := by
      apply ((continuous_fst.continuousAt.comp hR.continuousAt).eventually (lt_mem_nhds (show (0:ℝ) < (R (legendrianSphereChart p)).1 by rw [hRp]; norm_num)))
    filter_upwards [hright,hpos] with y hy hp
    intro hys
    change (R y).1 • legendrianSphereChart (R y).2 = y at hy
    have hunit := sphere_dot_self hys
    have hchart := sphere_dot_self (legendrianSphereChart_mem (R y).2)
    have hsq : (R y).1^2 = 1 := by
      have hscale : phaseDot ((R y).1 • legendrianSphereChart (R y).2)
          ((R y).1 • legendrianSphereChart (R y).2) =
          (R y).1^2*phaseDot (legendrianSphereChart (R y).2) (legendrianSphereChart (R y).2) := by
        simp [phaseDot]
        ring
      rwa [← hy,hscale,hchart,mul_one] at hunit
    have hr : (R y).1 = 1 := by nlinarith
    simpa only [hr,one_smul] using hy

end
end ContactTopology

namespace ContactTopology
open Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma normalScale_translate_with_period (a : ℝ) (s : ℝ) (p : Jet3) :
    normalScale s (p+corePoint a) = normalScale s p+corePoint a := by
  ext i
  fin_cases i <;> simp [normalScale,corePoint]

lemma normal_rescaling_periodic_with_period (a : ℝ) (F : Jet3 → Jet3)
    (hperiod : ∀ p, F (p+corePoint a) = F p+corePoint a)
    (G : ℝ → Jet3 → Jet3) (hG : ContDiff ℝ ∞ (fun q : ℝ × Jet3 => G q.1 q.2))
    (hGnz : ∀ s : ℝ, s ≠ 0 → ∀ p, G s p = normalScale s⁻¹ (F (normalScale s p))) :
    ∀ s p, G s (p+corePoint a) = G s p+corePoint a := by
  have hnz : ∀ s : ℝ, s ≠ 0 → ∀ p, G s (p+corePoint a) = G s p+corePoint a := by
    intro s hs p
    rw [hGnz s hs (p+corePoint a),hGnz s hs p,normalScale_translate_with_period,hperiod,normalScale_translate_with_period]
  intro s p
  by_cases hs : s = 0
  · subst s
    have hl : Continuous (fun s => G s (p+corePoint a)) :=
      hG.continuous.comp (continuous_id.prodMk continuous_const)
    have hr : Continuous (fun s => G s p+corePoint a) :=
      (hG.continuous.comp (continuous_id.prodMk continuous_const)).add continuous_const
    have he : (fun s => G s (p+corePoint a)) =ᶠ[𝓝[≠] (0:ℝ)] (fun s => G s p+corePoint a) := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact hnz s hs p
    exact ((hl.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hr.continuousAt).mp he).eq_of_nhds
  · exact hnz s hs p

lemma core_factor_periodic_with_period (a : ℝ) (lam : ℝ → ℝ)
    (hperiod : ∀ p, coreLinear lam (p+corePoint a) = coreLinear lam p+corePoint a) :
    Periodic lam a := by
  intro x
  have he := congrArg (fun v : Jet3 => v 2) (hperiod ![x,0,1])
  simpa [coreLinear,corePoint] using he

lemma periodic_deriv_with_period (a : ℝ) (lam : ℝ → ℝ) (hlam : Differentiable ℝ lam) (hperiod : Periodic lam a) :
    Periodic (deriv lam) a := by
  have heq : (fun x => lam (x+a)) = lam := funext hperiod
  intro x
  have hd := (hlam (x+a)).hasDerivAt.scomp (h := fun y : ℝ => y+a) x ((hasDerivAt_id x).add_const a)
  change HasDerivAt (fun y => lam (y+a)) _ x at hd
  rw [heq] at hd
  simpa only [one_smul] using hd.deriv.symm

lemma coreLinearPath_periodic_with_period (a : ℝ) (lam : ℝ → ℝ) (hlam : ContDiff ℝ ∞ lam) (hperiod : Periodic lam a) :
    ∀ s p, coreLinearPath lam s (p+corePoint a) = coreLinearPath lam s p+corePoint a := by
  have hpder := periodic_deriv_with_period a lam (hlam.differentiable (by simp)) hperiod
  intro s p
  ext i
  fin_cases i <;> simp [coreLinearPath,coreScaleFactor,corePoint,hperiod (p 0),hpder (p 0)]

end
end ContactTopology

namespace ContactTopology
open Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma concatenate_core_contact_deformations_with_period (a : ℝ) (U : Set Jet3) (F : Jet3 → Jet3)
    (G L : ℝ → Jet3 → Jet3)
    (hG : ContDiff ℝ ∞ (fun q : ℝ × Jet3 => G q.1 q.2))
    (hL : ContDiff ℝ ∞ (fun q : ℝ × Jet3 => L q.1 q.2))
    (hG1 : G 1 = F) (hmatch : G 0 = L 0) (hL1 : L 1 = id)
    (hcore : ∀ s x, G s (corePoint x) = corePoint x ∧ L s (corePoint x) = corePoint x)
    (hGper : ∀ s p, G s (p+corePoint a) = G s p+corePoint a)
    (hLper : ∀ s p, L s (p+corePoint a) = L s p+corePoint a)
    (hinjG : ∀ s ∈ Icc (0:ℝ) 1, InjOn (G s) U)
    (hinjL : ∀ s ∈ Icc (0:ℝ) 1, InjOn (L s) U)
    (hcG : ∀ s ∈ Icc (0:ℝ) 1, ∀ p ∈ U, ∃ a : ℝ, 0 < a ∧ ∀ v,
      jetContact (G s p) (fderiv ℝ (G s) p v) = a*jetContact p v)
    (hcL : ∀ s ∈ Icc (0:ℝ) 1, ∀ p ∈ U, ∃ a : ℝ, 0 < a ∧ ∀ v,
      jetContact (L s p) (fderiv ℝ (L s) p v) = a*jetContact p v) :
    ∃ H : ℝ → Jet3 → Jet3,
      ContDiff ℝ ∞ (fun q : ℝ × Jet3 => H q.1 q.2) ∧ H 0 = F ∧ H 1 = id ∧
      (∀ s x, H s (corePoint x) = corePoint x) ∧
      (∀ s p, H s (p+corePoint a) = H s p+corePoint a) ∧
      ∀ s ∈ Icc (0:ℝ) 1, InjOn (H s) U ∧ ∀ p ∈ U, ∃ a : ℝ, 0 < a ∧ ∀ v,
        jetContact (H s p) (fderiv ℝ (H s) p v) = a*jetContact p v := by
  let σ : ℝ → ℝ := fun t => Real.smoothTransition (4*t)
  let θ : ℝ → ℝ := fun t => Real.smoothTransition (4*t-3)
  have hσ : ContDiff ℝ ∞ σ := (Real.smoothTransition.contDiff (n := (⊤:ℕ∞))).comp (contDiff_const.mul contDiff_id)
  have hθ : ContDiff ℝ ∞ θ := (Real.smoothTransition.contDiff (n := (⊤:ℕ∞))).comp ((contDiff_const.mul contDiff_id).sub contDiff_const)
  have hσmem : ∀ t, 1-σ t ∈ Icc (0:ℝ) 1 := by
    intro t
    exact ⟨sub_nonneg.mpr (Real.smoothTransition.le_one _),sub_le_self _ (Real.smoothTransition.nonneg _)⟩
  have hθmem : ∀ t, θ t ∈ Icc (0:ℝ) 1 := fun t => ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩
  let H : ℝ → Jet3 → Jet3 := fun s p => if s ≤ 1/2 then G (1-σ s) p else L (θ s) p
  have hH : ContDiff ℝ ∞ (fun q : ℝ × Jet3 => H q.1 q.2) := by
    apply contDiff_iff_contDiffAt.mpr
    intro q
    rcases lt_trichotomy q.1 (1/2:ℝ) with hlo|hmid|hhi
    · have hn : ∀ᶠ z : ℝ × Jet3 in 𝓝 q, z.1 < 1/2 :=
        (isOpen_lt continuous_fst continuous_const).mem_nhds hlo
      have heq : (fun z : ℝ × Jet3 => H z.1 z.2) =ᶠ[𝓝 q] (fun z => G (1-σ z.1) z.2) := by
        filter_upwards [hn] with z hz
        simp only [H,if_pos hz.le]
      exact ((hG.comp (((contDiff_const.sub hσ).comp contDiff_fst).prodMk contDiff_snd)).contDiffAt).congr_of_eventuallyEq heq
    · have hn : ∀ᶠ z : ℝ × Jet3 in 𝓝 q, 1/4 < z.1 ∧ z.1 < 3/4 :=
        ((isOpen_lt continuous_const continuous_fst).inter (isOpen_lt continuous_fst continuous_const)).mem_nhds
          (show (1/4:ℝ) < q.1 ∧ q.1 < (3/4:ℝ) by rw [hmid]; constructor <;> norm_num)
      have heq : (fun z : ℝ × Jet3 => H z.1 z.2) =ᶠ[𝓝 q] (fun z => G 0 z.2) := by
        filter_upwards [hn] with z hz
        dsimp [H]
        split_ifs
        · have hσz : σ z.1 = 1 := Real.smoothTransition.one_of_one_le (by linarith)
          rw [hσz,sub_self]
        · have hθz : θ z.1 = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
          rw [hθz,← hmatch]
      exact ((hG.comp (contDiff_const.prodMk contDiff_snd)).contDiffAt).congr_of_eventuallyEq heq
    · have hn : ∀ᶠ z : ℝ × Jet3 in 𝓝 q, 1/2 < z.1 :=
        (isOpen_lt continuous_const continuous_fst).mem_nhds hhi
      have heq : (fun z : ℝ × Jet3 => H z.1 z.2) =ᶠ[𝓝 q] (fun z => L (θ z.1) z.2) := by
        filter_upwards [hn] with z hz
        simp only [H,if_neg (not_le.mpr hz)]
      exact ((hL.comp ((hθ.comp contDiff_fst).prodMk contDiff_snd)).contDiffAt).congr_of_eventuallyEq heq
  refine ⟨H,hH,?_,?_,?_,?_,?_⟩
  · have hσ0 : σ 0 = 0 := Real.smoothTransition.zero_of_nonpos (by norm_num)
    funext p
    simp only [H,show (0:ℝ) ≤ 1/2 by norm_num,if_true,hσ0,sub_zero,hG1]
  · have hθ1 : θ 1 = 1 := Real.smoothTransition.one_of_one_le (by norm_num)
    funext p
    simp only [H,show ¬(1:ℝ) ≤ 1/2 by norm_num,if_false,hθ1,hL1,Function.id_def]
  · intro s x
    dsimp [H]
    split_ifs
    · exact (hcore _ x).1
    · exact (hcore _ x).2
  · intro s p
    dsimp [H]
    split_ifs
    · exact hGper _ p
    · exact hLper _ p
  · intro s hs
    by_cases hlow : s ≤ 1/2
    · have heq : H s = G (1-σ s) := by funext p; simp only [H,if_pos hlow]
      rw [heq]
      exact ⟨hinjG _ (hσmem s),hcG _ (hσmem s)⟩
    · have heq : H s = L (θ s) := by funext p; simp only [H,if_neg hlow]
      rw [heq]
      exact ⟨hinjL _ (hθmem s),hcL _ (hθmem s)⟩

end
end ContactTopology

namespace ContactTopology
open Set Function
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Coordinate core-fixing contact deformation on the universal cover of a
standard Legendrian solid torus. Periodicity permits descent to the circle.
This is the local embedding step of Min's neighborhood-fixing Lemma2.7(2),
before the separate ambient contact-isotopy extension theorem is applied. -/
lemma legendrian_core_contact_deformation_with_period (a : ℝ) (e : ℝ) (he : 0 < e)
    (F : Jet3 → Jet3) (hF : ContDiff ℝ ∞ F)
    (hcore : ∀ x, F (corePoint x) = corePoint x)
    (hperiod : ∀ p, F (p+corePoint a) = F p+corePoint a)
    (hinj : InjOn F (normalStrip e))
    (lam : Jet3 → ℝ) (hlam : ContDiff ℝ ∞ lam)
    (hpos : ∀ p ∈ normalStrip e, 0 < lam p)
    (hcontact : ∀ p ∈ normalStrip e, ∀ v,
      jetContact (F p) (fderiv ℝ F p v) = lam p*jetContact p v) :
    ∃ H : ℝ → Jet3 → Jet3,
      ContDiff ℝ ∞ (fun q : ℝ × Jet3 => H q.1 q.2) ∧ H 0 = F ∧ H 1 = id ∧
      (∀ s x, H s (corePoint x) = corePoint x) ∧
      (∀ s p, H s (p+corePoint a) = H s p+corePoint a) ∧
      ∀ s ∈ Icc (0:ℝ) 1, InjOn (H s) (normalStrip e) ∧
        ∀ p ∈ normalStrip e, ∃ a : ℝ, 0 < a ∧ ∀ v,
          jetContact (H s p) (fderiv ℝ (H s) p v) = a*jetContact p v := by
  obtain ⟨G,L,hG,hL,hGnz,hLdef,hG1,hmatch,hL1,hcoreGL,hGc,hLc⟩ :=
    legendrian_core_two_stage_deformation e he F hF hcore hinj lam hlam hpos hcontact
  have hGper := normal_rescaling_periodic_with_period a F hperiod G hG hGnz
  have hGzero : G 0 = coreLinear (lam ∘ corePoint) := by
    rw [hmatch,hLdef,coreLinearPath_zero]
  have hlper : Periodic (lam ∘ corePoint) a := by
    apply core_factor_periodic_with_period a
    intro p
    rw [← hGzero]
    exact hGper 0 p
  have hLper : ∀ s p, L s (p+corePoint a) = L s p+corePoint a := by
    rw [hLdef]
    exact coreLinearPath_periodic_with_period a _ (hlam.comp corePoint_contDiff) hlper
  apply concatenate_core_contact_deformations_with_period a (normalStrip e) F G L hG hL hG1 hmatch hL1 hcoreGL hGper hLper
  · intro s hs
    exact (hGc s hs).1
  · intro s hs
    exact (hLc s hs).1.injOn
  · intro s hs p hp
    exact ⟨lam (normalScale s p),(hGc s hs).2.1 p hp,(hGc s hs).2.2 p hp⟩
  · intro s hs p hp
    exact ⟨coreScaleFactor (lam ∘ corePoint) s (p 0),(hLc s hs).2.1 _,(hLc s hs).2.2 p⟩

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

/-- A globally smooth positive denominator which equals x above one half. -/
def safePositiveDenominator (x : ℝ) : ℝ :=
  1-Real.smoothTransition (4*x-1)+Real.smoothTransition (4*x-1)*x

lemma safePositiveDenominator_contDiff : ContDiff ℝ ∞ safePositiveDenominator := by
  have hσ : ContDiff ℝ ∞ (fun x : ℝ => Real.smoothTransition (4*x-1)) :=
    (Real.smoothTransition.contDiff (n := (⊤:ℕ∞))).comp ((contDiff_const.mul contDiff_id).sub contDiff_const)
  exact (contDiff_const.sub hσ).add (hσ.mul contDiff_id)

lemma safePositiveDenominator_pos (x : ℝ) : 0 < safePositiveDenominator x := by
  by_cases hx : x ≤ 1/4
  · have hh : Real.smoothTransition (4*x-1) = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
    simp [safePositiveDenominator,hh]
  · have hσ₀ := Real.smoothTransition.nonneg (4*x-1)
    have hσ₁ := Real.smoothTransition.le_one (4*x-1)
    have hm := mul_nonneg hσ₀ (show 0 ≤ x-1/4 by linarith)
    dsimp [safePositiveDenominator]
    nlinarith

def safeReciprocal (x : ℝ) : ℝ := (safePositiveDenominator x)⁻¹

lemma safeReciprocal_contDiff : ContDiff ℝ ∞ safeReciprocal :=
  safePositiveDenominator_contDiff.inv (fun x => (safePositiveDenominator_pos x).ne')

lemma safeReciprocal_eq (x : ℝ) (hx : 1/2 ≤ x) : safeReciprocal x = x⁻¹ := by
  have hσ : Real.smoothTransition (4*x-1) = 1 := Real.smoothTransition.one_of_one_le (by linarith)
  simp [safeReciprocal,safePositiveDenominator,hσ]

def angleAlignmentRe (x : ℝ) (y : Phase) : ℝ :=
  Real.cos (2*Real.pi*x)*y 0+Real.sin (2*Real.pi*x)*y 1

def angleAlignmentIm (x : ℝ) (y : Phase) : ℝ :=
  Real.cos (2*Real.pi*x)*y 1-Real.sin (2*Real.pi*x)*y 0

/-- A smooth global extension of the canonical small-angle lift. On the
neighborhood where the two denominators exceed one half it is the true
coordinate lift; no global contact property is asserted. -/
def legendrianSphereMapLift (F : EquivariantSphereContactomorphism) (p : Jet3) : Jet3 :=
  let y := F.toFun (legendrianSphereChart p)
  ![p 0+Real.arctan (angleAlignmentIm (p 0) y*safeReciprocal (angleAlignmentRe (p 0) y))/(2*Real.pi),
    -2*Real.pi*(y 0*y 3-y 1*y 2)*safeReciprocal (zNormSq y),
    -(y 0*y 2+y 1*y 3)/2*safeReciprocal (zNormSq y)]

lemma sphere_map_comp_chart_contDiff (F : EquivariantSphereContactomorphism) :
    ContDiff ℝ ∞ (fun p => F.toFun (legendrianSphereChart p)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  exact (F.smooth _ (legendrianSphereChart_mem p)).comp p legendrianSphereChart_contDiff.contDiffAt

lemma legendrianSphereMapLift_contDiff (F : EquivariantSphereContactomorphism) :
    ContDiff ℝ ∞ (legendrianSphereMapLift F) := by
  let f : Jet3 → Phase := fun p => F.toFun (legendrianSphereChart p)
  have hf : ContDiff ℝ ∞ f := sphere_map_comp_chart_contDiff F
  have hc : ContDiff ℝ ∞ (fun p : Jet3 => Real.cos (2*Real.pi*p 0)) := by fun_prop
  have hs : ContDiff ℝ ∞ (fun p : Jet3 => Real.sin (2*Real.pi*p 0)) := by fun_prop
  have hRe : ContDiff ℝ ∞ (fun p => angleAlignmentRe (p 0) (f p)) :=
    (hc.mul ((contDiff_apply ℝ ℝ 0).comp hf)).add (hs.mul ((contDiff_apply ℝ ℝ 1).comp hf))
  have hIm : ContDiff ℝ ∞ (fun p => angleAlignmentIm (p 0) (f p)) :=
    (hc.mul ((contDiff_apply ℝ ℝ 1).comp hf)).sub (hs.mul ((contDiff_apply ℝ ℝ 0).comp hf))
  have hZ : ContDiff ℝ ∞ (fun p => zNormSq (f p)) := by dsimp [zNormSq]; fun_prop
  have hangle := (Real.contDiff_arctan.comp (hIm.mul (safeReciprocal_contDiff.comp hRe))).div_const (2*Real.pi)
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact (contDiff_apply ℝ ℝ 0).add hangle
  · change ContDiff ℝ ∞ (fun p : Jet3 => -2*Real.pi*((f p) 0*(f p) 3-(f p) 1*(f p) 2)*safeReciprocal (zNormSq (f p)))
    have hD : ContDiff ℝ ∞ (fun p : Jet3 => (f p) 0*(f p) 3-(f p) 1*(f p) 2) :=
      (((contDiff_apply ℝ ℝ 0).comp hf).mul ((contDiff_apply ℝ ℝ 3).comp hf)).sub
        (((contDiff_apply ℝ ℝ 1).comp hf).mul ((contDiff_apply ℝ ℝ 2).comp hf))
    exact (contDiff_const.mul hD).mul (safeReciprocal_contDiff.comp hZ)
  · change ContDiff ℝ ∞ (fun p : Jet3 => -((f p) 0*(f p) 2+(f p) 1*(f p) 3)/2*safeReciprocal (zNormSq (f p)))
    exact (((((contDiff_apply ℝ ℝ 0).comp hf).mul ((contDiff_apply ℝ ℝ 2).comp hf)).add
      (((contDiff_apply ℝ ℝ 1).comp hf).mul ((contDiff_apply ℝ ℝ 3).comp hf))).neg.div_const 2).mul
      (safeReciprocal_contDiff.comp hZ)

lemma angleAlignmentRe_core (x : ℝ) :
    angleAlignmentRe x (legendrianSphereChart (corePoint x)) = 1 := by
  rw [legendrianSphereChart_core]
  simpa [angleAlignmentRe,pow_two] using Real.cos_sq_add_sin_sq (2*Real.pi*x)

lemma angleAlignmentIm_core (x : ℝ) :
    angleAlignmentIm x (legendrianSphereChart (corePoint x)) = 0 := by
  rw [legendrianSphereChart_core]
  simp [angleAlignmentIm]
  ring

lemma legendrianSphereMapLift_core (F : EquivariantSphereContactomorphism)
    (hcore : ∀ x, F.toFun (legendrianSphereChart (corePoint x)) = legendrianSphereChart (corePoint x))
    (x : ℝ) : legendrianSphereMapLift F (corePoint x) = corePoint x := by
  have hZ : zNormSq (legendrianSphereChart (corePoint x)) = 1 := by
    rw [legendrianSphereChart_core]
    simpa [zNormSq] using Real.cos_sq_add_sin_sq (2*Real.pi*x)
  have hx : (corePoint x) 0 = x := rfl
  simp only [legendrianSphereMapLift,hcore,hx,angleAlignmentIm_core,zero_mul,
    Real.arctan_zero,zero_div,add_zero]
  rw [legendrianSphereChart_core]
  simp [corePoint]

lemma angleAlignmentRe_half_shift (x : ℝ) (y : Phase) :
    angleAlignmentRe (x+1/2) (-y) = angleAlignmentRe x y := by
  have hθ : 2*Real.pi*(x+1/2) = 2*Real.pi*x+Real.pi := by ring
  dsimp [angleAlignmentRe]
  rw [hθ,Real.cos_add_pi,Real.sin_add_pi]
  ring

lemma angleAlignmentIm_half_shift (x : ℝ) (y : Phase) :
    angleAlignmentIm (x+1/2) (-y) = angleAlignmentIm x y := by
  have hθ : 2*Real.pi*(x+1/2) = 2*Real.pi*x+Real.pi := by ring
  dsimp [angleAlignmentIm]
  rw [hθ,Real.cos_add_pi,Real.sin_add_pi]
  ring

lemma legendrianSphereMapLift_half_period (F : EquivariantSphereContactomorphism) (p : Jet3) :
    legendrianSphereMapLift F (p+corePoint (1/2)) = legendrianSphereMapLift F p+corePoint (1/2) := by
  have hneg : F.toFun (legendrianSphereChart (p+corePoint (1/2))) = -F.toFun (legendrianSphereChart p) := by
    rw [legendrianSphereChart_antipodal,F.antipodal _ (legendrianSphereChart_mem p)]
  have hZ : zNormSq (-F.toFun (legendrianSphereChart p)) = zNormSq (F.toFun (legendrianSphereChart p)) := by
    simp [zNormSq]
  simp only [legendrianSphereMapLift,hneg]
  ext i
  fin_cases i
  · dsimp [corePoint]
    simp only [angleAlignmentRe_half_shift,angleAlignmentIm_half_shift]
    ring
  · simp [hZ,corePoint]
  · simp [hZ,corePoint]

end
end ContactTopology

namespace ContactTopology
open BirkhoffGlobalSection BirkhoffGlobalSection.HopfTransport Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma angleAlignmentRe_chart (x : ℝ) (p : Jet3) :
    angleAlignmentRe x (legendrianSphereChart p) =
      (Real.sqrt (zNormSq (legendrianChartRaw p)+wNormSq (legendrianChartRaw p)))⁻¹*
        Real.cos (2*Real.pi*(p 0-x)) := by
  let a := (Real.sqrt (zNormSq (legendrianChartRaw p)+wNormSq (legendrianChartRaw p)))⁻¹
  change Real.cos (2*Real.pi*x)*(a*Real.cos (2*Real.pi*p 0))+
    Real.sin (2*Real.pi*x)*(a*Real.sin (2*Real.pi*p 0)) = a*Real.cos (2*Real.pi*(p 0-x))
  have he : 2*Real.pi*(p 0-x) = 2*Real.pi*p 0-2*Real.pi*x := by ring
  rw [he,Real.cos_sub]
  ring

lemma angleAlignmentIm_chart (x : ℝ) (p : Jet3) :
    angleAlignmentIm x (legendrianSphereChart p) =
      (Real.sqrt (zNormSq (legendrianChartRaw p)+wNormSq (legendrianChartRaw p)))⁻¹*
        Real.sin (2*Real.pi*(p 0-x)) := by
  let a := (Real.sqrt (zNormSq (legendrianChartRaw p)+wNormSq (legendrianChartRaw p)))⁻¹
  change Real.cos (2*Real.pi*x)*(a*Real.sin (2*Real.pi*p 0))-
    Real.sin (2*Real.pi*x)*(a*Real.cos (2*Real.pi*p 0)) = a*Real.sin (2*Real.pi*(p 0-x))
  have he : 2*Real.pi*(p 0-x) = 2*Real.pi*p 0-2*Real.pi*x := by ring
  rw [he,Real.sin_sub]
  ring

lemma legendrianSphereMapLift_eq_of_chart (F : EquivariantSphereContactomorphism) (p q : Jet3)
    (heq : legendrianSphereChart q = F.toFun (legendrianSphereChart p))
    (hang : |q 0-p 0| < 1/4)
    (hRe : 1/2 ≤ angleAlignmentRe (p 0) (F.toFun (legendrianSphereChart p)))
    (hZ : 1/2 ≤ zNormSq (F.toFun (legendrianSphereChart p))) :
    legendrianSphereMapLift F p = q := by
  have hθlo : -(Real.pi/2) < 2*Real.pi*(q 0-p 0) := by
    nlinarith [(abs_lt.mp hang).1,Real.pi_pos]
  have hθhi : 2*Real.pi*(q 0-p 0) < Real.pi/2 := by
    nlinarith [(abs_lt.mp hang).2,Real.pi_pos]
  have hcos : Real.cos (2*Real.pi*(q 0-p 0)) ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨hθlo,hθhi⟩).ne'
  have ha : (Real.sqrt (zNormSq (legendrianChartRaw q)+wNormSq (legendrianChartRaw q)))⁻¹ ≠ 0 :=
    inv_ne_zero (Real.sqrt_pos.mpr (legendrianChartRaw_radius_positive q)).ne'
  have hratio : angleAlignmentIm (p 0) (F.toFun (legendrianSphereChart p))*
      safeReciprocal (angleAlignmentRe (p 0) (F.toFun (legendrianSphereChart p))) =
      Real.tan (2*Real.pi*(q 0-p 0)) := by
    rw [safeReciprocal_eq _ hRe,← heq,angleAlignmentIm_chart,angleAlignmentRe_chart,
      Real.tan_eq_sin_div_cos]
    field_simp [(Real.sqrt_pos.mpr (legendrianChartRaw_radius_positive q)).ne']
  have hY : -2*Real.pi*((F.toFun (legendrianSphereChart p)) 0*(F.toFun (legendrianSphereChart p)) 3-
      (F.toFun (legendrianSphereChart p)) 1*(F.toFun (legendrianSphereChart p)) 2)*
      safeReciprocal (zNormSq (F.toFun (legendrianSphereChart p))) = q 1 := by
    rw [safeReciprocal_eq _ hZ]
    change legendrianNormalY (F.toFun (legendrianSphereChart p)) = _
    rw [← heq,legendrianNormalY_chart]
  have hW : -((F.toFun (legendrianSphereChart p)) 0*(F.toFun (legendrianSphereChart p)) 2+
      (F.toFun (legendrianSphereChart p)) 1*(F.toFun (legendrianSphereChart p)) 3)/2*
      safeReciprocal (zNormSq (F.toFun (legendrianSphereChart p))) = q 2 := by
    rw [safeReciprocal_eq _ hZ]
    have hh := legendrianNormalZ_chart q
    rw [heq] at hh
    convert! hh using 1 <;> dsimp [legendrianNormalZ] <;> ring
  ext i
  fin_cases i
  · change p 0+Real.arctan _/(2*Real.pi) = q 0
    rw [hratio,Real.arctan_tan hθlo hθhi]
    field_simp [Real.pi_ne_zero]
    <;> ring
  · exact hY
  · exact hW

/-- The explicit global lift agrees near every core point with the genuine
smooth inverse chart. This is the bridge from actual sphere maps to the
coordinate deformation theorem. -/
lemma legendrianSphereMapLift_local_identity (F : EquivariantSphereContactomorphism)
    (hcore : ∀ x, F.toFun (legendrianSphereChart (corePoint x)) = legendrianSphereChart (corePoint x))
    (x : ℝ) :
    ∀ᶠ p in 𝓝 (corePoint x),
      legendrianSphereChart (legendrianSphereMapLift F p) = F.toFun (legendrianSphereChart p) := by
  obtain ⟨r,hr,hrp,hleft,hright⟩ := legendrianSphereChart_local_inverse (corePoint x)
  let f : Jet3 → Phase := fun p => F.toFun (legendrianSphereChart p)
  have hf : ContDiff ℝ ∞ f := sphere_map_comp_chart_contDiff F
  have hfx : f (corePoint x) = legendrianSphereChart (corePoint x) := hcore x
  have hrf : ContinuousAt (fun p => r (f p)) (corePoint x) := by
    have hr' : ContinuousAt r (f (corePoint x)) := by rw [hfx]; exact hr.continuousAt
    exact hr'.comp hf.continuous.continuousAt
  have hq : r (f (corePoint x)) = corePoint x := by rw [hfx,hrp]
  have hang : ∀ᶠ p in 𝓝 (corePoint x), |(r (f p)) 0-p 0| < 1/4 := by
    have hc : ContinuousAt (fun p : Jet3 => |(r (f p)) 0-p 0|) (corePoint x) :=
      (((continuous_apply 0).continuousAt.comp hrf).sub (continuous_apply 0).continuousAt).abs
    apply hc.eventually (gt_mem_nhds (show |(r (f (corePoint x))) 0-(corePoint x) 0| < (1/4:ℝ) by rw [hq]; norm_num))
  have hA : ContinuousAt (fun p => angleAlignmentRe (p 0) (f p)) (corePoint x) := by
    have hc : ContDiff ℝ ∞ (fun p : Jet3 => Real.cos (2*Real.pi*p 0)) := by fun_prop
    have hs : ContDiff ℝ ∞ (fun p : Jet3 => Real.sin (2*Real.pi*p 0)) := by fun_prop
    exact ((hc.mul ((contDiff_apply ℝ ℝ 0).comp hf)).add
      (hs.mul ((contDiff_apply ℝ ℝ 1).comp hf))).continuous.continuousAt
  have hZ : ContinuousAt (fun p => zNormSq (f p)) (corePoint x) := by
    exact ((((contDiff_apply ℝ ℝ 0).comp hf).pow 2).add
      (((contDiff_apply ℝ ℝ 1).comp hf).pow 2)).continuous.continuousAt
  have hAval : angleAlignmentRe ((corePoint x) 0) (f (corePoint x)) = 1 := by
    rw [hfx]
    exact angleAlignmentRe_core x
  have hZval : zNormSq (f (corePoint x)) = 1 := by
    rw [hfx,legendrianSphereChart_core]
    simpa [zNormSq] using Real.cos_sq_add_sin_sq (2*Real.pi*x)
  have hAge : ∀ᶠ p in 𝓝 (corePoint x), 1/2 < angleAlignmentRe (p 0) (f p) :=
    hA.eventually (lt_mem_nhds (by change 1/2 < angleAlignmentRe ((corePoint x) 0) (f (corePoint x)); rw [hAval]; norm_num))
  have hZge : ∀ᶠ p in 𝓝 (corePoint x), 1/2 < zNormSq (f p) :=
    hZ.eventually (lt_mem_nhds (by change 1/2 < zNormSq (f (corePoint x)); rw [hZval]; norm_num))
  have hi : Tendsto f (𝓝 (corePoint x)) (𝓝 (legendrianSphereChart (corePoint x))) := by
    rw [← hfx]
    exact hf.continuous.continuousAt
  filter_upwards [hi.eventually hright,hang,hAge,hZge] with p hp ha hA hZ
  have heq := hp (F.maps_sphere (legendrianSphereChart_mem p))
  rw [legendrianSphereMapLift_eq_of_chart F p (r (f p)) heq ha hA.le hZ.le]
  exact heq

end
end ContactTopology

namespace ContactTopology
open BirkhoffGlobalSection BirkhoffGlobalSection.HopfTransport Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Compactness of one longitudinal period gives a uniform tubular strip. -/
lemma periodic_core_neighborhood_contains_strip (U : Set Jet3)
    (hcore : ∀ x, U ∈ 𝓝 (corePoint x))
    (hper : Periodic (fun p => p ∈ U) (corePoint 1)) :
    ∃ e : ℝ, 0 < e ∧ normalStrip e ⊆ U := by
  let K : Set Jet3 := corePoint '' Icc (0:ℝ) 1
  have hK : IsCompact K := isCompact_Icc.image corePoint_contDiff.continuous
  have hKU : K ⊆ interior U := by
    rintro p ⟨x,hx,rfl⟩
    exact mem_interior_iff_mem_nhds.mpr (hcore x)
  obtain ⟨e,he,hesub⟩ := hK.exists_thickening_subset_open isOpen_interior hKU
  refine ⟨e,he,?_⟩
  intro p hp
  let q : Jet3 := ![Int.fract (p 0),p 1,p 2]
  have hqrep : q = p-⌊p 0⌋ • corePoint 1 := by
    have hz : ⌊p 0⌋ • corePoint 1 = corePoint (⌊p 0⌋ : ℝ) := by
      ext i
      fin_cases i <;> simp [corePoint,zsmul_eq_mul,Pi.mul_apply]
    rw [hz]
    ext i
    fin_cases i
    · change Int.fract (p 0) = p 0-(⌊p 0⌋ : ℝ)
      rfl
    · change p 1 = p 1-0
      ring
    · change p 2 = p 2-0
      ring
  have hqmem : q ∈ U := by
    apply interior_subset (hesub ?_)
    apply Metric.mem_thickening_iff.mpr
    refine ⟨corePoint (Int.fract (p 0)),⟨Int.fract (p 0),⟨Int.fract_nonneg _,(Int.fract_lt_one _).le⟩,rfl⟩,?_⟩
    apply (dist_pi_lt_iff he).mpr
    intro i
    fin_cases i
    · simpa [q,corePoint] using he
    · simpa [q,corePoint,Real.dist_eq] using hp.1
    · simpa [q,corePoint,Real.dist_eq] using hp.2
  have hqeq : (q ∈ U) = (p ∈ U) := by
    rw [hqrep]
    exact hper.sub_zsmul_eq ⌊p 0⌋
  rwa [hqeq] at hqmem

lemma legendrianSphereMapLift_period (F : EquivariantSphereContactomorphism) (p : Jet3) :
    legendrianSphereMapLift F (p+corePoint 1) = legendrianSphereMapLift F p+corePoint 1 := by
  have ha : corePoint (1/2)+corePoint (1/2) = corePoint 1 := by
    ext i
    fin_cases i <;> norm_num [corePoint]
  have he : (p+corePoint (1/2))+corePoint (1/2) = p+corePoint 1 := by rw [add_assoc,ha]
  rw [← he,legendrianSphereMapLift_half_period,legendrianSphereMapLift_half_period,add_assoc,ha]

lemma legendrianSphereMapLift_uniform_identity (F : EquivariantSphereContactomorphism)
    (hcore : ∀ x, F.toFun (legendrianSphereChart (corePoint x)) = legendrianSphereChart (corePoint x)) :
    ∃ e : ℝ, 0 < e ∧ ∀ p ∈ normalStrip e,
      legendrianSphereChart (legendrianSphereMapLift F p) = F.toFun (legendrianSphereChart p) := by
  let U : Set Jet3 := {p | legendrianSphereChart (legendrianSphereMapLift F p) = F.toFun (legendrianSphereChart p)}
  have hUcore : ∀ x, U ∈ 𝓝 (corePoint x) := legendrianSphereMapLift_local_identity F hcore
  have hUper : Periodic (fun p => p ∈ U) (corePoint 1) := by
    intro p
    change (legendrianSphereChart (legendrianSphereMapLift F (p+corePoint 1)) = F.toFun (legendrianSphereChart (p+corePoint 1))) = _
    rw [legendrianSphereMapLift_period,legendrianSphereChart_periodic,legendrianSphereChart_periodic]
    rfl
  exact periodic_core_neighborhood_contains_strip U hUcore hUper

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

lemma legendrianSphereMapLift_injOn (F : EquivariantSphereContactomorphism) (U : Set Jet3)
    (hidentity : ∀ p ∈ U, legendrianSphereChart (legendrianSphereMapLift F p) = F.toFun (legendrianSphereChart p)) :
    InjOn (legendrianSphereMapLift F) U := by
  intro p hp q hq heq
  have hFpq : F.toFun (legendrianSphereChart p) = F.toFun (legendrianSphereChart q) := by
    rw [← hidentity p hp,← hidentity q hq,heq]
  have hχpq : legendrianSphereChart p = legendrianSphereChart q := by
    have hh := congrArg F.invFun hFpq
    simpa only [F.left_inv _ (legendrianSphereChart_mem p),F.left_inv _ (legendrianSphereChart_mem q)] using hh
  have h₁ : p 1 = q 1 := by rw [← legendrianNormalY_chart p,← legendrianNormalY_chart q,hχpq]
  have h₂ : p 2 = q 2 := by rw [← legendrianNormalZ_chart p,← legendrianNormalZ_chart q,hχpq]
  have htrig := legendrianSphereChart_eq_angles p q hχpq
  have hRe : angleAlignmentRe (p 0) (F.toFun (legendrianSphereChart p)) =
      angleAlignmentRe (q 0) (F.toFun (legendrianSphereChart q)) := by
    dsimp [angleAlignmentRe]
    rw [htrig.1,htrig.2,hFpq]
  have hIm : angleAlignmentIm (p 0) (F.toFun (legendrianSphereChart p)) =
      angleAlignmentIm (q 0) (F.toFun (legendrianSphereChart q)) := by
    dsimp [angleAlignmentIm]
    rw [htrig.1,htrig.2,hFpq]
  have h₀ := congrFun heq 0
  change p 0+Real.arctan _/(2*Real.pi) = q 0+Real.arctan _/(2*Real.pi) at h₀
  rw [hRe,hIm] at h₀
  have hpq₀ : p 0 = q 0 := by linarith
  ext i
  fin_cases i
  · exact hpq₀
  · exact h₁
  · exact h₂

end
end ContactTopology

namespace ContactTopology
open BirkhoffGlobalSection BirkhoffGlobalSection.HopfTransport Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma normalStrip_isOpen (e : ℝ) : IsOpen (normalStrip e) := by
  exact (isOpen_lt ((continuous_apply 1).abs) continuous_const).inter
    (isOpen_lt ((continuous_apply 2).abs) continuous_const)

lemma legendrianSphereMapLift_contact (F : EquivariantSphereContactomorphism)
    (U : Set Jet3) (hU : IsOpen U)
    (hid : ∀ p ∈ U, legendrianSphereChart (legendrianSphereMapLift F p) = F.toFun (legendrianSphereChart p))
    (p : Jet3) (hp : p ∈ U) :
    ∃ a : ℝ, 0 < a ∧ ∀ v,
      jetContact (legendrianSphereMapLift F p) (fderiv ℝ (legendrianSphereMapLift F) p v) = a*jetContact p v := by
  obtain ⟨a,ha,hc⟩ := F.contact _ (legendrianSphereChart_mem p)
  have hw : ∀ q, 0 < legendrianChartWeight q := fun q => inv_pos.mpr (legendrianChartRaw_radius_positive q)
  refine ⟨a*legendrianChartWeight p/legendrianChartWeight (legendrianSphereMapLift F p),
    div_pos (mul_pos ha (hw p)) (hw _),?_⟩
  intro v
  have ht := legendrianSphereChart_fderiv_tangent p v
  have hpb := hc (fderiv ℝ legendrianSphereChart p v) ht
  have heq : (legendrianSphereChart ∘ legendrianSphereMapLift F) =ᶠ[𝓝 p]
      (F.toFun ∘ legendrianSphereChart) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact hid q hq
  have hd : fderiv ℝ (legendrianSphereChart ∘ legendrianSphereMapLift F) p =
      fderiv ℝ (F.toFun ∘ legendrianSphereChart) p := heq.fderiv_eq
  rw [fderiv_comp p (legendrianSphereChart_contDiff.differentiable (by simp) _)
    (legendrianSphereMapLift_contDiff F |>.differentiable (by simp) p),
    fderiv_comp p ((F.smooth _ (legendrianSphereChart_mem p)).differentiableAt (by simp))
      (legendrianSphereChart_contDiff.differentiable (by simp) p)] at hd
  have hv := congrArg (fun L : Jet3 →L[ℝ] Phase => L v) hd
  change fderiv ℝ legendrianSphereChart (legendrianSphereMapLift F p)
      (fderiv ℝ (legendrianSphereMapLift F) p v) =
      fderiv ℝ F.toFun (legendrianSphereChart p) (fderiv ℝ legendrianSphereChart p v) at hv
  have hchart₁ := legendrianSphereChart_contact (legendrianSphereMapLift F p)
    (fderiv ℝ (legendrianSphereMapLift F) p v)
  have hchart₀ := legendrianSphereChart_contact p v
  rw [hid p hp,hv] at hchart₁
  rw [hpb,hchart₀] at hchart₁
  change a*(jetContact p v*legendrianChartWeight p) =
    jetContact (legendrianSphereMapLift F p) (fderiv ℝ (legendrianSphereMapLift F) p v)*
      legendrianChartWeight (legendrianSphereMapLift F p) at hchart₁
  calc
    _ = (a*(jetContact p v*legendrianChartWeight p))/legendrianChartWeight (legendrianSphereMapLift F p) :=
      (eq_div_iff (hw _).ne').mpr hchart₁.symm
    _ = _ := by ring

/-- An actual equivariant sphere contactomorphism fixing the real Legendrian
circle has a uniform coordinate neighborhood on which the explicit lift is
an injective positive contact map. -/
lemma legendrianSphereMapLift_contact_neighborhood (F : EquivariantSphereContactomorphism)
    (hcore : ∀ x, F.toFun (legendrianSphereChart (corePoint x)) = legendrianSphereChart (corePoint x)) :
    ∃ e : ℝ, 0 < e ∧
      (∀ p ∈ normalStrip e, legendrianSphereChart (legendrianSphereMapLift F p) = F.toFun (legendrianSphereChart p)) ∧
      InjOn (legendrianSphereMapLift F) (normalStrip e) ∧
      (∀ p ∈ normalStrip e, 0 < jetContactFactor (legendrianSphereMapLift F) p) ∧
      ∀ p ∈ normalStrip e, ∀ v,
        jetContact (legendrianSphereMapLift F p) (fderiv ℝ (legendrianSphereMapLift F) p v) =
          jetContactFactor (legendrianSphereMapLift F) p*jetContact p v := by
  obtain ⟨e,he,hid⟩ := legendrianSphereMapLift_uniform_identity F hcore
  refine ⟨e,he,hid,legendrianSphereMapLift_injOn F _ hid,?_,?_⟩
  · intro p hp
    obtain ⟨a,ha,hc⟩ := legendrianSphereMapLift_contact F _ (normalStrip_isOpen e) hid p hp
    have hh := hc (Pi.single 2 1)
    have hfactor : jetContactFactor (legendrianSphereMapLift F) p = a := by
      simpa [jetContactFactor,jetContact] using hh
    rwa [hfactor]
  · intro p hp v
    obtain ⟨a,ha,hc⟩ := legendrianSphereMapLift_contact F _ (normalStrip_isOpen e) hid p hp
    have hfactor : jetContactFactor (legendrianSphereMapLift F) p = a := by
      simpa [jetContactFactor,jetContact] using hc (Pi.single 2 1)
    rw [hfactor]
    exact hc v

/-- The coordinate deformation now applies to the lift of the supplied sphere
contactomorphism, with the half-period equivariance required by the quotient. -/
lemma sphere_core_fixing_coordinate_deformation (F : EquivariantSphereContactomorphism)
    (hcore : ∀ x, F.toFun (legendrianSphereChart (corePoint x)) = legendrianSphereChart (corePoint x)) :
    ∃ e : ℝ, 0 < e ∧ ∃ H : ℝ → Jet3 → Jet3,
      ContDiff ℝ ∞ (fun q : ℝ × Jet3 => H q.1 q.2) ∧
      H 0 = legendrianSphereMapLift F ∧ H 1 = id ∧
      (∀ s x, H s (corePoint x) = corePoint x) ∧
      (∀ s p, H s (p+corePoint (1/2)) = H s p+corePoint (1/2)) ∧
      (∀ p ∈ normalStrip e, legendrianSphereChart (H 0 p) = F.toFun (legendrianSphereChart p)) ∧
      ∀ s ∈ Icc (0:ℝ) 1, InjOn (H s) (normalStrip e) ∧
        ∀ p ∈ normalStrip e, ∃ a : ℝ, 0 < a ∧ ∀ v,
          jetContact (H s p) (fderiv ℝ (H s) p v) = a*jetContact p v := by
  obtain ⟨e,he,hid,hinj,hpos,hcontact⟩ := legendrianSphereMapLift_contact_neighborhood F hcore
  obtain ⟨H,hH,hH0,hH1,hHcore,hHper,hHcontact⟩ :=
    legendrian_core_contact_deformation_with_period (1/2) e he
      (legendrianSphereMapLift F) (legendrianSphereMapLift_contDiff F)
      (legendrianSphereMapLift_core F hcore) (legendrianSphereMapLift_half_period F)
      hinj (jetContactFactor (legendrianSphereMapLift F))
      (jetContactFactor_contDiff _ (legendrianSphereMapLift_contDiff F)) hpos hcontact
  refine ⟨e,he,H,hH,hH0,hH1,hHcore,hHper,?_,hHcontact⟩
  simpa only [hH0] using hid

end
end ContactTopology

open scoped ContDiff
theorem solution (F : BirkhoffGlobalSection.EquivariantSphereContactomorphism)
    (hcore : ∀ x : ℝ,
      F.toFun ![Real.cos (2*Real.pi*x),Real.sin (2*Real.pi*x),0,0] =
        ![Real.cos (2*Real.pi*x),Real.sin (2*Real.pi*x),0,0]) :
    let chart : (Fin 3 → ℝ) → BirkhoffGlobalSection.Phase := fun p =>
      BirkhoffGlobalSection.radialNormalize
        ![Real.cos (2*Real.pi*p 0),Real.sin (2*Real.pi*p 0),
          (-2*p 2)*Real.cos (2*Real.pi*p 0)+(p 1/(2*Real.pi))*Real.sin (2*Real.pi*p 0),
          (-2*p 2)*Real.sin (2*Real.pi*p 0)-(p 1/(2*Real.pi))*Real.cos (2*Real.pi*p 0)]
    let alpha : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ := fun p v => v 2-p 1*v 0
    ∃ e : ℝ, 0 < e ∧ ∃ H : ℝ → (Fin 3 → ℝ) → (Fin 3 → ℝ),
      ContDiff ℝ ∞ (fun q : ℝ × (Fin 3 → ℝ) => H q.1 q.2) ∧ H 1 = id ∧
      (∀ s x, H s ![x,0,0] = ![x,0,0]) ∧
      (∀ s p, H s (p+![1/2,0,0]) = H s p+![1/2,0,0]) ∧
      (∀ p, |p 1| < e ∧ |p 2| < e → chart (H 0 p) = F.toFun (chart p)) ∧
      ∀ s ∈ Set.Icc (0:ℝ) 1,
        Set.InjOn (H s) {p | |p 1| < e ∧ |p 2| < e} ∧
        ∀ p, |p 1| < e ∧ |p 2| < e → ∃ a : ℝ, 0 < a ∧ ∀ v,
          alpha (H s p) (fderiv ℝ (H s) p v) = a*alpha p v := by
  have hc : ∀ x, F.toFun (ContactTopology.legendrianSphereChart (ContactTopology.corePoint x)) =
      ContactTopology.legendrianSphereChart (ContactTopology.corePoint x) := by
    intro x
    rw [ContactTopology.legendrianSphereChart_core]
    exact hcore x
  obtain ⟨e,he,H,hH,hH0,hH1,hHcore,hHper,hid,hHcontact⟩ :=
    ContactTopology.sphere_core_fixing_coordinate_deformation F hc
  exact ⟨e,he,H,hH,hH1,hHcore,hHper,hid,hHcontact⟩
