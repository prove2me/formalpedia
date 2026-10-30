-- Prove2me | solution 1 for ContactTopology.periodic_legendrian_family_contact_generator
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-29T23:34:12.573813+00:00
-- url     : https://prove2.me/submissions/b5940f87-7a01-43b8-86d8-8191fc971365

import Definitions.Def_BirkhoffGlobalSection_SphereContact
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Separation.Hausdorff
import Theorems.Thm_BirkhoffGlobalSection_radial_normalization_contact_identity
import Theorems.Thm_ContactCalculus_exterior_pairing_pullback
import Theorems.Thm_ParameterizedCalculus_smooth_unit_interval_integral
import Theorems.Thm_SmoothJetExtension_compact_first_jet_extension

































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

namespace ContactTopology
open BirkhoffGlobalSection BirkhoffGlobalSection.HopfTransport Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma sphere_core_fixing_coordinate_deformation_alltime (F : EquivariantSphereContactomorphism)
    (hcore : ∀ x, F.toFun (legendrianSphereChart (corePoint x)) = legendrianSphereChart (corePoint x)) :
    ∃ e : ℝ, 0 < e ∧ ∃ H : ℝ → Jet3 → Jet3,
      ContDiff ℝ ∞ (fun q : ℝ × Jet3 => H q.1 q.2) ∧
      H 0 = legendrianSphereMapLift F ∧ H 1 = id ∧
      (∀ s x, H s (corePoint x) = corePoint x) ∧
      (∀ s p, H s (p+corePoint (1/2)) = H s p+corePoint (1/2)) ∧
      (∀ p ∈ normalStrip e, legendrianSphereChart (H 0 p) = F.toFun (legendrianSphereChart p)) ∧
      ∀ s : ℝ, InjOn (H s) (normalStrip e) ∧
        ∀ p ∈ normalStrip e, ∃ a : ℝ, 0 < a ∧ ∀ v,
          jetContact (H s p) (fderiv ℝ (H s) p v) = a*jetContact p v := by
  obtain ⟨e,he,H,hH,h0,h1,hc,hper,hid,hcontact⟩ := sphere_core_fixing_coordinate_deformation F hcore
  let K : ℝ → Jet3 → Jet3 := fun t => H (Real.smoothTransition t)
  have hσ : ContDiff ℝ ∞ (fun t : ℝ => Real.smoothTransition t) :=
    Real.smoothTransition.contDiff (n := (⊤:ℕ∞))
  have hK : ContDiff ℝ ∞ (fun q : ℝ × Jet3 => K q.1 q.2) :=
    hH.comp ((hσ.comp contDiff_fst).prodMk contDiff_snd)
  have hK0 : K 0 = H 0 := by
    simp only [K,Real.smoothTransition.zero_of_nonpos (show (0:ℝ) ≤ 0 by norm_num)]
  have hK1 : K 1 = H 1 := by
    simp only [K,Real.smoothTransition.one_of_one_le (show (1:ℝ) ≤ 1 by norm_num)]
  refine ⟨e,he,K,hK,hK0.trans h0,hK1.trans h1,?_,?_,?_,?_⟩
  · exact fun s x => hc _ x
  · exact fun s p => hper _ p
  · simpa only [hK0] using hid
  · intro s
    exact hcontact (Real.smoothTransition s)
      ⟨Real.smoothTransition.nonneg s,Real.smoothTransition.le_one s⟩

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

lemma corePoint_add (x y : ℝ) : corePoint (x+y) = corePoint x+corePoint y := by
  ext i
  fin_cases i <;> simp [corePoint]

lemma normalStrip_translate (e x : ℝ) (p : Jet3) : p+corePoint x ∈ normalStrip e ↔ p ∈ normalStrip e := by
  change (|p 1+0| < e ∧ |p 2+0| < e) ↔ _
  simp only [add_zero]
  rfl

lemma lifted_family_sphere_equal (e : ℝ) (H : ℝ → Jet3 → Jet3)
    (hinj : ∀ t, InjOn (H t) (normalStrip e))
    (hper : ∀ t p, H t (p+corePoint 1) = H t p+corePoint 1)
    (t : ℝ) (p q : Jet3) (hp : p ∈ normalStrip e) (hq : q ∈ normalStrip e)
    (heq : legendrianSphereChart (H t p) = legendrianSphereChart (H t q)) :
    ∃ n : ℤ, p = q+corePoint n := by
  obtain ⟨n,hn⟩ := (legendrianSphereChart_fiber _ _).mp heq
  have hshift : ∀ s, H s (q+corePoint n) = H s q+corePoint n := by
    intro s
    have hperiod : Periodic (fun r : ℝ => H s (q+corePoint r)-corePoint r) 1 := by
      intro r
      change H s (q+corePoint (r+1))-corePoint (r+1) = H s (q+corePoint r)-corePoint r
      simp only [corePoint_add,← add_assoc,hper]
      abel
    have hh := hperiod.int_mul_eq n
    have hzero : corePoint 0 = 0 := by ext i; fin_cases i <;> simp [corePoint]
    change H s (q+corePoint ((n:ℝ)*1))-corePoint ((n:ℝ)*1) = H s (q+corePoint 0)-corePoint 0 at hh
    simp only [mul_one,hzero,add_zero,sub_zero] at hh
    exact (sub_eq_iff_eq_add).mp hh
  refine ⟨n,hinj t hp ((normalStrip_translate e n q).mpr hq) ?_⟩
  rw [hshift]
  exact hn

end
end ContactTopology

namespace ContactTopology
open BirkhoffGlobalSection BirkhoffGlobalSection.HopfTransport Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- A jointly smooth contact family in the cover gives actual jointly smooth
inverse sphere coordinates near each moving point. -/
lemma legendrian_family_sphere_local_inverse (H : ℝ → Jet3 → Jet3)
    (hH : ContDiff ℝ ∞ (fun q : ℝ × Jet3 => H q.1 q.2))
    (U : Set Jet3) (hU : IsOpen U) (t : ℝ)
    (hcontact : ∀ p ∈ U, ∃ a : ℝ, 0 < a ∧ ∀ v,
      jetContact (H t p) (fderiv ℝ (H t) p v) = a*jetContact p v)
    (p : Jet3) (hp : p ∈ U) :
    ∃ r : ℝ × Phase → Jet3,
      ContDiffAt ℝ ∞ r (t,legendrianSphereChart (H t p)) ∧
      r (t,legendrianSphereChart (H t p)) = p ∧
      (∀ᶠ q : ℝ × Jet3 in 𝓝 (t,p), r (q.1,legendrianSphereChart (H q.1 q.2)) = q.2) ∧
      (∀ᶠ q : ℝ × Phase in 𝓝 (t,legendrianSphereChart (H t p)), q.2 ∈ unitThreeSphere →
        legendrianSphereChart (H q.1 (r q)) = q.2) ∧
      (∀ᶠ q : ℝ × Phase in 𝓝 (t,legendrianSphereChart (H t p)), r q ∈ U) := by
  obtain ⟨c,hc,hcpoint,hcleft,hcright⟩ := legendrianSphereChart_local_inverse (H t p)
  obtain ⟨b,hb,hbpoint,hbleft,hbright,hbU⟩ := contact_family_joint_local_inverse H hH U hU t hcontact p hp
  let K : ℝ × Phase → ℝ × Jet3 := fun q => (q.1,c q.2)
  have hK : ContDiffAt ℝ ∞ K (t,legendrianSphereChart (H t p)) :=
    contDiffAt_fst.prodMk (hc.comp (t,legendrianSphereChart (H t p)) contDiffAt_snd)
  have hKpoint : K (t,legendrianSphereChart (H t p)) = (t,H t p) := by
    change (t,c (legendrianSphereChart (H t p))) = _
    rw [hcpoint]
  have hb' : ContDiffAt ℝ ∞ b (K (t,legendrianSphereChart (H t p))) := by
    rw [hKpoint]
    exact hb
  have hr : ContDiffAt ℝ ∞ (b ∘ K) (t,legendrianSphereChart (H t p)) := hb'.comp _ hK
  refine ⟨b ∘ K,hr,?_,?_,?_,?_⟩
  · change b (K (t,legendrianSphereChart (H t p))) = _
    rw [hKpoint,hbpoint]
  · have hi : Tendsto (fun q : ℝ × Jet3 => H q.1 q.2) (𝓝 (t,p)) (𝓝 (H t p)) :=
      hH.continuous.continuousAt
    have hnear : ∀ᶠ q : ℝ × Jet3 in 𝓝 (t,p), c (legendrianSphereChart (H q.1 q.2)) = H q.1 q.2 :=
      hi.eventually hcleft
    filter_upwards [hnear,hbleft] with q hq hqb
    change b (q.1,c (legendrianSphereChart (H q.1 q.2))) = _
    rw [hq]
    exact hqb
  · have hi : Tendsto K (𝓝 (t,legendrianSphereChart (H t p))) (𝓝 (t,H t p)) := by
      rw [← hKpoint]
      exact hK.continuousAt
    have hsnd : Tendsto (fun q : ℝ × Phase => q.2) (𝓝 (t,legendrianSphereChart (H t p)))
        (𝓝 (legendrianSphereChart (H t p))) := continuous_snd.continuousAt
    filter_upwards [hi.eventually hbright,hsnd.eventually hcright] with q hq hcq
    intro hqs
    change legendrianSphereChart (H q.1 (b (K q))) = _
    change H q.1 (b (K q)) = c q.2 at hq
    rw [hq]
    exact hcq hqs
  · have hi : Tendsto K (𝓝 (t,legendrianSphereChart (H t p))) (𝓝 (t,H t p)) := by
      rw [← hKpoint]
      exact hK.continuousAt
    exact hi.eventually hbU

def sphereFamilyTimeVelocity (H : ℝ → Jet3 → Jet3) (q : ℝ × Jet3) : Phase :=
  fderiv ℝ (fun r : ℝ × Jet3 => legendrianSphereChart (H r.1 r.2)) q (1,0)

lemma sphereFamilyTimeVelocity_contDiff (H : ℝ → Jet3 → Jet3)
    (hH : ContDiff ℝ ∞ (fun q : ℝ × Jet3 => H q.1 q.2)) :
    ContDiff ℝ ∞ (sphereFamilyTimeVelocity H) := by
  exact ((legendrianSphereChart_contDiff.comp hH).fderiv_right (by simp)).clm_apply contDiff_const

lemma sphereFamilyTimeVelocity_eq_deriv (H : ℝ → Jet3 → Jet3)
    (hH : ContDiff ℝ ∞ (fun q : ℝ × Jet3 => H q.1 q.2)) (t : ℝ) (p : Jet3) :
    sphereFamilyTimeVelocity H (t,p) = deriv (fun s => legendrianSphereChart (H s p)) t := by
  have hc : HasDerivAt (fun s : ℝ => (s,p)) (1,0) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t p)
  have hd := ((legendrianSphereChart_contDiff.comp hH).differentiable (by simp) (t,p)).hasFDerivAt.comp_hasDerivAt t hc
  exact hd.deriv.symm

lemma sphereFamilyTimeVelocity_fiber_independent (e : ℝ) (H : ℝ → Jet3 → Jet3)
    (hH : ContDiff ℝ ∞ (fun q : ℝ × Jet3 => H q.1 q.2))
    (hinj : ∀ t, InjOn (H t) (normalStrip e))
    (hper : ∀ t p, H t (p+corePoint 1) = H t p+corePoint 1)
    (t : ℝ) (p q : Jet3) (hp : p ∈ normalStrip e) (hq : q ∈ normalStrip e)
    (heq : legendrianSphereChart (H t p) = legendrianSphereChart (H t q)) :
    sphereFamilyTimeVelocity H (t,p) = sphereFamilyTimeVelocity H (t,q) := by
  obtain ⟨n,hn⟩ := lifted_family_sphere_equal e H hinj hper t p q hp hq heq
  have hsame : (fun s => legendrianSphereChart (H s p)) = fun s => legendrianSphereChart (H s q) := by
    funext s
    have hperiod : Periodic (fun r => legendrianSphereChart (H s r)) (corePoint 1) := by
      intro r
      change legendrianSphereChart (H s (r+corePoint 1)) = legendrianSphereChart (H s r)
      rw [hper,legendrianSphereChart_periodic]
    have hz : n • corePoint 1 = corePoint n := by
      ext i
      fin_cases i <;> simp [corePoint,zsmul_eq_mul]
    rw [hn,← hz]
    exact hperiod.zsmul n q
  rw [sphereFamilyTimeVelocity_eq_deriv H hH,sphereFamilyTimeVelocity_eq_deriv H hH,hsame]

lemma local_sphere_family_velocity_contDiffAt (H : ℝ → Jet3 → Jet3)
    (hH : ContDiff ℝ ∞ (fun q : ℝ × Jet3 => H q.1 q.2))
    (r : ℝ × Phase → Jet3) (q : ℝ × Phase) (hr : ContDiffAt ℝ ∞ r q) :
    ContDiffAt ℝ ∞ (fun z : ℝ × Phase => sphereFamilyTimeVelocity H (z.1,r z)) q :=
  (sphereFamilyTimeVelocity_contDiff H hH).contDiffAt.comp q (contDiffAt_fst.prodMk hr)

end
end ContactTopology

namespace ContactTopology
open BirkhoffGlobalSection BirkhoffGlobalSection.HopfTransport Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma sphereFamilyTimeVelocity_tangent (H : ℝ → Jet3 → Jet3)
    (hH : ContDiff ℝ ∞ (fun q : ℝ × Jet3 => H q.1 q.2)) (t : ℝ) (p : Jet3) :
    phaseDot (legendrianSphereChart (H t p)) (sphereFamilyTimeVelocity H (t,p)) = 0 := by
  have he := fderiv_comp (t,p) (legendrianSphereChart_contDiff.differentiable (by simp) (H t p))
    (hH.differentiable (by simp) (t,p))
  unfold sphereFamilyTimeVelocity
  change phaseDot (legendrianSphereChart (H t p))
    (fderiv ℝ (legendrianSphereChart ∘ (fun q : ℝ × Jet3 => H q.1 q.2)) (t,p) (1,0)) = 0
  rw [he]
  exact legendrianSphereChart_fderiv_tangent _ _

lemma sphereFamilyTimeVelocity_half_shift (H : ℝ → Jet3 → Jet3)
    (hH : ContDiff ℝ ∞ (fun q : ℝ × Jet3 => H q.1 q.2))
    (hper : ∀ t p, H t (p+corePoint (1/2)) = H t p+corePoint (1/2)) (t : ℝ) (p : Jet3) :
    sphereFamilyTimeVelocity H (t,p+corePoint (1/2)) = -sphereFamilyTimeVelocity H (t,p) := by
  have heq : (fun s => legendrianSphereChart (H s (p+corePoint (1/2)))) =
      fun s => -legendrianSphereChart (H s p) := by
    funext s
    rw [hper,legendrianSphereChart_antipodal]
  rw [sphereFamilyTimeVelocity_eq_deriv H hH,sphereFamilyTimeVelocity_eq_deriv H hH,heq]
  exact deriv.neg

lemma sphereFamilyTimeVelocity_core_zero (H : ℝ → Jet3 → Jet3)
    (hH : ContDiff ℝ ∞ (fun q : ℝ × Jet3 => H q.1 q.2))
    (hcore : ∀ t x, H t (corePoint x) = corePoint x) (t x : ℝ) :
    sphereFamilyTimeVelocity H (t,corePoint x) = 0 := by
  have heq : (fun s => legendrianSphereChart (H s (corePoint x))) = fun _ : ℝ => legendrianSphereChart (corePoint x) := by
    funext s
    rw [hcore]
  rw [sphereFamilyTimeVelocity_eq_deriv H hH,heq]
  exact deriv_const t _

def sphereFamilyHamiltonianOnCover (H : ℝ → Jet3 → Jet3) (q : ℝ × Jet3) : ℝ :=
  phaseRadialContact (legendrianSphereChart (H q.1 q.2)) (sphereFamilyTimeVelocity H q)

lemma sphereFamilyHamiltonianOnCover_contDiff (H : ℝ → Jet3 → Jet3)
    (hH : ContDiff ℝ ∞ (fun q : ℝ × Jet3 => H q.1 q.2)) :
    ContDiff ℝ ∞ (sphereFamilyHamiltonianOnCover H) := by
  let A : ℝ × Jet3 → Phase := fun q => legendrianSphereChart (H q.1 q.2)
  let V := sphereFamilyTimeVelocity H
  have hA : ContDiff ℝ ∞ A := legendrianSphereChart_contDiff.comp hH
  have hV : ContDiff ℝ ∞ V := sphereFamilyTimeVelocity_contDiff H hH
  change ContDiff ℝ ∞ (fun q => phaseRadialContact (A q) (V q))
  dsimp [phaseRadialContact,phaseSymplecticForm]
  fun_prop

lemma sphereFamilyHamiltonianOnCover_half_period (H : ℝ → Jet3 → Jet3)
    (hH : ContDiff ℝ ∞ (fun q : ℝ × Jet3 => H q.1 q.2))
    (hper : ∀ t p, H t (p+corePoint (1/2)) = H t p+corePoint (1/2)) (t : ℝ) (p : Jet3) :
    sphereFamilyHamiltonianOnCover H (t,p+corePoint (1/2)) = sphereFamilyHamiltonianOnCover H (t,p) := by
  unfold sphereFamilyHamiltonianOnCover
  rw [hper,legendrianSphereChart_antipodal,sphereFamilyTimeVelocity_half_shift H hH hper]
  simp [phaseRadialContact,phaseSymplecticForm]

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

lemma contact_family_joint_open_inverse (H : ℝ → Jet3 → Jet3)
    (hH : ContDiff ℝ ∞ (fun q : ℝ × Jet3 => H q.1 q.2))
    (U : Set Jet3) (hU : IsOpen U)
    (hcontact : ∀ t p, p ∈ U → ∃ a : ℝ, 0 < a ∧ ∀ v,
      jetContact (H t p) (fderiv ℝ (H t) p v) = a*jetContact p v)
    (t : ℝ) (p : Jet3) (hp : p ∈ U) :
    ∃ b : ℝ × Jet3 → Jet3, ∃ W : Set (ℝ × Jet3), IsOpen W ∧ (t,H t p) ∈ W ∧
      ContDiffOn ℝ ∞ b W ∧ b (t,H t p) = p ∧
      (∀ᶠ q : ℝ × Jet3 in 𝓝 (t,p), b (q.1,H q.1 q.2) = q.2) ∧
      ∀ q ∈ W, H q.1 (b q) = q.2 ∧ b q ∈ U := by
  let G : ℝ × Jet3 → ℝ × Jet3 := fun q => (q.1,H q.1 q.2)
  have hG : ContDiff ℝ ∞ G := contDiff_fst.prodMk hH
  have hinj : ∀ q ∈ univ ×ˢ U, Injective (fderiv ℝ G q) := by
    intro q hq
    have hHt : ContDiff ℝ ∞ (H q.1) := hH.comp (contDiff_const.prodMk contDiff_id)
    have hsp := jet_contact_derivative_injective_of_positive_factor (H q.1) hHt U hU
      (hcontact q.1) q.2 hq.2
    exact family_world_derivative_injective H hH q.1 q.2 hsp
  obtain ⟨R,W,hW,hWp,hR,hRp,hleft,hright⟩ := smooth_local_inverse_on_open G hG
    (univ ×ˢ U) (isOpen_univ.prod hU) hinj (t,p) ⟨mem_univ t,hp⟩ rfl
  have hRsm : ContDiffOn ℝ ∞ (fun q => (R q).2) W := contDiff_snd.comp_contDiffOn hR
  refine ⟨fun q => (R q).2,W,hW,hWp,hRsm,congrArg Prod.snd hRp,?_,?_⟩
  · filter_upwards [hleft] with q hq
    exact congrArg Prod.snd hq
  · intro q hq
    have hh := hright q hq
    have ht := congrArg Prod.fst hh.1
    change (R q).1 = q.1 at ht
    have hx := congrArg Prod.snd hh.1
    change H (R q).1 (R q).2 = q.2 at hx
    rw [ht] at hx
    exact ⟨hx,hh.2.2⟩

lemma legendrian_family_sphere_open_inverse (H : ℝ → Jet3 → Jet3)
    (hH : ContDiff ℝ ∞ (fun q : ℝ × Jet3 => H q.1 q.2))
    (U : Set Jet3) (hU : IsOpen U)
    (hcontact : ∀ t p, p ∈ U → ∃ a : ℝ, 0 < a ∧ ∀ v,
      jetContact (H t p) (fderiv ℝ (H t) p v) = a*jetContact p v)
    (t : ℝ) (p : Jet3) (hp : p ∈ U) :
    ∃ r : ℝ × Phase → Jet3, ∃ Q : Set (ℝ × Phase), IsOpen Q ∧ (t,legendrianSphereChart (H t p)) ∈ Q ∧
      ContDiffOn ℝ ∞ r Q ∧ r (t,legendrianSphereChart (H t p)) = p ∧
      (∀ᶠ q : ℝ × Jet3 in 𝓝 (t,p), r (q.1,legendrianSphereChart (H q.1 q.2)) = q.2) ∧
      ∀ q ∈ Q, (q.2 ∈ unitThreeSphere → legendrianSphereChart (H q.1 (r q)) = q.2) ∧ r q ∈ U := by
  obtain ⟨c,V,hV,hVp,hc,hcp,hcleft,hcright⟩ := legendrianSphereChart_open_inverse (H t p)
  obtain ⟨b,W,hW,hWp,hb,hbp,hbleft,hbright⟩ := contact_family_joint_open_inverse H hH U hU hcontact t p hp
  let K : ℝ × Phase → ℝ × Jet3 := fun q => (q.1,c q.2)
  let D : Set (ℝ × Phase) := univ ×ˢ V
  have hD : IsOpen D := isOpen_univ.prod hV
  have hK : ContDiffOn ℝ ∞ K D := by
    intro q hq
    have hcat : ContDiffAt ℝ ∞ c q.2 := (hc q.2 hq.2).contDiffAt (hV.mem_nhds hq.2)
    exact (contDiffAt_fst.prodMk (hcat.comp q contDiffAt_snd)).contDiffWithinAt
  let Q := D ∩ K ⁻¹' W
  have hQ : IsOpen Q := hK.continuousOn.isOpen_inter_preimage hD hW
  have hKpoint : K (t,legendrianSphereChart (H t p)) = (t,H t p) := by
    change (t,c (legendrianSphereChart (H t p))) = _
    rw [hcp]
  have hQp : (t,legendrianSphereChart (H t p)) ∈ Q := ⟨⟨mem_univ t,hVp⟩,by change K _ ∈ W; rw [hKpoint]; exact hWp⟩
  have hr : ContDiffOn ℝ ∞ (b ∘ K) Q := hb.comp (hK.mono inter_subset_left) (fun q hq => hq.2)
  refine ⟨b ∘ K,Q,hQ,hQp,hr,?_,?_,?_⟩
  · change b (K (t,legendrianSphereChart (H t p))) = _
    rw [hKpoint,hbp]
  · have hi : Tendsto (fun q : ℝ × Jet3 => H q.1 q.2) (𝓝 (t,p)) (𝓝 (H t p)) := hH.continuous.continuousAt
    filter_upwards [hi.eventually hcleft,hbleft] with q hq hbq
    change b (q.1,c (legendrianSphereChart (H q.1 q.2))) = _
    rw [hq]
    exact hbq
  · intro q hq
    have hh := hbright (K q) hq.2
    refine ⟨?_,hh.2⟩
    intro hqs
    change legendrianSphereChart (H q.1 (b (K q))) = _
    have hhx := hh.1
    change H q.1 (b (K q)) = c q.2 at hhx
    rw [hhx]
    exact hcright q.2 hq.1.2 hqs

end
end ContactTopology

namespace ContactTopology
open BirkhoffGlobalSection BirkhoffGlobalSection.HopfTransport Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

def movingChartPreimage (e : ℝ) (H : ℝ → Jet3 → Jet3) (q : ℝ × Phase) : Jet3 := by
  classical
  exact if h : ∃ p ∈ normalStrip e, legendrianSphereChart (H q.1 p) = radialNormalize q.2 then h.choose else 0

lemma movingChartPreimage_spec (e : ℝ) (H : ℝ → Jet3 → Jet3) (q : ℝ × Phase)
    (h : ∃ p ∈ normalStrip e, legendrianSphereChart (H q.1 p) = radialNormalize q.2) :
    movingChartPreimage e H q ∈ normalStrip e ∧
      legendrianSphereChart (H q.1 (movingChartPreimage e H q)) = radialNormalize q.2 := by
  classical
  simp only [movingChartPreimage,dif_pos h]
  exact h.choose_spec

def movingSphereTube (e : ℝ) (H : ℝ → Jet3 → Jet3) : Set (ℝ × Phase) :=
  {q | 0 < zNormSq q.2+wNormSq q.2 ∧
    ∃ p ∈ normalStrip e, legendrianSphereChart (H q.1 p) = radialNormalize q.2}

def movingSphereHamiltonian (e : ℝ) (H : ℝ → Jet3 → Jet3) (q : ℝ × Phase) : ℝ :=
  sphereFamilyHamiltonianOnCover H (q.1,movingChartPreimage e H q)

lemma movingSphereHamiltonian_eq (e : ℝ) (H : ℝ → Jet3 → Jet3)
    (hH : ContDiff ℝ ∞ (fun q : ℝ × Jet3 => H q.1 q.2))
    (hinj : ∀ t, InjOn (H t) (normalStrip e))
    (hper : ∀ t p, H t (p+corePoint 1) = H t p+corePoint 1)
    (q : ℝ × Phase) (p : Jet3) (hp : p ∈ normalStrip e)
    (htrace : legendrianSphereChart (H q.1 p) = radialNormalize q.2) :
    movingSphereHamiltonian e H q = sphereFamilyHamiltonianOnCover H (q.1,p) := by
  have hpre := movingChartPreimage_spec e H q ⟨p,hp,htrace⟩
  have heq := hpre.2.trans htrace.symm
  have hv := sphereFamilyTimeVelocity_fiber_independent e H hH hinj hper q.1
    (movingChartPreimage e H q) p hpre.1 hp heq
  unfold movingSphereHamiltonian sphereFamilyHamiltonianOnCover
  rw [heq,hv]

/-- Each point of the radial moving tube has a genuine smooth local
Hamiltonian representative, and the representative agrees throughout its
whole open domain, independently of the chosen covering coordinate. -/
lemma movingSphereHamiltonian_local_representative (e : ℝ) (H : ℝ → Jet3 → Jet3)
    (hH : ContDiff ℝ ∞ (fun q : ℝ × Jet3 => H q.1 q.2))
    (hinj : ∀ t, InjOn (H t) (normalStrip e))
    (hper : ∀ t p, H t (p+corePoint 1) = H t p+corePoint 1)
    (hcontact : ∀ t p, p ∈ normalStrip e → ∃ a : ℝ, 0 < a ∧ ∀ v,
      jetContact (H t p) (fderiv ℝ (H t) p v) = a*jetContact p v)
    (q : ℝ × Phase) (hq : q ∈ movingSphereTube e H) :
    ∃ S : Set (ℝ × Phase), ∃ g : ℝ × Phase → ℝ,
      IsOpen S ∧ q ∈ S ∧ S ⊆ movingSphereTube e H ∧
      ContDiffOn ℝ ∞ g S ∧ EqOn (movingSphereHamiltonian e H) g S := by
  obtain ⟨p,hp,htrace⟩ := hq.2
  obtain ⟨r,Q,hQ,hQp,hr,hrp,hleft,hright⟩ := legendrian_family_sphere_open_inverse H hH
    (normalStrip e) (normalStrip_isOpen e) hcontact q.1 p hp
  rw [htrace] at hQp
  let K : ℝ × Phase → ℝ × Phase := fun z => (z.1,radialNormalize z.2)
  let P : Set (ℝ × Phase) := {z | 0 < zNormSq z.2+wNormSq z.2}
  have hP : IsOpen P := by
    have hc : Continuous (fun z : ℝ × Phase => zNormSq z.2+wNormSq z.2) := by
      dsimp [zNormSq,wNormSq]
      fun_prop
    exact isOpen_lt continuous_const hc
  have hK : ContDiffOn ℝ ∞ K P := by
    intro z hz
    have hN := (radial_normalization_contact_identity z.2 hz).1
    exact (contDiffAt_fst.prodMk (hN.comp z contDiffAt_snd)).contDiffWithinAt
  let S := P ∩ K ⁻¹' Q
  have hS : IsOpen S := hK.continuousOn.isOpen_inter_preimage hP hQ
  have hSq : q ∈ S := ⟨hq.1,hQp⟩
  have hsub : S ⊆ movingSphereTube e H := by
    intro z hz
    have hh := hright (K z) hz.2
    exact ⟨hz.1,r (K z),hh.2,hh.1 (radial_normalization_contact_identity z.2 hz.1).2.1⟩
  let g : ℝ × Phase → ℝ := fun z => sphereFamilyHamiltonianOnCover H (z.1,r (K z))
  have hrK : ContDiffOn ℝ ∞ (fun z => r (K z)) S :=
    hr.comp (hK.mono inter_subset_left) (fun z hz => hz.2)
  have hg : ContDiffOn ℝ ∞ g S :=
    (sphereFamilyHamiltonianOnCover_contDiff H hH).comp_contDiffOn (contDiffOn_fst.prodMk hrK)
  refine ⟨S,g,hS,hSq,hsub,hg,?_⟩
  intro z hz
  have hh := hright (K z) hz.2
  exact movingSphereHamiltonian_eq e H hH hinj hper z (r (K z)) hh.2
    (hh.1 (radial_normalization_contact_identity z.2 hz.1).2.1)

lemma movingSphereTube_isOpen (e : ℝ) (H : ℝ → Jet3 → Jet3)
    (hH : ContDiff ℝ ∞ (fun q : ℝ × Jet3 => H q.1 q.2))
    (hinj : ∀ t, InjOn (H t) (normalStrip e))
    (hper : ∀ t p, H t (p+corePoint 1) = H t p+corePoint 1)
    (hcontact : ∀ t p, p ∈ normalStrip e → ∃ a : ℝ, 0 < a ∧ ∀ v,
      jetContact (H t p) (fderiv ℝ (H t) p v) = a*jetContact p v) :
    IsOpen (movingSphereTube e H) := by
  apply isOpen_iff_mem_nhds.mpr
  intro q hq
  obtain ⟨S,g,hS,hSq,hsub,hg,heq⟩ := movingSphereHamiltonian_local_representative e H hH hinj hper hcontact q hq
  exact mem_of_superset (hS.mem_nhds hSq) hsub

lemma movingSphereHamiltonian_contDiffOn (e : ℝ) (H : ℝ → Jet3 → Jet3)
    (hH : ContDiff ℝ ∞ (fun q : ℝ × Jet3 => H q.1 q.2))
    (hinj : ∀ t, InjOn (H t) (normalStrip e))
    (hper : ∀ t p, H t (p+corePoint 1) = H t p+corePoint 1)
    (hcontact : ∀ t p, p ∈ normalStrip e → ∃ a : ℝ, 0 < a ∧ ∀ v,
      jetContact (H t p) (fderiv ℝ (H t) p v) = a*jetContact p v) :
    ContDiffOn ℝ ∞ (movingSphereHamiltonian e H) (movingSphereTube e H) := by
  intro q hq
  obtain ⟨S,g,hS,hSq,hsub,hg,heq⟩ := movingSphereHamiltonian_local_representative e H hH hinj hper hcontact q hq
  have hEq : movingSphereHamiltonian e H =ᶠ[𝓝 q] g := by
    filter_upwards [hS.mem_nhds hSq] with z hz
    exact heq hz
  exact (((hg q hSq).contDiffAt (hS.mem_nhds hSq)).congr_of_eventuallyEq hEq).contDiffWithinAt

end
end ContactTopology

namespace ContactTopology
open BirkhoffGlobalSection BirkhoffGlobalSection.HopfTransport Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Symmetrization retains a prescribed first jet on an invariant compact set. -/
lemma compact_invariant_first_jet_extension {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (tau : E ≃L[ℝ] E) (htau : ∀ x, tau (tau x) = x)
    (D : Set E) (hD : IsOpen D) (f : E → ℝ) (hf : ContDiffOn ℝ ∞ f D)
    (heven : ∀ x ∈ D, f (tau x) = f x)
    (C : Set E) (hC : IsCompact C) (hCD : C ⊆ D) (hCinv : ∀ x ∈ C, tau x ∈ C) :
    ∃ G : E → ℝ, ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧
      (∀ x, G (tau x) = G x) ∧ ∀ x ∈ C, G x = f x ∧ fderiv ℝ G x = fderiv ℝ f x := by
  obtain ⟨g,hg,hgc,hjet⟩ := SmoothJetExtension.compact_first_jet_extension C hC f (fderiv ℝ f) (by
    intro x hx
    exact ⟨D,hD,hCD hx,f,hf,fun q hq => ⟨rfl,rfl⟩⟩)
  let G : E → ℝ := fun x => (1/2:ℝ)*(g x+g (tau x))
  have hG : ContDiff ℝ ∞ G := contDiff_const.mul (hg.add (hg.comp tau.contDiff))
  have hGc : HasCompactSupport G := by
    have hh : HasCompactSupport (g+g ∘ tau) := hgc.add (hgc.comp_homeomorph tau.toHomeomorph)
    exact hh.mul_left
  refine ⟨G,hG,hGc,?_,?_⟩
  · intro x
    dsimp [G]
    rw [htau]
    ring
  · intro x hx
    have hxD := hCD hx
    have htx := hCinv x hx
    have htxD := hCD htx
    refine ⟨?_,?_⟩
    · dsimp [G]
      rw [(hjet x hx).1,(hjet (tau x) htx).1,heven x hxD]
      ring
    · have heq : (f ∘ tau) =ᶠ[𝓝 x] f := by
        filter_upwards [hD.mem_nhds hxD] with y hy
        exact heven y hy
      have hfd := (hf x hxD).contDiffAt (hD.mem_nhds hxD)
      have hft := (hf (tau x) htxD).contDiffAt (hD.mem_nhds htxD)
      have hcomp : (fderiv ℝ f (tau x)).comp (tau : E →L[ℝ] E) = fderiv ℝ f x := by
        have hh : fderiv ℝ (f ∘ tau) x = fderiv ℝ f x := heq.fderiv_eq
        rw [fderiv_comp x (hft.differentiableAt (by simp)) tau.differentiableAt,
          tau.hasFDerivAt.fderiv] at hh
        exact hh
      have hd := ((hg.differentiable (by simp) x).hasFDerivAt.add
        ((hg.differentiable (by simp) (tau x)).hasFDerivAt.comp x tau.hasFDerivAt)).const_smul (1/2:ℝ)
      change HasFDerivAt G _ x at hd
      rw [hd.fderiv,(hjet x hx).2,(hjet (tau x) htx).2,hcomp]
      ext v
      simp
      ring

def timeAntipodalEquiv : (ℝ × Phase) ≃L[ℝ] (ℝ × Phase) :=
  (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr (ContinuousLinearEquiv.neg ℝ)

lemma timeAntipodalEquiv_apply (q : ℝ × Phase) : timeAntipodalEquiv q = (q.1,-q.2) := rfl

lemma timeAntipodalEquiv_involutive (q : ℝ × Phase) : timeAntipodalEquiv (timeAntipodalEquiv q) = q := by
  simp only [timeAntipodalEquiv_apply,neg_neg]

lemma phaseRadiusSq_neg (y : Phase) : zNormSq (-y)+wNormSq (-y) = zNormSq y+wNormSq y := by
  simp [zNormSq,wNormSq]

lemma movingSphereTube_antipodal (e : ℝ) (H : ℝ → Jet3 → Jet3)
    (hper : ∀ t p, H t (p+corePoint (1/2)) = H t p+corePoint (1/2))
    (q : ℝ × Phase) (hq : q ∈ movingSphereTube e H) :
    timeAntipodalEquiv q ∈ movingSphereTube e H := by
  obtain ⟨p,hp,htrace⟩ := hq.2
  refine ⟨?_,p+corePoint (1/2),(normalStrip_translate e (1/2) p).mpr hp,?_⟩
  · change 0 < zNormSq (-q.2)+wNormSq (-q.2)
    rw [phaseRadiusSq_neg]
    exact hq.1
  · change legendrianSphereChart (H q.1 (p+corePoint (1/2))) = radialNormalize (-q.2)
    rw [hper,legendrianSphereChart_antipodal,htrace]
    exact (radial_normalization_contact_identity q.2 hq.1).2.2.1.symm

lemma movingSphereHamiltonian_even (e : ℝ) (H : ℝ → Jet3 → Jet3)
    (hH : ContDiff ℝ ∞ (fun q : ℝ × Jet3 => H q.1 q.2))
    (hinj : ∀ t, InjOn (H t) (normalStrip e))
    (hper : ∀ t p, H t (p+corePoint 1) = H t p+corePoint 1)
    (hhalf : ∀ t p, H t (p+corePoint (1/2)) = H t p+corePoint (1/2))
    (q : ℝ × Phase) (hq : q ∈ movingSphereTube e H) :
    movingSphereHamiltonian e H (timeAntipodalEquiv q) = movingSphereHamiltonian e H q := by
  obtain ⟨p,hp,htrace⟩ := hq.2
  have htrace' : legendrianSphereChart (H q.1 (p+corePoint (1/2))) = radialNormalize (-q.2) := by
    rw [hhalf,legendrianSphereChart_antipodal,htrace]
    exact (radial_normalization_contact_identity q.2 hq.1).2.2.1.symm
  rw [movingSphereHamiltonian_eq e H hH hinj hper (timeAntipodalEquiv q) (p+corePoint (1/2))
      ((normalStrip_translate e (1/2) p).mpr hp) htrace',
    movingSphereHamiltonian_eq e H hH hinj hper q p hp htrace]
  exact sphereFamilyHamiltonianOnCover_half_period H hH hhalf q.1 p

lemma movingSphereHamiltonian_compact_even_extension (e : ℝ) (H : ℝ → Jet3 → Jet3)
    (hH : ContDiff ℝ ∞ (fun q : ℝ × Jet3 => H q.1 q.2))
    (hinj : ∀ t, InjOn (H t) (normalStrip e))
    (hper : ∀ t p, H t (p+corePoint 1) = H t p+corePoint 1)
    (hhalf : ∀ t p, H t (p+corePoint (1/2)) = H t p+corePoint (1/2))
    (hcontact : ∀ t p, p ∈ normalStrip e → ∃ a : ℝ, 0 < a ∧ ∀ v,
      jetContact (H t p) (fderiv ℝ (H t) p v) = a*jetContact p v)
    (C : Set (ℝ × Phase)) (hC : IsCompact C) (hCD : C ⊆ movingSphereTube e H)
    (hCinv : ∀ q ∈ C, timeAntipodalEquiv q ∈ C) :
    ∃ G : ℝ × Phase → ℝ, ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧
      (∀ t y, G (t,-y) = G (t,y)) ∧
      ∀ q ∈ C, G q = movingSphereHamiltonian e H q ∧
        fderiv ℝ G q = fderiv ℝ (movingSphereHamiltonian e H) q := by
  obtain ⟨G,hG,hGc,heven,hjet⟩ := compact_invariant_first_jet_extension
    timeAntipodalEquiv timeAntipodalEquiv_involutive (movingSphereTube e H)
    (movingSphereTube_isOpen e H hH hinj hper hcontact) (movingSphereHamiltonian e H)
    (movingSphereHamiltonian_contDiffOn e H hH hinj hper hcontact)
    (movingSphereHamiltonian_even e H hH hinj hper hhalf) C hC hCD hCinv
  exact ⟨G,hG,hGc,fun t y => heven (t,y),hjet⟩

end
end ContactTopology

namespace ContactTopology
open BirkhoffGlobalSection BirkhoffGlobalSection.HopfTransport Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma normalize_sphere_point (y : Phase) (hy : y ∈ unitThreeSphere) : radialNormalize y = y := by
  change zNormSq y+wNormSq y = 1 at hy
  simp [radialNormalize,hy]

/-- The descended Hamiltonian admits a globally smooth, compactly supported,
antipodally even extension preserving its full first jet on a uniform smaller
moving tube, for every longitudinal coordinate and both endpoint times. -/
lemma compact_tube_hamiltonian_extension (e : ℝ) (he : 0 < e) (H : ℝ → Jet3 → Jet3)
    (hH : ContDiff ℝ ∞ (fun q : ℝ × Jet3 => H q.1 q.2))
    (hinj : ∀ t, InjOn (H t) (normalStrip e))
    (hper : ∀ t p, H t (p+corePoint 1) = H t p+corePoint 1)
    (hhalf : ∀ t p, H t (p+corePoint (1/2)) = H t p+corePoint (1/2))
    (hcontact : ∀ t p, p ∈ normalStrip e → ∃ a : ℝ, 0 < a ∧ ∀ v,
      jetContact (H t p) (fderiv ℝ (H t) p v) = a*jetContact p v) :
    ∃ d : ℝ, 0 < d ∧ d < e ∧ ∃ G : ℝ × Phase → ℝ,
      ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧ (∀ t y, G (t,-y) = G (t,y)) ∧
      ∀ t ∈ Icc (0:ℝ) 1, ∀ p : Jet3, |p 1| ≤ d → |p 2| ≤ d →
        G (t,legendrianSphereChart (H t p)) = sphereFamilyHamiltonianOnCover H (t,p) ∧
        fderiv ℝ G (t,legendrianSphereChart (H t p)) =
          fderiv ℝ (movingSphereHamiltonian e H) (t,legendrianSphereChart (H t p)) := by
  let d := e/2
  have hd : 0 < d := half_pos he
  have hde : d < e := half_lt_self he
  let B : Set (ℝ × Jet3) := Icc (0:ℝ) 1 ×ˢ Icc ![0,-d,-d] ![1,d,d]
  let A : ℝ × Jet3 → ℝ × Phase := fun q => (q.1,legendrianSphereChart (H q.1 q.2))
  let C₀ := A '' B
  let C := C₀ ∪ timeAntipodalEquiv '' C₀
  have hB : IsCompact B := isCompact_Icc.prod isCompact_Icc
  have hA : Continuous A := continuous_fst.prodMk (legendrianSphereChart_contDiff.comp hH).continuous
  have hC₀ : IsCompact C₀ := hB.image hA
  have hC : IsCompact C := hC₀.union (hC₀.image timeAntipodalEquiv.continuous)
  have hC₀D : C₀ ⊆ movingSphereTube e H := by
    rintro q ⟨z,hz,rfl⟩
    have hylo := hz.2.1 (1:Fin 3)
    have hyhi := hz.2.2 (1:Fin 3)
    have hzlo := hz.2.1 (2:Fin 3)
    have hzhi := hz.2.2 (2:Fin 3)
    change -d ≤ z.2 1 at hylo
    change z.2 1 ≤ d at hyhi
    change -d ≤ z.2 2 at hzlo
    change z.2 2 ≤ d at hzhi
    have hp : z.2 ∈ normalStrip e :=
      ⟨lt_of_le_of_lt (abs_le.mpr ⟨hylo,hyhi⟩) hde,lt_of_le_of_lt (abs_le.mpr ⟨hzlo,hzhi⟩) hde⟩
    have hunit := legendrianSphereChart_mem (H z.1 z.2)
    have hradius : zNormSq (legendrianSphereChart (H z.1 z.2))+
        wNormSq (legendrianSphereChart (H z.1 z.2)) = 1 := hunit
    refine ⟨?_,z.2,hp,?_⟩
    · change 0 < zNormSq (legendrianSphereChart (H z.1 z.2))+wNormSq (legendrianSphereChart (H z.1 z.2))
      rw [hradius]
      norm_num
    · exact (normalize_sphere_point _ hunit).symm
  have hCD : C ⊆ movingSphereTube e H := by
    intro q hq
    rcases hq with hq|⟨z,hz,rfl⟩
    · exact hC₀D hq
    · exact movingSphereTube_antipodal e H hhalf z (hC₀D hz)
  have hCinv : ∀ q ∈ C, timeAntipodalEquiv q ∈ C := by
    intro q hq
    rcases hq with hq|⟨z,hz,rfl⟩
    · exact Or.inr ⟨q,hq,rfl⟩
    · exact Or.inl (by simpa only [timeAntipodalEquiv_involutive] using hz)
  obtain ⟨G,hG,hGc,heven,hjet⟩ := movingSphereHamiltonian_compact_even_extension e H hH hinj hper hhalf hcontact C hC hCD hCinv
  refine ⟨d,hd,hde,G,hG,hGc,heven,?_⟩
  intro t ht p hp₁ hp₂
  let r : Jet3 := ![Int.fract (p 0),p 1,p 2]
  have hrrep : r = p-⌊p 0⌋ • corePoint 1 := by
    have hz : ⌊p 0⌋ • corePoint 1 = corePoint (⌊p 0⌋ : ℝ) := by
      ext i
      fin_cases i <;> simp [corePoint,zsmul_eq_mul]
    rw [hz]
    ext i
    fin_cases i
    · change Int.fract (p 0) = p 0-(⌊p 0⌋ : ℝ)
      rfl
    · change p 1 = p 1-0
      ring
    · change p 2 = p 2-0
      ring
  have hrB : r ∈ Icc ![0,-d,-d] ![1,d,d] := by
    constructor
    · intro i
      fin_cases i
      · exact Int.fract_nonneg _
      · exact (abs_le.mp hp₁).1
      · exact (abs_le.mp hp₂).1
    · intro i
      fin_cases i
      · exact (Int.fract_lt_one _).le
      · exact (abs_le.mp hp₁).2
      · exact (abs_le.mp hp₂).2
  have hperiod : Periodic (fun q => legendrianSphereChart (H t q)) (corePoint 1) := by
    intro q
    change legendrianSphereChart (H t (q+corePoint 1)) = legendrianSphereChart (H t q)
    rw [hper,legendrianSphereChart_periodic]
  have himg : legendrianSphereChart (H t r) = legendrianSphereChart (H t p) := by
    rw [hrrep]
    exact hperiod.sub_zsmul_eq ⌊p 0⌋
  have hpoint : (t,legendrianSphereChart (H t p)) ∈ C :=
    Or.inl ⟨(t,r),⟨ht,hrB⟩,Prod.ext rfl himg⟩
  have hj := hjet _ hpoint
  refine ⟨?_,hj.2⟩
  rw [hj.1]
  exact movingSphereHamiltonian_eq e H hH hinj hper (t,legendrianSphereChart (H t p)) p
    ⟨lt_of_le_of_lt hp₁ hde,lt_of_le_of_lt hp₂ hde⟩
    (normalize_sphere_point _ (legendrianSphereChart_mem _)).symm

end
end ContactTopology

namespace ContactTopology
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

lemma fderiv_clm_eval {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : E → V →L[ℝ] ℝ) (q u : E) (v : V) (hB : DifferentiableAt ℝ B q) :
    fderiv ℝ (fun z => B z v) q u = fderiv ℝ B q u v := by
  rw [fderiv_clm_apply hB (differentiableAt_const v)]
  simp

def familyContactPullback (A : ℝ × Jet3 → Phase) (q : ℝ × Jet3) : (ℝ × Jet3) →L[ℝ] ℝ :=
  (sphereRadialForm (A q)).comp (fderiv ℝ A q)

lemma familyContactPullback_contDiff (A : ℝ × Jet3 → Phase) (hA : ContDiff ℝ ∞ A) :
    ContDiff ℝ ∞ (familyContactPullback A) :=
  (sphereRadialForm_contDiff.comp hA).clm_comp (hA.fderiv_right (by simp))

def familyContactHamiltonian (A : ℝ × Jet3 → Phase) (q : ℝ × Jet3) : ℝ :=
  familyContactPullback A q (1,0)

lemma familyContactHamiltonian_contDiff (A : ℝ × Jet3 → Phase) (hA : ContDiff ℝ ∞ A) :
    ContDiff ℝ ∞ (familyContactHamiltonian A) :=
  (familyContactPullback_contDiff A hA).clm_apply contDiff_const

/-- Cartan's generator identity follows by applying exterior-derivative
naturality to the joint map, in the time and spatial directions. -/
lemma contact_family_hamiltonian_identity (A : ℝ × Jet3 → Phase) (hA : ContDiff ℝ ∞ A)
    (U : Set Jet3) (hU : IsOpen U) (lam : ℝ × Jet3 → ℝ) (hlam : ContDiff ℝ ∞ lam)
    (hcontact : ∀ q : ℝ × Jet3, q.2 ∈ U → ∀ v : Jet3,
      phaseRadialContact (A q) (fderiv ℝ A q (0,v)) = lam q*jetContact q.2 v)
    (q : ℝ × Jet3) (hq : q.2 ∈ U) (v : Jet3) :
    fderiv ℝ (familyContactHamiltonian A) q (0,v)+
      2*phaseRadialContact (fderiv ℝ A q (1,0)) (fderiv ℝ A q (0,v)) =
        fderiv ℝ lam q (1,0)*jetContact q.2 v := by
  let B := familyContactPullback A
  have hB : ContDiff ℝ ∞ B := familyContactPullback_contDiff A hA
  have heq : (fun z : ℝ × Jet3 => B z (0,v)) =ᶠ[𝓝 q]
      (fun z => lam z*jetContact z.2 v) := by
    have hn : ∀ᶠ z : ℝ × Jet3 in 𝓝 q, z.2 ∈ U :=
      continuous_snd.continuousAt.preimage_mem_nhds (hU.mem_nhds hq)
    filter_upwards [hn] with z hz
    change sphereRadialForm (A z) (fderiv ℝ A z (0,v)) = _
    rw [sphereRadialForm_apply]
    exact hcontact z hz v
  have hdeq : fderiv ℝ (fun z : ℝ × Jet3 => B z (0,v)) q =
      fderiv ℝ (fun z : ℝ × Jet3 => lam z*jetContact z.2 v) q := heq.fderiv_eq
  have hdJ := (hasFDerivAt_const (v 2) q).sub
    ((((ContinuousLinearMap.proj (1:Fin 3) : Jet3 →L[ℝ] ℝ).hasFDerivAt).comp q hasFDerivAt_snd).mul_const (v 0))
  change HasFDerivAt (fun z : ℝ × Jet3 => jetContact z.2 v) _ q at hdJ
  have hdprod := (hlam.differentiable (by simp) q).hasFDerivAt.mul hdJ
  change HasFDerivAt (fun z : ℝ × Jet3 => lam z*jetContact z.2 v) _ q at hdprod
  have htime : fderiv ℝ B q (1,0) (0,v) = fderiv ℝ lam q (1,0)*jetContact q.2 v := by
    rw [← fderiv_clm_eval B q (1,0) (0,v) (hB.differentiable (by simp) q),hdeq,hdprod.fderiv]
    simp [mul_comm]
  have hspace : fderiv ℝ B q (0,v) (1,0) = fderiv ℝ (familyContactHamiltonian A) q (0,v) := by
    exact (fderiv_clm_eval B q (0,v) (1,0) (hB.differentiable (by simp) q)).symm
  have hpb := ContactCalculus.exterior_pairing_pullback sphereRadialForm A q (1,0) (0,v)
    (sphereRadialForm_contDiff.differentiable (by simp) _)
    (hA.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  change fderiv ℝ B q (1,0) (0,v)-fderiv ℝ B q (0,v) (1,0) =
    fderiv ℝ sphereRadialForm (A q) (fderiv ℝ A q (1,0)) (fderiv ℝ A q (0,v))-
    fderiv ℝ sphereRadialForm (A q) (fderiv ℝ A q (0,v)) (fderiv ℝ A q (1,0)) at hpb
  rw [htime,hspace,sphereRadialForm_fderiv,sphereRadialForm_fderiv] at hpb
  have hskew : phaseRadialContact (fderiv ℝ A q (0,v)) (fderiv ℝ A q (1,0)) =
      -phaseRadialContact (fderiv ℝ A q (1,0)) (fderiv ℝ A q (0,v)) := by
    simp [phaseRadialContact,phaseSymplecticForm]
    ring
  rw [hskew] at hpb
  linarith

end
end ContactTopology

namespace ContactTopology
open BirkhoffGlobalSection BirkhoffGlobalSection.HopfTransport Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

def sphereFamilyMap (H : ℝ → Jet3 → Jet3) (q : ℝ × Jet3) : Phase := legendrianSphereChart (H q.1 q.2)

lemma sphereFamilyMap_contDiff (H : ℝ → Jet3 → Jet3)
    (hH : ContDiff ℝ ∞ (fun q : ℝ × Jet3 => H q.1 q.2)) : ContDiff ℝ ∞ (sphereFamilyMap H) :=
  legendrianSphereChart_contDiff.comp hH

lemma sphereFamilyMap_spatial_fderiv (H : ℝ → Jet3 → Jet3)
    (hH : ContDiff ℝ ∞ (fun q : ℝ × Jet3 => H q.1 q.2)) (q : ℝ × Jet3) (v : Jet3) :
    fderiv ℝ (sphereFamilyMap H) q (0,v) =
      fderiv ℝ legendrianSphereChart (H q.1 q.2) (fderiv ℝ (H q.1) q.2 v) := by
  have hd := fderiv_comp q (legendrianSphereChart_contDiff.differentiable (by simp) (H q.1 q.2))
    (hH.differentiable (by simp) q)
  change fderiv ℝ (legendrianSphereChart ∘ (fun r : ℝ × Jet3 => H r.1 r.2)) q (0,v) = _
  rw [hd]
  change fderiv ℝ legendrianSphereChart (H q.1 q.2)
    (fderiv ℝ (fun r : ℝ × Jet3 => H r.1 r.2) q (0,v)) = _
  rw [← joint_fderiv_slice_apply H hH q.1 q.2 v]

def sphereFamilyContactFactor (H : ℝ → Jet3 → Jet3) (q : ℝ × Jet3) : ℝ :=
  familyContactPullback (sphereFamilyMap H) q (0,Pi.single 2 1)

lemma sphereFamilyContactFactor_contDiff (H : ℝ → Jet3 → Jet3)
    (hH : ContDiff ℝ ∞ (fun q : ℝ × Jet3 => H q.1 q.2)) : ContDiff ℝ ∞ (sphereFamilyContactFactor H) :=
  (familyContactPullback_contDiff _ (sphereFamilyMap_contDiff H hH)).clm_apply contDiff_const

lemma sphereFamilyContactFactor_positive (e : ℝ) (H : ℝ → Jet3 → Jet3)
    (hH : ContDiff ℝ ∞ (fun q : ℝ × Jet3 => H q.1 q.2))
    (hcontact : ∀ t p, p ∈ normalStrip e → ∃ a : ℝ, 0 < a ∧ ∀ v,
      jetContact (H t p) (fderiv ℝ (H t) p v) = a*jetContact p v)
    (q : ℝ × Jet3) (hq : q.2 ∈ normalStrip e) :
    0 < sphereFamilyContactFactor H q ∧ ∀ v : Jet3,
      phaseRadialContact (sphereFamilyMap H q) (fderiv ℝ (sphereFamilyMap H) q (0,v)) =
        sphereFamilyContactFactor H q*jetContact q.2 v := by
  obtain ⟨a,ha,hc⟩ := hcontact q.1 q.2 hq
  have hformula : ∀ v : Jet3,
      phaseRadialContact (sphereFamilyMap H q) (fderiv ℝ (sphereFamilyMap H) q (0,v)) =
        (a*legendrianChartWeight (H q.1 q.2))*jetContact q.2 v := by
    intro v
    rw [sphereFamilyMap_spatial_fderiv H hH]
    change phaseRadialContact (legendrianSphereChart (H q.1 q.2)) _ = _
    rw [legendrianSphereChart_contact,hc]
    dsimp [legendrianChartWeight]
    ring
  have hfactor : sphereFamilyContactFactor H q = a*legendrianChartWeight (H q.1 q.2) := by
    change sphereRadialForm (sphereFamilyMap H q) (fderiv ℝ (sphereFamilyMap H) q (0,Pi.single 2 1)) = _
    rw [sphereRadialForm_apply]
    simpa [jetContact] using hformula (Pi.single 2 1)
  rw [hfactor]
  exact ⟨mul_pos ha (inv_pos.mpr (legendrianChartRaw_radius_positive _)),hformula⟩

lemma familyContactHamiltonian_sphereFamilyMap (H : ℝ → Jet3 → Jet3) :
    familyContactHamiltonian (sphereFamilyMap H) = sphereFamilyHamiltonianOnCover H := by
  funext q
  change sphereRadialForm (sphereFamilyMap H q) (fderiv ℝ (sphereFamilyMap H) q (1,0)) = _
  rw [sphereRadialForm_apply]
  rfl

lemma movingSphereTube_mem_image (e : ℝ) (H : ℝ → Jet3 → Jet3)
    (q : ℝ × Jet3) (hq : q.2 ∈ normalStrip e) :
    (q.1,sphereFamilyMap H q) ∈ movingSphereTube e H := by
  have hs := legendrianSphereChart_mem (H q.1 q.2)
  have hn : zNormSq (sphereFamilyMap H q)+wNormSq (sphereFamilyMap H q) = 1 := hs
  refine ⟨by change 0 < zNormSq (sphereFamilyMap H q)+wNormSq (sphereFamilyMap H q); rw [hn]; norm_num,
    q.2,hq,?_⟩
  exact (normalize_sphere_point _ hs).symm

lemma movingSphereHamiltonian_spatial_pullback (e : ℝ) (H : ℝ → Jet3 → Jet3)
    (hH : ContDiff ℝ ∞ (fun q : ℝ × Jet3 => H q.1 q.2))
    (hinj : ∀ t, InjOn (H t) (normalStrip e))
    (hper : ∀ t p, H t (p+corePoint 1) = H t p+corePoint 1)
    (hcontact : ∀ t p, p ∈ normalStrip e → ∃ a : ℝ, 0 < a ∧ ∀ v,
      jetContact (H t p) (fderiv ℝ (H t) p v) = a*jetContact p v)
    (q : ℝ × Jet3) (hq : q.2 ∈ normalStrip e) (v : Jet3) :
    fderiv ℝ (movingSphereHamiltonian e H) (q.1,sphereFamilyMap H q)
      (0,fderiv ℝ (sphereFamilyMap H) q (0,v)) =
      fderiv ℝ (sphereFamilyHamiltonianOnCover H) q (0,v) := by
  let W : ℝ × Jet3 → ℝ × Phase := fun z => (z.1,sphereFamilyMap H z)
  have hA := sphereFamilyMap_contDiff H hH
  have hW : ContDiff ℝ ∞ W := contDiff_fst.prodMk hA
  have hD := movingSphereTube_isOpen e H hH hinj hper hcontact
  have hf := movingSphereHamiltonian_contDiffOn e H hH hinj hper hcontact
  have hWq : W q ∈ movingSphereTube e H := movingSphereTube_mem_image e H q hq
  have hfat : DifferentiableAt ℝ (movingSphereHamiltonian e H) (W q) :=
    ((hf (W q) hWq).contDiffAt (hD.mem_nhds hWq)).differentiableAt (by simp)
  have heq : (movingSphereHamiltonian e H ∘ W) =ᶠ[𝓝 q] sphereFamilyHamiltonianOnCover H := by
    have hn : ∀ᶠ z : ℝ × Jet3 in 𝓝 q, z.2 ∈ normalStrip e :=
      continuous_snd.continuousAt.preimage_mem_nhds ((normalStrip_isOpen e).mem_nhds hq)
    filter_upwards [hn] with z hz
    exact movingSphereHamiltonian_eq e H hH hinj hper (W z) z.2 hz
      (normalize_sphere_point _ (legendrianSphereChart_mem _)).symm
  have hdEq : fderiv ℝ (movingSphereHamiltonian e H ∘ W) q =
      fderiv ℝ (sphereFamilyHamiltonianOnCover H) q := heq.fderiv_eq
  rw [fderiv_comp q hfat (hW.differentiable (by simp) q)] at hdEq
  have hv := congrArg (fun L : (ℝ × Jet3) →L[ℝ] ℝ => L (0,v)) hdEq
  have hdW := (hasFDerivAt_fst (𝕜 := ℝ) (p := q)).prodMk (hA.differentiable (by simp) q).hasFDerivAt
  change HasFDerivAt W _ q at hdW
  rw [hdW.fderiv] at hv
  exact hv

lemma movingSphereHamiltonian_generator_pairing (e : ℝ) (H : ℝ → Jet3 → Jet3)
    (hH : ContDiff ℝ ∞ (fun q : ℝ × Jet3 => H q.1 q.2))
    (hinj : ∀ t, InjOn (H t) (normalStrip e))
    (hper : ∀ t p, H t (p+corePoint 1) = H t p+corePoint 1)
    (hcontact : ∀ t p, p ∈ normalStrip e → ∃ a : ℝ, 0 < a ∧ ∀ v,
      jetContact (H t p) (fderiv ℝ (H t) p v) = a*jetContact p v)
    (q : ℝ × Jet3) (hq : q.2 ∈ normalStrip e) (v : Jet3) :
    fderiv ℝ (movingSphereHamiltonian e H) (q.1,sphereFamilyMap H q)
      (0,fderiv ℝ (sphereFamilyMap H) q (0,v)) =
      -2*phaseRadialContact (sphereFamilyTimeVelocity H q) (fderiv ℝ (sphereFamilyMap H) q (0,v))+
      (fderiv ℝ (sphereFamilyContactFactor H) q (1,0)/sphereFamilyContactFactor H q)*
        phaseRadialContact (sphereFamilyMap H q) (fderiv ℝ (sphereFamilyMap H) q (0,v)) := by
  have hfac := sphereFamilyContactFactor_positive e H hH hcontact q hq
  have hCartan := contact_family_hamiltonian_identity (sphereFamilyMap H) (sphereFamilyMap_contDiff H hH)
    (normalStrip e) (normalStrip_isOpen e) (sphereFamilyContactFactor H)
    (sphereFamilyContactFactor_contDiff H hH)
    (fun z hz => (sphereFamilyContactFactor_positive e H hH hcontact z hz).2) q hq v
  rw [familyContactHamiltonian_sphereFamilyMap] at hCartan
  rw [movingSphereHamiltonian_spatial_pullback e H hH hinj hper hcontact q hq v,hfac.2 v]
  change fderiv ℝ (sphereFamilyHamiltonianOnCover H) q (0,v) =
    -2*phaseRadialContact (fderiv ℝ (sphereFamilyMap H) q (1,0)) (fderiv ℝ (sphereFamilyMap H) q (0,v))+
      (fderiv ℝ (sphereFamilyContactFactor H) q (1,0)/sphereFamilyContactFactor H q)*
        (sphereFamilyContactFactor H q*jetContact q.2 v)
  field_simp [hfac.1.ne']
  nlinarith [hCartan]

end
end ContactTopology

namespace BirkhoffGlobalSection.HopfTransport
open BirkhoffGlobalSection Set
open scoped ContDiff
noncomputable section
lemma sphere_line_norm_positive (y v : Phase) (hy : y ∈ unitThreeSphere)
    (hv : phaseDot y v = 0) (s : ℝ) :
    0 < zNormSq (y+s•v) + wNormSq (y+s•v) := by
  have hy' := sphere_dot_self hy
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
    convert! dot_self_hasDerivAt hc using 1
    · ext s
      simp [zNormSq,wNormSq,phaseDot,pow_two,add_assoc]
    · simp [hv]
  have hQ : zNormSq y + wNormSq y = 1 := hy
  have hs := hq.sqrt (by simp [hQ])
  have hi := hs.inv (by simp [hQ])
  have hd := hi.smul hc
  convert! hd using 1 <;> simp [radialNormalize,hQ]


end
end BirkhoffGlobalSection.HopfTransport

namespace ContactTopology
open BirkhoffGlobalSection BirkhoffGlobalSection.HopfTransport Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma sphereFamilyMap_tangent_surjective (e : ℝ) (H : ℝ → Jet3 → Jet3)
    (hH : ContDiff ℝ ∞ (fun q : ℝ × Jet3 => H q.1 q.2))
    (hcontact : ∀ t p, p ∈ normalStrip e → ∃ a : ℝ, 0 < a ∧ ∀ v,
      jetContact (H t p) (fderiv ℝ (H t) p v) = a*jetContact p v)
    (t : ℝ) (p : Jet3) (hp : p ∈ normalStrip e) (v : Phase)
    (hv : phaseDot (sphereFamilyMap H (t,p)) v = 0) :
    ∃ w : Jet3, fderiv ℝ (sphereFamilyMap H) (t,p) (0,w) = v := by
  let y := sphereFamilyMap H (t,p)
  have hy : y ∈ unitThreeSphere := legendrianSphereChart_mem _
  obtain ⟨r,Q,hQ,hQp,hr,hrp,hleft,hright⟩ := legendrian_family_sphere_open_inverse H hH
    (normalStrip e) (normalStrip_isOpen e) hcontact t p hp
  have hrAt : ContDiffAt ℝ ∞ r (t,y) := (hr (t,y) hQp).contDiffAt (hQ.mem_nhds hQp)
  let c : ℝ → Phase := fun s => radialNormalize (y+s • v)
  have hc : HasDerivAt c v 0 := sphere_curve_hasDerivAt y v hy hv
  have hc0 : c 0 = y := by simp [c,normalize_sphere_point y hy]
  have hcsphere : ∀ s, c s ∈ unitThreeSphere := fun s =>
    (radial_normalization_contact_identity _ (sphere_line_norm_positive y v hy hv s)).2.1
  have hpair : HasDerivAt (fun s => (t,c s)) (0,v) 0 := (hasDerivAt_const (0:ℝ) t).prodMk hc
  have hrAt' : DifferentiableAt ℝ r (t,c 0) := by rw [hc0]; exact hrAt.differentiableAt (by simp)
  have hdR := hrAt'.hasFDerivAt.comp_hasDerivAt 0 hpair
  have hdR' : HasDerivAt (fun s => r (t,c s)) (fderiv ℝ r (t,y) (0,v)) 0 := by
    convert! hdR using 1 <;> simp only [Function.comp_apply,hc0]
  have hs : HasDerivAt (fun s => (t,r (t,c s))) (0,fderiv ℝ r (t,y) (0,v)) 0 :=
    (hasDerivAt_const (0:ℝ) t).prodMk hdR'
  have hr0 : r (t,c 0) = p := by rw [hc0]; exact hrp
  have hA : DifferentiableAt ℝ (sphereFamilyMap H) (t,r (t,c 0)) := by
    rw [hr0]
    exact (sphereFamilyMap_contDiff H hH).differentiable (by simp) (t,p)
  have hdA := hA.hasFDerivAt.comp_hasDerivAt 0 hs
  have hn : ∀ᶠ s in 𝓝 (0:ℝ), (t,c s) ∈ Q := by
    apply hpair.continuousAt.preimage_mem_nhds
    rw [hc0]
    exact hQ.mem_nhds hQp
  have heq : (fun s => sphereFamilyMap H (t,r (t,c s))) =ᶠ[𝓝 (0:ℝ)] c := by
    filter_upwards [hn] with s hs
    exact (hright (t,c s) hs).1 (hcsphere s)
  have hdA' : HasDerivAt c (fderiv ℝ (sphereFamilyMap H) (t,p) (0,fderiv ℝ r (t,y) (0,v))) 0 := by
    have hh := hdA.congr_of_eventuallyEq heq.symm
    simpa only [hr0] using hh
  exact ⟨fderiv ℝ r (t,y) (0,v),hdA'.unique hc⟩

end
end ContactTopology

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

namespace ContactTopology
open BirkhoffGlobalSection BirkhoffGlobalSection.HopfTransport BirkhoffGlobalSection.ContactGenerator Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma phaseDot_annihilator_radial (y z : Phase) (hy : phaseDot y y = 1)
    (hann : ∀ w : Phase, phaseDot y w = 0 → phaseDot z w = 0) :
    z = phaseDot z y • y := by
  ext i
  let w : Phase := Pi.single i 1-y i • y
  have hyw : phaseDot y w = 0 := by
    have he : phaseDot y w = y i-y i*phaseDot y y := by
      dsimp [w,phaseDot]
      fin_cases i <;> simp <;> ring
    rw [he,hy]
    ring
  have he : phaseDot z w = z i-y i*phaseDot z y := by
    dsimp [w,phaseDot]
    fin_cases i <;> simp <;> ring
  have hh := hann w hyw
  rw [he] at hh
  change z i = phaseDot z y*y i
  nlinarith [hh]

lemma contactField_gradient_radial (h b : ℝ) (g y : Phase) (hy : phaseDot y y = 1) :
    contactField h (g+b • y) y = contactField h g y := by
  have hJ : J (g+b • y) = J g+b • J y := by ext i; fin_cases i <;> simp [J] <;> ring
  have hdot : phaseDot y (g+b • y) = phaseDot y g+b*phaseDot y y := by
    simp [phaseDot]
    ring
  have hJdot : phaseDot (J y) (g+b • y) = phaseDot (J y) g := by
    simp [phaseDot,J]
    ring
  simp only [contactField,hJ,hdot,hy,hJdot]
  ext i
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  ring

lemma contactField_from_tangent_pairings (y V g : Phase) (m : ℝ)
    (hy : phaseDot y y = 1) (hV : phaseDot y V = 0)
    (hpair : ∀ w : Phase, phaseDot y w = 0 →
      phaseDot g w = -2*phaseRadialContact V w+m*phaseRadialContact y w) :
    contactField (phaseRadialContact y V) g y = V := by
  let g₀ := -J V+(m/2) • J y
  have hann : ∀ w : Phase, phaseDot y w = 0 → phaseDot (g-g₀) w = 0 := by
    intro w hw
    have hp := hpair w hw
    have hpres := prescribed_gradient_pairing y V w m
    change phaseDot g₀ w = _ at hpres
    have he : phaseDot (g-g₀) w = phaseDot g w-phaseDot g₀ w := by simp [phaseDot]; ring
    rw [he,hp,hpres]
    ring
  have hrad := phaseDot_annihilator_radial y (g-g₀) hy hann
  have hg : g = g₀+phaseDot (g-g₀) y • y := by
    rw [← hrad]
    abel
  rw [hg,contactField_gradient_radial _ _ _ _ hy]
  exact contactField_prescribed y V m hy hV

lemma compact_hamiltonian_reproduces_family_velocity (e : ℝ) (H : ℝ → Jet3 → Jet3)
    (hH : ContDiff ℝ ∞ (fun q : ℝ × Jet3 => H q.1 q.2))
    (hinj : ∀ t, InjOn (H t) (normalStrip e))
    (hper : ∀ t p, H t (p+corePoint 1) = H t p+corePoint 1)
    (hcontact : ∀ t p, p ∈ normalStrip e → ∃ a : ℝ, 0 < a ∧ ∀ v,
      jetContact (H t p) (fderiv ℝ (H t) p v) = a*jetContact p v)
    (G : ℝ × Phase → ℝ) (q : ℝ × Jet3) (hq : q.2 ∈ normalStrip e)
    (hval : G (q.1,sphereFamilyMap H q) = sphereFamilyHamiltonianOnCover H q)
    (hjet : fderiv ℝ G (q.1,sphereFamilyMap H q) =
      fderiv ℝ (movingSphereHamiltonian e H) (q.1,sphereFamilyMap H q)) :
    contactField (G (q.1,sphereFamilyMap H q)) (spatialGradient G (q.1,sphereFamilyMap H q))
      (sphereFamilyMap H q) = sphereFamilyTimeVelocity H q := by
  rw [hval]
  apply contactField_from_tangent_pairings (sphereFamilyMap H q) (sphereFamilyTimeVelocity H q)
    (spatialGradient G (q.1,sphereFamilyMap H q))
    (fderiv ℝ (sphereFamilyContactFactor H) q (1,0)/sphereFamilyContactFactor H q)
  · exact sphere_dot_self (legendrianSphereChart_mem _)
  · exact sphereFamilyTimeVelocity_tangent H hH q.1 q.2
  · intro w hw
    obtain ⟨v,hv⟩ := sphereFamilyMap_tangent_surjective e H hH hcontact q.1 q.2 hq w hw
    change phaseDot (fun i => fderiv ℝ G (q.1,sphereFamilyMap H q) (0,Pi.single i 1)) w = _
    rw [← clm_spatial_coordinates,hjet,← hv]
    exact movingSphereHamiltonian_generator_pairing e H hH hinj hper hcontact q hq v

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

namespace ContactTopology
open BirkhoffGlobalSection BirkhoffGlobalSection.HopfTransport BirkhoffGlobalSection.ContactGenerator Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma half_period_implies_period (H : ℝ → Jet3 → Jet3)
    (hhalf : ∀ t p, H t (p+corePoint (1/2)) = H t p+corePoint (1/2)) :
    ∀ t p, H t (p+corePoint 1) = H t p+corePoint 1 := by
  have ha : corePoint (1/2)+corePoint (1/2) = corePoint 1 := by
    ext i
    fin_cases i <;> norm_num [corePoint]
  intro t p
  have he : (p+corePoint (1/2))+corePoint (1/2) = p+corePoint 1 := by rw [add_assoc,ha]
  rw [← he,hhalf,hhalf,add_assoc,ha]

/-- An actual compact contact generator for the local family, on a uniform
smaller strip. Every infinitesimal contact and equivariance requirement is
proved, including exact equality to the local moving velocity. -/
lemma legendrian_family_ambient_contact_generator (e : ℝ) (he : 0 < e) (H : ℝ → Jet3 → Jet3)
    (hH : ContDiff ℝ ∞ (fun q : ℝ × Jet3 => H q.1 q.2))
    (hinj : ∀ t, InjOn (H t) (normalStrip e))
    (hhalf : ∀ t p, H t (p+corePoint (1/2)) = H t p+corePoint (1/2))
    (hcontact : ∀ t p, p ∈ normalStrip e → ∃ a : ℝ, 0 < a ∧ ∀ v,
      jetContact (H t p) (fderiv ℝ (H t) p v) = a*jetContact p v) :
    ∃ d : ℝ, 0 < d ∧ d < e ∧ ∃ X : ℝ → Phase → Phase, ∃ mu : ℝ → Phase → ℝ,
      ContDiff ℝ ∞ (fun q : ℝ × Phase => X q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × Phase => mu q.1 q.2) ∧
      (∃ C : Set Phase, IsCompact C ∧ ∀ t y, y ∉ C → X t y = 0) ∧
      (∀ t y, X t (-y) = -X t y) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ y ∈ unitThreeSphere, phaseDot y (X t y) = 0) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ y ∈ unitThreeSphere, ∀ v : Phase, phaseDot y v = 0 →
        phaseRadialContact (X t y) v+phaseRadialContact y (fderiv ℝ (X t) y v) =
          mu t y*phaseRadialContact y v) ∧
      ∀ t ∈ Icc (0:ℝ) 1, ∀ p : Jet3, |p 1| ≤ d → |p 2| ≤ d →
        X t (sphereFamilyMap H (t,p)) = sphereFamilyTimeVelocity H (t,p) := by
  have hper := half_period_implies_period H hhalf
  obtain ⟨d,hd,hde,G,hG,hGc,hGeven,hjet⟩ := compact_tube_hamiltonian_extension e he H hH hinj hper hhalf hcontact
  let X : ℝ → Phase → Phase := fun t y => contactField (G (t,y)) (spatialGradient G (t,y)) y
  let mu : ℝ → Phase → ℝ := fun t y => 2*phaseDot (J y) (spatialGradient G (t,y))
  have hX : ContDiff ℝ ∞ (fun q : ℝ × Phase => X q.1 q.2) := hamiltonian_field_contDiff hG
  have hmu : ContDiff ℝ ∞ (fun q : ℝ × Phase => mu q.1 q.2) := hamiltonian_factor_contDiff hG
  have hXsupport : ∃ C : Set Phase, IsCompact C ∧ ∀ t y, y ∉ C → X t y = 0 := hamiltonian_field_compact_support hGc
  have htan : ∀ t ∈ Icc (0:ℝ) 1, ∀ y ∈ unitThreeSphere, phaseDot y (X t y) = 0 := by
    intro t ht y hy
    exact contactField_tangent _ _ _ (sphere_dot_self hy)
  have hlie : ∀ t ∈ Icc (0:ℝ) 1, ∀ y ∈ unitThreeSphere, ∀ v : Phase, phaseDot y v = 0 →
      phaseRadialContact (X t y) v+phaseRadialContact y (fderiv ℝ (X t) y v) = mu t y*phaseRadialContact y v := by
    intro t ht y hy v hv
    exact hamiltonian_field_lie hG t y v (sphere_dot_self hy) hv
  have hpres : ∀ t ∈ Icc (0:ℝ) 1, ∀ p : Jet3, |p 1| ≤ d → |p 2| ≤ d →
      X t (sphereFamilyMap H (t,p)) = sphereFamilyTimeVelocity H (t,p) := by
    intro t ht p hp₁ hp₂
    have hj := hjet t ht p hp₁ hp₂
    exact compact_hamiltonian_reproduces_family_velocity e H hH hinj hper hcontact G (t,p)
      ⟨lt_of_le_of_lt hp₁ hde,lt_of_le_of_lt hp₂ hde⟩ hj.1 hj.2
  have hmuAvg : ContDiff ℝ ∞ (fun q : ℝ × Phase => (mu q.1 q.2+mu q.1 (-q.2))/2) :=
    (hmu.add (hmu.comp (contDiff_fst.prodMk contDiff_snd.neg))).div_const 2
  refine ⟨d,hd,hde,oddAverage X,(fun t y => (mu t y+mu t (-y))/2),
    oddAverage_contDiff hX,hmuAvg,oddAverage_compact_support hXsupport,oddAverage_odd X,
    oddAverage_tangent htan,oddAverage_lie hX hlie,?_⟩
  intro t ht p hp₁ hp₂
  have hp₁' : |(p+corePoint (1/2)) 1| ≤ d := by change |p 1+0| ≤ d; simpa using hp₁
  have hp₂' : |(p+corePoint (1/2)) 2| ≤ d := by change |p 2+0| ≤ d; simpa using hp₂
  have hn := hpres t ht (p+corePoint (1/2)) hp₁' hp₂'
  have hanti : sphereFamilyMap H (t,p+corePoint (1/2)) = -sphereFamilyMap H (t,p) := by
    change legendrianSphereChart (H t (p+corePoint (1/2))) = _
    rw [hhalf,legendrianSphereChart_antipodal]
    rfl
  rw [hanti,sphereFamilyTimeVelocity_half_shift H hH hhalf] at hn
  have hp := hpres t ht p hp₁ hp₂
  simp only [oddAverage,hp,hn,sub_neg_eq_add]
  ext i
  simp
  ring

end
end ContactTopology

open scoped ContDiff
theorem solution (e : ℝ) (he : 0 < e) (H : ℝ → (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (hH : ContDiff ℝ ∞ (fun q : ℝ × (Fin 3 → ℝ) => H q.1 q.2))
    (hinj : ∀ t, Set.InjOn (H t) {p | |p 1| < e ∧ |p 2| < e})
    (hhalf : ∀ t p, H t (p+![1/2,0,0]) = H t p+![1/2,0,0])
    (hcontact : ∀ t p, |p 1| < e ∧ |p 2| < e → ∃ a : ℝ, 0 < a ∧ ∀ v : Fin 3 → ℝ,
      (fderiv ℝ (H t) p v) 2-(H t p) 1*(fderiv ℝ (H t) p v) 0 = a*(v 2-p 1*v 0)) :
    let chart : (Fin 3 → ℝ) → BirkhoffGlobalSection.Phase := fun p =>
      BirkhoffGlobalSection.radialNormalize
        ![Real.cos (2*Real.pi*p 0),Real.sin (2*Real.pi*p 0),
          (-2*p 2)*Real.cos (2*Real.pi*p 0)+(p 1/(2*Real.pi))*Real.sin (2*Real.pi*p 0),
          (-2*p 2)*Real.sin (2*Real.pi*p 0)-(p 1/(2*Real.pi))*Real.cos (2*Real.pi*p 0)]
    ∃ d : ℝ, 0 < d ∧ d < e ∧
    ∃ X : ℝ → BirkhoffGlobalSection.Phase → BirkhoffGlobalSection.Phase,
    ∃ mu : ℝ → BirkhoffGlobalSection.Phase → ℝ,
      ContDiff ℝ ∞ (fun q : ℝ × BirkhoffGlobalSection.Phase => X q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × BirkhoffGlobalSection.Phase => mu q.1 q.2) ∧
      (∃ C : Set BirkhoffGlobalSection.Phase, IsCompact C ∧ ∀ t y, y ∉ C → X t y = 0) ∧
      (∀ t y, X t (-y) = -X t y) ∧
      (∀ t ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ BirkhoffGlobalSection.unitThreeSphere,
        BirkhoffGlobalSection.phaseDot y (X t y) = 0) ∧
      (∀ t ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ BirkhoffGlobalSection.unitThreeSphere,
        ∀ v : BirkhoffGlobalSection.Phase, BirkhoffGlobalSection.phaseDot y v = 0 →
          BirkhoffGlobalSection.phaseRadialContact (X t y) v+
            BirkhoffGlobalSection.phaseRadialContact y (fderiv ℝ (X t) y v) =
            mu t y*BirkhoffGlobalSection.phaseRadialContact y v) ∧
      ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ p : Fin 3 → ℝ, |p 1| ≤ d → |p 2| ≤ d →
        X t (chart (H t p)) = fderiv ℝ (fun q : ℝ × (Fin 3 → ℝ) => chart (H q.1 q.2)) (t,p) (1,0) := by
  exact ContactTopology.legendrian_family_ambient_contact_generator e he H hH hinj hhalf hcontact
