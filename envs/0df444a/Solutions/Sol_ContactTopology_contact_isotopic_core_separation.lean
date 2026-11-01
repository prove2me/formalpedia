-- Prove2me | solution 1 for ContactTopology.contact_isotopic_core_separation
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-31T06:02:35.61168+00:00
-- url     : https://prove2.me/submissions/8b863dcd-141d-4db3-a5bc-125a08c956fb

import Definitions.Def_BirkhoffGlobalSection_SphereContact
import Definitions.Def_ContactTopology_CoreSeparation
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Separation.Regular


namespace ContactTopology.CoreSeparation
open BirkhoffGlobalSection Set Function Filter MeasureTheory
open scoped ContDiff Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false

def qDotP (y : Phase) : ℝ := y 0*y 2+y 1*y 3
def height (y : Phase) : ℝ := -qDotP y*(2*zNormSq y)⁻¹
def parallelCore (s : ℝ) (u : Plane) : Phase :=
  scale s • ![u 0,u 1,-2*s*u 0,-2*s*u 1]
def parallelCoreSet (s : ℝ) : Set Phase := parallelCore s '' unitCircle

lemma scale_positive (s : ℝ) : 0 < scale s := by unfold scale; positivity
lemma scale_identity (s : ℝ) : scale s^2*(1+4*s^2)=1 := by
  have hp : 0 < 1+4*s^2 := by positivity
  have hs := Real.sq_sqrt hp.le
  unfold scale
  rw [inv_pow,hs]
  exact inv_mul_cancel₀ hp.ne'
lemma scale_smooth : ContDiff ℝ ∞ scale := by
  have hq : ContDiff ℝ ∞ (fun s : ℝ => 1+4*s^2) := by fun_prop
  exact (hq.sqrt (fun s => by positivity)).inv (fun s => (Real.sqrt_pos.mpr (by positivity : 0 < 1+4*s^2)).ne')
lemma parallelCore_smooth : ContDiff ℝ ∞ (fun p : ℝ × Plane => parallelCore p.1 p.2) := by
  apply (scale_smooth.comp contDiff_fst).smul
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp <;> fun_prop
lemma parallelCore_sphere (s : ℝ) (u : Plane) (hu : u ∈ unitCircle) : parallelCore s u ∈ unitThreeSphere := by
  have hnorm : u 0^2+u 1^2=1 := hu
  have he : zNormSq (parallelCore s u)+wNormSq (parallelCore s u)=
      scale s^2*(1+4*s^2)*(u 0^2+u 1^2) := by
    dsimp [parallelCore,zNormSq,wNormSq]
    ring
  change zNormSq (parallelCore s u)+wNormSq (parallelCore s u)=1
  rw [he,scale_identity,hnorm]
  norm_num
lemma parallelCore_qnorm (s : ℝ) (u : Plane) (hu : u ∈ unitCircle) :
    zNormSq (parallelCore s u)=scale s^2 := by
  have hnorm : u 0^2+u 1^2=1 := hu
  have he : zNormSq (parallelCore s u)=scale s^2*(u 0^2+u 1^2) := by
    dsimp [parallelCore,zNormSq]
    ring
  rw [he,hnorm,mul_one]
lemma parallelCore_height (s : ℝ) (u : Plane) (hu : u ∈ unitCircle) : height (parallelCore s u)=s := by
  have hq := parallelCore_qnorm s u hu
  have hp : qDotP (parallelCore s u)= -2*s*zNormSq (parallelCore s u) := by
    dsimp [qDotP,parallelCore,zNormSq]
    ring
  unfold height
  rw [hp]
  field_simp [(show zNormSq (parallelCore s u)≠0 by rw [hq]; exact (sq_pos_of_pos (scale_positive s)).ne')]

lemma height_smooth (y : Phase) (hy : zNormSq y≠0) : ContDiffAt ℝ ∞ height y := by
  unfold height qDotP zNormSq
  fun_prop (disch := aesop)

lemma height_derivative (y v : Phase) (hy : zNormSq y≠0) : fderiv ℝ height y v=
    (qDotP y*(2*y 0*v 0+2*y 1*v 1)-zNormSq y*(v 0*y 2+y 0*v 2+v 1*y 3+y 1*v 3))/(2*zNormSq y^2) := by
  let e (i : Fin 4) : Phase →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have h (i : Fin 4) : HasFDerivAt (fun y : Phase => y i) (e i) y := (e i).hasFDerivAt
  have hQ := ((h 0).pow 2).add ((h 1).pow 2)
  have hC := ((h 0).mul (h 2)).add ((h 1).mul (h 3))
  have hden : 2*zNormSq y≠0 := mul_ne_zero (by norm_num) hy
  have hI := (hasFDerivAt_inv hden).comp y (hQ.const_mul 2)
  have hd := hC.neg.mul hI
  change HasFDerivAt (𝕜 := ℝ) height _ y at hd
  rw [hd.fderiv]
  simp [e,qDotP,zNormSq]
  field_simp [hy]
  ring

/-- On a parallel core, its height differential is the contact form divided by
the positive first-plane norm. This identity uses actual ambient derivatives. -/
lemma height_contact_identity (y v : Phase) (s : ℝ) (hy : zNormSq y≠0)
    (hp0 : y 2= -2*s*y 0) (hp1 : y 3= -2*s*y 1) :
    zNormSq y*fderiv ℝ height y v=phaseRadialContact y v := by
  rw [height_derivative y v hy]
  change y 0^2+y 1^2≠0 at hy
  unfold qDotP zNormSq phaseRadialContact phaseSymplecticForm
  rw [hp0,hp1]
  field_simp [hy]
  ring

/-- Reuses the critical-value nullity argument of the accepted meridian
comparison proof; generalized to a countable family before choosing one height. -/
lemma critical_values_null (f : ℝ → ℝ) (I : Set ℝ) (hI : IsOpen I) (hf : DifferentiableOn ℝ f I) :
    volume (f '' {t | t ∈ I ∧ deriv f t=0})=0 := by
  let C : Set ℝ := {t | t ∈ I ∧ deriv f t=0}
  have hD : ∀ t ∈ C, HasFDerivWithinAt f (0 : ℝ →L[ℝ] ℝ) C t := by
    intro t ht
    have hd := ((hf t ht.1).differentiableAt (hI.mem_nhds ht.1)).hasDerivAt
    rw [ht.2] at hd
    simpa using hd.hasFDerivAt.hasFDerivWithinAt
  exact MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume hD (by intro t ht; simp)

lemma exists_common_regular_height {ι : Type*} [Countable ι]
    (f : ι → ℝ → ℝ) (I : ι → Set ℝ) (hI : ∀ i, IsOpen (I i))
    (hf : ∀ i, DifferentiableOn ℝ (f i) (I i)) (ε : ℝ) (hε : 0 < ε) :
    ∃ s : ℝ, |s|<ε ∧ ∀ i t, t ∈ I i → f i t=s → deriv (f i) t≠0 := by
  let C (i : ι) : Set ℝ := f i '' {t | t ∈ I i ∧ deriv (f i) t=0}
  have hnull : volume (⋃ i, C i)=0 := measure_iUnion_null (fun i => critical_values_null (f i) (I i) (hI i) (hf i))
  have hex : ∃ s ∈ Ioo (-ε) ε, s ∉ ⋃ i, C i := by
    by_contra hn
    push Not at hn
    have hle : volume (Ioo (-ε) ε)≤0 := by
      rw [← hnull]
      exact measure_mono (fun s hs => hn s hs)
    have hp : 0 < volume (Ioo (-ε) ε) := by rw [Real.volume_Ioo]; exact ENNReal.ofReal_pos.mpr (by linarith)
    exact (not_le_of_gt hp) hle
  obtain ⟨s,hs,hn⟩ := hex
  refine ⟨s,abs_lt.mpr hs,?_⟩
  intro i t ht he hz
  exact hn (mem_iUnion.mpr ⟨i,⟨t,⟨ht,hz⟩,he⟩⟩)

theorem exists_parallel_core_disjoint_countable_legendrian_curves {ι : Type*} [Countable ι]
    (γ : ι → ℝ → Phase) (hγ : ∀ i, ContDiff ℝ ∞ (γ i))
    (hL : ∀ i t, phaseRadialContact (γ i t) (deriv (γ i) t)=0)
    (ε : ℝ) (hε : 0 < ε) : ∃ s : ℝ, |s|<ε ∧
      ∀ i, Disjoint (range (γ i)) (parallelCoreSet s) := by
  let I (i : ι) : Set ℝ := {t | zNormSq (γ i t)≠0}
  let f (i : ι) : ℝ → ℝ := height ∘ γ i
  have hI (i : ι) : IsOpen (I i) := by
    have hQ : Continuous (fun t => zNormSq (γ i t)) := by
      have hc := (hγ i).continuous
      unfold zNormSq
      fun_prop
    exact isOpen_ne_fun hQ continuous_const
  have hf (i : ι) : DifferentiableOn ℝ (f i) (I i) := by
    intro t ht
    exact (((height_smooth _ ht).comp t (hγ i).contDiffAt).differentiableAt (by simp)).differentiableWithinAt
  obtain ⟨s,hs,hreg⟩ := exists_common_regular_height f I hI hf ε hε
  refine ⟨s,hs,?_⟩
  intro i
  apply Set.disjoint_left.mpr
  rintro y ⟨t,rfl⟩ ⟨u,hu,he⟩
  have hq : zNormSq (γ i t)≠0 := by
    rw [← he,parallelCore_qnorm s u hu]
    exact (sq_pos_of_pos (scale_positive s)).ne'
  have ht : t ∈ I i := hq
  have hvalue : f i t=s := by change height (γ i t)=s; rw [← he,parallelCore_height s u hu]
  have hcontact := height_contact_identity (γ i t) (deriv (γ i) t) s hq
    (by rw [← he]; simp [parallelCore]; ring)
    (by rw [← he]; simp [parallelCore]; ring)
  have hd : HasDerivAt (f i) (fderiv ℝ height (γ i t) (deriv (γ i) t)) t :=
    ((height_smooth _ hq).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t
      ((hγ i).differentiable (by simp) t).hasDerivAt
  apply hreg i t ht hvalue
  rw [hd.deriv]
  rw [hL] at hcontact
  exact (mul_eq_zero.mp hcontact).resolve_left hq

def rotationLinear (s : ℝ) : Phase →L[ℝ] Phase :=
  LinearMap.toContinuousLinearMap
    { toFun := rotation s
      map_add' := by intro u v; ext i; fin_cases i <;> simp [rotation] <;> ring
      map_smul' := by intro a v; ext i; fin_cases i <;> simp [rotation] <;> ring }

lemma rotation_smooth : ContDiff ℝ ∞ (fun p : ℝ × Phase => rotation p.1 p.2) := by
  apply (scale_smooth.comp contDiff_fst).smul
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp <;> fun_prop

lemma rotation_derivative (s : ℝ) (y v : Phase) :
    fderiv ℝ (rotation s) y v=rotation s v :=
  congrArg (fun L : Phase →L[ℝ] Phase => L v) (rotationLinear s).hasFDerivAt.fderiv

lemma scale_neg (s : ℝ) : scale (-s)=scale s := by simp [scale]

lemma rotation_inverse (s : ℝ) (y : Phase) : rotation (-s) (rotation s y)=y := by
  have hs := scale_identity s
  ext i
  calc
    _ = scale s^2*(1+4*s^2)*y i := by
      fin_cases i <;> simp [rotation,scale_neg] <;> ring
    _ = y i := by rw [hs,one_mul]

lemma rotation_norm (s : ℝ) (y : Phase) :
    zNormSq (rotation s y)+wNormSq (rotation s y)=zNormSq y+wNormSq y := by
  calc
    _ = scale s^2*(1+4*s^2)*(zNormSq y+wNormSq y) := by
      dsimp [rotation,zNormSq,wNormSq]
      ring
    _ = _ := by rw [scale_identity,one_mul]

lemma rotation_sphere (s : ℝ) : MapsTo (rotation s) unitThreeSphere unitThreeSphere := by
  intro y hy
  change zNormSq (rotation s y)+wNormSq (rotation s y)=1
  rw [rotation_norm]
  exact hy

lemma rotation_contact (s : ℝ) (y v : Phase) :
    phaseRadialContact (rotation s y) (rotation s v)=phaseRadialContact y v := by
  calc
    _ = scale s^2*(1+4*s^2)*phaseRadialContact y v := by
      dsimp [rotation,phaseRadialContact,phaseSymplecticForm]
      ring
    _ = _ := by rw [scale_identity,one_mul]

lemma rotation_zero (y : Phase) : rotation 0 y=y := by
  ext i
  fin_cases i <;> simp [rotation,scale]

def rotationContact (s : ℝ) : EquivariantSphereContactomorphism where
  toFun := rotation s
  invFun := rotation (-s)
  smooth := fun y _ => ((rotationLinear s).contDiff).contDiffAt
  inv_smooth := fun y _ => ((rotationLinear (-s)).contDiff).contDiffAt
  maps_sphere := rotation_sphere s
  inv_maps_sphere := rotation_sphere (-s)
  left_inv := fun y _ => rotation_inverse s y
  right_inv := by intro y _; simpa using rotation_inverse (-s) y
  antipodal := fun y _ => (rotationLinear s).map_neg y
  contact := by
    intro y _
    refine ⟨1,by norm_num,?_⟩
    intro v _
    rw [rotation_derivative,rotation_contact,one_mul]

def rotationIsotopy (s : ℝ) : EquivariantSphereContactIsotopy (rotationContact s) where
  slice := fun t => rotationContact (t*s)
  smooth := by
    intro t _ y _
    change ContDiffAt ℝ ∞ (fun p : ℝ × Phase => rotation (p.1*s) p.2) (t,y)
    exact (rotation_smooth.comp ((contDiff_fst.mul contDiff_const).prodMk contDiff_snd)).contDiffAt
  start := by intro y _; change rotation (0*s) y=y; rw [zero_mul,rotation_zero]
  finish := by intro y _; change rotation (1*s) y=rotation s y; rw [one_mul]

lemma rotation_core (s : ℝ) (u : Plane) :
    rotation s ![u 0,u 1,0,0]=parallelCore s u := by
  ext i
  fin_cases i <;> simp [rotation,parallelCore] <;> ring

def coreCurve (t : ℝ) : Phase := ![Real.cos t,Real.sin t,0,0]

lemma coreCurve_sphere (t : ℝ) : coreCurve t ∈ unitThreeSphere := by
  simpa [coreCurve,unitThreeSphere,zNormSq,wNormSq] using Real.cos_sq_add_sin_sq t

lemma coreCurve_smooth : ContDiff ℝ ∞ coreCurve := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [coreCurve] <;> fun_prop

lemma coreCurve_derivative (t : ℝ) :
    HasDerivAt coreCurve ![-Real.sin t,Real.cos t,0,0] t := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact Real.hasDerivAt_cos t
  · exact Real.hasDerivAt_sin t
  · exact hasDerivAt_const t 0
  · exact hasDerivAt_const t 0

lemma coreCurve_covers (u : Plane) (hu : u ∈ unitCircle) :
    ∃ t, coreCurve t=![u 0,u 1,0,0] := by
  have hnorm : u 0^2+u 1^2=1 := hu
  have hlo : -1 ≤ u 0 := by nlinarith [sq_nonneg (u 1),sq_nonneg (u 0+1)]
  have hhi : u 0 ≤ 1 := by nlinarith [sq_nonneg (u 1),sq_nonneg (u 0-1)]
  have hcos := Real.cos_arccos hlo hhi
  have hsin : Real.sin (Real.arccos (u 0))=|u 1| := by
    rw [Real.sin_arccos,show 1-u 0^2=u 1^2 by linarith,Real.sqrt_sq_eq_abs]
  by_cases hpos : 0 ≤ u 1
  · refine ⟨Real.arccos (u 0),?_⟩
    ext i
    fin_cases i <;> simp [coreCurve,hcos,hsin,abs_of_nonneg hpos]
  · refine ⟨-Real.arccos (u 0),?_⟩
    ext i
    fin_cases i <;> simp [coreCurve,hcos,hsin,abs_of_neg (lt_of_not_ge hpos)]

lemma imageCoreCurve_smooth (F : EquivariantSphereContactomorphism) :
    ContDiff ℝ ∞ (F.toFun ∘ coreCurve) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  exact (F.smooth _ (coreCurve_sphere t)).comp t coreCurve_smooth.contDiffAt

lemma imageCoreCurve_legendrian (F : EquivariantSphereContactomorphism) (t : ℝ) :
    phaseRadialContact ((F.toFun ∘ coreCurve) t) (deriv (F.toFun ∘ coreCurve) t)=0 := by
  have hd := ((F.smooth _ (coreCurve_sphere t)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t (coreCurve_derivative t)
  rw [hd.deriv]
  obtain ⟨a,ha,hF⟩ := F.contact _ (coreCurve_sphere t)
  change phaseRadialContact (F.toFun (coreCurve t)) _=0
  rw [hF _ (by dsimp [coreCurve,phaseDot]; ring)]
  simp [coreCurve,phaseRadialContact,phaseSymplecticForm]

theorem exists_parallel_core_disjoint_contactomorphic_core
    (F : EquivariantSphereContactomorphism) (ε : ℝ) (hε : 0 < ε) :
    ∃ s : ℝ, |s|<ε ∧ Disjoint
      ((fun u : Plane => F.toFun ![u 0,u 1,0,0]) '' unitCircle) (parallelCoreSet s) := by
  obtain ⟨s,hs,hdis⟩ := exists_parallel_core_disjoint_countable_legendrian_curves
    (fun _ : Unit => F.toFun ∘ coreCurve) (fun _ => imageCoreCurve_smooth F)
    (fun _ => imageCoreCurve_legendrian F) ε hε
  refine ⟨s,hs,(hdis ()).mono_left ?_⟩
  rintro y ⟨u,hu,rfl⟩
  obtain ⟨t,ht⟩ := coreCurve_covers u hu
  exact ⟨t,congrArg F.toFun ht⟩

lemma standardCore_sphere (u : Plane) (hu : u ∈ unitCircle) :
    standardCore u ∈ unitThreeSphere := by
  change u 0^2+u 1^2=1 at hu
  simpa [standardCore,unitThreeSphere,zNormSq,wNormSq] using hu

lemma unitCircle_compact : IsCompact unitCircle := by
  have hp : Continuous planeNormSq := by unfold planeNormSq; fun_prop
  have hc : IsClosed unitCircle := isClosed_eq hp continuous_const
  apply (isCompact_Icc : IsCompact (Icc (![-1,-1] : Plane) ![1,1])).of_isClosed_subset hc
  intro u hu
  have h : u 0^2+u 1^2=1 := hu
  constructor <;> intro i <;> fin_cases i <;> dsimp <;>
    nlinarith [sq_nonneg (u 0),sq_nonneg (u 1)]

lemma sphere_compact : IsCompact unitThreeSphere := by
  have hc : IsClosed unitThreeSphere := isClosed_eq (by unfold zNormSq wNormSq; fun_prop) continuous_const
  apply (isCompact_Icc : IsCompact (Icc (![-1,-1,-1,-1] : Phase) ![1,1,1,1])).of_isClosed_subset hc
  intro y hy
  have h : y 0^2+y 1^2+(y 2^2+y 3^2)=1 := hy
  constructor <;> intro i <;> fin_cases i <;> dsimp <;>
    nlinarith [sq_nonneg (y 0),sq_nonneg (y 1),sq_nonneg (y 2),sq_nonneg (y 3)]

lemma coreSet_compact (F : EquivariantSphereContactomorphism) : IsCompact (coreSet F) := by
  have hc : ContDiff ℝ ∞ standardCore := by
    apply contDiff_pi.mpr; intro i; fin_cases i <;> dsimp [standardCore] <;> fun_prop
  apply unitCircle_compact.image_of_continuousOn
  intro u hu
  exact ((F.smooth _ (standardCore_sphere u hu)).comp u hc.contDiffAt).continuousAt.continuousWithinAt

lemma sphere_wnorm_zero_is_core (y : Phase) (hy : y ∈ unitThreeSphere) (hw : wNormSq y=0) :
    ∃ u ∈ unitCircle, standardCore u=y := by
  have h2 : y 2=0 := by unfold wNormSq at hw; nlinarith [sq_nonneg (y 3)]
  have h3 : y 3=0 := by unfold wNormSq at hw; nlinarith [sq_nonneg (y 2)]
  refine ⟨![y 0,y 1],?_,?_⟩
  · change y 0^2+y 1^2=1
    change zNormSq y+wNormSq y=1 at hy
    simpa [hw,zNormSq] using hy
  · ext i; fin_cases i <;> simp [standardCore,h2,h3]

lemma small_tube_in_open (F : EquivariantSphereContactomorphism)
    (O : Set Phase) (hO : IsOpen O) (hcore : coreSet F ⊆ O) :
    ∃ r : ℝ, 0 < r ∧ F.toFun '' standardTube r ⊆ O := by
  let K : Set Phase := unitThreeSphere ∩ F.toFun ⁻¹' Oᶜ
  have hF : ContinuousOn F.toFun unitThreeSphere := fun y hy =>
    (F.smooth y hy).continuousAt.continuousWithinAt
  have hK : IsCompact K := sphere_compact.of_isClosed_subset
    (hF.preimage_isClosed_of_isClosed sphere_compact.isClosed hO.isClosed_compl) inter_subset_left
  have hw : Continuous (wNormSq : Phase → ℝ) := by unfold wNormSq; fun_prop
  have hpos : ∀ y ∈ K, 0 < wNormSq y := by
    intro y hy
    have hn : 0 ≤ wNormSq y := by unfold wNormSq; positivity
    refine lt_of_le_of_ne hn ?_
    intro he
    obtain ⟨u,hu,huy⟩ := sphere_wnorm_zero_is_core y hy.1 he.symm
    exact hy.2 (hcore ⟨u,hu,congrArg F.toFun huy⟩)
  obtain ⟨δ,hδ,hmin⟩ := hK.exists_forall_le' hw.continuousOn hpos
  refine ⟨Real.sqrt (δ/2),by positivity,?_⟩
  rintro z ⟨y,hy,rfl⟩
  by_contra hn
  have hδy := hmin y ⟨hy.1,hn⟩
  have hQ : zNormSq y ≤ 1 := by
    have hs : zNormSq y+wNormSq y=1 := hy.1
    have hw0 : 0 ≤ wNormSq y := by unfold wNormSq; positivity
    linarith
  have hsqrt : Real.sqrt (δ/2)^2=δ/2 := Real.sq_sqrt (by positivity)
  have hbound := mul_le_mul_of_nonneg_left hQ (sq_nonneg (Real.sqrt (δ/2)))
  rw [hsqrt] at hbound
  have hT := hy.2
  rw [hsqrt] at hT
  nlinarith

lemma disjoint_small_tubes (F G : EquivariantSphereContactomorphism)
    (hdis : Disjoint (coreSet F) (coreSet G)) :
    ∃ r q : ℝ, 0 < r ∧ 0 < q ∧ Disjoint
      (F.toFun '' standardTube r) (G.toFun '' standardTube q) := by
  obtain ⟨U,V,hU,hV,hFU,hGV,hUV⟩ := SeparatedNhds.of_isCompact_isClosed
    (coreSet_compact F) (coreSet_compact G).isClosed hdis
  obtain ⟨r,hr,hrU⟩ := small_tube_in_open F U hU hFU
  obtain ⟨q,hq,hqV⟩ := small_tube_in_open G V hV hGV
  exact ⟨r,q,hr,hq,hUV.mono hrU hqV⟩

theorem contact_isotopic_core_separation (F : EquivariantSphereContactomorphism)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ s : ℝ, ∃ G : EquivariantSphereContactomorphism, |s|<ε ∧
      (∀ y : Phase, G.toFun y=rotation s y) ∧
      Nonempty (EquivariantSphereContactIsotopy G) ∧
      Disjoint (coreSet F) (coreSet G) ∧
      ∃ r q : ℝ, 0 < r ∧ 0 < q ∧ Disjoint
        (F.toFun '' standardTube r) (G.toFun '' standardTube q) := by
  obtain ⟨s,hs,hdis⟩ := exists_parallel_core_disjoint_contactomorphic_core F ε hε
  have hG : coreSet (rotationContact s)=parallelCoreSet s := by
    apply image_congr
    intro u _
    exact rotation_core s u
  have hsep : Disjoint (coreSet F) (coreSet (rotationContact s)) := by
    rw [hG]
    exact hdis
  exact ⟨s,rotationContact s,hs,fun _ => rfl,⟨rotationIsotopy s⟩,hsep,disjoint_small_tubes F _ hsep⟩

end
end ContactTopology.CoreSeparation

open BirkhoffGlobalSection ContactTopology.CoreSeparation Set Function
open scoped ContDiff
theorem solution (F : EquivariantSphereContactomorphism)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ s : ℝ, ∃ G : EquivariantSphereContactomorphism, |s|<ε ∧
      (∀ y : Phase, G.toFun y=rotation s y) ∧
      Nonempty (EquivariantSphereContactIsotopy G) ∧
      Disjoint (coreSet F) (coreSet G) ∧
      ∃ r q : ℝ, 0 < r ∧ 0 < q ∧ Disjoint
        (F.toFun '' standardTube r) (G.toFun '' standardTube q) := by
  exact ContactTopology.CoreSeparation.contact_isotopic_core_separation F ε hε
