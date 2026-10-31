-- Prove2me | solution 1 for ContactTopology.projective_meridian_dividing_minimality
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-31T04:56:28.192884+00:00
-- url     : https://prove2.me/submissions/b2971eb5-8875-4b9b-b7bc-e9b901e454a3

import Definitions.Def_ContactTopology_ProjectiveMeridianLoops
import Definitions.Def_ContactTopology_ProjectiveSolidCoordinates
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Set.Card
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.ProjIcc
import Theorems.Thm_ContactTopology_projective_solid_boundary_core_dividing_coordinates


namespace ContactTopology.TorusMeridian
open Set Function Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- The existing angular-lift argument from RationalRotationDegree, specialized
only by its namespace. This uses Mathlib's actual covering lift. -/
lemma exists_continuous_angle {X : Type*} [TopologicalSpace X]
    [SimplyConnectedSpace X] [LocallyPathConnectedSpace X] [Nonempty X]
    (f : X → Circle) (hf : Continuous f) :
    ∃ θ : X → ℝ, Continuous θ ∧ ∀ x, Circle.exp (θ x)=f x := by
  let x₀ : X := Classical.choice inferInstance
  obtain ⟨a,ha⟩ := Circle.exp_surjective (f x₀)
  obtain ⟨θ,⟨hθ₀,hθ⟩,hunique⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
    ⟨f,hf⟩ x₀ a ha
  exact ⟨θ,θ.continuous,fun x => congrFun hθ x⟩

lemma exp_surjOn_full_turn (a : ℝ) : SurjOn Circle.exp (Icc a (a+2*Real.pi)) univ := by
  intro z hz
  obtain ⟨φ,hφ⟩ := Circle.exp_surjective z
  let q := (φ-a)/(2*Real.pi)
  let n : ℤ := ⌊q⌋
  have hper : 0 < 2*Real.pi := by positivity
  have hq : q*(2*Real.pi)=φ-a := by dsimp [q]; field_simp
  have hnlo : (n:ℝ) ≤ q := Int.floor_le q
  have hnhi : q < (n:ℝ)+1 := Int.lt_floor_add_one q
  refine ⟨φ-(n:ℝ)*(2*Real.pi),⟨?_,?_⟩,?_⟩
  · nlinarith [mul_le_mul_of_nonneg_right hnlo hper.le]
  · nlinarith [mul_lt_mul_of_pos_right hnhi hper]
  · rw [← hφ]
    exact Circle.exp_eq_exp.mpr ⟨-n,by push_cast; ring⟩

lemma continuous_lift_turn_constant (θ : ℝ × ℝ → ℝ) (hθ : Continuous θ)
    (hperiod : ∀ s : ℝ, Circle.exp (θ (s,2*Real.pi))=Circle.exp (θ (s,0))) :
    θ (1,2*Real.pi)-θ (1,0)=θ (0,2*Real.pi)-θ (0,0) := by
  let d : ℝ → ℝ := fun s => (θ (s,2*Real.pi)-θ (s,0))/(2*Real.pi)
  have hd : Continuous d :=
    ((hθ.comp (continuous_id.prodMk continuous_const)).sub
      (hθ.comp (continuous_id.prodMk continuous_const))).div_const _
  have hm : MapsTo d (Icc 0 1) (range ((↑) : ℤ → ℝ)) := by
    intro s hs
    obtain ⟨n,hn⟩ := Circle.exp_eq_exp.mp (hperiod s)
    refine ⟨n,?_⟩
    dsimp [d]
    rw [hn]
    field_simp [Real.pi_ne_zero]
    ring
  have he := isPreconnected_Icc.constant_of_mapsTo
    Real.isClosedEmbedding_intCast.isEmbedding.isDiscrete_range hd.continuousOn hm
    (show (1:ℝ) ∈ Icc 0 1 from ⟨by norm_num,le_rfl⟩)
    (show (0:ℝ) ∈ Icc 0 1 from ⟨le_rfl,by norm_num⟩)
  exact (div_left_inj' (show (2*Real.pi:ℝ) ≠ 0 by positivity)).mp he

lemma identity_lift_turn (θ : ℝ → ℝ) (hθ : Continuous θ)
    (hθexp : ∀ t, Circle.exp (θ t)=Circle.exp t) : θ (2*Real.pi)-θ 0=2*Real.pi := by
  let d : ℝ → ℝ := fun t => (θ t-t)/(2*Real.pi)
  have hd : Continuous d := (hθ.sub continuous_id).div_const _
  have hm : MapsTo d (Icc 0 (2*Real.pi)) (range ((↑) : ℤ → ℝ)) := by
    intro t ht
    obtain ⟨n,hn⟩ := Circle.exp_eq_exp.mp (hθexp t)
    refine ⟨n,?_⟩
    dsimp [d]
    rw [hn]
    field_simp [Real.pi_ne_zero]
    ring
  have he := isPreconnected_Icc.constant_of_mapsTo
    Real.isClosedEmbedding_intCast.isEmbedding.isDiscrete_range hd.continuousOn hm
    (show 2*Real.pi ∈ Icc 0 (2*Real.pi) from ⟨by positivity,le_rfl⟩)
    (show (0:ℝ) ∈ Icc 0 (2*Real.pi) from ⟨le_rfl,by positivity⟩)
  have hh := (div_left_inj' (show (2*Real.pi:ℝ) ≠ 0 by positivity)).mp he
  linarith

/-- A loop homotopic to one full turn has every circle value. The proof lifts
an actual homotopy, so no winding or surjectivity assumption is supplied. -/
theorem circle_surjective_of_homotopic_id (f : C(Circle,Circle))
    (hf : ContinuousMap.Homotopic (ContinuousMap.id Circle) f) : Surjective f := by
  obtain ⟨H⟩ := hf
  let L : ℝ × ℝ → Circle := fun p => H (Set.projIcc 0 1 zero_le_one p.1,Circle.exp p.2)
  have hL : Continuous L := H.continuous.comp
    ((continuous_projIcc.comp continuous_fst).prodMk (Circle.exp.continuous.comp continuous_snd))
  obtain ⟨θ,hθ,hθL⟩ := exists_continuous_angle L hL
  have hperiod (s : ℝ) : Circle.exp (θ (s,2*Real.pi))=Circle.exp (θ (s,0)) := by
    rw [hθL,hθL]
    simp only [L,Circle.exp_two_pi,Circle.exp_zero]
  have hbase (t : ℝ) : Circle.exp (θ (0,t))=Circle.exp t := by
    rw [hθL]
    simp [L]
  have hzero := identity_lift_turn (fun t => θ (0,t))
    (hθ.comp (continuous_const.prodMk continuous_id)) hbase
  have hone : θ (1,2*Real.pi)-θ (1,0)=2*Real.pi :=
    (continuous_lift_turn_constant θ hθ hperiod).trans hzero
  intro z
  obtain ⟨b,hb,heb⟩ := exp_surjOn_full_turn (θ (1,0)) (mem_univ z)
  have hθ1 : Continuous (fun t => θ (1,t)) := hθ.comp (continuous_const.prodMk continuous_id)
  obtain ⟨t,ht,he⟩ := (intermediate_value_Icc (by positivity : (0:ℝ) ≤ 2*Real.pi) hθ1.continuousOn)
    (show b ∈ Icc (θ (1,0)) (θ (1,2*Real.pi)) from ⟨hb.1,by linarith [hb.2]⟩)
  refine ⟨Circle.exp t,?_⟩
  have hlast : Circle.exp (θ (1,t))=f (Circle.exp t) := by rw [hθL]; simp [L]
  change θ (1,t)=b at he
  rw [← hlast,he,heb]

end
end ContactTopology.TorusMeridian


namespace ContactTopology.ProjectiveMeridian
open BirkhoffGlobalSection ContactTopology.SolidTorusQuotient ContactTopology.Projective Set Function Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section


lemma first_surjective_of_meridian_homotopy (γ : C(Circle,Circle × Circle))
    (hγ : ContinuousMap.Homotopic meridian γ) : Surjective (fun v => (γ v).1) := by
  obtain ⟨H⟩ := hγ
  let f : C(Circle,Circle) := ⟨fun v => (γ v).1,continuous_fst.comp γ.continuous⟩
  have hf : ContinuousMap.Homotopic (ContinuousMap.id Circle) f := by
    refine ⟨{ toFun := fun p => (H p).1
              continuous_toFun := continuous_fst.comp H.continuous
              map_zero_left := ?_, map_one_left := ?_ }⟩
    · intro v; rw [H.apply_zero]; rfl
    · intro v; rw [H.apply_one]; rfl
  exact ContactTopology.TorusMeridian.circle_surjective_of_homotopic_id f hf

/-- The product-coordinate dividing description forces at least two actual
projective intersections in every meridian representative. -/
lemma dividing_intersections_of_meridian_homotopy (j : DiskCircle → ProjectiveSphere 4)
    (hI : Injective j) (Z : Set (ProjectiveSphere 4))
    (hZ : ∀ p, ‖(p.1:ℂ)‖=1 → (j p ∈ Z ↔ (p.1:ℂ)=Complex.I ∨ (p.1:ℂ)= -Complex.I))
    (γ : C(Circle,Circle × Circle)) (hγ : ContinuousMap.Homotopic meridian γ) :
    2 ≤ (range (j ∘ boundaryCoordinates ∘ γ) ∩ Z).encard := by
  let b : Circle := Circle.exp (Real.pi/2)
  have hb : (b:ℂ)=Complex.I := by simp [b,Circle.coe_exp,Complex.exp_mul_I]
  have hbn : ((-b:Circle):ℂ)= -Complex.I := by simp [hb]
  obtain ⟨u,hu⟩ := first_surjective_of_meridian_homotopy γ hγ b
  obtain ⟨v,hv⟩ := first_surjective_of_meridian_homotopy γ hγ (-b)
  have huc : ((γ u).1:ℂ) = Complex.I :=
    (congrArg (fun z : Circle => (z:ℂ)) hu).trans hb
  have hvc : ((γ v).1:ℂ) = -Complex.I :=
    (congrArg (fun z : Circle => (z:ℂ)) hv).trans hbn
  have hune : j (boundaryCoordinates (γ u)) ≠ j (boundaryCoordinates (γ v)) := by
    intro he
    have hh := congrArg (fun p : DiskCircle => (p.1:ℂ)) (hI he)
    change ((γ u).1:ℂ)=((γ v).1:ℂ) at hh
    rw [huc,hvc] at hh
    have hi := congrArg Complex.im hh
    norm_num at hi
  have huz : j (boundaryCoordinates (γ u)) ∈ Z := by
    apply (hZ _ (Circle.norm_coe (γ u).1)).mpr
    left
    change ((γ u).1:ℂ)=Complex.I
    exact huc
  have hvz : j (boundaryCoordinates (γ v)) ∈ Z := by
    apply (hZ _ (Circle.norm_coe (γ v).1)).mpr
    right
    change ((γ v).1:ℂ)= -Complex.I
    exact hvc
  have hlt : 1 < (range (j ∘ boundaryCoordinates ∘ γ) ∩ Z).encard :=
    Set.one_lt_encard_iff.mpr ⟨j (boundaryCoordinates (γ u)),j (boundaryCoordinates (γ v)),
      ⟨⟨u,rfl⟩,huz⟩,⟨⟨v,rfl⟩,hvz⟩,hune⟩
  exact (ENat.add_one_le_iff (by simp)).mpr hlt

/-- The product meridian attains the two-point lower bound. -/
lemma meridian_dividing_intersections_eq_two (j : DiskCircle → ProjectiveSphere 4)
    (hI : Injective j) (Z : Set (ProjectiveSphere 4))
    (hZ : ∀ p, ‖(p.1:ℂ)‖=1 → (j p ∈ Z ↔ (p.1:ℂ)=Complex.I ∨ (p.1:ℂ)= -Complex.I)) (z : Circle) :
    (range (j ∘ boundaryCoordinates ∘ meridianAt z) ∩ Z).encard = 2 := by
  let b : Circle := Circle.exp (Real.pi/2)
  have hb : (b:ℂ)=Complex.I := by simp [b,Circle.coe_exp,Complex.exp_mul_I]
  have hbn : ((-b:Circle):ℂ)= -Complex.I := by simp [hb]
  have hp : j (unitDisk b,z) ≠ j (unitDisk (-b),z) := by
    intro he
    have hh := congrArg (fun p : DiskCircle => (p.1:ℂ)) (hI he)
    change (b:ℂ)=((-b:Circle):ℂ) at hh
    rw [hb,hbn] at hh
    have hi := congrArg Complex.im hh
    norm_num at hi
  have hset : range (j ∘ boundaryCoordinates ∘ meridianAt z) ∩ Z =
      {j (unitDisk b,z),j (unitDisk (-b),z)} := by
    ext y
    constructor
    · rintro ⟨⟨v,rfl⟩,hz⟩
      change j (unitDisk v,z) ∈ Z at hz
      rcases (hZ _ (Circle.norm_coe v)).mp hz with hv|hv
      · have he : v=b := Subtype.ext (hv.trans hb.symm)
        subst v
        exact Or.inl rfl
      · have he : v= -b := Subtype.ext (hv.trans hbn.symm)
        subst v
        exact Or.inr rfl
    · intro hy
      rcases hy with he|he
      · subst y
        refine ⟨⟨b,rfl⟩,(hZ _ (Circle.norm_coe b)).mpr (Or.inl hb)⟩
      · subst y
        refine ⟨⟨-b,rfl⟩,(hZ _ (Circle.norm_coe (-b))).mpr (Or.inr hbn)⟩
  rw [hset,Set.encard_pair hp]

end
end ContactTopology.ProjectiveMeridian


namespace ContactTopology.ProjectiveMeridian
open BirkhoffGlobalSection ContactTopology.SolidTorusQuotient ContactTopology.Projective
open ContactTopology.ConvexMeridian ContactTopology.TorusMeridian Set Function Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The positive-scale normalization identity reused from the accepted meridian
construction, with only its elementary norm-square calculation included. -/
lemma normalize_positive_scale (a : ℝ) (ha : 0<a) (y : Phase) :
    radialNormalize (a • y)=radialNormalize y := by
  have hQ : zNormSq (a • y)+wNormSq (a • y)=a^2*(zNormSq y+wNormSq y) := by
    simp [zNormSq,wNormSq]
    ring
  simp [radialNormalize,hQ,Real.sqrt_mul (sq_nonneg a),Real.sqrt_sq ha.le,
    mul_inv_rev,smul_smul,ha.ne']

/-- The standard boundary formula from the accepted sphere-model proof. -/
lemma solid_at_boundary (r : ℝ) (hr : 0<r) (p : Plane × Plane) (hu : p.1 ∈ unitCircle) :
    MeridianTorus.solid r p=MeridianTorus.surface r 1 p := by
  have hh : p.1 0^2+p.1 1^2=1 := hu
  have hraw : MeridianTorus.raw r 1 p=![p.1 0,p.1 1,r*p.2 0,r*p.2 1] := by
    ext i
    fin_cases i
    · rfl
    · rfl
    · dsimp [MeridianTorus.raw,MeridianTorus.dot2,MeridianTorus.cross2]
      linear_combination r*p.2 0*hh
    · dsimp [MeridianTorus.raw,MeridianTorus.dot2,MeridianTorus.cross2]
      linear_combination r*p.2 1*hh
  have he : MeridianTorus.raw r 1 p=r • MeridianTorus.solidRaw r p := by
    rw [hraw]
    ext i
    fin_cases i <;> simp [MeridianTorus.solidRaw] <;> field_simp [hr.ne'] <;> ring
  change radialNormalize (MeridianTorus.solidRaw r p)=radialNormalize (MeridianTorus.raw r 1 p)
  rw [he,normalize_positive_scale r hr]

/-- Reused verbatim from the accepted explicit convex-meridian construction. -/
lemma disk_at_boundary (r : ℝ) (u : Plane) (hu : u ∈ unitCircle) :
    disk r u=MeridianTorus.surface r (1/2) (u,MeridianTorus.pole) := by
  have h : u 0^2+u 1^2=1 := hu
  have he : raw r u=MeridianTorus.raw r (1/2) (u,MeridianTorus.pole) := by
    ext i
    fin_cases i
    · rfl
    · rfl
    · dsimp [raw,MeridianTorus.raw,MeridianTorus.dot2,MeridianTorus.cross2,MeridianTorus.pole]
      linear_combination -r*h
    · dsimp [raw,MeridianTorus.raw,MeridianTorus.dot2,MeridianTorus.cross2,MeridianTorus.pole]
      ring
  exact congrArg radialNormalize he

lemma actualSolid_meridian_boundary (F : EquivariantSphereContactomorphism) (r : ℝ) (hr : 0<r)
    (Φ : ℝ → Phase → Phase)
    (hT : ∀ q, Φ 1 (MeridianTorus.torusMap r 1 q)=MeridianTorus.torusMap r (1/2) q)
    (v : Circle) :
    actualSolid F r Φ (unitDisk v,1)=imageDisk F r (diskPlane (unitDisk v)).val := by
  have hu : (diskPlane (unitDisk v)).val ∈ unitCircle := (planeUnit v).property
  let q : MeridianTorus.UnitPlaneCircle × MeridianTorus.UnitPlaneCircle :=
    (⟨(diskPlane (unitDisk v)).val,hu⟩,⟨MeridianTorus.pole,MeridianTorus.pole_unit⟩)
  have hm : modelSolid r (unitDisk v,1)=MeridianTorus.torusMap r 1 q := by
    change MeridianTorus.solid r ((diskPlane (unitDisk v)).val,(planeUnit 1).val)=_
    have hp : (planeUnit (1:Circle)).val=MeridianTorus.pole := by
      ext i; fin_cases i <;> simp [planeUnit,MeridianTorus.pole]
    rw [hp]
    exact solid_at_boundary r hr _ hu
  change F.toFun (Φ 1 (modelSolid r (unitDisk v,1)))=F.toFun (disk r _)
  rw [hm,hT,disk_at_boundary r _ hu]
  rfl

lemma meridian_boundary_is_actual_disk (F : EquivariantSphereContactomorphism) (r : ℝ) (hr : 0<r)
    (Φ : ℝ → Phase → Phase)
    (hT : ∀ q, Φ 1 (MeridianTorus.torusMap r 1 q)=MeridianTorus.torusMap r (1/2) q)
    (hS : ∀ p, actualSolid F r Φ p ∈ unitThreeSphere)
    (e : DiskCircle ≃ₜ range (projectedModel (actualSolid F r Φ) hS))
    (he : ∀ p, (e (untwist p)).val=projectedModel (actualSolid F r Φ) hS p)
    (v : Circle) : ∃ y : RoundSphere 4,
      y.val=imageDisk F r (diskPlane (unitDisk v)).val ∧ project 4 y=(e (unitDisk v,1)).val := by
  refine ⟨sphereModel (actualSolid F r Φ) hS (unitDisk v,1),
    actualSolid_meridian_boundary F r hr Φ hT v,?_⟩
  have hu : untwist (unitDisk v,1)=(unitDisk v,1) := by
    apply Prod.ext
    · apply Subtype.ext
      simp [untwist]
    · simp [untwist]
  simpa only [hu,projectedModel,Function.comp_apply] using (he (unitDisk v,1)).symm

end
end ContactTopology.ProjectiveMeridian

open BirkhoffGlobalSection ContactTopology ContactTopology.SolidTorusQuotient ContactTopology.Projective ContactTopology.ConvexMeridian ContactTopology.ProjectiveMeridian Set Function Topology
open scoped ContDiff
theorem solution (F : EquivariantSphereContactomorphism) (r : ℝ) (hr : 0 < r) :
    (∃ d : ProjectiveSphere 4 → ℝ, Continuous d ∧
      ∀ y : RoundSphere 4, d (project 4 y)=phaseRadialContact y.val (imageEuler F y.val)) ∧
    ∃ Φ R : ℝ → Phase → Phase,
      ContDiff ℝ ∞ (fun p : ℝ × Phase => Φ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × Phase => R p.1 p.2) ∧
      (∀ t y, R t (Φ t y)=y) ∧ (∀ t y, Φ t (R t y)=y) ∧
      (∀ t y, Φ t (-y)= -Φ t y) ∧
      (∀ t, MapsTo (Φ t) unitThreeSphere unitThreeSphere) ∧
      (∀ q, Φ 1 (MeridianTorus.torusMap r 1 q)=MeridianTorus.torusMap r (1/2) q) ∧
      (∀ y, zNormSq y=0 → Φ 1 y=y) ∧
      range (actualSolid F r Φ)=F.toFun '' (Φ 1 '' MeridianTorus.solidRegion r) ∧
      ∃ hS : ∀ p, actualSolid F r Φ p ∈ unitThreeSphere,
        ∃ e : DiskCircle ≃ₜ range (projectedModel (actualSolid F r Φ) hS),
          (∀ p, (e (untwist p)).val=projectedModel (actualSolid F r Φ) hS p) ∧
          (∀ p, (e p).val ∈ projectedBoundarySet F r ↔ ‖(p.1:ℂ)‖=1) ∧
          (∀ p, (e p).val ∈ projectedCoreSet F ↔ (p.1:ℂ)=0) ∧
          (∀ p, ‖(p.1:ℂ)‖=1 → ((e p).val ∈ projectedEulerZero F ↔ (p.1:ℂ)=Complex.I ∨ (p.1:ℂ)= -Complex.I)) ∧
          (∀ v : Circle, ∃ y : RoundSphere 4,
            y.val=imageDisk F r (diskPlane (unitDisk v)).val ∧ project 4 y=(e (unitDisk v,1)).val) ∧
          (∀ z : Circle, (range ((fun p => (e p).val) ∘ boundaryCoordinates ∘ meridianAt z) ∩
            projectedEulerZero F).encard=2) ∧
          ∀ γ : C(Circle,Circle × Circle), ContinuousMap.Homotopic meridian γ →
            2 ≤ (range ((fun p => (e p).val) ∘ boundaryCoordinates ∘ γ) ∩ projectedEulerZero F).encard := by
  obtain ⟨hd,Φ,R,hΦ,hR,hRΦ,hΦR,hodd,hsph,hT,hfix,hKr,hS,e,he,hb,hc,hZ⟩ :=
    ContactTopology.projective_solid_boundary_core_dividing_coordinates F r hr
  refine ⟨hd,Φ,R,hΦ,hR,hRΦ,hΦR,hodd,hsph,hT,hfix,hKr,hS,e,he,hb,hc,hZ,?_,?_,?_⟩
  · exact meridian_boundary_is_actual_disk F r hr Φ hT hS e he
  · intro z
    exact meridian_dividing_intersections_eq_two (fun p => (e p).val)
      (fun p q hpq => e.injective (Subtype.ext hpq)) (projectedEulerZero F) hZ z
  · intro γ hγ
    exact dividing_intersections_of_meridian_homotopy (fun p => (e p).val)
      (fun p q hpq => e.injective (Subtype.ext hpq)) (projectedEulerZero F) hZ γ hγ
