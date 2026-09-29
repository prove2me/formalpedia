-- Prove2me | solution 1 for GaloisRep.preservesLimits_conditionSubfunctor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/e49c6f57-d70e-5c7c-a88b-e7b9a5d62835

import Mathlib
import Definitions.Def_GaloisRep_DeformationCondition
import Definitions.Def_GaloisRep_ConditionLifts
import Definitions.Def_Deformations_ConjQuotSubfunctor
import Definitions.Def_Deformations_ProartinianCompact
import Theorems.Thm_IsProartinian_finite_quotient_of_isOpen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe v u

p2m_open "CategoryTheory Function CategoryTheory.Limits IsLocalRing Filter Topology"

namespace Deformation
p2m_export "Deformation" "mapRepn repnFunctor repnFunctor_map liftFunctor IsLocalProartinianAlgebra ProartinianCat ProartinianCat.residueField ReflectedByInjective"
p2m_open "Deformation"

variable {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞]

namespace ProartinianCat
p2m_export "Deformation.ProartinianCat" "of Hom ofHom comp_apply residueField toResidueField ker_toResidueField isTerminalResidueField Hom.hom algebra carrier mk mk.injEq"
p2m_open "Deformation.ProartinianCat"

lemma isUnit_iff_toResidueField_ne_zero {R : ProartinianCat 𝓞} (a : R) :
    IsUnit a ↔ (toResidueField R).hom a ≠ 0 := by
  rw [← notMem_maximalIdeal, ← ker_toResidueField R, RingHom.mem_ker (f := (toResidueField R).hom)]

variable {J : Type u} [Category.{v} J] (D : J ⥤ ProartinianCat 𝓞)

def limitSubalgebra : Subalgebra 𝓞 (∀ j, D.obj j) where
  carrier := {x | (∀ (i j : J) (f : i ⟶ j), (D.map f).hom (x i) = x j) ∧
    ∀ i j : J, (toResidueField (D.obj i)).hom (x i) = (toResidueField (D.obj j)).hom (x j)}
  add_mem' {x y} hx hy := by
    refine ⟨fun i j f ↦ ?_, fun i j ↦ ?_⟩
    · show (D.map f).hom (x i + y i) = x j + y j
      rw [map_add, hx.1 i j f, hy.1 i j f]
    · show (toResidueField (D.obj i)).hom (x i + y i) = (toResidueField (D.obj j)).hom (x j + y j)
      rw [map_add, map_add, hx.2 i j, hy.2 i j]
  mul_mem' {x y} hx hy := by
    refine ⟨fun i j f ↦ ?_, fun i j ↦ ?_⟩
    · show (D.map f).hom (x i * y i) = x j * y j
      rw [map_mul, hx.1 i j f, hy.1 i j f]
    · show (toResidueField (D.obj i)).hom (x i * y i) = (toResidueField (D.obj j)).hom (x j * y j)
      rw [map_mul, map_mul, hx.2 i j, hy.2 i j]
  algebraMap_mem' o := by
    refine ⟨fun i j f ↦ ?_, fun i j ↦ ?_⟩
    · show (D.map f).hom (algebraMap 𝓞 (D.obj i) o) = algebraMap 𝓞 (D.obj j) o
      rw [AlgHomClass.commutes]
    · show (toResidueField (D.obj i)).hom (algebraMap 𝓞 (D.obj i) o)
        = (toResidueField (D.obj j)).hom (algebraMap 𝓞 (D.obj j) o)
      rw [AlgHomClass.commutes, AlgHomClass.commutes]

@[scoped simp]
lemma mem_limitSubalgebra {x : ∀ j, D.obj j} :
    x ∈ limitSubalgebra D ↔
      (∀ (i j : J) (f : i ⟶ j), (D.map f).hom (x i) = x j) ∧
      ∀ i j : J, (toResidueField (D.obj i)).hom (x i) = (toResidueField (D.obj j)).hom (x j) :=
  Iff.rfl

lemma limitSubalgebra_compatible (x : limitSubalgebra D) {i j : J} (f : i ⟶ j) :
    (D.map f).hom ((x : ∀ j, D.obj j) i) = (x : ∀ j, D.obj j) j :=
  x.2.1 i j f

lemma limitSubalgebra_residue_eq (x : limitSubalgebra D) (i j : J) :
    (toResidueField (D.obj i)).hom ((x : ∀ j, D.obj j) i)
      = (toResidueField (D.obj j)).hom ((x : ∀ j, D.obj j) j) :=
  x.2.2 i j

lemma isUnit_iff_isUnit_val_pi (x : limitSubalgebra D) :
    IsUnit x ↔ IsUnit (x : ∀ j, D.obj j) := by
  refine ⟨fun h ↦ h.map (limitSubalgebra D).val, fun h ↦ ?_⟩
  obtain ⟨u, hu⟩ := h
  have hcompat : ∀ (i j : J) (f : i ⟶ j),
      (D.map f).hom ((↑u : ∀ j, D.obj j) i) = (↑u : ∀ j, D.obj j) j := by
    rw [hu]; exact x.2.1
  have hres : ∀ i j : J, (toResidueField (D.obj i)).hom ((↑u : ∀ j, D.obj j) i)
      = (toResidueField (D.obj j)).hom ((↑u : ∀ j, D.obj j) j) := by
    rw [hu]; exact x.2.2
  have hmem : (↑u⁻¹ : ∀ j, D.obj j) ∈ limitSubalgebra D := by
    refine ⟨fun i j f ↦ ?_, fun i j ↦ ?_⟩
    · refine left_inv_eq_right_inv (a := (↑u : ∀ j, D.obj j) j) ?_ ?_
      · rw [← hcompat i j f, ← map_mul, ← Pi.mul_apply, u.inv_mul, Pi.one_apply, map_one]
      · rw [← Pi.mul_apply, u.mul_inv, Pi.one_apply]
    · refine left_inv_eq_right_inv (a := (toResidueField (D.obj j)).hom ((↑u : ∀ j, D.obj j) j))
        ?_ ?_
      · rw [← hres i j, ← map_mul, ← Pi.mul_apply, u.inv_mul, Pi.one_apply, map_one]
      · rw [← map_mul, ← Pi.mul_apply, u.mul_inv, Pi.one_apply, map_one]
  refine ⟨⟨x, ⟨(↑u⁻¹ : ∀ j, D.obj j), hmem⟩, ?_, ?_⟩, rfl⟩
  · exact Subtype.ext (show (x : ∀ j, D.obj j) * ↑u⁻¹ = 1 by rw [← hu, u.mul_inv])
  · exact Subtype.ext (show (↑u⁻¹ : ∀ j, D.obj j) * ↑x = 1 by rw [← hu, u.inv_mul])

lemma isUnit_val_iff_component (j₀ : J) (x : limitSubalgebra D) :
    IsUnit (x : ∀ j, D.obj j) ↔ IsUnit ((x : ∀ j, D.obj j) j₀) := by
  rw [Pi.isUnit_iff]
  refine ⟨fun h ↦ h j₀, fun h j ↦ ?_⟩
  rw [isUnit_iff_toResidueField_ne_zero] at h ⊢
  rwa [limitSubalgebra_residue_eq D x j j₀]

lemma isUnit_iff_component (j₀ : J) (x : limitSubalgebra D) :
    IsUnit x ↔ IsUnit ((x : ∀ j, D.obj j) j₀) :=
  (isUnit_iff_isUnit_val_pi D x).trans (isUnit_val_iff_component D j₀ x)

section Nonempty

variable [Nonempty J]

scoped instance : Nontrivial (limitSubalgebra D) :=
  ⟨0, 1, fun h ↦ zero_ne_one (α := D.obj (Classical.arbitrary J))
    (congrArg (fun z : limitSubalgebra D ↦ (z : ∀ j, D.obj j) (Classical.arbitrary J)) h)⟩

scoped instance : IsLocalRing (limitSubalgebra D) := by
  refine .of_nonunits_add fun x y hx hy hxy ↦ ?_
  rw [mem_nonunits_iff, isUnit_iff_component D (Classical.arbitrary J),
    ← notMem_maximalIdeal, not_not] at hx hy
  rw [isUnit_iff_component D (Classical.arbitrary J)] at hxy
  exact notMem_maximalIdeal.mpr hxy
    ((maximalIdeal (D.obj (Classical.arbitrary J))).add_mem hx hy)

scoped instance : IsLocalHom (algebraMap 𝓞 (limitSubalgebra D)) where
  map_nonunit o ho := by
    rw [isUnit_iff_component D (Classical.arbitrary J)] at ho
    exact (isUnit_map_iff (algebraMap 𝓞 (D.obj (Classical.arbitrary J))) o).mp ho

lemma mem_maximalIdeal_iff_component (j₀ : J) (x : limitSubalgebra D) :
    x ∈ maximalIdeal (limitSubalgebra D) ↔
      (x : ∀ j, D.obj j) j₀ ∈ maximalIdeal (D.obj j₀) := by
  rw [mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_component D j₀, ← mem_nonunits_iff,
    ← mem_maximalIdeal]

scoped instance : IsResidueAlgebra 𝓞 (limitSubalgebra D) := by
  constructor
  intro ξ
  obtain ⟨x, rfl⟩ := residue_surjective ξ
  obtain ⟨o, ho⟩ := IsResidueAlgebra.algebraMap_surjective 𝓞 (D.obj (Classical.arbitrary J))
    (residue _ ((x : ∀ j, D.obj j) (Classical.arbitrary J)))
  rw [IsScalarTower.algebraMap_apply 𝓞 (D.obj (Classical.arbitrary J))
    (ResidueField (D.obj (Classical.arbitrary J))), ResidueField.algebraMap_eq] at ho
  refine ⟨o, ?_⟩
  rw [IsScalarTower.algebraMap_apply 𝓞 (limitSubalgebra D)
    (ResidueField (limitSubalgebra D)), ResidueField.algebraMap_eq]
  refine (Ideal.Quotient.eq (I := maximalIdeal (limitSubalgebra D))).mpr ?_
  rw [mem_maximalIdeal_iff_component D (Classical.arbitrary J)]
  exact Ideal.Quotient.eq.mp ho

end Nonempty

scoped instance : IsTopologicalRing (limitSubalgebra D) :=
  (limitSubalgebra D).toSubring.instIsTopologicalRing

lemma isClosed_limitSubalgebra :
    IsClosed (limitSubalgebra D : Set (∀ j, D.obj j)) := by
  have heq : (limitSubalgebra D : Set (∀ j, D.obj j)) =
      (⋂ (i : J) (j : J) (f : i ⟶ j), {x : ∀ j, D.obj j | (D.map f).hom (x i) = x j}) ∩
      ⋂ (i : J) (j : J), {x : ∀ j, D.obj j |
        (toResidueField (D.obj i)).hom (x i) = (toResidueField (D.obj j)).hom (x j)} := by
    ext x
    simp only [SetLike.mem_coe, mem_limitSubalgebra, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_setOf_eq]
  rw [heq]
  refine IsClosed.inter ?_ ?_
  · exact isClosed_iInter fun i ↦ isClosed_iInter fun j ↦ isClosed_iInter fun f ↦
      isClosed_eq ((D.map f).hom.cont.comp (continuous_apply i)) (continuous_apply j)
  · exact isClosed_iInter fun i ↦ isClosed_iInter fun j ↦
      isClosed_eq ((toResidueField (D.obj i)).hom.cont.comp (continuous_apply i))
        ((toResidueField (D.obj j)).hom.cont.comp (continuous_apply j))

omit [IsLocalRing 𝓞] in

lemma hasBasis_nhds_zero_pi :
    (𝓝 (0 : ∀ j, D.obj j)).HasBasis
      (fun sI : Set J × ∀ j, Ideal (D.obj j) ↦
        sI.1.Finite ∧ ∀ j ∈ sI.1, IsOpen (sI.2 j : Set (D.obj j)))
      (fun sI ↦ sI.1.pi fun j ↦ (sI.2 j : Set (D.obj j))) := by
  rw [nhds_pi]
  exact Filter.hasBasis_pi fun j ↦ IsLinearTopology.hasBasis_open_ideal

lemma hasBasis_nhds_zero_limit :
    (𝓝 (0 : limitSubalgebra D)).HasBasis
      (fun sI : Set J × ∀ j, Ideal (D.obj j) ↦
        sI.1.Finite ∧ ∀ j ∈ sI.1, IsOpen (sI.2 j : Set (D.obj j)))
      (fun sI ↦ (↑(⨅ j ∈ sI.1, (sI.2 j).comap
          ((Pi.evalRingHom _ j).comp (limitSubalgebra D).toSubring.subtype)) :
        Set (limitSubalgebra D))) := by
  have hval : Topology.IsInducing
      (Subtype.val : limitSubalgebra D → ∀ j, D.obj j) := ⟨rfl⟩
  have hbasis : (𝓝 ((0 : limitSubalgebra D) : ∀ j, D.obj j)).HasBasis
      (fun sI : Set J × ∀ j, Ideal (D.obj j) ↦
        sI.1.Finite ∧ ∀ j ∈ sI.1, IsOpen (sI.2 j : Set (D.obj j)))
      (fun sI ↦ sI.1.pi fun j ↦ (sI.2 j : Set (D.obj j))) := hasBasis_nhds_zero_pi D
  refine (hval.basis_nhds hbasis).congr (fun _ ↦ Iff.rfl) (fun sI _ ↦ ?_)
  ext x
  simp only [Set.mem_preimage, Set.mem_pi, SetLike.mem_coe, Submodule.mem_iInf, Ideal.mem_comap,
    RingHom.coe_comp, Function.comp_apply]
  rfl

scoped instance : IsLinearTopology (limitSubalgebra D) (limitSubalgebra D) :=
  .mk_of_hasBasis _ (hasBasis_nhds_zero_limit D)

section Compact

variable [Finite (ResidueField 𝓞)] [Nonempty J]

scoped instance : CompactSpace (limitSubalgebra D) :=
  isCompact_iff_compactSpace.mp (isClosed_limitSubalgebra D).isCompact

set_option synthInstance.maxHeartbeats 320000 in

scoped instance : IsProartinian (limitSubalgebra D) where
  isArtinianRing_quotient I hI :=
    have : Finite (limitSubalgebra D ⧸ I) :=
      AddSubgroup.quotient_finite_of_isOpen _ hI
    inferInstance

scoped instance : IsLocalProartinianAlgebra 𝓞 (limitSubalgebra D) where

noncomputable def limitObj : ProartinianCat 𝓞 := of 𝓞 (limitSubalgebra D)

noncomputable def limitProj (j : J) : limitObj D ⟶ D.obj j :=
  ofHom ⟨(Pi.evalAlgHom 𝓞 _ j).comp (limitSubalgebra D).val,
    (continuous_apply j).comp continuous_subtype_val⟩

@[scoped simp]
lemma limitProj_apply (j : J) (x : limitSubalgebra D) :
    (limitProj D j).hom x = (x : ∀ j, D.obj j) j := rfl

noncomputable def limitCone : Cone D where
  pt := limitObj D
  π :=
    { app := fun j ↦ limitProj D j
      naturality := fun i j f ↦ by
        ext x
        exact (limitSubalgebra_compatible D x f).symm }

omit [Finite (ResidueField 𝓞)] [Nonempty J] in
variable {D} in

lemma mem_limitSubalgebra_of_cone (s : Cone D) (c : s.pt) :
    (fun j ↦ (s.π.app j).hom c) ∈ limitSubalgebra D := by
  refine ⟨fun i j f ↦ ?_, fun i j ↦ ?_⟩
  · exact congrArg (fun k ↦ Hom.hom k c) (s.w f)
  · have hij : s.π.app i ≫ toResidueField (D.obj i) = s.π.app j ≫ toResidueField (D.obj j) :=
      Subsingleton.elim _ _
    exact congrArg (fun k ↦ Hom.hom k c) hij

variable {D} in

noncomputable def limitLift (s : Cone D) : s.pt ⟶ limitObj D :=
  ofHom ⟨((Pi.algHom 𝓞 (fun j ↦ (D.obj j : Type u)) fun j ↦
        (s.π.app j).hom.toAlgHom : s.pt →ₐ[𝓞] ∀ j, D.obj j)).codRestrict
      (limitSubalgebra D) (mem_limitSubalgebra_of_cone s),
    Continuous.subtype_mk (continuous_pi fun j ↦ (s.π.app j).hom.cont) _⟩

variable {D} in
@[reassoc (attr := simp)]
lemma limitLift_proj (s : Cone D) (j : J) :
    limitLift s ≫ limitProj D j = s.π.app j := by
  ext c
  rfl

noncomputable def limitConeIsLimit : IsLimit (limitCone D) where
  lift s := limitLift s
  fac s j := limitLift_proj s j
  uniq s m hm := by
    ext c
    refine Subtype.ext (funext fun j ↦ ?_)
    exact congrArg (fun k ↦ Hom.hom k c) ((hm j).trans (limitLift_proj s j).symm)

end Compact

section HasLimits

variable (𝓞) in

scoped instance hasLimitsOfShape_of_nonempty [Finite (ResidueField 𝓞)] [Nonempty J] :
    HasLimitsOfShape J (ProartinianCat 𝓞) where
  has_limit F := HasLimit.mk ⟨limitCone F, limitConeIsLimit F⟩

variable (𝓞) in

scoped instance hasLimitsOfShape_of_isCofiltered [Finite (ResidueField 𝓞)] [IsCofiltered J] :
    HasLimitsOfShape J (ProartinianCat 𝓞) :=
  letI : Nonempty J := IsCofiltered.nonempty
  inferInstance

scoped instance solAux_hasTerminal : HasTerminal (ProartinianCat 𝓞) := isTerminalResidueField.hasTerminal

end HasLimits

end ProartinianCat
p2m_reactivate "P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation.ProartinianCat"

end Deformation
p2m_reactivate "P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation.ProartinianCat P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation"

p2m_open "CategoryTheory Function CategoryTheory.Limits IsLocalRing"

namespace Deformation
p2m_export "Deformation" "mapRepn repnFunctor repnFunctor_map liftFunctor IsLocalProartinianAlgebra ProartinianCat ProartinianCat.residueField ReflectedByInjective"
p2m_open "Deformation"

variable {n : Type} [Fintype n] [DecidableEq n]
variable (G : Type u) [Group G] [TopologicalSpace G]
variable (𝓞 : Type u) [CommRing 𝓞] [IsLocalRing 𝓞]

section GlueFamily

variable [Finite (ResidueField 𝓞)]
variable {J : Type u} [Category.{v} J] [Nonempty J] (D : J ⥤ ProartinianCat 𝓞)

namespace SubalgebraGL

p2m_open "Deformation.ProartinianCat P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation.ProartinianCat"

def glueMatrixFamily (M : ∀ j, Matrix n n (D.obj j))
    (h : ∀ a b, (fun j => M j a b) ∈ limitSubalgebra D) :
    Matrix n n (limitSubalgebra D) :=
  Matrix.of fun a b => (⟨fun j => M j a b, h a b⟩ : limitSubalgebra D)

omit [Fintype n] [DecidableEq n] in

lemma glueMatrixFamily_map_proj (M : ∀ j, Matrix n n (D.obj j))
    (h : ∀ a b, (fun j => M j a b) ∈ limitSubalgebra D) (j : J) :
    (glueMatrixFamily 𝓞 D M h).map (limitProj D j).hom.toRingHom = M j := by
  ext a b
  rfl

noncomputable def glueGLFamily (M : ∀ j, GL n (D.obj j))
    (h : ∀ a b, (fun j => (M j : Matrix n n (D.obj j)) a b) ∈ limitSubalgebra D) :
    GL n (limitSubalgebra D) :=
  Matrix.GeneralLinearGroup.mk''
    (glueMatrixFamily 𝓞 D (fun j => (M j : Matrix n n (D.obj j))) h) <| by
    refine (isUnit_iff_component D (Classical.arbitrary J) _).mpr ?_
    have h1 : ((glueMatrixFamily 𝓞 D (fun j => (M j : Matrix n n (D.obj j))) h).det :
          ∀ j, D.obj j) (Classical.arbitrary J) =
        (M (Classical.arbitrary J) : Matrix n n (D.obj (Classical.arbitrary J))).det :=
      ((limitProj D (Classical.arbitrary J)).hom.toRingHom.map_det _).trans
        (congrArg Matrix.det
          (glueMatrixFamily_map_proj 𝓞 D (fun j => (M j : Matrix n n (D.obj j))) h
            (Classical.arbitrary J)))
    rw [h1]
    exact (Matrix.isUnit_iff_isUnit_det _).mp (M _).isUnit

@[scoped simp]
lemma map_proj_glueGLFamily (M : ∀ j, GL n (D.obj j))
    (h : ∀ a b, (fun j => (M j : Matrix n n (D.obj j)) a b) ∈ limitSubalgebra D) (j : J) :
    Matrix.GeneralLinearGroup.map (limitProj D j).hom.toRingHom (glueGLFamily 𝓞 D M h) =
      M j := by
  ext a b
  rfl

omit [Fintype n] [DecidableEq n] in

lemma proj_map_injective {M N : Matrix n n (limitSubalgebra D)}
    (h : ∀ j, M.map (limitProj D j).hom.toRingHom = N.map (limitProj D j).hom.toRingHom) :
    M = N := by
  refine Matrix.ext fun a b => Subtype.val_injective (funext fun j => ?_)
  exact congrArg (fun P => P a b) (h j)

lemma proj_mapGL_injective {M N : GL n (limitSubalgebra D)}
    (h : ∀ j, Matrix.GeneralLinearGroup.map (limitProj D j).hom.toRingHom M =
      Matrix.GeneralLinearGroup.map (limitProj D j).hom.toRingHom N) :
    M = N :=
  Units.ext (proj_map_injective 𝓞 D fun j => congrArg Units.val (h j))

end SubalgebraGL
p2m_reactivate "P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation.ProartinianCat P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation.SubalgebraGL"

open SubalgebraGL _root_.Deformation.ProartinianCat _root_.P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation.ProartinianCat in

theorem existsUnique_repnGlueFamily (ρ : ∀ j, G →ₜ* GL n (D.obj j))
    (hcompat : ∀ (i j : J) (f : i ⟶ j), (repnFunctor n G 𝓞).map (D.map f) (ρ i) = ρ j)
    (hres : ∀ i j : J, (repnFunctor n G 𝓞).map (toResidueField (D.obj i)) (ρ i) =
      (repnFunctor n G 𝓞).map (toResidueField (D.obj j)) (ρ j)) :
    ∃! ρ' : G →ₜ* GL n (limitObj D),
      ∀ j, (repnFunctor n G 𝓞).map (limitProj D j) ρ' = ρ j := by

  have hmem : ∀ (σ : G) (a b : n),
      (fun j => (ρ j σ : Matrix n n (D.obj j)) a b) ∈ limitSubalgebra D := by
    intro σ a b
    refine ⟨fun i j f => ?_, fun i j => ?_⟩
    · have h1 : Matrix.GeneralLinearGroup.map (D.map f).hom.toRingHom (ρ i σ) = ρ j σ :=
        (repnFunctor_map G 𝓞 (D.map f) (ρ i) σ).symm.trans
          ((DFunLike.congr_fun (F := G →ₜ* GL n (D.obj j))
            (α := G) (β := fun _ => GL n (D.obj j)) (hcompat i j f) σ))
      exact congrArg (fun P : GL n (D.obj j) => (P : Matrix n n (D.obj j)) a b) h1
    · have h1 : Matrix.GeneralLinearGroup.map (toResidueField (D.obj i)).hom.toRingHom (ρ i σ)
          = Matrix.GeneralLinearGroup.map (toResidueField (D.obj j)).hom.toRingHom (ρ j σ) :=
        (repnFunctor_map G 𝓞 (toResidueField (D.obj i)) (ρ i) σ).symm.trans
          (((DFunLike.congr_fun (F := G →ₜ* GL n (residueField (𝓞 := 𝓞)))
            (α := G) (β := fun _ => GL n (residueField (𝓞 := 𝓞))) (hres i j) σ)).trans
            (repnFunctor_map G 𝓞 (toResidueField (D.obj j)) (ρ j) σ))
      exact congrArg (fun P : GL n (residueField (𝓞 := 𝓞)) =>
        (P : Matrix n n (residueField (𝓞 := 𝓞))) a b) h1
  refine ⟨⟨MonoidHom.mk' (fun σ => glueGLFamily 𝓞 D (fun j => ρ j σ) (hmem σ))
    (fun σ τ => proj_mapGL_injective 𝓞 D fun j => ?_), ?_⟩, fun j => ?_, fun ρ'' hρ'' => ?_⟩

  · rw [map_mul]
    simp only [map_proj_glueGLFamily]
    exact map_mul (ρ j) σ τ

  · refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · refine continuous_matrix fun a b => ?_
      exact Continuous.subtype_mk
        (continuous_pi fun j =>
          (Units.continuous_val.comp (map_continuous (ρ j))).matrix_elem a b) _
    · refine continuous_matrix fun a b => ?_
      refine continuous_induced_rng.mpr ?_
      refine ((continuous_pi fun j =>
        (Units.continuous_coe_inv.comp (map_continuous (ρ j))).matrix_elem a b).congr
        fun σ => ?_)
      refine funext fun j => ?_
      have h1 : Matrix.GeneralLinearGroup.map (limitProj D j).hom.toRingHom
          ((glueGLFamily 𝓞 D (fun j => ρ j σ) (hmem σ))⁻¹) = ((ρ j σ)⁻¹ : GL n (D.obj j)) := by
        rw [map_inv, map_proj_glueGLFamily]
      exact (congrArg (fun P : GL n (D.obj j) => (P : Matrix n n (D.obj j)) a b) h1).symm

  · refine ContinuousMonoidHom.ext fun σ => ?_
    exact (repnFunctor_map G 𝓞 (limitProj D j) _ σ).trans
      (map_proj_glueGLFamily 𝓞 D (fun j => ρ j σ) (hmem σ) j)

  · refine ContinuousMonoidHom.ext fun σ => ?_
    refine proj_mapGL_injective 𝓞 D fun j => ?_
    exact ((repnFunctor_map G 𝓞 (limitProj D j) ρ'' σ).symm.trans
      (DFunLike.congr_fun (F := G →ₜ* GL n (D.obj j))
        (α := G) (β := fun _ => GL n (D.obj j)) (hρ'' j) σ)).trans
      (map_proj_glueGLFamily 𝓞 D (fun j => ρ j σ) (hmem σ) j).symm

end GlueFamily
p2m_reactivate "P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation.ProartinianCat P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation.SubalgebraGL"

section LiftPreserves

variable [Finite (ResidueField 𝓞)]
variable (ρ₀ : (repnFunctor n G 𝓞).obj .residueField)

p2m_open "Deformation.ProartinianCat P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation.ProartinianCat"

omit [Finite (ResidueField 𝓞)] in

lemma mem_liftFunctor_obj_iff {R : ProartinianCat 𝓞} (ρ' : (repnFunctor n G 𝓞).obj R) :
    ρ' ∈ (liftFunctor n G 𝓞 ρ₀).obj R ↔
      (repnFunctor n G 𝓞).map (toResidueField R) ρ' = ρ₀ := by
  show (repnFunctor n G 𝓞).map (isTerminalResidueField.from R) ρ' ∈ ({ρ₀} : Set _) ↔ _
  rw [Set.mem_singleton_iff,
    Subsingleton.elim (isTerminalResidueField.from R) (toResidueField R)]

end LiftPreserves
p2m_reactivate "P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation.ProartinianCat P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation.SubalgebraGL"

end Deformation
p2m_reactivate "P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation.ProartinianCat P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation.SubalgebraGL"

open CategoryTheory IsLocalRing

namespace GaloisRep
p2m_export "GaloisRep" "IsArtinianTestAlgebra IsDeformationCondition conditionLifts conditionSubfunctor"
namespace SolAuxG5
p2m_open "GaloisRep"

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

variable {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]

p2m_open "Deformation P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation"

theorem discreteTopology_of_isArtinianRing (B : ProartinianCat 𝒪) [IsArtinianRing B] :
    DiscreteTopology B := by

  have hne : {I : Ideal B | IsOpen (I : Set B)}.Nonempty := ⟨⊤, isOpen_univ⟩
  obtain ⟨I₀, hI₀open, hI₀min⟩ :=
    (IsArtinian.set_has_minimal (R := B) (M := B) {I : Ideal B | IsOpen (I : Set B)} hne)

  have hle : ∀ J : Ideal B, IsOpen (J : Set B) → I₀ ≤ J := by
    intro J hJ
    have hinf : IsOpen ((I₀ ⊓ J : Ideal B) : Set B) := by
      have : ((I₀ ⊓ J : Ideal B) : Set B) = (I₀ : Set B) ∩ (J : Set B) := rfl
      rw [this]; exact hI₀open.inter hJ
    have := hI₀min (I₀ ⊓ J) hinf

    have heq : I₀ ⊓ J = I₀ := by
      by_contra hne'
      exact this (lt_of_le_of_ne inf_le_left hne')
    exact heq ▸ inf_le_right

  have hbot : I₀ = ⊥ := by
    refine le_bot_iff.mp fun x hx => ?_
    by_contra hx0

    have hmem : ({x}ᶜ : Set B) ∈ nhds (0 : B) :=
      isOpen_compl_singleton.mem_nhds (fun h => hx0 (Set.mem_singleton_iff.mp h).symm)
    obtain ⟨J, hJopen, hJsub⟩ := (IsLinearTopology.hasBasis_open_ideal.mem_iff).mp hmem
    exact hJsub (hle J hJopen hx) rfl

  rw [hbot] at hI₀open
  have h0 : IsOpen ({0} : Set B) := by simpa using hI₀open
  exact discreteTopology_iff_isOpen_singleton_zero.mpr h0 |> fun h => h

noncomputable def stdRep (B : ProartinianCat 𝒪) [IsArtinianRing B] (τ : Γℚ →ₜ* GL (Fin 2) B) :
    GaloisRepAdic B where
  V := Fin 2 → B
  finrank_eq := Module.finrank_fin_fun B
  ρ := (Units.coeHom _).comp (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp τ.toMonoidHom)
  isAdicContinuous := by
    haveI : DiscreteTopology B := discreteTopology_of_isArtinianRing B
    intro n
    have hcont : Continuous fun σ : Γℚ => ((τ σ : GL (Fin 2) B) : Matrix (Fin 2) (Fin 2) B) :=
      Units.continuous_val.comp (map_continuous τ)
    have hmem : (fun σ : Γℚ => ((τ σ : GL (Fin 2) B) : Matrix (Fin 2) (Fin 2) B)) ⁻¹' {1} ∈
        nhds (1 : Γℚ) := by
      refine ((isOpen_discrete _).preimage hcont).mem_nhds ?_
      simp
    obtain ⟨L, hL, hsub⟩ := (krullTopology_mem_nhds_one_iff ℚ (AlgebraicClosure ℚ) _).mp hmem
    refine ⟨L, hL, fun σ hσ v => ?_⟩
    have hσmem : σ ∈ (L.fixingSubgroup : Set Γℚ) := by
      rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]; exact hσ
    have h1 : ((τ σ : GL (Fin 2) B) : Matrix (Fin 2) (Fin 2) B) = 1 := hsub hσmem
    have hact : ((Units.coeHom _).comp
        (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp τ.toMonoidHom)) σ v =
        ((τ σ : GL (Fin 2) B) : Matrix (Fin 2) (Fin 2) B).mulVec v := by
      show ((Matrix.GeneralLinearGroup.toLin (τ σ) : LinearMap.GeneralLinearGroup B (Fin 2 → B)) :
        (Fin 2 → B) →ₗ[B] (Fin 2 → B)) v = _
      rw [Matrix.GeneralLinearGroup.coe_toLin]; rfl
    rw [hact, h1, Matrix.one_mulVec, sub_self]
    exact Submodule.zero_mem _

lemma stdRep_ρ_apply (B : ProartinianCat 𝒪) [IsArtinianRing B] (τ : Γℚ →ₜ* GL (Fin 2) B)
    (σ : Γℚ) (v : Fin 2 → B) :
    (stdRep B τ).ρ σ v = ((τ σ : GL (Fin 2) B) : Matrix (Fin 2) (Fin 2) B).mulVec v := by
  show ((Matrix.GeneralLinearGroup.toLin (τ σ) : LinearMap.GeneralLinearGroup B (Fin 2 → B)) :
    (Fin 2 → B) →ₗ[B] (Fin 2 → B)) v = _
  rw [Matrix.GeneralLinearGroup.coe_toLin]; rfl

noncomputable def equivStdRepOfBasis (B : ProartinianCat 𝒪) [IsArtinianRing B] (τ : Γℚ →ₜ* GL (Fin 2) B)
    (ρB : GaloisRepAdic B) (b : Module.Basis (Fin 2) B ρB.V)
    (hb : ∀ σ, LinearMap.toMatrix b b (ρB.ρ σ) = ((τ σ : GL (Fin 2) B) : Matrix (Fin 2) (Fin 2) B)) :
    GaloisRepAdic.Equiv ρB (stdRep B τ) where
  toLinearEquiv := b.equivFun
  map_apply σ x := by
    rw [stdRep_ρ_apply, ← hb σ]
    show (b.equivFun : ρB.V → (Fin 2 → B)) (ρB.ρ σ x) = _
    funext i
    simp only [Module.Basis.equivFun_apply]
    rw [← LinearMap.toMatrix_mulVec_repr b b (ρB.ρ σ) x]
    rfl

theorem isEquiv_stdRep_of_basis (B : ProartinianCat 𝒪) [IsArtinianRing B] (τ : Γℚ →ₜ* GL (Fin 2) B)
    (ρB : GaloisRepAdic B) (b : Module.Basis (Fin 2) B ρB.V)
    (hb : ∀ σ, LinearMap.toMatrix b b (ρB.ρ σ) = ((τ σ : GL (Fin 2) B) : Matrix (Fin 2) (Fin 2) B)) :
    ρB.IsEquiv (stdRep B τ) :=
  ⟨equivStdRepOfBasis B τ ρB b hb⟩

lemma toMatrix_stdRep (B : ProartinianCat 𝒪) [IsArtinianRing B] (τ : Γℚ →ₜ* GL (Fin 2) B) (σ : Γℚ) :
    LinearMap.toMatrix (Pi.basisFun B (Fin 2)) (Pi.basisFun B (Fin 2)) ((stdRep B τ).ρ σ) =
      ((τ σ : GL (Fin 2) B) : Matrix (Fin 2) (Fin 2) B) := by
  have : (stdRep B τ).ρ σ = Matrix.mulVecLin ((τ σ : GL (Fin 2) B) : Matrix (Fin 2) (Fin 2) B) :=
    LinearMap.ext fun v => stdRep_ρ_apply B τ σ v
  rw [this, LinearMap.toMatrix_eq_toMatrix']
  have h2 : Matrix.mulVecLin ((τ σ : GL (Fin 2) B) : Matrix (Fin 2) (Fin 2) B) =
      Matrix.toLin' ((τ σ : GL (Fin 2) B) : Matrix (Fin 2) (Fin 2) B) := by
    apply LinearMap.ext; intro v; rw [Matrix.toLin'_apply]; rfl
  rw [h2, LinearMap.toMatrix'_toLin']

theorem isArtinianTestAlgebra (B : ProartinianCat 𝒪) [IsArtinianRing B] :
    GaloisRep.IsArtinianTestAlgebra 𝒪 B where
  isLocalHom := inferInstance
  residue_surjective := by
    have h := IsResidueAlgebra.algebraMap_surjective 𝒪 (B : Type)
    rwa [IsScalarTower.algebraMap_eq 𝒪 B (ResidueField B), ResidueField.algebraMap_eq, RingHom.coe_comp] at h
  isArtinian := inferInstance

theorem isEquiv_baseChangeAlong_stdRep (B B' : ProartinianCat 𝒪) [IsArtinianRing B] [IsArtinianRing B']
    (f : B ⟶ B') (hf : IsLocalHom f.hom.toRingHom) (τ : Γℚ →ₜ* GL (Fin 2) B) :
    ((stdRep B τ).baseChangeAlong f.hom.toRingHom hf).IsEquiv
      (stdRep B' (mapRepn (Fin 2) Γℚ 𝒪 f τ)) := by
  letI : Algebra B B' := f.hom.toRingHom.toAlgebra
  refine ⟨{ toLinearEquiv := TensorProduct.piScalarRight B B' B' (Fin 2), map_apply := fun σ => ?_ }⟩

  change ∀ x : TensorProduct B B' (Fin 2 → B),
    (TensorProduct.piScalarRight B B' B' (Fin 2))
        (((Matrix.mulVecLin ((τ σ : GL (Fin 2) B) : Matrix (Fin 2) (Fin 2) B)).baseChange B') x) =
      ((Matrix.GeneralLinearGroup.map f.hom.toRingHom (τ σ) : GL (Fin 2) B') :
          Matrix (Fin 2) (Fin 2) B').mulVec ((TensorProduct.piScalarRight B B' B' (Fin 2)) x)
  intro x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, Matrix.mulVec_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, Matrix.mulVec_add]
  | tmul n v =>
    rw [LinearMap.baseChange_tmul, Matrix.mulVecLin_apply]
    funext i
    rw [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRight_apply,
      TensorProduct.piScalarRightHom_tmul, TensorProduct.piScalarRightHom_tmul]
    have hmap : ((Matrix.GeneralLinearGroup.map f.hom.toRingHom (τ σ) : GL (Fin 2) B') : Matrix (Fin 2) (Fin 2) B')
        = ((τ σ : GL (Fin 2) B) : Matrix (Fin 2) (Fin 2) B).map f.hom.toRingHom := by
      rw [Matrix.GeneralLinearGroup.map, Units.coe_map]; rfl
    simp only [hmap, Matrix.map_apply, Matrix.mulVec, dotProduct, Algebra.smul_def, RingHom.algebraMap_toAlgebra,
      map_sum, map_mul, Finset.sum_mul, mul_assoc]

end GaloisRep.SolAuxG5
p2m_reactivate "P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation.ProartinianCat P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation.SubalgebraGL"
p2m_reactivate "P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation.ProartinianCat P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation.SubalgebraGL"

namespace Deformation
p2m_export "Deformation" "mapRepn repnFunctor repnFunctor_map liftFunctor IsLocalProartinianAlgebra ProartinianCat ProartinianCat.residueField ReflectedByInjective"
p2m_open "Deformation"

variable {𝓞 : Type} [CommRing 𝓞] [IsLocalRing 𝓞]

namespace ProartinianCat
p2m_export "Deformation.ProartinianCat" "of Hom ofHom comp_apply residueField toResidueField ker_toResidueField isTerminalResidueField Hom.hom algebra carrier mk mk.injEq"
p2m_open "Deformation.ProartinianCat"

variable (B : ProartinianCat 𝓞)

def OpenIdx : Type := {I : Ideal B // IsOpen (X := B) I ∧ I ≠ ⊤}

scoped instance : PartialOrder (OpenIdx B) :=
  inferInstanceAs (PartialOrder {I : Ideal B // IsOpen (X := B) I ∧ I ≠ ⊤})

scoped instance : Nonempty (OpenIdx B) :=
  ⟨⟨maximalIdeal B, isOpen_maximalIdeal_of_isProartinian,
    (maximalIdeal.isMaximal B).ne_top⟩⟩

def OpenIdx.inf (I J : OpenIdx B) : OpenIdx B :=
  ⟨I.1 ⊓ J.1, IsOpen.inter I.2.1 J.2.1,
    fun h ↦ I.2.2 (top_le_iff.mp (h.symm.trans_le inf_le_left))⟩

variable {B} in
omit [IsLocalRing 𝓞] in
lemma OpenIdx.inf_le_left (I J : OpenIdx B) : OpenIdx.inf B I J ≤ I := by
  change I.1 ⊓ J.1 ≤ I.1
  exact _root_.inf_le_left

variable {B} in
omit [IsLocalRing 𝓞] in
lemma OpenIdx.inf_le_right (I J : OpenIdx B) : OpenIdx.inf B I J ≤ J := by
  change I.1 ⊓ J.1 ≤ J.1
  exact _root_.inf_le_right

variable {B} (I : OpenIdx B)

scoped instance quot_nontrivial : Nontrivial (B ⧸ I.1) := Ideal.Quotient.nontrivial_iff.2 I.2.2

scoped instance quot_isLocalRing : IsLocalRing (B ⧸ I.1) :=
  .of_surjective' _ Ideal.Quotient.mk_surjective

scoped instance quot_isArtinianRing : IsArtinianRing (B ⧸ I.1) :=
  IsProartinian.isArtinianRing_quotient I.1 I.2.1

scoped instance quot_discreteTopology : DiscreteTopology (B ⧸ I.1) :=
  QuotientAddGroup.discreteTopology I.2.1

scoped instance quot_isLocalProartinianAlgebra : IsLocalProartinianAlgebra 𝓞 (B ⧸ I.1) :=
  haveI : IsLocalHom (Ideal.Quotient.mk I.1) :=
    .of_surjective _ Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (algebraMap 𝓞 (B ⧸ I.1)) := by
    have heq : algebraMap 𝓞 (B ⧸ I.1) = (Ideal.Quotient.mk I.1).comp (algebraMap 𝓞 B) := by
      rw [IsScalarTower.algebraMap_eq 𝓞 B (B ⧸ I.1), Ideal.Quotient.algebraMap_eq]
    rw [heq]
    exact RingHom.isLocalHom_comp _ _
  { }

noncomputable def quotObj : ProartinianCat 𝓞 := of 𝓞 (B ⧸ I.1)

scoped instance [Finite (ResidueField 𝓞)] : Finite (quotObj I) :=
  IsProartinian.finite_quotient_of_isOpen (R := B) I.1 I.2.1

scoped instance : DiscreteTopology (quotObj I) :=
  inferInstanceAs (DiscreteTopology (B ⧸ I.1))

lemma continuous_quotientMk : Continuous (Ideal.Quotient.mk I.1) := by
  refine (RingHom.continuous_iff_isOpen_ker (f := Ideal.Quotient.mk I.1)).mpr ?_
  rw [Ideal.mk_ker]
  exact I.2.1

noncomputable def quotMk : B ⟶ quotObj I :=
  ofHom ⟨Ideal.Quotient.mkₐ 𝓞 I.1, continuous_quotientMk I⟩

@[scoped simp]
lemma quotMk_apply (b : B) : (quotMk I).hom b = Ideal.Quotient.mk I.1 b := rfl

noncomputable def quotFactor {I J : OpenIdx B} (h : I ≤ J) : quotObj I ⟶ quotObj J :=
  ofHom ⟨Ideal.Quotient.factorₐ 𝓞 (h : I.1 ≤ J.1), continuous_of_discreteTopology⟩

@[scoped simp]
lemma quotFactor_mk {I J : OpenIdx B} (h : I ≤ J) (b : B) :
    (quotFactor h).hom (Ideal.Quotient.mk I.1 b) = Ideal.Quotient.mk J.1 b := rfl

@[reassoc (attr := simp)]
lemma quotMk_quotFactor {I J : OpenIdx B} (h : I ≤ J) :
    quotMk I ≫ quotFactor h = quotMk J := by
  ext b
  rfl

noncomputable def quotLiftHom {C : ProartinianCat 𝓞} (g : B ⟶ C) (hg : ∀ x ∈ I.1, g.hom x = 0) :
    quotObj I ⟶ C :=
  ⟨{ Ideal.Quotient.liftₐ I.1 (g.hom : B →ₐ[𝓞] C) hg with cont := continuous_of_discreteTopology }⟩

lemma quotLiftHom_mk {C : ProartinianCat 𝓞} (g : B ⟶ C) (hg : ∀ x ∈ I.1, g.hom x = 0) (b : B) :
    (quotLiftHom I g hg).hom (Ideal.Quotient.mk I.1 b) = g.hom b := rfl

lemma quotMk_quotLiftHom {C : ProartinianCat 𝓞} (g : B ⟶ C) (hg : ∀ x ∈ I.1, g.hom x = 0) :
    quotMk I ≫ quotLiftHom I g hg = g := by
  ext b
  rfl

lemma quotLiftHom_injective {C : ProartinianCat 𝓞} (g : B ⟶ C) (hg : ∀ x ∈ I.1, g.hom x = 0)
    (hker : ∀ x, g.hom x = 0 → x ∈ I.1) : Function.Injective (quotLiftHom I g hg).hom := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (hker b hx)

end ProartinianCat
p2m_reactivate "P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation.ProartinianCat P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation.SubalgebraGL"

end Deformation
p2m_reactivate "P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation.ProartinianCat P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation.SubalgebraGL"

namespace GaloisRep
p2m_export "GaloisRep" "IsArtinianTestAlgebra IsDeformationCondition conditionLifts conditionSubfunctor"
namespace SolAuxG5
p2m_open "GaloisRep"

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

variable {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]

p2m_open "Deformation P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation Deformation.ProartinianCat P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation.ProartinianCat"

theorem exists_openIdx_comap_le [Finite (ResidueField 𝒪)] {T A : ProartinianCat 𝒪} (ι : T ⟶ A)
    (hι : Function.Injective ι.hom) (J : Ideal T) (hJ : IsOpen (J : Set T)) :
    ∃ J' : OpenIdx A, J'.1.comap ι.hom.toRingHom ≤ J := by
  haveI : T2Space A := inferInstance
  have hemb : Topology.IsClosedEmbedding ι.hom := (ι.hom.cont).isClosedEmbedding hι
  obtain ⟨U, hUopen, hUJ⟩ := hemb.isInducing.isOpen_iff.mp hJ
  have h0U : (0 : A) ∈ U := by
    have : (0 : T) ∈ ι.hom ⁻¹' U := by rw [hUJ]; exact J.zero_mem
    simpa using this
  obtain ⟨J', hJ'open, hJ'U⟩ := (IsLinearTopology.hasBasis_open_ideal.mem_iff).mp (hUopen.mem_nhds h0U)
  refine ⟨⟨J' ⊓ maximalIdeal A, ?_, ?_⟩, ?_⟩
  · have : ((J' ⊓ maximalIdeal A : Ideal A) : Set A) = (J' : Set A) ∩ (maximalIdeal A : Set A) := rfl
    rw [this]; exact hJ'open.inter isOpen_maximalIdeal_of_isProartinian
  · exact fun h => (maximalIdeal.isMaximal A).ne_top (top_le_iff.mp (h ▸ inf_le_right))
  · intro x hx
    have hx' : ι.hom x ∈ J' := (Ideal.mem_comap.mp hx).1
    have : x ∈ ι.hom ⁻¹' U := hJ'U hx'
    rw [hUJ] at this
    exact this

theorem isLocalHom_of_algHom_of_residue_surjective
    {R A : Type} [CommRing R] [IsLocalRing R] [Algebra 𝒪 R] [CommRing A] [IsLocalRing A] [Algebra 𝒪 A]
    [IsLocalHom (algebraMap 𝒪 A)]
    (hA : Function.Surjective (IsLocalRing.residue A ∘ algebraMap 𝒪 A))
    (φ : R →ₐ[𝒪] A) : IsLocalHom (φ : R →+* A) := by
  refine ⟨fun x hx => ?_⟩
  by_contra hxu
  have hxm : x ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal x).mpr hxu
  obtain ⟨o, ho⟩ := hA (IsLocalRing.residue A (φ x))
  simp only [Function.comp_apply] at ho
  have hou : IsUnit o := by
    by_contra hou
    have hom : algebraMap 𝒪 A o ∈ IsLocalRing.maximalIdeal A := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact fun h => hou ((isUnit_map_iff (algebraMap 𝒪 A) o).mp h)
    have h0 : IsLocalRing.residue A (φ x) = 0 := by
      rw [← ho, IsLocalRing.residue_eq_zero_iff]
      exact hom
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h0
    exact h0 hx
  have hker : x - algebraMap 𝒪 R o ∈ IsLocalRing.maximalIdeal R := by
    have hmem : x - algebraMap 𝒪 R o ∈ RingHom.ker ((IsLocalRing.residue A).comp (φ : R →+* A)) := by
      rw [RingHom.mem_ker, RingHom.comp_apply, map_sub, RingHom.coe_coe, AlgHom.commutes, map_sub, ho, sub_self]
    exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _) hmem
  have : algebraMap 𝒪 R o ∈ IsLocalRing.maximalIdeal R := by
    have h := sub_mem hxm hker
    rwa [sub_sub_cancel] at h
  exact (IsLocalRing.mem_maximalIdeal _).mp this (hou.map _)

theorem isLocalHom_coe_hom {X Y : ProartinianCat 𝒪} (f : X ⟶ Y) :
    IsLocalHom ((f.hom : X →ₐ[𝒪] Y) : X →+* Y) :=
  isLocalHom_of_algHom_of_residue_surjective (𝒪 := 𝒪)
    (by
      have h := IsResidueAlgebra.algebraMap_surjective 𝒪 (Y : Type)
      rwa [IsScalarTower.algebraMap_eq 𝒪 Y (ResidueField Y), ResidueField.algebraMap_eq, RingHom.coe_comp] at h)
    (f.hom : X →ₐ[𝒪] Y)

theorem isEquiv_symm {B : Type} [CommRing B] [IsLocalRing B] {ρ ρ' : GaloisRepAdic B} (h : ρ.IsEquiv ρ') :
    ρ'.IsEquiv ρ := ⟨h.some.symm⟩

theorem reflectedByInjective_conditionSubfunctor [Finite (ResidueField 𝒪)]
    (𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop)
    (h𝒟 : GaloisRep.IsDeformationCondition 𝒪 𝒟)
    (ρ₀ : (repnFunctor (Fin 2) Γℚ 𝒪).obj ProartinianCat.residueField)
    (hreflLift : ReflectedByInjective (Fin 2) (liftFunctor (Fin 2) Γℚ 𝒪 ρ₀)) :
    ReflectedByInjective (Fin 2) (GaloisRep.conditionSubfunctor 𝒪 𝒟 ρ₀) := by
  classical
  intro T A ι hι σ hσ
  obtain ⟨hlift, hD⟩ := hσ
  refine ⟨hreflLift ι hι hlift, ?_⟩
  intro C _ g ρC b hb

  haveI : DiscreteTopology C := discreteTopology_of_isArtinianRing C
  have hKopen : IsOpen ((RingHom.ker g.hom.toRingHom : Ideal T) : Set T) := by
    have : ((RingHom.ker g.hom.toRingHom : Ideal T) : Set T) = g.hom ⁻¹' {0} := by
      ext x; simp [RingHom.mem_ker]
    rw [this]
    exact (isOpen_discrete _).preimage g.hom.cont
  obtain ⟨J', hJ'⟩ := exists_openIdx_comap_le ι hι _ hKopen

  have hIopen : IsOpen ((J'.1.comap ι.hom.toRingHom : Ideal T) : Set T) := by
    have : ((J'.1.comap ι.hom.toRingHom : Ideal T) : Set T) = ι.hom ⁻¹' (J'.1 : Set A) := rfl
    rw [this]; exact J'.2.1.preimage ι.hom.cont
  have hIne : (J'.1.comap ι.hom.toRingHom : Ideal T) ≠ ⊤ := by
    intro h
    have h1 : (1 : T) ∈ J'.1.comap ι.hom.toRingHom := h ▸ Submodule.mem_top
    rw [Ideal.mem_comap, map_one] at h1
    exact J'.2.2 ((Ideal.eq_top_iff_one _).mpr h1)
  let IT : OpenIdx T := ⟨J'.1.comap ι.hom.toRingHom, hIopen, hIne⟩
  let qA : A ⟶ quotObj J' := quotMk J'
  let qT : T ⟶ quotObj IT := quotMk IT

  let ιbar : quotObj IT ⟶ quotObj J' := quotLiftHom IT (ι ≫ qA) (fun x hx => by
    show (qA).hom (ι.hom x) = 0
    rw [quotMk_apply]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_comap.mp hx))
  have hιbar_inj : Function.Injective ιbar.hom :=
    quotLiftHom_injective IT (ι ≫ qA) _ (fun x hx => by
      have hx' : (qA).hom (ι.hom x) = 0 := hx
      rw [quotMk_apply] at hx'
      exact Ideal.mem_comap.mpr (Ideal.Quotient.eq_zero_iff_mem.mp hx'))

  let gbar : quotObj IT ⟶ C := quotLiftHom IT g (fun x hx => (RingHom.mem_ker).mp (hJ' hx))
  have hcomm1 : qT ≫ ιbar = ι ≫ qA := quotMk_quotLiftHom IT _ _
  have hcomm2 : qT ≫ gbar = g := quotMk_quotLiftHom IT _ _

  have hpush1 : mapRepn (Fin 2) Γℚ 𝒪 qA (mapRepn (Fin 2) Γℚ 𝒪 ι σ) =
      mapRepn (Fin 2) Γℚ 𝒪 ιbar (mapRepn (Fin 2) Γℚ 𝒪 qT σ) := by
    simp only [mapRepn]
    rw [← types_comp_apply ((repnFunctor (Fin 2) Γℚ 𝒪).map ι) ((repnFunctor (Fin 2) Γℚ 𝒪).map qA),
      ← types_comp_apply ((repnFunctor (Fin 2) Γℚ 𝒪).map qT) ((repnFunctor (Fin 2) Γℚ 𝒪).map ιbar),
      ← Functor.map_comp, ← Functor.map_comp, hcomm1]
  have hpush2 : mapRepn (Fin 2) Γℚ 𝒪 gbar (mapRepn (Fin 2) Γℚ 𝒪 qT σ) = mapRepn (Fin 2) Γℚ 𝒪 g σ := by
    simp only [mapRepn]
    rw [← types_comp_apply ((repnFunctor (Fin 2) Γℚ 𝒪).map qT) ((repnFunctor (Fin 2) Γℚ 𝒪).map gbar),
      ← Functor.map_comp, hcomm2]

  have tA' := isArtinianTestAlgebra (𝒪 := 𝒪) (quotObj J')
  have tT' := isArtinianTestAlgebra (𝒪 := 𝒪) (quotObj IT)
  have tC := isArtinianTestAlgebra (𝒪 := 𝒪) C
  have hιloc : IsLocalHom ιbar.hom.toRingHom := isLocalHom_coe_hom ιbar
  have hgloc : IsLocalHom gbar.hom.toRingHom := isLocalHom_coe_hom gbar

  have hDA' : 𝒟 (stdRep (quotObj J') (mapRepn (Fin 2) Γℚ 𝒪 qA (mapRepn (Fin 2) Γℚ 𝒪 ι σ))) :=
    hD (quotObj J') qA _ (Pi.basisFun _ _) (toMatrix_stdRep _ _)
  rw [hpush1] at hDA'

  have e1 := isEquiv_baseChangeAlong_stdRep (quotObj IT) (quotObj J') ιbar hιloc (mapRepn (Fin 2) Γℚ 𝒪 qT σ)
  have hDbc : 𝒟 ((stdRep (quotObj IT) (mapRepn (Fin 2) Γℚ 𝒪 qT σ)).baseChangeAlong ιbar.hom.toRingHom hιloc) :=
    h𝒟.of_isEquiv tA' (isEquiv_symm e1) hDA'

  have hDT' : 𝒟 (stdRep (quotObj IT) (mapRepn (Fin 2) Γℚ 𝒪 qT σ)) :=
    h𝒟.of_baseChangeAlong_injective tT' tA' (ιbar.hom : quotObj IT →ₐ[𝒪] quotObj J') hιloc hιbar_inj hDbc

  have hDbc2 := h𝒟.baseChangeAlong tT' tC (gbar.hom : quotObj IT →ₐ[𝒪] C) hgloc hDT'
  have e2 := isEquiv_baseChangeAlong_stdRep (quotObj IT) C gbar hgloc (mapRepn (Fin 2) Γℚ 𝒪 qT σ)
  have hDstdC : 𝒟 (stdRep C (mapRepn (Fin 2) Γℚ 𝒪 g σ)) := by
    rw [← hpush2]; exact h𝒟.of_isEquiv tC e2 hDbc2

  exact h𝒟.of_isEquiv tC (isEquiv_symm (isEquiv_stdRep_of_basis C _ ρC b hb)) hDstdC

end GaloisRep.SolAuxG5
p2m_reactivate "P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation.ProartinianCat P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation.SubalgebraGL"
p2m_reactivate "P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation.ProartinianCat P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation.SubalgebraGL"

namespace GaloisRep
p2m_export "GaloisRep" "IsArtinianTestAlgebra IsDeformationCondition conditionLifts conditionSubfunctor"
namespace SolAuxG5
p2m_open "GaloisRep"

variable {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]

p2m_open "Deformation P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation Deformation.ProartinianCat P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation.ProartinianCat TensorProduct"

theorem isEquiv_baseChangeAlong_baseChangeAlong {A B C : Type} [CommRing A] [IsLocalRing A]
    [CommRing B] [IsLocalRing B] [CommRing C] [IsLocalRing C]
    (φ : A →+* B) (hφ : IsLocalHom φ) (ψ : B →+* C) (hψ : IsLocalHom ψ) (ρ : GaloisRepAdic A) :
    ((ρ.baseChangeAlong φ hφ).baseChangeAlong ψ hψ).IsEquiv
      (ρ.baseChangeAlong (ψ.comp φ) (RingHom.isLocalHom_comp ψ φ)) := by
  letI : Algebra A B := φ.toAlgebra
  letI : Algebra B C := ψ.toAlgebra
  letI : Algebra A C := (ψ.comp φ).toAlgebra
  haveI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  refine ⟨{ toLinearEquiv := TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C ρ.V,
            map_apply := fun σ => ?_ }⟩
  change ∀ x : C ⊗[B] (B ⊗[A] ρ.V),
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C ρ.V) (((ρ.ρ σ).baseChange B).baseChange C x) =
      (ρ.ρ σ).baseChange C ((TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C ρ.V) x)
  intro x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | tmul c y =>
    induction y using TensorProduct.induction_on with
    | zero => rw [tmul_zero, map_zero, map_zero, map_zero]
    | add y₁ y₂ h₁ h₂ => rw [tmul_add, map_add, map_add, h₁, h₂, map_add, map_add]
    | tmul b v =>
      rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
        TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
        TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, LinearMap.baseChange_tmul]

theorem finite_of_isArtinianRing [Finite (ResidueField 𝒪)] (B : ProartinianCat 𝒪) [IsArtinianRing B] :
    Finite B := by
  haveI : DiscreteTopology B := discreteTopology_of_isArtinianRing B
  haveI : Finite (B ⧸ (⊥ : Ideal B)) := IsProartinian.finite_quotient_of_isOpen (R := B) ⊥ (isOpen_discrete _)
  exact Finite.of_equiv _ (RingEquiv.quotientBot B).toEquiv

section FibreProduct

variable {K : Type} [Field K] [Algebra 𝒪 K]
variable (A B : Type) [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] [CommRing B] [IsLocalRing B] [Algebra 𝒪 B]
variable (f : A →ₐ[𝒪] K) (g : B →ₐ[𝒪] K)

def fibreProd : Subalgebra 𝒪 (A × B) where
  carrier := {x | f x.1 = g x.2}
  mul_mem' {x y} hx hy := by
    simp only [Set.mem_setOf_eq, Prod.fst_mul, Prod.snd_mul, map_mul] at *; rw [hx, hy]
  add_mem' {x y} hx hy := by
    simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, map_add] at *; rw [hx, hy]
  algebraMap_mem' o := by
    simp only [Set.mem_setOf_eq, Prod.algebraMap_apply, AlgHom.commutes]

variable {A B f g}

lemma mem_fibreProd {x : A × B} : x ∈ fibreProd A B f g ↔ f x.1 = g x.2 := Iff.rfl

def fibreProdFst : fibreProd A B f g →ₐ[𝒪] A := (AlgHom.fst 𝒪 A B).comp (fibreProd A B f g).val
def fibreProdSnd : fibreProd A B f g →ₐ[𝒪] B := (AlgHom.snd 𝒪 A B).comp (fibreProd A B f g).val

@[scoped simp] lemma fibreProdFst_apply (x : fibreProd A B f g) : fibreProdFst x = x.1.1 := rfl
@[scoped simp] lemma fibreProdSnd_apply (x : fibreProd A B f g) : fibreProdSnd x = x.1.2 := rfl

lemma fibreProd_comm : f.comp (fibreProdFst (f := f) (g := g)) = g.comp fibreProdSnd := by
  ext x; exact x.2

lemma fibreProd_injective :
    Function.Injective fun x : fibreProd A B f g => (fibreProdFst x, fibreProdSnd x) := by
  intro x y h
  simp only [fibreProdFst_apply, fibreProdSnd_apply, Prod.mk.injEq] at h
  exact Subtype.ext (Prod.ext h.1 h.2)

lemma fibreProd_surjective (a : A) (b : B) (h : f a = g b) :
    ∃ x : fibreProd A B f g, fibreProdFst x = a ∧ fibreProdSnd x = b :=
  ⟨⟨(a, b), h⟩, rfl, rfl⟩

theorem isUnit_fibreProd (hf : ∀ a : A, IsUnit a ↔ f a ≠ 0) (hg : ∀ b : B, IsUnit b ↔ g b ≠ 0)
    (x : fibreProd A B f g) (hx : f x.1.1 ≠ 0) : IsUnit x := by
  have hx2 : g x.1.2 ≠ 0 := x.2 ▸ hx
  obtain ⟨ua, hua⟩ := (hf _).mpr hx
  obtain ⟨ub, hub⟩ := (hg _).mpr hx2
  have ha : f ((ua⁻¹ : Aˣ) : A) = (f x.1.1)⁻¹ := by
    rw [← hua]; exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
  have hb : g ((ub⁻¹ : Bˣ) : B) = (g x.1.2)⁻¹ := by
    rw [← hub]; exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
  have hmem : (((ua⁻¹ : Aˣ) : A), ((ub⁻¹ : Bˣ) : B)) ∈ fibreProd A B f g := by
    show f _ = g _
    rw [ha, hb]; exact congrArg _ x.2
  have hx1 : x.1 = ((ua : A), (ub : B)) := Prod.ext hua.symm hub.symm
  refine ⟨⟨x, ⟨_, hmem⟩, ?_, ?_⟩, rfl⟩
  · apply Subtype.ext
    show x.1 * (((ua⁻¹ : Aˣ) : A), ((ub⁻¹ : Bˣ) : B)) = 1
    rw [hx1, Prod.mk_mul_mk, Units.mul_inv, Units.mul_inv]; rfl
  · apply Subtype.ext
    show (((ua⁻¹ : Aˣ) : A), ((ub⁻¹ : Bˣ) : B)) * x.1 = 1
    rw [hx1, Prod.mk_mul_mk, Units.inv_mul, Units.inv_mul]; rfl

theorem isLocalRing_fibreProd (hf : ∀ a : A, IsUnit a ↔ f a ≠ 0) (hg : ∀ b : B, IsUnit b ↔ g b ≠ 0) :
    IsLocalRing (fibreProd A B f g) := by
  haveI : Nontrivial (fibreProd A B f g) :=
    ⟨⟨0, 1, fun h => zero_ne_one (congrArg (fun x : fibreProd A B f g => x.1.1) h)⟩⟩
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  by_cases hx : f x.1.1 = 0
  · right
    apply isUnit_fibreProd hf hg
    show f (1 - x.1.1) ≠ 0
    rw [map_sub, map_one, hx, sub_zero]; exact one_ne_zero
  · left; exact isUnit_fibreProd hf hg x hx

theorem isUnit_fibreProd_iff (hf : ∀ a : A, IsUnit a ↔ f a ≠ 0) (hg : ∀ b : B, IsUnit b ↔ g b ≠ 0)
    (x : fibreProd A B f g) : IsUnit x ↔ f x.1.1 ≠ 0 :=
  ⟨fun h h0 => by
    have := (h.map fibreProdFst)
    rw [fibreProdFst_apply, hf] at this
    exact this h0, isUnit_fibreProd hf hg x⟩

end FibreProduct
p2m_reactivate "P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation.ProartinianCat P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation.SubalgebraGL"

end GaloisRep.SolAuxG5
p2m_reactivate "P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation.ProartinianCat P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation.SubalgebraGL P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.GaloisRep P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.GaloisRep.SolAuxG5"
p2m_reactivate "P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation.ProartinianCat P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation.SubalgebraGL P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.GaloisRep"

namespace GaloisRep
p2m_export "GaloisRep" "IsArtinianTestAlgebra IsDeformationCondition conditionLifts conditionSubfunctor"
namespace SolAuxG5
p2m_open "GaloisRep"

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

variable {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]

p2m_open "Deformation P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation Deformation.ProartinianCat P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation.ProartinianCat"

theorem isEquiv_trans {B : Type} [CommRing B] [IsLocalRing B] {ρ ρ' ρ'' : GaloisRepAdic B}
    (h : ρ.IsEquiv ρ') (h' : ρ'.IsEquiv ρ'') : ρ.IsEquiv ρ'' := ⟨h.some.trans h'.some⟩

theorem isEquiv_baseChangeAlong_congr {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    {φ ψ : A →+* B} (h : φ = ψ) (hφ : IsLocalHom φ) (hψ : IsLocalHom ψ) (ρ : GaloisRepAdic A) :
    (ρ.baseChangeAlong φ hφ).IsEquiv (ρ.baseChangeAlong ψ hψ) := by
  subst h; exact ⟨GaloisRepAdic.Equiv.refl _⟩

theorem isArtinianTestAlgebra_residueField :
    GaloisRep.IsArtinianTestAlgebra 𝒪 (ResidueField 𝒪) where
  isLocalHom := by
    refine ⟨fun o ho => ?_⟩
    by_contra h
    have : algebraMap 𝒪 (ResidueField 𝒪) o = 0 := by
      rw [ResidueField.algebraMap_eq, residue_eq_zero_iff]; exact (mem_maximalIdeal o).mpr h
    exact ho.ne_zero this
  residue_surjective := by
    intro y
    obtain ⟨x, rfl⟩ := residue_surjective y
    obtain ⟨o, rfl⟩ := residue_surjective x
    exact ⟨o, rfl⟩
  isArtinian := inferInstance

section FP

variable {K : Type} [Field K] [Algebra 𝒪 K]
variable {A B : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] [CommRing B] [IsLocalRing B] [Algebra 𝒪 B]
variable {f : A →ₐ[𝒪] K} {g : B →ₐ[𝒪] K}

theorem isArtinianTestAlgebra_fibreProd
    (hK : ∀ o : 𝒪, algebraMap 𝒪 K o ≠ 0 → IsUnit o) (hKs : Function.Surjective (algebraMap 𝒪 K))
    (hf : ∀ a : A, IsUnit a ↔ f a ≠ 0) (hg : ∀ b : B, IsUnit b ↔ g b ≠ 0) [Finite A] [Finite B]
    [hP : IsLocalRing (fibreProd A B f g)] :
    GaloisRep.IsArtinianTestAlgebra 𝒪 (fibreProd A B f g) where
  isLocalHom := by
    refine ⟨fun o ho => ?_⟩
    have h1 : f (algebraMap 𝒪 (fibreProd A B f g) o).1.1 ≠ 0 := (isUnit_fibreProd_iff hf hg _).mp ho
    have h2 : f (algebraMap 𝒪 (fibreProd A B f g) o).1.1 = algebraMap 𝒪 K o := by
      show f (algebraMap 𝒪 A o) = _
      rw [AlgHom.commutes]
    rw [h2] at h1
    exact hK o h1
  residue_surjective := by
    intro y
    obtain ⟨x, rfl⟩ := residue_surjective y
    obtain ⟨o, ho⟩ := hKs (f x.1.1)
    refine ⟨o, ?_⟩
    show residue _ (algebraMap 𝒪 _ o) = residue _ x
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff,
      isUnit_fibreProd_iff hf hg, not_not]
    show f ((algebraMap 𝒪 A o) - x.1.1) = 0
    rw [map_sub, AlgHom.commutes, ho, sub_self]
  isArtinian := by
    haveI : Finite (fibreProd A B f g) := inferInstance
    infer_instance

end FP
p2m_reactivate "P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation.ProartinianCat P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation.SubalgebraGL P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.GaloisRep P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.GaloisRep.SolAuxG5"

theorem isUnit_iff_toResidueField_ne_zero' (X : ProartinianCat 𝒪) (a : X) :
    IsUnit a ↔ (toResidueField X).hom.toAlgHom a ≠ 0 := by
  rw [← not_iff_not, not_not]
  show ¬ IsUnit a ↔ (toResidueField X).hom a = 0
  rw [← mem_nonunits_iff, ← mem_maximalIdeal, ← ker_toResidueField X, RingHom.mem_ker]

theorem D_stdRep_of_jointly_injective [Finite (ResidueField 𝒪)]
    (𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop)
    (h𝒟 : GaloisRep.IsDeformationCondition 𝒪 𝒟)
    {ι : Type} (C : ι → ProartinianCat 𝒪) [∀ i, IsArtinianRing (C i)] (S : Finset ι) :
    ∀ (Q : ProartinianCat 𝒪) [IsArtinianRing Q] (τ : Γℚ →ₜ* GL (Fin 2) Q)
      (g : ∀ i : S, Q ⟶ C i)
      (hinj : ∀ y : Q, (∀ i : S, (g i).hom y = 0) → y = 0)
      (hD : ∀ i : S, 𝒟 (stdRep (C i) (mapRepn (Fin 2) Γℚ 𝒪 (g i) τ))), 𝒟 (stdRep Q τ) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro Q _ τ g hinj hD
    exact absurd (hinj 1 (fun i => (Finset.notMem_empty _ i.2).elim)) one_ne_zero
  | @insert i₀ S' hi₀ IH =>
    intro Q _ τ g hinj hD

    have tQ := isArtinianTestAlgebra (𝒪 := 𝒪) Q
    have hingeD : ∀ i : (insert i₀ S' : Finset ι),
        𝒟 ((stdRep Q τ).baseChangeAlong (g i).hom.toRingHom (isLocalHom_coe_hom (g i))) := fun i =>
      h𝒟.of_isEquiv (isArtinianTestAlgebra (𝒪 := 𝒪) (C i))
        (isEquiv_symm (isEquiv_baseChangeAlong_stdRep Q (C i) (g i) (isLocalHom_coe_hom (g i)) τ)) (hD i)
    by_cases hS' : S' = ∅
    ·
      subst hS'
      have hinj₀ : Function.Injective (g ⟨i₀, Finset.mem_insert_self _ _⟩).hom := by
        rw [injective_iff_map_eq_zero]
        intro y hy
        refine hinj y fun i => ?_
        have hi' := i.2
        rw [Finset.mem_insert] at hi'
        rcases hi' with h | h
        · have : i = ⟨i₀, Finset.mem_insert_self _ _⟩ := Subtype.ext h
          rw [this]; exact hy
        · exact absurd h (Finset.notMem_empty _)
      exact h𝒟.of_baseChangeAlong_injective tQ (isArtinianTestAlgebra (𝒪 := 𝒪) (C i₀))
        ((g ⟨i₀, Finset.mem_insert_self _ _⟩).hom : Q →ₐ[𝒪] C i₀) (isLocalHom_coe_hom _) hinj₀
        (hingeD ⟨i₀, Finset.mem_insert_self _ _⟩)
    ·
      obtain ⟨i₁, hi₁⟩ := Finset.nonempty_iff_ne_empty.mpr hS'
      haveI : DiscreteTopology Q := discreteTopology_of_isArtinianRing Q
      let g' : ∀ i : S', Q ⟶ C i := fun i => g ⟨i, Finset.mem_insert_of_mem i.2⟩
      let K' : Ideal Q := ⨅ i : S', RingHom.ker (g' i).hom.toRingHom
      have hK'open : IsOpen ((K' : Ideal Q) : Set Q) := isOpen_discrete _
      have hK'ne : K' ≠ ⊤ := by
        intro h
        have h1 : (1 : Q) ∈ K' := h ▸ Submodule.mem_top
        have : (1 : Q) ∈ RingHom.ker (g' ⟨i₁, hi₁⟩).hom.toRingHom := (Submodule.mem_iInf _).mp h1 ⟨i₁, hi₁⟩
        rw [RingHom.mem_ker, map_one] at this
        exact one_ne_zero this
      let IK : OpenIdx Q := ⟨K', hK'open, hK'ne⟩
      let q' : Q ⟶ quotObj IK := quotMk IK
      have hK'le : ∀ i : S', ∀ x ∈ IK.1, (g' i).hom x = 0 := fun i x hx =>
        (RingHom.mem_ker).mp ((Submodule.mem_iInf _).mp hx i)
      let gbar : ∀ i : S', quotObj IK ⟶ C i := fun i => quotLiftHom IK (g' i) (hK'le i)
      have hgbar : ∀ i : S', q' ≫ gbar i = g' i := fun i => quotMk_quotLiftHom IK _ _

      have hinj' : ∀ y : quotObj IK, (∀ i : S', (gbar i).hom y = 0) → y = 0 := by
        intro y hy
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective (I := IK.1) y
        refine Ideal.Quotient.eq_zero_iff_mem.mpr ((Submodule.mem_iInf _).mpr fun i => ?_)
        exact (RingHom.mem_ker).mpr (hy i)
      have hD' : ∀ i : S', 𝒟 (stdRep (C i) (mapRepn (Fin 2) Γℚ 𝒪 (gbar i) (mapRepn (Fin 2) Γℚ 𝒪 q' τ))) := by
        intro i
        have : mapRepn (Fin 2) Γℚ 𝒪 (gbar i) (mapRepn (Fin 2) Γℚ 𝒪 q' τ) = mapRepn (Fin 2) Γℚ 𝒪 (g' i) τ := by
          simp only [mapRepn]
          rw [← types_comp_apply ((repnFunctor (Fin 2) Γℚ 𝒪).map q') ((repnFunctor (Fin 2) Γℚ 𝒪).map (gbar i)),
            ← Functor.map_comp, hgbar]
        rw [this]; exact hD ⟨i, Finset.mem_insert_of_mem i.2⟩
      have hDQ' : 𝒟 (stdRep (quotObj IK) (mapRepn (Fin 2) Γℚ 𝒪 q' τ)) := IH (quotObj IK) _ gbar hinj' hD'

      let g₀ : Q ⟶ C i₀ := g ⟨i₀, Finset.mem_insert_self _ _⟩
      let fA : C i₀ →ₐ[𝒪] (residueField (𝓞 := 𝒪)) := (toResidueField (C i₀)).hom.toAlgHom
      let fB : quotObj IK →ₐ[𝒪] (residueField (𝓞 := 𝒪)) := (toResidueField (quotObj IK)).hom.toAlgHom
      have hfA : ∀ a : C i₀, IsUnit a ↔ fA a ≠ 0 := isUnit_iff_toResidueField_ne_zero' (C i₀)
      have hfB : ∀ b : quotObj IK, IsUnit b ↔ fB b ≠ 0 := isUnit_iff_toResidueField_ne_zero' (quotObj IK)
      haveI : Finite (C i₀) := finite_of_isArtinianRing (C i₀)
      haveI : Finite (quotObj IK) := finite_of_isArtinianRing (quotObj IK)
      haveI hPloc : IsLocalRing (fibreProd (C i₀ : Type) (quotObj IK : Type) fA fB) := isLocalRing_fibreProd hfA hfB
      have hKloc : ∀ o : 𝒪, algebraMap 𝒪 (residueField (𝓞 := 𝒪)) o ≠ 0 → IsUnit o := by
        intro o ho
        by_contra hu
        apply ho
        show residue 𝒪 o = 0
        exact (residue_eq_zero_iff o).mpr ((mem_maximalIdeal o).mpr hu)
      have hKsurj : Function.Surjective (algebraMap 𝒪 (residueField (𝓞 := 𝒪))) := by
        show Function.Surjective (residue 𝒪); exact residue_surjective
      have tP := isArtinianTestAlgebra_fibreProd (𝒪 := 𝒪) hKloc hKsurj hfA hfB
      have tA := isArtinianTestAlgebra (𝒪 := 𝒪) (C i₀)
      have tB := isArtinianTestAlgebra (𝒪 := 𝒪) (quotObj IK)

      have hcompat : ∀ y : Q, fA (g₀.hom y) = fB (q'.hom y) := by
        intro y
        have h1 : g₀ ≫ toResidueField (C i₀) = toResidueField Q := Subsingleton.elim _ _
        have h2 : q' ≫ toResidueField (quotObj IK) = toResidueField Q := Subsingleton.elim _ _
        have e1 : (toResidueField (C i₀)).hom (g₀.hom y) = (toResidueField Q).hom y :=
          congrArg (fun φ : Q ⟶ residueField => φ.hom y) h1
        have e2 : (toResidueField (quotObj IK)).hom (q'.hom y) = (toResidueField Q).hom y :=
          congrArg (fun φ : Q ⟶ residueField => φ.hom y) h2
        exact e1.trans e2.symm
      let ιP : Q →ₐ[𝒪] fibreProd (C i₀ : Type) (quotObj IK : Type) fA fB :=
        AlgHom.codRestrict (((g₀.hom : Q →ₐ[𝒪] C i₀)).prod (q'.hom : Q →ₐ[𝒪] quotObj IK))
          (fibreProd (C i₀ : Type) (quotObj IK : Type) fA fB) (fun y => hcompat y)
      have hιP_fst : (fibreProdFst (f := fA) (g := fB)).comp ιP = (g₀.hom : Q →ₐ[𝒪] C i₀) := by
        ext y; rfl
      have hιP_snd : (fibreProdSnd (f := fA) (g := fB)).comp ιP = (q'.hom : Q →ₐ[𝒪] quotObj IK) := by
        ext y; rfl
      have hιP_inj : Function.Injective ιP := by
        rw [injective_iff_map_eq_zero]
        intro y hy
        have hy1 : g₀.hom y = 0 := congrArg (fun x => x.1.1) hy
        have hy2 : q'.hom y = 0 := congrArg (fun x => x.1.2) hy
        refine hinj y fun i => ?_
        rcases Finset.mem_insert.mp i.2 with h | h
        · have : i = ⟨i₀, Finset.mem_insert_self _ _⟩ := Subtype.ext h
          rw [this]; exact hy1
        · have hyK : y ∈ IK.1 := Ideal.Quotient.eq_zero_iff_mem.mp (by rw [← quotMk_apply]; exact hy2)
          exact hK'le ⟨i, h⟩ y hyK
      haveI := tP.isLocalHom
      have hιP_loc : IsLocalHom (ιP : Q →+* fibreProd (C i₀ : Type) (quotObj IK : Type) fA fB) :=
        isLocalHom_of_algHom_of_residue_surjective (𝒪 := 𝒪) tP.residue_surjective ιP

      let ρP := (stdRep Q τ).baseChangeAlong (ιP : Q →+* fibreProd (C i₀ : Type) (quotObj IK : Type) fA fB) hιP_loc
      have hpA := isLocalHom_of_algHom_of_residue_surjective (𝒪 := 𝒪) tA.residue_surjective (fibreProdFst (f := fA) (g := fB))
      have hpB := isLocalHom_of_algHom_of_residue_surjective (𝒪 := 𝒪) tB.residue_surjective (fibreProdSnd (f := fA) (g := fB))
      have hDA : 𝒟 (ρP.baseChangeAlong (fibreProdFst (f := fA) (g := fB) : fibreProd (C i₀ : Type) (quotObj IK : Type) fA fB →+* C i₀) hpA) := by
        have e1 := isEquiv_baseChangeAlong_baseChangeAlong (ιP : Q →+* fibreProd (C i₀ : Type) (quotObj IK : Type) fA fB) hιP_loc
          (fibreProdFst (f := fA) (g := fB) : fibreProd (C i₀ : Type) (quotObj IK : Type) fA fB →+* C i₀) hpA (stdRep Q τ)
        have hcomp : ((fibreProdFst (f := fA) (g := fB) : fibreProd (C i₀ : Type) (quotObj IK : Type) fA fB →+* C i₀).comp (ιP : Q →+* fibreProd (C i₀ : Type) (quotObj IK : Type) fA fB)) =
            g₀.hom.toRingHom := by
          ext y; rfl
        have e2 := isEquiv_baseChangeAlong_congr hcomp (RingHom.isLocalHom_comp _ _) (isLocalHom_coe_hom g₀) (stdRep Q τ)
        exact h𝒟.of_isEquiv tA (isEquiv_symm (isEquiv_trans e1 e2)) (hingeD ⟨i₀, Finset.mem_insert_self _ _⟩)
      have hDB : 𝒟 (ρP.baseChangeAlong (fibreProdSnd (f := fA) (g := fB) : fibreProd (C i₀ : Type) (quotObj IK : Type) fA fB →+* quotObj IK) hpB) := by
        have e1 := isEquiv_baseChangeAlong_baseChangeAlong (ιP : Q →+* fibreProd (C i₀ : Type) (quotObj IK : Type) fA fB) hιP_loc
          (fibreProdSnd (f := fA) (g := fB) : fibreProd (C i₀ : Type) (quotObj IK : Type) fA fB →+* quotObj IK) hpB (stdRep Q τ)
        have hcomp : ((fibreProdSnd (f := fA) (g := fB) : fibreProd (C i₀ : Type) (quotObj IK : Type) fA fB →+* quotObj IK).comp
            (ιP : Q →+* fibreProd (C i₀ : Type) (quotObj IK : Type) fA fB)) = q'.hom.toRingHom := by
          ext y; rfl
        have e2 := isEquiv_baseChangeAlong_congr hcomp (RingHom.isLocalHom_comp _ _) (isLocalHom_coe_hom q') (stdRep Q τ)
        have e3 := isEquiv_baseChangeAlong_stdRep Q (quotObj IK) q' (isLocalHom_coe_hom q') τ
        exact h𝒟.of_isEquiv tB (isEquiv_symm (isEquiv_trans (isEquiv_trans e1 e2) e3)) hDQ'

      have hDP : 𝒟 ρP :=
        h𝒟.of_fibreProduct tA tB (isArtinianTestAlgebra (𝒪 := 𝒪) residueField) tP fA fB
          (fibreProdFst (f := fA) (g := fB)) (fibreProdSnd (f := fA) (g := fB)) hpA hpB
          fibreProd_comm fibreProd_injective (fun a b h => fibreProd_surjective a b h) hDA hDB
      exact h𝒟.of_baseChangeAlong_injective tQ tP ιP hιP_loc hιP_inj hDP

end GaloisRep.SolAuxG5
p2m_reactivate "P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation.ProartinianCat P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation.SubalgebraGL P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.GaloisRep P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.GaloisRep.SolAuxG5"
p2m_reactivate "P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation.ProartinianCat P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation.SubalgebraGL P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.GaloisRep P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.GaloisRep.SolAuxG5"

namespace GaloisRep
p2m_export "GaloisRep" "IsArtinianTestAlgebra IsDeformationCondition conditionLifts conditionSubfunctor"
namespace SolAuxG5
p2m_open "GaloisRep"

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

variable {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] [Finite (ResidueField 𝒪)]

p2m_open "CategoryTheory CategoryTheory.Limits Deformation P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation Deformation.ProartinianCat P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation.ProartinianCat"

theorem mem_conditionLifts_limitObj'
    (𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop)
    (h𝒟 : GaloisRep.IsDeformationCondition 𝒪 𝒟)
    (ρ₀ : (repnFunctor (Fin 2) Γℚ 𝒪).obj ProartinianCat.residueField)
    {J : Type} [SmallCategory J] [Nonempty J] (D : J ⥤ ProartinianCat 𝒪)
    (x : Γℚ →ₜ* GL (Fin 2) (limitObj D))
    (hx : x ∈ (liftFunctor (Fin 2) Γℚ 𝒪 ρ₀).obj (limitObj D))
    (hproj : ∀ j, mapRepn (Fin 2) Γℚ 𝒪 (limitProj D j) x ∈ GaloisRep.conditionLifts 𝒪 𝒟 ρ₀ (D.obj j)) :
    x ∈ GaloisRep.conditionLifts 𝒪 𝒟 ρ₀ (limitObj D) := by
  classical
  refine ⟨hx, ?_⟩
  intro B _ f ρB b hb
  haveI : DiscreteTopology B := discreteTopology_of_isArtinianRing B

  set K₀ : Ideal (limitObj D) := RingHom.ker f.hom.toRingHom with hK₀
  have hK₀open : IsOpen ((K₀ : Ideal (limitObj D)) : Set (limitObj D)) := by
    have : ((K₀ : Ideal (limitObj D)) : Set (limitObj D)) = f.hom ⁻¹' {0} := by
      ext y; simp [hK₀, RingHom.mem_ker]
    rw [this]; exact (isOpen_discrete _).preimage f.hom.cont
  have hmem : ((K₀ : Ideal (limitObj D)) : Set (limitObj D)) ∈ nhds (0 : limitObj D) := hK₀open.mem_nhds K₀.zero_mem
  obtain ⟨U, hU, hUsub⟩ := (mem_nhds_induced (Subtype.val : limitSubalgebra D → ∀ j, D.obj j) 0 _).mp hmem
  have hU0 : U ∈ nhds (0 : ∀ j, D.obj j) := hU
  rw [nhds_pi] at hU0
  obtain ⟨Sset, hSfin, t, ht, hpi⟩ := Filter.mem_pi.mp hU0

  have hI : ∀ j, ∃ I : OpenIdx (D.obj j), ((I.1 : Ideal (D.obj j)) : Set (D.obj j)) ⊆ t j := by
    intro j
    obtain ⟨I', hI'open, hI'sub⟩ := (IsLinearTopology.hasBasis_open_ideal.mem_iff).mp (ht j)
    refine ⟨⟨I' ⊓ maximalIdeal _, ?_, ?_⟩, fun y hy => hI'sub hy.1⟩
    · have : ((I' ⊓ maximalIdeal (D.obj j) : Ideal (D.obj j)) : Set (D.obj j)) =
          (I' : Set (D.obj j)) ∩ (maximalIdeal (D.obj j) : Set (D.obj j)) := rfl
      rw [this]; exact hI'open.inter isOpen_maximalIdeal_of_isProartinian
    · exact fun h => (maximalIdeal.isMaximal (D.obj j)).ne_top (top_le_iff.mp (h ▸ inf_le_right))
  choose I hIt using hI
  let S : Finset J := hSfin.toFinset

  let K : Ideal (limitObj D) := ⨅ j : S, (I j).1.comap (limitProj D j).hom.toRingHom
  have hKle : ∀ y ∈ K, f.hom y = 0 := by
    intro y hy
    have hyU : ((show limitSubalgebra D from y) : ∀ j, D.obj j) ∈ U := by
      refine hpi fun j hj => hIt j ?_
      have := (Submodule.mem_iInf _).mp hy ⟨j, hSfin.mem_toFinset.mpr hj⟩
      exact Ideal.mem_comap.mp this
    exact (RingHom.mem_ker).mp (hUsub hyU)
  have hKopen : IsOpen ((K : Ideal (limitObj D)) : Set (limitObj D)) := by
    have : ((K : Ideal (limitObj D)) : Set (limitObj D)) =
        ⋂ j : S, (limitProj D j).hom ⁻¹' ((I j).1 : Set (D.obj j)) := by
      ext y; simp [K, Submodule.mem_iInf, Ideal.mem_comap]
    rw [this]
    exact isOpen_iInter_of_finite fun j => (I j).2.1.preimage (limitProj D j).hom.cont
  have hKne : K ≠ ⊤ := by
    intro h
    have : f.hom 1 = 0 := hKle 1 (h ▸ Submodule.mem_top)
    rw [map_one] at this
    exact one_ne_zero this
  let IK : OpenIdx (limitObj D) := ⟨K, hKopen, hKne⟩
  let qK : limitObj D ⟶ quotObj IK := quotMk IK
  let fbar : quotObj IK ⟶ B := quotLiftHom IK f hKle
  have hfbar : qK ≫ fbar = f := quotMk_quotLiftHom IK _ _

  let C : J → ProartinianCat 𝒪 := fun j => quotObj (I j)
  have hgker : ∀ j : S, ∀ y ∈ IK.1, (limitProj D j ≫ quotMk (I j)).hom y = 0 := by
    intro j y hy
    show (quotMk (I j)).hom ((limitProj D j).hom y) = 0
    rw [quotMk_apply]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_comap.mp ((Submodule.mem_iInf _).mp hy j))
  let g : ∀ j : S, quotObj IK ⟶ C j := fun j => quotLiftHom IK (limitProj D j ≫ quotMk (I j)) (hgker j)
  have hg : ∀ j : S, qK ≫ g j = limitProj D j ≫ quotMk (I j) := fun j => quotMk_quotLiftHom IK _ _
  have hinj : ∀ y : quotObj IK, (∀ j : S, (g j).hom y = 0) → y = 0 := by
    intro y hy
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective (I := IK.1) y
    refine Ideal.Quotient.eq_zero_iff_mem.mpr ((Submodule.mem_iInf _).mpr fun j => Ideal.mem_comap.mpr ?_)
    have h1 : (quotMk (I j)).hom ((limitProj D j).hom z) = 0 := hy j
    rw [quotMk_apply] at h1
    exact Ideal.Quotient.eq_zero_iff_mem.mp h1
  have hD : ∀ j : S, 𝒟 (stdRep (C j) (mapRepn (Fin 2) Γℚ 𝒪 (g j) (mapRepn (Fin 2) Γℚ 𝒪 qK x))) := by
    intro j
    have : mapRepn (Fin 2) Γℚ 𝒪 (g j) (mapRepn (Fin 2) Γℚ 𝒪 qK x) =
        mapRepn (Fin 2) Γℚ 𝒪 (quotMk (I j)) (mapRepn (Fin 2) Γℚ 𝒪 (limitProj D j) x) := by
      simp only [mapRepn]
      rw [← types_comp_apply ((repnFunctor (Fin 2) Γℚ 𝒪).map qK) ((repnFunctor (Fin 2) Γℚ 𝒪).map (g j)),
        ← Functor.map_comp, hg,
        ← types_comp_apply ((repnFunctor (Fin 2) Γℚ 𝒪).map (limitProj D j)) ((repnFunctor (Fin 2) Γℚ 𝒪).map (quotMk (I j))),
        ← Functor.map_comp]
    rw [this]
    exact (hproj j).2 (C j) (quotMk (I j)) _ (Pi.basisFun _ _) (toMatrix_stdRep _ _)

  have hDL' : 𝒟 (stdRep (quotObj IK) (mapRepn (Fin 2) Γℚ 𝒪 qK x)) :=
    D_stdRep_of_jointly_injective 𝒟 h𝒟 C S (quotObj IK) (mapRepn (Fin 2) Γℚ 𝒪 qK x) g hinj hD

  have tL' := isArtinianTestAlgebra (𝒪 := 𝒪) (quotObj IK)
  have tB := isArtinianTestAlgebra (𝒪 := 𝒪) B
  have hfloc : IsLocalHom fbar.hom.toRingHom := isLocalHom_coe_hom fbar
  have hDbc := h𝒟.baseChangeAlong tL' tB (fbar.hom : quotObj IK →ₐ[𝒪] B) hfloc hDL'
  have e := isEquiv_baseChangeAlong_stdRep (quotObj IK) B fbar hfloc (mapRepn (Fin 2) Γℚ 𝒪 qK x)
  have hpush : mapRepn (Fin 2) Γℚ 𝒪 fbar (mapRepn (Fin 2) Γℚ 𝒪 qK x) = mapRepn (Fin 2) Γℚ 𝒪 f x := by
    simp only [mapRepn]
    rw [← types_comp_apply ((repnFunctor (Fin 2) Γℚ 𝒪).map qK) ((repnFunctor (Fin 2) Γℚ 𝒪).map fbar),
      ← Functor.map_comp, hfbar]
  have hDstdB : 𝒟 (stdRep B (mapRepn (Fin 2) Γℚ 𝒪 f x)) := by
    rw [← hpush]; exact h𝒟.of_isEquiv tB e hDbc
  exact h𝒟.of_isEquiv tB (isEquiv_symm (isEquiv_stdRep_of_basis B _ ρB b hb)) hDstdB

end GaloisRep.SolAuxG5
p2m_reactivate "P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation.ProartinianCat P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation.SubalgebraGL P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.GaloisRep P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.GaloisRep.SolAuxG5"
p2m_reactivate "P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation.ProartinianCat P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation.SubalgebraGL P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.GaloisRep P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.GaloisRep.SolAuxG5"

namespace GaloisRep
p2m_export "GaloisRep" "IsArtinianTestAlgebra IsDeformationCondition conditionLifts conditionSubfunctor"
namespace SolAuxG5d
p2m_open "GaloisRep"

p2m_open "CategoryTheory CategoryTheory.Limits IsLocalRing Deformation P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation Deformation.ProartinianCat P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation.ProartinianCat P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.GaloisRep.SolAuxG5"

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

variable {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] [Finite (ResidueField 𝒪)]
variable (𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop)
variable (ρ₀ : (repnFunctor (Fin 2) Γℚ 𝒪).obj ProartinianCat.residueField)

theorem mem_conditionLifts_limitObj (h𝒟 : GaloisRep.IsDeformationCondition 𝒪 𝒟)
    (h₀ : ρ₀ ∈ GaloisRep.conditionLifts 𝒪 𝒟 ρ₀ ProartinianCat.residueField)
    {J : Type} [SmallCategory J] [Nonempty J] (D : J ⥤ ProartinianCat 𝒪)
    (x : Γℚ →ₜ* GL (Fin 2) (limitObj D))
    (hx : x ∈ (liftFunctor (Fin 2) Γℚ 𝒪 ρ₀).obj (limitObj D))
    (hproj : ∀ j, mapRepn (Fin 2) Γℚ 𝒪 (limitProj D j) x ∈ GaloisRep.conditionLifts 𝒪 𝒟 ρ₀ (D.obj j)) :
    x ∈ GaloisRep.conditionLifts 𝒪 𝒟 ρ₀ (limitObj D) :=
  GaloisRep.SolAuxG5.mem_conditionLifts_limitObj' 𝒟 h𝒟 ρ₀ D x hx hproj

theorem preservesLimit_conditionSubfunctor (h𝒟 : GaloisRep.IsDeformationCondition 𝒪 𝒟)
    (h₀ : ρ₀ ∈ GaloisRep.conditionLifts 𝒪 𝒟 ρ₀ ProartinianCat.residueField)
    {J : Type} [SmallCategory J] [Nonempty J] (D : J ⥤ ProartinianCat 𝒪) :
    PreservesLimit D (GaloisRep.conditionSubfunctor 𝒪 𝒟 ρ₀).toFunctor := by
  apply preservesLimit_of_preserves_limit_cone (limitConeIsLimit D)
  refine ((Types.isLimit_iff _).mpr ?_).some
  rintro s hs

  have hcompat : ∀ (i j : J) (f : i ⟶ j),
      (repnFunctor (Fin 2) Γℚ 𝒪).map (D.map f) (s i).1 = (s j).1 := fun i j f =>
    congrArg Subtype.val (hs f)
  have hlift : ∀ j : J, (repnFunctor (Fin 2) Γℚ 𝒪).map (toResidueField (D.obj j)) (s j).1 = ρ₀ :=
    fun j => (mem_liftFunctor_obj_iff Γℚ 𝒪 ρ₀ (s j).1).mp (s j).2.1
  have hres : ∀ i j : J,
      (repnFunctor (Fin 2) Γℚ 𝒪).map (toResidueField (D.obj i)) (s i).1 =
      (repnFunctor (Fin 2) Γℚ 𝒪).map (toResidueField (D.obj j)) (s j).1 := fun i j =>
    (hlift i).trans (hlift j).symm
  obtain ⟨ρ', hρ', huniq⟩ := existsUnique_repnGlueFamily Γℚ 𝒪 D (fun j => (s j).1) hcompat hres
  have hρ'lift : ρ' ∈ (liftFunctor (Fin 2) Γℚ 𝒪 ρ₀).obj (limitObj D) := by
    refine (mem_liftFunctor_obj_iff Γℚ 𝒪 ρ₀ ρ').mpr ?_
    have hcomp : toResidueField (limitObj D) =
        limitProj D (Classical.arbitrary J) ≫ toResidueField (D.obj (Classical.arbitrary J)) :=
      Subsingleton.elim _ _
    rw [hcomp, FunctorToTypes.map_comp_apply, hρ' (Classical.arbitrary J), hlift (Classical.arbitrary J)]
  have hρ'cond : ρ' ∈ GaloisRep.conditionLifts 𝒪 𝒟 ρ₀ (limitObj D) := by
    refine mem_conditionLifts_limitObj 𝒟 ρ₀ h𝒟 h₀ D ρ' hρ'lift fun j => ?_
    have : mapRepn (Fin 2) Γℚ 𝒪 (limitProj D j) ρ' = (s j).1 := hρ' j
    rw [this]; exact (s j).2
  refine ⟨⟨ρ', hρ'cond⟩, fun j => Subtype.ext (hρ' j), ?_⟩
  rintro ⟨ρ'', hρ''mem⟩ hρ''
  exact Subtype.ext (huniq ρ'' fun j => congrArg Subtype.val (hρ'' j))

noncomputable def uniqueObjResidueField
    (h₀ : ρ₀ ∈ GaloisRep.conditionLifts 𝒪 𝒟 ρ₀ ProartinianCat.residueField) :
    Unique ((GaloisRep.conditionSubfunctor 𝒪 𝒟 ρ₀).toFunctor.obj ProartinianCat.residueField) where
  default := ⟨ρ₀, h₀⟩
  uniq x := by
    refine Subtype.ext ?_
    have hx := (mem_liftFunctor_obj_iff Γℚ 𝒪 ρ₀ x.1).mp x.2.1
    rw [Subsingleton.elim (toResidueField (residueField (𝓞 := 𝒪))) (𝟙 _)] at hx
    exact (FunctorToTypes.map_id_apply _ _).symm.trans hx

theorem preservesLimit_empty_conditionSubfunctor
    (h₀ : ρ₀ ∈ GaloisRep.conditionLifts 𝒪 𝒟 ρ₀ ProartinianCat.residueField) :
    PreservesLimit (Functor.empty.{0} (ProartinianCat 𝒪)) (GaloisRep.conditionSubfunctor 𝒪 𝒟 ρ₀).toFunctor := by
  apply preservesLimit_of_preserves_limit_cone (isTerminalResidueField (𝓞 := 𝒪))
  haveI := uniqueObjResidueField 𝒟 ρ₀ h₀
  exact isLimitChangeEmptyCone _
    ((Types.isTerminalEquivUnique _).symm (uniqueObjResidueField 𝒟 ρ₀ h₀)) _ (Iso.refl _)

theorem preservesLimitsOfShape_conditionSubfunctor (h𝒟 : GaloisRep.IsDeformationCondition 𝒪 𝒟)
    (h₀ : ρ₀ ∈ GaloisRep.conditionLifts 𝒪 𝒟 ρ₀ ProartinianCat.residueField)
    (J : Type) [SmallCategory J] :
    PreservesLimitsOfShape J (GaloisRep.conditionSubfunctor 𝒪 𝒟 ρ₀).toFunctor := by
  rcases isEmpty_or_nonempty J with hJ | hJ
  · haveI := preservesLimit_empty_conditionSubfunctor 𝒟 ρ₀ h₀
    have : PreservesLimitsOfShape (Discrete PEmpty.{1}) (GaloisRep.conditionSubfunctor 𝒪 𝒟 ρ₀).toFunctor :=
      preservesLimitsOfShape_pempty_of_preservesTerminal _
    exact preservesLimitsOfShape_of_equiv (equivalenceOfIsEmpty (Discrete PEmpty.{1}) J) _
  · exact ⟨fun {D} => preservesLimit_conditionSubfunctor 𝒟 ρ₀ h𝒟 h₀ D⟩

end GaloisRep.SolAuxG5d
p2m_reactivate "P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation.ProartinianCat P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation.SubalgebraGL P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.GaloisRep P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.GaloisRep.SolAuxG5"
p2m_reactivate "P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation.ProartinianCat P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.Deformation.SubalgebraGL P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.GaloisRep P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor.GaloisRep.SolAuxG5"

theorem solution
    (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    (𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop)
    (ρ₀ : (Deformation.repnFunctor (Fin 2) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) 𝒪).obj
      Deformation.ProartinianCat.residueField)
    (h₀ : ρ₀ ∈ GaloisRep.conditionLifts 𝒪 𝒟 ρ₀ Deformation.ProartinianCat.residueField)
    [Finite (IsLocalRing.ResidueField 𝒪)]
    (h𝒟 : GaloisRep.IsDeformationCondition 𝒪 𝒟) :
    CategoryTheory.Limits.PreservesLimits (GaloisRep.conditionSubfunctor 𝒪 𝒟 ρ₀).toFunctor where
  preservesLimitsOfShape {J} _ := GaloisRep.SolAuxG5d.preservesLimitsOfShape_conditionSubfunctor 𝒟 ρ₀ h𝒟 h₀ J

end S_GaloisRep_preservesLimits_conditionSubfunctor
end P2MW
export P2MW.S_GaloisRep_preservesLimits_conditionSubfunctor (solution)
