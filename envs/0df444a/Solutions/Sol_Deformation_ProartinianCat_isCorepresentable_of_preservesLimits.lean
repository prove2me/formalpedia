-- Prove2me | solution 1 for Deformation.ProartinianCat.isCorepresentable_of_preservesLimits
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/7a934706-8ab9-57b8-92a4-e3a46c427691

import Mathlib
import Definitions.Def_Deformations_ProartinianCompact
import Definitions.Def_Mathlib_CategoryTheory_Corepresentable
import Theorems.Thm_IsProartinian_finite_quotient_of_isOpen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_ProartinianCat_isCorepresentable_of_preservesLimits

universe v u

p2m_open "CategoryTheory Function CategoryTheory.Limits IsLocalRing Filter Topology"

namespace Deformation
p2m_export "Deformation" "IsLocalProartinianAlgebra ProartinianCat"
p2m_open "Deformation"

variable {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞]

namespace ProartinianCat
p2m_export "Deformation.ProartinianCat" "of Hom ofHom comp_apply hom_ext ofEquiv toResidueField ker_toResidueField isTerminalResidueField Hom.hom algebra carrier mk commRing"
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
p2m_reactivate "P2MW.S_Deformation_ProartinianCat_isCorepresentable_of_preservesLimits.Deformation.ProartinianCat"

end Deformation
p2m_reactivate "P2MW.S_Deformation_ProartinianCat_isCorepresentable_of_preservesLimits.Deformation.ProartinianCat P2MW.S_Deformation_ProartinianCat_isCorepresentable_of_preservesLimits.Deformation"

namespace Deformation
p2m_export "Deformation" "IsLocalProartinianAlgebra ProartinianCat"
p2m_open "Deformation"
namespace ProartinianCat p2m_export "Deformation.ProartinianCat" "of Hom ofHom comp_apply hom_ext ofEquiv toResidueField ker_toResidueField isTerminalResidueField Hom.hom algebra carrier mk commRing" end ProartinianCat
p2m_open_scoped "Deformation.ProartinianCat" in
scoped instance ProartinianCat.solAux_hasLimits (𝓞 : Type u) [CommRing 𝓞] [IsLocalRing 𝓞]
    [Finite (IsLocalRing.ResidueField 𝓞)] : CategoryTheory.Limits.HasLimits (Deformation.ProartinianCat 𝓞) where
  has_limits_of_shape K _ := by
    rcases isEmpty_or_nonempty K with h | h
    · exact CategoryTheory.Limits.hasLimitsOfShape_of_equivalence (CategoryTheory.equivalenceOfIsEmpty (CategoryTheory.Discrete PEmpty.{1}) K)
    · infer_instance
p2m_reactivate "P2MW.S_Deformation_ProartinianCat_isCorepresentable_of_preservesLimits.Deformation.ProartinianCat P2MW.S_Deformation_ProartinianCat_isCorepresentable_of_preservesLimits.Deformation"
end Deformation
p2m_reactivate "P2MW.S_Deformation_ProartinianCat_isCorepresentable_of_preservesLimits.Deformation.ProartinianCat P2MW.S_Deformation_ProartinianCat_isCorepresentable_of_preservesLimits.Deformation"

p2m_open "CategoryTheory Function CategoryTheory.Limits IsLocalRing Filter Topology"

namespace Deformation
p2m_export "Deformation" "IsLocalProartinianAlgebra ProartinianCat"
p2m_open "Deformation"

variable {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞]

namespace ProartinianCat
p2m_export "Deformation.ProartinianCat" "of Hom ofHom comp_apply hom_ext ofEquiv toResidueField ker_toResidueField isTerminalResidueField Hom.hom algebra carrier mk commRing"
p2m_open "Deformation.ProartinianCat"

variable (B : ProartinianCat 𝓞)

def OpenIdx : Type u := {I : Ideal B // IsOpen (X := B) I ∧ I ≠ ⊤}

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

variable (B) in

noncomputable def quotDiagram : OpenIdx B ⥤ ProartinianCat 𝓞 where
  obj I := quotObj I
  map {I J} h := quotFactor (leOfHom h)
  map_id I := by
    refine hom_ext (ContinuousAlgHom.ext fun x ↦ ?_)
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  map_comp {I J K} h h' := by
    refine hom_ext (ContinuousAlgHom.ext fun x ↦ ?_)
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl

variable (B) in

noncomputable def quotCone : Cone (quotDiagram B) where
  pt := B
  π :=
    { app := fun I ↦ quotMk I
      naturality := fun I J h ↦ by
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
        exact (quotMk_quotFactor (leOfHom h)).symm }

variable (B) in

lemma eq_zero_of_forall_mem_openIdx {b : B.carrier} (hb : ∀ I : OpenIdx B, b ∈ I.1) :
    b = 0 := by
  by_contra hb0
  haveI : T2Space B.carrier := inferInstance
  obtain ⟨J, hJopen, hJsub⟩ := (IsLinearTopology.hasBasis_open_ideal (R := B)).mem_iff.mp
    ((isOpen_compl_singleton (x := b)).mem_nhds
      (by simpa using fun h ↦ hb0 h.symm))
  exact hJsub (hb ⟨J ⊓ maximalIdeal B, hJopen.inter isOpen_maximalIdeal_of_isProartinian,
    fun h ↦ (maximalIdeal.isMaximal B).ne_top (top_le_iff.mp (h.symm.trans_le inf_le_right))⟩).1
    rfl

variable [Finite (ResidueField 𝓞)]

variable (B) in

lemma exists_forall_quotientMk_eq (x : limitSubalgebra (quotDiagram B)) :
    ∃ b : B.carrier, ∀ I : OpenIdx B,
      Ideal.Quotient.mk I.1 b = (x : ∀ J, (quotDiagram B).obj J) I := by
  set S : OpenIdx B → Set B :=
    fun I ↦ Ideal.Quotient.mk I.1 ⁻¹' {(x : ∀ J, (quotDiagram B).obj J) I} with hS
  have hSne : ∀ I, (S I).Nonempty := fun I ↦ by
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective
      ((x : ∀ J, (quotDiagram B).obj J) I : B ⧸ I.1)
    exact ⟨b, hb⟩
  have hScl : ∀ I, IsClosed (S I) := fun I ↦
    (isClosed_singleton (X := B ⧸ I.1)).preimage (continuous_quotientMk I)
  have hSdir : Directed (· ⊇ ·) S := fun I J ↦ by
    refine ⟨OpenIdx.inf B I J, fun b hb ↦ ?_, fun b hb ↦ ?_⟩
    · simp only [hS, Set.mem_preimage, Set.mem_singleton_iff] at hb ⊢
      rw [← limitSubalgebra_compatible (quotDiagram B) x
        (homOfLE (OpenIdx.inf_le_left I J)), ← hb]
      exact (quotFactor_mk (OpenIdx.inf_le_left I J) b).symm
    · simp only [hS, Set.mem_preimage, Set.mem_singleton_iff] at hb ⊢
      rw [← limitSubalgebra_compatible (quotDiagram B) x
        (homOfLE (OpenIdx.inf_le_right I J)), ← hb]
      exact (quotFactor_mk (OpenIdx.inf_le_right I J) b).symm
  obtain ⟨b, hb⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed S hSdir
    hSne (fun I ↦ (hScl I).isCompact) hScl
  exact ⟨b, fun I ↦ by
    have h := Set.mem_iInter.mp hb I
    simp only [hS, Set.mem_preimage] at h
    exact h⟩

variable (B) in

lemma surjective_limitLift_quotCone :
    Function.Surjective (limitLift (quotCone B)).hom := fun x ↦ by
  obtain ⟨b, hb⟩ := exists_forall_quotientMk_eq B x
  exact ⟨b, Subtype.ext (funext fun I ↦ hb I)⟩

variable (B) in

lemma injective_limitLift_quotCone :
    Function.Injective (limitLift (quotCone B)).hom := by
  intro a b hab
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_mem_openIdx B fun I ↦ ?_
  refine (Ideal.Quotient.eq (I := I.1)).mp ?_
  exact congrArg
    (fun y : limitSubalgebra (quotDiagram B) ↦ (y : ∀ J, (quotDiagram B).obj J) I) hab

lemma isIso_of_bijective {X Y : ProartinianCat 𝓞} [CompactSpace X] (f : X ⟶ Y)
    (hf : Function.Bijective f.hom) : IsIso f := by

  set g : Y.carrier → X.carrier := Function.surjInv hf.2 with hg
  have hgf : ∀ x, g (f.hom x) = x := Function.leftInverse_surjInv hf
  have hfg : ∀ y, f.hom (g y) = y := Function.rightInverse_surjInv hf.2

  have hcont : Continuous g := by
    rw [continuous_iff_isClosed]
    intro s hs
    rw [← Set.image_eq_preimage_of_inverse hgf hfg]
    exact f.hom.cont.isClosedMap s hs

  refine ⟨⟨{ toFun := g
             map_one' := hf.1 (by rw [hfg, map_one])
             map_mul' := fun x y ↦ hf.1 (by rw [hfg, map_mul, hfg, hfg])
             map_zero' := hf.1 (by rw [hfg, map_zero])
             map_add' := fun x y ↦ hf.1 (by rw [hfg, map_add, hfg, hfg])
             commutes' := fun r ↦ hf.1 ((hfg _).trans (f.hom.commutes r).symm)
             cont := hcont }⟩, ?_, ?_⟩
  · ext x
    exact hgf x
  · ext y
    exact hfg y

variable (B) in

lemma isIso_limitLift_quotCone : IsIso (limitLift (quotCone B)) :=
  isIso_of_bijective _
    ⟨injective_limitLift_quotCone B, surjective_limitLift_quotCone B⟩

variable (B) in

noncomputable def quotConeIsLimit : IsLimit (quotCone B) :=
  IsLimit.ofPointIso (t := quotCone B) (limitConeIsLimit (quotDiagram B))
    (i := isIso_limitLift_quotCone B)

end ProartinianCat
p2m_reactivate "P2MW.S_Deformation_ProartinianCat_isCorepresentable_of_preservesLimits.Deformation.ProartinianCat P2MW.S_Deformation_ProartinianCat_isCorepresentable_of_preservesLimits.Deformation"

section StdObj

p2m_open "Deformation.ProartinianCat P2MW.S_Deformation_ProartinianCat_isCorepresentable_of_preservesLimits.Deformation.ProartinianCat"

variable (𝓞) in

def StdObjData : Type u :=
  Σ' (n : ℕ) (_ : CommRing (ULift.{u} (Fin n))) (_ : TopologicalSpace (ULift.{u} (Fin n)))
    (_ : Algebra 𝓞 (ULift.{u} (Fin n))), IsLocalProartinianAlgebra 𝓞 (ULift.{u} (Fin n))

namespace StdObjData

scoped instance (s : StdObjData 𝓞) : CommRing (ULift.{u} (Fin s.1)) := s.2.1
scoped instance (s : StdObjData 𝓞) : TopologicalSpace (ULift.{u} (Fin s.1)) := s.2.2.1
scoped instance (s : StdObjData 𝓞) : Algebra 𝓞 (ULift.{u} (Fin s.1)) := s.2.2.2.1
scoped instance (s : StdObjData 𝓞) : IsLocalProartinianAlgebra 𝓞 (ULift.{u} (Fin s.1)) := s.2.2.2.2

noncomputable def toObj (s : StdObjData 𝓞) : ProartinianCat 𝓞 := of 𝓞 (ULift.{u} (Fin s.1))

noncomputable def objEquiv (A : ProartinianCat 𝓞) [Finite A.carrier] :
    ULift.{u} (Fin (Nat.card A.carrier)) ≃ A.carrier :=
  Equiv.ulift.trans (Finite.equivFin A.carrier).symm

set_option backward.isDefEq.respectTransparency false in
p2m_attr_erase "instance" "Nat.instNeZeroCardOfNonemptyOfFinite in"
noncomputable def ofObj (A : ProartinianCat 𝓞) [Finite A.carrier] : StdObjData 𝓞 :=
  ⟨Nat.card A.carrier, (objEquiv A).commRing, ⊥, (objEquiv A).algebra 𝓞, by
    letI : CommRing (ULift.{u} (Fin (Nat.card A.carrier))) := (objEquiv A).commRing
    letI : TopologicalSpace (ULift.{u} (Fin (Nat.card A.carrier))) := ⊥
    letI : Algebra 𝓞 (ULift.{u} (Fin (Nat.card A.carrier))) := (objEquiv A).algebra 𝓞
    letI : DiscreteTopology (ULift.{u} (Fin (Nat.card A.carrier))) := ⟨rfl⟩

    let e : ULift.{u} (Fin (Nat.card A.carrier)) ≃ₐ[𝓞] A.carrier := (objEquiv A).algEquiv 𝓞
    haveI : IsArtinianRing (ULift.{u} (Fin (Nat.card A.carrier))) := isArtinian_of_finite
    haveI : Nontrivial (ULift.{u} (Fin (Nat.card A.carrier))) :=
      (objEquiv A).surjective.nontrivial

    haveI : IsLocalRing (ULift.{u} (Fin (Nat.card A.carrier))) := by
      refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a ↦ ?_
      rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (e a) with h | h
      · exact Or.inl (by simpa using h.map e.symm)
      · exact Or.inr (by simpa [map_sub, map_one] using h.map e.symm)

    haveI : IsLocalHom (algebraMap 𝓞 (ULift.{u} (Fin (Nat.card A.carrier)))) := by
      constructor
      intro o ho
      have h1 : IsUnit (algebraMap 𝓞 A.carrier o) := by
        have h2 := ho.map e
        rwa [AlgEquiv.commutes] at h2
      exact (isUnit_map_iff (algebraMap 𝓞 A.carrier) o).mp h1

    haveI : IsResidueAlgebra 𝓞 (ULift.{u} (Fin (Nat.card A.carrier))) := by
      constructor
      intro ξ
      obtain ⟨x, rfl⟩ := residue_surjective ξ
      obtain ⟨o, ho⟩ := IsResidueAlgebra.algebraMap_surjective 𝓞 A.carrier (residue _ (e x))
      rw [IsScalarTower.algebraMap_apply 𝓞 A.carrier (ResidueField A.carrier),
        ResidueField.algebraMap_eq] at ho
      refine ⟨o, ?_⟩
      rw [IsScalarTower.algebraMap_apply 𝓞 (ULift.{u} (Fin (Nat.card A.carrier)))
        (ResidueField (ULift.{u} (Fin (Nat.card A.carrier)))), ResidueField.algebraMap_eq]
      refine (Ideal.Quotient.eq
        (I := maximalIdeal (ULift.{u} (Fin (Nat.card A.carrier))))).mpr ?_
      have hunit : ∀ z : ULift.{u} (Fin (Nat.card A.carrier)), IsUnit (e z) ↔ IsUnit z :=
        fun z ↦ ⟨fun h ↦ by simpa using h.map e.symm, fun h ↦ h.map e⟩
      have hmem : ∀ z : ULift.{u} (Fin (Nat.card A.carrier)),
          z ∈ maximalIdeal _ ↔ e z ∈ maximalIdeal A.carrier := fun z ↦ by
        rw [mem_maximalIdeal, mem_nonunits_iff, mem_maximalIdeal, mem_nonunits_iff]
        exact (not_congr (hunit z)).symm
      rw [hmem, map_sub, AlgEquiv.commutes]
      exact Ideal.Quotient.eq.mp ho
    exact { }⟩

set_option backward.isDefEq.respectTransparency false in

lemma exists_iso (A : ProartinianCat 𝓞) [Finite A.carrier] :
    ∃ s : StdObjData 𝓞, Nonempty (s.toObj ≅ A) := by
  refine ⟨ofObj A, ⟨ofEquiv ?_⟩⟩
  refine { toAlgEquiv := (objEquiv A).algEquiv 𝓞, continuous_toFun := ?_,
           continuous_invFun := ?_ }
  ·
    exact continuous_of_discreteTopology
  ·
    exact continuous_of_discreteTopology

end StdObjData
p2m_reactivate "P2MW.S_Deformation_ProartinianCat_isCorepresentable_of_preservesLimits.Deformation.ProartinianCat P2MW.S_Deformation_ProartinianCat_isCorepresentable_of_preservesLimits.Deformation P2MW.S_Deformation_ProartinianCat_isCorepresentable_of_preservesLimits.Deformation.StdObjData"

end StdObj
p2m_reactivate "P2MW.S_Deformation_ProartinianCat_isCorepresentable_of_preservesLimits.Deformation.ProartinianCat P2MW.S_Deformation_ProartinianCat_isCorepresentable_of_preservesLimits.Deformation P2MW.S_Deformation_ProartinianCat_isCorepresentable_of_preservesLimits.Deformation.StdObjData"

end Deformation
p2m_reactivate "P2MW.S_Deformation_ProartinianCat_isCorepresentable_of_preservesLimits.Deformation.ProartinianCat P2MW.S_Deformation_ProartinianCat_isCorepresentable_of_preservesLimits.Deformation P2MW.S_Deformation_ProartinianCat_isCorepresentable_of_preservesLimits.Deformation.StdObjData"

namespace Deformation
p2m_export "Deformation" "IsLocalProartinianAlgebra ProartinianCat"
p2m_open "Deformation"

namespace OfPreservesLimits

variable {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞] [Finite (ResidueField 𝓞)]
variable (F : ProartinianCat 𝓞 ⥤ Type u) [PreservesLimits F]

p2m_open "Deformation.ProartinianCat P2MW.S_Deformation_ProartinianCat_isCorepresentable_of_preservesLimits.Deformation.ProartinianCat"

scoped instance instHasLimitsElements : HasLimits F.Elements where
  has_limits_of_shape _ _ := inferInstance

def StdElem : Type u :=
  Σ' (s : StdObjData 𝓞), F.obj s.toObj

variable {F} in

noncomputable def StdElem.toElement (s : StdElem F) : F.Elements :=
  ⟨s.1.toObj, s.2⟩

variable {F} in

lemma StdElem.exists_iso (X : F.Elements) (hX : Finite X.1.carrier) :
    ∃ s : StdElem F, Nonempty (s.toElement ≅ X) := by
  haveI := hX
  obtain ⟨s₀, ⟨e⟩⟩ := StdObjData.exists_iso X.1
  refine ⟨⟨s₀, F.map e.inv X.2⟩, ⟨CategoryOfElements.isoMk _ _ e ?_⟩⟩
  show (F.map e.inv ≫ F.map e.hom) X.2 = X.2
  rw [← Functor.map_comp, Iso.inv_hom_id]
  exact FunctorToTypes.map_id_apply _ _

noncomputable def StdCat : Type u :=
  InducedCategory F.Elements (StdElem.toElement (F := F))

noncomputable scoped instance : Category.{u} (StdCat F) :=
  inferInstanceAs (Category (InducedCategory _ (StdElem.toElement (F := F))))

noncomputable def stdInclusion : StdCat F ⥤ F.Elements :=
  inducedFunctor _

scoped instance : HasLimit (stdInclusion F) :=
  inferInstance

variable {F} (X : F.Elements)

noncomputable def quotElemDiagram : OpenIdx X.1 ⥤ F.Elements where
  obj I := ⟨quotObj I, F.map (quotMk I) X.2⟩
  map {I J} h := ⟨quotFactor (leOfHom h), by
    rw [← FunctorToTypes.map_comp_apply, quotMk_quotFactor]⟩
  map_id I := by
    apply CategoryOfElements.ext
    exact (quotDiagram X.1).map_id I
  map_comp {I J K} h h' := by
    apply CategoryOfElements.ext
    exact (quotDiagram X.1).map_comp h h'

noncomputable def quotElemCone : Cone (quotElemDiagram X) where
  pt := X
  π :=
    { app := fun I ↦ ⟨quotMk I, rfl⟩
      naturality := fun I J h ↦ by
        apply CategoryOfElements.ext
        exact (quotCone X.1).π.naturality h }

noncomputable def quotElemConeIsLimit : IsLimit (quotElemCone X) := by
  apply isLimitOfReflects (CategoryOfElements.π F)
  exact (quotConeIsLimit X.1).ofIsoLimit
    (Cones.ext (Iso.refl _) (fun I ↦ (Category.id_comp _).symm))

variable (F) in

noncomputable def weaklyInitialObj : F.Elements :=
  limit (stdInclusion F)

noncomputable def quotStdModel (I : OpenIdx X.1) : StdElem F :=
  (StdElem.exists_iso ((quotElemDiagram X).obj I)
    (inferInstanceAs (Finite (quotObj I)))).choose

noncomputable def quotStdModelIso (I : OpenIdx X.1) :
    (quotStdModel X I).toElement ≅ (quotElemDiagram X).obj I :=
  (StdElem.exists_iso ((quotElemDiagram X).obj I)
    (inferInstanceAs (Finite (quotObj I)))).choose_spec.some

noncomputable def quotStdDiagram : OpenIdx X.1 ⥤ StdCat F where
  obj I := quotStdModel X I
  map {I J} h := InducedCategory.homMk
    ((quotStdModelIso X I).hom ≫ (quotElemDiagram X).map h ≫ (quotStdModelIso X J).inv)
  map_id I := by
    apply InducedCategory.hom_ext
    show (quotStdModelIso X I).hom ≫ _ ≫ _ = _
    rw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id]
    rfl
  map_comp {I J K} h h' := by
    apply InducedCategory.hom_ext
    show (quotStdModelIso X I).hom ≫ _ ≫ _ = _
    rw [Functor.map_comp]
    show _ = ((quotStdModelIso X I).hom ≫ _ ≫ _) ≫ ((quotStdModelIso X J).hom ≫ _ ≫ _)
    simp

noncomputable def quotStdDiagramComparison :
    quotStdDiagram X ⋙ stdInclusion F ⟶ quotElemDiagram X where
  app I := (quotStdModelIso X I).hom
  naturality I J h := by
    show ((quotStdModelIso X I).hom ≫ (quotElemDiagram X).map h ≫ (quotStdModelIso X J).inv) ≫
      (quotStdModelIso X J).hom = (quotStdModelIso X I).hom ≫ (quotElemDiagram X).map h
    simp

variable (F) in

theorem exists_weakly_initial :
    ∃ T : F.Elements, ∀ X, Nonempty (T ⟶ X) := by
  refine ⟨weaklyInitialObj F, fun X ↦ ⟨?_⟩⟩
  exact (quotElemConeIsLimit X).lift
    ((Cones.postcompose (quotStdDiagramComparison X)).obj
      ((limit.cone (stdInclusion F)).whisker (quotStdDiagram X)))

variable (F) in

theorem isCorepresentable_of_preservesLimits : F.IsCorepresentable := by
  obtain ⟨T, hT⟩ := exists_weakly_initial F
  have : HasInitial F.Elements :=
    hasInitial_of_weakly_initial_and_hasWideEqualizers hT
  exact Functor.isCorepresentable_of_hasInitial_elements

end OfPreservesLimits
p2m_reactivate "P2MW.S_Deformation_ProartinianCat_isCorepresentable_of_preservesLimits.Deformation.ProartinianCat P2MW.S_Deformation_ProartinianCat_isCorepresentable_of_preservesLimits.Deformation P2MW.S_Deformation_ProartinianCat_isCorepresentable_of_preservesLimits.Deformation.StdObjData P2MW.S_Deformation_ProartinianCat_isCorepresentable_of_preservesLimits.Deformation.OfPreservesLimits"

end Deformation
p2m_reactivate "P2MW.S_Deformation_ProartinianCat_isCorepresentable_of_preservesLimits.Deformation.ProartinianCat P2MW.S_Deformation_ProartinianCat_isCorepresentable_of_preservesLimits.Deformation P2MW.S_Deformation_ProartinianCat_isCorepresentable_of_preservesLimits.Deformation.StdObjData P2MW.S_Deformation_ProartinianCat_isCorepresentable_of_preservesLimits.Deformation.OfPreservesLimits"

theorem solution {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞]
  [Finite (IsLocalRing.ResidueField 𝓞)] (F : CategoryTheory.Functor (Deformation.ProartinianCat 𝓞) (Type u))
  [CategoryTheory.Limits.PreservesLimits F] : F.IsCorepresentable :=
  Deformation.OfPreservesLimits.isCorepresentable_of_preservesLimits F

end S_Deformation_ProartinianCat_isCorepresentable_of_preservesLimits
end P2MW
export P2MW.S_Deformation_ProartinianCat_isCorepresentable_of_preservesLimits (solution)
