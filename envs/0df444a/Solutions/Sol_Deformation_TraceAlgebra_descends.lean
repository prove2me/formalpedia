-- Prove2me | solution 1 for Deformation.TraceAlgebra.descends
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/f6a4dd51-3f97-5a16-ab66-137d70a7fede

import Mathlib
import Definitions.Def_Deformations_TraceAlgebra
import Definitions.Def_Deformations_ClosedSubalgebra
import Definitions.Def_Deformations_MatrixRepresentation
import Definitions.Def_Representation_AbsolutelyIrreducible
import Theorems.Thm_Representation_span_range_eq_top_of_isAbsolutelyIrreducible_matrix
import Theorems.Thm_Matrix_span_eq_top_of_map_span_eq_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_TraceAlgebra_descends

universe u

open CategoryTheory Function IsLocalRing Filter Topology

set_option linter.unusedSectionVars false

namespace Deformation
p2m_export "Deformation" "conjKer mem_conjKer_iff conjAct_smul_apply traceSubalgebra isClosed_traceSubalgebra trace_mem_traceSubalgebra TraceAlgebra.Descends repnFunctor repnFunctor_map toRepresentation liftFunctor ProartinianCat ProartinianCat.residueField ProartinianCat.toResidueField ProartinianCat.isUnit_of_isUnit_val matrixRepresentation"
p2m_open "Deformation"

namespace Carayol

section IdealEntries

variable {n : Type} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

lemma mul_entries_mem {I J : Ideal R} {X Y : Matrix n n R}
    (hX : ∀ i j, X i j ∈ I) (hY : ∀ i j, Y i j ∈ J) (i j : n) : (X * Y) i j ∈ I * J := by
  rw [Matrix.mul_apply]
  exact Submodule.sum_mem _ fun k _ => Ideal.mul_mem_mul (hX i k) (hY k j)

lemma mul_entries_mem_right {I : Ideal R} {X Y : Matrix n n R}
    (hY : ∀ i j, Y i j ∈ I) (i j : n) : (X * Y) i j ∈ I := by
  rw [Matrix.mul_apply]
  exact Submodule.sum_mem _ fun k _ => I.mul_mem_left _ (hY k j)

lemma mul_entries_mem_left {I : Ideal R} {X Y : Matrix n n R}
    (hX : ∀ i j, X i j ∈ I) (i j : n) : (X * Y) i j ∈ I := by
  rw [Matrix.mul_apply]
  exact Submodule.sum_mem _ fun k _ => I.mul_mem_right _ (hX i k)

lemma trace_mem_of_entries_mem {I : Ideal R} {X : Matrix n n R}
    (hX : ∀ i j, X i j ∈ I) : Matrix.trace X ∈ I :=
  Submodule.sum_mem _ fun k _ => hX k k

end IdealEntries

variable {n : Type} [Fintype n] [DecidableEq n]
variable {G : Type u} [Group G] [TopologicalSpace G]
variable {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞] [Finite (ResidueField 𝓞)]
variable {A : ProartinianCat 𝓞}

p2m_open "Deformation.ProartinianCat"

abbrev matVal (ρ' : G →ₜ* GL n A) (g : G) : Matrix n n A.carrier :=
  ((ρ' g : GL n A.carrier) : Matrix n n A.carrier)

lemma matVal_mul (ρ' : G →ₜ* GL n A) (g h : G) :
    matVal ρ' (g * h) = matVal ρ' g * matVal ρ' h := by
  show ((ρ' (g * h) : GL n A.carrier) : Matrix n n A.carrier) = _
  rw [map_mul]
  rfl

lemma matVal_one (ρ' : G →ₜ* GL n A) : matVal ρ' 1 = 1 := by
  show ((ρ' 1 : GL n A.carrier) : Matrix n n A.carrier) = 1
  rw [map_one]
  rfl

lemma trace_matVal_mem (ρ' : G →ₜ* GL n A) (g : G) :
    Matrix.trace (matVal ρ' g) ∈ traceSubalgebra 𝓞 ρ' :=
  trace_mem_traceSubalgebra ρ' g

noncomputable abbrev matVal₀ (ρ₀ : (repnFunctor n G 𝓞).obj .residueField) (g : G) :
    Matrix n n (ProartinianCat.residueField (𝓞 := 𝓞)) :=
  ((DFunLike.coe (F := G →ₜ* GL n (ProartinianCat.residueField (𝓞 := 𝓞)))
      (α := G) (β := fun _ => GL n (ProartinianCat.residueField (𝓞 := 𝓞))) ρ₀ g :
    GL n (ProartinianCat.residueField (𝓞 := 𝓞))) :
      Matrix n n (ProartinianCat.residueField (𝓞 := 𝓞)))

section Residue

noncomputable abbrev resMap (A : ProartinianCat 𝓞) :
    A.carrier →+* (ProartinianCat.residueField (𝓞 := 𝓞)).carrier :=
  (toResidueField A).hom.toRingHom

lemma ker_resMap (A : ProartinianCat 𝓞) :
    RingHom.ker (resMap A) = maximalIdeal A.carrier :=
  ker_toResidueField A

lemma resMap_eq_zero_iff {a : A.carrier} :
    resMap A a = 0 ↔ a ∈ maximalIdeal A.carrier := by
  rw [← ker_resMap A]
  rfl

lemma isUnit_of_resMap_ne_zero {a : A.carrier} (ha : resMap A a ≠ 0) : IsUnit a := by
  by_contra h
  exact ha (resMap_eq_zero_iff.mpr ((mem_maximalIdeal a).mpr h))

lemma exists_algebraMap_resMap_eq (lam : (ProartinianCat.residueField (𝓞 := 𝓞)).carrier) :
    ∃ o : 𝓞, resMap A (algebraMap 𝓞 A.carrier o) = lam := by
  obtain ⟨o, ho⟩ := IsLocalRing.residue_surjective (R := 𝓞) lam
  refine ⟨o, ?_⟩
  have h1 : resMap A (algebraMap 𝓞 A.carrier o) =
      algebraMap 𝓞 (ProartinianCat.residueField (𝓞 := 𝓞)).carrier o :=
    (toResidueField A).hom.toAlgHom.commutes o
  rw [h1]
  exact ho ▸ congrFun (congrArg _ (ResidueField.algebraMap_eq 𝓞)) o

end Residue

section Choice

variable (ρ₀ : (repnFunctor n G 𝓞).obj .residueField)
variable [Representation.IsAbsolutelyIrreducible.{u} (toRepresentation ρ₀)]

lemma span_matVal₀_eq_top :
    Submodule.span (ProartinianCat.residueField (𝓞 := 𝓞)).carrier
      (Set.range (matVal₀ ρ₀)) = ⊤ := by
  haveI : Representation.IsAbsolutelyIrreducible.{u}
      (matrixRepresentation (k := (ProartinianCat.residueField (𝓞 := 𝓞)).carrier)
        (ρ₀.toMonoidHom : G →* GL n (ProartinianCat.residueField (𝓞 := 𝓞)).carrier)) := ‹_›
  exact Representation.span_range_eq_top_of_isAbsolutelyIrreducible_matrix
    (ρ₀.toMonoidHom : G →* GL n (ProartinianCat.residueField (𝓞 := 𝓞)).carrier)

lemma exists_basis_choice :
    ∃ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι) (gg : ι → G),
      LinearIndependent (ProartinianCat.residueField (𝓞 := 𝓞)).carrier
        (fun a : ι => matVal₀ ρ₀ (gg a)) ∧
      Submodule.span (ProartinianCat.residueField (𝓞 := 𝓞)).carrier
        (Set.range fun a : ι => matVal₀ ρ₀ (gg a)) = ⊤ := by
  obtain ⟨s, hs_sub, hs_span, hs_li⟩ :=
    exists_linearIndependent (ProartinianCat.residueField (𝓞 := 𝓞)).carrier
      (Set.range (matVal₀ ρ₀))
  haveI : Fintype s := hs_li.setFinite.fintype

  choose f hf using hs_sub
  refine ⟨s, inferInstance, Classical.decEq s, fun a => f a.2, ?_, ?_⟩
  · have h1 : (fun a : s => matVal₀ ρ₀ (f a.2)) = fun a : s => (a : Matrix n n _) := by
      funext a
      exact hf a.2
    rw [h1]
    exact hs_li
  · have h1 : (Set.range fun a : s => matVal₀ ρ₀ (f a.2)) = s := by
      ext x
      constructor
      · rintro ⟨a, rfl⟩
        show matVal₀ ρ₀ (f a.2) ∈ s
        rw [hf a.2]
        exact a.2
      · intro hx
        exact ⟨⟨x, hx⟩, hf hx⟩
    rw [h1, hs_span]
    exact span_matVal₀_eq_top ρ₀

end Choice

section LiftUnfold

omit [Finite (ResidueField 𝓞)] in

lemma mem_liftFunctor_obj_iff' (ρ₀ : (repnFunctor n G 𝓞).obj .residueField)
    {R : ProartinianCat 𝓞} (ρ' : (repnFunctor n G 𝓞).obj R) :
    ρ' ∈ (liftFunctor n G 𝓞 ρ₀).obj R ↔ (repnFunctor n G 𝓞).map (toResidueField R) ρ' = ρ₀ := by
  show (repnFunctor n G 𝓞).map (isTerminalResidueField.from R) ρ' ∈ ({ρ₀} : Set _) ↔ _
  rw [Set.mem_singleton_iff, Subsingleton.elim (isTerminalResidueField.from R) (toResidueField R)]

omit [Finite (ResidueField 𝓞)] in

lemma map_residue_eq_of_mem_liftFunctor {R : ProartinianCat 𝓞}
    {ρ₀ : (repnFunctor n G 𝓞).obj .residueField} {ρ' : G →ₜ* GL n R}
    (hρ' : ρ' ∈ (liftFunctor n G 𝓞 ρ₀).obj R) (g : G) :
    ((ρ' g : GL n R) : Matrix n n R).map
        (ProartinianCat.toResidueField R).hom.toRingHom =
      ((DFunLike.coe (F := G →ₜ* GL n ProartinianCat.residueField)
        (α := G) (β := fun _ => GL n ProartinianCat.residueField) ρ₀ g :
          GL n (ProartinianCat.residueField (𝓞 := 𝓞))) :
        Matrix n n (ProartinianCat.residueField (𝓞 := 𝓞))) := by
  have h1 : (repnFunctor n G 𝓞).map (ProartinianCat.toResidueField R) ρ' = ρ₀ :=
    (mem_liftFunctor_obj_iff' ρ₀ ρ').mp hρ'
  have h2 : Matrix.GeneralLinearGroup.map
      (ProartinianCat.toResidueField R).hom.toRingHom (ρ' g) =
      DFunLike.coe (F := G →ₜ* GL n ProartinianCat.residueField)
        (α := G) (β := fun _ => GL n ProartinianCat.residueField) ρ₀ g :=
    (repnFunctor_map G 𝓞 (ProartinianCat.toResidueField R) ρ' g).symm.trans
      (DFunLike.congr_fun (F := G →ₜ* GL n ProartinianCat.residueField)
        (α := G) (β := fun _ => GL n ProartinianCat.residueField) h1 g)
  exact congrArg Units.val h2

end LiftUnfold

section TraceForm

variable {ρ₀ : (repnFunctor n G 𝓞).obj .residueField}
variable {ρ' : G →ₜ* GL n A}
variable {ι : Type u} [Fintype ι] [DecidableEq ι] {gg : ι → G}

lemma matVal_map_resMap (hρ' : ρ' ∈ (liftFunctor n G 𝓞 ρ₀).obj A) (g : G) :
    (matVal ρ' g).map (resMap A) = matVal₀ ρ₀ g :=
  map_residue_eq_of_mem_liftFunctor hρ' g

noncomputable def gram (ρ' : G →ₜ* GL n A) (gg : ι → G) :
    Matrix ι ι (traceSubalgebra 𝓞 ρ') :=
  Matrix.of fun a b => ⟨Matrix.trace (matVal ρ' (gg a * gg b)), trace_matVal_mem ρ' _⟩

noncomputable def gramA (ρ' : G →ₜ* GL n A) (gg : ι → G) : Matrix ι ι A.carrier :=
  ((traceSubalgebra 𝓞 ρ').val.toRingHom.mapMatrix : Matrix ι ι (traceSubalgebra 𝓞 ρ') →+*
    Matrix ι ι A.carrier) (gram ρ' gg)

lemma mulVec_apply' {R : Type*} [NonUnitalNonAssocSemiring R] (M : Matrix ι ι R) (v : ι → R)
    (a : ι) : M.mulVec v a = ∑ b, M a b * v b := rfl

lemma gramA_apply (a b : ι) :
    gramA ρ' gg a b = Matrix.trace (matVal ρ' (gg a) * matVal ρ' (gg b)) := by
  show ((traceSubalgebra 𝓞 ρ').val.toRingHom.mapMatrix (gram ρ' gg)) a b = _
  rw [RingHom.mapMatrix_apply, Matrix.map_apply]
  show ((gram ρ' gg a b : traceSubalgebra 𝓞 ρ') : A.carrier) = _
  rw [show gram ρ' gg a b = ⟨Matrix.trace (matVal ρ' (gg a * gg b)), trace_matVal_mem ρ' _⟩
    from rfl]
  show Matrix.trace (matVal ρ' (gg a * gg b)) = _
  rw [matVal_mul]

lemma resMap_gramA (hρ' : ρ' ∈ (liftFunctor n G 𝓞 ρ₀).obj A) (a b : ι) :
    resMap A (gramA ρ' gg a b) =
      Matrix.trace (matVal₀ ρ₀ (gg a) * matVal₀ ρ₀ (gg b)) := by
  rw [gramA_apply, ← matVal_map_resMap hρ' (gg a), ← matVal_map_resMap hρ' (gg b),
    ← Matrix.map_mul]
  exact AddMonoidHom.map_trace (resMap A) (matVal ρ' (gg a) * matVal ρ' (gg b))

variable (hρ' : ρ' ∈ (liftFunctor n G 𝓞 ρ₀).obj A)
variable (hgg_li : LinearIndependent (ProartinianCat.residueField (𝓞 := 𝓞)).carrier
  fun a : ι => matVal₀ ρ₀ (gg a))
variable (hgg_span : Submodule.span (ProartinianCat.residueField (𝓞 := 𝓞)).carrier
  (Set.range fun a : ι => matVal₀ ρ₀ (gg a)) = ⊤)

include hρ' hgg_li hgg_span in

lemma isUnit_det_gramA : IsUnit (gramA ρ' gg).det := by
  set K := (ProartinianCat.residueField (𝓞 := 𝓞)).carrier
  refine isUnit_of_resMap_ne_zero (a := (gramA ρ' gg).det) ?_
  have h1 : resMap A (gramA ρ' gg).det = ((resMap A).mapMatrix (gramA ρ' gg)).det :=
    RingHom.map_det (resMap A) (gramA ρ' gg)
  rw [h1]

  have h2 : (resMap A).mapMatrix (gramA ρ' gg) =
      Matrix.of fun a b : ι => Matrix.trace (matVal₀ ρ₀ (gg a) * matVal₀ ρ₀ (gg b)) := by
    ext a b
    exact resMap_gramA hρ' a b
  rw [h2]

  intro hdet
  obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  set Y : Matrix n n K := ∑ b : ι, x b • matVal₀ ρ₀ (gg b) with hY
  have hYtr : ∀ a : ι, Matrix.trace (matVal₀ ρ₀ (gg a) * Y) = 0 := by
    intro a
    have h3 : Matrix.trace (matVal₀ ρ₀ (gg a) * Y) =
        ∑ b : ι, Matrix.trace (matVal₀ ρ₀ (gg a) * matVal₀ ρ₀ (gg b)) * x b := by
      rw [hY, Finset.mul_sum, Matrix.trace_sum]
      exact Finset.sum_congr rfl fun b _ => by
        rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, mul_comm]
    rw [h3]
    exact congrFun hx a
  have hYzero : Y = 0 := by
    rw [Matrix.ext_iff_trace_mul_left]
    intro Z
    have hZ : Z ∈ Submodule.span K (Set.range fun a : ι => matVal₀ ρ₀ (gg a)) :=
      hgg_span ▸ Submodule.mem_top
    rw [mul_zero, Matrix.trace_zero]
    induction hZ using Submodule.span_induction with
    | mem z hz => obtain ⟨a, rfl⟩ := hz; exact hYtr a
    | zero => simp
    | add z w _ _ hz hw => rw [add_mul, Matrix.trace_add, hz, hw, add_zero]
    | smul c z _ hz => rw [smul_mul_assoc, Matrix.trace_smul, hz, smul_zero]
  exact hx0 (funext fun b =>
    linearIndependent_iff'.mp hgg_li Finset.univ x (by rw [← hY, hYzero]) b (Finset.mem_univ b))

include hρ' hgg_li hgg_span in

lemma isUnit_det_gram : IsUnit (gram ρ' gg).det := by
  have h1 : IsUnit (((gram ρ' gg).det : traceSubalgebra 𝓞 ρ') : A.carrier) := by
    have h2 : (((gram ρ' gg).det : traceSubalgebra 𝓞 ρ') : A.carrier) = (gramA ρ' gg).det :=
      RingHom.map_det ((traceSubalgebra 𝓞 ρ').val.toRingHom) (gram ρ' gg)
    rw [h2]
    exact isUnit_det_gramA hρ' hgg_li hgg_span
  exact ProartinianCat.isUnit_of_isUnit_val (traceSubalgebra 𝓞 ρ')
    (isClosed_traceSubalgebra ρ') _ h1

noncomputable def coord (ρ' : G →ₜ* GL n A) (gg : ι → G) (X : Matrix n n A.carrier) :
    ι → A.carrier :=
  (gramA ρ' gg)⁻¹.mulVec fun b => Matrix.trace (matVal ρ' (gg b) * X)

lemma trace_pairing_eq_gramA_mulVec (c : ι → A.carrier) (b : ι) :
    Matrix.trace (matVal ρ' (gg b) * ∑ a : ι, c a • matVal ρ' (gg a)) =
      (gramA ρ' gg).mulVec c b := by
  rw [Finset.mul_sum, Matrix.trace_sum, mulVec_apply']
  exact Finset.sum_congr rfl fun a _ => by
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, mul_comm, gramA_apply]

include hρ' hgg_li hgg_span in

lemma coord_eq_of_eq_sum {X : Matrix n n A.carrier} {c : ι → A.carrier}
    (hX : X = ∑ a : ι, c a • matVal ρ' (gg a)) : coord ρ' gg X = c := by
  have hQ : IsUnit (gramA ρ' gg).det := isUnit_det_gramA hρ' hgg_li hgg_span
  have h1 : (fun b => Matrix.trace (matVal ρ' (gg b) * X)) = (gramA ρ' gg).mulVec c := by
    funext b
    rw [hX]
    exact trace_pairing_eq_gramA_mulVec c b
  show (gramA ρ' gg)⁻¹.mulVec (fun b => Matrix.trace (matVal ρ' (gg b) * X)) = c
  rw [h1, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hQ, Matrix.one_mulVec]

include hρ' hgg_li hgg_span in

lemma coord_mem_and_eq_sum {X : Matrix n n A.carrier}
    (hXspan : X ∈ Submodule.span A.carrier (Set.range fun a : ι => matVal ρ' (gg a)))
    (hXtr : ∀ b : ι, Matrix.trace (matVal ρ' (gg b) * X) ∈ traceSubalgebra 𝓞 ρ') :
    (∀ a, coord ρ' gg X a ∈ traceSubalgebra 𝓞 ρ') ∧
      X = ∑ a : ι, coord ρ' gg X a • matVal ρ' (gg a) := by

  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A.carrier).mp hXspan
  have hcoord : coord ρ' gg X = c := coord_eq_of_eq_sum hρ' hgg_li hgg_span hc.symm
  refine ⟨?_, by rw [hcoord]; exact hc.symm⟩

  intro a

  have hQ : IsUnit (gram ρ' gg).det := isUnit_det_gram hρ' hgg_li hgg_span
  have hkey : (gramA ρ' gg)⁻¹ =
      ((traceSubalgebra 𝓞 ρ').val.toRingHom.mapMatrix : Matrix ι ι (traceSubalgebra 𝓞 ρ') →+*
        Matrix ι ι A.carrier) (gram ρ' gg)⁻¹ := by
    refine Matrix.inv_eq_right_inv ?_
    show gramA ρ' gg * _ = 1
    rw [gramA, ← map_mul, Matrix.mul_nonsing_inv _ hQ, map_one]
  show (gramA ρ' gg)⁻¹.mulVec (fun b => Matrix.trace (matVal ρ' (gg b) * X)) a ∈ _
  rw [hkey, mulVec_apply']
  refine Subalgebra.sum_mem _ fun b _ => Subalgebra.mul_mem _ ?_ (hXtr b)
  show (((gram ρ' gg)⁻¹ a b : traceSubalgebra 𝓞 ρ') : A.carrier) ∈ traceSubalgebra 𝓞 ρ'
  exact SetLike.coe_mem _

include hρ' hgg_li hgg_span in

lemma matVal_coord_mem_and_eq_sum (g : G) :
    (∀ a, coord ρ' gg (matVal ρ' g) a ∈ traceSubalgebra 𝓞 ρ') ∧
      matVal ρ' g = ∑ a : ι, coord ρ' gg (matVal ρ' g) a • matVal ρ' (gg a) := by
  refine coord_mem_and_eq_sum hρ' hgg_li hgg_span ?_ ?_
  ·
    have hspan : Submodule.span A.carrier
        (Set.range fun a : ι => matVal ρ' (gg a)) = ⊤ := by
      refine Matrix.span_eq_top_of_map_span_eq_top (resMap A)
        (toResidueField_surjective A) ?_
      rw [show ((fun X : Matrix n n A.carrier => X.map (resMap A)) ''
          Set.range fun a : ι => matVal ρ' (gg a)) =
          Set.range fun a : ι => matVal₀ ρ₀ (gg a) by
        rw [← Set.range_comp]
        exact congrArg Set.range (funext fun a => matVal_map_resMap hρ' (gg a))]
      exact hgg_span
    rw [hspan]
    exact Submodule.mem_top
  · intro b
    rw [← matVal_mul]
    exact trace_matVal_mem ρ' _

include hρ' hgg_li hgg_span in

lemma coord_mem_maximalIdeal_of_entries_mem {X : Matrix n n A.carrier} {c : ι → A.carrier}
    (_hc : ∀ a, c a ∈ traceSubalgebra 𝓞 ρ') (hX : X = ∑ a : ι, c a • matVal ρ' (gg a))
    (hXm : ∀ i j, X i j ∈ maximalIdeal A.carrier) (a : ι) :
    c a ∈ maximalIdeal A.carrier := by
  have hcoord : coord ρ' gg X = c := coord_eq_of_eq_sum hρ' hgg_li hgg_span hX
  rw [← hcoord]
  show (gramA ρ' gg)⁻¹.mulVec (fun b => Matrix.trace (matVal ρ' (gg b) * X)) a ∈ _
  rw [mulVec_apply']
  refine Submodule.sum_mem _ fun b _ => Ideal.mul_mem_left _ _ ?_

  exact trace_mem_of_entries_mem fun i j => mul_entries_mem_right hXm i j

end TraceForm

section Span

variable {ρ₀ : (repnFunctor n G 𝓞).obj .residueField}
variable {ρ' : G →ₜ* GL n A}
variable {ι : Type u} [Fintype ι] [DecidableEq ι] {gg : ι → G}

variable (ρ' gg) in

def Mset : Set (Matrix n n A.carrier) :=
  (fun c : ι → A.carrier => ∑ a, c a • matVal ρ' (gg a)) ''
    {c | ∀ a, c a ∈ traceSubalgebra 𝓞 ρ'}

lemma mem_Mset_iff {X : Matrix n n A.carrier} :
    X ∈ Mset ρ' gg ↔ ∃ c : ι → A.carrier,
      (∀ a, c a ∈ traceSubalgebra 𝓞 ρ') ∧ X = ∑ a, c a • matVal ρ' (gg a) := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, hc, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, hc, rfl⟩

lemma sum_smul_mem_Mset {c : ι → A.carrier} (hc : ∀ a, c a ∈ traceSubalgebra 𝓞 ρ') :
    ∑ a, c a • matVal ρ' (gg a) ∈ Mset ρ' gg :=
  ⟨c, hc, rfl⟩

lemma add_mem_Mset {X Y : Matrix n n A.carrier} (hX : X ∈ Mset ρ' gg) (hY : Y ∈ Mset ρ' gg) :
    X + Y ∈ Mset ρ' gg := by
  obtain ⟨c, hc, rfl⟩ := mem_Mset_iff.mp hX
  obtain ⟨d, hd, rfl⟩ := mem_Mset_iff.mp hY
  refine mem_Mset_iff.mpr ⟨c + d, fun a => add_mem (hc a) (hd a), ?_⟩
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by rw [Pi.add_apply, add_smul]

lemma sub_mem_Mset {X Y : Matrix n n A.carrier} (hX : X ∈ Mset ρ' gg) (hY : Y ∈ Mset ρ' gg) :
    X - Y ∈ Mset ρ' gg := by
  obtain ⟨c, hc, rfl⟩ := mem_Mset_iff.mp hX
  obtain ⟨d, hd, rfl⟩ := mem_Mset_iff.mp hY
  refine mem_Mset_iff.mpr ⟨c - d, fun a => sub_mem (hc a) (hd a), ?_⟩
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun a _ => by rw [Pi.sub_apply, sub_smul]

lemma smul_mem_Mset {t : A.carrier} (ht : t ∈ traceSubalgebra 𝓞 ρ') {X : Matrix n n A.carrier}
    (hX : X ∈ Mset ρ' gg) : t • X ∈ Mset ρ' gg := by
  obtain ⟨c, hc, rfl⟩ := mem_Mset_iff.mp hX
  refine mem_Mset_iff.mpr ⟨fun a => t * c a, fun a => mul_mem ht (hc a), ?_⟩
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun a _ => by rw [smul_smul]

lemma sum_mem_Mset {κ : Type*} (s : Finset κ) {f : κ → Matrix n n A.carrier}
    (hf : ∀ k ∈ s, f k ∈ Mset ρ' gg) : ∑ k ∈ s, f k ∈ Mset ρ' gg := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using mem_Mset_iff.mpr ⟨0, fun a => zero_mem _, by simp⟩
  | insert k s hk ih =>
    rw [Finset.sum_insert hk]
    exact add_mem_Mset (hf k (Finset.mem_insert_self k s))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

variable (hρ' : ρ' ∈ (liftFunctor n G 𝓞 ρ₀).obj A)
variable (hgg_li : LinearIndependent (ProartinianCat.residueField (𝓞 := 𝓞)).carrier
  fun a : ι => matVal₀ ρ₀ (gg a))
variable (hgg_span : Submodule.span (ProartinianCat.residueField (𝓞 := 𝓞)).carrier
  (Set.range fun a : ι => matVal₀ ρ₀ (gg a)) = ⊤)

include hρ' hgg_li hgg_span in
lemma matVal_mem_Mset (g : G) : matVal ρ' g ∈ Mset ρ' gg := by
  obtain ⟨hmem, heq⟩ := matVal_coord_mem_and_eq_sum hρ' hgg_li hgg_span g
  exact mem_Mset_iff.mpr ⟨_, hmem, heq⟩

include hρ' hgg_li hgg_span in
lemma one_mem_Mset : (1 : Matrix n n A.carrier) ∈ Mset ρ' gg := by
  rw [← matVal_one ρ']
  exact matVal_mem_Mset hρ' hgg_li hgg_span 1

include hρ' hgg_li hgg_span in

lemma mul_mem_Mset {X Y : Matrix n n A.carrier} (hX : X ∈ Mset ρ' gg) (hY : Y ∈ Mset ρ' gg) :
    X * Y ∈ Mset ρ' gg := by
  obtain ⟨c, hc, rfl⟩ := mem_Mset_iff.mp hX
  obtain ⟨d, hd, rfl⟩ := mem_Mset_iff.mp hY
  rw [Finset.sum_mul]
  refine sum_mem_Mset _ fun a _ => ?_
  rw [smul_mul_assoc, Finset.mul_sum]
  refine smul_mem_Mset (hc a) (sum_mem_Mset _ fun b _ => ?_)
  rw [Matrix.mul_smul, ← matVal_mul]
  exact smul_mem_Mset (hd b) (matVal_mem_Mset hρ' hgg_li hgg_span _)

lemma isCompact_Mset : IsCompact (Mset ρ' gg) := by
  haveI : CompactSpace A.carrier := inferInstance
  refine IsCompact.image_of_continuousOn ?_ ?_
  ·
    have h1 : {c : ι → A.carrier | ∀ a, c a ∈ traceSubalgebra 𝓞 ρ'} =
        Set.pi Set.univ fun _ => (traceSubalgebra 𝓞 ρ' : Set A.carrier) := by
      ext c
      simp [Set.mem_pi]
    rw [h1]
    exact isCompact_univ_pi fun a => (isClosed_traceSubalgebra ρ').isCompact
  ·
    refine Continuous.continuousOn ?_
    refine continuous_finset_sum _ fun a _ => ?_
    exact (continuous_apply a).smul continuous_const

lemma isClosed_Mset : IsClosed (Mset ρ' gg) :=
  (isCompact_Mset (gg := gg) (ρ' := ρ')).isClosed

include hρ' hgg_li hgg_span in

lemma exists_mem_Mset_map_eq (Z : Matrix n n (ProartinianCat.residueField (𝓞 := 𝓞)).carrier) :
    ∃ X ∈ Mset ρ' gg, X.map (resMap A) = Z := by

  have hZ : Z ∈ Submodule.span (ProartinianCat.residueField (𝓞 := 𝓞)).carrier
      (Set.range fun a : ι => matVal₀ ρ₀ (gg a)) := hgg_span ▸ Submodule.mem_top
  obtain ⟨lam, hlam⟩ :=
    (Submodule.mem_span_range_iff_exists_fun
      (ProartinianCat.residueField (𝓞 := 𝓞)).carrier).mp hZ

  choose o ho using fun a => exists_algebraMap_resMap_eq (A := A) (lam a)
  refine ⟨∑ a, (algebraMap 𝓞 A.carrier (o a)) • matVal ρ' (gg a),
    sum_smul_mem_Mset fun a => Subalgebra.algebraMap_mem _ (o a), ?_⟩
  rw [← hlam]
  ext i j
  simp only [Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, map_sum,
    map_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [ho a]
  congr 1
  have := matVal_map_resMap hρ' (gg a)
  rw [← this, Matrix.map_apply]

include hρ' hgg_li hgg_span in

lemma exists_coeff_mem_maximalIdeal_of_mem_Mset {X : Matrix n n A.carrier}
    (hX : X ∈ Mset ρ' gg) (hXm : ∀ i j, X i j ∈ maximalIdeal A.carrier) :
    ∃ c : ι → A.carrier, (∀ a, c a ∈ traceSubalgebra 𝓞 ρ') ∧
      (∀ a, c a ∈ maximalIdeal A.carrier) ∧ X = ∑ a, c a • matVal ρ' (gg a) := by
  obtain ⟨c, hc, rfl⟩ := mem_Mset_iff.mp hX
  exact ⟨c, hc, fun a => coord_mem_maximalIdeal_of_entries_mem hρ' hgg_li hgg_span hc rfl hXm a,
    rfl⟩

end Span

section Idempotent

variable {ρ₀ : (repnFunctor n G 𝓞).obj .residueField}
variable {ρ' : G →ₜ* GL n A}
variable {ι : Type u} [Fintype ι] [DecidableEq ι] {gg : ι → G}

lemma tendsto_zero_of_mem_maximalIdeal_pow {z : ℕ → A.carrier}
    (hz : ∀ N, z N ∈ maximalIdeal A.carrier ^ (N + 1)) : Tendsto z atTop (𝓝 0) := by
  rw [(IsLinearTopology.hasBasis_open_ideal (R := A.carrier)).tendsto_right_iff]
  intro I hI
  obtain ⟨m, hm⟩ := exists_maximalIdeal_pow_le_of_isProartinian I hI
  filter_upwards [eventually_ge_atTop m] with N hN
  exact hm (Ideal.pow_le_pow_right (by omega) (hz N))

lemma tendsto_zero_of_entries_mem_maximalIdeal_pow {Z : ℕ → Matrix n n A.carrier}
    (hZ : ∀ N i j, Z N i j ∈ maximalIdeal A.carrier ^ (N + 1)) :
    Tendsto Z atTop (𝓝 0) := by
  refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
  exact tendsto_zero_of_mem_maximalIdeal_pow fun N => hZ N i j

lemma newton_identity {R : Type*} [Ring R] (e : R) :
    (3 * e ^ 2 - 2 * e ^ 3) ^ 2 - (3 * e ^ 2 - 2 * e ^ 3) =
      ((e ^ 2 - e) * (e ^ 2 - e)) * (4 * (e ^ 2 - e) - 3) := by
  have h := congrArg (Polynomial.aeval e)
    (show ((3 : Polynomial ℤ) * Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3) ^ 2 -
        (3 * Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3) =
      ((Polynomial.X ^ 2 - Polynomial.X) * (Polynomial.X ^ 2 - Polynomial.X)) *
        (4 * (Polynomial.X ^ 2 - Polynomial.X) - 3) from by ring)
  simpa only [map_sub, map_mul, map_pow, map_ofNat, Polynomial.aeval_X] using h

variable (ρ' gg) in

noncomputable def newtonSeq (x₀ : Matrix n n A.carrier) : ℕ → Matrix n n A.carrier
  | 0 => x₀
  | (k + 1) => 3 * (newtonSeq x₀ k) ^ 2 - 2 * (newtonSeq x₀ k) ^ 3

variable (hρ' : ρ' ∈ (liftFunctor n G 𝓞 ρ₀).obj A)
variable (hgg_li : LinearIndependent (ProartinianCat.residueField (𝓞 := 𝓞)).carrier
  fun a : ι => matVal₀ ρ₀ (gg a))
variable (hgg_span : Submodule.span (ProartinianCat.residueField (𝓞 := 𝓞)).carrier
  (Set.range fun a : ι => matVal₀ ρ₀ (gg a)) = ⊤)

include hρ' hgg_li hgg_span in

lemma newtonSeq_mem_Mset {x₀ : Matrix n n A.carrier} (hx₀ : x₀ ∈ Mset ρ' gg) (k : ℕ) :
    newtonSeq x₀ k ∈ Mset ρ' gg := by
  induction k with
  | zero => exact hx₀
  | succ k ih =>
    show 3 * (newtonSeq x₀ k) ^ 2 - 2 * (newtonSeq x₀ k) ^ 3 ∈ Mset ρ' gg
    have h2 : (newtonSeq x₀ k) ^ 2 ∈ Mset ρ' gg := by
      rw [pow_two]
      exact mul_mem_Mset hρ' hgg_li hgg_span ih ih
    have h3 : (newtonSeq x₀ k) ^ 3 ∈ Mset ρ' gg := by
      rw [pow_succ]
      exact mul_mem_Mset hρ' hgg_li hgg_span h2 ih
    have h32 : (3 : Matrix n n A.carrier) * (newtonSeq x₀ k) ^ 2 ∈ Mset ρ' gg := by
      rw [show (3 : Matrix n n A.carrier) * (newtonSeq x₀ k) ^ 2 =
        (newtonSeq x₀ k) ^ 2 + ((newtonSeq x₀ k) ^ 2 + (newtonSeq x₀ k) ^ 2) by noncomm_ring]
      exact add_mem_Mset h2 (add_mem_Mset h2 h2)
    have h23 : (2 : Matrix n n A.carrier) * (newtonSeq x₀ k) ^ 3 ∈ Mset ρ' gg := by
      rw [show (2 : Matrix n n A.carrier) * (newtonSeq x₀ k) ^ 3 =
        (newtonSeq x₀ k) ^ 3 + (newtonSeq x₀ k) ^ 3 by noncomm_ring]
      exact add_mem_Mset h3 h3
    exact sub_mem_Mset h32 h23

lemma newtonSeq_map_resMap {x₀ : Matrix n n A.carrier}
    {E : Matrix n n (ProartinianCat.residueField (𝓞 := 𝓞)).carrier}
    (hE : E * E = E) (hx₀ : (resMap A).mapMatrix x₀ = E) (k : ℕ) :
    (resMap A).mapMatrix (newtonSeq x₀ k) = E := by
  induction k with
  | zero => exact hx₀
  | succ k ih =>
    show (resMap A).mapMatrix (3 * (newtonSeq x₀ k) ^ 2 - 2 * (newtonSeq x₀ k) ^ 3) = E
    rw [map_sub, map_mul, map_mul, map_pow, map_pow, ih, map_ofNat, map_ofNat]
    have hE2 : E ^ 2 = E := by rw [pow_two, hE]
    have hE3 : E ^ 3 = E := by rw [pow_succ, hE2, hE]
    rw [hE2, hE3]
    noncomm_ring

lemma newtonSeq_defect_entries_mem {x₀ : Matrix n n A.carrier}
    (hx₀ : ∀ i j, (x₀ ^ 2 - x₀) i j ∈ maximalIdeal A.carrier) (k : ℕ) (i j : n) :
    ((newtonSeq x₀ k) ^ 2 - newtonSeq x₀ k) i j ∈ maximalIdeal A.carrier ^ (k + 1) := by
  induction k generalizing i j with
  | zero => (have h__af := hx₀ i j; simp at h__af ⊢; exact h__af)
  | succ k ih =>
    have hkey : (newtonSeq x₀ (k + 1)) ^ 2 - newtonSeq x₀ (k + 1) =
        (((newtonSeq x₀ k) ^ 2 - newtonSeq x₀ k) * ((newtonSeq x₀ k) ^ 2 - newtonSeq x₀ k)) *
          (4 * ((newtonSeq x₀ k) ^ 2 - newtonSeq x₀ k) - 3) := by
      show (3 * (newtonSeq x₀ k) ^ 2 - 2 * (newtonSeq x₀ k) ^ 3) ^ 2 -
        (3 * (newtonSeq x₀ k) ^ 2 - 2 * (newtonSeq x₀ k) ^ 3) = _
      exact newton_identity (newtonSeq x₀ k)
    rw [hkey]

    refine SetLike.le_def.mp ?_
      (mul_entries_mem (mul_entries_mem ih ih) (fun i j => Submodule.mem_top) i j)
    calc maximalIdeal A.carrier ^ (k + 1) * maximalIdeal A.carrier ^ (k + 1) * ⊤
        ≤ maximalIdeal A.carrier ^ (k + 1) * maximalIdeal A.carrier ^ (k + 1) :=
          Ideal.mul_le_inf.trans inf_le_left
      _ = maximalIdeal A.carrier ^ (k + 1 + (k + 1)) := (pow_add _ _ _).symm
      _ ≤ maximalIdeal A.carrier ^ (k + 1 + 1) := Ideal.pow_le_pow_right (by omega)

include hρ' hgg_li hgg_span in
set_option maxHeartbeats 4000000 in

lemma exists_idempotent_mem_Mset
    {E : Matrix n n (ProartinianCat.residueField (𝓞 := 𝓞)).carrier} (hE : E * E = E) :
    ∃ ε ∈ Mset ρ' gg, ε * ε = ε ∧ (resMap A).mapMatrix ε = E := by

  obtain ⟨x₀, hx₀mem, hx₀map⟩ := exists_mem_Mset_map_eq hρ' hgg_li hgg_span E
  have hx₀map' : (resMap A).mapMatrix x₀ = E := hx₀map

  have hx₀defect : ∀ i j, (x₀ ^ 2 - x₀) i j ∈ maximalIdeal A.carrier := by
    intro i j
    rw [← resMap_eq_zero_iff]
    have h1 : (resMap A).mapMatrix (x₀ ^ 2 - x₀) = 0 := by
      rw [map_sub, map_pow, hx₀map', pow_two, hE, sub_self]
    calc resMap A ((x₀ ^ 2 - x₀) i j) = ((resMap A).mapMatrix (x₀ ^ 2 - x₀)) i j := rfl
      _ = (0 : Matrix n n _) i j := by rw [h1]
      _ = 0 := rfl

  have hmem : ∀ k, newtonSeq x₀ k ∈ Mset ρ' gg :=
    newtonSeq_mem_Mset hρ' hgg_li hgg_span hx₀mem
  obtain ⟨ε, hεmem, hε⟩ := (isCompact_Mset (ρ' := ρ') (gg := gg)).exists_mapClusterPt
    (u := newtonSeq x₀) (f := atTop)
    (le_principal_iff.mpr (mem_map.mpr (Filter.Eventually.of_forall hmem)))
  refine ⟨ε, hεmem, ?_, ?_⟩
  ·
    have hcont : ContinuousAt (fun X : Matrix n n A.carrier => X ^ 2 - X) ε :=
      ((continuous_pow 2).sub continuous_id).continuousAt
    have hclust : MapClusterPt (ε ^ 2 - ε) atTop
        (fun k => (newtonSeq x₀ k) ^ 2 - newtonSeq x₀ k) :=
      hε.continuousAt_comp hcont
    have htend : Tendsto (fun k => (newtonSeq x₀ k) ^ 2 - newtonSeq x₀ k) atTop (𝓝 0) :=
      tendsto_zero_of_entries_mem_maximalIdeal_pow
        (fun k => newtonSeq_defect_entries_mem hx₀defect k)
    have hzero : ε ^ 2 - ε = 0 := eq_of_nhds_neBot (hclust.clusterPt.mono htend)
    have := sub_eq_zero.mp hzero
    rw [← pow_two]
    exact this
  ·
    have hcont : ContinuousAt (fun X : Matrix n n A.carrier => (resMap A).mapMatrix X) ε := by
      refine Continuous.continuousAt ?_
      show Continuous fun X : Matrix n n A.carrier => X.map (resMap A)
      exact continuous_id.matrix_map (map_continuous (toResidueField A).hom)
    have hclust : MapClusterPt ((resMap A).mapMatrix ε) atTop
        (fun k => (resMap A).mapMatrix (newtonSeq x₀ k)) :=
      hε.continuousAt_comp hcont
    have htend : Tendsto (fun k => (resMap A).mapMatrix (newtonSeq x₀ k)) atTop (𝓝 E) := by
      have h1 : (fun k => (resMap A).mapMatrix (newtonSeq x₀ k)) = fun _ => E :=
        funext fun k => newtonSeq_map_resMap hE hx₀map' k
      rw [h1]
      exact tendsto_const_nhds
    exact eq_of_nhds_neBot (hclust.clusterPt.mono htend)

end Idempotent

section Endgame

variable {ρ₀ : (repnFunctor n G 𝓞).obj .residueField}
variable {ρ' : G →ₜ* GL n A}
variable {ι : Type u} [Fintype ι] [DecidableEq ι] {gg : ι → G}

lemma solve_system {V : Type*} [AddCommGroup V] [Module A.carrier V]
    (D Dinv : Matrix ι ι A.carrier) (hDinv : Dinv * D = 1) (v rhs : ι → V)
    (hsys : ∀ a, ∑ b, D a b • v b = rhs a) (c : ι) :
    v c = ∑ a, Dinv c a • rhs a := by
  have h1 : ∑ a, Dinv c a • rhs a = ∑ a, Dinv c a • ∑ b, D a b • v b := by
    exact Finset.sum_congr rfl fun a _ => by rw [hsys a]
  rw [h1]
  have h2 : ∀ a, Dinv c a • ∑ b, D a b • v b = ∑ b, (Dinv c a * D a b) • v b := by
    intro a
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun b _ => by rw [smul_smul]
  rw [Finset.sum_congr rfl fun a _ => h2 a, Finset.sum_comm]
  have h3 : ∀ b, ∑ a, (Dinv c a * D a b) • v b = ((Dinv * D) c b) • v b := by
    intro b
    rw [← Finset.sum_smul]
    congr 1
  rw [Finset.sum_congr rfl fun b _ => h3 b, hDinv]
  have h4 : ∀ b, ((1 : Matrix ι ι A.carrier) c b) • v b =
      (if c = b then (1 : A.carrier) else 0) • v b := by
    intro b
    rw [Matrix.one_apply]
  rw [Finset.sum_congr rfl fun b _ => h4 b]
  simp [Finset.sum_ite_eq]

variable (hρ' : ρ' ∈ (liftFunctor n G 𝓞 ρ₀).obj A)
variable (hgg_li : LinearIndependent (ProartinianCat.residueField (𝓞 := 𝓞)).carrier
  fun a : ι => matVal₀ ρ₀ (gg a))
variable (hgg_span : Submodule.span (ProartinianCat.residueField (𝓞 := 𝓞)).carrier
  (Set.range fun a : ι => matVal₀ ρ₀ (gg a)) = ⊤)

variable [Nonempty n]

include hρ' hgg_li hgg_span in

lemma exists_eq_sum_smul_w (i₀ : n) {ε : Matrix n n A.carrier} (hεmem : ε ∈ Mset ρ' gg)
    (hε : ε * ε = ε)
    (hεmap : (resMap A).mapMatrix ε = Matrix.single i₀ i₀ 1)
    {w : n → Matrix n n A.carrier} (hwmem : ∀ i, w i ∈ Mset ρ' gg)
    (hwε : ∀ i, w i * ε = w i)
    (hwmap : ∀ i, (resMap A).mapMatrix (w i) = Matrix.single i i₀ 1) :
    ∀ Z ∈ Mset ρ' gg, Z * ε = Z →
      ∃ c : n → A.carrier, (∀ i, c i ∈ traceSubalgebra 𝓞 ρ') ∧ Z = ∑ i, c i • w i := by
  classical

  set v : ι → Matrix n n A.carrier := fun a => matVal ρ' (gg a) * ε with hv
  have hvmem : ∀ a, v a ∈ Mset ρ' gg :=
    fun a => mul_mem_Mset hρ' hgg_li hgg_span (matVal_mem_Mset hρ' hgg_li hgg_span _) hεmem
  have hvε : ∀ a, v a * ε = v a := fun a => by
    show matVal ρ' (gg a) * ε * ε = matVal ρ' (gg a) * ε
    rw [mul_assoc, hε]

  have step1 : ∀ Z ∈ Mset ρ' gg, Z * ε = Z →
      ∃ (t : n → A.carrier) (u : ι → A.carrier),
        (∀ i, t i ∈ traceSubalgebra 𝓞 ρ') ∧
        (∀ a, u a ∈ traceSubalgebra 𝓞 ρ') ∧ (∀ a, u a ∈ maximalIdeal A.carrier) ∧
        Z = (∑ i, t i • w i) + ∑ a, u a • v a := by
    intro Z hZmem hZε

    set Zbar := (resMap A).mapMatrix Z with hZbar
    have hZbarε : Zbar * Matrix.single i₀ i₀
        (1 : (ProartinianCat.residueField (𝓞 := 𝓞)).carrier) = Zbar := by
      rw [hZbar, ← hεmap, ← map_mul, hZε]

    choose o ho using fun i => exists_algebraMap_resMap_eq (A := A) (Zbar i i₀)
    set t : n → A.carrier := fun i => algebraMap 𝓞 A.carrier (o i) with ht
    have htT : ∀ i, t i ∈ traceSubalgebra 𝓞 ρ' := fun i => Subalgebra.algebraMap_mem _ (o i)

    have hdiff_mem : Z - ∑ i, t i • w i ∈ Mset ρ' gg :=
      sub_mem_Mset hZmem (sum_mem_Mset _ fun i _ => smul_mem_Mset (htT i) (hwmem i))
    have hdiff_red : (resMap A).mapMatrix (Z - ∑ i, t i • w i) = 0 := by
      rw [map_sub]
      have h1 : (resMap A).mapMatrix (∑ i, t i • w i) = Zbar := by
        rw [map_sum]
        have h2 : ∀ i, (resMap A).mapMatrix (t i • w i) =
            Zbar i i₀ • Matrix.single i i₀ (1 : (ProartinianCat.residueField (𝓞 := 𝓞)).carrier)
            := by
          intro i
          have h3 : (resMap A).mapMatrix (t i • w i) =
              resMap A (t i) • (resMap A).mapMatrix (w i) := by
            ext i' j'
            show resMap A ((t i • w i) i' j') = _
            rw [Matrix.smul_apply, smul_eq_mul, map_mul]
            rfl
          rw [h3, hwmap i, ht]
          rw [ho i]
        rw [Finset.sum_congr rfl fun i _ => h2 i]

        ext i' j'
        rw [Matrix.sum_apply]
        by_cases hj' : j' = i₀
        · rw [hj']
          rw [show ∑ i, (Zbar i i₀ • Matrix.single i i₀
              (1 : (ProartinianCat.residueField (𝓞 := 𝓞)).carrier)) i' i₀ =
              ∑ i, if i = i' then Zbar i i₀ else 0 from
            Finset.sum_congr rfl fun i _ => by
              rw [Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
              by_cases h : i = i' <;> simp [h]]
          rw [Finset.sum_ite_eq' Finset.univ i' fun i => Zbar i i₀]
          simp
        · rw [show ∑ i, (Zbar i i₀ • Matrix.single i i₀
              (1 : (ProartinianCat.residueField (𝓞 := 𝓞)).carrier)) i' j' = 0 from
            Finset.sum_eq_zero fun i _ => by
              rw [Matrix.smul_apply, Matrix.single_apply_of_col_ne _ _ (Ne.symm hj'),
                smul_zero]]

          symm
          calc Zbar i' j'
              = (Zbar * Matrix.single i₀ i₀
                  (1 : (ProartinianCat.residueField (𝓞 := 𝓞)).carrier)) i' j' := by
                rw [hZbarε]
            _ = 0 := by
                rw [Matrix.mul_apply]
                exact Finset.sum_eq_zero fun k _ => by
                  rw [Matrix.single_apply, if_neg fun h => hj' h.2.symm, mul_zero]
      rw [h1, sub_self]
    have hdiff_entries : ∀ i j, (Z - ∑ i, t i • w i) i j ∈ maximalIdeal A.carrier := by
      intro i j
      rw [← resMap_eq_zero_iff]
      calc resMap A ((Z - ∑ i, t i • w i) i j)
          = ((resMap A).mapMatrix (Z - ∑ i, t i • w i)) i j := rfl
        _ = (0 : Matrix n n _) i j := by rw [hdiff_red]
        _ = 0 := rfl

    obtain ⟨u, huT, hum, hueq⟩ :=
      exists_coeff_mem_maximalIdeal_of_mem_Mset hρ' hgg_li hgg_span hdiff_mem hdiff_entries
    refine ⟨t, u, htT, huT, hum, ?_⟩

    have h5 : Z - ∑ i, t i • w i = (Z - ∑ i, t i • w i) * ε := by
      rw [sub_mul, hZε, Finset.sum_mul]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by rw [smul_mul_assoc, hwε i]
    have h6 : (∑ a, u a • matVal ρ' (gg a)) * ε = ∑ a, u a • v a := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun a _ => by rw [smul_mul_assoc]
    have h7 : Z - ∑ i, t i • w i = ∑ a, u a • v a := by
      rw [h5, hueq, h6]
    rw [← h7]
    abel

  choose s uu hsT huuT huum hveq using fun a => step1 (v a) (hvmem a) (hvε a)

  set Usub : Matrix ι ι (traceSubalgebra 𝓞 ρ') :=
    Matrix.of fun a b => ⟨uu a b, huuT a b⟩ with hUsub
  set Dsub : Matrix ι ι (traceSubalgebra 𝓞 ρ') := 1 - Usub with hDsub
  set D : Matrix ι ι A.carrier :=
    ((traceSubalgebra 𝓞 ρ').val.toRingHom.mapMatrix : Matrix ι ι (traceSubalgebra 𝓞 ρ') →+*
      Matrix ι ι A.carrier) Dsub with hD

  have hDab : ∀ a b, D a b = (if a = b then (1 : A.carrier) else 0) - uu a b := by
    intro a b
    show ((Dsub a b : traceSubalgebra 𝓞 ρ') : A.carrier) = _
    rw [show Dsub a b = (1 : Matrix ι ι (traceSubalgebra 𝓞 ρ')) a b - Usub a b from rfl,
      Matrix.one_apply]
    rw [show Usub a b = (⟨uu a b, huuT a b⟩ : traceSubalgebra 𝓞 ρ') from rfl]
    by_cases h : a = b
    · simp only [if_pos h]
      rfl
    · simp only [if_neg h]
      rfl

  have hDdet : IsUnit D.det := by
    refine isUnit_of_resMap_ne_zero (a := D.det) ?_
    have h1 : resMap A D.det = ((resMap A).mapMatrix D).det := RingHom.map_det _ _
    have h2 : (resMap A).mapMatrix D = 1 := by
      ext a b
      show resMap A (D a b) = (1 : Matrix ι ι (ProartinianCat.residueField (𝓞 := 𝓞)).carrier) a b
      rw [hDab a b, map_sub]
      have h4 : resMap A (uu a b) = 0 := resMap_eq_zero_iff.mpr (huum a b)
      rw [h4, sub_zero, Matrix.one_apply]
      by_cases h : a = b <;> simp [h]
    rw [h1, h2, Matrix.det_one]
    exact one_ne_zero
  have hDsubdet : IsUnit Dsub.det := by
    have h1 : (((Dsub).det : traceSubalgebra 𝓞 ρ') : A.carrier) = D.det :=
      RingHom.map_det ((traceSubalgebra 𝓞 ρ').val.toRingHom) Dsub
    exact ProartinianCat.isUnit_of_isUnit_val (traceSubalgebra 𝓞 ρ')
      (isClosed_traceSubalgebra ρ') _ (h1 ▸ hDdet)

  set Dinv : Matrix ι ι A.carrier :=
    ((traceSubalgebra 𝓞 ρ').val.toRingHom.mapMatrix : Matrix ι ι (traceSubalgebra 𝓞 ρ') →+*
      Matrix ι ι A.carrier) Dsub⁻¹ with hDinv
  have hDinvD : Dinv * D = 1 := by
    rw [hDinv, hD, ← map_mul, Matrix.nonsing_inv_mul _ hDsubdet, map_one]
  have hDinvT : ∀ a b, Dinv a b ∈ traceSubalgebra 𝓞 ρ' := by
    intro a b
    show (((Dsub⁻¹) a b : traceSubalgebra 𝓞 ρ') : A.carrier) ∈ _
    exact SetLike.coe_mem _

  have hsys : ∀ a, ∑ b, D a b • v b = ∑ i, s a i • w i := by
    intro a
    have h1 : ∀ b, D a b • v b =
        (if a = b then (1 : A.carrier) else 0) • v b - uu a b • v b := by
      intro b
      rw [hDab a b, sub_smul]
    rw [Finset.sum_congr rfl fun b _ => h1 b, Finset.sum_sub_distrib]
    have h3 : ∑ b, (if a = b then (1 : A.carrier) else 0) • v b = v a := by
      simp [Finset.sum_ite_eq]
    rw [h3, hveq a]
    abel

  have hvsol : ∀ c, v c = ∑ a, Dinv c a • ∑ i, s a i • w i :=
    fun c => solve_system D Dinv hDinvD v (fun a => ∑ i, s a i • w i) hsys c

  have hvw : ∀ c, ∃ d : n → A.carrier, (∀ i, d i ∈ traceSubalgebra 𝓞 ρ') ∧
      v c = ∑ i, d i • w i := by
    intro c
    refine ⟨fun i => ∑ a, Dinv c a * s a i, fun i => Subalgebra.sum_mem _ fun a _ =>
      Subalgebra.mul_mem _ (hDinvT c a) (hsT a i), ?_⟩
    rw [hvsol c]
    rw [Finset.sum_congr rfl fun a (_ : a ∈ Finset.univ) =>
      (Finset.smul_sum (r := Dinv c a) (f := fun i => s a i • w i) (s := Finset.univ))]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    show ∑ a, Dinv c a • (s a i • w i) = (∑ a, Dinv c a * s a i) • w i
    rw [Finset.sum_smul]
    exact Finset.sum_congr rfl fun a _ => smul_smul _ _ _

  intro Z hZmem hZε
  obtain ⟨t, u, htT, huT, hum, hZeq⟩ := step1 Z hZmem hZε
  choose d hdT hdeq using hvw
  refine ⟨fun i => t i + ∑ a, u a * d a i, fun i => add_mem (htT i)
    (Subalgebra.sum_mem _ fun a _ => Subalgebra.mul_mem _ (huT a) (hdT a i)), ?_⟩
  rw [hZeq]
  have h8 : ∀ a, u a • v a = ∑ i, (u a * d a i) • w i := by
    intro a
    rw [hdeq a, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_smul]
  rw [Finset.sum_congr rfl fun a (_ : a ∈ Finset.univ) => h8 a, Finset.sum_comm,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  show t i • w i + ∑ a, (u a * d a i) • w i = (t i + ∑ a, u a * d a i) • w i
  rw [add_smul, Finset.sum_smul]

end Endgame

section Main

variable {ρ₀ : (repnFunctor n G 𝓞).obj .residueField}
variable {ρ' : G →ₜ* GL n A}

set_option maxHeartbeats 4000000 in

theorem descends_of_mem_liftFunctor
    [Representation.IsAbsolutelyIrreducible.{u} (toRepresentation ρ₀)]
    (hρ' : ρ' ∈ (liftFunctor n G 𝓞 ρ₀).obj A) :
    TraceAlgebra.Descends ρ' := by
  classical

  rcases isEmpty_or_nonempty n with hn | hn
  · exact ⟨1, one_mem _, fun g i j => (IsEmpty.false i).elim⟩

  obtain ⟨ι, hι₁, hι₂, gg, hgg_li, hgg_span⟩ := exists_basis_choice ρ₀
  obtain ⟨i₀⟩ := hn
  haveI : Nonempty n := ⟨i₀⟩

  have hE : Matrix.single i₀ i₀ (1 : (ProartinianCat.residueField (𝓞 := 𝓞)).carrier) *
      Matrix.single i₀ i₀ 1 = Matrix.single i₀ i₀ 1 := by
    rw [Matrix.single_mul_single_same, one_mul]
  obtain ⟨ε, hεmem, hεidem, hεmap⟩ :=
    exists_idempotent_mem_Mset hρ' hgg_li hgg_span hE

  choose W hWmem hWmap using fun i : n =>
    exists_mem_Mset_map_eq hρ' hgg_li hgg_span
      (Matrix.single i i₀ (1 : (ProartinianCat.residueField (𝓞 := 𝓞)).carrier))
  set w : n → Matrix n n A.carrier := fun i => W i * ε with hwdef
  have hwmem : ∀ i, w i ∈ Mset ρ' gg :=
    fun i => mul_mem_Mset hρ' hgg_li hgg_span (hWmem i) hεmem
  have hwε : ∀ i, w i * ε = w i := fun i => by
    show W i * ε * ε = W i * ε
    rw [mul_assoc, hεidem]
  have hwmap : ∀ i, (resMap A).mapMatrix (w i) = Matrix.single i i₀ 1 := fun i => by
    show (resMap A).mapMatrix (W i * ε) = _
    rw [map_mul, hεmap]
    have h1 : (resMap A).mapMatrix (W i) = Matrix.single i i₀ 1 := hWmap i
    rw [h1, Matrix.single_mul_single_same, one_mul]

  have hspan := exists_eq_sum_smul_w hρ' hgg_li hgg_span i₀ hεmem hεidem hεmap hwmem hwε hwmap

  set P : Matrix n n A.carrier := Matrix.of fun i j => w j i i₀ with hP
  have hPred : (resMap A).mapMatrix P = 1 := by
    ext i j
    show resMap A (w j i i₀) = (1 : Matrix n n (ProartinianCat.residueField (𝓞 := 𝓞)).carrier) i j
    calc resMap A (w j i i₀)
        = ((resMap A).mapMatrix (w j)) i i₀ := rfl
      _ = (Matrix.single j i₀ (1 : (ProartinianCat.residueField (𝓞 := 𝓞)).carrier)) i i₀ := by
          rw [hwmap j]
      _ = (1 : Matrix n n (ProartinianCat.residueField (𝓞 := 𝓞)).carrier) i j := by
          rw [Matrix.single_apply, Matrix.one_apply]
          by_cases h : i = j
          · subst h; simp
          · rw [if_neg fun hc => h (hc.1.symm), if_neg h]
  have hPdet : IsUnit P.det := by
    refine isUnit_of_resMap_ne_zero (a := P.det) ?_
    have h1 : resMap A P.det = ((resMap A).mapMatrix P).det := RingHom.map_det _ _
    rw [h1, hPred, Matrix.det_one]
    exact one_ne_zero

  set Pu : GL n A.carrier := (Matrix.isUnit_iff_isUnit_det P).mpr hPdet |>.unit with hPu
  have hPuval : (Pu : Matrix n n A.carrier) = P := IsUnit.unit_spec _

  have hPker : ConjAct.toConjAct Pu⁻¹ ∈ conjKer (n := n) A := by
    rw [mem_conjKer_iff, ConjAct.ofConjAct_toConjAct, map_inv]
    rw [show Matrix.GeneralLinearGroup.map (ProartinianCat.toResidueField A).hom.toRingHom Pu
        = 1 from Units.ext (by
      show ((Pu : Matrix n n A.carrier)).map (resMap A) = (1 : Matrix n n _)
      rw [hPuval]
      exact hPred)]
    exact inv_one

  refine ⟨ConjAct.toConjAct Pu⁻¹, hPker, fun g i j => ?_⟩

  have hcol : ∀ j : n, ∃ c : n → A.carrier, (∀ i, c i ∈ traceSubalgebra 𝓞 ρ') ∧
      matVal ρ' g * w j = ∑ i, c i • w i := by
    intro j
    refine hspan (matVal ρ' g * w j)
      (mul_mem_Mset hρ' hgg_li hgg_span (matVal_mem_Mset hρ' hgg_li hgg_span g) (hwmem j)) ?_
    rw [mul_assoc, hwε j]
  choose c hcT hceq using hcol

  set C : Matrix n n A.carrier := Matrix.of fun i j => c j i with hC
  have hcomm : matVal ρ' g * P = P * C := by
    ext i' j'
    rw [Matrix.mul_apply, Matrix.mul_apply]
    calc ∑ k, matVal ρ' g i' k * P k j'
        = (matVal ρ' g * w j') i' i₀ := by rw [Matrix.mul_apply]; rfl
      _ = (∑ k, c j' k • w k) i' i₀ := by rw [hceq j']
      _ = ∑ k, c j' k * w k i' i₀ := by
          rw [Matrix.sum_apply]
          exact Finset.sum_congr rfl fun k _ => by rw [Matrix.smul_apply, smul_eq_mul]
      _ = ∑ k, P i' k * C k j' := by
          exact Finset.sum_congr rfl fun k _ => by
            rw [mul_comm (c j' k) (w k i' i₀)]; rfl

  have hconj : ((ConjAct.toConjAct Pu⁻¹ • ρ') g : GL n A.carrier) = (Pu⁻¹ * ρ' g * Pu) := by
    rw [conjAct_smul_apply, ConjAct.ofConjAct_toConjAct, inv_inv]
  have hval : (((ConjAct.toConjAct Pu⁻¹ • ρ') g : GL n A.carrier) : Matrix n n A.carrier) = C
      := by
    rw [hconj]
    show ((Pu⁻¹ : GL n A.carrier) : Matrix n n A.carrier) * matVal ρ' g *
      ((Pu : GL n A.carrier) : Matrix n n A.carrier) = C
    rw [hPuval, mul_assoc, hcomm, ← mul_assoc]
    have h2 : ((Pu⁻¹ : GL n A.carrier) : Matrix n n A.carrier) * P = 1 := by
      rw [← hPuval]
      exact Pu.inv_val
    rw [h2, one_mul]
  rw [hval]
  exact hcT j i

end Main

end Carayol
end Deformation

theorem solution
    {n : Type} [Fintype n] [DecidableEq n] {G : Type u} [Group G] [TopologicalSpace G]
    {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞] [Finite (IsLocalRing.ResidueField 𝓞)]
    {A : Deformation.ProartinianCat 𝓞}
    {ρ₀ : (Deformation.repnFunctor n G 𝓞).obj Deformation.ProartinianCat.residueField}
    [Representation.IsAbsolutelyIrreducible.{u} (Deformation.toRepresentation ρ₀)]
    {ρ' : G →ₜ* GL n A} (hρ' : ρ' ∈ (Deformation.liftFunctor n G 𝓞 ρ₀).obj A) :
    Deformation.TraceAlgebra.Descends ρ' :=
  Deformation.Carayol.descends_of_mem_liftFunctor hρ'

end S_Deformation_TraceAlgebra_descends
end P2MW
export P2MW.S_Deformation_TraceAlgebra_descends (solution)
