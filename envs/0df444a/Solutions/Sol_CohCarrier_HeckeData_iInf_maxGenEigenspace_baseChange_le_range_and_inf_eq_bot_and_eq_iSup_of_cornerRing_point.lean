-- Prove2me | solution 1 for CohCarrier.HeckeData.iInf_maxGenEigenspace_baseChange_le_range_and_inf_eq_bot_and_eq_iSup_of_cornerRing_point
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/0b513c63-7bf0-51a1-a871-dcc0b2975194

import Definitions.Def_CohCarrier_HeckeData
import Definitions.Def_IharaLemma_IdempotentSplitting
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic

import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.MvPolynomial.Tower
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.RingTheory.Finiteness.Nilpotent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_HeckeData_iInf_maxGenEigenspace_baseChange_le_range_and_inf_eq_bot_and_eq_iSup_of_cornerRing_point

set_option autoImplicit false

open Polynomial IsLocalRing
open scoped TensorProduct IsMulCommutative

namespace CDecompAux

theorem eval_eq_zero_of_aeval_apply_eq_zero_of_mem_maxGenEigenspace
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (f : Module.End F V) (μ : F) (P : Polynomial F) {v : V}
    (hv : v ∈ f.maxGenEigenspace μ) (hv0 : v ≠ 0) (hP : Polynomial.aeval f P v = 0) :
    P.eval μ = 0 := by
  by_contra h
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace f μ v).mp hv
  have hcop : IsCoprime ((Polynomial.X - Polynomial.C μ) ^ k) P :=
    (((Polynomial.irreducible_X_sub_C μ).coprime_iff_not_dvd).mpr
      (fun hd => h (Polynomial.dvd_iff_isRoot.mp hd))).pow_left
  obtain ⟨a, b, hab⟩ := hcop
  have key := congrArg (fun Q => Polynomial.aeval f Q v) hab
  simp only [map_add, map_mul, map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, map_one,
    LinearMap.add_apply, Module.End.mul_apply, Module.End.one_apply,
    Algebra.algebraMap_eq_smul_one] at key
  rw [hk, hP, map_zero, map_zero, zero_add] at key
  exact hv0 key.symm

end CDecompAux

namespace CDecompAux

open Polynomial

theorem charpoly_eq_X_sub_C_pow_of_isNilpotent_sub_smul
    {K M : Type*} [Field K] [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    (φ : Module.End K M) (c : K) (h : IsNilpotent (φ - c • 1)) :
    φ.charpoly = (X - C c) ^ Module.finrank K M := by
  have h1 := h.charpoly_eq_X_pow_finrank
  rw [LinearMap.charpoly_sub_smul] at h1
  have h2 : φ.charpoly = (φ.charpoly.comp (X + C c)).comp (X - C c) := by
    rw [Polynomial.comp_assoc, add_comp, X_comp, C_comp, sub_add_cancel, comp_X]
  rw [h2, h1, Polynomial.X_pow_comp]

theorem map_charpoly_eq_X_sub_C_pow_of_isNilpotent_baseChange_sub_smul
    {R M k : Type*} [CommRing R] [Nontrivial R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Free R M] [Field k] [Algebra R k]
    (f : Module.End R M) (c : k) (h : IsNilpotent (f.baseChange k - c • 1)) :
    f.charpoly.map (algebraMap R k) = (X - C c) ^ f.charpoly.natDegree := by
  rw [LinearMap.charpoly_natDegree, ← LinearMap.charpoly_baseChange,
    charpoly_eq_X_sub_C_pow_of_isNilpotent_sub_smul _ c h, Module.finrank_baseChange]

end CDecompAux

namespace CDecompAux

variable {𝒪 : Type} [CommRing 𝒪] {H : Type} [AddCommGroup H] [Module 𝒪 H]
  {k : Type} [Field k] [Algebra 𝒪 k] (D : CohCarrier.HeckeData 𝒪 H k)
  (Sp : IharaLemma.IdempotentSplitting ↥D.opSubalgebra)

theorem opSubalgebra_smul_eq_apply (b : ↥D.opSubalgebra) (x : H) :
    b • x = (b : Module.End 𝒪 H) x := rfl

theorem isIdempotentElem_coe_e (i : Fin Sp.n) :
    IsIdempotentElem ((Sp.e i : ↥D.opSubalgebra) : Module.End 𝒪 H) := by
  have h := (Sp.idem i).eq
  have := congrArg (Subtype.val : ↥D.opSubalgebra → Module.End 𝒪 H) h
  simpa [IsIdempotentElem] using this

theorem commute_coe_e_op (i : Fin Sp.n) (g : D.Gen) :
    Commute ((Sp.e i : ↥D.opSubalgebra) : Module.End 𝒪 H) (D.op g) := by
  have hg : D.op g ∈ D.opSubalgebra := Algebra.subset_adjoin (Set.mem_range_self g)
  have h : Sp.e i * (⟨D.op g, hg⟩ : ↥D.opSubalgebra) = ⟨D.op g, hg⟩ * Sp.e i := mul_comm _ _
  exact congrArg (Subtype.val : ↥D.opSubalgebra → Module.End 𝒪 H) h

theorem coe_e_eq_subtype_comp_toCorner (i : Fin Sp.n) :
    ((Sp.e i : ↥D.opSubalgebra) : Module.End 𝒪 H) =
      ((IharaLemma.cornerSubmodule (M := H) (Sp.e i)).subtype.restrictScalars 𝒪) ∘ₗ
        ((IharaLemma.toCorner (M := H) (Sp.e i)).restrictScalars 𝒪) := by
  ext x
  rfl

variable (F : Type) [CommRing F] [Algebra 𝒪 F]

theorem range_cornerSubtype_baseChange_eq (i : Fin Sp.n) :
    LinearMap.range (((IharaLemma.cornerSubmodule (M := H) (Sp.e i)).subtype.restrictScalars 𝒪).baseChange F)
      = LinearMap.range (((Sp.e i : ↥D.opSubalgebra) : Module.End 𝒪 H).baseChange F) := by
  rw [coe_e_eq_subtype_comp_toCorner D Sp i, LinearMap.baseChange_comp,
    LinearMap.range_comp_of_range_eq_top]
  apply LinearMap.range_eq_top_of_surjective
  rw [LinearMap.baseChange_eq_ltensor]
  exact LinearMap.lTensor_surjective F
    (by
      intro y
      obtain ⟨x, hx⟩ := (LinearMap.surjective_rangeRestrict _ : Function.Surjective
        (IharaLemma.toCorner (M := H) (Sp.e i))) y
      exact ⟨x, hx⟩)

theorem isIdempotentElem_baseChange_coe_e (i : Fin Sp.n) :
    IsIdempotentElem (((Sp.e i : ↥D.opSubalgebra) : Module.End 𝒪 H).baseChange F) := by
  show _ * _ = _
  rw [← LinearMap.baseChange_mul, (isIdempotentElem_coe_e D Sp i).eq]

theorem commute_baseChange_coe_e_op (i : Fin Sp.n) (g : D.Gen) :
    Commute (((Sp.e i : ↥D.opSubalgebra) : Module.End 𝒪 H).baseChange F) ((D.op g).baseChange F) := by
  show _ * _ = _ * _
  rw [← LinearMap.baseChange_mul, ← LinearMap.baseChange_mul, (commute_coe_e_op D Sp i g).eq]

theorem mem_range_cornerSubtype_baseChange_iff (i : Fin Sp.n) (x : F ⊗[𝒪] H) :
    x ∈ LinearMap.range (((IharaLemma.cornerSubmodule (M := H) (Sp.e i)).subtype.restrictScalars 𝒪).baseChange F)
      ↔ (((Sp.e i : ↥D.opSubalgebra) : Module.End 𝒪 H).baseChange F) x = x := by
  rw [range_cornerSubtype_baseChange_eq]
  constructor
  · rintro ⟨y, rfl⟩
    exact LinearMap.congr_fun (isIdempotentElem_baseChange_coe_e D Sp F i).eq y
  · intro hx
    exact ⟨x, hx⟩

end CDecompAux

namespace CDecompAux

variable {𝒪 : Type} [CommRing 𝒪] {H : Type} [AddCommGroup H] [Module 𝒪 H]
  {k : Type} [Field k] [Algebra 𝒪 k] (D : CohCarrier.HeckeData 𝒪 H k)
  (Sp : IharaLemma.IdempotentSplitting ↥D.opSubalgebra)
  (F : Type) [CommRing F] [Algebra 𝒪 F]

theorem sum_coe_e : ∑ j, ((Sp.e j : ↥D.opSubalgebra) : Module.End 𝒪 H) = 1 := by
  have := congrArg (Subtype.val : ↥D.opSubalgebra → Module.End 𝒪 H) Sp.coi.complete
  simpa using this

theorem sum_baseChange_coe_e :
    ∑ j, ((Sp.e j : ↥D.opSubalgebra) : Module.End 𝒪 H).baseChange F = 1 := by
  have := congrArg (Module.End.baseChangeHom 𝒪 F H) (sum_coe_e D Sp)
  simp [map_sum] at this
  exact this

theorem sum_baseChange_coe_e_apply (x : F ⊗[𝒪] H) :
    ∑ j, (((Sp.e j : ↥D.opSubalgebra) : Module.End 𝒪 H).baseChange F) x = x := by
  have := LinearMap.congr_fun (sum_baseChange_coe_e D Sp F) x
  simpa using this

theorem baseChange_coe_e_apply_mem_iInf (i : Fin Sp.n) (a : D.Gen → F) {x : F ⊗[𝒪] H}
    (hx : x ∈ ⨅ g : D.Gen, Module.End.maxGenEigenspace ((D.op g).baseChange F) (a g)) :
    (((Sp.e i : ↥D.opSubalgebra) : Module.End 𝒪 H).baseChange F) x ∈
      ⨅ g : D.Gen, Module.End.maxGenEigenspace ((D.op g).baseChange F) (a g) := by
  rw [Submodule.mem_iInf] at hx ⊢
  intro g
  exact Module.End.mapsTo_maxGenEigenspace_of_comm
    (commute_baseChange_coe_e_op D Sp F i g).symm (a g) (hx g)

theorem map_baseChange_coe_e_iInf_eq (i : Fin Sp.n) (a : D.Gen → F) :
    Submodule.map (((Sp.e i : ↥D.opSubalgebra) : Module.End 𝒪 H).baseChange F)
        (⨅ g : D.Gen, Module.End.maxGenEigenspace ((D.op g).baseChange F) (a g)) =
      (⨅ g : D.Gen, Module.End.maxGenEigenspace ((D.op g).baseChange F) (a g)) ⊓
        LinearMap.range (((IharaLemma.cornerSubmodule (M := H) (Sp.e i)).subtype.restrictScalars 𝒪).baseChange F) := by
  ext y
  rw [Submodule.mem_map, Submodule.mem_inf]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨baseChange_coe_e_apply_mem_iInf D Sp F i a hx, ?_⟩
    rw [mem_range_cornerSubtype_baseChange_iff]
    exact LinearMap.congr_fun (isIdempotentElem_baseChange_coe_e D Sp F i).eq x
  · rintro ⟨hy, hy'⟩
    exact ⟨y, hy, (mem_range_cornerSubtype_baseChange_iff D Sp F i y).mp hy'⟩

theorem iInf_maxGenEigenspace_le_range_of_forall_ne (i₀ : Fin Sp.n) (a : D.Gen → F)
    (h : ∀ j : Fin Sp.n, j ≠ i₀ →
      (⨅ g : D.Gen, Module.End.maxGenEigenspace ((D.op g).baseChange F) (a g)) ⊓
        LinearMap.range (((IharaLemma.cornerSubmodule (M := H) (Sp.e j)).subtype.restrictScalars 𝒪).baseChange F)
          = ⊥) :
    (⨅ g : D.Gen, Module.End.maxGenEigenspace ((D.op g).baseChange F) (a g)) ≤
      LinearMap.range (((IharaLemma.cornerSubmodule (M := H) (Sp.e i₀)).subtype.restrictScalars 𝒪).baseChange F) := by
  intro x hx
  rw [mem_range_cornerSubtype_baseChange_iff]
  have hzero : ∀ j : Fin Sp.n, j ≠ i₀ →
      (((Sp.e j : ↥D.opSubalgebra) : Module.End 𝒪 H).baseChange F) x = 0 := fun j hj => by
    have hmem : (((Sp.e j : ↥D.opSubalgebra) : Module.End 𝒪 H).baseChange F) x ∈
        (⨅ g : D.Gen, Module.End.maxGenEigenspace ((D.op g).baseChange F) (a g)) ⊓
          LinearMap.range (((IharaLemma.cornerSubmodule (M := H) (Sp.e j)).subtype.restrictScalars 𝒪).baseChange F) := by
      rw [← map_baseChange_coe_e_iInf_eq]
      exact ⟨x, hx, rfl⟩
    rw [h j hj] at hmem
    exact (Submodule.mem_bot F).mp hmem
  calc (((Sp.e i₀ : ↥D.opSubalgebra) : Module.End 𝒪 H).baseChange F) x
      = ∑ j, (((Sp.e j : ↥D.opSubalgebra) : Module.End 𝒪 H).baseChange F) x := by
        rw [Finset.sum_eq_single i₀ (fun j _ hj => hzero j hj) (fun h' => absurd (Finset.mem_univ _) h')]
    _ = x := sum_baseChange_coe_e_apply D Sp F x

end CDecompAux

namespace CDecompAux

section generic

theorem aeval_comp_eq_comp_aeval_of_comp_eq {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (ι : N →ₗ[R] M) (T : Module.End R M) (T' : Module.End R N)
    (h : T ∘ₗ ι = ι ∘ₗ T') (P : Polynomial R) :
    Polynomial.aeval T P ∘ₗ ι = ι ∘ₗ Polynomial.aeval T' P := by
  have hn : ∀ n : ℕ, (T ^ n) ∘ₗ ι = ι ∘ₗ (T' ^ n) := by
    intro n
    induction n with
    | zero =>
      rw [pow_zero, pow_zero, Module.End.one_eq_id, Module.End.one_eq_id, LinearMap.id_comp,
        LinearMap.comp_id]
    | succ n ih =>
      rw [pow_succ, pow_succ, Module.End.mul_eq_comp, Module.End.mul_eq_comp, LinearMap.comp_assoc, h,
        ← LinearMap.comp_assoc, ih, LinearMap.comp_assoc]
  refine P.induction_on' (fun p q hp hq => ?_) (fun n a => ?_)
  · rw [map_add, map_add, LinearMap.add_comp, LinearMap.comp_add, hp, hq]
  · rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, Module.End.mul_eq_comp,
      Module.End.mul_eq_comp, LinearMap.comp_assoc, hn n, ← LinearMap.comp_assoc,
      ← LinearMap.comp_assoc]
    congr 1
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, LinearMap.smul_comp,
      LinearMap.comp_smul, Module.End.one_eq_id, Module.End.one_eq_id, LinearMap.id_comp,
      LinearMap.comp_id]

end generic

section corner

variable {𝒪 : Type} [CommRing 𝒪] {H : Type} [AddCommGroup H] [Module 𝒪 H]
  {k : Type} [Field k] [Algebra 𝒪 k] (D : CohCarrier.HeckeData 𝒪 H k)
  (Sp : IharaLemma.IdempotentSplitting ↥D.opSubalgebra)

abbrev opMem (g : D.Gen) : ↥D.opSubalgebra := ⟨D.op g, Algebra.subset_adjoin (Set.mem_range_self g)⟩

def Corner (i : Fin Sp.n) : Type := ↥(IharaLemma.cornerSubmodule (M := H) (Sp.e i))

noncomputable scoped instance instAddCommGroupCorner (i : Fin Sp.n) : AddCommGroup (Corner D Sp i) :=
  inferInstanceAs (AddCommGroup ↥(IharaLemma.cornerSubmodule (M := H) (Sp.e i)))

noncomputable scoped instance instModuleCorner (i : Fin Sp.n) : Module 𝒪 (Corner D Sp i) :=
  inferInstanceAs (Module 𝒪 ↥(IharaLemma.cornerSubmodule (M := H) (Sp.e i)))

noncomputable scoped instance instModuleCornerRingCorner (i : Fin Sp.n) : Module (Sp.CornerRing i) (Corner D Sp i) :=
  inferInstanceAs (Module (Sp.CornerRing i) ↥(IharaLemma.cornerSubmodule (M := H) (Sp.e i)))

scoped instance instIsScalarTowerCorner (i : Fin Sp.n) : IsScalarTower 𝒪 (Sp.CornerRing i) (Corner D Sp i) :=
  inferInstanceAs (IsScalarTower 𝒪 (Sp.CornerRing i) ↥(IharaLemma.cornerSubmodule (M := H) (Sp.e i)))

noncomputable def cornerIncl (i : Fin Sp.n) : Corner D Sp i →ₗ[𝒪] H :=
  (IharaLemma.cornerSubmodule (M := H) (Sp.e i)).subtype.restrictScalars 𝒪

noncomputable def cornerProj (i : Fin Sp.n) : H →ₗ[𝒪] Corner D Sp i :=
  (IharaLemma.toCorner (M := H) (Sp.e i)).restrictScalars 𝒪

noncomputable def opCorner (i : Fin Sp.n) (g : D.Gen) : Module.End 𝒪 (Corner D Sp i) :=
  ((opMem D g) • (LinearMap.id : ↥(IharaLemma.cornerSubmodule (M := H) (Sp.e i)) →ₗ[↥D.opSubalgebra]
      ↥(IharaLemma.cornerSubmodule (M := H) (Sp.e i)))).restrictScalars 𝒪

theorem cornerIncl_injective (i : Fin Sp.n) : Function.Injective (cornerIncl D Sp i) :=
  Subtype.val_injective

theorem cornerIncl_opCorner (i : Fin Sp.n) (g : D.Gen) (x : Corner D Sp i) :
    cornerIncl D Sp i (opCorner D Sp i g x) = D.op g (cornerIncl D Sp i x) := rfl

theorem cornerIncl_comp_opCorner (i : Fin Sp.n) (g : D.Gen) :
    cornerIncl D Sp i ∘ₗ opCorner D Sp i g = D.op g ∘ₗ cornerIncl D Sp i := rfl

theorem cornerIncl_cornerProj (i : Fin Sp.n) (v : H) :
    cornerIncl D Sp i (cornerProj D Sp i v) = (Sp.e i : ↥D.opSubalgebra) • v := rfl

theorem cornerIncl_comp_cornerProj (i : Fin Sp.n) :
    cornerIncl D Sp i ∘ₗ cornerProj D Sp i = ((Sp.e i : ↥D.opSubalgebra) : Module.End 𝒪 H) := rfl

theorem cornerProj_comp_cornerIncl (i : Fin Sp.n) :
    cornerProj D Sp i ∘ₗ cornerIncl D Sp i = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply cornerIncl_injective D Sp i
  exact IharaLemma.IdempotentSplitting.e_smul_coe Sp i
    (show ↥(IharaLemma.cornerSubmodule (M := H) (Sp.e i)) from x)

theorem cornerProj_surjective (i : Fin Sp.n) : Function.Surjective (cornerProj D Sp i) := fun y =>
  ⟨cornerIncl D Sp i y, LinearMap.congr_fun (cornerProj_comp_cornerIncl D Sp i) y⟩

scoped instance finite_corner [Module.Finite 𝒪 H] (i : Fin Sp.n) : Module.Finite 𝒪 (Corner D Sp i) :=
  Module.Finite.of_surjective _ (cornerProj_surjective D Sp i)

scoped instance projective_corner [Module.Projective 𝒪 H] (i : Fin Sp.n) :
    Module.Projective 𝒪 (Corner D Sp i) :=
  Module.Projective.of_split _ _ (cornerProj_comp_cornerIncl D Sp i)

scoped instance free_corner [IsLocalRing 𝒪] [Module.Finite 𝒪 H] [Module.Free 𝒪 H] (i : Fin Sp.n) :
    Module.Free 𝒪 (Corner D Sp i) :=
  Module.free_of_flat_of_isLocalRing

noncomputable abbrev charpolyCorner [IsLocalRing 𝒪] [Module.Finite 𝒪 H] [Module.Free 𝒪 H]
    (i : Fin Sp.n) (g : D.Gen) : Polynomial 𝒪 :=
  (opCorner D Sp i g).charpoly

theorem aeval_opCorner_charpolyCorner [IsLocalRing 𝒪] [Module.Finite 𝒪 H] [Module.Free 𝒪 H]
    (i : Fin Sp.n) (g : D.Gen) :
    Polynomial.aeval (opCorner D Sp i g) (charpolyCorner D Sp i g) = 0 :=
  LinearMap.aeval_self_charpoly _

theorem charpolyCorner_monic [IsLocalRing 𝒪] [Module.Finite 𝒪 H] [Module.Free 𝒪 H]
    (i : Fin Sp.n) (g : D.Gen) : (charpolyCorner D Sp i g).Monic :=
  LinearMap.charpoly_monic _

variable (F : Type) [CommRing F] [Algebra 𝒪 F]

theorem range_cornerSubtype_baseChange_eq_range_cornerIncl (i : Fin Sp.n) :
    LinearMap.range (((IharaLemma.cornerSubmodule (M := H) (Sp.e i)).subtype.restrictScalars 𝒪).baseChange F)
      = LinearMap.range ((cornerIncl D Sp i).baseChange F) := by
  rw [range_cornerSubtype_baseChange_eq, ← cornerIncl_comp_cornerProj D Sp i, LinearMap.baseChange_comp,
    LinearMap.range_comp_of_range_eq_top]
  apply LinearMap.range_eq_top_of_surjective
  rw [LinearMap.baseChange_eq_ltensor]
  exact LinearMap.lTensor_surjective F (cornerProj_surjective D Sp i)

theorem baseChange_op_comp_cornerIncl (i : Fin Sp.n) (g : D.Gen) :
    (D.op g).baseChange F ∘ₗ (cornerIncl D Sp i).baseChange F =
      (cornerIncl D Sp i).baseChange F ∘ₗ (opCorner D Sp i g).baseChange F := by
  rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, cornerIncl_comp_opCorner]

theorem aeval_baseChange_op_charpolyCorner_eq_zero [IsLocalRing 𝒪] [Module.Finite 𝒪 H]
    [Module.Free 𝒪 H] (i : Fin Sp.n) (g : D.Gen) {y : F ⊗[𝒪] H}
    (hy : y ∈ LinearMap.range ((cornerIncl D Sp i).baseChange F)) :
    Polynomial.aeval ((D.op g).baseChange F) ((charpolyCorner D Sp i g).map (algebraMap 𝒪 F)) y = 0 := by
  obtain ⟨z, rfl⟩ := hy
  have h := LinearMap.congr_fun (aeval_comp_eq_comp_aeval_of_comp_eq _ _ _
    (baseChange_op_comp_cornerIncl D Sp F i g) ((charpolyCorner D Sp i g).map (algebraMap 𝒪 F))) z
  rw [LinearMap.comp_apply] at h
  rw [h, LinearMap.comp_apply, Polynomial.aeval_map_algebraMap,
    show (opCorner D Sp i g).baseChange F = Module.End.baseChangeHom 𝒪 F _ (opCorner D Sp i g) from rfl,
    Polynomial.aeval_algHom_apply, aeval_opCorner_charpolyCorner, map_zero, LinearMap.zero_apply, map_zero]

end corner

end CDecompAux
p2m_reactivate "P2MW.S_CohCarrier_HeckeData_iInf_maxGenEigenspace_baseChange_le_range_and_inf_eq_bot_and_eq_iSup_of_cornerRing_point.CDecompAux"

namespace CDecompAux

section finiteness

variable {𝒪 : Type} [CommRing 𝒪] {H : Type} [AddCommGroup H] [Module 𝒪 H]
  {k : Type} [Field k] [Algebra 𝒪 k] (D : CohCarrier.HeckeData 𝒪 H k)
  (Sp : IharaLemma.IdempotentSplitting ↥D.opSubalgebra)

theorem finite_opSubalgebra [IsNoetherianRing 𝒪] [Module.Finite 𝒪 H] [Module.Free 𝒪 H] :
    Module.Finite 𝒪 ↥D.opSubalgebra :=
  Module.Finite.of_injective D.opSubalgebra.val.toLinearMap Subtype.val_injective

theorem toCornerRing_surjective (i : Fin Sp.n) : Function.Surjective (Sp.toCornerRing i) := by
  rintro ⟨_, a, rfl⟩
  exact ⟨a, rfl⟩

theorem finite_cornerRing [IsNoetherianRing 𝒪] [Module.Finite 𝒪 H] [Module.Free 𝒪 H] (i : Fin Sp.n) :
    Module.Finite 𝒪 (Sp.CornerRing i) := by
  haveI := finite_opSubalgebra D
  exact Module.Finite.of_surjective
    (IsScalarTower.toAlgHom 𝒪 (↥D.opSubalgebra) (Sp.CornerRing i)).toLinearMap
    (toCornerRing_surjective D Sp i)

noncomputable def act (i : Fin Sp.n) : Sp.CornerRing i →ₐ[𝒪] Module.End 𝒪 (Corner D Sp i) :=
  Algebra.lsmul 𝒪 𝒪 (Corner D Sp i)

theorem cornerIncl_act (i : Fin Sp.n) (z : Sp.CornerRing i) (v : Corner D Sp i) :
    cornerIncl D Sp i (act D Sp i z v) = (z : ↥D.opSubalgebra) • cornerIncl D Sp i v := by
  simp only [act, Algebra.lsmul_coe]
  rfl

theorem act_toCornerRing_opMem (i : Fin Sp.n) (g : D.Gen) :
    act D Sp i (Sp.toCornerRing i (opMem D g)) = opCorner D Sp i g := by
  apply LinearMap.ext
  intro v
  apply cornerIncl_injective D Sp i
  set w : ↥(IharaLemma.cornerSubmodule (M := H) (Sp.e i)) :=
    (show ↥(IharaLemma.cornerSubmodule (M := H) (Sp.e i)) from v) with hw
  have hv : cornerIncl D Sp i v = (w : H) := rfl
  rw [cornerIncl_act, cornerIncl_opCorner, IharaLemma.IdempotentSplitting.coe_toCornerRing, hv, mul_smul,
    IharaLemma.IdempotentSplitting.e_smul_coe, mul_smul]
  have hmem : (opMem D g) • (w : H) ∈ IharaLemma.cornerSubmodule (M := H) (Sp.e i) := by
    refine ⟨(opMem D g) • (w : H), ?_⟩
    show (Sp.e i : ↥D.opSubalgebra) • ((opMem D g) • (w : H)) = _
    rw [smul_smul, mul_comm, ← smul_smul, IharaLemma.IdempotentSplitting.e_smul_coe]
  exact IharaLemma.IdempotentSplitting.e_smul_coe Sp i ⟨_, hmem⟩

end finiteness
p2m_reactivate "P2MW.S_CohCarrier_HeckeData_iInf_maxGenEigenspace_baseChange_le_range_and_inf_eq_bot_and_eq_iSup_of_cornerRing_point.CDecompAux"

section artin

variable {R : Type} [CommRing R] [IsLocalRing R] {C : Type} [CommRing C] [Algebra R C] [IsLocalRing C]
  [Module.Finite R C]

theorem isNilpotent_one_tmul_of_character_eq_zero (π : C →ₐ[R] ResidueField R) {y : C} (hy : π y = 0) :
    IsNilpotent ((1 : ResidueField R) ⊗ₜ[R] y : ResidueField R ⊗[R] C) := by
  let πA : ResidueField R ⊗[R] C →ₐ[ResidueField R] ResidueField R :=
    Algebra.TensorProduct.lift (AlgHom.id (ResidueField R) (ResidueField R)) π (fun _ _ => Commute.all _ _)
  have hπA : πA ((1 : ResidueField R) ⊗ₜ[R] y) = 0 := by
    simp [πA, Algebra.TensorProduct.lift_tmul, hy]
  haveI : Nontrivial (ResidueField R ⊗[R] C) := πA.toRingHom.domain_nontrivial
  haveI : IsLocalRing (ResidueField R ⊗[R] C) :=
    IsLocalRing.of_surjective'
      (Algebra.TensorProduct.includeRight : C →ₐ[R] ResidueField R ⊗[R] C).toRingHom
      (by
        have h := TensorProduct.mk_surjective R C (ResidueField R)
          (by rw [IsLocalRing.ResidueField.algebraMap_eq]; exact IsLocalRing.residue_surjective)
        intro z
        obtain ⟨c, hc⟩ := h z
        exact ⟨c, hc⟩)
  haveI : IsArtinianRing (ResidueField R ⊗[R] C) :=
    IsArtinianRing.of_finite (ResidueField R) (ResidueField R ⊗[R] C)
  have hmem : ((1 : ResidueField R) ⊗ₜ[R] y : ResidueField R ⊗[R] C) ∈
      IsLocalRing.maximalIdeal (ResidueField R ⊗[R] C) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact (hu.map πA).ne_zero hπA
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := ResidueField R ⊗[R] C)
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hn
  refine ⟨n, ?_⟩
  have := Ideal.pow_mem_pow hmem n
  rw [hn] at this
  exact (Submodule.mem_bot _).mp this

omit [IsLocalRing C] [Module.Finite R C] in

theorem isNilpotent_baseChange_of_isNilpotent_one_tmul {M : Type} [AddCommGroup M] [Module R M]
    (ρ : C →ₐ[R] Module.End R M) {y : C}
    (hy : IsNilpotent ((1 : ResidueField R) ⊗ₜ[R] y : ResidueField R ⊗[R] C)) :
    IsNilpotent ((ρ y).baseChange (ResidueField R)) := by
  let Φ : ResidueField R ⊗[R] C →ₐ[ResidueField R] Module.End (ResidueField R) (ResidueField R ⊗[R] M) :=
    Algebra.TensorProduct.lift (Algebra.ofId (ResidueField R) _)
      ((Module.End.baseChangeHom R (ResidueField R) M).comp ρ)
      (fun a x => Algebra.commute_algebraMap_left a _)
  have hΦ : Φ ((1 : ResidueField R) ⊗ₜ[R] y) = (ρ y).baseChange (ResidueField R) := by
    simp only [Φ, Algebra.TensorProduct.lift_tmul, map_one, one_mul, AlgHom.comp_apply]
    rfl
  rw [← hΦ]
  exact hy.map Φ

end artin
p2m_reactivate "P2MW.S_CohCarrier_HeckeData_iInf_maxGenEigenspace_baseChange_le_range_and_inf_eq_bot_and_eq_iSup_of_cornerRing_point.CDecompAux"

section residue

variable {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪]
  {H : Type} [AddCommGroup H] [Module 𝒪 H] [Module.Finite 𝒪 H] [Module.Free 𝒪 H]
  (D : CohCarrier.HeckeData 𝒪 H (ResidueField 𝒪))
  (Sp : IharaLemma.IdempotentSplitting ↥D.opSubalgebra) (i₀ : Fin Sp.n)
  (πk : Sp.CornerRing i₀ →ₐ[𝒪] ResidueField 𝒪)
  (hπk : ∀ g : D.Gen, πk (Sp.toCornerRing i₀
    ⟨D.op g, Algebra.subset_adjoin (Set.mem_range_self g)⟩) = D.θbar g)

include hπk in

theorem isNilpotent_baseChange_opCorner_sub (g : D.Gen) :
    IsNilpotent ((opCorner D Sp i₀ g).baseChange (ResidueField 𝒪) -
      D.θbar g • (1 : Module.End (ResidueField 𝒪) (ResidueField 𝒪 ⊗[𝒪] Corner D Sp i₀))) := by
  obtain ⟨θ, hθ⟩ := IsLocalRing.residue_surjective (D.θbar g)
  haveI := finite_cornerRing D Sp i₀
  set y : Sp.CornerRing i₀ :=
    Sp.toCornerRing i₀ (opMem D g) - algebraMap 𝒪 (Sp.CornerRing i₀) θ with hy_def
  have hy : πk y = 0 := by
    rw [hy_def, map_sub, AlgHom.commutes, IsLocalRing.ResidueField.algebraMap_eq, hθ]
    exact sub_eq_zero.mpr (hπk g)
  have hnil := isNilpotent_baseChange_of_isNilpotent_one_tmul (R := 𝒪) (C := Sp.CornerRing i₀)
    (act D Sp i₀) (isNilpotent_one_tmul_of_character_eq_zero (R := 𝒪) (C := Sp.CornerRing i₀) πk hy)
  have hact : act D Sp i₀ y = opCorner D Sp i₀ g - θ • (1 : Module.End 𝒪 (Corner D Sp i₀)) := by
    rw [hy_def, map_sub, act_toCornerRing_opMem, AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
  rw [hact, LinearMap.baseChange_sub, LinearMap.baseChange_smul, LinearMap.baseChange_one] at hnil
  rwa [← hθ, ← IsLocalRing.ResidueField.algebraMap_eq, algebraMap_smul]

include hπk in

theorem map_residue_charpolyCorner_eq (g : D.Gen) :
    (charpolyCorner D Sp i₀ g).map (IsLocalRing.residue 𝒪) =
      (Polynomial.X - Polynomial.C (D.θbar g)) ^ (charpolyCorner D Sp i₀ g).natDegree := by
  rw [← IsLocalRing.ResidueField.algebraMap_eq]
  exact map_charpoly_eq_X_sub_C_pow_of_isNilpotent_baseChange_sub_smul (opCorner D Sp i₀ g) (D.θbar g)
    (isNilpotent_baseChange_opCorner_sub D Sp i₀ πk hπk g)

end residue
p2m_reactivate "P2MW.S_CohCarrier_HeckeData_iInf_maxGenEigenspace_baseChange_le_range_and_inf_eq_bot_and_eq_iSup_of_cornerRing_point.CDecompAux"

end CDecompAux
p2m_reactivate "P2MW.S_CohCarrier_HeckeData_iInf_maxGenEigenspace_baseChange_le_range_and_inf_eq_bot_and_eq_iSup_of_cornerRing_point.CDecompAux"

namespace CDecompAux

section clause2

variable {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪]
  {H : Type} [AddCommGroup H] [Module 𝒪 H] [Module.Finite 𝒪 H] [Module.Free 𝒪 H]
  (D : CohCarrier.HeckeData 𝒪 H (ResidueField 𝒪))
  (Sp : IharaLemma.IdempotentSplitting ↥D.opSubalgebra) (i₀ : Fin Sp.n)
  (πk : Sp.CornerRing i₀ →ₐ[𝒪] ResidueField 𝒪)
  (hπk : ∀ g : D.Gen, πk (Sp.toCornerRing i₀
    ⟨D.op g, Algebra.subset_adjoin (Set.mem_range_self g)⟩) = D.θbar g)
  (F : Type) [Field F] [Algebra 𝒪 F]

include hπk in
theorem forall_residualTest_of_inf_ne_bot (a : D.Gen → F)
    (h : (⨅ g : D.Gen, Module.End.maxGenEigenspace ((D.op g).baseChange F) (a g)) ⊓
      LinearMap.range (((IharaLemma.cornerSubmodule (M := H) (Sp.e i₀)).subtype.restrictScalars 𝒪).baseChange F)
        ≠ ⊥) (g : D.Gen) :
    ∃ R : Polynomial 𝒪, R.Monic ∧ Polynomial.aeval (a g) R = 0 ∧
      R.map (IsLocalRing.residue 𝒪) = (Polynomial.X - Polynomial.C (D.θbar g)) ^ R.natDegree := by
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp h
  obtain ⟨hvV, hvC⟩ := Submodule.mem_inf.mp hv
  refine ⟨charpolyCorner D Sp i₀ g, charpolyCorner_monic D Sp i₀ g, ?_,
    map_residue_charpolyCorner_eq D Sp i₀ πk hπk g⟩
  rw [range_cornerSubtype_baseChange_eq_range_cornerIncl] at hvC
  have hP := aeval_baseChange_op_charpolyCorner_eq_zero D Sp F i₀ g hvC
  have hroot := eval_eq_zero_of_aeval_apply_eq_zero_of_mem_maxGenEigenspace ((D.op g).baseChange F) (a g)
    ((charpolyCorner D Sp i₀ g).map (algebraMap 𝒪 F)) ((Submodule.mem_iInf _).mp hvV g) hv0 hP
  rwa [Polynomial.eval_map, ← Polynomial.aeval_def] at hroot

include hπk in

theorem iInf_maxGenEigenspace_inf_range_eq_bot_of_exists_not (a : D.Gen → F)
    (ha : ∃ g : D.Gen, ¬ (∃ R : Polynomial 𝒪, R.Monic ∧ Polynomial.aeval (a g) R = 0 ∧
        R.map (IsLocalRing.residue 𝒪) = (Polynomial.X - Polynomial.C (D.θbar g)) ^ R.natDegree)) :
    (⨅ g : D.Gen, Module.End.maxGenEigenspace ((D.op g).baseChange F) (a g)) ⊓
      LinearMap.range (((IharaLemma.cornerSubmodule (M := H) (Sp.e i₀)).subtype.restrictScalars 𝒪).baseChange F)
        = ⊥ := by
  by_contra h
  obtain ⟨g, hg⟩ := ha
  exact hg (forall_residualTest_of_inf_ne_bot D Sp i₀ πk hπk F a h g)

end clause2
p2m_reactivate "P2MW.S_CohCarrier_HeckeData_iInf_maxGenEigenspace_baseChange_le_range_and_inf_eq_bot_and_eq_iSup_of_cornerRing_point.CDecompAux"

end CDecompAux
p2m_reactivate "P2MW.S_CohCarrier_HeckeData_iInf_maxGenEigenspace_baseChange_le_range_and_inf_eq_bot_and_eq_iSup_of_cornerRing_point.CDecompAux"

namespace CDecompAux

theorem iSup_inf_eq_biSup_of_pass {ι α : Type*} [CompleteLattice α] (V : ι → α) (C : α)
    (pass : ι → Prop) (h1 : ∀ i, pass i → V i ≤ C) (h2 : ∀ i, ¬ pass i → V i ⊓ C = ⊥) :
    ⨆ i, V i ⊓ C = ⨆ (i : ι) (_ : pass i), V i := by
  apply le_antisymm
  · refine iSup_le fun i => ?_
    by_cases hi : pass i
    · exact le_trans inf_le_left (le_iSup₂ (f := fun i (_ : pass i) => V i) i hi)
    · rw [h2 i hi]
      exact bot_le
  · refine iSup₂_le fun i hi => ?_
    exact le_trans (le_inf le_rfl (h1 i hi)) (le_iSup (fun i => V i ⊓ C) i)

variable {𝒪 : Type} [CommRing 𝒪] {H : Type} [AddCommGroup H] [Module 𝒪 H]
  {k : Type} [Field k] [Algebra 𝒪 k] (D : CohCarrier.HeckeData 𝒪 H k)
  (Sp : IharaLemma.IdempotentSplitting ↥D.opSubalgebra)
  (F : Type) [Field F] [Algebra 𝒪 F]

theorem commute_baseChange_op_op (g h : D.Gen) :
    Commute ((D.op g).baseChange F) ((D.op h).baseChange F) := by
  have := congrArg (Module.End.baseChangeHom 𝒪 F H) (D.comm g h)
  rw [map_mul, map_mul] at this
  exact this

theorem iSup_iInf_maxGenEigenspace_baseChange_op_eq_top [Module.Finite 𝒪 H] [IsAlgClosed F] :
    ⨆ a : D.Gen → F, ⨅ g : D.Gen, Module.End.maxGenEigenspace ((D.op g).baseChange F) (a g) = ⊤ :=
  Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
    (fun g => (D.op g).baseChange F) (fun g h _ => commute_baseChange_op_op D F g h)
    (fun _ => Module.End.iSup_maxGenEigenspace_eq_top _)

theorem range_cornerSubtype_baseChange_eq_iSup_inf [Module.Finite 𝒪 H] [IsAlgClosed F]
    (i₀ : Fin Sp.n) :
    LinearMap.range (((IharaLemma.cornerSubmodule (M := H) (Sp.e i₀)).subtype.restrictScalars 𝒪).baseChange F) =
      ⨆ a : D.Gen → F, (⨅ g : D.Gen, Module.End.maxGenEigenspace ((D.op g).baseChange F) (a g)) ⊓
        LinearMap.range (((IharaLemma.cornerSubmodule (M := H) (Sp.e i₀)).subtype.restrictScalars 𝒪).baseChange F) := by
  simp_rw [← map_baseChange_coe_e_iInf_eq D Sp F i₀, ← Submodule.map_iSup,
    iSup_iInf_maxGenEigenspace_baseChange_op_eq_top D F, Submodule.map_top]
  exact range_cornerSubtype_baseChange_eq D Sp F i₀

theorem range_cornerSubtype_baseChange_eq_biSup_of_pass [Module.Finite 𝒪 H] [IsAlgClosed F]
    (i₀ : Fin Sp.n) (pass : (D.Gen → F) → Prop)
    (h1 : ∀ a : D.Gen → F, pass a →
      (⨅ g : D.Gen, Module.End.maxGenEigenspace ((D.op g).baseChange F) (a g)) ≤
        LinearMap.range (((IharaLemma.cornerSubmodule (M := H) (Sp.e i₀)).subtype.restrictScalars 𝒪).baseChange F))
    (h2 : ∀ a : D.Gen → F, ¬ pass a →
      (⨅ g : D.Gen, Module.End.maxGenEigenspace ((D.op g).baseChange F) (a g)) ⊓
        LinearMap.range (((IharaLemma.cornerSubmodule (M := H) (Sp.e i₀)).subtype.restrictScalars 𝒪).baseChange F) = ⊥) :
    LinearMap.range (((IharaLemma.cornerSubmodule (M := H) (Sp.e i₀)).subtype.restrictScalars 𝒪).baseChange F) =
      ⨆ (a : D.Gen → F) (_ : pass a),
        ⨅ g : D.Gen, Module.End.maxGenEigenspace ((D.op g).baseChange F) (a g) := by
  rw [range_cornerSubtype_baseChange_eq_iSup_inf D Sp F i₀]
  exact iSup_inf_eq_biSup_of_pass _ _ pass h1 h2

end CDecompAux
p2m_reactivate "P2MW.S_CohCarrier_HeckeData_iInf_maxGenEigenspace_baseChange_le_range_and_inf_eq_bot_and_eq_iSup_of_cornerRing_point.CDecompAux"

namespace CDecompAux

section LPass

variable {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] {F : Type} [Field F] [Algebra 𝒪 F]

theorem aeval_ne_zero_of_forall_residualTest {σ : Type} (c : σ → ResidueField 𝒪) (a : σ → F)
    (hinj : Function.Injective (algebraMap 𝒪 F))
    (hpass : ∀ s, ∃ R : Polynomial 𝒪, R.Monic ∧ Polynomial.aeval (a s) R = 0 ∧
        R.map (IsLocalRing.residue 𝒪) = (Polynomial.X - Polynomial.C (c s)) ^ R.natDegree)
    (Q : MvPolynomial σ 𝒪) (hQ : MvPolynomial.eval₂ (IsLocalRing.residue 𝒪) c Q ≠ 0) :
    MvPolynomial.aeval a Q ≠ 0 := by
  classical
  intro hQ0
  apply hQ

  let A : Subalgebra 𝒪 F := integralClosure 𝒪 F
  have hker : RingHom.ker (algebraMap 𝒪 A) ≤ maximalIdeal 𝒪 := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    have hx' : algebraMap 𝒪 F x = 0 := by
      have := congrArg (Subtype.val : A → F) hx
      simpa using this
    have hx0 : x = 0 := hinj (by rw [hx', map_zero])
    rw [hx0]
    exact zero_mem _
  obtain ⟨𝔫, h𝔫max, h𝔫⟩ :=
    Ideal.exists_ideal_over_maximal_of_isIntegral (S := A) (maximalIdeal 𝒪) hker
  have ha : ∀ s, IsIntegral 𝒪 (a s) := fun s => by
    obtain ⟨R, hRm, hRa, -⟩ := hpass s
    exact ⟨R, hRm, by rwa [Polynomial.aeval_def] at hRa⟩
  let a' : σ → A := fun s => ⟨a s, ha s⟩
  let π : A →+* A ⧸ 𝔫 := Ideal.Quotient.mk 𝔫
  have hle : maximalIdeal 𝒪 ≤ 𝔫.comap (algebraMap 𝒪 A) := h𝔫.ge
  let ι : ResidueField 𝒪 →+* A ⧸ 𝔫 := Ideal.quotientMap 𝔫 (algebraMap 𝒪 A) hle
  letI : Field (A ⧸ 𝔫) := Ideal.Quotient.field 𝔫
  have hι : π.comp (algebraMap 𝒪 A) = ι.comp (IsLocalRing.residue 𝒪) := by
    ext r
    exact (Ideal.quotientMap_mk (f := algebraMap 𝒪 A) (H := hle) (x := r)).symm

  have hroot : ∀ s, π (a' s) = ι (c s) := by
    intro s
    obtain ⟨R, hRm, hRa, hRres⟩ := hpass s
    have h1 : Polynomial.aeval (a' s) R = 0 := by
      apply Subtype.ext
      rw [show ((Polynomial.aeval (a' s) R : A) : F) = Polynomial.aeval (a s) R from
        Polynomial.aeval_subalgebra_coe R A (a' s)]
      simpa using hRa
    have h2 : π (Polynomial.aeval (a' s) R) = 0 := by rw [h1, map_zero]
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂, hι, ← Polynomial.eval₂_map, hRres,
      Polynomial.eval₂_pow, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C] at h2
    exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero h2)

  have hQA : MvPolynomial.aeval a' Q = 0 := by
    apply Subtype.val_injective
    have h := congrArg (fun φ : MvPolynomial σ 𝒪 →ₐ[𝒪] F => φ Q) (MvPolynomial.comp_aeval (R := 𝒪) a' A.val)
    change ((MvPolynomial.aeval a' Q : A) : F) = MvPolynomial.aeval a Q at h
    rw [h]
    simpa using hQ0
  have h3 : π (MvPolynomial.aeval a' Q) = 0 := by rw [hQA, map_zero]
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left, hι,
    show (π : A → A ⧸ 𝔫) ∘ a' = ι ∘ c from funext hroot, ← MvPolynomial.eval₂_comp_left] at h3
  exact (map_eq_zero_iff ι ι.injective).mp h3

end LPass
p2m_reactivate "P2MW.S_CohCarrier_HeckeData_iInf_maxGenEigenspace_baseChange_le_range_and_inf_eq_bot_and_eq_iSup_of_cornerRing_point.CDecompAux"

end CDecompAux
p2m_reactivate "P2MW.S_CohCarrier_HeckeData_iInf_maxGenEigenspace_baseChange_le_range_and_inf_eq_bot_and_eq_iSup_of_cornerRing_point.CDecompAux"

namespace CDecompAux

section ScalarNil

variable {F A : Type} [Field F] [CommRing A] [Algebra F A]

theorem isNilpotent_aeval_sub_algebraMap_eval {σ : Type} (t : σ → A) (a : σ → F)
    (hn : ∀ g, IsNilpotent (t g - algebraMap F A (a g))) (P : MvPolynomial σ F) :
    IsNilpotent (MvPolynomial.aeval t P - algebraMap F A (MvPolynomial.eval a P)) := by
  let I : Ideal A := nilradical A
  have hmk : ∀ g, Ideal.Quotient.mkₐ F I (t g) = algebraMap F (A ⧸ I) (a g) := fun g => by
    rw [Ideal.Quotient.mkₐ_eq_mk, ← Ideal.Quotient.mk_algebraMap]
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (mem_nilradical.mpr (hn g))
  rw [← mem_nilradical, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
  have h1 : (Ideal.Quotient.mkₐ F I) (MvPolynomial.aeval t P) =
      MvPolynomial.aeval (fun g => Ideal.Quotient.mkₐ F I (t g)) P := by
    rw [← MvPolynomial.comp_aeval, AlgHom.comp_apply]
  have h2 : (fun g => Ideal.Quotient.mkₐ F I (t g)) = (algebraMap F (A ⧸ I)) ∘ a := funext hmk
  calc Ideal.Quotient.mk I (MvPolynomial.aeval t P)
      = Ideal.Quotient.mkₐ F I (MvPolynomial.aeval t P) := rfl
    _ = MvPolynomial.aeval ((algebraMap F (A ⧸ I)) ∘ a) P := by rw [h1, h2]
    _ = algebraMap F (A ⧸ I) (MvPolynomial.aeval a P) := MvPolynomial.aeval_algebraMap_apply _ a P
    _ = Ideal.Quotient.mk I (algebraMap F A (MvPolynomial.eval a P)) := by
        rw [Ideal.Quotient.mk_algebraMap]
        rfl

theorem eq_one_of_isIdempotentElem_of_isNilpotent_sub_algebraMap (E : A) (hE : IsIdempotentElem E)
    (c : F) (hN : IsNilpotent (E - algebraMap F A c)) (hc : c ≠ 0) : E = 1 := by
  set N := E - algebraMap F A c with hNdef
  have hEN : E = algebraMap F A c + N := by rw [hNdef]; ring
  have key : algebraMap F A (c ^ 2 - c) = N * (1 - 2 * algebraMap F A c - N) := by
    have h := hE.eq
    rw [hEN] at h
    rw [map_sub, map_pow]
    linear_combination h
  have hnil : IsNilpotent (algebraMap F A (c ^ 2 - c)) := by
    rw [key]
    exact Commute.isNilpotent_mul_right (Commute.all _ _) hN
  by_cases hc1 : c = 1
  · subst hc1
    have h1E : IsIdempotentElem (1 - E) := hE.one_sub
    have hn1 : IsNilpotent (1 - E) := by
      have : 1 - E = -N := by rw [hNdef, map_one]; ring
      rw [this]
      exact hN.neg
    have := h1E.eq_zero_of_isNilpotent hn1
    exact (sub_eq_zero.mp this).symm
  · have hu : c ^ 2 - c ≠ 0 := by
      intro h0
      have : c * (c - 1) = 0 := by linear_combination h0
      rcases mul_eq_zero.mp this with h | h
      · exact hc h
      · exact hc1 (sub_eq_zero.mp h)
    have h1 : IsNilpotent (1 : A) := by
      have : (1 : A) = algebraMap F A ((c ^ 2 - c)⁻¹) * algebraMap F A (c ^ 2 - c) := by
        rw [← map_mul, inv_mul_cancel₀ hu, map_one]
      rw [this]
      exact Commute.isNilpotent_mul_left (Commute.all _ _) hnil
    obtain ⟨n, hn⟩ := h1
    rw [one_pow] at hn
    haveI : Subsingleton A := subsingleton_of_zero_eq_one hn.symm
    exact Subsingleton.elim _ _

end ScalarNil
p2m_reactivate "P2MW.S_CohCarrier_HeckeData_iInf_maxGenEigenspace_baseChange_le_range_and_inf_eq_bot_and_eq_iSup_of_cornerRing_point.CDecompAux"

end CDecompAux
p2m_reactivate "P2MW.S_CohCarrier_HeckeData_iInf_maxGenEigenspace_baseChange_le_range_and_inf_eq_bot_and_eq_iSup_of_cornerRing_point.CDecompAux"

namespace CDecompAux

section Clause1

variable {𝒪 : Type} [CommRing 𝒪] {H : Type} [AddCommGroup H] [Module 𝒪 H]
    {k : Type} [Field k] [Algebra 𝒪 k] (D : CohCarrier.HeckeData 𝒪 H k)
    (Sp : IharaLemma.IdempotentSplitting ↥D.opSubalgebra)

theorem exists_mvPolynomial_aeval_eq (b : ↥D.opSubalgebra) :
    ∃ P : MvPolynomial D.Gen 𝒪, MvPolynomial.aeval
      (fun g => (⟨D.op g, Algebra.subset_adjoin (Set.mem_range_self g)⟩ : ↥D.opSubalgebra)) P = b := by
  let op' : D.Gen → ↥D.opSubalgebra := fun g => ⟨D.op g, Algebra.subset_adjoin (Set.mem_range_self g)⟩
  let S : Subalgebra 𝒪 ↥D.opSubalgebra := (MvPolynomial.aeval op').range
  have hle : D.opSubalgebra ≤ S.map D.opSubalgebra.val := by
    show Algebra.adjoin 𝒪 (Set.range D.op) ≤ S.map D.opSubalgebra.val
    refine Algebra.adjoin_le ?_
    rintro _ ⟨g, rfl⟩
    exact ⟨op' g, ⟨MvPolynomial.X g, by simp [op']⟩, rfl⟩
  obtain ⟨s, ⟨P, hP⟩, hs⟩ := hle b.2
  exact ⟨P, hP.trans (Subtype.ext hs)⟩

variable (F : Type) [CommRing F] [Algebra 𝒪 F] (a : D.Gen → F)

theorem commute_baseChange_coe_op (b : ↥D.opSubalgebra) (g : D.Gen) :
    Commute ((b : Module.End 𝒪 H).baseChange F) ((D.op g).baseChange F) := by
  have hg : D.op g ∈ D.opSubalgebra := Algebra.subset_adjoin (Set.mem_range_self g)
  have h : b * (⟨D.op g, hg⟩ : ↥D.opSubalgebra) = ⟨D.op g, hg⟩ * b := mul_comm _ _
  have := congrArg (Module.End.baseChangeHom 𝒪 F H)
    (congrArg (Subtype.val : ↥D.opSubalgebra → Module.End 𝒪 H) h)
  rw [Subalgebra.coe_mul, Subalgebra.coe_mul, map_mul, map_mul] at this
  exact this

theorem baseChange_coe_apply_mem_iInf (b : ↥D.opSubalgebra) {x : F ⊗[𝒪] H}
    (hx : x ∈ ⨅ g : D.Gen, Module.End.maxGenEigenspace ((D.op g).baseChange F) (a g)) :
    ((b : Module.End 𝒪 H).baseChange F) x ∈
      ⨅ g : D.Gen, Module.End.maxGenEigenspace ((D.op g).baseChange F) (a g) := by
  rw [Submodule.mem_iInf] at hx ⊢
  intro g
  exact Module.End.mapsTo_maxGenEigenspace_of_comm
    (commute_baseChange_coe_op D F b g).symm (a g) (hx g)

noncomputable def restrictHom : ↥D.opSubalgebra →+*
    Module.End F ↥(⨅ g : D.Gen, Module.End.maxGenEigenspace ((D.op g).baseChange F) (a g)) where
  toFun b := ((b : Module.End 𝒪 H).baseChange F).restrict
    (fun x hx => baseChange_coe_apply_mem_iInf D F a b hx)
  map_one' := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rw [LinearMap.coe_restrict_apply]
    simp
  map_mul' b c := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rw [LinearMap.coe_restrict_apply, Module.End.mul_apply, LinearMap.coe_restrict_apply,
      LinearMap.coe_restrict_apply, Subalgebra.coe_mul, Module.End.mul_eq_comp, LinearMap.baseChange_comp,
      LinearMap.comp_apply]
  map_zero' := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rw [LinearMap.coe_restrict_apply]
    simp
  map_add' b c := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rw [LinearMap.coe_restrict_apply]
    simp

@[scoped simp] theorem coe_restrictHom_apply (b : ↥D.opSubalgebra)
    (x : ↥(⨅ g : D.Gen, Module.End.maxGenEigenspace ((D.op g).baseChange F) (a g))) :
    ((restrictHom D F a b x : ↥(⨅ g : D.Gen, Module.End.maxGenEigenspace ((D.op g).baseChange F) (a g))) :
      F ⊗[𝒪] H) = ((b : Module.End 𝒪 H).baseChange F) x := rfl

theorem restrictHom_algebraMap_apply (r : 𝒪)
    (x : ↥(⨅ g : D.Gen, Module.End.maxGenEigenspace ((D.op g).baseChange F) (a g))) :
    restrictHom D F a (algebraMap 𝒪 ↥D.opSubalgebra r) x = algebraMap 𝒪 F r • x := by
  apply Subtype.ext
  rw [coe_restrictHom_apply, Subalgebra.coe_algebraMap, Submodule.coe_smul]
  rw [Algebra.algebraMap_eq_smul_one, LinearMap.baseChange_smul, LinearMap.baseChange_one]
  simp [algebraMap_smul]

end Clause1
p2m_reactivate "P2MW.S_CohCarrier_HeckeData_iInf_maxGenEigenspace_baseChange_le_range_and_inf_eq_bot_and_eq_iSup_of_cornerRing_point.CDecompAux"

section Clause1Main

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {H : Type} [AddCommGroup H] [Module 𝒪 H]
    (D : CohCarrier.HeckeData 𝒪 H (ResidueField 𝒪))
    (Sp : IharaLemma.IdempotentSplitting ↥D.opSubalgebra) (i₀ : Fin Sp.n)

theorem exists_mvPolynomial_aeval_eq_e_and_eval₂_residue_eq_one
    (πk : Sp.CornerRing i₀ →ₐ[𝒪] ResidueField 𝒪)
    (hπk : ∀ g : D.Gen, πk (Sp.toCornerRing i₀
      ⟨D.op g, Algebra.subset_adjoin (Set.mem_range_self g)⟩) = D.θbar g) :
    ∃ P₀ : MvPolynomial D.Gen 𝒪, MvPolynomial.aeval
        (fun g => (⟨D.op g, Algebra.subset_adjoin (Set.mem_range_self g)⟩ : ↥D.opSubalgebra)) P₀ = Sp.e i₀ ∧
      MvPolynomial.eval₂ (IsLocalRing.residue 𝒪) D.θbar P₀ = 1 := by
  let op' : D.Gen → ↥D.opSubalgebra := fun g => ⟨D.op g, Algebra.subset_adjoin (Set.mem_range_self g)⟩
  obtain ⟨P₀, hP₀⟩ := exists_mvPolynomial_aeval_eq D (Sp.e i₀)
  refine ⟨P₀, hP₀, ?_⟩
  let ψ : ↥D.opSubalgebra →+* ResidueField 𝒪 :=
    (πk : Sp.CornerRing i₀ →+* ResidueField 𝒪).comp (Sp.toCornerRing i₀)
  have hψalg : ψ.comp (algebraMap 𝒪 ↥D.opSubalgebra) = IsLocalRing.residue 𝒪 := by
    ext r
    show πk (algebraMap 𝒪 (Sp.CornerRing i₀) r) = IsLocalRing.residue 𝒪 r
    rw [AlgHom.commutes]
    rfl
  have hψop : (ψ : ↥D.opSubalgebra → ResidueField 𝒪) ∘ op' = D.θbar := funext hπk
  have h1 : ψ (Sp.e i₀) = 1 := by
    show πk (Sp.toCornerRing i₀ (Sp.e i₀)) = 1
    have : Sp.toCornerRing i₀ (Sp.e i₀) = 1 := by
      apply IharaLemma.IdempotentSplitting.ext_cornerRing
      rw [IharaLemma.IdempotentSplitting.coe_toCornerRing,
        IharaLemma.IdempotentSplitting.coe_one_cornerRing, (Sp.idem i₀).eq, (Sp.idem i₀).eq]
    rw [this, map_one]
  rw [← h1, ← hP₀, MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left, hψalg]
  show _ = MvPolynomial.eval₂ (IsLocalRing.residue 𝒪) ((ψ : ↥D.opSubalgebra → ResidueField 𝒪) ∘ op') P₀
  rw [hψop]

theorem restrictHom_mem_adjoin (F : Type) [Field F] [Algebra 𝒪 F] (a : D.Gen → F) (b : ↥D.opSubalgebra) :
    restrictHom D F a b ∈ Algebra.adjoin F (Set.range fun g : D.Gen =>
      restrictHom D F a ⟨D.op g, Algebra.subset_adjoin (Set.mem_range_self g)⟩) := by
  obtain ⟨P, rfl⟩ := exists_mvPolynomial_aeval_eq D b
  induction P using MvPolynomial.induction_on with
  | add p q hp hq =>
    rw [map_add, map_add]
    exact Subalgebra.add_mem _ hp hq
  | mul_X p g hp =>
    rw [map_mul, map_mul, MvPolynomial.aeval_X]
    exact Subalgebra.mul_mem _ hp (Algebra.subset_adjoin (Set.mem_range_self g))
  | C r =>
    rw [MvPolynomial.algHom_C]
    have : restrictHom D F a (algebraMap 𝒪 ↥D.opSubalgebra r) =
        algebraMap F _ (algebraMap 𝒪 F r) := by
      apply LinearMap.ext
      intro x
      rw [restrictHom_algebraMap_apply, Module.algebraMap_end_apply]
    rw [this]
    exact Subalgebra.algebraMap_mem _ _

theorem isNilpotent_restrictHom_op_sub [Module.Finite 𝒪 H] (F : Type) [Field F] [Algebra 𝒪 F]
    (a : D.Gen → F) (g : D.Gen) :
    letI V : Submodule F (F ⊗[𝒪] H) :=
      ⨅ g : D.Gen, Module.End.maxGenEigenspace ((D.op g).baseChange F) (a g)
    letI : AddCommGroup ↥V := inferInstance
    IsNilpotent (restrictHom D F a ⟨D.op g, Algebra.subset_adjoin (Set.mem_range_self g)⟩ -
      algebraMap F (Module.End F ↥V) (a g)) := by
  let V : Submodule F (F ⊗[𝒪] H) :=
    ⨅ g : D.Gen, Module.End.maxGenEigenspace ((D.op g).baseChange F) (a g)
  letI : AddCommGroup ↥V := inferInstance
  have hcoe : ∀ (m : ℕ) (y : ↥V),
      ((((restrictHom D F a ⟨D.op g, Algebra.subset_adjoin (Set.mem_range_self g)⟩ -
          algebraMap F (Module.End F ↥V) (a g)) ^ m) y : ↥V) : F ⊗[𝒪] H) =
        (((D.op g).baseChange F - a g • 1) ^ m) (y : F ⊗[𝒪] H) := by
    intro m
    induction m with
    | zero => intro y; rfl
    | succ m ih =>
        intro y
        rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]
        rfl
  rw [Module.End.isNilpotent_iff_of_finite]
  rintro ⟨x, hx⟩
  have hx' : x ∈ Module.End.maxGenEigenspace ((D.op g).baseChange F) (a g) :=
    (Submodule.mem_iInf _).mp hx g
  obtain ⟨n, hn⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp hx'
  refine ⟨n, Subtype.ext ?_⟩
  rw [hcoe, hn]
  rfl

theorem restrictHom_e_eq_one [Module.Finite 𝒪 H] (F : Type) [Field F] [Algebra 𝒪 F] (a : D.Gen → F)
    (P₀ : MvPolynomial D.Gen 𝒪)
    (hP₀ : MvPolynomial.aeval
      (fun g => (⟨D.op g, Algebra.subset_adjoin (Set.mem_range_self g)⟩ : ↥D.opSubalgebra)) P₀ = Sp.e i₀)
    (hc : MvPolynomial.aeval a P₀ ≠ 0) :
    restrictHom D F a (Sp.e i₀) = 1 := by
  classical
  let op' : D.Gen → ↥D.opSubalgebra := fun g => ⟨D.op g, Algebra.subset_adjoin (Set.mem_range_self g)⟩
  let V : Submodule F (F ⊗[𝒪] H) :=
    ⨅ g : D.Gen, Module.End.maxGenEigenspace ((D.op g).baseChange F) (a g)

  letI : AddCommGroup ↥V := inferInstance
  let ρ : ↥D.opSubalgebra →+* Module.End F ↥V := restrictHom D F a
  let T' : D.Gen → Module.End F ↥V := fun g => ρ (op' g)
  let PF : MvPolynomial D.Gen F := MvPolynomial.map (algebraMap 𝒪 F) P₀
  have hcF : MvPolynomial.eval a PF = MvPolynomial.aeval a P₀ := by
    rw [MvPolynomial.eval_map]
    rfl
  have hnil : ∀ g, IsNilpotent (T' g - algebraMap F (Module.End F ↥V) (a g)) := fun g =>
    isNilpotent_restrictHom_op_sub D F a g

  let K : Subalgebra F (Module.End F ↥V) := Algebra.adjoin F (Set.range T')
  have hT'comm : ∀ x ∈ Set.range T', ∀ y ∈ Set.range T', x * y = y * x := by
    rintro _ ⟨g, rfl⟩ _ ⟨h, rfl⟩
    show ρ (op' g) * ρ (op' h) = ρ (op' h) * ρ (op' g)
    rw [← map_mul, ← map_mul, mul_comm]
  haveI hKcomm : IsMulCommutative ↥K := Algebra.isMulCommutative_adjoin F hT'comm
  have hρK : ∀ b : ↥D.opSubalgebra, ρ b ∈ K := fun b => restrictHom_mem_adjoin D F a b
  let ρK : ↥D.opSubalgebra →+* ↥K := ρ.codRestrict K hρK
  let t' : D.Gen → ↥K := fun g => ρK (op' g)
  have hnilK : ∀ g, IsNilpotent (t' g - algebraMap F ↥K (a g)) := by
    intro g
    obtain ⟨n, hn⟩ := hnil g
    refine ⟨n, Subtype.ext ?_⟩
    rw [Subalgebra.coe_pow, Subalgebra.coe_sub, Subalgebra.coe_algebraMap, Subalgebra.coe_zero]
    exact hn
  have hN : IsNilpotent (MvPolynomial.aeval t' PF - algebraMap F ↥K (MvPolynomial.eval a PF)) :=
    isNilpotent_aeval_sub_algebraMap_eval t' a hnilK PF

  have hρalg : ρK.comp (algebraMap 𝒪 ↥D.opSubalgebra) = (algebraMap F ↥K).comp (algebraMap 𝒪 F) := by
    refine RingHom.ext fun r => Subtype.ext (LinearMap.ext fun x => ?_)
    show ρ (algebraMap 𝒪 ↥D.opSubalgebra r) x = algebraMap F (Module.End F ↥V) (algebraMap 𝒪 F r) x
    rw [restrictHom_algebraMap_apply, Module.algebraMap_end_apply]
  have hε : ρK (Sp.e i₀) = MvPolynomial.aeval t' PF := by
    rw [← hP₀, MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left, hρalg, ← MvPolynomial.eval₂_map,
      MvPolynomial.aeval_def]
    rfl
  have hεidem : IsIdempotentElem (MvPolynomial.aeval t' PF) := by
    rw [← hε]
    exact (Sp.idem i₀).map ρK
  have hε1 : MvPolynomial.aeval t' PF = 1 :=
    eq_one_of_isIdempotentElem_of_isNilpotent_sub_algebraMap (MvPolynomial.aeval t' PF) hεidem
      (MvPolynomial.eval a PF) hN (by rw [hcF]; exact hc)
  have := congrArg (Subtype.val : ↥K → Module.End F ↥V) (hε.trans hε1)
  rw [Subalgebra.coe_one] at this
  exact this

theorem iInf_maxGenEigenspace_le_range_of_forall_pass [Module.Finite 𝒪 H] [Module.Free 𝒪 H]
    (πk : Sp.CornerRing i₀ →ₐ[𝒪] ResidueField 𝒪)
    (hπk : ∀ g : D.Gen, πk (Sp.toCornerRing i₀
      ⟨D.op g, Algebra.subset_adjoin (Set.mem_range_self g)⟩) = D.θbar g)
    (F : Type) [Field F] [Algebra 𝒪 F] (hinj : Function.Injective (algebraMap 𝒪 F)) (a : D.Gen → F)
    (hpass : ∀ g : D.Gen, ∃ R : Polynomial 𝒪, R.Monic ∧ Polynomial.aeval (a g) R = 0 ∧
        R.map (IsLocalRing.residue 𝒪) = (Polynomial.X - Polynomial.C (D.θbar g)) ^ R.natDegree) :
    (⨅ g : D.Gen, Module.End.maxGenEigenspace ((D.op g).baseChange F) (a g)) ≤
      LinearMap.range (((IharaLemma.cornerSubmodule (M := H) (Sp.e i₀)).subtype.restrictScalars 𝒪).baseChange F) := by
  obtain ⟨P₀, hP₀, hP₀res⟩ := exists_mvPolynomial_aeval_eq_e_and_eval₂_residue_eq_one D Sp i₀ πk hπk
  have hc : MvPolynomial.aeval a P₀ ≠ 0 :=
    aeval_ne_zero_of_forall_residualTest D.θbar a hinj hpass P₀ (by rw [hP₀res]; exact one_ne_zero)
  have h1 := restrictHom_e_eq_one D Sp i₀ F a P₀ hP₀ hc
  intro x hx
  rw [mem_range_cornerSubtype_baseChange_iff]
  have := congrArg (fun φ => ((φ ⟨x, hx⟩ :
    ↥(⨅ g : D.Gen, Module.End.maxGenEigenspace ((D.op g).baseChange F) (a g))) : F ⊗[𝒪] H)) h1
  simpa using this

end Clause1Main
p2m_reactivate "P2MW.S_CohCarrier_HeckeData_iInf_maxGenEigenspace_baseChange_le_range_and_inf_eq_bot_and_eq_iSup_of_cornerRing_point.CDecompAux"

end CDecompAux
p2m_reactivate "P2MW.S_CohCarrier_HeckeData_iInf_maxGenEigenspace_baseChange_le_range_and_inf_eq_bot_and_eq_iSup_of_cornerRing_point.CDecompAux"

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {H : Type} [AddCommGroup H] [Module 𝒪 H] [Module.Finite 𝒪 H] [Module.Free 𝒪 H]
    (D : CohCarrier.HeckeData 𝒪 H (ResidueField 𝒪))
    (Sp : IharaLemma.IdempotentSplitting ↥D.opSubalgebra) (i₀ : Fin Sp.n)
    (πk : Sp.CornerRing i₀ →ₐ[𝒪] ResidueField 𝒪)
    (hπk : ∀ g : D.Gen, πk (Sp.toCornerRing i₀
      ⟨D.op g, Algebra.subset_adjoin (Set.mem_range_self g)⟩) = D.θbar g)
    (F : Type) [Field F] [Algebra 𝒪 F] (hinj : Function.Injective (algebraMap 𝒪 F)) :

    (∀ a : D.Gen → F,
      (∀ g : D.Gen, (∃ R : Polynomial 𝒪, R.Monic ∧ Polynomial.aeval (a g) R = 0 ∧
        R.map (IsLocalRing.residue 𝒪) = (Polynomial.X - Polynomial.C (D.θbar g)) ^ R.natDegree)) →
      (⨅ g : D.Gen, Module.End.maxGenEigenspace ((D.op g).baseChange F) (a g)) ≤
        LinearMap.range (((IharaLemma.cornerSubmodule (M := H) (Sp.e i₀)).subtype.restrictScalars 𝒪).baseChange F)) ∧

    (∀ a : D.Gen → F,
      (∃ g : D.Gen, ¬ (∃ R : Polynomial 𝒪, R.Monic ∧ Polynomial.aeval (a g) R = 0 ∧
        R.map (IsLocalRing.residue 𝒪) = (Polynomial.X - Polynomial.C (D.θbar g)) ^ R.natDegree)) →
      (⨅ g : D.Gen, Module.End.maxGenEigenspace ((D.op g).baseChange F) (a g)) ⊓
        LinearMap.range (((IharaLemma.cornerSubmodule (M := H) (Sp.e i₀)).subtype.restrictScalars 𝒪).baseChange F) = ⊥) ∧

    (IsAlgClosed F →
      LinearMap.range (((IharaLemma.cornerSubmodule (M := H) (Sp.e i₀)).subtype.restrictScalars 𝒪).baseChange F) =
        ⨆ (a : D.Gen → F) (_ : ∀ g : D.Gen, (∃ R : Polynomial 𝒪, R.Monic ∧ Polynomial.aeval (a g) R = 0 ∧
        R.map (IsLocalRing.residue 𝒪) = (Polynomial.X - Polynomial.C (D.θbar g)) ^ R.natDegree)),
          ⨅ g : D.Gen, Module.End.maxGenEigenspace ((D.op g).baseChange F) (a g)) := by
  have h1 : ∀ a : D.Gen → F,
      (∀ g : D.Gen, (∃ R : Polynomial 𝒪, R.Monic ∧ Polynomial.aeval (a g) R = 0 ∧
        R.map (IsLocalRing.residue 𝒪) = (Polynomial.X - Polynomial.C (D.θbar g)) ^ R.natDegree)) →
      (⨅ g : D.Gen, Module.End.maxGenEigenspace ((D.op g).baseChange F) (a g)) ≤
        LinearMap.range (((IharaLemma.cornerSubmodule (M := H) (Sp.e i₀)).subtype.restrictScalars 𝒪).baseChange F) :=
    fun a ha => CDecompAux.iInf_maxGenEigenspace_le_range_of_forall_pass D Sp i₀ πk hπk F hinj a ha
  have h2 : ∀ a : D.Gen → F,
      (∃ g : D.Gen, ¬ (∃ R : Polynomial 𝒪, R.Monic ∧ Polynomial.aeval (a g) R = 0 ∧
        R.map (IsLocalRing.residue 𝒪) = (Polynomial.X - Polynomial.C (D.θbar g)) ^ R.natDegree)) →
      (⨅ g : D.Gen, Module.End.maxGenEigenspace ((D.op g).baseChange F) (a g)) ⊓
        LinearMap.range (((IharaLemma.cornerSubmodule (M := H) (Sp.e i₀)).subtype.restrictScalars 𝒪).baseChange F) = ⊥ :=
    fun a ha => CDecompAux.iInf_maxGenEigenspace_inf_range_eq_bot_of_exists_not D Sp i₀ πk hπk F a ha
  refine ⟨h1, h2, fun hF => ?_⟩
  haveI := hF
  exact CDecompAux.range_cornerSubtype_baseChange_eq_biSup_of_pass D Sp F i₀ _ h1
    (fun a ha => h2 a (not_forall.mp ha))

end S_CohCarrier_HeckeData_iInf_maxGenEigenspace_baseChange_le_range_and_inf_eq_bot_and_eq_iSup_of_cornerRing_point
end P2MW
export P2MW.S_CohCarrier_HeckeData_iInf_maxGenEigenspace_baseChange_le_range_and_inf_eq_bot_and_eq_iSup_of_cornerRing_point (solution)
