-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis.zdual_relIndex
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:51:21.872125+00:00
-- url     : https://prove2.me/submissions/20be2f07-9ae8-4a27-a0da-6f3b691cf8dd

import Definitions.Def_Formalism_FlagUnipotentLattices_IdealCountLeW
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Lemmata_GeneralBFactSecondMore_Imports
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ColonCountWeighted
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_DualLatticeIndexBis_exists_rat_basis
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_DualLatticeIndexBis_int_on_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open NumberField
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis
namespace Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (t : V →ₗ[ℚ] V →ₗ[ℚ] ℚ) (hnd : ∀ x, (∀ y, t x y = 0) → x = 0)
    (A B : Submodule ℤ V) (hAB : A ≤ B) (hB : B.FG) (hA : ∀ x : V, ∃ n : ℤ, n ≠ 0 ∧ n • x ∈ A)
    (A' B' : AddSubgroup V)
    (hA' : ∀ x, x ∈ A' ↔ ∀ y ∈ A, ∃ n : ℤ, t x y = n)
    (hB' : ∀ x, x ∈ B' ↔ ∀ y ∈ B, ∃ n : ℤ, t x y = n) :
    B'.relIndex A' = A.toAddSubgroup.relIndex B.toAddSubgroup := by
  classical
  have : Module.Finite ℤ B := Module.Finite.iff_fg.mpr hB
  have : Module.IsTorsionFree ℤ V := Module.IsTorsionFree.trans_faithfulSMul ℤ ℚ V
  obtain ⟨ι, _, ⟨b⟩⟩ : ∃ (ι : Type _) (_ : Fintype ι), Nonempty (Module.Basis ι ℤ B) :=
    ⟨_, inferInstance, ⟨Module.Free.chooseBasis ℤ B⟩⟩
  let A₀ : Submodule ℤ B := A.comap B.subtype
  have hrank : Module.finrank ℤ A₀ = Module.finrank ℤ B := by
    have h1 := Submodule.finrank_quotient_add_finrank A₀
    have h2 : Module.finrank ℤ (B ⧸ A₀) = 0 := by
      rw [Module.finrank_eq_zero_iff_isTorsion]
      intro x
      obtain ⟨y, rfl⟩ := A₀.mkQ_surjective x
      obtain ⟨n, hn, hny⟩ := hA (y : V)
      refine ⟨⟨n, mem_nonZeroDivisors_of_ne_zero hn⟩, ?_⟩
      change n • A₀.mkQ y = 0
      rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hny
    omega
  obtain ⟨b', a, ab', hab⟩ := Submodule.exists_smith_normal_form_of_rank_eq b hrank
  obtain ⟨vb, hvb, hBv⟩ := exists_rat_basis B b' (fun x => by
    obtain ⟨n, hn, hnx⟩ := hA x
    exact ⟨n, hn, hAB hnx⟩)
  obtain ⟨va, hva, hAv⟩ := exists_rat_basis A (ab'.map (Submodule.comapSubtypeEquivOfLe hAB)) hA
  have hvab : ∀ i, va i = (a i : ℚ) • vb i := by
    intro i
    rw [hva, hvb, Module.Basis.map_apply, Submodule.comapSubtypeEquivOfLe_apply_coe, hab,
      Int.cast_smul_eq_zsmul]
    rfl
  let S : V →ₗ[ℚ] V := ∑ i, LinearMap.smulRight (t.flip (va i)) (vb i)
  have hS1 : ∀ x, S x = ∑ i, t x (va i) • vb i := by
    intro x; simp [S, LinearMap.sum_apply]
  have hS2 : ∀ x, S x = ∑ i, t x (vb i) • va i := by
    intro x
    rw [hS1]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hvab, map_smul, smul_smul, smul_eq_mul, mul_comm]
  have hr1 : ∀ x i, vb.repr (S x) i = t x (va i) := by
    intro x i
    rw [hS1, Module.Basis.repr_sum_self]
  have hr2 : ∀ x i, va.repr (S x) i = t x (vb i) := by
    intro x i
    rw [hS2, Module.Basis.repr_sum_self]
  have hinj : Function.Injective S := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    apply hnd
    have h0 : t x = 0 := by
      apply va.ext
      intro i
      rw [← hr1, hx]; simp
    intro y
    rw [h0]; rfl
  have hsurj : Function.Surjective S := LinearMap.injective_iff_surjective.mp hinj
  have hmem : ∀ (cb : Module.Basis ι ℚ V) (y : V), y ∈ Submodule.span ℤ (Set.range cb) ↔
      ∀ i, ∃ n : ℤ, cb.repr y i = n := by
    intro cb y
    rw [Module.Basis.mem_span_iff_repr_mem]
    refine forall_congr' (fun i => ?_)
    constructor
    · rintro ⟨n, hn⟩; exact ⟨n, hn.symm⟩
    · rintro ⟨n, hn⟩; exact ⟨n, hn.symm⟩
  have eA : A' = B.toAddSubgroup.comap S.toAddMonoidHom := by
    ext x
    rw [hA', hAv, int_on_span (t x) va, AddSubgroup.mem_comap]
    change _ ↔ S x ∈ B
    rw [hBv, hmem]
    simp only [hr1]
  have eB : B' = A.toAddSubgroup.comap S.toAddMonoidHom := by
    ext x
    rw [hB', hBv, int_on_span (t x) vb, AddSubgroup.mem_comap]
    change _ ↔ S x ∈ A
    rw [hAv, hmem]
    simp only [hr2]
  rw [eA, eB, AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective hsurj]
end Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis
