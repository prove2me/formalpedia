-- Prove2me | solution 1 for Formalism.MainNotions.flipOneThree.Pf.KP.latRetract
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:41:19.953119+00:00
-- url     : https://prove2.me/submissions/f08ada41-3be9-466e-b40b-e67f2edbd11e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_LatRetract
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.MainNotions.flipOneThree.Pf.KP
open Submodule
section LatRetract
variable {O K V V' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V]
  [IsScalarTower O K V] [AddCommGroup V'] [Module K V'] [Module O V'] [IsScalarTower O K V']
  {ι ι' : Type} [Fintype ι] [Fintype ι']
omit [IsDiscreteValuationRing O] in
private theorem lrt_am_ne {a : O} (ha : a ≠ 0) : algebraMap O K a ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 ha
private theorem lrt_tf (O K V : Type) [CommRing O] [IsDomain O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] :
    Module.IsTorsionFree O V :=
  ⟨fun r hr x y hxy => by
    have hr0 : r ≠ 0 := hr.ne_zero
    have h1 : algebraMap O K r • x = algebraMap O K r • y := by
      rw [algebraMap_smul, algebraMap_smul]; exact hxy
    exact smul_right_injective V (lrt_am_ne (K := K) hr0) h1⟩
omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] [Fintype ι] in

private theorem lrt_coord (b : Module.Basis ι K V) {y : V}
    (hy : y ∈ span O (Set.range b)) (i : ι) : b.repr y i ∈ Set.range (algebraMap O K) := by
  classical
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    by_cases hji : j = i
    · subst hji; exact ⟨1, by simp⟩
    · exact ⟨0, by simp [hji]⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨u, hu⟩ := hx
    obtain ⟨v, hv⟩ := hy
    exact ⟨u + v, by simp [hu, hv]⟩
  | smul a x _ hx =>
    obtain ⟨u, hu⟩ := hx
    exact ⟨a * u, by
      rw [← algebraMap_smul K a x, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, hu]⟩
omit [IsDiscreteValuationRing O] in

private theorem lrt_den (b : Module.Basis ι K V) (F : V) :
    ∃ a : O, a ≠ 0 ∧ a • F ∈ span O (Set.range b) := by
  obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O)
    (fun i => b.repr F i)
  refine ⟨a, nonZeroDivisors.ne_zero a.2, ?_⟩
  have hF : (a : O) • F = ∑ i, (a : O) • (b.repr F i • b i) := by
    rw [← Finset.smul_sum, b.sum_repr F]
  rw [hF]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨z, hz⟩ := ha i
  rw [← smul_assoc, ← hz, algebraMap_smul]
  exact Submodule.smul_mem _ _ (subset_span ⟨i, rfl⟩)
private theorem lrt_inj (b : Module.Basis ι K V) (b' : Module.Basis ι' K V') (io : V →ₗ[K] V')
    (h : ∀ F, io F ∈ Submodule.span O (Set.range b') ↔ F ∈ Submodule.span O (Set.range b)) :
    Function.Injective io := by
  rw [injective_iff_map_eq_zero]
  intro F hF
  by_contra hne
  have h0 : b.repr F ≠ 0 := by simpa using hne
  obtain ⟨i, hi⟩ := DFunLike.ne_iff.1 h0
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hmem : ((b.repr F i * algebraMap O K ϖ)⁻¹) • F ∈ span O (Set.range b) := by
    rw [← h, map_smul, hF, smul_zero]; exact zero_mem _
  obtain ⟨z, hz⟩ := lrt_coord b hmem i
  have hϖ0 : algebraMap O K ϖ ≠ 0 := lrt_am_ne hϖ.ne_zero
  have hi' : b.repr F i ≠ 0 := by simpa using hi
  have h1 : algebraMap O K (ϖ * z) = algebraMap O K 1 := by
    rw [map_mul, hz, map_one, map_smul, Finsupp.smul_apply, smul_eq_mul]
    field_simp
  have h2 := IsFractionRing.injective O K h1
  exact hϖ.not_isUnit (IsUnit.of_mul_eq_one _ h2)
end LatRetract
end Formalism.MainNotions.flipOneThree.Pf.KP
end

set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.flipOneThree Formalism.MainNotions.flipOneThree.Pf Formalism.MainNotions.flipOneThree.Pf.KP
open Submodule
variable {O K V V' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V]
  [IsScalarTower O K V] [AddCommGroup V'] [Module K V'] [Module O V'] [IsScalarTower O K V']
  {ι ι' : Type} [Fintype ι] [Fintype ι']
namespace Formalism.MainNotions.flipOneThree.Pf.KP
theorem _root_.solution {O K V V' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] [AddCommGroup V'] [Module K V'] [Module O V'] [IsScalarTower O K V'] {ι ι' : Type} [Fintype ι] [Fintype ι'] (b : Module.Basis ι K V) (b' : Module.Basis ι' K V') (io : V →ₗ[K] V') (h : ∀ F, io F ∈ Submodule.span O (Set.range b') ↔ F ∈ Submodule.span O (Set.range b)) : ∃ ret : V' →ₗ[K] V, (∀ F, ret (io F) = F) ∧ ∀ G ∈ Submodule.span O (Set.range b'), ret G ∈ Submodule.span O (Set.range b) := by
  classical
  have : Module.IsTorsionFree O V := lrt_tf O K V
  have : Module.IsTorsionFree O V' := lrt_tf O K V'
  let R : Submodule O V := span O (Set.range b)
  let R' : Submodule O V' := span O (Set.range b')
  have : Module.Finite O R := Module.Finite.span_of_finite O (Set.finite_range b)
  have : Module.Finite O R' := Module.Finite.span_of_finite O (Set.finite_range b')
  let ioR : R →ₗ[O] R' := (io.restrictScalars O).restrict (fun F hF => (h F).2 hF)
  have hinj : Function.Injective ioR := fun x y hxy =>
    Subtype.ext (lrt_inj b b' io h (congrArg Subtype.val hxy))
  let N : Submodule O R' := LinearMap.range ioR
  have : Module.IsTorsionFree O (R' ⧸ N) := by
    refine ⟨fun r hr x y hxy => ?_⟩
    obtain ⟨x, rfl⟩ := N.mkQ_surjective x
    obtain ⟨y, rfl⟩ := N.mkQ_surjective y
    have h1 : N.mkQ (r • (x - y)) = 0 := by
      rw [smul_sub, map_sub, map_smul, map_smul, sub_eq_zero]; exact hxy
    rw [mkQ_apply, Quotient.mk_eq_zero] at h1
    obtain ⟨F, hF⟩ := h1
    have hr0 : r ≠ 0 := hr.ne_zero
    rw [← sub_eq_zero, ← map_sub, mkQ_apply, Quotient.mk_eq_zero]
    have hFv : io (F : V) = r • ((x - y : R') : V') := congrArg Subtype.val hF
    have hcalc : io ((algebraMap O K r)⁻¹ • (F : V)) = ((x - y : R') : V') := by
      rw [map_smul, hFv, ← algebraMap_smul K r, smul_smul, inv_mul_cancel₀ (lrt_am_ne hr0),
        one_smul]
    have hmem : (algebraMap O K r)⁻¹ • (F : V) ∈ R := by
      rw [← h, hcalc]
      exact (x - y).2
    exact ⟨⟨_, hmem⟩, Subtype.ext hcalc⟩
  obtain ⟨s, hs⟩ := N.mkQ.exists_rightInverse_of_surjective N.range_mkQ
  let e := LinearEquiv.ofInjective ioR hinj
  let p : R' →ₗ[O] N := (LinearMap.id - s ∘ₗ N.mkQ).codRestrict N (fun y => by
    rw [← Quotient.mk_eq_zero, ← mkQ_apply, LinearMap.sub_apply, map_sub, sub_eq_zero]
    exact (LinearMap.congr_fun hs (N.mkQ y)).symm)
  let retO : R' →ₗ[O] R := e.symm.toLinearMap ∘ₗ p
  have hretO : ∀ x : R, retO (ioR x) = x := by
    intro x
    show e.symm (p (ioR x)) = x
    rw [LinearEquiv.symm_apply_eq]
    apply Subtype.ext
    have h0 : N.mkQ (ioR x) = 0 := by
      rw [mkQ_apply, Quotient.mk_eq_zero]; exact ⟨x, rfl⟩
    show (LinearMap.id - s ∘ₗ N.mkQ : R' →ₗ[O] R') (ioR x) = ioR x
    simp [h0]
  let ret : V' →ₗ[K] V :=
    b'.constr K (fun j => ((retO ⟨b' j, subset_span ⟨j, rfl⟩⟩ : R) : V))
  have hret : ∀ G (hG : G ∈ R'), ret G = retO ⟨G, hG⟩ := by
    intro G hG
    induction hG using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      exact b'.constr_basis K _ j
    | zero =>
      rw [map_zero]
      exact (congrArg Subtype.val (map_zero retO)).symm
    | add x y hx hy ihx ihy =>
      rw [map_add, ihx, ihy]
      exact (congrArg Subtype.val (map_add retO ⟨x, hx⟩ ⟨y, hy⟩)).symm
    | smul a x hx ih =>
      have h1 : ret (a • x) = a • ret x := by
        rw [← algebraMap_smul K a x, map_smul, algebraMap_smul]
      rw [h1, ih]
      exact (congrArg Subtype.val (map_smul retO a ⟨x, hx⟩)).symm
  refine ⟨ret, fun F => ?_, fun G hG => by rw [hret G hG]; exact (retO _).2⟩
  obtain ⟨a, ha, haF⟩ := lrt_den (O := O) b F
  have h1 : ret (io (a • F)) = a • F := by
    rw [hret _ ((h _).2 haF)]
    exact congrArg Subtype.val (hretO ⟨a • F, haF⟩)
  have h2 : a • ret (io F) = a • F := by
    rw [← h1, ← algebraMap_smul K a F, map_smul, map_smul, algebraMap_smul]
  exact smul_right_injective V ha h2
end Formalism.MainNotions.flipOneThree.Pf.KP
