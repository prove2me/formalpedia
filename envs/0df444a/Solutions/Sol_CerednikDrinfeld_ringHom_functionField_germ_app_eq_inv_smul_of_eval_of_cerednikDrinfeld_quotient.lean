-- Prove2me | solution 1 for CerednikDrinfeld.ringHom_functionField_germ_app_eq_inv_smul_of_eval_of_cerednikDrinfeld_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/3cde1116-93f8-5c82-86f5-7e678e0367f4

import Theorems.Thm_CerednikDrinfeld_FormalOmega_existsUnique_hom_comp_eq_of_compatible_modPow
import Theorems.Thm_CerednikDrinfeld_FormalOmega_AdicPoint_toOmega_act
import Theorems.Thm_CerednikDrinfeld_FormalOmega_AdicPoint_toOmega_surjOn
import Theorems.Thm_CerednikDrinfeld_Omega_finite_setOf_apply_eq_zero_of_mem_holOn_affinoid
import Theorems.Thm_CerednikDrinfeld_Omega_forall_exists_finset_v_sub_lt_pow_of_finite_quotient
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFrame
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_ringHom_functionField_germ_app_eq_inv_smul_of_eval_of_cerednikDrinfeld_quotient

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega CerednikDrinfeld.Mumford AlgebraicCurve

namespace KcEvalRiderEngine

section Frame

variable {𝒪 : Type} [CommRing 𝒪] {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀]
  {C : Type} [Field C] [Algebra K₀ C] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
  {π : 𝒪} {ϖ : PseudoUniformizer K₀ C} {R : Type} [CommRing R] [Algebra 𝒪 R] [Algebra R C]
  [Algebra 𝒪 C] [IsScalarTower 𝒪 R C] [IsScalarTower 𝒪 K₀ C]

theorem isUnit_of_v_eq_one (hF : IsAdicFrame π ϖ R) {a : R} (h : Valued.v (algebraMap R C a) = 1) : IsUnit a := by
  have ha0 : algebraMap R C a ≠ 0 := fun h0 => by
    rw [h0, map_zero] at h
    exact zero_ne_one h
  have hinv : Valued.v (algebraMap R C a)⁻¹ ≤ 1 := by rw [map_inv₀, h, inv_one]
  obtain ⟨s, hs⟩ := (hF.range_eq _).1 hinv
  refine IsUnit.of_mul_eq_one s (hF.injective ?_)
  rw [map_mul, map_one, hs, mul_inv_cancel₀ ha0]

theorem isLocalRing (hF : IsAdicFrame π ϖ R) : IsLocalRing R := by
  haveI : Nontrivial R := ⟨⟨0, 1, fun h01 => (zero_ne_one' C) (by simpa using congrArg (algebraMap R C) h01)⟩⟩
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  by_cases ha : Valued.v (algebraMap R C a) < 1
  · right
    refine isUnit_of_v_eq_one hF ?_
    rw [map_sub, map_one]
    exact Valuation.map_one_sub_of_lt _ ha
  · left
    exact isUnit_of_v_eq_one hF (le_antisymm (hF.v_algebraMap_le_one a) (not_lt.1 ha))

theorem locCompact {r : ℕ} [Fact r.Prime] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪) [IsFractionRing 𝒪 K₀]
    (hπ : Irreducible π) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hF : IsAdicFrame π ϖ R)
    (hrk : ∀ x y : C, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hval : ∀ ε : Γ₀, ε ≠ 0 → ∃ y : C, y ≠ 0 ∧ Valued.v y ≤ ε) :
    ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀,
      Valued.v (algebraMap K₀ C a) ≤ (Valued.v (algebraMap K₀ C ϖ.ϖ))⁻¹ ^ n →
        ∃ t ∈ T, Valued.v (algebraMap K₀ C a - algebraMap K₀ C t) < (Valued.v (algebraMap K₀ C ϖ.ϖ)) ^ n := by
  haveI := hdvr
  haveI : Finite (𝒪 ⧸ Ideal.span {π}) :=
    Nat.finite_of_card_ne_zero (by rw [hres]; exact (Fact.out : r.Prime).ne_zero)
  refine forall_exists_finset_v_sub_lt_pow_of_finite_quotient 𝒪 K₀ π hπ C (fun a => ?_) (fun a ha => ?_)
    (fun ε hε => ?_) ϖ
  · exact (hF.integers _).2 ⟨a, rfl⟩
  · obtain ⟨b, hb⟩ := (hF.integers a).1 ha
    exact RingHom.mem_rangeS.2 ⟨b, hb⟩
  · obtain ⟨y, hy0, hy⟩ := hval ε hε
    have hπC : algebraMap K₀ C (algebraMap 𝒪 K₀ π) = algebraMap 𝒪 C π := (IsScalarTower.algebraMap_apply 𝒪 K₀ C π).symm
    obtain ⟨N, hN⟩ := hrk (algebraMap K₀ C (algebraMap 𝒪 K₀ π)) y (by rw [hπC]; exact hF.v_algebraMap_lt_one) hy0
    exact ⟨N, hN.trans hy⟩

omit [Algebra 𝒪 K₀] [Algebra R C] [Algebra 𝒪 C] [IsScalarTower 𝒪 R C] [IsScalarTower 𝒪 K₀ C] in

theorem small (ϖ : PseudoUniformizer K₀ C) (hval : ∀ ε : Γ₀, ε ≠ 0 → ∃ y : C, y ≠ 0 ∧ Valued.v y ≤ ε) (n : ℕ) :
    ∃ y : C, y ≠ 0 ∧ Valued.v y < Valued.v (algebraMap K₀ C ϖ.ϖ) ^ n := by
  obtain ⟨y, hy0, hy⟩ := hval (Valued.v (algebraMap K₀ C ϖ.ϖ) ^ (n + 1)) (pow_ne_zero _ ϖ.pos.ne')
  exact ⟨y, hy0, hy.trans_lt (pow_lt_pow_right_of_lt_one₀ ϖ.pos ϖ.lt_one (Nat.lt_succ_self n))⟩

end Frame

section Identity

variable {K₀ : Type} [Field K₀] {C : Type} [Field C] [Algebra K₀ C]
  {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀] (ϖ : PseudoUniformizer K₀ C)

theorem add_mem_affinoid {n : ℕ} {z c : C} (hz : z ∈ affinoid ϖ n)
    (hc : Valued.v c < Valued.v (algebraMap K₀ C ϖ.ϖ) ^ n) : z + c ∈ affinoid ϖ n := by
  rw [mem_affinoid_iff'] at hz ⊢
  obtain ⟨hz1, hz2⟩ := hz
  have hp1 : Valued.v (algebraMap K₀ C ϖ.ϖ) ≤ 1 := ϖ.lt_one.le
  have h1 : Valued.v (algebraMap K₀ C ϖ.ϖ) ^ n ≤ 1 := pow_le_one₀ zero_le' hp1
  have h2 : (1 : Γ₀) ≤ (Valued.v (algebraMap K₀ C ϖ.ϖ))⁻¹ ^ n := one_le_pow₀ ((one_le_inv₀ ϖ.pos).2 hp1)
  refine ⟨(Valuation.map_add _ _ _).trans (max_le hz1 ((hc.le.trans h1).trans h2)), fun a => ?_⟩
  have hlt : Valued.v c < Valued.v (z - algebraMap K₀ C a) := hc.trans_le (hz2 a)
  rw [show z + c - algebraMap K₀ C a = (z - algebraMap K₀ C a) + c by ring, Valuation.map_add_eq_of_lt_left _ hlt]
  exact hz2 a

theorem affinoid_infinite (n : ℕ) {z₀ : C} (hz₀ : z₀ ∈ affinoid ϖ n) {y : C} (hy0 : y ≠ 0)
    (hy : Valued.v y < Valued.v (algebraMap K₀ C ϖ.ϖ) ^ n) : (Set.univ : Set ↥(affinoid ϖ n)).Infinite := by
  have h1 : Valued.v (algebraMap K₀ C ϖ.ϖ) ^ n ≤ 1 := pow_le_one₀ zero_le' ϖ.lt_one.le
  have hy1 : Valued.v y < 1 := hy.trans_le h1
  have hypos : 0 < Valued.v y := (Valuation.pos_iff _).2 hy0
  have hmem : ∀ k : ℕ, z₀ + y ^ (k + 1) ∈ affinoid ϖ n := fun k =>
    add_mem_affinoid ϖ hz₀ (lt_of_le_of_lt (by
      rw [Valuation.map_pow]
      exact pow_le_of_le_one zero_le' hy1.le (Nat.succ_ne_zero k)) hy)
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => (⟨z₀ + y ^ (k + 1), hmem k⟩ : ↥(affinoid ϖ n)))
    (fun j k hjk => ?_) (fun _ => Set.mem_univ _)
  have hjk' : y ^ (j + 1) = y ^ (k + 1) := by
    have := congrArg Subtype.val hjk
    simpa using this
  have hv : Valued.v y ^ (j + 1) = Valued.v y ^ (k + 1) := by
    rw [← Valuation.map_pow, ← Valuation.map_pow, hjk']
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact (pow_lt_pow_right_of_lt_one₀ hypos hy1 (Nat.succ_lt_succ hlt)).ne' hv
  · exact (pow_lt_pow_right_of_lt_one₀ hypos hy1 (Nat.succ_lt_succ hlt)).ne hv

theorem holRing_eq_zero [CompleteSpace C] [IsAlgClosed C]
    (hrk : ∀ x y : C, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hT : ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀,
      Valued.v (algebraMap K₀ C a) ≤ (Valued.v (algebraMap K₀ C ϖ.ϖ))⁻¹ ^ n →
        ∃ t ∈ T, Valued.v (algebraMap K₀ C a - algebraMap K₀ C t) < (Valued.v (algebraMap K₀ C ϖ.ϖ)) ^ n)
    (hsmall : ∀ n : ℕ, ∃ y : C, y ≠ 0 ∧ Valued.v y < Valued.v (algebraMap K₀ C ϖ.ϖ) ^ n)
    (hex : IsExhausted ϖ) (F : ↥(holRing ϖ))
    (hF : ∀ n : ℕ, ∃ E : Set ↥(affinoid ϖ n), E.Finite ∧
      ∀ z : ↥(affinoid ϖ n), z ∉ E → (F : ↥(upperHalfPlane K₀ C) → C) ⟨z, affinoid_subset_upperHalfPlane ϖ n z.2⟩ = 0) :
    F = 0 := by
  have key : ∀ n : ℕ, restrictAffinoid ϖ n (F : ↥(upperHalfPlane K₀ C) → C) = 0 := by
    intro n
    by_contra hne
    have hfin := finite_setOf_apply_eq_zero_of_mem_holOn_affinoid K₀ C ϖ hrk n (hT n) (F.2 n) hne
    obtain ⟨E, hE, hEz⟩ := hF n
    obtain ⟨z₀, -⟩ : ∃ z₀ : ↥(affinoid ϖ n), restrictAffinoid ϖ n (F : ↥(upperHalfPlane K₀ C) → C) z₀ ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hne (funext hall)
    obtain ⟨y, hy0, hy⟩ := hsmall n
    refine affinoid_infinite ϖ n z₀.2 hy0 hy ((hfin.union hE).subset fun z _ => ?_)
    by_cases hz : z ∈ E
    · exact Or.inr hz
    · exact Or.inl (hEz z hz)
  apply Subtype.ext
  funext z
  obtain ⟨n, hn⟩ := hex z z.2
  have h := congrFun (key n) ⟨z, hn⟩
  exact h

end Identity

section Frac

variable {K₀ : Type} [Field K₀] {C : Type} [Field C] [Algebra K₀ C]
  {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀] [DecidableEq C]

omit [DecidableEq C] in

theorem cross {A₁ B₁ A₂ B₂ V : C} (e1 : B₁ * V = A₁) (e2 : B₂ * V = A₂) : A₁ * B₂ = B₁ * A₂ := by
  subst e1 e2; ring

theorem frac_eq [CompleteSpace C] [IsAlgClosed C] (ϖ : PseudoUniformizer K₀ C)
    (hrk : ∀ x y : C, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hT : ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀,
      Valued.v (algebraMap K₀ C a) ≤ (Valued.v (algebraMap K₀ C ϖ.ϖ))⁻¹ ^ n →
        ∃ t ∈ T, Valued.v (algebraMap K₀ C a - algebraMap K₀ C t) < (Valued.v (algebraMap K₀ C ϖ.ϖ)) ^ n)
    (hsmall : ∀ n : ℕ, ∃ y : C, y ≠ 0 ∧ Valued.v y < Valued.v (algebraMap K₀ C ϖ.ϖ) ^ n)
    (hex : IsExhausted ϖ)
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) [IsDomain (HolRingOf ϖ ρ)]
    (a₁ b₁ a₂ b₂ : HolRingOf ϖ ρ) (hb₁ : b₁ ∈ nonZeroDivisors (HolRingOf ϖ ρ))
    (hb₂ : b₂ ∈ nonZeroDivisors (HolRingOf ϖ ρ)) (g : G)
    (bad : ∀ n : ℕ, Set ↥(affinoid ϖ n)) (hbad : ∀ n, (bad n).Finite)
    (hagree : ∀ (n : ℕ) (z : ↥(affinoid ϖ n)), z ∉ bad n →
      (show ↥(Omega.holRing ϖ) from a₁ : ↥(Omega.upperHalfPlane K₀ C) → C)
          ⟨z, affinoid_subset_upperHalfPlane ϖ n z.2⟩ *
        (show ↥(Omega.holRing ϖ) from b₂ : ↥(Omega.upperHalfPlane K₀ C) → C)
          (ρ g • (⟨z, affinoid_subset_upperHalfPlane ϖ n z.2⟩ : ↥(Omega.upperHalfPlane K₀ C))) =
      (show ↥(Omega.holRing ϖ) from b₁ : ↥(Omega.upperHalfPlane K₀ C) → C)
          ⟨z, affinoid_subset_upperHalfPlane ϖ n z.2⟩ *
        (show ↥(Omega.holRing ϖ) from a₂ : ↥(Omega.upperHalfPlane K₀ C) → C)
          (ρ g • (⟨z, affinoid_subset_upperHalfPlane ϖ n z.2⟩ : ↥(Omega.upperHalfPlane K₀ C)))) :
    (Localization.mk a₁ ⟨b₁, hb₁⟩ : FractionRing (HolRingOf ϖ ρ)) =
      g⁻¹ • (Localization.mk a₂ ⟨b₂, hb₂⟩ : FractionRing (HolRingOf ϖ ρ)) := by
  have hb₁0 : b₁ ≠ 0 := nonZeroDivisors.ne_zero hb₁
  have hb₂0 : b₂ ≠ 0 := nonZeroDivisors.ne_zero hb₂

  have hring : a₁ * (g⁻¹ • b₂) = (g⁻¹ • a₂) * b₁ := by
    rw [← sub_eq_zero]
    refine holRing_eq_zero ϖ hrk hT hsmall hex (show ↥(holRing ϖ) from a₁ * (g⁻¹ • b₂) - (g⁻¹ • a₂) * b₁) fun n => ?_
    refine ⟨bad n, hbad n, fun z hz => ?_⟩
    have h := hagree n z hz
    change (show ↥(Omega.holRing ϖ) from a₁ : ↥(Omega.upperHalfPlane K₀ C) → C)
          ⟨z, affinoid_subset_upperHalfPlane ϖ n z.2⟩ *
        ((ρ g⁻¹ • (show ↥(Omega.holRing ϖ) from b₂) : ↥(Omega.holRing ϖ)) : ↥(Omega.upperHalfPlane K₀ C) → C)
          ⟨z, affinoid_subset_upperHalfPlane ϖ n z.2⟩ -
      ((ρ g⁻¹ • (show ↥(Omega.holRing ϖ) from a₂) : ↥(Omega.holRing ϖ)) : ↥(Omega.upperHalfPlane K₀ C) → C)
          ⟨z, affinoid_subset_upperHalfPlane ϖ n z.2⟩ *
        (show ↥(Omega.holRing ϖ) from b₁ : ↥(Omega.upperHalfPlane K₀ C) → C)
          ⟨z, affinoid_subset_upperHalfPlane ϖ n z.2⟩ = 0
    rw [coe_smul_holRing_apply, coe_smul_holRing_apply, map_inv, inv_inv, h]
    ring

  rw [Localization.mk_eq_mk', IsFractionRing.mk'_eq_div, IsFractionRing.mk'_eq_div, Mumford.frac_smul_def, map_div₀,
    Mumford.fracAct_algebraMap, Mumford.fracAct_algebraMap, div_eq_div_iff]
  · rw [← map_mul, ← map_mul, hring]
  · exact (map_ne_zero_iff _ (IsFractionRing.injective (HolRingOf ϖ ρ) _)).2 hb₁0
  · exact (map_ne_zero_iff _ (IsFractionRing.injective (HolRingOf ϖ ρ) _)).2 ((smul_ne_zero_iff_ne _).2 hb₂0)

end Frac

section SchemeSide

theorem exists_cPoint
    {𝒪 : Type} [CommRing 𝒪] {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀]
    {C : Type} [Field C] [Algebra K₀ C] {R : Type} [CommRing R] [Algebra 𝒪 R] [Algebra R C] [Algebra 𝒪 C]
    [IsScalarTower 𝒪 R C] [IsScalarTower 𝒪 K₀ C]
    {𝒴 : Scheme.{0}} (fY : 𝒴 ⟶ Spec (CommRingCat.of 𝒪)) (sC : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of 𝒪))
    (hsC : sC = Spec.map (CommRingCat.ofHom ((algebraMap K₀ C).comp (algebraMap 𝒪 K₀))))
    (P : Spec (CommRingCat.of R) ⟶ 𝒴) (hP : P ≫ fY = Scheme.specOver R) :
    ∃ q : Spec (CommRingCat.of C) ⟶ Limits.pullback fY sC,
      q ≫ Limits.pullback.fst fY sC = Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ P ∧
      q ≫ Limits.pullback.snd fY sC = 𝟙 (Spec (CommRingCat.of C)) := by
  refine ⟨Limits.pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ P) (𝟙 _) ?_,
    Limits.pullback.lift_fst _ _ _, Limits.pullback.lift_snd _ _ _⟩
  rw [Category.assoc, hP, Category.id_comp, hsC, Scheme.specOver, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]

theorem hom_eq_of_forall_modPow {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {R : Type} [CommRing R] [Algebra 𝒪 R] [IsLocalRing R]
    (hR : IsAdicComplete (Ideal.span {algebraMap 𝒪 R π}) R) {X : Scheme.{0}} {y₁ y₂ : Spec (CommRingCat.of R) ⟶ X}
    (h : ∀ n : ℕ, Spec.map (CommRingCat.ofHom (algebraMap R (modPow π R n))) ≫ y₁ =
      Spec.map (CommRingCat.ofHom (algebraMap R (modPow π R n))) ≫ y₂) :
    y₁ = y₂ := by
  have htr : ∀ n : ℕ, (modPowTransition π R n).toRingHom.comp (algebraMap R (modPow π R (n + 1))) =
      algebraMap R (modPow π R n) := fun n => RingHom.ext fun _ => rfl
  obtain ⟨y, -, huniq⟩ := existsUnique_hom_comp_eq_of_compatible_modPow π R hR
    (fun n => Spec.map (CommRingCat.ofHom (algebraMap R (modPow π R n))) ≫ y₂) (fun n => by
      rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, htr])
  exact (huniq y₁ h).trans (huniq y₂ fun _ => rfl).symm

theorem rPoint_comp_eq
    {𝒪 : Type} [CommRing 𝒪] {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀] (π : 𝒪)
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (vdet : Matrix.GeneralLinearGroup (Fin 2) K₀ →* Multiplicative ℤ)
    {R : Type} [CommRing R] [Algebra 𝒪 R] [IsLocalRing R]
    (hR : IsAdicComplete (Ideal.span {algebraMap 𝒪 R π}) R) (ψ₀ : Onr →ₐ[𝒪] R)
    {𝒳 𝒴 : Scheme.{0}} (f : 𝒳 ⟶ Spec (CommRingCat.of 𝒪)) (fY : 𝒴 ⟶ Spec (CommRingCat.of 𝒪))
    (Θ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
      (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B → (Scheme.nilpPoints f).obj B)
    (ΘY : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
      (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B → (Scheme.nilpPoints fY).obj B)
    (h : 𝒴 ⟶ 𝒳) (hhf : h ≫ f = fY) (g₀ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₀ : vdet g₀ = 1)
    (hh : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
        (x x' : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
        OmegaNr.IsTwistedAct π Onr Fr vdet B g₀ x x' →
          (Scheme.nilpPoints.mapHom fY f h hhf).app B (ΘY B hB x) = Θ B hB x')
    (PX : AdicPoint K₀ π R → (Spec (CommRingCat.of R) ⟶ 𝒳))
    (PY : AdicPoint K₀ π R → (Spec (CommRingCat.of R) ⟶ 𝒴))
    (hPX : ∀ (x : AdicPoint K₀ π R) (n : ℕ),
        Spec.map (CommRingCat.ofHom (algebraMap R (modPow π R n))) ≫ PX x =
          (Θ (modPow π R n) (isNilpotent_algebraMap_modPow π R n)
            (((Ideal.Quotient.mkₐ 𝒪 (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})).comp ψ₀), x.pt n)).1)
    (hPY : ∀ (x : AdicPoint K₀ π R) (n : ℕ),
        Spec.map (CommRingCat.ofHom (algebraMap R (modPow π R n))) ≫ PY x =
          (ΘY (modPow π R n) (isNilpotent_algebraMap_modPow π R n)
            (((Ideal.Quotient.mkₐ 𝒪 (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})).comp ψ₀), x.pt n)).1)
    (x : AdicPoint K₀ π R) :
    PY x ≫ h = PX (x.act g₀) := by
  refine hom_eq_of_forall_modPow π hR fun n => ?_
  rw [← Category.assoc, hPY x n, hPX (x.act g₀) n]
  have htw : OmegaNr.IsTwistedAct π Onr Fr vdet (modPow π R n) g₀
      (((Ideal.Quotient.mkₐ 𝒪 (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})).comp ψ₀), x.pt n)
      (((Ideal.Quotient.mkₐ 𝒪 (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})).comp ψ₀), (x.act g₀).pt n) := by
    refine ⟨?_, fun M => rfl⟩
    show _ = frobTwist Onr Fr (-Multiplicative.toAdd (vdet g₀)) _
    rw [hg₀, toAdd_one, neg_zero, frobTwist, zpow_zero]
    ext y
    rfl
  exact congrArg Subtype.val (hh _ _ _ _ htw)

end SchemeSide

end KcEvalRiderEngine

set_option linter.unusedVariables false in

theorem solution

    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (K₀ : Type) [Field K₀] [CharZero K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]

    (Onr : Type) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (vdet : Matrix.GeneralLinearGroup (Fin 2) K₀ →* Multiplicative ℤ)
    (hvdet : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℤ), vdet g = Multiplicative.ofAdd n ↔
      ∃ u : 𝒪ˣ, (Matrix.GeneralLinearGroup.det g : K₀) = algebraMap 𝒪 K₀ (u : 𝒪) * (algebraMap 𝒪 K₀ π) ^ n)

    (G : Type) [Group G] (σ : G →* Matrix.GeneralLinearGroup (Fin 2) K₀) (Γ : Subgroup G)
    (hcent : ∃ z ∈ Γ, ∃ c : K₀, ((σ z : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀) = c • (1 : Matrix (Fin 2) (Fin 2) K₀) ∧
      vdet (σ z) = Multiplicative.ofAdd (2 : ℤ))
    (hodd : ∃ w ∈ Γ, vdet (σ w) = Multiplicative.ofAdd (1 : ℤ))
    (Γ' : Subgroup G) (hΓ' : ∀ x : G, x ∈ Γ' ↔ x ∈ Γ ∧ Even (Multiplicative.toAdd (vdet (σ x))))

    (ρ : G →* PGL(2, K₀)) (hρ : ∀ g : G, ρ g = Matrix.ProjGenLinGroup.mk (σ g))
    (hdisc : ∀ v : LT.LatticeTree.Vertex 𝒪 K₀, Set.Finite {g : PGL(2, K₀) | g ∈ Γ'.map ρ ∧ g • v = v})
    (hcocpt : ∃ S : Finset (LT.LatticeTree.Vertex 𝒪 K₀), ∀ v : LT.LatticeTree.Vertex 𝒪 K₀, ∃ g ∈ Γ'.map ρ, g • v ∈ S)

    (𝒳 : Scheme.{0}) (f : 𝒳 ⟶ Spec (CommRingCat.of 𝒪)) [IsProper f] [Flat f]

    (Θ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
      (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B → (Scheme.nilpPoints f).obj B)
    (hΘnat : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
      (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
      Θ B' hB' ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ x) = (Scheme.nilpPoints f).map φ (Θ B hB x))
    (hΘinv : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (γ : G), γ ∈ Γ →
      ∀ x x' : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B,
        OmegaNr.IsTwistedAct π Onr Fr vdet B (σ γ) x x' → Θ B hB x' = Θ B hB x)
    (hΘfib : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra 𝒪 k] (hk : IsNilpotent (algebraMap 𝒪 k π)) (ψ : Onr →ₐ[𝒪] k),
      (∀ y : (Scheme.nilpPoints f).obj k, ∃ P : (Omega K₀ π).obj k, Θ k hk (ψ, P) = y) ∧
      ∀ P P' : (Omega K₀ π).obj k, Θ k hk (ψ, P) = Θ k hk (ψ, P') ↔
        ∃ γ ∈ Γ, OmegaNr.IsTwistedAct π Onr Fr vdet k (σ γ) (ψ, P) (ψ, P'))
    (hΘuniv : ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of 𝒪))
      (ρ' : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
        (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B → (Scheme.nilpPoints t).obj B),
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
        (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
        ρ' B' hB' ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ x) = (Scheme.nilpPoints t).map φ (ρ' B hB x)) →
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (γ : G), γ ∈ Γ →
        ∀ x x' : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B,
          OmegaNr.IsTwistedAct π Onr Fr vdet B (σ γ) x x' → ρ' B hB x' = ρ' B hB x) →
      ∃ u : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
          (Scheme.nilpPoints f).obj B → (Scheme.nilpPoints t).obj B,
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (y : (Scheme.nilpPoints f).obj B),
          u B' hB' ((Scheme.nilpPoints f).map φ y) = (Scheme.nilpPoints t).map φ (u B hB y)) ∧
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
          (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B), u B hB (Θ B hB x) = ρ' B hB x) ∧
        ∀ u' : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
            (Scheme.nilpPoints f).obj B → (Scheme.nilpPoints t).obj B,
          (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
            (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (y : (Scheme.nilpPoints f).obj B),
            u' B' hB' ((Scheme.nilpPoints f).map φ y) = (Scheme.nilpPoints t).map φ (u' B hB y)) →
          (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
            (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B), u' B hB (Θ B hB x) = ρ' B hB x) →
          ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (y : (Scheme.nilpPoints f).obj B),
            u' B hB y = u B hB y)

    (𝒴 : Scheme.{0}) (fY : 𝒴 ⟶ Spec (CommRingCat.of 𝒪)) [IsProper fY] [Flat fY] (ΓY' : Subgroup G)
    (ΘY : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
      (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B → (Scheme.nilpPoints fY).obj B)
    (hΘYnat : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
      (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
      ΘY B' hB' ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ x) = (Scheme.nilpPoints fY).map φ (ΘY B hB x))

    {C : Type} [Field C] [Algebra K₀ C] [DecidableEq C] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
    [CompleteSpace C] [IsAlgClosed C]
    {R : Type} [CommRing R] [Algebra 𝒪 R] [Algebra R C] [Algebra 𝒪 C] [IsScalarTower 𝒪 R C] [IsScalarTower 𝒪 K₀ C]
    (ϖ : PseudoUniformizer K₀ C) (hF : IsAdicFrame π ϖ R)
    (ψ₀ : Onr →ₐ[𝒪] R)
    (hrk : ∀ x y : C, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hval : ∀ ε : Γ₀, ε ≠ 0 → ∃ y : C, y ≠ 0 ∧ Valued.v y ≤ ε)
    (hex : Omega.IsExhausted ϖ) [IsDomain (Omega.HolRingOf ϖ ρ)]

    (Φ : AdicPoint K₀ π R → {p : Spec (CommRingCat.of R) ⟶ 𝒳 // p ≫ f = Scheme.specOver R})
    (hΦ : (∀ (x : AdicPoint K₀ π R) (n : ℕ),
        Spec.map (CommRingCat.ofHom (algebraMap R (modPow π R n))) ≫ (Φ x).1 =
          (Θ (modPow π R n) (isNilpotent_algebraMap_modPow π R n)
            (((Ideal.Quotient.mkₐ 𝒪 (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})).comp ψ₀), x.pt n)).1) ∧
      Function.Surjective Φ ∧
      (∀ x x' : AdicPoint K₀ π R, Φ x = Φ x' ↔ ∃ γ ∈ Γ', x' = x.act (σ γ)) ∧
      (Function.Injective (fun p : {p : Spec (CommRingCat.of R) ⟶ 𝒳 // p ≫ f = Scheme.specOver R} =>
          Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ p.1) ∧
        ∀ cpt : Spec (CommRingCat.of C) ⟶ 𝒳, cpt ≫ f = Scheme.specOver C →
          ∃ p : {p : Spec (CommRingCat.of R) ⟶ 𝒳 // p ≫ f = Scheme.specOver R},
            Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ p.1 = cpt))

    (ΦY : AdicPoint K₀ π R → {p : Spec (CommRingCat.of R) ⟶ 𝒴 // p ≫ fY = Scheme.specOver R})
    (hΦY : (∀ (x : AdicPoint K₀ π R) (n : ℕ),
        Spec.map (CommRingCat.ofHom (algebraMap R (modPow π R n))) ≫ (ΦY x).1 =
          (ΘY (modPow π R n) (isNilpotent_algebraMap_modPow π R n)
            (((Ideal.Quotient.mkₐ 𝒪 (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})).comp ψ₀), x.pt n)).1) ∧
      Function.Surjective ΦY ∧
      (∀ x x' : AdicPoint K₀ π R, ΦY x = ΦY x' ↔ ∃ γ ∈ ΓY', x' = x.act (σ γ)) ∧
      (Function.Injective (fun p : {p : Spec (CommRingCat.of R) ⟶ 𝒴 // p ≫ fY = Scheme.specOver R} =>
          Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ p.1) ∧
        ∀ cpt : Spec (CommRingCat.of C) ⟶ 𝒴, cpt ≫ fY = Scheme.specOver C →
          ∃ p : {p : Spec (CommRingCat.of R) ⟶ 𝒴 // p ≫ fY = Scheme.specOver R},
            Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ p.1 = cpt))

    (sC : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of 𝒪))
    (hsC : sC = Spec.map (CommRingCat.ofHom ((algebraMap K₀ C).comp (algebraMap 𝒪 K₀))))
    [IsIntegral (Limits.pullback f sC)] [IsIntegral (Limits.pullback fY sC)]

    (e : ↑(Limits.pullback f sC).functionField →+* ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ'))
    (heval : (∀ (U : (Limits.pullback f sC).Opens) (hU : genericPoint (Limits.pullback f sC : Scheme.{0}) ∈ U)
        (s : (Limits.pullback f sC).presheaf.obj (Opposite.op U)),
        ∃ (a b : Omega.HolRingOf ϖ ρ) (hb : b ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ)),
          ((e (((Limits.pullback f sC).presheaf.germ U (genericPoint (Limits.pullback f sC : Scheme.{0})) hU).hom s) : ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ')) : FractionRing (Omega.HolRingOf ϖ ρ)) =
              Localization.mk a ⟨b, hb⟩ ∧
          ∀ (x : AdicPoint K₀ π R) (z : ↥(Omega.upperHalfPlane K₀ C)), (z : C) = x.toOmega C →
            ∀ (q : Spec (CommRingCat.of C) ⟶ Limits.pullback f sC),
              q ≫ Limits.pullback.fst f sC = Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ (Φ x).1 →
              q ≫ Limits.pullback.snd f sC = 𝟙 (Spec (CommRingCat.of C)) →
              ∀ (hqU : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ q ⁻¹ᵁ U),
                (show ↥(Omega.holRing ϖ) from b : ↥(Omega.upperHalfPlane K₀ C) → C) z *
                    (Scheme.ΓSpecIso (CommRingCat.of C)).hom.hom
                (((Spec (CommRingCat.of C)).presheaf.map (homOfLE hqU).op).hom ((q.app U).hom s)) =
                  (show ↥(Omega.holRing ϖ) from a : ↥(Omega.upperHalfPlane K₀ C) → C) z))
    (eY : ↑(Limits.pullback fY sC).functionField →+* ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) ΓY'))
    (heYval : (∀ (U : (Limits.pullback fY sC).Opens) (hU : genericPoint (Limits.pullback fY sC : Scheme.{0}) ∈ U)
        (s : (Limits.pullback fY sC).presheaf.obj (Opposite.op U)),
        ∃ (a b : Omega.HolRingOf ϖ ρ) (hb : b ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ)),
          ((eY (((Limits.pullback fY sC).presheaf.germ U (genericPoint (Limits.pullback fY sC : Scheme.{0})) hU).hom s) : ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) ΓY')) : FractionRing (Omega.HolRingOf ϖ ρ)) =
              Localization.mk a ⟨b, hb⟩ ∧
          ∀ (x : AdicPoint K₀ π R) (z : ↥(Omega.upperHalfPlane K₀ C)), (z : C) = x.toOmega C →
            ∀ (q : Spec (CommRingCat.of C) ⟶ Limits.pullback fY sC),
              q ≫ Limits.pullback.fst fY sC = Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ (ΦY x).1 →
              q ≫ Limits.pullback.snd fY sC = 𝟙 (Spec (CommRingCat.of C)) →
              ∀ (hqU : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ q ⁻¹ᵁ U),
                (show ↥(Omega.holRing ϖ) from b : ↥(Omega.upperHalfPlane K₀ C) → C) z *
                    (Scheme.ΓSpecIso (CommRingCat.of C)).hom.hom
                (((Spec (CommRingCat.of C)).presheaf.map (homOfLE hqU).op).hom ((q.app U).hom s)) =
                  (show ↥(Omega.holRing ϖ) from a : ↥(Omega.upperHalfPlane K₀ C) → C) z))

    (hfin : (∀ (U : (Limits.pullback f sC).Opens) (hU : genericPoint (Limits.pullback f sC : Scheme.{0}) ∈ U) (n : ℕ),
        Set.Finite {z : ↥(Omega.affinoid ϖ n) | ∃ x : AdicPoint K₀ π R, (z : C) = x.toOmega C ∧
          ∃ q : Spec (CommRingCat.of C) ⟶ Limits.pullback f sC,
            q ≫ Limits.pullback.fst f sC = Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ (Φ x).1 ∧
            q ≫ Limits.pullback.snd f sC = 𝟙 (Spec (CommRingCat.of C)) ∧
            ¬ ((⊤ : (Spec (CommRingCat.of C)).Opens) ≤ q ⁻¹ᵁ U)}))
    (hfinY : (∀ (U : (Limits.pullback fY sC).Opens) (hU : genericPoint (Limits.pullback fY sC : Scheme.{0}) ∈ U) (n : ℕ),
        Set.Finite {z : ↥(Omega.affinoid ϖ n) | ∃ x : AdicPoint K₀ π R, (z : C) = x.toOmega C ∧
          ∃ q : Spec (CommRingCat.of C) ⟶ Limits.pullback fY sC,
            q ≫ Limits.pullback.fst fY sC = Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ (ΦY x).1 ∧
            q ≫ Limits.pullback.snd fY sC = 𝟙 (Spec (CommRingCat.of C)) ∧
            ¬ ((⊤ : (Spec (CommRingCat.of C)).Opens) ≤ q ⁻¹ᵁ U)}))

    (h : 𝒴 ⟶ 𝒳) (hhf : h ≫ f = fY) (g : G) (hg : vdet (σ g) = 1)
    (hh : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
        (x x' : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
        OmegaNr.IsTwistedAct π Onr Fr vdet B (σ g) x x' →
          (Scheme.nilpPoints.mapHom fY f h hhf).app B (ΘY B hB x) = Θ B hB x')
    (hC : Limits.pullback fY sC ⟶ Limits.pullback f sC)
    (hhC₁ : hC ≫ Limits.pullback.fst f sC = Limits.pullback.fst fY sC ≫ h)
    (hhC₂ : hC ≫ Limits.pullback.snd f sC = Limits.pullback.snd fY sC) :
    ∀ (U : (Limits.pullback f sC).Opens) (hU : genericPoint (Limits.pullback f sC : Scheme.{0}) ∈ U)
      (hU' : genericPoint (Limits.pullback fY sC : Scheme.{0}) ∈ hC ⁻¹ᵁ U) (sec : (Limits.pullback f sC).presheaf.obj (Opposite.op U)),
      ((eY (((Limits.pullback fY sC).presheaf.germ (hC ⁻¹ᵁ U) (genericPoint (Limits.pullback fY sC : Scheme.{0})) hU').hom ((hC.app U).hom sec)) :
          ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) ΓY')) : FractionRing (Omega.HolRingOf ϖ ρ)) =
        g⁻¹ • ((e (((Limits.pullback f sC).presheaf.germ U (genericPoint (Limits.pullback f sC : Scheme.{0})) hU).hom sec) : ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ')) : FractionRing (Omega.HolRingOf ϖ ρ)) := by
  intro U hU hU' sec
  haveI : IsDiscreteValuationRing 𝒪 := hdvr
  haveI : IsLocalRing R := KcEvalRiderEngine.isLocalRing hF
  have hΦa := hΦ.1
  have hΦYa := hΦY.1
  obtain ⟨a₂, b₂, hb₂, he₂, hv₂⟩ := heval U hU sec
  obtain ⟨a₁, b₁, hb₁, he₁, hv₁⟩ := heYval (hC ⁻¹ᵁ U) hU' ((hC.app U).hom sec)
  rw [he₁, he₂]

  have hA : ∀ x : AdicPoint K₀ π R, (ΦY x).1 ≫ h = (Φ (x.act (σ g))).1 := fun x =>
    KcEvalRiderEngine.rPoint_comp_eq π Onr Fr vdet hF.complete ψ₀ f fY Θ ΘY h hhf (σ g) hg hh
      (fun x => (Φ x).1) (fun x => (ΦY x).1) hΦa hΦYa x

  refine KcEvalRiderEngine.frac_eq ϖ hrk (KcEvalRiderEngine.locCompact hdvr hπ hres hF hrk hval)
    (KcEvalRiderEngine.small ϖ hval) hex ρ a₁ b₁ a₂ b₂ hb₁ hb₂ g
    (fun n => {z : ↥(Omega.affinoid ϖ n) | ∃ x : AdicPoint K₀ π R, (z : C) = x.toOmega C ∧
          ∃ q : Spec (CommRingCat.of C) ⟶ Limits.pullback fY sC,
            q ≫ Limits.pullback.fst fY sC = Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ (ΦY x).1 ∧
            q ≫ Limits.pullback.snd fY sC = 𝟙 (Spec (CommRingCat.of C)) ∧
            ¬ ((⊤ : (Spec (CommRingCat.of C)).Opens) ≤ q ⁻¹ᵁ (hC ⁻¹ᵁ U))})
    (fun n => hfinY (hC ⁻¹ᵁ U) hU' n) (fun n z hz => ?_)
  have hzΩ : (z : C) ∈ Omega.upperHalfPlane K₀ C := Omega.affinoid_subset_upperHalfPlane ϖ n z.2
  obtain ⟨x, -, hx⟩ := AdicPoint.toOmega_surjOn ϖ hF hzΩ
  obtain ⟨q', hq'₁, hq'₂⟩ := KcEvalRiderEngine.exists_cPoint fY sC hsC (ΦY x).1 (ΦY x).2
  have hqU : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ q' ⁻¹ᵁ (hC ⁻¹ᵁ U) := by
    by_contra hcon
    exact hz ⟨x, hx.symm, q', hq'₁, hq'₂, hcon⟩
  have hz1 : ((⟨(z : C), hzΩ⟩ : ↥(Omega.upperHalfPlane K₀ C)) : C) = x.toOmega C := hx.symm
  have hz2 : ((ρ g • (⟨(z : C), hzΩ⟩ : ↥(Omega.upperHalfPlane K₀ C)) : ↥(Omega.upperHalfPlane K₀ C)) : C) =
      (x.act (σ g)).toOmega C := by
    rw [Omega.coe_smul_upperHalfPlane, AdicPoint.toOmega_act ϖ hF (σ g) x, hρ g, ← hz1]
  have hQ₁ : (q' ≫ hC) ≫ Limits.pullback.fst f sC =
      Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ (Φ (x.act (σ g))).1 := by
    rw [Category.assoc, hhC₁, ← Category.assoc, hq'₁, Category.assoc, hA x]
  have hQ₂ : (q' ≫ hC) ≫ Limits.pullback.snd f sC = 𝟙 (Spec (CommRingCat.of C)) := by
    rw [Category.assoc, hhC₂, hq'₂]
  have e1 := hv₁ x ⟨(z : C), hzΩ⟩ hz1 q' hq'₁ hq'₂ hqU
  have e2 := hv₂ (x.act (σ g)) (ρ g • ⟨(z : C), hzΩ⟩) hz2 (q' ≫ hC) hQ₁ hQ₂ hqU
  exact KcEvalRiderEngine.cross e1 e2

end S_CerednikDrinfeld_ringHom_functionField_germ_app_eq_inv_smul_of_eval_of_cerednikDrinfeld_quotient
end P2MW
export P2MW.S_CerednikDrinfeld_ringHom_functionField_germ_app_eq_inv_smul_of_eval_of_cerednikDrinfeld_quotient (solution)
