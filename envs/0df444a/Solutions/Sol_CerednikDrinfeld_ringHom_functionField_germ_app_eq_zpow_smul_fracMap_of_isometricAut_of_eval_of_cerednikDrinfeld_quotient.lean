-- Prove2me | solution 1 for CerednikDrinfeld.ringHom_functionField_germ_app_eq_zpow_smul_fracMap_of_isometricAut_of_eval_of_cerednikDrinfeld_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/b579f028-f35c-5554-a749-ac27ea58ab34

import Theorems.Thm_CerednikDrinfeld_FormalOmega_existsUnique_hom_comp_eq_of_compatible_modPow
import Theorems.Thm_CerednikDrinfeld_FormalOmega_AdicPoint_toOmega_act
import Theorems.Thm_CerednikDrinfeld_FormalOmega_AdicPoint_toOmega_surjOn
import Theorems.Thm_CerednikDrinfeld_Omega_finite_setOf_apply_eq_zero_of_mem_holOn_affinoid
import Theorems.Thm_CerednikDrinfeld_Omega_forall_exists_finset_v_sub_lt_pow_of_finite_quotient
import Theorems.Thm_CerednikDrinfeld_FormalOmega_AdicPoint_exists_pt_eq_map_and_toOmega_eq_of_algEquiv
import Theorems.Thm_CerednikDrinfeld_specPoint_eq_specMap_comp_of_map_pt_eq_act_pt_of_cerednikDrinfeld_quotient
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFrame
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_ringHom_functionField_germ_app_eq_zpow_smul_fracMap_of_isometricAut_of_eval_of_cerednikDrinfeld_quotient
p2m_attr_erase "instance" "CerednikDrinfeld.FormalOmega.edgeQuot.instCommRing CerednikDrinfeld.FormalOmega.edgeQuot.instAlgebra CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₀"
p2m_attr_erase "simp" "CerednikDrinfeld.Mumford.smulHom_apply CerednikDrinfeld.Mumford.smulHom_mapDart CerednikDrinfeld.Mumford.walkCycle_nil LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq LocalGL2.swapUnit_val"

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega CerednikDrinfeld.Mumford AlgebraicCurve

namespace KcEvalRiderKitGal

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

end SchemeSide

end KcEvalRiderKitGal

namespace GalEv

universe u

noncomputable def ev {C : Type u} [CommRing C] {X : Scheme.{u}} (q : Spec (CommRingCat.of C) ⟶ X)
    (O : X.Opens) (h : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ q ⁻¹ᵁ O) : Γ(X, O) →+* C :=
  ((q.appLE O ⊤ h) ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom).hom

theorem ev_apply {C : Type u} [CommRing C] {X : Scheme.{u}} (q : Spec (CommRingCat.of C) ⟶ X)
    (O : X.Opens) (h : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ q ⁻¹ᵁ O) (t : Γ(X, O)) :
    ev q O h t = (Scheme.ΓSpecIso (CommRingCat.of C)).hom.hom
      (((Spec (CommRingCat.of C)).presheaf.map (homOfLE h).op).hom ((q.app O).hom t)) := rfl

theorem ev_res {C : Type u} [CommRing C] {X : Scheme.{u}} (q : Spec (CommRingCat.of C) ⟶ X)
    {O O' : X.Opens} (hO : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ q ⁻¹ᵁ O) (hO' : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ q ⁻¹ᵁ O')
    (e : O' ≤ O) (t : Γ(X, O)) :
    ev q O' hO' ((X.presheaf.map (homOfLE e).op).hom t) = ev q O hO t := by
  show (X.presheaf.map (homOfLE e).op ≫ q.appLE O' ⊤ hO' ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom).hom t = _
  rw [Scheme.Hom.map_appLE_assoc]
  rfl

theorem ev_comp {C : Type u} [CommRing C] {X Y : Scheme.{u}} (q : Spec (CommRingCat.of C) ⟶ X) (φ : X ⟶ Y)
    (O : Y.Opens) (O' : X.Opens) (hO' : O' ≤ φ ⁻¹ᵁ O) (h : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ q ⁻¹ᵁ O')
    (h' : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ (q ≫ φ) ⁻¹ᵁ O) (t : Γ(Y, O)) :
    ev q O' h ((φ.appLE O O' hO').hom t) = ev (q ≫ φ) O h' t := by
  show (φ.appLE O O' hO' ≫ q.appLE O' ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom).hom t = _
  rw [Scheme.Hom.appLE_comp_appLE_assoc]
  rfl

theorem ev_specMap {R C : Type u} [CommRing R] [CommRing C] (φ : R →+* C) (t : Γ(Spec (CommRingCat.of R), ⊤))
    (h : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ (Spec.map (CommRingCat.ofHom φ)) ⁻¹ᵁ ⊤) :
    ev (Spec.map (CommRingCat.ofHom φ)) ⊤ h t = φ ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom t) := by
  show ((Spec.map (CommRingCat.ofHom φ)).app ⊤ ≫ (Spec (CommRingCat.of C)).presheaf.map (homOfLE h).op ≫
      (Scheme.ΓSpecIso (CommRingCat.of C)).hom).hom t = _
  have : (Spec (CommRingCat.of C)).presheaf.map (homOfLE h).op = 𝟙 _ := by
    have : homOfLE h = 𝟙 _ := rfl
    rw [this]; exact (Spec (CommRingCat.of C)).presheaf.map_id _
  rw [this]
  erw [Category.id_comp]
  change ((Spec.map (CommRingCat.ofHom φ)).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom).hom t = _
  rw [Scheme.ΓSpecIso_naturality]
  rfl

theorem ev_id {C : Type u} [CommRing C] (t : Γ(Spec (CommRingCat.of C), ⊤))
    (h : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ (𝟙 (Spec (CommRingCat.of C))) ⁻¹ᵁ ⊤) :
    ev (𝟙 (Spec (CommRingCat.of C))) ⊤ h t = (Scheme.ΓSpecIso (CommRingCat.of C)).hom.hom t := by
  show ((𝟙 (Spec (CommRingCat.of C)) : Spec (CommRingCat.of C) ⟶ _).app ⊤ ≫
      (Spec (CommRingCat.of C)).presheaf.map (homOfLE h).op ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom).hom t = _
  have : (Spec (CommRingCat.of C)).presheaf.map (homOfLE h).op = 𝟙 _ := by
    have : homOfLE h = 𝟙 _ := rfl
    rw [this]; exact (Spec (CommRingCat.of C)).presheaf.map_id _
  rw [this, AlgebraicGeometry.Scheme.Hom.id_app]
  erw [Category.id_comp, Category.id_comp]

end GalEv

namespace GalAux

open CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega

theorem exists_restrict
    {𝒪 : Type} [CommRing 𝒪] {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀]
    {C : Type} [Field C] [Algebra K₀ C] [DecidableEq C] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
    {π : 𝒪} {ϖ : PseudoUniformizer K₀ C} {R : Type} [CommRing R] [Algebra 𝒪 R] [Algebra R C]
    [Algebra 𝒪 C] [IsScalarTower 𝒪 R C] [IsScalarTower 𝒪 K₀ C]
    (hF : IsAdicFrame π ϖ R) (s : IsometricAut K₀ C) :
    ∃ τ : R ≃ₐ[𝒪] R, ∀ a : R, algebraMap R C (τ a) = s.toRingEquiv (algebraMap R C a) := by
  classical

  have hex : ∀ (t : IsometricAut K₀ C) (a : R), ∃ b : R, algebraMap R C b = t.toRingEquiv (algebraMap R C a) := by
    intro t a
    obtain ⟨b, hb⟩ := (hF.range_eq (t.toRingEquiv (algebraMap R C a))).mp (by rw [t.isometry]; exact hF.v_algebraMap_le_one a)
    exact ⟨b, hb⟩
  choose F hF' using hex s
  choose Fi hFi using hex s⁻¹
  have hinj := hF.injective
  have hsi : ∀ c : C, (s⁻¹).toRingEquiv c = s.toRingEquiv.symm c := fun c => rfl
  let e : R ≃+* R :=
    { toFun := F
      invFun := Fi
      left_inv := fun a => hinj (by rw [hFi, hF', hsi, RingEquiv.symm_apply_apply])
      right_inv := fun a => hinj (by rw [hF', hFi, hsi, RingEquiv.apply_symm_apply])
      map_mul' := fun a b => hinj (by rw [hF', map_mul, map_mul, map_mul, hF', hF'])
      map_add' := fun a b => hinj (by rw [hF', map_add, map_add, map_add, hF', hF']) }
  refine ⟨AlgEquiv.ofRingEquiv (f := e) fun o => hinj ?_, fun a => hF' a⟩
  show algebraMap R C (F (algebraMap 𝒪 R o)) = algebraMap R C (algebraMap 𝒪 R o)
  rw [hF', ← IsScalarTower.algebraMap_apply 𝒪 R C, IsScalarTower.algebraMap_apply 𝒪 K₀ C, s.fix]

noncomputable def redMap {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {R : Type} [CommRing R] [Algebra 𝒪 R] (τ : R →ₐ[𝒪] R) (k : ℕ) :
    modPow π R k →ₐ[𝒪] modPow π R k :=
  Ideal.quotientMapₐ (Ideal.span {algebraMap 𝒪 R π ^ (k + 1)}) τ (by
    rw [Ideal.span_le]
    intro a ha
    rw [Set.mem_singleton_iff.mp ha]
    show algebraMap 𝒪 R π ^ (k + 1) ∈ Ideal.comap τ (Ideal.span {algebraMap 𝒪 R π ^ (k + 1)})
    rw [Ideal.mem_comap, map_pow, AlgHom.commutes]
    exact Ideal.subset_span (Set.mem_singleton _))

theorem redMap_mk {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {R : Type} [CommRing R] [Algebra 𝒪 R] (τ : R →ₐ[𝒪] R) (k : ℕ) (a : R) :
    redMap π τ k (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (k + 1)}) a) =
      Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (k + 1)}) (τ a) := by
  unfold redMap
  rw [Ideal.quotient_map_mkₐ]
  rfl

end GalAux

set_option maxHeartbeats 1600000 in
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

    (sC : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of 𝒪))
    (hsC : sC = Spec.map (CommRingCat.ofHom ((algebraMap K₀ C).comp (algebraMap 𝒪 K₀))))
    [IsIntegral (Limits.pullback f sC)]

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
    (hfin : (∀ (U : (Limits.pullback f sC).Opens) (hU : genericPoint (Limits.pullback f sC : Scheme.{0}) ∈ U) (n : ℕ),
        Set.Finite {z : ↥(Omega.affinoid ϖ n) | ∃ x : AdicPoint K₀ π R, (z : C) = x.toOmega C ∧
          ∃ q : Spec (CommRingCat.of C) ⟶ Limits.pullback f sC,
            q ≫ Limits.pullback.fst f sC = Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ (Φ x).1 ∧
            q ≫ Limits.pullback.snd f sC = 𝟙 (Spec (CommRingCat.of C)) ∧
            ¬ ((⊤ : (Spec (CommRingCat.of C)).Opens) ≤ q ⁻¹ᵁ U)}))

    (s : Omega.IsometricAut K₀ C) (n : ℤ)
    (hs : ∀ y : Onr, Fr (Fr y) = y → s.toRingEquiv (algebraMap R C (ψ₀ y)) = algebraMap R C (ψ₀ ((Fr ^ n : Onr ≃ₐ[𝒪] Onr) y)))
    (tC : Limits.pullback f sC ⟶ Limits.pullback f sC)
    (htC₁ : tC ≫ Limits.pullback.fst f sC = Limits.pullback.fst f sC)
    (htC₂ : tC ≫ Limits.pullback.snd f sC = Limits.pullback.snd f sC ≫ Spec.map (CommRingCat.ofHom (s.toRingEquiv : C →+* C)))
    (w : G) (hw : w ∈ Γ) (hw₁ : vdet (σ w) = Multiplicative.ofAdd (1 : ℤ)) :
    ∀ (U : (Limits.pullback f sC).Opens) (hU : genericPoint (Limits.pullback f sC : Scheme.{0}) ∈ U)
      (hU' : genericPoint (Limits.pullback f sC : Scheme.{0}) ∈ tC ⁻¹ᵁ U) (sec : (Limits.pullback f sC).presheaf.obj (Opposite.op U)),
      ((e (((Limits.pullback f sC).presheaf.germ (tC ⁻¹ᵁ U) (genericPoint (Limits.pullback f sC : Scheme.{0})) hU').hom ((tC.app U).hom sec)) : ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ')) : FractionRing (Omega.HolRingOf ϖ ρ)) =
        w ^ n • Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ ρ s)
          ((e (((Limits.pullback f sC).presheaf.germ U (genericPoint (Limits.pullback f sC : Scheme.{0})) hU).hom sec) : ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ')) : FractionRing (Omega.HolRingOf ϖ ρ)) := by
  classical
  intro U hU hU' sec
  haveI : IsDiscreteValuationRing 𝒪 := hdvr
  haveI : IsLocalRing R := KcEvalRiderKitGal.isLocalRing hF
  have hΦa := hΦ.1
  obtain ⟨a₂, b₂, hb₂, he₂, hv₂⟩ := heval U hU sec
  obtain ⟨a₁, b₁, hb₁, he₁, hv₁⟩ := heval (tC ⁻¹ᵁ U) hU' ((tC.app U).hom sec)
  rw [he₁, he₂]

  obtain ⟨τ, hτ⟩ := GalAux.exists_restrict hF s
  have hτ' : ∀ a : R, algebraMap R C (τ.symm a) = s.toRingEquiv.symm (algebraMap R C a) := fun a => by
    apply s.toRingEquiv.injective
    rw [← hτ, AlgEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  let τn : ∀ k : ℕ, modPow π R k →ₐ[𝒪] modPow π R k := fun k => GalAux.redMap π (τ : R →ₐ[𝒪] R) k
  let τn' : ∀ k : ℕ, modPow π R k →ₐ[𝒪] modPow π R k := fun k => GalAux.redMap π (τ.symm : R →ₐ[𝒪] R) k
  have hτn : ∀ (k : ℕ) (a : R), τn k (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (k + 1)}) a) =
      Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (k + 1)}) (τ a) := fun k a => GalAux.redMap_mk π _ k a
  have hτn' : ∀ (k : ℕ) (a : R), τn' k (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (k + 1)}) a) =
      Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (k + 1)}) (τ.symm a) := fun k a => GalAux.redMap_mk π _ k a
  have hcomp : ∀ k : ℕ, (τn k).comp (τn' k) = AlgHom.id 𝒪 _ := by
    intro k
    apply Ideal.Quotient.algHom_ext
    apply AlgHom.ext
    intro a
    show τn k (τn' k (Ideal.Quotient.mk _ a)) = Ideal.Quotient.mk _ a
    rw [hτn', hτn, AlgEquiv.apply_symm_apply]
  have hψτ : ∀ y : Onr, Fr (Fr y) = y → τ (ψ₀ y) = ψ₀ ((Fr ^ n : Onr ≃ₐ[𝒪] Onr) y) := fun y hy =>
    hF.injective (by rw [hτ, hs y hy])

  set g : G := w ^ (-n) with hg
  set σs := Omega.toAmbientOf ϖ ρ s with hσs
  have hb₂0 : b₂ ≠ 0 := nonZeroDivisors.ne_zero hb₂
  have hb₂' : σs.map b₂ ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ) :=
    mem_nonZeroDivisors_of_ne_zero (by rw [map_ne_zero_iff _ σs.map.injective]; exact hb₂0)
  have hfrac : Mumford.AmbientSemilinearAut.fracMap σs (Localization.mk a₂ ⟨b₂, hb₂⟩) =
      Localization.mk (σs.map a₂) ⟨σs.map b₂, hb₂'⟩ := by
    simp only [Localization.mk_eq_mk', IsFractionRing.mk'_eq_div]
    rw [map_div₀, Mumford.AmbientSemilinearAut.fracMap_algebraMap, Mumford.AmbientSemilinearAut.fracMap_algebraMap]
  have hwn : w ^ n = g⁻¹ := by rw [hg, zpow_neg, inv_inv]
  rw [hfrac, hwn]
  refine KcEvalRiderKitGal.frac_eq ϖ hrk (KcEvalRiderKitGal.locCompact hdvr hπ hres hF hrk hval)
    (KcEvalRiderKitGal.small ϖ hval) hex ρ a₁ b₁ (σs.map a₂) (σs.map b₂) hb₁ hb₂' g
    (fun k => {z : ↥(Omega.affinoid ϖ k) | ∃ x : AdicPoint K₀ π R, (z : C) = x.toOmega C ∧
          ∃ q : Spec (CommRingCat.of C) ⟶ Limits.pullback f sC,
            q ≫ Limits.pullback.fst f sC = Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ (Φ x).1 ∧
            q ≫ Limits.pullback.snd f sC = 𝟙 (Spec (CommRingCat.of C)) ∧
            ¬ ((⊤ : (Spec (CommRingCat.of C)).Opens) ≤ q ⁻¹ᵁ (tC ⁻¹ᵁ U))})
    (fun k => hfin (tC ⁻¹ᵁ U) hU' k) (fun k z hz => ?_)
  have hzΩ : (z : C) ∈ Omega.upperHalfPlane K₀ C := Omega.affinoid_subset_upperHalfPlane ϖ k z.2
  obtain ⟨x, -, hx⟩ := AdicPoint.toOmega_surjOn ϖ hF hzΩ

  obtain ⟨y, hypt, hyω⟩ := CerednikDrinfeld.FormalOmega.AdicPoint.exists_pt_eq_map_and_toOmega_eq_of_algEquiv π C τ.symm
    s.toRingEquiv.symm hτ' τn' hτn' (x.act (σ g))
  have hy' : ∀ k' : ℕ, DeligneDatum.map π (τn k') (y.pt k') = (x.act (σ (w ^ (-n)))).pt k' := by
    intro k'
    rw [hypt k', ← hg]
    show (Omega K₀ π).map (τn k') ((Omega K₀ π).map (τn' k') ((x.act (σ g)).pt k')) = (x.act (σ g)).pt k'
    rw [← (Omega K₀ π).map_comp, hcomp, (Omega K₀ π).map_id]
  have hPhi : (Φ x).1 = Spec.map (CommRingCat.ofHom τ.toAlgHom.toRingHom) ≫ (Φ y).1 :=
    CerednikDrinfeld.specPoint_eq_specMap_comp_of_map_pt_eq_act_pt_of_cerednikDrinfeld_quotient 𝒪 hdvr π hπ hcomplete hres hunr K₀
      Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr vdet hvdet G σ Γ hcent hodd Γ' hΓ' ρ hρ hdisc hcocpt 𝒳 f Θ hΘnat
      hΘinv hΘfib hΘuniv hF.complete ψ₀ τ n hψτ τn hτn w hw hw₁ (fun x => (Φ x).1) hΦa x y hy'

  obtain ⟨qx, hqx₁, hqx₂⟩ := KcEvalRiderKitGal.exists_cPoint f sC hsC (Φ x).1 (Φ x).2
  obtain ⟨q', hq'₁, hq'₂⟩ := KcEvalRiderKitGal.exists_cPoint f sC hsC (Φ y).1 (Φ y).2
  have hRC : Spec.map (CommRingCat.ofHom (s.toRingEquiv : C →+* C)) ≫ Spec.map (CommRingCat.ofHom (algebraMap R C)) =
      Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ Spec.map (CommRingCat.ofHom τ.toAlgHom.toRingHom) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    exact (hτ a).symm
  have hQ : qx ≫ tC = Spec.map (CommRingCat.ofHom (s.toRingEquiv : C →+* C)) ≫ q' := by
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, htC₁, hqx₁, hPhi, Category.assoc, hq'₁, ← Category.assoc, ← hRC, Category.assoc]
    · rw [Category.assoc, htC₂, ← Category.assoc, hqx₂, Category.id_comp, Category.assoc, hq'₂, Category.comp_id]
  have hqU : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ qx ⁻¹ᵁ (tC ⁻¹ᵁ U) := by
    by_contra hcon
    exact hz ⟨x, hx.symm, qx, hqx₁, hqx₂, hcon⟩
  have hq'U : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ q' ⁻¹ᵁ U := by
    intro p _
    have h1 := hqU (Set.mem_univ (IsLocalRing.closedPoint C))
    rw [← Scheme.Hom.comp_preimage, hQ, Scheme.Hom.comp_preimage] at h1
    have : p = (Spec.map (CommRingCat.ofHom (s.toRingEquiv : C →+* C))).base (IsLocalRing.closedPoint C) := Subsingleton.elim _ _
    rw [this]; exact h1

  have hz1 : ((⟨(z : C), hzΩ⟩ : ↥(Omega.upperHalfPlane K₀ C)) : C) = x.toOmega C := hx.symm
  have e1 := hv₁ x ⟨(z : C), hzΩ⟩ hz1 qx hqx₁ hqx₂ hqU

  have hζΩ : s.toRingEquiv.symm (Omega.pmoebius K₀ (ρ g) (z : C)) ∈ Omega.upperHalfPlane K₀ C :=
    (s⁻¹).mapsTo_upperHalfPlane (Omega.pmoebius_mem_upperHalfPlane K₀ hzΩ (ρ g))
  have hz2 : ((⟨s.toRingEquiv.symm (Omega.pmoebius K₀ (ρ g) (z : C)), hζΩ⟩ : ↥(Omega.upperHalfPlane K₀ C)) : C) = y.toOmega C := by
    show s.toRingEquiv.symm (Omega.pmoebius K₀ (ρ g) (z : C)) = y.toOmega C
    rw [hyω, AdicPoint.toOmega_act ϖ hF (σ g) x, hρ g, ← hz1]
  have e2 := hv₂ y ⟨s.toRingEquiv.symm (Omega.pmoebius K₀ (ρ g) (z : C)), hζΩ⟩ hz2 q' hq'₁ hq'₂ hq'U

  have hval : (Scheme.ΓSpecIso (CommRingCat.of C)).hom.hom
        (((Spec (CommRingCat.of C)).presheaf.map (homOfLE hqU).op).hom ((qx.app (tC ⁻¹ᵁ U)).hom ((tC.app U).hom sec))) =
      s.toRingEquiv ((Scheme.ΓSpecIso (CommRingCat.of C)).hom.hom
        (((Spec (CommRingCat.of C)).presheaf.map (homOfLE hq'U).op).hom ((q'.app U).hom sec))) := by
    have hsU : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ (qx ≫ tC) ⁻¹ᵁ U := by rw [Scheme.Hom.comp_preimage]; exact hqU
    have step1 : GalEv.ev qx (tC ⁻¹ᵁ U) hqU ((tC.app U).hom sec) = GalEv.ev (qx ≫ tC) U hsU sec := by
      rw [← GalEv.ev_comp qx tC U (tC ⁻¹ᵁ U) le_rfl hqU hsU sec, Scheme.Hom.appLE_eq_app]
    have hsU' : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ (Spec.map (CommRingCat.ofHom (s.toRingEquiv : C →+* C)) ≫ q') ⁻¹ᵁ U := by
      rw [← hQ]; exact hsU
    have step2 : GalEv.ev (qx ≫ tC) U hsU sec = GalEv.ev (Spec.map (CommRingCat.ofHom (s.toRingEquiv : C →+* C)) ≫ q') U hsU' sec := by
      have gen : ∀ (Q : Spec (CommRingCat.of C) ⟶ Limits.pullback f sC) (hQ' : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ Q ⁻¹ᵁ U),
          Q = qx ≫ tC → GalEv.ev Q U hQ' sec = GalEv.ev (qx ≫ tC) U hsU sec := by
        intro Q hQ' e; subst e; rfl
      exact (gen _ hsU' hQ.symm).symm
    have step3 : GalEv.ev (Spec.map (CommRingCat.ofHom (s.toRingEquiv : C →+* C)) ≫ q') U hsU' sec =
        GalEv.ev (Spec.map (CommRingCat.ofHom (s.toRingEquiv : C →+* C))) ⊤ le_top ((q'.appLE U ⊤ hq'U).hom sec) :=
      (GalEv.ev_comp _ q' U ⊤ hq'U le_top hsU' sec).symm
    have step4 := GalEv.ev_specMap (s.toRingEquiv : C →+* C) ((q'.appLE U ⊤ hq'U).hom sec) le_top
    show GalEv.ev qx (tC ⁻¹ᵁ U) hqU ((tC.app U).hom sec) = s.toRingEquiv (GalEv.ev q' U hq'U sec)
    rw [step1, step2, step3, step4]
    rfl
  rw [hval] at e1

  have e2' := congrArg s.toRingEquiv e2
  rw [map_mul] at e2'

  have hb : (show ↥(Omega.holRing ϖ) from σs.map b₂ : ↥(Omega.upperHalfPlane K₀ C) → C)
        (ρ g • (⟨z, Omega.affinoid_subset_upperHalfPlane ϖ k z.2⟩ : ↥(Omega.upperHalfPlane K₀ C))) =
      s.toRingEquiv ((show ↥(Omega.holRing ϖ) from b₂ : ↥(Omega.upperHalfPlane K₀ C) → C)
        ⟨s.toRingEquiv.symm (Omega.pmoebius K₀ (ρ g) (z : C)), hζΩ⟩) := by
    show s.toRingEquiv _ = _
    congr 1
  have ha : (show ↥(Omega.holRing ϖ) from σs.map a₂ : ↥(Omega.upperHalfPlane K₀ C) → C)
        (ρ g • (⟨z, Omega.affinoid_subset_upperHalfPlane ϖ k z.2⟩ : ↥(Omega.upperHalfPlane K₀ C))) =
      s.toRingEquiv ((show ↥(Omega.holRing ϖ) from a₂ : ↥(Omega.upperHalfPlane K₀ C) → C)
        ⟨s.toRingEquiv.symm (Omega.pmoebius K₀ (ρ g) (z : C)), hζΩ⟩) := by
    show s.toRingEquiv _ = _
    congr 1
  rw [hb, ha]
  exact KcEvalRiderKitGal.cross e1 e2'

end S_CerednikDrinfeld_ringHom_functionField_germ_app_eq_zpow_smul_fracMap_of_isometricAut_of_eval_of_cerednikDrinfeld_quotient
end P2MW
export P2MW.S_CerednikDrinfeld_ringHom_functionField_germ_app_eq_zpow_smul_fracMap_of_isometricAut_of_eval_of_cerednikDrinfeld_quotient (solution)
