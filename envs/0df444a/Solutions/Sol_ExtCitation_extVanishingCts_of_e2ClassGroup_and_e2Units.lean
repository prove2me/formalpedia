-- Prove2me | solution 1 for ExtCitation.extVanishingCts_of_e2ClassGroup_and_e2Units
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/9c35a593-f806-57a3-baf9-3d8efc57485a

import Definitions.Def_ExtCitation_AdmissibleExtension_v2
import Definitions.Def_ExtCitation_CyclotomicUnits
import Definitions.Def_ExtCitation_AdmissibleExtension
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_NumberField_exists_lift_mem_inertia_integralClosure
import Theorems.Thm_ValuationSubring_exists_liesOverPrime_mem_inertiaSubgroupIn
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units

section PART_R1B_MASCHKE_aux4

set_option autoImplicit false

namespace ExtCitation
p2m_export "ExtCitation" "ExtVanishingCts card_rootsOfUnity_eq_self cycloExp IsAdmissibleExtension SplitsGlobally Cyclotomic.instIsCycExt"
p2m_open "ExtCitation"

local notation "Qbar" => AlgebraicClosure ℚ
local notation "Gal" => Qbar ≃ₐ[ℚ] Qbar

private theorem w2kum_Normal_Qbar : Normal ℚ Qbar := by
  have h : @Normal ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) := inferInstance
  exact h

private theorem w2kum_IsAlgebraic_Qbar : Algebra.IsAlgebraic ℚ Qbar := by
  have h : @Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) :=
    inferInstance
  exact h

section Conj

variable {p : ℕ} [Fact p.Prime] {ζ : Qbar}

private theorem w2kum_exists_conj (hζ : IsPrimitiveRoot ζ p) {n : ℕ} (hn : n.Coprime p) :
    ∃ c : Gal, c ζ = ζ ^ n := by
  haveI := w2kum_Normal_Qbar
  haveI := w2kum_IsAlgebraic_Qbar
  have hζn : IsPrimitiveRoot (ζ ^ n) p := hζ.pow_of_coprime n hn
  have hminpoly : Polynomial.cyclotomic p ℚ = minpoly ℚ ζ :=
    Polynomial.cyclotomic_eq_minpoly_rat hζ (Fact.out : p.Prime).pos
  have hroot : Polynomial.aeval (ζ ^ n) (minpoly ℚ ζ) = 0 := by
    rw [← hminpoly]
    have h := hζn.isRoot_cyclotomic (Fact.out : p.Prime).pos
    rw [Polynomial.aeval_def, ← Polynomial.eval_map,
      Polynomial.map_cyclotomic p (algebraMap ℚ Qbar)]
    exact h
  have halg : IsAlgebraic ℚ ζ := Algebra.IsAlgebraic.isAlgebraic (R := ℚ) ζ
  exact minpoly.exists_algEquiv_of_root' halg hroot

omit [Fact p.Prime] in

private theorem w2kum_pow_mod (hζ : IsPrimitiveRoot ζ p) (a : ℕ) : ζ ^ (a % p) = ζ ^ a := by
  conv_rhs => rw [← Nat.mod_add_div a p]
  rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]

end Conj

section Maschke

variable (p : ℕ) [Fact p.Prime]
variable {V : Type} [AddCommGroup V] [Module (ZMod p) V]
  [DistribMulAction Gal V] [SMulCommClass Gal (ZMod p) V]
variable {ζ : Qbar}

private noncomputable def w2kumRho (σ : Gal) : V →ₗ[ZMod p] V :=
  DistribSMul.toLinearMap (ZMod p) V σ

@[scoped simp] private theorem w2kumRho_apply (σ : Gal) (x : V) : w2kumRho p σ x = σ • x := rfl

variable {p}

private theorem w2kum_smul_eq_of_apply_eq
    (htriv : ∀ σ : Gal, σ ζ = ζ → ∀ x : V, σ • x = x)
    {g h : Gal} (hgh : g ζ = h ζ) (x : V) : g • x = h • x := by
  have hfix : (h⁻¹ * g) ζ = ζ := by
    rw [AlgEquiv.mul_apply, hgh, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  have h1 := htriv _ hfix x
  rw [mul_smul] at h1
  calc g • x = h • h⁻¹ • g • x := (smul_inv_smul h _).symm
    _ = h • x := by rw [h1]

private theorem w2kum_inv_smul_eq_of_smul_eq {g h : Gal}
    (hgh : ∀ y : V, g • y = h • y) (x : V) : g⁻¹ • x = h⁻¹ • x := by
  have h1 : x = h • g⁻¹ • x := by rw [← hgh (g⁻¹ • x), smul_inv_smul]
  calc g⁻¹ • x = h⁻¹ • h • g⁻¹ • x := (inv_smul_smul h _).symm
    _ = h⁻¹ • x := by rw [← h1]

private theorem w2kum_splitsGlobally_of_forall_fix {p : ℕ} [Fact p.Prime]
    {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    [DistribMulAction Gal V] [SMulCommClass Gal (ZMod p) V]
    {ζ : Qbar} (hζ : IsPrimitiveRoot ζ p)
    (C : Submodule (ZMod p) V)
    (hsub : ∀ σ : Gal, ∀ x ∈ C, σ • x = x)
    (htriv : ∀ σ : Gal, σ ζ = ζ → ∀ x : V, σ • x = x) :
    SplitsGlobally C := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

  have hconj : ∀ d : (ZMod p)ˣ, ∃ c : Gal, c ζ = ζ ^ ((d : ZMod p)).val :=
    fun d => w2kum_exists_conj hζ (ZMod.val_coe_unit_coprime d)
  choose σ hσ using hconj

  have hcomp : ∀ (e d : (ZMod p)ˣ) (y : V), (σ e * σ d) • y = σ (e * d) • y := by
    intro e d y
    refine w2kum_smul_eq_of_apply_eq htriv ?_ y
    have hL : (σ e * σ d) ζ = ζ ^ ((e : ZMod p).val * (d : ZMod p).val) := by
      rw [AlgEquiv.mul_apply, hσ d, map_pow, hσ e, ← pow_mul]
    have hR : σ (e * d) ζ = ζ ^ ((e : ZMod p).val * (d : ZMod p).val) := by
      rw [hσ (e * d),
        show ((↑(e * d) : ZMod p)).val = (e : ZMod p).val * (d : ZMod p).val % p by
          rw [Units.val_mul, ZMod.val_mul]]
      exact w2kum_pow_mod hζ _
    rw [hL, hR]

  have hspec : ∀ τ : Gal, τ ζ = ζ ^ cycloExp p τ := fun τ =>
    modularCyclotomicCharacter.spec Qbar (card_rootsOfUnity_eq_self p)
      (τ : Qbar ≃+* Qbar) hζ.toRootsOfUnity.2
  have hτmatch : ∀ τ : Gal, ∃ e : (ZMod p)ˣ, ∀ x : V, τ • x = σ e • x := by
    intro τ
    refine ⟨modularCyclotomicCharacter Qbar (card_rootsOfUnity_eq_self p)
      (τ : Qbar ≃+* Qbar), fun x => ?_⟩
    refine w2kum_smul_eq_of_apply_eq htriv ?_ x
    rw [hσ]
    exact hspec τ

  obtain ⟨D, hCD⟩ := C.exists_isCompl
  set π₀ : V →ₗ[ZMod p] V := C.projection D hCD with hπ₀def

  set T : V →ₗ[ZMod p] V :=
    -(∑ d : (ZMod p)ˣ, (w2kumRho p (σ d)) ∘ₗ π₀ ∘ₗ (w2kumRho p ((σ d)⁻¹))) with hTdef
  have hTapp : ∀ x : V, T x = -(∑ d : (ZMod p)ˣ, σ d • π₀ ((σ d)⁻¹ • x)) := by
    intro x
    rw [hTdef]
    simp only [LinearMap.neg_apply, LinearMap.sum_apply, LinearMap.comp_apply, w2kumRho_apply]

  have hTmem : ∀ x : V, T x ∈ C := by
    intro x
    rw [hTapp]
    refine C.neg_mem (Submodule.sum_mem _ fun d _ => ?_)
    have hmem : π₀ ((σ d)⁻¹ • x) ∈ C := Submodule.projection_apply_mem hCD _
    rw [hsub (σ d) _ hmem]
    exact hmem

  have hTid : ∀ x ∈ C, T x = x := by
    intro x hx
    rw [hTapp]
    have hterm : ∀ d : (ZMod p)ˣ, σ d • π₀ ((σ d)⁻¹ • x) = x := by
      intro d
      rw [hsub ((σ d)⁻¹) x hx]
      have hproj : π₀ x = x := Submodule.projection_apply_left hCD ⟨x, hx⟩
      rw [hproj, hsub (σ d) x hx]
    rw [Finset.sum_congr rfl fun d _ => hterm d, Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul (ZMod p)]
    have hcard : ((Fintype.card (ZMod p)ˣ : ℕ) : ZMod p) = -1 := by
      rw [Fintype.card_units, ZMod.card]
      rw [Nat.cast_sub (Fact.out : p.Prime).one_lt.le, Nat.cast_one, ZMod.natCast_self, zero_sub]
    rw [hcard, neg_smul, one_smul, neg_neg]

  have hTequi : ∀ (e : (ZMod p)ˣ) (x : V), σ e • T x = T (σ e • x) := by
    intro e x
    rw [hTapp, hTapp, smul_neg]
    congr 1
    rw [Finset.smul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft e) _ _ ?_
    intro d
    simp only [Equiv.coe_mulLeft]
    have harg : (σ (e * d))⁻¹ • (σ e • x) = (σ d)⁻¹ • x := by
      rw [w2kum_inv_smul_eq_of_smul_eq (fun y => (hcomp e d y).symm) (σ e • x),
        mul_inv_rev, mul_smul, inv_smul_smul]
    rw [harg, ← mul_smul, hcomp e d]

  have hTequiv_all : ∀ (τ : Gal) (x : V), τ • T x = T (τ • x) := by
    intro τ x
    obtain ⟨e, he⟩ := hτmatch τ
    rw [he (T x), he x, hTequi e]

  refine ⟨LinearMap.ker T, fun τ x hx => ?_, ?_⟩
  · rw [LinearMap.mem_ker] at hx ⊢
    rw [← hTequiv_all τ x, hx, smul_zero]
  · refine IsCompl.of_eq ?_ ?_
    · rw [Submodule.eq_bot_iff]
      intro x hx
      obtain ⟨hxC, hxK⟩ := Submodule.mem_inf.mp hx
      rw [LinearMap.mem_ker] at hxK
      rw [← hTid x hxC, hxK]
    · rw [Submodule.eq_top_iff']
      intro x
      rw [Submodule.mem_sup]
      refine ⟨T x, hTmem x, x - T x, ?_, by abel⟩
      rw [LinearMap.mem_ker, map_sub, hTid _ (hTmem x), sub_self]

end Maschke

end ExtCitation
p2m_reactivate "P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation"

end PART_R1B_MASCHKE_aux4
p2m_reactivate "P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation"

section PART_R1A_MAIN_aux4

set_option autoImplicit false

namespace ExtCitation
p2m_export "ExtCitation" "ExtVanishingCts card_rootsOfUnity_eq_self cycloExp IsAdmissibleExtension SplitsGlobally Cyclotomic.instIsCycExt"
p2m_open "ExtCitation"

local notation "Qbar" => AlgebraicClosure ℚ
local notation "Gal" => Qbar ≃ₐ[ℚ] Qbar

section CycloExp

variable {p : ℕ} [Fact p.Prime]

private theorem w2kum_apply_eq_pow_cycloExp {ζ : Qbar} (hζ : IsPrimitiveRoot ζ p) (σ : Gal) :
    σ ζ = ζ ^ cycloExp p σ :=
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  modularCyclotomicCharacter.spec Qbar (card_rootsOfUnity_eq_self p) (σ : Qbar ≃+* Qbar)
    hζ.toRootsOfUnity.2

private theorem w2kum_cycloExp_lt (σ : Gal) : cycloExp p σ < p :=
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  ZMod.val_lt _

private theorem w2kum_cycloExp_eq_one_of_fix {ζ : Qbar} (hζ : IsPrimitiveRoot ζ p) {σ : Gal}
    (hσ : σ ζ = ζ) : cycloExp p σ = 1 :=
  hζ.pow_inj (w2kum_cycloExp_lt σ) (Fact.out : p.Prime).one_lt
    (by rw [← w2kum_apply_eq_pow_cycloExp hζ σ, pow_one, hσ])

private theorem w2kum_fix_of_cycloExp_coe_eq_one {ζ : Qbar} (hζ : IsPrimitiveRoot ζ p) {σ : Gal}
    (hω : ((cycloExp p σ : ℕ) : ZMod p) = 1) : σ ζ = ζ := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hlt : cycloExp p σ < p := ZMod.val_lt _
  have hexp : cycloExp p σ = 1 := by
    have hv := congrArg ZMod.val hω
    rwa [ZMod.val_natCast_of_lt hlt, ZMod.val_one p] at hv
  rw [w2kum_apply_eq_pow_cycloExp hζ σ, hexp, pow_one]

end CycloExp
p2m_reactivate "P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation"

section Vside

variable {p : ℕ} [Fact p.Prime]
variable {V : Type} [AddCommGroup V] [Module (ZMod p) V]
  [DistribMulAction Gal V] [SMulCommClass Gal (ZMod p) V]
variable {C : Submodule (ZMod p) V}

omit [SMulCommClass Gal (ZMod p) V] in

private theorem w2kum_smul_sub_mem (hadm : IsAdmissibleExtension p V C)
    {ζ : Qbar} (hζ : IsPrimitiveRoot ζ p) {σ : Gal} (hσ : σ ζ = ζ) (x : V) :
    σ • x - x ∈ C := by
  have h := hadm.cyclo_quot σ x
  rwa [w2kum_cycloExp_eq_one_of_fix hζ hσ, Nat.cast_one, one_smul] at h

omit [SMulCommClass Gal (ZMod p) V] in

private theorem w2kum_phi_mul (hadm : IsAdmissibleExtension p V C) {ζ : Qbar}
    (hζ : IsPrimitiveRoot ζ p) {σ τ : Gal} (_hσ : σ ζ = ζ) (hτ : τ ζ = ζ) (x₀ : V) :
    (σ * τ) • x₀ - x₀ = (σ • x₀ - x₀) + (τ • x₀ - x₀) := by
  have hτmem : τ • x₀ - x₀ ∈ C := w2kum_smul_sub_mem hadm hζ hτ x₀
  have hfix : σ • (τ • x₀ - x₀) = τ • x₀ - x₀ := hadm.fixed_sub σ _ hτmem
  have hexp : σ • τ • x₀ - σ • x₀ = τ • x₀ - x₀ := by rw [← smul_sub, hfix]
  calc (σ * τ) • x₀ - x₀ = (σ • τ • x₀ - σ • x₀) + (σ • x₀ - x₀) := by rw [mul_smul]; abel
    _ = (τ • x₀ - x₀) + (σ • x₀ - x₀) := by rw [hexp]
    _ = (σ • x₀ - x₀) + (τ • x₀ - x₀) := by abel

omit [SMulCommClass Gal (ZMod p) V] in

private theorem w2kum_finite (hadm : IsAdmissibleExtension p V C) : Finite V :=
  Nat.finite_of_card_ne_zero (hadm.card_total ▸ pow_ne_zero 2 (Fact.out : p.Prime).ne_zero)

omit [SMulCommClass Gal (ZMod p) V] in

private theorem w2kum_exists_notMem (hadm : IsAdmissibleExtension p V C) : ∃ x₀ : V, x₀ ∉ C := by
  by_contra h
  push Not at h
  have htop : C = ⊤ := Submodule.eq_top_iff'.mpr h
  have hcard := hadm.card_sub
  rw [htop] at hcard
  have hVcard : Nat.card (⊤ : Submodule (ZMod p) V) = Nat.card V :=
    Nat.card_congr Submodule.topEquiv.toEquiv
  rw [hVcard, hadm.card_total] at hcard
  have h2 := (Fact.out : p.Prime).two_le
  nlinarith [hcard]

omit [SMulCommClass Gal (ZMod p) V] in

private theorem w2kum_compl (hadm : IsAdmissibleExtension p V C) {x₀ : V} (hx₀ : x₀ ∉ C) :
    IsCompl C (Submodule.span (ZMod p) {x₀}) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI hfinV : Finite V := w2kum_finite hadm
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have hx₀ne : x₀ ≠ 0 := fun h => hx₀ (h ▸ C.zero_mem)
  have hdisj : Disjoint C (Submodule.span (ZMod p) {x₀}) := by
    rw [Submodule.disjoint_def]
    intro x hxC hxS
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hxS
    rcases eq_or_ne a 0 with rfl | ha
    · rw [zero_smul]
    · exact absurd (C.smul_mem a⁻¹ hxC) (by rwa [inv_smul_smul₀ ha])
  have hcardV : Nat.card V = p ^ 2 := hadm.card_total
  have hcardC : Nat.card C = p := hadm.card_sub
  have hpow := Module.natCard_eq_pow_finrank (K := ZMod p) (V := V)
  have hpowC := Module.natCard_eq_pow_finrank (K := ZMod p) (V := C)
  rw [Nat.card_zmod] at hpow hpowC
  have hfV : Module.finrank (ZMod p) V = 2 := by
    have h2 : p ^ Module.finrank (ZMod p) V = p ^ 2 := by rw [← hpow, hcardV]
    exact Nat.pow_right_injective (Fact.out : p.Prime).two_le h2
  have hfC : Module.finrank (ZMod p) C = 1 := by
    have h1 : p ^ Module.finrank (ZMod p) C = p ^ 1 := by rw [← hpowC, hcardC, pow_one]
    exact Nat.pow_right_injective (Fact.out : p.Prime).two_le h1
  have hfS : Module.finrank (ZMod p) (Submodule.span (ZMod p) {x₀}) = 1 :=
    finrank_span_singleton hx₀ne
  refine ⟨hdisj, ?_⟩
  rw [codisjoint_iff]
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq C (Submodule.span (ZMod p) {x₀})
  rw [hdisj.eq_bot, finrank_bot, add_zero, hfC, hfS] at hsum
  exact Submodule.eq_top_of_finrank_eq (by rw [hsum, hfV])

private theorem w2kum_triv_of_phi_eq_zero (hadm : IsAdmissibleExtension p V C)
    {σ : Gal} {x₀ : V} (hx₀ : x₀ ∉ C)
    (hphi : σ • x₀ = x₀) (x : V) : σ • x = x := by
  have hsup : C ⊔ Submodule.span (ZMod p) {x₀} = ⊤ :=
    codisjoint_iff.mp (w2kum_compl hadm hx₀).codisjoint
  have hx : x ∈ C ⊔ Submodule.span (ZMod p) {x₀} := hsup ▸ Submodule.mem_top
  obtain ⟨c, hc, s, hs, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hs
  rw [smul_add, hadm.fixed_sub σ c hc, smul_comm, hphi]

private def w2kumStabV (p : ℕ) [Fact p.Prime] (V : Type) [AddCommGroup V] [Module (ZMod p) V]
    [DistribMulAction Gal V] [SMulCommClass Gal (ZMod p) V] : Subgroup Gal where
  carrier := {σ : Gal | ∀ v : V, σ • v = v}
  one_mem' := fun v => one_smul _ v
  mul_mem' := fun {a b} ha hb v => by rw [mul_smul, hb v, ha v]
  inv_mem' := fun {a} ha v => by
    conv_lhs => rw [← ha v]
    rw [inv_smul_smul]

private theorem w2kumStabV_isOpen (hopen : IsOpen {σ : Gal | ∀ v : V, σ • v = v}) :
    IsOpen ((w2kumStabV p V : Subgroup Gal) : Set Gal) := hopen

private theorem w2kumStabV_normal : (w2kumStabV p V).Normal := by
  refine ⟨fun n hn g v => ?_⟩
  rw [mul_smul, mul_smul, hn (g⁻¹ • v), smul_inv_smul]

private theorem w2kum_phi_conj (hadm : IsAdmissibleExtension p V C) {ζ : Qbar}
    (hζ : IsPrimitiveRoot ζ p) {σ : Gal} (hσ : σ ζ = ζ) (τ : Gal) (x₀ : V) :
    (τ * σ * τ⁻¹) • x₀ - x₀ =
      ((cycloExp p τ⁻¹ : ℕ) : ZMod p) • (σ • x₀ - x₀) := by
  have hy : τ⁻¹ • x₀ - ((cycloExp p τ⁻¹ : ℕ) : ZMod p) • x₀ ∈ C := hadm.cyclo_quot τ⁻¹ x₀
  set c₁ : V := τ⁻¹ • x₀ - ((cycloExp p τ⁻¹ : ℕ) : ZMod p) • x₀ with hc₁def
  have hydecomp : τ⁻¹ • x₀ = ((cycloExp p τ⁻¹ : ℕ) : ZMod p) • x₀ + c₁ := by
    rw [hc₁def]; abel
  have hφmem : σ • x₀ - x₀ ∈ C := w2kum_smul_sub_mem hadm hζ hσ x₀
  have hstep : σ • (τ⁻¹ • x₀) - τ⁻¹ • x₀ =
      ((cycloExp p τ⁻¹ : ℕ) : ZMod p) • (σ • x₀ - x₀) := by
    rw [hydecomp, smul_add, smul_comm, hadm.fixed_sub σ c₁ hy, smul_sub]
    abel
  calc (τ * σ * τ⁻¹) • x₀ - x₀
      = τ • (σ • (τ⁻¹ • x₀)) - τ • (τ⁻¹ • x₀) := by
        rw [mul_smul, mul_smul, smul_inv_smul]
    _ = τ • (σ • (τ⁻¹ • x₀) - τ⁻¹ • x₀) := by rw [smul_sub]
    _ = τ • (((cycloExp p τ⁻¹ : ℕ) : ZMod p) • (σ • x₀ - x₀)) := by rw [hstep]
    _ = ((cycloExp p τ⁻¹ : ℕ) : ZMod p) • (τ • (σ • x₀ - x₀)) := smul_comm _ _ _
    _ = ((cycloExp p τ⁻¹ : ℕ) : ZMod p) • (σ • x₀ - x₀) := by
        rw [hadm.fixed_sub τ _ hφmem]

end Vside
p2m_reactivate "P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation"

section Emb

variable (p : ℕ) [Fact p.Prime]

private noncomputable def w2kumEmb : CyclotomicField p ℚ →ₐ[ℚ] Qbar :=
  haveI : Algebra.IsAlgebraic ℚ (CyclotomicField p ℚ) := Algebra.IsAlgebraic.of_finite ℚ _
  IsAlgClosed.lift

private noncomputable def w2kumZeta : Qbar :=
  w2kumEmb p (IsCyclotomicExtension.zeta p ℚ (CyclotomicField p ℚ))

private theorem w2kumZeta_spec : IsPrimitiveRoot (w2kumZeta p) p :=
  (IsCyclotomicExtension.zeta_spec p ℚ (CyclotomicField p ℚ)).map_of_injective
    (w2kumEmb p).injective

end Emb
p2m_reactivate "P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation"

section Lfield

variable {p : ℕ} [Fact p.Prime]
variable {V : Type} [AddCommGroup V] [Module (ZMod p) V]
  [DistribMulAction Gal V] [SMulCommClass Gal (ZMod p) V]

omit [SMulCommClass Gal (ZMod p) V] in

private theorem w2kum_stabV_fixes_zeta {C : Submodule (ZMod p) V} (hadm : IsAdmissibleExtension p V C)
    {ζ : Qbar} (hζ : IsPrimitiveRoot ζ p) {σ : Gal} (hσ : ∀ v : V, σ • v = v) :
    σ ζ = ζ := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨x₀, hx₀⟩ := w2kum_exists_notMem hadm
  have hquot := hadm.cyclo_quot σ x₀
  rw [hσ x₀] at hquot
  have h1 : (1 - (cycloExp p σ : ZMod p)) • x₀ ∈ C := by
    rw [sub_smul, one_smul]; exact hquot
  have hω : ((cycloExp p σ : ℕ) : ZMod p) = 1 := by
    by_contra hne
    have hinv : (1 - ((cycloExp p σ : ℕ) : ZMod p)) ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    have h2 := C.smul_mem (1 - ((cycloExp p σ : ℕ) : ZMod p))⁻¹ h1
    rw [smul_smul, inv_mul_cancel₀ hinv, one_smul] at h2
    exact hx₀ h2
  have hlt : cycloExp p σ < p := ZMod.val_lt _
  have hexp : cycloExp p σ = 1 := by
    have hv := congrArg ZMod.val hω
    rwa [ZMod.val_natCast_of_lt hlt, ZMod.val_one p] at hv
  rw [w2kum_apply_eq_pow_cycloExp hζ σ, hexp, pow_one]

private theorem w2kum_isGalois_Qbar : IsGalois ℚ Qbar := by
  have h : @IsGalois ℚ _ (AlgebraicClosure ℚ) _ (AlgebraicClosure.instAlgebra ℚ) := inferInstance
  exact h

variable (p V) in

private noncomputable def w2kumL : IntermediateField ℚ Qbar :=
  IntermediateField.fixedField (w2kumStabV p V)

variable (p V) in
private theorem w2kum_fixingSubgroup_L
    (hopen : IsOpen ((w2kumStabV p V : Subgroup Gal) : Set Gal)) :
    (w2kumL p V).fixingSubgroup = w2kumStabV p V := by
  haveI := w2kum_isGalois_Qbar
  exact InfiniteGalois.fixingSubgroup_fixedField
    ⟨w2kumStabV p V, Subgroup.isClosed_of_isOpen _ hopen⟩

variable (p V) in
private theorem w2kum_L_finiteDimensional
    (hopen : IsOpen ((w2kumStabV p V : Subgroup Gal) : Set Gal)) :
    FiniteDimensional ℚ (w2kumL p V) := by
  haveI := w2kum_isGalois_Qbar
  rw [← InfiniteGalois.isOpen_iff_finite]
  rw [w2kum_fixingSubgroup_L p V hopen]
  exact hopen

variable (p V) in

private theorem w2kum_L_map_le (σ : Gal) :
    (w2kumL p V).map (↑σ : Qbar →ₐ[ℚ] Qbar) ≤ w2kumL p V := by
  intro x hx
  rw [IntermediateField.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [w2kumL, IntermediateField.mem_fixedField_iff] at hy ⊢
  intro τ hτ
  have hτ' : σ⁻¹ * τ * σ ∈ w2kumStabV p V := fun v => by
    rw [mul_smul, mul_smul, hτ (σ • v), inv_smul_smul]
  have hy'' : (σ⁻¹ * τ * σ) • y = y := hy _ hτ'
  have hgoal : τ • (σ • y) = σ • y := by
    calc τ • (σ • y) = σ • ((σ⁻¹ * τ * σ) • y) := by
          rw [mul_smul, mul_smul, smul_inv_smul]
      _ = σ • y := by rw [hy'']
  exact hgoal

private theorem w2kum_zeta_mem {C : Submodule (ZMod p) V} (hadm : IsAdmissibleExtension p V C) :
    w2kumZeta p ∈ w2kumL p V := by
  rw [w2kumL, IntermediateField.mem_fixedField_iff]
  intro τ hτ
  exact w2kum_stabV_fixes_zeta hadm (w2kumZeta_spec p) hτ

private theorem w2kum_emb_mem {C : Submodule (ZMod p) V} (hadm : IsAdmissibleExtension p V C)
    (x : CyclotomicField p ℚ) : w2kumEmb p x ∈ w2kumL p V := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hx : x ∈ Algebra.adjoin ℚ
      {b : CyclotomicField p ℚ | ∃ n : ℕ, n ∈ ({p} : Set ℕ) ∧ n ≠ 0 ∧ b ^ n = 1} :=
    IsCyclotomicExtension.adjoin_roots x
  have hmem : ∀ b : CyclotomicField p ℚ,
      (∃ n : ℕ, n ∈ ({p} : Set ℕ) ∧ n ≠ 0 ∧ b ^ n = 1) → w2kumEmb p b ∈ w2kumL p V := by
    rintro b ⟨n, hn, -, hbn⟩
    rw [Set.mem_singleton_iff] at hn
    rw [hn] at hbn
    have hpow : w2kumEmb p b ^ p = 1 := by rw [← map_pow, hbn, map_one]
    obtain ⟨i, -, hi⟩ := (w2kumZeta_spec p).eq_pow_of_pow_eq_one hpow
    exact hi ▸ pow_mem (w2kum_zeta_mem hadm) i
  exact Algebra.adjoin_induction
    (fun b hb => hmem b hb)
    (fun r => by
      rw [AlgHom.commutes]
      exact (w2kumL p V).algebraMap_mem r)
    (fun a b _ _ iha ihb => by rw [map_add]; exact (w2kumL p V).add_mem iha ihb)
    (fun a b _ _ iha ihb => by rw [map_mul]; exact (w2kumL p V).mul_mem iha ihb)
    hx

private noncomputable def w2kumIota {C : Submodule (ZMod p) V} (hadm : IsAdmissibleExtension p V C) :
    CyclotomicField p ℚ →ₐ[ℚ] (w2kumL p V) :=
  AlgHom.codRestrict (w2kumEmb p) (w2kumL p V).toSubalgebra (w2kum_emb_mem hadm)

@[scoped simp] private theorem w2kumIota_apply {C : Submodule (ZMod p) V}
    (hadm : IsAdmissibleExtension p V C) (x : CyclotomicField p ℚ) :
    (w2kumIota hadm x : Qbar) = w2kumEmb p x := rfl

end Lfield
p2m_reactivate "P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation"

section Inertia

variable {p : ℕ} [Fact p.Prime]
variable {V : Type} [AddCommGroup V] [Module (ZMod p) V]
  [DistribMulAction Gal V] [SMulCommClass Gal (ZMod p) V]
variable {C : Submodule (ZMod p) V}

open ValuationSubring in

private theorem w2kum_inertia_le_stabV (hadm : IsAdmissibleExtension p V C)
    (q : ℕ) (hq : q.Prime) (A : ValuationSubring Qbar) (hA : A.LiesOverPrime q) :
    A.inertiaSubgroupIn ℚ ⊓ MulAction.stabilizer Gal (w2kumZeta p) ≤ w2kumStabV p V := by
  rintro σ ⟨hσI, hσζ⟩
  show ∀ v : V, σ • v = v
  by_cases hqp : q = p
  · obtain ⟨C', hC'stab, hcompl⟩ := hadm.locally_split A (hqp ▸ hA)
    have hσζ' : σ (w2kumZeta p) = w2kumZeta p := MulAction.mem_stabilizer_iff.mp hσζ
    have hσD : σ ∈ A.decompositionSubgroup ℚ := by
      obtain ⟨τ, -, rfl⟩ := Subgroup.mem_map.mp hσI
      exact τ.2
    intro v
    have hv : v ∈ C ⊔ C' := by
      rw [codisjoint_iff.mp hcompl.codisjoint]
      exact Submodule.mem_top
    obtain ⟨c, hc, c', hc', rfl⟩ := Submodule.mem_sup.mp hv
    have h1 : σ • c' ∈ C' := hC'stab σ hσD c' hc'
    have h2 : σ • c' - c' ∈ C := by
      have hq2 := hadm.cyclo_quot σ c'
      rwa [w2kum_cycloExp_eq_one_of_fix (w2kumZeta_spec p) hσζ', Nat.cast_one, one_smul] at hq2
    have h3 : σ • c' - c' ∈ C ⊓ C' := ⟨h2, C'.sub_mem h1 hc'⟩
    rw [disjoint_iff.mp hcompl.disjoint, Submodule.mem_bot] at h3
    have h4 : σ • c' = c' := sub_eq_zero.mp h3
    rw [smul_add, hadm.fixed_sub σ c hc, h4]
  · exact fun v => hadm.unramified_outside q hq hqp A hA σ hσI v

end Inertia
p2m_reactivate "P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation"

section CardH

variable {p : ℕ} [Fact p.Prime]
variable {V : Type} [AddCommGroup V] [Module (ZMod p) V]
  [DistribMulAction Gal V] [SMulCommClass Gal (ZMod p) V]
variable {C : Submodule (ZMod p) V}

private noncomputable def w2kumZetaL (hadm : IsAdmissibleExtension p V C) : w2kumL p V :=
  ⟨w2kumZeta p, w2kum_zeta_mem hadm⟩

private noncomputable def w2kumH (hadm : IsAdmissibleExtension p V C) :
    Subgroup ((w2kumL p V) ≃ₐ[ℚ] (w2kumL p V)) :=
  MulAction.stabilizer _ (w2kumZetaL hadm)

private theorem w2kum_card_H (hadm : IsAdmissibleExtension p V C)
    (hopen : IsOpen ((w2kumStabV p V : Subgroup Gal) : Set Gal))
    {σ₀ : Gal} {x₀ : V}
    (hσ₀ζ : σ₀ (w2kumZeta p) = w2kumZeta p) (hσ₀ : σ₀ • x₀ ≠ x₀) :
    Nat.card (w2kumH hadm) = p := by
  classical
  haveI := w2kum_isGalois_Qbar

  haveI hQbarNormal : Normal ℚ Qbar := by
    have h2 : @Normal ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) :=
      inferInstance
    exact h2

  haveI hLnormal' : @Normal ℚ ↥(w2kumL p V) _ _ (IntermediateField.algebra' (w2kumL p V)) :=
    (IntermediateField.normal_iff_forall_map_le'
      (K := w2kumL p V) (L := Qbar)).mpr (fun σ => w2kum_L_map_le p V σ)
  haveI hLnormal : Normal ℚ ↥(w2kumL p V) := by
    have e : (IntermediateField.algebra' (w2kumL p V) : Algebra ℚ ↥(w2kumL p V)) =
        (inferInstance : Algebra ℚ ↥(w2kumL p V)) := Subsingleton.elim _ _
    exact cast (congrArg (@Normal ℚ ↥(w2kumL p V) _ _) e) hLnormal'
  haveI : FiniteDimensional ℚ (w2kumL p V) := w2kum_L_finiteDimensional p V hopen
  set res := AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Qbar) (w2kumL p V) with hresdef
  have hsurj : Function.Surjective res := by
    rw [hresdef]
    exact AlgEquiv.restrictNormalHom_surjective _
  have hker : ∀ σ : Gal, res σ = 1 ↔ σ ∈ w2kumStabV p V := by
    intro σ
    rw [← w2kum_fixingSubgroup_L p V hopen,
      ← IntermediateField.restrictNormalHom_ker (w2kumL p V), MonoidHom.mem_ker, hresdef]
    exact ⟨fun h => h, fun h => h⟩
  set lift : ((w2kumL p V) ≃ₐ[ℚ] (w2kumL p V)) → Gal := Function.surjInv hsurj with hliftdef
  have hlift : ∀ τ, res (lift τ) = τ := Function.surjInv_eq hsurj

  have hindep : ∀ {σ σ' : Gal}, res σ = res σ' → ∀ v : V, σ • v = σ' • v := by
    intro σ σ' h v
    have hmem : σ'⁻¹ * σ ∈ w2kumStabV p V := by
      rw [← hker]
      rw [map_mul, map_inv, h, inv_mul_cancel]
    have h1 : (σ'⁻¹ * σ) • v = v := hmem v
    rw [mul_smul] at h1
    calc σ • v = σ' • σ'⁻¹ • σ • v := (smul_inv_smul σ' _).symm
      _ = σ' • v := by rw [h1]

  have hliftζ : ∀ τ : (w2kumL p V) ≃ₐ[ℚ] (w2kumL p V), τ ∈ w2kumH hadm →
      lift τ (w2kumZeta p) = w2kumZeta p := by
    intro τ hτ
    have hcomm : ((res (lift τ)) (w2kumZetaL hadm) : Qbar) = lift τ (w2kumZeta p) :=
      AlgEquiv.restrictNormal_commutes (lift τ) (w2kumL p V) (w2kumZetaL hadm)
    rw [hlift τ] at hcomm
    have hτζ : τ (w2kumZetaL hadm) = w2kumZetaL hadm := MulAction.mem_stabilizer_iff.mp hτ
    rw [← hcomm, hτζ]
    rfl

  have hφmem : ∀ τ : (w2kumL p V) ≃ₐ[ℚ] (w2kumL p V), τ ∈ w2kumH hadm →
      lift τ • x₀ - x₀ ∈ C := fun τ hτ =>
    w2kum_smul_sub_mem hadm (w2kumZeta_spec p) (hliftζ τ hτ) x₀
  set Φ : (w2kumH hadm) → Multiplicative C :=
    fun τ => Multiplicative.ofAdd (⟨lift ↑τ • x₀ - x₀, hφmem ↑τ τ.2⟩ : C) with hΦdef
  have hΦmul : ∀ τ₁ τ₂ : w2kumH hadm, Φ (τ₁ * τ₂) = Φ τ₁ * Φ τ₂ := by
    intro τ₁ τ₂
    have hres : res (lift ↑(τ₁ * τ₂)) = res (lift ↑τ₁ * lift ↑τ₂) := by
      rw [hlift, map_mul, hlift, hlift]; rfl
    have hval : lift ↑(τ₁ * τ₂) • x₀ - x₀ =
        (lift ↑τ₁ • x₀ - x₀) + (lift ↑τ₂ • x₀ - x₀) := by
      rw [hindep hres x₀]
      exact w2kum_phi_mul hadm (w2kumZeta_spec p)
        (hliftζ ↑τ₁ τ₁.2) (hliftζ ↑τ₂ τ₂.2) x₀
    simp only [hΦdef]
    rw [← ofAdd_add]
    congr 1
    exact Subtype.ext hval
  set ΦM : (w2kumH hadm) →* Multiplicative C :=
    { toFun := Φ
      map_one' := by
        simp only [hΦdef]
        have h1 : res (lift ↑(1 : w2kumH hadm)) = res 1 := by
          rw [hlift, Subgroup.coe_one, map_one]
        have h0 : lift ↑(1 : w2kumH hadm) • x₀ - x₀ = 0 := by
          rw [hindep h1 x₀, one_smul, sub_self]
        rw [show (⟨lift ↑(1 : w2kumH hadm) • x₀ - x₀, hφmem _ (1 : w2kumH hadm).2⟩ : C)
          = 0 from Subtype.ext h0]
        rfl
      map_mul' := hΦmul } with hΦMdef
  have hinj : Function.Injective ΦM := by
    rw [injective_iff_map_eq_one]
    intro τ hτ1
    have hval : lift ↑τ • x₀ - x₀ = 0 := by
      have h2 := congrArg (fun z => (Multiplicative.toAdd z : C).val) hτ1
      exact h2
    have hfix : lift ↑τ • x₀ = x₀ := by rwa [sub_eq_zero] at hval
    have hx₀C : x₀ ∉ C := by
      intro hmem
      exact hσ₀ (hadm.fixed_sub σ₀ x₀ hmem)
    have hstab : lift ↑τ ∈ w2kumStabV p V :=
      fun v => w2kum_triv_of_phi_eq_zero hadm hx₀C hfix v
    have hres1 : res (lift ↑τ) = 1 := (hker _).mpr hstab
    rw [hlift] at hres1
    exact Subtype.ext hres1
  have hnontriv : ΦM.range ≠ ⊥ := by
    intro hbot
    have hσ₀H : res σ₀ ∈ w2kumH hadm := by
      rw [w2kumH, MulAction.mem_stabilizer_iff]
      have hcomm : ((res σ₀) (w2kumZetaL hadm) : Qbar) = σ₀ (w2kumZeta p) :=
        AlgEquiv.restrictNormal_commutes σ₀ (w2kumL p V) (w2kumZetaL hadm)
      have heq : ((res σ₀) (w2kumZetaL hadm) : Qbar) =
          ((w2kumZetaL hadm : w2kumL p V) : Qbar) := by
        rw [hcomm, hσ₀ζ]
        rfl
      exact Subtype.ext heq
    have hmem : ΦM ⟨res σ₀, hσ₀H⟩ ∈ ΦM.range := ⟨_, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    have hval : lift (res σ₀) • x₀ - x₀ = 0 := by
      have h2 := congrArg (fun z => (Multiplicative.toAdd z : C).val) hmem
      exact h2
    have hfix : lift (res σ₀) • x₀ = x₀ := by rwa [sub_eq_zero] at hval
    rw [hindep (hlift (res σ₀)) x₀] at hfix
    exact hσ₀ hfix
  haveI : Finite V := w2kum_finite hadm
  have hCcard : Nat.card (Multiplicative C) = p :=
    (Nat.card_congr (Multiplicative.toAdd (α := C))).trans hadm.card_sub
  have hdvd : Nat.card ΦM.range ∣ p := by
    have h := Subgroup.card_subgroup_dvd_card ΦM.range
    rwa [hCcard] at h
  have hrange : Nat.card (w2kumH hadm) = Nat.card ΦM.range :=
    Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd _ hdvd with h1 | hp
  · exact absurd (Subgroup.card_eq_one.mp h1) hnontriv
  · rw [hrange, hp]

@[scoped simp] private theorem w2kumZetaL_eq_iota (hadm : IsAdmissibleExtension p V C) :
    w2kumZetaL hadm = w2kumIota hadm (IsCyclotomicExtension.zeta p ℚ (CyclotomicField p ℚ)) :=
  rfl

private theorem w2kum_hC (hadm : IsAdmissibleExtension p V C)
    (hopen : IsOpen ((w2kumStabV p V : Subgroup Gal) : Set Gal))
    {σ₀ : Gal} {x₀ : V}
    (hσ₀ζ : σ₀ (w2kumZeta p) = w2kumZeta p) (hσ₀ : σ₀ • x₀ ≠ x₀)
    (τ : (w2kumL p V) ≃ₐ[ℚ] (w2kumL p V))
    (hcomm : ∀ σ ∈ w2kumH hadm, τ * σ = σ * τ) : τ ∈ w2kumH hadm := by
  classical
  haveI := w2kum_isGalois_Qbar
  haveI hQbarNormal : Normal ℚ Qbar := by
    have h2 : @Normal ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) :=
      inferInstance
    exact h2
  haveI hLnormal' : @Normal ℚ ↥(w2kumL p V) _ _ (IntermediateField.algebra' (w2kumL p V)) :=
    (IntermediateField.normal_iff_forall_map_le'
      (K := w2kumL p V) (L := Qbar)).mpr (fun σ => w2kum_L_map_le p V σ)
  haveI hLnormal : Normal ℚ ↥(w2kumL p V) := by
    have e : (IntermediateField.algebra' (w2kumL p V) : Algebra ℚ ↥(w2kumL p V)) =
        (inferInstance : Algebra ℚ ↥(w2kumL p V)) := Subsingleton.elim _ _
    exact cast (congrArg (@Normal ℚ ↥(w2kumL p V) _ _) e) hLnormal'
  haveI : FiniteDimensional ℚ (w2kumL p V) := w2kum_L_finiteDimensional p V hopen
  set res := AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Qbar) (w2kumL p V) with hresdef
  have hsurj : Function.Surjective res := by
    rw [hresdef]
    exact AlgEquiv.restrictNormalHom_surjective _
  have hker : ∀ σ : Gal, res σ = 1 ↔ σ ∈ w2kumStabV p V := by
    intro σ
    rw [← w2kum_fixingSubgroup_L p V hopen,
      ← IntermediateField.restrictNormalHom_ker (w2kumL p V), MonoidHom.mem_ker, hresdef]
    exact ⟨fun h => h, fun h => h⟩
  have hindep : ∀ {σ σ' : Gal}, res σ = res σ' → ∀ v : V, σ • v = σ' • v := by
    intro σ σ' h v
    have hmem : σ'⁻¹ * σ ∈ w2kumStabV p V := by
      rw [← hker]
      rw [map_mul, map_inv, h, inv_mul_cancel]
    have h1 : (σ'⁻¹ * σ) • v = v := hmem v
    rw [mul_smul] at h1
    calc σ • v = σ' • σ'⁻¹ • σ • v := (smul_inv_smul σ' _).symm
      _ = σ' • v := by rw [h1]

  obtain ⟨t, ht⟩ := hsurj τ
  have hσ₀H : res σ₀ ∈ w2kumH hadm := by
    rw [w2kumH, MulAction.mem_stabilizer_iff]
    have hcomm₀ : ((res σ₀) (w2kumZetaL hadm) : Qbar) = σ₀ (w2kumZeta p) :=
      AlgEquiv.restrictNormal_commutes σ₀ (w2kumL p V) (w2kumZetaL hadm)
    have heq : ((res σ₀) (w2kumZetaL hadm) : Qbar) =
        ((w2kumZetaL hadm : w2kumL p V) : Qbar) := by
      rw [hcomm₀, hσ₀ζ]
      rfl
    exact Subtype.ext heq

  have hconj_res : res (t * σ₀ * t⁻¹) = res σ₀ := by
    rw [map_mul, map_mul, map_inv, ht]
    have hc := hcomm (res σ₀) hσ₀H
    rw [hc, mul_assoc, mul_inv_cancel, mul_one]
  have hsame : (t * σ₀ * t⁻¹) • x₀ = σ₀ • x₀ := hindep hconj_res x₀

  have hid := w2kum_phi_conj hadm (w2kumZeta_spec p) hσ₀ζ t x₀
  rw [hsame] at hid
  have hφ0 : σ₀ • x₀ - x₀ ≠ 0 := sub_ne_zero.mpr hσ₀
  have hω : ((cycloExp p t⁻¹ : ℕ) : ZMod p) = 1 := by
    by_contra hne
    have hsub : (((cycloExp p t⁻¹ : ℕ) : ZMod p) - 1) • (σ₀ • x₀ - x₀) = 0 := by
      rw [sub_smul, one_smul, ← hid]
      abel
    rcases smul_eq_zero.mp hsub with h | h
    · exact hne (by rwa [sub_eq_zero] at h)
    · exact hφ0 h

  have htζinv : t⁻¹ (w2kumZeta p) = w2kumZeta p :=
    w2kum_fix_of_cycloExp_coe_eq_one (w2kumZeta_spec p) hω
  have htζ : t (w2kumZeta p) = w2kumZeta p := by
    conv_lhs => rw [← htζinv]
    calc t (t⁻¹ (w2kumZeta p)) = (t * t⁻¹) (w2kumZeta p) := rfl
      _ = w2kumZeta p := by rw [mul_inv_cancel]; rfl
  rw [w2kumH, MulAction.mem_stabilizer_iff]
  have hcommt : ((res t) (w2kumZetaL hadm) : Qbar) = t (w2kumZeta p) :=
    AlgEquiv.restrictNormal_commutes t (w2kumL p V) (w2kumZetaL hadm)
  rw [ht] at hcommt
  have heq : (τ (w2kumZetaL hadm) : Qbar) = ((w2kumZetaL hadm : w2kumL p V) : Qbar) := by
    rw [hcommt, htζ]
    rfl
  exact Subtype.ext heq

end CardH
p2m_reactivate "P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation"

section Kummer

p2m_open "NumberField P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.NumberField"

variable {p : ℕ} [Fact p.Prime]
variable {V : Type} [AddCommGroup V] [Module (ZMod p) V]
  [DistribMulAction Gal V] [SMulCommClass Gal (ZMod p) V]
variable {C : Submodule (ZMod p) V}

private theorem w2kum_exists_kummer_generator (hadm : IsAdmissibleExtension p V C)
    (hopen : IsOpen ((w2kumStabV p V : Subgroup Gal) : Set Gal))
    {σ₀ : Gal} {x₀ : V}
    (hσ₀ζ : σ₀ (w2kumZeta p) = w2kumZeta p) (hσ₀ : σ₀ • x₀ ≠ x₀) :
    ∃ (b : 𝓞 (CyclotomicField p ℚ)) (β : w2kumL p V), b ≠ 0 ∧
      β ^ p = w2kumIota hadm b ∧
      ¬ ∃ c : CyclotomicField p ℚ, c ^ p = (b : CyclotomicField p ℚ) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI := w2kum_isGalois_Qbar
  haveI hQbarNormal : Normal ℚ Qbar := by
    have h2 : @Normal ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) :=
      inferInstance
    exact h2
  haveI hLnormal' : @Normal ℚ ↥(w2kumL p V) _ _ (IntermediateField.algebra' (w2kumL p V)) :=
    (IntermediateField.normal_iff_forall_map_le'
      (K := w2kumL p V) (L := Qbar)).mpr (fun σ => w2kum_L_map_le p V σ)
  haveI hLnormal : Normal ℚ ↥(w2kumL p V) := by
    have e : (IntermediateField.algebra' (w2kumL p V) : Algebra ℚ ↥(w2kumL p V)) =
        (inferInstance : Algebra ℚ ↥(w2kumL p V)) := Subsingleton.elim _ _
    exact cast (congrArg (@Normal ℚ ↥(w2kumL p V) _ _) e) hLnormal'
  haveI : FiniteDimensional ℚ (w2kumL p V) := w2kum_L_finiteDimensional p V hopen
  haveI : CharZero ↥(w2kumL p V) :=
    charZero_of_injective_algebraMap (algebraMap ℚ ↥(w2kumL p V)).injective
  haveI hLgalois : IsGalois ℚ ↥(w2kumL p V) := ⟨⟩

  letI : Algebra (CyclotomicField p ℚ) ↥(w2kumL p V) := (w2kumIota hadm).toAlgebra
  haveI : IsScalarTower ℚ (CyclotomicField p ℚ) ↥(w2kumL p V) :=
    IsScalarTower.of_algebraMap_eq (fun x => ((w2kumIota hadm).commutes x).symm)
  haveI : FiniteDimensional (CyclotomicField p ℚ) ↥(w2kumL p V) :=
    FiniteDimensional.right ℚ (CyclotomicField p ℚ) ↥(w2kumL p V)
  haveI hKcLgalois : IsGalois (CyclotomicField p ℚ) ↥(w2kumL p V) :=
    IsGalois.tower_top_of_isGalois ℚ (CyclotomicField p ℚ) ↥(w2kumL p V)

  have hζLalg : algebraMap (CyclotomicField p ℚ) ↥(w2kumL p V)
      (IsCyclotomicExtension.zeta p ℚ (CyclotomicField p ℚ)) = w2kumZetaL hadm := rfl

  have hres2mem : ∀ τ : ↥(w2kumL p V) ≃ₐ[CyclotomicField p ℚ] ↥(w2kumL p V),
      (τ.restrictScalars ℚ) ∈ w2kumH hadm := by
    intro τ
    rw [w2kumH, MulAction.mem_stabilizer_iff]
    show (τ.restrictScalars ℚ) (w2kumZetaL hadm) = w2kumZetaL hadm
    rw [← hζLalg]
    exact τ.commutes _
  have hres2inj : Function.Injective
      (fun τ : ↥(w2kumL p V) ≃ₐ[CyclotomicField p ℚ] ↥(w2kumL p V) =>
        τ.restrictScalars ℚ) := by
    intro τ₁ τ₂ h
    exact AlgEquiv.ext fun x => congrArg (fun f => f x) h

  have hfixKc : ∀ τ' : ↥(w2kumL p V) ≃ₐ[ℚ] ↥(w2kumL p V), τ' ∈ w2kumH hadm →
      ∀ x : CyclotomicField p ℚ,
        τ' (algebraMap (CyclotomicField p ℚ) ↥(w2kumL p V) x) =
          algebraMap (CyclotomicField p ℚ) ↥(w2kumL p V) x := by
    intro τ' hτ' x
    have hζfix : τ' (w2kumZetaL hadm) = w2kumZetaL hadm :=
      MulAction.mem_stabilizer_iff.mp hτ'
    have hx : x ∈ Algebra.adjoin ℚ
        {b : CyclotomicField p ℚ | ∃ n : ℕ, n ∈ ({p} : Set ℕ) ∧ n ≠ 0 ∧ b ^ n = 1} :=
      IsCyclotomicExtension.adjoin_roots x
    have hmem : ∀ b : CyclotomicField p ℚ,
        (∃ n : ℕ, n ∈ ({p} : Set ℕ) ∧ n ≠ 0 ∧ b ^ n = 1) →
          τ' (algebraMap _ _ b) = algebraMap _ _ b := by
      rintro b ⟨n, hn, -, hbn⟩
      rw [Set.mem_singleton_iff] at hn
      rw [hn] at hbn
      have hpow : (algebraMap (CyclotomicField p ℚ) ↥(w2kumL p V) b) ^ p = 1 := by
        rw [← map_pow, hbn, map_one]
      have hζLprim : IsPrimitiveRoot (w2kumZetaL hadm) p := by
        rw [← hζLalg]
        exact (IsCyclotomicExtension.zeta_spec p ℚ (CyclotomicField p ℚ)).map_of_injective
          (algebraMap (CyclotomicField p ℚ) ↥(w2kumL p V)).injective
      obtain ⟨i, -, hi⟩ := hζLprim.eq_pow_of_pow_eq_one hpow
      rw [← hi, map_pow, hζfix]
    refine Algebra.adjoin_induction
      (fun b hb => hmem b hb)
      (fun r => by
        rw [← IsScalarTower.algebraMap_apply ℚ (CyclotomicField p ℚ) ↥(w2kumL p V)]
        exact τ'.commutes r)
      (fun a b _ _ iha ihb => by rw [map_add, map_add, iha, ihb])
      (fun a b _ _ iha ihb => by rw [map_mul, map_mul, iha, ihb])
      hx
  have hres2surj : ∀ τ' ∈ w2kumH hadm,
      ∃ τ : ↥(w2kumL p V) ≃ₐ[CyclotomicField p ℚ] ↥(w2kumL p V),
        τ.restrictScalars ℚ = τ' := by
    intro τ' hτ'
    refine ⟨AlgEquiv.ofRingEquiv (f := τ'.toRingEquiv) (fun x => hfixKc τ' hτ' x), ?_⟩
    ext x
    rfl

  have hcardGal : Nat.card (↥(w2kumL p V) ≃ₐ[CyclotomicField p ℚ] ↥(w2kumL p V)) = p := by
    refine Eq.trans ?_ (w2kum_card_H hadm hopen hσ₀ζ hσ₀)
    apply Nat.card_congr
    refine Equiv.ofBijective
      (fun τ => ⟨τ.restrictScalars ℚ, hres2mem τ⟩) ⟨?_, ?_⟩
    · intro τ₁ τ₂ h
      exact hres2inj (congrArg Subtype.val h)
    · rintro ⟨τ', hτ'⟩
      obtain ⟨τ, hτ⟩ := hres2surj τ' hτ'
      exact ⟨τ, Subtype.ext hτ⟩

  have hfinrank : Module.finrank (CyclotomicField p ℚ) ↥(w2kumL p V) = p := by
    have h1 : Nat.card (↥(w2kumL p V) ≃ₐ[CyclotomicField p ℚ] ↥(w2kumL p V)) =
        Module.finrank (CyclotomicField p ℚ) ↥(w2kumL p V) :=
      IsGalois.card_aut_eq_finrank (CyclotomicField p ℚ) ↥(w2kumL p V)
    rw [← h1]
    exact hcardGal

  haveI hcyc : IsCyclic (↥(w2kumL p V) ≃ₐ[CyclotomicField p ℚ] ↥(w2kumL p V)) :=
    isCyclic_of_prime_card hcardGal
  have hprim : (primitiveRoots
      (Module.finrank (CyclotomicField p ℚ) ↥(w2kumL p V)) (CyclotomicField p ℚ)).Nonempty := by
    rw [hfinrank]
    exact ⟨_, (mem_primitiveRoots (Fact.out : p.Prime).pos).mpr
      (IsCyclotomicExtension.zeta_spec p ℚ (CyclotomicField p ℚ))⟩
  have htfae := (isCyclic_tfae (CyclotomicField p ℚ) ↥(w2kumL p V) hprim).out 0 1
  obtain ⟨a, hIrr, hSplit⟩ := htfae.mp ⟨hKcLgalois, hcyc⟩
  rw [hfinrank] at hIrr hSplit

  haveI := hSplit
  have hsplits : (((Polynomial.X : Polynomial (CyclotomicField p ℚ)) ^ p -
      Polynomial.C a).map
      (algebraMap (CyclotomicField p ℚ) ↥(w2kumL p V))).Splits :=
    Polynomial.IsSplittingField.splits (L := ↥(w2kumL p V)) _
  have hdeg : (((Polynomial.X : Polynomial (CyclotomicField p ℚ)) ^ p -
      Polynomial.C a).map
      (algebraMap (CyclotomicField p ℚ) ↥(w2kumL p V))).degree ≠ 0 := by
    rw [Polynomial.degree_map, Polynomial.degree_X_pow_sub_C (Fact.out : p.Prime).pos]
    exact_mod_cast Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  obtain ⟨β₀, hβ₀⟩ := hsplits.exists_eval_eq_zero hdeg
  have hβ₀pow : β₀ ^ p = algebraMap (CyclotomicField p ℚ) ↥(w2kumL p V) a := by
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
      Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
      sub_eq_zero] at hβ₀
    exact hβ₀

  have hanp : ∀ c : CyclotomicField p ℚ, c ^ p ≠ a :=
    (X_pow_sub_C_irreducible_iff_of_prime (Fact.out : p.Prime)).mp hIrr
  have ha0 : a ≠ 0 := fun h => hanp 0 (by rw [zero_pow (Fact.out : p.Prime).ne_zero, h])

  obtain ⟨dM, hdM⟩ := IsLocalization.exists_integer_multiple
    (M := nonZeroDivisors (𝓞 (CyclotomicField p ℚ))) a
  obtain ⟨bInt, hbInt⟩ := hdM
  set D : 𝓞 (CyclotomicField p ℚ) := (dM : 𝓞 (CyclotomicField p ℚ)) with hDdef
  have hD0' : D ≠ 0 := nonZeroDivisors.coe_ne_zero dM
  have hD0 : (D : CyclotomicField p ℚ) ≠ 0 := fun h =>
    hD0' ((map_eq_zero_iff _ (IsFractionRing.injective (𝓞 (CyclotomicField p ℚ))
      (CyclotomicField p ℚ))).mp h)
  have hbIntval : (bInt : CyclotomicField p ℚ) = (D : CyclotomicField p ℚ) * a := by
    have h := hbInt
    rw [Algebra.smul_def] at h
    exact h
  have harg : ((D ^ (p - 1) * bInt : 𝓞 (CyclotomicField p ℚ)) : CyclotomicField p ℚ) =
      (D : CyclotomicField p ℚ) ^ p * a := by
    push_cast [hbIntval]
    rw [← mul_assoc, ← pow_succ, Nat.sub_add_cancel (Fact.out : p.Prime).one_lt.le]
  refine ⟨D ^ (p - 1) * bInt,
    algebraMap (CyclotomicField p ℚ) ↥(w2kumL p V) (D : CyclotomicField p ℚ) * β₀,
    ?_, ?_, ?_⟩
  ·
    intro h
    rw [h] at harg
    simp only [map_zero] at harg
    rcases mul_eq_zero.mp harg.symm with h1 | h1
    · exact pow_ne_zero p hD0 h1
    · exact ha0 h1
  ·
    have hcoe : (w2kumIota hadm) (((D ^ (p - 1) * bInt : 𝓞 (CyclotomicField p ℚ)) :
        CyclotomicField p ℚ)) =
        algebraMap (CyclotomicField p ℚ) ↥(w2kumL p V)
          ((D : CyclotomicField p ℚ) ^ p * a) :=
      congrArg (algebraMap (CyclotomicField p ℚ) ↥(w2kumL p V)) harg
    rw [mul_pow, hβ₀pow, hcoe, map_mul, map_pow]
  ·
    rintro ⟨c, hc⟩
    apply hanp (c / (D : CyclotomicField p ℚ))
    rw [div_pow]
    rw [harg] at hc
    rw [hc, mul_comm, mul_div_assoc, div_self (pow_ne_zero p hD0), mul_one]

end Kummer
p2m_reactivate "P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation"

section Package

p2m_open "NumberField P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.NumberField JacobiSumStickelberger"

variable {p : ℕ} [Fact p.Prime]
variable {V : Type} [AddCommGroup V] [Module (ZMod p) V]
  [DistribMulAction Gal V] [SMulCommClass Gal (ZMod p) V]
variable {C : Submodule (ZMod p) V}

omit [Module (ZMod p) V] [SMulCommClass Gal (ZMod p) V] in

private theorem w2kum_dichotomy :
    (∀ σ : Gal, σ (w2kumZeta p) = w2kumZeta p → ∀ x : V, σ • x = x) ∨
    ∃ (σ₀ : Gal) (x₀ : V), σ₀ (w2kumZeta p) = w2kumZeta p ∧ σ₀ • x₀ ≠ x₀ := by
  by_cases h : ∀ σ : Gal, σ (w2kumZeta p) = w2kumZeta p → ∀ x : V, σ • x = x
  · exact Or.inl h
  · right
    push Not at h
    obtain ⟨σ₀, hσ₀ζ, x₀, hσ₀⟩ := h
    exact ⟨σ₀, x₀, hσ₀ζ, hσ₀⟩

private theorem w2kum_pkg_of_hbeig (hadm : IsAdmissibleExtension p V C)
    (hopen : IsOpen ((w2kumStabV p V : Subgroup Gal) : Set Gal))
    {σ₀ : Gal} {x₀ : V}
    (hσ₀ζ : σ₀ (w2kumZeta p) = w2kumZeta p) (hσ₀ : σ₀ • x₀ ≠ x₀)
    (hbeig_ext : ∀ (b : 𝓞 (CyclotomicField p ℚ)) (β : w2kumL p V), b ≠ 0 →
      β ^ p = w2kumIota hadm b → (¬ ∃ c : CyclotomicField p ℚ, c ^ p = (b : CyclotomicField p ℚ)) →
      ∀ d : (ZMod p)ˣ, ∃ γ : CyclotomicField p ℚ,
        (cycloGalEquiv p (CyclotomicField p ℚ)).symm d (b : CyclotomicField p ℚ) =
          (b : CyclotomicField p ℚ) ^ (((d : ZMod p)) ^ 2).val * γ ^ p) :
    ∃ (L : IntermediateField ℚ Qbar) (_ : FiniteDimensional ℚ ↥L) (_ : IsGalois ℚ ↥L)
      (ι : CyclotomicField p ℚ →ₐ[ℚ] ↥L) (b : 𝓞 (CyclotomicField p ℚ)) (_ : b ≠ 0)
      (β : ↥L) (_ : β ^ p = ι (b : CyclotomicField p ℚ)),
      (∀ q : ℕ, q.Prime → ∀ A : ValuationSubring Qbar, A.LiesOverPrime q →
        A.inertiaSubgroupIn ℚ ⊓ MulAction.stabilizer Gal
          ((ι (IsCyclotomicExtension.zeta p ℚ (CyclotomicField p ℚ)) : ↥L) : Qbar) ≤
            L.fixingSubgroup) ∧
      (∀ τ : ↥L ≃ₐ[ℚ] ↥L,
        (∀ σ ∈ MulAction.stabilizer (↥L ≃ₐ[ℚ] ↥L)
          (ι (IsCyclotomicExtension.zeta p ℚ (CyclotomicField p ℚ))), τ * σ = σ * τ) →
          τ ∈ MulAction.stabilizer (↥L ≃ₐ[ℚ] ↥L)
            (ι (IsCyclotomicExtension.zeta p ℚ (CyclotomicField p ℚ)))) ∧
      Nat.card (MulAction.stabilizer (↥L ≃ₐ[ℚ] ↥L)
        (ι (IsCyclotomicExtension.zeta p ℚ (CyclotomicField p ℚ)))) = p ∧
      (∀ d : (ZMod p)ˣ, ∃ γ : CyclotomicField p ℚ,
        (cycloGalEquiv p (CyclotomicField p ℚ)).symm d (b : CyclotomicField p ℚ) =
          (b : CyclotomicField p ℚ) ^ (((d : ZMod p)) ^ 2).val * γ ^ p) ∧
      ¬ ∃ c : CyclotomicField p ℚ, c ^ p = (b : CyclotomicField p ℚ) := by
  classical
  haveI := w2kum_isGalois_Qbar
  haveI hQbarNormal : Normal ℚ Qbar := by
    have h2 : @Normal ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) :=
      inferInstance
    exact h2
  haveI hLnormal' : @Normal ℚ ↥(w2kumL p V) _ _ (IntermediateField.algebra' (w2kumL p V)) :=
    (IntermediateField.normal_iff_forall_map_le'
      (K := w2kumL p V) (L := Qbar)).mpr (fun σ => w2kum_L_map_le p V σ)
  haveI hLnormal : Normal ℚ ↥(w2kumL p V) := by
    have e : (IntermediateField.algebra' (w2kumL p V) : Algebra ℚ ↥(w2kumL p V)) =
        (inferInstance : Algebra ℚ ↥(w2kumL p V)) := Subsingleton.elim _ _
    exact cast (congrArg (@Normal ℚ ↥(w2kumL p V) _ _) e) hLnormal'
  haveI hLfin : FiniteDimensional ℚ (w2kumL p V) := w2kum_L_finiteDimensional p V hopen
  haveI : CharZero ↥(w2kumL p V) :=
    charZero_of_injective_algebraMap (algebraMap ℚ ↥(w2kumL p V)).injective
  haveI hLgalois : IsGalois ℚ ↥(w2kumL p V) := ⟨⟩
  obtain ⟨b, β, hb0, hβ, hbnp⟩ :=
    w2kum_exists_kummer_generator hadm hopen hσ₀ζ hσ₀
  refine ⟨w2kumL p V, hLfin, hLgalois, w2kumIota hadm, b, hb0, β, hβ, ?_, ?_, ?_, ?_, hbnp⟩
  ·
    intro q hq A hA
    rw [w2kum_fixingSubgroup_L p V hopen]
    exact w2kum_inertia_le_stabV hadm q hq A hA
  ·
    intro τ hcomm
    exact w2kum_hC hadm hopen hσ₀ζ hσ₀ τ hcomm
  ·
    exact w2kum_card_H hadm hopen hσ₀ζ hσ₀
  ·
    exact hbeig_ext b β hb0 hβ hbnp

end Package
p2m_reactivate "P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation"

end ExtCitation
p2m_reactivate "P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation"

end PART_R1A_MAIN_aux4
p2m_reactivate "P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation"

section PART_R1A_HBEIG_aux1

namespace ExtCitation
p2m_export "ExtCitation" "ExtVanishingCts card_rootsOfUnity_eq_self cycloExp IsAdmissibleExtension SplitsGlobally Cyclotomic.instIsCycExt"
p2m_open "ExtCitation"

section Hbeig

p2m_open "NumberField P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.NumberField JacobiSumStickelberger"

variable {p : ℕ} [hp' : Fact p.Prime]
variable {V : Type} [AddCommGroup V] [Module (ZMod p) V]
  [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) V]
  [SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (ZMod p) V]
variable {C : Submodule (ZMod p) V}

set_option maxHeartbeats 3200000 in

private theorem w2kum_hbeig (hadm : IsAdmissibleExtension p V C)
    (hopen : IsOpen ((w2kumStabV p V : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :
      Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)))
    {σ₀ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} {x₀ : V}
    (_hσ₀ζ : σ₀ (w2kumZeta p) = w2kumZeta p) (hσ₀ : σ₀ • x₀ ≠ x₀)
    (b : 𝓞 (CyclotomicField p ℚ)) (β : w2kumL p V) (hb0 : b ≠ 0)
    (hβ : β ^ p = w2kumIota hadm b)
    (_hbnp : ¬ ∃ c : CyclotomicField p ℚ, c ^ p = (b : CyclotomicField p ℚ)) :
    ∀ d : (ZMod p)ˣ, ∃ γ : CyclotomicField p ℚ,
      (cycloGalEquiv p (CyclotomicField p ℚ)).symm d (b : CyclotomicField p ℚ) =
        (b : CyclotomicField p ℚ) ^ (((d : ZMod p)) ^ 2).val * γ ^ p := by
  classical
  intro d
  haveI : NeZero p := ⟨hp'.1.ne_zero⟩

  haveI := w2kum_isGalois_Qbar
  haveI hQbarNormal : Normal ℚ (AlgebraicClosure ℚ) := by
    have h2 : @Normal ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) :=
      inferInstance
    exact h2
  haveI hLnormal' : @Normal ℚ ↥(w2kumL p V) _ _ (IntermediateField.algebra' (w2kumL p V)) :=
    (IntermediateField.normal_iff_forall_map_le'
      (K := w2kumL p V) (L := AlgebraicClosure ℚ)).mpr (fun σ => w2kum_L_map_le p V σ)
  haveI hLnormal : Normal ℚ ↥(w2kumL p V) := by
    have e : (IntermediateField.algebra' (w2kumL p V) : Algebra ℚ ↥(w2kumL p V)) =
        (inferInstance : Algebra ℚ ↥(w2kumL p V)) := Subsingleton.elim _ _
    exact cast (congrArg (@Normal ℚ ↥(w2kumL p V) _ _) e) hLnormal'
  haveI : FiniteDimensional ℚ (w2kumL p V) := w2kum_L_finiteDimensional p V hopen
  haveI : CharZero ↥(w2kumL p V) :=
    charZero_of_injective_algebraMap (algebraMap ℚ ↥(w2kumL p V)).injective
  haveI hLgalois : IsGalois ℚ ↥(w2kumL p V) := ⟨⟩
  letI : Algebra (CyclotomicField p ℚ) ↥(w2kumL p V) := (w2kumIota hadm).toAlgebra
  haveI : IsScalarTower ℚ (CyclotomicField p ℚ) ↥(w2kumL p V) :=
    IsScalarTower.of_algebraMap_eq (fun x => ((w2kumIota hadm).commutes x).symm)
  haveI : FiniteDimensional (CyclotomicField p ℚ) ↥(w2kumL p V) :=
    FiniteDimensional.right ℚ (CyclotomicField p ℚ) ↥(w2kumL p V)
  haveI hKcLgalois : IsGalois (CyclotomicField p ℚ) ↥(w2kumL p V) :=
    IsGalois.tower_top_of_isGalois ℚ (CyclotomicField p ℚ) ↥(w2kumL p V)
  have hζLalg : algebraMap (CyclotomicField p ℚ) ↥(w2kumL p V)
      (IsCyclotomicExtension.zeta p ℚ (CyclotomicField p ℚ)) = w2kumZetaL hadm := rfl
  have hζLprim : IsPrimitiveRoot (w2kumZetaL hadm) p := by
    rw [← hζLalg]
    exact (IsCyclotomicExtension.zeta_spec p ℚ (CyclotomicField p ℚ)).map_of_injective
      (algebraMap (CyclotomicField p ℚ) ↥(w2kumL p V)).injective
  have hζL0 : (w2kumZetaL hadm) ≠ 0 := hζLprim.ne_zero hp'.1.ne_zero

  set res := AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) (w2kumL p V)
    with hresdef
  have hsurj : Function.Surjective res := by
    rw [hresdef]
    exact AlgEquiv.restrictNormalHom_surjective _
  have hker : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      res σ = 1 ↔ σ ∈ w2kumStabV p V := by
    intro σ
    rw [← w2kum_fixingSubgroup_L p V hopen,
      ← IntermediateField.restrictNormalHom_ker (w2kumL p V), MonoidHom.mem_ker, hresdef]
    exact ⟨fun h => h, fun h => h⟩

  have hfixKc : ∀ τ' : ↥(w2kumL p V) ≃ₐ[ℚ] ↥(w2kumL p V), τ' ∈ w2kumH hadm →
      ∀ x : CyclotomicField p ℚ,
        τ' (algebraMap (CyclotomicField p ℚ) ↥(w2kumL p V) x) =
          algebraMap (CyclotomicField p ℚ) ↥(w2kumL p V) x := by
    intro τ' hτ' x
    have hζfix : τ' (w2kumZetaL hadm) = w2kumZetaL hadm :=
      MulAction.mem_stabilizer_iff.mp hτ'
    have hx : x ∈ Algebra.adjoin ℚ
        {b : CyclotomicField p ℚ | ∃ n : ℕ, n ∈ ({p} : Set ℕ) ∧ n ≠ 0 ∧ b ^ n = 1} :=
      IsCyclotomicExtension.adjoin_roots x
    have hmem : ∀ b : CyclotomicField p ℚ,
        (∃ n : ℕ, n ∈ ({p} : Set ℕ) ∧ n ≠ 0 ∧ b ^ n = 1) →
          τ' (algebraMap _ _ b) = algebraMap _ _ b := by
      rintro b ⟨n, hn, -, hbn⟩
      rw [Set.mem_singleton_iff] at hn
      rw [hn] at hbn
      have hpow : (algebraMap (CyclotomicField p ℚ) ↥(w2kumL p V) b) ^ p = 1 := by
        rw [← map_pow, hbn, map_one]
      obtain ⟨i, -, hi⟩ := hζLprim.eq_pow_of_pow_eq_one hpow
      rw [← hi, map_pow, hζfix]
    refine Algebra.adjoin_induction
      (fun b hb => hmem b hb)
      (fun r => by
        rw [← IsScalarTower.algebraMap_apply ℚ (CyclotomicField p ℚ) ↥(w2kumL p V)]
        exact τ'.commutes r)
      (fun a b _ _ iha ihb => by rw [map_add, map_add, iha, ihb])
      (fun a b _ _ iha ihb => by rw [map_mul, map_mul, iha, ihb])
      hx

  set n : ℕ := (d : ZMod p).val with hndef
  have hncop : n.Coprime p := ZMod.val_coe_unit_coprime d
  have hnlt : n < p := ZMod.val_lt _
  obtain ⟨t, ht⟩ := w2kum_exists_conj (w2kumZeta_spec p) hncop
  set τ : ↥(w2kumL p V) ≃ₐ[ℚ] ↥(w2kumL p V) := res t with hτdef
  have hτζ : τ (w2kumZetaL hadm) = (w2kumZetaL hadm) ^ n := by
    apply Subtype.ext
    have hc : ((τ (w2kumZetaL hadm) : ↥(w2kumL p V)) : AlgebraicClosure ℚ) = t (w2kumZeta p) :=
      AlgEquiv.restrictNormal_commutes t (w2kumL p V) (w2kumZetaL hadm)
    rw [hc, ht, SubmonoidClass.coe_pow]
    rfl
  have hexpt : cycloExp p t = n :=
    (w2kumZeta_spec p).pow_inj (w2kum_cycloExp_lt t) hnlt
      ((w2kum_apply_eq_pow_cycloExp (w2kumZeta_spec p) t).symm.trans ht)

  set σd : CyclotomicField p ℚ ≃ₐ[ℚ] CyclotomicField p ℚ :=
    (cycloGalEquiv p (CyclotomicField p ℚ)).symm d with hσddef
  have hσdzeta : σd (IsCyclotomicExtension.zeta p ℚ (CyclotomicField p ℚ)) =
      (IsCyclotomicExtension.zeta p ℚ (CyclotomicField p ℚ)) ^ n := by
    have h1 : cycloGalEquiv p (CyclotomicField p ℚ) σd = d := MulEquiv.apply_symm_apply _ d
    have h2 : (IsCyclotomicExtension.zeta_spec p ℚ (CyclotomicField p ℚ)).autToPow ℚ σd = d := by
      rw [← h1]
      rfl
    have h3 := (IsCyclotomicExtension.zeta_spec p ℚ (CyclotomicField p ℚ)).autToPow_spec ℚ σd
    rw [h2] at h3
    exact h3.symm
  have hτKc : ∀ x : CyclotomicField p ℚ,
      τ (algebraMap (CyclotomicField p ℚ) ↥(w2kumL p V) x) =
        algebraMap (CyclotomicField p ℚ) ↥(w2kumL p V) (σd x) := by
    have heq : (τ : ↥(w2kumL p V) →ₐ[ℚ] ↥(w2kumL p V)).comp
          (IsScalarTower.toAlgHom ℚ (CyclotomicField p ℚ) ↥(w2kumL p V)) =
        (IsScalarTower.toAlgHom ℚ (CyclotomicField p ℚ) ↥(w2kumL p V)).comp
          (σd : CyclotomicField p ℚ →ₐ[ℚ] CyclotomicField p ℚ) := by
      refine AlgHom.ext_of_adjoin_eq_top
        (IsCyclotomicExtension.adjoin_primitive_root_eq_top
          (IsCyclotomicExtension.zeta_spec p ℚ (CyclotomicField p ℚ))) ?_
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      show τ (algebraMap (CyclotomicField p ℚ) ↥(w2kumL p V)
          (IsCyclotomicExtension.zeta p ℚ (CyclotomicField p ℚ))) =
        algebraMap (CyclotomicField p ℚ) ↥(w2kumL p V)
          (σd (IsCyclotomicExtension.zeta p ℚ (CyclotomicField p ℚ)))
      rw [hσdzeta, map_pow, hζLalg, hτζ]
    intro x
    exact AlgHom.congr_fun heq x

  have hβ0 : β ≠ 0 := by
    intro h
    rw [h, zero_pow hp'.1.ne_zero] at hβ
    have h1 : (b : CyclotomicField p ℚ) = 0 :=
      (map_eq_zero_iff _ (w2kumIota hadm).toRingHom.injective).mp hβ.symm
    exact hb0 ((map_eq_zero_iff _ (IsFractionRing.injective (𝓞 (CyclotomicField p ℚ))
      (CyclotomicField p ℚ))).mp h1)
  have hk : ∀ s : ↥(w2kumL p V) ≃ₐ[ℚ] ↥(w2kumL p V), s ∈ w2kumH hadm →
      ∃ k : ℕ, s β = (w2kumZetaL hadm) ^ k * β := by
    intro s hs
    have hsb : s (β ^ p) = β ^ p := by
      rw [hβ]
      exact hfixKc s hs (b : CyclotomicField p ℚ)
    have hu : (s β / β) ^ p = 1 := by
      rw [div_pow, ← map_pow, hsb, div_self (pow_ne_zero p hβ0)]
    obtain ⟨k, -, hk⟩ := hζLprim.eq_pow_of_pow_eq_one hu
    exact ⟨k, by rw [hk, div_mul_cancel₀ _ hβ0]⟩
  choose! kf hkf using hk
  have hiter : ∀ s : ↥(w2kumL p V) ≃ₐ[ℚ] ↥(w2kumL p V), s ∈ w2kumH hadm → ∀ m : ℕ,
      (s ^ m) β = (w2kumZetaL hadm) ^ (m * kf s) * β := by
    intro s hs m
    have hsζ : s (w2kumZetaL hadm) = w2kumZetaL hadm := MulAction.mem_stabilizer_iff.mp hs
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, map_mul, map_pow, hsζ, hkf s hs]
      ring

  have hx₀C : x₀ ∉ C := fun hmem => hσ₀ (hadm.fixed_sub σ₀ x₀ hmem)
  have hconj : ∀ s : ↥(w2kumL p V) ≃ₐ[ℚ] ↥(w2kumL p V), s ∈ w2kumH hadm →
      τ⁻¹ * s * τ = s ^ n := by
    intro s hs
    obtain ⟨S, hS⟩ := hsurj s

    have hSζ : S (w2kumZeta p) = w2kumZeta p := by
      have hc : ((res S (w2kumZetaL hadm) : ↥(w2kumL p V)) : AlgebraicClosure ℚ) =
          S (w2kumZeta p) :=
        AlgEquiv.restrictNormal_commutes S (w2kumL p V) (w2kumZetaL hadm)
      have hsζ : s (w2kumZetaL hadm) = w2kumZetaL hadm := MulAction.mem_stabilizer_iff.mp hs
      rw [hS, hsζ] at hc
      exact hc.symm

    have hφX : (t⁻¹ * S * t) • x₀ - x₀ = ((n : ℕ) : ZMod p) • (S • x₀ - x₀) := by
      have h := w2kum_phi_conj hadm (w2kumZeta_spec p) hSζ t⁻¹ x₀
      rw [inv_inv, hexpt] at h
      exact h

    have hY : ∀ m : ℕ, (S ^ m) (w2kumZeta p) = w2kumZeta p ∧
        (S ^ m) • x₀ - x₀ = ((m : ℕ) : ZMod p) • (S • x₀ - x₀) := by
      intro m
      induction m with
      | zero => exact ⟨by simp, by simp⟩
      | succ m ih =>
        refine ⟨by rw [pow_succ, AlgEquiv.mul_apply, hSζ, ih.1], ?_⟩
        rw [pow_succ, w2kum_phi_mul hadm (w2kumZeta_spec p) ih.1 hSζ x₀, ih.2, Nat.cast_succ,
          add_smul, one_smul]

    have hXζ : (t⁻¹ * S * t) (w2kumZeta p) = w2kumZeta p := by
      rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, ht, map_pow, hSζ, ← ht, ← AlgEquiv.mul_apply,
        inv_mul_cancel, AlgEquiv.one_apply]

    have hYinvζ : (S ^ n)⁻¹ (w2kumZeta p) = w2kumZeta p := by
      conv_lhs => rw [← (hY n).1]
      rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
    have hφYinv : (S ^ n)⁻¹ • x₀ - x₀ = -((S ^ n) • x₀ - x₀) := by
      have h := w2kum_phi_mul hadm (w2kumZeta_spec p) hYinvζ (hY n).1 x₀
      rw [inv_mul_cancel, one_smul, sub_self] at h
      exact eq_neg_of_add_eq_zero_left h.symm
    have hfix : ((S ^ n)⁻¹ * (t⁻¹ * S * t)) • x₀ = x₀ := by
      have h := w2kum_phi_mul hadm (w2kumZeta_spec p) hYinvζ hXζ x₀
      rw [hφYinv, hφX, (hY n).2, neg_add_cancel, sub_eq_zero] at h
      exact h
    have hXY : ∀ v : V, (t⁻¹ * S * t) • v = (S ^ n) • v := by
      intro v
      have htriv := w2kum_triv_of_phi_eq_zero hadm hx₀C hfix v
      rw [mul_smul] at htriv
      calc (t⁻¹ * S * t) • v = (S ^ n) • ((S ^ n)⁻¹ • (t⁻¹ * S * t) • v) :=
            (smul_inv_smul (S ^ n) _).symm
        _ = (S ^ n) • v := by rw [htriv]
    have hresXY : res (t⁻¹ * S * t) = res (S ^ n) := by
      have hmem : (t⁻¹ * S * t) * (S ^ n)⁻¹ ∈ w2kumStabV p V := fun v => by
        show ((t⁻¹ * S * t) * (S ^ n)⁻¹) • v = v
        rw [mul_smul, hXY, smul_inv_smul]
      have h1 : res ((t⁻¹ * S * t) * (S ^ n)⁻¹) = 1 := (hker _).mpr hmem
      rw [map_mul, map_inv, mul_inv_eq_one] at h1
      exact h1
    calc τ⁻¹ * s * τ = res (t⁻¹ * S * t) := by rw [hτdef, ← hS, ← map_inv, ← map_mul, ← map_mul]
      _ = res (S ^ n) := hresXY
      _ = s ^ n := by rw [map_pow, hS]

  have hsτβ : ∀ s : ↥(w2kumL p V) ≃ₐ[ℚ] ↥(w2kumL p V), s ∈ w2kumH hadm →
      s (τ β) = (w2kumZetaL hadm) ^ (n * (n * kf s)) * τ β := by
    intro s hs
    have h1 : s (τ β) = τ ((τ⁻¹ * s * τ) β) := by
      rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, ← AlgEquiv.mul_apply τ τ⁻¹, mul_inv_cancel,
        AlgEquiv.one_apply]
    rw [h1, hconj s hs, hiter s hs n, map_mul, map_pow, hτζ, ← pow_mul]

  set η : ↥(w2kumL p V) := τ β / β ^ (n * n) with hηdef
  have hηfix : ∀ g : ↥(w2kumL p V) ≃ₐ[CyclotomicField p ℚ] ↥(w2kumL p V), g η = η := by
    intro g
    have hs : (g.restrictScalars ℚ) ∈ w2kumH hadm := by
      rw [w2kumH, MulAction.mem_stabilizer_iff]
      show (g.restrictScalars ℚ) (w2kumZetaL hadm) = w2kumZetaL hadm
      rw [← hζLalg]
      exact g.commutes _
    have hg : g η = (g.restrictScalars ℚ) η := rfl
    rw [hg, hηdef, map_div₀, map_pow, hsτβ _ hs, hkf _ hs, mul_pow, ← pow_mul,
      show kf (g.restrictScalars ℚ) * (n * n) = n * (n * kf (g.restrictScalars ℚ)) by ring,
      mul_div_mul_left _ _ (pow_ne_zero _ hζL0)]
  obtain ⟨γ, hγ⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := CyclotomicField p ℚ) η).mpr hηfix

  have hτβ : τ β = η * β ^ (n * n) := by rw [hηdef, div_mul_cancel₀ _ (pow_ne_zero _ hβ0)]
  have hLeq : algebraMap (CyclotomicField p ℚ) ↥(w2kumL p V) (σd (b : CyclotomicField p ℚ)) =
      algebraMap (CyclotomicField p ℚ) ↥(w2kumL p V)
        ((b : CyclotomicField p ℚ) ^ (n * n) * γ ^ p) := by
    rw [← hτKc, map_mul, map_pow, map_pow, hγ]
    have hab : algebraMap (CyclotomicField p ℚ) ↥(w2kumL p V) (b : CyclotomicField p ℚ) =
        β ^ p := hβ.symm
    rw [hab, map_pow, hτβ, mul_pow, ← pow_mul, ← pow_mul]
    ring
  have hKeq : σd (b : CyclotomicField p ℚ) = (b : CyclotomicField p ℚ) ^ (n * n) * γ ^ p :=
    (algebraMap (CyclotomicField p ℚ) ↥(w2kumL p V)).injective hLeq

  have hval : ((d : ZMod p) ^ 2).val = (n * n) % p := by
    have h1 : (d : ZMod p) ^ 2 = ((n * n : ℕ) : ZMod p) := by
      rw [Nat.cast_mul, hndef, ZMod.natCast_zmod_val, sq]
    rw [h1, ZMod.val_natCast]
  have hsplit : (b : CyclotomicField p ℚ) ^ (n * n) =
      (b : CyclotomicField p ℚ) ^ ((n * n) % p) *
        ((b : CyclotomicField p ℚ) ^ ((n * n) / p)) ^ p := by
    conv_lhs => rw [← Nat.mod_add_div (n * n) p]
    ring
  refine ⟨(b : CyclotomicField p ℚ) ^ ((n * n) / p) * γ, ?_⟩
  rw [hKeq, hval, hsplit]
  ring

end Hbeig
p2m_reactivate "P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation"

end ExtCitation
p2m_reactivate "P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation"

end PART_R1A_HBEIG_aux1
p2m_reactivate "P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation"

section PART_R3_TBC_aux1

set_option autoImplicit false

namespace ExtCitation
p2m_export "ExtCitation" "ExtVanishingCts card_rootsOfUnity_eq_self cycloExp IsAdmissibleExtension SplitsGlobally Cyclotomic.instIsCycExt"
namespace KumFinite
p2m_open "ExtCitation"

p2m_open_scoped "NumberField P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.NumberField Pointwise"
p2m_open "Ideal NumberField.Ideal"

private theorem eq_bot_of_normal_of_disjoint_of_centralizer_le {G : Type*} [Group G]
    {S I D : Subgroup G} (hID : I ≤ D) (hSD : S ≤ D) (hIn : (I.subgroupOf D).Normal)
    (hSn : S.Normal) (hdisj : I ⊓ S = ⊥)
    (hC : ∀ τ : G, (∀ σ ∈ S, τ * σ = σ * τ) → τ ∈ S) : I = ⊥ := by
  have hSn' : (S.subgroupOf D).Normal := hSn.subgroupOf D
  have hdis : Disjoint (I.subgroupOf D) (S.subgroupOf D) := by
    rw [disjoint_iff, eq_bot_iff]
    intro y hy
    have h1 : (y : G) ∈ I := Subgroup.mem_subgroupOf.mp hy.1
    have h2 : (y : G) ∈ S := Subgroup.mem_subgroupOf.mp hy.2
    have : (y : G) ∈ I ⊓ S := ⟨h1, h2⟩
    rw [hdisj, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact Subtype.ext this
  rw [eq_bot_iff]
  intro x hx
  have hxS : x ∈ S := by
    refine hC x fun σ hσ => ?_
    have h := Subgroup.commute_of_normal_of_disjoint _ _ hIn hSn' hdis ⟨x, hID hx⟩ ⟨σ, hSD hσ⟩
      (Subgroup.mem_subgroupOf.mpr hx) (Subgroup.mem_subgroupOf.mpr hσ)
    exact congrArg Subtype.val h.eq
  have : x ∈ I ⊓ S := ⟨hx, hxS⟩
  rwa [hdisj] at this

private theorem card_stabilizer_eq_one_of {M α : Type*} [Group M] [MulAction M α] {a : α}
    (h : ∀ m ∈ MulAction.stabilizer M a, m = 1) : Nat.card (MulAction.stabilizer M a) = 1 := by
  rw [(Subgroup.eq_bot_iff_forall _).mpr h, Subgroup.card_bot]

section Cyclo

variable (p : ℕ) [hp : Fact p.Prime] (L : Type*) [Field L] [NumberField L]
  [Algebra (CyclotomicField p ℚ) L]

local notation "C" => CyclotomicField p ℚ

set_option backward.isDefEq.respectTransparency false in

private noncomputable scoped instance instIsCycExtC : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
  inferInstance

private noncomputable def zetaL : L := algebraMap C L (IsCyclotomicExtension.zeta p ℚ C)

omit [NumberField L] in
private theorem zetaL_spec : IsPrimitiveRoot (zetaL p L) p :=
  (IsCyclotomicExtension.zeta_spec p ℚ C).map_of_injective (algebraMap C L).injective

private noncomputable def stabZeta : Subgroup (L ≃ₐ[ℚ] L) :=
  MulAction.stabilizer (L ≃ₐ[ℚ] L) (zetaL p L)

private theorem mem_stabZeta {σ : L ≃ₐ[ℚ] L} : σ ∈ stabZeta p L ↔ σ (zetaL p L) = zetaL p L := Iff.rfl

private scoped instance isScalarTower_rat : IsScalarTower ℚ C L :=
  IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

private theorem apply_algebraMap_of_mem_stabZeta {σ : L ≃ₐ[ℚ] L} (hσ : σ ∈ stabZeta p L) (c : C) :
    σ (algebraMap C L c) = algebraMap C L c := by
  have hp0 : NeZero p := ⟨hp.1.ne_zero⟩
  have hc : c ∈ Algebra.adjoin ℚ ({IsCyclotomicExtension.zeta p ℚ C} : Set C) := by
    rw [IsCyclotomicExtension.adjoin_primitive_root_eq_top (IsCyclotomicExtension.zeta_spec p ℚ C)]
    trivial
  refine Algebra.adjoin_induction (fun x hx => ?_) (fun r => ?_) (fun x y _ _ hx hy => ?_)
    (fun x y _ _ hx hy => ?_) hc
  · rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact hσ
  · rw [← IsScalarTower.algebraMap_apply, AlgEquiv.commutes]
  · rw [map_add, map_add, hx, hy]
  · rw [map_mul, map_mul, hx, hy]

private theorem stabZeta_normal : (stabZeta p L).Normal := by
  have hp0 : NeZero p := ⟨hp.1.ne_zero⟩
  refine ⟨fun σ hσ τ => ?_⟩
  rw [mem_stabZeta] at hσ ⊢
  have h1 : (τ⁻¹ (zetaL p L)) ^ p = 1 := by
    rw [← map_pow, (zetaL_spec p L).pow_eq_one, map_one]
  obtain ⟨i, -, hi⟩ := (zetaL_spec p L).eq_pow_of_pow_eq_one h1
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, ← hi, map_pow, hσ, hi,
    ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

variable [IsGalois ℚ L]

private scoped instance isGaloisGroup_stabZeta : IsGaloisGroup (stabZeta p L) C L where
  faithful := inferInstance
  commutes := ⟨fun σ c x => by
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul']
    congr 1
    exact apply_algebraMap_of_mem_stabZeta p L σ.2 c⟩
  isInvariant := ⟨fun x hx => by
    set K₁ : IntermediateField ℚ L := IntermediateField.adjoin ℚ {zetaL p L} with hK₁
    have hSK₁ : K₁.fixingSubgroup = stabZeta p L := by
      ext σ
      rw [IntermediateField.mem_fixingSubgroup_iff, mem_stabZeta]
      constructor
      · intro h
        exact h _ (IntermediateField.mem_adjoin_simple_self ℚ (zetaL p L))
      · intro h y hy
        have hy' : y ∈ (IntermediateField.adjoin ℚ {zetaL p L}).toSubalgebra := hy
        rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
          (Algebra.IsAlgebraic.isAlgebraic _)] at hy'
        refine Algebra.adjoin_induction (fun z hz => ?_) (fun r => ?_) (fun z w _ _ hz hw => ?_)
          (fun z w _ _ hz hw => ?_) hy'
        · rw [Set.mem_singleton_iff] at hz; rw [hz]; exact h
        · exact σ.commutes r
        · rw [map_add, hz, hw]
        · rw [map_mul, hz, hw]
    have hxK : x ∈ K₁ := by
      rw [← IsGalois.fixedField_fixingSubgroup K₁, IntermediateField.mem_fixedField_iff, hSK₁]
      intro f hf
      exact hx ⟨f, hf⟩
    have hK₁le : K₁ ≤ (IsScalarTower.toAlgHom ℚ C L).fieldRange := by
      rw [hK₁, IntermediateField.adjoin_simple_le_iff]
      exact AlgHom.mem_fieldRange.mpr ⟨IsCyclotomicExtension.zeta p ℚ C, rfl⟩
    obtain ⟨c, hc⟩ := AlgHom.mem_fieldRange.mp (hK₁le hxK)
    exact ⟨c, hc⟩⟩

omit [NumberField L] [Algebra (CyclotomicField p ℚ) L] [IsGalois ℚ L] in

private theorem liesOver_span_of_mem (Q : Ideal (𝓞 L)) [Q.IsPrime] (hQ : (p : 𝓞 L) ∈ Q) :
    Q.LiesOver (Ideal.span {(p : ℤ)}) := by
  refine ⟨?_⟩
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible
      (Nat.prime_iff_prime_int.mp hp.1).irreducible
  refine hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_
  rw [Ideal.span_singleton_le_iff_mem]
  show algebraMap ℤ (𝓞 L) (p : ℤ) ∈ Q
  simpa using hQ

private theorem smul_ne_of_mem_stabZeta (hp2 : p ≠ 2)
    (hIS : ∀ Q : Ideal (𝓞 L), Q.IsMaximal → Q.inertia (L ≃ₐ[ℚ] L) ⊓ stabZeta p L = ⊥)
    (hC : ∀ τ : L ≃ₐ[ℚ] L, (∀ σ ∈ stabZeta p L, τ * σ = σ * τ) → τ ∈ stabZeta p L)
    (hcard : Nat.card (stabZeta p L) = p)
    (Q : Ideal (𝓞 L)) [hQm : Q.IsMaximal] (hQ : (p : 𝓞 L) ∈ Q)
    {σ : L ≃ₐ[ℚ] L} (hσS : σ ∈ stabZeta p L) (hσQ : σ • Q = Q) : σ = 1 := by
  classical
  by_contra hσ1
  set S := stabZeta p L with hSdef
  set D : Subgroup (L ≃ₐ[ℚ] L) := MulAction.stabilizer (L ≃ₐ[ℚ] L) Q with hDdef
  set I : Subgroup (L ≃ₐ[ℚ] L) := Q.inertia (L ≃ₐ[ℚ] L) with hIdef

  have hSD : S ≤ D := by
    haveI : Fact (Nat.card S).Prime := ⟨hcard.symm ▸ hp.1⟩
    rcases (D.subgroupOf S).eq_bot_or_eq_top_of_prime_card with h | h
    · exfalso
      have hmem : (⟨σ, hσS⟩ : S) ∈ D.subgroupOf S := Subgroup.mem_subgroupOf.mpr hσQ
      rw [h, Subgroup.mem_bot, Subgroup.mk_eq_one] at hmem
      exact hσ1 hmem
    · intro τ hτ
      have : (⟨τ, hτ⟩ : S) ∈ D.subgroupOf S := by rw [h]; trivial
      exact Subgroup.mem_subgroupOf.mp this
  have hID : I ≤ D := Ideal.inertia_le_stabilizer Q
  have hIn : (I.subgroupOf D).Normal := by
    rw [hIdef, hDdef, Ideal.inertia, AddSubgroup.subgroupOf_inertia]; infer_instance
  have hIbot : I = ⊥ :=
    eq_bot_of_normal_of_disjoint_of_centralizer_le hID hSD hIn (stabZeta_normal p L) (hIS Q hQm) hC

  set pZ : Ideal ℤ := Ideal.span {(p : ℤ)} with hpZ
  haveI hQover : Q.LiesOver pZ := liesOver_span_of_mem p L Q hQ
  have hpZbot : pZ ≠ ⊥ := by
    rw [hpZ, Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hp.1.ne_zero
  haveI hpZmax : pZ.IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp.1).irreducible
  have hQbot : Q ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hQm
    (NumberField.RingOfIntegers.not_isField L)

  letI : Field (ℤ ⧸ pZ) := Ideal.Quotient.field pZ
  letI : Field (𝓞 L ⧸ Q) := Ideal.Quotient.field Q
  haveI : Finite (ℤ ⧸ pZ) := Ideal.finiteQuotientOfFreeOfNeBot pZ hpZbot
  haveI : Finite (𝓞 L ⧸ Q) := Ideal.finiteQuotientOfFreeOfNeBot Q hQbot
  haveI : Module.Finite (ℤ ⧸ pZ) (𝓞 L ⧸ Q) := Module.Finite.of_finite
  haveI : Algebra.IsAlgebraic (ℤ ⧸ pZ) (𝓞 L ⧸ Q) := Algebra.IsAlgebraic.of_finite _ _
  haveI : Algebra.IsSeparable (ℤ ⧸ pZ) (𝓞 L ⧸ Q) := inferInstance
  have hcardI : Nat.card I = Ideal.ramificationIdx' pZ Q := by
    rw [hIdef, Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[ℚ] L) pZ Q,
      Ideal.ramificationIdxIn_eq_ramificationIdx pZ Q (L ≃ₐ[ℚ] L), Ideal.ramificationIdx'_eq_ramificationIdx _ _ hpZbot]

  set 𝔭 : Ideal (𝓞 C) := Q.under (𝓞 C) with h𝔭def
  haveI : Q.LiesOver 𝔭 := ⟨rfl⟩
  haveI : 𝔭.LiesOver pZ := ⟨by rw [h𝔭def, Ideal.under_under]; exact Q.over_def pZ⟩
  have h𝔭bot : 𝔭 ≠ ⊥ := fun h => hQbot (Ideal.eq_bot_of_comap_eq_bot h)
  have htower : Ideal.ramificationIdx' pZ Q =
      Ideal.ramificationIdx' pZ 𝔭 * Ideal.ramificationIdx' 𝔭 Q :=
    Ideal.ramificationIdx_algebra_tower' pZ 𝔭 Q
  have he𝔭 : Ideal.ramificationIdx' pZ 𝔭 = p - 1 := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ hpZbot]
    exact IsCyclotomicExtension.Rat.ramificationIdx_eq_of_prime p C 𝔭
  have heQ : Ideal.ramificationIdx' 𝔭 Q ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver Q h𝔭bot
  have h2 : 2 ≤ Nat.card I := by
    rw [hcardI, htower, he𝔭]
    have : 2 ≤ p - 1 := by
      have := hp.1.two_le
      omega
    calc 2 ≤ (p - 1) * 1 := by omega
      _ ≤ (p - 1) * Ideal.ramificationIdx' 𝔭 Q := Nat.mul_le_mul_left _ (Nat.pos_of_ne_zero heQ)
  rw [hIbot, Subgroup.card_bot] at h2
  omega

private theorem ramificationIdx_under_eq_one
    (hIS : ∀ Q : Ideal (𝓞 L), Q.IsMaximal → Q.inertia (L ≃ₐ[ℚ] L) ⊓ stabZeta p L = ⊥)
    (Q : Ideal (𝓞 L)) [hQm : Q.IsMaximal] :
    Ideal.ramificationIdx' (Q.under (𝓞 C)) Q = 1 := by
  classical
  have hQbot : Q ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hQm
    (NumberField.RingOfIntegers.not_isField L)
  set 𝔭 : Ideal (𝓞 C) := Q.under (𝓞 C) with h𝔭def
  haveI : Q.LiesOver 𝔭 := ⟨rfl⟩
  have h𝔭bot : 𝔭 ≠ ⊥ := fun h => hQbot (Ideal.eq_bot_of_comap_eq_bot h)
  haveI h𝔭max : 𝔭.IsMaximal := Ideal.IsPrime.isMaximal inferInstance h𝔭bot
  letI : Field (𝓞 C ⧸ 𝔭) := Ideal.Quotient.field 𝔭
  letI : Field (𝓞 L ⧸ Q) := Ideal.Quotient.field Q
  haveI : Finite (𝓞 C ⧸ 𝔭) := Ideal.finiteQuotientOfFreeOfNeBot 𝔭 h𝔭bot
  haveI : Finite (𝓞 L ⧸ Q) := Ideal.finiteQuotientOfFreeOfNeBot Q hQbot
  haveI : Module.Finite (𝓞 C ⧸ 𝔭) (𝓞 L ⧸ Q) := Module.Finite.of_finite
  haveI : Algebra.IsAlgebraic (𝓞 C ⧸ 𝔭) (𝓞 L ⧸ Q) := Algebra.IsAlgebraic.of_finite _ _
  haveI : Algebra.IsSeparable (𝓞 C ⧸ 𝔭) (𝓞 L ⧸ Q) := inferInstance
  haveI hGSO : IsGaloisGroup (stabZeta p L) (𝓞 C) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing (stabZeta p L) (𝓞 C) (𝓞 L) C L
  have h1 : Nat.card (Q.inertia (stabZeta p L)) = Ideal.ramificationIdx' 𝔭 Q := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := stabZeta p L) 𝔭 Q,
      Ideal.ramificationIdxIn_eq_ramificationIdx 𝔭 Q (stabZeta p L), Ideal.ramificationIdx'_eq_ramificationIdx _ _ h𝔭bot]
  have h2 : Q.inertia (stabZeta p L) = ⊥ := by
    have h : Q.inertia (stabZeta p L) = (Q.inertia (L ≃ₐ[ℚ] L)).subgroupOf (stabZeta p L) :=
      (AddSubgroup.subgroupOf_inertia _ (stabZeta p L)).symm
    rw [h, Subgroup.subgroupOf_eq_bot, disjoint_iff]
    exact hIS Q hQm
  rw [← h1, h2, Subgroup.card_bot]

private theorem inertiaDeg_under_eq_one (hp2 : p ≠ 2)
    (hIS : ∀ Q : Ideal (𝓞 L), Q.IsMaximal → Q.inertia (L ≃ₐ[ℚ] L) ⊓ stabZeta p L = ⊥)
    (hC : ∀ τ : L ≃ₐ[ℚ] L, (∀ σ ∈ stabZeta p L, τ * σ = σ * τ) → τ ∈ stabZeta p L)
    (hcard : Nat.card (stabZeta p L) = p)
    (Q : Ideal (𝓞 L)) [hQm : Q.IsMaximal] (hQ : (p : 𝓞 L) ∈ Q) :
    Ideal.inertiaDeg' (Q.under (𝓞 C)) Q = 1 := by
  classical
  have hQbot : Q ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hQm
    (NumberField.RingOfIntegers.not_isField L)
  set 𝔭 : Ideal (𝓞 C) := Q.under (𝓞 C) with h𝔭def
  haveI : Q.LiesOver 𝔭 := ⟨rfl⟩
  have h𝔭bot : 𝔭 ≠ ⊥ := fun h => hQbot (Ideal.eq_bot_of_comap_eq_bot h)
  haveI h𝔭max : 𝔭.IsMaximal := Ideal.IsPrime.isMaximal inferInstance h𝔭bot
  letI : Field (𝓞 C ⧸ 𝔭) := Ideal.Quotient.field 𝔭
  letI : Field (𝓞 L ⧸ Q) := Ideal.Quotient.field Q
  haveI : Finite (𝓞 C ⧸ 𝔭) := Ideal.finiteQuotientOfFreeOfNeBot 𝔭 h𝔭bot
  haveI : Finite (𝓞 L ⧸ Q) := Ideal.finiteQuotientOfFreeOfNeBot Q hQbot
  haveI : Module.Finite (𝓞 C ⧸ 𝔭) (𝓞 L ⧸ Q) := Module.Finite.of_finite
  haveI : Algebra.IsAlgebraic (𝓞 C ⧸ 𝔭) (𝓞 L ⧸ Q) := Algebra.IsAlgebraic.of_finite _ _
  haveI : Algebra.IsSeparable (𝓞 C ⧸ 𝔭) (𝓞 L ⧸ Q) := inferInstance
  haveI hGSO : IsGaloisGroup (stabZeta p L) (𝓞 C) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing (stabZeta p L) (𝓞 C) (𝓞 L) C L
  have key := Ideal.card_stabilizer_eq_card_inertia_mul_finrank (G := stabZeta p L) 𝔭 Q

  rw [card_stabilizer_eq_one_of] at key
  · rw [Ideal.inertiaDeg'_eq_inertiaDeg]
    exact Nat.eq_one_of_mul_eq_one_left key.symm
  · intro s hs
    exact Subtype.ext (smul_ne_of_mem_stabZeta p L hp2 hIS hC hcard Q hQ s.2 hs)

end Cyclo
p2m_reactivate "P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation"

section Tame

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

open UniqueFactorizationMonoid _root_.IsDedekindDomain _root_.Ideal.IsDedekindDomain in

private theorem dvd_count_normalizedFactors_span [DecidableEq (Ideal (𝓞 K))]
    (b : 𝓞 K) (hb : b ≠ 0) (β : 𝓞 L) (n : ℕ) (hn : n ≠ 0)
    (hβ : β ^ n = algebraMap (𝓞 K) (𝓞 L) b)
    (he : ∀ Q : Ideal (𝓞 L), Q.IsMaximal → Ideal.ramificationIdx' (Q.under (𝓞 K)) Q = 1)
    (𝔮 : HeightOneSpectrum (𝓞 K)) :
    n ∣ Multiset.count 𝔮.asIdeal (normalizedFactors (Ideal.span {b})) := by
  classical
  haveI h𝔮max : 𝔮.asIdeal.IsMaximal := 𝔮.isPrime.isMaximal 𝔮.ne_bot
  obtain ⟨Q, hQm, hQ𝔮⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) 𝔮.asIdeal
  haveI := hQm
  haveI := hQ𝔮
  have hQbot : Q ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hQm
    (NumberField.RingOfIntegers.not_isField L)
  have hQirr : Irreducible Q := (Ideal.prime_of_isPrime hQbot hQm.isPrime).irreducible
  have hIbot : Ideal.span {b} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  have he1 : Ideal.ramificationIdx' 𝔮.asIdeal Q = 1 := by
    have h := he Q hQm
    rwa [← Ideal.over_def Q 𝔮.asIdeal] at h
  have key := Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx_mul
    (S := 𝓞 L) hIbot 𝔮.irreducible hQirr hQbot
  rw [he1, Nat.cast_one, one_mul, Ideal.map_span, Set.image_singleton, ← hβ,
    ← Ideal.span_singleton_pow,
    emultiplicity_pow (Ideal.prime_of_isPrime hQbot hQm.isPrime),
    emultiplicity_eq_count_normalizedFactors 𝔮.irreducible hIbot, normalize_eq] at key

  have hfin : emultiplicity Q (Ideal.span {β}) ≠ ⊤ := by
    intro htop
    rw [htop, ENat.mul_top (by exact_mod_cast hn)] at key
    exact ENat.coe_ne_top _ key.symm
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hfin
  rw [← hm, ← Nat.cast_mul, Nat.cast_inj] at key
  exact ⟨m, key.symm⟩

end Tame
p2m_reactivate "P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation"

end ExtCitation.KumFinite
p2m_reactivate "P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation.KumFinite"
p2m_reactivate "P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation"

end PART_R3_TBC_aux1
p2m_reactivate "P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation.KumFinite"

section PART_R3_TA_aux1

set_option autoImplicit false

namespace ExtCitation
p2m_export "ExtCitation" "ExtVanishingCts card_rootsOfUnity_eq_self cycloExp IsAdmissibleExtension SplitsGlobally Cyclotomic.instIsCycExt"
namespace KumLift
p2m_open "ExtCitation"

p2m_open_scoped "NumberField P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.NumberField"
open ValuationSubring

local notation "Qbar" => AlgebraicClosure ℚ

private theorem inertia_inf_stabilizer_eq_bot
    (L : IntermediateField ℚ Qbar) [FiniteDimensional ℚ L] [IsGalois ℚ L] (ζ : L)
    (hI : ∀ q : ℕ, q.Prime → ∀ A : ValuationSubring Qbar, A.LiesOverPrime q →
      A.inertiaSubgroupIn ℚ ⊓ MulAction.stabilizer (Qbar ≃ₐ[ℚ] Qbar) (ζ : Qbar) ≤
        L.fixingSubgroup)
    (Q : Ideal (𝓞 L)) (hQ : Q.IsMaximal) :
    Q.inertia (L ≃ₐ[ℚ] L) ⊓ MulAction.stabilizer (L ≃ₐ[ℚ] L) ζ = ⊥ := by
  classical
  haveI := hQ
  haveI : NumberField L := NumberField.mk
  rw [eq_bot_iff]
  rintro τ ⟨hτI, hτζ⟩
  rw [Subgroup.mem_bot]

  have hQbot : Q ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hQ
    (NumberField.RingOfIntegers.not_isField L)
  letI : Field (𝓞 L ⧸ Q) := Ideal.Quotient.field Q
  haveI : Finite (𝓞 L ⧸ Q) := Ideal.finiteQuotientOfFreeOfNeBot Q hQbot
  obtain ⟨q, hqchar⟩ := CharP.exists (𝓞 L ⧸ Q)
  haveI := hqchar
  have hq : q.Prime := CharP.char_is_prime (𝓞 L ⧸ Q) q
  have hqQ : (q : 𝓞 L) ∈ Q := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact CharP.cast_eq_zero (𝓞 L ⧸ Q) q

  obtain ⟨σ, hστ, 𝔔, h𝔔max, hq𝔔, hσ𝔔⟩ :=
    NumberField.exists_lift_mem_inertia_integralClosure L Q hqQ τ hτI
  haveI := h𝔔max
  obtain ⟨A, hA, hσA⟩ :=
    ValuationSubring.exists_liesOverPrime_mem_inertiaSubgroupIn 𝔔 hq hq𝔔 σ hσ𝔔

  have hres : ∀ x : L, σ (x : Qbar) = ((τ x : L) : Qbar) := fun x => by
    have hc : ((AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Qbar) L σ x : L) : Qbar) = σ x :=
      σ.restrictNormal_commutes L x
    rw [← hc, hστ]

  have hσζ : σ (ζ : Qbar) = ζ := by
    rw [hres ζ]
    have : τ ζ = ζ := hτζ
    rw [this]
  have hσL : σ ∈ L.fixingSubgroup := hI q hq A hA ⟨hσA, hσζ⟩

  ext x
  have hx : σ (x : Qbar) = x := (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσL x x.2
  rw [hres x] at hx
  rw [AlgEquiv.one_apply]
  exact_mod_cast hx

end ExtCitation.KumLift
p2m_reactivate "P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation.KumFinite"
p2m_reactivate "P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation.KumFinite"

end PART_R3_TA_aux1
p2m_reactivate "P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation.KumFinite"

section PART_R3_TD_LOCROOT_aux1

set_option autoImplicit false

namespace NumberField
p2m_export "NumberField" "FinitePlace mk place HeightOneSpectrum.one_lt_absNorm RingOfIntegers.not_isField RingOfIntegers HeightOneSpectrum.absNorm_ne_zero FinitePlace.norm_embedding_int RingOfIntegers.map_mk HeightOneSpectrum.one_lt_absNorm_nnreal RingOfIntegers.coe_eq_algebraMap RingOfIntegers.ext RingOfIntegers.isIntegral_coe exists_lift_mem_inertia_integralClosure"
namespace LocRoot
p2m_open "NumberField"

p2m_open_scoped "NumberField P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.NumberField NNReal"
p2m_open "IsDedekindDomain NumberField.Ideal Filter Topology"

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (𝔭 : HeightOneSpectrum (𝓞 K)) (Q : Ideal (𝓞 L)) [hQm : Q.IsMaximal] [Q.LiesOver 𝔭.asIdeal]

private theorem comap_pow_le (he : Ideal.ramificationIdx' 𝔭.asIdeal Q = 1) (k : ℕ) :
    (Q ^ k).comap (algebraMap (𝓞 K) (𝓞 L)) ≤ 𝔭.asIdeal ^ k := by
  classical
  intro a ha
  rw [Ideal.mem_comap] at ha
  by_cases ha0 : a = 0
  · rw [ha0]; exact Submodule.zero_mem _
  have hQbot : Q ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hQm
    (NumberField.RingOfIntegers.not_isField L)
  have hQirr : Irreducible Q := (Ideal.prime_of_isPrime hQbot hQm.isPrime).irreducible
  have hIbot : Ideal.span {a} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  have key := Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx_mul
    (S := 𝓞 L) hIbot 𝔭.irreducible hQirr hQbot
  rw [he, Nat.cast_one, one_mul, Ideal.map_span, Set.image_singleton] at key
  have h1 : (k : ℕ∞) ≤ emultiplicity Q (Ideal.span {algebraMap (𝓞 K) (𝓞 L) a}) := by
    rw [← pow_dvd_iff_le_emultiplicity, Ideal.dvd_span_singleton]
    exact ha
  rw [key, ← pow_dvd_iff_le_emultiplicity, Ideal.dvd_span_singleton] at h1
  exact h1

omit hQm in

private theorem card_quot_pow_eq (hf : Ideal.inertiaDeg' 𝔭.asIdeal Q = 1) (k : ℕ) :
    Nat.card (𝓞 L ⧸ Q ^ k) = Nat.card (𝓞 K ⧸ 𝔭.asIdeal ^ k) := by
  have h := Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver Q 𝔭.asIdeal 𝔭.isPrime 𝔭.ne_bot
  rw [hf, pow_one] at h
  have e1 : Ideal.absNorm (Q ^ k) = Ideal.absNorm (𝔭.asIdeal ^ k) := by rw [map_pow, map_pow, h]
  simpa [Ideal.absNorm_apply, Submodule.cardQuot_apply] using e1

private theorem exists_sub_mem_pow (he : Ideal.ramificationIdx' 𝔭.asIdeal Q = 1)
    (hf : Ideal.inertiaDeg' 𝔭.asIdeal Q = 1) (k : ℕ) (z : 𝓞 L) :
    ∃ y : 𝓞 K, algebraMap (𝓞 K) (𝓞 L) y - z ∈ Q ^ k := by
  classical
  have hQbot : Q ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hQm
    (NumberField.RingOfIntegers.not_isField L)
  have hP : Q.comap (algebraMap (𝓞 K) (𝓞 L)) = 𝔭.asIdeal := (Ideal.over_def Q 𝔭.asIdeal).symm
  have hle : 𝔭.asIdeal ^ k ≤ (Q ^ k).comap (algebraMap (𝓞 K) (𝓞 L)) := by
    rw [← hP]
    exact Ideal.le_comap_pow _ k
  have hinj : Function.Injective (Ideal.quotientMap (Q ^ k) (algebraMap (𝓞 K) (𝓞 L)) hle) :=
    Ideal.quotientMap_injective' (comap_pow_le 𝔭 Q he k)
  haveI : Finite (𝓞 L ⧸ Q ^ k) := Ideal.finiteQuotientOfFreeOfNeBot (Q ^ k) (pow_ne_zero k hQbot)
  haveI : Finite (𝓞 K ⧸ 𝔭.asIdeal ^ k) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (pow_ne_zero k 𝔭.ne_bot)
  obtain ⟨e⟩ := Finite.card_eq.mp (card_quot_pow_eq 𝔭 Q hf k).symm
  have hsurj := (Finite.injective_iff_surjective_of_equiv e).mp hinj
  obtain ⟨yq, hyq⟩ := hsurj (Ideal.Quotient.mk (Q ^ k) z)
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective yq
  refine ⟨y, ?_⟩
  rw [Ideal.quotientMap_mk, Ideal.Quotient.eq] at hyq
  exact hyq

omit hQm in

private theorem norm_algebraMap_le_of_mem_pow {a : 𝓞 K} {k : ℕ} (ha : a ∈ 𝔭.asIdeal ^ k) :
    ‖algebraMap (𝓞 K) (𝔭.adicCompletion K) a‖ ≤ ((Ideal.absNorm 𝔭.asIdeal : ℝ)⁻¹) ^ k := by
  set N : ℝ≥0 := (Ideal.absNorm 𝔭.asIdeal : ℝ≥0) with hNdef
  have hN : 1 < N := NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal 𝔭
  have hv : 𝔭.intValuation a ≤ WithZero.exp (-(k : ℤ)) :=
    (𝔭.intValuation_le_pow_iff_mem a k).mpr ha

  have h1 : ‖algebraMap (𝓞 K) (𝔭.adicCompletion K) a‖ =
      WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero 𝔭)
        (𝔭.intValuation a) := by
    rw [IsScalarTower.algebraMap_apply (𝓞 K) K (𝔭.adicCompletion K)]
    exact NumberField.FinitePlace.norm_embedding_int K 𝔭 a
  have h2 : WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero 𝔭)
      (𝔭.intValuation a) ≤ WithZeroMulInt.toNNReal
        (NumberField.HeightOneSpectrum.absNorm_ne_zero 𝔭) (WithZero.exp (-(k : ℤ))) :=
    (WithZeroMulInt.toNNReal_strictMono hN).monotone hv
  have h3 : WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero 𝔭)
      (WithZero.exp (-(k : ℤ))) = (N ^ k)⁻¹ := by
    rw [WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
    have hu : WithZero.unzero (WithZero.exp_ne_zero (a := -(k : ℤ))) =
        Multiplicative.ofAdd (-(k : ℤ)) := by
      rw [← WithZero.coe_inj, WithZero.coe_unzero]
      rfl
    rw [hu, toAdd_ofAdd, zpow_neg, zpow_natCast]
  rw [h3] at h2
  rw [h1, inv_pow]
  have h4 : (((N ^ k)⁻¹ : ℝ≥0) : ℝ) = (((Ideal.absNorm 𝔭.asIdeal : ℝ)) ^ k)⁻¹ := by
    rw [hNdef]
    push_cast
    rfl
  rw [← h4]
  exact_mod_cast h2

private theorem exists_pow_eq (he : Ideal.ramificationIdx' 𝔭.asIdeal Q = 1)
    (hf : Ideal.inertiaDeg' 𝔭.asIdeal Q = 1)
    (b : 𝓞 K) (β : 𝓞 L) (n : ℕ) (hβ : β ^ n = algebraMap (𝓞 K) (𝓞 L) b) :
    ∃ x : 𝔭.adicCompletion K, x ^ n = algebraMap (𝓞 K) (𝔭.adicCompletion K) b := by
  classical

  choose y hy using fun k => exists_sub_mem_pow 𝔭 Q he hf k β
  have hb_k : ∀ k, y k ^ n - b ∈ 𝔭.asIdeal ^ k := fun k => by
    apply comap_pow_le 𝔭 Q he k
    rw [Ideal.mem_comap, map_sub, map_pow, ← hβ]
    exact Ideal.mem_of_dvd (hab := sub_dvd_pow_sub_pow _ _ n) (ha := hy k)
  have hdiff : ∀ k, y (k + 1) - y k ∈ 𝔭.asIdeal ^ k := fun k => by
    apply comap_pow_le 𝔭 Q he k
    rw [Ideal.mem_comap, map_sub]
    have h1 : algebraMap (𝓞 K) (𝓞 L) (y (k + 1)) - β ∈ Q ^ k :=
      Ideal.pow_le_pow_right (Nat.le_succ k) (hy (k + 1))
    have h2 := sub_mem h1 (hy k)
    rwa [sub_sub_sub_cancel_right] at h2

  set Kp := 𝔭.adicCompletion K
  set r : ℝ := ((Ideal.absNorm 𝔭.asIdeal : ℝ))⁻¹ with hr
  have hN1 : 1 < (Ideal.absNorm 𝔭.asIdeal : ℝ) := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm 𝔭
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hr1 : r < 1 := by rw [hr]; exact inv_lt_one_of_one_lt₀ hN1
  set s : ℕ → Kp := fun k => algebraMap (𝓞 K) Kp (y k) with hs
  have hcauchy : CauchySeq s := by
    refine cauchySeq_of_le_geometric r 1 hr1 fun k => ?_
    rw [one_mul, dist_eq_norm, ← norm_neg, neg_sub, hs]
    simp only
    rw [← map_sub]
    exact norm_algebraMap_le_of_mem_pow 𝔭 (hdiff k)
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨x, ?_⟩
  have h1 : Tendsto (fun k => s k ^ n) atTop (𝓝 (x ^ n)) := hx.pow n
  have h2 : Tendsto (fun k => s k ^ n) atTop (𝓝 (algebraMap (𝓞 K) Kp b)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_)
      (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1)
    rw [hs]
    simp only
    rw [← map_pow, ← map_sub]
    exact norm_algebraMap_le_of_mem_pow 𝔭 (hb_k k)
  exact tendsto_nhds_unique h1 h2

end NumberField.LocRoot
p2m_reactivate "P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation.KumFinite"
p2m_reactivate "P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation.KumFinite"

namespace NumberField p2m_export "NumberField" "FinitePlace mk place HeightOneSpectrum.one_lt_absNorm RingOfIntegers.not_isField RingOfIntegers HeightOneSpectrum.absNorm_ne_zero FinitePlace.norm_embedding_int RingOfIntegers.map_mk HeightOneSpectrum.one_lt_absNorm_nnreal RingOfIntegers.coe_eq_algebraMap RingOfIntegers.ext RingOfIntegers.isIntegral_coe exists_lift_mem_inertia_integralClosure" end NumberField
p2m_open_scoped "NumberField" in

private theorem NumberField.exists_pow_eq_algebraMap_adicCompletion_of_ramificationIdx_eq_one_of_inertiaDeg_eq_one
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : Ideal (NumberField.RingOfIntegers L)) [Q.IsMaximal] [Q.LiesOver 𝔭.asIdeal]
    (he : Ideal.ramificationIdx' 𝔭.asIdeal Q = 1) (hf : Ideal.inertiaDeg' 𝔭.asIdeal Q = 1)
    (b : NumberField.RingOfIntegers K) (β : NumberField.RingOfIntegers L) (n : ℕ)
    (hβ : β ^ n = algebraMap (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) b) :
    ∃ x : 𝔭.adicCompletion K,
      x ^ n = algebraMap (NumberField.RingOfIntegers K) (𝔭.adicCompletion K) b :=
  NumberField.LocRoot.exists_pow_eq 𝔭 Q he hf b β n hβ

end PART_R3_TD_LOCROOT_aux1
p2m_reactivate "P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation.KumFinite"

section PART_R3_TE_aux1

set_option autoImplicit false

namespace ExtCitation
p2m_export "ExtCitation" "ExtVanishingCts card_rootsOfUnity_eq_self cycloExp IsAdmissibleExtension SplitsGlobally Cyclotomic.instIsCycExt"
namespace KumTail
p2m_open "ExtCitation"

p2m_open "NumberField P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.NumberField IsDedekindDomain JacobiSumStickelberger Stickelberger ExtCitation.Cyclotomic"

variable (p : ℕ) [Fact p.Prime]

private theorem exists_unit_pow_eq {R F : Type*} [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] [IsIntegrallyClosed R] {n : ℕ} (hn : 0 < n) (u : Rˣ) (w : F)
    (hw : w ^ n = algebraMap R F u) : ∃ ε : Rˣ, ε ^ n = u ∧ algebraMap R F ε = w := by
  have hint : IsIntegral R (w ^ n) := by
    rw [hw]; exact isIntegral_algebraMap
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow hn hint
  have hyn : y ^ n = u := by
    apply IsFractionRing.injective R F
    rw [map_pow, hy, hw]
  have hyu : IsUnit y := (isUnit_pow_iff hn.ne').mp (hyn ▸ Units.isUnit u)
  refine ⟨hyu.unit, ?_, by simpa using hy⟩
  ext; simpa using hyn

local notation "K" => CyclotomicField p ℚ

private theorem units_tail
    (unitsGalAction' : (ZMod p)ˣ →* Module.End (ZMod p)
      (ModP p (Additive (𝓞 (CyclotomicField p ℚ))ˣ)))
    (hρ : ∀ d u, unitsGalAction' d
        (ModP.proj p _ (Additive.ofMul u)) =
      ModP.proj p _ (Additive.ofMul
        (Units.mapEquiv (clRingAction p (CyclotomicField p ℚ) d).toMulEquiv u)))
    (hUnitsB2 : ∀ u : (𝓞 (CyclotomicField p ℚ))ˣ,
      IsOmegaEigenvector unitsGalAction' 2
        (ModP.proj p (Additive (𝓞 (CyclotomicField p ℚ))ˣ) (Additive.ofMul u)) →
      (∀ 𝔭 : HeightOneSpectrum (𝓞 (CyclotomicField p ℚ)),
        (p : 𝓞 (CyclotomicField p ℚ)) ∈ 𝔭.asIdeal →
        ∃ v : (𝔭.adicCompletion (CyclotomicField p ℚ))ˣ,
          v ^ p = (Units.map (algebraMap (𝓞 (CyclotomicField p ℚ))
            (𝔭.adicCompletion (CyclotomicField p ℚ))).toMonoidHom) u) →
      ModP.proj p (Additive (𝓞 (CyclotomicField p ℚ))ˣ) (Additive.ofMul u) = 0)
    (b γ : 𝓞 K) (u : (𝓞 K)ˣ) (hγ : γ ≠ 0) (hb : b = u * γ ^ p)
    (he2 : ∀ d : (ZMod p)ˣ, ∃ n : ℕ, (n : ZMod p) = (d : ZMod p) ^ 2 ∧
      ∃ c₁ c₂ : 𝓞 K, c₂ ≠ 0 ∧
        clRingAction p K d b * c₂ ^ p = b ^ n * c₁ ^ p)
    (hloc : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ 𝔭.asIdeal →
      ∃ v : 𝔭.adicCompletion K, v ^ p = algebraMap (𝓞 K) (𝔭.adicCompletion K) b) :
    ∃ ε : (𝓞 K)ˣ, u = ε ^ p := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  haveI : NeZero p := ⟨hp0.ne'⟩
  have hinjK : Function.Injective (algebraMap (𝓞 K) K) := IsFractionRing.injective (𝓞 K) K

  have heig : IsOmegaEigenvector unitsGalAction' 2
      (ModP.proj p (Additive (𝓞 K)ˣ) (Additive.ofMul u)) := by
    intro d
    obtain ⟨n, hn, c₁, c₂, hc₂, hrel⟩ := he2 d
    set σ : 𝓞 K ≃+* 𝓞 K := clRingAction p K d with hσ

    have hσγ : σ γ ≠ 0 := σ.map_ne_zero_iff.mpr hγ
    have hden : (algebraMap (𝓞 K) K (σ γ * c₂)) ≠ 0 :=
      (map_ne_zero_iff _ hinjK).mpr (mul_ne_zero hσγ hc₂)
    have hun : algebraMap (𝓞 K) K ((u : 𝓞 K) ^ n) ≠ 0 :=
      (map_ne_zero_iff _ hinjK).mpr (pow_ne_zero _ (Units.ne_zero u))

    set w : K := algebraMap (𝓞 K) K (γ ^ n * c₁) / algebraMap (𝓞 K) K (σ γ * c₂) with hw
    have hrelK : algebraMap (𝓞 K) K (σ (u : 𝓞 K)) * (algebraMap (𝓞 K) K (σ γ * c₂)) ^ p =
        algebraMap (𝓞 K) K ((u : 𝓞 K) ^ n) * (algebraMap (𝓞 K) K (γ ^ n * c₁)) ^ p := by
      have := congrArg (algebraMap (𝓞 K) K) hrel
      simp only [hb, map_mul, map_pow] at this
      simp only [map_mul, map_pow]
      linear_combination this

    set ε : (𝓞 K)ˣ := Units.mapEquiv σ.toMulEquiv u * (u ^ n)⁻¹ with hε
    have hεval : (ε : 𝓞 K) * (u : 𝓞 K) ^ n = σ (u : 𝓞 K) := by
      have h1 : ε * u ^ n = Units.mapEquiv σ.toMulEquiv u := by rw [hε, inv_mul_cancel_right]
      have h2 := congrArg Units.val h1
      simpa [Units.coe_mapEquiv] using h2
    have hwp : w ^ p = algebraMap (𝓞 K) K (ε : 𝓞 K) := by
      have key : algebraMap (𝓞 K) K ((u : 𝓞 K) ^ n) *
          (algebraMap (𝓞 K) K (ε : 𝓞 K) * (algebraMap (𝓞 K) K (σ γ * c₂)) ^ p) =
          algebraMap (𝓞 K) K ((u : 𝓞 K) ^ n) * (algebraMap (𝓞 K) K (γ ^ n * c₁)) ^ p := by
        calc algebraMap (𝓞 K) K ((u : 𝓞 K) ^ n) *
              (algebraMap (𝓞 K) K (ε : 𝓞 K) * (algebraMap (𝓞 K) K (σ γ * c₂)) ^ p)
            = algebraMap (𝓞 K) K ((ε : 𝓞 K) * (u : 𝓞 K) ^ n) *
                (algebraMap (𝓞 K) K (σ γ * c₂)) ^ p := by simp only [map_mul]; ring
          _ = algebraMap (𝓞 K) K (σ (u : 𝓞 K)) * (algebraMap (𝓞 K) K (σ γ * c₂)) ^ p := by
                rw [hεval]
          _ = _ := hrelK
      have key' := mul_left_cancel₀ hun key
      rw [hw, div_pow, div_eq_iff (pow_ne_zero _ hden)]
      exact key'.symm
    obtain ⟨w₀, hw₀, -⟩ := exists_unit_pow_eq hp0 ε w hwp

    have hunits : Units.mapEquiv σ.toMulEquiv u = u ^ n * w₀ ^ p := by
      rw [hw₀, hε, mul_comm, inv_mul_cancel_right]
    have hz : ModP.proj p (Additive (𝓞 K)ˣ) (p • Additive.ofMul w₀) = 0 :=
      (ModP.proj_eq_zero_iff p (Additive (𝓞 K)ˣ)).mpr ⟨Additive.ofMul w₀, rfl⟩
    rw [hρ d u, hunits, ofMul_mul, ofMul_pow, ofMul_pow, map_add, hz, add_zero, map_nsmul,
      ← hn, Nat.cast_smul_eq_nsmul]

  have hloc' : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ 𝔭.asIdeal →
      ∃ v : (𝔭.adicCompletion K)ˣ,
        v ^ p = (Units.map (algebraMap (𝓞 K) (𝔭.adicCompletion K)).toMonoidHom) u := by
    intro 𝔭 h𝔭
    obtain ⟨v, hv⟩ := hloc 𝔭 h𝔭
    have hinj : Function.Injective (algebraMap (𝓞 K) (𝔭.adicCompletion K)) := by
      have h1 : algebraMap (𝓞 K) (𝔭.adicCompletion K) =
          (algebraMap K (𝔭.adicCompletion K)).comp (algebraMap (𝓞 K) K) :=
        RingHom.ext fun _ => rfl
      rw [h1, RingHom.coe_comp]
      exact (algebraMap K (𝔭.adicCompletion K)).injective.comp hinjK
    have hγ' : algebraMap (𝓞 K) (𝔭.adicCompletion K) γ ≠ 0 :=
      (map_ne_zero_iff _ hinj).mpr hγ
    have hu' : algebraMap (𝓞 K) (𝔭.adicCompletion K) u ≠ 0 :=
      (map_ne_zero_iff _ hinj).mpr (Units.ne_zero u)
    have hvγ : (v / (algebraMap (𝓞 K) (𝔭.adicCompletion K) γ)) ^ p =
        algebraMap (𝓞 K) (𝔭.adicCompletion K) u := by
      rw [div_pow, hv, hb, map_mul, map_pow, mul_div_assoc, div_self (pow_ne_zero _ hγ'),
        mul_one]
    have hv0 : v / (algebraMap (𝓞 K) (𝔭.adicCompletion K) γ) ≠ 0 := by
      intro h; rw [h, zero_pow hp0.ne'] at hvγ; exact hu' hvγ.symm
    refine ⟨Units.mk0 _ hv0, ?_⟩
    ext
    simp [Units.val_mk0, hvγ]

  have h0 := hUnitsB2 u heig hloc'
  obtain ⟨y, hy⟩ := (ModP.proj_eq_zero_iff p (Additive (𝓞 K)ˣ)).mp h0
  refine ⟨Additive.toMul y, ?_⟩
  have hy' := congrArg Additive.toMul hy
  rw [toMul_nsmul] at hy'
  simpa using hy'.symm

end ExtCitation.KumTail
p2m_reactivate "P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation.KumFinite"
p2m_reactivate "P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation.KumFinite"

end PART_R3_TE_aux1
p2m_reactivate "P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation.KumFinite"

section PART_R3_BRIDGE_aux1

namespace ExtCitation
p2m_export "ExtCitation" "ExtVanishingCts card_rootsOfUnity_eq_self cycloExp IsAdmissibleExtension SplitsGlobally Cyclotomic.instIsCycExt"
namespace KumBridge
p2m_open "ExtCitation"

p2m_open_scoped "NumberField P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.NumberField"
open IsDedekindDomain ValuationSubring

variable (p : ℕ) [hp : Fact p.Prime]

local notation "C" => CyclotomicField p ℚ
local notation "Qbar" => AlgebraicClosure ℚ

section

variable (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [IsGalois ℚ L]
  (ι : CyclotomicField p ℚ →ₐ[ℚ] L) (b : 𝓞 (CyclotomicField p ℚ)) (β : L)

omit [FiniteDimensional ℚ L] [IsGalois ℚ L] in

private theorem isIntegral_beta (hβ : β ^ p = ι b) : IsIntegral ℤ β := by
  refine IsIntegral.of_pow hp.1.pos ?_
  rw [hβ]
  exact map_isIntegral_int ι.toRingHom (NumberField.RingOfIntegers.isIntegral_coe b)

private noncomputable def betaInt (hβ : β ^ p = ι b) : 𝓞 L := ⟨β, isIntegral_beta p L ι b β hβ⟩

omit [FiniteDimensional ℚ L] [IsGalois ℚ L] in

private theorem betaInt_pow (hβ : β ^ p = ι b) :
    letI : Algebra C L := ι.toRingHom.toAlgebra
    betaInt p L ι b β hβ ^ p = algebraMap (𝓞 C) (𝓞 L) b := by
  letI : Algebra C L := ι.toRingHom.toAlgebra
  apply NumberField.RingOfIntegers.ext
  rw [NumberField.RingOfIntegers.coe_eq_algebraMap, NumberField.RingOfIntegers.coe_eq_algebraMap,
    map_pow, ← IsScalarTower.algebraMap_apply (𝓞 C) (𝓞 L) L b,
    IsScalarTower.algebraMap_apply (𝓞 C) C L b]
  show (algebraMap (𝓞 L) L ⟨β, isIntegral_beta p L ι b β hβ⟩) ^ p = algebraMap C L (b : C)
  rw [NumberField.RingOfIntegers.map_mk]
  exact hβ

variable (hI : ∀ q : ℕ, q.Prime → ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q →
      A.inertiaSubgroupIn ℚ ⊓ MulAction.stabilizer (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
        ((ι (IsCyclotomicExtension.zeta p ℚ (CyclotomicField p ℚ)) : L) : AlgebraicClosure ℚ) ≤
        L.fixingSubgroup)

include hI in

private theorem tame (hb : b ≠ 0) (hβ : β ^ p = ι b) [DecidableEq (Ideal (𝓞 (CyclotomicField p ℚ)))]
    (𝔮 : HeightOneSpectrum (𝓞 (CyclotomicField p ℚ))) :
    p ∣ Multiset.count 𝔮.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b})) := by
  letI : Algebra C L := ι.toRingHom.toAlgebra
  haveI : NumberField L := NumberField.mk

  have hIS' : ∀ Q : Ideal (𝓞 L), Q.IsMaximal →
      Q.inertia (L ≃ₐ[ℚ] L) ⊓ KumFinite.stabZeta p L = ⊥ :=
    fun Q hQ => KumLift.inertia_inf_stabilizer_eq_bot L _ hI Q hQ
  have he : ∀ Q : Ideal (𝓞 L), Q.IsMaximal → Ideal.ramificationIdx' (Q.under (𝓞 C)) Q = 1 :=
    fun Q hQ => by haveI := hQ; exact KumFinite.ramificationIdx_under_eq_one p L hIS' Q
  exact KumFinite.dvd_count_normalizedFactors_span b hb _ p hp.1.ne_zero
    (betaInt_pow p L ι b β hβ) he 𝔮

include hI in

private theorem loc (hp2 : p ≠ 2) (hβ : β ^ p = ι b)
    (hC : ∀ τ : L ≃ₐ[ℚ] L,
      (∀ σ ∈ MulAction.stabilizer (L ≃ₐ[ℚ] L) (ι (IsCyclotomicExtension.zeta p ℚ C)),
        τ * σ = σ * τ) →
      τ ∈ MulAction.stabilizer (L ≃ₐ[ℚ] L) (ι (IsCyclotomicExtension.zeta p ℚ C)))
    (hcard : Nat.card (MulAction.stabilizer (L ≃ₐ[ℚ] L)
      (ι (IsCyclotomicExtension.zeta p ℚ C))) = p)
    (𝔭 : HeightOneSpectrum (𝓞 (CyclotomicField p ℚ))) (h𝔭 : (p : 𝓞 C) ∈ 𝔭.asIdeal) :
    ∃ v : 𝔭.adicCompletion C, v ^ p = algebraMap (𝓞 C) (𝔭.adicCompletion C) b := by
  letI : Algebra C L := ι.toRingHom.toAlgebra
  haveI : NumberField L := NumberField.mk
  have hIS' : ∀ Q : Ideal (𝓞 L), Q.IsMaximal →
      Q.inertia (L ≃ₐ[ℚ] L) ⊓ KumFinite.stabZeta p L = ⊥ :=
    fun Q hQ => KumLift.inertia_inf_stabilizer_eq_bot L _ hI Q hQ
  have he : ∀ Q : Ideal (𝓞 L), Q.IsMaximal → Ideal.ramificationIdx' (Q.under (𝓞 C)) Q = 1 :=
    fun Q hQ => by haveI := hQ; exact KumFinite.ramificationIdx_under_eq_one p L hIS' Q
  haveI h𝔭max : 𝔭.asIdeal.IsMaximal := 𝔭.isPrime.isMaximal 𝔭.ne_bot
  obtain ⟨Q, hQm, hQover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) 𝔭.asIdeal
  haveI := hQm
  haveI := hQover
  have hpQ : (p : 𝓞 L) ∈ Q := by
    have h1 : algebraMap (𝓞 C) (𝓞 L) (p : 𝓞 C) ∈ Q := by
      rw [← Ideal.mem_comap]
      change (p : 𝓞 C) ∈ Q.under (𝓞 C)
      rw [← Ideal.over_def Q 𝔭.asIdeal]
      exact h𝔭
    simpa using h1
  have he1 : Ideal.ramificationIdx' 𝔭.asIdeal Q = 1 := by
    have h := he Q hQm
    rwa [← Ideal.over_def Q 𝔭.asIdeal] at h
  have hf1 : Ideal.inertiaDeg' 𝔭.asIdeal Q = 1 := by
    have h := KumFinite.inertiaDeg_under_eq_one p L hp2 hIS' hC hcard Q hpQ
    rwa [← Ideal.over_def Q 𝔭.asIdeal] at h
  exact NumberField.exists_pow_eq_algebraMap_adicCompletion_of_ramificationIdx_eq_one_of_inertiaDeg_eq_one
    𝔭 Q he1 hf1 b _ p (betaInt_pow p L ι b β hβ)

end
p2m_reactivate "P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation.KumFinite"

open _root_.NumberField _root_.P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.NumberField JacobiSumStickelberger in

private theorem he2_of_field (b : 𝓞 (CyclotomicField p ℚ)) (d : (ZMod p)ˣ) (n : ℕ)
    (γ : CyclotomicField p ℚ)
    (h : (cycloGalEquiv p (CyclotomicField p ℚ)).symm d (b : CyclotomicField p ℚ) =
      (b : CyclotomicField p ℚ) ^ n * γ ^ p) :
    ∃ c₁ c₂ : 𝓞 (CyclotomicField p ℚ), c₂ ≠ 0 ∧
      clRingAction p (CyclotomicField p ℚ) d b * c₂ ^ p = b ^ n * c₁ ^ p := by
  obtain ⟨c₁, c₂, hc₂, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 C) γ
  have hc₂' : c₂ ≠ 0 := nonZeroDivisors.ne_zero hc₂
  refine ⟨c₁, c₂, hc₂', ?_⟩
  have hinj : Function.Injective (algebraMap (𝓞 C) C) := IsFractionRing.injective (𝓞 C) C
  apply hinj

  have hσ : algebraMap (𝓞 C) C (clRingAction p C d b) =
      (cycloGalEquiv p C).symm d (algebraMap (𝓞 C) C b) := by
    simp [clRingAction, galRestrictionDatum_apply, algebraMap_galRestrict_apply]
  rw [RingOfIntegers.coe_eq_algebraMap] at h
  have hc₂K : algebraMap (𝓞 C) C c₂ ≠ 0 := (map_ne_zero_iff _ hinj).mpr hc₂'
  rw [map_mul, map_mul, map_pow, map_pow, map_pow, hσ, h, div_pow, mul_assoc,
    div_mul_cancel₀ _ (pow_ne_zero p hc₂K)]

end ExtCitation.KumBridge
p2m_reactivate "P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation.KumFinite"
p2m_reactivate "P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation.KumFinite"

end PART_R3_BRIDGE_aux1
p2m_reactivate "P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation.KumFinite"

section PART_R3_CASE2_aux1

namespace ExtCitation
p2m_export "ExtCitation" "ExtVanishingCts card_rootsOfUnity_eq_self cycloExp IsAdmissibleExtension SplitsGlobally Cyclotomic.instIsCycExt"
namespace KumBridge
p2m_open "ExtCitation"

p2m_open_scoped "NumberField P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.NumberField"
open IsDedekindDomain ValuationSubring JacobiSumStickelberger Stickelberger ExtCitation.Cyclotomic

variable (p : ℕ) [hp : Fact p.Prime]

local notation "C" => CyclotomicField p ℚ
local notation "Qbar" => AlgebraicClosure ℚ

private theorem case2_false (hp5 : 5 ≤ p)
    (unitsGalAction' : (ZMod p)ˣ →* Module.End (ZMod p)
      (ModP p (Additive (𝓞 (CyclotomicField p ℚ))ˣ)))
    (hρ : ∀ d u, unitsGalAction' d
        (ModP.proj p _ (Additive.ofMul u)) =
      ModP.proj p _ (Additive.ofMul
        (Units.mapEquiv (clRingAction p (CyclotomicField p ℚ) d).toMulEquiv u)))
    (hE2CL : ∀ a : ClGalModule p (𝓞 (CyclotomicField p ℚ)),
      IsOmegaEigenvector (clGalAction p (CyclotomicField p ℚ)) 2 a → a = 0)
    (hUnitsB2 : ∀ u : (𝓞 (CyclotomicField p ℚ))ˣ,
      IsOmegaEigenvector unitsGalAction' 2
        (ModP.proj p (Additive (𝓞 (CyclotomicField p ℚ))ˣ) (Additive.ofMul u)) →
      (∀ 𝔭 : HeightOneSpectrum (𝓞 (CyclotomicField p ℚ)),
        (p : 𝓞 (CyclotomicField p ℚ)) ∈ 𝔭.asIdeal →
        ∃ v : (𝔭.adicCompletion (CyclotomicField p ℚ))ˣ,
          v ^ p = (Units.map (algebraMap (𝓞 (CyclotomicField p ℚ))
            (𝔭.adicCompletion (CyclotomicField p ℚ))).toMonoidHom) u) →
      ModP.proj p (Additive (𝓞 (CyclotomicField p ℚ))ˣ) (Additive.ofMul u) = 0)

    (middle : ∀ (b : 𝓞 C), b ≠ 0 →
      (∀ 𝔮 : HeightOneSpectrum (𝓞 C),
        p ∣ Multiset.count 𝔮.asIdeal
          (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b}))) →
      (∀ d : (ZMod p)ˣ, ∃ n : ℕ, (n : ZMod p) = (d : ZMod p) ^ 2 ∧
        ∃ c₁ c₂ : 𝓞 C, c₂ ≠ 0 ∧ (clRingAction p C d) b * c₂ ^ p = b ^ n * c₁ ^ p) →
      (∀ a : ClGalModule p (𝓞 C), IsOmegaEigenvector (clGalAction p C) 2 a → a = 0) →
      ∃ (u : (𝓞 C)ˣ) (γ : 𝓞 C), γ ≠ 0 ∧ (b : 𝓞 C) = ↑u * γ ^ p)

    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (ι : CyclotomicField p ℚ →ₐ[ℚ] L) (b : 𝓞 (CyclotomicField p ℚ)) (hb0 : b ≠ 0) (β : L)
    (hβ : β ^ p = ι b)
    (hI : ∀ q : ℕ, q.Prime → ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q →
      A.inertiaSubgroupIn ℚ ⊓ MulAction.stabilizer (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
        ((ι (IsCyclotomicExtension.zeta p ℚ (CyclotomicField p ℚ)) : L) : AlgebraicClosure ℚ) ≤
        L.fixingSubgroup)
    (hC : ∀ τ : L ≃ₐ[ℚ] L,
      (∀ σ ∈ MulAction.stabilizer (L ≃ₐ[ℚ] L) (ι (IsCyclotomicExtension.zeta p ℚ C)),
        τ * σ = σ * τ) →
      τ ∈ MulAction.stabilizer (L ≃ₐ[ℚ] L) (ι (IsCyclotomicExtension.zeta p ℚ C)))
    (hcard : Nat.card (MulAction.stabilizer (L ≃ₐ[ℚ] L)
      (ι (IsCyclotomicExtension.zeta p ℚ C))) = p)
    (hbeig : ∀ d : (ZMod p)ˣ, ∃ γ : C,
      (cycloGalEquiv p C).symm d (b : C) = (b : C) ^ ((d : ZMod p) ^ 2).val * γ ^ p)
    (hbnp : ¬ ∃ c : C, c ^ p = (b : C)) : False := by
  classical
  have hp2 : p ≠ 2 := by omega

  have he2 : ∀ d : (ZMod p)ˣ, ∃ n : ℕ, (n : ZMod p) = (d : ZMod p) ^ 2 ∧
      ∃ c₁ c₂ : 𝓞 C, c₂ ≠ 0 ∧ (clRingAction p C d) b * c₂ ^ p = b ^ n * c₁ ^ p := fun d => by
    obtain ⟨γ, hγ⟩ := hbeig d
    exact ⟨((d : ZMod p) ^ 2).val, ZMod.natCast_zmod_val _, he2_of_field p b d _ γ hγ⟩

  have hval : ∀ 𝔮 : HeightOneSpectrum (𝓞 C),
      p ∣ Multiset.count 𝔮.asIdeal
        (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b})) :=
    fun 𝔮 => tame p L ι b β hI hb0 hβ 𝔮
  obtain ⟨u, γ, hγ0, hbu⟩ := middle b hb0 hval he2 hE2CL

  have hloc : ∀ 𝔭 : HeightOneSpectrum (𝓞 C), (p : 𝓞 C) ∈ 𝔭.asIdeal →
      ∃ v : 𝔭.adicCompletion C, v ^ p = algebraMap (𝓞 C) (𝔭.adicCompletion C) b :=
    fun 𝔭 h𝔭 => loc p L ι b β hI hp2 hβ hC hcard 𝔭 h𝔭
  obtain ⟨ε, hε⟩ := KumTail.units_tail p unitsGalAction' hρ hUnitsB2 b γ u hγ0 hbu he2 hloc

  apply hbnp
  refine ⟨(((ε : 𝓞 C) * γ : 𝓞 C) : C), ?_⟩
  rw [hbu, hε]
  simp only [map_mul, map_pow, Units.val_pow_eq_pow_val]
  ring

end ExtCitation.KumBridge
p2m_reactivate "P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation.KumFinite"
p2m_reactivate "P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation.KumFinite"

end PART_R3_CASE2_aux1
p2m_reactivate "P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation.KumFinite"

section PART_R2_aux2

set_option autoImplicit false

namespace ExtCitation
p2m_export "ExtCitation" "ExtVanishingCts card_rootsOfUnity_eq_self cycloExp IsAdmissibleExtension SplitsGlobally Cyclotomic.instIsCycExt"
p2m_open "ExtCitation"

p2m_open "NumberField P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.NumberField JacobiSumStickelberger Stickelberger Finset"
open scoped Classical

variable {p : ℕ} [Fact p.Prime]

section Generic

variable {M : Type*} [AddCommGroup M] [Module (ZMod p) M]

private noncomputable def w2kum_rawProj (ρ : (ZMod p)ˣ →* Module.End (ZMod p) M) (i : ℕ) :
    Module.End (ZMod p) M :=
  ∑ d : (ZMod p)ˣ, (((d : ZMod p) ^ i)⁻¹) • ρ d

private theorem w2kum_rawProj_apply (ρ : (ZMod p)ˣ →* Module.End (ZMod p) M) (i : ℕ) (a : M) :
    w2kum_rawProj ρ i a = ∑ d : (ZMod p)ˣ, (((d : ZMod p)^i)⁻¹) • ρ d a := by
  simp only [w2kum_rawProj, LinearMap.sum_apply, LinearMap.smul_apply]

private theorem w2kum_pow_unit_ne_zero (d : (ZMod p)ˣ) (i : ℕ) : ((d : ZMod p)^i) ≠ 0 := by
  have : ((d^i : (ZMod p)ˣ) : ZMod p) = (d : ZMod p)^i := by push_cast; ring
  rw [← this]; exact Units.ne_zero (d^i)

private theorem w2kum_isOmegaEigenvector_rawProj
    (ρ : (ZMod p)ˣ →* Module.End (ZMod p) M) (i : ℕ) (a : M) :
    IsOmegaEigenvector ρ i (w2kum_rawProj ρ i a) := by
  intro d'
  rw [w2kum_rawProj_apply, map_sum, Finset.smul_sum]
  simp only [(ρ d').map_smul, ← Module.End.mul_apply, ← ρ.map_mul]
  refine Fintype.sum_equiv (Equiv.mulLeft d') _ _ fun d => ?_
  rw [smul_smul]; congr 1
  simp only [Equiv.coe_mulLeft]
  have hne : ((d : ZMod p)^i) ≠ 0 := w2kum_pow_unit_ne_zero d i
  have hne' : ((d' : ZMod p)^i) ≠ 0 := w2kum_pow_unit_ne_zero d' i
  field_simp; push_cast; ring

end Generic
p2m_reactivate "P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation.KumFinite"

variable (p)

local notation "Kc" => CyclotomicField p ℚ
local notation "ACl" => Additive (ClassGroup (𝓞 Kc))

private noncomputable def w2kum_clAut (d : (ZMod p)ˣ) : ACl ≃+ ACl :=
  MulEquiv.toAdditive (ClassGroup.mulEquiv (clRingAction p Kc d))

private theorem w2kum_clAut_ofMul (d : (ZMod p)ˣ) (C : ClassGroup (𝓞 Kc)) :
    w2kum_clAut p d (Additive.ofMul C)
      = Additive.ofMul (ClassGroup.mulEquiv (clRingAction p Kc d) C) := rfl

private theorem w2kum_clGalAction_clProj (d : (ZMod p)ˣ) (c : ACl) :
    clGalAction p Kc d (clProj p (𝓞 Kc) c) = clProj p (𝓞 Kc) (w2kum_clAut p d c) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rfl

private noncomputable def w2kum_wt (d : (ZMod p)ˣ) : ℕ := (((d : ZMod p) ^ 2)⁻¹).val

private theorem w2kum_wt_cast (d : (ZMod p)ˣ) :
    (w2kum_wt p d : ZMod p) = ((d : ZMod p)^2)⁻¹ := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  unfold w2kum_wt
  rw [ZMod.natCast_val, ZMod.cast_id]

private noncomputable def w2kum_intProj (z : ACl) : ACl :=
  ∑ d : (ZMod p)ˣ, (w2kum_wt p d) • (w2kum_clAut p d z)

private theorem w2kum_clProj_intProj (z : ACl) :
    clProj p (𝓞 Kc) (w2kum_intProj p z)
      = w2kum_rawProj (clGalAction p Kc) 2 (clProj p (𝓞 Kc) z) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [w2kum_rawProj_apply]
  unfold w2kum_intProj
  rw [map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [map_nsmul, ← w2kum_clGalAction_clProj, ← w2kum_wt_cast, Nat.cast_smul_eq_nsmul]

private theorem w2kum_clProj_intProj_isEigen (z : ACl) :
    IsOmegaEigenvector (clGalAction p Kc) 2 (clProj p (𝓞 Kc) (w2kum_intProj p z)) := by
  rw [w2kum_clProj_intProj]
  exact w2kum_isOmegaEigenvector_rawProj _ 2 _

private theorem w2kum_pow_intProj_eq_neg
    (x z : ACl) (k : ℕ) (hxz : x = p^k • z)
    (hpx : p • x = 0)
    (n : (ZMod p)ˣ → ℕ) (hn : ∀ d, (n d : ZMod p) = (d : ZMod p)^2)
    (heig : ∀ d, w2kum_clAut p d x = (n d) • x) :
    p^k • (w2kum_intProj p z) = -x := by
  unfold w2kum_intProj
  rw [Finset.smul_sum]
  have hstep : ∀ d : (ZMod p)ˣ, p^k • (w2kum_wt p d) • w2kum_clAut p d z
      = (w2kum_wt p d * n d) • x := by
    intro d
    rw [smul_comm, ← map_nsmul, ← hxz, heig d, ← mul_nsmul']
  rw [Finset.sum_congr rfl fun d _ => hstep d]

  have hmod : ∀ d : (ZMod p)ˣ, ((w2kum_wt p d * n d : ℕ) : ZMod p) = 1 := by
    intro d
    push_cast
    rw [w2kum_wt_cast, hn d, inv_mul_cancel₀ (w2kum_pow_unit_ne_zero d 2)]
  have hone : ∀ d : (ZMod p)ˣ, (w2kum_wt p d * n d) • x = x := by
    intro d

    have hreduce : (w2kum_wt p d * n d) • x = ((w2kum_wt p d * n d) % p) • x := by
      conv_lhs => rw [← Nat.div_add_mod (w2kum_wt p d * n d) p,
        add_nsmul, mul_smul, smul_comm p, hpx, smul_zero, zero_add]
    rw [hreduce]
    have key := ZMod.val_natCast p (w2kum_wt p d * n d)
    rw [hmod d, ZMod.val_one p] at key
    rw [key.symm, one_nsmul]
  simp only [hone, Finset.sum_const, Finset.card_univ, ZMod.card_units p]

  have hp1 : (p - 1 + 1) • x = 0 := by
    rw [Nat.sub_add_cancel (Fact.out : p.Prime).one_le]; exact hpx
  rw [add_nsmul, one_nsmul] at hp1
  exact (neg_eq_of_add_eq_zero_left hp1).symm

private theorem w2kum_cl_descent
    (x : ACl) (hpx : p • x = 0)
    (n : (ZMod p)ˣ → ℕ) (hn : ∀ d, (n d : ZMod p) = (d : ZMod p)^2)
    (heig : ∀ d, w2kum_clAut p d x = (n d) • x)
    (hE2CL : ∀ a : ClGalModule p (𝓞 Kc),
      IsOmegaEigenvector (clGalAction p Kc) 2 a → a = 0) :
    x = 0 := by
  have hstep : ∀ k : ℕ, ∃ z : ACl, x = p^k • z := by
    intro k
    induction k with
    | zero => exact ⟨x, by simp⟩
    | succ k ih =>
      obtain ⟨z, hz⟩ := ih
      have heigz : clProj p (𝓞 Kc) (w2kum_intProj p z) = 0 :=
        hE2CL _ (w2kum_clProj_intProj_isEigen p z)
      obtain ⟨w, hw⟩ := (ModP.proj_eq_zero_iff p (Additive (ClassGroup (𝓞 Kc)))).mp heigz
      have hneg : p^k • (w2kum_intProj p z) = -x :=
        w2kum_pow_intProj_eq_neg p x z k hz hpx n hn heig
      refine ⟨-w, ?_⟩
      rw [pow_succ, mul_smul, smul_neg, hw, smul_neg, hneg, neg_neg]

  haveI : Fintype (ClassGroup (𝓞 Kc)) := inferInstance
  set N := Nat.card ACl with hN
  have hNpos : 0 < N := Nat.card_pos
  have hpp : p.Prime := Fact.out
  set a := N.factorization p
  obtain ⟨z, hz⟩ := hstep a
  have hlag : N • z = 0 := card_nsmul_eq_zero'

  have hfac : ordProj[p] N * ordCompl[p] N = N := Nat.ordProj_mul_ordCompl_eq_self N p
  have hmx : (ordCompl[p] N) • x = 0 := by
    rw [hz, ← mul_nsmul', mul_comm,
      show p^a = ordProj[p] N from rfl, hfac]
    exact hlag
  have hcop : Nat.Coprime p (ordCompl[p] N) := Nat.coprime_ordCompl hpp hNpos.ne'
  have hox : addOrderOf x = 1 := by
    refine Nat.eq_one_of_dvd_coprimes hcop ?_ ?_
    · exact addOrderOf_dvd_of_nsmul_eq_zero hpx
    · exact addOrderOf_dvd_of_nsmul_eq_zero hmx
  exact (AddMonoid.addOrderOf_eq_one_iff).mp hox

section Middle

open UniqueFactorizationMonoid
open scoped nonZeroDivisors

omit [Fact p.Prime] in

private theorem w2kum_Ideal_pow_injective
    {I J : Ideal (𝓞 Kc)} (hI : I ≠ 0) (hJ : J ≠ 0) {n : ℕ} (hn : n ≠ 0)
    (h : I^n = J^n) : I = J := by
  have hnf : normalizedFactors I = normalizedFactors J := by
    have h1 : n • normalizedFactors I = n • normalizedFactors J := by
      rw [← normalizedFactors_pow, ← normalizedFactors_pow, h]
    ext q
    have hc := congrArg (Multiset.count q) h1
    simp only [Multiset.count_nsmul] at hc
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hn) hc
  obtain ⟨u, hu⟩ := (associated_iff_normalizedFactors_eq_normalizedFactors hI hJ).mpr hnf
  rw [Subsingleton.elim u 1, Units.val_one, mul_one] at hu
  exact hu

private theorem w2kum_exists_pow_eq_span
    (b : 𝓞 Kc) (hb0 : b ≠ 0)
    (hval : ∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum (𝓞 Kc),
      p ∣ Multiset.count 𝔮.asIdeal (normalizedFactors (Ideal.span {b}))) :
    ∃ 𝔟 : Ideal (𝓞 Kc), 𝔟 ≠ 0 ∧ 𝔟^p = Ideal.span {b} := by
  have hspan0 : (Ideal.span {b} : Ideal (𝓞 Kc)) ≠ 0 := by
    rwa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  have hdvd : ∀ a ∈ normalizedFactors (Ideal.span ({b} : Set (𝓞 Kc))),
      p ∣ Multiset.count a (normalizedFactors (Ideal.span {b})) := by
    intro a ha
    have hprime := prime_of_normalized_factor a ha
    have hairr := hprime.irreducible
    exact hval ⟨a, (Ideal.isPrime_of_prime hprime), hprime.ne_zero⟩
  obtain ⟨M, hM⟩ := Multiset.exists_smul_of_dvd_count _ hdvd
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hMsub : ∀ a ∈ M, a ∈ normalizedFactors (Ideal.span ({b} : Set (𝓞 Kc))) := by
    intro a ha; rw [hM]; exact (Multiset.mem_nsmul_of_ne_zero hp0).mpr ha
  have hMirr : ∀ a ∈ M, Irreducible a := fun a ha =>
    (prime_of_normalized_factor a (hMsub a ha)).irreducible
  have hMnorm : ∀ a ∈ M, normalize a = a := fun a ha =>
    normalize_normalized_factor a (hMsub a ha)
  have h𝔟0 : (M.prod : Ideal (𝓞 Kc)) ≠ 0 := fun hprod0 =>
    (hMirr 0 (Multiset.prod_eq_zero_iff.mp hprod0)).ne_zero rfl
  refine ⟨M.prod, h𝔟0, ?_⟩
  obtain ⟨u, hu⟩ :=
    (associated_iff_normalizedFactors_eq_normalizedFactors (pow_ne_zero p h𝔟0) hspan0).mpr (by
      rw [normalizedFactors_pow, hM]
      congr 1
      rw [normalizedFactors_prod_eq M hMirr, Multiset.map_congr rfl hMnorm, Multiset.map_id'])
  rw [Subsingleton.elim u 1, Units.val_one, mul_one] at hu
  exact hu

private theorem w2kum_clAut_mk0_eq
    (b : 𝓞 Kc) (hb0 : b ≠ 0) (𝔟 : Ideal (𝓞 Kc)) (h𝔟 : 𝔟 ≠ 0)
    (h𝔟p : 𝔟^p = Ideal.span {b})
    (d : (ZMod p)ˣ) (nd : ℕ) (c₁ c₂ : 𝓞 Kc) (hc₂ : c₂ ≠ 0)
    (hrel : (clRingAction p Kc d) b * c₂^p = b^nd * c₁^p) :
    w2kum_clAut p d (Additive.ofMul (ClassGroup.mk0 ⟨𝔟, mem_nonZeroDivisors_of_ne_zero h𝔟⟩))
      = nd • Additive.ofMul (ClassGroup.mk0 ⟨𝔟, mem_nonZeroDivisors_of_ne_zero h𝔟⟩) := by
  set 𝔟' := (⟨𝔟, mem_nonZeroDivisors_of_ne_zero h𝔟⟩ : (Ideal (𝓞 Kc))⁰) with h𝔟'

  rw [w2kum_clAut_ofMul, ClassGroup.mulEquiv_mk0,
    ← ofMul_pow, ← map_pow]

  refine congrArg Additive.ofMul ((ClassGroup.mk0_eq_mk0_iff).mpr ⟨c₂, c₁, hc₂, ?_, ?_⟩)
  ·
    intro hc₁0
    rw [hc₁0, zero_pow (Fact.out : p.Prime).ne_zero, mul_zero] at hrel
    have hσb : (clRingAction p Kc d) b ≠ 0 := fun h =>
      hb0 ((clRingAction p Kc d).injective (by rw [h, map_zero]))
    exact (mul_ne_zero hσb (pow_ne_zero p hc₂)) hrel
  ·
    show Ideal.span {c₂} * (Ideal.mapNonZero (clRingAction p Kc d) 𝔟' : Ideal (𝓞 Kc))
        = Ideal.span {c₁} * ((𝔟'^nd : (Ideal (𝓞 Kc))⁰) : Ideal (𝓞 Kc))
    rw [Ideal.coe_mapNonZero, SubmonoidClass.coe_pow,
      show ((𝔟' : (Ideal (𝓞 Kc))⁰) : Ideal (𝓞 Kc)) = 𝔟 from rfl]

    refine w2kum_Ideal_pow_injective p
      (mul_ne_zero (by rwa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot])
        (mem_nonZeroDivisors_iff_ne_zero.mp
          (Ideal.mapNonZero (clRingAction p Kc d) 𝔟').2))
      (mul_ne_zero (by
          rw [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
          intro hc₁0
          rw [hc₁0, zero_pow (Fact.out : p.Prime).ne_zero, mul_zero] at hrel
          exact (mul_ne_zero (fun h => hb0 ((clRingAction p Kc d).injective
            (by rw [h, map_zero]))) (pow_ne_zero p hc₂)) hrel)
        (pow_ne_zero nd h𝔟))
      (Fact.out : p.Prime).ne_zero ?_

    rw [mul_pow, mul_pow, ← Ideal.map_pow, h𝔟p, ← pow_mul, mul_comm nd p, pow_mul, h𝔟p,
      Ideal.span_singleton_pow, Ideal.span_singleton_pow, Ideal.span_singleton_pow,
      show Ideal.map ((clRingAction p Kc d) : 𝓞 Kc →+* 𝓞 Kc) (Ideal.span {b})
          = Ideal.span {(clRingAction p Kc d) b} by
        rw [Ideal.map_span, Set.image_singleton]; rfl,
      Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_mul_span_singleton,
      mul_comm (c₂^p), mul_comm (c₁^p), hrel]

private theorem w2kum_middle
    (b : 𝓞 Kc) (hb0 : b ≠ 0)
    (hval : ∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum (𝓞 Kc),
      p ∣ Multiset.count 𝔮.asIdeal (normalizedFactors (Ideal.span {b})))
    (he2 : ∀ d : (ZMod p)ˣ, ∃ n : ℕ, (n : ZMod p) = (d : ZMod p)^2 ∧
      ∃ c₁ c₂ : 𝓞 Kc, c₂ ≠ 0 ∧ (clRingAction p Kc d) b * c₂^p = b^n * c₁^p)
    (hE2CL : ∀ a : ClGalModule p (𝓞 Kc),
      IsOmegaEigenvector (clGalAction p Kc) 2 a → a = 0) :
    ∃ (u : (𝓞 Kc)ˣ) (γ : 𝓞 Kc), γ ≠ 0 ∧ (b : 𝓞 Kc) = ↑u * γ^p := by

  obtain ⟨𝔟, h𝔟0, h𝔟p⟩ := w2kum_exists_pow_eq_span p b hb0 hval
  have h𝔟mem : 𝔟 ∈ (Ideal (𝓞 Kc))⁰ := mem_nonZeroDivisors_of_ne_zero h𝔟0
  set x : ACl := Additive.ofMul (ClassGroup.mk0 ⟨𝔟, h𝔟mem⟩) with hx

  have hpx : p • x = 0 := by
    show Additive.ofMul ((ClassGroup.mk0 ⟨𝔟, h𝔟mem⟩)^p) = Additive.ofMul 1
    congr 1
    rw [← map_pow]
    refine (ClassGroup.mk0_eq_one_iff _).mpr ?_
    show (𝔟^p).IsPrincipal
    rw [h𝔟p]; exact ⟨b, rfl⟩

  choose n hn c₁ c₂ hc₂ hrel using he2
  have heig : ∀ d, w2kum_clAut p d x = (n d) • x := fun d =>
    w2kum_clAut_mk0_eq p b hb0 𝔟 h𝔟0 h𝔟p d (n d) (c₁ d) (c₂ d) (hc₂ d) (hrel d)

  have hxz : x = 0 := w2kum_cl_descent p x hpx n hn heig hE2CL

  have hmk1 : ClassGroup.mk0 (⟨𝔟, h𝔟mem⟩ : (Ideal (𝓞 Kc))⁰) = 1 := by
    have := hxz; rw [hx] at this
    exact Additive.ofMul.injective this
  obtain ⟨γ, hγ⟩ := (ClassGroup.mk0_eq_one_iff h𝔟mem).mp hmk1
  have hγ0 : γ ≠ 0 := by
    rintro rfl
    rw [Submodule.span_zero_singleton] at hγ
    exact h𝔟0 hγ
  have hspan : Ideal.span {b} = Ideal.span {γ^p} := by
    rw [← h𝔟p, hγ, Ideal.span_singleton_pow]
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
  refine ⟨u⁻¹, γ, hγ0, ?_⟩
  rw [← hu, mul_comm b, Units.inv_mul_cancel_left]

end Middle
p2m_reactivate "P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation.KumFinite"

end ExtCitation
p2m_reactivate "P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation.KumFinite"

end PART_R2_aux2
p2m_reactivate "P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation.KumFinite"

section PART_SOLUTION_tail

open _root_.NumberField _root_.P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.NumberField IsDedekindDomain JacobiSumStickelberger Stickelberger _root_.ExtCitation _root_.P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation ExtCitation.Cyclotomic in

theorem solution (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    (unitsGalAction' : (ZMod p)ˣ →* Module.End (ZMod p)
      (ModP p (Additive (𝓞 (CyclotomicField p ℚ))ˣ)))
    (hρ : ∀ d u, unitsGalAction' d
        (ModP.proj p _ (Additive.ofMul u)) =
      ModP.proj p _ (Additive.ofMul
        (Units.mapEquiv (clRingAction p (CyclotomicField p ℚ) d).toMulEquiv u)))
    (hE2CL : ∀ a : ClGalModule p (𝓞 (CyclotomicField p ℚ)),
      IsOmegaEigenvector (clGalAction p (CyclotomicField p ℚ)) 2 a → a = 0)
    (hUnitsB2 : ∀ u : (𝓞 (CyclotomicField p ℚ))ˣ,
      IsOmegaEigenvector unitsGalAction' 2
        (ModP.proj p (Additive (𝓞 (CyclotomicField p ℚ))ˣ) (Additive.ofMul u)) →
      (∀ 𝔭 : HeightOneSpectrum (𝓞 (CyclotomicField p ℚ)),
        (p : 𝓞 (CyclotomicField p ℚ)) ∈ 𝔭.asIdeal →
        ∃ v : (𝔭.adicCompletion (CyclotomicField p ℚ))ˣ,
          v ^ p = (Units.map (algebraMap (𝓞 (CyclotomicField p ℚ))
            (𝔭.adicCompletion (CyclotomicField p ℚ))).toMonoidHom) u) →
      ModP.proj p (Additive (𝓞 (CyclotomicField p ℚ))ˣ) (Additive.ofMul u) = 0) :
    ExtVanishingCts p := by
  intro V _ _ _ _ C hadm
  classical
  rcases (w2kum_dichotomy (p := p) (V := V)) with htriv | ⟨σ₀, x₀, hσ₀ζ, hσ₀⟩
  ·
    exact w2kum_splitsGlobally_of_forall_fix (w2kumZeta_spec p) C hadm.fixed_sub htriv
  ·
    exfalso
    obtain ⟨L, hLfin, hLgal, ι, b, hb0, β, hβ, hI, hC, hcard, hbeig, hbnp⟩ :=
      w2kum_pkg_of_hbeig hadm.toIsAdmissibleExtension hadm.open_kernel hσ₀ζ hσ₀
        (fun b β hb0 hβ hbnp =>
          w2kum_hbeig hadm.toIsAdmissibleExtension hadm.open_kernel hσ₀ζ hσ₀ b β hb0 hβ hbnp)
    haveI := hLfin
    haveI := hLgal
    exact KumBridge.case2_false p hp5 unitsGalAction' hρ hE2CL hUnitsB2 (w2kum_middle p)
      L ι b hb0 β hβ hI hC hcard hbeig hbnp

end PART_SOLUTION_tail
p2m_reactivate "P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.ExtCitation.KumFinite"

end S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units
end P2MW
export P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units (solution)
