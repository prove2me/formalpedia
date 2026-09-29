-- Prove2me | solution 1 for FinFlatHopf.exists_subgroup_inertia_trivial_quotient_cyclotomic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/186c45a3-8ace-566b-999a-c2719c8d61f7

import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Bialgebra.Convolution
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Finiteness.Nakayama
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.FieldTheory.Finiteness
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Ideal.Span
import Definitions.Def_GaloisRep_Flat
import Mathlib.RingTheory.HopfAlgebra.TensorProduct
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.Coalgebra.Convolution
import Mathlib.RingTheory.FiniteType
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.Polynomial.Subring
import Mathlib.RingTheory.Valuation.RamificationGroup
import Definitions.Def_FLTPrelim_Ramification
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Algebra.Pi
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.Module.Defs
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Definitions.Def_HopfAlgebra_CartierDualMap
import Theorems.Thm_HopfAlgebra_exists_quotientFlag_of_galoisStableChain
import Theorems.Thm_FinFlatHopf_not_isLocalRing_dual_of_isLocalRing
import Theorems.Thm_CartierDual_exists_bialgEquiv_bidual
import Theorems.Thm_FinFlatHopf_inertiaFixed_valuationSubring_dvr_fixer_le_inertia
import Theorems.Thm_FinFlatHopf_dualPoints_equiv_monoidHom
import Theorems.Thm_ValuationSubring_valuation_sub_lt_one_of_mem_inertiaSubgroupIn
import Definitions.Def_FieldTheory_RatAlgClosureGalois
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic

namespace FinFlatHopf p2m_export "FinFlatHopf" "not_isLocalRing_dual_of_isLocalRing inertiaFixed_valuationSubring_dvr_fixer_le_inertia dualPoints_equiv_monoidHom" end FinFlatHopf
p2m_open_scoped "FinFlatHopf" in

theorem FinFlatHopf.isLocalRing_subalgebra_of_isIntegral
    {B A : Type} [CommRing B] [CommRing A] [Algebra B A]
    [Algebra.IsIntegral B A] [IsLocalRing A] (C : Subalgebra B A) :
    IsLocalRing C := by
  haveI : Algebra.IsIntegral (↥C) A := Algebra.IsIntegral.tower_top B
  have halg : ∀ x : ↥C, algebraMap (↥C) A x = (x : A) := fun _ => rfl
  have hker : RingHom.ker (algebraMap (↥C) A) ≤ ⊥ := fun x hx => by
    have h0 : (x : A) = 0 := by rw [← halg x]; exact RingHom.mem_ker.mp hx
    exact Ideal.mem_bot.mpr (Subtype.ext h0)
  refine IsLocalRing.of_unique_max_ideal
    ⟨(IsLocalRing.maximalIdeal A).comap (algebraMap (↥C) A),
     Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _, fun P hP => ?_⟩
  haveI : P.IsMaximal := hP
  obtain ⟨Q, hQmax, hQcomap⟩ :=
    Ideal.exists_ideal_over_maximal_of_isIntegral P (le_trans hker bot_le)
  rw [← hQcomap, IsLocalRing.eq_maximalIdeal hQmax]

#print axioms FinFlatHopf.isLocalRing_subalgebra_of_isIntegral

set_option autoImplicit false

noncomputable section

namespace FinFlatHopf
p2m_export "FinFlatHopf" "not_isLocalRing_dual_of_isLocalRing inertiaFixed_valuationSubring_dvr_fixer_le_inertia dualPoints_equiv_monoidHom"
namespace W4
p2m_open "FinFlatHopf"

open WithConv

variable {R H M : Type} [CommRing R] [CommRing H] [Algebra R H] [Algebra R (AlgebraicClosure ℚ)]

variable (R) in

def FixesBase (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) : Prop :=
  ∀ r : R, σ (algebraMap R (AlgebraicClosure ℚ) r) = algebraMap R (AlgebraicClosure ℚ) r

def fixAlgHom (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hσ : FixesBase R σ) : (AlgebraicClosure ℚ) →ₐ[R] (AlgebraicClosure ℚ) :=
  { σ.toRingEquiv.toRingHom with commutes' := hσ }

@[scoped simp] lemma fixAlgHom_apply (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hσ : FixesBase R σ) (x : (AlgebraicClosure ℚ)) :
    fixAlgHom σ hσ x = σ x := rfl

def compPoint (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hσ : FixesBase R σ) (f : WithConv (H →ₐ[R] (AlgebraicClosure ℚ))) :
    WithConv (H →ₐ[R] (AlgebraicClosure ℚ)) :=
  toConv ((fixAlgHom σ hσ).comp f.ofConv)

@[scoped simp] lemma compPoint_apply (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hσ : FixesBase R σ) (f : WithConv (H →ₐ[R] (AlgebraicClosure ℚ)))
    (x : H) : compPoint σ hσ f x = σ (f x) := rfl

open Classical in

def actDevice (e : WithConv (H →ₐ[R] (AlgebraicClosure ℚ)) ≃ M) (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (m : M) : M :=
  if hσ : FixesBase R σ then e (compPoint σ hσ (e.symm m)) else m

lemma actDevice_of_fixes (e : WithConv (H →ₐ[R] (AlgebraicClosure ℚ)) ≃ M) (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hσ : FixesBase R σ)
    (m : M) : actDevice e σ m = e (compPoint σ hσ (e.symm m)) := by
  unfold actDevice
  exact dif_pos hσ

lemma actDevice_of_not_fixes (e : WithConv (H →ₐ[R] (AlgebraicClosure ℚ)) ≃ M) (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hσ : ¬ FixesBase R σ) (m : M) : actDevice e σ m = m := by
  unfold actDevice
  exact dif_neg hσ

lemma fixesBase_of_pointwise (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (f g : WithConv (H →ₐ[R] (AlgebraicClosure ℚ)))
    (hfg : ∀ x : H, g x = σ (f x)) : FixesBase R σ := by
  intro r
  calc σ (algebraMap R (AlgebraicClosure ℚ) r)
      = σ (f (algebraMap R H r)) := by rw [f.ofConv.commutes r]
    _ = g (algebraMap R H r) := (hfg _).symm
    _ = algebraMap R (AlgebraicClosure ℚ) r := g.ofConv.commutes r

theorem hact_actDevice (e : WithConv (H →ₐ[R] (AlgebraicClosure ℚ)) ≃ M) (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (f g : WithConv (H →ₐ[R] (AlgebraicClosure ℚ))) (hfg : ∀ x : H, g x = σ (f x)) :
    e g = actDevice e σ (e f) := by
  have hσ : FixesBase R σ := fixesBase_of_pointwise σ f g hfg
  have hg : g = compPoint σ hσ f := by
    apply ofConv_injective
    ext x
    exact hfg x
  rw [hg, actDevice_of_fixes e σ hσ, Equiv.symm_apply_apply]

lemma actDevice_eq_smul [SMul (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) M] (e : WithConv (H →ₐ[R] (AlgebraicClosure ℚ)) ≃ M)
    (he_act : ∀ (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (f g : WithConv (H →ₐ[R] (AlgebraicClosure ℚ))),
      (∀ x : H, g x = σ (f x)) → e g = σ • e f)
    (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hσ : FixesBase R σ) (m : M) : actDevice e σ m = σ • m := by
  rw [actDevice_of_fixes e σ hσ]
  conv_rhs => rw [← e.apply_symm_apply m]
  exact he_act σ (e.symm m) (compPoint σ hσ (e.symm m)) (fun x => rfl)

theorem hstab_actDevice [SMul (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) M] (e : WithConv (H →ₐ[R] (AlgebraicClosure ℚ)) ≃ M)
    (he_act : ∀ (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (f g : WithConv (H →ₐ[R] (AlgebraicClosure ℚ))),
      (∀ x : H, g x = σ (f x)) → e g = σ • e f)
    (I : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hI : ∀ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), FixesBase R σ → σ ∈ I)
    (S : Set M) (hS : ∀ σ ∈ I, ∀ x ∈ S, σ • x ∈ S)
    (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (x : M) (hx : x ∈ S) : actDevice e σ x ∈ S := by
  by_cases hσ : FixesBase R σ
  · rw [actDevice_eq_smul e he_act σ hσ]
    exact hS σ (hI σ hσ) x hx
  · rw [actDevice_of_not_fixes e σ hσ]
    exact hx

lemma fixesBase_subring_iff (B : Subring (AlgebraicClosure ℚ)) (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :
    FixesBase B σ ↔ ∀ x ∈ B, σ x = x :=
  ⟨fun h x hx => h ⟨x, hx⟩, fun h r => h r.1 r.2⟩

lemma fixesBase_one : FixesBase R (1 : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :=
  fun _ => rfl

lemma fixesBase_mul (σ τ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hσ : FixesBase R σ) (hτ : FixesBase R τ) : FixesBase R (σ * τ) := fun r => by
  change σ (τ (algebraMap R (AlgebraicClosure ℚ) r)) = algebraMap R (AlgebraicClosure ℚ) r
  rw [hτ r, hσ r]

lemma fixesBase_inv (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hσ : FixesBase R σ) :
    FixesBase R σ⁻¹ := fun r => by
  have h := congrArg σ.symm (hσ r)
  rw [AlgEquiv.symm_apply_apply] at h
  exact h.symm

variable (R) in

def fixers : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) where
  carrier := {σ | FixesBase R σ}
  one_mem' := fixesBase_one
  mul_mem' := fun {σ τ} hσ hτ => fixesBase_mul σ τ hσ hτ
  inv_mem' := fun {σ} hσ => fixesBase_inv σ hσ

lemma mem_fixers_iff (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :
    σ ∈ fixers R ↔ FixesBase R σ := Iff.rfl

def fixAlgEquiv (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hσ : FixesBase R σ) :
    (AlgebraicClosure ℚ) ≃ₐ[R] (AlgebraicClosure ℚ) :=
  AlgEquiv.ofRingEquiv (f := (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ)) hσ

@[scoped simp] lemma fixAlgEquiv_apply (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hσ : FixesBase R σ) (x : AlgebraicClosure ℚ) : fixAlgEquiv σ hσ x = σ x := rfl

lemma toAlgHom_fixAlgEquiv (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hσ : FixesBase R σ) : (fixAlgEquiv σ hσ).toAlgHom = fixAlgHom σ hσ :=
  AlgHom.ext fun _ => rfl

lemma fixAlgEquiv_symm_apply (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hσ : FixesBase R σ) (x : AlgebraicClosure ℚ) : (fixAlgEquiv σ hσ).symm x = σ⁻¹ x := rfl

lemma toConv_toAlgHom_comp (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hσ : FixesBase R σ) (f : WithConv (H →ₐ[R] (AlgebraicClosure ℚ))) :
    toConv ((fixAlgEquiv σ hσ).toAlgHom.comp f.ofConv) = compPoint σ hσ f := by
  rw [toAlgHom_fixAlgEquiv]
  rfl

lemma compPoint_compPoint (σ τ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hσ : FixesBase R σ) (hτ : FixesBase R τ) (f : WithConv (H →ₐ[R] (AlgebraicClosure ℚ))) :
    compPoint σ hσ (compPoint τ hτ f) = compPoint (σ * τ) (fixesBase_mul σ τ hσ hτ) f := by
  apply ofConv_injective
  ext x
  rfl

lemma compPoint_one (f : WithConv (H →ₐ[R] (AlgebraicClosure ℚ))) :
    compPoint 1 fixesBase_one f = f := by
  apply ofConv_injective
  ext x
  rfl

theorem hstab_actDevice_of_fixers (e : WithConv (H →ₐ[R] (AlgebraicClosure ℚ)) ≃ M) (S : Set M)
    (hS : ∀ (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hσ : FixesBase R σ),
      ∀ x ∈ S, e (compPoint σ hσ (e.symm x)) ∈ S)
    (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (x : M) (hx : x ∈ S) :
    actDevice e σ x ∈ S := by
  by_cases hσ : FixesBase R σ
  · rw [actDevice_of_fixes e σ hσ]
    exact hS σ hσ x hx
  · rw [actDevice_of_not_fixes e σ hσ]
    exact hx

end FinFlatHopf.W4
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf"

end
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"

set_option autoImplicit false

noncomputable section

namespace FinFlatHopf
p2m_export "FinFlatHopf" "not_isLocalRing_dual_of_isLocalRing inertiaFixed_valuationSubring_dvr_fixer_le_inertia dualPoints_equiv_monoidHom"
namespace W4
p2m_open "FinFlatHopf"

open WithConv Coalgebra

variable {S X L : Type} [CommRing S] [CommRing X] [Bialgebra S X] [Field L] [Algebra S L]
  (P : ValuationSubring L)

def Cong (f g : WithConv (X →ₐ[S] L)) : Prop := ∀ x : X, P.valuation (f x - g x) < 1

def RedTriv (f : WithConv (X →ₐ[S] L)) : Prop :=
  ∀ x : X, P.valuation (f x - algebraMap S L (counit x)) < 1

lemma cong_refl (f : WithConv (X →ₐ[S] L)) : Cong P f f := fun x => by simp

lemma cong_symm {f g : WithConv (X →ₐ[S] L)} (h : Cong P f g) : Cong P g f := fun x => by
  rw [Valuation.map_sub_swap]; exact h x

lemma cong_trans {f g k : WithConv (X →ₐ[S] L)} (h₁ : Cong P f g) (h₂ : Cong P g k) :
    Cong P f k := fun x => by
  have : f x - k x = (f x - g x) + (g x - k x) := by ring
  rw [this]
  exact Valuation.map_add_lt _ (h₁ x) (h₂ x)

lemma redTriv_iff_cong_one (f : WithConv (X →ₐ[S] L)) : RedTriv P f ↔ Cong P f 1 := Iff.rfl

def ValuesIn : Prop := ∀ (f : X →ₐ[S] L) (x : X), f x ∈ P

lemma valuesIn_of_finite [Module.Finite S X] (hS : ∀ s : S, algebraMap S L s ∈ P) :
    ValuesIn (S := S) (X := X) P := by
  intro f x
  have hO : P.valuation.Integers P.valuation.valuationSubring :=
    Valuation.valuationSubring.integers P.valuation
  have hmem : ∀ s : S, algebraMap S L s ∈ P.valuation.valuationSubring := fun s =>
    show P.valuation (algebraMap S L s) ≤ 1 from (P.valuation_le_one_iff _).mpr (hS s)
  let φ : S →+* P.valuation.valuationSubring := (algebraMap S L).codRestrict _ hmem
  have hx : IsIntegral S x := Algebra.IsIntegral.isIntegral x
  have hy : IsIntegral P.valuation.valuationSubring (f x) := by
    refine hx.map_of_comp_eq φ (f : X →ₐ[S] L).toRingHom ?_
    ext s
    change ((φ s : P.valuation.valuationSubring) : L) = f (algebraMap S X s)
    rw [AlgHom.commutes]
    rfl
  exact P.mem_of_valuation_le_one _ (hO.isIntegral_iff_v_le_one.mp hy)

variable {P}

lemma val_mul_lt_one_of_lt_of_mem {a b : L} (ha : P.valuation a < 1) (hb : b ∈ P) :
    P.valuation (a * b) < 1 := by
  rw [Valuation.map_mul]
  calc P.valuation a * P.valuation b ≤ P.valuation a * 1 :=
        mul_le_mul' le_rfl ((P.valuation_le_one_iff b).mpr hb)
    _ = P.valuation a := mul_one _
    _ < 1 := ha

lemma cong_mul (hval : ValuesIn (S := S) (X := X) P) {f f' g g' : WithConv (X →ₐ[S] L)}
    (hf : Cong P f f') (hg : Cong P g g') : Cong P (f * g) (f' * g') := by
  intro x
  set ρ := ℛ S x
  have hfg : (f * g) x = ∑ i ∈ ρ.index, f (ρ.left i) * g (ρ.right i) :=
    Coalgebra.Repr.convMul_apply ρ (toConv f.ofConv.toLinearMap) (toConv g.ofConv.toLinearMap)
  have hfg' : (f' * g') x = ∑ i ∈ ρ.index, f' (ρ.left i) * g' (ρ.right i) :=
    Coalgebra.Repr.convMul_apply ρ (toConv f'.ofConv.toLinearMap) (toConv g'.ofConv.toLinearMap)
  rw [hfg, hfg', ← Finset.sum_sub_distrib]
  refine P.valuation.map_sum_lt one_ne_zero fun i _ => ?_
  have : f (ρ.left i) * g (ρ.right i) - f' (ρ.left i) * g' (ρ.right i) =
      (f (ρ.left i) - f' (ρ.left i)) * g (ρ.right i) +
        (g (ρ.right i) - g' (ρ.right i)) * f' (ρ.left i) := by ring
  rw [this]
  exact Valuation.map_add_lt _ (val_mul_lt_one_of_lt_of_mem (hf _) (hval _ _))
    (val_mul_lt_one_of_lt_of_mem (hg _) (hval _ _))

section additive

variable {M : Type} [AddCommGroup M] (e : WithConv (X →ₐ[S] L) ≃ M)
  (he_add : ∀ f g, e (f * g) = e f + e g)
include he_add

lemma e_one : e 1 = 0 := by
  have h := he_add 1 1
  rw [one_mul] at h
  simpa using h

lemma mul_symm_neg (f : WithConv (X →ₐ[S] L)) : f * e.symm (-(e f)) = 1 := by
  apply e.injective
  rw [he_add, Equiv.apply_symm_apply, add_neg_cancel, e_one e he_add]

lemma symm_neg_mul (f : WithConv (X →ₐ[S] L)) : e.symm (-(e f)) * f = 1 := by
  apply e.injective
  rw [he_add, Equiv.apply_symm_apply, neg_add_cancel, e_one e he_add]

lemma e_symm_add (m n : M) : e.symm (m + n) = e.symm m * e.symm n := by
  apply e.injective
  rw [he_add, Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

variable (P)

def redKernel (hval : ValuesIn (S := S) (X := X) P) : AddSubgroup M where
  carrier := {m | Cong P (e.symm m) 1}
  zero_mem' := by
    change Cong P (e.symm 0) 1
    rw [← e_one e he_add, Equiv.symm_apply_apply]
    exact cong_refl P 1
  add_mem' := by
    intro m n hm hn
    have hm' : Cong P (e.symm m) 1 := hm
    have hn' : Cong P (e.symm n) 1 := hn
    change Cong P (e.symm (m + n)) 1
    rw [e_symm_add e he_add]
    simpa [one_mul] using cong_mul hval hm' hn'
  neg_mem' := by
    intro m hm
    have hm : Cong P (e.symm m) 1 := hm
    change Cong P (e.symm (-m)) 1

    have hinv : e.symm m * e.symm (-m) = 1 := by
      have := mul_symm_neg e he_add (e.symm m)
      rwa [Equiv.apply_symm_apply] at this
    have h1 : Cong P (1 * e.symm (-m)) (e.symm m * e.symm (-m)) :=
      cong_mul hval (cong_symm P hm) (cong_refl P _)
    rw [one_mul, hinv] at h1
    exact h1

variable {P}

lemma mem_redKernel_iff (hval : ValuesIn (S := S) (X := X) P) (f : WithConv (X →ₐ[S] L)) :
    e f ∈ redKernel P e he_add hval ↔ RedTriv P f := by
  change Cong P (e.symm (e f)) 1 ↔ _
  rw [Equiv.symm_apply_apply]
  rfl

lemma sub_mem_redKernel_of_cong (hval : ValuesIn (S := S) (X := X) P)
    {f g : WithConv (X →ₐ[S] L)} (h : Cong P g f) :
    e g - e f ∈ redKernel P e he_add hval := by
  have hsub : e g - e f = e (g * e.symm (-(e f))) := by
    rw [he_add, Equiv.apply_symm_apply, sub_eq_add_neg]
  rw [hsub, mem_redKernel_iff e he_add hval, redTriv_iff_cong_one]
  have h1 : Cong P (g * e.symm (-(e f))) (f * e.symm (-(e f))) :=
    cong_mul hval h (cong_refl P _)
  rwa [mul_symm_neg e he_add] at h1

lemma sub_mem_redKernel_of_pointwise (hval : ValuesIn (S := S) (X := X) P) (σ : L → L)
    (hσ : ∀ a ∈ P, P.valuation (σ a - a) < 1)
    (f g : WithConv (X →ₐ[S] L)) (hfg : ∀ x : X, g x = σ (f x)) :
    e g - e f ∈ redKernel P e he_add hval := by
  refine sub_mem_redKernel_of_cong e he_add hval fun x => ?_
  rw [hfg]
  exact hσ _ (hval _ _)

lemma smul_sub_mem_redKernel {Γ : Type} [SMul Γ M] (hval : ValuesIn (S := S) (X := X) P)
    (act : Γ → L → L)
    (he_act : ∀ (σ : Γ) (f g : WithConv (X →ₐ[S] L)), (∀ x : X, g x = act σ (f x)) → e g = σ • e f)
    (σ : Γ) (hσ : ∀ a ∈ P, P.valuation (act σ a - a) < 1)
    (f g : WithConv (X →ₐ[S] L)) (hfg : ∀ x : X, g x = act σ (f x)) :
    σ • e f - e f ∈ redKernel P e he_add hval := by
  rw [← he_act σ f g hfg]
  exact sub_mem_redKernel_of_pointwise e he_add hval (act σ) hσ f g hfg

end additive
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"

end FinFlatHopf.W4
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"

end
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"

set_option autoImplicit false

noncomputable section

namespace FinFlatHopf
p2m_export "FinFlatHopf" "not_isLocalRing_dual_of_isLocalRing inertiaFixed_valuationSubring_dvr_fixer_le_inertia dualPoints_equiv_monoidHom"
namespace W4
p2m_open "FinFlatHopf"

open WithConv Coalgebra

variable {S X Y L : Type} [CommRing S] [CommRing X] [CommRing Y] [Bialgebra S X] [Bialgebra S Y]
  [CommRing L] [Algebra S L] (π : X →ₐc[S] Y)

def pullPoint (g : WithConv (Y →ₐ[S] L)) : WithConv (X →ₐ[S] L) :=
  toConv (g.ofConv.comp (π : X →ₐ[S] Y))

@[scoped simp] lemma pullPoint_apply (g : WithConv (Y →ₐ[S] L)) (x : X) : pullPoint π g x = g (π x) := rfl

lemma ofConv_pullPoint (g : WithConv (Y →ₐ[S] L)) :
    (pullPoint π g).ofConv = g.ofConv.comp (π : X →ₐ[S] Y) := rfl

lemma pullPoint_injective (hπ : Function.Surjective π) :
    Function.Injective (pullPoint (L := L) π) := by
  intro g g' h
  apply ofConv_injective
  exact (AlgHom.cancel_right hπ).mp (congrArg ofConv h)

lemma pullPoint_mul (g g' : WithConv (Y →ₐ[S] L)) :
    pullPoint π (g * g') = pullPoint π g * pullPoint π g' := by
  apply ofConv_injective
  exact AlgHom.convMul_comp_bialgHom_distrib g g' π

lemma pullPoint_one : pullPoint π (1 : WithConv (Y →ₐ[S] L)) = 1 := by
  apply ofConv_injective
  ext x
  change (1 : WithConv (Y →ₐ[S] L)) (π x) = (1 : WithConv (X →ₐ[S] L)) x
  rw [AlgHom.convOne_apply, AlgHom.convOne_apply, CoalgHomClass.counit_comp_apply]

lemma pullPoint_pointwise (σ : L → L) (g g' : WithConv (Y →ₐ[S] L))
    (h : ∀ y : Y, g' y = σ (g y)) : ∀ x : X, pullPoint π g' x = σ (pullPoint π g x) :=
  fun x => h (π x)

section factor

variable {M : Type} [AddCommGroup M] (e : WithConv (X →ₐ[S] L) ≃ M) (K : AddSubgroup M)
  (hπ : Function.Surjective π)
  (hfac : ∀ f : X →ₐ[S] L,
    (∃ g : Y →ₐ[S] L, g.comp (π : X →ₐ[S] Y) = f) ↔ e (WithConv.toConv f) ∈ K)
include hπ hfac

omit hπ in
lemma e_pullPoint_mem (g : WithConv (Y →ₐ[S] L)) : e (pullPoint π g) ∈ K :=
  (hfac _).mp ⟨g.ofConv, rfl⟩

def quotPtsEquiv : WithConv (Y →ₐ[S] L) ≃ K :=
  Equiv.ofBijective (fun g => ⟨e (pullPoint π g), e_pullPoint_mem π e K hfac g⟩) (by
    constructor
    · intro g g' h
      have h' : e (pullPoint π g) = e (pullPoint π g') := congrArg Subtype.val h
      exact pullPoint_injective π hπ (e.injective h')
    · rintro ⟨k, hk⟩
      have hk' : e (WithConv.toConv (e.symm k).ofConv) ∈ K := by
        change e (e.symm k) ∈ K
        rwa [Equiv.apply_symm_apply]
      obtain ⟨g, hg⟩ := (hfac _).mpr hk'
      refine ⟨toConv g, Subtype.ext ?_⟩
      change e (pullPoint π (toConv g)) = k
      have : pullPoint π (toConv g) = e.symm k := by
        apply ofConv_injective
        exact hg
      rw [this, Equiv.apply_symm_apply])

@[scoped simp] lemma coe_quotPtsEquiv (g : WithConv (Y →ₐ[S] L)) :
    ((quotPtsEquiv π e K hπ hfac g : K) : M) = e (pullPoint π g) := rfl

lemma quotPts_he_add (he_add : ∀ f g, e (f * g) = e f + e g) (g g' : WithConv (Y →ₐ[S] L)) :
    quotPtsEquiv π e K hπ hfac (g * g') =
      quotPtsEquiv π e K hπ hfac g + quotPtsEquiv π e K hπ hfac g' := by
  apply Subtype.ext
  change e (pullPoint π (g * g')) = e (pullPoint π g) + e (pullPoint π g')
  rw [pullPoint_mul, he_add]

lemma quotPts_he_act (act : (L → L) → M → M)
    (he_act : ∀ (σ : L → L) (f g : WithConv (X →ₐ[S] L)),
      (∀ x : X, g x = σ (f x)) → e g = act σ (e f))
    (σ : L → L) (g g' : WithConv (Y →ₐ[S] L)) (h : ∀ y : Y, g' y = σ (g y)) :
    ((quotPtsEquiv π e K hπ hfac g' : K) : M) = act σ ((quotPtsEquiv π e K hπ hfac g : K) : M) := by
  rw [coe_quotPtsEquiv, coe_quotPtsEquiv]
  exact he_act σ _ _ (pullPoint_pointwise π σ g g' h)

lemma natCard_quotPts : Nat.card (WithConv (Y →ₐ[S] L)) = Nat.card K :=
  Nat.card_congr (quotPtsEquiv π e K hπ hfac)

lemma finite_quotPts [Finite K] : Finite (WithConv (Y →ₐ[S] L)) :=
  Finite.of_equiv _ (quotPtsEquiv π e K hπ hfac).symm

end factor
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"

end FinFlatHopf.W4
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"

end
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"

namespace FinFlatHopf
p2m_export "FinFlatHopf" "not_isLocalRing_dual_of_isLocalRing inertiaFixed_valuationSubring_dvr_fixer_le_inertia dualPoints_equiv_monoidHom"
p2m_open "FinFlatHopf"

section S0

private lemma isUnit_in_subring_of_finite {R : Type*} [CommRing R] [Finite R]
    (S : Subring R) (s : S) (hs : IsUnit (s : R)) : IsUnit s := by
  obtain ⟨u, hu⟩ := hs
  haveI : Finite Rˣ := Finite.of_injective (Units.val : Rˣ → R) Units.val_injective
  have hn : 0 < Nat.card Rˣ := Nat.card_pos
  have hpow : (s : R) ^ Nat.card Rˣ = 1 := by
    rw [← hu, ← Units.val_pow_eq_pow_val, pow_card_eq_one', Units.val_one]
  have hpow' : s ^ Nat.card Rˣ = 1 := by
    apply Subtype.ext; push_cast; exact hpow
  exact IsUnit.of_pow_eq_one hpow' hn.ne'

theorem isLocalRing_subring_of_finite
    (R : Type*) [CommRing R] [IsLocalRing R] [Finite R] (p : ℕ) (hpr : p.Prime)
    (hRp : Nat.card (IsLocalRing.ResidueField R) = p) (S : Subring R) :
    ∃ _ : IsLocalRing S, Nat.card (IsLocalRing.ResidueField S) = p := by

  haveI hloc : IsLocalRing S := by
    refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self (fun s => ?_)
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (s : R) with h | h
    · exact Or.inl (isUnit_in_subring_of_finite S s h)
    · refine Or.inr (isUnit_in_subring_of_finite S (1 - s) ?_)
      push_cast; exact h

  haveI hlocHom : IsLocalHom (S.subtype : S →+* R) :=
    ⟨fun s hs => isUnit_in_subring_of_finite S s hs⟩

  let ψ := IsLocalRing.ResidueField.map (S.subtype : S →+* R)
  have hψinj : Function.Injective ψ := (ψ : _ →+* _).injective

  haveI : Finite (IsLocalRing.ResidueField R) := .of_surjective _ Ideal.Quotient.mk_surjective
  haveI : Finite (IsLocalRing.ResidueField S) :=
    .of_surjective _ Ideal.Quotient.mk_surjective
  haveI : Fintype (IsLocalRing.ResidueField R) := Fintype.ofFinite _
  haveI : Fintype (IsLocalRing.ResidueField S) := Fintype.ofFinite _
  letI : Algebra (IsLocalRing.ResidueField S) (IsLocalRing.ResidueField R) := ψ.toAlgebra
  have hpow : Fintype.card (IsLocalRing.ResidueField R) =
      Fintype.card (IsLocalRing.ResidueField S) ^
        Module.finrank (IsLocalRing.ResidueField S) (IsLocalRing.ResidueField R) :=
    Module.card_eq_pow_finrank

  rw [← Nat.card_eq_fintype_card, hRp] at hpow
  have h2 : 2 ≤ Fintype.card (IsLocalRing.ResidueField S) := Fintype.one_lt_card
  refine ⟨hloc, ?_⟩
  rw [Nat.card_eq_fintype_card]
  rcases (Nat.Prime.eq_one_or_self_of_dvd hpr _
    (hpow ▸ dvd_pow_self _ (by
      by_contra hd0
      rw [hd0, pow_zero] at hpow
      exact hpr.one_lt.ne' hpow))) with h1 | hp
  · omega
  · exact hp

end S0
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"

section S1

private lemma unit_smul_eq_zero {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {r : R} (hr : IsUnit r) {x : M} (hrx : r • x = 0) : x = 0 := by
  have h1 : ((↑hr.unit⁻¹ : R) * r) • x = 0 := by rw [mul_smul, hrx, smul_zero]
  rwa [hr.val_inv_mul, one_smul] at h1

theorem exists_submodule_card_eq_residue
    (R : Type*) [CommRing R] [IsLocalRing R] (p : ℕ)
    (hRp : Nat.card (IsLocalRing.ResidueField R) = p)
    (M : Type*) [AddCommGroup M] [Module R M] [Finite M] (hM : ∃ m : M, m ≠ 0) :
    ∃ N : Submodule R M, Nat.card N = p := by
  classical
  set 𝔪 := IsLocalRing.maximalIdeal R

  haveI : Finite (Submodule R M) :=
    Finite.of_injective (fun N => (N : Set M)) SetLike.coe_injective
  obtain ⟨k, hk⟩ : ∃ k, 𝔪 ^ (k + 1) • (⊤ : Submodule R M) = 𝔪 ^ k • ⊤ := by
    by_contra h
    push Not at h
    have hanti : StrictAnti fun i => 𝔪 ^ i • (⊤ : Submodule R M) :=
      strictAnti_nat_of_succ_lt fun i =>
        lt_of_le_of_ne (Submodule.smul_mono (Ideal.pow_le_pow_right i.le_succ) le_rfl) (h i)
    exact (Finite.of_injective _ hanti.injective).false

  have hNbot : 𝔪 ^ k • (⊤ : Submodule R M) = ⊥ := by
    have hNfg : (𝔪 ^ k • (⊤ : Submodule R M)).FG := Submodule.FG.of_finite
    have hNle : 𝔪 ^ k • (⊤ : Submodule R M) ≤ 𝔪 • (𝔪 ^ k • ⊤) := by
      conv_lhs => rw [← hk, pow_succ', Submodule.mul_smul]
    obtain ⟨r, hr1, hr0⟩ :=
      Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul 𝔪 _ hNfg hNle
    have hrunit : IsUnit r := by
      rw [← IsLocalRing.notMem_maximalIdeal]
      intro hr
      refine (IsLocalRing.maximalIdeal.isMaximal R).ne_top (𝔪.eq_top_iff_one.mpr ?_)
      simpa using 𝔪.sub_mem hr hr1
    exact eq_bot_iff.mpr fun n hn => unit_smul_eq_zero hrunit (hr0 n hn)

  have hex : ∃ i, 𝔪 ^ i • (⊤ : Submodule R M) = ⊥ := ⟨k, hNbot⟩
  have hk₀ : 𝔪 ^ (Nat.find hex) • (⊤ : Submodule R M) = ⊥ := Nat.find_spec hex
  have hk₀pos : 0 < Nat.find hex := by
    refine Nat.pos_of_ne_zero fun h0 => ?_
    obtain ⟨m, hm⟩ := hM
    have : m ∈ (⊥ : Submodule R M) := by
      rw [← hk₀, h0, pow_zero, Ideal.one_eq_top, Submodule.top_smul]; exact Submodule.mem_top
    exact hm (by simpa using this)
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk₀pos.ne'
  have hjne : 𝔪 ^ j • (⊤ : Submodule R M) ≠ ⊥ :=
    Nat.find_min hex (hj.symm ▸ j.lt_succ_self : j < Nat.find hex)
  have hjsucc : 𝔪 ^ (j + 1) • (⊤ : Submodule R M) = ⊥ := by
    have heq : j + 1 = Nat.find hex := hj.symm
    rw [heq]; exact hk₀

  obtain ⟨x, hx, hxne⟩ := (Submodule.ne_bot_iff _).mp hjne
  have hkillx : ∀ r ∈ 𝔪, r • x = (0 : M) := fun r hr => by
    have hmem : r • x ∈ 𝔪 ^ (j + 1) • (⊤ : Submodule R M) := by
      rw [pow_succ', Submodule.mul_smul]; exact Submodule.smul_mem_smul hr hx
    simpa [hjsucc] using hmem

  refine ⟨Submodule.span R {x}, ?_⟩
  have hker : LinearMap.ker (LinearMap.toSpanSingleton R M x) = 𝔪 := by
    ext r
    simp only [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
    refine ⟨fun hrx => ?_, hkillx r⟩
    by_contra hr
    exact hxne (unit_smul_eq_zero (IsLocalRing.notMem_maximalIdeal.mp hr) hrx)
  calc Nat.card ↥(Submodule.span R {x})
      = Nat.card ↥(LinearMap.range (LinearMap.toSpanSingleton R M x)) := by
          rw [LinearMap.range_toSpanSingleton]
    _ = Nat.card (R ⧸ LinearMap.ker (LinearMap.toSpanSingleton R M x)) :=
          (Nat.card_congr (LinearMap.toSpanSingleton R M x).quotKerEquivRange.toEquiv).symm
    _ = Nat.card (R ⧸ 𝔪) := by rw [hker]
    _ = Nat.card (IsLocalRing.ResidueField R) := rfl
    _ = p := hRp

end S1
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"

end FinFlatHopf
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"

#print axioms FinFlatHopf.isLocalRing_subring_of_finite
#print axioms FinFlatHopf.exists_submodule_card_eq_residue

namespace FinFlatHopf
p2m_export "FinFlatHopf" "not_isLocalRing_dual_of_isLocalRing inertiaFixed_valuationSubring_dvr_fixer_le_inertia dualPoints_equiv_monoidHom"
p2m_open "FinFlatHopf"

section S2

variable {B : Type*} [CommRing B] [IsDomain B]

omit [IsDomain B] in

theorem nonunits_eq_span_of_uniformizer (p : B) (_hp0 : p ≠ 0) (hp_nu : ¬ IsUnit p)
    (hDVR : ∀ x : B, x ≠ 0 → ∃ (k : ℕ) (u : Bˣ), x = u * p ^ k) :
    nonunits B = (Ideal.span {p} : Set B) := by
  ext x
  simp only [SetLike.mem_coe, Ideal.mem_span_singleton]
  constructor
  · intro hx
    rcases eq_or_ne x 0 with rfl | hx0
    · exact ⟨0, by ring⟩
    obtain ⟨k, u, rfl⟩ := hDVR x hx0
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact absurd (by simp only [pow_zero, mul_one]; exact u.isUnit) hx
    · refine ⟨u * p ^ (k - 1), ?_⟩
      have hrw : p * ((↑u : B) * p ^ (k - 1)) = ↑u * (p * p ^ (k - 1)) := by ring
      rw [hrw, ← pow_succ', Nat.sub_add_cancel hk]
  · rintro ⟨c, rfl⟩
    exact fun h => hp_nu (isUnit_of_mul_isUnit_left h)

theorem isLocalRing_of_uniformizer (p : B) (hp0 : p ≠ 0) (hp_nu : ¬ IsUnit p)
    (hDVR : ∀ x : B, x ≠ 0 → ∃ (k : ℕ) (u : Bˣ), x = u * p ^ k) :
    IsLocalRing B := by
  have hset := nonunits_eq_span_of_uniformizer p hp0 hp_nu hDVR
  refine IsLocalRing.of_nonunits_add (fun a b ha hb => ?_)
  have ha' : a ∈ (Ideal.span {p} : Ideal B) := by
    rw [← SetLike.mem_coe, ← hset]; exact ha
  have hb' : b ∈ (Ideal.span {p} : Ideal B) := by
    rw [← SetLike.mem_coe, ← hset]; exact hb
  have hsum := (Ideal.span {p} : Ideal B).add_mem ha' hb'
  rw [hset]; exact SetLike.mem_coe.mpr hsum

theorem maximalIdeal_eq_span_of_uniformizer (p : B) (hp0 : p ≠ 0) (hp_nu : ¬ IsUnit p)
    (hDVR : ∀ x : B, x ≠ 0 → ∃ (k : ℕ) (u : Bˣ), x = u * p ^ k) :
    letI := isLocalRing_of_uniformizer p hp0 hp_nu hDVR
    IsLocalRing.maximalIdeal B = Ideal.span {p} := by
  letI := isLocalRing_of_uniformizer p hp0 hp_nu hDVR
  exact SetLike.coe_injective (nonunits_eq_span_of_uniformizer p hp0 hp_nu hDVR)

theorem uniformizer_notMem_maximalIdeal_sq (p : B) (hp0 : p ≠ 0) (hp_nu : ¬ IsUnit p)
    (hDVR : ∀ x : B, x ≠ 0 → ∃ (k : ℕ) (u : Bˣ), x = u * p ^ k) :
    letI := isLocalRing_of_uniformizer p hp0 hp_nu hDVR
    p ∉ IsLocalRing.maximalIdeal B ^ 2 := by
  letI := isLocalRing_of_uniformizer p hp0 hp_nu hDVR
  rw [maximalIdeal_eq_span_of_uniformizer p hp0 hp_nu hDVR, sq,
    Ideal.span_singleton_mul_span_singleton, Ideal.mem_span_singleton]
  rintro ⟨c, hc⟩

  have h1 : p * (1 - p * c) = 0 := by
    have hrw : p * (1 - p * c) = p - p * p * c := by ring
    rw [hrw, ← hc, sub_self]
  have h2 : 1 - p * c = 0 := (mul_eq_zero.mp h1).resolve_left hp0
  have h3 : p * c = 1 := (sub_eq_zero.mp h2).symm
  exact hp_nu ⟨⟨p, c, h3, by rw [mul_comm]; exact h3⟩, rfl⟩

omit [IsDomain B] in

theorem isPrincipalIdealRing_of_uniformizer (p : B)
    (hDVR : ∀ x : B, x ≠ 0 → ∃ (k : ℕ) (u : Bˣ), x = u * p ^ k) :
    IsPrincipalIdealRing B := by
  classical
  constructor
  intro I
  rcases eq_or_ne I ⊥ with rfl | hI
  · exact ⟨0, by simp⟩

  have hEx : ∃ k, p ^ k ∈ I := by
    obtain ⟨x, hxI, hx0⟩ := (Submodule.ne_bot_iff I).mp hI
    obtain ⟨k, u, rfl⟩ := hDVR x hx0
    refine ⟨k, ?_⟩
    have := I.smul_mem ((↑u⁻¹ : B)) hxI
    simpa [← mul_assoc] using this
  refine ⟨p ^ Nat.find hEx, le_antisymm (fun y hy => ?_)
    (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Nat.find_spec hEx)))⟩
  rcases eq_or_ne y 0 with rfl | hy0
  · exact Submodule.zero_mem _
  obtain ⟨j, v, rfl⟩ := hDVR y hy0
  have hpj : p ^ j ∈ I := by
    have := I.smul_mem ((↑v⁻¹ : B)) hy
    simpa [← mul_assoc] using this
  have hjk : Nat.find hEx ≤ j := Nat.find_le hpj
  rw [Ideal.mem_span_singleton]
  exact ⟨v * p ^ (j - Nat.find hEx), by
    rw [mul_comm (p ^ Nat.find hEx), mul_assoc, ← pow_add, Nat.sub_add_cancel hjk]⟩

end S2
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"

end FinFlatHopf
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"

#print axioms FinFlatHopf.nonunits_eq_span_of_uniformizer
#print axioms FinFlatHopf.isLocalRing_of_uniformizer
#print axioms FinFlatHopf.maximalIdeal_eq_span_of_uniformizer
#print axioms FinFlatHopf.uniformizer_notMem_maximalIdeal_sq
#print axioms FinFlatHopf.isPrincipalIdealRing_of_uniformizer

set_option autoImplicit false

noncomputable section

namespace FinFlatHopf
p2m_export "FinFlatHopf" "not_isLocalRing_dual_of_isLocalRing inertiaFixed_valuationSubring_dvr_fixer_le_inertia dualPoints_equiv_monoidHom"
namespace W4
p2m_open "FinFlatHopf"

open TensorProduct WithConv Coalgebra

section generic

variable {R S H L : Type} [CommRing R] [CommRing S] [Algebra R S] [CommRing H] [HopfAlgebra R H]
  [Field L] [Algebra R L] [Algebra S L] [IsScalarTower R S L]

example : HopfAlgebra S (S ⊗[R] H) := inferInstance
example [Module.Flat R H] : Module.Flat S (S ⊗[R] H) := inferInstance
example [Module.Finite R H] : Module.Finite S (S ⊗[R] H) := inferInstance
example [Module.Finite R H] : Algebra.FiniteType S (S ⊗[R] H) := inferInstance
example [Coalgebra.IsCocomm R H] : Coalgebra.IsCocomm S (S ⊗[R] H) := inferInstance

def ptsEquiv : WithConv (S ⊗[R] H →ₐ[S] L) ≃ WithConv (H →ₐ[R] L) :=
  (WithConv.equiv _).trans <| (AlgHom.liftEquiv R S H L).symm.trans (WithConv.equiv _).symm

@[scoped simp] lemma ptsEquiv_apply (F : WithConv (S ⊗[R] H →ₐ[S] L)) (h : H) :
    ptsEquiv F h = F ((1 : S) ⊗ₜ[R] h) := rfl

@[scoped simp] lemma ptsEquiv_symm_apply (f : WithConv (H →ₐ[R] L)) (s : S) (h : H) :
    (ptsEquiv (R := R) (S := S) (H := H) (L := L)).symm f (s ⊗ₜ[R] h) = s • f h := rfl

def reprOneTmul (h : H) {ι : Type*} (ρ : Coalgebra.Repr R h ι) : Coalgebra.Repr S ((1 : S) ⊗ₜ[R] h) ι where
  index := ρ.index
  left i := (1 : S) ⊗ₜ[R] ρ.left i
  right i := (1 : S) ⊗ₜ[R] ρ.right i
  eq := by
    rw [TensorProduct.comul_tmul, CommSemiring.comul_apply, ← ρ.eq, tmul_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [AlgebraTensorModule.tensorTensorTensorComm_tmul]

lemma ptsEquiv_mul (F G : WithConv (S ⊗[R] H →ₐ[S] L)) :
    ptsEquiv (F * G) = ptsEquiv F * ptsEquiv G := by
  apply ofConv_injective
  ext h
  change (F * G) ((1 : S) ⊗ₜ[R] h) = (ptsEquiv F * ptsEquiv G) h
  have hR : (ptsEquiv F * ptsEquiv G) h =
      ∑ i ∈ (ℛ R h).index, F ((1 : S) ⊗ₜ[R] (ℛ R h).left i) * G ((1 : S) ⊗ₜ[R] (ℛ R h).right i) :=
    Coalgebra.Repr.convMul_apply (ℛ R h) (toConv (ptsEquiv F).ofConv.toLinearMap)
      (toConv (ptsEquiv G).ofConv.toLinearMap)
  have hL : (F * G) ((1 : S) ⊗ₜ[R] h) =
      ∑ i ∈ (ℛ R h).index, F ((1 : S) ⊗ₜ[R] (ℛ R h).left i) * G ((1 : S) ⊗ₜ[R] (ℛ R h).right i) :=
    Coalgebra.Repr.convMul_apply (reprOneTmul h (ℛ R h)) (toConv F.ofConv.toLinearMap)
      (toConv G.ofConv.toLinearMap)
  rw [hL, hR]

lemma ptsEquiv_one : ptsEquiv (1 : WithConv (S ⊗[R] H →ₐ[S] L)) = (1 : WithConv (H →ₐ[R] L)) := by
  apply ofConv_injective
  ext h
  change (1 : WithConv (S ⊗[R] H →ₐ[S] L)) ((1 : S) ⊗ₜ[R] h) = (1 : WithConv (H →ₐ[R] L)) h
  rw [AlgHom.convOne_apply, AlgHom.convOne_apply, TensorProduct.counit_tmul,
    CommSemiring.counit_apply, Algebra.smul_def, mul_one, ← IsScalarTower.algebraMap_apply]

variable {M : Type}

lemma he_add_baseChange [Add M] (e : WithConv (H →ₐ[R] L) ≃ M)
    (he_add : ∀ f g, e (f * g) = e f + e g) (F G : WithConv (S ⊗[R] H →ₐ[S] L)) :
    (ptsEquiv.trans e) (F * G) = (ptsEquiv.trans e) F + (ptsEquiv.trans e) G := by
  simp only [Equiv.trans_apply, ptsEquiv_mul]
  exact he_add _ _

lemma he_act_baseChange {Γ : Type} [SMul Γ M] (act : Γ → L → L) (e : WithConv (H →ₐ[R] L) ≃ M)
    (he_act : ∀ (σ : Γ) (f g : WithConv (H →ₐ[R] L)), (∀ x : H, g x = act σ (f x)) → e g = σ • e f)
    (σ : Γ) (F G : WithConv (S ⊗[R] H →ₐ[S] L)) (hFG : ∀ x : S ⊗[R] H, G x = act σ (F x)) :
    (ptsEquiv.trans e) G = σ • (ptsEquiv.trans e) F :=
  he_act σ (ptsEquiv F) (ptsEquiv G) fun x => hFG ((1 : S) ⊗ₜ[R] x)

lemma pointwise_baseChange_of_pointwise (τ : L →ₐ[S] L) (F G : WithConv (S ⊗[R] H →ₐ[S] L))
    (hfg : ∀ x : H, ptsEquiv G x = τ (ptsEquiv F x)) : ∀ x : S ⊗[R] H, G x = τ (F x) := by
  have : G.ofConv = τ.comp F.ofConv := by
    apply Algebra.TensorProduct.ext_ring
    ext x
    simpa using hfg x
  intro x
  exact congrArg (fun φ : S ⊗[R] H →ₐ[S] L => φ x) this

end generic
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"

section subringBase

abbrev algebraOfSubring (p : ℕ) (B : Subring (AlgebraicClosure ℚ))
    (hB : ∀ q : ℚ, q ∈ GaloisRep.ratLocalizedAt p → algebraMap ℚ (AlgebraicClosure ℚ) q ∈ B) :
    Algebra (GaloisRep.ratLocalizedAt p) B :=
  RingHom.toAlgebra
    { toFun := fun q => ⟨algebraMap ℚ (AlgebraicClosure ℚ) q.1, hB q.1 q.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }

lemma algebraMap_algebraOfSubring_apply (p : ℕ) (B : Subring (AlgebraicClosure ℚ))
    (hB : ∀ q : ℚ, q ∈ GaloisRep.ratLocalizedAt p → algebraMap ℚ (AlgebraicClosure ℚ) q ∈ B)
    (q : GaloisRep.ratLocalizedAt p) :
    letI := algebraOfSubring p B hB
    ((algebraMap (GaloisRep.ratLocalizedAt p) B q : B) : AlgebraicClosure ℚ) =
      algebraMap ℚ (AlgebraicClosure ℚ) q := rfl

lemma isScalarTower_algebraOfSubring (p : ℕ) (B : Subring (AlgebraicClosure ℚ))
    (hB : ∀ q : ℚ, q ∈ GaloisRep.ratLocalizedAt p → algebraMap ℚ (AlgebraicClosure ℚ) q ∈ B) :
    letI := algebraOfSubring p B hB
    IsScalarTower (GaloisRep.ratLocalizedAt p) B (AlgebraicClosure ℚ) := by
  letI := algebraOfSubring p B hB
  exact IsScalarTower.of_algebraMap_eq fun q => rfl

end subringBase
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"

end FinFlatHopf.W4
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"

end
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"

p2m_open_scoped "FinFlatHopf" in

theorem FinFlatHopf.finite_withConv_algHom
    (S H L : Type) [CommRing S] [CommRing H] [Algebra S H]
    [Module.Free S H] [Module.Finite S H] [Field L] [Algebra S L] :
    Finite (WithConv (H →ₐ[S] L)) := by
  haveI hfin : Finite (H →ₐ[S] L) := by
    haveI hmod : Module.Finite L (H →ₗ[S] L) := inferInstance
    exact (linearIndependent_algHom_toLinearMap S H L).finite
  exact Finite.of_equiv _ (WithConv.equiv (H →ₐ[S] L)).symm

#print axioms FinFlatHopf.finite_withConv_algHom

open Pointwise

p2m_open_scoped "FinFlatHopf" in

theorem FinFlatHopf.isIntegral_of_mem_valuationSubring_of_fixers_le
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (B : Subring (AlgebraicClosure ℚ))
    (hB : ∀ x : AlgebraicClosure ℚ, x ∈ B ↔
      (x ∈ P ∧ ∀ σ ∈ P.inertiaSubgroupIn ℚ, σ x = x))
    (hfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      (∀ x ∈ B, σ x = x) → σ ∈ P.inertiaSubgroupIn ℚ)
    (x : AlgebraicClosure ℚ) (hx : x ∈ P) : IsIntegral (↥B) x := by
  classical
  set I : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
    P.inertiaSubgroupIn ℚ with hIdef
  set T : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    IntermediateField.fixedField I with hTdef
  have hBT : ∀ b ∈ B, b ∈ T := fun b hb =>
    (IntermediateField.mem_fixedField_iff I b).mpr ((hB b).mp hb).2
  have halgQ : IsIntegral ℚ x := (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).isIntegral
  have halg : IsIntegral (↥T) x := halgQ.tower_top
  set f : Polynomial (↥T) := minpoly (↥T) x with hfdef
  have hfmonic : f.Monic := minpoly.monic halg
  set φ : (↥T) →+* AlgebraicClosure ℚ := algebraMap (↥T) (AlgebraicClosure ℚ) with hφdef
  set F : Polynomial (AlgebraicClosure ℚ) := f.map φ with hFdef
  have hFmonic : F.Monic := hfmonic.map φ
  have hFsplits : F.Splits := IsAlgClosed.splits F

  have hroot : ∀ r ∈ F.roots, r ∈ P := by
    intro r hr
    have hev : (Polynomial.aeval r) (minpoly (↥T) x) = 0 := by
      have h1 : F.IsRoot r := Polynomial.isRoot_of_mem_roots hr
      rw [Polynomial.IsRoot] at h1
      rw [Polynomial.aeval_def, ← Polynomial.eval_map]
      exact h1
    obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root' halg.isAlgebraic hev
    set σ' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ := σ.restrictScalars ℚ with hσ'def
    have hσ'B : ∀ b ∈ B, σ' b = b := by
      intro b hb
      have hcomm : σ (algebraMap (↥T) (AlgebraicClosure ℚ) ⟨b, hBT b hb⟩) =
          algebraMap (↥T) (AlgebraicClosure ℚ) ⟨b, hBT b hb⟩ := σ.commutes _
      simpa [hσ'def] using hcomm
    have hσ'D : σ' ∈ P.decompositionSubgroup ℚ := by
      obtain ⟨τ, -, hτ⟩ := Subgroup.mem_map.mp (hfix σ' hσ'B)
      exact hτ ▸ τ.2
    have hstab : σ' • P = P := MulAction.mem_stabilizer_iff.mp hσ'D
    have hmem : σ' • x ∈ σ' • P := ValuationSubring.smul_mem_pointwise_smul σ' x P hx
    rw [hstab, AlgEquiv.smul_def] at hmem
    have hres : σ' x = r := hσ
    rwa [hres] at hmem

  have hcard : Multiset.card F.roots = F.natDegree :=
    Polynomial.splits_iff_card_roots.mp hFsplits
  have hFprod : F = (F.roots.map fun r => Polynomial.X - Polynomial.C r).prod :=
    hFsplits.eq_prod_roots_of_monic hFmonic
  have hcoeffP : ∀ k, F.coeff k ∈ P := by
    intro k
    rcases le_or_gt k (Multiset.card F.roots) with hk | hk
    · rw [hFprod, Multiset.prod_X_sub_C_coeff F.roots hk]
      refine mul_mem (pow_mem (neg_mem (one_mem P)) _) ?_
      rw [Multiset.esymm]
      refine multiset_sum_mem _ fun a ha => ?_
      obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp ha
      refine multiset_prod_mem _ fun c hc => ?_
      exact hroot c (Multiset.mem_of_le (Multiset.mem_powersetCard.mp ht).1 hc)
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hcard ▸ hk)]
      exact zero_mem P

  have hcoeffB : ∀ k, F.coeff k ∈ B := by
    intro k
    refine (hB _).mpr ⟨hcoeffP k, ?_⟩
    intro σ hσI
    have hTk : (F.coeff k) ∈ T := by
      rw [hFdef, Polynomial.coeff_map]
      exact (f.coeff k).2
    exact (IntermediateField.mem_fixedField_iff I _).mp hTk σ hσI

  have hsub : (↑F.coeffs : Set (AlgebraicClosure ℚ)) ⊆ B := by
    intro c hc
    obtain ⟨n, -, rfl⟩ := Polynomial.mem_coeffs_iff.mp hc
    exact hcoeffB n
  refine ⟨F.toSubring B hsub, ?_, ?_⟩
  · exact (Polynomial.monic_toSubring (hp := hsub)).mpr hFmonic
  ·
    have hAB : algebraMap (↥B) (AlgebraicClosure ℚ) = B.subtype := RingHom.ext fun _ => rfl
    rw [hAB, Polynomial.eval₂_eq_eval_map, Polynomial.map_toSubring, hFdef, Polynomial.eval_map,
      hφdef, ← Polynomial.aeval_def, hfdef]
    exact minpoly.aeval (↥T) x

#print axioms FinFlatHopf.isIntegral_of_mem_valuationSubring_of_fixers_le

open scoped TensorProduct

p2m_open_scoped "FinFlatHopf" in

theorem FinFlatHopf.injective_eval_points
    (R C L : Type) [CommRing R] [Nontrivial R] [CommRing C] [Algebra R C]
    [Module.Free R C] [Module.Finite R C] [Field L] [Algebra R L]
    (hR : Function.Injective (algebraMap R L))
    (hfin : Finite (C →ₐ[R] L))
    (hcard : Nat.card (C →ₐ[R] L) = Module.finrank R C) :
    Function.Injective (fun c : C => (fun g : C →ₐ[R] L => g c)) := by
  classical
  haveI := Fintype.ofFinite (C →ₐ[R] L)

  suffices h0 : ∀ x : C, (∀ g : C →ₐ[R] L, g x = 0) → x = 0 by
    intro c₁ c₂ h
    have hsub : ∀ g : C →ₐ[R] L, g (c₁ - c₂) = 0 := by
      intro g
      rw [map_sub, sub_eq_zero]
      exact congrFun h g
    exact sub_eq_zero.mp (h0 _ hsub)
  intro x hx

  set lift : (C →ₐ[R] L) ≃ (L ⊗[R] C →ₐ[L] L) := AlgHom.liftEquiv R L C L with hliftdef
  have hli : LinearIndependent L
      (fun g : (C →ₐ[R] L) => (lift g).toLinearMap) :=
    (linearIndependent_algHom_toLinearMap L (L ⊗[R] C) L).comp lift lift.injective

  have hfrV : Module.finrank L (L ⊗[R] C) = Module.finrank R C :=
    Module.finrank_baseChange
  have hfr : Fintype.card (C →ₐ[R] L) =
      Module.finrank L (Module.Dual L (L ⊗[R] C)) := by
    rw [Subspace.dual_finrank_eq, hfrV, ← Nat.card_eq_fintype_card, hcard]
  set bdual : Module.Basis (C →ₐ[R] L) L (Module.Dual L (L ⊗[R] C)) :=
    basisOfLinearIndependentOfCardEqFinrank'
      (fun g : (C →ₐ[R] L) => (lift g).toLinearMap) hli hfr with hbdef
  have hbcoe : ∀ g : (C →ₐ[R] L), bdual g = (lift g).toLinearMap := by
    intro g
    rw [hbdef, coe_basisOfLinearIndependentOfCardEqFinrank']

  have hVx : ∀ g : (C →ₐ[R] L), (lift g).toLinearMap (1 ⊗ₜ[R] x) = 0 := by
    intro g
    have : (lift g) ((1 : L) ⊗ₜ[R] x) = (1 : L) • g x := by
      rw [hliftdef]
      exact AlgHom.liftEquiv_tmul g 1 x
    simp only [AlgHom.toLinearMap_apply]
    rw [this, one_smul, hx g]

  have hdual : ∀ φ : Module.Dual L (L ⊗[R] C), φ (1 ⊗ₜ[R] x) = 0 := by
    intro φ
    have hrepr := bdual.sum_repr φ
    rw [← hrepr, LinearMap.coe_sum, Finset.sum_apply]
    refine Finset.sum_eq_zero fun g _ => ?_
    rw [LinearMap.smul_apply, hbcoe g, hVx g, smul_zero]

  have hV0 : ((1 : L) ⊗ₜ[R] x : L ⊗[R] C) = 0 :=
    (Module.forall_dual_apply_eq_zero_iff L _).mp hdual

  have hinc : Function.Injective
      (Algebra.TensorProduct.includeRight : C →ₐ[R] L ⊗[R] C) :=
    Algebra.TensorProduct.includeRight_injective hR
  have hzero : (Algebra.TensorProduct.includeRight : C →ₐ[R] L ⊗[R] C) x =
      (Algebra.TensorProduct.includeRight : C →ₐ[R] L ⊗[R] C) 0 := by
    rw [map_zero]
    exact hV0
  exact hinc hzero

#print axioms FinFlatHopf.injective_eval_points

p2m_open_scoped "FinFlatHopf" in

private theorem FinFlatHopf.isUnit_of_injective_of_integral_inv
    {R A B : Type} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) (hf : Function.Injective f)
    {a : A} (u : Bˣ) (hu : (↑u : B) = f a)
    (hint : IsIntegral R ((↑u⁻¹ : B))) : IsUnit a := by
  classical
  obtain ⟨F, hFm, hF0⟩ := hint
  rw [← Polynomial.aeval_def] at hF0
  rcases hn : F.natDegree with _ | m
  ·
    have hF1 : F = 1 := by
      rwa [← Polynomial.Monic.natDegree_eq_zero hFm]
    rw [hF1, map_one] at hF0
    haveI : Subsingleton B := subsingleton_of_zero_eq_one hF0.symm
    haveI : Subsingleton A := hf.subsingleton
    exact isUnit_of_subsingleton a
  ·
    have key := congrArg (fun z : B => z * (↑u : B) ^ (m + 1)) hF0
    rw [Polynomial.aeval_eq_sum_range, hn] at key
    simp only [zero_mul, Finset.sum_mul] at key

    have hterm : ∀ i ∈ Finset.range (m + 1 + 1),
        F.coeff i • (↑u⁻¹ : B) ^ i * (↑u : B) ^ (m + 1) =
          F.coeff i • (↑u : B) ^ (m + 1 - i) := by
      intro i hi
      have hile : i ≤ m + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hsplit : (u : Bˣ) ^ (m + 1) = u ^ i * u ^ (m + 1 - i) := by
        rw [← pow_add, Nat.add_sub_cancel' hile]
      have hgrp : (u⁻¹ : Bˣ) ^ i * u ^ (m + 1) = u ^ (m + 1 - i) := by
        rw [hsplit, inv_pow, ← mul_assoc, inv_mul_cancel, one_mul]
      calc F.coeff i • (↑u⁻¹ : B) ^ i * (↑u : B) ^ (m + 1)
          = F.coeff i • ((↑u⁻¹ : B) ^ i * (↑u : B) ^ (m + 1)) := by
            rw [smul_mul_assoc]
        _ = F.coeff i • ((↑(u⁻¹ ^ i * u ^ (m + 1)) : B)) := by
            rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
        _ = F.coeff i • (↑u : B) ^ (m + 1 - i) := by
            rw [hgrp, Units.val_pow_eq_pow_val]
    rw [Finset.sum_congr rfl hterm] at key

    rw [Finset.sum_range_succ] at key
    have htop : F.coeff (m + 1) • (↑u : B) ^ (m + 1 - (m + 1)) = 1 := by
      have hc1 : F.coeff (m + 1) = 1 := by
        have := Polynomial.Monic.coeff_natDegree hFm
        rwa [hn] at this
      rw [hc1, Nat.sub_self, pow_zero, one_smul]
    rw [htop] at key

    have hsum : (∑ i ∈ Finset.range (m + 1), F.coeff i • (↑u : B) ^ (m + 1 - i)) = -1 :=
      eq_neg_of_add_eq_zero_left key

    have hpull : ∀ i ∈ Finset.range (m + 1),
        F.coeff i • (↑u : B) ^ (m + 1 - i) = f a * (F.coeff i • f (a ^ (m - i))) := by
      intro i hi
      have hile : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hexp : m + 1 - i = (m - i) + 1 := by omega
      rw [hexp, pow_succ, hu, ← map_pow, mul_smul_comm,
        mul_comm (f (a ^ (m - i))) (f a)]
    rw [Finset.sum_congr rfl hpull, ← Finset.mul_sum] at hsum

    have himg : f (∑ i ∈ Finset.range (m + 1), F.coeff i • a ^ (m - i)) =
        ∑ i ∈ Finset.range (m + 1), F.coeff i • f (a ^ (m - i)) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => map_smul f _ _
    rw [← himg] at hsum
    have hone : f (a * -(∑ i ∈ Finset.range (m + 1), F.coeff i • a ^ (m - i))) = f 1 := by
      rw [map_mul, map_neg, map_one, mul_neg, hsum, neg_neg]
    have hmul : a * -(∑ i ∈ Finset.range (m + 1), F.coeff i • a ^ (m - i)) = 1 := hf hone
    exact ⟨⟨a, -(∑ i ∈ Finset.range (m + 1), F.coeff i • a ^ (m - i)), hmul,
      by rwa [mul_comm] at hmul⟩, rfl⟩

p2m_open_scoped "FinFlatHopf" in

theorem FinFlatHopf.isLocalRing_of_points_cong
    (R C P : Type) [CommRing R] [CommRing C] [Nontrivial C] [CommRing P]
    [Algebra R C] [Algebra R P] [IsLocalRing P]
    (K : Type) [Finite K] [Nonempty K] (g : K → (C →ₐ[R] P))
    (hinj : Function.Injective (fun (c : C) (k : K) => g k c))
    (hintP : ∀ x : P, IsIntegral R x)
    (hcong : ∀ k l : K, ∀ c : C, g k c - g l c ∈ IsLocalRing.maximalIdeal P) :
    IsLocalRing C := by
  classical
  haveI := Fintype.ofFinite K
  obtain ⟨k₀⟩ := ‹Nonempty K›
  set D : Ideal C := (IsLocalRing.maximalIdeal P).comap (g k₀) with hD

  have hDnon : ∀ c : C, c ∈ D → c ∈ nonunits C := by
    intro c hc hcu
    have h2 : g k₀ c ∈ IsLocalRing.maximalIdeal P := hc
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h2
    exact h2 (hcu.map (g k₀))

  have hnonD : ∀ c : C, c ∈ nonunits C → c ∈ D := by
    intro c
    rw [← not_imp_not]
    intro hcD
    rw [mem_nonunits_iff, not_not]

    have hu : ∀ k : K, IsUnit (g k c) := by
      intro k
      by_contra hk
      refine hcD ?_
      have h1 : g k c ∈ IsLocalRing.maximalIdeal P := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        exact hk
      have heq : g k₀ c = (g k₀ c - g k c) + g k c := by ring
      show g k₀ c ∈ IsLocalRing.maximalIdeal P
      rw [heq]
      exact Ideal.add_mem _ (hcong k₀ k c) h1

    obtain ⟨ev, hevcoe⟩ : ∃ ev : C →ₐ[R] (K → P), ⇑ev = fun (c : C) (k : K) => g k c :=
      ⟨Pi.algHom R (fun _ : K => P) (fun k => g k), rfl⟩
    have hevinj : Function.Injective ev := by
      rw [hevcoe]
      exact hinj
    have huT : IsUnit (ev c) := by
      have hc : ev c = fun k => g k c := congrFun hevcoe c
      rw [hc]
      exact Pi.isUnit_iff.mpr hu
    obtain ⟨u, hu'⟩ := huT
    have hyint : IsIntegral R ((↑u⁻¹ : K → P)) := by
      choose p hmon hz using fun k => hintP ((↑u⁻¹ : K → P) k)
      refine ⟨∏ k, p k, Polynomial.monic_prod_of_monic _ _ (fun k _ => hmon k), ?_⟩
      rw [← Polynomial.aeval_def]
      funext k
      have hcomp : (Polynomial.aeval ((↑u⁻¹ : K → P)) (∏ j, p j)) k =
          Polynomial.aeval ((↑u⁻¹ : K → P) k) (∏ j, p j) := by
        exact (Polynomial.aeval_algHom_apply (Pi.evalAlgHom _ _ k) _ _).symm
      rw [Pi.zero_apply, hcomp, map_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ k) (hz k)
    exact FinFlatHopf.isUnit_of_injective_of_integral_inv ev hevinj u hu' hyint

  refine IsLocalRing.of_nonunits_add ?_
  intro a b ha hb
  exact hDnon _ (D.add_mem (hnonD a ha) (hnonD b hb))

#print axioms FinFlatHopf.isUnit_of_injective_of_integral_inv
#print axioms FinFlatHopf.isLocalRing_of_points_cong

set_option autoImplicit false

noncomputable section

namespace FinFlatHopf
p2m_export "FinFlatHopf" "not_isLocalRing_dual_of_isLocalRing inertiaFixed_valuationSubring_dvr_fixer_le_inertia dualPoints_equiv_monoidHom"
namespace W4
p2m_open "FinFlatHopf"

open WithConv

abbrev Pts (R C : Type) [CommRing R] [CommRing C] [Algebra R C]
    [Algebra R (AlgebraicClosure ℚ)] : Type :=
  WithConv (C →ₐ[R] AlgebraicClosure ℚ)

abbrev DPts (R C : Type) [CommRing R] [CommRing C] [Bialgebra R C]
    [Algebra R (AlgebraicClosure ℚ)] : Type :=
  WithConv (CartierDual R C →ₐ[R] AlgebraicClosure ℚ)

abbrev Nadd (R C : Type) [CommRing R] [CommRing C] [Bialgebra R C]
    [Algebra R (AlgebraicClosure ℚ)] : Type :=
  Additive (Pts R C →* (AlgebraicClosure ℚ)ˣ)

def ipAct {R C : Type} [CommRing R] [CommRing C] [Bialgebra R C] [Coalgebra.IsCocomm R C]
    [Module.Finite R C] [Module.Free R C] [Algebra R (AlgebraicClosure ℚ)]
    (eW3 : DPts R C ≃* (Pts R C →* (AlgebraicClosure ℚ)ˣ))
    (IP : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hIP : ∀ σ, σ ∈ IP ↔ FixesBase R σ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ IP) (x : Nadd R C) : Nadd R C :=
  Additive.ofMul (eW3 (compPoint σ ((hIP σ).mp hσ) (eW3.symm (Additive.toMul x))))

end FinFlatHopf.W4
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"

end
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"

set_option autoImplicit false

namespace FinFlatHopf
p2m_export "FinFlatHopf" "not_isLocalRing_dual_of_isLocalRing inertiaFixed_valuationSubring_dvr_fixer_le_inertia dualPoints_equiv_monoidHom"
p2m_open "FinFlatHopf"

theorem exists_stable_addSubgroup_card_eq
    {R : Type*} [CommRing R] [IsLocalRing R] (p : ℕ) (hpr : p.Prime)
    (hRp : Nat.card (IsLocalRing.ResidueField R) = p)
    {M : Type*} [AddCommGroup M] [Module R M] [Finite M]
    (V : Set R)
    (N₀ : AddSubgroup M) (hN₀V : ∀ v ∈ V, ∀ m ∈ N₀, v • m ∈ N₀)
    (hne : ∃ x ∈ N₀, x ≠ 0) :
    ∃ A : AddSubgroup M, A ≤ N₀ ∧ Nat.card A = p ∧ ∀ v ∈ V, ∀ a ∈ A, v • a ∈ A := by
  classical
  obtain ⟨x₀, hx₀N, hx₀ne⟩ := hne

  have hI : Module.annihilator R M ≠ ⊤ := by
    intro h
    have h1 : (1 : R) ∈ Module.annihilator R M := h ▸ Submodule.mem_top
    exact hx₀ne (by simpa using Module.mem_annihilator.mp h1 x₀)
  haveI : Nontrivial (R ⧸ Module.annihilator R M) := Ideal.Quotient.nontrivial_iff.mpr hI
  haveI : IsLocalRing (R ⧸ Module.annihilator R M) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  haveI : Finite (R ⧸ Module.annihilator R M) := by
    haveI : Finite (AddMonoid.End M) :=
      Finite.of_injective (fun f : AddMonoid.End M => (f : M → M)) DFunLike.coe_injective
    exact Finite.of_injective _ (RingHom.kerLift_injective (Module.toAddMonoidEnd R M))
  have hRqres : Nat.card (IsLocalRing.ResidueField (R ⧸ Module.annihilator R M)) = p := by
    rw [← hRp]
    let φ : R →+* IsLocalRing.ResidueField (R ⧸ Module.annihilator R M) :=
      (IsLocalRing.residue _).comp (Ideal.Quotient.mk _)
    have hφ : Function.Surjective φ :=
      (IsLocalRing.residue_surjective).comp Ideal.Quotient.mk_surjective
    have hker : RingHom.ker φ = IsLocalRing.maximalIdeal R :=
      IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective φ hφ)
    have e₁ : R ⧸ RingHom.ker φ ≃+* IsLocalRing.ResidueField (R ⧸ Module.annihilator R M) :=
      RingHom.quotientKerEquivOfSurjective hφ
    have e₂ : R ⧸ RingHom.ker φ ≃+* IsLocalRing.ResidueField R := Ideal.quotEquivOfEq hker
    exact (Nat.card_congr e₁.toEquiv).symm.trans (Nat.card_congr e₂.toEquiv)

  let S : Subring (R ⧸ Module.annihilator R M) :=
    Subring.closure ((Ideal.Quotient.mk (Module.annihilator R M)) '' V)
  obtain ⟨hSloc, hSres⟩ :=
    isLocalRing_subring_of_finite (R ⧸ Module.annihilator R M) p hpr hRqres S
  haveI := hSloc

  letI instRbar : Module (R ⧸ Module.annihilator R M) M := Module.quotientAnnihilator
  letI instS : Module S M := Module.compHom M S.subtype

  have hN0S : ∀ (s : S) (m : M), m ∈ N₀ → s • m ∈ N₀ := by
    suffices h : ∀ x ∈ S, ∀ m ∈ N₀, x • m ∈ N₀ from fun s m hm => h s.1 s.2 m hm
    intro x hx
    refine Subring.closure_induction (p := fun x _ => ∀ m ∈ N₀, x • m ∈ N₀)
      ?_ ?_ ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨v, hv, rfl⟩ m hm
      show v • m ∈ N₀
      exact hN₀V v hv m hm
    · intro m _
      rw [zero_smul]
      exact N₀.zero_mem
    · intro m hm
      rw [one_smul]
      exact hm
    · intro x y _ _ hx hy m hm
      rw [add_smul]
      exact N₀.add_mem (hx m hm) (hy m hm)
    · intro x _ hx m hm
      rw [neg_smul]
      exact N₀.neg_mem (hx m hm)
    · intro x y _ _ hx hy m hm
      rw [mul_smul]
      exact hx _ (hy m hm)

  let N0' : Submodule S M :=
    { carrier := N₀
      add_mem' := fun ha hb => N₀.add_mem ha hb
      zero_mem' := N₀.zero_mem
      smul_mem' := fun s m hm => hN0S s m hm }
  haveI : Finite N0' := Finite.of_injective (fun x : N0' => (x : M)) Subtype.val_injective
  have hN0ne : ∃ m : N0', m ≠ 0 := ⟨⟨x₀, hx₀N⟩, fun h => hx₀ne (congrArg Subtype.val h)⟩

  obtain ⟨A', hA'card⟩ := exists_submodule_card_eq_residue S p hSres N0' hN0ne
  refine ⟨(A'.map N0'.subtype).toAddSubgroup, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, -, rfl⟩ := Submodule.mem_map.mp hx
    exact a.2
  · rw [← hA'card]
    exact (Nat.card_congr
      (Submodule.equivMapOfInjective N0'.subtype N0'.injective_subtype A').toEquiv).symm
  · intro v hv x hx
    obtain ⟨a, haA, rfl⟩ := Submodule.mem_map.mp hx
    have hvS : Ideal.Quotient.mk (Module.annihilator R M) v ∈ S :=
      Subring.subset_closure ⟨v, hv, rfl⟩
    exact Submodule.mem_map.mpr ⟨(⟨_, hvS⟩ : S) • a, A'.smul_mem _ haA, rfl⟩

end FinFlatHopf
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"

set_option autoImplicit false

noncomputable section

namespace FinFlatHopf
p2m_export "FinFlatHopf" "not_isLocalRing_dual_of_isLocalRing inertiaFixed_valuationSubring_dvr_fixer_le_inertia dualPoints_equiv_monoidHom"
namespace W4
p2m_open "FinFlatHopf"

section quotient

lemma natCard_residueField_quotient (R : Type) [CommRing R] [IsLocalRing R] (I : Ideal R)
    (hI : I ≠ ⊤) :
    haveI := Ideal.Quotient.nontrivial_iff.mpr hI
    haveI : IsLocalRing (R ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    Nat.card (IsLocalRing.ResidueField (R ⧸ I)) = Nat.card (IsLocalRing.ResidueField R) := by
  haveI := Ideal.Quotient.nontrivial_iff.mpr hI
  haveI : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let φ : R →+* IsLocalRing.ResidueField (R ⧸ I) :=
    (IsLocalRing.residue (R ⧸ I)).comp (Ideal.Quotient.mk I)
  have hφ : Function.Surjective φ :=
    (IsLocalRing.residue_surjective).comp Ideal.Quotient.mk_surjective
  have hker : RingHom.ker φ = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective φ hφ)
  have e₁ : R ⧸ RingHom.ker φ ≃+* IsLocalRing.ResidueField (R ⧸ I) :=
    RingHom.quotientKerEquivOfSurjective hφ
  have e₂ : R ⧸ RingHom.ker φ ≃+* IsLocalRing.ResidueField R := Ideal.quotEquivOfEq hker
  exact (Nat.card_congr e₁.toEquiv).symm.trans (Nat.card_congr e₂.toEquiv)

end quotient
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"

section quotAnn

variable (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M]

abbrev Rbar : Type := R ⧸ Module.annihilator R M

abbrev moduleRbar : Module (Rbar R M) M := Module.quotientAnnihilator

lemma mk_smul_eq (r : R) (m : M) :
    letI := moduleRbar R M
    (Ideal.Quotient.mk (Module.annihilator R M) r) • m = r • m := rfl

scoped instance finite_Rbar [Finite M] : Finite (Rbar R M) := by
  haveI : Finite (AddMonoid.End M) :=
    Finite.of_injective (fun f : AddMonoid.End M => (f : M → M)) DFunLike.coe_injective
  exact Finite.of_injective _ (RingHom.kerLift_injective (Module.toAddMonoidEnd R M))

variable {R M} in
lemma annihilator_ne_top [Nontrivial M] : Module.annihilator R M ≠ ⊤ := by
  intro h
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  have h1 : (1 : R) ∈ Module.annihilator R M := h ▸ Submodule.mem_top
  exact hm (by simpa using Module.mem_annihilator.mp h1 m)

scoped instance nontrivial_Rbar [Nontrivial M] : Nontrivial (Rbar R M) :=
  Ideal.Quotient.nontrivial_iff.mpr annihilator_ne_top

scoped instance isLocalRing_Rbar [IsLocalRing R] [Nontrivial M] : IsLocalRing (Rbar R M) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

lemma natCard_residueField_Rbar [IsLocalRing R] [Nontrivial M] :
    Nat.card (IsLocalRing.ResidueField (Rbar R M)) = Nat.card (IsLocalRing.ResidueField R) :=
  natCard_residueField_quotient R _ annihilator_ne_top

end quotAnn
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"

section scal

variable (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M]
  (u : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → Rˣ)
  (IP : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))

def scalSubring : Subring (Rbar R M) :=
  Subring.closure
    ((fun σ => Ideal.Quotient.mk (Module.annihilator R M) (u σ : R)) '' (IP : Set _))

abbrev Scal : Type := ↥(scalSubring R M u IP)

abbrev moduleScal : Module (Scal R M u IP) M :=
  letI := moduleRbar R M
  Module.compHom M (scalSubring R M u IP).subtype

lemma scal_smul_def (r : Scal R M u IP) (m : M) :
    letI := moduleScal R M u IP
    letI := moduleRbar R M
    r • m = (r : Rbar R M) • m := rfl

lemma isLocalRing_scal [IsLocalRing R] [Finite M] [Nontrivial M] (p : ℕ) (hp : p.Prime)
    (hR : Nat.card (IsLocalRing.ResidueField R) = p) :
    ∃ _ : IsLocalRing (Scal R M u IP),
      Nat.card (IsLocalRing.ResidueField (Scal R M u IP)) = p :=
  FinFlatHopf.isLocalRing_subring_of_finite (Rbar R M) p hp
    ((natCard_residueField_Rbar R M).trans hR) (scalSubring R M u IP)

lemma exists_scal_smul_eq
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) M]
    (hu : ∀ σ ∈ IP, ∀ m : M, σ • m = (u σ : R) • m) :
    letI := moduleScal R M u IP
    ∀ σ ∈ IP, ∃ r : Scal R M u IP, ∀ m : M, σ • m = r • m := by
  letI := moduleScal R M u IP
  intro σ hσ
  exact ⟨⟨Ideal.Quotient.mk _ (u σ : R), Subring.subset_closure ⟨σ, hσ, rfl⟩⟩,
    fun m => hu σ hσ m⟩

lemma scal_smul_mem
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) M]
    (hu : ∀ σ ∈ IP, ∀ m : M, σ • m = (u σ : R) • m)
    (K : AddSubgroup M) (hK : ∀ σ ∈ IP, ∀ m ∈ K, σ • m ∈ K) :
    letI := moduleScal R M u IP
    ∀ (r : Scal R M u IP) (m : M), m ∈ K → r • m ∈ K := by
  letI := moduleRbar R M
  letI := moduleScal R M u IP
  suffices h : ∀ x ∈ scalSubring R M u IP, ∀ m ∈ K, x • m ∈ K from
    fun r m hm => h r.1 r.2 m hm
  intro x hx
  refine Subring.closure_induction (p := fun x _ => ∀ m ∈ K, x • m ∈ K)
    ?_ ?_ ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨σ, hσ, rfl⟩ m hm
    show (u σ : R) • m ∈ K
    rw [← hu σ hσ m]
    exact hK σ hσ m hm
  · intro m _
    rw [zero_smul]
    exact K.zero_mem
  · intro m hm
    rw [one_smul]
    exact hm
  · intro x y _ _ hx hy m hm
    rw [add_smul]
    exact K.add_mem (hx m hm) (hy m hm)
  · intro x _ hx m hm
    rw [neg_smul]
    exact K.neg_mem (hx m hm)
  · intro x y _ _ hx hy m hm
    rw [mul_smul]
    exact hx _ (hy m hm)

abbrev moduleK
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) M]
    (hu : ∀ σ ∈ IP, ∀ m : M, σ • m = (u σ : R) • m)
    (K : AddSubgroup M) (hK : ∀ σ ∈ IP, ∀ m ∈ K, σ • m ∈ K) :
    Module (Scal R M u IP) ↥K :=
  letI := moduleScal R M u IP
  letI : SMul (Scal R M u IP) ↥K :=
    ⟨fun r k => ⟨r • (k : M), scal_smul_mem R M u IP hu K hK r k k.2⟩⟩
  Function.Injective.module (Scal R M u IP) K.subtype (fun _ _ h => Subtype.ext h)
    (fun _ _ => rfl)

lemma coe_smulK
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) M]
    (hu : ∀ σ ∈ IP, ∀ m : M, σ • m = (u σ : R) • m)
    (K : AddSubgroup M) (hK : ∀ σ ∈ IP, ∀ m ∈ K, σ • m ∈ K)
    (r : Scal R M u IP) (k : ↥K) :
    letI := moduleK R M u IP hu K hK
    letI := moduleScal R M u IP
    ((r • k : ↥K) : M) = r • (k : M) := rfl

end scal
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"

end FinFlatHopf.W4
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"

end
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"

set_option autoImplicit false

noncomputable section

namespace FinFlatHopf
p2m_export "FinFlatHopf" "not_isLocalRing_dual_of_isLocalRing inertiaFixed_valuationSubring_dvr_fixer_le_inertia dualPoints_equiv_monoidHom"
namespace W4
p2m_open "FinFlatHopf"

open WithConv

theorem hscal_of_hu
    {B X C M Kadd Rsc : Type} [CommRing B] [CommRing X] [CommRing C] [Bialgebra B X]
    [Bialgebra B C] [Algebra B (AlgebraicClosure ℚ)] [AddCommGroup M]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) M]
    (e' : WithConv (X →ₐ[B] AlgebraicClosure ℚ) ≃ M)
    (he'_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (X →ₐ[B] AlgebraicClosure ℚ)),
      (∀ x : X, g x = σ (f x)) → e' g = σ • e' f)
    (IP : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hIP : ∀ σ, σ ∈ IP ↔ FixesBase B σ)
    [CommRing Rsc] [Module Rsc M]
    (mkR : ∀ σ ∈ IP, ∃ r : Rsc, ∀ m : M, σ • m = r • m)
    (π : X →ₐc[B] C)
    [AddCommGroup Kadd] [Module Rsc Kadd] (eC : Pts B C ≃ Kadd)
    (jK : Kadd → M) (hjK : Function.Injective jK)
    (hj : ∀ f : Pts B C, jK (eC f) = e' (pullPoint π f))
    (hjsmul : ∀ (r : Rsc) (k : Kadd), jK (r • k) = r • jK k) :
    ∀ σ (hσ : σ ∈ IP), ∃ r : Rsc, ∀ f : Pts B C,
      eC (compPoint σ ((hIP σ).mp hσ) f) = r • eC f := by
  intro σ hσ
  obtain ⟨r, hr⟩ := mkR σ hσ
  refine ⟨r, fun f => hjK ?_⟩
  rw [hjsmul, hj, hj, ← hr]
  exact he'_act σ (pullPoint π f) (pullPoint π (compPoint σ ((hIP σ).mp hσ) f))
    (pullPoint_pointwise π (fun y => σ y) f _ (fun _ => rfl))

end FinFlatHopf.W4
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"

end
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"

set_option autoImplicit false

noncomputable section

namespace FinFlatHopf
p2m_export "FinFlatHopf" "not_isLocalRing_dual_of_isLocalRing inertiaFixed_valuationSubring_dvr_fixer_le_inertia dualPoints_equiv_monoidHom"
namespace W4
p2m_open "FinFlatHopf"

open WithConv

section hLoc

variable (R : Type) [CommRing R] [Algebra R (AlgebraicClosure ℚ)]
  (P : ValuationSubring (AlgebraicClosure ℚ))
  (hRP : ∀ r : R, algebraMap R (AlgebraicClosure ℚ) r ∈ P)

abbrev algebraP : Algebra R P :=
  RingHom.toAlgebra
    { toFun := fun r => ⟨algebraMap R (AlgebraicClosure ℚ) r, hRP r⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }

def valAlgHom : letI := algebraP R P hRP; P →ₐ[R] AlgebraicClosure ℚ :=
  letI := algebraP R P hRP
  { toFun := fun y => (y : AlgebraicClosure ℚ)
    map_one' := rfl
    map_mul' := fun _ _ => rfl
    map_zero' := rfl
    map_add' := fun _ _ => rfl
    commutes' := fun _ => rfl }

def liftPt {X : Type} [CommRing X] [Algebra R X] (g : X →ₐ[R] AlgebraicClosure ℚ)
    (hg : ∀ x : X, g x ∈ P) : letI := algebraP R P hRP; X →ₐ[R] P :=
  letI := algebraP R P hRP
  { toFun := fun x => ⟨g x, hg x⟩
    map_one' := Subtype.ext (map_one g)
    map_mul' := fun a b => Subtype.ext (map_mul g a b)
    map_zero' := Subtype.ext (map_zero g)
    map_add' := fun a b => Subtype.ext (map_add g a b)
    commutes' := fun r => Subtype.ext (g.commutes r) }

include hRP in

theorem isLocalRing_of_card_of_redTriv [IsDomain R]
    (hRinj : Function.Injective (algebraMap R (AlgebraicClosure ℚ)))
    (hintP : ∀ x : AlgebraicClosure ℚ, x ∈ P → IsIntegral R x)
    (X : Type) [CommRing X] [HopfAlgebra R X] [Module.Finite R X] [Module.Free R X]
    (hcard : Nat.card (WithConv (X →ₐ[R] AlgebraicClosure ℚ)) = Module.finrank R X)
    (hred : ∀ g : X →ₐ[R] AlgebraicClosure ℚ, RedTriv P (toConv g)) : IsLocalRing X := by
  classical
  letI := algebraP R P hRP

  haveI hfinW : Finite (WithConv (X →ₐ[R] AlgebraicClosure ℚ)) :=
    FinFlatHopf.finite_withConv_algHom R X (AlgebraicClosure ℚ)
  let ε : WithConv (X →ₐ[R] AlgebraicClosure ℚ) ≃ (X →ₐ[R] AlgebraicClosure ℚ) :=
    ⟨WithConv.ofConv, WithConv.toConv, fun _ => rfl, fun _ => rfl⟩
  haveI hfin : Finite (X →ₐ[R] AlgebraicClosure ℚ) := Finite.of_equiv _ ε
  have hcard' : Nat.card (X →ₐ[R] AlgebraicClosure ℚ) = Module.finrank R X := by
    rw [← Nat.card_congr ε]
    exact hcard

  haveI : Nonempty (X →ₐ[R] AlgebraicClosure ℚ) :=
    ⟨(Algebra.ofId R (AlgebraicClosure ℚ)).comp (Bialgebra.counitAlgHom R X)⟩
  haveI : Nontrivial X :=
    Module.nontrivial_of_finrank_pos (R := R) (by rw [← hcard']; exact Nat.card_pos)

  have hval : ValuesIn (S := R) (X := X) P := valuesIn_of_finite (X := X) P hRP
  let gP : (X →ₐ[R] AlgebraicClosure ℚ) → (X →ₐ[R] P) := fun g => liftPt R P hRP g (hval g)
  have hinj : Function.Injective (fun (c : X) (k : X →ₐ[R] AlgebraicClosure ℚ) => gP k c) := by
    intro c c' h
    apply FinFlatHopf.injective_eval_points R X (AlgebraicClosure ℚ) hRinj hfin hcard'
    funext k
    exact congrArg Subtype.val (congrFun h k)
  have hintP' : ∀ y : P, IsIntegral R y := fun y =>
    (isIntegral_algHom_iff (valAlgHom R P hRP) (fun a b h => Subtype.ext h)).mp (hintP y.1 y.2)
  have hcong : ∀ (k l : X →ₐ[R] AlgebraicClosure ℚ) (c : X),
      gP k c - gP l c ∈ IsLocalRing.maximalIdeal P := by
    intro k l c
    rw [ValuationSubring.valuation_lt_one_iff]
    have hkl : Cong P (toConv k) (toConv l) :=
      cong_trans P ((redTriv_iff_cong_one P _).mp (hred k))
        (cong_symm P ((redTriv_iff_cong_one P _).mp (hred l)))
    exact hkl c
  exact FinFlatHopf.isLocalRing_of_points_cong R X P (X →ₐ[R] AlgebraicClosure ℚ) gP hinj
    hintP' hcong

end hLoc
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"

end FinFlatHopf.W4
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"

end
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"

set_option autoImplicit false

noncomputable section

namespace FinFlatHopf
p2m_export "FinFlatHopf" "not_isLocalRing_dual_of_isLocalRing inertiaFixed_valuationSubring_dvr_fixer_le_inertia dualPoints_equiv_monoidHom"
namespace W4
p2m_open "FinFlatHopf"

open WithConv
open Additive (ofMul toMul)

section exponent

lemma exists_pow_of_algEquiv (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (q : ℕ)
    [NeZero q] : ∃ a : ℕ, ∀ μ : AlgebraicClosure ℚ, μ ^ q = 1 → σ μ = μ ^ a := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) q
  have hσζ : (σ ζ) ^ q = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
  obtain ⟨a, -, ha⟩ := hζ.eq_pow_of_pow_eq_one hσζ
  refine ⟨a, fun μ hμ => ?_⟩
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ
  rw [map_pow, ← ha, ← pow_mul, ← pow_mul, mul_comm a i]

end exponent
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"

section transposeModule

variable {R C : Type} [CommRing R] [CommRing C] [Bialgebra R C]
  [Algebra R (AlgebraicClosure ℚ)]
  {Kadd : Type} [AddCommGroup Kadd] (eC : Pts R C ≃ Kadd)
  (heC : ∀ f g : Pts R C, eC (f * g) = eC f + eC g)
  {Rsc : Type} [CommRing Rsc] [Module Rsc Kadd]
include heC

def mulBy (r : Rsc) : Pts R C →* Pts R C where
  toFun f := eC.symm (r • eC f)
  map_one' := by rw [Equiv.symm_apply_eq, e_one eC heC, smul_zero]
  map_mul' f g := by rw [heC, smul_add, e_symm_add eC heC]

lemma mulBy_apply (r : Rsc) (f : Pts R C) : mulBy eC heC r f = eC.symm (r • eC f) := rfl

lemma mulBy_one' : mulBy eC heC (1 : Rsc) = MonoidHom.id _ :=
  MonoidHom.ext fun f => by
    show eC.symm ((1 : Rsc) • eC f) = f
    rw [one_smul, Equiv.symm_apply_apply]

lemma mulBy_mul (r s : Rsc) :
    mulBy eC heC (r * s) = (mulBy eC heC s).comp (mulBy eC heC r) :=
  MonoidHom.ext fun f => by
    show eC.symm ((r * s) • eC f) = eC.symm (s • eC (eC.symm (r • eC f)))
    rw [Equiv.apply_symm_apply, ← mul_smul, mul_comm r s]

lemma mulBy_zero (f : Pts R C) : mulBy eC heC (0 : Rsc) f = 1 := by
  show eC.symm ((0 : Rsc) • eC f) = 1
  rw [zero_smul, Equiv.symm_apply_eq, e_one eC heC]

lemma mulBy_add (r s : Rsc) (f : Pts R C) :
    mulBy eC heC (r + s) f = mulBy eC heC r f * mulBy eC heC s f := by
  show eC.symm ((r + s) • eC f) = eC.symm (r • eC f) * eC.symm (s • eC f)
  rw [add_smul, e_symm_add eC heC]

abbrev trModule : Module Rsc (Nadd R C) where
  smul r χ := ofMul ((toMul χ).comp (mulBy eC heC r))
  one_smul χ := by
    show ofMul ((toMul χ).comp (mulBy eC heC (1 : Rsc))) = χ
    rw [mulBy_one', MonoidHom.comp_id, ofMul_toMul]
  mul_smul r s χ := by
    show ofMul ((toMul χ).comp (mulBy eC heC (r * s))) =
      ofMul ((toMul (ofMul ((toMul χ).comp (mulBy eC heC s)))).comp (mulBy eC heC r))
    rw [mulBy_mul, toMul_ofMul, MonoidHom.comp_assoc]
  smul_zero r := by
    show ofMul ((toMul (0 : Nadd R C)).comp (mulBy eC heC r)) = 0
    have h : (toMul (0 : Nadd R C)).comp (mulBy eC heC r) = 1 := MonoidHom.ext fun _ => rfl
    rw [h]
    rfl
  smul_add r χ ψ := by
    show ofMul ((toMul (χ + ψ)).comp (mulBy eC heC r)) =
      ofMul (((toMul χ).comp (mulBy eC heC r)) * ((toMul ψ).comp (mulBy eC heC r)))
    congr 1
  add_smul r s χ := by
    show ofMul ((toMul χ).comp (mulBy eC heC (r + s))) =
      ofMul (((toMul χ).comp (mulBy eC heC r)) * ((toMul χ).comp (mulBy eC heC s)))
    congr 1
    exact MonoidHom.ext fun f => by
      show toMul χ (mulBy eC heC (r + s) f) = toMul χ (mulBy eC heC r f) * toMul χ (mulBy eC heC s f)
      rw [mulBy_add, map_mul]
  zero_smul χ := by
    show ofMul ((toMul χ).comp (mulBy eC heC (0 : Rsc))) = 0
    have h1 : (toMul χ).comp (mulBy eC heC (0 : Rsc)) = 1 := MonoidHom.ext fun f => by
      show toMul χ (mulBy eC heC (0 : Rsc) f) = 1
      rw [mulBy_zero, map_one]
    rw [h1]
    rfl

lemma trModule_smul_apply (r : Rsc) (χ : Nadd R C) (f : Pts R C) :
    letI := trModule eC heC (Rsc := Rsc)
    toMul (r • χ) f = toMul χ (eC.symm (r • eC f)) := rfl

end transposeModule
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"

theorem hS7_of_scalar
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (R : Type) [CommRing R] [Algebra R (AlgebraicClosure ℚ)]
    (IP : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hIP : ∀ σ, σ ∈ IP ↔ FixesBase R σ)
    (C : Type) [CommRing C] [HopfAlgebra R C] [Coalgebra.IsCocomm R C] [Module.Finite R C]
    [Module.Free R C]
    [Finite (DPts R C)]
    (Kadd : Type) [AddCommGroup Kadd]
    (eC : Pts R C ≃ Kadd) (heC : ∀ f g, eC (f * g) = eC f + eC g)
    (hq : ∀ k : Kadd, (p ^ n) • k = 0)
    (eW3 : DPts R C ≃* (Pts R C →* (AlgebraicClosure ℚ)ˣ))
    (hequivW3 : ∀ (τ : AlgebraicClosure ℚ ≃ₐ[R] AlgebraicClosure ℚ) (g : DPts R C) (f : Pts R C),
      ((eW3 (toConv (τ.toAlgHom.comp g.ofConv)) f : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) =
        τ ((eW3 g (toConv (τ.symm.toAlgHom.comp f.ofConv)) : (AlgebraicClosure ℚ)ˣ) :
          AlgebraicClosure ℚ))
    (Rsc : Type) [CommRing Rsc] [IsLocalRing Rsc]
    (hRp : Nat.card (IsLocalRing.ResidueField Rsc) = p)
    [Module Rsc Kadd]
    (hscal : ∀ σ (hσ : σ ∈ IP), ∃ r : Rsc, ∀ f : Pts R C,
      eC (compPoint σ ((hIP σ).mp hσ) f) = r • eC f) :
    ∀ N0 : AddSubgroup (Nadd R C),
      (∀ σ (hσ : σ ∈ IP) (x : Nadd R C), x ∈ N0 → ipAct eW3 IP hIP σ hσ x ∈ N0) → N0 ≠ ⊥ →
      ∃ A : AddSubgroup (Nadd R C), A ≤ N0 ∧ Nat.card A = p ∧
        ∀ σ (hσ : σ ∈ IP) (x : Nadd R C), x ∈ A → ipAct eW3 IP hIP σ hσ x ∈ A := by
  intro N0 hN0 hne
  classical
  letI := trModule eC heC (Rsc := Rsc)
  haveI : Finite (Nadd R C) := Finite.of_equiv _ (eW3.toEquiv.trans Additive.ofMul)
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩

  have hpow : ∀ (f : Pts R C) (m : ℕ), eC (f ^ m) = m • eC f := by
    intro f m
    induction m with
    | zero => rw [pow_zero, zero_nsmul, e_one eC heC]
    | succ m ih => rw [pow_succ, heC, ih, succ_nsmul]
  have htor : ∀ f : Pts R C, f ^ (p ^ n) = 1 := fun f =>
    eC.injective (by rw [hpow, hq, e_one eC heC])
  have hval1 : ∀ (χ : Pts R C →* (AlgebraicClosure ℚ)ˣ) (f : Pts R C),
      ((χ f : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ^ (p ^ n) = 1 := by
    intro χ f
    rw [← Units.val_pow_eq_pow_val, ← map_pow, htor, map_one, Units.val_one]

  have key : ∀ σ (hσ : σ ∈ IP), ∃ v : Rsc, ∀ χ : Nadd R C, ipAct eW3 IP hIP σ hσ χ = v • χ := by
    intro σ hσ
    obtain ⟨a, ha⟩ := exists_pow_of_algEquiv σ (p ^ n)
    have hσ' : σ⁻¹ ∈ IP := IP.inv_mem hσ
    obtain ⟨r, hr⟩ := hscal σ⁻¹ hσ'
    have hfix : FixesBase R σ := (hIP σ).mp hσ
    refine ⟨(a : Rsc) * r, fun χ => ?_⟩
    apply toMul.injective
    apply MonoidHom.ext
    intro f
    apply Units.ext

    have hpt : toConv ((fixAlgEquiv σ hfix).symm.toAlgHom.comp f.ofConv) =
        compPoint σ⁻¹ ((hIP σ⁻¹).mp hσ') f := by
      apply ofConv_injective
      ext x
      rfl
    have hχg : eW3 (eW3.symm (toMul χ)) = toMul χ := MulEquiv.apply_symm_apply eW3 _

    have lhs : ((toMul (ipAct eW3 IP hIP σ hσ χ) f : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)
        = σ ((toMul χ (compPoint σ⁻¹ ((hIP σ⁻¹).mp hσ') f) : (AlgebraicClosure ℚ)ˣ) :
            AlgebraicClosure ℚ) := by
      show ((eW3 (compPoint σ hfix (eW3.symm (toMul χ))) f : (AlgebraicClosure ℚ)ˣ) :
          AlgebraicClosure ℚ) = _
      rw [← toConv_toAlgHom_comp σ hfix (eW3.symm (toMul χ)),
        hequivW3 (fixAlgEquiv σ hfix) (eW3.symm (toMul χ)) f, hχg, hpt, fixAlgEquiv_apply]

    have rhs : ((toMul (((a : Rsc) * r) • χ) f : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)
        = ((toMul χ (compPoint σ⁻¹ ((hIP σ⁻¹).mp hσ') f) : (AlgebraicClosure ℚ)ˣ) :
            AlgebraicClosure ℚ) ^ a := by
      show ((toMul χ (eC.symm (((a : Rsc) * r) • eC f)) : (AlgebraicClosure ℚ)ˣ) :
          AlgebraicClosure ℚ) = _
      rw [mul_smul, Nat.cast_smul_eq_nsmul Rsc, ← hr f, ← hpow, Equiv.symm_apply_apply, map_pow,
        Units.val_pow_eq_pow_val]
    rw [lhs, rhs]
    exact ha _ (hval1 (toMul χ) _)

  let V : Set Rsc := {v | ∃ σ, ∃ hσ : σ ∈ IP, ∀ χ : Nadd R C, ipAct eW3 IP hIP σ hσ χ = v • χ}
  have hN0V : ∀ v ∈ V, ∀ m ∈ N0, v • m ∈ N0 := by
    rintro v ⟨σ, hσ, hv⟩ m hm
    rw [← hv m]
    exact hN0 σ hσ m hm

  obtain ⟨A, hAN0, hcard, hAV⟩ :=
    FinFlatHopf.exists_stable_addSubgroup_card_eq (R := Rsc) (M := Nadd R C) p (Fact.out) hRp V N0
      (fun v hv m hm => hN0V v hv m hm)
      (by
        obtain ⟨x, hx⟩ := AddSubgroup.ne_bot_iff_exists_ne_zero.mp hne
        exact ⟨x.1, x.2, fun h => hx (Subtype.ext h)⟩)
  refine ⟨A, hAN0, hcard, fun σ hσ x hx => ?_⟩
  obtain ⟨v, hv⟩ := key σ hσ
  rw [hv x]
  exact hAV v ⟨σ, hσ, hv⟩ x hx

end FinFlatHopf.W4
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"

end
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"

set_option autoImplicit false

noncomputable section

namespace FinFlatHopf
p2m_export "FinFlatHopf" "not_isLocalRing_dual_of_isLocalRing inertiaFixed_valuationSubring_dvr_fixer_le_inertia dualPoints_equiv_monoidHom"
namespace W4
p2m_open "FinFlatHopf"

open WithConv

section core

variable {G : Type} [CommGroup G] [Finite G]

lemma eq_of_forall_monoidHom_apply_eq {x y : G}
    (h : ∀ χ : G →* (AlgebraicClosure ℚ)ˣ, χ x = χ y) : x = y := by
  haveI : NeZero ((Monoid.exponent G : ℕ) : ℚ) :=
    ⟨Nat.cast_ne_zero.mpr Monoid.exponent_ne_zero_of_finite⟩
  exact (CommGroup.forall_apply_eq_apply_iff G).mp h

theorem eq_pow_of_characters (τ : AlgebraicClosure ℚ → AlgebraicClosure ℚ) (T : G → G)
    (q a : ℕ) (hτ : ∀ μ : AlgebraicClosure ℚ, μ ^ q = 1 → τ μ = μ ^ a)
    (hG : ∀ k : G, k ^ q = 1)
    {I : Type} (Φ : I → (G →* (AlgebraicClosure ℚ)ˣ)) (hΦ : Function.Surjective Φ)
    (hT : ∀ (i : I) (k : G), ((Φ i (T k) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) =
      τ ((Φ i k : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ))
    (k : G) : T k = k ^ a := by
  apply eq_of_forall_monoidHom_apply_eq
  intro χ
  obtain ⟨i, rfl⟩ := hΦ χ
  apply Units.ext
  rw [hT i k, map_pow, Units.val_pow_eq_pow_val]
  apply hτ
  rw [← Units.val_pow_eq_pow_val, ← map_pow, hG k, map_one, Units.val_one]

end core
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"

section transport

variable {M₀ G : Type} [CommMonoid M₀] [CommGroup G] (ε : M₀ ≃ G)
  (hε : ∀ f g : M₀, ε (f * g) = ε f * ε g)
include hε

lemma transport_map_one : ε 1 = 1 := by
  have h := hε 1 1
  rw [one_mul] at h
  simpa using h

def symmHom : G →* M₀ where
  toFun := ε.symm
  map_one' := by
    apply ε.injective
    rw [Equiv.apply_symm_apply, transport_map_one ε hε]
  map_mul' x y := by
    apply ε.injective
    rw [hε, Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

def toHom : M₀ →* G where
  toFun := ε
  map_one' := transport_map_one ε hε
  map_mul' := hε

@[scoped simp] lemma symmHom_apply (x : G) : symmHom ε hε x = ε.symm x := rfl
@[scoped simp] lemma toHom_apply (f : M₀) : toHom ε hε f = ε f := rfl

lemma surjective_comp_symmHom {I R : Type} [CommMonoid R] (pair : I → (M₀ →* R))
    (hpair : Function.Surjective pair) :
    Function.Surjective fun i => (pair i).comp (symmHom ε hε) := by
  intro χ
  obtain ⟨i, hi⟩ := hpair (χ.comp (toHom ε hε))
  refine ⟨i, ?_⟩
  ext x
  simp [hi]

end transport
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"

section pairingShape

variable {S C Ω N : Type} [CommRing S] [CommRing C] [Bialgebra S C] [Field Ω] [Algebra S Ω]

lemma pair_comp_eq_of_equivariant_of_trivial (pair : N → WithConv (C →ₐ[S] Ω) → Ω)
    (τ : Ω ≃ₐ[S] Ω) (actN : N → N)
    (hequiv : ∀ (g : N) (f : WithConv (C →ₐ[S] Ω)),
      pair (actN g) f = τ (pair g (toConv (τ.symm.toAlgHom.comp f.ofConv))))
    (htriv : ∀ g : N, actN g = g)
    (g : N) (f : WithConv (C →ₐ[S] Ω)) :
    pair g (toConv (τ.toAlgHom.comp f.ofConv)) = τ (pair g f) := by
  have hX : toConv (τ.symm.toAlgHom.comp (toConv (τ.toAlgHom.comp f.ofConv)).ofConv) = f := by
    apply ofConv_injective
    ext x
    exact τ.symm_apply_apply (f x)
  have h := hequiv g (toConv (τ.toAlgHom.comp f.ofConv))
  rw [htriv g, hX] at h
  exact h

end pairingShape
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"

end FinFlatHopf.W4
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"

end
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace FinFlatHopf
p2m_export "FinFlatHopf" "not_isLocalRing_dual_of_isLocalRing inertiaFixed_valuationSubring_dvr_fixer_le_inertia dualPoints_equiv_monoidHom"
namespace W4
p2m_open "FinFlatHopf"

variable (R A : Type) [CommRing R] [CommRing A] [Bialgebra R A]

def cartierDualEquivWithConv : CartierDual R A ≃+* WithConv (A →ₗ[R] R) where
  toFun φ := WithConv.toConv (CartierDual.toDual R A φ)
  invFun f := CartierDual.ofDual R A f.ofConv
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' φ ψ := by
    apply WithConv.ofConv_injective
    exact CartierDual.mul_eq_convMul φ ψ
  map_add' _ _ := rfl

@[scoped simp] lemma cartierDualEquivWithConv_apply (φ : CartierDual R A) :
    cartierDualEquivWithConv R A φ = WithConv.toConv (CartierDual.toDual R A φ) := rfl

@[scoped simp] lemma cartierDualEquivWithConv_symm_apply (f : WithConv (A →ₗ[R] R)) :
    (cartierDualEquivWithConv R A).symm f = CartierDual.ofDual R A f.ofConv := rfl

theorem isLocalRing_withConv_of_cartierDual [Coalgebra.IsCocomm R A]
    [IsLocalRing (CartierDual R A)] : IsLocalRing (WithConv (A →ₗ[R] R)) :=
  haveI : Nontrivial (WithConv (A →ₗ[R] R)) :=
    (cartierDualEquivWithConv R A).injective.nontrivial
  IsLocalRing.of_surjective' (cartierDualEquivWithConv R A).toRingHom
    (cartierDualEquivWithConv R A).surjective

end FinFlatHopf.W4
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"

end
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace FinFlatHopf
p2m_export "FinFlatHopf" "not_isLocalRing_dual_of_isLocalRing inertiaFixed_valuationSubring_dvr_fixer_le_inertia dualPoints_equiv_monoidHom"
namespace W4
p2m_open "FinFlatHopf"

theorem isLocalRing_of_injective_algHom {R X Y : Type} [CommRing R] [Ring X] [CommRing Y]
    [Algebra R X] [Algebra R Y] [Module.Finite R Y] [IsLocalRing Y]
    (ι : X →ₐ[R] Y) (hι : Function.Injective ι) : IsLocalRing X := by
  haveI : IsLocalRing ι.range := FinFlatHopf.isLocalRing_subalgebra_of_isIntegral ι.range
  haveI : Nontrivial X := (AlgEquiv.ofInjective ι hι).symm.injective.nontrivial
  exact IsLocalRing.of_surjective' (AlgEquiv.ofInjective ι hι).symm.toRingEquiv.toRingHom
    (AlgEquiv.ofInjective ι hι).symm.surjective

section cartier

variable {R : Type} [CommRing R]
  {X : Type} [CommRing X] [Bialgebra R X] [Module.Finite R X] [Module.Free R X]
  {D : Type} [CommRing D] [Bialgebra R D] [Module.Finite R D] [Module.Free R D]

lemma cartierDualMap_injective (π : X →ₐc[R] D) (hπ : Function.Surjective π) :
    Function.Injective (CartierDual.map π) := by
  intro φ ψ h
  apply CartierDual.ext
  intro d
  obtain ⟨x, rfl⟩ := hπ d
  have := congrArg (fun χ : CartierDual R X => χ x) h
  simpa only [CartierDual.map_apply] using this

end cartier
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"

theorem isLocalRing_cartierDual_of_quotient (R C D : Type) [CommRing R]
    [CommRing C] [HopfAlgebra R C] [Coalgebra.IsCocomm R C] [Module.Finite R C] [Module.Free R C]
    [IsLocalRing C]
    [CommRing D] [Bialgebra R D] [Module.Finite R D] [Module.Free R D]
    (π : CartierDual R C →ₐc[R] D) (hπ : Function.Surjective π)
    (bidual : ∃ e : C ≃ₐc[R] CartierDual R (CartierDual R C),
      ∀ (a : C) (φ : CartierDual R C), e a φ = φ a) :
    IsLocalRing (CartierDual R D) := by
  obtain ⟨e, -⟩ := bidual
  let ι : CartierDual R D →ₐ[R] C :=
    (e.symm.toAlgEquiv : CartierDual R (CartierDual R C) →ₐ[R] C).comp
      (CartierDual.map π : CartierDual R D →ₐ[R] CartierDual R (CartierDual R C))
  have hι : Function.Injective ι := by
    intro φ ψ h
    apply cartierDualMap_injective π hπ
    exact e.symm.toAlgEquiv.injective h
  exact isLocalRing_of_injective_algHom ι hι

end FinFlatHopf.W4
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"

end
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"

set_option autoImplicit false

noncomputable section

namespace FinFlatHopf
p2m_export "FinFlatHopf" "not_isLocalRing_dual_of_isLocalRing inertiaFixed_valuationSubring_dvr_fixer_le_inertia dualPoints_equiv_monoidHom"
namespace W4
p2m_open "FinFlatHopf"

open WithConv

lemma redTriv_of_pullPoint {S X Y L : Type} [CommRing S] [CommRing X] [CommRing Y]
    [Bialgebra S X] [Bialgebra S Y] [Field L] [Algebra S L] (P : ValuationSubring L)
    (π : X →ₐc[S] Y) (hπ : Function.Surjective π) (g : WithConv (Y →ₐ[S] L))
    (h : RedTriv P (pullPoint π g)) : RedTriv P g := by
  intro y
  obtain ⟨x, rfl⟩ := hπ y
  have hx := h x
  rw [pullPoint_apply] at hx
  rwa [CoalgHomClass.counit_comp_apply π x]

theorem dualSide_compPoint_eq_pow
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (R : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [IsLocalRing R]
    [Algebra R (AlgebraicClosure ℚ)]
    (hRinj : Function.Injective (algebraMap R (AlgebraicClosure ℚ)))
    (hp𝔪 : (p : R) ∉ IsLocalRing.maximalIdeal R ^ 2)
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (hRP : ∀ r : R, algebraMap R (AlgebraicClosure ℚ) r ∈ P)
    (IP : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hIP : ∀ σ, σ ∈ IP ↔ FixesBase R σ)
    (hIPval : ∀ σ ∈ IP, ∀ x ∈ P, P.valuation (σ x - x) < 1)
    (C : Type) [CommRing C] [HopfAlgebra R C] [Coalgebra.IsCocomm R C] [Module.Finite R C]
    [Module.Free R C] [IsLocalRing C]
    [Finite (DPts R C)]
    (Kadd : Type) [AddCommGroup Kadd] [Finite Kadd]
    (eC : Pts R C ≃ Kadd) (heC : ∀ f g, eC (f * g) = eC f + eC g)
    (hq : ∀ k : Kadd, (p ^ n) • k = 0)
    (eW3 : DPts R C ≃* (Pts R C →* (AlgebraicClosure ℚ)ˣ))
    (hequivW3 : ∀ (τ : AlgebraicClosure ℚ ≃ₐ[R] AlgebraicClosure ℚ) (g : DPts R C) (f : Pts R C),
      ((eW3 (toConv (τ.toAlgHom.comp g.ofConv)) f : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) =
        τ ((eW3 g (toConv (τ.symm.toAlgHom.comp f.ofConv)) : (AlgebraicClosure ℚ)ˣ) :
          AlgebraicClosure ℚ))
    (hLoc : ∀ (X : Type) [CommRing X] [HopfAlgebra R X] [Module.Finite R X] [Module.Free R X],
      Nat.card (WithConv (X →ₐ[R] AlgebraicClosure ℚ)) = Module.finrank R X →
      (∀ g : X →ₐ[R] AlgebraicClosure ℚ, RedTriv P (toConv g)) → IsLocalRing X)
    (hS7 : ∀ N0 : AddSubgroup (Nadd R C),
      (∀ σ (hσ : σ ∈ IP) (x : Nadd R C), x ∈ N0 → ipAct eW3 IP hIP σ hσ x ∈ N0) → N0 ≠ ⊥ →
      ∃ A : AddSubgroup (Nadd R C), A ≤ N0 ∧ Nat.card A = p ∧
        ∀ σ (hσ : σ ∈ IP) (x : Nadd R C), x ∈ A → ipAct eW3 IP hIP σ hσ x ∈ A)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ IP) (a : ℕ)
    (hχ : ∀ μ : AlgebraicClosure ℚ, μ ^ p ^ n = 1 → σ μ = μ ^ a)
    (f : Pts R C) :
    compPoint σ ((hIP σ).mp hσ) f = f ^ a := by
  classical
  have hfixσ : FixesBase R σ := (hIP σ).mp hσ

  let eN : DPts R C ≃ Nadd R C := eW3.toEquiv.trans Additive.ofMul
  have heN : ∀ g g' : DPts R C, eN (g * g') = eN g + eN g' := fun g g' => by
    change Additive.ofMul (eW3 (g * g')) = Additive.ofMul (eW3 g) + Additive.ofMul (eW3 g')
    rw [map_mul]
    rfl
  haveI : Finite (Nadd R C) := Finite.of_equiv _ eN
  have hvalN : ValuesIn (S := R) (X := CartierDual R C) P :=
    valuesIn_of_finite (X := CartierDual R C) P hRP
  have ipAct_eq : ∀ τ' (hτ' : τ' ∈ IP) (x : Nadd R C),
      ipAct eW3 IP hIP τ' hτ' x = eN (compPoint τ' ((hIP τ').mp hτ') (eN.symm x)) :=
    fun _ _ _ => rfl

  let N0 : AddSubgroup (Nadd R C) := redKernel P eN heN hvalN
  have hmove : ∀ τ' (hτ' : τ' ∈ IP) (g : DPts R C),
      eN (compPoint τ' ((hIP τ').mp hτ') g) - eN g ∈ N0 := fun τ' hτ' g =>
    sub_mem_redKernel_of_pointwise eN heN hvalN (fun y => τ' y) (hIPval τ' hτ') g
      (compPoint τ' ((hIP τ').mp hτ') g) (fun _ => rfl)
  have hN0stab : ∀ τ' (hτ' : τ' ∈ IP) (x : Nadd R C), x ∈ N0 → ipAct eW3 IP hIP τ' hτ' x ∈ N0 := by
    intro τ' hτ' x hx
    rw [ipAct_eq]

    have hx' : Cong P (eN.symm x) 1 := hx
    have hc : Cong P (compPoint τ' ((hIP τ').mp hτ') (eN.symm x)) (eN.symm x) := fun y =>
      hIPval τ' hτ' _ (hvalN _ _)
    exact (mem_redKernel_iff eN heN hvalN _).mpr (cong_trans P hc hx')

  have hN0bot : N0 = ⊥ := by
    by_contra hne
    obtain ⟨A, hAN0, hcardA, hAstab⟩ := hS7 N0 hN0stab hne

    have hstabA : ∀ τ' (x : Nadd R C), x ∈ (A : Set (Nadd R C)) → actDevice eN τ' x ∈ (A : Set (Nadd R C)) :=
      hstab_actDevice_of_fixers eN (A : Set (Nadd R C)) (fun τ' hτ' x hx => by
        have h := hAstab τ' ((hIP τ').mpr hτ') x hx
        rwa [ipAct_eq] at h)
    have hstabN0 : ∀ τ' (x : Nadd R C), x ∈ (N0 : Set (Nadd R C)) →
        actDevice eN τ' x ∈ (N0 : Set (Nadd R C)) :=
      hstab_actDevice_of_fixers eN (N0 : Set (Nadd R C)) (fun τ' hτ' x hx => by
        have h := hN0stab τ' ((hIP τ').mpr hτ') x hx
        rwa [ipAct_eq] at h)

    obtain ⟨Bf, instCR, instHA, π, φ, _hFT, hFlat, hπs, hφs, _hcomp, _hbij, hfac, hcoc, hfin⟩ :=
      HopfAlgebra.exists_quotientFlag_of_galoisStableChain R hRinj (CartierDual R C) (Nadd R C)
        eN heN (actDevice eN) (fun τ' f' g' h => hact_actDevice eN τ' f' g' h) 2 ![A, N0, ⊤]
        (by
          intro i
          fin_cases i
          · exact hAN0
          · exact le_top)
        rfl
        (by
          intro i τ' x hx
          fin_cases i
          · exact hstabA τ' x hx
          · exact hstabN0 τ' x hx
          · exact AddSubgroup.mem_top _)
    have hcocB : ∀ i, Coalgebra.IsCocomm R (Bf i) := hcoc inferInstance
    have hfinB := hfin inferInstance
    have instFin : ∀ i, Module.Finite R (Bf i) := fun i => (hfinB i).1
    have instFree : ∀ i, Module.Free R (Bf i) := fun i => by
      haveI := hFlat i
      haveI := instFin i
      exact Module.free_of_finite_type_torsion_free'

    have hrank0 : Module.finrank R (Bf 0) = p := by
      rw [(hfinB 0).2 (by decide)]
      exact hcardA
    have hrank1 : Module.finrank R (Bf 1) = Nat.card (![A, N0, ⊤] (1 : Fin (2 + 1))) :=
      (hfinB 1).2 (by decide)

    have hDloc : IsLocalRing (Bf 1) := by
      refine hLoc (Bf 1) ?_ ?_
      · rw [hrank1]
        exact natCard_quotPts (π 1) eN _ (hπs 1) (hfac 1)
      · intro g
        have hmem : eN (pullPoint (π 1) (toConv g)) ∈ (![A, N0, ⊤] (1 : Fin (2 + 1))) :=
          e_pullPoint_mem (π 1) eN _ (hfac 1) (toConv g)
        have hred : RedTriv P (pullPoint (π 1) (toConv g)) :=
          (mem_redKernel_iff eN heN hvalN _).mp hmem
        exact redTriv_of_pullPoint P (π 1) (hπs 1) (toConv g) hred

    let φ0 : Bf 1 →ₐc[R] Bf 0 := φ 0
    have hφ0 : Function.Surjective φ0 := hφs 0
    haveI : IsLocalRing (Bf 1) := hDloc
    haveI : Nontrivial (Bf 0) := by
      apply Module.nontrivial_of_finrank_pos (R := R)
      rw [hrank0]
      exact (Fact.out : p.Prime).pos
    haveI : IsLocalRing (Bf 0) := IsLocalRing.of_surjective' (φ0 : Bf 1 →+* Bf 0) hφ0

    haveI : IsLocalRing (CartierDual R (Bf 0)) :=
      isLocalRing_cartierDual_of_quotient R C (Bf 0) (π 0) (hπs 0)
        (CartierDual.exists_bialgEquiv_bidual R C)

    exact FinFlatHopf.not_isLocalRing_dual_of_isLocalRing R p (Fact.out : p.Prime).one_lt hp𝔪
      (Bf 0) hrank0 (isLocalRing_withConv_of_cartierDual R (Bf 0))

  have htrivN : ∀ g : DPts R C, compPoint σ hfixσ g = g := by
    intro g
    have hsub : eN (compPoint σ hfixσ g) - eN g ∈ (⊥ : AddSubgroup (Nadd R C)) := by
      rw [← hN0bot]
      exact hmove σ hσ g
    have h0 : eN (compPoint σ hfixσ g) - eN g = 0 := (AddSubgroup.mem_bot).mp hsub
    exact eN.injective (sub_eq_zero.mp h0)

  have hpair : ∀ (g : DPts R C) (f' : Pts R C),
      ((eW3 g (toConv ((fixAlgEquiv σ hfixσ).toAlgHom.comp f'.ofConv)) : (AlgebraicClosure ℚ)ˣ) :
          AlgebraicClosure ℚ) =
        (fixAlgEquiv σ hfixσ) ((eW3 g f' : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) := by
    intro g f'
    refine pair_comp_eq_of_equivariant_of_trivial
      (fun (g : DPts R C) (f : Pts R C) => ((eW3 g f : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ))
      (fixAlgEquiv σ hfixσ) (fun g => toConv ((fixAlgEquiv σ hfixσ).toAlgHom.comp g.ofConv))
      (fun g f => hequivW3 (fixAlgEquiv σ hfixσ) g f) (fun g => ?_) g f'
    show toConv ((fixAlgEquiv σ hfixσ).toAlgHom.comp g.ofConv) = g
    rw [toConv_toAlgHom_comp]
    exact htrivN g

  let ε : Pts R C ≃ Multiplicative Kadd := eC.trans Multiplicative.ofAdd
  have hε : ∀ f g : Pts R C, ε (f * g) = ε f * ε g := fun f g => by
    change Multiplicative.ofAdd (eC (f * g)) = Multiplicative.ofAdd (eC f) * Multiplicative.ofAdd (eC g)
    rw [heC]
    rfl
  let Φ : DPts R C → (Multiplicative Kadd →* (AlgebraicClosure ℚ)ˣ) :=
    fun g => (eW3 g).comp (symmHom ε hε)
  have hΦ : Function.Surjective Φ :=
    surjective_comp_symmHom ε hε (fun g => eW3 g) eW3.surjective
  let T : Multiplicative Kadd → Multiplicative Kadd := fun k => ε (compPoint σ hfixσ (ε.symm k))
  have hT : ∀ (g : DPts R C) (k : Multiplicative Kadd),
      ((Φ g (T k) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) =
        σ ((Φ g k : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) := by
    intro g k
    change ((eW3 g (ε.symm (ε (compPoint σ hfixσ (ε.symm k)))) : (AlgebraicClosure ℚ)ˣ) :
        AlgebraicClosure ℚ) = σ ((eW3 g (ε.symm k) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)
    rw [Equiv.symm_apply_apply, ← toConv_toAlgHom_comp σ hfixσ (ε.symm k), hpair]
    rfl
  have hG : ∀ k : Multiplicative Kadd, k ^ (p ^ n) = 1 := by
    intro k
    rw [← ofAdd_toAdd k, ← ofAdd_nsmul, hq, ofAdd_zero]
  have hTk := eq_pow_of_characters (fun x => σ x) T (p ^ n) a (fun μ hμ => hχ μ hμ) hG Φ hΦ hT

  apply ε.injective
  have h1 : ε (f ^ a) = ε f ^ a := map_pow (toHom ε hε) f a
  have h2 : T (ε f) = ε (compPoint σ hfixσ f) := by
    change ε (compPoint σ hfixσ (ε.symm (ε f))) = _
    rw [Equiv.symm_apply_apply]
  rw [h1, ← hTk (ε f), h2]

end FinFlatHopf.W4
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"

end
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"

set_option autoImplicit false

noncomputable section

namespace FinFlatHopf
p2m_export "FinFlatHopf" "not_isLocalRing_dual_of_isLocalRing inertiaFixed_valuationSubring_dvr_fixer_le_inertia dualPoints_equiv_monoidHom"
namespace W4
p2m_open "FinFlatHopf"

open WithConv

theorem smul_eq_nsmul_of_compPoint_eq_pow
    {B X C M Kadd : Type} [CommRing B] [CommRing X] [CommRing C] [Bialgebra B X]
    [Bialgebra B C] [Algebra B (AlgebraicClosure ℚ)] [AddCommGroup M]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) M]
    (e' : WithConv (X →ₐ[B] AlgebraicClosure ℚ) ≃ M)
    (he'_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (X →ₐ[B] AlgebraicClosure ℚ)),
      (∀ x : X, g x = σ (f x)) → e' g = σ • e' f)
    (π : X →ₐc[B] C)
    [AddCommGroup Kadd] (eC : Pts B C ≃ Kadd) (heC : ∀ f g : Pts B C, eC (f * g) = eC f + eC g)
    (jK : Kadd →+ M) (hj : ∀ f : Pts B C, jK (eC f) = e' (pullPoint π f))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hfix : FixesBase B σ) (a : ℕ)
    (hpow : ∀ f : Pts B C, compPoint σ hfix f = f ^ a) :
    ∀ k : Kadd, σ • jK k = a • jK k := by

  have hpowE : ∀ (f : Pts B C) (m : ℕ), eC (f ^ m) = m • eC f := by
    intro f m
    induction m with
    | zero => rw [pow_zero, zero_nsmul, e_one eC heC]
    | succ m ih => rw [pow_succ, heC, ih, succ_nsmul]
  intro k
  obtain ⟨f, rfl⟩ := eC.surjective k
  rw [← map_nsmul jK a (eC f), ← hpowE, ← hpow, hj, hj]
  exact (he'_act σ (pullPoint π f) (pullPoint π (compPoint σ hfix f))
    (pullPoint_pointwise π (fun y => σ y) f _ (fun _ => rfl))).symm

theorem conj3_on_K
    {B X C M : Type} [CommRing B] [CommRing X] [CommRing C] [Bialgebra B X]
    [Bialgebra B C] [Algebra B (AlgebraicClosure ℚ)] [AddCommGroup M]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) M]
    (e' : WithConv (X →ₐ[B] AlgebraicClosure ℚ) ≃ M)
    (he'_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (X →ₐ[B] AlgebraicClosure ℚ)),
      (∀ x : X, g x = σ (f x)) → e' g = σ • e' f)
    (π : X →ₐc[B] C) (K : AddSubgroup M)
    (eC : Pts B C ≃ ↥K) (heC : ∀ f g : Pts B C, eC (f * g) = eC f + eC g)
    (hj : ∀ f : Pts B C, ((eC f : ↥K) : M) = e' (pullPoint π f))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hfix : FixesBase B σ) (a : ℕ)
    (hpow : ∀ f : Pts B C, compPoint σ hfix f = f ^ a) :
    ∀ t ∈ K, σ • t = a • t := fun t ht =>
  smul_eq_nsmul_of_compPoint_eq_pow e' he'_act π eC heC K.subtype hj σ hfix a hpow ⟨t, ht⟩

end FinFlatHopf.W4
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"

end
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"

set_option maxHeartbeats 3200000

namespace FinFlatHopf
p2m_export "FinFlatHopf" "not_isLocalRing_dual_of_isLocalRing inertiaFixed_valuationSubring_dvr_fixer_le_inertia dualPoints_equiv_monoidHom"
p2m_open "FinFlatHopf"

open IsLocalRing AlgebraicClosure ValuationSubring GaloisRep

end FinFlatHopf
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"

p2m_open "FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4 IsLocalRing AlgebraicClosure ValuationSubring GaloisRep"

theorem solution (p : ℕ) [Fact p.Prime]
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Flat (GaloisRep.ratLocalizedAt p) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H]
    {M : Type} [AddCommGroup M] [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) M]
    (e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ M)
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (he_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ x : H, g x = σ (f x)) → e g = σ • (e f))
    (R : Type) [CommRing R] [IsLocalRing R] [Module R M]
    (hR : Nat.card (IsLocalRing.ResidueField R) = p)
    (u : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → Rˣ)
    (hu : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ m : M, σ • m = (u σ : R) • m) :
    ∃ T : AddSubgroup M,
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ t ∈ T, σ • t ∈ T) ∧
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ m : M, σ • m - m ∈ T) ∧
      ∀ (n a : ℕ) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
        σ ∈ P.inertiaSubgroupIn ℚ →
        (∀ μ : AlgebraicClosure ℚ, μ ^ p ^ n = 1 → σ μ = μ ^ a) →
        (∀ t ∈ T, p ^ n • t = 0) → ∀ t ∈ T, σ • t = a • t := by

  classical
  set IP : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) := P.inertiaSubgroupIn ℚ
  let B : Subring (AlgebraicClosure ℚ) :=
  { carrier := {x | x ∈ P ∧ ∀ σ ∈ IP, σ x = x}
    mul_mem' := fun {a b} ⟨haP, haσ⟩ ⟨hbP, hbσ⟩ =>
      ⟨mul_mem haP hbP, fun σ hσ => by rw [map_mul, haσ σ hσ, hbσ σ hσ]⟩
    one_mem' := ⟨P.one_mem, fun σ _ => map_one σ⟩
    add_mem' := fun {a b} ⟨haP, haσ⟩ ⟨hbP, hbσ⟩ =>
      ⟨add_mem haP hbP, fun σ hσ => by rw [map_add, haσ σ hσ, hbσ σ hσ]⟩
    zero_mem' := ⟨P.zero_mem, fun σ _ => map_zero σ⟩
    neg_mem' := fun {a} ⟨haP, haσ⟩ =>
      ⟨neg_mem haP, fun σ hσ => by rw [map_neg, haσ σ hσ]⟩ }
  have hB : ∀ x : AlgebraicClosure ℚ, x ∈ B ↔
      (x ∈ P ∧ ∀ σ ∈ IP, σ x = x) := fun _ => Iff.rfl
  obtain ⟨⟨hp_nu, hDVR⟩, hsubset, hfixers⟩ :=
    FinFlatHopf.inertiaFixed_valuationSubring_dvr_fixer_le_inertia p P hP B hB

  have hp0 : (p : ↥B) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  haveI : IsLocalRing ↥B := isLocalRing_of_uniformizer (p : ↥B) hp0 hp_nu hDVR
  haveI : IsPrincipalIdealRing ↥B := isPrincipalIdealRing_of_uniformizer (p : ↥B) hDVR
  have hp𝔪 : (p : ↥B) ∉ (IsLocalRing.maximalIdeal ↥B) ^ 2 :=
    uniformizer_notMem_maximalIdeal_sq (p : ↥B) hp0 hp_nu hDVR

  letI : Algebra (GaloisRep.ratLocalizedAt p) ↥B := algebraOfSubring p B hsubset
  haveI : IsScalarTower (GaloisRep.ratLocalizedAt p) ↥B (AlgebraicClosure ℚ) :=
    IsScalarTower.of_algebraMap_eq fun q => rfl
  have hRinj : Function.Injective (algebraMap ↥B (AlgebraicClosure ℚ)) :=
    Subtype.val_injective
  have hRP : ∀ r : ↥B, algebraMap ↥B (AlgebraicClosure ℚ) r ∈ P :=
    fun r => ((hB r).mp r.2).1
  have hIPval : ∀ σ ∈ IP, ∀ x ∈ P, P.valuation (σ x - x) < 1 := fun σ hσ x hx =>
    (ValuationSubring.valuation_sub_lt_one_of_mem_inertiaSubgroupIn P hσ hx).2
  have hfixB : ∀ σ ∈ IP, ∀ b ∈ B, σ b = b := fun σ hσ b hb => ((hB b).mp hb).2 σ hσ
  have hIP : ∀ σ, σ ∈ IP ↔ FixesBase ↥B σ := fun σ =>
    ⟨fun hσ => (fixesBase_subring_iff B σ).mpr (hfixB σ hσ),
     fun hF => hfixers σ ((fixesBase_subring_iff B σ).mp hF)⟩
  have hintP : ∀ x : AlgebraicClosure ℚ, x ∈ P → IsIntegral ↥B x :=
    fun x hx => isIntegral_of_mem_valuationSubring_of_fixers_le P B hB hfixers x hx

  have instT : IsScalarTower ↥(ratLocalizedAt p) ↥B (AlgebraicClosure ℚ) :=
    IsScalarTower.of_algebraMap_eq fun q => rfl
  haveI : Module.Free (↥B) (↥B ⊗[ratLocalizedAt p] H) :=
    Module.free_of_finite_type_torsion_free'

  haveI : Finite (WithConv (↥B ⊗[ratLocalizedAt p] H →ₐ[↥B] AlgebraicClosure ℚ)) :=
    finite_withConv_algHom ↥B (↥B ⊗[ratLocalizedAt p] H) (AlgebraicClosure ℚ)
  let e_B : WithConv (↥B ⊗[ratLocalizedAt p] H →ₐ[↥B] AlgebraicClosure ℚ) ≃ M :=
    (@ptsEquiv ↥(ratLocalizedAt p) ↥B H (AlgebraicClosure ℚ) _ _ _ _ _ _ _ _ instT).trans e
  haveI : Finite M := Finite.of_equiv _ e_B
  have he_add_B : ∀ F G, e_B (F * G) = e_B F + e_B G :=
    @he_add_baseChange ↥(ratLocalizedAt p) ↥B H (AlgebraicClosure ℚ)
      _ _ _ _ _ _ _ _ instT M _ e he_add
  have he_act_B :
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
        (F G : WithConv (↥B ⊗[ratLocalizedAt p] H →ₐ[↥B] AlgebraicClosure ℚ)),
        (∀ x, G x = σ (F x)) → e_B G = σ • e_B F :=
    @he_act_baseChange ↥(ratLocalizedAt p) ↥B H (AlgebraicClosure ℚ)
      _ _ _ _ _ _ _ _ instT M (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) _
      (fun τ => ⇑τ) e he_act

  have hval_B : ValuesIn (S := ↥B) (X := ↥B ⊗[ratLocalizedAt p] H) P :=
    valuesIn_of_finite P hRP
  let K : AddSubgroup M := redKernel P e_B he_add_B hval_B

  have hKcong : ∀ σ ∈ IP, ∀ m : M, σ • m - m ∈ K := by
    intro σ hσ m
    have hσv : ∀ a ∈ P, P.valuation (σ a - a) < 1 :=
      fun a ha => (valuation_sub_lt_one_of_mem_inertiaSubgroupIn P hσ ha).2
    have hσB : FixesBase ↥B σ := (hIP σ).mp hσ
    set f := e_B.symm m with hfdef
    have hfg : ∀ x : ↥B ⊗[ratLocalizedAt p] H,
        compPoint σ hσB f x = σ (f x) := fun x => rfl
    have hres := smul_sub_mem_redKernel e_B he_add_B hval_B
      (Γ := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (fun τ => ⇑τ)
      he_act_B σ hσv f (compPoint σ hσB f) hfg
    rw [show e_B f = m from e_B.apply_symm_apply m] at hres
    exact hres

  have hKfix : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : FixesBase ↥B σ),
      ∀ x ∈ (K : Set M), e_B (compPoint σ hσ (e_B.symm x)) ∈ (K : Set M) := by
    intro σ hσ x hx
    have hσIP : σ ∈ IP := (hIP σ).mpr hσ
    have heq : e_B (compPoint σ hσ (e_B.symm x)) = σ • x := by
      have h := he_act_B σ (e_B.symm x) (compPoint σ hσ (e_B.symm x)) (fun _ => rfl)
      rwa [e_B.apply_symm_apply] at h
    rw [heq]
    have h1 : σ • x - x + x ∈ K := K.add_mem (hKcong σ hσIP x) hx
    rwa [sub_add_cancel] at h1

  obtain ⟨Bf, instCR, instHA, πf, φf, _hFT, hFlatB, hπs, _hφs, _hcomp, _hbij, hfac, hcoc, hfin⟩ :=
    HopfAlgebra.exists_quotientFlag_of_galoisStableChain ↥B hRinj
      (↥B ⊗[ratLocalizedAt p] H) M e_B he_add_B (actDevice e_B)
      (fun τ f g h => hact_actDevice e_B τ f g h) 1 ![K, ⊤]
      (by intro i; fin_cases i; exact le_top) rfl
      (by
        intro i σ x hx
        fin_cases i
        · exact hstab_actDevice_of_fixers e_B (↑K) hKfix σ x hx
        · exact AddSubgroup.mem_top _)

  have hcocB : ∀ i, Coalgebra.IsCocomm ↥B (Bf i) := hcoc inferInstance
  have hfinB := hfin inferInstance
  haveI : Module.Finite ↥B (Bf 0) := (hfinB 0).1
  haveI : Module.Free ↥B (Bf 0) := Module.free_of_finite_type_torsion_free'
  have hrankC : Module.finrank ↥B (Bf 0) = Nat.card ↥K := by
    have h := (hfinB 0).2 (by decide)
    simpa only [Matrix.cons_val_zero] using h

  have hfacK : ∀ f : (↥B ⊗[ratLocalizedAt p] H) →ₐ[↥B] AlgebraicClosure ℚ,
      (∃ g : (Bf 0) →ₐ[↥B] AlgebraicClosure ℚ,
        g.comp (πf 0 : (↥B ⊗[ratLocalizedAt p] H) →ₐ[↥B] Bf 0) = f)
        ↔ e_B (WithConv.toConv f) ∈ K := by
    intro f
    have h := hfac 0 f
    simpa only [Matrix.cons_val_zero] using h
  let eC : WithConv (Bf 0 →ₐ[↥B] AlgebraicClosure ℚ) ≃ ↥K :=
    quotPtsEquiv (πf 0) e_B K (hπs 0) hfacK

  have heC : ∀ F G, eC (F * G) = eC F + eC G :=
    quotPts_he_add (πf 0) e_B K (hπs 0) hfacK he_add_B

  have hcardC : Nat.card (WithConv (Bf 0 →ₐ[↥B] AlgebraicClosure ℚ)) =
      Module.finrank ↥B (Bf 0) := by
    rw [Nat.card_congr eC, ← hrankC]
  have hredC : ∀ g : (Bf 0) →ₐ[↥B] AlgebraicClosure ℚ, RedTriv P (WithConv.toConv g) := by
    intro g

    have hmem : e_B (pullPoint (πf 0) (WithConv.toConv g)) ∈ K :=
      e_pullPoint_mem (πf 0) e_B K hfacK (WithConv.toConv g)
    have hredpull : RedTriv P (pullPoint (πf 0) (WithConv.toConv g)) :=
      (mem_redKernel_iff e_B he_add_B hval_B _).mp hmem
    exact redTriv_of_pullPoint P (πf 0) (hπs 0) (WithConv.toConv g) hredpull
  haveI : IsLocalRing (Bf 0) :=
    isLocalRing_of_card_of_redTriv ↥B P hRP hRinj hintP (Bf 0) hcardC hredC

  have hKIP : ∀ σ ∈ IP, ∀ m ∈ K, σ • m ∈ K := fun σ hσ m hm => by
    have h := K.add_mem (hKcong σ hσ m) hm
    rwa [sub_add_cancel] at h

  refine ⟨K, fun σ hσ t ht => hKIP σ hσ t ht, hKcong, ?_⟩
  intro n a σ hσ hχ hT

  rcases subsingleton_or_nontrivial M with hMsub | hMnt
  · intro t ht; simp [Subsingleton.elim (σ • t) 0, Subsingleton.elim (a • t) 0]
  haveI := hMnt
  letI := moduleScal R M u IP
  obtain ⟨hScalLoc, hScalRes⟩ := isLocalRing_scal R M u IP p Fact.out hR
  haveI := hScalLoc
  letI := moduleK R M u IP hu K hKIP

  haveI : Module.Free ↥B (CartierDual ↥B (Bf 0)) := inferInstance
  haveI : Finite (DPts ↥B (Bf 0)) :=
    finite_withConv_algHom ↥B (CartierDual ↥B (Bf 0)) (AlgebraicClosure ℚ)
  obtain ⟨eW3, _hpairing, hequivW3⟩ :=
    FinFlatHopf.dualPoints_equiv_monoidHom ↥B (Bf 0) (AlgebraicClosure ℚ) hcardC

  have hLoc : ∀ (X : Type), [CommRing X] → [HopfAlgebra ↥B X] → [Module.Finite ↥B X] →
      [Module.Free ↥B X] →
      Nat.card (WithConv (X →ₐ[↥B] AlgebraicClosure ℚ)) = Module.finrank ↥B X →
      (∀ g : X →ₐ[↥B] AlgebraicClosure ℚ, RedTriv P (WithConv.toConv g)) → IsLocalRing X :=
    fun X _ _ _ _ hc hr => isLocalRing_of_card_of_redTriv ↥B P hRP hRinj hintP X hc hr
  have hscal : ∀ σ (hσ : σ ∈ IP), ∃ r : Scal R M u IP, ∀ f : Pts ↥B (Bf 0),
      eC (compPoint σ ((hIP σ).mp hσ) f) = r • eC f := by
    refine hscal_of_hu (B := ↥B) (X := ↥B ⊗[ratLocalizedAt p] H) (C := Bf 0)
      e_B he_act_B IP hIP (Rsc := Scal R M u IP)
      (exists_scal_smul_eq R M u IP hu) (πf 0) eC
      (fun k => (k : M)) Subtype.val_injective ?_ ?_
    · exact fun f => coe_quotPtsEquiv (πf 0) e_B K (hπs 0) hfacK f
    · exact fun r k => coe_smulK R M u IP hu K hKIP r k
  have hq : ∀ k : ↥K, (p ^ n) • k = 0 := fun k => Subtype.ext (by
    simpa using hT k.1 k.2)
  have hS7' := hS7_of_scalar p n ↥B IP hIP (Bf 0) ↥K eC heC hq eW3 hequivW3
    (Scal R M u IP) hScalRes hscal

  have hpow : ∀ f : Pts ↥B (Bf 0), compPoint σ ((hIP σ).mp hσ) f = f ^ a :=
    dualSide_compPoint_eq_pow p n ↥B hRinj hp𝔪 P hRP IP hIP hIPval (Bf 0)
      ↥K eC heC hq eW3 hequivW3 hLoc hS7' σ hσ a hχ
  exact conj3_on_K e_B he_act_B (πf 0) K eC heC
    (fun f => coe_quotPtsEquiv (πf 0) e_B K (hπs 0) hfacK f)
    σ ((hIP σ).mp hσ) a hpow

section Grading

p2m_open "FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf"

end Grading
p2m_reactivate "P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.W4"

end S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic
end P2MW
export P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic (solution)
