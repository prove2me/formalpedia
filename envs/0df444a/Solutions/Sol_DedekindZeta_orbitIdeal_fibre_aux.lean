-- Prove2me | solution 1 for DedekindZeta.orbitIdeal_fibre_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:23:44.689081+00:00
-- url     : https://prove2.me/submissions/7f63d0d7-6e6d-4ef0-94dc-330833945df8

import Mathlib
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_Statements
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
attribute [local simp] DedekindZeta.Theta.gaussVSchwartz_apply
attribute [local simp] DedekindZeta.Theta.mixedGaussianSchwartz_apply



set_option autoImplicit true
open NumberField NumberField.InfinitePlace IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open Filter Finset Asymptotics Topology
open scoped Real nonZeroDivisors
open DedekindZeta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
open scoped NNReal ENNReal
namespace DedekindZeta
theorem _root_.solution (I : FractionalIdeal (𝓞 K)⁰ K)
    (bfun : {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0} → 𝓞 K)
    (hbfun : ∀ a, (bfun a : K) = ((I.den : 𝓞 K) : K) * a.1)
    (hd_ne : ((I.den : 𝓞 K) : K) ≠ 0)
    (ψ : Quotient (MulAction.orbitRel
          (Multiplicative (Fin (NumberField.Units.rank K) → ℤ))
          {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0}) → NonzeroIdeal K)
    (hψval : ∀ o, ((ψ o : NonzeroIdeal K) : Ideal (𝓞 K))
        = Ideal.span {bfun (Quotient.out o)})
    (J : NonzeroIdeal K) :
    Finite {o // ψ o = J}
      ∧ Nat.card {o // ψ o = J} ≤ NumberField.Units.torsionOrder K := by
  classical
  by_cases hne : Nonempty {o // ψ o = J}
  · obtain ⟨ostar⟩ := hne
    -- For each fibre element, the relating unit decomposes (Dirichlet) into a
    -- torsion factor `ζ` and a free part `coneUnitHom (ofAdd e)`.
    have hex : ∀ oo : {o // ψ o = J},
        ∃ ζ : NumberField.Units.torsion K,
          ∃ g : Multiplicative (Fin (NumberField.Units.rank K) → ℤ),
            (Quotient.out ostar.1).1
              = ((ζ : (𝓞 K)ˣ) : K) * ((coneUnitHom (K := K) g : 𝓞 K) : K)
                  * (Quotient.out oo.1).1 := by
      intro oo
      have hoo : Ideal.span {bfun (Quotient.out oo.1)} = (J : Ideal (𝓞 K)) := by
        rw [← hψval oo.1]; exact congrArg Subtype.val oo.2
      have hostar : Ideal.span {bfun (Quotient.out ostar.1)} = (J : Ideal (𝓞 K)) := by
        rw [← hψval ostar.1]; exact congrArg Subtype.val ostar.2
      have hspan : Ideal.span {bfun (Quotient.out oo.1)}
          = Ideal.span {bfun (Quotient.out ostar.1)} := hoo.trans hostar.symm
      obtain ⟨u, hu_assoc⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
      -- Cast `bfun oo · u = bfun ostar` into `K` and cancel `d`.
      have hcastK : (bfun (Quotient.out oo.1) : K) * ((u : 𝓞 K) : K)
          = (bfun (Quotient.out ostar.1) : K) := by
        rw [← hu_assoc]; push_cast; ring
      rw [hbfun (Quotient.out oo.1), hbfun (Quotient.out ostar.1), mul_assoc] at hcastK
      have hcancel : (Quotient.out oo.1).1 * ((u : 𝓞 K) : K) = (Quotient.out ostar.1).1 :=
        mul_left_cancel₀ hd_ne hcastK
      -- Dirichlet decomposition of the unit `u`.
      obtain ⟨⟨ζ, ee⟩, hu_eq, -⟩ := NumberField.Units.exist_unique_eq_mul_prod K u
      have hcuh : (coneUnitHom (K := K) (Multiplicative.ofAdd ee) : (𝓞 K)ˣ)
          = ∏ i, NumberField.Units.fundSystem K i ^ (ee i) := by
        simp [coneUnitHom]
      have hu_eq2 : u = (ζ : (𝓞 K)ˣ) * coneUnitHom (K := K) (Multiplicative.ofAdd ee) := by
        rw [hu_eq, ← hcuh]
      have hu_castK : ((u : 𝓞 K) : K)
          = ((ζ : (𝓞 K)ˣ) : K)
            * ((coneUnitHom (K := K) (Multiplicative.ofAdd ee) : 𝓞 K) : K) := by
        rw [hu_eq2]; push_cast; ring
      refine ⟨ζ, Multiplicative.ofAdd ee, ?_⟩
      rw [← hcancel, hu_castK]; ring
    choose ζfun gfun hζgfun using hex
    -- Injectivity of `oo ↦ ζfun oo` into `torsion K`.
    have hΦinj : Function.Injective ζfun := by
      intro x y hxy
      have heq := (hζgfun x).symm.trans (hζgfun y)
      rw [hxy] at heq
      rw [mul_assoc, mul_assoc] at heq
      have hζ0 : (((ζfun y : (𝓞 K)ˣ) : 𝓞 K) : K) ≠ 0 :=
        RingOfIntegers.coe_ne_zero_iff.mpr (Units.ne_zero _)
      have hcc : ((coneUnitHom (K := K) (gfun x) : 𝓞 K) : K) * (Quotient.out x.1).1
          = ((coneUnitHom (K := K) (gfun y) : 𝓞 K) : K) * (Quotient.out y.1).1 :=
        mul_left_cancel₀ hζ0 heq
      have hSeq : (gfun x • Quotient.out x.1 :
            {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0})
          = gfun y • Quotient.out y.1 := by
        apply Subtype.ext
        show ((coneUnitHom (K := K) (gfun x) : 𝓞 K) : K) * (Quotient.out x.1).1
            = ((coneUnitHom (K := K) (gfun y) : 𝓞 K) : K) * (Quotient.out y.1).1
        exact hcc
      have hmem : Quotient.out y.1 ∈ MulAction.orbit
          (Multiplicative (Fin (NumberField.Units.rank K) → ℤ)) (Quotient.out x.1) :=
        ⟨(gfun y)⁻¹ * gfun x, by
          show ((gfun y)⁻¹ * gfun x) • Quotient.out x.1 = Quotient.out y.1
          rw [mul_smul, hSeq, inv_smul_smul]⟩
      have hyx : y.1 = x.1 := by
        have hsound := Quotient.sound (MulAction.orbitRel_apply.mpr hmem)
        rwa [Quotient.out_eq, Quotient.out_eq] at hsound
      exact Subtype.ext hyx.symm
    refine ⟨Finite.of_injective ζfun hΦinj, ?_⟩
    calc Nat.card {o // ψ o = J}
        ≤ Nat.card (NumberField.Units.torsion K) :=
          Nat.card_le_card_of_injective ζfun hΦinj
      _ = NumberField.Units.torsionOrder K := by rfl
  · -- Empty fibre.
    haveI : IsEmpty {o // ψ o = J} := not_nonempty_iff.mp hne
    exact ⟨inferInstance, by
      rw [Nat.card_eq_zero.mpr (Or.inl this)]; exact Nat.zero_le _⟩
end DedekindZeta
