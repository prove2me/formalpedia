-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.units_square_index
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:20:30.388815+00:00
-- url     : https://prove2.me/submissions/d980a4d2-3fe6-4afb-9409-485f2fc6d6fd

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_LatticeDeterminantIndexSq
import Definitions.Def_Formalism_FlagUnipotentLattices_SignaturePreservingEntryNorms
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegerGroupLocalParametrization
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5a4_torsion_real

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField nonZeroDivisors Finset
noncomputable section
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.LocalIntegralStructure Formalism.HermitianLatticeCounting.P.IntegralityLocalGlobal
set_option linter.all false
open NumberField.Units
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : UnitsSquareIndex := by
  intro F _ _ hr
  classical
  set S : Subgroup (𝓞 F)ˣ := (powMonoidHom 2 : (𝓞 F)ˣ →* (𝓞 F)ˣ).range with hS
  obtain ⟨θ, hθd⟩ : ∃ θ : (𝓞 F)ˣ →* Multiplicative (Fin (rank F) → ZMod 2), ∀ x, θ x =
      Multiplicative.ofAdd (fun i =>
        (((basisModTorsion F).repr (Additive.ofMul (x : (𝓞 F)ˣ ⧸ torsion F)) i : ℤ) : ZMod 2)) :=
   ⟨{ toFun := fun x => Multiplicative.ofAdd (fun i =>
        (((basisModTorsion F).repr (Additive.ofMul (x : (𝓞 F)ˣ ⧸ torsion F)) i : ℤ) : ZMod 2))
      map_one' := by
        simp only [QuotientGroup.mk_one, ofMul_one, map_zero, Finsupp.coe_zero, Pi.zero_apply,
          Int.cast_zero]; rfl
      map_mul' := by
        intro x y
        simp only [QuotientGroup.mk_mul, ofMul_mul, map_add, Finsupp.coe_add, Pi.add_apply,
          Int.cast_add]; rfl }, fun _ => rfl⟩
  have hθ : ∀ (x ζ : (𝓞 F)ˣ) (e : Fin (rank F) → ℤ), ζ ∈ torsion F →
      x = ζ * ∏ i, (fundSystem F i) ^ (e i) →
      θ x = Multiplicative.ofAdd (fun i => ((e i : ℤ) : ZMod 2)) := by
    intro x ζ e hζ hx
    have := fun_eq_repr F hζ hx
    rw [hθd, ← this]
  have hsurj : Function.Surjective θ := by
    intro v
    refine ⟨1 * ∏ i, (fundSystem F i) ^ (((Multiplicative.toAdd v i).val : ℕ) : ℤ), ?_⟩
    rw [hθ _ 1 _ (one_mem _) rfl]
    apply Multiplicative.toAdd.injective
    funext i
    simp
  have hsq : ∀ a : Multiplicative (Fin (rank F) → ZMod 2), a ^ 2 = 1 := by
    intro a
    apply Multiplicative.toAdd.injective
    funext i
    rw [sq]
    show Multiplicative.toAdd a i + Multiplicative.toAdd a i = 0
    exact CharTwo.add_self_eq_zero _
  have hker : θ.ker = S ⊔ torsion F := by
    apply le_antisymm
    · intro x hx
      obtain ⟨⟨ζ, e⟩, hxe, _⟩ := exist_unique_eq_mul_prod F x
      simp only at hxe
      rw [MonoidHom.mem_ker, hθ x ζ e ζ.2 hxe] at hx
      have h2 : ∀ i, (2 : ℤ) ∣ e i := by
        intro i
        have := congrFun (congrArg Multiplicative.toAdd hx) i
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd (e i) 2).mp this
      choose e' he' using h2
      have : x = (∏ i, (fundSystem F i) ^ (e' i)) ^ 2 * ζ := by
        rw [hxe, mul_comm, ← Finset.prod_pow]
        congr 1
        refine Finset.prod_congr rfl (fun i _ => ?_)
        rw [he' i, mul_comm, zpow_mul]; rfl
      rw [this]
      exact Subgroup.mul_mem_sup ⟨_, rfl⟩ ζ.2
    · apply sup_le
      · rintro _ ⟨y, rfl⟩
        rw [MonoidHom.mem_ker, powMonoidHom_apply, map_pow, hsq]
      · intro ζ hζ
        rw [MonoidHom.mem_ker, hθ ζ ζ (fun _ => 0) hζ (by simp)]
        simp; rfl
  have hST : S ⊓ torsion F = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨y, rfl⟩, hx⟩
    have hx' : y ^ 2 ∈ torsion F := hx
    have hy : y ∈ torsion F := by
      rw [torsion, CommGroup.mem_torsion] at hx' ⊢
      exact hx'.of_pow (by norm_num)
    show y ^ 2 ∈ (⊥ : Subgroup (𝓞 F)ˣ)
    rw [Subgroup.mem_bot]
    rcases s5a4_torsion_real hr y hy with h | h <;> simp [h]
  have hT : Nat.card (torsion F) = 2 := by
    rw [Nat.card_eq_two_iff]
    refine ⟨1, ⟨-1, neg_one_mem_torsion⟩, ?_, ?_⟩
    · intro h
      have h1 : (1 : (𝓞 F)ˣ) = -1 := congrArg Subtype.val h
      have h2 : ((1 : 𝓞 F) : F) = -1 := by
        have := congrArg (fun u : (𝓞 F)ˣ => ((u : 𝓞 F) : F)) h1
        simpa using this
      norm_num at h2
    · apply Set.eq_univ_of_forall
      intro x
      rcases s5a4_torsion_real hr x.1 x.2 with h | h
      · left; exact Subtype.ext h
      · right; exact Subtype.ext h
  have hrank : rank F + 1 = finrank ℚ F := by
    have h1 := InfinitePlace.card_add_two_mul_card_eq_rank F
    have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces F
    have h3 : InfinitePlace.nrComplexPlaces F = 0 := by
      rw [InfinitePlace.nrComplexPlaces, Fintype.card_eq_zero_iff]
      exact ⟨fun w => (InfinitePlace.not_isReal_iff_isComplex.mpr w.2) (hr w.1)⟩
    have h4 : 0 < Fintype.card (InfinitePlace F) := Fintype.card_pos
    rw [rank]; omega
  show S.index = _
  rw [← Subgroup.relIndex_mul_index (le_sup_left : S ≤ S ⊔ torsion F), Subgroup.relIndex_sup_left,
    ← Subgroup.inf_relIndex_right, hST, Subgroup.relIndex_bot_left, hT, ← hker, Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top, Nat.card_congr Multiplicative.toAdd,
    Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin, ← hrank, pow_succ,
    mul_comm]
end Formalism.HermitianLatticeCounting.P
