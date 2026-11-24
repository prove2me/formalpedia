-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.vectorCountBounds.card_preimage_piQ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:55.193827+00:00
-- url     : https://prove2.me/submissions/c7a7bed0-6eab-44fb-9b0c-57d938e681a7

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNotMemOfSol
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityEleventh
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_card_ker_piQ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_finite_quot
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_piQ_surjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.vectorCountBounds
open HermitianSublattices idealPowerSpanBounds traceDeterminantCongruences reductionMapsOfForms hermitianFormColumns
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable [Fact (IsFixF K F)]
variable {m : Type} [Fintype m] [DecidableEq m]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.vectorCountBounds
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ)
    (T : (m → 𝓞 K ⧸ extP K 𝔭 ^ k) → Prop) :
    Nat.card {x : m → 𝓞 K ⧸ extP K 𝔭 ^ (k + 1) // T (fun i => piQ K 𝔭 k (x i))} =
      Ideal.absNorm 𝔭 ^ (2 * Fintype.card m) * Nat.card {x // T x} := by
  classical
  haveI := finite_quot (K := K) h𝔭 k
  haveI := finite_quot (K := K) h𝔭 (k + 1)
  haveI : Fintype (𝓞 K ⧸ extP K 𝔭 ^ k) := Fintype.ofFinite _
  haveI : Fintype (𝓞 K ⧸ extP K 𝔭 ^ (k + 1)) := Fintype.ofFinite _
  have hF : IsFixF K F := Fact.out
  have hz : ∀ w : 𝓞 K ⧸ extP K 𝔭 ^ k, Nat.card {z // piQ K 𝔭 k z = w} = Ideal.absNorm 𝔭 ^ 2 := by
    intro w
    obtain ⟨z0, hz0⟩ := piQ_surjective (K := K) 𝔭 k w
    rw [← card_ker_piQ hK hF h𝔭 k]
    exact Nat.card_congr
      { toFun := fun z => ⟨z.1 - z0, by rw [RingHom.mem_ker, map_sub, z.2, hz0, sub_self]⟩
        invFun := fun q => ⟨q.1 + z0, by rw [map_add, RingHom.mem_ker.mp q.2, hz0, zero_add]⟩
        left_inv := fun z => Subtype.ext (sub_add_cancel _ _)
        right_inv := fun q => Subtype.ext (add_sub_cancel_right _ _) }
  have hfib : ∀ y : m → 𝓞 K ⧸ extP K 𝔭 ^ k,
      Nat.card {x : m → 𝓞 K ⧸ extP K 𝔭 ^ (k + 1) // (fun i => piQ K 𝔭 k (x i)) = y} =
        Ideal.absNorm 𝔭 ^ (2 * Fintype.card m) := by
    intro y
    have e : {x : m → 𝓞 K ⧸ extP K 𝔭 ^ (k + 1) // (fun i => piQ K 𝔭 k (x i)) = y} ≃
        ((i : m) → {z // piQ K 𝔭 k z = y i}) :=
      (Equiv.subtypeEquivRight (fun x => funext_iff)).trans
        (Equiv.subtypePiEquivPi (p := fun i z => piQ K 𝔭 k z = y i))
    rw [Nat.card_congr e, Nat.card_pi]
    simp only [hz, Finset.prod_const, Finset.card_univ]
    rw [← pow_mul]
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Fintype.card_subtype]
  rw [Finset.card_eq_sum_card_fiberwise (f := fun x => fun i => piQ K 𝔭 k (x i))
    (t := Finset.univ.filter T) ?_]
  · rw [Finset.sum_congr rfl (g := fun _ => Ideal.absNorm 𝔭 ^ (2 * Fintype.card m)) ?_,
      Finset.sum_const, smul_eq_mul, mul_comm]
    intro b hb
    rw [Finset.mem_filter] at hb
    rw [← hfib b, Nat.card_eq_fintype_card, Fintype.card_subtype]
    apply congrArg Finset.card
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨h ▸ hb.2, h⟩
  · intro x hx
    simpa using hx
end Formalism.HermitianLattices.Ext.L3.vectorCountBounds
