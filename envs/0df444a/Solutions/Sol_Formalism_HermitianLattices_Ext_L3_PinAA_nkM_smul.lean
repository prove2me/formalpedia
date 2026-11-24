-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.PinAA.nkM_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:11:51.88026+00:00
-- url     : https://prove2.me/submissions/e8261357-a69b-4a4d-8422-0681bd76125f

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySixth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NkCountLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoMeanAlphaN
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MulEqZeroIff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_PinAA_rd_mk
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_PinAA_rd_surjective
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_PinAA_rd_star
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_PinAA_mul_eq_mul_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_PinAA_card_ker_rd
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_PinAA_map_smul_mk
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply


section
open NumberField Module Matrix
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.PinAA
open HermitianSublattices LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans localValuationFiltration
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
variable {κ : Type} [Fintype κ] [DecidableEq κ] [Fact (IsFixF K F)]
private theorem card_subtype_comp_eq_card_mul_card_ker_of_surjective {A B : Type} [AddCommGroup A] [AddCommGroup B] (f : A →+ B)
    (hf : Function.Surjective f) (T : B → Prop) :
    Nat.card {a : A // T (f a)} = Nat.card {b : B // T b} * Nat.card (AddMonoidHom.ker f) := by
  have hs : ∀ b, f (Function.surjInv hf b) = b := Function.surjInv_eq hf
  rw [← Nat.card_prod]
  apply Nat.card_congr
  exact
    { toFun := fun a => (⟨f a.1, a.2⟩, ⟨a.1 - Function.surjInv hf (f a.1), by
        rw [AddMonoidHom.mem_ker, map_sub, hs, sub_self]⟩)
      invFun := fun p => ⟨Function.surjInv hf p.1.1 + p.2.1, by
        rw [map_add, hs, AddMonoidHom.mem_ker.mp p.2.2, add_zero]; exact p.1.2⟩
      left_inv := fun a => Subtype.ext (by
        show Function.surjInv hf (f a.1) + (a.1 - Function.surjInv hf (f a.1)) = a.1
        abel)
      right_inv := fun p => by
        have e : f (Function.surjInv hf p.1.1 + p.2.1) = p.1.1 := by
          rw [map_add, hs, AddMonoidHom.mem_ker.mp p.2.2, add_zero]
        refine Prod.ext (Subtype.ext e) (Subtype.ext ?_)
        show Function.surjInv hf p.1.1 + p.2.1 - Function.surjInv hf (f (Function.surjInv hf p.1.1 + p.2.1)) = p.2.1
        rw [e]; abel }
private theorem card_ker_compLeft_eq_card_ker_pow {A B : Type} [Ring A] [Ring B] (R : A →+* B) :
    Nat.card (AddMonoidHom.ker (AddMonoidHom.compLeft R.toAddMonoidHom κ)) =
      Nat.card (RingHom.ker R) ^ Fintype.card κ := by
  have e : AddMonoidHom.ker (AddMonoidHom.compLeft R.toAddMonoidHom κ) ≃ (κ → RingHom.ker R) :=
    { toFun := fun x i => ⟨x.1 i, by
        have h := congrFun (AddMonoidHom.mem_ker.mp x.2) i
        exact (RingHom.mem_ker).mpr h⟩
      invFun := fun g => ⟨fun i => (g i).1, by
        rw [AddMonoidHom.mem_ker]
        funext i
        exact (RingHom.mem_ker).mp (g i).2⟩
      left_inv := fun x => rfl
      right_inv := fun g => rfl }
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_eq_fintype_card (α := κ)]
end Formalism.HermitianLattices.Ext.L3.PinAA
end
end

set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.PinAA
open HermitianSublattices LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans localValuationFiltration
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
variable {κ : Type} [Fintype κ] [DecidableEq κ] [Fact (IsFixF K F)]
namespace Formalism.HermitianLattices.Ext.L3.PinAA
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F}
    (hc : c ≠ 0) (n : 𝓞 F) {k : ℕ} (hk : vF 𝔭 c ≤ k) (H : Matrix κ κ (𝓞 K)) :
    Nat.card {x : κ → 𝓞 K ⧸ extP K 𝔭 ^ k //
        star x ⬝ᵥ ((ι c • H).map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) *ᵥ x) =
          Ideal.Quotient.mk _ (ι (c * n))} =
      Ideal.absNorm 𝔭 ^ (2 * vF 𝔭 c * Fintype.card κ) *
        Nat.card {x : κ → 𝓞 K ⧸ extP K 𝔭 ^ (k - vF 𝔭 c) //
          star x ⬝ᵥ (H.map (Ideal.Quotient.mk (extP K 𝔭 ^ (k - vF 𝔭 c))) *ᵥ x) =
            Ideal.Quotient.mk _ (ι n)} := by
  have key : ∀ x : κ → 𝓞 K ⧸ extP K 𝔭 ^ k,
      (star x ⬝ᵥ ((ι c • H).map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) *ᵥ x) =
          Ideal.Quotient.mk _ (ι (c * n))) ↔
        star (fun i => rd K 𝔭 k (vF 𝔭 c) (x i)) ⬝ᵥ
            (H.map (Ideal.Quotient.mk (extP K 𝔭 ^ (k - vF 𝔭 c))) *ᵥ
              fun i => rd K 𝔭 k (vF 𝔭 c) (x i)) =
          Ideal.Quotient.mk _ (ι n) := by
    intro x
    have e : rd K 𝔭 k (vF 𝔭 c) (star x ⬝ᵥ (H.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) *ᵥ x)) =
        star (fun i => rd K 𝔭 k (vF 𝔭 c) (x i)) ⬝ᵥ
            (H.map (Ideal.Quotient.mk (extP K 𝔭 ^ (k - vF 𝔭 c))) *ᵥ
              fun i => rd K 𝔭 k (vF 𝔭 c) (x i)) := by
      simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, Pi.star_apply, rd_star,
        Matrix.map_apply, rd_mk]
    rw [map_smul_mk, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, map_mul, map_mul,
      mul_eq_mul_iff h𝔭 hc hk, e, rd_mk]
  have hsurj : Function.Surjective
      (AddMonoidHom.compLeft (rd K 𝔭 k (vF 𝔭 c)).toAddMonoidHom κ) := by
    intro y
    refine ⟨fun i => Function.surjInv (rd_surjective 𝔭 k (vF 𝔭 c)) (y i), ?_⟩
    funext i
    exact Function.surjInv_eq (rd_surjective 𝔭 k (vF 𝔭 c)) (y i)
  rw [Nat.card_congr (Equiv.subtypeEquivRight key)]
  refine (card_subtype_comp_eq_card_mul_card_ker_of_surjective _ hsurj (fun y => star y ⬝ᵥ
      (H.map (Ideal.Quotient.mk (extP K 𝔭 ^ (k - vF 𝔭 c))) *ᵥ y) = Ideal.Quotient.mk _ (ι n))).trans ?_
  rw [card_ker_compLeft_eq_card_ker_pow, card_ker_rd hK Fact.out h𝔭 hk, ← pow_mul, mul_comm]
end Formalism.HermitianLattices.Ext.L3.PinAA
