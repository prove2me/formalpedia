-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.PinAA.akM_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:11:50.764909+00:00
-- url     : https://prove2.me/submissions/af9526d5-a0b5-4d6e-bdb9-9ecbc8c05f67

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySixth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NkCountLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoMeanAlphaN
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MulEqZeroIff
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
private theorem card_ker_mapMatrix_eq_card_ker_pow_sq {A B : Type} [Ring A] [Ring B] (R : A →+* B) :
    Nat.card (AddMonoidHom.ker (R.toAddMonoidHom.mapMatrix : Matrix κ κ A →+ Matrix κ κ B)) =
      Nat.card (RingHom.ker R) ^ (Fintype.card κ ^ 2) := by
  have e : AddMonoidHom.ker (R.toAddMonoidHom.mapMatrix : Matrix κ κ A →+ Matrix κ κ B) ≃
      (κ → κ → RingHom.ker R) :=
    { toFun := fun X i j => ⟨X.1 i j, by
        have h := congrFun (congrFun (AddMonoidHom.mem_ker.mp X.2) i) j
        exact (RingHom.mem_ker).mpr h⟩
      invFun := fun g => ⟨Matrix.of fun i j => (g i j).1, by
        rw [AddMonoidHom.mem_ker]
        ext i j
        exact (RingHom.mem_ker).mp (g i j).2⟩
      left_inv := fun X => rfl
      right_inv := fun g => rfl }
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_fun, Nat.card_eq_fintype_card (α := κ), ← pow_mul, sq]
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
    (hc : c ≠ 0) {k : ℕ} (hk : vF 𝔭 c ≤ k) (H : Matrix κ κ (𝓞 K)) :
    Nat.card {X : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ k) //
        Xᴴ * (ι c • H).map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) * X =
          (ι c • H).map (Ideal.Quotient.mk (extP K 𝔭 ^ k))} =
      Ideal.absNorm 𝔭 ^ (2 * vF 𝔭 c * Fintype.card κ ^ 2) *
        Nat.card {X : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ (k - vF 𝔭 c)) //
          Xᴴ * H.map (Ideal.Quotient.mk (extP K 𝔭 ^ (k - vF 𝔭 c))) * X =
            H.map (Ideal.Quotient.mk (extP K 𝔭 ^ (k - vF 𝔭 c)))} := by
  have hHR : (H.map (Ideal.Quotient.mk (extP K 𝔭 ^ k))).map (rd K 𝔭 k (vF 𝔭 c)) =
      H.map (Ideal.Quotient.mk (extP K 𝔭 ^ (k - vF 𝔭 c))) := by
    rw [Matrix.map_map]; rfl
  have key : ∀ X : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ k),
      (Xᴴ * (ι c • H).map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) * X =
          (ι c • H).map (Ideal.Quotient.mk (extP K 𝔭 ^ k))) ↔
        (X.map (rd K 𝔭 k (vF 𝔭 c)))ᴴ * H.map (Ideal.Quotient.mk (extP K 𝔭 ^ (k - vF 𝔭 c))) *
            X.map (rd K 𝔭 k (vF 𝔭 c)) =
          H.map (Ideal.Quotient.mk (extP K 𝔭 ^ (k - vF 𝔭 c))) := by
    intro X
    have hR : (X.map (rd K 𝔭 k (vF 𝔭 c)))ᴴ * H.map (Ideal.Quotient.mk (extP K 𝔭 ^ (k - vF 𝔭 c))) *
        X.map (rd K 𝔭 k (vF 𝔭 c)) =
        (Xᴴ * H.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) * X).map (rd K 𝔭 k (vF 𝔭 c)) := by
      rw [Matrix.map_mul, Matrix.map_mul, ← hHR,
        Matrix.conjTranspose_map _ (fun a => rd_star 𝔭 k (vF 𝔭 c) a)]
    rw [map_smul_mk, Matrix.mul_smul, Matrix.smul_mul, hR, ← hHR, ← Matrix.ext_iff,
      ← Matrix.ext_iff]
    refine forall_congr' fun i => forall_congr' fun j => ?_
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.map_apply]
    exact mul_eq_mul_iff h𝔭 hc hk _ _
  have hsurj : Function.Surjective
      ((rd K 𝔭 k (vF 𝔭 c)).toAddMonoidHom.mapMatrix :
        Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ k) →+ Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ (k - vF 𝔭 c))) := by
    intro Y
    refine ⟨Y.map (Function.surjInv (rd_surjective 𝔭 k (vF 𝔭 c))), ?_⟩
    ext i j
    exact Function.surjInv_eq (rd_surjective 𝔭 k (vF 𝔭 c)) (Y i j)
  rw [Nat.card_congr (Equiv.subtypeEquivRight key)]
  refine (card_subtype_comp_eq_card_mul_card_ker_of_surjective _ hsurj (fun Y => Yᴴ * H.map (Ideal.Quotient.mk (extP K 𝔭 ^ (k - vF 𝔭 c))) * Y =
      H.map (Ideal.Quotient.mk (extP K 𝔭 ^ (k - vF 𝔭 c))))).trans ?_
  rw [card_ker_mapMatrix_eq_card_ker_pow_sq, card_ker_rd hK Fact.out h𝔭 hk, ← pow_mul, mul_comm]
end Formalism.HermitianLattices.Ext.L3.PinAA
