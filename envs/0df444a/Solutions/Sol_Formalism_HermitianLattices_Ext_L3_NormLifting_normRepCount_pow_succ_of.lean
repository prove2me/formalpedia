-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.NormLifting.normRepCount_pow_succ_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:30.295482+00:00
-- url     : https://prove2.me/submissions/24c705cb-1afb-4b38-9d4f-4f9fb7b95981

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFiberMulCardRange
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountPowSuccInert
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormLifting_conjO_conjO
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormLifting_conjQ_mk
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormLifting_normRepCount_eq
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormLifting_exists_inv_mod
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormLifting_stable_pow
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormLifting_card_lift
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjO_conjO


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.NormLifting
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.HermitianLattices.Ext.L3.NormLifting
theorem _root_.solution {Q : Ideal (𝓞 K)} (hQ0 : Q ≠ ⊥) (hQ : Q.map (conjO K) = Q)
    (θ n : 𝓞 K) (hθ : IsCoprime (Ideal.span {θ - conjO K θ}) Q)
    (hnQ : IsCoprime (Ideal.span {n}) Q) (hn : conjO K n = n) (q : ℕ)
    (hq : Ideal.absNorm Q = q ^ 2) (M k : ℕ) (hM : 1 ≤ M) (hk : 1 ≤ k) :
    normRepCount K (Q ^ (k + 1)) M n = q ^ (2 * M - 1) * normRepCount K (Q ^ k) M n := by
  rw [normRepCount_eq _ (stable_pow hQ (k + 1)), normRepCount_eq _ (stable_pow hQ k)]
  have hle : Q ^ (k + 1) ≤ Q ^ k := Ideal.pow_le_pow_right (Nat.le_succ k)
  have : Finite (𝓞 K ⧸ Q ^ (k + 1)) := Ideal.finiteQuotientOfFreeOfNeBot _ (pow_ne_zero _ hQ0)
  obtain ⟨e, he⟩ := exists_inv_mod (hθ.pow_right (n := k + 1))
  obtain ⟨m, hm⟩ := exists_inv_mod (hnQ.pow_right (n := k + 1))
  have h := card_lift (σ := conjQ _ (stable_pow hQ (k + 1))) (τ := conjQ _ (stable_pow hQ k))
    (π := Ideal.Quotient.factor hle) (Ideal.Quotient.factor_surjective hle)
    (by
      intro a
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [conjQ_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk, conjQ_mk])
    (by
      intro a
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [conjQ_mk, conjQ_mk, conjO_conjO])
    (by
      intro a b ha hb
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
      rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at ha hb
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      have h2 : a * b ∈ Q ^ (k + k) := by rw [pow_add]; exact Ideal.mul_mem_mul ha hb
      exact Ideal.pow_le_pow_right (by omega) h2)
    (θ := Ideal.Quotient.mk _ θ) (e := Ideal.Quotient.mk _ e)
    (by rw [conjQ_mk, ← map_sub]; exact he)
    (n := Ideal.Quotient.mk _ n) (m := Ideal.Quotient.mk _ m) hm
    (by rw [conjQ_mk, hn]) q
    (by
      have h1 : ∀ J : Ideal (𝓞 K), Nat.card (𝓞 K ⧸ J) = Ideal.absNorm J := fun J => by
        rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
      rw [h1, h1, map_pow, map_pow, hq]; ring) M hM
  rw [Ideal.Quotient.factor_mk] at h
  exact h
end Formalism.HermitianLattices.Ext.L3.NormLifting
