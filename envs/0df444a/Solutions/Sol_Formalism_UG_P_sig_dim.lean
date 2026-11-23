-- Prove2me | solution 1 for Formalism.UG.P.sig_dim
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:18:39.590027+00:00
-- url     : https://prove2.me/submissions/244a0754-2367-4d22-9409-5e24d5294dc9

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureConjugationInvariant
import Theorems.Thm_Formalism_UG_P_sig_quad
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix
namespace Formalism.UG.P
open Formalism.UG
section Sig
variable {n : Type} [Fintype n] [DecidableEq n]
private lemma eq_zero_of_sum_star_mul_self_add_eq_zero {ι κ : Type} [Fintype ι] [Fintype κ] (a : ι → ℂ) (b : κ → ℂ)
    (h : (∑ i, star (a i) * a i) + ∑ j, star (b j) * b j = 0) : a = 0 ∧ b = 0 := by
  have hz : ∀ z : ℂ, star z * z = ((Complex.normSq z : ℝ) : ℂ) := fun z => by
    rw [Complex.normSq_eq_conj_mul_self]; rfl
  simp only [hz] at h
  rw [← Complex.ofReal_sum, ← Complex.ofReal_sum, ← Complex.ofReal_add, Complex.ofReal_eq_zero] at h
  have h1 : 0 ≤ ∑ i, Complex.normSq (a i) := Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have h2 : 0 ≤ ∑ j, Complex.normSq (b j) := Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
  have hA : ∑ i, Complex.normSq (a i) = 0 := by linarith
  have hB : ∑ j, Complex.normSq (b j) = 0 := by linarith
  rw [Finset.sum_eq_zero_iff_of_nonneg fun i _ => Complex.normSq_nonneg _] at hA hB
  exact ⟨funext fun i => Complex.normSq_eq_zero.1 (hA i (Finset.mem_univ _)),
    funext fun j => Complex.normSq_eq_zero.1 (hB j (Finset.mem_univ _))⟩
end Sig
end Formalism.UG.P
end

set_option autoImplicit false
open Matrix
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution {p q p' q' : ℕ} (J : Matrix n n ℂ) (Q : Matrix n (Fin p ⊕ Fin q) ℂ)
    (hQ : Qᴴ * J * Q = Jpq p q) (Q' : Matrix n (Fin p' ⊕ Fin q') ℂ)
    (hQ' : Q'ᴴ * J * Q' = Jpq p' q') :
    p + q' ≤ Fintype.card n := by
  classical

  let φ : ((Fin p → ℂ) × (Fin q' → ℂ)) →ₗ[ℂ] (n → ℂ) :=
    { toFun := fun ab => Q *ᵥ Sum.elim ab.1 (0 : Fin q → ℂ) + Q' *ᵥ Sum.elim (0 : Fin p' → ℂ) ab.2
      map_add' := by
        intro x y
        have h1 : Sum.elim (x.1 + y.1) (0 : Fin q → ℂ) = Sum.elim x.1 (0 : Fin q → ℂ) + Sum.elim y.1 (0 : Fin q → ℂ) := by
          ext (i | i) <;> simp
        have h2 : Sum.elim (0 : Fin p' → ℂ) (x.2 + y.2) = Sum.elim (0 : Fin p' → ℂ) x.2 + Sum.elim (0 : Fin p' → ℂ) y.2 := by
          ext (i | i) <;> simp
        simp only [Prod.fst_add, Prod.snd_add, h1, h2, Matrix.mulVec_add]
        abel
      map_smul' := by
        intro c x
        have h1 : Sum.elim (c • x.1) (0 : Fin q → ℂ) = c • Sum.elim x.1 (0 : Fin q → ℂ) := by
          ext (i | i) <;> simp
        have h2 : Sum.elim (0 : Fin p' → ℂ) (c • x.2) = c • Sum.elim (0 : Fin p' → ℂ) x.2 := by
          ext (i | i) <;> simp
        simp only [Prod.smul_fst, Prod.smul_snd, h1, h2, Matrix.mulVec_smul, RingHom.id_apply,
          smul_add] }
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨a, b⟩ hab
    have hw : Q *ᵥ Sum.elim a (0 : Fin q → ℂ) = Q' *ᵥ (-(Sum.elim (0 : Fin p' → ℂ) b)) := by
      rw [Matrix.mulVec_neg]
      exact eq_neg_of_add_eq_zero_left hab
    have e1 := sig_quad J Q hQ (Sum.elim a (0 : Fin q → ℂ))
    have e2 := sig_quad J Q' hQ' (-(Sum.elim (0 : Fin p' → ℂ) b))
    rw [← hw, e1] at e2
    simp only [Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, Pi.neg_apply, star_zero, mul_zero,
      Finset.sum_const_zero, sub_zero, zero_sub, star_neg, neg_mul_neg] at e2
    have := eq_zero_of_sum_star_mul_self_add_eq_zero a b (by rw [e2]; ring)
    rw [this.1, this.2]
    rfl
  have := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_fin_fun,
    Module.finrank_fintype_fun_eq_card] at this
end Formalism.UG.P
