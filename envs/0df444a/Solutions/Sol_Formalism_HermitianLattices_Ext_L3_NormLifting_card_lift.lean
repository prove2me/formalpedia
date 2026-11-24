-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.NormLifting.card_lift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:46:36.252799+00:00
-- url     : https://prove2.me/submissions/24d73d21-9437-4d25-8bc0-756d300cd3b4

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFiberMulCardRange
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormLifting_card_fiber_mul_card_range
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormLifting_card_eq_mul_of_fibers
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormLifting_mem_fixSub
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormLifting_card_fixSub_sq
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormLifting_linPart_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormLifting_range_linPart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.NormLifting
variable {A B : Type*} [CommRing A] [CommRing B] {σ : A →+* A} {τ : B →+* B} {π : A →+* B}
namespace Formalism.HermitianLattices.Ext.L3.NormLifting
theorem _root_.solution [Finite A] (hπ : Function.Surjective π) (hστ : ∀ a, π (σ a) = τ (π a))
    (hσ : ∀ a, σ (σ a) = a) (hsq : ∀ a b, π a = 0 → π b = 0 → a * b = 0) {θ e : A}
    (he : (θ - σ θ) * e = 1) {n m : A} (hnm : n * m = 1) (hn : σ n = n) (q : ℕ)
    (hq : Nat.card A = q ^ 2 * Nat.card B) (M : ℕ) (hM : 1 ≤ M) :
    Nat.card {x : Fin M → A // ∑ i, σ (x i) * x i = n} =
      q ^ (2 * M - 1) * Nat.card {x : Fin M → B // ∑ i, τ (x i) * x i = π n} := by

  classical
  let I : Ideal A := RingHom.ker π
  have hmemI : ∀ a, a ∈ I ↔ π a = 0 := fun a => RingHom.mem_ker
  have hI : ∀ a ∈ I, σ a ∈ I := by
    intro a ha
    rw [hmemI] at ha ⊢
    rw [hστ, ha, map_zero]
  have hsqI : ∀ a ∈ I, ∀ b ∈ I, a * b = 0 := fun a ha b hb => hsq a b ((hmemI a).mp ha) ((hmemI b).mp hb)
  haveI : Finite B := Finite.of_surjective π hπ
  have hAIB : Nat.card I * Nat.card B = Nat.card A := by
    have h1 := card_fiber_mul_card_range π.toAddMonoidHom 0 (zero_mem _)
    have e1 : {g : A // π.toAddMonoidHom g = 0} ≃ I :=
      { toFun := fun g => ⟨g.1, (hmemI _).mpr g.2⟩
        invFun := fun g => ⟨g.1, (hmemI _).mp g.2⟩
        left_inv := fun g => rfl
        right_inv := fun g => rfl }
    have e2 : (π.toAddMonoidHom.range) ≃ B :=
      { toFun := fun b => b.1
        invFun := fun b => ⟨b, (hπ b).elim fun a ha => ⟨a, ha⟩⟩
        left_inv := fun b => rfl
        right_inv := fun b => rfl }
    rw [Nat.card_congr e1, Nat.card_congr e2] at h1
    exact h1
  have hBpos : 0 < Nat.card B := Nat.card_pos
  have hApos : 0 < Nat.card A := Nat.card_pos
  have hq0 : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · rw [h] at hq
      simp at hq
      omega
    · exact h
  have hIcard : Nat.card I = q ^ 2 := by
    have h1 := hAIB
    rw [hq] at h1
    exact Nat.eq_of_mul_eq_mul_right hBpos h1
  have hFix : Nat.card (fixSub σ I) = q := by
    have h1 := card_fixSub_sq hσ hI he
    rw [hIcard] at h1
    exact Nat.pow_left_injective (by norm_num) h1
  let Φ : {x : Fin M → A // ∑ i, σ (x i) * x i = n} → {x : Fin M → B // ∑ i, τ (x i) * x i = π n} :=
    fun x => ⟨fun i => π (x.1 i), by
      have h1 : ∑ i, τ (π (x.1 i)) * π (x.1 i) = π (∑ i, σ (x.1 i) * x.1 i) := by
        rw [map_sum]
        exact Finset.sum_congr rfl (fun i _ => by rw [map_mul, hστ])
      rw [h1, x.2]⟩
  refine card_eq_mul_of_fibers Φ _ (fun yb => ?_)
  choose lift hlift using hπ
  let y : Fin M → A := fun i => lift (yb.1 i)
  have hyπ : ∀ i, π (y i) = yb.1 i := fun i => hlift _
  have hwI : n - ∑ i, σ (y i) * y i ∈ I := by
    rw [hmemI, map_sub, map_sum]
    have h1 : ∑ i, π (σ (y i) * y i) = ∑ i, τ (yb.1 i) * yb.1 i :=
      Finset.sum_congr rfl (fun i _ => by rw [map_mul, hστ, hyπ])
    rw [h1, yb.2, sub_self]
  have hwσ : σ (n - ∑ i, σ (y i) * y i) = n - ∑ i, σ (y i) * y i := by
    rw [map_sub, hn, map_sum]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => by rw [map_mul, hσ, mul_comm])
  have hwR : n - ∑ i, σ (y i) * y i ∈ (linPart σ I y).range := by
    rw [range_linPart hσ hI hsqI he hnm y hwI]
    exact (mem_fixSub σ I).mpr ⟨hwI, hwσ⟩
  have h1 := card_fiber_mul_card_range (linPart σ I y) _ hwR
  rw [range_linPart hσ hI hsqI he hnm y hwI, hFix] at h1
  have hcardI : Nat.card (Fin M → I) = q ^ (2 * M) := by
    rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hIcard, ← pow_mul]
  rw [hcardI] at h1
  have key : ∀ x : Fin M → A, ∀ hx : ∀ i, x i - y i ∈ I,
      ∑ i, σ (x i) * x i = ∑ i, σ (y i) * y i + linPart σ I y (fun i => ⟨x i - y i, hx i⟩) := by
    intro x hx
    rw [linPart_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have h0 : σ (x i - y i) * (x i - y i) = 0 := hsqI _ (hI _ (hx i)) _ (hx i)
    simp only [map_sub] at h0 ⊢
    linear_combination h0
  have hmem : ∀ x : {x : {x : Fin M → A // ∑ i, σ (x i) * x i = n} // Φ x = yb}, ∀ i, x.1.1 i - y i ∈ I := by
    intro x i
    rw [hmemI, map_sub, hyπ]
    have h2 := congrArg (fun z : {x : Fin M → B // ∑ i, τ (x i) * x i = π n} => z.1 i) x.2
    simp only [Φ] at h2
    rw [h2, sub_self]
  have e : {x : {x : Fin M → A // ∑ i, σ (x i) * x i = n} // Φ x = yb} ≃
      {δ : Fin M → I // linPart σ I y δ = n - ∑ i, σ (y i) * y i} :=
    { toFun := fun x => ⟨fun i => ⟨x.1.1 i - y i, hmem x i⟩, by
          have h2 := key x.1.1 (hmem x)
          rw [x.1.2] at h2
          linear_combination -h2⟩
      invFun := fun δ => ⟨⟨fun i => y i + δ.1 i, by
            have h2 := key (fun i => y i + δ.1 i) (fun i => by simp [(δ.1 i).2])
            rw [h2]
            have h3 : (fun i => (⟨y i + (δ.1 i : A) - y i, by simp [(δ.1 i).2]⟩ : I)) = δ.1 := by
              funext i
              apply Subtype.ext
              simp
            rw [h3, δ.2]
            ring⟩, by
          apply Subtype.ext
          funext i
          simp only [Φ]
          rw [map_add, hyπ, (hmemI _).mp (δ.1 i).2, add_zero]⟩
      left_inv := fun x => by
        apply Subtype.ext
        apply Subtype.ext
        funext i
        simp
      right_inv := fun δ => by
        apply Subtype.ext
        funext i
        apply Subtype.ext
        simp }
  rw [Nat.card_congr e]
  have h4 : q ^ (2 * M) = q ^ (2 * M - 1) * q := by
    rw [← pow_succ]
    congr 1
    omega
  rw [h4] at h1
  exact Nat.eq_of_mul_eq_mul_right hq0 h1
end Formalism.HermitianLattices.Ext.L3.NormLifting
