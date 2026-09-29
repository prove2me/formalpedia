-- Prove2me | solution 1 for GaloisRepAdic.exists_inertia_labels_mul_dichotomy_of_forall_wild_apply_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/680c354b-e7b6-5615-acf5-c532946772ee

import Definitions.Def_GaloisRep_Adic
import Mathlib
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_GaloisRepAdic_exists_charpoly_inertia_eq_and_pow_sq_sub_one_eq_one_of_forall_mem_inertiaSubgroupIn_wild_apply_eq_one
import Theorems.Thm_ValuationSubring_tameCharacter_mul_of_mem_inertiaSubgroupIn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRepAdic_exists_inertia_labels_mul_dichotomy_of_forall_wild_apply_eq_one

set_option autoImplicit false

open Polynomial

namespace GaloisRepAdic
p2m_export "GaloisRepAdic" "det finrank_eq ρ V exists_charpoly_inertia_eq_and_pow_sq_sub_one_eq_one_of_forall_mem_inertiaSubgroupIn_wild_apply_eq_one"
namespace MultLabels
p2m_open "GaloisRepAdic"

open Polynomial

private theorem tameCharacter_eq_residue (P : ValuationSubring (AlgebraicClosure ℚ)) {π : AlgebraicClosure ℚ}
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (x : P) (hx : σ π / π = x) :
    P.tameCharacter π σ = IsLocalRing.residue P x := by
  unfold ValuationSubring.tameCharacter
  have hmem : σ π / π ∈ P := hx ▸ x.2
  rw [dif_pos hmem]
  congr 1
  exact Subtype.ext hx

private theorem tameCharacter_one (P : ValuationSubring (AlgebraicClosure ℚ)) {z : AlgebraicClosure ℚ}
    (hz : z ≠ 0) : P.tameCharacter z 1 = 1 := by
  rw [tameCharacter_eq_residue P 1 (by rw [AlgEquiv.one_apply, div_self hz, OneMemClass.coe_one]), map_one]

private theorem tameCharacter_mul_inv_eq_one (P : ValuationSubring (AlgebraicClosure ℚ))
    {z : AlgebraicClosure ℚ} (hz : z ≠ 0) {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hσ : σ ∈ P.inertiaSubgroupIn ℚ) : P.tameCharacter z σ * P.tameCharacter z σ⁻¹ = 1 := by
  rw [← ValuationSubring.tameCharacter_mul_of_mem_inertiaSubgroupIn P z hz hσ σ⁻¹, mul_inv_cancel,
    tameCharacter_one P hz]

private theorem tameCharacter_commutator_eq_one (P : ValuationSubring (AlgebraicClosure ℚ))
    {z : AlgebraicClosure ℚ} (hz : z ≠ 0) {σ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hσ : σ ∈ P.inertiaSubgroupIn ℚ) (hτ : τ ∈ P.inertiaSubgroupIn ℚ) :
    P.tameCharacter z (σ * τ * σ⁻¹ * τ⁻¹) = 1 := by
  have hστ : σ * τ ∈ P.inertiaSubgroupIn ℚ := mul_mem hσ hτ
  have hστσ : σ * τ * σ⁻¹ ∈ P.inertiaSubgroupIn ℚ := mul_mem hστ (inv_mem hσ)
  rw [ValuationSubring.tameCharacter_mul_of_mem_inertiaSubgroupIn P z hz hστσ τ⁻¹,
    ValuationSubring.tameCharacter_mul_of_mem_inertiaSubgroupIn P z hz hστ σ⁻¹,
    ValuationSubring.tameCharacter_mul_of_mem_inertiaSubgroupIn P z hz hσ τ]
  calc P.tameCharacter z σ * P.tameCharacter z τ * P.tameCharacter z σ⁻¹ * P.tameCharacter z τ⁻¹
      = (P.tameCharacter z σ * P.tameCharacter z σ⁻¹) * (P.tameCharacter z τ * P.tameCharacter z τ⁻¹) := by
        ring
    _ = 1 := by rw [tameCharacter_mul_inv_eq_one P hz hσ, tameCharacter_mul_inv_eq_one P hz hτ, one_mul]

private theorem wild_at_of_tameCharacter_eq_one (P : ValuationSubring (AlgebraicClosure ℚ))
    {z : AlgebraicClosure ℚ} {γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (h : P.tameCharacter z γ = 1) : γ z * z⁻¹ - 1 ∈ P.nonunits := by
  unfold ValuationSubring.tameCharacter at h
  by_cases hmem : γ z / z ∈ P
  · rw [dif_pos hmem] at h
    have hsub : (⟨γ z / z, hmem⟩ : P) - 1 ∈ IsLocalRing.maximalIdeal P := by
      rw [← Ideal.Quotient.eq, map_one]
      exact h
    have := (ValuationSubring.coe_mem_nonunits_iff (a := (⟨γ z / z, hmem⟩ : P) - 1)).mpr hsub
    simpa [div_eq_mul_inv] using this
  · rw [dif_neg hmem] at h
    exact absurd h zero_ne_one

private theorem commutator_wild (P : ValuationSubring (AlgebraicClosure ℚ))
    {σ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hσ : σ ∈ P.inertiaSubgroupIn ℚ) (hτ : τ ∈ P.inertiaSubgroupIn ℚ) :
    ∀ z : AlgebraicClosure ℚ, z ≠ 0 → (σ * τ * σ⁻¹ * τ⁻¹) z * z⁻¹ - 1 ∈ P.nonunits :=
  fun _ hz => wild_at_of_tameCharacter_eq_one P (tameCharacter_commutator_eq_one P hz hσ hτ)

private theorem apply_mul_apply_comm {O' : Type} [CommRing O'] [IsLocalRing O'] (ρ : GaloisRepAdic O')
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (htame : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      σ ∈ P.inertiaSubgroupIn ℚ →
        (∀ z : AlgebraicClosure ℚ, z ≠ 0 → σ z * z⁻¹ - 1 ∈ P.nonunits) → ρ.ρ σ = 1)
    {σ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hσ : σ ∈ P.inertiaSubgroupIn ℚ) (hτ : τ ∈ P.inertiaSubgroupIn ℚ) :
    ρ.ρ σ * ρ.ρ τ = ρ.ρ τ * ρ.ρ σ := by
  have hc : σ * τ * σ⁻¹ * τ⁻¹ ∈ P.inertiaSubgroupIn ℚ :=
    mul_mem (mul_mem (mul_mem hσ hτ) (inv_mem hσ)) (inv_mem hτ)
  have h1 : ρ.ρ (σ * τ * σ⁻¹ * τ⁻¹) = 1 := htame _ hc (commutator_wild P hσ hτ)
  have hmul : σ * τ * σ⁻¹ * τ⁻¹ * (τ * σ) = σ * τ := by
    rw [mul_assoc, ← mul_assoc τ⁻¹, inv_mul_cancel, one_mul, inv_mul_cancel_right]
  have := congrArg ρ.ρ hmul
  rw [map_mul, h1, one_mul, map_mul, map_mul] at this
  exact this.symm

section Domain

variable {R : Type} [CommRing R] [IsDomain R]

private theorem roots_pair_of_mul_eq {a b c d : R}
    (h : (X - C a) * (X - C b) = (X - C c) * (X - C d)) : (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have ha : (a - c) * (a - d) = 0 := by
    have := congrArg (Polynomial.eval a) h
    simpa only [eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul] using this.symm
  rcases mul_eq_zero.mp ha with hac | had
  · left
    refine ⟨sub_eq_zero.mp hac, ?_⟩
    rw [sub_eq_zero.mp hac] at h
    have := mul_left_cancel₀ (X_sub_C_ne_zero c) h
    exact Polynomial.C_injective (sub_right_inj.mp this)
  · right
    refine ⟨sub_eq_zero.mp had, ?_⟩
    rw [sub_eq_zero.mp had, mul_comm (X - C c)] at h
    have := mul_left_cancel₀ (X_sub_C_ne_zero d) h
    exact Polynomial.C_injective (sub_right_inj.mp this)

private theorem eq_zero_of_smul_vec_eq_zero {c : R} {v : Fin 2 → R} (h : c • v = 0) (hv : v ≠ 0) : c = 0 := by
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hv
  have hk' : c * v k = 0 := by simpa using congrFun h k
  exact (mul_eq_zero.mp hk').resolve_right hk

private theorem vec_eq_zero_of_smul_eq_zero {c : R} {v : Fin 2 → R} (h : c • v = 0) (hc : c ≠ 0) : v = 0 := by
  funext k
  have hk' : c * v k = 0 := by simpa using congrFun h k
  simpa using (mul_eq_zero.mp hk').resolve_left hc

private theorem parallel_of_mulVec_eq_zero {N : Matrix (Fin 2) (Fin 2) R} (hN : N ≠ 0)
    {x y : Fin 2 → R} (hx : N.mulVec x = 0) (hy : N.mulVec y = 0) : x 0 * y 1 = x 1 * y 0 := by

  have hrow : ∀ i : Fin 2, N i 0 * x 0 + N i 1 * x 1 = 0 ∧ N i 0 * y 0 + N i 1 * y 1 = 0 := by
    intro i
    have ex := congrFun hx i
    have ey := congrFun hy i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.zero_apply] at ex ey
    exact ⟨ex, ey⟩
  by_contra hne
  apply hN
  ext i k
  obtain ⟨ex, ey⟩ := hrow i
  have h0 : N i 0 * (x 0 * y 1 - x 1 * y 0) = 0 := by
    linear_combination y 1 * ex - x 1 * ey
  have h1 : N i 1 * (x 0 * y 1 - x 1 * y 0) = 0 := by
    linear_combination x 0 * ey - y 0 * ex
  have hd : x 0 * y 1 - x 1 * y 0 ≠ 0 := fun h => hne (sub_eq_zero.mp h)
  rw [Matrix.zero_apply]
  fin_cases k
  · exact (mul_eq_zero.mp h0).resolve_right hd
  · exact (mul_eq_zero.mp h1).resolve_right hd

private theorem mulVec_eq_smul_or_of_commute {N B : Matrix (Fin 2) (Fin 2) R} (hN : N ≠ 0)
    (hcomm : N * B = B * N) {v : Fin 2 → R} (hv : v ≠ 0) (hNv : N.mulVec v = 0) {α β : R}
    (hB : (B - α • (1 : Matrix (Fin 2) (Fin 2) R)) * (B - β • (1 : Matrix (Fin 2) (Fin 2) R)) = 0) :
    B.mulVec v = α • v ∨ B.mulVec v = β • v := by

  set u : Fin 2 → R := (B - β • (1 : Matrix (Fin 2) (Fin 2) R)).mulVec v with hu
  have hBu : (B - α • (1 : Matrix (Fin 2) (Fin 2) R)).mulVec u = 0 := by
    rw [hu, Matrix.mulVec_mulVec, hB, Matrix.zero_mulVec]
  have hNu : N.mulVec u = 0 := by
    have hc : N * (B - β • (1 : Matrix (Fin 2) (Fin 2) R)) =
        (B - β • (1 : Matrix (Fin 2) (Fin 2) R)) * N := by
      rw [mul_sub, sub_mul, hcomm, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
    rw [hu, Matrix.mulVec_mulVec, hc, ← Matrix.mulVec_mulVec, hNv, Matrix.mulVec_zero]
  by_cases hu0 : u = 0
  · right
    have : B.mulVec v - β • v = 0 := by
      rw [← hu0, hu, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    exact sub_eq_zero.mp this
  · left

    have hpar := parallel_of_mulVec_eq_zero hN hNu hNv
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hv
    rw [Pi.zero_apply] at hk
    have huk : u k ≠ 0 := by
      intro huk
      apply hu0
      funext l
      rw [Pi.zero_apply]
      fin_cases k <;> fin_cases l
      · simpa using huk
      · have h0 : u 0 = 0 := by simpa using huk
        have : u 1 * v 0 = 0 := by rw [← hpar, h0, zero_mul]
        exact (mul_eq_zero.mp this).resolve_right (by simpa using hk)
      · have h1 : u 1 = 0 := by simpa using huk
        have : u 0 * v 1 = 0 := by rw [hpar, h1, zero_mul]
        exact (mul_eq_zero.mp this).resolve_right (by simpa using hk)
      · simpa using huk
    have hvec : v k • u = u k • v := by
      funext l
      simp only [Pi.smul_apply, smul_eq_mul]
      fin_cases k <;> fin_cases l
      · exact mul_comm _ _
      · simp only [Fin.zero_eta, Fin.mk_one]
        linear_combination -hpar
      · simp only [Fin.zero_eta, Fin.mk_one]
        linear_combination hpar
      · exact mul_comm _ _
    have happ := congrArg (fun w => (B - α • (1 : Matrix (Fin 2) (Fin 2) R)).mulVec w) hvec
    simp only [Matrix.mulVec_smul] at happ
    rw [hBu, smul_zero] at happ
    have h0 := vec_eq_zero_of_smul_eq_zero happ.symm huk
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at h0
    exact h0

private theorem forall_or_forall_of_forall_or {G : Type} [Group G] {I : Subgroup G} {S T : G → Prop}
    (hS1 : ∀ σ ∈ I, ∀ τ ∈ I, S σ → S τ → S (σ * τ)) (hS2 : ∀ σ ∈ I, S σ → S σ⁻¹)
    (hT1 : ∀ σ ∈ I, ∀ τ ∈ I, T σ → T τ → T (σ * τ)) (hT2 : ∀ σ ∈ I, T σ → T σ⁻¹)
    (h : ∀ σ ∈ I, S σ ∨ T σ) : (∀ σ ∈ I, S σ) ∨ (∀ σ ∈ I, T σ) := by
  by_contra hcon
  rw [not_or, not_forall, not_forall] at hcon
  obtain ⟨⟨σ, hσ⟩, ⟨τ, hτ⟩⟩ := hcon
  rw [Classical.not_imp] at hσ hτ
  obtain ⟨hσI, hσS⟩ := hσ
  obtain ⟨hτI, hτT⟩ := hτ
  have hσT : T σ := (h σ hσI).resolve_left hσS
  have hτS : S τ := (h τ hτI).resolve_right hτT
  rcases h (σ * τ) (mul_mem hσI hτI) with hst | hst
  ·
    have := hS1 _ (mul_mem hσI hτI) _ (inv_mem hτI) hst (hS2 τ hτI hτS)
    rw [mul_inv_cancel_right] at this
    exact hσS this
  ·
    have := hT1 _ (inv_mem hσI) _ (mul_mem hσI hτI) (hT2 σ hσI hσT) hst
    rw [inv_mul_cancel_left] at this
    exact hτT this

end Domain

theorem exists_inertia_labels_mul_dichotomy_of_forall_wild_apply_eq_one
    {O' : Type} [CommRing O'] [IsLocalRing O'] (ρ : GaloisRepAdic O')
    {q : ℕ} [Fact q.Prime]
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (htame : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      σ ∈ P.inertiaSubgroupIn ℚ →
        (∀ z : AlgebraicClosure ℚ, z ≠ 0 → σ z * z⁻¹ - 1 ∈ P.nonunits) → ρ.ρ σ = 1)
    {O'' : Type} [CommRing O''] [IsDomain O''] (j : O' →+* O'')
    (hsplit : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∃ α β : O'',
      (LinearMap.charpoly (ρ.ρ σ)).map j = (X - C α) * (X - C β)) :
    ∃ a b : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → O''ˣ,
      (∀ σ ∈ P.inertiaSubgroupIn ℚ,
        (LinearMap.charpoly (ρ.ρ σ)).map j = (X - C ((a σ : O''ˣ) : O'')) * (X - C ((b σ : O''ˣ) : O''))) ∧
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ τ ∈ P.inertiaSubgroupIn ℚ,
        a (σ * τ) = a σ * a τ ∧ b (σ * τ) = b σ * b τ) ∧
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, a σ ^ (q ^ 2 - 1) = 1 ∧ b σ ^ (q ^ 2 - 1) = 1) ∧
      ((∀ σ ∈ P.inertiaSubgroupIn ℚ, a σ ^ (q - 1) = 1 ∧ b σ ^ (q - 1) = 1) ∨
        (∀ σ ∈ P.inertiaSubgroupIn ℚ, b σ = a σ ^ q ∧ a σ = b σ ^ q)) ∧
      (∀ σ ∈ P.inertiaSubgroupIn ℚ,
        (∀ z : AlgebraicClosure ℚ, z ≠ 0 → σ z * z⁻¹ - 1 ∈ P.nonunits) → a σ = 1 ∧ b σ = 1) := by
  classical
  have hq : q.Prime := Fact.out

  obtain ⟨bV⟩ : Nonempty (Module.Basis (Fin 2) O' ρ.V) := ⟨Module.finBasisOfFinrankEq O' ρ.V ρ.finrank_eq⟩
  obtain ⟨A, hA⟩ : ∃ A : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → Matrix (Fin 2) (Fin 2) O'',
      ∀ σ, A σ = (LinearMap.toMatrix bV bV (ρ.ρ σ)).map j := ⟨_, fun _ => rfl⟩
  have A_mul : ∀ σ τ, A (σ * τ) = A σ * A τ := by
    intro σ τ
    rw [hA, hA, hA, map_mul, LinearMap.toMatrix_mul, Matrix.map_mul]
  have A_comm : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ τ ∈ P.inertiaSubgroupIn ℚ, A σ * A τ = A τ * A σ := by
    intro σ hσ τ hτ
    rw [← A_mul, ← A_mul, hA, hA, map_mul ρ.ρ σ τ, map_mul ρ.ρ τ σ, apply_mul_apply_comm ρ P htame hσ hτ]
  have A_charpoly : ∀ σ, (A σ).charpoly = (LinearMap.charpoly (ρ.ρ σ)).map j := by
    intro σ
    rw [hA, Matrix.charpoly_map, LinearMap.charpoly_toMatrix]
  have A_det : ∀ σ, (A σ).det = j (LinearMap.det (ρ.ρ σ)) := by
    intro σ
    rw [hA, ← RingHom.mapMatrix_apply, ← RingHom.map_det, LinearMap.det_toMatrix]
  have A_det_unit : ∀ σ, IsUnit (A σ).det := fun σ => by
    rw [A_det]
    exact (((Group.isUnit σ).map ρ.ρ).map LinearMap.det).map j

  have hsplit' := hsplit
  choose! α β hαβ using hsplit'
  have A_CH : ∀ σ ∈ P.inertiaSubgroupIn ℚ,
      (A σ - α σ • (1 : Matrix (Fin 2) (Fin 2) O'')) * (A σ - β σ • (1 : Matrix (Fin 2) (Fin 2) O'')) = 0 := by
    intro σ hσ
    have h := Matrix.aeval_self_charpoly (A σ)
    rw [A_charpoly, hαβ σ hσ, map_mul, map_sub, map_sub, aeval_X, aeval_C, aeval_C,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one] at h
    exact h

  have hv : ∃ v : Fin 2 → O'', v ≠ 0 ∧
      ∀ σ ∈ P.inertiaSubgroupIn ℚ, (A σ).mulVec v = α σ • v ∨ (A σ).mulVec v = β σ • v := by
    by_cases hsc : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∃ c : O'', A σ = c • (1 : Matrix (Fin 2) (Fin 2) O'')
    · refine ⟨fun _ => 1, fun h => one_ne_zero (congrFun h 0), fun σ hσ => ?_⟩
      obtain ⟨c, hc⟩ := hsc σ hσ
      have hcc : (c - α σ) * (c - β σ) = 0 := by
        have h := A_CH σ hσ
        rw [hc, ← sub_smul, ← sub_smul, smul_mul_assoc, mul_smul_comm, smul_smul, one_mul] at h
        have h00 := congrFun (congrFun h 0) 0
        simpa only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, Matrix.zero_apply] using h00
      have hAv : (A σ).mulVec (fun _ => (1 : O'')) = c • fun _ => (1 : O'') := by
        rw [hc, Matrix.smul_mulVec, Matrix.one_mulVec]
      rcases mul_eq_zero.mp hcc with h | h
      · left
        rw [hAv, sub_eq_zero.mp h]
      · right
        rw [hAv, sub_eq_zero.mp h]
    · rw [not_forall] at hsc
      obtain ⟨σ₀, hσ₀⟩ := hsc
      rw [Classical.not_imp] at hσ₀
      obtain ⟨hσ₀I, hns⟩ := hσ₀
      have hne : ∀ c : O'', A σ₀ - c • (1 : Matrix (Fin 2) (Fin 2) O'') ≠ 0 :=
        fun c h => hns ⟨c, sub_eq_zero.mp h⟩
      have hdet : (A σ₀ - α σ₀ • (1 : Matrix (Fin 2) (Fin 2) O'')).det = 0 ∨
          (A σ₀ - β σ₀ • (1 : Matrix (Fin 2) (Fin 2) O'')).det = 0 := by
        have h := congrArg Matrix.det (A_CH σ₀ hσ₀I)
        rw [Matrix.det_mul, Matrix.det_zero] at h
        exact mul_eq_zero.mp h
      obtain ⟨γ, hN0, hNdet⟩ : ∃ γ : O'', A σ₀ - γ • (1 : Matrix (Fin 2) (Fin 2) O'') ≠ 0 ∧
          (A σ₀ - γ • (1 : Matrix (Fin 2) (Fin 2) O'')).det = 0 := by
        rcases hdet with h | h
        · exact ⟨α σ₀, hne _, h⟩
        · exact ⟨β σ₀, hne _, h⟩
      obtain ⟨v, hv0, hNv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hNdet
      refine ⟨v, hv0, fun σ hσ => ?_⟩
      have hc : (A σ₀ - γ • (1 : Matrix (Fin 2) (Fin 2) O'')) * A σ =
          A σ * (A σ₀ - γ • (1 : Matrix (Fin 2) (Fin 2) O'')) := by
        rw [sub_mul, mul_sub, A_comm σ₀ hσ₀I σ hσ, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
      exact mulVec_eq_smul_or_of_commute hN0 hc hv0 hNv (A_CH σ hσ)
  obtain ⟨v, hv0, hv⟩ := hv

  obtain ⟨a', ha'⟩ : ∃ a' : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → O'',
      ∀ σ, a' σ = if (A σ).mulVec v = α σ • v then α σ else β σ := ⟨_, fun _ => rfl⟩
  obtain ⟨b', hb'⟩ : ∃ b' : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → O'',
      ∀ σ, b' σ = if (A σ).mulVec v = α σ • v then β σ else α σ := ⟨_, fun _ => rfl⟩
  have hav : ∀ σ ∈ P.inertiaSubgroupIn ℚ, (A σ).mulVec v = a' σ • v := by
    intro σ hσ
    rw [ha']
    split_ifs with h
    · exact h
    · exact (hv σ hσ).resolve_left h
  have hab' : ∀ σ ∈ P.inertiaSubgroupIn ℚ,
      (LinearMap.charpoly (ρ.ρ σ)).map j = (X - C (a' σ)) * (X - C (b' σ)) := by
    intro σ hσ
    rw [ha', hb']
    split_ifs with h
    · exact hαβ σ hσ
    · rw [mul_comm]
      exact hαβ σ hσ
  have hdet' : ∀ σ ∈ P.inertiaSubgroupIn ℚ, (A σ).det = a' σ * b' σ := by
    intro σ hσ
    rw [Matrix.det_eq_sign_charpoly_coeff, A_charpoly, hab' σ hσ, Fintype.card_fin,
      Polynomial.coeff_zero_eq_eval_zero, eval_mul, eval_sub, eval_sub, eval_X, eval_C, eval_C]
    ring
  have hunit' : ∀ σ ∈ P.inertiaSubgroupIn ℚ, IsUnit (a' σ) ∧ IsUnit (b' σ) := by
    intro σ hσ
    exact IsUnit.mul_iff.mp (hdet' σ hσ ▸ A_det_unit σ)

  have ha'mul : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ τ ∈ P.inertiaSubgroupIn ℚ, a' (σ * τ) = a' σ * a' τ := by
    intro σ hσ τ hτ
    have h1 : (A (σ * τ)).mulVec v = (a' σ * a' τ) • v := by
      rw [A_mul, ← Matrix.mulVec_mulVec, hav τ hτ, Matrix.mulVec_smul, hav σ hσ, smul_smul, mul_comm]
    rw [hav (σ * τ) (mul_mem hσ hτ)] at h1
    have h2 : (a' (σ * τ) - a' σ * a' τ) • v = 0 := by rw [sub_smul, h1, sub_self]
    exact sub_eq_zero.mp (eq_zero_of_smul_vec_eq_zero h2 hv0)
  have hb'mul : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ τ ∈ P.inertiaSubgroupIn ℚ, b' (σ * τ) = b' σ * b' τ := by
    intro σ hσ τ hτ
    have hd : (A (σ * τ)).det = (A σ).det * (A τ).det := by rw [A_mul, Matrix.det_mul]
    rw [hdet' _ (mul_mem hσ hτ), hdet' σ hσ, hdet' τ hτ, ha'mul σ hσ τ hτ] at hd
    have hne : a' σ * a' τ ≠ 0 := ((hunit' σ hσ).1.mul (hunit' τ hτ).1).ne_zero
    have : a' σ * a' τ * b' (σ * τ) = a' σ * a' τ * (b' σ * b' τ) := by linear_combination hd
    exact mul_left_cancel₀ hne this

  obtain ⟨a₁, b₁, hG⟩ :=
   GaloisRepAdic.exists_charpoly_inertia_eq_and_pow_sq_sub_one_eq_one_of_forall_mem_inertiaSubgroupIn_wild_apply_eq_one
      ρ P hP htame j hsplit

  obtain ⟨a, ha⟩ : ∃ a : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → O''ˣ,
      ∀ σ, a σ = if a' σ = ((a₁ σ : O''ˣ) : O'') then a₁ σ else b₁ σ := ⟨_, fun _ => rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → O''ˣ,
      ∀ σ, b σ = if a' σ = ((a₁ σ : O''ˣ) : O'') then b₁ σ else a₁ σ := ⟨_, fun _ => rfl⟩
  have hmatch : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ((a σ : O''ˣ) : O'') = a' σ ∧ ((b σ : O''ˣ) : O'') = b' σ ∧
      ((a σ = a₁ σ ∧ b σ = b₁ σ) ∨ (a σ = b₁ σ ∧ b σ = a₁ σ)) := by
    intro σ hσ
    have hp := roots_pair_of_mul_eq ((hab' σ hσ).symm.trans (hG σ hσ).1)
    rw [ha, hb]
    split_ifs with h
    · refine ⟨h.symm, ?_, Or.inl ⟨rfl, rfl⟩⟩
      rcases hp with ⟨_, h2⟩ | ⟨h1, h2⟩
      · exact h2.symm
      · rw [h2, ← h1, h]
    · refine ⟨?_, ?_, Or.inr ⟨rfl, rfl⟩⟩
      · rcases hp with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact absurd h1 h
        · exact h1.symm
      · rcases hp with ⟨h1, _⟩ | ⟨_, h2⟩
        · exact absurd h1 h
        · exact h2.symm

  have hi : ∀ σ ∈ P.inertiaSubgroupIn ℚ,
      (LinearMap.charpoly (ρ.ρ σ)).map j = (X - C ((a σ : O''ˣ) : O'')) * (X - C ((b σ : O''ˣ) : O'')) := by
    intro σ hσ
    obtain ⟨h1, h2, -⟩ := hmatch σ hσ
    rw [h1, h2]
    exact hab' σ hσ
  have hmul : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ τ ∈ P.inertiaSubgroupIn ℚ,
      a (σ * τ) = a σ * a τ ∧ b (σ * τ) = b σ * b τ := by
    intro σ hσ τ hτ
    obtain ⟨h1, h2, -⟩ := hmatch σ hσ
    obtain ⟨h3, h4, -⟩ := hmatch τ hτ
    obtain ⟨h5, h6, -⟩ := hmatch _ (mul_mem hσ hτ)
    exact ⟨Units.ext (by rw [Units.val_mul, h1, h3, h5]; exact ha'mul σ hσ τ hτ),
      Units.ext (by rw [Units.val_mul, h2, h4, h6]; exact hb'mul σ hσ τ hτ)⟩
  have hiii : ∀ σ ∈ P.inertiaSubgroupIn ℚ, a σ ^ (q ^ 2 - 1) = 1 ∧ b σ ^ (q ^ 2 - 1) = 1 := by
    intro σ hσ
    obtain ⟨-, -, hc⟩ := hmatch σ hσ
    rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
      exact (hG σ hσ).2.2
    · rw [h1, h2]
      exact ⟨(hG σ hσ).2.2.2, (hG σ hσ).2.2.1⟩
  have hii : ∀ σ ∈ P.inertiaSubgroupIn ℚ,
      (X - C (((a σ) ^ q : O''ˣ) : O'')) * (X - C (((b σ) ^ q : O''ˣ) : O'')) =
        (X - C ((a σ : O''ˣ) : O'')) * (X - C ((b σ : O''ˣ) : O'')) := by
    intro σ hσ
    obtain ⟨-, -, hc⟩ := hmatch σ hσ
    rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
      exact (hG σ hσ).2.1
    · rw [h1, h2, mul_comm, (hG σ hσ).2.1, mul_comm]

  have ha1 : a 1 = 1 := by
    have h := (hmul 1 (one_mem _) 1 (one_mem _)).1
    rw [mul_one] at h
    have h' : a 1 * a 1 = a 1 * 1 := by rw [mul_one]; exact h.symm
    exact mul_left_cancel h'
  have hb1 : b 1 = 1 := by
    have h := (hmul 1 (one_mem _) 1 (one_mem _)).2
    rw [mul_one] at h
    have h' : b 1 * b 1 = b 1 * 1 := by rw [mul_one]; exact h.symm
    exact mul_left_cancel h'
  have hainv : ∀ σ ∈ P.inertiaSubgroupIn ℚ, a σ⁻¹ = (a σ)⁻¹ := by
    intro σ hσ
    apply eq_inv_of_mul_eq_one_left
    rw [← (hmul _ (inv_mem hσ) σ hσ).1, inv_mul_cancel, ha1]
  have hbinv : ∀ σ ∈ P.inertiaSubgroupIn ℚ, b σ⁻¹ = (b σ)⁻¹ := by
    intro σ hσ
    apply eq_inv_of_mul_eq_one_left
    rw [← (hmul _ (inv_mem hσ) σ hσ).2, inv_mul_cancel, hb1]

  have hper : ∀ σ ∈ P.inertiaSubgroupIn ℚ,
      (a σ ^ q = a σ ∧ b σ ^ q = b σ) ∨ (a σ ^ q = b σ ∧ b σ ^ q = a σ) := by
    intro σ hσ
    rcases roots_pair_of_mul_eq (hii σ hσ) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨Units.ext h1, Units.ext h2⟩
    · exact Or.inr ⟨Units.ext h1, Units.ext h2⟩
  have hunif := forall_or_forall_of_forall_or
    (I := P.inertiaSubgroupIn ℚ) (S := fun σ => a σ ^ q = a σ ∧ b σ ^ q = b σ)
    (T := fun σ => a σ ^ q = b σ ∧ b σ ^ q = a σ)
    (fun σ hσ τ hτ hS hT => by
      refine ⟨?_, ?_⟩
      · rw [(hmul σ hσ τ hτ).1, mul_pow, hS.1, hT.1]
      · rw [(hmul σ hσ τ hτ).2, mul_pow, hS.2, hT.2])
    (fun σ hσ hS => by
      refine ⟨?_, ?_⟩
      · rw [hainv σ hσ, inv_pow, hS.1]
      · rw [hbinv σ hσ, inv_pow, hS.2])
    (fun σ hσ τ hτ hS hT => by
      refine ⟨?_, ?_⟩
      · rw [(hmul σ hσ τ hτ).1, mul_pow, hS.1, hT.1, (hmul σ hσ τ hτ).2]
      · rw [(hmul σ hσ τ hτ).2, mul_pow, hS.2, hT.2, (hmul σ hσ τ hτ).1])
    (fun σ hσ hS => by
      refine ⟨?_, ?_⟩
      · rw [hainv σ hσ, inv_pow, hS.1, hbinv σ hσ]
      · rw [hbinv σ hσ, inv_pow, hS.2, hainv σ hσ])
    hper
  have hq1 : q - 1 + 1 = q := Nat.sub_add_cancel hq.one_lt.le
  have hdich : (∀ σ ∈ P.inertiaSubgroupIn ℚ, a σ ^ (q - 1) = 1 ∧ b σ ^ (q - 1) = 1) ∨
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, b σ = a σ ^ q ∧ a σ = b σ ^ q) := by
    rcases hunif with h | h
    · left
      intro σ hσ
      obtain ⟨h1, h2⟩ := h σ hσ
      refine ⟨?_, ?_⟩
      · have h3 : a σ ^ (q - 1) * a σ = 1 * a σ := by rw [← pow_succ, hq1, h1, one_mul]
        exact mul_right_cancel h3
      · have h3 : b σ ^ (q - 1) * b σ = 1 * b σ := by rw [← pow_succ, hq1, h2, one_mul]
        exact mul_right_cancel h3
    · right
      intro σ hσ
      obtain ⟨h1, h2⟩ := h σ hσ
      exact ⟨h1.symm, h2.symm⟩

  have hwild : ∀ σ ∈ P.inertiaSubgroupIn ℚ,
      (∀ z : AlgebraicClosure ℚ, z ≠ 0 → σ z * z⁻¹ - 1 ∈ P.nonunits) → a σ = 1 ∧ b σ = 1 := by
    intro σ hσ hw
    have hρ1 : ρ.ρ σ = 1 := htame σ hσ hw
    have hA1 : A σ = 1 := by
      rw [hA, hρ1, LinearMap.toMatrix_one, ← RingHom.mapMatrix_apply, map_one]
    have ha'1 : a' σ = 1 := by
      have h := hav σ hσ
      rw [hA1, Matrix.one_mulVec] at h
      have h2 : (a' σ - 1) • v = 0 := by rw [sub_smul, one_smul, ← h, sub_self]
      exact sub_eq_zero.mp (eq_zero_of_smul_vec_eq_zero h2 hv0)
    have hb'1 : b' σ = 1 := by
      have h := hdet' σ hσ
      rw [hA1, Matrix.det_one, ha'1, one_mul] at h
      exact h.symm
    obtain ⟨h1, h2, -⟩ := hmatch σ hσ
    exact ⟨Units.ext (by rw [h1, ha'1, Units.val_one]), Units.ext (by rw [h2, hb'1, Units.val_one])⟩
  exact ⟨a, b, hi, hmul, hiii, hdich, hwild⟩

private abbrev w2SplitRing_L (O' : Type) [CommRing O'] [IsDomain O'] : Type :=
  AlgebraicClosure (FractionRing O')

private noncomputable abbrev w2SplitRing_B (O' : Type) [CommRing O'] [IsDomain O'] :
    Subalgebra O' (w2SplitRing_L O') :=
  integralClosure O' (w2SplitRing_L O')

end GaloisRepAdic.MultLabels

theorem solution
    {O' : Type} [CommRing O'] [IsLocalRing O'] (ρ : GaloisRepAdic O')
    {q : ℕ} [Fact q.Prime]
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (htame : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      σ ∈ P.inertiaSubgroupIn ℚ →
        (∀ z : AlgebraicClosure ℚ, z ≠ 0 → σ z * z⁻¹ - 1 ∈ P.nonunits) → ρ.ρ σ = 1)
    {O'' : Type} [CommRing O''] [IsDomain O''] (j : O' →+* O'')
    (hsplit : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∃ α β : O'',
      (LinearMap.charpoly (ρ.ρ σ)).map j = (X - C α) * (X - C β)) :
    ∃ a b : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → O''ˣ,
      (∀ σ ∈ P.inertiaSubgroupIn ℚ,
        (LinearMap.charpoly (ρ.ρ σ)).map j = (X - C ((a σ : O''ˣ) : O'')) * (X - C ((b σ : O''ˣ) : O''))) ∧
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ τ ∈ P.inertiaSubgroupIn ℚ,
        a (σ * τ) = a σ * a τ ∧ b (σ * τ) = b σ * b τ) ∧
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, a σ ^ (q ^ 2 - 1) = 1 ∧ b σ ^ (q ^ 2 - 1) = 1) ∧
      ((∀ σ ∈ P.inertiaSubgroupIn ℚ, a σ ^ (q - 1) = 1 ∧ b σ ^ (q - 1) = 1) ∨
        (∀ σ ∈ P.inertiaSubgroupIn ℚ, b σ = a σ ^ q ∧ a σ = b σ ^ q)) ∧
      (∀ σ ∈ P.inertiaSubgroupIn ℚ,
        (∀ z : AlgebraicClosure ℚ, z ≠ 0 → σ z * z⁻¹ - 1 ∈ P.nonunits) → a σ = 1 ∧ b σ = 1) := by
  exact GaloisRepAdic.MultLabels.exists_inertia_labels_mul_dichotomy_of_forall_wild_apply_eq_one ρ P hP htame j hsplit

end S_GaloisRepAdic_exists_inertia_labels_mul_dichotomy_of_forall_wild_apply_eq_one
end P2MW
export P2MW.S_GaloisRepAdic_exists_inertia_labels_mul_dichotomy_of_forall_wild_apply_eq_one (solution)
