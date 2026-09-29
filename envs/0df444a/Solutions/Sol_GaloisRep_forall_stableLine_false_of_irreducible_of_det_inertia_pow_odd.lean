-- Prove2me | solution 1 for GaloisRep.forall_stableLine_false_of_irreducible_of_det_inertia_pow_odd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/da0a069d-3c48-5846-98ea-93738698ee81

import Mathlib
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_Matrix_mul_comm_of_forall_map_mulVec_mem_span_of_forall_exists_mulVec_not_mem_span
import Theorems.Thm_GaloisRep_character_pow_sub_one_eq_one_of_mem_inertiaSubgroupIn
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_forall_stableLine_false_of_irreducible_of_det_inertia_pow_odd

set_option autoImplicit false

namespace GaloisRep
p2m_export "GaloisRep" "character_pow_sub_one_eq_one_of_mem_inertiaSubgroupIn"
namespace AbsIrrBridgeAux
p2m_open "GaloisRep"

open Polynomial in

theorem exists_natCast_eq_of_pow_eq_self {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (x : K) (hx : x ^ p = x) : ∃ n : ℕ, (n : K) = x := by
  classical
  have hp : p.Prime := Fact.out
  set f : K[X] := X ^ p - X with hf
  have hf0 : f ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero K hp.one_lt
  have hdeg : f.natDegree = p := FiniteField.X_pow_card_sub_X_natDegree_eq K hp.one_lt
  let ι : ZMod p →+* K := ZMod.castHom (dvd_refl p) K
  have hinj : Function.Injective ι := ZMod.castHom_injective K
  let S : Finset K := Finset.univ.map ⟨ι, hinj⟩
  have hS : S.val ≤ f.roots := by
    rw [Multiset.le_iff_subset S.nodup]
    intro y hy
    obtain ⟨k, -, rfl⟩ := Finset.mem_map.mp (Finset.mem_val.mp hy)
    rw [Polynomial.mem_roots hf0, Polynomial.IsRoot.def, hf, eval_sub, eval_pow, eval_X, sub_eq_zero]
    change ι k ^ p = ι k
    rw [← map_pow, ZMod.pow_card]
  have hcard : f.roots.card ≤ S.val.card := by
    rw [Finset.card_val, Finset.card_map, Finset.card_univ, ZMod.card]
    exact (Polynomial.card_roots' f).trans hdeg.le
  have heq : S.val = f.roots := Multiset.eq_of_le_of_card_le hS hcard
  have hx' : x ∈ f.roots := by
    rw [Polynomial.mem_roots hf0, Polynomial.IsRoot.def, hf, eval_sub, eval_pow, eval_X, sub_eq_zero]
    exact hx
  rw [← heq] at hx'
  obtain ⟨k, -, hk⟩ := Finset.mem_map.mp (Finset.mem_val.mp hx')
  refine ⟨k.val, ?_⟩
  rw [← hk]
  change ((k.val : ℕ) : K) = ι k
  rw [← map_natCast ι, ZMod.natCast_zmod_val]

theorem exists_smul_vecCons_eq_of_mul_add_mul_eq_zero {K : Type*} [Field K] (a b : K)
    (x : Fin 2 → K) (hab : a ≠ 0 ∨ b ≠ 0) (h : a * x 0 + b * x 1 = 0) :
    ∃ c : K, c • ![b, -a] = x := by
  by_cases ha : a = 0
  · have hb : b ≠ 0 := hab.resolve_left (not_not.mpr ha)
    have hx1 : x 1 = 0 := by
      rw [ha, zero_mul, zero_add] at h
      exact (mul_eq_zero.mp h).resolve_left hb
    refine ⟨x 0 / b, ?_⟩
    funext k
    fin_cases k
    · simp [div_mul_cancel₀ _ hb]
    · simp [ha, hx1]
  · refine ⟨-(x 1) / a, ?_⟩
    funext k
    fin_cases k
    · have hx0 : x 0 = -(b * x 1) / a := by
        field_simp
        linear_combination h
      simp [hx0]
      ring
    · simp [ha]

theorem eq_zero_of_det_eq_zero_of_forall_mul_comm {F : Type*} [Field F] {ι : Type*}
    (M : ι → Matrix (Fin 2) (Fin 2) F)
    (hirr : ∀ v : Fin 2 → F, v ≠ 0 → ∃ i, (M i).mulVec v ∉ F ∙ v)
    (X : Matrix (Fin 2) (Fin 2) F) (hX : ∀ i, M i * X = X * M i) (hdet : X.det = 0) : X = 0 := by
  classical
  by_contra hX0
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  obtain ⟨i, hi⟩ := hirr v hv0
  apply hi
  have hw : X.mulVec ((M i).mulVec v) = 0 := by
    rw [Matrix.mulVec_mulVec, ← hX i, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  obtain ⟨r, hr⟩ : ∃ r : Fin 2, X r 0 ≠ 0 ∨ X r 1 ≠ 0 := by
    by_contra h'
    push Not at h'
    apply hX0
    ext r c
    fin_cases c
    · exact (h' r).1
    · exact (h' r).2
  have hrow : ∀ w : Fin 2 → F, X.mulVec w = 0 → X r 0 * w 0 + X r 1 * w 1 = 0 := fun w hw0 => by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congr_fun hw0 r
  obtain ⟨c, hc⟩ := exists_smul_vecCons_eq_of_mul_add_mul_eq_zero _ _ v hr (hrow v hv)
  obtain ⟨d, hd⟩ := exists_smul_vecCons_eq_of_mul_add_mul_eq_zero _ _ _ hr (hrow _ hw)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    exact hv0 hc.symm
  refine Submodule.mem_span_singleton.mpr ⟨d / c, ?_⟩
  calc (d / c) • v = (d / c) • (c • ![X r 1, -X r 0]) := by rw [hc]
    _ = d • ![X r 1, -X r 0] := by rw [smul_smul, div_mul_cancel₀ _ hc0]
    _ = (M i).mulVec v := hd

end GaloisRep.AbsIrrBridgeAux

open GaloisRep.AbsIrrBridgeAux in

theorem solution
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) {F : Type} [Field F] [CharP F p]
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) F)
    (hfin : GaloisFactorsThroughFiniteLevel ρ)
    (hirr : ∀ u : Fin 2 → F, u ≠ 0 →
      ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, Matrix.mulVec (ρ σ).val u ∉ F ∙ u)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p) (m : ℕ) (hm : Odd m)
    (hdet : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ a : ℕ,
      (∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 → σ μ = μ ^ a) → (ρ σ).val.det = (a : F) ^ m)
    {F' : Type} [Field F'] (e : F →+* F') (u : Fin 2 → F') (hu : u ≠ 0) :
    ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, Matrix.mulVec ((ρ σ).val.map e) u ∉ F' ∙ u := by
  classical
  by_contra hcon
  push Not at hcon
  have hp : p.Prime := Fact.out
  haveI : CharP F' p := charP_of_injective_ringHom e.injective p

  have hcomm : ∀ σ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      (ρ σ).val * (ρ τ).val = (ρ τ).val * (ρ σ).val :=
    Matrix.mul_comm_of_forall_map_mulVec_mem_span_of_forall_exists_mulVec_not_mem_span e
      (fun σ => (ρ σ).val) hirr u hu hcon

  choose c hc using fun σ => Submodule.mem_span_singleton.mp (hcon σ)
  have hdetne : ∀ σ, ((ρ σ).val.map e).det ≠ 0 := fun σ => by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero e).mpr (Matrix.GeneralLinearGroup.det_ne_zero (ρ σ))
  have hc0 : ∀ σ, c σ ≠ 0 := fun σ h0 => by
    have h1 : ((ρ σ).val.map e).mulVec u = 0 := by rw [← hc σ, h0, zero_smul]
    exact hu (Matrix.eq_zero_of_mulVec_eq_zero (hdetne σ) h1)
  have hinj : Function.Injective fun x : F' => x • u := smul_left_injective F' hu
  have hmap1 : ((1 : GL (Fin 2) F).val.map e) = 1 := by
    rw [Units.val_one]
    exact Matrix.map_one e (map_zero e) (map_one e)
  have hc1 : c 1 = 1 := by
    apply hinj
    simp only
    rw [hc 1, map_one, hmap1, Matrix.one_mulVec, one_smul]
  have hcmul : ∀ σ τ, c (σ * τ) = c σ * c τ := fun σ τ => by
    apply hinj
    simp only
    rw [hc, map_mul, Units.val_mul, Matrix.map_mul, ← Matrix.mulVec_mulVec, ← hc τ, Matrix.mulVec_smul,
      ← hc σ, smul_smul, mul_comm]
  let η : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* F'ˣ :=
    { toFun := fun σ => Units.mk0 (c σ) (hc0 σ)
      map_one' := Units.ext hc1
      map_mul' := fun σ τ => Units.ext (hcmul σ τ) }
  have hηfin : GaloisFactorsThroughFiniteLevel η := by
    obtain ⟨L, hL, hker⟩ := hfin
    refine ⟨L, hL, fun σ hσ => Units.ext ?_⟩
    show c σ = 1
    apply hinj
    simp only
    rw [hc σ, hker σ hσ, hmap1, Matrix.one_mulVec, one_smul]

  have hscalar : ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∃ n : ℕ,
      (ρ τ).val = (n : F) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    intro τ hτ
    have h1 : η τ ^ (p - 1) = 1 :=
      GaloisRep.character_pow_sub_one_eq_one_of_mem_inertiaSubgroupIn p η hηfin P hP hτ
    have h1' : c τ ^ (p - 1) = 1 := by
      have := congrArg (fun x : F'ˣ => (x : F')) h1
      simpa [η] using this
    have h2 : c τ ^ p = c τ := by
      calc c τ ^ p = c τ ^ (p - 1 + 1) := by rw [Nat.sub_add_cancel hp.one_le]
        _ = c τ := by rw [pow_succ, h1', one_mul]
    obtain ⟨n, hn⟩ := exists_natCast_eq_of_pow_eq_self (c τ) h2
    set X : Matrix (Fin 2) (Fin 2) F := (ρ τ).val - (n : F) • 1 with hXdef
    have hXmap : X.map e = (ρ τ).val.map e - (n : F') • 1 := by
      change e.mapMatrix X = e.mapMatrix (ρ τ).val - (n : F') • 1
      rw [hXdef, map_sub, Nat.cast_smul_eq_nsmul, map_nsmul, map_one, Nat.cast_smul_eq_nsmul]
    have hXu : (X.map e).mulVec u = 0 := by
      rw [hXmap, Matrix.sub_mulVec, ← hc τ, Matrix.smul_mulVec, Matrix.one_mulVec, hn, sub_self]
    have hXdet : X.det = 0 := by
      have h := Matrix.exists_mulVec_eq_zero_iff.mp ⟨u, hu, hXu⟩
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det] at h
      exact (map_eq_zero e).mp h
    have hXcomm : ∀ σ, (ρ σ).val * X = X * (ρ σ).val := fun σ => by
      rw [hXdef, mul_sub, sub_mul, hcomm σ τ, Matrix.mul_smul, Matrix.smul_mul, mul_one, one_mul]
    have hX0 := eq_zero_of_det_eq_zero_of_forall_mul_comm (fun σ => (ρ σ).val) hirr X hXcomm hXdet
    exact ⟨n, sub_eq_zero.mp hX0⟩

  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare (F := ZMod p) (by rw [ZMod.ringChar_zmod_n]; exact hp2)
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact ha IsSquare.zero
  obtain ⟨τ, hτ, hτμ⟩ :=
    ValuationSubring.exists_mem_inertiaSubgroupIn_apply_eq_pow P hp hP (Units.mk0 a ha0)
  have hdet1 : (ρ τ).val.det = ((a.val : ℕ) : F) ^ m := hdet τ hτ a.val hτμ
  obtain ⟨n, hn⟩ := hscalar τ hτ
  have hdet2 : (ρ τ).val.det = (n : F) ^ 2 := by
    rw [hn, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  let ι : ZMod p →+* F := ZMod.castHom (dvd_refl p) F
  have hι : Function.Injective ι := ZMod.castHom_injective F
  have hιa : ι a = ((a.val : ℕ) : F) := by
    rw [← map_natCast ι a.val, ZMod.natCast_zmod_val]
  have key : a ^ m = (n : ZMod p) ^ 2 := by
    apply hι
    rw [map_pow, map_pow, map_natCast, hιa, ← hdet1, hdet2]
  obtain ⟨j, hj⟩ := hm
  apply ha
  refine ⟨(n : ZMod p) * (a ^ j)⁻¹, ?_⟩
  have haj : a ^ j ≠ 0 := pow_ne_zero j ha0
  rw [show (n : ZMod p) * (a ^ j)⁻¹ * ((n : ZMod p) * (a ^ j)⁻¹) = (n : ZMod p) ^ 2 * ((a ^ j)⁻¹) ^ 2 by ring,
    ← key, hj]
  field_simp
  ring

end S_GaloisRep_forall_stableLine_false_of_irreducible_of_det_inertia_pow_odd
end P2MW
export P2MW.S_GaloisRep_forall_stableLine_false_of_irreducible_of_det_inertia_pow_odd (solution)
