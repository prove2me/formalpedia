-- Prove2me | solution 1 for DiazModulus.exists_card_mul_boxHilb_le_translates
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-29T08:06:51.52165+00:00
-- url     : https://prove2.me/submissions/5e058417-3cd3-49be-999c-eb8ee04e9de1

import Definitions.Def_DiazHilbertBox
import Theorems.Thm_DiazModulus_sum_boxHilb_le_boxHilb_iInf
import Theorems.Thm_DiazModulus_boxHilb_map_algEquiv

open Complex ComplexConjugate

/-! # Comaximal translates: `N · h_H(T) ≤ h_{∩ σ_i(H)}(T + C)` (DALAG Lemma 5.10)

Write `J_i = σ_i(H)`. Chinese remainder separators: for `i ≠ j`, comaximality gives
`x + y = 1` with `x ∈ J_i`, `y ∈ J_j`, so `q_{ij} := y ∈ J_j` is `≡ 1` modulo `J_i`; then
`P_i = Π_{j ≠ i} q_{ij}` lies in every `J_j` with `j ≠ i` and is `≡ 1` modulo `J_i`, so
`a P_i ∈ J_i` forces `a ∈ J_i`. Each `P_i` lies in some `F (T_i)` (`hFex`), hence in
`F C` with `C = Σ_i T_i` (`hFmono`). The separated-components bound
`sum_boxHilb_le_boxHilb_iInf` (C1) gives `Σ_i h_{J_i}(T) ≤ h_{∩ J_i}(T + C)`, and each
`h_{J_i}(T) = h_H(T)` because `σ_i` preserves `F T` (`boxHilb_map_algEquiv`, F5). The constant
`C` depends only on the separators, not on `T`. -/

namespace C11_C2
open DiazModulus

/-- Chinese remainder separators for pairwise comaximal ideals. -/
theorem exists_separators {S ι : Type*} [CommRing S] [Fintype ι] [DecidableEq ι]
    (J : ι → Ideal S) (hcop : Pairwise fun i j => J i ⊔ J j = ⊤) :
    ∃ P : ι → S, (∀ i, Ideal.Quotient.mk (J i) (P i) = 1) ∧ ∀ i j, i ≠ j → P i ∈ J j := by
  have hq : ∀ i j, i ≠ j → ∃ q ∈ J j, Ideal.Quotient.mk (J i) q = 1 := by
    intro i j hij
    have h1 : (1 : S) ∈ J i ⊔ J j := by rw [hcop hij]; exact Submodule.mem_top
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 h1
    refine ⟨y, hy, ?_⟩
    rw [show y = 1 - x by rw [← hxy]; ring, map_sub, map_one,
      Ideal.Quotient.eq_zero_iff_mem.2 hx, sub_zero]
  choose! q hqJ hq1 using hq
  refine ⟨fun i => ∏ j ∈ Finset.univ.erase i, q i j, fun i => ?_, fun i j hij => ?_⟩
  · rw [map_prod]
    exact Finset.prod_eq_one fun j hj => hq1 i j (Finset.ne_of_mem_erase hj).symm
  · show (∏ j ∈ Finset.univ.erase i, q i j) ∈ J j
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_erase.2 ⟨hij.symm, Finset.mem_univ j⟩)]
    exact Ideal.mul_mem_right _ _ (hqJ i j hij)

end C11_C2

open DiazModulus C11_C2 in
theorem solution {K S B : Type*} [Field K] [CommRing S] [Algebra K S] (F : (B → ℕ) → Submodule K S)
    (hFmono : Monotone F)
    (hFmul : ∀ {Tₑ Uₑ : B → ℕ} {aₑ bₑ : S}, aₑ ∈ F Tₑ → bₑ ∈ F Uₑ → aₑ * bₑ ∈ F (Tₑ + Uₑ))
    (hFfin : ∀ Tₑ, FiniteDimensional K ↥(F Tₑ))
    (hFex : ∀ sₑ : S, ∃ Tₑ, sₑ ∈ F Tₑ) {ι : Type*} [Fintype ι] (H : Ideal S)
    (σ : ι → S ≃ₐ[K] S) (hσ : ∀ i T, (F T).map (σ i).toLinearMap = F T)
    (hcop : Pairwise fun i j => H.map (σ i) ⊔ H.map (σ j) = ⊤) :
    ∃ C : B → ℕ, ∀ T, Fintype.card ι * boxHilb F H T ≤ boxHilb F (⨅ i, H.map (σ i)) (T + C) := by
  classical
  obtain ⟨P, hP1, hPI⟩ := exists_separators (fun i => H.map (σ i)) hcop
  choose Tₚ hTₚ using fun i => hFex (P i)
  refine ⟨∑ i, Tₚ i, fun T => ?_⟩
  have hPC : ∀ i, P i ∈ F (∑ i, Tₚ i) := fun i =>
    hFmono (Finset.single_le_sum (fun j _ b => Nat.zero_le (Tₚ j b)) (Finset.mem_univ i)) (hTₚ i)
  have hPreg : ∀ i (a : S), a * P i ∈ H.map (σ i) → a ∈ H.map (σ i) := by
    intro i a ha
    rw [← Ideal.Quotient.eq_zero_iff_mem] at ha ⊢
    rw [map_mul, hP1 i, mul_one] at ha
    exact ha
  have hC1 := DiazModulus.sum_boxHilb_le_boxHilb_iInf F hFmul hFfin (fun i => H.map (σ i)) P
    (∑ i, Tₚ i) T hPC hPI hPreg
  have hF5 : ∀ i, boxHilb F (H.map (σ i)) T = boxHilb F H T := fun i =>
    DiazModulus.boxHilb_map_algEquiv F (σ i) H T (hσ i T)
  simp only [hF5, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hC1
  exact hC1
