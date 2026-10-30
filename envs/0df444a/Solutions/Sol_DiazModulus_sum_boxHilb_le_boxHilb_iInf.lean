-- Prove2me | solution 1 for DiazModulus.sum_boxHilb_le_boxHilb_iInf
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-29T08:09:35.550661+00:00
-- url     : https://prove2.me/submissions/14b554e8-0b45-40e2-8806-0e7c37300638

import Definitions.Def_DiazHilbertBox
import Theorems.Thm_DiazModulus_card_le_boxHilb_of_linearIndependent

open Complex ComplexConjugate

/-! # Separated components: `Σ_i h_{I_i}(T) ≤ h_{∩ I_i}(T + C)` (DALAG Ex. 8.5a)

For each `i`, lift a basis of the image of `F T` in `S ⧸ I_i` (`Module.finBasis`) to elements
`e_{i,k} ∈ F T`: there are `h_{I_i}(T)` of them and they are independent modulo `I_i`. The
products `e_{i,k} P_i` lie in `F (T + C)` (`hFmul`). They are independent modulo `⋂ I_j`: if
`Σ g_{i,k} e_{i,k} P_i ∈ ⋂ I_j`, fix `j`; the terms with `i ≠ j` lie in `I_j` because
`P_i ∈ I_j`, so `(Σ_k g_{j,k} e_{j,k}) P_j ∈ I_j`, hence `Σ_k g_{j,k} e_{j,k} ∈ I_j` by the
regularity of `P_j` modulo `I_j`, and every `g_{j,k} = 0`. The family is indexed by
`Σ i, Fin (h_{I_i}(T))`, of cardinality `Σ_i h_{I_i}(T)`, and
`card_le_boxHilb_of_linearIndependent` (F3) bounds that cardinality by `h_{⋂ I_i}(T + C)`. -/

namespace C11_C1
open DiazModulus

/-- `boxHilb F I T` elements of `F T`, independent modulo `I`. -/
theorem exists_family {K S B : Type*} [Field K] [CommRing S] [Algebra K S]
    (F : (B → ℕ) → Submodule K S) (hFfin : ∀ Tₑ, FiniteDimensional K ↥(F Tₑ))
    (I : Ideal S) (T : B → ℕ) :
    ∃ e : Fin (boxHilb F I T) → S, (∀ k, e k ∈ F T) ∧
      LinearIndependent K (fun k => Ideal.Quotient.mk I (e k)) := by
  have := hFfin T
  let W := (F T).map (Ideal.Quotient.mkₐ K I).toLinearMap
  let b : Module.Basis (Fin (boxHilb F I T)) K W := Module.finBasis K W
  have hmem : ∀ k, ∃ s ∈ F T, (Ideal.Quotient.mkₐ K I).toLinearMap s = (b k : S ⧸ I) :=
    fun k => Submodule.mem_map.1 (b k).2
  choose e he hbe using hmem
  refine ⟨e, he, ?_⟩
  have hli : LinearIndependent K (fun k => (b k : S ⧸ I)) :=
    b.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  convert hli using 1
  funext k
  rw [← hbe k]
  rfl

end C11_C1

open DiazModulus C11_C1 in
theorem solution {K S B : Type*} [Field K] [CommRing S] [Algebra K S] (F : (B → ℕ) → Submodule K S)
    (hFmul : ∀ {Tₑ Uₑ : B → ℕ} {aₑ bₑ : S}, aₑ ∈ F Tₑ → bₑ ∈ F Uₑ → aₑ * bₑ ∈ F (Tₑ + Uₑ))
    (hFfin : ∀ Tₑ, FiniteDimensional K ↥(F Tₑ)) {ι : Type*} [Fintype ι] (I : ι → Ideal S) (P : ι → S) (C T : B → ℕ)
    (hPC : ∀ i, P i ∈ F C) (hPI : ∀ i j, i ≠ j → P i ∈ I j)
    (hPreg : ∀ i (a : S), a * P i ∈ I i → a ∈ I i) :
    ∑ i, boxHilb F (I i) T ≤ boxHilb F (⨅ i, I i) (T + C) := by
  classical
  choose e he hli using fun i => exists_family F hFfin (I i) T
  let E : (Σ i, Fin (boxHilb F (I i) T)) → S := fun x => e x.1 x.2 * P x.1
  have hE : ∀ x, E x ∈ F (T + C) := fun x => hFmul (he x.1 x.2) (hPC x.1)
  have hind : LinearIndependent K (fun x => Ideal.Quotient.mk (⨅ i, I i) (E x)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg x
    obtain ⟨j, k⟩ := x
    have hs : (∑ x, g x • E x) ∈ ⨅ i, I i := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.mkₐ_eq_mk K, map_sum]
      simp_rw [map_smul, Ideal.Quotient.mkₐ_eq_mk]
      exact hg
    have hsj : (∑ x, g x • E x) ∈ I j := (Submodule.mem_iInf _).1 hs j
    set a : ι → S := fun i => ∑ k, g ⟨i, k⟩ • e i k with ha
    have hsum : (∑ x, g x • E x) = ∑ i, a i * P i := by
      rw [Fintype.sum_sigma]
      simp only [E, ha, Finset.sum_mul, smul_mul_assoc]
    rw [hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ j)] at hsj
    have hrest : (∑ i ∈ Finset.univ.erase j, a i * P i) ∈ I j :=
      Ideal.sum_mem _ fun i hi => Ideal.mul_mem_left _ _ (hPI i j (Finset.ne_of_mem_erase hi))
    have haj : a j ∈ I j := hPreg j _ ((Submodule.add_mem_iff_left _ hrest).1 hsj)
    have h0 : ∑ k, g ⟨j, k⟩ • Ideal.Quotient.mk (I j) (e j k) = 0 := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.mkₐ_eq_mk K, ha, map_sum] at haj
      simp_rw [map_smul, Ideal.Quotient.mkₐ_eq_mk] at haj
      exact haj
    exact Fintype.linearIndependent_iff.1 (hli j) _ h0 k
  calc ∑ i, boxHilb F (I i) T = Fintype.card (Σ i, Fin (boxHilb F (I i) T)) := by
        simp [Fintype.card_sigma]
    _ ≤ boxHilb F (⨅ i, I i) (T + C) :=
        DiazModulus.card_le_boxHilb_of_linearIndependent F hFfin (⨅ i, I i) (T + C) E hE hind
