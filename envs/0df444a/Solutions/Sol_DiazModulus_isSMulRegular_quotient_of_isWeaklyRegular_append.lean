-- Prove2me | solution 1 for DiazModulus.isSMulRegular_quotient_of_isWeaklyRegular_append
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-29T08:19:23.828983+00:00
-- url     : https://prove2.me/submissions/ad366030-b15d-46d2-a421-74b1f378c99f

import Mathlib

open Complex ComplexConjugate

/-! # Each member of a regular chain is regular modulo its predecessors

Let `ps₀ ++ [P 0, …, P (r-1)]` be a weakly regular sequence on `S`. Then for every `k < r` the
element `P k` is regular on `S ⧸ ((ps₀) + (P j)_{j<k})`. This is the definition of weak regularity
read at the index `|ps₀| + k`: the element there is `P k`, and the first `|ps₀| + k` terms are
`ps₀ ++ [P 0, …, P (k-1)]` (`List.take_length_add_append`), whose ideal is
`(ps₀) ⊔ span (P '' {j | j < k})` (`Ideal.ofList_append`, plus `x ∈ (ofFn P).take k ↔ x ∈ P '' {j < k}`).
Mathlib phrases the quotient as `S ⧸ (I • ⊤)`, and `I • ⊤ = I` for an ideal (`Ideal.mul_top`), so the
two quotient modules agree through `Submodule.quotEquivOfEq`. -/

namespace C11_R4

theorem mem_take_ofFn_iff {S : Type*} {r : ℕ} (P : Fin r → S) (k : Fin r) (x : S) :
    x ∈ (List.ofFn P).take k ↔ x ∈ P '' {j | j < k} := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hik : i < k := by simp at hi; omega
    have hir : i < r := by simp at hi; omega
    refine ⟨⟨i, hir⟩, ?_, ?_⟩
    · exact Fin.lt_def.mpr hik
    · simp
  · rintro ⟨j, hj, rfl⟩
    have hjk : (j : ℕ) < k := Fin.lt_def.mp hj
    refine ⟨j, ?_, ?_⟩
    · simp; omega
    · simp

theorem ofList_take_ofFn {S : Type*} [CommRing S] {r : ℕ} (P : Fin r → S) (k : Fin r) :
    Ideal.ofList ((List.ofFn P).take k) = Ideal.span (P '' {j | j < k}) := by
  unfold Ideal.ofList
  congr 1
  ext x
  exact mem_take_ofFn_iff P k x

end C11_R4

open C11_R4 in
theorem solution {S : Type*} [CommRing S] (ps₀ : List S) {r : ℕ}
    (P : Fin r → S) (h : RingTheory.Sequence.IsWeaklyRegular S (ps₀ ++ List.ofFn P)) (k : Fin r) :
    IsSMulRegular (S ⧸ (Ideal.ofList ps₀ ⊔ Ideal.span (P '' {j | j < k}))) (P k) := by
  have hlen : ps₀.length + (k : ℕ) < (ps₀ ++ List.ofFn P).length := by simp
  have hreg := h.regular_mod_prev (ps₀.length + k) hlen
  have hget : (ps₀ ++ List.ofFn P)[ps₀.length + (k : ℕ)] = P k := by
    rw [List.getElem_append_right (by omega)]
    simp
  have htake : (ps₀ ++ List.ofFn P).take (ps₀.length + k) = ps₀ ++ (List.ofFn P).take k :=
    List.take_length_add_append _
  have hI : (Ideal.ofList ((ps₀ ++ List.ofFn P).take (ps₀.length + k)) • ⊤ : Submodule S S) =
      Ideal.ofList ps₀ ⊔ Ideal.span (P '' {j | j < k}) := by
    rw [htake, Ideal.ofList_append, ofList_take_ofFn, smul_eq_mul, Ideal.mul_top]
  rw [hget] at hreg
  exact (Submodule.quotEquivOfEq _ _ hI).isSMulRegular_congr (P k) |>.mp hreg
