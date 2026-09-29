-- Prove2me | solution 1 for EulerMascheroni.P2.primitive_normalization
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-12T19:44:59.673625+00:00
-- url     : https://prove2.me/submissions/7a97ef5f-60d8-42ac-8c59-cb45bc63208b

import Definitions.Def_eulerMascheroni_p2PrimitiveNormalization
import Mathlib.Tactic
open Filter Topology
open EulerMascheroni.P2

namespace P2NormalizationProof
lemma normalization (n : ℕ) (hQ : 0 < Q n) :
    0 < primitiveQ n ∧ 0 < primitiveScale n ∧
    (primitiveQ n : ℝ) = primitiveScale n * (Q n : ℝ) ∧
    (primitiveP n : ℝ) = primitiveScale n * (P n : ℝ) := by
  have hqr : (0 : ℝ) < (Q n : ℝ) := by exact_mod_cast hQ
  have hd : 0 < primitiveQ n := (P n / Q n).pos
  have hnum : (primitiveP n : ℝ) / (primitiveQ n : ℝ) =
      (P n : ℝ) / (Q n : ℝ) := by
    exact_mod_cast (Rat.num_div_den (P n / Q n))
  refine ⟨hd, div_pos (by exact_mod_cast hd) hqr, ?_, ?_⟩
  · dsimp [primitiveScale]
    field_simp
  · dsimp [primitiveScale]
    have hdr : (primitiveQ n : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    field_simp at hnum ⊢
    nlinarith

lemma integer_normalizations (n : ℕ) (hQ : 0 < Q n)
    (c : ℝ) (hc : c ≠ 0) (p q : ℤ)
    (hp : (p : ℝ) = c * (P n : ℝ)) (hq : (q : ℝ) = c * (Q n : ℝ)) :
    ∃ m : ℤ, m ≠ 0 ∧ p = m * primitiveP n ∧
      q = m * (primitiveQ n : ℤ) ∧ c = (m : ℝ) * primitiveScale n := by
  have hqr : (0 : ℝ) < (Q n : ℝ) := by exact_mod_cast hQ
  have hq0 : q ≠ 0 := by
    intro he
    have := mul_ne_zero hc hqr.ne'
    simp only [he, Int.cast_zero] at hq
    exact this hq.symm
  have he : P n / Q n = (p : ℚ) / (q : ℚ) := by
    have her : (P n : ℝ) / (Q n : ℝ) = (p : ℝ) / (q : ℝ) := by
      rw [hp,hq]
      field_simp
    exact_mod_cast her
  obtain ⟨m,hmP,hmQ⟩ := Rat.num_den_mk hq0 (he.trans (Rat.divInt_eq_div p q).symm)
  have hm0 : m ≠ 0 := by intro he; simp [he] at hmQ; exact hq0 hmQ
  refine ⟨m,hm0,hmP,hmQ,?_⟩
  have hmq : (q : ℝ) = (m : ℝ) * (primitiveQ n : ℝ) := by exact_mod_cast hmQ
  dsimp [primitiveScale]
  rw [hq] at hmq
  rw [← mul_div_assoc]
  exact (eq_div_iff hqr.ne').mpr hmq

end P2NormalizationProof

theorem solution (n : ℕ) (hQ : 0 < Q n) :
    0 < primitiveQ n ∧ 0 < primitiveScale n ∧
    (primitiveQ n : ℝ) = primitiveScale n * (Q n : ℝ) ∧
    (primitiveP n : ℝ) = primitiveScale n * (P n : ℝ) ∧
    (∀ (c : ℝ), c ≠ 0 → ∀ p q : ℤ,
      (p : ℝ) = c * (P n : ℝ) → (q : ℝ) = c * (Q n : ℝ) →
      ∃ m : ℤ, m ≠ 0 ∧ p = m * primitiveP n ∧
        q = m * (primitiveQ n : ℤ) ∧ c = (m : ℝ) * primitiveScale n) := by
  obtain ⟨hd,hc,hq,hp⟩ := P2NormalizationProof.normalization n hQ
  exact ⟨hd,hc,hq,hp,fun c hc p q hp hq =>
    P2NormalizationProof.integer_normalizations n hQ c hc p q hp hq⟩
