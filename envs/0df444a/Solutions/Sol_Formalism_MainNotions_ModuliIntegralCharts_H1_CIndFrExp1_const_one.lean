-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1.const_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:41:46.407932+00:00
-- url     : https://prove2.me/submissions/67cf5a87-c954-4b9c-8656-a5bbd0a9498b

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PairEvaluation
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_AevalDiagMonomial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1
open MvPolynomial Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation
variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}
private theorem memIo_lemma {σ : Type} (n : ℕ) (p : MvPolynomial σ S) :
    p ∈ Io S σ ^ n ↔ ∀ x ∈ p.support, n ≤ Finsupp.degree x :=
  mem_pow_idealOfVars_iff n p
private theorem ccmem_lemma_2 {σ : Type} {n : ℕ} {p : MvPolynomial σ S} (hp : p ∈ Io S σ ^ (n + 1)) :
    coeff 0 p = 0 := by
  by_contra hne
  have h := (memIo_lemma (n + 1) p).1 hp 0 (MvPolynomial.mem_support_iff.2 hne)
  simp [Finsupp.degree] at h
private theorem ccaeval_lemma_3 {σ τ : Type} (g : σ → MvPolynomial τ S) (hg : ∀ i, constantCoeff (g i) = 0)
    (p : MvPolynomial σ S) : constantCoeff (aeval g p) = constantCoeff p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp only [aeval_C, algebraMap_eq, constantCoeff_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, aeval_X, constantCoeff_X, hg, mul_zero]
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1
open MvPolynomial Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation
variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1
theorem _root_.solution {P : MvPolynomial (Fin 2 × Fin d) S} {m : ℕ}
    (fF : Fin d → MvPolynomial (Fin 3 × Fin d) S)
    (hF : ∀ i, fF i - (xs S d 0 i + xs S d 1 i) ∈ Io S (Fin 3 × Fin d) ^ 2)
    (hph1 : ev2 P fF (xs S d 2) - ev2 P (xs S d 0) (xs S d 2) * ev2 P (xs S d 1) (xs S d 2) ∈
      Io S (Fin 3 × Fin d) ^ (m + 1))
    (hu : IsUnit (coeff 0 P)) : P - 1 ∈ Io S (Fin 2 × Fin d) ^ 1 := by
  have hx : ∀ (k : Fin 3) (i : Fin d), constantCoeff (xs S d k i) = 0 := by
    intro k i
    simp [xs]
  have hfF : ∀ i, constantCoeff (fF i) = 0 := by
    intro i
    have h2 : coeff 0 (fF i - (xs S d 0 i + xs S d 1 i)) = 0 := ccmem_lemma_2 (n := 1) (hF i)
    rw [coeff_sub, coeff_add] at h2
    have h0 : coeff 0 (xs S d 0 i) = 0 := hx 0 i
    have h1 : coeff 0 (xs S d 1 i) = 0 := hx 1 i
    rw [h0, h1, add_zero, sub_zero] at h2
    exact h2
  have key : ∀ u v : Fin d → MvPolynomial (Fin 3 × Fin d) S, (∀ i, constantCoeff (u i) = 0) →
      (∀ i, constantCoeff (v i) = 0) → constantCoeff (ev2 P u v) = coeff 0 P := by
    intro u v hu hv
    rw [ev2, ccaeval_lemma_3]
    · rfl
    · rintro ⟨k, i⟩
      fin_cases k
      · simpa using hu i
      · simpa using hv i
  have h1 : constantCoeff (ev2 P fF (xs S d 2) - ev2 P (xs S d 0) (xs S d 2) * ev2 P (xs S d 1) (xs S d 2)) = 0 :=
    ccmem_lemma_2 hph1
  rw [map_sub, map_mul, key _ _ hfF (hx 2), key _ _ (hx 0) (hx 2), key _ _ (hx 1) (hx 2)] at h1
  have h2 : coeff 0 P * (1 - coeff 0 P) = 0 := by linear_combination h1
  obtain ⟨v, hv⟩ := hu.exists_left_inv
  have h3 : 1 - coeff 0 P = 0 := by
    calc 1 - coeff 0 P = (v * coeff 0 P) * (1 - coeff 0 P) := by rw [hv, one_mul]
      _ = v * (coeff 0 P * (1 - coeff 0 P)) := by ring
      _ = 0 := by rw [h2, mul_zero]
  rw [memIo_lemma]
  intro x hx
  by_contra hlt
  have h0 : Finsupp.degree x = 0 := by omega
  have hs : ∑ j ∈ x.support, x j = 0 := h0
  have hx0 : x = 0 := by
    ext i
    by_contra hi
    exact hi ((Finset.sum_eq_zero_iff.1 hs) i (Finsupp.mem_support_iff.2 hi))
  subst hx0
  apply MvPolynomial.mem_support_iff.1 hx
  rw [coeff_sub, coeff_zero_one]
  linear_combination -h3
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1
