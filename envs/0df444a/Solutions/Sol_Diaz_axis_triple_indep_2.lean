-- Prove2me | solution 2 for Diaz.axis_triple_indep
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T09:20:58.474162+00:00
-- url     : https://prove2.me/submissions/ef53fea1-55db-46d1-ba3e-1b645aad5885

/-
`Diaz.axis_triple_indep`, routed through the published nodes it uses:
`Diaz.transcendental_of_candidate` (Hermite–Lindemann, contrapositive) and
`Diaz.not_on_axes` over `Q̄`, which is what "a candidate lies on neither axis"
amounts to once the candidate is known transcendental over the algebraic
numbers.  The rest is the case analysis on `τ` real / purely imaginary.
-/
import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation
import Theorems.Thm_Diaz_transcendental_of_candidate
import Theorems.Thm_Diaz_not_on_axes

open ComplexConjugate
open Diaz

private theorem gr_hmem (z : ℂ) : IsAlgebraic ℚ z ↔ z ∈ Qbar := by
  rw [Qbar, IntermediateField.mem_toSubfield, mem_algebraicClosure_iff]

private theorem gr_conjalg {z : ℂ} (h : IsAlgebraic ℚ z) : IsAlgebraic ℚ (conj z) :=
  h.algHom (((starRingEnd ℂ) : ℂ →+* ℂ).toRatAlgHom)

open Diaz in
theorem solution {u τ : ℂ}
    (hu0 : u ≠ 0) (hexpu : IsAlgebraic ℚ (Complex.exp u))
    (hρ : IsAlgebraic ℚ (u * conj u))
    (hax : conj τ = τ ∨ conj τ = -τ)
    (hq : IsAlgebraic ℚ ((u + τ) * conj (u + τ)))
    (hne : (u + τ) * conj (u + τ) ≠ u * conj u)
    {a b c : ℚ} (hrel : (a : ℂ) * u + (b : ℂ) * conj u + (c : ℂ) * τ = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have hTu : Transcendental (↥Qbar) u :=
    fun hcon => Diaz.transcendental_of_candidate hu0 hexpu (hcon.restrictScalars ℚ)
  obtain ⟨hax1, hax2⟩ := Diaz.not_on_axes (K := Qbar) hTu ((gr_hmem _).mp hρ)
  have hcu0 : conj u ≠ 0 := by simpa using hu0
  have hexpc : IsAlgebraic ℚ (Complex.exp (conj u)) := by
    rw [Complex.exp_conj]; exact gr_conjalg hexpu
  have hTne : u - conj u ≠ 0 := sub_ne_zero.mpr (fun h => hax1 h.symm)
  have hSne : u + conj u ≠ 0 := fun h => hax2 (by linear_combination h)
  have hexpS : IsAlgebraic ℚ (Complex.exp (u + conj u)) := by
    rw [Complex.exp_add]
    exact (gr_hmem _).mpr (Qbar.mul_mem ((gr_hmem _).mp hexpu) ((gr_hmem _).mp hexpc))
  have hexpT : IsAlgebraic ℚ (Complex.exp (u - conj u)) := by
    rw [Complex.exp_sub]
    exact (gr_hmem _).mpr (Qbar.div_mem ((gr_hmem _).mp hexpu) ((gr_hmem _).mp hexpc))
  have hcq : ∀ q : ℚ, conj ((q : ℂ)) = (q : ℂ) := fun q => by simp
  have hconj : (a : ℂ) * conj u + (b : ℂ) * u + (c : ℂ) * conj τ = 0 := by
    have h := congrArg conj hrel
    rw [map_add, map_add, map_mul, map_mul, map_mul, hcq, hcq, hcq, Complex.conj_conj,
      map_zero] at h
    exact h
  have hratmem : ∀ q : ℚ, ((q : ℂ)) ∈ Qbar := fun q => by
    simpa using Qbar.ratCast_mem q
  rcases hax with hA | hB
  · -- τ real
    have hab : (a : ℂ) = (b : ℂ) := by
      have hz : ((a : ℂ) - (b : ℂ)) * (u - conj u) = 0 := by
        rw [hA] at hconj; linear_combination hrel - hconj
      rcases mul_eq_zero.mp hz with h | h
      · linear_combination h
      · exact absurd h hTne
    have habq : a = b := by exact_mod_cast hab
    have hrel2 : (a : ℂ) * (u + conj u) + (c : ℂ) * τ = 0 := by
      linear_combination hrel + (conj u) * hab
    by_cases hc0 : c = 0
    · have hz : (a : ℂ) * (u + conj u) = 0 := by
        rw [hc0] at hrel2; simpa using hrel2
      have ha0 : (a : ℂ) = 0 := by
        rcases mul_eq_zero.mp hz with h | h
        · exact h
        · exact absurd h hSne
      have haq : a = 0 := by exact_mod_cast ha0
      exact ⟨haq, habq.symm.trans haq, hc0⟩
    · exfalso
      have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc0
      set r : ℚ := -a / c with hrdef
      have hrC : (r : ℂ) = -(a : ℂ) / (c : ℂ) := by rw [hrdef]; push_cast; ring
      have hτeq : τ = (r : ℂ) * (u + conj u) := by
        rw [hrC, div_mul_eq_mul_div, eq_div_iff hcC]
        linear_combination hrel2
      have hqq : (u + τ) * conj (u + τ) - u * conj u
          = ((r : ℂ) * (1 + (r : ℂ))) * (u + conj u) ^ 2 := by
        rw [map_add, hA, hτeq]; ring
      by_cases hrm : (r : ℂ) * (1 + (r : ℂ)) = 0
      · exact hne (by rw [hrm] at hqq; linear_combination hqq)
      · refine Diaz.transcendental_of_candidate hSne hexpS
          (IsAlgebraic.of_pow (n := 2) (by norm_num) ?_)
        have e : (u + conj u) ^ 2
            = ((u + τ) * conj (u + τ) - u * conj u) / ((r : ℂ) * (1 + (r : ℂ))) := by
          rw [eq_div_iff hrm, hqq]; ring
        rw [e]
        exact (gr_hmem _).mpr (Qbar.div_mem
          (Qbar.sub_mem ((gr_hmem _).mp hq) ((gr_hmem _).mp hρ))
          (Qbar.mul_mem (hratmem r) (Qbar.add_mem Qbar.one_mem (hratmem r))))
  · -- τ purely imaginary
    have hab : (a : ℂ) + (b : ℂ) = 0 := by
      have hz : ((a : ℂ) + (b : ℂ)) * (u + conj u) = 0 := by
        rw [hB] at hconj; linear_combination hrel + hconj
      rcases mul_eq_zero.mp hz with h | h
      · exact h
      · exact absurd h hSne
    have habq : b = -a := by
      have hb : (b : ℂ) = -(a : ℂ) := by linear_combination hab
      exact_mod_cast hb
    have hrel2 : (a : ℂ) * (u - conj u) + (c : ℂ) * τ = 0 := by
      linear_combination hrel - (conj u) * hab
    by_cases hc0 : c = 0
    · have hz : (a : ℂ) * (u - conj u) = 0 := by
        rw [hc0] at hrel2; simpa using hrel2
      have ha0 : (a : ℂ) = 0 := by
        rcases mul_eq_zero.mp hz with h | h
        · exact h
        · exact absurd h hTne
      have haq : a = 0 := by exact_mod_cast ha0
      exact ⟨haq, by rw [habq, haq]; ring, hc0⟩
    · exfalso
      have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc0
      set r : ℚ := -a / c with hrdef
      have hrC : (r : ℂ) = -(a : ℂ) / (c : ℂ) := by rw [hrdef]; push_cast; ring
      have hτeq : τ = (r : ℂ) * (u - conj u) := by
        rw [hrC, div_mul_eq_mul_div, eq_div_iff hcC]
        linear_combination hrel2
      have hqq : (u + τ) * conj (u + τ) - u * conj u
          = (-((r : ℂ) * (1 + (r : ℂ)))) * (u - conj u) ^ 2 := by
        rw [map_add, hB, hτeq]; ring
      by_cases hrm : (r : ℂ) * (1 + (r : ℂ)) = 0
      · exact hne (by rw [hrm] at hqq; linear_combination hqq)
      · refine Diaz.transcendental_of_candidate hTne hexpT
          (IsAlgebraic.of_pow (n := 2) (by norm_num) ?_)
        have hrm' : (-((r : ℂ) * (1 + (r : ℂ)))) ≠ 0 := neg_ne_zero.mpr hrm
        have e : (u - conj u) ^ 2
            = ((u + τ) * conj (u + τ) - u * conj u) / (-((r : ℂ) * (1 + (r : ℂ)))) := by
          rw [eq_div_iff hrm', hqq]; ring
        rw [e]
        exact (gr_hmem _).mpr (Qbar.div_mem
          (Qbar.sub_mem ((gr_hmem _).mp hq) ((gr_hmem _).mp hρ))
          (Qbar.neg_mem (Qbar.mul_mem (hratmem r) (Qbar.add_mem Qbar.one_mem (hratmem r)))))
