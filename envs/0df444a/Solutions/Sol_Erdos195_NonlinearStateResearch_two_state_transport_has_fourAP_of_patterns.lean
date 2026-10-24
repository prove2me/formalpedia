-- Prove2me | solution 1 for Erdos195.NonlinearStateResearch.two_state_transport_has_fourAP_of_patterns
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T09:58:18.93367+00:00
-- url     : https://prove2.me/submissions/37a727ad-b97d-4378-85c9-1569720021d2

import Mathlib
import Definitions.Def_Erdos195_defs
import Definitions.Def_Erdos195_TwoStateBinary_Model
import Theorems.Thm_Erdos195_TriangularWeightResearch_triangular_transport_has_fourAP_of_patterns

namespace Erdos195.NonlinearStateResearch

@[simp] private theorem stateValue_zero (a : Bool → ℤ) (δ₀ δ₁ : Bool → Bool) (s : Bool) :
    stateValue a δ₀ δ₁ s 0 = 0 := by
  rw [stateValue]
  simp

@[simp] private theorem stateValue_even (a : Bool → ℤ) (δ₀ δ₁ : Bool → Bool)
    (s : Bool) (n : ℕ) :
    stateValue a δ₀ δ₁ s (2 * n) = 2 * stateValue a δ₀ δ₁ (δ₀ s) n := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [stateValue]
    simp [hn]

@[simp] private theorem stateValue_odd (a : Bool → ℤ) (δ₀ δ₁ : Bool → Bool)
    (s : Bool) (n : ℕ) :
    stateValue a δ₀ δ₁ s (2 * n + 1) =
      2 * stateValue a δ₀ δ₁ (δ₁ s) n + a s := by
  rw [stateValue]
  simp [show (2 * n + 1) / 2 = n by omega]

@[simp] private theorem stateValue_one (a : Bool → ℤ) (δ₀ δ₁ : Bool → Bool) (s : Bool) :
    stateValue a δ₀ δ₁ s 1 = a s := by
  simpa using stateValue_odd a δ₀ δ₁ s 0

private theorem head_odd_of_surjective (a : Bool → ℤ) (δ₀ δ₁ : Bool → Bool) (s : Bool)
    (hs : Function.Surjective (stateValue a δ₀ δ₁ s)) : Odd (a s) := by
  obtain ⟨n, hn⟩ := hs 1
  by_cases he : n % 2 = 0
  · have en : n = 2 * (n / 2) := by omega
    rw [en, stateValue_even] at hn
    omega
  · have en : n = 2 * (n / 2) + 1 := by omega
    rw [en, stateValue_odd] at hn
    refine ⟨-stateValue a δ₀ δ₁ (δ₁ s) (n / 2), ?_⟩
    omega

/-- Onto coverage passes to BOTH branches, even though their states differ. -/
private theorem children_surjective (a : Bool → ℤ) (δ₀ δ₁ : Bool → Bool) (s : Bool)
    (hs : Function.Surjective (stateValue a δ₀ δ₁ s)) :
    Function.Surjective (stateValue a δ₀ δ₁ (δ₀ s)) ∧
      Function.Surjective (stateValue a δ₀ δ₁ (δ₁ s)) := by
  obtain ⟨r, hr⟩ := head_odd_of_surjective a δ₀ δ₁ s hs
  constructor
  · intro z
    obtain ⟨n, hn⟩ := hs (2 * z)
    by_cases he : n % 2 = 0
    · have en : n = 2 * (n / 2) := by omega
      rw [en, stateValue_even] at hn
      exact ⟨n / 2, by omega⟩
    · have en : n = 2 * (n / 2) + 1 := by omega
      rw [en, stateValue_odd] at hn
      omega
  · intro z
    obtain ⟨n, hn⟩ := hs (2 * z + a s)
    by_cases he : n % 2 = 0
    · have en : n = 2 * (n / 2) := by omega
      rw [en, stateValue_even] at hn
      omega
    · have en : n = 2 * (n / 2) + 1 := by omega
      rw [en, stateValue_odd] at hn
      exact ⟨n / 2, by omega⟩

/-- A fixed odd transition has the genuine missing value -a(s). -/
private theorem odd_fixed_missing (a : Bool → ℤ) (δ₀ δ₁ : Bool → Bool) (s : Bool)
    (ha : Odd (a s)) (hfix : δ₁ s = s) (n : ℕ) :
    stateValue a δ₀ δ₁ s n ≠ -a s := by
  obtain ⟨r, hr⟩ := ha
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hz : n = 0
    · simp only [hz, stateValue_zero] at hn
      omega
    by_cases he : n % 2 = 0
    · have en : n = 2 * (n / 2) := by omega
      rw [en, stateValue_even] at hn
      omega
    · have en : n = 2 * (n / 2) + 1 := by omega
      rw [en, stateValue_odd, hfix] at hn
      exact ih (n / 2) (by omega) (by omega)

private theorem odd_transition_ne_of_surjective (a : Bool → ℤ) (δ₀ δ₁ : Bool → Bool)
    (s : Bool) (hs : Function.Surjective (stateValue a δ₀ δ₁ s)) : δ₁ s ≠ s := by
  intro hfix
  obtain ⟨n, hn⟩ := hs (-a s)
  exact odd_fixed_missing a δ₀ δ₁ s (head_odd_of_surjective a δ₀ δ₁ s hs) hfix n hn

/-- With two states, onto of the initial state forces the other state reachable. -/
private theorem all_states_surjective (a : Bool → ℤ) (δ₀ δ₁ : Bool → Bool)
    (s : Bool) (hs : Function.Surjective (stateValue a δ₀ δ₁ s)) :
    ∀ t, Function.Surjective (stateValue a δ₀ δ₁ t) := by
  have hne := odd_transition_ne_of_surjective a δ₀ δ₁ s hs
  have ho := (children_surjective a δ₀ δ₁ s hs).2
  have hcover : ∀ x y : Bool, x ≠ y → ∀ z : Bool, z = x ∨ z = y := by
    decide
  intro t
  rcases hcover s (δ₁ s) (Ne.symm hne) t with rfl | rfl
  · exact hs
  · exact ho


open TriangularWeightResearch

@[simp] private theorem weight_zero (a : ℕ → ℤ) : weightValue a 0 = 0 := by
  rw [weightValue]
  simp

private theorem weight_even (a : ℕ → ℤ) (n : ℕ) :
    weightValue a (2*n) = 2 * weightValue (fun j => a (j+1)) n := by
  by_cases hn : n = 0
  · simp only [hn, mul_zero, weight_zero]
  · rw [weightValue]
    simp [hn]

private theorem weight_odd (a : ℕ → ℤ) (n : ℕ) :
    weightValue a (2*n+1) = 2 * weightValue (fun j => a (j+1)) n + a 0 := by
  rw [weightValue]
  simp [show (2*n+1)/2=n by omega]

private theorem progression_of_equations (f : ℕ ≃ ℤ) (i j k l : ℕ)
    (hij : i < j) (hjk : j < k) (hkl : k < l)
    (h1 : f i + f k = 2 * f j) (h2 : f j + f l = 2 * f k) :
    HasMonotoneAP f 4 := by
  have e2 : f i + 2 * (f j - f i) = f k := by linarith
  have e3 : f i + 3 * (f j - f i) = f l := by linarith
  refine ⟨[i,j,k,l], ⟨f i, f j-f i, Or.inl ?_⟩, ?_⟩
  · simpa [List.range_succ] using And.intro e2.symm e3.symm
  · simpa [List.pairwise_cons] using
      And.intro (And.intro hij (And.intro (lt_trans hij hjk)
        (lt_trans hij (lt_trans hjk hkl))))
        (And.intro (And.intro hjk (lt_trans hjk hkl)) hkl)


/-- Equal successors reduce exactly to the already checked global-weight family. -/
private theorem stateValue_common_successor (a : Bool → ℤ) (δ₀ δ₁ : Bool → Bool)
    (heq : ∀ t, δ₁ t = δ₀ t) (s : Bool) (n : ℕ) :
    stateValue a δ₀ δ₁ s n = weightValue (fun j => a ((δ₀^[j]) s)) n := by
  induction n using Nat.strong_induction_on generalizing s with
  | h n ih =>
    by_cases hz : n = 0
    · simp only [hz, stateValue_zero, weight_zero]
    have hsmall : n / 2 < n := by omega
    have hshift : (fun j => a ((δ₀^[j]) (δ₀ s))) =
        (fun j => a ((δ₀^[j + 1]) s)) := by
      funext j
      rw [Function.iterate_succ_apply]
    by_cases he : n % 2 = 0
    · have en : n = 2 * (n / 2) := by omega
      calc
        stateValue a δ₀ δ₁ s n = 2 * stateValue a δ₀ δ₁ (δ₀ s) (n / 2) := by
          conv_lhs => rw [en, stateValue_even]
        _ = 2 * weightValue (fun j => a ((δ₀^[j + 1]) s)) (n / 2) := by
          rw [ih (n / 2) hsmall, hshift]
        _ = weightValue (fun j => a ((δ₀^[j]) s)) n := by
          conv_rhs => rw [en, weight_even]
    · have en : n = 2 * (n / 2) + 1 := by omega
      calc
        stateValue a δ₀ δ₁ s n =
            2 * stateValue a δ₀ δ₁ (δ₀ s) (n / 2) + a s := by
          conv_lhs => rw [en, stateValue_odd, heq]
        _ = 2 * weightValue (fun j => a ((δ₀^[j + 1]) s)) (n / 2) + a s := by
          rw [ih (n / 2) hsmall, hshift]
        _ = weightValue (fun j => a ((δ₀^[j]) s)) n := by
          conv_rhs => rw [en, weight_odd]
          rfl

private theorem stateValue_constant (a : Bool → ℤ) (δ₀ δ₁ : Bool → Bool)
    (c : ℤ) (ha : ∀ t, a t = c) (s : Bool) (n : ℕ) :
    stateValue a δ₀ δ₁ s n = c * (n : ℤ) := by
  induction n using Nat.strong_induction_on generalizing s with
  | h n ih =>
    by_cases hz : n = 0
    · simp [hz]
    have hsmall : n / 2 < n := by omega
    by_cases he : n % 2 = 0
    · have en : n = 2 * (n / 2) := by omega
      calc
        stateValue a δ₀ δ₁ s n = 2 * stateValue a δ₀ δ₁ (δ₀ s) (n / 2) := by
          conv_lhs => rw [en, stateValue_even]
        _ = 2 * (c * (n / 2 : ℕ)) := by rw [ih (n / 2) hsmall]
        _ = c * (n : ℤ) := by
          have hn : (n : ℤ) = 2 * (n / 2 : ℕ) := by exact_mod_cast en
          rw [hn]
          ring
    · have en : n = 2 * (n / 2) + 1 := by omega
      calc
        stateValue a δ₀ δ₁ s n =
            2 * stateValue a δ₀ δ₁ (δ₁ s) (n / 2) + a s := by
          conv_lhs => rw [en, stateValue_odd]
        _ = 2 * (c * (n / 2 : ℕ)) + c := by rw [ih (n / 2) hsmall, ha]
        _ = c * (n : ℤ) := by
          have hn : (n : ℤ) = 2 * (n / 2 : ℕ) + 1 := by exact_mod_cast en
          rw [hn]
          ring

private theorem coefficients_distinct_of_surjective (a : Bool → ℤ) (δ₀ δ₁ : Bool → Bool)
    (s : Bool) (hs : Function.Surjective (stateValue a δ₀ δ₁ s)) : a false ≠ a true := by
  intro heq
  have ha : ∀ t, a t = a false := by intro t; cases t <;> simp_all
  rcases le_total 0 (a false) with hp | hn
  · obtain ⟨n, hv⟩ := hs (-1)
    rw [stateValue_constant a δ₀ δ₁ (a false) ha] at hv
    have := mul_nonneg hp (Nat.cast_nonneg (α := ℤ) n)
    omega
  · obtain ⟨n, hv⟩ := hs 1
    rw [stateValue_constant a δ₀ δ₁ (a false) ha] at hv
    have := mul_nonpos_of_nonpos_of_nonneg hn (Nat.cast_nonneg (α := ℤ) n)
    omega

/-- A state with a fixed even transition forces an AP.  The scale allows
this state to lie one (or more) zero-branches below the initial state. -/
private theorem fixed_even_transport_has_fourAP (p : ℕ ≃ ℕ)
    (hTail : ∀ k m : ℕ, 4 ≤ m →
      p.symm (2^k*0) < p.symm (2^k*1) ∧
      p.symm (2^k*1) < p.symm (2^k*2) ∧
      p.symm (2^k*2) < p.symm (2^k*m))
    (a : Bool → ℤ) (δ₀ δ₁ : Bool → Bool)
    (s : Bool) (hs : Function.Surjective (stateValue a δ₀ δ₁ s))
    (heven : δ₀ s = s) (k : ℕ) (c : ℤ) (f : ℕ ≃ ℤ)
    (hv : ∀ n, f (p.symm (2^k*n)) =
      c * stateValue a δ₀ δ₁ s n) : HasMonotoneAP f 4 := by
  have hodd := odd_transition_ne_of_surjective a δ₀ δ₁ s hs
  have hneq := coefficients_distinct_of_surjective a δ₀ δ₁ s hs
  have hc : a (δ₁ s) ≠ a s := by
    cases s <;> cases ht : δ₁ _ <;> simp_all
    omega
  have ha : a s ≠ 0 := by
    obtain ⟨r, hr⟩ := head_odd_of_surjective a δ₀ δ₁ s hs
    omega
  obtain ⟨n, hn⟩ := hs (3 * a s)
  have h0 : n ≠ 0 := by intro h; simp only [h, stateValue_zero] at hn; omega
  have h1 : n ≠ 1 := by intro h; simp only [h, stateValue_one] at hn; omega
  have h2 : n ≠ 2 := by
    intro h
    have he := stateValue_even a δ₀ δ₁ s 1
    simp only [heven, stateValue_one] at he
    rw [h, he] at hn
    omega
  have h3 : n ≠ 3 := by
    intro h
    have he := stateValue_odd a δ₀ δ₁ s 1
    simp only [stateValue_one] at he
    rw [h, he] at hn
    omega
  apply progression_of_equations f
    (p.symm (2^k*0))
    (p.symm (2^k*1))
    (p.symm (2^k*2))
    (p.symm (2^k*n))
    (hTail k n (by omega)).1
    (hTail k n (by omega)).2.1
    (hTail k n (by omega)).2.2
  · have he := stateValue_even a δ₀ δ₁ s 1
    simp only [heven, stateValue_one] at he
    simp only [hv, stateValue_zero, stateValue_one, he]
    ring
  · have he := stateValue_even a δ₀ δ₁ s 1
    simp only [heven, stateValue_one] at he
    simp only [hv, stateValue_one, hn, he]
    ring


/-- Every bijective two-state binary-prefix transport under the stated dyadic order patterns
contains a monotone four-term arithmetic progression.  The coefficients,
initial state, and both transition maps are completely unrestricted. -/
private theorem two_state_obstruction_core
    (p : ℕ ≃ ℕ) (hTail : ∀ k m : ℕ, 4 ≤ m →
      p.symm (2^k*0) < p.symm (2^k*1) ∧
      p.symm (2^k*1) < p.symm (2^k*2) ∧
      p.symm (2^k*2) < p.symm (2^k*m))
    (hPattern : ∀ k n : ℕ, 2 ≤ n →
      p.symm (2^k*3) < p.symm (2^k*2) ∧
      p.symm (2^k*2) < p.symm (2^k*(2*n+1)) ∧
      p.symm (2^k*(2*n+1)) < p.symm (2^k*(2*n)))
    (a : Bool → ℤ) (δ₀ δ₁ : Bool → Bool) (s : Bool)
    (f : ℕ ≃ ℤ)
    (hval : ∀ i, f i = stateValue a δ₀ δ₁ s (p i)) :
    HasMonotoneAP f 4 := by
  have hs : Function.Surjective (stateValue a δ₀ δ₁ s) := by
    intro z
    obtain ⟨i, hi⟩ := f.surjective z
    exact ⟨p i, (hval i).symm.trans hi⟩
  have hall := all_states_surjective a δ₀ δ₁ s hs
  have hv (n : ℕ) : f (p.symm n) = stateValue a δ₀ δ₁ s n := by
    simpa using hval (p.symm n)
  by_cases hfix : δ₀ s = s
  · apply fixed_even_transport_has_fourAP p hTail a δ₀ δ₁ s hs hfix 0 1 f
    intro n
    simpa using hv n
  by_cases hnext : δ₀ (δ₀ s) = δ₀ s
  · apply fixed_even_transport_has_fourAP p hTail a δ₀ δ₁ (δ₀ s) (hall _) hnext 1 2 f
    intro n
    simpa using (hv (2*n)).trans (stateValue_even a δ₀ δ₁ s n)
  have hcover : ∀ x y : Bool, x ≠ y → ∀ z : Bool, z = x ∨ z = y := by decide
  have hnone (t : Bool) : δ₀ t ≠ t := by
    rcases hcover s (δ₀ s) (Ne.symm hfix) t with rfl | rfl
    · exact hfix
    · exact hnext
  have hother : ∀ x y z : Bool, y ≠ x → z ≠ x → y = z := by decide
  have heq (t : Bool) : δ₁ t = δ₀ t :=
    hother t (δ₁ t) (δ₀ t)
      (odd_transition_ne_of_surjective a δ₀ δ₁ t (hall t)) (hnone t)
  refine triangular_transport_has_fourAP_of_patterns p
    (fun j => a ((δ₀^[j]) s)) f ?_ hPattern
  intro i
  exact (hval i).trans (stateValue_common_successor a δ₀ δ₁ heq s _)

end Erdos195.NonlinearStateResearch

open Erdos195 Erdos195.NonlinearStateResearch

theorem solution
    (p : ℕ ≃ ℕ) (a : Bool → ℤ) (δ₀ δ₁ : Bool → Bool) (s : Bool)
    (f : ℕ ≃ ℤ)
    (hval : ∀ i, f i = stateValue a δ₀ δ₁ s (p i))
    (hTail : ∀ k m : ℕ, 4 ≤ m →
      p.symm (2^k*0) < p.symm (2^k*1) ∧
      p.symm (2^k*1) < p.symm (2^k*2) ∧
      p.symm (2^k*2) < p.symm (2^k*m))
    (hPattern : ∀ k n : ℕ, 2 ≤ n →
      p.symm (2^k*3) < p.symm (2^k*2) ∧
      p.symm (2^k*2) < p.symm (2^k*(2*n+1)) ∧
      p.symm (2^k*(2*n+1)) < p.symm (2^k*(2*n))) : HasMonotoneAP f 4 :=
  two_state_obstruction_core p hTail hPattern a δ₀ δ₁ s f hval
