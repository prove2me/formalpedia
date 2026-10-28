-- Prove2me | solution 1 for D1Bound5.pellCFPrefixCheck_pairs
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:34:18.191874+00:00
-- url     : https://prove2.me/submissions/1d382f4a-1dfa-43e0-93ce-0dfe899d57df

import Mathlib.Data.Rat.Lemmas
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import Definitions.Def_D1Bound5_PellCFPrefixCheck_Definitions
import Definitions.Def_D1Bound5_PellConvergentCompleteness_Definitions
import Theorems.Thm_D1Bound5_pellCFCheckFrom_sound
import Theorems.Thm_D1Bound5_pellConvergentPair_recurrence

section
namespace D1Bound5

























theorem pellCFAt_succ (d a0 : ℤ) (s : PellCFState) (n : ℕ) :
    pellCFAt d a0 s (n+1) = pellCFStep d a0 (pellCFAt d a0 s n) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simpa only [pellCFAt] using ih (pellCFStep d a0 s)







theorem pellRealTail_succ (x : ℝ) (n : ℕ) :
    pellRealTail x (n+1) = (Int.fract (pellRealTail x n))⁻¹ := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simpa only [pellRealTail] using ih (Int.fract x)⁻¹



private theorem pell_sqrt_interval {d a0 : ℤ}
    (h0 : 0 ≤ a0) (hlo : a0^2 < d) (hhi : d < (a0+1)^2) :
    (a0 : ℝ) < Real.sqrt d ∧ Real.sqrt d < a0+1 := by
  have hd0 : (0 : ℝ) ≤ d := by
    exact_mod_cast (show 0 ≤ d by nlinarith [sq_nonneg a0])
  have hs := Real.sq_sqrt hd0
  have hs0 := Real.sqrt_nonneg (d : ℝ)
  have h0' : (0 : ℝ) ≤ a0 := by exact_mod_cast h0
  have hlo' : (a0 : ℝ)^2 < d := by exact_mod_cast hlo
  have hhi' : (d : ℝ) < ((a0 : ℝ)+1)^2 := by exact_mod_cast hhi
  constructor <;> nlinarith

private theorem pellCFState_floor {d a0 : ℤ} {s : PellCFState}
    (hr : (a0 : ℝ) < Real.sqrt d ∧ Real.sqrt d < a0+1)
    (hg : PellCFStateGood a0 s) :
    ⌊(Real.sqrt (d : ℝ)+s.m)/s.Q⌋ = s.a := by
  have hQ : (0 : ℝ) < s.Q := by exact_mod_cast hg.1
  apply Int.floor_eq_iff.mpr
  constructor
  · apply (le_div_iff₀ hQ).mpr
    have hlo : (s.a : ℝ)*s.Q ≤ a0+s.m := by exact_mod_cast hg.2.1
    linarith only [hlo,hr.1]
  · apply (div_lt_iff₀ hQ).mpr
    have hhi_int : a0+s.m < (s.a+1)*s.Q := hg.2.2
    have hhi_int' : a0+s.m+1 ≤ (s.a+1)*s.Q := by omega
    have hhi : (a0 : ℝ)+s.m+1 ≤ (s.a+1)*s.Q := by
      exact_mod_cast hhi_int'
    linarith only [hhi,hr.2]

private theorem pellCFState_tail {d a0 : ℤ} {s : PellCFState}
    (hr : (a0 : ℝ) < Real.sqrt d ∧ Real.sqrt d < a0+1)
    (hd0 : (0 : ℝ) ≤ d)
    (hg : PellCFStateGood a0 s)
    (hg' : PellCFStateGood a0 (pellCFStep d a0 s))
    (ht : PellCFTransitionGood d a0 s) :
    (Int.fract ((Real.sqrt (d : ℝ)+s.m)/s.Q))⁻¹ =
      (Real.sqrt d+(pellCFStep d a0 s).m)/(pellCFStep d a0 s).Q := by
  have hf := pellCFState_floor hr hg
  have hQ : (s.Q : ℝ) ≠ 0 := by exact_mod_cast hg.1.ne'
  have hQ' : ((pellCFStep d a0 s).Q : ℝ) ≠ 0 := by exact_mod_cast hg'.1.ne'
  have hlo : (s.a : ℝ)*s.Q ≤ a0+s.m := by exact_mod_cast hg.2.1
  have hm : (0 : ℝ) < Real.sqrt d-(pellCFStep d a0 s).m := by
    simp only [pellCFStep]
    push_cast
    linarith only [hlo,hr.1]
  have ht' : (s.Q : ℝ)*(pellCFStep d a0 s).Q =
      d-((pellCFStep d a0 s).m : ℝ)^2 := by exact_mod_cast ht
  have hs := Real.sq_sqrt hd0
  rw [Int.fract,hf]
  have hrewrite : (Real.sqrt (d : ℝ)+s.m)/s.Q-(s.a : ℝ) =
      (Real.sqrt d-(pellCFStep d a0 s).m)/s.Q := by
    simp only [pellCFStep]
    push_cast
    field_simp [hQ]
    <;> ring
  rw [hrewrite,inv_div]
  apply (div_eq_div_iff hm.ne' hQ').mpr
  nlinarith



theorem _root_.solution {d a0 : ℤ} {N : ℕ}
    (h : pellCFPrefixCheck d a0 N = true) :
    ∀ i ≤ N, pellConvergentPair (Real.sqrt (d : ℝ)) i =
      ((pellCFAt d a0 (pellCFInit a0) i).p,
       (pellCFAt d a0 (pellCFInit a0) i).q) := by
  have hh : (0 ≤ a0 ∧ a0^2 < d ∧ d < (a0+1)^2) ∧
      pellCFCheckFrom d a0 (pellCFInit a0) N = true := by
    simpa only [pellCFPrefixCheck,Bool.and_eq_true,decide_eq_true_eq] using h
  have hr := pell_sqrt_interval hh.1.1 hh.1.2.1 hh.1.2.2
  have hd0 : (0 : ℝ) ≤ d := by
    exact_mod_cast (show 0 ≤ d by nlinarith [sq_nonneg a0,hh.1.2.1])
  obtain ⟨hg,ht⟩ := pellCFCheckFrom_sound d a0 (pellCFInit a0) N hh.2
  let s (i : ℕ) := pellCFAt d a0 (pellCFInit a0) i
  have hs (i : ℕ) : s (i+1) = pellCFStep d a0 (s i) := pellCFAt_succ _ _ _ _
  have htail : ∀ i ≤ N, pellRealTail (Real.sqrt (d : ℝ)) i =
      (Real.sqrt d+(s i).m)/(s i).Q := by
    intro i
    induction i with
    | zero => intro hi; simp [pellRealTail,s,pellCFAt,pellCFInit]
    | succ i ih =>
        intro hi
        rw [pellRealTail_succ,ih (by omega),hs]
        exact pellCFState_tail hr hd0 (hg i (by omega))
          (hs i ▸ hg (i+1) hi) (ht i (by omega))
  have hf (i : ℕ) (hi : i ≤ N) :
      ⌊pellRealTail (Real.sqrt (d : ℝ)) i⌋ = (s i).a := by
    rw [htail i hi]
    exact pellCFState_floor hr (hg i hi)
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      intro hi
      rcases i with (_ | _ | i)
      · change (⌊Real.sqrt (d : ℝ)⌋,1) = (a0,1)
        have hf0 := hf 0 (by omega)
        simpa only [pellRealTail,s,pellCFAt,pellCFInit] using
          congrArg (fun a : ℤ => (a,1)) hf0
      · have hf0 := hf 0 (by omega)
        have hf1 := hf 1 hi
        change ⌊Real.sqrt (d : ℝ)⌋ = a0 at hf0
        change
          (⌊Real.sqrt (d : ℝ)⌋ * ⌊pellRealTail (Real.sqrt (d : ℝ)) 1⌋+1,
            ⌊pellRealTail (Real.sqrt (d : ℝ)) 1⌋) = ((s 1).p,(s 1).q)
        rw [hf0,hf1]
        simp only [s,pellCFAt,pellCFInit,pellCFStep]
        ext <;> ring
      · rw [pellConvergentPair_recurrence,
          ih (i+1) (by omega) (by omega),ih i (by omega) (by omega),hf (i+2) hi]
        have hpp : (s (i+1)).pp = (s i).p := by rw [hs]; rfl
        have hqq : (s (i+1)).qq = (s i).q := by rw [hs]; rfl
        change
          ((s (i+2)).a*(s (i+1)).p+(s i).p,
           (s (i+2)).a*(s (i+1)).q+(s i).q) = ((s (i+2)).p,(s (i+2)).q)
        rw [hs (i+1)]
        change
          ((pellCFStep d a0 (s (i+1))).a*(s (i+1)).p+(s i).p,
           (pellCFStep d a0 (s (i+1))).a*(s (i+1)).q+(s i).q) =
          ((pellCFStep d a0 (s (i+1))).a*(s (i+1)).p+(s (i+1)).pp,
           (pellCFStep d a0 (s (i+1))).a*(s (i+1)).q+(s (i+1)).qq)
        rw [hpp,hqq]





end D1Bound5
end
