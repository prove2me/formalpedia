-- Prove2me | solution 1 for CyclotomicRankTwoSVP.Main.sparse_multiplicity
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:32:09.92412+00:00
-- url     : https://prove2.me/submissions/937c3acb-82f8-4abb-8d82-adc7fe4711d6

import Mathlib
import Definitions.Def_CyclotomicRankTwoSVP_Main_Arithmetic

open scoped BigOperators

theorem solution (q s : ℕ) [Fact q.Prime] (hq : Odd q)
    (a : Fin s → Fin q) (ha : Function.Injective a) (c : Fin s → ZMod q)
    (hc : ∀ i, c i ≠ 0)
    (hF : (∑ i, Polynomial.monomial (a i).val (c i)) ≠ 0) :
    Polynomial.rootMultiplicity (1 : ZMod q) (∑ i, Polynomial.monomial (a i).val (c i)) ≤ s - 1 := by
  classical
  let D : Polynomial (ZMod q) := Polynomial.X - Polynomial.C 1
  have hle_root {P : Polynomial (ZMod q)} (hP : P ≠ 0) (k : ℕ)
      (hk : D ^ k ∣ P) : k ≤ Polynomial.rootMultiplicity 1 P := by
    by_contra h
    have hr : Polynomial.rootMultiplicity (1 : ZMod q) P ≤ k - 1 := by omega
    have hn := (Polynomial.rootMultiplicity_le_iff hP (1 : ZMod q) (k - 1)).mp hr
    have hkpos : 0 < k := by omega
    apply hn
    simpa [D, Nat.sub_add_cancel hkpos] using hk
  have hD : Polynomial.derivative D = 1 := by simp [D]
  have hderiv (k : ℕ) {P : Polynomial (ZMod q)}
      (hP : D ^ (k + 1) ∣ P) : D ^ k ∣ Polynomial.derivative P := by
    rcases hP with ⟨H, rfl⟩
    refine ⟨Polynomial.C (k + 1 : ZMod q) * H + D * Polynomial.derivative H, ?_⟩
    rw [Polynomial.derivative_mul, Polynomial.derivative_pow]
    rw [Nat.add_sub_cancel, hD, mul_one]
    simp only [pow_succ, Nat.cast_add, Nat.cast_one, map_add, map_one]
    ring
  have main : ∀ n : ℕ, ∀ (a : Fin (n + 1) → Fin q), Function.Injective a →
      ∀ (c : Fin (n + 1) → ZMod q), (∀ i, c i ≠ 0) →
      (∑ i, Polynomial.monomial (a i).val (c i)) ≠ 0 →
      Polynomial.rootMultiplicity (1 : ZMod q)
        (∑ i, Polynomial.monomial (a i).val (c i)) ≤ n := by
    intro n
    induction n with
    | zero =>
        intro a ha c hc hF
        have hnroot : ¬ Polynomial.IsRoot
            (∑ i : Fin 1, Polynomial.monomial (a i).val (c i)) (1 : ZMod q) := by
          simp [Polynomial.IsRoot, hc]
        rw [Polynomial.rootMultiplicity_eq_zero hnroot]
    | succ n ih =>
        intro a ha c hc hF
        let F : Polynomial (ZMod q) := ∑ i, Polynomial.monomial (a i).val (c i)
        let A : ZMod q := ((a (Fin.last (n + 1))).val : ZMod q)
        let G : Polynomial (ZMod q) := Polynomial.X * Polynomial.derivative F - A • F
        let a' : Fin (n + 1) → Fin q := fun i => a i.castSucc
        let c' : Fin (n + 1) → ZMod q := fun i =>
          c i.castSucc * (((a i.castSucc).val : ZMod q) - A)
        let P : Polynomial (ZMod q) := ∑ i, Polynomial.monomial (a' i).val (c' i)
        have ha' : Function.Injective a' := by
          intro i j hij
          apply Fin.ext
          have hcast : i.castSucc = j.castSucc := ha hij
          exact congrArg (fun r : Fin (n + 1 + 1) => r.val) hcast
        have hAcast (i : Fin (n + 1)) :
            (((a i.castSucc).val : ZMod q)) ≠ A := by
          intro h
          change (((a i.castSucc).val : ZMod q)) =
            (((a (Fin.last (n + 1))).val : ZMod q)) at h
          have hv : (a i.castSucc).val = (a (Fin.last (n + 1))).val := by
            have hm := (ZMod.natCast_eq_natCast_iff'
              (a i.castSucc).val (a (Fin.last (n + 1))).val q).mp h
            simpa [Nat.mod_eq_of_lt (a i.castSucc).isLt,
              Nat.mod_eq_of_lt (a (Fin.last (n + 1))).isLt] using hm
          have hai : a i.castSucc = a (Fin.last (n + 1)) := Fin.ext hv
          have hil : i.castSucc = Fin.last (n + 1) := ha hai
          exact Fin.castSucc_ne_last i hil
        have hc' : ∀ i, c' i ≠ 0 := by
          intro i
          exact mul_ne_zero (hc _) (sub_ne_zero.mpr (hAcast i))
        have hcoeff (i : Fin (n + 1)) : P.coeff (a' i).val = c' i := by
          have heq (x : Fin (n + 1)) :
              ((a' x).val = (a' i).val) ↔ x = i := by
            constructor
            · intro h
              apply ha'
              exact Fin.ext h
            · intro h
              cases h
              rfl
          simp [P, Polynomial.coeff_monomial, heq]
        have hP : P ≠ 0 := by
          intro hzero
          have hz := congrArg (fun R : Polynomial (ZMod q) => R.coeff (a' 0).val) hzero
          have : c' 0 = 0 := by simpa [hcoeff] using hz
          exact hc' 0 this
        have hterm (e : ℕ) (d : ZMod q) :
            Polynomial.X * Polynomial.derivative (Polynomial.monomial e d) -
                A • Polynomial.monomial e d =
              Polynomial.monomial e (d * ((e : ZMod q) - A)) := by
          by_cases he : e = 0
          · subst e
            simp [Polynomial.derivative_monomial, Polynomial.smul_monomial,
              smul_eq_mul, mul_comm]
          · rw [Polynomial.derivative_monomial, Polynomial.X_mul_monomial,
              Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr he),
              Polynomial.smul_monomial]
            rw [← Polynomial.monomial_sub]
            congr 1
            simp only [smul_eq_mul]
            ring
        have hG : G = P := by
          calc
            G = ∑ i : Fin (n + 2), Polynomial.monomial (a i).val
                (c i * (((a i).val : ZMod q) - A)) := by
              dsimp [G, F]
              simp only [map_sum, Finset.mul_sum, Finset.smul_sum,
                ← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro i hi
              exact hterm (a i).val (c i)
            _ = P := by
              rw [Fin.sum_univ_castSucc]
              simp [P, a', c', A]
        have hG0 : G ≠ 0 := hG.symm ▸ hP
        have hm : D ^ Polynomial.rootMultiplicity (1 : ZMod q) F ∣ F := by
          simpa [D] using Polynomial.pow_rootMultiplicity_dvd F (1 : ZMod q)
        cases hmk : Polynomial.rootMultiplicity (1 : ZMod q) F with
        | zero => simpa [F, hmk] using Nat.zero_le (n + 1)
        | succ k =>
            have hm' : D ^ (k + 1) ∣ F := by simpa [hmk] using hm
            have hkder : D ^ k ∣ Polynomial.derivative F := hderiv k hm'
            have hkF : D ^ k ∣ F :=
              dvd_trans (pow_dvd_pow D (Nat.le_succ k)) hm'
            have hkG : D ^ k ∣ G := by
              dsimp [G]
              rw [Polynomial.smul_eq_C_mul]
              exact dvd_sub (dvd_mul_of_dvd_right hkder Polynomial.X)
                (dvd_mul_of_dvd_right hkF (Polynomial.C A))
            have hk : k ≤ Polynomial.rootMultiplicity (1 : ZMod q) G :=
              hle_root hG0 k hkG
            have hi := ih a' ha' c' hc' hP
            have hGP : Polynomial.rootMultiplicity (1 : ZMod q) G ≤ n := by
              simpa [P, hG] using hi
            omega
  cases s with
  | zero => simp at hF
  | succ n => simpa using main n a ha c hc hF
