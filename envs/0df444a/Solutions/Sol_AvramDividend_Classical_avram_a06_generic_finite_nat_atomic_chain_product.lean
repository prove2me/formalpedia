-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_generic_finite_nat_atomic_chain_product
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T11:33:43.519406+00:00
-- url     : https://prove2.me/submissions/50551d42-e8e0-4455-9063-eb1905c655c1

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Finset
noncomputable section

/-- Repeated one-step conditional atom factorisation implies finite joint product laws. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (Z : Fin n → Ω → ℕ)
    (hStep : ∀ (j : Fin n) (v : Fin n → ℕ) (k : ℕ),
      P {ω | (∀ i : Fin n, i < j → Z i ω = v i) ∧ Z j ω = k} =
        P {ω | ∀ i : Fin n, i < j → Z i ω = v i} *
        P {ω | Z j ω = k}) :
    ∀ v : Fin n → ℕ,
      P {ω | ∀ i, Z i ω = v i} =
        ∏ i : Fin n, P {ω | Z i ω = v i} := by
  classical
  intro v
  let f : Fin n → ENNReal := fun i => P {ω | Z i ω = v i}
  let S : ℕ → Finset (Fin n) := fun m =>
    Finset.univ.filter (fun i => i.val < m)
  let E : ℕ → Set Ω := fun m =>
    {ω | ∀ i : Fin n, i.val < m → Z i ω = v i}
  have hInd : ∀ m : ℕ, m ≤ n →
      P (E m) = ∏ i ∈ S m, f i := by
    intro m
    induction m with
    | zero =>
        intro _
        simp [E, S]
    | succ m ih =>
        intro hmn
        have hm : m < n := by omega
        let j : Fin n := ⟨m, hm⟩
        have hE : E (m + 1) =
            {ω | (∀ i : Fin n, i < j → Z i ω = v i) ∧
              Z j ω = v j} := by
          ext ω
          change (∀ i : Fin n, i.val < m + 1 → Z i ω = v i) ↔
            ((∀ i : Fin n, i < j → Z i ω = v i) ∧ Z j ω = v j)
          constructor
          · intro h
            constructor
            · intro i hi
              exact h i (by change i.val < m at hi; omega)
            · exact h j (by change m < m + 1; omega)
          · rintro ⟨hbefore, hj⟩ i hi
            by_cases hij : i = j
            · simpa [hij] using hj
            · have him : i < j := by
                change i.val < m
                have hne : i.val ≠ m := by
                  intro heq
                  apply hij
                  exact Fin.ext heq
                omega
              exact hbefore i him
        have hPrev : E m =
            {ω | ∀ i : Fin n, i < j → Z i ω = v i} := by
          ext ω
          change (∀ i : Fin n, i.val < m → Z i ω = v i) ↔
            (∀ i : Fin n, i < j → Z i ω = v i)
          constructor
          · intro h i hi
            exact h i (by change i.val < m at hi; exact hi)
          · intro h i hi
            exact h i (by change i.val < m; exact hi)
        have hS : S (m + 1) = insert j (S m) := by
          ext i
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_insert]
          constructor
          · intro hi
            by_cases hil : i.val < m
            · exact Or.inr hil
            · left
              apply Fin.ext
              dsimp [j]
              omega
          · rintro (rfl | hi)
            · change m < m + 1
              omega
            · omega
        have hNot : j ∉ S m := by
          simp [S, j]
        calc
          P (E (m + 1)) =
              P {ω | (∀ i : Fin n, i < j → Z i ω = v i) ∧
                Z j ω = v j} := congrArg P hE
          _ = P (E m) * f j := by
            simpa only [← hPrev, f] using hStep j v (v j)
          _ = (∏ i ∈ S m, f i) * f j := by rw [ih (by omega)]
          _ = ∏ i ∈ S (m + 1), f i := by
            rw [hS, Finset.prod_insert hNot]
            exact mul_comm _ _
  have hTop := hInd n le_rfl
  have hEtop : E n = {ω | ∀ i, Z i ω = v i} := by
    ext ω
    simp [E, Fin.isLt]
  have hStop : S n = Finset.univ := by
    ext i
    simp [S, i.isLt]
  rw [hEtop, hStop] at hTop
  simpa [f] using hTop
