-- Prove2me | solution 1 for BBBV.RandomPermutation.expected_queryMag_le
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T04:50:33.160987+00:00
-- url     : https://prove2.me/submissions/4886f6ae-bacc-4119-8d95-2245a996a614

import Mathlib
import Definitions.Def_BBBV_RandomPermutation_Chain

namespace BBBV.RandomPermutation

private theorem state_succ {n T : ℕ} {W : Type} [Fintype W]
    (M : QueryAlg (BBBV.RandomOracle.Str n) (BBBV.RandomOracle.Str n) W T)
    (g : Fin T → BBBV.RandomOracle.Str n → BBBV.RandomOracle.Str n) (i : ℕ) :
    state M g (i + 1) = if h : i < T then
      M.U ⟨i, h⟩ (oracleOp (g ⟨i, h⟩) (state M g i)) else state M g i := rfl

private theorem state_unit {n T : ℕ} {W : Type} [Fintype W]
    (M : QueryAlg (BBBV.RandomOracle.Str n) (BBBV.RandomOracle.Str n) W T)
    (g : Fin T → BBBV.RandomOracle.Str n → BBBV.RandomOracle.Str n) (i : ℕ) :
    ‖state M g i‖ = 1 := by
  induction i with
  | zero => exact M.init_norm
  | succ i ih => rw [state_succ]; split <;> simp_all

private theorem query_sum_le {n : ℕ} {W : Type} [Fintype W]
    (φ : State (BBBV.RandomOracle.Str n) (BBBV.RandomOracle.Str n) W) (hφ : ‖φ‖ = 1) :
    ∑ y, queryMag y φ ≤ 1 := by
  classical
  have hn := EuclideanSpace.norm_sq_eq φ
  rw [hφ] at hn
  simp only [one_pow, Fintype.sum_prod_type, Fintype.sum_option] at hn
  have hnon : 0 ≤ ∑ z : BBBV.RandomOracle.Str n, ∑ w : W, ‖φ (none, z, w)‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  unfold queryMag
  linarith

private theorem piChain_congr {n T : ℕ} (ω ω' : Ω n T) (k : ℕ)
    (hπ : ω.1 = ω'.1) (hx : ∀ a ≤ k, x ω a = x ω' a) :
    piChain ω k = piChain ω' k := by
  induction k with
  | zero => exact hπ
  | succ k ih =>
    change piChain ω k * Equiv.swap (x ω k) (x ω (k + 1)) =
      piChain ω' k * Equiv.swap (x ω' k) (x ω' (k + 1))
    rw [ih (fun a ha => hx a (by omega)), hx k (by omega), hx (k + 1) le_rfl]

private theorem state_prefix {n T : ℕ} {W : Type} [Fintype W]
    (M : QueryAlg (BBBV.RandomOracle.Str n) (BBBV.RandomOracle.Str n) W T)
    (ω ω' : Ω n T) (i : ℕ) (hπ : ω.1 = ω'.1)
    (hx : ∀ a < i, x ω a = x ω' a) :
    state M (hybrid ω) i = state M (hybrid ω') i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [state_succ, state_succ]
    split
    · rw [ih (fun a ha => hx a (by omega))]
      have hp := piChain_congr ω ω' i hπ (fun a ha => hx a (by omega))
      simp only [hybrid, hp]
    · exact ih (fun a ha => hx a (by omega))

private theorem average_bound {n T : ℕ} {W : Type} [Fintype W]
    (φ : Ω n T → State (BBBV.RandomOracle.Str n) (BBBV.RandomOracle.Str n) W)
    (z : Ω n T → BBBV.RandomOracle.Str n)
    (e : BBBV.RandomOracle.Str n → (Ω n T ≃ Ω n T))
    (hφ : ∀ y ω, φ (e y ω) = φ ω)
    (hz : ∀ ω, (∑ y, queryMag (z (e y ω)) (φ ω)) ≤ 1) :
    avg (fun ω => queryMag (z ω) (φ ω)) ≤ 1 / (2 : ℝ) ^ n := by
  classical
  let S := ∑ ω : Ω n T, queryMag (z ω) (φ ω)
  have he (y : BBBV.RandomOracle.Str n) :
      (∑ ω : Ω n T, queryMag (z (e y ω)) (φ ω)) = S := by
    conv_lhs => enter [2, ω]; rw [← hφ y ω]
    exact Equiv.sum_comp (e y) (fun ω => queryMag (z ω) (φ ω))
  have hcard : (Fintype.card (BBBV.RandomOracle.Str n) : ℝ) = (2 : ℝ) ^ n := by
    simp [BBBV.RandomOracle.Str]
  have hb : (2 : ℝ) ^ n * S ≤ (Fintype.card (Ω n T) : ℝ) := by
    calc
      _ = ∑ y : BBBV.RandomOracle.Str n, ∑ ω : Ω n T,
          queryMag (z (e y ω)) (φ ω) := by simp only [he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
      _ = ∑ ω : Ω n T, ∑ y : BBBV.RandomOracle.Str n,
          queryMag (z (e y ω)) (φ ω) := Finset.sum_comm
      _ ≤ ∑ _ω : Ω n T, (1 : ℝ) := Finset.sum_le_sum (fun ω _ => hz ω)
      _ = _ := by simp
  have hc : (0 : ℝ) < Fintype.card (Ω n T) := by
    exact_mod_cast Fintype.card_pos
  unfold avg
  apply (div_le_iff₀ hc).2
  have hb' : S ≤ (Fintype.card (Ω n T) : ℝ) / (2 : ℝ) ^ n :=
    (le_div_iff₀ (by positivity)).2 (by simpa [mul_comm] using hb)
  simpa [S, mul_comm, div_eq_mul_inv, mul_assoc] using hb'

theorem expected_queryMag_le {n T : ℕ} {W : Type} [Fintype W]
    (M : QueryAlg (BBBV.RandomOracle.Str n) (BBBV.RandomOracle.Str n) W T) (i : Fin T) (j : ℕ)
    (hij : (i : ℕ) ≤ j) (hj : j ≤ T + 1) :
    avg (fun ω : Ω n T => queryMag (x ω j) (state M (hybrid ω) i)) ≤
      1 / (2 : ℝ) ^ n := by
  classical
  cases j with
  | zero =>
    have hi : (i : ℕ) = 0 := by omega
    let e (y : BBBV.RandomOracle.Str n) : Ω n T ≃ Ω n T :=
      Equiv.prodCongr (Equiv.mulRight (Equiv.addRight (-y))) (Equiv.refl _)
    apply average_bound (fun ω => state M (hybrid ω) i) (fun ω => x ω 0) e
    · intro y ω; simp [hi, state]
    · intro ω
      have hx (y : BBBV.RandomOracle.Str n) : x (e y ω) 0 = x ω 0 + y := by
        change (Equiv.addRight (-y)).symm (ω.1.symm (BBBV.RandomOracle.ones n)) =
          ω.1.symm (BBBV.RandomOracle.ones n) + y
        simp
      simp_rw [hx]
      calc
        _ = ∑ y, queryMag y (state M (hybrid ω) i) := by
          simpa using Equiv.sum_comp (Equiv.addLeft (x ω 0)) (fun y => queryMag y (state M (hybrid ω) i))
        _ ≤ _ := query_sum_le _ (state_unit M _ _)
  | succ k =>
    let a : Fin (T + 1) := ⟨k, by omega⟩
    let e (y : BBBV.RandomOracle.Str n) : Ω n T ≃ Ω n T :=
      Equiv.prodCongr (Equiv.refl _) (Equiv.addRight (Pi.single a y))
    have hp (y : BBBV.RandomOracle.Str n) (ω : Ω n T) :
        state M (hybrid (e y ω)) i = state M (hybrid ω) i := by
      apply state_prefix M (e y ω) ω i rfl
      intro b hb
      cases b with
      | zero => rfl
      | succ b =>
        have hbt : b < T + 1 := by omega
        have hba : (⟨b, hbt⟩ : Fin (T + 1)) ≠ a := by
          intro hh; have := congrArg Fin.val hh; dsimp [a] at this; omega
        simp [e, x, hbt, Pi.single_apply, hba]
    apply average_bound (fun ω => state M (hybrid ω) i) (fun ω => x ω (k + 1)) e hp
    intro ω
    have hx (y : BBBV.RandomOracle.Str n) : x (e y ω) (k + 1) = x ω (k + 1) + y := by
      simp [e, x, show k < T + 1 by omega, a, Pi.single_apply]
    simp_rw [hx]
    calc
      _ = ∑ y, queryMag y (state M (hybrid ω) i) := by
        simpa using Equiv.sum_comp (Equiv.addLeft (x ω (k + 1))) (fun y => queryMag y (state M (hybrid ω) i))
      _ ≤ _ := query_sum_le _ (state_unit M _ _)

end BBBV.RandomPermutation

open BBBV.RandomPermutation

theorem solution {n T : ℕ} {W : Type} [Fintype W]
    (M : QueryAlg (BBBV.RandomOracle.Str n) (BBBV.RandomOracle.Str n) W T) (i : Fin T) (j : ℕ)
    (hij : (i : ℕ) ≤ j) (hj : j ≤ T + 1) :
    avg (fun ω : Ω n T => queryMag (x ω j) (state M (hybrid ω) i)) ≤
      1 / (2 : ℝ) ^ n := BBBV.RandomPermutation.expected_queryMag_le M i j hij hj

#print axioms solution
