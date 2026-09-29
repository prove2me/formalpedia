-- Prove2me | solution 1 for AutomorphicForm.summable_integral_rpow_neg_and_summable_rpow_neg_of_ncard_spread_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/237f6c66-0e8d-5ab1-83fa-e6a71f60968d

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_summable_integral_rpow_neg_and_summable_rpow_neg_of_ncard_spread_le

set_option autoImplicit false

open MeasureTheory

noncomputable section

namespace CountSum

theorem summable_indicator_rpow_neg_of_ncard_le {ι : Type} (P : ι → Prop) [DecidablePred P] (s : ι → ℝ)
    (hs : ∀ e, 0 ≤ s e) (C : ℝ) (d : ℕ)
    (hcount : ∀ R : ℝ, 0 ≤ R → {e : ι | P e ∧ s e ≤ R}.Finite ∧ (({e : ι | P e ∧ s e ≤ R}.ncard : ℕ) : ℝ) ≤ C * (1 + R) ^ d)
    (A : ℕ) (hA : d + 2 ≤ A) :
    Summable (fun e : ι => if P e then (1 + s e) ^ (-(A : ℝ)) else 0) := by
  classical

  set a : ℕ → ℝ := fun n => C * (2 + (n : ℝ)) ^ d * (1 + (n : ℝ)) ^ (-(A : ℝ)) with ha
  have hC : 0 ≤ C := by
    have h := (hcount 0 le_rfl).2
    have h0 : (0 : ℝ) ≤ (({e : ι | P e ∧ s e ≤ 0}.ncard : ℕ) : ℝ) := by positivity
    simpa using h0.trans h
  have ha0 : ∀ n, 0 ≤ a n := fun n => by positivity
  have hasum : Summable a := by

    have hle : ∀ n : ℕ, a n ≤ C * 2 ^ d * (1 / ((n : ℝ) + 1) ^ (A - d)) := by
      intro n
      have h1 : (2 + (n : ℝ)) ^ d ≤ 2 ^ d * (1 + (n : ℝ)) ^ d := by
        rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) d
      have h2 : (1 + (n : ℝ)) ^ (-(A : ℝ)) = 1 / (1 + (n : ℝ)) ^ A := by
        rw [Real.rpow_neg (by positivity), Real.rpow_natCast, one_div]
      rw [ha]; dsimp only
      rw [h2]
      have h3 : (1 + (n : ℝ)) ^ d * (1 / (1 + (n : ℝ)) ^ A) = 1 / ((n : ℝ) + 1) ^ (A - d) := by
        rw [add_comm (1 : ℝ) n]
        have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        field_simp
        rw [← pow_add, Nat.add_sub_cancel' (by omega)]
      calc C * (2 + (n : ℝ)) ^ d * (1 / (1 + (n : ℝ)) ^ A)
          ≤ C * (2 ^ d * (1 + (n : ℝ)) ^ d) * (1 / (1 + (n : ℝ)) ^ A) := by gcongr
        _ = C * 2 ^ d * ((1 + (n : ℝ)) ^ d * (1 / (1 + (n : ℝ)) ^ A)) := by ring
        _ = C * 2 ^ d * (1 / ((n : ℝ) + 1) ^ (A - d)) := by rw [h3]
    refine Summable.of_nonneg_of_le ha0 hle ?_
    refine Summable.mul_left _ ?_
    have hp : 1 < A - d := by omega
    exact_mod_cast (summable_nat_add_iff 1).2 ((Real.summable_one_div_nat_pow).2 hp)

  refine summable_of_sum_le (fun e => by
    split_ifs
    · exact Real.rpow_nonneg (by linarith [hs e]) _
    · exact le_rfl) (c := ∑' n, a n) fun u => ?_

  have hfib : ∑ e ∈ u, (if P e then (1 + s e) ^ (-(A : ℝ)) else 0) =
      ∑ n ∈ (u.filter P).image (fun e => ⌊s e⌋₊), ∑ e ∈ (u.filter P).filter (fun e => ⌊s e⌋₊ = n), (1 + s e) ^ (-(A : ℝ)) := by
    rw [← Finset.sum_filter, Finset.sum_image' ]
    intro n hn
    rfl
  rw [hfib]
  calc ∑ n ∈ (u.filter P).image (fun e => ⌊s e⌋₊), ∑ e ∈ (u.filter P).filter (fun e => ⌊s e⌋₊ = n), (1 + s e) ^ (-(A : ℝ))
      ≤ ∑ n ∈ (u.filter P).image (fun e => ⌊s e⌋₊), a n := by
        refine Finset.sum_le_sum fun n _ => ?_

        have hterm : ∀ e ∈ (u.filter P).filter (fun e => ⌊s e⌋₊ = n), (1 + s e) ^ (-(A : ℝ)) ≤ (1 + (n : ℝ)) ^ (-(A : ℝ)) := by
          intro e he
          rw [Finset.mem_filter] at he
          have hn : (n : ℝ) ≤ s e := by rw [← he.2]; exact Nat.floor_le (hs e)
          exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by simp)
        have hcard : (((u.filter P).filter (fun e => ⌊s e⌋₊ = n)).card : ℝ) ≤ C * (2 + (n : ℝ)) ^ d := by
          obtain ⟨hfinR, hR⟩ := hcount ((n : ℝ) + 1) (by positivity)
          have hsub : (((u.filter P).filter (fun e => ⌊s e⌋₊ = n)) : Set ι) ⊆ {e : ι | P e ∧ s e ≤ (n : ℝ) + 1} := by
            intro e he
            simp only [Finset.coe_filter, Finset.mem_filter, Set.mem_setOf_eq] at he
            refine ⟨he.1.2, ?_⟩
            have := Nat.lt_floor_add_one (s e)
            rw [he.2] at this
            push_cast at this
            linarith
          have h1 := Set.ncard_le_ncard hsub hfinR
          rw [Set.ncard_coe_finset] at h1
          calc (((u.filter P).filter (fun e => ⌊s e⌋₊ = n)).card : ℝ) ≤ (({e : ι | P e ∧ s e ≤ (n : ℝ) + 1}.ncard : ℕ) : ℝ) := by
                exact_mod_cast h1
            _ ≤ C * (1 + ((n : ℝ) + 1)) ^ d := hR
            _ = C * (2 + (n : ℝ)) ^ d := by ring
        calc ∑ e ∈ (u.filter P).filter (fun e => ⌊s e⌋₊ = n), (1 + s e) ^ (-(A : ℝ))
            ≤ ∑ e ∈ (u.filter P).filter (fun e => ⌊s e⌋₊ = n), (1 + (n : ℝ)) ^ (-(A : ℝ)) := Finset.sum_le_sum hterm
          _ = (((u.filter P).filter (fun e => ⌊s e⌋₊ = n)).card : ℝ) * (1 + (n : ℝ)) ^ (-(A : ℝ)) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ C * (2 + (n : ℝ)) ^ d * (1 + (n : ℝ)) ^ (-(A : ℝ)) := by gcongr
          _ = a n := rfl
    _ ≤ ∑' n, a n := hasum.sum_le_tsum _ (fun n _ => ha0 n)

theorem integral_profile (a : ℝ) (ha : 0 < a) (c : ℝ) (B : ℝ) :
    ∫ t : ℝ, (a + |t + c| / 2) ^ (-B) = 2 * a ^ (1 - B) * ∫ x : ℝ, (1 + |x|) ^ (-B) := by
  have h1 : (fun t : ℝ => (a + |t + c| / 2) ^ (-B)) = fun t => (fun u : ℝ => (a + |u| / 2) ^ (-B)) (t + c) := rfl
  rw [h1, integral_add_right_eq_self (fun u : ℝ => (a + |u| / 2) ^ (-B)) c]
  have h2 : (fun u : ℝ => (a + |u| / 2) ^ (-B)) = fun u => a ^ (-B) * (fun x : ℝ => (1 + |x|) ^ (-B)) ((2 * a)⁻¹ * u) := by
    funext u
    have : a + |u| / 2 = a * (1 + |(2 * a)⁻¹ * u|) := by
      rw [abs_mul, abs_inv, abs_of_pos (by positivity : (0 : ℝ) < 2 * a)]
      field_simp
    rw [this, Real.mul_rpow ha.le (by positivity)]
  rw [h2, integral_const_mul, Measure.integral_comp_mul_left (fun x : ℝ => (1 + |x|) ^ (-B)) ((2 * a)⁻¹)]
  rw [inv_inv, abs_of_pos (by positivity : (0 : ℝ) < 2 * a), smul_eq_mul]
  have : a ^ (-B) * (2 * a) = 2 * a ^ (1 - B) := by
    rw [sub_eq_add_neg, Real.rpow_add ha, Real.rpow_one]; ring
  rw [← mul_assoc, this]

theorem integrable_profile (a : ℝ) (ha : 0 < a) (c : ℝ) (B : ℝ) (hB : 1 < B) :
    Integrable (fun t : ℝ => (a + |t + c| / 2) ^ (-B)) := by
  have hI : Integrable (fun x : ℝ => (1 + |x|) ^ (-B)) := by
    have := integrable_one_add_norm (E := ℝ) (μ := volume) (r := B) (by simpa using hB)
    simpa [Real.norm_eq_abs] using this
  have h2 : (fun t : ℝ => (a + |t + c| / 2) ^ (-B)) =
      fun t => a ^ (-B) * (fun x : ℝ => (1 + |x|) ^ (-B)) ((2 * a)⁻¹ * (t + c)) := by
    funext t
    have : a + |t + c| / 2 = a * (1 + |(2 * a)⁻¹ * (t + c)|) := by
      rw [abs_mul, abs_inv, abs_of_pos (by positivity : (0 : ℝ) < 2 * a)]
      field_simp
    rw [this, Real.mul_rpow ha.le (by positivity)]
  rw [h2]
  refine Integrable.const_mul ?_ _
  have h3 := (hI.comp_mul_left' (inv_ne_zero (by positivity : (2 * a : ℝ) ≠ 0))).comp_add_right c
  exact h3

theorem spread_le_sum {V : Type} [Fintype V] (τ : V → ℝ) (t : ℝ) :
    ∑ v : V, ∑ v' : V, |τ v - τ v'| ≤ 2 * (Fintype.card V : ℝ) * ∑ v : V, |t + τ v| := by
  calc ∑ v : V, ∑ v' : V, |τ v - τ v'| ≤ ∑ v : V, ∑ v' : V, (|t + τ v| + |t + τ v'|) := by
        refine Finset.sum_le_sum fun v _ => Finset.sum_le_sum fun v' _ => ?_
        calc |τ v - τ v'| = |(t + τ v) - (t + τ v')| := by ring_nf
          _ ≤ |t + τ v| + |t + τ v'| := abs_sub _ _
    _ = 2 * (Fintype.card V : ℝ) * ∑ v : V, |t + τ v| := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        rw [← Finset.mul_sum]
        ring

end CountSum

open CountSum in
theorem solution
    (V : Type) [Fintype V] [Nonempty V] (ιE : Type) (nE : ιE → ℕ)
    (τ τ' : ιE → V → ℝ) (C : ℝ) (d : ℕ)
    (hcount : ∀ R : ℝ, 0 ≤ R →
      {e : ιE | 0 < nE e ∧ ∑ v : V, ∑ v' : V, |τ e v - τ e v'| ≤ R}.Finite ∧
      (({e : ιE | 0 < nE e ∧ ∑ v : V, ∑ v' : V, |τ e v - τ e v'| ≤ R}.ncard : ℕ) : ℝ) ≤ C * (1 + R) ^ d) :
    ∀ B : ℕ, d + 3 ≤ B →
      Summable (fun e : ιE => if 0 < nE e then
        ∫ t : ℝ, (1 + ∑ v : V, (|t + τ e v| + |t - τ' e v|)) ^ (-(B : ℝ)) else 0) ∧
      Summable (fun e : ιE => if 0 < nE e then
        (1 + ∑ v : V, (|τ e v| + |τ' e v|)) ^ (-(B : ℝ)) else 0) := by
  classical
  intro B hB
  obtain ⟨v₀⟩ := (inferInstance : Nonempty V)
  set N : ℝ := (Fintype.card V : ℝ) with hN
  have hN1 : (1 : ℝ) ≤ N := by
    have : 1 ≤ Fintype.card V := Fintype.card_pos
    rw [hN]; exact_mod_cast this
  have h4N : (0 : ℝ) < 4 * N := by positivity
  have h2N : (0 : ℝ) < 2 * N := by positivity
  set sp : ιE → ℝ := fun e => ∑ v : V, ∑ v' : V, |τ e v - τ e v'| with hsp
  have hsp0 : ∀ e, 0 ≤ sp e := fun e => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hBr : (1 : ℝ) < (B : ℝ) := by exact_mod_cast (show 1 < B by omega)
  set I : ℝ := ∫ x : ℝ, (1 + |x|) ^ (-(B : ℝ)) with hI
  have hI0 : 0 ≤ I := integral_nonneg fun x => Real.rpow_nonneg (by positivity) _

  have S1 := summable_indicator_rpow_neg_of_ncard_le (fun e => 0 < nE e) sp hsp0 C d hcount (B - 1) (by omega)
  have S2 := summable_indicator_rpow_neg_of_ncard_le (fun e => 0 < nE e) sp hsp0 C d hcount B (by omega)
  constructor
  ·
    set K₁ : ℝ := 2 * I * (4 * N) ^ ((B : ℝ) - 1) with hK₁
    refine Summable.of_nonneg_of_le (fun e => ?_) (fun e => ?_) ((S1.mul_left K₁))
    · split_ifs
      · exact integral_nonneg fun t => Real.rpow_nonneg (by positivity) _
      · exact le_rfl
    · by_cases he : 0 < nE e
      · simp only [if_pos he]
        set a : ℝ := 1 + sp e / (4 * N) with ha
        have ha1 : 1 ≤ a := by
          have h0 : 0 ≤ sp e / (4 * N) := div_nonneg (hsp0 e) h4N.le
          simp only [ha]; linarith
        have ha0 : 0 < a := by linarith

        have hdom : ∀ t : ℝ, (1 + ∑ v : V, (|t + τ e v| + |t - τ' e v|)) ^ (-(B : ℝ)) ≤ (a + |t + τ e v₀| / 2) ^ (-(B : ℝ)) := by
          intro t
          have h1 : |t + τ e v₀| ≤ ∑ v : V, |t + τ e v| :=
            Finset.single_le_sum (f := fun v => |t + τ e v|) (fun v _ => abs_nonneg _) (Finset.mem_univ v₀)
          have h2 : sp e ≤ 2 * N * ∑ v : V, |t + τ e v| := spread_le_sum (τ e) t
          have h3 : ∑ v : V, |t + τ e v| ≤ ∑ v : V, (|t + τ e v| + |t - τ' e v|) :=
            Finset.sum_le_sum fun v _ => le_add_of_nonneg_right (abs_nonneg _)
          have h4 : sp e / (4 * N) ≤ (∑ v : V, |t + τ e v|) / 2 := by
            rw [div_le_iff₀ h4N]
            nlinarith [h2, hN1]
          have h5 : a + |t + τ e v₀| / 2 ≤ 1 + ∑ v : V, (|t + τ e v| + |t - τ' e v|) := by rw [ha]; linarith
          exact Real.rpow_le_rpow_of_nonpos (by positivity) h5 (by simp)
        have hint := integrable_profile a ha0 (τ e v₀) (B : ℝ) hBr
        calc ∫ t : ℝ, (1 + ∑ v : V, (|t + τ e v| + |t - τ' e v|)) ^ (-(B : ℝ))
            ≤ ∫ t : ℝ, (a + |t + τ e v₀| / 2) ^ (-(B : ℝ)) := by
              refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => Real.rpow_nonneg (by positivity) _) hint
                (Filter.Eventually.of_forall hdom)
          _ = 2 * a ^ (1 - (B : ℝ)) * I := integral_profile a ha0 _ _
          _ ≤ 2 * ((4 * N) ^ ((B : ℝ) - 1) * (1 + sp e) ^ (-((B - 1 : ℕ) : ℝ))) * I := by
              gcongr

              have hq : (1 + sp e) / (4 * N) ≤ a := by
                rw [ha, div_le_iff₀ h4N, add_mul, div_mul_cancel₀ _ h4N.ne']
                nlinarith [hN1, hsp0 e]
              have hneg : (1 : ℝ) - B ≤ 0 := by linarith
              calc a ^ (1 - (B : ℝ)) ≤ ((1 + sp e) / (4 * N)) ^ (1 - (B : ℝ)) :=
                    Real.rpow_le_rpow_of_nonpos (by positivity) hq hneg
                _ = (4 * N) ^ ((B : ℝ) - 1) * (1 + sp e) ^ (-((B - 1 : ℕ) : ℝ)) := by
                    rw [Real.div_rpow (by linarith [hsp0 e]) (by positivity), Nat.cast_sub (by omega), Nat.cast_one,
                      neg_sub, div_eq_mul_inv, ← Real.rpow_neg (by positivity), neg_sub, mul_comm]
          _ = K₁ * (1 + sp e) ^ (-((B - 1 : ℕ) : ℝ)) := by rw [hK₁]; ring
      · simp only [if_neg he, mul_zero]; exact le_rfl
  ·
    set K₂ : ℝ := (2 * N) ^ (B : ℝ) with hK₂
    refine Summable.of_nonneg_of_le (fun e => ?_) (fun e => ?_) ((S2.mul_left K₂))
    · split_ifs
      · exact Real.rpow_nonneg (by positivity) _
      · exact le_rfl
    · by_cases he : 0 < nE e
      · simp only [if_pos he]
        have h2 : sp e ≤ 2 * N * ∑ v : V, |τ e v| := by simpa using spread_le_sum (τ e) 0
        have h3 : ∑ v : V, |τ e v| ≤ ∑ v : V, (|τ e v| + |τ' e v|) :=
          Finset.sum_le_sum fun v _ => le_add_of_nonneg_right (abs_nonneg _)
        have hq : (1 + sp e) / (2 * N) ≤ 1 + ∑ v : V, (|τ e v| + |τ' e v|) := by
          rw [div_le_iff₀ h2N]
          have hs0 : 0 ≤ ∑ v : V, (|τ e v| + |τ' e v|) := Finset.sum_nonneg fun v _ => by positivity
          nlinarith [hN1, h2, h3, hs0]
        calc (1 + ∑ v : V, (|τ e v| + |τ' e v|)) ^ (-(B : ℝ)) ≤ ((1 + sp e) / (2 * N)) ^ (-(B : ℝ)) :=
              Real.rpow_le_rpow_of_nonpos (by positivity) hq (by simp)
          _ = K₂ * (1 + sp e) ^ (-(B : ℝ)) := by
              rw [Real.div_rpow (by linarith [hsp0 e]) (by positivity), hK₂, div_eq_mul_inv, ← Real.rpow_neg (by positivity),
                neg_neg, mul_comm]
      · simp only [if_neg he, mul_zero]; exact le_rfl

end

end S_AutomorphicForm_summable_integral_rpow_neg_and_summable_rpow_neg_of_ncard_spread_le
end P2MW
export P2MW.S_AutomorphicForm_summable_integral_rpow_neg_and_summable_rpow_neg_of_ncard_spread_le (solution)
