-- Prove2me | solution 1 for GRH.centered_moebius_uniform_large_modulus_range
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T05:16:13.024227+00:00
-- url     : https://prove2.me/submissions/dc0048dc-5648-4712-8b8c-07d527bc5d09

import Definitions.Def_GRH_AdditiveMoebiusSpectrum
import Theorems.Thm_GRH_centered_moebius_mertens_remainder
import Theorems.Thm_Helfgott_coprime_mobius_reciprocal_le_one
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

open Finset GRH.AdditiveMoebiusSpectrum

private theorem prefixIdentity {q : ℕ} (a : ZMod q) (N : ℕ) :
    fiber a N (weight true N) = 2 * GRH.OneSidedMoebius.residue a N.sqrt -
      GRH.OneSidedMoebius.residue a N := by
  classical
  let f := fun k : ℕ => if (k : ZMod q) = a then (ArithmeticFunction.moebius k : ℝ) else 0
  have hset : (range (N+1)).filter (fun k => k ≤ N.sqrt) = range (N.sqrt+1) := by
    ext k
    simp only [mem_filter, mem_range]
    have := Nat.sqrt_le_self N
    omega
  have hp : (∑ k ∈ range (N+1), if k ≤ N.sqrt then f k else 0) =
      GRH.OneSidedMoebius.residue a N.sqrt := by
    rw [← sum_filter, hset]
    rfl
  unfold fiber
  calc
    _ = ∑ k ∈ range (N+1), (2 * (if k ≤ N.sqrt then f k else 0) - f k) := by
      apply sum_congr rfl
      intro k _
      by_cases hr : (k : ZMod q) = a <;> by_cases hk : k ≤ N.sqrt <;>
        simp [f,weight,hr,hk,Nat.lt_of_not_ge,not_lt.mpr]
      all_goals ring
    _ = _ := by rw [sum_sub_distrib, ← mul_sum, hp]; rfl

private theorem countBound {q : ℕ} (a : ZMod q) (N : ℕ) :
    ((range (N+1)).filter (fun n : ℕ => (n : ZMod q) = a)).card ≤ N / q + 1 := by
  let S := (range (N+1)).filter fun n : ℕ => (n : ZMod q) = a
  have h := card_le_card_of_injOn (s:=S) (t:=range (N/q+1)) (fun n => n/q) (by
    intro n hn
    have hn' := mem_range.mp (mem_filter.mp hn).1
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (by omega : n ≤ N)))) (by
    intro i hi j hj he
    have hij : (i : ZMod q) = (j : ZMod q) :=
      (mem_filter.mp hi).2.trans (mem_filter.mp hj).2.symm
    have hm : i % q = j % q := by simpa only [ZMod.val_natCast] using congrArg ZMod.val hij
    change i / q = j / q at he
    calc i = i % q + q * (i / q) := (Nat.mod_add_div i q).symm
         _ = j % q + q * (j / q) := by rw [hm,he]
         _ = j := Nat.mod_add_div j q)
  simpa only [card_range] using h

private theorem absFiber {q : ℕ} (a : ZMod q) (N : ℕ) :
    |fiber a N (weight true N)| ≤ (N : ℝ) / q + 1 := by
  classical
  let S := (range (N+1)).filter fun n : ℕ => (n : ZMod q) = a
  have h : fiber a N (weight true N) = ∑ k ∈ S, weight true N k := by
    simp only [fiber,S,sum_filter]
  rw [h]
  calc
    _ ≤ ∑ k ∈ S, |weight true N k| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ S, (1 : ℝ) := by
      apply sum_le_sum
      intro k _
      have hm : |(ArithmeticFunction.moebius k : ℝ)| ≤ 1 := by
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n:=k))
      simpa [weight] using (show |if N.sqrt < k then -(ArithmeticFunction.moebius k : ℝ)
          else (ArithmeticFunction.moebius k : ℝ)| ≤ 1 by split_ifs <;> simpa using hm)
    _ = (S.card : ℝ) := by simp
    _ ≤ ((N/q : ℕ) : ℝ)+1 := by exact_mod_cast countBound a N
    _ ≤ _ := add_le_add Nat.cast_div_le le_rfl

private theorem correctionBounds (q : ℕ) [NeZero q] (N : ℕ) :
    0 ≤ correction q N ∧ correction q N ≤ (N : ℝ)/q := by
  have hi : Finset.Ioc 0 N.sqrt = Finset.Icc 1 N.sqrt := by ext k; simp; omega
  have h : |GRH.reducedMoebiusHarmonic q N.sqrt| ≤ 1 := by
    simpa only [GRH.reducedMoebiusHarmonic, hi, ZMod.isUnit_iff_coprime] using
      Helfgott.coprime_mobius_reciprocal_le_one q N.sqrt
  have hs := (abs_le.mp h)
  have hh : (GRH.reducedMoebiusHarmonic q N.sqrt)^2 ≤ 1 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hs.2) (by linarith only [hs.1] :
      0 ≤ 1 + GRH.reducedMoebiusHarmonic q N.sqrt)]
  exact ⟨mul_nonneg (by positivity) (sq_nonneg _),
    (mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ (N : ℝ)/q)).trans_eq (mul_one _)⟩

theorem solution (q : ℕ) [NeZero q] (a : ZMod q) (N : ℕ) :
    (GRH.centeredMoebiusBilinear q a N + correction q N = fiber a N (weight true N)) ∧
    |GRH.centeredMoebiusBilinear q a N| ≤ 2 * (N : ℝ)/q + 1 ∧
    (N ≤ q^2 → |GRH.centeredMoebiusBilinear q a N| ≤ 2 * Real.sqrt N + 1) ∧
    (∀ σ : ℝ, 0 ≤ σ → ((N : ℝ)+1)^(1-σ) ≤ q →
      |GRH.centeredMoebiusBilinear q a N| ≤ 3 * ((N : ℝ)+1)^σ) := by
  have h0 := (GRH.centered_moebius_mertens_remainder q a N).1
  change GRH.centeredMoebiusBilinear q a N + (GRH.OneSidedMoebius.residue a N +
    1 / (q : ℝ) * N * (GRH.reducedMoebiusHarmonic q N.sqrt)^2) =
      2 * GRH.OneSidedMoebius.residue a N.sqrt at h0
  have he : GRH.centeredMoebiusBilinear q a N + correction q N = fiber a N (weight true N) := by
    rw [prefixIdentity,correction]
    simp only [div_eq_mul_inv,one_mul] at h0 ⊢
    linarith only [h0]
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  obtain ⟨hc,hcap⟩ := correctionBounds q N
  have hs : |GRH.centeredMoebiusBilinear q a N| ≤ 2*(N : ℝ)/q+1 := by
    calc
      _ = |fiber a N (weight true N) - correction q N| := by rw [← he,add_sub_cancel_right]
      _ ≤ |fiber a N (weight true N)| + |correction q N| := abs_sub _ _
      _ ≤ (N : ℝ)/q+1 + (N : ℝ)/q := add_le_add (absFiber a N) (by rwa [abs_of_nonneg hc])
      _ = _ := by ring
  refine ⟨he,hs,?_,?_⟩
  · intro hN
    have hN' : (N : ℝ) ≤ (q : ℝ)^2 := by exact_mod_cast hN
    have hroot := Real.sqrt_le_sqrt hN'
    rw [Real.sqrt_sq hq.le] at hroot
    have hsqr := Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) N)
    have hdiv : (N : ℝ)/q ≤ Real.sqrt N := (div_le_iff₀ hq).mpr (by
      nlinarith [mul_nonneg (Real.sqrt_nonneg (N : ℝ)) (sub_nonneg.mpr hroot)])
    linarith only [hs,hdiv,show 2*(N : ℝ)/q=2*((N : ℝ)/q) by ring]
  · intro σ hσ hcut
    let X : ℝ := (N : ℝ)+1
    have hX : 1 ≤ X := by dsimp [X]; linarith [Nat.cast_nonneg (α:=ℝ) N]
    have hx : 0 < X := by linarith
    have hp : 1 ≤ X^σ := Real.one_le_rpow hX hσ
    have hmul : X^σ * X^(1-σ) = X := by
      rw [← Real.rpow_add hx, show σ+(1-σ)=1 by ring,Real.rpow_one]
    have hdiv : (N : ℝ)/q ≤ X^σ := (div_le_iff₀ hq).mpr (by
      calc (N : ℝ) ≤ X := by dsimp [X]; linarith
           _ = X^σ * X^(1-σ) := hmul.symm
           _ ≤ X^σ * q := mul_le_mul_of_nonneg_left hcut (by positivity))
    change _ ≤ 3*X^σ
    linarith only [hs,hp,hdiv,show 2*(N : ℝ)/q=2*((N : ℝ)/q) by ring]
