-- Prove2me | solution 1 for DisruptReroute.Resil.theorem_5_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T12:53:13.054204+00:00
-- url     : https://prove2.me/submissions/777f76fb-0868-4837-bdba-b9c0a030fc40

import Mathlib
import Definitions.Def_DisruptReroute_Resil_Risk
import Definitions.Def_DisruptReroute_Resil_Diversification

set_option autoImplicit false

namespace P118

open DisruptReroute.Resil

lemma rowsum_eq {N M : ℕ} (A B : OrderNetwork N M) (tier : Fin N → ℕ)
    (hA : IsTiered A tier) (hB : IsTiered B tier) (hDiv : MoreDiversified A B tier)
    (m : ℕ) (k : Fin N) : ∑ j, A.order m k j = ∑ j, B.order m k j := by
  by_cases hm : m = tier k
  · subst hm
    have h1 : ∑ j ∈ buyers A tier k, A.order (tier k) k j = ∑ j, A.order (tier k) k j := by
      unfold buyers
      apply Finset.sum_filter_of_ne
      intro x _ hx
      exact lt_of_le_of_ne (A.order_nonneg _ _ _) (Ne.symm hx)
    have h2 : ∑ j ∈ buyers B tier k, B.order (tier k) k j = ∑ j, B.order (tier k) k j := by
      unfold buyers
      apply Finset.sum_filter_of_ne
      intro x _ hx
      exact lt_of_le_of_ne (B.order_nonneg _ _ _) (Ne.symm hx)
    rw [← h1, ← h2]
    exact (hDiv k).2.1
  · have hA0 : ∀ j, A.order m k j = 0 := by
      intro j
      rcases (A.order_nonneg m k j).lt_or_eq with h | h
      · exact absurd (hA.2.1 m k j h).1.symm hm
      · exact h.symm
    have hB0 : ∀ j, B.order m k j = 0 := by
      intro j
      rcases (B.order_nonneg m k j).lt_or_eq with h | h
      · exact absurd (hB.2.1 m k j h).1.symm hm
      · exact h.symm
    simp [hA0, hB0]

lemma colsum_eq {N M : ℕ} (A B : OrderNetwork N M) (tier : Fin N → ℕ)
    (hA : IsTiered A tier) (hB : IsTiered B tier) (hDiv : MoreDiversified A B tier)
    (X : Finset (Fin N)) (m : ℕ) :
    ∑ i, ∑ k ∈ X, A.order m k i = ∑ i, ∑ k ∈ X, B.order m k i := by
  calc ∑ i, ∑ k ∈ X, A.order m k i = ∑ k ∈ X, ∑ i, A.order m k i := Finset.sum_comm
    _ = ∑ k ∈ X, ∑ i, B.order m k i :=
        Finset.sum_congr rfl fun k _ => rowsum_eq A B tier hA hB hDiv m k
    _ = ∑ i, ∑ k ∈ X, B.order m k i := Finset.sum_comm

lemma D0_eq {N M : ℕ} (R : RiskData N M) (A B : OrderNetwork N M) (tier : Fin N → ℕ)
    (hA : IsTiered A tier) (hB : IsTiered B tier) (hDiv : MoreDiversified A B tier)
    (c : Fin N → ℝ) (y : ℝ) : D0 R A c y = D0 R B c y := by
  unfold D0
  simp only [rowsum_eq A B tier hA hB hDiv]

lemma sum_zetaI {N M : ℕ} (R : RiskData N M) (O : OrderNetwork N M)
    (c : Fin N → ℝ) (y : ℝ) :
    ∑ i, zetaI R O c y i = ∑ m ∈ Finset.Icc 1 M, ((∑ i, y * R.holding m i) +
      (∑ j, sigmaSw O (D0 R O c y) y m j) *
        R.sInv m (∑ j, sigmaSw O (D0 R O c y) y m j)) := by
  unfold zetaI
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Finset.sum_add_distrib, Finset.sum_mul]

lemma T_nonneg {N M : ℕ} (O : OrderNetwork N M) (X : Finset (Fin N)) (y : ℝ) (m : ℕ) :
    0 ≤ ∑ j, sigmaSw O X y m j :=
  Finset.sum_nonneg fun j _ => by unfold sigmaSw; exact le_max_left _ _

lemma T0_eq {N M : ℕ} (A B : OrderNetwork N M) (tier : Fin N → ℕ)
    (hA : IsTiered A tier) (hB : IsTiered B tier) (hDiv : MoreDiversified A B tier)
    (X : Finset (Fin N)) (m : ℕ) :
    ∑ j, sigmaSw A X 0 m j = ∑ j, sigmaSw B X 0 m j := by
  have hO : ∀ (O : OrderNetwork N M),
      ∑ j, sigmaSw O X 0 m j = ∑ j, ∑ k ∈ X, O.order m k j := by
    intro O
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold sigmaSw
    rw [sub_zero]
    exact max_eq_right (Finset.sum_nonneg fun k _ => O.order_nonneg m k j)
  rw [hO A, hO B]
  exact colsum_eq A B tier hA hB hDiv X m

lemma pt_le {N M : ℕ} (A B : OrderNetwork N M) (tier : Fin N → ℕ)
    (hA : IsTiered A tier) (hDiv : MoreDiversified A B tier)
    (X : Finset (Fin N)) (θ : ℝ)
    (hθA : AssumptionTwoOne A tier θ) (hθB : AssumptionTwoOne B tier θ)
    (m : ℕ) (i : Fin N) :
    sigmaSw B X θ m i + ∑ k ∈ X, A.order m k i ≤
      sigmaSw A X θ m i + ∑ k ∈ X, B.order m k i := by
  unfold sigmaSw
  have hθ := hθA.1
  have sB0 : 0 ≤ ∑ k ∈ X, B.order m k i := Finset.sum_nonneg fun k _ => B.order_nonneg m k i
  by_cases hpos : ∃ k ∈ X, 0 < A.order m k i
  · obtain ⟨k, hkX, hk⟩ := hpos
    obtain ⟨_, ht2⟩ := hA.2.1 m k i hk
    have hm : tier i - 1 = m := by omega
    have hkA : k ∈ suppliers A tier i := by
      unfold suppliers
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hm]; exact hk
    have hkB := (hDiv i).2.2.1 hkA
    have hBθ : θ ≤ B.order m k i := by
      have := hθB.2 i k hkB; rwa [hm] at this
    have hAθ : θ ≤ A.order m k i := by
      have := hθA.2 i k hkA; rwa [hm] at this
    have hA1 : A.order m k i ≤ ∑ k ∈ X, A.order m k i :=
      Finset.single_le_sum (fun k _ => A.order_nonneg m k i) hkX
    have hB1 : B.order m k i ≤ ∑ k ∈ X, B.order m k i :=
      Finset.single_le_sum (fun k _ => B.order_nonneg m k i) hkX
    rw [max_eq_right (by linarith), max_eq_right (by linarith)]
    linarith
  · simp only [not_exists, not_and, not_lt] at hpos
    have hA0 : ∑ k ∈ X, A.order m k i = 0 :=
      Finset.sum_eq_zero fun k hk => le_antisymm (hpos k hk) (A.order_nonneg m k i)
    rw [hA0, zero_sub, show max (0:ℝ) (-θ) = 0 from max_eq_left (by linarith)]
    have : max 0 (∑ k ∈ X, B.order m k i - θ) ≤ ∑ k ∈ X, B.order m k i :=
      max_le sB0 (by linarith)
    linarith

lemma T_le {N M : ℕ} (A B : OrderNetwork N M) (tier : Fin N → ℕ)
    (hA : IsTiered A tier) (hB : IsTiered B tier) (hDiv : MoreDiversified A B tier)
    (X : Finset (Fin N)) (θ : ℝ)
    (hθA : AssumptionTwoOne A tier θ) (hθB : AssumptionTwoOne B tier θ) (m : ℕ) :
    ∑ j, sigmaSw B X θ m j ≤ ∑ j, sigmaSw A X θ m j := by
  have h := Finset.sum_le_sum
    (fun i (_ : i ∈ Finset.univ) => pt_le A B tier hA hDiv X θ hθA hθB m i)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at h
  have hs := colsum_eq A B tier hA hB hDiv X m
  linarith

end P118

open DisruptReroute.Resil in
theorem solution {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (R : RiskData N M) (A B : OrderNetwork N M) (tier : Fin N → ℕ)
    (hA : IsTiered A tier) (hB : IsTiered B tier)
    (hDiv : MoreDiversified A B tier) :
    MoreResilient R B A tier := by
  intro c θ hθA hθB
  have hD : ∀ y, D0 R A c y = D0 R B c y := fun y => P118.D0_eq R A B tier hA hB hDiv c y
  unfold zeta
  rw [P118.sum_zetaI R A c 0, P118.sum_zetaI R B c 0, P118.sum_zetaI R A c θ, P118.sum_zetaI R B c θ,
    hD 0, hD θ]
  have h0 : ∀ m, ∑ j, sigmaSw A (D0 R B c 0) 0 m j = ∑ j, sigmaSw B (D0 R B c 0) 0 m j :=
    fun m => P118.T0_eq A B tier hA hB hDiv _ m
  simp only [h0]
  have hS : ∑ m ∈ Finset.Icc 1 M, ((∑ i, θ * R.holding m i) +
        (∑ j, sigmaSw B (D0 R B c θ) θ m j) *
          R.sInv m (∑ j, sigmaSw B (D0 R B c θ) θ m j)) ≤
      ∑ m ∈ Finset.Icc 1 M, ((∑ i, θ * R.holding m i) +
        (∑ j, sigmaSw A (D0 R B c θ) θ m j) *
          R.sInv m (∑ j, sigmaSw A (D0 R B c θ) θ m j)) := by
    refine Finset.sum_le_sum fun m hm => ?_
    have hle := P118.T_le A B tier hA hB hDiv (D0 R B c θ) θ hθA hθB m
    have h0B := P118.T_nonneg B (D0 R B c θ) θ m
    have h0A := P118.T_nonneg A (D0 R B c θ) θ m
    have hmono := R.sInv_monotone m hm (Set.mem_Ici.mpr h0B) (Set.mem_Ici.mpr h0A) hle
    have hnn := R.sInv_nonneg m hm _ h0B
    have := mul_le_mul hle hmono hnn h0A
    linarith
  have hS0 : 0 ≤ ∑ m ∈ Finset.Icc 1 M, ((∑ i, (0:ℝ) * R.holding m i) +
        (∑ j, sigmaSw B (D0 R B c 0) 0 m j) *
          R.sInv m (∑ j, sigmaSw B (D0 R B c 0) 0 m j)) := by
    refine Finset.sum_nonneg fun m hm => ?_
    have h0B := P118.T_nonneg B (D0 R B c 0) 0 m
    have hnn := R.sInv_nonneg m hm _ h0B
    simp only [zero_mul, Finset.sum_const_zero, zero_add]
    exact mul_nonneg h0B hnn
  exact div_le_div_of_nonneg_right (by linarith) hS0
