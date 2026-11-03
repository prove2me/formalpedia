-- Prove2me | solution 1 for GGHRSW.ColoredMatrix.consistent_display
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T20:23:31.306074+00:00
-- url     : https://prove2.me/submissions/b9aeae82-0bbd-4447-a2ba-86a84358229f

import Mathlib

set_option autoImplicit false
open Classical
open Matrix

section ConsistentDisplayHelpers

private abbrev V (p : ℕ) := Fin 5 → ZMod p

private theorem card_V (p : ℕ) [Fact p.Prime] : Fintype.card (V p) = p ^ 5 := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  simp [V]

private theorem card_dotProduct_eq_zero_of_eq (p : ℕ) [Fact p.Prime]
    (v : V p) (hv : v ≠ 0) (a : ZMod p) :
    (Finset.univ.filter fun u : V p => u ⬝ᵥ v = a).card =
      (Finset.univ.filter fun u : V p => u ⬝ᵥ v = 0).card := by
  have hne : ∃ i₀ : Fin 5, v i₀ ≠ 0 := by
    by_contra! h
    apply hv
    ext i
    exact h i
  rcases hne with ⟨i₀, hi₀⟩
  let δ : V p := Pi.single i₀ (a * (v i₀)⁻¹)
  have hδ : δ ⬝ᵥ v = a := by
    simp [δ, single_dotProduct, mul_assoc, inv_mul_cancel₀ hi₀]
  refine Finset.card_bij (fun u _ => u - δ) ?_ ?_ ?_
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    rw [sub_dotProduct, hu, hδ, sub_self]
  · intro u₁ _ u₂ _ h
    exact sub_left_inj.mp h
  · intro u hu
    refine ⟨u + δ, ?_, add_sub_cancel_right u δ⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    rw [add_dotProduct, hu, hδ, zero_add]

private theorem card_dotProduct_eq (p : ℕ) [Fact p.Prime]
    (v : V p) (hv : v ≠ 0) (a : ZMod p) :
    (Finset.univ.filter fun u : V p => u ⬝ᵥ v = a).card = p ^ 4 := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hsum : ∑ b : ZMod p, (Finset.univ.filter fun u : V p => u ⬝ᵥ v = b).card =
      (Finset.univ : Finset (V p)).card := by
    simpa using (Finset.card_eq_sum_card_fiberwise
      (f := fun u : V p => u ⬝ᵥ v) (s := Finset.univ) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)).symm
  have hconst : ∑ b : ZMod p, (Finset.univ.filter fun u : V p => u ⬝ᵥ v = b).card =
      p * (Finset.univ.filter fun u : V p => u ⬝ᵥ v = 0).card := by
    rw [Finset.sum_congr rfl fun b _ => card_dotProduct_eq_zero_of_eq p v hv b]
    simp [Finset.sum_const, ZMod.card]
  have hcard : (Finset.univ : Finset (V p)).card = p * p ^ 4 := by
    rw [Finset.card_univ, card_V p]
    ring
  have h0 : (Finset.univ.filter fun u : V p => u ⬝ᵥ v = 0).card = p ^ 4 := by
    apply Nat.eq_of_mul_eq_mul_left (Fact.out : p.Prime).pos
    linarith
  rw [card_dotProduct_eq_zero_of_eq p v hv a, h0]

private theorem card_dotProduct_zero_vec (p : ℕ) [Fact p.Prime] (a : ZMod p) :
    (Finset.univ.filter fun u : V p => u ⬝ᵥ (0 : V p) = a).card =
      if a = 0 then p ^ 5 else 0 := by
  simp only [dotProduct_zero]
  split_ifs with ha
  · subst ha
    simp [card_V p]
  · have : (Finset.univ.filter fun _ : V p => (0 : ZMod p) = a) = ∅ := by
      ext u
      simp [Ne.symm ha]
    rw [this, Finset.card_empty]

private theorem card_pair_dotProduct_eq (p : ℕ) [Fact p.Prime] (a : ZMod p) :
    (Finset.univ.filter fun y : V p × V p => a = y.1 ⬝ᵥ y.2).card =
      (p ^ 5 - 1) * p ^ 4 + (if a = 0 then p ^ 5 else 0) := by
  have heq : (Finset.univ.filter fun y : V p × V p => a = y.1 ⬝ᵥ y.2).card =
      ∑ b : V p, (Finset.univ.filter fun u : V p => u ⬝ᵥ b = a).card := by
    simp only [Finset.card_filter, eq_comm (a := a)]
    exact Fintype.sum_prod_type_right _
  rw [heq, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : V p))]
  rw [card_dotProduct_zero_vec p a]
  have hsum : ∑ b ∈ Finset.univ.erase (0 : V p),
      (Finset.univ.filter fun u : V p => u ⬝ᵥ b = a).card = (p ^ 5 - 1) * p ^ 4 := by
    have hcongr : ∀ b ∈ Finset.univ.erase (0 : V p),
        (Finset.univ.filter fun u : V p => u ⬝ᵥ b = a).card = p ^ 4 := by
      intro b hb
      exact card_dotProduct_eq p b (Finset.ne_of_mem_erase hb) a
    rw [Finset.sum_congr rfl hcongr, Finset.sum_const,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, card_V p, smul_eq_mul]
  omega

private theorem card_quad_filter (p : ℕ) [Fact p.Prime] (Q : V p × V p → Prop) :
    (Finset.univ.filter fun x : V p × V p × V p × V p =>
      x.1 ⬝ᵥ x.2.1 = x.2.2.1 ⬝ᵥ x.2.2.2 ∧ Q (x.1, x.2.1)).card =
      (Finset.univ.filter Q).card * ((p ^ 5 - 1) * p ^ 4) +
        (Finset.univ.filter fun y : V p × V p => Q y ∧ y.1 ⬝ᵥ y.2 = 0).card * p ^ 5 := by
  have hsplit : (Finset.univ.filter fun x : V p × V p × V p × V p =>
      x.1 ⬝ᵥ x.2.1 = x.2.2.1 ⬝ᵥ x.2.2.2 ∧ Q (x.1, x.2.1)).card =
      ∑ y : V p × V p, (Finset.univ.filter fun z : V p × V p =>
        y.1 ⬝ᵥ y.2 = z.1 ⬝ᵥ z.2 ∧ Q y).card := by
    simp only [Finset.card_filter]
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun s _ => ?_
    exact Fintype.sum_prod_type _
  rw [hsplit]
  have h1 : ∀ y : V p × V p,
      (Finset.univ.filter fun z : V p × V p => y.1 ⬝ᵥ y.2 = z.1 ⬝ᵥ z.2 ∧ Q y).card =
        (if Q y then (p ^ 5 - 1) * p ^ 4 else 0) +
          (if Q y ∧ y.1 ⬝ᵥ y.2 = 0 then p ^ 5 else 0) := by
    intro y
    by_cases hQ : Q y
    · simp only [hQ, and_true, true_and, ↓reduceIte]
      exact card_pair_dotProduct_eq p (y.1 ⬝ᵥ y.2)
    · simp [hQ]
  simp_rw [h1, Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_const, smul_eq_mul]

private theorem permMatrix_mulVec_apply (p : ℕ) (P : Equiv.Perm (Fin 5)) (t : V p) (i : Fin 5) :
    (P.permMatrix (ZMod p) *ᵥ t) i = t (P i) := by
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, mulVec, dotProduct]

private theorem card_w_zero_bounds (p : ℕ) [Fact p.Prime] (P : Equiv.Perm (Fin 5)) (hP : P ≠ 1)
    (c c' : ZMod p) (hc : ¬(c = 0 ∧ c' = 0)) :
    let w : V p → V p := fun t => c' • t + c • (P.permMatrix (ZMod p) *ᵥ t)
    1 ≤ (Finset.univ.filter fun t : V p => w t = 0).card ∧
      (Finset.univ.filter fun t : V p => w t = 0).card ≤ p ^ 4 := by
  intro w
  constructor
  · refine Finset.card_pos.mpr ⟨0, ?_⟩
    simp [w]
  · have hPi : ∃ i₀ : Fin 5, P i₀ ≠ i₀ := by
      by_contra! h
      apply hP
      exact Equiv.ext h
    rcases hPi with ⟨i₀, hi₀⟩
    let v₀ : V p := c' • Pi.single i₀ 1 + c • Pi.single (P i₀) 1
    have hv₀ : v₀ ≠ 0 := by
      intro h0
      apply hc
      have h1 : v₀ i₀ = 0 := congrFun h0 i₀
      have h2 : v₀ (P i₀) = 0 := congrFun h0 (P i₀)
      simp only [v₀, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same,
        Pi.single_eq_of_ne hi₀, Pi.single_eq_of_ne (Ne.symm hi₀),
        smul_eq_mul, mul_one, mul_zero, add_zero, zero_add] at h1 h2
      exact ⟨h2, h1⟩
    have hsub : (Finset.univ.filter fun t : V p => w t = 0) ⊆
        Finset.univ.filter fun t : V p => t ⬝ᵥ v₀ = 0 := by
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      have hti : w t i₀ = 0 := congrFun ht i₀
      simp only [w, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        permMatrix_mulVec_apply] at hti
      simp only [v₀, dotProduct_add, dotProduct_smul, dotProduct_single,
        smul_eq_mul, mul_one]
      exact hti
    exact (Finset.card_le_card hsub).trans (le_of_eq (card_dotProduct_eq p v₀ hv₀ 0))

private theorem card_M2_eq (p : ℕ) [Fact p.Prime] (w : V p → V p) :
    (Finset.univ.filter fun y : V p × V p => y.1 ⬝ᵥ w y.2 = 0).card =
      (Finset.univ.filter fun t : V p => w t = 0).card * p ^ 5 +
        (p ^ 5 - (Finset.univ.filter fun t : V p => w t = 0).card) * p ^ 4 := by
  have hsplit : (Finset.univ.filter fun y : V p × V p => y.1 ⬝ᵥ w y.2 = 0).card =
      ∑ t : V p, (Finset.univ.filter fun s : V p => s ⬝ᵥ w t = 0).card := by
    simp only [Finset.card_filter]
    exact Fintype.sum_prod_type_right _
  rw [hsplit]
  have h1 : ∀ t ∈ (Finset.univ : Finset (V p)),
      (Finset.univ.filter fun s : V p => s ⬝ᵥ w t = 0).card =
        if w t = 0 then p ^ 5 else p ^ 4 := by
    intro t _
    by_cases hwt : w t = 0
    · have heq : (Finset.univ.filter fun s : V p => s ⬝ᵥ w t = 0) = Finset.univ := by
        ext s; simp [hwt]
      rw [heq, if_pos hwt, Finset.card_univ, card_V p]
    · rw [if_neg hwt]
      convert card_dotProduct_eq p (w t) hwt 0
  rw [Finset.sum_congr rfl h1, Finset.sum_ite, Finset.sum_const, Finset.sum_const,
    smul_eq_mul, smul_eq_mul]
  have hnot : (Finset.univ.filter fun t : V p => ¬w t = 0).card =
      p ^ 5 - (Finset.univ.filter fun t : V p => w t = 0).card := by
    have := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (p := fun t : V p => w t = 0)
    rw [Finset.card_univ, card_V p] at this
    omega
  rw [hnot]

end ConsistentDisplayHelpers

theorem solution (p : ℕ) [Fact p.Prime] (P : Equiv.Perm (Fin 5)) (hP : P ≠ 1)
    (c c' : ZMod p) (hc : ¬(c = 0 ∧ c' = 0)) :
    let S := Finset.univ.filter fun x :
        (Fin 5 → ZMod p) × (Fin 5 → ZMod p) × (Fin 5 → ZMod p) × (Fin 5 → ZMod p) =>
      x.1 ⬝ᵥ x.2.1 = x.2.2.1 ⬝ᵥ x.2.2.2
    let E := S.filter fun x =>
      c' * (x.2.2.1 ⬝ᵥ x.2.2.2) + c * (x.1 ⬝ᵥ (P.permMatrix (ZMod p) *ᵥ x.2.1)) = 0
    1 / (p : ℝ) < (E.card : ℝ) / S.card ∧ (E.card : ℝ) / S.card < 2 / (p : ℝ) := by
  intro S E
  let w : V p → V p := fun t => c' • t + c • (P.permMatrix (ZMod p) *ᵥ t)
  let Q_E : V p × V p → Prop := fun y => y.1 ⬝ᵥ w y.2 = 0
  have hE_eq : E = Finset.univ.filter fun x : V p × V p × V p × V p =>
      x.1 ⬝ᵥ x.2.1 = x.2.2.1 ⬝ᵥ x.2.2.2 ∧ Q_E (x.1, x.2.1) := by
    ext x
    simp only [E, S, Q_E, w, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul, h1]
      exact h2
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul, h1] at h2
      exact h2
  have hScard : S.card =
      p ^ 10 * ((p ^ 5 - 1) * p ^ 4) + ((p ^ 5 - 1) * p ^ 4 + p ^ 5) * p ^ 5 := by
    let QT : V p × V p → Prop := fun _ => True
    have hq := card_quad_filter p QT
    have h1 : S.card = (Finset.univ.filter fun x : V p × V p × V p × V p =>
        x.1 ⬝ᵥ x.2.1 = x.2.2.1 ⬝ᵥ x.2.2.2 ∧ QT (x.1, x.2.1)).card := by
      congr 1; ext x; simp [S, QT]
    have h2 : (Finset.univ.filter QT).card = p ^ 10 := by
      have : Finset.univ.filter QT = Finset.univ := by ext y; simp [QT]
      rw [this, Finset.card_univ, Fintype.card_prod, card_V p]
      ring
    have h3 : (Finset.univ.filter fun y : V p × V p => QT y ∧ y.1 ⬝ᵥ y.2 = 0).card =
        (p ^ 5 - 1) * p ^ 4 + p ^ 5 := by
      have : (Finset.univ.filter fun y : V p × V p => QT y ∧ y.1 ⬝ᵥ y.2 = 0) =
          Finset.univ.filter fun y : V p × V p => (0 : ZMod p) = y.1 ⬝ᵥ y.2 := by
        ext y; simp [QT, eq_comm]
      rw [this, card_pair_dotProduct_eq p 0]
      simp
    refine (?_ : S.card = _).trans (hq.trans ?_)
    · convert h1
    · congr 2
      · convert h2
      · congr 1
        convert h3
  have hEcard : E.card =
      (Finset.univ.filter Q_E).card * ((p ^ 5 - 1) * p ^ 4) +
        (Finset.univ.filter fun y : V p × V p => Q_E y ∧ y.1 ⬝ᵥ y.2 = 0).card * p ^ 5 := by
    rw [hE_eq]
    convert card_quad_filter p Q_E
  have hK := card_w_zero_bounds p P hP c c' hc
  set K := (Finset.univ.filter fun t : V p => w t = 0).card
  have hM2 : (Finset.univ.filter Q_E).card = K * p ^ 5 + (p ^ 5 - K) * p ^ 4 :=
    card_M2_eq p w
  set M12 := (Finset.univ.filter fun y : V p × V p => Q_E y ∧ y.1 ⬝ᵥ y.2 = 0).card
  have hM12_ge : p ^ 5 ≤ M12 := by
    have hinj : Function.Injective (fun s : V p => (s, (0 : V p))) := fun s₁ s₂ h =>
      congrArg Prod.fst h
    have hsub : (Finset.univ : Finset (V p)).map ⟨fun s => (s, (0 : V p)), hinj⟩ ⊆
        Finset.univ.filter fun y : V p × V p => Q_E y ∧ y.1 ⬝ᵥ y.2 = 0 := by
      intro y hy
      simp only [Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk, true_and] at hy
      rcases hy with ⟨s, rfl⟩
      simp [Q_E, w]
    have hle := Finset.card_le_card hsub
    simpa [card_V p] using hle
  have hM12_le : M12 ≤ (p ^ 5 - 1) * p ^ 4 + p ^ 5 := by
    have hsub : (Finset.univ.filter fun y : V p × V p => Q_E y ∧ y.1 ⬝ᵥ y.2 = 0) ⊆
        Finset.univ.filter fun y : V p × V p => (0 : ZMod p) = y.1 ⬝ᵥ y.2 := by
      intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      exact hy.2.symm
    have hle := Finset.card_le_card hsub
    rw [card_pair_dotProduct_eq p 0] at hle
    simpa using hle
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hp5 : 1 ≤ p ^ 5 := Nat.one_le_pow 5 p (by omega)
  have hK1 : 1 ≤ K := hK.1
  have hK2 : K ≤ p ^ 4 := hK.2
  have hK5 : K ≤ p ^ 5 := hK2.trans (Nat.pow_le_pow_right (by omega) (by decide))
  have hq2 : (2 : ℤ) ≤ p := by exact_mod_cast hp2
  have hK1_z : 1 ≤ (K : ℤ) := by exact_mod_cast hK1
  have hK2_z : (K : ℤ) ≤ (p : ℤ) ^ 4 := by exact_mod_cast hK2
  have hM12_ge_z : (p : ℤ) ^ 5 ≤ (M12 : ℤ) := by exact_mod_cast hM12_ge
  have hM12_le_z : (M12 : ℤ) ≤ ((p : ℤ) ^ 5 - 1) * (p : ℤ) ^ 4 + (p : ℤ) ^ 5 := by
    zify [hp5] at hM12_le
    exact hM12_le
  have hS_int : (S.card : ℤ) =
      (p : ℤ) ^ 10 * (((p : ℤ) ^ 5 - 1) * (p : ℤ) ^ 4) +
        (((p : ℤ) ^ 5 - 1) * (p : ℤ) ^ 4 + (p : ℤ) ^ 5) * (p : ℤ) ^ 5 := by
    zify [hp5] at hScard
    exact hScard
  have hE_int : (E.card : ℤ) =
      ((K : ℤ) * (p : ℤ) ^ 5 + ((p : ℤ) ^ 5 - (K : ℤ)) * (p : ℤ) ^ 4) *
        (((p : ℤ) ^ 5 - 1) * (p : ℤ) ^ 4) + (M12 : ℤ) * (p : ℤ) ^ 5 := by
    rw [hM2] at hEcard
    zify [hp5, hK5] at hEcard
    exact hEcard
  have hq5_pos : 0 ≤ (p : ℤ) ^ 5 - 1 := by
    have : (1 : ℤ) ≤ (p : ℤ) ^ 5 := by exact_mod_cast hp5
    linarith
  have hE_lo : S.card < p * E.card := by
    have hid_lo : (p : ℤ) * (E.card : ℤ) - (S.card : ℤ) =
        ((K : ℤ) - 1) * ((p : ℤ) - 1) * ((p : ℤ) ^ 5 - 1) * (p : ℤ) ^ 9 +
          ((M12 : ℤ) - (p : ℤ) ^ 5) * (p : ℤ) ^ 6 +
          ((p : ℤ) - 2) * (p : ℤ) ^ 14 + ((p : ℤ) - 2) * (p : ℤ) ^ 10 + 2 * (p : ℤ) ^ 9 := by
      rw [hE_int, hS_int]
      ring
    have hK_sub : 0 ≤ (K : ℤ) - 1 := by linarith
    have hq_sub1 : 0 ≤ (p : ℤ) - 1 := by linarith
    have hq_sub2 : 0 ≤ (p : ℤ) - 2 := by linarith
    have hM_sub : 0 ≤ (M12 : ℤ) - (p : ℤ) ^ 5 := by linarith
    have hq_pos : 0 < (p : ℤ) := by linarith
    have hdiff_pos : 0 < (p : ℤ) * (E.card : ℤ) - (S.card : ℤ) := by
      rw [hid_lo]
      positivity
    have : (S.card : ℤ) < (p : ℤ) * (E.card : ℤ) := by linarith
    exact_mod_cast this
  have hE_hi : p * E.card < 2 * S.card := by
    have hid_hi : 2 * (S.card : ℤ) - (p : ℤ) * (E.card : ℤ) =
        ((p : ℤ) ^ 4 - (K : ℤ)) * ((p : ℤ) - 1) * ((p : ℤ) ^ 5 - 1) * (p : ℤ) ^ 9 +
          (((p : ℤ) ^ 5 - 1) * (p : ℤ) ^ 4 + (p : ℤ) ^ 5 - (M12 : ℤ)) * (p : ℤ) ^ 6 +
          (((p : ℤ) - 2) * ((p : ℤ) ^ 2 + 2 * (p : ℤ) + 4) + 6) * (p : ℤ) ^ 15 +
          ((p : ℤ) - 1) * ((p : ℤ) + 1) * (p : ℤ) ^ 13 +
          2 * ((p : ℤ) - 1) * ((p : ℤ) ^ 2 + (p : ℤ) + 1) * (p : ℤ) ^ 11 +
          (((p : ℤ) - 1) * ((p : ℤ) + 4) + 2) * (p : ℤ) ^ 9 := by
      rw [hE_int, hS_int]
      ring
    have hK_up : 0 ≤ (p : ℤ) ^ 4 - (K : ℤ) := by linarith
    have hq_sub1 : 0 ≤ (p : ℤ) - 1 := by linarith
    have hq_sub2 : 0 ≤ (p : ℤ) - 2 := by linarith
    have hM_up : 0 ≤ ((p : ℤ) ^ 5 - 1) * (p : ℤ) ^ 4 + (p : ℤ) ^ 5 - (M12 : ℤ) := by linarith
    have hq_pos : 0 < (p : ℤ) := by linarith
    have hdiff_pos : 0 < 2 * (S.card : ℤ) - (p : ℤ) * (E.card : ℤ) := by
      rw [hid_hi]
      positivity
    have : (p : ℤ) * (E.card : ℤ) < 2 * (S.card : ℤ) := by linarith
    exact_mod_cast this
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hS_pos : (0 : ℝ) < S.card := by
    have : 0 < S.card := by omega
    exact_mod_cast this
  constructor
  · rw [div_lt_div_iff₀ hp_pos hS_pos]
    have hE_lo_r : (S.card : ℝ) < (p : ℝ) * (E.card : ℝ) := by exact_mod_cast hE_lo
    linarith
  · rw [div_lt_div_iff₀ hS_pos hp_pos]
    have hE_hi_r : (p : ℝ) * (E.card : ℝ) < 2 * (S.card : ℝ) := by exact_mod_cast hE_hi
    linarith
