-- Prove2me | solution 1 for BipHamCount.Deterministic.lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-26T09:14:56.768494+00:00
-- url     : https://prove2.me/submissions/ae38c3d6-5a11-4370-aecc-60fa5585111b

import Definitions.Def_BipHamCount_Deterministic_Core
import Theorems.Thm_BipHamCount_Deterministic_lemma_2_1

open BipHamCount.Deterministic Finset
open scoped BigOperators Matrix

set_option maxHeartbeats 2000000

private lemma ryser_square {d : ℕ} (M : Matrix (Fin d) (Fin d) ℤ) :
    M.permanent = ∑ X ∈ (univ : Finset (Fin d)).powerset,
      (-1 : ℤ) ^ (d-X.card) * ∏ i, ∑ j ∈ X, M i j := by
  calc
    M.permanent = Mᵀ.permanent := (Matrix.permanent_transpose M).symm
    _ = rectPermanent M := by
      classical
      unfold Matrix.permanent rectPermanent
      congr 1
      ext π; simp
    _ = _ := by simpa only [Fintype.card_fin] using (lemma_2_1 (I := Fin d) (J := Fin d) (R := ℤ) rfl M)

private lemma ordered_ryser {m d : ℕ} (A : Matrix (Fin m) (Fin m) ℤ)
    (S T : Finset (Fin m)) (hs : S.card = d) (ht : T.card = d) :
    (A.submatrix (S.orderEmbOfFin hs) (T.orderEmbOfFin ht)).permanent = ∑ X ∈ T.powerset,
      (-1 : ℤ) ^ (T.card - X.card) * ∏ i ∈ S, ∑ j ∈ X, A i j := by
  classical
  rw [ryser_square]
  let e := T.orderEmbOfFin ht
  have hset : (univ.image e).powerset = T.powerset := by simp [e]
  rw [← hset, powerset_image, sum_image (Finset.image_injective e.injective).injOn]
  refine sum_congr rfl (fun X hX => ?_)
  rw [card_image_of_injective _ e.injective, ht]
  congr 1
  calc
    _ = ∏ i ∈ univ.image (S.orderEmbOfFin hs), ∑ j ∈ X.image e, A i j := by
      rw [prod_image (S.orderEmbOfFin hs).injective.injOn]
      refine prod_congr rfl (fun i hi => ?_)
      rw [sum_image e.injective.injOn]
      rfl
    _ = _ := by rw [image_orderEmbOfFin_univ]

private lemma minor_ryser {m : ℕ} (A : Matrix (Fin m) (Fin m) ℤ)
    (S T : Finset (Fin m)) (hc : T.card = S.card) :
    permMinor A S T = ∑ X ∈ T.powerset,
      (-1 : ℤ) ^ (T.card-X.card) * ∏ i ∈ S, ∑ j ∈ X, A i j := by
  rw [permMinor, dif_pos hc]
  exact ordered_ryser A S T rfl hc

private lemma minor_ryser_col {m : ℕ} (B : Matrix (Fin m) (Fin m) ℤ)
    (S T : Finset (Fin m)) (hc : T.card = S.card) :
    permMinor B T S = ∑ Y ∈ T.powerset,
      (-1 : ℤ) ^ (T.card-Y.card) * ∏ i ∈ S, ∑ j ∈ Y, B j i := by
  rw [permMinor, dif_pos hc.symm, ← Matrix.permanent_transpose]
  exact ordered_ryser Bᵀ S T hc.symm rfl

private lemma sign_product (a b d : ℕ) (ha : a ≤ d) (hb : b ≤ d) :
    (-1 : ℤ)^(d-a) * (-1 : ℤ)^(d-b) = (-1 : ℤ)^(a+b) := by
  rw [← pow_add]
  have hp : Even ((d-a)+(d-b)) ↔ Even (a+b) := by
    simp only [Nat.even_iff]
    omega
  by_cases h : Even (a+b)
  · rw [(hp.mpr h).neg_one_pow, h.neg_one_pow]
  · rw [(Nat.not_even_iff_odd.mp (fun h' => h (hp.mp h'))).neg_one_pow,
      (Nat.not_even_iff_odd.mp h).neg_one_pow]

private noncomputable def summand {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ) (S T X Y : Finset (Fin m)) : ℤ :=
  (-1) ^ (X.card + Y.card) * ((-1) ^ (Sᶜ.card + 1) * minor A Sᶜ Tᶜ * minor B Tᶜ Sᶜ *
    ∏ i ∈ S, w A B X Y i)

private lemma expandTerm {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ)
    (S T : Finset (Fin m)) (hc : T.card = S.card) :
    sigmaTerm A B S T = ∑ X ∈ T.powerset, ∑ Y ∈ T.powerset, summand A B S T X Y := by
  classical
  rw [sigmaTerm, minor_ryser A S T hc, minor_ryser_col B S T hc]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [sum_comm (s := T.powerset) (t := T.powerset)]
  refine sum_congr rfl (fun X hX => ?_)
  refine sum_congr rfl (fun Y hY => ?_)
  have hsign := sign_product X.card Y.card T.card (Finset.card_le_card (mem_powerset.mp hX))
    (Finset.card_le_card (mem_powerset.mp hY))
  unfold summand
  simp only [w, Finset.prod_mul_distrib]
  rw [← hsign]
  ring

theorem solution (m : ℕ) (A B : Matrix (Fin m) (Fin m) ℤ) (v : Fin m) (k : ℕ) :
    sigmaSmall A B v k =
      ∑ X ∈ (Finset.univ : Finset (Fin m)).powerset,
        ∑ Y ∈ Finset.univ.powerset.filter (fun Y : Finset (Fin m) => (X ∪ Y).card ≤ k),
          (-1 : ℤ) ^ (X.card + Y.card) * Fval A B v k X Y := by
  classical
  let SS := (univ.erase v).powerset.filter (fun S => S.card ≤ k)
  let P := (univ : Finset (Fin m)).powerset
  let f := fun S T X Y : Finset (Fin m) =>
    if T.card = S.card ∧ X ⊆ T ∧ Y ⊆ T then summand A B S T X Y else 0
  have powers (T : Finset (Fin m)) : T.powerset = P.filter (· ⊆ T) := by
    ext X
    simp [P]
  have lhs : sigmaSmall A B v k =
      ∑ S ∈ SS, ∑ T ∈ P, ∑ X ∈ P, ∑ Y ∈ P, f S T X Y := by
    unfold sigmaSmall
    refine sum_congr rfl (fun S hS => ?_)
    rw [sum_filter]
    refine sum_congr rfl (fun T hT => ?_)
    by_cases h : T.card = S.card
    · rw [if_pos h, expandTerm A B S T h, powers T, sum_filter]
      refine sum_congr rfl (fun X hX => ?_)
      by_cases hx : X ⊆ T
      · rw [if_pos hx, sum_filter]
        simp only [f, h, hx, true_and]
      · simp [f, hx]
    · simp [h, f]
  rw [lhs]
  calc
    _ = ∑ st ∈ SS ×ˢ P, ∑ xy ∈ P ×ˢ P, f st.1 st.2 xy.1 xy.2 := by
      simp only [sum_product]
    _ = ∑ xy ∈ P ×ˢ P, ∑ st ∈ SS ×ˢ P, f st.1 st.2 xy.1 xy.2 := sum_comm
    _ = ∑ X ∈ P, ∑ Y ∈ P, ∑ S ∈ SS, ∑ T ∈ P, f S T X Y := by
      simp only [sum_product]
    _ = _ := by
      refine sum_congr rfl (fun X hX => ?_)
      rw [sum_filter]
      refine sum_congr rfl (fun Y hY => ?_)
      by_cases hc : (X ∪ Y).card ≤ k
      · rw [if_pos hc, Fval, Finset.mul_sum]
        refine sum_congr rfl (fun S hS => ?_)
        rw [Finset.mul_sum, sum_filter]
        refine sum_congr rfl (fun T hT => ?_)
        by_cases h : T.card = S.card ∧ X ∪ Y ⊆ T
        · obtain ⟨ht, hxy⟩ := h
          have ⟨hx, hy⟩ := union_subset_iff.mp hxy
          simp [f, ht, hx, hy, hxy, summand]
        · have h' : ¬(T.card = S.card ∧ X ⊆ T ∧ Y ⊆ T) := by
            simpa only [union_subset_iff] using h
          simp [f, h, h']
      · rw [if_neg hc]
        apply sum_eq_zero
        intro S hS
        have hsk : S.card ≤ k := (mem_filter.mp hS).2
        apply sum_eq_zero
        intro T hT
        have h : ¬(T.card = S.card ∧ X ⊆ T ∧ Y ⊆ T) := by
          rintro ⟨he,hx,hy⟩
          exact hc ((card_le_card (union_subset hx hy)).trans (he.le.trans hsk))
        simp [f, h]
