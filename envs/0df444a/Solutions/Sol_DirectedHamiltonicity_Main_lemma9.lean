-- Prove2me | solution 1 for DirectedHamiltonicity.Main.lemma9
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-26T06:46:18.310798+00:00
-- url     : https://prove2.me/submissions/436e9903-e78a-4b05-b005-441553a7d5e0

import Definitions.Def_DirectedHamiltonicity_Main_DetSum

open DirectedHamiltonicity.Main DirectedHamiltonicity.Main.Multidigraph
open scoped BigOperators

namespace DHCSampling

private abbrev Bit := ZMod 2

private abbrev Row {W : Type} [Fintype W] (a : Option W → Bit) :=
  {u : Option W → Bit // a ⬝ᵥ u = 1}

open Classical in
/-- The fiber at one of a nonzero linear form is a translate of its kernel. -/
private theorem row_card {W : Type} [Fintype W] (a : Option W → Bit) (ha : a ≠ 0) :
    Nat.card (Row a) = Nat.card (Finset W) := by
  classical
  simp only [Nat.card_eq_fintype_card]
  let L : (Option W → Bit) →ₗ[Bit] Bit :=
    { toFun := dotProduct a
      map_add' := dotProduct_add a
      map_smul' := fun c v => dotProduct_smul c a v }
  have hL : L ≠ 0 := by
    intro h
    apply ha
    funext j
    have hh := LinearMap.congr_fun h (Pi.single j 1)
    simpa [L, dotProduct_single_one] using hh
  obtain ⟨v, hv⟩ := (LinearMap.surjective hL) 1
  let e : Row a ≃ LinearMap.ker L :=
    { toFun := fun u => ⟨u.1 - v, by change L (u.1 - v) = 0; rw [map_sub, hv]; exact sub_eq_zero.mpr u.2⟩
      invFun := fun u => ⟨u.1 + v, by change L (u.1 + v) = 1; rw [map_add, hv, LinearMap.mem_ker.mp u.2, zero_add]⟩
      left_inv := fun _ => Subtype.ext (sub_add_cancel _ _)
      right_inv := fun _ => Subtype.ext (add_sub_cancel_right _ _) }
  have hd := Module.Dual.finrank_ker_add_one_of_ne_zero hL
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_option] at hd
  rw [Fintype.card_congr e, Module.card_eq_pow_finrank (K := Bit)]
  simp [Nat.add_right_cancel hd, Bit]


variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
variable (H : Multidigraph V E) (w : E → ℕ) (s t : V)
private abbrev Choices := (i : Internal s t) → Finset (H.incomingWeights w i.1)

open Classical in
private noncomputable def state (X : Finset (Internal s t)) (R : Choices H w s t)
    (i : Internal s t) : H.CoeffVec w i.1 :=
  fun j => j.elim (if i ∈ X then 1 else 0) (H.diagCoeffs w s t X R i)

/-- Every monomial on an arc entering i has its exponent in the original set W_i. -/
private theorem coeff_outside (X : Finset (Internal s t)) (R : Choices H w s t)
    (i : Internal s t) (n : ℕ) (hn : n ∉ H.incomingWeights w i.1) :
    ((H.augLaplacian w s t X R) ⟨i.1, i.2.1⟩ ⟨i.1, i.2.1⟩).coeff n = 0 := by
  classical
  simp only [augLaplacian, reducedLaplacian, Matrix.submatrix_apply, laplacian, if_true,
    Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro e he
  have hh := (Finset.mem_filter.mp he).2
  rcases e with e | ⟨j, b⟩
  · change H.head e.1 = i.1 at hh
    have hb : w e.1 ∈ H.incomingWeights w i.1 := by
      simp only [incomingWeights, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨e.1, hh, rfl⟩
    change ((Polynomial.X : Polynomial Bit) ^ w e.1).coeff n = 0
    have hne : n ≠ w e.1 := fun heq => hn (heq.symm ▸ hb)
    simp [Polynomial.coeff_X_pow, hne]
  · change j.1 = i.1 at hh
    have hji : j = i := Subtype.ext hh
    subst j
    have hb := b.1.2
    change ((Polynomial.X : Polynomial Bit) ^ (b.1 : ℕ)).coeff n = 0
    have hne : n ≠ (b.1 : ℕ) := fun heq => hn (heq.symm ▸ hb)
    simp [Polynomial.coeff_X_pow, hne]

private theorem offdiag_zero {A B : Type} [Fintype B] (G : Multidigraph A B)
    (p : B → Polynomial Bit) {u v : A} (huv : u ≠ v) (ht : ∀ e, G.tail e ≠ u) :
    G.laplacian p u v = 0 := by
  classical
  simp only [laplacian, if_neg huv, neg_eq_zero]
  apply Finset.sum_eq_zero
  intro e he
  exact (ht e (Finset.mem_filter.mp he).2.1).elim

set_option maxHeartbeats 400000 in
private theorem state_ne (X : Finset (Internal s t)) (R : Choices H w s t)
    (hX : X ∈ H.survivors w s t R) (i : Internal s t) : state H w s t X R i ≠ 0 := by
  classical
  let _ : DecidableEq V := Classical.typeDecidableEq V
  intro h
  by_cases hi : i ∈ X
  · simpa [state, hi] using congrFun h none
  · simp only [survivors, Finset.mem_filter, Finset.mem_univ, true_and] at hX
    apply hX i hi
    funext v
    by_cases hv : i.1 = v.1
    · have hv' : v = (⟨i.1, i.2.1⟩ : {x // x ≠ s}) := Subtype.ext hv.symm
      subst v
      apply Polynomial.ext
      intro n
      simp only [Pi.zero_apply, Polynomial.coeff_zero]
      by_cases hn : n ∈ H.incomingWeights w i.1
      · exact congrFun h (some ⟨n,hn⟩)
      · exact coeff_outside H w s t X R i n hn
    · apply offdiag_zero (H.subXR w s t X R) (H.subXRLabel w s t X R) hv
      intro e ht
      rcases e with e | e
      · change H.tail e.1 = i.1 at ht
        have hvtx : H.tail e.1 ≠ s ∧ H.tail e.1 ≠ t := ht.symm ▸ i.2
        exact hi ((show (⟨H.tail e.1, hvtx⟩ : Internal s t) = i from Subtype.ext ht) ▸ e.2 hvtx)
      · exact i.2.2 ht.symm

private abbrev NZ (W : Type) := {u : Option W → Bit // u ≠ 0}

private noncomputable def fiber {W : Type} [Fintype W] (v : Option W → Bit) :
    {a : NZ W // a.1 ⬝ᵥ v = 1} ≃ Row v where
  toFun a := ⟨a.1.1, (dotProduct_comm _ _).trans a.2⟩
  invFun u := ⟨⟨u.1, fun h => by simpa [h] using u.2⟩, (dotProduct_comm _ _).trans u.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem nz_card (W : Type) [Fintype W] : Nat.card (NZ W) = 2 ^ (Fintype.card W + 1) - 1 := by
  classical
  simp [NZ, Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Bit]

private theorem factor (k : ℕ) :
    ((2 : ℝ)^k) / ((2 : ℝ)^(k+1) - 1) = (2 - (1 / 2 : ℝ)^k)⁻¹ := by
  have hk : (1 : ℝ) ≤ 2^k := one_le_pow₀ (by norm_num)
  rw [one_div, inv_pow, pow_succ]
  field_simp

private theorem internal_card (hst : s ≠ t) : Fintype.card (Internal s t) = Fintype.card V - 2 := by
  classical
  have e : Internal s t ≃ {x : V // ¬(x = s ∨ x = t)} :=
    Equiv.subtypeEquivRight (fun x => not_or.symm)
  rw [Fintype.card_congr e, Fintype.card_subtype_compl, Fintype.card_subtype_eq_or_eq_of_ne hst]

end DHCSampling

open DHCSampling

set_option maxHeartbeats 1000000 in
open Classical in
theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (H : Multidigraph V E) (w : E → ℕ) (s t : V) (hst : s ≠ t) (_hnorm : H.IsNormalized w s t)
    (d : ℕ) (_hd : 1 ≤ d) (hdeg : ∀ v, (H.incomingWeights w v).card ≤ d)
    (R : (i : Internal s t) → Finset (H.incomingWeights w i.1))
    (X : Finset (Internal s t)) (hX : X ∈ H.survivors w s t R) :
    ((Finset.univ.filter fun a : H.NonzeroCoeffs w s t =>
          X ∈ H.sampled w s t (fun i => (a i).1) R).card : ℝ) /
        (Fintype.card (H.NonzeroCoeffs w s t) : ℝ) =
      ∏ i : Internal s t, (2 - (1 / 2 : ℝ) ^ (H.incomingWeights w i.1).card)⁻¹ ∧
    ((2 - (1 / 2 : ℝ) ^ d) ^ (Fintype.card V - 2))⁻¹ ≤
      ∏ i : Internal s t, (2 - (1 / 2 : ℝ) ^ (H.incomingWeights w i.1).card)⁻¹ := by
  classical
  let v := state H w s t X R
  let W := fun i : Internal s t => H.incomingWeights w i.1
  let P := fun a : H.NonzeroCoeffs w s t => X ∈ H.sampled w s t (fun i => (a i).1) R
  have hP (a : H.NonzeroCoeffs w s t) : P a ↔ ∀ i, (a i).1 ⬝ᵥ v i = 1 := by
    simp only [P, sampled, Finset.mem_filter, Finset.mem_univ, true_and]
    apply forall_congr'
    intro i
    by_cases hi : i ∈ X <;> simp [v, state, dotProduct, Fintype.sum_option, hi]
  let e : {a // P a} ≃ ((i : Internal s t) → Row (v i)) :=
    (Equiv.subtypeEquivRight hP).trans <|
      (Equiv.subtypePiEquivPi (p := fun i (a : NZ (W i)) => a.1 ⬝ᵥ v i = 1)).trans <|
      Equiv.piCongrRight (fun i => fiber (v i))
  have count : (Finset.univ.filter P).card = ∏ i, 2 ^ (W i).card := by
    rw [← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_pi]
    apply Finset.prod_congr rfl
    intro i _
    have hrow := row_card (v i) (state_ne H w s t X R hX i)
    simpa [Nat.card_eq_fintype_card, W] using hrow
  have total : Fintype.card (H.NonzeroCoeffs w s t) = ∏ i, (2 ^ ((W i).card + 1) - 1) := by
    rw [Fintype.card_pi]
    apply Finset.prod_congr rfl
    intro i _
    simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using nz_card (W i)
  constructor
  · change ((Finset.univ.filter P).card : ℝ) / _ = _
    rw [count, total, Nat.cast_prod, Nat.cast_prod, ← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [Nat.cast_sub (one_le_pow₀ (by norm_num : 1 ≤ (2:ℕ)) (n := (W i).card + 1))]
    push_cast
    exact factor _
  · have hu (k : ℕ) : (1 / 2 : ℝ)^k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    rw [← internal_card s t hst, ← inv_pow, ← Finset.card_univ (α := Internal s t), ← Finset.prod_const]
    apply Finset.prod_le_prod
    · intro i _
      exact inv_nonneg.mpr (by linarith [hu d])
    · intro i _
      have := hu (W i).card
      apply inv_anti₀ (by linarith)
      exact sub_le_sub_left (pow_le_pow_of_le_one (by norm_num) (by norm_num) (hdeg i.1)) _

