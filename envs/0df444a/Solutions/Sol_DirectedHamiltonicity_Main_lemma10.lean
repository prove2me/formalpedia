-- Prove2me | solution 1 for DirectedHamiltonicity.Main.lemma10
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-26T06:46:20.167117+00:00
-- url     : https://prove2.me/submissions/201b3149-8106-46ac-bbb1-8dd4e33f2c15

import Definitions.Def_DirectedHamiltonicity_Main_DetSum

open DirectedHamiltonicity.Main DirectedHamiltonicity.Main.Multidigraph
open scoped BigOperators

namespace DHCExpectedCount

abbrev Bit := ZMod 2

private noncomputable def bits {A : Type} [Fintype A] : Finset A ≃ (A → Bit) := by
  classical
  exact {
    toFun := fun S j => if j ∈ S then 1 else 0
    invFun := fun x => Finset.univ.filter (fun j => x j = 1)
    left_inv := fun S => by ext j; by_cases h : j ∈ S <;> simp [h]
    right_inv := fun x => by
      funext j
      have all_bits (y : Bit) : y = 0 ∨ y = 1 := by decide +revert
      have h := all_bits (x j)
      rcases h with h | h <;> simp [h] }

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

private theorem aug_coeff (R : Choices H w s t) (i : Internal s t)
    (b : H.incomingWeights w i.1) :
    (∑ e : H.AugArc w s t R, if e.1.1 = i.1 then
      (Polynomial.X : Polynomial Bit) ^ (e.2.1 : ℕ) else 0).coeff b.1 = bits (R i) b := by
  classical
  rw [Fintype.sum_sigma, Finset.sum_eq_single i]
  · simp only [if_true, Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow]
    change (∑ v : R i, if b.1 = v.1.1 then (1 : Bit) else 0) = _
    simp only [← Subtype.ext_iff]
    by_cases hb : b ∈ R i
    · let j : R i := ⟨b, hb⟩
      rw [Finset.sum_eq_single j]
      · simp [j, bits, hb]
      · intro k _ hkj
        exact if_neg (fun h => hkj (Subtype.ext h.symm))
      · simp
    · rw [Finset.sum_eq_zero]
      · simp [bits, hb]
      · intro k _
        have hne : b ≠ k.1 := fun h => hb (h.symm ▸ k.2)
        simp [hne]
  · intro j _ hj
    have hji : j.1 ≠ i.1 := fun h => hj (Subtype.ext h)
    simp [hji]
  · simp

/-- Adding the arcs indexed by R translates the diagonal by the indicator of R. -/
private theorem diag_shift (X : Finset (Internal s t)) (R : Choices H w s t)
    (i : Internal s t) (b : H.incomingWeights w i.1) :
    H.diagCoeffs w s t X R i b =
      H.diagCoeffs w s t X (fun _ => ∅) i b + bits (R i) b := by
  classical
  simp only [diagCoeffs, augLaplacian, reducedLaplacian, Matrix.submatrix_apply, laplacian,
    if_true, Finset.sum_filter, Fintype.sum_sum_type, subXR, addArcs, subXRLabel,
    Sum.elim_inl, Sum.elim_inr, augGraph, Polynomial.coeff_add]
  rw [add_assoc]
  apply congrArg (_ + ·)
  calc
    _ = bits (R i) b := by
      convert! aug_coeff H w s t R i b using 1
      apply congrArg (fun p : Polynomial Bit => p.coeff b.1)
      apply Finset.sum_congr (by ext; simp)
      intro e _
      by_cases hj : e.1.1 = i.1 <;> simp [hj]
    _ = _ := by
      have he := aug_coeff H w s t (fun _ => ∅) i b
      rw [show bits (∅ : Finset (H.incomingWeights w i.1)) b = 0 by simp [bits]] at he
      symm
      apply add_eq_right.mpr
      convert! he using 1
      apply congrArg (fun p : Polynomial Bit => p.coeff b.1)
      apply Finset.sum_congr (by ext; simp)
      intro e _
      exact (Finset.notMem_empty e.2.1 e.2.2).elim

/-- Encode a pair (R,X) by the indicator of X and the translated diagonal bits. -/
private noncomputable def encode {I : Type} [Fintype I] {W : I → Type}
    [∀ i, Fintype (W i)] (offset : Finset I → (i : I) → W i → Bit) :
    ((∀ i, Finset (W i)) × Finset I) ≃ ((i : I) → Option (W i) → Bit) where
  toFun p i := fun j => j.elim (bits p.2 i) (fun b => offset p.2 i b + bits (p.1 i) b)
  invFun u :=
    let X := bits.symm (fun i => u i none)
    (fun i => bits.symm (fun b => u i (some b) - offset X i b), X)
  left_inv := by
    rintro ⟨R, X⟩
    simp
  right_inv := by
    intro u
    funext i j
    cases j <;> simp

end DHCExpectedCount

open DHCExpectedCount

set_option maxHeartbeats 800000 in
theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (H : Multidigraph V E) (w : E → ℕ) (s t : V) (_hst : s ≠ t) (_hnorm : H.IsNormalized w s t)
    (a : H.NonzeroCoeffs w s t) :
    (∑ R : (i : Internal s t) → Finset (H.incomingWeights w i.1),
        ((H.sampled w s t (fun i => (a i).1) R).card : ℝ)) /
      (Fintype.card ((i : Internal s t) → Finset (H.incomingWeights w i.1)) : ℝ) = 1 := by
  classical
  let offset := fun X => H.diagCoeffs w s t X (fun _ => ∅)
  let P := fun (R : Choices H w s t) (X : Finset (Internal s t)) =>
    X ∈ H.sampled w s t (fun i => (a i).1) R
  -- Reindex successful pairs by a tuple of independent affine-hyperplane points.
  let e : (Σ R : Choices H w s t, {X // P R X}) ≃ ((i : Internal s t) → Row (a i).1) :=
    (Equiv.subtypeProdEquivSigmaSubtype P).symm.trans <|
      ((encode offset).subtypeEquiv (q := fun u => ∀ i, (a i).1 ⬝ᵥ u i = 1) (by
        rintro ⟨R, X⟩
        simp only [P, sampled, Finset.mem_filter, Finset.mem_univ, true_and]
        apply forall_congr'
        intro i
        simp only [encode, Equiv.coe_fn_mk, dotProduct, Fintype.sum_option, Option.elim_none, Option.elim_some]
        simp only [offset]
        rw [show H.diagCoeffs w s t X R i = _ from funext (diag_shift H w s t X R i)]
        by_cases hi : i ∈ X <;> simp [bits, hi])).trans
      (Equiv.subtypePiEquivPi (p := fun i u => (a i).1 ⬝ᵥ u = 1))
  have hc := Fintype.card_congr e
  have hrow (i : Internal s t) := row_card (a i).1 (a i).2
  simp only [Fintype.card_sigma, Fintype.card_pi] at hc
  have hn : (∑ R : Choices H w s t, (H.sampled w s t (fun i => (a i).1) R).card) =
      Fintype.card (Choices H w s t) := by
    calc
      _ = ∏ i, Fintype.card (Row (a i).1) := by simpa [P] using hc
      _ = _ := by
        rw [Fintype.card_pi]
        apply Finset.prod_congr rfl
        intro i _
        simpa only [← Nat.card_eq_fintype_card] using hrow i
  have hpos : 0 < Fintype.card (Choices H w s t) := Fintype.card_pos
  apply (div_eq_iff (by exact_mod_cast hpos.ne')).2
  rw [one_mul]
  exact_mod_cast hn

