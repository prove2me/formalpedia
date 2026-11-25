-- Prove2me | solution 1 for DetDLP.trunc_poly_int_contract_and_uniqueness
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T13:33:27.646531+00:00
-- url     : https://prove2.me/submissions/ea475117-80e1-420a-be7c-e27baf053b82

import Mathlib
import Definitions.Def_DetDLP_BTN

set_option autoImplicit false

open DetDLP

private lemma coeff_sum_fin_monomial {R : Type*} [Semiring R] (ℓ' : ℕ) (f : Fin ℓ' → R)
    (k : ℕ) (hk : k < ℓ') :
    (∑ i : Fin ℓ', Polynomial.monomial i.val (f i)).coeff k = f ⟨k, hk⟩ := by
  rw [Polynomial.finset_sum_coeff]
  rw [Finset.sum_eq_single (⟨k, hk⟩ : Fin ℓ')]
  · simp [Polynomial.coeff_monomial]
  · intro b _ hb
    rw [Polynomial.coeff_monomial]
    have hne : b.val ≠ k := fun h => hb (Fin.ext h)
    simp [hne]
  · intro hmem
    exact (hmem (Finset.mem_univ _)).elim

private lemma truncPolyOfCoeffs_inj (P ℓ' : ℕ) (c₁ c₂ : Fin ℓ' → ℕ)
    (hc₁ : ∀ i, c₁ i < 2 ^ P) (hc₂ : ∀ i, c₂ i < 2 ^ P)
    (heq : truncPolyOfCoeffs P ℓ' c₁ = truncPolyOfCoeffs P ℓ' c₂) :
    c₁ = c₂ := by
  haveI : NeZero (2 ^ P) := ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos P)⟩
  unfold truncPolyOfCoeffs at heq
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton, Polynomial.X_pow_dvd_iff] at heq
  funext i
  have hi := heq i.val i.isLt
  rw [Polynomial.coeff_sub, sub_eq_zero] at hi
  rw [coeff_sum_fin_monomial ℓ' (fun j : Fin ℓ' => (c₁ j : ZMod (2 ^ P))) i.val i.isLt,
      coeff_sum_fin_monomial ℓ' (fun j : Fin ℓ' => (c₂ j : ZMod (2 ^ P))) i.val i.isLt] at hi
  have hval := congrArg ZMod.val hi
  rw [ZMod.val_natCast_of_lt (hc₁ i), ZMod.val_natCast_of_lt (hc₂ i)] at hval
  exact hval

private lemma quotient_map_int_poly_eq_truncPolyOfCoeffs (P ℓ' : ℕ) (Z : Polynomial ℤ) :
    Ideal.Quotient.mk (Ideal.span {(Polynomial.X : Polynomial (ZMod (2 ^ P))) ^ ℓ'})
      (Polynomial.map (Int.castRingHom (ZMod (2 ^ P))) Z) =
    truncPolyOfCoeffs P ℓ' (fun i : Fin ℓ' => ((Z.coeff i.val : ZMod (2 ^ P)).val)) := by
  haveI : NeZero (2 ^ P) := ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos P)⟩
  unfold truncPolyOfCoeffs
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton, Polynomial.X_pow_dvd_iff]
  intro d hd
  rw [Polynomial.coeff_sub,
      coeff_sum_fin_monomial ℓ'
        (fun i : Fin ℓ' => (((Z.coeff i.val : ZMod (2 ^ P)).val : ℕ) : ZMod (2 ^ P))) d hd]
  simp only [Polynomial.coeff_map, Int.coe_castRingHom, ZMod.natCast_zmod_val, sub_self]

theorem solution :
    ∀ (G : BipartiteMultigraph) (P ℓ' : ℕ)
      (A : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Fin ℓ' → ℕ),
      (∀ v t i, A v t i < 2 ^ P) →
      let T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → TruncPoly P ℓ' :=
        fun v t => truncPolyOfCoeffs P ℓ' (A v t)
      let Z : Polynomial ℤ :=
        BTNContract G (fun v t => ∑ i : Fin ℓ', Polynomial.monomial i.val (A v t i : ℤ))
      (∀ v t, EncodesTruncPoly P ℓ' (encodeNatListBin (List.ofFn (A v t))) (T v t)) ∧
      BTNContract G T =
        truncPolyOfCoeffs P ℓ' (fun i : Fin ℓ' => ((Z.coeff i.val : ZMod (2 ^ P)).val)) ∧
      ∀ w : List Bool,
        EncodesTruncPoly P ℓ' w (BTNContract G T) →
        w = encodeNatListBin (List.ofFn fun i : Fin ℓ' => ((Z.coeff i.val : ZMod (2 ^ P)).val)) := by
  intro G P ℓ' A hA
  haveI : NeZero (2 ^ P) := ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos P)⟩
  dsimp only
  let I : Ideal (Polynomial (ZMod (2 ^ P))) :=
    Ideal.span {(Polynomial.X : Polynomial (ZMod (2 ^ P))) ^ ℓ'}
  let φ : Polynomial ℤ →+* TruncPoly P ℓ' :=
    (Ideal.Quotient.mk I).comp (Polynomial.mapRingHom (Int.castRingHom (ZMod (2 ^ P))))
  have hφ_entry : ∀ (v : Fin G.nV) (t : Fin (G.deg v) → Bool),
      φ (∑ i : Fin ℓ', Polynomial.monomial i.val (A v t i : ℤ)) =
        truncPolyOfCoeffs P ℓ' (A v t) := by
    intro v t
    unfold truncPolyOfCoeffs
    change Ideal.Quotient.mk I
      ((Polynomial.mapRingHom (Int.castRingHom (ZMod (2 ^ P))))
        (∑ i : Fin ℓ', Polynomial.monomial i.val (A v t i : ℤ))) = _
    congr 1
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    change Polynomial.map (Int.castRingHom (ZMod (2 ^ P)))
      (Polynomial.monomial i.val (A v t i : ℤ)) = _
    simp [Polynomial.map_monomial]
  have hBTN :
      BTNContract G (fun v t => truncPolyOfCoeffs P ℓ' (A v t)) =
      truncPolyOfCoeffs P ℓ'
        (fun i : Fin ℓ' =>
          (((BTNContract G (fun v t => ∑ i : Fin ℓ', Polynomial.monomial i.val (A v t i : ℤ))).coeff
              i.val : ZMod (2 ^ P)).val)) := by
    have hmap :
        φ (BTNContract G (fun v t => ∑ i : Fin ℓ', Polynomial.monomial i.val (A v t i : ℤ))) =
        BTNContract G (fun v t => truncPolyOfCoeffs P ℓ' (A v t)) := by
      unfold BTNContract
      rw [map_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [map_prod]
      refine Finset.prod_congr rfl fun v _ => ?_
      exact hφ_entry v (fun i => x ((G.ports v).get i))
    rw [← hmap]
    exact quotient_map_int_poly_eq_truncPolyOfCoeffs P ℓ'
      (BTNContract G (fun v t => ∑ i : Fin ℓ', Polynomial.monomial i.val (A v t i : ℤ)))
  refine ⟨fun v t => ⟨A v t, hA v t, rfl, rfl⟩, hBTN, ?_⟩
  intro w hw
  rcases hw with ⟨c, hc, rfl, hceq⟩
  rw [hBTN] at hceq
  have hce :
      c = fun i : Fin ℓ' =>
        (((BTNContract G (fun v t => ∑ i : Fin ℓ', Polynomial.monomial i.val (A v t i : ℤ))).coeff
            i.val : ZMod (2 ^ P)).val) :=
    (truncPolyOfCoeffs_inj P ℓ' _ c (fun _ => ZMod.val_lt _) hc hceq).symm
  rw [hce]
