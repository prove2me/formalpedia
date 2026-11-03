-- Prove2me | solution 1 for GGHRSW.ColoredMatrix.observation_4_2a
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T20:09:04.781185+00:00
-- url     : https://prove2.me/submissions/8c7e770e-d2a3-44d1-8452-aea0b3f16c60

import Mathlib
import Definitions.Def_GGHRSW_ColoredMatrix_Model

set_option autoImplicit false
open Matrix GGHRSW.ColoredMatrix

section BookendHelpers

variable {p : ℕ}

private theorem tele_prod {R : Type*} [Monoid R] (n : ℕ) :
    ∀ (G : Fin (n + 1) → Rˣ) (X : Fin n → R),
      (List.ofFn fun i : Fin n => (↑(G i.castSucc) : R) * X i * ↑(G i.succ)⁻¹).prod =
        ↑(G 0) * (List.ofFn X).prod * ↑(G (Fin.last n))⁻¹ := by
  induction n with
  | zero =>
    intro G X
    simp
  | succ n ih =>
    intro G X
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
    have := ih (fun i => G i.succ) (fun i => X i.succ)
    simp only [← Fin.succ_castSucc]
    rw [this]
    simp only [Fin.succ_last, Fin.castSucc_zero, mul_assoc, Units.inv_mul_cancel_left]

private theorem blockDiag_mul {r : ℕ} (d d' : Fin r → ZMod p)
    (B B' : Matrix (Fin 5) (Fin 5) (ZMod p)) :
    GGHRSW.ColoredMatrix.blockDiag d B * GGHRSW.ColoredMatrix.blockDiag d' B' =
      GGHRSW.ColoredMatrix.blockDiag (fun j => d j * d' j) (B * B') := by
  unfold GGHRSW.ColoredMatrix.blockDiag
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply,
    Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp [Matrix.diagonal_mul_diagonal]

private theorem blockDiag_one {r : ℕ} :
    GGHRSW.ColoredMatrix.blockDiag (fun _ : Fin r => (1 : ZMod p))
      (1 : Matrix (Fin 5) (Fin 5) (ZMod p)) = 1 := by
  unfold GGHRSW.ColoredMatrix.blockDiag
  rw [Matrix.reindex_apply]
  simp [Matrix.diagonal_one, Matrix.fromBlocks_one]

private theorem blockDiag_prod {r : ℕ} (n : ℕ) :
    ∀ (d : Fin n → Fin r → ZMod p) (B : Fin n → Matrix (Fin 5) (Fin 5) (ZMod p)),
      (List.ofFn fun i => GGHRSW.ColoredMatrix.blockDiag (d i) (B i)).prod =
        GGHRSW.ColoredMatrix.blockDiag (fun j => ∏ i, d i j) (List.ofFn B).prod := by
  induction n with
  | zero =>
    intro d B
    simp [blockDiag_one]
  | succ n ih =>
    intro d B
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, ih, blockDiag_mul]
    simp [Fin.prod_univ_succ]

private theorem smul_prod {R : Type*} [CommSemiring R] {m : ℕ} (n : ℕ) :
    ∀ (c : Fin n → R) (M : Fin n → Matrix (Fin m) (Fin m) R),
      (List.ofFn fun i => c i • M i).prod = (∏ i, c i) • (List.ofFn M).prod := by
  induction n with
  | zero =>
    intro c M
    simp
  | succ n ih =>
    intro c M
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, ih, smul_mul_smul_comm,
      Fin.prod_univ_succ]

private theorem bd_ll {r : ℕ} (d : Fin r → ZMod p) (B : Matrix (Fin 5) (Fin 5) (ZMod p))
    (k k' : Fin r) :
    GGHRSW.ColoredMatrix.blockDiag d B (Fin.castAdd 5 k) (Fin.castAdd 5 k') = diagonal d k k' := by
  simp [GGHRSW.ColoredMatrix.blockDiag, Matrix.reindex_apply]

private theorem bd_lr {r : ℕ} (d : Fin r → ZMod p) (B : Matrix (Fin 5) (Fin 5) (ZMod p))
    (k : Fin r) (k' : Fin 5) :
    GGHRSW.ColoredMatrix.blockDiag d B (Fin.castAdd 5 k) (Fin.natAdd r k') = 0 := by
  simp [GGHRSW.ColoredMatrix.blockDiag, Matrix.reindex_apply]

private theorem bd_rl {r : ℕ} (d : Fin r → ZMod p) (B : Matrix (Fin 5) (Fin 5) (ZMod p))
    (k : Fin 5) (k' : Fin r) :
    GGHRSW.ColoredMatrix.blockDiag d B (Fin.natAdd r k) (Fin.castAdd 5 k') = 0 := by
  simp [GGHRSW.ColoredMatrix.blockDiag, Matrix.reindex_apply]

private theorem bd_rr {r : ℕ} (d : Fin r → ZMod p) (B : Matrix (Fin 5) (Fin 5) (ZMod p))
    (k k' : Fin 5) :
    GGHRSW.ColoredMatrix.blockDiag d B (Fin.natAdd r k) (Fin.natAdd r k') = B k k' := by
  simp [GGHRSW.ColoredMatrix.blockDiag, Matrix.reindex_apply]

private theorem sandwich_eval {m : ℕ} (e : Fin (2 * m) → ZMod p)
    (B : Matrix (Fin 5) (Fin 5) (ZMod p)) (mid low : Fin m → ZMod p) (star star' : Fin 5 → ZMod p) :
    (bookendRow mid star * GGHRSW.ColoredMatrix.blockDiag e B * bookendCol low star') 0 0 =
      star ⬝ᵥ (B *ᵥ star') := by
  simp only [Matrix.mul_apply, Fin.sum_univ_add (a := 2 * m) (b := 5)]
  simp [bd_ll, bd_lr, bd_rl, bd_rr, bookendRow, bookendCol, Fin.sum_univ_succ]
  rw [Finset.sum_eq_zero, zero_add]
  · simp [dotProduct, mulVec, Fin.sum_univ_succ]
    ring
  · intro x _
    split_ifs with h
    · rw [Finset.sum_eq_zero, zero_mul]
      intro x1 _
      split_ifs with h1
      · rfl
      · rw [diagonal_apply]
        by_cases hx : x1 = x
        · exact absurd (hx ▸ h) h1
        · simp [hx]
    · rfl

private theorem bookend_id (p : ℕ) [Fact p.Prime] (bp : BP) (ω : Sample p bp)
    (b : Fin bp.n → Bool) :
    (sTil ω * (List.ofFn fun i => DTil ω i (b i)).prod * tTil ω) 0 0 =
        (∏ i, alpha bp ω.γ i (b i)) *
          (ω.sStar ⬝ᵥ
            ((List.ofFn fun i => (bp.A i (b i)).permMatrix (ZMod p)).prod *ᵥ ω.tStar)) ∧
      (s'Til ω * (List.ofFn fun i => D'Til ω i (b i)).prod * t'Til ω) 0 0 =
        (∏ i, alpha' bp ω.γ i (b i)) * (ω.s'Star ⬝ᵥ ω.t'Star) := by
  constructor
  · have hT : sTil ω * (List.ofFn fun i => DTil ω i (b i)).prod * tTil ω =
        bookendRow ω.sMid ω.sStar * (List.ofFn fun i => Dmat ω i (b i)).prod *
          bookendCol ω.tLow ω.tStar := by
      unfold sTil tTil DTil
      rw [tele_prod bp.n ω.R (fun i => Dmat ω i (b i))]
      simp only [Matrix.mul_assoc, Units.inv_mul_cancel_left]
      have hc : ∀ c : Matrix (Fin (NDim bp.n)) (Fin 1) (ZMod p),
          Units.val ((ω.R (Fin.last bp.n))⁻¹) *
            (Units.val (ω.R (Fin.last bp.n)) * c) = c := fun c => by
        rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
      erw [hc]
    rw [hT]
    have hD : (List.ofFn fun i => Dmat ω i (b i)).prod =
        GGHRSW.ColoredMatrix.blockDiag (fun j => ∏ i, ω.d i (b i) j)
          ((∏ i, alpha bp ω.γ i (b i)) •
            (List.ofFn fun i => (bp.A i (b i)).permMatrix (ZMod p)).prod) := by
      unfold Dmat
      rw [blockDiag_prod bp.n (fun i => ω.d i (b i))
        (fun i => alpha bp ω.γ i (b i) • (bp.A i (b i)).permMatrix (ZMod p)),
        smul_prod]
    rw [hD, sandwich_eval, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  · have hT : s'Til ω * (List.ofFn fun i => D'Til ω i (b i)).prod * t'Til ω =
        bookendRow ω.s'Mid ω.s'Star * (List.ofFn fun i => D'mat ω i (b i)).prod *
          bookendCol ω.t'Low ω.t'Star := by
      unfold s'Til t'Til D'Til
      rw [tele_prod bp.n ω.R' (fun i => D'mat ω i (b i))]
      simp only [Matrix.mul_assoc, Units.inv_mul_cancel_left]
      have hc : ∀ c : Matrix (Fin (NDim bp.n)) (Fin 1) (ZMod p),
          Units.val ((ω.R' (Fin.last bp.n))⁻¹) *
            (Units.val (ω.R' (Fin.last bp.n)) * c) = c := fun c => by
        rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
      erw [hc]
    rw [hT]
    have hD : (List.ofFn fun i => D'mat ω i (b i)).prod =
        GGHRSW.ColoredMatrix.blockDiag (fun j => ∏ i, ω.d' i (b i) j)
          ((∏ i, alpha' bp ω.γ i (b i)) •
            (List.ofFn fun _ : Fin bp.n => (1 : Matrix (Fin 5) (Fin 5) (ZMod p))).prod) := by
      unfold D'mat
      rw [blockDiag_prod bp.n (fun i => ω.d' i (b i))
        (fun i => alpha' bp ω.γ i (b i) • (1 : Matrix (Fin 5) (Fin 5) (ZMod p))),
        smul_prod]
    rw [hD, sandwich_eval, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    simp

private theorem prod_card_filter_lt {α M : Type*} [LinearOrder α] [CommMonoid M]
    (S : Finset α) (g : ℕ → M) :
    (∏ i ∈ S, g (S.filter (· < i)).card) = ∏ r ∈ Finset.range S.card, g r := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a s hmax ih =>
    have ha : a ∉ s := fun h => lt_irrefl a (hmax a h)
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, Finset.prod_range_succ, mul_comm]
    rw [← ih]
    congr 1
    · refine Finset.prod_congr rfl fun x hx => ?_
      have hxa : ¬(a < x) := not_lt_of_gt (hmax x hx)
      have hflt : (insert a s).filter (· < x) = s.filter (· < x) := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | hy, hyx⟩
          · exact absurd hyx hxa
          · exact ⟨hy, hyx⟩
        · rintro ⟨hy, hyx⟩
          exact ⟨Or.inr hy, hyx⟩
      rw [hflt]
    · have hflt : (insert a s).filter (· < a) = s := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | hy, hya⟩
          · exact absurd hya (lt_irrefl _)
          · exact hy
        · intro hy
          exact ⟨Or.inr hy, hmax y hy⟩
      rw [hflt]

private theorem pos_eq_on_block (bp : BP) (j : Fin bp.ℓ) {i : Fin bp.n} (hi : i ∈ bp.block j) :
    pos bp i = ((bp.block j).filter (· < i)).card := by
  unfold pos BP.block at *
  congr 1
  ext i'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  rw [hi, and_comm]

private theorem prod_even_shift (φ : ℕ → ZMod p) (k : ℕ) :
    (∏ r ∈ Finset.range k, φ ((2 * r + 2) % (2 * k))) = ∏ r ∈ Finset.range k, φ (2 * r) := by
  rcases k with _ | m
  · simp
  · rw [Finset.prod_range_succ, Finset.prod_range_succ']
    have hm : (2 * m + 2) % (2 * (m + 1)) = 2 * 0 := by
      have : 2 * m + 2 = 2 * (m + 1) := by ring
      rw [this, Nat.mod_self, mul_zero]
    rw [hm]
    congr 1
    refine Finset.prod_congr rfl fun r hr => ?_
    rw [Finset.mem_range] at hr
    have hlt : 2 * r + 2 < 2 * (m + 1) := by omega
    rw [Nat.mod_eq_of_lt hlt]
    ring_nf

private theorem prod_alpha_eq_on_block (bp : BP)
    (γ : Fin bp.ℓ → Bool → Fin (2 * bp.n) → ZMod p) (χ : Fin bp.ℓ → Bool) (j : Fin bp.ℓ) :
    (∏ i ∈ bp.block j, alpha bp γ i (χ (bp.inp i))) =
      ∏ i ∈ bp.block j, alpha' bp γ i (χ (bp.inp i)) := by
  have h1 : (∏ i ∈ bp.block j, alpha bp γ i (χ (bp.inp i))) =
      ∏ i ∈ bp.block j,
        (gam bp γ j (χ j) (2 * ((bp.block j).filter (· < i)).card) *
          gam bp γ j (χ j) (2 * ((bp.block j).filter (· < i)).card + 1)) := by
    refine Finset.prod_congr rfl fun i hi => ?_
    have hinp : bp.inp i = j := by
      simpa [BP.block] using hi
    simp only [alpha, hinp, pos_eq_on_block bp j hi]
  have h2 : (∏ i ∈ bp.block j, alpha' bp γ i (χ (bp.inp i))) =
      ∏ i ∈ bp.block j,
        (gam bp γ j (χ j) (2 * ((bp.block j).filter (· < i)).card + 1) *
          gam bp γ j (χ j)
            ((2 * ((bp.block j).filter (· < i)).card + 2) % (2 * (bp.block j).card))) := by
    refine Finset.prod_congr rfl fun i hi => ?_
    have hinp : bp.inp i = j := by
      simpa [BP.block] using hi
    simp only [alpha', blockSize, hinp, pos_eq_on_block bp j hi]
  rw [h1, h2,
    prod_card_filter_lt (bp.block j)
      (fun r => gam bp γ j (χ j) (2 * r) * gam bp γ j (χ j) (2 * r + 1)),
    prod_card_filter_lt (bp.block j)
      (fun r => gam bp γ j (χ j) (2 * r + 1) *
        gam bp γ j (χ j) ((2 * r + 2) % (2 * (bp.block j).card))),
    Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    prod_even_shift (gam bp γ j (χ j)) (bp.block j).card, mul_comm]

private theorem prod_alpha_eq (bp : BP)
    (γ : Fin bp.ℓ → Bool → Fin (2 * bp.n) → ZMod p) (χ : Fin bp.ℓ → Bool) :
    (∏ i : Fin bp.n, alpha bp γ i (χ (bp.inp i))) =
      ∏ i : Fin bp.n, alpha' bp γ i (χ (bp.inp i)) := by
  rw [← Finset.prod_fiberwise_of_maps_to (g := bp.inp) (t := Finset.univ) (fun _ _ => Finset.mem_univ _),
    ← Finset.prod_fiberwise_of_maps_to (g := bp.inp) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  refine Finset.prod_congr rfl fun j _ => ?_
  exact prod_alpha_eq_on_block bp γ χ j

private theorem permMatrix_map_intCast (σ : Equiv.Perm (Fin 5)) :
    (Int.castRingHom (ZMod p)).mapMatrix (σ.permMatrix ℤ) = σ.permMatrix (ZMod p) := by
  ext r c
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]

end BookendHelpers

theorem solution (p : ℕ) [Fact p.Prime] (bp : BP) (ω : Sample p bp)
    (χ : Fin bp.ℓ → Bool) (h : bp.eval χ = true) :
    Fchi bp ω χ = 0 := by
  unfold Fchi
  have hb := bookend_id p bp ω (fun i => χ (bp.inp i))
  rw [hb.1, hb.2]
  have hZ : (List.ofFn fun i => (bp.A i (χ (bp.inp i))).permMatrix ℤ).prod = 1 := by
    unfold BP.eval at h
    exact of_decide_eq_true h
  have hP : (List.ofFn fun i => (bp.A i (χ (bp.inp i))).permMatrix (ZMod p)).prod = 1 := by
    have hmap := congrArg ((Int.castRingHom (ZMod p)).mapMatrix) hZ
    rw [map_list_prod, map_one, List.map_ofFn] at hmap
    have hfn : ((Int.castRingHom (ZMod p)).mapMatrix ∘
        fun i => (bp.A i (χ (bp.inp i))).permMatrix ℤ) =
        fun i => (bp.A i (χ (bp.inp i))).permMatrix (ZMod p) := by
      funext i
      exact permMatrix_map_intCast (bp.A i (χ (bp.inp i)))
    rwa [hfn] at hmap
  have hBookend : ω.sStar ⬝ᵥ ω.tStar = ω.s'Star ⬝ᵥ ω.t'Star :=
    ω.2.2.2.2.2.2.2.2.1.property
  rw [hP, Matrix.one_mulVec, hBookend, prod_alpha_eq bp ω.γ χ, sub_self]
