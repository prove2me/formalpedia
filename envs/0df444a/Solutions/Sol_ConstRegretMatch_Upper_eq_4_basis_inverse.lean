-- Prove2me | solution 1 for ConstRegretMatch.Upper.eq_4_basis_inverse
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T23:02:10.231517+00:00
-- url     : https://prove2.me/submissions/94ce8653-bf3a-4f6a-8a09-f5ce64844008

import Mathlib
import Definitions.Def_ConstRegretMatch_Upper_Network
import Definitions.Def_ConstRegretMatch_Upper_SPP

open ConstRegretMatch.Upper Filter Topology Matrix

namespace CRMEq4Sol

variable {n d : ℕ}

/-- extend a function on `ℳ₊` by zero -/
noncomputable def extM (z : Fin d → ℝ) (w : {m // m ∈ Mplus z} → ℝ) (m : Fin d) : ℝ :=
  if h : m ∈ Mplus z then w ⟨m, h⟩ else 0

noncomputable def extQ (s : Fin n → ℝ) (w : {j // j ∈ Qplus s} → ℝ) (j : Fin n) : ℝ :=
  if h : j ∈ Qplus s then w ⟨j, h⟩ else 0

lemma basis_mulVec (N : MatchingNetwork n d) (z : Fin d → ℝ) (s : Fin n → ℝ)
    (w : BasisIdx z s → ℝ) (i : Fin n) :
    (basisMatrix N z s *ᵥ w) i =
      ∑ m, N.M i m * extM z (fun x => w (Sum.inl x)) m + extQ s (fun x => w (Sum.inr x)) i := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, basisMatrix]
  congr 1
  · have h1 : ∑ x : {m // m ∈ Mplus z}, N.M i x.1 * w (Sum.inl x) =
        ∑ m ∈ Mplus z, N.M i m * extM z (fun x => w (Sum.inl x)) m := by
      rw [Finset.sum_subtype (Mplus z) (p := fun m => m ∈ Mplus z) (fun _ => Iff.rfl)]
      apply Finset.sum_congr rfl
      intro x _
      simp [extM, x.2]
    rw [h1]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro m _ hm
    simp [extM, hm]
  · by_cases h : i ∈ Qplus s
    · rw [Fintype.sum_eq_single ⟨i, h⟩]
      · simp [extQ, h]
      · intro x hx
        have : i ≠ x.1 := fun e => hx (Subtype.ext e.symm)
        simp [this]
    · rw [Finset.sum_eq_zero]
      · simp [extQ, h]
      · intro x _
        have : i ≠ x.1 := fun e => h (e ▸ x.2)
        simp [this]

lemma extM_basic (z : Fin d → ℝ) (s : Fin n → ℝ) (hz : ∀ m, 0 ≤ z m) :
    extM z (fun x => basicPart z s (Sum.inl x)) = z := by
  funext m
  unfold extM
  split_ifs with h
  · rfl
  · simp only [Mplus, Finset.mem_filter, Finset.mem_univ, true_and] at h
    exact (le_antisymm (not_lt.mp h) (hz m)).symm

lemma extQ_basic (z : Fin d → ℝ) (s : Fin n → ℝ) (hs : ∀ i, 0 ≤ s i) :
    extQ s (fun x => basicPart z s (Sum.inr x)) = s := by
  funext m
  unfold extQ
  split_ifs with h
  · rfl
  · simp only [Qplus, Finset.mem_filter, Finset.mem_univ, true_and] at h
    exact (le_antisymm (not_lt.mp h) (hs m)).symm

lemma basis_mulVec_basic (N : MatchingNetwork n d) (z : Fin d → ℝ) (s : Fin n → ℝ)
    (lam : Fin n → ℝ) (h : SPPFeasible N lam z s) :
    basisMatrix N z s *ᵥ basicPart z s = lam := by
  funext i
  rw [basis_mulVec]
  have e1 := extM_basic z s h.1
  have e2 := extQ_basic z s h.2.1
  simp only [basicPart] at e1 e2 ⊢
  rw [e1, e2]
  exact h.2.2 i

lemma basicPart_pos (z : Fin d → ℝ) (s : Fin n → ℝ) (c : BasisIdx z s) : 0 < basicPart z s c := by
  rcases c with ⟨m, hm⟩ | ⟨j, hj⟩
  · simp only [Mplus, Finset.mem_filter, Finset.mem_univ, true_and] at hm
    exact hm
  · simp only [Qplus, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact hj

/-- Under GP the basis matrix has trivial kernel. -/
lemma basis_ker (N : MatchingNetwork n d) (r : Fin d → ℝ) (lam : Fin n → ℝ)
    (z : Fin d → ℝ) (s : Fin n → ℝ) (hGP : IsGP N r lam z s)
    (v : BasisIdx z s → ℝ) (hv : basisMatrix N z s *ᵥ v = 0) : v = 0 := by
  obtain ⟨⟨hz0, hs0, hfeas⟩, hopt⟩ := hGP.1
  -- small δ
  have hev : ∀ᶠ δ in 𝓝 (0 : ℝ), ∀ c, |δ * v c| < basicPart z s c := by
    rw [Filter.eventually_all]
    intro c
    have hc : Tendsto (fun δ : ℝ => |δ * v c|) (𝓝 0) (𝓝 (|0 * v c|)) :=
      ((continuous_id.mul continuous_const).abs).tendsto 0
    simp only [zero_mul, abs_zero] at hc
    exact hc.eventually (gt_mem_nhds (basicPart_pos z s c))
  obtain ⟨δ, hδ, hδpos⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin (s := Set.Ioi (0 : ℝ)) (a := 0))).exists
  have hδpos' : 0 < δ := hδpos
  let zt : ℝ → Fin d → ℝ := fun t m => z m + t * extM z (fun x => v (Sum.inl x)) m
  let st : ℝ → Fin n → ℝ := fun t j => s j + t * extQ s (fun x => v (Sum.inr x)) j
  have hfeas_t : ∀ t, |t| ≤ δ → SPPFeasible N lam (zt t) (st t) := by
    intro t ht
    refine ⟨?_, ?_, ?_⟩
    · intro m
      simp only [zt, extM]
      split_ifs with h
      · have h1 := hδ (Sum.inl ⟨m, h⟩)
        have h2 : |t * v (Sum.inl ⟨m, h⟩)| ≤ |δ * v (Sum.inl ⟨m, h⟩)| := by
          rw [abs_mul, abs_mul]
          exact mul_le_mul_of_nonneg_right (ht.trans (le_abs_self δ)) (abs_nonneg _)
        have h3 := neg_abs_le (t * v (Sum.inl ⟨m, h⟩))
        simp only [basicPart] at h1
        linarith
      · simpa using hz0 m
    · intro j
      simp only [st, extQ]
      split_ifs with h
      · have h1 := hδ (Sum.inr ⟨j, h⟩)
        have h2 : |t * v (Sum.inr ⟨j, h⟩)| ≤ |δ * v (Sum.inr ⟨j, h⟩)| := by
          rw [abs_mul, abs_mul]
          exact mul_le_mul_of_nonneg_right (ht.trans (le_abs_self δ)) (abs_nonneg _)
        have h3 := neg_abs_le (t * v (Sum.inr ⟨j, h⟩))
        simp only [basicPart] at h1
        linarith
      · simpa using hs0 j
    · intro i
      have hb := congrFun hv i
      rw [basis_mulVec] at hb
      simp only [Pi.zero_apply] at hb
      simp only [zt, st, mul_add, Finset.sum_add_distrib]
      have : ∑ m, N.M i m * (t * extM z (fun x => v (Sum.inl x)) m) =
          t * ∑ m, N.M i m * extM z (fun x => v (Sum.inl x)) m := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro m _; ring
      rw [this, ← hfeas i]
      linear_combination t * hb
  set L := ∑ m, r m * extM z (fun x => v (Sum.inl x)) m with hL
  have hobj : ∀ t, ∑ m, r m * zt t m = ∑ m, r m * z m + t * L := by
    intro t
    simp only [zt, mul_add, Finset.sum_add_distrib, hL, Finset.mul_sum]
    congr 1; apply Finset.sum_congr rfl; intro m _; ring
  have h1 := hopt _ _ (hfeas_t δ (by rw [abs_of_pos hδpos']))
  have h2 := hopt _ _ (hfeas_t (-δ) (by rw [abs_neg, abs_of_pos hδpos']))
  rw [hobj] at h1 h2
  have hL0 : L = 0 := by
    have a : δ * L ≤ 0 := by linarith
    have b : -δ * L ≤ 0 := by linarith
    nlinarith
  have hoptδ : SPPOptimal N r lam (zt δ) (st δ) := by
    refine ⟨hfeas_t δ (by rw [abs_of_pos hδpos']), ?_⟩
    intro z' s' h'
    rw [hobj, hL0, mul_zero, add_zero]
    exact hopt z' s' h'
  obtain ⟨ez, es⟩ := hGP.2.1 _ _ hoptδ
  funext c
  rcases c with ⟨m, hm⟩ | ⟨j, hj⟩
  · have := congrFun ez m
    simp only [zt, extM, hm, dif_pos] at this
    have : δ * v (Sum.inl ⟨m, hm⟩) = 0 := by linarith
    simpa [hδpos'.ne'] using this
  · have := congrFun es j
    simp only [st, extQ, hj, dif_pos] at this
    have : δ * v (Sum.inr ⟨j, hj⟩) = 0 := by linarith
    simpa [hδpos'.ne'] using this

lemma card_basis (N : MatchingNetwork n d) (r : Fin d → ℝ) (lam : Fin n → ℝ)
    (z : Fin d → ℝ) (s : Fin n → ℝ) (hGP : IsGP N r lam z s) :
    Fintype.card (BasisIdx z s) = n := by
  rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_coe]
  exact hGP.2.2

/-- Under GP, `ℬ` has a two-sided inverse whose entries are bounded by `n!`. -/
lemma basis_inverse (N : MatchingNetwork n d) (r : Fin d → ℝ) (lam : Fin n → ℝ)
    (z : Fin d → ℝ) (s : Fin n → ℝ) (hGP : IsGP N r lam z s) :
    ∃ Y : Matrix (BasisIdx z s) (Fin n) ℝ,
      Y * basisMatrix N z s = 1 ∧ basisMatrix N z s * Y = 1 ∧
      ∀ c i, |Y c i| ≤ (n.factorial : ℝ) := by
  classical
  let e : BasisIdx z s ≃ Fin n := Fintype.equivFinOfCardEq (card_basis N r lam z s hGP)
  set B := basisMatrix N z s with hB
  let B' : Matrix (Fin n) (Fin n) ℝ := B.submatrix id e.symm
  have hBB' : B = B'.submatrix id e := by
    ext i c; simp [B']
  have hdet : B'.det ≠ 0 := by
    intro h0
    obtain ⟨u, hu0, hu⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have : B *ᵥ (u ∘ e) = 0 := by
      have h := Matrix.submatrix_mulVec_equiv B u id e.symm
      simp only [Equiv.symm_symm, Function.comp_id] at h
      rw [← h]; exact hu
    have hk := basis_ker N r lam z s hGP _ this
    apply hu0
    funext k
    have := congrFun hk (e.symm k)
    simpa using this
  let Y : Matrix (BasisIdx z s) (Fin n) ℝ := (B'⁻¹).submatrix e id
  have hYB : Y * B = 1 := by
    rw [hBB']
    have := Matrix.submatrix_mul_equiv (B'⁻¹) B' e (Equiv.refl (Fin n)) e
    simp only [Equiv.coe_refl] at this
    simp only [Y]
    rw [this, Matrix.nonsing_inv_mul _ (Ne.isUnit hdet)]
    exact Matrix.submatrix_one_equiv e
  refine ⟨Y, hYB, (Matrix.mul_eq_one_comm_of_equiv e).mp hYB, ?_⟩
  -- entry bound
  -- integrality of det
  have hent : ∀ i k, B' i k = 0 ∨ B' i k = 1 := by
    intro i k
    simp only [B', B, Matrix.submatrix_apply, id, basisMatrix]
    rcases e.symm k with ⟨m, hm⟩ | ⟨j, hj⟩ <;>
      simp only [MatchingNetwork.M, MatchingNetwork.inc] <;> split_ifs <;> simp
  let BZ : Matrix (Fin n) (Fin n) ℤ := fun i k => if B' i k = 0 then 0 else 1
  have hBZ : B' = BZ.map (Int.castRingHom ℝ) := by
    ext i k
    show B' i k = (((if B' i k = 0 then 0 else 1 : ℤ)) : ℝ)
    rcases hent i k with h | h <;> simp [h]
  have hdetZ : B'.det = ((BZ.det : ℤ) : ℝ) := by
    rw [hBZ]
    have := RingHom.map_det (Int.castRingHom ℝ) BZ
    rw [RingHom.mapMatrix_apply] at this
    rw [← this]; simp
  have hdet1 : 1 ≤ |B'.det| := by
    rw [hdetZ]
    have : BZ.det ≠ 0 := by
      intro h; apply hdet; rw [hdetZ, h]; simp
    have h2 := Int.one_le_abs this
    rw [← Int.cast_abs]
    exact_mod_cast h2
  have hadj : ∀ a b, |B'.adjugate a b| ≤ (n.factorial : ℝ) := by
    intro a b
    rw [Matrix.adjugate_apply]
    have := Matrix.det_le (A := B'.updateRow b (Pi.single a 1)) (abv := AbsoluteValue.abs)
      (x := (1 : ℝ)) (by
        intro i k
        simp only [AbsoluteValue.abs_apply]
        by_cases hi : i = b
        · subst hi
          rw [Matrix.updateRow_self]
          by_cases hk : k = a
          · subst hk; simp
          · simp [Pi.single_apply, hk]
        · rw [Matrix.updateRow_ne hi]
          rcases hent i k with h | h <;> simp [h])
    simpa [Fintype.card_fin] using this
  intro c i
  simp only [Y, Matrix.submatrix_apply, id, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul]
  rw [Ring.inverse_eq_inv', abs_mul, abs_inv]
  have hpos : 0 < |B'.det| := by linarith
  calc |B'.det|⁻¹ * |B'.adjugate (e c) i| ≤ 1 * |B'.adjugate (e c) i| := by
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        exact inv_le_one_of_one_le₀ hdet1
    _ ≤ n.factorial := by rw [one_mul]; exact hadj _ _

end CRMEq4Sol

open CRMEq4Sol in
theorem solution {n d : ℕ} (N : MatchingNetwork n d) :
    ∃ ω : ℝ, 0 < ω ∧
      ∀ (r : Fin d → ℝ), IsMatchValues r →
      ∀ (lam : Fin n → ℝ), IsArrivalRates lam →
      ∀ (z : Fin d → ℝ) (s : Fin n → ℝ), IsGP N r lam z s →
        ∃ Y : Matrix (BasisIdx z s) (Fin n) ℝ,
          Y * basisMatrix N z s = 1 ∧ basisMatrix N z s * Y = 1 ∧
          Y.mulVec lam = basicPart z s ∧
          (∀ c, 0 < basicPart z s c) ∧
          ∀ c i, |Y c i| ≤ ω := by
  refine ⟨n.factorial, by exact_mod_cast Nat.factorial_pos n, ?_⟩
  intro r _ lam _ z s hGP
  obtain ⟨Y, h1, h2, h3⟩ := basis_inverse N r lam z s hGP
  refine ⟨Y, h1, h2, ?_, basicPart_pos z s, h3⟩
  rw [← basis_mulVec_basic N z s lam hGP.1.1, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
