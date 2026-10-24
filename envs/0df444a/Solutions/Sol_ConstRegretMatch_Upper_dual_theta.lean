-- Prove2me | solution 1 for ConstRegretMatch.Upper.dual_theta
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T23:06:17.536802+00:00
-- url     : https://prove2.me/submissions/470d6007-bfbf-4f2e-b878-05c9ebe863d5

import Mathlib
import Definitions.Def_ConstRegretMatch_Upper_Network
import Definitions.Def_ConstRegretMatch_Upper_SPP

open ConstRegretMatch.Upper Filter Topology Matrix

namespace CRMDualSol

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


noncomputable def rho (r : Fin d → ℝ) (z : Fin d → ℝ) (s : Fin n → ℝ) : BasisIdx z s → ℝ :=
  Sum.elim (fun m => r m.1) (fun _ => 0)

lemma rho_dot (r : Fin d → ℝ) (z : Fin d → ℝ) (s : Fin n → ℝ) (q : BasisIdx z s → ℝ) :
    rho r z s ⬝ᵥ q = ∑ m, r m * extM z (fun x => q (Sum.inl x)) m := by
  simp only [dotProduct, Fintype.sum_sum_type, rho, Sum.elim_inl, Sum.elim_inr, zero_mul,
    Finset.sum_const_zero, add_zero]
  have h1 : ∑ m ∈ Mplus z, r m * extM z (fun x => q (Sum.inl x)) m =
      ∑ m, r m * extM z (fun x => q (Sum.inl x)) m :=
    Finset.sum_subset (Finset.subset_univ _) (fun m _ hm => by simp [extM, hm])
  rw [← h1, Finset.sum_subtype (Mplus z) (p := fun m => m ∈ Mplus z) (fun _ => Iff.rfl)]
  apply Finset.sum_congr rfl
  intro x _
  simp [extM, x.2]

lemma dual_iff (N : MatchingNetwork n d) (r : Fin d → ℝ) (z : Fin d → ℝ) (s : Fin n → ℝ)
    (θ : Fin n → ℝ) : IsSPPDual N r z s θ ↔ θ ᵥ* basisMatrix N z s = rho r z s := by
  constructor
  · rintro ⟨h1, h2⟩
    funext c
    rcases c with ⟨m, hm⟩ | ⟨j, hj⟩
    · simp only [vecMul, dotProduct, basisMatrix, rho, Sum.elim_inl]
      rw [← h2 m hm]; apply Finset.sum_congr rfl; intro i _; ring
    · simp only [vecMul, dotProduct, basisMatrix, rho, Sum.elim_inr]
      rw [Finset.sum_eq_single j]
      · simp [h1 j hj]
      · intro b _ hb; simp [hb]
      · simp
  · intro h
    refine ⟨fun j hj => ?_, fun m hm => ?_⟩
    · have := congrFun h (Sum.inr ⟨j, hj⟩)
      simp only [vecMul, dotProduct, basisMatrix, rho, Sum.elim_inr] at this
      rw [Finset.sum_eq_single j] at this
      · simpa using this
      · intro b _ hb; simp [hb]
      · simp
    · have := congrFun h (Sum.inl ⟨m, hm⟩)
      simp only [vecMul, dotProduct, basisMatrix, rho, Sum.elim_inl] at this
      rw [← this]; apply Finset.sum_congr rfl; intro i _; ring

lemma perturb (N : MatchingNetwork n d) (r : Fin d → ℝ) (lam : Fin n → ℝ)
    (z : Fin d → ℝ) (s : Fin n → ℝ) (hGP : IsGP N r lam z s)
    (Y : Matrix (BasisIdx z s) (Fin n) ℝ) (hBY : basisMatrix N z s * Y = 1)
    (w : Fin d → ℝ) (u : Fin n → ℝ) (hw : ∀ m, 0 ≤ w m) (hu : ∀ i, 0 ≤ u i) :
    ∃ t : ℝ, 0 < t ∧ ∃ z' s', SPPFeasible N lam z' s' ∧
      ∑ m, r m * z' m = ∑ m, r m * z m + t * (∑ m, r m * w m -
        (rho r z s ᵥ* Y) ⬝ᵥ (fun i => ∑ m, N.M i m * w m + u i)) ∧
      ∀ j, j ∉ Qplus s → s' j = t * u j := by
  set a : Fin n → ℝ := fun i => ∑ m, N.M i m * w m + u i with ha
  set q := Y *ᵥ a with hq
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ c, |t * q c| < basicPart z s c := by
    rw [Filter.eventually_all]
    intro c
    have hc : Tendsto (fun t : ℝ => |t * q c|) (𝓝 0) (𝓝 (|0 * q c|)) :=
      ((continuous_id.mul continuous_const).abs).tendsto 0
    simp only [zero_mul, abs_zero] at hc
    exact hc.eventually (gt_mem_nhds (basicPart_pos z s c))
  obtain ⟨t, ht, htpos⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin (s := Set.Ioi (0 : ℝ)) (a := 0))).exists
  have htpos' : 0 < t := htpos
  set x : BasisIdx z s → ℝ := fun c => basicPart z s c - t * q c with hx
  have hxpos : ∀ c, 0 < x c := fun c => by
    have h1 := ht c; have h2 := le_abs_self (t * q c); simp only [hx]; linarith
  have hxe : x = basicPart z s - t • q := by funext c; simp [hx]
  refine ⟨t, htpos', fun m => extM z (fun y => x (Sum.inl y)) m + t * w m,
    fun j => extQ s (fun y => x (Sum.inr y)) j + t * u j, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro m
    have : 0 ≤ extM z (fun y => x (Sum.inl y)) m := by
      unfold extM; split_ifs with h
      · exact (hxpos _).le
      · exact le_refl 0
    have := mul_nonneg htpos'.le (hw m)
    linarith
  · intro j
    have : 0 ≤ extQ s (fun y => x (Sum.inr y)) j := by
      unfold extQ; split_ifs with h
      · exact (hxpos _).le
      · exact le_refl 0
    have := mul_nonneg htpos'.le (hu j)
    linarith
  · intro i
    have hB := basis_mulVec N z s x i
    have hBq : basisMatrix N z s *ᵥ q = a := by rw [hq, mulVec_mulVec, hBY, one_mulVec]
    have hxv : basisMatrix N z s *ᵥ x = lam - t • a := by
      rw [hxe, mulVec_sub, mulVec_smul, hBq, basis_mulVec_basic N z s lam hGP.1.1]
    have := congrFun hxv i
    rw [hB] at this
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ha] at this
    simp only [mul_add, Finset.sum_add_distrib]
    have e : ∑ m, N.M i m * (t * w m) = t * ∑ m, N.M i m * w m := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro m _; ring
    rw [e]; linarith
  · simp only [mul_add, Finset.sum_add_distrib]
    have e0 := rho_dot r z s x
    rw [hxe, dotProduct_sub, dotProduct_smul, rho_dot r z s (basicPart z s)] at e0
    have hz := extM_basic z s hGP.1.1.1
    rw [hz] at e0
    have e2 : rho r z s ⬝ᵥ q = (rho r z s ᵥ* Y) ⬝ᵥ a := by rw [hq, dotProduct_mulVec]
    have e3 : ∑ m, r m * (t * w m) = t * ∑ m, r m * w m := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro m _; ring
    have e4 : (fun c => (basicPart z s - t • q) c) = x := by rw [hxe]
    rw [e3]
    simp only [smul_eq_mul] at e0
    have e5 : ∑ m, r m * extM z (fun y => x (Sum.inl y)) m =
        ∑ m, r m * extM z (fun y => (basicPart z s - t • q) (Sum.inl y)) m := by rw [hxe]
    rw [e5, ← e0, e2]
    ring
  · intro j hj
    simp [extQ, hj]

end CRMDualSol

open CRMDualSol in
theorem solution {n d : ℕ} (N : MatchingNetwork n d) (r : Fin d → ℝ) (hr : IsMatchValues r)
    (lam : Fin n → ℝ) (hlam : IsArrivalRates lam) (z : Fin d → ℝ) (s : Fin n → ℝ)
    (hGP : IsGP N r lam z s) :
    (∃! θ : Fin n → ℝ, IsSPPDual N r z s θ) ∧
      ∀ θ : Fin n → ℝ, IsSPPDual N r z s θ →
        (∀ Y : Matrix (BasisIdx z s) (Fin n) ℝ, Y * basisMatrix N z s = 1 →
          ∀ i, θ i = ∑ m : {m // m ∈ Mplus z}, r m.1 * Y (Sum.inl m) i) ∧
        (∀ i, 0 ≤ θ i) ∧
        (∀ m, r m ≤ ∑ i, N.M i m * θ i) ∧
        ∑ i, lam i * θ i = ∑ m, r m * z m ∧
        ∀ i ∈ Qzero s, 0 < θ i := by
  obtain ⟨Y, hYB, hBY, _⟩ := basis_inverse N r lam z s hGP
  set θ0 := rho r z s ᵥ* Y with hθ0def
  have hθ0 : IsSPPDual N r z s θ0 :=
    (dual_iff N r z s θ0).2 (by rw [hθ0def, vecMul_vecMul, hYB, vecMul_one])
  have huniq : ∀ θ, IsSPPDual N r z s θ → θ = θ0 := by
    intro θ h
    have h' := (dual_iff N r z s θ).1 h
    calc θ = θ ᵥ* (basisMatrix N z s * Y) := by rw [hBY, vecMul_one]
      _ = θ0 := by rw [← vecMul_vecMul, h']
  refine ⟨⟨θ0, hθ0, huniq⟩, ?_⟩
  intro θ hθ
  rw [huniq θ hθ]
  -- positivity on 𝒬₀
  have hpos : ∀ i ∈ Qzero s, 0 < θ0 i := by
    intro i hi
    have hiQ : i ∉ Qplus s := by
      simp only [Qzero, Qplus, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact hi
    have hsi : s i = 0 := by
      simp only [Qzero, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact le_antisymm (not_lt.mp hi) (hGP.1.1.2.1 i)
    obtain ⟨t, ht, z', s', hf, hobj, hs'⟩ := perturb N r lam z s hGP Y hBY 0 (Pi.single i 1)
      (fun _ => le_refl 0) (fun j => by by_cases h : j = i <;> simp [Pi.single_apply, h])
    have ha : (fun j => ∑ m, N.M j m * (0 : Fin d → ℝ) m + (Pi.single i (1 : ℝ) : Fin n → ℝ) j) =
        Pi.single i 1 := by funext j; simp
    rw [ha, dotProduct_single, mul_one] at hobj
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_sub] at hobj
    have hle := hGP.1.2 z' s' hf
    rw [hobj] at hle
    have h0 : 0 ≤ θ0 i := by nlinarith
    rcases h0.lt_or_eq with h | h
    · exact h
    · exfalso
      have hopt' : SPPOptimal N r lam z' s' := by
        refine ⟨hf, fun z'' s'' h'' => ?_⟩
        rw [hobj, ← hθ0def, ← h, neg_zero, mul_zero, add_zero]
        exact hGP.1.2 z'' s'' h''
      have := (hGP.2.1 z' s' hopt').2
      have h2 := hs' i hiQ
      rw [this, hsi] at h2
      simp at h2
      linarith
  refine ⟨?_, ?_, ?_, ?_, hpos⟩
  · intro Y' hY'
    have e : BasisIdx z s ≃ Fin n := Fintype.equivFinOfCardEq (card_basis N r lam z s hGP)
    have hBY' : basisMatrix N z s * Y' = 1 := (Matrix.mul_eq_one_comm_of_equiv e).mp hY'
    have hd : IsSPPDual N r z s (rho r z s ᵥ* Y') :=
      (dual_iff N r z s _).2 (by rw [vecMul_vecMul, hY', vecMul_one])
    have := huniq _ hd
    intro i
    rw [← this]
    simp [vecMul, dotProduct, Fintype.sum_sum_type, rho]
  · intro i
    by_cases hi : i ∈ Qplus s
    · rw [hθ0.1 i hi]
    · apply le_of_lt
      apply hpos
      simp only [Qzero, Qplus, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact hi
  · intro m
    obtain ⟨t, ht, z', s', hf, hobj, _⟩ := perturb N r lam z s hGP Y hBY (Pi.single m 1) 0
      (fun j => by by_cases h : j = m <;> simp [Pi.single_apply, h]) (fun _ => le_refl 0)
    have ha : (fun j => ∑ m', N.M j m' * (Pi.single m (1 : ℝ) : Fin d → ℝ) m' + (0 : Fin n → ℝ) j) =
        fun j => N.M j m := by
      funext j; simp [Pi.single_apply]
    rw [ha] at hobj
    have hrw : ∑ m', r m' * (Pi.single m (1 : ℝ) : Fin d → ℝ) m' = r m := by simp [Pi.single_apply]
    rw [hrw] at hobj
    have hle := hGP.1.2 z' s' hf
    rw [hobj] at hle
    have : θ0 ⬝ᵥ (fun j => N.M j m) = ∑ i, N.M i m * θ0 i := by
      simp only [dotProduct]; apply Finset.sum_congr rfl; intro i _; ring
    rw [← hθ0def] at hle
    rw [← this]
    nlinarith
  · have h1 : ∑ i, lam i * θ0 i = θ0 ⬝ᵥ lam := by
      simp only [dotProduct]; apply Finset.sum_congr rfl; intro i _; ring
    rw [h1, ← basis_mulVec_basic N z s lam hGP.1.1, dotProduct_mulVec,
      (dual_iff N r z s θ0).1 hθ0, rho_dot, extM_basic z s hGP.1.1.1]
