-- Prove2me | solution 1 for DavidonVM.Termination.quadratic_termination
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T22:29:16.022922+00:00
-- url     : https://prove2.me/submissions/59e90d69-13f3-41eb-ab57-4478109fe5db

import Mathlib
import Definitions.Def_DavidonVM_Termination_Method

set_option autoImplicit false

open Matrix

lemma dvm_vmv {n : ℕ} (u v w : Fin n → ℝ) : vecMulVec u v *ᵥ w = (v ⬝ᵥ w) • u := by
  ext i
  simp only [mulVec, dotProduct, vecMulVec, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma dvm_symdot {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : Aᵀ = A) (a b : Fin n → ℝ) :
    (A *ᵥ a) ⬝ᵥ b = a ⬝ᵥ (A *ᵥ b) := by
  have h : a ᵥ* A = A *ᵥ a := by
    have := vecMul_transpose A a
    rwa [hA] at this
  rw [dotProduct_mulVec, h]

open DavidonVM.Termination in
lemma dvm_y {n : ℕ} (G : Mat n) (ξ : Vec n) (x : ℕ → Vec n) (k : ℕ) :
    G *ᵥ (x (k + 1) - x k) = grad G ξ (x (k + 1)) - grad G ξ (x k) := by
  have : x (k + 1) - x k = (x (k + 1) - ξ) - (x k - ξ) := by abel
  rw [this, mulVec_sub]
  rfl

open DavidonVM.Termination in
lemma dvm_u {n : ℕ} (G : Mat n) (ξ : Vec n) (x : ℕ → Vec n) (H : ℕ → Mat n)
    (hrun : IsQuadRun G ξ x H) (k : ℕ) :
    H k *ᵥ grad G ξ (x (k + 1)) = -(x (k + 1) - x k) + H k *ᵥ (G *ᵥ (x (k + 1) - x k)) := by
  obtain ⟨hx, _⟩ := hrun k
  have hs : H k *ᵥ grad G ξ (x k) = -(x (k + 1) - x k) := by
    rw [hx]; abel
  have hg1 : grad G ξ (x (k + 1)) = grad G ξ (x k) + G *ᵥ (x (k + 1) - x k) := by
    rw [dvm_y G ξ x k]; abel
  rw [hg1, mulVec_add, hs]

open DavidonVM.Termination in
lemma dvm_MN {n : ℕ} (G : Mat n) (ξ : Vec n) (x : ℕ → Vec n) (H : ℕ → Mat n)
    (k : ℕ) (hsym : (H k)ᵀ = H k) (hu : H k *ᵥ grad G ξ (x (k + 1)) = 0) :
    Mval (grad G ξ) x H k = Nval (grad G ξ) x H k := by
  unfold Mval Nval
  rw [hu, ← dvm_symdot hsym, hu]
  simp

open DavidonVM.Termination in
lemma dvm_hered {n : ℕ} (G : Mat n) (hGs : Gᵀ = G) (ξ : Vec n) (x : ℕ → Vec n) (H : ℕ → Mat n)
    (hH0 : (H 0).IsSymm) (hrun : IsQuadRun G ξ x H)
    (hMN : ∀ k < n, Mval (grad G ξ) x H k ≠ Nval (grad G ξ) x H k) :
    ∀ k, k ≤ n → (H k)ᵀ = H k ∧
      ∀ j < k, H k *ᵥ (G *ᵥ (x (j + 1) - x j)) = x (j + 1) - x j := by
  intro k
  induction k with
  | zero => intro _; exact ⟨hH0.eq, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ k ih =>
    intro hk
    obtain ⟨hsym, hher⟩ := ih (by omega)
    obtain ⟨hx, hHk⟩ := hrun k
    have hu := dvm_u G ξ x H hrun k
    have hy := dvm_y G ξ x k
    have hne := hMN k (by omega)
    set a : ℝ := (Mval (grad G ξ) x H k - Nval (grad G ξ) x H k)⁻¹ with ha
    set u : Vec n := H k *ᵥ grad G ξ (x (k + 1)) with hudef
    have hmul : ∀ v : Vec n, H (k + 1) *ᵥ v = H k *ᵥ v + a • ((u ⬝ᵥ v) • u) := by
      intro v
      rw [hHk, add_mulVec, smul_mulVec, dvm_vmv]
    refine ⟨?_, ?_⟩
    · rw [hHk]
      simp [transpose_add, transpose_smul, transpose_vecMulVec, hsym]
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hjk | hjk
      · have hort : u ⬝ᵥ (G *ᵥ (x (j + 1) - x j)) = 0 := by
          rw [hu]
          have e1 : (H k *ᵥ (G *ᵥ (x (k + 1) - x k))) ⬝ᵥ (G *ᵥ (x (j + 1) - x j))
              = (G *ᵥ (x (k + 1) - x k)) ⬝ᵥ (H k *ᵥ (G *ᵥ (x (j + 1) - x j))) :=
            dvm_symdot hsym _ _
          have e2 : (G *ᵥ (x (k + 1) - x k)) ⬝ᵥ (x (j + 1) - x j)
              = (x (k + 1) - x k) ⬝ᵥ (G *ᵥ (x (j + 1) - x j)) := dvm_symdot hGs _ _
          rw [add_dotProduct, neg_dotProduct, e1, hher j hjk, e2]
          ring
        rw [hmul, hher j hjk, hort]
        simp
      · rw [hjk]
        have hN : u ⬝ᵥ grad G ξ (x (k + 1)) = Nval (grad G ξ) x H k := by
          unfold Nval; exact dotProduct_comm _ _
        have hM : u ⬝ᵥ grad G ξ (x k) = Mval (grad G ξ) x H k := by
          unfold Mval; exact dvm_symdot hsym _ _
        have h1 : u ⬝ᵥ (G *ᵥ (x (k + 1) - x k)) =
            Nval (grad G ξ) x H k - Mval (grad G ξ) x H k := by
          rw [hy, dotProduct_sub, hN, hM]
        have h2 : a * (Nval (grad G ξ) x H k - Mval (grad G ξ) x H k) = -1 := by
          have : Mval (grad G ξ) x H k - Nval (grad G ξ) x H k ≠ 0 := sub_ne_zero.2 hne
          rw [ha]; field_simp; ring
        rw [hmul, h1, smul_smul, h2, neg_one_smul, hu]
        abel

open DavidonVM.Termination in
lemma dvm_indep {n : ℕ} (G : Mat n) (hGs : Gᵀ = G) (ξ : Vec n) (x : ℕ → Vec n) (H : ℕ → Mat n)
    (hH0 : (H 0).IsSymm) (hrun : IsQuadRun G ξ x H)
    (hMN : ∀ k < n, Mval (grad G ξ) x H k ≠ Nval (grad G ξ) x H k) :
    ∀ m, m ≤ n → ∀ c : ℕ → ℝ, ∑ j ∈ Finset.range m, c j • (x (j + 1) - x j) = 0 →
      ∀ j < m, c j = 0 := by
  have hher := dvm_hered G hGs ξ x H hH0 hrun hMN
  intro m
  induction m with
  | zero => intro _ c _ j hj; exact absurd hj (Nat.not_lt_zero _)
  | succ m ih =>
    intro hm c hsum j hj
    rw [Finset.sum_range_succ] at hsum
    by_cases hc : c m = 0
    · rw [hc, zero_smul, add_zero] at hsum
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hjm | hjm
      · exact ih (by omega) c hsum j hjm
      · rw [hjm]; exact hc
    · exfalso
      obtain ⟨hsym, hm'⟩ := hher m (by omega)
      have h1 : x (m + 1) - x m
          = ∑ i ∈ Finset.range m, (-(c i / c m)) • (x (i + 1) - x i) := by
        have e : c m • (x (m + 1) - x m) = -(∑ i ∈ Finset.range m, c i • (x (i + 1) - x i)) :=
          eq_neg_of_add_eq_zero_right hsum
        calc x (m + 1) - x m = (c m)⁻¹ • (c m • (x (m + 1) - x m)) := by
              rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
          _ = _ := by
              rw [e, smul_neg, Finset.smul_sum, ← Finset.sum_neg_distrib]
              apply Finset.sum_congr rfl
              intro i _
              rw [smul_smul, ← neg_smul]
              congr 1
              ring
      have key : H m *ᵥ (G *ᵥ (x (m + 1) - x m)) = x (m + 1) - x m := by
        calc H m *ᵥ (G *ᵥ (x (m + 1) - x m))
            = H m *ᵥ (G *ᵥ ∑ i ∈ Finset.range m, (-(c i / c m)) • (x (i + 1) - x i)) := by
              rw [← h1]
          _ = ∑ i ∈ Finset.range m, (-(c i / c m)) • (x (i + 1) - x i) := by
              simp only [mulVec_sum, mulVec_smul]
              apply Finset.sum_congr rfl
              intro i hi
              rw [hm' i (Finset.mem_range.1 hi)]
          _ = x (m + 1) - x m := h1.symm
      have hu := dvm_u G ξ x H hrun m
      rw [key] at hu
      have hu0 : H m *ᵥ grad G ξ (x (m + 1)) = 0 := by rw [hu]; abel
      exact hMN m (by omega) (dvm_MN G ξ x H m hsym hu0)

open DavidonVM.Termination in
theorem solution {n : ℕ} (G : Mat n) (hG : G.PosDef) (ξ : Vec n)
    (x : ℕ → Vec n) (H : ℕ → Mat n) (hH0 : (H 0).IsSymm) (hrun : IsQuadRun G ξ x H)
    (hMN : ∀ k < n, Mval (grad G ξ) x H k ≠ Nval (grad G ξ) x H k) :
    H n = G⁻¹ ∧ x (n + 1) = ξ := by
  have hGs : Gᵀ = G := by
    have := hG.isHermitian.eq
    simpa using this
  have hher := dvm_hered G hGs ξ x H hH0 hrun hMN
  have hind := dvm_indep G hGs ξ x H hH0 hrun hMN n le_rfl
  let S : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => (x (j.1 + 1) - x j.1) i
  have hli : LinearIndependent ℝ S.col := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have := hind (fun i => if h : i < n then g ⟨i, h⟩ else 0) ?_ j.1 j.2
    · simpa [j.2] using this
    · rw [← Fin.sum_univ_eq_sum_range (fun i => (if h : i < n then g ⟨i, h⟩ else 0) •
          (x (i + 1) - x i)) n]
      rw [← hg]
      apply Finset.sum_congr rfl
      intro i _
      have hc : S.col i = x (i.1 + 1) - x i.1 := rfl
      rw [hc]
      simp [i.2]
  have hS : IsUnit S := Matrix.linearIndependent_cols_iff_isUnit.1 hli
  have hHG : H n * G = 1 := by
    apply (hS.mul_left_inj).1
    ext i j
    have h2 := congrFun ((hher n le_rfl).2 j.1 j.2) i
    rw [mulVec_mulVec] at h2
    rw [Matrix.one_mul]
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, S] using h2
  refine ⟨(Matrix.inv_eq_left_inv hHG).symm, ?_⟩
  obtain ⟨hx, _⟩ := hrun n
  have : H n *ᵥ grad G ξ (x n) = x n - ξ := by
    unfold grad
    rw [mulVec_mulVec, hHG, one_mulVec]
  rw [hx, this]
  abel
