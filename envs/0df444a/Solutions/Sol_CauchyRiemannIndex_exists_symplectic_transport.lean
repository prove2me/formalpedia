-- Prove2me | solution 1 for CauchyRiemannIndex.exists_symplectic_transport
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-16T17:01:47.931968+00:00
-- url     : https://prove2.me/submissions/bd25c3ef-59f7-48f0-ac4f-39e041a1c0ca

import Definitions.Def_CauchyRiemannIndex_Setting

open Matrix CauchyRiemannIndex

namespace CRLTransport

noncomputable section

variable {n : ℕ}

/-- Vectors of `ℝ²ⁿ`. -/
abbrev Vn (n : ℕ) : Type := Fin n ⊕ Fin n → ℝ

lemma J_mulVec_J (x : Vn n) : J₀ n *ᵥ (J₀ n *ᵥ x) = -x := by
  rw [mulVec_mulVec, J₀, Matrix.J_squared, neg_mulVec, one_mulVec]

lemma J_vecMul (x : Vn n) : x ᵥ* J₀ n = -(J₀ n *ᵥ x) := by
  rw [← mulVec_transpose, J₀, Matrix.J_transpose, neg_mulVec]

lemma dot_J_self (x : Vn n) : x ⬝ᵥ (J₀ n *ᵥ x) = 0 := by
  have h : x ⬝ᵥ (J₀ n *ᵥ x) = (x ᵥ* J₀ n) ⬝ᵥ x := dotProduct_mulVec _ _ _
  rw [J_vecMul, neg_dotProduct, dotProduct_comm (J₀ n *ᵥ x) x] at h
  linarith

/-- The transvection `x ↦ x + c ⟨J w, x⟩ w`. -/
def tv (c : ℝ) (w : Vn n) : Mat n := 1 + c • vecMulVec w (J₀ n *ᵥ w)

lemma tv_mulVec (c : ℝ) (w x : Vn n) :
    tv c w *ᵥ x = x + (c * ((J₀ n *ᵥ w) ⬝ᵥ x)) • w := by
  rw [tv, add_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul, smul_smul]

lemma tv_symplectic (c : ℝ) (w : Vn n) : IsSymplectic (tv c w) := by
  unfold IsSymplectic
  rw [SymplecticGroup.mem_iff]
  set N : Mat n := c • vecMulVec w (J₀ n *ᵥ w) with hN
  have hNJ : N * J₀ n = c • vecMulVec w w := by
    rw [hN, Matrix.smul_mul, vecMulVec_mul, J_vecMul, J_mulVec_J, neg_neg]
  have hJN : J₀ n * Nᵀ = -(c • vecMulVec w w) := by
    rw [hN, transpose_smul, transpose_vecMulVec, Matrix.mul_smul, mul_vecMulVec, J_mulVec_J,
      neg_vecMulVec, smul_neg]
  have hNJN : N * J₀ n * Nᵀ = 0 := by
    rw [hNJ, hN, transpose_smul, transpose_vecMulVec, Matrix.smul_mul, Matrix.mul_smul,
      vecMulVec_mul_vecMulVec, dot_J_self, zero_smul, vecMulVec_zero, smul_zero, smul_zero]
  have hexp : (1 + N) * J₀ n * (1 + N)ᵀ = J₀ n + N * J₀ n + J₀ n * Nᵀ + N * J₀ n * Nᵀ := by
    rw [transpose_add, transpose_one]; noncomm_ring
  change (1 + N) * J₀ n * (1 + N)ᵀ = J₀ n
  rw [hexp, hNJN, hJN, hNJ]
  abel

lemma mat_eq_one_of_mulVec {A : Mat n} (h : ∀ x, A *ᵥ x = x) : A = 1 := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  rw [mulVec_single_one] at this
  simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using this

/-- `u₁ = u + J u`. -/
def mid (u : Vn n) : Vn n := u + J₀ n *ᵥ u

/-- The two-step transport. -/
def tau (p : (Vn n) × (Vn n)) : Mat n :=
  tv (1 / ((J₀ n *ᵥ (p.2 - mid p.1)) ⬝ᵥ mid p.1)) (p.2 - mid p.1) *
    tv (-1 / (p.1 ⬝ᵥ p.1)) (J₀ n *ᵥ p.1)

/-- Its domain. -/
def dom (n : ℕ) : Set ((Vn n) × (Vn n)) :=
  {p | p.1 ⬝ᵥ p.1 ≠ 0 ∧ (J₀ n *ᵥ (p.2 - mid p.1)) ⬝ᵥ mid p.1 ≠ 0}

lemma continuous_mid : Continuous (mid (n := n)) := by
  unfold mid; exact continuous_id.add (continuous_const.matrix_mulVec continuous_id)

lemma isOpen_dom : IsOpen (dom n) := by
  have h1 : Continuous fun p : (Vn n) × (Vn n) => p.1 ⬝ᵥ p.1 :=
    continuous_fst.dotProduct continuous_fst
  have h2 : Continuous fun p : (Vn n) × (Vn n) => (J₀ n *ᵥ (p.2 - mid p.1)) ⬝ᵥ mid p.1 :=
    (continuous_const.matrix_mulVec (continuous_snd.sub (continuous_mid.comp continuous_fst))).dotProduct
      (continuous_mid.comp continuous_fst)
  exact (isOpen_ne_fun h1 continuous_const).inter (isOpen_ne_fun h2 continuous_const)

lemma dot_mid_self (u : Vn n) : u ⬝ᵥ mid u = u ⬝ᵥ u := by
  rw [mid, dotProduct_add, dot_J_self, add_zero]

lemma diag_mem (u : Vn n) (hu : u ≠ 0) : (u, u) ∈ dom n := by
  have h0 : u ⬝ᵥ u ≠ 0 := fun h => hu (dotProduct_self_eq_zero.1 h)
  refine ⟨h0, ?_⟩
  show (J₀ n *ᵥ (u - mid u)) ⬝ᵥ mid u ≠ 0
  rw [show u - mid u = -(J₀ n *ᵥ u) by rw [mid]; abel, mulVec_neg, J_mulVec_J, neg_neg,
    dot_mid_self]
  exact h0

lemma tv_first (u : Vn n) (hu : u ⬝ᵥ u ≠ 0) (x : Vn n) :
    tv (-1 / (u ⬝ᵥ u)) (J₀ n *ᵥ u) *ᵥ x = x + (1 / (u ⬝ᵥ u) * (u ⬝ᵥ x)) • (J₀ n *ᵥ u) := by
  rw [tv_mulVec, J_mulVec_J, neg_dotProduct]
  congr 2
  ring

lemma tau_mulVec (p : (Vn n) × (Vn n)) (hp : p ∈ dom n) : tau p *ᵥ p.1 = p.2 := by
  obtain ⟨h1, h2⟩ := hp
  have hm : tv (-1 / (p.1 ⬝ᵥ p.1)) (J₀ n *ᵥ p.1) *ᵥ p.1 = mid p.1 := by
    rw [tv_first _ h1, show 1 / (p.1 ⬝ᵥ p.1) * (p.1 ⬝ᵥ p.1) = 1 by field_simp, one_smul]; rfl
  rw [tau, ← mulVec_mulVec, hm, tv_mulVec, show 1 / ((J₀ n *ᵥ (p.2 - mid p.1)) ⬝ᵥ mid p.1) *
      ((J₀ n *ᵥ (p.2 - mid p.1)) ⬝ᵥ mid p.1) = 1 by field_simp, one_smul]
  abel

lemma tau_diag (u : Vn n) (hu : (u, u) ∈ dom n) : tau (u, u) = 1 := by
  obtain ⟨h1, -⟩ := hu
  apply mat_eq_one_of_mulVec
  intro x
  have hw : u - mid u = -(J₀ n *ᵥ u) := by rw [mid]; abel
  have hT2 : ∀ y, tv (1 / ((J₀ n *ᵥ (u - mid u)) ⬝ᵥ mid u)) (u - mid u) *ᵥ y =
      y - (1 / (u ⬝ᵥ u) * (u ⬝ᵥ y)) • (J₀ n *ᵥ u) := by
    intro y
    rw [tv_mulVec, hw, mulVec_neg, J_mulVec_J, neg_neg, dot_mid_self, smul_neg, sub_eq_add_neg]
  change (tv _ _ * tv _ _) *ᵥ x = x
  rw [← mulVec_mulVec, tv_first _ h1, hT2, dotProduct_add, dotProduct_smul, dot_J_self,
    smul_eq_mul, mul_zero, add_zero, add_sub_cancel_right]

lemma continuousOn_tau : ContinuousOn (tau (n := n)) (dom n) := by
  have hJ : Continuous fun v : Vn n => J₀ n *ᵥ v := continuous_const.matrix_mulVec continuous_id
  have htv : ∀ {c : (Vn n) × (Vn n) → ℝ} {w : (Vn n) × (Vn n) → Vn n}, ContinuousOn c (dom n) →
      Continuous w → ContinuousOn (fun p => tv (c p) (w p)) (dom n) := by
    intro c w hc hw
    unfold tv
    exact continuousOn_const.add (hc.smul ((hw.matrix_vecMulVec (hJ.comp hw)).continuousOn))
  have hw2 : Continuous fun p : (Vn n) × (Vn n) => p.2 - mid p.1 :=
    continuous_snd.sub (continuous_mid.comp continuous_fst)
  refine ContinuousOn.mul (htv ?_ hw2) (htv ?_ (hJ.comp continuous_fst))
  · exact continuousOn_const.div ((hJ.comp hw2).dotProduct
      (continuous_mid.comp continuous_fst)).continuousOn fun p hp => hp.2
  · exact continuousOn_const.div (continuous_fst.dotProduct continuous_fst).continuousOn
      fun p hp => hp.1

end

end CRLTransport

namespace CauchyRiemannIndex

open CRLTransport

theorem exists_symplectic_transport_aux (n : ℕ) :
    ∃ U : Set ((Fin n ⊕ Fin n → ℝ) × (Fin n ⊕ Fin n → ℝ)), IsOpen U ∧
      (∀ u, u ≠ 0 → (u, u) ∈ U) ∧
      ∃ τ : (Fin n ⊕ Fin n → ℝ) × (Fin n ⊕ Fin n → ℝ) → Mat n, ContinuousOn τ U ∧
        ∀ p ∈ U, IsSymplectic (τ p) ∧ τ p *ᵥ p.1 = p.2 ∧ (p.1 = p.2 → τ p = 1) := by
  refine ⟨dom n, isOpen_dom, diag_mem, tau, continuousOn_tau, fun p hp => ⟨?_, tau_mulVec p hp, ?_⟩⟩
  · exact (Matrix.symplecticGroup (Fin n) ℝ).mul_mem (tv_symplectic _ _) (tv_symplectic _ _)
  · intro h
    obtain ⟨a, b⟩ := p
    simp only at h
    subst h
    exact tau_diag a hp

end CauchyRiemannIndex

open CauchyRiemannIndex in
theorem solution (n : ℕ) :
    ∃ U : Set ((Fin n ⊕ Fin n → ℝ) × (Fin n ⊕ Fin n → ℝ)), IsOpen U ∧
      (∀ u, u ≠ 0 → (u, u) ∈ U) ∧
      ∃ τ : (Fin n ⊕ Fin n → ℝ) × (Fin n ⊕ Fin n → ℝ) → Mat n, ContinuousOn τ U ∧
        ∀ p ∈ U, IsSymplectic (τ p) ∧ τ p *ᵥ p.1 = p.2 ∧ (p.1 = p.2 → τ p = 1) :=
  CauchyRiemannIndex.exists_symplectic_transport_aux n
