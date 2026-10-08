-- Prove2me | solution 1 for ExplicitExpanders.Attach.theorem_1_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T06:35:59.21416+00:00
-- url     : https://prove2.me/submissions/2529c5a4-91a3-4cc9-a10f-c3197a2bd10b

import Mathlib
import Definitions.Def_ExplicitExpanders_Attach_IsNDLambda
import Definitions.Def_ExplicitExpanders_Attach_attachMatrix

set_option autoImplicit false

namespace Thm12P54d4b856

open Matrix ExplicitExpanders.Attach

theorem dot_mulVec_symm {V : Type*} [Fintype V] (A : Matrix V V ℝ) (hA : A.IsSymm)
    (u f : V → ℝ) : u ⬝ᵥ (A *ᵥ f) = (A *ᵥ u) ⬝ᵥ f := by
  rw [dotProduct_mulVec]
  congr 1
  conv_lhs => rw [← hA.eq]
  rw [vecMul_transpose]

theorem dot_self_pos {V : Type*} [Fintype V] (f : V → ℝ) (hf : f ≠ 0) : 0 < f ⬝ᵥ f := by
  obtain ⟨v, hv⟩ := Function.ne_iff.mp hf
  unfold dotProduct
  exact Finset.sum_pos' (fun i _ => mul_self_nonneg (f i)) ⟨v, Finset.mem_univ _, mul_self_pos.mpr hv⟩

theorem parseval {V : Type*} [Fintype V] (b : OrthonormalBasis V ℝ (EuclideanSpace ℝ V))
    (f g : V → ℝ) : ∑ i, (f ⬝ᵥ ⇑(b i)) * (⇑(b i) ⬝ᵥ g) = f ⬝ᵥ g := by
  have h := b.sum_inner_mul_inner (WithLp.toLp 2 f) (WithLp.toLp 2 g)
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] at h
  simpa [dotProduct_comm] using h

theorem variational {V : Type*} [Fintype V] (A : Matrix V V ℝ) (hA : A.IsSymm) (d : ℝ)
    (hrow : A *ᵥ (fun _ => (1 : ℝ)) = d • (fun _ => (1 : ℝ))) (lam : ℝ)
    (h1 : ∀ (μ : ℝ) (f : V → ℝ), f ≠ 0 → ∑ v, f v = 0 → A *ᵥ f = μ • f → |μ| ≤ lam)
    (f : V → ℝ) (hf : ∑ v, f v = 0) : |f ⬝ᵥ (A *ᵥ f)| ≤ lam * (f ⬝ᵥ f) := by
  classical
  have hH : A.IsHermitian := by
    show Aᴴ = A
    rw [conjTranspose_eq_transpose_of_trivial]
    exact hA
  set b := hH.eigenvectorBasis with hb
  set μ := hH.eigenvalues with hμ
  have heig : ∀ i, A *ᵥ ⇑(b i) = μ i • ⇑(b i) := fun i => hH.mulVec_eigenvectorBasis i
  set one : V → ℝ := fun _ => 1 with hone
  have hf1 : one ⬝ᵥ f = 0 := by simp [dotProduct, hone, hf]
  have hexp : f ⬝ᵥ (A *ᵥ f) = ∑ i, μ i * ((⇑(b i) ⬝ᵥ f) * (⇑(b i) ⬝ᵥ f)) := by
    rw [← parseval b f (A *ᵥ f)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [dot_mulVec_symm A hA, heig i, smul_dotProduct, smul_eq_mul, dotProduct_comm f]
    ring
  have hnorm : f ⬝ᵥ f = ∑ i, (⇑(b i) ⬝ᵥ f) * (⇑(b i) ⬝ᵥ f) := by
    rw [← parseval b f f]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [dotProduct_comm f]
  have hkey : ∀ i, (⇑(b i) ⬝ᵥ f) ≠ 0 → |μ i| ≤ lam := by
    intro i hci
    set u : V → ℝ := ⇑(b i) with hu
    set s : ℝ := one ⬝ᵥ u with hs
    have hne : Nonempty V := by
      by_contra hV
      rw [not_nonempty_iff] at hV
      exact hci (by simp [dotProduct])
    have hn : (Fintype.card V : ℝ) ≠ 0 := by
      have := Fintype.card_pos (α := V)
      positivity
    have hms : μ i * s = d * s := by
      have e1 : one ⬝ᵥ (A *ᵥ u) = μ i * s := by
        rw [heig i, dotProduct_smul, smul_eq_mul]
      have e2 : one ⬝ᵥ (A *ᵥ u) = d * s := by
        rw [dot_mulVec_symm A hA, hrow, smul_dotProduct, smul_eq_mul]
      rw [← e1, e2]
    set g : V → ℝ := u - (s / Fintype.card V) • one with hg
    have hgf : g ⬝ᵥ f = u ⬝ᵥ f := by
      rw [hg, sub_dotProduct, smul_dotProduct, hf1]; simp
    have hg0 : g ≠ 0 := by
      intro h
      apply hci
      rw [← hgf, h, zero_dotProduct]
    have hgsum : ∑ v, g v = 0 := by
      have : ∑ v, g v = one ⬝ᵥ g := by simp [dotProduct, hone]
      rw [this, hg, dotProduct_sub, dotProduct_smul, smul_eq_mul]
      have : one ⬝ᵥ one = (Fintype.card V : ℝ) := by simp [dotProduct, hone]
      rw [this, ← hs]
      field_simp
      ring
    have hAg : A *ᵥ g = μ i • g := by
      rw [hg, mulVec_sub, mulVec_smul, heig i, hrow, smul_sub, smul_smul, smul_smul]
      congr 2
      field_simp
      linarith [hms]
    exact h1 (μ i) g hg0 hgsum hAg
  rw [hexp, hnorm, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
  rw [abs_mul, abs_of_nonneg (mul_self_nonneg (⇑(b i) ⬝ᵥ f))]
  by_cases hc : (⇑(b i) ⬝ᵥ f) = 0
  · simp [hc]
  · exact mul_le_mul_of_nonneg_right (hkey i hc) (mul_self_nonneg _)

/-- quadratic form of a symmetric matrix with constant row sums, without the mean-zero
assumption: the constant part contributes `d (∑ g)^2 / n`. -/
theorem boundH {V : Type*} [Fintype V] (A : Matrix V V ℝ) (hA : A.IsSymm) (d : ℝ)
    (hrow : A *ᵥ (fun _ => (1 : ℝ)) = d • (fun _ => (1 : ℝ))) (lam : ℝ) (hlam : 0 ≤ lam)
    (hd : 0 ≤ d)
    (h1 : ∀ (μ : ℝ) (f : V → ℝ), f ≠ 0 → ∑ v, f v = 0 → A *ᵥ f = μ • f → |μ| ≤ lam)
    (hn : 0 < (Fintype.card V : ℝ)) (g : V → ℝ) :
    |g ⬝ᵥ (A *ᵥ g)| ≤ lam * (g ⬝ᵥ g) + d * (∑ v, g v) ^ 2 / Fintype.card V := by
  set n : ℝ := (Fintype.card V : ℝ) with hn'
  set S : ℝ := ∑ v, g v with hS
  set one : V → ℝ := fun _ => 1 with hone
  set c : ℝ := S / n with hc
  obtain ⟨g0, hg0⟩ : ∃ g0 : V → ℝ, g0 = g - c • one := ⟨_, rfl⟩
  have hg : g = g0 + c • one := by rw [hg0]; abel
  have h1g : one ⬝ᵥ g = S := by simp [dotProduct, hone, hS]
  have h11 : one ⬝ᵥ one = n := by simp [dotProduct, hone, hn']
  have h1g0 : one ⬝ᵥ g0 = 0 := by
    rw [hg0, dotProduct_sub, dotProduct_smul, smul_eq_mul, h1g, h11, hc]
    field_simp
    ring
  have hsum0 : ∑ v, g0 v = 0 := by
    rw [← h1g0]; simp [dotProduct, hone]
  have hq : g ⬝ᵥ (A *ᵥ g) = g0 ⬝ᵥ (A *ᵥ g0) + d * S ^ 2 / n := by
    have e1 : g0 ⬝ᵥ (A *ᵥ one) = 0 := by
      rw [hrow, dotProduct_smul, smul_eq_mul, dotProduct_comm, h1g0, mul_zero]
    have e2 : one ⬝ᵥ (A *ᵥ g0) = 0 := by
      rw [dot_mulVec_symm A hA, hrow, smul_dotProduct, smul_eq_mul, h1g0, mul_zero]
    have e3 : one ⬝ᵥ (A *ᵥ one) = d * n := by
      rw [hrow, dotProduct_smul, smul_eq_mul, h11]
    rw [hg, mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, add_dotProduct,
      dotProduct_smul, smul_dotProduct, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      smul_eq_mul, smul_eq_mul, smul_eq_mul, e1, e2, e3, hc]
    field_simp
    ring
  have hnorm : g0 ⬝ᵥ g0 ≤ g ⬝ᵥ g := by
    have : g ⬝ᵥ g = g0 ⬝ᵥ g0 + c ^ 2 * n := by
      rw [hg, dotProduct_add, add_dotProduct, add_dotProduct, dotProduct_smul,
        smul_dotProduct, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
        smul_eq_mul, smul_eq_mul, h1g0, dotProduct_comm g0 one, h1g0, h11]
      ring
    rw [this]
    have : 0 ≤ c ^ 2 * n := by positivity
    linarith
  have hv := variational A hA d hrow lam h1 g0 hsum0
  have hnn : 0 ≤ d * S ^ 2 / n := by positivity
  rw [hq]
  calc |g0 ⬝ᵥ (A *ᵥ g0) + d * S ^ 2 / n|
      ≤ |g0 ⬝ᵥ (A *ᵥ g0)| + |d * S ^ 2 / n| := abs_add_le _ _
    _ = |g0 ⬝ᵥ (A *ᵥ g0)| + d * S ^ 2 / n := by rw [abs_of_nonneg hnn]
    _ ≤ lam * (g0 ⬝ᵥ g0) + d * S ^ 2 / n := by linarith
    _ ≤ lam * (g ⬝ᵥ g) + d * S ^ 2 / n := by
        have := mul_le_mul_of_nonneg_left hnorm hlam
        linarith

theorem eqL {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
    (W : Fin r → Finset V) (f : V ⊕ Fin r → ℝ) :
    f ⬝ᵥ (matL W *ᵥ f) = ∑ v ∈ loopSet W, f (Sum.inl v) ^ 2 := by
  have h1 : ∀ v : V, (matL W *ᵥ f) (Sum.inl v)
      = (if v ∈ loopSet W then (1 : ℝ) else 0) * f (Sum.inl v) := by
    intro v
    simp [matL, mulVec, dotProduct, Fintype.sum_sum_type, fromBlocks, diagonal]
  have h2 : ∀ i : Fin r, (matL W *ᵥ f) (Sum.inr i) = 0 := by
    intro i
    simp [matL, mulVec, dotProduct, Fintype.sum_sum_type, fromBlocks]
  rw [dotProduct, Fintype.sum_sum_type]
  simp only [h1, h2, mul_zero, Finset.sum_const_zero, add_zero]
  have h3 : ∀ v : V, f (Sum.inl v) *
      ((if v ∈ loopSet W then (1 : ℝ) else 0) * f (Sum.inl v))
      = if v ∈ loopSet W then f (Sum.inl v) ^ 2 else 0 := by
    intro v; split_ifs <;> ring
  simp_rw [h3]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

theorem quad_eq {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ} (W : Fin r → Finset V)
    (f : V ⊕ Fin r → ℝ) :
    f ⬝ᵥ (matR W *ᵥ f) = 2 * ∑ i, ∑ v ∈ W i, f (Sum.inr i) * f (Sum.inl v) := by
  simp only [dotProduct, mulVec, Fintype.sum_sum_type, matR, fromBlocks_apply₁₁,
    fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, incidence, transpose_apply,
    of_apply, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, zero_add, add_zero, ite_mul,
    one_mul]
  rw [two_mul]
  congr 1
  · simp_rw [Finset.mul_sum, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_filter]
    exact Finset.sum_congr (by ext; simp) fun v _ => mul_comm _ _
  · simp_rw [Finset.mul_sum, mul_ite, mul_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_filter]
    exact Finset.sum_congr (by ext; simp) fun v _ => rfl

theorem amgm (a b x : ℝ) (hx : 0 < x) : 2 * |a * b| ≤ a ^ 2 / x + x * b ^ 2 := by
  have key : ∀ c : ℝ, 2 * (a * c) ≤ a ^ 2 / x + x * c ^ 2 := by
    intro c
    have h1 : 0 ≤ (a - x * c) ^ 2 / x := div_nonneg (sq_nonneg _) hx.le
    have h2 : (a - x * c) ^ 2 / x = a ^ 2 / x + x * c ^ 2 - 2 * (a * c) := by
      field_simp; ring
    linarith
  rcases abs_cases (a * b) with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]; exact key b
  · rw [h]; have := key (-b); nlinarith [this]

theorem boundR {V : Type*} [Fintype V] [DecidableEq V] (p r : ℕ) (W : Fin r → Finset V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (W i) (W j)) (hcard : ∀ i, (W i).card = p + 2)
    (f : V ⊕ Fin r → ℝ) (x : ℝ) (hx : 0 < x) :
      |f ⬝ᵥ (matR W *ᵥ f)| ≤
        ((p : ℝ) + 2) / x * ∑ i, f (Sum.inr i) ^ 2 +
          x * ∑ v ∈ attachedSet W, f (Sum.inl v) ^ 2 := by
  have hq := quad_eq W f
  rw [hq, abs_mul, abs_two]
  have hW : ∑ v ∈ attachedSet W, f (Sum.inl v) ^ 2
      = ∑ i, ∑ v ∈ W i, f (Sum.inl v) ^ 2 := by
    unfold attachedSet
    rw [Finset.sum_biUnion]
    intro i _ j _ hij
    exact hdisj i j hij
  rw [hW]
  calc 2 * |∑ i, ∑ v ∈ W i, f (Sum.inr i) * f (Sum.inl v)|
      ≤ 2 * ∑ i, ∑ v ∈ W i, |f (Sum.inr i) * f (Sum.inl v)| := by
        gcongr
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        gcongr with i _
        exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, ∑ v ∈ W i, 2 * |f (Sum.inr i) * f (Sum.inl v)| := by
        rw [Finset.mul_sum]; simp only [Finset.mul_sum]
    _ ≤ ∑ i, ∑ v ∈ W i, (f (Sum.inr i) ^ 2 / x + x * f (Sum.inl v) ^ 2) := by
        gcongr with i _ v _
        exact amgm _ _ x hx
    _ = ((p : ℝ) + 2) / x * ∑ i, f (Sum.inr i) ^ 2 +
          x * ∑ i, ∑ v ∈ W i, f (Sum.inl v) ^ 2 := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, hcard, nsmul_eq_mul,
          Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        push_cast; ring

theorem quadH {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (r : ℕ) (f : V ⊕ Fin r → ℝ) :
    f ⬝ᵥ (matH H r *ᵥ f) =
      (fun v => f (Sum.inl v)) ⬝ᵥ (H.adjMatrix ℝ *ᵥ fun v => f (Sum.inl v)) := by
  rw [matH, fromBlocks_mulVec]
  simp only [zero_mulVec, add_zero]
  rw [dotProduct, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
    add_zero]
  rfl

/-- one entry of the row-sum vector at an old vertex -/
theorem row_inl {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    {r : ℕ} (W : Fin r → Finset V) (hdisj : ∀ i j, i ≠ j → Disjoint (W i) (W j)) (v : V) :
    (matG H W *ᵥ 1) (Sum.inl v) = (H.adjMatrix ℝ *ᵥ 1) v + 1 := by
  have hR : (matR W *ᵥ (1 : V ⊕ Fin r → ℝ)) (Sum.inl v) =
      ∑ i, if v ∈ W i then (1 : ℝ) else 0 := by
    rw [matR, fromBlocks_mulVec]
    simp [mulVec, dotProduct, incidence]
  have hL : (matL W *ᵥ (1 : V ⊕ Fin r → ℝ)) (Sum.inl v) =
      if v ∈ loopSet W then (1 : ℝ) else 0 := by
    rw [matL, fromBlocks_mulVec]
    simp [mulVec, dotProduct, diagonal]
  have hH : (matH H r *ᵥ (1 : V ⊕ Fin r → ℝ)) (Sum.inl v) = (H.adjMatrix ℝ *ᵥ 1) v := by
    rw [matH, fromBlocks_mulVec]
    simp
  rw [matG, add_mulVec, add_mulVec, Pi.add_apply, Pi.add_apply, hR, hL, hH, add_assoc]
  congr 1
  by_cases hv : v ∈ attachedSet W
  · have hnl : v ∉ loopSet W := by simp [loopSet, hv]
    obtain ⟨i0, -, hi0⟩ := Finset.mem_biUnion.mp hv
    rw [if_neg hnl, add_zero]
    rw [Finset.sum_eq_single i0]
    · simp [hi0]
    · intro j _ hj
      have hd := hdisj j i0 hj
      rw [if_neg]
      intro hvj
      exact Finset.disjoint_left.mp hd hvj hi0
    · simp
  · have hl : v ∈ loopSet W := by simp [loopSet, hv]
    rw [if_pos hl]
    have : ∀ i, v ∉ W i := by
      intro i hi
      exact hv (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hi⟩)
    simp [this]

theorem row_inr {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (p : ℕ) {r : ℕ} (W : Fin r → Finset V) (hcard : ∀ i, (W i).card = p + 2) (i : Fin r) :
    (matG H W *ᵥ 1) (Sum.inr i) = (p : ℝ) + 2 := by
  have hR : (matR W *ᵥ (1 : V ⊕ Fin r → ℝ)) (Sum.inr i) = (p : ℝ) + 2 := by
    rw [matR, fromBlocks_mulVec]
    simp [mulVec, dotProduct, incidence, hcard]
  have hL : (matL W *ᵥ (1 : V ⊕ Fin r → ℝ)) (Sum.inr i) = 0 := by
    rw [matL, fromBlocks_mulVec]
    simp
  have hH : (matH H r *ᵥ (1 : V ⊕ Fin r → ℝ)) (Sum.inr i) = 0 := by
    rw [matH, fromBlocks_mulVec]
    simp
  rw [matG, add_mulVec, add_mulVec, Pi.add_apply, Pi.add_apply, hR, hL, hH]
  ring

end Thm12P54d4b856

open ExplicitExpanders.Attach Matrix in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (p m r : ℕ) (hH : IsNDLambda H m (p + 1) (2 * Real.sqrt p))
    (W : Fin r → Finset V) (hdisj : ∀ i j, i ≠ j → Disjoint (W i) (W j))
    (hcard : ∀ i, (W i).card = p + 2) :
    IsNDLambdaMatrix (matG H W) (m + r) (p + 2)
      (Real.sqrt (2 * ((p : ℝ) + 1)) + Real.sqrt p + ((p : ℝ) + 1) * r / m) := by
  obtain ⟨-, hcardV, hsymm, hrow, heig⟩ := hH
  have hrow' : H.adjMatrix ℝ *ᵥ (fun _ => (1 : ℝ)) = ((p : ℝ) + 1) • (fun _ => (1 : ℝ)) := by
    rw [show (fun _ : V => (1 : ℝ)) = 1 from rfl, hrow]; push_cast; rfl
  have hm : (0 : ℝ) < m := by
    rw [← hcardV]; exact_mod_cast Fintype.card_pos
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [hcardV]
  · unfold matG matH matR matL
    refine ((Matrix.IsSymm.fromBlocks hsymm ?_ ?_).add
      (Matrix.IsSymm.fromBlocks ?_ ?_ ?_)).add (Matrix.IsSymm.fromBlocks ?_ ?_ ?_)
    · simp
    · exact Matrix.isSymm_zero
    · exact Matrix.isSymm_zero
    · rfl
    · exact Matrix.isSymm_zero
    · exact Matrix.isSymm_diagonal _
    · simp
    · exact Matrix.isSymm_zero
  · funext u
    rcases u with v | i
    · rw [Thm12P54d4b856.row_inl H W hdisj v]
      have := congrFun hrow v
      simp only [Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one] at this ⊢
      rw [this]; push_cast; ring
    · rw [Thm12P54d4b856.row_inr H p W hcard i]
      simp
  · intro μ f hf0 hfs hAf
    set g : V → ℝ := fun v => f (Sum.inl v) with hg
    set s := Real.sqrt p with hs
    set t := Real.sqrt (2 * ((p : ℝ) + 1)) with ht
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have ht0 : 0 ≤ t := Real.sqrt_nonneg _
    have hss : s ^ 2 = p := Real.sq_sqrt (by positivity)
    have htt : t ^ 2 = 2 * ((p : ℝ) + 1) := Real.sq_sqrt (by positivity)
    have hst : s < t := Real.sqrt_lt_sqrt (by positivity) (by linarith)
    set x := t - s with hxdef
    have hx : 0 < x := by rw [hxdef]; linarith
    have hxdiv : ((p : ℝ) + 2) / x = t + s := by
      rw [div_eq_iff hx.ne', hxdef]
      linear_combination hss - htt
    have h2s1 : 2 * s + 1 ≤ t + s := by
      nlinarith [sq_nonneg (s - 1), mul_self_nonneg (s + 1 - t)]
    have hq : f ⬝ᵥ (matG H W *ᵥ f) = μ * (f ⬝ᵥ f) := by
      rw [hAf, dotProduct_smul, smul_eq_mul]
    have hsplit : f ⬝ᵥ (matG H W *ᵥ f) = f ⬝ᵥ (matH H r *ᵥ f) + f ⬝ᵥ (matR W *ᵥ f)
        + f ⬝ᵥ (matL W *ᵥ f) := by
      simp only [matG, add_mulVec, dotProduct_add]
    have hHb := Thm12P54d4b856.boundH (H.adjMatrix ℝ) hsymm ((p : ℝ) + 1) hrow' (2 * s)
      (by positivity) (by positivity) heig (by rw [hcardV]; exact hm) g
    rw [hcardV] at hHb
    rw [← Thm12P54d4b856.quadH H r f] at hHb
    have hSum : ∑ v, g v = -∑ i, f (Sum.inr i) := by
      rw [Fintype.sum_sum_type] at hfs
      simp only [hg]
      linarith
    have hCS : (∑ i, f (Sum.inr i)) ^ 2 ≤ (r : ℝ) * ∑ i, f (Sum.inr i) ^ 2 := by
      have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin r)))
        (f := fun i => f (Sum.inr i))
      simpa using this
    have hT : (∑ v, g v) ^ 2 ≤ (r : ℝ) * ∑ i, f (Sum.inr i) ^ 2 := by
      rw [hSum, neg_sq]; exact hCS
    have hLq := Thm12P54d4b856.eqL W f
    have hRb := Thm12P54d4b856.boundR p r W hdisj hcard f x hx
    rw [hxdiv] at hRb
    have hgg : g ⬝ᵥ g = ∑ v ∈ loopSet W, f (Sum.inl v) ^ 2
        + ∑ v ∈ attachedSet W, f (Sum.inl v) ^ 2 := by
      have e : ∑ v ∈ loopSet W, f (Sum.inl v) ^ 2 + ∑ v ∈ attachedSet W, f (Sum.inl v) ^ 2
          = ∑ v, f (Sum.inl v) ^ 2 := by
        unfold loopSet
        exact Finset.sum_sdiff (Finset.subset_univ _)
      rw [e]
      simp [dotProduct, hg, sq]
    have hff : f ⬝ᵥ f = g ⬝ᵥ g + ∑ i, f (Sum.inr i) ^ 2 := by
      simp [dotProduct, Fintype.sum_sum_type, hg, sq]
    have hFpos : 0 < f ⬝ᵥ f := Thm12P54d4b856.dot_self_pos f hf0
    set a := ∑ v ∈ loopSet W, f (Sum.inl v) ^ 2 with ha
    set b := ∑ v ∈ attachedSet W, f (Sum.inl v) ^ 2 with hb
    set c := ∑ i, f (Sum.inr i) ^ 2 with hc
    set T := (∑ v, g v) ^ 2 with hTdef
    have ha0 : 0 ≤ a := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hb0 : 0 ≤ b := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hc0 : 0 ≤ c := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hTm : ((p : ℝ) + 1) * T / m ≤ ((p : ℝ) + 1) * r / m * (a + b + c) := by
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hm, mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc T ≤ (r : ℝ) * c := hT
        _ ≤ (r : ℝ) * (a + b + c) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
    have hA2 : a * (2 * s + 1) ≤ a * (t + s) := mul_le_mul_of_nonneg_left h2s1 ha0
    have habs : |μ| * (f ⬝ᵥ f) ≤
        (t + s + ((p : ℝ) + 1) * r / m) * (f ⬝ᵥ f) := by
      have e1 : |μ| * (f ⬝ᵥ f) = |f ⬝ᵥ (matG H W *ᵥ f)| := by
        rw [hq, abs_mul, abs_of_pos hFpos]
      rw [e1, hsplit, hLq]
      have tri := abs_add_le (f ⬝ᵥ (matH H r *ᵥ f) + f ⬝ᵥ (matR W *ᵥ f)) a
      have tri2 := abs_add_le (f ⬝ᵥ (matH H r *ᵥ f)) (f ⬝ᵥ (matR W *ᵥ f))
      rw [abs_of_nonneg ha0] at tri
      rw [hgg] at hHb
      rw [hff, hgg]
      have hxb : x * b = (t - s) * b := by rw [hxdef]
      linarith [tri, tri2, hHb, hRb, hTm, hA2, hxb]
    exact le_of_mul_le_mul_right habs hFpos
