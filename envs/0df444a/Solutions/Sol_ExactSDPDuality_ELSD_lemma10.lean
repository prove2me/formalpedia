-- Prove2me | solution 1 for ExactSDPDuality.ELSD.lemma10
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:54:55.0254+00:00
-- url     : https://prove2.me/submissions/b3d83fb8-cb6d-4257-9c08-270c79487b06

import Mathlib
import Definitions.Def_ExactSDPDuality_ELSD_Model

open Matrix

namespace ExactSDPDuality.ELSD

section aux_l10

variable {n m : ℕ}

lemma aux_l10_frob_add_left (A B C : Matrix (Fin n) (Fin n) ℝ) :
    frob (A + B) C = frob A C + frob B C := by
  simp [frob, add_mul, Finset.sum_add_distrib]

lemma aux_l10_frob_add_right (A B C : Matrix (Fin n) (Fin n) ℝ) :
    frob A (B + C) = frob A B + frob A C := by
  simp [frob, mul_add, Finset.sum_add_distrib]

lemma aux_l10_frob_sub_left (A B C : Matrix (Fin n) (Fin n) ℝ) :
    frob (A - B) C = frob A C - frob B C := by
  simp [frob, sub_mul, Finset.sum_sub_distrib]

lemma aux_l10_frob_smul_left (c : ℝ) (A C : Matrix (Fin n) (Fin n) ℝ) :
    frob (c • A) C = c * frob A C := by
  simp [frob, Finset.mul_sum, mul_assoc]

lemma aux_l10_frob_smul_right (c : ℝ) (A C : Matrix (Fin n) (Fin n) ℝ) :
    frob A (c • C) = c * frob A C := by
  simp only [frob, Finset.mul_sum, Matrix.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma aux_l10_frob_comm (A B : Matrix (Fin n) (Fin n) ℝ) : frob A B = frob B A := by
  simp [frob, mul_comm]

lemma aux_l10_frob_zero_left (C : Matrix (Fin n) (Fin n) ℝ) : frob 0 C = 0 := by
  simp [frob]

lemma aux_l10_frob_zero_right (C : Matrix (Fin n) (Fin n) ℝ) : frob C 0 = 0 := by
  simp [frob]

lemma aux_l10_Qstar_add (Q : Fin m → Matrix (Fin n) (Fin n) ℝ) (A B : Matrix (Fin n) (Fin n) ℝ) :
    Qstar Q (A + B) = Qstar Q A + Qstar Q B := by
  funext i
  simp [Qstar, aux_l10_frob_add_left]

lemma aux_l10_Qstar_smul (Q : Fin m → Matrix (Fin n) (Fin n) ℝ) (c : ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) : Qstar Q (c • A) = c • Qstar Q A := by
  funext i
  simp [Qstar, aux_l10_frob_smul_left]

lemma aux_l10_Qstar_zero (Q : Fin m → Matrix (Fin n) (Fin n) ℝ) : Qstar Q 0 = 0 := by
  funext i
  simp [Qstar, aux_l10_frob_zero_left]

lemma aux_l10_QsharpZero_zero (Q0 : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin m → Matrix (Fin n) (Fin n) ℝ) : QsharpZero Q0 Q 0 :=
  ⟨aux_l10_frob_zero_right Q0, aux_l10_Qstar_zero Q⟩

lemma aux_l10_QsharpZero_smul (Q0 : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin m → Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (X : Matrix (Fin n) (Fin n) ℝ)
    (h : QsharpZero Q0 Q X) : QsharpZero Q0 Q (c • X) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · rw [aux_l10_frob_smul_right, h1, mul_zero]
  · rw [aux_l10_Qstar_smul, h2, smul_zero]

lemma aux_l10_QsharpZero_add (Q0 : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin m → Matrix (Fin n) (Fin n) ℝ) (X Y : Matrix (Fin n) (Fin n) ℝ)
    (hX : QsharpZero Q0 Q X) (hY : QsharpZero Q0 Q Y) : QsharpZero Q0 Q (X + Y) := by
  obtain ⟨h1, h2⟩ := hX
  obtain ⟨h3, h4⟩ := hY
  refine ⟨?_, ?_⟩
  · rw [aux_l10_frob_add_right, h1, h3, add_zero]
  · rw [aux_l10_Qstar_add, h2, h4, add_zero]

/-- `Q*` as a linear map. -/
def aux_l10_QstarLin (Q : Fin m → Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] (Fin m → ℝ) where
  toFun := Qstar Q
  map_add' := aux_l10_Qstar_add Q
  map_smul' := fun c A => by simp [aux_l10_Qstar_smul]

lemma aux_l10_psd_mul_transpose (D : Matrix (Fin n) (Fin n) ℝ) : (D * Dᵀ).PosSemidef := by
  simpa [conjTranspose_eq_transpose_of_trivial] using posSemidef_self_mul_conjTranspose D

/-- Shifting a chain by one index. -/
lemma aux_l10_shift (Q0 : Matrix (Fin n) (Fin n) ℝ) (Q : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (k : ℕ) (U W : ℕ → Matrix (Fin n) (Fin n) ℝ) (h : IsCSeq Q0 Q k U W) :
    IsCSeq Q0 Q (k + 1) (fun j => U (j - 1)) (fun j => W (j - 1)) := by
  obtain ⟨hU0, hW0, h⟩ := h
  refine ⟨by simpa using hU0, by simpa using hW0, ?_⟩
  intro i hi1 hik
  rcases Nat.lt_or_ge i 2 with hi | hi
  · have hi' : i = 1 := by omega
    subst hi'
    simp only [Nat.sub_self, Nat.zero_sub, hU0, hW0, add_zero, zero_mul, sub_zero]
    exact ⟨aux_l10_QsharpZero_zero Q0 Q, PosSemidef.zero⟩
  · exact h (i - 1) (by omega) (by omega)

lemma aux_l10_Wmono (Q0 : Matrix (Fin n) (Fin n) ℝ) (Q : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (k : ℕ) : Wset Q0 Q k ⊆ Wset Q0 Q (k + 1) := by
  rintro X ⟨U, W, h, hX⟩
  exact ⟨_, _, aux_l10_shift Q0 Q k U W h, by simpa using hX⟩

lemma aux_l10_Umono (Q0 : Matrix (Fin n) (Fin n) ℝ) (Q : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (k : ℕ) : Uset Q0 Q k ⊆ Uset Q0 Q (k + 1) := by
  rintro X ⟨U, W, h, hX⟩
  exact ⟨_, _, aux_l10_shift Q0 Q k U W h, by simpa using hX⟩

/-- Rescaling a chain. -/
lemma aux_l10_scale (Q0 : Matrix (Fin n) (Fin n) ℝ) (Q : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (k : ℕ) (U W : ℕ → Matrix (Fin n) (Fin n) ℝ) (h : IsCSeq Q0 Q k U W) (t : ℕ → ℝ)
    (ht : ∀ i, 1 ≤ i → i ≤ k → t (i - 1) = t i ^ 2) :
    IsCSeq Q0 Q k (fun i => t (i - 1) • U i) (fun i => t i • W i) := by
  obtain ⟨hU0, hW0, h⟩ := h
  refine ⟨by simp [hU0], by simp [hW0], ?_⟩
  intro i hi1 hik
  obtain ⟨hq, hp⟩ := h i hi1 hik
  refine ⟨?_, ?_⟩
  · have e : t (i - 1) • U i + t (i - 1) • W (i - 1) = t (i - 1) • (U i + W (i - 1)) :=
      (smul_add _ _ _).symm
    show QsharpZero Q0 Q (t (i - 1) • U i + t (i - 1) • W (i - 1))
    rw [e]
    exact aux_l10_QsharpZero_smul Q0 Q _ _ hq
  · have e : t (i - 1) • U i - (t i • W i) * (t i • W i)ᵀ
        = t i ^ 2 • (U i - W i * (W i)ᵀ) := by
      rw [ht i hi1 hik, transpose_smul, smul_mul_smul_comm, smul_sub, sq]
    show PosSemidef (t (i - 1) • U i - (t i • W i) * (t i • W i)ᵀ)
    rw [e]
    exact hp.smul (sq_nonneg _)

/-- Adding two chains. -/
lemma aux_l10_add (Q0 : Matrix (Fin n) (Fin n) ℝ) (Q : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (k : ℕ) (U W U' W' : ℕ → Matrix (Fin n) (Fin n) ℝ) (h : IsCSeq Q0 Q k U W)
    (h' : IsCSeq Q0 Q k U' W') (t : ℕ → ℝ)
    (ht : ∀ i, 1 ≤ i → i ≤ k → t (i - 1) = 2 * t i ^ 2) :
    IsCSeq Q0 Q k (fun i => t (i - 1) • (U i + U' i)) (fun i => t i • (W i + W' i)) := by
  obtain ⟨hU0, hW0, h⟩ := h
  obtain ⟨hU0', hW0', h'⟩ := h'
  refine ⟨by simp [hU0, hU0'], by simp [hW0, hW0'], ?_⟩
  intro i hi1 hik
  obtain ⟨hq, hp⟩ := h i hi1 hik
  obtain ⟨hq', hp'⟩ := h' i hi1 hik
  refine ⟨?_, ?_⟩
  · have e : t (i - 1) • (U i + U' i) + t (i - 1) • (W (i - 1) + W' (i - 1))
        = t (i - 1) • ((U i + W (i - 1)) + (U' i + W' (i - 1))) := by
      simp only [smul_add]; abel
    show QsharpZero Q0 Q (t (i - 1) • (U i + U' i) + t (i - 1) • (W (i - 1) + W' (i - 1)))
    rw [e]
    exact aux_l10_QsharpZero_smul Q0 Q _ _ (aux_l10_QsharpZero_add Q0 Q _ _ hq hq')
  · have e : t (i - 1) • (U i + U' i) - (t i • (W i + W' i)) * (t i • (W i + W' i))ᵀ
        = t i ^ 2 • ((2 : ℝ) • (U i - W i * (W i)ᵀ) + (2 : ℝ) • (U' i - W' i * (W' i)ᵀ)
            + (W i - W' i) * (W i - W' i)ᵀ) := by
      rw [ht i hi1 hik, transpose_smul, smul_mul_smul_comm]
      simp only [transpose_add, transpose_sub, add_mul, mul_add, sub_mul, mul_sub]
      module
    show PosSemidef (t (i - 1) • (U i + U' i) - (t i • (W i + W' i)) * (t i • (W i + W' i))ᵀ)
    rw [e]
    refine PosSemidef.smul ?_ (sq_nonneg _)
    refine PosSemidef.add (PosSemidef.add ?_ ?_) (aux_l10_psd_mul_transpose _)
    · exact hp.smul (by norm_num)
    · exact hp'.smul (by norm_num)

/-- `𝒲ₖ` as a submodule. -/
def aux_l10_Wsub (Q0 : Matrix (Fin n) (Fin n) ℝ) (Q : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (k : ℕ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) where
  carrier := Wset Q0 Q k
  zero_mem' := by
    refine ⟨fun _ => 0, fun _ => 0, ⟨rfl, rfl, fun i _ _ => ?_⟩, rfl⟩
    simp only [add_zero, zero_mul, sub_zero]
    exact ⟨aux_l10_QsharpZero_zero Q0 Q, PosSemidef.zero⟩
  add_mem' := by
    rintro _ _ ⟨U, W, h, rfl⟩ ⟨U', W', h', rfl⟩
    refine ⟨_, _, aux_l10_add Q0 Q k U W U' W' h h' (fun i => 2 ^ (2 ^ (k - i)) / 2) ?_, ?_⟩
    · intro i hi1 hik
      have e : k - (i - 1) = (k - i) + 1 := by omega
      simp only [e, pow_succ, pow_mul]
      ring
    · simp
  smul_mem' := by
    rintro c _ ⟨U, W, h, rfl⟩
    refine ⟨_, _, aux_l10_scale Q0 Q k U W h (fun i => c ^ (2 ^ (k - i))) ?_, ?_⟩
    · intro i hi1 hik
      have e : k - (i - 1) = (k - i) + 1 := by omega
      simp only [e, pow_succ, pow_mul]
    · simp

lemma aux_l10_frob_eq_hadamard (M A : Matrix (Fin n) (Fin n) ℝ) :
    frob M A = star (fun _ => (1 : ℝ)) ⬝ᵥ ((M ⊙ A) *ᵥ fun _ => (1 : ℝ)) := by
  simp [frob, dotProduct, mulVec, hadamard]

lemma aux_l10_frob_psd_nonneg {M A : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosSemidef)
    (hA : A.PosSemidef) : 0 ≤ frob M A := by
  rw [aux_l10_frob_eq_hadamard]
  exact (hM.hadamard hA).dotProduct_mulVec_nonneg _

lemma aux_l10_frob_mul_transpose (D A : Matrix (Fin n) (Fin n) ℝ) :
    frob (D * Dᵀ) A = ∑ j, (fun a => D a j) ⬝ᵥ (A *ᵥ fun a => D a j) := by
  simp only [frob, mul_apply, transpose_apply, dotProduct, mulVec, Finset.sum_mul,
    Finset.mul_sum]
  rw [eq_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Key lemma: if `A ⪰ 0`, `U ⪰ W Wᵀ` and `U • A = 0`, then `W • A = 0`. -/
lemma aux_l10_key {A U W : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef)
    (hUW : (U - W * Wᵀ).PosSemidef) (hU : frob U A = 0) : frob W A = 0 := by
  have h1 := aux_l10_frob_psd_nonneg hUW hA
  rw [aux_l10_frob_sub_left, hU, aux_l10_frob_mul_transpose] at h1
  have hnn : ∀ j ∈ (Finset.univ : Finset (Fin n)),
      0 ≤ (fun a => W a j) ⬝ᵥ (A *ᵥ fun a => W a j) := fun j _ => by
    simpa using hA.dotProduct_mulVec_nonneg (fun a => W a j)
  have hsum : ∑ j, (fun a => W a j) ⬝ᵥ (A *ᵥ fun a => W a j) = 0 :=
    le_antisymm (by linarith) (Finset.sum_nonneg hnn)
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum
  have hker : ∀ j, A *ᵥ (fun a => W a j) = 0 := fun j => by
    have := hz j (Finset.mem_univ _)
    exact (hA.dotProduct_mulVec_zero_iff _).mp (by simpa using this)
  have hsym : ∀ a b, A a b = A b a := fun a b => by
    have := hA.1.apply b a
    simpa using this
  have : frob W A = ∑ j, (A *ᵥ fun a => W a j) j := by
    simp only [frob, mulVec, dotProduct]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => ?_
    rw [hsym]; ring
  rw [this]
  simp [hker]

lemma aux_l10_frob_Qaff (Q0 : Matrix (Fin n) (Fin n) ℝ) (Q : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (x : Fin m → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    frob A (Qaff Q0 Q x) = frob A Q0 - x ⬝ᵥ Qstar Q A := by
  simp only [frob, Qaff, Qhat, Qstar, dotProduct, Matrix.sub_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  rw [eq_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end aux_l10

end ExactSDPDuality.ELSD

open ExactSDPDuality.ELSD
open Matrix

theorem solution {n m : ℕ} (Q0 : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hQ0 : Q0.IsSymm) (hQ : ∀ i, (Q i).IsSymm) :
    (∀ k, 1 ≤ k → Uset Q0 Q k ⊆ Uset Q0 Q (k + 1) ∧ Wset Q0 Q k ⊆ Wset Q0 Q (k + 1)) ∧
      (∀ k, k ≤ m →
        (∃ S : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ),
            (S : Set (Matrix (Fin n) (Fin n) ℝ)) = Wset Q0 Q k) ∧
          ∃ S : Submodule ℝ (Fin m → ℝ), (S : Set (Fin m → ℝ)) = Qstar Q '' Wset Q0 Q k) ∧
      (∀ j k, 1 ≤ j → j ≤ k → k ≤ m → Qstar Q '' Wset Q0 Q j ⊆ Qstar Q '' Wset Q0 Q k) ∧
      ((0 : Fin m → ℝ) ∈ feasibleSet Q0 Q →
        ∀ k, 1 ≤ k → k ≤ m → feasibleSet Q0 Q ⊆ perp (Qstar Q '' Wset Q0 Q k)) := by
  refine ⟨fun k _ => ⟨aux_l10_Umono Q0 Q k, aux_l10_Wmono Q0 Q k⟩, fun k _ => ?_, ?_, ?_⟩
  · refine ⟨⟨aux_l10_Wsub Q0 Q k, rfl⟩, ⟨(aux_l10_Wsub Q0 Q k).map (aux_l10_QstarLin Q), ?_⟩⟩
    rw [Submodule.map_coe]
    rfl
  · intro j k _ hjk _
    have hmono : Monotone (fun k => Wset Q0 Q k) := monotone_nat_of_le_succ (aux_l10_Wmono Q0 Q)
    exact Set.image_mono (hmono hjk)
  · intro h0 k _ _ x hx y hy
    have hQ0psd : Q0.PosSemidef := by
      simpa [feasibleSet, Qaff, Qhat] using h0
    have hxpsd : (Qaff Q0 Q x).PosSemidef := hx
    obtain ⟨W, ⟨Uf, Wf, ⟨hU0, hW0, hc⟩, rfl⟩, rfl⟩ := hy
    have inv : ∀ i, i ≤ k → frob (Wf i) Q0 = 0 ∧ frob (Wf i) (Qaff Q0 Q x) = 0 := by
      intro i
      induction i with
      | zero => intro _; rw [hW0]; exact ⟨aux_l10_frob_zero_left _, aux_l10_frob_zero_left _⟩
      | succ i ih =>
        intro hi
        obtain ⟨ih1, ih2⟩ := ih (by omega)
        obtain ⟨⟨hq1, hq2⟩, hp⟩ := hc (i + 1) (by omega) hi
        simp only [Nat.add_sub_cancel] at hq1 hq2
        have hdot : x ⬝ᵥ Qstar Q (Wf i) = 0 := by
          have := aux_l10_frob_Qaff Q0 Q x (Wf i)
          linarith
        have hU1 : frob (Uf (i + 1)) Q0 = 0 := by
          have := aux_l10_frob_add_left (Uf (i + 1)) (Wf i) Q0
          rw [aux_l10_frob_comm] at hq1
          linarith
        have hU2 : frob (Uf (i + 1)) (Qaff Q0 Q x) = 0 := by
          rw [aux_l10_frob_Qaff, hU1]
          have e : Qstar Q (Uf (i + 1)) = - Qstar Q (Wf i) := by
            rw [aux_l10_Qstar_add] at hq2
            exact eq_neg_of_add_eq_zero_left hq2
          rw [e, dotProduct_neg, hdot]
          simp
        exact ⟨aux_l10_key hQ0psd hp hU1, aux_l10_key hxpsd hp hU2⟩
    obtain ⟨i1, i2⟩ := inv k le_rfl
    have := aux_l10_frob_Qaff Q0 Q x (Wf k)
    linarith
