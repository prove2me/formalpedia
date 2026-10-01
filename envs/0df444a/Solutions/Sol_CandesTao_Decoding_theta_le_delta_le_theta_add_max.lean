-- Prove2me | solution 1 for CandesTao.Decoding.theta_le_delta_le_theta_add_max
-- status  : ACCEPTED   (prove)
-- author  : @radokirov
-- created : 2026-10-01T05:02:02.428013+00:00
-- url     : https://prove2.me/submissions/61f6cbc3-d471-4cbd-a4fb-4115c422dc56

import Definitions.Def_CandesTao_Decoding_RestrictedIsometry
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic

open CandesTao.Decoding

namespace CandesTaoLemma12

/-- The set whose infimum is `δ_k`. -/
def DS {p m : ℕ} (F : Matrix (Fin p) (Fin m) ℝ) (k : ℕ) : Set ℝ :=
  {δ : ℝ | 0 ≤ δ ∧ ∀ T : Finset (Fin m), T.card ≤ k → ∀ c : Fin m → ℝ, SupportedOn c T →
    (1 - δ) * l2Norm c ^ 2 ≤ l2Norm (F.mulVec c) ^ 2 ∧
    l2Norm (F.mulVec c) ^ 2 ≤ (1 + δ) * l2Norm c ^ 2}

/-- The set whose infimum is `θ_{k,k'}`. -/
def TS {p m : ℕ} (F : Matrix (Fin p) (Fin m) ℝ) (k k' : ℕ) : Set ℝ :=
  {θ : ℝ | 0 ≤ θ ∧ ∀ T T' : Finset (Fin m), Disjoint T T' → T.card ≤ k → T'.card ≤ k' →
    ∀ c c' : Fin m → ℝ, SupportedOn c T → SupportedOn c' T' →
    |dotProduct (F.mulVec c) (F.mulVec c')| ≤ θ * l2Norm c * l2Norm c'}

lemma nsq {n : ℕ} (x : Fin n → ℝ) : l2Norm x ^ 2 = ∑ i, x i ^ 2 := by
  unfold l2Norm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (x i))]

lemma nsq_add {n : ℕ} (x y : Fin n → ℝ) :
    l2Norm (x + y) ^ 2 = l2Norm x ^ 2 + 2 * dotProduct x y + l2Norm y ^ 2 := by
  rw [nsq, nsq, nsq, dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply]
  ring

lemma nsq_sub {n : ℕ} (x y : Fin n → ℝ) :
    l2Norm (x - y) ^ 2 = l2Norm x ^ 2 - 2 * dotProduct x y + l2Norm y ^ 2 := by
  rw [nsq, nsq, nsq, dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.sub_apply]
  ring

lemma nsq_smul {n : ℕ} (a : ℝ) (x : Fin n → ℝ) : l2Norm (a • x) ^ 2 = a ^ 2 * l2Norm x ^ 2 := by
  rw [nsq, nsq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

lemma eq_zero_of_nsq {n : ℕ} (x : Fin n → ℝ) (h : l2Norm x = 0) : x = 0 := by
  have h2 : ∑ i, x i ^ 2 = 0 := by rw [← nsq, h]; ring
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (x i))] at h2
  funext i
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (h2 i (Finset.mem_univ i))

lemma dot_disjoint {m : ℕ} (c c' : Fin m → ℝ) (T T' : Finset (Fin m)) (hTT : Disjoint T T')
    (hc : SupportedOn c T) (hc' : SupportedOn c' T') : dotProduct c c' = 0 := by
  unfold dotProduct
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : j ∈ T
  · have : j ∉ T' := Finset.disjoint_left.mp hTT hj
    rw [hc' j this, mul_zero]
  · rw [hc j hj, zero_mul]

lemma supp_add {m : ℕ} (c c' : Fin m → ℝ) (T T' : Finset (Fin m))
    (hc : SupportedOn c T) (hc' : SupportedOn c' T') : SupportedOn (c + c') (T ∪ T') := by
  intro j hj
  rw [Finset.mem_union, not_or] at hj
  simp [hc j hj.1, hc' j hj.2]

lemma supp_sub {m : ℕ} (c c' : Fin m → ℝ) (T T' : Finset (Fin m))
    (hc : SupportedOn c T) (hc' : SupportedOn c' T') : SupportedOn (c - c') (T ∪ T') := by
  intro j hj
  rw [Finset.mem_union, not_or] at hj
  simp [hc j hj.1, hc' j hj.2]

lemma supp_smul {m : ℕ} (a : ℝ) (c : Fin m → ℝ) (T : Finset (Fin m))
    (hc : SupportedOn c T) : SupportedOn (a • c) T := by
  intro j hj
  simp [hc j hj]

/-- Cauchy–Schwarz row by row: `‖F x‖² ≤ (∑ᵢⱼ Fᵢⱼ²) ‖x‖²`. -/
lemma mulVec_sq_le {p m : ℕ} (F : Matrix (Fin p) (Fin m) ℝ) (x : Fin m → ℝ) :
    l2Norm (F.mulVec x) ^ 2 ≤ (∑ i, ∑ j, F i j ^ 2) * l2Norm x ^ 2 := by
  rw [nsq, nsq, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

lemma DS_nonempty {p m : ℕ} (F : Matrix (Fin p) (Fin m) ℝ) (k : ℕ) : (DS F k).Nonempty := by
  refine ⟨max 1 (∑ i, ∑ j, F i j ^ 2), le_trans zero_le_one (le_max_left _ _), ?_⟩
  intro U _ x _
  have h0 : 0 ≤ l2Norm x ^ 2 := sq_nonneg _
  have h1 : 0 ≤ l2Norm (F.mulVec x) ^ 2 := sq_nonneg _
  have hb := mulVec_sq_le F x
  have hm1 : 1 ≤ max 1 (∑ i, ∑ j, F i j ^ 2) := le_max_left _ _
  have hmK : (∑ i, ∑ j, F i j ^ 2) ≤ max 1 (∑ i, ∑ j, F i j ^ 2) := le_max_right _ _
  constructor
  · nlinarith
  · nlinarith

lemma DS_bdd {p m : ℕ} (F : Matrix (Fin p) (Fin m) ℝ) (k : ℕ) : BddBelow (DS F k) :=
  ⟨0, fun _ hx => hx.1⟩

lemma TS_bdd {p m : ℕ} (F : Matrix (Fin p) (Fin m) ℝ) (k k' : ℕ) : BddBelow (TS F k k') :=
  ⟨0, fun _ hx => hx.1⟩

/-- Polarization: an admissible `δ` for `S + S'` is an admissible `θ` for `S, S'`. -/
lemma DS_sub_TS {p m : ℕ} (F : Matrix (Fin p) (Fin m) ℝ) (S S' : ℕ) :
    DS F (S + S') ⊆ TS F S S' := by
  intro δ hδ
  refine ⟨hδ.1, ?_⟩
  intro T T' hTT hT hT' c c' hc hc'
  set a := l2Norm c with ha
  set b := l2Norm c' with hb
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  set X := dotProduct (F.mulVec c) (F.mulVec c') with hX
  -- degenerate cases
  by_cases hab : a * b = 0
  · rcases mul_eq_zero.mp hab with h | h
    · have : c = 0 := eq_zero_of_nsq c h
      rw [hX, this, Matrix.mulVec_zero, zero_dotProduct, abs_zero]
      exact mul_nonneg (mul_nonneg hδ.1 ha0) hb0
    · have : c' = 0 := eq_zero_of_nsq c' h
      rw [hX, this, Matrix.mulVec_zero, dotProduct_zero, abs_zero]
      exact mul_nonneg (mul_nonneg hδ.1 ha0) hb0
  have habpos : 0 < a * b := lt_of_le_of_ne (mul_nonneg ha0 hb0) (Ne.symm hab)
  -- rescaled vectors
  set u := b • c with hu
  set v := a • c' with hv
  have hcard : (T ∪ T').card ≤ S + S' := by
    rw [Finset.card_union_of_disjoint hTT]; omega
  have hsu := supp_smul b c T hc
  have hsv := supp_smul a c' T' hc'
  have huv0 : dotProduct u v = 0 := dot_disjoint u v T T' hTT hsu hsv
  have hnu : l2Norm u ^ 2 = b ^ 2 * a ^ 2 := by rw [hu, nsq_smul]
  have hnv : l2Norm v ^ 2 = a ^ 2 * b ^ 2 := by rw [hv, nsq_smul]
  have hp := (hδ.2 _ hcard (u + v) (supp_add u v T T' hsu hsv)).2
  have hm := (hδ.2 _ hcard (u - v) (supp_sub u v T T' hsu hsv)).1
  rw [nsq_add, huv0, hnu, hnv] at hp
  rw [nsq_sub, huv0, hnu, hnv] at hm
  have hp2 := (hδ.2 _ hcard (u + v) (supp_add u v T T' hsu hsv)).1
  have hm2 := (hδ.2 _ hcard (u - v) (supp_sub u v T T' hsu hsv)).2
  rw [nsq_add, huv0, hnu, hnv] at hp2
  rw [nsq_sub, huv0, hnu, hnv] at hm2
  rw [Matrix.mulVec_add, nsq_add] at hp hp2
  rw [Matrix.mulVec_sub, nsq_sub] at hm hm2
  have hFuv : dotProduct (F.mulVec u) (F.mulVec v) = a * b * X := by
    rw [hu, hv, Matrix.mulVec_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, smul_eq_mul, hX]
    ring
  rw [hFuv] at hp hm hp2 hm2
  -- `4 a b X ≤ 4 δ a² b²` and `-4 δ a² b² ≤ 4 a b X`
  have hup : a * b * X ≤ δ * (a * b) * (a * b) := by nlinarith
  have hlo : -(δ * (a * b) * (a * b)) ≤ a * b * X := by nlinarith
  rw [abs_le]
  constructor
  · have := (mul_le_mul_iff_of_pos_left habpos).mp (by nlinarith : a * b * (-(δ * a * b)) ≤ a * b * X)
    linarith
  · have := (mul_le_mul_iff_of_pos_left habpos).mp (by nlinarith : a * b * X ≤ a * b * (δ * a * b))
    linarith

/-- Splitting the support: `θ + max δ₁ δ₂` is admissible for `S + S'`. -/
lemma add_max_mem {p m : ℕ} (F : Matrix (Fin p) (Fin m) ℝ) (S S' : ℕ) (θ δ₁ δ₂ : ℝ)
    (hθ : θ ∈ TS F S S') (h₁ : δ₁ ∈ DS F S) (h₂ : δ₂ ∈ DS F S') :
    θ + max δ₁ δ₂ ∈ DS F (S + S') := by
  classical
  refine ⟨add_nonneg hθ.1 (le_trans h₁.1 (le_max_left _ _)), ?_⟩
  intro U hU c hc
  obtain ⟨T, hTU, hTcard⟩ := Finset.exists_subset_card_eq (min_le_right S U.card)
  set T' := U \ T with hT'
  have hT'card : T'.card ≤ S' := by
    have h := Finset.card_sdiff_add_card_eq_card hTU
    rw [hTcard] at h
    show (U \ T).card ≤ S'
    omega
  have hTS : T.card ≤ S := by rw [hTcard]; exact min_le_left _ _
  have hdisj : Disjoint T T' := Finset.disjoint_sdiff
  set c₁ : Fin m → ℝ := fun j => if j ∈ T then c j else 0 with hc₁
  set c₂ : Fin m → ℝ := fun j => if j ∈ T then 0 else c j with hc₂
  have hsplit : c = c₁ + c₂ := by
    funext j; simp only [hc₁, hc₂, Pi.add_apply]; split_ifs <;> simp
  have hs₁ : SupportedOn c₁ T := by intro j hj; simp [hc₁, hj]
  have hs₂ : SupportedOn c₂ T' := by
    intro j hj
    simp only [hc₂]
    split_ifs with h
    · rfl
    · have : j ∉ U := by
        intro hjU; exact hj (Finset.mem_sdiff.mpr ⟨hjU, h⟩)
      exact hc j this
  have h12 : dotProduct c₁ c₂ = 0 := dot_disjoint c₁ c₂ T T' hdisj hs₁ hs₂
  set A := l2Norm c₁
  set B := l2Norm c₂
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  have hcn : l2Norm c ^ 2 = A ^ 2 + B ^ 2 := by rw [hsplit, nsq_add, h12]; ring
  have hFc : l2Norm (F.mulVec c) ^ 2 = l2Norm (F.mulVec c₁) ^ 2 +
      2 * dotProduct (F.mulVec c₁) (F.mulVec c₂) + l2Norm (F.mulVec c₂) ^ 2 := by
    rw [hsplit, Matrix.mulVec_add, nsq_add]
  have hP := hθ.2 T T' hdisj hTS hT'card c₁ c₂ hs₁ hs₂
  rw [abs_le] at hP
  have e₁ := h₁.2 T hTS c₁ hs₁
  have e₂ := h₂.2 T' hT'card c₂ hs₂
  set M := max δ₁ δ₂
  have hM₁ : δ₁ * A ^ 2 ≤ M * A ^ 2 :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
  have hM₂ : δ₂ * B ^ 2 ≤ M * B ^ 2 :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)
  have hAB : θ * (2 * A * B) ≤ θ * (A ^ 2 + B ^ 2) :=
    mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (A - B)]) hθ.1
  rw [hcn, hFc]
  constructor
  · nlinarith
  · nlinarith

end CandesTaoLemma12

open CandesTaoLemma12 in
theorem solution {p m : ℕ} (F : Matrix (Fin p) (Fin m) ℝ) (S S' : ℕ)
    (hS : 1 ≤ S) (hS' : 1 ≤ S') (hSS' : S + S' ≤ m) :
    restrictedOrthogonalityConst F S S' ≤ restrictedIsometryConst F (S + S') ∧
    restrictedIsometryConst F (S + S') ≤
      restrictedOrthogonalityConst F S S' +
        max (restrictedIsometryConst F S) (restrictedIsometryConst F S') := by
  have eD : ∀ k, restrictedIsometryConst F k = sInf (DS F k) := fun _ => rfl
  have eT : restrictedOrthogonalityConst F S S' = sInf (TS F S S') := rfl
  have hTne : (TS F S S').Nonempty :=
    (DS_nonempty F (S + S')).mono (DS_sub_TS F S S')
  refine ⟨?_, ?_⟩
  · rw [eT, eD]
    exact csInf_le_csInf (TS_bdd F S S') (DS_nonempty F (S + S')) (DS_sub_TS F S S')
  · rw [eT, eD, eD, eD]
    apply le_of_forall_pos_lt_add
    intro ε hε
    obtain ⟨θ, hθ, hθlt⟩ :=
      exists_lt_of_csInf_lt hTne (by linarith : sInf (TS F S S') < sInf (TS F S S') + ε / 2)
    obtain ⟨d₁, hd₁, hd₁lt⟩ := exists_lt_of_csInf_lt (DS_nonempty F S)
      (by linarith : sInf (DS F S) < sInf (DS F S) + ε / 2)
    obtain ⟨d₂, hd₂, hd₂lt⟩ := exists_lt_of_csInf_lt (DS_nonempty F S')
      (by linarith : sInf (DS F S') < sInf (DS F S') + ε / 2)
    have hmem := add_max_mem F S S' θ d₁ d₂ hθ hd₁ hd₂
    have hle := csInf_le (DS_bdd F (S + S')) hmem
    have hmax : max d₁ d₂ < max (sInf (DS F S)) (sInf (DS F S')) + ε / 2 := by
      apply max_lt
      · linarith [le_max_left (sInf (DS F S)) (sInf (DS F S'))]
      · linarith [le_max_right (sInf (DS F S)) (sInf (DS F S'))]
    linarith
