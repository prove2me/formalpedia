-- Prove2me | solution 1 for ExecCompLP.Consistency.consistency
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T19:27:36.276646+00:00
-- url     : https://prove2.me/submissions/9f5081c3-03d3-47c8-96f6-8cb971a6b3c6

import Mathlib
import Definitions.Def_ExecCompLP_Consistency_Setting

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped Matrix

namespace ExecCompLPPf

open ExecCompLP.Consistency

variable {m n : ℕ}

/-- Cost vector of the augmented program (slack variables cost nothing). -/
noncomputable def ccost (c : Fin n → ℝ) : Fin n ⊕ Fin m → ℝ
  | Sum.inl j => c j
  | Sum.inr _ => 0

/-- The augmented point `(a, X a - b)`. -/
noncomputable def zvec (X : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (a : Fin n → ℝ) :
    Fin n ⊕ Fin m → ℝ
  | Sum.inl j => a j
  | Sum.inr i => ∑ j, X i j * a j - b i

lemma sum_augCol (X : Matrix (Fin m) (Fin n) ℝ) (d : Fin n ⊕ Fin m → ℝ) (i : Fin m) :
    ∑ k, d k * augCol X k i = ∑ j, X i j * d (Sum.inl j) - d (Sum.inr i) := by
  rw [Fintype.sum_sum_type]
  simp only [augCol, mul_ite, mul_neg, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]
  rw [sub_eq_add_neg]
  congr 1
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

lemma zvec_sum (X : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (a : Fin n → ℝ) (i : Fin m) :
    ∑ k, zvec X b a k * augCol X k i = b i := by
  rw [sum_augCol]
  simp only [zvec]
  ring

lemma cost_zvec (X : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (a : Fin n → ℝ) : ∑ k, ccost c k * zvec X b a k = ∑ j, c j * a j := by
  rw [Fintype.sum_sum_type]
  simp [ccost, zvec]

lemma mem_feasible_iff (X : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (a : Fin n → ℝ) :
    a ∈ feasibleSet X b ↔ ∀ k, 0 ≤ zvec X b a k := by
  constructor
  · rintro ⟨h1, h2⟩ (j | i)
    · exact h1 j
    · simp only [zvec]; linarith [h2 i]
  · intro h
    refine ⟨fun j => h (Sum.inl j), fun i => ?_⟩
    have := h (Sum.inr i)
    simp only [zvec] at this
    linarith

lemma eq_zero_of_inl (X : Matrix (Fin m) (Fin n) ℝ) (d : Fin n ⊕ Fin m → ℝ)
    (hd : ∀ i, ∑ k, d k * augCol X k i = 0) (hl : ∀ j, d (Sum.inl j) = 0) : d = 0 := by
  funext k
  rcases k with j | i
  · exact hl j
  · have := hd i
    rw [sum_augCol] at this
    simp only [hl, mul_zero, Finset.sum_const_zero, zero_sub, neg_eq_zero] at this
    exact this

lemma exists_step {ι : Type*} [Fintype ι] (z d : ι → ℝ) (hz : ∀ k, 0 ≤ z k)
    (h : ∀ k, 0 < z k ∨ 0 ≤ d k) : ∃ t : ℝ, 0 < t ∧ ∀ k, 0 ≤ z k + t * d k := by
  have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), ∀ k, 0 ≤ z k + t * d k := by
    rw [Filter.eventually_all]
    intro k
    rcases h k with hk | hk
    · have ht : Tendsto (fun t : ℝ => z k + t * d k) (𝓝[>] 0) (𝓝 (z k)) := by
        have hc : Continuous (fun t : ℝ => z k + t * d k) := by fun_prop
        have h2 := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
        simpa using h2
      filter_upwards [ht.eventually_const_lt hk] with t ht'
      exact ht'.le
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have : 0 ≤ t * d k := mul_nonneg (le_of_lt ht) hk
      linarith [hz k]
  obtain ⟨t, h1, h2⟩ := (hev.and self_mem_nhdsWithin).exists
  exact ⟨t, h2, h1⟩

/-- At a unique optimum, no feasible direction with non-positive cost moves the `a` part. -/
lemma no_improving_dir {ξ : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {c : Fin n → ℝ}
    {αhat : Fin n → ℝ} (hI : AssumptionI ξ b c αhat) (d : Fin n ⊕ Fin m → ℝ)
    (hd : ∀ i, ∑ k, d k * augCol ξ k i = 0)
    (hsign : ∀ k, 0 < zvec ξ b αhat k ∨ 0 ≤ d k)
    (hcost : ∑ k, ccost c k * d k ≤ 0) : ∀ j, d (Sum.inl j) = 0 := by
  have hz : ∀ k, 0 ≤ zvec ξ b αhat k := (mem_feasible_iff ξ b αhat).1 hI.1.1
  obtain ⟨t, ht, htk⟩ := exists_step _ d hz hsign
  set a' : Fin n → ℝ := fun j => αhat j + t * d (Sum.inl j) with ha'
  have hz' : ∀ k, zvec ξ b a' k = zvec ξ b αhat k + t * d k := by
    rintro (j | i)
    · simp [zvec, a']
    · have h1 := hd i
      rw [sum_augCol] at h1
      have h2 : ∑ j, ξ i j * d (Sum.inl j) = d (Sum.inr i) := by linarith
      have h3 : ∑ j, ξ i j * a' j = ∑ j, ξ i j * αhat j + t * ∑ j, ξ i j * d (Sum.inl j) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => by simp only [a']; ring
      simp only [zvec]
      rw [h3, h2]
      ring
  have hfeas : a' ∈ feasibleSet ξ b := (mem_feasible_iff ξ b a').2 fun k => by
    rw [hz' k]; exact htk k
  have hcd : ∑ k, ccost c k * d k = ∑ j, c j * d (Sum.inl j) := by
    rw [Fintype.sum_sum_type]; simp [ccost]
  have hle : ∑ j, c j * a' j ≤ ∑ j, c j * αhat j := by
    have : ∑ j, c j * a' j = ∑ j, c j * αhat j + t * ∑ j, c j * d (Sum.inl j) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by simp only [a']; ring
    rw [this]
    have : t * ∑ j, c j * d (Sum.inl j) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos ht.le (by rw [← hcd]; exact hcost)
    linarith
  have hmin : IsMinimizer ξ b c a' := ⟨hfeas, fun a'' ha'' => le_trans hle (hI.1.2 a'' ha'')⟩
  have heq := hI.2 a' hmin
  intro j
  have := congrFun heq j
  simp only [a'] at this
  have h0 : t * d (Sum.inl j) = 0 := by linarith
  rcases mul_eq_zero.1 h0 with h | h
  · exact absurd h ht.ne'
  · exact h

lemma exists_basis {N : ℕ} {ι : Type*} [Fintype ι] (p : ι → Prop) [DecidablePred p]
    (h : (Finset.univ.filter p).card = N) :
    ∃ E : Fin N → ι, Function.Injective E ∧ (∀ r, p (E r)) ∧ ∀ k, p k → ∃ r, E r = k := by
  set s := Finset.univ.filter p
  have hs : Fintype.card s = N := by rw [Fintype.card_coe]; exact h
  let e : s ≃ Fin N := Fintype.equivFinOfCardEq hs
  refine ⟨fun r => (e.symm r).1, ?_, ?_, ?_⟩
  · intro r r' hrr
    exact e.symm.injective (Subtype.ext hrr)
  · intro r
    exact (Finset.mem_filter.1 (e.symm r).2).2
  · intro k hk
    exact ⟨e ⟨k, Finset.mem_filter.2 ⟨Finset.mem_univ _, hk⟩⟩, by simp⟩

lemma card_pos (ξ : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (a : Fin n → ℝ)
    (hnd : Nondegenerate ξ b a) :
    (Finset.univ.filter (fun k : Fin n ⊕ Fin m => 0 < zvec ξ b a k)).card = m := by
  unfold Nondegenerate at hnd
  have e1 : (Finset.univ.filter (fun k : Fin n ⊕ Fin m => 0 < zvec ξ b a k)).card =
      (Finset.univ.filter (fun j => 0 < a j)).card
        + (Finset.univ.filter (fun i => b i < ∑ j, ξ i j * a j)).card := by
    rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, Fintype.sum_sum_type]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [zvec, sub_pos]
  rw [e1]
  exact hnd

section lift

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-- Extend a vector indexed by the basis to the whole index set, by zero. -/
noncomputable def lift (E : Fin N → ι) (v : Fin N → ℝ) : ι → ℝ :=
  fun k => ∑ r, if E r = k then v r else 0

lemma sum_mul_lift (E : Fin N → ι) (f : ι → ℝ) (v : Fin N → ℝ) :
    ∑ k, f k * lift E v k = ∑ r, f (E r) * v r := by
  simp only [lift, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp

lemma lift_apply_E {E : Fin N → ι} (hE : Function.Injective E) (v : Fin N → ℝ) (r : Fin N) :
    lift E v (E r) = v r := by
  simp [lift, hE.eq_iff]

lemma lift_apply_of_not {E : Fin N → ι} (v : Fin N → ℝ) {k : ι} (hk : ∀ r, E r ≠ k) :
    lift E v k = 0 := by
  simp [lift, hk]

lemma lift_nonneg (E : Fin N → ι) {v : Fin N → ℝ} (hv : ∀ r, 0 ≤ v r) (k : ι) :
    0 ≤ lift E v k :=
  Finset.sum_nonneg fun r _ => by
    split_ifs
    · exact hv r
    · exact le_refl 0

lemma lift_self {E : Fin N → ι} (hE : Function.Injective E) (v : ι → ℝ)
    (h : ∀ k, (∀ r, E r ≠ k) → v k = 0) : lift E (v ∘ E) = v := by
  funext k
  by_cases hk : ∃ r, E r = k
  · obtain ⟨r, rfl⟩ := hk
    rw [lift_apply_E hE]; rfl
  · push_neg at hk
    rw [lift_apply_of_not _ hk, h k hk]

lemma continuous_lift (E : Fin N → ι) (k : ι) : Continuous fun v : Fin N → ℝ => lift E v k := by
  unfold lift
  refine continuous_finset_sum _ fun r _ => ?_
  by_cases h : E r = k
  · simp only [h, if_true]; exact continuous_apply r
  · simp only [h, if_false]; exact continuous_const

end lift

/-- The basis matrix: columns `augCol X (E r)`. -/
noncomputable def Nmat (E : Fin m → Fin n ⊕ Fin m) (X : Matrix (Fin m) (Fin n) ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i r => augCol X (E r) i

lemma sum_lift_augCol (E : Fin m → Fin n ⊕ Fin m) (X : Matrix (Fin m) (Fin n) ℝ)
    (v : Fin m → ℝ) (i : Fin m) :
    ∑ k, lift E v k * augCol X k i = (Nmat E X *ᵥ v) i := by
  calc ∑ k, lift E v k * augCol X k i = ∑ k, augCol X k i * lift E v k :=
        Finset.sum_congr rfl fun k _ => mul_comm _ _
    _ = ∑ r, augCol X (E r) i * v r := sum_mul_lift E (fun k => augCol X k i) v
    _ = (Nmat E X *ᵥ v) i := by simp [Matrix.mulVec, dotProduct, Nmat]

lemma continuous_augCol (k : Fin n ⊕ Fin m) (i : Fin m) :
    Continuous fun X : Matrix (Fin m) (Fin n) ℝ => augCol X k i := by
  rcases k with j | i'
  · simp only [augCol]; exact continuous_id.matrix_elem i j
  · simp only [augCol]; exact continuous_const

lemma continuous_Nmat (E : Fin m → Fin n ⊕ Fin m) : Continuous (Nmat E) := by
  refine continuous_matrix fun i r => ?_
  simpa [Nmat] using continuous_augCol (E r) i

noncomputable def yv (E : Fin m → Fin n ⊕ Fin m) (c : Fin n → ℝ) (X : Matrix (Fin m) (Fin n) ℝ) :
    Fin m → ℝ :=
  (fun r => ccost c (E r)) ᵥ* (Nmat E X)⁻¹

noncomputable def red (E : Fin m → Fin n ⊕ Fin m) (c : Fin n → ℝ)
    (X : Matrix (Fin m) (Fin n) ℝ) (k : Fin n ⊕ Fin m) : ℝ :=
  ccost c k - ∑ i, yv E c X i * augCol X k i

noncomputable def wv (E : Fin m → Fin n ⊕ Fin m) (b : Fin m → ℝ) (X : Matrix (Fin m) (Fin n) ℝ) :
    Fin m → ℝ :=
  (Nmat E X)⁻¹ *ᵥ b

lemma red_E (E : Fin m → Fin n ⊕ Fin m) (c : Fin n → ℝ) (X : Matrix (Fin m) (Fin n) ℝ)
    (hX : IsUnit (Nmat E X).det) (r : Fin m) : red E c X (E r) = 0 := by
  have h1 : yv E c X ᵥ* Nmat E X = fun r => ccost c (E r) := by
    simp only [yv, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hX, Matrix.vecMul_one]
  have h2 := congrFun h1 r
  simp only [Matrix.vecMul, dotProduct, Nmat, Matrix.of_apply] at h2
  simp only [red, h2, sub_self]

lemma cost_identity (E : Fin m → Fin n ⊕ Fin m) (c : Fin n → ℝ) (X : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (z : Fin n ⊕ Fin m → ℝ) (hz : ∀ i, ∑ k, z k * augCol X k i = b i) :
    ∑ k, ccost c k * z k = ∑ k, red E c X k * z k + ∑ i, yv E c X i * b i := by
  have hswap : ∑ k, (∑ i, yv E c X i * augCol X k i) * z k = ∑ i, yv E c X i * b i := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hz i, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  simp only [red, sub_mul, Finset.sum_sub_distrib]
  rw [hswap]
  ring

/-- Deterministic core: near `ξ`, the perturbed program has a unique minimizer close to `αhat`. -/
theorem local_good {ξ : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {c : Fin n → ℝ}
    {αhat : Fin n → ℝ} (hI : AssumptionI ξ b c αhat) (hnd : Nondegenerate ξ b αhat)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X in 𝓝 ξ, ∃ a, IsMinimizer X b c a ∧ (∀ a', IsMinimizer X b c a' → a' = a) ∧
      dist a αhat < ε := by
  classical
  have hz0 : ∀ k, 0 ≤ zvec ξ b αhat k := (mem_feasible_iff ξ b αhat).1 hI.1.1
  obtain ⟨E, hEinj, hEp, hEsurj⟩ :=
    exists_basis (fun k => 0 < zvec ξ b αhat k) (card_pos ξ b αhat hnd)
  have hoff : ∀ k, (∀ r, E r ≠ k) → ¬ 0 < zvec ξ b αhat k := fun k hk hp => by
    obtain ⟨r, hr⟩ := hEsurj k hp
    exact hk r hr
  have hz0lift : lift E (zvec ξ b αhat ∘ E) = zvec ξ b αhat :=
    lift_self hEinj _ fun k hk => le_antisymm (not_lt.1 (hoff k hk)) (hz0 k)
  have hNz0 : Nmat E ξ *ᵥ (zvec ξ b αhat ∘ E) = b := by
    funext i
    rw [← sum_lift_augCol, hz0lift]
    exact zvec_sum ξ b αhat i
  have hfin : ∀ d : Fin n ⊕ Fin m → ℝ, (∀ i, ∑ k, d k * augCol ξ k i = 0) →
      (∀ k, 0 < zvec ξ b αhat k ∨ 0 ≤ d k) → ∑ k, ccost c k * d k ≤ 0 → d = 0 :=
    fun d hd hs hc => eq_zero_of_inl ξ d hd (no_improving_dir hI d hd hs hc)
  -- the basis matrix is invertible
  have hdet : (Nmat E ξ).det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have hd : ∀ i, ∑ k, lift E v k * augCol ξ k i = 0 := fun i => by
      rw [sum_lift_augCol, hv]; rfl
    have hsign : ∀ (s : ℝ) k, 0 < zvec ξ b αhat k ∨ 0 ≤ s * lift E v k := fun s k => by
      by_cases hk : ∃ r, E r = k
      · obtain ⟨r, rfl⟩ := hk
        exact Or.inl (hEp r)
      · push_neg at hk
        right
        rw [lift_apply_of_not _ hk]
        simp
    have hzero : ∀ s : ℝ, s ≠ 0 → ∑ k, ccost c k * (s * lift E v k) ≤ 0 → v = 0 := by
      intro s hs hc
      have h := hfin (fun k => s * lift E v k)
        (fun i => by simp_rw [mul_assoc, ← Finset.mul_sum, hd i, mul_zero]) (hsign s) hc
      funext r
      have h' := congrFun h (E r)
      simp only [lift_apply_E hEinj, Pi.zero_apply, mul_eq_zero] at h'
      rcases h' with h' | h'
      · exact absurd h' hs
      · exact h'
    rcases le_total (∑ k, ccost c k * lift E v k) 0 with hL | hL
    · exact hv0 (hzero 1 one_ne_zero (by simpa only [one_mul] using hL))
    · exact hv0 (hzero (-1) (by norm_num)
        (by simp only [neg_one_mul, mul_neg, Finset.sum_neg_distrib, neg_nonpos]; exact hL))
  have hU : IsUnit (Nmat E ξ).det := isUnit_iff_ne_zero.2 hdet
  -- reduced costs are strictly positive off the basis
  have hred0 : ∀ k, (∀ r, E r ≠ k) → 0 < red E c ξ k := by
    intro k hk
    by_contra hle
    push_neg at hle
    let w : Fin m → ℝ := (Nmat E ξ)⁻¹ *ᵥ (fun i => augCol ξ k i)
    let d : Fin n ⊕ Fin m → ℝ := fun k' => (Pi.single k (1:ℝ) : Fin n ⊕ Fin m → ℝ) k' - lift E w k'
    have hd : ∀ i, ∑ k', d k' * augCol ξ k' i = 0 := by
      intro i
      simp only [d, sub_mul, Finset.sum_sub_distrib, sum_lift_augCol, w]
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hU, Matrix.one_mulVec]
      simp [Pi.single_apply]
    have hs : ∀ k', 0 < zvec ξ b αhat k' ∨ 0 ≤ d k' := by
      intro k'
      by_cases hk' : ∃ r, E r = k'
      · obtain ⟨r, rfl⟩ := hk'
        exact Or.inl (hEp r)
      · push_neg at hk'
        right
        simp only [d, lift_apply_of_not _ hk', sub_zero, Pi.single_apply]
        split_ifs <;> norm_num
    have hc : ∑ k', ccost c k' * d k' = red E c ξ k := by
      simp only [d, mul_sub, Finset.sum_sub_distrib, sum_mul_lift]
      have hdot : ∑ r, ccost c (E r) * w r =
          ((fun r => ccost c (E r)) ᵥ* (Nmat E ξ)⁻¹) ⬝ᵥ (fun i => augCol ξ k i) := by
        simp only [w]
        exact Matrix.dotProduct_mulVec _ _ _
      rw [hdot]
      simp [red, yv, Pi.single_apply, dotProduct]
    have h := hfin d hd hs (by rw [hc]; exact hle)
    have h' := congrFun h k
    simp only [d, lift_apply_of_not _ hk, Pi.single_eq_same, sub_zero, Pi.zero_apply] at h'
    exact one_ne_zero h'
  -- continuity
  have hNc := continuous_Nmat E
  have hinv : ContinuousAt (fun X => (Nmat E X)⁻¹) ξ := by
    have h1 : ContinuousAt Ring.inverse (Nmat E ξ).det := by
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ hdet
    exact (continuousAt_matrix_inv _ h1).comp hNc.continuousAt
  have hw : ContinuousAt (wv E b) ξ :=
    ((continuous_id.matrix_mulVec continuous_const :
      Continuous fun M : Matrix (Fin m) (Fin m) ℝ => M *ᵥ b).continuousAt).comp hinv
  have hy : ContinuousAt (yv E c) ξ :=
    ((continuous_const.matrix_vecMul continuous_id :
      Continuous fun M : Matrix (Fin m) (Fin m) ℝ => (fun r => ccost c (E r)) ᵥ* M).continuousAt).comp
      hinv
  have hred : ∀ k, ContinuousAt (fun X => red E c X k) ξ := by
    intro k
    unfold red
    refine continuousAt_const.sub ?_
    refine tendsto_finset_sum _ fun i _ => ?_
    exact ((continuous_apply i).continuousAt.comp hy).mul (continuous_augCol k i).continuousAt
  have hwξ : wv E b ξ = zvec ξ b αhat ∘ E := by
    calc wv E b ξ = (Nmat E ξ)⁻¹ *ᵥ (Nmat E ξ *ᵥ (zvec ξ b αhat ∘ E)) := by rw [hNz0]; rfl
      _ = zvec ξ b αhat ∘ E := by
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hU, Matrix.one_mulVec]
  have haX : ContinuousAt (fun X => fun j => lift E (wv E b X) (Sum.inl j)) ξ :=
    ((continuous_pi fun j => continuous_lift E (Sum.inl j)).continuousAt).comp hw
  have haξ : (fun j => lift E (wv E b ξ) (Sum.inl j)) = αhat := by
    rw [hwξ, hz0lift]
    rfl
  have h1 : ∀ᶠ X in 𝓝 ξ, IsUnit (Nmat E X).det :=
    (Filter.Tendsto.eventually_ne (hNc.matrix_det.tendsto ξ) hdet).mono
      fun X h => isUnit_iff_ne_zero.2 h
  have h2 : ∀ᶠ X in 𝓝 ξ, ∀ r, 0 < wv E b X r := by
    rw [Filter.eventually_all]
    intro r
    have hr : ContinuousAt (fun X => wv E b X r) ξ := (continuous_apply r).continuousAt.comp hw
    refine Filter.Tendsto.eventually_const_lt ?_ hr
    show 0 < wv E b ξ r
    rw [hwξ]
    exact hEp r
  have h3 : ∀ᶠ X in 𝓝 ξ, ∀ k, (∀ r, E r ≠ k) → 0 < red E c X k := by
    rw [Filter.eventually_all]
    intro k
    by_cases hk : ∀ r, E r ≠ k
    · exact (Filter.Tendsto.eventually_const_lt (hred0 k hk) (hred k)).mono fun X h _ => h
    · exact Filter.Eventually.of_forall fun X h => absurd h hk
  have h4 : ∀ᶠ X in 𝓝 ξ, dist (fun j => lift E (wv E b X) (Sum.inl j)) αhat < ε := by
    have := haX.preimage_mem_nhds (Metric.ball_mem_nhds _ hε)
    rw [haξ] at this
    exact this
  filter_upwards [h1, h2, h3, h4] with X hX1 hX2 hX3 hX4
  set w := wv E b X with hwdef
  set a : Fin n → ℝ := fun j => lift E w (Sum.inl j) with hadef
  have hz_nonneg : ∀ k, 0 ≤ lift E w k := lift_nonneg E (fun r => (hX2 r).le)
  have hzsum : ∀ i, ∑ k, lift E w k * augCol X k i = b i := by
    intro i
    rw [sum_lift_augCol, hwdef, wv, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hX1,
      Matrix.one_mulVec]
  have hzvec : zvec X b a = lift E w := by
    funext k
    rcases k with j | i
    · rfl
    · have h := hzsum i
      rw [sum_augCol] at h
      simp only [zvec, a]
      linarith
  have hfeas : a ∈ feasibleSet X b := (mem_feasible_iff X b a).2 (by rw [hzvec]; exact hz_nonneg)
  have hred_nonneg : ∀ k, 0 ≤ red E c X k := by
    intro k
    by_cases hk : ∃ r, E r = k
    · obtain ⟨r, rfl⟩ := hk
      rw [red_E E c X hX1 r]
    · push_neg at hk
      exact (hX3 k hk).le
  have hredz : ∑ k, red E c X k * lift E w k = 0 := by
    rw [sum_mul_lift]
    simp [red_E E c X hX1]
  have hcosta : ∑ j, c j * a j = ∑ i, yv E c X i * b i := by
    rw [← cost_zvec X b c a, hzvec, cost_identity E c X b _ hzsum, hredz, zero_add]
  have hcost' : ∀ a' ∈ feasibleSet X b,
      ∑ j, c j * a' j = ∑ k, red E c X k * zvec X b a' k + ∑ i, yv E c X i * b i := by
    intro a' _
    rw [← cost_zvec X b c a']
    exact cost_identity E c X b _ (zvec_sum X b a')
  have hmin : IsMinimizer X b c a := by
    refine ⟨hfeas, fun a' ha' => ?_⟩
    rw [hcosta, hcost' a' ha']
    have : 0 ≤ ∑ k, red E c X k * zvec X b a' k :=
      Finset.sum_nonneg fun k _ =>
        mul_nonneg (hred_nonneg k) ((mem_feasible_iff X b a').1 ha' k)
    linarith
  refine ⟨a, hmin, fun a' ha' => ?_, hX4⟩
  have hz' := (mem_feasible_iff X b a').1 ha'.1
  have hle := ha'.2 a hfeas
  rw [hcosta, hcost' a' ha'.1] at hle
  have hsum0 : ∑ k, red E c X k * zvec X b a' k = 0 := by
    have : 0 ≤ ∑ k, red E c X k * zvec X b a' k :=
      Finset.sum_nonneg fun k _ => mul_nonneg (hred_nonneg k) (hz' k)
    linarith
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (fun k _ => mul_nonneg (hred_nonneg k) (hz' k))).1 hsum0
  have hoff' : ∀ k, (∀ r, E r ≠ k) → zvec X b a' k = 0 := by
    intro k hk
    have := hterm k (Finset.mem_univ _)
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (hX3 k hk).ne'
    · exact h
  have hself := lift_self hEinj (zvec X b a') hoff'
  have hNv : Nmat E X *ᵥ (zvec X b a' ∘ E) = b := by
    funext i
    rw [← sum_lift_augCol, hself]
    exact zvec_sum X b a' i
  have hvw : zvec X b a' ∘ E = w := by
    have hU' := hX1
    calc zvec X b a' ∘ E = (Nmat E X)⁻¹ *ᵥ (Nmat E X *ᵥ (zvec X b a' ∘ E)) := by
          rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hU', Matrix.one_mulVec]
      _ = w := by rw [hNv, hwdef, wv]
  funext j
  have := congrFun hself (Sum.inl j)
  rw [hvw] at this
  simp only [zvec] at this
  rw [← this]

end ExecCompLPPf

open MeasureTheory Filter Topology ExecCompLP.Consistency in
theorem solution {m n : ℕ} (ξ : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (αhat : Fin n → ℝ) (hI : AssumptionI ξ b c αhat) (hII : AssumptionII ξ)
    (hnd : Nondegenerate ξ b αhat)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (η : ℕ → Ω → Matrix (Fin m) (Fin n) ℝ)
    (hη : ∀ i j, TendstoInMeasure P (fun N ω => η N ω i j) atTop (fun _ => 0)) :
    ∀ ε > 0, Tendsto (fun N => P {ω | ¬ ∃ a, IsMinimizer (ξ + η N ω) b c a ∧
        (∀ a', IsMinimizer (ξ + η N ω) b c a' → a' = a) ∧ dist a αhat < ε})
      atTop (𝓝 0) := by
  intro ε hε
  have hev := ExecCompLPPf.local_good hI hnd hε
  obtain ⟨δ, hδ, hδgood⟩ : ∃ δ > 0, ∀ X : Matrix (Fin m) (Fin n) ℝ,
      (∀ i j, |X i j - ξ i j| < δ) → ∃ a, IsMinimizer X b c a ∧
        (∀ a', IsMinimizer X b c a' → a' = a) ∧ dist a αhat < ε := by
    have hev' : ∀ᶠ X in @nhds (Fin m → Fin n → ℝ) _ (Matrix.of.symm ξ), ∃ a, IsMinimizer X b c a ∧
        (∀ a', IsMinimizer X b c a' → a' = a) ∧ dist a αhat < ε := hev
    obtain ⟨δ, hδ, h⟩ := Metric.eventually_nhds_iff.1 hev'
    refine ⟨δ, hδ, fun X hX => h (y := Matrix.of.symm X) ?_⟩
    rw [dist_pi_lt_iff hδ]
    intro i
    rw [dist_pi_lt_iff hδ]
    intro j
    rw [Real.dist_eq]
    exact hX i j
  have hsub : ∀ N, {ω | ¬ ∃ a, IsMinimizer (ξ + η N ω) b c a ∧
        (∀ a', IsMinimizer (ξ + η N ω) b c a' → a' = a) ∧ dist a αhat < ε} ⊆
      ⋃ p : Fin m × Fin n, {ω | ENNReal.ofReal δ ≤ edist (η N ω p.1 p.2) 0} := by
    intro N ω hω
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    by_contra hcon
    push_neg at hcon
    apply hω
    apply hδgood
    intro i j
    have h := hcon (i, j)
    rw [edist_dist, Real.dist_eq, sub_zero] at h
    have h' := (ENNReal.ofReal_lt_ofReal_iff hδ).1 h
    simpa [Matrix.add_apply] using h'
  have hsum : Tendsto (fun N => ∑ p : Fin m × Fin n,
      P {ω | ENNReal.ofReal δ ≤ edist (η N ω p.1 p.2) 0}) atTop (𝓝 0) := by
    rw [show (0 : ENNReal) = ∑ _p : Fin m × Fin n, (0 : ENNReal) by simp]
    exact tendsto_finsetSum _ fun p _ => hη p.1 p.2 _ (ENNReal.ofReal_pos.2 hδ)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le)
    (fun N => (measure_mono (hsub N)).trans (measure_iUnion_fintype_le P _))
