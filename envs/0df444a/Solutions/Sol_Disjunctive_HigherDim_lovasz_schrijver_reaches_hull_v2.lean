-- Prove2me | solution 1 for Disjunctive.HigherDim.lovasz_schrijver_reaches_hull_v2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T23:41:08.527973+00:00
-- url     : https://prove2.me/submissions/86b22f52-f9b3-4265-9aeb-6dc9c913cb5c

import Mathlib
import Definitions.Def_Disjunctive_HigherDim_Basic
import Definitions.Def_Disjunctive_HigherDim_Lifts
import Definitions.Def_Disjunctive_HigherDim_BoundRows



namespace Disjunctive.HigherDim

lemma hd_row_single {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) (k : Fin n) (c : ℝ)
    (hi : A i = Pi.single k c) (x : Fin n → ℝ) : (A.mulVec x) i = c * x k := by
  simp [Matrix.mulVec, dotProduct, hi, Pi.single_apply]

lemma hd_poly_nonneg {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ}
    {Nprime : Finset (Fin n)} (hK : HasBoundRows A b Nprime) {x : Fin n → ℝ}
    (hx : x ∈ Poly A b) (k : Fin n) : 0 ≤ x k := by
  obtain ⟨i, hi, hb⟩ := hK.1 k
  have := hx i
  rw [hd_row_single A i k 1 hi, hb] at this
  linarith

lemma hd_poly_le_one {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ}
    {Nprime : Finset (Fin n)} (hK : HasBoundRows A b Nprime) {x : Fin n → ℝ}
    (hx : x ∈ Poly A b) (k : Fin n) (hk : k ∈ Nprime) : x k ≤ 1 := by
  obtain ⟨i, hi, hb⟩ := hK.2 k hk
  have hi' : A i = Pi.single k (-1) := by rw [hi, Pi.single_neg]
  have := hx i
  rw [hd_row_single A i k (-1) hi', hb] at this
  linarith

lemma hd_poly_convex {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    Convex ℝ (Poly A b) := by
  intro x hx y hy a c ha hc hac i
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have h1 := mul_le_mul_of_nonneg_left (hx i) ha
  have h2 := mul_le_mul_of_nonneg_left (hy i) hc
  have : b i = a * b i + c * b i := by rw [← add_mul, hac, one_mul]
  linarith

lemma hd_face_slice {n : ℕ} (T : Set (Fin n → ℝ)) (k : Fin n) (c s : ℝ) (hs : s ≠ 0)
    (h : ∀ z ∈ T, 0 ≤ s * (z k - c)) :
    convexHull ℝ T ∩ {x | x k = c} ⊆ convexHull ℝ (T ∩ {x | x k = c}) := by
  classical
  rintro x ⟨hx, hxk⟩
  rw [mem_convexHull_iff_exists_fintype] at hx
  obtain ⟨ι, _, w, z, hw0, hw1, hz, rfl⟩ := hx
  have hsum : ∑ i, w i * (s * (z i k - c)) = 0 := by
    have e : (∑ i, w i • z i) k = ∑ i, w i * z i k := by simp [Finset.sum_apply]
    simp only [Set.mem_setOf_eq] at hxk
    have e2 : ∑ i, w i * (s * (z i k - c)) = s * (∑ i, w i * z i k) - s * c * ∑ i, w i := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      congr 1; ext i; ring
    rw [e2, ← e, hxk, hw1]; ring
  have hterm :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_nonneg (hw0 i) (h _ (hz i)))).1 hsum
  rw [← Finset.centerMass_eq_of_sum_1 _ _ hw1, ← Finset.centerMass_filter_ne_zero]
  apply Finset.centerMass_mem_convexHull
  · intro i _; exact hw0 i
  · rw [Finset.sum_filter_ne_zero, hw1]; norm_num
  · intro i hi
    simp only [Finset.mem_filter] at hi
    refine ⟨hz i, ?_⟩
    have := hterm i (Finset.mem_univ _)
    rcases mul_eq_zero.1 this with h1 | h1
    · exact absurd h1 hi.2
    · rcases mul_eq_zero.1 h1 with h2 | h2
      · exact absurd h2 hs
      · show z i k = c; linarith

lemma hd_conv_slice {n : ℕ} (T : Set (Fin n → ℝ)) (k : Fin n) (h0 : ∀ z ∈ T, 0 ≤ z k)
    (h1 : ∀ z ∈ T, z k ≤ 1) :
    convexHull ℝ (convexHull ℝ T ∩ ZeroOneSet k) = convexHull ℝ (T ∩ ZeroOneSet k) := by
  apply le_antisymm
  · apply convexHull_min _ (convex_convexHull _ _)
    rintro x ⟨hx, hk | hk⟩
    · have := hd_face_slice T k 0 1 one_ne_zero (by intro z hz; simpa using h0 z hz) ⟨hx, hk⟩
      exact convexHull_mono (Set.inter_subset_inter_right _ (fun y hy => Or.inl hy)) this
    · have := hd_face_slice T k 1 (-1) (by norm_num)
        (by intro z hz; have := h1 z hz; linarith) ⟨hx, hk⟩
      exact convexHull_mono (Set.inter_subset_inter_right _ (fun y hy => Or.inr hy)) this
  · exact convexHull_mono (Set.inter_subset_inter_left _ (subset_convexHull ℝ T))

lemma hd_pj_convex {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (j : Fin n) :
    Convex ℝ (Pj A b j) := by
  rintro x ⟨y, hy⟩ x' ⟨y', hy'⟩ a c ha hc hac
  refine ⟨a • y + c • y', ?_, ?_, ?_⟩
  · intro i
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1 := mul_nonneg ha (hy.1 i)
    have h2 := mul_nonneg hc (hy'.1 i)
    have : b i = a * b i + c * b i := by rw [← add_mul, hac, one_mul]
    nlinarith
  · intro i
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1 := mul_nonneg ha (hy.2.1 i)
    have h2 := mul_nonneg hc (hy'.2.1 i)
    nlinarith
  · have e1 : y j = x j := hy.2.2
    have e2 : y' j = x' j := hy'.2.2
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, e1, e2]

theorem hd_pj_core {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (Nprime : Finset (Fin n)) (hK : HasBoundRows A b Nprime) (j : Fin n) (hj : j ∈ Nprime) :
    Pj A b j = convexHull ℝ (Poly A b ∩ ZeroOneSet j) := by
  apply le_antisymm
  · rintro x ⟨y, h1, h2, h3⟩
    -- bounds on x j
    have hl0 : 0 ≤ x j := by
      obtain ⟨i, hi, hb⟩ := hK.1 j
      have := h2 i
      rw [hd_row_single A i j 1 hi, hb] at this
      simp only at h3
      linarith
    have hl1 : x j ≤ 1 := by
      obtain ⟨i, hi, hb⟩ := hK.2 j hj
      have hi' : A i = Pi.single j (-1) := by rw [hi, Pi.single_neg]
      have := h1 i
      rw [hd_row_single A i j (-1) hi', hd_row_single A i j (-1) hi', hb] at this
      simp only at h3
      linarith
    simp only at h1 h2 h3
    rcases eq_or_lt_of_le hl0 with h0 | h0
    · apply subset_convexHull
      refine ⟨fun i => ?_, Or.inl h0.symm⟩
      have := h1 i; have := h2 i; rw [← h0] at *; linarith
    rcases eq_or_lt_of_le hl1 with h1' | h1'
    · apply subset_convexHull
      refine ⟨fun i => ?_, Or.inr h1'⟩
      have := h1 i; have := h2 i; rw [h1'] at *; linarith
    set l := x j with hl
    have hxeq : x = (1 - l) • ((1 - l)⁻¹ • (x - y)) + l • (l⁻¹ • y) := by
      rw [smul_smul, smul_smul, mul_inv_cancel₀ (by linarith), mul_inv_cancel₀ (by linarith),
        one_smul, one_smul, sub_add_cancel]
    rw [hxeq]
    apply convex_convexHull ℝ _ _ _ (by linarith) h0.le (by ring)
    · apply subset_convexHull
      refine ⟨fun i => ?_, Or.inl ?_⟩
      · simp only [Matrix.mulVec_smul, Matrix.mulVec_sub, Pi.smul_apply, Pi.sub_apply,
          smul_eq_mul]
        rw [le_inv_mul_iff₀ (by linarith)]
        have := h1 i
        nlinarith
      · simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, ← h3, ← hl, sub_self, mul_zero]
    · apply subset_convexHull
      refine ⟨fun i => ?_, Or.inr ?_⟩
      · simp only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
        rw [le_inv_mul_iff₀ h0]
        have := h2 i
        nlinarith
      · simp only [Pi.smul_apply, smul_eq_mul, h3, ← hl]
        exact inv_mul_cancel₀ h0.ne'
  · apply convexHull_min _ (hd_pj_convex A b j)
    rintro x ⟨hx, hxj | hxj⟩
    · refine ⟨0, fun i => ?_, fun i => ?_, ?_⟩
      · simp only [Matrix.mulVec_zero, Pi.zero_apply, hxj]; have := hx i; linarith
      · simp [hxj]
      · simp [hxj]
    · refine ⟨x, fun i => ?_, fun i => ?_, rfl⟩
      · simp [hxj]
      · simp only [hxj, mul_one]; have := hx i; linarith

theorem hd_ls_one_core {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (Nprime : Finset (Fin n)) (hK : HasBoundRows A b Nprime) :
    ∀ j ∈ Nprime, NOp A b Nprime ⊆ convexHull ℝ (Poly A b ∩ ZeroOneSet j) := by
  intro j hj x ⟨Y, hY⟩
  rw [← hd_pj_core A b Nprime hK j hj]
  exact ⟨fun k => Y k j, (hY.2.2 j hj).1, (hY.2.2 j hj).2, hY.2.1 j hj⟩

theorem hd_iter_core {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (Nprime : Finset (Fin n)) (hK : HasBoundRows A b Nprime) (l : List (Fin n))
    (hl : ∀ j ∈ l, j ∈ Nprime) :
    IteratedSplit (Poly A b) l = convexHull ℝ (Poly A b ∩ ⋂ j ∈ l.toFinset, ZeroOneSet j) := by
  induction l using List.reverseRecOn with
  | nil =>
    simp only [IteratedSplit, List.foldl_nil, List.toFinset_nil, Finset.notMem_empty,
      Set.iInter_of_empty, Set.iInter_univ, Set.inter_univ]
    exact (hd_poly_convex A b).convexHull_eq.symm
  | append_singleton l k ih =>
    have ih' := ih (fun j hj => hl j (by simp [hj]))
    have hk : k ∈ Nprime := hl k (by simp)
    unfold IteratedSplit at ih' ⊢
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ih']
    unfold SplitConvexify
    rw [hd_conv_slice]
    · congr 1
      ext x
      simp only [Set.mem_inter_iff, Set.mem_iInter, List.mem_toFinset, List.mem_append,
        List.mem_singleton]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨h1, fun j hj => hj.elim (h2 j) (fun e => e ▸ h3)⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, fun j hj => h2 j (Or.inl hj)⟩, h2 k (Or.inr rfl)⟩
    · intro z hz; exact hd_poly_nonneg hK hz.1 k
    · intro z hz; exact hd_poly_le_one hK hz.1 k hk

theorem hd_full_core {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (Nprime : Finset (Fin n)) (hK : HasBoundRows A b Nprime) (l : List (Fin n))
    (heq : l.toFinset = Nprime) :
    IteratedSplit (Poly A b) l = convexHull ℝ (K0Set A b Nprime) := by
  rw [hd_iter_core A b Nprime hK l (fun j hj => heq ▸ List.mem_toFinset.2 hj), heq]
  rfl

lemma hd_K0_sub_NOp {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (Nprime : Finset (Fin n)) (x : Fin n → ℝ) (hx : x ∈ Poly A b)
    (h01 : ∀ j ∈ Nprime, x j = 0 ∨ x j = 1) : x ∈ NOp A b Nprime := by
  refine ⟨fun i j => x i * x j, fun i j => mul_comm _ _, fun j hj => ?_, fun j hj => ⟨?_, ?_⟩⟩
  · rcases h01 j hj with h | h <;> simp [h]
  · intro i
    have e : (fun k => (fun i j => x i * x j) k j) = x j • x := by
      funext k; simp [mul_comm]
    simp only [e, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
    have := hx i
    rcases h01 j hj with h | h <;> simp [h] <;> linarith
  · intro i
    have e : (fun k => (fun i j => x i * x j) k j) = x j • x := by
      funext k; simp [mul_comm]
    simp only [e, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
    have := hx i
    rcases h01 j hj with h | h <;> simp [h] <;> linarith

theorem hd_ls_hull_core {n p : ℕ} {mA : Fin (p + 1) → ℕ}
    (A : (t : Fin (p + 1)) → Matrix (Fin (mA t)) (Fin n) ℝ)
    (b : (t : Fin (p + 1)) → Fin (mA t) → ℝ) (Nprime : Finset (Fin n)) (hp : Nprime.card = p)
    (hK : ∀ t, HasBoundRows (A t) (b t) Nprime)
    (hStep : ∀ t : Fin p, Poly (A t.succ) (b t.succ) = NOp (A t.castSucc) (b t.castSucc) Nprime) :
    Poly (A (Fin.last p)) (b (Fin.last p)) = convexHull ℝ (K0Set (A 0) (b 0) Nprime) := by
  have key : ∀ t : Fin (p + 1), ∀ S : Finset (Fin n), S ⊆ Nprime → S.card = t.val →
      Poly (A t) (b t) ⊆
        convexHull ℝ (Poly (A 0) (b 0) ∩ {x | ∀ j ∈ S, x j = 0 ∨ x j = 1}) := by
    intro t
    induction t using Fin.induction with
    | zero =>
      intro S _ hc x hx
      rw [Fin.val_zero, Finset.card_eq_zero] at hc
      subst hc
      exact subset_convexHull ℝ _ ⟨hx, by simp⟩
    | succ i ih =>
      intro S hS hc x hx
      rw [hStep i] at hx
      rw [Fin.val_succ] at hc
      obtain ⟨k, hk⟩ : S.Nonempty := Finset.card_pos.1 (by omega)
      have hS' := ih (S.erase k) ((Finset.erase_subset _ _).trans hS)
        (by rw [Finset.card_erase_of_mem hk, hc, Fin.coe_castSucc]; omega)
      have h1 := hd_ls_one_core (A i.castSucc) (b i.castSucc) Nprime (hK _) k (hS hk) hx
      have h2 := convexHull_mono (𝕜 := ℝ) (Set.inter_subset_inter_left (ZeroOneSet k) hS') h1
      rw [hd_conv_slice] at h2
      · refine convexHull_mono ?_ h2
        rintro y ⟨⟨hy0, hyS⟩, hyk⟩
        refine ⟨hy0, fun j hj => ?_⟩
        by_cases hjk : j = k
        · subst hjk; exact hyk
        · exact hyS j (Finset.mem_erase.2 ⟨hjk, hj⟩)
      · intro z hz; exact hd_poly_nonneg (hK 0) hz.1 k
      · intro z hz; exact hd_poly_le_one (hK 0) hz.1 k (hS hk)
  have sub : ∀ t : Fin (p + 1), K0Set (A 0) (b 0) Nprime ⊆ Poly (A t) (b t) := by
    intro t
    induction t using Fin.induction with
    | zero => exact Set.inter_subset_left
    | succ i ih =>
      intro x hx
      rw [hStep i]
      apply hd_K0_sub_NOp _ _ _ _ (ih hx)
      intro j hj
      have := hx.2
      simp only [Set.mem_iInter] at this
      exact this j hj
  apply le_antisymm
  · refine (key (Fin.last p) Nprime le_rfl (by simp [hp])).trans (convexHull_mono ?_)
    rintro y ⟨hy0, hy⟩
    refine ⟨hy0, ?_⟩
    simp only [Set.mem_iInter]
    exact hy
  · exact convexHull_min (sub _) (hd_poly_convex _ _)

def hdLam {n : ℕ} (S J : Finset (Fin n)) (w : Finset (Fin n) → ℝ) : ℝ :=
  ∑ T ∈ (S \ J).powerset, (-1 : ℝ) ^ T.card * w (J ∪ T)

def hdMu {n : ℕ} (Nprime : Finset (Fin n)) (w : Finset (Fin n) → ℝ)
    (v : Finset (Fin n) → Fin n → ℝ) (S J : Finset (Fin n)) (k : Fin n) : ℝ :=
  ∑ T ∈ (S \ J).powerset, (-1 : ℝ) ^ T.card * MomentEval Nprime w v (J ∪ T) k

lemma hd_mobius {n : ℕ} (f : Finset (Fin n) → ℝ) (S : Finset (Fin n)) :
    ∑ J ∈ S.powerset, ∑ T ∈ (S \ J).powerset, (-1 : ℝ) ^ T.card * f (J ∪ T) = f ∅ := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.sum_powerset_insert ha, ← ih, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro J hJ
    have haJ : a ∉ J := fun h => ha (Finset.mem_powerset.1 hJ h)
    have haSJ : a ∉ S \ J := fun h => ha (Finset.mem_sdiff.1 h).1
    rw [Finset.insert_sdiff_of_notMem _ haJ, Finset.insert_sdiff_insert,
      Finset.sdiff_insert_of_notMem ha, Finset.sum_powerset_insert haSJ, add_assoc,
      add_eq_left, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro T hT
    have haT : a ∉ T := fun h => haSJ (Finset.mem_powerset.1 hT h)
    rw [Finset.card_insert_of_notMem haT, Finset.union_insert, Finset.insert_union]
    ring

lemma hd_row_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (Nprime : Finset (Fin n)) (w : Finset (Fin n) → ℝ) (v : Finset (Fin n) → Fin n → ℝ)
    (i : Fin m) (S J : Finset (Fin n)) :
    RowNLt A b Nprime w v i J (S \ J) =
      ∑ k, A i k * hdMu Nprime w v S J k - b i * hdLam S J w := by
  unfold RowNLt hdMu hdLam
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intros; apply Finset.sum_congr rfl; intros; ring
  · apply Finset.sum_congr rfl; intros; ring

lemma hd_sum_single {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) (k : Fin n) (c : ℝ)
    (hi : A i = Pi.single k c) (f : Fin n → ℝ) : ∑ k', A i k' * f k' = c * f k := by
  simp [hi, Pi.single_apply]

theorem hd_sa_core {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (Nprime : Finset (Fin n)) (hK : HasBoundRows A b Nprime) (t : ℕ) (S : Finset (Fin n))
    (hS : S ⊆ Nprime) (hc : S.card = t) :
    KtSet A b Nprime t ⊆ convexHull ℝ (Poly A b ∩ {x | ∀ j ∈ S, x j = 0 ∨ x j = 1}) := by
  classical
  rintro x ⟨w, v, hw0, hw1, hv0, hrowall⟩
  have hrow : ∀ i, ∀ J ∈ S.powerset,
      0 ≤ ∑ k, A i k * hdMu Nprime w v S J k - b i * hdLam S J w := by
    intro i J hJ
    rw [Finset.mem_powerset] at hJ
    rw [← hd_row_eq]
    apply hrowall i J (S \ J) Finset.disjoint_sdiff (hJ.trans hS) (Finset.sdiff_subset.trans hS)
    rw [Finset.union_sdiff_of_subset hJ, hc]
  have hmu0 : ∀ J ∈ S.powerset, ∀ k, 0 ≤ hdMu Nprime w v S J k := by
    intro J hJ k
    obtain ⟨i, hi, hb⟩ := hK.1 k
    have := hrow i J hJ
    rw [hd_sum_single A i k 1 hi, hb] at this
    linarith
  have hmu1 : ∀ J ∈ S.powerset, ∀ k ∈ Nprime, hdMu Nprime w v S J k ≤ hdLam S J w := by
    intro J hJ k hk
    obtain ⟨i, hi, hb⟩ := hK.2 k hk
    have hi' : A i = Pi.single k (-1) := by rw [hi, Pi.single_neg]
    have := hrow i J hJ
    rw [hd_sum_single A i k (-1) hi', hb] at this
    linarith
  have hlam0 : ∀ J ∈ S.powerset, 0 ≤ hdLam S J w := by
    intro J hJ
    rcases S.eq_empty_or_nonempty with hSe | ⟨j, hj⟩
    · subst hSe
      simp only [Finset.powerset_empty, Finset.mem_singleton] at hJ
      subst hJ
      simp [hdLam, hw0]
    · exact (hmu0 J hJ j).trans (hmu1 J hJ j (hS hj))
  have hmuJ : ∀ J ∈ S.powerset, ∀ j ∈ J, hdMu Nprime w v S J j = hdLam S J w := by
    intro J hJ j hj
    unfold hdMu hdLam MomentEval
    apply Finset.sum_congr rfl
    intro T _
    rw [if_pos (hS (Finset.mem_powerset.1 hJ hj)),
      Finset.insert_eq_of_mem (Finset.mem_union_left _ hj)]
  have hmuJ' : ∀ J ∈ S.powerset, ∀ j ∈ S, j ∉ J → hdMu Nprime w v S J j = 0 := by
    intro J hJ j hjS hjJ
    unfold hdMu MomentEval
    simp only [if_pos (hS hjS)]
    have hjm : j ∈ S \ J := Finset.mem_sdiff.2 ⟨hjS, hjJ⟩
    rw [← Finset.insert_erase hjm, Finset.sum_powerset_insert (Finset.notMem_erase j _),
      ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro T hT
    have hjT : j ∉ T := fun h => Finset.notMem_erase j _ (Finset.mem_powerset.1 hT h)
    rw [Finset.card_insert_of_notMem hjT, Finset.union_insert, Finset.insert_idem]
    ring
  have hsumlam : ∑ J ∈ S.powerset, hdLam S J w = 1 := by
    unfold hdLam; rw [hd_mobius w S, hw0]
  have hsummu : ∀ k, ∑ J ∈ S.powerset, hdMu Nprime w v S J k = x k := by
    intro k
    unfold hdMu
    rw [hd_mobius (fun U => MomentEval Nprime w v U k) S]
    unfold MomentEval
    split_ifs with hk
    · simp [hw1 k hk]
    · simp [hv0 k hk]
  set F0 := S.powerset.filter (fun J => ¬ hdLam S J w ≠ 0) with hF0
  set F1 := S.powerset.filter (fun J => hdLam S J w ≠ 0) with hF1
  set r : Fin n → ℝ := fun k => ∑ J ∈ F0, hdMu Nprime w v S J k with hr
  have hr0 : ∀ j ∈ Nprime, r j = 0 := by
    intro j hj
    apply Finset.sum_eq_zero
    intro J hJ
    obtain ⟨hJ1, hJ2⟩ := Finset.mem_filter.1 hJ
    push_neg at hJ2
    have := hmu1 J hJ1 j hj
    have := hmu0 J hJ1 j
    linarith
  have hAr : ∀ i, 0 ≤ ∑ k, A i k * r k := by
    intro i
    simp only [hr, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_nonneg
    intro J hJ
    obtain ⟨hJ1, hJ2⟩ := Finset.mem_filter.1 hJ
    push_neg at hJ2
    have := hrow i J hJ1
    rw [hJ2, mul_zero, sub_zero] at this
    exact this
  have hsumF1 : ∑ J ∈ F1, hdLam S J w = 1 := by
    rw [hF1, Finset.sum_filter_ne_zero, hsumlam]
  set pt : Finset (Fin n) → Fin n → ℝ :=
    fun J k => (hdLam S J w)⁻¹ * hdMu Nprime w v S J k + r k with hpt
  have hcm : F1.centerMass (fun J => hdLam S J w) pt = x := by
    unfold Finset.centerMass
    rw [hsumF1, inv_one, one_smul]
    ext k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hpt]
    rw [← hsummu k, ← Finset.sum_filter_add_sum_filter_not S.powerset
      (fun J => hdLam S J w ≠ 0)]
    have e1 : ∑ J ∈ F1, hdLam S J w * ((hdLam S J w)⁻¹ * hdMu Nprime w v S J k + r k) =
        ∑ J ∈ F1, hdMu Nprime w v S J k + (∑ J ∈ F1, hdLam S J w) * r k := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro J hJ
      have := (Finset.mem_filter.1 hJ).2
      rw [mul_add, ← mul_assoc, mul_inv_cancel₀ this, one_mul]
    rw [e1, hsumF1, one_mul]
  rw [← hcm]
  apply Finset.centerMass_mem_convexHull
  · intro J hJ; exact hlam0 J (Finset.mem_filter.1 hJ).1
  · rw [hsumF1]; norm_num
  · intro J hJ
    obtain ⟨hJS, hJne⟩ := Finset.mem_filter.1 hJ
    have hpos : 0 < hdLam S J w := lt_of_le_of_ne (hlam0 J hJS) (Ne.symm hJne)
    refine ⟨fun i => ?_, fun j hj => ?_⟩
    · have e : (A.mulVec (pt J)) i = (hdLam S J w)⁻¹ * ∑ k, A i k * hdMu Nprime w v S J k +
          ∑ k, A i k * r k := by
        simp only [Matrix.mulVec, dotProduct, hpt, mul_add, Finset.sum_add_distrib,
          Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl; intros; ring
      rw [e]
      have h1 := hrow i J hJS
      have h2 := hAr i
      have : b i ≤ (hdLam S J w)⁻¹ * ∑ k, A i k * hdMu Nprime w v S J k := by
        rw [le_inv_mul_iff₀ hpos]; linarith
      linarith
    · simp only [hpt, hr0 j (hS hj), add_zero]
      by_cases hjJ : j ∈ J
      · right; rw [hmuJ J hJS j hjJ, inv_mul_cancel₀ hJne]
      · left; rw [hmuJ' J hJS j hj hjJ, mul_zero]

theorem hd_sa_split_core {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (Nprime : Finset (Fin n)) (hK : HasBoundRows A b Nprime) (t : ℕ)
    (l : List (Fin n)) (hnd : l.Nodup) (hl : ∀ j ∈ l, j ∈ Nprime) (hlen : l.length = t) :
    KtSet A b Nprime t ⊆ IteratedSplit (Poly A b) l := by
  rw [hd_iter_core A b Nprime hK l hl]
  have := hd_sa_core A b Nprime hK t l.toFinset (fun j hj => hl j (List.mem_toFinset.1 hj))
    (by rw [List.toFinset_card_of_nodup hnd, hlen])
  refine this.trans (convexHull_mono ?_)
  rintro x ⟨hx, hx2⟩
  refine ⟨hx, ?_⟩
  simp only [Set.mem_iInter]
  intro j hj
  exact hx2 j hj

end Disjunctive.HigherDim

open Disjunctive.HigherDim


theorem solution {n p : ℕ} {mA : Fin (p + 1) → ℕ}
    (A : (t : Fin (p + 1)) → Matrix (Fin (mA t)) (Fin n) ℝ)
    (b : (t : Fin (p + 1)) → Fin (mA t) → ℝ) (Nprime : Finset (Fin n)) (hp : Nprime.card = p)
    (hK : ∀ t, HasBoundRows (A t) (b t) Nprime)
    (hStep : ∀ t : Fin p, Poly (A t.succ) (b t.succ) = NOp (A t.castSucc) (b t.castSucc) Nprime) :
    Poly (A (Fin.last p)) (b (Fin.last p)) = convexHull ℝ (K0Set (A 0) (b 0) Nprime) := by
  exact hd_ls_hull_core A b Nprime hp hK hStep
