-- Prove2me | solution 1 for FuzzyGames.Walras.zero_not_mem_convexHull_Q
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T01:13:14.634582+00:00
-- url     : https://prove2.me/submissions/fef29cf9-ff5e-494f-b661-90c0dcb1e6a2

import Mathlib
import Definitions.Def_FuzzyGames_Walras_Basic



namespace FuzzyGames.Walras

open Set Pointwise

variable {n l : ℕ}

lemma dot_add' (p y z : Fin l → ℝ) : dot p (y + z) = dot p y + dot p z := by
  unfold dot; simp [mul_add, Finset.sum_add_distrib]

lemma dot_smul' (p : Fin l → ℝ) (a : ℝ) (y : Fin l → ℝ) : dot p (a • y) = a * dot p y := by
  unfold dot; simp [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring)

lemma dot_sub' (p y z : Fin l → ℝ) : dot p (y - z) = dot p y - dot p z := by
  unfold dot; simp [mul_sub, Finset.sum_sub_distrib]

lemma dot_zero' (p : Fin l → ℝ) : dot p 0 = 0 := by simp [dot]

lemma dot_sum' (p : Fin l → ℝ) {ι : Type*} (s : Finset ι) (f : ι → Fin l → ℝ) :
    dot p (∑ i ∈ s, f i) = ∑ i ∈ s, dot p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [dot_zero']
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, dot_add', ih]

lemma mem_Ytau {E : Economy n l} {τ : Fin n → ℝ} {s : Fin l → ℝ} (h : s ∈ E.Ytau τ) :
    ∃ y : Fin n → Fin l → ℝ, (∀ i, y i ∈ E.Y i) ∧ s = ∑ i, τ i • y i := by
  unfold Economy.Ytau at h
  rw [Set.mem_finset_sum] at h
  obtain ⟨g, hg, hs⟩ := h
  have : ∀ i, ∃ y, y ∈ E.Y i ∧ τ i • y = g i := fun i => by
    obtain ⟨y, hy, e⟩ := hg (Finset.mem_univ i); exact ⟨y, hy, e⟩
  choose y hy he using this
  exact ⟨y, hy, by rw [← hs]; exact Finset.sum_congr rfl (fun i _ => (he i).symm)⟩

lemma mem_Ytau_of {E : Economy n l} {τ : Fin n → ℝ} (y : Fin n → Fin l → ℝ) (hy : ∀ i, y i ∈ E.Y i) :
    ∑ i, τ i • y i ∈ E.Ytau τ := by
  unfold Economy.Ytau
  rw [Set.mem_finset_sum]
  exact ⟨fun i => τ i • y i, fun {i} _ => Set.smul_mem_smul_set (hy i), rfl⟩

theorem walras_sub_core (E : Economy n l) (hE : E.Assumptions) : E.walras ⊆ E.fuzzyCore := by
  rintro x ⟨hx1, p, hinc, hopt⟩
  refine ⟨hx1, ?_⟩
  rintro τ hτ hτ0 ⟨xt, ⟨hxt0, hxtY⟩, hxt⟩
  have hc : ∀ i, ∀ y ∈ E.Y i, dot p y ≤ dot p (x i) := by
    intro i y hy
    have : ((dot p y : ℝ) : EReal) ≤ E.income i p :=
      le_iSup₂ (f := fun y (_ : y ∈ E.Y i) => ((dot p y : ℝ) : EReal)) y hy
    rw [← hinc i] at this
    exact_mod_cast this
  have hs : ∀ i, 0 < τ i → dot p (x i) < dot p (xt i) := by
    intro i hi
    by_contra hle
    push_neg at hle
    have hbud : xt i ∈ E.budget i p := ⟨hxt0 i hi, by rw [← hinc i]; exact_mod_cast hle⟩
    exact (hxt i hi).2 (hopt i _ hbud)
  obtain ⟨y, hy, hsum⟩ := mem_Ytau hxtY
  have hτ0' : ∀ i, 0 ≤ τ i := fun i => hτ.1 i
  obtain ⟨i0, hi0⟩ : ∃ i, 0 < τ i := by
    by_contra hcon
    push_neg at hcon
    apply hτ0
    funext i
    exact le_antisymm (hcon i) (hτ0' i)
  have h1 : dot p (∑ i, τ i • xt i) = ∑ i, τ i * dot p (xt i) := by
    rw [dot_sum']; exact Finset.sum_congr rfl (fun i _ => dot_smul' _ _ _)
  have h2 : dot p (∑ i, τ i • y i) = ∑ i, τ i * dot p (y i) := by
    rw [dot_sum']; exact Finset.sum_congr rfl (fun i _ => dot_smul' _ _ _)
  have h3 : ∑ i, τ i * dot p (x i) < ∑ i, τ i * dot p (xt i) := by
    apply Finset.sum_lt_sum
    · intro i _
      rcases (hτ0' i).eq_or_lt with h | h
      · rw [← h]; simp
      · exact le_of_lt (mul_lt_mul_of_pos_left (hs i h) h)
    · exact ⟨i0, Finset.mem_univ _, mul_lt_mul_of_pos_left (hs i0 hi0) hi0⟩
  have h4 : ∑ i, τ i * dot p (y i) ≤ ∑ i, τ i * dot p (x i) :=
    Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hc i _ (hy i)) (hτ0' i))
  have : ∑ i, τ i * dot p (xt i) = ∑ i, τ i * dot p (y i) := by
    rw [← h1, ← h2, hsum]
  linarith

lemma P_convex (E : Economy n l) (hE : E.Assumptions) (i : Fin n) (xb : Fin l → ℝ)
    (hxb : 0 ≤ xb) :
    Convex ℝ {x : Fin l → ℝ | 0 ≤ x ∧ E.spref i x xb} := by
  have key : ∀ x y : Fin l → ℝ, 0 ≤ x → 0 ≤ y → E.spref i x xb → E.pref i y x →
      ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 → 0 ≤ a • x + b • y ∧ E.spref i (a • x + b • y) xb := by
    intro x y hx hy hsx hyx a b ha hb hab
    have hxx : 0 ≤ x ∧ E.pref i x x := ⟨hx, hE.refl i x hx⟩
    have hyy : 0 ≤ y ∧ E.pref i y x := ⟨hy, hyx⟩
    have h1 := hE.convex_upper i x hx hxx hyy ha hb hab
    have hz : 0 ≤ a • x + b • y := h1.1
    refine ⟨hz, hE.trans i _ x xb hz hx hxb h1.2 hsx.1, ?_⟩
    intro hcon
    exact hsx.2 (hE.trans i xb _ x hxb hz hx hcon h1.2)
  intro x hx y hy a b ha hb hab
  rcases hE.total i x y hx.1 hy.1 with h | h
  · have := key y x hy.1 hx.1 hy.2 h b a hb ha (by linarith)
    rw [add_comm] at this
    exact this
  · exact key x y hx.1 hy.1 hx.2 h a b ha hb hab

lemma Q_convex (E : Economy n l) (hE : E.Assumptions) (xbar : Fin n → Fin l → ℝ)
    (hx : xbar ∈ E.X 1) (i : Fin n) : Convex ℝ (E.Q xbar i) := by
  have hxb : 0 ≤ xbar i := hx.1 i one_pos
  exact (hE.convex_Y i).sub (P_convex E hE i _ hxb)

lemma Q_nonempty' (E : Economy n l) (hE : E.Assumptions) (xbar : Fin n → Fin l → ℝ)
    (hx : xbar ∈ E.X 1) (i : Fin n) : (E.Q xbar i).Nonempty := by
  have hxb : 0 ≤ xbar i := hx.1 i one_pos
  obtain ⟨y, hy, -⟩ := hE.pos_endowed i
  obtain ⟨z, hz0, hz⟩ := hE.nonsatiation i _ hxb
  exact ⟨y - z, y, hy, z, ⟨hz0, hz⟩, rfl⟩

def Sset (E : Economy n l) (xbar : Fin n → Fin l → ℝ) : Set (Fin l → ℝ) :=
  {s | ∃ τ ∈ stdSimplex ℝ (Fin n), ∃ q : Fin n → Fin l → ℝ,
    (∀ i, q i ∈ E.Q xbar i) ∧ s = ∑ i, τ i • q i}

lemma S_convex (E : Economy n l) (xbar : Fin n → Fin l → ℝ)
    (hQ : ∀ i, Convex ℝ (E.Q xbar i)) : Convex ℝ (Sset E xbar) := by
  rintro _ ⟨τ, hτ, q, hq, rfl⟩ _ ⟨σ, hσ, q', hq', rfl⟩ a b ha hb hab
  refine ⟨a • τ + b • σ, ⟨?_, ?_⟩, fun i => if a * τ i + b * σ i = 0 then q i else
    ((a * τ i) / (a * τ i + b * σ i)) • q i + ((b * σ i) / (a * τ i + b * σ i)) • q' i, ?_, ?_⟩
  · intro i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hτ.1 i)) (mul_nonneg hb (hσ.1 i))
  · simp [Finset.sum_add_distrib, ← Finset.mul_sum, hτ.2, hσ.2, hab]
  · intro i
    by_cases h : a * τ i + b * σ i = 0
    · simp only [h, if_true]; exact hq i
    · simp only [h, if_false]
      have h1 := mul_nonneg ha (hτ.1 i)
      have h2 := mul_nonneg hb (hσ.1 i)
      have hpos : 0 < a * τ i + b * σ i := lt_of_le_of_ne (add_nonneg h1 h2) (Ne.symm h)
      refine hQ i (hq i) (hq' i) (div_nonneg h1 hpos.le) (div_nonneg h2 hpos.le) ?_
      field_simp
  · rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : a * τ i + b * σ i = 0
    · have h1 := mul_nonneg ha (hτ.1 i)
      have h2 := mul_nonneg hb (hσ.1 i)
      have e1 : a * τ i = 0 := by linarith
      have e2 : b * σ i = 0 := by linarith
      simp only [h, if_true, Pi.add_apply, Pi.smul_apply, smul_eq_mul, zero_smul, ← smul_smul, e1, e2]
      simp [smul_smul, e1, e2]
    · simp only [h, if_false, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have e1 : (a * τ i + b * σ i) * ((a * τ i) / (a * τ i + b * σ i)) = a * τ i := by
        field_simp
      have e2 : (a * τ i + b * σ i) * ((b * σ i) / (a * τ i + b * σ i)) = b * σ i := by
        field_simp
      simp only [smul_add, smul_smul, e1, e2]

lemma Q_sub_S (E : Economy n l) (xbar : Fin n → Fin l → ℝ)
    (hne : ∀ i, (E.Q xbar i).Nonempty) (i : Fin n) : E.Q xbar i ⊆ Sset E xbar := by
  classical
  intro q hq
  choose d hd using hne
  refine ⟨fun j => if j = i then 1 else 0, ⟨fun j => by dsimp only; split_ifs <;> norm_num, by simp⟩,
    fun j => if j = i then q else d j, fun j => ?_, ?_⟩
  · by_cases h : j = i
    · subst h; simpa using hq
    · simpa [h] using hd j
  · rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj; simp [hj]
    · intro h; exact absurd (Finset.mem_univ i) h

lemma zero_not_mem_S (E : Economy n l) (xbar : Fin n → Fin l → ℝ)
    (hx : xbar ∈ E.fuzzyCore) : (0 : Fin l → ℝ) ∉ Sset E xbar := by
  rintro ⟨τ, hτ, q, hq, h0⟩
  have hq' : ∀ i, ∃ y x : Fin l → ℝ, y ∈ E.Y i ∧ (0 ≤ x ∧ E.spref i x (xbar i)) ∧ y - x = q i :=
    fun i => by obtain ⟨y, hy, x, hx', e⟩ := hq i; exact ⟨y, x, hy, hx', e⟩
  choose y x hy hxp hyx using hq'
  have hcube : τ ∈ FuzzyGames.NTUCore.cube n := by
    refine ⟨fun i => hτ.1 i, fun i => ?_⟩
    have : τ i ≤ ∑ j, τ j := Finset.single_le_sum (fun j _ => hτ.1 j) (Finset.mem_univ i)
    rw [hτ.2] at this
    exact this
  have hne : τ ≠ 0 := by
    intro h
    have := hτ.2
    rw [h] at this
    simp at this
  refine hx.2 τ hcube hne ⟨x, ⟨fun i _ => (hxp i).1, ?_⟩, fun i _ => (hxp i).2⟩
  have : ∑ i, τ i • x i = ∑ i, τ i • y i := by
    have h1 : ∑ i, τ i • (y i - x i) = 0 := by
      calc ∑ i, τ i • (y i - x i) = ∑ i, τ i • q i :=
            Finset.sum_congr rfl (fun i _ => by rw [hyx])
        _ = 0 := h0.symm
    simp only [smul_sub, Finset.sum_sub_distrib] at h1
    exact (sub_eq_zero.1 h1).symm
  rw [this]
  exact mem_Ytau_of y hy

theorem zero_not_mem_hull (E : Economy n l) (hE : E.Assumptions) (xbar : Fin n → Fin l → ℝ)
    (hx : xbar ∈ E.fuzzyCore) : (0 : Fin l → ℝ) ∉ convexHull ℝ (⋃ i, E.Q xbar i) := by
  intro h
  have hX := hx.1
  have hsub : (⋃ i, E.Q xbar i) ⊆ Sset E xbar :=
    Set.iUnion_subset (fun i => Q_sub_S E xbar (Q_nonempty' E hE xbar hX) i)
  exact zero_not_mem_S E xbar hx
    (convexHull_min hsub (S_convex E xbar (Q_convex E hE xbar hX)) h)

end FuzzyGames.Walras

open FuzzyGames.Walras


theorem solution {n l : ℕ} (E : Economy n l) (hE : E.Assumptions)
    (xbar : Fin n → Fin l → ℝ) (hx : xbar ∈ E.fuzzyCore) :
    (0 : Fin l → ℝ) ∉ convexHull ℝ (⋃ i, E.Q xbar i) := by
  exact zero_not_mem_hull E hE xbar hx
