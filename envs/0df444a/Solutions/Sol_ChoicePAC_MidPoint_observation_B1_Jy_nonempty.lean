-- Prove2me | solution 1 for ChoicePAC.MidPoint.observation_B1_Jy_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T15:58:23.949654+00:00
-- url     : https://prove2.me/submissions/f3ff38e0-7c9e-44a2-af60-18b43a9c5c96

import Mathlib
import Definitions.Def_ChoicePAC_MidPoint_Model
import Definitions.Def_ChoicePAC_MidPoint_Assumptions

open ChoicePAC.MidPoint Matrix

namespace B1aux

variable {NT n m : ℕ} (I : Instance NT n m)

lemma sum_le_lam {Y : Fin n → ℝ} (hP : I.P *ᵥ Y ≤ I.lam) (h0 : 0 ≤ Y) (q : Fin NT)
    (T : Finset (Fin n)) (hT : ∀ j ∈ T, I.typ j = q) : ∑ j ∈ T, Y j ≤ I.lam q := by
  have h1 : ∑ j ∈ T, Y j = ∑ j ∈ T, I.P q j * Y j := by
    apply Finset.sum_congr rfl; intro j hj; simp [Instance.P, hT j hj]
  have h2 : ∑ j ∈ T, I.P q j * Y j ≤ ∑ j, I.P q j * Y j := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro j _ _
    apply mul_nonneg _ (h0 j)
    unfold Instance.P; split_ifs <;> norm_num
  have h3 : (I.P *ᵥ Y) q = ∑ j, I.P q j * Y j := rfl
  linarith [hP q]

/-- local optimality: if all capacity constraints are slack at a DLP-optimal `Y`,
then `Y` is optimal for problem (3). -/
lemma opt3 {Y : Fin n → ℝ} (hY : I.IsDLPOptimal I.C I.lam Y)
    (hslack : ∀ i, (I.Abar *ᵥ Y) i < I.C i) :
    ∀ x : Fin n → ℝ, I.P *ᵥ x ≤ I.lam → 0 ≤ x → I.rbar ⬝ᵥ x ≤ I.rbar ⬝ᵥ Y := by
  intro z hPz hz
  obtain ⟨⟨hA, hP, h0⟩, hopt⟩ := hY
  have hev : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ∀ i, (I.Abar *ᵥ (Y + ε • (z - Y))) i ≤ I.C i := by
    rw [Filter.eventually_all]
    intro i
    have hc : Continuous (fun ε : ℝ => (I.Abar *ᵥ Y) i + ε * (I.Abar *ᵥ (z - Y)) i) := by
      fun_prop
    have ht := (hc.tendsto 0)
    simp only [zero_mul, add_zero] at ht
    have := ht.eventually (gt_mem_nhds (hslack i))
    apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
    filter_upwards [this] with ε hε
    rw [Matrix.mulVec_add, Matrix.mulVec_smul]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  have hev2 : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ε ∈ Set.Ioo 0 1 :=
    Ioo_mem_nhdsGT (by norm_num)
  obtain ⟨ε, hε, hε2⟩ := (hev.and hev2).exists
  have hfeas : I.DLPFeasible I.C I.lam (Y + ε • (z - Y)) := by
    refine ⟨fun i => hε i, ?_, ?_⟩
    · intro q
      have e : Y + ε • (z - Y) = (1 - ε) • Y + ε • z := by
        ext j; simp; ring
      rw [e, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have := hP q; have := hPz q
      nlinarith [hε2.1, hε2.2]
    · intro j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.zero_apply]
      have : (0:ℝ) ≤ Y j := h0 j
      have : (0:ℝ) ≤ z j := hz j
      nlinarith [hε2.1, hε2.2]
  have := hopt _ hfeas
  rw [dotProduct_add, dotProduct_smul, dotProduct_sub, smul_eq_mul] at this
  have hpos := hε2.1
  by_contra hcon
  push Not at hcon
  nlinarith

end B1aux

theorem solution {NT n m : ℕ} (I : Instance NT n m) (hI : I.IsValid)
    (h21 : I.Assumption21) (h22 : I.Assumption22) (Y : Fin n → ℝ)
    (hY : I.IsDLPOptimal I.C I.lam Y) :
    (I.Jy Y).Nonempty := by
  classical
  obtain ⟨⟨hA, hP, h0⟩, hopt⟩ := hY
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  have hle : ∀ j, Y j ≤ I.lam (I.typ j) := by
    intro j
    have := B1aux.sum_le_lam I hP h0 (I.typ j) {j} (by simp)
    simpa using this
  -- every component is 0 or full
  have h01 : ∀ j, Y j = 0 ∨ Y j = I.lam (I.typ j) := by
    intro j
    have : j ∉ I.Jy Y := by rw [hne]; simp
    simp only [Instance.Jy, Finset.mem_filter, Finset.mem_univ, true_and, not_and_or,
      not_lt] at this
    rcases this with h | h
    · left; have : (0:ℝ) ≤ Y j := h0 j
      linarith
    · right; linarith [hle j]
  -- offers in the same type as a full nonzero offer are zero
  have hzero : ∀ j j', Y j = I.lam (I.typ j) → Y j ≠ 0 → j' ≠ j → I.typ j' = I.typ j →
      Y j' = 0 := by
    intro j j' hj hj0 hne' ht
    have := B1aux.sum_le_lam I hP h0 (I.typ j) {j, j'} (by
      intro x hx; simp at hx; rcases hx with rfl | rfl <;> simp [ht])
    rw [Finset.sum_pair (Ne.symm hne')] at this
    have : (0:ℝ) ≤ Y j' := h0 j'
    linarith
  set Act := I.dlpActive Y
  have memAct : ∀ r, r ∈ Act ↔ I.dlpRow r ⬝ᵥ Y = I.dlpRhs r := by
    intro r; simp [Act, Instance.dlpActive]
  set L : Finset (Fin n) := Finset.univ.filter (fun j => Y j ≠ 0) with hL
  set Z : Finset (Fin n) := Finset.univ.filter (fun j => Y j = 0) with hZ
  have rowj : ∀ j, I.dlpRow (Sum.inr (Sum.inr j)) = -Pi.single j 1 := by
    intro j; ext x
    simp only [Instance.dlpRow, Pi.neg_apply, Pi.single_apply]
    split_ifs <;> norm_num
  have actZ : ∀ j ∈ Z, Sum.inr (Sum.inr j) ∈ Act := by
    intro j hj
    rw [memAct, rowj]
    simp [Z] at hj
    simp [Instance.dlpRhs, hj]
  have actL : ∀ j ∈ L, Sum.inr (Sum.inl (I.typ j)) ∈ Act := by
    intro j hj
    simp [L] at hj
    have hfull : Y j = I.lam (I.typ j) := (h01 j).resolve_left hj
    rw [memAct]
    show (I.P *ᵥ Y) (I.typ j) = I.lam (I.typ j)
    show ∑ x, I.P (I.typ j) x * Y x = _
    rw [Finset.sum_eq_single j]
    · simp [Instance.P, hfull]
    · intro b _ hb
      by_cases ht : I.typ b = I.typ j
      · simp [hzero j b hfull hj hb ht]
      · simp [Instance.P, ht]
    · simp
  have actB : ∀ i ∈ I.BA Y, (Sum.inl i : Fin m ⊕ Fin NT ⊕ Fin n) ∈ Act := by
    intro i hi
    rw [memAct]
    simp [Instance.BA] at hi
    exact hi
  -- span
  have hspan : Submodule.span ℝ (I.dlpRow '' ↑Act) = ⊤ := by
    set S := Submodule.span ℝ (I.dlpRow '' ↑Act)
    have hsingle : ∀ j, (Pi.single j (1 : ℝ) : Fin n → ℝ) ∈ S := by
      intro j
      by_cases hj : Y j = 0
      · have : I.dlpRow (Sum.inr (Sum.inr j)) ∈ S :=
          Submodule.subset_span ⟨_, actZ j (by simp [Z, hj]), rfl⟩
        rw [rowj] at this
        simpa using S.neg_mem this
      · have hfull : Y j = I.lam (I.typ j) := (h01 j).resolve_left hj
        have hrow : I.dlpRow (Sum.inr (Sum.inl (I.typ j))) ∈ S :=
          Submodule.subset_span ⟨_, actL j (by simp [L, hj]), rfl⟩
        set T := (Finset.univ.filter (fun b => I.typ b = I.typ j)).erase j
        have hT : ∀ b ∈ T, (Pi.single b (1 : ℝ) : Fin n → ℝ) ∈ S := by
          intro b hb
          simp [T] at hb
          have hb0 := hzero j b hfull hj hb.1 hb.2
          have : I.dlpRow (Sum.inr (Sum.inr b)) ∈ S :=
            Submodule.subset_span ⟨_, actZ b (by simp [Z, hb0]), rfl⟩
          rw [rowj] at this
          simpa using S.neg_mem this
        have heq : (Pi.single j (1 : ℝ) : Fin n → ℝ) =
            I.dlpRow (Sum.inr (Sum.inl (I.typ j))) - ∑ b ∈ T, Pi.single b 1 := by
          ext x
          simp only [Pi.sub_apply, Finset.sum_apply, Instance.dlpRow, Instance.P, Pi.single_apply,
            Finset.sum_ite_eq, Finset.sum_ite_eq']
          by_cases hx : x = j
          · subst hx; simp [T]
          · by_cases htx : I.typ x = I.typ j
            · simp [T, htx, hx]
            · simp [T, htx, hx]
        rw [heq]
        exact S.sub_mem hrow (S.sum_mem hT)
    rw [Submodule.eq_top_iff']
    intro x
    rw [pi_eq_sum_univ x]
    refine S.sum_mem (fun j _ => S.smul_mem _ ?_)
    have : (fun j' => if j = j' then (1:ℝ) else 0) = Pi.single j 1 := by
      ext j'; simp [Pi.single_apply, eq_comm]
    rw [this]; exact hsingle j
  have hcard := h21.1 Y ⟨hA, hP, h0⟩ hspan
  -- lower bound on the card of the active set
  set S1 : Finset (Fin m ⊕ Fin NT ⊕ Fin n) := Z.map ⟨fun j => Sum.inr (Sum.inr j),
    fun a b h => by simpa using h⟩
  set S2 : Finset (Fin m ⊕ Fin NT ⊕ Fin n) := L.image (fun j => Sum.inr (Sum.inl (I.typ j)))
  set S3 : Finset (Fin m ⊕ Fin NT ⊕ Fin n) := (I.BA Y).map ⟨Sum.inl, Sum.inl_injective⟩
  have hS2 : S2.card = L.card := by
    apply Finset.card_image_of_injOn
    intro a ha b hb hab
    simp only [Sum.inr.injEq, Sum.inl.injEq] at hab
    by_contra hne'
    simp [L] at ha hb
    exact hb (hzero a b ((h01 a).resolve_left ha) ha (Ne.symm hne') hab.symm)
  have hsub : S1 ∪ S2 ∪ S3 ⊆ Act := by
    intro r hr
    simp only [Finset.mem_union, S1, S2, S3, Finset.mem_map, Finset.mem_image,
      Function.Embedding.coeFn_mk] at hr
    rcases hr with (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) | ⟨i, hi, rfl⟩
    · exact actZ j hj
    · exact actL j hj
    · exact actB i hi
  have hd12 : Disjoint S1 S2 := by
    rw [Finset.disjoint_left]; intro r h1 h2
    simp only [S1, S2, Finset.mem_map, Finset.mem_image, Function.Embedding.coeFn_mk] at h1 h2
    obtain ⟨a, _, rfl⟩ := h1; obtain ⟨b, _, hb⟩ := h2; cases hb
  have hd3 : Disjoint (S1 ∪ S2) S3 := by
    rw [Finset.disjoint_left]; intro r h1 h3
    simp [S1, S2, S3] at h1 h3
    obtain ⟨i, _, rfl⟩ := h3
    rcases h1 with ⟨a, _, h⟩ | ⟨b, _, h⟩ <;> simp at h
  have hZL : Z.card + L.card = n := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun j => Y j = 0)
    simpa [Z, L] using this
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hd3, Finset.card_union_of_disjoint hd12, hS2] at hc
  simp only [S1, S3, Finset.card_map] at hc
  have hBA : I.BA Y = ∅ := by
    have e1 : Act.card = n := hcard
    rw [← Finset.card_eq_zero]; omega
  have hslack : ∀ i, (I.Abar *ᵥ Y) i < I.C i := by
    intro i
    have : i ∉ I.BA Y := by rw [hBA]; simp
    simp [Instance.BA] at this
    exact lt_of_le_of_ne (hA i) this
  exact h22 Y ⟨hP, h0, B1aux.opt3 I ⟨⟨hA, hP, h0⟩, hopt⟩ hslack⟩ hA
