-- Prove2me | solution 1 for ChoicePAC.MidPoint.observation_B2_W_invertible
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T16:03:27.362183+00:00
-- url     : https://prove2.me/submissions/f8c259fc-a54e-4a47-8c5c-46ccec954b4b

import Mathlib
import Definitions.Def_ChoicePAC_MidPoint_Model
import Definitions.Def_ChoicePAC_MidPoint_Assumptions

open ChoicePAC.MidPoint Matrix

namespace PertAux

variable {NT n m : ℕ} (I : Instance NT n m)

lemma row_inl (i : Fin m) (x : Fin n → ℝ) :
    I.dlpRow (Sum.inl i) ⬝ᵥ x = (I.Abar *ᵥ x) i := rfl

lemma row_P (q : Fin NT) (x : Fin n → ℝ) :
    I.dlpRow (Sum.inr (Sum.inl q)) ⬝ᵥ x = (I.P *ᵥ x) q := rfl

lemma row_sign (j : Fin n) (x : Fin n → ℝ) :
    I.dlpRow (Sum.inr (Sum.inr j)) ⬝ᵥ x = - x j := by
  simp [Instance.dlpRow, dotProduct, ite_mul]

lemma mem_active (Y : Fin n → ℝ) (r : Fin m ⊕ Fin NT ⊕ Fin n) :
    r ∈ I.dlpActive Y ↔ I.dlpRow r ⬝ᵥ Y = I.dlpRhs r := by
  simp [Instance.dlpActive]

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

lemma ev_le (a b c0 : ℝ) (h : a ≤ c0) (h' : a = c0 → b ≤ 0) :
    ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), a + ε * b ≤ c0 := by
  by_cases hac : a = c0
  · have hb := h' hac
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have : (0 : ℝ) < ε := hε
    nlinarith
  · have hlt : a < c0 := lt_of_le_of_ne h hac
    have hc : Continuous (fun ε : ℝ => a + ε * b) := by fun_prop
    have ht := hc.tendsto 0
    simp only [zero_mul, add_zero] at ht
    apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
    filter_upwards [ht.eventually (gt_mem_nhds hlt)] with ε hε
    exact hε.le

lemma feasDir {c : Fin m → ℝ} {Y d : Fin n → ℝ} (hF : I.DLPFeasible c I.lam Y)
    (hA : ∀ i, (I.Abar *ᵥ Y) i = c i → (I.Abar *ᵥ d) i ≤ 0)
    (hP : ∀ q, (I.P *ᵥ Y) q = I.lam q → (I.P *ᵥ d) q ≤ 0)
    (h0 : ∀ j, Y j = 0 → 0 ≤ d j) :
    ∃ ε : ℝ, 0 < ε ∧ I.DLPFeasible c I.lam (Y + ε • d) := by
  obtain ⟨hFA, hFP, hF0⟩ := hF
  have e1 : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ∀ i, (I.Abar *ᵥ Y) i + ε * (I.Abar *ᵥ d) i ≤ c i := by
    rw [Filter.eventually_all]; intro i; exact ev_le _ _ _ (hFA i) (hA i)
  have e2 : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ∀ q, (I.P *ᵥ Y) q + ε * (I.P *ᵥ d) q ≤ I.lam q := by
    rw [Filter.eventually_all]; intro q; exact ev_le _ _ _ (hFP q) (hP q)
  have e3 : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ j, -Y j + ε * (-d j) ≤ 0 := by
    rw [Filter.eventually_all]; intro j
    exact ev_le _ _ _ (by have : (0:ℝ) ≤ Y j := hF0 j; linarith)
      (fun h => by have := h0 j (by linarith); linarith)
  obtain ⟨ε, ⟨⟨h1, h2⟩, h3⟩, h4⟩ := ((e1.and e2).and e3).and self_mem_nhdsWithin |>.exists
  refine ⟨ε, h4, ?_, ?_, ?_⟩
  · intro i
    simp only [mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact h1 i
  · intro q
    simp only [mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact h2 q
  · intro j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have := h3 j; linarith

/-- The linear functional `v ↦ v ⬝ᵥ d`. -/
def dotL (d : Fin n → ℝ) : (Fin n → ℝ) →ₗ[ℝ] ℝ where
  toFun v := v ⬝ᵥ d
  map_add' a b := by simp [add_dotProduct]
  map_smul' a b := by simp [smul_dotProduct]

lemma eq_zero_of_perp {G : Set (Fin n → ℝ)} (hG : Submodule.span ℝ G = ⊤) (d : Fin n → ℝ)
    (hd : ∀ v ∈ G, v ⬝ᵥ d = 0) : d = 0 := by
  have hle : Submodule.span ℝ G ≤ LinearMap.ker (dotL d) := by
    rw [Submodule.span_le]; intro v hv; exact hd v hv
  rw [hG] at hle
  ext j
  have := hle (Submodule.mem_top (x := (Pi.single j 1 : Fin n → ℝ)))
  simpa [dotL] using this

/-- An optimal solution which is the unique optimum is a vertex: its active rows span. -/
lemma span_top {Y : Fin n → ℝ} (hY : I.IsDLPOptimal I.C I.lam Y)
    (huniq : ∀ x, I.IsDLPOptimal I.C I.lam x → x = Y) :
    Submodule.span ℝ (I.dlpRow '' ↑(I.dlpActive Y)) = ⊤ := by
  classical
  by_contra hne
  set S := Submodule.span ℝ (I.dlpRow '' ↑(I.dlpActive Y))
  have hlt : S < ⊤ := lt_top_iff_ne_top.mpr hne
  obtain ⟨f, hf0, hfS⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hlt inferInstance
  set d : Fin n → ℝ := fun j => f (Pi.single j 1)
  have hfd : ∀ v, f v = v ⬝ᵥ d := by
    intro v
    conv_lhs => rw [pi_eq_sum_univ v]
    simp [map_sum, d, dotProduct]
    apply Finset.sum_congr rfl; intro j _
    congr 1
    congr 1; ext k; simp [Pi.single_apply, eq_comm]
  have hperp : ∀ r ∈ I.dlpActive Y, I.dlpRow r ⬝ᵥ d = 0 := by
    intro r hr
    rw [← hfd]
    have : f (I.dlpRow r) ∈ S.map f := Submodule.mem_map_of_mem
      (Submodule.subset_span ⟨r, hr, rfl⟩)
    rw [hfS] at this; simpa using this
  have memAct : ∀ r, r ∈ I.dlpActive Y ↔ I.dlpRow r ⬝ᵥ Y = I.dlpRhs r := by
    intro r; simp [Instance.dlpActive]
  have hd0 : d ≠ 0 := by
    intro h; apply hf0; apply LinearMap.ext; intro v; rw [hfd]; simp [h]
  -- both directions are feasible
  have dir : ∀ s : ℝ, ∃ ε : ℝ, 0 < ε ∧ I.DLPFeasible I.C I.lam (Y + ε • (s • d)) := by
    intro s
    apply feasDir I hY.1
    · intro i hi
      have := hperp (Sum.inl i) ((memAct _).2 (by rw [row_inl]; exact hi))
      rw [row_inl] at this
      simp [mulVec_smul, this]
    · intro q hq
      have := hperp (Sum.inr (Sum.inl q)) ((memAct _).2 (by rw [row_P]; exact hq))
      rw [row_P] at this
      simp [mulVec_smul, this]
    · intro j hj
      have := hperp (Sum.inr (Sum.inr j)) ((memAct _).2 (by
        rw [row_sign]; simp [Instance.dlpRhs, hj]))
      rw [row_sign] at this
      have : d j = 0 := by linarith
      simp [this]
  obtain ⟨ε1, hε1, hF1⟩ := dir 1
  obtain ⟨ε2, hε2, hF2⟩ := dir (-1)
  have o1 := hY.2 _ hF1
  have o2 := hY.2 _ hF2
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, one_smul, neg_smul,
    dotProduct_neg] at o1 o2
  have hrd : I.rbar ⬝ᵥ d = 0 := by nlinarith
  have hopt : I.IsDLPOptimal I.C I.lam (Y + ε1 • (1 : ℝ) • d) := by
    refine ⟨hF1, fun y hy => ?_⟩
    have := hY.2 y hy
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, one_smul, hrd]
    linarith
  have := huniq _ hopt
  apply hd0
  have h2 : ε1 • (1 : ℝ) • d = 0 := by
    have := congrArg (fun x => x - Y) this
    simpa using this
  rw [one_smul] at h2
  exact (smul_eq_zero.mp h2).resolve_left hε1.ne'

/-- Nondegeneracy forces `λ > 0` (at the vertex `x = 0`). -/
lemma lam_pos (hI : I.IsValid) (h21 : I.Assumption21) : ∀ q, 0 < I.lam q := by
  classical
  intro q
  by_contra hle
  have h : I.lam q = 0 := le_antisymm (not_lt.mp hle) (hI.1 q)
  have hfeas : I.DLPFeasible I.C I.lam 0 := by
    refine ⟨?_, ?_, le_rfl⟩
    · simpa using hI.2.1
    · simpa using hI.1
  have memAct : ∀ r, r ∈ I.dlpActive 0 ↔ I.dlpRow r ⬝ᵥ 0 = I.dlpRhs r := by
    intro r; simp [Instance.dlpActive]
  have hsign : ∀ j, (Sum.inr (Sum.inr j) : Fin m ⊕ Fin NT ⊕ Fin n) ∈ I.dlpActive 0 := by
    intro j; rw [memAct]; simp [Instance.dlpRhs]
  have hspan : Submodule.span ℝ (I.dlpRow '' ↑(I.dlpActive 0)) = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro x
    rw [pi_eq_sum_univ x]
    refine Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ ?_)
    have : I.dlpRow (Sum.inr (Sum.inr j)) ∈ Submodule.span ℝ (I.dlpRow '' ↑(I.dlpActive 0)) :=
      Submodule.subset_span ⟨_, hsign j, rfl⟩
    have e : (fun j' => if j = j' then (1:ℝ) else 0) = - I.dlpRow (Sum.inr (Sum.inr j)) := by
      ext j'; simp [Instance.dlpRow, eq_comm]; split_ifs <;> norm_num
    rw [e]; exact Submodule.neg_mem _ this
  have hcard := h21.1 0 hfeas hspan
  have hsub : (Finset.univ.map ⟨fun j => (Sum.inr (Sum.inr j) : Fin m ⊕ Fin NT ⊕ Fin n),
      fun a b h => by simpa using h⟩) ∪ {Sum.inr (Sum.inl q)} ⊆ I.dlpActive 0 := by
    intro r hr
    simp only [Finset.mem_union, Finset.mem_map, Finset.mem_univ, true_and,
      Function.Embedding.coeFn_mk, Finset.mem_singleton] at hr
    rcases hr with ⟨j, rfl⟩ | rfl
    · exact hsign j
    · rw [memAct]; simp [Instance.dlpRhs, h]
  have hdisj : Disjoint (Finset.univ.map ⟨fun j => (Sum.inr (Sum.inr j) : Fin m ⊕ Fin NT ⊕ Fin n),
      fun a b h => by simpa using h⟩) {Sum.inr (Sum.inl q)} := by
    rw [Finset.disjoint_singleton_right, Finset.mem_map]
    rintro ⟨x, _, hx⟩; cases hx
  have := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj] at this
  simp at this
  omega

end PertAux

namespace PertAux

variable {NT n m : ℕ} (I : Instance NT n m)

/-- Observation B.2 with all the structural facts used later. -/
lemma B2_core (hI : I.IsValid) (h21 : I.Assumption21) (Y : Fin n → ℝ)
    (hY : I.IsDLPOptimal I.C I.lam Y) :
    Fintype.card (↥(I.BA Y) ⊕ ↥(I.B2 Y)) = Fintype.card ↥(I.Jy Y) ∧
      Function.Bijective (I.Wmat Y).mulVec := by
  classical
  have hlam := lam_pos I hI h21
  obtain ⟨Y0, hY0, hu0⟩ := h21.2
  have huniq : ∀ x, I.IsDLPOptimal I.C I.lam x → x = Y :=
    fun x hx => (hu0 x hx).trans (hu0 Y hY).symm
  have hspan := span_top I hY huniq
  have hcard := h21.1 Y hY.1 hspan
  obtain ⟨⟨hA, hP, h0⟩, _⟩ := hY
  have hle : ∀ j, Y j ≤ I.lam (I.typ j) := by
    intro j
    simpa using sum_le_lam I hP h0 (I.typ j) {j} (by simp)
  have hzero : ∀ j j', Y j = I.lam (I.typ j) → j' ≠ j → I.typ j' = I.typ j → Y j' = 0 := by
    intro j j' hj hne' ht
    have := sum_le_lam I hP h0 (I.typ j) {j, j'} (by
      intro x hx; simp at hx; rcases hx with rfl | rfl <;> simp [ht])
    rw [Finset.sum_pair (Ne.symm hne')] at this
    have : (0:ℝ) ≤ Y j' := h0 j'
    linarith
  have hPge : ∀ j, Y j ≤ (I.P *ᵥ Y) (I.typ j) := by
    intro j
    show Y j ≤ ∑ x, I.P (I.typ j) x * Y x
    have := Finset.single_le_sum (f := fun x => I.P (I.typ j) x * Y x)
      (fun x _ => mul_nonneg (by unfold Instance.P; split_ifs <;> norm_num) (h0 x))
      (Finset.mem_univ j)
    simpa [Instance.P] using this
  -- the active set
  have hact : I.dlpActive Y = (I.BA Y).disjSum ((I.BP Y).disjSum (Instance.J0 Y)) := by
    ext r
    rcases r with i | q | j
    · rw [mem_active, row_inl]; simp [Instance.BA, Instance.dlpRhs]
    · rw [mem_active, row_P]; simp [Instance.BP, Instance.dlpRhs]
    · rw [mem_active, row_sign]; simp [Instance.J0, Instance.dlpRhs]
  rw [hact, Finset.card_disjSum, Finset.card_disjSum] at hcard
  -- B1 = typ '' Jλ
  have hB1 : I.B1 Y = (I.Jlam Y).image I.typ := by
    ext q
    simp only [Instance.B1, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨_, j, hj, hq⟩; exact ⟨j, hj, hq⟩
    · rintro ⟨j, hj, rfl⟩
      refine ⟨?_, j, hj, rfl⟩
      simp only [Instance.BP, Finset.mem_filter, Finset.mem_univ, true_and]
      simp only [Instance.Jlam, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      exact le_antisymm (hP _) (hj ▸ hPge j)
  have hB1card : (I.B1 Y).card = (I.Jlam Y).card := by
    rw [hB1]
    apply Finset.card_image_of_injOn
    intro a ha b hb hab
    by_contra hne'
    simp only [Instance.Jlam, Finset.coe_filter, Finset.mem_univ, true_and,
      Set.mem_setOf_eq] at ha hb
    have := hzero a b ha (Ne.symm hne') hab.symm
    have := hlam (I.typ b)
    linarith
  have hBP : (I.B2 Y).card + (I.B1 Y).card = (I.BP Y).card :=
    Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)
  -- partition of the offers
  have hpart : (Instance.J0 Y).card + (I.Jy Y).card + (I.Jlam Y).card = n := by
    have hd1 : Disjoint (Instance.J0 Y) (I.Jy Y) := by
      rw [Finset.disjoint_left]; intro j h1 h2
      simp [Instance.J0, Instance.Jy] at h1 h2; linarith [h2.1]
    have hd2 : Disjoint (Instance.J0 Y ∪ I.Jy Y) (I.Jlam Y) := by
      rw [Finset.disjoint_left]; intro j h1 h2
      simp [Instance.J0, Instance.Jy, Instance.Jlam] at h1 h2
      have := hlam (I.typ j)
      rcases h1 with h | h
      · linarith
      · linarith [h.2]
    have hU : Instance.J0 Y ∪ I.Jy Y ∪ I.Jlam Y = Finset.univ := by
      ext j
      simp only [Instance.J0, Instance.Jy, Instance.Jlam, Finset.mem_union, Finset.mem_filter,
        Finset.mem_univ, true_and, iff_true]
      have h0j : (0:ℝ) ≤ Y j := h0 j
      rcases lt_or_eq_of_le h0j with h | h
      · rcases lt_or_eq_of_le (hle j) with h' | h'
        · exact Or.inl (Or.inr ⟨h, h'⟩)
        · exact Or.inr h'
      · exact Or.inl (Or.inl h.symm)
    have := congrArg Finset.card hU
    rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1] at this
    simpa using this
  have hsq : Fintype.card (↥(I.BA Y) ⊕ ↥(I.B2 Y)) = Fintype.card ↥(I.Jy Y) := by
    rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_coe, Fintype.card_coe]
    omega
  refine ⟨hsq, ?_⟩
  -- injectivity
  have hker : ∀ w : ↥(I.Jy Y) → ℝ, (I.Wmat Y) *ᵥ w = 0 → w = 0 := by
    intro w hw
    set d : Fin n → ℝ := fun j => if h : j ∈ I.Jy Y then w ⟨j, h⟩ else 0 with hd
    have hsum : ∀ g : Fin n → ℝ, g ⬝ᵥ d = ∑ j : ↥(I.Jy Y), g j * w j := by
      intro g
      rw [dotProduct, ← Finset.sum_subset (Finset.subset_univ (I.Jy Y))]
      · rw [← Finset.sum_coe_sort (I.Jy Y)]
        apply Finset.sum_congr rfl
        intro j _
        simp [d, j.2]
      · intro j _ hj; simp [d, hj]
    have hperp : ∀ r ∈ I.dlpActive Y, I.dlpRow r ⬝ᵥ d = 0 := by
      intro r hr
      rw [hact] at hr
      rcases r with i | q | j
      · simp only [Finset.inl_mem_disjSum] at hr
        rw [hsum]
        have := congrFun hw (Sum.inl ⟨i, hr⟩)
        simpa [Matrix.mulVec, dotProduct, Instance.Wmat, Instance.dlpRow] using this
      · simp only [Finset.inr_mem_disjSum, Finset.inl_mem_disjSum] at hr
        rw [hsum]
        by_cases hq1 : q ∈ I.B1 Y
        · apply Finset.sum_eq_zero
          intro j _
          have hP0 : I.P q j = 0 := by
            unfold Instance.P
            rw [if_neg]
            intro htq
            simp only [Instance.B1, Finset.mem_filter] at hq1
            obtain ⟨_, j0, hj0, hq0⟩ := hq1
            simp only [Instance.Jlam, Finset.mem_filter, Finset.mem_univ, true_and] at hj0
            have hjJ := j.2
            simp only [Instance.Jy, Finset.mem_filter, Finset.mem_univ, true_and] at hjJ
            have hne' : (j : Fin n) ≠ j0 := by
              intro h; rw [h] at hjJ; linarith [hjJ.2]
            have := hzero j0 j hj0 hne' (htq.trans hq0.symm)
            linarith [hjJ.1]
          show I.dlpRow (Sum.inr (Sum.inl q)) j * w j = 0
          simp [Instance.dlpRow, hP0]
        · have hq2 : q ∈ I.B2 Y := Finset.mem_sdiff.mpr ⟨hr, hq1⟩
          have := congrFun hw (Sum.inr ⟨q, hq2⟩)
          simpa [Matrix.mulVec, dotProduct, Instance.Wmat, Instance.dlpRow] using this
      · simp only [Finset.inr_mem_disjSum] at hr
        rw [row_sign]
        have : j ∉ I.Jy Y := by
          simp [Instance.J0] at hr; simp [Instance.Jy, hr]
        simp [d, this]
    have hd0 := eq_zero_of_perp hspan d (by
      rintro v ⟨r, hr, rfl⟩; exact hperp r hr)
    ext j
    have := congrFun hd0 j
    simpa [d, j.2] using this
  have hinj : Function.Injective (I.Wmat Y).mulVec := by
    intro u v huv
    have := hker (u - v) (by rw [Matrix.mulVec_sub, huv, sub_self])
    exact sub_eq_zero.mp this
  have hfin : Module.finrank ℝ (↥(I.Jy Y) → ℝ) = Module.finrank ℝ (↥(I.BA Y) ⊕ ↥(I.B2 Y) → ℝ) := by
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card, hsq]
  have hinjL : Function.Injective (Matrix.mulVecLin (I.Wmat Y)) := hinj
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).1 hinjL⟩

end PertAux

theorem solution {NT n m : ℕ} (I : Instance NT n m) (hI : I.IsValid)
    (h21 : I.Assumption21) (h22 : I.Assumption22) (Y : Fin n → ℝ)
    (hY : I.IsDLPOptimal I.C I.lam Y) :
    Fintype.card (↥(I.BA Y) ⊕ ↥(I.B2 Y)) = Fintype.card ↥(I.Jy Y) ∧
      Function.Bijective (I.Wmat Y).mulVec :=
  PertAux.B2_core I hI h21 Y hY
