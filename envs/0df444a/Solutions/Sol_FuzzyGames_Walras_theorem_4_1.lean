-- Prove2me | solution 1 for FuzzyGames.Walras.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T01:16:30.219131+00:00
-- url     : https://prove2.me/submissions/1039850b-3229-4658-b7a8-79cf90cee371

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
lemma dot_smul_left (a : ℝ) (p q : Fin l → ℝ) : dot (a • p) q = a * dot p q := by
  unfold dot; simp [Finset.mul_sum, mul_assoc]

lemma dot_zero_left (q : Fin l → ℝ) : dot (0 : Fin l → ℝ) q = 0 := by simp [dot]

lemma exists_sep (C : Set (Fin l → ℝ)) (hC : Convex ℝ C) (hne : C.Nonempty)
    (h0 : (0 : Fin l → ℝ) ∉ C) : ∃ p : Fin l → ℝ, ‖p‖ = 1 ∧ ∀ q ∈ C, dot p q ≤ 0 := by
  classical
  obtain ⟨c0, hc0⟩ := hne
  have fin_step : ∀ u : Finset (Fin l → ℝ), (↑u ⊆ C) →
      ∃ p : Fin l → ℝ, ‖p‖ = 1 ∧ ∀ q ∈ u, dot p q ≤ 0 := by
    intro u hu
    have hFsub : convexHull ℝ (insert c0 (u : Set (Fin l → ℝ))) ⊆ C :=
      convexHull_min (Set.insert_subset hc0 hu) hC
    have hFc : IsCompact (convexHull ℝ (insert c0 (u : Set (Fin l → ℝ)))) :=
      Set.Finite.isCompact_convexHull (𝕜 := ℝ) (Set.Finite.insert c0 u.finite_toSet)
    obtain ⟨f, w, hf0, hfb⟩ := geometric_hahn_banach_point_closed (convex_convexHull ℝ _)
      hFc.isClosed (fun h => h0 (hFsub h))
    rw [map_zero] at hf0
    set p0 : Fin l → ℝ := fun k => - f (fun j => if k = j then 1 else 0) with hp0
    have hdot : ∀ b, dot p0 b = - f b := by
      intro b
      have := LinearMap.pi_apply_eq_sum_univ f.toLinearMap b
      simp only [ContinuousLinearMap.coe_coe] at this
      rw [this]
      unfold dot
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun k _ => by simp [hp0, mul_comm])
    have hneg : ∀ b ∈ convexHull ℝ (insert c0 (u : Set (Fin l → ℝ))), dot p0 b < 0 := by
      intro b hb
      rw [hdot]
      have := hfb b hb
      linarith
    have hc0F : c0 ∈ convexHull ℝ (insert c0 (u : Set (Fin l → ℝ))) :=
      subset_convexHull ℝ _ (Set.mem_insert _ _)
    have hp0ne : p0 ≠ 0 := by
      intro h
      have := hneg c0 hc0F
      rw [h, dot_zero_left] at this
      exact lt_irrefl _ this
    have hnpos : 0 < ‖p0‖ := norm_pos_iff.2 hp0ne
    refine ⟨(‖p0‖⁻¹) • p0, ?_, ?_⟩
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnpos.ne']
    · intro q hq
      rw [dot_smul_left]
      have := hneg q (subset_convexHull ℝ _ (Set.mem_insert_of_mem _ hq))
      exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 hnpos.le) this.le
  have hsph : IsCompact (Metric.sphere (0 : Fin l → ℝ) 1) := isCompact_sphere 0 1
  have key := hsph.inter_iInter_nonempty (fun q : C => {p : Fin l → ℝ | dot p (q : Fin l → ℝ) ≤ 0})
    (fun q => isClosed_le (by unfold dot; fun_prop) continuous_const) (by
      intro u
      obtain ⟨p, hp1, hp⟩ := fin_step (u.image (fun q : C => (q : Fin l → ℝ)))
        (by intro x hx; simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx
            obtain ⟨q, _, rfl⟩ := hx; exact q.2)
      refine ⟨p, by simpa using hp1, ?_⟩
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
      intro q hq
      exact hp q (Finset.mem_image_of_mem _ hq))
  obtain ⟨p, hps, hpC⟩ := key
  refine ⟨p, by simpa using hps, fun q hq => ?_⟩
  simp only [Set.mem_iInter, Set.mem_setOf_eq] at hpC
  exact hpC ⟨q, hq⟩


lemma le_zero_of_forall_small (d M : ℝ) (h : ∀ α : ℝ, 0 < α → α < 1 → d ≤ α * M) : d ≤ 0 := by
  by_contra hd
  push_neg at hd
  have hden : 0 < |M| + d + 1 := by positivity
  set α := d / (|M| + d + 1) with hα
  have hα0 : 0 < α := div_pos hd hden
  have hα1 : α < 1 := by rw [hα, div_lt_one hden]; have := abs_nonneg M; linarith
  have e : α * (|M| + d + 1) = d := by rw [hα]; field_simp
  have h1 := h α hα0 hα1
  have h2 : α * M ≤ α * |M| := mul_le_mul_of_nonneg_left (le_abs_self M) hα0.le
  have h3 : 0 < α * (d + 1) := mul_pos hα0 (by linarith)
  nlinarith

theorem core_sub_walras (E : Economy n l) (hE : E.Assumptions) : E.fuzzyCore ⊆ E.walras := by
  classical
  intro xbar hx
  have hX : xbar ∈ E.X 1 := hx.1
  have hxb : ∀ i, 0 ≤ xbar i := fun i => hX.1 i one_pos
  refine ⟨hX, ?_⟩
  rcases isEmpty_or_nonempty (Fin n) with hn | ⟨⟨i0⟩⟩
  · exact ⟨0, fun i => (hn.false i).elim, fun i => (hn.false i).elim⟩
  have hSne : (Sset E xbar).Nonempty := by
    obtain ⟨q, hq⟩ := Q_nonempty' E hE xbar hX i0
    exact ⟨q, Q_sub_S E xbar (Q_nonempty' E hE xbar hX) i0 hq⟩
  obtain ⟨p, hp1, hpS⟩ := exists_sep (Sset E xbar) (S_convex E xbar (Q_convex E hE xbar hX)) hSne
    (zero_not_mem_S E xbar hx)
  -- (A)
  have hA : ∀ i, ∀ y ∈ E.Y i, ∀ x, 0 ≤ x → E.spref i x (xbar i) → dot p y ≤ dot p x := by
    intro i y hy x hx0 hxs
    have hq : y - x ∈ E.Q xbar i := ⟨y, hy, x, ⟨hx0, hxs⟩, rfl⟩
    have := hpS _ (Q_sub_S E xbar (Q_nonempty' E hE xbar hX) i hq)
    rw [dot_sub'] at this
    linarith
  -- p nonneg
  have hpnn : ∀ k, 0 ≤ p k := by
    intro k
    by_contra hk
    push_neg at hk
    obtain ⟨y0, hy0, -⟩ := hE.pos_endowed i0
    obtain ⟨x0, hx00, hx0⟩ := hE.nonsatiation i0 _ (hxb i0)
    set M := |dot p x0 - dot p y0| + 1 with hM
    set t := M / (-p k) with ht
    have ht0 : 0 ≤ t := div_nonneg (by positivity) (by linarith)
    set e : Fin l → ℝ := fun j => if k = j then 1 else 0 with he
    have he0 : 0 ≤ t • e := by
      intro j; simp only [he, Pi.smul_apply, smul_eq_mul]; split_ifs <;> simp [ht0]
    have hmem := hE.comprehensive_Y i0 y0 hy0 (t • e) he0
    have h1 := hA i0 _ hmem x0 hx00 hx0
    have hde : dot p e = p k := by
      simp only [dot, he]; simp
    rw [dot_sub', dot_smul', hde] at h1
    have hne : -p k ≠ 0 := by linarith
    have : t * (-p k) = M := by rw [ht]; exact div_mul_cancel₀ M hne
    have := le_abs_self (dot p x0 - dot p y0)
    nlinarith
  -- (C)
  have hC : ∀ i, ∀ y ∈ E.Y i, dot p y ≤ dot p (xbar i) := by
    intro i y hy
    obtain ⟨z, hz0, hz⟩ := hE.nonsatiation i _ (hxb i)
    suffices hsf : dot p y - dot p (xbar i) ≤ 0 by linarith
    apply le_zero_of_forall_small (dot p y - dot p (xbar i)) (dot p z - dot p (xbar i))
    intro α hα0 hα1
    have hw := hE.strict_convex i z (xbar i) hz0 (hxb i) hz α hα0 hα1
    have hw0 : 0 ≤ α • z + (1 - α) • xbar i :=
      add_nonneg (smul_nonneg hα0.le hz0) (smul_nonneg (by linarith) (hxb i))
    have := hA i y hy _ hw0 hw
    rw [dot_add', dot_smul', dot_smul'] at this
    linarith
  -- (D)
  obtain ⟨y, hy, hsum⟩ := mem_Ytau hX.2
  have hsum' : ∑ i, dot p (xbar i) = ∑ i, dot p (y i) := by
    simp only [Pi.one_apply, one_smul] at hsum
    have h1 := congrArg (dot p) hsum
    rw [dot_sum', dot_sum'] at h1
    exact h1
  have hyeq : ∀ i, dot p (y i) = dot p (xbar i) := by
    have := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (f := fun i => dot p (y i))
      (g := fun i => dot p (xbar i)) (fun i _ => hC i _ (hy i))).1 hsum'.symm
    exact fun i => this i (Finset.mem_univ i)
  have hinc : ∀ i, E.income i p = ((dot p (xbar i) : ℝ) : EReal) := by
    intro i
    apply le_antisymm
    · exact iSup₂_le (fun z hz => EReal.coe_le_coe_iff.2 (hC i z hz))
    · exact le_iSup₂_of_le (y i) (hy i) (by rw [hyeq])
  -- p nonzero
  obtain ⟨k0, hk0⟩ : ∃ k, p k ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have : p = 0 := funext hcon
    rw [this, norm_zero] at hp1
    exact zero_ne_one hp1
  refine ⟨p, fun i => (hinc i).symm, fun i z hz => ?_⟩
  obtain ⟨hz0, hzb⟩ := hz
  rw [hinc i] at hzb
  have hzle : dot p z ≤ dot p (xbar i) := EReal.coe_le_coe_iff.1 hzb
  by_contra hn
  have hzs : E.spref i z (xbar i) := by
    refine ⟨?_, hn⟩
    rcases hE.total i (xbar i) z (hxb i) hz0 with h | h
    · exact absurd h hn
    · exact h
  -- openness
  have hUc := hE.closed_lower i (xbar i) (hxb i)
  have hV : IsOpen ((fun α : ℝ => α • z) ⁻¹' {w | 0 ≤ w ∧ E.pref i (xbar i) w}ᶜ) :=
    (continuous_id.smul continuous_const).isOpen_preimage _ hUc.isOpen_compl
  have h1V : (1 : ℝ) ∈ ((fun α : ℝ => α • z) ⁻¹' {w | 0 ≤ w ∧ E.pref i (xbar i) w}ᶜ) := by
    simp only [Set.mem_preimage, one_smul, Set.mem_compl_iff, Set.mem_setOf_eq]
    exact fun h => hn h.2
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hV 1 h1V
  set α : ℝ := 1 - min (ε / 2) (1 / 2) with hα
  have hm1 : min (ε / 2) (1 / 2) ≤ 1 / 2 := min_le_right _ _
  have hm2 : min (ε / 2) (1 / 2) ≤ ε / 2 := min_le_left _ _
  have hm3 : 0 < min (ε / 2) (1 / 2) := lt_min (by linarith) (by norm_num)
  have hα0 : 0 < α := by rw [hα]; linarith
  have hα1 : α < 1 := by rw [hα]; linarith
  have hαV : α ∈ ((fun α : ℝ => α • z) ⁻¹' {w | 0 ≤ w ∧ E.pref i (xbar i) w}ᶜ) := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, hα]
    rw [abs_lt]; constructor <;> linarith
  simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_setOf_eq] at hαV
  have hαz0 : 0 ≤ α • z := smul_nonneg hα0.le hz0
  have hnp : ¬ E.pref i (xbar i) (α • z) := fun h => hαV ⟨hαz0, h⟩
  have hsp : E.spref i (α • z) (xbar i) := by
    refine ⟨?_, hnp⟩
    rcases hE.total i (xbar i) (α • z) (hxb i) hαz0 with h | h
    · exact absurd h hnp
    · exact h
  obtain ⟨y0, hy0, hy0pos⟩ := hE.pos_endowed i
  have hpos : 0 < dot p y0 := by
    unfold dot
    apply Finset.sum_pos'
    · intro k _; exact mul_nonneg (hpnn k) (hy0pos k).le
    · exact ⟨k0, Finset.mem_univ _, mul_pos (lt_of_le_of_ne (hpnn k0) (Ne.symm hk0)) (hy0pos k0)⟩
  have h1 := hA i (y i) (hy i) _ hαz0 hsp
  have h2 := hC i y0 hy0
  rw [dot_smul', hyeq] at h1
  have h3 : α * dot p z ≤ α * dot p (xbar i) := mul_le_mul_of_nonneg_left hzle hα0.le
  have h4 : 0 < (1 - α) * dot p (xbar i) := mul_pos (by linarith) (by linarith)
  nlinarith

theorem theorem_4_1_core (E : Economy n l) (hE : E.Assumptions) : E.fuzzyCore = E.walras :=
  Set.Subset.antisymm (core_sub_walras E hE) (walras_sub_core E hE)

end FuzzyGames.Walras

open FuzzyGames.Walras


theorem solution {n l : ℕ} (E : Economy n l) (hE : E.Assumptions) :
    E.fuzzyCore = E.walras := by
  exact theorem_4_1_core E hE
