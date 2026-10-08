-- Prove2me | solution 1 for CoffmanMitrani1980.Region.lemma2_vertices_are_priority_vectors
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T04:53:55.290398+00:00
-- url     : https://prove2.me/submissions/f31f790e-efb4-4e36-805b-fdb4b6e3bb3d

import Definitions.Def_CoffmanMitrani1980_Region_Model

open Finset


namespace CoffmanMitrani1980.Region

lemma cm_rho_pos {M : ℕ} (p : Params M) (i : Fin M) : 0 < p.rho i :=
  div_pos (p.lam_pos i) (p.mu_pos i)

lemma cm_a_pos {M : ℕ} (p : Params M) (i : Fin M) : 0 < p.a i :=
  div_pos (cm_rho_pos p i) (p.mu_pos i)

lemma cm_sumrho_lt {M : ℕ} (p : Params M) (g : Finset (Fin M)) : ∑ i ∈ g, p.rho i < 1 :=
  lt_of_le_of_lt (Finset.sum_le_sum_of_subset_of_nonneg (subset_univ g)
    (fun i _ _ => (cm_rho_pos p i).le)) p.load_lt_one

lemma cm_f_nonneg {M : ℕ} (p : Params M) (g : Finset (Fin M)) : 0 ≤ p.f g :=
  div_nonneg (sum_nonneg fun i _ => (cm_a_pos p i).le) (sub_pos.2 (cm_sumrho_lt p g)).le

lemma cm_key (A α1 α2 R r1 r2 : ℝ) (hA : 0 ≤ A) (ha1 : 0 ≤ α1) (ha2 : 0 ≤ α2)
    (hr1 : 0 ≤ r1) (hr2 : 0 ≤ r2) (hD : 0 < 1 - (R + r1 + r2)) :
    (A + α1) / (1 - (R + r1)) + (A + α2) / (1 - (R + r2)) ≤
      (A + α1 + α2) / (1 - (R + r1 + r2)) + A / (1 - R) := by
  have hD1 : 0 < 1 - (R + r1) := by linarith
  have hD2 : 0 < 1 - (R + r2) := by linarith
  have hD0 : 0 < 1 - R := by linarith
  have i1 : 1 / (1 - (R + r1)) + 1 / (1 - (R + r2)) ≤ 1 / (1 - (R + r1 + r2)) + 1 / (1 - R) := by
    rw [div_add_div _ _ hD1.ne' hD2.ne', div_add_div _ _ hD.ne' hD0.ne']
    have e1 : 1 * (1 - (R + r2)) + (1 - (R + r1)) * 1 = 1 * (1 - R) + (1 - (R + r1 + r2)) * 1 := by ring
    rw [e1]
    apply div_le_div_of_nonneg_left (by linarith) (mul_pos hD hD0)
    nlinarith [mul_nonneg hr1 hr2]
  have i2 : α1 / (1 - (R + r1)) ≤ α1 / (1 - (R + r1 + r2)) :=
    div_le_div_of_nonneg_left ha1 hD (by linarith)
  have i3 : α2 / (1 - (R + r2)) ≤ α2 / (1 - (R + r1 + r2)) :=
    div_le_div_of_nonneg_left ha2 hD (by linarith)
  have i4 := mul_le_mul_of_nonneg_left i1 hA
  have e1 : (A + α1) / (1 - (R + r1)) = A * (1 / (1 - (R + r1))) + α1 / (1 - (R + r1)) := by ring
  have e2 : (A + α2) / (1 - (R + r2)) = A * (1 / (1 - (R + r2))) + α2 / (1 - (R + r2)) := by ring
  have e3 : (A + α1 + α2) / (1 - (R + r1 + r2)) = A * (1 / (1 - (R + r1 + r2))) +
      α1 / (1 - (R + r1 + r2)) + α2 / (1 - (R + r1 + r2)) := by ring
  have e4 : A / (1 - R) = A * (1 / (1 - R)) := by ring
  rw [e1, e2, e3, e4]
  nlinarith

lemma cm_supermod {M : ℕ} (p : Params M) (S T : Finset (Fin M)) :
    p.f S + p.f T ≤ p.f (S ∪ T) + p.f (S ∩ T) := by
  have hS : ∀ u : Fin M → ℝ, ∑ i ∈ S, u i = ∑ i ∈ S ∩ T, u i + ∑ i ∈ S \ T, u i :=
    fun u => (sum_inter_add_sum_sdiff S T u).symm
  have hT : ∀ u : Fin M → ℝ, ∑ i ∈ T, u i = ∑ i ∈ S ∩ T, u i + ∑ i ∈ T \ S, u i :=
    fun u => by rw [inter_comm]; exact (sum_inter_add_sum_sdiff T S u).symm
  have hU : ∀ u : Fin M → ℝ, ∑ i ∈ S ∪ T, u i =
      ∑ i ∈ S ∩ T, u i + ∑ i ∈ S \ T, u i + ∑ i ∈ T \ S, u i := fun u => by
    rw [← hS u, ← sum_union disjoint_sdiff, union_sdiff_self_eq_union]
  have hpos := cm_sumrho_lt p (S ∪ T)
  unfold Params.f
  rw [hS p.a, hS p.rho, hT p.a, hT p.rho, hU p.a, hU p.rho]
  rw [hU p.rho] at hpos
  exact cm_key _ _ _ _ _ _ (sum_nonneg fun i _ => (cm_a_pos p i).le)
    (sum_nonneg fun i _ => (cm_a_pos p i).le) (sum_nonneg fun i _ => (cm_a_pos p i).le)
    (sum_nonneg fun i _ => (cm_rho_pos p i).le) (sum_nonneg fun i _ => (cm_rho_pos p i).le)
    (by linarith)

lemma cm_f_empty {M : ℕ} (p : Params M) : p.f ∅ = 0 := by simp [Params.f]

lemma cm_f_univ {M : ℕ} (p : Params M) : p.f univ = p.V / (1 - ∑ i, p.rho i) := by
  unfold Params.f Params.V Params.a Params.rho
  congr 1
  refine sum_congr rfl (fun i _ => ?_)
  rw [div_div, sq]

lemma cm_mem_Hss_iff {M : ℕ} (p : Params M) (W : Fin M → ℝ) :
    W ∈ p.Hss ↔ (∑ i, p.rho i * W i = p.f univ) ∧ ∀ g, p.f g ≤ ∑ i ∈ g, p.rho i * W i := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by rw [h1, cm_f_univ], fun g => ?_⟩
    by_cases h0 : g = ∅
    · subst h0; simp [cm_f_empty]
    by_cases hu : g = univ
    · subst hu; rw [h1, cm_f_univ]
    exact h2 g (nonempty_iff_ne_empty.2 h0) hu
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [h1, cm_f_univ], fun g _ _ => h2 g⟩

lemma cm_tight {M : ℕ} (p : Params M) (W : Fin M → ℝ)
    (hfe : ∀ g, p.f g ≤ ∑ i ∈ g, p.rho i * W i) (S T : Finset (Fin M))
    (hS : ∑ i ∈ S, p.rho i * W i = p.f S) (hT : ∑ i ∈ T, p.rho i * W i = p.f T) :
    ∑ i ∈ S ∪ T, p.rho i * W i = p.f (S ∪ T) ∧ ∑ i ∈ S ∩ T, p.rho i * W i = p.f (S ∩ T) := by
  have h1 := sum_union_inter (s₁ := S) (s₂ := T) (f := fun i => p.rho i * W i)
  have h2 := cm_supermod p S T
  have h3 := hfe (S ∪ T)
  have h4 := hfe (S ∩ T)
  constructor <;> linarith

lemma cm_mem_topSet {M : ℕ} (π : Equiv.Perm (Fin M)) (k : ℕ) (x : Fin M) :
    x ∈ topSet π k ↔ ((π.symm x : Fin M) : ℕ) < k := by
  simp only [topSet, mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨j, hj, rfl⟩; simpa using hj
  · intro h; exact ⟨π.symm x, h, by simp⟩

lemma cm_topSet_zero {M : ℕ} (π : Equiv.Perm (Fin M)) : topSet π 0 = ∅ := by
  ext x; simp [cm_mem_topSet]

lemma cm_topSet_succ {M : ℕ} (π : Equiv.Perm (Fin M)) (k : ℕ) (hk : k < M) :
    topSet π (k + 1) = insert (π ⟨k, hk⟩) (topSet π k) := by
  ext y
  rw [mem_insert, cm_mem_topSet, cm_mem_topSet]
  constructor
  · intro h
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | h
    · right; exact h
    · left
      have : π.symm y = ⟨k, hk⟩ := Fin.ext h
      rw [← this]; simp
  · rintro (rfl | h)
    · simp
    · omega

lemma cm_notMem_topSet {M : ℕ} (π : Equiv.Perm (Fin M)) (k : ℕ) (hk : k < M) :
    π ⟨k, hk⟩ ∉ topSet π k := by
  rw [cm_mem_topSet]; simp

lemma cm_topSet_swap {M : ℕ} (π : Equiv.Perm (Fin M)) (k : ℕ) (hk : k < M) (x : Fin M)
    (hx : x ∉ topSet π k) (l : ℕ) (hl : l ≤ k) :
    topSet (π.trans (Equiv.swap (π ⟨k, hk⟩) x)) l = topSet π l := by
  unfold topSet
  apply image_congr
  intro j hj
  simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hj
  simp only [Equiv.trans_apply]
  apply Equiv.swap_apply_of_ne_of_ne
  · intro h
    have := π.injective h
    rw [this] at hj; simp at hj; omega
  · intro h; apply hx; rw [← h, cm_mem_topSet]; simp; omega

lemma cm_chain_step {M : ℕ} (P : Finset (Fin M) → Prop)
    (hU : ∀ S T, P S → P T → P (S ∪ T) ∧ P (S ∩ T)) (huniv : P univ)
    (hsep : ∀ i j : Fin M, i ≠ j → ∃ g, P g ∧ ¬(i ∈ g ↔ j ∈ g))
    (S : Finset (Fin M)) (hS : P S) (hne : S ≠ univ) : ∃ x ∉ S, P (insert x S) := by
  classical
  let F := (univ : Finset (Finset (Fin M))).filter (fun T => P T ∧ S ⊂ T)
  have hF : F.Nonempty := ⟨univ, by simp [F, huniv, ssubset_univ_iff.2 hne]⟩
  obtain ⟨T, hTF, hmin⟩ := F.exists_min_image card hF
  simp only [F, mem_filter, mem_univ, true_and] at hTF
  obtain ⟨hPT, hST⟩ := hTF
  obtain ⟨x, hxT, hxS⟩ := exists_of_ssubset hST
  have aux : ∀ a b g, a ∈ T → a ∉ S → b ∈ T → b ∉ S → P g → a ∈ g → b ∉ g → False := by
    intro a b g haT haS hbT hbS hPg hag hbg
    have hP' : P ((g ∪ S) ∩ T) := (hU _ _ (hU g S hPg hS).1 hPT).2
    have hmem : (g ∪ S) ∩ T ∈ F := by
      simp only [F, mem_filter, mem_univ, true_and]
      refine ⟨hP', ?_⟩
      rw [ssubset_iff_of_subset]
      · exact ⟨a, by simp [hag, haT], haS⟩
      · intro y hy; simp [hy, hST.subset hy]
    have h1 := hmin _ hmem
    have h2 : (g ∪ S) ∩ T ⊂ T := by
      rw [ssubset_iff_of_subset inter_subset_right]
      exact ⟨b, hbT, by simp [hbg, hbS]⟩
    have := card_lt_card h2
    omega
  refine ⟨x, hxS, ?_⟩
  by_cases hT : T = insert x S
  · rw [← hT]; exact hPT
  exfalso
  have hsub : insert x S ⊆ T := insert_subset hxT hST.subset
  obtain ⟨k, hkT, hkn⟩ := exists_of_ssubset (lt_of_le_of_ne hsub (Ne.symm hT))
  rw [mem_insert, not_or] at hkn
  obtain ⟨g, hPg, hg⟩ := hsep x k (Ne.symm hkn.1)
  by_cases hxg : x ∈ g
  · exact aux x k g hxT hxS hkT hkn.2 hPg hxg (fun h => hg ⟨fun _ => h, fun _ => hxg⟩)
  · exact aux k x g hkT hkn.2 hxT hxS hPg (by tauto) hxg

lemma cm_sep {M : ℕ} (p : Params M) (W : Fin M → ℝ) (hW : W ∈ Set.extremePoints ℝ p.Hss)
    (i j : Fin M) (hij : i ≠ j) :
    ∃ g, (∑ k ∈ g, p.rho k * W k = p.f g) ∧ ¬(i ∈ g ↔ j ∈ g) := by
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  obtain ⟨hmem, hext⟩ := mem_extremePoints.1 hW
  rw [cm_mem_Hss_iff] at hmem
  set d : Fin M → ℝ := fun k => (if k = i then 1 / p.rho i else 0) -
    (if k = j then 1 / p.rho j else 0) with hd
  have hc : ∀ g : Finset (Fin M), ∑ k ∈ g, p.rho k * d k =
      (if i ∈ g then 1 else 0) - (if j ∈ g then 1 else 0) := by
    intro g
    simp [hd, mul_sub, sum_sub_distrib, (cm_rho_pos p i).ne', (cm_rho_pos p j).ne']
  have hlin : ∀ (t : ℝ) (g : Finset (Fin M)), ∑ k ∈ g, p.rho k * (W + t • d) k =
      ∑ k ∈ g, p.rho k * W k + t * ∑ k ∈ g, p.rho k * d k := by
    intro t g
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, sum_add_distrib, mul_sum]
    congr 1
    exact sum_congr rfl fun k _ => by ring
  have hev : ∀ᶠ t in nhds (0:ℝ), ∀ g, p.f g ≤ ∑ k ∈ g, p.rho k * (W + t • d) k := by
    rw [Filter.eventually_all]
    intro g
    simp only [hlin]
    by_cases ht : ∑ k ∈ g, p.rho k * W k = p.f g
    · have h0 : ∑ k ∈ g, p.rho k * d k = 0 := by
        rw [hc]
        by_cases hi : i ∈ g
        · have hj : j ∈ g := (hcon g ht).1 hi
          simp [hi, hj]
        · have hj : j ∉ g := fun h => hi ((hcon g ht).2 h)
          simp [hi, hj]
      exact Filter.Eventually.of_forall fun t => by rw [h0]; linarith [hmem.2 g]
    · have hlt : p.f g < ∑ k ∈ g, p.rho k * W k + 0 * ∑ k ∈ g, p.rho k * d k := by
        rw [zero_mul, add_zero]; exact lt_of_le_of_ne (hmem.2 g) (Ne.symm ht)
      have hcont : Continuous fun t : ℝ =>
          ∑ k ∈ g, p.rho k * W k + t * ∑ k ∈ g, p.rho k * d k := by fun_prop
      exact ((hcont.tendsto 0).eventually (lt_mem_nhds hlt)).mono fun t ht => ht.le
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hev
  have hmemt : ∀ t : ℝ, |t| < ε → W + t • d ∈ p.Hss := by
    intro t ht
    rw [cm_mem_Hss_iff]
    refine ⟨?_, hball (by simpa [Real.dist_eq] using ht)⟩
    rw [hlin, hc]; simp [hmem.1]
  have h1 := hmemt (ε/2) (by rw [abs_of_pos (by linarith)]; linarith)
  have h2 := hmemt (-(ε/2)) (by rw [abs_neg, abs_of_pos (by linarith)]; linarith)
  have hseg : W ∈ openSegment ℝ (W + (ε/2) • d) (W + (-(ε/2)) • d) :=
    ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, by ext k; simp; ring⟩
  have := (hext _ h1 _ h2 hseg).1
  have hk := congrFun this i
  simp [hd, hij, (cm_rho_pos p i).ne'] at hk
  linarith

theorem lemma2_core {M : ℕ} (p : Params M) :
    ∀ W ∈ Set.extremePoints ℝ p.Hss, ∃ π : Equiv.Perm (Fin M), W = p.prioVec π := by
  intro W hW
  have hmem := (cm_mem_Hss_iff p W).1 hW.1
  let P : Finset (Fin M) → Prop := fun g => ∑ k ∈ g, p.rho k * W k = p.f g
  have hU : ∀ S T, P S → P T → P (S ∪ T) ∧ P (S ∩ T) :=
    fun S T hS hT => cm_tight p W hmem.2 S T hS hT
  have huniv : P univ := hmem.1
  have hsep := cm_sep p W hW
  have hchain : ∀ k ≤ M, ∃ π : Equiv.Perm (Fin M), ∀ l ≤ k, P (topSet π l) := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨1, fun l hl => by
        rw [Nat.le_zero.1 hl, cm_topSet_zero]; simp [P, cm_f_empty]⟩
    | succ k ih =>
      intro hk
      obtain ⟨π, hπ⟩ := ih (by omega)
      have hk' : k < M := by omega
      have hne : topSet π k ≠ univ := fun h =>
        cm_notMem_topSet π k hk' (by rw [h]; exact mem_univ _)
      obtain ⟨x, hx, hPx⟩ := cm_chain_step P hU huniv hsep _ (hπ k le_rfl) hne
      refine ⟨π.trans (Equiv.swap (π ⟨k, hk'⟩) x), fun l hl => ?_⟩
      rcases Nat.lt_or_eq_of_le hl with hl | rfl
      · rw [cm_topSet_swap π k hk' x hx l (by omega)]; exact hπ l (by omega)
      · rw [cm_topSet_succ _ k hk', cm_topSet_swap π k hk' x hx k le_rfl]
        simpa using hPx
  obtain ⟨π, hπ⟩ := hchain M le_rfl
  refine ⟨π, funext fun i => ?_⟩
  have hr := (π.symm i).isLt
  have h1 := hπ ((π.symm i : ℕ) + 1) (by omega)
  have h0 := hπ (π.symm i : ℕ) (by omega)
  simp only [P] at h1 h0
  rw [cm_topSet_succ π _ hr, sum_insert (cm_notMem_topSet π _ hr)] at h1
  simp only [Fin.eta, Equiv.apply_symm_apply] at h1
  have e := cm_topSet_succ π _ hr
  simp only [Fin.eta, Equiv.apply_symm_apply] at e
  unfold Params.prioVec
  rw [e, eq_div_iff (cm_rho_pos p i).ne']
  linarith

end CoffmanMitrani1980.Region

open CoffmanMitrani1980.Region


theorem solution {M : ℕ} (p : Params M) :
    ∀ W ∈ Set.extremePoints ℝ p.Hss, ∃ π : Equiv.Perm (Fin M), W = p.prioVec π := by
  exact lemma2_core p
