-- Prove2me | solution 1 for CountOrderings.NFree.display_A12_limit
-- status  : ACCEPTED   (prove)
-- author  : @bersubs
-- created : 2026-11-15T17:31:36.017211+00:00
-- url     : https://prove2.me/submissions/1f9bc90a-7bbf-47cf-ab89-54c6b26efa2a

import Theorems.Thm_CountOrderings_NFree_lemma_6_1
import Theorems.Thm_CountOrderings_NFree_lemma_6_2

open Filter Topology

namespace CountOrderings.NFree

private def rootEdge (I : X3CInstance) (s : Fin I.n) : OrigEdge I :=
  ⟨.rootSet s, trivial⟩

private def incidenceEdge (I : X3CInstance) (s : Fin I.n) (j : Fin (3 * I.h))
    (hsj : j ∈ I.S s) : OrigEdge I := ⟨.setElem s j, hsj⟩

private noncomputable def incomingPositions {I : X3CInstance}
    (σ : Fin (4 * I.n) ≃ OrigEdge I) (j : Fin (3 * I.h)) : Finset (Fin (4 * I.n)) := by
  classical
  exact Finset.univ.filter (fun p => ∃ s : Fin I.n, (σ p).1 = .setElem s j)

private theorem mem_incomingPositions {I : X3CInstance}
    (σ : Fin (4 * I.n) ≃ OrigEdge I) (j : Fin (3 * I.h)) (p : Fin (4 * I.n)) :
    p ∈ incomingPositions σ j ↔ ∃ s : Fin I.n, (σ p).1 = .setElem s j := by
  classical
  simp [incomingPositions]

private theorem incomingPositions_nonempty {I : X3CInstance} (hI : I.Standing)
    (σ : Fin (4 * I.n) ≃ OrigEdge I) (j : Fin (3 * I.h)) :
    (incomingPositions σ j).Nonempty := by
  obtain ⟨s, hsj⟩ := hI.1 j
  refine ⟨σ.symm (incidenceEdge I s j hsj), (mem_incomingPositions ..).mpr ⟨s, ?_⟩⟩
  rw [Equiv.apply_symm_apply]
  rfl

private noncomputable def lastPosition {I : X3CInstance} (hI : I.Standing)
    (σ : Fin (4 * I.n) ≃ OrigEdge I) (j : Fin (3 * I.h)) : Fin (4 * I.n) :=
  (incomingPositions σ j).max' (incomingPositions_nonempty hI σ j)

private theorem lastPosition_spec {I : X3CInstance} (hI : I.Standing)
    (σ : Fin (4 * I.n) ≃ OrigEdge I) (j : Fin (3 * I.h)) :
    ∃ s : Fin I.n, (σ (lastPosition hI σ j)).1 = .setElem s j :=
  (mem_incomingPositions ..).mp (Finset.max'_mem _ _)

private theorem le_lastPosition {I : X3CInstance} (hI : I.Standing)
    (σ : Fin (4 * I.n) ≃ OrigEdge I) (j : Fin (3 * I.h)) {p : Fin (4 * I.n)}
    (hp : ∃ s : Fin I.n, (σ p).1 = .setElem s j) : p ≤ lastPosition hI σ j :=
  Finset.le_max' _ _ ((mem_incomingPositions ..).mpr hp)

private theorem rho_eq_lastPosition {I : X3CInstance} (hI : I.Standing)
    (σ : Fin (4 * I.n) ≃ OrigEdge I) (j : Fin (3 * I.h)) :
    rho σ j = (lastPosition hI σ j).val + 1 := by
  change (incomingPositions σ j).sup (fun p => p.val + 1) = _
  apply le_antisymm
  · refine Finset.sup_le_iff.mpr fun p hp => Nat.succ_le_succ ?_
    exact le_lastPosition hI σ j ((mem_incomingPositions ..).mp hp)
  · exact Finset.le_sup (f := fun p : Fin (4 * I.n) => p.val + 1) (Finset.max'_mem _ _)

private noncomputable def marker {I : X3CInstance} (hI : I.Standing)
    (σ : Fin (4 * I.n) ≃ OrigEdge I) : Fin (3 * I.h) ⊕ Fin I.n ↪ Fin (4 * I.n) where
  toFun := Sum.elim (lastPosition hI σ) (fun s => σ.symm (rootEdge I s))
  inj' := by
    rintro (j | s) (k | t) h
    · change lastPosition hI σ j = lastPosition hI σ k at h
      obtain ⟨s, hs⟩ := lastPosition_spec hI σ j
      obtain ⟨t, ht⟩ := lastPosition_spec hI σ k
      rw [h, ht] at hs
      cases hs
      rfl
    · change lastPosition hI σ j = σ.symm (rootEdge I t) at h
      obtain ⟨s, hs⟩ := lastPosition_spec hI σ j
      rw [h, Equiv.apply_symm_apply] at hs
      cases hs
    · change σ.symm (rootEdge I s) = lastPosition hI σ k at h
      obtain ⟨t, ht⟩ := lastPosition_spec hI σ k
      rw [← h, Equiv.apply_symm_apply] at ht
      cases ht
    · change σ.symm (rootEdge I s) = σ.symm (rootEdge I t) at h
      have hs := congrArg Subtype.val (σ.symm.injective h)
      cases hs
      rfl

private noncomputable def marked {I : X3CInstance} (hI : I.Standing)
    (σ : Fin (4 * I.n) ≃ OrigEdge I) : Finset (Fin (4 * I.n)) :=
  Finset.univ.map (marker hI σ)

private def suffix (I : X3CInstance) (i : ℕ) : Finset (Fin (4 * I.n)) :=
  Finset.univ.filter (fun p => 4 * I.n ≤ p.val + i)

private theorem mem_suffix {I : X3CInstance} (i : ℕ) (p : Fin (4 * I.n)) :
    p ∈ suffix I i ↔ 4 * I.n ≤ p.val + i := by
  simp [suffix]

private theorem rootPosition_iff {I : X3CInstance}
    (σ : Fin (4 * I.n) ≃ OrigEdge I) (p : Fin (4 * I.n)) (s : Fin I.n) :
    p = σ.symm (rootEdge I s) ↔ (σ p).1 = .rootSet s := by
  constructor
  · rintro rfl
    rw [Equiv.apply_symm_apply]
    rfl
  · intro hp
    apply σ.injective
    rw [Equiv.apply_symm_apply]
    exact Subtype.ext hp

private theorem Ccount_eq_marked {I : X3CInstance} (hI : I.Standing)
    (σ : Fin (4 * I.n) ≃ OrigEdge I) (i : ℕ) (hi : i ≤ 4 * I.n) :
    Ccount σ i = ((suffix I i).filter (fun p => p ∈ marked hI σ)).card := by
  classical
  unfold Ccount
  let Y : Finset (Fin (3 * I.h)) :=
    Finset.univ.filter (fun j => 4 * I.n + 1 - i ≤ rho σ j)
  let X : Finset (Fin I.n) := Finset.univ.filter (fun s => ∃ p : Fin (4 * I.n),
    4 * I.n + 1 - i ≤ p.val + 1 ∧ (σ p).1 = .rootSet s)
  change Y.card + X.card = _
  have hmem (z : Fin (3 * I.h) ⊕ Fin I.n) : z ∈ Y.disjSum X ↔
      marker hI σ z ∈ suffix I i := by
    cases z with
    | inl j =>
      simp only [Y, Finset.inl_mem_disjSum, Finset.mem_filter, Finset.mem_univ, true_and,
        rho_eq_lastPosition hI, mem_suffix]
      change 4 * I.n + 1 - i ≤ (lastPosition hI σ j).val + 1 ↔
        4 * I.n ≤ (lastPosition hI σ j).val + i
      omega
    | inr s =>
      simp only [X, Finset.inr_mem_disjSum, Finset.mem_filter, Finset.mem_univ, true_and,
        ← rootPosition_iff σ, mem_suffix]
      change (∃ p : Fin (4 * I.n), 4 * I.n + 1 - i ≤ p.val + 1 ∧
        p = σ.symm (rootEdge I s)) ↔ 4 * I.n ≤ (σ.symm (rootEdge I s)).val + i
      constructor
      · rintro ⟨p, hp, rfl⟩
        omega
      · intro hp
        exact ⟨_, by omega, rfl⟩
  rw [← Finset.card_disjSum, ← Finset.card_map (f := marker hI σ)]
  apply congrArg Finset.card
  ext p
  simp only [marked, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, hmem]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨hz, z, rfl⟩
  · rintro ⟨hp, z, rfl⟩
    exact ⟨z, hp, rfl⟩

private theorem suffix_step {I : X3CInstance} (i : ℕ) (hi : i < 4 * I.n) :
    suffix I (i + 1) =
      insert (⟨4 * I.n - (i + 1), by omega⟩ : Fin (4 * I.n)) (suffix I i) := by
  ext p
  simp only [mem_suffix, Finset.mem_insert, Fin.ext_iff]
  omega

private theorem Ccount_succ_le {I : X3CInstance} (hI : I.Standing)
    (σ : Fin (4 * I.n) ≃ OrigEdge I) (i : ℕ) (hi : i < 4 * I.n) :
    Ccount σ (i + 1) ≤ Ccount σ i + 1 := by
  rw [Ccount_eq_marked hI σ (i + 1) (by omega),
    Ccount_eq_marked hI σ i (by omega), suffix_step i hi, Finset.filter_insert]
  split
  · exact Finset.card_insert_le _ _
  · omega

private noncomputable def poleIndices {I : X3CInstance} (σ : Fin (4 * I.n) ≃ OrigEdge I) : Finset ℕ :=
  (Finset.Icc 1 (4 * I.n)).filter fun i => Ccount σ i = i

private noncomputable def regularFactor {I : X3CInstance} (σ : Fin (4 * I.n) ≃ OrigEdge I)
    (i : ℕ) (q : ℝ) : ℝ :=
  if Ccount σ i = i then 1 / (i : ℝ) else 1 / ((i : ℝ) + q * (Ccount σ i : ℝ))

private noncomputable def regularProduct {I : X3CInstance} (σ : Fin (4 * I.n) ≃ OrigEdge I)
    (q : ℝ) : ℝ :=
  ∏ i ∈ Finset.Icc 1 (4 * I.n), regularFactor σ i q

private noncomputable def suffixWeight {I : X3CInstance} (σ : Fin (4 * I.n) ≃ OrigEdge I) : ℝ :=
  ∏ i ∈ Finset.Icc (4 * I.h + 1) (4 * I.n), 1 / ((i : ℝ) - (Ccount σ i : ℝ))

private theorem tendsto_shift :
    Tendsto (fun q : ℝ => q + 1) (𝓝[≠] (-1)) (𝓝 0) := by
  have h : Tendsto (fun q : ℝ => q) (𝓝[≠] (-1)) (𝓝 (-1)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  simpa using h.add_const 1

private theorem regularProduct_eq {I : X3CInstance} (σ : Fin (4 * I.n) ≃ OrigEdge I)
    (q : ℝ) (hq : q + 1 ≠ 0) :
    (q + 1) ^ (poleIndices σ).card * chi σ q = regularProduct σ q := by
  have hp : (∏ i ∈ Finset.Icc 1 (4 * I.n),
      (q + 1) ^ (if Ccount σ i = i then 1 else 0)) = (q + 1) ^ (poleIndices σ).card := by
    rw [Finset.prod_pow_eq_pow_sum, Finset.sum_boole]
    rfl
  rw [← hp, chi, regularProduct, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i hi => ?_
  by_cases h : Ccount σ i = i
  · have hi0 : i ≠ 0 := by have := (Finset.mem_Icc.mp hi).1; omega
    have hir : (i : ℝ) ≠ 0 := by exact_mod_cast hi0
    simp only [regularFactor, h, if_true, pow_one]
    rw [show (i : ℝ) + q * (i : ℝ) = (i : ℝ) * (q + 1) by ring]
    field_simp
  · simp [regularFactor, h]

private theorem tendsto_regularProduct {I : X3CInstance} (σ : Fin (4 * I.n) ≃ OrigEdge I) :
    Tendsto (regularProduct σ) (𝓝[≠] (-1)) (𝓝 (regularProduct σ (-1))) := by
  unfold regularProduct
  apply tendsto_finsetProd
  intro i _
  unfold regularFactor
  by_cases h : Ccount σ i = i
  · simp only [if_pos h]
    exact tendsto_const_nhds
  · simp only [if_neg h]
    have hn : (i : ℝ) + (-1 : ℝ) * (Ccount σ i : ℝ) ≠ 0 := by
      have hcast : (Ccount σ i : ℝ) ≠ (i : ℝ) := by exact_mod_cast h
      simpa [sub_eq_add_neg] using sub_ne_zero.mpr hcast.symm
    have hc : ContinuousAt (fun q : ℝ => (i : ℝ) + q * (Ccount σ i : ℝ)) (-1) := by
      fun_prop
    have hOne : ContinuousAt (fun _ : ℝ => (1 : ℝ)) (-1) := continuousAt_const
    exact (hOne.div hc hn).tendsto.mono_left nhdsWithin_le_nhds

private theorem tendsto_normalized_chi {I : X3CInstance} (σ : Fin (4 * I.n) ≃ OrigEdge I)
    {k : ℕ} (hk : (poleIndices σ).card ≤ k) :
    Tendsto (fun q : ℝ => (q + 1) ^ k * chi σ q) (𝓝[≠] (-1))
      (𝓝 ((0 : ℝ) ^ (k - (poleIndices σ).card) * regularProduct σ (-1))) := by
  refine ((tendsto_shift.pow _).mul (tendsto_regularProduct σ)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with q hq
  have hq' : q + 1 ≠ 0 := by
    intro h
    exact (show q ≠ (-1 : ℝ) from hq) (by linarith)
  rw [← regularProduct_eq σ q hq', ← mul_assoc, ← pow_add, Nat.sub_add_cancel hk]

private theorem prod_Icc_natCast (k : ℕ) :
    (∏ i ∈ Finset.Icc 1 k, (i : ℝ)) = (k.factorial : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hIcc : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
      ext i
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hm : k + 1 ∉ Finset.Icc 1 k := by simp
    rw [hIcc, Finset.prod_insert hm, ih, Nat.factorial_succ, Nat.cast_mul]

private theorem tendsto_exact_cover {I : X3CInstance} (hI : I.Standing)
    (σ : Fin (4 * I.n) ≃ OrigEdge I)
    (hfirst : ∀ i ∈ Finset.Icc 1 (4 * I.h), Ccount σ i = i)
    (hlast : ∀ i ∈ Finset.Icc (4 * I.h + 1) (4 * I.n), Ccount σ i < i) :
    Tendsto (fun q : ℝ => (q + 1) ^ (4 * I.h) * chi σ q) (𝓝[≠] (-1))
      (𝓝 (1 / ((4 * I.h).factorial : ℝ) * suffixWeight σ)) := by
  have hh := hI.2
  have hsub : Finset.Icc 1 (4 * I.h) ⊆ Finset.Icc 1 (4 * I.n) := by
    intro i hi
    have h := Finset.mem_Icc.mp hi
    exact Finset.mem_Icc.mpr ⟨h.1, by omega⟩
  have hdifference :
      Finset.Icc 1 (4 * I.n) \ Finset.Icc 1 (4 * I.h) =
        Finset.Icc (4 * I.h + 1) (4 * I.n) := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_Icc]
    omega
  have hpoles : poleIndices σ = Finset.Icc 1 (4 * I.h) := by
    apply Finset.ext
    intro i
    rw [poleIndices, Finset.mem_filter]
    constructor
    · rintro ⟨ht, h⟩
      by_contra he
      have hi : i ∈ Finset.Icc (4 * I.h + 1) (4 * I.n) := by
        rw [← hdifference]
        exact Finset.mem_sdiff.mpr ⟨ht, he⟩
      exact (hlast i hi).ne h
    · exact fun h => ⟨hsub h, hfirst i h⟩
  have hfirst_prod :
      (∏ i ∈ Finset.Icc 1 (4 * I.h), regularFactor σ i (-1)) =
        1 / ((4 * I.h).factorial : ℝ) := by
    calc
      _ = ∏ i ∈ Finset.Icc 1 (4 * I.h), (i : ℝ)⁻¹ := by
        apply Finset.prod_congr rfl
        intro i hi
        simp [regularFactor, hfirst i hi, one_div]
      _ = _ := by rw [Finset.prod_inv_distrib, prod_Icc_natCast, one_div]
  have hlast_prod :
      (∏ i ∈ Finset.Icc (4 * I.h + 1) (4 * I.n), regularFactor σ i (-1)) =
        suffixWeight σ := by
    apply Finset.prod_congr rfl
    intro i hi
    simp [regularFactor, (hlast i hi).ne, sub_eq_add_neg]
  have hr : regularProduct σ (-1) = 1 / ((4 * I.h).factorial : ℝ) * suffixWeight σ := by
    rw [regularProduct, ← Finset.prod_sdiff hsub, hdifference, hfirst_prod, hlast_prod, mul_comm]
  have hcard : (poleIndices σ).card = 4 * I.h := by simp [hpoles]
  simpa [hcard, hr] using (tendsto_normalized_chi σ (k := 4 * I.h) hcard.le)

private theorem tendsto_noncover {I : X3CInstance} (hI : I.Standing)
    (σ : Fin (4 * I.n) ≃ OrigEdge I)
    (hstep : ∀ i < 4 * I.n, Ccount σ (i + 1) ≤ Ccount σ i + 1)
    (hdeficit : ((Finset.Icc 1 (4 * I.h)).filter fun i => Ccount σ i < i).Nonempty) :
    Tendsto (fun q : ℝ => (q + 1) ^ (4 * I.h) * chi σ q) (𝓝[≠] (-1)) (𝓝 0) := by
  have hh := hI.2
  obtain ⟨i, hi⟩ := hdeficit
  obtain ⟨hiRange, hiDeficit⟩ := Finset.mem_filter.mp hi
  have hBounds := Finset.mem_Icc.mp hiRange
  have hpropagate (j : ℕ) (hij : i ≤ j) (hjn : j ≤ 4 * I.n) : Ccount σ j < j := by
    induction j with
    | zero => omega
    | succ j ih =>
      by_cases hb : i ≤ j
      · have hprev := ih hb (by omega)
        have hnew := hstep j (by omega)
        omega
      · have he : j + 1 = i := by omega
        simpa [he] using hiDeficit
  have hsub : poleIndices σ ⊆ Finset.Icc 1 (4 * I.h) := by
    intro j hj
    obtain ⟨hRange, hEq⟩ := Finset.mem_filter.mp hj
    have hb := Finset.mem_Icc.mp hRange
    have hij : j < i := by
      by_contra! hge
      exact (hpropagate j hge hb.2).ne hEq
    exact Finset.mem_Icc.mpr ⟨hb.1, by omega⟩
  have hssub : poleIndices σ ⊂ Finset.Icc 1 (4 * I.h) :=
    (Finset.ssubset_iff_of_subset hsub).mpr ⟨i, hiRange, fun hm =>
      hiDeficit.ne (Finset.mem_filter.mp hm).2⟩
  have hcard : (poleIndices σ).card < 4 * I.h := by
    simpa using Finset.card_lt_card hssub
  have hne : 4 * I.h - (poleIndices σ).card ≠ 0 := by omega
  simpa [zero_pow hne] using (tendsto_normalized_chi σ (k := 4 * I.h) hcard.le)

private theorem omegaXC_pairwise_disjoint (I : X3CInstance) :
    Set.PairwiseDisjoint (↑I.exactCovers) (omegaXC I) := by
  intro X _ Y _ hXY
  change Disjoint (omegaXC I X) (omegaXC I Y)
  rw [Finset.disjoint_left]
  intro σ hX hY
  have he : edgesOf I X = edgesOf I Y :=
    (Finset.mem_filter.mp hX).2.symm.trans (Finset.mem_filter.mp hY).2
  apply hXY
  apply Finset.ext
  intro i
  let r : OrigEdge I := ⟨.rootSet i, trivial⟩
  have hmem (Z : Finset (Fin I.n)) : r ∈ edgesOf I Z ↔ i ∈ Z := by
    unfold edgesOf
    rw [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  rw [← hmem X, ← hmem Y, he]

private theorem scaled_constant_sum (I : X3CInstance) (hI : I.Standing) :
    1 / ((4 * I.h).factorial : ℝ) * ∑ _X ∈ I.exactCovers,
        ((4 * I.h).factorial : ℝ) / ((4 : ℝ) ^ I.h * (3 : ℝ) ^ (I.n - I.h)) =
      (4 : ℝ) ^ (-(I.h : ℤ)) * (3 : ℝ) ^ ((I.h : ℤ) - I.n) * I.numExactCovers := by
  have hh := hI.2
  have hpow : (I.h : ℤ) - I.n = -((I.n - I.h : ℕ) : ℤ) := by omega
  rw [Finset.sum_const, nsmul_eq_mul, ← X3CInstance.numExactCovers,
    hpow, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
  have hf : (((4 * I.h).factorial : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp

private theorem limit_from_pole_steps (I : X3CInstance) (hI : I.Standing)
    (hstep : ∀ (σ : Fin (4 * I.n) ≃ OrigEdge I) (i : ℕ), i < 4 * I.n →
      Ccount σ (i + 1) ≤ Ccount σ i + 1) :
    Tendsto (fun q : ℝ => (q + 1) ^ (4 * I.h) * ∑ σ ∈ omegaLE I, chi σ q) (𝓝[≠] (-1))
        (𝓝 ((4 : ℝ) ^ (-(I.h : ℤ)) * (3 : ℝ) ^ ((I.h : ℤ) - I.n) * I.numExactCovers)) ∧
      Tendsto (fun q : ℝ => ∑ X ∈ I.exactCovers, ∑ σ ∈ omegaXC I X, (q + 1) ^ (4 * I.h) * chi σ q)
        (𝓝[≠] (-1))
        (𝓝 ((4 : ℝ) ^ (-(I.h : ℤ)) * (3 : ℝ) ^ ((I.h : ℤ) - I.n) * I.numExactCovers)) ∧
      1 / ((4 * I.h).factorial : ℝ) * ∑ X ∈ I.exactCovers, ∑ σ ∈ omegaXC I X,
          ∏ i ∈ Finset.Icc (4 * I.h + 1) (4 * I.n), 1 / ((i : ℝ) - (Ccount σ i : ℝ)) =
        (4 : ℝ) ^ (-(I.h : ℤ)) * (3 : ℝ) ^ ((I.h : ℤ) - I.n) * I.numExactCovers ∧
      1 / ((4 * I.h).factorial : ℝ) * ∑ _X ∈ I.exactCovers,
          ((4 * I.h).factorial : ℝ) / ((4 : ℝ) ^ I.h * (3 : ℝ) ^ (I.n - I.h)) =
        (4 : ℝ) ^ (-(I.h : ℤ)) * (3 : ℝ) ^ ((I.h : ℤ) - I.n) * I.numExactCovers := by
  classical
  let W := (4 : ℝ) ^ (-(I.h : ℤ)) * (3 : ℝ) ^ ((I.h : ℤ) - I.n) * I.numExactCovers
  have hconst := scaled_constant_sum I hI
  have hweights :
      (1 / ((4 * I.h).factorial : ℝ) *
        ∑ X ∈ I.exactCovers, ∑ σ ∈ omegaXC I X, suffixWeight σ) = W := by
    have hsum :
        (∑ X ∈ I.exactCovers, ∑ σ ∈ omegaXC I X, suffixWeight σ) =
          ∑ _X ∈ I.exactCovers,
            ((4 * I.h).factorial : ℝ) / ((4 : ℝ) ^ I.h * (3 : ℝ) ^ (I.n - I.h)) := by
      exact Finset.sum_congr rfl fun X hX => lemma_6_2 I hI X hX
    rw [hsum]
    exact hconst
  have hcover :
      Tendsto (fun q : ℝ => ∑ X ∈ I.exactCovers, ∑ σ ∈ omegaXC I X,
        (q + 1) ^ (4 * I.h) * chi σ q) (𝓝[≠] (-1)) (𝓝 W) := by
    rw [← hweights, Finset.mul_sum]
    simp_rw [Finset.mul_sum]
    apply tendsto_finsetSum
    intro X hX
    apply tendsto_finsetSum
    intro σ hσ
    have hLE : σ ∈ omegaLE I := (Finset.mem_filter.mp hσ).1
    obtain ⟨hf, hl⟩ := (lemma_6_1 I hI σ hLE).1 X hX hσ
    exact tendsto_exact_cover hI σ hf hl
  refine ⟨?_, hcover, hweights, hconst⟩
  let C := I.exactCovers.biUnion (omegaXC I)
  have hsub : C ⊆ omegaLE I := by
    intro σ hσ
    obtain ⟨X, _, hX⟩ := Finset.mem_biUnion.mp hσ
    exact (Finset.mem_filter.mp hX).1
  have hC :
      Tendsto (fun q : ℝ => ∑ σ ∈ C, (q + 1) ^ (4 * I.h) * chi σ q)
        (𝓝[≠] (-1)) (𝓝 W) := by
    simpa only [C, Finset.sum_biUnion (omegaXC_pairwise_disjoint I)] using hcover
  have hNC :
      Tendsto (fun q : ℝ => ∑ σ ∈ omegaLE I \ C, (q + 1) ^ (4 * I.h) * chi σ q)
        (𝓝[≠] (-1)) (𝓝 0) := by
    rw [← Finset.sum_const_zero (s := omegaLE I \ C)]
    apply tendsto_finsetSum
    intro σ hσ
    obtain ⟨hLE, hb⟩ := Finset.mem_sdiff.mp hσ
    have hno : ¬ ∃ X ∈ I.exactCovers, σ ∈ omegaXC I X := by
      rintro ⟨X, hX, hs⟩
      exact hb (Finset.mem_biUnion.mpr ⟨X, hX, hs⟩)
    exact tendsto_noncover hI σ (hstep σ) ((lemma_6_1 I hI σ hLE).2 hno)
  simp_rw [Finset.mul_sum]
  simpa only [Finset.sum_sdiff hsub, zero_add] using hNC.add hC

end CountOrderings.NFree

open CountOrderings.NFree in
theorem solution (I : X3CInstance) (hI : I.Standing) :
    Tendsto (fun q : ℝ => (q + 1) ^ (4 * I.h) * ∑ σ ∈ omegaLE I, chi σ q) (𝓝[≠] (-1))
        (𝓝 ((4 : ℝ) ^ (-(I.h : ℤ)) * (3 : ℝ) ^ ((I.h : ℤ) - I.n) * I.numExactCovers)) ∧
      Tendsto (fun q : ℝ => ∑ X ∈ I.exactCovers, ∑ σ ∈ omegaXC I X, (q + 1) ^ (4 * I.h) * chi σ q)
        (𝓝[≠] (-1))
        (𝓝 ((4 : ℝ) ^ (-(I.h : ℤ)) * (3 : ℝ) ^ ((I.h : ℤ) - I.n) * I.numExactCovers)) ∧
      1 / ((4 * I.h).factorial : ℝ) * ∑ X ∈ I.exactCovers, ∑ σ ∈ omegaXC I X,
          ∏ i ∈ Finset.Icc (4 * I.h + 1) (4 * I.n), 1 / ((i : ℝ) - (Ccount σ i : ℝ)) =
        (4 : ℝ) ^ (-(I.h : ℤ)) * (3 : ℝ) ^ ((I.h : ℤ) - I.n) * I.numExactCovers ∧
      1 / ((4 * I.h).factorial : ℝ) * ∑ _X ∈ I.exactCovers,
          ((4 * I.h).factorial : ℝ) / ((4 : ℝ) ^ I.h * (3 : ℝ) ^ (I.n - I.h)) =
        (4 : ℝ) ^ (-(I.h : ℤ)) * (3 : ℝ) ^ ((I.h : ℤ) - I.n) * I.numExactCovers := by
  exact limit_from_pole_steps I hI (Ccount_succ_le hI)
