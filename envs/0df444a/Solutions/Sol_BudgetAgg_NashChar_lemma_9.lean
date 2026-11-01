-- Prove2me | solution 1 for BudgetAgg.NashChar.lemma_9
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T21:13:50.428813+00:00
-- url     : https://prove2.me/submissions/2ddfaac4-3554-447f-a237-df4b5a989129

import Mathlib
import Definitions.Def_BudgetAgg_NashChar_Setting
import Theorems.Thm_BudgetAgg_NashChar_lemma_7

open BudgetAgg.NashChar

theorem nc_leontief_le {m : ℕ} (p : stdSimplex ℝ (Fin m)) (q : Fin m → ℝ) (k : Fin m)
    (hk : 0 < p.1 k) : leontief p q ≤ q k / p.1 k := by
  unfold leontief
  exact Finset.inf'_le _ (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩)

theorem nc_lt_leontief {m : ℕ} (p : stdSimplex ℝ (Fin m)) (q : Fin m → ℝ) (c : ℝ)
    (h : ∀ k, 0 < p.1 k → c < q k / p.1 k) : c < leontief p q := by
  unfold leontief
  rw [Finset.lt_inf'_iff]
  intro k hk
  exact h k (Finset.mem_filter.mp hk).2

theorem nc_exists_crit {m : ℕ} (p : stdSimplex ℝ (Fin m)) (q : Fin m → ℝ) :
    ∃ k, 0 < p.1 k ∧ q k / p.1 k = leontief p q := by
  unfold leontief
  obtain ⟨k, hk, he⟩ := Finset.exists_mem_eq_inf' (positive_support_nonempty p)
    (fun j => q j / p.1 j)
  exact ⟨k, (Finset.mem_filter.mp hk).2, he.symm⟩

theorem nc_mem_crit {m : ℕ} (p : stdSimplex ℝ (Fin m)) (q : Fin m → ℝ) (k : Fin m) :
    k ∈ crit p q ↔ 0 < p.1 k ∧ q k / p.1 k = leontief p q := by
  unfold crit
  simp [Finset.mem_filter]

/-- A distribution that makes every agent strictly better off violates core fair share
(take the grand coalition). -/
theorem nc_not_core {n m : ℕ} [NeZero n] (P : Profile n m) (q qs : stdSimplex ℝ (Fin m))
    (h : ∀ i, leontief (P i) q.1 < leontief (P i) qs.1) : ¬ IsCoreFairShare P q := by
  intro hc
  apply hc Finset.univ Finset.univ_nonempty
  refine ⟨qs, fun q'' i _ => ?_⟩
  have hn : ((Finset.univ : Finset (Fin n)).card : ℝ) / (n : ℝ) = 1 := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact div_self (Nat.cast_ne_zero.mpr (NeZero.ne n))
  have hf : (fun j => ((Finset.univ : Finset (Fin n)).card : ℝ) / (n : ℝ) * qs.1 j +
      (1 - ((Finset.univ : Finset (Fin n)).card : ℝ) / (n : ℝ)) * q''.1 j) = qs.1 := by
    funext j; rw [hn]; ring
  rw [hf]
  exact h i

theorem nc_le_leontief {m : ℕ} (p : stdSimplex ℝ (Fin m)) (q : Fin m → ℝ) (c : ℝ)
    (h : ∀ k, 0 < p.1 k → c ≤ q k / p.1 k) : c ≤ leontief p q := by
  unfold leontief
  rw [Finset.le_inf'_iff]
  intro k hk
  exact h k (Finset.mem_filter.mp hk).2

theorem nc_leontief_nonneg {m : ℕ} (p : stdSimplex ℝ (Fin m)) (q : stdSimplex ℝ (Fin m)) :
    0 ≤ leontief p q.1 := by
  obtain ⟨k, hk, hke⟩ := nc_exists_crit p q.1
  rw [← hke]; exact div_nonneg (q.2.1 k) hk.le

theorem nc_crit_ne {m : ℕ} (p : stdSimplex ℝ (Fin m)) (q : Fin m → ℝ) : (crit p q).Nonempty := by
  obtain ⟨k, hk, hke⟩ := nc_exists_crit p q
  exact ⟨k, (nc_mem_crit _ _ k).mpr ⟨hk, hke⟩⟩

theorem nc_sigma_pos {m : ℕ} (p : stdSimplex ℝ (Fin m)) (q : Fin m → ℝ) :
    0 < ∑ k ∈ crit p q, p.1 k :=
  Finset.sum_pos (fun k hk => ((nc_mem_crit _ _ k).mp hk).1) (nc_crit_ne p q)

theorem nc_sigma_le {m : ℕ} (p : stdSimplex ℝ (Fin m)) (q : Fin m → ℝ) :
    ∑ k ∈ crit p q, p.1 k ≤ 1 := by
  rw [← p.2.2]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun k _ _ => p.2.1 k)

theorem nc_star_mem {m : ℕ} (p : stdSimplex ℝ (Fin m)) (q : Fin m → ℝ) :
    starPeak p q ∈ stdSimplex ℝ (Fin m) := by
  have hσ := nc_sigma_pos p q
  refine ⟨fun j => ?_, ?_⟩
  · unfold starPeak; split_ifs
    · exact div_nonneg (p.2.1 j) hσ.le
    · exact le_refl _
  · unfold starPeak
    rw [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.sum_div, div_self hσ.ne']

/-- The segment from `p` to its star peak. -/
noncomputable def nc_path {m : ℕ} (p : stdSimplex ℝ (Fin m)) (q : Fin m → ℝ) (t : ℝ) :
    Fin m → ℝ :=
  fun j => t * starPeak p q j + (1 - t) * p.1 j

theorem nc_path_mem {m : ℕ} (p : stdSimplex ℝ (Fin m)) (q : Fin m → ℝ) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : nc_path p q t ∈ stdSimplex ℝ (Fin m) := by
  have := (convex_stdSimplex ℝ (Fin m)) (nc_star_mem p q) p.2 ht0 (by linarith : 0 ≤ 1 - t)
    (by ring)
  convert this using 1
  funext j; simp [nc_path, smul_eq_mul]

theorem nc_path_on {m : ℕ} (p : stdSimplex ℝ (Fin m)) (q : Fin m → ℝ) (t : ℝ) (j : Fin m)
    (hj : j ∈ crit p q) :
    nc_path p q t j = (t / (∑ k ∈ crit p q, p.1 k) + (1 - t)) * p.1 j := by
  unfold nc_path starPeak; rw [if_pos hj]; ring

theorem nc_path_off {m : ℕ} (p : stdSimplex ℝ (Fin m)) (q : Fin m → ℝ) (t : ℝ) (j : Fin m)
    (hj : j ∉ crit p q) : nc_path p q t j = (1 - t) * p.1 j := by
  unfold nc_path starPeak; rw [if_neg hj]; ring

theorem nc_c_ge_one {m : ℕ} (p : stdSimplex ℝ (Fin m)) (q : Fin m → ℝ) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : 1 ≤ t / (∑ k ∈ crit p q, p.1 k) + (1 - t) := by
  have hσ := nc_sigma_pos p q
  have hσ1 := nc_sigma_le p q
  have : t ≤ t / (∑ k ∈ crit p q, p.1 k) := by
    rw [le_div_iff₀ hσ]; nlinarith
  linarith

/-- F1: critical sets at `q` do not change along the segment. -/
theorem nc_path_crit {m : ℕ} (p : stdSimplex ℝ (Fin m)) (q : stdSimplex ℝ (Fin m)) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    crit ⟨nc_path p q.1 t, nc_path_mem p q.1 t ht0 ht1⟩ q.1 = crit p q.1 := by
  set π : stdSimplex ℝ (Fin m) := ⟨nc_path p q.1 t, nc_path_mem p q.1 t ht0 ht1⟩ with hπ
  set c := t / (∑ k ∈ crit p q.1, p.1 k) + (1 - t) with hc
  have hc1 : 1 ≤ c := nc_c_ge_one p q.1 t ht0 ht1
  set u := leontief p q.1 with hu
  have hu0 : 0 ≤ u := nc_leontief_nonneg p q
  have hT : ∀ k ∈ crit p q.1, 0 < π.1 k ∧ q.1 k / π.1 k = u / c := by
    intro k hk
    obtain ⟨hp, he⟩ := (nc_mem_crit _ _ k).mp hk
    have hπk : π.1 k = c * p.1 k := nc_path_on p q.1 t k hk
    refine ⟨by rw [hπk]; positivity, ?_⟩
    rw [hπk, hu, ← he]; field_simp
  have hoff : ∀ k, k ∉ crit p q.1 → 0 < π.1 k → u / c < q.1 k / π.1 k := by
    intro k hk hπk
    have hπk' : π.1 k = (1 - t) * p.1 k := nc_path_off p q.1 t k hk
    have hp : 0 < p.1 k := by
      rw [hπk'] at hπk
      rcases lt_or_eq_of_le (p.2.1 k) with h | h
      · exact h
      · rw [← h, mul_zero] at hπk; exact absurd hπk (lt_irrefl _)
    have ht : 0 < 1 - t := by
      rw [hπk'] at hπk; exact pos_of_mul_pos_left hπk hp.le
    have hlt : u < q.1 k / p.1 k := by
      have hle := nc_leontief_le p q.1 k hp
      have hne : q.1 k / p.1 k ≠ u := fun he => hk ((nc_mem_crit _ _ k).mpr ⟨hp, he⟩)
      exact lt_of_le_of_ne hle (Ne.symm hne)
    have h1 : u / c ≤ u := div_le_self hu0 hc1
    have h2 : q.1 k / p.1 k ≤ q.1 k / π.1 k := by
      rw [hπk']
      apply div_le_div_of_nonneg_left (q.2.1 k) (by positivity)
      nlinarith
    linarith
  -- the Leontief utility under π
  have hL : leontief π q.1 = u / c := by
    apply le_antisymm
    · obtain ⟨j0, hj0⟩ := nc_crit_ne p q.1
      obtain ⟨hπ0, he0⟩ := hT j0 hj0
      rw [← he0]; exact nc_leontief_le π q.1 j0 hπ0
    · apply nc_le_leontief
      intro k hk
      by_cases hkT : k ∈ crit p q.1
      · exact le_of_eq (hT k hkT).2.symm
      · exact (hoff k hkT hk).le
  ext k
  rw [nc_mem_crit, hL]
  constructor
  · rintro ⟨hπk, he⟩
    by_contra hkT
    have := hoff k hkT hπk
    rw [he] at this; exact lt_irrefl _ this
  · intro hk; exact hT k hk

/-- F2: an open neighbourhood of `q` on which critical sets stay inside `T_{q}` along the
whole segment. -/
theorem nc_path_nbhd {m : ℕ} (p : stdSimplex ℝ (Fin m)) (q : stdSimplex ℝ (Fin m)) :
    ∃ U : Set (Fin m → ℝ), IsOpen U ∧ q.1 ∈ U ∧ ∀ t, 0 ≤ t → ∀ ht1 : t ≤ 1,
      ∀ qh : stdSimplex ℝ (Fin m), qh.1 ∈ U →
      ∀ ht0 : 0 ≤ t, crit ⟨nc_path p q.1 t, nc_path_mem p q.1 t ht0 ht1⟩ qh.1 ⊆ crit p q.1 := by
  classical
  obtain ⟨j0, hj0⟩ := nc_crit_ne p q.1
  obtain ⟨hp0, he0⟩ := (nc_mem_crit _ _ j0).mp hj0
  set F := Finset.univ.filter (fun j => 0 < p.1 j ∧ j ∉ crit p q.1)
  refine ⟨⋂ j ∈ F, {x : Fin m → ℝ | x j0 / p.1 j0 < x j / p.1 j}, ?_, ?_, ?_⟩
  · apply isOpen_biInter_finset
    intro j _
    exact isOpen_lt ((continuous_apply j0).div_const _) ((continuous_apply j).div_const _)
  · simp only [Set.mem_iInter, Set.mem_setOf_eq]
    intro j hj
    obtain ⟨hp, hjT⟩ := (Finset.mem_filter.mp hj).2
    rw [he0]
    have hle := nc_leontief_le p q.1 j hp
    have hne : q.1 j / p.1 j ≠ leontief p q.1 := fun he => hjT ((nc_mem_crit _ _ j).mpr ⟨hp, he⟩)
    exact lt_of_le_of_ne hle (Ne.symm hne)
  · intro t _ ht1 qh hU ht0 k hk
    simp only [Set.mem_iInter, Set.mem_setOf_eq] at hU
    set π : stdSimplex ℝ (Fin m) := ⟨nc_path p q.1 t, nc_path_mem p q.1 t ht0 ht1⟩
    by_contra hkT
    obtain ⟨hπk, hek⟩ := (nc_mem_crit _ _ k).mp hk
    have hπk' : π.1 k = (1 - t) * p.1 k := nc_path_off p q.1 t k hkT
    have hp : 0 < p.1 k := by
      rw [hπk'] at hπk
      rcases lt_or_eq_of_le (p.2.1 k) with h | h
      · exact h
      · rw [← h, mul_zero] at hπk; exact absurd hπk (lt_irrefl _)
    have ht : 0 < 1 - t := by rw [hπk'] at hπk; exact pos_of_mul_pos_left hπk hp.le
    have hkF : k ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp, hkT⟩
    have h1 := hU k hkF
    set c := t / (∑ k ∈ crit p q.1, p.1 k) + (1 - t)
    have hc1 : 1 ≤ c := nc_c_ge_one p q.1 t ht0 ht1
    have hπ0 : π.1 j0 = c * p.1 j0 := nc_path_on p q.1 t j0 hj0
    have hπ0pos : 0 < π.1 j0 := by rw [hπ0]; positivity
    have h2 := nc_leontief_le π qh.1 j0 hπ0pos
    have h3 : qh.1 j0 / π.1 j0 ≤ qh.1 j0 / p.1 j0 := by
      rw [hπ0]; apply div_le_div_of_nonneg_left (qh.2.1 j0) hp0; nlinarith
    have h4 : qh.1 k / p.1 k ≤ qh.1 k / π.1 k := by
      rw [hπk']; apply div_le_div_of_nonneg_left (qh.2.1 k) (by positivity); nlinarith
    linarith

/-- F3: the single-step argument (strategyproofness, group-strategyproofness, Lemma 7). -/
theorem nc_step {n m : ℕ} [NeZero n] [NeZero m] (f : Mechanism n m) (hf_gsp : IsGroupSP f)
    (hf_eff : ∀ P, IsEfficient P (f P)) (B B' : Profile n m) (a : Fin n)
    (hBB : ∀ r, r ≠ a → B' r = B r)
    (hcrit' : crit (B' a) (f B).1 = crit (B a) (f B).1)
    (hsub : crit (B a) (f B').1 ⊆ crit (B a) (f B).1) : f B' = f B := by
  classical
  set q := f B with hq
  set qh := f B' with hqh
  set T := crit (B a) q.1 with hT
  -- (1) truthful B, deviation to B'
  have h1 : leontief (B a) qh.1 ≤ leontief (B a) q.1 := by
    rcases hf_gsp {a} B B' (fun r hr => hBB r (by simpa using hr)) with h | h
    · obtain ⟨i, hi, hlt⟩ := h
      rw [Finset.mem_singleton.mp hi] at hlt; exact hlt.le
    · exact le_of_eq (h a (Finset.mem_singleton_self a)).symm
  -- (2) truthful B', deviation to B
  have h2 : leontief (B' a) q.1 ≤ leontief (B' a) qh.1 := by
    rcases hf_gsp {a} B' B (fun r hr => (hBB r (by simpa using hr)).symm) with h | h
    · obtain ⟨i, hi, hlt⟩ := h
      rw [Finset.mem_singleton.mp hi] at hlt; exact hlt.le
    · exact (h a (Finset.mem_singleton_self a)).symm.le
  -- on T, qh ≥ q
  have hT_le : ∀ j ∈ T, q.1 j ≤ qh.1 j := by
    intro j hj
    rw [← hcrit'] at hj
    obtain ⟨hp, he⟩ := (nc_mem_crit _ _ j).mp hj
    have := nc_leontief_le (B' a) qh.1 j hp
    have h3 : q.1 j / (B' a).1 j ≤ qh.1 j / (B' a).1 j := by rw [he]; linarith
    exact (div_le_div_iff_of_pos_right hp).mp h3
  have hua : leontief (B a) qh.1 = leontief (B a) q.1 := by
    apply le_antisymm h1
    obtain ⟨k, hk, hke⟩ := nc_exists_crit (B a) qh.1
    have hkT : k ∈ T := hsub ((nc_mem_crit _ _ k).mpr ⟨hk, hke⟩)
    rw [← hke]
    calc leontief (B a) q.1 ≤ q.1 k / (B a).1 k := nc_leontief_le _ _ k hk
      _ ≤ qh.1 k / (B a).1 k := div_le_div_of_nonneg_right (hT_le k hkT) hk.le
  have hua' : leontief (B' a) qh.1 = leontief (B' a) q.1 := by
    apply le_antisymm _ h2
    by_contra hlt
    push_neg at hlt
    have hTlt : ∀ j ∈ T, q.1 j < qh.1 j := by
      intro j hj
      rw [← hcrit'] at hj
      obtain ⟨hp, he⟩ := (nc_mem_crit _ _ j).mp hj
      have := nc_leontief_le (B' a) qh.1 j hp
      have h3 : q.1 j / (B' a).1 j < qh.1 j / (B' a).1 j := by rw [he]; linarith
      exact (div_lt_div_iff_of_pos_right hp).mp h3
    obtain ⟨k, hk, hke⟩ := nc_exists_crit (B a) qh.1
    have hkT : k ∈ T := hsub ((nc_mem_crit _ _ k).mpr ⟨hk, hke⟩)
    have : leontief (B a) q.1 < leontief (B a) qh.1 := by
      rw [← hke]
      calc leontief (B a) q.1 ≤ q.1 k / (B a).1 k := nc_leontief_le _ _ k hk
        _ < qh.1 k / (B a).1 k := div_lt_div_of_pos_right (hTlt k hkT) hk
    linarith
  -- all utilities at B coincide
  have hall : ∀ r, leontief (B r) q.1 = leontief (B r) qh.1 := by
    intro r
    by_cases hra : r = a
    · rw [hra, hua]
    have hBr : B' r = B r := hBB r hra
    rcases lt_trichotomy (leontief (B r) q.1) (leontief (B r) qh.1) with h | h | h
    · exfalso
      rcases hf_gsp {a, r} B B' (fun x hx => hBB x (by
          intro hxa; apply hx; rw [hxa]; simp)) with h' | h'
      · obtain ⟨i, hi, hlt⟩ := h'
        rcases Finset.mem_insert.mp hi with hi | hi
        · rw [hi, hua] at hlt; exact lt_irrefl _ hlt
        · rw [Finset.mem_singleton.mp hi] at hlt; linarith
      · have := h' r (by simp); linarith
    · exact h
    · exfalso
      rcases hf_gsp {a, r} B' B (fun x hx => (hBB x (by
          intro hxa; apply hx; rw [hxa]; simp)).symm) with h' | h'
      · obtain ⟨i, hi, hlt⟩ := h'
        rcases Finset.mem_insert.mp hi with hi | hi
        · rw [hi, hua'] at hlt; exact lt_irrefl _ hlt
        · rw [Finset.mem_singleton.mp hi, hBr] at hlt; linarith
      · have := h' r (by simp); rw [hBr] at this; linarith
  -- qh is efficient at B
  have heff : IsEfficient B qh := by
    rintro ⟨q', hweak, i', hstrict⟩
    apply hf_eff B
    refine ⟨q', fun i => ?_, i', ?_⟩
    · rw [hall i]; exact hweak i
    · rw [hall i']; exact hstrict
  exact (lemma_7 B q qh (hf_eff B) heff hall).symm

/-- One agent moves to her star peak without changing the outcome. -/
theorem nc_single {n m : ℕ} [NeZero n] [NeZero m] (f : Mechanism n m) (hf_cont : Continuous f)
    (hf_gsp : IsGroupSP f) (hf_eff : ∀ P, IsEfficient P (f P)) (Q : Profile n m) (a : Fin n) :
    f (Function.update Q a ⟨starPeak (Q a) (f Q).1, nc_star_mem (Q a) (f Q).1⟩) = f Q := by
  classical
  set q := f Q with hq
  set p := Q a with hp
  -- the path of profiles
  let π : Set.Icc (0 : ℝ) 1 → stdSimplex ℝ (Fin m) := fun t =>
    ⟨nc_path p q.1 t.1, nc_path_mem p q.1 t.1 t.2.1 t.2.2⟩
  have hπc : Continuous π := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro j
    unfold nc_path
    exact ((continuous_subtype_val.mul continuous_const).add
      ((continuous_const.sub continuous_subtype_val).mul continuous_const))
  let φ : Set.Icc (0 : ℝ) 1 → Profile n m := fun t => Function.update Q a (π t)
  have hφc : Continuous φ := continuous_const.update a hπc
  obtain ⟨U, hUo, hqU, hUsub⟩ := nc_path_nbhd p q
  set A := {t : Set.Icc (0 : ℝ) 1 | f (φ t) = q} with hA
  have h0 : (⟨0, le_refl 0, zero_le_one⟩ : Set.Icc (0 : ℝ) 1) ∈ A := by
    show f (φ _) = q
    have : π ⟨0, le_refl 0, zero_le_one⟩ = p := by
      apply Subtype.ext; funext j; simp [π, nc_path]
    simp only [φ, this, hp, Function.update_eq_self, hq]
  -- base step: from any point of A, every point mapping into U lies in A
  have hstep : ∀ t s : Set.Icc (0 : ℝ) 1, t ∈ A → (f (φ s)).1 ∈ U → s ∈ A := by
    intro t s ht hs
    have hft : f (φ t) = q := ht
    show f (φ s) = q
    rw [← hft]
    apply nc_step f hf_gsp hf_eff (φ t) (φ s) a
    · intro r hr; simp [φ, Function.update_of_ne hr]
    · simp only [φ, Function.update_self, hft]
      rw [nc_path_crit p q s.1 s.2.1 s.2.2, nc_path_crit p q t.1 t.2.1 t.2.2]
    · simp only [φ, Function.update_self, hft]
      rw [nc_path_crit p q t.1 t.2.1 t.2.2]
      exact hUsub t.1 t.2.1 t.2.2 (f (φ s)) hs t.2.1
  have hAeq : A = (fun t => (f (φ t)).1) ⁻¹' U := by
    ext s
    constructor
    · intro hs; show (f (φ s)).1 ∈ U; rw [show f (φ s) = q from hs]; exact hqU
    · intro hs; exact hstep _ s h0 hs
  have hgc : Continuous (fun t => (f (φ t)).1) := continuous_subtype_val.comp (hf_cont.comp hφc)
  have hclopen : IsClopen A := by
    constructor
    · have : A = (fun t => f (φ t)) ⁻¹' {q} := rfl
      rw [this]; exact isClosed_singleton.preimage (hf_cont.comp hφc)
    · rw [hAeq]; exact hUo.preimage hgc
  haveI : ConnectedSpace (Set.Icc (0 : ℝ) 1) :=
    isConnected_iff_connectedSpace.mp (isConnected_Icc zero_le_one)
  have hAuniv := hclopen.eq_univ ⟨_, h0⟩
  have h1 : (⟨1, zero_le_one, le_refl 1⟩ : Set.Icc (0 : ℝ) 1) ∈ A := by rw [hAuniv]; trivial
  have h1' : f (φ ⟨1, zero_le_one, le_refl 1⟩) = q := h1
  have : π ⟨1, zero_le_one, le_refl 1⟩ = ⟨starPeak p q.1, nc_star_mem p q.1⟩ := by
    apply Subtype.ext; funext j; simp [π, nc_path]
  simp only [φ, this] at h1'
  exact h1'

theorem solution {n m : ℕ} [NeZero n] [NeZero m]
    (f : Mechanism n m) (hf_cont : Continuous f) (hf_gsp : IsGroupSP f)
    (hf_eff : ∀ P, IsEfficient P (f P)) (P : Profile n m) :
    ∃ Ps : Profile n m,
      (∀ i, (Ps i).1 = starPeak (P i) (f P).1) ∧
      f Ps = f P ∧
      (∀ i, crit (Ps i) (f P).1 = crit (P i) (f P).1) := by
  classical
  set q := f P with hq
  let star : Fin n → stdSimplex ℝ (Fin m) := fun i => ⟨starPeak (P i) q.1, nc_star_mem (P i) q.1⟩
  let PA : Finset (Fin n) → Profile n m := fun A i => if i ∈ A then star i else P i
  have hPA : ∀ A : Finset (Fin n), f (PA A) = q := by
    intro A
    induction A using Finset.induction_on with
    | empty => simp [PA, hq]
    | insert a A ha ih =>
      have hupd : PA (insert a A) = Function.update (PA A) a
          ⟨starPeak (PA A a) (f (PA A)).1, nc_star_mem (PA A a) (f (PA A)).1⟩ := by
        funext i
        by_cases hia : i = a
        · subst hia
          have hPa : PA A i = P i := by simp [PA, ha]
          have hL : PA (insert i A) i = star i := by simp [PA]
          rw [hL, Function.update_self]
          apply Subtype.ext
          show starPeak (P i) q.1 = starPeak (PA A i) (f (PA A)).1
          rw [hPa, ih]
        · rw [Function.update_of_ne hia]
          simp [PA, Finset.mem_insert, hia]
      rw [hupd, nc_single f hf_cont hf_gsp hf_eff (PA A) a, ih]
  refine ⟨PA Finset.univ, fun i => by simp [PA, star], hPA _, fun i => ?_⟩
  have : PA Finset.univ i = ⟨nc_path (P i) q.1 1, nc_path_mem (P i) q.1 1 zero_le_one le_rfl⟩ := by
    apply Subtype.ext; funext j; simp [PA, star, nc_path]
  rw [this, nc_path_crit (P i) q 1 zero_le_one le_rfl]
