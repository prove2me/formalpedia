-- Prove2me | solution 1 for CorrClusterExp.IBR.proposition_3_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T20:54:09.395093+00:00
-- url     : https://prove2.me/submissions/d94e59ba-8531-49a2-a8d0-f73ba76f2b07

import Mathlib
import Definitions.Def_CorrClusterExp_IBR_Setting

open CorrClusterExp.IBR Matrix Finset

/-! ## Part 1: exchangeable laws and their moments -/

/-- number of treated clusters -/
def p31_cnt {n : ℕ} (z : Fin n → Bool) : ℕ := (univ.filter fun i => z i = true).card

/-- precomposition by a permutation, as an equivalence of assignments -/
def p31_permEquiv {n : ℕ} (σ : Equiv.Perm (Fin n)) : (Fin n → Bool) ≃ (Fin n → Bool) where
  toFun z := z ∘ σ
  invFun z := z ∘ σ.symm
  left_inv z := by funext i; simp
  right_inv z := by funext i; simp

lemma p31_cnt_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (z : Fin n → Bool) :
    p31_cnt (z ∘ σ) = p31_cnt z := by
  unfold p31_cnt
  apply Finset.card_nbij' (fun i => σ i) (fun i => σ.symm i)
  · intro i hi; simpa using hi
  · intro i hi; simpa using hi
  · intro i _; simp
  · intro i _; simp

lemma p31_cnt_real {n : ℕ} (z : Fin n → Bool) :
    (p31_cnt z : ℝ) = ∑ i, (if z i = true then (1 : ℝ) else 0) := by
  unfold p31_cnt
  rw [Finset.sum_boole]

lemma p31_cnt_sq {n : ℕ} (z : Fin n → Bool) :
    (p31_cnt z : ℝ) ^ 2 = ∑ i, ∑ k, (if z i = true ∧ z k = true then (1 : ℝ) else 0) := by
  rw [sq, p31_cnt_real, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro k _
  by_cases hi : z i = true <;> by_cases hk : z k = true <;> simp [hi, hk]

/-- first moment of a law -/
noncomputable def p31_m1 {n : ℕ} (L : (Fin n → Bool) → ℝ) (i : Fin n) : ℝ :=
  ∑ z, if z i = true then L z else 0

/-- second moment of a law -/
noncomputable def p31_m2 {n : ℕ} (L : (Fin n → Bool) → ℝ) (i k : Fin n) : ℝ :=
  ∑ z, if z i = true ∧ z k = true then L z else 0

lemma p31_m2_diag {n : ℕ} (L : (Fin n → Bool) → ℝ) (i : Fin n) :
    p31_m2 L i i = p31_m1 L i := by
  unfold p31_m2 p31_m1; simp

lemma p31_m2_symm {n : ℕ} (L : (Fin n → Bool) → ℝ) (i k : Fin n) :
    p31_m2 L i k = p31_m2 L k i := by
  unfold p31_m2; apply Finset.sum_congr rfl; intro z _; simp [and_comm]

lemma p31_sum_m1 {n : ℕ} (L : (Fin n → Bool) → ℝ) :
    ∑ i, p31_m1 L i = ∑ z, L z * p31_cnt z := by
  unfold p31_m1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro z _
  rw [p31_cnt_real, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  split_ifs <;> simp

lemma p31_sum_m2 {n : ℕ} (L : (Fin n → Bool) → ℝ) :
    ∑ i, ∑ k, p31_m2 L i k = ∑ z, L z * (p31_cnt z : ℝ) ^ 2 := by
  unfold p31_m2
  have : ∀ i k : Fin n, (∑ z, if z i = true ∧ z k = true then L z else 0) =
      ∑ z, L z * (if z i = true ∧ z k = true then (1 : ℝ) else 0) := by
    intro i k; apply Finset.sum_congr rfl; intro z _; split_ifs <;> simp
  simp_rw [this, p31_cnt_sq, Finset.mul_sum]
  rw [eq_comm, Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_comm]

/-- An exchangeable law: invariant under permutation of the clusters. -/
def p31_Exch {n : ℕ} (L : (Fin n → Bool) → ℝ) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (z : Fin n → Bool), L (z ∘ σ) = L z

lemma p31_m1_perm {n : ℕ} (L : (Fin n → Bool) → ℝ) (hL : p31_Exch L)
    (σ : Equiv.Perm (Fin n)) (i : Fin n) : p31_m1 L (σ i) = p31_m1 L i := by
  unfold p31_m1
  rw [← (p31_permEquiv σ.symm).sum_comp]
  apply Finset.sum_congr rfl; intro z _
  simp only [p31_permEquiv, Equiv.coe_fn_mk, Function.comp_apply, Equiv.symm_apply_apply]
  rw [hL]

lemma p31_m2_perm {n : ℕ} (L : (Fin n → Bool) → ℝ) (hL : p31_Exch L)
    (σ : Equiv.Perm (Fin n)) (i k : Fin n) : p31_m2 L (σ i) (σ k) = p31_m2 L i k := by
  unfold p31_m2
  rw [← (p31_permEquiv σ.symm).sum_comp]
  apply Finset.sum_congr rfl; intro z _
  simp only [p31_permEquiv, Equiv.coe_fn_mk, Function.comp_apply, Equiv.symm_apply_apply]
  rw [hL]

lemma p31_m1_const {n : ℕ} (L : (Fin n → Bool) → ℝ) (hL : p31_Exch L) (i j : Fin n) :
    p31_m1 L i = p31_m1 L j := by
  have := p31_m1_perm L hL (Equiv.swap j i) j
  rw [Equiv.swap_apply_left] at this
  exact this

lemma p31_m2_B {n : ℕ} (L : (Fin n → Bool) → ℝ) (hL : p31_Exch L) (i k i' : Fin n)
    (hik : i ≠ k) (hi'k : i' ≠ k) : p31_m2 L i k = p31_m2 L i' k := by
  have := p31_m2_perm L hL (Equiv.swap i' i) i' k
  rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hi'k.symm hik.symm] at this
  exact this

lemma p31_m2_const {n : ℕ} (L : (Fin n → Bool) → ℝ) (hL : p31_Exch L) (i k i' k' : Fin n)
    (hik : i ≠ k) (hik' : i' ≠ k') : p31_m2 L i k = p31_m2 L i' k' := by
  by_cases h : i' = k
  · subst h
    rw [p31_m2_symm L i i', p31_m2_symm L i' k']
    -- m2 i' i = m2 k' i'  : move first coord i' ... use symmetric form
    rw [p31_m2_symm L i' i, p31_m2_B L hL i i' k' (fun h => hik h) (fun h => hik' h.symm)]
  · rw [p31_m2_B L hL i k i' hik h, p31_m2_symm L i' k,
      p31_m2_B L hL k i' k' (fun h' => h h'.symm) (fun h' => hik' h'.symm), p31_m2_symm]

/-- For an exchangeable law on `n ≥ 2` clusters, each first moment is `E[cnt]/n`. -/
lemma p31_m1_val {n : ℕ} (hn : 1 ≤ n) (L : (Fin n → Bool) → ℝ) (hL : p31_Exch L)
    (i : Fin n) : p31_m1 L i = (∑ z, L z * p31_cnt z) / n := by
  rw [← p31_sum_m1]
  have : ∑ j, p31_m1 L j = ∑ _j : Fin n, p31_m1 L i :=
    Finset.sum_congr rfl (fun j _ => p31_m1_const L hL j i)
  rw [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : (n : ℝ) ≠ 0 := by have : (1 : ℝ) ≤ n := by exact_mod_cast hn
                           linarith
  field_simp

lemma p31_offdiag_sum {n : ℕ} (M : Fin n → Fin n → ℝ) :
    ∑ i, ∑ k, M i k = ∑ i, M i i + ∑ i, ∑ k ∈ univ.erase i, M i k := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]

/-- For an exchangeable law, each off-diagonal second moment is
`(E[cnt²] − E[cnt]) / (n(n−1))`. -/
lemma p31_m2_val {n : ℕ} (hn : 2 ≤ n) (L : (Fin n → Bool) → ℝ) (hL : p31_Exch L)
    (i k : Fin n) (hik : i ≠ k) :
    p31_m2 L i k = (∑ z, L z * (p31_cnt z : ℝ) ^ 2 - ∑ z, L z * p31_cnt z) /
      ((n : ℝ) * ((n : ℝ) - 1)) := by
  rw [← p31_sum_m2, ← p31_sum_m1, p31_offdiag_sum]
  simp_rw [p31_m2_diag]
  have : ∀ j, ∑ l ∈ univ.erase j, p31_m2 L j l = ∑ _l ∈ univ.erase j, p31_m2 L i k := by
    intro j; apply Finset.sum_congr rfl; intro l hl
    exact p31_m2_const L hL j l i k (Finset.ne_of_mem_erase hl).symm hik
  simp_rw [this, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : (n : ℝ) * ((n : ℝ) - 1) ≠ 0 := by
    apply mul_ne_zero <;> linarith
  rw [Nat.cast_sub (by omega), eq_div_iff h1]
  push_cast
  ring

/-! ## Part 2: the uniform law on `h`-subsets -/

noncomputable def p31_U {n : ℕ} (h : ℕ) (z : Fin n → Bool) : ℝ :=
  if p31_cnt z = h then 1 / (n.choose h : ℝ) else 0

lemma p31_card_cnt {n : ℕ} (h : ℕ) :
    (univ.filter fun z : Fin n → Bool => p31_cnt z = h).card = n.choose h := by
  rw [show n.choose h = (powersetCard h (univ : Finset (Fin n))).card by simp]
  refine Finset.card_nbij'
    (fun z : Fin n → Bool => (univ.filter fun i => z i = true : Finset (Fin n)))
    (fun (s : Finset (Fin n)) (i : Fin n) => decide (i ∈ s)) ?_ ?_ ?_ ?_
  · intro z hz
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    simp only [Finset.mem_coe, Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, hz⟩
  · intro s hs
    simp only [Finset.mem_coe, Finset.mem_powersetCard] at hs
    show (fun (i : Fin n) => decide (i ∈ s)) ∈ (univ.filter fun z : Fin n → Bool => p31_cnt z = h)
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    unfold p31_cnt
    rw [← hs.2]; congr 1; ext i; simp
  · intro z _; funext i; simp
  · intro s _; ext i; simp

lemma p31_U_exch {n : ℕ} (h : ℕ) : p31_Exch (p31_U (n := n) h) := by
  intro σ z; unfold p31_U; rw [p31_cnt_perm]

lemma p31_U_nonneg {n : ℕ} (h : ℕ) (z : Fin n → Bool) : 0 ≤ p31_U h z := by
  unfold p31_U; split_ifs
  · positivity
  · exact le_refl _

lemma p31_U_sum_mul {n : ℕ} (h : ℕ) (hh : h ≤ n) (f : ℕ → ℝ) :
    ∑ z : Fin n → Bool, p31_U h z * f (p31_cnt z) = f h := by
  unfold p31_U
  have : ∀ z : Fin n → Bool, (if p31_cnt z = h then 1 / (n.choose h : ℝ) else 0) * f (p31_cnt z)
      = if p31_cnt z = h then f h / (n.choose h : ℝ) else 0 := by
    intro z; split_ifs with hz
    · rw [hz]; ring
    · ring
  simp_rw [this]
  rw [← Finset.sum_filter, Finset.sum_const, p31_card_cnt, nsmul_eq_mul]
  have : (0 : ℝ) < n.choose h := by exact_mod_cast Nat.choose_pos hh
  field_simp

lemma p31_U_sum {n : ℕ} (h : ℕ) (hh : h ≤ n) : ∑ z : Fin n → Bool, p31_U h z = 1 := by
  have := p31_U_sum_mul h hh (fun _ => 1)
  simpa using this

lemma p31_U_m1 {n : ℕ} (hn : 1 ≤ n) (h : ℕ) (hh : h ≤ n) (i : Fin n) :
    p31_m1 (p31_U h) i = h / n := by
  rw [p31_m1_val hn _ (p31_U_exch h), p31_U_sum_mul h hh (fun m => (m : ℝ))]

lemma p31_U_m2 {n : ℕ} (hn : 2 ≤ n) (h : ℕ) (hh : h ≤ n) (i k : Fin n) (hik : i ≠ k) :
    p31_m2 (p31_U h) i k = ((h : ℝ) ^ 2 - h) / ((n : ℝ) * ((n : ℝ) - 1)) := by
  rw [p31_m2_val hn _ (p31_U_exch h) i k hik, p31_U_sum_mul h hh (fun m => (m : ℝ) ^ 2),
    p31_U_sum_mul h hh (fun m => (m : ℝ))]

/-! ## Part 3: the law of Proposition 3.1 -/

lemma p31_U_lin {n : ℕ} (a b : ℕ) (ha : a ≤ n) (hb : b ≤ n) (p : ℝ) (g : ℕ → ℝ) :
    ∑ z : Fin n → Bool, (p * p31_U a z + (1 - p) * p31_U b z) * g (p31_cnt z) =
      p * g a + (1 - p) * g b := by
  have : ∀ z : Fin n → Bool, (p * p31_U a z + (1 - p) * p31_U b z) * g (p31_cnt z) =
      p * (p31_U a z * g (p31_cnt z)) + (1 - p) * (p31_U b z * g (p31_cnt z)) := by
    intro z; ring
  simp_rw [this]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, p31_U_sum_mul a ha,
    p31_U_sum_mul b hb]

lemma p31_frac_eq (q : ℝ) (n : ℕ) (z : Fin n → Bool) :
    fracLaw q n z = ((⌈q * n⌉₊ : ℝ) - q * n) * p31_U ⌊q * n⌋₊ z +
      (1 - ((⌈q * n⌉₊ : ℝ) - q * n)) * p31_U ⌈q * n⌉₊ z := by
  unfold fracLaw p31_U p31_cnt
  simp only
  split_ifs <;> ring

/-- the two cases for `x = qn ≥ 0`: integral, or `⌈x⌉ = ⌊x⌋ + 1`. -/
lemma p31_ceil_cases (x : ℝ) (hx : 0 ≤ x) :
    (x = ⌊x⌋₊ ∧ ⌈x⌉₊ = ⌊x⌋₊) ∨ ((⌊x⌋₊ : ℝ) < x ∧ ⌈x⌉₊ = ⌊x⌋₊ + 1) := by
  rcases eq_or_lt_of_le (Nat.floor_le hx) with h | h
  · left; refine ⟨h.symm, ?_⟩
    rw [← h, Nat.ceil_natCast, Nat.floor_natCast]
  · right; refine ⟨h, ?_⟩
    rw [Nat.ceil_eq_iff (by omega)]
    push_cast
    exact ⟨by simpa using h, (Nat.lt_floor_add_one x).le⟩

structure p31_Data (q : ℝ) (n : ℕ) : Prop where
  hq0 : 0 < q
  hq1 : q < 1
  hn : 2 ≤ n

lemma p31_frac_exch (q : ℝ) (n : ℕ) : p31_Exch (fracLaw q n) := by
  intro σ z
  rw [p31_frac_eq, p31_frac_eq, p31_U_exch, p31_U_exch]

/-- `E[g(cnt)]` under the law of Proposition 3.1 -/
lemma p31_frac_mom (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1) (n : ℕ) (g : ℕ → ℝ) :
    ∑ z, fracLaw q n z * g (p31_cnt z) =
      ((⌈q * n⌉₊ : ℝ) - q * n) * g ⌊q * n⌋₊ + (1 - ((⌈q * n⌉₊ : ℝ) - q * n)) * g ⌈q * n⌉₊ := by
  have hx : q * n ≤ n := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have hb : ⌈q * n⌉₊ ≤ n := Nat.ceil_le.2 hx
  have ha : ⌊q * n⌋₊ ≤ n := le_trans (Nat.floor_le_ceil _) hb
  simp_rw [p31_frac_eq]
  exact p31_U_lin _ _ ha hb _ g

/-- the "fractional part" `r = qn − ⌊qn⌋` and the moments -/
lemma p31_frac_moments (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1) (n : ℕ) :
    ∑ z, fracLaw q n z * 1 = 1 ∧
    ∑ z, fracLaw q n z * (p31_cnt z : ℝ) = q * n ∧
    ∑ z, fracLaw q n z * (p31_cnt z : ℝ) ^ 2 =
      (q * n) ^ 2 + (q * n - ⌊q * n⌋₊) * (1 - (q * n - ⌊q * n⌋₊)) := by
  have hx : 0 ≤ q * n := by positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [p31_frac_mom q hq0 hq1 n (fun _ => 1)]; ring
  · rw [p31_frac_mom q hq0 hq1 n (fun m => (m : ℝ))]
    rcases p31_ceil_cases (q * n) hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h2]; linarith
    · rw [h2]; push_cast; ring
  · rw [p31_frac_mom q hq0 hq1 n (fun m => (m : ℝ) ^ 2)]
    rcases p31_ceil_cases (q * n) hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only [h2]; rw [← h1]; ring
    · simp only [h2]; push_cast; ring

lemma p31_frac_nonneg (q : ℝ) (hq0 : 0 < q) (n : ℕ) (z : Fin n → Bool) : 0 ≤ fracLaw q n z := by
  have hx : 0 ≤ q * n := by positivity
  rw [p31_frac_eq]
  have h1 : 0 ≤ (⌈q * n⌉₊ : ℝ) - q * n := by linarith [Nat.le_ceil (q * n)]
  have h2 : 0 ≤ 1 - ((⌈q * n⌉₊ : ℝ) - q * n) := by
    have := Nat.ceil_lt_add_one hx; linarith
  have := p31_U_nonneg ⌊q * n⌋₊ z
  have := p31_U_nonneg ⌈q * n⌉₊ z
  positivity

lemma p31_frac_exp (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1) (n : ℕ) (hn : 1 ≤ n) :
    IsExperiment q (fracLaw q n) := by
  obtain ⟨h1, h2, -⟩ := p31_frac_moments q hq0 hq1 n
  refine ⟨p31_frac_nonneg q hq0 n, by simpa using h1, ?_⟩
  intro i
  have := p31_m1_val hn _ (p31_frac_exch q n) i
  unfold p31_m1 at this
  rw [this, h2]
  have : (n : ℝ) ≠ 0 := by have : (1 : ℝ) ≤ n := by exact_mod_cast hn
                           linarith
  field_simp

/-- the common off-diagonal correlation `σ_f = (r(1−r)/(q(1−q)) − n)/(n(n−1))` -/
noncomputable def p31_sig (q : ℝ) (n : ℕ) : ℝ :=
  ((q * n - ⌊q * n⌋₊) * (1 - (q * n - ⌊q * n⌋₊)) / (q * (1 - q)) - n) / ((n : ℝ) * ((n : ℝ) - 1))

lemma p31_corr_eq_m2 {n : ℕ} (q : ℝ) (P : (Fin n → Bool) → ℝ) (i k : Fin n) :
    corr q P i k = (p31_m2 P i k - q ^ 2) / (q * (1 - q)) := rfl

lemma p31_corr_diag {n : ℕ} (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (P : (Fin n → Bool) → ℝ)
    (hP : IsExperiment q P) (i : Fin n) : corr q P i i = 1 := by
  rw [p31_corr_eq_m2, p31_m2_diag]
  unfold p31_m1
  rw [hP.2.2 i]
  have : q * (1 - q) ≠ 0 := by apply mul_ne_zero hq0.ne'; linarith
  have h5 : (1 - q) ≠ 0 := by intro h; apply this; rw [h, mul_zero]
  field_simp

lemma p31_frac_corr_off (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) (hn : 2 ≤ n)
    (i k : Fin n) (hik : i ≠ k) : corr q (fracLaw q n) i k = p31_sig q n := by
  obtain ⟨-, h2, h3⟩ := p31_frac_moments q hq0 hq1.le n
  rw [p31_corr_eq_m2, p31_m2_val hn _ (p31_frac_exch q n) i k hik, h2, h3]
  unfold p31_sig
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : (n : ℝ) * ((n : ℝ) - 1) ≠ 0 := by apply mul_ne_zero <;> linarith
  have h4 : q * (1 - q) ≠ 0 := by apply mul_ne_zero hq0.ne'; linarith
  have h5 : (1 - q) ≠ 0 := by intro h; apply h4; rw [h, mul_zero]
  have h6 : (n : ℝ) - 1 ≠ 0 := by linarith
  have h7 : (n : ℝ) ≠ 0 := by linarith
  field_simp
  ring

/-! ## Part 4: lower bound for an arbitrary experiment -/

lemma p31_bdd {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ) :
    BddAbove ((fun y => y ⬝ᵥ (S *ᵥ y)) '' box w) := by
  have hbox : box w = Set.pi Set.univ (fun i => Set.Icc 0 (w i)) := by
    ext y; simp only [Set.mem_pi, Set.mem_univ, forall_const, Set.mem_Icc]; exact Iff.rfl
  have hc : IsCompact (box w) := by
    rw [hbox]; exact isCompact_univ_pi (fun i => isCompact_Icc)
  apply hc.bddAbove_image
  apply Continuous.continuousOn
  exact Continuous.dotProduct continuous_id (Continuous.matrix_mulVec continuous_const continuous_id)

lemma p31_zero_mem {n : ℕ} (w : Fin n → ℝ) (hw0 : ∀ i, 0 ≤ w i) : (0 : Fin n → ℝ) ∈ box w :=
  fun i => ⟨le_refl _, hw0 i⟩

lemma p31_wc_nonneg {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ)
    (hw0 : ∀ i, 0 ≤ w i) : 0 ≤ worstCase S w := by
  unfold worstCase
  apply le_csSup (p31_bdd S w)
  exact ⟨0, p31_zero_mem w hw0, by simp⟩

lemma p31_le_wc {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (w y : Fin n → ℝ) (hy : y ∈ box w) :
    y ⬝ᵥ (S *ᵥ y) ≤ worstCase S w :=
  le_csSup (p31_bdd S w) ⟨y, hy, rfl⟩

def p31_ind {n : ℕ} (z : Fin n → Bool) : Fin n → ℝ := fun i => if z i = true then 1 else 0

lemma p31_ind_mem {n : ℕ} (z : Fin n → Bool) : p31_ind z ∈ box (fun _ : Fin n => (1 : ℝ)) := by
  intro i; unfold p31_ind; split_ifs <;> norm_num

lemma p31_val_ind {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (z : Fin n → Bool) :
    p31_ind z ⬝ᵥ (S *ᵥ p31_ind z) =
      ∑ i, ∑ k, S i k * (if z i = true ∧ z k = true then (1 : ℝ) else 0) := by
  simp only [dotProduct, mulVec, p31_ind, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro k _
  by_cases hi : z i = true <;> by_cases hk : z k = true <;> simp [hi, hk]

lemma p31_avg {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (L : (Fin n → Bool) → ℝ) :
    ∑ z, L z * (p31_ind z ⬝ᵥ (S *ᵥ p31_ind z)) = ∑ i, ∑ k, S i k * p31_m2 L i k := by
  simp_rw [p31_val_ind, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro k _
  unfold p31_m2
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro z _
  split_ifs <;> ring

lemma p31_wc_ge_avg {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (h : ℕ) (hh : h ≤ n) :
    ∑ i, ∑ k, S i k * p31_m2 (p31_U h) i k ≤ worstCase S (fun _ => 1) := by
  rw [← p31_avg]
  calc ∑ z, p31_U h z * (p31_ind z ⬝ᵥ (S *ᵥ p31_ind z))
      ≤ ∑ z, p31_U h z * worstCase S (fun _ => 1) := by
        apply Finset.sum_le_sum; intro z _
        exact mul_le_mul_of_nonneg_left (p31_le_wc S _ _ (p31_ind_mem z)) (p31_U_nonneg h z)
    _ = worstCase S (fun _ => 1) := by rw [← Finset.sum_mul, p31_U_sum h hh, one_mul]

/-- `Σ_{i,k} Σ(P)_{ik} ≥ r(1−r)/(q(1−q))` for every experiment (integrality of the count). -/
lemma p31_T_lower {n : ℕ} (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (P : (Fin n → Bool) → ℝ)
    (hP : IsExperiment q P) :
    (q * n - ⌊q * n⌋₊) * (1 - (q * n - ⌊q * n⌋₊)) / (q * (1 - q)) ≤
      ∑ i, ∑ k, corr q P i k := by
  set a : ℝ := (⌊q * n⌋₊ : ℝ)
  have hE1 : ∑ z, P z * (p31_cnt z : ℝ) = q * n := by
    rw [← p31_sum_m1]
    unfold p31_m1
    simp_rw [hP.2.2]
    simp [mul_comm]
  have hE2 : ∑ i, ∑ k, p31_m2 P i k = ∑ z, P z * (p31_cnt z : ℝ) ^ 2 := p31_sum_m2 P
  have hint : ∀ c : ℕ, 0 ≤ ((c : ℝ) - a) * ((c : ℝ) - a - 1) := by
    intro c
    rcases le_or_gt c ⌊q * n⌋₊ with hc | hc
    · have : (c : ℝ) ≤ a := by simp only [a]; exact_mod_cast hc
      nlinarith
    · have : (⌊q * n⌋₊ : ℝ) + 1 ≤ c := by exact_mod_cast hc
      nlinarith
  have hsum : 0 ≤ ∑ z, P z * (((p31_cnt z : ℝ) - a) * ((p31_cnt z : ℝ) - a - 1)) :=
    Finset.sum_nonneg (fun z _ => mul_nonneg (hP.1 z) (hint _))
  have hexp : ∑ z, P z * (((p31_cnt z : ℝ) - a) * ((p31_cnt z : ℝ) - a - 1)) =
      ∑ z, P z * (p31_cnt z : ℝ) ^ 2 - (2 * a + 1) * ∑ z, P z * (p31_cnt z : ℝ) +
        a * (a + 1) * ∑ z, P z := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro z _; ring
  rw [hexp, hE1, hP.2.1] at hsum
  have hT : ∑ i, ∑ k, corr q P i k = (∑ i, ∑ k, p31_m2 P i k - (n : ℝ) ^ 2 * q ^ 2) /
      (q * (1 - q)) := by
    have hne : q * (1 - q) ≠ 0 := (mul_pos hq0 (by linarith)).ne'
    simp_rw [p31_corr_eq_m2]
    rw [eq_div_iff hne, Finset.sum_mul]
    simp_rw [Finset.sum_mul, div_mul_cancel₀ _ hne, Finset.sum_sub_distrib]
    simp
    ring
  rw [hT, hE2]
  have hpos : 0 < q * (1 - q) := mul_pos hq0 (by linarith)
  apply div_le_div_of_nonneg_right _ hpos.le
  nlinarith

/-- every experiment has worst case at least `h + h(h−1)σ_f` on unit clusters. -/
lemma p31_lower {n : ℕ} (hn : 2 ≤ n) (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (P : (Fin n → Bool) → ℝ) (hP : IsExperiment q P) (h : ℕ) (hh : h ≤ n) :
    (h : ℝ) + h * ((h : ℝ) - 1) * p31_sig q n ≤ worstCase (corr q P) (fun _ => 1) := by
  refine le_trans ?_ (p31_wc_ge_avg (corr q P) h hh)
  rw [p31_offdiag_sum]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hd : ∑ i, corr q P i i * p31_m2 (p31_U h) i i = h := by
    simp_rw [p31_corr_diag q hq0 hq1 P hP, p31_m2_diag, p31_U_m1 (by omega) h hh, one_mul]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  set β : ℝ := ((h : ℝ) ^ 2 - h) / ((n : ℝ) * ((n : ℝ) - 1)) with hβ
  have ho : ∑ i, ∑ k ∈ univ.erase i, corr q P i k * p31_m2 (p31_U h) i k =
      β * ∑ i, ∑ k ∈ univ.erase i, corr q P i k := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k hk
    rw [p31_U_m2 hn h hh i k (Finset.ne_of_mem_erase hk).symm]; ring
  rw [hd, ho]
  have hT := p31_T_lower q hq0 hq1 P hP
  rw [p31_offdiag_sum (corr q P)] at hT
  simp_rw [p31_corr_diag q hq0 hq1 P hP] at hT
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hT
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hβ0 : 0 ≤ β := by
    rw [hβ]; apply div_nonneg
    · have : (0 : ℝ) ≤ h := Nat.cast_nonneg h
      rcases Nat.eq_zero_or_pos h with h0 | h0
      · subst h0; simp
      · have : (1 : ℝ) ≤ h := by exact_mod_cast h0
        nlinarith
    · apply mul_nonneg <;> linarith
  have : β * ((q * n - ⌊q * n⌋₊) * (1 - (q * n - ⌊q * n⌋₊)) / (q * (1 - q)) - n) ≤
      β * ∑ i, ∑ k ∈ univ.erase i, corr q P i k := by
    apply mul_le_mul_of_nonneg_left _ hβ0; linarith
  have hsig : (h : ℝ) * ((h : ℝ) - 1) * p31_sig q n =
      β * ((q * n - ⌊q * n⌋₊) * (1 - (q * n - ⌊q * n⌋₊)) / (q * (1 - q)) - n) := by
    rw [hβ]; unfold p31_sig
    have h1 : (n : ℝ) * ((n : ℝ) - 1) ≠ 0 := by apply mul_ne_zero <;> linarith
    field_simp
  linarith

/-! ## Part 5: upper bound for a constant off-diagonal correlation matrix -/

lemma p31_phi_two (u y : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    Int.fract (u + y) * (1 - Int.fract (u + y)) ≤ u * (1 - u) + y * (1 - y) := by
  rcases lt_or_ge (u + y) 1 with h | h
  · rw [Int.fract_eq_self.2 ⟨by linarith, h⟩]; nlinarith
  · have : Int.fract (u + y) = u + y - 1 := by
      rw [← Int.fract_sub_one, Int.fract_eq_self.2 ⟨by linarith, by linarith⟩]
    rw [this]; nlinarith

lemma p31_phi_sum {n : ℕ} (y : Fin n → ℝ) (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1) (s : Finset (Fin n)) :
    Int.fract (∑ i ∈ s, y i) * (1 - Int.fract (∑ i ∈ s, y i)) ≤
      ∑ i ∈ s, y i * (1 - y i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    have e : Int.fract (y j + ∑ i ∈ s, y i) = Int.fract (Int.fract (∑ i ∈ s, y i) + y j) := by
      conv_lhs => rw [← Int.floor_add_fract (∑ i ∈ s, y i)]
      rw [show y j + ((⌊∑ i ∈ s, y i⌋ : ℝ) + Int.fract (∑ i ∈ s, y i)) =
        (Int.fract (∑ i ∈ s, y i) + y j) + (⌊∑ i ∈ s, y i⌋ : ℝ) by ring, Int.fract_add_intCast]
    rw [e]
    have := p31_phi_two (Int.fract (∑ i ∈ s, y i)) (y j) (Int.fract_nonneg _)
      (Int.fract_lt_one _) (hy j).1 (hy j).2
    linarith

lemma p31_val_upper {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (σ : ℝ) (hσ : σ ≤ 1)
    (hdiag : ∀ i, C i i = 1) (hoff : ∀ i k, i ≠ k → C i k = σ) (M : ℝ)
    (hM : ∀ h : ℕ, h ≤ n → (h : ℝ) + h * ((h : ℝ) - 1) * σ ≤ M)
    (y : Fin n → ℝ) (hy : y ∈ box (fun _ : Fin n => (1 : ℝ))) :
    y ⬝ᵥ (C *ᵥ y) ≤ M := by
  set T := ∑ i, y i with hTdef
  have hrow : ∀ i, (C *ᵥ y) i = y i + σ * (T - y i) := by
    intro i
    simp only [mulVec, dotProduct]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hdiag, one_mul]
    rw [Finset.sum_congr rfl (fun k hk => by rw [hoff i k (Finset.ne_of_mem_erase hk).symm]),
      ← Finset.mul_sum, Finset.sum_erase_eq_sub (Finset.mem_univ i)]
  set Q := ∑ i, y i ^ 2 with hQ
  have hval : y ⬝ᵥ (C *ᵥ y) = (1 - σ) * Q + σ * T ^ 2 := by
    simp only [dotProduct, hrow]
    have : ∀ i, y i * (y i + σ * (T - y i)) = (1 - σ) * y i ^ 2 + (σ * T) * y i := by
      intro i; ring
    simp_rw [this]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← hTdef]; ring
  have hy' : ∀ i, 0 ≤ y i ∧ y i ≤ 1 := hy
  have hphi := p31_phi_sum y hy' univ
  rw [← hTdef] at hphi
  have hQT : Q = T - ∑ i, y i * (1 - y i) := by
    rw [hQ, hTdef, ← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro i _; ring
  set f := Int.fract T with hf
  set m := ⌊T⌋ with hm
  have hTm : T = m + f := (Int.floor_add_fract T).symm
  have hT0 : 0 ≤ T := Finset.sum_nonneg (fun i _ => (hy' i).1)
  have hTn : T ≤ n := by
    calc T = ∑ i, y i := rfl
      _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum (fun i _ => (hy' i).2)
      _ = n := by simp
  have hf0 : 0 ≤ f := Int.fract_nonneg T
  have hf1 : f < 1 := Int.fract_lt_one T
  have hm0 : 0 ≤ m := Int.floor_nonneg.2 hT0
  have hQb : Q ≤ m + f ^ 2 := by rw [hQT]; nlinarith
  have hstep1 : y ⬝ᵥ (C *ᵥ y) ≤ (1 - σ) * (m + f ^ 2) + σ * (m + f) ^ 2 := by
    rw [hval, hTm]
    have : (1 - σ) * Q ≤ (1 - σ) * (m + f ^ 2) := mul_le_mul_of_nonneg_left hQb (by linarith)
    linarith
  set G : ℝ → ℝ := fun t => t + t * (t - 1) * σ with hG
  have hstep2 : (1 - σ) * (m + f ^ 2) + σ * (m + f) ^ 2 ≤ (1 - f) * G m + f * G (m + 1) := by
    simp only [hG]; nlinarith
  have hmN : ((m.toNat : ℕ) : ℝ) = (m : ℝ) := by
    have : ((m.toNat : ℤ) : ℝ) = (m : ℝ) := by rw [Int.toNat_of_nonneg hm0]
    exact_mod_cast this
  have hmn : m.toNat ≤ n := by
    have : (m : ℝ) ≤ n := by linarith
    have : m ≤ (n : ℤ) := by exact_mod_cast this
    omega
  have hGm : G m ≤ M := by
    have := hM m.toNat hmn; rw [hmN] at this; exact this
  rcases eq_or_lt_of_le hf0 with h0 | hpos
  · have : (1 - f) * G m + f * G (m + 1) = G m := by rw [← h0]; ring
    linarith
  · have hm1 : m.toNat + 1 ≤ n := by
      have : (m : ℝ) < n := by linarith
      have : m < (n : ℤ) := by exact_mod_cast this
      omega
    have hGm1 : G (m + 1) ≤ M := by
      have := hM (m.toNat + 1) hm1; push_cast at this; rw [hmN] at this; exact this
    have : (1 - f) * G m + f * G (m + 1) ≤ (1 - f) * M + f * M := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left hGm (by linarith)
      · exact mul_le_mul_of_nonneg_left hGm1 hf0
    linarith

/-! ## Part 6: assembling the optimal value -/

lemma p31_val_formula {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (σ : ℝ)
    (hdiag : ∀ i, C i i = 1) (hoff : ∀ i k, i ≠ k → C i k = σ) (y : Fin n → ℝ) :
    y ⬝ᵥ (C *ᵥ y) = (1 - σ) * ∑ i, y i ^ 2 + σ * (∑ i, y i) ^ 2 := by
  set T := ∑ i, y i with hTdef
  have hrow : ∀ i, (C *ᵥ y) i = y i + σ * (T - y i) := by
    intro i
    simp only [mulVec, dotProduct]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hdiag, one_mul]
    rw [Finset.sum_congr rfl (fun k hk => by rw [hoff i k (Finset.ne_of_mem_erase hk).symm]),
      ← Finset.mul_sum, Finset.sum_erase_eq_sub (Finset.mem_univ i)]
  simp only [dotProduct, hrow]
  have : ∀ i, y i * (y i + σ * (T - y i)) = (1 - σ) * y i ^ 2 + (σ * T) * y i := by
    intro i; ring
  simp_rw [this]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← hTdef]; ring

lemma p31_val_indset {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (σ : ℝ)
    (hdiag : ∀ i, C i i = 1) (hoff : ∀ i k, i ≠ k → C i k = σ) (s : Finset (Fin n)) :
    (fun i => if i ∈ s then (1 : ℝ) else 0) ⬝ᵥ (C *ᵥ (fun i => if i ∈ s then (1 : ℝ) else 0)) =
      s.card + s.card * ((s.card : ℝ) - 1) * σ := by
  rw [p31_val_formula C σ hdiag hoff]
  have h1 : ∑ i, (if i ∈ s then (1 : ℝ) else 0) ^ 2 = s.card := by
    have : ∀ i, (if i ∈ s then (1 : ℝ) else 0) ^ 2 = if i ∈ s then 1 else 0 := by
      intro i; split_ifs <;> norm_num
    simp_rw [this]; rw [Finset.sum_boole]; simp
  have h2 : ∑ i, (if i ∈ s then (1 : ℝ) else 0) = s.card := by
    rw [Finset.sum_boole]; simp
  rw [h1, h2]; ring

/-- the quadratic `G(h) = h + h(h−1)σ` -/
noncomputable def p31_G (σ : ℝ) (h : ℝ) : ℝ := h + h * (h - 1) * σ

lemma p31_G_cmp (σ : ℝ) (hσ : σ < 0) (h hs : ℝ)
    (hle : (hs - (-1 / (2 * σ) + 1 / 2)) ^ 2 ≤ (h - (-1 / (2 * σ) + 1 / 2)) ^ 2) :
    p31_G σ h ≤ p31_G σ hs := by
  unfold p31_G
  have key : ∀ t : ℝ, t + t * (t - 1) * σ =
      σ * (t - (-1 / (2 * σ) + 1 / 2)) ^ 2 - σ * (-1 / (2 * σ) + 1 / 2) ^ 2 := by
    intro t; have : σ ≠ 0 := hσ.ne; field_simp; ring
  rw [key h, key hs]
  nlinarith

lemma p31_G_nearest (σ : ℝ) (hσ : σ < 0) (n : ℕ) (hstar : ℕ)
    (hnear : ∀ h : ℤ, |(hstar : ℝ) - min (-1 / (2 * σ) + 1 / 2) (n : ℝ)| ≤
      |(h : ℝ) - min (-1 / (2 * σ) + 1 / 2) (n : ℝ)|) :
    hstar ≤ n ∧ ∀ h : ℕ, h ≤ n → p31_G σ h ≤ p31_G σ hstar := by
  set x0 := -1 / (2 * σ) + 1 / 2 with hx0
  rcases le_or_gt x0 n with hx | hx
  · rw [min_eq_left hx] at hnear
    refine ⟨?_, ?_⟩
    · by_contra hc
      push Not at hc
      have hc' : (n : ℝ) + 1 ≤ hstar := by exact_mod_cast hc
      have := hnear n
      push_cast at this
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at this
      linarith
    · intro h _
      apply p31_G_cmp σ hσ
      have := hnear h
      push_cast at this
      exact sq_le_sq.2 this
  · rw [min_eq_right hx.le] at hnear
    have hs : (hstar : ℝ) = n := by
      have := hnear n
      push_cast at this
      simp only [sub_self, abs_zero] at this
      have := abs_nonneg ((hstar : ℝ) - n)
      have h0 : |(hstar : ℝ) - n| = 0 := by linarith
      rw [abs_eq_zero] at h0; linarith
    have hsn : hstar = n := by exact_mod_cast hs
    refine ⟨hsn.le, ?_⟩
    intro h hh
    apply p31_G_cmp σ hσ
    rw [hs]
    have : (h : ℝ) ≤ n := by exact_mod_cast hh
    nlinarith

lemma p31_sig_neg (q : ℝ) (hq0 : 0 < q) (hq : q ≤ 1 / 2) (n : ℕ) (hn : 2 ≤ n) :
    p31_sig q n < 0 := by
  unfold p31_sig
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hx : 0 ≤ q * n := by positivity
  set a : ℝ := (⌊q * n⌋₊ : ℝ) with ha
  have ha0 : a ≤ q * n := Nat.floor_le hx
  have ha1 : q * n < a + 1 := Nat.lt_floor_add_one _
  have hpos : 0 < q * (1 - q) := mul_pos hq0 (by linarith)
  apply div_neg_of_neg_of_pos _ (by apply mul_pos <;> linarith)
  rw [sub_neg, div_lt_iff₀ hpos]
  -- r(1−r) < n q (1−q)
  rcases lt_or_ge (q * n) 1 with h1 | h1
  · have ha00 : a = 0 := by
      rw [ha]; simp only [Nat.cast_eq_zero, Nat.floor_eq_zero]; exact h1
    rw [ha00]
    have : q < q * n := by nlinarith
    nlinarith
  · have : (q * n - a) * (1 - (q * n - a)) ≤ 1 / 4 := by nlinarith [sq_nonneg (q * n - a - 1 / 2)]
    nlinarith

lemma p31_sig_ge (q : ℝ) (hq0 : 0 < q) (hq : q ≤ 1 / 2) (n : ℕ) (hn : 2 ≤ n) :
    -1 / ((n : ℝ) - 1) ≤ p31_sig q n := by
  unfold p31_sig
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hx : 0 ≤ q * n := by positivity
  have ha0 : (⌊q * n⌋₊ : ℝ) ≤ q * n := Nat.floor_le hx
  have ha1 : q * n < (⌊q * n⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hpos : 0 < q * (1 - q) := mul_pos hq0 (by linarith)
  have hR : 0 ≤ (q * n - ⌊q * n⌋₊) * (1 - (q * n - ⌊q * n⌋₊)) / (q * (1 - q)) := by
    apply div_nonneg _ hpos.le; apply mul_nonneg <;> linarith
  rw [div_le_div_iff₀ (by linarith) (by apply mul_pos <;> linarith)]
  nlinarith

/-- The main optimality statement on `n ≥ 2` unit clusters. -/
lemma p31_main (q : ℝ) (hq0 : 0 < q) (hq : q ≤ 1 / 2) (n : ℕ) (hn : 2 ≤ n) :
    IsExperiment q (fracLaw q n) ∧
    worstCase (corr q (fracLaw q n)) (fun _ : Fin n => (1 : ℝ)) =
      VOPT q (fun _ : Fin n => (1 : ℝ)) ∧
    (∀ i k : Fin n, i ≠ k → corr q (fracLaw q n) i k = p31_sig q n) ∧
    (∀ h : ℕ, h ≤ n → p31_G (p31_sig q n) h ≤ VOPT q (fun _ : Fin n => (1 : ℝ))) ∧
    (∃ h0 : ℕ, h0 ≤ n ∧ VOPT q (fun _ : Fin n => (1 : ℝ)) = p31_G (p31_sig q n) h0) ∧
    ∀ hs : ℕ, hs ≤ n → (∀ h : ℕ, h ≤ n → p31_G (p31_sig q n) h ≤ p31_G (p31_sig q n) hs) →
      VOPT q (fun _ : Fin n => (1 : ℝ)) = p31_G (p31_sig q n) hs ∧
      ∀ s : Finset (Fin n), s.card = hs →
        IsMaxOn (fun y => y ⬝ᵥ (corr q (fracLaw q n) *ᵥ y)) (box fun _ : Fin n => (1 : ℝ))
          (fun i => if i ∈ s then (1 : ℝ) else 0) := by
  have hq1 : q < 1 := by linarith
  have hexp := p31_frac_exp q hq0 hq1.le n (by omega)
  set σ := p31_sig q n with hσ
  have hoff := p31_frac_corr_off q hq0 hq1 n hn
  have hdiag := p31_corr_diag q hq0 hq1 (fracLaw q n) hexp
  have hσ1 : σ ≤ 1 := by have := p31_sig_neg q hq0 hq n hn; linarith
  have hupper : ∀ M : ℝ, (∀ h : ℕ, h ≤ n → p31_G σ h ≤ M) →
      ∀ y ∈ box (fun _ : Fin n => (1 : ℝ)), y ⬝ᵥ (corr q (fracLaw q n) *ᵥ y) ≤ M := by
    intro M hM y hy
    exact p31_val_upper _ σ hσ1 hdiag hoff M hM y hy
  have hne : ({P | IsExperiment q P} : Set ((Fin n → Bool) → ℝ)).Nonempty := ⟨_, hexp⟩
  have hlow : ∀ h : ℕ, h ≤ n → p31_G σ h ≤ VOPT q (fun _ : Fin n => (1 : ℝ)) := by
    intro h hh
    unfold VOPT
    apply le_csInf (hne.image _)
    rintro _ ⟨P, hP, rfl⟩
    exact p31_lower hn q hq0 hq1 P hP h hh
  have hVle : VOPT q (fun _ : Fin n => (1 : ℝ)) ≤
      worstCase (corr q (fracLaw q n)) (fun _ : Fin n => (1 : ℝ)) := by
    unfold VOPT
    apply csInf_le
    · refine ⟨0, ?_⟩
      rintro _ ⟨P, -, rfl⟩
      exact p31_wc_nonneg _ _ (fun _ => zero_le_one)
    · exact ⟨_, hexp, rfl⟩
  obtain ⟨h0, hh0, hmax⟩ := Finset.exists_max_image (Finset.range (n + 1))
    (fun h : ℕ => p31_G σ h) ⟨0, Finset.mem_range.2 (by omega)⟩
  have hmax' : ∀ h : ℕ, h ≤ n → p31_G σ h ≤ p31_G σ h0 :=
    fun h hh => hmax h (Finset.mem_range.2 (by omega))
  have hh0n : h0 ≤ n := by have := Finset.mem_range.1 hh0; omega
  have hwc : worstCase (corr q (fracLaw q n)) (fun _ : Fin n => (1 : ℝ)) ≤ p31_G σ h0 := by
    unfold worstCase
    apply csSup_le ⟨_, Set.mem_image_of_mem _ (p31_zero_mem _ (fun _ => zero_le_one))⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hupper _ hmax' y hy
  have hV0 := hlow h0 hh0n
  have hVeq : VOPT q (fun _ : Fin n => (1 : ℝ)) = p31_G σ h0 := by linarith
  refine ⟨hexp, by linarith, hoff, hlow, ⟨h0, hh0n, hVeq⟩, ?_⟩
  intro hs hsn hsmax
  have : p31_G σ hs = p31_G σ h0 := le_antisymm (hmax' hs hsn) (hsmax h0 hh0n)
  refine ⟨by rw [hVeq, this], ?_⟩
  intro s hs' y hy
  show y ⬝ᵥ (corr q (fracLaw q n) *ᵥ y) ≤ (fun i => if i ∈ s then (1 : ℝ) else 0) ⬝ᵥ
    (corr q (fracLaw q n) *ᵥ (fun i => if i ∈ s then (1 : ℝ) else 0))
  rw [p31_val_indset _ σ hdiag hoff s, hs']
  have := hupper _ hsmax y hy
  unfold p31_G at this
  exact this

/-! ## Part 7: the cases of Proposition 3.1 and the limit -/

lemma p31_sig_int (q : ℝ) (n m : ℕ) (hn : 2 ≤ n) (hm : q * n = m) :
    p31_sig q n = -1 / ((n : ℝ) - 1) := by
  unfold p31_sig
  rw [hm, Nat.floor_natCast]
  simp only [sub_self, zero_mul, zero_div, zero_sub]
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have : (n : ℝ) ≠ 0 := by positivity
  have : (n : ℝ) - 1 ≠ 0 := by linarith
  field_simp

lemma p31_x0_int (n : ℕ) (hn : 2 ≤ n) :
    -1 / (2 * (-1 / ((n : ℝ) - 1))) + 1 / 2 = (n : ℝ) / 2 := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have : (n : ℝ) - 1 ≠ 0 := by linarith
  field_simp
  ring

lemma p31_odd_sq (n h : ℕ) (hn : Odd n) : 1 / 4 ≤ ((h : ℝ) - (n : ℝ) / 2) ^ 2 := by
  obtain ⟨k, rfl⟩ := hn
  have hd : (2 * (h : ℤ) - (2 * k + 1)) ≤ -1 ∨ 1 ≤ (2 * (h : ℤ) - (2 * k + 1)) := by omega
  have hsq : (1 : ℤ) ≤ (2 * (h : ℤ) - (2 * k + 1)) ^ 2 := by
    rcases hd with hd | hd <;> nlinarith
  have hsqR : (1 : ℝ) ≤ (2 * (h : ℝ) - (2 * k + 1)) ^ 2 := by exact_mod_cast hsq
  push_cast
  nlinarith

lemma p31_limit (q : ℝ) (hq0 : 0 < q) (hq : q ≤ 1 / 2) :
    Filter.Tendsto (fun n : ℕ => 4 * VOPT q (fun _ : Fin n => (1 : ℝ)) / n)
      Filter.atTop (nhds 1) := by
  have hq1 : q < 1 := by linarith
  have hpos : 0 < q * (1 - q) := mul_pos hq0 (by linarith)
  set K : ℝ := 1 / (4 * (q * (1 - q))) with hK
  have hK0 : 0 < K := by positivity
  set u : ℕ → ℝ := fun n => (n : ℝ) ^ 2 / (((n : ℝ) - 1) * ((n : ℝ) - K)) with hu
  have hulim : Filter.Tendsto u Filter.atTop (nhds 1) := by
    have h1 : Filter.Tendsto (fun n : ℕ => 1 / ((1 - 1 / (n : ℝ)) * (1 - K * (1 / (n : ℝ)))))
        Filter.atTop (nhds (1 / ((1 - 0) * (1 - K * 0)))) := by
      apply Filter.Tendsto.div tendsto_const_nhds
      · apply Filter.Tendsto.mul
        · exact tendsto_const_nhds.sub tendsto_one_div_atTop_nhds_zero_nat
        · exact tendsto_const_nhds.sub (tendsto_const_nhds.mul tendsto_one_div_atTop_nhds_zero_nat)
      · norm_num
    simp only [sub_zero, mul_zero, mul_one, div_one] at h1
    apply h1.congr'
    filter_upwards [Filter.eventually_ge_atTop (⌈K⌉₊ + 2)] with n hn
    have hnK : K + 2 ≤ (n : ℝ) := by
      have : ((⌈K⌉₊ + 2 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
      push_cast at this; linarith [Nat.le_ceil K]
    have : (n : ℝ) ≠ 0 := by linarith
    have : (n : ℝ) - 1 ≠ 0 := by linarith
    have : (n : ℝ) - K ≠ 0 := by linarith
    simp only [hu]
    field_simp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hulim
  · filter_upwards [Filter.eventually_ge_atTop 2] with n hn
    obtain ⟨-, -, -, hlow, -, -⟩ := p31_main q hq0 hq n hn
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hl := hlow (n / 2) (Nat.div_le_self _ _)
    have hsg := p31_sig_ge q hq0 hq n hn
    set h := n / 2 with hh
    have hhR : (h : ℝ) * ((h : ℝ) - 1) ≥ 0 := by
      rcases Nat.eq_zero_or_pos h with h0 | h0
      · rw [h0]; simp
      · have : (1 : ℝ) ≤ h := by exact_mod_cast h0
        nlinarith
    have hG : (h : ℝ) * ((n : ℝ) - h) / ((n : ℝ) - 1) ≤ p31_G (p31_sig q n) h := by
      unfold p31_G
      have := mul_le_mul_of_nonneg_left hsg hhR
      have e : (h : ℝ) * ((n : ℝ) - h) / ((n : ℝ) - 1) =
          h + h * ((h : ℝ) - 1) * (-1 / ((n : ℝ) - 1)) := by
        have : (n : ℝ) - 1 ≠ 0 := by linarith
        field_simp; ring
      rw [e]; linarith
    have h4 : (n : ℝ) * ((n : ℝ) - 1) ≤ 4 * ((h : ℝ) * ((n : ℝ) - h)) := by
      have hc : n = 2 * h ∨ n = 2 * h + 1 := by omega
      rcases hc with hc | hc
      · have : (n : ℝ) = 2 * h := by exact_mod_cast hc
        rw [this]; nlinarith
      · have : (n : ℝ) = 2 * h + 1 := by exact_mod_cast hc
        rw [this]; nlinarith
    rw [le_div_iff₀ (by linarith), one_mul]
    have : (n : ℝ) / 4 ≤ (h : ℝ) * ((n : ℝ) - h) / ((n : ℝ) - 1) := by
      rw [div_le_div_iff₀ (by norm_num) (by linarith)]; linarith
    linarith
  · filter_upwards [Filter.eventually_ge_atTop 2,
      Filter.eventually_gt_atTop ⌈2 * K⌉₊] with n hn hnK
    obtain ⟨-, -, -, -, ⟨h0, -, hV⟩, -⟩ := p31_main q hq0 hq n hn
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hnK' : 2 * K < n := lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hnK)
    set σ := p31_sig q n with hσ
    set s := -σ with hs
    -- bounds on s
    have hx : 0 ≤ q * n := by positivity
    set R := (q * n - ⌊q * n⌋₊) * (1 - (q * n - ⌊q * n⌋₊)) with hR
    have hR0 : 0 ≤ R := by
      have ha0 : (⌊q * n⌋₊ : ℝ) ≤ q * n := Nat.floor_le hx
      have ha1 : q * n < (⌊q * n⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
      apply mul_nonneg <;> linarith
    have hR1 : R ≤ 1 / 4 := by nlinarith [sq_nonneg (q * n - ⌊q * n⌋₊ - 1 / 2)]
    have hV0 : R / (q * (1 - q)) ≤ K := by
      rw [hK, div_le_div_iff₀ hpos (by positivity)]; nlinarith
    have hV00 : 0 ≤ R / (q * (1 - q)) := div_nonneg hR0 hpos.le
    have hnn : 0 < (n : ℝ) * ((n : ℝ) - 1) := by apply mul_pos <;> linarith
    have hsdef : s = ((n : ℝ) - R / (q * (1 - q))) / ((n : ℝ) * ((n : ℝ) - 1)) := by
      rw [hs, hσ]; unfold p31_sig; rw [← hR, ← neg_div]; ring
    have hs_up : s ≤ 1 / ((n : ℝ) - 1) := by
      rw [hsdef, div_le_div_iff₀ hnn (by linarith)]; nlinarith
    have hs_lo : ((n : ℝ) - K) / ((n : ℝ) * ((n : ℝ) - 1)) ≤ s := by
      rw [hsdef]; apply div_le_div_of_nonneg_right _ hnn.le; linarith
    have hnK0 : 0 < (n : ℝ) - K := by linarith
    have hs0 : 0 < s := lt_of_lt_of_le (div_pos hnK0 hnn) hs_lo
    -- G(h0) ≤ (1+s)²/(4s)
    have hG : p31_G σ h0 ≤ (1 + s) ^ 2 / (4 * s) := by
      unfold p31_G
      rw [le_div_iff₀ (by positivity)]
      have : σ = -s := by rw [hs]; ring
      rw [this]
      nlinarith [sq_nonneg (2 * s * h0 - (1 + s))]
    rw [hV]
    have hnpos : (0 : ℝ) < n := by linarith
    have step1 : 4 * p31_G σ h0 / n ≤ (1 + s) ^ 2 * (1 / s) / n := by
      apply div_le_div_of_nonneg_right _ hnpos.le
      have : 4 * ((1 + s) ^ 2 / (4 * s)) = (1 + s) ^ 2 * (1 / s) := by field_simp
      linarith
    have h1s : (1 + s) ^ 2 ≤ ((n : ℝ) / ((n : ℝ) - 1)) ^ 2 := by
      have : 1 + s ≤ (n : ℝ) / ((n : ℝ) - 1) := by
        have e : (n : ℝ) / ((n : ℝ) - 1) = 1 + 1 / ((n : ℝ) - 1) := by
          have : (n : ℝ) - 1 ≠ 0 := by linarith
          field_simp; ring
        rw [e]; linarith
      apply pow_le_pow_left₀ (by linarith) this
    have hinv : 1 / s ≤ (n : ℝ) * ((n : ℝ) - 1) / ((n : ℝ) - K) := by
      rw [div_le_div_iff₀ hs0 hnK0, one_mul]
      have := (div_le_iff₀ hnn).1 hs_lo
      linarith
    have step2 : (1 + s) ^ 2 * (1 / s) / n ≤
        ((n : ℝ) / ((n : ℝ) - 1)) ^ 2 * ((n : ℝ) * ((n : ℝ) - 1) / ((n : ℝ) - K)) / n := by
      apply div_le_div_of_nonneg_right _ hnpos.le
      apply mul_le_mul h1s hinv (by positivity) (by positivity)
    have e3 : ((n : ℝ) / ((n : ℝ) - 1)) ^ 2 * ((n : ℝ) * ((n : ℝ) - 1) / ((n : ℝ) - K)) / n =
        u n := by
      simp only [hu]
      have : (n : ℝ) - 1 ≠ 0 := by linarith
      have : (n : ℝ) ≠ 0 := by linarith
      have : (n : ℝ) - K ≠ 0 := by linarith
      field_simp
    linarith

theorem solution (q : ℝ) (hq0 : 0 < q) (hq : q ≤ 1 / 2) :
    (∀ n : ℕ, 2 ≤ n →
      IsExperiment q (fracLaw q n) ∧
      worstCase (corr q (fracLaw q n)) (fun _ : Fin n => (1 : ℝ)) =
        VOPT q (fun _ : Fin n => (1 : ℝ)) ∧
      ((∃ m : ℕ, q * n = m) →
        (∀ i k : Fin n, i ≠ k → corr q (fracLaw q n) i k = -1 / ((n : ℝ) - 1)) ∧
        (Even n →
          (∀ s : Finset (Fin n), 2 * s.card = n →
            IsMaxOn (fun y => y ⬝ᵥ (corr q (fracLaw q n) *ᵥ y)) (box fun _ : Fin n => (1 : ℝ))
              (fun i => if i ∈ s then (1 : ℝ) else 0)) ∧
          VOPT q (fun _ : Fin n => (1 : ℝ)) = 1 / 4 * ((n : ℝ) ^ 2 / ((n : ℝ) - 1))) ∧
        (Odd n →
          (∀ s : Finset (Fin n), (2 * s.card = n + 1 ∨ 2 * s.card + 1 = n) →
            IsMaxOn (fun y => y ⬝ᵥ (corr q (fracLaw q n) *ᵥ y)) (box fun _ : Fin n => (1 : ℝ))
              (fun i => if i ∈ s then (1 : ℝ) else 0)) ∧
          VOPT q (fun _ : Fin n => (1 : ℝ)) = ((n : ℝ) + 1) / 4)) ∧
      ((¬ ∃ m : ℕ, q * n = m) →
        ∀ p σ : ℝ, p = (⌈q * n⌉₊ : ℝ) - q * n →
          σ = -((n * q * (1 - q) - p * (1 - p)) / (n * (n - 1) * q * (1 - q))) →
          (∀ i k : Fin n, i ≠ k → corr q (fracLaw q n) i k = σ) ∧
          -1 / ((n : ℝ) - 1) < σ ∧ σ < 0 ∧
          ∀ hstar : ℕ,
            (∀ h : ℤ, |(hstar : ℝ) - min (-1 / (2 * σ) + 1 / 2) (n : ℝ)| ≤
              |(h : ℝ) - min (-1 / (2 * σ) + 1 / 2) (n : ℝ)|) →
            (∀ s : Finset (Fin n), s.card = hstar →
              IsMaxOn (fun y => y ⬝ᵥ (corr q (fracLaw q n) *ᵥ y)) (box fun _ : Fin n => (1 : ℝ))
                (fun i => if i ∈ s then (1 : ℝ) else 0)) ∧
            VOPT q (fun _ : Fin n => (1 : ℝ)) = hstar + hstar * ((hstar : ℝ) - 1) * σ)) ∧
    Filter.Tendsto (fun n : ℕ => 4 * VOPT q (fun _ : Fin n => (1 : ℝ)) / n)
      Filter.atTop (nhds 1) := by
  refine ⟨?_, p31_limit q hq0 hq⟩
  intro n hn
  obtain ⟨hexp, hwc, hoff, -, -, hmax⟩ := p31_main q hq0 hq n hn
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  refine ⟨hexp, hwc, ?_, ?_⟩
  · -- integral case
    rintro ⟨m, hm⟩
    have hsig := p31_sig_int q n m hn hm
    have hσneg : p31_sig q n < 0 := p31_sig_neg q hq0 hq n hn
    have hx0 := p31_x0_int n hn
    -- comparison criterion
    have hcrit : ∀ hs : ℕ, (∀ h : ℕ, h ≤ n → ((hs : ℝ) - (n : ℝ) / 2) ^ 2 ≤
        ((h : ℝ) - (n : ℝ) / 2) ^ 2) →
        ∀ h : ℕ, h ≤ n → p31_G (p31_sig q n) h ≤ p31_G (p31_sig q n) hs := by
      intro hs H h hh
      apply p31_G_cmp _ hσneg
      rw [hsig, hx0]; exact H h hh
    refine ⟨fun i k hik => by rw [hoff i k hik, hsig], ?_, ?_⟩
    · intro heven
      obtain ⟨c, hc⟩ := heven
      have hcR : (c : ℝ) = (n : ℝ) / 2 := by
        have : (n : ℝ) = c + c := by exact_mod_cast hc
        linarith
      have hcm : ∀ h : ℕ, h ≤ n → p31_G (p31_sig q n) h ≤ p31_G (p31_sig q n) c := by
        apply hcrit; intro h _; rw [hcR, sub_self]; norm_num; positivity
      have hcn : c ≤ n := by omega
      obtain ⟨hV, hIs⟩ := hmax c hcn hcm
      refine ⟨fun s hs => hIs s (by omega), ?_⟩
      rw [hV]; unfold p31_G; rw [hcR, hsig]
      field_simp
      ring
    · intro hodd
      have hcrit' : ∀ c : ℕ, (2 * c = n + 1 ∨ 2 * c + 1 = n) →
          ∀ h : ℕ, h ≤ n → p31_G (p31_sig q n) h ≤ p31_G (p31_sig q n) c := by
        intro c hc
        apply hcrit
        intro h _
        have : ((c : ℝ) - (n : ℝ) / 2) ^ 2 = 1 / 4 := by
          rcases hc with hc | hc
          · have : (2 : ℝ) * c = n + 1 := by exact_mod_cast hc
            nlinarith
          · have : (2 : ℝ) * c + 1 = n := by exact_mod_cast hc
            nlinarith
        rw [this]; exact p31_odd_sq n h hodd
      refine ⟨fun s hs => (hmax s.card (by omega) (hcrit' s.card hs)).2 s rfl, ?_⟩
      obtain ⟨k, hk⟩ := hodd
      have hk' : 2 * k + 1 = n := by omega
      obtain ⟨hV, -⟩ := hmax k (by omega) (hcrit' k (Or.inr hk'))
      rw [hV]; unfold p31_G; rw [hsig]
      have : (n : ℝ) = 2 * k + 1 := by exact_mod_cast hk'.symm
      rw [this]
      have : (2 * (k : ℝ) + 1) - 1 ≠ 0 := by
        have : (1 : ℝ) ≤ k := by
          have : 1 ≤ k := by omega
          exact_mod_cast this
        linarith
      have hk0 : (k : ℝ) ≠ 0 := by
        have : 1 ≤ k := by omega
        positivity
      field_simp
      ring
  · -- non-integral case
    intro hnot p σ hp hσ
    have hx : 0 ≤ q * n := by positivity
    have hcase : (⌊q * n⌋₊ : ℝ) < q * n ∧ ⌈q * n⌉₊ = ⌊q * n⌋₊ + 1 := by
      rcases p31_ceil_cases (q * n) hx with ⟨h1, -⟩ | h
      · exact absurd ⟨_, h1⟩ hnot
      · exact h
    have ha1 : q * n < (⌊q * n⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have hpos : 0 < q * (1 - q) := mul_pos hq0 (by linarith)
    have hσeq : σ = p31_sig q n := by
      rw [hσ, hp, hcase.2]; unfold p31_sig
      push_cast
      have : (n : ℝ) ≠ 0 := by linarith
      have : (1 - q) ≠ 0 := by linarith
      have : q ≠ 0 := hq0.ne'
      field_simp
      ring
    have hσneg : σ < 0 := by rw [hσeq]; exact p31_sig_neg q hq0 hq n hn
    refine ⟨fun i k hik => by rw [hoff i k hik, hσeq], ?_, hσneg, ?_⟩
    · rw [hσeq]; unfold p31_sig
      have hR : 0 < (q * n - ⌊q * n⌋₊) * (1 - (q * n - ⌊q * n⌋₊)) / (q * (1 - q)) := by
        apply div_pos _ hpos; apply mul_pos <;> linarith [hcase.1]
      rw [div_lt_div_iff₀ (by linarith) (by apply mul_pos <;> linarith)]
      nlinarith
    · intro hstar hnear
      obtain ⟨hsn, hsmax⟩ := p31_G_nearest σ hσneg n hstar hnear
      rw [hσeq] at hsmax
      obtain ⟨hV, hIs⟩ := hmax hstar hsn hsmax
      refine ⟨hIs, ?_⟩
      rw [hV, hσeq]; rfl
