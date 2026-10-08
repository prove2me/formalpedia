-- Prove2me | solution 1 for BartlettNN.Sigmoid.lemma23_pdim_cover
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T05:34:30.218041+00:00
-- url     : https://prove2.me/submissions/d9516f7b-cd0b-46a2-9a50-db224328a2ce

import Mathlib
import Definitions.Def_BartlettNN_Sigmoid_Fat
import Definitions.Def_BartlettNN_FatNet_coverNum

set_option autoImplicit false

/-- Strict Sauer-type binomial bound. -/
lemma d7b_binom_lt (d L : ℕ) (hd : 1 ≤ d) (hdL : d ≤ L) :
    ((∑ k ∈ Finset.range (d + 1), L.choose k : ℕ) : ℝ) < (Real.exp 1 * L / d) ^ d := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (lt_of_lt_of_le hd hdL)
  have hL0 : L ≠ 0 := by omega
  set x : ℝ := d / L with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 := by rw [hx, div_le_one hLpos]; exact_mod_cast hdL
  have hmain : ((∑ k ∈ Finset.range (d + 1), L.choose k : ℕ) : ℝ) * x ^ d < Real.exp 1 ^ d := by
    rw [Nat.cast_sum, Finset.sum_mul]
    calc ∑ k ∈ Finset.range (d + 1), ((L.choose k : ℕ) : ℝ) * x ^ d
        ≤ ∑ k ∈ Finset.range (d + 1), (L.choose k : ℝ) * x ^ k := by
          apply Finset.sum_le_sum; intro k hk
          have hk' : k ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
          exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hx0.le hx1 hk') (by positivity)
      _ ≤ ∑ k ∈ Finset.range (L + 1), (L.choose k : ℝ) * x ^ k := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.range_subset_range.2 (by omega)
          · intros; positivity
      _ = (x + 1) ^ L := by
          rw [add_pow]; apply Finset.sum_congr rfl; intros; rw [one_pow]; ring
      _ < Real.exp x ^ L := by
          exact pow_lt_pow_left₀ (Real.add_one_lt_exp hx0.ne') (by positivity) hL0
      _ = Real.exp 1 ^ d := by
          rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; congr 1; rw [hx]; field_simp
  have : (Real.exp 1 * L / d) ^ d = Real.exp 1 ^ d / x ^ d := by
    rw [hx, div_pow, div_pow, mul_pow]; field_simp
  rw [this, lt_div_iff₀ (by positivity)]
  exact hmain

open BartlettNN.Margin in
/-- Pseudo-shattering with strict/weak thresholds yields γ-shattering at some positive margin. -/
lemma d7b_margin {X : Type} (F : Set (X → ℝ)) {ι : Type} [Fintype ι] (x' : ι → X) (r : ι → ℝ)
    (h : ∀ b : ι → Bool, ∃ f ∈ F, ∀ j, (r j ≤ f (x' j) ↔ b j = true)) :
    ∃ γ0 : ℝ, 0 < γ0 ∧ ∃ r' : ι → ℝ, ∀ b : ι → Bool, ∃ f ∈ F, ∀ j,
      γ0 ≤ (f (x' j) - r' j) * pm (b j) := by
  classical
  choose g hgF hg using h
  let φ : (ι → Bool) × ι → ℝ := fun p => r p.2 - g p.1 (x' p.2)
  let D : Finset ((ι → Bool) × ι) := Finset.univ.filter (fun p => g p.1 (x' p.2) < r p.2)
  let S : Finset ℝ := insert 1 (D.image φ)
  have hS : S.Nonempty := Finset.insert_nonempty _ _
  set δ := S.min' hS with hδ
  have hδpos : 0 < δ := by
    rw [hδ, Finset.lt_min'_iff]
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · norm_num
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hy
      have := (Finset.mem_filter.1 hp).2
      simp only [φ]; linarith
  have hδle : ∀ p ∈ D, δ ≤ φ p := fun p hp =>
    Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hp))
  refine ⟨δ / 2, by linarith, fun j => r j - δ / 2, fun b => ⟨g b, hgF b, fun j => ?_⟩⟩
  have hbj := hg b j
  cases hb : b j
  · have hlt : g b (x' j) < r j := by
      by_contra hc; rw [not_lt] at hc; have := hbj.1 hc; rw [hb] at this; exact absurd this (by simp)
    have := hδle (b, j) (Finset.mem_filter.2 ⟨Finset.mem_univ _, hlt⟩)
    simp only [φ] at this
    simp only [pm]; norm_num; linarith
  · have hle : r j ≤ g b (x' j) := hbj.2 hb
    simp only [pm]; norm_num; linarith

open BartlettNN.Margin in
/-- If the threshold patterns agree, the values are within `w`. -/
lemma d7b_close (M w v u : ℝ) (n : ℕ) (hw : 0 < w) (hM : M = (n + 1) * w)
    (hv : v ∈ Set.Icc (-M / 2) (M / 2)) (hu : u ∈ Set.Icc (-M / 2) (M / 2))
    (h : ∀ k : ℕ, k < n → (-M / 2 + (k + 1) * w ≤ v ↔ -M / 2 + (k + 1) * w ≤ u)) :
    |v - u| ≤ w := by
  -- show u ≤ v + w and v ≤ u + w by symmetric argument
  have key : ∀ a b : ℝ, a ∈ Set.Icc (-M / 2) (M / 2) → b ∈ Set.Icc (-M / 2) (M / 2) →
      (∀ k : ℕ, k < n → (-M / 2 + (k + 1) * w ≤ a ↔ -M / 2 + (k + 1) * w ≤ b)) → b ≤ a + w := by
    intro a b ha hb hab
    by_contra hc
    rw [not_le] at hc
    set k := ⌊(a + M / 2) / w⌋₊ with hk
    have hy0 : 0 ≤ (a + M / 2) / w := div_nonneg (by linarith [ha.1]) hw.le
    have h1 : (k : ℝ) ≤ (a + M / 2) / w := Nat.floor_le hy0
    have h2 : (a + M / 2) / w < k + 1 := Nat.lt_floor_add_one _
    have h1' : (k : ℝ) * w ≤ a + M / 2 := by rwa [le_div_iff₀ hw] at h1
    have h2' : a + M / 2 < (k + 1) * w := by rwa [div_lt_iff₀ hw] at h2
    have hthr_b : -M / 2 + (k + 1) * w ≤ b := by nlinarith
    have hkn : k < n := by
      have : -M / 2 + (k + 1) * w < M / 2 := by linarith [hb.2]
      have : ((k : ℝ) + 1) * w < (n + 1) * w := by linarith
      have : (k : ℝ) + 1 < n + 1 := lt_of_mul_lt_mul_right this hw.le
      exact_mod_cast (by linarith : (k : ℝ) < n)
    have := (hab k hkn).2 hthr_b
    linarith
  rw [abs_le]
  constructor
  · have := key v u hv hu h; linarith
  · have := key u v hu hv (fun k hk => (h k hk).symm); linarith

open BartlettNN.Margin in
lemma d7b_fat_le {X : Type} (F : Set (X → ℝ)) (d : ℕ) (hp : BartlettNN.Sigmoid.pdim F = d)
    {k : ℕ} (x' : Fin k → X) (γ0 : ℝ) (hγ0 : 0 < γ0) (hs : GammaShatters F γ0 x') : k ≤ d := by
  have h1 : (k : ℕ∞) ≤ fat F γ0 :=
    le_iSup_of_le k (le_iSup_of_le x' (le_iSup_of_le hs le_rfl))
  have h2 : fat F γ0 ≤ BartlettNN.Sigmoid.pdim F :=
    le_iSup_of_le γ0 (le_iSup_of_le hγ0 le_rfl)
  have := h1.trans (h2.trans hp.le)
  exact_mod_cast this

open BartlettNN.Margin in
/-- Covering number at a fixed sample is bounded by the Sauer sum. -/
lemma d7b_cover_le {X : Type} (F : Set (X → ℝ)) (M γ : ℝ) (d m : ℕ)
    (hF : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (-M / 2) (M / 2))
    (hp : BartlettNN.Sigmoid.pdim F = d) (hM : 0 < M) (hγ : 0 < γ) (x : Fin m → X) :
    coverNum (dInf x) F γ ≤
      ((∑ k ∈ Finset.range (d + 1), (m * ⌊M / γ⌋₊).choose k : ℕ) : ℕ∞) := by
  classical
  set n := ⌊M / γ⌋₊ with hn
  set w : ℝ := M / (n + 1) with hw
  have hwpos : 0 < w := by positivity
  have hMw : M = (n + 1) * w := by rw [hw]; field_simp
  have hwγ : w < γ := by
    rw [hw, div_lt_iff₀ (by positivity)]
    have := Nat.lt_floor_add_one (M / γ)
    rw [div_lt_iff₀ hγ] at this
    linarith
  let thr : Fin n → ℝ := fun k => -M / 2 + ((k : ℕ) + 1) * w
  let enc : (X → ℝ) → Finset (Fin m × Fin n) := fun f =>
    Finset.univ.filter (fun z => thr z.2 ≤ f (x z.1))
  let 𝒜 : Finset (Finset (Fin m × Fin n)) := Finset.univ.filter (fun s => ∃ f ∈ F, enc f = s)
  let rep : Finset (Fin m × Fin n) → (X → ℝ) := fun s =>
    if h : ∃ f ∈ F, enc f = s then h.choose else 0
  -- covering
  have hcover : ∀ f ∈ F, ∃ g ∈ 𝒜.image rep, dInf x g f < γ := by
    intro f hf
    have hex : ∃ g ∈ F, enc g = enc f := ⟨f, hf, rfl⟩
    refine ⟨rep (enc f), Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, f, hf, rfl⟩), ?_⟩
    have hrep : rep (enc f) = hex.choose := by simp only [rep, dif_pos hex]
    obtain ⟨hgF, hge⟩ := hex.choose_spec
    rw [hrep]
    set g := hex.choose
    have hi : ∀ i, |g (x i) - f (x i)| ≤ w := by
      intro i
      apply d7b_close M w _ _ n hwpos hMw (hF g hgF _) (hF f hf _)
      intro k hk
      have := congrArg (fun s => (i, (⟨k, hk⟩ : Fin n)) ∈ s) hge
      simpa [enc, thr] using this
    rcases isEmpty_or_nonempty (Fin m) with hm | hm
    · simp [dInf, Real.iSup_of_isEmpty, hγ]
    · obtain ⟨i, hi'⟩ := exists_eq_ciSup_of_finite (f := fun i => |g (x i) - f (x i)|)
      simp only [dInf]
      rw [← hi']
      exact lt_of_le_of_lt (hi i) hwγ
  have hcov : coverNum (dInf x) F γ ≤ ((𝒜.image rep).card : ℕ∞) :=
    iInf₂_le (f := fun (T : Finset (X → ℝ)) (_ : ∀ f ∈ F, ∃ g ∈ T, dInf x g f < γ) =>
      (T.card : ℕ∞)) _ hcover
  -- shattered sets are small
  have hshat : ∀ s, 𝒜.Shatters s → s.card ≤ d := by
    intro s hs
    have hpseudo : ∀ b : s → Bool, ∃ f ∈ F, ∀ j : s,
        (thr j.1.2 ≤ f (x j.1.1) ↔ b j = true) := by
      intro b
      obtain ⟨u, hu, hsu⟩ :=
        hs (Finset.filter_subset (fun z => ∃ hz : z ∈ s, b ⟨z, hz⟩ = true) s)
      obtain ⟨f, hf, rfl⟩ := (Finset.mem_filter.1 hu).2
      refine ⟨f, hf, fun j => ?_⟩
      have key := congrArg (fun t => j.1 ∈ t) hsu
      simp only [enc, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and,
        eq_iff_iff] at key
      have hj := j.2
      constructor
      · intro h1
        obtain ⟨_, _, h3⟩ := key.1 ⟨hj, h1⟩
        exact h3
      · intro h1
        exact (key.2 ⟨hj, ⟨hj, h1⟩⟩).2
    obtain ⟨γ0, hγ0, r', hr'⟩ := d7b_margin F (fun j : s => x j.1.1) (fun j => thr j.1.2) hpseudo
    let e : Fin s.card ≃ s := s.equivFin.symm
    have hG : GammaShatters F γ0 (fun i => x (e i).1.1) := by
      refine ⟨fun i => r' (e i), fun b => ?_⟩
      obtain ⟨f, hf, hfb⟩ := hr' (fun j => b (e.symm j))
      refine ⟨f, hf, fun i => ?_⟩
      have := hfb (e i)
      simpa using this
    exact d7b_fat_le F d hp _ γ0 hγ0 hG
  have hcard : 𝒜.card ≤ ∑ k ∈ Finset.range (d + 1), (m * n).choose k := by
    calc 𝒜.card ≤ 𝒜.shatterer.card := Finset.card_le_card_shatterer 𝒜
      _ ≤ ∑ k ∈ Finset.range (d + 1),
            ((Finset.univ : Finset (Fin m × Fin n)).powersetCard k).card := by
          refine (Finset.card_le_card fun s hs => Finset.mem_biUnion.2 ⟨s.card, ?_⟩).trans
            Finset.card_biUnion_le
          have := hshat s (Finset.mem_shatterer.1 hs)
          exact ⟨Finset.mem_range.2 (by omega),
            Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, rfl⟩⟩
      _ = ∑ k ∈ Finset.range (d + 1), (m * n).choose k := by
          simp [Finset.card_powersetCard]
  calc coverNum (dInf x) F γ ≤ ((𝒜.image rep).card : ℕ∞) := hcov
    _ ≤ (𝒜.card : ℕ∞) := by exact_mod_cast Finset.card_image_le
    _ ≤ _ := by exact_mod_cast hcard

/-! Lemma 23 [20], p. 533, for positive scales below `emM/d`. -/

open BartlettNN.Sigmoid in
theorem solution :
    ∀ {X : Type} (F : Set (X → ℝ)) (M γ : ℝ) (d m : ℕ),
      F.Nonempty →
      (∀ f ∈ F, ∀ x, f x ∈ Set.Icc (-M / 2) (M / 2)) →
      pdim F = d → 0 < M → 0 < γ → 1 ≤ d → d ≤ m →
      γ < Real.exp 1 * m * M / d →
      ∃ K : ℕ, BartlettNN.Margin.Ninf F γ m = K ∧
        Real.log K < d * Real.log (Real.exp 1 * m * M / (γ * d)) := by
  intro X F M γ d m _ hF hp hM hγ hd hdm hγlt
  set n := ⌊M / γ⌋₊ with hn
  set B : ℕ := ∑ k ∈ Finset.range (d + 1), (m * n).choose k with hB
  have hNle : BartlettNN.Margin.Ninf F γ m ≤ (B : ℕ∞) :=
    iSup_le fun x => d7b_cover_le F M γ d m hF hp hM hγ x
  have hNtop : BartlettNN.Margin.Ninf F γ m ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top _) hNle
  set K := (BartlettNN.Margin.Ninf F γ m).toNat with hK
  have hNK : BartlettNN.Margin.Ninf F γ m = K := (ENat.natCast_toNat hNtop).symm
  have hKB : K ≤ B := by
    have : (K : ℕ∞) ≤ B := hNK ▸ hNle
    exact_mod_cast this
  refine ⟨K, hNK, ?_⟩
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le hd hdm)
  set base : ℝ := Real.exp 1 * m * M / (γ * d) with hbase
  have hbase1 : 1 < base := by
    rw [hbase, one_lt_div (by positivity)]
    rw [lt_div_iff₀ hdpos] at hγlt
    linarith
  have hlogpos : 0 < Real.log base := Real.log_pos hbase1
  have hBlt : (B : ℝ) < base ^ d := by
    rcases Nat.eq_zero_or_pos n with h0 | hnpos
    · have : B = 1 := by
        rw [hB, h0, mul_zero]
        rw [Finset.sum_eq_single 0]
        · simp
        · intro k _ hk; exact Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hk)
        · intro h; simp at h
      rw [this]; push_cast
      exact one_lt_pow₀ hbase1 (by omega)
    · have hL : d ≤ m * n := le_trans hdm (Nat.le_mul_of_pos_right m hnpos)
      have h1 := d7b_binom_lt d (m * n) hd hL
      refine lt_of_lt_of_le h1 ?_
      apply pow_le_pow_left₀ (by positivity)
      have hnle : (n : ℝ) ≤ M / γ := Nat.floor_le (by positivity)
      rw [hbase]
      push_cast
      rw [div_le_div_iff₀ hdpos (by positivity)]
      have : (n : ℝ) * γ ≤ M := by rwa [le_div_iff₀ hγ] at hnle
      have he : 0 < Real.exp 1 := Real.exp_pos 1
      have : Real.exp 1 * m * (n * γ) ≤ Real.exp 1 * m * M := by gcongr
      nlinarith
  rcases Nat.eq_zero_or_pos K with hK0 | hKpos
  · rw [hK0]; simp; positivity
  · have hKr : (0 : ℝ) < K := by exact_mod_cast hKpos
    calc Real.log K ≤ Real.log B := Real.log_le_log hKr (by exact_mod_cast hKB)
      _ < Real.log (base ^ d) := Real.log_lt_log (by
            have : (0 : ℝ) < B := lt_of_lt_of_le hKr (by exact_mod_cast hKB)
            exact this) hBlt
      _ = d * Real.log base := by rw [Real.log_pow]
