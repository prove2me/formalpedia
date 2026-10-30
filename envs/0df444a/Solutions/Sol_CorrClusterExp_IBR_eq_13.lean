-- Prove2me | solution 1 for CorrClusterExp.IBR.eq_13
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T20:37:05.097291+00:00
-- url     : https://prove2.me/submissions/0dbe686a-2900-4f7c-aeec-54cc51430489

import Mathlib
import Definitions.Def_CorrClusterExp_IBR_Setting
import Theorems.Thm_CorrClusterExp_IBR_proposition_3_1
import Theorems.Thm_CorrClusterExp_IBR_ibr_additivity
import Theorems.Thm_CorrClusterExp_IBR_lemma_4_2

open CorrClusterExp.IBR Matrix Finset

lemma e13_bdd {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ) :
    BddAbove ((fun y => y ⬝ᵥ (S *ᵥ y)) '' box w) := by
  have hbox : box w = Set.pi Set.univ (fun i => Set.Icc 0 (w i)) := by
    ext y; simp only [Set.mem_pi, Set.mem_univ, forall_const, Set.mem_Icc]; exact Iff.rfl
  have hc : IsCompact (box w) := by
    rw [hbox]; exact isCompact_univ_pi (fun i => isCompact_Icc)
  apply hc.bddAbove_image
  apply Continuous.continuousOn
  exact Continuous.dotProduct continuous_id (Continuous.matrix_mulVec continuous_const continuous_id)

lemma e13_zero_mem {n : ℕ} (w : Fin n → ℝ) (hw0 : ∀ i, 0 ≤ w i) : (0 : Fin n → ℝ) ∈ box w :=
  fun i => ⟨le_refl _, hw0 i⟩

lemma e13_wc_nonneg {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ)
    (hw0 : ∀ i, 0 ≤ w i) : 0 ≤ worstCase S w := by
  unfold worstCase
  apply le_csSup (e13_bdd S w)
  exact ⟨0, e13_zero_mem w hw0, by simp⟩

lemma e13_wc_mono {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (w w' : Fin n → ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (h : ∀ i, w i ≤ w' i) : worstCase S w ≤ worstCase S w' := by
  unfold worstCase
  apply csSup_le_csSup (e13_bdd S w') ⟨_, Set.mem_image_of_mem _ (e13_zero_mem w hw0)⟩
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨y, fun i => ⟨(hy i).1, le_trans (hy i).2 (h i)⟩, rfl⟩

lemma e13_wc_const {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (a : ℝ) (ha : 0 ≤ a) :
    worstCase S (fun _ => a) ≤ a ^ 2 * worstCase S (fun _ => 1) := by
  have hwc0 := e13_wc_nonneg S (fun _ => (1 : ℝ)) (fun _ => zero_le_one)
  unfold worstCase at hwc0 ⊢
  apply csSup_le ⟨_, Set.mem_image_of_mem _ (e13_zero_mem _ (fun _ => ha))⟩
  rintro _ ⟨y, hy, rfl⟩
  dsimp only
  rcases eq_or_lt_of_le ha with h0 | hpos
  · have : y = 0 := by
      funext i; have := hy i; simp only at this; rw [← h0] at this
      exact le_antisymm this.2 this.1
    subst this; simp only [mulVec_zero, dotProduct_zero]; positivity
  · set u : Fin n → ℝ := a⁻¹ • y with hu
    have hyu : y = a • u := by rw [hu, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
    have hub : u ∈ box (fun _ => (1 : ℝ)) := by
      intro i
      have := hy i
      simp only [hu, Pi.smul_apply, smul_eq_mul]
      refine ⟨mul_nonneg (inv_nonneg.2 ha) this.1, ?_⟩
      rw [inv_mul_le_iff₀ hpos]; linarith [this.2]
    have hval : y ⬝ᵥ (S *ᵥ y) = a ^ 2 * (u ⬝ᵥ (S *ᵥ u)) := by
      rw [hyu, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]; ring
    rw [hval]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact le_csSup (e13_bdd S _) ⟨u, hub, rfl⟩

/-- On one cluster `corr` of `fracLaw` has unit diagonal, so the worst case on `[0,1]` is `≤ 1`. -/
lemma e13_wc_one (q : ℝ) (hq0 : 0 < q) (hq : q ≤ 1 / 2) :
    worstCase (corr q (fracLaw q 1)) (fun _ : Fin 1 => (1 : ℝ)) ≤ 1 := by
  have hfl : ⌊q * (1 : ℕ)⌋₊ = 0 := by
    rw [Nat.floor_eq_zero]; push_cast; linarith
  have hcl : ⌈q * (1 : ℕ)⌉₊ = 1 := by
    rw [Nat.ceil_eq_iff (by norm_num)]; push_cast; constructor <;> linarith
  have hC : corr q (fracLaw q 1) 0 0 = 1 := by
    unfold corr fracLaw
    rw [hfl, hcl]
    rw [← (Equiv.funUnique (Fin 1) Bool).symm.sum_comp]
    simp only [Fintype.univ_bool]
    simp [Equiv.funUnique]
    have h1q : (1 : ℝ) - q ≠ 0 := (by linarith : (0 : ℝ) < 1 - q).ne'
    field_simp
  unfold worstCase
  apply csSup_le ⟨_, Set.mem_image_of_mem _ (e13_zero_mem _ (fun _ => zero_le_one))⟩
  rintro _ ⟨y, hy, rfl⟩
  dsimp only
  simp only [dotProduct, mulVec, Fin.sum_univ_one]
  have h00 : (0 : Fin 1) = 0 := rfl
  rw [show corr q (fracLaw q 1) = fun i j => corr q (fracLaw q 1) i j from rfl]
  simp only
  rw [Subsingleton.elim (0 : Fin 1) 0, hC]
  have := hy 0
  simp only at this
  nlinarith [this.1, this.2]

/-- Marginal of a law on `Fin k` to the first `m` coordinates. -/
noncomputable def e13_marg {m k : ℕ} (h : m ≤ k) (P : (Fin k → Bool) → ℝ)
    (z' : Fin m → Bool) : ℝ :=
  ∑ z, if (fun i => z (Fin.castLE h i)) = z' then P z else 0

lemma e13_marg_sum {m k : ℕ} (h : m ≤ k) (P : (Fin k → Bool) → ℝ)
    (c : (Fin m → Bool) → Prop) [DecidablePred c] :
    ∑ z', (if c z' then e13_marg h P z' else 0) =
      ∑ z, (if c (fun i => z (Fin.castLE h i)) then P z else 0) := by
  unfold e13_marg
  have hh : ∀ z' : Fin m → Bool, (if c z' then ∑ z, (if (fun i => z (Fin.castLE h i)) = z' then
      P z else 0) else 0) = ∑ z, (if c z' then (if (fun i => z (Fin.castLE h i)) = z' then
      P z else 0) else 0) := by
    intro z'; split_ifs <;> simp
  simp_rw [hh]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  rw [Finset.sum_eq_single (fun i => z (Fin.castLE h i))]
  · simp
  · intro b _ hb
    split_ifs with h1 h2
    · exact absurd h2.symm hb
    · rfl
    · rfl
  · intro hh; exact absurd (Finset.mem_univ _) hh

lemma e13_marg_exp {m k : ℕ} (h : m ≤ k) (q : ℝ) (P : (Fin k → Bool) → ℝ)
    (hP : IsExperiment q P) : IsExperiment q (e13_marg h P) := by
  obtain ⟨h0, h1, h2⟩ := hP
  refine ⟨?_, ?_, ?_⟩
  · intro z'; unfold e13_marg
    apply Finset.sum_nonneg; intro z _; split_ifs
    · exact h0 z
    · exact le_refl _
  · have := e13_marg_sum h P (fun _ => True)
    simp only [if_true] at this
    rw [this, h1]
  · intro i
    rw [e13_marg_sum h P (fun z' => z' i = true)]
    exact h2 (Fin.castLE h i)

lemma e13_marg_corr {m k : ℕ} (h : m ≤ k) (q : ℝ) (P : (Fin k → Bool) → ℝ) (i j : Fin m) :
    corr q (e13_marg h P) i j = corr q P (Fin.castLE h i) (Fin.castLE h j) := by
  unfold corr
  rw [e13_marg_sum h P (fun z' => z' i = true ∧ z' j = true)]

lemma e13_wc_marg {m k : ℕ} (h : m ≤ k) (q : ℝ) (P : (Fin k → Bool) → ℝ) :
    worstCase (corr q (e13_marg h P)) (fun _ : Fin m => (1 : ℝ)) ≤
      worstCase (corr q P) (fun _ : Fin k => (1 : ℝ)) := by
  unfold worstCase
  apply csSup_le ⟨_, Set.mem_image_of_mem _ (e13_zero_mem _ (fun _ => zero_le_one))⟩
  rintro _ ⟨y, hy, rfl⟩
  dsimp only
  set y' : Fin k → ℝ := fun i => if hi : i.val < m then y ⟨i.val, hi⟩ else 0 with hy'
  have hy'b : y' ∈ box (fun _ : Fin k => (1 : ℝ)) := by
    intro i; simp only [hy']; split_ifs
    · exact hy _
    · exact ⟨le_refl _, zero_le_one⟩
  have hcast : ∀ i : Fin m, y' (Fin.castLE h i) = y i := by
    intro i; simp [hy', Fin.castLE, i.isLt]
  have hout : ∀ i : Fin k, i ∉ Set.range (Fin.castLE h) → y' i = 0 := by
    intro i hi
    simp only [hy']
    rw [dif_neg]
    intro hlt
    exact hi ⟨⟨i.val, hlt⟩, Fin.ext rfl⟩
  have hval : y ⬝ᵥ (corr q (e13_marg h P) *ᵥ y) = y' ⬝ᵥ (corr q P *ᵥ y') := by
    simp only [dotProduct, mulVec]
    apply Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h)
    · intro i hi; rw [hout i hi, zero_mul]
    · intro i
      rw [hcast]
      congr 1
      apply Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h)
      · intro j hj; rw [hout j hj, mul_zero]
      · intro j; rw [hcast, e13_marg_corr]
  rw [hval]
  exact le_csSup (e13_bdd _ _) ⟨y', hy'b, rfl⟩

lemma e13_fq_mono (q : ℝ) (hq0 : 0 < q) (hq : q ≤ 1 / 2) {m k : ℕ} (h : m ≤ k) :
    fq q m ≤ fq q k := by
  unfold fq VOPT
  have hne : ({P | IsExperiment q P} : Set ((Fin k → Bool) → ℝ)).Nonempty :=
    ⟨ibrLaw q (Composition.ones k),
      (ibr_additivity q hq0 hq k (Composition.ones k) (fun _ => 1) (fun _ => zero_le_one)).1⟩
  apply le_csInf (hne.image _)
  rintro _ ⟨P, hP, rfl⟩
  calc sInf ((fun P => worstCase (corr q P) (fun _ : Fin m => (1 : ℝ))) ''
          {P | IsExperiment q P})
      ≤ worstCase (corr q (e13_marg h P)) (fun _ : Fin m => (1 : ℝ)) := by
        apply csInf_le
        · refine ⟨0, ?_⟩
          rintro _ ⟨P', -, rfl⟩
          exact e13_wc_nonneg _ _ (fun _ => zero_le_one)
        · exact ⟨_, e13_marg_exp h q P hP, rfl⟩
    _ ≤ _ := e13_wc_marg h q P

lemma e13_fq_ge_one (q : ℝ) (hq0 : 0 < q) (hq : q ≤ 1 / 2) (k : ℕ) (hk : 1 ≤ k) :
    1 ≤ fq q k := by
  have h := lemma_4_2 q hq0 hq k hk (fun _ : Fin k => (1 : ℝ)) (fun _ => zero_le_one)
    (fun _ _ _ => le_refl _)
  unfold fq
  have : (1 : ℝ) ≤ max ((1 : ℝ) ^ 2) (1 / 4 * ∑ _i : Fin k, (1 : ℝ) ^ 2) := by
    simp
  linarith [h.1, h.2.1]

/-- The worst case of the law of Proposition 3.1 on `m ≤ k` unit clusters is at most `f_q(k)`. -/
lemma e13_block_ones (q : ℝ) (hq0 : 0 < q) (hq : q ≤ 1 / 2) (m k : ℕ) (hm : 1 ≤ m)
    (hmk : m ≤ k) :
    worstCase (corr q (fracLaw q m)) (fun _ : Fin m => (1 : ℝ)) ≤ fq q k := by
  rcases eq_or_lt_of_le hm with h1 | h2
  · subst h1
    exact le_trans (e13_wc_one q hq0 hq) (e13_fq_ge_one q hq0 hq k hmk)
  · have hP := ((proposition_3_1 q hq0 hq).1 m h2).2.1
    rw [hP]
    exact e13_fq_mono q hq0 hq hmk

/-- The blocks of the `k`-grouping: `⌊n/k⌋` blocks of size `k`, then a block of size `n mod k`
if it is nonzero. -/
def e13_blocks (n k : ℕ) : List ℕ :=
  List.replicate (n / k) k ++ (if n % k = 0 then [] else [n % k])

lemma e13_mem_blocks {n k a : ℕ} (hk : 1 ≤ k) (ha : a ∈ e13_blocks n k) : 0 < a ∧ a ≤ k := by
  unfold e13_blocks at ha
  rw [List.mem_append] at ha
  rcases ha with ha | ha
  · rw [List.eq_of_mem_replicate ha]; omega
  · split_ifs at ha with h0
    · simp at ha
    · rw [List.mem_singleton] at ha
      subst ha
      exact ⟨Nat.pos_of_ne_zero h0, (Nat.mod_lt n (by omega)).le⟩

lemma e13_sum_blocks (n k : ℕ) : (e13_blocks n k).sum = n := by
  unfold e13_blocks
  rw [List.sum_append, List.sum_replicate, smul_eq_mul]
  split_ifs with h0
  · simp only [List.sum_nil, add_zero]
    have := Nat.div_add_mod n k
    rw [h0, add_zero] at this
    linarith [mul_comm (n / k) k]
  · simp only [List.sum_cons, List.sum_nil, add_zero]
    have := Nat.div_add_mod n k
    linarith [mul_comm (n / k) k]

def e13_comp (n k : ℕ) (hk : 1 ≤ k) : Composition n where
  blocks := e13_blocks n k
  blocks_pos := fun ha => (e13_mem_blocks hk ha).1
  blocks_sum := e13_sum_blocks n k

lemma e13_length (n k : ℕ) (hk : 1 ≤ k) : (e13_comp n k hk).length ≤ n / k + 1 := by
  show (e13_blocks n k).length ≤ n / k + 1
  unfold e13_blocks
  rw [List.length_append, List.length_replicate]
  split_ifs <;> simp

lemma e13_sizeUpTo (n k : ℕ) (hk : 1 ≤ k) (j : ℕ) (hj : j ≤ n / k) :
    (e13_comp n k hk).sizeUpTo j = j * k := by
  show ((e13_blocks n k).take j).sum = j * k
  unfold e13_blocks
  rw [List.take_append_of_le_length (by rw [List.length_replicate]; exact hj),
    List.take_replicate, List.sum_replicate, smul_eq_mul, min_eq_left hj]

lemma e13_kgrouped (n k : ℕ) (hk : 1 ≤ k) : KGrouped k (e13_comp n k hk) := by
  intro h hh
  refine ⟨h, e13_sizeUpTo n k hk h ?_⟩
  rw [Nat.le_div_iff_mul_le (by omega)]
  exact hh.le

theorem solution (q : ℝ) (hq0 : 0 < q) (hq : q ≤ 1 / 2) (k : ℕ) (hk : 1 ≤ k) (n : ℕ)
    (w : Fin n → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw : Antitone w) :
    Vk q k w ≤ fq q k * ∑ i ∈ univ.filter (fun i : Fin n => k ∣ i.val), w i ^ 2 := by
  set c := e13_comp n k hk with hc
  have hVk : Vk q k w ≤ VIBR q w c := by
    unfold Vk
    exact ciInf_le (Finite.bddBelow_range _) (⟨c, e13_kgrouped n k hk⟩ : {c : Composition n // KGrouped k c})
  rw [(ibr_additivity q hq0 hq n c w hw0).2] at hVk
  -- leader of each block
  let lead : Fin c.length → Fin n := fun j => c.embedding j ⟨0, c.one_le_blocksFun j⟩
  have hlead : ∀ j : Fin c.length, (lead j : ℕ) = j.val * k := by
    intro j
    simp only [lead, Composition.coe_embedding, add_zero]
    apply e13_sizeUpTo
    have h1 := j.isLt
    have h2 := e13_length n k hk
    by_contra hcon
    push Not at hcon
    -- then j ≥ n/k + 1, so sizeUpTo (n/k+1) ≤ n contradiction via block sizes
    have : n / k + 1 ≤ j.val := hcon
    have h3 : c.length ≤ n / k + 1 := h2
    omega
  have hblock : ∀ j : Fin c.length,
      worstCase (corr q (fracLaw q (c.blocksFun j))) (fun i => w (c.embedding j i)) ≤
        fq q k * w (lead j) ^ 2 := by
    intro j
    have hbk : c.blocksFun j ≤ k := (e13_mem_blocks hk (c.blocksFun_mem_blocks j)).2
    have hb1 : 1 ≤ c.blocksFun j := c.one_le_blocksFun j
    calc worstCase (corr q (fracLaw q (c.blocksFun j))) (fun i => w (c.embedding j i))
        ≤ worstCase (corr q (fracLaw q (c.blocksFun j))) (fun _ => w (lead j)) := by
          apply e13_wc_mono _ _ _ (fun i => hw0 _)
          intro i
          apply hw
          show lead j ≤ c.embedding j i
          rw [Fin.le_def]
          simp only [lead, Composition.coe_embedding]
          omega
      _ ≤ w (lead j) ^ 2 * worstCase (corr q (fracLaw q (c.blocksFun j))) (fun _ => 1) :=
          e13_wc_const _ _ (hw0 _)
      _ ≤ w (lead j) ^ 2 * fq q k :=
          mul_le_mul_of_nonneg_left (e13_block_ones q hq0 hq _ k hb1 hbk) (sq_nonneg _)
      _ = fq q k * w (lead j) ^ 2 := by ring
  have hinj : Function.Injective lead := by
    intro a b hab
    have := congrArg Fin.val hab
    rw [hlead, hlead] at this
    exact Fin.ext (Nat.eq_of_mul_eq_mul_right (by omega) this)
  have hsum : ∑ j : Fin c.length, w (lead j) ^ 2 ≤
      ∑ i ∈ univ.filter (fun i : Fin n => k ∣ i.val), w i ^ 2 := by
    rw [← Finset.sum_image (f := fun i => w i ^ 2) (fun a _ b _ h => hinj h)]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro i hi
      rw [Finset.mem_image] at hi
      obtain ⟨j, -, rfl⟩ := hi
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by rw [hlead]; exact Dvd.intro_left _ rfl⟩
    · intro i _ _; exact sq_nonneg _
  calc Vk q k w ≤ _ := hVk
    _ ≤ ∑ j : Fin c.length, fq q k * w (lead j) ^ 2 := Finset.sum_le_sum (fun j _ => hblock j)
    _ = fq q k * ∑ j : Fin c.length, w (lead j) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (le_trans zero_le_one (e13_fq_ge_one q hq0 hq k hk))
