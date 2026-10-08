-- Prove2me | solution 1 for BartlettNN.Sigmoid.lemma22_cover_combos
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T15:19:24.955312+00:00
-- url     : https://prove2.me/submissions/31524eb8-610c-4cec-811c-0b0b8e26e01e

import Mathlib
import Definitions.Def_BartlettNN_FatNet_coverNum
import Definitions.Def_BartlettNN_Sigmoid_Networks

set_option autoImplicit false

open BartlettNN.FatNet in
noncomputable def L22phi {X : Type*} {m : ℕ} (x : Fin m → X) :
    (X → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) where
  toFun f := WithLp.toLp 2 (fun i => f (x i) / Real.sqrt m)
  map_add' f g := by
    rw [← WithLp.toLp_add]; congr 1; funext i; simp [add_div]
  map_smul' c f := by
    rw [RingHom.id_apply, ← WithLp.toLp_smul]; congr 1; funext i; simp [mul_div_assoc]

lemma L22_norm_phi_sq {X : Type*} {m : ℕ} (x : Fin m → X) (g : X → ℝ) :
    ‖L22phi x g‖ ^ 2 = (1 / (m : ℝ)) * ∑ i, (g (x i)) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  show (g (x i) / Real.sqrt m) ^ 2 = _
  rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  ring

open BartlettNN.FatNet in
lemma L22_dL2_eq {X : Type*} {m : ℕ} (x : Fin m → X) (f g : X → ℝ) :
    dL2 x f g = ‖L22phi x f - L22phi x g‖ := by
  rw [← map_sub, ← Real.sqrt_sq (norm_nonneg _), L22_norm_phi_sq]
  rfl

lemma L22_norm_phi_sq_le {X : Type*} {m : ℕ} (x : Fin m → X) (g : X → ℝ) (R : ℝ)
    (h : ∀ y, |g y| ≤ R) : ‖L22phi x g‖ ^ 2 ≤ R ^ 2 := by
  rw [L22_norm_phi_sq]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp; positivity
  · have hs : ∑ i, (g (x i)) ^ 2 ≤ ∑ _i : Fin m, R ^ 2 := by
      apply Finset.sum_le_sum; intro i _
      have := h (x i)
      nlinarith [abs_nonneg (g (x i)), sq_abs (g (x i))]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    calc (1 / (m : ℝ)) * ∑ i, (g (x i)) ^ 2 ≤ (1 / (m : ℝ)) * (m * R ^ 2) :=
          mul_le_mul_of_nonneg_left hs (by positivity)
      _ = R ^ 2 := by field_simp

lemma L22_norm_phi_le {X : Type*} {m : ℕ} (x : Fin m → X) (g : X → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (h : ∀ y, |g y| ≤ R) : ‖L22phi x g‖ ≤ R := by
  have := L22_norm_phi_sq_le x g R h
  by_contra hc
  push_neg at hc
  nlinarith [norm_nonneg (L22phi x g)]

lemma L22_var {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]
    (lam : ι → ℝ) (v : ι → E) (h0 : ∀ a, 0 ≤ lam a) (h1 : ∑ a, lam a = 1) (B : ℝ)
    (hB : ∀ a, ‖v a‖ ^ 2 ≤ B) (c : E) (hc : c = ∑ b, lam b • v b) :
    ∑ a, lam a * ‖v a - c‖ ^ 2 ≤ B := by
  have key : ∑ a, lam a * inner ℝ (v a) c = ‖c‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    calc ∑ a, lam a * inner ℝ (v a) c = inner ℝ (∑ a, lam a • v a) c := by
          rw [sum_inner]; simp [real_inner_smul_left]
      _ = inner ℝ c c := by rw [← hc]
  have e : ∀ a, lam a * ‖v a - c‖ ^ 2
      = lam a * ‖v a‖ ^ 2 - 2 * (lam a * inner ℝ (v a) c) + lam a * ‖c‖ ^ 2 := by
    intro a; rw [norm_sub_sq_real]; ring
  rw [Finset.sum_congr rfl (fun a _ => e a), Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, key, ← Finset.sum_mul, h1]
  have : ∑ a, lam a * ‖v a‖ ^ 2 ≤ ∑ a, lam a * B :=
    Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hB a) (h0 a)
  rw [← Finset.sum_mul, h1] at this
  nlinarith [sq_nonneg ‖c‖]

lemma L22_maurey {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]
    (lam : ι → ℝ) (v : ι → E) (h0 : ∀ a, 0 ≤ lam a) (h1 : ∑ a, lam a = 1) (B : ℝ)
    (hB : ∀ a, ‖v a‖ ^ 2 ≤ B) (c : E) (hc : c = ∑ b, lam b • v b) (k : ℕ) :
    ∃ s : Fin k → ι, ‖∑ j, v (s j) - (k : ℝ) • c‖ ^ 2 ≤ k * B := by
  have hvar := L22_var lam v h0 h1 B hB c hc
  have hzero : ∑ a, lam a • (v a - c) = 0 := by
    rw [Finset.sum_congr rfl (fun a _ => smul_sub (lam a) (v a) c), Finset.sum_sub_distrib,
      ← Finset.sum_smul, h1, one_smul, ← hc, sub_self]
  have hne : (Finset.univ : Finset ι).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at h1
    exact zero_ne_one h1
  induction k with
  | zero => exact ⟨Fin.elim0, by simp⟩
  | succ k ih =>
    obtain ⟨s, hs⟩ := ih
    obtain ⟨D, hD⟩ : ∃ D, D = ∑ j, v (s j) - (k : ℝ) • c := ⟨_, rfl⟩
    rw [← hD] at hs
    obtain ⟨a0, -, ha0⟩ := Finset.exists_min_image Finset.univ
      (fun a => ‖D + (v a - c)‖ ^ 2) hne
    have hcross : ∑ a, lam a * inner ℝ D (v a - c) = 0 := by
      have : inner ℝ D (∑ a, lam a • (v a - c)) = 0 := by rw [hzero, inner_zero_right]
      rw [inner_sum] at this
      simpa [real_inner_smul_right] using this
    have e : ∀ a, lam a * ‖D + (v a - c)‖ ^ 2
        = lam a * ‖D‖ ^ 2 + 2 * (lam a * inner ℝ D (v a - c)) + lam a * ‖v a - c‖ ^ 2 := by
      intro a; rw [norm_add_sq_real]; ring
    have havg : ∑ a, lam a * ‖D + (v a - c)‖ ^ 2 = ‖D‖ ^ 2 + ∑ a, lam a * ‖v a - c‖ ^ 2 := by
      rw [Finset.sum_congr rfl (fun a _ => e a), Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.sum_mul, h1, ← Finset.mul_sum, hcross]
      ring
    have hmin : ‖D + (v a0 - c)‖ ^ 2 ≤ ∑ a, lam a * ‖D + (v a - c)‖ ^ 2 := by
      calc ‖D + (v a0 - c)‖ ^ 2 = ∑ a, lam a * ‖D + (v a0 - c)‖ ^ 2 := by
            rw [← Finset.sum_mul, h1, one_mul]
        _ ≤ _ := Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (ha0 a (Finset.mem_univ a)) (h0 a)
    refine ⟨Fin.snoc (α := fun _ => ι) s a0, ?_⟩
    have hsum : ∑ j : Fin (k + 1), v (Fin.snoc (α := fun _ => ι) s a0 j) - ((k + 1 : ℕ) : ℝ) • c
        = D + (v a0 - c) := by
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      rw [hD]; push_cast; rw [add_smul, one_smul]; abel
    rw [hsum]
    push_cast
    linarith

open BartlettNN.FatNet in
lemma L22_cover_of_N2 {X : Type*} {F : Set (X → ℝ)} {ε : ℝ} {m N : ℕ} (hN : N2 F ε m ≤ N)
    (x : Fin m → X) :
    ∃ T : Finset (X → ℝ), T.card ≤ N ∧ ∀ f ∈ F, ∃ t ∈ T, dL2 x t f < ε := by
  have h1 : BartlettNN.Margin.coverNum (dL2 x) F ε ≤ N := by
    exact le_trans (le_iSup (fun x => BartlettNN.Margin.coverNum (dL2 x) F ε) x) hN
  have h2 : BartlettNN.Margin.coverNum (dL2 x) F ε < ((N + 1 : ℕ) : ℕ∞) :=
    lt_of_le_of_lt h1 (by exact_mod_cast Nat.lt_succ_self N)
  unfold BartlettNN.Margin.coverNum at h2
  rw [iInf_lt_iff] at h2
  obtain ⟨T, hT⟩ := h2
  rw [iInf_lt_iff] at hT
  obtain ⟨hcov, hc⟩ := hT
  have : T.card < N + 1 := by exact_mod_cast hc
  exact ⟨T, by omega, hcov⟩

lemma L22_clip_close {lo hi a z : ℝ} (h1 : lo ≤ a) (h2 : a ≤ hi) :
    |max lo (min hi z) - a| ≤ |z - a| := by
  have e1 := le_abs_self (z - a)
  have e2 := neg_abs_le (z - a)
  rw [abs_le]
  simp only [max_def, min_def]
  split_ifs <;> constructor <;> linarith

lemma L22_clip_bound {M z : ℝ} (hM : 0 ≤ M) : |max (-M / 2) (min (M / 2) z)| ≤ M / 2 := by
  rw [abs_le]
  simp only [max_def, min_def]
  split_ifs <;> constructor <;> linarith

noncomputable def L22clip {X : Type*} (M : ℝ) (t : X → ℝ) : X → ℝ :=
  fun y => max (-M / 2) (min (M / 2) (t y))

open BartlettNN.FatNet in
lemma L22_dL2_clip {X : Type*} {m : ℕ} (x : Fin m → X) (M : ℝ) (t f : X → ℝ)
    (hf : ∀ y, f y ∈ Set.Icc (-M / 2) (M / 2)) :
    dL2 x (L22clip M t) f ≤ dL2 x t f := by
  unfold dL2
  apply Real.sqrt_le_sqrt
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro i _
  rw [sq_le_sq]
  exact L22_clip_close (hf (x i)).1 (hf (x i)).2

lemma L22_phi_combo {X : Type*} {m : ℕ} (x : Fin m → X) {n : ℕ} (w : Fin n → ℝ)
    (f : Fin n → X → ℝ) :
    L22phi x (fun y => ∑ i, w i * f i y) = ∑ i, w i • L22phi x (f i) := by
  have : (fun y => ∑ i, w i * f i y) = ∑ i, w i • f i := by
    funext y; simp [Finset.sum_apply]
  rw [this, map_sum]
  simp only [map_smul]

open BartlettNN.FatNet in
lemma L22_norm_combo {X : Type*} {m : ℕ} (x : Fin m → X) {F : Set (X → ℝ)} {M A : ℝ}
    (hM : 0 ≤ M) (hF : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (-M / 2) (M / 2)) {h : X → ℝ}
    (hh : h ∈ combos F A) : ‖L22phi x h‖ ≤ A * (M / 2) := by
  obtain ⟨n, w, f, hf, hw, rfl⟩ := hh
  rw [L22_phi_combo]
  calc ‖∑ i, w i • L22phi x (f i)‖ ≤ ∑ i, ‖w i • L22phi x (f i)‖ := norm_sum_le _ _
    _ ≤ ∑ i, |w i| * (M / 2) := by
        apply Finset.sum_le_sum; intro i _
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (L22_norm_phi_le x (f i) (M / 2) (by linarith)
          (fun y => abs_le.2 ⟨by linarith [(hF _ (hf i) y).1], (hF _ (hf i) y).2⟩)) (abs_nonneg _)
    _ = (∑ i, |w i|) * (M / 2) := by rw [Finset.sum_mul]
    _ ≤ A * (M / 2) := mul_le_mul_of_nonneg_right hw (by linarith)

open Classical in
noncomputable def L22G {X : Type*} (M A : ℝ) (T : Finset (X → ℝ)) : Finset (X → ℝ) :=
  insert 0 ((T.image (L22clip M)).image (fun t => A • t) ∪
    (T.image (L22clip M)).image (fun t => (-A) • t))

open Classical in
lemma L22G_card {X : Type*} (M A : ℝ) (T : Finset (X → ℝ)) {N : ℕ} (hTc : T.card ≤ N) :
    (L22G M A T).card ≤ 2 * N + 1 := by
  unfold L22G
  have h3 : ((T.image (L22clip M)).image (fun t => A • t)).card ≤ N :=
    (Finset.card_image_le.trans Finset.card_image_le).trans hTc
  have h4 : ((T.image (L22clip M)).image (fun t => (-A) • t)).card ≤ N :=
    (Finset.card_image_le.trans Finset.card_image_le).trans hTc
  have h2 := (Finset.card_union_le ((T.image (L22clip M)).image (fun t => A • t))
    ((T.image (L22clip M)).image (fun t => (-A) • t))).trans (add_le_add h3 h4)
  refine (Finset.card_insert_le _ _).trans ?_
  omega

lemma L22_scal {A w : ℝ} (hA : 0 < A) : |w| / A * (if 0 ≤ w then A else -A) = w := by
  split_ifs with hw
  · rw [abs_of_nonneg hw, div_mul_cancel₀ _ hA.ne']
  · rw [abs_of_neg (not_le.mp hw), div_mul_eq_mul_div, neg_mul_neg, mul_div_assoc,
      div_self hA.ne', mul_one]

open Classical BartlettNN.FatNet in
lemma L22_big {X : Type*} {F : Set (X → ℝ)} {M A γ : ℝ} {m N : ℕ} (x : Fin m → X)
    (hF : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (-M / 2) (M / 2)) (hM : 0 ≤ M) (hA : 0 < A)
    (hγ : 0 < γ) (T : Finset (X → ℝ)) (hTc : T.card ≤ N)
    (hT : ∀ f ∈ F, ∃ t ∈ T, dL2 x t f < γ / (2 * A))
    (k : ℕ) (hk : 0 < k) (hkb : A ^ 2 * M ^ 2 < k * γ ^ 2) :
    ∃ C : Finset (X → ℝ), C.card ≤ (2 * N + 1) ^ k ∧
      ∀ h ∈ combos F A, ∃ c ∈ C, dL2 x c h < γ := by
  refine ⟨(Fintype.piFinset fun _ : Fin k => L22G M A T).image
    (fun u => (1 / (k : ℝ)) • ∑ j, u j), ?_, ?_⟩
  · calc _ ≤ (Fintype.piFinset fun _ : Fin k => L22G M A T).card := Finset.card_image_le
      _ = (L22G M A T).card ^ k := by rw [Fintype.card_piFinset]; simp
      _ ≤ _ := Nat.pow_le_pow_left (L22G_card M A T hTc) k
  intro h hh
  obtain ⟨n, w, f, hf, hw, rfl⟩ := hh
  choose t ht hd using fun i => hT (f i) (hf i)
  obtain ⟨g, hg⟩ : ∃ g : Option (Fin n) → X → ℝ, g = fun a => Option.elim a 0
      (fun i => (if 0 ≤ w i then A else -A) • L22clip M (t i)) := ⟨_, rfl⟩
  obtain ⟨lam, hlam⟩ : ∃ lam : Option (Fin n) → ℝ, lam = fun a => Option.elim a
      (1 - ∑ i, |w i| / A) (fun i => |w i| / A) := ⟨_, rfl⟩
  have hgn : g none = 0 := by rw [hg]; rfl
  have hgs : ∀ i, g (some i) = (if 0 ≤ w i then A else -A) • L22clip M (t i) := by
    intro i; rw [hg]; rfl
  have hln : lam none = 1 - ∑ i, |w i| / A := by rw [hlam]; rfl
  have hls : ∀ i, lam (some i) = |w i| / A := by intro i; rw [hlam]; rfl
  have h0 : ∀ a, 0 ≤ lam a := by
    intro a; cases a with
    | none =>
      rw [hln, ← Finset.sum_div, sub_nonneg]
      exact (div_le_one hA).2 hw
    | some i => rw [hls]; exact div_nonneg (abs_nonneg _) hA.le
  have h1 : ∑ a, lam a = 1 := by
    rw [Fintype.sum_option, hln]; simp only [hls]; ring
  have hgG : ∀ a, g a ∈ L22G M A T := by
    intro a; cases a with
    | none => rw [hgn]; exact Finset.mem_insert_self _ _
    | some i =>
      rw [hgs]
      unfold L22G
      apply Finset.mem_insert_of_mem
      split_ifs
      · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ (ht i)))
      · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ (ht i)))
  set B := (A * (M / 2)) ^ 2 with hB
  have hBv : ∀ a, ‖L22phi x (g a)‖ ^ 2 ≤ B := by
    intro a; cases a with
    | none => rw [hgn, map_zero, norm_zero, hB]; nlinarith [sq_nonneg (A * (M / 2))]
    | some i =>
      apply L22_norm_phi_sq_le
      intro y
      rw [hgs, Pi.smul_apply, smul_eq_mul, abs_mul]
      have hs : |(if 0 ≤ w i then A else -A)| = A := by
        split_ifs <;> simp [abs_of_pos hA]
      rw [hs]
      exact mul_le_mul_of_nonneg_left (L22_clip_bound hM) hA.le
  obtain ⟨c, hc⟩ : ∃ c, c = ∑ b, lam b • L22phi x (g b) := ⟨_, rfl⟩
  have hcw : c = ∑ i, w i • L22phi x (L22clip M (t i)) := by
    rw [hc, Fintype.sum_option, hgn, map_zero, smul_zero, zero_add]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hls, hgs, map_smul, smul_smul, L22_scal hA]
  obtain ⟨s, hs⟩ := L22_maurey lam (fun a => L22phi x (g a)) h0 h1 B hBv c hc k
  refine ⟨(1 / (k : ℝ)) • ∑ j, g (s j),
    Finset.mem_image.2 ⟨fun j => g (s j), Fintype.mem_piFinset.2 (fun j => hgG (s j)), rfl⟩, ?_⟩
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rw [L22_dL2_eq]
  have hP : ‖L22phi x ((1 / (k : ℝ)) • ∑ j, g (s j)) - c‖ < γ / 2 := by
    have e : L22phi x ((1 / (k : ℝ)) • ∑ j, g (s j)) - c
        = (1 / (k : ℝ)) • (∑ j, L22phi x (g (s j)) - (k : ℝ) • c) := by
      rw [map_smul, map_sum, smul_sub, smul_smul, one_div, inv_mul_cancel₀ hk'.ne', one_smul]
    have hsq : ‖L22phi x ((1 / (k : ℝ)) • ∑ j, g (s j)) - c‖ ^ 2 ≤ B / k := by
      rw [e, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      calc (1 / (k : ℝ)) ^ 2 * ‖∑ j, L22phi x (g (s j)) - (k : ℝ) • c‖ ^ 2
          ≤ (1 / (k : ℝ)) ^ 2 * (k * B) := mul_le_mul_of_nonneg_left hs (by positivity)
        _ = B / k := by field_simp
    have hlt : B / k < (γ / 2) ^ 2 := by
      rw [div_lt_iff₀ hk', hB]; nlinarith
    nlinarith [norm_nonneg (L22phi x ((1 / (k : ℝ)) • ∑ j, g (s j)) - c)]
  have hQ : ‖c - L22phi x (fun y => ∑ i, w i * f i y)‖ ≤ γ / 2 := by
    rw [hcw, L22_phi_combo, ← Finset.sum_sub_distrib]
    calc ‖∑ i, (w i • L22phi x (L22clip M (t i)) - w i • L22phi x (f i))‖
        ≤ ∑ i, ‖w i • L22phi x (L22clip M (t i)) - w i • L22phi x (f i)‖ := norm_sum_le _ _
      _ ≤ ∑ i, |w i| * (γ / (2 * A)) := by
          apply Finset.sum_le_sum; intro i _
          rw [← smul_sub, norm_smul, Real.norm_eq_abs, ← L22_dL2_eq]
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          exact ((L22_dL2_clip x M (t i) (f i) (hF _ (hf i))).trans_lt (hd i)).le
      _ = (∑ i, |w i|) * (γ / (2 * A)) := by rw [Finset.sum_mul]
      _ ≤ A * (γ / (2 * A)) := mul_le_mul_of_nonneg_right hw (by positivity)
      _ = γ / 2 := by field_simp
  calc _ ≤ ‖L22phi x ((1 / (k : ℝ)) • ∑ j, g (s j)) - c‖
        + ‖c - L22phi x (fun y => ∑ i, w i * f i y)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < γ / 2 + γ / 2 := by linarith
    _ = γ := by ring

open BartlettNN.FatNet in
theorem L22_core {X : Type*} (F : Set (X → ℝ)) (M A γ : ℝ) (m : ℕ)
    (hFne : F.Nonempty) (hF : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (-M / 2) (M / 2))
    (hA : 0 < A) (hγ : 0 < γ) :
    ∀ N : ℕ, N2 F (γ / (2 * A)) m ≤ N →
      ∃ K : ℕ, N2 (combos F A) γ m = K ∧
        Real.logb 2 K ≤ 2 * M ^ 2 * A ^ 2 / γ ^ 2 * Real.logb 2 (2 * N + 1) := by
  intro N hN
  have hL : 0 ≤ Real.logb 2 (2 * (N : ℝ) + 1) := by
    apply Real.logb_nonneg one_lt_two
    have : (0 : ℝ) ≤ N := N.cast_nonneg
    linarith
  have hRHS : 0 ≤ 2 * M ^ 2 * A ^ 2 / γ ^ 2 * Real.logb 2 (2 * N + 1) :=
    mul_nonneg (by positivity) hL
  have finish : ∀ Bnd : ℕ,
      (∀ x : Fin m → X, BartlettNN.Margin.coverNum (dL2 x) (combos F A) γ ≤ Bnd) →
      Real.logb 2 Bnd ≤ 2 * M ^ 2 * A ^ 2 / γ ^ 2 * Real.logb 2 (2 * N + 1) →
      ∃ K : ℕ, N2 (combos F A) γ m = K ∧
        Real.logb 2 K ≤ 2 * M ^ 2 * A ^ 2 / γ ^ 2 * Real.logb 2 (2 * N + 1) := by
    intro Bnd hB hlog
    have hle : N2 (combos F A) γ m ≤ Bnd := iSup_le hB
    have hne : N2 (combos F A) γ m ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top Bnd) hle
    refine ⟨(N2 (combos F A) γ m).toNat, (ENat.natCast_toNat hne).symm, ?_⟩
    have hKB : (N2 (combos F A) γ m).toNat ≤ Bnd := ENat.toNat_le_of_le_natCast hle
    rcases Nat.eq_zero_or_pos (N2 (combos F A) γ m).toNat with h0 | hpos
    · rw [h0]; simpa using hRHS
    · exact le_trans (Real.logb_le_logb_of_le one_lt_two (by exact_mod_cast hpos)
        (by exact_mod_cast hKB)) hlog
  by_cases hsmall : A * (M / 2) < γ
  · refine finish 1 ?_ (by simpa using hRHS)
    intro x
    unfold BartlettNN.Margin.coverNum
    refine le_trans (iInf₂_le ({0} : Finset (X → ℝ)) ?_) (by simp)
    intro h hh
    refine ⟨0, Finset.mem_singleton_self _, ?_⟩
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simpa [dL2] using hγ
    · obtain ⟨f0, hf0⟩ := hFne
      have hM : 0 ≤ M := by
        have := hF f0 hf0 (x ⟨0, hm⟩)
        simp only [Set.mem_Icc] at this
        linarith [this.1, this.2]
      rw [L22_dL2_eq, map_zero, zero_sub, norm_neg]
      exact lt_of_le_of_lt (L22_norm_combo x hM hF hh) hsmall
  · push_neg at hsmall
    have hM : 0 < M := by nlinarith
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t = A ^ 2 * M ^ 2 / γ ^ 2 := ⟨_, rfl⟩
    have ht4 : 4 ≤ t := by
      rw [ht, le_div_iff₀ (by positivity)]; nlinarith
    have hkt : ((⌊t⌋₊ + 1 : ℕ) : ℝ) ≤ t + 1 := by
      push_cast; linarith [Nat.floor_le (by linarith : 0 ≤ t)]
    have htk : t < ((⌊t⌋₊ + 1 : ℕ) : ℝ) := by
      push_cast; exact Nat.lt_floor_add_one t
    have hkb : A ^ 2 * M ^ 2 < ((⌊t⌋₊ + 1 : ℕ) : ℝ) * γ ^ 2 := by
      have e : t * γ ^ 2 = A ^ 2 * M ^ 2 := by rw [ht]; field_simp
      have := mul_lt_mul_of_pos_right htk (pow_pos hγ 2)
      rw [e] at this; exact this
    refine finish ((2 * N + 1) ^ (⌊t⌋₊ + 1)) ?_ ?_
    · intro x
      obtain ⟨T, hTc, hT⟩ := L22_cover_of_N2 hN x
      obtain ⟨C, hCc, hC⟩ := L22_big x hF hM.le hA hγ T hTc hT (⌊t⌋₊ + 1) (by omega) hkb
      unfold BartlettNN.Margin.coverNum
      exact le_trans (iInf₂_le C hC) (by exact_mod_cast hCc)
    · push_cast
      rw [Real.logb_pow]
      have h2t : 2 * M ^ 2 * A ^ 2 / γ ^ 2 = 2 * t := by rw [ht]; ring
      rw [h2t]
      apply mul_le_mul_of_nonneg_right _ hL
      push_cast at hkt ⊢
      linarith

theorem solution :
    ∀ {X : Type} (F : Set (X → ℝ)) (M A γ : ℝ) (m : ℕ),
      F.Nonempty →
      (∀ f ∈ F, ∀ x, f x ∈ Set.Icc (-M / 2) (M / 2)) →
      0 < M → 0 < A → 0 < γ → 1 ≤ m →
      ∀ N : ℕ, BartlettNN.FatNet.N2 F (γ / (2 * A)) m ≤ N →
        ∃ K : ℕ, BartlettNN.FatNet.N2 (BartlettNN.FatNet.combos F A) γ m = K ∧
          Real.logb 2 K ≤ (2 * M ^ 2 * A ^ 2 / γ ^ 2) * Real.logb 2 (2 * N + 1) := by
  intro X F M A γ m hFne hF _ hA hγ _ N hN
  exact L22_core F M A γ m hFne hF hA hγ N hN
