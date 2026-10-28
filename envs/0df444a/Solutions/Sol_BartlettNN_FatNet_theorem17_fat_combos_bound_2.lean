-- Prove2me | solution 2 for BartlettNN.FatNet.theorem17_fat_combos_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T07:31:21.214077+00:00
-- url     : https://prove2.me/submissions/5dd71d0a-7c0e-4611-bff8-99e697e0e351

import Mathlib
import Definitions.Def_BartlettNN_Margin_FatShattering
import Definitions.Def_BartlettNN_FatNet_coverNum
import Definitions.Def_BartlettNN_FatNet_combos
import Theorems.Thm_BartlettNN_FatNet_lemma20_l2_covering_upper_bound

-- carved verbatim out of submission 35503c7d-491b-46b3-9643-8ef49b13d218, lines 1817-1883

section
set_option autoImplicit false
open BartlettNN
open BartlettNN.FatNet
open BartlettNN.Margin BartlettNN.FatNet Finset

lemma restrict_shatters {X : Type*} {H : Set (X → ℝ)} {γ : ℝ} {m k : ℕ} {x : Fin m → X}
    (hx : GammaShatters H γ x) (hk : k ≤ m) : GammaShatters H γ (x ∘ Fin.castLE hk) := by
  obtain ⟨r, hr⟩ := hx
  refine ⟨r ∘ Fin.castLE hk, fun b => ?_⟩
  obtain ⟨h, hH, hh⟩ := hr (fun j => if hj : (j : ℕ) < k then b ⟨j, hj⟩ else true)
  refine ⟨h, hH, fun i => ?_⟩
  have := hh (Fin.castLE hk i)
  simpa [Fin.castLE, i.isLt] using this

lemma exists_shattered_of_le_fat {X : Type*} {F : Set (X → ℝ)} {γ : ℝ} {d : ℕ} (hd : 0 < d)
    (h : (d : ℕ∞) ≤ fat F γ) : ∃ x : Fin d → X, GammaShatters F γ x := by
  have hlt : ((d - 1 : ℕ) : ℕ∞) < fat F γ := lt_of_lt_of_le (Nat.cast_lt.mpr (by omega)) h
  unfold fat at hlt
  obtain ⟨m, hm⟩ := lt_iSup_iff.1 hlt
  obtain ⟨x, hx⟩ := lt_iSup_iff.1 hm
  obtain ⟨hs, hms⟩ := lt_iSup_iff.1 hx
  have : d - 1 < m := by exact_mod_cast hms
  exact ⟨x ∘ Fin.castLE (by omega), restrict_shatters hs (by omega)⟩

end

section
set_option autoImplicit false
open Classical

def T (K : ℕ) : ℕ → ℕ
  | 0 => 1
  | r+1 => 2 * K^r

end

section
set_option autoImplicit false
open BartlettNN
open BartlettNN.FatNet
open BartlettNN.Margin BartlettNN.FatNet Finset

lemma exists_cover {X : Type*} {F : Set (X → ℝ)} {γ : ℝ} {d N : ℕ} (hN : N1 F γ d = N)
    (x : Fin d → X) :
    ∃ T : Finset (X → ℝ), (∀ f ∈ F, ∃ g ∈ T, dL1 x g f < γ) ∧ T.card ≤ N := by
  have hle : coverNum (dL1 x) F γ ≤ N := by
    rw [← hN]; exact le_iSup (fun x => coverNum (dL1 x) F γ) x
  by_contra hne
  push Not at hne
  have h2 : ((N + 1 : ℕ) : ℕ∞) ≤ coverNum (dL1 x) F γ := by
    unfold coverNum
    exact le_iInf₂ fun T hT => Nat.cast_le.mpr (Nat.succ_le_of_lt (hne T hT))
  have h3 := h2.trans hle
  norm_cast at h3
  omega

lemma ham_bound {X : Type*} {d : ℕ} (hd : 0 < d) (x : Fin d → X) (r : Fin d → ℝ)
    (b : Fin d → Bool) (h g : X → ℝ) {γ : ℝ}
    (hsep : ∀ i, 4 * γ ≤ (h (x i) - r i) * pm (b i)) (hdist : dL1 x g h < γ) :
    4 * (univ.filter fun i => b i ≠ decide (r i ≤ g (x i))).card < d := by
  set S := univ.filter fun i => b i ≠ decide (r i ≤ g (x i)) with hSdef
  have hpt : ∀ i ∈ S, 4 * γ ≤ |g (x i) - h (x i)| := by
    intro i hi
    simp only [S, mem_filter, mem_univ, true_and] at hi
    have hs := hsep i
    by_cases hrg : r i ≤ g (x i)
    · have hbf : b i = false := by
        cases hb : b i
        · rfl
        · rw [hb] at hi; simp [hrg] at hi
      rw [hbf] at hs
      simp only [pm] at hs
      norm_num at hs
      rw [le_abs]; left; linarith
    · have hbt : b i = true := by
        cases hb : b i
        · rw [hb] at hi; simp [hrg] at hi
        · rfl
      rw [hbt] at hs
      simp only [pm] at hs
      norm_num at hs
      push Not at hrg
      rw [le_abs]; right; linarith
  have hsum : (S.card : ℝ) * (4 * γ) ≤ ∑ i, |g (x i) - h (x i)| := by
    calc (S.card : ℝ) * (4 * γ) = ∑ i ∈ S, 4 * γ := by rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ S, |g (x i) - h (x i)| := sum_le_sum hpt
      _ ≤ ∑ i, |g (x i) - h (x i)| :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => abs_nonneg _)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hγ : 0 < γ := lt_of_le_of_lt (by unfold dL1; positivity) hdist
  unfold dL1 at hdist
  have hS : ∑ i, |g (x i) - h (x i)| < γ * d := by
    rw [one_div, ← div_eq_inv_mul, div_lt_iff₀ hdpos] at hdist; exact hdist
  have hlt : (S.card : ℝ) * 4 < d := by
    have h1 := hsum.trans_lt hS
    by_contra hc; push Not at hc
    nlinarith
  have : ((4 * S.card : ℕ) : ℝ) < (d : ℝ) := by push_cast; linarith
  exact_mod_cast this

lemma weight_ge_one {H d : ℕ} (h : 4 * H ≤ d) : (1 : ℝ) ≤ (4/3 : ℝ)^d * (81/256)^H := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add, pow_mul, mul_right_comm, ← mul_pow]
  have h1 : ((4/3:ℝ)^4 * (81/256)) = 1 := by norm_num
  rw [h1, one_pow, one_mul]
  exact one_le_pow₀ (by norm_num)

lemma prod_weight {d : ℕ} (b c : Fin d → Bool) (a : ℝ) :
    ∏ i, (if b i = c i then (1:ℝ) else a) = a ^ (univ.filter fun i => b i ≠ c i).card := by
  rw [Finset.prod_ite]
  simp

lemma sum_weight {d : ℕ} (c : Fin d → Bool) (a : ℝ) :
    ∑ b : Fin d → Bool, ∏ i, (if b i = c i then (1:ℝ) else a) = (1 + a)^d := by
  rw [← Fintype.prod_sum (fun i (j : Bool) => if j = c i then (1:ℝ) else a)]
  have h1 : ∀ i, ∑ j : Bool, (if j = c i then (1:ℝ) else a) = 1 + a := by
    intro i; cases c i <;> simp [add_comm]
  rw [Finset.prod_congr rfl (fun i _ => h1 i)]
  simp

lemma main_count {X : Type*} {F : Set (X → ℝ)} {γ : ℝ} {d : ℕ} (hd : 0 < d) (x : Fin d → X)
    (r : Fin d → ℝ) (hb : ∀ b : Fin d → Bool, ∃ h ∈ F, ∀ i, 4 * γ ≤ (h (x i) - r i) * pm (b i))
    (T : Finset (X → ℝ)) (hT : ∀ f ∈ F, ∃ g ∈ T, dL1 x g f < γ) :
    (2:ℝ)^d ≤ T.card * (337/192)^d := by
  let c : (X → ℝ) → Fin d → Bool := fun g i => decide (r i ≤ g (x i))
  let w : (Fin d → Bool) → (X → ℝ) → ℝ :=
    fun b g => (4/3:ℝ)^d * ∏ i, (if b i = c g i then (1:ℝ) else 81/256)
  have hw0 : ∀ b g, 0 ≤ w b g := fun b g => by
    apply mul_nonneg (by positivity)
    apply prod_nonneg
    intro i _
    split_ifs <;> norm_num
  have key : ∀ b : Fin d → Bool, (1:ℝ) ≤ ∑ g ∈ T, w b g := by
    intro b
    obtain ⟨h, hF, hs⟩ := hb b
    obtain ⟨g, hgT, hg⟩ := hT h hF
    have hH := ham_bound hd x r b h g hs hg
    have h1 : 1 ≤ w b g := by
      show 1 ≤ (4/3:ℝ)^d * ∏ i, (if b i = c g i then (1:ℝ) else 81/256)
      rw [prod_weight]
      exact weight_ge_one hH.le
    exact h1.trans (single_le_sum (fun g _ => hw0 b g) hgT)
  calc (2:ℝ)^d = ∑ b : Fin d → Bool, (1:ℝ) := by simp
    _ ≤ ∑ b : Fin d → Bool, ∑ g ∈ T, w b g := sum_le_sum fun b _ => key b
    _ = ∑ g ∈ T, ∑ b : Fin d → Bool, w b g := sum_comm
    _ = ∑ g ∈ T, (4/3:ℝ)^d * (1 + 81/256)^d := by
        refine sum_congr rfl fun g _ => ?_
        simp only [w]
        rw [← mul_sum, sum_weight]
    _ = T.card * (337/192)^d := by
        rw [sum_const, nsmul_eq_mul, ← mul_pow]; norm_num

end

section
set_option autoImplicit false

open BartlettNN.FatNet in
theorem fatnet_l19 {X : Type*} (F : Set (X → ℝ)) (γ : ℝ) (d : ℕ)
    (hF : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    (hfat : (d : ℕ∞) ≤ BartlettNN.Margin.fat F (4 * γ)) :
    ∀ N : ℕ, N1 F γ d = N → (d : ℝ) / 32 ≤ Real.logb 2 N := by
  intro N hN
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp only [Nat.cast_zero, zero_div]
    rcases Nat.eq_zero_or_pos N with rfl | hNp
    · simp
    · exact Real.logb_nonneg one_lt_two (by exact_mod_cast hNp)
  obtain ⟨x, r, hr⟩ := exists_shattered_of_le_fat hd hfat
  obtain ⟨T, hT, hTc⟩ := exists_cover hN x
  have hc := main_count hd x r hr T hT
  have hTc' : (T.card : ℝ) ≤ N := by exact_mod_cast hTc
  have hc' : (2:ℝ)^d ≤ N * (337/192)^d :=
    hc.trans (mul_le_mul_of_nonneg_right hTc' (by positivity))
  have hNpos : (0:ℝ) < N := by
    by_contra h0
    push Not at h0
    have h00 : (N:ℝ) = 0 := le_antisymm h0 (Nat.cast_nonneg _)
    rw [h00, zero_mul] at hc'
    have : (0:ℝ) < 2^d := by positivity
    linarith
  have h32 : (2:ℝ)^d ≤ (N:ℝ)^32 := by
    have h1 : ((2:ℝ)^d)^32 ≤ ((N:ℝ) * (337/192)^d)^32 :=
      pow_le_pow_left₀ (by positivity) hc' 32
    have h2 : ((337/192:ℝ))^32 ≤ 2^31 := by norm_num
    have h3 : (((337/192:ℝ))^32)^d ≤ ((2:ℝ)^31)^d := pow_le_pow_left₀ (by positivity) h2 d
    have e1 : ((2:ℝ)^d)^32 = 2^d * (2^31)^d := by
      rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1; ring
    have e2 : ((N:ℝ) * (337/192)^d)^32 = (N:ℝ)^32 * ((337/192)^32)^d := by
      rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm d 32]
    rw [e1, e2] at h1
    have h4 : (2:ℝ)^d * (2^31)^d ≤ (N:ℝ)^32 * (2^31)^d :=
      h1.trans (mul_le_mul_of_nonneg_left h3 (by positivity))
    exact le_of_mul_le_mul_right h4 (by positivity)
  rw [Real.le_logb_iff_rpow_le one_lt_two hNpos]
  have h5 : ((2:ℝ) ^ ((d:ℝ)/32))^(32:ℕ) ≤ (N:ℝ)^32 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have h6 : (d:ℝ)/32 * ((32:ℕ):ℝ) = (d:ℕ) := by push_cast; ring
    rw [h6, Real.rpow_natCast]
    exact h32
  exact le_of_pow_le_pow_left₀ (by norm_num) hNpos.le h5

-- ===== copied from Solutions/Sol_pv_dd4c1fa3.lean =====

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
lemma L22_cover_of_N2 {X : Type*} {F : Set (X → ℝ)} {ε : ℝ} {m N : ℕ} (hN : N2 F ε m = N)
    (x : Fin m → X) :
    ∃ T : Finset (X → ℝ), T.card ≤ N ∧ ∀ f ∈ F, ∃ t ∈ T, dL2 x t f < ε := by
  have h1 : BartlettNN.Margin.coverNum (dL2 x) F ε ≤ N := by
    rw [← hN]; exact le_iSup (fun x => BartlettNN.Margin.coverNum (dL2 x) F ε) x
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
theorem fatnet_l22 {X : Type*} (F : Set (X → ℝ)) (M A γ : ℝ) (m : ℕ)
    (hFne : F.Nonempty) (hF : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (-M / 2) (M / 2))
    (hA : 0 < A) (hγ : 0 < γ) :
    ∀ N : ℕ, N2 F (γ / (2 * A)) m = N →
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

-- ===== theorem 17 glue =====

end

section
set_option autoImplicit false
open BartlettNN.Margin BartlettNN.FatNet

lemma combos_abs_le {X : Type*} {F : Set (X → ℝ)} {M A : ℝ} (hM : 0 ≤ M)
    (hF : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (-M / 2) (M / 2)) {h : X → ℝ} (hh : h ∈ combos F A)
    (x : X) : |h x| ≤ A * (M / 2) := by
  obtain ⟨N, w, f, hf, hw, rfl⟩ := hh
  calc |∑ i, w i * f i x| ≤ ∑ i, |w i * f i x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |w i| * (M / 2) := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        exact abs_le.2 ⟨by linarith [(hF _ (hf i) x).1], (hF _ (hf i) x).2⟩
    _ = (∑ i, |w i|) * (M / 2) := by rw [Finset.sum_mul]
    _ ≤ A * (M / 2) := mul_le_mul_of_nonneg_right hw (by linarith)

lemma fat_mono_of {X : Type*} {H H' : Set (X → ℝ)} {γ γ' : ℝ}
    (h : ∀ (m : ℕ) (x : Fin m → X), GammaShatters H γ x → GammaShatters H' γ' x) :
    fat H γ ≤ fat H' γ' := by
  unfold fat
  refine iSup_le fun m => iSup_le fun x => iSup_le fun hx => ?_
  exact le_iSup_of_le m (le_iSup_of_le x (le_iSup_of_le (h m x hx) le_rfl))

lemma gap_of_one_le_fat {X : Type*} {H : Set (X → ℝ)} {γ : ℝ} (h1 : 1 ≤ fat H γ) :
    ∃ h₁ ∈ H, ∃ h₂ ∈ H, ∃ y : X, 2 * γ ≤ h₁ y - h₂ y := by
  by_contra hcon
  push Not at hcon
  have hle : fat H γ ≤ 0 := by
    unfold fat
    refine iSup_le fun m => iSup_le fun x => iSup_le fun hx => ?_
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · exfalso
      obtain ⟨r, hr⟩ := hx
      obtain ⟨g1, hg1, hg1'⟩ := hr (fun _ => true)
      obtain ⟨g2, hg2, hg2'⟩ := hr (fun _ => false)
      have a1 := hg1' ⟨0, hm⟩
      have a2 := hg2' ⟨0, hm⟩
      simp only [pm, if_true, mul_one, Bool.false_eq_true, if_false, mul_neg] at a1 a2
      have := hcon g1 hg1 g2 hg2 (x ⟨0, hm⟩)
      linarith
  have := h1.trans hle
  simp at this

lemma dL1_le_dL2 {X : Type*} {m : ℕ} (x : Fin m → X) (f g : X → ℝ) : dL1 x f g ≤ dL2 x f g := by
  unfold dL1 dL2
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  apply Real.le_sqrt_of_sq_le
  have hcs : (∑ i : Fin m, (1 : ℝ) * |f (x i) - g (x i)|) ^ 2 ≤
      (∑ i : Fin m, (1 : ℝ) ^ 2) * ∑ i : Fin m, |f (x i) - g (x i)| ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, sq_abs] at hcs
  rw [mul_pow]
  have e : (1 / (m : ℝ)) ^ 2 = (1 / m) * (1 / m) := by ring
  rw [e, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hm']
  linarith

noncomputable def resc {X : Type*} (D : ℝ) (h : X → ℝ) : X → ℝ := fun x => (h x + D / 2) / D

lemma resc_shatters {X : Type*} {H : Set (X → ℝ)} {D γ : ℝ} (hD : 0 < D) {m : ℕ} {x : Fin m → X}
    (hx : GammaShatters H γ x) : GammaShatters (resc D '' H) (γ / D) x := by
  obtain ⟨r, hr⟩ := hx
  refine ⟨fun i => (r i + D / 2) / D, fun b => ?_⟩
  obtain ⟨h, hh, hb⟩ := hr b
  refine ⟨resc D h, ⟨h, hh, rfl⟩, fun i => ?_⟩
  have e : (resc D h (x i) - (r i + D / 2) / D) * pm (b i) = ((h (x i) - r i) * pm (b i)) / D := by
    unfold resc; field_simp; ring
  rw [e]
  exact div_le_div_of_nonneg_right (hb i) hD.le

lemma resc_dL1 {X : Type*} {D : ℝ} (hD : 0 < D) {m : ℕ} (x : Fin m → X) (g h : X → ℝ) :
    dL1 x (resc D g) (resc D h) = dL1 x g h / D := by
  unfold dL1 resc
  have e : ∀ i, |(g (x i) + D / 2) / D - (h (x i) + D / 2) / D| = |g (x i) - h (x i)| / D := by
    intro i
    rw [← sub_div, abs_div, abs_of_pos hD]
    congr 2
    ring
  simp only [e, ← Finset.sum_div]
  ring

lemma N1_resc_le {X : Type*} {H : Set (X → ℝ)} {D γ : ℝ} (hD : 0 < D) (m : ℕ) :
    N1 (resc D '' H) (γ / D) m ≤ N2 H γ m := by
  unfold N1 N2
  refine iSup_mono fun x => ?_
  unfold coverNum
  classical
  refine le_iInf fun T => le_iInf fun hT => ?_
  refine iInf_le_of_le (T.image (resc D)) (iInf_le_of_le ?_ ?_)
  · intro f' hf'
    obtain ⟨h, hh, rfl⟩ := hf'
    obtain ⟨g, hg, hgd⟩ := hT h hh
    refine ⟨resc D g, Finset.mem_image_of_mem _ hg, ?_⟩
    rw [resc_dL1 hD]
    exact div_lt_div_of_pos_right ((dL1_le_dL2 x g h).trans_lt hgd) hD
  · exact_mod_cast Finset.card_image_le

lemma resc_mem_Icc {X : Type*} {F : Set (X → ℝ)} {M A : ℝ} (hM : 0 < M) (hA : 0 < A)
    (hF : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (-M / 2) (M / 2)) :
    ∀ f ∈ resc (M * A) '' combos F A, ∀ x, f x ∈ Set.Icc (0 : ℝ) 1 := by
  rintro _ ⟨h, hh, rfl⟩ x
  have hb := combos_abs_le hM.le hF hh x
  have hD : 0 < M * A := mul_pos hM hA
  rw [abs_le] at hb
  unfold resc
  constructor
  · apply div_nonneg _ hD.le
    nlinarith
  · rw [div_le_one hD]
    nlinarith

lemma logb_nat_nonneg (n : ℕ) : 0 ≤ Real.logb 2 (n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact Real.logb_nonneg one_lt_two (by exact_mod_cast hn)

lemma eq6' {X : Type*} (F : Set (X → ℝ)) (M A γ : ℝ) (m d : ℕ)
    (hFne : F.Nonempty) (hF : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (-M / 2) (M / 2))
    (hM : 0 < M) (hA : 0 < A) (hγ : 0 < γ)
    (hm : (m : ℕ∞) ≤ fat (combos F A) (4 * γ)) (hd : fat F (γ / (8 * A)) = d)
    (hmd : 2 + 2 * (d : ℝ) * Real.logb 2 (64 * M * A / γ) ≤ (m : ℝ)) :
    (m : ℝ) ≤ 64 * M ^ 2 * A ^ 2 / γ ^ 2 *
      (3 + (d : ℝ) * Real.logb 2 (8 * Real.exp 1 * m * M * A / γ) *
        Real.logb 2 (36 * m * M ^ 2 * A ^ 2 / γ ^ 2)) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm1
  · simp only [Nat.cast_zero, mul_zero, zero_mul, zero_div, Real.logb_zero, add_zero]
    positivity
  have hD : 0 < M * A := mul_pos hM hA
  -- range: 8γ ≤ MA
  have h8 : 8 * γ ≤ M * A := by
    have h1 : (1 : ℕ∞) ≤ fat (combos F A) (4 * γ) := le_trans (by exact_mod_cast hm1) hm
    obtain ⟨h₁, hh₁, h₂, hh₂, y, hy⟩ := gap_of_one_le_fat h1
    have a1 := abs_le.1 (combos_abs_le hM.le hF hh₁ y)
    have a2 := abs_le.1 (combos_abs_le hM.le hF hh₂ y)
    nlinarith
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  -- lemma 19 on the rescaled class
  have hfat' : (m : ℕ∞) ≤ fat (resc (M * A) '' combos F A) (4 * (γ / (M * A))) := by
    refine hm.trans (fat_mono_of fun n x hx => ?_)
    have := resc_shatters (H := combos F A) hD hx
    rwa [mul_div_assoc] at this
  -- lemma 20
  have hd20 : fat F (γ / (2 * A) / 4) = d := by
    have : γ / (2 * A) / 4 = γ / (8 * A) := by field_simp; ring
    rw [this]; exact hd
  have hmd20 : 2 + 2 * (d : ℝ) * Real.logb 2 (32 * M / (γ / (2 * A))) ≤ (m : ℝ) := by
    have : 32 * M / (γ / (2 * A)) = 64 * M * A / γ := by field_simp; ring
    rw [this]; exact hmd
  obtain ⟨N, hN, hlogN⟩ := BartlettNN.FatNet.lemma20_l2_covering_upper_bound F M (γ / (2 * A)) d m hM (by positivity) hF hd20 hmd20
  -- lemma 22
  obtain ⟨K, hK, hlogK⟩ := fatnet_l22 F M A γ m hFne hF hA hγ N hN
  -- N1 of rescaled ≤ K
  have hle : N1 (resc (M * A) '' combos F A) (γ / (M * A)) m ≤ (K : ℕ∞) :=
    hK ▸ N1_resc_le hD m
  have hne : N1 (resc (M * A) '' combos F A) (γ / (M * A)) m ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.coe_ne_top K) hle
  set N' := (N1 (resc (M * A) '' combos F A) (γ / (M * A)) m).toNat with hN'def
  have hN' : N1 (resc (M * A) '' combos F A) (γ / (M * A)) m = N' := (ENat.coe_toNat hne).symm
  have h19 := fatnet_l19 (resc (M * A) '' combos F A) (γ / (M * A)) m
    (resc_mem_Icc hM hA hF) hfat' N' hN'
  have hN'K : N' ≤ K := by
    have := hN' ▸ hle
    exact_mod_cast this
  have hlogN'K : Real.logb 2 (N' : ℝ) ≤ Real.logb 2 K := by
    rcases Nat.eq_zero_or_pos N' with h0 | hp
    · rw [h0]; simp only [Nat.cast_zero, Real.logb_zero]; exact logb_nat_nonneg K
    · exact Real.logb_le_logb_of_le one_lt_two (by exact_mod_cast hp) (by exact_mod_cast hN'K)
  -- the logarithmic factors
  set L1 := Real.logb 2 (8 * Real.exp 1 * m * M * A / γ) with hL1
  set L2 := Real.logb 2 (36 * m * M ^ 2 * A ^ 2 / γ ^ 2) with hL2
  have he : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hL1n : 0 ≤ L1 := by
    apply Real.logb_nonneg one_lt_two
    rw [le_div_iff₀ hγ]
    have : 8 * Real.exp 1 * m * M * A = 8 * Real.exp 1 * m * (M * A) := by ring
    rw [this]
    have h16 : 16 * γ ≤ 8 * Real.exp 1 * 1 * (M * A) := by nlinarith
    have : 8 * Real.exp 1 * 1 * (M * A) ≤ 8 * Real.exp 1 * m * (M * A) := by
      apply mul_le_mul_of_nonneg_right _ hD.le
      nlinarith
    linarith
  have hL2n : 0 ≤ L2 := by
    apply Real.logb_nonneg one_lt_two
    rw [le_div_iff₀ (by positivity)]
    have : 36 * m * M ^ 2 * A ^ 2 = 36 * m * (M * A) ^ 2 := by ring
    rw [this]
    have h64 : 64 * γ ^ 2 ≤ (M * A) ^ 2 := by nlinarith
    nlinarith
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hprod : 0 ≤ (d : ℝ) * L1 * L2 := by positivity
  have hbound : Real.logb 2 (2 * (N : ℝ) + 1) ≤ 3 + (d : ℝ) * L1 * L2 := by
    rcases Nat.eq_zero_or_pos N with h0 | hNp
    · rw [h0]; simp only [Nat.cast_zero, mul_zero, zero_add, Real.logb_one]; linarith
    have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hNp
    have hlog4 : Real.logb 2 (2 * (N : ℝ) + 1) ≤ 2 + Real.logb 2 N := by
      have h1 : Real.logb 2 (2 * (N : ℝ) + 1) ≤ Real.logb 2 (4 * N) :=
        Real.logb_le_logb_of_le one_lt_two (by positivity) (by linarith)
      have h2 : Real.logb 2 (4 * (N : ℝ)) = 2 + Real.logb 2 N := by
        rw [Real.logb_mul (by norm_num) (by positivity)]
        have : Real.logb 2 (4 : ℝ) = 2 := by
          rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.logb_pow, Real.logb_self_eq_one one_lt_two]
          norm_num
        rw [this]
      linarith
    -- rewrite lemma 20's bound
    have e1 : 4 * Real.exp 1 * m * M / (d * (γ / (2 * A))) = 8 * Real.exp 1 * m * M * A / γ / d := by
      rcases Nat.eq_zero_or_pos d with hd0' | hdp
      · rw [hd0']; simp
      · have : (d : ℝ) ≠ 0 := by positivity
        field_simp
        ring
    have e2 : 9 * m * M ^ 2 / (γ / (2 * A)) ^ 2 = 36 * m * M ^ 2 * A ^ 2 / γ ^ 2 := by
      field_simp; ring
    rw [e1, e2, ← hL2] at hlogN
    rcases Nat.eq_zero_or_pos d with hd0' | hdp
    · rw [hd0'] at hlogN ⊢
      simp only [Nat.cast_zero, zero_mul] at hlogN ⊢
      linarith
    · have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hdp
      have hL1' : Real.logb 2 (8 * Real.exp 1 * m * M * A / γ / d) ≤ L1 := by
        have hpos : 0 < 8 * Real.exp 1 * m * M * A / γ / d := by positivity
        apply Real.logb_le_logb_of_le one_lt_two hpos
        apply div_le_self (by positivity) hdR
      have : (d : ℝ) * Real.logb 2 (8 * Real.exp 1 * m * M * A / γ / d) * L2 ≤ d * L1 * L2 := by
        apply mul_le_mul_of_nonneg_right _ hL2n
        exact mul_le_mul_of_nonneg_left hL1' hd0
      linarith
  have hK0 : 0 ≤ 2 * M ^ 2 * A ^ 2 / γ ^ 2 := by positivity
  have hfin : (m : ℝ) / 32 ≤ 2 * M ^ 2 * A ^ 2 / γ ^ 2 * (3 + (d : ℝ) * L1 * L2) :=
    h19.trans (hlogN'K.trans (hlogK.trans (mul_le_mul_of_nonneg_left hbound hK0)))
  have e : 64 * M ^ 2 * A ^ 2 / γ ^ 2 * (3 + (d : ℝ) * L1 * L2) =
      32 * (2 * M ^ 2 * A ^ 2 / γ ^ 2 * (3 + (d : ℝ) * L1 * L2)) := by ring
  rw [e]
  linarith

lemma scalar_inv (x a b : ℝ) (hx : 1 ≤ x) (ha : 1 ≤ a) (hb : 0 ≤ b)
    (h : x ≤ a * (b + Real.log x) ^ 2) : x ≤ 4 * a * (b + Real.log a + 1) ^ 2 := by
  set s := Real.sqrt x with hs
  set r := Real.sqrt a with hr
  have hs1 : 1 ≤ s := by rw [hs]; exact Real.one_le_sqrt.2 hx
  have hr1 : 1 ≤ r := by rw [hr]; exact Real.one_le_sqrt.2 ha
  have hsx : s ^ 2 = x := Real.sq_sqrt (by linarith)
  have hra : r ^ 2 = a := Real.sq_sqrt (by linarith)
  have hlx : Real.log x = 2 * Real.log s := by
    rw [← hsx, Real.log_pow]; push_cast; ring
  have hla : Real.log a = 2 * Real.log r := by
    rw [← hra, Real.log_pow]; push_cast; ring
  have hls : 0 ≤ Real.log s := Real.log_nonneg hs1
  have hlr : 0 ≤ Real.log r := Real.log_nonneg hr1
  -- s ≤ r (b + log x)
  have h1 : s ≤ r * (b + Real.log x) := by
    have := Real.sqrt_le_sqrt h
    rw [Real.sqrt_mul (by linarith), Real.sqrt_sq (by rw [hlx]; linarith)] at this
    exact this
  -- log s ≤ s/(4r) + log(4r) - 1
  have h2 : Real.log s ≤ s / (4 * r) + Real.log (4 * r) - 1 := by
    have := Real.log_le_sub_one_of_pos (show 0 < s / (4 * r) by positivity)
    rw [Real.log_div (by positivity) (by positivity)] at this
    linarith
  have h4r : Real.log (4 * r) = Real.log 4 + Real.log r := Real.log_mul (by norm_num) (by positivity)
  have hl4 : Real.log 4 < 3 / 2 := by
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    rw [this]; linarith [Real.log_two_lt_d9]
  have key : r * (s / (4 * r)) = s / 4 := by field_simp
  have h3 : s ≤ 2 * r * (b + Real.log a + 1) := by
    rw [hla]
    rw [hlx] at h1
    have h5 : r * (b + 2 * Real.log s) ≤ r * (b + 2 * (s / (4 * r) + Real.log (4 * r) - 1)) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      linarith
    have h6 : r * (b + 2 * (s / (4 * r) + Real.log (4 * r) - 1)) =
        r * b + s / 2 + 2 * r * (Real.log 4 + Real.log r) - 2 * r := by
      rw [h4r, mul_add, mul_add, mul_sub, mul_add, mul_add]
      have : r * (2 * (s / (4 * r))) = s / 2 := by rw [← mul_assoc, mul_comm r 2, mul_assoc, key]; ring
      linarith [this]
    have h7 : s ≤ r * b + s / 2 + 2 * r * (Real.log 4 + Real.log r) - 2 * r := by linarith
    nlinarith
  have h3' : 0 ≤ s := by linarith
  have := pow_le_pow_left₀ h3' h3 2
  rw [hsx] at this
  calc x ≤ (2 * r * (b + Real.log a + 1)) ^ 2 := this
    _ = 4 * r ^ 2 * (b + Real.log a + 1) ^ 2 := by ring
    _ = 4 * a * (b + Real.log a + 1) ^ 2 := by rw [hra]

lemma log_bounds : 0.69 < Real.log 2 ∧ Real.log 2 < 0.7 := by
  constructor
  · have := Real.log_two_gt_d9; norm_num at this ⊢; linarith
  · have := Real.log_two_lt_d9; norm_num at this ⊢; linarith

lemma logb2_eq (y : ℝ) : Real.logb 2 y = Real.log y / Real.log 2 := rfl

lemma caseA (u : ℝ) (d m : ℕ) (hu : 2 ≤ u) (hd : 1 ≤ d)
    (h : (m : ℝ) < 2 + 2 * d * Real.logb 2 (256 * u)) :
    (m : ℝ) ≤ 10 ^ 8 * u ^ 2 * d * (Real.log (u * d)) ^ 2 := by
  obtain ⟨hl1, hl2⟩ := log_bounds
  set ℓ := Real.log 2 with hℓ
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hlu : ℓ ≤ Real.log u := Real.log_le_log (by norm_num) hu
  have hld : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg hdR
  have hL : Real.log (u * d) = Real.log u + Real.log d :=
    Real.log_mul (by positivity) (by positivity)
  set L := Real.log (u * d) with hLdef
  have h256 : Real.logb 2 (256 * u) = 8 + Real.log u / ℓ := by
    rw [logb2_eq, Real.log_mul (by norm_num) (by positivity),
      show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]
    have : ℓ ≠ 0 := by positivity
    field_simp
    push_cast
    ring
  rw [h256] at h
  have hlu0 : 0 ≤ Real.log u := by linarith
  have hdiv : Real.log u / ℓ ≤ 2 * Real.log u := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hLu : Real.log u ≤ L := by linarith
  have hLh : (1 / 2 : ℝ) ≤ L := by linarith
  have hm1 : (m : ℝ) ≤ 2 + 16 * d + 4 * d * Real.log u := by nlinarith
  have hb : 2 + 16 * (d : ℝ) + 4 * d * Real.log u ≤ 80 * d * L ^ 2 := by
    have hL2 : (1 / 4 : ℝ) ≤ L ^ 2 := by nlinarith
    have t1 : (2 : ℝ) ≤ 8 * d * L ^ 2 := by nlinarith
    have t2 : 16 * (d : ℝ) ≤ 64 * d * L ^ 2 := by nlinarith
    have t3 : 4 * (d : ℝ) * Real.log u ≤ 8 * d * L ^ 2 := by
      have : Real.log u ≤ 2 * L ^ 2 := by nlinarith
      nlinarith
    linarith
  have hu2 : (4 : ℝ) ≤ u ^ 2 := by nlinarith
  have hdl : 0 ≤ (d : ℝ) * L ^ 2 := by positivity
  nlinarith

lemma caseB (u : ℝ) (d m : ℕ) (hu : 2 ≤ u) (hd : 1 ≤ d) (hm : 1 ≤ m)
    (h : (m : ℝ) ≤ 1024 * u ^ 2 * (3 + (d : ℝ) * Real.logb 2 (32 * Real.exp 1 * m * u) *
      Real.logb 2 (576 * m * u ^ 2))) :
    (m : ℝ) ≤ 10 ^ 8 * u ^ 2 * d * (Real.log (u * d)) ^ 2 := by
  obtain ⟨hl1, hl2⟩ := log_bounds
  set ℓ := Real.log 2 with hℓ
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hu0 : 0 < u := by linarith
  have hlu : ℓ ≤ Real.log u := Real.log_le_log (by norm_num) hu
  have hld : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg hdR
  have hlm : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hmR
  have hL : Real.log (u * d) = Real.log u + Real.log d :=
    Real.log_mul (by positivity) (by positivity)
  set L := Real.log (u * d) with hLdef
  have he : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have he3 : Real.exp 1 ≤ 3 := by
    have := Real.exp_one_lt_d9; norm_num at this; linarith
  have hmu : 2 ≤ (m : ℝ) * u := by
    have := mul_le_mul hmR hu (by norm_num) (by positivity)
    linarith
  set P := Real.log (32 * Real.exp 1 * m * u) with hP
  set Q := Real.log (576 * m * u ^ 2) with hQ
  have hP0 : 0 ≤ P := by
    apply Real.log_nonneg
    have e : 32 * Real.exp 1 * (m : ℝ) * u = 32 * Real.exp 1 * ((m : ℝ) * u) := by ring
    rw [e]
    have := mul_le_mul he hmu (by norm_num) (by positivity)
    linarith
  have hPQ : P ≤ Q := by
    apply Real.log_le_log (by positivity)
    have h1 : 0 ≤ (m : ℝ) * u := by positivity
    have h2 : 0 ≤ 576 * u - 32 * Real.exp 1 := by linarith
    have h3 := mul_nonneg h1 h2
    have e : (m : ℝ) * u * (576 * u - 32 * Real.exp 1) =
        576 * m * u ^ 2 - 32 * Real.exp 1 * m * u := by ring
    rw [e] at h3
    linarith
  have hQe : Q = Real.log 576 + 2 * Real.log u + Real.log m := by
    rw [hQ, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow]
    push_cast; ring
  have h576 : Real.log 576 ≤ 10 * ℓ := by
    have : Real.log 576 ≤ Real.log (2 ^ 10) := Real.log_le_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at this; push_cast at this; linarith
  have h576' : 6 * ℓ ≤ Real.log 576 := by
    have : Real.log (2 ^ 6) ≤ Real.log 576 := Real.log_le_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at this; push_cast at this; linarith
  have hQl : 2 * ℓ ≤ Q := by rw [hQe]; linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hQ0 : 0 ≤ Q := by linarith
  rw [logb2_eq, logb2_eq, ← hP, ← hQ] at h
  have hPQd : (d : ℝ) * (P / ℓ) * (Q / ℓ) ≤ d * Q ^ 2 / ℓ ^ 2 := by
    have e : (d : ℝ) * (P / ℓ) * (Q / ℓ) = d * (P * Q) / ℓ ^ 2 := by field_simp
    rw [e]
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have := mul_le_mul_of_nonneg_right hPQ hQ0
    rw [sq]; exact this
  have hQ2 : 4 * ℓ ^ 2 ≤ Q ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hQl 2
    linarith [show (2 * ℓ) ^ 2 = 4 * ℓ ^ 2 by ring]
  have hdQ : Q ^ 2 ≤ d * Q ^ 2 := le_mul_of_one_le_left (sq_nonneg _) hdR
  have h3 : (3 : ℝ) ≤ d * Q ^ 2 / ℓ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have : 0 ≤ ℓ ^ 2 := sq_nonneg _
    linarith
  have h4l : (1 : ℝ) ≤ 4 * ℓ ^ 2 := by nlinarith
  have hinv : d * Q ^ 2 / ℓ ^ 2 ≤ 4 * d * Q ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have ht : 0 ≤ (d : ℝ) * Q ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left h4l ht
    have e : (d : ℝ) * Q ^ 2 * (4 * ℓ ^ 2) = 4 * d * Q ^ 2 * ℓ ^ 2 := by ring
    linarith
  have hx : (m : ℝ) ≤ 8192 * u ^ 2 * d * (Real.log 576 + 2 * Real.log u + Real.log m) ^ 2 := by
    rw [← hQe]
    have hu2 : 0 ≤ 1024 * u ^ 2 := by positivity
    have hin : 3 + (d : ℝ) * (P / ℓ) * (Q / ℓ) ≤ 8 * d * Q ^ 2 := by linarith
    have := mul_le_mul_of_nonneg_left hin hu2
    have e : 1024 * u ^ 2 * (8 * (d : ℝ) * Q ^ 2) = 8192 * u ^ 2 * d * Q ^ 2 := by ring
    linarith
  have hb0 : 0 ≤ Real.log 576 + 2 * Real.log u := by linarith
  have hu4 : (4 : ℝ) ≤ u ^ 2 := by nlinarith
  have ha1 : (1 : ℝ) ≤ 8192 * u ^ 2 * d := by
    have := mul_le_mul hu4 hdR (by norm_num) (by positivity)
    linarith
  have hs := scalar_inv (m : ℝ) (8192 * u ^ 2 * d) (Real.log 576 + 2 * Real.log u) hmR ha1 hb0 hx
  have hla : Real.log (8192 * u ^ 2 * d) = 13 * ℓ + 2 * Real.log u + Real.log d := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, show (8192 : ℝ) = 2 ^ 13 by norm_num, Real.log_pow]
    push_cast; ring
  rw [hla] at hs
  have hbase0 : 0 ≤ Real.log 576 + 2 * Real.log u + (13 * ℓ + 2 * Real.log u + Real.log d) + 1 := by
    linarith
  have hbase : Real.log 576 + 2 * Real.log u + (13 * ℓ + 2 * Real.log u + Real.log d) + 1 ≤ 29 * L := by
    linarith
  have hsq := pow_le_pow_left₀ hbase0 hbase 2
  have hpos : 0 ≤ 4 * (8192 * u ^ 2 * (d : ℝ)) := by positivity
  have h5 := mul_le_mul_of_nonneg_left hsq hpos
  have ht : 0 ≤ u ^ 2 * (d : ℝ) * L ^ 2 := by positivity
  have e : 4 * (8192 * u ^ 2 * (d : ℝ)) * (29 * L) ^ 2 = 27557888 * (u ^ 2 * d * L ^ 2) := by ring
  have e2 : (10 : ℝ) ^ 8 * u ^ 2 * d * L ^ 2 = 100000000 * (u ^ 2 * d * L ^ 2) := by ring
  linarith

end

section
set_option autoImplicit false

open BartlettNN.FatNet in
theorem solution :
    ∃ c : ℝ, 0 < c ∧ ∀ {X : Type} (F : Set (X → ℝ)) (M A γ : ℝ) (d : ℕ),
      F.Nonempty → (∀ f ∈ F, ∀ x, f x ∈ Set.Icc (-M / 2) (M / 2)) → 0 < A → 0 < γ →
      BartlettNN.Margin.fat F (γ / (32 * A)) = d → 1 ≤ d →
      ∃ k : ℕ, BartlettNN.Margin.fat (combos F A) γ = k ∧
        (k : ℝ) ≤ c * M ^ 2 * A ^ 2 * d / γ ^ 2 * (Real.log (M * A * d / γ)) ^ 2 := by
  refine ⟨10 ^ 8, by norm_num, ?_⟩
  intro X F M A γ d hFne hF hA hγ hd hd1
  -- M > 0 from d ≥ 1
  have hM : 0 < M := by
    have h1 : (1 : ℕ∞) ≤ BartlettNN.Margin.fat F (γ / (32 * A)) := by rw [hd]; exact_mod_cast hd1
    obtain ⟨f₁, hf₁, f₂, hf₂, y, hy⟩ := gap_of_one_le_fat h1
    have a1 := hF f₁ hf₁ y
    have a2 := hF f₂ hf₂ y
    have : 0 < 2 * (γ / (32 * A)) := by positivity
    linarith [a1.2, a2.1]
  set u := M * A / γ with hu
  have hupos : 0 < u := by positivity
  set E := (10 : ℝ) ^ 8 * u ^ 2 * d * (Real.log (u * d)) ^ 2 with hE
  have hE0 : 0 ≤ E := by positivity
  -- every admissible length is bounded by E
  have hall : ∀ m : ℕ, (m : ℕ∞) ≤ BartlettNN.Margin.fat (combos F A) γ → (m : ℝ) ≤ E := by
    intro m hm
    rcases Nat.eq_zero_or_pos m with rfl | hm1
    · simpa using hE0
    have hu2 : 2 ≤ u := by
      have h1 : (1 : ℕ∞) ≤ BartlettNN.Margin.fat (combos F A) γ := le_trans (by exact_mod_cast hm1) hm
      obtain ⟨h₁, hh₁, h₂, hh₂, y, hy⟩ := gap_of_one_le_fat h1
      have a1 := abs_le.1 (combos_abs_le hM.le hF hh₁ y)
      have a2 := abs_le.1 (combos_abs_le hM.le hF hh₂ y)
      rw [hu, le_div_iff₀ hγ]
      nlinarith
    by_cases hmd : 2 + 2 * (d : ℝ) * Real.logb 2 (64 * M * A / (γ / 4)) ≤ (m : ℝ)
    · have hm4 : (m : ℕ∞) ≤ BartlettNN.Margin.fat (combos F A) (4 * (γ / 4)) := by
        rw [show 4 * (γ / 4) = γ by ring]; exact hm
      have hd4 : BartlettNN.Margin.fat F (γ / 4 / (8 * A)) = d := by
        rw [show γ / 4 / (8 * A) = γ / (32 * A) by field_simp; ring]; exact hd
      have h6 := eq6' F M A (γ / 4) m d hFne hF hM hA (by positivity) hm4 hd4 hmd
      have e1 : 64 * M ^ 2 * A ^ 2 / (γ / 4) ^ 2 = 1024 * u ^ 2 := by
        rw [hu]; field_simp; ring
      have e2 : 8 * Real.exp 1 * m * M * A / (γ / 4) = 32 * Real.exp 1 * m * u := by
        rw [hu]; field_simp; ring
      have e3 : 36 * m * M ^ 2 * A ^ 2 / (γ / 4) ^ 2 = 576 * m * u ^ 2 := by
        rw [hu]; field_simp; ring
      rw [e1, e2, e3] at h6
      exact caseB u d m hu2 hd1 hm1 h6
    · push Not at hmd
      have e : 64 * M * A / (γ / 4) = 256 * u := by rw [hu]; field_simp; ring
      rw [e] at hmd
      exact caseA u d m hu2 hd1 hmd
  have hfin : BartlettNN.Margin.fat (combos F A) γ ≠ ⊤ := by
    intro htop
    have := hall (⌈E⌉₊ + 1) (by rw [htop]; exact le_top)
    have := Nat.le_ceil E
    push_cast at *
    linarith
  refine ⟨(BartlettNN.Margin.fat (combos F A) γ).toNat, (ENat.coe_toNat hfin).symm, ?_⟩
  have hk := hall _ (ENat.coe_toNat hfin).le
  have eE : E = 10 ^ 8 * M ^ 2 * A ^ 2 * d / γ ^ 2 * (Real.log (M * A * d / γ)) ^ 2 := by
    rw [hE, hu]
    have : M * A / γ * d = M * A * d / γ := by ring
    rw [this]
    field_simp
  rw [← eE]
  exact hk

end
