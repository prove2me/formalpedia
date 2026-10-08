-- Prove2me | solution 1 for BartlettNN.FatNet.lemma19_l1_covering_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T03:54:33.479073+00:00
-- url     : https://prove2.me/submissions/530ad545-cabe-40d1-acfb-1e5f16f9194e

import Mathlib
import Definitions.Def_BartlettNN_Margin_FatShattering
import Definitions.Def_BartlettNN_FatNet_coverNum

set_option autoImplicit false

namespace BartlettNN.FatNet.L19

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

end BartlettNN.FatNet.L19

open BartlettNN.FatNet in
theorem solution {X : Type*} (F : Set (X → ℝ)) (γ : ℝ) (d : ℕ)
    (hF : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    (hfat : (d : ℕ∞) ≤ BartlettNN.Margin.fat F (4 * γ)) :
    ∀ N : ℕ, N1 F γ d = N → (d : ℝ) / 32 ≤ Real.logb 2 N := by
  intro N hN
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp only [Nat.cast_zero, zero_div]
    rcases Nat.eq_zero_or_pos N with rfl | hNp
    · simp
    · exact Real.logb_nonneg one_lt_two (by exact_mod_cast hNp)
  obtain ⟨x, r, hr⟩ := L19.exists_shattered_of_le_fat hd hfat
  obtain ⟨T, hT, hTc⟩ := L19.exists_cover hN x
  have hc := L19.main_count hd x r hr T hT
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
