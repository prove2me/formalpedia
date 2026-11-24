-- Prove2me | solution 1 for Formalism.SA.P.card_box_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:02:34.697353+00:00
-- url     : https://prove2.me/submissions/59b386f3-8fb6-4359-9a83-957cd5a1b948

import Definitions.Def_Formalism_LatticeRigidity_StatementC
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_SqrtAbsNormLeProd
import Theorems.Thm_Formalism_SA_P_sqrt_absNorm_le_prod
import Theorems.Thm_Formalism_SA_P_absNorm_pos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.SA.P
open NumberField Finset
variable {E : Type} [Field E] [NumberField E] [NumberField.IsTotallyComplex E]
private theorem absNorm_le_prod_infinitePlace_sq (b : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hb : b ≠ 0)
    (l : E) (hl : l ∈ b) (hl0 : l ≠ 0) :
    (FractionalIdeal.absNorm b : ℝ) ≤ ∏ w : InfinitePlace E, w l ^ 2 := by
  have h := sqrt_absNorm_le_prod b hb l hl hl0
  have hN' : (0 : ℝ) ≤ (FractionalIdeal.absNorm b : ℝ) := by
    exact_mod_cast FractionalIdeal.absNorm_nonneg b
  rw [Finset.prod_pow, ← Real.sq_sqrt hN']
  exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
private theorem floor_mem_Icc_neg_ceil_ceil (x s : ℝ) (h : |x| < s) : ⌊x⌋ ∈ Finset.Icc (-⌈s⌉) ⌈s⌉ := by
  rw [Finset.mem_Icc]
  have h1 := abs_lt.mp h
  have h2 : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
  have h3 : x < ⌊x⌋ + 1 := Int.lt_floor_add_one x
  have h4 : s ≤ ⌈s⌉ := Int.le_ceil s
  have h5 : (⌊x⌋ : ℝ) < ⌈s⌉ := by linarith
  have h6 : ((-⌈s⌉ - 1 : ℤ) : ℝ) < ⌊x⌋ := by push_cast; linarith
  have h5' : ⌊x⌋ < ⌈s⌉ := by exact_mod_cast h5
  have h6' : -⌈s⌉ - 1 < ⌊x⌋ := by exact_mod_cast h6
  constructor <;> omega
private theorem card_Icc_neg_self_eq (m : ℤ) (hm : 0 ≤ m) :
    ((Finset.Icc (-m) m).card : ℝ) = 2 * (m : ℝ) + 1 := by
  rw [Int.card_Icc, show m + 1 - -m = 2 * m + 1 by ring]
  have h0 : (0 : ℤ) ≤ 2 * m + 1 := by omega
  rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]
  push_cast
  ring
end Formalism.SA.P
end

set_option autoImplicit false
open Formalism Formalism.SA Formalism.SA.P
open NumberField Finset
variable {E : Type} [Field E] [NumberField E] [NumberField.IsTotallyComplex E]
namespace Formalism.SA.P
theorem _root_.solution (b : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hb : b ≠ 0)
    (ρ : InfinitePlace E → ℝ) (hρ : ∀ w, 0 < ρ w) (P : Finset E)
    (hP : ∀ l ∈ P, l ∈ b ∧ l ≠ 0 ∧ ∀ w, w l < ρ w) :
    (P.card : ℝ) ≤ (100 : ℝ) ^ Fintype.card (InfinitePlace E) * (∏ w, ρ w ^ 2) /
      (FractionalIdeal.absNorm b : ℝ) := by
  classical
  set d := Fintype.card (InfinitePlace E) with hd
  set N : ℝ := (FractionalIdeal.absNorm b : ℝ) with hNdef
  set R : ℝ := ∏ w, ρ w ^ 2 with hRdef
  have hN : 0 < N := absNorm_pos b hb
  have hR : 0 < R := Finset.prod_pos fun w _ => by have := hρ w; positivity
  have hd1 : 0 < d := Fintype.card_pos
  by_cases hX : N ≤ 2 ^ d * R
  swap
  · rcases P.eq_empty_or_nonempty with h | ⟨l, hlP⟩
    · rw [h, Finset.card_empty, Nat.cast_zero]; positivity
    · exfalso
      obtain ⟨hlb, hl0, hlt⟩ := hP l hlP
      apply hX
      have h1 := absNorm_le_prod_infinitePlace_sq b hb l hlb hl0
      have h2 : ∏ w : InfinitePlace E, w l ^ 2 ≤ ∏ w, ρ w ^ 2 :=
        Finset.prod_le_prod (fun w _ => by positivity)
          (fun w _ => pow_le_pow_left₀ (NumberField.InfinitePlace.pos_iff.mpr hl0).le (hlt w).le 2)
      have h3 : (1 : ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
      nlinarith

  set X : ℝ := 2 ^ d * R / N with hXdef
  have hX1 : 1 ≤ X := by rw [hXdef, le_div_iff₀ hN]; linarith
  set s : ℝ := X ^ ((1 : ℝ) / (2 * d)) with hsdef
  have hs1 : 1 ≤ s := Real.one_le_rpow hX1 (by positivity)
  have hs0 : 0 < s := by linarith
  have hsX : s ^ (2 * d) = X := by
    rw [hsdef, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    have : (1 : ℝ) / (2 * d) * ((2 * d : ℕ) : ℝ) = 1 := by
      push_cast
      have : (0 : ℝ) < d := by exact_mod_cast hd1
      field_simp
    rw [this, Real.rpow_one]
  set m : ℤ := ⌈s⌉ with hmdef
  have hm0 : 0 ≤ m := by
    have : (0 : ℝ) < ⌈s⌉ := lt_of_lt_of_le hs0 (Int.le_ceil s)
    have : (0 : ℤ) < ⌈s⌉ := by exact_mod_cast this
    omega
  let f : E → InfinitePlace E → ℤ × ℤ := fun l w =>
    (⌊(w.embedding l).re / (ρ w / s)⌋, ⌊(w.embedding l).im / (ρ w / s)⌋)
  let T : Finset (InfinitePlace E → ℤ × ℤ) :=
    Fintype.piFinset fun _ => (Finset.Icc (-m) m) ×ˢ (Finset.Icc (-m) m)
  have hmaps : Set.MapsTo f ↑P ↑T := by
    intro l hlP
    obtain ⟨_, _, hlt⟩ := hP l (Finset.mem_coe.mp hlP)
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro w
    have hδ : 0 < ρ w / s := div_pos (hρ w) hs0
    have hz : ‖w.embedding l‖ < ρ w := by
      rw [NumberField.InfinitePlace.norm_embedding_eq]; exact hlt w
    have key : ∀ y : ℝ, |y| ≤ ‖w.embedding l‖ → |y / (ρ w / s)| < s := by
      intro y hy
      rw [abs_div, abs_of_pos hδ, div_lt_iff₀ hδ]
      have : s * (ρ w / s) = ρ w := by field_simp
      rw [this]; linarith
    rw [Finset.mem_product]
    exact ⟨floor_mem_Icc_neg_ceil_ceil _ _ (key _ (Complex.abs_re_le_norm _)),
      floor_mem_Icc_neg_ceil_ceil _ _ (key _ (Complex.abs_im_le_norm _))⟩
  have hinj : Set.InjOn f ↑P := by
    intro l hlP l' hlP' hfl
    obtain ⟨hlb, hl0, _⟩ := hP l (Finset.mem_coe.mp hlP)
    obtain ⟨hlb', hl0', _⟩ := hP l' (Finset.mem_coe.mp hlP')
    by_contra hne
    have hsub0 : l - l' ≠ 0 := sub_ne_zero.mpr hne
    have hsubb : l - l' ∈ b := by
      have := Submodule.sub_mem (b : Submodule (𝓞 E) E) (FractionalIdeal.mem_coe.mpr hlb)
        (FractionalIdeal.mem_coe.mpr hlb')
      exact FractionalIdeal.mem_coe.mp this
    have hlow := absNorm_le_prod_infinitePlace_sq b hb (l - l') hsubb hsub0
    have hsmall : ∀ w, w (l - l') ^ 2 < 2 * (ρ w / s) ^ 2 := by
      intro w
      have hδ : 0 < ρ w / s := div_pos (hρ w) hs0
      have hfw := congrFun hfl w
      simp only [f, Prod.mk.injEq] at hfw
      have hre := Int.abs_sub_lt_one_of_floor_eq_floor hfw.1
      have him := Int.abs_sub_lt_one_of_floor_eq_floor hfw.2
      rw [← sub_div, abs_div, abs_of_pos hδ, div_lt_one hδ] at hre him
      rw [← NumberField.InfinitePlace.norm_embedding_eq, map_sub, Complex.sq_norm,
        Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
      have h1 := abs_lt.mp hre
      have h2 := abs_lt.mp him
      nlinarith
    have hprod : ∏ w : InfinitePlace E, (2 * (ρ w / s) ^ 2) = N := by
      have e1 : ∏ w : InfinitePlace E, (2 * (ρ w / s) ^ 2) = 2 ^ d * R / s ^ (2 * d) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← hd]
        simp only [div_pow]
        rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, ← hd, ← hRdef, ← pow_mul,
          mul_comm 2 d, mul_div_assoc]
      rw [e1, hsX, hXdef]
      field_simp
    have hlt : ∏ w : InfinitePlace E, w (l - l') ^ 2 < ∏ w : InfinitePlace E, (2 * (ρ w / s) ^ 2) :=
      Finset.prod_lt_prod_of_nonempty
        (fun w _ => by have := (NumberField.InfinitePlace.pos_iff (w := w)).mpr hsub0; positivity)
        (fun w _ => hsmall w) Finset.univ_nonempty
    rw [hprod] at hlt
    linarith
  have hcard := Finset.card_le_card_of_injOn f hmaps hinj
  have hT : (T.card : ℝ) = ((2 * (m : ℝ) + 1) ^ 2) ^ d := by
    simp only [T]
    rw [Fintype.card_piFinset]
    push_cast
    simp only [Finset.card_product, Nat.cast_mul, card_Icc_neg_self_eq m hm0]
    rw [Finset.prod_const, Finset.card_univ, ← hd, sq]
  have hm1 : (m : ℝ) < s + 1 := Int.ceil_lt_add_one s
  have h5 : 2 * (m : ℝ) + 1 ≤ 5 * s := by linarith
  have hm0' : (0 : ℝ) ≤ m := by exact_mod_cast hm0
  calc (P.card : ℝ) ≤ T.card := by exact_mod_cast hcard
    _ = ((2 * (m : ℝ) + 1) ^ 2) ^ d := hT
    _ ≤ ((5 * s) ^ 2) ^ d := by gcongr
    _ = 25 ^ d * s ^ (2 * d) := by rw [mul_pow, mul_pow, pow_mul]; norm_num
    _ = 50 ^ d * R / N := by
        rw [hsX, hXdef, show (50 : ℝ) = 25 * 2 by norm_num, mul_pow]; ring
    _ ≤ 100 ^ d * R / N := by
        gcongr
        norm_num
end Formalism.SA.P
