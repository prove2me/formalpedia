-- Prove2me | solution 1 for DQI.Semicircle.lemma_9_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T22:29:48.120626+00:00
-- url     : https://prove2.me/submissions/558fc063-9e9e-4d5a-bc85-8933ecfa9660

import Mathlib
import Definitions.Def_DQI_Semicircle_Setting

namespace Aux_DQI_Semicircle_lemma_9_1

open DQI.Semicircle Polynomial

variable {p : ℕ} [Fact p.Prime] {m : ℕ}

lemma omega_eq (a : ZMod p) : omega a = (ZMod.stdAddChar (N := p) : AddChar (ZMod p) ℂ) a := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  rfl

lemma parseval (h : ZMod p → ℝ) :
    ∑ y : ZMod p, ‖∑ x : ZMod p, omega (y * x) * (h x : ℂ)‖ ^ 2 = (p : ℝ) * ∑ x, (h x) ^ 2 := by
  have hp0 : 0 < ringChar (ZMod p) := by
    rw [ZMod.ringChar_zmod_n]; exact (Fact.out : p.Prime).pos
  have hconj : ∀ a : ZMod p, (starRingEnd ℂ) ((ZMod.stdAddChar (N := p) : AddChar (ZMod p) ℂ) a) =
      (ZMod.stdAddChar (N := p) : AddChar (ZMod p) ℂ) (-a) := by
    intro a
    rw [AddChar.starComp_apply hp0, AddChar.inv_apply]
  have key : ∀ y : ZMod p, ((‖∑ x : ZMod p, omega (y * x) * (h x : ℂ)‖ : ℝ) : ℂ) ^ 2 =
      ∑ x : ZMod p, ∑ x' : ZMod p,
        (ZMod.stdAddChar (N := p) : AddChar (ZMod p) ℂ) (y * (x - x')) * ((h x * h x' : ℝ) : ℂ) := by
    intro y
    rw [← Complex.mul_conj']
    simp only [omega_eq, map_sum, map_mul, hconj, Complex.conj_ofReal]
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro x' _
    rw [show y * (x - x') = y * x + -(y * x') by ring, AddChar.map_add_eq_mul]
    push_cast
    ring
  apply Complex.ofReal_injective
  push_cast
  rw [Finset.sum_congr rfl (fun y _ => key y), Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  rw [Finset.sum_eq_single x]
  · rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar p), sub_self, if_pos rfl, ZMod.card]
    push_cast
    ring
  · intro x' _ hx'
    rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar p),
      if_neg (sub_ne_zero.mpr (Ne.symm hx'))]
    simp
  · intro hx
    exact absurd (Finset.mem_univ x) hx

lemma g_props (F : Fin m → Finset (ZMod p)) (r : ℕ) (hF : ∀ i, (F i).card = r) (hr : 1 ≤ r)
    (hrp : r < p) (i : Fin m) :
    ∑ a, g F i a = 0 ∧ ∑ a, (g F i a) ^ 2 = 1 := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  have hs0 : ∑ a, (fval F i a - fbar F i) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
    unfold fbar
    rw [← mul_assoc, mul_one_div_cancel hp, one_mul, sub_self]
  obtain ⟨a, ha⟩ : (F i).Nonempty := Finset.card_pos.mp (by rw [hF]; omega)
  obtain ⟨b, hb⟩ : ∃ b, b ∉ F i := by
    by_contra hcon
    push_neg at hcon
    have h1 : F i = Finset.univ := Finset.eq_univ_of_forall hcon
    have h2 := congrArg Finset.card h1
    rw [hF, Finset.card_univ, hcard] at h2
    omega
  have hab : a ≠ b := fun h => hb (h ▸ ha)
  have hle : (fval F i a - fbar F i) ^ 2 + (fval F i b - fbar F i) ^ 2 ≤
      ∑ x, (fval F i x - fbar F i) ^ 2 := by
    have := Finset.sum_le_sum_of_subset_of_nonneg (s := {a, b}) (t := Finset.univ)
      (f := fun x => (fval F i x - fbar F i) ^ 2) (Finset.subset_univ _)
      (fun _ _ _ => sq_nonneg _)
    rw [Finset.sum_pair hab] at this
    exact this
  have hfa : fval F i a = 1 := if_pos ha
  have hfb : fval F i b = -1 := if_neg hb
  rw [hfa, hfb] at hle
  have hV : 0 < ∑ x, (fval F i x - fbar F i) ^ 2 := by nlinarith [sq_nonneg (fbar F i)]
  constructor
  · unfold g
    rw [← Finset.sum_div, hs0, zero_div]
  · unfold g
    simp only [div_pow]
    rw [← Finset.sum_div]
    unfold phi
    rw [Real.sq_sqrt hV.le, div_self hV.ne']

lemma gt_zero (F : Fin m → Finset (ZMod p)) (i : Fin m) (hg : ∑ a, g F i a = 0) :
    gt F i 0 = 0 := by
  unfold gt
  have h0 : ∀ x : ZMod p, omega (0 * x) = 1 := by
    intro x
    simp [omega]
  simp only [h0, one_mul]
  rw [← Complex.ofReal_sum, hg]
  simp

lemma gt_parseval (F : Fin m → Finset (ZMod p)) (i : Fin m) (hg2 : ∑ a, (g F i a) ^ 2 = 1) :
    ∑ y, ‖gt F i y‖ ^ 2 = 1 := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have h1 : ∀ y, ‖gt F i y‖ ^ 2 =
      (1 / (p : ℝ)) * ‖∑ x : ZMod p, omega (y * x) * (g F i x : ℂ)‖ ^ 2 := by
    intro y
    unfold gt
    rw [norm_mul, mul_pow]
    congr 1
    rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), div_pow, one_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  rw [Finset.sum_congr rfl (fun y _ => h1 y), ← Finset.mul_sum, parseval, hg2, mul_one, one_div,
    inv_mul_cancel₀ hp]

end Aux_DQI_Semicircle_lemma_9_1

namespace Aux_DQI_Semicircle_lemma_9_1

open DQI.Semicircle Polynomial in
theorem eq68 (p : ℕ) [Fact p.Prime] (m : ℕ) (F : Fin m → Finset (ZMod p)) (r : ℕ)
    (hF : ∀ i, (F i).card = r) (hr : 1 ≤ r) (hrp : r < p) (k : ℕ) :
    ∑ y ∈ Finset.univ.filter (fun y : Fin m → ZMod p => wt y = k), ‖gtil F y‖ ^ 2 =
      (m.choose k : ℝ) := by
  have hg : ∀ i, ∑ a, g F i a = 0 ∧ ∑ a, (g F i a) ^ 2 = 1 := g_props F r hF hr hrp
  have hsum1 : ∀ i, ∑ a, ‖gt F i a‖ ^ 2 = 1 := fun i => gt_parseval F i (hg i).2
  have h0 : ∀ i, gt F i 0 = 0 := fun i => gt_zero F i (hg i).1
  have hnorm : ∀ y : Fin m → ZMod p, ‖gtil F y‖ ^ 2 =
      ∏ i ∈ Finset.univ.filter (fun i => y i ≠ 0), ‖gt F i (y i)‖ ^ 2 := by
    intro y
    unfold gtil
    rw [norm_prod, ← Finset.prod_pow]
  obtain ⟨Fp, hFp⟩ : ∃ Fp : Fin m → ZMod p → ℝ[X],
      Fp = fun i a => if a ≠ 0 then C (‖gt F i a‖ ^ 2) else X := ⟨_, rfl⟩
  have h1 : ∀ y : Fin m → ZMod p,
      C (∏ i ∈ Finset.univ.filter (fun i => y i ≠ 0), ‖gt F i (y i)‖ ^ 2) *
        X ^ (Finset.univ.filter (fun i => ¬ (y i ≠ 0))).card = ∏ i, Fp i (y i) := by
    intro y
    simp only [hFp]
    rw [Finset.prod_ite, map_prod, Finset.prod_const]
  have h2 : ∀ i, ∑ a, Fp i a = X + 1 := by
    intro i
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod p))]
    have e1 : Fp i 0 = X := by simp [hFp]
    have e2 : ∀ a ∈ Finset.univ.erase (0 : ZMod p), Fp i a = C (‖gt F i a‖ ^ 2) := by
      intro a ha
      simp [hFp, Finset.ne_of_mem_erase ha]
    rw [e1, Finset.sum_congr rfl e2, ← map_sum, Finset.sum_erase_eq_sub (Finset.mem_univ _),
      hsum1 i, h0 i, norm_zero]
    simp
  have hpoly : ∑ y : Fin m → ZMod p,
      C (∏ i ∈ Finset.univ.filter (fun i => y i ≠ 0), ‖gt F i (y i)‖ ^ 2) *
        X ^ (Finset.univ.filter (fun i => ¬ (y i ≠ 0))).card = (X + 1 : ℝ[X]) ^ m := by
    rw [Finset.sum_congr rfl (fun y _ => h1 y), ← Fintype.prod_sum Fp,
      Finset.prod_congr rfl (fun i _ => h2 i), Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  have hcoef := congrArg (fun P : ℝ[X] => P.coeff (m - k)) hpoly
  simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_X_add_one_pow] at hcoef
  have hz : ∀ y : Fin m → ZMod p,
      wt y + (Finset.univ.filter (fun i => ¬ (y i ≠ 0))).card = m := by
    intro y
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m)))
      (fun i => y i ≠ 0)
    rw [Finset.card_univ, Fintype.card_fin] at this
    exact this
  rw [Finset.sum_filter]
  by_cases hkm : k ≤ m
  · rw [Nat.choose_symm hkm] at hcoef
    rw [← hcoef]
    apply Finset.sum_congr rfl
    intro y _
    have := hz y
    by_cases hw : wt y = k
    · have hc : m - k = (Finset.univ.filter (fun i => ¬ (y i ≠ 0))).card := by omega
      rw [if_pos hw, if_pos hc, hnorm]
    · have hc : ¬ (m - k = (Finset.univ.filter (fun i => ¬ (y i ≠ 0))).card) := by omega
      rw [if_neg hw, if_neg hc]
  · push_neg at hkm
    rw [Nat.choose_eq_zero_of_lt hkm, Nat.cast_zero]
    apply Finset.sum_eq_zero
    intro y _
    have := hz y
    have hw : ¬ (wt y = k) := by omega
    rw [if_neg hw]

end Aux_DQI_Semicircle_lemma_9_1

namespace Aux_DQI_Semicircle_lemma_9_1

open DQI.Semicircle

lemma norm_sq_sum_of_sub {ι : Type*} (T : Finset ι) (c : ι → ℂ)
    (hT : ∀ y ∈ T, ∀ y' ∈ T, y = y') :
    ‖∑ y ∈ T, c y‖ ^ 2 = ∑ y ∈ T, ‖c y‖ ^ 2 := by
  rcases T.eq_empty_or_nonempty with h | ⟨y0, hy0⟩
  · simp [h]
  · have : T = {y0} := Finset.eq_singleton_iff_unique_mem.mpr ⟨hy0, fun y hy => hT y hy y0 hy0⟩
    rw [this, Finset.sum_singleton, Finset.sum_singleton]

end Aux_DQI_Semicircle_lemma_9_1

open Aux_DQI_Semicircle_lemma_9_1 in
open DQI.Semicircle in
theorem solution (p : ℕ) [Fact p.Prime] (m n : ℕ) (B : Matrix (Fin m) (Fin n) (ZMod p))
    (F : Fin m → Finset (ZMod p)) (r : ℕ) (hF : ∀ i, (F i).card = r) (hr : 1 ≤ r) (hrp : r < p)
    (hnm : n < m) (ℓ : ℕ) (w : Fin (ℓ + 1) → ℝ) (hdist : DistGt B (2 * ℓ)) :
    ∑ s : Fin n → ZMod p, ‖Ptilde B F ℓ w s‖ ^ 2 = ∑ k, w k ^ 2 := by
  -- the kernel of Bᵀ is non-trivial, hence ℓ < m
  have hker : ∃ d : Fin m → ZMod p, d ≠ 0 ∧ B.transpose.mulVec d = 0 := by
    have hne := LinearMap.ker_ne_bot_of_finrank_lt (f := Matrix.mulVecLin B.transpose)
      (by simpa [Module.finrank_fin_fun] using hnm)
    obtain ⟨d, hd, hd0⟩ := (Submodule.ne_bot_iff _).mp hne
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hd
    exact ⟨d, hd0, hd⟩
  obtain ⟨d, hd0, hdk⟩ := hker
  have hwd := hdist d hd0 hdk
  have hwtle : ∀ y : Fin m → ZMod p, wt y ≤ m := by
    intro y
    unfold wt
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hℓm : ℓ < m := by have := hwtle d; omega
  -- injectivity of y ↦ Bᵀ y on low-weight vectors
  have hinj : ∀ y y' : Fin m → ZMod p, wt y ≤ ℓ → wt y' ≤ ℓ →
      B.transpose.mulVec y = B.transpose.mulVec y' → y = y' := by
    intro y y' hy hy' heq
    by_contra hne
    have h1 : y - y' ≠ 0 := sub_ne_zero.mpr hne
    have h2 : B.transpose.mulVec (y - y') = 0 := by rw [Matrix.mulVec_sub, heq, sub_self]
    have h3 := hdist _ h1 h2
    have h4 : wt (y - y') ≤ wt y + wt y' := by
      unfold wt
      calc (Finset.univ.filter fun i => (y - y') i ≠ 0).card
          ≤ ((Finset.univ.filter fun i => y i ≠ 0) ∪ (Finset.univ.filter fun i => y' i ≠ 0)).card := by
            apply Finset.card_le_card
            intro i hi
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
            simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
            by_contra hc
            push_neg at hc
            apply hi
            rw [Pi.sub_apply, hc.1, hc.2, sub_zero]
        _ ≤ _ := Finset.card_union_le _ _
    omega
  -- coefficients
  obtain ⟨A, hA⟩ : ∃ A : ℕ → ℝ, A = fun k => if h : k < ℓ + 1 then w ⟨k, h⟩ else 0 := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : (Fin m → ZMod p) → Fin (ℓ + 1),
      g = fun y => ⟨min (wt y) ℓ, by omega⟩ := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : Finset (Fin m → ZMod p), Y = Finset.univ.filter (fun y => wt y ≤ ℓ) :=
    ⟨_, rfl⟩
  have hfib : ∀ k : Fin (ℓ + 1), Y.filter (fun y => g y = k) =
      Finset.univ.filter (fun y : Fin m → ZMod p => wt y = (k : ℕ)) := by
    intro k
    have := k.isLt
    ext y
    rw [hY, hg]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.ext_iff]
    constructor
    · rintro ⟨h1, h2⟩
      omega
    · intro h1
      constructor <;> omega
  have hfib2 : ∀ (s : Fin n → ZMod p) (k : Fin (ℓ + 1)),
      (Y.filter (fun y => B.transpose.mulVec y = s)).filter (fun y => g y = k) =
      Finset.univ.filter (fun y : Fin m → ZMod p => wt y = (k : ℕ) ∧ B.transpose.mulVec y = s) := by
    intro s k
    have := k.isLt
    ext y
    rw [hY, hg]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.ext_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨by omega, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨by omega, h2⟩, by omega⟩
  have hAk : ∀ (k : Fin (ℓ + 1)) (y : Fin m → ZMod p), wt y = (k : ℕ) → A (wt y) = w k := by
    intro k y hy
    rw [hA, hy]
    simp only [dif_pos k.isLt, Fin.eta]
  obtain ⟨c, hc⟩ : ∃ c : (Fin m → ZMod p) → ℂ,
      ∀ y, c y = ((A (wt y) / Real.sqrt (m.choose (wt y)) : ℝ) : ℂ) * gtil F y :=
    ⟨fun y => ((A (wt y) / Real.sqrt (m.choose (wt y)) : ℝ) : ℂ) * gtil F y, fun _ => rfl⟩
  have hP : ∀ s, Ptilde B F ℓ w s = ∑ y ∈ Y.filter (fun y => B.transpose.mulVec y = s), c y := by
    intro s
    unfold Ptilde
    rw [← Finset.sum_fiberwise (Y.filter (fun y => B.transpose.mulVec y = s)) g c]
    apply Finset.sum_congr rfl
    intro k _
    rw [hfib2 s k, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    rw [Finset.mem_filter] at hy
    rw [hc y, hAk k y hy.2.1, hy.2.1]
  have hYinj : ∀ s, ∀ y ∈ Y.filter (fun y => B.transpose.mulVec y = s),
      ∀ y' ∈ Y.filter (fun y => B.transpose.mulVec y = s), y = y' := by
    intro s y hy y' hy'
    rw [Finset.mem_filter, hY, Finset.mem_filter] at hy hy'
    exact hinj y y' hy.1.2 hy'.1.2 (hy.2.trans hy'.2.symm)
  have h68 := eq68 p m F r hF hr hrp
  calc ∑ s : Fin n → ZMod p, ‖Ptilde B F ℓ w s‖ ^ 2
      = ∑ s : Fin n → ZMod p, ∑ y ∈ Y.filter (fun y => B.transpose.mulVec y = s), ‖c y‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro s _
        rw [hP s, norm_sq_sum_of_sub _ _ (hYinj s)]
    _ = ∑ y ∈ Y, ‖c y‖ ^ 2 := Finset.sum_fiberwise Y _ _
    _ = ∑ k : Fin (ℓ + 1), ∑ y ∈ Y.filter (fun y => g y = k), ‖c y‖ ^ 2 :=
        (Finset.sum_fiberwise Y g _).symm
    _ = ∑ k : Fin (ℓ + 1), (w k ^ 2 / (m.choose (k : ℕ) : ℝ)) *
          ∑ y ∈ Finset.univ.filter (fun y : Fin m → ZMod p => wt y = (k : ℕ)), ‖gtil F y‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro k _
        rw [hfib k, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y hy
        rw [Finset.mem_filter] at hy
        have hpos : (0 : ℝ) ≤ (m.choose (wt y) : ℝ) := Nat.cast_nonneg _
        rw [hc y]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, div_pow,
          Real.sq_sqrt hpos, hAk k y hy.2, hy.2]
    _ = ∑ k : Fin (ℓ + 1), w k ^ 2 := by
        apply Finset.sum_congr rfl
        intro k _
        rw [h68 (k : ℕ)]
        have hk : (k : ℕ) ≤ m := by have := k.isLt; omega
        have hC : (m.choose (k : ℕ) : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.choose_pos hk).ne'
        field_simp
