-- Prove2me | solution 1 for FTheoryK3Tate.discOrder_IIstar
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-22T11:11:51.600389+00:00
-- url     : https://prove2.me/submissions/8e7a2a4d-fb98-4a96-b7f8-1c8d4d4b8def

import Definitions.Def_FTheoryK3TateCore

open Polynomial

namespace K3TateAux

variable {R : Type*} [CommRing R]
variable {R : Type*} [CommRing R]

lemma rootMultiplicity_neg [IsDomain R] (a : R) (p : R[X]) :
    rootMultiplicity a (-p) = rootMultiplicity a p := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  · have : -p = C (-1) * p := by simp [C_neg, C_1, neg_mul]
    rw [this, rootMultiplicity_mul (mul_ne_zero (C_ne_zero.mpr (neg_ne_zero.mpr one_ne_zero)) hp),
      rootMultiplicity_C, zero_add]

lemma rootMultiplicity_pow [IsDomain R] (a : R) (p : R[X]) (n : ℕ) :
    rootMultiplicity a (p ^ n) = n * rootMultiplicity a p := by
  induction n with
  | zero => simp
  | succ n ih =>
      rcases eq_or_ne p 0 with rfl | hp
      · rw [zero_pow (Nat.succ_ne_zero n), rootMultiplicity_zero, Nat.mul_zero]
      · rw [pow_succ, rootMultiplicity_mul (mul_ne_zero (pow_ne_zero n hp) hp), ih, Nat.succ_mul]

lemma rootMultiplicity_add_of_lt (a : R) {p q : R[X]} (hzero : p + q ≠ 0) (hq : q ≠ 0)
    (h : rootMultiplicity a q < rootMultiplicity a p) :
    rootMultiplicity a (p + q) = rootMultiplicity a q := by
  apply le_antisymm
  · rw [rootMultiplicity_le_iff hzero]
    intro hdvd
    have hp : (X - C a) ^ (rootMultiplicity a q + 1) ∣ p :=
      (pow_dvd_pow (X - C a) (Nat.succ_le_of_lt h)).trans (pow_rootMultiplicity_dvd p a)
    have hq' : (X - C a) ^ (rootMultiplicity a q + 1) ∣ q := by
      have := dvd_sub hdvd hp
      rwa [show p + q - p = q by ring] at this
    exact pow_rootMultiplicity_not_dvd hq a hq'
  · calc rootMultiplicity a q = min (rootMultiplicity a p) (rootMultiplicity a q) :=
          (min_eq_right (le_of_lt h)).symm
      _ ≤ rootMultiplicity a (p + q) := rootMultiplicity_add a hzero

end K3TateAux

namespace K3TateProof

open FTheoryK3Tate

variable {k : Type*} [Field k] [CharZero k]

theorem discriminant_natDegree_le (f g : k[X])
    (hf : f.natDegree ≤ 8) (hg : g.natDegree ≤ 12) :
    (Δ f g).natDegree ≤ 24 := by
  unfold Δ
  compute_degree
  omega

theorem sum_rootMultiplicity_discriminant_le (f g : k[X]) (_h : Δ f g ≠ 0)
    (S : Finset k) :
    (∑ t₀ ∈ S, (Δ f g).rootMultiplicity t₀) ≤ (Δ f g).natDegree := by
  classical
  calc ∑ t₀ ∈ S, (Δ f g).rootMultiplicity t₀
      = ∑ t₀ ∈ S, (Δ f g).roots.count t₀ := by simp only [count_roots]
    _ ≤ ∑ t₀ ∈ S ∪ (Δ f g).roots.toFinset, (Δ f g).roots.count t₀ :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
          (fun i _ _ => Nat.zero_le _)
    _ = (Δ f g).roots.card :=
        Multiset.sum_count_eq_card (fun a ha => Finset.mem_union_right _ (Multiset.mem_toFinset.mpr ha))
    _ ≤ (Δ f g).natDegree := card_roots' _

lemma rootMultiplicity_27g2 (g : k[X]) (t₀ : k) (hg0 : g ≠ 0) :
    (27 * g ^ 2).rootMultiplicity t₀ = 2 * g.rootMultiplicity t₀ := by
  have h27 : (27 : k[X]) = C (27 : k) := (C_eq_natCast 27).symm
  rw [h27, rootMultiplicity_mul (by simp [hg0]), rootMultiplicity_C, zero_add,
    K3TateAux.rootMultiplicity_pow t₀ g 2]

lemma rootMultiplicity_4f3 (f : k[X]) (t₀ : k) (hf0 : f ≠ 0) :
    (4 * f ^ 3).rootMultiplicity t₀ = 3 * f.rootMultiplicity t₀ := by
  have h4 : (4 : k[X]) = C (4 : k) := (C_eq_natCast 4).symm
  rw [h4, rootMultiplicity_mul (by simp [hf0]), rootMultiplicity_C, zero_add,
    K3TateAux.rootMultiplicity_pow t₀ f 3]

theorem discOrder_II (f g : k[X]) (t₀ : k) (h : HasKodaira f g t₀ Kodaira.II) :
    (Δ f g).rootMultiplicity t₀ = 2 := by
  obtain ⟨hf1, hg1⟩ := h
  have hg0 : g ≠ 0 := fun h0 => by simp [h0] at hg1
  have hB : (27 * g ^ 2).rootMultiplicity t₀ = 2 := by
    rw [rootMultiplicity_27g2 g t₀ hg0, hg1]
  rcases eq_or_ne f 0 with hf0 | hf0
  · rw [Δ, hf0]
    rw [show (4 : k[X]) * 0 ^ 3 + 27 * g ^ 2 = 27 * g ^ 2 by ring]
    exact hB
  · have hA : (4 * f ^ 3).rootMultiplicity t₀ = 3 * f.rootMultiplicity t₀ :=
      rootMultiplicity_4f3 f t₀ hf0
    have hf1' : 1 ≤ f.rootMultiplicity t₀ := (le_rootMultiplicity_iff hf0).2 (by simpa using hf1)
    have hne : Δ f g ≠ 0 := by
      intro hzero
      rw [Δ] at hzero
      have h1 : (4 : k[X]) * f ^ 3 = -((27 : k[X]) * g ^ 2) := by
        rw [eq_neg_iff_add_eq_zero]
        exact hzero
      have hthis : (4 * f ^ 3).rootMultiplicity t₀ = (27 * g ^ 2).rootMultiplicity t₀ := by
        rw [h1, K3TateAux.rootMultiplicity_neg]
      rw [hA, hB] at hthis
      omega
    have hlt : (27 * g ^ 2).rootMultiplicity t₀ < (4 * f ^ 3).rootMultiplicity t₀ := by
      rw [hB, hA]
      omega
    rw [Δ, K3TateAux.rootMultiplicity_add_of_lt t₀ hne (by simp [hg0]) hlt, hB]

theorem discOrder_III (f g : k[X]) (t₀ : k) (h : HasKodaira f g t₀ Kodaira.III) :
    (Δ f g).rootMultiplicity t₀ = 3 := by
  obtain ⟨hf1, hg2⟩ := h
  have hf0 : f ≠ 0 := fun h0 => by simp [h0] at hf1
  have hA : (4 * f ^ 3).rootMultiplicity t₀ = 3 := by
    rw [rootMultiplicity_4f3 f t₀ hf0, hf1]
  have hΔ' : Δ f g = 27 * g ^ 2 + 4 * f ^ 3 := by rw [Δ]; ring
  rcases eq_or_ne g 0 with hg0 | hg0
  · rw [Δ, hg0]
    rw [show (4 : k[X]) * f ^ 3 + 27 * (0 : k[X]) ^ 2 = 4 * f ^ 3 by ring]
    exact hA
  · have hg2' : 2 ≤ g.rootMultiplicity t₀ := (le_rootMultiplicity_iff hg0).2 hg2
    have hB : (27 * g ^ 2).rootMultiplicity t₀ = 2 * g.rootMultiplicity t₀ :=
      rootMultiplicity_27g2 g t₀ hg0
    have hne : 27 * g ^ 2 + 4 * f ^ 3 ≠ 0 := by
      intro hzero
      have h1 : (27 : k[X]) * g ^ 2 = -((4 : k[X]) * f ^ 3) := by
        rw [eq_neg_iff_add_eq_zero]
        exact hzero
      have hthis : (27 * g ^ 2).rootMultiplicity t₀ = (4 * f ^ 3).rootMultiplicity t₀ := by
        rw [h1, K3TateAux.rootMultiplicity_neg]
      rw [hB, hA] at hthis
      omega
    have hlt : (4 * f ^ 3).rootMultiplicity t₀ < (27 * g ^ 2).rootMultiplicity t₀ := by
      rw [hB, hA]
      omega
    rw [hΔ', K3TateAux.rootMultiplicity_add_of_lt t₀ hne (by simp [hf0]) hlt, hA]

lemma rootMultiplicity_discriminant_eq_of_dvd (f g : k[X]) (t₀ : k) {n d : ℕ}
    (hf : (X - C t₀) ^ n ∣ f) (hg : g.rootMultiplicity t₀ = d) (hd0 : d ≠ 0)
    (hlt : 2 * d < 3 * n) :
    (Δ f g).rootMultiplicity t₀ = 2 * d := by
  have hg0 : g ≠ 0 := fun h0 => by
    rw [h0, rootMultiplicity_zero] at hg
    omega
  have hB : (27 * g ^ 2).rootMultiplicity t₀ = 2 * d := by
    rw [rootMultiplicity_27g2 g t₀ hg0, hg]
  rcases eq_or_ne f 0 with hf0 | hf0
  · rw [Δ, hf0]
    rw [show (4 : k[X]) * 0 ^ 3 + 27 * g ^ 2 = 27 * g ^ 2 by ring]
    exact hB
  · have hA : (4 * f ^ 3).rootMultiplicity t₀ = 3 * f.rootMultiplicity t₀ :=
      rootMultiplicity_4f3 f t₀ hf0
    have hfn : n ≤ f.rootMultiplicity t₀ := (le_rootMultiplicity_iff hf0).2 hf
    have hne : Δ f g ≠ 0 := by
      intro hzero
      rw [Δ] at hzero
      have h1 : (4 : k[X]) * f ^ 3 = -((27 : k[X]) * g ^ 2) := by
        rw [eq_neg_iff_add_eq_zero]
        exact hzero
      have hthis : (4 * f ^ 3).rootMultiplicity t₀ = (27 * g ^ 2).rootMultiplicity t₀ := by
        rw [h1, K3TateAux.rootMultiplicity_neg]
      rw [hA, hB] at hthis
      omega
    have hlt' : (27 * g ^ 2).rootMultiplicity t₀ < (4 * f ^ 3).rootMultiplicity t₀ := by
      rw [hB, hA]
      omega
    rw [Δ, K3TateAux.rootMultiplicity_add_of_lt t₀ hne (by simp [hg0]) hlt', hB]

lemma rootMultiplicity_discriminant_eq_of_dvd_right (f g : k[X]) (t₀ : k) {m n : ℕ}
    (hf : f.rootMultiplicity t₀ = m) (hm0 : m ≠ 0) (hg : (X - C t₀) ^ n ∣ g)
    (hlt : 3 * m < 2 * n) :
    (Δ f g).rootMultiplicity t₀ = 3 * m := by
  have hf0 : f ≠ 0 := fun h0 => by
    rw [h0, rootMultiplicity_zero] at hf
    omega
  have hA : (4 * f ^ 3).rootMultiplicity t₀ = 3 * m := by
    rw [rootMultiplicity_4f3 f t₀ hf0, hf]
  have hΔ' : Δ f g = 27 * g ^ 2 + 4 * f ^ 3 := by rw [Δ]; ring
  rcases eq_or_ne g 0 with hg0 | hg0
  · rw [Δ, hg0]
    rw [show (4 : k[X]) * f ^ 3 + 27 * (0 : k[X]) ^ 2 = 4 * f ^ 3 by ring]
    exact hA
  · have hgn : n ≤ g.rootMultiplicity t₀ := (le_rootMultiplicity_iff hg0).2 hg
    have hB : (27 * g ^ 2).rootMultiplicity t₀ = 2 * g.rootMultiplicity t₀ :=
      rootMultiplicity_27g2 g t₀ hg0
    have hne : 27 * g ^ 2 + 4 * f ^ 3 ≠ 0 := by
      intro hzero
      have h1 : (27 : k[X]) * g ^ 2 = -((4 : k[X]) * f ^ 3) := by
        rw [eq_neg_iff_add_eq_zero]
        exact hzero
      have hthis : (27 * g ^ 2).rootMultiplicity t₀ = (4 * f ^ 3).rootMultiplicity t₀ := by
        rw [h1, K3TateAux.rootMultiplicity_neg]
      rw [hB, hA] at hthis
      omega
    have hlt' : (4 * f ^ 3).rootMultiplicity t₀ < (27 * g ^ 2).rootMultiplicity t₀ := by
      rw [hB, hA]
      omega
    rw [hΔ', K3TateAux.rootMultiplicity_add_of_lt t₀ hne (by simp [hf0]) hlt', hA]

theorem discOrder_IV (f g : k[X]) (t₀ : k) (h : HasKodaira f g t₀ Kodaira.IV) :
    (Δ f g).rootMultiplicity t₀ = 4 := by
  obtain ⟨hf2, hg2⟩ := h
  exact rootMultiplicity_discriminant_eq_of_dvd f g t₀ hf2 hg2 (by norm_num) (by norm_num)

theorem discOrder_IVstar (f g : k[X]) (t₀ : k) (h : HasKodaira f g t₀ Kodaira.IVstar) :
    (Δ f g).rootMultiplicity t₀ = 8 := by
  obtain ⟨hf3, hg4⟩ := h
  exact rootMultiplicity_discriminant_eq_of_dvd f g t₀ hf3 hg4 (by norm_num) (by norm_num)

theorem discOrder_IIstar (f g : k[X]) (t₀ : k) (h : HasKodaira f g t₀ Kodaira.IIstar) :
    (Δ f g).rootMultiplicity t₀ = 10 := by
  obtain ⟨hf4, hg5⟩ := h
  exact rootMultiplicity_discriminant_eq_of_dvd f g t₀ hf4 hg5 (by norm_num) (by norm_num)

theorem discOrder_IIIstar (f g : k[X]) (t₀ : k) (h : HasKodaira f g t₀ Kodaira.IIIstar) :
    (Δ f g).rootMultiplicity t₀ = 9 := by
  obtain ⟨hf3, hg5⟩ := h
  exact rootMultiplicity_discriminant_eq_of_dvd_right f g t₀ hf3 (by norm_num) hg5 (by norm_num)

theorem discOrder_I0star_general (f g : k[X]) (t₀ : k)
    (hf : (X - C t₀) ^ 2 ∣ f) (hg : (X - C t₀) ^ 3 ∣ g)
    (hred : 4 * ((taylor t₀ f).coeff 2) ^ 3 + 27 * ((taylor t₀ g).coeff 3) ^ 2 ≠ 0) :
    (Δ f g).rootMultiplicity t₀ = 6 := by
  let F := f /ₘ (X - C t₀) ^ 2
  let G := g /ₘ (X - C t₀) ^ 3
  have hF : (X - C t₀) ^ 2 * F = f := by
    have hmod : f %ₘ (X - C t₀) ^ 2 = 0 :=
      (modByMonic_eq_zero_iff_dvd ((monic_X_sub_C t₀).pow 2)).2 hf
    have h := modByMonic_add_div f ((X - C t₀) ^ 2)
    rwa [hmod, zero_add] at h
  have hG : (X - C t₀) ^ 3 * G = g := by
    have hmod : g %ₘ (X - C t₀) ^ 3 = 0 :=
      (modByMonic_eq_zero_iff_dvd ((monic_X_sub_C t₀).pow 3)).2 hg
    have h := modByMonic_add_div g ((X - C t₀) ^ 3)
    rwa [hmod, zero_add] at h
  have htX : taylor t₀ (X - C t₀) = X := by
    simp [taylor_apply, sub_comp]
  have ht2 : taylor t₀ ((X - C t₀) ^ 2) = X ^ 2 := by
    rw [pow_two, taylor_mul, htX, pow_two]
  have ht3 : taylor t₀ ((X - C t₀) ^ 3) = X ^ 3 := by
    rw [show (X - C t₀) ^ 3 = (X - C t₀) ^ 2 * (X - C t₀) by ring, taylor_mul, ht2, htX]
    ring
  have hc2 : (taylor t₀ f).coeff 2 = F.eval t₀ := by
    rw [← hF, taylor_mul, ht2, coeff_X_pow_mul (taylor t₀ F) 2 0, taylor_coeff_zero]
  have hc3 : (taylor t₀ g).coeff 3 = G.eval t₀ := by
    rw [← hG, taylor_mul, ht3, coeff_X_pow_mul (taylor t₀ G) 3 0, taylor_coeff_zero]
  have hQeval : (4 * F ^ 3 + 27 * G ^ 2).eval t₀ ≠ 0 := by
    have hq : (4 * F ^ 3 + 27 * G ^ 2).eval t₀
        = 4 * (F.eval t₀) ^ 3 + 27 * (G.eval t₀) ^ 2 := by simp
    rw [hq, ← hc2, ← hc3]
    exact hred
  have hQne : 4 * F ^ 3 + 27 * G ^ 2 ≠ 0 :=
    fun h0 => hQeval (by rw [h0]; simp)
  have hQ0 : (4 * F ^ 3 + 27 * G ^ 2).rootMultiplicity t₀ = 0 :=
    rootMultiplicity_eq_zero (fun hroot => hQeval hroot)
  have hΔeq : Δ f g = (X - C t₀) ^ 6 * (4 * F ^ 3 + 27 * G ^ 2) := by
    rw [Δ, ← hF, ← hG]
    ring
  rw [hΔeq, rootMultiplicity_mul (mul_ne_zero (pow_ne_zero 6 (monic_X_sub_C t₀).ne_zero) hQne),
    rootMultiplicity_X_sub_C_pow, hQ0, add_zero]

theorem discOrder_I0star (f g : k[X]) (t₀ : k) (h : HasKodaira f g t₀ Kodaira.I0star) :
    (Δ f g).rootMultiplicity t₀ = 6 := by
  obtain ⟨hf2, hg3, hred⟩ := h
  exact discOrder_I0star_general f g t₀
    (by simpa [hf2] using pow_rootMultiplicity_dvd f t₀)
    (by simpa [hg3] using pow_rootMultiplicity_dvd g t₀)
    hred

lemma discOrder_eq_rootMultiplicity (f g : k[X]) (t₀ : k) (κ : Kodaira)
    (h : HasKodaira f g t₀ κ) : (Δ f g).rootMultiplicity t₀ = κ.discOrder := by
  cases κ with
  | II => exact discOrder_II f g t₀ h
  | III => exact discOrder_III f g t₀ h
  | IV => exact discOrder_IV f g t₀ h
  | I0star => exact discOrder_I0star f g t₀ h
  | IVstar => exact discOrder_IVstar f g t₀ h
  | IIIstar => exact discOrder_IIIstar f g t₀ h
  | IIstar => exact discOrder_IIstar f g t₀ h

theorem kodaira_brane_budget (f g : k[X]) (h : IsK3Data f g)
    (S : Finset k) (τ : k → Kodaira)
    (hτ : ∀ t ∈ S, HasKodaira f g t (τ t)) :
    ∑ t ∈ S, (τ t).discOrder ≤ 24 := by
  obtain ⟨hf8, hg12, hΔ⟩ := h
  have hper : ∀ t ∈ S, (Δ f g).rootMultiplicity t = (τ t).discOrder :=
    fun t ht => discOrder_eq_rootMultiplicity f g t (τ t) (hτ t ht)
  calc ∑ t ∈ S, (τ t).discOrder
      = ∑ t ∈ S, (Δ f g).rootMultiplicity t :=
        Finset.sum_congr rfl (fun t ht => (hper t ht).symm)
    _ ≤ (Δ f g).natDegree := sum_rootMultiplicity_discriminant_le f g hΔ S
    _ ≤ 24 := discriminant_natDegree_le f g hf8 hg12

theorem card_IVstar_le_three (f g : k[X]) (h : IsK3Data f g) :
    {t₀ : k | HasKodaira f g t₀ Kodaira.IVstar}.Finite ∧
    Nat.card {t₀ : k | HasKodaira f g t₀ Kodaira.IVstar} ≤ 3 := by
  obtain ⟨hf8, hg12, hΔ⟩ := h
  have h8 : ∀ t₀ ∈ {t₀ : k | HasKodaira f g t₀ Kodaira.IVstar},
      (Δ f g).rootMultiplicity t₀ = 8 :=
    fun t₀ ht => discOrder_IVstar f g t₀ ht
  have hroot : ∀ t₀ ∈ {t₀ : k | HasKodaira f g t₀ Kodaira.IVstar}, (Δ f g).IsRoot t₀ := by
    intro t₀ ht
    have hpos : 0 < (Δ f g).rootMultiplicity t₀ := by rw [h8 t₀ ht]; norm_num
    exact (rootMultiplicity_pos'.mp hpos).2
  have hfin : {t₀ : k | HasKodaira f g t₀ Kodaira.IVstar}.Finite :=
    (finite_setOfPred_isRoot hΔ).subset hroot
  refine ⟨hfin, ?_⟩
  have hcw : ∑ t₀ ∈ hfin.toFinset, (Δ f g).rootMultiplicity t₀ = 8 * hfin.toFinset.card := by
    rw [Finset.sum_congr rfl (fun t₀ ht => h8 t₀ (hfin.mem_toFinset.mp ht))]
    simp [Finset.sum_const, mul_comm]
  have hsum := sum_rootMultiplicity_discriminant_le f g hΔ hfin.toFinset
  have hdeg : (Δ f g).natDegree ≤ 24 := discriminant_natDegree_le f g hf8 hg12
  have hcard : 8 * hfin.toFinset.card ≤ 24 := by
    rw [← hcw]
    exact le_trans hsum hdeg
  rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hfin]
  omega

theorem card_IIIstar_le_two (f g : k[X]) (h : IsK3Data f g) :
    {t₀ : k | HasKodaira f g t₀ Kodaira.IIIstar}.Finite ∧
    Nat.card {t₀ : k | HasKodaira f g t₀ Kodaira.IIIstar} ≤ 2 := by
  obtain ⟨hf8, hg12, hΔ⟩ := h
  have h9 : ∀ t₀ ∈ {t₀ : k | HasKodaira f g t₀ Kodaira.IIIstar},
      (Δ f g).rootMultiplicity t₀ = 9 :=
    fun t₀ ht => discOrder_IIIstar f g t₀ ht
  have hroot : ∀ t₀ ∈ {t₀ : k | HasKodaira f g t₀ Kodaira.IIIstar}, (Δ f g).IsRoot t₀ := by
    intro t₀ ht
    have hpos : 0 < (Δ f g).rootMultiplicity t₀ := by rw [h9 t₀ ht]; norm_num
    exact (rootMultiplicity_pos'.mp hpos).2
  have hfin : {t₀ : k | HasKodaira f g t₀ Kodaira.IIIstar}.Finite :=
    (finite_setOfPred_isRoot hΔ).subset hroot
  refine ⟨hfin, ?_⟩
  have hcw : ∑ t₀ ∈ hfin.toFinset, (Δ f g).rootMultiplicity t₀ = 9 * hfin.toFinset.card := by
    rw [Finset.sum_congr rfl (fun t₀ ht => h9 t₀ (hfin.mem_toFinset.mp ht))]
    simp [Finset.sum_const, mul_comm]
  have hsum := sum_rootMultiplicity_discriminant_le f g hΔ hfin.toFinset
  have hdeg : (Δ f g).natDegree ≤ 24 := discriminant_natDegree_le f g hf8 hg12
  have hcard : 9 * hfin.toFinset.card ≤ 24 := by
    rw [← hcw]
    exact le_trans hsum hdeg
  rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hfin]
  omega

theorem at_most_two_E8 (f g : k[X]) (h : IsK3Data f g) :
    {t₀ : k | IsE8Point f g t₀}.Finite ∧
    Nat.card {t₀ : k | IsE8Point f g t₀} ≤ 2 := by
  obtain ⟨hf8, hg12, hΔ⟩ := h
  have h10 : ∀ t₀ ∈ {t₀ : k | IsE8Point f g t₀}, (Δ f g).rootMultiplicity t₀ = 10 :=
    fun t₀ ht => discOrder_IIstar f g t₀ ht
  have hroot : ∀ t₀ ∈ {t₀ : k | IsE8Point f g t₀}, (Δ f g).IsRoot t₀ := by
    intro t₀ ht
    have hpos : 0 < (Δ f g).rootMultiplicity t₀ := by rw [h10 t₀ ht]; norm_num
    exact (rootMultiplicity_pos'.mp hpos).2
  have hfin : {t₀ : k | IsE8Point f g t₀}.Finite :=
    (finite_setOfPred_isRoot hΔ).subset hroot
  refine ⟨hfin, ?_⟩
  have hcw : ∑ t₀ ∈ hfin.toFinset, (Δ f g).rootMultiplicity t₀ = 10 * hfin.toFinset.card := by
    rw [Finset.sum_congr rfl (fun t₀ ht => h10 t₀ (hfin.mem_toFinset.mp ht))]
    simp [Finset.sum_const, mul_comm]
  have hsum := sum_rootMultiplicity_discriminant_le f g hΔ hfin.toFinset
  have hdeg : (Δ f g).natDegree ≤ 24 := discriminant_natDegree_le f g hf8 hg12
  have hcard : 10 * hfin.toFinset.card ≤ 24 := by
    rw [← hcw]
    exact le_trans hsum hdeg
  rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hfin]
  omega

theorem budget_exceptional (f g : k[X]) (h : IsK3Data f g)
    (S6 S7 S8 : Finset k)
    (d67 : Disjoint S6 S7) (d68 : Disjoint S6 S8) (d78 : Disjoint S7 S8)
    (h6 : ∀ t ∈ S6, HasKodaira f g t Kodaira.IVstar)
    (h7 : ∀ t ∈ S7, HasKodaira f g t Kodaira.IIIstar)
    (h8 : ∀ t ∈ S8, HasKodaira f g t Kodaira.IIstar) :
    8 * S6.card + 9 * S7.card + 10 * S8.card ≤ 24 := by
  classical
  obtain ⟨hf8, hg12, hΔ⟩ := h
  have h6' : ∀ t ∈ S6, 8 ≤ (Δ f g).rootMultiplicity t := by
    intro t ht
    rw [discOrder_IVstar f g t (h6 t ht)]
  have h7' : ∀ t ∈ S7, 9 ≤ (Δ f g).rootMultiplicity t := by
    intro t ht
    rw [discOrder_IIIstar f g t (h7 t ht)]
  have h8' : ∀ t ∈ S8, 10 ≤ (Δ f g).rootMultiplicity t := by
    intro t ht
    rw [discOrder_IIstar f g t (h8 t ht)]
  have e1 : 8 * S6.card = ∑ t ∈ S6, (8 : ℕ) := by
    rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have e2 : 9 * S7.card = ∑ t ∈ S7, (9 : ℕ) := by
    rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have e3 : 10 * S8.card = ∑ t ∈ S8, (10 : ℕ) := by
    rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hd678 : Disjoint (S6 ∪ S7) S8 := (Finset.disjoint_union_left).2 ⟨d68, d78⟩
  calc 8 * S6.card + 9 * S7.card + 10 * S8.card
      = (∑ t ∈ S6, (8 : ℕ)) + (∑ t ∈ S7, (9 : ℕ)) + (∑ t ∈ S8, (10 : ℕ)) := by
        rw [e1, e2, e3]
    _ ≤ (∑ t ∈ S6, (Δ f g).rootMultiplicity t)
          + (∑ t ∈ S7, (Δ f g).rootMultiplicity t)
          + (∑ t ∈ S8, (Δ f g).rootMultiplicity t) :=
        add_le_add (add_le_add (Finset.sum_le_sum h6') (Finset.sum_le_sum h7'))
          (Finset.sum_le_sum h8')
    _ = ∑ t ∈ S6 ∪ S7 ∪ S8, (Δ f g).rootMultiplicity t := by
        rw [Finset.sum_union hd678, Finset.sum_union d67]
    _ ≤ (Δ f g).natDegree := sum_rootMultiplicity_discriminant_le f g hΔ _
    _ ≤ 24 := discriminant_natDegree_le f g hf8 hg12

theorem residual_budget (f g : k[X]) (h : IsK3Data f g)
    (E S : Finset k) (hE : ∀ t ∈ E, IsE8Point f g t) (hd : Disjoint E S) :
    10 * E.card + ∑ t ∈ S, (Δ f g).rootMultiplicity t ≤ 24 := by
  classical
  obtain ⟨hf8, hg12, hΔ⟩ := h
  have hE10 : ∑ t ∈ E, (Δ f g).rootMultiplicity t = 10 * E.card := by
    rw [Finset.sum_congr rfl (fun t ht => discOrder_IIstar f g t (hE t ht))]
    simp [Finset.sum_const, mul_comm]
  calc 10 * E.card + ∑ t ∈ S, (Δ f g).rootMultiplicity t
      = ∑ t ∈ E, (Δ f g).rootMultiplicity t
          + ∑ t ∈ S, (Δ f g).rootMultiplicity t := by
        rw [hE10]
    _ = ∑ t ∈ E ∪ S, (Δ f g).rootMultiplicity t := (Finset.sum_union hd).symm
    _ ≤ (Δ f g).natDegree := sum_rootMultiplicity_discriminant_le f g hΔ _
    _ ≤ 24 := discriminant_natDegree_le f g hf8 hg12

end K3TateProof

open FTheoryK3Tate K3TateProof

variable {k : Type*} [Field k] [CharZero k]

theorem solution (f g : k[X]) (t₀ : k) (h : HasKodaira f g t₀ Kodaira.IIstar) :
    (Δ f g).rootMultiplicity t₀ = 10 := by
  obtain ⟨hf4, hg5⟩ := h
  exact rootMultiplicity_discriminant_eq_of_dvd f g t₀ hf4 hg5 (by norm_num) (by norm_num)

#check @solution
#print axioms solution
