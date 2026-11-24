-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.idealOrder_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:54:05.114668+00:00
-- url     : https://prove2.me/submissions/09491c94-c49c-412c-b554-67198251a2c8

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_MultiIndexDerivation
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealOrderDecrease
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LeadingForm
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mem_multiIndicesOfDegree
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mem_maximalIdeal_pow_succ_iff_multiIndexDeriv_mem
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_exists_idealOrder_eq_coe
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_idealOrder_bot
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_le_idealOrder_iff
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_multiIndexDeriv_mul_sub_sum_mem
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_unitMultiIndex_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.unitMultiIndex_apply


section
namespace FunctorialResolution.EmbeddedResolution
open IsLocalRing
private theorem idealOrder_eq_of_le_of_not_le {R : Type*} [CommRing R] [IsLocalRing R] {n : ℕ}
    {I : Ideal R} (h1 : I ≤ IsLocalRing.maximalIdeal R ^ n)
    (h2 : ¬ I ≤ IsLocalRing.maximalIdeal R ^ (n + 1)) : idealOrder I = (n : ℕ∞) := by
  have h3 : (n : ℕ∞) ≤ idealOrder I := (le_idealOrder_iff I n).mpr h1
  have h4 : ¬ (((n + 1 : ℕ) : ℕ∞) ≤ idealOrder I) := fun hc =>
    h2 ((le_idealOrder_iff I (n + 1)).mp hc)
  rw [not_le] at h4
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt h4)
  rw [← hm] at h3 h4 ⊢
  have hle : n ≤ m := by exact_mod_cast h3
  have hlt : m < n + 1 := by exact_mod_cast h4
  have hme : m = n := by omega
  exact_mod_cast hme
private theorem ofDigits_add (N : ℕ) {h : ℕ} (β γ : Fin h → ℕ) :
    ofDigitsFin N (fun i => β i + γ i) = ofDigitsFin N β + ofDigitsFin N γ := by
  simp only [ofDigitsFin, add_mul]
  rw [Finset.sum_add_distrib]
private theorem ofDigits_fin_succ (N : ℕ) {n : ℕ} (δ : Fin (n + 1) → ℕ) :
    ofDigitsFin N δ = δ 0 + (ofDigitsFin N fun i : Fin n => δ i.succ) * N := by
  simp only [ofDigitsFin]
  rw [Fin.sum_univ_succ, Finset.sum_mul]
  congr 1
  · simp
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.val_succ, pow_succ, mul_assoc]
private theorem ofDigits_injective_of_lt (N : ℕ) (hN : 0 < N) : ∀ (h : ℕ) (β γ : Fin h → ℕ),
    (∀ i, β i < N) → (∀ i, γ i < N) → ofDigitsFin N β = ofDigitsFin N γ → β = γ := by
  intro h
  induction h with
  | zero =>
    intro β γ _ _ _
    funext i
    exact i.elim0
  | succ n ih =>
    intro β γ hβ hγ hsum
    rw [ofDigits_fin_succ N β, ofDigits_fin_succ N γ] at hsum
    have h0 : β 0 = γ 0 := by
      have hmod : (β 0 + (ofDigitsFin N fun i : Fin n => β i.succ) * N) % N
          = (γ 0 + (ofDigitsFin N fun i : Fin n => γ i.succ) * N) % N := by rw [hsum]
      rwa [Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right,
        Nat.mod_eq_of_lt (hβ 0), Nat.mod_eq_of_lt (hγ 0)] at hmod
    rw [h0] at hsum
    have h1 : (ofDigitsFin N fun i : Fin n => β i.succ) = ofDigitsFin N fun i : Fin n => γ i.succ :=
      Nat.eq_of_mul_eq_mul_right hN (Nat.add_left_cancel hsum)
    have h2 := ih _ _ (fun i => hβ i.succ) (fun i => hγ i.succ) h1
    funext i
    refine Fin.cases ?_ ?_ i
    · exact h0
    · intro j
      exact congrFun h2 j
private theorem exists_ofDigits_le_of_sum_eq {h : ℕ} (P : (Fin h → ℕ) → Prop) (r N : ℕ)
    (hex : ∃ β : Fin h → ℕ, (∑ i, β i = r) ∧ P β) :
    ∃ β₀ : Fin h → ℕ, (∑ i, β₀ i = r) ∧ P β₀ ∧
      ∀ β : Fin h → ℕ, (∑ i, β i = r) → P β → ofDigitsFin N β₀ ≤ ofDigitsFin N β := by
  classical
  obtain ⟨β₁, hβ₁, hP₁⟩ := hex
  obtain ⟨β₀, hmem, hmin⟩ := Finset.exists_min_image
    ((multiIndicesOfDegree h r).filter P) (ofDigitsFin N)
    ⟨β₁, Finset.mem_filter.mpr ⟨(mem_multiIndicesOfDegree β₁).mpr hβ₁, hP₁⟩⟩
  rw [Finset.mem_filter, mem_multiIndicesOfDegree] at hmem
  exact ⟨β₀, hmem.1, hmem.2, fun β hβ hPβ =>
    hmin β (Finset.mem_filter.mpr ⟨(mem_multiIndicesOfDegree β).mpr hβ, hPβ⟩)⟩
private theorem sum_notMem_of_unique_notMem {R : Type*} [CommRing R] {I : Ideal R} {ι : Type*}
    [DecidableEq ι] (t : Finset ι) (F : ι → R) (a : ι) (ha : a ∈ t) (hFa : F a ∉ I)
    (hrest : ∀ b ∈ t, b ≠ a → F b ∈ I) : (∑ b ∈ t, F b) ∉ I := by
  intro hsum
  refine hFa ?_
  have h1 : (∑ b ∈ t.erase a, F b) ∈ I :=
    Ideal.sum_mem _ fun b hb => hrest b (Finset.mem_of_mem_erase hb) (Finset.ne_of_mem_erase hb)
  have h2 : F a + ∑ b ∈ t.erase a, F b = ∑ b ∈ t, F b := Finset.add_sum_erase t F ha
  have h3 := sub_mem hsum h1
  rw [← h2, add_sub_cancel_right] at h3
  exact h3
private theorem mul_notMem_maximalIdeal_pow_add_succ {k R : Type*} [CommRing k] [CommRing R]
    [IsLocalRing R] [Algebra k R] {h : ℕ} (x : Fin h → R) (D : Fin h → Derivation k R R)
    (hx : Ideal.span (Set.range x) = IsLocalRing.maximalIdeal R)
    (hD : ∀ i j, D i (x j) = if i = j then 1 else 0)
    (hDD : ∀ i j : Fin h, ∀ a : R, D i (D j a) = D j (D i a))
    (hunit : ∀ n : ℕ, 1 ≤ n → IsUnit ((n : ℕ) : R))
    {r s : ℕ} {f g : R} (hf : f ∈ IsLocalRing.maximalIdeal R ^ r)
    (hnf : f ∉ IsLocalRing.maximalIdeal R ^ (r + 1))
    (hg : g ∈ IsLocalRing.maximalIdeal R ^ s)
    (hng : g ∉ IsLocalRing.maximalIdeal R ^ (s + 1)) :
    f * g ∉ IsLocalRing.maximalIdeal R ^ (r + s + 1) := by
  have hfex : ∃ β : Fin h → ℕ, (∑ i, β i = r) ∧
      multiIndexDeriv D β f ∉ IsLocalRing.maximalIdeal R := by
    by_contra hcon
    push Not at hcon
    refine hnf ((mem_maximalIdeal_pow_succ_iff_multiIndexDeriv_mem x D hx hD hDD hunit r hf).mpr ?_)
    intro β hβ
    exact hcon β ((mem_multiIndicesOfDegree β).mp hβ)
  have hgex : ∃ γ : Fin h → ℕ, (∑ i, γ i = s) ∧
      multiIndexDeriv D γ g ∉ IsLocalRing.maximalIdeal R := by
    by_contra hcon
    push Not at hcon
    refine hng ((mem_maximalIdeal_pow_succ_iff_multiIndexDeriv_mem x D hx hD hDD hunit s hg).mpr ?_)
    intro γ hγ
    exact hcon γ ((mem_multiIndicesOfDegree γ).mp hγ)
  obtain ⟨β₀, hβ₀deg, hβ₀f, hβ₀min⟩ := exists_ofDigits_le_of_sum_eq
    (fun β => multiIndexDeriv D β f ∉ IsLocalRing.maximalIdeal R) r (r + s + 1) hfex
  obtain ⟨γ₀, hγ₀deg, hγ₀g, hγ₀min⟩ := exists_ofDigits_le_of_sum_eq
    (fun γ => multiIndexDeriv D γ g ∉ IsLocalRing.maximalIdeal R) s (r + s + 1) hgex
  obtain ⟨α, hα⟩ : ∃ α : Fin h → ℕ, ∀ i, α i = β₀ i + γ₀ i := ⟨_, fun _ => rfl⟩
  have hαsum : ∑ i, α i = r + s := by
    have hc : ∑ i, α i = ∑ i, (β₀ i + γ₀ i) := Finset.sum_congr rfl fun i _ => hα i
    rw [hc, Finset.sum_add_distrib, hβ₀deg, hγ₀deg]
  have hbase : ofDigitsFin (r + s + 1) α
      = ofDigitsFin (r + s + 1) β₀ + ofDigitsFin (r + s + 1) γ₀ := by
    rw [← ofDigits_add]
    exact congrArg (ofDigitsFin (r + s + 1)) (funext hα)
  intro hmem
  have hfg : f * g ∈ IsLocalRing.maximalIdeal R ^ (r + s) := by
    rw [pow_add]
    exact Ideal.mul_mem_mul hf hg
  have hkey := (mem_maximalIdeal_pow_succ_iff_multiIndexDeriv_mem x D hx hD hDD hunit (r + s) hfg).mp hmem
    α ((mem_multiIndicesOfDegree α).mpr hαsum)
  have hsub := multiIndexDeriv_mul_sub_sum_mem D (IsLocalRing.maximalIdeal R) r s α hαsum hf hg
  have hT := sub_mem hkey hsub
  rw [sub_sub_cancel] at hT
  refine (sum_notMem_of_unique_notMem _ _ β₀ ?_ ?_ ?_) hT
  · rw [Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨fun i => Finset.mem_range.mpr ?_, hβ₀deg⟩
    have := hα i
    omega
  · have hγeq : (fun i => α i - β₀ i) = γ₀ := by
      funext i
      have := hα i
      omega
    rw [hγeq]
    have hcne : (∏ i, (α i).choose (β₀ i)) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro i _
      refine (Nat.choose_pos ?_).ne'
      have := hα i
      omega
    exact IsLocalRing.notMem_maximalIdeal.mpr
      (((hunit _ (Nat.one_le_iff_ne_zero.mpr hcne)).mul
        (IsLocalRing.notMem_maximalIdeal.mp hβ₀f)).mul
        (IsLocalRing.notMem_maximalIdeal.mp hγ₀g))
  · intro β hβt hβne
    rw [Finset.mem_filter, Fintype.mem_piFinset] at hβt
    obtain ⟨hβrange, hβsum⟩ := hβt
    have hβle : ∀ i, β i ≤ α i := fun i =>
      Nat.lt_succ_iff.mp (Finset.mem_range.mp (hβrange i))
    by_cases hcase : multiIndexDeriv D β f ∈ IsLocalRing.maximalIdeal R
    · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hcase)
    · have hmin1 : ofDigitsFin (r + s + 1) β₀ ≤ ofDigitsFin (r + s + 1) β := hβ₀min β hβsum hcase
      have hbβ : ∀ i, β i < r + s + 1 := by
        intro i
        have h1 : β i ≤ r := by
          rw [← hβsum]
          exact Finset.single_le_sum (f := β) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
        omega
      have hbβ₀ : ∀ i, β₀ i < r + s + 1 := by
        intro i
        have h1 : β₀ i ≤ r := by
          rw [← hβ₀deg]
          exact Finset.single_le_sum (f := β₀) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
        omega
      have hne : ofDigitsFin (r + s + 1) β₀ ≠ ofDigitsFin (r + s + 1) β := fun heq =>
        hβne (ofDigits_injective_of_lt (r + s + 1) (by omega) h β β₀ hbβ hbβ₀ heq.symm)
      have hstrict : ofDigitsFin (r + s + 1) β₀ < ofDigitsFin (r + s + 1) β :=
        lt_of_le_of_ne hmin1 hne
      have hγsum : ∑ i, (α i - β i) = s := by
        have h1 : ∑ i, ((α i - β i) + β i) = ∑ i, α i :=
          Finset.sum_congr rfl fun i _ => by
            have := hβle i
            omega
        rw [Finset.sum_add_distrib, hβsum, hαsum] at h1
        omega
      have hsplit : ofDigitsFin (r + s + 1) β + ofDigitsFin (r + s + 1) (fun i => α i - β i)
          = ofDigitsFin (r + s + 1) α := by
        rw [← ofDigits_add]
        exact congrArg (ofDigitsFin (r + s + 1)) (funext fun i => by
          show β i + (α i - β i) = α i
          have := hβle i
          omega)
      have hγlt : ofDigitsFin (r + s + 1) (fun i => α i - β i) < ofDigitsFin (r + s + 1) γ₀ := by
        omega
      have hgmem : multiIndexDeriv D (fun i => α i - β i) g ∈ IsLocalRing.maximalIdeal R := by
        by_contra hcon2
        exact absurd (hγ₀min _ hγsum hcon2) (by omega)
      exact Ideal.mul_mem_left _ _ hgmem
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open IsLocalRing
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {k R : Type*} [CommRing k] [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [Algebra k R] {h : ℕ} (x : Fin h → R) (D : Fin h → Derivation k R R)
    (hx : Ideal.span (Set.range x) = IsLocalRing.maximalIdeal R)
    (hD : ∀ i j, D i (x j) = if i = j then 1 else 0)
    (hDD : ∀ i j : Fin h, ∀ a : R, D i (D j a) = D j (D i a))
    (hunit : ∀ n : ℕ, 1 ≤ n → IsUnit ((n : ℕ) : R)) (I J : Ideal R) :
    idealOrder (I * J) = idealOrder I + idealOrder J := by
  by_cases hI : I = ⊥
  · subst hI
    have hbm : (⊥ : Ideal R) * J = ⊥ := by
      refine le_antisymm (Ideal.mul_le.mpr ?_) bot_le
      intro a ha b _
      rw [Ideal.mem_bot] at ha ⊢
      rw [ha, zero_mul]
    rw [hbm, idealOrder_bot]
    exact le_antisymm le_self_add le_top
  · by_cases hJ : J = ⊥
    · subst hJ
      have hbm : I * (⊥ : Ideal R) = ⊥ := by
        refine le_antisymm (Ideal.mul_le.mpr ?_) bot_le
        intro a _ b hb
        rw [Ideal.mem_bot] at hb ⊢
        rw [hb, mul_zero]
      rw [hbm, idealOrder_bot]
      exact le_antisymm le_add_self le_top
    · obtain ⟨r, hr⟩ := exists_idealOrder_eq_coe hI
      obtain ⟨s, hs⟩ := exists_idealOrder_eq_coe hJ
      have hIr : I ≤ IsLocalRing.maximalIdeal R ^ r :=
        (le_idealOrder_iff I r).mp (le_of_eq hr.symm)
      have hJs : J ≤ IsLocalRing.maximalIdeal R ^ s :=
        (le_idealOrder_iff J s).mp (le_of_eq hs.symm)
      have hIn : ¬ I ≤ IsLocalRing.maximalIdeal R ^ (r + 1) := by
        intro hc
        have hle := (le_idealOrder_iff I (r + 1)).mpr hc
        rw [hr] at hle
        have hnat : r + 1 ≤ r := by exact_mod_cast hle
        omega
      have hJn : ¬ J ≤ IsLocalRing.maximalIdeal R ^ (s + 1) := by
        intro hc
        have hle := (le_idealOrder_iff J (s + 1)).mpr hc
        rw [hs] at hle
        have hnat : s + 1 ≤ s := by exact_mod_cast hle
        omega
      obtain ⟨a, haI, han⟩ : ∃ a ∈ I, a ∉ IsLocalRing.maximalIdeal R ^ (r + 1) := by
        by_contra hc
        push Not at hc
        exact hIn fun y hy => hc y hy
      obtain ⟨b, hbJ, hbn⟩ : ∃ b ∈ J, b ∉ IsLocalRing.maximalIdeal R ^ (s + 1) := by
        by_contra hc
        push Not at hc
        exact hJn fun y hy => hc y hy
      have hmul : a * b ∉ IsLocalRing.maximalIdeal R ^ (r + s + 1) :=
        mul_notMem_maximalIdeal_pow_add_succ x D hx hD hDD hunit (hIr haI) han (hJs hbJ) hbn
      have h1 : ¬ I * J ≤ IsLocalRing.maximalIdeal R ^ (r + s + 1) := fun hc =>
        hmul (hc (Ideal.mul_mem_mul haI hbJ))
      have h2 : I * J ≤ IsLocalRing.maximalIdeal R ^ (r + s) := by
        rw [pow_add]
        exact Ideal.mul_mono hIr hJs
      rw [idealOrder_eq_of_le_of_not_le h2 h1, hr, hs]
      exact Nat.cast_add r s
end FunctorialResolution.EmbeddedResolution
