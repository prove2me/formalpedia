-- Prove2me | solution 1 for FuzzyGames.NTUCore.eq_7_11
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T20:01:39.552205+00:00
-- url     : https://prove2.me/submissions/8b8113ff-6445-4b79-ab58-aa6b60e4bd59

import Mathlib
import Definitions.Def_FuzzyGames_NTUCore_Basic

open Set Finset Pointwise

namespace FuzzyGames.NTUCore.Aux
open FuzzyGames.NTUCore

theorem mem_piV {n : ℕ} (𝒞 : CoalFamily n) (V : Finset (Fin n) → Set (Fin n → ℝ))
    (τ x : Fin n → ℝ) :
    x ∈ piV 𝒞 V τ ↔ ∃ m ∈ balances 𝒞 τ, ∃ w : Finset (Fin n) → Fin n → ℝ,
      (∀ A ∈ 𝒞.C, w A ∈ V A) ∧ ∑ A ∈ 𝒞.C, m A • w A = x := by
  classical
  unfold piV
  simp only [Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨m, hm, hx⟩
    rw [Set.mem_finsetSum] at hx
    obtain ⟨g, hg, rfl⟩ := hx
    have : ∀ A ∈ 𝒞.C, ∃ w ∈ V A, m A • w = g A := fun A hA => by
      simpa [Set.mem_smul_set] using hg hA
    choose! w hw hw' using this
    exact ⟨m, hm, w, hw, Finset.sum_congr rfl (fun A hA => hw' A hA)⟩
  · rintro ⟨m, hm, w, hw, rfl⟩
    exact ⟨m, hm, Set.finsetSum_mem_finsetSum _ _ _ (fun A hA =>
      Set.smul_mem_smul_set (hw A hA))⟩


theorem ereal_sum_coe {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ∑ i ∈ s, ((f i : ℝ) : EReal) = ((∑ i ∈ s, f i : ℝ) : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, EReal.coe_add]

section
variable {n : ℕ} {𝒞 : CoalFamily n} {V : Finset (Fin n) → Set (Fin n → ℝ)}

noncomputable def rA (V : Finset (Fin n) → Set (Fin n → ℝ)) (A : Finset (Fin n))
    (l : Fin n → ℝ) : ℝ := sSup ((fun w => ∑ i ∈ A, l i * w i) '' V A)

theorem bddA (hV : IsNTUGame 𝒞 V) {A : Finset (Fin n)} (hA : A ∈ 𝒞.C) {l : Fin n → ℝ}
    (hl : ∀ i, 0 ≤ l i) : BddAbove ((fun w => ∑ i ∈ A, l i * w i) '' V A) := by
  obtain ⟨C, _, hC⟩ := hV.bddAbove A hA
  refine ⟨∑ i ∈ A, l i * C i, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨c, hc, p, hp, hcp⟩ := Set.mem_sub.1 (hC hw)
  rw [Set.mem_singleton_iff] at hc
  subst hc
  apply Finset.sum_le_sum; intro i _
  apply mul_le_mul_of_nonneg_left _ (hl i)
  rw [← hcp]; simp only [Pi.sub_apply]; linarith [hp.2 i]

theorem le_rA (hV : IsNTUGame 𝒞 V) {A : Finset (Fin n)} (hA : A ∈ 𝒞.C) {l : Fin n → ℝ}
    (hl : ∀ i, 0 ≤ l i) {w : Fin n → ℝ} (hw : w ∈ V A) : ∑ i ∈ A, l i * w i ≤ rA V A l :=
  le_csSup (bddA hV hA hl) ⟨w, hw, rfl⟩

theorem coalSupport_eq (hV : IsNTUGame 𝒞 V) {A : Finset (Fin n)} (hA : A ∈ 𝒞.C)
    {l : Fin n → ℝ} (hl : ∀ i, 0 ≤ l i) : coalSupport V A l = ((rA V A l : ℝ) : EReal) := by
  apply le_antisymm
  · unfold coalSupport
    exact iSup₂_le fun w hw => EReal.coe_le_coe_iff.2 (le_rA hV hA hl hw)
  · by_contra h
    push_neg at h
    obtain ⟨b, hb1, hb2⟩ := EReal.lt_iff_exists_real_btwn.1 h
    rw [EReal.coe_lt_coe_iff] at hb2
    obtain ⟨_, ⟨w, hw, rfl⟩, hlt⟩ :=
      exists_lt_of_lt_csSup ((hV.nonempty A hA).image _) hb2
    have : ((∑ i ∈ A, l i * w i : ℝ) : EReal) ≤ coalSupport V A l := by
      unfold coalSupport
      exact le_iSup₂ (f := fun c (_ : c ∈ V A) => ((∑ i ∈ A, l i * c i : ℝ) : EReal)) w hw
    have := this.trans_lt hb1
    rw [EReal.coe_lt_coe_iff] at this
    linarith

theorem sum_A_eq_sum (A : Finset (Fin n)) (l w : Fin n → ℝ) (hw : w ∈ Rtau (coal A)) :
    ∑ i ∈ A, l i * w i = ∑ i, l i * w i := by
  classical
  apply Finset.sum_subset (Finset.subset_univ A)
  intro i _ hi
  have : w i = 0 := hw i (by simp [coal, hi])
  simp [this]

end

end FuzzyGames.NTUCore.Aux

open FuzzyGames.NTUCore FuzzyGames.NTUCore.Aux in
theorem solution {n : ℕ} (𝒞 : CoalFamily n) {V : Finset (Fin n) → Set (Fin n → ℝ)}
    (hV : IsNTUGame 𝒞 V) :
    ∀ τ ∈ orthant n, ∀ l : Fin n → ℝ, (∀ i, 0 ≤ l i) →
      supportFn (piV 𝒞 V τ) l = piv 𝒞 V τ l := by
  classical
  intro τ _ l hl
  have hpiv : piv 𝒞 V τ l = ⨆ m ∈ balances 𝒞 τ,
      ((∑ A ∈ 𝒞.C, m A * rA V A l : ℝ) : EReal) := by
    unfold piv
    congr 1; ext m; congr 1; ext _
    rw [← ereal_sum_coe]
    apply Finset.sum_congr rfl; intro A hA
    rw [coalSupport_eq hV hA hl, ← EReal.coe_mul]
  rw [hpiv]
  apply le_antisymm
  · unfold supportFn
    refine iSup₂_le fun x hx => ?_
    obtain ⟨m, hm, w, hw, rfl⟩ := (mem_piV 𝒞 V τ x).1 hx
    refine le_trans ?_ (le_iSup₂ (f := fun m (_ : m ∈ balances 𝒞 τ) =>
      ((∑ A ∈ 𝒞.C, m A * rA V A l : ℝ) : EReal)) m hm)
    rw [EReal.coe_le_coe_iff]
    calc ∑ i, l i * (∑ A ∈ 𝒞.C, m A • w A) i
        = ∑ A ∈ 𝒞.C, m A * ∑ i, l i * w A i := by
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro A _; apply Finset.sum_congr rfl; intro i _; ring
      _ ≤ ∑ A ∈ 𝒞.C, m A * rA V A l := by
          apply Finset.sum_le_sum; intro A hA
          apply mul_le_mul_of_nonneg_left _ (hm.1 A)
          rw [← sum_A_eq_sum A l (w A) (hV.subset_Rtau A hA (hw A hA))]
          exact le_rA hV hA hl (hw A hA)
  · refine iSup₂_le fun m hm => ?_
    apply le_of_forall_lt
    intro c hc
    obtain ⟨b, hb1, hb2⟩ := EReal.lt_iff_exists_real_btwn.1 hc
    rw [EReal.coe_lt_coe_iff] at hb2
    refine hb1.trans_le ?_
    set Msum := ∑ A ∈ 𝒞.C, m A with hMsum
    have hM0 : 0 ≤ Msum := Finset.sum_nonneg fun A _ => hm.1 A
    set gap := ∑ A ∈ 𝒞.C, m A * rA V A l - b
    have hgap : 0 < gap := by simp only [gap]; linarith
    set ε := gap / (Msum + 1)
    have hε : 0 < ε := div_pos hgap (by linarith)
    have hεM : ε * Msum < gap := by
      have : ε * (Msum + 1) = gap := div_mul_cancel₀ _ (by linarith)
      nlinarith
    have hex : ∀ A ∈ 𝒞.C, ∃ w ∈ V A, rA V A l - ε < ∑ i ∈ A, l i * w i := by
      intro A hA
      obtain ⟨_, ⟨w, hw, rfl⟩, hlt⟩ :=
        exists_lt_of_lt_csSup ((hV.nonempty A hA).image _) (by linarith : rA V A l - ε < rA V A l)
      exact ⟨w, hw, hlt⟩
    choose! w hw hwlt using hex
    have hx : ∑ A ∈ 𝒞.C, m A • w A ∈ piV 𝒞 V τ := (mem_piV 𝒞 V τ _).2 ⟨m, hm, w, hw, rfl⟩
    refine le_trans ?_ (le_iSup₂ (f := fun x (_ : x ∈ piV 𝒞 V τ) =>
      ((∑ i, l i * x i : ℝ) : EReal)) _ hx)
    rw [EReal.coe_le_coe_iff]
    have e : ∑ i, l i * (∑ A ∈ 𝒞.C, m A • w A) i = ∑ A ∈ 𝒞.C, m A * ∑ i ∈ A, l i * w A i := by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro A hA
      rw [← Finset.mul_sum, sum_A_eq_sum A l (w A) (hV.subset_Rtau A hA (hw A hA)),
        Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i _; ring
    rw [e]
    have : ∑ A ∈ 𝒞.C, m A * (rA V A l - ε) ≤ ∑ A ∈ 𝒞.C, m A * ∑ i ∈ A, l i * w A i :=
      Finset.sum_le_sum fun A hA => mul_le_mul_of_nonneg_left (hwlt A hA).le (hm.1 A)
    have e2 : ∑ A ∈ 𝒞.C, m A * (rA V A l - ε) = ∑ A ∈ 𝒞.C, m A * rA V A l - ε * Msum := by
      rw [hMsum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro A _; ring
    simp only [gap] at hεM
    linarith
