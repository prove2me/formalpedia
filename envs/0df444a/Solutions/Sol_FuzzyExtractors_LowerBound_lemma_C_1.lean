-- Prove2me | solution 1 for FuzzyExtractors.LowerBound.lemma_C_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-20T09:18:00.672992+00:00
-- url     : https://prove2.me/submissions/ffb9b8a2-8f24-46c9-b692-06c2aa1134f0

/-
SPDX-License-Identifier: Apache-2.0
Original Lean proof of the secure-sketch coding lower bound, Lemma C.1.
Mathematical source: Dodis, Ostrovsky, Reyzin and Smith, Fuzzy Extractors,
arXiv:cs/0602007v4, Appendix C, printed pages 40-41.
Native Prove2Me definitions are imported unchanged. No accepted proof source is copied.
This proof uses a direct joint-mass inequality over arbitrary sketch outputs.
-/
import Mathlib
import Definitions.Def_FuzzyExtractors_LowerBound_Basic

-- BEGIN Foundation
open scoped ENNReal
-- END Foundation

-- BEGIN JointMass
namespace FuzzyLowerBoundProof

open scoped ENNReal

theorem joint_withSketch_apply {M V : Type} (SS : M → PMF V) (W : PMF M)
    (w : M) (v : V) :
    FuzzyExtractors.Hamming.withSketch SS W (w, v) = W w * SS w v := by
  classical
  rw [FuzzyExtractors.Hamming.withSketch, PMF.bind_apply]
  calc
    _ = ∑' a, if w = a then W a * SS a v else 0 := by
      apply tsum_congr
      intro a
      rw [PMF.map_apply]
      by_cases h : w = a
      · subst a
        simp
      · simp [Prod.mk.injEq, h]
    _ = W w * SS w v := by simp

end FuzzyLowerBoundProof
-- END JointMass

-- BEGIN EntropyBound
namespace FuzzyLowerBoundProof

open scoped ENNReal

noncomputable def guessingMass {M V : Type} (J : PMF (M × V)) : ℝ≥0∞ :=
  ∑' v, ⨆ w, J (w, v)

theorem column_mass_total {M V : Type} [Fintype M] (J : PMF (M × V)) :
    ∑' v, ∑ w, J (w, v) = 1 := by
  rw [← J.tsum_coe, ENNReal.tsum_prod', ENNReal.tsum_comm]
  simp only [tsum_fintype]

theorem guessingMass_le_one {M V : Type} [Fintype M] (J : PMF (M × V)) :
    guessingMass J ≤ 1 := by
  rw [guessingMass, ← column_mass_total J]
  apply ENNReal.tsum_le_tsum
  intro v
  apply iSup_le
  intro w
  exact Finset.single_le_sum (f := fun x : M => J (x, v))
    (fun _ _ => zero_le) (Finset.mem_univ w)

theorem one_le_card_mul_guessing {M V : Type} [Fintype M]
    (J : PMF (M × V)) (k : ℕ) (T : V → Finset M)
    (hzero : ∀ w v, w ∉ T v → J (w, v) = 0)
    (hcard : ∀ v, (T v).card ≤ k) : 1 ≤ (k : ℝ≥0∞) * guessingMass J := by
  classical
  rw [← column_mass_total J, guessingMass, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro v
  calc
    ∑ w, J (w, v) = ∑ w ∈ T v, J (w, v) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro w _ hw
      exact hzero w v hw
    _ ≤ ∑ _w ∈ T v, (⨆ w, J (w, v)) :=
      Finset.sum_le_sum (fun w _ => le_iSup (fun w => J (w, v)) w)
    _ = ((T v).card : ℝ≥0∞) * (⨆ w, J (w, v)) := by simp
    _ ≤ (k : ℝ≥0∞) * (⨆ w, J (w, v)) :=
      mul_le_mul_left (show ((T v).card : ℝ≥0∞) ≤ (k : ℝ≥0∞) by
        exact_mod_cast hcard v) _

theorem avgMinEntropy_le_log_of_fiber_bound {M V : Type} [Fintype M]
    (J : PMF (M × V)) (k : ℕ) (hk : 0 < k) (T : V → Finset M)
    (hzero : ∀ w v, w ∉ T v → J (w, v) = 0)
    (hcard : ∀ v, (T v).card ≤ k) :
    FuzzyExtractors.Hamming.avgMinEntropy J ≤ Real.logb 2 k := by
  have hg1 := guessingMass_le_one J
  have hmass := one_le_card_mul_guessing J k T hzero hcard
  have hgfin : guessingMass J ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hg1
  have hgzero : guessingMass J ≠ 0 := by
    intro h
    simp only [h, mul_zero] at hmass
    exact not_le_of_gt zero_lt_one hmass
  have hgpos := ENNReal.toReal_pos hgzero hgfin
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hreal : (1 : ℝ) ≤ (k : ℝ) * (guessingMass J).toReal := by
    have ht := (ENNReal.toReal_le_toReal ENNReal.one_ne_top
      (ENNReal.mul_ne_top (by simp) hgfin)).2 hmass
    simpa using ht
  have hinv : (k : ℝ)⁻¹ ≤ (guessingMass J).toReal := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hkpos).2
    simpa [mul_comm] using hreal
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (inv_pos.mpr hkpos) hinv
  rw [Real.logb_inv] at hlog
  change -Real.logb 2 (guessingMass J).toReal ≤ Real.logb 2 k
  linarith

end FuzzyLowerBoundProof
-- END EntropyBound

-- BEGIN UniformEntropy
namespace FuzzyLowerBoundProof

open scoped ENNReal

theorem minEntropy_uniform {M : Type} (S : Finset M) (hS : S.Nonempty) :
    FuzzyExtractors.Hamming.minEntropy (PMF.uniformOfFinset S hS) =
      Real.logb 2 (S.card : ℝ) := by
  classical
  have hsup : (⨆ w, PMF.uniformOfFinset S hS w) = (S.card : ℝ≥0∞)⁻¹ := by
    apply le_antisymm
    · apply iSup_le
      intro w
      by_cases hw : w ∈ S
      · simp only [PMF.uniformOfFinset_apply_of_mem hS hw, le_refl]
      · simp only [PMF.uniformOfFinset_apply_of_notMem hS hw, zero_le]
    · let w := hS.choose
      have hw : w ∈ S := hS.choose_spec
      calc
        (S.card : ℝ≥0∞)⁻¹ = PMF.uniformOfFinset S hS w :=
          (PMF.uniformOfFinset_apply_of_mem hS hw).symm
        _ ≤ ⨆ a, PMF.uniformOfFinset S hS a := le_iSup _ w
  rw [FuzzyExtractors.Hamming.minEntropy, hsup, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, Real.logb_inv, neg_neg]

theorem minEntropy_uniform_eq {M : Type} (S : Finset M) (hS : S.Nonempty)
    (m : ℝ) (hm : (S.card : ℝ) = (2 : ℝ) ^ m) :
    FuzzyExtractors.Hamming.minEntropy (PMF.uniformOfFinset S hS) = m := by
  rw [minEntropy_uniform, hm, Real.logb_rpow (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (2 : ℝ) ≠ 1)]

end FuzzyLowerBoundProof
-- END UniformEntropy

-- BEGIN CodeCore
namespace FuzzyLowerBoundProof

open FuzzyExtractors.Hamming FuzzyExtractors.LowerBound

theorem code_card_le_K {M : Type} (dis : M → M → ℕ) (t : ℕ)
    (S C : Finset M) (hCS : C ⊆ S) (hC : IsCode dis C t) :
    C.card ≤ K dis t S := by
  classical
  exact Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hCS, hC⟩)

theorem K_pos {M : Type} (dis : M → M → ℕ) (t : ℕ)
    (S : Finset M) (hS : S.Nonempty) : 0 < K dis t S := by
  classical
  obtain ⟨w, hw⟩ := hS
  have hc : IsCode dis {w} t := by
    intro z c hc c' hc' _ _
    exact (Finset.mem_singleton.mp hc).trans (Finset.mem_singleton.mp hc').symm
  have hcard := code_card_le_K dis t S {w} (Finset.singleton_subset_iff.mpr hw) hc
  simpa only [Finset.card_singleton, Nat.succ_le_iff] using hcard

theorem producers_isCode {M V : Type} (dis : M → M → ℕ)
    (hsymm : ∀ x y, dis x y = dis y x) (t : ℕ)
    (SS : M → PMF V) (Rec : M → V → PMF M)
    (hcorrect : SketchCorrect dis t SS Rec) (S : Finset M) (v : V) :
    IsCode dis (producers SS S v) t := by
  classical
  intro z c hc c' hc' hzc hzc'
  have hcv : v ∈ (SS c).support := (Finset.mem_filter.mp hc).2
  have hc'v : v ∈ (SS c').support := (Finset.mem_filter.mp hc').2
  have h1 : Rec z v = PMF.pure c :=
    hcorrect c z (by simpa only [hsymm c z] using hzc) v hcv
  have h2 : Rec z v = PMF.pure c' :=
    hcorrect c' z (by simpa only [hsymm c' z] using hzc') v hc'v
  have h := congrArg (fun P : PMF M => P c) (h1.symm.trans h2)
  by_contra hne
  simp [PMF.pure_apply, hne] at h

theorem producers_card_le_K {M V : Type} (dis : M → M → ℕ)
    (hsymm : ∀ x y, dis x y = dis y x) (t : ℕ)
    (SS : M → PMF V) (Rec : M → V → PMF M)
    (hcorrect : SketchCorrect dis t SS Rec) (S : Finset M) (v : V) :
    (producers SS S v).card ≤ K dis t S := by
  classical
  exact code_card_le_K dis t S _ (Finset.filter_subset _ S)
    (producers_isCode dis hsymm t SS Rec hcorrect S v)

end FuzzyLowerBoundProof
-- END CodeCore

-- BEGIN NativeRoot
namespace FuzzyLowerBoundProof

open FuzzyExtractors.Hamming FuzzyExtractors.LowerBound

theorem entropy_le_log_K {M V : Type} [Fintype M] (dis : M → M → ℕ)
    (hsymm : ∀ x y, dis x y = dis y x) (m m' : ℝ) (t : ℕ)
    (SS : M → PMF V) (Rec : M → V → PMF M)
    (hSS : IsSecureSketch dis m m' t SS Rec)
    (S : Finset M) (hS : S.Nonempty) (hSm : (S.card : ℝ) = (2 : ℝ) ^ m) :
    m' ≤ Real.logb 2 (K dis t S : ℝ) := by
  classical
  let W := PMF.uniformOfFinset S hS
  have hsecurity : m' ≤ avgMinEntropy (withSketch SS W) :=
    hSS.2 W (le_of_eq (minEntropy_uniform_eq S hS m hSm).symm)
  have hvanish : ∀ w v, w ∉ producers SS S v → withSketch SS W (w, v) = 0 := by
    intro w v hwv
    rw [joint_withSketch_apply]
    by_cases hw : w ∈ S
    · have hv : v ∉ (SS w).support := by
        intro hv
        exact hwv (Finset.mem_filter.mpr ⟨hw, hv⟩)
      rw [((SS w).apply_eq_zero_iff v).mpr hv, mul_zero]
    · rw [PMF.uniformOfFinset_apply_of_notMem hS hw, zero_mul]
  exact hsecurity.trans (avgMinEntropy_le_log_of_fiber_bound
    (withSketch SS W) (K dis t S) (K_pos dis t S hS) (producers SS S)
    hvanish (producers_card_le_K dis hsymm t SS Rec hSS.1 S))

theorem secure_sketch_coding_bound {M V : Type} [Fintype M] (dis : M → M → ℕ)
    (hsymm : ∀ x y, dis x y = dis y x) (m m' : ℝ) (t : ℕ)
    (SS : M → PMF V) (Rec : M → V → PMF M)
    (hSS : IsSecureSketch dis m m' t SS Rec)
    (N : ℕ) (hN : N ≤ Fintype.card M) (hNm : (N : ℝ) = (2 : ℝ) ^ m) :
    m' ≤ L dis t N hN := by
  classical
  have hNpos : 0 < N := by
    have hNr : (0 : ℝ) < N := by rw [hNm]; positivity
    exact_mod_cast hNr
  have hfamily : (Finset.univ.powersetCard N : Finset (Finset M)).Nonempty :=
    Finset.powersetCard_nonempty.2 (by simpa using hN)
  obtain ⟨S, hS, hmin⟩ :=
    Finset.exists_mem_eq_inf' hfamily (fun S => (K dis t S : ℝ))
  have hcard : S.card = N := (Finset.mem_powersetCard.mp hS).2
  have hSne : S.Nonempty := Finset.card_pos.mp (by simpa only [hcard] using hNpos)
  have hSm : (S.card : ℝ) = (2 : ℝ) ^ m := by rw [hcard, hNm]
  have hbound := entropy_le_log_K dis hsymm m m' t SS Rec hSS S hSne hSm
  simpa only [L, hmin] using hbound

end FuzzyLowerBoundProof


namespace FuzzyExtractors.LowerBound

/-- Lemma C.1 (Appendix C, p. 40): the existence of an (𝓜, m, m', t)-secure sketch implies
`m' ≤ L(𝓜, t, m)`, where `2^m = N` is a natural number with `N ≤ |𝓜|`. -/
theorem lemma_C_1 {M V : Type} [Fintype M] (dis : M → M → ℕ)
    (hzero : ∀ x y, dis x y = 0 ↔ x = y)
    (hsymm : ∀ x y, dis x y = dis y x)
    (htri : ∀ x y z, dis x z ≤ dis x y + dis y z)
    (m m' : ℝ) (t : ℕ)
    (SS : M → PMF V) (Rec : M → V → PMF M) (hSS : FuzzyExtractors.Hamming.IsSecureSketch dis m m' t SS Rec)
    (N : ℕ) (hN : N ≤ Fintype.card M) (hNm : (N : ℝ) = (2 : ℝ) ^ m) :
    m' ≤ L dis t N hN := by
  have _ := hzero
  have _ := htri
  exact FuzzyLowerBoundProof.secure_sketch_coding_bound dis hsymm m m' t
    SS Rec hSS N hN hNm

end FuzzyExtractors.LowerBound
-- END NativeRoot

theorem solution {M V : Type} [Fintype M] (dis : M → M → ℕ)
    (hzero : ∀ x y, dis x y = 0 ↔ x = y)
    (hsymm : ∀ x y, dis x y = dis y x)
    (htri : ∀ x y z, dis x z ≤ dis x y + dis y z)
    (m m' : ℝ) (t : ℕ)
    (SS : M → PMF V) (Rec : M → V → PMF M)
    (hSS : FuzzyExtractors.Hamming.IsSecureSketch dis m m' t SS Rec)
    (N : ℕ) (hN : N ≤ Fintype.card M) (hNm : (N : ℝ) = (2 : ℝ) ^ m) :
    m' ≤ FuzzyExtractors.LowerBound.L dis t N hN :=
  FuzzyExtractors.LowerBound.lemma_C_1 dis hzero hsymm htri m m' t SS Rec hSS N hN hNm
