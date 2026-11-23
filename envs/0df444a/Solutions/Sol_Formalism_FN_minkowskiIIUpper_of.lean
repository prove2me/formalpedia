-- Prove2me | solution 1 for Formalism.FN.minkowskiIIUpper_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:45:53.542436+00:00
-- url     : https://prove2.me/submissions/3faae5bb-6b7b-4cb5-9a4a-3a5ae3187935

import Definitions.Def_Formalism_SuccessiveMinima_DefsMink
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_MeasureEqCovolumeMulVolumeImage
import Theorems.Thm_Formalism_FN_measure_eq_covolume_mul_volume_image

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module Metric Set
open scoped Pointwise ENNReal
noncomputable section
open Formalism Formalism.FN
namespace Formalism.FN
theorem _root_.solution (hc : MinkCore) (hs : SuccMinFacts) (ha : AdaptedBasis) :
    MinkowskiIIUpper := by
  intro E _ _ _ _ _ μ _ L _ _ K hKc hKconv hKsymm hK0
  obtain ⟨v, hvli, hvL, hvK, hpos, hmono, hspan⟩ := hs L K hKc hKconv hKsymm hK0
  obtain ⟨b, hb⟩ := ha L v hvli hvL
  set B := b.ofZLatticeBasis ℝ L with hB
  have hBfun : ∀ i, B i = (b i : E) := fun i => by simp [hB]
  set lam : Fin (finrank ℝ E) → ℝ := fun i => succMin L K ((i : ℕ) + 1) with hlam
  have hneg : ∀ a ∈ interior K, -a ∈ interior K := by
    intro a ha'
    have hU : IsOpen ((fun x : E => -x) ⁻¹' interior K) := isOpen_interior.preimage continuous_neg
    have hsub : (fun x : E => -x) ⁻¹' interior K ⊆ K := fun x hx => by
      simpa using hKsymm _ (interior_subset hx)
    exact interior_maximal hsub hU (by simpa using ha')
  have hCo : IsOpen (B.equivFun '' ((1 / 2 : ℝ) • interior K)) :=
    B.equivFunL.toHomeomorph.isOpenMap _ (isOpen_interior.smul₀ (by norm_num))
  have hCc : Convex ℝ (B.equivFun '' ((1 / 2 : ℝ) • interior K)) :=
    (hKconv.interior.smul (1 / 2 : ℝ)).linear_image B.equivFun.toLinearMap
  have hCs : ∀ x ∈ B.equivFun '' ((1 / 2 : ℝ) • interior K),
      -x ∈ B.equivFun '' ((1 / 2 : ℝ) • interior K) := by
    rintro _ ⟨w, hw, rfl⟩
    rw [Set.mem_smul_set] at hw
    obtain ⟨a, ha', rfl⟩ := hw
    exact ⟨(1 / 2 : ℝ) • -a, Set.smul_mem_smul_set (hneg a ha'), by rw [smul_neg, map_neg]⟩
  have hCb : Bornology.IsBounded (B.equivFun '' ((1 / 2 : ℝ) • interior K)) :=
    B.equivFunL.lipschitz.isBounded_image ((hKc.isBounded.subset interior_subset).smul₀ _)
  have key := hc (finrank ℝ E) (B.equivFun '' ((1 / 2 : ℝ) • interior K)) lam hCo hCc hCs hCb
    hpos hmono (by
      intro j x hx y hy hint i hji
      rw [Set.mem_smul_set] at hx hy
      obtain ⟨_, ⟨w, hw, rfl⟩, rfl⟩ := hx
      obtain ⟨_, ⟨w', hw', rfl⟩, rfl⟩ := hy
      rw [Set.mem_smul_set] at hw hw'
      obtain ⟨a, ha', rfl⟩ := hw
      obtain ⟨a', ha'', rfl⟩ := hw'
      obtain ⟨u, hu⟩ : ∃ u, u = lam j • ((1 / 2 : ℝ) • a - (1 / 2 : ℝ) • a') := ⟨_, rfl⟩
      have heu : B.equivFun u =
          lam j • B.equivFun ((1 / 2 : ℝ) • a) - lam j • B.equivFun ((1 / 2 : ℝ) • a') := by
        rw [hu, map_smul B.equivFun (lam j), map_sub, smul_sub]
      have hrepr : ∀ i, B.repr u i =
          (lam j • B.equivFun ((1 / 2 : ℝ) • a)) i - (lam j • B.equivFun ((1 / 2 : ℝ) • a')) i := by
        intro i
        have h := congrFun heu i
        rw [B.equivFun_apply] at h
        exact h
      have huL : u ∈ L := by
        rw [← B.sum_repr u]
        refine sum_mem fun i _ => ?_
        obtain ⟨m, hm⟩ := hint i
        rw [hrepr i, hm, hBfun i]
        rw [Int.cast_smul_eq_zsmul ℝ m]
        exact L.smul_mem m (b i).2
      have hmid : (1 / 2 : ℝ) • a - (1 / 2 : ℝ) • a' ∈ interior K := by
        rw [sub_eq_add_neg, ← smul_neg]
        exact hKconv.interior ha' (hneg a' ha'') (by norm_num) (by norm_num) (by norm_num)
      have hmem : u ∈ Submodule.span ℝ (v '' {k | k < j}) :=
        hspan j u huL (by rw [hu]; exact Set.smul_mem_smul_set hmid)
      have hsub : Submodule.span ℝ (v '' {k | k < j}) ≤ Submodule.span ℝ (B '' {k | k < j}) := by
        rw [Submodule.span_le]
        rintro _ ⟨k, hk, rfl⟩
        have h1 : v k ∈ Submodule.span ℝ (v '' {k' | k' ≤ k}) :=
          Submodule.subset_span ⟨k, le_refl k, rfl⟩
        rw [← hb k] at h1
        refine Submodule.span_mono ?_ h1
        rintro _ ⟨k', hk', rfl⟩
        exact ⟨k', show k' < j from lt_of_le_of_lt hk' hk, hBfun k'⟩
      have hsupp := (B.mem_span_image).mp (hsub hmem)
      have hz : B.repr u i = 0 := by
        by_contra h
        exact absurd (hsupp (Finsupp.mem_support_iff.mpr h)) (not_lt.mpr hji)
      have h0 := hrepr i
      rw [hz] at h0
      exact sub_eq_zero.mp h0.symm)
  have hthm := measure_eq_covolume_mul_volume_image μ L b ((1 / 2 : ℝ) • interior K)
  rw [← hB] at hthm
  have hhalf : μ ((1 / 2 : ℝ) • interior K) =
      ENNReal.ofReal ((1 / 2 : ℝ) ^ finrank ℝ E) * μ (interior K) := by
    rw [Measure.addHaar_smul, abs_of_pos (by positivity : (0 : ℝ) < (1 / 2 : ℝ) ^ finrank ℝ E)]
  have hKfin : μ K < ⊤ := hKc.measure_lt_top
  have hIfin : μ (interior K) < ⊤ := lt_of_le_of_lt (measure_mono interior_subset) hKfin
  have hKle : μ K ≤ μ (interior K) := by
    calc μ K ≤ μ (interior K ∪ frontier K) := by
          apply measure_mono
          intro x hx
          rw [← closure_eq_interior_union_frontier]
          exact subset_closure hx
      _ ≤ μ (interior K) + μ (frontier K) := measure_union_le _ _
      _ = μ (interior K) := by rw [hKconv.addHaar_frontier μ, add_zero]
  have hP : 0 ≤ ∏ i, lam i := Finset.prod_nonneg fun i _ => (hpos i).le
  have hc0 : 0 ≤ ZLattice.covolume L μ := (ZLattice.covolume_pos L μ).le
  have e1 : (μ ((1 / 2 : ℝ) • interior K)).toReal =
      ZLattice.covolume L μ * (volume (B.equivFun '' ((1 / 2 : ℝ) • interior K))).toReal := by
    rw [hthm, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc0]
  have e2 : (μ ((1 / 2 : ℝ) • interior K)).toReal =
      (1 / 2 : ℝ) ^ finrank ℝ E * (μ (interior K)).toReal := by
    rw [hhalf, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  have e3 : (μ (interior K)).toReal = 2 ^ finrank ℝ E * (ZLattice.covolume L μ *
      (volume (B.equivFun '' ((1 / 2 : ℝ) • interior K))).toReal) := by
    have h2 : (2 : ℝ) ^ finrank ℝ E * (1 / 2 : ℝ) ^ finrank ℝ E = 1 := by
      rw [← mul_pow]
      norm_num
    calc (μ (interior K)).toReal
        = 2 ^ finrank ℝ E * ((1 / 2 : ℝ) ^ finrank ℝ E * (μ (interior K)).toReal) := by
          rw [← mul_assoc, h2, one_mul]
      _ = _ := by rw [← e2, e1]
  have hK' : μ.real K ≤ (μ (interior K)).toReal := ENNReal.toReal_mono hIfin.ne hKle
  calc μ.real K * ∏ i, lam i ≤ (μ (interior K)).toReal * ∏ i, lam i :=
        mul_le_mul_of_nonneg_right hK' hP
    _ = 2 ^ finrank ℝ E * ZLattice.covolume L μ *
        ((volume (B.equivFun '' ((1 / 2 : ℝ) • interior K))).toReal * ∏ i, lam i) := by
          rw [e3]
          ring
    _ ≤ 2 ^ finrank ℝ E * ZLattice.covolume L μ * 1 :=
        mul_le_mul_of_nonneg_left key (mul_nonneg (by positivity) hc0)
    _ = _ := mul_one _
end Formalism.FN
