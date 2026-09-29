-- Prove2me | solution 1 for FrobeniusDensity.tendsto_sub_one_mul_idealSum_test
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/d599fce5-3198-506f-aafc-776d7e8e63bf

import Theorems.Thm_FrobeniusDensity_idealSum_ne_top
import Definitions.Def_FrobeniusDensity_PrimeSums
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test

set_option autoImplicit false

p2m_open "Ideal NumberField Filter Topology Asymptotics IsDedekindDomain Ideal.IsDedekindDomain"
open scoped ENNReal

namespace FrobeniusDensity
p2m_export "FrobeniusDensity" "normRpow idealSum idealCount zetaTerm"
p2m_open "FrobeniusDensity"

variable (K : Type*) [Field K] [NumberField K]

lemma zetaTerm_nonneg (s : ℝ) (n : ℕ) : 0 ≤ zetaTerm K s n := by
  unfold zetaTerm
  split
  · exact le_refl 0
  · exact mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

private lemma tendsto_sum_idealCount_div :
    Tendsto (fun n : ℕ => (∑ k ∈ Finset.Icc 1 n, (idealCount K k : ℝ)) / n) atTop
      (𝓝 (dedekindZeta_residue K)) := by
  simp only [idealCount]
  refine ((Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr fun n ↦ ?_
  simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
  congr
  rw [← add_left_inj 1, ← card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
    show 1 = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} by
      simp [Ideal.absNorm_eq_zero_iff],
    Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
    ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ ↦ Ideal.finite_setOf_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

private lemma isBigO_sum_of_tendsto_div :
    (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, (idealCount K k : ℝ))
      =O[atTop] (fun n => (n : ℝ) ^ (1:ℝ)) := by
  simp only [Real.rpow_one]
  rw [isBigO_iff]

  have hbdd : BddAbove (Set.range (fun n : ℕ =>
      (∑ k ∈ Finset.Icc 1 n, (idealCount K k : ℝ)) / n)) :=
    (tendsto_sum_idealCount_div K).bddAbove_range
  obtain ⟨C, hC⟩ := hbdd
  refine ⟨max C 0, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  rw [Real.norm_of_nonneg hn'.le,
    Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)]
  calc ∑ k ∈ Finset.Icc 1 n, (idealCount K k : ℝ)
      = ((∑ k ∈ Finset.Icc 1 n, (idealCount K k : ℝ)) / n) * n := by field_simp
    _ ≤ C * n := mul_le_mul_of_nonneg_right (hC ⟨n, rfl⟩) hn'.le
    _ ≤ max C 0 * n := mul_le_mul_of_nonneg_right (le_max_left _ _) hn'.le

private lemma LSeriesSummable_idealCount {s : ℝ} (hs : 1 < s) :
    LSeriesSummable (fun n => (idealCount K n : ℂ)) s := by
  refine LSeriesSummable_of_sum_norm_bigO_and_nonneg (f := fun n => (idealCount K n : ℝ))
    ?_ (fun n => Nat.cast_nonneg _) zero_le_one (by simpa using hs)
  exact isBigO_sum_of_tendsto_div K

private lemma term_eq_ofReal_zetaTerm (s : ℝ) (n : ℕ) :
    LSeries.term (fun n => (idealCount K n : ℂ)) s n = (zetaTerm K s n : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [zetaTerm, LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero hn, zetaTerm, if_neg hn]
    have hpos : (0:ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_cpow hpos.le,
      Complex.ofReal_neg, Complex.ofReal_natCast, Complex.cpow_neg, div_eq_mul_inv]

private lemma summable_zetaTerm {s : ℝ} (hs : 1 < s) : Summable (zetaTerm K s) := by
  have h : Summable fun n => ((zetaTerm K s n : ℝ) : ℂ) := by
    refine (LSeriesSummable_idealCount K hs).congr fun n => ?_
    exact term_eq_ofReal_zetaTerm K s n
  exact Complex.summable_ofReal.mp h

private def NormFiber (n : ℕ) : Type _ :=
  {I : {I : Ideal (𝓞 K) // I ≠ ⊥} // Ideal.absNorm I.1 = n}

private noncomputable def normFiberEquiv :
    (Σ n : ℕ, NormFiber K n) ≃ {I : Ideal (𝓞 K) // I ≠ ⊥} where
  toFun p := p.2.1
  invFun I := ⟨Ideal.absNorm I.1, I, rfl⟩
  left_inv p := by rcases p with ⟨n, I, rfl⟩; rfl
  right_inv I := rfl

private lemma tsum_normFiber (s : ℝ) (n : ℕ) :
    ∑' I : NormFiber K n, normRpow K s I.1.1 = ENNReal.ofReal (zetaTerm K s n) := by
  have hconst : ∀ I : NormFiber K n, normRpow K s I.1.1 = (n : ℝ≥0∞) ^ (-s) := fun I => by
    rw [normRpow, I.2]
  rw [tsum_congr hconst, ENNReal.tsum_const]
  rcases eq_or_ne n 0 with rfl | hn
  · have : IsEmpty (NormFiber K 0) := ⟨fun I => I.1.2 (Ideal.absNorm_eq_zero_iff.mp I.2)⟩
    simp [zetaTerm, ENat.card_eq_coe_natCard]
  · have hpos : (0:ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hequiv : NormFiber K n ≃ {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
      { toFun := fun I => ⟨I.1.1, I.2⟩
        invFun := fun I => ⟨⟨I.1, fun h => hn (by rw [← I.2, h, Ideal.absNorm_bot])⟩, I.2⟩
        left_inv := fun I => rfl
        right_inv := fun I => rfl }
    have hfin : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
      (Ideal.finite_setOf_absNorm_eq n).to_subtype
    have hfin' : Finite (NormFiber K n) := Finite.of_equiv _ hequiv.symm
    rw [zetaTerm, if_neg hn, ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_rpow_of_pos hpos, ENat.card_eq_coe_natCard, Nat.card_congr hequiv]
    simp only [ENNReal.ofReal_natCast, idealCount]
    norm_cast

private lemma tsum_equiv' {α β : Type*} (e : α ≃ β) (f : β → ℝ≥0∞) :
    ∑' a, f (e a) = ∑' b, f b := by
  refine le_antisymm (ENNReal.tsum_comp_le_tsum_of_injective e.injective f) ?_
  simpa using ENNReal.tsum_comp_le_tsum_of_injective e.symm.injective fun a => f (e a)

private lemma idealSum_eq_tsum_zetaTerm (s : ℝ) :
    idealSum K s = ∑' n : ℕ, ENNReal.ofReal (zetaTerm K s n) := by
  rw [idealSum, ← tsum_equiv' (normFiberEquiv K) (fun I => normRpow K s I.1),
    ENNReal.tsum_sigma']
  exact tsum_congr fun n => tsum_normFiber K s n

private lemma dedekindZeta_eq_ofReal_tsum (s : ℝ) :
    dedekindZeta K s = ((∑' n, zetaTerm K s n : ℝ) : ℂ) := by
  rw [dedekindZeta, LSeries, Complex.ofReal_tsum]
  exact tsum_congr fun n => term_eq_ofReal_zetaTerm K s n

private lemma idealSum_toReal_eq {s : ℝ} (hs : 1 < s) :
    (idealSum K s).toReal = ∑' n, zetaTerm K s n := by
  rw [idealSum_eq_tsum_zetaTerm,
    ← ENNReal.ofReal_tsum_of_nonneg (zetaTerm_nonneg K s) (summable_zetaTerm K hs),
    ENNReal.toReal_ofReal]
  exact tsum_nonneg (zetaTerm_nonneg K s)

end FrobeniusDensity

p2m_open "FrobeniusDensity P2MW.S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test.FrobeniusDensity"

theorem solution (K : Type*) [Field K] [NumberField K] :
    Filter.Tendsto (fun s : ℝ => (s - 1) * (FrobeniusDensity.idealSum K s).toReal)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (dedekindZeta_residue K)) := by
  rw [← Filter.tendsto_ofReal_iff]
  refine (tendsto_sub_one_mul_dedekindZeta_nhdsGT K).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [Set.mem_Ioi] at hs
  rw [idealSum_toReal_eq K hs, dedekindZeta_eq_ofReal_tsum]
  push_cast
  ring

end S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test
end P2MW
export P2MW.S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test (solution)
