-- Prove2me | solution 1 for BalanceSpecification.finite_code_pressure_le_one_of_growth_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:36:22.017373+00:00
-- url     : https://prove2.me/submissions/52f07c44-da4b-47d9-a083-6e2bb5725677

module
public import Definitions.Def_BalanceSpecificaton_SGapRenewal
public import Definitions.Def_BalanceSpecificaton_GrowthUpperBounds
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SGapEntropy
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_renewalFinset
public import Theorems.Thm_BalanceSpecification_mem_renewalGaps
public import Theorems.Thm_BalanceSpecification_mem_shortWords
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_nil_mem_generatedWords
public import Theorems.Thm_BalanceSpecification_periodicConfiguration_shift
public import Theorems.Thm_BalanceSpecification_renewalCount_zero
public import Theorems.Thm_BalanceSpecification_sGapListConcat_cons
public import Theorems.Thm_BalanceSpecification_sGapListConcat_nil
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
attribute [local simp] BalanceSpecification.follower_card_reverseLanguage
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_forbiddenShift_iff
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_renewalFinset
attribute [local simp] BalanceSpecification.mem_renewalGaps
attribute [local simp] BalanceSpecification.mem_shortWords
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.nil_mem_generatedWords
attribute [local simp] BalanceSpecification.periodicConfiguration_shift
attribute [local simp] BalanceSpecification.renewalCount_zero
attribute [local simp] BalanceSpecification.sGapListConcat_cons
attribute [local simp] BalanceSpecification.sGapListConcat_nil
attribute [local simp] BalanceSpecification.wordCount_reverseLanguage



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open Filter Set
open scoped Topology
namespace BalanceSpecification
theorem _root_.solution
    {A I : Type*} [Fintype A] [Fintype I] [TopologicalSpace A]
    {X : ShiftSpace A} (c : I → Word A) {γ C : ℝ}
    (hγ : 0 < γ) (_hC : 0 < C)
    (hcounts : ∀ n : ℕ, (wordCount (language X) n : ℝ) ≤ C * γ ^ n)
    (hinj : ∀ r : ℕ, Function.Injective
      (fun f : Fin r → I => (List.ofFn (fun i => c (f i))).flatten))
    (hmem : ∀ (r : ℕ) (f : Fin r → I),
      (List.ofFn (fun i => c (f i))).flatten ∈ language X) :
    ∑ i, (γ⁻¹) ^ (c i).length ≤ 1 := by
  classical
  let P : ℝ := ∑ i, (γ⁻¹) ^ (c i).length
  let M : ℕ := Finset.univ.sup (fun i : I => (c i).length)
  have hpowers (r : ℕ) : P ^ r ≤ ((r * M + 1 : ℕ) : ℝ) * C := by
    let concat : (Fin r → I) → Word A := fun f => (List.ofFn (fun i => c (f i))).flatten
    let T : Finset (Word A) := Finset.univ.image concat
    have hlength (f : Fin r → I) : (concat f).length = ∑ i, (c (f i)).length := by
      simp only [concat, List.length_flatten, List.map_ofFn, List.sum_ofFn, Function.comp_def]
    have hTmem {w : Word A} (hw : w ∈ T) : w ∈ language X := by
      obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp hw
      exact hmem r f
    have hlen_maps (w : Word A) (hw : w ∈ T) : w.length ∈ Finset.range (r * M + 1) := by
      obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp hw
      apply Finset.mem_range.mpr
      rw [hlength]
      have hh : (∑ i : Fin r, (c (f i)).length) ≤ ∑ _ : Fin r, M :=
        Finset.sum_le_sum fun i _ => Finset.le_sup
          (f := fun i : I => (c i).length) (Finset.mem_univ (f i))
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id, Nat.succ_eq_add_one]
        using Nat.lt_succ_of_le hh
    have hfiber (n : ℕ) :
        (∑ w ∈ T.filter (fun w => w.length = n), (γ⁻¹) ^ w.length) ≤ C := by
      have hcard : (T.filter (fun w => w.length = n)).card ≤ wordCount (language X) n := by
        apply Finset.card_le_card
        intro w hw
        obtain ⟨hwT, hwlen⟩ := Finset.mem_filter.mp hw
        exact mem_wordFinset.mpr ⟨hTmem hwT, hwlen⟩
      calc
        _ = ((T.filter (fun w => w.length = n)).card : ℝ) * (γ⁻¹) ^ n := by
          rw [Finset.sum_congr rfl (fun w hw => by rw [(Finset.mem_filter.mp hw).2])]
          simp only [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (wordCount (language X) n : ℝ) * (γ⁻¹) ^ n :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (pow_nonneg (inv_nonneg.mpr hγ.le) _)
        _ ≤ (C * γ ^ n) * (γ⁻¹) ^ n :=
          mul_le_mul_of_nonneg_right (hcounts n) (pow_nonneg (inv_nonneg.mpr hγ.le) _)
        _ = C := by rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ hγ.ne', one_pow, mul_one]
    calc
      P ^ r = ∑ f : Fin r → I, ∏ i : Fin r, (γ⁻¹) ^ (c (f i)).length :=
        Fintype.sum_pow (f := fun i : I => (γ⁻¹) ^ (c i).length) r
      _ = ∑ f : Fin r → I, (γ⁻¹) ^ (concat f).length := by
        apply Finset.sum_congr rfl
        intro f hf
        rw [hlength]
        exact Finset.prod_pow_eq_pow_sum _ _ _
      _ = ∑ w ∈ T, (γ⁻¹) ^ w.length :=
        (Finset.sum_image (f := fun w : Word A => (γ⁻¹) ^ w.length)
          (fun f hf g hg heq => hinj r heq)).symm
      _ = ∑ n ∈ Finset.range (r * M + 1),
          ∑ w ∈ T.filter (fun w => w.length = n), (γ⁻¹) ^ w.length :=
        (Finset.sum_fiberwise_of_maps_to hlen_maps _).symm
      _ ≤ ∑ _ ∈ Finset.range (r * M + 1), C :=
        Finset.sum_le_sum (fun n _ => hfiber n)
      _ = ((r * M + 1 : ℕ) : ℝ) * C := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  by_contra hP
  have hP1 : 1 < P := lt_of_not_ge hP
  have hPpos : 0 < P := zero_lt_one.trans hP1
  have hq : |P⁻¹| < 1 := by
    rw [abs_of_pos (inv_pos.mpr hPpos)]
    exact inv_lt_one_of_one_lt₀ hP1
  have ht1 := (tendsto_self_mul_const_pow_of_abs_lt_one hq).const_mul (M : ℝ)
  have ht0 := tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr hPpos.le)
    (inv_lt_one_of_one_lt₀ hP1)
  have ht : Tendsto (fun r : ℕ => (((r * M + 1 : ℕ) : ℝ) * C) / P ^ r)
      atTop (𝓝 0) := by
    have hh := (ht1.add ht0).mul_const C
    convert hh using 1
    · funext r
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, div_eq_mul_inv, inv_pow]
      ring
    · norm_num
  obtain ⟨r, hr⟩ := (ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))).exists
  have hge : 1 ≤ (((r * M + 1 : ℕ) : ℝ) * C) / P ^ r := by
    apply (le_div_iff₀ (pow_pos hPpos r)).mpr
    simpa only [one_mul] using hpowers r
  exact (not_lt_of_ge hge) hr
end BalanceSpecification
