-- Prove2me | solution 1 for BilateralProfit.lemma_4_5
-- status  : ACCEPTED   (prove)
-- author  : @sim2000dg
-- created : 2026-11-13T14:50:20.092812+00:00
-- url     : https://prove2.me/submissions/4876edbf-2fe4-46df-845f-9a0cc92f57d6

import Mathlib
import Definitions.Def_BilateralProfit_SellerTree
import Definitions.Def_BilateralProfit_QueryRoutine
import Theorems.Thm_SinkhornHall_lemma_1_1
import Theorems.Thm_BilateralProfit_lemma_4_8


namespace BilateralProfit.LibraryDetection45TradeFacts

open MeasureTheory

variable {K : ℕ}

theorem coord_mem (hK : 0 < K) (i : Fin (K + 1)) :
    (i : ℝ) / K ∈ Set.Icc (0 : ℝ) 1 := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hi : (i : ℕ) ≤ K := by omega
  constructor
  · positivity
  · apply (div_le_one hKr).mpr
    exact_mod_cast hi

theorem pt_mem (hK : 0 < K) (x : Grid K) :
    pt K x ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 :=
  ⟨coord_mem hK x.1, coord_mem hK x.2⟩

theorem spread_mem (hK : 0 < K) (a : Act K) :
    (pt K a.1).2 - (pt K a.1).1 ∈ Set.Icc (0 : ℝ) 1 := by
  have hleft := coord_mem hK a.1.1
  have hright := coord_mem hK a.1.2
  have horder : ((a.1.1 : ℕ) : ℝ) ≤ ((a.1.2 : ℕ) : ℝ) := by exact_mod_cast a.2
  have hdiv := div_le_div_of_nonneg_right horder (by positivity : (0 : ℝ) ≤ K)
  change ((a.1.2 : ℕ) : ℝ) / K - ((a.1.1 : ℕ) : ℝ) / K ∈ Set.Icc 0 1
  exact ⟨sub_nonneg.mpr hdiv, by linarith [hleft.1, hright.2]⟩

theorem tradeBit_nonneg (v a : ℝ × ℝ) : 0 ≤ tradeBit v a := by
  unfold tradeBit
  split_ifs <;> norm_num

theorem tradeBit_le_one (v a : ℝ × ℝ) : tradeBit v a ≤ 1 := by
  unfold tradeBit
  split_ifs <;> norm_num

theorem measurableSet_trades (a : ℝ × ℝ) : MeasurableSet {v | Trades v a} := by
  change MeasurableSet (Set.Iic a.1 ×ˢ Set.Ici a.2)
  exact measurableSet_Iic.prod measurableSet_Ici

theorem Ptrade_nonneg (μ : Measure (ℝ × ℝ)) (a : ℝ × ℝ) : 0 ≤ Ptrade μ a :=
  ENNReal.toReal_nonneg

theorem Ptrade_le_one (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ] (a : ℝ × ℝ) :
    Ptrade μ a ≤ 1 := by
  change μ.real {v | Trades v a} ≤ 1
  exact measureReal_le_one

theorem P0_nonneg (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) (a : ℝ × ℝ) :
    0 ≤ P0 ρ a := by
  exact Finset.sum_nonneg (fun x _ => mul_nonneg (hρ.1 x) (tradeBit_nonneg _ _))

theorem P0_le_one (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) (a : ℝ × ℝ) :
    P0 ρ a ≤ 1 := by
  calc
    P0 ρ a ≤ ∑ x, ρ x := Finset.sum_le_sum (fun x _ => by
      simpa using mul_le_mul_of_nonneg_left (tradeBit_le_one (pt K x.1) a) (hρ.1 x))
    _ = 1 := hρ.2

theorem valProfitPt_eq_spread_mul_P0 (ρ : Grid K × Act K → ℝ) (a : ℝ × ℝ) :
    valProfitPt ρ a = (a.2 - a.1) * P0 ρ a := by
  unfold valProfitPt profit P0
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem margLaw_apply (ρ : Grid K × Act K → ℝ) (s : Set (ℝ × ℝ)) :
    margLaw ρ s = ∑ x, ENNReal.ofReal (ρ x) * Measure.dirac (pt K x.1) s := by
  classical
  simp [margLaw, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]

theorem margLaw_univ (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) :
    margLaw ρ Set.univ = 1 := by
  rw [margLaw_apply]
  simp only [measure_univ, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => hρ.1 x), hρ.2]
  exact ENNReal.ofReal_one

theorem margLaw_isValLaw (hK : 0 < K) (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) :
    IsValLaw (margLaw ρ) := by
  refine ⟨⟨margLaw_univ ρ hρ⟩, ?_⟩
  rw [margLaw_apply]
  apply Finset.sum_eq_zero
  intro x _
  have hx : pt K x.1 ∉ (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)ᶜ :=
    fun h => h (pt_mem hK x.1)
  rw [Measure.dirac_apply, Set.indicator_of_notMem hx, mul_zero]

theorem Ptrade_margLaw_eq_P0 (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (a : ℝ × ℝ) : Ptrade (margLaw ρ) a = P0 ρ a := by
  classical
  unfold Ptrade
  rw [margLaw_apply, ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro x _
    by_cases h : Trades (pt K x.1) a
    · simp [tradeBit, h, ENNReal.toReal_ofReal (hρ.1 x)]
    · simp [tradeBit, h]
  · intro x _
    finiteness

theorem muP_margLaw_eq_valProfitPt (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (a : ℝ × ℝ) : muP (margLaw ρ) a = valProfitPt ρ a := by
  rw [muP, Ptrade_margLaw_eq_P0 ρ hρ, valProfitPt_eq_spread_mul_P0]

theorem valProfit_nonneg (hK : 0 < K) (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (a : Act K) : 0 ≤ valProfit ρ a := by
  rw [valProfit, valProfitPt_eq_spread_mul_P0]
  exact mul_nonneg (spread_mem hK a).1 (P0_nonneg ρ hρ _)

theorem valProfit_le_one (hK : 0 < K) (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (a : Act K) : valProfit ρ a ≤ 1 := by
  rw [valProfit, valProfitPt_eq_spread_mul_P0]
  have hs := spread_mem hK a
  have hp0 := P0_nonneg ρ hρ (pt K a.1)
  have hp1 := P0_le_one ρ hρ (pt K a.1)
  calc
    _ ≤ 1 * P0 ρ (pt K a.1) := mul_le_mul_of_nonneg_right hs.2 hp0
    _ ≤ 1 := by simpa using hp1

theorem valProfit_le_optVal (ρ : Grid K × Act K → ℝ) (a : Act K) :
    valProfit ρ a ≤ optVal ρ :=
  le_ciSup (Finite.bddAbove_range (valProfit ρ)) a

theorem optVal_nonneg (hK : 0 < K) (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) :
    0 ≤ optVal ρ :=
  (valProfit_nonneg hK ρ hρ default).trans (valProfit_le_optVal ρ default)

theorem optVal_le_one (hK : 0 < K) (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) :
    optVal ρ ≤ 1 :=
  ciSup_le (valProfit_le_one hK ρ hρ)

theorem gapStar_nonneg (ρ : Grid K × Act K → ℝ) (a : Act K) :
    0 ≤ gapStar ρ a :=
  sub_nonneg.mpr (valProfit_le_optVal ρ a)

theorem gapStar_le_one (hK : 0 < K) (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (a : Act K) : gapStar ρ a ≤ 1 := by
  change optVal ρ - valProfit ρ a ≤ 1
  linarith [optVal_le_one hK ρ hρ, valProfit_nonneg hK ρ hρ a]

end BilateralProfit.LibraryDetection45TradeFacts


namespace BilateralProfit.LibraryDetection45

open MeasureTheory
attribute [local instance] Classical.propDecidable

variable {Q Out : Type}

/-- The finite decision tree obtained by retaining the two biased-bit responses. -/
inductive BTree (Q Out : Type) : Type where
  | done : Out → BTree Q Out
  | node : Q → BTree Q Out → BTree Q Out → BTree Q Out

namespace BTree

@[reducible] def Leaves : BTree Q Out → Type
  | .done _ => Unit
  | .node _ l r => Leaves l ⊕ Leaves r

@[reducible] instance leavesFintype : (T : BTree Q Out) → Fintype T.Leaves
  | .done _ => inferInstanceAs (Fintype Unit)
  | .node _ l r => by
      letI := leavesFintype l
      letI := leavesFintype r
      exact inferInstanceAs (Fintype (l.Leaves ⊕ r.Leaves))

def output : (T : BTree Q Out) → T.Leaves → Out
  | .done o, _ => o
  | .node _ l _, .inl i => l.output i
  | .node _ _ r, .inr i => r.output i

noncomputable def mass (p : Q → ℝ) : (T : BTree Q Out) → T.Leaves → ℝ
  | .done _, _ => 1
  | .node q l _, .inl i => (1 - p q) * l.mass p i
  | .node q _ r, .inr i => p q * r.mass p i

noncomputable def eval (p : Q → ℝ) (E : Out → Prop) : BTree Q Out → ℝ
  | .done o => by classical exact if E o then 1 else 0
  | .node q l r => (1 - p q) * l.eval p E + p q * r.eval p E

lemma mass_sum (p : Q → ℝ) (T : BTree Q Out) : ∑ i, T.mass p i = 1 := by
  induction T with
  | done o => simp [mass, Leaves, leavesFintype]
  | node q l r ihl ihr =>
      change (∑ i : l.Leaves ⊕ r.Leaves, _) = 1
      simp only [Fintype.sum_sum_type, mass, ← Finset.mul_sum, ihl, ihr]
      ring

lemma mass_pos (p : Q → ℝ) (hp : ∀ q, 0 < p q ∧ p q < 1) (T : BTree Q Out)
    (i : T.Leaves) : 0 < T.mass p i := by
  induction T with
  | done o => exact zero_lt_one
  | node q l r ihl ihr =>
      cases i with
      | inl i => exact mul_pos (sub_pos.mpr (hp q).2) (ihl i)
      | inr i => exact mul_pos (hp q).1 (ihr i)

lemma eval_eq_sum (p : Q → ℝ) (E : Out → Prop) (T : BTree Q Out) :
    T.eval p E = ∑ i, T.mass p i * (if E (T.output i) then 1 else 0) := by
  classical
  induction T with
  | done o => simp [eval, Leaves, mass, output, leavesFintype]; rfl
  | node q l r ihl ihr =>
      change (1 - p q) * l.eval p E + p q * r.eval p E = ∑ i : l.Leaves ⊕ r.Leaves, _
      simp only [Leaves, leavesFintype, Fintype.sum_sum_type, mass, output, eval, ihl, ihr,
        mul_assoc, ← Finset.mul_sum]
      rfl

noncomputable def count [DecidableEq Q] (p : Q → ℝ) (a : Q) : BTree Q Out → ℝ
  | .done _ => 0
  | .node q l r => (if q = a then 1 else 0) + (1 - p q) * l.count p a + p q * r.count p a

lemma count_nonneg [DecidableEq Q] (p : Q → ℝ) (hp : ∀ q, 0 ≤ p q ∧ p q ≤ 1)
    (a : Q) (T : BTree Q Out) : 0 ≤ T.count p a := by
  induction T with
  | done o => exact le_rfl
  | node q l r ihl ihr =>
      dsimp [count]
      exact add_nonneg (add_nonneg (by split_ifs <;> norm_num)
        (mul_nonneg (sub_nonneg.mpr (hp q).2) ihl)) (mul_nonneg (hp q).1 ihr)

noncomputable def bernKL (u v : ℝ) : ℝ :=
  u * Real.log (u / v) + (1 - u) * Real.log ((1 - u) / (1 - v))

noncomputable def info (p s : Q → ℝ) : BTree Q Out → ℝ
  | .done _ => 0
  | .node q l r => bernKL (p q) (s q) + (1 - p q) * l.info p s + p q * r.info p s

lemma info_eq_sum_count [Fintype Q] [DecidableEq Q] (p s : Q → ℝ) (T : BTree Q Out) :
    T.info p s = ∑ a, T.count p a * bernKL (p a) (s a) := by
  induction T with
  | done o => simp [info, count]
  | node q l r ihl ihr =>
      simp only [count, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [← ihl, ← ihr]
      rfl

lemma info_eq_leafKL (p s : Q → ℝ)
    (hp : ∀ q, 0 < p q ∧ p q < 1) (hs : ∀ q, 0 < s q ∧ s q < 1)
    (T : BTree Q Out) :
    T.info p s = ∑ i, T.mass p i * Real.log (T.mass p i / T.mass s i) := by
  induction T with
  | done o => simp [Leaves, mass, info]
  | node q l r ihl ihr =>
      have hp0 := (hp q).1.ne'
      have hp1 := (sub_pos.mpr (hp q).2).ne'
      have hs0 := (hs q).1.ne'
      have hs1 := (sub_pos.mpr (hs q).2).ne'
      change _ = ∑ i : l.Leaves ⊕ r.Leaves, _
      simp only [Fintype.sum_sum_type, mass]
      have hl (i : l.Leaves) :
          Real.log ((1 - p q) * l.mass p i / ((1 - s q) * l.mass s i)) =
            Real.log ((1 - p q) / (1 - s q)) + Real.log (l.mass p i / l.mass s i) := by
        rw [mul_div_mul_comm, Real.log_mul (div_ne_zero hp1 hs1)
          (div_ne_zero (mass_pos p hp l i).ne' (mass_pos s hs l i).ne')]
      have hr (i : r.Leaves) :
          Real.log (p q * r.mass p i / (s q * r.mass s i)) =
            Real.log (p q / s q) + Real.log (r.mass p i / r.mass s i) := by
        rw [mul_div_mul_comm, Real.log_mul (div_ne_zero hp0 hs0)
          (div_ne_zero (mass_pos p hp r i).ne' (mass_pos s hs r i).ne')]
      simp_rw [hl, hr]
      have hsums (A c : ℝ) (U : BTree Q Out)
          (hU : U.info p s = ∑ i, U.mass p i * Real.log (U.mass p i / U.mass s i)) :
          (∑ i, A * U.mass p i * (c + Real.log (U.mass p i / U.mass s i))) =
            A * c + A * U.info p s := by
        calc
          _ = A * c * (∑ i, U.mass p i) +
              A * (∑ i, U.mass p i * Real.log (U.mass p i / U.mass s i)) := by
                simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
                apply Finset.sum_congr rfl
                intro i _
                ring
          _ = _ := by rw [mass_sum, ← hU]; ring
      rw [hsums _ _ l ihl, hsums _ _ r ihr]
      dsimp [info, bernKL]
      ring

end BTree

lemma bernKL_le_chiSquared {u v : ℝ} (hu : 0 < u) (hu1 : u < 1)
    (hv : 0 < v) (hv1 : v < 1) :
    BTree.bernKL u v ≤ (u - v) ^ 2 / (v * (1 - v)) := by
  have h1 := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hu hv)) hu.le
  have h2 := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos (sub_pos.mpr hu1) (sub_pos.mpr hv1)))
    (sub_nonneg.mpr hu1.le)
  calc
    _ ≤ u * (u / v - 1) + (1 - u) * ((1 - u) / (1 - v) - 1) := add_le_add h1 h2
    _ = _ := by field_simp [hv.ne', (sub_pos.mpr hv1).ne']; ring

lemma biased_bernKL_bound {u v : ℝ} (hu : 0 ≤ u ∧ u ≤ 1) (hv : 0 ≤ v ∧ v ≤ 1) :
    BTree.bernKL (1 / 4 + u / 2) (1 / 4 + v / 2) ≤ (4 / 3) * (u - v) ^ 2 := by
  have hv0 : 0 < (1 / 4 + v / 2) * (1 - (1 / 4 + v / 2)) := by
    apply mul_pos <;> linarith [hv.1, hv.2]
  have hden : (3 / 16 : ℝ) ≤ (1 / 4 + v / 2) * (1 - (1 / 4 + v / 2)) := by
    nlinarith [mul_nonneg hv.1 (sub_nonneg.mpr hv.2)]
  refine (bernKL_le_chiSquared (u := 1 / 4 + u / 2) (v := 1 / 4 + v / 2)
    (by linarith [hu.1]) (by linarith [hu.2])
    (by linarith [hv.1]) (by linarith [hv.2])).trans ?_
  apply (div_le_iff₀ hv0).mpr
  nlinarith [mul_nonneg (sq_nonneg (u - v)) (sub_nonneg.mpr hden)]

noncomputable def binaryLaw (p : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 - p) • Measure.dirac (-(1 / 2 : ℝ)) +
    ENNReal.ofReal p • Measure.dirac (3 / 2 : ℝ)

lemma binaryLaw_probability {p : ℝ} (hp : 0 ≤ p ∧ p ≤ 1) :
    IsProbabilityMeasure (binaryLaw p) := by
  constructor
  simp only [binaryLaw, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem,
    Set.mem_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr hp.2) hp.1]
  norm_num

lemma binaryLaw_supported (p : ℝ) :
    binaryLaw p (Set.Icc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 2))ᶜ = 0 := by
  have h0 : (-(1 / 2 : ℝ)) ∈ Set.Icc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 2) := by norm_num
  have h1 : (3 / 2 : ℝ) ∈ Set.Icc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 2) := by norm_num
  norm_num [binaryLaw, Measure.dirac_apply', measurableSet_Icc.compl]

lemma binaryLaw_mean {p : ℝ} (hp : 0 ≤ p ∧ p ≤ 1) :
    ∫ r, r ∂binaryLaw p = 2 * p - 1 / 2 := by
  rw [binaryLaw, integral_add_measure]
  · simp only [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal hp.1,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hp.2)]
    ring
  · exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  · exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

lemma lintegral_binaryLaw (p : ℝ) (f : ℝ → ENNReal) :
    (∫⁻ r, f r ∂binaryLaw p) =
      ENNReal.ofReal (1 - p) * f (-(1 / 2 : ℝ)) + ENNReal.ofReal p * f (3 / 2 : ℝ) := by
  simp only [binaryLaw, lintegral_add_measure, lintegral_smul_measure, lintegral_dirac, smul_eq_mul]

lemma BTree.eval_nonneg (p : Q → ℝ) (hp : ∀ q, 0 ≤ p q ∧ p q ≤ 1)
    (T : BTree Q Out) (E : Out → Prop) : 0 ≤ T.eval p E := by
  induction T with
  | done o => simp only [BTree.eval]; split_ifs <;> positivity
  | node q l r ihl ihr =>
      exact add_nonneg (mul_nonneg (sub_nonneg.mpr (hp q).2) ihl) (mul_nonneg (hp q).1 ihr)

namespace QTree

noncomputable def toBinary : BilateralProfit.QTree Q Out → BTree Q Out
  | .done o => .done o
  | .query q k => .node q (toBinary (k (-(1 / 2 : ℝ)))) (toBinary (k (3 / 2 : ℝ)))

lemma prob_binaryLaw [DecidableEq Q] (R : BilateralProfit.QTree Q Out)
    (p : Q → ℝ) (hp : ∀ q, 0 ≤ p q ∧ p q ≤ 1) (E : Out → Prop) (cnt : Q → ℕ) :
    R.prob (fun q _ => binaryLaw (p q)) E cnt = ENNReal.ofReal ((toBinary R).eval p E) := by
  induction R generalizing cnt with
  | done o =>
      simp only [BilateralProfit.QTree.prob, toBinary, BTree.eval]
      split_ifs <;> norm_num
  | query q k ih =>
      change (∫⁻ r, (k r).prob (fun q _ => binaryLaw (p q)) E
        (Function.update cnt q (cnt q + 1)) ∂binaryLaw (p q)) = _
      rw [lintegral_binaryLaw, ih, ih]
      change _ = ENNReal.ofReal ((1 - p q) * (toBinary (k (-(1 / 2 : ℝ)))).eval p E +
        p q * (toBinary (k (3 / 2 : ℝ))).eval p E)
      rw [← ENNReal.ofReal_mul (sub_nonneg.mpr (hp q).2),
        ← ENNReal.ofReal_mul (hp q).1, ← ENNReal.ofReal_add]
      · exact mul_nonneg (sub_nonneg.mpr (hp q).2) (BTree.eval_nonneg p hp _ E)
      · exact mul_nonneg (hp q).1 (BTree.eval_nonneg p hp _ E)

end QTree

namespace BTree

lemma eval_mono (p : Q → ℝ) (hp : ∀ q, 0 ≤ p q ∧ p q ≤ 1)
    (T : BTree Q Out) (E F : Out → Prop) (hEF : ∀ o, E o → F o) :
    T.eval p E ≤ T.eval p F := by
  induction T with
  | done o => simp only [eval]; split_ifs <;> simp_all
  | node q l r ihl ihr =>
      exact add_le_add (mul_le_mul_of_nonneg_left ihl (sub_nonneg.mpr (hp q).2))
        (mul_le_mul_of_nonneg_left ihr (hp q).1)

lemma eval_disjoint (p : Q → ℝ) (hp : ∀ q, 0 ≤ p q ∧ p q ≤ 1)
    (T : BTree Q Out) (E F : Out → Prop) (hEF : ∀ o, E o → ¬ F o) :
    T.eval p E + T.eval p F ≤ 1 := by
  induction T with
  | done o => simp only [eval]; split_ifs <;> simp_all
  | node q l r ihl ihr =>
      have hl := mul_le_mul_of_nonneg_left ihl (sub_nonneg.mpr (hp q).2)
      have hr := mul_le_mul_of_nonneg_left ihr (hp q).1
      dsimp [eval]
      linarith

lemma sum_count_node [Fintype Q] [DecidableEq Q] (p cost : Q → ℝ)
    (q : Q) (l r : BTree Q Out) :
    (∑ a, (BTree.node q l r).count p a * cost a) =
      cost q + (1 - p q) * (∑ a, l.count p a * cost a) +
        p q * (∑ a, r.count p a * cost a) := by
  simp only [count, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

end BTree

namespace QTree

lemma count_cost_le [Fintype Q] [DecidableEq Q] (R : BilateralProfit.QTree Q Out)
    (p : Q → ℝ) (hp : ∀ q, 0 ≤ p q ∧ p q ≤ 1)
    (cost : Q → ℝ) {c : ℝ} (hc : 0 ≤ c) {N : ℕ}
    (hN : R.QueriesAtMost N) (hcost : R.AllQueries (fun q => cost q ≤ c)) :
    (∑ a, (toBinary R).count p a * cost a) ≤ N * c := by
  induction R generalizing N with
  | done o => simp only [toBinary, BTree.count, zero_mul, Finset.sum_const_zero]; positivity
  | query q k ih =>
      cases N with
      | zero => exact False.elim hN
      | succ N =>
          rw [toBinary, BTree.sum_count_node]
          have hl := mul_le_mul_of_nonneg_left
            (ih (-(1 / 2 : ℝ)) (hN _) (hcost.2 _)) (sub_nonneg.mpr (hp q).2)
          have hr := mul_le_mul_of_nonneg_left
            (ih (3 / 2 : ℝ) (hN _) (hcost.2 _)) (hp q).1
          simp only [Nat.cast_add, Nat.cast_one]
          nlinarith [hcost.1]

end QTree

end BilateralProfit.LibraryDetection45


namespace BilateralProfit.LibraryDetection45

attribute [local instance] Classical.propDecidable

lemma finite_event_l1 {ι : Type} [Fintype ι] (p s : ι → ℝ)
    (hpsum : ∑ i, p i = 1) (hssum : ∑ i, s i = 1) (E : ι → Prop) :
    2 * ((∑ i, p i * (if E i then 1 else 0)) - (∑ i, s i * (if E i then 1 else 0))) ≤
      ∑ i, |p i - s i| := by
  classical
  have hpoint (i : ι) :
      2 * (p i * (if E i then 1 else 0) - s i * (if E i then 1 else 0)) -
        (p i - s i) ≤ |p i - s i| := by
    by_cases hi : E i
    · simp only [if_pos hi, mul_one]
      nlinarith [le_abs_self (p i - s i)]
    · simp only [if_neg hi, mul_zero, sub_self, mul_zero, zero_sub]
      exact neg_le_abs (p i - s i)
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
  simpa only [Finset.sum_sub_distrib, ← Finset.mul_sum, hpsum, hssum, sub_self, sub_zero] using hsum

namespace BTree

variable {Q Out : Type}

instance leavesNonempty (T : BTree Q Out) : Nonempty T.Leaves := by
  induction T with
  | done o => exact ⟨()⟩
  | node q l r ihl ihr => obtain ⟨x⟩ := ihl; exact ⟨Sum.inl x⟩

/-- Pinsker's inequality imported from the proved finite-vector library theorem. -/
lemma library_testing_bound (p s : Q → ℝ)
    (hp : ∀ q, 0 < p q ∧ p q < 1) (hs : ∀ q, 0 < s q ∧ s q < 1)
    (T : BTree Q Out) (E : Out → Prop)
    (hE : 0 ≤ T.eval p E - T.eval s E) :
    2 * (T.eval p E - T.eval s E) ^ 2 ≤ T.info p s := by
  classical
  have hpin := SinkhornHall.lemma_1_1 (T.mass p) (T.mass s)
    (fun i => (T.mass_pos p hp i).le) (fun i => (T.mass_pos s hs i).le)
    ((T.mass_sum p).trans (T.mass_sum s).symm)
  have hnot : ¬ ∃ i, T.mass s i = 0 ∧ 0 < T.mass p i := by
    rintro ⟨i, hi, _⟩
    exact (T.mass_pos s hs i).ne' hi
  rw [SinkhornHall.klDiv, if_neg hnot, EReal.coe_le_coe_iff, T.mass_sum p,
    mul_one, ← T.info_eq_leafKL p s hp hs] at hpin
  have hl1 := finite_event_l1 (T.mass p) (T.mass s) (T.mass_sum p) (T.mass_sum s)
    (fun i => E (T.output i))
  rw [← T.eval_eq_sum p E, ← T.eval_eq_sum s E] at hl1
  have hl1nonneg : 0 ≤ ∑ i, |T.mass p i - T.mass s i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hsq := mul_self_le_mul_self (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hE) hl1
  nlinarith

lemma detection_separation_library [Fintype Q] [DecidableEq Q]
    (u v : Q → ℝ) (hu : ∀ q, 0 ≤ u q ∧ u q ≤ 1) (hv : ∀ q, 0 ≤ v q ∧ v q ≤ 1)
    (T : BTree Q Out) (E : Out → Prop)
    (hE0 : (9 / 10 : ℝ) ≤ T.eval (fun q => 1 / 4 + u q / 2) E)
    (hE1 : T.eval (fun q => 1 / 4 + v q / 2) E ≤ 1 / 10) :
    1 ≤ ∑ a, (4 * T.count (fun q => 1 / 4 + u q / 2) a) * (v a - u a) ^ 2 := by
  let p := fun q => (1 / 4 : ℝ) + u q / 2
  let s := fun q => (1 / 4 : ℝ) + v q / 2
  have hp (q : Q) : 0 < p q ∧ p q < 1 := by dsimp [p]; constructor <;> linarith [(hu q).1, (hu q).2]
  have hs (q : Q) : 0 < s q ∧ s q < 1 := by dsimp [s]; constructor <;> linarith [(hv q).1, (hv q).2]
  have hdiff : (4 / 5 : ℝ) ≤ T.eval p E - T.eval s E := by
    change (9 / 10 : ℝ) ≤ T.eval p E at hE0
    change T.eval s E ≤ 1 / 10 at hE1
    linarith
  have htest := T.library_testing_bound p s hp hs E (by linarith)
  have hinfo : (32 / 25 : ℝ) ≤ T.info p s := by nlinarith
  have hupper : T.info p s ≤ (4 / 3) * ∑ a, T.count p a * (v a - u a) ^ 2 := by
    rw [info_eq_sum_count, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a _
    have hc := count_nonneg p (fun q => ⟨(hp q).1.le, (hp q).2.le⟩) a T
    have hb := mul_le_mul_of_nonneg_left (biased_bernKL_bound (hu a) (hv a)) hc
    convert hb using 1 <;> dsimp [p, s] <;> ring
  have heq : (∑ a, (4 * T.count p a) * (v a - u a) ^ 2) =
      4 * ∑ a, T.count p a * (v a - u a) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  change 1 ≤ ∑ a, (4 * T.count p a) * (v a - u a) ^ 2
  rw [heq]
  linarith

end BTree

end BilateralProfit.LibraryDetection45


namespace BilateralProfit.LibraryDetection45Scales

open Finset

/-- The dyadic precisions in the proof of inexpensive detection, stopped at the
first precision reaching one. -/
theorem scales (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    ∃ J : ℕ, ∃ ε : Fin (J + 1) → ℝ,
      (∀ j, x ≤ ε j ∧ ε j ≤ 1) ∧
      (∀ d : ℝ, 0 ≤ d → d ≤ 1 → ∃ j, d ≤ ε j ∧ ε j < 2 * (x + d)) ∧
      (∑ j, 1 / ε j ≤ 4 / x) ∧
      (∑ j, 1 / (ε j) ^ 2 ≤ 4 / x ^ 2) := by
  classical
  have hex : ∃ n : ℕ, 1 ≤ (2 : ℝ) ^ n * x := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / x) (by norm_num : (1 : ℝ) < 2)
    exact ⟨n, ((div_lt_iff₀ hx).mp hn).le⟩
  let J := Nat.find hex
  let ε : Fin (J + 1) → ℝ := fun j => min ((2 : ℝ) ^ (j : ℕ) * x) 1
  have htop : 1 ≤ (2 : ℝ) ^ J * x := Nat.find_spec hex
  have hbelow : ∀ n < J, (2 : ℝ) ^ n * x < 1 := by
    intro n hn
    exact lt_of_not_ge (Nat.find_min hex hn)
  have hrange : ∀ j, x ≤ ε j ∧ ε j ≤ 1 := by
    intro j
    refine ⟨le_min ?_ hx1, min_le_right _ _⟩
    have hpow : (1 : ℝ) ≤ 2 ^ (j : ℕ) := one_le_pow₀ (by norm_num)
    nlinarith
  have hpos : ∀ j, 0 < ε j := fun j => hx.trans_le (hrange j).1
  have hlast : ε (Fin.last J) = 1 := min_eq_right htop
  have hgeo : (∑ j : Fin J, (1 / (2 : ℝ)) ^ (j : ℕ)) ≤ 2 := by
    simpa only [Fin.sum_univ_eq_sum_range] using sum_geometric_two_le J
  have hfirst : ∀ j : Fin J, 1 / ε j.castSucc = (1 / x) * (1 / (2 : ℝ)) ^ (j : ℕ) := by
    intro j
    change 1 / min ((2 : ℝ) ^ (j : ℕ) * x) 1 = _
    rw [min_eq_left (hbelow j j.isLt).le]
    simp [div_eq_mul_inv, mul_inv_rev, inv_pow, mul_comm]
  have hsum : ∑ j, 1 / ε j ≤ 4 / x := by
    rw [Fin.sum_univ_castSucc, hlast]
    simp only [div_one]
    calc
      (∑ j : Fin J, 1 / ε j.castSucc) + 1 =
          (1 / x) * (∑ j : Fin J, (1 / (2 : ℝ)) ^ (j : ℕ)) + 1 := by
        simp_rw [hfirst]
        rw [mul_sum]
      _ ≤ (1 / x) * 2 + 1 := by
        have hmul := mul_le_mul_of_nonneg_left hgeo (show 0 ≤ 1 / x by positivity)
        linarith
      _ ≤ 4 / x := by
        have hxinv : 1 ≤ 1 / x := (one_le_div hx).mpr hx1
        simp only [div_eq_mul_inv] at hxinv ⊢
        linarith
  refine ⟨J, ε, hrange, ?_, hsum, ?_⟩
  · intro d hd hd1
    have hexd : ∃ n : ℕ, d ≤ (2 : ℝ) ^ n * x := ⟨J, hd1.trans htop⟩
    let k := Nat.find hexd
    have hk : k ≤ J := Nat.find_min' hexd (hd1.trans htop)
    have hkd : d ≤ (2 : ℝ) ^ k * x := Nat.find_spec hexd
    have hkmin : ∀ n < k, (2 : ℝ) ^ n * x < d := by
      intro n hn
      exact lt_of_not_ge (Nat.find_min hexd hn)
    refine ⟨⟨k, by omega⟩, le_min hkd hd1, ?_⟩
    by_cases hk0 : k = 0
    · have hle : min ((2 : ℝ) ^ k * x) 1 ≤ x := by simp [hk0, min_eq_left hx1]
      exact hle.trans_lt (by linarith)
    · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hk0
      have hprev := hkmin n (by omega)
      have hpow : (2 : ℝ) ^ k * x < 2 * d := by
        rw [hn, pow_succ]
        nlinarith
      exact (min_le_left _ _).trans_lt (hpow.trans (by linarith))
  · calc
      ∑ j, 1 / ε j ^ 2 ≤ ∑ j, (1 / x) * (1 / ε j) := by
        apply sum_le_sum
        intro j _
        have hinv : 1 / ε j ≤ 1 / x := one_div_le_one_div_of_le hx (hrange j).1
        have hmul := mul_le_mul_of_nonneg_right hinv (by positivity : 0 ≤ 1 / ε j)
        simpa [pow_two, div_eq_mul_inv, mul_inv_rev, mul_comm] using hmul
      _ = (1 / x) * ∑ j, 1 / ε j := (mul_sum _ _ _).symm
      _ ≤ (1 / x) * (4 / x) := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 4 / x ^ 2 := by ring

end BilateralProfit.LibraryDetection45Scales


namespace BilateralProfit.LibraryDetection45

open MeasureTheory

variable {K : ℕ}

/-- The success property furnished by the localized estimation lemma. -/
def EstimationGuarantee (ρ : Grid K × Act K → ℝ) (ε : ℝ)
    (R : BilateralProfit.QTree (Act K) (Act K → ℝ)) : Prop :=
  ∀ μ : Measure (ℝ × ℝ), IsValLaw μ →
    ∀ (c : ℝ) (obs : Act K → Measure ℝ), (∀ a, IsProbabilityMeasure (obs a)) →
      (∀ a, obs a (Set.Icc c (c + 2))ᶜ = 0) →
      (∀ a, ∫ r, r ∂(obs a) = Ptrade μ (pt K a.1)) →
      ENNReal.ofReal (9 / 10) ≤
        R.prob (fun a _ => obs a)
          (fun est => ∀ a, gapStar ρ a ≤ ε → |est a - muP μ (pt K a.1)| ≤ ε / 4)
          (fun _ => 0)

lemma biased_parameters {u : ℝ} (hu : 0 ≤ u ∧ u ≤ 1) :
    0 ≤ 1 / 4 + u / 2 ∧ 1 / 4 + u / 2 ≤ 1 := by
  constructor <;> linarith [hu.1, hu.2]

/-- A single appropriate scale forces a constant weighted squared discrepancy. -/
theorem detection_at_scale (hK : 0 < K) (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (ε x : ℝ) (R : BilateralProfit.QTree (Act K) (Act K → ℝ))
    (hR : EstimationGuarantee ρ ε R)
    (μ : Measure (ℝ × ℝ)) (hμ : IsValLaw μ) (a : Act K)
    (hgap : gapStar ρ a ≤ ε) (himprove : optVal ρ + x ≤ muP μ (pt K a.1))
    (hscale : ε < 2 * (x + gapStar ρ a)) :
    1 ≤ ∑ b, (4 * (QTree.toBinary R).count
      (fun q => 1 / 4 + P0 ρ (pt K q.1) / 2) b) *
      (Ptrade μ (pt K b.1) - P0 ρ (pt K b.1)) ^ 2 := by
  classical
  letI : IsProbabilityMeasure μ := hμ.1
  let u := fun b : Act K => P0 ρ (pt K b.1)
  let v := fun b : Act K => Ptrade μ (pt K b.1)
  have hu (b : Act K) : 0 ≤ u b ∧ u b ≤ 1 :=
    ⟨LibraryDetection45TradeFacts.P0_nonneg ρ hρ _, LibraryDetection45TradeFacts.P0_le_one ρ hρ _⟩
  have hv (b : Act K) : 0 ≤ v b ∧ v b ≤ 1 :=
    ⟨LibraryDetection45TradeFacts.Ptrade_nonneg μ _, LibraryDetection45TradeFacts.Ptrade_le_one μ _⟩
  let p := fun b : Act K => (1 / 4 : ℝ) + u b / 2
  let s := fun b : Act K => (1 / 4 : ℝ) + v b / 2
  have hp (b : Act K) : 0 ≤ p b ∧ p b ≤ 1 := biased_parameters (hu b)
  have hs (b : Act K) : 0 ≤ s b ∧ s b ≤ 1 := biased_parameters (hv b)
  let E0 := fun est : Act K → ℝ => |est a - valProfit ρ a| ≤ ε / 4
  let EP := fun est : Act K → ℝ =>
    ∀ b, gapStar ρ b ≤ ε → |est b - muP μ (pt K b.1)| ≤ ε / 4
  let Eref := fun est : Act K → ℝ =>
    ∀ b, gapStar ρ b ≤ ε → |est b - muP (margLaw ρ) (pt K b.1)| ≤ ε / 4
  have href := hR (margLaw ρ) (LibraryDetection45TradeFacts.margLaw_isValLaw hK ρ hρ)
    (-(1 / 2)) (fun b => binaryLaw (p b))
    (fun b => binaryLaw_probability (hp b))
    (fun b => binaryLaw_supported (p b)) (fun b => by
      rw [binaryLaw_mean (hp b), LibraryDetection45TradeFacts.Ptrade_margLaw_eq_P0 ρ hρ]
      dsimp [p, u]
      ring)
  have htrue := hR μ hμ (-(1 / 2)) (fun b => binaryLaw (s b))
    (fun b => binaryLaw_probability (hs b))
    (fun b => binaryLaw_supported (s b)) (fun b => by
      rw [binaryLaw_mean (hs b)]
      dsimp [s, v]
      ring)
  rw [QTree.prob_binaryLaw R p hp] at href
  rw [QTree.prob_binaryLaw R s hs] at htrue
  have hrefReal : (9 / 10 : ℝ) ≤ (QTree.toBinary R).eval p Eref :=
    (ENNReal.ofReal_le_ofReal_iff (BTree.eval_nonneg p hp _ Eref)).mp href
  have htrueReal : (9 / 10 : ℝ) ≤ (QTree.toBinary R).eval s EP :=
    (ENNReal.ofReal_le_ofReal_iff (BTree.eval_nonneg s hs _ EP)).mp htrue
  have hE0 : (9 / 10 : ℝ) ≤ (QTree.toBinary R).eval p E0 := by
    apply hrefReal.trans
    apply BTree.eval_mono p hp _ Eref E0
    intro est hest
    have hh := hest a hgap
    simpa only [E0, valProfit, LibraryDetection45TradeFacts.muP_margLaw_eq_valProfitPt ρ hρ] using hh
  have hdis : ∀ est, E0 est → ¬ EP est := by
    intro est he0 hep
    have hh := hep a hgap
    have hb := (abs_le.mp he0).2
    have hc := (abs_le.mp hh).1
    change ε < 2 * (x + (optVal ρ - valProfit ρ a)) at hscale
    linarith
  have hdisprob := BTree.eval_disjoint s hs (QTree.toBinary R) E0 EP hdis
  have hE1 : (QTree.toBinary R).eval s E0 ≤ 1 / 10 := by linarith
  exact BTree.detection_separation_library u v hu hv (QTree.toBinary R) E0 hE0 hE1

/-- Assemble the experiments at a finite geometric family of precisions. -/
theorem detection_from_scales {J : ℕ} (hK : 0 < K)
    (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) (x C : ℝ) (hx : 0 < x) (hC : 0 ≤ C)
    (ε : Fin (J + 1) → ℝ) (hε : ∀ j, x ≤ ε j ∧ ε j ≤ 1)
    (hcover : ∀ d : ℝ, 0 ≤ d → d ≤ 1 → ∃ j, d ≤ ε j ∧ ε j < 2 * (x + d))
    (hsum1 : ∑ j, 1 / ε j ≤ 4 / x) (hsum2 : ∑ j, 1 / (ε j) ^ 2 ≤ 4 / x ^ 2)
    (R : Fin (J + 1) → BilateralProfit.QTree (Act K) (Act K → ℝ))
    (N : Fin (J + 1) → ℕ)
    (hbound : ∀ j, (N j : ℝ) ≤ C * Real.log K ^ 3 *
      ((K : ℝ) / (ε j) ^ 2 + Real.log K ^ 3 / (ε j) ^ 3))
    (hcap : ∀ j, (R j).QueriesAtMost (N j))
    (hquery : ∀ j, (R j).AllQueries (fun a => gapStar ρ a ≤ 2 * ε j))
    (hest : ∀ j, EstimationGuarantee ρ (ε j) (R j)) :
    ∃ n : Act K → ℝ, (∀ a, 0 ≤ n a) ∧
      ∑ a, n a * (gapStar ρ a + x) ≤
        (48 * C) * Real.log K ^ 3 * ((K : ℝ) / x + Real.log K ^ 3 / x ^ 2) ∧
      ∀ μ : Measure (ℝ × ℝ), IsValLaw μ →
        (∃ a : Act K, optVal ρ + x ≤ muP μ (pt K a.1)) →
          1 ≤ ∑ a, n a * (Ptrade μ (pt K a.1) - P0 ρ (pt K a.1)) ^ 2 := by
  classical
  let p := fun a : Act K => (1 / 4 : ℝ) + P0 ρ (pt K a.1) / 2
  have hp (a : Act K) : 0 ≤ p a ∧ p a ≤ 1 :=
    biased_parameters ⟨LibraryDetection45TradeFacts.P0_nonneg ρ hρ _, LibraryDetection45TradeFacts.P0_le_one ρ hρ _⟩
  let nj := fun (j : Fin (J + 1)) (a : Act K) => (QTree.toBinary (R j)).count p a
  let n := fun a => 4 * ∑ j, nj j a
  have hnj (j : Fin (J + 1)) (a : Act K) : 0 ≤ nj j a :=
    BTree.count_nonneg p hp a _
  have hεpos (j : Fin (J + 1)) : 0 < ε j := hx.trans_le (hε j).1
  have hlog : 0 ≤ Real.log K := Real.log_nonneg (by exact_mod_cast (show 1 ≤ K by omega))
  refine ⟨n, fun a => mul_nonneg (by norm_num) (Finset.sum_nonneg (fun j _ => hnj j a)), ?_, ?_⟩
  · have hlocal (j : Fin (J + 1)) :
        (∑ a, nj j a * (gapStar ρ a + x)) ≤
          3 * C * Real.log K ^ 3 * ((K : ℝ) / ε j + Real.log K ^ 3 / (ε j) ^ 2) := by
      have hjpos := hεpos j
      have hmono : ∀ T : BilateralProfit.QTree (Act K) (Act K → ℝ),
          T.AllQueries (fun a => gapStar ρ a ≤ 2 * ε j) →
          T.AllQueries (fun a => gapStar ρ a + x ≤ 3 * ε j) := by
        intro T hT
        induction T with
        | done o => trivial
        | query b f ih => exact ⟨by linarith [hT.1, (hε j).1], fun z => ih z (hT.2 z)⟩
      have hcost := QTree.count_cost_le (R j) p hp (fun a => gapStar ρ a + x)
        (c := 3 * ε j) (by positivity) (hcap j) (hmono _ (hquery j))
      calc
        _ ≤ (N j : ℝ) * (3 * ε j) := hcost
        _ ≤ (C * Real.log K ^ 3 * ((K : ℝ) / (ε j) ^ 2 + Real.log K ^ 3 / (ε j) ^ 3)) *
            (3 * ε j) := mul_le_mul_of_nonneg_right (hbound j) (by positivity)
        _ = _ := by field_simp [(hεpos j).ne'] <;> ring
    have hs : (∑ j, ((K : ℝ) / ε j + Real.log K ^ 3 / (ε j) ^ 2)) ≤
        4 * ((K : ℝ) / x + Real.log K ^ 3 / x ^ 2) := by
      calc
        _ = (K : ℝ) * (∑ j, 1 / ε j) + Real.log K ^ 3 * (∑ j, 1 / (ε j) ^ 2) := by
          simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ ≤ (K : ℝ) * (4 / x) + Real.log K ^ 3 * (4 / x ^ 2) :=
          add_le_add (mul_le_mul_of_nonneg_left hsum1 (by positivity))
            (mul_le_mul_of_nonneg_left hsum2 (by positivity))
        _ = _ := by ring
    calc
      _ = 4 * ∑ j, ∑ a, nj j a * (gapStar ρ a + x) := by
        dsimp [n]
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro a _
        ring
      _ ≤ 4 * ∑ j, 3 * C * Real.log K ^ 3 *
          ((K : ℝ) / ε j + Real.log K ^ 3 / (ε j) ^ 2) := by
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => hlocal j)) (by norm_num)
      _ = (12 * C * Real.log K ^ 3) *
          ∑ j, ((K : ℝ) / ε j + Real.log K ^ 3 / (ε j) ^ 2) := by
        rw [← Finset.mul_sum]
        ring
      _ ≤ (12 * C * Real.log K ^ 3) *
          (4 * ((K : ℝ) / x + Real.log K ^ 3 / x ^ 2)) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by ring
  · intro μ hμ himprove
    obtain ⟨a, ha⟩ := himprove
    obtain ⟨j, hj, hjscale⟩ := hcover (gapStar ρ a) (LibraryDetection45TradeFacts.gapStar_nonneg ρ a)
      (LibraryDetection45TradeFacts.gapStar_le_one hK ρ hρ a)
    have hsep := detection_at_scale hK ρ hρ (ε j) x (R j) (hest j) μ hμ a hj ha hjscale
    apply hsep.trans
    apply Finset.sum_le_sum
    intro b _
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    change 4 * nj j b ≤ 4 * ∑ i, nj i b
    exact mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (fun i _ => hnj i b) (Finset.mem_univ j)) (by norm_num)

/-- A checked reduction from the exact localized-estimation statement to detection. -/
theorem detection_of_localized_estimation
    (hestimation :
      ∃ C : ℝ, ∀ K : ℕ, 2 ≤ K → ∀ ρ : Grid K × Act K → ℝ, IsDist ρ →
        ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
          ∃ (R : BilateralProfit.QTree (Act K) (Act K → ℝ)) (N : ℕ),
            (N : ℝ) ≤ C * Real.log K ^ 3 * ((K : ℝ) / ε ^ 2 + Real.log K ^ 3 / ε ^ 3) ∧
            R.QueriesAtMost N ∧ R.AllQueries (fun a => gapStar ρ a ≤ 2 * ε) ∧
            EstimationGuarantee ρ ε R) :
    ∃ C : ℝ, ∀ K : ℕ, 2 ≤ K → ∀ ρ : Grid K × Act K → ℝ, IsDist ρ →
      ∀ x : ℝ, 0 < x → x ≤ 1 →
        ∃ n : Act K → ℝ, (∀ a, 0 ≤ n a) ∧
          ∑ a, n a * (gapStar ρ a + x) ≤
            C * Real.log K ^ 3 * ((K : ℝ) / x + Real.log K ^ 3 / x ^ 2) ∧
          ∀ μ : Measure (ℝ × ℝ), IsValLaw μ →
            (∃ a : Act K, optVal ρ + x ≤ muP μ (pt K a.1)) →
              1 ≤ ∑ a, n a * (Ptrade μ (pt K a.1) - P0 ρ (pt K a.1)) ^ 2 := by
  classical
  obtain ⟨C, hC⟩ := hestimation
  refine ⟨48 * max C 0, ?_⟩
  intro K hK ρ hρ x hx hx1
  obtain ⟨J, ε, hε, hcover, hsum1, hsum2⟩ := LibraryDetection45Scales.scales x hx hx1
  have hlog : 0 ≤ Real.log K := Real.log_nonneg (by exact_mod_cast (show 1 ≤ K by omega))
  have hall (j : Fin (J + 1)) :
      ∃ (R : BilateralProfit.QTree (Act K) (Act K → ℝ)) (N : ℕ),
        (N : ℝ) ≤ max C 0 * Real.log K ^ 3 *
          ((K : ℝ) / (ε j) ^ 2 + Real.log K ^ 3 / (ε j) ^ 3) ∧
          R.QueriesAtMost N ∧ R.AllQueries (fun a => gapStar ρ a ≤ 2 * ε j) ∧
          EstimationGuarantee ρ (ε j) R := by
    have hjpos : 0 < ε j := hx.trans_le (hε j).1
    obtain ⟨R, N, hb, hc, hq, he⟩ := hC K hK ρ hρ (ε j) hjpos (hε j).2
    refine ⟨R, N, hb.trans ?_, hc, hq, he⟩
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left C 0) (by positivity)) (by positivity)
  choose R N hprops using hall
  exact detection_from_scales (by omega) ρ hρ x (max C 0) hx (le_max_right C 0)
    ε hε hcover hsum1 hsum2 R N (fun j => (hprops j).1)
    (fun j => (hprops j).2.1) (fun j => (hprops j).2.2.1) (fun j => (hprops j).2.2.2)

end BilateralProfit.LibraryDetection45
open MeasureTheory BilateralProfit

theorem solution :
    ∃ C : ℝ, ∀ K : ℕ, 2 ≤ K → ∀ ρ : Grid K × Act K → ℝ, IsDist ρ →
      ∀ x : ℝ, 0 < x → x ≤ 1 →
        ∃ n : Act K → ℝ, (∀ a, 0 ≤ n a) ∧
          ∑ a, n a * (gapStar ρ a + x) ≤
            C * Real.log K ^ 3 * ((K : ℝ) / x + Real.log K ^ 3 / x ^ 2) ∧
          ∀ μ : Measure (ℝ × ℝ), IsValLaw μ →
            (∃ a : Act K, optVal ρ + x ≤ muP μ (pt K a.1)) →
              1 ≤ ∑ a, n a * (Ptrade μ (pt K a.1) - P0 ρ (pt K a.1)) ^ 2 := by
  exact BilateralProfit.LibraryDetection45.detection_of_localized_estimation BilateralProfit.lemma_4_8
