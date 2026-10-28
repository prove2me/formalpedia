-- Prove2me | solution 1 for BootRobust.Perf.theorem_6
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-27T10:03:18.546983+00:00
-- url     : https://prove2.me/submissions/d12ad6f6-bd96-4bdf-99c0-9a2b4e906f2d

import Mathlib
import Definitions.Def_BootRobust_Perf_Setting

-- Complete module: BRProof/PartialRatio.lean

open MeasureTheory Set
open scoped BigOperators

namespace BootRobust.Perf.BRFresh

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def weightedMass (w D : ι → ℝ) (S : Finset ι) : ℝ := ∑ i ∈ S, w i * D i

def weightedLoss (w ℓ D : ι → ℝ) (S : Finset ι) : ℝ := ∑ i ∈ S, w i * ℓ i * D i

omit [Fintype ι] [DecidableEq ι] in
theorem weightedMass_pos {D w : ι → ℝ} {S : Finset ι}
    (hD : ∀ i, 0 ≤ D i) (hw : ∀ i, 0 < w i) (hm : 0 < mass D S) :
    0 < weightedMass w D S := by
  obtain ⟨i, hi, hDi⟩ := (Finset.sum_pos_iff_of_nonneg (fun i (_ : i ∈ S) => hD i)).mp hm
  exact Finset.sum_pos' (fun i _ => mul_nonneg (hw i).le (hD i))
    ⟨i, hi, mul_pos (hw i) hDi⟩

omit [DecidableEq ι] in
theorem dj_weightedMass_pos {n k j : ℕ} {N : ℕ → Finset ι} {w D : ι → ℝ}
    (hn : 1 ≤ n) (hk : 1 ≤ k) (hw : ∀ i, 0 < w i) (hD : D ∈ Dj n k N j) :
    0 < weightedMass w D (N j) :=
  weightedMass_pos hD.1.1 hw ((div_pos (by positivity : (0:ℝ) < k) (by positivity : (0:ℝ) < n)).trans_le hD.2.2)

omit [DecidableEq ι] in
theorem lp_scale_unique {n k j : ℕ} {N : ℕ → Finset ι} {w D P : ι → ℝ} {s : ℝ}
    (hp : lpFeasible n k N w j D s P) : s * weightedMass w D (N j) = 1 := by
  calc
    _ = ∑ i ∈ N j, w i * (s * D i) := by
      simp only [weightedMass, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = ∑ i ∈ N j, w i * P i := by simp only [hp.2.2.1]
    _ = 1 := hp.2.2.2.2.1

omit [DecidableEq ι] in
theorem lp_ratio_value {n k j : ℕ} {N : ℕ → Finset ι} {w ℓ D P : ι → ℝ} {s : ℝ}
    (hp : lpFeasible n k N w j D s P) :
    (∑ i ∈ N j, w i * ℓ i * P i) = weightedLoss w ℓ D (N j) / weightedMass w D (N j) := by
  have hs := lp_scale_unique hp
  have hW : weightedMass w D (N j) ≠ 0 := by intro h; rw [h, mul_zero] at hs; norm_num at hs
  have hobj : (∑ i ∈ N j, w i * ℓ i * P i) = s * weightedLoss w ℓ D (N j) := by
    simp only [← hp.2.2.1, weightedLoss, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  apply (eq_div_iff hW).mpr
  rw [hobj]
  calc
    _ = (s * weightedMass w D (N j)) * weightedLoss w ℓ D (N j) := by ring
    _ = weightedLoss w ℓ D (N j) := by rw [hs, one_mul]

omit [DecidableEq ι] in
theorem lp_ratio_feasible {n k j : ℕ} {N : ℕ → Finset ι} {w D : ι → ℝ}
    (hn : 1 ≤ n) (hk : 1 ≤ k) (hw : ∀ i, 0 < w i) (hD : D ∈ Dj n k N j) :
    lpFeasible n k N w j D (weightedMass w D (N j))⁻¹
      (fun i => (weightedMass w D (N j))⁻¹ * D i) := by
  have hW := dj_weightedMass_pos hn hk hw hD
  refine ⟨inv_pos.mpr hW, fun i => mul_nonneg (inv_nonneg.mpr hW.le) (hD.1.1 i),
    fun _ => rfl, ?_, ?_, ?_, ?_⟩
  · rw [← Finset.mul_sum, hD.1.2, mul_one]
  · calc
      _ = (weightedMass w D (N j))⁻¹ * weightedMass w D (N j) := by
        simp only [weightedMass, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = 1 := inv_mul_cancel₀ hW.ne'
  · rw [← Finset.mul_sum]
    calc
      _ = (weightedMass w D (N j))⁻¹ * ((k : ℝ) / n) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hD.2.2 (inv_nonneg.mpr hW.le)
  · rw [← Finset.mul_sum]
    exact (mul_le_mul_of_nonneg_left hD.2.1 (inv_nonneg.mpr hW.le)).trans_eq (by ring)

omit [DecidableEq ι] in
theorem partialEst_eq_ratio {n k j : ℕ} {N : ℕ → Finset ι} {w ℓ D : ι → ℝ}
    (hn : 1 ≤ n) (hk : 1 ≤ k) (hw : ∀ i, 0 < w i) (hD : D ∈ Dj n k N j) :
    partialEst n k N w ℓ j D =
      ((weightedLoss w ℓ D (N j) / weightedMass w D (N j) : ℝ) : EReal) := by
  apply le_antisymm
  · apply iSup_le
    intro p
    apply iSup_le
    intro hp
    exact le_of_eq (congrArg (fun x : ℝ => (x : EReal)) (lp_ratio_value hp))
  · have hp := lp_ratio_feasible hn hk hw hD
    have hv := lp_ratio_value (ℓ := ℓ) hp
    exact le_iSup_of_le ((weightedMass w D (N j))⁻¹,
      fun i => (weightedMass w D (N j))⁻¹ * D i)
      (le_iSup_of_le hp (le_of_eq (congrArg (fun x : ℝ => (x : EReal)) hv.symm)))

end BootRobust.Perf.BRFresh

-- Complete module: BRProof/FirstNeighborhood.lean

open MeasureTheory Set
open scoped BigOperators

namespace BootRobust.Perf.BRFresh

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem mass_integral {n : ℕ} {D : ι → ℝ} (hD : D ∈ Dnn n) (S : Finset ι) :
    ∃ q : ℕ, (n : ℝ) * mass D S = q := by
  classical
  choose q _hq hq using hD.2
  refine ⟨∑ i ∈ S, q i, ?_⟩
  simp only [mass, Finset.mul_sum, hq, Nat.cast_sum]

omit [DecidableEq ι] in
theorem jstar_mem_Dj {n k : ℕ} {N : ℕ → Finset ι} {D : ι → ℝ}
    (hn : 1 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n)
    (hN0 : N 0 = ∅) (hNn : N n = Finset.univ) (hD : D ∈ Dnn n) :
    jstar n k N D ∈ Finset.Icc 1 n ∧ D ∈ Dj n k N (jstar n k N D) := by
  have hn0 : (0 : ℝ) < n := by positivity
  have hk0 : (0 : ℝ) < k := by positivity
  have hreach : (k : ℝ) / n ≤ mass D (N n) := by
    rw [hNn]
    change (k : ℝ) / n ≤ ∑ i, D i
    rw [hD.1.2]
    exact (div_le_one hn0).mpr (by exact_mod_cast hkn)
  have hne : {j : ℕ | (k : ℝ) / n ≤ mass D (N j)}.Nonempty := ⟨n, hreach⟩
  have hmem : (k : ℝ) / n ≤ mass D (N (jstar n k N D)) := Nat.sInf_mem hne
  have hjn : jstar n k N D ≤ n := Nat.sInf_le hreach
  have hj0 : jstar n k N D ≠ 0 := by
    intro he
    rw [he, hN0] at hmem
    simp only [mass, Finset.sum_empty] at hmem
    exact (div_pos hk0 hn0).not_ge hmem
  have hj1 : 1 ≤ jstar n k N D := by omega
  have hprev : mass D (N (jstar n k N D - 1)) < (k : ℝ) / n := by
    by_contra! hh
    have hmin : jstar n k N D ≤ jstar n k N D - 1 := Nat.sInf_le hh
    omega
  obtain ⟨q, hq⟩ := mass_integral hD (N (jstar n k N D - 1))
  have hqk : (q : ℝ) < k := by
    have hb := (lt_div_iff₀ hn0).mp hprev
    nlinarith
  have hqk' : q + 1 ≤ k := by
    have hqkNat : q < k := by exact_mod_cast hqk
    omega
  have hqle : (q : ℝ) + 1 ≤ k := by exact_mod_cast hqk'
  refine ⟨Finset.mem_Icc.mpr ⟨hj1, hjn⟩, hD.1, ?_, hmem⟩
  apply (le_div_iff₀ hn0).mpr
  nlinarith

omit [DecidableEq ι] in
theorem nominal_eq_partial {n k : ℕ} {N : ℕ → Finset ι} {w ℓ D : ι → ℝ}
    (hn : 1 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n)
    (hN0 : N 0 = ∅) (hNn : N n = Finset.univ) (hw : ∀ i, 0 < w i)
    (hD : D ∈ Dnn n) :
    ((nominalEst n k N w ℓ D : ℝ) : EReal) = partialEst n k N w ℓ (jstar n k N D) D := by
  rw [partialEst_eq_ratio hn hk hw (jstar_mem_Dj hn hk hkn hN0 hNn hD).2]
  congr 1
  unfold nominalEst weightedLoss weightedMass
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

end BootRobust.Perf.BRFresh

-- Complete module: BRProof/EmpiricalBasics.lean

open MeasureTheory Set
open scoped BigOperators

namespace BootRobust.Perf.BRFresh

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem empirical_test {n : ℕ} (ω : Fin n → ι) (f : ι → ℝ) :
    ∑ i, empDist ω i * f i = (∑ t, f (ω t)) / n := by
  have hc (i : ι) : ((Finset.univ.filter (fun t => ω t = i)).card : ℝ) =
      ∑ t : Fin n, if ω t = i then (1 : ℝ) else 0 := by simp
  simp only [empDist, div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  congr 1
  simp_rw [hc, Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

theorem empDist_mem_simplex {n : ℕ} (hn : 1 ≤ n) (ω : Fin n → ι) :
    empDist ω ∈ stdSimplex ℝ ι := by
  refine ⟨fun i => by unfold empDist; positivity, ?_⟩
  have hh := empirical_test ω (fun _ => 1)
  simpa only [mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, div_self (show (n : ℝ) ≠ 0 by positivity)] using hh

theorem empDist_mem_Dnn {n : ℕ} (hn : 1 ≤ n) (ω : Fin n → ι) : empDist ω ∈ Dnn n := by
  refine ⟨empDist_mem_simplex hn ω, fun i => ?_⟩
  refine ⟨(Finset.univ.filter (fun t => ω t = i)).card, ?_, ?_⟩
  · exact (Finset.card_filter_le _ _).trans (by simp)
  · unfold empDist
    field_simp

theorem mass_empDist {n : ℕ} (ω : Fin n → ι) (S : Finset ι) :
    mass (empDist ω) S = ((Finset.univ.filter (fun t => ω t ∈ S)).card : ℝ) / n := by
  have hh := empirical_test ω (fun i => if i ∈ S then 1 else 0)
  simpa [mass, Finset.sum_filter, mul_ite] using hh

end BootRobust.Perf.BRFresh

-- Complete module: BRProof/ConvexEvents.lean

open MeasureTheory Set
open scoped BigOperators

namespace BootRobust.Perf.BRFresh

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem mass_combo (D E : ι → ℝ) (S : Finset ι) (a b : ℝ) :
    mass (a • D + b • E) S = a * mass D S + b * mass E S := by
  simp only [mass, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, Finset.mul_sum]

omit [Fintype ι] [DecidableEq ι] in
theorem weightedMass_combo (w D E : ι → ℝ) (S : Finset ι) (a b : ℝ) :
    weightedMass w (a • D + b • E) S = a * weightedMass w D S + b * weightedMass w E S := by
  simp only [weightedMass, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
    Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> ring

omit [Fintype ι] [DecidableEq ι] in
theorem weightedLoss_combo (w ℓ D E : ι → ℝ) (S : Finset ι) (a b : ℝ) :
    weightedLoss w ℓ (a • D + b • E) S = a * weightedLoss w ℓ D S + b * weightedLoss w ℓ E S := by
  simp only [weightedLoss, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
    Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> ring

omit [DecidableEq ι] in
theorem convex_Dj (n k : ℕ) (N : ℕ → Finset ι) (j : ℕ) : Convex ℝ (Dj n k N j) := by
  intro D hD E hE a b ha hb hab
  refine ⟨convex_stdSimplex ℝ ι hD.1 hE.1 ha hb hab, ?_, ?_⟩
  · rw [mass_combo]
    have h1 := mul_le_mul_of_nonneg_left hD.2.1 ha
    have h2 := mul_le_mul_of_nonneg_left hE.2.1 hb
    exact (add_le_add h1 h2).trans_eq (by rw [← add_mul, hab, one_mul])
  · rw [mass_combo]
    have h1 := mul_le_mul_of_nonneg_left hD.2.2 ha
    have h2 := mul_le_mul_of_nonneg_left hE.2.2 hb
    exact (show (k : ℝ) / n = a * ((k : ℝ) / n) + b * ((k : ℝ) / n) by rw [← add_mul, hab, one_mul]).trans_le (add_le_add h1 h2)

omit [DecidableEq ι] in
theorem mem_Cj_real_iff {n k j : ℕ} {N : ℕ → Finset ι} {w ℓ D : ι → ℝ}
    (hn : 1 ≤ n) (hk : 1 ≤ k) (hw : ∀ i, 0 < w i) (c : ℝ) :
    D ∈ Cj n k N w ℓ (c : EReal) j ↔
      D ∈ Dj n k N j ∧ c * weightedMass w D (N j) < weightedLoss w ℓ D (N j) := by
  constructor
  · intro hD
    refine ⟨hD.1, ?_⟩
    have hh := hD.2
    rw [partialEst_eq_ratio hn hk hw hD.1, EReal.coe_lt_coe_iff,
      lt_div_iff₀ (dj_weightedMass_pos hn hk hw hD.1)] at hh
    exact hh
  · intro hD
    refine ⟨hD.1, ?_⟩
    rw [partialEst_eq_ratio hn hk hw hD.1, EReal.coe_lt_coe_iff,
      lt_div_iff₀ (dj_weightedMass_pos hn hk hw hD.1)]
    exact hD.2

omit [DecidableEq ι] in
theorem convex_Cj {n k : ℕ} (N : ℕ → Finset ι) (w ℓ : ι → ℝ) (c : EReal) (j : ℕ)
    (hn : 1 ≤ n) (hk : 1 ≤ k) (hw : ∀ i, 0 < w i) :
    Convex ℝ (Cj n k N w ℓ c j) := by
  induction c using EReal.rec with
  | top =>
    have he : Cj n k N w ℓ ⊤ j = ∅ := by ext D; simp [Cj]
    rw [he]
    exact convex_empty
  | bot =>
    have he : Cj n k N w ℓ ⊥ j = Dj n k N j := by
      ext D
      constructor
      · exact fun hD => hD.1
      · intro hD
        refine ⟨hD, ?_⟩
        rw [partialEst_eq_ratio hn hk hw hD]
        exact EReal.bot_lt_coe _
    rw [he]
    exact convex_Dj n k N j
  | coe c =>
    intro D hD E hE a b ha hb hab
    rw [mem_Cj_real_iff hn hk hw c] at hD hE ⊢
    refine ⟨convex_Dj n k N j hD.1 hE.1 ha hb hab, ?_⟩
    rw [weightedMass_combo, weightedLoss_combo]
    have hgapD : 0 < weightedLoss w ℓ D (N j) - c * weightedMass w D (N j) := sub_pos.mpr hD.2
    have hgapE : 0 < weightedLoss w ℓ E (N j) - c * weightedMass w E (N j) := sub_pos.mpr hE.2
    have hpos : 0 < a * (weightedLoss w ℓ D (N j) - c * weightedMass w D (N j)) +
        b * (weightedLoss w ℓ E (N j) - c * weightedMass w E (N j)) := by
      by_cases ha' : 0 < a
      · exact add_pos_of_pos_of_nonneg (mul_pos ha' hgapD) (mul_nonneg hb hgapE.le)
      · have hb' : 0 < b := by linarith
        exact add_pos_of_nonneg_of_pos (mul_nonneg ha hgapD.le) (mul_pos hb' hgapE)
    nlinarith

end BootRobust.Perf.BRFresh

-- Complete module: BRProof/BudgetEvents.lean

open MeasureTheory Set
open scoped BigOperators

namespace BootRobust.Perf.BRFresh

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem Cj_subset_simplex (n k : ℕ) (N : ℕ → Finset ι) (w ℓ : ι → ℝ) (c : EReal) (j : ℕ) :
    Cj n k N w ℓ c j ⊆ stdSimplex ℝ ι := fun _ h => h.1.1

omit [DecidableEq ι] in
theorem budget_event_radius {n k j : ℕ} {N : ℕ → Finset ι} {w ℓ D Dtr : ι → ℝ} {r : ℝ}
    (hj : j ∈ Finset.Icc 1 n)
    (hD : D ∈ Cj n k N w ℓ (robustBudget n k N w ℓ Dtr r) j) :
    max (r : EReal) (rj n k N Dtr j) ≤ bootDist D Dtr := by
  have hr : (r : EReal) < bootDist D Dtr := by
    by_contra! he
    have hb : partialEst n k N w ℓ j D ≤ robustBudget n k N w ℓ Dtr r :=
      le_iSup_of_le j (le_iSup_of_le hj (le_iSup_of_le D (le_iSup_of_le ⟨hD.1.1, he⟩ le_rfl)))
    exact hD.2.not_ge hb
  exact max_le hr.le (iInf_le_of_le D (iInf_le_of_le hD.1 le_rfl))

theorem disappointment_subset {n k : ℕ} {N : ℕ → Finset ι} {w ℓ Dtr : ι → ℝ} {r : ℝ}
    (hn : 1 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n)
    (hN0 : N 0 = ∅) (hNn : N n = Finset.univ) (hw : ∀ i, 0 < w i) :
    {ω : Fin n → ι | robustBudget n k N w ℓ Dtr r <
      ((nominalEst n k N w ℓ (empDist ω) : ℝ) : EReal)} ⊆
    ⋃ j ∈ Finset.Icc 1 n, {ω | empDist ω ∈ Cj n k N w ℓ (robustBudget n k N w ℓ Dtr r) j} := by
  intro ω hω
  have hD := empDist_mem_Dnn hn ω
  have hj := jstar_mem_Dj hn hk hkn hN0 hNn hD
  refine mem_iUnion.mpr ⟨jstar n k N (empDist ω), mem_iUnion.mpr ⟨hj.1, hj.2, ?_⟩⟩
  change robustBudget n k N w ℓ Dtr r < ((nominalEst n k N w ℓ (empDist ω) : ℝ) : EReal) at hω
  rwa [nominal_eq_partial hn hk hkn hN0 hNn hw hD] at hω

end BootRobust.Perf.BRFresh

-- Complete module: BRProof/SharedBasics.lean

-- Complete module: BRProof/FiniteGibbs.lean

open scoped BigOperators

namespace BootRobust.Perf.BRFresh

/-- The finite log-sum inequality, allowing missing mass on the comparison side. -/
theorem finite_gibbs {α : Type*} (s : Finset α) (p q : α → ℝ)
    (hp : ∀ i ∈ s, 0 < p i) (hq : ∀ i ∈ s, 0 < q i)
    (hs : ∑ i ∈ s, p i = 1) (ht : ∑ i ∈ s, q i ≤ 1) :
    ∑ i ∈ s, p i * Real.log (q i / p i) ≤ 0 := by
  have hterm (i) (hi : i ∈ s) :
      p i * Real.log (q i / p i) ≤ q i - p i := by
    have h := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (div_pos (hq i hi) (hp i hi))) (hp i hi).le
    have he : p i * (q i / p i - 1) = q i - p i := by
      field_simp [(hp i hi).ne']
    exact h.trans_eq he
  calc
    _ ≤ ∑ i ∈ s, (q i - p i) := Finset.sum_le_sum hterm
    _ = (∑ i ∈ s, q i) - 1 := by rw [Finset.sum_sub_distrib, hs]
    _ ≤ 0 := by linarith

end BootRobust.Perf.BRFresh

-- Complete module: BRProof/ProductWeights.lean

open MeasureTheory Set
open scoped BigOperators

namespace BootRobust.Perf.BRFresh

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def wordWeight (p : ι → ℝ) {n : ℕ} (ω : Fin n → ι) : ℝ := ∏ t, p (ω t)

omit [Fintype ι] [DecidableEq ι] in
theorem wordWeight_nonneg (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) {n : ℕ}
    (ω : Fin n → ι) : 0 ≤ wordWeight p ω := Finset.prod_nonneg (fun _ _ => hp _)

omit [Fintype ι] [DecidableEq ι] in
theorem wordWeight_pos (p : ι → ℝ) (hp : ∀ i, 0 < p i) {n : ℕ}
    (ω : Fin n → ι) : 0 < wordWeight p ω := Finset.prod_pos (fun _ _ => hp _)

omit [DecidableEq ι] in
theorem sum_wordWeight (p : ι → ℝ) (hp : ∑ i, p i = 1) (n : ℕ) :
    ∑ ω : Fin n → ι, wordWeight p ω = 1 := by
  unfold wordWeight
  rw [← Fintype.sum_pow, hp, one_pow]

section Measure
variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem drawLaw_singleton (p : ι → ℝ) (i : ι) :
    drawLaw p {i} = ENNReal.ofReal (p i) := by
  simp [drawLaw, Pi.single_apply]

theorem bootLaw_singleton (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) {n : ℕ}
    (ω : Fin n → ι) : bootLaw p n {ω} = ENNReal.ofReal (wordWeight p ω) := by
  rw [bootLaw, Measure.pi_singleton]
  simp_rw [drawLaw_singleton]
  exact (ENNReal.ofReal_prod_of_nonneg (fun _ _ => hp _)).symm

theorem bootLaw_finset (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) {n : ℕ}
    (s : Finset (Fin n → ι)) :
    bootLaw p n (s : Set (Fin n → ι)) = ENNReal.ofReal (∑ ω ∈ s, wordWeight p ω) := by
  rw [← sum_measure_singleton]
  simp_rw [bootLaw_singleton p hp]
  exact (ENNReal.ofReal_sum_of_nonneg (fun _ _ => wordWeight_nonneg p hp _)).symm

end Measure
end BootRobust.Perf.BRFresh

-- Complete module: BRProof/EmpiricalMean.lean

open scoped BigOperators

namespace BootRobust.Perf.BRFresh
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def empiricalMean {n : ℕ} (s : Finset (Fin n → ι)) (a : (Fin n → ι) → ℝ) : ι → ℝ :=
  ∑ ω ∈ s, a ω • empDist ω

omit [Fintype ι] in
theorem empiricalMean_apply {n : ℕ} (s : Finset (Fin n → ι)) (a : (Fin n → ι) → ℝ)
    (i : ι) : empiricalMean s a i = ∑ ω ∈ s, a ω * empDist ω i := by
  simp [empiricalMean, Finset.sum_apply]

omit [Fintype ι] in
theorem empiricalMean_mem {n : ℕ} (s : Finset (Fin n → ι)) (a : (Fin n → ι) → ℝ)
    {C : Set (ι → ℝ)} (hC : Convex ℝ C) (ha : ∀ ω ∈ s, 0 ≤ a ω)
    (hs : ∑ ω ∈ s, a ω = 1) (hm : ∀ ω ∈ s, empDist ω ∈ C) :
    empiricalMean s a ∈ C := hC.sum_mem ha hs hm

theorem empiricalMean_test {n : ℕ} (hn : 1 ≤ n) (s : Finset (Fin n → ι))
    (a : (Fin n → ι) → ℝ) (f : ι → ℝ) :
    ∑ ω ∈ s, a ω * (∑ t, f (ω t)) =
      (n : ℝ) * ∑ i, empiricalMean s a i * f i := by
  simp_rw [empiricalMean_apply, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω hω
  rw [show (∑ i, a ω * empDist ω i * f i) =
    a ω * ∑ i, empDist ω i * f i by simp [Finset.mul_sum, mul_assoc]]
  rw [empirical_test]
  field_simp

theorem empiricalMean_letter_pos {n : ℕ} (hn : 1 ≤ n)
    (s : Finset (Fin n → ι)) (a : (Fin n → ι) → ℝ)
    (ha : ∀ ω ∈ s, 0 < a ω) {ω : Fin n → ι} (hω : ω ∈ s) (t : Fin n) :
    0 < empiricalMean s a (ω t) := by
  have hc : 0 < (Finset.univ.filter (fun u => ω u = ω t)).card :=
    Finset.card_pos.mpr ⟨t, by simp⟩
  have he : 0 < empDist ω (ω t) := by unfold empDist; positivity
  rw [empiricalMean_apply]
  exact (mul_pos (ha ω hω) he).trans_le
    (Finset.single_le_sum (fun v hv => mul_nonneg (ha v hv).le
      ((empDist_mem_simplex hn v).1 _)) hω)

end BootRobust.Perf.BRFresh

-- Complete module: BRProof/ConditionalEntropy.lean

open scoped BigOperators

namespace BootRobust.Perf.BRFresh
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem conditional_entropy_bound {n : ℕ} (hn : 1 ≤ n) (p : ι → ℝ)
    (hp : ∀ i, 0 < p i) (s : Finset (Fin n → ι))
    (a : (Fin n → ι) → ℝ) (ha : ∀ ω ∈ s, 0 < a ω)
    (hs : ∑ ω ∈ s, a ω = 1) (Z : ℝ) (hZ : 0 < Z)
    (hcond : ∀ ω ∈ s, a ω = wordWeight p ω / Z) :
    Real.log Z + (n : ℝ) * ∑ i, empiricalMean s a i *
      Real.log (empiricalMean s a i / p i) ≤ 0 := by
  let q := empiricalMean s a
  have hq : q ∈ stdSimplex ℝ ι := empiricalMean_mem s a (convex_stdSimplex ℝ ι)
    (fun ω hω => (ha ω hω).le) hs (fun ω _ => empDist_mem_simplex hn ω)
  have hletter (ω) (hω : ω ∈ s) (t : Fin n) : 0 < q (ω t) :=
    empiricalMean_letter_pos hn s a ha hω t
  have hprod (ω) (hω : ω ∈ s) : 0 < wordWeight q ω :=
    Finset.prod_pos (fun t _ => hletter ω hω t)
  have hsumq : ∑ ω ∈ s, wordWeight q ω ≤ 1 := by
    rw [← sum_wordWeight q hq.2 n]
    exact Finset.sum_le_univ_sum_of_nonneg (fun ω => wordWeight_nonneg q hq.1 ω)
  have hg := finite_gibbs s a (wordWeight q) ha hprod hs hsumq
  have hid (ω) (hω : ω ∈ s) :
      Real.log (wordWeight q ω / a ω) =
      (∑ t, (Real.log (q (ω t)) - Real.log (p (ω t)))) + Real.log Z := by
    rw [Real.log_div (hprod ω hω).ne' (ha ω hω).ne', hcond ω hω,
      Real.log_div (wordWeight_pos p hp ω).ne' hZ.ne']
    unfold wordWeight
    rw [Real.log_prod (fun t _ => (hletter ω hω t).ne'),
      Real.log_prod (fun t _ => (hp (ω t)).ne'), Finset.sum_sub_distrib]
    ring
  have hrewrite : (∑ ω ∈ s, a ω * Real.log (wordWeight q ω / a ω)) =
      ∑ ω ∈ s, a ω * ((∑ t, (Real.log (q (ω t)) - Real.log (p (ω t)))) + Real.log Z) := by
    apply Finset.sum_congr rfl
    intro ω hω
    rw [hid ω hω]
  rw [hrewrite] at hg
  have hmean := empiricalMean_test hn s a (fun i => Real.log (q i) - Real.log (p i))
  have hlog (i : ι) : q i * (Real.log (q i) - Real.log (p i)) =
      q i * Real.log (q i / p i) := by
    by_cases hi : q i = 0
    · simp [hi]
    · rw [Real.log_div hi (hp i).ne']
  have heq : (∑ ω ∈ s, a ω * ((∑ t, (Real.log (q (ω t)) - Real.log (p (ω t)))) +
      Real.log Z)) = (n : ℝ) * ∑ i, q i * Real.log (q i / p i) + Real.log Z := by
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hs, one_mul, hmean]
    change (n : ℝ) * (∑ i, q i * (Real.log (q i) - Real.log (p i))) + Real.log Z = _
    simp_rw [hlog]
  rw [heq] at hg
  simpa only [add_comm] using hg

end BootRobust.Perf.BRFresh

-- Complete module: BRProof/ConvexEventBound.lean

open MeasureTheory Set
open scoped BigOperators

namespace BootRobust.Perf.BRFresh
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

 theorem finite_convex_event_bound (p : ι → ℝ) (_hp : p ∈ stdSimplex ℝ ι)
    (hpos : ∀ i, 0 < p i) (n : ℕ) (hn : 1 ≤ n)
    (C : Set (ι → ℝ)) (hC : Convex ℝ C) (_hCsub : C ⊆ stdSimplex ℝ ι)
    (s : Finset (Fin n → ι)) (hsC : ∀ ω ∈ s, empDist ω ∈ C)
    (t : EReal) (hlower : ∃ r : ℝ, (r : EReal) ≤ t)
    (hKL : ∀ D ∈ C, t ≤ bootDist D p) :
    ENNReal.ofReal (∑ ω ∈ s, wordWeight p ω) ≤ expNeg n t := by
  classical
  by_cases hs : s.Nonempty
  · let Z := ∑ ω ∈ s, wordWeight p ω
    have hZ : 0 < Z := Finset.sum_pos (fun ω _ => wordWeight_pos p hpos ω) hs
    let a : (Fin n → ι) → ℝ := fun ω => wordWeight p ω / Z
    have ha (ω) (_ : ω ∈ s) : 0 < a ω := div_pos (wordWeight_pos p hpos ω) hZ
    have has : ∑ ω ∈ s, a ω = 1 := by
      dsimp [a]
      rw [← Finset.sum_div]
      exact div_self hZ.ne'
    let q := empiricalMean s a
    have hqC : q ∈ C := empiricalMean_mem s a hC (fun ω hω => (ha ω hω).le) has hsC
    have hdist : bootDist q p = ((∑ i, q i * Real.log (q i / p i) : ℝ) : EReal) := by
      rw [bootDist, if_pos]
      intro i hi
      exact False.elim ((hpos i).ne' hi)
    have htk := hKL q hqC
    rw [hdist] at htk
    have htTop : t ≠ ⊤ := ne_top_of_le_ne_top (by simp) htk
    obtain ⟨r, hr⟩ := hlower
    have htBot : t ≠ ⊥ := ne_bot_of_le_ne_bot (by simp) hr
    have hreal : t.toReal ≤ ∑ i, q i * Real.log (q i / p i) := by
      simpa using EReal.toReal_le_toReal htk htBot (by simp)
    have hent := conditional_entropy_bound hn p hpos s a ha has Z hZ (fun _ _ => rfl)
    have hlog : Real.log Z ≤ -((n : ℝ) * t.toReal) := by
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hm := mul_le_mul_of_nonneg_left hreal hn0
      dsimp [q] at hm
      linarith
    have hexp := Real.exp_le_exp.mpr hlog
    rw [Real.exp_log hZ] at hexp
    simpa only [expNeg, if_neg htTop] using ENNReal.ofReal_le_ofReal hexp
  · simp [Finset.not_nonempty_iff_eq_empty.mp hs]

 theorem convex_event_bound [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (p : ι → ℝ) (hp : p ∈ stdSimplex ℝ ι) (hpos : ∀ i, 0 < p i)
    (n : ℕ) (hn : 1 ≤ n) (C : Set (ι → ℝ)) (hC : Convex ℝ C)
    (hCsub : C ⊆ stdSimplex ℝ ι) (t : EReal)
    (hlower : ∃ r : ℝ, (r : EReal) ≤ t) (hKL : ∀ D ∈ C, t ≤ bootDist D p) :
    bootLaw p n {ω | empDist ω ∈ C} ≤ expNeg n t := by
  classical
  let s : Finset (Fin n → ι) := Finset.univ.filter (fun ω => empDist ω ∈ C)
  have he : (s : Set (Fin n → ι)) = {ω | empDist ω ∈ C} := by ext ω; simp [s]
  rw [← he, bootLaw_finset p hp.1]
  exact finite_convex_event_bound p hp hpos n hn C hC hCsub s
    (fun ω hω => (Finset.mem_filter.mp hω).2) t hlower hKL

end BootRobust.Perf.BRFresh

-- Complete module: BRProof/NativeConclusion.lean

open MeasureTheory Set
open scoped BigOperators

namespace BootRobust.Perf.BRFresh

theorem native_theorem_6 {ι : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n)
    (N : ℕ → Finset ι) (_hNmono : Monotone N) (hN0 : N 0 = ∅) (hNn : N n = Finset.univ)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (Dtr : ι → ℝ) (hDtr : Dtr ∈ stdSimplex ℝ ι)
    (hDtrpos : ∀ i, 0 < Dtr i) (r : ℝ) {Z : Type*} (L : Z → ι → ℝ) (z : Z) :
    bootLaw Dtr n
        {ω | robustBudget n k N w (L z) Dtr r <
          ((nominalEst n k N w (L z) (empDist ω) : ℝ) : EReal)} ≤
      ∑ j ∈ Finset.Icc 1 n, expNeg n (max (r : EReal) (rj n k N Dtr j)) := by
  classical
  let C : ℕ → Set (ι → ℝ) := fun j =>
    Cj n k N w (L z) (robustBudget n k N w (L z) Dtr r) j
  calc
    _ ≤ bootLaw Dtr n (⋃ j ∈ Finset.Icc 1 n, {ω | empDist ω ∈ C j}) :=
      measure_mono (disappointment_subset hn hk hkn hN0 hNn hw)
    _ ≤ ∑ j ∈ Finset.Icc 1 n, bootLaw Dtr n {ω | empDist ω ∈ C j} :=
      measure_biUnion_finset_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j hj
      exact convex_event_bound Dtr hDtr hDtrpos n hn (C j)
        (convex_Cj N w (L z) _ j hn hk hw)
        (Cj_subset_simplex n k N w (L z) _ j)
        (max (r : EReal) (rj n k N Dtr j)) ⟨r, le_max_left _ _⟩
        (fun _ hD => budget_event_radius hj hD)

end BootRobust.Perf.BRFresh

-- Complete module: BRProof/FinalRoot.lean

open MeasureTheory Set
open scoped BigOperators

namespace BootRobust.Perf

/-- Theorem 6, p. 15: the robust formulation with bootstrap distance `B` and radius `r`
suffers bootstrap disappointment (17) at most `∑_{j ∈ [n]} exp(−n · max{r, r^j_n})`: for any
decision `z`, the probability that the estimate (18) on the bootstrap data exceeds the robust
budget (26) computed on the training data is at most that sum. -/
theorem theorem_6 {ι : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n)
    (N : ℕ → Finset ι) (hNmono : Monotone N) (hN0 : N 0 = ∅) (hNn : N n = Finset.univ)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (Dtr : ι → ℝ) (hDtr : Dtr ∈ stdSimplex ℝ ι)
    (hDtrpos : ∀ i, 0 < Dtr i) (r : ℝ) {Z : Type*} (L : Z → ι → ℝ) (z : Z) :
    bootLaw Dtr n
        {ω | robustBudget n k N w (L z) Dtr r <
          ((nominalEst n k N w (L z) (empDist ω) : ℝ) : EReal)} ≤
      ∑ j ∈ Finset.Icc 1 n, expNeg n (max (r : EReal) (rj n k N Dtr j)) := by exact BRFresh.native_theorem_6 n k hn hk hkn N hNmono hN0 hNn w hw Dtr hDtr hDtrpos r L z

end BootRobust.Perf



open BootRobust.Perf MeasureTheory Set
open scoped BigOperators
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n)
    (N : ℕ → Finset ι) (hNmono : Monotone N) (hN0 : N 0 = ∅) (hNn : N n = Finset.univ)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (Dtr : ι → ℝ) (hDtr : Dtr ∈ stdSimplex ℝ ι)
    (hDtrpos : ∀ i, 0 < Dtr i) (r : ℝ) {Z : Type*} (L : Z → ι → ℝ) (z : Z) :
    bootLaw Dtr n
        {ω | robustBudget n k N w (L z) Dtr r <
          ((nominalEst n k N w (L z) (empDist ω) : ℝ) : EReal)} ≤
      ∑ j ∈ Finset.Icc 1 n, expNeg n (max (r : EReal) (rj n k N Dtr j)) := by
  exact BootRobust.Perf.theorem_6 n k hn hk hkn N hNmono hN0 hNn w hw Dtr hDtr hDtrpos r L z
