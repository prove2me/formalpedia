-- Prove2me | solution 1 for BassokSubstitution.no_order_above_base_stock
-- status  : ACCEPTED   (disprove)
-- author  : @sometik179
-- created : 2026-10-16T11:15:28.609006+00:00
-- url     : https://prove2.me/submissions/dc9fc9c2-432d-40da-a698-06b52db65fac

-- Licensed under Apache 2.0. Checked disproof of the entire exact native Theorem 2.
import Mathlib
import Definitions.Def_BassokSubstitution_Profit

section CompleteVerifiedFoundation

/- Complete verified reused body: TransportDefinitions -/

open scoped BigOperators
open BassokSubstitution

namespace BassokInventoryResearch

variable {N : ℕ}

def gain (M : Model N) (j i : Fin N) : ℝ :=
  M.netRevenue j i + M.penalty i - M.s j

def gainConstant (M : Model N) : ℝ := 1 + ∑ j, ∑ i, |gain M j i|

def rowSum (w : Fin N → Fin N → ℝ) (j : Fin N) : ℝ := ∑ i, w j i

def colSum (w : Fin N → Fin N → ℝ) (i : Fin N) : ℝ := ∑ j, w j i

def transportSet (y d : Fin N → ℝ) : Set (Fin N → Fin N → ℝ) :=
  {w | (∀ j i, 0 ≤ w j i) ∧ (∀ j i, i < j → w j i = 0) ∧
    (∀ j, rowSum w j ≤ y j) ∧ (∀ i, colSum w i ≤ d i)}

def gainValue (M : Model N) (w : Fin N → Fin N → ℝ) : ℝ :=
  ∑ j, ∑ i, gain M j i * w j i

noncomputable def transportValue (M : Model N) (y d : Fin N → ℝ) : ℝ :=
  sSup (gainValue M '' transportSet y d)

def baseline (M : Model N) (y d : Fin N → ℝ) : ℝ :=
  (∑ j, M.s j * y j) - ∑ i, M.penalty i * d i

theorem gainConstant_pos (M : Model N) : 0 < gainConstant M := by
  unfold gainConstant
  positivity

theorem abs_gain_le (M : Model N) (j i : Fin N) : |gain M j i| ≤ gainConstant M := by
  have hi : |gain M j i| ≤ ∑ i, |gain M j i| :=
    Finset.single_le_sum (fun a _ => abs_nonneg (gain M j a)) (Finset.mem_univ i)
  have hj : (∑ i, |gain M j i|) ≤ ∑ j, ∑ i, |gain M j i| :=
    Finset.single_le_sum (fun a _ => Finset.sum_nonneg (fun b _ => abs_nonneg (gain M a b)))
      (Finset.mem_univ j)
  unfold gainConstant
  linarith

theorem rowSum_nonneg {w : Fin N → Fin N → ℝ} (hw : ∀ j i, 0 ≤ w j i) (j) :
    0 ≤ rowSum w j := Finset.sum_nonneg (fun i _ => hw j i)

theorem colSum_nonneg {w : Fin N → Fin N → ℝ} (hw : ∀ j i, 0 ≤ w j i) (i) :
    0 ≤ colSum w i := Finset.sum_nonneg (fun j _ => hw j i)

theorem entry_le_row {w : Fin N → Fin N → ℝ} (hw : ∀ j i, 0 ≤ w j i) (j i) :
    w j i ≤ rowSum w j := Finset.single_le_sum (fun a _ => hw j a) (Finset.mem_univ i)

theorem entry_le_col {w : Fin N → Fin N → ℝ} (hw : ∀ j i, 0 ≤ w j i) (j i) :
    w j i ≤ colSum w i := Finset.single_le_sum (fun a _ => hw a i) (Finset.mem_univ j)

end BassokInventoryResearch

/- Complete verified reused body: TransportCompact -/

open scoped BigOperators
open BassokSubstitution

namespace BassokInventoryResearch

variable {N : ℕ}

theorem transport_zero {y d : Fin N → ℝ} (hy : 0 ≤ y) (hd : 0 ≤ d) :
    (0 : Fin N → Fin N → ℝ) ∈ transportSet y d := by
  simpa [transportSet, rowSum, colSum] using And.intro (show ∀ j, 0 ≤ y j from hy) (show ∀ i, 0 ≤ d i from hd)

theorem transport_closed (y d : Fin N → ℝ) : IsClosed (transportSet y d) := by
  unfold transportSet
  simp only [Set.ofPred_and, Set.ofPred_forall]
  apply IsClosed.inter
  · exact isClosed_iInter fun j => isClosed_iInter fun i =>
      isClosed_le continuous_const (by fun_prop)
  apply IsClosed.inter
  · exact isClosed_iInter fun j => isClosed_iInter fun i =>
      isClosed_iInter fun _ => isClosed_eq (by fun_prop) continuous_const
  apply IsClosed.inter
  · exact isClosed_iInter fun j => isClosed_le (by unfold rowSum; fun_prop) continuous_const
  · exact isClosed_iInter fun i => isClosed_le (by unfold colSum; fun_prop) continuous_const

theorem transport_compact (y d : Fin N → ℝ) : IsCompact (transportSet y d) := by
  apply (isCompact_Icc : IsCompact (Set.Icc (0 : Fin N → Fin N → ℝ) (fun j _ => y j))).of_isClosed_subset
    (transport_closed y d)
  intro w hw
  exact ⟨hw.1, fun j i => (entry_le_row hw.1 j i).trans (hw.2.2.1 j)⟩

theorem gainValue_continuous (M : Model N) : Continuous (gainValue M) := by
  unfold gainValue
  fun_prop

theorem transport_attained (M : Model N) {y d : Fin N → ℝ}
    (hy : 0 ≤ y) (hd : 0 ≤ d) :
    ∃ w ∈ transportSet y d, gainValue M w = transportValue M y d ∧
      ∀ v ∈ transportSet y d, gainValue M v ≤ gainValue M w := by
  obtain ⟨w, hw, hmax⟩ := (transport_compact y d).exists_isMaxOn
    ⟨0, transport_zero hy hd⟩ (gainValue_continuous M).continuousOn
  refine ⟨w, hw, ?_, hmax⟩
  apply le_antisymm
  · exact le_csSup ⟨gainValue M w, by rintro _ ⟨v,hv,rfl⟩; exact hmax hv⟩ ⟨w,hw,rfl⟩
  · exact csSup_le ⟨gainValue M w, w, hw, rfl⟩ (by rintro _ ⟨v,hv,rfl⟩; exact hmax hv)

theorem gainValue_le_transportValue (M : Model N) {y d : Fin N → ℝ}
    (hy : 0 ≤ y) (hd : 0 ≤ d) {w} (hw : w ∈ transportSet y d) :
    gainValue M w ≤ transportValue M y d := by
  obtain ⟨v, _, hv, hmax⟩ := transport_attained M hy hd
  exact hv ▸ hmax w hw

theorem transportValue_le (M : Model N) {y d : Fin N → ℝ}
    (hy : 0 ≤ y) (hd : 0 ≤ d) {a : ℝ}
    (ha : ∀ w ∈ transportSet y d, gainValue M w ≤ a) :
    transportValue M y d ≤ a := by
  obtain ⟨w, hw, hval, _⟩ := transport_attained M hy hd
  exact hval ▸ ha w hw

end BassokInventoryResearch

/- Complete verified reused body: NativeTransport -/

open scoped BigOperators
open BassokSubstitution

namespace BassokInventoryResearch

variable {N : ℕ}

theorem sum_Iic_eq {f : Fin N → ℝ} (i : Fin N) (hf : ∀ j, i < j → f j = 0) :
    ∑ j ∈ Finset.Iic i, f j = ∑ j, f j := by
  apply Finset.sum_subset (Finset.subset_univ _)
  intro j _ hj
  exact hf j (lt_of_not_ge (by simpa using hj))

def transportAllocation (y d : Fin N → ℝ) (w : Fin N → Fin N → ℝ) : Allocation N :=
  ⟨w, fun i => d i - colSum w i, fun j => y j - rowSum w j⟩

theorem transportAllocation_feasible {y d : Fin N → ℝ} {w}
    (hw : w ∈ transportSet y d) : (transportAllocation y d w).Feasible y d := by
  refine ⟨hw.2.1, hw.1, fun i => sub_nonneg.mpr (hw.2.2.2 i),
    fun j => sub_nonneg.mpr (hw.2.2.1 j), ?_, ?_⟩
  · intro i
    change d i - colSum w i + (∑ j ∈ Finset.Iic i, w j i) = d i
    rw [sum_Iic_eq i (fun j hj => hw.2.1 j i hj)]
    simp [colSum]
  · intro j
    change y j - rowSum w j + (∑ i, w j i) = y j
    simp [rowSum]

theorem feasible_transport {y d : Fin N → ℝ} {a : Allocation N}
    (ha : a.Feasible y d) : a.w ∈ transportSet y d := by
  refine ⟨ha.2.1, ha.1, fun j => ?_, fun i => ?_⟩
  · have := ha.2.2.2.2.2 j
    have := ha.2.2.2.1 j
    dsimp [rowSum]
    linarith
  · have h := ha.2.2.2.2.1 i
    rw [sum_Iic_eq i (fun j hj => ha.1 j i hj)] at h
    have := ha.2.2.1 i
    dsimp [colSum]
    linarith

theorem gainValue_expand (M : Model N) (w : Fin N → Fin N → ℝ) :
    gainValue M w = (∑ i, ∑ j, M.netRevenue j i * w j i) +
      (∑ i, M.penalty i * colSum w i) - ∑ j, M.s j * rowSum w j := by
  simp only [gainValue, gain, add_mul, sub_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, rowSum, colSum, Finset.mul_sum]
  rw [Finset.sum_comm (f := fun j i => M.netRevenue j i * w j i),
    Finset.sum_comm (f := fun j i => M.penalty i * w j i)]

theorem allocation_objective_eq (M : Model N) {y d : Fin N → ℝ} {a : Allocation N}
    (ha : a.Feasible y d) : M.allocObjective a = baseline M y d + gainValue M a.w := by
  have hu : ∀ i, a.u i = d i - colSum a.w i := by
    intro i
    have h := ha.2.2.2.2.1 i
    rw [sum_Iic_eq i (fun j hj => ha.1 j i hj)] at h
    dsimp [colSum]; linarith
  have hv : ∀ j, a.v j = y j - rowSum a.w j := by
    intro j; have := ha.2.2.2.2.2 j
    dsimp [rowSum]; linarith
  have hr : ∀ i, (∑ j ∈ Finset.Iic i, M.netRevenue j i * a.w j i) =
      ∑ j, M.netRevenue j i * a.w j i := by
    intro i; apply sum_Iic_eq; intro j hj; rw [ha.1 j i hj, mul_zero]
  simp only [Model.allocObjective, hr, hu, hv, baseline, gainValue_expand,
    mul_sub, Finset.sum_sub_distrib]
  ring

theorem G_eq_baseline_add (M : Model N) {y d : Fin N → ℝ}
    (hy : 0 ≤ y) (hd : 0 ≤ d) : M.G y d = baseline M y d + transportValue M y d := by
  obtain ⟨w, hw, hval, hmax⟩ := transport_attained M hy hd
  have hwa := transportAllocation_feasible hw
  have hobj := allocation_objective_eq M hwa
  change M.allocObjective (transportAllocation y d w) = baseline M y d + gainValue M w at hobj
  have hbound : ∀ a : Allocation N, a.Feasible y d →
      M.allocObjective a ≤ baseline M y d + transportValue M y d := by
    intro a ha
    rw [allocation_objective_eq M ha, ← hval]
    exact add_le_add le_rfl (hmax a.w (feasible_transport ha))
  unfold Model.G
  apply le_antisymm
  · apply csSup_le (show (M.allocObjective '' {a : Allocation N | a.Feasible y d}).Nonempty from
      ⟨M.allocObjective (transportAllocation y d w), transportAllocation y d w, hwa, rfl⟩)
    rintro _ ⟨a,ha,rfl⟩; exact hbound a ha
  · rw [← hval, ← hobj]
    exact le_csSup ⟨_, by rintro _ ⟨a,ha,rfl⟩; exact hbound a ha⟩
      ⟨transportAllocation y d w,hwa,rfl⟩

end BassokInventoryResearch

/- Complete verified reused body: NativeBounds -/

open scoped BigOperators
open BassokSubstitution

namespace BassokInventoryResearch

variable {N : ℕ}

theorem transportValue_nonneg (M : Model N) {y d : Fin N → ℝ}
    (hy : 0 ≤ y) (hd : 0 ≤ d) : 0 ≤ transportValue M y d := by
  simpa [gainValue] using gainValue_le_transportValue M hy hd (transport_zero hy hd)

theorem transportValue_upper (M : Model N) {y d : Fin N → ℝ}
    (hy : 0 ≤ y) (hd : 0 ≤ d) : transportValue M y d ≤ gainConstant M * ∑ i, d i := by
  apply transportValue_le M hy hd
  intro w hw
  calc
    gainValue M w ≤ ∑ j, ∑ i, gainConstant M * w j i := by
      apply Finset.sum_le_sum; intro j _
      apply Finset.sum_le_sum; intro i _
      exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans (abs_gain_le M j i)) (hw.1 j i)
    _ = gainConstant M * ∑ i, colSum w i := by
      simp only [Finset.mul_sum, colSum]; rw [Finset.sum_comm]
    _ ≤ gainConstant M * ∑ i, d i := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun i _ => hw.2.2.2 i)) (gainConstant_pos M).le

theorem abs_sum_mul_le {a y : Fin N → ℝ} (hy : 0 ≤ y) :
    |∑ i, a i * y i| ≤ ∑ i, |a i| * y i := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  exact Finset.sum_le_sum (fun i _ => by rw [abs_mul, abs_of_nonneg (hy i)])

theorem abs_G_le (M : Model N) {y d : Fin N → ℝ} (hy : 0 ≤ y) (hd : 0 ≤ d) :
    |M.G y d| ≤ (∑ j, |M.s j| * y j) + ∑ i, (|M.penalty i| + gainConstant M) * d i := by
  rw [G_eq_baseline_add M hy hd]
  have hb : |baseline M y d| ≤ (∑ j, |M.s j| * y j) + ∑ i, |M.penalty i| * d i :=
    (abs_sub _ _).trans (add_le_add (abs_sum_mul_le hy) (abs_sum_mul_le hd))
  have h := (abs_add_le (baseline M y d) (transportValue M y d)).trans
    (add_le_add hb (show |transportValue M y d| ≤ gainConstant M * ∑ i, d i from by
      rw [abs_of_nonneg (transportValue_nonneg M hy hd)]
      exact transportValue_upper M hy hd))
  simpa only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, add_assoc] using h

theorem G_upper_bound (M : Model N) {y d : Fin N → ℝ} (hy : 0 ≤ y) (hd : 0 ≤ d) :
    M.G y d ≤ (∑ j, M.s j * y j) + ∑ i, (|M.penalty i| + gainConstant M) * d i := by
  rw [G_eq_baseline_add M hy hd]
  have h := transportValue_upper M hy hd
  have hp : -(∑ i, M.penalty i * d i) ≤ ∑ i, |M.penalty i| * d i :=
    (neg_le_abs _).trans (abs_sum_mul_le hd)
  dsimp [baseline]
  simp only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
  linarith

end BassokInventoryResearch

/- Complete verified reused body: RowTrimming -/

open scoped BigOperators
open BassokSubstitution

namespace BassokInventoryResearch

variable {N : ℕ}

noncomputable def trimFactor (mass cap : ℝ) : ℝ := min mass cap / mass

theorem trimFactor_bounds {mass cap : ℝ} (hm : 0 ≤ mass) (hc : 0 ≤ cap) :
    0 ≤ trimFactor mass cap ∧ trimFactor mass cap ≤ 1 ∧
      trimFactor mass cap * mass = min mass cap := by
  rcases hm.eq_or_lt with hm | hm
  · subst mass; simp [trimFactor, min_eq_left hc]
  · refine ⟨div_nonneg (le_min hm.le hc) hm.le, ?_, ?_⟩
    · exact (div_le_one hm).mpr (min_le_left _ _)
    · exact div_mul_cancel₀ _ (ne_of_gt hm)

noncomputable def rowTrim (w : Fin N → Fin N → ℝ) (cap : Fin N → ℝ) (j i : Fin N) : ℝ :=
  trimFactor (rowSum w j) (cap j) * w j i

theorem rowTrim_nonneg {w : Fin N → Fin N → ℝ} {cap : Fin N → ℝ}
    (hw : ∀ j i, 0 ≤ w j i) (hc : 0 ≤ cap) : ∀ j i, 0 ≤ rowTrim w cap j i := by
  intro j i
  exact mul_nonneg (trimFactor_bounds (rowSum_nonneg hw j) (hc j)).1 (hw j i)

theorem rowTrim_le {w : Fin N → Fin N → ℝ} {cap : Fin N → ℝ}
    (hw : ∀ j i, 0 ≤ w j i) (hc : 0 ≤ cap) : ∀ j i, rowTrim w cap j i ≤ w j i := by
  intro j i
  exact mul_le_of_le_one_left (hw j i) (trimFactor_bounds (rowSum_nonneg hw j) (hc j)).2.1

theorem rowTrim_sum {w : Fin N → Fin N → ℝ} {cap : Fin N → ℝ}
    (hw : ∀ j i, 0 ≤ w j i) (hc : 0 ≤ cap) (j : Fin N) :
    rowSum (rowTrim w cap) j = min (rowSum w j) (cap j) := by
  unfold rowSum rowTrim
  rw [← Finset.mul_sum]
  exact (trimFactor_bounds (rowSum_nonneg hw j) (hc j)).2.2

theorem rowTrim_loss {w : Fin N → Fin N → ℝ} {cap y : Fin N → ℝ}
    (hw : ∀ j i, 0 ≤ w j i) (hc : 0 ≤ cap) (hy : ∀ j, rowSum w j ≤ y j) :
    (∑ j, ∑ i, (w j i - rowTrim w cap j i)) ≤ ∑ j, |y j - cap j| := by
  apply Finset.sum_le_sum
  intro j _
  change (∑ i, (w j i - rowTrim w cap j i)) ≤ _
  rw [Finset.sum_sub_distrib]
  change rowSum w j - rowSum (rowTrim w cap) j ≤ _
  rw [rowTrim_sum hw hc]
  rcases le_total (rowSum w j) (cap j) with h | h
  · rw [min_eq_left h, sub_self]; exact abs_nonneg _
  · rw [min_eq_right h]
    exact (sub_le_sub_right (hy j) _).trans (le_abs_self _)

end BassokInventoryResearch

/- Complete verified reused body: TransportTrimming -/

open scoped BigOperators
open BassokSubstitution

namespace BassokInventoryResearch

variable {N : ℕ}

theorem transport_trim {y d y' d' : Fin N → ℝ} {w}
    (hw : w ∈ transportSet y d) (hy' : 0 ≤ y') (hd' : 0 ≤ d') :
    ∃ v ∈ transportSet y' d', (∀ j i, v j i ≤ w j i) ∧
      (∑ j, ∑ i, (w j i - v j i)) ≤
        (∑ j, |y j - y' j|) + ∑ i, |d i - d' i| := by
  let w₁ := rowTrim w y'
  let wT := fun i j => w₁ j i
  let v := fun j i => rowTrim wT d' i j
  have h₁ := rowTrim_nonneg hw.1 hy'
  have h₁le := rowTrim_le hw.1 hy'
  have hT : ∀ i j, 0 ≤ wT i j := fun i j => h₁ j i
  have hv0 : ∀ j i, 0 ≤ v j i := fun j i => rowTrim_nonneg hT hd' i j
  have hv₁ : ∀ j i, v j i ≤ w₁ j i := fun j i => rowTrim_le hT hd' i j
  have hvw : ∀ j i, v j i ≤ w j i := fun j i => (hv₁ j i).trans (h₁le j i)
  have hrows : ∀ j, rowSum w₁ j ≤ y' j := fun j =>
    (rowTrim_sum hw.1 hy' j).le.trans (min_le_right _ _)
  have hcols : ∀ i, colSum w₁ i ≤ d i := fun i =>
    (Finset.sum_le_sum (fun j _ => h₁le j i)).trans (hw.2.2.2 i)
  refine ⟨v, ⟨hv0, ?_, ?_, ?_⟩, hvw, ?_⟩
  · intro j i hij
    exact le_antisymm (by simpa [hw.2.1 j i hij] using hvw j i) (hv0 j i)
  · intro j
    exact (Finset.sum_le_sum (fun i _ => hv₁ j i)).trans (hrows j)
  · intro i
    change rowSum (rowTrim wT d') i ≤ d' i
    rw [rowTrim_sum hT hd']
    exact min_le_right _ _
  · have hfirst := rowTrim_loss hw.1 hy' hw.2.2.1
    have hsecond := rowTrim_loss hT hd' hcols
    have hsecond' : (∑ j, ∑ i, (w₁ j i - v j i)) ≤ ∑ i, |d i - d' i| := by
      rw [Finset.sum_comm]
      exact hsecond
    have heq : (∑ j, ∑ i, (w j i - v j i)) =
        (∑ j, ∑ i, (w j i - w₁ j i)) + (∑ j, ∑ i, (w₁ j i - v j i)) := by
      simp only [← Finset.sum_add_distrib]
      congr 1; funext j
      congr 1; funext i
      ring
    rw [heq]
    exact add_le_add hfirst hsecond'

theorem gainValue_loss (M : Model N) {w v : Fin N → Fin N → ℝ}
    (hvw : ∀ j i, v j i ≤ w j i) :
    gainValue M w - gainValue M v ≤ gainConstant M * (∑ j, ∑ i, (w j i - v j i)) := by
  simp only [gainValue, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  apply Finset.sum_le_sum
  intro i _
  rw [← mul_sub]
  exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans (abs_gain_le M j i))
    (sub_nonneg.mpr (hvw j i))

theorem transportValue_le_add (M : Model N) {y d y' d' : Fin N → ℝ}
    (hy : 0 ≤ y) (hd : 0 ≤ d) (hy' : 0 ≤ y') (hd' : 0 ≤ d') :
    transportValue M y d ≤ transportValue M y' d' + gainConstant M *
      ((∑ j, |y j - y' j|) + ∑ i, |d i - d' i|) := by
  obtain ⟨w,hw,heq,_⟩ := transport_attained M hy hd
  obtain ⟨v,hv,hvw,hloss⟩ := transport_trim hw hy' hd'
  have hgain := gainValue_loss M hvw
  have hvval := gainValue_le_transportValue M hy' hd' hv
  have := mul_le_mul_of_nonneg_left hloss (gainConstant_pos M).le
  rw [← heq]
  linarith

theorem transportValue_lipschitz (M : Model N) {y d y' d' : Fin N → ℝ}
    (hy : 0 ≤ y) (hd : 0 ≤ d) (hy' : 0 ≤ y') (hd' : 0 ≤ d') :
    |transportValue M y d - transportValue M y' d'| ≤ gainConstant M *
      ((∑ j, |y j - y' j|) + ∑ i, |d i - d' i|) := by
  have h := transportValue_le_add M hy hd hy' hd'
  have h' := transportValue_le_add M hy' hd' hy hd
  simp only [abs_sub_comm (y' _), abs_sub_comm (d' _)] at h'
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end BassokInventoryResearch

/- Complete verified reused body: FiniteLipschitz -/

noncomputable section
open Set
open scoped BigOperators
namespace BassokInventoryResearch
variable {N : ℕ}

theorem continuousOn_of_sum_lipschitz {S : Set (Fin N → ℝ)} {F : (Fin N → ℝ) → ℝ}
    {K : ℝ} (hK : 0 ≤ K)
    (hF : ∀ y ∈ S, ∀ z ∈ S, |F y - F z| ≤ K * ∑ i, |y i - z i|) :
    ContinuousOn F S := by
  let C : NNReal := ⟨K * N, mul_nonneg hK (Nat.cast_nonneg N)⟩
  have hh : LipschitzOnWith C F S := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro y hy z hz
    rw [Real.dist_eq]
    apply (hF y hy z hz).trans
    have hs : (∑ i : Fin N, |y i - z i|) ≤ N * dist y z := by
      calc
        (∑ i : Fin N, |y i - z i|) ≤ ∑ _i : Fin N, dist y z := by
          apply Finset.sum_le_sum
          intro i _
          exact (Real.dist_eq (y i) (z i)) ▸ dist_le_pi_dist y z i
        _ = N * dist y z := by simp
    have hm := mul_le_mul_of_nonneg_left hs hK
    change K * ∑ i, |y i - z i| ≤ (K * N) * dist y z
    nlinarith
  exact hh.continuousOn

end BassokInventoryResearch
end

/- Complete verified reused body: NativeContinuity -/

open scoped BigOperators
open BassokSubstitution

namespace BassokInventoryResearch

variable {N : ℕ}

theorem weighted_sum_lipschitz (a y z : Fin N → ℝ) :
    |(∑ i, a i * y i) - ∑ i, a i * z i| ≤ (∑ i, |a i|) * ∑ i, |y i - z i| := by
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun j _ => abs_nonneg (a j)) (Finset.mem_univ i)) (abs_nonneg _)

theorem G_stock_lipschitz (M : Model N) {y z d : Fin N → ℝ}
    (hy : 0 ≤ y) (hz : 0 ≤ z) (hd : 0 ≤ d) :
    |M.G y d - M.G z d| ≤ (gainConstant M + ∑ j, |M.s j|) * ∑ j, |y j - z j| := by
  rw [G_eq_baseline_add M hy hd, G_eq_baseline_add M hz hd]
  have hg := transportValue_lipschitz M hy hd hz hd
  simp only [sub_self, abs_zero, Finset.sum_const_zero, add_zero] at hg
  have hb := weighted_sum_lipschitz M.s y z
  have heq : baseline M y d + transportValue M y d -
      (baseline M z d + transportValue M z d) =
      ((∑ j, M.s j * y j) - ∑ j, M.s j * z j) +
      (transportValue M y d - transportValue M z d) := by unfold baseline; ring
  rw [heq]
  exact (abs_add_le _ _).trans (by nlinarith [add_le_add hb hg])

theorem G_demand_lipschitz (M : Model N) {y d e : Fin N → ℝ}
    (hy : 0 ≤ y) (hd : 0 ≤ d) (he : 0 ≤ e) :
    |M.G y d - M.G y e| ≤ (gainConstant M + ∑ i, |M.penalty i|) * ∑ i, |d i - e i| := by
  rw [G_eq_baseline_add M hy hd, G_eq_baseline_add M hy he]
  have hg := transportValue_lipschitz M hy hd hy he
  simp only [sub_self, abs_zero, Finset.sum_const_zero, zero_add] at hg
  have hb := weighted_sum_lipschitz M.penalty d e
  have heq : baseline M y d + transportValue M y d -
      (baseline M y e + transportValue M y e) =
      -((∑ i, M.penalty i * d i) - ∑ i, M.penalty i * e i) +
      (transportValue M y d - transportValue M y e) := by unfold baseline; ring
  rw [heq]
  apply (abs_add_le _ _).trans
  rw [abs_neg]
  nlinarith [add_le_add hb hg]

theorem G_continuousOn_nonneg (M : Model N) {y : Fin N → ℝ} (hy : 0 ≤ y) :
    ContinuousOn (M.G y) {d | 0 ≤ d} := by
  apply continuousOn_of_sum_lipschitz (K := gainConstant M + ∑ i, |M.penalty i|)
  · exact add_nonneg (gainConstant_pos M).le (Finset.sum_nonneg (fun i _ => abs_nonneg _))
  · intro d hd e he
    exact G_demand_lipschitz M hy hd he

end BassokInventoryResearch

/- Complete verified reused body: DemandMeasure -/

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators
namespace BassokInventoryResearch
open BassokSubstitution
variable {N : ℕ}

def positivePart (d : Fin N → ℝ) : Fin N → ℝ := fun i => max (d i) 0

theorem positivePart_nonneg (d : Fin N → ℝ) : 0 ≤ positivePart d :=
  fun _ => le_max_right _ _

theorem positivePart_eq {d : Fin N → ℝ} (hd : 0 ≤ d) : positivePart d = d := by
  ext i
  exact max_eq_left (hd i)

theorem continuous_positivePart : Continuous (positivePart : (Fin N → ℝ) → _) := by
  exact continuous_pi fun i => (continuous_apply i).max continuous_const

theorem demand_nonneg_ae (ν : Fin N → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : DemandLaw ν) : ∀ᵐ d ∂Measure.pi ν, 0 ≤ d := by
  have hi (i : Fin N) : ∀ᵐ x ∂ν i, 0 ≤ x := by
    rw [ae_iff]
    simp only [not_le]
    change ν i (Set.Iio (0 : ℝ)) = 0
    exact (hν i).1
  have hj (i : Fin N) : ∀ᵐ d ∂Measure.pi ν, 0 ≤ d i :=
    (measurePreserving_eval ν i).quasiMeasurePreserving.ae (hi i)
  exact (ae_all_iff.mpr hj)

theorem demand_coord_integrable (ν : Fin N → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)] (hν : DemandLaw ν) (i : Fin N) :
    Integrable (fun d : Fin N → ℝ => d i) (Measure.pi ν) := by
  exact (measurePreserving_eval ν i).integrable_comp_of_integrable (hν i).2.1

theorem orthant_aestronglyMeasurable (ν : Fin N → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)] (hν : DemandLaw ν)
    {f : (Fin N → ℝ) → ℝ} (hf : ContinuousOn f {d | 0 ≤ d}) :
    AEStronglyMeasurable f (Measure.pi ν) := by
  have hc : Continuous (fun d => f (positivePart d)) :=
    hf.comp_continuous continuous_positivePart positivePart_nonneg
  apply hc.aestronglyMeasurable.congr
  filter_upwards [demand_nonneg_ae ν hν] with d hd
  rw [positivePart_eq hd]

end BassokInventoryResearch
end

/- Complete verified reused body: OrthantIntegration -/

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators
namespace BassokInventoryResearch
open BassokSubstitution
variable {N : ℕ}

theorem orthant_integrable_of_bound (ν : Fin N → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)] (hν : DemandLaw ν)
    {f : (Fin N → ℝ) → ℝ} (hf : ContinuousOn f {d | 0 ≤ d})
    (A : ℝ) (w : Fin N → ℝ) (hb : ∀ d, 0 ≤ d → |f d| ≤ A + ∑ i, w i * d i) :
    Integrable f (Measure.pi ν) := by
  have hi : Integrable (fun d : Fin N → ℝ => A + ∑ i, w i * d i) (Measure.pi ν) :=
    (integrable_const A).add (integrable_finsetSum _ fun i _ =>
      (demand_coord_integrable ν hν i).const_mul (w i))
  apply hi.mono' (orthant_aestronglyMeasurable ν hν hf)
  filter_upwards [demand_nonneg_ae ν hν] with d hd
  simpa only [Real.norm_eq_abs, Pi.sub_apply] using hb d hd

theorem expected_lipschitz_bound (ν : Fin N → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)] (hν : DemandLaw ν)
    {f g : (Fin N → ℝ) → ℝ} (hf : Integrable f (Measure.pi ν))
    (hg : Integrable g (Measure.pi ν)) (C : ℝ)
    (hb : ∀ d, 0 ≤ d → |f d - g d| ≤ C) :
    |(∫ d, f d ∂Measure.pi ν) - ∫ d, g d ∂Measure.pi ν| ≤ C := by
  rw [← integral_sub hf hg, ← Real.norm_eq_abs]
  apply (norm_integral_le_integral_norm _).trans
  have hh : ∫ d, ‖f d - g d‖ ∂Measure.pi ν ≤ ∫ _d : Fin N → ℝ, C ∂Measure.pi ν := by
    apply integral_mono_ae (hf.sub hg).norm (integrable_const C)
    filter_upwards [demand_nonneg_ae ν hν] with d hd
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using hb d hd
  simpa using hh

end BassokInventoryResearch
end

/- Complete verified reused body: NativeExpectation -/

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators
namespace BassokInventoryResearch
open BassokSubstitution
variable {N : ℕ}

def demandBound (M : Model N) (d : Fin N → ℝ) : ℝ :=
  ∑ i, (|M.penalty i| + gainConstant M) * d i

noncomputable def demandBudget (M : Model N) (ν : Fin N → Measure ℝ) : ℝ :=
  ∫ d, demandBound M d ∂Measure.pi ν

theorem demandBound_integrable (M : Model N) (ν : Fin N → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)] (hν : DemandLaw ν) :
    Integrable (demandBound M) (Measure.pi ν) := by
  exact integrable_finsetSum _ fun i _ =>
    (demand_coord_integrable ν hν i).const_mul _

theorem demandBudget_nonneg (M : Model N) (ν : Fin N → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)] (hν : DemandLaw ν) : 0 ≤ demandBudget M ν := by
  apply integral_nonneg_of_ae
  filter_upwards [demand_nonneg_ae ν hν] with d hd
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (add_nonneg (abs_nonneg _) (gainConstant_pos M).le) (hd i)

theorem G_integrable (M : Model N) (ν : Fin N → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)] (hν : DemandLaw ν)
    {y : Fin N → ℝ} (hy : 0 ≤ y) : Integrable (M.G y) (Measure.pi ν) := by
  exact orthant_integrable_of_bound ν hν (G_continuousOn_nonneg M hy)
    (∑ i, |M.s i| * y i) (fun i => |M.penalty i| + gainConstant M)
    (fun d hd => abs_G_le M hy hd)

theorem expected_G_continuousOn (M : Model N) (ν : Fin N → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)] (hν : DemandLaw ν) :
    ContinuousOn (fun y => ∫ d, M.G y d ∂Measure.pi ν) {y | 0 ≤ y} := by
  apply continuousOn_of_sum_lipschitz
    (show 0 ≤ gainConstant M + ∑ i, |M.s i| from
      add_nonneg (gainConstant_pos M).le (Finset.sum_nonneg fun _ _ => abs_nonneg _))
  intro y hy z hz
  exact expected_lipschitz_bound ν hν (G_integrable M ν hν hy) (G_integrable M ν hν hz)
    _ (fun d hd => G_stock_lipschitz M hy hz hd)

theorem profit_continuousOn (M : Model N) (ν : Fin N → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)] (hν : DemandLaw ν) :
    ContinuousOn (M.profit (Measure.pi ν) 0) {y | 0 ≤ y} := by
  have hc : Continuous (fun y : Fin N → ℝ => -(∑ i, M.c i * y i)) := by fun_prop
  change ContinuousOn (fun y => M.profit (Measure.pi ν) 0 y) _
  simp only [Model.profit, Pi.zero_apply, sub_zero]
  exact hc.continuousOn.add (expected_G_continuousOn M ν hν)

theorem profit_coercive_bound (M : Model N) (ν : Fin N → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)] (hν : DemandLaw ν)
    {y : Fin N → ℝ} (hy : 0 ≤ y) :
    M.profit (Measure.pi ν) 0 y ≤ demandBudget M ν - ∑ i, (M.c i - M.s i) * y i := by
  have hh : (∫ d, M.G y d ∂Measure.pi ν) ≤
      ∫ d, (∑ i, M.s i * y i) + demandBound M d ∂Measure.pi ν := by
    apply integral_mono_ae (G_integrable M ν hν hy)
      ((integrable_const _).add (demandBound_integrable M ν hν))
    filter_upwards [demand_nonneg_ae ν hν] with d hd
    exact G_upper_bound M hy hd
  rw [integral_add (integrable_const _) (demandBound_integrable M ν hν)] at hh
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul] at hh
  simp only [Model.profit, Pi.zero_apply, sub_zero, sub_mul, Finset.sum_sub_distrib]
  change -(∑ i, M.c i * y i) + (∫ d, M.G y d ∂Measure.pi ν) ≤
    (∫ d, demandBound M d ∂Measure.pi ν) - ((∑ i, M.c i * y i) - ∑ i, M.s i * y i)
  linarith

end BassokInventoryResearch
end

/- Complete verified reused body: CoerciveMaximum -/

noncomputable section
open Set
open scoped BigOperators
namespace BassokInventoryResearch
variable {N : ℕ}

theorem coercive_orthant_maximum (F : (Fin N → ℝ) → ℝ)
    (hc : ContinuousOn F {y | 0 ≤ y}) (a : Fin N → ℝ)
    (ha : ∀ i, 0 < a i) (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ y, 0 ≤ y → F y ≤ K - ∑ i, a i * y i) :
    ∃ z : Fin N → ℝ, 0 ≤ z ∧ ∀ y, 0 ≤ y → F y ≤ F z := by
  let B : Fin N → ℝ := fun i => (K + |F 0| + 1) / a i
  have hB : 0 ≤ B := by
    intro i
    dsimp [B]
    exact div_nonneg (by positivity) (ha i).le
  have hbox : Set.Icc (0 : Fin N → ℝ) B ⊆ {y | 0 ≤ y} := fun _ h => h.1
  obtain ⟨z, hz, hmax⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : Fin N → ℝ) B)).exists_isMaxOn
    ⟨0, le_rfl, hB⟩ (hc.mono hbox)
  refine ⟨z, hz.1, fun y hy => ?_⟩
  by_cases h : y ≤ B
  · exact hmax ⟨hy, h⟩
  · have hex : ∃ i, B i < y i := by
      simpa only [Pi.le_def, not_forall, not_le] using h
    obtain ⟨i, hi⟩ := hex
    have hi' : K + |F 0| + 1 < a i * y i := by
      exact (div_lt_iff₀ (ha i)).mp hi |>.trans_eq (mul_comm _ _)
    have hsum : a i * y i ≤ ∑ j, a j * y j :=
      Finset.single_le_sum (fun j _ => mul_nonneg (ha j).le (hy j)) (Finset.mem_univ i)
    have hf0 : F 0 ≤ F z := hmax ⟨le_rfl, hB⟩
    have hfy := hb y hy
    have habs := neg_abs_le (F 0)
    linarith

theorem strict_midpoint_unique {F : (Fin N → ℝ) → ℝ}
    (hs : ∀ y z, 0 ≤ y → 0 ≤ z → y ≠ z →
      (F y + F z) / 2 < F (fun i => (y i + z i) / 2))
    {z y : Fin N → ℝ} (hz : 0 ≤ z) (hy : 0 ≤ y)
    (hmax : ∀ x, 0 ≤ x → F x ≤ F z) (heq : F y = F z) : y = z := by
  by_contra hne
  have hh := hs y z hy hz hne
  have hn : 0 ≤ (fun i => (y i + z i) / 2) := fun i => div_nonneg (add_nonneg (hy i) (hz i)) (by norm_num)
  have hm := hmax _ hn
  rw [heq] at hh
  linarith

end BassokInventoryResearch
end

/- Complete verified reused body: ProfitAlgebra -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace BassokInventoryResearch
open BassokSubstitution
variable {N : ℕ}

theorem profit_shift (M : Model N) (μ : Measure (Fin N → ℝ)) (x y : Fin N → ℝ) :
    M.profit μ x y = M.profit μ 0 y + ∑ i, M.c i * x i := by
  simp only [Model.profit, Pi.zero_apply, sub_zero, mul_sub, Finset.sum_sub_distrib]
  ring

theorem purchase_midpoint (M : Model N) (y z : Fin N → ℝ) :
    (∑ i, M.c i * ((y i + z i) / 2)) =
      ((∑ i, M.c i * y i) + ∑ i, M.c i * z i) / 2 := by
  calc
    _ = ∑ i, (M.c i * y i + M.c i * z i) / 2 := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [← Finset.sum_div, Finset.sum_add_distrib]

theorem profit_strict_midpoint (M : Model N) (μ : Measure (Fin N → ℝ))
    {y z : Fin N → ℝ}
    (h : ((∫ d, M.G y d ∂μ) + ∫ d, M.G z d ∂μ) / 2 <
      ∫ d, M.G (fun i => (y i + z i) / 2) d ∂μ) :
    (M.profit μ 0 y + M.profit μ 0 z) / 2 <
      M.profit μ 0 (fun i => (y i + z i) / 2) := by
  simp only [Model.profit, Pi.zero_apply, sub_zero]
  rw [purchase_midpoint]
  linarith

theorem base_stock_of_unique_maximum (M : Model N) (μ : Measure (Fin N → ℝ))
    {z : Fin N → ℝ}
    (hm : ∀ y, 0 ≤ y → M.profit μ 0 y ≤ M.profit μ 0 z)
    (hu : ∀ y, 0 ≤ y → M.profit μ 0 y = M.profit μ 0 z → y = z) :
    ∀ x : Fin N → ℝ, 0 ≤ x → x ≤ z →
      IsMaxOn (M.profit μ x) {y | x ≤ y} z ∧
        ∀ y, x ≤ y → IsMaxOn (M.profit μ x) {y | x ≤ y} y → y = z := by
  intro x hx hxz
  have hmax : IsMaxOn (M.profit μ x) {y | x ≤ y} z := by
    intro y hy
    change M.profit μ x y ≤ M.profit μ x z
    rw [profit_shift M μ x y, profit_shift M μ x z]
    linarith [hm y (hx.trans hy)]
  refine ⟨hmax, fun y hy hymax => hu y (hx.trans hy) ?_⟩
  have h1 := hmax hy
  have h2 := hymax hxz
  change M.profit μ x y ≤ M.profit μ x z at h1
  change M.profit μ x z ≤ M.profit μ x y at h2
  rw [profit_shift M μ x y, profit_shift M μ x z] at h1 h2
  linarith

end BassokInventoryResearch
end

/- Complete verified reused body: TransportConcavity -/

open scoped BigOperators
open BassokSubstitution

namespace BassokInventoryResearch

variable {N : ℕ}

theorem transport_midpoint {y z d e : Fin N → ℝ} {w v : Fin N → Fin N → ℝ}
    (hw : w ∈ transportSet y d) (hv : v ∈ transportSet z e) :
    (fun j i => (w j i + v j i) / 2) ∈
      transportSet (fun j => (y j + z j) / 2) (fun i => (d i + e i) / 2) := by
  refine ⟨fun j i => div_nonneg (add_nonneg (hw.1 j i) (hv.1 j i)) (by norm_num), ?_, ?_, ?_⟩
  · intro j i hij; dsimp; rw [hw.2.1 j i hij, hv.2.1 j i hij]; norm_num
  · intro j
    dsimp [rowSum]
    simp only [← Finset.sum_div, Finset.sum_add_distrib]
    have := hw.2.2.1 j; have := hv.2.2.1 j
    dsimp [rowSum] at *; linarith
  · intro i
    dsimp [colSum]
    simp only [← Finset.sum_div, Finset.sum_add_distrib]
    have := hw.2.2.2 i; have := hv.2.2.2 i
    dsimp [colSum] at *; linarith

theorem gainValue_midpoint (M : Model N) (w v : Fin N → Fin N → ℝ) :
    gainValue M (fun j i => (w j i + v j i) / 2) = (gainValue M w + gainValue M v) / 2 := by
  dsimp [gainValue]
  simp only [← mul_div_assoc, mul_add, ← Finset.sum_div, Finset.sum_add_distrib]

theorem G_midpoint_le (M : Model N) {y z d : Fin N → ℝ}
    (hy : 0 ≤ y) (hz : 0 ≤ z) (hd : 0 ≤ d) :
    (M.G y d + M.G z d) / 2 ≤ M.G (fun j => (y j + z j) / 2) d := by
  have hq : 0 ≤ fun j => (y j + z j) / 2 := fun j => div_nonneg (add_nonneg (hy j) (hz j)) (by norm_num)
  obtain ⟨w,hw,heq,_⟩ := transport_attained M hy hd
  obtain ⟨v,hv,hveq,_⟩ := transport_attained M hz hd
  have hm := transport_midpoint hw hv
  have hdd : (fun i => (d i + d i) / 2) = d := by funext i; ring
  rw [hdd] at hm
  have hgain := gainValue_le_transportValue M hq hd hm
  rw [gainValue_midpoint, heq, hveq] at hgain
  rw [G_eq_baseline_add M hy hd, G_eq_baseline_add M hz hd, G_eq_baseline_add M hq hd]
  have hb : baseline M (fun j => (y j + z j) / 2) d =
      (baseline M y d + baseline M z d) / 2 := by
    dsimp [baseline]
    simp only [← mul_div_assoc, mul_add, ← Finset.sum_div, Finset.sum_add_distrib]
    ring
  rw [hb]
  linarith

end BassokInventoryResearch

end CompleteVerifiedFoundation

section CompleteConcreteModel

open scoped BigOperators
open BassokSubstitution BassokInventoryResearch

namespace BassokDisproofResearch

noncomputable section

def model : Model 3 where
  c := ![79 / 48, 47 / 48, 29 / 48]
  p := ![3, 2, 1]
  penalty := 0
  s := 0
  b := 0

def baseStock : Fin 3 → ℝ := ![1, 1, 1]
def forcedStock : Fin 3 → ℝ := ![3 / 2, 1 / 2, 3 / 2]
def initialStock : Fin 3 → ℝ := ![3 / 2, 0, 5 / 4]
def scenario : Fin 6 → Fin 3 → ℝ :=
  ![![0, 0, 2], ![0, 2, 2], ![1, 0, 2], ![1, 2, 2], ![4, 0, 2], ![4, 2, 2]]
def scenarioWeight : Fin 6 → ℝ := ![1 / 4, 1 / 4, 1 / 8, 1 / 8, 1 / 8, 1 / 8]

noncomputable def baselineRevenue (y : Fin 3 → ℝ) : ℝ :=
  model.G y (scenario 0) / 4 + model.G y (scenario 1) / 4 +
  model.G y (scenario 2) / 8 + model.G y (scenario 3) / 8 +
  model.G y (scenario 4) / 8 + model.G y (scenario 5) / 8
noncomputable def baselineProfit (y : Fin 3 → ℝ) : ℝ :=
  baselineRevenue y - ∑ i, model.c i * y i

theorem model_assumptions : model.Assumption1 ∧ model.Assumption2 ∧
    model.Assumption3 ∧ 0 ≤ model.b ∧
    (∀ i, model.s i < model.c i ∧ model.c i < model.p i + model.penalty i) := by
  refine ⟨?_, ?_, ?_, by norm_num [model], ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [model] at *
  · intro i j _
    norm_num [model]
  · intro i j _
    fin_cases i <;> fin_cases j <;> norm_num [model, Model.netRevenue]
  · intro i
    fin_cases i <;> norm_num [model]

theorem stocks_nonneg : 0 ≤ baseStock ∧ 0 ≤ initialStock ∧ initialStock ≤ forcedStock := by
  constructor
  · intro i; fin_cases i <;> norm_num [baseStock]
  constructor
  · intro i; fin_cases i <;> norm_num [initialStock]
  · intro i; fin_cases i <;> norm_num [initialStock, forcedStock]

theorem scenario_nonneg (s : Fin 6) : 0 ≤ scenario s := by
  intro i; fin_cases s <;> fin_cases i <;> norm_num [scenario]

theorem baselineRevenue_eq_sum (y : Fin 3 → ℝ) :
    baselineRevenue y = ∑ s, scenarioWeight s * model.G y (scenario s) := by
  simp [baselineRevenue, scenarioWeight, Fin.sum_univ_succ]
  ring

theorem model_baseline (y d : Fin 3 → ℝ) : baseline model y d = 0 := by
  simp [baseline, model]

theorem G_le_of_transport {y d : Fin 3 → ℝ} {v : ℝ}
    (hy : 0 ≤ y) (hd : 0 ≤ d)
    (h : ∀ w ∈ transportSet y d, gainValue model w ≤ v) : model.G y d ≤ v := by
  rw [G_eq_baseline_add model hy hd, model_baseline, zero_add]
  exact transportValue_le model hy hd h

end

end BassokDisproofResearch

end CompleteConcreteModel

section CompletePrefixBounds

open scoped BigOperators
open BassokSubstitution BassokInventoryResearch

namespace BassokDisproofResearch

noncomputable section

def prefix0 (y d : Fin 3 → ℝ) : ℝ := min (d 0) (y 0)
def prefix1 (y d : Fin 3 → ℝ) : ℝ :=
  min (d 0 + d 1) (min (y 0 + d 1) (y 0 + y 1))
def prefix2 (y d : Fin 3 → ℝ) : ℝ :=
  min (d 0 + d 1 + d 2) (min (y 0 + d 1 + d 2)
    (min (y 0 + y 1 + d 2) (y 0 + y 1 + y 2)))

theorem G_le_prefix {y d : Fin 3 → ℝ} (hy : 0 ≤ y) (hd : 0 ≤ d) :
    model.G y d ≤ prefix0 y d + prefix1 y d + prefix2 y d := by
  apply G_le_of_transport hy hd
  intro w hw
  have h10 := hw.2.1 1 0 (by decide)
  have h20 := hw.2.1 2 0 (by decide)
  have h21 := hw.2.1 2 1 (by decide)
  have hr0 := hw.2.2.1 0
  have hr1 := hw.2.2.1 1
  have hr2 := hw.2.2.1 2
  have hc0 := hw.2.2.2 0
  have hc1 := hw.2.2.2 1
  have hc2 := hw.2.2.2 2
  simp [rowSum, colSum, Fin.sum_univ_succ, h10, h20, h21] at hr0 hr1 hr2 hc0 hc1 hc2
  have h00 := hw.1 0 0
  have h01 := hw.1 0 1
  have h02 := hw.1 0 2
  have h11 := hw.1 1 1
  have h12 := hw.1 1 2
  have h22 := hw.1 2 2
  have h0 : w 0 0 ≤ prefix0 y d := by
    unfold prefix0
    exact le_min hc0 (by linarith)
  have h1 : w 0 0 + w 0 1 + w 1 1 ≤ prefix1 y d := by
    unfold prefix1
    exact le_min (by linarith) (le_min (by linarith) (by linarith))
  have h2 : w 0 0 + w 0 1 + w 0 2 + w 1 1 + w 1 2 + w 2 2 ≤ prefix2 y d := by
    unfold prefix2
    exact le_min (by linarith) (le_min (by linarith) (le_min (by linarith) (by linarith)))
  have he : gainValue model w = w 0 0 + (w 0 0 + w 0 1 + w 1 1) +
      (w 0 0 + w 0 1 + w 0 2 + w 1 1 + w 1 2 + w 2 2) := by
    simp [gainValue, gain, model, Model.netRevenue, Fin.sum_univ_succ, h10, h20, h21]
    ring
  rw [he]
  linarith

theorem G_scenario_bounds {y : Fin 3 → ℝ} (hy : 0 ≤ y) :
    model.G y (scenario 0) ≤ 2 ∧
    model.G y (scenario 1) ≤ y 0 + y 1 + y 2 + min 2 (y 0 + y 1) ∧
    model.G y (scenario 2) ≤ 2 * min 1 (y 0) +
      min 3 (min (y 0 + 2) (y 0 + y 1 + y 2)) ∧
    model.G y (scenario 3) ≤ 2 * y 0 + 2 * y 1 + y 2 + min 1 (y 0) ∧
    model.G y (scenario 4) ≤ 3 * y 0 + min 2 (y 1 + y 2) ∧
    model.G y (scenario 5) ≤ 3 * y 0 + 2 * y 1 + y 2 := by
  have h (s : Fin 6) := G_le_prefix hy (scenario_nonneg s)
  have h0 := hy 0
  have h1 := hy 1
  have h2 := hy 2
  have p00 : prefix0 y (scenario 0) ≤ 0 := min_le_left _ _
  have p10 : prefix1 y (scenario 0) ≤ 0 := by
    simp [prefix1, scenario]
  have p20 : prefix2 y (scenario 0) ≤ 2 := by
    simp [prefix2, scenario]
  refine ⟨by linarith [h 0], ?_, ?_, ?_, ?_, ?_⟩
  · have p0 : prefix0 y (scenario 1) ≤ 0 := min_le_left _ _
    have p1 : prefix1 y (scenario 1) ≤ min 2 (y 0 + y 1) := by
      unfold prefix1
      simp only [scenario, Matrix.cons_val_zero, Matrix.cons_val_one,
        zero_add]
      exact le_min (min_le_left _ _) ((min_le_right _ _).trans (min_le_right _ _))
    have p2 : prefix2 y (scenario 1) ≤ y 0 + y 1 + y 2 := by
      exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    linarith [h 1]
  · have p0 : prefix0 y (scenario 2) ≤ min 1 (y 0) := le_rfl
    have p1 : prefix1 y (scenario 2) ≤ min 1 (y 0) := by
      change min (1 + 0) (min (y 0 + 0) (y 0 + y 1)) ≤ _
      simp only [add_zero]
      exact le_min (min_le_left _ _) ((min_le_right _ _).trans (min_le_left _ _))
    have p2 : prefix2 y (scenario 2) ≤
        min 3 (min (y 0 + 2) (y 0 + y 1 + y 2)) := by
      change min (1 + 0 + 2) (min (y 0 + 0 + 2)
        (min (y 0 + y 1 + 2) (y 0 + y 1 + y 2))) ≤ _
      norm_num only [add_zero, show (1 : ℝ) + 2 = 3 by norm_num]
      exact le_min (min_le_left _ _) (le_min
        ((min_le_right _ _).trans (min_le_left _ _))
        ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
    linarith [h 2]
  · have p0 : prefix0 y (scenario 3) ≤ min 1 (y 0) := le_rfl
    have p1 : prefix1 y (scenario 3) ≤ y 0 + y 1 :=
      (min_le_right _ _).trans (min_le_right _ _)
    have p2 : prefix2 y (scenario 3) ≤ y 0 + y 1 + y 2 :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    linarith [h 3]
  · have p0 : prefix0 y (scenario 4) ≤ y 0 := min_le_right _ _
    have p1 : prefix1 y (scenario 4) ≤ y 0 := by
      simp [prefix1, scenario]
    have p2 : prefix2 y (scenario 4) ≤ y 0 + min 2 (y 1 + y 2) := by
      change min (4 + 0 + 2) (min (y 0 + 0 + 2)
        (min (y 0 + y 1 + 2) (y 0 + y 1 + y 2))) ≤ _
      simp only [add_zero]
      rw [add_min]
      apply le_min
      · exact (min_le_right _ _).trans (min_le_left _ _)
      · have hh := (min_le_right (4 + 2 : ℝ) (min (y 0 + 2)
            (min (y 0 + y 1 + 2) (y 0 + y 1 + y 2)))).trans
            ((min_le_right _ _).trans (min_le_right _ _))
        linarith
    linarith [h 4]
  · have p0 : prefix0 y (scenario 5) ≤ y 0 := min_le_right _ _
    have p1 : prefix1 y (scenario 5) ≤ y 0 + y 1 :=
      (min_le_right _ _).trans (min_le_right _ _)
    have p2 : prefix2 y (scenario 5) ≤ y 0 + y 1 + y 2 :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    linarith [h 5]

end

end BassokDisproofResearch

end CompletePrefixBounds

section CompleteAtomicValues

open scoped BigOperators
open BassokSubstitution BassokInventoryResearch

namespace BassokDisproofResearch

noncomputable section

def witnessBase : Fin 6 → Fin 3 → Fin 3 → ℝ :=
  ![![![0,0,0], ![0,0,1], ![0,0,1]],
    ![![0,1,0], ![0,1,0], ![0,0,1]],
    ![![1,0,0], ![0,0,1], ![0,0,1]],
    ![![1,0,0], ![0,1,0], ![0,0,1]],
    ![![1,0,0], ![0,0,1], ![0,0,1]],
    ![![1,0,0], ![0,1,0], ![0,0,1]]]

def witnessForced : Fin 6 → Fin 3 → Fin 3 → ℝ :=
  ![![![0,0,0], ![0,0,1/2], ![0,0,3/2]],
    ![![0,3/2,0], ![0,1/2,0], ![0,0,3/2]],
    ![![1,0,0], ![0,0,1/2], ![0,0,3/2]],
    ![![1,1/2,0], ![0,1/2,0], ![0,0,3/2]],
    ![![3/2,0,0], ![0,0,1/2], ![0,0,3/2]],
    ![![3/2,0,0], ![0,1/2,0], ![0,0,3/2]]]

def baseValue : Fin 6 → ℝ := ![2,5,5,6,5,6]
def forcedValue : Fin 6 → ℝ := ![2,11/2,5,13/2,13/2,7]

theorem witnessBase_mem (s : Fin 6) :
    witnessBase s ∈ transportSet baseStock (scenario s) := by
  fin_cases s <;> norm_num [transportSet, witnessBase, baseStock, scenario,
    rowSum, colSum, Fin.sum_univ_succ, Fin.forall_fin_succ, Matrix.cons_val_two] <;> decide

theorem witnessForced_mem (s : Fin 6) :
    witnessForced s ∈ transportSet forcedStock (scenario s) := by
  fin_cases s <;> norm_num [transportSet, witnessForced, forcedStock, scenario,
    rowSum, colSum, Fin.sum_univ_succ, Fin.forall_fin_succ, Matrix.cons_val_two] <;> decide

theorem witnessBase_gain (s : Fin 6) : gainValue model (witnessBase s) = baseValue s := by
  fin_cases s <;> norm_num [gainValue, gain, model, Model.netRevenue,
    witnessBase, baseValue, Fin.sum_univ_succ]

theorem witnessForced_gain (s : Fin 6) : gainValue model (witnessForced s) = forcedValue s := by
  fin_cases s <;> norm_num [gainValue, gain, model, Model.netRevenue,
    witnessForced, forcedValue, Fin.sum_univ_succ]

theorem G_base_value (s : Fin 6) : model.G baseStock (scenario s) = baseValue s := by
  have hl : baseValue s ≤ model.G baseStock (scenario s) := by
    rw [G_eq_baseline_add model stocks_nonneg.1 (scenario_nonneg s), model_baseline, zero_add]
    rw [← witnessBase_gain]
    exact gainValue_le_transportValue model stocks_nonneg.1 (scenario_nonneg s) (witnessBase_mem s)
  apply le_antisymm _ hl
  obtain ⟨h0,h1,h2,h3,h4,h5⟩ := G_scenario_bounds stocks_nonneg.1
  fin_cases s <;> norm_num [baseStock, baseValue, Matrix.cons_val_two] at * <;> assumption

theorem G_forced_value (s : Fin 6) : model.G forcedStock (scenario s) = forcedValue s := by
  have hq : 0 ≤ forcedStock := stocks_nonneg.2.1.trans stocks_nonneg.2.2
  have hl : forcedValue s ≤ model.G forcedStock (scenario s) := by
    rw [G_eq_baseline_add model hq (scenario_nonneg s), model_baseline, zero_add]
    rw [← witnessForced_gain]
    exact gainValue_le_transportValue model hq (scenario_nonneg s) (witnessForced_mem s)
  apply le_antisymm _ hl
  obtain ⟨h0,h1,h2,h3,h4,h5⟩ := G_scenario_bounds hq
  fin_cases s <;> norm_num [forcedStock, forcedValue, Matrix.cons_val_two] at * <;> assumption

theorem baseline_values : baselineRevenue baseStock = 9 / 2 ∧
    baselineRevenue forcedStock = 5 ∧ baselineProfit baseStock = 61 / 48 ∧
    baselineProfit forcedStock = 109 / 96 := by
  have hb : baselineRevenue baseStock = 9 / 2 := by
    unfold baselineRevenue
    simp only [G_base_value]
    change (2:ℝ)/4+5/4+5/8+6/8+5/8+6/8 = 9/2
    norm_num
  have hq : baselineRevenue forcedStock = 5 := by
    unfold baselineRevenue
    simp only [G_forced_value]
    change (2:ℝ)/4+(11/2)/4+5/8+(13/2)/8+(13/2)/8+7/8 = 5
    norm_num
  refine ⟨hb, hq, ?_, ?_⟩
  · simp only [baselineProfit, hb]
    norm_num [model, baseStock, Fin.sum_univ_succ]
  · simp only [baselineProfit, hq]
    norm_num [model, forcedStock, Fin.sum_univ_succ]


end

end BassokDisproofResearch

end CompleteAtomicValues

section CompleteSharpCertificates

open scoped BigOperators
open BassokSubstitution BassokInventoryResearch

namespace BassokDisproofResearch

theorem min_half_abs (a b : ℝ) : min a b = (a + b - |a - b|) / 2 := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

theorem min_three_average (a b c : ℝ) : min a (min b c) ≤ (a + b + c) / 3 := by
  have h0 := min_le_left a (min b c)
  have h1 := (min_le_right a (min b c)).trans (min_le_left b c)
  have h2 := (min_le_right a (min b c)).trans (min_le_right b c)
  linarith

theorem min_two_support (t : ℝ) :
    min 2 t ≤ 5 / 6 * t + 1 / 3 - 1 / 6 * |t - 2| := by
  rcases le_total t 2 with h | h
  · rw [min_eq_right h, abs_of_nonpos (sub_nonpos.mpr h)]
    linarith
  · rw [min_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)]
    linarith

theorem chain_abs_bound (a b c : ℝ) :
    |a| + |b| + |c| ≤ 3 * |a| + 2 * |a + b| + |b + c| := by
  have hb : |b| ≤ |a + b| + |a| := by
    calc
      |b| = |a + b - a| := by congr 1; ring
      _ ≤ |a + b| + |a| := abs_sub _ _
  have hc : |c| ≤ |b + c| + |b| := by
    calc
      |c| = |b + c - b| := by congr 1; ring
      _ ≤ |b + c| + |b| := abs_sub _ _
  linarith

theorem purchase_expand (y : Fin 3 → ℝ) :
    (∑ i, model.c i * y i) = 79 / 48 * y 0 + 47 / 48 * y 1 + 29 / 48 * y 2 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change 79 / 48 * y 0 + (47 / 48 * y 1 + 29 / 48 * y 2) = _
  ring

theorem baseline_sharp_components {y : Fin 3 → ℝ} (hy : 0 ≤ y) :
    3 / 16 * |y 0 - 1| + 1 / 8 * |y 0 + y 1 - 2| +
      1 / 16 * |y 1 + y 2 - 2| ≤ baselineProfit baseStock - baselineProfit y := by
  obtain ⟨h0,h1,h2,h3,h4,h5⟩ := G_scenario_bounds hy
  have m1 := min_half_abs 2 (y 0 + y 1)
  have m2 := min_half_abs 1 (y 0)
  have m4 := min_half_abs 2 (y 1 + y 2)
  rw [abs_sub_comm 2 (y 0 + y 1)] at m1
  rw [abs_sub_comm 1 (y 0)] at m2
  rw [abs_sub_comm 2 (y 1 + y 2)] at m4
  have mt := min_three_average 3 (y 0 + 2) (y 0 + y 1 + y 2)
  rw [baseline_values.2.2.1]
  unfold baselineProfit
  rw [purchase_expand]
  unfold baselineRevenue
  linarith

theorem forced_sharp_components {y : Fin 3 → ℝ} (hy : initialStock ≤ y) :
    13 / 48 * (y 0 - 3 / 2) + 1 / 8 * |y 0 + y 1 - 2| +
      1 / 48 * |y 1 + y 2 - 2| ≤ baselineProfit forcedStock - baselineProfit y := by
  have hy0 : 0 ≤ y := stocks_nonneg.2.1.trans hy
  obtain ⟨h0,h1,h2,h3,h4,h5⟩ := G_scenario_bounds hy0
  have m1 := min_half_abs 2 (y 0 + y 1)
  rw [abs_sub_comm 2 (y 0 + y 1)] at m1
  have m2 := min_le_left (1 : ℝ) (y 0)
  have mt := min_le_left (3 : ℝ) (min (y 0 + 2) (y 0 + y 1 + y 2))
  have m4 := min_two_support (y 1 + y 2)
  rw [baseline_values.2.2.2]
  unfold baselineProfit
  rw [purchase_expand]
  unfold baselineRevenue
  linarith

theorem baseline_sharp {y : Fin 3 → ℝ} (hy : 0 ≤ y) :
    (1 / 16 : ℝ) * (∑ i, |y i - baseStock i|) ≤
      baselineProfit baseStock - baselineProfit y := by
  have h := chain_abs_bound (y 0 - 1) (y 1 - 1) (y 2 - 1)
  have he01 : y 0 - 1 + (y 1 - 1) = y 0 + y 1 - 2 := by ring
  have he12 : y 1 - 1 + (y 2 - 1) = y 1 + y 2 - 2 := by ring
  rw [he01, he12] at h
  have hb := baseline_sharp_components hy
  have hs : (∑ i, |y i - baseStock i|) = |y 0 - 1| + |y 1 - 1| + |y 2 - 1| := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change |y 0 - 1| + (|y 1 - 1| + |y 2 - 1|) = _
    ring
  rw [hs]
  linarith

theorem forced_sharp {y : Fin 3 → ℝ} (hy : initialStock ≤ y) :
    (1 / 48 : ℝ) * (∑ i, |y i - forcedStock i|) ≤
      baselineProfit forcedStock - baselineProfit y := by
  have h := chain_abs_bound (y 0 - 3 / 2) (y 1 - 1 / 2) (y 2 - 3 / 2)
  have he01 : y 0 - 3 / 2 + (y 1 - 1 / 2) = y 0 + y 1 - 2 := by ring
  have he12 : y 1 - 1 / 2 + (y 2 - 3 / 2) = y 1 + y 2 - 2 := by ring
  rw [he01, he12] at h
  have ha : 0 ≤ y 0 - 3 / 2 := by have := hy 0; norm_num [initialStock] at this; linarith
  rw [abs_of_nonneg ha] at h
  have hb := forced_sharp_components hy
  have h01 := abs_nonneg (y 0 + y 1 - 2)
  have hs : (∑ i, |y i - forcedStock i|) =
      |y 0 - 3/2| + |y 1 - 1/2| + |y 2 - 3/2| := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change |y 0 - 3/2| + (|y 1 - 1/2| + |y 2 - 3/2|) = _
    ring
  rw [hs]
  rw [abs_of_nonneg ha]
  linarith

end BassokDisproofResearch

end CompleteSharpCertificates

section CompleteAtomicMeasure

open scoped BigOperators ENNReal
open MeasureTheory Set Filter BassokSubstitution BassokInventoryResearch

namespace BassokDisproofResearch

noncomputable section

def atomicLaw : Fin 3 → Measure ℝ :=
  ![(1/2 : ℝ≥0∞) • Measure.dirac 0 + (1/4 : ℝ≥0∞) • Measure.dirac 1 +
      (1/4 : ℝ≥0∞) • Measure.dirac 4,
    (1/2 : ℝ≥0∞) • Measure.dirac 0 + (1/2 : ℝ≥0∞) • Measure.dirac 2,
    Measure.dirac 2]

instance atomic_probability (i : Fin 3) : IsProbabilityMeasure (atomicLaw i) := by
  constructor
  fin_cases i <;> norm_num [atomicLaw, Measure.add_apply, Measure.smul_apply]
  all_goals
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_add]

theorem atomic_nonneg (i : Fin 3) : ∀ᵐ z ∂atomicLaw i, 0 ≤ z := by
  rw [ae_iff]
  simp only [not_le]
  change atomicLaw i (Iio 0) = 0
  fin_cases i <;> norm_num [atomicLaw, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply]

theorem real_integrable_weighted_dirac {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (f : α → ℝ) (a : α) {c : ℝ≥0∞} (hc : c ≠ ∞) :
    Integrable f (c • Measure.dirac a) :=
  (integrable_dirac (by simp)).smul_measure hc

theorem atomic_integrable (f : ℝ → ℝ) (i : Fin 3) : Integrable f (atomicLaw i) := by
  fin_cases i
  · exact ((real_integrable_weighted_dirac f 0 (by norm_num)).add_measure
      (real_integrable_weighted_dirac f 1 (by norm_num))).add_measure
      (real_integrable_weighted_dirac f 4 (by norm_num))
  · exact (real_integrable_weighted_dirac f 0 (by norm_num)).add_measure
      (real_integrable_weighted_dirac f 2 (by norm_num))
  · exact integrable_dirac (by simp)

def atomicJoint : Measure (Fin 3 → ℝ) :=
  ∑ s : Fin 6, ENNReal.ofReal (scenarioWeight s) • Measure.dirac (scenario s)

set_option maxHeartbeats 1000000 in
theorem atomic_pi : Measure.pi atomicLaw = atomicJoint := by
  apply Measure.pi_eq
  intro t _
  classical
  unfold atomicJoint
  rw [Measure.finsetSum_apply]
  simp only [Measure.smul_apply,
    Measure.dirac_apply, Fin.sum_univ_succ, Fin.prod_univ_succ,
    Fin.sum_univ_zero, Fin.prod_univ_zero, add_zero, mul_one]
  by_cases h00 : (0 : ℝ) ∈ t 0 <;>
    by_cases h01 : (1 : ℝ) ∈ t 0 <;>
    by_cases h04 : (4 : ℝ) ∈ t 0 <;>
    by_cases h10 : (0 : ℝ) ∈ t (0 : Fin 2).succ <;>
    by_cases h12 : (2 : ℝ) ∈ t (0 : Fin 2).succ <;>
    by_cases h22 : (2 : ℝ) ∈ t (0 : Fin 1).succ.succ <;>
    norm_num [atomicLaw, scenarioWeight, scenario, Measure.add_apply,
      Measure.smul_apply, Measure.dirac_apply, Set.indicator, Set.mem_pi,
      Fin.forall_fin_succ, Matrix.cons_val_two, h00, h01, h04, h10, h12, h22]
  all_goals
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_add, ENNReal.toReal_mul]

theorem atomic_joint_integrable (f : (Fin 3 → ℝ) → ℝ) : Integrable f atomicJoint := by
  apply integrable_finsetSum_measure.mpr
  intro s _
  exact real_integrable_weighted_dirac f (scenario s) ENNReal.ofReal_ne_top

theorem atomic_joint_integral (f : (Fin 3 → ℝ) → ℝ) :
    (∫ d, f d ∂atomicJoint) = ∑ s : Fin 6, scenarioWeight s * f (scenario s) := by
  unfold atomicJoint
  rw [integral_finsetSum_measure (fun s _ =>
    real_integrable_weighted_dirac f (scenario s) ENNReal.ofReal_ne_top)]
  apply Finset.sum_congr rfl
  intro s _
  rw [integral_smul_measure, integral_dirac, smul_eq_mul]
  rw [ENNReal.toReal_ofReal]
  fin_cases s <;> norm_num [scenarioWeight]

theorem atomic_G_integral (y : Fin 3 → ℝ) :
    (∫ d, model.G y d ∂Measure.pi atomicLaw) = baselineRevenue y := by
  rw [atomic_pi, atomic_joint_integral, baselineRevenue_eq_sum]

theorem atomic_G_integrable (y : Fin 3 → ℝ) :
    Integrable (model.G y) (Measure.pi atomicLaw) := by
  rw [atomic_pi]
  exact atomic_joint_integrable _

end

end BassokDisproofResearch

end CompleteAtomicMeasure

section CompleteGeneralDemand

noncomputable section
namespace BassokDisproofResearch
open MeasureTheory Set Filter BassokSubstitution BassokInventoryResearch
variable {N : ℕ}

theorem general_demand_nonneg (μ : Fin N → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hn : ∀ i, ∀ᵐ x ∂μ i, 0 ≤ x) : ∀ᵐ d ∂Measure.pi μ, 0 ≤ d := by
  exact ae_all_iff.mpr fun i => (measurePreserving_eval μ i).quasiMeasurePreserving.ae (hn i)

theorem general_G_integrable (M : Model N) (μ : Fin N → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)]
    (hn : ∀ i, ∀ᵐ x ∂μ i, 0 ≤ x) (hi : ∀ i, Integrable id (μ i))
    {y : Fin N → ℝ} (hy : 0 ≤ y) : Integrable (M.G y) (Measure.pi μ) := by
  have ha : AEStronglyMeasurable (M.G y) (Measure.pi μ) := by
    have hc : Continuous (fun d => M.G y (positivePart d)) :=
      (G_continuousOn_nonneg M hy).comp_continuous continuous_positivePart positivePart_nonneg
    apply hc.aestronglyMeasurable.congr
    filter_upwards [general_demand_nonneg μ hn] with d hd
    rw [positivePart_eq hd]
  have hb : Integrable (fun d : Fin N → ℝ => (∑ j, |M.s j| *y j) +
      ∑ i, (|M.penalty i|+gainConstant M)*d i) (Measure.pi μ) :=
    (integrable_const _).add (integrable_finsetSum _ fun i _ =>
      ((measurePreserving_eval μ i).integrable_comp_of_integrable (hi i)).const_mul _)
  apply hb.mono' ha
  filter_upwards [general_demand_nonneg μ hn] with d hd
  simpa only [Real.norm_eq_abs] using abs_G_le M hy hd

end BassokDisproofResearch
end

end CompleteGeneralDemand

section CompleteExponentialNoise

noncomputable section
namespace BassokDisproofResearch
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

def noise : Measure ℝ := expMeasure 1

instance noise_probability : IsProbabilityMeasure noise :=
  isProbabilityMeasure_expMeasure (by norm_num)

theorem noise_density : noise = volume.withDensity (exponentialPDF 1) := rfl

theorem noise_ac : noise ≪ volume := by
  rw [noise_density]
  exact withDensity_absolutelyContinuous _ _

theorem noise_nonneg : ∀ᵐ x ∂noise, 0 ≤ x := by
  rw [ae_iff]
  simp only [not_le]
  change noise (Iio 0) = 0
  rw [noise_density, withDensity_apply _ measurableSet_Iio]
  exact lintegral_exponentialPDF_of_nonpos (r := 1) le_rfl

theorem noise_integrable : Integrable id noise := by
  rw [noise_density]
  apply (integrable_withDensity_iff_integrable_smul'
    (show Measurable (exponentialPDF 1) from (measurable_exponentialPDFReal 1).ennreal_ofReal)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mpr
  have hi : IntegrableOn (fun x : ℝ => x * Real.exp (-x)) (Ioi 0) := by
    simpa using integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := 1) (p := 1) (b := 1) (by norm_num) (by norm_num) (by norm_num)
  have hh : Integrable (fun x : ℝ => (Ioi 0).indicator (fun x => x * Real.exp (-x)) x) volume :=
    hi.integrable_indicator measurableSet_Ioi
  apply hh.congr
  filter_upwards [] with x
  simp only [exponentialPDF_eq,
    id_eq, smul_eq_mul]
  by_cases hx : 0 < x
  · simp [hx, hx.le, mul_comm, ENNReal.toReal_ofReal (Real.exp_pos _).le]
  · have hle : x ≤ 0 := le_of_not_gt hx
    by_cases hz : x = 0
    · simp [hz]
    · have hlt : x < 0 := lt_of_le_of_ne hle hz
      simp [hx, not_le.mpr hlt]


theorem noise_full_support {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    0 < noise (Ioo a b) := by
  rw [noise_density, withDensity_apply _ measurableSet_Ioo,
    setLIntegral_pos_iff (show Measurable (exponentialPDF 1) from
      (measurable_exponentialPDFReal 1).ennreal_ofReal)]
  have he : Function.support (exponentialPDF 1) ∩ Ioo a b = Ioo a b := by
    apply Set.inter_eq_right.mpr
    intro x hx
    exact ne_of_gt (by
      rw [exponentialPDF_of_nonneg (ha.trans hx.1.le)]
      positivity)
  rw [he, Real.volume_Ioo, ENNReal.ofReal_pos]
  linarith

def noiseMean : ℝ := ∫ x, x ∂noise

theorem noiseMean_nonneg : 0 ≤ noiseMean := integral_nonneg_of_ae noise_nonneg

end BassokDisproofResearch
end

end CompleteExponentialNoise

section CompleteScaledNoise

noncomputable section
namespace BassokDisproofResearch
open MeasureTheory Set Filter

def scaledNoise (e : ℝ) : Measure ℝ := noise.map (fun x => e*x)

instance scaledNoise_probability (e : ℝ) : IsProbabilityMeasure (scaledNoise e) :=
  Measure.isProbabilityMeasure_map (by fun_prop)

theorem scaledNoise_ac {e : ℝ} (he : 0 < e) : scaledNoise e ≪ volume := by
  have h := noise_ac.map (show Measurable (fun x : ℝ => e*x) by fun_prop)
  rw [Real.map_volume_mul_left he.ne'] at h
  exact h.trans Measure.smul_absolutelyContinuous

theorem scaledNoise_nonneg {e : ℝ} (he : 0 ≤ e) : ∀ᵐ x ∂scaledNoise e, 0 ≤ x := by
  apply (ae_map_iff (by fun_prop) measurableSet_Ici).mpr
  filter_upwards [noise_nonneg] with x hx
  exact mul_nonneg he hx

theorem scaledNoise_integrable (e : ℝ) : Integrable id (scaledNoise e) := by
  exact (integrable_map_measure (by fun_prop) (by fun_prop)).mpr
    (noise_integrable.const_mul e)

theorem scaledNoise_mean (e : ℝ) : (∫ x, x ∂scaledNoise e) = e*noiseMean := by
  rw [scaledNoise, integral_map (by fun_prop) (by fun_prop), integral_const_mul]
  rfl

theorem scaledNoise_full_support {e a b : ℝ} (he : 0 < e) (ha : 0 ≤ a) (hab : a < b) :
    0 < scaledNoise e (Ioo a b) := by
  rw [scaledNoise, Measure.map_apply (by fun_prop) measurableSet_Ioo]
  have hset : (fun x : ℝ => e*x) ⁻¹' Ioo a b = Ioo (a/e) (b/e) := by
    ext x
    simp only [Set.mem_preimage, mem_Ioo, div_lt_iff₀ he, lt_div_iff₀ he]
    rw [mul_comm x e]
  rw [hset]
  exact noise_full_support (div_nonneg ha he.le) ((div_lt_div_iff_of_pos_right he).mpr hab)

end BassokDisproofResearch
end

end CompleteScaledNoise

section CompleteCouplingDefinitions

noncomputable section
namespace BassokDisproofResearch
open MeasureTheory Set Filter
open scoped ENNReal

def keepPair (e : ℝ) (zt : ℝ × ℝ) : ℝ × ℝ := (zt.1, zt.1+e*zt.2)
def dropPair (e : ℝ) (zt : ℝ × ℝ) : ℝ × ℝ := (zt.1, e*zt.2)

def smoothingCoupling (μ : Measure ℝ) (e : ℝ) : Measure (ℝ × ℝ) :=
  ENNReal.ofReal (1-e) • (μ.prod noise).map (keepPair e) +
  ENNReal.ofReal e • (μ.prod noise).map (dropPair e)

def smoothedLaw (μ : Measure ℝ) (e : ℝ) : Measure ℝ :=
  (smoothingCoupling μ e).map Prod.snd

theorem smoothing_weights {e : ℝ} (he : 0 ≤ e) (he1 : e ≤ 1) :
    ENNReal.ofReal (1-e) + ENNReal.ofReal e = 1 := by
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr he1) he]
  norm_num

theorem smoothingCoupling_probability (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {e : ℝ} (he : 0 ≤ e) (he1 : e ≤ 1) : IsProbabilityMeasure (smoothingCoupling μ e) := by
  constructor
  simp only [smoothingCoupling, Measure.add_apply, Measure.smul_apply,
    Measure.map_apply (show Measurable (keepPair e) by unfold keepPair; fun_prop) MeasurableSet.univ,
    Measure.map_apply (show Measurable (dropPair e) by unfold dropPair; fun_prop) MeasurableSet.univ,
    Set.preimage_univ, measure_univ, smul_eq_mul, mul_one]
  exact smoothing_weights he he1

theorem coupling_fst (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {e : ℝ} (he : 0 ≤ e) (he1 : e ≤ 1) :
    (smoothingCoupling μ e).map Prod.fst = μ := by
  rw [smoothingCoupling, Measure.map_add _ _ measurable_fst, Measure.map_smul, Measure.map_smul,
    Measure.map_map measurable_fst (show Measurable (keepPair e) by unfold keepPair; fun_prop),
    Measure.map_map measurable_fst (show Measurable (dropPair e) by unfold dropPair; fun_prop)]
  change ENNReal.ofReal (1-e) • (μ.prod noise).map Prod.fst +
    ENNReal.ofReal e • (μ.prod noise).map Prod.fst = μ
  rw [measurePreserving_fst.map_eq, ← add_smul, smoothing_weights he he1, one_smul]

theorem smoothedLaw_probability (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {e : ℝ} (he : 0 ≤ e) (he1 : e ≤ 1) : IsProbabilityMeasure (smoothedLaw μ e) := by
  have := smoothingCoupling_probability μ he he1
  exact Measure.isProbabilityMeasure_map measurable_snd.aemeasurable

end BassokDisproofResearch
end

end CompleteCouplingDefinitions

section CompleteSmoothedLaw

noncomputable section
namespace BassokDisproofResearch
open MeasureTheory Set Filter
open scoped ENNReal MeasureTheory

theorem smoothedLaw_formula (μ : Measure ℝ) [IsProbabilityMeasure μ] (e : ℝ) :
    smoothedLaw μ e = ENNReal.ofReal (1-e) • (μ ∗ scaledNoise e) +
      ENNReal.ofReal e • scaledNoise e := by
  rw [smoothedLaw, smoothingCoupling, Measure.map_add _ _ measurable_snd, Measure.map_smul, Measure.map_smul,
    Measure.map_map measurable_snd (show Measurable (keepPair e) by unfold keepPair; fun_prop),
    Measure.map_map measurable_snd (show Measurable (dropPair e) by unfold dropPair; fun_prop)]
  have hdrop : (μ.prod noise).map (Prod.snd ∘ dropPair e) = scaledNoise e := by
    calc
      _ = ((μ.prod noise).map Prod.snd).map (fun t => e*t) := by
        rw [Measure.map_map (by fun_prop) measurable_snd]
        rfl
      _ = scaledNoise e := by rw [(measurePreserving_snd (μ := μ) (ν := noise)).map_eq]; rfl
  rw [hdrop]
  congr 1
  rw [Measure.conv, scaledNoise]
  have hprod : μ.prod (noise.map (fun t => e*t)) =
      (μ.prod noise).map (fun zt : ℝ × ℝ => (zt.1,e*zt.2)) := by
    simpa only [Measure.map_id, Prod.map_def, id_eq] using (Measure.map_prod_map μ noise measurable_id
      (show Measurable (fun t : ℝ => e*t) by fun_prop))
  rw [hprod, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

theorem smoothedLaw_ac (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {e : ℝ} (he : 0 < e) : smoothedLaw μ e ≪ volume := by
  rw [smoothedLaw_formula]
  exact ((Measure.conv_absolutelyContinuous (scaledNoise_ac he)).smul_left (ENNReal.ofReal (1-e))).add_left
    ((scaledNoise_ac he).smul_left (ENNReal.ofReal e))

theorem smoothedLaw_full_support (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {e : ℝ} (he : 0 < e) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    0 < smoothedLaw μ e (Ioo a b) := by
  rw [smoothedLaw_formula, Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  exact lt_of_lt_of_le (ENNReal.mul_pos (ENNReal.ofReal_pos.mpr he).ne'
    (scaledNoise_full_support he ha hab).ne') (le_add_left le_rfl)

end BassokDisproofResearch
end

end CompleteSmoothedLaw

section CompleteCouplingIntegrability

noncomputable section
namespace BassokDisproofResearch
open MeasureTheory Set Filter
open scoped ENNReal

theorem source_fst_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable id μ) : Integrable Prod.fst (μ.prod noise) :=
  measurePreserving_fst.integrable_comp_of_integrable hμ

theorem source_snd_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Integrable Prod.snd (μ.prod noise) :=
  measurePreserving_snd.integrable_comp_of_integrable noise_integrable

theorem coupling_integrable_fst (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable id μ) (e : ℝ) : Integrable Prod.fst (smoothingCoupling μ e) := by
  have hk : Integrable Prod.fst ((μ.prod noise).map (keepPair e)) :=
    (integrable_map_measure (by fun_prop) (by unfold keepPair; fun_prop)).mpr
      (source_fst_integrable μ hμ)
  have hd : Integrable Prod.fst ((μ.prod noise).map (dropPair e)) :=
    (integrable_map_measure (by fun_prop) (by unfold dropPair; fun_prop)).mpr
      (source_fst_integrable μ hμ)
  exact (hk.smul_measure ENNReal.ofReal_ne_top).add_measure
    (hd.smul_measure ENNReal.ofReal_ne_top)

theorem coupling_integrable_snd (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable id μ) (e : ℝ) : Integrable Prod.snd (smoothingCoupling μ e) := by
  have hk : Integrable Prod.snd ((μ.prod noise).map (keepPair e)) :=
    (integrable_map_measure (by fun_prop) (by unfold keepPair; fun_prop)).mpr
      ((source_fst_integrable μ hμ).add ((source_snd_integrable μ).const_mul e))
  have hd : Integrable Prod.snd ((μ.prod noise).map (dropPair e)) :=
    (integrable_map_measure (by fun_prop) (by unfold dropPair; fun_prop)).mpr
      ((source_snd_integrable μ).const_mul e)
  exact (hk.smul_measure ENNReal.ofReal_ne_top).add_measure
    (hd.smul_measure ENNReal.ofReal_ne_top)

theorem smoothedLaw_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable id μ) (e : ℝ) : Integrable id (smoothedLaw μ e) :=
  (integrable_map_measure (by fun_prop) measurable_snd.aemeasurable).mpr
    (coupling_integrable_snd μ hμ e)

end BassokDisproofResearch
end

end CompleteCouplingIntegrability

section CompleteCouplingSupport

noncomputable section
namespace BassokDisproofResearch
open MeasureTheory Set Filter
open scoped ENNReal

theorem coupling_nonneg (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, 0 ≤ x) {e : ℝ} (he : 0 ≤ e) :
    ∀ᵐ z ∂smoothingCoupling μ e, 0 ≤ z.1 ∧ 0 ≤ z.2 := by
  have hf : ∀ᵐ z ∂μ.prod noise, 0 ≤ z.1 :=
    measurePreserving_fst.quasiMeasurePreserving.ae hμ
  have ht : ∀ᵐ z ∂μ.prod noise, 0 ≤ z.2 :=
    measurePreserving_snd.quasiMeasurePreserving.ae noise_nonneg
  rw [smoothingCoupling, ae_add_measure_iff]
  constructor
  · apply Measure.ae_smul_measure _ _
    apply (ae_map_iff (by unfold keepPair; fun_prop) (by measurability)).mpr
    filter_upwards [hf,ht] with z hz hzt
    exact ⟨hz, add_nonneg hz (mul_nonneg he hzt)⟩
  · apply Measure.ae_smul_measure _ _
    apply (ae_map_iff (by unfold dropPair; fun_prop) (by measurability)).mpr
    filter_upwards [hf,ht] with z hz hzt
    exact ⟨hz, mul_nonneg he hzt⟩

theorem smoothedLaw_nonneg (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, 0 ≤ x) {e : ℝ} (he : 0 ≤ e) :
    ∀ᵐ x ∂smoothedLaw μ e, 0 ≤ x := by
  apply (ae_map_iff measurable_snd.aemeasurable measurableSet_Ici).mpr
  exact (coupling_nonneg μ hμ he).mono fun _ h => h.2

end BassokDisproofResearch
end

end CompleteCouplingSupport

section CompleteSmoothedDemand

noncomputable section
namespace BassokDisproofResearch
open MeasureTheory Set Filter BassokSubstitution
variable {N : ℕ}

theorem smoothed_demand (μ : Fin N → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hn : ∀ i, ∀ᵐ x ∂μ i, 0 ≤ x) (hi : ∀ i, Integrable id (μ i))
    {e : ℝ} (he : 0 < e) : DemandLaw (fun i => smoothedLaw (μ i) e) := by
  intro i
  refine ⟨?_, smoothedLaw_integrable (μ i) (hi i) e, smoothedLaw_ac (μ i) he⟩
  have h := smoothedLaw_nonneg (μ i) (hn i) he.le
  rw [ae_iff] at h
  simpa only [not_le, Set.Iio_def] using h

theorem smoothed_full_support (μ : Fin N → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {e : ℝ} (he : 0 < e) : FullSupport (fun i => smoothedLaw (μ i) e) := by
  intro i a b ha hab
  exact smoothedLaw_full_support (μ i) he ha hab

end BassokDisproofResearch
end

end CompleteSmoothedDemand

section CompleteCouplingError

noncomputable section
namespace BassokDisproofResearch
open MeasureTheory Set Filter
open scoped ENNReal

theorem coupling_error (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable id μ) (hn : ∀ᵐ x ∂μ, 0 ≤ x)
    {e : ℝ} (he : 0 ≤ e) (he1 : e ≤ 1) :
    (∫ z, |z.2-z.1| ∂smoothingCoupling μ e) ≤ e*((∫ x, x ∂μ)+noiseMean) := by
  let f : ℝ × ℝ → ℝ := fun z => |z.2-z.1|
  have hk0 : Integrable (fun z : ℝ × ℝ => |e*z.2|) (μ.prod noise) :=
    ((source_snd_integrable μ).const_mul e).abs
  have hd0 : Integrable (fun z : ℝ × ℝ => |e*z.2-z.1|) (μ.prod noise) :=
    (((source_snd_integrable μ).const_mul e).sub (source_fst_integrable μ hμ)).abs
  have hk : Integrable f ((μ.prod noise).map (keepPair e)) := by
    apply (integrable_map_measure (by dsimp [f]; fun_prop) (by unfold keepPair; fun_prop)).mpr
    simpa [Function.comp_def, f, keepPair] using hk0
  have hd : Integrable f ((μ.prod noise).map (dropPair e)) := by
    apply (integrable_map_measure (by dsimp [f]; fun_prop) (by unfold dropPair; fun_prop)).mpr
    exact hd0
  have hp : ∀ᵐ z ∂μ.prod noise, 0 ≤ z.1 ∧ 0 ≤ z.2 := by
    filter_upwards [measurePreserving_fst.quasiMeasurePreserving.ae hn,
      measurePreserving_snd.quasiMeasurePreserving.ae noise_nonneg] with z h1 h2
    exact ⟨h1,h2⟩
  have hi1 : (∫ z : ℝ × ℝ, z.1 ∂μ.prod noise) = ∫ x, x ∂μ := by
    simpa only [(measurePreserving_fst (μ := μ) (ν := noise)).map_eq] using
      (integral_map (μ := μ.prod noise) (f := fun x : ℝ => x)
        measurable_fst.aemeasurable (by fun_prop)).symm
  have hi2 : (∫ z : ℝ × ℝ, z.2 ∂μ.prod noise) = noiseMean := by
    simpa only [(measurePreserving_snd (μ := μ) (ν := noise)).map_eq, noiseMean] using
      (integral_map (μ := μ.prod noise) (f := fun x : ℝ => x)
        measurable_snd.aemeasurable (by fun_prop)).symm
  have hik : (∫ z, f z ∂(μ.prod noise).map (keepPair e)) = e*noiseMean := by
    rw [integral_map (by unfold keepPair; fun_prop) (by dsimp [f]; fun_prop)]
    calc
      _ = ∫ z : ℝ × ℝ, e*z.2 ∂μ.prod noise := by
        apply integral_congr_ae
        filter_upwards [hp] with z hz
        simp [f,keepPair,abs_of_nonneg (mul_nonneg he hz.2)]
      _ = _ := by rw [integral_const_mul,hi2]
  have hid : (∫ z, f z ∂(μ.prod noise).map (dropPair e)) ≤
      (∫ x, x ∂μ)+e*noiseMean := by
    rw [integral_map (by unfold dropPair; fun_prop) (by dsimp [f]; fun_prop)]
    calc
      _ ≤ ∫ z : ℝ × ℝ, z.1+e*z.2 ∂μ.prod noise := by
        apply integral_mono_ae hd0 ((source_fst_integrable μ hμ).add
          ((source_snd_integrable μ).const_mul e))
        filter_upwards [hp] with z hz
        dsimp [f,dropPair]
        exact abs_sub_le_iff.mpr ⟨by nlinarith [mul_nonneg he hz.2],by nlinarith [mul_nonneg he hz.2]⟩
      _ = _ := by rw [integral_add (source_fst_integrable μ hμ)
          ((source_snd_integrable μ).const_mul e), integral_const_mul,hi1,hi2]
  change (∫ z, f z ∂smoothingCoupling μ e) ≤ _
  rw [smoothingCoupling, integral_add_measure
    (hk.smul_measure ENNReal.ofReal_ne_top) (hd.smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal (sub_nonneg.mpr he1), ENNReal.toReal_ofReal he,
    smul_eq_mul, smul_eq_mul, hik]
  nlinarith [mul_le_mul_of_nonneg_left hid he]

end BassokDisproofResearch
end

end CompleteCouplingError

section CompleteProductCoupling

noncomputable section
namespace BassokDisproofResearch
open MeasureTheory Set Filter BassokSubstitution BassokInventoryResearch
variable {N : ℕ}

theorem product_coupling_fst (μ : Fin N → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {e : ℝ} (he : 0 ≤ e) (he1 : e ≤ 1) :
    MeasurePreserving (fun z : Fin N → ℝ × ℝ => fun i => (z i).1)
      (Measure.pi (fun i => smoothingCoupling (μ i) e)) (Measure.pi μ) := by
  have (i : Fin N) := smoothingCoupling_probability (μ i) he he1
  have (i : Fin N) := Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
    (μ := smoothingCoupling (μ i) e)
  refine ⟨by fun_prop, ?_⟩
  rw [Measure.pi_map_pi (fun _ => measurable_fst.aemeasurable)]
  simp_rw [coupling_fst _ he he1]

theorem product_coupling_snd (μ : Fin N → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {e : ℝ} (he : 0 ≤ e) (he1 : e ≤ 1) :
    MeasurePreserving (fun z : Fin N → ℝ × ℝ => fun i => (z i).2)
      (Measure.pi (fun i => smoothingCoupling (μ i) e))
      (Measure.pi (fun i => smoothedLaw (μ i) e)) := by
  have (i : Fin N) := smoothingCoupling_probability (μ i) he he1
  have (i : Fin N) := smoothedLaw_probability (μ i) he he1
  refine ⟨by fun_prop, ?_⟩
  exact Measure.pi_map_pi (fun _ => measurable_snd.aemeasurable)

theorem product_coupling_nonneg (μ : Fin N → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (hn : ∀ i, ∀ᵐ x ∂μ i, 0 ≤ x)
    {e : ℝ} (he : 0 ≤ e) (he1 : e ≤ 1) :
    ∀ᵐ z ∂Measure.pi (fun i => smoothingCoupling (μ i) e),
      (0 ≤ fun i => (z i).1) ∧ (0 ≤ fun i => (z i).2) := by
  have (i : Fin N) := smoothingCoupling_probability (μ i) he he1
  have h : ∀ᵐ z ∂Measure.pi (fun i => smoothingCoupling (μ i) e),
      ∀ i, 0 ≤ (z i).1 ∧ 0 ≤ (z i).2 :=
    ae_all_iff.mpr fun i => (measurePreserving_eval (fun j => smoothingCoupling (μ j) e) i).quasiMeasurePreserving.ae
      (coupling_nonneg (μ i) (hn i) he)
  exact h.mono fun z hz => ⟨fun i => (hz i).1,fun i => (hz i).2⟩

end BassokDisproofResearch
end

end CompleteProductCoupling

section CompleteExpectationPerturbation

noncomputable section
namespace BassokDisproofResearch
open MeasureTheory Set Filter BassokSubstitution BassokInventoryResearch
variable {N : ℕ}

theorem expectation_perturbation (M : Model N) (μ : Fin N → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)]
    (hn : ∀ i, ∀ᵐ x ∂μ i, 0 ≤ x) (hi : ∀ i, Integrable id (μ i))
    {e : ℝ} (he : 0 ≤ e) (he1 : e ≤ 1) {y : Fin N → ℝ} (hy : 0 ≤ y) :
    |(∫ d, M.G y d ∂Measure.pi (fun i => smoothedLaw (μ i) e)) -
      (∫ d, M.G y d ∂Measure.pi μ)| ≤
      (gainConstant M + ∑ i, |M.penalty i|)*e*∑ i, ((∫ t, t ∂μ i)+noiseMean) := by
  let lam := fun i => smoothingCoupling (μ i) e
  let ν := fun i => smoothedLaw (μ i) e
  have (i : Fin N) := smoothingCoupling_probability (μ i) he he1
  have (i : Fin N) := smoothedLaw_probability (μ i) he he1
  have hfst := product_coupling_fst μ he he1
  have hsnd := product_coupling_snd μ he he1
  change MeasurePreserving (fun z : Fin N → ℝ × ℝ => fun i => (z i).1) (Measure.pi lam) (Measure.pi μ) at hfst
  change MeasurePreserving (fun z : Fin N → ℝ × ℝ => fun i => (z i).2) (Measure.pi lam) (Measure.pi ν) at hsnd
  have hg0 := general_G_integrable M μ hn hi hy
  have hg1 := general_G_integrable M ν (fun i => smoothedLaw_nonneg (μ i) (hn i) he)
    (fun i => smoothedLaw_integrable (μ i) (hi i) e) hy
  have hf0 := hfst.integrable_comp_of_integrable hg0
  have hf1 := hsnd.integrable_comp_of_integrable hg1
  change Integrable (fun z => M.G y (fun i => (z i).1)) (Measure.pi lam) at hf0
  change Integrable (fun z => M.G y (fun i => (z i).2)) (Measure.pi lam) at hf1
  have h0 : (∫ z, M.G y (fun i => (z i).1) ∂Measure.pi lam) =
      ∫ d, M.G y d ∂Measure.pi μ := by
    have hm : AEStronglyMeasurable (M.G y) ((Measure.pi lam).map (fun z i => (z i).1)) := by
      rw [hfst.map_eq]; exact hg0.aestronglyMeasurable
    simpa only [hfst.map_eq] using (integral_map hfst.measurable.aemeasurable hm).symm
  have h1 : (∫ z, M.G y (fun i => (z i).2) ∂Measure.pi lam) =
      ∫ d, M.G y d ∂Measure.pi ν := by
    have hm : AEStronglyMeasurable (M.G y) ((Measure.pi lam).map (fun z i => (z i).2)) := by
      rw [hsnd.map_eq]; exact hg1.aestronglyMeasurable
    simpa only [hsnd.map_eq] using (integral_map hsnd.measurable.aemeasurable hm).symm
  have hd (i : Fin N) : Integrable (fun z : Fin N → ℝ × ℝ => |(z i).2-(z i).1|)
      (Measure.pi lam) :=
    (measurePreserving_eval lam i).integrable_comp_of_integrable
      (((coupling_integrable_snd (μ i) (hi i) e).sub
        (coupling_integrable_fst (μ i) (hi i) e)).abs)
  have hdi (i : Fin N) : (∫ z : Fin N → ℝ × ℝ, |(z i).2-(z i).1| ∂Measure.pi lam) =
      ∫ z, |z.2-z.1| ∂lam i := by
    simpa only [(measurePreserving_eval lam i).map_eq] using
      (integral_map (μ := Measure.pi lam) (φ := fun z => z i)
        (f := fun z : ℝ × ℝ => |z.2-z.1|) (measurable_pi_apply i).aemeasurable (by fun_prop)).symm
  let C := gainConstant M + ∑ i, |M.penalty i|
  have hC : 0 ≤ C := add_nonneg (gainConstant_pos M).le (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  calc
    _ = |∫ z, M.G y (fun i => (z i).2) - M.G y (fun i => (z i).1) ∂Measure.pi lam| := by
      rw [integral_sub hf1 hf0,h1,h0]
    _ ≤ ∫ z, |M.G y (fun i => (z i).2) - M.G y (fun i => (z i).1)| ∂Measure.pi lam :=
      abs_integral_le_integral_abs
    _ ≤ ∫ z : Fin N → ℝ × ℝ, C*∑ i, |(z i).2-(z i).1| ∂Measure.pi lam := by
      apply integral_mono_ae (hf1.sub hf0).abs
        ((integrable_finsetSum _ fun i _ => hd i).const_mul C)
      filter_upwards [product_coupling_nonneg μ hn he he1] with z hz
      exact G_demand_lipschitz M hy hz.2 hz.1
    _ = C*∑ i, ∫ z, |z.2-z.1| ∂lam i := by
      rw [integral_const_mul,integral_finsetSum _ fun i _ => hd i]
      simp_rw [hdi]
    _ ≤ C*∑ i, e*((∫ t, t ∂μ i)+noiseMean) := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact Finset.sum_le_sum fun i _ => coupling_error (μ i) (hi i) (hn i) he he1
    _ = _ := by rw [← Finset.mul_sum]; change C*(e*_) = C*e*_; ring

end BassokDisproofResearch
end

end CompleteExpectationPerturbation

section CompletePerturbationParameter

noncomputable section
namespace BassokDisproofResearch
open MeasureTheory Set BassokSubstitution BassokInventoryResearch

def perturbationBudget : ℝ :=
  (gainConstant model + ∑ i, |model.penalty i|)*
    ∑ i, ((∫ t, t ∂atomicLaw i)+noiseMean)

theorem perturbationBudget_nonneg : 0 ≤ perturbationBudget := by
  apply mul_nonneg
  · exact add_nonneg (gainConstant_pos model).le (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  · exact Finset.sum_nonneg fun i _ => add_nonneg
      (integral_nonneg_of_ae (atomic_nonneg i)) noiseMean_nonneg

def smoothingSize : ℝ := 1 / (1000*(perturbationBudget+1))

theorem smoothingSize_bounds : 0 < smoothingSize ∧ smoothingSize ≤ 1 := by
  have hb := perturbationBudget_nonneg
  constructor
  · exact one_div_pos.mpr (by positivity)
  · change 1 / (1000*(perturbationBudget+1)) ≤ 1
    apply (div_le_iff₀ (by positivity : 0 < 1000*(perturbationBudget+1))).mpr
    linarith

def counterLaw (i : Fin 3) : Measure ℝ := smoothedLaw (atomicLaw i) smoothingSize

instance counterLaw_probability (i : Fin 3) : IsProbabilityMeasure (counterLaw i) :=
  smoothedLaw_probability (atomicLaw i) smoothingSize_bounds.1.le smoothingSize_bounds.2

theorem counterLaw_demand : DemandLaw counterLaw :=
  smoothed_demand atomicLaw atomic_nonneg (atomic_integrable id) smoothingSize_bounds.1

theorem counterLaw_support : FullSupport counterLaw :=
  smoothed_full_support atomicLaw smoothingSize_bounds.1

theorem counterLaw_error {y : Fin 3 → ℝ} (hy : 0 ≤ y) :
    |model.profit (Measure.pi counterLaw) 0 y - baselineProfit y| ≤ (1/1000 : ℝ) := by
  have h := expectation_perturbation model atomicLaw atomic_nonneg (atomic_integrable id)
    smoothingSize_bounds.1.le smoothingSize_bounds.2 hy
  rw [atomic_G_integral] at h
  have heq : model.profit (Measure.pi counterLaw) 0 y - baselineProfit y =
      (∫ d, model.G y d ∂Measure.pi counterLaw) - baselineRevenue y := by
    simp only [Model.profit, Pi.zero_apply, sub_zero, baselineProfit]
    ring
  rw [heq]
  apply h.trans
  change _ ≤ (1/1000 : ℝ)
  have hp : 0 < perturbationBudget+1 := by linarith [perturbationBudget_nonneg]
  have hh : smoothingSize*perturbationBudget ≤ (1/1000 : ℝ) := by
    dsimp [smoothingSize]
    rw [one_div_mul_eq_div]
    apply (div_le_iff₀ (by positivity : 0 < 1000*(perturbationBudget+1))).mpr
    linarith
  convert hh using 1
  dsimp [perturbationBudget]
  ring

end BassokDisproofResearch
end

end CompletePerturbationParameter

section CompleteSharpPerturbation

noncomputable section
namespace BassokDisproofResearch
open Set
variable {N : ℕ}

theorem sharp_perturbed_maximum (F F₀ : (Fin N → ℝ) → ℝ)
    (l z : Fin N → ℝ) (hz : l ≤ z) (k e : ℝ) (hk : 0 < k)
    (he : 2*e < k) (hc : ContinuousOn F {y | l ≤ y})
    (herr : ∀ y, l ≤ y → |F y-F₀ y| ≤ e)
    (hsharp : ∀ y, l ≤ y → k * (∑ i, |y i-z i|) ≤ F₀ z-F₀ y) :
    ∃ w, l ≤ w ∧ IsMaxOn F {y | l ≤ y} w ∧
      k * (∑ i, |w i-z i|) ≤ 2*e := by
  let b : Fin N → ℝ := fun i => z i+1
  have hzb : z ≤ b := fun i => by dsimp [b]; linarith
  obtain ⟨w, hw, hmax⟩ := (isCompact_Icc : IsCompact (Icc l b)).exists_isMaxOn
    ⟨z, hz, hzb⟩ (hc.mono fun _ h => h.1)
  have hall : IsMaxOn F {y | l ≤ y} w := by
    intro y hy
    change F y ≤ F w
    by_cases hyb : y ≤ b
    · exact hmax ⟨hy, hyb⟩
    · obtain ⟨i, hi⟩ : ∃ i, b i < y i := by
        simpa only [Pi.le_def, not_forall, not_le] using hyb
      have hd : 1 < |y i-z i| := by dsimp [b] at hi; rw [abs_of_pos (by linarith)]; linarith
      have hs : 1 < ∑ j, |y j-z j| := hd.trans_le
        (Finset.single_le_sum (fun j _ => abs_nonneg (y j-z j)) (Finset.mem_univ i))
      have hzerr := (abs_le.mp (herr z hz)).1
      have hyerr := (abs_le.mp (herr y hy)).2
      have hh := hsharp y hy
      have hwz : F z ≤ F w := hmax ⟨hz, hzb⟩
      have hp : k < k * (∑ j, |y j-z j|) := by simpa using mul_lt_mul_of_pos_left hs hk
      linarith
  refine ⟨w, hw.1, hall, ?_⟩
  have hzw : F z ≤ F w := hall hz
  have hwe := (abs_le.mp (herr w hw.1)).2
  have hze := (abs_le.mp (herr z hz)).1
  have hh := hsharp w hw.1
  linarith

theorem coordinate_le_sum_distance (y z : Fin N → ℝ) (i : Fin N) :
    |y i-z i| ≤ ∑ j, |y j-z j| :=
  Finset.single_le_sum (fun j _ => abs_nonneg (y j-z j)) (Finset.mem_univ i)

end BassokDisproofResearch
end

end CompleteSharpPerturbation

section CompleteCounterexampleMaxima

noncomputable section
namespace BassokDisproofResearch
open MeasureTheory Set BassokSubstitution BassokInventoryResearch

theorem counterexample_maxima : ∃ u q : Fin 3 → ℝ,
    0 ≤ u ∧ IsMaxOn (model.profit (Measure.pi counterLaw) 0) {y | 0 ≤ y} u ∧
    initialStock ≤ q ∧
    IsMaxOn (model.profit (Measure.pi counterLaw) initialStock) {y | initialStock ≤ y} q ∧
    u 2 ≤ initialStock 2 ∧ q 2 ≠ initialStock 2 := by
  have hc := profit_continuousOn model counterLaw counterLaw_demand
  obtain ⟨u, hu, hum, hud⟩ := sharp_perturbed_maximum
    (model.profit (Measure.pi counterLaw) 0) baselineProfit 0 baseStock
    stocks_nonneg.1 (1/16) (1/1000) (by norm_num) (by norm_num) hc
    (fun y hy => counterLaw_error hy) (fun y hy => baseline_sharp hy)
  obtain ⟨q, hq, hqm, hqd⟩ := sharp_perturbed_maximum
    (model.profit (Measure.pi counterLaw) 0) baselineProfit initialStock forcedStock
    stocks_nonneg.2.2 (1/48) (1/1000) (by norm_num) (by norm_num)
    (hc.mono fun _ h => stocks_nonneg.2.1.trans h)
    (fun y hy => counterLaw_error (stocks_nonneg.2.1.trans hy))
    (fun y hy => forced_sharp hy)
  refine ⟨u,q,hu,hum,hq,?_,?_,?_⟩
  · intro y hy
    change model.profit _ initialStock y ≤ model.profit _ initialStock q
    rw [profit_shift model (Measure.pi counterLaw) initialStock y,
      profit_shift model (Measure.pi counterLaw) initialStock q]
    have hh : model.profit (Measure.pi counterLaw) 0 y ≤ model.profit (Measure.pi counterLaw) 0 q := hqm hy
    linarith
  · have hi := coordinate_le_sum_distance u baseStock 2
    have hj := (le_abs_self (u 2-baseStock 2)).trans hi
    change u 2 - 1 ≤ ∑ j, |u j-baseStock j| at hj
    change u 2 ≤ 5/4
    linarith
  · have hi := coordinate_le_sum_distance q forcedStock 2
    have hj := (neg_le_abs (q 2-forcedStock 2)).trans hi
    change -(q 2 - 3/2) ≤ ∑ j, |q j-forcedStock j| at hj
    have : initialStock 2 < q 2 := by change 5/4 < q 2; linarith
    exact ne_of_gt this

end BassokDisproofResearch
end

end CompleteCounterexampleMaxima

section CompleteNativeRoot

open MeasureTheory Set BassokSubstitution
namespace BassokDisproofResearch

set_option linter.unusedVariables false in
theorem native_disproof : ¬ (∀ {N : ℕ} (M : Model N)
    (hA1 : M.Assumption1) (hA2 : M.Assumption2) (hA3 : M.Assumption3) (hb : 0 ≤ M.b)
    (hcost : ∀ i, M.s i < M.c i ∧ M.c i < M.p i + M.penalty i)
    (ν : Fin N → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)] (hν : DemandLaw ν)
    (hsupp : FullSupport ν)
    (ystar : Fin N → ℝ) (hystar_nonneg : 0 ≤ ystar)
    (hystar : IsMaxOn (M.profit (Measure.pi ν) 0) {y | 0 ≤ y} ystar)
    (x : Fin N → ℝ) (hx : 0 ≤ x)
    (ybar : Fin N → ℝ) (hybar_ge : x ≤ ybar)
    (hybar : IsMaxOn (M.profit (Measure.pi ν) x) {y | x ≤ y} ybar)
    (i : Fin N) (hi : ystar i ≤ x i),
    ybar i = x i) := by
  intro h
  obtain ⟨u, q, hu, hum, hq, hqm, hui, hqi⟩ := counterexample_maxima
  obtain ⟨hA1,hA2,hA3,hb,hcost⟩ := model_assumptions
  exact hqi (h model hA1 hA2 hA3 hb hcost counterLaw counterLaw_demand
    counterLaw_support u hu hum initialStock stocks_nonneg.2.1 q hq hqm 2 hui)

end BassokDisproofResearch

end CompleteNativeRoot

open MeasureTheory Set BassokSubstitution

set_option linter.unusedVariables false in
theorem solution : ¬ (∀ {N : ℕ} (M : Model N)
    (hA1 : M.Assumption1) (hA2 : M.Assumption2) (hA3 : M.Assumption3) (hb : 0 ≤ M.b)
    (hcost : ∀ i, M.s i < M.c i ∧ M.c i < M.p i + M.penalty i)
    (ν : Fin N → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)] (hν : DemandLaw ν)
    (hsupp : FullSupport ν)
    (ystar : Fin N → ℝ) (hystar_nonneg : 0 ≤ ystar)
    (hystar : IsMaxOn (M.profit (Measure.pi ν) 0) {y | 0 ≤ y} ystar)
    (x : Fin N → ℝ) (hx : 0 ≤ x)
    (ybar : Fin N → ℝ) (hybar_ge : x ≤ ybar)
    (hybar : IsMaxOn (M.profit (Measure.pi ν) x) {y | x ≤ y} ybar)
    (i : Fin N) (hi : ystar i ≤ x i),
    ybar i = x i) := BassokDisproofResearch.native_disproof
