-- Prove2me | solution 1 for ConsistentSubmodular.FractionalWindow.exists_windowSamples
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:41:03.075671+00:00
-- url     : https://prove2.me/submissions/45ea6bb1-e2a2-46c2-be0b-b59792b19907

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_PathSubdivision
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_WindowSamples
import Theorems.Thm_ConsistentSubmodular_physical_multilinear_lift
import Theorems.Thm_ConsistentSubmodular_PolygonalPath_subdivide_node_in_segment
import Theorems.Thm_ConsistentSubmodular_PolygonalPath_subdivide_edge
import Theorems.Thm_ConsistentSubmodular_PolygonalPath_Along_subdivide
import Theorems.Thm_ConsistentSubmodular_physical_intersection_lower
import Theorems.Thm_ConsistentSubmodular_RoundingBudget_window_value_budget_exp
import Theorems.Thm_ConsistentSubmodular_Objective_exists_residual_rounding

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

variable {n : ℕ}

namespace Objective

variable (f : Objective n)

theorem bufferedOptimum_mono {N Q R : Finset (Fin n)} {k : ℕ}
    (hQR : Q ⊆ R) : f.bufferedOptimum N Q k ≤ f.bufferedOptimum N R k := by
  have hA := f.bufferedOptimizer_spec N Q k
  exact (f.monotone _ _ (Finset.union_subset_union_left hQR)).trans
    (f.le_bufferedOptimum hA.1 hA.2.1)

end Objective

end ConsistentSubmodular

end

end

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

variable {n m : ℕ}

theorem physicalProbability_nonnegative
    (cores : Fin (m + 1) → Finset (Fin n)) (p : Point m)
    (hp : ∀ i, 0 ≤ p i) (e : Fin n) : 0 ≤ physicalProbability cores p e := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact hp i
  · rfl

theorem physicalProbability_le_mass
    (cores : Fin (m + 1) → Finset (Fin n)) (p : Point m)
    (hp : ∀ i, 0 ≤ p i) (e : Fin n) :
    physicalProbability cores p e ≤ ∑ i, p i := by
  exact Finset.sum_le_sum (fun i _ => by split_ifs <;> simp_all)

theorem physicalProbability_mem_unitInterval
    (cores : Fin (m + 1) → Finset (Fin n)) (p : Point m)
    (hp : IsSimplex p) (e : Fin n) :
    0 ≤ physicalProbability cores p e ∧ physicalProbability cores p e ≤ 1 := by
  exact ⟨physicalProbability_nonnegative cores p hp.1 e,
    (physicalProbability_le_mass cores p hp.1 e).trans_eq hp.2⟩

theorem physicalProbability_total
    (cores : Fin (m + 1) → Finset (Fin n)) (p : Point m) :
    (∑ e, physicalProbability cores p e) = ∑ i, p i * (cores i).card := by
  unfold physicalProbability
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp [mul_comm]

theorem physicalProbability_total_le
    (cores : Fin (m + 1) → Finset (Fin n)) (p : Point m)
    (hp : ∀ i, 0 ≤ p i) (hmass : (∑ i, p i) ≤ 1)
    {k : ℕ} (hcore : ∀ i, (cores i).card ≤ k) :
    (∑ e, physicalProbability cores p e) ≤ k := by
  rw [physicalProbability_total]
  calc
    (∑ i, p i * (cores i).card) ≤ ∑ i, p i * (k : ℝ) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (hcore i)) (hp i))
    _ = (∑ i, p i) * k := (Finset.sum_mul _ _ _).symm
    _ ≤ 1 * (k : ℝ) := mul_le_mul_of_nonneg_right hmass (Nat.cast_nonneg k)
    _ = k := one_mul _

theorem physicalProbability_vertex
    (cores : Fin (m + 1) → Finset (Fin n)) (i : Fin (m + 1)) (e : Fin n) :
    physicalProbability cores (vertex i) e = if e ∈ cores i then 1 else 0 := by
  classical
  unfold physicalProbability vertex
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

theorem physicalProbability_abs_difference_le
    (cores : Fin (m + 1) → Finset (Fin n)) (p q : Point m) (e : Fin n) :
    |physicalProbability cores p e - physicalProbability cores q e| ≤
      physicalProbability cores (fun i => |p i - q i|) e := by
  unfold physicalProbability
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  split_ifs <;> simp

/-- Expected changes along a shared-threshold transition are bounded by the
type L1 distance times core capacity, with repeated physical elements counted
only once in the actual recourse. -/
theorem physicalProbability_l1_le
    (cores : Fin (m + 1) → Finset (Fin n)) (p q : Point m)
    {k : ℕ} (hcore : ∀ i, (cores i).card ≤ k) :
    (∑ e, |physicalProbability cores p e - physicalProbability cores q e|) ≤
      (k : ℝ) * ∑ i, |p i - q i| := by
  calc
    _ ≤ ∑ e, physicalProbability cores (fun i => |p i - q i|) e :=
      Finset.sum_le_sum (fun e _ => physicalProbability_abs_difference_le cores p q e)
    _ = ∑ i, |p i - q i| * (cores i).card := physicalProbability_total _ _
    _ ≤ ∑ i, |p i - q i| * (k : ℝ) := Finset.sum_le_sum
      (fun i _ => mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (hcore i)) (abs_nonneg _))
    _ = _ := by rw [← Finset.sum_mul]; ring

end ConsistentSubmodular

end

end

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

variable {m : ℕ}

theorem typeL1_simplex_le_two {p q : Point m} (hp : IsSimplex p) (hq : IsSimplex q) :
    typeL1 p q ≤ 2 := by
  calc
    typeL1 p q ≤ ∑ i, (p i + q i) := by
      apply Finset.sum_le_sum
      intro i _
      exact abs_le.mpr ⟨by linarith [hp.1 i, hq.1 i], by linarith [hp.1 i, hq.1 i]⟩
    _ = 2 := by rw [Finset.sum_add_distrib, hp.2, hq.2]; norm_num

theorem typeL1_mix (p q : Point m) (x y : ℝ) :
    typeL1 (mix p q x) (mix p q y) = |x - y| * typeL1 p q := by
  unfold typeL1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he : mix p q x i - mix p q y i = (x - y) * (q i - p i) := by unfold mix; ring
  rw [he, abs_mul, abs_sub_comm (q i)]

namespace PolygonalPath

theorem subdivide_terminal (γ : PolygonalPath m) (N : ℕ) (hN : 0 < N) :
    (γ.subdivide N).node (Fin.last (γ.subdivide N).pieces) = γ.node (Fin.last γ.pieces) := by
  simp [subdivide, Nat.mul_div_cancel _ hN]

theorem subdivide_original_node (γ : PolygonalPath m) (N : ℕ) (hN : 0 < N)
    (i : Fin (γ.pieces + 1)) :
    (γ.subdivide N).node ⟨i.val * N, by
      dsimp only [subdivide_pieces]
      have := i.isLt
      nlinarith⟩ = γ.node i := by
  by_cases hi : i.val < γ.pieces
  · simpa using γ.subdivide_node_in_segment N hN ⟨i.val, hi⟩ 0 (Nat.zero_le N)
  · have he : i.val = γ.pieces := by omega
    have hl : i = Fin.last γ.pieces := Fin.ext he
    subst i
    exact γ.subdivide_terminal N hN

theorem subdivide_initial (γ : PolygonalPath m) (N : ℕ) (hN : 0 < N) :
    (γ.subdivide N).node 0 = γ.node 0 := by
  simpa [-subdivide_pieces] using γ.subdivide_original_node N hN 0

theorem subdivide_step_le (γ : PolygonalPath m)
    (hγ : ∀ i, IsSimplex (γ.node i)) (N : ℕ) (hN : 0 < N)
    (j : Fin (γ.subdivide N).pieces) :
    typeL1 ((γ.subdivide N).node j.castSucc) ((γ.subdivide N).node j.succ) ≤ 2 / N := by
  obtain ⟨a, r, hr, hl, hu⟩ := γ.subdivide_edge N hN j
  rw [hl, hu, typeL1_mix]
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have habs : |(r : ℝ) / N - ((r : ℝ) + 1) / N| = 1 / N := by
    have he : (r : ℝ) / N - ((r : ℝ) + 1) / N = -(1 / N) := by ring
    rw [he, abs_neg, abs_of_nonneg (by positivity)]
  rw [habs]
  have h := mul_le_mul_of_nonneg_left (typeL1_simplex_le_two (hγ a.castSucc) (hγ a.succ))
    (show (0 : ℝ) ≤ 1 / N by positivity)
  simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using h

theorem subdivide_length_le (γ : PolygonalPath m)
    (hγ : ∀ i, IsSimplex (γ.node i)) (N : ℕ) (hN : 0 < N) :
    (γ.subdivide N).length ≤ 2 * γ.pieces := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun j _ => γ.subdivide_step_le hγ N hN j)
  change (γ.subdivide N).length ≤ _ at h
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  simp only [Fintype.card_eq_nat_card, Nat.card_fin] at h
  change (γ.subdivide N).length ≤ ((γ.pieces * N : ℕ) : ℝ) * (2 / N) at h
  rw [Nat.cast_mul] at h
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have he : (γ.pieces : ℝ) * N * (2 / N) = 2 * γ.pieces := by field_simp
  rwa [he] at h

end PolygonalPath

end ConsistentSubmodular

end

end

section

namespace ConsistentSubmodular

theorem lt_two_pow_logBudget (x : ℕ) : x < 2 ^ logBudget x :=
  Nat.lt_pow_succ_log_self (by norm_num) x

theorem one_le_logBudget (x : ℕ) : 1 ≤ logBudget x := Nat.le_add_left 1 _

namespace RoundingBudget

/-- `exp (-c) ≤ 1 / B` once `B ≤ 2 ^ c`. -/
theorem exp_neg_le_inv_of_le_two_pow {B c : ℕ} (hB : 0 < B) (hc : B ≤ 2 ^ c) :
    Real.exp (-(c : ℝ)) ≤ 1 / B := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hpow : (2 : ℝ) ^ c ≤ Real.exp c := by
    calc (2 : ℝ) ^ c ≤ Real.exp 1 ^ c := pow_le_pow_left₀ (by norm_num) h2 c
      _ = Real.exp c := by rw [← Real.exp_nat_mul, mul_one]
  have hBr : (B : ℝ) ≤ Real.exp c := (by exact_mod_cast hc : (B : ℝ) ≤ 2 ^ c).trans hpow
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le (by exact_mod_cast hB) hBr

/-- The cardinality tail of deviation `κ / N` fits the per-test budget once
`κ ≥ 4 N² c` and `4 B ≤ 2 ^ c`. -/
theorem size_budget_exp (B N c : ℕ) (κ : ℝ) (hB : 0 < B) (hN : 0 < N)
    (hc : 4 * B ≤ 2 ^ c) (hκ : 4 * (N : ℝ) ^ 2 * c ≤ κ) (hκpos : 0 < κ) :
    Real.exp (-((κ / N) ^ 2) / (4 * κ)) ≤ 1 / (4 * B) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hexp : -((κ / N) ^ 2) / (4 * κ) = -(κ / (4 * (N : ℝ) ^ 2)) := by
    field_simp
  rw [hexp]
  have hge : (c : ℝ) ≤ κ / (4 * (N : ℝ) ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have h := exp_neg_le_inv_of_le_two_pow (B := 4 * B) (by positivity) hc
  push_cast at h
  exact (Real.exp_le_exp.mpr (neg_le_neg hge)).trans h

/-- Common per-test budget, with one quarter reserved for total operations. -/
theorem union_budget (B d e : ℝ) (hB : 0 < B) (hd : d ≤ B) (he : e ≤ B) :
    d * (1 / (4 * B)) + e * (1 / (4 * B)) + (1 : ℝ) / 4 < 1 := by
  have hp : (0 : ℝ) ≤ 1 / (4 * B) := by positivity
  have h1 := mul_le_mul_of_nonneg_right hd hp
  have h2 := mul_le_mul_of_nonneg_right he hp
  have hcancel : B * (1 / (4 * B)) = (1 : ℝ) / 4 := by field_simp
  rw [hcancel] at h1 h2
  linarith

end RoundingBudget

end ConsistentSubmodular

end

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

namespace FractionalWindow

variable {n κ N T S : ℕ} {α : ℝ} {f : Objective n} {old initial terminal : Finset (Fin n)}
  {Q : ℕ → Finset (Fin n)} {hQ : Monotone Q}
  (W : FractionalWindow f old Q hQ κ N T initial terminal α S)

theorem retained_physical (i : Fin (3 * N + 2)) :
    α * f.bufferedOptimum old (Q (W.retained i)) κ ≤
      finiteExpectation (physicalProbability W.cores W.checkpoint)
        (fun A => f.value (Q (W.retained i) ∪ A)) :=
  (W.checkpoint_retained i).trans (physical_multilinear_lift f W.cores (Q (W.retained i))
    W.checkpoint W.simplex.1 W.simplex.2.le)

end FractionalWindow

end ConsistentSubmodular

end

end

section

namespace ConsistentSubmodular

theorem windowTestBound_pos (N S : ℕ) : 0 < windowTestBound N S := by
  unfold windowTestBound
  positivity

theorem windowHeavyBound_pos {N : ℕ} (S : ℕ) (hN : 0 < N) : 0 < windowHeavyBound N S := by
  unfold windowHeavyBound
  have := one_le_logBudget (4 * windowTestBound N S)
  positivity

/-- The bound allows both node and intersection value tests, even if both
endpoints of each entry/exit path are counted separately. -/
theorem window_test_count (N S s nodes tests : ℕ) (hs : s ≤ S)
    (hnodes : nodes ≤ 8 * N * s + 2)
    (htests : tests ≤ 16 * N * s + 3 * N + 4) :
    nodes + tests ≤ windowTestBound N S := by
  have hh := Nat.mul_le_mul_left (24 * N) hs
  have hsq : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hNS : N * S ≤ (N + 1) ^ 2 * S := Nat.mul_le_mul_right S (by nlinarith)
  unfold windowTestBound
  nlinarith

theorem window_cost_budget (S s κ : ℕ) (hs : s ≤ S) :
    2 * (s : ℝ) * κ ≤ (8 * (S : ℝ) * κ) * (1 / 4 : ℝ) := by
  have hs' : (s : ℝ) ≤ S := by exact_mod_cast hs
  have hh := mul_le_mul_of_nonneg_right hs' (show 0 ≤ 2 * (κ : ℝ) by positivity)
  nlinarith only [hh]

theorem window_scale_positive {N S κ : ℕ} (hN : 0 < N) (hκ : windowHeavyBound N S ≤ κ) :
    0 < κ := lt_of_lt_of_le (windowHeavyBound_pos S hN) hκ

end ConsistentSubmodular

end

section

open scoped BigOperators
set_option maxHeartbeats 2000000
open ConsistentSubmodular
open ConsistentSubmodular.FractionalWindow
variable {n κ N T S : ℕ} {α : ℝ} {f : Objective n} {old initial terminal : Finset (Fin n)}
  {Q : ℕ → Finset (Fin n)} {hQ : Monotone Q}
  (W : FractionalWindow f old Q hQ κ N T initial terminal α S)

theorem solution (hN : 200 ≤ N) (hS : 0 < S) (hκ : windowHeavyBound N S ≤ κ)
    (hV : 0 < f.bufferedOptimum old ∅ κ) :
    Nonempty (WindowSamples W (windowHeavyBound N S)) := by
  classical
  let V := f.bufferedOptimum old ∅ κ
  let B := windowTestBound N S
  let H := windowHeavyBound N S
  have hNpos : 0 < N := by omega
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hNpos
  have hSr : (0 : ℝ) < S := Nat.cast_pos.mpr hS
  have hBr : (0 : ℝ) < B := Nat.cast_pos.mpr (windowTestBound_pos N S)
  have hHpos : 0 < H := windowHeavyBound_pos S hNpos
  have hκpos : 0 < κ := window_scale_positive hNpos hκ
  have hκr : (0 : ℝ) < κ := Nat.cast_pos.mpr hκpos
  have hsubpos : 0 < 8 * N := by omega
  let E := W.entry.subdivide (8 * N)
  let X := W.exit.subdivide (8 * N)
  let P := CompatibleProfile.fromPhysical f W.cores Q hQ
  have hE : E.Along (fun p => IsSimplex p ∧ α * f.bufferedOptimum old (Q 0) κ ≤ P.multilinearValue 0 p) :=
    (show W.entry.Along (fun p => IsSimplex p ∧ α * f.bufferedOptimum old (Q 0) κ ≤
      P.multilinearValue 0 p) from W.entry_safe).subdivide (8 * N) hsubpos
  have hX : X.Along (fun p => IsSimplex p ∧ α * f.bufferedOptimum old (Q T) κ ≤ P.multilinearValue T p) :=
    (show W.exit.Along (fun p => IsSimplex p ∧ α * f.bufferedOptimum old (Q T) κ ≤
      P.multilinearValue T p) from W.exit_safe).subdivide (8 * N) hsubpos
  let Node := Fin (E.pieces + 1) ⊕ Fin (X.pieces + 1)
  let Edge := Fin E.pieces ⊕ Fin X.pieces
  let Test := Edge ⊕ Fin (3 * N + 2)
  let point : Node → Point (3 * N + 1) := Sum.elim E.node X.node
  let z := fun t => physicalProbability W.cores (point t)
  let edgeL : Edge → Node := Sum.elim (fun j => .inl j.castSucc) (fun j => .inr j.castSucc)
  let edgeR : Edge → Node := Sum.elim (fun j => .inl j.succ) (fun j => .inr j.succ)
  let cp : Node := .inl (Fin.last E.pieces)
  let left : Test → Node := Sum.elim edgeL (fun _ => cp)
  let right : Test → Node := Sum.elim edgeR (fun _ => cp)
  let buffers : Test → Finset (Fin n) := Sum.elim
    (Sum.elim (fun _ => Q 0) (fun _ => Q T)) (fun i => Q (W.retained i))
  let targets : Test → ℝ := Sum.elim
    (Sum.elim (fun _ => α * f.bufferedOptimum old (Q 0) κ - V / (4 * N))
      (fun _ => α * f.bufferedOptimum old (Q T) κ - V / (4 * N)))
    (fun i => α * f.bufferedOptimum old (Q (W.retained i)) κ)
  have hpoint (t : Node) : IsSimplex (point t) := by
    cases t with
    | inl j => exact (hE.1 j).1
    | inr j => exact (hX.1 j).1
  have hz (t : Node) (e) : 0 ≤ z t e ∧ z t e ≤ 1 :=
    physicalProbability_mem_unitInterval W.cores _ (hpoint t) e
  have hsupport (t : Node) (e) (he : e ∉ old) : z t e = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hn : e ∉ W.cores i := fun hi => he (W.core_subset i hi)
    simp [hn]
  have hmass (t : Node) : (∑ e, z t e) ≤ κ :=
    physicalProbability_total_le W.cores _ (hpoint t).1 (hpoint t).2.le W.core_card
  have hcp : point cp = W.checkpoint := by
    exact (W.entry.subdivide_terminal (8 * N) hsubpos).trans W.entry_terminal
  have hdist (γ : PolygonalPath (3 * N + 1)) (hcube : ∀ j, IsSimplex (γ.node j))
      (j : Fin (γ.subdivide (8 * N)).pieces) :
      typeL1 ((γ.subdivide (8 * N)).node j.castSucc) ((γ.subdivide (8 * N)).node j.succ) ≤ 1 / (4 * N) := by
    have h := γ.subdivide_step_le hcube (8 * N) hsubpos j
    have he : (2 : ℝ) / (8 * N : ℕ) = 1 / (4 * N) := by push_cast; ring
    rwa [he] at h
  have htarget (i : Test) : targets i ≤ finiteExpectation
      (fun e => min (z (left i) e) (z (right i) e)) (fun S => f.value (buffers i ∪ S)) := by
    cases i with
    | inl edge =>
      cases edge with
      | inl j =>
        have hlift := physical_intersection_lower f W.cores (Q 0) V hV.le W.core_value
          (E.node j.castSucc) (E.node j.succ) (hE.1 _).1 (hE.1 _).1
        have hd := mul_le_mul_of_nonneg_left (hdist W.entry (fun j => (W.entry_safe.1 j).1) j) hV.le
        have hv := (hE.1 j.castSucc).2
        change α * f.bufferedOptimum old (Q 0) κ - V / (4 * N) ≤ _
        change α * f.bufferedOptimum old (Q 0) κ ≤ finiteExpectation _ (f.onTypes W.cores (Q 0)).value at hv
        dsimp only [z, point, left, right, edgeL, edgeR, buffers, Sum.elim] at *
        change V * (∑ i, |E.node j.castSucc i - E.node j.succ i|) ≤ V * (1 / (4 * N)) at hd
        rw [mul_one_div] at hd
        nlinarith only [hlift, hd, hv]
      | inr j =>
        have hlift := physical_intersection_lower f W.cores (Q T) V hV.le W.core_value
          (X.node j.castSucc) (X.node j.succ) (hX.1 _).1 (hX.1 _).1
        have hd := mul_le_mul_of_nonneg_left (hdist W.exit (fun j => (W.exit_safe.1 j).1) j) hV.le
        have hv := (hX.1 j.castSucc).2
        change α * f.bufferedOptimum old (Q T) κ - V / (4 * N) ≤ _
        change α * f.bufferedOptimum old (Q T) κ ≤ finiteExpectation _ (f.onTypes W.cores (Q T)).value at hv
        dsimp only [z, point, left, right, edgeL, edgeR, buffers, Sum.elim] at *
        change V * (∑ i, |X.node j.castSucc i - X.node j.succ i|) ≤ V * (1 / (4 * N)) at hd
        rw [mul_one_div] at hd
        nlinarith only [hlift, hd, hv]
    | inr i =>
      simpa only [targets, left, right, buffers, Sum.elim, z, min_self, hcp] using W.retained_physical i
  have hpathcost (γ : PolygonalPath (3 * N + 1)) (hcube : ∀ j, IsSimplex (γ.node j)) :
      (∑ j : Fin (γ.subdivide (8 * N)).pieces,
        ∑ e, |physicalProbability W.cores ((γ.subdivide (8 * N)).node j.castSucc) e -
          physicalProbability W.cores ((γ.subdivide (8 * N)).node j.succ) e|) ≤
        2 * (γ.pieces : ℝ) * κ := by
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun (j : Fin (γ.subdivide (8 * N)).pieces) _ =>
      physicalProbability_l1_le W.cores ((γ.subdivide (8 * N)).node j.castSucc)
        ((γ.subdivide (8 * N)).node j.succ) W.core_card)
    rw [← Finset.mul_sum] at hsum
    have hh := mul_le_mul_of_nonneg_left (γ.subdivide_length_le hcube (8 * N) hsubpos) (Nat.cast_nonneg κ : (0 : ℝ) ≤ κ)
    change _ ≤ (κ : ℝ) * (γ.subdivide (8 * N)).length at hsum
    nlinarith only [hsum, hh]
  have hcostBudget : (∑ j : Edge, ∑ e, |z (edgeL j) e - z (edgeR j) e|) ≤
      (8 * (S : ℝ) * κ) * (1 / 4 : ℝ) := by
    rw [Fintype.sum_sum_type]
    have he := hpathcost W.entry (fun j => (W.entry_safe.1 j).1)
    have hx := hpathcost W.exit (fun j => (W.exit_safe.1 j).1)
    have hb := window_cost_budget S (W.entry.pieces + W.exit.pieces) κ W.pieces
    push_cast at hb
    dsimp only [z, point, edgeL, edgeR, Sum.elim]
    nlinarith only [he, hx, hb]
  have hcount : Fintype.card Node + Fintype.card Test ≤ B := by
    have hnodeCard : Fintype.card Node = (E.pieces + 1) + (X.pieces + 1) := by
      exact (Fintype.card_congr (show Node ≃ Fin ((E.pieces + 1) + (X.pieces + 1)) from
        finSumFinEquiv)).trans (Fintype.card_fin _)
    have htestCard : Fintype.card Test = (E.pieces + X.pieces) + (3 * N + 2) := by
      exact (Fintype.card_congr (show Test ≃ Fin ((E.pieces + X.pieces) + (3 * N + 2)) from
        (Equiv.sumCongr finSumFinEquiv (Equiv.refl _)).trans finSumFinEquiv)).trans (Fintype.card_fin _)
    apply window_test_count N S (W.entry.pieces + W.exit.pieces) _ _ W.pieces
    · rw [hnodeCard]
      simp only [E, X, PolygonalPath.subdivide_pieces]
      nlinarith
    · rw [htestCard]
      simp only [E, X, PolygonalPath.subdivide_pieces]
      nlinarith
  have hcountNode : (Fintype.card Node : ℝ) ≤ B := by exact_mod_cast (show Fintype.card Node ≤ B by omega)
  have hcountTest : (Fintype.card Test : ℝ) ≤ B := by exact_mod_cast (show Fintype.card Test ≤ B by omega)
  obtain ⟨c, hcdef⟩ : ∃ c, c = logBudget (4 * B) := ⟨_, rfl⟩
  have hc : 4 * B ≤ 2 ^ c := hcdef ▸ (lt_two_pow_logBudget _).le
  have hHeq : H = 64 * N ^ 2 * c := by rw [hcdef]; rfl
  have hHc : 64 * N ^ 2 * c ≤ H := hHeq.ge
  have hlarge : 4 * (N : ℝ) ^ 2 * c ≤ κ := by
    have hHκ : H ≤ κ := hκ
    have h4 : 4 * N ^ 2 * c ≤ H := by
      rw [hHeq]
      exact Nat.mul_le_mul_right c (Nat.mul_le_mul_right (N ^ 2) (by norm_num))
    exact_mod_cast h4.trans hHκ
  have hb2 : (κ : ℝ) / N ≤ 2 * κ := by
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
    have := div_le_self hκr.le hN1
    linarith
  obtain ⟨D, S, hDU, hDH, hSU, hzero, hone, hcard, hval, hcost, hequal⟩ :=
    f.exists_residual_rounding old κ H hHpos hκ V hV
      (fun A hA hAk => by simpa using f.le_bufferedOptimum (Q := ∅) hA hAk)
      z hz hsupport hmass buffers left right edgeL edgeR targets htarget
      (V / (4 * N)) ((κ : ℝ) / N) (8 * (S : ℝ) * κ) (1 / (4 * B)) (1 / (4 * B)) (1 / 4)
      (by positivity) (by positivity) hb2 (mul_pos (mul_pos (by norm_num) hSr) hκr)
      (RoundingBudget.size_budget_exp B N c κ (windowTestBound_pos N S) hNpos hc hlarge hκr)
      (RoundingBudget.window_value_budget_exp B N c H V (windowTestBound_pos N S) hNpos hV
        hHpos hc hHc)
      hcostBudget (RoundingBudget.union_budget B _ _ hBr hcountNode hcountTest)
  have hpure (t : Node) (A : Finset (Fin n))
      (ht : ∀ e, z t e = if e ∈ A then 1 else 0) : S t = A := by
    ext e
    by_cases he : e ∈ A
    · exact ⟨fun _ => he, fun _ => hone t e (by simp [ht, he])⟩
    · exact ⟨fun hs => (hzero t e (by simp [ht, he]) hs).elim, fun h => (he h).elim⟩
  have hE0 : S (.inl 0) = initial := by
    apply hpure
    intro e
    change physicalProbability W.cores (E.node 0) e = _
    rw [show E.node 0 = vertex 0 from (W.entry.subdivide_initial (8 * N) hsubpos).trans W.entry_initial,
      physicalProbability_vertex, W.core_initial]
  have hXT : S (.inr (Fin.last X.pieces)) = terminal := by
    apply hpure
    intro e
    change physicalProbability W.cores (X.node (Fin.last X.pieces)) e = _
    rw [show X.node (Fin.last X.pieces) = vertex (Fin.last (3 * N + 1)) from
      (W.exit.subdivide_terminal (8 * N) hsubpos).trans W.exit_terminal,
      physicalProbability_vertex, W.core_terminal]
  have hjoin : S cp = S (.inr 0) := by
    apply hequal
    intro e
    change physicalProbability W.cores (point cp) e = physicalProbability W.cores (X.node 0) e
    rw [hcp, show X.node 0 = W.checkpoint from (W.exit.subdivide_initial (8 * N) hsubpos).trans W.exit_initial]
  have hVle (t : ℕ) : V ≤ f.bufferedOptimum old (Q t) κ := by
    exact f.bufferedOptimum_mono (Finset.empty_subset (Q t))
  have hsmall : V / (4 * N) ≤ V / N := by
    have h : (0 : ℝ) ≤ V / N := div_nonneg hV.le hNr.le
    have he : V / (4 * N) = (V / N) / 4 := by ring
    rw [he]
    linarith
  have htest (i : Fin (3 * N + 2)) : α * f.bufferedOptimum old (Q (W.retained i)) κ - V / N ≤
      f.value (Q (W.retained i) ∪ (D ∪ S cp)) := by
    have h := hval (.inr i)
    simp only [targets, buffers, left, right, Sum.elim, Finset.inter_self] at h
    linarith only [h, hsmall]
  have hrelax (t : ℕ) : (α - 2 / N) * f.bufferedOptimum old (Q t) κ ≤
      α * f.bufferedOptimum old (Q t) κ - V / (4 * N) - V / (4 * N) := by
    have hm := div_le_div_of_nonneg_right (hVle t) hNr.le
    have he : V / (4 * N) = (V / N) / 4 := by ring
    have hf : (0 : ℝ) ≤ f.bufferedOptimum old (Q t) κ / N :=
      div_nonneg (f.bufferedOptimum_nonnegative _ _ _) hNr.le
    rw [he]
    have he2 : (2 / N) * f.bufferedOptimum old (Q t) κ = 2 * (f.bufferedOptimum old (Q t) κ / N) := by ring
    nlinarith only [hm, hf, he2]
  refine ⟨{
    forced := D
    forced_subset := hDU
    forced_card := hDH
    entryPieces := E.pieces
    exitPieces := X.pieces
    entry := fun j => S (.inl j)
    exit := fun j => S (.inr j)
    entry_initial := hE0
    join := hjoin
    exit_terminal := hXT
    entry_subset := fun j => hSU (.inl j)
    exit_subset := fun j => hSU (.inr j)
    entry_card := fun j => hcard (.inl j)
    exit_card := fun j => hcard (.inr j)
    cost := ?_
    entry_first_good := ?_
    exit_first_good := ?_
    entry_intersection := ?_
    exit_intersection := ?_
    checkpoint_tests := htest
  }⟩
  · rw [Fintype.sum_sum_type] at hcost
    simpa only [edgeL, edgeR, Sum.elim, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hcost.le
  · have ht := htest 0
    rw [W.retained_initial] at ht
    have hm := f.monotone _ _ (show Q 0 ∪ initial ⊆ Q 0 ∪ (D ∪ S (.inl 0)) by
      rw [hE0]; intro e he; simp only [Finset.mem_union] at he ⊢; tauto)
    have hopt := W.retained_optimal 0
    rw [W.retained_initial, W.core_initial] at hopt
    rw [hopt] at hm
    have hnonneg := f.bufferedOptimum_nonnegative old (Q 0) κ
    have hcoef : α - 2 / N ≤ 1 := by
      have : (0 : ℝ) ≤ 2 / N := by positivity
      linarith [W.level_le]
    exact (mul_le_of_le_one_left hnonneg hcoef).trans hm
  · have ht := htest (Fin.last (3 * N + 1))
    rw [W.retained_terminal, hjoin] at ht
    have hm := div_le_div_of_nonneg_right (hVle T) hNr.le
    have hf : (0 : ℝ) ≤ f.bufferedOptimum old (Q T) κ / N :=
      div_nonneg (f.bufferedOptimum_nonnegative _ _ _) hNr.le
    have he : (2 / N) * f.bufferedOptimum old (Q T) κ = 2 * (f.bufferedOptimum old (Q T) κ / N) := by ring
    nlinarith only [ht, hm, hf, he]
  · intro j
    exact (hrelax 0).trans (hval (.inl (.inl j)))
  · intro j
    exact (hrelax T).trans (hval (.inl (.inr j)))

end
