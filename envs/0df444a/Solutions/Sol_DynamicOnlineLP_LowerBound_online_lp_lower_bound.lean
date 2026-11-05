-- Prove2me | solution 1 for DynamicOnlineLP.LowerBound.online_lp_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-04T07:31:40.983247+00:00
-- url     : https://prove2.me/submissions/ce9ecee5-d952-4202-812e-fb1db731c2b9

import Mathlib
import Definitions.Def_DynamicOnlineLP_LowerBound_OnlineLP

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! Draft for 4b783f9a (AWY 2014 Theorem 2). Plan: scratch/decomp/4b783f9a.plan.md.
Part K1: structural facts about `decisions` (feasibility, locality). -/

namespace DynamicOnlineLP.LowerBound

section K1
variable {m n : ℕ} (A : OnlineAlgorithm m) (π : Fin n → ℝ) (a : Fin n → Fin m → ℝ)
  (b : Fin m → ℝ) (σ : Equiv.Perm (Fin n))

theorem decisions_zero (s : ℕ) : decisions A π a b σ 0 s = 0 := rfl

theorem decisions_succ (t s : ℕ) :
    decisions A π a b σ (t + 1) s =
      if s < t then decisions A π a b σ t s else if s = t then
        (if 0 ≤ A.propose n b ((List.range (t + 1)).map (arrival π a σ)) ∧
            A.propose n b ((List.range (t + 1)).map (arrival π a σ)) ≤ 1 ∧
            ∀ i : Fin m, ∑ u ∈ Finset.range t, (arrival π a σ u).2 i * decisions A π a b σ t u
              + (arrival π a σ t).2 i * A.propose n b ((List.range (t + 1)).map (arrival π a σ))
              ≤ b i
          then A.propose n b ((List.range (t + 1)).map (arrival π a σ)) else 0) else 0 := rfl

theorem decisions_ge (t s : ℕ) (h : t ≤ s) : decisions A π a b σ t s = 0 := by
  induction t with
  | zero => rfl
  | succ t _ =>
    rw [decisions_succ]
    have h1 : ¬ s < t := by omega
    have h2 : ¬ s = t := by omega
    simp [h1, h2]

theorem decisions_stable (s t : ℕ) (hst : s < t) :
    ∀ T, t ≤ T → decisions A π a b σ T s = decisions A π a b σ t s := by
  intro T hT
  induction T with
  | zero => omega
  | succ T ih =>
    rcases Nat.eq_or_lt_of_le hT with h | h
    · rw [h]
    · have hT' : t ≤ T := by omega
      rw [decisions_succ, if_pos (by omega), ih hT']

/-- Every run of the online algorithm is feasible for the offline problem (by induction on time). -/
theorem decisions_feasible_aux (hb : ∀ i, 0 ≤ b i) : ∀ t,
    (∀ i, ∑ s ∈ Finset.range t, (arrival π a σ s).2 i * decisions A π a b σ t s ≤ b i) ∧
    ∀ s, 0 ≤ decisions A π a b σ t s ∧ decisions A π a b σ t s ≤ 1 := by
  intro t
  induction t with
  | zero => exact ⟨fun i => by simpa using hb i, fun s => by simp [decisions_zero]⟩
  | succ t ih =>
    obtain ⟨ihf, ihb⟩ := ih
    set p := A.propose n b ((List.range (t + 1)).map (arrival π a σ)) with hp
    have hsum : ∀ i, ∑ s ∈ Finset.range (t + 1), (arrival π a σ s).2 i * decisions A π a b σ (t + 1) s
        = ∑ s ∈ Finset.range t, (arrival π a σ s).2 i * decisions A π a b σ t s
          + (arrival π a σ t).2 i * decisions A π a b σ (t + 1) t := by
      intro i
      rw [Finset.sum_range_succ]
      congr 1
      apply Finset.sum_congr rfl
      intro s hs
      rw [Finset.mem_range] at hs
      rw [decisions_succ, if_pos hs]
    have hdt : decisions A π a b σ (t + 1) t =
        if 0 ≤ p ∧ p ≤ 1 ∧ ∀ i : Fin m, ∑ u ∈ Finset.range t,
            (arrival π a σ u).2 i * decisions A π a b σ t u + (arrival π a σ t).2 i * p ≤ b i
        then p else 0 := by
      rw [decisions_succ, if_neg (lt_irrefl t), if_pos rfl]
    refine ⟨fun i => ?_, fun s => ?_⟩
    · rw [hsum i, hdt]
      split_ifs with hc
      · exact hc.2.2 i
      · simpa using ihf i
    · rw [decisions_succ]
      split_ifs with h1 h2 hc
      · exact ihb s
      · exact ⟨hc.1, hc.2.1⟩
      · simp
      · simp

/-- The online run, reindexed by column: column `u` gets the decision made at its arrival time. -/
noncomputable def onlineX : Fin n → ℝ := fun u => decisions A π a b σ n (σ.symm u).val

theorem sum_range_arrival (f : ℕ → ℝ → (Fin m → ℝ) → ℝ) :
    ∑ s ∈ Finset.range n, f s (arrival π a σ s).1 (arrival π a σ s).2
      = ∑ u : Fin n, f (σ.symm u).val (π u) (a u) := by
  rw [← Fin.sum_univ_eq_sum_range (fun s => f s (arrival π a σ s).1 (arrival π a σ s).2)]
  rw [← Equiv.sum_comp σ (fun u => f (σ.symm u).val (π u) (a u))]
  apply Finset.sum_congr rfl
  intro s _
  simp [arrival, s.isLt]

theorem online_feasible (hb : ∀ i, 0 ≤ b i) : IsFeasible a b (onlineX A π a b σ) := by
  obtain ⟨hf, hbd⟩ := decisions_feasible_aux A π a b σ hb n
  refine ⟨fun i => ?_, fun u => hbd _⟩
  have := hf i
  rw [sum_range_arrival π a σ (fun s _ c => c i * decisions A π a b σ n s)] at this
  simpa [onlineX] using this

theorem onlineValue_eq : onlineValue A π a b σ = objective π (onlineX A π a b σ) := by
  unfold onlineValue objective
  rw [sum_range_arrival π a σ (fun s p _ => p * decisions A π a b σ n s)]
  rfl

end K1

/-- Locality: the decisions up to time `T` depend only on the first `T` arrivals. -/
theorem decisions_local {m n : ℕ} (A : OnlineAlgorithm m) (π π' : Fin n → ℝ)
    (a a' : Fin n → Fin m → ℝ) (b : Fin m → ℝ) (σ σ' : Equiv.Perm (Fin n)) (T : ℕ)
    (h : ∀ s < T, arrival π a σ s = arrival π' a' σ' s) :
    ∀ t ≤ T, ∀ s, decisions A π a b σ t s = decisions A π' a' b σ' t s := by
  intro t
  induction t with
  | zero => intro _ s; rfl
  | succ t ih =>
    intro ht s
    have hprev : ∀ s, decisions A π a b σ t s = decisions A π' a' b σ' t s := ih (by omega)
    have hlist : (List.range (t + 1)).map (arrival π a σ)
        = (List.range (t + 1)).map (arrival π' a' σ') := by
      apply List.map_congr_left
      intro s hs
      rw [List.mem_range] at hs
      exact h s (by omega)
    have hat : arrival π a σ t = arrival π' a' σ' t := h t (by omega)
    have hsum : ∀ i, ∑ u ∈ Finset.range t, (arrival π a σ u).2 i * decisions A π a b σ t u
        = ∑ u ∈ Finset.range t, (arrival π' a' σ' u).2 i * decisions A π' a' b σ' t u := by
      intro i
      apply Finset.sum_congr rfl
      intro u hu
      rw [Finset.mem_range] at hu
      rw [h u (by omega), hprev u]
    rw [decisions_succ, decisions_succ, hlist, hat, hprev s]
    simp only [hsum]


/-- Positions per copy: `k` v-columns, `M` mediums, a pool of `2k`. -/
abbrev awyW (k M : ℕ) : ℕ := k + (M + 2 * k)

def awyPos (z k M : ℕ) (t : Fin (z * awyW k M)) : Fin z × Fin (awyW k M) :=
  finProdFinEquiv.symm t

def col (z k M : ℕ) (i : Fin z) (r : Fin (awyW k M)) : Fin (z * awyW k M) :=
  finProdFinEquiv (i, r)

def vA (k M : ℕ) (a : Fin k) : Fin (awyW k M) := Fin.castAdd (M + 2 * k) a
def mA (k M : ℕ) (b : Fin M) : Fin (awyW k M) := Fin.natAdd k (Fin.castAdd (2 * k) b)
def pA (k M : ℕ) (p : Fin (2 * k)) : Fin (awyW k M) := Fin.natAdd k (Fin.natAdd M p)

theorem awyPos_col (z k M : ℕ) (i : Fin z) (r : Fin (awyW k M)) :
    awyPos z k M (col z k M i r) = (i, r) := by
  simp [awyPos, col]

theorem sum_cols (z k M : ℕ) (f : Fin (z * awyW k M) → ℝ) :
    ∑ t, f t = ∑ i : Fin z, ∑ r : Fin (awyW k M), f (col z k M i r) := by
  rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  rfl

theorem sum_pos (k M : ℕ) (g : Fin (awyW k M) → ℝ) :
    ∑ r, g r = ∑ a : Fin k, g (vA k M a) + ∑ b : Fin M, g (mA k M b)
      + ∑ p : Fin (2 * k), g (pA k M p) := by
  rw [Fin.sum_univ_add, Fin.sum_univ_add, add_assoc]
  rfl

@[simp] theorem vA_val (k M : ℕ) (a : Fin k) : (vA k M a).val = a.val := rfl
@[simp] theorem mA_val (k M : ℕ) (b : Fin M) : (mA k M b).val = k + b.val := rfl
@[simp] theorem pA_val (k M : ℕ) (p : Fin (2 * k)) : (pA k M p).val = k + (M + p.val) := rfl

/-- Profits: `v` columns 4, mediums 2, pool 3 if its index lies in `H i`, else 1. -/
def awyπ (z k M : ℕ) (H : Fin z → Finset ℕ) (t : Fin (z * awyW k M)) : ℝ :=
  if (awyPos z k M t).2.val < k then 4
  else if (awyPos z k M t).2.val < k + M then 2
  else if (awyPos z k M t).2.val - (k + M) ∈ H (awyPos z k M t).1 then 3 else 1

/-- Demands: row `j < 2^z` is the bit pattern `finFunctionFinEquiv.symm j`; `v_i` uses the rows
whose bit `i` is 1, every other column of copy `i` the rows whose bit `i` is 0. -/
def awya (z k M m : ℕ) (α : ℝ) (t : Fin (z * awyW k M)) (j : Fin m) : ℝ :=
  if hj : j.val < 2 ^ z then
    if (awyPos z k M t).2.val < k then
      (if (finFunctionFinEquiv.symm ⟨j.val, hj⟩ : Fin z → Fin 2) (awyPos z k M t).1 = 1
        then α else 0)
    else
      (if (finFunctionFinEquiv.symm ⟨j.val, hj⟩ : Fin z → Fin 2) (awyPos z k M t).1 = 0
        then α else 0)
  else 0

theorem π_v (z k M : ℕ) (H : Fin z → Finset ℕ) (i : Fin z) (a : Fin k) :
    awyπ z k M H (col z k M i (vA k M a)) = 4 := by
  simp [awyπ, awyPos_col, a.isLt]

theorem π_m (z k M : ℕ) (H : Fin z → Finset ℕ) (i : Fin z) (b : Fin M) :
    awyπ z k M H (col z k M i (mA k M b)) = 2 := by
  simp [awyπ, awyPos_col, b.isLt]

theorem π_p (z k M : ℕ) (H : Fin z → Finset ℕ) (i : Fin z) (p : Fin (2 * k)) :
    awyπ z k M H (col z k M i (pA k M p)) = if p.val ∈ H i then 3 else 1 := by
  have e : k + (M + p.val) - (k + M) = p.val := by omega
  simp only [awyπ, awyPos_col, pA_val, e]
  rw [if_neg (by omega), if_neg (by omega)]

/-- Load of a row `j < 2^z`. -/
theorem row_load (z k M m : ℕ) (α : ℝ) (x : Fin (z * awyW k M) → ℝ) (j : Fin m)
    (hj : j.val < 2 ^ z) :
    ∑ t, awya z k M m α t j * x t = ∑ i : Fin z, α *
      (if (finFunctionFinEquiv.symm ⟨j.val, hj⟩ : Fin z → Fin 2) i = 1
        then ∑ a : Fin k, x (col z k M i (vA k M a))
        else ∑ b : Fin M, x (col z k M i (mA k M b)) + ∑ p : Fin (2 * k), x (col z k M i (pA k M p))) := by
  rw [sum_cols]
  apply Finset.sum_congr rfl
  intro i _
  rw [sum_pos]
  set β := (finFunctionFinEquiv.symm ⟨j.val, hj⟩ : Fin z → Fin 2)
  have hv : ∀ a : Fin k, awya z k M m α (col z k M i (vA k M a)) j = if β i = 1 then α else 0 := by
    intro a; simp [awya, hj, awyPos_col, a.isLt, β]
  have hm : ∀ b : Fin M, awya z k M m α (col z k M i (mA k M b)) j = if β i = 0 then α else 0 := by
    intro b; simp [awya, hj, awyPos_col, β]
  have hp : ∀ p : Fin (2 * k), awya z k M m α (col z k M i (pA k M p)) j = if β i = 0 then α else 0 := by
    intro p
    simp only [awya, hj, dif_pos, awyPos_col, pA_val]
    rw [if_neg (by omega)]
  simp only [hv, hm, hp]
  rcases Fin.exists_fin_two.mp ⟨β i, rfl⟩ with h | h
  · rw [h]; simp [Finset.mul_sum, mul_add]
  · rw [h]; simp [Finset.mul_sum]

/-- Per-copy optimal value of the non-`v` part (top `k` profits). -/
def awyTop (k M q : ℕ) : ℝ :=
  if k ≤ q then 3 * k else if q + M ≤ k then 2 * q + M + k else 2 * k + q

/-- Per-copy penalty: accepted mediums when `q ≥ k`, rejected mediums when `q + M ≤ k`. -/
def awyD (z k M : ℕ) (H : Fin z → Finset ℕ) (x : Fin (z * awyW k M) → ℝ) (i : Fin z) : ℝ :=
  ∑ b : Fin M, (if k ≤ (H i).card then x (col z k M i (mA k M b))
    else if (H i).card + M ≤ k then 1 - x (col z k M i (mA k M b)) else 0)

theorem awyD_eq (z k M : ℕ) (H : Fin z → Finset ℕ) (x : Fin (z * awyW k M) → ℝ) (i : Fin z) :
    awyD z k M H x i = if k ≤ (H i).card then ∑ b : Fin M, x (col z k M i (mA k M b))
      else if (H i).card + M ≤ k then M - ∑ b : Fin M, x (col z k M i (mA k M b)) else 0 := by
  unfold awyD
  split_ifs <;> simp [Finset.sum_sub_distrib]

theorem count_mem (N : ℕ) (H : Finset ℕ) (hH : H ⊆ Finset.range N) :
    ∑ p : Fin N, (if p.val ∈ H then (1 : ℝ) else 0) = H.card := by
  rw [Fin.sum_univ_eq_sum_range (fun n => if n ∈ H then (1 : ℝ) else 0) N, Finset.sum_boole,
    Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hH]

theorem objective_eq (z k M : ℕ) (H : Fin z → Finset ℕ) (x : Fin (z * awyW k M) → ℝ) :
    objective (awyπ z k M H) x = ∑ i : Fin z, (4 * ∑ a : Fin k, x (col z k M i (vA k M a))
      + 2 * ∑ b : Fin M, x (col z k M i (mA k M b))
      + ∑ p : Fin (2 * k), (if p.val ∈ H i then 3 else 1) * x (col z k M i (pA k M p))) := by
  unfold objective
  rw [sum_cols]
  apply Finset.sum_congr rfl
  intro i _
  rw [sum_pos]
  simp only [π_v, π_m, π_p, Finset.mul_sum]

theorem pool_split (N : ℕ) (H : Finset ℕ) (y : Fin N → ℝ) :
    ∑ p : Fin N, (if p.val ∈ H then (3 : ℝ) else 1) * y p
      = ∑ p, y p + 2 * ∑ p : Fin N, (if p.val ∈ H then y p else 0) := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> ring

/-- Upper bound: every feasible `x` loses at least the medium penalties. -/
theorem K2_ub (z k M m : ℕ) (α : ℝ) (H : Fin z → Finset ℕ) (hα : 0 < α) (h2z : 2 ^ z ≤ m)
    (hH : ∀ i, H i ⊆ Finset.range (2 * k)) (x : Fin (z * awyW k M) → ℝ)
    (hx : IsFeasible (awya z k M m α) (fun _ => α * (z * k)) x) :
    objective (awyπ z k M H) x + ∑ i, awyD z k M H x i ≤ ∑ i : Fin z, (4 * k + awyTop k M (H i).card) := by
  obtain ⟨hrow, hbox⟩ := hx
  set V : Fin z → ℝ := fun i => ∑ a : Fin k, x (col z k M i (vA k M a)) with hV
  set Md : Fin z → ℝ := fun i => ∑ b : Fin M, x (col z k M i (mA k M b)) with hMd
  set Pt : Fin z → ℝ := fun i => ∑ p : Fin (2 * k), x (col z k M i (pA k M p)) with hPt
  set Hx : Fin z → ℝ := fun i => ∑ p : Fin (2 * k), (if p.val ∈ H i then x (col z k M i (pA k M p)) else 0)
    with hHx
  set c : Fin z → ℝ := fun i => max (V i) (Md i + Pt i) with hc
  -- the row whose bits pick the larger side of every copy
  have hsumc : ∑ i, c i ≤ z * k := by
    set β : Fin z → Fin 2 := fun i => if Md i + Pt i ≤ V i then 1 else 0 with hβ
    set j0 := finFunctionFinEquiv β
    have hj : j0.val < 2 ^ z := j0.isLt
    set row : Fin m := ⟨j0.val, lt_of_lt_of_le hj h2z⟩
    have h := hrow row
    rw [row_load z k M m α x row hj] at h
    have hsymm : (finFunctionFinEquiv.symm ⟨row.val, hj⟩ : Fin z → Fin 2) = β := by
      have : (⟨row.val, hj⟩ : Fin (2 ^ z)) = j0 := Fin.ext rfl
      rw [this]; exact finFunctionFinEquiv.symm_apply_apply β
    rw [hsymm] at h
    have hterm : ∀ i, α * (if β i = 1 then ∑ a : Fin k, x (col z k M i (vA k M a))
        else ∑ b : Fin M, x (col z k M i (mA k M b)) + ∑ p : Fin (2 * k), x (col z k M i (pA k M p)))
        = α * c i := by
      intro i
      by_cases hi : Md i + Pt i ≤ V i
      · have : β i = 1 := by simp [hβ, hi]
        rw [this, if_pos rfl]; simp only [hc, hV]; rw [max_eq_left hi]
      · have : β i = 0 := by simp [hβ, hi]
        rw [this, if_neg (by decide)]; simp only [hc, hMd, hPt]
        rw [max_eq_right (le_of_lt (not_le.mp hi))]
    simp only [hterm, ← Finset.mul_sum] at h
    have : α * ∑ i, c i ≤ α * (z * k) := h
    exact le_of_mul_le_mul_left this hα
  have hper : ∀ i, (4 * V i + 2 * Md i + (Pt i + 2 * Hx i)) + awyD z k M H x i
      ≤ awyTop k M (H i).card + 4 * c i := by
    intro i
    have hVk : V i ≤ k := by
      have : V i ≤ ∑ a : Fin k, (1 : ℝ) := Finset.sum_le_sum fun a _ => (hbox _).2
      simpa using this
    have hHq : Hx i ≤ (H i).card := by
      rw [← count_mem (2 * k) (H i) (hH i)]
      apply Finset.sum_le_sum; intro p _
      split_ifs
      · exact (hbox _).2
      · exact le_rfl
    have hHP : Hx i ≤ Pt i := by
      apply Finset.sum_le_sum; intro p _
      split_ifs
      · exact le_rfl
      · exact (hbox _).1
    have hMd0 : 0 ≤ Md i := Finset.sum_nonneg fun b _ => (hbox _).1
    have hc1 : V i ≤ c i := le_max_left _ _
    have hc2 : Md i + Pt i ≤ c i := le_max_right _ _
    rw [awyD_eq]
    unfold awyTop
    have hq : ((H i).card : ℝ) = ((H i).card : ℕ) := rfl
    split_ifs with h1 h2
    · have : (k : ℝ) ≤ (H i).card := by exact_mod_cast h1
      simp only [hMd] at hMd0 ⊢
      linarith
    · have : ((H i).card : ℝ) + M ≤ k := by exact_mod_cast h2
      simp only [hMd] at hMd0 ⊢
      linarith
    · have : ((H i).card : ℝ) < k := by exact_mod_cast (not_le.mp h1)
      linarith
  have hobj := objective_eq z k M H x
  simp only [pool_split] at hobj
  rw [hobj, ← Finset.sum_add_distrib]
  calc ∑ i, (4 * V i + 2 * Md i + (Pt i + 2 * Hx i) + awyD z k M H x i)
      ≤ ∑ i, (awyTop k M (H i).card + 4 * c i) := Finset.sum_le_sum fun i _ => hper i
    _ = ∑ i, awyTop k M (H i).card + 4 * ∑ i, c i := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ ∑ i, awyTop k M (H i).card + 4 * (z * k) := by linarith
    _ = ∑ i : Fin z, (4 * k + awyTop k M (H i).card) := by
        rw [Finset.sum_add_distrib]; simp; ring

noncomputable def mvS (k M q : ℕ) : ℝ := if k ≤ q then 0 else if q + M ≤ k then 1 else ((k : ℝ) - q) / M
noncomputable def hvS (k q : ℕ) : ℝ := if k ≤ q then (k : ℝ) / q else 1
noncomputable def lvS (k M q : ℕ) : ℝ :=
  if k ≤ q then 0 else if q + M ≤ k then ((k : ℝ) - q - M) / (2 * k - q) else 0

/-- The explicit optimal primal: all `v` columns, then the top `k` units of the rest. -/
noncomputable def xS (z k M : ℕ) (H : Fin z → Finset ℕ) (t : Fin (z * awyW k M)) : ℝ :=
  if (awyPos z k M t).2.val < k then 1
  else if (awyPos z k M t).2.val < k + M then mvS k M (H (awyPos z k M t).1).card
  else if (awyPos z k M t).2.val - (k + M) ∈ H (awyPos z k M t).1 then hvS k (H (awyPos z k M t).1).card
  else lvS k M (H (awyPos z k M t).1).card

theorem xS_v (z k M : ℕ) (H : Fin z → Finset ℕ) (i : Fin z) (a : Fin k) :
    xS z k M H (col z k M i (vA k M a)) = 1 := by simp [xS, awyPos_col, a.isLt]
theorem xS_m (z k M : ℕ) (H : Fin z → Finset ℕ) (i : Fin z) (b : Fin M) :
    xS z k M H (col z k M i (mA k M b)) = mvS k M (H i).card := by simp [xS, awyPos_col, b.isLt]
theorem xS_p (z k M : ℕ) (H : Fin z → Finset ℕ) (i : Fin z) (p : Fin (2 * k)) :
    xS z k M H (col z k M i (pA k M p)) = if p.val ∈ H i then hvS k (H i).card else lvS k M (H i).card := by
  have e : k + (M + p.val) - (k + M) = p.val := by omega
  simp only [xS, awyPos_col, pA_val, e]
  rw [if_neg (by omega), if_neg (by omega)]

theorem pool_count (N : ℕ) (H : Finset ℕ) (hH : H ⊆ Finset.range N) (u w : ℝ) :
    ∑ p : Fin N, (if p.val ∈ H then u else w) = H.card * u + (N - H.card) * w := by
  have : ∀ p : Fin N, (if p.val ∈ H then u else w) = w + (u - w) * (if p.val ∈ H then (1 : ℝ) else 0) := by
    intro p; split_ifs <;> ring
  simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, count_mem N H hH]
  simp; ring

theorem xS_case (k M q : ℕ) (hk : 1 ≤ k) (hq : q ≤ 2 * k) :
    (0 ≤ mvS k M q ∧ mvS k M q ≤ 1) ∧ (0 ≤ hvS k q ∧ hvS k q ≤ 1) ∧ (0 ≤ lvS k M q ∧ lvS k M q ≤ 1) ∧
    M * mvS k M q + (q * hvS k q + (2 * k - q) * lvS k M q) = k ∧
    2 * (M * mvS k M q) + (q * (3 * hvS k q) + (2 * k - q) * lvS k M q) = awyTop k M q := by
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hqr : (q : ℝ) ≤ 2 * k := by exact_mod_cast hq
  unfold mvS hvS lvS awyTop
  split_ifs with h1 h2
  · have h1r : (k : ℝ) ≤ q := by exact_mod_cast h1
    have hq0 : (0 : ℝ) < q := by linarith
    refine ⟨⟨le_rfl, by norm_num⟩, ⟨by positivity, (div_le_one hq0).mpr h1r⟩, ⟨le_rfl, by norm_num⟩, ?_, ?_⟩
    · field_simp; ring
    · field_simp; ring
  · have h2r : (q : ℝ) + M ≤ k := by exact_mod_cast h2
    have h1r : (q : ℝ) < k := by exact_mod_cast (not_le.mp h1)
    have hd : (0 : ℝ) < 2 * k - q := by linarith
    refine ⟨⟨by norm_num, le_rfl⟩, ⟨by norm_num, le_rfl⟩, ⟨div_nonneg (by linarith) hd.le,
      (div_le_one hd).mpr (by linarith)⟩, ?_, ?_⟩
    · field_simp; ring
    · field_simp; ring
  · have h2r : (k : ℝ) < q + M := by exact_mod_cast (not_le.mp h2)
    have h1r : (q : ℝ) < k := by exact_mod_cast (not_le.mp h1)
    have hM : (0 : ℝ) < M := by linarith [(Nat.cast_nonneg q : (0 : ℝ) ≤ q)]
    refine ⟨⟨div_nonneg (by linarith) hM.le, (div_le_one hM).mpr (by linarith)⟩, ⟨by norm_num, le_rfl⟩,
      ⟨le_rfl, by norm_num⟩, ?_, ?_⟩
    · field_simp; ring
    · field_simp; ring

theorem xS_feasible (z k M m : ℕ) (α : ℝ) (H : Fin z → Finset ℕ) (hk : 1 ≤ k) (hα : 0 < α)
    (hH : ∀ i, H i ⊆ Finset.range (2 * k)) :
    IsFeasible (awya z k M m α) (fun _ => α * (z * k)) (xS z k M H) := by
  have hqc : ∀ i, (H i).card ≤ 2 * k := fun i => by
    simpa using Finset.card_le_card (hH i)
  refine ⟨fun j => ?_, fun t => ?_⟩
  · by_cases hj : j.val < 2 ^ z
    · rw [row_load z k M m α _ j hj]
      have hterm : ∀ i : Fin z, α * (if (finFunctionFinEquiv.symm ⟨j.val, hj⟩ : Fin z → Fin 2) i = 1
          then ∑ a : Fin k, xS z k M H (col z k M i (vA k M a))
          else ∑ b : Fin M, xS z k M H (col z k M i (mA k M b))
            + ∑ p : Fin (2 * k), xS z k M H (col z k M i (pA k M p))) = α * k := by
        intro i
        simp only [xS_v, xS_m, xS_p, pool_count (2 * k) (H i) (hH i)]
        have := (xS_case k M (H i).card hk (hqc i)).2.2.2.1
        split_ifs
        · simp
        · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          rw [this]
      rw [Finset.sum_congr rfl (fun i _ => hterm i)]
      simp; ring_nf; exact le_rfl
    · have : ∀ t, awya z k M m α t j = 0 := fun t => by simp [awya, hj]
      simp only [this, zero_mul, Finset.sum_const_zero]
      positivity
  · have hc := xS_case k M (H (awyPos z k M t).1).card hk (hqc _)
    unfold xS
    split_ifs
    · norm_num
    · exact hc.1
    · exact hc.2.1
    · exact hc.2.2.1

theorem xS_objective (z k M : ℕ) (H : Fin z → Finset ℕ) (hk : 1 ≤ k)
    (hH : ∀ i, H i ⊆ Finset.range (2 * k)) :
    objective (awyπ z k M H) (xS z k M H) = ∑ i : Fin z, (4 * k + awyTop k M (H i).card) := by
  have hqc : ∀ i, (H i).card ≤ 2 * k := fun i => by
    simpa using Finset.card_le_card (hH i)
  rw [objective_eq]
  apply Finset.sum_congr rfl
  intro i _
  simp only [xS_v, xS_m, xS_p]
  have hp : ∀ p : Fin (2 * k), (if p.val ∈ H i then (3 : ℝ) else 1) *
      (if p.val ∈ H i then hvS k (H i).card else lvS k M (H i).card)
      = if p.val ∈ H i then 3 * hvS k (H i).card else lvS k M (H i).card := by
    intro p; split_ifs <;> ring
  simp only [hp, pool_count (2 * k) (H i) (hH i)]
  have := (xS_case k M (H i).card hk (hqc i)).2.2.2.2
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  push_cast
  linarith

theorem awyD_nonneg (z k M : ℕ) (H : Fin z → Finset ℕ) (x : Fin (z * awyW k M) → ℝ)
    (hx : ∀ t, 0 ≤ x t ∧ x t ≤ 1) (i : Fin z) : 0 ≤ awyD z k M H x i := by
  unfold awyD
  apply Finset.sum_nonneg; intro b _
  split_ifs
  · exact (hx _).1
  · linarith [(hx (col z k M i (mA k M b))).2]
  · exact le_rfl

theorem awyTop_le (k M q : ℕ) : awyTop k M q ≤ 3 * k := by
  unfold awyTop
  split_ifs with h1 h2
  · exact le_rfl
  · have : (q : ℝ) + M ≤ k := by exact_mod_cast h2
    have : (q : ℝ) ≤ k := by linarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
    linarith
  · have : (q : ℝ) < k := by exact_mod_cast (not_le.mp h1)
    linarith

/-- K2: the exact LP bound for the AWY instance. -/
theorem K2 (z k M m : ℕ) (α : ℝ) (H : Fin z → Finset ℕ) (hk : 1 ≤ k) (hα : 0 < α)
    (h2z : 2 ^ z ≤ m) (hH : ∀ i, H i ⊆ Finset.range (2 * k)) :
    (OPT (awyπ z k M H) (awya z k M m α) (fun _ => α * (z * k)) ≤ 7 * z * k) ∧
    (∑ i, (4 * k + awyTop k M (H i).card) ≤
      OPT (awyπ z k M H) (awya z k M m α) (fun _ => α * (z * k))) ∧
    ∀ x, IsFeasible (awya z k M m α) (fun _ => α * (z * k)) x →
      objective (awyπ z k M H) x + ∑ i, awyD z k M H x i ≤ ∑ i, (4 * k + awyTop k M (H i).card) := by
  have hub := K2_ub z k M m α H hα h2z hH
  have hobj : ∀ x, IsFeasible (awya z k M m α) (fun _ => α * (z * k)) x →
      objective (awyπ z k M H) x ≤ ∑ i : Fin z, (4 * k + awyTop k M (H i).card) := by
    intro x hx
    have := hub x hx
    have : 0 ≤ ∑ i, awyD z k M H x i := Finset.sum_nonneg fun i _ => awyD_nonneg z k M H x hx.2 i
    linarith
  have hsum7 : ∑ i : Fin z, (4 * (k : ℝ) + awyTop k M (H i).card) ≤ 7 * z * k := by
    have : ∑ i : Fin z, (4 * (k : ℝ) + awyTop k M (H i).card) ≤ ∑ i : Fin z, (7 * (k : ℝ)) :=
      Finset.sum_le_sum fun i _ => by linarith [awyTop_le k M (H i).card]
    simp at this; linarith
  have hfeas := xS_feasible z k M m α H hk hα hH
  have hbdd : BddAbove (objective (awyπ z k M H) '' {x | IsFeasible (awya z k M m α) (fun _ => α * (z * k)) x}) := by
    refine ⟨∑ i : Fin z, (4 * k + awyTop k M (H i).card), ?_⟩
    rintro y ⟨x, hx, rfl⟩
    exact hobj x hx
  refine ⟨?_, ?_, hub⟩
  · unfold OPT
    apply csSup_le (Set.Nonempty.image _ ⟨xS z k M H, hfeas⟩)
    rintro y ⟨x, hx, rfl⟩
    exact (hobj x hx).trans hsum7
  · unfold OPT
    rw [← xS_objective z k M H hk hH]
    exact le_csSup hbdd ⟨xS z k M H, hfeas, rfl⟩


/-- K3' (labelling split over a ground set `U ⊇ P`). -/
theorem K3' {α : Type} [DecidableEq α] (U P : Finset α) (f : Finset α → ℝ) (g : ℕ → ℝ)
    (hPU : P ⊆ U) (hf : ∀ G, f G = f (G ∩ P)) :
    ∑ G ∈ U.powerset, f G * g G.card
      = ∑ A ∈ P.powerset, f A * ∑ C ∈ (U \ P).powerset, g (A.card + C.card) := by
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_product']
  symm
  apply Finset.sum_bij' (fun x _ => x.1 ∪ x.2) (fun G _ => (G ∩ P, G \ P))
  · intro x hx
    simp only [Finset.mem_product, Finset.mem_powerset] at hx ⊢
    exact Finset.union_subset (hx.1.trans hPU) (hx.2.trans Finset.sdiff_subset)
  · intro G hG
    simp only [Finset.mem_product, Finset.mem_powerset] at hG ⊢
    exact ⟨Finset.inter_subset_right, Finset.sdiff_subset_sdiff hG le_rfl⟩
  · intro x hx
    simp only [Finset.mem_product, Finset.mem_powerset] at hx
    obtain ⟨h1, h2⟩ := hx
    ext y
    · simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨hy | hy, hyP⟩
        · exact hy
        · exact absurd hyP (Finset.mem_sdiff.mp (h2 hy)).2
      · intro hy; exact ⟨Or.inl hy, h1 hy⟩
    · simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨hy | hy, hyP⟩
        · exact absurd (h1 hy) hyP
        · exact hy
      · intro hy; exact ⟨Or.inr hy, (Finset.mem_sdiff.mp (h2 hy)).2⟩
  · intro G _
    ext y
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  · intro x hx
    simp only [Finset.mem_product, Finset.mem_powerset] at hx
    obtain ⟨h1, h2⟩ := hx
    have hdisj : Disjoint x.1 x.2 := by
      rw [Finset.disjoint_left]
      intro y hy1 hy2
      exact (Finset.mem_sdiff.mp (h2 hy2)).2 (h1 hy1)
    have hint : (x.1 ∪ x.2) ∩ P = x.1 := by
      ext y
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨hy | hy, hyP⟩
        · exact hy
        · exact absurd hyP (Finset.mem_sdiff.mp (h2 hy)).2
      · intro hy; exact ⟨Or.inl hy, h1 hy⟩
    rw [Finset.card_union_of_disjoint hdisj, hf (x.1 ∪ x.2), hint]


theorem pascal_sum (R : ℕ) (f : ℕ → ℝ) :
    ∑ c ∈ Finset.range (R + 2), (Nat.choose (R + 1) c : ℝ) * f c
      = ∑ c ∈ Finset.range (R + 1), (Nat.choose R c : ℝ) * (f c + f (c + 1)) := by
  rw [Finset.sum_range_succ']
  simp only [Nat.choose_succ_succ, Nat.cast_add, add_mul, Finset.sum_add_distrib, mul_add]
  have h1 : ∑ c ∈ Finset.range (R + 1), (Nat.choose R (c + 1) : ℝ) * f (c + 1)
      = ∑ c ∈ Finset.range (R + 1), (Nat.choose R c : ℝ) * f c - f 0 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ' (fun c => (Nat.choose R c : ℝ) * f c)]
    simp only [Nat.choose_succ_self, Nat.choose_zero_right, Nat.cast_zero, Nat.cast_one,
      zero_mul, one_mul, add_zero]
    ring
  rw [h1]
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul]
  ring

/-- Centered moments `∑ C(R,c) (2c-R)^p`. -/
noncomputable def bmom (p R : ℕ) : ℝ :=
  ∑ c ∈ Finset.range (R + 1), (Nat.choose R c : ℝ) * ((2 * c - R : ℝ)) ^ p

theorem bmom_succ (p R : ℕ) :
    bmom p (R + 1) = ∑ c ∈ Finset.range (R + 1), (Nat.choose R c : ℝ) *
      (((2 * c - R : ℝ) - 1) ^ p + ((2 * c - R : ℝ) + 1) ^ p) := by
  unfold bmom
  rw [pascal_sum R (fun c => ((2 * c - (R + 1 : ℕ) : ℝ)) ^ p)]
  apply Finset.sum_congr rfl
  intro c _
  push_cast
  ring_nf

theorem bmom_zero (R : ℕ) : bmom 0 R = 2 ^ R := by
  unfold bmom
  simp only [pow_zero, mul_one]
  exact_mod_cast Nat.sum_range_choose R

theorem bmom_two (R : ℕ) : bmom 2 R = R * 2 ^ R := by
  induction R with
  | zero => simp [bmom]
  | succ R ih =>
    rw [bmom_succ]
    have : ∀ c ∈ Finset.range (R + 1), (Nat.choose R c : ℝ) *
        (((2 * c - R : ℝ) - 1) ^ 2 + ((2 * c - R : ℝ) + 1) ^ 2)
        = 2 * ((Nat.choose R c : ℝ) * ((2 * c - R : ℝ)) ^ 2) + 2 * ((Nat.choose R c : ℝ) * 1) := by
      intro c _; ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have h0 := bmom_zero R
    unfold bmom at ih h0
    simp only [pow_zero] at h0
    rw [ih, h0]
    push_cast
    ring

theorem bmom_four (R : ℕ) : bmom 4 R = (3 * R ^ 2 - 2 * R) * 2 ^ R := by
  induction R with
  | zero => simp [bmom]
  | succ R ih =>
    rw [bmom_succ]
    have : ∀ c ∈ Finset.range (R + 1), (Nat.choose R c : ℝ) *
        (((2 * c - R : ℝ) - 1) ^ 4 + ((2 * c - R : ℝ) + 1) ^ 4)
        = 2 * ((Nat.choose R c : ℝ) * ((2 * c - R : ℝ)) ^ 4)
          + 12 * ((Nat.choose R c : ℝ) * ((2 * c - R : ℝ)) ^ 2)
          + 2 * ((Nat.choose R c : ℝ) * ((2 * c - R : ℝ)) ^ 0) := by
      intro c _; ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    have h0 := bmom_zero R
    have h2 := bmom_two R
    unfold bmom at ih h0 h2
    rw [ih, h0, h2]
    push_cast
    ring

/-- Pointwise truncation inequality behind the fourth-moment anti-concentration. -/
theorem trunc_pt (R y : ℝ) (hR : 0 < R) :
    y ^ 2 ≤ R / 4 + 8 * R * (if R / 4 < y ^ 2 then 1 else 0) + y ^ 4 / (8 * R) := by
  have h8 : 0 < 8 * R := by linarith
  have key : 8 * R * y ^ 2 ≤ 2 * R ^ 2 + 64 * R ^ 2 + y ^ 4 := by
    nlinarith [sq_nonneg (y ^ 2 - 4 * R), sq_nonneg R]
  split_ifs with h
  · have h' : (8 * R * y ^ 2 - 66 * R ^ 2) / (8 * R) ≤ y ^ 4 / (8 * R) :=
      div_le_div_of_nonneg_right (by linarith) h8.le
    have e : (8 * R * y ^ 2 - 66 * R ^ 2) / (8 * R) = y ^ 2 - 66 * R / 8 := by
      field_simp
    linarith
  · have : y ^ 4 / (8 * R) ≥ 0 := by positivity
    linarith

/-- At least `3/64` of the subsets have `(2c-R)^2 > R/4`. -/
theorem big_dev (R : ℕ) (hR : 1 ≤ R) :
    (3 / 64 : ℝ) * 2 ^ R ≤ ∑ c ∈ Finset.range (R + 1),
      if (R : ℝ) / 4 < ((2 * c - R : ℝ)) ^ 2 then (Nat.choose R c : ℝ) else 0 := by
  have hRr : (0 : ℝ) < R := by exact_mod_cast hR
  have hpt : ∀ c ∈ Finset.range (R + 1), (Nat.choose R c : ℝ) * ((2 * c - R : ℝ)) ^ 2 ≤
      (R / 4) * ((Nat.choose R c : ℝ) * ((2 * c - R : ℝ)) ^ 0)
        + 8 * R * (if (R : ℝ) / 4 < ((2 * c - R : ℝ)) ^ 2 then (Nat.choose R c : ℝ) else 0)
        + ((Nat.choose R c : ℝ) * ((2 * c - R : ℝ)) ^ 4) / (8 * R) := by
    intro c _
    have hC : (0 : ℝ) ≤ Nat.choose R c := Nat.cast_nonneg _
    have := mul_le_mul_of_nonneg_left (trunc_pt R (2 * c - R) hRr) hC
    have e : (if (R : ℝ) / 4 < ((2 * c - R : ℝ)) ^ 2 then (Nat.choose R c : ℝ) else 0)
        = (Nat.choose R c : ℝ) * (if (R : ℝ) / 4 < ((2 * c - R : ℝ)) ^ 2 then 1 else 0) := by
      split_ifs <;> simp
    rw [e]
    calc _ ≤ _ := this
      _ = _ := by ring
  have hs := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.sum_div] at hs
  have e2 := bmom_two R
  have e4 := bmom_four R
  have e0 := bmom_zero R
  unfold bmom at e2 e4 e0
  rw [e2, e4, e0] at hs
  set S := ∑ c ∈ Finset.range (R + 1),
      if (R : ℝ) / 4 < ((2 * c - R : ℝ)) ^ 2 then (Nat.choose R c : ℝ) else 0
  have hW : (0 : ℝ) < 2 ^ R := by positivity
  have hq : (3 * (R : ℝ) ^ 2 - 2 * R) * 2 ^ R / (8 * R) ≤ 3 * R / 8 * 2 ^ R := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have : (3 / 8 : ℝ) * R * 2 ^ R ≤ 8 * R * S := by nlinarith
  nlinarith

/-- Reflection `c ↦ R - c` swaps the signs of `2c - R`. -/
theorem refl_sum (R : ℕ) (P : ℝ → Prop) [DecidablePred P] :
    ∑ c ∈ Finset.range (R + 1), (if P (2 * c - R : ℝ) then (Nat.choose R c : ℝ) else 0)
      = ∑ c ∈ Finset.range (R + 1), (if P (-(2 * c - R : ℝ)) then (Nat.choose R c : ℝ) else 0) := by
  rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro c hc
  rw [Finset.mem_range] at hc
  have hle : c ≤ R := by omega
  have e1 : R + 1 - 1 - c = R - c := by omega
  rw [e1, Nat.choose_symm hle, Nat.cast_sub hle]
  congr 2
  ring

theorem side_dev (R : ℕ) (hR : 1 ≤ R) :
    (3 / 128 : ℝ) * 2 ^ R ≤ (∑ c ∈ Finset.range (R + 1),
      if 0 < (2 * c - R : ℝ) ∧ (R : ℝ) / 4 < ((2 * c - R : ℝ)) ^ 2
        then (Nat.choose R c : ℝ) else 0) ∧
    (3 / 128 : ℝ) * 2 ^ R ≤ (∑ c ∈ Finset.range (R + 1),
      if (2 * c - R : ℝ) < 0 ∧ (R : ℝ) / 4 < ((2 * c - R : ℝ)) ^ 2
        then (Nat.choose R c : ℝ) else 0) := by
  have hRr : (0 : ℝ) < R := by exact_mod_cast hR
  have hb := big_dev R hR
  have hsplit : ∀ c ∈ Finset.range (R + 1),
      (if (R : ℝ) / 4 < ((2 * c - R : ℝ)) ^ 2 then (Nat.choose R c : ℝ) else 0)
        = (if 0 < (2 * c - R : ℝ) ∧ (R : ℝ) / 4 < ((2 * c - R : ℝ)) ^ 2
            then (Nat.choose R c : ℝ) else 0)
          + (if (2 * c - R : ℝ) < 0 ∧ (R : ℝ) / 4 < ((2 * c - R : ℝ)) ^ 2
            then (Nat.choose R c : ℝ) else 0) := by
    intro c _
    by_cases h : (R : ℝ) / 4 < ((2 * c - R : ℝ)) ^ 2
    · have hne : (2 * c - R : ℝ) ≠ 0 := by
        intro h0; rw [h0] at h; nlinarith
      rcases lt_or_gt_of_ne hne with hl | hl
      · simp [h, hl, not_lt.mpr hl.le]
      · simp [h, hl, not_lt.mpr hl.le]
    · simp [h]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib] at hb
  have hr := refl_sum R (fun y => 0 < y ∧ (R : ℝ) / 4 < y ^ 2)
  simp only [neg_pos, neg_sq] at hr
  rw [hr] at hb ⊢
  constructor <;> linarith

/-- Chebyshev on the seen labels: at least `3/4` of them have `(2h-j)^2 ≤ 4j`. -/
theorem cheb_seen (j : ℕ) :
    (3 / 4 : ℝ) * 2 ^ j ≤ ∑ h ∈ Finset.range (j + 1),
      if ((2 * h - j : ℝ)) ^ 2 ≤ 4 * j then (Nat.choose j h : ℝ) else 0 := by
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj; simp <;> norm_num
  have hjr : (0 : ℝ) < j := by exact_mod_cast hj
  have hpt : ∀ h ∈ Finset.range (j + 1), 4 * j * ((Nat.choose j h : ℝ) * ((2 * h - j : ℝ)) ^ 0) ≤
      4 * j * (if ((2 * h - j : ℝ)) ^ 2 ≤ 4 * j then (Nat.choose j h : ℝ) else 0)
        + (Nat.choose j h : ℝ) * ((2 * h - j : ℝ)) ^ 2 := by
    intro h _
    have hC : (0 : ℝ) ≤ Nat.choose j h := Nat.cast_nonneg _
    split_ifs with hc
    · simp only [pow_zero, mul_one]
      have : 0 ≤ (Nat.choose j h : ℝ) * ((2 * h - j : ℝ)) ^ 2 := by positivity
      linarith
    · push Not at hc
      simp only [pow_zero, mul_one, mul_zero, zero_add]
      nlinarith
  have hs := Finset.sum_le_sum hpt
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  have e2 := bmom_two j
  have e0 := bmom_zero j
  unfold bmom at e2 e0
  rw [e2, e0] at hs
  nlinarith

/-- K4 (revised): binomial overlap with a small seen part. -/
theorem K4new (k M j : ℕ) (hk : 1 ≤ k) (hM : 64 * M ^ 2 ≤ k) (hj : 64 * j ≤ k) :
    (9 / 512 : ℝ) * 2 ^ (2 * k) ≤ ∑ h ∈ Finset.range (j + 1), (Nat.choose j h : ℝ) *
      min (∑ c ∈ Finset.range (2 * k - j + 1),
              if k ≤ h + c then (Nat.choose (2 * k - j) c : ℝ) else 0)
          (∑ c ∈ Finset.range (2 * k - j + 1),
              if h + c + M ≤ k then (Nat.choose (2 * k - j) c : ℝ) else 0) := by
  set R := 2 * k - j with hRdef
  have hR1 : 1 ≤ R := by omega
  have hRk : k ≤ R := by omega
  have hjk : j ≤ 2 * k := by omega
  have hRc : (R : ℝ) = 2 * k - j := by rw [hRdef, Nat.cast_sub hjk]; push_cast; ring
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hMr : 64 * (M : ℝ) ^ 2 ≤ k := by exact_mod_cast hM
  have hjr : 64 * (j : ℝ) ≤ k := by exact_mod_cast hj
  have hRkr : (k : ℝ) ≤ R := by exact_mod_cast hRk
  obtain ⟨hpos, hneg⟩ := side_dev R hR1
  have hW : (0 : ℝ) ≤ 2 ^ R := by positivity
  have hpt : ∀ h ∈ Finset.range (j + 1),
      (if ((2 * h - j : ℝ)) ^ 2 ≤ 4 * j then (Nat.choose j h : ℝ) else 0) * ((3 / 128) * 2 ^ R)
        ≤ (Nat.choose j h : ℝ) *
      min (∑ c ∈ Finset.range (R + 1),
              if k ≤ h + c then (Nat.choose R c : ℝ) else 0)
          (∑ c ∈ Finset.range (R + 1),
              if h + c + M ≤ k then (Nat.choose R c : ℝ) else 0) := by
    intro h _
    have hC : (0 : ℝ) ≤ Nat.choose j h := Nat.cast_nonneg _
    split_ifs with hty
    · apply mul_le_mul_of_nonneg_left _ hC
      apply le_min
      · refine hpos.trans (Finset.sum_le_sum fun c _ => ?_)
        split_ifs with h1 h2
        · exact le_rfl
        · exfalso; apply h2
          have hy : |(2 * h - j : ℝ)| < 2 * c - R := by
            apply abs_lt_of_sq_lt_sq _ h1.1.le
            nlinarith
          have := neg_abs_le (2 * h - j : ℝ)
          have : (k : ℝ) ≤ h + c := by linarith
          exact_mod_cast this
        · exact Nat.cast_nonneg _
        · exact le_rfl
      · refine hneg.trans (Finset.sum_le_sum fun c _ => ?_)
        split_ifs with h1 h2
        · exact le_rfl
        · exfalso; apply h2
          have hsq : (|(2 * h - j : ℝ)| + 2 * M) ^ 2 ≤ 2 * (2 * h - j : ℝ) ^ 2 + 8 * (M : ℝ) ^ 2 := by
            nlinarith [sq_nonneg (|(2 * h - j : ℝ)| - 2 * M), sq_abs (2 * h - j : ℝ)]
          have hy : |(|(2 * h - j : ℝ)| + 2 * M)| < -(2 * c - R : ℝ) := by
            apply abs_lt_of_sq_lt_sq _ (by linarith [h1.1])
            nlinarith [h1.2]
          have h3 := le_abs_self (|(2 * h - j : ℝ)| + 2 * M)
          have h4 := le_abs_self (2 * h - j : ℝ)
          have : (h : ℝ) + c + M ≤ k := by linarith
          exact_mod_cast this
        · exact Nat.cast_nonneg _
        · exact le_rfl
    · rw [zero_mul]
      apply mul_nonneg hC
      apply le_min <;> exact Finset.sum_nonneg fun c _ => by split_ifs <;> simp
  have hs := Finset.sum_le_sum hpt
  rw [← Finset.sum_mul] at hs
  have hc := cheb_seen j
  have h2k : (2 : ℝ) ^ (2 * k) = 2 ^ j * 2 ^ R := by
    rw [← pow_add]; congr 1; omega
  rw [h2k]
  have : (3 / 4 : ℝ) * 2 ^ j * ((3 / 128) * 2 ^ R) ≤ _ * ((3 / 128) * 2 ^ R) :=
    mul_le_mul_of_nonneg_right hc (by positivity)
  nlinarith



/-- Rank of `w` inside `Q` under the arrival order `σ`. -/
def rk {n : ℕ} (Q : Finset (Fin n)) (σ : Equiv.Perm (Fin n)) (w : Fin n) : ℕ :=
  (Q.filter (fun v => σ.symm v < σ.symm w)).card

theorem rk_swap {n : ℕ} (Q : Finset (Fin n)) (t u : Fin n) (ht : t ∈ Q) (hu : u ∈ Q)
    (σ : Equiv.Perm (Fin n)) : rk Q (Equiv.swap t u * σ) t = rk Q σ u := by
  unfold rk
  have hτ : ∀ v, v ∈ Q → Equiv.swap t u v ∈ Q := by
    intro v hv
    rw [Equiv.swap_apply_def]
    split_ifs <;> assumption
  apply Finset.card_nbij' (Equiv.swap t u) (Equiv.swap t u)
  · intro v hv
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hv ⊢
    refine ⟨hτ v hv.1, ?_⟩
    have := hv.2
    simp only [Equiv.Perm.mul_def, Equiv.symm_trans_apply, Equiv.symm_swap,
      Equiv.swap_apply_left] at this
    exact this
  · intro v hv
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hv ⊢
    refine ⟨hτ v hv.1, ?_⟩
    simp only [Equiv.Perm.mul_def, Equiv.symm_trans_apply, Equiv.symm_swap,
      Equiv.swap_apply_left, Equiv.swap_apply_self]
    exact hv.2
  · intro v _; simp
  · intro v _; simp

theorem sum_rk_swap {n : ℕ} (Q : Finset (Fin n)) (t u : Fin n) (ht : t ∈ Q) (hu : u ∈ Q)
    (f : ℕ → ℕ) : ∑ σ : Equiv.Perm (Fin n), f (rk Q σ t) = ∑ σ : Equiv.Perm (Fin n), f (rk Q σ u) := by
  rw [← Equiv.sum_comp (Equiv.mulLeft (Equiv.swap t u))]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Equiv.coe_mulLeft]
  exact congrArg f (rk_swap Q t u ht hu σ)

theorem rk_injOn {n : ℕ} (Q : Finset (Fin n)) (σ : Equiv.Perm (Fin n)) :
    Set.InjOn (rk Q σ) Q := by
  have key : ∀ u v, u ∈ Q → v ∈ Q → σ.symm u < σ.symm v → rk Q σ u < rk Q σ v := by
    intro u v hu hv huv
    unfold rk
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨u, ?_, ?_⟩
      · simp [hu, huv]
      · simp
    · intro w hw
      simp only [Finset.mem_filter] at hw ⊢
      exact ⟨hw.1, hw.2.trans huv⟩
  intro u hu v hv h
  by_contra hne
  have hne' : σ.symm u ≠ σ.symm v := fun e => hne (σ.symm.injective e)
  rcases lt_or_gt_of_ne hne' with hl | hl
  · exact absurd h (key u v hu hv hl).ne
  · exact absurd h (key v u hv hu hl).ne'

theorem rk_lt {n : ℕ} (Q : Finset (Fin n)) (σ : Equiv.Perm (Fin n)) (u : Fin n) (hu : u ∈ Q) :
    rk Q σ u < Q.card := by
  unfold rk
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
  exact ⟨u, hu, by simp⟩

theorem count_rk_le {n : ℕ} (Q : Finset (Fin n)) (σ : Equiv.Perm (Fin n)) (r : ℕ)
    (hr : r < Q.card) : r + 1 ≤ (Q.filter (fun u => rk Q σ u ≤ r)).card := by
  have himg : Q.image (rk Q σ) = Finset.range Q.card := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hy
      exact Finset.mem_range.mpr (rk_lt Q σ u hu)
    · rw [Finset.card_image_of_injOn (rk_injOn Q σ), Finset.card_range]
  have := Finset.card_le_card_of_surjOn (rk Q σ) (s := Q.filter (fun u => rk Q σ u ≤ r))
    (t := Finset.range (r + 1)) (by
      intro y hy
      have hy' : y ∈ Q.image (rk Q σ) := by
        rw [himg]; simp only [Finset.coe_range, Set.mem_Iio] at hy; exact Finset.mem_range.mpr (by omega)
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hy'
      simp only [Finset.coe_range, Set.mem_Iio] at hy
      exact ⟨u, by simp [hu]; omega, rfl⟩)
  simpa using this

/-- K5b (rank uniformity, lower half): at least a `(r+1)/(|P|+1)` fraction of the arrival orders
bring at most `r` elements of `P` before `t`. -/
theorem K5b (n : ℕ) (P : Finset (Fin n)) (t : Fin n) (ht : t ∉ P) (r : ℕ) (hr : r ≤ P.card) :
    (r + 1) * Nat.factorial n ≤ (P.card + 1) *
      (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
        (P.filter (fun u => σ.symm u < σ.symm t)).card ≤ r)).card := by
  set Q := insert t P with hQ
  have htQ : t ∈ Q := Finset.mem_insert_self t P
  have hQc : Q.card = P.card + 1 := Finset.card_insert_of_notMem ht
  have hPt : ∀ σ : Equiv.Perm (Fin n), (P.filter (fun u => σ.symm u < σ.symm t)).card = rk Q σ t := by
    intro σ
    unfold rk
    rw [hQ, Finset.filter_insert, if_neg (lt_irrefl _)]
  let g : ℕ → ℕ := fun x => if x ≤ r then 1 else 0
  have hcard : (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
      (P.filter (fun u => σ.symm u < σ.symm t)).card ≤ r)).card = ∑ σ, g (rk Q σ t) := by
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro σ _
    rw [hPt σ]
  have hall : ∀ u ∈ Q, ∑ σ : Equiv.Perm (Fin n), g (rk Q σ t) = ∑ σ, g (rk Q σ u) :=
    fun u hu => sum_rk_swap Q t u htQ hu g
  have hsum : Q.card * ∑ σ : Equiv.Perm (Fin n), g (rk Q σ t)
      = ∑ σ : Equiv.Perm (Fin n), ∑ u ∈ Q, g (rk Q σ u) := by
    rw [Finset.sum_comm, ← smul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_congr rfl hall
  have hlow : ∀ σ : Equiv.Perm (Fin n), r + 1 ≤ ∑ u ∈ Q, g (rk Q σ u) := by
    intro σ
    have := count_rk_le Q σ r (by omega)
    rw [Finset.card_filter] at this
    exact this
  have hfin : (r + 1) * Nat.factorial n ≤ ∑ σ : Equiv.Perm (Fin n), ∑ u ∈ Q, g (rk Q σ u) := by
    have := Finset.sum_le_sum (fun σ (_ : σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin n)))) => hlow σ)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, smul_eq_mul] at this
    linarith
  rw [hcard, ← hQc, hsum]
  exact hfin


/-! ## K6: per-medium information bound -/

/-- Penalty of one medium decision `x` when the copy has `q` high labels. -/
def penM (k M q : ℕ) (x : ℝ) : ℝ := if k ≤ q then x else if q + M ≤ k then 1 - x else 0

/-- Labels as subsets of `ℕ`. -/
def Hn (z k : ℕ) (H : Fin z → Finset (Fin (2 * k))) : Fin z → Finset ℕ :=
  fun j => (H j).map Fin.valEmbedding

theorem mem_Hn (z k : ℕ) (H : Fin z → Finset (Fin (2 * k))) (j : Fin z) (p : Fin (2 * k)) :
    p.val ∈ Hn z k H j ↔ p ∈ H j := by
  simp [Hn, Fin.val_inj]

theorem card_Hn (z k : ℕ) (H : Fin z → Finset (Fin (2 * k))) (j : Fin z) :
    (Hn z k H j).card = (H j).card := by
  simp [Hn]

theorem Hn_sub (z k : ℕ) (H : Fin z → Finset (Fin (2 * k))) (j : Fin z) :
    Hn z k H j ⊆ Finset.range (2 * k) := by
  intro x hx
  simp only [Hn, Finset.mem_map, Fin.valEmbedding_apply] at hx
  obtain ⟨p, _, rfl⟩ := hx
  exact Finset.mem_range.mpr p.isLt

theorem π_congr (z k M : ℕ) (H H' : Fin z → Finset ℕ) (u : Fin (z * awyW k M))
    (h : ∀ p : Fin (2 * k), col z k M (awyPos z k M u).1 (pA k M p) = u →
      (p.val ∈ H (awyPos z k M u).1 ↔ p.val ∈ H' (awyPos z k M u).1)) :
    awyπ z k M H u = awyπ z k M H' u := by
  by_cases h3 : (awyPos z k M u).2.val < k + M
  · simp [awyπ, h3]
  · have hlt : (awyPos z k M u).2.val - (k + M) < 2 * k := by
      have := (awyPos z k M u).2.isLt
      simp only [awyW] at this
      omega
    have hu : col z k M (awyPos z k M u).1 (pA k M ⟨_, hlt⟩) = u := by
      have : pA k M ⟨_, hlt⟩ = (awyPos z k M u).2 := by
        apply Fin.ext; simp only [pA_val]; omega
      rw [this]
      show finProdFinEquiv ((awyPos z k M u).1, (awyPos z k M u).2) = u
      rw [Prod.mk.eta]
      exact finProdFinEquiv.apply_symm_apply u
    have key : (awyPos z k M u).2.val - (k + M) ∈ H (awyPos z k M u).1 ↔
        (awyPos z k M u).2.val - (k + M) ∈ H' (awyPos z k M u).1 := h _ hu
    simp only [awyπ, key]

theorem onlineX_local {m n : ℕ} (A : OnlineAlgorithm m) (π π' : Fin n → ℝ)
    (a : Fin n → Fin m → ℝ) (b : Fin m → ℝ) (σ : Equiv.Perm (Fin n)) (t : Fin n)
    (h : ∀ u, σ.symm u ≤ σ.symm t → π u = π' u) :
    onlineX A π a b σ t = onlineX A π' a b σ t := by
  unfold onlineX
  have hT : (σ.symm t).val + 1 ≤ n := (σ.symm t).isLt
  rw [decisions_stable A π a b σ _ _ (Nat.lt_succ_self _) n hT,
    decisions_stable A π' a b σ _ _ (Nat.lt_succ_self _) n hT]
  apply decisions_local A π π' a a b σ σ ((σ.symm t).val + 1) _ _ le_rfl
  intro s hs
  unfold arrival
  split_ifs with hsn
  · rw [h (σ ⟨s, hsn⟩) (by rw [Equiv.symm_apply_apply, Fin.le_def]; exact Nat.lt_succ_iff.mp hs)]
  · rfl

theorem conv_min (f X Y : ℝ) (h0 : 0 ≤ f) (h1 : f ≤ 1) : min X Y ≤ f * X + (1 - f) * Y := by
  nlinarith [min_le_left X Y, min_le_right X Y, mul_le_mul_of_nonneg_left (min_le_left X Y) h0,
    mul_le_mul_of_nonneg_left (min_le_right X Y) (sub_nonneg.mpr h1)]

theorem penM_nonneg (k M q : ℕ) (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : 0 ≤ penM k M q x := by
  unfold penM; split_ifs <;> linarith

/-- The labelling average of the penalty, for a decision that sees only the labels in `P`. -/
theorem overlap (k M : ℕ) (hk : 1 ≤ k) (hM : 1 ≤ M) (hM2 : 64 * M ^ 2 ≤ k)
    (P : Finset (Fin (2 * k))) (hP : 64 * P.card ≤ k) (f : Finset (Fin (2 * k)) → ℝ)
    (h01 : ∀ G, 0 ≤ f G ∧ f G ≤ 1) (hloc : ∀ G, f G = f (G ∩ P)) :
    (9 / 512 : ℝ) * 2 ^ (2 * k) ≤ ∑ G : Finset (Fin (2 * k)), penM k M G.card (f G) := by
  set gP : ℕ → ℝ := fun c => if k ≤ c then 1 else 0 with hgP
  set gN : ℕ → ℝ := fun c => if k ≤ c then 0 else if c + M ≤ k then 1 else 0 with hgN
  have hsplit : ∀ G : Finset (Fin (2 * k)),
      penM k M G.card (f G) = f G * gP G.card + (1 - f G) * gN G.card := by
    intro G; simp only [hgP, hgN, penM]; split_ifs <;> ring
  have e1 := K3' Finset.univ P f gP (Finset.subset_univ _) hloc
  have e2 := K3' Finset.univ P (fun G => 1 - f G) gN (Finset.subset_univ _)
    (fun G => by show 1 - f G = 1 - f (G ∩ P); rw [← hloc G])
  beta_reduce at e1 e2
  rw [Finset.powerset_univ] at e1 e2
  simp only [hsplit, Finset.sum_add_distrib]
  rw [e1, e2, ← Finset.sum_add_distrib]
  have hmin : ∀ A ∈ P.powerset, min (∑ C ∈ (Finset.univ \ P).powerset, gP (A.card + C.card))
      (∑ C ∈ (Finset.univ \ P).powerset, gN (A.card + C.card)) ≤
      f A * ∑ C ∈ (Finset.univ \ P).powerset, gP (A.card + C.card) +
      (1 - f A) * ∑ C ∈ (Finset.univ \ P).powerset, gN (A.card + C.card) :=
    fun A _ => conv_min _ _ _ (h01 A).1 (h01 A).2
  refine le_trans ?_ (Finset.sum_le_sum hmin)
  have hR : (Finset.univ \ P).card = 2 * k - P.card := by
    rw [Finset.card_univ_sdiff, Fintype.card_fin]
  have inner : ∀ (g : ℕ → ℝ) (h : ℕ), ∑ C ∈ (Finset.univ \ P).powerset, g (h + C.card)
      = ∑ c ∈ Finset.range (2 * k - P.card + 1), (Nat.choose (2 * k - P.card) c : ℝ) * g (h + c) := by
    intro g h
    have := Finset.sum_powerset_apply_card (fun c => g (h + c)) (x := (Finset.univ \ P))
    simp only [nsmul_eq_mul] at this
    rw [this, hR]
  set F : ℕ → ℝ := fun h => min
    (∑ c ∈ Finset.range (2 * k - P.card + 1), (Nat.choose (2 * k - P.card) c : ℝ) * gP (h + c))
    (∑ c ∈ Finset.range (2 * k - P.card + 1), (Nat.choose (2 * k - P.card) c : ℝ) * gN (h + c)) with hF
  have hA : ∀ A ∈ P.powerset, min (∑ C ∈ (Finset.univ \ P).powerset, gP (A.card + C.card))
      (∑ C ∈ (Finset.univ \ P).powerset, gN (A.card + C.card)) = F A.card := by
    intro A _
    rw [inner gP A.card, inner gN A.card]
  rw [Finset.sum_congr rfl hA]
  have hout := Finset.sum_powerset_apply_card F (x := P)
  simp only [nsmul_eq_mul] at hout
  rw [hout]
  have hK := K4new k M P.card hk hM2 hP
  refine hK.trans (le_of_eq ?_)
  apply Finset.sum_congr rfl; intro h _
  simp only [hF]
  congr 2
  · apply Finset.sum_congr rfl; intro c _; simp only [hgP]; split_ifs <;> simp
  · apply Finset.sum_congr rfl; intro c _; simp only [hgN]; split_ifs <;> first | omega | simp

/-- Number of pool columns of copy `i` that arrive before `t`. -/
def seen (z k M : ℕ) (i : Fin z) (t : Fin (z * awyW k M)) (σ : Equiv.Perm (Fin (z * awyW k M))) : ℕ :=
  (Finset.univ.filter (fun p : Fin (2 * k) => σ.symm (col z k M i (pA k M p)) < σ.symm t)).card

theorem col_inj (z k M : ℕ) (j j' : Fin z) (r r' : Fin (awyW k M)) (h : col z k M j r = col z k M j' r') :
    j = j' ∧ r = r' := by
  have := congrArg finProdFinEquiv.symm h
  simpa [col] using this

/-- K6: for every labelling off copy `i` and every medium of copy `i`, the labelling and order
average of its penalty is a constant. -/
theorem K6 (z k M m : ℕ) (α : ℝ) (A : OnlineAlgorithm m) (hk : 1 ≤ k) (hM : 1 ≤ M)
    (hM2 : 64 * M ^ 2 ≤ k) (hα : 0 < α) (H0 : Fin z → Finset (Fin (2 * k))) (i : Fin z) (b : Fin M) :
    (9 / (512 * 192) : ℝ) * 2 ^ (2 * k) * (Nat.factorial (z * awyW k M)) ≤
      ∑ σ : Equiv.Perm (Fin (z * awyW k M)), ∑ G : Finset (Fin (2 * k)),
        penM k M G.card (onlineX A (awyπ z k M (Hn z k (Function.update H0 i G)))
          (awya z k M m α) (fun _ => α * (z * k)) σ (col z k M i (mA k M b))) := by
  set n := z * awyW k M with hn
  set t := col z k M i (mA k M b) with ht
  have hbb : ∀ j : Fin m, 0 ≤ (fun _ => α * (z * k) : Fin m → ℝ) j := fun j => by positivity
  have hpt : ∀ p : Fin (2 * k), col z k M i (pA k M p) ≠ t := by
    intro p h
    have := congrArg Fin.val (col_inj _ _ _ _ _ _ _ h).2
    simp only [pA_val, mA_val] at this
    omega
  have hper : ∀ σ : Equiv.Perm (Fin n),
      (if 64 * seen z k M i t σ ≤ k then (9 / 512 : ℝ) * 2 ^ (2 * k) else 0)
      ≤ ∑ G : Finset (Fin (2 * k)), penM k M G.card (onlineX A (awyπ z k M (Hn z k (Function.update H0 i G)))
          (awya z k M m α) (fun _ => α * (z * k)) σ t) := by
    intro σ
    set f : Finset (Fin (2 * k)) → ℝ := fun G => onlineX A (awyπ z k M (Hn z k (Function.update H0 i G)))
      (awya z k M m α) (fun _ => α * (z * k)) σ t with hf
    have h01 : ∀ G, 0 ≤ f G ∧ f G ≤ 1 := fun G => (online_feasible A _ _ _ σ hbb).2 t
    split_ifs with hs
    · set P := Finset.univ.filter (fun p : Fin (2 * k) => σ.symm (col z k M i (pA k M p)) < σ.symm t)
        with hP
      have hloc : ∀ G, f G = f (G ∩ P) := by
        intro G
        apply onlineX_local
        intro u hu
        apply π_congr
        intro p hpu
        rw [mem_Hn, mem_Hn]
        by_cases hj : (awyPos z k M u).1 = i
        · rw [hj, Function.update_self, Function.update_self]
          have hu' : col z k M i (pA k M p) = u := hj ▸ hpu
          have hpP : p ∈ P := by
            rw [hP, Finset.mem_filter]
            refine ⟨Finset.mem_univ _, ?_⟩
            rw [hu']
            refine lt_of_le_of_ne hu ?_
            intro e
            exact hpt p (hu'.trans (σ.symm.injective e))
          simp [Finset.mem_inter, hpP]
        · rw [Function.update_of_ne hj, Function.update_of_ne hj]
      exact overlap k M hk hM hM2 P hs f h01 hloc
    · exact Finset.sum_nonneg fun G _ => penM_nonneg _ _ _ _ (h01 G).1 (h01 G).2
  -- counting orders with few seen pool columns
  set S := Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => 64 * seen z k M i t σ ≤ k) with hS
  have hcount : Nat.factorial n ≤ 192 * S.card := by
    set Pc := (Finset.univ : Finset (Fin (2 * k))).image (fun p => col z k M i (pA k M p)) with hPc
    have hinj : Function.Injective (fun p : Fin (2 * k) => col z k M i (pA k M p)) := by
      intro p p' h
      have := congrArg Fin.val (col_inj _ _ _ _ _ _ _ h).2
      simp only [pA_val] at this
      exact Fin.ext (by omega)
    have hPcc : Pc.card = 2 * k := by rw [hPc, Finset.card_image_of_injective _ hinj]; simp
    have htPc : t ∉ Pc := by
      intro h
      obtain ⟨p, _, hp⟩ := Finset.mem_image.mp h
      exact hpt p hp
    have hK := K5b n Pc t htPc (k / 64) (by rw [hPcc]; omega)
    have hfil : ∀ σ : Equiv.Perm (Fin n), (Pc.filter (fun u => σ.symm u < σ.symm t)).card
        = seen z k M i t σ := by
      intro σ
      rw [hPc, Finset.filter_image, Finset.card_image_of_injective _ hinj]
      rfl
    have hsub : (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
        (Pc.filter (fun u => σ.symm u < σ.symm t)).card ≤ k / 64)) ⊆ S := by
      intro σ hσ
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
      rw [← hfil σ]; omega
    have h1 := Finset.card_le_card hsub
    rw [hPcc] at hK
    have h2 : (k / 64 + 1) * Nat.factorial n ≤ (2 * k + 1) * S.card :=
      hK.trans (Nat.mul_le_mul_left _ h1)
    have h3 : 2 * k + 1 ≤ 192 * (k / 64 + 1) := by omega
    have h4 : Nat.factorial n * (2 * k + 1) ≤ (192 * S.card) * (2 * k + 1) := by
      calc Nat.factorial n * (2 * k + 1) ≤ Nat.factorial n * (192 * (k / 64 + 1)) :=
            Nat.mul_le_mul_left _ h3
        _ = 192 * ((k / 64 + 1) * Nat.factorial n) := by ring
        _ ≤ 192 * ((2 * k + 1) * S.card) := Nat.mul_le_mul_left _ h2
        _ = (192 * S.card) * (2 * k + 1) := by ring
    exact Nat.le_of_mul_le_mul_right h4 (by omega)
  have hsum := Finset.sum_le_sum (fun σ (_ : σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin n)))) => hper σ)
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, nsmul_eq_mul, add_zero] at hsum
  refine le_trans ?_ hsum
  have hc : (Nat.factorial n : ℝ) ≤ 192 * S.card := by exact_mod_cast hcount
  have hW : (0 : ℝ) < 2 ^ (2 * k) := by positivity
  rw [← hS]
  nlinarith

/-! ## K7: Yao average over labellings and the constants -/

theorem yao_update {ι S : Type} [Fintype ι] [DecidableEq ι] [Fintype S] (i : ι)
    (f : (ι → S) → ℝ) :
    ∑ H : ι → S, ∑ G : S, f (Function.update H i G) = Fintype.card S * ∑ H : ι → S, f H := by
  let e : (ι → S) × S ≃ (ι → S) × S :=
    { toFun := fun p => (Function.update p.1 i p.2, p.1 i)
      invFun := fun p => (Function.update p.1 i p.2, p.1 i)
      left_inv := fun p => by simp
      right_inv := fun p => by simp }
  rw [← Fintype.sum_prod_type']
  have := Equiv.sum_comp e (fun p => f p.1)
  simp only [e, Equiv.coe_fn_mk] at this
  rw [this, Fintype.sum_prod_type]
  simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.mul_sum]

theorem awyπ_nonneg (z k M : ℕ) (H : Fin z → Finset ℕ) (t : Fin (z * awyW k M)) :
    0 ≤ awyπ z k M H t := by
  unfold awyπ; split_ifs <;> norm_num

theorem awya_bounds (z k M m : ℕ) (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1) (t : Fin (z * awyW k M))
    (j : Fin m) : 0 ≤ awya z k M m α t j ∧ awya z k M m α t j ≤ 1 := by
  unfold awya; split_ifs <;> constructor <;> linarith

theorem main_bound : ∃ c K : ℝ, 0 < c ∧ 0 < K ∧
    ∀ (m : ℕ) (B : ℝ), 2 ≤ m → K * Real.log (m : ℝ) ≤ B →
      ∀ A : OnlineAlgorithm m,
        ∃ (n : ℕ) (π : Fin n → ℝ) (a : Fin n → Fin m → ℝ),
          (∀ t, 0 ≤ π t) ∧ (∀ t i, 0 ≤ a t i ∧ a t i ≤ 1) ∧
            expectedOnlineValue A π a (fun _ => B) <
              (1 - c * Real.sqrt (Real.log (m : ℝ) / B)) * OPT π a (fun _ => B) := by
  set c6 : ℝ := 9 / (512 * 192) with hc6
  refine ⟨c6 / 1000, 400, by positivity, by norm_num, ?_⟩
  intro m B hm hB A
  set z := Nat.log 2 m with hz
  have hz1 : 1 ≤ z := Nat.le_log_of_pow_le one_lt_two (by simpa using hm)
  have h2z : 2 ^ z ≤ m := Nat.pow_log_le_self 2 (by omega)
  have hmz : m < 2 ^ (z + 1) := Nat.lt_pow_succ_log_self one_lt_two m
  have hzr : (1 : ℝ) ≤ z := by exact_mod_cast hz1
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hm0 : (0 : ℝ) < m := by positivity
  have hlogm_lo : (z : ℝ) * Real.log 2 ≤ Real.log m := by
    rw [← Real.log_pow]
    apply Real.log_le_log (by positivity)
    exact_mod_cast h2z
  have hlogm_hi : Real.log m < ((z : ℝ) + 1) * Real.log 2 := by
    have : Real.log m < Real.log ((2 : ℝ) ^ (z + 1)) :=
      Real.log_lt_log hm0 (by exact_mod_cast hmz)
    rw [Real.log_pow] at this; push_cast at this; exact this
  have hz0 : (0 : ℝ) < z := by linarith
  have hBz : 256 ≤ B / z := by
    rw [le_div_iff₀ hz0]; nlinarith
  have hB0 : 0 < B := by
    have := (le_div_iff₀ hz0).mp hBz; linarith
  set k := ⌈B / z⌉₊ with hk
  have hkge : B / z ≤ k := Nat.le_ceil _
  have hklt : (k : ℝ) < B / z + 1 := Nat.ceil_lt_add_one (by positivity)
  have hk256r : (256 : ℝ) ≤ k := by linarith
  have hk256 : 256 ≤ k := by exact_mod_cast hk256r
  have hk1 : 1 ≤ k := by omega
  have hBle : B ≤ z * k := by
    have := (div_le_iff₀ hz0).mp hkge; linarith
  have hBgt : (z : ℝ) * (k - 1) < B := by
    have : (k : ℝ) - 1 < B / z := by linarith
    have := (lt_div_iff₀ hz0).mp this; linarith
  set α := B / (z * k) with hαdef
  have hzk0 : (0 : ℝ) < z * k := by positivity
  have hα0 : 0 < α := div_pos hB0 hzk0
  have hα1 : α ≤ 1 := (div_le_one hzk0).mpr hBle
  have hαzk : α * (z * k) = B := by rw [hαdef]; field_simp
  set r := Real.sqrt k with hr
  have hr2 : r ^ 2 = k := Real.sq_sqrt (Nat.cast_nonneg _)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr16 : 16 ≤ r := by nlinarith
  set M := ⌊r / 8⌋₊ with hMdef
  have hMle : (M : ℝ) ≤ r / 8 := Nat.floor_le (by positivity)
  have hMgt : r / 8 < M + 1 := Nat.lt_floor_add_one _
  have hM16 : r / 16 < M := by linarith
  have hM1 : 1 ≤ M := by
    have : (0 : ℝ) < M := by linarith
    have : 0 < M := by exact_mod_cast this
    omega
  have hM2 : 64 * M ^ 2 ≤ k := by
    have : 64 * (M : ℝ) ^ 2 ≤ k := by
      have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg _
      nlinarith
    exact_mod_cast this
  -- the penalty of medium `b` of copy `i`
  set bb : Fin m → ℝ := fun _ => α * (z * k) with hbb
  let P : (Fin z → Finset (Fin (2 * k))) → Equiv.Perm (Fin (z * awyW k M)) → Fin z → Fin M → ℝ :=
    fun H σ i b => penM k M (H i).card (onlineX A (awyπ z k M (Hn z k H)) (awya z k M m α) bb σ
      (col z k M i (mA k M b)))
  set nf : ℝ := (Nat.factorial (z * awyW k M) : ℝ) with hnf
  set cH : ℝ := (Fintype.card (Fin z → Finset (Fin (2 * k))) : ℝ) with hcH
  have hib : ∀ i b, cH * (c6 * nf) ≤ ∑ H : Fin z → Finset (Fin (2 * k)), ∑ σ, P H σ i b := by
    intro i b
    have hy := yao_update i (fun H : Fin z → Finset (Fin (2 * k)) => ∑ σ, P H σ i b)
    have hK6 : ∀ H : Fin z → Finset (Fin (2 * k)),
        c6 * 2 ^ (2 * k) * nf ≤ ∑ G : Finset (Fin (2 * k)), ∑ σ, P (Function.update H i G) σ i b := by
      intro H
      have := K6 z k M m α A hk1 hM1 hM2 hα0 H i b
      rw [Finset.sum_comm] at this
      simpa only [P, Function.update_self] using this
    have hcard : (Fintype.card (Finset (Fin (2 * k))) : ℝ) = 2 ^ (2 * k) := by
      rw [Fintype.card_finset, Fintype.card_fin]; push_cast; ring
    rw [hcard] at hy
    have hsum := Finset.sum_le_sum (fun H (_ : H ∈ (Finset.univ : Finset (Fin z → Finset (Fin (2 * k))))) => hK6 H)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hy] at hsum
    have hW : (0 : ℝ) < 2 ^ (2 * k) := by positivity
    have : 2 ^ (2 * k) * (cH * (c6 * nf)) ≤ 2 ^ (2 * k) * ∑ H : Fin z → Finset (Fin (2 * k)), ∑ σ, P H σ i b := by
      rw [hcH]; linarith
    exact le_of_mul_le_mul_left this hW
  set D : (Fin z → Finset (Fin (2 * k))) → ℝ := fun H => ∑ σ, ∑ i, ∑ b, P H σ i b with hD
  have hsumD : ∑ H : Fin z → Finset (Fin (2 * k)), (z * M * (c6 * nf)) ≤ ∑ H, D H := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    calc (Fintype.card (Fin z → Finset (Fin (2 * k))) : ℝ) * (z * M * (c6 * nf))
        = ∑ i : Fin z, ∑ b : Fin M, cH * (c6 * nf) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hcH]; ring
      _ ≤ ∑ i : Fin z, ∑ b : Fin M, ∑ H : Fin z → Finset (Fin (2 * k)), ∑ σ, P H σ i b :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun b _ => hib i b
      _ = ∑ i : Fin z, ∑ H : Fin z → Finset (Fin (2 * k)), ∑ b : Fin M, ∑ σ, P H σ i b :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ H : Fin z → Finset (Fin (2 * k)), ∑ i : Fin z, ∑ b : Fin M, ∑ σ, P H σ i b :=
          Finset.sum_comm
      _ = ∑ H : Fin z → Finset (Fin (2 * k)), ∑ i : Fin z, ∑ σ, ∑ b : Fin M, P H σ i b :=
          Finset.sum_congr rfl fun H _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ H, D H :=
          Finset.sum_congr rfl fun H _ => Finset.sum_comm
  obtain ⟨H, _, hH⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsumD
  -- the instance
  refine ⟨z * awyW k M, awyπ z k M (Hn z k H), awya z k M m α, awyπ_nonneg z k M _,
    fun t j => awya_bounds z k M m α hα0.le hα1 t j, ?_⟩
  have hb : (fun _ : Fin m => B) = bb := funext fun _ => hαzk.symm
  rw [hb]
  obtain ⟨hO7, hOlo, hub⟩ := K2 z k M m α (Hn z k H) hk1 hα0 h2z (Hn_sub z k H)
  set O := OPT (awyπ z k M (Hn z k H)) (awya z k M m α) bb with hO
  have hσ : ∀ σ, onlineValue A (awyπ z k M (Hn z k H)) (awya z k M m α) bb σ
      + ∑ i, ∑ b, P H σ i b ≤ O := by
    intro σ
    rw [onlineValue_eq]
    have h1 := hub (onlineX A (awyπ z k M (Hn z k H)) (awya z k M m α) bb σ)
      (online_feasible A _ _ bb σ (fun _ => by positivity))
    have h2 : ∑ i, awyD z k M (Hn z k H) (onlineX A (awyπ z k M (Hn z k H)) (awya z k M m α) bb σ) i
        = ∑ i, ∑ b, P H σ i b := by
      apply Finset.sum_congr rfl; intro i _
      simp only [awyD, P, penM, card_Hn]
    linarith
  have hsumσ := Finset.sum_le_sum (fun σ (_ : σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin (z * awyW k M))))) => hσ σ)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul] at hsumσ
  have hnf0 : (0 : ℝ) < nf := by rw [hnf]; exact_mod_cast Nat.factorial_pos _
  have hE : expectedOnlineValue A (awyπ z k M (Hn z k H)) (awya z k M m α) bb ≤ O - z * M * c6 := by
    unfold expectedOnlineValue
    rw [div_le_iff₀ hnf0]
    have : D H = ∑ σ, ∑ i, ∑ b, P H σ i b := rfl
    rw [← hnf] at hsumσ
    nlinarith
  -- constants
  set s := Real.sqrt (Real.log m / B) with hs
  have hlog0 : 0 ≤ Real.log m := by nlinarith
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = Real.log m / B := Real.sq_sqrt (div_nonneg hlog0 hB0.le)
  have hkl : (k : ℝ) * Real.log m ≤ 4 * B := by
    have h1 : (k : ℝ) * Real.log m ≤ k * (((z : ℝ) + 1) * 0.6931471808) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      nlinarith
    have hzk2 : (z : ℝ) * 2 ≤ z * k := by nlinarith
    nlinarith
  have hsr : s * r ≤ 2 := by
    have : (s * r) ^ 2 ≤ 4 := by
      rw [mul_pow, hs2, hr2, div_mul_eq_mul_div, div_le_iff₀ hB0]
      linarith
    nlinarith [mul_nonneg hs0 hr0]
  have hsk : s * k ≤ 2 * r := by
    rw [← hr2]; nlinarith
  have hkey : c6 / 1000 * s * (7 * z * k) < z * M * c6 := by
    have hc60 : 0 < c6 := by rw [hc6]; norm_num
    have : 7 * (s * k) < 1000 / 1000 * 224 * M := by nlinarith
    have hM0 : (0 : ℝ) < M := by linarith
    nlinarith [mul_pos hz0 hc60, mul_pos (mul_pos hz0 hc60) hM0]
  have hcs0 : 0 ≤ c6 / 1000 * s := by positivity
  have : c6 / 1000 * s * O ≤ c6 / 1000 * s * (7 * z * k) := mul_le_mul_of_nonneg_left hO7 hcs0
  calc expectedOnlineValue A (awyπ z k M (Hn z k H)) (awya z k M m α) bb ≤ O - z * M * c6 := hE
    _ < O - c6 / 1000 * s * O := by linarith
    _ = (1 - c6 / 1000 * s) * O := by ring

end DynamicOnlineLP.LowerBound

open DynamicOnlineLP.LowerBound in
theorem solution : ∃ c K : ℝ, 0 < c ∧ 0 < K ∧
      ∀ (m : ℕ) (B : ℝ), 2 ≤ m → K * Real.log (m : ℝ) ≤ B →
        ∀ A : OnlineAlgorithm m,
          ∃ (n : ℕ) (π : Fin n → ℝ) (a : Fin n → Fin m → ℝ),
            (∀ t, 0 ≤ π t) ∧ (∀ t i, 0 ≤ a t i ∧ a t i ≤ 1) ∧
              expectedOnlineValue A π a (fun _ => B) <
                (1 - c * Real.sqrt (Real.log (m : ℝ) / B)) * OPT π a (fun _ => B) := by
  exact main_bound
