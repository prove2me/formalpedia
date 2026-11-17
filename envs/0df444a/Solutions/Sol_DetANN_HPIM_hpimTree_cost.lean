-- Prove2me | solution 1 for DetANN.HPIM.hpimTree_cost
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-16T06:42:45.386613+00:00
-- url     : https://prove2.me/submissions/d6dec6bd-d4ba-48de-b9a8-5a17ae97ec45

import Mathlib
import Definitions.Def_DetANN_HPIMTree
import Theorems.Thm_DetANN_HPIM_lookupTree_spec
import Theorems.Thm_DetANN_HPIM_median_threshold
import Theorems.Thm_DetANN_HPIM_bisect_spec

/-!
# The query cost of the HPIM tree, from the lookup contract, the median threshold and the ladder
search
-/

namespace DetANN.HPIM

variable {m : ℕ}

section M4

open Classical

variable {n : ℕ} (P : Fin n → EuclideanSpace ℝ (Fin m))

lemma thrReach_of_dist {d : ℝ} {i j : Fin n} (h : dist (P i) (P j) ≤ d) : thrReach P d i j := by
  by_cases hij : i = j
  · subst hij; exact SimpleGraph.Reachable.refl _
  · exact SimpleGraph.Adj.reachable (by rw [SimpleGraph.fromRel_adj]; exact ⟨hij, Or.inl h⟩)

lemma thrReach_symm {d : ℝ} {i j : Fin n} (h : thrReach P d i j) : thrReach P d j i :=
  SimpleGraph.Reachable.symm h

lemma thrReach_trans {d : ℝ} {i j k : Fin n} (h : thrReach P d i j) (h' : thrReach P d j k) :
    thrReach P d i k :=
  SimpleGraph.Reachable.trans h h'

lemma dist_le_of_thrReach {d : ℝ} (hd : 0 ≤ d) {i j : Fin n} (h : thrReach P d i j) :
    dist (P i) (P j) ≤ ((n : ℝ) - 1) * d :=
  (median_threshold P).1 d hd i j h

lemma medThreshold_spec (hn : 2 ≤ n) (hP : Function.Injective P) :
    (∃ i, n / 2 + 1 ≤ (Finset.univ.filter (thrReach P (medThreshold P) i)).card) ∧
    0 < medThreshold P ∧
    ∀ d' < medThreshold P, ∀ i, (Finset.univ.filter (thrReach P d' i)).card ≤ n / 2 :=
  (median_threshold P).2.2.2 hn hP

lemma exists_rep (d : ℝ) (i : Fin n) : ∃ j, thrReach P d i j ∧ IsRep P d j :=
  (median_threshold P).2.1 d i

lemma card_reps_le (d : ℝ) (i₀ : Fin n)
    (hbig : n / 2 + 1 ≤ (Finset.univ.filter (thrReach P d i₀)).card) :
    (Finset.univ.filter (IsRep P d)).card ≤ (n + 1) / 2 :=
  (median_threshold P).2.2.1 d i₀ hbig

end M4

section Node

open Classical

variable {N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ)

lemma hpimNode_succ_eq (f : ℕ) (S : Finset (Fin N)) (h : ¬ S.card ≤ 1) :
    hpimNode Y δ (f + 1) S =
      .node S.card (MOf Y δ S) (Nat.clog 2 (MOf Y δ S - 1)) (ZOf Y δ S)
        (fun i => ((S.orderEmbOfFin rfl i : Fin N) : ℕ))
        (fun i => hpimNode Y δ f (compBotOf Y S i)) (hpimNode Y δ f (repsOf Y S)) := by
  rw [hpimNode, if_neg h]

lemma hpimNode_single (f : ℕ) (k : Fin N) :
    hpimNode Y δ f {k} = .single (k : ℕ) := by
  cases f with
  | zero => simp [hpimNode]
  | succ f => rw [hpimNode]; simp

end Node

lemma clog_child {n k : ℕ} (hn : 2 ≤ n) (hk : k ≤ (n + 1) / 2) :
    Nat.clog 2 k + 1 ≤ Nat.clog 2 n := by
  rw [Nat.clog_of_one_lt (n := n) (by norm_num) (by omega)]
  have : (n + 2 - 1) / 2 = (n + 1) / 2 := by omega
  rw [this]
  exact Nat.add_le_add_right (Nat.clog_mono_right 2 hk) 1

section NodeFacts

open Classical

variable {N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ)

lemma ptsOf_injective (hY : Function.Injective Y) (S : Finset (Fin N)) :
    Function.Injective (ptsOf Y S) :=
  fun _ _ h => (S.orderEmbOfFin rfl).injective (hY h)

lemma rmedOf_pos (hY : Function.Injective Y) (S : Finset (Fin N)) (hS : 2 ≤ S.card) :
    0 < rmedOf Y S := by
  unfold rmedOf
  have := (medThreshold_spec (ptsOf Y S) hS (ptsOf_injective Y hY S)).2.1
  positivity

lemma lamOf_pos (hδ : 0 < δ) : 0 < lamOf N δ := by unfold lamOf; positivity

lemma rhoOf_pos (hY : Function.Injective Y) (hδ : 0 < δ) (S : Finset (Fin N)) (hS : 2 ≤ S.card)
    (k : ℕ) : 0 < rhoOf Y δ S k := by
  unfold rhoOf
  have := rmedOf_pos Y hY S hS
  positivity

lemma rhoOf_succ (S : Finset (Fin N)) (k : ℕ) :
    rhoOf Y δ S (k + 1) = (1 + δ / 4) * rhoOf Y δ S k := by
  unfold rhoOf; ring

lemma exists_ladder_top (hY : Function.Injective Y) (hδ : 0 < δ) (S : Finset (Fin N))
    (hS : 2 ≤ S.card) : ∃ k, bOf Y δ S ≤ rhoOf Y δ S k := by
  have hA : 0 < rmedOf Y S / 2 / 2 := by have := rmedOf_pos Y hY S hS; positivity
  have hc : 0 < 1 + δ / 4 := by positivity
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (bOf Y δ S * (1 + δ / 4) / (rmedOf Y S / 2 / 2))
    (by linarith : (1 : ℝ) < 1 + δ / 4)
  refine ⟨k, ?_⟩
  unfold rhoOf
  rw [le_div_iff₀ hc]
  rw [div_lt_iff₀ hA] at hk
  linarith

lemma MOf_eq (hY : Function.Injective Y) (hδ : 0 < δ) (S : Finset (Fin N)) (hS : 2 ≤ S.card) :
    MOf Y δ S = Nat.find (exists_ladder_top Y δ hY hδ S hS) + 1 := by
  unfold MOf; rw [dif_pos (exists_ladder_top Y δ hY hδ S hS)]

/-- The NearNbr contract of the `i`-th lookup of a node. -/
lemma lookup_node_spec (hm : 1 ≤ m) (hY : Function.Injective Y) (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    (S : Finset (Fin N)) (hS : 2 ≤ S.card) (i : ℕ) (hi : i < MOf Y δ S)
    (q : EuclideanSpace ℝ (Fin m)) :
    (∀ l, lookup (ZOf Y δ S) i q = some l →
      ∃ h : l < S.card, ‖q - ptsOf Y S ⟨l, h⟩‖ ≤ (1 + δ / 4) * rhoOf Y δ S i) ∧
    (lookup (ZOf Y δ S) i q = none → ∀ j, rhoOf Y δ S i < ‖q - ptsOf Y S j‖) := by
  have := (lookupTree_spec hm (n := S.card) (by omega) (ptsOf Y S) (rhoOf Y δ S i) δ
    (rhoOf_pos Y δ hY hδ S hS i) hδ hδ').1 q
  simp only [lookup, dif_pos hi]
  exact this

end NodeFacts

/-! ## The cost bound: arithmetic -/

lemma natlog_le_real (n : ℕ) (hn : n ≠ 0) : (Nat.log 2 n : ℝ) ≤ 2 * Real.log n := by
  have h := Nat.pow_log_le_self 2 hn
  have h' : ((2 : ℝ)) ^ (Nat.log 2 n) ≤ n := by exact_mod_cast h
  have := Real.log_le_log (by positivity) h'
  rw [Real.log_pow] at this
  have h2 := Real.log_two_gt_d9
  nlinarith [Nat.cast_nonneg (α := ℝ) (Nat.log 2 n)]

lemma clog_le_real (n : ℕ) (hn : 1 ≤ n) : (Nat.clog 2 n : ℝ) ≤ 2 * Real.log n + 1 := by
  rcases Nat.lt_or_ge 1 n with h | h
  · have h1 := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) h
    have h1' : ((2 : ℝ)) ^ (Nat.clog 2 n - 1) ≤ n := by exact_mod_cast h1.le
    have := Real.log_le_log (by positivity) h1'
    rw [Real.log_pow] at this
    have hc : (Nat.clog 2 n : ℝ) ≤ ((Nat.clog 2 n - 1 : ℕ) : ℝ) + 1 := by
      have : Nat.clog 2 n ≤ (Nat.clog 2 n - 1) + 1 := by omega
      exact_mod_cast this
    nlinarith [Real.log_two_gt_d9, Nat.cast_nonneg (α := ℝ) (Nat.clog 2 n - 1)]
  · have : n = 1 := by omega
    subst this; simp

/-- The basic facts on `L = log (N/δ)`. -/
lemma logL_facts (N : ℕ) (hN : 1 ≤ N) (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    Real.log 2 ≤ Real.log (N / δ) ∧ Real.log N ≤ Real.log (N / δ) ∧
      -Real.log δ ≤ Real.log (N / δ) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN'
  have hd : Real.log δ ≤ -Real.log 2 := by
    have := Real.log_le_log hδ hδ'.le
    rwa [one_div, Real.log_inv] at this
  have hl2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  rw [Real.log_div (by positivity) hδ.ne']
  refine ⟨by linarith, by linarith, by linarith⟩

lemma clogN_bound (N : ℕ) (hN : 1 ≤ N) (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    (Nat.clog 2 N : ℝ) + 1 ≤ 5 * Real.log (N / δ) := by
  obtain ⟨h2, hN2, -⟩ := logL_facts N hN δ hδ hδ'
  have := clog_le_real N hN
  have := Real.log_two_gt_d9
  linarith

lemma V_bound (m N : ℕ) (hm : 1 ≤ m) (hN : 1 ≤ N) (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    ((5 * Nat.log 2 (2 * bspFuel N m δ) + 7 : ℕ) : ℝ) ≤ 371 * m * Real.log (N / δ) := by
  obtain ⟨h2, hN2, hd⟩ := logL_facts N hN δ hδ hδ'
  set L := Real.log (N / δ)
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set B : ℝ := 2 ^ 12 / (δ / 4)
  have hB : B = 2 ^ 14 / δ := by simp only [B]; field_simp; norm_num
  have hB1 : 1 ≤ B := by
    rw [hB, le_div_iff₀ hδ]; linarith
  set X : ℝ := (N : ℝ) * B ^ (2 * m)
  have hX1 : 1 ≤ X := one_le_mul_of_one_le_of_one_le hN' (one_le_pow₀ hB1)
  have hF : ((bspFuel N m δ : ℕ) : ℝ) ≤ X + 2 := by
    change ((⌈X⌉₊ + 1 : ℕ) : ℝ) ≤ X + 2
    push_cast
    have := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ X)
    linarith
  have hpos : 2 * bspFuel N m δ ≠ 0 := by unfold bspFuel; omega
  have h1 := natlog_le_real _ hpos
  have h6 : (((2 * bspFuel N m δ : ℕ)) : ℝ) ≤ 6 * X := by push_cast; linarith
  have hlog6 : Real.log (((2 * bspFuel N m δ : ℕ)) : ℝ) ≤ Real.log (6 * X) :=
    Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hpos) h6
  have hX : Real.log (6 * X) = Real.log 6 + Real.log N + (2 * m : ℕ) * Real.log B := by
    simp only [X]
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow]
    ring
  have hlB : Real.log B ≤ 14 * Real.log 2 + L := by
    have : B ≤ 2 ^ 14 * (N / δ) := by
      rw [hB, mul_div_assoc']; gcongr; linarith
    have := Real.log_le_log (by positivity) this
    rwa [Real.log_mul (by positivity) (by positivity), Real.log_pow] at this
  have hl6 : Real.log 6 ≤ 3 * Real.log 2 := by
    rw [← Real.log_rpow (by norm_num)]
    exact Real.log_le_log (by norm_num) (by norm_num)
  have hlB0 : 0 ≤ Real.log B := Real.log_nonneg hB1
  have hcast : ((2 * m : ℕ) : ℝ) = 2 * m := by push_cast; ring
  rw [hcast] at hX
  have key : Real.log (6 * X) ≤ 36 * m * L := by
    rw [hX]
    have : (2 * m : ℝ) * Real.log B ≤ 2 * m * (16 * L) := by
      gcongr; linarith
    nlinarith
  push_cast
  nlinarith

lemma Kb_bound (N : ℕ) (hN : 1 ≤ N) (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    (Nat.clog 2 ⌈144 * (N : ℝ) * ((Nat.clog 2 N : ℝ) + 1) / δ ^ 2⌉₊ : ℝ) ≤
      26 * Real.log (N / δ) := by
  obtain ⟨h2, hN2, hd⟩ := logL_facts N hN δ hδ hδ'
  set L := Real.log (N / δ)
  have hl2 := Real.log_two_gt_d9
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set Yv : ℝ := 144 * (N : ℝ) * ((Nat.clog 2 N : ℝ) + 1) / δ ^ 2
  have hcN : (Nat.clog 2 N : ℝ) + 1 ≤ 2 * N := by
    have := clog_le_real N hN
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < N)
    linarith
  have hY1 : 1 ≤ Yv := by
    simp only [Yv]; rw [le_div_iff₀ (by positivity)]
    have : δ ^ 2 ≤ 1 := by nlinarith
    have : (1 : ℝ) ≤ (Nat.clog 2 N : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) (Nat.clog 2 N)]
    nlinarith
  have hK1 : 1 ≤ ⌈Yv⌉₊ := Nat.one_le_iff_ne_zero.2 (by
    intro h; rw [Nat.ceil_eq_zero] at h; linarith)
  have hKle : ((⌈Yv⌉₊ : ℕ) : ℝ) ≤ 576 * (N / δ) ^ 2 := by
    have := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ Yv)
    have hY : Yv ≤ 288 * (N / δ) ^ 2 := by
      simp only [Yv]; rw [div_pow, mul_div_assoc', div_le_div_iff_of_pos_right (by positivity)]
      nlinarith
    nlinarith
  have hc := clog_le_real _ hK1
  have hlK := Real.log_le_log (by exact_mod_cast hK1) hKle
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hlK
  have h576 : Real.log 576 ≤ 10 * Real.log 2 := by
    rw [← Real.log_rpow (by norm_num)]
    exact Real.log_le_log (by norm_num) (by norm_num)
  push_cast at hlK
  linarith

/-- The final combination. -/
lemma final_arith (m : ℕ) (hm : 1 ≤ m) (L A V K : ℝ) (hL : Real.log 2 ≤ L)
    (hA : A ≤ 5 * L) (hV : V ≤ 371 * m * L) (hK : K ≤ 26 * L) (hA0 : 0 ≤ A) (hV0 : 0 ≤ V)
    (_hK0 : 0 ≤ K) :
    A * (2 * V + 1) + K * (V + 1) + V + 3 ≤ 15000 * m * L ^ 2 := by
  have hl2 := Real.log_two_gt_d9
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hL0 : 0 ≤ L := by linarith
  have hmL : L ≤ m * L := by nlinarith
  have h1 : 2 * V + 1 ≤ 744 * m * L := by nlinarith
  have h2 : V + 1 ≤ 373 * m * L := by nlinarith
  have e1 : A * (2 * V + 1) ≤ 5 * L * (744 * m * L) :=
    mul_le_mul hA h1 (by linarith) (by linarith)
  have e2 : K * (V + 1) ≤ 26 * L * (373 * m * L) :=
    mul_le_mul hK h2 (by linarith) (by linarith)
  have e3 : V + 3 ≤ 754 * m * L ^ 2 := by
    have : m * L ≤ 2 * (m * L) * L := by nlinarith
    nlinarith
  nlinarith

/-! ## The cost bound: structure -/

section CostStructure

open Classical

lemma lookupCost_le {M : ℕ} (Z : Fin M → BoxTree m) (q : Fin m → ℝ) (V : ℕ)
    (hV : ∀ i : Fin M, (Z i).visits q ≤ V) (i : ℕ) : lookupCost Z i q ≤ V := by
  unfold lookupCost; split_ifs with h
  · exact hV _
  · exact Nat.zero_le _

lemma bisectCost_le {M : ℕ} (Z : Fin M → BoxTree m) (q : Fin m → ℝ) (V : ℕ)
    (hV : ∀ i : Fin M, (Z i).visits q ≤ V) : ∀ t lo, bisectCost Z q t lo ≤ t * (V + 1) + 1 := by
  intro t
  induction t with
  | zero => intro lo; simp [bisectCost]
  | succ t ih =>
    intro lo
    have h1 : lookupCCost Z (lo + 2 ^ t) q ≤ V := lookupCost_le Z q V hV _
    simp only [bisectCost]
    split_ifs
    · have := ih (lo + 2 ^ t); nlinarith
    · have := ih lo; nlinarith

variable {N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ)

/-- The ladder-length bound `Kb = ⌈144 N (h+1)/δ²⌉`. -/
noncomputable def Kb (N : ℕ) (δ : ℝ) : ℕ := ⌈144 * (N : ℝ) * ((Nat.clog 2 N : ℝ) + 1) / δ ^ 2⌉₊

lemma MOf_le (hY : Function.Injective Y) (hδ : 0 < δ) (hδ' : δ < 1 / 2) (S : Finset (Fin N))
    (hS : 2 ≤ S.card) : MOf Y δ S - 1 ≤ Kb N δ := by
  rw [MOf_eq Y δ hY hδ S hS, Nat.add_sub_cancel]
  apply Nat.find_min'
  -- Bernoulli: (1+γ)^K ≥ 1 + Kγ ≥ 9 n λ
  set K := Kb N δ
  have hr := rmedOf_pos Y hY S hS
  have hlam := lamOf_pos (N := N) δ hδ
  have hK : 144 * (N : ℝ) * ((Nat.clog 2 N : ℝ) + 1) / δ ^ 2 ≤ K := Nat.le_ceil _
  have hn : (S.card : ℝ) ≤ N := by exact_mod_cast (Finset.card_le_univ S).trans (by simp)
  have hbern : 1 + (K : ℝ) * (δ / 4) ≤ (1 + δ / 4) ^ K :=
    one_add_mul_le_pow (by linarith) K
  unfold bOf rhoOf lamOf
  have hc : (0 : ℝ) < 1 + δ / 4 := by positivity
  rw [le_div_iff₀ hc]
  have hh : (0 : ℝ) ≤ (Nat.clog 2 N : ℝ) := Nat.cast_nonneg _
  have key : (S.card : ℝ) * (4 * ((Nat.clog 2 N : ℝ) + 1) / δ) * 9 ≤ (K : ℝ) * (δ / 4) := by
    have e : (S.card : ℝ) * (4 * ((Nat.clog 2 N : ℝ) + 1) / δ) * 9 =
        144 * (S.card : ℝ) * ((Nat.clog 2 N : ℝ) + 1) / δ ^ 2 * (δ / 4) := by
      field_simp; ring
    rw [e]
    gcongr
    calc 144 * (S.card : ℝ) * ((Nat.clog 2 N : ℝ) + 1) / δ ^ 2
        ≤ 144 * (N : ℝ) * ((Nat.clog 2 N : ℝ) + 1) / δ ^ 2 := by gcongr
      _ ≤ (K : ℝ) := hK
  have h98 : 1 + δ / 4 ≤ 9 / 8 := by linarith
  have hpos : 0 ≤ (S.card : ℝ) * (4 * ((Nat.clog 2 N : ℝ) + 1) / δ) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h98 (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hpos)
    hr.le)]

/-- The per-lookup visit bound for every node of the tree. -/
noncomputable def Vb (N m : ℕ) (δ : ℝ) : ℕ := 5 * Nat.log 2 (2 * bspFuel N m δ) + 7

lemma bspFuel_mono {n n' : ℕ} (h : n ≤ n') (hδ : 0 < δ) : bspFuel n m δ ≤ bspFuel n' m δ := by
  unfold bspFuel
  have : (n : ℝ) ≤ n' := by exact_mod_cast h
  gcongr

lemma node_visits_le (hm : 1 ≤ m) (hY : Function.Injective Y) (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    (S : Finset (Fin N)) (hS : 2 ≤ S.card) (q : Fin m → ℝ) :
    ∀ i : Fin (MOf Y δ S), (ZOf Y δ S i).visits q ≤ Vb N m δ := by
  intro i
  have := (lookupTree_spec hm (n := S.card) (by omega) (ptsOf Y S) (rhoOf Y δ S i) δ
    (rhoOf_pos Y δ hY hδ S hS i) hδ hδ').2 q
  refine this.trans ?_
  unfold Vb
  have hc : S.card ≤ N := (Finset.card_le_univ S).trans (by simp)
  have := Nat.log_mono_right (b := 2) (Nat.mul_le_mul_left 2 (bspFuel_mono δ hc hδ (m := m)))
  omega

/-- **Cost structure.** The cost of a node is at most `(⌈log₂|S|⌉ + 1)(2V + 1) + ⌈log₂ Kb⌉(V + 1) + V + 3`. -/
theorem hpimNode_cost (hm : 1 ≤ m) (hY : Function.Injective Y) (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    ∀ f (S : Finset (Fin N)), S.Nonempty → Nat.clog 2 S.card < f → ∀ q : Fin m → ℝ,
      (hpimNode Y δ f S).cost q ≤ (Nat.clog 2 S.card + 1) * (2 * Vb N m δ + 1) +
        Nat.clog 2 (Kb N δ) * (Vb N m δ + 1) + Vb N m δ + 3 := by
  intro f
  induction f with
  | zero => intro S _ h; omega
  | succ f ih =>
    intro S hS hf q
    by_cases h1 : S.card ≤ 1
    · have hc : S.card = 1 := le_antisymm h1 (Finset.card_pos.2 hS)
      obtain ⟨k, rfl⟩ := Finset.card_eq_one.1 hc
      rw [hpimNode_single]; simp [HTree.cost]
    push Not at h1
    have hS2 : 2 ≤ S.card := h1
    set V := Vb N m δ
    set P := ptsOf Y S
    obtain ⟨⟨i₀, hbig⟩, hmedpos, hsmall⟩ := medThreshold_spec P hS2 (ptsOf_injective Y hY S)
    have hrmed : rmedOf Y S = medThreshold P / 2 := rfl
    have hvis := node_visits_le Y δ hm hY hδ hδ' S hS2 q
    have hlc := fun i => lookupCost_le (ZOf Y δ S) q V hvis i
    have hbc := bisectCost_le (ZOf Y δ S) q V hvis
    have hMK := MOf_le Y δ hY hδ hδ' S hS2
    have ht0 : Nat.clog 2 (MOf Y δ S - 1) ≤ Nat.clog 2 (Kb N δ) := Nat.clog_mono_right 2 hMK
    set L := Nat.clog 2 S.card
    rw [hpimNode_succ_eq Y δ f S (by omega)]
    simp only [HTree.cost]
    rcases h0 : lookup (ZOf Y δ S) 0 q with _ | i
    · simp only
      have hl0 := hlc 0
      have hlM := hlc (MOf Y δ S - 1)
      rcases hMl : lookup (ZOf Y δ S) (MOf Y δ S - 1) q with _ | l
      · simp only
        -- case (ii): recurse into the representatives
        have h2r : 2 * rmedOf Y S = medThreshold P := by rw [hrmed]; ring
        have hcardR : (repsOf Y S).card ≤ (S.card + 1) / 2 := by
          unfold repsOf
          rw [Finset.card_map]
          have := card_reps_le P (2 * rmedOf Y S) i₀ (by rw [h2r]; exact hbig)
          convert this using 2
        have hRne : (repsOf Y S).Nonempty := by
          obtain ⟨j, -, hj⟩ := exists_rep P (2 * rmedOf Y S) i₀
          exact ⟨_, Finset.mem_map_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩)⟩
        have hcl := clog_child hS2 hcardR
        have := ih (repsOf Y S) hRne (by omega) q
        nlinarith
      · simp only
        -- case (iii): the ladder search
        have := hbc (Nat.clog 2 (MOf Y δ S - 1)) 0
        have hlC : lookupCCost (ZOf Y δ S) (bisect (ZOf Y δ S) q (Nat.clog 2 (MOf Y δ S - 1)) 0) q
            ≤ V := hlc _
        nlinarith
    · simp only
      -- case (i): recurse into the bottom component
      obtain ⟨hin, -⟩ := (lookup_node_spec Y δ hm hY hδ hδ' S hS2 0
        (by have := MOf_eq Y δ hY hδ S hS2; omega) (WithLp.toLp 2 q)).1 i (by simpa using h0)
      rw [dif_pos hin]
      have hcardC : (compBotOf Y S ⟨i, hin⟩).card ≤ (S.card + 1) / 2 := by
        unfold compBotOf
        rw [Finset.card_map]
        have := hsmall (2 * (rmedOf Y S / 2)) (by rw [hrmed]; linarith) ⟨i, hin⟩
        refine le_trans (le_of_eq ?_) (this.trans (by omega))
        congr 1
      have hCne : (compBotOf Y S ⟨i, hin⟩).Nonempty :=
        ⟨_, Finset.mem_map_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_univ _,
          SimpleGraph.Reachable.refl _⟩)⟩
      have hcl := clog_child hS2 hcardC
      have := ih _ hCne (by omega) q
      have hl0 := hlc 0
      nlinarith

end CostStructure

theorem hpimTree_cost_aux :
    ∃ C₁ : ℕ, ∀ (m N : ℕ), 1 ≤ m → 1 ≤ N →
      ∀ Y : Fin N → EuclideanSpace ℝ (Fin m), Function.Injective Y →
        ∀ δ : ℝ, 0 < δ → δ < 1 / 2 → ∀ q : EuclideanSpace ℝ (Fin m),
          ((hpimTree Y δ).cost q : ℝ) ≤ C₁ * m * Real.log (N / δ) ^ 2 := by
  refine ⟨15000, ?_⟩
  intro m N hm hN Y hY δ hδ hδ' q
  have hS : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0, hN⟩, Finset.mem_univ _⟩
  have hf : Nat.clog 2 (Finset.univ : Finset (Fin N)).card < N + 1 := by
    rw [Finset.card_univ, Fintype.card_fin]
    have := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self (n := N)).le
    omega
  have h := hpimNode_cost Y δ hm hY hδ hδ' (N + 1) Finset.univ hS hf q
  rw [Finset.card_univ, Fintype.card_fin] at h
  have hc : ((hpimTree Y δ).cost q : ℝ) ≤
      (((Nat.clog 2 N + 1) * (2 * Vb N m δ + 1) + Nat.clog 2 (Kb N δ) * (Vb N m δ + 1) +
        Vb N m δ + 3 : ℕ) : ℝ) := by
    unfold hpimTree; exact_mod_cast h
  push_cast at hc
  obtain ⟨h2, -, -⟩ := logL_facts N hN δ hδ hδ'
  have := final_arith m hm (Real.log (N / δ)) ((Nat.clog 2 N : ℝ) + 1) (Vb N m δ : ℝ)
    (Nat.clog 2 (Kb N δ) : ℝ) h2 (clogN_bound N hN δ hδ hδ') (V_bound m N hm hN δ hδ hδ')
    (Kb_bound N hN δ hδ hδ') (by positivity) (by positivity) (by positivity)
  push_cast
  linarith

end DetANN.HPIM

open DetANN.HPIM in
theorem solution :
    ∃ C₁ : ℕ, ∀ (m N : ℕ), 1 ≤ m → 1 ≤ N →
      ∀ Y : Fin N → EuclideanSpace ℝ (Fin m), Function.Injective Y →
        ∀ δ : ℝ, 0 < δ → δ < 1 / 2 → ∀ q : EuclideanSpace ℝ (Fin m),
          ((hpimTree Y δ).cost q : ℝ) ≤ C₁ * m * Real.log (N / δ) ^ 2 :=
  hpimTree_cost_aux
