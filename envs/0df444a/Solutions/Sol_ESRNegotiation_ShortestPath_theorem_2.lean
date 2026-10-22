-- Prove2me | solution 1 for ESRNegotiation.ShortestPath.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T01:35:20.919347+00:00
-- url     : https://prove2.me/submissions/7e3eda96-f37d-49a1-89fe-255f39c3cabf

import Mathlib
import Definitions.Def_ESRNegotiation_ShortestPath_Model

set_option autoImplicit false

open ESRNegotiation.ShortestPath in
theorem esr9704_iter_zero {n : ℕ} {N : Network n} (T : Structure N) (k : ℕ) :
    (T.val^[k]) 0 = 0 :=
  Function.iterate_fixed T.property.1 k

open ESRNegotiation.ShortestPath in
theorem esr9704_depth_spec {n : ℕ} {N : Network n} (T : Structure N) (j : Fin (n + 1)) :
    (T.val^[depth T j]) j = 0 :=
  Nat.find_spec (T.property.2.2 j)

open ESRNegotiation.ShortestPath in
theorem esr9704_lt_depth {n : ℕ} {N : Network n} (T : Structure N) (j : Fin (n + 1))
    {m : ℕ} (hm : m < depth T j) : (T.val^[m]) j ≠ 0 :=
  Nat.find_min (T.property.2.2 j) hm

open ESRNegotiation.ShortestPath in
theorem esr9704_iter_inj {n : ℕ} {N : Network n} (T : Structure N) (j : Fin (n + 1))
    {a b : ℕ} (hab : a < b) (hb : b ≤ depth T j) : (T.val^[a]) j ≠ (T.val^[b]) j := by
  intro h
  have hper : ∀ x, (T.val^[a + x + (b - a)]) j = (T.val^[a + x]) j := by
    intro x
    have e : a + x + (b - a) = x + b := by omega
    rw [e, Function.iterate_add_apply, ← h, ← Function.iterate_add_apply, Nat.add_comm x a]
  have := hper (depth T j - b)
  rw [show a + (depth T j - b) + (b - a) = depth T j by omega, esr9704_depth_spec] at this
  exact esr9704_lt_depth T j (m := a + (depth T j - b)) (by omega) this.symm

open ESRNegotiation.ShortestPath in
theorem esr9704_par_ne {n : ℕ} {N : Network n} (T : Structure N) (j : Fin (n + 1))
    (hj : j ≠ 0) : T.val j ≠ j := by
  intro h
  have := esr9704_depth_spec T j
  rw [Function.iterate_fixed h] at this
  exact hj this

open ESRNegotiation.ShortestPath in
theorem esr9704_arc {n : ℕ} {N : Network n} (T : Structure N) (j : Fin (n + 1))
    {m : ℕ} (hm : m < depth T j) : esr N ((T.val^[m + 1]) j) ((T.val^[m]) j) := by
  have hne := esr9704_lt_depth T j hm
  have := T.property.2.1 _ hne
  rwa [Function.iterate_succ_apply']

open ESRNegotiation.ShortestPath in
theorem esr9704_rho_pos {n : ℕ} {N : Network n} (hS : Standing N) {i j : Fin (n + 1)}
    (h : esr N i j) : 0 < rho N i j := by
  obtain ⟨h0, h1⟩ := hS.1 i j h
  unfold rho
  apply div_pos <;> linarith

open ESRNegotiation.ShortestPath in
theorem esr9704_pathProd_eq {n : ℕ} {N : Network n} (T : Structure N) (v : Fin (n + 1)) :
    pathProd N T v = ((List.range (depth T v)).map
      (fun m => rho N ((T.val^[m + 1]) v) ((T.val^[m]) v))).prod := by
  unfold pathProd rootPath
  rw [List.map_map]
  rfl

open ESRNegotiation.ShortestPath in
theorem esr9704_rootCost_eq {n : ℕ} {N : Network n} (T : Structure N) (v : Fin (n + 1)) :
    rootCost N T v = ((List.range (depth T v)).map
      (fun m => Real.log (rho N ((T.val^[m + 1]) v) ((T.val^[m]) v)))).sum := by
  unfold rootCost rootPath
  rw [List.map_map]
  rfl

theorem esr9704_prod_exp (f : ℕ → ℝ) (k : ℕ) (hf : ∀ m < k, 0 < f m) :
    ((List.range k).map f).prod =
      Real.exp (((List.range k).map (fun m => Real.log (f m))).sum) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.prod_range_succ, List.sum_range_succ, Real.exp_add,
      ih (fun m hm => hf m (by omega)), Real.exp_log (hf k (by omega))]

open ESRNegotiation.ShortestPath in
theorem esr9704_pathProd_exp {n : ℕ} {N : Network n} (hS : Standing N) (T : Structure N)
    (v : Fin (n + 1)) : pathProd N T v = Real.exp (rootCost N T v) := by
  rw [esr9704_pathProd_eq, esr9704_rootCost_eq]
  exact esr9704_prod_exp _ _ (fun m hm => esr9704_rho_pos hS (esr9704_arc T v hm))

open ESRNegotiation.ShortestPath in
theorem esr9704_pathProd_pos {n : ℕ} {N : Network n} (hS : Standing N) (T : Structure N)
    (v : Fin (n + 1)) : 0 < pathProd N T v := by
  rw [esr9704_pathProd_exp hS]
  exact Real.exp_pos _

/-- The list `f^[k] j, f^[k-1] j, ..., j`. -/
def esr9704_upL {α : Type} (f : α → α) (j : α) : ℕ → List α
  | 0 => [j]
  | k + 1 => (f^[k + 1]) j :: esr9704_upL f j k

theorem esr9704_upL_head {α : Type} (f : α → α) (j : α) (k : ℕ) :
    ∃ t, esr9704_upL f j k = (f^[k]) j :: t := by
  cases k with
  | zero => exact ⟨[], rfl⟩
  | succ k => exact ⟨esr9704_upL f j k, rfl⟩

theorem esr9704_upL_last {α : Type} (f : α → α) (j : α) (k : ℕ) :
    (esr9704_upL f j k).getLast? = some j := by
  induction k with
  | zero => rfl
  | succ k ih =>
    obtain ⟨t, ht⟩ := esr9704_upL_head f j k
    show ((f^[k + 1]) j :: esr9704_upL f j k).getLast? = some j
    rw [ht, List.getLast?_cons_cons, ← ht]
    exact ih

theorem esr9704_upL_mem {α : Type} (f : α → α) (j : α) (k : ℕ) (x : α)
    (h : x ∈ esr9704_upL f j k) : ∃ m ≤ k, x = (f^[m]) j := by
  induction k with
  | zero =>
    simp [esr9704_upL] at h
    exact ⟨0, le_rfl, h⟩
  | succ k ih =>
    simp only [esr9704_upL, List.mem_cons] at h
    rcases h with h | h
    · exact ⟨k + 1, le_rfl, h⟩
    · obtain ⟨m, hm, hx⟩ := ih h
      exact ⟨m, by omega, hx⟩

open ESRNegotiation.ShortestPath in
theorem esr9704_pathCost_cons2 {n : ℕ} (N : Network n) (a b : Fin (n + 1))
    (t : List (Fin (n + 1))) :
    pathCost N (a :: b :: t) = Real.log (rho N a b) + pathCost N (b :: t) := by
  simp [pathCost]

open ESRNegotiation.ShortestPath in
theorem esr9704_upL_cost {n : ℕ} (N : Network n) (f : Fin (n + 1) → Fin (n + 1))
    (j : Fin (n + 1)) (k : ℕ) :
    pathCost N (esr9704_upL f j k) =
      ((List.range k).map (fun m => Real.log (rho N ((f^[m + 1]) j) ((f^[m]) j)))).sum := by
  induction k with
  | zero => simp [esr9704_upL, pathCost]
  | succ k ih =>
    obtain ⟨t, ht⟩ := esr9704_upL_head f j k
    show pathCost N ((f^[k + 1]) j :: esr9704_upL f j k) = _
    rw [ht, esr9704_pathCost_cons2, ← ht, ih, List.sum_range_succ]
    ring

open ESRNegotiation.ShortestPath in
theorem esr9704_upL_chain {n : ℕ} {N : Network n} (T : Structure N) (j : Fin (n + 1))
    (k : ℕ) (hk : k ≤ depth T j) : (esr9704_upL T.val j k).Chain' (esr N) := by
  induction k with
  | zero => exact List.IsChain.singleton _
  | succ k ih =>
    obtain ⟨t, ht⟩ := esr9704_upL_head T.val j k
    show ((T.val^[k + 1]) j :: esr9704_upL T.val j k).Chain' (esr N)
    rw [ht]
    refine List.isChain_cons_cons.2 ⟨esr9704_arc T j (by omega), ?_⟩
    rw [← ht]
    exact ih (by omega)

open ESRNegotiation.ShortestPath in
theorem esr9704_upL_nodup {n : ℕ} {N : Network n} (T : Structure N) (j : Fin (n + 1))
    (k : ℕ) (hk : k ≤ depth T j) : (esr9704_upL T.val j k).Nodup := by
  induction k with
  | zero => simp [esr9704_upL]
  | succ k ih =>
    show ((T.val^[k + 1]) j :: esr9704_upL T.val j k).Nodup
    refine List.nodup_cons.2 ⟨?_, ih (by omega)⟩
    intro h
    obtain ⟨m, hm, hx⟩ := esr9704_upL_mem _ _ _ _ h
    exact esr9704_iter_inj T j (a := m) (b := k + 1) (by omega) hk hx.symm

open ESRNegotiation.ShortestPath in
theorem esr9704_part1 {n : ℕ} {N : Network n} (hS : Standing N) (Tstar : Structure N)
    (hshort : IsShortestPathTree N Tstar) (T : Structure N) :
    Gamma N Tstar ≤ Gamma N T := by
  unfold Gamma
  apply Finset.sum_le_sum
  intro v hv
  have hv0 : v ≠ 0 := Finset.ne_of_mem_erase hv
  rw [esr9704_pathProd_exp hS, esr9704_pathProd_exp hS]
  apply Real.exp_le_exp.2
  have hl : IsESRPath N v (esr9704_upL T.val v (depth T v)) := by
    refine ⟨?_, esr9704_upL_last _ _ _, esr9704_upL_chain T v _ le_rfl,
      esr9704_upL_nodup T v _ le_rfl⟩
    obtain ⟨t, ht⟩ := esr9704_upL_head T.val v (depth T v)
    rw [ht, esr9704_depth_spec]
    rfl
  have := hshort v hv0 _ hl
  rw [esr9704_upL_cost, ← esr9704_rootCost_eq] at this
  exact this

open ESRNegotiation.ShortestPath in
theorem esr9704_gain_update {n : ℕ} (N : Network n) (T : Structure N) (w : Fin (n + 1) → ℝ)
    (j : Fin (n + 1)) (y : ℝ) (i : Fin (n + 1)) :
    gain N T (Function.update w j y) i = gain N T w i +
      (if j ≠ 0 ∧ T.val j = i then y - w j else 0) -
      (if i = 0 then 0 else (if i = j then y - w j else 0)) := by
  have hu : ∀ k, Function.update w j y k = w k + (if k = j then y - w j else 0) := by
    intro k
    by_cases hk : k = j
    · subst hk; simp
    · simp [hk]
  unfold gain
  simp only [hu]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs <;> ring

theorem esr9704_amgm {θ a b : ℝ} (h0 : 0 < θ) (h1 : θ < 1) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : (θ * (a + b)) ^ θ * ((1 - θ) * (a + b)) ^ (1 - θ) ≤ a ^ θ * b ^ (1 - θ)) :
    b = (1 - θ) / θ * a := by
  have hs : 0 ≤ a + b := by linarith
  have h1' : (0 : ℝ) < 1 - θ := by linarith
  have hK : 0 < θ ^ θ * (1 - θ) ^ (1 - θ) := by positivity
  have hθθ : 0 < θ ^ θ := by positivity
  have hθθ' : 0 < (1 - θ) ^ (1 - θ) := by positivity
  have e1 : (θ * (a + b)) ^ θ * ((1 - θ) * (a + b)) ^ (1 - θ) =
      θ ^ θ * (1 - θ) ^ (1 - θ) * (a + b) := by
    rw [Real.mul_rpow h0.le hs, Real.mul_rpow h1'.le hs]
    have hss : (a + b) ^ θ * (a + b) ^ (1 - θ) = a + b := by
      rw [← Real.rpow_add' hs (by norm_num), add_sub_cancel, Real.rpow_one]
    calc θ ^ θ * (a + b) ^ θ * ((1 - θ) ^ (1 - θ) * (a + b) ^ (1 - θ))
        = θ ^ θ * (1 - θ) ^ (1 - θ) * ((a + b) ^ θ * (a + b) ^ (1 - θ)) := by ring
      _ = _ := by rw [hss]
  have e2 : a ^ θ * b ^ (1 - θ) =
      θ ^ θ * (1 - θ) ^ (1 - θ) * ((a / θ) ^ θ * (b / (1 - θ)) ^ (1 - θ)) := by
    rw [Real.div_rpow ha h0.le, Real.div_rpow hb h1'.le]
    field_simp
  have amgm := Real.geom_mean_le_arith_mean2_weighted (w₁ := θ) (w₂ := 1 - θ)
    (p₁ := a / θ) (p₂ := b / (1 - θ)) h0.le h1'.le (div_nonneg ha h0.le)
    (div_nonneg hb h1'.le) (by ring)
  have hsum : θ * (a / θ) + (1 - θ) * (b / (1 - θ)) = a + b := by
    field_simp
  have heq : (a / θ) ^ θ * (b / (1 - θ)) ^ (1 - θ) =
      θ * (a / θ) + (1 - θ) * (b / (1 - θ)) := by
    apply le_antisymm amgm
    rw [hsum]
    rw [e1, e2] at h
    exact le_of_mul_le_mul_left h hK
  rw [Real.geom_mean_eq_arith_mean2_weighted_iff_of_pos h0 h1' (div_nonneg ha h0.le)
    (div_nonneg hb h1'.le) (by ring)] at heq
  have hθne : θ ≠ 0 := h0.ne'
  have h1ne : 1 - θ ≠ 0 := h1'.ne'
  field_simp at heq ⊢
  linarith

open ESRNegotiation.ShortestPath in
theorem esr9704_nash_ratio {n : ℕ} {N : Network n} (hS : Standing N) (T : Structure N)
    (w : Fin (n + 1) → ℝ) (hNN : IsNashNash N T w) (j : Fin (n + 1)) (hj : j ≠ 0) :
    gain N T w j = rho N (T.val j) j * gain N T w (T.val j) := by
  have hpj : T.val j ≠ j := esr9704_par_ne T j hj
  have hesr : esr N (T.val j) j := T.property.2.1 j hj
  obtain ⟨hθ0, hθ1⟩ := hS.1 _ _ hesr
  obtain ⟨ha, hb, hmax⟩ := hNN j hj
  have hga : ∀ y, gain N T (Function.update w j y) (T.val j) =
      gain N T w (T.val j) + (y - w j) := by
    intro y
    rw [esr9704_gain_update]
    simp [hj, hpj]
  have hgb : ∀ y, gain N T (Function.update w j y) j = gain N T w j - (y - w j) := by
    intro y
    rw [esr9704_gain_update]
    simp [hj, hpj]
  have hs : 0 ≤ gain N T w (T.val j) + gain N T w j := by linarith
  have key := hmax (w j + (N.θ (T.val j) j * (gain N T w (T.val j) + gain N T w j)
      - gain N T w (T.val j)))
    (by rw [hga]; ring_nf; positivity)
    (by rw [hgb]; nlinarith)
  simp only [nashProduct] at key
  rw [hga, hgb] at key
  have e1 : gain N T w (T.val j) + (w j + (N.θ (T.val j) j * (gain N T w (T.val j) +
      gain N T w j) - gain N T w (T.val j)) - w j) =
      N.θ (T.val j) j * (gain N T w (T.val j) + gain N T w j) := by ring
  have e2 : gain N T w j - (w j + (N.θ (T.val j) j * (gain N T w (T.val j) +
      gain N T w j) - gain N T w (T.val j)) - w j) =
      (1 - N.θ (T.val j) j) * (gain N T w (T.val j) + gain N T w j) := by ring
  rw [e1, e2] at key
  exact esr9704_amgm hθ0 hθ1 ha hb key

open ESRNegotiation.ShortestPath in
theorem esr9704_gain_iter {n : ℕ} {N : Network n} (hS : Standing N) (T : Structure N)
    (w : Fin (n + 1) → ℝ) (hNN : IsNashNash N T w) (v : Fin (n + 1)) :
    ∀ k ≤ depth T v, gain N T w v = ((List.range k).map
      (fun m => rho N ((T.val^[m + 1]) v) ((T.val^[m]) v))).prod * gain N T w ((T.val^[k]) v) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    rw [ih (by omega), List.prod_range_succ, esr9704_nash_ratio hS T w hNN _
      (esr9704_lt_depth T v (by omega)), ← Function.iterate_succ_apply' T.val k v]
    ring

open ESRNegotiation.ShortestPath in
theorem esr9704_sum_gain {n : ℕ} (N : Network n) (T : Structure N) (w : Fin (n + 1) → ℝ) :
    ∑ i, gain N T w i = PiGain N := by
  have h1 : ∑ i, ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).filter
      (fun j => j ≠ 0 ∧ T.val j = i), w j = ∑ i, (if i = 0 then 0 else w i) := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases hj : j = 0
    · simp [hj]
    · simp [hj]
  unfold gain PiGain
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [h1]
  simp

open ESRNegotiation.ShortestPath in
theorem esr9704_gain_root {n : ℕ} {N : Network n} (hS : Standing N) (T : Structure N)
    (w : Fin (n + 1) → ℝ) (hNN : IsNashNash N T w) :
    gain N T w 0 * (1 + Gamma N T) = PiGain N := by
  have hsum := esr9704_sum_gain N T w
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 0)] at hsum
  have hv : ∀ v ∈ (Finset.univ : Finset (Fin (n + 1))).erase 0,
      gain N T w v = pathProd N T v * gain N T w 0 := by
    intro v _
    have := esr9704_gain_iter hS T w hNN v (depth T v) le_rfl
    rw [esr9704_depth_spec] at this
    rw [esr9704_pathProd_eq]
    exact this
  rw [Finset.sum_congr rfl hv, ← Finset.sum_mul] at hsum
  unfold Gamma
  rw [← hsum]
  ring

open ESRNegotiation.ShortestPath in
theorem esr9704_Gamma_nonneg {n : ℕ} {N : Network n} (hS : Standing N) (T : Structure N) :
    0 ≤ Gamma N T :=
  Finset.sum_nonneg (fun v _ => (esr9704_pathProd_pos hS T v).le)

open ESRNegotiation.ShortestPath in
theorem solution {n : ℕ} (N : Network n) (hN : Standing N)
    (Tstar : Structure N) (hshort : IsShortestPathTree N Tstar) :
    (∀ T : Structure N, Gamma N Tstar ≤ Gamma N T) ∧
    (∀ T : Structure N, ∀ wstar w : Fin (n + 1) → ℝ,
      IsNashNash N Tstar wstar → IsNashNash N T w →
        gain N T w 0 ≤ gain N Tstar wstar 0) := by
  refine ⟨esr9704_part1 hN Tstar hshort, ?_⟩
  intro T wstar w hs hw
  have h1 := esr9704_gain_root hN Tstar wstar hs
  have h2 := esr9704_gain_root hN T w hw
  have hΓs := esr9704_Gamma_nonneg hN Tstar
  have hΓ := esr9704_part1 hN Tstar hshort T
  have hP := hN.2.2.2
  have g1 : gain N Tstar wstar 0 = PiGain N / (1 + Gamma N Tstar) := by
    rw [eq_div_iff (by linarith)]
    exact h1
  have g2 : gain N T w 0 = PiGain N / (1 + Gamma N T) := by
    rw [eq_div_iff (by linarith)]
    exact h2
  rw [g1, g2]
  apply div_le_div_of_nonneg_left hP.le (by linarith) (by linarith)
