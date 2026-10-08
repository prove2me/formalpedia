-- Prove2me | solution 1 for CongestionPoA.SymSum.symmetric_poa_sum_eq
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T19:43:35.306981+00:00
-- url     : https://prove2.me/submissions/61c1f2bd-243f-42ba-82bb-5e4e062b1b1c

import Mathlib
import Definitions.Def_CongestionPoA_SymSum_Model



namespace CongestionPoA.SymSum

open Finset CongestionPoA.AsymSum

theorem ss_load_eq {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (A : ι → Finset E) (e : E) :
    (load A e : ℝ) = ∑ j, if e ∈ A j then (1:ℝ) else 0 := by
  unfold load
  rw [Finset.card_filter]; push_cast; rfl

theorem ss_load_update {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (A : ι → Finset E) (i : ι) (S : Finset E) (e : E) (he : e ∈ S) :
    (load (Function.update A i S) e : ℝ) = load A e + if e ∈ A i then 0 else 1 := by
  rw [ss_load_eq, ss_load_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have : ∑ j ∈ univ.erase i, (if e ∈ Function.update A i S j then (1:ℝ) else 0)
      = ∑ j ∈ univ.erase i, (if e ∈ A j then (1:ℝ) else 0) :=
    Finset.sum_congr rfl (fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)])
  rw [this, Function.update_self]
  by_cases h : e ∈ A i <;> simp [h, he] <;> ring

theorem ss_dev_cost' {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (G : CongestionGame ι E) (a b : E → ℝ) (hlin : ∀ e k, G.latency e k = a e * k + b e)
    (A : ι → Finset E) (i : ι) (S : Finset E) :
    cost G (Function.update A i S) i
      = ∑ e ∈ S, (a e * ((load A e : ℝ) + if e ∈ A i then 0 else 1) + b e) := by
  unfold cost
  rw [Function.update_self]
  refine Finset.sum_congr rfl (fun e he => ?_)
  rw [hlin, ss_load_update A i S e he]

theorem ss_dev_cost {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (G : CongestionGame ι E) (a b : E → ℝ) (hlin : ∀ e k, G.latency e k = a e * k + b e)
    (A : ι → Finset E) (i : ι) (S : Finset E) :
    cost G (Function.update A i S) i
      = ∑ e ∈ S, (a e * (load A e : ℝ) + b e) + ∑ e ∈ S \ A i, a e := by
  rw [ss_dev_cost' G a b hlin, Finset.sdiff_eq_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  split_ifs <;> ring

theorem ss_sumcost {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (A : ι → Finset E) (f : E → ℝ) :
    ∑ i, ∑ e ∈ A i, f e = ∑ e, (load A e : ℝ) * f e := by
  have : ∀ i, ∑ e ∈ A i, f e = ∑ e, if e ∈ A i then f e else 0 := fun i => by
    rw [← Finset.sum_filter]; congr 1; ext; simp
  simp_rw [this]
  rw [Finset.sum_comm]
  congr 1; ext e
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  rfl

theorem nd_core {N : ℕ} {E : Type*} [Fintype E] [DecidableEq E]
    (G : CongestionGame (Fin N) E) (a b : E → ℝ)
    (hlin : ∀ e k, G.latency e k = a e * k + b e) (hsym : IsSymmetric G)
    (A P : Fin N → Finset E) (hA : IsPureNash G A) (hP : IsProfile G P) (i j : Fin N) :
    cost G A i ≤ ∑ e ∈ P j, (a e * (load A e : ℝ) + b e) + ∑ e ∈ P j \ A i, a e := by
  have hmem : P j ∈ G.strategies i := by rw [hsym i j]; exact hP j
  have := hA.2 i (P j) hmem
  rwa [ss_dev_cost G a b hlin] at this

theorem sj_core {N : ℕ} {E : Type*} [Fintype E] [DecidableEq E]
    (G : CongestionGame (Fin N) E) (a b : E → ℝ)
    (hlin : ∀ e k, G.latency e k = a e * k + b e) (hsym : IsSymmetric G)
    (A P : Fin N → Finset E) (hA : IsPureNash G A) (hP : IsProfile G P) (i : Fin N) :
    (N : ℝ) * cost G A i ≤
      ∑ e, (load P e : ℝ) * (a e * (load A e : ℝ) + b e) + ∑ e, a e * (load P e : ℝ)
        - ∑ e ∈ A i, a e * (load P e : ℝ) := by
  have h1 : (N:ℝ) * cost G A i = ∑ _j : Fin N, cost G A i := by simp
  have h2 : ∑ _j : Fin N, cost G A i ≤ ∑ j : Fin N, (∑ e ∈ P j, (a e * (load A e : ℝ) + b e)
      + ∑ e ∈ P j \ A i, a e) :=
    Finset.sum_le_sum (fun j _ => nd_core G a b hlin hsym A P hA hP i j)
  have h3 : ∀ j, ∑ e ∈ P j \ A i, a e
      = ∑ e ∈ P j, a e - ∑ e ∈ P j, (if e ∈ A i then a e else 0) := by
    intro j
    rw [Finset.sdiff_eq_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    split_ifs <;> simp_all
  simp_rw [h3] at h2
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ss_sumcost, ss_sumcost, ss_sumcost] at h2
  have h4 : ∑ e, (load P e : ℝ) * (if e ∈ A i then a e else 0)
      = ∑ e ∈ A i, a e * (load P e : ℝ) := by
    have : ∀ e, (load P e : ℝ) * (if e ∈ A i then a e else 0)
        = if e ∈ A i then a e * load P e else 0 := fun e => by split_ifs <;> ring
    simp_rw [this]; rw [Finset.sum_ite_mem, Finset.univ_inter]
  have h5 : ∑ e, (load P e : ℝ) * a e = ∑ e, a e * (load P e : ℝ) :=
    Finset.sum_congr rfl (fun e _ => by ring)
  linarith

theorem si_mul {N : ℕ} {E : Type*} [Fintype E] [DecidableEq E]
    (G : CongestionGame (Fin N) E) (a b : E → ℝ)
    (hlin : ∀ e k, G.latency e k = a e * k + b e) (hsym : IsSymmetric G)
    (A P : Fin N → Finset E) (hA : IsPureNash G A) (hP : IsProfile G P) :
    (N : ℝ) * sumCost G A ≤
      ((N : ℝ) - 1) * ∑ e, a e * ((load P e : ℝ) * (load A e : ℝ) + (load P e : ℝ))
        + ∑ e, a e * (load P e : ℝ) + N * ∑ e, b e * (load P e : ℝ) := by
  have h1 : (N : ℝ) * sumCost G A = ∑ i, (N : ℝ) * cost G A i := by
    unfold sumCost; rw [Finset.mul_sum]
  have h2 := Finset.sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin N))) =>
    sj_core G a b hlin hsym A P hA hP i)
  rw [Finset.sum_sub_distrib, ss_sumcost] at h2
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h2
  set S1 := ∑ e, a e * ((load P e : ℝ) * (load A e : ℝ))
  set Y := ∑ e, a e * (load P e : ℝ)
  set S3 := ∑ e, b e * (load P e : ℝ)
  have e1 : ∑ e, (load P e : ℝ) * (a e * (load A e : ℝ) + b e) = S1 + S3 := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun e _ => by ring)
  have e2 : ∑ e, (load A e : ℝ) * (a e * (load P e : ℝ)) = S1 :=
    Finset.sum_congr rfl (fun e _ => by ring)
  have e3 : ∑ e, a e * ((load P e : ℝ) * (load A e : ℝ) + (load P e : ℝ)) = S1 + Y := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun e _ => by ring)
  rw [e3]
  rw [e1, e2] at h2
  nlinarith

theorem si_core {N : ℕ} (hN : 1 ≤ N) {E : Type*} [Fintype E] [DecidableEq E]
    (G : CongestionGame (Fin N) E) (a b : E → ℝ)
    (hlin : ∀ e k, G.latency e k = a e * k + b e) (hsym : IsSymmetric G)
    (A P : Fin N → Finset E) (hA : IsPureNash G A) (hP : IsProfile G P) :
    sumCost G A ≤
      ((N : ℝ) - 1) / N * ∑ e, a e * ((load P e : ℝ) * (load A e : ℝ) + (load P e : ℝ))
        + 1 / (N : ℝ) * ∑ e, a e * (load P e : ℝ) + ∑ e, b e * (load P e : ℝ) := by
  have hm := si_mul G a b hlin hsym A P hA hP
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  set Q := ∑ e, a e * ((load P e : ℝ) * (load A e : ℝ) + (load P e : ℝ))
  set Y := ∑ e, a e * (load P e : ℝ)
  set S3 := ∑ e, b e * (load P e : ℝ)
  have hR : (N : ℝ) * (((N : ℝ) - 1) / N * Q + 1 / (N : ℝ) * Y + S3)
      = ((N : ℝ) - 1) * Q + Y + N * S3 := by
    field_simp
  by_contra h
  push_neg at h
  have := mul_lt_mul_of_pos_left h hNpos
  linarith

theorem ss_int (x y : ℕ) : 3 * ((y : ℝ) * x + y) ≤ (x : ℝ) ^ 2 + 5 * (y : ℝ) ^ 2 := by
  have key : 3 * (y * x + y) ≤ x ^ 2 + 5 * y ^ 2 := by
    rcases Nat.lt_or_ge y 2 with hy | hy
    · interval_cases y
      · simp
      · rcases Nat.lt_or_ge x 2 with hx | hx
        · interval_cases x <;> simp
        · nlinarith
    · nlinarith [sq_nonneg ((2 * x : ℤ) - 3 * y)]
  exact_mod_cast key

theorem t3_core {N : ℕ} (hN : 1 ≤ N) {E : Type*} [Fintype E] [DecidableEq E]
    (G : CongestionGame (Fin N) E) (hlin : IsLinear G) (hsym : IsSymmetric G)
    (A P : Fin N → Finset E) (hA : IsPureNash G A) (hP : IsProfile G P) :
    sumCost G A ≤ (5 * (N : ℝ) - 2) / (2 * (N : ℝ) + 1) * sumCost G P := by
  obtain ⟨a, b, ha, hb, hl⟩ := hlin
  have hm := si_mul G a b hl hsym A P hA hP
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hsc : ∀ X : Fin N → Finset E, sumCost G X
      = ∑ e, a e * (load X e : ℝ) ^ 2 + ∑ e, b e * (load X e : ℝ) := by
    intro X
    unfold sumCost cost
    simp_rw [hl]
    rw [ss_sumcost, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun e _ => by ring)
  rw [hsc A, hsc P] at *
  set Q := ∑ e, a e * ((load P e : ℝ) * (load A e : ℝ) + (load P e : ℝ))
  set Y := ∑ e, a e * (load P e : ℝ)
  set SAa := ∑ e, a e * (load A e : ℝ) ^ 2
  set SAb := ∑ e, b e * (load A e : ℝ)
  set SPa := ∑ e, a e * (load P e : ℝ) ^ 2
  set SPb := ∑ e, b e * (load P e : ℝ)
  have hQ : 3 * Q ≤ SAa + 5 * SPa := by
    simp only [Q, SAa, SPa, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun e _ => by
      have := ss_int (load A e) (load P e)
      have := ha e
      nlinarith)
  have hY : Y ≤ SPa := by
    exact Finset.sum_le_sum (fun e _ => by
      have h0 : (load P e : ℝ) ≤ (load P e : ℝ) ^ 2 := by
        rcases Nat.eq_zero_or_pos (load P e) with h | h
        · rw [h]; simp
        · have : (1:ℝ) ≤ load P e := by exact_mod_cast h
          nlinarith
      exact mul_le_mul_of_nonneg_left h0 (ha e))
  have hSAb : 0 ≤ SAb := Finset.sum_nonneg (fun e _ => mul_nonneg (hb e) (Nat.cast_nonneg _))
  have hSPb : 0 ≤ SPb := Finset.sum_nonneg (fun e _ => mul_nonneg (hb e) (Nat.cast_nonneg _))
  have hpos : (0:ℝ) < 2 * N + 1 := by linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
  have hq2 := mul_le_mul_of_nonneg_left hQ (by linarith : (0:ℝ) ≤ N - 1)
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ N - 1) hSAb,
    mul_nonneg (by linarith : (0:ℝ) ≤ N - 1) hSPb]

abbrev TE (N : ℕ) := Fin N × Fin N × Fin N

def tP (N : ℕ) (i : Fin N) : Finset (TE N) := univ.filter (fun e => e.1 = i)
def tA (N : ℕ) (k : Fin N) : Finset (TE N) := univ.filter (fun e => e.2.1 = k ∨ e.2.2 = k)
noncomputable def ta (N : ℕ) (e : TE N) : ℝ := if e.2.1 = e.2.2 then (N:ℝ) + 2 else 1
noncomputable def tG (N : ℕ) : CongestionGame (Fin N) (TE N) :=
  { strategies := fun _ => univ.image (tP N) ∪ univ.image (tA N),
    latency := fun e k => ta N e * k }

theorem tP_load (N : ℕ) (e : TE N) : load (tP N) e = 1 := by
  unfold load tP
  have : univ.filter (fun i : Fin N => e ∈ univ.filter (fun e : TE N => e.1 = i)) = {e.1} := by
    ext i; simp [eq_comm]
  rw [this, card_singleton]

theorem tA_load (N : ℕ) (e : TE N) :
    (load (tA N) e : ℝ) = if e.2.1 = e.2.2 then 1 else 2 := by
  unfold load tA
  have : univ.filter (fun i : Fin N => e ∈ univ.filter (fun e : TE N => e.2.1 = i ∨ e.2.2 = i))
      = {e.2.1, e.2.2} := by
    ext i; simp [eq_comm]
  rw [this]
  by_cases h : e.2.1 = e.2.2
  · rw [h]; simp
  · rw [Finset.card_pair h]; simp [h]

theorem t_sum_all (N : ℕ) (g : Fin N → Fin N → ℝ) :
    ∑ e : TE N, g e.2.1 e.2.2 = N * ∑ m, ∑ l, g m l := by
  rw [Fintype.sum_prod_type]
  simp [Fintype.sum_prod_type]

theorem t_sum_tP (N : ℕ) (j : Fin N) (f : TE N → ℝ) :
    ∑ e ∈ tP N j, f e = ∑ m, ∑ l, f (j, m, l) := by
  unfold tP
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb; simp [hb]
  · simp

theorem t_dsum1 (N : ℕ) (k : Fin N) :
    ∑ m : Fin N, ∑ l : Fin N, (2 * (if m = k then (1:ℝ) else 0) + 2 * (if l = k then (1:ℝ) else 0)
      + ((N:ℝ) - 2) * ((if m = k then (1:ℝ) else 0) * (if l = k then (1:ℝ) else 0)))
      = 5 * N - 2 := by
  simp [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

theorem t_dsum2 (N : ℕ) (k : Fin N) :
    ∑ m : Fin N, ∑ l : Fin N, (3 + (2 * (N:ℝ) + 1) * (if m = l then (1:ℝ) else 0)
      - (if m = k then (1:ℝ) else 0) - (if l = k then (1:ℝ) else 0)
      - (N:ℝ) * ((if m = k then (1:ℝ) else 0) * (if l = k then (1:ℝ) else 0)))
      = 5 * (N:ℝ) ^ 2 - 2 * N := by
  simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

theorem t_dsum3 (N : ℕ) :
    ∑ m : Fin N, ∑ l : Fin N, (1 + ((N:ℝ) + 1) * (if m = l then (1:ℝ) else 0))
      = 2 * (N:ℝ) ^ 2 + N := by
  simp [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

theorem tG_lat (N : ℕ) : ∀ e k, (tG N).latency e k = ta N e * k + (fun _ => (0:ℝ)) e := by
  intro e k; simp [tG]

theorem t_costA (N : ℕ) (k : Fin N) : cost (tG N) (tA N) k = N * (5 * N - 2) := by
  calc cost (tG N) (tA N) k = ∑ e ∈ tA N k, ta N e * (load (tA N) e : ℝ) := rfl
  _ = ∑ e : TE N, (fun m l => 2 * (if m = k then (1:ℝ) else 0) + 2 * (if l = k then (1:ℝ) else 0)
      + ((N:ℝ) - 2) * ((if m = k then (1:ℝ) else 0) * (if l = k then (1:ℝ) else 0))) e.2.1 e.2.2 := by
      rw [show tA N k = univ.filter (fun e : TE N => e.2.1 = k ∨ e.2.2 = k) from rfl, Finset.sum_filter]
      refine Finset.sum_congr rfl (fun e _ => ?_)
      obtain ⟨i, m, l⟩ := e
      rw [tA_load]; simp only [ta]
      by_cases h1 : m = k <;> by_cases h2 : l = k <;> by_cases h3 : m = l <;> simp_all <;> ring_nf
  _ = N * (5 * N - 2) := by
      rw [t_sum_all N (fun m l => 2 * (if m = k then (1:ℝ) else 0) + 2 * (if l = k then (1:ℝ) else 0)
        + ((N:ℝ) - 2) * ((if m = k then (1:ℝ) else 0) * (if l = k then (1:ℝ) else 0))), t_dsum1]

theorem t_costP (N : ℕ) (i : Fin N) : cost (tG N) (tP N) i = 2 * (N:ℝ) ^ 2 + N := by
  calc cost (tG N) (tP N) i = ∑ e ∈ tP N i, ta N e * (load (tP N) e : ℝ) := rfl
  _ = ∑ m : Fin N, ∑ l : Fin N, (1 + ((N:ℝ) + 1) * (if m = l then (1:ℝ) else 0)) := by
      rw [t_sum_tP]
      refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun l _ => ?_))
      rw [tP_load]; simp only [ta]
      by_cases h3 : m = l <;> simp_all <;> ring_nf
  _ = 2 * (N:ℝ) ^ 2 + N := t_dsum3 N

theorem t_devP (N : ℕ) (k j : Fin N) :
    cost (tG N) (Function.update (tA N) k (tP N j)) k = 5 * (N:ℝ) ^ 2 - 2 * N := by
  rw [ss_dev_cost' (tG N) (ta N) _ (tG_lat N), t_sum_tP, ← t_dsum2 N k]
  refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun l _ => ?_))
  rw [tA_load]; simp only [ta, tA, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases h1 : m = k <;> by_cases h2 : l = k <;> by_cases h3 : m = l <;> simp_all <;> ring_nf

theorem t_nash (N : ℕ) : IsPureNash (tG N) (tA N) := by
  refine ⟨fun k => ?_, fun k S hS => ?_⟩
  · simp [tG]
  · simp only [tG, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hS
    rcases hS with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [t_devP, t_costA]; ring_nf; rfl
    · rw [ss_dev_cost (tG N) (ta N) _ (tG_lat N), t_costA]
      have h1 : ∑ e ∈ tA N j, (ta N e * (load (tA N) e : ℝ) + 0) = N * (5 * N - 2) := by
        simp only [add_zero]; exact t_costA N j
      have h2 : 0 ≤ ∑ e ∈ tA N j \ tA N k, ta N e :=
        Finset.sum_nonneg (fun e _ => by unfold ta; split_ifs <;> positivity)
      linarith

theorem t4_core (N : ℕ) (hN : 1 ≤ N) :
    ∃ (E : Type) (_ : Fintype E) (_ : DecidableEq E) (G : CongestionGame (Fin N) E)
      (A P : Fin N → Finset E),
      IsLinear G ∧ IsSymmetric G ∧ IsPureNash G A ∧ IsProfile G P ∧ 0 < sumCost G P ∧
        sumCost G A = (5 * (N : ℝ) - 2) / (2 * (N : ℝ) + 1) * sumCost G P := by
  refine ⟨TE N, inferInstance, inferInstance, tG N, tA N, tP N, ?_, ?_, t_nash N, ?_, ?_, ?_⟩
  · exact ⟨ta N, fun _ => 0, fun e => by unfold ta; split_ifs <;> positivity,
      fun _ => le_refl _, tG_lat N⟩
  · intro i j; rfl
  · intro i; simp [tG]
  · unfold sumCost; simp only [t_costP]; simp
    have : (1:ℝ) ≤ N := by exact_mod_cast hN
    positivity
  · unfold sumCost; simp only [t_costP, t_costA]; simp
    have : (1:ℝ) ≤ N := by exact_mod_cast hN
    field_simp

theorem goal_core (N : ℕ) (hN : 1 ≤ N) :
    (∀ (E : Type) [Fintype E] [DecidableEq E] (G : CongestionGame (Fin N) E)
        (A P : Fin N → Finset E),
        IsLinear G → IsSymmetric G → IsPureNash G A → IsProfile G P →
          sumCost G A ≤ (5 * (N : ℝ) - 2) / (2 * (N : ℝ) + 1) * sumCost G P) ∧
    ∃ (E : Type) (_ : Fintype E) (_ : DecidableEq E) (G : CongestionGame (Fin N) E)
      (A P : Fin N → Finset E),
      IsLinear G ∧ IsSymmetric G ∧ IsPureNash G A ∧ IsProfile G P ∧ 0 < sumCost G P ∧
        sumCost G A = (5 * (N : ℝ) - 2) / (2 * (N : ℝ) + 1) * sumCost G P :=
  ⟨fun E _ _ G A P hl hs hA hP => t3_core hN G hl hs A P hA hP, t4_core N hN⟩

end CongestionPoA.SymSum

open CongestionPoA.SymSum


theorem solution (N : ℕ) (hN : 1 ≤ N) :
    (∀ (E : Type) [Fintype E] [DecidableEq E] (G : CongestionPoA.AsymSum.CongestionGame (Fin N) E)
        (A P : Fin N → Finset E),
        CongestionPoA.AsymSum.IsLinear G → IsSymmetric G → CongestionPoA.AsymSum.IsPureNash G A → CongestionPoA.AsymSum.IsProfile G P →
          CongestionPoA.AsymSum.sumCost G A ≤ (5 * (N : ℝ) - 2) / (2 * (N : ℝ) + 1) * CongestionPoA.AsymSum.sumCost G P) ∧
    ∃ (E : Type) (_ : Fintype E) (_ : DecidableEq E) (G : CongestionPoA.AsymSum.CongestionGame (Fin N) E)
      (A P : Fin N → Finset E),
      CongestionPoA.AsymSum.IsLinear G ∧ IsSymmetric G ∧ CongestionPoA.AsymSum.IsPureNash G A ∧ CongestionPoA.AsymSum.IsProfile G P ∧ 0 < CongestionPoA.AsymSum.sumCost G P ∧
        CongestionPoA.AsymSum.sumCost G A = (5 * (N : ℝ) - 2) / (2 * (N : ℝ) + 1) * CongestionPoA.AsymSum.sumCost G P := by
  exact goal_core N hN
