-- Prove2me | solution 1 for DQI.Semicircle.eq_131
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T00:45:00.757435+00:00
-- url     : https://prove2.me/submissions/6b8f0e0b-5357-4005-8742-93dc909767b7

import Mathlib
import Definitions.Def_DQI_Semicircle_Setting

namespace Aux_DQI_Semicircle_eq_131

open DQI.Semicircle

/-! ## Elementary symmetric functions of multisets -/

lemma esymm_cons_succ (a : ℝ) (s : Multiset ℝ) (k : ℕ) :
    (a ::ₘ s).esymm (k + 1) = s.esymm (k + 1) + a * s.esymm k := by
  simp only [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_add, Multiset.sum_add,
    Multiset.map_map, Function.comp_def, Multiset.prod_cons, Multiset.sum_map_mul_left]

lemma esymm_zero' (s : Multiset ℝ) : s.esymm 0 = 1 := by
  simp [Multiset.esymm]

lemma esymm_nil (j : ℕ) : (0 : Multiset ℝ).esymm j = if j = 0 then 1 else 0 := by
  rcases j with _ | j
  · simp [esymm_zero']
  · simp [Multiset.esymm, Multiset.powersetCard_zero_right]

lemma esymm_rec (α β : ℝ) : ∀ s : Multiset ℝ, (∀ v ∈ s, v ^ 2 = α + β * v) → ∀ k : ℕ,
    s.esymm (k + 1) * s.esymm 1 = ((k : ℝ) + 2) * s.esymm (k + 1 + 1) +
      α * ((Multiset.card s : ℝ) - k) * s.esymm k + β * ((k : ℝ) + 1) * s.esymm (k + 1) := by
  intro s
  induction s using Multiset.induction_on with
  | empty =>
    intro _ k
    simp only [esymm_nil, Multiset.card_zero]
    rcases k with _ | k <;> simp
  | cons a s ih =>
    intro hs k
    have ha : a ^ 2 = α + β * a := hs a (Multiset.mem_cons_self a s)
    have ih' := ih (fun v hv => hs v (Multiset.mem_cons_of_mem hv))
    have e1 : (a ::ₘ s).esymm 1 = s.esymm 1 + a := by
      have := esymm_cons_succ a s 0
      simp only [zero_add, esymm_zero', mul_one] at this
      exact this
    rw [e1, Multiset.card_cons, esymm_cons_succ a s (k + 1), esymm_cons_succ a s k]
    rcases k with _ | k
    · have h0 := ih' 0
      simp only [esymm_zero', zero_add] at h0 ⊢
      push_cast at h0 ⊢
      linear_combination h0 + ha
    · have h1 := ih' (k + 1)
      have h2 := ih' k
      rw [esymm_cons_succ a s k]
      push_cast at h1 h2 ⊢
      linear_combination h1 + a * h2 + s.esymm (k + 1) * ha

section

variable {p : ℕ} [Fact p.Prime] {m n : ℕ}

/-! ## The functions `g` -/

lemma g_props (F : Fin m → Finset (ZMod p)) (r : ℕ) (hF : ∀ i, (F i).card = r) (hr : 1 ≤ r)
    (hrp : r < p) (i : Fin m) :
    ∑ a, g F i a = 0 ∧ ∑ a, (g F i a) ^ 2 = 1 := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  have hs0 : ∑ a, (fval F i a - fbar F i) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
    unfold fbar
    rw [← mul_assoc, mul_one_div_cancel hp, one_mul, sub_self]
  obtain ⟨a, ha⟩ : (F i).Nonempty := Finset.card_pos.mp (by rw [hF]; omega)
  obtain ⟨b, hb⟩ : ∃ b, b ∉ F i := by
    by_contra hcon
    push_neg at hcon
    have h1 : F i = Finset.univ := Finset.eq_univ_of_forall hcon
    have h2 := congrArg Finset.card h1
    rw [hF, Finset.card_univ, hcard] at h2
    omega
  have hab : a ≠ b := fun h => hb (h ▸ ha)
  have hle : (fval F i a - fbar F i) ^ 2 + (fval F i b - fbar F i) ^ 2 ≤
      ∑ x, (fval F i x - fbar F i) ^ 2 := by
    have := Finset.sum_le_sum_of_subset_of_nonneg (s := {a, b}) (t := Finset.univ)
      (f := fun x => (fval F i x - fbar F i) ^ 2) (Finset.subset_univ _)
      (fun _ _ _ => sq_nonneg _)
    rw [Finset.sum_pair hab] at this
    exact this
  have hfa : fval F i a = 1 := if_pos ha
  have hfb : fval F i b = -1 := if_neg hb
  rw [hfa, hfb] at hle
  have hV : 0 < ∑ x, (fval F i x - fbar F i) ^ 2 := by nlinarith [sq_nonneg (fbar F i)]
  constructor
  · unfold g
    rw [← Finset.sum_div, hs0, zero_div]
  · unfold g
    simp only [div_pow]
    rw [← Finset.sum_div]
    unfold phi
    rw [Real.sq_sqrt hV.le, div_self hV.ne']

lemma sum_fval (F : Fin m → Finset (ZMod p)) (r : ℕ) (hF : ∀ i, (F i).card = r) (i : Fin m) :
    ∑ a, fval F i a = 2 * (r : ℝ) - p := by
  have h1 : ∀ a, fval F i a = 2 * (if a ∈ F i then (1 : ℝ) else 0) - 1 := by
    intro a
    unfold fval
    split_ifs <;> norm_num
  rw [Finset.sum_congr rfl (fun a _ => h1 a), Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, Finset.sum_const, Finset.card_univ,
    ZMod.card, hF]
  simp

lemma fbar_eq (F : Fin m → Finset (ZMod p)) (r : ℕ) (hF : ∀ i, (F i).card = r) (i : Fin m) :
    fbar F i = (2 * (r : ℝ) - p) / p := by
  unfold fbar
  rw [sum_fval F r hF i]
  ring

lemma sumsq_fval (F : Fin m → Finset (ZMod p)) (r : ℕ) (hF : ∀ i, (F i).card = r) (i : Fin m) :
    ∑ a, (fval F i a - fbar F i) ^ 2 = 4 * r * ((p : ℝ) - r) / p := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have h1 : ∀ a, (fval F i a - fbar F i) ^ 2 = 1 + fbar F i ^ 2 - 2 * fbar F i * fval F i a := by
    intro a
    have : fval F i a ^ 2 = 1 := by
      unfold fval
      split_ifs <;> norm_num
    linear_combination this
  rw [Finset.sum_congr rfl (fun a _ => h1 a), Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_fval F r hF i, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul,
    fbar_eq F r hF i]
  field_simp <;> ring

lemma rpos (r : ℕ) (hr : 1 ≤ r) (hrp : r < p) : (0 : ℝ) < r * ((p : ℝ) - r) := by
  have h1 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have h2 : (r : ℝ) < p := by exact_mod_cast hrp
  exact mul_pos h1 (by linarith)

lemma phi_eq (F : Fin m → Finset (ZMod p)) (r : ℕ) (hF : ∀ i, (F i).card = r) (hr : 1 ≤ r)
    (hrp : r < p) (i : Fin m) :
    phi F i = 2 * Real.sqrt (r * ((p : ℝ) - r)) / Real.sqrt p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hrr := rpos (p := p) r hr hrp
  unfold phi
  rw [sumsq_fval F r hF i]
  rw [show (4 * r * ((p : ℝ) - r) / p) = (2 * Real.sqrt (r * ((p : ℝ) - r)) / Real.sqrt p) ^ 2 by
    rw [div_pow, mul_pow, Real.sq_sqrt hrr.le, Real.sq_sqrt hp0.le]; ring]
  exact Real.sqrt_sq (by positivity)

lemma g_formula (F : Fin m → Finset (ZMod p)) (r : ℕ) (hF : ∀ i, (F i).card = r) (hr : 1 ≤ r)
    (hrp : r < p) (i : Fin m) (a : ZMod p) :
    g F i a = (fval F i a - (2 * (r : ℝ) - p) / p) * Real.sqrt p /
      (2 * Real.sqrt (r * ((p : ℝ) - r))) := by
  unfold g
  rw [fbar_eq F r hF i, phi_eq F r hF hr hrp i, div_div_eq_mul_div]

lemma indicator_eq (F : Fin m → Finset (ZMod p)) (r : ℕ) (hF : ∀ i, (F i).card = r)
    (hr : 1 ≤ r) (hrp : r < p) (i : Fin m) (a : ZMod p) :
    (if a ∈ F i then (1 : ℝ) else 0) =
      r / p + Real.sqrt (r * ((p : ℝ) - r)) / Real.sqrt p * g F i a := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp1 : (p : ℝ) ≠ 0 := hp0.ne'
  have ht0 : Real.sqrt (r * ((p : ℝ) - r)) ≠ 0 :=
    (Real.sqrt_pos.mpr (rpos (p := p) r hr hrp)).ne'
  have hs0 : Real.sqrt (p : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hp0).ne'
  rw [g_formula F r hF hr hrp i a]
  unfold fval
  split_ifs
  · field_simp <;> ring
  · field_simp <;> ring

lemma g_sq (F : Fin m → Finset (ZMod p)) (r : ℕ) (hF : ∀ i, (F i).card = r) (hr : 1 ≤ r)
    (hrp : r < p) (i : Fin m) (a : ZMod p) :
    g F i a ^ 2 = 1 / p + dparOf p r / Real.sqrt p * g F i a := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp1 : (p : ℝ) ≠ 0 := hp0.ne'
  have hr0 : (r : ℝ) ≠ 0 := by
    have : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
    exact this.ne'
  have hpr : (p : ℝ) - r ≠ 0 := by
    have h2 : (r : ℝ) < p := by exact_mod_cast hrp
    linarith
  have hrr := rpos (p := p) r hr hrp
  obtain ⟨t, ht⟩ : ∃ t, t = Real.sqrt (r * ((p : ℝ) - r)) := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt (p : ℝ) := ⟨_, rfl⟩
  have ht2 : t ^ 2 = r * ((p : ℝ) - r) := by rw [ht]; exact Real.sq_sqrt hrr.le
  have hs2 : s ^ 2 = p := by rw [hs]; exact Real.sq_sqrt hp0.le
  have ht0 : t ≠ 0 := by rw [ht]; exact (Real.sqrt_pos.mpr hrr).ne'
  have hs0 : s ≠ 0 := by rw [hs]; exact (Real.sqrt_pos.mpr hp0).ne'
  have hgf := g_formula F r hF hr hrp i a
  rw [← ht, ← hs] at hgf
  unfold dparOf
  rw [← ht, ← hs, hgf]
  obtain ⟨f, hf⟩ : ∃ f, f = fval F i a := ⟨_, rfl⟩
  have hf1 : f = 1 ∨ f = -1 := by
    rw [hf]
    unfold fval
    split_ifs
    · left; rfl
    · right; rfl
  rw [← hf]
  obtain ⟨c, hc⟩ : ∃ c, c = (2 * (r : ℝ) - p) / p := ⟨_, rfl⟩
  rw [← hc]
  have L : ((f - c) * s / (2 * t)) ^ 2 = (f - c) ^ 2 * s ^ 2 / (4 * t ^ 2) := by ring
  have R : ((p : ℝ) - 2 * r) / t / s * ((f - c) * s / (2 * t)) =
      ((p : ℝ) - 2 * r) * (f - c) / (2 * t ^ 2) := by
    field_simp <;> ring
  rw [L, R, hs2, ht2, hc]
  rcases hf1 with h | h
  · rw [h]
    field_simp <;> ring
  · rw [h]
    field_simp <;> ring

/-! ## Elementary symmetric functions of the `g`-values -/

lemma E_zero (B : Matrix (Fin m) (Fin n) (ZMod p)) (F : Fin m → Finset (ZMod p))
    (x : Fin n → ZMod p) : esymmG B F 0 x = 1 := by
  unfold esymmG
  exact esymm_zero' _

lemma E_one (B : Matrix (Fin m) (Fin n) (ZMod p)) (F : Fin m → Finset (ZMod p))
    (x : Fin n → ZMod p) : esymmG B F 1 x = ∑ i, g F i (B.mulVec x i) := by
  unfold esymmG
  rw [Finset.esymm_map_val, Finset.powersetCard_one, Finset.sum_map]
  simp

lemma E_rec (B : Matrix (Fin m) (Fin n) (ZMod p)) (F : Fin m → Finset (ZMod p)) (r : ℕ)
    (hF : ∀ i, (F i).card = r) (hr : 1 ≤ r) (hrp : r < p) (x : Fin n → ZMod p) (k : ℕ) :
    esymmG B F (k + 1) x * esymmG B F 1 x = ((k : ℝ) + 2) * esymmG B F (k + 1 + 1) x +
      1 / (p : ℝ) * ((m : ℝ) - k) * esymmG B F k x +
      dparOf p r / Real.sqrt p * ((k : ℝ) + 1) * esymmG B F (k + 1) x := by
  have h := esymm_rec (1 / (p : ℝ)) (dparOf p r / Real.sqrt p)
    (Finset.univ.val.map fun i => g F i (B.mulVec x i)) ?_ k
  · rw [Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin] at h
    exact h
  · intro v hv
    obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hv
    exact g_sq F r hF hr hrp i _

/-! ## Uniformity of linear maps with independent rows -/

def subM (B : Matrix (Fin m) (Fin n) (ZMod p)) (V : Finset (Fin m)) : Matrix V (Fin n) (ZMod p) :=
  B.submatrix (fun u : V => (u : Fin m)) id

noncomputable def cnt (B : Matrix (Fin m) (Fin n) (ZMod p)) (V : Finset (Fin m)) : ℝ :=
  ((Finset.univ.filter (fun x : Fin n → ZMod p => (subM B V).mulVec x = 0)).card : ℝ)

lemma fiber_card {V : Type*} [Fintype V] [DecidableEq V] (A : Matrix V (Fin n) (ZMod p))
    (hA : Function.Surjective A.mulVec) (y : V → ZMod p) :
    (Finset.univ.filter (fun x : Fin n → ZMod p => A.mulVec x = y)).card =
      (Finset.univ.filter (fun x : Fin n → ZMod p => A.mulVec x = 0)).card := by
  obtain ⟨x0, hx0⟩ := hA y
  apply Finset.card_nbij' (fun x => x - x0) (fun x => x + x0)
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [Matrix.mulVec_sub, hx, hx0, sub_self]
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [Matrix.mulVec_add, hx, hx0, zero_add]
  · intro x _
    simp
  · intro x _
    simp

lemma sum_comp_surj {V : Type*} [Fintype V] [DecidableEq V] (A : Matrix V (Fin n) (ZMod p))
    (hA : Function.Surjective A.mulVec) (G : (V → ZMod p) → ℝ) :
    ∑ x : Fin n → ZMod p, G (A.mulVec x) =
      ((Finset.univ.filter (fun x : Fin n → ZMod p => A.mulVec x = 0)).card : ℝ) *
        ∑ y, G y := by
  have hfib : ∑ y : V → ZMod p, ∑ x ∈ Finset.univ.filter
      (fun x : Fin n → ZMod p => A.mulVec x = y), G (A.mulVec x) =
      ∑ x : Fin n → ZMod p, G (A.mulVec x) :=
    Finset.sum_fiberwise _ _ _
  rw [← hfib, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  have h1 : ∀ x ∈ Finset.univ.filter (fun x : Fin n → ZMod p => A.mulVec x = y),
      G (A.mulVec x) = G y := by
    intro x hx
    rw [(Finset.mem_filter.mp hx).2]
  rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, fiber_card A hA y, mul_comm]

lemma sum_prod_eq (B : Matrix (Fin m) (Fin n) (ZMod p)) (V : Finset (Fin m))
    (hA : Function.Surjective (subM B V).mulVec) (h : Fin m → ZMod p → ℝ) :
    ∑ x : Fin n → ZMod p, ∏ u ∈ V, h u (B.mulVec x u) = cnt B V * ∏ u ∈ V, ∑ a, h u a := by
  have e : ∀ x : Fin n → ZMod p, ∏ u ∈ V, h u (B.mulVec x u) =
      (fun y : V → ZMod p => ∏ u : V, h u (y u)) ((subM B V).mulVec x) := by
    intro x
    rw [← Finset.prod_coe_sort V]
    rfl
  rw [Finset.sum_congr rfl (fun x _ => e x)]
  refine (sum_comp_surj (subM B V) hA (fun y : V → ZMod p => ∏ u : V, h u (y u))).trans ?_
  unfold cnt
  congr 1
  rw [← Finset.prod_coe_sort V (fun u => ∑ a, h u a)]
  exact (Fintype.prod_sum (fun (u : V) (a : ZMod p) => h u a)).symm

lemma surj_of_dist (B : Matrix (Fin m) (Fin n) (ZMod p)) (t : ℕ) (hdist : DistGt B t)
    (V : Finset (Fin m)) (hV : V.card ≤ t) : Function.Surjective (subM B V).mulVec := by
  have hinj : Function.Injective (subM B V).transpose.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro d hd
    rw [Matrix.mulVecLin_apply] at hd
    by_contra hne
    obtain ⟨u, hu⟩ : ∃ u, d u ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hne (funext hcon)
    let e : Fin m → ZMod p := fun i => if hi : i ∈ V then d ⟨i, hi⟩ else 0
    have he : B.transpose.mulVec e = 0 := by
      funext j
      have h1 := congrFun hd j
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, subM, Matrix.submatrix_apply,
        id, Pi.zero_apply] at h1 ⊢
      rw [← h1]
      have hsub : ∑ i ∈ V, B i j * e i = ∑ i, B i j * e i :=
        Finset.sum_subset (Finset.subset_univ V) (fun i _ hi => by simp [e, hi])
      rw [← hsub, ← Finset.sum_coe_sort V]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp [e, i.2]
    have hne' : e ≠ 0 := by
      intro h0
      have := congrFun h0 u.1
      simp [e, u.2] at this
      exact hu this
    have hwt : wt e ≤ V.card := by
      unfold wt
      apply Finset.card_le_card
      intro i hi
      by_contra hiV
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact hi (by simp [e, hiV])
    have := hdist e hne' he
    omega
  have hrank : (subM B V).rank = Fintype.card V := by
    rw [← Matrix.rank_transpose, Matrix.rank, LinearMap.finrank_range_of_inj hinj,
      Module.finrank_fintype_fun_eq_card]
  have htop : LinearMap.range (subM B V).mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_fintype_fun_eq_card]
    exact hrank
  intro y
  have hy : y ∈ LinearMap.range (subM B V).mulVecLin := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨x, hx⟩ := hy
  exact ⟨x, hx⟩

lemma t_lt_m (B : Matrix (Fin m) (Fin n) (ZMod p)) (t : ℕ) (hdist : DistGt B t) (hnm : n < m) :
    t < m := by
  have hker : LinearMap.ker B.transpose.mulVecLin ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt
    rw [Module.finrank_fin_fun, Module.finrank_fin_fun]
    exact hnm
  obtain ⟨d, hd, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have h1 := hdist d hne (LinearMap.mem_ker.mp hd)
  have h2 : wt d ≤ m := by
    unfold wt
    calc _ ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_filter_le _ _
      _ = m := by simp
  omega

noncomputable def Pw (p n k : ℕ) : ℝ := (p : ℝ) ^ ((n : ℤ) - k)

lemma cnt_eq (B : Matrix (Fin m) (Fin n) (ZMod p)) (V : Finset (Fin m))
    (hA : Function.Surjective (subM B V).mulVec) : cnt B V = Pw p n V.card := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have h : ∑ _x : Fin n → ZMod p, (1 : ℝ) = cnt B V * ∑ _y : V → ZMod p, (1 : ℝ) := by
    unfold cnt
    exact sum_comp_surj (subM B V) hA (fun _ => 1)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_pi,
    Finset.prod_const, ZMod.card, Fintype.card_fin, Fintype.card_coe, nsmul_eq_mul,
    mul_one] at h
  push_cast at h
  unfold Pw
  rw [zpow_sub₀ hp0, zpow_natCast, zpow_natCast, eq_div_iff (pow_ne_zero _ hp0)]
  linarith

lemma pair_sum (B : Matrix (Fin m) (Fin n) (ZMod p)) (F : Fin m → Finset (ZMod p))
    (hg0 : ∀ i, ∑ a, g F i a = 0) (hg1 : ∀ i, ∑ a, g F i a ^ 2 = 1)
    (S T : Finset (Fin m)) (hA : Function.Surjective (subM B (S ∪ T)).mulVec) :
    ∑ x : Fin n → ZMod p, (∏ i ∈ S, g F i (B.mulVec x i)) * (∏ i ∈ T, g F i (B.mulVec x i)) =
      if S = T then cnt B (S ∪ T) else 0 := by
  have e : ∀ x : Fin n → ZMod p,
      (∏ i ∈ S, g F i (B.mulVec x i)) * (∏ i ∈ T, g F i (B.mulVec x i)) =
      ∏ u ∈ S ∪ T, ((if u ∈ S then g F u (B.mulVec x u) else 1) *
        (if u ∈ T then g F u (B.mulVec x u) else 1)) := by
    intro x
    rw [Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.prod_ite_mem,
      Finset.inter_eq_right.mpr Finset.subset_union_left,
      Finset.inter_eq_right.mpr Finset.subset_union_right]
  rw [Finset.sum_congr rfl (fun x _ => e x)]
  have hsp : ∑ x : Fin n → ZMod p, ∏ u ∈ S ∪ T,
      ((if u ∈ S then g F u (B.mulVec x u) else 1) *
        (if u ∈ T then g F u (B.mulVec x u) else 1)) =
      cnt B (S ∪ T) * ∏ u ∈ S ∪ T, ∑ a, ((if u ∈ S then g F u a else 1) *
        (if u ∈ T then g F u a else 1)) :=
    sum_prod_eq B (S ∪ T) hA
      (fun u a => (if u ∈ S then g F u a else 1) * (if u ∈ T then g F u a else 1))
  rw [hsp]
  by_cases hST : S = T
  · subst hST
    rw [if_pos rfl, Finset.prod_eq_one, mul_one]
    intro u hu
    rw [Finset.union_self] at hu
    simp only [if_pos hu]
    rw [Finset.sum_congr rfl (fun a _ => (sq (g F u a)).symm)]
    exact hg1 u
  · rw [if_neg hST]
    have hex : ∃ u ∈ S ∪ T,
        ∑ a, ((if u ∈ S then g F u a else 1) * (if u ∈ T then g F u a else 1)) = 0 := by
      by_cases h1 : S ⊆ T
      · have h2 : ¬ T ⊆ S := fun h2 => hST (Finset.Subset.antisymm h1 h2)
        obtain ⟨u, huT, huS⟩ := Finset.not_subset.mp h2
        refine ⟨u, Finset.mem_union_right _ huT, ?_⟩
        simp only [if_neg huS, if_pos huT, one_mul]
        exact hg0 u
      · obtain ⟨u, huS, huT⟩ := Finset.not_subset.mp h1
        refine ⟨u, Finset.mem_union_left _ huS, ?_⟩
        simp only [if_pos huS, if_neg huT, mul_one]
        exact hg0 u
    obtain ⟨u, hu, h0⟩ := hex
    rw [Finset.prod_eq_zero hu h0, mul_zero]

lemma gram (B : Matrix (Fin m) (Fin n) (ZMod p)) (F : Fin m → Finset (ZMod p)) (r : ℕ)
    (hF : ∀ i, (F i).card = r) (hr : 1 ≤ r) (hrp : r < p) (ℓ : ℕ)
    (hdist : DistGt B (2 * ℓ + 1)) (a b : ℕ) (hab : a + b ≤ 2 * ℓ + 1) :
    ∑ x : Fin n → ZMod p, esymmG B F a x * esymmG B F b x =
      if a = b then (m.choose b : ℝ) * Pw p n b else 0 := by
  have hg := g_props F r hF hr hrp
  simp only [esymmG, Finset.esymm_map_val, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  have hS : ∀ S ∈ (Finset.univ : Finset (Fin m)).powersetCard a,
      ∑ x : Fin n → ZMod p, ∑ T ∈ (Finset.univ : Finset (Fin m)).powersetCard b,
        (∏ i ∈ S, g F i (B.mulVec x i)) * (∏ i ∈ T, g F i (B.mulVec x i)) =
      if a = b then Pw p n b else 0 := by
    intro S hS
    rw [Finset.sum_comm]
    have hT : ∀ T ∈ (Finset.univ : Finset (Fin m)).powersetCard b,
        ∑ x : Fin n → ZMod p,
          (∏ i ∈ S, g F i (B.mulVec x i)) * (∏ i ∈ T, g F i (B.mulVec x i)) =
        if S = T then cnt B (S ∪ T) else 0 := by
      intro T hT
      have hcard : (S ∪ T).card ≤ 2 * ℓ + 1 := by
        have := Finset.card_union_le S T
        rw [(Finset.mem_powersetCard.mp hS).2, (Finset.mem_powersetCard.mp hT).2] at this
        omega
      exact pair_sum B F (fun i => (hg i).1) (fun i => (hg i).2) S T
        (surj_of_dist B _ hdist _ hcard)
    rw [Finset.sum_congr rfl hT, Finset.sum_ite_eq]
    have hSa := (Finset.mem_powersetCard.mp hS).2
    by_cases hab' : a = b
    · subst hab'
      rw [if_pos hS, if_pos rfl, Finset.union_self,
        cnt_eq B S (surj_of_dist B _ hdist S (by omega)), hSa]
    · rw [if_neg hab', if_neg]
      intro hmem
      exact hab' (hSa.symm.trans (Finset.mem_powersetCard.mp hmem).2)
  rw [Finset.sum_congr rfl hS]
  by_cases hab' : a = b
  · subst hab'
    rw [if_pos rfl, if_pos rfl, Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  · rw [if_neg hab', if_neg hab', Finset.sum_const_zero]

/-! ## The tridiagonal entries -/

noncomputable def T (B : Matrix (Fin m) (Fin n) (ZMod p)) (F : Fin m → Finset (ZMod p))
    (j k : ℕ) : ℝ :=
  ∑ x : Fin n → ZMod p, esymmG B F j x * (esymmG B F k x * esymmG B F 1 x)

lemma Tform_zero (B : Matrix (Fin m) (Fin n) (ZMod p)) (F : Fin m → Finset (ZMod p)) (j : ℕ) :
    T B F j 0 = ∑ x : Fin n → ZMod p, esymmG B F j x * esymmG B F 1 x := by
  unfold T
  simp only [E_zero, one_mul]

lemma Tform_succ (B : Matrix (Fin m) (Fin n) (ZMod p)) (F : Fin m → Finset (ZMod p)) (r : ℕ)
    (hF : ∀ i, (F i).card = r) (hr : 1 ≤ r) (hrp : r < p) (j k : ℕ) :
    T B F j (k + 1) =
      ((k : ℝ) + 2) * (∑ x : Fin n → ZMod p, esymmG B F j x * esymmG B F (k + 1 + 1) x) +
      1 / (p : ℝ) * ((m : ℝ) - k) * (∑ x : Fin n → ZMod p, esymmG B F j x * esymmG B F k x) +
      dparOf p r / Real.sqrt p * ((k : ℝ) + 1) *
        (∑ x : Fin n → ZMod p, esymmG B F j x * esymmG B F (k + 1) x) := by
  have h : ∀ x : Fin n → ZMod p, esymmG B F j x * (esymmG B F (k + 1) x * esymmG B F 1 x) =
      ((k : ℝ) + 2) * (esymmG B F j x * esymmG B F (k + 1 + 1) x) +
      1 / (p : ℝ) * ((m : ℝ) - k) * (esymmG B F j x * esymmG B F k x) +
      dparOf p r / Real.sqrt p * ((k : ℝ) + 1) * (esymmG B F j x * esymmG B F (k + 1) x) := by
    intro x
    rw [E_rec B F r hF hr hrp x k]
    ring
  unfold T
  rw [Finset.sum_congr rfl (fun x _ => h x), Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]

lemma Ediag (B : Matrix (Fin m) (Fin n) (ZMod p)) (F : Fin m → Finset (ZMod p)) (r : ℕ)
    (hF : ∀ i, (F i).card = r) (hr : 1 ≤ r) (hrp : r < p) (ℓ : ℕ)
    (hdist : DistGt B (2 * ℓ + 1)) (k : ℕ) (hk : k ≤ ℓ) :
    T B F k k = dparOf p r / Real.sqrt p * k * ((m.choose k : ℝ) * Pw p n k) := by
  rcases k with _ | k
  · rw [Tform_zero, gram B F r hF hr hrp ℓ hdist 0 1 (by omega)]
    simp
  · rw [Tform_succ B F r hF hr hrp, gram B F r hF hr hrp ℓ hdist (k + 1) (k + 1 + 1) (by omega),
      gram B F r hF hr hrp ℓ hdist (k + 1) k (by omega),
      gram B F r hF hr hrp ℓ hdist (k + 1) (k + 1) (by omega)]
    split_ifs <;> first | (exfalso; omega) | (push_cast; ring)

lemma Eup (B : Matrix (Fin m) (Fin n) (ZMod p)) (F : Fin m → Finset (ZMod p)) (r : ℕ)
    (hF : ∀ i, (F i).card = r) (hr : 1 ≤ r) (hrp : r < p) (ℓ : ℕ)
    (hdist : DistGt B (2 * ℓ + 1)) (k : ℕ) (hk : k + 1 ≤ ℓ) :
    T B F (k + 1) k = ((k : ℝ) + 1) * ((m.choose (k + 1) : ℝ) * Pw p n (k + 1)) := by
  rcases k with _ | k
  · simp only [zero_add]
    rw [Tform_zero, gram B F r hF hr hrp ℓ hdist 1 1 (by omega), if_pos rfl]
    push_cast
    ring
  · rw [Tform_succ B F r hF hr hrp,
      gram B F r hF hr hrp ℓ hdist (k + 1 + 1) (k + 1 + 1) (by omega),
      gram B F r hF hr hrp ℓ hdist (k + 1 + 1) k (by omega),
      gram B F r hF hr hrp ℓ hdist (k + 1 + 1) (k + 1) (by omega)]
    split_ifs <;> first | (exfalso; omega) | (push_cast; ring)

lemma Edown (B : Matrix (Fin m) (Fin n) (ZMod p)) (F : Fin m → Finset (ZMod p)) (r : ℕ)
    (hF : ∀ i, (F i).card = r) (hr : 1 ≤ r) (hrp : r < p) (ℓ : ℕ)
    (hdist : DistGt B (2 * ℓ + 1)) (k : ℕ) (hk : k + 1 ≤ ℓ) :
    T B F k (k + 1) = 1 / (p : ℝ) * ((m : ℝ) - k) * ((m.choose k : ℝ) * Pw p n k) := by
  rw [Tform_succ B F r hF hr hrp, gram B F r hF hr hrp ℓ hdist k (k + 1 + 1) (by omega),
    gram B F r hF hr hrp ℓ hdist k k (by omega),
    gram B F r hF hr hrp ℓ hdist k (k + 1) (by omega)]
  split_ifs <;> first | (exfalso; omega) | (push_cast; ring)

lemma Efar (B : Matrix (Fin m) (Fin n) (ZMod p)) (F : Fin m → Finset (ZMod p)) (r : ℕ)
    (hF : ∀ i, (F i).card = r) (hr : 1 ≤ r) (hrp : r < p) (ℓ : ℕ)
    (hdist : DistGt B (2 * ℓ + 1)) (j k : ℕ) (hj : j ≤ ℓ) (hk : k ≤ ℓ)
    (h1 : j ≠ k) (h2 : j ≠ k + 1) (h3 : k ≠ j + 1) : T B F j k = 0 := by
  rcases k with _ | k
  · rw [Tform_zero, gram B F r hF hr hrp ℓ hdist j 1 (by omega)]
    split_ifs <;> first | (exfalso; omega) | rfl
  · rw [Tform_succ B F r hF hr hrp, gram B F r hF hr hrp ℓ hdist j (k + 1 + 1) (by omega),
      gram B F r hF hr hrp ℓ hdist j k (by omega),
      gram B F r hF hr hrp ℓ hdist j (k + 1) (by omega)]
    split_ifs <;> first | (exfalso; omega) | simp

noncomputable def D (p n m k : ℕ) : ℝ := Real.sqrt (Pw p n k * m.choose k)

lemma Pw_succ (j : ℕ) : Pw p n j = p * Pw p n (j + 1) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  unfold Pw
  rw [show ((n : ℤ) - (j : ℕ)) = ((n : ℤ) - ((j + 1 : ℕ) : ℤ)) + 1 by push_cast; ring,
    zpow_add_one₀ hp0]
  ring

lemma choose_rel (j : ℕ) (hj : j + 1 ≤ m) :
    ((m : ℝ) - j) * m.choose j = ((j : ℝ) + 1) * m.choose (j + 1) := by
  have h := Nat.choose_succ_right_eq m j
  have h' : ((m.choose (j + 1) * (j + 1) : ℕ) : ℝ) = ((m.choose j * (m - j) : ℕ) : ℝ) := by
    rw [h]
  push_cast [Nat.cast_sub (show j ≤ m by omega)] at h'
  linarith

lemma Rlem (j : ℕ) (hj : j + 1 ≤ m) :
    1 / (p : ℝ) * ((m : ℝ) - j) * ((m.choose j : ℝ) * Pw p n j) =
      ((j : ℝ) + 1) * ((m.choose (j + 1) : ℝ) * Pw p n (j + 1)) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [Pw_succ (p := p) (n := n) j]
  calc 1 / (p : ℝ) * ((m : ℝ) - j) * ((m.choose j : ℝ) * (p * Pw p n (j + 1)))
      = ((p : ℝ) * (1 / p)) * ((((m : ℝ) - j) * m.choose j) * Pw p n (j + 1)) := by ring
    _ = (((j : ℝ) + 1) * m.choose (j + 1)) * Pw p n (j + 1) := by
        rw [mul_one_div_cancel hp0, one_mul, choose_rel j hj]
    _ = ((j : ℝ) + 1) * ((m.choose (j + 1) : ℝ) * Pw p n (j + 1)) := by ring

lemma Qlem (j : ℕ) (hj : j + 1 ≤ m) :
    ((j : ℝ) + 1) * ((m.choose (j + 1) : ℝ) * Pw p n (j + 1)) / (D p n m j * D p n m (j + 1)) =
      Real.sqrt (((j : ℝ) + 1) * ((m : ℝ) - j)) / Real.sqrt p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hC0 : (0 : ℝ) < m.choose j := by exact_mod_cast Nat.choose_pos (by omega)
  have hC1 : (0 : ℝ) < m.choose (j + 1) := by exact_mod_cast Nat.choose_pos hj
  have hCC := choose_rel j hj
  have hmj : (j : ℝ) + 1 ≤ m := by exact_mod_cast hj
  unfold D
  rw [Pw_succ (p := p) (n := n) j]
  obtain ⟨P1, hP1⟩ : ∃ P, P = Pw p n (j + 1) := ⟨_, rfl⟩
  have hP1pos : 0 < P1 := by rw [hP1]; exact zpow_pos hp0 _
  obtain ⟨C0, hC0d⟩ : ∃ C, C = (m.choose j : ℝ) := ⟨_, rfl⟩
  obtain ⟨C1, hC1d⟩ : ∃ C, C = (m.choose (j + 1) : ℝ) := ⟨_, rfl⟩
  rw [← hP1, ← hC0d, ← hC1d]
  rw [← hC0d, ← hC1d] at hCC
  rw [← hC0d] at hC0
  rw [← hC1d] at hC1
  have hX0 : 0 ≤ (p : ℝ) * P1 * C0 := (mul_pos (mul_pos hp0 hP1pos) hC0).le
  have hX1 : 0 ≤ P1 * C1 := (mul_pos hP1pos hC1).le
  have hq : 0 ≤ ((j : ℝ) + 1) * ((m : ℝ) - j) := mul_nonneg (by positivity) (by linarith)
  have hD0 : 0 < Real.sqrt ((p : ℝ) * P1 * C0) :=
    Real.sqrt_pos.mpr (mul_pos (mul_pos hp0 hP1pos) hC0)
  have hD1 : 0 < Real.sqrt (P1 * C1) := Real.sqrt_pos.mpr (mul_pos hP1pos hC1)
  have hs : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr hp0
  rw [div_eq_div_iff (mul_pos hD0 hD1).ne' hs.ne']
  apply (sq_eq_sq₀ (mul_nonneg (mul_nonneg (by positivity) (mul_pos hC1 hP1pos).le)
    (Real.sqrt_nonneg _)) (mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))).mp
  simp only [mul_pow]
  rw [Real.sq_sqrt hp0.le, Real.sq_sqrt hq, Real.sq_sqrt hX0, Real.sq_sqrt hX1]
  linear_combination (-((j : ℝ) + 1) * p * P1 ^ 2 * C1) * hCC

lemma entry (B : Matrix (Fin m) (Fin n) (ZMod p)) (F : Fin m → Finset (ZMod p)) (r : ℕ)
    (hF : ∀ i, (F i).card = r) (hr : 1 ≤ r) (hrp : r < p) (ℓ : ℕ)
    (hdist : DistGt B (2 * ℓ + 1)) (hlm : 2 * ℓ + 1 < m) (j k : Fin (ℓ + 1)) :
    T B F j k / (D p n m j * D p n m k) = Atri m ℓ (dparOf p r) j k / Real.sqrt p := by
  have hj := j.isLt
  have hk := k.isLt
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  simp only [Atri]
  split_ifs with h1 h2 h3
  · rw [← h1, Ediag B F r hF hr hrp ℓ hdist j (by omega)]
    have hC : (0 : ℝ) < m.choose j := by exact_mod_cast Nat.choose_pos (by omega)
    have hP : (0 : ℝ) < Pw p n j := zpow_pos hp0 _
    have hDD : D p n m j * D p n m j = Pw p n j * m.choose j :=
      Real.mul_self_sqrt (mul_pos hP hC).le
    have hC' := hC.ne'
    have hP' := hP.ne'
    have hs : Real.sqrt (p : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hp0).ne'
    rw [hDD]
    field_simp
    try ring
  · rw [h2, Edown B F r hF hr hrp ℓ hdist j (by omega), Rlem (p := p) (m := m) (n := n) j (by omega),
      Qlem (p := p) (m := m) (n := n) j (by omega)]
  · rw [h3, Eup B F r hF hr hrp ℓ hdist k (by omega), mul_comm (D p n m ((k : ℕ) + 1)),
      Qlem (p := p) (m := m) (n := n) k (by omega)]
  · rw [Efar B F r hF hr hrp ℓ hdist j k (by omega) (by omega) h1 h3 h2, zero_div, zero_div]

end


theorem expSat_eq (p : ℕ) [Fact p.Prime] (m n : ℕ) (B : Matrix (Fin m) (Fin n) (ZMod p))
    (F : Fin m → Finset (ZMod p)) (r : ℕ) (hF : ∀ i, (F i).card = r) (hr : 1 ≤ r) (hrp : r < p)
    (hnm : n < m) (ℓ : ℕ) (w : Fin (ℓ + 1) → ℝ)
    (hnorm : ∑ x, ampl B F ℓ w x ^ 2 = 1) (hdist : DistGt B (2 * ℓ + 1)) :
    expSat B F (ampl B F ℓ w) =
      (m : ℝ) * r / p + Real.sqrt (r * ((p : ℝ) - r)) / p * (w ⬝ᵥ (Atri m ℓ (dparOf p r)).mulVec w) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hlm : 2 * ℓ + 1 < m := t_lt_m B _ hdist hnm
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt (p : ℝ) := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, t = Real.sqrt (r * ((p : ℝ) - r)) := ⟨_, rfl⟩
  have hss : s * s = p := by rw [hs]; exact Real.mul_self_sqrt hp0.le
  have hs0 : s ≠ 0 := by rw [hs]; exact (Real.sqrt_pos.mpr hp0).ne'
  have hsat : ∀ x, (sat B F x : ℝ) = (m : ℝ) * r / p + t / s * esymmG B F 1 x := by
    intro x
    unfold sat
    rw [Finset.natCast_card_filter, E_one]
    rw [Finset.sum_congr rfl (fun i _ => indicator_eq F r hF hr hrp i (B.mulVec x i))]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← Finset.mul_sum, ← ht, ← hs]
    ring
  have hampl : ∀ x, ampl B F ℓ w x =
      ∑ k : Fin (ℓ + 1), w k / D p n m k * esymmG B F k x := by
    intro x
    unfold ampl D Pw
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  have hsq : ∀ x, ampl B F ℓ w x ^ 2 * esymmG B F 1 x =
      ∑ j : Fin (ℓ + 1), ∑ k : Fin (ℓ + 1), (w j / D p n m j * (w k / D p n m k)) *
        (esymmG B F j x * (esymmG B F k x * esymmG B F 1 x)) := by
    intro x
    rw [hampl, sq, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  have hmain : ∑ x, ampl B F ℓ w x ^ 2 * esymmG B F 1 x =
      1 / s * (w ⬝ᵥ (Atri m ℓ (dparOf p r)).mulVec w) := by
    rw [Finset.sum_congr rfl (fun x _ => hsq x), Finset.sum_comm]
    have hj : ∀ j : Fin (ℓ + 1), ∑ x : Fin n → ZMod p, ∑ k : Fin (ℓ + 1),
        (w j / D p n m j * (w k / D p n m k)) *
          (esymmG B F j x * (esymmG B F k x * esymmG B F 1 x)) =
        ∑ k : Fin (ℓ + 1), w j * (Atri m ℓ (dparOf p r) j k * w k) / s := by
      intro j
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [← Finset.mul_sum]
      have key : ∀ S : ℝ, S / (D p n m j * D p n m k) = Atri m ℓ (dparOf p r) j k / s →
          (w j / D p n m j * (w k / D p n m k)) * S =
            w j * (Atri m ℓ (dparOf p r) j k * w k) / s := by
        intro S hS
        rw [show (w j / D p n m j * (w k / D p n m k)) * S =
          w j * w k * (S / (D p n m j * D p n m k)) by ring, hS]
        ring
      apply key
      rw [hs]
      exact entry B F r hF hr hrp ℓ hdist hlm j k
    rw [Finset.sum_congr rfl (fun j _ => hj j)]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
    ring
  unfold expSat
  simp only [hsat]
  have hsplit : ∀ x, ampl B F ℓ w x ^ 2 * ((m : ℝ) * r / p + t / s * esymmG B F 1 x) =
      (m : ℝ) * r / p * ampl B F ℓ w x ^ 2 + t / s * (ampl B F ℓ w x ^ 2 * esymmG B F 1 x) :=
    fun x => by ring
  rw [Finset.sum_congr rfl (fun x _ => hsplit x), Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, hnorm, hmain, ← ht]
  generalize (w ⬝ᵥ (Atri m ℓ (dparOf p r)).mulVec w) = X
  rw [show t / s * (1 / s * X) = t * X / (s * s) by ring, hss]
  ring

section Ray

open Matrix

lemma rayleigh {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.IsHermitian) (v : Fin N → ℝ) :
    v ⬝ᵥ (A *ᵥ v) ≤ sSup (spectrum ℝ A) * (v ⬝ᵥ v) := by
  obtain ⟨U, hU⟩ : ∃ U : Matrix (Fin N) (Fin N) ℝ,
      U = (hA.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℝ) := ⟨_, rfl⟩
  have hspec : A = U * diagonal (RCLike.ofReal ∘ hA.eigenvalues) * star U := by
    have := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    rw [hU]
    exact this
  have hUU : U * star U = 1 := by
    rw [hU]
    exact Matrix.mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.2
  have hstar : star U = Uᵀ := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  obtain ⟨w, hw⟩ : ∃ w : Fin N → ℝ, w = Uᵀ *ᵥ v := ⟨_, rfl⟩
  have hL : ∀ j, hA.eigenvalues j ≤ sSup (spectrum ℝ A) := fun j =>
    le_csSup (Matrix.finite_spectrum A).bddAbove (hA.eigenvalues_mem_spectrum_real j)
  have h1 : v ⬝ᵥ (A *ᵥ v) = ∑ j, hA.eigenvalues j * (w j) ^ 2 := by
    have hAv : A *ᵥ v =
        U *ᵥ (diagonal (RCLike.ofReal ∘ hA.eigenvalues) *ᵥ (Uᵀ *ᵥ v)) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hstar, ← hspec]
    rw [hAv, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, ← hw]
    simp only [dotProduct, Matrix.mulVec_diagonal, Function.comp_apply, RCLike.ofReal_real_eq_id,
      id_eq]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have h2 : v ⬝ᵥ v = ∑ j, (w j) ^ 2 := by
    have : w ⬝ᵥ w = v ⬝ᵥ v := by
      rw [hw, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.transpose_transpose,
        Matrix.mulVec_mulVec, ← hstar, hUU, Matrix.one_mulVec]
    rw [← this, dotProduct]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [h1, h2, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_right (hL j) (sq_nonneg _)

lemma atri_herm (m ℓ : ℕ) (d : ℝ) : (Atri m ℓ d).IsHermitian := by
  show (Atri m ℓ d)ᴴ = Atri m ℓ d
  rw [Matrix.conjTranspose_eq_transpose_of_trivial]
  ext i j
  simp only [Matrix.transpose_apply, Atri]
  split_ifs <;> first
    | rfl
    | (exfalso; omega)
    | (have h : i = j := Fin.ext (by omega); subst h; rfl)

lemma exists_top_eig {N : ℕ} (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hA : A.IsHermitian) :
    ∃ v : Fin (N + 1) → ℝ, v ⬝ᵥ v = 1 ∧ v ⬝ᵥ A.mulVec v = sSup (spectrum ℝ A) := by
  have hne : (spectrum ℝ A).Nonempty := ⟨_, hA.eigenvalues_mem_spectrum_real 0⟩
  have hmem := hne.csSup_mem (Matrix.finite_spectrum A)
  have hmem' : sSup (spectrum ℝ A) ∈ Set.range hA.eigenvalues := by
    rw [← hA.spectrum_real_eq_range_eigenvalues]
    exact hmem
  obtain ⟨j, hj⟩ := hmem'
  have hv1 : (⇑(hA.eigenvectorBasis j) : Fin (N + 1) → ℝ) ⬝ᵥ ⇑(hA.eigenvectorBasis j) = 1 := by
    have h := hA.eigenvectorBasis.inner_eq_one j
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h
    simpa only [star_trivial] using h
  refine ⟨⇑(hA.eigenvectorBasis j), hv1, ?_⟩
  rw [hA.mulVec_eigenvectorBasis j, dotProduct_smul, smul_eq_mul, hv1, mul_one, hj]

end Ray

section Corr

variable {p : ℕ} [Fact p.Prime] {m n : ℕ}

lemma fval_eq (F : Fin m → Finset (ZMod p)) (r : ℕ) (hF : ∀ i, (F i).card = r) (hr : 1 ≤ r)
    (hrp : r < p) (i : Fin m) (a : ZMod p) :
    fval F i a = (2 * (r : ℝ) - p) / p +
      2 * Real.sqrt (r * ((p : ℝ) - r)) / Real.sqrt p * g F i a := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have ht0 : Real.sqrt (r * ((p : ℝ) - r)) ≠ 0 :=
    (Real.sqrt_pos.mpr (rpos (p := p) r hr hrp)).ne'
  have hs0 : Real.sqrt (p : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hp0).ne'
  rw [g_formula F r hF hr hrp i a]
  field_simp <;> ring

lemma obj_eq (B : Matrix (Fin m) (Fin n) (ZMod p)) (F : Fin m → Finset (ZMod p)) (r : ℕ)
    (hF : ∀ i, (F i).card = r) (hr : 1 ≤ r) (hrp : r < p) (x : Fin n → ZMod p) :
    obj B F x = (m : ℝ) * ((2 * (r : ℝ) - p) / p) +
      2 * Real.sqrt (r * ((p : ℝ) - r)) / Real.sqrt p * esymmG B F 1 x := by
  unfold obj
  rw [E_one, Finset.mul_sum,
    Finset.sum_congr rfl (fun i _ => fval_eq F r hF hr hrp i (B.mulVec x i)),
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ### Functions that are polynomials in `obj` -/

def PS (B : Matrix (Fin m) (Fin n) (ZMod p)) (F : Fin m → Finset (ZMod p)) (L : ℕ)
    (f : (Fin n → ZMod p) → ℝ) : Prop :=
  ∃ P : Polynomial ℝ, P.natDegree ≤ L ∧ ∀ x, f x = P.eval (obj B F x)

lemma PS_congr {B : Matrix (Fin m) (Fin n) (ZMod p)} {F : Fin m → Finset (ZMod p)} {L : ℕ}
    {f g : (Fin n → ZMod p) → ℝ} (h : PS B F L f) (hfg : ∀ x, f x = g x) : PS B F L g := by
  obtain ⟨P, hP, hPf⟩ := h
  exact ⟨P, hP, fun x => (hfg x).symm.trans (hPf x)⟩

lemma PS_mono {B : Matrix (Fin m) (Fin n) (ZMod p)} {F : Fin m → Finset (ZMod p)} {L L' : ℕ}
    {f : (Fin n → ZMod p) → ℝ} (hL : L ≤ L') (h : PS B F L f) : PS B F L' f := by
  obtain ⟨P, hP, hPf⟩ := h
  exact ⟨P, hP.trans hL, hPf⟩

lemma PS_lin {B : Matrix (Fin m) (Fin n) (ZMod p)} {F : Fin m → Finset (ZMod p)} {L : ℕ}
    {f g : (Fin n → ZMod p) → ℝ} (a b : ℝ) (hf : PS B F L f) (hg : PS B F L g) :
    PS B F L (fun x => a * f x + b * g x) := by
  obtain ⟨P, hP, hPf⟩ := hf
  obtain ⟨Q, hQ, hQg⟩ := hg
  refine ⟨Polynomial.C a * P + Polynomial.C b * Q, ?_, fun x => ?_⟩
  · exact Polynomial.natDegree_add_le_of_degree_le
      ((Polynomial.natDegree_C_mul_le _ _).trans hP) ((Polynomial.natDegree_C_mul_le _ _).trans hQ)
  · simp [hPf, hQg]

lemma PS_mul {B : Matrix (Fin m) (Fin n) (ZMod p)} {F : Fin m → Finset (ZMod p)} {L L' : ℕ}
    {f g : (Fin n → ZMod p) → ℝ} (hf : PS B F L f) (hg : PS B F L' g) :
    PS B F (L + L') (fun x => f x * g x) := by
  obtain ⟨P, hP, hPf⟩ := hf
  obtain ⟨Q, hQ, hQg⟩ := hg
  refine ⟨P * Q, Polynomial.natDegree_mul_le.trans (add_le_add hP hQ), fun x => ?_⟩
  simp [hPf, hQg]

lemma PS_const (B : Matrix (Fin m) (Fin n) (ZMod p)) (F : Fin m → Finset (ZMod p)) (c : ℝ) :
    PS B F 0 (fun _ => c) :=
  ⟨Polynomial.C c, (Polynomial.natDegree_C c).le, fun x => by simp⟩

lemma PS_obj (B : Matrix (Fin m) (Fin n) (ZMod p)) (F : Fin m → Finset (ZMod p)) :
    PS B F 1 (obj B F) :=
  ⟨Polynomial.X, Polynomial.natDegree_X_le, fun x => by simp⟩

lemma PS_sum {B : Matrix (Fin m) (Fin n) (ZMod p)} {F : Fin m → Finset (ZMod p)} {L : ℕ}
    {ι : Type*} [DecidableEq ι] (f : ι → (Fin n → ZMod p) → ℝ) :
    ∀ s : Finset ι, (∀ i ∈ s, PS B F L (f i)) → PS B F L (fun x => ∑ i ∈ s, f i x) := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨0, by simp, fun x => by simp⟩
  | insert a s ha ih =>
    intro h
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    refine PS_congr (PS_lin 1 1 h1 h2) (fun x => ?_)
    try dsimp only
    rw [Finset.sum_insert ha]
    ring

lemma PS_E (B : Matrix (Fin m) (Fin n) (ZMod p)) (F : Fin m → Finset (ZMod p)) (r : ℕ)
    (hF : ∀ i, (F i).card = r) (hr : 1 ≤ r) (hrp : r < p) :
    ∀ k : ℕ, PS B F k (esymmG B F k) ∧ PS B F (k + 1) (esymmG B F (k + 1)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  obtain ⟨φ, hφ⟩ : ∃ φ, φ = 2 * Real.sqrt (r * ((p : ℝ) - r)) / Real.sqrt p := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = (m : ℝ) * ((2 * (r : ℝ) - p) / p) := ⟨_, rfl⟩
  have hφ0 : φ ≠ 0 := by
    rw [hφ]
    exact (div_pos (mul_pos (by norm_num) (Real.sqrt_pos.mpr (rpos (p := p) r hr hrp)))
      (Real.sqrt_pos.mpr hp0)).ne'
  have hobj : ∀ x, obj B F x = c + φ * esymmG B F 1 x := by
    intro x
    rw [hc, hφ]
    exact obj_eq B F r hF hr hrp x
  have h0 : PS B F 0 (esymmG B F 0) := PS_congr (PS_const B F 1) (fun x => (E_zero B F x).symm)
  have h1 : PS B F 1 (esymmG B F 1) := by
    refine PS_congr (PS_lin (1 / φ) (-c / φ) (PS_obj B F) (PS_mono zero_le_one (PS_const B F 1)))
      (fun x => ?_)
    try dsimp only
    rw [hobj x]
    field_simp <;> ring
  have hstep : ∀ k, PS B F k (esymmG B F k) → PS B F (k + 1) (esymmG B F (k + 1)) →
      PS B F (k + 1 + 1) (esymmG B F (k + 1 + 1)) := by
    intro k hk0 hk1
    have hk2 : ((k : ℝ) + 2) ≠ 0 := by positivity
    have hmul : PS B F (k + 1 + 1) (fun x => esymmG B F (k + 1) x * esymmG B F 1 x) :=
      PS_mul hk1 h1
    have hA : PS B F (k + 1 + 1) (esymmG B F k) := PS_mono (by omega) hk0
    have hB : PS B F (k + 1 + 1) (esymmG B F (k + 1)) := PS_mono (by omega) hk1
    have hl1 := PS_lin (1 / ((k : ℝ) + 2)) (-(1 / (p : ℝ) * ((m : ℝ) - k)) / ((k : ℝ) + 2)) hmul hA
    have hl2 := PS_lin 1 (-(dparOf p r / Real.sqrt p * ((k : ℝ) + 1)) / ((k : ℝ) + 2)) hl1 hB
    refine PS_congr hl2 (fun x => ?_)
    try dsimp only
    rw [E_rec B F r hF hr hrp x k]
    field_simp <;> ring
  intro k
  induction k with
  | zero => exact ⟨h0, h1⟩
  | succ k ih => exact ⟨ih.2, hstep k ih.1 ih.2⟩

/-! ### Functions that are combinations of the `E_k` -/

def ES (B : Matrix (Fin m) (Fin n) (ZMod p)) (F : Fin m → Finset (ZMod p)) (L : ℕ)
    (f : (Fin n → ZMod p) → ℝ) : Prop :=
  ∃ c : ℕ → ℝ, ∀ x, f x = ∑ k ∈ Finset.range (L + 1), c k * esymmG B F k x

lemma ES_congr {B : Matrix (Fin m) (Fin n) (ZMod p)} {F : Fin m → Finset (ZMod p)} {L : ℕ}
    {f g : (Fin n → ZMod p) → ℝ} (h : ES B F L f) (hfg : ∀ x, f x = g x) : ES B F L g := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, fun x => (hfg x).symm.trans (hc x)⟩

lemma ES_lin {B : Matrix (Fin m) (Fin n) (ZMod p)} {F : Fin m → Finset (ZMod p)} {L : ℕ}
    {f g : (Fin n → ZMod p) → ℝ} (a b : ℝ) (hf : ES B F L f) (hg : ES B F L g) :
    ES B F L (fun x => a * f x + b * g x) := by
  obtain ⟨c, hc⟩ := hf
  obtain ⟨c', hc'⟩ := hg
  refine ⟨fun k => a * c k + b * c' k, fun x => ?_⟩
  try dsimp only
  rw [hc x, hc' x, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

lemma ES_smul {B : Matrix (Fin m) (Fin n) (ZMod p)} {F : Fin m → Finset (ZMod p)} {L : ℕ}
    {f : (Fin n → ZMod p) → ℝ} (a : ℝ) (hf : ES B F L f) : ES B F L (fun x => a * f x) := by
  obtain ⟨c, hc⟩ := hf
  refine ⟨fun k => a * c k, fun x => ?_⟩
  try dsimp only
  rw [hc x, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

lemma ES_mono {B : Matrix (Fin m) (Fin n) (ZMod p)} {F : Fin m → Finset (ZMod p)} {L L' : ℕ}
    {f : (Fin n → ZMod p) → ℝ} (hL : L ≤ L') (h : ES B F L f) : ES B F L' f := by
  obtain ⟨c, hc⟩ := h
  refine ⟨fun k => if k ≤ L then c k else 0, fun x => ?_⟩
  try dsimp only
  rw [hc x]
  have hsub : ∑ k ∈ Finset.range (L + 1), (if k ≤ L then c k else 0) * esymmG B F k x =
      ∑ k ∈ Finset.range (L' + 1), (if k ≤ L then c k else 0) * esymmG B F k x := by
    apply Finset.sum_subset (Finset.range_subset_range.mpr (by omega))
    intro k _ hk
    simp only [Finset.mem_range] at hk
    rw [if_neg (show ¬ (k ≤ L) by omega), zero_mul]
  rw [← hsub]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  simp only [Finset.mem_range] at hk
  rw [if_pos (show k ≤ L by omega)]

lemma ES_single (B : Matrix (Fin m) (Fin n) (ZMod p)) (F : Fin m → Finset (ZMod p)) (j : ℕ) :
    ES B F j (esymmG B F j) := by
  refine ⟨fun k => if k = j then 1 else 0, fun x => ?_⟩
  try dsimp only
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self j)) h

lemma ES_sum {B : Matrix (Fin m) (Fin n) (ZMod p)} {F : Fin m → Finset (ZMod p)} {L : ℕ}
    {ι : Type*} [DecidableEq ι] (f : ι → (Fin n → ZMod p) → ℝ) :
    ∀ s : Finset ι, (∀ i ∈ s, ES B F L (f i)) → ES B F L (fun x => ∑ i ∈ s, f i x) := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨fun _ => 0, fun x => by simp⟩
  | insert a s ha ih =>
    intro h
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    refine ES_congr (ES_lin 1 1 h1 h2) (fun x => ?_)
    try dsimp only
    rw [Finset.sum_insert ha]
    ring

lemma ES_E1mul (B : Matrix (Fin m) (Fin n) (ZMod p)) (F : Fin m → Finset (ZMod p)) (r : ℕ)
    (hF : ∀ i, (F i).card = r) (hr : 1 ≤ r) (hrp : r < p) (k : ℕ) :
    ES B F (k + 1) (fun x => esymmG B F k x * esymmG B F 1 x) := by
  rcases k with _ | k
  · refine ES_congr (ES_single B F 1) (fun x => ?_)
    simp only [E_zero, one_mul]
  · have h1 : ES B F (k + 1 + 1) (esymmG B F (k + 1 + 1)) := ES_single B F (k + 1 + 1)
    have h2 : ES B F (k + 1 + 1) (esymmG B F k) := ES_mono (by omega) (ES_single B F k)
    have h3 : ES B F (k + 1 + 1) (esymmG B F (k + 1)) := ES_mono (by omega) (ES_single B F (k + 1))
    have hl := ES_lin ((k : ℝ) + 2) (1 / (p : ℝ) * ((m : ℝ) - k)) h1 h2
    have hl2 := ES_lin 1 (dparOf p r / Real.sqrt p * ((k : ℝ) + 1)) hl h3
    refine ES_congr hl2 (fun x => ?_)
    try dsimp only
    rw [E_rec B F r hF hr hrp x k]
    ring

lemma ES_mulE1 (B : Matrix (Fin m) (Fin n) (ZMod p)) (F : Fin m → Finset (ZMod p)) (r : ℕ)
    (hF : ∀ i, (F i).card = r) (hr : 1 ≤ r) (hrp : r < p) (L : ℕ)
    (f : (Fin n → ZMod p) → ℝ) (hf : ES B F L f) :
    ES B F (L + 1) (fun x => f x * esymmG B F 1 x) := by
  obtain ⟨c, hc⟩ := hf
  have h := ES_sum (B := B) (F := F) (L := L + 1)
    (fun k x => c k * (esymmG B F k x * esymmG B F 1 x)) (Finset.range (L + 1))
    (fun k hk => by
      simp only [Finset.mem_range] at hk
      exact ES_smul (c k) (ES_mono (by omega) (ES_E1mul B F r hF hr hrp k)))
  refine ES_congr h (fun x => ?_)
  try dsimp only
  rw [hc x, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

lemma ES_pow (B : Matrix (Fin m) (Fin n) (ZMod p)) (F : Fin m → Finset (ZMod p)) (r : ℕ)
    (hF : ∀ i, (F i).card = r) (hr : 1 ≤ r) (hrp : r < p) :
    ∀ j : ℕ, ES B F j (fun x => esymmG B F 1 x ^ j) := by
  intro j
  induction j with
  | zero =>
    refine ES_congr (ES_single B F 0) (fun x => ?_)
    try dsimp only
    rw [E_zero, pow_zero]
  | succ j ih =>
    refine ES_congr (ES_mulE1 B F r hF hr hrp j _ ih) (fun x => ?_)
    try dsimp only
    rw [pow_succ]

lemma ES_poly (B : Matrix (Fin m) (Fin n) (ZMod p)) (F : Fin m → Finset (ZMod p)) (r : ℕ)
    (hF : ∀ i, (F i).card = r) (hr : 1 ≤ r) (hrp : r < p) (L : ℕ) (Q : Polynomial ℝ)
    (hQ : Q.natDegree ≤ L) : ES B F L (fun x => Q.eval (esymmG B F 1 x)) := by
  have h := ES_sum (B := B) (F := F) (L := L)
    (fun j x => Q.coeff j * esymmG B F 1 x ^ j) (Finset.range (Q.natDegree + 1))
    (fun j hj => by
      simp only [Finset.mem_range] at hj
      exact ES_smul (Q.coeff j) (ES_mono (by omega) (ES_pow B F r hF hr hrp j)))
  refine ES_congr h (fun x => ?_)
  try dsimp only
  rw [Polynomial.eval_eq_sum_range]

lemma D_pos (k : ℕ) (hk : k ≤ m) : 0 < D p n m k := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hC : (0 : ℝ) < m.choose k := by exact_mod_cast Nat.choose_pos hk
  have hP : (0 : ℝ) < Pw p n k := zpow_pos hp0 _
  exact Real.sqrt_pos.mpr (mul_pos hP hC)

lemma forward (B : Matrix (Fin m) (Fin n) (ZMod p)) (F : Fin m → Finset (ZMod p)) (r : ℕ)
    (hF : ∀ i, (F i).card = r) (hr : 1 ≤ r) (hrp : r < p) (ℓ : ℕ) (hlm : ℓ < m)
    (P : Polynomial ℝ) (hP : P.natDegree ≤ ℓ) :
    ∃ w : Fin (ℓ + 1) → ℝ, ∀ x, P.eval (obj B F x) = ampl B F ℓ w x := by
  obtain ⟨φ, hφ⟩ : ∃ φ, φ = 2 * Real.sqrt (r * ((p : ℝ) - r)) / Real.sqrt p := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = (m : ℝ) * ((2 * (r : ℝ) - p) / p) := ⟨_, rfl⟩
  have hobj : ∀ x, obj B F x = c + φ * esymmG B F 1 x := by
    intro x
    rw [hc, hφ]
    exact obj_eq B F r hF hr hrp x
  have hq : (Polynomial.C c + Polynomial.C φ * Polynomial.X).natDegree ≤ 1 :=
    Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_C c).le.trans zero_le_one)
      ((Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le)
  have hQ : (P.comp (Polynomial.C c + Polynomial.C φ * Polynomial.X)).natDegree ≤ ℓ := by
    refine Polynomial.natDegree_comp_le.trans ?_
    calc P.natDegree * (Polynomial.C c + Polynomial.C φ * Polynomial.X).natDegree
        ≤ ℓ * 1 := Nat.mul_le_mul hP hq
      _ = ℓ := mul_one ℓ
  obtain ⟨a, ha⟩ := ES_poly B F r hF hr hrp ℓ _ hQ
  beta_reduce at ha
  refine ⟨fun k => a k * D p n m k, fun x => ?_⟩
  have hev : P.eval (obj B F x) =
      (P.comp (Polynomial.C c + Polynomial.C φ * Polynomial.X)).eval (esymmG B F 1 x) := by
    rw [Polynomial.eval_comp, hobj x]
    simp
  rw [hev, ha x]
  unfold ampl
  rw [← Fin.sum_univ_eq_sum_range (fun k => a k * esymmG B F k x) (ℓ + 1)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hD := (D_pos (p := p) (n := n) (m := m) k (by omega)).ne'
  unfold D Pw at hD ⊢
  field_simp
  try ring

lemma backward (B : Matrix (Fin m) (Fin n) (ZMod p)) (F : Fin m → Finset (ZMod p)) (r : ℕ)
    (hF : ∀ i, (F i).card = r) (hr : 1 ≤ r) (hrp : r < p) (ℓ : ℕ) (w : Fin (ℓ + 1) → ℝ) :
    ∃ P : Polynomial ℝ, P.natDegree ≤ ℓ ∧ ∀ x, P.eval (obj B F x) = ampl B F ℓ w x := by
  have h := PS_sum (B := B) (F := F) (L := ℓ)
    (fun (k : Fin (ℓ + 1)) x => w k * esymmG B F k x /
      Real.sqrt ((p : ℝ) ^ ((n : ℤ) - (k : ℕ)) * (m.choose k : ℝ))) Finset.univ
    (fun k _ => by
      refine PS_congr (PS_lin (w k / Real.sqrt ((p : ℝ) ^ ((n : ℤ) - (k : ℕ)) *
        (m.choose k : ℝ))) 0 (PS_mono (by omega) (PS_E B F r hF hr hrp k).1)
          (PS_mono (by omega) (PS_E B F r hF hr hrp k).1)) (fun x => ?_)
      try dsimp only
      ring)
  obtain ⟨P, hP, hPf⟩ := h
  exact ⟨P, hP, fun x => (hPf x).symm⟩

lemma ampl_normsq (B : Matrix (Fin m) (Fin n) (ZMod p)) (F : Fin m → Finset (ZMod p)) (r : ℕ)
    (hF : ∀ i, (F i).card = r) (hr : 1 ≤ r) (hrp : r < p) (ℓ : ℕ)
    (hdist : DistGt B (2 * ℓ + 1)) (hlm : 2 * ℓ + 1 < m) (w : Fin (ℓ + 1) → ℝ) :
    ∑ x, ampl B F ℓ w x ^ 2 = w ⬝ᵥ w := by
  have hampl : ∀ x, ampl B F ℓ w x =
      ∑ k : Fin (ℓ + 1), w k / D p n m k * esymmG B F k x := by
    intro x
    unfold ampl D Pw
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  have hsq : ∀ x, ampl B F ℓ w x ^ 2 =
      ∑ j : Fin (ℓ + 1), ∑ k : Fin (ℓ + 1), (w j / D p n m j * (w k / D p n m k)) *
        (esymmG B F j x * esymmG B F k x) := by
    intro x
    rw [hampl, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
    ring
  rw [Finset.sum_congr rfl (fun x _ => hsq x), Finset.sum_comm]
  unfold dotProduct
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  have hg : ∀ k : Fin (ℓ + 1), ∑ x, esymmG B F j x * esymmG B F k x =
      if (j : ℕ) = k then (m.choose k : ℝ) * Pw p n k else 0 :=
    fun k => gram B F r hF hr hrp ℓ hdist j k (by omega)
  simp only [hg]
  rw [Finset.sum_eq_single j]
  · rw [if_pos rfl]
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    have hC : (0 : ℝ) < m.choose j := by exact_mod_cast Nat.choose_pos (by omega)
    have hP : (0 : ℝ) < Pw p n j := zpow_pos hp0 _
    have hDD : D p n m j * D p n m j = Pw p n j * m.choose j :=
      Real.mul_self_sqrt (mul_pos hP hC).le
    have hC' := hC.ne'
    have hP' := hP.ne'
    rw [div_mul_div_comm, hDD]
    field_simp
    try ring
  · intro k _ hk
    rw [if_neg (fun h => hk (Fin.ext h).symm), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

end Corr

end Aux_DQI_Semicircle_eq_131

open Aux_DQI_Semicircle_eq_131 in
open DQI.Semicircle in
theorem solution (p : ℕ) [Fact p.Prime] (m n : ℕ) (B : Matrix (Fin m) (Fin n) (ZMod p))
    (F : Fin m → Finset (ZMod p)) (r : ℕ) (hF : ∀ i, (F i).card = r) (hr : 1 ≤ r) (hrp : r < p)
    (hnm : n < m) (ℓ : ℕ) (hdist : DistGt B (2 * ℓ + 1)) :
    optSat B F ℓ / m =
      (r : ℝ) / p + Real.sqrt ((r : ℝ) / p * (1 - (r : ℝ) / p)) * lamMax (Atri m ℓ (dparOf p r)) / m := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hlm : 2 * ℓ + 1 < m := t_lt_m B _ hdist hnm
  obtain ⟨t, ht⟩ : ∃ t, t = Real.sqrt (r * ((p : ℝ) - r)) := ⟨_, rfl⟩
  have ht0 : 0 ≤ t := by rw [ht]; exact Real.sqrt_nonneg _
  have ht2 : t ^ 2 = r * ((p : ℝ) - r) := by
    rw [ht]; exact Real.sq_sqrt (rpos (p := p) r hr hrp).le
  have hA := atri_herm m ℓ (dparOf p r)
  have hS : IsGreatest {e : ℝ | ∃ P : Polynomial ℝ, P.natDegree ≤ ℓ ∧
      ∑ x, (P.eval (obj B F x)) ^ 2 = 1 ∧
      e = ∑ x, (P.eval (obj B F x)) ^ 2 * (sat B F x : ℝ)}
      ((m : ℝ) * r / p + t / p * sSup (spectrum ℝ (Atri m ℓ (dparOf p r)))) := by
    constructor
    · obtain ⟨v, hv1, hvA⟩ := exists_top_eig _ hA
      obtain ⟨P, hP, hPv⟩ := backward B F r hF hr hrp ℓ v
      have hn1 : ∑ x, ampl B F ℓ v x ^ 2 = 1 := by
        rw [ampl_normsq B F r hF hr hrp ℓ hdist hlm v]
        exact hv1
      refine ⟨P, hP, ?_, ?_⟩
      · simp only [hPv]
        exact hn1
      · simp only [hPv]
        have h := expSat_eq p m n B F r hF hr hrp hnm ℓ v hn1 hdist
        unfold expSat at h
        rw [h, hvA, ← ht]
    · rintro e ⟨P, hP, hn, rfl⟩
      obtain ⟨w, hw⟩ := forward B F r hF hr hrp ℓ (by omega) P hP
      simp only [hw] at hn ⊢
      have h := expSat_eq p m n B F r hF hr hrp hnm ℓ w hn hdist
      unfold expSat at h
      rw [h, ← ht]
      have hray := rayleigh _ hA w
      rw [ampl_normsq B F r hF hr hrp ℓ hdist hlm w] at hn
      rw [hn, mul_one] at hray
      have := mul_le_mul_of_nonneg_left hray (div_nonneg ht0 hp0.le)
      linarith
  unfold optSat lamMax
  rw [hS.csSup_eq]
  have hsq : Real.sqrt ((r : ℝ) / p * (1 - (r : ℝ) / p)) = t / p := by
    rw [show (r : ℝ) / p * (1 - (r : ℝ) / p) = (t / p) ^ 2 by
      rw [div_pow, ht2]; field_simp <;> ring]
    exact Real.sqrt_sq (div_nonneg ht0 hp0.le)
  rw [hsq]
  field_simp
  try ring
