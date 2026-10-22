-- Prove2me | solution 1 for DERAggregation.MarketPower.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T22:01:24.578564+00:00
-- url     : https://prove2.me/submissions/777b840c-cd6d-4c13-b6e7-645aca9b2a1b

import Mathlib
import Definitions.Def_DERAggregation_MarketPower_Setting

set_option autoImplicit false

namespace EB55Aux

open DERAggregation.MarketPower Finset

theorem key_id {ι : Type*} (a b C : ι → ℝ) (lam : ℝ) (i : ι) (ha : a i < 0) (z : ℝ) :
    u a b i (C i + z) - lam * z =
      (u a b i (C i + zT a b C lam i) - lam * zT a b C lam i) +
        a i * (z - zT a b C lam i) ^ 2 := by
  have ha' : a i ≠ 0 := ne_of_lt ha
  unfold u zT
  field_simp
  ring

theorem zT_shift {ι : Type*} (a b C : ι → ℝ) (α lam : ℝ) (i : ι) :
    zT a b C lam i = zT a b C α i + (lam - α) * (1 / (2 * a i)) := by
  unfold zT; ring

theorem zT_gt {ι : Type*} (a b C : ι → ℝ) (lam : ℝ) (i : ι) (ha : a i < 0) (hl : lam < b i) :
    -C i < zT a b C lam i := by
  unfold zT
  have : 0 < (lam - b i) / (2 * a i) := div_pos_of_neg_of_neg (by linarith) (by linarith)
  linarith

theorem respP {ι : Type*} (a b C : ι → ℝ) (lam : ℝ) (i : ι) (ha : a i < 0) (z : ℝ)
    (h : IsRespP a b C lam i z) : z = zT a b C lam i := by
  obtain ⟨hz, hopt⟩ := h
  have hid := key_id a b C lam i ha
  rcases lt_or_ge (-C i) (zT a b C lam i) with h1 | h1
  · have h0 := hopt _ h1
    have e1 := hid (zT a b C lam i)
    have e2 := hid z
    simp only [sub_self] at e1
    have h2 : (z - zT a b C lam i) ^ 2 ≤ 0 := by
      nlinarith [sq_nonneg (z - zT a b C lam i)]
    have h3 : (z - zT a b C lam i) ^ 2 = 0 := le_antisymm h2 (sq_nonneg _)
    have h4 : z - zT a b C lam i = 0 := by simpa using h3
    linarith
  · exfalso
    have h3 : -C i < (z - C i) / 2 := by linarith
    have h0 := hopt _ h3
    have e1 := hid ((z - C i) / 2)
    have e2 := hid z
    have hp1 : 0 < (z - C i) / 2 - zT a b C lam i := by linarith
    have hp2 : (z - C i) / 2 - zT a b C lam i < z - zT a b C lam i := by linarith
    have hps : ((z - C i) / 2 - zT a b C lam i) ^ 2 < (z - zT a b C lam i) ^ 2 := by
      nlinarith
    have : a i * (((z - C i) / 2 - zT a b C lam i) ^ 2 - (z - zT a b C lam i) ^ 2) > 0 :=
      mul_pos_of_neg_of_neg ha (by linarith)
    nlinarith

theorem respP_of {ι : Type*} (a b C : ι → ℝ) (lam : ℝ) (i : ι) (ha : a i < 0)
    (hl : lam < b i) : IsRespP a b C lam i (zT a b C lam i) := by
  refine ⟨zT_gt a b C lam i ha hl, fun z' _ => ?_⟩
  have hid := key_id a b C lam i ha
  have e1 := hid z'
  have e2 := hid (zT a b C lam i)
  simp only [sub_self] at e2
  nlinarith [sq_nonneg (z' - zT a b C lam i)]

theorem respN {ι : Type*} (a b C : ι → ℝ) (lam : ℝ) (i : ι) (ha : a i < 0) (d : ℝ)
    (h : IsRespN a b C lam i d) : d = max 0 (zT a b C lam i) := by
  obtain ⟨hd, hopt⟩ := h
  have hid := key_id a b C lam i ha
  rcases le_or_gt 0 (zT a b C lam i) with h1 | h1
  · have h0 := hopt _ h1
    have e1 := hid (zT a b C lam i)
    have e2 := hid d
    simp only [sub_self] at e1
    have h2 : (d - zT a b C lam i) ^ 2 ≤ 0 := by
      nlinarith [sq_nonneg (d - zT a b C lam i)]
    have h3 : (d - zT a b C lam i) ^ 2 = 0 := le_antisymm h2 (sq_nonneg _)
    have h4 : d - zT a b C lam i = 0 := by simpa using h3
    rw [max_eq_right h1]; linarith
  · rw [max_eq_left h1.le]
    by_contra hne
    have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hne)
    have h0 := hopt 0 le_rfl
    have e1 := hid 0
    have e2 := hid d
    have hp : (0 - zT a b C lam i) ^ 2 < (d - zT a b C lam i) ^ 2 := by nlinarith
    have : a i * ((0 - zT a b C lam i) ^ 2 - (d - zT a b C lam i) ^ 2) > 0 :=
      mul_pos_of_neg_of_neg ha (by linarith)
    nlinarith

theorem respN_of {ι : Type*} (a b C : ι → ℝ) (lam : ℝ) (i : ι) (ha : a i < 0) :
    IsRespN a b C lam i (max 0 (zT a b C lam i)) := by
  have hid := key_id a b C lam i ha
  refine ⟨le_max_left _ _, fun d' hd' => ?_⟩
  have e1 := hid d'
  have e2 := hid (max 0 (zT a b C lam i))
  rcases le_or_gt 0 (zT a b C lam i) with h1 | h1
  · rw [max_eq_right h1] at e2 ⊢
    simp only [sub_self] at e2
    nlinarith [sq_nonneg (d' - zT a b C lam i)]
  · rw [max_eq_left h1.le] at e2 ⊢
    have h2 : (0 - zT a b C lam i) ^ 2 ≤ (d' - zT a b C lam i) ^ 2 := by nlinarith
    have h3 := mul_le_mul_of_nonpos_left h2 ha.le
    linarith

/-- Per-prosumer welfare comparison used for (46e). -/
theorem per_i (a k t d δ : ℝ) (ha : a < 0) (hak : 2 * a * k = 1) (hk : k < 0) (hd : 0 ≤ d)
    (hδ : 0 ≤ δ) :
    δ * (max 0 t - d) + δ ^ 2 * k / 2 ≤ a * (max 0 t - t) ^ 2 - a * (d - t) ^ 2 := by
  rcases le_total 0 t with h | h
  · rw [max_eq_right h]
    have key : a * (t - t) ^ 2 - a * (d - t) ^ 2 - (δ * (t - d) + δ ^ 2 * k / 2) =
        -a * (t - d + δ * k) ^ 2 := by
      linear_combination (δ * (t - d) + δ ^ 2 * k / 2) * hak
    have : 0 ≤ -a * (t - d + δ * k) ^ 2 :=
      mul_nonneg (by linarith) (sq_nonneg _)
    linarith
  · rw [max_eq_left h]
    have h1 : 0 ≤ -a * d ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    have h2 : 0 ≤ d * (a * t) := mul_nonneg hd (mul_nonneg_of_nonpos_of_nonpos ha.le h)
    have h3 : 0 ≤ δ * d := mul_nonneg hδ hd
    have h4 : δ ^ 2 * k ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hk.le
    nlinarith

theorem per_i_le (a t d : ℝ) (ha : a < 0) (hd : 0 ≤ d) :
    a * (d - t) ^ 2 ≤ a * (max 0 t - t) ^ 2 := by
  rcases le_total 0 t with h | h
  · rw [max_eq_right h]; simp only [sub_self]
    nlinarith [sq_nonneg (d - t)]
  · rw [max_eq_left h]
    have h2 : (0 - t) ^ 2 ≤ (d - t) ^ 2 := by nlinarith
    have h3 := mul_le_mul_of_nonpos_left h2 ha.le
    linarith

theorem welT_eq {ι : Type*} [Fintype ι] (a b C : ι → ℝ) (α : ℝ) (N : ℕ) (z : ι → ℝ)
    (y : Fin N → ℝ) (h : ∑ j, y j = ∑ i, z i) :
    welT a b C α N z y = ∑ i, (u a b i (C i + z i) - α * z i) := by
  unfold welT
  rw [← Finset.mul_sum, h, Finset.mul_sum, Finset.sum_sub_distrib]

theorem welS_eq {ι : Type*} [Fintype ι] (a b C : ι → ℝ) (α : ℝ) (N : ℕ) (z : ι → ℝ)
    (q : ℝ) (h : ∑ i, z i = (N : ℝ) * q) :
    welS a b C α N z q = ∑ i, (u a b i (C i + z i) - α * z i) := by
  unfold welS
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, h]; ring

theorem welSN_eq {ι : Type*} [Fintype ι] (a b C : ι → ℝ) (α : ℝ) (N : ℕ) (z : ι → ℝ)
    (q : ℝ) (h : ∑ i, z i = (N : ℝ) * q) :
    welSN a b C α N z q = ∑ i, (u a b i (C i + z i) - α * z i) := by
  unfold welSN
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, h]; ring

theorem sum_const_fin (N : ℕ) (hN : 1 ≤ N) (S : ℝ) : ∑ _j : Fin N, S / (N : ℝ) = S := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : (N : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  field_simp

/-- The strategic outcome with participation is the linear Cournot equilibrium. -/
theorem stratP_eq {ι : Type*} [Fintype ι] (a b C : ι → ℝ) (α : ℝ) (N : ℕ)
    (ha : ∀ i, a i < 0) (hN : 1 ≤ N)
    (hS : 0 < ∑ i, zT a b C α i)
    (hV : ∑ i, 1 / (2 * a i) < 0)
    (hlam : ∀ T : ℝ, 0 ≤ T → ∀ i,
      α + (T - ∑ l, zT a b C α l) / (∑ l, 1 / (2 * a l)) < b i)
    (q lam : ℝ) (z : ι → ℝ) (h : IsStratP a b C α N q lam z) :
    (∀ i, z i = zT a b C α i + (lam - α) * (1 / (2 * a i))) ∧
    ((N : ℝ) + 1) * q = ∑ i, zT a b C α i ∧
    (lam - α) * (∑ i, 1 / (2 * a i)) = -q ∧ 0 ≤ q ∧ ∑ i, z i = (N : ℝ) * q := by
  obtain ⟨hq, ⟨hresp, hsum⟩, hdev⟩ := h
  have hz : ∀ i, z i = zT a b C α i + (lam - α) * (1 / (2 * a i)) := fun i => by
    rw [respP a b C lam i (ha i) (z i) (hresp i), zT_shift a b C α lam i]
  have hsum' : (∑ i, zT a b C α i) + (lam - α) * (∑ i, 1 / (2 * a i)) = (N : ℝ) * q := by
    rw [← hsum, Finset.sum_congr rfl (fun i _ => hz i), Finset.sum_add_distrib,
      ← Finset.mul_sum]
  set S := ∑ i, zT a b C α i with hSdef
  set V := ∑ i, 1 / (2 * a i) with hVdef
  have hdev' : ∀ q' : ℝ, 0 ≤ q' →
      ((N : ℝ) * q - S) * q ≤ (q' + ((N : ℝ) - 1) * q - S) * q' := by
    intro q' hq'
    have hT : 0 ≤ q' + ((N : ℝ) - 1) * q := by
      have : (1 : ℝ) ≤ N := by exact_mod_cast hN
      nlinarith
    set T := q' + ((N : ℝ) - 1) * q with hTdef
    set lam' := α + (T - S) / V with hlam'
    have hV0 : V ≠ 0 := ne_of_lt hV
    have hcl : ClearsP a b C T lam' (fun i => zT a b C lam' i) := by
      refine ⟨fun i => respP_of a b C lam' i (ha i) (hlam T hT i), ?_⟩
      simp only
      rw [Finset.sum_congr rfl (fun i _ => zT_shift a b C α lam' i), Finset.sum_add_distrib,
        ← Finset.mul_sum, hlam']
      field_simp
      ring
    have h0 := hdev q' lam' (fun i => zT a b C lam' i) hq' hcl
    have e1 : (lam' - α) * V = T - S := by rw [hlam']; field_simp; ring
    have h1 : (lam' - α) * q' ≤ (lam - α) * q := by linarith
    have h2 := mul_le_mul_of_nonpos_left h1 hV.le
    have e1q : V * ((lam' - α) * q') = (T - S) * q' := by rw [← e1]; ring
    have e2q : V * ((lam - α) * q) = ((N : ℝ) * q - S) * q := by
      rw [show V * ((lam - α) * q) = ((lam - α) * V) * q by ring]
      rw [show (lam - α) * V = (N : ℝ) * q - S by linarith]
    linarith
  have hNq : ((N : ℝ) + 1) * q = S := by
    set K := S - ((N : ℝ) - 1) * q with hK
    rcases le_or_gt 0 K with hK0 | hK0
    · have h0 := hdev' (K / 2) (by linarith)
      have h1 : (q - K / 2) ^ 2 ≤ 0 := by nlinarith
      have h2 : (q - K / 2) ^ 2 = 0 := le_antisymm h1 (sq_nonneg _)
      have h3 : q - K / 2 = 0 := by simpa using h2
      linarith
    · exfalso
      have h0 := hdev' 0 le_rfl
      have h1 : 0 < q - K := by linarith
      have h2 : q * (q - K) ≤ 0 := by nlinarith
      have h3 : q = 0 := by nlinarith
      rw [h3] at hK
      linarith
  refine ⟨hz, hNq, ?_, hq, hsum⟩
  linarith

/-- At a strategic outcome without participation, the shortfall `Σ (max 0 zT_i − d_i)`
is at least the per-generator supply. -/
theorem stratN_bound {ι : Type*} [Fintype ι] (a b C : ι → ℝ) (α : ℝ) (N : ℕ)
    (ha : ∀ i, a i < 0) (q lam : ℝ) (d : ι → ℝ) (h : IsStratN a b C α N q lam d) :
    (∀ i, 0 ≤ d i) ∧ ∑ i, d i = (N : ℝ) * q ∧ 0 ≤ q ∧
    q ≤ ∑ i, (max 0 (zT a b C α i) - d i) := by
  obtain ⟨hq, ⟨hresp, hsum⟩, hdev⟩ := h
  have hd0 : ∀ i, 0 ≤ d i := fun i => (hresp i).1
  have hd : ∀ i, d i = max 0 (zT a b C α i + (lam - α) * (1 / (2 * a i))) := fun i => by
    rw [respN a b C lam i (ha i) (d i) (hresp i), zT_shift a b C α lam i]
  have hk : ∀ i, 1 / (2 * a i) < 0 := fun i => by
    apply div_neg_of_pos_of_neg one_pos; linarith [ha i]
  refine ⟨hd0, hsum, hq, ?_⟩
  set WJ := ∑ i, (if 0 < d i then -(1 / (2 * a i)) else 0) with hWJ
  have hWJ0 : 0 ≤ WJ := Finset.sum_nonneg (fun i _ => by
    split_ifs
    · linarith [hk i]
    · exact le_rfl)
  have hact : ∀ i, 0 < d i → d i = zT a b C α i + (lam - α) * (1 / (2 * a i)) := by
    intro i hi
    have := hd i
    rcases le_total 0 (zT a b C α i + (lam - α) * (1 / (2 * a i))) with h1 | h1
    · rw [max_eq_right h1] at this; exact this
    · rw [max_eq_left h1] at this; linarith
  have hlow : (lam - α) * WJ ≤ ∑ i, (max 0 (zT a b C α i) - d i) := by
    rw [hWJ, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    split_ifs with hi
    · have h1 := hact i hi
      have h2 := le_max_right 0 (zT a b C α i)
      linarith
    · have h1 : d i = 0 := le_antisymm (not_lt.mp hi) (hd0 i)
      have h2 := le_max_left 0 (zT a b C α i)
      rw [h1, mul_zero]; linarith
  have hmain : q ≤ (lam - α) * WJ := by
    rcases eq_or_lt_of_le hq with hq0 | hqpos
    · have hz : ∀ i, d i = 0 := by
        have h0 : ∑ i, d i = 0 := by rw [hsum, ← hq0, mul_zero]
        intro i
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hd0 i)).mp h0 i (Finset.mem_univ _)
      have h0 : WJ = 0 := by
        rw [hWJ]; apply Finset.sum_eq_zero; intro i _; simp [hz i]
      rw [h0, mul_zero, ← hq0]
    · by_contra hlt0
      have hlt := not_le.mp hlt0
      set g := q - (lam - α) * WJ with hg
      have hgpos : 0 < g := by linarith
      set m := min g q with hm
      have hmpos : 0 < m := lt_min hgpos hqpos
      have hW1 : 0 < 4 * (WJ + 1) := by linarith
      set η := m / (4 * (WJ + 1)) with hη
      have hηpos : 0 < η := div_pos hmpos hW1
      have hηW : η * WJ ≤ m / 4 := by
        have e : η * (4 * (WJ + 1)) = m := by rw [hη]; field_simp
        nlinarith
      set lam' := lam + η with hlam'
      set d' : ι → ℝ := fun i => max 0 (zT a b C lam' i) with hd'
      have hd'eq : ∀ i, d' i =
          max 0 (zT a b C α i + (lam - α) * (1 / (2 * a i)) + η * (1 / (2 * a i))) := by
        intro i
        simp only [hd']
        rw [zT_shift a b C α lam' i, hlam']
        congr 1; ring
      have hlo : ∀ i, d i - η * (if 0 < d i then -(1 / (2 * a i)) else 0) ≤ d' i := by
        intro i
        rw [hd'eq i]
        split_ifs with hi
        · have h1 := hact i hi
          have h2 := le_max_right 0
            (zT a b C α i + (lam - α) * (1 / (2 * a i)) + η * (1 / (2 * a i)))
          linarith
        · have h1 : d i = 0 := le_antisymm (not_lt.mp hi) (hd0 i)
          have h2 := le_max_left 0
            (zT a b C α i + (lam - α) * (1 / (2 * a i)) + η * (1 / (2 * a i)))
          rw [h1]; linarith
      have hup : ∀ i, d' i ≤ d i := by
        intro i
        rw [hd'eq i, hd i]
        apply max_le_max le_rfl
        have : η * (1 / (2 * a i)) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hηpos.le (hk i).le
        linarith
      set q' := ∑ i, d' i - ((N : ℝ) - 1) * q with hq'
      have hsumlo : (N : ℝ) * q - η * WJ ≤ ∑ i, d' i := by
        rw [← hsum, hWJ, Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_le_sum (fun i _ => hlo i)
      have hsumup : ∑ i, d' i ≤ (N : ℝ) * q := by
        rw [← hsum]; exact Finset.sum_le_sum (fun i _ => hup i)
      have hq'lo : q - η * WJ ≤ q' := by rw [hq']; linarith
      have hq'up : q' ≤ q := by rw [hq']; linarith
      have hmq : m ≤ q := min_le_right _ _
      have hmg : m ≤ g := min_le_left _ _
      have hq'0 : 0 ≤ q' := by linarith
      have hcl : ClearsN a b C (q' + ((N : ℝ) - 1) * q) lam' d' := by
        refine ⟨fun i => respN_of a b C lam' i (ha i), ?_⟩
        rw [hq']; ring
      have h0 := hdev q' lam' d' hq'0 hcl
      have h1 : (lam - α + η) * q' ≤ (lam - α) * q := by rw [hlam'] at h0; linarith
      rcases le_or_gt 0 (lam - α + η) with hc | hc
      · have h2 := mul_le_mul_of_nonneg_left hq'lo hc
        have h3 : η * q ≤ η * ((lam - α + η) * WJ) := by nlinarith
        have h4 : q ≤ (lam - α + η) * WJ := le_of_mul_le_mul_left h3 hηpos
        nlinarith
      · have h2 := mul_le_mul_of_nonpos_left hq'up hc.le
        nlinarith [mul_pos hηpos hqpos]
  exact le_trans hmain hlow

end EB55Aux

open DERAggregation.MarketPower Finset in
theorem solution {ι : Type*} [Fintype ι] (a b C : ι → ℝ) (α : ℝ) (N : ℕ)
    (h5 : Assumption5 a b C α N) :
    WTN a b C α N ≤ WT a b C α N ∧
    (∀ (q lam : ℝ) (z : ι → ℝ) (qN lamN : ℝ) (d : ι → ℝ),
      IsStratP a b C α N q lam z → IsStratN a b C α N qN lamN d →
        welSN a b C α N d qN ≤ welS a b C α N z q) ∧
    (∀ (q lam : ℝ) (z : ι → ℝ), IsStratP a b C α N q lam z →
      welS a b C α N z q ≤ WT a b C α N) ∧
    (∀ (qN lamN : ℝ) (d : ι → ℝ), IsStratN a b C α N qN lamN d →
      welSN a b C α N d qN ≤ WTN a b C α N) ∧
    (∀ (q lam : ℝ) (z : ι → ℝ) (qN lamN : ℝ) (d : ι → ℝ),
      IsStratP a b C α N q lam z → IsStratN a b C α N qN lamN d →
        WT a b C α N - welS a b C α N z q ≤ WTN a b C α N - welSN a b C α N d qN) := by
  obtain ⟨ha, _hα, _hC, hN, H1, H2, ⟨i0, _⟩⟩ := h5
  have : Nonempty ι := ⟨i0⟩
  have hk : ∀ i, 1 / (2 * a i) < 0 := fun i => by
    apply div_neg_of_pos_of_neg one_pos; linarith [ha i]
  have hak : ∀ i, 2 * a i * (1 / (2 * a i)) = 1 := fun i => by
    have : a i ≠ 0 := ne_of_lt (ha i)
    field_simp
  have hV : ∑ i, 1 / (2 * a i) < 0 := by
    have := Finset.sum_lt_sum_of_nonempty (g := fun _ => (0 : ℝ)) Finset.univ_nonempty
      (fun i _ => hk i)
    simpa using this
  have hV0 : (∑ i, 1 / (2 * a i)) ≠ 0 := ne_of_lt hV
  have hS1 : ∑ i, zT a b C α i = -(∑ i, C i) + ∑ i, (α - b i) / (2 * a i) := by
    unfold zT; rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]
  have hS2 : ∑ i, (α - b i) / (2 * a i) =
      α * (∑ i, 1 / (2 * a i)) - ∑ i, b i / (2 * a i) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _; ring
  have hS : 0 < ∑ i, zT a b C α i := by rw [hS1]; exact H2
  have hαP : α < ((∑ l, C l) + (∑ l, b l / (2 * a l))) / (∑ l, 1 / (2 * a l)) := by
    rw [lt_div_iff_of_neg hV]; linarith
  have hαb : ∀ i, α < b i := fun i => lt_trans hαP (H1 i)
  have hlam : ∀ T : ℝ, 0 ≤ T → ∀ i,
      α + (T - ∑ l, zT a b C α l) / (∑ l, 1 / (2 * a l)) < b i := by
    intro T hT i
    have key : ∀ (V c B T : ℝ), V ≠ 0 →
        α + (T - (-c + (α * V - B))) / V = T / V + (c + B) / V := by
      intro V c B T hV; field_simp; ring
    rw [hS1, hS2, key _ _ _ _ hV0]
    have : T / (∑ l, 1 / (2 * a l)) ≤ 0 := div_nonpos_of_nonneg_of_nonpos hT hV.le
    linarith [H1 i]
  -- per-term upper bounds
  have hub : ∀ z : ι → ℝ, ∑ i, (u a b i (C i + z i) - α * z i) ≤
      ∑ i, (u a b i (C i + zT a b C α i) - α * zT a b C α i) := by
    intro z
    apply Finset.sum_le_sum; intro i _
    have := EB55Aux.key_id a b C α i (ha i) (z i)
    nlinarith [sq_nonneg (z i - zT a b C α i), ha i]
  have hubN : ∀ d : ι → ℝ, (∀ i, 0 ≤ d i) → ∑ i, (u a b i (C i + d i) - α * d i) ≤
      ∑ i, (u a b i (C i + max 0 (zT a b C α i)) - α * max 0 (zT a b C α i)) := by
    intro d hd
    apply Finset.sum_le_sum; intro i _
    have e1 := EB55Aux.key_id a b C α i (ha i) (d i)
    have e2 := EB55Aux.key_id a b C α i (ha i) (max 0 (zT a b C α i))
    have := EB55Aux.per_i_le (a i) (zT a b C α i) (d i) (ha i) (hd i)
    linarith
  have hWT : WT a b C α N = ∑ i, (u a b i (C i + zT a b C α i) - α * zT a b C α i) := by
    apply IsGreatest.csSup_eq
    refine ⟨⟨zT a b C α, fun _ => (∑ i, zT a b C α i) / N,
      ⟨fun i => EB55Aux.zT_gt a b C α i (ha i) (hαb i),
        fun _ => div_nonneg hS.le (Nat.cast_nonneg _), EB55Aux.sum_const_fin N hN _⟩, ?_⟩, ?_⟩
    · rw [EB55Aux.welT_eq a b C α N _ _ (EB55Aux.sum_const_fin N hN _)]
    · rintro w ⟨z, y, ⟨_, _, hsum⟩, rfl⟩
      rw [EB55Aux.welT_eq a b C α N z y hsum]
      exact hub z
  have hWTN : WTN a b C α N =
      ∑ i, (u a b i (C i + max 0 (zT a b C α i)) - α * max 0 (zT a b C α i)) := by
    apply IsGreatest.csSup_eq
    refine ⟨⟨fun i => max 0 (zT a b C α i), fun _ => (∑ i, max 0 (zT a b C α i)) / N,
      ⟨fun i => le_max_left _ _,
        fun _ => div_nonneg (Finset.sum_nonneg (fun i _ => le_max_left _ _)) (Nat.cast_nonneg _),
        EB55Aux.sum_const_fin N hN _⟩, ?_⟩, ?_⟩
    · rw [EB55Aux.welT_eq a b C α N _ _ (EB55Aux.sum_const_fin N hN _)]
    · rintro w ⟨d, y, ⟨hd, _, hsum⟩, rfl⟩
      rw [EB55Aux.welT_eq a b C α N d y hsum]
      exact hubN d hd
  have h46a : WTN a b C α N ≤ WT a b C α N := by
    rw [hWT, hWTN]
    exact hub (fun i => max 0 (zT a b C α i))
  have h46c : ∀ (q lam : ℝ) (z : ι → ℝ), IsStratP a b C α N q lam z →
      welS a b C α N z q ≤ WT a b C α N := by
    intro q lam z hP
    obtain ⟨_, _, _, _, hsumz⟩ := EB55Aux.stratP_eq a b C α N ha hN hS hV hlam q lam z hP
    rw [hWT, EB55Aux.welS_eq a b C α N z q hsumz]
    exact hub z
  have h46d : ∀ (qN lamN : ℝ) (d : ι → ℝ), IsStratN a b C α N qN lamN d →
      welSN a b C α N d qN ≤ WTN a b C α N := by
    intro qN lamN d hNs
    obtain ⟨hd0, hsumd, _, _⟩ := EB55Aux.stratN_bound a b C α N ha qN lamN d hNs
    rw [hWTN, EB55Aux.welSN_eq a b C α N d qN hsumd]
    exact hubN d hd0
  have h46e : ∀ (q lam : ℝ) (z : ι → ℝ) (qN lamN : ℝ) (d : ι → ℝ),
      IsStratP a b C α N q lam z → IsStratN a b C α N qN lamN d →
        WT a b C α N - welS a b C α N z q ≤ WTN a b C α N - welSN a b C α N d qN := by
    intro q lam z qN lamN d hP hNs
    obtain ⟨hz, hNq, hδV, hq, hsumz⟩ := EB55Aux.stratP_eq a b C α N ha hN hS hV hlam q lam z hP
    obtain ⟨hd0, hsumd, _hqN, hbound⟩ := EB55Aux.stratN_bound a b C α N ha qN lamN d hNs
    rw [hWT, hWTN, EB55Aux.welS_eq a b C α N z q hsumz, EB55Aux.welSN_eq a b C α N d qN hsumd,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    have hδ : 0 ≤ lam - α := by
      by_contra hneg0
      have hneg := not_le.mp hneg0
      have : 0 < (lam - α) * ∑ i, 1 / (2 * a i) := mul_pos_of_neg_of_neg hneg hV
      linarith
    have hL : ∀ i, (u a b i (C i + zT a b C α i) - α * zT a b C α i) -
        (u a b i (C i + z i) - α * z i) = -((lam - α) ^ 2 * (1 / (2 * a i)) / 2) := by
      intro i
      have e := EB55Aux.key_id a b C α i (ha i) (z i)
      rw [e, hz i]
      linear_combination (-((lam - α) ^ 2 * (1 / (2 * a i)) / 2)) * hak i
    have hR : ∀ i, (lam - α) * (max 0 (zT a b C α i) - d i) +
        (lam - α) ^ 2 * (1 / (2 * a i)) / 2 ≤
        (u a b i (C i + max 0 (zT a b C α i)) - α * max 0 (zT a b C α i)) -
          (u a b i (C i + d i) - α * d i) := by
      intro i
      have e1 := EB55Aux.key_id a b C α i (ha i) (max 0 (zT a b C α i))
      have e2 := EB55Aux.key_id a b C α i (ha i) (d i)
      have := EB55Aux.per_i (a i) (1 / (2 * a i)) (zT a b C α i) (d i) (lam - α) (ha i)
        (hak i) (hk i) (hd0 i) hδ
      linarith
    rw [Finset.sum_congr rfl (fun i _ => hL i)]
    have hR' := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hR i)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hR'
    have hs1 : ∑ i, (lam - α) ^ 2 * (1 / (2 * a i)) / 2 =
        (lam - α) ^ 2 * (∑ i, 1 / (2 * a i)) / 2 := by
      rw [Finset.mul_sum, Finset.sum_div]
    have hs2 : ∑ i, -((lam - α) ^ 2 * (1 / (2 * a i)) / 2) =
        -((lam - α) ^ 2 * (∑ i, 1 / (2 * a i)) / 2) := by
      rw [Finset.sum_neg_distrib, hs1]
    rw [hs2]
    rw [hs1] at hR'
    have hq_le : q ≤ ∑ i, (max 0 (zT a b C α i) - d i) := by
      have hmax : ∑ i, zT a b C α i ≤ ∑ i, max 0 (zT a b C α i) :=
        Finset.sum_le_sum (fun i _ => le_max_right _ _)
      have hsplit : ∑ i, (max 0 (zT a b C α i) - d i) =
          ∑ i, max 0 (zT a b C α i) - ∑ i, d i := Finset.sum_sub_distrib _ _
      have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
      have h1 := mul_le_mul_of_nonneg_left hbound hN0
      have h2 : ((N : ℝ) + 1) * q ≤ ((N : ℝ) + 1) * ∑ i, (max 0 (zT a b C α i) - d i) := by
        rw [hNq]; nlinarith
      exact le_of_mul_le_mul_left h2 (by positivity)
    have h3 := mul_le_mul_of_nonneg_left hq_le hδ
    have h4 : (lam - α) ^ 2 * (∑ i, 1 / (2 * a i)) = -((lam - α) * q) := by
      rw [show (lam - α) ^ 2 * (∑ i, 1 / (2 * a i)) =
        (lam - α) * ((lam - α) * (∑ i, 1 / (2 * a i))) by ring, hδV]
      ring
    linarith
  refine ⟨h46a, ?_, h46c, h46d, h46e⟩
  intro q lam z qN lamN d hP hNs
  have := h46e q lam z qN lamN d hP hNs
  linarith
