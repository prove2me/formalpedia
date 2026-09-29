-- Prove2me | solution 1 for EdmondsKarp.Scaling.scaling_augmentation_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:10:17.889151+00:00
-- url     : https://prove2.me/submissions/8583679c-f109-4d4c-ae3f-cbe10c750954

import Mathlib
import Definitions.Def_EdmondsKarp_Scaling_Transport
import Definitions.Def_EdmondsKarp_Scaling_Augmentation
import Definitions.Def_EdmondsKarp_Scaling_Run

namespace EdmondsKarp.Scaling

/-- integrality of a flow -/
def aux_sab_Int {m n : ℕ} (x : Flow m n) : Prop :=
  (∀ i, ∃ z : ℤ, x.f0 i = z) ∧ (∀ i j, ∃ z : ℤ, x.fx i j = z) ∧
    (∀ j, ∃ z : ℤ, x.fz j = z) ∧ ∃ z : ℤ, x.ret = z

theorem aux_sab_pathDir_int {m n : ℕ} (L : List (Node m n)) (u v : Node m n) :
    ∃ z : ℤ, pathDir L u v = z := by
  unfold pathDir
  split_ifs
  · exact ⟨0, by norm_num⟩
  · exact ⟨1, by norm_num⟩
  · exact ⟨-1, by norm_num⟩
  · exact ⟨0, by norm_num⟩

theorem aux_sab_value_le {m n : ℕ} (T : Transport m n) (x : Flow m n) (hx : IsFlow T x) :
    x.ret ≤ ∑ i, T.a i ∧ x.ret ≤ ∑ j, T.b j := by
  obtain ⟨_, _, _, _, ha, hb, h1, _, _, h4⟩ := hx
  constructor
  · have : ∑ i, x.f0 i ≤ ∑ i, T.a i := Finset.sum_le_sum (fun i _ => ha i)
    linarith
  · have : ∑ j, x.fz j ≤ ∑ j, T.b j := Finset.sum_le_sum (fun j _ => hb j)
    linarith

theorem aux_sab_value_ge {m n : ℕ} (T : Transport m n) (x : Flow m n) (hx : IsFlow T x)
    (hno : ¬ ∃ L, IsAugPath T x L) :
    min (∑ i, T.a i) (∑ j, T.b j) ≤ x.ret := by
  obtain ⟨_, _, _, _, ha, hb, h1, _, _, h4⟩ := hx
  by_contra hcon
  push Not at hcon
  have hA : x.ret < ∑ i, T.a i := lt_of_lt_of_le hcon (min_le_left _ _)
  have hB : x.ret < ∑ j, T.b j := lt_of_lt_of_le hcon (min_le_right _ _)
  have hA' : ∑ i, x.f0 i < ∑ i, T.a i := by linarith
  have hB' : ∑ j, x.fz j < ∑ j, T.b j := by linarith
  obtain ⟨i, _, hi⟩ := Finset.exists_lt_of_sum_lt hA'
  obtain ⟨j, _, hj⟩ := Finset.exists_lt_of_sum_lt hB'
  apply hno
  refine ⟨[.s, .src i, .dst j, .t], ?_, rfl, rfl, ?_⟩
  · simp
  · intro e he
    simp at he
    rcases he with rfl | rfl | rfl
    · simp only [resCap]
      exact WithTop.coe_pos.mpr (by linarith)
    · simp [resCap]
    · simp only [resCap]
      exact WithTop.coe_pos.mpr (by linarith)

theorem aux_sab_resCap_int {m n : ℕ} (T : Transport m n) (hTa : ∀ i, ∃ z : ℤ, T.a i = z)
    (hTb : ∀ j, ∃ z : ℤ, T.b j = z) (x : Flow m n) (hx : aux_sab_Int x) (u v : Node m n) :
    resCap T x u v = ⊤ ∨ ∃ z : ℤ, resCap T x u v = (((z : ℤ) : ℝ) : WithTop ℝ) := by
  obtain ⟨hf0, hfx, hfz, _⟩ := hx
  rcases u with _ | _ | i | j <;> rcases v with _ | _ | i' | j' <;> simp [resCap]
  · obtain ⟨z1, h1⟩ := hTa i'
    obtain ⟨z2, h2⟩ := hf0 i'
    exact ⟨z1 - z2, by rw [h1, h2]; norm_cast⟩
  · exact hfz j'
  · exact hf0 i
  · obtain ⟨z1, h1⟩ := hTb j
    obtain ⟨z2, h2⟩ := hfz j
    exact ⟨z1 - z2, by rw [h1, h2]; norm_cast⟩
  · exact hfx i' j


theorem aux_sab_step {m n : ℕ} (T : Transport m n) (hTa : ∀ i, ∃ z : ℤ, T.a i = z)
    (hTb : ∀ j, ∃ z : ℤ, T.b j = z) (x y : Flow m n) (hx : aux_sab_Int x)
    (h : AugStep T x y) : aux_sab_Int y ∧ x.ret + 1 ≤ y.ret := by
  obtain ⟨L, ε, hL, ⟨_, e, he, heq⟩, rfl⟩ := h
  have hpos : 0 < resCap T x e.1 e.2 := hL.2.2.2 e he
  rw [heq] at hpos
  have hε : 0 < ε := WithTop.coe_pos.mp hpos
  obtain ⟨zε, hzε⟩ : ∃ z : ℤ, ε = z := by
    rcases aux_sab_resCap_int T hTa hTb x hx e.1 e.2 with h | ⟨z, hz⟩
    · rw [h] at heq; exact absurd heq.symm WithTop.coe_ne_top
    · rw [hz] at heq; exact ⟨z, (WithTop.coe_inj.mp heq).symm⟩
  have hε1 : 1 ≤ ε := by
    rw [hzε] at hε ⊢
    have : (0:ℤ) < zε := by exact_mod_cast hε
    have : (1:ℤ) ≤ zε := this
    exact_mod_cast this
  obtain ⟨hf0, hfx, hfz, ⟨zr, hzr⟩⟩ := hx
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i
    obtain ⟨z1, h1⟩ := hf0 i
    obtain ⟨z3, h3⟩ := aux_sab_pathDir_int L .s (.src i)
    exact ⟨z1 + zε * z3, by simp only [augment]; rw [h1, hzε, h3]; push_cast; ring⟩
  · intro i j
    obtain ⟨z1, h1⟩ := hfx i j
    obtain ⟨z3, h3⟩ := aux_sab_pathDir_int L (.src i) (.dst j)
    exact ⟨z1 + zε * z3, by simp only [augment]; rw [h1, hzε, h3]; push_cast; ring⟩
  · intro j
    obtain ⟨z1, h1⟩ := hfz j
    obtain ⟨z3, h3⟩ := aux_sab_pathDir_int L (.dst j) .t
    exact ⟨z1 + zε * z3, by simp only [augment]; rw [h1, hzε, h3]; push_cast; ring⟩
  · exact ⟨zr + zε, by simp only [augment]; rw [hzr, hzε]; push_cast; ring⟩
  · simp only [augment]; linarith

theorem aux_sab_Int_zero {m n : ℕ} : aux_sab_Int (0 : Flow m n) :=
  ⟨fun _ => ⟨0, Int.cast_zero.symm⟩, fun _ _ => ⟨0, Int.cast_zero.symm⟩,
    fun _ => ⟨0, Int.cast_zero.symm⟩, ⟨0, Int.cast_zero.symm⟩⟩

theorem aux_sab_Int_two {m n : ℕ} (x : Flow m n) (hx : aux_sab_Int x) :
    aux_sab_Int ((2 : ℝ) • x) := by
  obtain ⟨hf0, hfx, hfz, ⟨zr, hzr⟩⟩ := hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨z, hz⟩ := hf0 i
    exact ⟨2 * z, by show (2:ℝ) * x.f0 i = _; rw [hz]; push_cast; ring⟩
  · intro i j
    obtain ⟨z, hz⟩ := hfx i j
    exact ⟨2 * z, by show (2:ℝ) * x.fx i j = _; rw [hz]; push_cast; ring⟩
  · intro j
    obtain ⟨z, hz⟩ := hfz j
    exact ⟨2 * z, by show (2:ℝ) * x.fz j = _; rw [hz]; push_cast; ring⟩
  · exact ⟨2 * zr, by show (2:ℝ) * x.ret = _; rw [hzr]; push_cast; ring⟩

theorem aux_sab_arith (l M q : ℕ) (K W : ℕ → ℕ)
    (hKW : ∀ p, p < l → K p + 2 * W (p + 1) ≤ W p)
    (hWM : ∀ p, W p ≤ 2 * W (p + 1) + M) (hWl : W l = 0) (hWq : W (q + 1) ≤ M) :
    ∑ p ∈ Finset.range l, K p ≤ M * (q + 2) := by
  have hK : ∀ p, p < l → K p ≤ M := by
    intro p hp
    have h1 := hKW p hp
    have h2 := hWM p
    omega
  have htel : ∀ t j, l - j = t → j ≤ l → ∑ p ∈ Finset.Ico j l, K p ≤ W j := by
    intro t
    induction t with
    | zero =>
      intro j hj hjl
      have : j = l := by omega
      subst this
      simp
    | succ t ih =>
      intro j hj hjl
      have hjl' : j < l := by omega
      rw [Finset.sum_eq_sum_Ico_succ_bot hjl']
      have h1 := ih (j + 1) (by omega) (by omega)
      have h2 := hKW j hjl'
      omega
  have hr : min (q + 1) l ≤ l := min_le_right _ _
  rw [← Finset.sum_range_add_sum_Ico _ hr]
  have hA : ∑ p ∈ Finset.range (min (q + 1) l), K p ≤ (min (q + 1) l) * M := by
    have := Finset.sum_le_card_nsmul (Finset.range (min (q + 1) l)) K M (by
      intro p hp
      rw [Finset.mem_range] at hp
      exact hK p (lt_of_lt_of_le hp hr))
    simpa using this
  have hB : ∑ p ∈ Finset.Ico (min (q + 1) l) l, K p ≤ M := by
    refine le_trans (htel _ _ rfl hr) ?_
    rcases le_total (q + 1) l with h | h
    · rw [min_eq_left h]; exact hWq
    · rw [min_eq_right h, hWl]; exact Nat.zero_le _
  have hC : (min (q + 1) l) * M ≤ (q + 1) * M := Nat.mul_le_mul_right _ (min_le_left _ _)
  nlinarith

end EdmondsKarp.Scaling

open EdmondsKarp.Scaling

theorem solution {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (a : Fin m → ℕ)
    (b : Fin n → ℕ) (d : Fin m → Fin n → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j)
    (hsum : ∑ i, a i = ∑ j, b j) (hd : ∀ i j, 0 ≤ d i j) (l : ℕ)
    (hla : ∀ i, a i < 2 ^ l) (hlb : ∀ j, b j < 2 ^ l) (K : ℕ → ℕ) (F : ℕ → ℕ → Flow m n)
    (hR : IsScalingRun a b d l K F) :
    ((∑ p ∈ Finset.range l, K p : ℕ) : ℤ) ≤
      ((max m n : ℕ) : ℤ) *
        (2 + ⌊Real.logb 2 (((∑ i, a i : ℕ) : ℝ) / ((max m n : ℕ) : ℝ))⌋) := by
  -- integrality of capacities
  have hTa : ∀ p, ∀ i, ∃ z : ℤ, (problem a b d p).a i = z :=
    fun p i => ⟨((a i / 2 ^ p : ℕ) : ℤ), (Int.cast_natCast _).symm⟩
  have hTb : ∀ p, ∀ j, ∃ z : ℤ, (problem a b d p).b j = z :=
    fun p j => ⟨((b j / 2 ^ p : ℕ) : ℤ), (Int.cast_natCast _).symm⟩
  -- one phase
  have phase : ∀ p, p < l → aux_sab_Int (F p 0) → ∀ k, k ≤ K p →
      aux_sab_Int (F p k) ∧ (F p 0).ret + k ≤ (F p k).ret := by
    intro p hp h0 k
    induction k with
    | zero => intro _; simpa using h0
    | succ k ih =>
      intro hk
      obtain ⟨h1, h2⟩ := ih (by omega)
      have := aux_sab_step _ (hTa p) (hTb p) _ _ h1 (hR.step p hp k (by omega))
      refine ⟨this.1, ?_⟩
      push_cast
      linarith [this.2]
  -- integrality of initial flows
  have hinit : ∀ t p, p < l → l - 1 - p = t → aux_sab_Int (F p 0) := by
    intro t
    induction t with
    | zero =>
      intro p hp ht
      have : p = l - 1 := by omega
      rw [this, hR.start]
      exact aux_sab_Int_zero
    | succ t ih =>
      intro p hp ht
      have hr := hR.restart (p + 1) (by omega) (by omega)
      simp only [Nat.add_sub_cancel] at hr
      rw [hr]
      exact aux_sab_Int_two _
        (phase (p + 1) (by omega) (ih (p + 1) (by omega) (by omega)) (K (p + 1)) le_rfl).1
  have hint : ∀ p, p < l → aux_sab_Int (F p 0) := fun p hp => hinit _ p hp rfl
  -- sums of capacities
  set A : ℕ → ℕ := fun p => ∑ i, a i / 2 ^ p with hAdef
  set B : ℕ → ℕ := fun p => ∑ j, b j / 2 ^ p with hBdef
  set W : ℕ → ℕ := fun p => min (A p) (B p) with hWdef
  have hsumA : ∀ p, ∑ i, (problem a b d p).a i = ((A p : ℕ) : ℝ) := by
    intro p; simp only [hAdef]; rw [Nat.cast_sum]; rfl
  have hsumB : ∀ p, ∑ j, (problem a b d p).b j = ((B p : ℕ) : ℝ) := by
    intro p; simp only [hBdef]; rw [Nat.cast_sum]; rfl
  have hWl : W l = 0 := by
    have : A l = 0 := Finset.sum_eq_zero (fun i _ => Nat.div_eq_of_lt (hla i))
    simp only [hWdef, this]; simp
  have hKW : ∀ p, p < l → K p + 2 * W (p + 1) ≤ W p := by
    intro p hp
    have hflow := (hR.pseudo p hp (K p) le_rfl).1
    obtain ⟨hle1, hle2⟩ := aux_sab_value_le _ _ hflow
    rw [hsumA] at hle1
    rw [hsumB] at hle2
    have hph := (phase p hp (hint p hp) (K p) le_rfl).2
    have h0 : ((2 * W (p + 1) : ℕ) : ℝ) ≤ (F p 0).ret := by
      by_cases hpl : p + 1 < l
      · have hr := hR.restart (p + 1) (by omega) hpl
        simp only [Nat.add_sub_cancel] at hr
        rw [hr]
        show _ ≤ (2 : ℝ) * (F (p + 1) (K (p + 1))).ret
        have hge := aux_sab_value_ge _ _ (hR.pseudo (p + 1) hpl _ le_rfl).1 (hR.stop (p + 1) hpl)
        rw [hsumA, hsumB] at hge
        have : ((W (p + 1) : ℕ) : ℝ) = min ((A (p + 1) : ℕ) : ℝ) ((B (p + 1) : ℕ) : ℝ) := by
          simp only [hWdef]; push_cast; rfl
        push_cast
        rw [this]
        linarith
      · have hpe : p + 1 = l := by omega
        rw [hpe, hWl]
        have : p = l - 1 := by omega
        rw [this, hR.start]
        show ((2 * 0 : ℕ) : ℝ) ≤ 0
        simp
    have hWp : ((W p : ℕ) : ℝ) = min ((A p : ℕ) : ℝ) ((B p : ℕ) : ℝ) := by
      simp only [hWdef]; push_cast; rfl
    have : ((K p : ℕ) : ℝ) + ((2 * W (p + 1) : ℕ) : ℝ) ≤ ((W p : ℕ) : ℝ) := by
      rw [hWp]
      refine le_min ?_ ?_ <;> linarith
    exact_mod_cast this
  -- W p ≤ 2 W (p+1) + max m n
  have hdiv : ∀ (x p : ℕ), x / 2 ^ p ≤ 2 * (x / 2 ^ (p + 1)) + 1 := by
    intro x p
    rw [pow_succ, ← Nat.div_div_eq_div_mul]
    omega
  have hAM : ∀ p, A p ≤ 2 * A (p + 1) + m := by
    intro p
    simp only [hAdef]
    calc ∑ i, a i / 2 ^ p ≤ ∑ i, (2 * (a i / 2 ^ (p + 1)) + 1) :=
          Finset.sum_le_sum (fun i _ => hdiv (a i) p)
      _ = 2 * ∑ i, a i / 2 ^ (p + 1) + m := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]; simp
  have hBM : ∀ p, B p ≤ 2 * B (p + 1) + n := by
    intro p
    simp only [hBdef]
    calc ∑ j, b j / 2 ^ p ≤ ∑ j, (2 * (b j / 2 ^ (p + 1)) + 1) :=
          Finset.sum_le_sum (fun j _ => hdiv (b j) p)
      _ = 2 * ∑ j, b j / 2 ^ (p + 1) + n := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]; simp
  have hWM : ∀ p, W p ≤ 2 * W (p + 1) + max m n := by
    intro p
    have h1 := hAM p
    have h2 := hBM p
    simp only [hWdef]
    omega
  -- A p * 2^p ≤ S
  have hAS : ∀ p, A p * 2 ^ p ≤ ∑ i, a i := by
    intro p
    simp only [hAdef]
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun i _ => Nat.div_mul_le_self _ _)
  -- M ≤ S
  have hmS : m ≤ ∑ i, a i := by
    calc m = ∑ _i : Fin m, 1 := by simp
      _ ≤ ∑ i, a i := Finset.sum_le_sum (fun i _ => Nat.succ_le_of_lt (ha i))
  have hnS : n ≤ ∑ i, a i := by
    rw [hsum]
    calc n = ∑ _j : Fin n, 1 := by simp
      _ ≤ ∑ j, b j := Finset.sum_le_sum (fun j _ => Nat.succ_le_of_lt (hb j))
  have hMS : max m n ≤ ∑ i, a i := max_le hmS hnS
  have hMpos : 0 < max m n := lt_of_lt_of_le hm (le_max_left _ _)
  -- the real part
  have hMposR : (0 : ℝ) < ((max m n : ℕ) : ℝ) := by exact_mod_cast hMpos
  have h1x : (1 : ℝ) ≤ ((∑ i, a i : ℕ) : ℝ) / ((max m n : ℕ) : ℝ) := by
    rw [one_le_div hMposR]; exact_mod_cast hMS
  have hxpos : (0 : ℝ) < ((∑ i, a i : ℕ) : ℝ) / ((max m n : ℕ) : ℝ) := by linarith
  have hlog0 := Real.logb_nonneg one_lt_two h1x
  have hqz0 : 0 ≤ ⌊Real.logb 2 (((∑ i, a i : ℕ) : ℝ) / ((max m n : ℕ) : ℝ))⌋ :=
    Int.floor_nonneg.mpr hlog0
  have hlt := Int.lt_floor_add_one (Real.logb 2 (((∑ i, a i : ℕ) : ℝ) / ((max m n : ℕ) : ℝ)))
  set qz := ⌊Real.logb 2 (((∑ i, a i : ℕ) : ℝ) / ((max m n : ℕ) : ℝ))⌋ with hqzdef
  have hqq : ((qz.toNat : ℕ) : ℤ) = qz := Int.toNat_of_nonneg hqz0
  have hqR : ((qz.toNat : ℕ) : ℝ) = (qz : ℝ) := by
    rw [← Int.cast_natCast]; exact congrArg _ hqq
  have hlt' : Real.logb 2 (((∑ i, a i : ℕ) : ℝ) / ((max m n : ℕ) : ℝ)) <
      ((qz.toNat + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_add, Nat.cast_one, hqR]; exact hlt
  have hx2 := (Real.logb_lt_iff_lt_rpow one_lt_two hxpos).mp hlt'
  rw [Real.rpow_natCast, div_lt_iff₀ hMposR] at hx2
  have hSlt : ∑ i, a i < max m n * 2 ^ (qz.toNat + 1) := by
    have : ((∑ i, a i : ℕ) : ℝ) < ((max m n * 2 ^ (qz.toNat + 1) : ℕ) : ℝ) := by
      push_cast; push_cast at hx2; linarith
    exact_mod_cast this
  have hWq : W (qz.toNat + 1) ≤ max m n := by
    have h1 := hAS (qz.toNat + 1)
    have h2 : A (qz.toNat + 1) < max m n :=
      Nat.lt_of_mul_lt_mul_right (lt_of_le_of_lt h1 hSlt)
    have h3 : W (qz.toNat + 1) ≤ A (qz.toNat + 1) := min_le_left _ _
    omega
  have hfin := aux_sab_arith l (max m n) qz.toNat K W hKW hWM hWl hWq
  have hfinZ : ((∑ p ∈ Finset.range l, K p : ℕ) : ℤ) ≤
      ((max m n * (qz.toNat + 2) : ℕ) : ℤ) := by exact_mod_cast hfin
  rw [← hqq]
  push_cast at hfinZ ⊢
  linarith
