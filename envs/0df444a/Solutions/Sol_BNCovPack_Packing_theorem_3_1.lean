-- Prove2me | solution 1 for BNCovPack.Packing.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T04:07:56.244655+00:00
-- url     : https://prove2.me/submissions/93fb0824-7ea9-47f3-b9d5-b5d093ed7bdf

import Mathlib
import Definitions.Def_OnlinePrimalDual_GeneralPacking_GeneralInstance
import Definitions.Def_OnlinePrimalDual_GeneralPacking_aMax
import Definitions.Def_OnlinePrimalDual_GeneralPacking_aMin
import Definitions.Def_BNCovPack_Packing_Scheme

set_option autoImplicit false

namespace BNCovPackPf

open OnlinePrimalDual.GeneralPacking BNCovPack.Packing

theorem exp_sub_le (u v : ℝ) : Real.exp u - Real.exp v ≤ (u - v) * Real.exp u := by
  have h1 : Real.exp v = Real.exp u * Real.exp (v - u) := by
    rw [← Real.exp_add]; congr 1; ring
  have h2 := Real.add_one_le_exp (v - u)
  have h3 := Real.exp_pos u
  rw [h1]
  nlinarith

theorem alg (c B P β Sy a T x : ℝ) (hc : 0 < c) (hβ : β = B / (2 * c)) (hP : 0 ≤ P)
    (hx0 : P * (Real.exp (β * Sy) - 1) ≤ x) :
    c * (P * (Real.exp (β * (Sy + a * T)) - 1) - x) ≤
      T * (B / 2) * (a * (P * (Real.exp (β * (Sy + a * T)) - 1) + P)) := by
  have h1 := exp_sub_le (β * (Sy + a * T)) (β * Sy)
  have hcb : c * β = B / 2 := by
    rw [hβ, mul_div_assoc', div_eq_div_iff (mul_pos two_pos hc).ne' two_ne_zero]; ring
  have e : β * (Sy + a * T) - β * Sy = β * (a * T) := by ring
  rw [e] at h1
  have h2 : c * (P * (Real.exp (β * (Sy + a * T)) - 1) - x) ≤
      c * P * (Real.exp (β * (Sy + a * T)) - Real.exp (β * Sy)) := by
    nlinarith [mul_le_mul_of_nonneg_left hx0 hc.le]
  have h3 : c * P * (Real.exp (β * (Sy + a * T)) - Real.exp (β * Sy)) ≤
      c * P * (β * (a * T) * Real.exp (β * (Sy + a * T))) :=
    mul_le_mul_of_nonneg_left h1 (mul_nonneg hc.le hP)
  calc _ ≤ _ := h2
    _ ≤ _ := h3
    _ = (c * β) * (a * T * P * Real.exp (β * (Sy + a * T))) := by ring
    _ = _ := by rw [hcb]; ring

theorem alg2 (a p n β S : ℝ) (ha : 0 < a) (hp : 0 < p) (hn : 0 < n) (hβ : 0 < β)
    (hS : a * (n * p / (β * a ^ 2)) ≤ S) : 1 ≤ a * (1 / (n * p) * (Real.exp (β * S) - 1)) := by
  have h1 : n * p / a ≤ β * S := by
    have : β * (a * (n * p / (β * a ^ 2))) = n * p / a := by
      field_simp
    rw [← this]; exact mul_le_mul_of_nonneg_left hS hβ.le
  have h2 := Real.add_one_le_exp (β * S)
  have h3 : n * p / a ≤ Real.exp (β * S) - 1 := by linarith
  rw [show a * (1 / (n * p) * (Real.exp (β * S) - 1)) = a * (Real.exp (β * S) - 1) / (n * p) by
    ring]
  rw [le_div_iff₀ (mul_pos hn hp), one_mul]
  have := mul_le_mul_of_nonneg_left h3 ha.le
  rw [show a * (n * p / a) = n * p by field_simp] at this
  linarith

theorem final_bound (c B S R : ℝ) (hc : 0 < c) (hB : 0 < B)
    (h : Real.exp (B / (2 * c) * S) ≤ R) : S ≤ c * (2 * Real.log R) / B := by
  have h1 : B / (2 * c) * S ≤ Real.log R := by
    rw [← Real.log_exp (B / (2 * c) * S)]; exact Real.log_le_log (Real.exp_pos _) h
  rw [le_div_iff₀ hB]
  have e : S * B = 2 * c * (B / (2 * c) * S) := by
    field_simp
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left h1 (by linarith : (0:ℝ) ≤ 2 * c)]

section
variable {I : Type*} [Fintype I] {m : ℕ}

theorem sum_update_mul (F : Finset (Fin m)) (a y : Fin m → ℝ) (j : Fin m) (t : ℝ)
    (hj : j ∈ F) :
    ∑ k ∈ F, a k * Function.update y j t k = ∑ k ∈ F, a k * y k + a j * (t - y j) := by
  have h : ∀ k, a k * Function.update y j t k
      = a k * y k + (if k = j then a j * (t - y j) else 0) := by
    intro k
    rw [Function.update_apply]
    split_ifs with hk
    · subst hk; ring
    · ring
  rw [Finset.sum_congr rfl (fun k _ => h k), Finset.sum_add_distrib]
  simp [hj]

theorem a_le_prefixMax (inst : GeneralInstance I (Fin m)) (i : I) (j k : Fin m) (hk : k ≤ j) :
    inst.a i k ≤ prefixMax inst i j :=
  Finset.le_sup' (inst.a i) (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩)

theorem prefixMax_nonneg (inst : GeneralInstance I (Fin m)) (i : I) (j : Fin m) :
    0 ≤ prefixMax inst i j :=
  (inst.ha_nonneg i j).trans (a_le_prefixMax inst i j j le_rfl)

theorem prefixMax_le_aMax [NeZero m] (inst : GeneralInstance I (Fin m)) (i : I) (j : Fin m) :
    prefixMax inst i j ≤ aMax inst i := by
  unfold prefixMax aMax
  exact Finset.sup'_mono _ (Finset.subset_univ _) _

theorem aMax_nonneg [NeZero m] (inst : GeneralInstance I (Fin m)) (i : I) : 0 ≤ aMax inst i :=
  (prefixMax_nonneg inst i ⟨0, NeZero.pos m⟩).trans (prefixMax_le_aMax inst i _)

theorem aMin_spec (inst : GeneralInstance I (Fin m)) (i : I) (j : Fin m) (h : inst.a i j ≠ 0) :
    aMin inst i ≤ inst.a i j ∧ 0 < aMin inst i := by
  unfold aMin
  have hmem : inst.a i j ∈ (Finset.univ.filter (fun k => inst.a i k ≠ 0)).image (inst.a i) :=
    Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, rfl⟩
  have hne : ((Finset.univ.filter (fun k => inst.a i k ≠ 0)).image (inst.a i)).Nonempty :=
    ⟨_, hmem⟩
  rw [dif_pos hne]
  refine ⟨Finset.min'_le _ _ hmem, ?_⟩
  obtain ⟨k, hk, hkv⟩ := Finset.mem_image.mp (Finset.min'_mem _ hne)
  rw [← hkv]
  have := (Finset.mem_filter.mp hk).2
  exact lt_of_le_of_ne (inst.ha_nonneg i k) (Ne.symm this)

theorem aMin_nonneg (inst : GeneralInstance I (Fin m)) (i : I) : 0 ≤ aMin inst i := by
  by_cases h : ∃ j, inst.a i j ≠ 0
  · obtain ⟨j, hj⟩ := h
    exact (aMin_spec inst i j hj).2.le
  · push Not at h
    unfold aMin
    rw [dif_neg]
    rintro ⟨v, hv⟩
    obtain ⟨k, hk, _⟩ := Finset.mem_image.mp hv
    exact (Finset.mem_filter.mp hk).2 (h k)

theorem inc_mono [Nonempty I] (inst : GeneralInstance I (Fin m)) (B : ℝ) (hB : 0 < B)
    (y : Fin m → ℝ) (hy : ∀ k, 0 ≤ y k) (j0 j1 : Fin m) (hz : ∀ k, j0 < k → y k = 0)
    (h01 : j0 ≤ j1) (i : I) :
    increment inst B y j1 i ≤ increment inst B y j0 i := by
  unfold increment
  have hsub : Finset.univ.filter (fun k : Fin m => k ≤ j0) ⊆
      Finset.univ.filter (fun k : Fin m => k ≤ j1) := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact hk.trans h01
  have hS : ∑ k ∈ Finset.univ.filter (fun k : Fin m => k ≤ j1), inst.a i k * y k
      = ∑ k ∈ Finset.univ.filter (fun k : Fin m => k ≤ j0), inst.a i k * y k := by
    symm
    apply Finset.sum_subset hsub
    intro k _ hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hk
    simp [hz k hk]
  rw [hS]
  have hSnn : 0 ≤ ∑ k ∈ Finset.univ.filter (fun k : Fin m => k ≤ j0), inst.a i k * y k :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (inst.ha_nonneg i k) (hy k))
  have hc := inst.hc_pos i
  have hE : 0 ≤ Real.exp (B / (2 * inst.c i) *
      ∑ k ∈ Finset.univ.filter (fun k : Fin m => k ≤ j0), inst.a i k * y k) - 1 := by
    have : 0 ≤ B / (2 * inst.c i) *
        ∑ k ∈ Finset.univ.filter (fun k : Fin m => k ≤ j0), inst.a i k * y k :=
      mul_nonneg (div_nonneg hB.le (by linarith)) hSnn
    linarith [Real.add_one_le_exp (B / (2 * inst.c i) *
      ∑ k ∈ Finset.univ.filter (fun k : Fin m => k ≤ j0), inst.a i k * y k)]
  have hn : (0:ℝ) < Fintype.card I := Nat.cast_pos.mpr Fintype.card_pos
  have hp0 := prefixMax_nonneg inst i j0
  have hp01 : prefixMax inst i j0 ≤ prefixMax inst i j1 := by
    unfold prefixMax; exact Finset.sup'_mono _ hsub _
  rcases hp0.lt_or_eq with hp | hp
  · apply mul_le_mul_of_nonneg_right _ hE
    exact one_div_le_one_div_of_le (mul_pos hn hp) (mul_le_mul_of_nonneg_left hp01 hn.le)
  · have hS0 : ∑ k ∈ Finset.univ.filter (fun k : Fin m => k ≤ j0), inst.a i k * y k = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have hk' : k ≤ j0 := (Finset.mem_filter.mp hk).2
      have h1 := a_le_prefixMax inst i j0 k hk'
      rw [← hp] at h1
      have : inst.a i k = 0 := le_antisymm h1 (inst.ha_nonneg i k)
      simp [this]
    rw [hS0]; simp

/-- the left side of the new covering constraint in round `j` at dual value `t` -/
noncomputable def gfun (inst : GeneralInstance I (Fin m)) (B : ℝ) (s : State I m) (j : Fin m)
    (t : ℝ) : ℝ := ∑ i, inst.a i j * primalAt inst B s j t i

theorem roundValue_eq (inst : GeneralInstance I (Fin m)) (B : ℝ) (s : State I m) (j : Fin m) :
    roundValue inst B s j = sInf {t : ℝ | 0 ≤ t ∧ 1 ≤ gfun inst B s j t} := rfl

theorem gfun_cont (inst : GeneralInstance I (Fin m)) (B : ℝ) (s : State I m) (j : Fin m) :
    Continuous (gfun inst B s j) := by
  have hu : ∀ k, Continuous fun t : ℝ => Function.update s.y j t k := by
    intro k
    by_cases h : k = j
    · subst h; simp only [Function.update_self]; exact continuous_id
    · simp only [Function.update_of_ne h]; exact continuous_const
  unfold gfun primalAt increment
  fun_prop

theorem set_nonempty [Nonempty I] (inst : GeneralInstance I (Fin m)) (B : ℝ) (hB : 0 < B)
    (s : State I m) (j : Fin m) (hx : ∀ i, 0 ≤ s.x i) (hy : ∀ k, 0 ≤ s.y k)
    (hcolj : ∃ i, 0 < inst.a i j) : ∃ t, 0 ≤ t ∧ 1 ≤ gfun inst B s j t := by
  obtain ⟨i0, ha⟩ := hcolj
  have hn : (0:ℝ) < Fintype.card I := Nat.cast_pos.mpr Fintype.card_pos
  have hp : 0 < prefixMax inst i0 j := ha.trans_le (a_le_prefixMax inst i0 j j le_rfl)
  have hc := inst.hc_pos i0
  have hβ : 0 < B / (2 * inst.c i0) := div_pos hB (by linarith)
  have ht : 0 ≤ (Fintype.card I : ℝ) * prefixMax inst i0 j / (B / (2 * inst.c i0) * inst.a i0 j ^ 2) :=
    div_nonneg (mul_nonneg hn.le hp.le) (mul_nonneg hβ.le (sq_nonneg _))
  refine ⟨_, ht, ?_⟩
  set t := (Fintype.card I : ℝ) * prefixMax inst i0 j / (B / (2 * inst.c i0) * inst.a i0 j ^ 2)
    with htdef
  have hjF : j ∈ Finset.univ.filter (fun k : Fin m => k ≤ j) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl⟩
  have hun : ∀ k, 0 ≤ Function.update s.y j t k := by
    intro k; rw [Function.update_apply]; split_ifs
    · exact ht
    · exact hy k
  have hS : inst.a i0 j * t ≤
      ∑ k ∈ Finset.univ.filter (fun k : Fin m => k ≤ j), inst.a i0 k * Function.update s.y j t k := by
    have := Finset.single_le_sum (f := fun k => inst.a i0 k * Function.update s.y j t k)
      (fun k _ => mul_nonneg (inst.ha_nonneg i0 k) (hun k)) hjF
    simpa using this
  calc (1:ℝ) ≤ inst.a i0 j * increment inst B (Function.update s.y j t) j i0 := by
        unfold increment
        exact alg2 _ _ _ _ _ ha hp hn hβ hS
    _ ≤ inst.a i0 j * primalAt inst B s j t i0 :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) ha.le
    _ ≤ gfun inst B s j t :=
        Finset.single_le_sum (f := fun i => inst.a i j * primalAt inst B s j t i)
          (fun i _ => mul_nonneg (inst.ha_nonneg i j) ((hx i).trans (le_max_left _ _)))
          (Finset.mem_univ i0)

theorem T_mem [Nonempty I] (inst : GeneralInstance I (Fin m)) (B : ℝ) (hB : 0 < B)
    (s : State I m) (j : Fin m) (hx : ∀ i, 0 ≤ s.x i) (hy : ∀ k, 0 ≤ s.y k)
    (hcolj : ∃ i, 0 < inst.a i j) :
    0 ≤ roundValue inst B s j ∧ 1 ≤ gfun inst B s j (roundValue inst B s j) := by
  have hne := set_nonempty inst B hB s j hx hy hcolj
  have hcl : IsClosed {t : ℝ | 0 ≤ t ∧ 1 ≤ gfun inst B s j t} :=
    (isClosed_le continuous_const continuous_id).inter
      (isClosed_le continuous_const (gfun_cont inst B s j))
  exact hcl.csInf_mem hne ⟨0, fun t ht => ht.1⟩

theorem below_T (inst : GeneralInstance I (Fin m)) (B : ℝ) (s : State I m) (j : Fin m)
    (t : ℝ) (ht : 0 ≤ t) (htT : t < roundValue inst B s j) : gfun inst B s j t < 1 := by
  by_contra h
  push Not at h
  exact notMem_of_lt_csInf htT ⟨0, fun t ht => ht.1⟩ ⟨ht, h⟩

theorem gT_le (inst : GeneralInstance I (Fin m)) (B : ℝ) (s : State I m) (j : Fin m)
    (hT : 0 < roundValue inst B s j) : gfun inst B s j (roundValue inst B s j) ≤ 1 := by
  have hlim : Filter.Tendsto (gfun inst B s j) (nhdsWithin (roundValue inst B s j)
      (Set.Iio (roundValue inst B s j))) (nhds (gfun inst B s j (roundValue inst B s j))) :=
    ((gfun_cont inst B s j).tendsto _).mono_left nhdsWithin_le_nhds
  apply le_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsLT hT] with t ht
  exact (below_T inst B s j t ht.1.le ht.2).le

theorem step_i [Nonempty I] (inst : GeneralInstance I (Fin m)) (B : ℝ) (hB : 0 < B)
    (s : State I m) (j : Fin m) (T : ℝ) (hT : 0 ≤ T) (hyj : s.y j = 0)
    (hx : ∀ i, 0 ≤ s.x i) (i : I) (hinv : increment inst B s.y j i ≤ s.x i) :
    inst.c i * (primalAt inst B s j T i - s.x i) ≤
      T * (B / 2) * (inst.a i j * (primalAt inst B s j T i +
        1 / ((Fintype.card I : ℝ) * prefixMax inst i j))) := by
  have hc := inst.hc_pos i
  have ha := inst.ha_nonneg i j
  have hn : (0:ℝ) < Fintype.card I := Nat.cast_pos.mpr Fintype.card_pos
  have hp0 := prefixMax_nonneg inst i j
  have hP : 0 ≤ 1 / ((Fintype.card I : ℝ) * prefixMax inst i j) :=
    div_nonneg zero_le_one (mul_nonneg hn.le hp0)
  have hx' : s.x i ≤ primalAt inst B s j T i := le_max_left _ _
  have hRHS : 0 ≤ T * (B / 2) * (inst.a i j * (primalAt inst B s j T i +
        1 / ((Fintype.card I : ℝ) * prefixMax inst i j))) :=
    mul_nonneg (mul_nonneg hT (by linarith)) (mul_nonneg ha (add_nonneg ((hx i).trans hx') hP))
  by_cases hcase : increment inst B (Function.update s.y j T) j i ≤ s.x i
  · have he : primalAt inst B s j T i = s.x i := max_eq_left hcase
    calc inst.c i * (primalAt inst B s j T i - s.x i) = 0 := by rw [he]; ring
      _ ≤ _ := hRHS
  · push Not at hcase
    have hxe : primalAt inst B s j T i = increment inst B (Function.update s.y j T) j i :=
      max_eq_right hcase.le
    rcases hp0.lt_or_eq with hp | hp
    · have hjF : j ∈ Finset.univ.filter (fun k : Fin m => k ≤ j) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl⟩
      have hST : ∑ k ∈ Finset.univ.filter (fun k : Fin m => k ≤ j),
          inst.a i k * Function.update s.y j T k =
          ∑ k ∈ Finset.univ.filter (fun k : Fin m => k ≤ j), inst.a i k * s.y k
            + inst.a i j * T := by
        rw [sum_update_mul _ _ _ _ _ hjF, hyj, sub_zero]
      have hincT : increment inst B (Function.update s.y j T) j i =
          1 / ((Fintype.card I : ℝ) * prefixMax inst i j) *
            (Real.exp (B / (2 * inst.c i) *
              (∑ k ∈ Finset.univ.filter (fun k : Fin m => k ≤ j), inst.a i k * s.y k
                + inst.a i j * T)) - 1) := by
        unfold increment; rw [hST]
      rw [hxe, hincT]
      exact alg (inst.c i) B _ _ _ (inst.a i j) T (s.x i) hc rfl hP hinv
    · exfalso
      have : increment inst B (Function.update s.y j T) j i = 0 := by
        unfold increment; rw [← hp]; simp
      linarith [hx i]

theorem sumQ [Nonempty I] (inst : GeneralInstance I (Fin m)) (j : Fin m) :
    ∑ i, inst.a i j * (1 / ((Fintype.card I : ℝ) * prefixMax inst i j)) ≤ 1 := by
  have hn : (0:ℝ) < Fintype.card I := Nat.cast_pos.mpr Fintype.card_pos
  calc ∑ i, inst.a i j * (1 / ((Fintype.card I : ℝ) * prefixMax inst i j))
      ≤ ∑ _i : I, 1 / (Fintype.card I : ℝ) := by
        apply Finset.sum_le_sum; intro i _
        have ha := inst.ha_nonneg i j
        have hle := a_le_prefixMax inst i j j le_rfl
        rcases (prefixMax_nonneg inst i j).lt_or_eq with hp | hp
        · rw [mul_one_div, div_le_div_iff₀ (mul_pos hn hp) hn]; nlinarith
        · rw [← hp, mul_zero, div_zero, mul_zero]; exact (one_div_pos.mpr hn).le
    _ = 1 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; exact mul_one_div_cancel hn.ne'

theorem xstep [Nonempty I] (inst : GeneralInstance I (Fin m)) (B : ℝ) (hB : 0 < B)
    (s : State I m) (j : Fin m) (T : ℝ) (hT0 : 0 ≤ T) (hg : 0 < T → gfun inst B s j T ≤ 1)
    (hyj : s.y j = 0) (hx : ∀ i, 0 ≤ s.x i)
    (hinv : ∀ i, increment inst B s.y j i ≤ s.x i) :
    ∑ i, inst.c i * primalAt inst B s j T i ≤ ∑ i, inst.c i * s.x i + B * T := by
  have hsum : ∑ i, inst.c i * (primalAt inst B s j T i - s.x i) ≤
      T * (B / 2) * (gfun inst B s j T +
        ∑ i, inst.a i j * (1 / ((Fintype.card I : ℝ) * prefixMax inst i j))) := by
    calc _ ≤ ∑ i, T * (B / 2) * (inst.a i j * (primalAt inst B s j T i +
            1 / ((Fintype.card I : ℝ) * prefixMax inst i j))) :=
          Finset.sum_le_sum (fun i _ => step_i inst B hB s j T hT0 hyj hx i (hinv i))
      _ = _ := by
          rw [← Finset.mul_sum]; congr 1; unfold gfun; rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro i _; ring
  have hQ := sumQ inst j
  have hbound : T * (B / 2) * (gfun inst B s j T +
      ∑ i, inst.a i j * (1 / ((Fintype.card I : ℝ) * prefixMax inst i j))) ≤ B * T := by
    rcases hT0.lt_or_eq with hTpos | hTz
    · have h2 : gfun inst B s j T +
          ∑ i, inst.a i j * (1 / ((Fintype.card I : ℝ) * prefixMax inst i j)) ≤ 2 := by
        linarith [hg hTpos]
      calc _ ≤ T * (B / 2) * 2 := mul_le_mul_of_nonneg_left h2 (mul_nonneg hT0 (by linarith))
        _ = B * T := by ring
    · rw [← hTz]; simp
  have he : ∑ i, inst.c i * (primalAt inst B s j T i - s.x i) =
      ∑ i, inst.c i * primalAt inst B s j T i - ∑ i, inst.c i * s.x i := by
    rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro i _; ring
  linarith

theorem vstep [Nonempty I] [NeZero m] (inst : GeneralInstance I (Fin m)) (B : ℝ) (hB : 0 < B)
    (s : State I m) (j : Fin m) (T : ℝ) (hT : 0 < T) (hg : gfun inst B s j T ≤ 1)
    (hy : ∀ k, 0 ≤ s.y k) (hx : ∀ i, 0 ≤ s.x i) (hz : ∀ k, j < k → s.y k = 0)
    (i : I) (ha : 0 < inst.a i j) :
    Real.exp (B / (2 * inst.c i) * ∑ k, inst.a i k * Function.update s.y j T k) ≤
      1 + (Fintype.card I : ℝ) * aMax inst i / aMin inst i := by
  have hn : (0:ℝ) < Fintype.card I := Nat.cast_pos.mpr Fintype.card_pos
  have hc := inst.hc_pos i
  have hun : ∀ k, 0 ≤ Function.update s.y j T k := by
    intro k; rw [Function.update_apply]; split_ifs
    · exact hT.le
    · exact hy k
  have haI : inst.a i j * increment inst B (Function.update s.y j T) j i ≤ 1 := by
    calc inst.a i j * increment inst B (Function.update s.y j T) j i
        ≤ inst.a i j * primalAt inst B s j T i :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) ha.le
      _ ≤ gfun inst B s j T :=
          Finset.single_le_sum (f := fun i => inst.a i j * primalAt inst B s j T i)
            (fun i _ => mul_nonneg (inst.ha_nonneg i j) ((hx i).trans (le_max_left _ _)))
            (Finset.mem_univ i)
      _ ≤ 1 := hg
  have hfull : ∑ k, inst.a i k * Function.update s.y j T k =
      ∑ k ∈ Finset.univ.filter (fun k : Fin m => k ≤ j),
        inst.a i k * Function.update s.y j T k := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k _ hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hk
    rw [Function.update_of_ne (ne_of_gt hk), hz k hk, mul_zero]
  have hSnn : 0 ≤ ∑ k ∈ Finset.univ.filter (fun k : Fin m => k ≤ j),
        inst.a i k * Function.update s.y j T k :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (inst.ha_nonneg i k) (hun k))
  have hp : 0 < prefixMax inst i j := ha.trans_le (a_le_prefixMax inst i j j le_rfl)
  have hpmax := prefixMax_le_aMax inst i j
  obtain ⟨hminle, hminpos⟩ := aMin_spec inst i j ha.ne'
  unfold increment at haI
  rw [hfull]
  have hE1 : 1 ≤ Real.exp (B / (2 * inst.c i) * ∑ k ∈ Finset.univ.filter (fun k : Fin m => k ≤ j),
        inst.a i k * Function.update s.y j T k) :=
    Real.one_le_exp (mul_nonneg (div_nonneg hB.le (by linarith)) hSnn)
  revert haI hE1
  generalize Real.exp (B / (2 * inst.c i) * ∑ k ∈ Finset.univ.filter (fun k : Fin m => k ≤ j),
        inst.a i k * Function.update s.y j T k) = E
  intro haI hE1
  rw [show inst.a i j * (1 / ((Fintype.card I : ℝ) * prefixMax inst i j) * (E - 1)) =
      inst.a i j * (E - 1) / ((Fintype.card I : ℝ) * prefixMax inst i j) by ring,
    div_le_one (mul_pos hn hp)] at haI
  rw [← sub_le_iff_le_add', le_div_iff₀ hminpos]
  nlinarith [mul_nonneg (sub_nonneg.mpr hE1) (sub_nonneg.mpr hminle),
    mul_nonneg hn.le (sub_nonneg.mpr hpmax)]

/-- the invariants of the scheme after `r` rounds -/
structure Good [NeZero m] (inst : GeneralInstance I (Fin m)) (B : ℝ) (r : ℕ) (s : State I m) :
    Prop where
  ynn : ∀ k, 0 ≤ s.y k
  yz : ∀ k : Fin m, r ≤ (k : ℕ) → s.y k = 0
  xnn : ∀ i, 0 ≤ s.x i
  inv : ∀ i, ∀ j : Fin m, r ≤ (j : ℕ) → increment inst B s.y j i ≤ s.x i
  cov : ∀ k : Fin m, (k : ℕ) < r → 1 ≤ ∑ i, inst.a i k * s.x i
  comp : ∑ i, inst.c i * s.x i ≤ B * ∑ k, s.y k
  viol : ∀ i, Real.exp (B / (2 * inst.c i) * ∑ k, inst.a i k * s.y k) ≤
    1 + (Fintype.card I : ℝ) * aMax inst i / aMin inst i

theorem good_zero [NeZero m] (inst : GeneralInstance I (Fin m)) (B : ℝ) (hB : 0 < B) :
    Good inst B 0 (initState I m) where
  ynn := fun _ => le_rfl
  yz := fun _ _ => rfl
  xnn := fun _ => le_rfl
  inv := by intro i j _; simp [increment, initState]
  cov := fun k hk => absurd hk (Nat.not_lt_zero _)
  comp := by simp [initState]
  viol := by
    intro i
    simp only [initState, mul_zero, Finset.sum_const_zero, Real.exp_zero]
    exact le_add_of_nonneg_right
      (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (aMax_nonneg inst i)) (aMin_nonneg inst i))

theorem good_step [Nonempty I] [NeZero m] (inst : GeneralInstance I (Fin m)) (B : ℝ)
    (hB : 0 < B) (hcol : ∀ j : Fin m, ∃ i, 0 < inst.a i j) (j : Fin m) (s : State I m)
    (hs : Good inst B j s) : Good inst B ((j : ℕ) + 1) (runRound inst B s j) := by
  have hyj : s.y j = 0 := hs.yz j le_rfl
  have hz : ∀ k, j < k → s.y k = 0 := fun k hk => hs.yz k (Fin.le_iff_val_le_val.mp hk.le)
  have hinv0 : ∀ i, increment inst B s.y j i ≤ s.x i := fun i => hs.inv i j le_rfl
  unfold runRound
  split_ifs with hskip
  · have hupd : Function.update s.y j 0 = s.y := by
      funext k
      by_cases hk : k = j
      · subst hk; rw [Function.update_self, hyj]
      · rw [Function.update_of_ne hk]
    rw [hupd]
    exact
      { ynn := hs.ynn
        yz := fun k hk => hs.yz k (by omega)
        xnn := hs.xnn
        inv := fun i j1 hj1 =>
          (inc_mono inst B hB s.y hs.ynn j j1 hz (Fin.le_iff_val_le_val.mpr (by omega)) i).trans
            (hinv0 i)
        cov := by
          intro k hk
          rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
          · exact hs.cov k hk
          · have : k = j := Fin.ext hk
            subst this; exact hskip
        comp := hs.comp
        viol := hs.viol }
  · obtain ⟨hT0, hTg⟩ := T_mem inst B hB s j hs.xnn hs.ynn (hcol j)
    have hg := gT_le inst B s j
    have hun : ∀ k, 0 ≤ Function.update s.y j (roundValue inst B s j) k := by
      intro k; rw [Function.update_apply]; split_ifs
      · exact hT0
      · exact hs.ynn k
    have hz' : ∀ k, j < k → Function.update s.y j (roundValue inst B s j) k = 0 := by
      intro k hk; rw [Function.update_of_ne (ne_of_gt hk), hz k hk]
    have hsumy : ∑ k, Function.update s.y j (roundValue inst B s j) k =
        ∑ k, s.y k + roundValue inst B s j := by
      have := sum_update_mul Finset.univ (fun _ => (1:ℝ)) s.y j (roundValue inst B s j)
        (Finset.mem_univ _)
      simp only [one_mul] at this
      rw [this, hyj, sub_zero]
    have hX := xstep inst B hB s j (roundValue inst B s j) hT0 hg hyj hs.xnn hinv0
    exact
      { ynn := hun
        yz := by
          intro k hk
          exact hz' k (Fin.lt_def.mpr (by omega))
        xnn := fun i => (hs.xnn i).trans (le_max_left _ _)
        inv := fun i j1 hj1 =>
          (inc_mono inst B hB _ hun j j1 hz' (Fin.le_iff_val_le_val.mpr (by omega)) i).trans
            (le_max_right _ _)
        cov := by
          intro k hk
          rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
          · refine (hs.cov k hk).trans (Finset.sum_le_sum fun i _ => ?_)
            exact mul_le_mul_of_nonneg_left (le_max_left _ _) (inst.ha_nonneg i k)
          · have : k = j := Fin.ext hk
            subst this; exact hTg
        comp := by
          show ∑ i, inst.c i * primalAt inst B s j (roundValue inst B s j) i ≤
            B * ∑ k, Function.update s.y j (roundValue inst B s j) k
          rw [hsumy]; nlinarith [hs.comp]
        viol := by
          intro i
          show Real.exp (B / (2 * inst.c i) *
              ∑ k, inst.a i k * Function.update s.y j (roundValue inst B s j) k) ≤ _
          have hS := sum_update_mul Finset.univ (inst.a i) s.y j (roundValue inst B s j)
            (Finset.mem_univ _)
          rw [hyj, sub_zero] at hS
          rcases (inst.ha_nonneg i j).lt_or_eq with ha | ha
          · rcases hT0.lt_or_eq with hT | hT
            · exact vstep inst B hB s j _ hT (hg hT) hs.ynn hs.xnn hz i ha
            · rw [hS, ← hT, mul_zero, add_zero]; exact hs.viol i
          · rw [hS, ← ha, zero_mul, add_zero]; exact hs.viol i }

theorem good_all [Nonempty I] [NeZero m] (inst : GeneralInstance I (Fin m)) (B : ℝ)
    (hB : 0 < B) (hcol : ∀ j : Fin m, ∃ i, 0 < inst.a i j) :
    ∀ r, r ≤ m → Good inst B r (stateAfter inst B r) := by
  intro r
  induction r with
  | zero => intro _; exact good_zero inst B hB
  | succ r ih =>
    intro hr
    have h : r < m := by omega
    have e : stateAfter inst B (r + 1) = runRound inst B (stateAfter inst B r) ⟨r, h⟩ := by
      simp only [stateAfter, dif_pos h]
    rw [e]
    exact good_step inst B hB hcol ⟨r, h⟩ _ (ih (by omega))

end

end BNCovPackPf

open BNCovPack.Packing OnlinePrimalDual.GeneralPacking in
theorem solution {I : Type*} [Fintype I] [Nonempty I] {m : ℕ} [NeZero m]
    (inst : GeneralInstance I (Fin m)) (B : ℝ) (hB : 0 < B)
    (hcol : ∀ j : Fin m, ∃ i, 0 < inst.a i j) :
    (∀ r : ℕ, r ≤ m → ∀ k : Fin m, 0 ≤ (stateAfter inst B r).y k) ∧
    (∀ r : ℕ, r ≤ m → ∀ y' : Fin m → ℝ, (∀ k, 0 ≤ y' k) →
      (∀ i, ∑ k ∈ Finset.univ.filter (fun k : Fin m => (k : ℕ) < r), inst.a i k * y' k
        ≤ inst.c i) →
      ∑ k ∈ Finset.univ.filter (fun k : Fin m => (k : ℕ) < r), y' k ≤ B * dualValue inst B r) ∧
    (∀ i : I, ∑ k : Fin m, inst.a i k * (stateAfter inst B m).y k ≤
      inst.c i * (2 * Real.log (1 + (Fintype.card I : ℝ) * aMax inst i / aMin inst i)) / B) := by
  have hg := BNCovPackPf.good_all inst B hB hcol
  refine ⟨fun r hr k => (hg r hr).ynn k, ?_, ?_⟩
  · intro r hr y' hy' hfeas
    have G := hg r hr
    have hdual : dualValue inst B r = ∑ k, (stateAfter inst B r).y k := by
      unfold dualValue
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro k _ hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hk
      exact G.yz k hk
    rw [hdual]
    refine le_trans ?_ G.comp
    calc ∑ k ∈ Finset.univ.filter (fun k : Fin m => (k : ℕ) < r), y' k
        ≤ ∑ k ∈ Finset.univ.filter (fun k : Fin m => (k : ℕ) < r),
            y' k * ∑ i, inst.a i k * (stateAfter inst B r).x i := by
          apply Finset.sum_le_sum; intro k hk
          exact le_mul_of_one_le_right (hy' k) (G.cov k (Finset.mem_filter.mp hk).2)
      _ = ∑ i, (stateAfter inst B r).x i *
            ∑ k ∈ Finset.univ.filter (fun k : Fin m => (k : ℕ) < r), inst.a i k * y' k := by
          simp only [Finset.mul_sum]; rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro k _; ring
      _ ≤ ∑ i, (stateAfter inst B r).x i * inst.c i := by
          apply Finset.sum_le_sum; intro i _
          exact mul_le_mul_of_nonneg_left (hfeas i) (G.xnn i)
      _ = ∑ i, inst.c i * (stateAfter inst B r).x i := by
          apply Finset.sum_congr rfl; intro i _; ring
  · intro i
    exact BNCovPackPf.final_bound _ _ _ _ (inst.hc_pos i) hB ((hg m le_rfl).viol i)
