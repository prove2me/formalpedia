-- Prove2me | solution 1 for CurvatureSubmod.CSSP.condNum_sq_ge
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:16:36.620294+00:00
-- url     : https://prove2.me/submissions/db9b14d8-d70e-4fc7-b12c-ac9e53c22f4f

import Mathlib
import Definitions.Def_CurvatureSubmod_CSSP_Setting
set_option autoImplicit false
open CurvatureSubmod.CSSP

theorem pyth {m : ℕ} (K : Submodule ℝ (EuclideanSpace ℝ (Fin m))) (v : EuclideanSpace ℝ (Fin m)) :
    ‖v - K.starProjection v‖ ^ 2 = ‖v‖ ^ 2 - ‖K.starProjection v‖ ^ 2 := by
  have h1 : K.starProjection v ∈ K := Submodule.starProjection_apply_mem K v
  have h2 : v - K.starProjection v ∈ Kᗮ := Submodule.sub_starProjection_mem_orthogonal v
  have h3 : inner ℝ (K.starProjection v) (v - K.starProjection v) = 0 :=
    Submodule.inner_right_of_mem_orthogonal h1 h2
  have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (K.starProjection v)
    (v - K.starProjection v) h3
  rw [add_sub_cancel] at this
  rw [sq, sq, sq]
  linarith

theorem sol_fA_eq_sum_sub {m n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin m)) (S : Finset (Fin n)) :
    fA c S = ∑ i, (‖c i‖ ^ 2 - ‖proj c S (c i)‖ ^ 2) := by
  unfold fA
  exact Finset.sum_congr rfl fun i _ => pyth (colSpan c S) (c i)

theorem norm_proj_mono {m : ℕ} {K L : Submodule ℝ (EuclideanSpace ℝ (Fin m))} (h : K ≤ L)
    (v : EuclideanSpace ℝ (Fin m)) :
    ‖K.starProjection v‖ ≤ ‖L.starProjection v‖ := by
  have := Submodule.starProjection_comp_starProjection_of_le h
  have h2 : K.starProjection (L.starProjection v) = K.starProjection v := by
    simpa using congrArg (fun T => T v) this
  calc ‖K.starProjection v‖ = ‖K.starProjection (L.starProjection v)‖ := by rw [h2]
    _ ≤ _ := Submodule.norm_starProjection_apply_le _ _

theorem colSpan_mono {m n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin m)) {A B : Finset (Fin n)}
    (h : A ⊆ B) : colSpan c A ≤ colSpan c B :=
  Submodule.span_mono (Set.image_mono (by exact_mod_cast h))

theorem proj_sq_mono {m n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin m)) {A B : Finset (Fin n)}
    (h : A ⊆ B) (v : EuclideanSpace ℝ (Fin m)) :
    ‖proj c A v‖ ^ 2 ≤ ‖proj c B v‖ ^ 2 := by
  have := norm_proj_mono (colSpan_mono c h) v
  exact pow_le_pow_left₀ (norm_nonneg _) this 2

theorem sol_fA_monoDec {m n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin m)) :
    MonoDec (fA c) := by
  intro A i
  unfold marg
  rw [sol_fA_eq_sum_sub c (insert i A), sol_fA_eq_sum_sub c A, ← Finset.sum_sub_distrib]
  refine Finset.sum_nonpos fun j _ => ?_
  have := proj_sq_mono c (Finset.subset_insert i A) (c j)
  linarith

theorem proj_empty {m n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin m)) (x : EuclideanSpace ℝ (Fin m)) :
    proj c ∅ x = 0 := by
  unfold proj colSpan
  simp

theorem proj_self_of_mem {m n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin m)) {S : Finset (Fin n)}
    {j : Fin n} (hj : j ∈ S) : proj c S (c j) = c j := by
  unfold proj
  rw [Submodule.starProjection_eq_self_iff]
  exact Submodule.subset_span ⟨j, hj, rfl⟩

theorem sol_abs_marg_empty {m n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin m)) (i : Fin n) :
    |marg (fA c) ∅ i| = ∑ j, ‖proj c {i} (c j)‖ ^ 2 := by
  unfold marg
  rw [Finset.insert_empty, sol_fA_eq_sum_sub c {i}, sol_fA_eq_sum_sub c ∅, ← Finset.sum_sub_distrib]
  have : ∀ j, ‖c j‖ ^ 2 - ‖proj c {i} (c j)‖ ^ 2 - (‖c j‖ ^ 2 - ‖proj c ∅ (c j)‖ ^ 2) =
      -‖proj c {i} (c j)‖ ^ 2 := by
    intro j
    rw [proj_empty]
    simp
  simp_rw [this]
  rw [Finset.sum_neg_distrib, abs_neg]
  exact abs_of_nonneg (Finset.sum_nonneg fun j _ => sq_nonneg _)

theorem sol_abs_marg_top {m n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin m)) (i : Fin n) :
    |marg (fA c) (Finset.univ.erase i) i| =
      ‖c i - proj c (Finset.univ.erase i) (c i)‖ ^ 2 := by
  unfold marg
  rw [Finset.insert_erase (Finset.mem_univ i)]
  have h1 : fA c Finset.univ = 0 := by
    unfold fA
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [proj_self_of_mem c (Finset.mem_univ j)]
    simp
  have h2 : fA c (Finset.univ.erase i) = ‖c i - proj c (Finset.univ.erase i) (c i)‖ ^ 2 := by
    unfold fA
    refine Finset.sum_eq_single i (fun j _ hj => ?_) (fun h => absurd (Finset.mem_univ i) h)
    rw [proj_self_of_mem c (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)]
    simp
  rw [h1, h2, zero_sub, abs_neg]
  exact abs_of_nonneg (sq_nonneg _)

theorem exists_coeff {m n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin m)) (S : Finset (Fin n))
    (y : EuclideanSpace ℝ (Fin m)) (hy : y ∈ colSpan c S) :
    ∃ a : Fin n → ℝ, (∀ j, j ∉ S → a j = 0) ∧ ∑ j, a j • c j = y := by
  unfold colSpan at hy
  rw [Finsupp.mem_span_image_iff_linearCombination ℝ] at hy
  obtain ⟨l, hl, hly⟩ := hy
  refine ⟨fun j => l j, ?_, ?_⟩
  · intro j hj
    exact (Finsupp.mem_supported' ℝ l).1 hl j (by simpa using hj)
  · rw [← hly, Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)]

theorem applyA_smul {m n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin m)) (r : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : applyA c (r • x) = r • applyA c x := by
  simp [applyA, Finset.smul_sum, smul_smul]

theorem sol_exists_unit_small {m n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin m)) (i : Fin n) :
    ∃ x : EuclideanSpace ℝ (Fin n), ‖x‖ = 1 ∧
      ‖applyA c x‖ ≤ Real.sqrt |marg (fA c) (Finset.univ.erase i) i| := by
  rw [sol_abs_marg_top, Real.sqrt_sq (norm_nonneg _)]
  obtain ⟨a, ha0, hay⟩ := exists_coeff c (Finset.univ.erase i) (proj c (Finset.univ.erase i) (c i))
    (Submodule.starProjection_apply_mem _ _)
  set x0 : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i 1 - WithLp.toLp 2 a with hx0
  have hai : a i = 0 := ha0 i (by simp)
  have hx0i : x0 i = 1 := by simp [hx0, hai]
  have hApp : applyA c x0 = c i - proj c (Finset.univ.erase i) (c i) := by
    rw [← hay]
    simp [applyA, hx0, sub_smul, Finset.sum_sub_distrib, EuclideanSpace.single_apply]
  have hn : 1 ≤ ‖x0‖ := by
    have := PiLp.norm_apply_le x0 i
    rw [hx0i] at this
    simpa using this
  refine ⟨(‖x0‖⁻¹) • x0, ?_, ?_⟩
  · rw [norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (by linarith)
  · rw [applyA_smul, norm_smul, hApp, norm_inv, norm_norm]
    calc ‖x0‖⁻¹ * ‖c i - proj c (Finset.univ.erase i) (c i)‖
        ≤ 1 * ‖c i - proj c (Finset.univ.erase i) (c i)‖ := by
          gcongr
          exact inv_le_one_of_one_le₀ hn
      _ = _ := one_mul _

theorem norm_proj_single_sq {m n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin m)) (i j : Fin n) :
    ‖proj c {i} (c j)‖ ^ 2 = (inner ℝ (c i) (c j)) ^ 2 / ‖c i‖ ^ 2 := by
  have : proj c {i} (c j) = (inner ℝ (c i) (c j) / ((‖c i‖ ^ 2 : ℝ) : ℝ)) • c i := by
    unfold proj colSpan
    simp only [Finset.coe_singleton, Set.image_singleton]
    exact Submodule.starProjection_singleton ℝ (c j)
  rw [this, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, div_pow]
  by_cases h0 : c i = 0
  · simp [h0]
  · have : ‖c i‖ ≠ 0 := norm_ne_zero_iff.mpr h0
    field_simp

theorem sol_exists_unit_large {m n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin m)) (i : Fin n) :
    ∃ x : EuclideanSpace ℝ (Fin n), ‖x‖ = 1 ∧
      Real.sqrt |marg (fA c) ∅ i| ≤ ‖applyA c x‖ := by
  rw [sol_abs_marg_empty]
  simp_rw [norm_proj_single_sq]
  set w : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun j => inner ℝ (c i) (c j)) with hw
  have hw2 : ‖w‖ ^ 2 = ∑ j, (inner ℝ (c i) (c j)) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [hw]
  have hsingle : ‖(EuclideanSpace.single i (1:ℝ) : EuclideanSpace ℝ (Fin n))‖ = 1 := by simp
  by_cases hw0 : ‖w‖ = 0
  · refine ⟨EuclideanSpace.single i 1, hsingle, ?_⟩
    have : ∑ j, (inner ℝ (c i) (c j)) ^ 2 / ‖c i‖ ^ 2 = 0 := by
      rw [← Finset.sum_div, ← hw2, hw0]; simp
    rw [this]; simp
  · have hwpos : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hw0)
    have hc0 : c i ≠ 0 := by
      intro h
      apply hw0
      have : ∑ j, (inner ℝ (c i) (c j)) ^ 2 = 0 := by simp [h]
      rw [← hw2] at this
      exact pow_eq_zero_iff (two_ne_zero) |>.mp this
    have hcpos : 0 < ‖c i‖ := norm_pos_iff.mpr hc0
    refine ⟨(‖w‖⁻¹) • w, ?_, ?_⟩
    · rw [norm_smul, norm_inv, norm_norm]
      exact inv_mul_cancel₀ hw0
    · rw [applyA_smul, norm_smul, norm_inv, norm_norm]
      have hinner : inner ℝ (c i) (applyA c w) = ‖w‖ ^ 2 := by
        rw [hw2]
        simp [applyA, inner_sum, inner_smul_right, hw, sq]
      have hcs : ‖w‖ ^ 2 ≤ ‖c i‖ * ‖applyA c w‖ := by
        rw [← hinner]
        exact real_inner_le_norm _ _
      have hs : ∑ j, (inner ℝ (c i) (c j)) ^ 2 / ‖c i‖ ^ 2 = (‖w‖ / ‖c i‖) ^ 2 := by
        rw [← Finset.sum_div, ← hw2, div_pow]
      rw [hs, Real.sqrt_sq (by positivity)]
      rw [div_le_iff₀ hcpos, inv_mul_eq_div, div_mul_eq_mul_div, le_div_iff₀ hwpos]
      nlinarith

theorem applyA_norm_le {m n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ = 1) : ‖applyA c x‖ ≤ ∑ j, ‖c j‖ := by
  unfold applyA
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_smul]
  have : ‖x j‖ ≤ 1 := by
    have := PiLp.norm_apply_le x j
    rw [hx] at this
    exact this
  calc ‖x j‖ * ‖c j‖ ≤ 1 * ‖c j‖ := by gcongr
    _ = ‖c j‖ := one_mul _

theorem applyA_cont {m n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin m)) :
    Continuous (fun x : EuclideanSpace ℝ (Fin n) => ‖applyA c x‖) := by
  unfold applyA
  fun_prop

theorem exists_lower {m n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin m)) (hc : LinearIndependent ℝ c)
    (hn : Nonempty (Fin n)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ = 1 → δ ≤ ‖applyA c x‖ := by
  have hcomp : IsCompact (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) := isCompact_sphere _ _
  have hne : (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1).Nonempty := by
    obtain ⟨i⟩ := hn
    exact ⟨EuclideanSpace.single i 1, by simp⟩
  obtain ⟨x0, hx0, hmin⟩ := hcomp.exists_isMinOn hne (applyA_cont c).continuousOn
  refine ⟨‖applyA c x0‖, ?_, fun x hx => hmin (by simpa using hx)⟩
  rw [norm_pos_iff]
  intro h0
  have hx0n : ‖x0‖ = 1 := by simpa using hx0
  rw [Fintype.linearIndependent_iff] at hc
  have : ∀ j, x0 j = 0 := fun j => hc (fun j => x0 j) (by simpa [applyA] using h0) j
  have : x0 = 0 := by ext j; exact this j
  rw [this] at hx0n
  simp at hx0n

theorem solution {m n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin m))
    (hc : LinearIndependent ℝ c) (i : Fin n) :
    marg (fA c) ∅ i / marg (fA c) (Finset.univ.erase i) i ≤ condNum c ^ 2 := by
  have hnonpos := sol_fA_monoDec c
  have h1 : marg (fA c) ∅ i = -|marg (fA c) ∅ i| := by rw [abs_of_nonpos (hnonpos _ _), neg_neg]
  have h2 : marg (fA c) (Finset.univ.erase i) i = -|marg (fA c) (Finset.univ.erase i) i| := by
    rw [abs_of_nonpos (hnonpos _ _), neg_neg]
  rw [h1, h2, neg_div_neg_eq, sol_abs_marg_top, sol_abs_marg_empty]
  set S1 := ∑ j, ‖proj c {i} (c j)‖ ^ 2 with hS1
  set S2 := ‖c i - proj c (Finset.univ.erase i) (c i)‖ ^ 2 with hS2
  have hS1' : S1 = |marg (fA c) ∅ i| := (sol_abs_marg_empty c i).symm
  have hS2' : S2 = |marg (fA c) (Finset.univ.erase i) i| := (sol_abs_marg_top c i).symm
  obtain ⟨xl, hxl, hl⟩ := sol_exists_unit_large c i
  obtain ⟨xs, hxs, hs⟩ := sol_exists_unit_small c i
  rw [← hS1'] at hl
  rw [← hS2'] at hs
  haveI : Nonempty (Fin n) := ⟨i⟩
  obtain ⟨δ, hδ, hδle⟩ := exists_lower c hc inferInstance
  have hne : Nonempty {x : EuclideanSpace ℝ (Fin n) // ‖x‖ = 1} := ⟨⟨xl, hxl⟩⟩
  have hbdd : BddAbove (Set.range fun x : {x : EuclideanSpace ℝ (Fin n) // ‖x‖ = 1} =>
      ‖applyA c x.1‖) := ⟨∑ j, ‖c j‖, by rintro _ ⟨x, rfl⟩; exact applyA_norm_le c x.1 x.2⟩
  have hbdd' : BddBelow (Set.range fun x : {x : EuclideanSpace ℝ (Fin n) // ‖x‖ = 1} =>
      ‖applyA c x.1‖) := ⟨0, by rintro _ ⟨x, rfl⟩; exact norm_nonneg _⟩
  have hsup : Real.sqrt S1 ≤ ⨆ x : {x : EuclideanSpace ℝ (Fin n) // ‖x‖ = 1}, ‖applyA c x.1‖ :=
    hl.trans (le_ciSup hbdd ⟨xl, hxl⟩)
  have hinf : (⨅ x : {x : EuclideanSpace ℝ (Fin n) // ‖x‖ = 1}, ‖applyA c x.1‖) ≤ Real.sqrt S2 :=
    (ciInf_le hbdd' ⟨xs, hxs⟩).trans hs
  have hinfpos : δ ≤ ⨅ x : {x : EuclideanSpace ℝ (Fin n) // ‖x‖ = 1}, ‖applyA c x.1‖ :=
    le_ciInf fun x => hδle x.1 x.2
  unfold condNum
  set sup := ⨆ x : {x : EuclideanSpace ℝ (Fin n) // ‖x‖ = 1}, ‖applyA c x.1‖
  set inf := ⨅ x : {x : EuclideanSpace ℝ (Fin n) // ‖x‖ = 1}, ‖applyA c x.1‖
  have hinf0 : 0 < inf := lt_of_lt_of_le hδ hinfpos
  have hS1nn : 0 ≤ S1 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hS2nn : 0 ≤ S2 := sq_nonneg _
  have hsup2 : S1 ≤ sup ^ 2 := by
    calc S1 = Real.sqrt S1 ^ 2 := (Real.sq_sqrt hS1nn).symm
      _ ≤ sup ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsup 2
  have hinf2 : inf ^ 2 ≤ S2 := by
    calc inf ^ 2 ≤ Real.sqrt S2 ^ 2 := pow_le_pow_left₀ hinf0.le hinf 2
      _ = S2 := Real.sq_sqrt hS2nn
  rw [div_pow]
  calc S1 / S2 ≤ S1 / inf ^ 2 := div_le_div_of_nonneg_left hS1nn (by positivity) hinf2
    _ ≤ sup ^ 2 / inf ^ 2 := div_le_div_of_nonneg_right hsup2 (by positivity)

