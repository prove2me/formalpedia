-- Prove2me | solution 1 for CtxInvOpt.PolyCone.lemma10_polyCone_angle
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T07:45:36.412294+00:00
-- url     : https://prove2.me/submissions/bd0cb444-f730-4cd2-b6d0-eca0c0ad3761

import Mathlib
import Definitions.Def_CtxInvOpt_PolyCone_Cones

open CtxInvOpt.PolyCone CtxInvOpt.Offline

namespace PolyConeAux

/-- Pythagorean split of `w + b • δ` along `V` and `Vᗮ`. -/
theorem pyth {d : ℕ} (V : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (w δ : EuclideanSpace ℝ (Fin d)) (hw : w ∈ V) (b : ℝ) :
    ‖w + b • δ‖ ^ 2 = ‖w + b • V.starProjection δ‖ ^ 2
      + b ^ 2 * ‖δ - V.starProjection δ‖ ^ 2 := by
  have hq : V.starProjection δ ∈ V := Submodule.starProjection_apply_mem V δ
  have hr : δ - V.starProjection δ ∈ Vᗮ := Submodule.sub_starProjection_mem_orthogonal δ
  have hx : w + b • V.starProjection δ ∈ V := V.add_mem hw (V.smul_mem b hq)
  have hy : b • (δ - V.starProjection δ) ∈ Vᗮ := Vᗮ.smul_mem b hr
  have hinner : inner ℝ (w + b • V.starProjection δ) (b • (δ - V.starProjection δ)) = 0 :=
    Submodule.inner_right_of_mem_orthogonal hx hy
  have hsplit : w + b • δ = (w + b • V.starProjection δ) + b • (δ - V.starProjection δ) := by
    rw [smul_sub]; abel
  rw [hsplit, norm_add_sq_real, hinner, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

end PolyConeAux

namespace PolyConeAux

/-- Partial sums over the first `k` vectors. -/
noncomputable def S {d p : ℕ} (δ : Fin p → EuclideanSpace ℝ (Fin d)) (β : Fin p → ℝ) (k : ℕ) :
    EuclideanSpace ℝ (Fin d) :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin p => j.val < k), β j • δ j

theorem S_mem {d p : ℕ} (δ : Fin p → EuclideanSpace ℝ (Fin d)) (β : Fin p → ℝ) (k : ℕ) :
    S δ β k ∈ Submodule.span ℝ (δ '' {j | j.val < k}) := by
  unfold S
  refine Submodule.sum_mem _ (fun j hj => Submodule.smul_mem _ _ (Submodule.subset_span ?_))
  exact ⟨j, by simpa using hj, rfl⟩

theorem S_succ {d p : ℕ} (δ : Fin p → EuclideanSpace ℝ (Fin d)) (β : Fin p → ℝ) (k : ℕ)
    (hk : k < p) : S δ β (k + 1) = S δ β k + β ⟨k, hk⟩ • δ ⟨k, hk⟩ := by
  unfold S
  have hset : Finset.univ.filter (fun j : Fin p => j.val < k + 1) =
      insert ⟨k, hk⟩ (Finset.univ.filter (fun j : Fin p => j.val < k)) := by
    ext j; simp [Fin.ext_iff]; omega
  have hnot : (⟨k, hk⟩ : Fin p) ∉ Finset.univ.filter (fun j : Fin p => j.val < k) := by simp
  rw [hset, Finset.sum_insert hnot, add_comm]

theorem S_full {d p : ℕ} (δ : Fin p → EuclideanSpace ℝ (Fin d)) (β : Fin p → ℝ) :
    S δ β p = ∑ j, β j • δ j := by
  unfold S
  congr 1
  ext j; simp

/-- Homogeneous Lemma B-4: every coefficient is controlled by the norm of the combination. -/
theorem coeff_bound {d p : ℕ} (η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1)
    (δ : Fin p → EuclideanSpace ℝ (Fin d)) (hunit : ∀ i, ‖δ i‖ = 1)
    (hsep : ∀ i : Fin p, 0 < i.val →
      η ≤ ‖δ i - (Submodule.span ℝ (δ '' {j | j < i})).starProjection (δ i)‖) :
    ∀ k : ℕ, 1 ≤ k → k ≤ p → ∀ (β : Fin p → ℝ) (i : Fin p), i.val < k →
      |β i| * η ^ (k - 1) ≤ ‖S δ β k‖ := by
  intro k hk1
  induction k, hk1 using Nat.le_induction with
  | base =>
    intro hp β i hi
    have hi0 : i = ⟨0, by omega⟩ := Fin.ext (by simp; omega)
    have h1 : S δ β 1 = β i • δ i := by
      have := S_succ δ β 0 (by omega)
      rw [this]
      have h0 : S δ β 0 = 0 := by unfold S; simp
      rw [h0, zero_add, hi0]
    rw [h1, norm_smul, hunit, Real.norm_eq_abs]
    simp
  | succ k hk ih =>
    intro hp β i hi
    have hkp : k < p := by omega
    set V := Submodule.span ℝ (δ '' {j | j.val < k}) with hV
    set δk := δ ⟨k, hkp⟩
    set b := β ⟨k, hkp⟩
    set q := V.starProjection δk
    set ρ := ‖δk - q‖
    have hρ : η ≤ ρ := hsep ⟨k, hkp⟩ (by simp; omega)
    have hsq : ‖q‖ ^ 2 + ρ ^ 2 = 1 := by
      have := pyth V 0 δk V.zero_mem 1
      simp only [zero_add, one_smul, one_pow, one_mul] at this
      rw [hunit] at this
      linarith
    have hv : S δ β (k + 1) = S δ β k + b • δk := S_succ δ β k hkp
    have hpy := pyth V (S δ β k) δk (S_mem δ β k) b
    rw [← hv] at hpy
    replace hpy : ‖S δ β (k + 1)‖ ^ 2 = ‖S δ β k + b • q‖ ^ 2 + b ^ 2 * ρ ^ 2 := hpy
    have hvn : 0 ≤ ‖S δ β (k + 1)‖ := norm_nonneg _
    have hρ0 : 0 ≤ ρ := norm_nonneg _
    have hηk : η ^ (k + 1 - 1) = η * η ^ (k - 1) := by
      rw [show k + 1 - 1 = (k - 1) + 1 by omega, pow_succ, mul_comm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hik | hik
    · -- old index
      have hM := ih (by omega) β i hik
      set N := ‖S δ β k‖
      set x := ‖S δ β k + b • q‖
      have hx0 : 0 ≤ x := norm_nonneg _
      have hxN : N - |b| * ‖q‖ ≤ x := by
        have h1 : N ≤ x + ‖b • q‖ := by
          have := norm_sub_le (S δ β k + b • q) (b • q)
          simpa using this
        rw [norm_smul, Real.norm_eq_abs] at h1
        linarith
      have hq0 : 0 ≤ ‖q‖ := norm_nonneg _
      have hb0 : 0 ≤ |b| := abs_nonneg _
      have hbsq : |b| ^ 2 = b ^ 2 := sq_abs b
      have hM0 : 0 ≤ |β i| * η ^ (k - 1) := by positivity
      have key : ρ ^ 2 * N ^ 2 ≤ ‖S δ β (k + 1)‖ ^ 2 := by
        rw [hpy]
        rcases le_or_gt (N - |b| * ‖q‖) 0 with hc | hc
        · have hq1 : ‖q‖ ^ 2 ≤ 1 := by nlinarith
          have hN0 : 0 ≤ N := norm_nonneg _
          have : N ^ 2 ≤ |b| ^ 2 * ‖q‖ ^ 2 := by nlinarith
          have h5 : N ^ 2 ≤ b ^ 2 := by nlinarith
          have h6 : ρ ^ 2 * N ^ 2 ≤ ρ ^ 2 * b ^ 2 :=
            mul_le_mul_of_nonneg_left h5 (sq_nonneg ρ)
          nlinarith [sq_nonneg x]
        · have hx2 : (N - |b| * ‖q‖) ^ 2 ≤ x ^ 2 := by nlinarith
          nlinarith [sq_nonneg (N * ‖q‖ - |b|)]
      rw [hηk]
      have hN0 : 0 ≤ N := norm_nonneg _
      have h2 : η * (|β i| * η ^ (k - 1)) ≤ ρ * N := by
        apply mul_le_mul hρ hM hM0 hρ0
      have h3 : ρ * N ≤ ‖S δ β (k + 1)‖ := by
        have := mul_nonneg hρ0 hN0
        nlinarith
      nlinarith
    · -- new index
      have hik' : i = ⟨k, hkp⟩ := Fin.ext hik
      subst hik'
      have key : b ^ 2 * ρ ^ 2 ≤ ‖S δ β (k + 1)‖ ^ 2 := by
        rw [hpy]; nlinarith [sq_nonneg ‖S δ β k + b • q‖]
      have hbr : |b| * ρ ≤ ‖S δ β (k + 1)‖ := by
        have : 0 ≤ |b| * ρ := by positivity
        nlinarith [sq_abs b]
      have hpow : η ^ (k + 1 - 1) ≤ η := by
        rw [hηk]
        have : η ^ (k - 1) ≤ 1 := pow_le_one₀ hη0.le hη1
        nlinarith
      calc |b| * η ^ (k + 1 - 1) ≤ |b| * ρ :=
            mul_le_mul_of_nonneg_left (hpow.trans hρ) (abs_nonneg _)
        _ ≤ _ := hbr

end PolyConeAux

namespace PolyConeAux

theorem vecAngle_nonneg' {d : ℕ} (c ch : EuclideanSpace ℝ (Fin d)) : 0 ≤ vecAngle c ch := by
  unfold vecAngle; split_ifs
  · exact le_rfl
  · exact Real.arccos_nonneg _

/-- Reduction of the angle bound to a pointwise inner-product bound for one unit vector. -/
theorem uncAngle_le_of {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (κ : ℝ)
    (ch : EuclideanSpace ℝ (Fin d)) (hch : ‖ch‖ = 1)
    (hc : ∀ c ∈ K, κ * ‖c‖ ≤ inner ℝ c ch) : uncAngle K ≤ Real.arccos κ := by
  unfold uncAngle
  have hmem : ch ∈ unitSphere d := by simp [unitSphere, hch]
  refine (ciInf_le ⟨0, ?_⟩ (⟨ch, hmem⟩ : unitSphere d)).trans ?_
  · rintro _ ⟨x, rfl⟩
    exact Real.iSup_nonneg (fun c => vecAngle_nonneg' _ _)
  · refine Real.iSup_le (fun c => ?_) (Real.arccos_nonneg _)
    unfold vecAngle
    split_ifs with h0
    · exact Real.arccos_nonneg _
    · rw [not_or] at h0
      apply Real.arccos_le_arccos
      have hpos : 0 < ‖(c : EuclideanSpace ℝ (Fin d))‖ := norm_pos_iff.mpr h0.1
      rw [hch, mul_one, le_div_iff₀ hpos]
      exact hc c c.2

end PolyConeAux

open PolyConeAux in
theorem solution {d p : ℕ} (hd : 2 ≤ d) (hpd : p ≤ d) (η : ℝ) (hη0 : 0 < η)
    (hη1 : η ≤ 1) (δ : Fin p → EuclideanSpace ℝ (Fin d)) (hunit : ∀ i, ‖δ i‖ = 1)
    (hsep : ∀ i : Fin p, 0 < i.val →
      η ≤ ‖δ i - (Submodule.span ℝ (δ '' {j | j < i})).starProjection (δ i)‖) :
    CtxInvOpt.Offline.uncAngle (polyCone δ) ≤ Real.arccos (η ^ (d - 1) / (d : ℝ) ^ ((3 : ℝ) / 2)) := by
  set κ := η ^ (d - 1) / (d : ℝ) ^ ((3 : ℝ) / 2) with hκ
  rcases Nat.eq_zero_or_pos p with hp | hp
  · subst hp
    refine uncAngle_le_of _ κ (EuclideanSpace.single ⟨0, by omega⟩ 1) (by simp) ?_
    intro c hc
    have hc0 : c = 0 := by
      have h := hc.1
      have : Set.range δ = ∅ := Set.range_eq_empty δ
      rw [this, Submodule.span_empty, Submodule.mem_bot] at h
      exact h
    subst hc0
    simp
  · set s : EuclideanSpace ℝ (Fin d) := ∑ j, δ j with hs
    have hcoef : ∀ (β : Fin p → ℝ) (i : Fin p), |β i| * η ^ (p - 1) ≤ ‖∑ j, β j • δ j‖ := by
      intro β i
      have := coeff_bound η hη0 hη1 δ hunit hsep p hp le_rfl β i i.2
      rwa [S_full] at this
    have hφ : 0 < η ^ (p - 1) := pow_pos hη0 _
    have hslow : η ^ (p - 1) ≤ ‖s‖ := by
      have := hcoef (fun _ => 1) ⟨0, hp⟩
      simpa [hs] using this
    have hspos : 0 < ‖s‖ := lt_of_lt_of_le hφ hslow
    have hsup : ‖s‖ ≤ p := by
      calc ‖s‖ ≤ ∑ j, ‖δ j‖ := norm_sum_le _ _
        _ = p := by simp [hunit]
    have hκle : κ ≤ η ^ (p - 1) / p := by
      have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
      have hpd' : (p : ℝ) ≤ d := by exact_mod_cast hpd
      have hp' : (0 : ℝ) < p := by exact_mod_cast hp
      have hdd : (d : ℝ) ≤ (d : ℝ) ^ ((3 : ℝ) / 2) := by
        have := Real.rpow_le_rpow_of_exponent_le hd1 (by norm_num : (1 : ℝ) ≤ 3 / 2)
        simpa using this
      have hpow : η ^ (d - 1) ≤ η ^ (p - 1) :=
        pow_le_pow_of_le_one hη0.le hη1 (by omega)
      rw [hκ]
      exact div_le_div₀ hφ.le hpow hp' (hpd'.trans hdd)
    refine uncAngle_le_of _ κ (‖s‖⁻¹ • s) ?_ ?_
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hspos.ne']
    · intro c hc
      obtain ⟨hspan, hnn⟩ := hc
      obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hspan
      set A := inner ℝ c s with hA
      have hAsum : A = ∑ j, inner ℝ c (δ j) := by rw [hA, hs, inner_sum]
      have hA0 : 0 ≤ A := by rw [hAsum]; exact Finset.sum_nonneg (fun j _ => hnn j)
      have hcc : ‖c‖ ^ 2 = ∑ j, β j * inner ℝ c (δ j) := by
        rw [← real_inner_self_eq_norm_sq]
        nth_rewrite 1 [← hβ]
        rw [sum_inner]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [real_inner_smul_left, real_inner_comm]
      have hβb : ∀ j, |β j| * η ^ (p - 1) ≤ ‖c‖ := by
        intro j; have := hcoef β j; rwa [hβ] at this
      -- φ ‖c‖² ≤ ‖c‖ A
      have hmain : η ^ (p - 1) * ‖c‖ ^ 2 ≤ ‖c‖ * A := by
        rw [hcc, hAsum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_le_sum (fun j _ => ?_)
        have h1 : β j * inner ℝ c (δ j) ≤ |β j| * inner ℝ c (δ j) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (hnn j)
        have h2 := mul_le_mul_of_nonneg_right (hβb j) (hnn j)
        nlinarith [hφ]
      have hφc : η ^ (p - 1) * ‖c‖ ≤ A := by
        rcases eq_or_lt_of_le (norm_nonneg c) with h0 | h0
        · rw [← h0]; simpa using hA0
        · nlinarith
      have hin : inner ℝ c (‖s‖⁻¹ • s) = A / ‖s‖ := by
        rw [real_inner_smul_right, hA, inv_mul_eq_div]
      rw [hin, le_div_iff₀ hspos]
      have hp' : (0 : ℝ) < p := by exact_mod_cast hp
      have hκ0 : 0 ≤ κ := by rw [hκ]; positivity
      calc κ * ‖c‖ * ‖s‖ ≤ κ * ‖c‖ * p :=
            mul_le_mul_of_nonneg_left hsup (mul_nonneg hκ0 (norm_nonneg _))
        _ ≤ (η ^ (p - 1) / p) * ‖c‖ * p := by
            gcongr
        _ = η ^ (p - 1) * ‖c‖ := by field_simp
        _ ≤ A := hφc
