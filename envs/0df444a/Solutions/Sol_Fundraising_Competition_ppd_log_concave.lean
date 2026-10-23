-- Prove2me | solution 1 for Fundraising.Competition.ppd_log_concave
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T16:28:04.120901+00:00
-- url     : https://prove2.me/submissions/34a889f6-e21c-4043-a953-3ceaa69db95c

import Mathlib
import Definitions.Def_Fundraising_Competition_Setting

namespace FRHelp

open Finset Real

section LogSum

variable {ι : Type*} (A : Finset ι) (w c : ι → ℝ)

/-- `F(t) = Σ_J w_J e^t / (c_J + e^t)`. -/
noncomputable def F0 (t : ℝ) : ℝ := ∑ J ∈ A, w J * (exp t / (c J + exp t))
/-- `F'(t) = Σ_J w_J c_J e^t / (c_J + e^t)^2`. -/
noncomputable def F1 (t : ℝ) : ℝ := ∑ J ∈ A, w J * (c J * exp t / (c J + exp t) ^ 2)
/-- `F''(t) = Σ_J w_J c_J e^t (c_J - e^t) / (c_J + e^t)^3`. -/
noncomputable def F2 (t : ℝ) : ℝ :=
  ∑ J ∈ A, w J * (c J * exp t * (c J - exp t) / (c J + exp t) ^ 3)

variable {A w c}

lemma hasDerivAt_term0 (cJ : ℝ) (hc : 0 ≤ cJ) (t : ℝ) :
    HasDerivAt (fun t => exp t / (cJ + exp t)) (cJ * exp t / (cJ + exp t) ^ 2) t := by
  have hpos : 0 < cJ + exp t := by positivity
  have := (hasDerivAt_exp t).div ((hasDerivAt_exp t).const_add cJ) hpos.ne'
  refine this.congr_deriv ?_
  field_simp
  ring

lemma hasDerivAt_term1 (cJ : ℝ) (hc : 0 ≤ cJ) (t : ℝ) :
    HasDerivAt (fun t => cJ * exp t / (cJ + exp t) ^ 2)
      (cJ * exp t * (cJ - exp t) / (cJ + exp t) ^ 3) t := by
  have hpos : 0 < cJ + exp t := by positivity
  have := ((hasDerivAt_exp t).const_mul cJ).div
    (((hasDerivAt_exp t).const_add cJ).pow 2) (pow_ne_zero 2 hpos.ne')
  refine this.congr_deriv ?_
  simp only [Pi.pow_apply, Nat.cast_ofNat]
  field_simp
  ring

lemma hasDerivAt_F0 (hc : ∀ J ∈ A, 0 ≤ c J) (t : ℝ) :
    HasDerivAt (F0 A w c) (F1 A w c t) t := by
  unfold F0 F1
  have := HasDerivAt.fun_sum (u := A) (A := fun J t => w J * (exp t / (c J + exp t)))
    (A' := fun J => w J * (c J * exp t / (c J + exp t) ^ 2)) (x := t)
    (fun J hJ => (hasDerivAt_term0 (c J) (hc J hJ) t).const_mul (w J))
  exact this

lemma hasDerivAt_F1 (hc : ∀ J ∈ A, 0 ≤ c J) (t : ℝ) :
    HasDerivAt (F1 A w c) (F2 A w c t) t := by
  unfold F1 F2
  exact HasDerivAt.fun_sum (u := A) (A := fun J t => w J * (c J * exp t / (c J + exp t) ^ 2))
    (A' := fun J => w J * (c J * exp t * (c J - exp t) / (c J + exp t) ^ 3)) (x := t)
    (fun J hJ => (hasDerivAt_term1 (c J) (hc J hJ) t).const_mul (w J))

lemma F0_pos (hw : ∀ J ∈ A, 0 ≤ w J) (hc : ∀ J ∈ A, 0 ≤ c J)
    (hpos : ∃ J ∈ A, 0 < w J) (t : ℝ) : 0 < F0 A w c t := by
  obtain ⟨J0, hJ0, hw0⟩ := hpos
  unfold F0
  apply Finset.sum_pos' (fun J hJ => mul_nonneg (hw J hJ) (by
    have := hc J hJ; positivity))
  exact ⟨J0, hJ0, mul_pos hw0 (by have := hc J0 hJ0; positivity)⟩

lemma F0_nonneg (hw : ∀ J ∈ A, 0 ≤ w J) (hc : ∀ J ∈ A, 0 ≤ c J) (t : ℝ) :
    0 ≤ F0 A w c t := by
  unfold F0
  exact Finset.sum_nonneg (fun J hJ => mul_nonneg (hw J hJ) (by
    have := hc J hJ; positivity))

/-- Term-wise comparison: `F'' ≤ (1 + 2 p₀) F' - 2 p₀ F` with `p₀ = 1/(1+e^t)`. -/
lemma F2_le (hw : ∀ J ∈ A, 0 ≤ w J) (hc : ∀ J ∈ A, 1 ≤ c J) (t : ℝ) :
    F2 A w c t ≤ (1 + 2 / (1 + exp t)) * F1 A w c t - 2 / (1 + exp t) * F0 A w c t := by
  unfold F0 F1 F2
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro J hJ
  have hcJ := hc J hJ
  have hwJ := hw J hJ
  have he := exp_pos t
  have h1 : 0 < c J + exp t := by linarith
  have h2 : 0 < 1 + exp t := by linarith
  have key : (1 + 2 / (1 + exp t)) * (w J * (c J * exp t / (c J + exp t) ^ 2)) -
      2 / (1 + exp t) * (w J * (exp t / (c J + exp t))) -
      w J * (c J * exp t * (c J - exp t) / (c J + exp t) ^ 3) =
      2 * w J * exp t ^ 3 * (c J - 1) / ((c J + exp t) ^ 3 * (1 + exp t)) := by
    field_simp
    ring
  have : 0 ≤ 2 * w J * exp t ^ 3 * (c J - 1) / ((c J + exp t) ^ 3 * (1 + exp t)) := by
    apply div_nonneg
    · have : 0 ≤ c J - 1 := by linarith
      positivity
    · positivity
  linarith

/-- The (S8) bound for the second derivative of `log F`. -/
lemma logF_second_le (hw : ∀ J ∈ A, 0 ≤ w J) (hc : ∀ J ∈ A, 1 ≤ c J)
    (hpos : ∃ J ∈ A, 0 < w J) (t : ℝ) :
    (F2 A w c t * F0 A w c t - F1 A w c t ^ 2) / F0 A w c t ^ 2 ≤
      1 / 4 - exp t / (1 + exp t) ^ 2 := by
  have hc0 : ∀ J ∈ A, 0 ≤ c J := fun J hJ => by linarith [hc J hJ]
  have hF := F0_pos hw hc0 hpos t
  have h2 := F2_le hw hc t
  have he := exp_pos t
  set p := 2 / (1 + exp t) with hp
  set F := F0 A w c t
  set G := F1 A w c t
  set H := F2 A w c t
  have hrhs : 1 / 4 - exp t / (1 + exp t) ^ 2 = (1 / 2 - p / 2) ^ 2 := by
    rw [hp]; field_simp; ring
  rw [hrhs, div_le_iff₀ (by positivity)]
  have : H * F ≤ ((1 + p) * G - p * F) * F := mul_le_mul_of_nonneg_right h2 hF.le
  nlinarith [sq_nonneg (G - (1 + p) / 2 * F)]

/-- `log F` has derivative `F'/F`, and `F'/F` has derivative `(F'' F - F'^2)/F^2`. -/
lemma hasDerivAt_logF (hw : ∀ J ∈ A, 0 ≤ w J) (hc : ∀ J ∈ A, 0 ≤ c J)
    (hpos : ∃ J ∈ A, 0 < w J) (t : ℝ) :
    HasDerivAt (fun t => Real.log (F0 A w c t)) (F1 A w c t / F0 A w c t) t :=
  (hasDerivAt_F0 hc t).log (F0_pos hw hc hpos t).ne'

lemma hasDerivAt_F1_div_F0 (hw : ∀ J ∈ A, 0 ≤ w J) (hc : ∀ J ∈ A, 0 ≤ c J)
    (hpos : ∃ J ∈ A, 0 < w J) (t : ℝ) :
    HasDerivAt (fun t => F1 A w c t / F0 A w c t)
      ((F2 A w c t * F0 A w c t - F1 A w c t ^ 2) / F0 A w c t ^ 2) t := by
  have := (hasDerivAt_F1 (w := w) hc t).div (hasDerivAt_F0 (w := w) hc t) (F0_pos hw hc hpos t).ne'
  refine this.congr_deriv ?_
  ring

end LogSum

end FRHelp

namespace Fundraising.Competition
namespace FRModel

open Finset Real FRHelp

variable {n : ℕ}

/-- `c_J = 1 + Σ_{j ∈ J, j ≠ i} e^{s_j}`. -/
noncomputable def cof (s : Fin n → ℝ) (i : Fin n) (J : Finset (Fin n)) : ℝ :=
  1 + ∑ j ∈ J.erase i, exp (s j)

lemma one_le_cof (s : Fin n → ℝ) (i : Fin n) (J : Finset (Fin n)) : 1 ≤ cof s i J := by
  unfold cof
  have : 0 ≤ ∑ j ∈ J.erase i, exp (s j) := Finset.sum_nonneg (fun j _ => (exp_pos _).le)
  linarith

lemma cof_nonneg (s : Fin n → ℝ) (i : Fin n) (J : Finset (Fin n)) : 0 ≤ cof s i J := by
  linarith [one_le_cof s i J]

lemma mem_contactSets {i : Fin n} {J : Finset (Fin n)} : J ∈ contactSets i ↔ i ∈ J := by
  simp [contactSets]

lemma theta_update (s : Fin n → ℝ) (i : Fin n) (J : Finset (Fin n)) (hi : i ∈ J) (t : ℝ) :
    theta (Function.update s i t) J i = exp t / (cof s i J + exp t) := by
  unfold theta cof
  rw [← Finset.add_sum_erase J _ hi]
  simp only [Function.update_self]
  have : ∑ j ∈ J.erase i, exp (Function.update s i t j) = ∑ j ∈ J.erase i, exp (s j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [this]
  ring_nf

lemma shareSum_update_s (s x : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    shareSum (Function.update s i t) x i = F0 (contactSets i) (weight x i) (cof s i) t := by
  unfold shareSum F0
  apply Finset.sum_congr rfl
  intro J hJ
  rw [theta_update s i J (mem_contactSets.mp hJ)]

lemma shareSum_eq_F0 (s x : Fin n → ℝ) (i : Fin n) :
    shareSum s x i = F0 (contactSets i) (weight x i) (cof s i) (s i) := by
  rw [← shareSum_update_s, Function.update_eq_self]

lemma weight_update_x (x : Fin n → ℝ) (i : Fin n) (ξ : ℝ) (J : Finset (Fin n)) (hi : i ∈ J) :
    weight (Function.update x i ξ) i J = weight x i J := by
  unfold weight
  congr 1
  · apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  · apply Finset.prod_congr rfl
    intro j hj
    have : j ≠ i := by
      rintro rfl
      exact (Finset.mem_compl.mp hj) hi
    rw [Function.update_of_ne this]

lemma shareSum_update_x (s x : Fin n → ℝ) (i : Fin n) (ξ : ℝ) :
    shareSum s (Function.update x i ξ) i = shareSum s x i := by
  unfold shareSum
  apply Finset.sum_congr rfl
  intro J hJ
  rw [weight_update_x x i ξ J (mem_contactSets.mp hJ)]

lemma weight_nonneg (x : Fin n → ℝ) (hx : ∀ j, x j ∈ Set.Icc (0 : ℝ) 1) (i : Fin n)
    (J : Finset (Fin n)) : 0 ≤ weight x i J := by
  unfold weight
  apply mul_nonneg
  · exact Finset.prod_nonneg (fun j _ => (hx j).1)
  · exact Finset.prod_nonneg (fun j _ => by linarith [(hx j).2])

lemma exists_weight_pos (x : Fin n → ℝ) (hx : ∀ j, x j ∈ Set.Icc (0 : ℝ) 1) (i : Fin n) :
    ∃ J ∈ contactSets i, 0 < weight x i J := by
  classical
  refine ⟨insert i (Finset.univ.filter (fun j => x j = 1)), ?_, ?_⟩
  · rw [mem_contactSets]; exact Finset.mem_insert_self _ _
  · unfold weight
    apply mul_pos
    · apply Finset.prod_pos
      intro j hj
      have hj' := Finset.mem_of_mem_erase hj
      have hne := Finset.ne_of_mem_erase hj
      rcases Finset.mem_insert.mp hj' with h | h
      · exact absurd h hne
      · rw [(Finset.mem_filter.mp h).2]; norm_num
    · apply Finset.prod_pos
      intro j hj
      have h1 := Finset.mem_compl.mp hj
      have : x j ≠ 1 := by
        intro h; apply h1
        exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      have := (hx j).2
      have : x j < 1 := lt_of_le_of_ne this ‹x j ≠ 1›
      linarith

lemma shareSum_pos (s x : Fin n → ℝ) (hx : ∀ j, x j ∈ Set.Icc (0 : ℝ) 1) (i : Fin n) :
    0 < shareSum s x i := by
  rw [shareSum_eq_F0]
  exact F0_pos (fun J _ => weight_nonneg x hx i J) (fun J _ => cof_nonneg s i J)
    (exists_weight_pos x hx i) _

/-- The function `t ↦ log shareSum(s_{-i}, t)` has derivative `F1/F0`. -/
lemma deriv_log_shareSum (s x : Fin n → ℝ) (hx : ∀ j, x j ∈ Set.Icc (0 : ℝ) 1) (i : Fin n) :
    deriv (fun t => Real.log (shareSum (Function.update s i t) x i)) =
      fun t => F1 (contactSets i) (weight x i) (cof s i) t /
        F0 (contactSets i) (weight x i) (cof s i) t := by
  funext t
  simp_rw [shareSum_update_s]
  exact (hasDerivAt_logF (fun J _ => weight_nonneg x hx i J) (fun J _ => cof_nonneg s i J)
    (exists_weight_pos x hx i) t).deriv

lemma eq_S8_proof (s x : Fin n → ℝ) (hx : ∀ j, x j ∈ Set.Icc (0 : ℝ) 1) (i : Fin n) :
    deriv (deriv (fun t => Real.log (shareSum (Function.update s i t) x i))) (s i) ≤
      1 / 4 - Real.exp (s i) / (1 + Real.exp (s i)) ^ 2 := by
  rw [deriv_log_shareSum s x hx i]
  rw [(hasDerivAt_F1_div_F0 (fun J _ => weight_nonneg x hx i J) (fun J _ => cof_nonneg s i J)
    (exists_weight_pos x hx i) (s i)).deriv]
  exact logF_second_le (fun J _ => weight_nonneg x hx i J) (fun J _ => one_le_cof s i J)
    (exists_weight_pos x hx i) _


lemma deriv_differentiable_of_contDiff2 {f : ℝ → ℝ} (h : ContDiff ℝ 2 f) :
    Differentiable ℝ (deriv f) := by
  have h' : ContDiff ℝ (1 + 1) f := by rw [one_add_one_eq_two]; exact h
  exact ((contDiff_succ_iff_deriv (n := 1)).mp h').2.2.differentiable (by norm_num)

lemma PPD_update (S : Setting n) (s x : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    PPD S (Function.update s i t) x i =
      S.δ i t * S.z * F0 (contactSets i) (weight x i) (cof s i) t := by
  unfold PPD
  rw [shareSum_update_s, Function.update_self]

/-- Derivative of `t ↦ log PPD_i(s_{-i}, t)` at a point where `δ_i > 0`. -/
lemma hasDerivAt_logPPD (S : Setting n) (hS : Standing S) (s x : Fin n → ℝ)
    (hx : ∀ j, x j ∈ Set.Icc (0 : ℝ) 1) (i : Fin n) (t : ℝ) (hδ : 0 < S.δ i t) :
    HasDerivAt (fun t => Real.log (PPD S (Function.update s i t) x i))
      (deriv (S.δ i) t / S.δ i t +
        F1 (contactSets i) (weight x i) (cof s i) t /
          F0 (contactSets i) (weight x i) (cof s i) t) t := by
  have hw : ∀ J ∈ contactSets i, 0 ≤ weight x i J := fun J _ => weight_nonneg x hx i J
  have hc : ∀ J ∈ contactSets i, 0 ≤ cof s i J := fun J _ => cof_nonneg s i J
  have hpos := exists_weight_pos x hx i
  have hF := F0_pos hw hc hpos t
  have hz := hS.z_pos
  have hd : HasDerivAt (S.δ i) (deriv (S.δ i) t) t :=
    (((hS.δ_contDiff i).differentiable (by norm_num)) t).hasDerivAt
  have hprod := ((hd.mul_const S.z).mul (hasDerivAt_F0 (w := weight x i) hc t))
  have hne : S.δ i t * S.z * F0 (contactSets i) (weight x i) (cof s i) t ≠ 0 := by positivity
  have := hprod.log hne
  simp_rw [PPD_update]
  refine this.congr_deriv ?_
  simp only [Pi.mul_apply]
  field_simp

lemma ppd_log_concave_proof (S : Setting n) (hS : Standing S) (hA : Assumption1 S)
    (s x : Fin n → ℝ) (hx : ∀ j, x j ∈ Set.Icc (0 : ℝ) 1) (i : Fin n) :
    ConcaveOn ℝ (Set.Icc (S.a i) (S.b i))
      (fun t => Real.log (PPD S (Function.update s i t) x i)) := by
  have hw : ∀ J ∈ contactSets i, 0 ≤ weight x i J := fun J _ => weight_nonneg x hx i J
  have hc : ∀ J ∈ contactSets i, 0 ≤ cof s i J := fun J _ => cof_nonneg s i J
  have hc1 : ∀ J ∈ contactSets i, 1 ≤ cof s i J := fun J _ => one_le_cof s i J
  have hpos := exists_weight_pos x hx i
  have hδc : ContDiff ℝ 2 (S.δ i) := hS.δ_contDiff i
  have hδd : Differentiable ℝ (S.δ i) := hδc.differentiable (by norm_num)
  have hδ'd : Differentiable ℝ (deriv (S.δ i)) := deriv_differentiable_of_contDiff2 hδc
  have hz := hS.z_pos
  set A := contactSets i
  set w := weight x i
  set c := cof s i
  have hint : interior (Set.Icc (S.a i) (S.b i)) = Set.Ioo (S.a i) (S.b i) := interior_Icc
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc _ _)
    (f' := fun t => deriv (S.δ i) t / S.δ i t + F1 A w c t / F0 A w c t)
    (f'' := fun t => deriv (fun u => deriv (S.δ i) u / S.δ i u) t +
      (F2 A w c t * F0 A w c t - F1 A w c t ^ 2) / F0 A w c t ^ 2)
  · -- continuity
    have : ∀ t ∈ Set.Icc (S.a i) (S.b i),
        HasDerivAt (fun t => Real.log (PPD S (Function.update s i t) x i))
          (deriv (S.δ i) t / S.δ i t + F1 A w c t / F0 A w c t) t :=
      fun t ht => hasDerivAt_logPPD S hS s x hx i t (hS.δ_pos i t ht)
    exact fun t ht => (this t ht).continuousAt.continuousWithinAt
  · intro t ht
    rw [hint] at ht
    have ht' : t ∈ Set.Icc (S.a i) (S.b i) := Set.Ioo_subset_Icc_self ht
    exact (hasDerivAt_logPPD S hS s x hx i t (hS.δ_pos i t ht')).hasDerivWithinAt
  · intro t ht
    rw [hint] at ht
    have ht' : t ∈ Set.Icc (S.a i) (S.b i) := Set.Ioo_subset_Icc_self ht
    have hδt : S.δ i t ≠ 0 := (hS.δ_pos i t ht').ne'
    have h1 : DifferentiableAt ℝ (fun u => deriv (S.δ i) u / S.δ i u) t :=
      (hδ'd t).div (hδd t) hδt
    exact (h1.hasDerivAt.add (hasDerivAt_F1_div_F0 hw hc hpos t)).hasDerivWithinAt
  · intro t ht
    rw [hint] at ht
    have ht' : t ∈ Set.Icc (S.a i) (S.b i) := Set.Ioo_subset_Icc_self ht
    have hδt : 0 < S.δ i t := hS.δ_pos i t ht'
    have hA' := hA i t ht'
    -- identify deriv (deriv (log ∘ δ)) with deriv (δ'/δ)
    have hev : deriv (fun u => Real.log (S.δ i u)) =ᶠ[nhds t]
        (fun u => deriv (S.δ i) u / S.δ i u) := by
      have : ∀ᶠ u in nhds t, 0 < S.δ i u :=
        continuousAt_const.eventually_lt (hδd.continuous.continuousAt (x := t)) hδt
      filter_upwards [this] with u hu
      exact deriv.log (hδd u) hu.ne'
    rw [hev.deriv_eq] at hA'
    have hS8 := logF_second_le hw hc1 hpos t
    linarith
end FRModel
end Fundraising.Competition

open Fundraising.Competition in
theorem solution {n : ℕ} (S : Setting n) (hS : Standing S) (hA : Assumption1 S)
    (s x : Fin n → ℝ) (hx : ∀ j, x j ∈ Set.Icc (0 : ℝ) 1) (i : Fin n) :
    ConcaveOn ℝ (Set.Icc (S.a i) (S.b i))
      (fun t => Real.log (PPD S (Function.update s i t) x i)) :=
  Fundraising.Competition.FRModel.ppd_log_concave_proof S hS hA s x hx i
