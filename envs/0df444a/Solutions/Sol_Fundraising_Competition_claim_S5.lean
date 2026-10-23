-- Prove2me | solution 1 for Fundraising.Competition.claim_S5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T16:32:11.553969+00:00
-- url     : https://prove2.me/submissions/ee7f7f01-b443-40ce-be50-2bb6e7ef66c0

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

section BR

open Set

/-- Abstract best-response characterization for one HO. -/
lemma br_abstract (P : ℝ → ℝ) (a b B : ℝ) (C : ℝ → ℝ) (hab : a ≤ b)
    (hP : ContinuousOn P (Icc a b)) (hPpos : ∀ σ ∈ Icc a b, 0 < P σ) (hB : 0 < B)
    (hC : StrictMonoOn C (Icc 0 1)) (σ ξ : ℝ) (hσ : σ ∈ Icc a b) (hξ : ξ ∈ Icc (0 : ℝ) 1) :
    ((∀ q ∈ Icc a b ×ˢ Icc (0 : ℝ) 1, max (B - ξ * P σ) 0 ≤ max (B - q.2 * P q.1) 0) ∧
      ∀ q, (q ∈ Icc a b ×ˢ Icc (0 : ℝ) 1 ∧
          ∀ r ∈ Icc a b ×ˢ Icc (0 : ℝ) 1, max (B - q.2 * P q.1) 0 ≤ max (B - r.2 * P r.1) 0) →
        min (q.2 * P q.1) B - C q.2 ≤ min (ξ * P σ) B - C ξ) ↔
    ((∀ τ ∈ Icc a b, P τ ≤ P σ) ∧ ξ = min (B / P σ) 1) := by
  -- a maximizer exists
  obtain ⟨σs, hσs, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab) hP
  rw [isMaxOn_iff] at hmax
  set M := P σs with hM
  have hMpos : 0 < M := hPpos σs hσs
  have hbound : ∀ q ∈ Icc a b ×ˢ Icc (0 : ℝ) 1, q.2 * P q.1 ≤ M := by
    intro q hq
    obtain ⟨hq1, hq2⟩ := hq
    have := hPpos q.1 hq1
    have := hmax q.1 hq1
    nlinarith [hq2.1, hq2.2]
  -- the candidate strategy is a gap minimizer
  have cand : ∀ σ' ∈ Icc a b, P σ' = M → ∀ q ∈ Icc a b ×ˢ Icc (0 : ℝ) 1,
      max (B - min (B / P σ') 1 * P σ') 0 ≤ max (B - q.2 * P q.1) 0 := by
    intro σ' _ hσ' q hq
    rw [hσ']
    have hq' := hbound q hq
    rcases le_total B M with h | h
    · have : min (B / M) 1 = B / M := min_eq_left ((div_le_one hMpos).mpr h)
      rw [this, div_mul_cancel₀ _ hMpos.ne']
      simp only [sub_self, max_self]
      exact le_max_right _ _
    · have : min (B / M) 1 = 1 := min_eq_right ((le_div_iff₀ hMpos).mpr (by linarith))
      rw [this, one_mul]
      exact max_le_max (by linarith) le_rfl
  constructor
  · rintro ⟨hgap, hutil⟩
    have hs_mem : (σs, min (B / M) 1) ∈ Icc a b ×ˢ Icc (0 : ℝ) 1 :=
      ⟨hσs, ⟨le_min (by positivity) zero_le_one, min_le_right _ _⟩⟩
    have hgap' : max (B - ξ * P σ) 0 ≤ max (B - min (B / M) 1 * M) 0 := hgap _ hs_mem
    have hσpos := hPpos σ hσ
    have hPσ := hmax σ hσ
    rcases lt_or_ge M B with h | h
    · -- M < B: must use full effort at a maximizer
      have h1 : min (B / M) 1 = 1 := min_eq_right ((le_div_iff₀ hMpos).mpr (by linarith))
      simp only [h1, one_mul] at hgap'
      have hge : M ≤ ξ * P σ := by
        have hgm : max (B - M) 0 = B - M := max_eq_left (by linarith)
        rw [hgm] at hgap'
        linarith [le_max_left (B - ξ * P σ) 0]
      have hPeq : P σ = M := by nlinarith [hξ.2]
      have hξ1 : ξ = 1 := by
        rw [hPeq] at hge
        have := hξ.2
        nlinarith
      refine ⟨fun τ hτ => hPeq ▸ hmax τ hτ, ?_⟩
      rw [hPeq, h1, hξ1]
    · -- B ≤ M
      have h1 : min (B / M) 1 = B / M := min_eq_left ((div_le_one hMpos).mpr h)
      have hBM : B / M * M = B := div_mul_cancel₀ _ hMpos.ne'
      rw [h1, hBM, sub_self, max_self] at hgap'
      have hcov : B ≤ ξ * P σ := by
        have := le_max_left (B - ξ * P σ) 0
        linarith
      have hu : min (min (B / M) 1 * M) B - C (min (B / M) 1) ≤ min (ξ * P σ) B - C ξ :=
        hutil (σs, min (B / M) 1) ⟨hs_mem, cand σs hσs rfl⟩
      rw [h1, hBM, min_self] at hu
      have hcov' : min (ξ * P σ) B = B := min_eq_right hcov
      rw [hcov'] at hu
      have hCle : C ξ ≤ C (B / M) := by linarith
      have hBMmem : B / M ∈ Icc (0 : ℝ) 1 := ⟨by positivity, (div_le_one hMpos).mpr h⟩
      have hξle : ξ ≤ B / M := (hC.le_iff_le hξ hBMmem).mp hCle
      have hξM : ξ * M ≤ B := by
        have := mul_le_mul_of_nonneg_right hξle hMpos.le
        rwa [hBM] at this
      have hξpos : 0 < ξ := by
        by_contra hneg
        have : ξ = 0 := le_antisymm (not_lt.mp hneg) hξ.1
        rw [this, zero_mul] at hcov
        linarith
      have hPeq : P σ = M := by
        have : ξ * M ≤ ξ * P σ := by linarith
        have := le_of_mul_le_mul_left this hξpos
        linarith
      refine ⟨fun τ hτ => hPeq ▸ hmax τ hτ, ?_⟩
      rw [hPeq, h1]
      apply le_antisymm hξle
      rw [div_le_iff₀ hMpos]
      rw [hPeq] at hcov
      linarith
  · rintro ⟨hPmax, hξeq⟩
    have hPσ : P σ = M := le_antisymm (hmax σ hσ) (hPmax σs hσs)
    have hσpos := hPpos σ hσ
    refine ⟨?_, ?_⟩
    · intro q hq
      rw [hξeq]
      exact cand σ hσ hPσ q hq
    · rintro q ⟨hq, hqmin⟩
      have hle := hqmin (σ, ξ) ⟨hσ, hξ⟩
      have hq' := hbound q hq
      have hq2 := hq.2
      rw [hξeq, hPσ] at hle ⊢
      rcases lt_or_ge M B with h | h
      · have h1 : min (B / M) 1 = 1 := min_eq_right ((le_div_iff₀ hMpos).mpr (by linarith))
        rw [h1, one_mul] at hle ⊢
        rw [max_eq_left (by linarith : (0:ℝ) ≤ B - M)] at hle
        have hge : M ≤ q.2 * P q.1 := by
          have := le_max_left (B - q.2 * P q.1) 0
          linarith
        have hPq := hPpos q.1 hq.1
        have hPq' := hmax q.1 hq.1
        have hq21 : q.2 = 1 := by nlinarith [hq2.2]
        have hqeq : q.2 * P q.1 = M := le_antisymm hq' hge
        rw [hqeq, hq21]
      · have h1 : min (B / M) 1 = B / M := min_eq_left ((div_le_one hMpos).mpr h)
        have hBM : B / M * M = B := div_mul_cancel₀ _ hMpos.ne'
        rw [h1, hBM] at hle ⊢
        simp only [sub_self, max_self] at hle
        have hcov : B ≤ q.2 * P q.1 := by
          have := le_max_left (B - q.2 * P q.1) 0
          linarith
        have hBMmem : B / M ∈ Icc (0 : ℝ) 1 := ⟨by positivity, (div_le_one hMpos).mpr h⟩
        have hge : B / M ≤ q.2 := by
          rw [div_le_iff₀ hMpos]
          nlinarith [hq2.1, hmax q.1 hq.1]
        have hC' : C (B / M) ≤ C q.2 := (hC.le_iff_le hBMmem hq2).mpr hge
        rw [min_self]
        have : min (q.2 * P q.1) B ≤ B := min_le_right _ _
        linarith

end BR

lemma gap_update (S : Setting n) (s x : Fin n → ℝ) (i : Fin n) (σ ξ : ℝ) :
    gap S (Function.update s i σ) (Function.update x i ξ) i =
      max (S.B i - ξ * PPD S (Function.update s i σ) x i) 0 := by
  unfold gap expDonation PPD
  rw [shareSum_update_x]
  simp only [Function.update_self]
  ring_nf

lemma utility_update (S : Setting n) (s x : Fin n → ℝ) (i : Fin n) (σ ξ : ℝ) :
    utility S (Function.update s i σ) (Function.update x i ξ) i =
      min (ξ * PPD S (Function.update s i σ) x i) (S.B i) - S.C i ξ := by
  unfold utility expDonation PPD
  rw [shareSum_update_x]
  simp only [Function.update_self]
  ring_nf

lemma PPD_cont (S : Setting n) (hS : Standing S) (s x : Fin n → ℝ) (i : Fin n) :
    Continuous (fun σ => PPD S (Function.update s i σ) x i) := by
  simp_rw [PPD_update]
  have hδd : Differentiable ℝ (S.δ i) := (hS.δ_contDiff i).differentiable (by norm_num)
  have hF : Continuous (F0 (contactSets i) (weight x i) (cof s i)) := by
    unfold F0
    apply continuous_finsetSum
    intro J _
    have : ∀ t, cof s i J + exp t ≠ 0 := fun t => by
      have := cof_nonneg s i J; positivity
    fun_prop (disch := exact this _)
  exact (hδd.continuous.mul continuous_const).mul hF

lemma PPD_pos (S : Setting n) (hS : Standing S) (s x : Fin n → ℝ)
    (hx : ∀ j, x j ∈ Set.Icc (0 : ℝ) 1) (i : Fin n) (σ : ℝ) (hσ : σ ∈ Set.Icc (S.a i) (S.b i)) :
    0 < PPD S (Function.update s i σ) x i := by
  unfold PPD
  have := shareSum_pos (Function.update s i σ) x hx i
  have := hS.δ_pos i σ hσ
  have := hS.z_pos
  rw [Function.update_self]
  positivity

lemma claim_S5_proof (S : Setting n) (hS : Standing S) (s x : Fin n → ℝ)
    (hbox : InProfileBox S s x) (i : Fin n) :
    IsBestResponse S s x i (s i, x i) ↔
      (IsMaxOn (fun σ => PPD S (Function.update s i σ) x i) (Set.Icc (S.a i) (S.b i)) (s i) ∧
        x i = min (S.B i / PPD S s x i) 1) := by
  have hx : ∀ j, x j ∈ Set.Icc (0 : ℝ) 1 := fun j => (hbox j).2
  have key := br_abstract (fun σ => PPD S (Function.update s i σ) x i) (S.a i) (S.b i) (S.B i)
    (S.C i) (hS.a_le_b i) (PPD_cont S hS s x i).continuousOn (PPD_pos S hS s x hx i)
    (hS.B_pos i) (hS.C_strictMonoOn i) (s i) (x i) (hbox i).1 (hbox i).2
  simp only [Function.update_eq_self] at key
  rw [isMaxOn_iff]
  simp only [Function.update_eq_self]
  refine Iff.trans ?_ key
  have hu0 : utility S s x i = min (x i * PPD S s x i) (S.B i) - S.C i (x i) := by
    have := utility_update S s x i (s i) (x i)
    simpa only [Function.update_eq_self] using this
  have hg0 : gap S s x i = max (S.B i - x i * PPD S s x i) 0 := by
    have := gap_update S s x i (s i) (x i)
    simpa only [Function.update_eq_self] using this
  unfold IsBestResponse gapMinimizers stratBox
  simp only [gap_update, utility_update, Function.update_eq_self, Set.mem_setOf_eq, hu0, hg0]
  constructor
  · rintro ⟨⟨_, h1⟩, h2⟩
    exact ⟨h1, fun q hq => h2 q hq⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨⟨(hbox i).1, (hbox i).2⟩, h1⟩, fun q hq => h2 q hq⟩
end FRModel
end Fundraising.Competition

open Fundraising.Competition in
theorem solution {n : ℕ} (S : Setting n) (hS : Standing S) (s x : Fin n → ℝ)
    (hbox : InProfileBox S s x) (i : Fin n) :
    IsBestResponse S s x i (s i, x i) ↔
      (IsMaxOn (fun σ => PPD S (Function.update s i σ) x i) (Set.Icc (S.a i) (S.b i)) (s i) ∧
        x i = min (S.B i / PPD S s x i) 1) :=
  Fundraising.Competition.FRModel.claim_S5_proof S hS s x hbox i
