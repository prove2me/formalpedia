-- Prove2me | solution 1 for Fundraising.Competition.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T16:36:49.526991+00:00
-- url     : https://prove2.me/submissions/a7c57b52-3caf-4fb5-ba96-ef8793cc4bfb

import Mathlib
import Definitions.Def_Fundraising_Competition_Setting
import Theorems.Thm_Fundraising_Competition_claim_S5
import Theorems.Thm_Fundraising_Competition_ppd_log_concave
import Theorems.Thm_AGT_brouwer_fixed_point

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


section KKT

open Set

lemma kkt_iff_max {f : ℝ → ℝ} {a b s d : ℝ} (hab : a ≤ b) (hs : s ∈ Icc a b)
    (hconc : ConcaveOn ℝ (Icc a b) f) (hd : HasDerivAt f d s) :
    (∀ t ∈ Icc a b, f t ≤ f s) ↔
      ∃ l1 l2 : ℝ, 0 ≤ l1 ∧ 0 ≤ l2 ∧ d + l1 - l2 = 0 ∧ l1 * (a - s) = 0 ∧ l2 * (s - b) = 0 := by
  constructor
  · intro hmax
    have hloc : IsLocalMaxOn f (Icc a b) s := (isMaxOn_iff.mpr hmax).localize
    have hF : HasFDerivWithinAt f (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) d) (Icc a b) s :=
      hd.hasDerivWithinAt.hasFDerivWithinAt
    have key : ∀ y ∈ Icc a b, (y - s) * d ≤ 0 := by
      intro y hy
      have hy' : y - s ∈ posTangentConeAt (Icc a b) s :=
        sub_mem_posTangentConeAt_of_segment_subset ((convex_Icc a b).segment_subset hs hy)
      have := hloc.hasFDerivWithinAt_nonpos hF hy'
      simpa [mul_comm] using this
    refine ⟨max (-d) 0, max d 0, le_max_right _ _, le_max_right _ _, ?_, ?_, ?_⟩
    · rcases le_total d 0 with h | h
      · rw [max_eq_left (by linarith), max_eq_right h]; ring
      · rw [max_eq_right (by linarith), max_eq_left h]; ring
    · rcases le_total 0 d with h | h
      · rw [max_eq_right (by linarith)]; ring
      · rcases eq_or_lt_of_le hs.1 with h' | h'
        · rw [h']; ring
        · rcases eq_or_lt_of_le h with h'' | h''
          · rw [h'']; simp
          · exfalso
            have := key a ⟨le_rfl, hab⟩
            nlinarith
    · rcases le_total d 0 with h | h
      · rw [max_eq_right h]; ring
      · rcases eq_or_lt_of_le hs.2 with h' | h'
        · rw [h']; ring
        · rcases eq_or_lt_of_le h with h'' | h''
          · rw [← h'']; simp
          · exfalso
            have := key b ⟨hab, le_rfl⟩
            nlinarith
  · rintro ⟨l1, l2, hl1, hl2, hsum, h1, h2⟩ t ht
    rcases lt_trichotomy t s with h | h | h
    · have hl1' : l1 = 0 := by
        rcases mul_eq_zero.mp h1 with h' | h'
        · exact h'
        · exfalso; linarith [ht.1]
      have hsl := hconc.le_slope_of_hasDerivAt ht hs h hd
      rw [slope_def_field, le_div_iff₀ (by linarith)] at hsl
      have : 0 ≤ d * (s - t) := mul_nonneg (by linarith) (by linarith)
      linarith
    · rw [h]
    · have hl2' : l2 = 0 := by
        rcases mul_eq_zero.mp h2 with h' | h'
        · exact h'
        · exfalso; linarith [ht.2]
      have hsl := hconc.slope_le_of_hasDerivAt hs ht h hd
      rw [slope_def_field, div_le_iff₀ (by linarith)] at hsl
      have : d * (t - s) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
      linarith

lemma clamp_fix {a b y g : ℝ} (hab : a ≤ b) (h : y = max a (min b (y + g))) :
    (0 < g → y = b) ∧ (g < 0 → y = a) := by
  constructor
  · intro hg
    rcases le_total b (y + g) with h1 | h1
    · rw [min_eq_left h1, max_eq_right hab] at h; exact h
    · rw [min_eq_right h1] at h
      have := le_max_right a (y + g)
      linarith
  · intro hg
    rcases le_total b (y + g) with h1 | h1
    · rw [min_eq_left h1, max_eq_right hab] at h
      linarith
    · rw [min_eq_right h1] at h
      rcases le_total a (y + g) with h2 | h2
      · rw [max_eq_right h2] at h; linarith
      · rw [max_eq_left h2] at h; exact h

end KKT

lemma deriv_theta_update (s : Fin n → ℝ) (i : Fin n) (J : Finset (Fin n)) (hi : i ∈ J) :
    deriv (fun t => theta (Function.update s i t) J i) (s i) =
      cof s i J * exp (s i) / (cof s i J + exp (s i)) ^ 2 := by
  have : (fun t => theta (Function.update s i t) J i) = fun t => exp t / (cof s i J + exp t) :=
    funext (theta_update s i J hi)
  rw [this]
  exact (hasDerivAt_term0 _ (cof_nonneg s i J) _).deriv

lemma sum_deriv_theta (s x : Fin n → ℝ) (i : Fin n) :
    (∑ J ∈ contactSets i, weight x i J * deriv (fun t => theta (Function.update s i t) J i) (s i))
      = F1 (contactSets i) (weight x i) (cof s i) (s i) := by
  unfold F1
  apply Finset.sum_congr rfl
  intro J hJ
  rw [deriv_theta_update s i J (mem_contactSets.mp hJ)]

/-- The per-HO equilibrium condition (7) is equivalent to the best response. -/
lemma br_iff_kkt (S : Setting n) (hS : Standing S) (hA : Assumption1 S) (s x : Fin n → ℝ)
    (hbox : InProfileBox S s x) (i : Fin n) :
    IsBestResponse S s x i (s i, x i) ↔
      (x i = min (S.B i / PPD S s x i) 1 ∧
        ∃ lam₁ lam₂ : ℝ, 0 ≤ lam₁ ∧ 0 ≤ lam₂ ∧
          deriv (S.δ i) (s i) / S.δ i (s i) +
            (∑ J ∈ contactSets i,
                weight x i J * deriv (fun t => theta (Function.update s i t) J i) (s i)) /
              shareSum s x i + lam₁ - lam₂ = 0 ∧
          lam₁ * (S.a i - s i) = 0 ∧ lam₂ * (s i - S.b i) = 0) := by
  have hx : ∀ j, x j ∈ Set.Icc (0 : ℝ) 1 := fun j => (hbox j).2
  rw [Fundraising.Competition.claim_S5 S hS s x hbox i, and_comm]
  apply and_congr_right
  intro _
  have hconc := Fundraising.Competition.ppd_log_concave S hS hA s x hx i
  have hd := hasDerivAt_logPPD S hS s x hx i (s i) (hS.δ_pos i (s i) (hbox i).1)
  rw [← shareSum_eq_F0, ← sum_deriv_theta] at hd
  rw [← kkt_iff_max (hS.a_le_b i) (hbox i).1 hconc hd, isMaxOn_iff]
  apply forall₂_congr
  intro t ht
  rw [Real.log_le_log_iff (PPD_pos S hS s x hx i t ht) (PPD_pos S hS s x hx i (s i) (hbox i).1)]

lemma weight_cont (i : Fin n) (J : Finset (Fin n)) : Continuous (fun x : Fin n → ℝ => weight x i J) := by
  unfold weight
  fun_prop

lemma cof_cont (i : Fin n) (J : Finset (Fin n)) : Continuous (fun s : Fin n → ℝ => cof s i J) := by
  unfold cof
  fun_prop

lemma shareSum_cont (i : Fin n) :
    Continuous (fun p : (Fin n → ℝ) × (Fin n → ℝ) => shareSum p.1 p.2 i) := by
  unfold shareSum
  apply continuous_finsetSum
  intro J _
  apply Continuous.mul ((weight_cont i J).comp continuous_snd)
  unfold theta
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro p
  have : 0 ≤ ∑ j ∈ J, exp (p.1 j) := Finset.sum_nonneg (fun j _ => (exp_pos _).le)
  linarith

lemma F1_cont (i : Fin n) :
    Continuous (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      F1 (contactSets i) (weight p.2 i) (cof p.1 i) (p.1 i)) := by
  unfold F1
  apply continuous_finsetSum
  intro J _
  apply Continuous.mul ((weight_cont i J).comp continuous_snd)
  have hc : Continuous (fun p : (Fin n → ℝ) × (Fin n → ℝ) => cof p.1 i J) :=
    (cof_cont i J).comp continuous_fst
  refine Continuous.div ?_ ?_ ?_
  · fun_prop
  · fun_prop
  intro p
  have := cof_nonneg p.1 i J
  positivity

end FRModel
end Fundraising.Competition

open FRHelp Fundraising.Competition Fundraising.Competition.FRModel in
theorem solution {n : ℕ} (S : Setting n) (hS : Standing S) (hA : Assumption1 S) :
    (∃ s x : Fin n → ℝ, IsNE S s x) ∧
    ∀ s x : Fin n → ℝ, InProfileBox S s x →
      (IsNE S s x ↔ ∀ i : Fin n,
        x i = min (S.B i / PPD S s x i) 1 ∧
        ∃ lam₁ lam₂ : ℝ, 0 ≤ lam₁ ∧ 0 ≤ lam₂ ∧
          deriv (S.δ i) (s i) / S.δ i (s i) +
            (∑ J ∈ contactSets i,
                weight x i J * deriv (fun t => theta (Function.update s i t) J i) (s i)) /
              shareSum s x i + lam₁ - lam₂ = 0 ∧
          lam₁ * (S.a i - s i) = 0 ∧ lam₂ * (s i - S.b i) = 0) := by
  have char : ∀ s x : Fin n → ℝ, InProfileBox S s x →
      (IsNE S s x ↔ ∀ i : Fin n,
        x i = min (S.B i / PPD S s x i) 1 ∧
        ∃ lam₁ lam₂ : ℝ, 0 ≤ lam₁ ∧ 0 ≤ lam₂ ∧
          deriv (S.δ i) (s i) / S.δ i (s i) +
            (∑ J ∈ contactSets i,
                weight x i J * deriv (fun t => theta (Function.update s i t) J i) (s i)) /
              shareSum s x i + lam₁ - lam₂ = 0 ∧
          lam₁ * (S.a i - s i) = 0 ∧ lam₂ * (s i - S.b i) = 0) := by
    intro s x hbox
    unfold IsNE
    constructor
    · rintro ⟨_, h⟩ i
      exact (br_iff_kkt S hS hA s x hbox i).mp (h i)
    · intro h
      exact ⟨hbox, fun i => (br_iff_kkt S hS hA s x hbox i).mpr (h i)⟩
  refine ⟨?_, char⟩
  -- Existence via Brouwer's fixed-point theorem applied to the projected-gradient map.
  let E := (Fin n → ℝ) × (Fin n → ℝ)
  let K : Set E := (Set.univ.pi fun i => Set.Icc (S.a i) (S.b i)) ×ˢ
    (Set.univ.pi fun _ => Set.Icc (0 : ℝ) 1)
  have memK : ∀ p : E, p ∈ K ↔ InProfileBox S p.1 p.2 := by
    intro p
    exact Iff.intro (fun h i => ⟨h.1 i (Set.mem_univ i), h.2 i (Set.mem_univ i)⟩)
      (fun h => ⟨fun i _ => (h i).1, fun i _ => (h i).2⟩)
  let g : Fin n → E → ℝ := fun i p =>
    deriv (S.δ i) (p.1 i) / S.δ i (p.1 i) +
      F1 (contactSets i) (weight p.2 i) (cof p.1 i) (p.1 i) / shareSum p.1 p.2 i
  let Φ : E → E := fun p =>
    (fun i => max (S.a i) (min (S.b i) (p.1 i + g i p)),
     fun i => min (S.B i / PPD S p.1 p.2 i) 1)
  have hKconv : Convex ℝ K :=
    (convex_pi (fun i _ => convex_Icc _ _)).prod (convex_pi (fun _ _ => convex_Icc _ _))
  have hKcpt : IsCompact K :=
    (isCompact_univ_pi (fun i => isCompact_Icc)).prod (isCompact_univ_pi (fun _ => isCompact_Icc))
  have hKne : K.Nonempty := ⟨(S.a, fun _ => 0), (memK _).mpr fun i =>
    ⟨⟨le_rfl, hS.a_le_b i⟩, ⟨le_rfl, zero_le_one⟩⟩⟩
  have hδc : ∀ i, Continuous (S.δ i) := fun i =>
    ((hS.δ_contDiff i).differentiable (by norm_num)).continuous
  have hδ'c : ∀ i, Continuous (deriv (S.δ i)) := fun i =>
    (hS.δ_contDiff i).continuous_deriv (by norm_num)
  have hpos_share : ∀ p ∈ K, ∀ i, 0 < shareSum p.1 p.2 i := fun p hp i =>
    shareSum_pos p.1 p.2 (fun j => ((memK p).mp hp j).2) i
  have hpos_δ : ∀ p ∈ K, ∀ i, 0 < S.δ i (p.1 i) := fun p hp i =>
    hS.δ_pos i _ ((memK p).mp hp i).1
  have hpos_PPD : ∀ p ∈ K, ∀ i, 0 < PPD S p.1 p.2 i := fun p hp i => by
    unfold PPD
    have := hpos_share p hp i
    have := hpos_δ p hp i
    have := hS.z_pos
    positivity
  have hgc : ∀ i, ContinuousOn (g i) K := by
    intro i
    have h1 : Continuous (fun p : E => p.1 i) := (continuous_apply i).comp continuous_fst
    apply ContinuousOn.add
    · exact ((hδ'c i).comp h1).continuousOn.div ((hδc i).comp h1).continuousOn
        (fun p hp => (hpos_δ p hp i).ne')
    · exact (F1_cont i).continuousOn.div (shareSum_cont i).continuousOn
        (fun p hp => (hpos_share p hp i).ne')
  have hPPDc : ∀ i, Continuous (fun p : E => PPD S p.1 p.2 i) := by
    intro i
    have h1 : Continuous (fun p : E => p.1 i) := (continuous_apply i).comp continuous_fst
    unfold PPD
    exact (((hδc i).comp h1).mul continuous_const).mul (shareSum_cont i)
  have hΦc : ContinuousOn Φ K := by
    apply ContinuousOn.prodMk
    · apply continuousOn_pi.mpr
      intro i
      have h1 : Continuous (fun p : E => p.1 i) := (continuous_apply i).comp continuous_fst
      exact (continuous_const.max (continuous_const.min continuous_id)).comp_continuousOn
        (h1.continuousOn.add (hgc i))
    · apply continuousOn_pi.mpr
      intro i
      exact (continuous_id.min continuous_const).comp_continuousOn
        (ContinuousOn.div continuousOn_const (hPPDc i).continuousOn
          (fun p hp => (hpos_PPD p hp i).ne'))
  have hΦK : Set.MapsTo Φ K K := by
    intro p hp
    rw [memK]
    intro i
    refine ⟨⟨le_max_left _ _, max_le (hS.a_le_b i) (min_le_left _ _)⟩, ⟨?_, min_le_right _ _⟩⟩
    have := hpos_PPD p hp i
    have := hS.B_pos i
    exact le_min (by positivity) zero_le_one
  obtain ⟨p, hpK, hfix⟩ := AGT.brouwer_fixed_point hKconv hKcpt hKne Φ hΦc hΦK
  have hbox := (memK p).mp hpK
  refine ⟨p.1, p.2, (char p.1 p.2 hbox).mpr ?_⟩
  intro i
  have hfix1 : p.1 i = max (S.a i) (min (S.b i) (p.1 i + g i p)) :=
    (congrFun (congrArg Prod.fst hfix) i).symm
  have hfix2 : p.2 i = min (S.B i / PPD S p.1 p.2 i) 1 :=
    (congrFun (congrArg Prod.snd hfix) i).symm
  refine ⟨hfix2, ?_⟩
  rw [sum_deriv_theta]
  have hcl := clamp_fix (hS.a_le_b i) hfix1
  set d := g i p with hd
  refine ⟨max (-d) 0, max d 0, le_max_right _ _, le_max_right _ _, ?_, ?_, ?_⟩
  · have : deriv (S.δ i) (p.1 i) / S.δ i (p.1 i) +
        F1 (contactSets i) (weight p.2 i) (cof p.1 i) (p.1 i) / shareSum p.1 p.2 i = d := rfl
    rw [this]
    rcases le_total d 0 with h | h
    · rw [max_eq_left (by linarith), max_eq_right h]; ring
    · rw [max_eq_right (by linarith), max_eq_left h]; ring
  · rcases le_or_gt 0 d with h | h
    · rw [max_eq_right (by linarith)]; ring
    · rw [hcl.2 h]; ring
  · rcases le_or_gt d 0 with h | h
    · rw [max_eq_right h]; ring
    · rw [hcl.1 h]; ring
