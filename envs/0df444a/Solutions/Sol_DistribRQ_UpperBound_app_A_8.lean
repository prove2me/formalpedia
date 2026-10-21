-- Prove2me | solution 1 for DistribRQ.UpperBound.app_A_8
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T09:49:00.288754+00:00
-- url     : https://prove2.me/submissions/12f8a577-61be-4a39-a4ab-7cc347217df9

import Mathlib
import Definitions.Def_DistribRQ_UpperBound_Model

open MeasureTheory ProbabilityTheory

namespace DistribRQSol
open DistribRQ.UpperBound

lemma integrable_cast (r : NNReal) : Integrable (fun n : ℕ => (n:ℝ)) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff]
  have hs : Summable (fun n : ℕ => Real.exp (-r) * ((2*(r:ℝ))^n / n.factorial)) :=
    (Real.summable_pow_div_factorial (2*(r:ℝ))).mul_left _
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hs
  rw [Real.norm_natCast]
  have h1 : (n:ℝ) ≤ 2^n := by exact_mod_cast (Nat.lt_two_pow_self).le
  have hr : (0:ℝ) ≤ (r:ℝ)^n := by positivity
  have he : 0 ≤ Real.exp (-r) := by positivity
  have hf : (0:ℝ) < n.factorial := by positivity
  have e : Real.exp (-r) * r^n / n.factorial * n = Real.exp (-r) * ((r:ℝ)^n * n / n.factorial) := by ring
  rw [e, mul_pow]
  apply mul_le_mul_of_nonneg_left _ he
  rw [div_le_div_iff_of_pos_right hf]
  nlinarith

lemma integrable_of_bound (r : NNReal) {f : ℕ → ℝ} (A B : ℝ) (h : ∀ n : ℕ, |f n| ≤ A + B * n) :
    Integrable f (poissonMeasure r) :=
  Integrable.mono' ((integrable_const A).add ((integrable_cast r).const_mul B))
    (Measurable.of_discrete).aestronglyMeasurable
    (Filter.Eventually.of_forall fun n => by simpa [Real.norm_eq_abs] using h n)

/-- mean -/
noncomputable def mPois (μ : ℝ) : ℝ := EPois μ (fun n => (n:ℝ))

lemma mPois_nonneg (μ : ℝ) : 0 ≤ mPois μ :=
  integral_nonneg (fun n => Nat.cast_nonneg _)

lemma EPois_abs_le (μ : ℝ) {f : ℕ → ℝ} (A B : ℝ) (h : ∀ n : ℕ, |f n| ≤ A + B * n) :
    |EPois μ f| ≤ A + B * mPois μ := by
  unfold EPois mPois
  have hi : Integrable (fun n : ℕ => A + B * (n:ℝ)) (poissonMeasure μ.toNNReal) :=
    (integrable_const A).add ((integrable_cast _).const_mul B)
  calc |∫ n, f n ∂(poissonMeasure μ.toNNReal)|
      ≤ ∫ n, (A + B * (n:ℝ)) ∂(poissonMeasure μ.toNNReal) := by
        rw [← Real.norm_eq_abs]
        exact norm_integral_le_of_norm_le hi
          (Filter.Eventually.of_forall fun n => by simpa [Real.norm_eq_abs] using h n)
    _ = A + B * ∫ n, (n:ℝ) ∂(poissonMeasure μ.toNNReal) := by
        rw [integral_add (integrable_const A) ((integrable_cast _).const_mul B), integral_const,
          integral_const_mul]
        simp

lemma integrable_comp_sub (r : NNReal) {F : ℝ → ℝ} (α β : ℝ) (hβ : 0 ≤ β)
    (hF : ∀ t, |F t| ≤ α + β * |t|) (y : ℝ) :
    Integrable (fun n : ℕ => F (y - n)) (poissonMeasure r) := by
  refine integrable_of_bound r (α + β * |y|) β (fun n => ?_)
  have h1 : |y - n| ≤ |y| + n := by
    have := abs_sub y (n:ℝ); rw [Nat.abs_cast] at this; exact this
  nlinarith [hF (y - n)]

lemma EPois_comp_sub_abs_le (μ : ℝ) {F : ℝ → ℝ} (α β : ℝ) (hβ : 0 ≤ β)
    (hF : ∀ t, |F t| ≤ α + β * |t|) (y : ℝ) :
    |EPois μ (fun n : ℕ => F (y - n))| ≤ (α + β * |y|) + β * mPois μ := by
  refine EPois_abs_le μ _ β (fun n => ?_)
  have h1 : |y - n| ≤ |y| + n := by
    have := abs_sub y (n:ℝ); rw [Nat.abs_cast] at this; exact this
  nlinarith [hF (y - n)]

lemma measurable_EPois_comp_sub (μ : ℝ) {F : ℝ → ℝ} (hF : Measurable F) :
    Measurable (fun y : ℝ => EPois μ (fun n : ℕ => F (y - n))) := by
  unfold EPois
  have : StronglyMeasurable (fun p : ℝ × ℕ => F (p.1 - p.2)) := by
    apply Measurable.stronglyMeasurable
    exact hF.comp (measurable_fst.sub (measurable_from_nat.comp measurable_snd))
  exact (this.integral_prod_right' (ν := poissonMeasure μ.toNNReal)).measurable

lemma intervalIntegrable_EPois_comp_sub (μ : ℝ) {F : ℝ → ℝ} (hF : Measurable F) (α β : ℝ)
    (hβ : 0 ≤ β) (hb : ∀ t, |F t| ≤ α + β * |t|) (a b : ℝ) :
    IntervalIntegrable (fun y : ℝ => EPois μ (fun n : ℕ => F (y - n))) volume a b := by
  have hg : IntervalIntegrable (fun y : ℝ => (α + β * |y|) + β * mPois μ) volume a b :=
    (by fun_prop : Continuous (fun y : ℝ => (α + β * |y|) + β * mPois μ)).intervalIntegrable a b
  refine hg.mono_fun' (measurable_EPois_comp_sub μ hF).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  simpa [Real.norm_eq_abs] using EPois_comp_sub_abs_le μ α β hβ hb y

lemma EPois_add (μ : ℝ) {f g : ℕ → ℝ} (hf : Integrable f (poissonMeasure μ.toNNReal))
    (hg : Integrable g (poissonMeasure μ.toNNReal)) :
    EPois μ (fun n => f n + g n) = EPois μ f + EPois μ g := integral_add hf hg

lemma EPois_const (μ : ℝ) (c : ℝ) : EPois μ (fun _ => c) = c := by
  unfold EPois; simp

lemma EPois_mono (μ : ℝ) {f g : ℕ → ℝ} (hf : Integrable f (poissonMeasure μ.toNNReal))
    (hg : Integrable g (poissonMeasure μ.toNNReal)) (h : ∀ n, f n ≤ g n) :
    EPois μ f ≤ EPois μ g := integral_mono hf hg h

/-! ## Facts about `G` -/

variable {N : ℕ} (P : Primitives N) (π : Policy N)

/-- the integrand of `G`, as a function of `y - n` -/
noncomputable def phi (i : Fin N) (t : ℝ) : ℝ :=
  P.h i * max t 0 + (P.h0 + P.p i) * max (-t) 0

lemma G_eq (i : Fin N) (y : ℝ) : G P i y = EPois (P.lam i * P.L i) (fun n : ℕ => phi P i (y - n)) :=
  rfl

lemma phi_nonneg (i : Fin N) (t : ℝ) : 0 ≤ phi P i t := by
  unfold phi
  have := P.h_pos i; have := P.h0_pos; have := P.p_pos i
  have : 0 ≤ max t 0 := le_max_right _ _
  have : 0 ≤ max (-t) 0 := le_max_right _ _
  positivity

lemma phi_bound (i : Fin N) (t : ℝ) : |phi P i t| ≤ 0 + (P.h i + (P.h0 + P.p i)) * |t| := by
  rw [abs_of_nonneg (phi_nonneg P i t)]
  unfold phi
  have := P.h_pos i; have := P.h0_pos; have := P.p_pos i
  have h1 : max t 0 ≤ |t| := max_le (le_abs_self t) (abs_nonneg t)
  have h2 : max (-t) 0 ≤ |t| := max_le (neg_le_abs t) (abs_nonneg t)
  nlinarith

lemma phi_meas (i : Fin N) : Measurable (phi P i) := by
  unfold phi; fun_prop

lemma phi_convex (i : Fin N) : ConvexOn ℝ Set.univ (phi P i) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  unfold phi
  have := P.h_pos i; have := P.h0_pos; have := P.p_pos i
  have e1 : max (a * x + b * y) 0 ≤ a * max x 0 + b * max y 0 := by
    apply max_le
    · nlinarith [le_max_left x 0, le_max_left y 0]
    · nlinarith [le_max_right x 0, le_max_right y 0]
  have e2 : max (-(a * x + b * y)) 0 ≤ a * max (-x) 0 + b * max (-y) 0 := by
    apply max_le
    · nlinarith [le_max_left (-x) 0, le_max_left (-y) 0]
    · nlinarith [le_max_right (-x) 0, le_max_right (-y) 0]
  nlinarith

lemma G_convex (i : Fin N) : ConvexOn ℝ Set.univ (G P i) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  have hb' : 0 ≤ P.h i + (P.h0 + P.p i) := by
    have := P.h_pos i; have := P.h0_pos; have := P.p_pos i; linarith
  have I : ∀ y, Integrable (fun n : ℕ => phi P i (y - n))
      (poissonMeasure (P.lam i * P.L i).toNNReal) :=
    integrable_comp_sub _ 0 _ hb' (phi_bound P i)
  rw [G_eq, G_eq, G_eq]
  unfold EPois
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add ((I x).const_mul a)
    ((I y).const_mul b)]
  apply integral_mono (I _) (((I x).const_mul a).add ((I y).const_mul b))
  intro n
  have := (phi_convex P i).2 (Set.mem_univ (x - n)) (Set.mem_univ (y - n)) ha hb hab
  simp only [smul_eq_mul] at this
  have e : a * x + b * y - n = a * (x - n) + b * (y - n) := by
    have : (n:ℝ) = a * n + b * n := by rw [← add_mul, hab, one_mul]
    linarith
  simp only [Pi.add_apply]
  rw [e]; exact this

lemma G_nonneg (i : Fin N) (y : ℝ) : 0 ≤ G P i y := by
  rw [G_eq]; exact integral_nonneg (fun n => phi_nonneg P i _)

lemma G_bound (i : Fin N) : ∃ α β : ℝ, 0 ≤ β ∧ ∀ t, |G P i t| ≤ α + β * |t| := by
  have hb' : 0 ≤ P.h i + (P.h0 + P.p i) := by
    have := P.h_pos i; have := P.h0_pos; have := P.p_pos i; linarith
  refine ⟨(P.h i + (P.h0 + P.p i)) * mPois (P.lam i * P.L i), P.h i + (P.h0 + P.p i), hb',
    fun t => ?_⟩
  rw [G_eq]
  have := EPois_comp_sub_abs_le (P.lam i * P.L i) 0 _ hb' (phi_bound P i) t
  linarith

lemma G_meas (i : Fin N) : Measurable (G P i) := by
  have : G P i = fun y => EPois (P.lam i * P.L i) (fun n : ℕ => phi P i (y - n)) := rfl
  rw [this]; exact measurable_EPois_comp_sub _ (phi_meas P i)

lemma G_le_max (i : Fin N) {t : ℝ} (ht : t ∈ Set.Icc (π.r i) (π.r i + π.Q i)) :
    G P i t ≤ max (G P i (π.r i)) (G P i (π.r i + π.Q i)) := by
  apply (G_convex P i).le_on_segment (Set.mem_univ _) (Set.mem_univ _)
  rw [segment_eq_Icc (by linarith [π.Q_pos i])]; exact ht

lemma G_bdd (i : Fin N) : BddAbove (G P i '' Set.Ioc (π.r i) (π.r i + π.Q i)) := by
  refine ⟨max (G P i (π.r i)) (G P i (π.r i + π.Q i)), ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  exact G_le_max P π i ⟨ht.1.le, ht.2⟩

lemma G_le_Gw (i : Fin N) {t : ℝ} (ht : t ∈ Set.Ioc (π.r i) (π.r i + π.Q i)) :
    G P i t ≤ Gw P π i :=
  le_csSup (G_bdd P π i) (Set.mem_image_of_mem _ ht)

lemma G_top_le_Gw (i : Fin N) : G P i (π.r i + π.Q i) ≤ Gw P π i :=
  G_le_Gw P π i ⟨by linarith [π.Q_pos i], le_rfl⟩

/-! ## Lemma 3 -/

lemma feasible_sum_eq {x : ℝ} {z : Fin N → ℝ} (hz : z ∈ Feasible π x) {i : Fin N}
    (hi : z i ≤ π.r i) : ∑ j, z j = x := by
  rcases hz with ⟨_, h2, h3⟩
  by_contra hne
  have := h3 (lt_of_le_of_ne h2 hne) i
  linarith

lemma sum_erase_le_S {x : ℝ} {z : Fin N → ℝ} (hz : z ∈ Feasible π x) (i : Fin N) :
    ∑ j ∈ Finset.univ.erase i, z j ≤ S π i := by
  unfold S
  exact Finset.sum_le_sum (fun j _ => hz.1 j)

lemma M_le_GBO (i : Fin N) (x : ℝ) : max (Gw P π i) (Ccost P π i) ≤ GammaBarOwn P π i x := by
  unfold GammaBarOwn
  split_ifs
  · exact le_rfl
  · exact le_max_right _ _

lemma c_le_M (c : Fin N → ℝ → ℝ) (hc : AdmissibleCharge P π c) {x : ℝ} {z : Fin N → ℝ}
    (hz : z ∈ Feasible π x) {j : Fin N} (hj : π.r j < z j) :
    c j (z j) ≤ max (Gw P π j) (Ccost P π j) := by
  have := hc.1 j (z j) hj
  have h2 := G_le_Gw P π j ⟨hj, hz.1 j⟩
  calc c j (z j) ≤ max (G P j (z j)) (Ccost P π j) := this
    _ ≤ max (Gw P π j) (Ccost P π j) := max_le_max h2 le_rfl

theorem app_A_3' (c : Fin N → ℝ → ℝ) (hc : AdmissibleCharge P π c) (x : ℝ) (z : Fin N → ℝ)
    (hz : z ∈ Feasible π x) (i : Fin N) : c i (z i) ≤ GammaBarOwn P π i x := by
  by_cases hi : π.r i < z i
  · exact (c_le_M P π c hc hz hi).trans (M_le_GBO P π i x)
  push Not at hi
  have hsum := feasible_sum_eq π hz hi
  have hS := sum_erase_le_S π hz i
  have hsplit := Finset.add_sum_erase Finset.univ z (Finset.mem_univ i)
  have hlow : x - S π i ≤ z i := by linarith
  have hnot : ¬ (x - S π i > π.r i) := by linarith
  unfold GammaBarOwn
  rw [if_neg hnot]
  have hb : π.r i < π.r i + π.Q i := by linarith [π.Q_pos i]
  have hseg : G P i (z i) ≤ max (G P i (x - S π i)) (G P i (π.r i + π.Q i)) := by
    apply (G_convex P i).le_on_segment (Set.mem_univ _) (Set.mem_univ _)
    rw [segment_eq_Icc (by linarith)]; exact ⟨hlow, by linarith⟩
  have := hc.2 i (z i) hi
  have := G_top_le_Gw P π i
  calc c i (z i) ≤ G P i (z i) := by assumption
    _ ≤ max (G P i (x - S π i)) (G P i (π.r i + π.Q i)) := hseg
    _ ≤ max (G P i (x - S π i)) (max (Gw P π i) (Ccost P π i)) :=
        max_le_max le_rfl (le_trans (by assumption) (le_max_left _ _))

theorem lemma_3' [NeZero N] (c : Fin N → ℝ → ℝ) (hc : AdmissibleCharge P π c) (x : ℝ)
    (z : Fin N → ℝ) (hz : z ∈ Feasible π x) : ∑ i, c i (z i) ≤ GammaBar P π x := by
  classical
  set M : Fin N → ℝ := fun j => max (Gw P π j) (Ccost P π j) with hM
  by_cases hall : ∀ j, π.r j < z j
  · -- no deficit retailer
    have i0 : Fin N := 0
    calc ∑ i, c i (z i) ≤ ∑ i, M i := Finset.sum_le_sum (fun j _ => c_le_M P π c hc hz (hall j))
      _ = ∑ j ∈ Finset.univ.erase 0, M j + M 0 := (Finset.sum_erase_add _ _ (Finset.mem_univ 0)).symm
      _ ≤ GammaBarI P π 0 x := by
          unfold GammaBarI; exact add_le_add le_rfl (M_le_GBO P π 0 x)
      _ ≤ GammaBar P π x := Finset.le_sup' (fun i => GammaBarI P π i x) (Finset.mem_univ 0)
  push Not at hall
  set D := Finset.univ.filter (fun j => z j ≤ π.r j) with hD
  have hDne : D.Nonempty := by
    obtain ⟨j, hj⟩ := hall; exact ⟨j, by simp [hD, hj]⟩
  set b : Fin N → ℝ := fun j => π.r j + π.Q j with hb
  set σ : Fin N → ℝ := fun j => (G P j (z j) - G P j (b j)) / (b j - z j) with hσ
  obtain ⟨i, hiD, hmax⟩ := Finset.exists_max_image D σ hDne
  have hi : z i ≤ π.r i := (Finset.mem_filter.1 hiD).2
  have hsum := feasible_sum_eq π hz hi
  have hsplit := Finset.add_sum_erase Finset.univ z (Finset.mem_univ i)
  set Ds := ∑ j ∈ Finset.univ.erase i, (b j - z j) with hDs
  have hDs_eq : Ds = S π i - ∑ j ∈ Finset.univ.erase i, z j := by
    rw [hDs, Finset.sum_sub_distrib]; rfl
  have hDs_nonneg : 0 ≤ Ds := Finset.sum_nonneg (fun j _ => by
    have := hz.1 j; simp only [hb]; linarith)
  have hxS : x - S π i = z i - Ds := by linarith
  -- key identity for deficit retailers
  have hGid : ∀ j, z j ≤ π.r j → G P j (z j) = G P j (b j) + σ j * (b j - z j) := by
    intro j hj
    have : 0 < b j - z j := by simp only [hb]; linarith [π.Q_pos j]
    simp only [hσ]; field_simp; ring
  set s := max (σ i) 0 with hs
  -- bound on the other retailers
  have hother : ∀ j, c j (z j) ≤ M j + s * (b j - z j) := by
    intro j
    have hd : 0 ≤ b j - z j := by have := hz.1 j; simp only [hb]; linarith
    by_cases hj : π.r j < z j
    · have := c_le_M P π c hc hz hj
      have : 0 ≤ s * (b j - z j) := mul_nonneg (le_max_right _ _) hd
      simp only [hM]; linarith
    · push Not at hj
      have h1 := hc.2 j (z j) hj
      have h2 := hGid j hj
      have h3 : G P j (b j) ≤ M j := (G_top_le_Gw P π j).trans (le_max_left _ _)
      have h4 : σ j ≤ σ i := hmax j (by simp [hD, hj])
      have h5 : σ j * (b j - z j) ≤ s * (b j - z j) :=
        mul_le_mul_of_nonneg_right (h4.trans (le_max_left _ _)) hd
      linarith
  have hsum_other : ∑ j ∈ Finset.univ.erase i, c j (z j) ≤
      ∑ j ∈ Finset.univ.erase i, M j + s * Ds := by
    rw [hDs, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun j _ => hother j)
  -- bound on retailer i
  have hnot : ¬ (x - S π i > π.r i) := by
    have := hDs_nonneg; rw [hxS]; push Not; linarith
  have hown : c i (z i) + s * Ds ≤ GammaBarOwn P π i x := by
    unfold GammaBarOwn
    rw [if_neg hnot, hxS]
    have h1 := hc.2 i (z i) hi
    have h2 := hGid i hi
    have h3 : G P i (b i) ≤ M i := (G_top_le_Gw P π i).trans (le_max_left _ _)
    have hdi : 0 < b i - z i := by simp only [hb]; linarith [π.Q_pos i]
    by_cases hσi : σ i ≤ 0
    · have : s = 0 := by simp only [hs]; exact max_eq_right hσi
      rw [this, zero_mul, add_zero]
      have : σ i * (b i - z i) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hσi hdi.le
      refine le_trans ?_ (le_max_right _ _)
      simp only [hM] at h3 ⊢; linarith
    · push Not at hσi
      have : s = σ i := by simp only [hs]; exact max_eq_left hσi.le
      rw [this]
      refine le_trans ?_ (le_max_left _ _)
      rcases hDs_nonneg.lt_or_eq with hpos | hzero
      · have hsl := (G_convex P i).slope_mono_adjacent (Set.mem_univ (z i - Ds))
          (Set.mem_univ (b i)) (by linarith : z i - Ds < z i) (by linarith : z i < b i)
        have e1 : z i - (z i - Ds) = Ds := by ring
        have e2 : (G P i (b i) - G P i (z i)) / (b i - z i) = -σ i := by
          rw [show G P i (b i) - G P i (z i) = -σ i * (b i - z i) by linarith, mul_div_assoc,
            div_self hdi.ne', mul_one]
        rw [e1, e2, div_le_iff₀ hpos] at hsl
        linarith
      · rw [← hzero]; simp; linarith
  calc ∑ i, c i (z i) = c i (z i) + ∑ j ∈ Finset.univ.erase i, c j (z j) :=
        (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
    _ ≤ GammaBarOwn P π i x + ∑ j ∈ Finset.univ.erase i, M j := by linarith
    _ = GammaBarI P π i x := by unfold GammaBarI; ring
    _ ≤ GammaBar P π x := Finset.le_sup' (fun i => GammaBarI P π i x) (Finset.mem_univ i)


/-! ## Bounds and measurability of `Γ̄`, `Ĝ` -/

lemma GBO_bound (i : Fin N) : ∃ α β : ℝ, 0 ≤ β ∧ ∀ x, |GammaBarOwn P π i x| ≤ α + β * |x| := by
  obtain ⟨α, β, hβ, hG⟩ := G_bound P i
  refine ⟨|max (Gw P π i) (Ccost P π i)| + α + β * |S π i|, β, hβ, fun x => ?_⟩
  have h0 : |x - S π i| ≤ |x| + |S π i| := abs_sub _ _
  have h1 : |G P i (x - S π i)| ≤ α + β * (|x| + |S π i|) :=
    (hG _).trans (by gcongr)
  have h2 := abs_nonneg (G P i (x - S π i))
  unfold GammaBarOwn
  split_ifs
  · nlinarith
  · have := abs_max_le_max_abs_abs (a := G P i (x - S π i)) (b := max (Gw P π i) (Ccost P π i))
    have := max_le_add_of_nonneg (abs_nonneg (G P i (x - S π i)))
      (abs_nonneg (max (Gw P π i) (Ccost P π i)))
    nlinarith

lemma GB_bound [NeZero N] : ∃ α β : ℝ, 0 ≤ β ∧ ∀ x, |GammaBar P π x| ≤ α + β * |x| := by
  choose α β hβ hb using fun i => GBO_bound P π i
  set K : Fin N → ℝ := fun i => |∑ j ∈ Finset.univ.erase i, max (Gw P π j) (Ccost P π j)|
  refine ⟨∑ i, (K i + α i), ∑ i, β i, Finset.sum_nonneg (fun i _ => hβ i), fun x => ?_⟩
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun i => GammaBarI P π i x)
  unfold GammaBar; rw [hi]
  calc |GammaBarI P π i x| ≤ ∑ k, |GammaBarI P π k x| :=
        Finset.single_le_sum (f := fun k => |GammaBarI P π k x|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ i)
    _ ≤ ∑ k, ((K k + α k) + β k * |x|) := Finset.sum_le_sum (fun k _ => by
        unfold GammaBarI
        have := hb k x
        have := abs_add_le (∑ j ∈ Finset.univ.erase k, max (Gw P π j) (Ccost P π j))
          (GammaBarOwn P π k x)
        simp only [K]; linarith)
    _ = ∑ i, (K i + α i) + (∑ i, β i) * |x| := by
        rw [Finset.sum_add_distrib, Finset.sum_mul]

lemma Ghat_bound [NeZero N] : ∃ α β : ℝ, 0 ≤ β ∧ ∀ x, |Ghat P π x| ≤ α + β * |x| := by
  obtain ⟨α, β, hβ, h⟩ := GB_bound P π
  refine ⟨α + |∑ i, Ccost P π i|, β, hβ, fun x => ?_⟩
  unfold Ghat
  have := abs_sub (GammaBar P π x) (∑ i, Ccost P π i)
  linarith [h x]

lemma GBO_meas (i : Fin N) : Measurable (GammaBarOwn P π i) := by
  have : GammaBarOwn P π i = fun x => if π.r i < x - S π i then max (Gw P π i) (Ccost P π i)
      else max (G P i (x - S π i)) (max (Gw P π i) (Ccost P π i)) := rfl
  rw [this]
  exact Measurable.ite (measurableSet_lt measurable_const (measurable_id.sub_const _))
    measurable_const (((G_meas P i).comp (measurable_id.sub_const _)).max measurable_const)

lemma GB_meas [NeZero N] : Measurable (GammaBar P π) := by
  have : GammaBar P π = Finset.univ.sup' Finset.univ_nonempty (fun i => GammaBarI P π i) := by
    funext x; rw [Finset.sup'_apply]; rfl
  rw [this]
  exact Finset.measurable_sup' _ (fun i _ => measurable_const.add (GBO_meas P π i))

lemma Ghat_meas [NeZero N] : Measurable (Ghat P π) :=
  (GB_meas P π).sub_const _

/-! ## (8), (9), (10) -/

lemma GammaHat_nonneg (κ : Kernel ℝ (Fin N → ℝ)) (c : Fin N → ℝ → ℝ)
    (hc_nonneg : ∀ i z, 0 ≤ c i z) (x : ℝ) : 0 ≤ GammaHat κ c x :=
  integral_nonneg (fun z => Finset.sum_nonneg (fun i _ => hc_nonneg i _))

lemma GammaHat_meas (κ : Kernel ℝ (Fin N → ℝ)) (c : Fin N → ℝ → ℝ)
    (hc_meas : ∀ i, Measurable (c i)) : Measurable (GammaHat κ c) := by
  have hf : StronglyMeasurable (fun z : Fin N → ℝ => ∑ i, c i (z i)) :=
    (Finset.measurable_sum _ (fun i _ => (hc_meas i).comp (measurable_pi_apply i))).stronglyMeasurable
  exact (hf.integral_kernel (κ := κ)).measurable

theorem app_A_8' [NeZero N] (κ : Kernel ℝ (Fin N → ℝ)) [IsMarkovKernel κ]
    (hκ : ∀ x, κ x (Feasible π x)ᶜ = 0) (c : Fin N → ℝ → ℝ) (hc : AdmissibleCharge P π c)
    (hc_nonneg : ∀ i z, 0 ≤ c i z) (x : ℝ) :
    GammaHat κ c x ≤ GammaBar P π x ∧ GammaBar P π x = Ghat P π x + ∑ i, Ccost P π i := by
  refine ⟨?_, by unfold Ghat; ring⟩
  have hae : ∀ᵐ z ∂(κ x), z ∈ Feasible π x := ae_iff.2 (hκ x)
  unfold GammaHat
  calc ∫ z, ∑ i, c i (z i) ∂(κ x) ≤ ∫ _z, GammaBar P π x ∂(κ x) :=
        integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun z => Finset.sum_nonneg (fun i _ => hc_nonneg i _))
          (integrable_const _) (hae.mono fun z hz => lemma_3' P π c hc x z hz)
    _ = GammaBar P π x := by simp

lemma GammaHat_bound [NeZero N] (κ : Kernel ℝ (Fin N → ℝ)) [IsMarkovKernel κ]
    (hκ : ∀ x, κ x (Feasible π x)ᶜ = 0) (c : Fin N → ℝ → ℝ) (hc : AdmissibleCharge P π c)
    (hc_nonneg : ∀ i z, 0 ≤ c i z) :
    ∃ α β : ℝ, 0 ≤ β ∧ ∀ x, |GammaHat κ c x| ≤ α + β * |x| := by
  obtain ⟨α, β, hβ, h⟩ := GB_bound P π
  refine ⟨α, β, hβ, fun x => ?_⟩
  have h1 := GammaHat_nonneg κ c hc_nonneg x
  have h2 := (app_A_8' P π κ hκ c hc hc_nonneg x).1
  rw [abs_of_nonneg h1]
  exact h2.trans ((le_abs_self _).trans (h x))

lemma lin_bound (a : ℝ) (ha : 0 ≤ a) : ∀ t : ℝ, |a * t| ≤ 0 + a * |t| := by
  intro t; rw [abs_mul, abs_of_nonneg ha]; simp

lemma F_bound [NeZero N] : ∃ α β : ℝ, 0 ≤ β ∧ ∀ t, |P.h0 * t + Ghat P π t| ≤ α + β * |t| := by
  obtain ⟨α, β, hβ, h⟩ := Ghat_bound P π
  refine ⟨α, P.h0 + β, by linarith [P.h0_pos], fun t => ?_⟩
  have := abs_add_le (P.h0 * t) (Ghat P π t)
  have := lin_bound P.h0 P.h0_pos.le t
  linarith [h t]

theorem app_A_9' [NeZero N] (κ : Kernel ℝ (Fin N → ℝ)) [IsMarkovKernel κ]
    (hκ : ∀ x, κ x (Feasible π x)ᶜ = 0) (c : Fin N → ℝ → ℝ) (hc : AdmissibleCharge P π c)
    (hc_nonneg : ∀ i z, 0 ≤ c i z) (y : ℝ) :
    Gamma0 P κ c y ≤ Lambda0 P π y + ∑ i, Ccost P π i := by
  set μ := lam0 P * P.L0
  obtain ⟨α, β, hβ, hb⟩ := Ghat_bound P π
  obtain ⟨α', β', hβ', hb'⟩ := GB_bound P π
  have I1 : Integrable (fun n : ℕ => P.h0 * (y - n)) (poissonMeasure μ.toNNReal) :=
    integrable_comp_sub _ 0 P.h0 P.h0_pos.le (lin_bound P.h0 P.h0_pos.le) y
  have I2 : Integrable (fun n : ℕ => Ghat P π (y - n)) (poissonMeasure μ.toNNReal) :=
    integrable_comp_sub _ α β hβ hb y
  have I3 : Integrable (fun n : ℕ => GammaBar P π (y - n)) (poissonMeasure μ.toNNReal) :=
    integrable_comp_sub _ α' β' hβ' hb' y
  have hL : Lambda0 P π y = EPois μ (fun n : ℕ => P.h0 * (y - n)) +
      EPois μ (fun n : ℕ => Ghat P π (y - n)) := EPois_add μ I1 I2
  have hGB : EPois μ (fun n : ℕ => GammaBar P π (y - n)) =
      EPois μ (fun n : ℕ => Ghat P π (y - n)) + ∑ i, Ccost P π i := by
    rw [← EPois_const μ (∑ i, Ccost P π i), ← EPois_add μ I2 (integrable_const _)]
    congr 1; funext n; unfold Ghat; ring
  have hmono : EPois μ (fun n : ℕ => GammaHat κ c (y - n)) ≤
      EPois μ (fun n : ℕ => GammaBar P π (y - n)) :=
    integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun n => GammaHat_nonneg κ c hc_nonneg _) I3
      (Filter.Eventually.of_forall fun n => (app_A_8' P π κ hκ c hc hc_nonneg _).1)
  unfold Gamma0
  rw [hL]
  linarith

lemma Gamma0_int [NeZero N] (κ : Kernel ℝ (Fin N → ℝ)) [IsMarkovKernel κ]
    (hκ : ∀ x, κ x (Feasible π x)ᶜ = 0) (c : Fin N → ℝ → ℝ) (hc : AdmissibleCharge P π c)
    (hc_meas : ∀ i, Measurable (c i)) (hc_nonneg : ∀ i z, 0 ≤ c i z) (a b : ℝ) :
    IntervalIntegrable (Gamma0 P κ c) volume a b := by
  obtain ⟨α, β, hβ, hb⟩ := GammaHat_bound P π κ hκ c hc hc_nonneg
  have h1 := intervalIntegrable_EPois_comp_sub (lam0 P * P.L0) (F := fun t => P.h0 * t)
    (measurable_const.mul measurable_id) 0 P.h0 P.h0_pos.le (lin_bound P.h0 P.h0_pos.le) a b
  have h2 := intervalIntegrable_EPois_comp_sub (lam0 P * P.L0) (GammaHat_meas κ c hc_meas)
    α β hβ hb a b
  exact h1.add h2

lemma Lambda0_int [NeZero N] (a b : ℝ) : IntervalIntegrable (Lambda0 P π) volume a b := by
  obtain ⟨α, β, hβ, hb⟩ := F_bound P π
  exact intervalIntegrable_EPois_comp_sub (lam0 P * P.L0) (F := fun t => P.h0 * t + Ghat P π t)
    ((measurable_const.mul measurable_id).add (Ghat_meas P π)) α β hβ hb a b

theorem app_A_10' [NeZero N] (κ : Kernel ℝ (Fin N → ℝ)) [IsMarkovKernel κ]
    (hκ : ∀ x, κ x (Feasible π x)ᶜ = 0) (c : Fin N → ℝ → ℝ) (hc : AdmissibleCharge P π c)
    (hc_meas : ∀ i, Measurable (c i)) (hc_nonneg : ∀ i z, 0 ≤ c i z) :
    (lam0 P * P.K0 + ∫ y in π.r0..π.r0 + π.Q0, Gamma0 P κ c y) / π.Q0 ≤
      C0hat P π + ∑ i, Ccost P π i := by
  have hQ := π.Q0_pos
  have hmono : ∫ y in π.r0..π.r0 + π.Q0, Gamma0 P κ c y ≤
      ∫ y in π.r0..π.r0 + π.Q0, (Lambda0 P π y + ∑ i, Ccost P π i) :=
    intervalIntegral.integral_mono_on (by linarith)
      (Gamma0_int P π κ hκ c hc hc_meas hc_nonneg _ _)
      ((Lambda0_int P π _ _).add intervalIntegrable_const)
      (fun y _ => app_A_9' P π κ hκ c hc hc_nonneg y)
  rw [intervalIntegral.integral_add (Lambda0_int P π _ _) intervalIntegrable_const,
    intervalIntegral.integral_const, smul_eq_mul,
    show π.r0 + π.Q0 - π.r0 = π.Q0 by ring] at hmono
  unfold C0hat
  rw [div_add' _ _ _ hQ.ne', div_le_div_iff_of_pos_right hQ]
  linarith

theorem theorem_1' [NeZero N] (κ : Kernel ℝ (Fin N → ℝ)) [IsMarkovKernel κ]
    (hκ : ∀ x, κ x (Feasible π x)ᶜ = 0) (c : Fin N → ℝ → ℝ) (hc : AdmissibleCharge P π c)
    (hc_meas : ∀ i, Measurable (c i)) (hc_nonneg : ∀ i z, 0 ≤ c i z) (Omega : ℝ → ℝ)
    (hOmega_int : IntervalIntegrable Omega volume π.r0 (π.r0 + π.Q0))
    (hOmega : ∀ y, Omega y ≤ lam0 P * Kbar P / π.Q0 +
      EPois (lam0 P * P.L0) (fun n => GammaHat κ c (y - n))) :
    Csys P π Omega ≤ CU P π := by
  have hQ := π.Q0_pos
  set μ := lam0 P * P.L0
  set k := lam0 P * Kbar P / π.Q0 with hk
  have hkQ : k * π.Q0 = lam0 P * Kbar P := by rw [hk]; field_simp
  have I1 : ∀ y : ℝ, Integrable (fun n : ℕ => P.h0 * (y - n)) (poissonMeasure μ.toNNReal) :=
    integrable_comp_sub _ 0 P.h0 P.h0_pos.le (lin_bound P.h0 P.h0_pos.le)
  have hE1 := intervalIntegrable_EPois_comp_sub μ (F := fun t => P.h0 * t)
    (measurable_const.mul measurable_id) 0 P.h0 P.h0_pos.le (lin_bound P.h0 P.h0_pos.le)
    π.r0 (π.r0 + π.Q0)
  have hfun : (fun y : ℝ => EPois μ (fun n : ℕ => P.h0 * (y - n) + Omega y)) =
      fun y => EPois μ (fun n : ℕ => P.h0 * (y - n)) + Omega y := by
    funext y
    rw [EPois_add μ (I1 y) (integrable_const _), EPois_const]
  have hle : ∫ y in π.r0..π.r0 + π.Q0, EPois μ (fun n : ℕ => P.h0 * (y - n) + Omega y) ≤
      ∫ y in π.r0..π.r0 + π.Q0, (Lambda0 P π y + (∑ i, Ccost P π i + k)) := by
    rw [hfun]
    refine intervalIntegral.integral_mono_on (by linarith) (hE1.add hOmega_int)
      ((Lambda0_int P π _ _).add intervalIntegrable_const) (fun y _ => ?_)
    have h9 := app_A_9' P π κ hκ c hc hc_nonneg y
    have h1 := hOmega y
    unfold Gamma0 at h9
    linarith
  rw [intervalIntegral.integral_add (Lambda0_int P π _ _) intervalIntegrable_const,
    intervalIntegral.integral_const, smul_eq_mul,
    show π.r0 + π.Q0 - π.r0 = π.Q0 by ring] at hle
  unfold Csys CU C0hat
  rw [div_le_iff₀ hQ, add_mul, add_mul, div_mul_cancel₀ _ hQ.ne', div_mul_cancel₀ _ hQ.ne']
  nlinarith

end DistribRQSol

open DistribRQ.UpperBound

theorem solution {N : ℕ} [NeZero N] (P : Primitives N) (π : Policy N) (κ : Kernel ℝ (Fin N → ℝ)) [IsMarkovKernel κ] (hκ : ∀ x, κ x (Feasible π x)ᶜ = 0) (c : Fin N → ℝ → ℝ) (hc : AdmissibleCharge P π c) (hc_meas : ∀ i, Measurable (c i)) (hc_nonneg : ∀ i z, 0 ≤ c i z) (x : ℝ) : GammaHat κ c x ≤ GammaBar P π x ∧ GammaBar P π x = Ghat P π x + ∑ i, Ccost P π i :=
  DistribRQSol.app_A_8' P π κ hκ c hc hc_nonneg x
