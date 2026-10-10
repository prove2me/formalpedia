-- Prove2me | solution 2 for BayesRouting.VOI.relative_value_sign_and_monotone
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-10T01:03:17.973056+00:00
-- url     : https://prove2.me/submissions/d1693f9d-6a03-4537-8c7c-669252296526

import Mathlib
import Definitions.Def_BayesRouting_VOI_Game
import Definitions.Def_BayesRouting_VOI_Potential
import Definitions.Def_BayesRouting_VOI_Flows
import Definitions.Def_BayesRouting_VOI_Pairwise

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Filter Topology

/-! ### Scalar facts about `x ↦ ∫_0^x c` -/

lemma vsi_support {c : ℝ → ℝ} (hc : Monotone c) (hcc : Continuous c) (x y : ℝ) :
    c x * (y - x) ≤ (∫ z in (0:ℝ)..y, c z) - ∫ z in (0:ℝ)..x, c z := by
  rw [intervalIntegral.integral_interval_sub_left
    (hcc.intervalIntegrable (μ := MeasureTheory.volume) _ _)
    (hcc.intervalIntegrable (μ := MeasureTheory.volume) _ _)]
  rcases le_total x y with hxy | hxy
  · have := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hxy (continuous_const.intervalIntegrable x y)
      (hcc.intervalIntegrable x y) (fun z hz => hc hz.1)
    simp only [intervalIntegral.integral_const, smul_eq_mul] at this
    linarith
  · rw [intervalIntegral.integral_symm]
    have := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hxy (hcc.intervalIntegrable y x)
      (continuous_const.intervalIntegrable y x) (fun z hz => hc hz.2)
    simp only [intervalIntegral.integral_const, smul_eq_mul] at this
    nlinarith

lemma vsi_nonneg {c : ℝ → ℝ} (hpos : ∀ z, 0 ≤ z → 0 < c z) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ ∫ z in (0:ℝ)..x, c z :=
  intervalIntegral.integral_nonneg hx (fun u hu => (hpos u hu.1).le)

lemma vsi_convex {c : ℝ → ℝ} (hc : Monotone c) (hcc : Continuous c) (x y a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (∫ z in (0:ℝ)..(a * x + b * y), c z) ≤
      a * (∫ z in (0:ℝ)..x, c z) + b * ∫ z in (0:ℝ)..y, c z := by
  have h1 := vsi_support hc hcc (a * x + b * y) x
  have h2 := vsi_support hc hcc (a * x + b * y) y
  have h3 : a * (c (a * x + b * y) * (x - (a * x + b * y))) +
      b * (c (a * x + b * y) * (y - (a * x + b * y))) = 0 := by
    have : b = 1 - a := by linarith
    subst this; ring
  have h4 := mul_le_mul_of_nonneg_left h1 ha
  have h5 := mul_le_mul_of_nonneg_left h2 hb
  set m := ∫ z in (0:ℝ)..(a * x + b * y), c z
  have h6 : a * m + b * m = m := by rw [← add_mul, hab, one_mul]
  nlinarith

/-- Upper bound used for the Lipschitz estimate. -/
lemma vsi_up {c : ℝ → ℝ} (hc : Monotone c) (hcc : Continuous c) (hpos : ∀ z, 0 ≤ z → 0 < c z)
    {w w' Δ M : ℝ} (hw : 0 ≤ w) (hle : w ≤ w' + Δ) (hΔ : 0 ≤ Δ) (hM : w' + Δ ≤ M) :
    (∫ z in (0:ℝ)..w, c z) ≤ (∫ z in (0:ℝ)..w', c z) + c M * Δ := by
  have h := vsi_support hc hcc w w'
  have hcw : 0 < c w := hpos w hw
  have hcM : c w ≤ c M := hc (by linarith)
  rcases le_total w w' with h1 | h1
  · nlinarith
  · nlinarith

/-! ### Helpers on the direction `z^{ij}` and convexity along lines -/

open BayesRouting.VOI in
lemma brv_pt_i {I : Type} [DecidableEq I] {i j : I} (hij : i ≠ j) (lam : I → ℝ) (ε : ℝ) :
    (lam + ε • dir i j) i = lam i + ε := by
  simp [dir, Pi.single_apply, hij]

open BayesRouting.VOI in
lemma brv_pt_j {I : Type} [DecidableEq I] {i j : I} (hij : i ≠ j) (lam : I → ℝ) (ε : ℝ) :
    (lam + ε • dir i j) j = lam j - ε := by
  simp [dir, Pi.single_apply, hij.symm, sub_eq_add_neg]

open BayesRouting.VOI in
lemma brv_pt_other {I : Type} [DecidableEq I] {i j k : I} (hki : k ≠ i) (hkj : k ≠ j)
    (lam : I → ℝ) (ε : ℝ) : (lam + ε • dir i j) k = lam k := by
  simp [dir, Pi.single_apply, hki, hkj]

open BayesRouting.VOI in
lemma brv_sum_dir {I : Type} [Fintype I] [DecidableEq I] (i j : I) : ∑ k, dir i j k = 0 := by
  simp [dir, Finset.sum_sub_distrib]

open BayesRouting.VOI in
lemma brv_mem {I : Type} [Fintype I] [DecidableEq I] {i j : I} (hij : i ≠ j) {lam : I → ℝ}
    (hlam : lam ∈ stdSimplex ℝ I) {ε : ℝ} (h1 : -lam i ≤ ε) (h2 : ε ≤ lam j) :
    lam + ε • dir i j ∈ stdSimplex ℝ I := by
  refine ⟨fun k => ?_, ?_⟩
  · by_cases hki : k = i
    · subst hki; rw [brv_pt_i hij]; linarith
    · by_cases hkj : k = j
      · subst hkj; rw [brv_pt_j hij]; linarith
      · rw [brv_pt_other hki hkj]; exact hlam.1 k
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, brv_sum_dir, hlam.2]
    ring

lemma brv_line_convex {I : Type} {f : (I → ℝ) → ℝ} {C : Set (I → ℝ)} (hf : ConvexOn ℝ C f)
    (μ d : I → ℝ) : ConvexOn ℝ {ε : ℝ | μ + ε • d ∈ C} (fun ε => f (μ + ε • d)) := by
  have key : ∀ x y a b : ℝ, a + b = 1 →
      μ + (a • x + b • y) • d = a • (μ + x • d) + b • (μ + y • d) := by
    intro x y a b hab
    ext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (-(μ k)) * hab
  refine ⟨?_, ?_⟩
  · intro x hx y hy a b ha hb hab
    show μ + (a • x + b • y) • d ∈ C
    rw [key x y a b hab]
    exact hf.1 hx hy ha hb hab
  · intro x hx y hy a b ha hb hab
    show f (μ + (a • x + b • y) • d) ≤ a • f (μ + x • d) + b • f (μ + y • d)
    rw [key x y a b hab]
    exact hf.2 hx hy ha hb hab

namespace BayesRouting.VOI

variable {I : Type} [Fintype I] [DecidableEq I] {T : I → Type} [∀ i, Fintype (T i)]
  [∀ i, DecidableEq (T i)] {S E R : Type} [Fintype S] [Fintype E] [DecidableEq E] [Fintype R]

lemma vg_cont (G : Game I T S E R) (s : S) (e : E) : Continuous (G.cost s e) :=
  (G.cost_diff s e).continuous

lemma vg_mono (G : Game I T S E R) (s : S) (e : E) : Monotone (G.cost s e) :=
  (G.cost_strictMono s e).monotone

lemma vg_load_add (G : Game I T S E R) (q p : (k : I) → T k → R → ℝ) (ε : ℝ) (e : E)
    (t : (k : I) → T k) : edgeLoad G (q + ε • p) e t = edgeLoad G q e t + ε * edgeLoad G p e t := by
  simp only [edgeLoad, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    Finset.mul_sum]

lemma vg_load_comb (G : Game I T S E R) (q p : (k : I) → T k → R → ℝ) (a b : ℝ) (e : E)
    (t : (k : I) → T k) :
    edgeLoad G (a • q + b • p) e t = a * edgeLoad G q e t + b * edgeLoad G p e t := by
  simp only [edgeLoad, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    Finset.mul_sum]

lemma vg_load_sub (G : Game I T S E R) (q p : (k : I) → T k → R → ℝ) (e : E)
    (t : (k : I) → T k) : edgeLoad G (q - p) e t = edgeLoad G q e t - edgeLoad G p e t := by
  simp only [edgeLoad, Pi.sub_apply, Finset.sum_sub_distrib]

lemma vg_load_nonneg (G : Game I T S E R) {lam : I → ℝ} {q : (k : I) → T k → R → ℝ}
    (hq : q ∈ feasibleStrategies G lam) (e : E) (t : (k : I) → T k) : 0 ≤ edgeLoad G q e t :=
  Finset.sum_nonneg (fun r _ => Finset.sum_nonneg (fun k _ => hq.2 k (t k) r))

lemma vg_load_le (G : Game I T S E R) {lam : I → ℝ} (hlam : lam ∈ stdSimplex ℝ I)
    {q : (k : I) → T k → R → ℝ} (hq : q ∈ feasibleStrategies G lam) (e : E)
    (t : (k : I) → T k) : edgeLoad G q e t ≤ G.D := by
  unfold edgeLoad
  calc ∑ r ∈ univ.filter (fun r => e ∈ G.route r), ∑ k, q k (t k) r
      ≤ ∑ r, ∑ k, q k (t k) r :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun r _ _ => Finset.sum_nonneg (fun k _ => hq.2 k (t k) r))
    _ = ∑ k, lam k * G.D := by
        rw [Finset.sum_comm]; exact Finset.sum_congr rfl (fun k _ => hq.1 k (t k))
    _ = G.D := by rw [← Finset.sum_mul, hlam.2, one_mul]

lemma vg_pot_nonneg (G : Game I T S E R) {lam : I → ℝ} {q : (k : I) → T k → R → ℝ}
    (hq : q ∈ feasibleStrategies G lam) : 0 ≤ potential G q :=
  Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun e _ => Finset.sum_nonneg fun t _ =>
    mul_nonneg (G.prior_nonneg s t) (vsi_nonneg (G.cost_pos s e) (vg_load_nonneg G hq e t))

lemma vg_bdd (G : Game I T S E R) (lam : I → ℝ) :
    BddBelow (potential G '' feasibleStrategies G lam) :=
  ⟨0, by rintro _ ⟨q, hq, rfl⟩; exact vg_pot_nonneg G hq⟩

lemma vg_nonempty [Nonempty R] (G : Game I T S E R) {lam : I → ℝ} (hlam : ∀ k, 0 ≤ lam k) :
    (feasibleStrategies G lam).Nonempty := by
  refine ⟨fun k _ _ => lam k * G.D / (Fintype.card R : ℝ), fun k _ => ?_, fun k _ _ => ?_⟩
  · have : (Fintype.card R : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  · exact div_nonneg (mul_nonneg (hlam k) G.D_pos.le) (Nat.cast_nonneg _)

lemma vg_le (G : Game I T S E R) {lam : I → ℝ} {q : (k : I) → T k → R → ℝ}
    (hq : q ∈ feasibleStrategies G lam) : eqPotential G lam ≤ potential G q :=
  csInf_le (vg_bdd G lam) ⟨q, hq, rfl⟩

lemma vg_inf_bound {X : Type} {s : Set X} (hs : s.Nonempty) (f : X → ℝ) {b K : ℝ} (hb : 0 ≤ b)
    (h : ∀ x ∈ s, K ≤ b * f x) : K ≤ b * sInf (f '' s) := by
  rcases hb.lt_or_eq with hb | hb
  · have : K / b ≤ sInf (f '' s) := by
      apply le_csInf (hs.image f)
      rintro _ ⟨x, hx, rfl⟩
      rw [div_le_iff₀ hb]; linarith [h x hx]
    rw [div_le_iff₀ hb] at this; linarith
  · obtain ⟨x, hx⟩ := hs
    have := h x hx; rw [← hb] at this ⊢; simpa using this

lemma vg_typeProb_pos [∀ i, Nonempty (T i)] (G : Game I T S E R) (k : I) (tk : T k) :
    0 < typeProb G k tk := by
  unfold typeProb
  rw [Finset.sum_comm]
  set t0 : (k' : I) → T k' := Function.update (fun k' => Classical.arbitrary (T k')) k tk
  have hmem : t0 ∈ univ.filter (fun t : (k' : I) → T k' => t k = tk) := by
    simp [t0]
  calc (0:ℝ) < ∑ s, G.prior s t0 := G.prior_full_support t0
    _ ≤ _ := Finset.single_le_sum (f := fun t => ∑ s, G.prior s t)
        (fun t _ => Finset.sum_nonneg (fun s _ => G.prior_nonneg s t)) hmem

lemma vg_lin [∀ i, Nonempty (T i)] (G : Game I T S E R) (q p : (k : I) → T k → R → ℝ) :
    ∑ s, ∑ e, ∑ t, G.prior s t * (G.cost s e (edgeLoad G q e t) * edgeLoad G p e t) =
      ∑ k, ∑ tk, typeProb G k tk * ∑ r, expCost G q k tk r * p k tk r := by
  set F : I → R → S → ((k : I) → T k) → E → ℝ := fun k r s t e =>
    if e ∈ G.route r then G.prior s t * (G.cost s e (edgeLoad G q e t) * p k (t k) r) else 0
    with hF
  have hL : ∑ s, ∑ e, ∑ t, G.prior s t * (G.cost s e (edgeLoad G q e t) * edgeLoad G p e t) =
      ∑ s, ∑ e, ∑ t, ∑ r, ∑ k, F k r s t e := by
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun e _ =>
      Finset.sum_congr rfl fun t _ => ?_
    have hp : edgeLoad G p e t = ∑ r, if e ∈ G.route r then ∑ k, p k (t k) r else 0 := by
      simp only [edgeLoad, Finset.sum_filter]
    rw [hp, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [hF]
    split_ifs <;> simp [Finset.mul_sum]
  have hswap : ∑ s, ∑ e, ∑ t, ∑ r, ∑ k, F k r s t e = ∑ k, ∑ r, ∑ s, ∑ t, ∑ e, F k r s t e := by
    calc _ = ∑ s, ∑ e, ∑ t, ∑ k, ∑ r, F k r s t e :=
          Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun e _ =>
            Finset.sum_congr rfl fun t _ => Finset.sum_comm
      _ = ∑ s, ∑ e, ∑ k, ∑ t, ∑ r, F k r s t e :=
          Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun e _ => Finset.sum_comm
      _ = ∑ s, ∑ k, ∑ e, ∑ t, ∑ r, F k r s t e :=
          Finset.sum_congr rfl fun s _ => Finset.sum_comm
      _ = ∑ k, ∑ s, ∑ e, ∑ t, ∑ r, F k r s t e := Finset.sum_comm
      _ = ∑ k, ∑ s, ∑ e, ∑ r, ∑ t, F k r s t e :=
          Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun s _ =>
            Finset.sum_congr rfl fun e _ => Finset.sum_comm
      _ = ∑ k, ∑ s, ∑ r, ∑ e, ∑ t, F k r s t e :=
          Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun s _ => Finset.sum_comm
      _ = ∑ k, ∑ r, ∑ s, ∑ e, ∑ t, F k r s t e :=
          Finset.sum_congr rfl fun k _ => Finset.sum_comm
      _ = ∑ k, ∑ r, ∑ s, ∑ t, ∑ e, F k r s t e :=
          Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun r _ =>
            Finset.sum_congr rfl fun s _ => Finset.sum_comm
  have hR : ∀ k, ∑ tk, typeProb G k tk * ∑ r, expCost G q k tk r * p k tk r =
      ∑ r, ∑ s, ∑ t, ∑ e, F k r s t e := by
    intro k
    have step1 : ∀ tk, typeProb G k tk * ∑ r, expCost G q k tk r * p k tk r =
        ∑ r, ∑ s, ∑ t ∈ univ.filter (fun t : (k' : I) → T k' => t k = tk), ∑ e, F k r s t e := by
      intro tk
      have hne := (vg_typeProb_pos G k tk).ne'
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      unfold expCost belief
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t ht => ?_
      have htk : t k = tk := (Finset.mem_filter.mp ht).2
      have he : ∑ e, F k r s t e =
          ∑ e ∈ G.route r, G.prior s t * (G.cost s e (edgeLoad G q e t) * p k (t k) r) := by
        simp only [hF]
        rw [Finset.sum_ite_mem, Finset.univ_inter]
      rw [he, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [htk]
      field_simp
    rw [Finset.sum_congr rfl fun tk _ => step1 tk, Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    exact Finset.sum_fiberwise univ (fun t : (k' : I) → T k' => t k) (fun t => ∑ e, F k r s t e)
  rw [hL, hswap]
  exact Finset.sum_congr rfl fun k _ => (hR k).symm

lemma vg_bwe_sum [∀ i, Nonempty (T i)] [Nonempty R] (G : Game I T S E R) {lam : I → ℝ}
    {q : (k : I) → T k → R → ℝ} (hq : IsBWE G lam q) (k : I) (tk : T k) :
    ∑ r, expCost G q k tk r * q k tk r =
      univ.inf' univ_nonempty (fun r => expCost G q k tk r) * (lam k * G.D) := by
  rw [← hq.1.1 k tk, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rcases (hq.1.2 k tk r).lt_or_eq with h | h
  · have : expCost G q k tk r = univ.inf' univ_nonempty (fun r => expCost G q k tk r) :=
      le_antisymm (Finset.le_inf' _ _ fun r' _ => hq.2 k tk r h r')
        (Finset.inf'_le _ (mem_univ r))
    rw [this]
  · rw [← h]; ring

lemma vg_ge_min [Nonempty R] (G : Game I T S E R) {lam' : I → ℝ}
    {q' : (k : I) → T k → R → ℝ} (hq' : q' ∈ feasibleStrategies G lam')
    (q : (k : I) → T k → R → ℝ) (k : I) (tk : T k) :
    univ.inf' univ_nonempty (fun r => expCost G q k tk r) * (lam' k * G.D) ≤
      ∑ r, expCost G q k tk r * q' k tk r := by
  rw [← hq'.1 k tk, Finset.mul_sum]
  exact Finset.sum_le_sum fun r _ =>
    mul_le_mul_of_nonneg_right (Finset.inf'_le _ (mem_univ r)) (hq'.2 k tk r)

lemma vg_pot_support (G : Game I T S E R) (q q' : (k : I) → T k → R → ℝ) :
    ∑ s, ∑ e, ∑ t, G.prior s t * (G.cost s e (edgeLoad G q e t) * edgeLoad G (q' - q) e t) ≤
      potential G q' - potential G q := by
  unfold potential
  simp only [← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun e _ =>
    Finset.sum_le_sum fun t _ => ?_
  rw [vg_load_sub, ← mul_sub]
  exact mul_le_mul_of_nonneg_left (vsi_support (vg_mono G s e) (vg_cont G s e) _ _)
    (G.prior_nonneg s t)

lemma vg_lower [∀ i, Nonempty (T i)] [Nonempty R] (G : Game I T S E R) {lam : I → ℝ}
    {q : (k : I) → T k → R → ℝ} (hq : IsBWE G lam q) {lam' : I → ℝ}
    {q' : (k : I) → T k → R → ℝ} (hq' : q' ∈ feasibleStrategies G lam') :
    potential G q + G.D * ∑ k, (lam' k - lam k) * popCost G q k ≤ potential G q' := by
  have h1 := vg_pot_support G q q'
  rw [vg_lin] at h1
  suffices G.D * ∑ k, (lam' k - lam k) * popCost G q k ≤
      ∑ k, ∑ tk, typeProb G k tk * ∑ r, expCost G q k tk r * (q' - q) k tk r by linarith
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  unfold popCost
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun tk _ => ?_
  have e1 := vg_bwe_sum G hq k tk
  have e2 := vg_ge_min G hq' q k tk
  have hsub : ∑ r, expCost G q k tk r * (q' - q) k tk r =
      ∑ r, expCost G q k tk r * q' k tk r - ∑ r, expCost G q k tk r * q k tk r := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [Pi.sub_apply]; ring
  rw [hsub, e1]
  have hp := (vg_typeProb_pos G k tk).le
  set m := univ.inf' univ_nonempty (fun r => expCost G q k tk r)
  calc G.D * ((lam' k - lam k) * (typeProb G k tk * m))
      = typeProb G k tk * (m * (lam' k * G.D) - m * (lam k * G.D)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hp

lemma vg_hasDeriv (G : Game I T S E R) (q p : (k : I) → T k → R → ℝ) :
    HasDerivAt (fun ε : ℝ => potential G (q + ε • p))
      (∑ s, ∑ e, ∑ t, G.prior s t * (G.cost s e (edgeLoad G q e t) * edgeLoad G p e t)) 0 := by
  have hfun : (fun ε : ℝ => potential G (q + ε • p)) = fun ε => ∑ s, ∑ e, ∑ t,
      G.prior s t * ∫ z in (0:ℝ)..(edgeLoad G q e t + ε * edgeLoad G p e t), G.cost s e z := by
    funext ε; unfold potential; simp only [vg_load_add]
  rw [hfun]
  apply HasDerivAt.fun_sum; intro s _
  apply HasDerivAt.fun_sum; intro e _
  apply HasDerivAt.fun_sum; intro t _
  apply HasDerivAt.const_mul
  have h1 : HasDerivAt (fun ε : ℝ => edgeLoad G q e t + ε * edgeLoad G p e t)
      (edgeLoad G p e t) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const (edgeLoad G p e t)).const_add
      (edgeLoad G q e t)
  have h2 := ((vg_cont G s e).integral_hasStrictDerivAt 0
    (edgeLoad G q e t + 0 * edgeLoad G p e t)).hasDerivAt
  have h3 := h2.comp (0:ℝ) h1
  rw [zero_mul, add_zero] at h3
  exact h3

lemma vg_convex [∀ i, Nonempty (T i)] [Nonempty R] (G : Game I T S E R) :
    ConvexOn ℝ (stdSimplex ℝ I) (eqPotential G) := by
  refine ⟨convex_stdSimplex ℝ I, fun x hx y hy a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  have key : ∀ q ∈ feasibleStrategies G x, ∀ q' ∈ feasibleStrategies G y,
      eqPotential G (a • x + b • y) ≤ a * potential G q + b * potential G q' := by
    intro q hq q' hq'
    have hmem : a • q + b • q' ∈ feasibleStrategies G (a • x + b • y) := by
      refine ⟨fun k tk => ?_, fun k tk r => ?_⟩
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
          ← Finset.mul_sum, hq.1 k tk, hq'.1 k tk]
        ring
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        exact add_nonneg (mul_nonneg ha (hq.2 k tk r)) (mul_nonneg hb (hq'.2 k tk r))
    refine (vg_le G hmem).trans ?_
    unfold potential
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun e _ =>
      Finset.sum_le_sum fun t _ => ?_
    rw [vg_load_comb]
    have h := vsi_convex (vg_mono G s e) (vg_cont G s e) (edgeLoad G q e t)
      (edgeLoad G q' e t) a b ha hb hab
    have hp := G.prior_nonneg s t
    calc G.prior s t * ∫ z in (0:ℝ)..(a * edgeLoad G q e t + b * edgeLoad G q' e t), G.cost s e z
        ≤ G.prior s t * (a * (∫ z in (0:ℝ)..(edgeLoad G q e t), G.cost s e z) +
            b * ∫ z in (0:ℝ)..(edgeLoad G q' e t), G.cost s e z) :=
          mul_le_mul_of_nonneg_left h hp
      _ = _ := by ring
  have hQx := vg_nonempty G hx.1
  have hQy := vg_nonempty G hy.1
  have h2 : ∀ q' ∈ feasibleStrategies G y,
      eqPotential G (a • x + b • y) - a * eqPotential G x ≤ b * potential G q' := by
    intro q' hq'
    have h := vg_inf_bound hQx (potential G) ha
      (K := eqPotential G (a • x + b • y) - b * potential G q')
      (fun q hq => by linarith [key q hq q' hq'])
    change _ ≤ a * eqPotential G x at h
    linarith
  have h3 := vg_inf_bound hQy (potential G) hb
    (K := eqPotential G (a • x + b • y) - a * eqPotential G x) h2
  change _ ≤ b * eqPotential G y at h3
  linarith

lemma vg_transfer [Nonempty R] (G : Game I T S E R) {lam lam' : I → ℝ}
    (hl : ∀ k, 0 ≤ lam k) (hl' : ∀ k, 0 ≤ lam' k) {q' : (k : I) → T k → R → ℝ}
    (hq' : q' ∈ feasibleStrategies G lam') :
    ∃ q ∈ feasibleStrategies G lam, ∃ Δ : ℝ, 0 ≤ Δ ∧ Δ ≤ G.D * ∑ k, |lam k - lam' k| ∧
      Δ ≤ G.D * ∑ k, lam k ∧ ∀ e t, edgeLoad G q e t ≤ edgeLoad G q' e t + Δ := by
  have hD := G.D_pos
  have hR : (0:ℝ) < Fintype.card R := by exact_mod_cast Fintype.card_pos
  set a : I → ℝ := fun k => if lam k ≤ lam' k then lam k / lam' k else 1 with ha
  set b : I → ℝ := fun k => if lam k ≤ lam' k then 0 else (lam k - lam' k) * G.D /
    (Fintype.card R : ℝ) with hb
  have ha0 : ∀ k, 0 ≤ a k := fun k => by
    simp only [ha]; split_ifs
    · exact div_nonneg (hl k) (hl' k)
    · exact zero_le_one
  have ha1 : ∀ k, a k ≤ 1 := fun k => by
    simp only [ha]; split_ifs with h
    · rcases (hl' k).lt_or_eq with h' | h'
      · rw [div_le_one h']; exact h
      · rw [← h', div_zero]; exact zero_le_one
    · exact le_rfl
  have hb0 : ∀ k, 0 ≤ b k := fun k => by
    simp only [hb]; split_ifs with h
    · exact le_rfl
    · exact div_nonneg (mul_nonneg (by linarith) hD.le) hR.le
  have hbR : ∀ k, (Fintype.card R : ℝ) * b k = if lam k ≤ lam' k then 0 else (lam k - lam' k) * G.D := by
    intro k; simp only [hb]; split_ifs
    · ring
    · field_simp
  refine ⟨fun k tk r => a k * q' k tk r + b k, ⟨fun k tk => ?_, fun k tk r => ?_⟩,
    (Fintype.card R : ℝ) * ∑ k, b k, ?_, ?_, ?_, fun e t => ?_⟩
  · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hq'.1 k tk, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, hbR k]
    simp only [ha]
    split_ifs with h
    · rcases (hl' k).lt_or_eq with h' | h'
      · field_simp; ring
      · have : lam k = 0 := le_antisymm (h'.symm ▸ h) (hl k)
        rw [← h', this]; ring
    · ring
  · exact add_nonneg (mul_nonneg (ha0 k) (hq'.2 k tk r)) (hb0 k)
  · exact mul_nonneg hR.le (Finset.sum_nonneg fun k _ => hb0 k)
  · rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [hbR k]; split_ifs with h
    · exact mul_nonneg hD.le (abs_nonneg _)
    · rw [mul_comm]; exact mul_le_mul_of_nonneg_left (le_abs_self _) hD.le
  · rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [hbR k]; split_ifs with h
    · exact mul_nonneg hD.le (hl k)
    · rw [mul_comm]; exact mul_le_mul_of_nonneg_left (by linarith [hl' k]) hD.le
  · unfold edgeLoad
    calc ∑ r ∈ univ.filter (fun r => e ∈ G.route r), ∑ k, (a k * q' k (t k) r + b k)
        = ∑ r ∈ univ.filter (fun r => e ∈ G.route r), ∑ k, a k * q' k (t k) r +
            ∑ r ∈ univ.filter (fun r => e ∈ G.route r), ∑ k, b k := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun r _ => Finset.sum_add_distrib
      _ ≤ ∑ r ∈ univ.filter (fun r => e ∈ G.route r), ∑ k, q' k (t k) r +
            ∑ r, ∑ k, b k :=
          add_le_add (Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun k _ =>
              mul_le_of_le_one_left (hq'.2 k (t k) r) (ha1 k))
            (Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.filter_subset (fun r => e ∈ G.route r) (univ : Finset R))
              (fun r _ _ => Finset.sum_nonneg fun k _ => hb0 k))
      _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

lemma vg_lip [∀ i, Nonempty (T i)] [Nonempty R] (G : Game I T S E R) {lam lam' : I → ℝ}
    (hlam : lam ∈ stdSimplex ℝ I) (hlam' : lam' ∈ stdSimplex ℝ I) :
    eqPotential G lam ≤ eqPotential G lam' +
      (∑ s, ∑ e, ∑ t, G.prior s t * G.cost s e (2 * G.D)) * (G.D * ∑ k, |lam k - lam' k|) := by
  set K := ∑ s, ∑ e, ∑ t, G.prior s t * G.cost s e (2 * G.D) with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun e _ =>
    Finset.sum_nonneg fun t _ => mul_nonneg (G.prior_nonneg s t)
      (G.cost_pos s e _ (by linarith [G.D_pos])).le
  have h := vg_inf_bound (vg_nonempty G hlam'.1) (potential G) zero_le_one
    (K := eqPotential G lam - K * (G.D * ∑ k, |lam k - lam' k|)) (fun q' hq' => by
      obtain ⟨q, hq, Δ, hΔ0, hΔ1, hΔ2, hw⟩ := vg_transfer G hlam.1 hlam'.1 hq'
      rw [hlam.2, mul_one] at hΔ2
      have h1 : potential G q ≤ potential G q' + K * Δ := by
        unfold potential
        rw [hK, Finset.sum_mul, ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun s _ => ?_
        rw [Finset.sum_mul, ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun e _ => ?_
        rw [Finset.sum_mul, ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun t _ => ?_
        have := vsi_up (vg_mono G s e) (vg_cont G s e) (G.cost_pos s e)
          (vg_load_nonneg G hq e t) (hw e t) hΔ0
          (by linarith [vg_load_le G hlam' hq' e t] : edgeLoad G q' e t + Δ ≤ 2 * G.D)
        have hp := G.prior_nonneg s t
        calc G.prior s t * ∫ z in (0:ℝ)..(edgeLoad G q e t), G.cost s e z
            ≤ G.prior s t * ((∫ z in (0:ℝ)..(edgeLoad G q' e t), G.cost s e z) +
                G.cost s e (2 * G.D) * Δ) := mul_le_mul_of_nonneg_left this hp
          _ = _ := by ring
      have h2 := vg_le G hq
      have h3 : K * Δ ≤ K * (G.D * ∑ k, |lam k - lam' k|) := mul_le_mul_of_nonneg_left hΔ1 hK0
      linarith)
  change _ ≤ 1 * eqPotential G lam' at h
  linarith

lemma vg_part2 [∀ i, Nonempty (T i)] [Nonempty R] (G : Game I T S E R) :
    ∀ lam ∈ stdSimplex ℝ I, ∀ d : I → ℝ, (∃ δ : ℝ, 0 < δ ∧ lam + δ • d ∈ stdSimplex ℝ I) →
      ∃ L : ℝ, Tendsto (fun ε : ℝ => (eqPotential G (lam + ε • d) - eqPotential G lam) / ε)
        (𝓝[>] 0) (𝓝 L) := by
  intro lam hlam d ⟨δ, hδ, hδmem⟩
  have hconv := brv_line_convex (vg_convex G) lam d
  have h0 : (0:ℝ) ∈ {ε : ℝ | lam + ε • d ∈ stdSimplex ℝ I} := by simpa using hlam
  have hsub : Set.Icc 0 δ ⊆ {ε : ℝ | lam + ε • d ∈ stdSimplex ℝ I} :=
    by rw [← segment_eq_Icc hδ.le]; exact hconv.1.segment_subset h0 hδmem
  set K := ∑ s, ∑ e, ∑ t, G.prior s t * G.cost s e (2 * G.D)
  refine ⟨_, MonotoneOn.tendsto_nhdsWithin_Ioo_right (y := δ) ⟨δ / 2, by linarith, by linarith⟩
    ?_ ⟨-(K * (G.D * ∑ k, |d k|)), ?_⟩⟩
  · intro x hx y hy hxy
    have := hconv.secant_mono (a := 0) (x := x) (y := y) h0 (hsub ⟨hx.1.le, hx.2.le⟩)
      (hsub ⟨hy.1.le, hy.2.le⟩) (ne_of_gt hx.1) (ne_of_gt hy.1) hxy
    simpa using this
  · rintro _ ⟨ε, hε, rfl⟩
    have hmem : lam + ε • d ∈ stdSimplex ℝ I := hsub ⟨hε.1.le, hε.2.le⟩
    have h := vg_lip G hlam hmem
    have habs : ∑ k, |lam k - (lam + ε • d) k| = ε * ∑ k, |d k| := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sub_add_cancel_left, abs_neg,
        abs_mul, abs_of_pos hε.1]
    rw [habs] at h
    rw [le_div_iff₀ hε.1]
    nlinarith

lemma vg_part3 [∀ i, Nonempty (T i)] [Nonempty R] (G : Game I T S E R) :
    ∀ lam ∈ stdSimplex ℝ I, ∀ i j : I, i ≠ j → 0 < lam j →
      ∀ q : (k : I) → T k → R → ℝ, IsBWE G lam q →
        Tendsto (fun ε : ℝ => (eqPotential G (lam + ε • dir i j) - eqPotential G lam) / ε)
          (𝓝[>] 0) (𝓝 (-(G.D * relValue G q i j))) := by
  classical
  intro lam hlam i j hij hj q hq
  have hD := G.D_pos
  have hex : ∀ k (tk : T k), ∃ r ∈ (univ : Finset R), ∀ r' ∈ (univ : Finset R),
      expCost G q k tk r ≤ expCost G q k tk r' := fun k tk =>
    Finset.exists_min_image univ (fun r => expCost G q k tk r) univ_nonempty
  set rs : (k : I) → T k → R := fun k tk => (hex k tk).choose with hrs
  have hrs_eq : ∀ k (tk : T k), expCost G q k tk (rs k tk) =
      univ.inf' univ_nonempty (fun r => expCost G q k tk r) := fun k tk =>
    le_antisymm (Finset.le_inf' _ _ fun r' hr' => (hex k tk).choose_spec.2 r' hr')
      (Finset.inf'_le _ (mem_univ _))
  set p : (k : I) → T k → R → ℝ := fun k tk r =>
    (if k = i then (if r = rs k tk then G.D else 0) else 0) -
      (if k = j then q k tk r / lam j else 0) with hp
  -- the linear term
  have hrow : ∀ k (tk : T k), ∑ r, expCost G q k tk r * p k tk r =
      (if k = i then G.D * univ.inf' univ_nonempty (fun r => expCost G q k tk r) else 0) -
        (if k = j then G.D * univ.inf' univ_nonempty (fun r => expCost G q k tk r) else 0) := by
    intro k tk
    simp only [hp, mul_sub, Finset.sum_sub_distrib]
    congr 1
    · split_ifs with h
      · simp only [mul_ite, mul_zero, Finset.sum_ite_eq', mem_univ, if_true, hrs_eq]; ring
      · simp
    · split_ifs with h
      · subst h
        have := vg_bwe_sum G hq k tk
        simp only [mul_div_assoc'] 
        rw [← Finset.sum_div, this]
        field_simp
      · simp
  have hk : ∀ k, ∑ tk, typeProb G k tk * ∑ r, expCost G q k tk r * p k tk r =
      (if k = i then G.D * popCost G q k else 0) - (if k = j then G.D * popCost G q k else 0) := by
    intro k
    simp only [hrow, mul_sub, Finset.sum_sub_distrib]
    unfold popCost
    congr 1
    · split_ifs with h
      · rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun tk _ => by ring
      · simp
    · split_ifs with h
      · rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun tk _ => by ring
      · simp
  have hlin : ∑ s, ∑ e, ∑ t, G.prior s t * (G.cost s e (edgeLoad G q e t) * edgeLoad G p e t) =
      -(G.D * relValue G q i j) := by
    rw [vg_lin, Finset.sum_congr rfl fun k _ => hk k, Finset.sum_sub_distrib]
    simp only [Finset.sum_ite_eq', Finset.sum_ite_eq, mem_univ, if_true]
    unfold relValue
    ring
  have hfeas : ∀ ε : ℝ, 0 ≤ ε → ε ≤ lam j →
      q + ε • p ∈ feasibleStrategies G (lam + ε • dir i j) := by
    intro ε h0 h1
    refine ⟨fun k tk => ?_, fun k tk r => ?_⟩
    · have hsp : ∑ r, p k tk r = G.D * dir i j k := by
        simp only [hp, Finset.sum_sub_distrib, dir, Pi.sub_apply, Pi.single_apply]
        by_cases hki : k = i
        · have hkj : k ≠ j := fun h => hij (hki.symm.trans h)
          simp only [if_pos hki, if_neg hkj, Finset.sum_const_zero, sub_zero]
          simp
        · by_cases hkj : k = j
          · simp only [if_neg hki, if_pos hkj, Finset.sum_const_zero, zero_sub]
            rw [← Finset.sum_div, hq.1.1 k tk, hkj, mul_div_right_comm, div_self hj.ne']
            ring
          · simp only [if_neg hki, if_neg hkj, Finset.sum_const_zero, sub_zero]
            simp
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum, hq.1.1 k tk, hsp]
      ring
    · have hq0 := hq.1.2 k tk r
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hp]
      by_cases hki : k = i
      · have hkj : k ≠ j := fun h => hij (hki.symm.trans h)
        rw [if_pos hki, if_neg hkj]
        split_ifs
        · nlinarith
        · simp [hq0]
      · by_cases hkj : k = j
        · rw [if_neg hki, if_pos hkj]
          have : ε * (q k tk r / lam j) ≤ q k tk r := by
            rw [mul_div_assoc', div_le_iff₀ hj]; nlinarith
          linarith
        · rw [if_neg hki, if_neg hkj]; simp [hq0]
  have hΦ0 : eqPotential G lam = potential G q := by
    refine le_antisymm (vg_le G hq.1) (le_csInf ((vg_nonempty G hlam.1).image _) ?_)
    rintro _ ⟨q', hq', rfl⟩
    have := vg_lower G hq hq'
    simp only [sub_self, zero_mul, Finset.sum_const_zero, mul_zero, add_zero] at this
    exact this
  have hsumdir : ∀ ε : ℝ, ∑ k, ((lam + ε • dir i j) k - lam k) * popCost G q k =
      ε * (popCost G q i - popCost G q j) := by
    intro ε
    have hk' : ∀ k, ((lam + ε • dir i j) k - lam k) * popCost G q k =
        (if k = i then ε * popCost G q k else 0) - (if k = j then ε * popCost G q k else 0) := by
      intro k
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, dir, Pi.sub_apply, Pi.single_apply]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl fun k _ => hk' k, Finset.sum_sub_distrib]
    simp only [Finset.sum_ite_eq', Finset.sum_ite_eq, mem_univ, if_true]
    ring
  have hlow : ∀ ε : ℝ, 0 < ε → ε ≤ lam j →
      eqPotential G lam - ε * (G.D * relValue G q i j) ≤ eqPotential G (lam + ε • dir i j) := by
    intro ε h0 h1
    have hmem := brv_mem hij hlam (by linarith [hlam.1 i]) h1
    apply le_csInf ((vg_nonempty G hmem.1).image _)
    rintro _ ⟨q', hq', rfl⟩
    have := vg_lower G hq hq'
    rw [hsumdir] at this
    rw [hΦ0]
    unfold relValue
    linarith
  have hder := vg_hasDeriv G q p
  rw [hlin] at hder
  have hslope := hder.tendsto_slope_zero_right
  have hslope' : Tendsto (fun ε : ℝ => (potential G (q + ε • p) - eqPotential G lam) / ε)
      (𝓝[>] 0) (𝓝 (-(G.D * relValue G q i j))) := by
    refine hslope.congr' (Eventually.of_forall fun ε => ?_)
    simp only [zero_add, zero_smul, add_zero, smul_eq_mul, hΦ0]
    rw [div_eq_inv_mul]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hslope' ?_ ?_
  · filter_upwards [Ioo_mem_nhdsGT hj] with ε hε
    rw [le_div_iff₀ hε.1]
    have := hlow ε hε.1 hε.2.le
    linarith
  · filter_upwards [Ioo_mem_nhdsGT hj] with ε hε
    exact div_le_div_of_nonneg_right (by linarith [vg_le G (hfeas ε hε.1.le hε.2.le)]) hε.1.le


/-! ### Prop 3 machinery: route flows, decomposition, compactness, uniqueness -/

lemma pm_rest {lam : I → ℝ} (hlam : lam ∈ stdSimplex ℝ I) {i j : I} (hij : i ≠ j) :
    restSize lam i j = 1 - lam i - lam j := by
  unfold restSize
  have h1 := Finset.add_sum_erase univ lam (mem_univ i)
  have h2 := Finset.add_sum_erase (univ.erase i) lam (Finset.mem_erase.mpr ⟨hij.symm, mem_univ j⟩)
  rw [hlam.2] at h1
  linarith

lemma pm_rf_base (G : Game I T S E R) {lam : I → ℝ} (hlam : lam ∈ stdSimplex ℝ I)
    {q : (k : I) → T k → R → ℝ} (hq : q ∈ feasibleStrategies G lam) :
    routeFlow q ∈ flowBase G := by
  refine ⟨fun r i ti ti' t t' => ?_, fun t => ?_, fun r t => ?_⟩
  · simp only [routeFlow, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : k = i
    · subst hk; simp only [Function.update_self]
    · simp only [Function.update_of_ne hk, sub_self]
  · simp only [routeFlow]
    rw [Finset.sum_comm, Finset.sum_congr rfl fun k _ => hq.1 k (t k), ← Finset.sum_mul, hlam.2,
      one_mul]
  · exact Finset.sum_nonneg fun k _ => hq.2 k (t k) r

lemma pm_rf_impact [∀ i, Nonempty (T i)] [Nonempty R] (G : Game I T S E R) {lam : I → ℝ}
    (hlam : lam ∈ stdSimplex ℝ I) {q : (k : I) → T k → R → ℝ}
    (hq : q ∈ feasibleStrategies G lam) (i : I) :
    impact G i (routeFlow q) ≤ lam i * G.D := by
  unfold impact
  refine Finset.sup'_le _ _ fun t _ => ?_
  have h1 : ∀ r, ∑ k ∈ univ.erase i, q k (t k) r ≤
      univ.inf' univ_nonempty (fun ti : T i => routeFlow q r (Function.update t i ti)) := by
    intro r
    refine Finset.le_inf' _ _ fun ti _ => ?_
    simp only [routeFlow]
    rw [← Finset.add_sum_erase _ _ (mem_univ i)]
    simp only [Function.update_self]
    have : ∑ k ∈ univ.erase i, q k (Function.update t i ti k) r =
        ∑ k ∈ univ.erase i, q k (t k) r :=
      Finset.sum_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
    rw [this]
    linarith [hq.2 i ti r]
  have h2 : ∑ r, ∑ k ∈ univ.erase i, q k (t k) r = (1 - lam i) * G.D := by
    rw [Finset.sum_comm, Finset.sum_congr rfl fun k _ => hq.1 k (t k), ← Finset.sum_mul]
    congr 1
    have := Finset.add_sum_erase univ lam (mem_univ i)
    rw [hlam.2] at this
    linarith
  have h3 := Finset.sum_le_sum fun r (_ : r ∈ univ) => h1 r
  show G.D - ∑ r, univ.inf' univ_nonempty (fun ti : T i => routeFlow q r (Function.update t i ti))
    ≤ lam i * G.D
  linarith

lemma pm_rf_pair [∀ i, Nonempty (T i)] [Nonempty R] (G : Game I T S E R) {lam : I → ℝ}
    (hlam : lam ∈ stdSimplex ℝ I) {i j : I} (hij : i ≠ j)
    {q : (k : I) → T k → R → ℝ} (hq : q ∈ feasibleStrategies G lam) :
    routeFlow q ∈ pairFeasible G lam i j := by
  refine ⟨pm_rf_base G hlam hq, fun k _ _ => pm_rf_impact G hlam hq k, ?_⟩
  show impact G i (routeFlow q) + impact G j (routeFlow q) ≤ (1 - restSize lam i j) * G.D
  rw [pm_rest hlam hij]
  have := pm_rf_impact G hlam hq i
  have := pm_rf_impact G hlam hq j
  linarith

lemma pm_impact_nonneg [∀ i, Nonempty (T i)] [Nonempty R] (G : Game I T S E R)
    {f : R → ((k : I) → T k) → ℝ} (hf : f ∈ flowBase G) (i : I) : 0 ≤ impact G i f := by
  unfold impact
  obtain ⟨t⟩ : Nonempty ((k : I) → T k) := inferInstance
  refine le_trans ?_ (Finset.le_sup' _ (mem_univ t))
  have : ∑ r, univ.inf' univ_nonempty (fun ti : T i => f r (Function.update t i ti)) ≤
      ∑ r, f r t :=
    Finset.sum_le_sum fun r _ => by
      have := Finset.inf'_le (fun ti : T i => f r (Function.update t i ti)) (mem_univ (t i))
      simp only [Function.update_eq_self] at this
      exact this
  show 0 ≤ G.D - ∑ r, univ.inf' univ_nonempty (fun ti : T i => f r (Function.update t i ti))
  linarith [hf.2.1 t]

lemma pm_additive {F : ((k : I) → T k) → ℝ}
    (hF : ∀ i (a b : T i) (t t' : (k : I) → T k),
      F (Function.update t i a) - F (Function.update t i b) =
        F (Function.update t' i a) - F (Function.update t' i b))
    (t0 t : (k : I) → T k) :
    F t = F t0 + ∑ i, (F (Function.update t0 i (t i)) - F t0) := by
  have key : ∀ s : Finset I, ∀ t : (k : I) → T k, (∀ k, k ∉ s → t k = t0 k) →
      F t = F t0 + ∑ i ∈ s, (F (Function.update t0 i (t i)) - F t0) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro t ht
      have : t = t0 := funext fun k => ht k (Finset.notMem_empty k)
      subst this; simp
    | @insert a s ha ih =>
      intro t ht
      have h1 := ih (Function.update t a (t0 a)) (fun k hk => by
        by_cases hka : k = a
        · subst hka; simp
        · rw [Function.update_of_ne hka]
          exact ht k (by simp [Finset.mem_insert, hka, hk]))
      have h2 : ∑ i ∈ s, (F (Function.update t0 i (Function.update t a (t0 a) i)) - F t0) =
          ∑ i ∈ s, (F (Function.update t0 i (t i)) - F t0) :=
        Finset.sum_congr rfl fun i hi => by
          rw [Function.update_of_ne (fun h => ha (by rw [← h]; exact hi))]
      have h3 := hF a (t a) (t0 a) t t0
      simp only [Function.update_eq_self] at h3
      rw [Finset.sum_insert ha]
      linarith
  exact key univ t (fun k hk => absurd (mem_univ k) hk)

lemma pm_decomp [∀ i, Nonempty (T i)] [Nonempty R] (G : Game I T S E R) {μ : I → ℝ}
    (hμ : μ ∈ stdSimplex ℝ I) {f : R → ((k : I) → T k) → ℝ} (hf : f ∈ flowBase G)
    (himp : ∀ k, impact G k f ≤ μ k * G.D) :
    ∃ q ∈ feasibleStrategies G μ, routeFlow q = f := by
  obtain ⟨hf1, hf2, hf3⟩ := hf
  obtain ⟨t0⟩ : Nonempty ((k : I) → T k) := inferInstance
  obtain ⟨h, hh⟩ : ∃ h : (k : I) → R → T k → ℝ,
      ∀ k r a, h k r a = f r (Function.update t0 k a) - f r t0 := ⟨_, fun _ _ _ => rfl⟩
  obtain ⟨m, hm⟩ : ∃ m : I → R → ℝ, ∀ k r, m k r = univ.inf' univ_nonempty (h k r) :=
    ⟨_, fun _ _ => rfl⟩
  have hmle : ∀ k r a, m k r ≤ h k r a := fun k r a => by
    rw [hm]; exact Finset.inf'_le _ (mem_univ a)
  have hmex : ∀ k r, ∃ a, h k r a = m k r := fun k r => by
    obtain ⟨a, -, ha⟩ := Finset.exists_mem_eq_inf' (univ_nonempty (α := T k)) (h k r)
    exact ⟨a, by rw [hm, ha]⟩
  have hadd : ∀ r t, f r t = f r t0 + ∑ k, h k r (t k) := by
    intro r t
    rw [pm_additive (F := f r) (fun i a b t t' => hf1 r i a b t t') t0 t]
    simp only [hh]
  have hsumh : ∀ k a, ∑ r, h k r a = 0 := by
    intro k a
    simp only [hh, Finset.sum_sub_distrib, hf2]
    ring
  have hJ : ∀ k, -∑ r, m k r ≤ μ k * G.D := by
    intro k
    refine le_trans ?_ (himp k)
    unfold impact
    refine le_trans ?_ (Finset.le_sup' _ (mem_univ t0))
    have hle : ∀ r, univ.inf' univ_nonempty (fun a : T k => f r (Function.update t0 k a)) ≤
        f r t0 + m k r := by
      intro r
      obtain ⟨a, ha⟩ := hmex k r
      refine le_trans (Finset.inf'_le _ (mem_univ a)) ?_
      rw [← ha, hh]
      linarith
    have h2 := Finset.sum_le_sum fun r (_ : r ∈ univ) => hle r
    rw [Finset.sum_add_distrib, hf2 t0] at h2
    show -∑ r, m k r ≤
      G.D - ∑ r, univ.inf' univ_nonempty (fun a : T k => f r (Function.update t0 k a))
    linarith
  obtain ⟨c, hc⟩ : ∃ c : R → ℝ, ∀ r, c r = f r t0 + ∑ k, m k r := ⟨_, fun _ => rfl⟩
  have hfc : ∀ r t, f r t = c r + ∑ k, (h k r (t k) - m k r) := by
    intro r t
    rw [hadd r t, hc, Finset.sum_sub_distrib]
    ring
  have hc0 : ∀ r, 0 ≤ c r := by
    intro r
    have h1 := hfc r (fun k => (hmex k r).choose)
    have h2 : ∀ k, h k r ((hmex k r).choose) - m k r = 0 := fun k => by
      rw [(hmex k r).choose_spec, sub_self]
    simp only [h2, Finset.sum_const_zero, add_zero] at h1
    rw [← h1]
    exact hf3 r _
  have hsc : ∑ r, c r = G.D + ∑ k, ∑ r, m k r := by
    simp only [hc]
    rw [Finset.sum_add_distrib, hf2 t0, Finset.sum_comm]
  obtain ⟨s, hs⟩ : ∃ s : I → ℝ, ∀ k, s k = μ k * G.D + ∑ r, m k r := ⟨_, fun _ => rfl⟩
  have hs0 : ∀ k, 0 ≤ s k := fun k => by rw [hs]; linarith [hJ k]
  have hσ : ∑ k, s k = ∑ r, c r := by
    simp only [hs, Finset.sum_add_distrib, ← Finset.sum_mul, hμ.2, one_mul, hsc]
  refine ⟨fun k a r => (h k r a - m k r) + c r * (s k / ∑ k', s k'),
    ⟨fun k a => ?_, fun k a r => ?_⟩, ?_⟩
  · simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, hsumh, ← Finset.sum_mul, ← hσ]
    by_cases hz : ∑ k', s k' = 0
    · have hsk : s k = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun k' _ => hs0 k').mp hz k (mem_univ k)
      rw [hz, zero_mul]
      linarith [hs k]
    · have : (∑ k', s k') * (s k / ∑ k', s k') = s k := by field_simp
      rw [this]
      linarith [hs k]
  · exact add_nonneg (sub_nonneg.mpr (hmle k r a))
      (mul_nonneg (hc0 r) (div_nonneg (hs0 k) (Finset.sum_nonneg fun k' _ => hs0 k')))
  · funext r t
    simp only [routeFlow]
    rw [hfc r t, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div]
    by_cases hz : ∑ k', s k' = 0
    · have hz' : ∑ r', c r' = 0 := by rw [← hσ]; exact hz
      have hcr : c r = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun r' _ => hc0 r').mp hz' r (mem_univ r)
      rw [hcr]; ring
    · rw [div_self hz]; ring

/-! ### Continuity and compactness -/

lemma pm_prim_cont (G : Game I T S E R) (s : S) (e : E) :
    Continuous (fun x : ℝ => ∫ z in (0:ℝ)..x, G.cost s e z) :=
  continuous_iff_continuousAt.2 fun x =>
    ((vg_cont G s e).integral_hasStrictDerivAt 0 x).hasDerivAt.continuousAt

lemma pm_pot_cont (G : Game I T S E R) : Continuous (potential G) := by
  have hl : ∀ e t, Continuous fun q : (k : I) → T k → R → ℝ => edgeLoad G q e t := by
    intro e t
    show Continuous fun q : (k : I) → T k → R → ℝ =>
      ∑ r ∈ univ.filter (fun r => e ∈ G.route r), ∑ k, q k (t k) r
    exact continuous_finsetSum _ fun r _ => continuous_finsetSum _ fun k _ => by fun_prop
  show Continuous fun q : (k : I) → T k → R → ℝ =>
    ∑ s, ∑ e, ∑ t, G.prior s t * ∫ z in (0:ℝ)..(edgeLoad G q e t), G.cost s e z
  exact continuous_finsetSum _ fun s _ => continuous_finsetSum _ fun e _ =>
    continuous_finsetSum _ fun t _ => continuous_const.mul ((pm_prim_cont G s e).comp (hl e t))

lemma pm_fpot_cont (G : Game I T S E R) : Continuous (flowPotential G) := by
  have hl : ∀ e t, Continuous fun f : R → ((k : I) → T k) → ℝ => flowLoad G f e t := by
    intro e t
    show Continuous fun f : R → ((k : I) → T k) → ℝ =>
      ∑ r ∈ univ.filter (fun r => e ∈ G.route r), f r t
    exact continuous_finsetSum _ fun r _ => by fun_prop
  show Continuous fun f : R → ((k : I) → T k) → ℝ =>
    ∑ s, ∑ e, ∑ t, G.prior s t * ∫ z in (0:ℝ)..(flowLoad G f e t), G.cost s e z
  exact continuous_finsetSum _ fun s _ => continuous_finsetSum _ fun e _ =>
    continuous_finsetSum _ fun t _ => continuous_const.mul ((pm_prim_cont G s e).comp (hl e t))

lemma pm_impact_cont [∀ i, Nonempty (T i)] [Nonempty R] (G : Game I T S E R) (i : I) :
    Continuous (impact G i) := by
  show Continuous fun f : R → ((k : I) → T k) → ℝ =>
    univ.sup' univ_nonempty (fun t : (k : I) → T k =>
      G.D - ∑ r, univ.inf' univ_nonempty (fun ti : T i => f r (Function.update t i ti)))
  refine Continuous.finset_sup'_apply _ fun t _ => ?_
  refine continuous_const.sub (continuous_finsetSum _ fun r _ => ?_)
  exact Continuous.finset_inf'_apply _ fun ti _ => by fun_prop

lemma pm_Q_compact (G : Game I T S E R) (μ : I → ℝ) : IsCompact (feasibleStrategies G μ) := by
  have hcl : IsClosed (feasibleStrategies G μ) := by
    unfold feasibleStrategies
    simp only [Set.ofPred_and, Set.ofPred_forall]
    exact (isClosed_iInter fun i => isClosed_iInter fun ti =>
        isClosed_eq (continuous_finsetSum _ fun r _ => by fun_prop) continuous_const).inter
      (isClosed_iInter fun i => isClosed_iInter fun ti => isClosed_iInter fun r =>
        isClosed_le continuous_const (by fun_prop))
  have hbox : IsCompact (Set.univ.pi fun i : I => Set.univ.pi fun ti : T i =>
      Set.univ.pi fun r : R => Set.Icc (0:ℝ) (|μ i| * G.D)) :=
    isCompact_univ_pi fun i => isCompact_univ_pi fun ti => isCompact_univ_pi fun r => isCompact_Icc
  refine hbox.of_isClosed_subset hcl fun q hq => ?_
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
  intro i ti r
  refine ⟨hq.2 i ti r, ?_⟩
  have h1 : q i ti r ≤ ∑ r', q i ti r' :=
    Finset.single_le_sum (f := fun r' => q i ti r') (fun r' _ => hq.2 i ti r') (mem_univ r)
  rw [hq.1 i ti] at h1
  have := G.D_pos
  have : μ i * G.D ≤ |μ i| * G.D := mul_le_mul_of_nonneg_right (le_abs_self _) this.le
  linarith

lemma pm_attain [Nonempty R] (G : Game I T S E R) {μ : I → ℝ} (hμ : μ ∈ stdSimplex ℝ I) :
    ∃ q ∈ feasibleStrategies G μ, potential G q = eqPotential G μ := by
  obtain ⟨q, hq, hmin⟩ := (pm_Q_compact G μ).exists_isMinOn (vg_nonempty G hμ.1)
    (pm_pot_cont G).continuousOn
  refine ⟨q, hq, le_antisymm ?_ (vg_le G hq)⟩
  exact le_csInf ((vg_nonempty G hμ.1).image _)
    (by rintro _ ⟨q', hq', rfl⟩; exact isMinOn_iff.mp hmin q' hq')

lemma pm_base_closed (G : Game I T S E R) : IsClosed (flowBase G) := by
  unfold flowBase
  simp only [Set.ofPred_and, Set.ofPred_forall]
  exact (isClosed_iInter fun r => isClosed_iInter fun i => isClosed_iInter fun ti =>
      isClosed_iInter fun ti' => isClosed_iInter fun t => isClosed_iInter fun t' =>
        isClosed_eq (by fun_prop) (by fun_prop)).inter
    ((isClosed_iInter fun t =>
        isClosed_eq (continuous_finsetSum _ fun r _ => by fun_prop) continuous_const).inter
      (isClosed_iInter fun r => isClosed_iInter fun t => isClosed_le continuous_const (by fun_prop)))

lemma pm_pf_closed [∀ i, Nonempty (T i)] [Nonempty R] (G : Game I T S E R) (lam : I → ℝ)
    (i j : I) : IsClosed (pairFeasible G lam i j) := by
  unfold pairFeasible
  refine (pm_base_closed G).inter ?_
  simp only [Set.ofPred_and, Set.ofPred_forall]
  exact (isClosed_iInter fun k => isClosed_iInter fun _ => isClosed_iInter fun _ =>
      isClosed_le (pm_impact_cont G k) continuous_const).inter
    (isClosed_le ((pm_impact_cont G i).add (pm_impact_cont G j)) continuous_const)

lemma pm_pf_compact [∀ i, Nonempty (T i)] [Nonempty R] (G : Game I T S E R) (lam : I → ℝ)
    (i j : I) : IsCompact (pairFeasible G lam i j) := by
  have hbox : IsCompact (Set.univ.pi fun r : R => Set.univ.pi fun t : ((k : I) → T k) =>
      Set.Icc (0:ℝ) G.D) :=
    isCompact_univ_pi fun r => isCompact_univ_pi fun t => isCompact_Icc
  refine hbox.of_isClosed_subset (pm_pf_closed G lam i j) fun f hf => ?_
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
  intro r t
  refine ⟨hf.1.2.2 r t, ?_⟩
  have h1 : f r t ≤ ∑ r', f r' t :=
    Finset.single_le_sum (f := fun r' => f r' t) (fun r' _ => hf.1.2.2 r' t) (mem_univ r)
  rw [hf.1.2.1 t] at h1
  exact h1

lemma pm_P_ne [∀ i, Nonempty (T i)] [Nonempty R] (G : Game I T S E R) {lam : I → ℝ}
    (hlam : lam ∈ stdSimplex ℝ I) {i j : I} (hij : i ≠ j) :
    ∃ f0, f0 ∈ pairOptimal G lam i j := by
  obtain ⟨q, hq⟩ := vg_nonempty G hlam.1
  obtain ⟨f0, hf0, hmin⟩ := (pm_pf_compact G lam i j).exists_isMinOn
    ⟨_, pm_rf_pair G hlam hij hq⟩ (pm_fpot_cont G).continuousOn
  exact ⟨f0, hf0, fun g hg => isMinOn_iff.mp hmin g hg⟩

lemma pm_P_compact [∀ i, Nonempty (T i)] [Nonempty R] (G : Game I T S E R) {lam : I → ℝ}
    {i j : I} {f0 : R → ((k : I) → T k) → ℝ} (hf0 : f0 ∈ pairOptimal G lam i j) :
    IsCompact (pairOptimal G lam i j) := by
  have : pairOptimal G lam i j =
      pairFeasible G lam i j ∩ {f | flowPotential G f ≤ flowPotential G f0} := by
    ext f
    simp only [pairOptimal, flowArgmin, Set.mem_ofPred_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨hf, hmin⟩; exact ⟨hf, hmin f0 hf0.1⟩
    · rintro ⟨hf, hle⟩; exact ⟨hf, fun g hg => hle.trans (hf0.2 g hg)⟩
  rw [this]
  exact (pm_pf_compact G lam i j).inter_right (isClosed_le (pm_fpot_cont G) continuous_const)

lemma pm_low [∀ i, Nonempty (T i)] [Nonempty R] (G : Game I T S E R) {lam : I → ℝ}
    (hlam : lam ∈ stdSimplex ℝ I) {i j : I} (hij : i ≠ j) :
    ∃ f1 ∈ pairOptimal G lam i j, impact G i f1 = lowThr G lam i j * G.D ∧
      ∀ f ∈ pairOptimal G lam i j, impact G i f1 ≤ impact G i f := by
  obtain ⟨f0, hf0⟩ := pm_P_ne G hlam hij
  obtain ⟨f1, hf1, hmin⟩ := (pm_P_compact G hf0).exists_isMinOn ⟨f0, hf0⟩
    (pm_impact_cont G i).continuousOn
  have hmin' : ∀ f ∈ pairOptimal G lam i j, impact G i f1 ≤ impact G i f :=
    fun f hf => isMinOn_iff.mp hmin f hf
  refine ⟨f1, hf1, ?_, hmin'⟩
  have hs : sInf (impact G i '' pairOptimal G lam i j) = impact G i f1 :=
    IsLeast.csInf_eq ⟨⟨f1, hf1, rfl⟩, by rintro _ ⟨f, hf, rfl⟩; exact hmin' f hf⟩
  unfold lowThr
  rw [hs]
  field_simp [G.D_pos.ne']

lemma pm_high [∀ i, Nonempty (T i)] [Nonempty R] (G : Game I T S E R) {lam : I → ℝ}
    (hlam : lam ∈ stdSimplex ℝ I) {i j : I} (hij : i ≠ j) :
    ∃ f2 ∈ pairOptimal G lam i j,
      (1 - restSize lam i j) * G.D - impact G j f2 = highThr G lam i j * G.D ∧
      ∀ f ∈ pairOptimal G lam i j,
        (1 - restSize lam i j) * G.D - impact G j f ≤ (1 - restSize lam i j) * G.D - impact G j f2 := by
  obtain ⟨f0, hf0⟩ := pm_P_ne G hlam hij
  obtain ⟨f2, hf2, hmax⟩ := (pm_P_compact G hf0).exists_isMaxOn
    (f := fun f => (1 - restSize lam i j) * G.D - impact G j f) ⟨f0, hf0⟩
    (continuous_const.sub (pm_impact_cont G j)).continuousOn
  have hmax' : ∀ f ∈ pairOptimal G lam i j,
      (1 - restSize lam i j) * G.D - impact G j f ≤ (1 - restSize lam i j) * G.D - impact G j f2 :=
    fun f hf => isMaxOn_iff.mp hmax f hf
  refine ⟨f2, hf2, ?_, hmax'⟩
  have hs : sSup ((fun f => (1 - restSize lam i j) * G.D - impact G j f) '' pairOptimal G lam i j) =
      (1 - restSize lam i j) * G.D - impact G j f2 :=
    IsGreatest.csSup_eq ⟨⟨f2, hf2, rfl⟩, by rintro _ ⟨f, hf, rfl⟩; exact hmax' f hf⟩
  unfold highThr
  rw [hs]
  field_simp [G.D_pos.ne']

/-! ### Strict convexity and uniqueness of the optimal edge load -/

lemma pm_strict (G : Game I T S E R) (s : S) (e : E) {x y : ℝ} (hxy : x ≠ y) :
    (∫ z in (0:ℝ)..((1/2:ℝ) * x + (1/2:ℝ) * y), G.cost s e z) <
      (1/2:ℝ) * (∫ z in (0:ℝ)..x, G.cost s e z) + (1/2:ℝ) * ∫ z in (0:ℝ)..y, G.cost s e z := by
  have hd : deriv (fun x : ℝ => ∫ z in (0:ℝ)..x, G.cost s e z) = G.cost s e := by
    funext x; exact ((vg_cont G s e).integral_hasStrictDerivAt 0 x).hasDerivAt.deriv
  have hsc : StrictConvexOn ℝ Set.univ (fun x : ℝ => ∫ z in (0:ℝ)..x, G.cost s e z) :=
    StrictMono.strictConvexOn_univ_of_deriv (pm_prim_cont G s e)
      (by rw [hd]; exact G.cost_strictMono s e)
  have := hsc.2 (Set.mem_univ x) (Set.mem_univ y) hxy (by norm_num : (0:ℝ) < 1/2)
    (by norm_num : (0:ℝ) < 1/2) (by norm_num)
  simpa only [smul_eq_mul] using this

lemma pm_fload_comb (G : Game I T S E R) (f g : R → ((k : I) → T k) → ℝ) (a b : ℝ) (e : E)
    (t : (k : I) → T k) :
    flowLoad G (a • f + b • g) e t = a * flowLoad G f e t + b * flowLoad G g e t := by
  simp only [flowLoad, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    Finset.mul_sum]

lemma pm_impact_conv [∀ i, Nonempty (T i)] [Nonempty R] (G : Game I T S E R) (k : I)
    (f g : R → ((k : I) → T k) → ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    impact G k (a • f + b • g) ≤ a * impact G k f + b * impact G k g := by
  unfold impact
  refine Finset.sup'_le _ _ fun t _ => ?_
  have h1 := Finset.le_sup' (fun t : (k' : I) → T k' =>
    G.D - ∑ r, univ.inf' univ_nonempty (fun ti : T k => f r (Function.update t k ti))) (mem_univ t)
  have h2 := Finset.le_sup' (fun t : (k' : I) → T k' =>
    G.D - ∑ r, univ.inf' univ_nonempty (fun ti : T k => g r (Function.update t k ti))) (mem_univ t)
  have h3 : ∀ r, a * univ.inf' univ_nonempty (fun ti : T k => f r (Function.update t k ti)) +
      b * univ.inf' univ_nonempty (fun ti : T k => g r (Function.update t k ti)) ≤
      univ.inf' univ_nonempty (fun ti : T k => (a • f + b • g) r (Function.update t k ti)) := by
    intro r
    refine Finset.le_inf' _ _ fun ti _ => ?_
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left (Finset.inf'_le _ (mem_univ ti)) ha)
      (mul_le_mul_of_nonneg_left (Finset.inf'_le _ (mem_univ ti)) hb)
  have h4 := Finset.sum_le_sum fun r (_ : r ∈ univ) => h3 r
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h4
  have h5 := mul_le_mul_of_nonneg_left h1 ha
  have h6 := mul_le_mul_of_nonneg_left h2 hb
  have hD : G.D = a * G.D + b * G.D := by rw [← add_mul, hab, one_mul]
  linarith

lemma pm_pf_conv [∀ i, Nonempty (T i)] [Nonempty R] (G : Game I T S E R) (lam : I → ℝ) (i j : I)
    {f g : R → ((k : I) → T k) → ℝ} (hf : f ∈ pairFeasible G lam i j)
    (hg : g ∈ pairFeasible G lam i j) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • f + b • g ∈ pairFeasible G lam i j := by
  obtain ⟨⟨hf1, hf2, hf3⟩, hf4, hf5⟩ := hf
  obtain ⟨⟨hg1, hg2, hg3⟩, hg4, hg5⟩ := hg
  refine ⟨⟨fun r k ti ti' t t' => ?_, fun t => ?_, fun r t => ?_⟩, fun k hki hkj => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination a * hf1 r k ti ti' t t' + b * hg1 r k ti ti' t t'
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
      hf2, hg2]
    linear_combination G.D * hab
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hf3 r t)) (mul_nonneg hb (hg3 r t))
  · have h1 := pm_impact_conv G k f g ha hb hab
    have h2 := mul_le_mul_of_nonneg_left (hf4 k hki hkj) ha
    have h3 := mul_le_mul_of_nonneg_left (hg4 k hki hkj) hb
    have hx : lam k * G.D = a * (lam k * G.D) + b * (lam k * G.D) := by
      rw [← add_mul, hab, one_mul]
    linarith
  · have h1 := pm_impact_conv G i f g ha hb hab
    have h2 := pm_impact_conv G j f g ha hb hab
    have h3 := mul_le_mul_of_nonneg_left hf5 ha
    have h4 := mul_le_mul_of_nonneg_left hg5 hb
    have hx : (1 - restSize lam i j) * G.D =
        a * ((1 - restSize lam i j) * G.D) + b * ((1 - restSize lam i j) * G.D) := by
      rw [← add_mul, hab, one_mul]
    show impact G i (a • f + b • g) + impact G j (a • f + b • g) ≤ (1 - restSize lam i j) * G.D
    linarith

lemma pm_unique [∀ i, Nonempty (T i)] [Nonempty R] (G : Game I T S E R) (lam : I → ℝ) (i j : I)
    {f g : R → ((k : I) → T k) → ℝ} (hf : f ∈ pairOptimal G lam i j)
    (hg : g ∈ pairOptimal G lam i j) : flowLoad G f = flowLoad G g := by
  by_contra hne
  obtain ⟨e0, t0, hne'⟩ : ∃ e t, flowLoad G f e t ≠ flowLoad G g e t := by
    by_contra h
    exact hne (funext fun e => funext fun t => by
      by_contra h'; exact h ⟨e, t, h'⟩)
  obtain ⟨s0, hs0⟩ : ∃ s, 0 < G.prior s t0 := by
    by_contra h
    have : ∑ s, G.prior s t0 ≤ 0 :=
      Finset.sum_nonpos fun s _ => le_of_not_gt fun hs => h ⟨s, hs⟩
    linarith [G.prior_full_support t0]
  have hmem := pm_pf_conv G lam i j hf.1 hg.1 (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  have hfg : flowPotential G f = flowPotential G g := le_antisymm (hf.2 g hg.1) (hg.2 f hf.1)
  have hle := hf.2 _ hmem
  have hterm : ∀ s e t, G.prior s t *
      ∫ z in (0:ℝ)..(flowLoad G ((1/2:ℝ) • f + (1/2:ℝ) • g) e t), G.cost s e z ≤
      (1/2:ℝ) * (G.prior s t * ∫ z in (0:ℝ)..(flowLoad G f e t), G.cost s e z) +
      (1/2:ℝ) * (G.prior s t * ∫ z in (0:ℝ)..(flowLoad G g e t), G.cost s e z) := by
    intro s e t
    rw [pm_fload_comb]
    have h := vsi_convex (vg_mono G s e) (vg_cont G s e) (flowLoad G f e t) (flowLoad G g e t)
      (1/2) (1/2) (by norm_num) (by norm_num) (by norm_num)
    have h2 := mul_le_mul_of_nonneg_left h (G.prior_nonneg s t)
    linarith
  have hstrict : G.prior s0 t0 *
      ∫ z in (0:ℝ)..(flowLoad G ((1/2:ℝ) • f + (1/2:ℝ) • g) e0 t0), G.cost s0 e0 z <
      (1/2:ℝ) * (G.prior s0 t0 * ∫ z in (0:ℝ)..(flowLoad G f e0 t0), G.cost s0 e0 z) +
      (1/2:ℝ) * (G.prior s0 t0 * ∫ z in (0:ℝ)..(flowLoad G g e0 t0), G.cost s0 e0 z) := by
    rw [pm_fload_comb]
    have h := pm_strict G s0 e0 hne'
    have h2 := mul_lt_mul_of_pos_left h hs0
    linarith
  have hlt : flowPotential G ((1/2:ℝ) • f + (1/2:ℝ) • g) <
      (1/2:ℝ) * flowPotential G f + (1/2:ℝ) * flowPotential G g := by
    unfold flowPotential
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_lt_sum (fun s _ => Finset.sum_le_sum fun e _ =>
        Finset.sum_le_sum fun t _ => hterm s e t)
      ⟨s0, mem_univ _, Finset.sum_lt_sum (fun e _ => Finset.sum_le_sum fun t _ => hterm s0 e t)
        ⟨e0, mem_univ _, Finset.sum_lt_sum (fun t _ => hterm s0 e0 t) ⟨t0, mem_univ _, hstrict⟩⟩⟩
  linarith

/-! ### Ψ along the line and the threshold points -/

lemma pm_bwe_min [∀ i, Nonempty (T i)] [Nonempty R] (G : Game I T S E R) {lam : I → ℝ}
    (hlam : lam ∈ stdSimplex ℝ I) {q : (k : I) → T k → R → ℝ} (hq : IsBWE G lam q) :
    potential G q = eqPotential G lam := by
  refine le_antisymm (le_csInf ((vg_nonempty G hlam.1).image _) ?_) (vg_le G hq.1)
  rintro _ ⟨q', hq', rfl⟩
  have := vg_lower G hq hq'
  simpa using this

lemma pm_pf_line [∀ i, Nonempty (T i)] [Nonempty R] (G : Game I T S E R) {i j : I} (hij : i ≠ j)
    (lam : I → ℝ) (s : ℝ) : pairFeasible G (lam + s • dir i j) i j = pairFeasible G lam i j := by
  have h : ∀ k, k ≠ i → k ≠ j → (lam + s • dir i j) k = lam k :=
    fun k hki hkj => brv_pt_other hki hkj lam s
  have hr : restSize (lam + s • dir i j) i j = restSize lam i j := by
    unfold restSize
    refine Finset.sum_congr rfl (fun k hk => ?_)
    simp only [Finset.mem_erase] at hk
    exact h k hk.2.1 hk.1
  ext f
  simp only [pairFeasible, Set.mem_inter_iff, Set.mem_ofPred_eq, hr]
  constructor
  · rintro ⟨hb, h1, h2⟩
    refine ⟨hb, fun k hki hkj => ?_, h2⟩
    rw [← h k hki hkj]; exact h1 k hki hkj
  · rintro ⟨hb, h1, h2⟩
    refine ⟨hb, fun k hki hkj => ?_, h2⟩
    rw [h k hki hkj]; exact h1 k hki hkj

lemma pm_po_line [∀ i, Nonempty (T i)] [Nonempty R] (G : Game I T S E R) {i j : I} (hij : i ≠ j)
    (lam : I → ℝ) (s : ℝ) : pairOptimal G (lam + s • dir i j) i j = pairOptimal G lam i j := by
  unfold pairOptimal
  rw [pm_pf_line G hij]

lemma pm_lb [∀ i, Nonempty (T i)] [Nonempty R] (G : Game I T S E R) {μ : I → ℝ}
    (hμ : μ ∈ stdSimplex ℝ I) {i j : I} (hij : i ≠ j) {f0 : R → ((k : I) → T k) → ℝ}
    (hf0 : f0 ∈ pairOptimal G μ i j) : flowPotential G f0 ≤ eqPotential G μ :=
  le_csInf ((vg_nonempty G hμ.1).image _)
    (by rintro _ ⟨q, hq, rfl⟩; exact hf0.2 _ (pm_rf_pair G hμ hij hq))

lemma pm_ub [∀ i, Nonempty (T i)] [Nonempty R] (G : Game I T S E R) {μ : I → ℝ}
    (hμ : μ ∈ stdSimplex ℝ I) {i j : I} {f : R → ((k : I) → T k) → ℝ}
    (hf : f ∈ pairFeasible G μ i j) (hi : impact G i f ≤ μ i * G.D)
    (hj : impact G j f ≤ μ j * G.D) : eqPotential G μ ≤ flowPotential G f := by
  have himp : ∀ k, impact G k f ≤ μ k * G.D := by
    intro k
    by_cases hki : k = i
    · rw [hki]; exact hi
    by_cases hkj : k = j
    · rw [hkj]; exact hj
    exact hf.2.1 k hki hkj
  obtain ⟨q, hq, hqf⟩ := pm_decomp G hμ hf.1 himp
  rw [← hqf]
  exact vg_le G hq

lemma pm_gt [∀ i, Nonempty (T i)] [Nonempty R] (G : Game I T S E R) {μ : I → ℝ}
    (hμ : μ ∈ stdSimplex ℝ I) {i j : I} (hij : i ≠ j) {f0 : R → ((k : I) → T k) → ℝ}
    (hf0 : f0 ∈ pairOptimal G μ i j)
    (hout : ∀ f ∈ pairOptimal G μ i j, μ i * G.D < impact G i f ∨ μ j * G.D < impact G j f) :
    flowPotential G f0 < eqPotential G μ := by
  obtain ⟨q, hq, hqe⟩ := pm_attain G hμ
  rw [← hqe]
  by_contra hle
  have hle' : potential G q ≤ flowPotential G f0 := not_lt.mp hle
  have hrf := pm_rf_pair G hμ hij hq
  have hopt : routeFlow q ∈ pairOptimal G μ i j :=
    ⟨hrf, fun g hg => le_trans hle' (hf0.2 g hg)⟩
  rcases hout _ hopt with h | h
  · linarith [pm_rf_impact G hμ hq i]
  · linarith [pm_rf_impact G hμ hq j]

lemma pm_conv_line [∀ i, Nonempty (T i)] [Nonempty R] (G : Game I T S E R) {i j : I}
    (hij : i ≠ j) {lam : I → ℝ} (hlam : lam ∈ stdSimplex ℝ I) :
    ConvexOn ℝ (Set.Icc (-lam i) (lam j)) (fun s : ℝ => eqPotential G (lam + s • dir i j)) :=
  (brv_line_convex (vg_convex G) lam (dir i j)).subset
    (fun s hs => brv_mem hij hlam hs.1 hs.2) (convex_Icc _ _)

lemma pm_facts [∀ i, Nonempty (T i)] [Nonempty R] (G : Game I T S E R) {i j : I} (hij : i ≠ j)
    {lam : I → ℝ} (hlam : lam ∈ stdSimplex ℝ I) :
    ∃ Φd : ℝ, (∀ f ∈ pairOptimal G lam i j, flowPotential G f = Φd) ∧
      (∀ s, -lam i ≤ s → s ≤ lam j → Φd ≤ eqPotential G (lam + s • dir i j)) ∧
      (∀ s, lowThr G lam i j - lam i ≤ s → s ≤ highThr G lam i j - lam i →
        eqPotential G (lam + s • dir i j) = Φd) ∧
      0 ≤ lowThr G lam i j ∧ lowThr G lam i j ≤ highThr G lam i j ∧
      highThr G lam i j ≤ lam i + lam j ∧
      (∀ f ∈ pairOptimal G lam i j, lowThr G lam i j * G.D ≤ impact G i f) ∧
      (∀ f ∈ pairOptimal G lam i j,
        (lam i + lam j) * G.D - impact G j f ≤ highThr G lam i j * G.D) ∧
      (lam i < lowThr G lam i j → Φd < eqPotential G lam) ∧
      (highThr G lam i j < lam i → Φd < eqPotential G lam) := by
  obtain ⟨f1, hf1, hf1e, hf1m⟩ := pm_low G hlam hij
  obtain ⟨f2, hf2, hf2e, hf2m⟩ := pm_high G hlam hij
  have hrest := pm_rest hlam hij
  have hD := G.D_pos
  have hPeq : ∀ f ∈ pairOptimal G lam i j, flowPotential G f = flowPotential G f1 :=
    fun f hf => le_antisymm (hf.2 f1 hf1.1) (hf1.2 f hf.1)
  have hi1 := pm_impact_nonneg G hf1.1.1 i
  have hj1 := pm_impact_nonneg G hf1.1.1 j
  have hi2 := pm_impact_nonneg G hf2.1.1 i
  have hj2 := pm_impact_nonneg G hf2.1.1 j
  have hs1 : impact G i f1 + impact G j f1 ≤ (1 - restSize lam i j) * G.D := hf1.1.2.2
  have hs2 : impact G i f2 + impact G j f2 ≤ (1 - restSize lam i j) * G.D := hf2.1.2.2
  have h12 := hf1m f2 hf2
  rw [hrest] at hs1 hs2 hf2e hf2m
  have hl0 : 0 ≤ lowThr G lam i j := le_of_mul_le_mul_right (by linarith) hD
  have hlh : lowThr G lam i j ≤ highThr G lam i j := le_of_mul_le_mul_right (by linarith) hD
  have hhs : highThr G lam i j ≤ lam i + lam j := le_of_mul_le_mul_right (by linarith) hD
  have hlb : ∀ s, -lam i ≤ s → s ≤ lam j →
      flowPotential G f1 ≤ eqPotential G (lam + s • dir i j) := by
    intro s h1 h2
    exact pm_lb G (brv_mem hij hlam h1 h2) hij (by rw [pm_po_line G hij]; exact hf1)
  have hA : eqPotential G (lam + (lowThr G lam i j - lam i) • dir i j) ≤ flowPotential G f1 := by
    refine pm_ub G (brv_mem hij hlam (by linarith) (by linarith))
      (by rw [pm_pf_line G hij]; exact hf1.1) ?_ ?_
    · rw [brv_pt_i hij]; linarith
    · rw [brv_pt_j hij]; linarith
  have hB : eqPotential G (lam + (highThr G lam i j - lam i) • dir i j) ≤ flowPotential G f2 := by
    refine pm_ub G (brv_mem hij hlam (by linarith) (by linarith))
      (by rw [pm_pf_line G hij]; exact hf2.1) ?_ ?_
    · rw [brv_pt_i hij]; linarith
    · rw [brv_pt_j hij]; linarith
  rw [hPeq f2 hf2] at hB
  have hconv := pm_conv_line G hij hlam
  have hseg : ∀ s, lowThr G lam i j - lam i ≤ s → s ≤ highThr G lam i j - lam i →
      eqPotential G (lam + s • dir i j) = flowPotential G f1 := by
    intro s h1 h2
    have hab : lowThr G lam i j - lam i ≤ highThr G lam i j - lam i := by linarith
    have hmem : s ∈ segment ℝ (lowThr G lam i j - lam i) (highThr G lam i j - lam i) := by
      rw [segment_eq_Icc hab]; exact ⟨h1, h2⟩
    have := hconv.le_on_segment ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ hmem
    exact le_antisymm (this.trans (max_le hA hB)) (hlb s (by linarith) (by linarith))
  have hR1 : lam i < lowThr G lam i j → flowPotential G f1 < eqPotential G lam := by
    intro h
    refine pm_gt G hlam hij hf1 fun f hf => Or.inl ?_
    have := hf1m f hf
    have := mul_lt_mul_of_pos_right h hD
    linarith
  have hR3 : highThr G lam i j < lam i → flowPotential G f1 < eqPotential G lam := by
    intro h
    refine pm_gt G hlam hij hf1 fun f hf => Or.inr ?_
    have := hf2m f hf
    have := mul_lt_mul_of_pos_right h hD
    linarith
  refine ⟨flowPotential G f1, hPeq, hlb, hseg, hl0, hlh, hhs, fun f hf => ?_, fun f hf => ?_,
    hR1, hR3⟩
  · rw [← hf1e]; exact hf1m f hf
  · have := hf2m f hf
    linarith


end BayesRouting.VOI

open Filter Topology BayesRouting.VOI in
theorem pm_lemma5 {I : Type} [Fintype I] [DecidableEq I] {T : I → Type} [∀ i, Fintype (T i)]
    [∀ i, DecidableEq (T i)] [∀ i, Nonempty (T i)] {S E R : Type} [Fintype S] [Fintype E]
    [DecidableEq E] [Fintype R] [Nonempty R]
    (G : Game I T S E R) :
    ConvexOn ℝ (stdSimplex ℝ I) (eqPotential G) ∧
      (∀ lam ∈ stdSimplex ℝ I, ∀ d : I → ℝ, (∃ δ : ℝ, 0 < δ ∧ lam + δ • d ∈ stdSimplex ℝ I) →
        ∃ L : ℝ, Tendsto (fun ε : ℝ => (eqPotential G (lam + ε • d) - eqPotential G lam) / ε)
          (𝓝[>] 0) (𝓝 L)) ∧
      ∀ lam ∈ stdSimplex ℝ I, ∀ i j : I, i ≠ j → 0 < lam j →
        ∀ q : (k : I) → T k → R → ℝ, IsBWE G lam q →
          Tendsto (fun ε : ℝ => (eqPotential G (lam + ε • dir i j) - eqPotential G lam) / ε)
            (𝓝[>] 0) (𝓝 (-(G.D * relValue G q i j))) := by
  exact ⟨vg_convex G, vg_part2 G, vg_part3 G⟩

open BayesRouting.VOI in
theorem pm_prop3 {I : Type} [Fintype I] [DecidableEq I] {T : I → Type} [∀ i, Fintype (T i)]
    [∀ i, DecidableEq (T i)] [∀ i, Nonempty (T i)] {S E R : Type} [Fintype S] [Fintype E]
    [DecidableEq E] [Fintype R] [Nonempty R]
    (G : Game I T S E R) (i j : I) (hij : i ≠ j) :
    (∀ lam ∈ stdSimplex ℝ I, 0 < lam i → 0 < lam j →
      ∀ ε : ℝ, 0 < ε → 0 < (lam + ε • dir i j) j →
        ((lam i < lowThr G lam i j ∧ (lam + ε • dir i j) i < lowThr G lam i j) →
            eqPotential G (lam + ε • dir i j) < eqPotential G lam) ∧
        ((lowThr G lam i j ≤ lam i ∧ lam i ≤ highThr G lam i j ∧
            lowThr G lam i j ≤ (lam + ε • dir i j) i ∧ (lam + ε • dir i j) i ≤ highThr G lam i j) →
            eqPotential G (lam + ε • dir i j) = eqPotential G lam) ∧
        ((highThr G lam i j < lam i ∧ highThr G lam i j < (lam + ε • dir i j) i) →
            eqPotential G lam < eqPotential G (lam + ε • dir i j))) ∧
    (∀ lam ∈ stdSimplex ℝ I, 0 < lam i → 0 < lam j →
      ∀ q : (k : I) → T k → R → ℝ, IsBWE G lam q →
        ((lowThr G lam i j ≤ lam i ∧ lam i ≤ highThr G lam i j) →
            ∀ f ∈ pairOptimal G lam i j, edgeLoad G q = flowLoad G f) ∧
        ((∃ f ∈ pairOptimal G lam i j, edgeLoad G q = flowLoad G f) →
            lowThr G lam i j ≤ lam i ∧ lam i ≤ highThr G lam i j)) := by
  refine ⟨fun lam hlam hi hj ε hε hεj => ?_, fun lam hlam hi hj q hq => ?_⟩
  · obtain ⟨Φd, -, -, hseg, hl0, hlh, hhs, -, -, hR1, hR3⟩ := pm_facts G hij hlam
    have hconv := pm_conv_line G hij hlam
    rw [brv_pt_j hij] at hεj
    simp only [brv_pt_i hij]
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · obtain ⟨h1, h2⟩ := h
      have hA := (hseg (lowThr G lam i j - lam i) le_rfl (by linarith)).le
      have hslope := hconv.slope_mono_adjacent (x := 0) (y := ε) (z := lowThr G lam i j - lam i)
        ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ hε (by linarith)
      simp only [zero_smul, add_zero, sub_zero] at hslope
      have hlt0 := hR1 h1
      by_contra hcon
      have hcon' : eqPotential G lam ≤ eqPotential G (lam + ε • dir i j) := not_lt.mp hcon
      have h5 : 0 ≤ (eqPotential G (lam + ε • dir i j) - eqPotential G lam) / ε :=
        div_nonneg (by linarith) hε.le
      have hpos : 0 < lowThr G lam i j - lam i - ε := by linarith
      have h7 := (le_div_iff₀ hpos).mp (h5.trans hslope)
      linarith
    · obtain ⟨h1, h2, h3, h4⟩ := h
      rw [hseg ε (by linarith) (by linarith)]
      have h0 := hseg 0 (by linarith) (by linarith)
      simp only [zero_smul, add_zero] at h0
      rw [h0]
    · obtain ⟨h1, h2⟩ := h
      have hB := (hseg (highThr G lam i j - lam i) (by linarith) le_rfl).le
      have hslope := hconv.slope_mono_adjacent (x := highThr G lam i j - lam i) (y := 0) (z := ε)
        ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith) hε
      simp only [zero_smul, add_zero, sub_zero, zero_sub] at hslope
      have hlt0 := hR3 h1
      have hpos : 0 < (eqPotential G lam -
          eqPotential G (lam + (highThr G lam i j - lam i) • dir i j)) /
            -(highThr G lam i j - lam i) :=
        div_pos (by linarith) (by linarith)
      have h7 := (lt_div_iff₀ hε).mp (hpos.trans_le hslope)
      linarith
  · obtain ⟨Φd, hPeq, -, hseg, -, -, -, hlowb, hhighb, -, -⟩ := pm_facts G hij hlam
    have hmin := pm_bwe_min G hlam hq
    have hrf := pm_rf_pair G hlam hij hq.1
    have hD := G.D_pos
    have hopt : ∀ f ∈ pairOptimal G lam i j, potential G q = flowPotential G f →
        routeFlow q ∈ pairOptimal G lam i j := by
      intro f hf heq
      refine ⟨hrf, fun g hg => ?_⟩
      rw [show flowPotential G (routeFlow q) = potential G q from rfl, heq]
      exact hf.2 g hg
    refine ⟨fun h f hf => ?_, fun h => ?_⟩
    · obtain ⟨h1, h2⟩ := h
      have h0 := hseg 0 (by linarith) (by linarith)
      simp only [zero_smul, add_zero] at h0
      have hq' := hopt f hf (by rw [hmin, h0, hPeq f hf])
      exact pm_unique G lam i j hq' hf
    · obtain ⟨f, hf, hload⟩ := h
      have hpot : potential G q = flowPotential G f := by
        show ∑ s, ∑ e, ∑ t, G.prior s t * ∫ z in (0:ℝ)..(edgeLoad G q e t), G.cost s e z = _
        rw [hload]
        rfl
      have hq' := hopt f hf hpot
      have hi' := pm_rf_impact G hlam hq.1 i
      have hj' := pm_rf_impact G hlam hq.1 j
      have hl := hlowb _ hq'
      have hh := hhighb _ hq'
      constructor
      · exact le_of_mul_le_mul_right (by linarith) hD
      · exact le_of_mul_le_mul_right (by linarith) hD

/-! ### The direction `z^{ij}` -/

open BayesRouting.VOI in
lemma brv_dir_swap {I : Type} [DecidableEq I] (i j : I) : dir j i = - dir i j := by
  simp only [dir, neg_sub]

lemma brv_add_add {I : Type} (lam z : I → ℝ) (a b : ℝ) :
    lam + a • z + b • z = lam + (a + b) • z := by
  rw [add_smul, add_assoc]

/-! ### The thresholds depend only on `λ^{-ij}` -/

open BayesRouting.VOI in
lemma brv_thr {I : Type} [Fintype I] [DecidableEq I] {T : I → Type} [∀ i, Fintype (T i)]
    [∀ i, DecidableEq (T i)] [∀ i, Nonempty (T i)] {S E R : Type} [Fintype S] [Fintype E]
    [DecidableEq E] [Fintype R] [Nonempty R]
    (G : Game I T S E R) (i j : I) (lam lam' : I → ℝ)
    (h : ∀ k, k ≠ i → k ≠ j → lam' k = lam k) :
    lowThr G lam' i j = lowThr G lam i j ∧ highThr G lam' i j = highThr G lam i j := by
  have hr : restSize lam' i j = restSize lam i j := by
    unfold restSize
    refine Finset.sum_congr rfl (fun k hk => ?_)
    simp only [Finset.mem_erase] at hk
    exact h k hk.2.1 hk.1
  have hp : pairFeasible G lam' i j = pairFeasible G lam i j := by
    ext f
    simp only [pairFeasible, Set.mem_inter_iff, Set.mem_setOf_eq, hr]
    constructor
    · rintro ⟨hb, h1, h2⟩
      refine ⟨hb, fun k hki hkj => ?_, h2⟩
      rw [← h k hki hkj]; exact h1 k hki hkj
    · rintro ⟨hb, h1, h2⟩
      refine ⟨hb, fun k hki hkj => ?_, h2⟩
      rw [h k hki hkj]; exact h1 k hki hkj
  constructor <;> simp only [lowThr, highThr, pairOptimal, hp, hr]

/-! ### One-variable convex analysis -/

lemma brv_slope {φ : ℝ → ℝ} {S : Set ℝ} {c L t : ℝ} (hconv : ConvexOn ℝ S φ)
    (hS : Set.Icc 0 t ⊆ S) (h0 : φ 0 = c)
    (hL : Tendsto (fun ε => (φ ε - c) / ε) (𝓝[>] 0) (𝓝 L)) (ht : 0 < t) :
    L ≤ (φ t - c) / t := by
  apply le_of_tendsto hL
  filter_upwards [Ioo_mem_nhdsGT ht] with ε hε
  have := hconv.secant_mono (a := 0) (x := ε) (y := t) (hS ⟨le_refl 0, ht.le⟩)
    (hS ⟨hε.1.le, hε.2.le⟩) (hS ⟨ht.le, le_refl t⟩) (ne_of_gt hε.1) (ne_of_gt ht) hε.2.le
  simpa [h0] using this

lemma brv_lim_nonneg {φ : ℝ → ℝ} {c L : ℝ}
    (hL : Tendsto (fun ε => (φ ε - c) / ε) (𝓝[>] 0) (𝓝 L))
    (hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), c ≤ φ ε) : 0 ≤ L := by
  apply ge_of_tendsto hL
  filter_upwards [hev, self_mem_nhdsWithin] with ε hε hpos
  exact div_nonneg (by linarith) (le_of_lt hpos)

lemma brv_rcont {φ : ℝ → ℝ} {c L : ℝ}
    (hL : Tendsto (fun ε => (φ ε - c) / ε) (𝓝[>] 0) (𝓝 L)) :
    Tendsto φ (𝓝[>] 0) (𝓝 c) := by
  have h1 : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have h2 := (h1.mul hL).const_add c
  rw [zero_mul, add_zero] at h2
  apply h2.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hne : ε ≠ 0 := ne_of_gt hε
  field_simp
  ring

lemma brv_le_of_right {φ : ℝ → ℝ} {c b : ℝ} (hc : Tendsto φ (𝓝[>] 0) (𝓝 c)) (hb : 0 < b)
    (hlt : ∀ ε' ∈ Set.Ioo 0 b, φ ε' ≤ φ b) : c ≤ φ b := by
  apply le_of_tendsto hc
  filter_upwards [Ioo_mem_nhdsGT hb] with ε' h
  exact hlt ε' h

/-! ### Proposition 3 along the line `λ + s z^{ij}` -/

open BayesRouting.VOI in
lemma brv_V2pts {I : Type} [Fintype I] [DecidableEq I] {T : I → Type} [∀ i, Fintype (T i)]
    [∀ i, DecidableEq (T i)] [∀ i, Nonempty (T i)] {S E R : Type} [Fintype S] [Fintype E]
    [DecidableEq E] [Fintype R] [Nonempty R]
    (G : Game I T S E R) (i j : I) (hij : i ≠ j) (lam : I → ℝ) (hlam : lam ∈ stdSimplex ℝ I)
    (s t : ℝ) (hst : s < t) (hs : -lam i < s) (ht : t < lam j) :
    (lam i + t < lowThr G lam i j →
        eqPotential G (lam + t • dir i j) < eqPotential G (lam + s • dir i j)) ∧
    (lowThr G lam i j ≤ lam i + s → lam i + t ≤ highThr G lam i j →
        eqPotential G (lam + t • dir i j) = eqPotential G (lam + s • dir i j)) ∧
    (highThr G lam i j < lam i + s →
        eqPotential G (lam + s • dir i j) < eqPotential G (lam + t • dir i j)) := by
  set μ := lam + s • dir i j with hμ
  have hμmem : μ ∈ stdSimplex ℝ I := brv_mem hij hlam (by linarith) (by linarith)
  have hμi : μ i = lam i + s := brv_pt_i hij lam s
  have hμj : μ j = lam j - s := brv_pt_j hij lam s
  have hstep : μ + (t - s) • dir i j = lam + t • dir i j := by
    rw [hμ, brv_add_add]; congr 2; ring
  have hthr := brv_thr G i j lam μ (fun k hki hkj => brv_pt_other hki hkj lam s)
  have hV2 := (pm_prop3 G i j hij).1 μ hμmem
    (by rw [hμi]; linarith) (by rw [hμj]; linarith) (t - s) (by linarith)
    (by rw [hstep, brv_pt_j hij]; linarith)
  rw [hstep, hthr.1, hthr.2, hμi, brv_pt_i hij] at hV2
  obtain ⟨h1, h2, h3⟩ := hV2
  refine ⟨fun h => h1 ⟨by linarith, h⟩, fun ha hb => h2 ⟨ha, by linarith, by linarith, hb⟩,
    fun h => h3 ⟨h, by linarith⟩⟩

/-! ### The parent -/

open BayesRouting.VOI in
theorem solution {I : Type} [Fintype I] [DecidableEq I] {T : I → Type} [∀ i, Fintype (T i)]
    [∀ i, DecidableEq (T i)] [∀ i, Nonempty (T i)] {S E R : Type} [Fintype S] [Fintype E]
    [DecidableEq E] [Fintype R] [Nonempty R]
    (G : Game I T S E R) (i j : I) (hij : i ≠ j) :
    (∀ lam ∈ stdSimplex ℝ I, 0 < lam i → 0 < lam j →
      ∀ q : (k : I) → T k → R → ℝ, IsBWE G lam q →
        (lam i < lowThr G lam i j → 0 < relValue G q i j) ∧
        (lowThr G lam i j ≤ lam i → lam i ≤ highThr G lam i j → relValue G q i j = 0) ∧
        (highThr G lam i j < lam i → relValue G q i j < 0)) ∧
    (∀ lam ∈ stdSimplex ℝ I, 0 < lam i → 0 < lam j →
      ∀ ε : ℝ, 0 < ε → 0 < (lam + ε • dir i j) j →
        ∀ q q' : (k : I) → T k → R → ℝ, IsBWE G lam q → IsBWE G (lam + ε • dir i j) q' →
          relValue G q' i j ≤ relValue G q i j) := by
  obtain ⟨hconv, -, hder⟩ := pm_lemma5 G
  have hD := G.D_pos
  have hswap : ∀ (q : (k : I) → T k → R → ℝ), relValue G q j i = - relValue G q i j := by
    intro q; unfold relValue; ring
  have hsub : ∀ (lam : I → ℝ) (η : ℝ), lam + η • dir j i = lam + (-η) • dir i j := by
    intro lam η; rw [brv_dir_swap, smul_neg, neg_smul]
  refine ⟨?_, ?_⟩
  · intro lam hlam hi hj q hq
    set V := relValue G q i j with hV
    set g : ℝ → ℝ := fun s => eqPotential G (lam + s • dir i j) with hg
    set h : ℝ → ℝ := fun s => eqPotential G (lam + s • dir j i) with hh
    have hgh : ∀ s, h s = g (-s) := by intro s; simp only [hh, hg, hsub]
    have hg0 : g 0 = eqPotential G lam := by simp [hg]
    have hh0 : h 0 = eqPotential G lam := by simp [hh]
    have hR : Tendsto (fun s => (g s - eqPotential G lam) / s) (𝓝[>] 0) (𝓝 (-(G.D * V))) :=
      hder lam hlam i j hij hj q hq
    have hL : Tendsto (fun s => (h s - eqPotential G lam) / s) (𝓝[>] 0) (𝓝 (G.D * V)) := by
      have := hder lam hlam j i hij.symm hi q hq
      rw [hswap q, mul_neg, neg_neg] at this
      exact this
    have hgc : ConvexOn ℝ {s : ℝ | lam + s • dir i j ∈ stdSimplex ℝ I} g :=
      brv_line_convex hconv lam (dir i j)
    have hhc : ConvexOn ℝ {s : ℝ | lam + s • dir j i ∈ stdSimplex ℝ I} h :=
      brv_line_convex hconv lam (dir j i)
    have hgS : Set.Icc 0 (lam j) ⊆ {s : ℝ | lam + s • dir i j ∈ stdSimplex ℝ I} :=
      fun s hs => brv_mem hij hlam (by linarith [hs.1]) hs.2
    have hhS : Set.Icc 0 (lam i) ⊆ {s : ℝ | lam + s • dir j i ∈ stdSimplex ℝ I} :=
      fun s hs => brv_mem hij.symm hlam (by linarith [hs.1]) hs.2
    have P := brv_V2pts G i j hij lam hlam
    refine ⟨fun hl => ?_, fun hl hu => ?_, fun hu => ?_⟩
    · -- regime 1
      set t := min ((lowThr G lam i j - lam i) / 2) (lam j / 2) with ht
      have ht0 : 0 < t := lt_min (by linarith) (by linarith)
      have ht1 : t ≤ (lowThr G lam i j - lam i) / 2 := min_le_left _ _
      have ht2 : t ≤ lam j / 2 := min_le_right _ _
      have hdec : g t < g 0 := (P 0 t ht0 (by linarith) (by linarith)).1 (by linarith)
      have hsl := brv_slope hgc ((Set.Icc_subset_Icc_right (by linarith)).trans hgS) hg0 hR ht0
      have hneg : (g t - eqPotential G lam) / t < 0 :=
        div_neg_of_neg_of_pos (by linarith) ht0
      have : 0 < G.D * V := by linarith
      exact pos_of_mul_pos_right this hD.le
    · -- regime 2
      have hA : 0 ≤ -(G.D * V) := by
        apply brv_lim_nonneg hR
        rcases lt_or_eq_of_le hu with hu' | hu'
        · filter_upwards [Ioo_mem_nhdsGT (lt_min (sub_pos.mpr hu') (half_pos hj))] with ε hε
          have h1 : ε < highThr G lam i j - lam i := lt_of_lt_of_le hε.2 (min_le_left _ _)
          have h2 : ε < lam j / 2 := lt_of_lt_of_le hε.2 (min_le_right _ _)
          have := (P 0 ε hε.1 (by linarith) (by linarith)).2.1 (by linarith) (by linarith)
          rw [← hg0]; exact this.symm.le
        · filter_upwards [Ioo_mem_nhdsGT (half_pos hj)] with ε hε
          rw [← hg0]
          refine brv_le_of_right (hg0 ▸ brv_rcont hR) hε.1 (fun ε' hε' => ?_)
          exact ((P ε' ε hε'.2 (by linarith [hε'.1]) (by linarith [hε.2])).2.2
            (by rw [hu']; linarith [hε'.1])).le
      have hB : 0 ≤ G.D * V := by
        apply brv_lim_nonneg hL
        rcases lt_or_eq_of_le hl with hl' | hl'
        · filter_upwards [Ioo_mem_nhdsGT (lt_min (sub_pos.mpr hl') (half_pos hi))] with η hη
          have h1 : η < lam i - lowThr G lam i j := lt_of_lt_of_le hη.2 (min_le_left _ _)
          have h2 : η < lam i / 2 := lt_of_lt_of_le hη.2 (min_le_right _ _)
          have := (P (-η) 0 (by linarith [hη.1]) (by linarith) (by linarith)).2.1
            (by linarith) (by linarith)
          rw [hgh, ← hg0]; exact this.le
        · filter_upwards [Ioo_mem_nhdsGT (half_pos hi)] with η hη
          rw [← hh0]
          refine brv_le_of_right (hh0 ▸ brv_rcont hL) hη.1 (fun η' hη' => ?_)
          rw [hgh, hgh]
          exact ((P (-η) (-η') (by linarith [hη'.2]) (by linarith [hη.2])
            (by linarith [hη'.1])).1 (by rw [← hl']; linarith [hη'.1])).le
      have hDV : G.D * V = 0 := le_antisymm (by linarith) hB
      rcases mul_eq_zero.mp hDV with h0 | h0
      · exact absurd h0 hD.ne'
      · exact h0
    · -- regime 3
      set t := min ((lam i - highThr G lam i j) / 2) (lam i / 2) with ht
      have ht0 : 0 < t := lt_min (by linarith) (by linarith)
      have ht1 : t ≤ (lam i - highThr G lam i j) / 2 := min_le_left _ _
      have ht2 : t ≤ lam i / 2 := min_le_right _ _
      have hinc : g (-t) < g 0 := (P (-t) 0 (by linarith) (by linarith) (by linarith)).2.2
        (by linarith)
      have hsl := brv_slope hhc ((Set.Icc_subset_Icc_right (by linarith)).trans hhS) hh0 hL ht0
      rw [hgh] at hsl
      have hneg : (g (-t) - eqPotential G lam) / t < 0 :=
        div_neg_of_neg_of_pos (by linarith) ht0
      have : G.D * V < 0 := by linarith
      by_contra hc
      push_neg at hc
      have := mul_nonneg hD.le hc
      linarith
  · intro lam hlam hi hj ε hε hεj q q' hq hq'
    have hεj' : ε < lam j := by rw [brv_pt_j hij] at hεj; linarith
    set lam' := lam + ε • dir i j with hlam'
    have hlam'mem : lam' ∈ stdSimplex ℝ I := brv_mem hij hlam (by linarith) hεj'.le
    have hi' : 0 < lam' i := by rw [hlam', brv_pt_i hij]; linarith
    set g : ℝ → ℝ := fun s => eqPotential G (lam + s • dir i j) with hg
    set h : ℝ → ℝ := fun s => eqPotential G (lam' + s • dir j i) with hh
    have hg0 : g 0 = eqPotential G lam := by simp [hg]
    have hh0 : h 0 = eqPotential G lam' := by simp [hh]
    have hR : Tendsto (fun s => (g s - eqPotential G lam) / s) (𝓝[>] 0)
        (𝓝 (-(G.D * relValue G q i j))) := hder lam hlam i j hij hj q hq
    have hL : Tendsto (fun s => (h s - eqPotential G lam') / s) (𝓝[>] 0)
        (𝓝 (G.D * relValue G q' i j)) := by
      have := hder lam' hlam'mem j i hij.symm hi' q' hq'
      rw [hswap q', mul_neg, neg_neg] at this
      exact this
    have hgc : ConvexOn ℝ {s : ℝ | lam + s • dir i j ∈ stdSimplex ℝ I} g :=
      brv_line_convex hconv lam (dir i j)
    have hhc : ConvexOn ℝ {s : ℝ | lam' + s • dir j i ∈ stdSimplex ℝ I} h :=
      brv_line_convex hconv lam' (dir j i)
    have hgS : Set.Icc 0 ε ⊆ {s : ℝ | lam + s • dir i j ∈ stdSimplex ℝ I} :=
      fun s hs => brv_mem hij hlam (by linarith [hs.1]) (by linarith [hs.2])
    have hhS : Set.Icc 0 ε ⊆ {s : ℝ | lam' + s • dir j i ∈ stdSimplex ℝ I} := by
      intro s hs
      apply brv_mem hij.symm hlam'mem
      · rw [hlam', brv_pt_j hij]; linarith [hs.1]
      · rw [hlam', brv_pt_i hij]; linarith [hs.2]
    have s1 := brv_slope hgc hgS hg0 hR hε
    have s2 := brv_slope hhc hhS hh0 hL hε
    have hback : h ε = eqPotential G lam := by
      simp only [hh, hlam', hsub, brv_add_add, add_neg_cancel, zero_smul, add_zero]
    have hfwd : g ε = eqPotential G lam' := by simp only [hg, hlam']
    rw [hback] at s2
    rw [hfwd] at s1
    have e : (eqPotential G lam - eqPotential G lam') / ε =
        -((eqPotential G lam' - eqPotential G lam) / ε) := by ring
    have : G.D * relValue G q' i j ≤ G.D * relValue G q i j := by linarith
    exact le_of_mul_le_mul_left this hD
