-- Prove2me | solution 1 for BayesRouting.VOI.eqPotential_convex_dirDeriv
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-10T00:38:57.677047+00:00
-- url     : https://prove2.me/submissions/7fa1d4a0-4d65-45e0-be3e-37d8127acb89

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

end BayesRouting.VOI

open Filter Topology BayesRouting.VOI in
theorem solution {I : Type} [Fintype I] [DecidableEq I] {T : I → Type} [∀ i, Fintype (T i)]
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
