-- Prove2me | solution 1 for CryptoMembership.PerfectInfo.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T08:04:48.201469+00:00
-- url     : https://prove2.me/submissions/d5b23781-240e-452a-9cb1-87ad2082fb34

import Mathlib
import Definitions.Def_CryptoMembership_PerfectInfo_Model
import Theorems.Thm_CryptoMembership_PerfectInfo_proposition_1_exp_utility
import Theorems.Thm_CryptoMembership_PerfectInfo_cutoff_optimality
import Theorems.Thm_CryptoMembership_PerfectInfo_eq15_equilibrium_iff
import Theorems.Thm_CryptoMembership_PerfectInfo_lhs15_log_concave_bell
import Theorems.Thm_CryptoMembership_PerfectInfo_eq15_root_count
import Theorems.Thm_CryptoMembership_PerfectInfo_eq15_root_statics

open CryptoMembership.PerfectInfo MeasureTheory ProbabilityTheory

namespace Prop2Red

/-- On the left of the maximiser, `lhs15` is strictly increasing. -/
theorem side_left (P : Params) (hP : P.Standing) (sHat : ℝ)
    (hmax : ∀ t, lhs15 P t ≤ lhs15 P sHat)
    {x y : ℝ} (hxy : x < y) (hy : y ≤ sHat) : lhs15 P x < lhs15 P y := by
  obtain ⟨hpos, hconc, -, -⟩ := lhs15_log_concave_bell P hP
  have hfx : Real.log (lhs15 P x) ≤ Real.log (lhs15 P sHat) :=
    Real.log_le_log (hpos x) (hmax x)
  rw [← Real.log_lt_log_iff (hpos x) (hpos y)]
  have hxs : x < sHat := lt_of_lt_of_le hxy hy
  rcases hy.lt_or_eq with hy | hy
  · have hd : 0 < sHat - x := by linarith
    have ha : 0 < (sHat - y) / (sHat - x) := div_pos (by linarith) hd
    have hb : 0 < (y - x) / (sHat - x) := div_pos (by linarith) hd
    have hab : (sHat - y) / (sHat - x) + (y - x) / (sHat - x) = 1 := by
      field_simp; ring
    have hcomb : (sHat - y) / (sHat - x) * x + (y - x) / (sHat - x) * sHat = y := by
      field_simp; ring
    have := hconc.2 (Set.mem_univ x) (Set.mem_univ sHat) hxs.ne ha hb hab
    simp only [smul_eq_mul] at this
    rw [hcomb] at this
    have k1 := mul_le_mul_of_nonneg_left hfx hb.le
    have k2 : (sHat - y) / (sHat - x) * Real.log (lhs15 P x) +
        (y - x) / (sHat - x) * Real.log (lhs15 P x) = Real.log (lhs15 P x) := by
      rw [← add_mul, hab, one_mul]
    linarith
  · rw [hy]
    have := hconc.2 (Set.mem_univ x) (Set.mem_univ sHat) hxs.ne
      (by norm_num : (0:ℝ) < 1/2) (by norm_num : (0:ℝ) < 1/2) (by norm_num)
    simp only [smul_eq_mul] at this
    have hm := Real.log_le_log (hpos _) (hmax ((1/2:ℝ) * x + 1/2 * sHat))
    linarith

/-- On the right of the maximiser, `lhs15` is strictly decreasing. -/
theorem side_right (P : Params) (hP : P.Standing) (sHat : ℝ)
    (hmax : ∀ t, lhs15 P t ≤ lhs15 P sHat)
    {x y : ℝ} (hx : sHat ≤ x) (hxy : x < y) : lhs15 P y < lhs15 P x := by
  obtain ⟨hpos, hconc, -, -⟩ := lhs15_log_concave_bell P hP
  have hfy : Real.log (lhs15 P y) ≤ Real.log (lhs15 P sHat) :=
    Real.log_le_log (hpos y) (hmax y)
  rw [← Real.log_lt_log_iff (hpos y) (hpos x)]
  have hys : sHat < y := lt_of_le_of_lt hx hxy
  rcases hx.lt_or_eq with hx | hx
  · have hd : 0 < y - sHat := by linarith
    have ha : 0 < (y - x) / (y - sHat) := div_pos (by linarith) hd
    have hb : 0 < (x - sHat) / (y - sHat) := div_pos (by linarith) hd
    have hab : (y - x) / (y - sHat) + (x - sHat) / (y - sHat) = 1 := by
      field_simp; ring
    have hcomb : (y - x) / (y - sHat) * sHat + (x - sHat) / (y - sHat) * y = x := by
      field_simp; ring
    have := hconc.2 (Set.mem_univ sHat) (Set.mem_univ y) hys.ne ha hb hab
    simp only [smul_eq_mul] at this
    rw [hcomb] at this
    have k1 := mul_le_mul_of_nonneg_left hfy ha.le
    have k2 : (y - x) / (y - sHat) * Real.log (lhs15 P y) +
        (x - sHat) / (y - sHat) * Real.log (lhs15 P y) = Real.log (lhs15 P y) := by
      rw [← add_mul, hab, one_mul]
    linarith
  · rw [← hx]
    have := hconc.2 (Set.mem_univ sHat) (Set.mem_univ y) hys.ne
      (by norm_num : (0:ℝ) < 1/2) (by norm_num : (0:ℝ) < 1/2) (by norm_num)
    simp only [smul_eq_mul] at this
    have hm := Real.log_le_log (hpos _) (hmax ((1/2:ℝ) * sHat + 1/2 * y))
    linarith

/-- Equilibrium price attached to a root `s` of (15). -/
noncomputable def priceOf (P : Params) (xi s : ℝ) : ℝ :=
  Real.exp (-(Real.sqrt (P.tauEps / P.tauE) * s) - xi - Real.log (1 - P.rho))

theorem eq_of_root (P : Params) (hP : P.Standing) (A xi s : ℝ)
    (hs : lhs15 P s = rhs15 P A xi) :
    IsEquilibrium P A xi (Set.Ici (A + s)) (priceOf P xi s) := by
  rw [eq15_equilibrium_iff P hP]
  refine ⟨Real.exp_pos _, by simpa using hs, ?_⟩
  rw [priceOf, Real.log_exp]; ring

theorem equilibria_eq_image (P : Params) (hP : P.Standing) (A xi : ℝ) :
    equilibria P A xi =
      (fun s => (Set.Ici (A + s), priceOf P xi s)) '' {s | lhs15 P s = rhs15 P A xi} := by
  ext ⟨B, p⟩
  constructor
  · intro h
    obtain ⟨a, rfl⟩ := (cutoff_optimality P hP A xi).2 B p h
    obtain ⟨hp, hl, hlog⟩ := (eq15_equilibrium_iff P hP A xi a p).1 h
    refine ⟨a - A, hl, ?_⟩
    simp only [Prod.mk.injEq]
    refine ⟨by congr 1; ring, ?_⟩
    rw [priceOf, ← Real.exp_log hp, hlog]; congr 1; ring
  · rintro ⟨s, hs, hEq⟩
    simp only [Prod.mk.injEq] at hEq
    obtain ⟨rfl, rfl⟩ := hEq
    exact eq_of_root P hP A xi s hs

theorem encard_equilibria (P : Params) (hP : P.Standing) (A xi : ℝ) :
    (equilibria P A xi).encard = {s | lhs15 P s = rhs15 P A xi}.encard := by
  rw [equilibria_eq_image P hP]
  apply Set.InjOn.encard_image
  intro s _ t _ h
  simp only [Prod.mk.injEq] at h
  have := Set.Ici_inj.1 h.1
  linarith

theorem rhs15_pos (P : Params) (A xi : ℝ) : 0 < rhs15 P A xi := Real.exp_pos _

/-- The lowest root lies to the left of the maximiser. -/
theorem lowest_le (P : Params) (hP : P.Standing) (sHat : ℝ)
    (hmax : ∀ t, lhs15 P t ≤ lhs15 P sHat)
    (hcount : ∀ R : ℝ, 0 < R →
        ({s : ℝ | lhs15 P s = R}.encard = 2 ↔ R < lhs15 P sHat))
    (R s : ℝ) (hR : 0 < R) (hs : lhs15 P s = R) (hmin : ∀ t, lhs15 P t = R → s ≤ t) :
    s ≤ sHat := by
  by_contra hcon
  push Not at hcon
  have hlt : R < lhs15 P sHat := hs ▸ side_right P hP sHat hmax le_rfl hcon
  obtain ⟨x, y, hxy, hset⟩ := Set.encard_eq_two.1 ((hcount R hR).2 hlt)
  have hsmem : s ∈ ({x, y} : Set ℝ) := hset ▸ hs
  -- find the other root t ≠ s
  obtain ⟨t, ht, hts⟩ : ∃ t, lhs15 P t = R ∧ t ≠ s := by
    rcases hsmem with h | h
    · refine ⟨y, ?_, by rw [h]; exact hxy.symm⟩
      have : y ∈ ({x, y} : Set ℝ) := by simp
      rw [← hset] at this; exact this
    · rw [Set.mem_singleton_iff] at h
      refine ⟨x, ?_, by rw [h]; exact hxy⟩
      have : x ∈ ({x, y} : Set ℝ) := by simp
      rw [← hset] at this; exact this
  have hst := hmin t ht
  have hst' : s < t := lt_of_le_of_ne hst (Ne.symm hts)
  have := side_right P hP sHat hmax hcon.le hst'
  rw [ht, hs] at this
  exact lt_irrefl _ this

/-- The highest root lies to the right of the maximiser. -/
theorem highest_ge (P : Params) (hP : P.Standing) (sHat : ℝ)
    (hmax : ∀ t, lhs15 P t ≤ lhs15 P sHat)
    (hcount : ∀ R : ℝ, 0 < R →
        ({s : ℝ | lhs15 P s = R}.encard = 2 ↔ R < lhs15 P sHat))
    (R s : ℝ) (hR : 0 < R) (hs : lhs15 P s = R) (hmaxr : ∀ t, lhs15 P t = R → t ≤ s) :
    sHat ≤ s := by
  by_contra hcon
  push Not at hcon
  have hlt : R < lhs15 P sHat := hs ▸ side_left P hP sHat hmax hcon le_rfl
  obtain ⟨x, y, hxy, hset⟩ := Set.encard_eq_two.1 ((hcount R hR).2 hlt)
  have hsmem : s ∈ ({x, y} : Set ℝ) := hset ▸ hs
  obtain ⟨t, ht, hts⟩ : ∃ t, lhs15 P t = R ∧ t ≠ s := by
    rcases hsmem with h | h
    · refine ⟨y, ?_, by rw [h]; exact hxy.symm⟩
      have : y ∈ ({x, y} : Set ℝ) := by simp
      rw [← hset] at this; exact this
    · rw [Set.mem_singleton_iff] at h
      refine ⟨x, ?_, by rw [h]; exact hxy⟩
      have : x ∈ ({x, y} : Set ℝ) := by simp
      rw [← hset] at this; exact this
  have hst := hmaxr t ht
  have hst' : t < s := lt_of_le_of_ne hst hts
  have := side_left P hP sHat hmax hst' hcon.le
  rw [ht, hs] at this
  exact lt_irrefl _ this

/-! ### Gaussian computations -/

instance epsLaw_prob (P : Params) : IsProbabilityMeasure (epsLaw P) := by
  unfold epsLaw; infer_instance

theorem endowLaw_eq_map (P : Params) (A : ℝ) :
    endowLaw P A = (epsLaw P).map (· + A) := by
  rw [endowLaw, epsLaw, gaussianReal_map_add_const, zero_add]

theorem epsLaw_pos_Ioo (P : Params) (hP : P.Standing) {x y : ℝ} (hxy : x < y) :
    (epsLaw P) (Set.Ioo x y) ≠ 0 := by
  have hv : (P.tauEps⁻¹).toNNReal ≠ 0 := by
    have : 0 < P.tauEps⁻¹ := inv_pos.2 hP.2.2.1
    intro h
    rw [Real.toNNReal_eq_zero] at h
    linarith
  intro h
  have h2 := gaussianReal_absolutelyContinuous' 0 hv h
  rw [Real.volume_Ioo] at h2
  simp at h2
  linarith

theorem buyerMass_Ici (P : Params) (A a : ℝ) :
    buyerMass P A (Set.Ici a) = (epsLaw P).real (Set.Ici (a - A)) := by
  rw [buyerMass, endowLaw_eq_map, measureReal_def, measureReal_def,
    Measure.map_apply (measurable_add_const A) measurableSet_Ici]
  congr 2
  ext y; simp

theorem buyerMass_strictAnti (P : Params) (hP : P.Standing) (A a A' a' : ℝ)
    (h : a' - A' < a - A) : buyerMass P A (Set.Ici a) < buyerMass P A' (Set.Ici a') := by
  rw [buyerMass_Ici, buyerMass_Ici]
  set s := a - A
  set s' := a' - A'
  have hunion : Set.Ici s' = Set.Ico s' s ∪ Set.Ici s := by
    ext y; simp only [Set.mem_Ici, Set.mem_union, Set.mem_Ico]
    constructor
    · intro hy; by_cases hys : y < s
      · exact Or.inl ⟨hy, hys⟩
      · exact Or.inr (not_lt.1 hys)
    · rintro (⟨hy, -⟩ | hy) <;> linarith
  rw [hunion, measureReal_union (Set.disjoint_left.2 fun y hy hy' => by
    simp only [Set.mem_Ico, Set.mem_Ici] at hy hy'; linarith) measurableSet_Ici]
  have : 0 < (epsLaw P).real (Set.Ico s' s) := by
    rw [measureReal_def]
    apply ENNReal.toReal_pos
    · intro h0
      exact epsLaw_pos_Ioo P hP h (measure_mono_null Set.Ioo_subset_Ico_self h0)
    · exact measure_ne_top _ _
  linarith

/-- The excess-utility integral g(s) = E[max(e^{(1-η)(ε - s)} - 1, 0)]. -/
noncomputable def gfun (P : Params) (s : ℝ) : ℝ :=
  ∫ y, max (Real.exp ((1 - P.eta) * (y - s)) - 1) 0 ∂(epsLaw P)

theorem gint (P : Params) (s : ℝ) :
    Integrable (fun y => max (Real.exp ((1 - P.eta) * (y - s)) - 1) 0) (epsLaw P) := by
  have hi : Integrable (fun y => Real.exp (-((1 - P.eta) * s)) * Real.exp ((1 - P.eta) * y))
      (epsLaw P) := (integrable_exp_mul_gaussianReal (1 - P.eta)).const_mul _
  refine hi.mono' ?_ ?_
  · exact (by fun_prop : Continuous fun y =>
      max (Real.exp ((1 - P.eta) * (y - s)) - 1) 0).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun y => ?_)
    rw [← Real.exp_add, Real.norm_eq_abs]
    have he : Real.exp ((1 - P.eta) * (y - s)) = Real.exp (-((1 - P.eta) * s) + (1 - P.eta) * y) := by
      congr 1; ring
    rw [abs_of_nonneg (le_max_right _ _), ← he]
    exact max_le (by linarith) (Real.exp_pos _).le

theorem gfun_nonneg (P : Params) (s : ℝ) : 0 ≤ gfun P s :=
  integral_nonneg (fun _ => le_max_right _ _)

theorem gfun_strictAnti (P : Params) (hP : P.Standing) {s s' : ℝ} (h : s < s') :
    gfun P s' < gfun P s := by
  have h1 : 0 < 1 - P.eta := by linarith [hP.2.1]
  rw [gfun, gfun, ← sub_pos, ← integral_sub (gint P s) (gint P s')]
  rw [integral_pos_iff_support_of_nonneg_ae]
  · apply pos_iff_ne_zero.2
    intro h0
    refine epsLaw_pos_Ioo P hP (lt_add_one s') (measure_mono_null ?_ h0)
    intro y hy
    rw [Function.mem_support]
    have hy1 : s' < y := hy.1
    have e1 : 0 < (1 - P.eta) * (y - s) := mul_pos h1 (by linarith)
    have e2 : (1 - P.eta) * (y - s') < (1 - P.eta) * (y - s) :=
      mul_lt_mul_of_pos_left (by linarith) h1
    have e3 := Real.exp_lt_exp.2 e2
    have e4 : 1 < Real.exp ((1 - P.eta) * (y - s)) := by
      have := Real.add_one_lt_exp (ne_of_gt e1); linarith
    have : max (Real.exp ((1 - P.eta) * (y - s')) - 1) 0 <
        max (Real.exp ((1 - P.eta) * (y - s)) - 1) 0 := by
      rw [max_eq_left (by linarith : (0:ℝ) ≤ Real.exp ((1 - P.eta) * (y - s)) - 1)]
      exact max_lt (by linarith) (by linarith)
    linarith
  · refine Filter.Eventually.of_forall (fun y => ?_)
    simp only [Pi.zero_apply, Pi.sub_apply, sub_nonneg]
    apply max_le_max _ le_rfl
    have : (1 - P.eta) * (y - s') ≤ (1 - P.eta) * (y - s) :=
      mul_le_mul_of_nonneg_left (by linarith) h1.le
    linarith [Real.exp_le_exp.2 this]
  · exact (gint P s).sub (gint P s')

theorem expUtility_eq (P : Params) (hP : P.Standing) (A xi a p : ℝ)
    (heq : IsEquilibrium P A xi (Set.Ici a) p) (x : ℝ) :
    expUtility P A (Set.Ici a) x = p * Real.exp ((1 - P.eta) * (x - a)) := by
  obtain ⟨hp, hl, hlog⟩ := (eq15_equilibrium_iff P hP A xi a p).1 heq
  rw [proposition_1_exp_utility P hP A x a]
  unfold lhs15 rhs15 at hl
  have harg : P.eta / Real.sqrt P.tauEps + Real.sqrt P.tauEps * (A - a) =
      P.eta / Real.sqrt P.tauEps - Real.sqrt P.tauEps * (a - A) := by ring
  rw [harg]
  have hPhi : Phi (P.eta / Real.sqrt P.tauEps - Real.sqrt P.tauEps * (a - A)) =
      Real.exp (-A - xi - P.eta ^ 2 / (2 * P.tauEps) - Real.log (1 - P.rho) -
        (1 - P.eta + Real.sqrt (P.tauEps / P.tauE)) * (a - A)) := by
    rw [Real.exp_sub, ← hl]
    field_simp
  rw [hPhi, ← Real.exp_log hp, hlog, ← Real.exp_add, ← Real.exp_add]
  congr 1; ring

theorem exAnte_eq (P : Params) (hP : P.Standing) (A xi a p : ℝ)
    (heq : IsEquilibrium P A xi (Set.Ici a) p) :
    exAnteUtility P A (Set.Ici a) p = p * gfun P (a - A) := by
  have hp := heq.price_pos
  unfold exAnteUtility
  simp_rw [expUtility_eq P hP A xi a p heq]
  have : ∀ x, max (p * Real.exp ((1 - P.eta) * (x - a)) - p) 0 =
      p * max (Real.exp ((1 - P.eta) * (x - a)) - 1) 0 := by
    intro x
    rw [mul_max_of_nonneg _ _ hp.le, mul_zero]; congr 1; ring
  simp_rw [this]
  rw [integral_const_mul, gfun, endowLaw_eq_map,
    integral_map (measurable_add_const A).aemeasurable
      (by fun_prop : Continuous fun x =>
        max (Real.exp ((1 - P.eta) * (x - a)) - 1) 0).aestronglyMeasurable]
  congr 1
  apply integral_congr_ae
  refine Filter.Eventually.of_forall (fun y => ?_)
  simp only
  congr 3; ring

theorem price_eq (P : Params) (hP : P.Standing) (A xi a p : ℝ)
    (heq : IsEquilibrium P A xi (Set.Ici a) p) :
    Real.log p = -(Real.sqrt (P.tauEps / P.tauE) * (a - A)) - xi - Real.log (1 - P.rho) := by
  obtain ⟨-, -, hlog⟩ := (eq15_equilibrium_iff P hP A xi a p).1 heq
  rw [hlog]; ring

theorem root_of_eq (P : Params) (hP : P.Standing) (A xi a p : ℝ)
    (heq : IsEquilibrium P A xi (Set.Ici a) p) : lhs15 P (a - A) = rhs15 P A xi :=
  ((eq15_equilibrium_iff P hP A xi a p).1 heq).2.1

/-- The cutoff of a high-price equilibrium is the lowest root. -/
theorem high_min (P : Params) (hP : P.Standing) (A xi a p : ℝ) (h : IsHighPriceEq P A xi a p) :
    ∀ t, lhs15 P t = rhs15 P A xi → a - A ≤ t := by
  intro t ht
  have := h.2 _ _ (eq_of_root P hP A xi t ht)
  linarith

theorem low_max (P : Params) (hP : P.Standing) (A xi a p : ℝ) (h : IsLowPriceEq P A xi a p) :
    ∀ t, lhs15 P t = rhs15 P A xi → t ≤ a - A := by
  intro t ht
  have := h.2 _ _ (eq_of_root P hP A xi t ht)
  linarith

end Prop2Red

open Prop2Red in
theorem solution (P : Params) (hP : P.Standing) :
    ∃ K : ℝ,
      (∀ A xi : ℝ, (equilibria P A xi).encard = 2 ↔ K < A + xi) ∧
      (∀ A xi : ℝ, (equilibria P A xi).encard = 1 ↔ A + xi = K) ∧
      (∀ A xi : ℝ, equilibria P A xi = ∅ ↔ A + xi < K) ∧
      (∀ (A xi : ℝ) (B : Set ℝ) (price : ℝ), IsEquilibrium P A xi B price →
          ∃ a : ℝ, B = Set.Ici a ∧ lhs15 P (a - A) = rhs15 P A xi) ∧
      (∀ A xi a : ℝ, lhs15 P (a - A) = rhs15 P A xi →
          ∃ price : ℝ, IsEquilibrium P A xi (Set.Ici a) price) ∧
      (∀ A xi a price : ℝ, IsEquilibrium P A xi (Set.Ici a) price →
          Real.log price = Real.sqrt (P.tauEps / P.tauE) * (A - a) - xi - Real.log (1 - P.rho)) ∧
      (∀ xi A A' a price a' price' : ℝ, A < A' →
          IsHighPriceEq P A xi a price → IsHighPriceEq P A' xi a' price' →
          price < price' ∧
          devRevenue P A (Set.Ici a) price < devRevenue P A' (Set.Ici a') price' ∧
          exAnteUtility P A (Set.Ici a) price < exAnteUtility P A' (Set.Ici a') price' ∧
          buyerMass P A (Set.Ici a) < buyerMass P A' (Set.Ici a')) ∧
      (∀ xi A A' a price a' price' : ℝ, A < A' →
          IsLowPriceEq P A xi a price → IsLowPriceEq P A' xi a' price' →
          price' < price ∧
          devRevenue P A' (Set.Ici a') price' < devRevenue P A (Set.Ici a) price ∧
          exAnteUtility P A' (Set.Ici a') price' < exAnteUtility P A (Set.Ici a) price ∧
          buyerMass P A' (Set.Ici a') < buyerMass P A (Set.Ici a)) ∧
      (∀ A xi xi' a price a' price' : ℝ, xi < xi' →
          IsHighPriceEq P A xi a price → IsHighPriceEq P A xi' a' price' →
          buyerMass P A (Set.Ici a) < buyerMass P A (Set.Ici a')) ∧
      (∀ A xi xi' a price a' price' : ℝ, xi < xi' →
          IsLowPriceEq P A xi a price → IsLowPriceEq P A xi' a' price' →
          buyerMass P A (Set.Ici a') < buyerMass P A (Set.Ici a)) ∧
      (∀ xi : ℝ, ∃ A₀ : ℝ, ∀ A : ℝ, A < A₀ → equilibria P A xi = ∅) ∧
      (∀ A : ℝ, ∃ ξ₀ : ℝ, ∀ xi : ℝ, xi < ξ₀ → equilibria P A xi = ∅) := by
  obtain ⟨sHat, hmax, hcount⟩ := eq15_root_count P hP
  obtain ⟨hpos, -, -, -⟩ := lhs15_log_concave_bell P hP
  obtain ⟨hrhs, hstat⟩ := eq15_root_statics P hP
  obtain ⟨hstatL, hstatR⟩ := hstat sHat hmax
  set M := lhs15 P sHat with hM
  have hMpos : 0 < M := hpos sHat
  set q := P.eta ^ 2 / (2 * P.tauEps) - (-Real.log (1 - P.rho)) with hq
  set K := -Real.log M - P.eta ^ 2 / (2 * P.tauEps) - Real.log (1 - P.rho) with hK
  have hrhs_def : ∀ A xi, rhs15 P A xi =
      Real.exp (-A - xi - P.eta ^ 2 / (2 * P.tauEps) - Real.log (1 - P.rho)) := fun _ _ => rfl
  -- R < M ↔ K < A + xi
  have hlt : ∀ A xi, rhs15 P A xi < M ↔ K < A + xi := by
    intro A xi
    rw [hrhs_def, ← Real.lt_log_iff_exp_lt hMpos]
    constructor <;> intro h <;> linarith
  have heqK : ∀ A xi, rhs15 P A xi = M ↔ A + xi = K := by
    intro A xi
    rw [hrhs_def]
    constructor
    · intro h
      have := congrArg Real.log h
      rw [Real.log_exp] at this
      linarith
    · intro h
      rw [← Real.exp_log hMpos]; congr 1; linarith
  have hgt : ∀ A xi, M < rhs15 P A xi ↔ A + xi < K := by
    intro A xi
    constructor
    · intro h
      by_contra h'
      push Not at h'
      rcases h'.lt_or_eq with h' | h'
      · linarith [(hlt A xi).2 h']
      · linarith [(heqK A xi).2 h'.symm]
    · intro h
      by_contra h'
      push Not at h'
      rcases h'.lt_or_eq with h' | h'
      · linarith [(hlt A xi).1 h']
      · linarith [(heqK A xi).1 h']
  have hcount2 : ∀ R : ℝ, 0 < R →
      ({s : ℝ | lhs15 P s = R}.encard = 2 ↔ R < lhs15 P sHat) := fun R hR => (hcount R hR).1
  -- comparison of equilibrium objects through the roots
  have hcmp : ∀ A xi a p A' xi' a' p', IsEquilibrium P A xi (Set.Ici a) p →
      IsEquilibrium P A' xi' (Set.Ici a') p' → xi = xi' → a' - A' < a - A →
      p < p' ∧ devRevenue P A (Set.Ici a) p < devRevenue P A' (Set.Ici a') p' ∧
      exAnteUtility P A (Set.Ici a) p < exAnteUtility P A' (Set.Ici a') p' ∧
      buyerMass P A (Set.Ici a) < buyerMass P A' (Set.Ici a') := by
    intro A xi a p A' xi' a' p' h h' hxi hs
    subst hxi
    have hp := h.price_pos
    have hp' := h'.price_pos
    have hl := price_eq P hP A xi a p h
    have hl' := price_eq P hP A' xi a' p' h'
    have hc : 0 < Real.sqrt (P.tauEps / P.tauE) :=
      Real.sqrt_pos.2 (div_pos hP.2.2.1 hP.2.2.2.1)
    have hpp : p < p' := by
      rw [← Real.log_lt_log_iff hp hp', hl, hl']
      nlinarith
    have hm := buyerMass_strictAnti P hP A a A' a' hs
    have hm0 : 0 ≤ buyerMass P A (Set.Ici a) := measureReal_nonneg
    have hg := gfun_strictAnti P hP hs
    have hg0 := gfun_nonneg P (a - A)
    refine ⟨hpp, ?_, ?_, hm⟩
    · unfold devRevenue
      have hr := hP.2.2.2.2.1
      have : buyerMass P A (Set.Ici a) * p < buyerMass P A' (Set.Ici a') * p' := by
        nlinarith
      rw [mul_assoc, mul_assoc]
      exact mul_lt_mul_of_pos_left this hr
    · rw [exAnte_eq P hP A xi a p h, exAnte_eq P hP A' xi a' p' h']
      nlinarith
  have hlow : ∀ A xi a p, IsHighPriceEq P A xi a p → a - A ≤ sHat := fun A xi a p h =>
    lowest_le P hP sHat hmax hcount2 (rhs15 P A xi) (a - A) (rhs15_pos P A xi)
      (root_of_eq P hP A xi a p h.1) (high_min P hP A xi a p h)
  have hhigh : ∀ A xi a p, IsLowPriceEq P A xi a p → sHat ≤ a - A := fun A xi a p h =>
    highest_ge P hP sHat hmax hcount2 (rhs15 P A xi) (a - A) (rhs15_pos P A xi)
      (root_of_eq P hP A xi a p h.1) (low_max P hP A xi a p h)
  refine ⟨K, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro A xi
    rw [encard_equilibria P hP, (hcount _ (rhs15_pos P A xi)).1, hlt]
  · intro A xi
    rw [encard_equilibria P hP, (hcount _ (rhs15_pos P A xi)).2.1, heqK]
  · intro A xi
    rw [← Set.encard_eq_zero, encard_equilibria P hP, (hcount _ (rhs15_pos P A xi)).2.2, hgt]
  · intro A xi B p h
    obtain ⟨a, rfl⟩ := (cutoff_optimality P hP A xi).2 B p h
    exact ⟨a, rfl, root_of_eq P hP A xi a p h⟩
  · intro A xi a h
    refine ⟨priceOf P xi (a - A), ?_⟩
    have := eq_of_root P hP A xi (a - A) h
    simpa using this
  · intro A xi a p h
    exact ((eq15_equilibrium_iff P hP A xi a p).1 h).2.2
  · intro xi A A' a p a' p' hAA h h'
    have hR : rhs15 P A' xi < rhs15 P A xi := hrhs A xi A' xi (by linarith)
    have hs : a' - A' < a - A :=
      hstatL _ _ _ _ (rhs15_pos P A' xi) hR (root_of_eq P hP A xi a p h.1)
        (root_of_eq P hP A' xi a' p' h'.1) (hlow A xi a p h) (hlow A' xi a' p' h')
    exact hcmp A xi a p A' xi a' p' h.1 h'.1 rfl hs
  · intro xi A A' a p a' p' hAA h h'
    have hR : rhs15 P A' xi < rhs15 P A xi := hrhs A xi A' xi (by linarith)
    have hs : a - A < a' - A' :=
      hstatR _ _ _ _ (rhs15_pos P A' xi) hR (root_of_eq P hP A xi a p h.1)
        (root_of_eq P hP A' xi a' p' h'.1) (hhigh A xi a p h) (hhigh A' xi a' p' h')
    exact hcmp A' xi a' p' A xi a p h'.1 h.1 rfl hs
  · intro A xi xi' a p a' p' hxx h h'
    have hR : rhs15 P A xi' < rhs15 P A xi := hrhs A xi A xi' (by linarith)
    have hs : a' - A < a - A :=
      hstatL _ _ _ _ (rhs15_pos P A xi') hR (root_of_eq P hP A xi a p h.1)
        (root_of_eq P hP A xi' a' p' h'.1) (hlow A xi a p h) (hlow A xi' a' p' h')
    exact buyerMass_strictAnti P hP A a A a' hs
  · intro A xi xi' a p a' p' hxx h h'
    have hR : rhs15 P A xi' < rhs15 P A xi := hrhs A xi A xi' (by linarith)
    have hs : a - A < a' - A :=
      hstatR _ _ _ _ (rhs15_pos P A xi') hR (root_of_eq P hP A xi a p h.1)
        (root_of_eq P hP A xi' a' p' h'.1) (hhigh A xi a p h) (hhigh A xi' a' p' h')
    exact buyerMass_strictAnti P hP A a' A a hs
  · intro xi
    refine ⟨K - xi, fun A hA => ?_⟩
    rw [← Set.encard_eq_zero, encard_equilibria P hP, (hcount _ (rhs15_pos P A xi)).2.2, hgt]
    linarith
  · intro A
    refine ⟨K - A, fun xi hxi => ?_⟩
    rw [← Set.encard_eq_zero, encard_equilibria P hP, (hcount _ (rhs15_pos P A xi)).2.2, hgt]
    linarith
