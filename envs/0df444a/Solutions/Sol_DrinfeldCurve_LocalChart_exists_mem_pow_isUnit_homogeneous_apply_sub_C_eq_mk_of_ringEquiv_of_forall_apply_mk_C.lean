-- Prove2me | solution 1 for DrinfeldCurve.LocalChart.exists_mem_pow_isUnit_homogeneous_apply_sub_C_eq_mk_of_ringEquiv_of_forall_apply_mk_C
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/dc452e6f-90e3-52fe-a4db-ef82abd90295

import Mathlib
import Definitions.Def_DrinfeldCurve_LocalChart
import Theorems.Thm_MvPowerSeries_mem_span_X_pow_iff_forall_coeff_eq_zero_of_degree_lt
import Theorems.Thm_DrinfeldCurve_LocalChart_coeff_mem_span_of_eq_add_rel_mul_of_forall_coeff_eq_zero
import Theorems.Thm_DrinfeldCurve_LocalChart_exists_apply_mk_X_eq_mk_linearPart_rational_of_ringEquiv_of_forall_apply_mk_C
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DrinfeldCurve_LocalChart_exists_mem_pow_isUnit_homogeneous_apply_sub_C_eq_mk_of_ringEquiv_of_forall_apply_mk_C

set_option autoImplicit false

open IsLocalRing

namespace DrinfeldCurve
p2m_export "DrinfeldCurve" "LocalChart.drinfeldForm mk mk_surjective x y relation LocalChart.coeff_mem_span_of_eq_add_rel_mul_of_forall_coeff_eq_zero LocalChart.exists_apply_mk_X_eq_mk_linearPart_rational_of_ringEquiv_of_forall_apply_mk_C"
namespace LocalChart
p2m_export "DrinfeldCurve.LocalChart" "drinfeldForm coeff_mem_span_of_eq_add_rel_mul_of_forall_coeff_eq_zero exists_apply_mk_X_eq_mk_linearPart_rational_of_ringEquiv_of_forall_apply_mk_C"
namespace HasseTransportAux
p2m_open "DrinfeldCurve.LocalChart DrinfeldCurve"

section Graded

variable (W : Type) [CommRing W]

noncomputable abbrev nd (e i : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (e - i)

omit W in
@[scoped simp] theorem nd_zero (e i : ℕ) : nd e i 0 = i := by simp [nd]

omit W in
@[scoped simp] theorem nd_one (e i : ℕ) : nd e i 1 = e - i := by simp [nd]

omit W in
theorem eq_nd (n : Fin 2 →₀ ℕ) : n = nd (n 0 + n 1) (n 0) := by
  ext j
  fin_cases j <;> simp [nd]

omit W in
theorem nd_injOn (e : ℕ) : Set.InjOn (nd e) ↑(Finset.range (e + 1)) := by
  intro i _ j _ h
  have := congrArg (fun n : Fin 2 →₀ ℕ => n 0) h
  simpa using this

theorem coeff_eq_zero_of_mem_pow (e : ℕ) (g : MvPowerSeries (Fin 2) W)
    (hg : g ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ e)
    (n : Fin 2 →₀ ℕ) (hn : n 0 + n 1 < e) : MvPowerSeries.coeff n g = 0 :=
  (MvPowerSeries.mem_span_X_pow_iff_forall_coeff_eq_zero_of_degree_lt W e g).mp hg n hn

theorem mem_pow_of_coeff_eq_zero (e : ℕ) (g : MvPowerSeries (Fin 2) W)
    (hg : ∀ n : Fin 2 →₀ ℕ, n 0 + n 1 < e → MvPowerSeries.coeff n g = 0) :
    g ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ e :=
  (MvPowerSeries.mem_span_X_pow_iff_forall_coeff_eq_zero_of_degree_lt W e g).mpr hg

theorem mem_span_X_of_coeff_zero (g : MvPowerSeries (Fin 2) W)
    (hg : MvPowerSeries.coeff (0 : Fin 2 →₀ ℕ) g = 0) :
    g ∈ Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1} := by
  rw [← pow_one (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1})]
  refine mem_pow_of_coeff_eq_zero W 1 g fun n hn => ?_
  have : n = 0 := by
    ext j; fin_cases j <;> simp <;> omega
  rw [this]; exact hg

theorem pow_mul_pow_mem_pow (x y : MvPowerSeries (Fin 2) W)
    (hx : x ∈ Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1})
    (hy : y ∈ Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1})
    (i j e : ℕ) (he : i + j = e) :
    x ^ i * y ^ j ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ e := by
  have := Ideal.mul_mem_mul (Ideal.pow_mem_pow hx i) (Ideal.pow_mem_pow hy j)
  rwa [← pow_add, he] at this

noncomputable def low (e : ℕ) (g : MvPowerSeries (Fin 2) W) : MvPowerSeries (Fin 2) W :=
  ∑ i ∈ Finset.range (e + 1), MvPowerSeries.monomial (nd e i) (MvPowerSeries.coeff (nd e i) g)

theorem coeff_low (e : ℕ) (g : MvPowerSeries (Fin 2) W) (n : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff n (low W e g) = if n 0 + n 1 = e then MvPowerSeries.coeff n g else 0 := by
  classical
  rw [low, map_sum]
  simp only [MvPowerSeries.coeff_monomial]
  by_cases h : n 0 + n 1 = e
  · rw [if_pos h, Finset.sum_eq_single (n 0)]
    · have hn : n = nd e (n 0) := by
        have := eq_nd n; rwa [h] at this
      rw [if_pos hn, ← hn]
    · intro i _ hne
      rw [if_neg]
      intro hni
      apply hne
      have := congrArg (fun m : Fin 2 →₀ ℕ => m 0) hni
      simp at this
      exact this.symm
    · intro hn0
      exfalso; apply hn0
      simp only [Finset.mem_range]; omega
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [if_neg]
    intro hni
    apply h
    simp only [Finset.mem_range] at hi
    rw [hni, nd_zero, nd_one]; omega

theorem sub_low_mem_pow (e : ℕ) (g : MvPowerSeries (Fin 2) W)
    (hg : ∀ n : Fin 2 →₀ ℕ, n 0 + n 1 < e → MvPowerSeries.coeff n g = 0) :
    g - low W e g ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (e + 1) := by
  refine mem_pow_of_coeff_eq_zero W (e + 1) _ fun n hn => ?_
  rw [map_sub, coeff_low]
  split_ifs with h
  · exact sub_self _
  · rw [hg n (by omega), sub_zero]

theorem low_mem_pow (e : ℕ) (g : MvPowerSeries (Fin 2) W) :
    low W e g ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ e := by
  refine mem_pow_of_coeff_eq_zero W e _ fun n hn => ?_
  rw [coeff_low, if_neg (by omega)]

theorem monomial_nd_eq (e i : ℕ) (c : W) :
    MvPowerSeries.monomial (nd e i) c =
      MvPowerSeries.C c * MvPowerSeries.X 0 ^ i * MvPowerSeries.X 1 ^ (e - i) := by
  rw [MvPowerSeries.X_pow_eq, MvPowerSeries.X_pow_eq, ← MvPowerSeries.monomial_zero_eq_C_apply,
    MvPowerSeries.monomial_mul_monomial, MvPowerSeries.monomial_mul_monomial]
  simp [nd]

theorem low_eq_sum_C_mul (e : ℕ) (g : MvPowerSeries (Fin 2) W) :
    low W e g = ∑ i ∈ Finset.range (e + 1),
      MvPowerSeries.C (MvPowerSeries.coeff (nd e i) g) * MvPowerSeries.X 0 ^ i * MvPowerSeries.X 1 ^ (e - i) := by
  unfold low
  exact Finset.sum_congr rfl fun i _ => monomial_nd_eq W e i _

end Graded

theorem ne_zero_of_maximalIdeal_eq (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    (π : W) (hπ : maximalIdeal W = Ideal.span {π}) : π ≠ 0 := by
  intro h
  apply IsDiscreteValuationRing.not_a_field (R := W)
  rw [hπ, h, Ideal.span_singleton_zero]

theorem coeff_zero_eq_zero_of_sub_drinfeldForm_mem (q : ℕ) [Fact q.Prime] (W : Type) [CommRing W]
    (f : MvPowerSeries (Fin 2) W)
    (hf : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈
      (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (q + 2)) :
    MvPowerSeries.coeff (0 : Fin 2 →₀ ℕ) f = 0 := by
  classical
  have h1 := (MvPowerSeries.mem_span_X_pow_iff_forall_coeff_eq_zero_of_degree_lt W (q + 2) _).mp hf 0 (by simp)
  have e1 : (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1 ^ q =
      MvPowerSeries.monomial (Finsupp.single 0 1 + Finsupp.single 1 q) 1 := by
    rw [MvPowerSeries.X_pow_eq, MvPowerSeries.X_def, MvPowerSeries.monomial_mul_monomial, one_mul]
  have e2 : (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) ^ q * MvPowerSeries.X 1 =
      MvPowerSeries.monomial (Finsupp.single 0 q + Finsupp.single 1 1) 1 := by
    rw [MvPowerSeries.X_pow_eq, MvPowerSeries.X_def, MvPowerSeries.monomial_mul_monomial, one_mul]
  have h2 : MvPowerSeries.coeff (0 : Fin 2 →₀ ℕ) (DrinfeldCurve.LocalChart.drinfeldForm q W) = 0 := by
    unfold DrinfeldCurve.LocalChart.drinfeldForm
    rw [e1, e2, map_sub, MvPowerSeries.coeff_monomial, MvPowerSeries.coeff_monomial, if_neg, if_neg, sub_zero]
    · intro hn
      have := congrArg (fun n : Fin 2 →₀ ℕ => n 1) hn
      simp at this
    · intro hn
      have := congrArg (fun n : Fin 2 →₀ ℕ => n 0) hn
      simp at this
  rw [map_sub, h2, sub_zero] at h1
  exact h1

theorem memSpanX_iff_coeff_zero_eq_zero (W : Type) [CommRing W] (g : MvPowerSeries (Fin 2) W) :
    g ∈ Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1} ↔
      MvPowerSeries.coeff (0 : Fin 2 →₀ ℕ) g = 0 := by
  have := MvPowerSeries.mem_span_X_pow_iff_forall_coeff_eq_zero_of_degree_lt W 1 g
  rw [pow_one] at this
  rw [this]
  constructor
  · intro h; exact h 0 (by simp)
  · intro h n hn
    have : n = 0 := by
      ext i; fin_cases i <;> simp <;> omega
    rw [this]; exact h

theorem mem_map_span_X_iff_not_isUnit (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    (π : W) (hπ : maximalIdeal W = Ideal.span {π})
    (f u v : MvPowerSeries (Fin 2) W) (hv : IsUnit v)
    (hf : MvPowerSeries.coeff (0 : Fin 2 →₀ ℕ) f = 0)
    (x : MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C π * v - f * u}) :
    x ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}).map
        (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C π * v - f * u})) ↔ ¬ IsUnit x := by
  classical
  have hπm : π ∈ maximalIdeal W := by rw [hπ]; exact Ideal.mem_span_singleton_self _
  constructor
  ·
    intro hx hunit
    obtain ⟨g, hg, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hx
    have hg0 : MvPowerSeries.coeff (0 : Fin 2 →₀ ℕ) g = 0 := (memSpanX_iff_coeff_zero_eq_zero W g).mp hg
    set φ : MvPowerSeries (Fin 2) W →+* ResidueField W := (residue W).comp MvPowerSeries.constantCoeff with hφ
    have hker : ∀ a ∈ Ideal.span {MvPowerSeries.C π * v - f * u}, φ a = 0 := by
      intro a ha
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      have hf' : MvPowerSeries.constantCoeff f = 0 := by
        rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]; exact hf
      simp only [hφ, RingHom.coe_comp, Function.comp_apply, map_mul, map_sub, MvPowerSeries.constantCoeff_C, hf']
      rw [(residue_eq_zero_iff π).mpr hπm]; simp
    have h1 := hunit.map (Ideal.Quotient.lift _ φ hker)
    rw [Ideal.Quotient.lift_mk] at h1
    simp only [hφ, RingHom.coe_comp, Function.comp_apply] at h1
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hg0, map_zero] at h1
    exact not_isUnit_zero h1
  ·
    intro hx
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hc : MvPowerSeries.constantCoeff g ∈ maximalIdeal W := by
      rw [mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      exact hx ((MvPowerSeries.isUnit_iff_constantCoeff.mpr hu).map _)
    rw [hπ] at hc
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hc
    obtain ⟨vU, hvU⟩ := hv

    have hfI : f ∈ Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1} :=
      (memSpanX_iff_coeff_zero_eq_zero W f).mpr hf
    have hCπ : Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C π * v - f * u}) (MvPowerSeries.C π) ∈
        (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}).map
          (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C π * v - f * u})) := by
      have e : Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C π * v - f * u}) (MvPowerSeries.C π) =
          Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C π * v - f * u}) (f * u * ↑vU⁻¹) := by
        rw [Ideal.Quotient.eq]
        refine Ideal.mem_span_singleton'.mpr ⟨↑vU⁻¹, ?_⟩
        have hvv : v * ↑vU⁻¹ = 1 := by rw [← hvU]; exact Units.mul_inv vU
        linear_combination (MvPowerSeries.C π) * hvv
      rw [e]
      exact Ideal.mem_map_of_mem _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hfI))
    have hgsplit : g = (g - MvPowerSeries.C (MvPowerSeries.constantCoeff g)) + MvPowerSeries.C w * MvPowerSeries.C π := by
      rw [← map_mul, hw]; ring
    have hgI : g - MvPowerSeries.C (MvPowerSeries.constantCoeff g) ∈
        Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1} :=
      (memSpanX_iff_coeff_zero_eq_zero W _).mpr (by
        rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]; simp)
    rw [hgsplit, map_add, map_mul]
    exact Ideal.add_mem _ (Ideal.mem_map_of_mem _ hgI) (Ideal.mul_mem_left _ _ hCπ)

theorem map_mem_pow_of_mem_pow {A B : Type} [CommRing A] [CommRing B] (ψ : A ≃+* B)
    (J₁ : Ideal A) (J₂ : Ideal B)
    (h₁ : ∀ x, x ∈ J₁ → ¬ IsUnit x) (h₂ : ∀ y, ¬ IsUnit y → y ∈ J₂)
    (e : ℕ) (x : A) (hx : x ∈ J₁ ^ e) : ψ x ∈ J₂ ^ e := by
  have hle : J₁.map ψ.toRingHom ≤ J₂ := by
    intro y hy
    obtain ⟨x', hx', rfl⟩ := (Ideal.mem_map_iff_of_surjective ψ.toRingHom ψ.surjective).mp hy
    refine h₂ _ fun hu => h₁ x' hx' ?_
    have := hu.map ψ.symm
    simpa using this
  have h1 : ψ.toRingHom x ∈ (J₁ ^ e).map ψ.toRingHom := Ideal.mem_map_of_mem _ hx
  rw [Ideal.map_pow] at h1
  exact Ideal.pow_right_mono hle e h1

section Line

variable (W : Type) [CommRing W]

noncomputable def lineSubst (a b : W) : Fin 2 → PowerSeries W :=
  fun s => PowerSeries.C (if s = 0 then a else b) * PowerSeries.X

theorem hasSubst_lineSubst (a b : W) : MvPowerSeries.HasSubst (lineSubst W a b) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro s
  show PowerSeries.constantCoeff (PowerSeries.C (if s = 0 then a else b) * PowerSeries.X) = 0
  simp

noncomputable def lineEval (a b : W) (G : MvPowerSeries (Fin 2) W) : PowerSeries W :=
  MvPowerSeries.subst (lineSubst W a b) G

theorem lineEval_mul (a b : W) (G H : MvPowerSeries (Fin 2) W) :
    lineEval W a b (G * H) = lineEval W a b G * lineEval W a b H :=
  MvPowerSeries.subst_mul (hasSubst_lineSubst W a b) G H

theorem lineEval_pow (a b : W) (G : MvPowerSeries (Fin 2) W) (n : ℕ) :
    lineEval W a b (G ^ n) = lineEval W a b G ^ n :=
  MvPowerSeries.subst_pow (hasSubst_lineSubst W a b) G n

theorem lineEval_sum (a b : W) (s : Finset ℕ) (G : ℕ → MvPowerSeries (Fin 2) W) :
    lineEval W a b (∑ i ∈ s, G i) = ∑ i ∈ s, lineEval W a b (G i) := by
  unfold lineEval
  rw [← MvPowerSeries.coe_substAlgHom (hasSubst_lineSubst W a b), map_sum]

theorem lineEval_C (a b w : W) :
    lineEval W a b (MvPowerSeries.C w) = PowerSeries.C w := by
  unfold lineEval
  rw [MvPowerSeries.subst_C]
  rfl

theorem mvcoeff_C_mul_X_pow (c : W) (e m : ℕ) :
    MvPowerSeries.coeff (Finsupp.single () e) (PowerSeries.C c * PowerSeries.X ^ m) = if e = m then c else 0 :=
  PowerSeries.coeff_C_mul_X_pow c m e

theorem coeff_lineEval (a b : W) (G : MvPowerSeries (Fin 2) W) (e : ℕ) :
    PowerSeries.coeff e (lineEval W a b G) =
      ∑ i ∈ Finset.range (e + 1), MvPowerSeries.coeff (nd e i) G * a ^ i * b ^ (e - i) := by
  classical
  show MvPowerSeries.coeff (Finsupp.single () e) (MvPowerSeries.subst (lineSubst W a b) G) = _
  rw [MvPowerSeries.coeff_subst (hasSubst_lineSubst W a b)]
  have hterm : ∀ d : Fin 2 →₀ ℕ,
      MvPowerSeries.coeff d G • MvPowerSeries.coeff (Finsupp.single () e)
          (d.prod fun s n => lineSubst W a b s ^ n) =
        if d 0 + d 1 = e then MvPowerSeries.coeff d G * a ^ d 0 * b ^ d 1 else 0 := by
    intro d
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
    have : lineSubst W a b 0 ^ d 0 * lineSubst W a b 1 ^ d 1 =
        PowerSeries.C (a ^ d 0 * b ^ d 1) * PowerSeries.X ^ (d 0 + d 1) := by
      simp only [lineSubst, if_true, if_neg (by decide : (1 : Fin 2) ≠ 0), map_mul, map_pow]
      ring
    rw [this, mvcoeff_C_mul_X_pow, smul_eq_mul]
    by_cases h : d 0 + d 1 = e
    · rw [if_pos h.symm, if_pos h, mul_assoc]
    · rw [if_neg (Ne.symm h), if_neg h, mul_zero]
  simp only [hterm]
  rw [finsum_eq_sum_of_support_subset _ (s := (Finset.range (e + 1)).image (nd e)) ?_]
  · rw [Finset.sum_image (nd_injOn e)]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_range] at hi
    rw [nd_zero, nd_one, if_pos (by omega)]
  · intro d hd
    rw [Function.mem_support] at hd
    have h : d 0 + d 1 = e := by
      by_contra h; exact hd (if_neg h)
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
    exact ⟨d 0, by omega, by rw [(eq_nd d), h, nd_zero]⟩

theorem constantCoeff_lineEval (a b : W) (G : MvPowerSeries (Fin 2) W) :
    PowerSeries.constantCoeff (lineEval W a b G) = MvPowerSeries.coeff (0 : Fin 2 →₀ ℕ) G := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_lineEval]
  simp [nd]

theorem coeff_one_lineEval (a b : W) (G : MvPowerSeries (Fin 2) W) :
    PowerSeries.coeff 1 (lineEval W a b G) =
      MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1) G * a +
        MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1) G * b := by
  rw [coeff_lineEval, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  simp [nd, add_comm]

theorem coeff_pow_mul_pow (φ χ : PowerSeries W) (hφ : PowerSeries.constantCoeff φ = 0)
    (hχ : PowerSeries.constantCoeff χ = 0) (j k : ℕ) :
    PowerSeries.coeff (j + k) (φ ^ j * χ ^ k) = PowerSeries.coeff 1 φ ^ j * PowerSeries.coeff 1 χ ^ k := by
  obtain ⟨φ', rfl⟩ := PowerSeries.X_dvd_iff.mpr hφ
  obtain ⟨χ', rfl⟩ := PowerSeries.X_dvd_iff.mpr hχ
  have h1 : (PowerSeries.X * φ') ^ j * (PowerSeries.X * χ') ^ k =
      PowerSeries.X ^ (j + k) * (φ' ^ j * χ' ^ k) := by ring
  have h2 := PowerSeries.coeff_X_pow_mul (φ' ^ j * χ' ^ k) (j + k) 0
  rw [zero_add] at h2
  rw [h1, h2]
  have h3 : ∀ ψ : PowerSeries W, PowerSeries.coeff 1 (PowerSeries.X * ψ) = PowerSeries.coeff 0 ψ :=
    fun ψ => PowerSeries.coeff_succ_X_mul 0 ψ
  rw [h3, h3]
  simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, map_pow]

end Line

theorem natDir_rational (q : ℕ) [Fact q.Prime] (W : Type) [CommRing W] [IsLocalRing W]
    (hq : (q : W) ∈ maximalIdeal W) (n₀ n₁ : ℕ) (h : n₀ = 1 ∨ (n₀ = 0 ∧ n₁ = 1)) :
    ((n₀ : W) ∉ maximalIdeal W ∨ (n₁ : W) ∉ maximalIdeal W) ∧
      (n₀ : W) ^ q * (n₁ : W) - (n₀ : W) * (n₁ : W) ^ q ∈ maximalIdeal W := by
  have hq0 : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  have h1 : (1 : W) ∉ maximalIdeal W := fun h => (mem_maximalIdeal _).mp h isUnit_one

  have fermat : ∀ n : ℕ, (n : W) ^ q - (n : W) ∈ maximalIdeal W := by
    intro n
    have hz : ((n : ℤ) ^ q - n : ZMod q) = 0 := by
      push_cast
      rw [ZMod.pow_card, sub_self]
    have hdvd : (q : ℤ) ∣ (n : ℤ) ^ q - n := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact_mod_cast hz
    obtain ⟨k, hk⟩ := hdvd
    have e : (n : W) ^ q - (n : W) = (((n : ℤ) ^ q - n : ℤ) : W) := by push_cast; ring
    rw [e, hk]
    push_cast
    exact Ideal.mul_mem_right _ _ hq
  rcases h with rfl | ⟨rfl, rfl⟩
  · refine ⟨Or.inl (by rw [Nat.cast_one]; exact h1), ?_⟩
    rw [Nat.cast_one, one_pow, one_mul, one_mul]
    have := fermat n₁
    rw [show (n₁ : W) - (n₁ : W) ^ q = -((n₁ : W) ^ q - (n₁ : W)) by ring]
    exact Submodule.neg_mem _ this
  · refine ⟨Or.inr (by rw [Nat.cast_one]; exact h1), ?_⟩
    rw [Nat.cast_zero, Nat.cast_one, zero_pow hq0, zero_mul, zero_mul, sub_zero]
    exact zero_mem _

theorem isUnit_of_sub_sum_mem (W₁ W₂ : Type) [CommRing W₁] [CommRing W₂] [IsLocalRing W₂]
    (ρ : W₁ →+* W₂) (e : ℕ) (c : ℕ → W₁) (lam : W₂) (hlam : IsUnit lam) (n₀ n₁ : ℕ) (ℓ₀ ℓ₁ : W₂)
    (h₀ : ℓ₀ - lam * (n₀ : W₂) ∈ maximalIdeal W₂) (h₁ : ℓ₁ - lam * (n₁ : W₂) ∈ maximalIdeal W₂)
    (hU : IsUnit (∑ i ∈ Finset.range (e + 1), c i * (n₀ : W₁) ^ i * (n₁ : W₁) ^ (e - i)))
    (x : W₂) (hx : x - ∑ i ∈ Finset.range (e + 1), ρ (c i) * ℓ₀ ^ i * ℓ₁ ^ (e - i) ∈ maximalIdeal W₂) :
    IsUnit x := by
  classical
  set res : W₂ →+* ResidueField W₂ := residue W₂ with hres
  have hresm : ∀ w : W₂, w ∈ maximalIdeal W₂ ↔ res w = 0 := fun w => (residue_eq_zero_iff w).symm
  have hres_unit : ∀ w : W₂, IsUnit w → res w ≠ 0 := by
    intro w hw h0
    exact (mem_maximalIdeal w).mp ((hresm w).mpr h0) hw

  by_contra hxu
  have hx0 : res x = 0 := (hresm x).mp ((mem_maximalIdeal x).mpr hxu)
  have hℓ₀ : res ℓ₀ = res lam * (n₀ : ResidueField W₂) := by
    have := (hresm _).mp h₀; rw [map_sub, map_mul, map_natCast, sub_eq_zero] at this; exact this
  have hℓ₁ : res ℓ₁ = res lam * (n₁ : ResidueField W₂) := by
    have := (hresm _).mp h₁; rw [map_sub, map_mul, map_natCast, sub_eq_zero] at this; exact this
  have hsum : res x = res lam ^ e * res (ρ (∑ i ∈ Finset.range (e + 1), c i * (n₀ : W₁) ^ i * (n₁ : W₁) ^ (e - i))) := by
    have := (hresm _).mp hx
    rw [map_sub, sub_eq_zero] at this
    rw [this, map_sum, map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ e := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    simp only [map_mul, map_pow, map_natCast, hℓ₀, hℓ₁]
    have epow : res lam ^ e = res lam ^ i * res lam ^ (e - i) := by
      rw [← pow_add, Nat.add_sub_cancel' hi']
    rw [mul_pow, mul_pow, epow]
    ring
  have hu1 : res lam ^ e ≠ 0 := pow_ne_zero _ (hres_unit lam hlam)
  have hu2 : res (ρ (∑ i ∈ Finset.range (e + 1), c i * (n₀ : W₁) ^ i * (n₁ : W₁) ^ (e - i))) ≠ 0 :=
    hres_unit _ (hU.map ρ)
  exact mul_ne_zero hu1 hu2 (hsum ▸ hx0)

end DrinfeldCurve.LocalChart.HasseTransportAux
p2m_reactivate "P2MW.S_DrinfeldCurve_LocalChart_exists_mem_pow_isUnit_homogeneous_apply_sub_C_eq_mk_of_ringEquiv_of_forall_apply_mk_C.DrinfeldCurve P2MW.S_DrinfeldCurve_LocalChart_exists_mem_pow_isUnit_homogeneous_apply_sub_C_eq_mk_of_ringEquiv_of_forall_apply_mk_C.DrinfeldCurve.LocalChart P2MW.S_DrinfeldCurve_LocalChart_exists_mem_pow_isUnit_homogeneous_apply_sub_C_eq_mk_of_ringEquiv_of_forall_apply_mk_C.DrinfeldCurve.LocalChart.HasseTransportAux"
p2m_reactivate "P2MW.S_DrinfeldCurve_LocalChart_exists_mem_pow_isUnit_homogeneous_apply_sub_C_eq_mk_of_ringEquiv_of_forall_apply_mk_C.DrinfeldCurve P2MW.S_DrinfeldCurve_LocalChart_exists_mem_pow_isUnit_homogeneous_apply_sub_C_eq_mk_of_ringEquiv_of_forall_apply_mk_C.DrinfeldCurve.LocalChart"
p2m_reactivate "P2MW.S_DrinfeldCurve_LocalChart_exists_mem_pow_isUnit_homogeneous_apply_sub_C_eq_mk_of_ringEquiv_of_forall_apply_mk_C.DrinfeldCurve"

open DrinfeldCurve.LocalChart.HasseTransportAux

theorem solution
    (q : ℕ) [Fact q.Prime]
    (W₁ : Type) [CommRing W₁] [IsDomain W₁] [IsDiscreteValuationRing W₁]
    (π₁ : W₁) (hπ₁ : maximalIdeal W₁ = Ideal.span {π₁}) (hq₁ : (q : W₁) ∈ maximalIdeal W₁)
    (f₁ u₁ v₁ : MvPowerSeries (Fin 2) W₁) (hu₁ : IsUnit u₁) (hv₁ : IsUnit v₁)
    (hf₁ : f₁ - DrinfeldCurve.LocalChart.drinfeldForm q W₁ ∈
      (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ (q + 2))
    (W₂ : Type) [CommRing W₂] [IsDomain W₂] [IsDiscreteValuationRing W₂]
    (π₂ : W₂) (hπ₂ : maximalIdeal W₂ = Ideal.span {π₂}) (hq₂ : (q : W₂) ∈ maximalIdeal W₂)
    (f₂ u₂ v₂ : MvPowerSeries (Fin 2) W₂) (hu₂ : IsUnit u₂) (hv₂ : IsUnit v₂)
    (hf₂ : f₂ - DrinfeldCurve.LocalChart.drinfeldForm q W₂ ∈
      (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₂), MvPowerSeries.X 1}) ^ (q + 2))
    (ρ : W₁ →+* W₂) (hρ : ρ π₁ = π₂)
    (ψ : (MvPowerSeries (Fin 2) W₁ ⧸ Ideal.span {MvPowerSeries.C π₁ * v₁ - f₁ * u₁}) ≃+*
      (MvPowerSeries (Fin 2) W₂ ⧸ Ideal.span {MvPowerSeries.C π₂ * v₂ - f₂ * u₂}))
    (hψ : ∀ w : W₁, ψ (Ideal.Quotient.mk _ (MvPowerSeries.C w)) = Ideal.Quotient.mk _ (MvPowerSeries.C (ρ w)))
    (s : MvPowerSeries (Fin 2) W₁ ⧸ Ideal.span {MvPowerSeries.C π₁ * v₁ - f₁ * u₁})
    (a₀ : W₁) (e₀ : ℕ) (he₀ : 1 ≤ e₀) (h : MvPowerSeries (Fin 2) W₁)
    (hh : h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ e₀)
    (hunit : ∀ a b : W₁, (a ∉ maximalIdeal W₁ ∨ b ∉ maximalIdeal W₁) →
      a ^ q * b - a * b ^ q ∈ maximalIdeal W₁ →
        IsUnit (∑ i ∈ Finset.range (e₀ + 1),
          MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (e₀ - i)) h * a ^ i * b ^ (e₀ - i)))
    (hs : s - Ideal.Quotient.mk _ (MvPowerSeries.C a₀) = Ideal.Quotient.mk _ h) :
    ∃ (h' : MvPowerSeries (Fin 2) W₂)
      (_ : h' ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₂), MvPowerSeries.X 1}) ^ e₀),
      (∀ a b : W₂, (a ∉ maximalIdeal W₂ ∨ b ∉ maximalIdeal W₂) →
        a ^ q * b - a * b ^ q ∈ maximalIdeal W₂ →
          IsUnit (∑ i ∈ Finset.range (e₀ + 1),
            MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (e₀ - i)) h' * a ^ i * b ^ (e₀ - i))) ∧
      ψ s - Ideal.Quotient.mk _ (MvPowerSeries.C (ρ a₀)) =
        Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C π₂ * v₂ - f₂ * u₂}) h' := by
  classical

  obtain ⟨g, hg0, hgψ, hgrat⟩ :=
    DrinfeldCurve.LocalChart.exists_apply_mk_X_eq_mk_linearPart_rational_of_ringEquiv_of_forall_apply_mk_C
      q W₁ π₁ hπ₁ hq₁ f₁ u₁ v₁ hu₁ hv₁ hf₁ W₂ π₂ hπ₂ hq₂ f₂ u₂ v₂ hu₂ hv₂ hf₂ ρ hρ ψ hψ
  have hπ₂0 : π₂ ≠ 0 := ne_zero_of_maximalIdeal_eq W₂ π₂ hπ₂
  have hf₁0 := coeff_zero_eq_zero_of_sub_drinfeldForm_mem q W₁ f₁ hf₁
  have hf₂0 := coeff_zero_eq_zero_of_sub_drinfeldForm_mem q W₂ f₂ hf₂

  have htrans : ∀ (e : ℕ) (x : MvPowerSeries (Fin 2) W₁ ⧸ Ideal.span {MvPowerSeries.C π₁ * v₁ - f₁ * u₁}),
      x ∈ ((Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ e).map
          (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C π₁ * v₁ - f₁ * u₁})) →
      ψ x ∈ ((Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₂), MvPowerSeries.X 1}) ^ e).map
          (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C π₂ * v₂ - f₂ * u₂})) := by
    intro e x hx
    rw [Ideal.map_pow] at hx ⊢
    exact map_mem_pow_of_mem_pow ψ _ _
      (fun y hy => (mem_map_span_X_iff_not_isUnit W₁ π₁ hπ₁ f₁ u₁ v₁ hv₁ hf₁0 y).mp hy)
      (fun y hy => (mem_map_span_X_iff_not_isUnit W₂ π₂ hπ₂ f₂ u₂ v₂ hv₂ hf₂0 y).mpr hy) e x hx

  obtain ⟨h', hh'mem, hh'eq⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp
    (htrans e₀ _ (Ideal.mem_map_of_mem _ hh))

  set P : MvPowerSeries (Fin 2) W₂ := ∑ i ∈ Finset.range (e₀ + 1),
    MvPowerSeries.C (ρ (MvPowerSeries.coeff (nd e₀ i) h)) * g 0 ^ i * g 1 ^ (e₀ - i) with hP
  have hgmem : ∀ j : Fin 2,
      g j ∈ Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₂), MvPowerSeries.X 1} :=
    fun j => mem_span_X_of_coeff_zero W₂ (g j) (hg0 j)
  have hPmem : P ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₂), MvPowerSeries.X 1}) ^ e₀ := by
    rw [hP]
    refine Ideal.sum_mem _ fun i hi => ?_
    rw [mul_assoc]
    refine Ideal.mul_mem_left _ _ ?_
    simp only [Finset.mem_range] at hi
    exact pow_mul_pow_mem_pow W₂ (g 0) (g 1) (hgmem 0) (hgmem 1) i (e₀ - i) e₀ (by omega)
  have hlowψ : ψ (Ideal.Quotient.mk _ (low W₁ e₀ h)) = Ideal.Quotient.mk _ P := by
    rw [low_eq_sum_C_mul, map_sum, map_sum, hP, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [map_mul, map_pow, hψ, hgψ]

  have hhigh := sub_low_mem_pow W₁ e₀ h (coeff_eq_zero_of_mem_pow W₁ e₀ h hh)
  obtain ⟨k, hkmem, hkeq⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp
    (htrans (e₀ + 1) _ (Ideal.mem_map_of_mem _ hhigh))

  have hkI : h' - P - k ∈ Ideal.span {MvPowerSeries.C π₂ * v₂ - f₂ * u₂} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_sub, hh'eq, hkeq, map_sub, map_sub, hlowψ, sub_self]
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hkI
  have hrel : h' - P = k + (MvPowerSeries.C π₂ * v₂ - f₂ * u₂) * r := by
    linear_combination (-1 : MvPowerSeries (Fin 2) W₂) * hr
  have hdeg : ∀ n : Fin 2 →₀ ℕ, n 0 + n 1 = e₀ →
      MvPowerSeries.coeff n h' - MvPowerSeries.coeff n P ∈ maximalIdeal W₂ := by
    intro n hn
    rw [← map_sub, hπ₂]
    exact DrinfeldCurve.LocalChart.coeff_mem_span_of_eq_add_rel_mul_of_forall_coeff_eq_zero W₂ π₂ hπ₂0
      f₂ u₂ v₂ hv₂ hf₂0 e₀ (h' - P) k r
      (coeff_eq_zero_of_mem_pow W₂ e₀ _ (Ideal.sub_mem _ hh'mem hPmem))
      (coeff_eq_zero_of_mem_pow W₂ (e₀ + 1) k hkmem) hrel n hn
  refine ⟨h', hh'mem, ?_, ?_⟩
  ·
    intro a b hab hF
    obtain ⟨lam, n₀, n₁, hlam, hn, hn₁, hl₀, hl₁⟩ := hgrat a b hab hF
    obtain ⟨hrat₁, hrat₂⟩ := natDir_rational q W₁ hq₁ n₀ n₁ hn
    have hU := hunit (n₀ : W₁) (n₁ : W₁) hrat₁ hrat₂

    have step1 : (∑ i ∈ Finset.range (e₀ + 1), MvPowerSeries.coeff (nd e₀ i) h' * a ^ i * b ^ (e₀ - i)) -
        (∑ i ∈ Finset.range (e₀ + 1), MvPowerSeries.coeff (nd e₀ i) P * a ^ i * b ^ (e₀ - i)) ∈
          maximalIdeal W₂ := by
      rw [← Finset.sum_sub_distrib]
      refine Ideal.sum_mem _ fun i hi => ?_
      rw [← sub_mul, ← sub_mul]
      refine Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (hdeg _ ?_))
      simp only [Finset.mem_range] at hi
      rw [nd_zero, nd_one]; omega

    have h0 : ∀ j : Fin 2, PowerSeries.constantCoeff (lineEval W₂ a b (g j)) = 0 := fun j => by
      rw [constantCoeff_lineEval, hg0]
    have step2 : (∑ i ∈ Finset.range (e₀ + 1), MvPowerSeries.coeff (nd e₀ i) P * a ^ i * b ^ (e₀ - i)) =
        ∑ i ∈ Finset.range (e₀ + 1), ρ (MvPowerSeries.coeff (nd e₀ i) h) *
          (MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1) (g 0) * a +
              MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1) (g 0) * b) ^ i *
          (MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1) (g 1) * a +
              MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1) (g 1) * b) ^ (e₀ - i) := by
      rw [← coeff_lineEval, hP, lineEval_sum, map_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      simp only [Finset.mem_range] at hi
      rw [lineEval_mul, lineEval_mul, lineEval_pow, lineEval_pow, lineEval_C, mul_assoc,
        PowerSeries.coeff_C_mul]
      have := coeff_pow_mul_pow W₂ (lineEval W₂ a b (g 0)) (lineEval W₂ a b (g 1)) (h0 0) (h0 1) i (e₀ - i)
      rw [show i + (e₀ - i) = e₀ by omega] at this
      rw [this, coeff_one_lineEval, coeff_one_lineEval, mul_assoc]
    rw [step2] at step1
    exact isUnit_of_sub_sum_mem W₁ W₂ ρ e₀ (fun i => MvPowerSeries.coeff (nd e₀ i) h) lam hlam n₀ n₁ _ _
      hl₀ hl₁ hU _ step1
  ·
    rw [← hψ a₀, ← map_sub, hs]
    exact hh'eq.symm

end S_DrinfeldCurve_LocalChart_exists_mem_pow_isUnit_homogeneous_apply_sub_C_eq_mk_of_ringEquiv_of_forall_apply_mk_C
end P2MW
export P2MW.S_DrinfeldCurve_LocalChart_exists_mem_pow_isUnit_homogeneous_apply_sub_C_eq_mk_of_ringEquiv_of_forall_apply_mk_C (solution)
