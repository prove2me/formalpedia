-- Prove2me | solution 1 for CountingLLL.RandomRAM.reciprocal_prefix_cross_moments
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T05:44:41.334762+00:00
-- url     : https://prove2.me/submissions/3419a8b2-d230-474d-8311-a59a3d1e9b1d

import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ResearchReciprocalCross

noncomputable def prefixProduct (n : ℕ) (ω : ℕ → ℝ) : ℝ := ∏ j ∈ Finset.range n, ω j

private theorem prefix_cross_identity (ω : ℕ → ℝ) (i j : ℕ) :
    prefixProduct i ω * prefixProduct (i + j) ω =
      ∏ k ∈ Finset.range (i + j), if k < i then (ω k)^2 else ω k := by
  have hfirst : (∏ k ∈ Finset.range i, if k < i then (ω k)^2 else ω k) =
      (∏ k ∈ Finset.range i, ω k)^2 := by
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro k hk
    simp [Finset.mem_range.mp hk]
  have hsecond : (∏ k ∈ Finset.range j, if i + k < i then (ω (i+k))^2 else ω (i+k)) =
      ∏ k ∈ Finset.range j, ω (i+k) := by
    apply Finset.prod_congr rfl
    intro k hk
    simp
  rw [Finset.prod_range_add, hfirst, hsecond]
  simp only [prefixProduct, Finset.prod_range_add]
  ring

/-- The i,j cross moment of the prefix products in Lemma 5.4. -/
theorem cross_moment (ν : Measure ℝ) [IsProbabilityMeasure ν] (i j : ℕ) :
    (∫ ω, prefixProduct i ω * prefixProduct (i + j) ω
      ∂(Measure.infinitePi fun _ : ℕ => ν)) =
      (∫ x, x ^ 2 ∂ν) ^ i * (∫ x, x ∂ν) ^ j := by
  let μ : Measure (ℕ → ℝ) := Measure.infinitePi fun _ : ℕ => ν
  let φ : ℕ → ℝ → ℝ := fun k x => if k < i then x^2 else x
  have hφ : ∀ k, Measurable (φ k) := by
    intro k
    by_cases h : k < i <;> simp [φ, h] <;> fun_prop
  have hm : ∀ k : Fin (i+j), Measurable (fun ω : ℕ → ℝ => ω k.val) :=
    fun k => measurable_pi_apply k.val
  have hind : iIndepFun (fun (k : Fin (i+j)) (ω : ℕ → ℝ) => ω k.val) μ := by
    have hall : iIndepFun (fun (k : ℕ) (ω : ℕ → ℝ) => ω k) μ :=
      iIndepFun_infinitePi (fun _ => measurable_id)
    exact hall.precomp Fin.val_injective
  have heval : ∀ k : Fin (i+j), μ.map (fun ω => ω k.val) = ν := by
    intro k
    exact Measure.infinitePi_map_eval (fun _ : ℕ => ν) k.val
  have h := hind.integral_fun_prod_comp (f := fun (k : Fin (i+j)) => φ k.val)
    (fun k => (hm k).aemeasurable) (fun k => (hφ k.val).aestronglyMeasurable)
  have hcoord : ∀ k : Fin (i+j), (∫ ω, φ k.val (ω k.val) ∂μ) = ∫ x, φ k.val x ∂ν := by
    intro k
    rw [← integral_map (hm k).aemeasurable (hφ k.val).aestronglyMeasurable, heval]
  simp_rw [hcoord] at h
  have hleft : (∫ ω, prefixProduct i ω * prefixProduct (i + j) ω ∂μ) =
      ∫ ω, ∏ k : Fin (i+j), φ k.val (ω k.val) ∂μ := by
    apply integral_congr_ae
    filter_upwards with ω
    rw [prefix_cross_identity]
    symm
    exact Fin.prod_univ_eq_prod_range (fun k => φ k (ω k)) (i+j)
  rw [hleft, h]
  rw [Fin.prod_univ_eq_prod_range (fun k : ℕ => ∫ x, φ k x ∂ν) (i+j), Finset.prod_range_add]
  have h1 : (∏ k ∈ Finset.range i, ∫ x, φ k x ∂ν) = (∫ x, x ^ 2 ∂ν) ^ i := by
    calc
      _ = ∏ _k ∈ Finset.range i, ∫ x, x ^ 2 ∂ν := by
        apply Finset.prod_congr rfl
        intro k hk
        simp [φ, Finset.mem_range.mp hk]
      _ = _ := by simp
  have h2 : (∏ k ∈ Finset.range j, ∫ x, φ (i+k) x ∂ν) = (∫ x, x ∂ν) ^ j := by
    simp [φ]
  rw [h1, h2]

/-- Each cross product is genuinely integrable under the source second-moment hypothesis. -/
theorem cross_integrable (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : MemLp (fun x : ℝ => x) 2 ν) (i j : ℕ) :
    Integrable (fun ω => prefixProduct i ω * prefixProduct (i+j) ω)
      (Measure.infinitePi fun _ : ℕ => ν) := by
  classical
  let μ : Measure (ℕ → ℝ) := Measure.infinitePi fun _ : ℕ => ν
  let φ : ℕ → ℝ → ℝ := fun k x => if k < i then x^2 else x
  have hφint : ∀ k, Integrable (φ k) ν := by
    intro k
    by_cases h : k < i
    · simpa [φ, h, Real.norm_eq_abs, sq_abs] using hν.integrable_norm_pow (p := 2) (by norm_num)
    · simpa [φ, h] using hν.integrable (by norm_num)
  have hm : ∀ k : Fin (i+j), Measurable (fun ω : ℕ → ℝ => ω k.val) :=
    fun k => measurable_pi_apply k.val
  have hind : iIndepFun (fun (k : Fin (i+j)) (ω : ℕ → ℝ) => ω k.val) μ := by
    have hall : iIndepFun (fun (k : ℕ) (ω : ℕ → ℝ) => ω k) μ :=
      iIndepFun_infinitePi (fun _ => measurable_id)
    exact hall.precomp Fin.val_injective
  have heval : ∀ k : Fin (i+j), μ.map (fun ω => ω k.val) = ν := by
    intro k
    exact Measure.infinitePi_map_eval (fun _ : ℕ => ν) k.val
  have hvec : AEMeasurable (fun (ω : ℕ → ℝ) (k : Fin (i+j)) => ω k.val) μ :=
    aemeasurable_pi_iff.mpr (fun k => (hm k).aemeasurable)
  have hmap : μ.map (fun (ω : ℕ → ℝ) (k : Fin (i+j)) => ω k.val) =
      Measure.pi (fun _ : Fin (i+j) => ν) := by
    rw [hind.map_fun_eq_pi_map (fun k => (hm k).aemeasurable)]
    simp_rw [heval]
  have hprod : Integrable (fun x : Fin (i+j) → ℝ => ∏ k, φ k.val (x k))
      (Measure.pi (fun _ : Fin (i+j) => ν)) := Integrable.fintype_prod (fun k => hφint k.val)
  rw [← hmap] at hprod
  have hcomp := hprod.comp_aemeasurable hvec
  have heq : (fun ω : ℕ → ℝ => prefixProduct i ω * prefixProduct (i+j) ω) =
      (fun ω => ∏ k : Fin (i+j), φ k.val (ω k.val)) := by
    funext ω
    rw [prefix_cross_identity]
    symm
    exact Fin.prod_univ_eq_prod_range (fun k => φ k (ω k)) (i+j)
  rw [heq]
  exact hcomp

/-- Absolute cross moment, used to justify the double-series interchange. -/
theorem cross_abs_moment (ν : Measure ℝ) [IsProbabilityMeasure ν] (i j : ℕ) :
    (∫ ω, |prefixProduct i ω * prefixProduct (i+j) ω|
      ∂(Measure.infinitePi fun _ : ℕ => ν)) =
      (∫ x, x ^ 2 ∂ν) ^ i * (∫ x, |x| ∂ν) ^ j := by
  let νabs : Measure ℝ := ν.map (abs : ℝ → ℝ)
  letI : IsProbabilityMeasure νabs := Measure.isProbabilityMeasure_map measurable_abs.aemeasurable
  let T : (ℕ → ℝ) → (ℕ → ℝ) := fun ω k => |ω k|
  let μ : Measure (ℕ → ℝ) := Measure.infinitePi fun _ : ℕ => ν
  have hT : Measurable T := measurable_pi_lambda _ (fun k => measurable_abs.comp (measurable_pi_apply k))
  have hmap : μ.map T = Measure.infinitePi (fun _ : ℕ => νabs) :=
    Measure.infinitePi_map_pi (fun _ : ℕ => ν) (f := fun _ x => |x|) (fun _ => measurable_abs)
  have hmeas (n : ℕ) : Measurable (prefixProduct n) := by
    unfold prefixProduct
    fun_prop
  have hleft : (∫ ω, |prefixProduct i ω * prefixProduct (i+j) ω| ∂μ) =
      ∫ ω, prefixProduct i ω * prefixProduct (i+j) ω
        ∂(Measure.infinitePi fun _ : ℕ => νabs) := by
    rw [← hmap]
    have hchange := integral_map (μ := μ) (φ := T) (f := fun ω => prefixProduct i ω * prefixProduct (i+j) ω)
      hT.aemeasurable ((hmeas i).mul (hmeas (i+j))).aestronglyMeasurable
    rw [hchange]
    apply integral_congr_ae
    filter_upwards with ω
    simp [T, prefixProduct, abs_mul, Finset.abs_prod]
  rw [hleft, cross_moment]
  have h1 : (∫ x, x ^ 2 ∂νabs) = ∫ x, x ^ 2 ∂ν := by
    rw [show νabs = ν.map (abs : ℝ → ℝ) from rfl,
      integral_map measurable_abs.aemeasurable (by fun_prop)]
    simp only [sq_abs]
  have h2 : (∫ x, x ∂νabs) = ∫ x, |x| ∂ν := by
    change (∫ x, (id : ℝ → ℝ) x ∂νabs) = _
    rw [show νabs = ν.map (abs : ℝ → ℝ) from rfl,
      integral_map measurable_abs.aemeasurable aestronglyMeasurable_id]
    rfl
  rw [h1, h2]

end ResearchReciprocalCross

open ResearchReciprocalCross

theorem solution (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : MemLp (fun x : ℝ => x) 2 ν) (i j : ℕ) :
    Integrable (fun ω : ℕ → ℝ => (∏ k ∈ Finset.range i, ω k) *
      (∏ k ∈ Finset.range (i+j), ω k)) (Measure.infinitePi fun _ : ℕ => ν) ∧
    (∫ ω, (∏ k ∈ Finset.range i, ω k) * (∏ k ∈ Finset.range (i+j), ω k)
      ∂(Measure.infinitePi fun _ : ℕ => ν)) =
      (∫ x, x ^ 2 ∂ν) ^ i * (∫ x, x ∂ν) ^ j ∧
    (∫ ω, |(∏ k ∈ Finset.range i, ω k) * (∏ k ∈ Finset.range (i+j), ω k)|
      ∂(Measure.infinitePi fun _ : ℕ => ν)) =
      (∫ x, x ^ 2 ∂ν) ^ i * (∫ x, |x| ∂ν) ^ j := by
  exact ⟨cross_integrable ν hν i j, cross_moment ν i j, cross_abs_moment ν i j⟩
