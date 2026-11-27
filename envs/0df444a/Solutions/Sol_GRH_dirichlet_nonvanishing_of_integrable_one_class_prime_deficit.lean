-- Prove2me | solution 1 for GRH.dirichlet_nonvanishing_of_integrable_one_class_prime_deficit
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T02:23:43.414805+00:00
-- url     : https://prove2.me/submissions/796ee968-82a9-42c5-b831-78e0f5c5cab8

import Theorems.Thm_GRH_nonnegative_mellin_with_holomorphic_correction_excludes_product_zeros
import Theorems.Thm_GRH_identity_progression_mangoldt_series_detects_all_dirichlet_zeros
import Theorems.Thm_GRH_identity_progression_prime_weight_mellin_majorant
import Theorems.Thm_GRH_prime_power_excess_in_a_progression_is_uniformly_square_root
import Mathlib.MeasureTheory.Function.Floor
import Definitions.Def_GRH_OneSidedMoebius
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.MeasureTheory.Order.Group.Lattice

/- The Mellin convergence proof is adapted from pitimespi's public Lean formalization,
   https://prove2.me/submissions/371c6c95-d927-4bbe-822c-d3f6df8f83e7
   licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
   The auxiliary namespace and imports have been changed. This file uses the local differentiation of an absolutely convergent Mellin integral
   to continue the transform of the positive prime deficit. -/
open Complex MeasureTheory Filter Topology Set Metric GRH.OneSidedMoebius
noncomputable section
namespace PrimeDeficitMellinAux


/-- `mellinK A k s = ∫_{x>1} A(x) (-log x)^k x^{-s-1} dx`; for `k = 0` this is the Mellin-type
transform `F(s) = ∫_{x>1} A(x) x^{-s-1} dx`, and `mellinK A k` is its `k`-th derivative. -/
def mellinK (A : ℝ → ℝ) (k : ℕ) (s : ℂ) : ℂ :=
  ∫ x in Ioi (1:ℝ), (A x : ℂ) * ((-Real.log x : ℝ) : ℂ) ^ k * (x : ℂ) ^ (-s - 1)

/-- Convergence of the real Mellin integral `∫_{x>1} A(x) x^{-σ-1} dx`. -/
def Conv (A : ℝ → ℝ) (σ : ℝ) : Prop :=
  IntegrableOn (fun x : ℝ => A x * x ^ (-σ - 1)) (Ioi 1)

lemma log_pow_le (k : ℕ) {η : ℝ} (hη : 0 < η) {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ^ k ≤ ((k:ℝ) / η) ^ k * x ^ η := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using Real.one_le_rpow hx hη.le
  · have hk' : (0:ℝ) < k := by exact_mod_cast hk
    have hε : 0 < η / k := div_pos hη hk'
    have h1 : Real.log x ≤ x ^ (η / k) / (η / k) := Real.log_le_rpow_div (by linarith) hε
    have h0 : 0 ≤ Real.log x := Real.log_nonneg hx
    have hx0 : 0 ≤ x := by linarith
    calc Real.log x ^ k ≤ (x ^ (η / k) / (η / k)) ^ k := pow_le_pow_left₀ h0 h1 k
      _ = ((k:ℝ) / η) ^ k * x ^ η := by
        rw [div_pow, ← Real.rpow_natCast (x ^ (η / k)), ← Real.rpow_mul hx0,
          div_mul_cancel₀ η hk'.ne', div_eq_mul_inv, ← inv_pow, inv_div, mul_comm]

lemma conv_mono {A : ℝ → ℝ} (hA : Measurable A) (hA0 : ∀ x, 1 < x → 0 ≤ A x) {σ σ' : ℝ}
    (h : Conv A σ) (hσ : σ ≤ σ') : Conv A σ' := by
  refine h.mono' ((hA.mul (measurable_id.pow_const _)).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx' : (1:ℝ) < x := hx
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hA0 x hx') (Real.rpow_nonneg (by linarith) _))]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hx'.le (by linarith)) (hA0 x hx')

/-- Absolute convergence of the real Mellin integral `∫_{x>1} |A(x)| x^{-σ-1} dx`. -/
def ConvAbs (A : ℝ → ℝ) (σ : ℝ) : Prop :=
  IntegrableOn (fun x : ℝ => |A x| * x ^ (-σ - 1)) (Ioi 1)

lemma convAbs_of_conv {A : ℝ → ℝ} (hA0 : ∀ x, 1 < x → 0 ≤ A x) {σ : ℝ} (h : Conv A σ) :
    ConvAbs A σ := by
  refine IntegrableOn.congr_fun h (fun x hx => ?_) measurableSet_Ioi
  simp only [abs_of_nonneg (hA0 x hx)]

/-- Domination: absolute convergence at `σ` gives integrability of
`|A(x)| (log x)^k x^{-σ'-1}` for every `σ' > σ`. -/
lemma integrableOn_log_pow {A : ℝ → ℝ} (hA : Measurable A)
    {σ σ' : ℝ} (hσ : σ < σ') (hc : ConvAbs A σ) (k : ℕ) :
    IntegrableOn (fun x : ℝ => |A x| * Real.log x ^ k * x ^ (-σ' - 1)) (Ioi 1) := by
  have hη : 0 < σ' - σ := sub_pos.mpr hσ
  refine (hc.const_mul (((k:ℝ) / (σ' - σ)) ^ k)).mono'
    (((hA.abs.mul (Real.measurable_log.pow_const k)).mul
      (measurable_id.pow_const _)).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx' : (1:ℝ) < x := hx
  have hx0 : 0 < x := by linarith
  have hAx := abs_nonneg (A x)
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx'.le
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have key := log_pow_le k hη hx'.le
  calc |A x| * Real.log x ^ k * x ^ (-σ' - 1)
      ≤ |A x| * (((k:ℝ) / (σ' - σ)) ^ k * x ^ (σ' - σ)) * x ^ (-σ' - 1) := by gcongr
    _ = ((k:ℝ) / (σ' - σ)) ^ k * (|A x| * (x ^ (σ' - σ) * x ^ (-σ' - 1))) := by ring
    _ = ((k:ℝ) / (σ' - σ)) ^ k * (|A x| * x ^ (-σ - 1)) := by
        rw [← Real.rpow_add hx0]; ring_nf

lemma integrableOn_log_pow_of_nonneg {A : ℝ → ℝ} (hA : Measurable A)
    (hA0 : ∀ x, 1 < x → 0 ≤ A x) {σ σ' : ℝ} (hσ : σ < σ') (hc : Conv A σ) (k : ℕ) :
    IntegrableOn (fun x : ℝ => A x * Real.log x ^ k * x ^ (-σ' - 1)) (Ioi 1) := by
  refine IntegrableOn.congr_fun (integrableOn_log_pow hA hσ (convAbs_of_conv hA0 hc) k)
    (fun x hx => ?_) measurableSet_Ioi
  simp only [abs_of_nonneg (hA0 x hx)]

lemma norm_integrand (A : ℝ → ℝ) (k : ℕ) {x : ℝ} (hx : 1 < x) (z : ℂ) :
    ‖(A x : ℂ) * ((-Real.log x : ℝ) : ℂ) ^ k * (x : ℂ) ^ (-z - 1)‖ =
      |A x| * Real.log x ^ k * x ^ (-z.re - 1) := by
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx.le
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
    Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
  simp [abs_of_nonneg hlog]

lemma hasDerivAt_integrand (A : ℝ → ℝ) (k : ℕ) {x : ℝ} (hx : 0 < x) (z : ℂ) :
    HasDerivAt (fun s : ℂ => (A x : ℂ) * ((-Real.log x : ℝ) : ℂ) ^ k * (x : ℂ) ^ (-s - 1))
      ((A x : ℂ) * ((-Real.log x : ℝ) : ℂ) ^ (k + 1) * (x : ℂ) ^ (-z - 1)) z := by
  have h1 : HasDerivAt (fun s : ℂ => -s - 1) (-1) z := by
    simpa using (hasDerivAt_id z).neg.sub_const 1
  have h2 := h1.const_cpow (c := (x:ℂ)) (Or.inl (by exact_mod_cast hx.ne'))
  have h3 := h2.const_mul ((A x : ℂ) * ((-Real.log x : ℝ) : ℂ) ^ k)
  refine h3.congr_deriv ?_
  rw [← Complex.ofReal_log hx.le]
  push_cast
  ring

lemma aestronglyMeasurable_integrand {A : ℝ → ℝ} (hA : Measurable A) (k : ℕ) (z : ℂ) :
    AEStronglyMeasurable
      (fun x : ℝ => (A x : ℂ) * ((-Real.log x : ℝ) : ℂ) ^ k * (x : ℂ) ^ (-z - 1))
      (volume.restrict (Ioi 1)) := by
  refine Measurable.aestronglyMeasurable ?_
  refine ((Complex.measurable_ofReal.comp hA).mul ?_).mul ?_
  · exact (Complex.measurable_ofReal.comp Real.measurable_log.neg).pow_const k
  · exact Complex.measurable_ofReal.pow_const _

lemma integrable_integrand {A : ℝ → ℝ} (hA : Measurable A)
    {τ : ℝ} (hconv : ∀ σ, τ < σ → ConvAbs A σ) (k : ℕ) {s : ℂ} (hs : τ < s.re) :
    Integrable (fun x : ℝ => (A x : ℂ) * ((-Real.log x : ℝ) : ℂ) ^ k * (x : ℂ) ^ (-s - 1))
      (volume.restrict (Ioi 1)) := by
  have hI := integrableOn_log_pow hA (σ := (τ + s.re) / 2) (σ' := s.re) (by linarith)
    (hconv _ (by linarith)) k
  refine hI.mono' (aestronglyMeasurable_integrand hA k s) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [norm_integrand A k hx]

lemma hasDerivAt_mellinK {A : ℝ → ℝ} (hA : Measurable A)
    {τ : ℝ} (hconv : ∀ σ, τ < σ → ConvAbs A σ) (k : ℕ) {s : ℂ} (hs : τ < s.re) :
    HasDerivAt (mellinK A k) (mellinK A (k+1) s) s := by
  set δ := (s.re - τ) / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  set σ₁ := s.re - δ with hσ₁
  have hτσ₁ : τ < σ₁ := by rw [hσ₁, hδ]; linarith
  have hbound := integrableOn_log_pow hA (σ := (τ + σ₁) / 2) (σ' := σ₁) (by linarith)
    (hconv _ (by linarith)) (k + 1)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 1))
    (F := fun z x => (A x : ℂ) * ((-Real.log x : ℝ) : ℂ) ^ k * (x : ℂ) ^ (-z - 1))
    (F' := fun z x => (A x : ℂ) * ((-Real.log x : ℝ) : ℂ) ^ (k + 1) * (x : ℂ) ^ (-z - 1))
    (x₀ := s) (s := ball s δ)
    (bound := fun x => |A x| * Real.log x ^ (k + 1) * x ^ (-σ₁ - 1))
    (ball_mem_nhds s hδpos)
    (Eventually.of_forall fun z => aestronglyMeasurable_integrand hA k z)
    (integrable_integrand hA hconv k hs)
    (aestronglyMeasurable_integrand hA (k + 1) s) ?_ hbound ?_
  · exact key.2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx z hz
    have hx' : (1:ℝ) < x := hx
    rw [norm_integrand A (k + 1) hx']
    have hzre : σ₁ ≤ z.re := by
      have h1 : |z.re - s.re| ≤ ‖z - s‖ := by
        simpa using Complex.abs_re_le_norm (z - s)
      have h2 : ‖z - s‖ < δ := by simpa [dist_eq_norm] using hz
      have := (abs_lt.mp (lt_of_le_of_lt h1 h2)).1
      rw [hσ₁]; linarith
    have hlog : 0 ≤ Real.log x := Real.log_nonneg hx'.le
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hx'.le (by linarith)) (by positivity)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx z _
    exact hasDerivAt_integrand A k (by linarith [show (1:ℝ) < x from hx]) z

end PrimeDeficitMellinAux

open GRH.SplitPrimeLower GRH.PrimeDeficitMean

private theorem kernelIntegrable {f : ℝ → ℝ} (hm : Measurable f) {s : ℂ}
    (hi : IntegrableOn (fun x : ℝ => f x*x^(-s.re-1)) (Ioi 1)) :
    IntegrableOn (fun x : ℝ => (f x:ℂ)*(x:ℂ)^(-s-1)) (Ioi 1) := by
  refine hi.norm.mono' (((Complex.measurable_ofReal.comp hm).mul
    (Complex.measurable_ofReal.pow_const _)).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0<x := zero_lt_one.trans hx
  simp [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hx0,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hx0.le (-s.re-1))]

theorem solution (q : ℕ) [NeZero q] (θ : ℝ) (hθ : 0<θ) (hθ1 : θ<1)
    (h : IntegrableOn (fun x : ℝ => deficit q x*x^(-θ-1)) (Ioi 1)) :
    ∀ (χ : DirichletCharacter ℂ q) (s : ℂ), θ<s.re → ¬ (χ=1 ∧ s=1) → χ.LFunction s ≠ 0 := by
  let D := deficit q
  let E := primeMajorant q 0 0
  let A := fun x : ℝ => D x+E x
  have hdm : Measurable D := (measurable_id.sub (measurable_const.mul
    ((measurable_of_countable (primeWeight q)).comp Nat.measurable_floor))).max measurable_const
  have hd0 (x : ℝ) (_ : 1<x) : 0≤D x := le_max_right .. 
  have hdc (t : ℝ) (ht : θ<t) : PrimeDeficitMellinAux.Conv D t :=
    PrimeDeficitMellinAux.conv_mono hdm hd0 h ht.le
  have hconv (t : ℝ) (ht : θ<t) := PrimeDeficitMellinAux.convAbs_of_conv hd0 (hdc t ht)
  have hB : DifferentiableOn ℂ (transform D) {s : ℂ | θ<s.re} := by
    have he : PrimeDeficitMellinAux.mellinK D 0 = transform D := by
      funext s;simp [PrimeDeficitMellinAux.mellinK,transform]
    rw [← he]
    exact fun s hs => (PrimeDeficitMellinAux.hasDerivAt_mellinK hdm hconv 0 hs).differentiableAt.differentiableWithinAt
  obtain ⟨hem,hei,hef⟩ := GRH.identity_progression_prime_weight_mellin_majorant q 0 0
    (by norm_num) (by norm_num)
  have ham : Measurable A := hdm.add hem
  obtain ⟨_,_,hw⟩ := GRH.prime_power_excess_in_a_progression_is_uniformly_square_root
  have ha0 (x : ℝ) (_ : 1<x) : 0 ≤ A x := by
    have hh : x-(q.totient:ℝ)*primeWeight q ⌊x⌋₊ ≤ D x := le_max_left .. 
    have hg := mul_nonneg (Nat.cast_nonneg (α:=ℝ) q.totient) (hw q ⌊x⌋₊).1
    dsimp only [A,E,primeMajorant]
    rw [zero_mul,zero_add]
    linarith
  have hai (t : ℝ) (ht : 1<t) : IntegrableOn (fun x : ℝ => A x*x^(-t-1)) (Ioi 1) := by
    have hsum := (hdc t (hθ1.trans ht)).add (hei t ht)
    change IntegrableOn (fun x : ℝ => (D x+E x)*x^(-t-1)) (Ioi 1)
    simp_rw [add_mul]
    exact hsum
  have hform (s : ℂ) (hs : 1<s.re) : transform A s =
      transform D s - (logDeriv (regularProduct q) s+1)/s := by
    have idD := kernelIntegrable (s:=s) hdm (hdc s.re (hθ1.trans hs))
    have idE := kernelIntegrable (s:=s) hem (hei s.re hs)
    have hsum : transform A s = transform D s + transform E s := by
      unfold transform A
      simp_rw [Complex.ofReal_add,add_mul]
      exact integral_add idD idE
    rw [hsum]
    have hE := hef s hs
    change transform E s = _ at hE
    simp [hE,sub_eq_add_neg]
  obtain ⟨hp,hr,split,_⟩ := GRH.identity_progression_mangoldt_series_detects_all_dirichlet_zeros q
  have free := GRH.nonnegative_mellin_with_holomorphic_correction_excludes_product_zeros
    (regularProduct q) (transform D) A θ hp (fun z hz => hr z hz.le) hB hθ hθ1 ham ha0 hai hform
  exact fun χ s hs he => split χ s he (free s hs)

/- License for the attributed portions above.

                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

-/
