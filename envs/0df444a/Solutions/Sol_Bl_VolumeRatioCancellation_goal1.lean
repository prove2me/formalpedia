-- Prove2me | solution 1 for Bl.VolumeRatioCancellation.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:20:57.962467+00:00
-- url     : https://prove2.me/submissions/6062f30a-441f-4cd8-a202-c36845601a4f

import Mathlib
import Definitions.Def_Lemmata_Cancellation_EnnrealVolumeRatioStepCancel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u_1 u_2
namespace Bl.VolumeRatioCancellation
private lemma ennreal_volume_ratio_step_cancel {u w z : WithZero (Multiplicative ℤ)} (hz : z ≠ 0)
    (h : u * z ≤ w * z) : u ≤ w := by
  have h' := mul_le_mul_left h z⁻¹
  simpa [mul_assoc, mul_inv_cancel₀ hz] using h'
end Bl.VolumeRatioCancellation
end

set_option autoImplicit false
universe u_1 u_2
open Bl Bl.VolumeRatioCancellation
namespace Bl.VolumeRatioCancellation
theorem _root_.solution :
  ∀ {R : Type u_1} [inst : CommRing.{u_1} R] [inst_1 : IsDedekindDomain.{u_1} R] {K : Type u_2} [inst_2 : Field.{u_2} K]
  [inst_3 : Algebra.{u_1, u_2} R K] [inst_4 : IsFractionRing.{u_1, u_2} R K]
  (T : Finset.{u_1} (IsDedekindDomain.HeightOneSpectrum.{u_1} R))
  (a c : IsDedekindDomain.HeightOneSpectrum.{u_1} R → K),
  (∀ (p : IsDedekindDomain.HeightOneSpectrum.{u_1} R), Membership.mem.{u_1, u_1} T p → Ne.{u_2 + 1} (c p) 0) →
    Exists.{u_2 + 1} fun (t : K) ↦
      And
        (∀ (p : IsDedekindDomain.HeightOneSpectrum.{u_1} R),
          Membership.mem.{u_1, u_1} T p →
            LE.le.{0}
              (DFunLike.coe.{u_2 + 1, u_2 + 1, 1} (IsDedekindDomain.HeightOneSpectrum.valuation.{u_1, u_2} K p)
                (HSub.hSub.{u_2, u_2, u_2} t (a p)))
              (DFunLike.coe.{u_2 + 1, u_2 + 1, 1} (IsDedekindDomain.HeightOneSpectrum.valuation.{u_1, u_2} K p) (c p)))
        (∀ (p : IsDedekindDomain.HeightOneSpectrum.{u_1} R),
          Not (Membership.mem.{u_1, u_1} T p) →
            LE.le.{0}
              (DFunLike.coe.{u_2 + 1, u_2 + 1, 1} (IsDedekindDomain.HeightOneSpectrum.valuation.{u_1, u_2} K p) t) 1) := by
  intro R _ _ K _ _ _ T a c hc
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors R) T a
  have hd0 : (b : R) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  have hdK : algebraMap R K (b : R) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hd0
  have hb' : ∀ i ∈ T, ∃ r : R, algebraMap R K r = algebraMap R K (b : R) * a i := by
    intro i hi
    obtain ⟨r, hr⟩ := hb i hi
    exact ⟨r, by rw [hr, Algebra.smul_def]⟩
  choose! x hx using hb'
  have hspan : Ideal.span {(b : R)} ≠ 0 := by
    rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  set S := (Ideal.finite_factors hspan).toFinset with hS
  let N : IsDedekindDomain.HeightOneSpectrum R → ℕ := fun p =>
    (WithZero.log (p.valuation K (c p) * p.intValuation (b : R))).natAbs
  let m : IsDedekindDomain.HeightOneSpectrum R → ℕ := fun q =>
    multiplicity q.asIdeal (Ideal.span {(b : R)})
  let e : IsDedekindDomain.HeightOneSpectrum R → ℕ := fun q => if q ∈ T then N q else m q
  let xx : (T ∪ S : Finset _) → R := fun i => if i.1 ∈ T then x i.1 else 0
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := T ∪ S)
    (fun q => q.asIdeal) e (fun q _ => q.prime)
    (fun q _ q' _ hne h => hne (IsDedekindDomain.HeightOneSpectrum.ext h)) xx
  refine ⟨algebraMap R K y / algebraMap R K (b : R), ?_, ?_⟩
  · intro p hp
    have h1 := hy p (Finset.mem_union_left _ hp)
    simp only [xx, e, hp, if_true] at h1
    have h2 := (p.intValuation_le_pow_iff_mem _ _).mpr h1
    have hcv : p.valuation K (c p) ≠ 0 := by simpa using hc p hp
    have hγ : p.valuation K (c p) * p.intValuation (b : R) ≠ 0 :=
      mul_ne_zero hcv (p.intValuation_ne_zero _ hd0)
    have h3 : WithZero.exp (-((N p : ℕ) : ℤ)) ≤ p.valuation K (c p) * p.intValuation (b : R) := by
      conv_rhs => rw [← WithZero.exp_log hγ]
      rw [WithZero.exp_le_exp]
      simp only [N]
      omega
    have key : (algebraMap R K y / algebraMap R K (b : R) - a p) * algebraMap R K (b : R)
        = algebraMap R K (y - x p) := by
      rw [map_sub, hx p hp, sub_mul, div_mul_cancel₀ _ hdK]; ring
    have h4 : p.valuation K (algebraMap R K y / algebraMap R K (b : R) - a p) * p.intValuation (b : R)
        ≤ p.valuation K (c p) * p.intValuation (b : R) := by
      have vb : p.valuation K (algebraMap R K (b : R)) = p.intValuation (b : R) := by
        rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
      have e1 : p.valuation K (algebraMap R K y / algebraMap R K (b : R) - a p) * p.intValuation (b : R)
          = p.intValuation (y - x p) := by
        rw [← vb, ← map_mul, key, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
      rw [e1]
      exact h2.trans h3
    exact ennreal_volume_ratio_step_cancel (p.intValuation_ne_zero _ hd0) h4
  · intro q hq
    have key : (algebraMap R K y / algebraMap R K (b : R)) * algebraMap R K (b : R)
        = algebraMap R K y := div_mul_cancel₀ _ hdK
    have h5 : q.intValuation y ≤ q.intValuation (b : R) := by
      by_cases hqS : q ∈ S
      · have h1 := hy q (Finset.mem_union_right _ hqS)
        simp only [xx, e, hq, if_false, sub_zero] at h1
        rw [q.intValuation_eq_exp_neg_multiplicity hd0]
        exact (q.intValuation_le_pow_iff_mem _ _).mpr h1
      · have hnd : ¬ q.asIdeal ∣ Ideal.span {(b : R)} := by
          simpa [hS] using hqS
        have hone : q.intValuation (b : R) = 1 := by
          refine le_antisymm (q.intValuation_le_one _) (not_lt.mp ?_)
          rw [q.intValuation_lt_one_iff_dvd]
          exact hnd
        rw [hone]
        exact q.intValuation_le_one _
    have h4 : q.valuation K (algebraMap R K y / algebraMap R K (b : R)) * q.intValuation (b : R)
        ≤ 1 * q.intValuation (b : R) := by
      have vb : q.valuation K (algebraMap R K (b : R)) = q.intValuation (b : R) := by
        rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
      have e1 : q.valuation K (algebraMap R K y / algebraMap R K (b : R)) * q.intValuation (b : R)
          = q.intValuation y := by
        rw [← vb, ← map_mul, key, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
      rw [e1, one_mul]
      exact h5
    exact ennreal_volume_ratio_step_cancel (q.intValuation_ne_zero _ hd0) h4
end Bl.VolumeRatioCancellation
