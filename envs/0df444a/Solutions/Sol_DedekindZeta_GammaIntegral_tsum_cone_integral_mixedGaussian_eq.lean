-- Prove2me | solution 1 for DedekindZeta.GammaIntegral.tsum_cone_integral_mixedGaussian_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:50:37.304911+00:00
-- url     : https://prove2.me/submissions/41a9e48b-c992-4dd1-97fc-45e9daefb92e

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_GammaIntegral
import Theorems.Thm_DedekindZeta_GammaIntegral_tsum_lintegral_enorm_cone_mixedGaussian_ne_top
import Theorems.Thm_DedekindZeta_GammaIntegral_cone_integral_orbit_collapse
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
attribute [local simp] DedekindZeta.Theta.gaussVSchwartz_apply
attribute [local simp] DedekindZeta.Theta.mixedGaussianSchwartz_apply



set_option autoImplicit true
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory
open scoped Real ENNReal
open DedekindZeta DedekindZeta.GammaIntegral
open DedekindZeta DedekindZeta.Theta
open NumberField.Units NumberField.Units.dirichletUnitTheorem
attribute [local instance] DedekindZeta.coneMulAction DedekindZeta.coneMeasurableConstSMul
  DedekindZeta.coneCountable DedekindZeta.coneSMulInvariantMeasure
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
open scoped nonZeroDivisors
set_option maxHeartbeats 1600000
variable {K}
namespace DedekindZeta.GammaIntegral
theorem _root_.solution (s : ℂ) (hs : 1 < s.re)
    {a : Ideal (RingOfIntegers K)} (ha : a ≠ 0) :
    ∑' a' : {a' : RingOfIntegers K // a' ∈ a ∧ a' ≠ 0},
          ∫ x, (mixedEmbedding.fundamentalCone K).indicator
              (fun x => (mixedGaussian K
                  (x * mixedEmbedding K ((a'.1 : RingOfIntegers K) : K)) : ℂ)
                * (mixedEmbedding.norm x : ℂ) ^ s) x ∂(mixedMulHaar K)
      = (Units.torsionOrder K : ℂ) * I K s *
          ∑' I : {I : (Ideal (RingOfIntegers K))⁰ //
                    (a ∣ (I : Ideal (RingOfIntegers K))) ∧
                      Submodule.IsPrincipal (I : Ideal (RingOfIntegers K))},
              (Ideal.absNorm (I : Ideal (RingOfIntegers K)) : ℂ) ^ (-s) := by
  classical
  set T := {a' : RingOfIntegers K // a' ∈ a ∧ a' ≠ 0} with hT
  set Idx := {J : (Ideal (RingOfIntegers K))⁰ //
      (a ∣ (J : Ideal (RingOfIntegers K))) ∧
        Submodule.IsPrincipal (J : Ideal (RingOfIntegers K))} with hIdx
  -- The element-wise cone-integral summand.
  set Φ : T → ℂ := fun a' => ∫ x, (mixedEmbedding.fundamentalCone K).indicator
      (fun x => (mixedGaussian K
          (x * mixedEmbedding K ((a'.1 : RingOfIntegers K) : K)) : ℂ)
        * (mixedEmbedding.norm x : ℂ) ^ s) x ∂(mixedMulHaar K) with hΦ
  -- A chosen generator of each principal ideal in the index set.
  let gen : Idx → RingOfIntegers K := fun J =>
    letI := J.2.2
    Submodule.IsPrincipal.generator
      ((J : (Ideal (RingOfIntegers K))⁰) : Ideal (RingOfIntegers K))
  have hgen : ∀ J : Idx, ((J : (Ideal (RingOfIntegers K))⁰) : Ideal (RingOfIntegers K))
      = Ideal.span {gen J} := by
    intro J
    letI := J.2.2
    exact (Submodule.IsPrincipal.span_singleton_generator _).symm
  -- The generator is nonzero (its span is the nonzero ideal `J`).
  have hgne : ∀ J : Idx, gen J ≠ 0 := by
    intro J h
    have hbot : ((J : (Ideal (RingOfIntegers K))⁰) : Ideal (RingOfIntegers K)) = ⊥ := by
      rw [hgen J, h]; exact Ideal.span_singleton_eq_bot.mpr rfl
    exact (mem_nonZeroDivisors_iff_ne_zero.mp J.1.2)
      (by rw [Ideal.zero_eq_bot]; exact hbot)
  -- The generator lies in `a` (since `a ∣ J = span {gen J}`).
  have hmemgen : ∀ J : Idx, gen J ∈ a := by
    intro J
    have hle : (Ideal.span {gen J} : Ideal (RingOfIntegers K)) ≤ a := by
      rw [← hgen J]; exact Ideal.dvd_iff_le.mp J.2.1
    exact (Ideal.span_singleton_le_iff_mem a).mp hle
  -- `span {↑u * x} = span {x}` for a unit `u`.
  have hspan_unit : ∀ (u : (RingOfIntegers K)ˣ) (x : RingOfIntegers K),
      Ideal.span {(u : RingOfIntegers K) * x} = Ideal.span {x} := by
    intro u x
    rw [Ideal.span_singleton_eq_span_singleton]
    exact ⟨u⁻¹, by rw [mul_right_comm, Units.mul_inv, one_mul]⟩
  -- The reindexing map `Σ J, units → {a' ∈ a, a' ≠ 0}`, `(J, u) ↦ ↑u · gen J`.
  set f : (Σ _ : Idx, (RingOfIntegers K)ˣ) → T :=
    fun p => ⟨(p.2 : RingOfIntegers K) * gen p.1,
      Ideal.mul_mem_left a (p.2 : RingOfIntegers K) (hmemgen p.1),
      mul_ne_zero p.2.ne_zero (hgne p.1)⟩ with hf
  have hinj : Function.Injective f := by
    rintro ⟨J1, u1⟩ ⟨J2, u2⟩ h
    have hval : (u1 : RingOfIntegers K) * gen J1 = (u2 : RingOfIntegers K) * gen J2 := by
      have := congrArg Subtype.val h
      simpa [hf] using this
    have hJ : ((J1 : (Ideal (RingOfIntegers K))⁰) : Ideal (RingOfIntegers K))
        = ((J2 : (Ideal (RingOfIntegers K))⁰) : Ideal (RingOfIntegers K)) := by
      rw [hgen J1, hgen J2, ← hspan_unit u1 (gen J1), ← hspan_unit u2 (gen J2), hval]
    have hJeq : J1 = J2 := Subtype.ext (Subtype.ext hJ)
    subst hJeq
    have huu := mul_right_cancel₀ (hgne J1) hval
    exact congrArg (Sigma.mk J1) (Units.ext huu)
  have hsurj : Function.Surjective f := by
    rintro ⟨a', ha'mem, ha'ne⟩
    have hJne : Ideal.span {a'} ∈ (Ideal (RingOfIntegers K))⁰ := by
      rw [mem_nonZeroDivisors_iff_ne_zero]
      intro h
      exact ha'ne (Ideal.span_singleton_eq_bot.mp (by rw [← Ideal.zero_eq_bot]; exact h))
    have hdvd : a ∣ ((⟨Ideal.span {a'}, hJne⟩ : (Ideal (RingOfIntegers K))⁰) :
        Ideal (RingOfIntegers K)) :=
      Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem a).mpr ha'mem)
    have hprin : Submodule.IsPrincipal
        ((⟨Ideal.span {a'}, hJne⟩ : (Ideal (RingOfIntegers K))⁰) :
          Ideal (RingOfIntegers K)) := ⟨a', rfl⟩
    set J : Idx := ⟨⟨Ideal.span {a'}, hJne⟩, hdvd, hprin⟩ with hJdef
    have hgenJ : Ideal.span {a'} = Ideal.span {gen J} := hgen J
    obtain ⟨v, hv⟩ := Ideal.span_singleton_eq_span_singleton.mp hgenJ
    refine ⟨⟨J, v⁻¹⟩, ?_⟩
    apply Subtype.ext
    show ((v⁻¹ : (RingOfIntegers K)ˣ) : RingOfIntegers K) * gen J = a'
    rw [← hv, mul_comm a' (v : RingOfIntegers K), ← mul_assoc, Units.inv_mul, one_mul]
  set e : (Σ _ : Idx, (RingOfIntegers K)ˣ) ≃ T := Equiv.ofBijective f ⟨hinj, hsurj⟩ with he
  -- Summability of the `a'`-family from the L¹/Tonelli finiteness.
  have hfin := tsum_lintegral_enorm_cone_mixedGaussian_ne_top s hs ha
  have hbsum : Summable (fun a' : T => (∫⁻ x, ‖(mixedEmbedding.fundamentalCone K).indicator
        (fun x => (mixedGaussian K
            (x * mixedEmbedding K ((a'.1 : RingOfIntegers K) : K)) : ℂ)
          * (mixedEmbedding.norm x : ℂ) ^ s) x‖ₑ ∂(mixedMulHaar K)).toReal) :=
    ENNReal.summable_toReal hfin
  have hbound : ∀ a' : T, ‖Φ a'‖ ≤ (∫⁻ x, ‖(mixedEmbedding.fundamentalCone K).indicator
        (fun x => (mixedGaussian K
            (x * mixedEmbedding K ((a'.1 : RingOfIntegers K) : K)) : ℂ)
          * (mixedEmbedding.norm x : ℂ) ^ s) x‖ₑ ∂(mixedMulHaar K)).toReal := by
    intro a'
    have hne := ENNReal.ne_top_of_tsum_ne_top hfin a'
    have key : ‖Φ a'‖ₑ ≤ ∫⁻ x, ‖(mixedEmbedding.fundamentalCone K).indicator
        (fun x => (mixedGaussian K
            (x * mixedEmbedding K ((a'.1 : RingOfIntegers K) : K)) : ℂ)
          * (mixedEmbedding.norm x : ℂ) ^ s) x‖ₑ ∂(mixedMulHaar K) := by
      simp only [hΦ]; exact enorm_integral_le_lintegral_enorm _
    calc ‖Φ a'‖ = (‖Φ a'‖ₑ).toReal := (toReal_enorm (Φ a')).symm
      _ ≤ _ := ENNReal.toReal_mono hne key
  have hΦsum : Summable Φ := Summable.of_norm_bounded hbsum hbound
  have hcompsum : Summable (fun p => Φ (e p)) := (Equiv.summable_iff e).mpr hΦsum
  -- The single-orbit collapse evaluates each inner unit-sum.
  have hinner : ∀ J : Idx, (∑' u : (RingOfIntegers K)ˣ, Φ (e ⟨J, u⟩))
      = (Units.torsionOrder K : ℂ) * I K s
          * (Ideal.absNorm ((J : (Ideal (RingOfIntegers K))⁰) :
              Ideal (RingOfIntegers K)) : ℂ) ^ (-s) := by
    intro J
    have hc := cone_integral_orbit_collapse s hs (hgne J)
    rw [← hgen J] at hc
    rw [← hc]
    exact tsum_congr (fun u => rfl)
  rw [← Equiv.tsum_eq e Φ,
    hcompsum.tsum_sigma' (fun J => hcompsum.comp_injective sigma_mk_injective)]
  refine Eq.trans (tsum_congr (fun J => hinner J)) ?_
  rw [tsum_mul_left]
end DedekindZeta.GammaIntegral
