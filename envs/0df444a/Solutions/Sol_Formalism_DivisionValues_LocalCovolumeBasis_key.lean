-- Prove2me | solution 1 for Formalism.DivisionValues.LocalCovolumeBasis.key
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:26:37.729925+00:00
-- url     : https://prove2.me/submissions/9056ef7e-3825-42bb-ae0b-cb47b10b2c19

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LcvBasis
import Theorems.Thm_Formalism_DivisionValues_LocalCovolumeBasis_len_zero_of_le
import Theorems.Thm_Formalism_DivisionValues_LocalCovolumeBasis_len_off
import Theorems.Thm_Formalism_DivisionValues_LocalCovolumeBasis_len_on
import Theorems.Thm_Formalism_DivisionValues_LocalCovolumeBasis_le_of_image
import Theorems.Thm_Formalism_HermitianLatticesTheory_indexBasic_len_add
import Theorems.Thm_Formalism_HermitianLatticesTheory_indexBasic_locLen_self
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_locS_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Formalism.HermitianLatticesTheory
noncomputable section
open Formalism Formalism.DivisionValues Formalism.DivisionValues.LocalCovolumeBasis
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module (𝓞 K) V]
namespace Formalism.DivisionValues.LocalCovolumeBasis
theorem _root_.solution (A : Submodule (𝓞 K) V) : ∀ (n : ℕ) (N : Submodule (𝓞 K) V), N ≤ A →
    N.toAddSubgroup.relIndex A.toAddSubgroup = n → n ≠ 0 →
    (∀ w : HeightOneSpectrum (𝓞 K), Module.length (𝓞 K)
      (↥(localization₂ w.asIdeal A) ⧸ (localization₂ w.asIdeal N).comap (localization₂ w.asIdeal A).subtype) ≠ ⊤) ∧
    (Function.support fun w : HeightOneSpectrum (𝓞 K) => locLen w.asIdeal A N).Finite ∧
    Real.log (n : ℝ) = ∑ᶠ w : HeightOneSpectrum (𝓞 K),
      Real.log (Ideal.absNorm w.asIdeal : ℝ) * (locLen w.asIdeal A N : ℝ) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro N hNA hn hn0
  by_cases hEq : N = A
  · subst hEq
    have h0 : ∀ w : HeightOneSpectrum (𝓞 K), locLen w.asIdeal N N = 0 :=
      fun w => indexBasic_locLen_self _ _
    have hn1 : n = 1 := by rw [← hn]; exact AddSubgroup.relIndex_self _
    refine ⟨fun w => by rw [len_zero_of_le _ _ le_rfl]; exact ENat.zero_ne_top, ?_, ?_⟩
    · simp [h0]
    · simp [h0, hn1]
  have hlt : N < A := lt_of_le_of_ne hNA hEq
  have hfin : Finite (↥A ⧸ N.comap A.subtype) := by
    apply Nat.finite_of_card_ne_zero
    rw [← hn] at hn0
    exact hn0

  set S : Set (Submodule (𝓞 K) V) := {M | N < M ∧ M ≤ A} with hS
  have hSfin : S.Finite := by
    apply Set.Finite.of_finite_image (f := fun M : Submodule (𝓞 K) V =>
      (N.comap A.subtype).mkQ '' (A.subtype ⁻¹' (M : Set V))) (Set.toFinite _)
    intro M1 h1 M2 h2 himg
    exact le_antisymm (le_of_image h2.1.le h1.2 himg) (le_of_image h1.1.le h2.2 himg.symm)
  obtain ⟨M0, hM0⟩ := hSfin.exists_minimal ⟨A, hlt, le_rfl⟩
  have hM0S : M0 ∈ S := hM0.1
  have hmin : ∀ M, N < M → M ≤ M0 → M = M0 := fun M h1 h2 =>
    le_antisymm h2 (hM0.2 ⟨h1, h2.trans hM0S.2⟩ h2)
  obtain ⟨a, haM0, haN⟩ := SetLike.exists_of_lt hM0S.1
  have hstep : ∀ b ∈ M0, b ∉ N → N ⊔ Submodule.span (𝓞 K) {b} = M0 := by
    intro b hb hbN
    apply hmin
    · refine lt_of_le_of_ne le_sup_left fun h => hbN ?_
      rw [h]; exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self b)
    · exact sup_le hM0S.1.le ((Submodule.span_singleton_le_iff_mem _ _).mpr hb)
  have hM0eq : M0 = N ⊔ Submodule.span (𝓞 K) {a} := (hstep a haM0 haN).symm

  set p : Ideal (𝓞 K) := N.comap (LinearMap.toSpanSingleton (𝓞 K) V a) with hpdef
  have hp : ∀ r, r ∈ p ↔ r • a ∈ N := fun r => Iff.rfl
  have hpmax : p.IsMaximal := by
    rw [Ideal.isMaximal_iff]
    refine ⟨fun h => haN (by simpa using (hp 1).mp h), ?_⟩
    intro J x hpJ hxp hxJ
    have hxa : x • a ∈ M0 := M0.smul_mem x haM0
    have hxaN : x • a ∉ N := fun h => hxp ((hp x).mpr h)
    have e := hstep _ hxa hxaN
    have ha' : a ∈ N ⊔ Submodule.span (𝓞 K) {x • a} := e ▸ haM0
    obtain ⟨m, hm, z, hz, hmz⟩ := Submodule.mem_sup.mp ha'
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hz
    have h1 : (1 - s * x) ∈ p := by
      rw [hp, sub_smul, one_smul, mul_smul]
      rw [sub_eq_iff_eq_add.mpr hmz.symm]
      exact hm
    have h2 : s * x ∈ J := J.mul_mem_left s hxJ
    have := J.add_mem (hpJ h1) h2
    simpa using this

  have hcard : N.toAddSubgroup.relIndex M0.toAddSubgroup = Ideal.absNorm p := by
    have haM0' : a ∈ M0 := haM0
    let g : 𝓞 K →ₗ[𝓞 K] ↥M0 ⧸ N.comap M0.subtype :=
      (N.comap M0.subtype).mkQ ∘ₗ LinearMap.toSpanSingleton (𝓞 K) (↥M0) ⟨a, haM0'⟩
    have hg : ∀ r, g r = Submodule.Quotient.mk (r • (⟨a, haM0'⟩ : ↥M0)) := fun r => rfl
    have hgs : Function.Surjective g := by
      intro z
      induction z using Submodule.Quotient.induction_on with
      | H x =>
        have hx : (x : V) ∈ N ⊔ Submodule.span (𝓞 K) {a} := hM0eq ▸ x.2
        obtain ⟨m, hm, z, hz, hmz⟩ := Submodule.mem_sup.mp hx
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
        refine ⟨c, ?_⟩
        rw [hg, Submodule.Quotient.eq]
        show (c • a - (x : V)) ∈ N
        rw [← hmz]
        have : c • a - (m + c • a) = -m := by abel
        rw [this]; exact N.neg_mem hm
    have hker : LinearMap.ker g = p := by
      ext r
      rw [LinearMap.mem_ker, hg, Submodule.Quotient.mk_eq_zero, hp]
      rfl
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    exact (Nat.card_congr (((Submodule.quotEquivOfEq _ _ hker.symm).trans
      (g.quotKerEquivOfSurjective hgs)).toEquiv)).symm
  set m := M0.toAddSubgroup.relIndex A.toAddSubgroup with hmdef
  have hprod : Ideal.absNorm p * m = n := by
    rw [← hcard, hmdef, AddSubgroup.relIndex_mul_relIndex _ _ _ hM0S.1.le hM0S.2, hn]
  have hm0 : m ≠ 0 := fun h => hn0 (by rw [← hprod, h, mul_zero])
  have hN0 : Ideal.absNorm p ≠ 0 := fun h => hn0 (by rw [← hprod, h, zero_mul])
  have hN1 : Ideal.absNorm p ≠ 1 := fun h => hpmax.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  have hmn : m < n := by
    rw [← hprod]
    have : 2 ≤ Ideal.absNorm p := by omega
    calc m = 1 * m := (one_mul m).symm
      _ < Ideal.absNorm p * m := Nat.mul_lt_mul_of_pos_right (by omega) (Nat.pos_of_ne_zero hm0)
  obtain ⟨ihlen, ihsupp, ihlog⟩ := ih m hmn M0 hM0S.2 rfl hm0
  have hpbot : p ≠ ⊥ := fun h => hN0 (Ideal.absNorm_eq_zero_iff.mpr h)
  let w0 : HeightOneSpectrum (𝓞 K) := ⟨p, hpmax.isPrime, hpbot⟩

  have hsmall : ∀ w : HeightOneSpectrum (𝓞 K), Module.length (𝓞 K)
      (↥(localization₂ w.asIdeal M0) ⧸ (localization₂ w.asIdeal N).comap (localization₂ w.asIdeal M0).subtype) =
        ((if w = w0 then 1 else 0 : ℕ) : ℕ∞) := by
    intro w
    rw [hM0eq]
    by_cases hw : w = w0
    · have hwp : w.asIdeal = p := by rw [hw]
      rw [if_pos hw]
      have := len_on (N := N) (a := a) w.asIdeal (hwp ▸ hpmax) (fun r => by rw [hwp]; exact hp r)
      rw [this]; rfl
    · rw [if_neg hw]
      have hwp : w.asIdeal ≠ p := fun h => hw (HeightOneSpectrum.ext h)
      have := len_off (N := N) (a := a) hpmax hp w.asIdeal w.isMaximal.ne_top hwp
      rw [this]; rfl
  have hadd : ∀ w : HeightOneSpectrum (𝓞 K), Module.length (𝓞 K)
      (↥(localization₂ w.asIdeal A) ⧸ (localization₂ w.asIdeal N).comap (localization₂ w.asIdeal A).subtype) =
      Module.length (𝓞 K)
      (↥(localization₂ w.asIdeal M0) ⧸ (localization₂ w.asIdeal N).comap (localization₂ w.asIdeal M0).subtype) +
      Module.length (𝓞 K)
      (↥(localization₂ w.asIdeal A) ⧸ (localization₂ w.asIdeal M0).comap (localization₂ w.asIdeal A).subtype) :=
    fun w => indexBasic_len_add _ _ _ (locBasic_locS_mono _ hM0S.1.le)
      (locBasic_locS_mono _ hM0S.2)
  have hlen : ∀ w : HeightOneSpectrum (𝓞 K),
      locLen w.asIdeal A N = (if w = w0 then 1 else 0) + locLen w.asIdeal A M0 := by
    intro w
    unfold locLen
    rw [hadd w, hsmall w, ENat.toNat_add (ENat.natCast_ne_top _) (ihlen w), ENat.toNat_natCast]
  refine ⟨fun w => by rw [hadd w, hsmall w]; exact WithTop.add_ne_top.mpr ⟨ENat.natCast_ne_top _, ihlen w⟩,
    ?_, ?_⟩
  · apply (ihsupp.union (Set.finite_singleton w0)).subset
    intro w hw
    rw [Function.mem_support, hlen w] at hw
    by_cases h : w = w0
    · exact Or.inr h
    · left
      rw [if_neg h, zero_add] at hw
      exact hw
  · have hsum : (fun w : HeightOneSpectrum (𝓞 K) =>
        Real.log (Ideal.absNorm w.asIdeal : ℝ) * (locLen w.asIdeal A N : ℝ)) =
        fun w => Real.log (Ideal.absNorm w.asIdeal : ℝ) * ((if w = w0 then 1 else 0 : ℕ) : ℝ) +
          Real.log (Ideal.absNorm w.asIdeal : ℝ) * (locLen w.asIdeal A M0 : ℝ) := by
      funext w
      rw [hlen w]; push_cast; ring
    rw [hsum, finsum_add_distrib, ← ihlog, finsum_eq_single _ w0]
    · rw [if_pos rfl, ← hprod]
      push_cast
      rw [Real.log_mul (by exact_mod_cast hN0) (by exact_mod_cast hm0)]
      simp [w0]
    · intro w hw; simp [hw]
    · apply (Set.finite_singleton w0).subset
      intro w hw
      by_contra h
      have h' : w ≠ w0 := h
      apply hw
      simp [h']
    · apply ihsupp.subset
      intro w hw
      rw [Function.mem_support] at hw ⊢
      intro h; apply hw; rw [h]; simp
end Formalism.DivisionValues.LocalCovolumeBasis
