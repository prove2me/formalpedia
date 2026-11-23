-- Prove2me | solution 1 for Formalism.DivisionValues.LocalCovolumeBasis.len_on
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:15:58.593674+00:00
-- url     : https://prove2.me/submissions/329f109b-91fb-42e6-bbc4-efc445b9209e

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LcvBasis
import Theorems.Thm_P2M_Formalism_DivisionValues_LocalCovolumeBasis_mem_locP__ad3a70047646
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_le_locS


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
theorem _root_.solution {N : Submodule (𝓞 K) V} {a : V} (q : Ideal (𝓞 K)) [hq : q.IsPrime]
    (hqmax : q.IsMaximal) (hp : ∀ r, r ∈ q ↔ r • a ∈ N) :
    Module.length (𝓞 K) (↥(localization₂ q (N ⊔ Submodule.span (𝓞 K) {a})) ⧸
      (localization₂ q N).comap (localization₂ q (N ⊔ Submodule.span (𝓞 K) {a})).subtype) = 1 := by
  set M := N ⊔ Submodule.span (𝓞 K) {a} with hM
  have haM : a ∈ M := Submodule.mem_sup_right (Submodule.mem_span_singleton_self a)
  have haL : a ∈ localization₂ q M := locBasic_le_locS _ M haM
  set Q := (localization₂ q N).comap (localization₂ q M).subtype with hQ
  let f : 𝓞 K →ₗ[𝓞 K] ↥(localization₂ q M) ⧸ Q :=
    Q.mkQ ∘ₗ LinearMap.toSpanSingleton (𝓞 K) (↥(localization₂ q M)) ⟨a, haL⟩
  have hf : ∀ r, f r = Submodule.Quotient.mk (r • (⟨a, haL⟩ : ↥(localization₂ q M))) := fun r => rfl
  have hsurj : Function.Surjective f := by
    intro z
    induction z using Submodule.Quotient.induction_on with
    | H x =>
      obtain ⟨t, htq, htx⟩ := (mem_locP' q M x.1).mp x.2
      obtain ⟨n, hn, z, hz, hnz⟩ := Submodule.mem_sup.mp htx
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
      obtain ⟨u, i, hi, hui⟩ := hqmax.exists_inv htq
      refine ⟨u * c, ?_⟩
      rw [hf, Submodule.Quotient.eq]
      show ((u * c) • a - (x : V)) ∈ localization₂ q N
      refine (mem_locP' q N _).mpr ⟨t, htq, ?_⟩
      have hc : c = t * (u * c) + i * c := by linear_combination (-c) * hui
      have key : t • ((u * c) • a - (x : V)) = -((i * c) • a) - n := by
        rw [smul_sub, ← hnz, smul_smul]
        have : c • a = (t * (u * c)) • a + (i * c) • a := by rw [← add_smul, ← hc]
        rw [this]; abel
      rw [key]
      exact N.sub_mem (N.neg_mem ((hp _).mp (Ideal.mul_mem_right c q hi))) hn
  have hker : LinearMap.ker f = q := by
    ext r
    rw [LinearMap.mem_ker, hf, Submodule.Quotient.mk_eq_zero]
    constructor
    · intro h
      obtain ⟨t, htq, htr⟩ := (mem_locP' q N _).mp h
      have : (t * r) • a ∈ N := by rw [mul_smul]; exact htr
      exact ((hq.mem_or_mem ((hp _).mpr this)).resolve_left htq)
    · intro h
      exact locBasic_le_locS _ N ((hp r).mp h)
  have e : (↥(localization₂ q M) ⧸ Q) ≃ₗ[𝓞 K] (𝓞 K ⧸ q) :=
    (f.quotKerEquivOfSurjective hsurj).symm.trans (Submodule.quotEquivOfEq _ _ hker)
  have : IsSimpleModule (𝓞 K) (𝓞 K ⧸ q) := isSimpleModule_iff_isCoatom.mpr hqmax.out
  have : IsSimpleModule (𝓞 K) (↥(localization₂ q M) ⧸ Q) := IsSimpleModule.congr e
  exact Module.length_eq_one_iff.mpr inferInstance
end Formalism.DivisionValues.LocalCovolumeBasis
