-- Prove2me | solution 1 for Formalism.DivisionValues.indexChange_uniformizer
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:34:01.519925+00:00
-- url     : https://prove2.me/submissions/058115f5-8cd2-4d56-8e19-9dd2e9a5f505

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Theorems.Thm_Formalism_DivisionValues_idxChange_cnt_unit
import Theorems.Thm_Formalism_DivisionValues_idxChange_det_Dg
import Theorems.Thm_Formalism_DivisionValues_idxChange_act_Dg_alg
import Theorems.Thm_Formalism_HermitianLatticesTheory_indexBasic_locLen_self
import Theorems.Thm_Formalism_HermitianLatticesTheory_indexBasic_smul_locP
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_le_locS


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDedekindDomain Formalism.HermitianLatticesTheory
open scoped Matrix nonZeroDivisors
noncomputable section
open Formalism Formalism.DivisionValues
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] {d : ℕ}
namespace Formalism.DivisionValues
theorem _root_.solution (v : HeightOneSpectrum R) (i : Fin d) {ϖ t : R}
    (hcnt : FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ (algebraMap R K ϖ)) = 1)
    (htp : t ∉ v.asIdeal) (ht : ∀ x ∈ v.asIdeal, ∃ u : R, t * x = ϖ * u) :
    IdxChangeP v (idxChangeDg i (algebraMap R K ϖ)) := by
  intro e he
  rw [idxChange_act_Dg_alg, idxChange_det_Dg, hcnt]
  have : Nonempty (Fin d) := ⟨i⟩
  set p := v.asIdeal with hpdef
  set upd := Function.update e i (ϖ • e i) with hupd
  set A := Submodule.span R (Set.range e) with hAdef
  set B := Submodule.span R (Set.range upd) with hBdef
  have hupdi : upd i = ϖ • e i := by simp [upd]
  have hupdk : ∀ k, k ≠ i → upd k = e k := fun k hk => by simp [upd, Function.update_of_ne hk]
  have hBA : B ≤ A := by
    rw [hBdef, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    by_cases hk : k = i
    · subst hk; rw [hupdi]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    · rw [hupdk k hk]; exact Submodule.subset_span ⟨k, rfl⟩

  let be := basisOfLinearIndependentOfCardEqFinrank he (by simp)
  have hbe : ∀ k, be k = e k := fun k => by
    simp [be, coe_basisOfLinearIndependentOfCardEqFinrank]
  let f : (Fin d → K) →ₗ[R] K := (be.coord i).restrictScalars R
  have hf : ∀ k, f (e k) = if k = i then 1 else 0 := by
    intro k
    simp only [f, LinearMap.restrictScalars_apply, Basis.coord_apply, ← hbe, Basis.repr_self]
    by_cases hk : k = i
    · subst hk; simp
    · simp [hk]
  have hcoord : ∀ x ∈ B, ∃ u : R, f x = algebraMap R K (ϖ * u) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      by_cases hk : k = i
      · subst hk
        refine ⟨1, ?_⟩
        rw [hupdi, map_smul, hf, if_pos rfl, Algebra.smul_def, mul_one, mul_one]
      · refine ⟨0, ?_⟩
        rw [hupdk k hk, hf, if_neg hk]; simp
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨u, hu⟩ := hx
      obtain ⟨u', hu'⟩ := hy
      exact ⟨u + u', by rw [map_add, hu, hu', mul_add, map_add]⟩
    | smul a x _ hx =>
      obtain ⟨u, hu⟩ := hx
      exact ⟨a * u, by rw [map_smul, hu, Algebra.smul_def, ← map_mul]; ring_nf⟩
  have hK1 : ∀ r ∈ p, r • e i ∈ localization₂ p B := by
    intro r hr
    obtain ⟨u, hu⟩ := ht r hr
    refine ⟨t, htp, ?_⟩
    have : t • r • e i = u • upd i := by
      rw [hupdi, smul_smul, smul_smul, hu, mul_comm]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hK2 : ∀ r : R, r • e i ∈ localization₂ p B → r ∈ p := by
    intro r hr
    obtain ⟨s, hs, hsr⟩ := hr
    obtain ⟨u, hu⟩ := hcoord _ hsr
    rw [smul_smul, map_smul, hf, if_pos rfl, Algebra.smul_def, mul_one] at hu
    have h2 : s * r = ϖ * u := IsFractionRing.injective R K hu
    have hmem : s * r ∈ p := by
      rw [h2]
      exact Ideal.mul_mem_right _ _ (by
        by_contra hϖ
        have := idxChange_cnt_unit (K := K) v hϖ
        rw [hcnt] at this
        exact one_ne_zero this)
    rcases v.isPrime.mem_or_mem hmem with h | h
    · exact absurd h hs
    · exact h
  have hei : e i ∈ localization₂ p A := locBasic_le_locS _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let Q := ↥(localization₂ p A) ⧸ (localization₂ p B).comap (localization₂ p A).subtype
  let φ : R →ₗ[R] Q := LinearMap.toSpanSingleton R Q (Submodule.Quotient.mk ⟨e i, hei⟩)
  have hker : LinearMap.ker φ = p := by
    ext r
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply,
      SetLike.val_smul]
    exact ⟨hK2 r, hK1 r⟩
  have hsurj : Function.Surjective φ := by
    intro q
    induction q using Submodule.Quotient.induction_on with
    | H y =>
      obtain ⟨s, hs, hsy⟩ := y.2
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hsy
      obtain ⟨t', i', hi', hti⟩ := v.isMaximal.exists_inv hs
      refine ⟨t' * c i, ?_⟩
      rw [LinearMap.toSpanSingleton_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq,
        Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub, SetLike.val_smul]
      apply indexBasic_smul_locP p B hs
      have hsc : s * (t' * c i) = c i - i' * c i := by linear_combination (c i) * hti
      have key : s • ((t' * c i) • e i - (y : Fin d → K)) =
          -((i' * c i) • e i + ∑ k ∈ Finset.univ.erase i, c k • e k) := by
        rw [smul_sub, ← hc, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), smul_smul, hsc,
          sub_smul]
        abel
      rw [key]
      refine (localization₂ p B).neg_mem ((localization₂ p B).add_mem (hK1 _ (Ideal.mul_mem_right _ _ hi')) ?_)
      refine (localization₂ p B).sum_mem fun k hk => ?_
      have hki : k ≠ i := Finset.ne_of_mem_erase hk
      refine locBasic_le_locS _ _ ?_
      rw [← hupdk k hki]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have : IsSimpleModule R (R ⧸ p) :=
    isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp v.isMaximal)
  have hlen : Module.length R Q = 1 := by
    rw [← (LinearMap.quotKerEquivOfSurjective φ hsurj).length_eq,
      (Submodule.quotEquivOfEq _ _ hker).length_eq]
    exact Module.length_eq_one R _
  unfold lidx
  rw [inf_eq_right.mpr hBA, indexBasic_locLen_self]
  unfold locLen
  rw [hlen]
  simp
end Formalism.DivisionValues
