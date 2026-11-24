-- Prove2me | solution 1 for Formalism.L2.DIV.unitary_one_mem_range_norm_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:04:02.525275+00:00
-- url     : https://prove2.me/submissions/91c5bf08-55db-4793-9342-ee53b2e8d4a4

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP
import Theorems.Thm_Formalism_L2_DIV_conjugation_tmul
import Theorems.Thm_Formalism_L2_DIV_adele_trace_from_base
import Theorems.Thm_Formalism_L2_DIV_finite_adele_is_unit
import Theorems.Thm_Formalism_L2_DIV_valuation_eq_one_eventually

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain TensorProduct Formalism.UG Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.UG.P
open scoped nonZeroDivisors
open Formalism Formalism.L2 Formalism.L2.DIV
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
namespace Formalism.L2.DIV
theorem _root_.solution (σ : E →ₐ[F] E) (hσ : IsConjOf σ) (y : (AfE F E)ˣ) (hy : y ∈ U1 σ) :
    y ∈ (h90 σ).range := by
  classical
  obtain ⟨hne, hinv, hfix⟩ := hσ
  have hex : ∃ e, σ e ≠ e := by
    by_contra hcon
    exact hne (AlgHom.ext fun e => by
      by_contra h
      exact hcon ⟨e, h⟩)
  obtain ⟨e0, he0⟩ := hex
  obtain ⟨θ, hθ⟩ : ∃ θ, θ = e0 - σ e0 := ⟨_, rfl⟩
  have hθ0 : θ ≠ 0 := by rw [hθ]; exact sub_ne_zero.mpr (Ne.symm he0)
  have hσθ : σ θ = -θ := by rw [hθ, map_sub, hinv]; ring
  obtain ⟨D, hD⟩ := hfix (θ * θ) (by rw [map_mul, hσθ]; ring)
  have hD0 : D ≠ 0 := by
    rintro rfl
    rw [map_zero] at hD
    exact hθ0 (mul_self_eq_zero.mp hD.symm)
  obtain ⟨Y, hY⟩ : ∃ Y : AfE F E, Y = (y : AfE F E) := ⟨_, rfl⟩
  obtain ⟨Y', hY'⟩ : ∃ Y' : AfE F E, Y' = ((y⁻¹ : (AfE F E)ˣ) : AfE F E) := ⟨_, rfl⟩
  have hYY : Y * Y' = 1 := by rw [hY, hY']; exact y.mul_inv
  have hsY : sigR σ 𝔸 Y = Y' := by
    have h1 : y * conjId σ y = 1 := hy
    have h2 : conjId σ y = y⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [hY, hY', ← h2]
    rfl
  obtain ⟨T, hT⟩ := adele_trace_from_base σ hinv hfix Y
  rw [hsY] at hT
  let iR : 𝔸 →ₐ[F] AfE F E := Algebra.TensorProduct.includeRight
  have hT' : iR T = Y + Y' := hT
  let Sp : Set (HeightOneSpectrum (𝓞 F)) :=
    {v | Valued.v (2 + T v) = 1 ∨ (Valued.v (2 - T v) ≠ 1 ∧ 2 + T v ≠ 0)}
  let ep : 𝔸 := ⟨fun v => if v ∈ Sp then 1 else 0, Filter.Eventually.of_forall (fun v => by
    show (if v ∈ Sp then (1 : v.adicCompletion F) else 0) ∈ v.adicCompletionIntegers F
    split_ifs
    · exact one_mem _
    · exact zero_mem _)⟩
  have hep : ∀ v, ep v = if v ∈ Sp then 1 else 0 := fun v => rfl
  have hpp : ep * ep = ep := by
    refine FiniteAdeleRing.ext _ fun v => ?_
    show ep v * ep v = ep v
    rw [hep]
    split_ifs <;> simp
  obtain ⟨m, hmdef⟩ : ∃ m : 𝔸, m = ep * (2 + T) + (1 - ep) * (algebraMap F 𝔸 (-D) * (2 - T)) := ⟨_, rfl⟩
  have hm : ∀ v, m v = if v ∈ Sp then 2 + T v
      else algebraMap F (v.adicCompletion F) (-D) * (2 - T v) := by
    intro v
    have h1 : m v = ep v * (2 + T v) +
        (1 - ep v) * (algebraMap F (v.adicCompletion F) (-D) * (2 - T v)) := by
      show evalV F v m = evalV F v ep * (2 + evalV F v T) +
        (1 - evalV F v ep) * (algebraMap F (v.adicCompletion F) (-D) * (2 - evalV F v T))
      rw [hmdef]
      simp only [map_add, map_mul, map_sub, map_one, map_ofNat, AlgHom.commutes]
    rw [h1, hep]
    split_ifs <;> simp
  have h4 : ∀ v : HeightOneSpectrum (𝓞 F), (4 : v.adicCompletion F) ≠ 0 := by
    intro v
    rw [← map_ofNat (algebraMap F (v.adicCompletion F)) 4]
    exact (map_ne_zero _).mpr (by norm_num)
  have hmU : IsUnit m := by
    apply finite_adele_is_unit
    · intro v
      rw [hm]
      split_ifs with hv
      · rcases hv with hv | hv
        · intro h
          rw [h, map_zero] at hv
          exact zero_ne_one hv
        · exact hv.2
      · have hv' : ¬ (Valued.v (2 + T v) = 1 ∨ (Valued.v (2 - T v) ≠ 1 ∧ 2 + T v ≠ 0)) := hv
        rw [not_or, not_and_or, not_not, not_not] at hv'
        refine mul_ne_zero ((map_ne_zero _).mpr (neg_ne_zero.mpr hD0)) ?_
        rcases hv'.2 with h | h
        · intro h'
          rw [h', map_zero] at h
          exact zero_ne_one h
        · have : 2 - T v = 4 := by linear_combination -h
          rw [this]
          exact h4 v
    · filter_upwards [T.2, valuation_eq_one_eventually (F := F) 2 (by norm_num), valuation_eq_one_eventually (F := F) 4 (by norm_num),
        valuation_eq_one_eventually D hD0] with v hTv h2v h4v hDv
      have hTv' : Valued.v (T v) ≤ 1 := hTv
      rw [map_ofNat] at h2v h4v
      have hle1 : Valued.v (2 + T v) ≤ 1 := (Valuation.map_add _ _ _).trans (max_le h2v.le hTv')
      have hle2 : Valued.v (2 - T v) ≤ 1 := (Valuation.map_sub _ _ _).trans (max_le h2v.le hTv')
      have hor : Valued.v (2 + T v) = 1 ∨ Valued.v (2 - T v) = 1 := by
        by_contra hcon
        rw [not_or] at hcon
        have := Valuation.map_add_lt (Valued.v) (lt_of_le_of_ne hle1 hcon.1) (lt_of_le_of_ne hle2 hcon.2)
        rw [show (2 + T v) + (2 - T v) = 4 by ring, h4v] at this
        exact lt_irrefl _ this
      rw [hm]
      split_ifs with hv
      · rcases hv with hv | hv
        · exact hv
        · exact hor.resolve_right hv.1
      · have hv' : ¬ (Valued.v (2 + T v) = 1 ∨ (Valued.v (2 - T v) ≠ 1 ∧ 2 + T v ≠ 0)) := hv
        rw [not_or] at hv'
        rw [map_mul, map_neg, Valuation.map_neg, hDv, one_mul]
        exact hor.resolve_left hv'.1
  obtain ⟨p, hpdef⟩ : ∃ p : AfE F E, p = iR ep := ⟨_, rfl⟩
  obtain ⟨t, htdef⟩ : ∃ t : AfE F E, t = θ ⊗ₜ[F] (1 : 𝔸) := ⟨_, rfl⟩
  obtain ⟨d, hddef⟩ : ∃ d : AfE F E, d = iR (algebraMap F 𝔸 D) := ⟨_, rfl⟩
  have hp : p * p = p := by rw [hpdef, ← map_mul, hpp]
  have hsp : sigR σ 𝔸 p = p := by
    rw [hpdef]
    show sigR σ 𝔸 ((1 : E) ⊗ₜ[F] ep) = (1 : E) ⊗ₜ[F] ep
    rw [conjugation_tmul, map_one]
  have hst : sigR σ 𝔸 t = -t := by rw [htdef, conjugation_tmul, hσθ, TensorProduct.neg_tmul]
  have htt : t * t = d := by
    rw [htdef, hddef, Algebra.TensorProduct.tmul_mul_tmul, ← hD, mul_one]
    show algebraMap F E D ⊗ₜ[F] (1 : 𝔸) = (1 : E) ⊗ₜ[F] algebraMap F 𝔸 D
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  obtain ⟨X, hX⟩ : ∃ X : AfE F E, X = p * (1 + Y) + (1 - p) * t * (1 - Y) := ⟨_, rfl⟩
  have hsX : sigR σ 𝔸 X = p * (1 + Y') - (1 - p) * t * (1 - Y') := by
    rw [hX]
    simp only [map_add, map_mul, map_sub, map_one, hsp, hst, hsY]
    ring
  have hYX : Y * sigR σ 𝔸 X = X := by
    rw [hsX, hX]
    linear_combination (p + (1 - p) * t) * hYY
  have him : iR m = p * (2 + (Y + Y')) + (1 - p) * (-d * (2 - (Y + Y'))) := by
    rw [hmdef, hpdef, hddef, ← hT']
    simp only [map_add, map_mul, map_sub, map_one, map_ofNat, map_neg]
  have hXX : X * sigR σ 𝔸 X = iR m := by
    rw [him, hsX, hX]
    linear_combination ((1 + Y) * (1 + Y') - (-t * (1 + Y) * (1 - Y') + t * (1 - Y) * (1 + Y'))
      - t * t * ((1 - Y) * (1 - Y'))) * hp - (1 - p) * ((1 - Y) * (1 - Y')) * htt
      + (p - (1 - p) * d) * hYY
  have hXU : IsUnit X := by
    apply isUnit_of_mul_isUnit_left (y := sigR σ 𝔸 X)
    rw [hXX]
    exact hmU.map iR
  obtain ⟨Xu, hXu⟩ := hXU
  refine ⟨Xu, ?_⟩
  show Xu / conjId σ Xu = y
  rw [div_eq_iff_eq_mul]
  apply Units.ext
  show (Xu : AfE F E) = (y : AfE F E) * sigR σ 𝔸 (Xu : AfE F E)
  rw [hXu, ← hY, hYX]
end Formalism.L2.DIV
