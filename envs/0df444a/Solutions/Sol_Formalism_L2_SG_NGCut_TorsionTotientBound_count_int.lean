-- Prove2me | solution 1 for Formalism.L2.SG.NGCut.TorsionTotientBound.count_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:52:51.267917+00:00
-- url     : https://prove2.me/submissions/2b580a17-c642-427a-a507-49ee7acb13b3

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_TwoLeAbsNormPrime
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_MemTorsionOfMulConj
import Theorems.Thm_Formalism_L2_SG_NGCut_TorsionTotientBound_cO_coe
import Theorems.Thm_Formalism_L2_SG_NGCut_TorsionTotientBound_mem_torsion_of_mul_conj
import Theorems.Thm_Formalism_L2_SG_NGCut_TorsionTotientBound_absNorm_map_equiv
import Theorems.Thm_Formalism_L2_SG_NGCut_TorsionTotientBound_card_dvd_le_absNorm
import Theorems.Thm_Formalism_L2_SG_NGCut_TorsionTotientBound_torsionOrder_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.NGCut Formalism.L2.SG.NGCut.TorsionTotientBound
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace Formalism.L2.SG.NGCut.TorsionTotientBound
theorem _root_.solution (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) (m : 𝓞 E) (hm : m ≠ 0) (S : Finset (𝓞 E))
    (hS : ∀ y ∈ S, y ∈ I ∧ y * cO E y = m) :
    S.card * Ideal.absNorm I ^ 2 ≤ 2 * (Module.finrank ℚ E) ^ 2 * (Algebra.norm ℤ m).natAbs := by
  classical
  haveI : Fintype (Units.torsion E) := Fintype.ofFinite _
  rcases S.eq_empty_or_nonempty with hS0 | ⟨y0, hy0⟩
  · simp [hS0]
  have hNI' : Ideal.absNorm (I.map (cO E)) = Ideal.absNorm I :=
    absNorm_map_equiv (cO E) I
  have hI0 : Ideal.absNorm I ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have hI'0 : I.map (cO E) ≠ ⊥ := by
    intro h; apply hI0; rw [← hNI']; exact Ideal.absNorm_eq_zero_iff.mpr h
  have hdvdI : ∀ y ∈ S, I ∣ Ideal.span {y} := fun y hy =>
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem I).mpr (hS y hy).1)
  have hdvdI' : ∀ y ∈ S, I.map (cO E) ∣ Ideal.span {cO E y} := fun y hy =>
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr
      (Ideal.mem_map_of_mem (cO E) (hS y hy).1))
  have hspan : ∀ y ∈ S, Ideal.span {y} * Ideal.span {cO E y} = Ideal.span {m} :=
    fun y hy => by rw [Ideal.span_singleton_mul_span_singleton, (hS y hy).2]
  obtain ⟨M, hM⟩ : I * I.map (cO E) ∣ Ideal.span {m} := by
    rw [← hspan y0 hy0]; exact mul_dvd_mul (hdvdI y0 hy0) (hdvdI' y0 hy0)
  have hm0 : Ideal.span {m} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  have hM0 : M ≠ ⊥ := by
    rintro rfl; rw [Ideal.mul_bot] at hM; exact hm0 hM
  have hNm : (Algebra.norm ℤ m).natAbs = Ideal.absNorm I ^ 2 * Ideal.absNorm M := by
    rw [← Ideal.absNorm_span_singleton, hM, map_mul, map_mul, hNI', sq]
  have hII' : I * I.map (cO E) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.mul_eq_bot, not_or]; exact ⟨hI, hI'0⟩
  have hdiv : ∀ y ∈ S, ∃ K : Ideal (𝓞 E), Ideal.span {y} = I * K := fun y hy => by
    obtain ⟨K, hK⟩ := hdvdI y hy; exact ⟨K, hK⟩
  choose! J hJ using hdiv
  have hJM : ∀ y ∈ S, J y ∣ M := fun y hy => by
    obtain ⟨K, hK⟩ := hdvdI' y hy
    refine ⟨K, ?_⟩
    have h := hspan y hy
    rw [hJ y hy, hK, hM] at h
    apply mul_left_cancel₀ hII'
    rw [← h]; ring
  have hcardJ : (S.image J).card ≤ Ideal.absNorm M :=
    card_dvd_le_absNorm M hM0 _ (fun K hK => by
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hK; exact hJM y hy)
  have hT : ∀ K ∈ S.image J, (S.filter fun y => J y = K).card ≤ Fintype.card (Units.torsion E) := by
    intro K hK
    obtain ⟨y1, hy1, rfl⟩ := Finset.mem_image.mp hK
    calc (S.filter fun y => J y = J y1).card
        ≤ ((Finset.univ : Finset (Units.torsion E)).image
            (fun ζ : Units.torsion E => ((ζ : (𝓞 E)ˣ) : 𝓞 E) * y1)).card := by
          apply Finset.card_le_card
          intro y hy
          rw [Finset.mem_filter] at hy
          obtain ⟨hyS, hyJ⟩ := hy
          have hsp : Ideal.span {y1} = Ideal.span {y} := by rw [hJ y hyS, hJ y1 hy1, hyJ]
          obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hsp
          have hy1m := (hS y1 hy1).2
          have hym := (hS y hyS).2
          rw [← hu, map_mul] at hym
          have huu : (u : 𝓞 E) * cO E (u : 𝓞 E) = 1 := by
            apply mul_left_cancel₀ hm
            calc m * ((u : 𝓞 E) * cO E (u : 𝓞 E))
                = y1 * (u : 𝓞 E) * (cO E y1 * cO E (u : 𝓞 E)) := by
                  rw [← hy1m]; ring
              _ = m * 1 := by rw [hym, mul_one]
          have htor : u ∈ Units.torsion E := by
            apply mem_torsion_of_mul_conj
            have h := congrArg (fun z : 𝓞 E => (z : E)) huu
            simpa [cO_coe] using h
          rw [Finset.mem_image]
          exact ⟨(⟨u, htor⟩ : Units.torsion E), Finset.mem_univ _, by
            show (u : 𝓞 E) * y1 = y
            rw [mul_comm]; exact hu⟩
      _ ≤ Fintype.card (Units.torsion E) := by
          rw [← Finset.card_univ]; exact Finset.card_image_le
  have hcard : S.card ≤ Fintype.card (Units.torsion E) * (S.image J).card :=
    Finset.card_le_mul_card_image S _ hT
  have htors : Fintype.card (Units.torsion E) ≤ 2 * (Module.finrank ℚ E) ^ 2 := by
    have h := torsionOrder_le E
    first
    | exact h
    | (rw [← Nat.card_eq_fintype_card]; exact h)
    | (rw [← Nat.card_eq_fintype_card]; unfold Units.torsionOrder at h; exact h)
    | (simpa [Units.torsionOrder, Nat.card_eq_fintype_card] using h)
  have hS' : S.card ≤ 2 * (Module.finrank ℚ E) ^ 2 * Ideal.absNorm M :=
    hcard.trans (Nat.mul_le_mul htors hcardJ)
  calc S.card * Ideal.absNorm I ^ 2
      ≤ 2 * (Module.finrank ℚ E) ^ 2 * Ideal.absNorm M * Ideal.absNorm I ^ 2 :=
        Nat.mul_le_mul hS' le_rfl
    _ = 2 * (Module.finrank ℚ E) ^ 2 * (Algebra.norm ℤ m).natAbs := by rw [hNm]; ring
end Formalism.L2.SG.NGCut.TorsionTotientBound
